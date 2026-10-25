import re
import sys
from lark import Lark, Transformer

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")


# ==========================================
# 1. DPLL SOLVER
# ==========================================

def simplify(cnf, literal):
    neg = -literal
    return [[l for l in c if l != neg] for c in cnf if literal not in c]


def get_variables(cnf):
    return {abs(l) for c in cnf for l in c}


def dpll(cnf, assignment=None, all_vars=None):
    assignment = {} if assignment is None else assignment.copy()
    if all_vars is None:
        all_vars = get_variables(cnf)

    while True:
        if any(len(c) == 0 for c in cnf):
            return False, None
        if not cnf:
            for v in all_vars:
                assignment.setdefault(v, 0)
            return True, assignment

        unit = next((c for c in cnf if len(c) == 1), None)
        if unit:
            lit = unit[0]
            assignment[abs(lit)] = 1 if lit > 0 else 0
            cnf = simplify(cnf, lit)
            continue

        lits = {l for c in cnf for l in c}
        pure = {l for l in lits if -l not in lits}
        if pure:
            for lit in pure:
                assignment[abs(lit)] = 1 if lit > 0 else 0
            cnf = [c for c in cnf if not any(l in pure for l in c)]
            continue
        break

    if any(len(c) == 0 for c in cnf):
        return False, None
    if not cnf:
        for v in all_vars:
            assignment.setdefault(v, 0)
        return True, assignment

    branch = sorted(v for v in all_vars if v not in assignment)[0]
    sat, model = dpll(simplify(cnf, branch), {**assignment, branch: 1}, all_vars)
    return (True, model) if sat else dpll(simplify(cnf, -branch), {**assignment, branch: 0}, all_vars)


# ==========================================
# 2. BIT-BLASTER
# ==========================================

class BitBlaster:
    def __init__(self, width=4):
        self.width = width
        self.vars = {}
        self.bool_vars = {}
        self.clauses = [[1]]
        self.var_count = 1

    def new_var(self):
        self.var_count += 1
        return self.var_count

    def get_var(self, name):
        if name not in self.vars:
            self.vars[name] = [self.new_var() for _ in range(self.width)]
        return self.vars[name]

    def get_bool_var(self, name):
        if name not in self.bool_vars:
            self.bool_vars[name] = self.new_var()
        return self.bool_vars[name]

    def constant(self, val):
        return [1 if (val >> i) & 1 else -1 for i in range(self.width)]

    def and_gate(self, a, b):
        if a == 1: return b
        if b == 1: return a
        if a == -1 or b == -1: return -1
        z = self.new_var()
        self.clauses += [[-z, a], [-z, b], [-a, -b, z]]
        return z

    def or_gate(self, a, b):
        if a == -1: return b
        if b == -1: return a
        if a == 1 or b == 1: return 1
        z = self.new_var()
        self.clauses += [[-z, a, b], [-a, z], [-b, z]]
        return z

    def xor_gate(self, a, b):
        if a == -1: return b
        if b == -1: return a
        if a == 1: return -b
        if b == 1: return -a
        z = self.new_var()
        self.clauses += [[-a, -b, -z], [a, b, -z], [a, -b, z], [-a, b, z]]
        return z

    def b_not(self, a):
        return [-x for x in a]

    def b_and(self, a, b):
        return [self.and_gate(a[i], b[i]) for i in range(self.width)]

    def b_or(self, a, b):
        return [self.or_gate(a[i], b[i]) for i in range(self.width)]

    def b_xor(self, a, b):
        return [self.xor_gate(a[i], b[i]) for i in range(self.width)]

    def b_add(self, a, b, cin=-1):
        s, c = [], cin
        for i in range(self.width):
            s.append(self.xor_gate(self.xor_gate(a[i], b[i]), c))
            c = self.or_gate(self.and_gate(a[i], b[i]), self.and_gate(c, self.xor_gate(a[i], b[i])))
        return s

    def b_sub(self, a, b):
        return self.b_add(a, self.b_not(b), cin=1)

    def b_mul(self, a, b):
        acc = self.constant(0)
        for j in range(self.width):
            row = [-1] * j + [self.and_gate(a[i - j], b[j]) for i in range(j, self.width)]
            acc = self.b_add(acc, row)
        return acc

    def b_ge(self, a, b):
        c = 1
        for i in range(self.width):
            c = self.or_gate(self.and_gate(a[i], -b[i]), self.and_gate(c, self.xor_gate(a[i], -b[i])))
        return c

    def b_lt(self, a, b):
        return -self.b_ge(a, b)

    def b_eq(self, a, b):
        eq = 1
        for i in range(self.width):
            eq = self.and_gate(eq, -self.xor_gate(a[i], b[i]))
        return eq

    def b_mux(self, cond, then_t, else_t):
        return [self.or_gate(self.and_gate(cond, then_t[i]), self.and_gate(-cond, else_t[i])) for i in range(self.width)]


# ==========================================
# 3. GRAMATICA LARK & TRANSFORMER
# ==========================================

grammar = r"""
    start: (formula [";"])*

    ?formula: formula_and
    ?formula_and: formula_and _AND formula_not   -> f_and
                | formula_not
    ?formula_not: _NOT formula_not               -> f_not
                | "(" formula ")"
                | atom

    ?atom: term "<" term                        -> lt
         | term ("=" | "==") term               -> eq
         | term "[" INT "]"                     -> bit_select
         | CNAME                                -> bool_var

    ?term: ternary
    ?ternary: term_or "?" term ":" ternary      -> mux
            | term_or

    ?term_or: term_or ("|" | "OR"i) term_xor     -> b_or
            | term_xor

    ?term_xor: term_xor ("⊕" | "^" | "XOR"i) term_and -> b_xor
             | term_and

    ?term_and: term_and ("&" | "AND"i) term_concat    -> b_and
             | term_concat

    ?term_concat: term_concat ("◦" | "++") term_shift -> concat
                | term_shift

    ?term_shift: term_shift "<<" term_add       -> shl
               | term_shift ">>" term_add       -> shr
               | term_add

    ?term_add: term_add "+" term_mul            -> add
             | term_add ("−" | "-") term_mul    -> sub
             | term_mul

    ?term_mul: term_mul ("·" | "*") term_unary  -> mul
             | term_mul "/" term_unary          -> div
             | term_unary

    ?term_unary: ("∼" | "~") term_unary         -> b_not
               | postfix

    ?postfix: postfix "[" INT ":" INT "]"       -> slice
            | "ext" "(" term ")"                -> ext
            | primary

    ?primary: CNAME                             -> var
            | INT                               -> const
            | "(" term ")"

    _AND: "∧" | "/\\" | "AND"i
    _NOT: "¬" | "!" | "NOT"i

    COMMENT: /#[^\n]*/ | /\/\/[^\n]*/
    %ignore COMMENT

    %import common.CNAME
    %import common.INT
    %import common.WS
    %ignore WS
"""


class BitBlastTransformer(Transformer):
    def __init__(self, bb: BitBlaster):
        super().__init__()
        self.bb = bb

    def f_and(self, items):
        return self.bb.and_gate(items[0], items[1])

    def f_not(self, items):
        return -items[0]

    def lt(self, items):
        return self.bb.b_lt(items[0], items[1])

    def eq(self, items):
        return self.bb.b_eq(items[0], items[1])

    def bit_select(self, items):
        return items[0][int(items[1])]

    def bool_var(self, items):
        return self.bb.get_bool_var(str(items[0]))

    def mux(self, items):
        cond = items[0][0] if isinstance(items[0], list) else items[0]
        return self.bb.b_mux(cond, items[1], items[2])

    def b_or(self, items):
        return self.bb.b_or(items[0], items[1])

    def b_xor(self, items):
        return self.bb.b_xor(items[0], items[1])

    def b_and(self, items):
        return self.bb.b_and(items[0], items[1])

    def add(self, items):
        return self.bb.b_add(items[0], items[1])

    def sub(self, items):
        return self.bb.b_sub(items[0], items[1])

    def mul(self, items):
        return self.bb.b_mul(items[0], items[1])

    def b_not(self, items):
        return self.bb.b_not(items[0])

    def var(self, items):
        return self.bb.get_var(str(items[0]))

    def const(self, items):
        return self.bb.constant(int(items[0]))

    def start(self, items):
        return items

    # Operadores nao implementados
    def div(self, items):
        raise NotImplementedError("Operador de divisão '/' ainda não implementado")

    def shl(self, items):
        raise NotImplementedError("Operador de deslocamento '<<' ainda não implementado")

    def shr(self, items):
        raise NotImplementedError("Operador de deslocamento '>>' ainda não implementado")

    def concat(self, items):
        raise NotImplementedError("Operador de concatenação '◦' ainda não implementado")

    def slice(self, items):
        raise NotImplementedError("Operador de fatiamento '[c1:c2]' ainda não implementado")

    def ext(self, items):
        raise NotImplementedError("Operador 'ext' ainda não implementado")


parser = Lark(grammar, parser="earley")


# ==========================================
# 4. SOLVER & MAIN
# ==========================================

def solve(text: str):
    lines = [l.strip() for l in text.strip().splitlines() if l.strip()]
    if not lines:
        return

    width = 4
    if lines[0].isdigit():
        width, lines = int(lines[0]), lines[1:]
    else:
        nums = [int(n) for n in re.findall(r"\b\d+\b", "\n".join(lines))]
        if nums:
            width = max(2, max(nums).bit_length())

    bb = BitBlaster(width)
    transformer = BitBlastTransformer(bb)

    try:
        tree = parser.parse("\n".join(lines))
        res = transformer.transform(tree)
    except Exception as e:
        msg = getattr(e, "orig_exc", e)
        sys.stderr.write(f"{msg}\n")
        sys.stderr.flush()
        return

    if isinstance(res, list):
        for lit in res:
            if lit is not None:
                bb.clauses.append([lit])
    elif res is not None:
        bb.clauses.append([res])

    sat, model = dpll(bb.clauses)
    if not sat:
        print("UNSAT")
        return

    print("SAT")
    res_str = []
    for name in sorted(bb.vars):
        bits = [str(model.get(abs(b), 0)) for b in reversed(bb.vars[name])]
        res_str.append(f"{name} = {''.join(bits)}")

    sys.stderr.write(", ".join(res_str) + "\n")
    sys.stderr.flush()


def main():
    raw = sys.stdin.read().strip()
    if raw:
        solve(raw)


if __name__ == "__main__":
    main()
