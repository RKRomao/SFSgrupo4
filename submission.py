import re
import sys
from dataclasses import dataclass
from typing import List, NamedTuple, Optional

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")


def simplify(cnf, literal):
    neg = -literal
    return [[lit for lit in clause if lit != neg] for clause in cnf if literal not in clause]


def get_variables(cnf):
    return {abs(lit) for clause in cnf for lit in clause}


def dpll(cnf, assignment=None, all_vars=None):
    if assignment is None:
        assignment = {}
    else:
        assignment = assignment.copy()

    if all_vars is None:
        all_vars = get_variables(cnf)

    while True:
        if any(len(c) == 0 for c in cnf):
            return False, None
        if len(cnf) == 0:
            for v in all_vars:
                if v not in assignment:
                    assignment[v] = 0
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
    if len(cnf) == 0:
        for v in all_vars:
            if v not in assignment:
                assignment[v] = 0
        return True, assignment

    branch_var = sorted(v for v in all_vars if v not in assignment)[0]
    sat, model = dpll(simplify(cnf, branch_var), {**assignment, branch_var: 1}, all_vars)
    if sat:
        return True, model
    return dpll(simplify(cnf, -branch_var), {**assignment, branch_var: 0}, all_vars)


class Token(NamedTuple):
    type: str
    value: str
    line: int = 1
    col: int = 0


TOKEN_SPEC = [
    ("SKIP",      r"[ \t\r\n]+"),
    ("SHL",       r"<<"),
    ("SHR",       r">>"),
    ("CONCAT",    r"◦|\+\+"),
    ("EQ",        r"==|="),
    ("AND",       r"∧|/\\|\bAND\b|\band\b"),
    ("NOT",       r"¬|!|\bNOT\b|\bnot\b"),
    ("PLUS",      r"\+"),
    ("MINUS",     r"−|-"),
    ("MUL",       r"·|\*"),
    ("DIV",       r"/"),
    ("B_XOR",     r"⊕|\^|\bXOR\b|\bxor\b"),
    ("B_AND",     r"&"),
    ("B_OR",      r"\|"),
    ("B_NOT",     r"∼|~"),
    ("LT",        r"<"),
    ("QUESTION",  r"\?"),
    ("COLON",     r":"),
    ("LBRACKET",  r"\["),
    ("RBRACKET",  r"\]"),
    ("LPAREN",    r"\("),
    ("RPAREN",    r"\)"),
    ("SEMICOLON", r";"),
    ("EXT",       r"\bext\b"),
    ("CONST",     r"\b\d+\b"),
    ("IDENT",     r"\b[a-zA-Z_]\w*\b"),
]

MASTER_REGEX = re.compile("|".join(f"(?P<{p[0]}>{p[1]})" for p in TOKEN_SPEC))


def tokenize(text: str) -> List[Token]:
    tokens = []
    line, start = 1, 0
    for m in MASTER_REGEX.finditer(text):
        kind, val = m.lastgroup, m.group()
        if kind == "SKIP":
            nl = val.count("\n")
            if nl:
                line += nl
                start = m.end() - len(val.split("\n")[-1])
            continue
        tokens.append(Token(kind, val, line, m.start() - start))
    return tokens


@dataclass
class FormulaAnd: left: any; right: any
@dataclass
class FormulaNot: child: any
@dataclass
class Rel: op: str; left: any; right: any
@dataclass
class BinOp: op: str; left: any; right: any
@dataclass
class UnOp: op: str; child: any
@dataclass
class Var: name: str
@dataclass
class Const: val: int
@dataclass
class Mux: cond: any; then_t: any; else_t: any
@dataclass
class Slice: term: any; high: int; low: int
@dataclass
class BitSelect: term: any; index: int
@dataclass
class Ext: term: any


PRECEDENCE = {
    "B_OR":   (1, "|"),
    "B_XOR":  (2, "⊕"),
    "B_AND":  (3, "&"),
    "CONCAT": (4, "◦"),
    "SHL":    (5, "<<"), "SHR":   (5, ">>"),
    "PLUS":   (6, "+"),  "MINUS": (6, "−"),
    "MUL":    (7, "·"),  "DIV":   (7, "/"),
}


class Parser:
    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.pos = 0

    def peek(self) -> Optional[Token]:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def match(self, *expected: str) -> Optional[Token]:
        tok = self.peek()
        if tok and tok.type in expected:
            self.pos += 1
            return tok
        return None

    def expect(self, expected: str) -> Token:
        tok = self.match(expected)
        if not tok:
            raise ValueError(f"Expected {expected}, got {self.peek()}")
        return tok

    def parse_formula(self):
        node = self.parse_formula_unary()
        while self.match("AND"):
            node = FormulaAnd(node, self.parse_formula_unary())
        return node

    def parse_formula_unary(self):
        if self.match("NOT"):
            return FormulaNot(self.parse_formula_unary())
        if self.peek() and self.peek().type == "LPAREN":
            saved = self.pos
            self.pos += 1
            try:
                inner = self.parse_formula()
                if self.match("RPAREN") and not (self.peek() and self.peek().type in ("LT", "EQ")):
                    return inner
            except Exception:
                pass
            self.pos = saved
        return self.parse_atom()

    def parse_atom(self):
        left = self.parse_term()
        rel = self.match("LT", "EQ")
        if rel:
            return Rel("<" if rel.type == "LT" else "=", left, self.parse_term())
        return left

    def parse_term(self):
        term = self.parse_binary()
        if self.match("QUESTION"):
            then_t = self.parse_term()
            self.expect("COLON")
            else_t = self.parse_term()
            return Mux(term, then_t, else_t)
        return term

    def parse_binary(self, min_prec=1):
        left = self.parse_unary_term()
        while self.peek() and self.peek().type in PRECEDENCE:
            prec, op = PRECEDENCE[self.peek().type]
            if prec < min_prec:
                break
            self.pos += 1
            right = self.parse_binary(prec + 1)
            left = BinOp(op, left, right)
        return left

    def parse_unary_term(self):
        if self.match("B_NOT"):
            return UnOp("∼", self.parse_unary_term())
        return self.parse_primary()

    def parse_primary(self):
        tok = self.peek()
        if not tok:
            raise ValueError("Unexpected end of input")
        if self.match("LPAREN"):
            node = self.parse_term()
            self.expect("RPAREN")
        elif self.match("EXT"):
            self.expect("LPAREN")
            node = Ext(self.parse_term())
            self.expect("RPAREN")
        elif self.match("CONST"):
            node = Const(int(tok.value))
        elif self.match("IDENT"):
            node = Var(tok.value)
        else:
            raise ValueError(f"Unexpected token: {tok}")

        while self.match("LBRACKET"):
            c1 = int(self.expect("CONST").value)
            if self.match("COLON"):
                c2 = int(self.expect("CONST").value)
                self.expect("RBRACKET")
                node = Slice(node, c1, c2)
            else:
                self.expect("RBRACKET")
                node = BitSelect(node, c1)
        return node


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

    def constant(self, val, width=None):
        w = width if width is not None else self.width
        return [1 if (val >> i) & 1 else -1 for i in range(w)]

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
        s = []
        c = cin
        for i in range(self.width):
            s.append(self.xor_gate(self.xor_gate(a[i], b[i]), c))
            c = self.or_gate(self.and_gate(a[i], b[i]), self.and_gate(c, self.xor_gate(a[i], b[i])))
        return s

    def b_sub(self, a, b):
        return self.b_add(a, self.b_not(b), cin=1)

    def b_mul(self, a, b):
        acc = self.constant(0)
        for j in range(self.width):
            row = []
            for i in range(self.width):
                if i < j:
                    row.append(-1)
                else:
                    row.append(self.and_gate(a[i - j], b[j]))
            acc = self.b_add(acc, row)
        return acc

    def b_ge(self, a, b):
        c = 1
        for i in range(self.width):
            t1 = self.and_gate(a[i], -b[i])
            t2 = self.xor_gate(a[i], -b[i])
            c = self.or_gate(t1, self.and_gate(c, t2))
        return c

    def b_lt(self, a, b):
        return -self.b_ge(a, b)

    def b_eq(self, a, b):
        eq = 1
        for i in range(self.width):
            bit_eq = -self.xor_gate(a[i], b[i])
            eq = self.and_gate(eq, bit_eq)
        return eq

    def b_mux(self, cond, then_t, else_t):
        res = []
        for i in range(self.width):
            t1 = self.and_gate(cond, then_t[i])
            t2 = self.and_gate(-cond, else_t[i])
            res.append(self.or_gate(t1, t2))
        return res

    def b_div(self, a, b):
        rem = self.constant(0)
        q = [-1] * self.width
        for i in range(self.width - 1, -1, -1):
            rem = [a[i]] + rem[:-1]
            ge = self.b_ge(rem, b)
            sub = self.b_sub(rem, b)
            rem = self.b_mux(ge, sub, rem)
            q[i] = ge
        return q

    def b_shl(self, a, b):
        res = a
        for j in range(self.width):
            shift_amt = 1 << j
            if shift_amt < self.width:
                shifted = [-1] * shift_amt + res[:-shift_amt]
                res = self.b_mux(b[j], shifted, res)
        return res

    def b_shr(self, a, b):
        res = a
        for j in range(self.width):
            shift_amt = 1 << j
            if shift_amt < self.width:
                shifted = res[shift_amt:] + [-1] * shift_amt
                res = self.b_mux(b[j], shifted, res)
        return res

    def b_concat(self, a, b):
        full = b + a
        return full[:self.width]

    def b_slice(self, a, high, low):
        sl = a[low:high + 1]
        if len(sl) < self.width:
            sl = sl + [-1] * (self.width - len(sl))
        return sl[:self.width]

    def b_ext(self, a):
        if len(a) < self.width:
            return a + [-1] * (self.width - len(a))
        return a[:self.width]

    def blast_formula(self, node):
        if isinstance(node, FormulaAnd):
            return self.and_gate(self.blast_formula(node.left), self.blast_formula(node.right))
        if isinstance(node, FormulaNot):
            return -self.blast_formula(node.child)
        if isinstance(node, Rel):
            t1 = self.blast_term(node.left)
            t2 = self.blast_term(node.right)
            return self.b_lt(t1, t2) if node.op == "<" else self.b_eq(t1, t2)
        if isinstance(node, BitSelect):
            t = self.blast_term(node.term)
            return t[node.index]
        if isinstance(node, Var):
            return self.get_bool_var(node.name)
        return 1

    def blast_term(self, node):
        if isinstance(node, Var):
            return self.get_var(node.name)
        if isinstance(node, Const):
            return self.constant(node.val)
        if isinstance(node, UnOp) and node.op == "∼":
            return self.b_not(self.blast_term(node.child))
        if isinstance(node, BinOp):
            t1 = self.blast_term(node.left)
            t2 = self.blast_term(node.right)
            ops = {
                "+": self.b_add, "−": self.b_sub, "·": self.b_mul, "/": self.b_div,
                "<<": self.b_shl, ">>": self.b_shr, "&": self.b_and, "|": self.b_or,
                "⊕": self.b_xor, "◦": self.b_concat
            }
            return ops[node.op](t1, t2)
        if isinstance(node, Mux):
            cond = self.blast_formula(node.cond)
            return self.b_mux(cond, self.blast_term(node.then_t), self.blast_term(node.else_t))
        if isinstance(node, Slice):
            return self.b_slice(self.blast_term(node.term), node.high, node.low)
        if isinstance(node, Ext):
            return self.b_ext(self.blast_term(node.term))
        raise ValueError(f"Unknown term node: {node}")


def solve(text: str):
    lines = [l.strip() for l in text.strip().splitlines() if l.strip()]
    if not lines:
        return

    # Determinacao da largura em bits (bit 0 e o menos significativo)
    width = 4
    if lines[0].isdigit():
        width, lines = int(lines[0]), lines[1:]
    else:
        nums = [int(n) for n in re.findall(r"\b\d+\b", "\n".join(lines))]
        if nums:
            width = max(2, max(nums).bit_length())

    bb = BitBlaster(width)
    for line in lines:
        for stmt in line.split(";"):
            stmt = stmt.strip()
            if not stmt:
                continue
            ast = Parser(tokenize(stmt)).parse_formula()
            lit = bb.blast_formula(ast)
            bb.clauses.append([lit])

    sat, model = dpll(bb.clauses)
    if not sat:
        print("UNSAT")
        return

    print("SAT")
    res = []
    for name in sorted(bb.vars):
        bits = [str(model.get(abs(b), 0)) for b in reversed(bb.vars[name])]
        res.append(f"{name} = {''.join(bits)}")

    sys.stderr.write(", ".join(res) + "\n")
    sys.stderr.flush()


def main():
    raw = sys.stdin.read().strip()
    if raw:
        solve(raw)


if __name__ == "__main__":
    main()
