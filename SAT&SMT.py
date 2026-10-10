import re
import sys
from lark import Lark, Transformer


grammar = """
    start: constraint+

    ?constraint: expr ("=" | "==") expr  -> eq
               | expr "<" expr            -> lt
               | expr ">" expr            -> gt

    ?expr: expr_or

    ?expr_or: expr_or ("OR"i | "|") expr_xor    -> b_or
            | expr_xor

    ?expr_xor: expr_xor ("XOR"i | "^") expr_and -> b_xor
             | expr_and

    ?expr_and: expr_and ("AND"i | "&") expr_not -> b_and
             | expr_not

    ?expr_not: ("NOT"i | "~") atom              -> b_not
             | atom

    ?atom: CNAME                                -> var
         | INT                                  -> const
         | "(" expr ")"

    %import common.CNAME
    %import common.INT
    %import common.WS
    %ignore WS
"""


class BitBlaster:
    def __init__(self, width=2):
        self.width = width
        self.vars = {}
        self.clauses = [[1]]
        self.var_count = 1

    def new_var(self):
        self.var_count += 1
        return self.var_count

    def get_var(self, name):
        if name not in self.vars:
            self.vars[name] = [self.new_var() for _ in range(self.width)]
        return self.vars[name]

    def constant(self, val):
        return [1 if (val >> i) & 1 else -1 for i in range(self.width)]

    def b_not(self, a):
        return [-x for x in a]

    def and_gate(self, a, b):
        z = self.new_var()
        self.clauses += [[-z, a], [-z, b], [-a, -b, z]]
        return z

    def or_gate(self, a, b):
        z = self.new_var()
        self.clauses += [[-z, a, b], [-a, z], [-b, z]]
        return z

    def xor_gate(self, a, b):
        z = self.new_var()
        self.clauses += [[-a, -b, -z], [a, b, -z], [a, -b, z], [-a, b, z]]
        return z

    def b_and(self, a, b):
        return [self.and_gate(a[i], b[i]) for i in range(self.width)]

    def b_or(self, a, b):
        return [self.or_gate(a[i], b[i]) for i in range(self.width)]

    def b_xor(self, a, b):
        return [self.xor_gate(a[i], b[i]) for i in range(self.width)]

    def assert_equal(self, a, b):
        for i in range(self.width):
            self.clauses += [[-a[i], b[i]], [a[i], -b[i]]]

    def assert_less(self, a, b):
        c = 1
        for i in range(self.width):
            t1 = self.and_gate(a[i], -b[i])
            t2 = self.xor_gate(a[i], -b[i])
            c = self.or_gate(t1, self.and_gate(c, t2))
        self.clauses.append([-c])

    def assert_greater(self, a, b):
        self.assert_less(b, a)


class Flattening(Transformer):
    def __init__(self, blaster):
        super().__init__()
        self.bb = blaster

    def var(self, items):
        return self.bb.get_var(str(items[0]))

    def const(self, items):
        return self.bb.constant(int(items[0]))

    def b_not(self, items):
        return self.bb.b_not(items[0])

    def b_and(self, items):
        return self.bb.b_and(items[0], items[1])

    def b_or(self, items):
        return self.bb.b_or(items[0], items[1])

    def b_xor(self, items):
        return self.bb.b_xor(items[0], items[1])

    def eq(self, items):
        self.bb.assert_equal(items[0], items[1])

    def lt(self, items):
        self.bb.assert_less(items[0], items[1])

    def gt(self, items):
        self.bb.assert_greater(items[0], items[1])


def dpll(cnf, model=None, decision_vars=None):
    if model is None:
        model = {}

    while True:
        if any(len(c) == 0 for c in cnf):
            return False, None

        unit = next((c[0] for c in cnf if len(c) == 1), None)
        if unit is None:
            break

        model[abs(unit)] = 1 if unit > 0 else 0
        cnf = [[l for l in c if l != -unit] for c in cnf if unit not in c]

    if any(len(c) == 0 for c in cnf):
        return False, None

    unassigned = [v for v in (decision_vars or []) if v not in model]
    if not unassigned:
        if not cnf:
            return True, model
        all_vars = set(abs(l) for c in cnf for l in c)
        unassigned = [v for v in sorted(all_vars) if v not in model]
        if not unassigned:
            return True, model

    branch = unassigned[0]
    for val in [1, 0]:
        lit = branch if val else -branch
        next_cnf = [[l for l in c if l != -lit] for c in cnf if lit not in c]
        sat, res = dpll(next_cnf, {**model, branch: val}, decision_vars)
        if sat:
            return True, res

    return False, None


def solve(text):
    lines = [l.strip() for l in text.strip().splitlines() if l.strip()]
    if not lines:
        return

    nums = [int(n) for n in re.findall(r"\b\d+\b", text)]
    width = max(2, max(nums).bit_length() if nums else 2)
    if lines and lines[0].isdigit():
        width, lines = int(lines[0]), lines[1:]

    bb = BitBlaster(width)
    parser = Lark(grammar, parser="lalr")
    tree = parser.parse("\n".join(lines))
    Flattening(bb).transform(tree)

    dec_vars = [b for name in sorted(bb.vars, reverse=True) for b in reversed(bb.vars[name])]
    sat, model = dpll(bb.clauses, decision_vars=dec_vars)

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
