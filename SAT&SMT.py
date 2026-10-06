<<<<<<< HEAD
=======
import re
import sys


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


def dpll(cnf, model=None, decision_vars=None):
    if model is None:
        model = {}

    while True:
        if any(len(c) == 0 for c in cnf):
            return False, None
        if not cnf:
            return True, model

        unit = next((c[0] for c in cnf if len(c) == 1), None)
        if unit is None:
            break

        model[abs(unit)] = 1 if unit > 0 else 0
        cnf = [[l for l in c if l != -unit] for c in cnf if unit not in c]

    if any(len(c) == 0 for c in cnf):
        return False, None
    if not cnf:
        return True, model

    all_vars = set(abs(l) for c in cnf for l in c)
    cand = [v for v in (decision_vars or []) if v in all_vars and v not in model]
    branch = cand[0] if cand else next(iter(all_vars - model.keys()))

    for val in [0, 1]:
        lit = branch if val else -branch
        next_cnf = [[l for l in c if l != -lit] for c in cnf if lit not in c]
        sat, res = dpll(next_cnf, {**model, branch: val}, decision_vars)
        if sat:
            return True, res

    return False, None


def eval_expr(bb, tokens):
    while tokens and tokens[0] == "(" and tokens[-1] == ")":
        tokens = tokens[1:-1]

    for op, fn in [("OR", bb.b_or), ("|", bb.b_or), ("XOR", bb.b_xor), ("^", bb.b_xor), ("AND", bb.b_and), ("&", bb.b_and)]:
        if op in tokens:
            idx = tokens.index(op)
            return fn(eval_expr(bb, tokens[:idx]), eval_expr(bb, tokens[idx + 1:]))

    if tokens and tokens[0] in ["NOT", "~"]:
        return bb.b_not(eval_expr(bb, tokens[1:]))

    if len(tokens) == 1:
        return bb.constant(int(tokens[0])) if tokens[0].isdigit() else bb.get_var(tokens[0])

    return bb.constant(0)


def add_constraint(bb, text):
    raw_tokens = re.findall(r"==|=|<=|>=|<|>|!=|\(|\)|~|\^|&|\||[a-zA-Z_]\w*|\d+", text)
    tokens = [t.upper() if t.upper() in ["AND", "OR", "XOR", "NOT"] else t for t in raw_tokens]

    for i, tok in enumerate(tokens):
        if tok in ["=", "==", "<", ">"]:
            left = eval_expr(bb, tokens[:i])
            right = eval_expr(bb, tokens[i + 1:])
            if tok in ["=", "=="]:
                bb.assert_equal(left, right)
            elif tok == "<":
                bb.assert_less(left, right)
            elif tok == ">":
                bb.assert_greater(left, right)
            break


def solve(text):
    lines = [l.strip() for l in text.strip().splitlines() if l.strip()]
    if not lines:
        return

    nums = [int(n) for n in re.findall(r"\b\d+\b", text)]
    width = max(2, max(nums).bit_length() if nums else 2)
    if lines and lines[0].isdigit():
        width, lines = int(lines[0]), lines[1:]

    bb = BitBlaster(width)
    for line in lines:
        for sub in re.split(r"[;\n]", line):
            if sub.strip():
                add_constraint(bb, sub.strip())

    dec_vars = [v for name in sorted(bb.vars) for v in bb.vars[name]]
    sat, model = dpll(bb.clauses, decision_vars=dec_vars)

    if not sat:
        print("UNSAT")
        return

    print("SAT")
    res = []
    for name in sorted(bb.vars):
        bits = [str(model.get(abs(b), 0) if b not in (1, -1) else (1 if b == 1 else 0)) for b in reversed(bb.vars[name])]
        res.append(f"{name} = {''.join(bits)}")

    sys.stderr.write(", ".join(res) + "\n")
    sys.stderr.flush()


def main():
    raw = sys.stdin.read().strip()
    if raw:
        solve(raw)


if __name__ == "__main__":
    main()
>>>>>>> 9136f4fb81e6110bdf91dfa159e7839de08db052
