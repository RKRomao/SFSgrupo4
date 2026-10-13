import re
import sys


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
        if any(len(clause) == 0 for clause in cnf):
            return False, None

        if len(cnf) == 0:
            for v in all_vars:
                if v not in assignment:
                    assignment[v] = 0
            return True, assignment

        unit_clause = next((c for c in cnf if len(c) == 1), None)
        if unit_clause:
            unit_lit = unit_clause[0]
            assignment[abs(unit_lit)] = 1 if unit_lit > 0 else 0
            cnf = simplify(cnf, unit_lit)
            continue

        all_lits = {lit for clause in cnf for lit in clause}
        pure_lits = {lit for lit in all_lits if -lit not in all_lits}
        if pure_lits:
            for lit in sorted(pure_lits, key=lambda x: abs(x)):
                assignment[abs(lit)] = 1 if lit > 0 else 0
            cnf = [clause for clause in cnf if not any(lit in pure_lits for lit in clause)]
            continue

        break

    if any(len(clause) == 0 for clause in cnf):
        return False, None

    if len(cnf) == 0:
        for v in all_vars:
            if v not in assignment:
                assignment[v] = 0
        return True, assignment

    unassigned = [v for v in sorted(all_vars) if v not in assignment]
    branch_var = unassigned[0]

    sat, model = dpll(simplify(cnf, branch_var), {**assignment, branch_var: 1}, all_vars)
    if sat:
        return True, model

    return dpll(simplify(cnf, -branch_var), {**assignment, branch_var: 0}, all_vars)


def tokenize(text):
    return re.findall(r"[a-zA-Z_]\w*|\d+|==|!=|<=|>=|[=<>~^&|();]", text)


class Parser:
    def __init__(self, bb, tokens):
        self.bb = bb
        self.tokens = tokens
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def match(self, *expected):
        tok = self.peek()
        if tok and tok.upper() in [e.upper() for e in expected]:
            self.pos += 1
            return tok
        return None

    def expect(self, expected):
        tok = self.match(expected)
        if not tok:
            raise ValueError(f"Expected {expected}")
        return tok

    def parse_all(self):
        while self.pos < len(self.tokens):
            while self.match(";"):
                pass
            if self.pos >= len(self.tokens):
                break
            self.parse_constraint()

    def parse_constraint(self):
        left = self.parse_expr()
        op = self.match("==", "!=", "<=", ">=", "=", "<", ">")
        if not op:
            self.bb.assert_equal(left, self.bb.constant(1))
            return
        right = self.parse_expr()
        if op in ("=", "=="):
            self.bb.assert_equal(left, right)
        elif op == "<":
            self.bb.assert_less(left, right)
        elif op == ">":
            self.bb.assert_greater(left, right)
        elif op == "<=":
            self.bb.assert_less_or_equal(left, right)
        elif op == ">=":
            self.bb.assert_greater_or_equal(left, right)
        elif op == "!=":
            self.bb.assert_not_equal(left, right)

    def parse_expr(self):
        return self.parse_or()

    def parse_or(self):
        left = self.parse_xor()
        while self.match("OR", "|"):
            right = self.parse_xor()
            left = self.bb.b_or(left, right)
        return left

    def parse_xor(self):
        left = self.parse_and()
        while self.match("XOR", "^"):
            right = self.parse_and()
            left = self.bb.b_xor(left, right)
        return left

    def parse_and(self):
        left = self.parse_not()
        while self.match("AND", "&"):
            right = self.parse_not()
            left = self.bb.b_and(left, right)
        return left

    def parse_not(self):
        if self.match("NOT", "~"):
            return self.bb.b_not(self.parse_not())
        return self.parse_atom()

    def parse_atom(self):
        tok = self.peek()
        if self.match("("):
            val = self.parse_expr()
            self.expect(")")
            return val
        if tok and tok.isdigit():
            self.pos += 1
            return self.bb.constant(int(tok))
        if tok and re.match(r"^[a-zA-Z_]\w*$", tok):
            self.pos += 1
            return self.bb.get_var(tok)
        raise ValueError(f"Unexpected token {tok}")


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

    def assert_not_equal(self, a, b):
        diffs = [self.xor_gate(a[i], b[i]) for i in range(self.width)]
        self.clauses.append(diffs)

    def assert_less(self, a, b):
        c = 1
        for i in range(self.width):
            t1 = self.and_gate(a[i], -b[i])
            t2 = self.xor_gate(a[i], -b[i])
            c = self.or_gate(t1, self.and_gate(c, t2))
        self.clauses.append([-c])

    def assert_greater(self, a, b):
        self.assert_less(b, a)

    def assert_less_or_equal(self, a, b):
        c = 1
        for i in range(self.width):
            t1 = self.and_gate(b[i], -a[i])
            t2 = self.xor_gate(b[i], -a[i])
            c = self.or_gate(t1, self.and_gate(c, t2))
        self.clauses.append([c])

    def assert_greater_or_equal(self, a, b):
        self.assert_less_or_equal(b, a)


def solve(text):
    raw_lines = text.strip().splitlines()
    lines = []
    width = 2
    width_found = False

    for l in raw_lines:
        l = l.strip()
        if not l or l.startswith(("#", "//", "%", "/*")):
            continue
        if l.startswith("c ") or l.startswith("p "):
            continue
        l = re.sub(r"(//|#).*$", "", l).strip()
        if not l:
            continue
        if not width_found:
            m = re.match(r"^(?:width|bits|bitwidth|size)?\s*[:=]?\s*(\d+)\s*(?:bits?)?$", l, re.IGNORECASE)
            if m:
                width = int(m.group(1))
                width_found = True
                continue
        lines.append(l)

    if not lines:
        return

    if not width_found:
        nums = [int(n) for n in re.findall(r"\b\d+\b", "\n".join(lines))]
        if nums:
            width = max(2, max(nums).bit_length())

    bb = BitBlaster(width)
    tokens = tokenize("\n".join(lines))
    Parser(bb, tokens).parse_all()

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
