import re
import sys
from typing import List, Dict, Optional, Tuple, Set


def simplify(cnf: List[List[int]], literal: int) -> List[List[int]]:
    neg = -literal
    new_cnf = []
    for clause in cnf:
        if literal in clause:
            continue
        new_cnf.append([lit for lit in clause if lit != neg])
    return new_cnf


def get_variables(cnf: List[List[int]]) -> Set[int]:
    vars_set = set()
    for clause in cnf:
        for lit in clause:
            vars_set.add(abs(lit))
    return vars_set


def dpll(cnf: List[List[int]], assignment: Optional[Dict[int, int]] = None, all_vars: Optional[Set[int]] = None) -> Tuple[bool, Optional[Dict[int, int]]]:
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

        unit = next((c for c in cnf if len(c) == 1), None)
        if unit:
            lit = unit[0]
            assignment[abs(lit)] = 1 if lit > 0 else 0
            cnf = simplify(cnf, lit)
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
    branch = unassigned[0]

    sat, model = dpll(simplify(cnf, branch), {**assignment, branch: 1}, all_vars)
    if sat:
        return True, model

    return dpll(simplify(cnf, -branch), {**assignment, branch: 0}, all_vars)


class BitBlaster:
    def __init__(self, width: int = 2):
        self.width = width
        self.var_count = 1
        self.TRUE = 1
        self.clauses: List[List[int]] = [[self.TRUE]]
        self.variables: Dict[str, List[int]] = {}

    def new_var(self) -> int:
        self.var_count += 1
        return self.var_count

    def add_clause(self, clause: List[int]):
        self.clauses.append(clause)

    def get_var(self, name: str) -> List[int]:
        if name not in self.variables:
            bits = [self.new_var() for _ in range(self.width)]
            self.variables[name] = bits
        return self.variables[name]

    def constant(self, val: int) -> List[int]:
        bits = []
        for i in range(self.width):
            bit_val = (val >> i) & 1
            bits.append(self.TRUE if bit_val == 1 else -self.TRUE)
        return bits

    def b_not(self, a: List[int]) -> List[int]:
        return [-lit for lit in a]

    def and_gate(self, a: int, b: int) -> int:
        out = self.new_var()
        self.add_clause([-out, a])
        self.add_clause([-out, b])
        self.add_clause([-a, -b, out])
        return out

    def or_gate(self, a: int, b: int) -> int:
        out = self.new_var()
        self.add_clause([-out, a, b])
        self.add_clause([-a, out])
        self.add_clause([-b, out])
        return out

    def xor_gate(self, a: int, b: int) -> int:
        out = self.new_var()
        self.add_clause([-a, -b, -out])
        self.add_clause([a, b, -out])
        self.add_clause([a, -b, out])
        self.add_clause([-a, b, out])
        return out

    def b_and(self, a: List[int], b: List[int]) -> List[int]:
        return [self.and_gate(a[i], b[i]) for i in range(self.width)]

    def b_or(self, a: List[int], b: List[int]) -> List[int]:
        return [self.or_gate(a[i], b[i]) for i in range(self.width)]

    def b_xor(self, a: List[int], b: List[int]) -> List[int]:
        return [self.xor_gate(a[i], b[i]) for i in range(self.width)]

    def b_add(self, a: List[int], b: List[int]) -> List[int]:
        res = []
        carry = -self.TRUE
        for i in range(self.width):
            t1 = self.xor_gate(a[i], b[i])
            z = self.xor_gate(t1, carry)
            res.append(z)
            c1 = self.and_gate(a[i], b[i])
            c2 = self.and_gate(carry, t1)
            carry = self.or_gate(c1, c2)
        return res

    def b_sub(self, a: List[int], b: List[int]) -> List[int]:
        res = []
        carry = self.TRUE
        for i in range(self.width):
            t1 = self.xor_gate(a[i], -b[i])
            z = self.xor_gate(t1, carry)
            res.append(z)
            c1 = self.and_gate(a[i], -b[i])
            c2 = self.and_gate(carry, t1)
            carry = self.or_gate(c1, c2)
        return res

    def assert_equal(self, a: List[int], b: List[int]):
        for i in range(self.width):
            self.add_clause([-a[i], b[i]])
            self.add_clause([a[i], -b[i]])

    def assert_less_than(self, a: List[int], b: List[int]):
        carry = self.TRUE
        for i in range(self.width):
            term1 = self.and_gate(a[i], -b[i])
            term2 = self.xor_gate(a[i], -b[i])
            term3 = self.and_gate(carry, term2)
            carry = self.or_gate(term1, term3)
        self.add_clause([-carry])

    def assert_greater_than(self, a: List[int], b: List[int]):
        self.assert_less_than(b, a)


class Parser:
    def __init__(self, blaster: BitBlaster):
        self.bb = blaster

    def tokenize(self, text: str) -> List[str]:
        specials = ["==", "=", "<=", ">=", "<", ">", "!=", "(", ")", "~", "^", "&", "|", "+", "-"]
        pattern = "|".join(re.escape(s) for s in sorted(specials, key=len, reverse=True))
        pattern += r"|[a-zA-Z_][a-zA-Z0-9_]*|\d+"
        return re.findall(pattern, text)

    def find_op(self, tokens: List[str], ops: List[str]) -> int:
        depth = 0
        for i in reversed(range(len(tokens))):
            tok = tokens[i]
            if tok == ")":
                depth += 1
            elif tok == "(":
                depth -= 1
            elif depth == 0 and tok in ops:
                return i
        return -1

    def strip_parens(self, tokens: List[str]) -> List[str]:
        while tokens and tokens[0] == "(" and tokens[-1] == ")":
            depth = 0
            encloses = True
            for i in range(len(tokens) - 1):
                if tokens[i] == "(":
                    depth += 1
                elif tokens[i] == ")":
                    depth -= 1
                if depth == 0:
                    encloses = False
                    break
            if encloses:
                tokens = tokens[1:-1]
            else:
                break
        return tokens

    def parse_constraint(self, text: str):
        tokens = self.tokenize(text)
        if not tokens:
            return

        rel_idx = self.find_op(tokens, ["=", "==", "<", ">"])
        if rel_idx == -1:
            return

        rel_op = tokens[rel_idx]
        left_val = self.eval_expr(tokens[:rel_idx])
        right_val = self.eval_expr(tokens[rel_idx + 1:])

        if rel_op in ["=", "=="]:
            self.bb.assert_equal(left_val, right_val)
        elif rel_op == "<":
            self.bb.assert_less_than(left_val, right_val)
        elif rel_op == ">":
            self.bb.assert_greater_than(left_val, right_val)

    def eval_expr(self, tokens: List[str]) -> List[int]:
        tokens = self.strip_parens(tokens)
        if not tokens:
            return self.bb.constant(0)

        idx = self.find_op(tokens, ["OR", "|"])
        if idx != -1:
            return self.bb.b_or(self.eval_expr(tokens[:idx]), self.eval_expr(tokens[idx + 1:]))

        idx = self.find_op(tokens, ["XOR", "^"])
        if idx != -1:
            return self.bb.b_xor(self.eval_expr(tokens[:idx]), self.eval_expr(tokens[idx + 1:]))

        idx = self.find_op(tokens, ["AND", "&"])
        if idx != -1:
            return self.bb.b_and(self.eval_expr(tokens[:idx]), self.eval_expr(tokens[idx + 1:]))

        idx = self.find_op(tokens, ["+", "-"])
        if idx != -1:
            if tokens[idx] == "+":
                return self.bb.b_add(self.eval_expr(tokens[:idx]), self.eval_expr(tokens[idx + 1:]))
            return self.bb.b_sub(self.eval_expr(tokens[:idx]), self.eval_expr(tokens[idx + 1:]))

        if tokens[0] in ["NOT", "~"]:
            return self.bb.b_not(self.eval_expr(tokens[1:]))

        if len(tokens) == 1:
            tok = tokens[0]
            if tok.isdigit():
                return self.bb.constant(int(tok))
            return self.bb.get_var(tok)

        return self.bb.constant(0)


def solve(raw_input: str):
    lines = [line.strip() for line in raw_input.strip().splitlines() if line.strip()]
    if not lines:
        return

    width = 2
    constraint_lines = []

    for line in lines:
        if line.isdigit():
            width = int(line)
        elif re.match(r"^(?:width|bits)\s*[:=]?\s*(\d+)$", line, re.IGNORECASE):
            m = re.match(r"^(?:width|bits)\s*[:=]?\s*(\d+)$", line, re.IGNORECASE)
            if m:
                width = int(m.group(1))
        else:
            constraint_lines.append(line)

    if not any(l.isdigit() for l in lines):
        all_nums = [int(n) for n in re.findall(r"\b\d+\b", raw_input)]
        if all_nums:
            max_num = max(all_nums)
            width = max(width, max_num.bit_length())

    blaster = BitBlaster(width)
    parser = Parser(blaster)

    for cline in constraint_lines:
        for sub in re.split(r"[;\n]", cline):
            if sub.strip():
                parser.parse_constraint(sub.strip())

    sat, model = dpll(blaster.clauses)

    if not sat or model is None:
        print("UNSAT")
        return

    print("SAT")

    results = []
    for name in sorted(blaster.variables.keys()):
        bits = blaster.variables[name]
        bit_chars = []
        for b in reversed(bits):
            if b == blaster.TRUE:
                val = 1
            elif b == -blaster.TRUE:
                val = 0
            else:
                val = model.get(abs(b), 0)
                if b < 0:
                    val = 1 - val
            bit_chars.append(str(val))
        results.append(f"{name} = {''.join(bit_chars)}")

    sys.stderr.write(", ".join(results) + "\n")


def main():
    raw = sys.stdin.read().strip()
    if raw:
        solve(raw)


if __name__ == "__main__":
    main()
