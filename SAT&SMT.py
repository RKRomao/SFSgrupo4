import ast
import json
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


def format_solution(sat: bool, model: Optional[Dict[int, int]] = None) -> str:
    return "SAT" if sat else "UNSAT"


def solve_cnf(cnf: List[List[int]]) -> str:
    sat, model = dpll(cnf)
    return format_solution(sat, model)


def parse_cnf(raw: str) -> List[List[int]]:
    raw = raw.strip()
    if not raw:
        return []

    try:
        data = ast.literal_eval(raw)
        if isinstance(data, list):
            return [[int(lit) for lit in clause] for clause in data]
    except Exception:
        pass

    try:
        data = json.loads(raw)
        if isinstance(data, list):
            return [[int(lit) for lit in clause] for clause in data]
    except Exception:
        pass

    clause_matches = re.findall(r"\[([^\[\]]*)\]", raw)
    if clause_matches:
        clauses = []
        for cm in clause_matches:
            lits = [int(x) for x in re.findall(r"-?\d+", cm)]
            clauses.append(lits)
        return clauses

    clauses = []
    for line in raw.splitlines():
        line = line.strip()
        if not line or line.startswith("c") or line.startswith("p") or line.startswith("%") or line == "0":
            continue
        lits = [int(x) for x in line.split() if x != "0"]
        if lits:
            clauses.append(lits)
    return clauses


def is_pure_sat(raw: str) -> bool:
    raw = raw.strip()
    if not raw:
        return False

    if raw.startswith("["):
        try:
            data = ast.literal_eval(raw)
            if isinstance(data, list):
                if not data:
                    return True
                if all(isinstance(x, list) and all(isinstance(y, int) for y in x) for x in data):
                    return True
                if all(isinstance(f, list) and all(isinstance(c, list) and all(isinstance(y, int) for y in c) for c in f) for f in data):
                    return True
        except Exception:
            pass

    non_empty = [l.strip() for l in raw.splitlines() if l.strip()]
    if any(l.startswith("p cnf") for l in non_empty):
        return True

    bracket_matches = re.findall(r"\[([^\[\]]*)\]", raw)
    if bracket_matches and not any(re.search(r"[a-zA-Z_=<>!]", b) for b in bracket_matches):
        return True

    all_num_lines = True
    has_clauses = False
    for l in non_empty:
        if l.startswith("c") or l.startswith("%"):
            continue
        parts = l.split()
        if not parts:
            continue
        try:
            [int(x) for x in parts]
            has_clauses = True
        except ValueError:
            all_num_lines = False
            break

    return all_num_lines and has_clauses


def solve_sat(raw: str):
    try:
        data = ast.literal_eval(raw.strip())
        if isinstance(data, list):
            if data and isinstance(data[0], list) and data[0] and isinstance(data[0][0], list):
                for formula in data:
                    print(solve_cnf(formula))
                return
            print(solve_cnf(data))
            return
    except Exception:
        pass

    try:
        data = json.loads(raw.strip())
        if isinstance(data, list):
            if data and isinstance(data[0], list) and data[0] and isinstance(data[0][0], list):
                for formula in data:
                    print(solve_cnf(formula))
                return
            print(solve_cnf(data))
            return
    except Exception:
        pass

    lines = [line.strip() for line in raw.splitlines() if line.strip()]
    if lines and all(line.startswith("[") for line in lines) and len(lines) > 1:
        parsed_lines = []
        all_lines_parsed = True
        for line in lines:
            try:
                c = parse_cnf(line)
                if c:
                    parsed_lines.append(c)
                else:
                    all_lines_parsed = False
                    break
            except Exception:
                all_lines_parsed = False
                break

        if all_lines_parsed and len(parsed_lines) > 1:
            for c in parsed_lines:
                print(solve_cnf(c))
            return

    cnf = parse_cnf(raw)
    print(solve_cnf(cnf))


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

    def assert_not_equal(self, a: List[int], b: List[int]):
        diffs = [self.xor_gate(a[i], b[i]) for i in range(self.width)]
        self.add_clause(diffs)

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

    def assert_less_or_equal(self, a: List[int], b: List[int]):
        carry = self.TRUE
        for i in range(self.width):
            term1 = self.and_gate(b[i], -a[i])
            term2 = self.xor_gate(b[i], -a[i])
            term3 = self.and_gate(carry, term2)
            carry = self.or_gate(term1, term3)
        self.add_clause([carry])

    def assert_greater_or_equal(self, a: List[int], b: List[int]):
        self.assert_less_or_equal(b, a)

    def assert_relation(self, rel_op: str, a: List[int], b: List[int], is_positive: bool = True):
        if is_positive:
            if rel_op in ["=", "=="]:
                self.assert_equal(a, b)
            elif rel_op == "!=":
                self.assert_not_equal(a, b)
            elif rel_op == "<":
                self.assert_less_than(a, b)
            elif rel_op == ">":
                self.assert_greater_than(a, b)
            elif rel_op == "<=":
                self.assert_less_or_equal(a, b)
            elif rel_op == ">=":
                self.assert_greater_or_equal(a, b)
        else:
            if rel_op in ["=", "=="]:
                self.assert_not_equal(a, b)
            elif rel_op == "!=":
                self.assert_equal(a, b)
            elif rel_op == "<":
                self.assert_greater_or_equal(a, b)
            elif rel_op == ">":
                self.assert_less_or_equal(a, b)
            elif rel_op == "<=":
                self.assert_greater_than(a, b)
            elif rel_op == ">=":
                self.assert_less_than(a, b)


class Parser:
    def __init__(self, blaster: BitBlaster):
        self.bb = blaster

    @staticmethod
    def tokenize(text: str) -> List[str]:
        specials = ["==", "!=", "<=", ">=", "=", "<", ">", "(", ")", "~", "^", "&", "|", "+", "-"]
        pattern = "|".join(re.escape(s) for s in sorted(specials, key=len, reverse=True))
        pattern += r"|[a-zA-Z_][a-zA-Z0-9_]*|\d+"
        return re.findall(pattern, text)

    @staticmethod
    def find_op(tokens: List[str], ops: List[str]) -> int:
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

    @staticmethod
    def strip_parens(tokens: List[str]) -> List[str]:
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


def split_top_level(text: str, delimiter_regex: str) -> List[str]:
    parts = []
    current = []
    depth = 0
    i = 0
    while i < len(text):
        c = text[i]
        if c == "(":
            depth += 1
            current.append(c)
            i += 1
        elif c == ")":
            depth -= 1
            current.append(c)
            i += 1
        elif depth == 0:
            m = re.match(delimiter_regex, text[i:], re.IGNORECASE)
            if m:
                parts.append("".join(current).strip())
                current = []
                i += len(m.group(0))
            else:
                current.append(c)
                i += 1
        else:
            current.append(c)
            i += 1
    if current:
        parts.append("".join(current).strip())
    return [p for p in parts if p]


def parse_atom(atom_text: str, atom_registry: Dict[str, int], var_to_atom: Dict[int, Tuple[str, List[str], List[str]]]) -> int:
    atom_text = atom_text.strip()
    is_neg = False
    while True:
        if atom_text.startswith("not ") or atom_text.startswith("NOT "):
            is_neg = not is_neg
            atom_text = atom_text[4:].strip()
        elif atom_text.startswith("~") or atom_text.startswith("!"):
            is_neg = not is_neg
            atom_text = atom_text[1:].strip()
        elif atom_text.startswith("(") and atom_text.endswith(")"):
            depth = 0
            encloses = True
            for i in range(len(atom_text) - 1):
                if atom_text[i] == "(":
                    depth += 1
                elif atom_text[i] == ")":
                    depth -= 1
                if depth == 0:
                    encloses = False
                    break
            if encloses:
                atom_text = atom_text[1:-1].strip()
            else:
                break
        else:
            break

    tokens = Parser.tokenize(atom_text)
    rel_idx = Parser.find_op(tokens, ["<=", ">=", "==", "!=", "=", "<", ">"])
    if rel_idx != -1:
        rel_op = tokens[rel_idx]
        if rel_op == "=":
            rel_op = "=="
        left_tokens = tokens[:rel_idx]
        right_tokens = tokens[rel_idx + 1:]
        canonical_key = " ".join(left_tokens) + " " + rel_op + " " + " ".join(right_tokens)
        if canonical_key not in atom_registry:
            var_id = len(atom_registry) + 1
            atom_registry[canonical_key] = var_id
            var_to_atom[var_id] = (rel_op, left_tokens, right_tokens)
        var_id = atom_registry[canonical_key]
        return -var_id if is_neg else var_id
    else:
        canonical_key = " ".join(tokens)
        if canonical_key not in atom_registry:
            var_id = len(atom_registry) + 1
            atom_registry[canonical_key] = var_id
            var_to_atom[var_id] = ("==", tokens, ["1"])
        var_id = atom_registry[canonical_key]
        return -var_id if is_neg else var_id


def solve_smt(raw_input: str):
    lines = [line.strip() for line in raw_input.strip().splitlines() if line.strip()]
    if not lines:
        return

    width = 2
    raw_constraints = []

    for line in lines:
        if line.isdigit():
            width = int(line)
        elif re.match(r"^(?:width|bits)\s*[:=]?\s*(\d+)$", line, re.IGNORECASE):
            m = re.match(r"^(?:width|bits)\s*[:=]?\s*(\d+)$", line, re.IGNORECASE)
            if m:
                width = int(m.group(1))
        else:
            raw_constraints.append(line)

    if not any(l.isdigit() for l in lines):
        all_nums = [int(n) for n in re.findall(r"\b\d+\b", raw_input)]
        if all_nums:
            max_num = max(all_nums)
            width = max(width, max_num.bit_length())

    atom_registry: Dict[str, int] = {}
    var_to_atom: Dict[int, Tuple[str, List[str], List[str]]] = {}
    cnf: List[List[int]] = []

    for cline in raw_constraints:
        sub_constrs = cline.split(";")
        for sub in sub_constrs:
            sub = sub.strip()
            if not sub:
                continue
            and_parts = split_top_level(sub, r"^\s*(?:and|&&)\b\s*")
            for and_p in and_parts:
                or_parts = split_top_level(and_p, r"^\s*(?:or|\|\|)\b\s*")
                clause = []
                for or_p in or_parts:
                    lit = parse_atom(or_p, atom_registry, var_to_atom)
                    clause.append(lit)
                if clause:
                    cnf.append(clause)

    if not cnf:
        print("SAT")
        return

    # DPLL(T) architecture:
    # 1. First, check Boolean satisfiability with the SAT solver (DPLL) before theory solving!
    while True:
        sat, bool_model = dpll(cnf)
        if not sat or bool_model is None:
            print("UNSAT")
            return

        # 2. Theory check with BitBlaster
        blaster = BitBlaster(width)
        parser = Parser(blaster)

        active_vars = []
        theory_ok = True
        for var_id, atom_info in var_to_atom.items():
            val = bool_model.get(var_id, 0)
            is_pos = (val == 1)
            active_vars.append(var_id if is_pos else -var_id)
            rel_op, left_tokens, right_tokens = atom_info
            try:
                left_val = parser.eval_expr(left_tokens)
                right_val = parser.eval_expr(right_tokens)
                blaster.assert_relation(rel_op, left_val, right_val, is_positive=is_pos)
            except Exception:
                theory_ok = False
                break

        if theory_ok:
            theory_sat, theory_model = dpll(blaster.clauses)
            if theory_sat and theory_model is not None:
                print("SAT")
                results = []
                for name in sorted(blaster.variables.keys()):
                    bits = blaster.variables[name]
                    bit_chars = []
                    for b in reversed(bits):
                        if b == blaster.TRUE:
                            v = 1
                        elif b == -blaster.TRUE:
                            v = 0
                        else:
                            v = theory_model.get(abs(b), 0)
                            if b < 0:
                                v = 1 - v
                        bit_chars.append(str(v))
                    results.append(f"{name} = {''.join(bit_chars)}")
                if results:
                    sys.stderr.write(", ".join(results) + "\n")
                return

        # If theory assignment is inconsistent, learn conflict clause and repeat DPLL
        conflict = [-lit for lit in active_vars]
        cnf.append(conflict)


def solve(raw_input: str):
    if is_pure_sat(raw_input):
        solve_sat(raw_input)
    else:
        solve_smt(raw_input)


def main():
    raw = sys.stdin.read().strip()
    if raw:
        solve(raw)


if __name__ == "__main__":
    main()
