import ast
import json
import re
import sys
from typing import List, Dict, Optional, Tuple, Set


def simplify(cnf: List[List[int]], literal: int) -> List[List[int]]:
    neg_literal = -literal
    new_cnf = []
    for clause in cnf:
        if literal in clause:
            continue
        new_cnf.append([lit for lit in clause if lit != neg_literal])
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


def main():
    raw = sys.stdin.read().strip()
    if not raw:
        return

    try:
        data = ast.literal_eval(raw)
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
        data = json.loads(raw)
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


if __name__ == "__main__":
    main()