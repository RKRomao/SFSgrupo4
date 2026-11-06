"""
Script utilitário para codificar um tabuleiro de Futoshiki
na linguagem SMT / Bit-Vectors do projeto e apresentar a solução resolvida.
"""

import subprocess
import sys


def solve_futoshiki(n, clues_fixed, clues_lt):
    """
    n: tamanho da grelha (ex: 4 para 4x4)
    clues_fixed: dicionario com {(r, c): valor} (1-based)
    clues_lt: lista de pares [((r1, c1), (r2, c2))] representando cell1 < cell2
    """
    # 3 bits chegam para representar números até 4 (0..7).
    # Para n=5 ou n=8, 4 bits chegam (0..15).
    bit_width = max(2, (n + 1).bit_length())

    lines = [str(bit_width)]

    # 1. Restrições de Domínio: 0 < x_rc e x_rc < n+1 (para garantir que 1 <= x_rc <= n)
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            lines.append(f"0 < x_{r}{c}")
            lines.append(f"x_{r}{c} < {n + 1}")

    # 2. Restrições de Linha: todos os elementos da mesma linha são distintos
    for r in range(1, n + 1):
        for c1 in range(1, n + 1):
            for c2 in range(c1 + 1, n + 1):
                lines.append(f"!(x_{r}{c1} = x_{r}{c2})")

    # 3. Restrições de Coluna: todos os elementos da mesma coluna são distintos
    for c in range(1, n + 1):
        for r1 in range(1, n + 1):
            for r2 in range(r1 + 1, n + 1):
                lines.append(f"!(x_{r1}{c} = x_{r2}{c})")

    # 4. Células pré-preenchidas
    for (r, c), val in clues_fixed.items():
        lines.append(f"x_{r}{c} = {val}")

    # 5. Desigualdades (célula1 < célula2)
    for (r1, c1), (r2, c2) in clues_lt:
        lines.append(f"x_{r1}{c1} < x_{r2}{c2}")

    input_text = "\n".join(lines)

    # Executar o solver
    p = subprocess.Popen(
        [sys.executable, "submission.py"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    stdout, stderr = p.communicate(input_text)

    if "SAT" not in stdout:
        print("UNSAT: O tabuleiro não tem solução válida.")
        return None

    # Extrair modelo binário do stderr
    # Exemplo: x_11 = 001, x_12 = 100, ...
    grid = [[0] * n for _ in range(n)]
    for item in stderr.strip().split(","):
        item = item.strip()
        if not item or "=" not in item:
            continue
        var_name, bin_val = [x.strip() for x in item.split("=")]
        if var_name.startswith("x_"):
            parts = var_name[2:]
            r = int(parts[0]) - 1
            c = int(parts[1]) - 1
            int_val = int(bin_val, 2)
            grid[r][c] = int_val

    return grid, input_text


def print_grid(grid):
    n = len(grid)
    sep = "+---" * n + "+"
    print(sep)
    for row in grid:
        print("| " + " | ".join(str(val) for val in row) + " |")
        print(sep)


if __name__ == "__main__":
    # Exemplo concreto 4x4
    N = 4
    fixed = {
        (4, 1): 4,
        (3, 4): 1,
    }
    # Lista de desigualdades: cell_a < cell_b
    lt_inequalities = [
        ((1, 1), (1, 2)),  # x_11 < x_12
        ((1, 4), (1, 3)),  # x_14 < x_13 (ou x_13 > x_14)
        ((1, 1), (2, 1)),  # x_11 < x_21
        ((2, 1), (3, 1)),  # x_21 < x_31
        ((2, 3), (2, 4)),  # x_23 < x_24
        ((3, 2), (3, 3)),  # x_32 < x_33
    ]

    print("A resolver o Futoshiki 4x4 através do SMT Bit-Vector Solver...")
    result = solve_futoshiki(N, fixed, lt_inequalities)
    if result:
        grid, smt_code = result
        print("\n=== Solução Encontrada ===")
        print_grid(grid)

