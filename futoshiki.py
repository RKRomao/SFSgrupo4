"""
Resolução e Validação do Puzzle Futoshiki 5x5 com Z3.

Variáveis do tabuleiro:
[a, b, c, d, e]
[f, g, h, i, j]
[k, l, m, n, o]
[p, q, r, s, t]
[u, v, w, x, y]

Restrições:
- a > b
- c > d > e
- j = 2
- f = 4
- m = 4
- s < t
- t = 4
- u < v < w
- Cada linha e cada coluna contém os números de 1 a 5 sem repetições.
"""

import sys
from z3 import Ints, Solver, Distinct, sat

if hasattr(sys.stdout, "reconfigure"):
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass


def get_futoshiki_solver():
    """
    Cria e configura o solver Z3 com as variáveis e restrições do Futoshiki uma única vez.
    Retorna o solver e a grelha simbólica.
    """
    a, b, c, d, e = Ints('a b c d e')
    f, g, h, i, j = Ints('f g h i j')
    k, l, m, n, o = Ints('k l m n o')
    p, q, r, s, t = Ints('p q r s t')
    u, v, w, x, y = Ints('u v w x y')

    grid = [
        [a, b, c, d, e],
        [f, g, h, i, j],
        [k, l, m, n, o],
        [p, q, r, s, t],
        [u, v, w, x, y]
    ]

    solver = Solver()

    # Domínio: intervalo [1, 5]
    for row in grid:
        for cell in row:
            solver.add(cell >= 1, cell <= 5)

    # Linhas distintas
    for row in grid:
        solver.add(Distinct(row))

    # Colunas distintas
    for col in zip(*grid):
        solver.add(Distinct(list(col)))

    # Restrições do problema (valores fixos e desigualdades)
    solver.add(a > b)
    solver.add(c > d, d > e)
    solver.add(j == 2, f == 4, m == 4, t == 4)
    solver.add(s < t)
    solver.add(u < v, v < w)

    return solver, grid


def check(board):
    """
    Valida se um dado tabuleiro satisfaz todas as restrições com Z3.
    Reutiliza as restrições base sem código duplicado.
    """
    if not board or len(board) != 5 or any(len(row) != 5 for row in board):
        return False

    solver, grid = get_futoshiki_solver()
    for r in range(5):
        for c in range(5):
            solver.add(grid[r][c] == int(board[r][c]))

    return solver.check() == sat


# 1. Encontra a solução utilizando o Z3
solver, grid = get_futoshiki_solver()

if solver.check() == sat:
    model = solver.model()

    # Atribuição individual às variáveis descritas no exercício
    a, b, c, d, e = [model[cell].as_long() for cell in grid[0]]
    f, g, h, i, j = [model[cell].as_long() for cell in grid[1]]
    k, l, m, n, o = [model[cell].as_long() for cell in grid[2]]
    p, q, r, s, t = [model[cell].as_long() for cell in grid[3]]
    u, v, w, x, y = [model[cell].as_long() for cell in grid[4]]

    board = [
        [a, b, c, d, e],
        [f, g, h, i, j],
        [k, l, m, n, o],
        [p, q, r, s, t],
        [u, v, w, x, y]
    ]
else:
    board = []


if __name__ == "__main__":
    print("Tabuleiro:")
    for row in board:
        print(row)

    print("\nValores das variáveis:")
    print(f"a={a}, b={b}, c={c}, d={d}, e={e}")
    print(f"f={f}, g={g}, h={h}, i={i}, j={j}")
    print(f"k={k}, l={l}, m={m}, n={n}, o={o}")
    print(f"p={p}, q={q}, r={r}, s={s}, t={t}")
    print(f"u={u}, v={v}, w={w}, x={x}, y={y}")

    print("\ncheck(board) validado com Z3:")
    print(check(board))  # True
