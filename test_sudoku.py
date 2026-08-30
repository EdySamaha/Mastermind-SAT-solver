"""Tests for the Sudoku solver/generator — plain asserts, no framework.

    python test_sudoku.py

Covers: solving a known puzzle, solution legality, uniqueness counting
(unique / ambiguous / impossible), and that generated puzzles are uniquely
solvable and that solving one recovers the intended solution.
"""

from __future__ import annotations

import random

from sudoku_solver import (SudokuSolver, format_grid, is_valid_solution,
                           parse_grid, to_line)

# A well-known puzzle with a single solution.
PUZZLE = ("53..7...."
          "6..195..."
          ".98....6."
          "8...6...3"
          "4..8.3..1"
          "7...2...6"
          ".6....28."
          "...419..5"
          "....8..79")

SOLUTION = ("534678912"
            "672195348"
            "198342567"
            "859761423"
            "426853791"
            "713924856"
            "961537284"
            "287419635"
            "345286179")


def test_solve_known() -> None:
    solver = SudokuSolver()
    grid = parse_grid(PUZZLE)
    sol = solver.solve(grid)
    assert sol is not None, "known puzzle should solve"
    assert to_line(sol) == to_line(parse_grid(SOLUTION)), "wrong solution"
    assert is_valid_solution(sol), "solution breaks Sudoku rules"
    # Clues must be preserved.
    for r in range(9):
        for c in range(9):
            if grid[r][c]:
                assert sol[r][c] == grid[r][c]
    print("[solve] known 9x9 puzzle solved correctly and legally.")


def test_uniqueness() -> None:
    solver = SudokuSolver()
    assert solver.count_solutions(parse_grid(PUZZLE), cap=2) == 1, \
        "proper puzzle should be unique"
    # Empty grid has astronomically many solutions -> cap hit at 2.
    empty = [[0] * 9 for _ in range(9)]
    assert solver.count_solutions(empty, cap=2) == 2, "empty grid should be 2+"
    # Contradiction: two 5s in the top row -> no solution.
    bad = [[0] * 9 for _ in range(9)]
    bad[0][0] = 5
    bad[0][1] = 5
    assert solver.count_solutions(bad, cap=2) == 0, "illegal clues -> 0"
    print("[uniqueness] unique / ambiguous / impossible all detected.")


def test_generate() -> None:
    solver = SudokuSolver()
    for seed in range(4):
        rng = random.Random(seed)
        puzzle, solution = solver.generate(rng)
        assert is_valid_solution(solution), "generated solution illegal"
        assert solver.count_solutions(puzzle, cap=2) == 1, \
            "generated puzzle must be uniquely solvable"
        recovered = solver.solve(puzzle)
        assert to_line(recovered) == to_line(solution), \
            "solving the generated puzzle must recover the solution"
        clues = sum(1 for row in puzzle for v in row if v)
        # Puzzle clues must be a subset of the solution.
        for r in range(9):
            for c in range(9):
                if puzzle[r][c]:
                    assert puzzle[r][c] == solution[r][c]
        print(f"[generate] seed {seed}: {clues} clues, unique, recovers solution.")


def test_roundtrip() -> None:
    grid = parse_grid(PUZZLE)
    assert to_line(grid) == PUZZLE.replace("0", "."), "line round-trip failed"
    # parse(format-free line) is stable
    assert to_line(parse_grid(to_line(grid))) == to_line(grid)
    print("[roundtrip] parse_grid / to_line are consistent.")


if __name__ == "__main__":
    test_solve_known()
    test_uniqueness()
    test_roundtrip()
    test_generate()
    print("\nAll Sudoku tests passed.")
