"""Sudoku via the Z3 SMT solver — solve given puzzles, and generate new ones.

The encoding is the same idea as the Mastermind solver in this repo, with one
extra dimension. There we had one boolean per ``(position, color)``; here we
have one boolean per ``(row, col, digit)``:

    var(r, c, d)  ==  "cell (r, c) holds digit d"

Base rules (a standard Sudoku of box size ``b`` has an ``n = b*b`` grid):

    - each cell holds exactly one digit
    - each digit appears exactly once per row
    - each digit appears exactly once per column
    - each digit appears exactly once per b*b box

**Solving** a puzzle is just adding the given clues as extra constraints and
asking Z3 for a model. **Generating** a puzzle *uses* the solver: build a random
full solution, then blank out cells for as long as the solution stays unique
(checked by asking the solver for a *second* solution and getting `unsat`).

    python sudoku_solver.py --mode solve --puzzle 53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79
    python sudoku_solver.py --mode generate --seed 1
    python sudoku_solver.py --mode solve --file puzzle.txt --count
"""

from __future__ import annotations

import random
from typing import List, Optional, Sequence, Tuple

import z3

Grid = List[List[int]]  # 0 = blank


class SudokuSolver:
    """Z3 model of a Sudoku board. Reusable across many solve/count calls."""

    def __init__(self, box: int = 3) -> None:
        self.box = box
        self.n = box * box
        n = self.n
        # vars[r][c][d-1] : Bool "cell (r,c) holds digit d"  (d in 1..n)
        self.vars = [[[z3.Bool(f"x_{r}_{c}_{d}") for d in range(1, n + 1)]
                      for c in range(n)] for r in range(n)]
        self.solver = z3.Solver()
        self._add_base_constraints()

    # -- helpers ---------------------------------------------------------- #
    @staticmethod
    def _exactly_one(bools: Sequence[z3.BoolRef]) -> z3.BoolRef:
        return z3.PbEq([(b, 1) for b in bools], 1)

    def _cell(self, r: int, c: int) -> List[z3.BoolRef]:
        return self.vars[r][c]

    # -- constraints ------------------------------------------------------ #
    def _add_base_constraints(self) -> None:
        n, box = self.n, self.box
        # Each cell holds exactly one digit.
        for r in range(n):
            for c in range(n):
                self.solver.add(self._exactly_one(self._cell(r, c)))
        # Each digit exactly once per row and per column.
        for d in range(n):
            for r in range(n):
                self.solver.add(self._exactly_one(
                    [self.vars[r][c][d] for c in range(n)]))
            for c in range(n):
                self.solver.add(self._exactly_one(
                    [self.vars[r][c][d] for r in range(n)]))
        # Each digit exactly once per box.
        for br in range(0, n, box):
            for bc in range(0, n, box):
                for d in range(n):
                    cells = [self.vars[r][c][d]
                             for r in range(br, br + box)
                             for c in range(bc, bc + box)]
                    self.solver.add(self._exactly_one(cells))

    def _clue_terms(self, grid: Grid) -> List[z3.BoolRef]:
        """Constraints pinning the given (non-blank) cells to their digits."""
        terms = []
        for r in range(self.n):
            for c in range(self.n):
                d = grid[r][c]
                if d:
                    terms.append(self.vars[r][c][d - 1])
        return terms

    def _read_model(self, model: z3.ModelRef) -> Grid:
        n = self.n
        out = [[0] * n for _ in range(n)]
        for r in range(n):
            for c in range(n):
                for d in range(n):
                    if z3.is_true(model.evaluate(self.vars[r][c][d],
                                                 model_completion=True)):
                        out[r][c] = d + 1
                        break
        return out

    # -- public API ------------------------------------------------------- #
    def solve(self, grid: Grid) -> Optional[Grid]:
        """Return a completed grid consistent with `grid`, or None if none."""
        self.solver.push()
        for term in self._clue_terms(grid):
            self.solver.add(term)
        result = self.solver.check()
        out = self._read_model(self.solver.model()) if result == z3.sat else None
        self.solver.pop()
        return out

    def count_solutions(self, grid: Grid, cap: int = 2) -> int:
        """Count solutions up to `cap` (stops early — 2 is enough for
        uniqueness). Returns 0 (impossible), 1 (unique), or >=2 (ambiguous)."""
        self.solver.push()
        for term in self._clue_terms(grid):
            self.solver.add(term)
        found = 0
        while found < cap and self.solver.check() == z3.sat:
            model = self.solver.model()
            found += 1
            # Block this exact solution, then look for another.
            block = [self.vars[r][c][d]
                     for r in range(self.n) for c in range(self.n)
                     for d in range(self.n)
                     if z3.is_true(model.evaluate(self.vars[r][c][d],
                                                  model_completion=True))]
            self.solver.add(z3.Not(z3.And(block)))
        self.solver.pop()
        return found

    # -- generation (uses the solver above) ------------------------------- #
    def random_full(self, rng: random.Random) -> Grid:
        """A random complete solution: seed the diagonal boxes with random
        permutations (they don't constrain each other), then let Z3 complete."""
        n, box = self.n, self.box
        grid = [[0] * n for _ in range(n)]
        for b in range(box):
            digits = list(range(1, n + 1))
            rng.shuffle(digits)
            i = 0
            for r in range(b * box, b * box + box):
                for c in range(b * box, b * box + box):
                    grid[r][c] = digits[i]
                    i += 1
        full = self.solve(grid)
        assert full is not None, "diagonal-seeded grid should always complete"
        return full

    def generate(self, rng: random.Random,
                 min_clues: Optional[int] = None) -> Tuple[Grid, Grid]:
        """Return ``(puzzle, solution)``. Blanks out cells in random order,
        keeping a blank only if the puzzle still has a unique solution. Stops
        once `min_clues` clues remain (if given), else digs as far as it can."""
        solution = self.random_full(rng)
        puzzle = [row[:] for row in solution]
        cells = [(r, c) for r in range(self.n) for c in range(self.n)]
        rng.shuffle(cells)
        clues = self.n * self.n
        for r, c in cells:
            if min_clues is not None and clues <= min_clues:
                break
            saved = puzzle[r][c]
            puzzle[r][c] = 0
            if self.count_solutions(puzzle, cap=2) == 1:
                clues -= 1              # removal kept it unique — leave blank
            else:
                puzzle[r][c] = saved    # removal broke uniqueness — restore
        return puzzle, solution


# --------------------------------------------------------------------------- #
# Grid <-> text
# --------------------------------------------------------------------------- #

def parse_grid(text: str, box: int = 3) -> Grid:
    """Parse an 81-char (for 9x9) string. '0' or '.' are blanks; other
    whitespace is ignored. Only single-digit cells (n <= 9) are supported."""
    n = box * box
    if n > 9:
        raise ValueError("text parsing only supports n <= 9 (single digits)")
    chars = [ch for ch in text if not ch.isspace()]
    cleaned = [("0" if ch == "." else ch) for ch in chars]
    if len(cleaned) != n * n:
        raise ValueError(f"expected {n * n} cells, got {len(cleaned)}")
    grid = [[0] * n for _ in range(n)]
    for i, ch in enumerate(cleaned):
        if not ch.isdigit() or not (0 <= int(ch) <= n):
            raise ValueError(f"bad cell {ch!r}")
        grid[i // n][i % n] = int(ch)
    return grid


def format_grid(grid: Grid, box: int = 3) -> str:
    """Pretty grid with box separators (for n <= 9)."""
    n = box * box
    width = len(str(n))
    lines = []
    for r in range(n):
        if r and r % box == 0:
            sep = "+".join("-" * ((width + 1) * box + 1) for _ in range(box))
            lines.append(sep[1:])
        row = []
        for c in range(n):
            if c and c % box == 0:
                row.append("|")
            v = grid[r][c]
            row.append(f"{v if v else '.':>{width}}")
        lines.append(" ".join(row))
    return "\n".join(lines)


def to_line(grid: Grid) -> str:
    """One-line form ('.' for blanks) — round-trips with parse_grid."""
    return "".join(str(v) if v else "." for row in grid for v in row)


def is_valid_solution(grid: Grid, box: int = 3) -> bool:
    """True iff `grid` is a fully-filled, rule-legal Sudoku (used by tests)."""
    n = box * box
    full = set(range(1, n + 1))
    for r in range(n):
        if {grid[r][c] for c in range(n)} != full:
            return False
    for c in range(n):
        if {grid[r][c] for r in range(n)} != full:
            return False
    for br in range(0, n, box):
        for bc in range(0, n, box):
            block = {grid[r][c] for r in range(br, br + box)
                     for c in range(bc, bc + box)}
            if block != full:
                return False
    return True


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #

def _count_clues(grid: Grid) -> int:
    return sum(1 for row in grid for v in row if v)


if __name__ == "__main__":
    import argparse
    import sys

    p = argparse.ArgumentParser(description="Z3-based Sudoku solver/generator.")
    p.add_argument("--mode", choices=["solve", "generate"], default="solve")
    p.add_argument("--box", type=int, default=3,
                   help="box size; grid is box*box per side (default 3 -> 9x9)")
    p.add_argument("--puzzle", type=str, default=None,
                   help="solve mode: puzzle as an 81-char string ('.'/0 blanks)")
    p.add_argument("--file", type=str, default=None,
                   help="solve mode: read the puzzle from this file")
    p.add_argument("--count", action="store_true",
                   help="solve mode: also report how many solutions exist")
    p.add_argument("--seed", type=int, default=None,
                   help="generate mode: RNG seed for a reproducible puzzle")
    p.add_argument("--min-clues", type=int, default=None,
                   help="generate mode: stop removing once this many clues remain")
    args = p.parse_args()

    solver = SudokuSolver(args.box)

    if args.mode == "generate":
        rng = random.Random(args.seed)
        puzzle, solution = solver.generate(rng, min_clues=args.min_clues)
        print(f"Puzzle ({_count_clues(puzzle)} clues):\n")
        print(format_grid(puzzle, args.box))
        print("\nOne-line:", to_line(puzzle))
        print("\nSolution:\n")
        print(format_grid(solution, args.box))
        sys.exit(0)

    # solve mode
    if args.puzzle:
        text = args.puzzle
    elif args.file:
        with open(args.file, encoding="utf-8") as fh:
            text = fh.read()
    else:
        print("solve mode needs --puzzle or --file", file=sys.stderr)
        sys.exit(2)

    grid = parse_grid(text, args.box)
    print(f"Puzzle ({_count_clues(grid)} clues):\n")
    print(format_grid(grid, args.box))
    if args.count:
        n = solver.count_solutions(grid, cap=2)
        label = {0: "no solutions", 1: "unique solution"}.get(n, "2+ solutions")
        print(f"\nSolutions: {label}")
    solution = solver.solve(grid)
    if solution is None:
        print("\nNo solution — the clues are contradictory.")
        sys.exit(1)
    print("\nSolution:\n")
    print(format_grid(solution, args.box))
