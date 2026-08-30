# Sudoku — solver & generator (Z3)

A companion to the Mastermind solver in this repo, built on the **same idea**:
model the board as boolean constraints and let the [Z3](https://github.com/Z3Prover/z3)
SMT solver do the reasoning. It **solves** any given puzzle and **generates**
new ones that are guaranteed to have a unique solution.

## Files

| File | What it is |
|------|------------|
| `sudoku_solver.py` | `SudokuSolver` class (solve + count solutions), a puzzle generator, and grid/text helpers. Runnable CLI. |
| `test_sudoku.py`   | Tests: solve a known puzzle, check legality, uniqueness detection, and that generated puzzles are uniquely solvable. |

## Setup

Same dependency as the rest of the repo:

```bash
pip install -r requirements.txt
```

## Solve a puzzle

Give it a puzzle as an 81-character string (`.` or `0` for blanks; whitespace is
ignored), or point it at a file:

```bash
python sudoku_solver.py --mode solve --count \
  --puzzle "53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79"
```

```
Puzzle (30 clues):

5 3 . | . 7 . | . . .
6 . . | 1 9 5 | . . .
. 9 8 | . . . | . 6 .
------+-------+-------
...

Solutions: unique solution

Solution:

5 3 4 | 6 7 8 | 9 1 2
6 7 2 | 1 9 5 | 3 4 8
...
```

`--count` additionally reports whether the puzzle has **no**, **one**, or **2+**
solutions. Read a puzzle from a file with `--file puzzle.txt`.

## Generate a puzzle

```bash
python sudoku_solver.py --mode generate --seed 7
```

Prints a puzzle (with its clue count), a one-line form you can paste back into
`--puzzle`, and the solution. `--seed` makes it reproducible; `--min-clues N`
stops removing cells once `N` clues remain (fewer clues ≈ harder, down to the
minimum that stays unique).

## How it works — the encoding

One boolean per `(row, col, digit)`:

> `var(r, c, d)`  =  *"cell (r, c) holds digit d"*

This is exactly the Mastermind `var(position, color)` idea with one extra
dimension. Four constraint families cover the rules — each is an **exactly-one**
count (expressed with Z3's `PbEq` pseudo-boolean equality):

1. each **cell** holds exactly one digit,
2. each **digit** appears exactly once per **row**,
3. each **digit** appears exactly once per **column**,
4. each **digit** appears exactly once per **box** (the `b×b` sub-square).

Rules 2–3 are the Mastermind "each color used at most once" constraint applied
along rows and columns; rule 4 (the box) is the only genuinely new idea.

### Solving
Add the given clues as unit constraints (`var(r, c, clue) == true`) and ask Z3
for a model. Reading the true variables back out gives the completed grid. If no
model exists, the clues are contradictory.

### Counting / uniqueness
To check uniqueness we solve, then add a **blocking clause** — "the solution is
not this exact assignment" — and solve again. If the second solve is `unsat`,
the puzzle is unique. We stop at a cap of 2, since one alternative is all we need
to prove non-uniqueness.

### Generating (this uses the solver twice)
1. **Random full solution.** Seed the three diagonal boxes with independent
   random permutations (they share no row, column, or box, so any filling is
   legal), then let Z3 complete the rest. Different seeds → different grids.
2. **Dig holes.** Walk the 81 cells in random order; blank each one and re-check
   uniqueness. Keep the blank only if the puzzle *still* has exactly one
   solution; otherwise restore the digit. The result is a puzzle you can't
   reduce further without making it ambiguous.

So generation is not a lookup or a template — every puzzle is carved out of a
freshly-solved random grid, with the solver itself acting as the referee that
guarantees a unique answer.

## Configurable board size

`--box` sets the sub-square size; the grid is `box*box` per side. Default `3`
(the usual 9×9). `--box 2` gives a 4×4 "Shidoku"; larger boxes work but get slow,
and the text `--puzzle` parser only handles single-digit grids (n ≤ 9).

## Tests

```bash
python test_sudoku.py
```

Solves a known puzzle and checks the solution is legal and preserves the clues;
confirms uniqueness detection on unique / empty / contradictory grids; and
generates several puzzles, asserting each is uniquely solvable and that solving
it recovers the intended solution.

## Notes

- **Solving is complete and exact** — Z3 either returns the solution or proves
  there is none. There's no guessing or backtracking heuristic to tune.
- The diagonal-box seeding gives good variety for a demo; it is not a uniform
  sample over all valid grids (that's a harder problem and not the point here).
