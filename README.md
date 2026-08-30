# Mastermind — game + Z3 constraint solver

A playable Mastermind game and an automatic **code-breaker** that models the
board as a set of boolean constraints and lets the [Z3](https://github.com/Z3Prover/z3)
SMT solver do the deduction. Fully configurable board: `positions` pins drawn
from `colors` distinct colors, **no color repeats** (the palette can be larger
than the board, so some colors go unused).

## Files

| File | What it is |
|------|------------|
| `mastermind_game.py`   | Playable human game **and** the shared `random_secret` / `score` helpers the solver and tests import. |
| `mastermind_solver.py` | The `MastermindSolver` class plus self-play and interactive code-breaker loops. |
| `test_solver.py`       | Test harness: cross-checks `score` against a brute-force reference, then plays hundreds of random games and asserts every one is solved. |
| `requirements.txt`     | `z3-solver` (pinned to the tested version). |

## Setup

```bash
pip install -r requirements.txt
```

## Play as a human

```bash
python mastermind_game.py --positions 4 --colors 8      # defaults
```

Guess the sequence of distinct colors; after each guess you're told how many are
**correct and in place** (black) and **correct but out of place** (white).

## Run the solver

Self-play — the solver invents a secret and breaks it, printing each guess:

```bash
python mastermind_solver.py --mode self --positions 5 --colors 6 --seed 1
```

```
  guess  1: 42613  ->  0 black, 4 white
  guess  2: 61352  ->  0 black, 4 white
  guess  3: 13546  ->  0 black, 4 white
  guess  4: 35264  ->  3 black, 1 white
  guess  5: 35124  ->  3 black, 1 white
  guess  6: 25164  ->  5 black, 0 white
  solved in 6 guesses: 25164
```

Interactive — you hold a secret in your head, the solver guesses and you type the
`blacks whites` feedback each round:

```bash
python mastermind_solver.py --mode interactive --positions 5 --colors 6
```

Force a specific secret in self-play with `--secret 2-5-1-6-4` (or `25164` when
every color is a single digit).

## How it works — the encoding

One boolean variable per `(position, color)` pair:

> `var(p, c)`  =  *"position `p` holds color `c`"*

**Base rules** (the no-duplicates variant):

- each position holds **exactly one** color — `Sum_c If(var(p,c),1,0) == 1`;
- each color is used **at most once** — `Sum_p If(var(p,c),1,0) <= 1`.

The key idea is that any feedback `(blacks, whites)` for a guess `g` collapses
into just **two counting constraints** — there is no separate rule per outcome:

- **black pegs** (right color, right place):
  `Sum_p If(var(p, g[p]), 1, 0) == blacks`
- **total color matches** (black + white): for each color `c` in the guess,
  `present_c = Or_p var(p, c)`; then
  `Sum_c If(present_c, 1, 0) == blacks + whites`.
  (Valid because a guess uses distinct colors, so each shared color is counted
  once.)

The code-breaker is then a loop: ask Z3 for **any** board consistent with all the
feedback so far, play it, score it, add the two constraints, and repeat until it
scores all-black. If the feedback is ever mutually contradictory the solver
reports that no consistent sequence exists.

## Strategy and guess counts

This is a **consistent-guess** strategy: every guess is some assignment that
satisfies all feedback received. It is guaranteed to converge, but it is **not**
Knuth's minimax-optimal strategy — it doesn't pick the guess that minimizes the
worst-case remaining candidates. In practice it's still tight. Measured over 300
random games each (`test_solver.py`):

| Board (positions, colors) | Avg guesses | Worst |
|---|---|---|
| (5, 6) | 4.93 | 8 |
| (5, 5) — permutation | 4.56 | 8 |
| (4, 8) | 4.80 | 7 |

## Tests

```bash
python test_solver.py
```

Cross-checks `score` on every guess/secret pair for several small boards
(~130k pairs), then plays 300 random games each on `(5,6)`, `(5,5)`, and `(4,8)`,
asserting every game is solved and the recovered sequence equals the secret.

## Also in this repo: a Sudoku solver

The same boolean-grid + Z3 technique extends naturally to Sudoku — `var(r,c,d)`
("cell (r,c) holds digit d") in place of `var(position,color)`. `sudoku_solver.py`
**solves** any given puzzle (and can prove its solution is unique) and
**generates** new puzzles with a guaranteed-unique solution. See
[SUDOKU.md](SUDOKU.md).

## Documentation

- [Z3 for Python](https://ericpony.github.io/z3py-tutorial/guide-examples.htm)
