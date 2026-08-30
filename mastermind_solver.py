"""A Mastermind code-breaker built on the Z3 SMT solver.

The board is modelled with one boolean per (position, color):

    var(p, c)  ==  "position p holds color c"

Base rules (the no-duplicates variant): every position holds exactly one color,
and every color is used at most once.

The whole point — and what makes this scale — is that any feedback
``(blacks, whites)`` for a guess collapses into just two counting constraints,
so we never need a separate rule per outcome:

    blacks : sum over positions p of var(p, guess[p])              == blacks
    total  : sum over colors c in the guess of  OR_p var(p, c)     == blacks + whites
             (i.e. how many of the guessed colors appear anywhere in the secret)

The code-breaker is then a loop: ask Z3 for any board consistent with all the
feedback so far, play it, fold in the new feedback, repeat until solved. This
always converges; it is not guaranteed to be guess-minimal (see the README).

    python mastermind_solver.py --mode self --positions 5 --colors 6 --seed 1
    python mastermind_solver.py --mode interactive --positions 5 --colors 6
"""

from __future__ import annotations

import random
from typing import List, Optional, Sequence, Tuple

import z3

import mastermind_game as game


class MastermindSolver:
    """Maintains the Z3 constraints and proposes consistent guesses."""

    def __init__(self, positions: int, colors: int) -> None:
        if colors < positions:
            raise ValueError("colors must be >= positions (no duplicates)")
        self.positions = positions
        self.colors = list(range(1, colors + 1))
        self._cidx = {c: i for i, c in enumerate(self.colors)}
        self.solver = z3.Solver()
        # vars[p][i] -> Bool "position p holds the color self.colors[i]"
        self.vars: List[List[z3.BoolRef]] = [
            [z3.Bool(f"p{p}_c{c}") for c in self.colors]
            for p in range(positions)
        ]
        self._add_base_constraints()

    # -- helpers ---------------------------------------------------------- #
    def _var(self, pos: int, color: int) -> z3.BoolRef:
        return self.vars[pos][self._cidx[color]]

    @staticmethod
    def _count(bools: Sequence[z3.BoolRef]) -> z3.ArithRef:
        """Number of true booleans in `bools`, as a Z3 integer term."""
        return z3.Sum([z3.If(b, 1, 0) for b in bools])

    # -- constraints ------------------------------------------------------ #
    def _add_base_constraints(self) -> None:
        # Each position holds exactly one color.
        for p in range(self.positions):
            self.solver.add(self._count(self.vars[p]) == 1)
        # Each color is used at most once (no duplicates).
        for i in range(len(self.colors)):
            column = [self.vars[p][i] for p in range(self.positions)]
            self.solver.add(self._count(column) <= 1)

    def add_feedback(self, guess: Sequence[int], blacks: int, whites: int) -> None:
        """Constrain the secret to be consistent with one scored guess."""
        # Right color AND right place.
        self.solver.add(
            self._count([self._var(p, guess[p]) for p in range(self.positions)])
            == blacks
        )
        # How many guessed colors appear anywhere in the secret == blacks+whites.
        present = [z3.Or([self._var(p, c) for p in range(self.positions)])
                   for c in guess]
        self.solver.add(self._count(present) == blacks + whites)

    # -- querying --------------------------------------------------------- #
    def next_guess(self) -> Optional[Sequence[int]]:
        """A board consistent with all feedback so far, or None if impossible."""
        if self.solver.check() != z3.sat:
            return None
        model = self.solver.model()
        guess: List[int] = [0] * self.positions
        for p in range(self.positions):
            for i, c in enumerate(self.colors):
                if z3.is_true(model.evaluate(self.vars[p][i],
                                             model_completion=True)):
                    guess[p] = c
                    break
        return tuple(guess)


# --------------------------------------------------------------------------- #
# Play loops
# --------------------------------------------------------------------------- #

def _fmt(seq: Sequence[int]) -> str:
    return "".join(map(str, seq)) if max(seq, default=0) <= 9 else str(tuple(seq))


def solve_self(positions: int, colors: int,
               secret: Optional[Sequence[int]] = None,
               seed: Optional[int] = None,
               verbose: bool = True) -> Tuple[int, Sequence[int]]:
    """Self-play: the solver breaks a (given or random) secret automatically.

    Returns ``(num_guesses, secret)``. Raises if the feedback ever becomes
    contradictory (which would indicate a scoring/encoding bug)."""
    rng = random.Random(seed)
    if secret is None:
        secret = game.random_secret(positions, colors, rng)
    solver = MastermindSolver(positions, colors)
    guesses = 0
    while True:
        guess = solver.next_guess()
        if guess is None:
            raise RuntimeError("no candidate consistent with feedback — "
                               "scoring/encoding bug?")
        guesses += 1
        blacks, whites = game.score(guess, secret)
        if verbose:
            print(f"  guess {guesses:2d}: {_fmt(guess)}  ->  "
                  f"{blacks} black, {whites} white")
        if blacks == positions:
            if verbose:
                print(f"  solved in {guesses} guesses: {_fmt(guess)}")
            return guesses, guess
        solver.add_feedback(guess, blacks, whites)


def solve_interactive(positions: int, colors: int) -> None:
    """The solver proposes guesses; you type the feedback each round."""
    solver = MastermindSolver(positions, colors)
    print(f"\nThink of {positions} distinct colors from 1..{colors}. "
          "I'll guess; after each guess tell me 'blacks whites'.\n"
          "(blacks = right color & place, whites = right color wrong place)\n")
    guesses = 0
    while True:
        guess = solver.next_guess()
        if guess is None:
            print("No sequence is consistent with the feedback you gave — "
                  "double-check your black/white counts.")
            return
        guesses += 1
        print(f"Guess {guesses}: {_fmt(guess)}")
        raw = input("  feedback (blacks whites): ").strip().replace(",", " ")
        try:
            blacks, whites = (int(x) for x in raw.split())
        except ValueError:
            print("  please enter two numbers, e.g. '2 1'")
            guesses -= 1
            continue
        if not (0 <= blacks <= positions and 0 <= whites <= positions
                and blacks + whites <= positions):
            print("  those counts aren't possible for this board; try again")
            guesses -= 1
            continue
        if blacks == positions:
            print(f"Solved in {guesses} guesses! The sequence is {_fmt(guess)}.")
            return
        solver.add_feedback(guess, blacks, whites)


if __name__ == "__main__":
    import argparse

    p = argparse.ArgumentParser(description="Z3-based Mastermind solver.")
    p.add_argument("--positions", type=int, default=5)
    p.add_argument("--colors", type=int, default=6)
    p.add_argument("--mode", choices=["self", "interactive"], default="self")
    p.add_argument("--secret", type=str, default=None,
                   help="self mode: force a secret, e.g. 3-1-6-2-4 or 31624")
    p.add_argument("--seed", type=int, default=None)
    args = p.parse_args()

    if args.mode == "interactive":
        solve_interactive(args.positions, args.colors)
    else:
        secret = None
        if args.secret:
            raw = args.secret.replace(",", "-").replace(" ", "-")
            parts = raw.split("-") if "-" in raw else list(raw)
            secret = tuple(int(x) for x in parts)
        print(f"Self-play on a {args.positions}-position / {args.colors}-color "
              "board:")
        solve_self(args.positions, args.colors, secret=secret, seed=args.seed)
