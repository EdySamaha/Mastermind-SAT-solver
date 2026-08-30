"""Test harness for the Mastermind solver — plain asserts, no framework.

Run it directly:

    python test_solver.py

It (1) cross-checks `score` against an independent brute-force count, then
(2) plays many random self-play games on a few boards, asserting every game is
solved and the recovered sequence equals the secret, and prints the average and
worst-case guess counts.
"""

from __future__ import annotations

import itertools
import random
from typing import Sequence, Tuple

import mastermind_game as game
from mastermind_solver import solve_self


def brute_score(guess: Sequence[int], secret: Sequence[int]) -> Tuple[int, int]:
    """Independent reference scorer, computed the long way as a cross-check.

    Blacks are exact-position matches. For whites, we walk the leftover pins
    (the non-black ones on each side) and pair up shared colors — the classic
    peg-matching definition, written without relying on the no-dup shortcut that
    ``game.score`` uses, so the two implementations can disagree if either is
    wrong.
    """
    blacks = sum(1 for g, s in zip(guess, secret) if g == s)
    left_guess = [g for g, s in zip(guess, secret) if g != s]
    left_secret = [s for g, s in zip(guess, secret) if g != s]
    whites = 0
    remaining = list(left_secret)
    for g in left_guess:
        if g in remaining:
            remaining.remove(g)
            whites += 1
    return blacks, whites


def test_score() -> None:
    """`game.score` must match the brute-force reference on all small boards."""
    checked = 0
    for positions, colors in [(3, 4), (4, 6), (2, 5)]:
        pool = range(1, colors + 1)
        for secret in itertools.permutations(pool, positions):
            for guess in itertools.permutations(pool, positions):
                assert game.score(guess, secret) == brute_score(guess, secret), \
                    f"score mismatch: guess={guess} secret={secret}"
                checked += 1
    print(f"[score] {checked} guess/secret pairs match the reference scorer.")


def test_selfplay() -> None:
    """Play many random games per board; every one must solve exactly."""
    boards = [(5, 6), (5, 5), (4, 8)]
    games_per_board = 300
    rng = random.Random(12345)
    for positions, colors in boards:
        counts = []
        for _ in range(games_per_board):
            secret = game.random_secret(positions, colors, rng)
            n, found = solve_self(positions, colors, secret=secret,
                                   verbose=False)
            assert tuple(found) == tuple(secret), \
                f"found {found} != secret {secret}"
            assert n >= 1
            counts.append(n)
        avg = sum(counts) / len(counts)
        print(f"[self-play] ({positions},{colors}): "
              f"{games_per_board} games, all solved  |  "
              f"avg {avg:.2f} guesses, worst {max(counts)}, best {min(counts)}")


if __name__ == "__main__":
    test_score()
    test_selfplay()
    print("\nAll tests passed.")
