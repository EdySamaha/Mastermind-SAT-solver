"""Mastermind — the game, plus reusable scoring/generation helpers.

The secret is a sequence of `positions` pins, each a distinct color drawn from
`1..colors` (no color repeats). The classic feedback is two counts:

    blacks — right color in the right position
    whites — right color, wrong position

Run this file to play as a human. The solver (`mastermind_solver.py`) and the
tests import `random_secret` and `score` from here, so the game and the solver
always agree on the rules.
"""

from __future__ import annotations

import random
from typing import Optional, Sequence, Tuple

# Defaults for the human game (override on the CLI). The solver defaults to a
# 5-position / 6-color board, matching the target variant.
DEFAULT_COLORS = 8
DEFAULT_POSITIONS = 4

Sequence_t = Tuple[int, ...]


def random_secret(positions: int = DEFAULT_POSITIONS,
                  colors: int = DEFAULT_COLORS,
                  rng: Optional[random.Random] = None) -> Sequence_t:
    """Return a random secret: `positions` distinct colors from ``1..colors``.

    Requires ``colors >= positions`` (no duplicates are allowed, so there must be
    at least one distinct color per position).
    """
    if colors < positions:
        raise ValueError(
            f"colors ({colors}) must be >= positions ({positions}): "
            "no-duplicates needs at least one distinct color per position")
    r = rng or random
    return tuple(r.sample(range(1, colors + 1), positions))


def score(guess: Sequence[int], secret: Sequence[int]) -> Tuple[int, int]:
    """Score a guess against the secret, returning ``(blacks, whites)``.

    ``blacks`` = positions where color and place both match.
    ``whites`` = colors present in the secret but in the wrong place.

    This is only valid for the no-duplicates variant, where each color occurs at
    most once in both guess and secret; then the number of shared colors is just
    the size of the set intersection, and whites = shared - blacks.
    """
    if len(guess) != len(secret):
        raise ValueError("guess and secret must be the same length")
    blacks = sum(1 for g, s in zip(guess, secret) if g == s)
    shared = len(set(guess) & set(secret))
    return blacks, shared - blacks


def score_message(guess: Sequence[int], secret: Sequence[int]) -> str:
    """Human-readable version of `score` (the original game's feedback line)."""
    blacks, whites = score(guess, secret)
    return (f"You have {blacks} Correct in place and "
            f"{whites} Correct but Not in place")


def _parse_guess(raw: str, positions: int, colors: int) -> Optional[Sequence_t]:
    """Parse a human guess. Accepts space/comma-separated numbers, or — when
    every color is a single digit (colors <= 9) — a bare digit string like
    ``2413``. Returns a validated tuple, or None with a printed reason."""
    raw = raw.strip()
    if not raw:
        return None
    if any(sep in raw for sep in (" ", ",")):
        parts = raw.replace(",", " ").split()
    elif colors <= 9:
        parts = list(raw)
    else:
        print("Separate colors with spaces or commas.")
        return None
    try:
        guess = tuple(int(p) for p in parts)
    except ValueError:
        print("Colors must be numbers.")
        return None
    if len(guess) != positions:
        print(f"Please enter exactly {positions} colors.")
        return None
    if any(not (1 <= c <= colors) for c in guess):
        print(f"Colors must be between 1 and {colors}.")
        return None
    if len(set(guess)) != len(guess):
        print("No duplicate colors allowed.")
        return None
    return guess


def play(positions: int = DEFAULT_POSITIONS, colors: int = DEFAULT_COLORS,
         rng: Optional[random.Random] = None) -> None:
    """Interactive human game loop."""
    secret = random_secret(positions, colors, rng)
    print("\n--------- WELCOME TO MASTERMIND! ----------\n")
    print(f"Guess the sequence of {positions} distinct colors between 1 and "
          f"{colors}.\nColors don't repeat. Press q to give up.\n****")
    while True:
        raw = input(f"Enter {positions} distinct numbers (1..{colors}): ")
        if raw.strip().lower() == "q":
            print("The secret was:", "".join(map(str, secret))
                  if colors <= 9 else secret)
            return
        guess = _parse_guess(raw, positions, colors)
        if guess is None:
            continue
        blacks, whites = score(guess, secret)
        if blacks == positions:
            print(f"All {positions} are correct, Congratulations!!! :)")
            return
        print(score_message(guess, secret))


if __name__ == "__main__":
    import argparse

    p = argparse.ArgumentParser(description="Play Mastermind (no-duplicates).")
    p.add_argument("--positions", type=int, default=DEFAULT_POSITIONS)
    p.add_argument("--colors", type=int, default=DEFAULT_COLORS)
    p.add_argument("--seed", type=int, default=None)
    args = p.parse_args()
    play(args.positions, args.colors,
         random.Random(args.seed) if args.seed is not None else None)
