"""Independently replay the two rectangular sieves using Python 3.9 or later."""
import json
from math import gcd
from pathlib import Path

BASE = 360_360
LENGTH = 100_000_000
LIMIT = 4_000
BLOCK = 1 << 20
STARTS = (64, 10**18)


def residue_classes():
    """Each excluded class certifies 0 < n mod d <= 2*tau(d)-3."""
    counts = [0] * (LIMIT + 1)
    for divisor in range(1, LIMIT + 1):
        for multiple in range(divisor, LIMIT + 1, divisor):
            counts[multiple] += 1

    by_period = {}
    for d in range(2, LIMIT + 1):
        common = gcd(BASE, d)
        period = d // common
        max_reduced_remainder = min(d - 1, 2 * counts[d] - 3) // common
        if period == 1 or max_reduced_remainder == 0:
            continue
        inverse = pow(BASE // common, -1, period)
        excluded = by_period.setdefault(period, set())
        for j in range(1, max_reduced_remainder + 1):
            excluded.add(j * inverse % period)
    return by_period


def survivors(start, classes):
    if BASE * start < LIMIT * LIMIT + LIMIT:
        raise ValueError("This interval begins too early for the divisor bound.")
    for lo in range(start, start + LENGTH, BLOCK):
        size = min(BLOCK, start + LENGTH - lo)
        keep = bytearray([1]) * size
        for period, excluded in classes.items():
            for residue in excluded:
                offset = (residue - lo) % period
                if offset < size:
                    count = (size - 1 - offset) // period + 1
                    keep[offset::period] = bytes(count)
        yield from (lo + i for i, flag in enumerate(keep) if flag)


def replay():
    data = json.loads(Path(__file__).with_name("witnesses.json").read_text(encoding="utf-8"))
    classes = residue_classes()
    for start in STARTS:
        witnesses = {}
        for q, shift, divisors in data[str(start)]:
            if q in witnesses or not start <= q < start + LENGTH:
                raise ValueError(f"Duplicated or misplaced multiplier {q}")
            n = BASE * q
            m = n - shift
            if not 0 < m < n or len(set(divisors)) < shift + 3:
                raise ValueError(f"Insufficient divisor witness for {q}")
            if any(d <= 0 or m % d for d in divisors):
                raise ValueError(f"Incorrect divisor of {m}")
            witnesses[q] = shift
        remaining = set(survivors(start, classes))
        if remaining != set(witnesses):
            raise ValueError(f"Residual multipliers and witnesses differ at {start}")
        print(f"[{BASE*start:,}, {BASE*(start+LENGTH):,}) verified; "
              f"{len(remaining)} direct divisor witnesses")


if __name__ == "__main__":
    replay()
