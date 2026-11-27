"""Exact two-ended search for decimal reversal products with one distinct digit."""

import argparse
from collections import defaultdict
from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class PrefixPair:
    first: int
    second: int
    first_reversed: int
    second_reversed: int


def extension_digits(left_unit, right_unit):
    by_residue = defaultdict(list)
    for left in range(10):
        for right in range(10):
            by_residue[(left * right_unit + right * left_unit) % 10].append((left, right))
    return by_residue


def initial_pairs(digit, scale):
    return [
        PrefixPair(left, right, left, right)
        for left in range(1, 10)
        for right in range(left, 10)
        if left * right % 10 == digit
        and scale * left * right < 100 * digit <= scale * (left + 1) * (right + 1)
    ]


def extend(pairs, place, digit, scale, digits_by_residue):
    lower_digits = digit * ((place - 1) // 9)
    threshold = digit * (10 * place) ** 2
    for pair in pairs:
        low_product = pair.first_reversed * pair.second_reversed
        required = (digit - (low_product - lower_digits) // place) % 10
        for left, right in digits_by_residue[required]:
            first = 10 * pair.first + left
            second = 10 * pair.second + right
            if scale * first * second < threshold <= scale * (first + 1) * (second + 1):
                yield PrefixPair(first, second, pair.first_reversed + left * place,
                                 pair.second_reversed + right * place)


def complete(pairs, place, digit, scale):
    # Cover both possible lengths of the factor: 2k and 2k+1, for k outer digits.
    even_target = digit * ((place ** 4 - (1 if scale == 9 else 10)) // scale)
    odd_target = digit * ((100 * place ** 4 - (1 if scale == 9 else 10)) // scale)
    for pair in pairs:
        first = pair.first * place + pair.second_reversed
        reverse = pair.second * place + pair.first_reversed
        if first * reverse == even_target:
            yield first, reverse
        for middle in range(10):
            first = (10 * pair.first + middle) * place + pair.second_reversed
            reverse = (10 * pair.second + middle) * place + pair.first_reversed
            if first * reverse == odd_target:
                yield first, reverse


def run(depth, digit, scale, report_every):
    # Splitting by endpoint digits keeps the low-order extension table fixed.
    endpoints = initial_pairs(digit, scale)
    for seed in endpoints:
        pairs = [seed]
        table = extension_digits(seed.first, seed.second)
        place = 10
        for k in range(1, depth + 1):
            for first, reverse in complete(pairs, place, digit, scale):
                print(f"MATCH {first} {reverse} {first * reverse}", flush=True)
            if k == depth or k % report_every == 0:
                print(f"d={digit} scale={scale} ends={seed.first},{seed.second} "
                      f"depth={k} pairs={len(pairs)}", flush=True)
            if k < depth:
                pairs = list(extend(pairs, place, digit, scale, table))
                if not pairs:
                    print(f"d={digit} scale={scale} ends={seed.first},{seed.second} "
                          f"empty at depth {k + 1}", flush=True)
                    break
                place *= 10


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, required=True)
    parser.add_argument("--digit", type=int, choices=range(1, 10))
    parser.add_argument("--scale", type=int, choices=(9, 90))
    parser.add_argument("--report-every", type=int, default=25)
    args = parser.parse_args()
    if args.depth < 1 or args.report_every < 1:
        parser.error("depth and report interval must be positive")
    for value in ([args.digit] if args.digit else range(1, 10)):
        for factor in ([args.scale] if args.scale else (9, 90)):
            run(args.depth, value, factor, args.report_every)
