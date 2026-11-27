"""Find all terms of A307812 below a power of ten using integer arithmetic."""

import argparse
from math import isqrt, prod


def prime_powers(prime, upper_bound):
    power = 1
    while power <= upper_bound:
        yield power
        power *= prime


def terms_below(limit):
    # Solving n(n+1)/2 < limit gives the inclusive upper bound on n.
    last_index = (isqrt(1 + 8 * (limit - 1)) - 1) // 2
    records = []
    for two in prime_powers(2, last_index):
        for three in prime_powers(3, last_index // two):
            prefix = two * three
            for five in prime_powers(5, last_index // prefix):
                base = prefix * five
                if base % 20 == 0:
                    # Then n/2 is a multiple of ten, so the triangular value ends in zero.
                    continue
                for seven in prime_powers(7, last_index // base):
                    n = base * seven
                    triangular = n * (n + 1) // 2
                    digits = str(triangular)
                    if "0" in digits:
                        continue
                    product = prod(int(digit) for digit in digits)
                    if product % n == 0:
                        records.append((n, triangular, product // n))
    return sorted(records)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("exponent", type=int, nargs="?", default=300)
    args = parser.parse_args()
    if args.exponent < 1:
        parser.error("the exponent must be positive")
    records = terms_below(10 ** args.exponent)
    for n, triangular, quotient in records:
        print(n, triangular, quotient, sep="\t")
