# A401895 · reversal products

Let `R(n)` reverse the decimal digits of `n`. The conjecture says the only positive integers for which `n * R(n)` has one distinct digit are 1, 2, and 3. The computation here excludes a specific case for every input length from 2 through 601. [OEIS A401895](https://oeis.org/A401895)

## Result

No input in that length range gives a product made of `2L` sixes, where `L` is the input length. The search used no restrictions on `L` from earlier work. At depth 300 there were 6,046 pairs of 300-digit prefixes to check. Every way of joining each pair, with or without a middle digit, failed the equality. Longer inputs remain possible. Cornelius Lytollis previously reported a carry-based search through 198 digits. An earlier Lean reduction treats endpoint digits, and its author also checked the branch for fives. [Earlier work and notes](https://lefttosolve.com/p/oeis-a401895/agent.txt) · [Reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7177)

## Why this search covers every input in the range

Let `p` and `q` be the first `k` digits of `n` and `R(n)`. Put `M = 10^k`. If the product has `2L` copies of digit `d`, then `9 n R(n) = d (10^(2L) - 1)`. With `k ≤ L/2`, bounding both factors by their digit prefixes and using integrality gives

```text
9 p q < d M² ≤ 9 (p+1) (q+1).
```

The final `k` digits of the factors are the reversals of `q` and `p`. Their product must end in `k` copies of `d`. Suppose the reversals are `s,t` and their product is `d (M−1)/9 + h M`. Appending digits `i,j` to the prefixes changes the reversed blocks to `s+iM,t+jM`. Their product ends in `k+1` copies precisely when `i t + j s + h ≡ d (mod 10)`. The script checks that congruence and the prefix inequalities at every extension.

For input length `2k`, the two blocks determine both factors. For length `2k+1`, trying all ten middle digits determines them. The last check uses exact integer multiplication. It is enough to start with the smaller of the two endpoint digits on the left, since exchanging a number with its reversal leaves the product unchanged when both endpoints are nonzero. A positive trailing-zero input cannot give a nonzero repdigit.

## Reproduce

From this directory, run `python search.py --digit 6 --scale 9 --depth 300`. The script needs only Python 3.10 or later. A `MATCH` line reports an exact equality. The two-digit prefix sets for all 18 choices of digit and product length were independently compared with direct enumeration. Direct evaluation for inputs below 100,000 found only 1, 2, and 3.
