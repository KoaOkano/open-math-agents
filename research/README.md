# Conjecture research by KoaOkano

| Problem | Result | Evidence |
| --- | --- | --- |
| [A071622 · parity of powers of 4/3](https://lefttosolve.com/p/oeis-a071622) | Disproved the logarithmic lower bound at `n = 18,966`. Exactly 9,483 floors are odd and 9,483 are even, giving `a(n) = 0`. The Lean kernel checks the sum using exact integer division. | [Statement](../statements/oeis-a071622.lean) · [Disproof](../proofs/oeis-a071622.lean) |
| [A152661 · permutations](https://lefttosolve.com/p/oeis-a152661) | Proved both the recurrence and the identity with A077613 by counting labels of each parity. | [Statement](../statements/oeis-a152661.lean) · [Proof](../proofs/oeis-a152661.lean) |
| [A168494 · Hankel sequence](https://lefttosolve.com/p/oeis-a168494) | Disproved the printed recurrence. Its left side equals 7,936 at `n = 6`. Two terms in the source have the same subscript. | [Statement](../statements/oeis-a168494.lean) · [Disproof](../proofs/oeis-a168494.lean) |
| [A191993 · central binomial coefficients](https://lefttosolve.com/p/oeis-a191993) | Proved Mathar's recurrence for the sum of a power of three and half a central binomial coefficient. | [Statement](../statements/oeis-a191993.lean) · [Proof](../proofs/oeis-a191993.lean) |
| [A207262 · divisor-power sums](https://lefttosolve.com/p/oeis-a207262) | Proved Ianakiev's quotient formula by splitting the divisors of twice an odd number into odd divisors and their doubles. | [Statement](../statements/oeis-a207262.lean) · [Proof](../proofs/oeis-a207262.lean) |
| [A393794 · 1089 trick](https://lefttosolve.com/p/oeis-a393794) | Disproved the uniqueness assertion at index 5. Both 108,910,890 and 109,999,890 are nine-digit fixed points. The Lean kernel checked the disproof. | [Statement](../statements/oeis-a393794.lean) · [Disproof](../proofs/oeis-a393794.lean) |
| [A401895 · reversal products](https://lefttosolve.com/p/oeis-a401895) | Finite search excludes products consisting of an even number of sixes for inputs of 2–601 digits. The conjecture is open. | [Search and derivation](a401895/README.md) |

The [solver profile](https://lefttosolve.com/a/KoaOkano) records work attributed by Left to Solve. The site reviews new statements before accepting proof submissions against them.

The witness used for A393794 already occurs as a two-cycle of a related map in Almirantis and Li's 2024 paper. [First arXiv version, page 7](https://arxiv.org/pdf/2408.02527v1#page=7)
