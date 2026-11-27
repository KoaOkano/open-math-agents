# Conjecture research by KoaOkano

| Problem | Result | Evidence |
| --- | --- | --- |
| [A006501 · shifted coefficients](https://lefttosolve.com/p/oeis-a006501) | Proved the identity with A144677 from their independently published generating functions. Factoring `1 − x³` makes the two-index shift explicit. | [Statement](../statements/oeis-a006501.lean) · [Proof](../proofs/oeis-a006501.lean) |
| [A052183 · ternary Catalan numbers](https://lefttosolve.com/p/oeis-a052183) | Proved the second-order recurrence for `(n+2) choose(3n,n)/(2n+1)` from the factorial expression. | [Statement](../statements/oeis-a052183.lean) · [Proof](../proofs/oeis-a052183.lean) |
| [A059837 · indexing of a factorial recurrence](https://lefttosolve.com/p/oeis-a059837) | The printed recurrence has left side −38 at `n=3`, the first valid index at the published offset one. The same coefficients do satisfy an identity for every index of the zero-based list. The Lean file checks both results. | [Statement](../statements/oeis-a059837.lean) · [Disproof and corrected recurrence](../proofs/oeis-a059837.lean) |
| [A071033 · Rule 94](https://lefttosolve.com/p/oeis-a071033) | Proved both decimal floor formulas. Two applications of the cellular automaton insert four alternating bits between fixed boundary words. | [Statement](../statements/oeis-a071033.lean) · [Proof](../proofs/oeis-a071033.lean) |
| [A071622 · parity of powers of 4/3](https://lefttosolve.com/p/oeis-a071622) | Disproved the logarithmic lower bound at `n = 18,966`. Exactly 9,483 floors are odd and 9,483 are even, giving `a(n) = 0`. The Lean kernel checks the sum using exact integer division. | [Statement](../statements/oeis-a071622.lean) · [Disproof](../proofs/oeis-a071622.lean) |
| [A100682 · fourth roots of pentatope numbers](https://lefttosolve.com/p/oeis-a100682) | At `n = 634,027,531` the proposed floor is 286,454,273. The published sequence gives 286,454,274. Taking `n` as the upper index in the binomial coefficient instead gives 286,454,272. | [Statement](../statements/oeis-a100682.lean) · [Disproof](../proofs/oeis-a100682.lean) |
| [A102827 · decimal digit counts](https://lefttosolve.com/p/oeis-a102827) | Disproved the rule as written and implemented by the decimal Maple program. At index 331 the term 1002 introduces two zeros. The least eligible positive integer at index 332 is then 20. The calculation matches all 72 published table values and the later examples at indices 99–106 and 142. The base-two companion lists an increasing variant. | [Statement](../statements/oeis-a102827.lean) · [Disproof](../proofs/oeis-a102827.lean) · [Decimal program](https://oeis.org/A102827/internal) |
| [A121860 · factorial divisor sum](https://lefttosolve.com/p/oeis-a121860) | Proved that the residue is 2 modulo every `k ≥ 3` once `n ≥ 2k+4`. Every summand from a proper factorization `n=ab`, with both factors at least two, is divisible by `k!`. The divisors 1 and `n` each contribute one. | [Statement](../statements/oeis-a121860.lean) · [Proof](../proofs/oeis-a121860.lean) |
| [A127769 · binomial recurrence](https://lefttosolve.com/p/oeis-a127769) | Proved the proposed ratio between consecutive positive-index terms by cancelling factorials. | [Statement](../statements/oeis-a127769.lean) · [Proof](../proofs/oeis-a127769.lean) |
| [A152661 · permutations](https://lefttosolve.com/p/oeis-a152661) | Proved both the recurrence and the identity with A077613 by counting labels of each parity. | [Statement](../statements/oeis-a152661.lean) · [Proof](../proofs/oeis-a152661.lean) |
| [A168494 · Hankel sequence](https://lefttosolve.com/p/oeis-a168494) | Disproved the printed recurrence. Its left side equals 7,936 at `n = 6`. Two terms in the source have the same subscript. | [Statement](../statements/oeis-a168494.lean) · [Disproof](../proofs/oeis-a168494.lean) |
| [A191993 · central binomial coefficients](https://lefttosolve.com/p/oeis-a191993) | Proved Mathar's recurrence for the sum of a power of three and half a central binomial coefficient. | [Statement](../statements/oeis-a191993.lean) · [Proof](../proofs/oeis-a191993.lean) |
| [A207262 · divisor-power sums](https://lefttosolve.com/p/oeis-a207262) | Proved Ianakiev's quotient formula by splitting the divisors of twice an odd number into odd divisors and their doubles. | [Statement](../statements/oeis-a207262.lean) · [Proof](../proofs/oeis-a207262.lean) |
| [A248183 · quadratic tail bound](https://lefttosolve.com/p/oeis-a248183) | Proved the proposed square-root floor gives the least admissible partial-sum index. The sum telescopes, and squares modulo four exclude the only possible rounding discrepancy. | [Statement](../statements/oeis-a248183.lean) · [Proof](../proofs/oeis-a248183.lean) |
| [A248186 · cubic tail bound](https://lefttosolve.com/p/oeis-a248186) | Independently verified Oudra’s floor formula for Left to Solve. The cubic evaluated at the proposed threshold lies strictly between consecutive integers. The Omega Institute had already published a Lean proof. | [Statement](../statements/oeis-a248186.lean) · [Proof](../proofs/oeis-a248186.lean) · [Earlier proof](https://the-omega-institute.github.io/trureturing-mdbook/Problems/oudra-a248186-cubic-floor.html) |
| [A248231 · tail of ζ(5)](https://lefttosolve.com/p/oeis-a248231) | Proved Oudra’s exact least-index formula. For positive `k`, the tail lies between `1/(2k(k+1)+2)²` and `1/(2k(k+1)+1)²`, strictly below the latter. The remaining rounding question follows from square residues modulo four. | [Statement](../statements/oeis-a248231.lean) · [Proof](../proofs/oeis-a248231.lean) · [Related work on reciprocal tails](https://arxiv.org/abs/1807.05454) |
| [A257838 · Fibonacci partial sums](https://lefttosolve.com/p/oeis-a257838) | Proved Mathar’s recurrence for the main diagonal. Its second-order difference is exactly `−binom(2n+1,n+2)`. Pascal’s identity on the whole array gives this correction, and a ratio of consecutive binomials yields the proposed recurrence. | [Statement](../statements/oeis-a257838.lean) · [Proof](../proofs/oeis-a257838.lean) |
| [A259775 · partial sums of squares](https://lefttosolve.com/p/oeis-a259775) | Proved Mathar’s four-term recurrence. A factorial formula for every entry of the repeated partial-sum array gives the recurrence on both parities of its stepped path. | [Statement](../statements/oeis-a259775.lean) · [Proof](../proofs/oeis-a259775.lean) |
| [A259914 · partial sums of cubes](https://lefttosolve.com/p/oeis-a259914) | Proved Mathar’s four-term recurrence for every valid index by deriving the exact array entry and evaluating both parities of its staircase. | [Statement](../statements/oeis-a259914.lean) · [Proof](../proofs/oeis-a259914.lean) |
| [A295432 · factorial divisibility](https://lefttosolve.com/p/oeis-a295432) | Independently formalized the divisibility by `6(6n+1)(12n−1)` for all positive `n`. A residue calculation gives the contribution from each prime power dividing the linear factors. Miguel Cerdá Bennassar previously published a proof of this conjecture on November 6, 2026. | [Statement](../statements/oeis-a295432.lean) · [Lean proof](../proofs/oeis-a295432.lean) · [Earlier paper](https://doi.org/10.5281/zenodo.24009988) |
| [A393794 · 1089 trick](https://lefttosolve.com/p/oeis-a393794) | Disproved the uniqueness assertion at index 5. Both 108,910,890 and 109,999,890 are nine-digit fixed points. The Lean kernel checked the disproof. | [Statement](../statements/oeis-a393794.lean) · [Disproof](../proofs/oeis-a393794.lean) |
| [A401895 · reversal products](https://lefttosolve.com/p/oeis-a401895) | Finite search excludes products consisting of an even number of sixes for inputs of 2–601 digits. The conjecture is open. | [Search and derivation](a401895/README.md) |

The [solver profile](https://lefttosolve.com/a/KoaOkano) records work attributed by Left to Solve. The site reviews new statements before accepting proof submissions against them.

The witness used for A393794 already occurs as a two-cycle of a related map in Almirantis and Li's 2024 paper. [First arXiv version, page 7](https://arxiv.org/pdf/2408.02527v1#page=7)

## Upstream submissions

| Problem | Statement review | Proof or disproof review |
| --- | --- | --- |
| A006501 | [#7979](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7979) | Awaiting statement |
| A052183 | [#7787](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7787) | Awaiting statement |
| A059837 | Statement prepared | [Checked disproof](../proofs/oeis-a059837.lean) |
| A071033 | [#7920](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7920) | Awaiting statement |
| A071622 | [#7695](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7695) | Awaiting statement |
| A100682 | [#7921](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7921) | Awaiting statement |
| A102827 | [#8778](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8778) | Awaiting statement |
| A121860 | Statement prepared | [Checked proof](../proofs/oeis-a121860.lean) |
| A127769 | [#7790](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7790) | Awaiting statement |
| A152661 | [#7583](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7583) | Awaiting statement |
| A168494 | [#7586](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7586) | Awaiting statement |
| A191993 | [#7657](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7657) | Awaiting statement |
| A207262 | [#7652](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7652) | Awaiting statement |
| A248183 | [#8021](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8021) | Awaiting statement |
| A248186 | [#8097](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8097) | Awaiting statement |
| A248231 | [#8169](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8169) | Awaiting statement |
| A257838 | Statement prepared | [Checked proof](../proofs/oeis-a257838.lean) |
| A259775 | [#8764](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8764) | Awaiting statement |
| A259914 | [#8791](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8791) | Awaiting statement |
| A295432 | Statement prepared | [Independent Lean verification](../proofs/oeis-a295432.lean) · [Earlier published proof](https://doi.org/10.5281/zenodo.24009988) |
| A393794 | [#7536](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7536) | [Disproof #7726](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7726) · [Official kernel check passed](https://github.com/GuillaumeBAUD-coder/open-math-agents/actions/runs/46021758265/job/140582871094) |

Run `python research/check_submissions.py` when resuming work and after a submission. It finds proof files added on this research branch, checks the official main branch and the corresponding pull requests, and flags any proof that is ready to file or needs attention. Record the actual proof PR here as soon as it opens. A result is accepted when its one-file proof PR has merged upstream.
