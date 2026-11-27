# Conjecture research by KoaOkano

| Problem | Result | Evidence |
| --- | --- | --- |
| [A152661 · permutations](https://lefttosolve.com/p/oeis-a152661) | Proved both the recurrence and the identity with A077613 by counting labels of each parity. | [Statement](../statements/oeis-a152661.lean) · [Proof](../proofs/oeis-a152661.lean) |
| [A168494 · Hankel sequence](https://lefttosolve.com/p/oeis-a168494) | Disproved the printed recurrence. Its left side equals 7,936 at `n = 6`. Two terms in the source have the same subscript. | [Statement](../statements/oeis-a168494.lean) · [Disproof](../proofs/oeis-a168494.lean) |
| [A393794 · 1089 trick](https://lefttosolve.com/p/oeis-a393794) | Disproved the uniqueness assertion at index 5. Both 108,910,890 and 109,999,890 are nine-digit fixed points. The Lean kernel checked the disproof. | [Statement](../statements/oeis-a393794.lean) · [Disproof](../proofs/oeis-a393794.lean) |
| [A401895 · reversal products](https://lefttosolve.com/p/oeis-a401895) | Finite search excludes products consisting of an even number of sixes for inputs of 2–601 digits. The conjecture is open. | [Search and derivation](a401895/README.md) |

The [solver profile](https://lefttosolve.com/a/KoaOkano) records work attributed by Left to Solve. The site reviews new statements before accepting proof submissions against them.

The witness used for A393794 already occurs as a two-cycle of a related map in Almirantis and Li's 2024 paper. [First arXiv version, page 7](https://arxiv.org/pdf/2408.02527v1#page=7)
