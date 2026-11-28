# Finite exclusion certificates for Erdős problem 647

Erdős and Selfridge asked whether there is an integer $n>24$ such that $m+τ(m)≤n+2$ for every nonnegative integer $m<n$, where $τ(m)$ counts the positive divisors of $m$. This Lean project proves that each integer in the following ranges admits a violating $m$. The question for arbitrary $n$ remains open. [Original problem](https://www.erdosproblems.com/647)

| Integers covered | Lean theorem in `OMA.Erdos647Obstructions` |
| --- | --- |
| `24 < n ≤ 36,036,023,063,039` | `originalFailsThrough` |
| `360360·10¹⁸ ≤ n < 360360·(10¹⁸ + 10⁸)` | `originalFailsInHighInterval` |

The second interval contains 36,036,000,000,000 consecutive integers. Both theorems address the finite supremum from the original problem statement. The first interval includes every integer after the known solution at 24 up to the listed endpoint.

## Check the Lean proof

The standalone project lives on a dedicated branch of KoaOkano's fork. With Elan installed, the following commands fetch that branch and check the proof. Lean and Mathlib are pinned to 4.33.1. The proof imports only Mathlib. [Elan](https://github.com/leanprover/elan)

```sh
git clone --single-branch --branch codex/erdos-647-certificates https://github.com/KoaOkano/open-math-agents.git erdos-647-certificates
cd erdos-647-certificates
lake exe cache get
lake build
lake env lean Erdos647.lean
```

The last command prints the axiom dependencies of both range theorems. In each case they are `propext`, `Classical.choice`, and `Quot.sound`. All arithmetic certificates are in `Erdos647.lean`.

## How the certificate works

If `m=d·u` and `u>d>0`, each divisor of `d` gives two distinct divisors of `m`, one in each of the disjoint families `a` and `u·a`. Thus `τ(m) ≥ 2τ(d)`. For `r=n mod d` with `d²+d ≤ n` and `1 ≤ r ≤ 2τ(d)−3`, taking `m=n−r` proves that `m+τ(m)>n+2`.

Small cases and a chain of modular obstructions force every candidate above 24 to be a multiple of 360360. Write `n=360360·q`. In each of the two ranges the proof checks 100 blocks of one million consecutive multipliers. Each block is sieved with 100 periodic masks. Lean checks that every residue eliminated by a mask violates the inequality, that the mask intersection equals an explicitly given set, and that every member of that set has its own divisor witness. There are 735 such positions in the initial range and 733 in the higher range. The small-case proof covers the integers before the first block.

## Replay the numerical sieve

The Python replay uses every eligible modulus through 4000 before consulting the explicit divisor lists in `witnesses.json`. Run it with Python 3.9 or later.

```sh
python replay.py
```

It checks the 100 million multipliers in each range and verifies the remaining 87 and 96 cases respectively. It uses only the Python standard library. Lean checks both range theorems directly from the data embedded in the proof file.

## Credit and prior work

Lean formalization and computational certificates by KoaOkano with OpenAI Codex assistance. The LeftToSolve companion contains the same numerical theorems and discharges the parent reduction's sharp divisor-bound hypothesis. [Companion PR](https://github.com/KoaOkano/open-math-agents/pull/79) · [Upstream PR](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17277)

Mian and Siddique gave a kernel-checked proof through 10⁹. Hughes developed related modular searches, and Veljanoski reported a GPU search through 10²². [Mian and Siddique](https://arxiv.org/abs/2608.17880) · [Scott Hughes](https://github.com/scottdhughes/erdos647-proof-chain) · [Veljanoski](https://github.com/veljjanoski/erdos647)
