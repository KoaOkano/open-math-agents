import Mathlib

/-!
# Last four digits of the greedy harmonic-sum denominators

A374663 chooses the least positive divisor d for the kth harmonic term
that keeps its partial sum strictly below 1. If the previous sum is s,
the admissible integers satisfy d > 1/(k(1-s)), so the least is the floor
of this positive rational plus one. A375516 takes the denominator of the
resulting reduced rational partial sum. Its proposed last-four-digits
pattern begins at n = 5.

Sources: https://oeis.org/A375516 and https://oeis.org/A374663
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a375516

def nextDivisor (k : ℕ) (s : ℚ) : ℕ := ⌊1 / ((k : ℚ)*(1-s))⌋₊+1

def partialSum : ℕ → ℚ
  | 0 => 0
  | n+1 =>
    let s := partialSum n
    s + 1 / (((n+1 : ℕ) : ℚ) * nextDivisor (n+1) s)

theorem main : ∀ n : ℕ, 5 ≤ n → (partialSum n).den % 10000 = 1200 := by
  sorry

end OMA.S_oeis_a375516
