import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Sqrt

/-!
# The least partial-sum index for the series defining zeta(5)

Subtracting the first k terms of the absolutely convergent zeta series
leaves the sum from k+1 to infinity. The search is over positive k.
For n>1, the proposed floor is the integer part of
(sqrt(2*n^2-4)+1)/2. Taking the integer square root before adding one and
dividing by two gives exactly the same floor.

Source: https://oeis.org/A248231 (conjecture by Ridouane Oudra)
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a248231

noncomputable def term (i : ℕ) : ℝ := 1/((i : ℝ)+1)^5

noncomputable def tail (k : ℕ) := ∑' j : ℕ, term (k+j)

def proposal (n : ℕ) := (Nat.sqrt (2*n^2-4)+1)/2

theorem main : ∀ n : ℕ, 1 < n →
    IsLeast {k : ℕ | 0 < k ∧ tail k < 1/(n : ℝ)^4} (proposal n) := by
  sorry

end OMA.S_oeis_a248231
