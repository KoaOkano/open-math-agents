import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Bounds.Defs

/-!
# The least partial-sum index for A248183

The source starts its search at k=1. Index i=0 in the sum represents h=1.
For n>1 the proposed natural-valued floor is the integer part of
(sqrt(2*n^2+4)-1)/2. Replacing the square root by its integer part before
subtracting one and dividing by two preserves that floor.

Source: https://oeis.org/A248183 (conjecture by Ridouane Oudra)
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a248183

def tail (k : ℕ) : ℚ := 1/4 - ∑ i ∈ Finset.range k,
  1 / (((i : ℚ)+1) * (i+2) * (i+3))

def proposal (n : ℕ) := (Nat.sqrt (2*n^2+4)-1)/2

theorem main : ∀ n : ℕ, 1 < n →
    IsLeast {k : ℕ | 0 < k ∧ tail k < 1/(n : ℚ)^2} (proposal n) := by
  sorry

end OMA.S_oeis_a248183
