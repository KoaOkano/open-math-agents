import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The least partial-sum index for A248186

The partial sum starts at h=1 and the least admissible k is positive.
The source defines r as the positive real number 3^(-1/3). On the stated
range n>2 the conjectured floor is a natural number.

Source: https://oeis.org/A248186 (conjecture by Ridouane Oudra)
Prior Lean proof: https://the-omega-institute.github.io/trureturing-mdbook/Problems/oudra-a248186-cubic-floor.html
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a248186

noncomputable def tail (k : ℕ) : ℝ := 1/18 - ∑ i ∈ Finset.range k,
  1 / (((i : ℝ)+1)*(i+2)*(i+3)*(i+4))

noncomputable def r := (3 : ℝ) ^ (-(1 : ℝ)/3)

noncomputable def threshold (n : ℕ) := r*n + r^2/n

theorem main : ∀ n : ℕ, 2 < n →
    IsLeast {k : ℕ | 0 < k ∧ tail k < 1/(n : ℝ)^3} ⌊threshold n - 1⌋₊ := by
  sorry

end OMA.S_oeis_a248186
