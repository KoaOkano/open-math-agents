import Mathlib

/-!
# Nonnegative coefficients of Kimberling's reciprocal series

For r = 9/10 the weight is floor(1 + (n+1)r), expressed by exact
integer division. The inverse exists over the integers since weight 0 = 1.
Source: https://oeis.org/A289921
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a289921

def weight (n : ℕ) : ℤ := 1 + ((9*(n+1)/10 : ℕ) : ℤ)

noncomputable def denominator : PowerSeries ℤ :=
  PowerSeries.mk fun n => (-1 : ℤ)^n * weight n

noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (PowerSeries.invOfUnit denominator 1)

theorem main : ∀ n : ℕ, 0 ≤ a n := by
  sorry

end OMA.S_oeis_a289921
