import Mathlib

/-!
# Nonnegative coefficients of Kimberling's reciprocal series

As r approaches 19/21 strictly from below, floor(1+(n+1)r) stabilizes at
ceil(19(n+1)/21). Each coefficient of the reciprocal depends on finitely
many denominator coefficients, so these exact ceiling weights describe
the coefficientwise limiting sequence.
Source: https://oeis.org/A289923
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a289923

def weight (n : ℕ) : ℤ := (((19*(n+1)+20)/21 : ℕ) : ℤ)

noncomputable def denominator : PowerSeries ℤ :=
  PowerSeries.mk fun n => (-1 : ℤ)^n * weight n

noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (PowerSeries.invOfUnit denominator 1)

theorem main : ∀ n : ℕ, 0 ≤ a n := by
  sorry

end OMA.S_oeis_a289923
