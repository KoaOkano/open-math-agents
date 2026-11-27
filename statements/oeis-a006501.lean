import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# A coefficient identity for A006501 and A144677

The two ordinary generating functions are given independently in the OEIS
entries. Both sequences start at index zero. In the coefficient shift by
two, a term with negative index is zero.

Sources: https://oeis.org/A006501 and https://oeis.org/A144677
Conjecture by R. J. Mathar. The companion denominator is Johannes W. Meijer's.
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a006501

open PowerSeries

noncomputable def seriesA : PowerSeries ℚ :=
  (1 + X^2) * ((1-X)^2 * (1-X^3)^2)⁻¹

noncomputable def seriesB : PowerSeries ℚ :=
  ((1-X)^4 * (1+X+X^2)^2)⁻¹

theorem main : ∀ n : ℕ, coeff n seriesA =
    coeff n seriesB + (if 2 ≤ n then coeff (n-2) seriesB else 0) := by
  sorry

end OMA.S_oeis_a006501
