import OMAStatements.S_oeis_a006501
import Mathlib.Tactic.Ring

open PowerSeries OMA.S_oeis_a006501

theorem OMA.solution : type_of% @OMA.S_oeis_a006501.main := by
  have den (x : PowerSeries ℚ) :
      (1-x)^2 * (1-x^3)^2 = (1-x)^4 * (1+x+x^2)^2 := by ring
  intro n
  rw [seriesA, den, ← seriesB, add_mul, one_mul, map_add, coeff_X_pow_mul']
