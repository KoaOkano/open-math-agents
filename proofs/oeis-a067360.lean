import OMAStatements.S_oeis_a067360

/-!
# Colin Barker's formulas for A067360

For θ = 2 arctan(1/4), the two numbers 17 exp(±iθ) are 15 ± 8i.
Their powers give the sine formula, and both satisfy z² − 30z + 289 = 0.
-/

open OMA.S_oeis_a067360 Complex

namespace A067360

private noncomputable def angle : ℝ := 2 * Real.arctan (1 / 4)

private theorem angle_values : Real.cos angle = 15 / 17 ∧ Real.sin angle = 8 / 17 := by
  have h := Real.cos_sq_arctan (1 / 4)
  norm_num at h
  have hs : Real.sin (Real.arctan (1 / 4)) = Real.cos (Real.arctan (1 / 4)) / 4 := by
    rw [Real.sin_arctan, Real.cos_arctan]
    ring
  constructor
  · rw [angle, Real.cos_two_mul]
    nlinarith
  · rw [angle, Real.sin_two_mul, hs]
    nlinarith

private theorem polar_pow (t : ℝ) (n : ℕ) :
    ((17 : ℂ) * ((Real.cos t : ℂ) + (Real.sin t : ℂ) * I)) ^ n =
      17 ^ n * ((Real.cos (n * t) : ℂ) + (Real.sin (n * t) : ℂ) * I) := by
  rw [mul_pow]
  congr 1
  simpa using Complex.cos_add_sin_mul_I_pow n (t : ℂ)

private theorem closed (n : ℕ) : (a n : ℂ) =
    I * ((15 - 8 * I) ^ n - (15 + 8 * I) ^ n) / 2 := by
  obtain ⟨hc, hs⟩ := angle_values
  have hp : (15 + 8 * I : ℂ) = 17 * ((Real.cos angle : ℂ) + (Real.sin angle : ℂ) * I) := by
    rw [hc, hs]
    push_cast
    ring
  have hm : (15 - 8 * I : ℂ) = 17 * ((Real.cos (-angle) : ℂ) + (Real.sin (-angle) : ℂ) * I) := by
    rw [Real.cos_neg, Real.sin_neg, hc, hs]
    push_cast
    ring
  have ht : 2 * (n : ℝ) * Real.arctan (1 / 4) = n * angle := by unfold angle; ring
  rw [hm, hp, polar_pow, polar_pow, mul_neg, Real.cos_neg, Real.sin_neg, a, ht]
  push_cast
  ring_nf
  simp [Complex.I_sq]

private theorem root_recurrence (z : ℂ) (hz : z ^ 2 = 30 * z - 289) (k : ℕ) :
    z ^ (k + 2) = 30 * z ^ (k + 1) - 289 * z ^ k := by
  rw [pow_add, hz, pow_succ]
  ring

end A067360

theorem OMA.solution : type_of% @OMA.S_oeis_a067360.main := by
  constructor
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
    apply Complex.ofReal_injective
    push_cast
    rw [A067360.closed, A067360.closed, A067360.closed]
    have hm : (15 - 8 * I : ℂ) ^ 2 = 30 * (15 - 8 * I) - 289 := by
      apply Complex.ext <;> norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    have hp : (15 + 8 * I : ℂ) ^ 2 = 30 * (15 + 8 * I) - 289 := by
      apply Complex.ext <;> norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    rw [A067360.root_recurrence _ hm, A067360.root_recurrence _ hp]
    ring
  · exact fun n _ => A067360.closed n
