import OMAStatements.S_oeis_a373163
import Mathlib.Tactic

open OMA.S_oeis_a373163

namespace CosineDifferences

private noncomputable def wave (k : ℕ) : ℝ := Real.cos (2*k*Real.pi/3)
private noncomputable def series (x : ℝ) : ℝ := ∑' k : ℕ, wave k*x^k

private lemma periodic (k : ℕ) : wave (k+3)=wave k := by
  unfold wave
  push_cast
  rw [show 2*((k:ℝ)+3)*Real.pi/3=2*k*Real.pi/3+2*Real.pi by ring, Real.cos_add_two_pi]

private lemma generating (x : ℝ) (hx : 0≤x) (hlt : x<1) :
    (1+x+x^2)*series x = 1+x/2 := by
  have summable : Summable (fun k : ℕ => wave k*x^k) := by
    apply Summable.of_norm_bounded (g := fun k : ℕ => x^k) (summable_geometric_of_lt_one hx hlt)
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx k)]
    exact mul_le_of_le_one_left (pow_nonneg hx k) (Real.abs_cos_le_one _)
  have w0 : wave 0=1 := by simp [wave]
  have w1 : wave 1 = -(1/2:ℝ) := by
    unfold wave
    rw [show 2*((1:ℕ):ℝ)*Real.pi/3=Real.pi-Real.pi/3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  have w2 : wave 2 = -(1/2:ℝ) := by
    unfold wave
    rw [show 2*((2:ℕ):ℝ)*Real.pi/3=Real.pi/3+Real.pi by ring, Real.cos_add_pi, Real.cos_pi_div_three]
  have tail : (∑' k : ℕ, wave (k+3)*x^(k+3))=series x*x^3 := by
    unfold series
    rw [← tsum_mul_right]
    apply tsum_congr
    intro k
    rw [periodic, pow_add, mul_assoc]
  have h := summable.sum_add_tsum_nat_add 3
  change (∑ k ∈ Finset.range 3, wave k*x^k) + (∑' k : ℕ, wave (k+3)*x^(k+3)) = series x at h
  rw [tail] at h
  norm_num [Finset.sum_range_succ, w0, w1, w2] at h
  apply (mul_left_cancel₀ (a := 1-x) (by linarith))
  linear_combination -h

private def value (n : ℕ) : ℚ :=
  (n:ℚ)*(2*n+1)/(2*((n:ℚ)^2+n+1))

private lemma fraction_eq (n : ℕ) (hn : 2≤n) : fraction n = (value n : ℝ) := by
  have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : (n:ℝ) ≠ 0 := by linarith
  have iden := generating (1/(n:ℝ)) (by positivity) (by
    apply (div_lt_iff₀ (by linarith : 0 < (n:ℝ))).mpr
    simpa using hn')
  have hseries : fraction n = series (1/(n:ℝ)) := by
    simp [fraction, series, wave, div_eq_mul_inv, inv_pow]
  rw [hseries]
  unfold value
  push_cast
  have hd : (n:ℝ)^2+n+1 ≠ 0 := by positivity
  field_simp [hn0, hd] at iden ⊢
  nlinarith only [iden]

-- Exact rational checks of the order-forty differences rule out either choice
-- of overall sign. The same order has opposite signs at consecutive indices.
private def weight (k : ℕ) : ℤ :=
  (-1:ℤ)^(40-k) * ((Nat.factorial 40 / (k.factorial*(40-k).factorial) : ℕ) : ℤ)

private def difference40 (s : ℕ) : ℚ :=
  ∑ k ∈ Finset.range 41, (weight k : ℚ) * value (s+k)

private lemma real_difference (s : ℕ) (hs : 2 ≤ s) :
    (fwdDiff 1)^[40] fraction s = (difference40 s : ℝ) := by
  unfold difference40
  push_cast
  rw [fwdDiff_iter_eq_sum_shift]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k≤40 := by have := Finset.mem_range.mp hk; omega
  have hw : (-1:ℤ)^(40-k) * (Nat.choose 40 k : ℤ) = weight k := by
    rw [weight, Nat.choose_eq_factorial_div_factorial hk']
  have hshift : k • (1:ℕ) = k := by simp
  rw [hw, hshift, zsmul_eq_mul, fraction_eq (s+k) (by omega)]

private lemma opposite_signs :
    0 < (fwdDiff 1)^[40] fraction 2 ∧ (fwdDiff 1)^[40] fraction 3 < 0 := by
  rw [real_difference 2 (by decide), real_difference 3 (by decide)]
  exact ⟨by exact_mod_cast (show 0 < difference40 2 by decide +kernel),
    by exact_mod_cast (show difference40 3 < 0 by decide +kernel)⟩

private lemma first_difference : fwdDiff 1 fraction 2 = 17/182 := by
  norm_num [fwdDiff, fraction_eq 2 (by decide), fraction_eq 3 (by decide), value]

end CosineDifferences

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a373163.main) := by
  intro h
  have h40 := h 40 3 (by decide)
  norm_num only [even_two, Even.neg_one_pow (show Even 40 by decide), one_mul] at h40
  exact (not_lt_of_ge h40) CosineDifferences.opposite_signs.2
