import OMAStatements.S_oeis_a110515

/-! Paul Barry's Jacobi-symbol formula for the sequence array A110515.
The numerator and the supplementary law for 2 give the same four signs. -/

namespace A110515

open PowerSeries OMA.S_oeis_a110515

private def sign (n : ℕ) : ℚ := if n % 4 = 1 then -1 else 1

private theorem symbol (n : ℕ) : (jacobiSym ((2 : ℤ) ^ n) (2 * n + 1) : ℚ) = sign n := by
  rw [jacobiSym.pow_left, jacobiSym.at_two (Nat.odd_iff.mpr (by omega)),
    ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega : (2*n+1) % 2 ≠ 0)]
  by_cases h : (2*n+1) % 8 = 1 ∨ (2*n+1) % 8 = 7
  · simp [h, sign, show n % 4 ≠ 1 by omega]
  · rw [if_neg h, neg_one_pow_eq_pow_mod_two]
    by_cases r : n % 4 = 1
    · simp [sign, r, show n % 2 = 1 by omega]
    · simp [sign, r, show n % 2 = 0 by omega]

private theorem series : G = mk sign := by
  have hp : mk sign * (1 - X ^ 4) = 1 - X + X ^ 2 + X ^ 3 := by
    ext n
    by_cases hn : n < 4
    · interval_cases n <;>
        norm_num [mul_sub, coeff_mul_X_pow', coeff_X_pow, coeff_X, coeff_one, sign]
    · have h₄ : 4 ≤ n := by omega
      have period : (n - 4) % 4 = n % 4 := by omega
      simp [mul_sub, coeff_mul_X_pow', coeff_X_pow, coeff_X, coeff_one, sign, h₄, period,
        show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega]
  unfold G
  rw [← hp, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp), mul_one]

end A110515

open A110515 OMA.S_oeis_a110515

theorem OMA.solution : type_of% @OMA.S_oeis_a110515.main := by
  intro n k
  by_cases h : k ≤ n
  · simpa [T, h, series] using (symbol (n - k)).symm
  · simp [T, h]
