import OMAStatements.S_oeis_a382437

/-!
The sequence in OEIS A382437 is twice the Chebyshev value T at 2 with
index 2^n, minus 2. Expanding at 1 gives V. Barbera's binomial sum.
Lean proof by KoaOkano, assisted by OpenAI Codex.
-/

open Polynomial Polynomial.Chebyshev Finset OMA.S_oeis_a382437

private def fac (k : ℕ) : ℚ := k.factorial

private theorem fac_succ (k : ℕ) : fac (k+1) = (k+1 : ℚ) * fac k := by
  simp [fac, Nat.factorial_succ]

private theorem fac_pos (k : ℕ) : 0 < fac k := by
  unfold fac
  exact_mod_cast Nat.factorial_pos k

private noncomputable def c (m k : ℕ) : ℚ := 2 * (taylor 1 (T ℚ m)).coeff k

private theorem derivative_value (m k : ℕ) :
    (derivative^[k] (T ℚ m)).eval 1 = fac k * (taylor 1 (T ℚ m)).coeff k := by
  rw [← factorial_smul_hasseDeriv, taylor_coeff]
  simp [fac, nsmul_eq_mul]

private theorem coefficient_recurrence (m k : ℕ) :
    (2 * (k:ℚ) + 1) * (k+1) * c m (k+1) =
      ((m:ℚ)^2 - (k:ℚ)^2) * c m k := by
  have h := iterate_derivative_T_eval_one_recurrence (R := ℚ) (m : ℤ) k
  rw [derivative_value, derivative_value, fac_succ] at h
  push_cast at h
  apply mul_left_cancel₀ (fac_pos k).ne'
  unfold c
  linear_combination 2 * h

private theorem coefficient_factorials (k s : ℕ) :
    c (k+1+s) (k+1) * fac (2*k+2) * fac s =
      2 * ((k+1+s : ℕ) : ℚ) * 2^(k+1) * fac (2*k+1+s) := by
  induction k generalizing s with
  | zero =>
    have h := coefficient_recurrence (1+s) 0
    have h0 : c (1+s) 0 = 2 := by simp [c, T_eval_one]
    rw [h0] at h
    norm_num at h
    simp only [Nat.zero_add, Nat.mul_zero, show 1+s = s+1 by omega] at h ⊢
    rw [fac_succ s]
    norm_num [fac] at h ⊢
    linear_combination 2 * (s.factorial : ℚ) * h
  | succ k ih =>
    have old := ih (s+1)
    rw [show k+1+(s+1) = k+2+s by omega,
      show 2*k+1+(s+1) = 2*k+2+s by omega, fac_succ s] at old
    have step := coefficient_recurrence (k+2+s) (k+1)
    change c (k+2+s) (k+2) * fac (2*(k+1)+2) * fac s =
      2 * ((k+2+s : ℕ) : ℚ) * 2^(k+2) * fac (2*(k+1)+1+s)
    rw [show 2*(k+1)+2 = (2*k+2)+1+1 by omega,
      show 2*(k+1)+1+s = (2*k+2+s)+1 by omega,
      fac_succ (2*k+2+1), fac_succ (2*k+2), fac_succ (2*k+2+s),
      pow_succ (2:ℚ) (k+1)]
    push_cast at old step ⊢
    linear_combination 2 * fac (2*k+2) * fac s * step +
      (2 * (2*(k:ℚ)+(s:ℚ)+3)) * old

private theorem positive_coefficient (j s : ℕ) :
    c (j+1+s) (j+1) = ((j+1+s : ℕ) : ℚ) * 2^(j+1) *
      ((2*j+1+s).choose (2*j+1) : ℚ) / (j+1) := by
  have h := coefficient_factorials j s
  have hb : ((2*j+1+s).choose (2*j+1) : ℚ) * fac (2*j+1) * fac s =
      fac (2*j+1+s) := by
    unfold fac
    have hnat := Nat.choose_mul_factorial_mul_factorial
      (show 2*j+1 ≤ 2*j+1+s by omega)
    rw [show 2*j+1+s-(2*j+1) = s by omega] at hnat
    exact_mod_cast hnat
  rw [show 2*j+2 = 2*j+1+1 by omega, fac_succ, ← hb] at h
  apply (eq_div_iff (by positivity)).2
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℚ) ≠ 0)
    (fac_pos (2*j+1)).ne') (fac_pos s).ne')
  push_cast at h ⊢
  linear_combination h

private theorem chebyshev_sum (m : ℕ) :
    2 * (T ℚ m).eval 2 - 2 = ∑ k ∈ Icc 1 m,
      (m:ℚ) * 2^k * ((m+k-1).choose (2*k-1) : ℚ) / (k:ℚ) := by
  have he := (taylor 1 (T ℚ (m:ℤ))).eval_eq_sum_range (1:ℚ)
  rw [taylor_eval] at he
  simp only [natDegree_taylor, natDegree_T, Int.natAbs_natCast, one_pow, mul_one] at he
  have hs : range (m+1) = insert 0 (Icc 1 m) := by
    ext k
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hs, sum_insert (by simp)] at he
  have h0 : (taylor 1 (T ℚ (m:ℤ))).coeff 0 = 1 := by simp [T_eval_one]
  rw [h0] at he
  norm_num at he
  calc
    2 * (T ℚ m).eval 2 - 2 = ∑ k ∈ Icc 1 m, c m k := by
      unfold c
      rw [← mul_sum]
      linarith
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      obtain ⟨hpos, hle⟩ := mem_Icc.mp hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := ⟨k-1, by omega⟩
      obtain ⟨s, rfl⟩ : ∃ s, m = j+1+s := ⟨m-(j+1), by omega⟩
      simpa only [show j+1+s+(j+1)-1 = 2*j+1+s by omega,
        show 2*(j+1)-1 = 2*j+1 by omega, Nat.cast_add, Nat.cast_one] using
        positive_coefficient j s

private theorem sequence_value (n : ℕ) :
    (a n : ℚ) = 2 * (T ℚ ((2:ℤ)^n)).eval 2 - 2 := by
  induction n with
  | zero => norm_num [a, T_one]
  | succ n ih =>
    have h := congrArg (Polynomial.eval (2:ℚ))
      (T_mul_T (R := ℚ) ((2:ℤ)^n) ((2:ℤ)^n))
    simp only [eval_mul, eval_ofNat, eval_add, sub_self, T_zero, eval_one] at h
    rw [a]
    push_cast
    rw [ih, pow_succ (2:ℤ), mul_two]
    nlinarith

theorem OMA.solution : type_of% @OMA.S_oeis_a382437.main := by
  intro n
  have h := chebyshev_sum (2^n)
  push_cast at h
  exact (sequence_value n).trans h
