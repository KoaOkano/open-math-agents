import OMAStatements.S_oeis_a188648

/-!
Velin Yanev's terminating hypergeometric formula for A188648 follows by
reversing the binomial sum. Its term at index k is precisely the square
of binom(n+k, 2k) for k ≤ n. The factorial duplication formula for
(1/2)ₖ cancels the powers of 16 in the hypergeometric series.
-/

namespace BinomialSquares188648

open OMA.S_oeis_a188648

private lemma half_factorial (k : ℕ) :
    (4 : ℚ)^k * (ascPochhammer ℚ k).eval (1/2) * k.factorial = (2*k).factorial := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, ascPochhammer_succ_eval, Nat.factorial_succ k,
      show 2*(k+1) = (2*k+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ (2*k)]
    push_cast
    rw [← ih]
    ring

private lemma binomial_product (n k : ℕ) (hk : k ≤ n) :
    n.descFactorial k * (n+1).ascFactorial k =
      (n+k).choose (2*k) * (2*k).factorial := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos (n-k))
  rw [← Nat.mul_assoc, Nat.factorial_mul_descFactorial hk, Nat.factorial_mul_ascFactorial]
  have h := Nat.choose_mul_factorial_mul_factorial (show 2*k ≤ n+k by omega)
  rw [show n+k-2*k = n-k by omega] at h
  simpa only [Nat.mul_comm (n-k).factorial] using h.symm

private lemma summand (n k : ℕ) (hk : k ≤ n) :
    term n k = ((n+k).choose (2*k) : ℚ)^2 := by
  let A := (ascPochhammer ℚ k).eval (-(n : ℚ))
  let B := (ascPochhammer ℚ k).eval ((n : ℚ)+1)
  let C := (ascPochhammer ℚ k).eval (1/2)
  let K := (k.factorial : ℚ)
  let P := (4 : ℚ)^k
  have hden : P*C*K = ((2*k).factorial : ℚ) := half_factorial k
  have hK : K ≠ 0 := by dsimp [K]; positivity
  have hP : P ≠ 0 := by dsimp [P]; positivity
  have hC : C ≠ 0 := by
    intro hz
    rw [hz, mul_zero, zero_mul] at hden
    exact (show ((2*k).factorial : ℚ) ≠ 0 by positivity) hden.symm
  have hnum : A*B = (-1:ℚ)^k * ((n+k).choose (2*k) : ℚ) * (2*k).factorial := by
    dsimp only [A, B]
    rw [ascPochhammer_eval_neg_eq_descPochhammer ℚ (n:ℚ),
      descPochhammer_eval_eq_descFactorial, ← Nat.cast_one (R := ℚ),
      ← Nat.cast_add, ← Nat.cast_ascFactorial]
    have h := congrArg (fun z : ℕ => (z : ℚ)) (binomial_product n k hk)
    push_cast at h
    linear_combination (-1:ℚ)^k * h
  have hquot : (A*B)/(C*K*P) = (-1:ℚ)^k * ((n+k).choose (2*k) : ℚ) := by
    apply (div_eq_iff (mul_ne_zero (mul_ne_zero hC hK) hP)).mpr
    rw [hnum, ← hden]
    ring
  have h16 : (1/16 : ℚ)^k = (P*P)⁻¹ := by
    dsimp [P]
    rw [← mul_pow, ← inv_pow]
    norm_num
  calc
    term n k = ((A*B)/(C*K*P))^2 := by
      unfold term
      rw [ascPochhammer_eval_one, h16]
      change A*A*B*B/(C*C*K)*(P*P)⁻¹/K = _
      field_simp [hC, hK, hP]
    _ = _ := by
      rw [hquot, mul_pow, pow_right_comm (-1 : ℚ) k 2]
      norm_num

end BinomialSquares188648

open Finset BinomialSquares188648 OMA.S_oeis_a188648

theorem OMA.solution : type_of% @OMA.S_oeis_a188648.main := by
  intro n
  have hsum : HasSum (term n) (∑ k ∈ range (n+1), term n k) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hnk : n < k := by simp only [mem_range, not_lt] at hk; omega
    simp [term, ascPochhammer_eval_neg_coe_nat_of_lt hnk]
  convert hsum using 1
  unfold a
  push_cast
  rw [← sum_range_reflect (fun k : ℕ => ((2*n-k).choose k : ℚ)^2) (n+1)]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa only [mem_range, Nat.lt_succ_iff] using hk
  rw [summand _ _ hkn]
  simp only [Nat.add_one_sub_one]
  rw [show 2*n-(n-k) = n+k by omega, ← Nat.choose_symm (show n-k ≤ n+k by omega),
    show n+k-(n-k) = 2*k by omega]
