import OMAStatements.S_oeis_a273400
import Mathlib.Tactic

open OMA.S_oeis_a273400

namespace IteratedCatalan

private lemma doubling (n : ℕ) (hn : 1 ≤ n) : 2*catalan n ≤ catalan (n+1) := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n+1), ← succ_mul_catalan_eq_centralBinom n] at h
  have ratio : (n+2)*catalan (n+1) = 2*(2*n+1)*catalan n := by
    apply (mul_left_cancel₀ (a := n+1) (by positivity))
    nlinarith only [h]
  apply (Nat.le_of_mul_le_mul_left (c := n+2) · (by positivity))
  nlinarith [Nat.mul_le_mul_right (2*catalan n) (show n+2≤2*n+1 by omega)]

private lemma exponential (k : ℕ) : 2^k ≤ catalan (k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h := doubling (k+1) (by omega)
    omega

private lemma index_le (n : ℕ) : n ≤ catalan n := by
  cases n with
  | zero => simp
  | succ k => exact (Nat.succ_le_of_lt (Nat.lt_two_pow_self : k < 2^k)).trans (exponential k)

private lemma four_times (m : ℕ) (hm : 6 ≤ m) : 4*m+1 ≤ catalan m := by
  induction m, hm using Nat.le_induction with
  | base => have h := exponential 5; norm_num at h ⊢; omega
  | succ m hm ih => have h := doubling m (by omega); omega

private lemma digits_bound (n : ℕ) (hn : 6 ≤ n) : catalan n < (Nat.digits 10 (a n)).length := by
  let x := catalan n
  have hx : 6 ≤ x := hn.trans (index_le n)
  have hsize := four_times x hx
  have hexp := exponential (catalan x-1)
  rw [show catalan x-1+1=catalan x by omega] at hexp
  have hp : 10^x ≤ a n := calc
    10^x ≤ (2^4)^x := Nat.pow_le_pow_left (by decide) _
    _ = 2^(4*x) := (pow_mul 2 4 x).symm
    _ ≤ 2^(catalan x-1) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ a n := hexp
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 10)).mp
    (hp.trans_lt (Nat.lt_base_pow_length_digits (by decide)))

end IteratedCatalan

theorem OMA.solution : type_of% @OMA.S_oeis_a273400.main := by
  apply (Set.finite_Iio 6).subset
  intro n hn
  change (Nat.digits 10 (a n)).length < catalan n at hn
  change n < 6
  by_contra h
  exact (Nat.not_lt_of_ge (IteratedCatalan.digits_bound n (by omega)).le) hn
