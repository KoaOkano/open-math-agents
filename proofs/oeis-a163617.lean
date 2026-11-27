import OMAStatements.S_oeis_a163617
import Mathlib.Tactic

open OMA.S_oeis_a163617

namespace GrayRecurrence

lemma sign (n : ℕ) : (-1 : ℤ)^n = 1-2*(n%2 : ℕ) := by
  calc
    (-1 : ℤ)^n = (-1 : ℤ)^(2*(n/2) + n%2) := by congr 1; omega
    _ = _ := by
      rw [pow_add, pow_mul]
      rcases (show n%2=0 ∨ n%2=1 by omega) with h | h <;> norm_num [h]

lemma gray_step (n : ℕ) :
    ((n ^^^ (n/2) : ℕ) : ℤ) =
      2 * (((n/2) ^^^ ((n/2)/2) : ℕ) : ℤ) + ((n+n/2)%2 : ℕ) := by
  have h := Nat.mod_add_div (n ^^^ (n/2)) 2
  rw [Nat.xor_mod_two_eq, Nat.xor_div_two] at h
  exact_mod_cast (show n ^^^ (n/2) = 2*((n/2) ^^^ ((n/2)/2)) + (n+n/2)%2 by omega)

end GrayRecurrence

theorem OMA.solution : type_of% @OMA.S_oeis_a163617.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => norm_num [a]
    | succ m =>
      have h := ih ((m+1)/2) (by omega)
      rw [a, GrayRecurrence.gray_step]
      simp only [GrayRecurrence.sign] at h ⊢
      split_ifs with hbit <;> push_cast at * <;> omega
