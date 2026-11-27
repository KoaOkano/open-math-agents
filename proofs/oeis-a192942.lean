import OMAStatements.S_oeis_a192942
import Mathlib.Tactic

open Polynomial OMA.S_oeis_a192942

namespace ProductRemainder

private noncomputable abbrev modulus : ℤ[X] := X^2 - X - 1

private noncomputable def linearCoeff : ℤ[X] →+ ℤ where
  toFun q := (q %ₘ modulus).coeff 1
  map_zero' := by simp
  map_add' _ _ := by simp [add_modByMonic]

private lemma step (m : ℕ) :
    p (m+1) = p m * (C 2 * X + C ((m+1 : ℕ) : ℤ)) := by
  exact Finset.prod_Icc_succ_top (by omega) _

-- The last two factors leave four times the modulus after the recurrence is formed.
private lemma recurrence (m : ℕ) :
    a (m+2) + (-2*((m:ℤ)+2)-1) * a (m+1) + (((m:ℤ)+2)^2-5) * a m = 0 := by
  have h :
      p (m+2) + (-2*((m:ℤ)+2)-1) • p (m+1) + (((m:ℤ)+2)^2-5) • p m
        = (4 * p m) * modulus := by
    rw [step (m+1), step m]
    simp [modulus, Polynomial.smul_eq_C_mul]
    ring
  have hm : modulus.Monic := by unfold modulus; monicity!
  have hz : linearCoeff ((4 * p m) * modulus) = 0 := by
    change (((4 * p m) * modulus) %ₘ modulus).coeff 1 = 0
    rw [mul_self_modByMonic hm, coeff_zero]
  have hc := (congrArg linearCoeff h).trans hz
  simp only [map_add, map_zsmul] at hc
  simpa [zsmul_eq_mul, linearCoeff, a, modulus] using hc

end ProductRemainder

theorem OMA.solution : type_of% @OMA.S_oeis_a192942.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
  simpa using ProductRemainder.recurrence m
