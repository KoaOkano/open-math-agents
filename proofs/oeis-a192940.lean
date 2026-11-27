import OMAStatements.S_oeis_a192940
import Mathlib.Tactic

open Polynomial OMA.S_oeis_a192940

namespace EvenProductRemainder

private noncomputable abbrev modulus : ℤ[X] := X^2 - X - 1

private noncomputable def linearCoeff : ℤ[X] →+ ℤ where
  toFun q := (q %ₘ modulus).coeff 1
  map_zero' := by simp
  map_add' _ _ := by simp [add_modByMonic]

private lemma step (m : ℕ) :
    p (m+1) = p m * (X + C (2 * ((m+1 : ℕ) : ℤ))) := by
  exact Finset.prod_Icc_succ_top (by omega) _

-- The polynomial recurrence has remainder zero before taking its linear coefficient.
private lemma recurrence (m : ℕ) :
    a (m+2) + (-4*((m:ℤ)+2)+1) * a (m+1) +
      (4*((m:ℤ)+2)^2-6*((m:ℤ)+2)+1) * a m = 0 := by
  have h :
      p (m+2) + (-4*((m:ℤ)+2)+1) • p (m+1) +
        (4*((m:ℤ)+2)^2-6*((m:ℤ)+2)+1) • p m = p m * modulus := by
    rw [step (m+1), step m]
    simp [modulus, Polynomial.smul_eq_C_mul]
    ring
  have hm : modulus.Monic := by unfold modulus; monicity!
  have hz : linearCoeff (p m * modulus) = 0 := by
    change ((p m * modulus) %ₘ modulus).coeff 1 = 0
    rw [mul_self_modByMonic hm, coeff_zero]
  have hc := (congrArg linearCoeff h).trans hz
  simp only [map_add, map_zsmul] at hc
  simpa [zsmul_eq_mul, linearCoeff, a, modulus] using hc

end EvenProductRemainder

theorem OMA.solution : type_of% @OMA.S_oeis_a192940.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
  simpa using EvenProductRemainder.recurrence m
