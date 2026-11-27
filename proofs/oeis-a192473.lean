import OMAStatements.S_oeis_a192473
import Mathlib.Tactic

open Polynomial OMA.S_oeis_a192473

namespace PowerRemainder

private noncomputable abbrev modulus : ℤ[X] := X^2 - X - 1

private noncomputable def linearCoeff : ℤ[X] →+ ℤ where
  toFun q := (q %ₘ modulus).coeff 1
  map_zero' := by simp
  map_add' _ _ := by simp [add_modByMonic]

private lemma constant_remainder (q : ℤ[X]) : linearCoeff (1 + q*modulus) = 0 := by
  have hm : modulus.Monic := by unfold modulus; monicity!
  have hd : modulus.degree = 2 := by unfold modulus; compute_degree!
  have h1 : (1 : ℤ[X]) %ₘ modulus = 1 :=
    (modByMonic_eq_self_iff hm).2 (by simp [hd])
  change ((1 + q*modulus) %ₘ modulus).coeff 1 = 0
  simp [add_modByMonic, mul_self_modByMonic hm, h1, coeff_one]

private lemma recurrence (m : ℕ) :
    a (m+4) = 4*a (m+3) - 3*a (m+2) - 2*a (m+1) + a m := by
  -- For the two geometric sequences the characteristic polynomial is evaluated at
  -- X and at X². Both evaluations have the common factor X² − X − 1.
  have h :
      p (m+4) - (4:ℕ) • p (m+3) + (3:ℕ) • p (m+2) + (2:ℕ) • p (m+1) - p m =
        1 + (X^m * (X^2-3*X+1) + X^(2*m+2) * (X^4-X^2-1) * (X^2+X-1)) * modulus := by
    simp only [p, modulus, Nat.mul_add, pow_add, nsmul_eq_mul]
    ring
  have hc := (congrArg linearCoeff h).trans (constant_remainder _)
  simp only [map_add, map_sub, map_nsmul] at hc
  simp only [nsmul_eq_mul] at hc
  change a (m+4) - 4*a (m+3) + 3*a (m+2) + 2*a (m+1) - a m = 0 at hc
  omega

end PowerRemainder

theorem OMA.solution : type_of% @OMA.S_oeis_a192473.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m+4 := ⟨n-4, by omega⟩
  simpa using PowerRemainder.recurrence m
