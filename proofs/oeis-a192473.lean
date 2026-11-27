import OMAStatements.S_oeis_a192473

/-!
Colin Barker's recurrence for Clark Kimberling's OEIS A192473.
The powers of X and X² have respective annihilators t² − t − 1 and
t² − 3t + 1 modulo X² − X − 1. Their product gives the recurrence.
Lean proof by KoaOkano, assisted by OpenAI Codex.
-/

open Polynomial OMA.S_oeis_a192473

private noncomputable abbrev divisor : ℤ[X] := X ^ 2 - X - 1

private noncomputable def difference (k : ℕ) : ℤ[X] :=
  p (k + 4) - 4 • p (k + 3) + 3 • p (k + 2) + 2 • p (k + 1) - p k - 1

private theorem divides_difference (k : ℕ) : divisor ∣ difference k := by
  refine ⟨X ^ k * (X ^ 2 - 3 * X + 1) +
    X ^ (2 * k + 2) * (X ^ 2 + X - 1) * (X ^ 4 - X ^ 2 - 1), ?_⟩
  simp only [difference, p, divisor, pow_add, nsmul_eq_mul, Nat.cast_ofNat]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a192473.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hm : divisor.Monic := by unfold divisor; monicity!
  have hd : divisor.degree = 2 := by unfold divisor; compute_degree!
  have h1 : (1 : ℤ[X]) %ₘ divisor = 1 :=
    (modByMonic_eq_self_iff hm).2 (by rw [hd, degree_one]; decide)
  have hc : (1 : ℤ[X]).coeff 1 = 0 := by simp [coeff_one]
  have hz : modByMonicHom divisor (difference k) = 0 :=
    (modByMonic_eq_zero_iff_dvd hm).2 (divides_difference k)
  have h := congrArg (lcoeff ℤ 1) hz
  simp only [difference, map_add, map_sub, map_nsmul, map_zero] at h
  simp only [modByMonicHom_apply, lcoeff_apply, nsmul_eq_mul, Nat.cast_ofNat,
    h1, hc, sub_zero] at h
  unfold a
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  change (p (k + 4) %ₘ divisor).coeff 1 = _
  linarith
