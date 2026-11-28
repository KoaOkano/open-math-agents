import OMAStatements.S_oeis_a222013
import Mathlib

open PowerSeries

namespace OEISParity

private abbrev F := ZMod 2
private abbrev S := PowerSeries F
private abbrev red := PowerSeries.map (Int.castRingHom F)

private theorem parity (B : S) (hb : B = 1 + B ^ 2 * X) (n : ℕ) :
    coeff n B = 1 ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  have hfr : frobenius F 2 = RingHom.id F := by
    ext a
    exact ZMod.pow_card a
  have hs : B ^ 2 = expand 2 (by decide) B := by
    have h := MvPowerSeries.map_frobenius_expand (f := B) 2 (by decide)
    rw [hfr, MvPowerSeries.map_id] at h
    exact h.symm
  have h0 : coeff 0 B = 1 := by
    have h := congrArg (coeff 0) hb
    simpa using h
  have hstep (m : ℕ) : coeff (m + 1) B =
      if 2 ∣ m then coeff (m / 2) B else 0 := by
    have h := congrArg (coeff (m + 1)) hb
    simpa [coeff_one, coeff_succ_mul_X, hs, coeff_expand] using h
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact iff_of_true h0 ⟨0, rfl⟩
    | succ m =>
      rw [hstep]
      by_cases he : 2 ∣ m
      · obtain ⟨u, rfl⟩ := he
        rw [if_pos (dvd_mul_right 2 u), show 2 * u / 2 = u by omega]
        refine (ih u (by omega)).trans ?_
        constructor
        · rintro ⟨k, hk⟩
          exact ⟨k + 1, by rw [pow_succ]; omega⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk
          | succ k => exact ⟨k, by rw [pow_succ] at hk; omega⟩
      · rw [if_neg he]
        constructor
        · intro h
          exact (zero_ne_one h).elim
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk
          | succ k => rw [pow_succ] at hk; omega

end OEISParity

open OEISParity OMA.S_oeis_a222013

theorem OMA.solution : type_of% @OMA.S_oeis_a222013.main := by
  classical
  rintro A ⟨T, ht, ha⟩ n
  let B : PowerSeries (ZMod 2) := red A
  let U : ℕ → PowerSeries (ZMod 2) := fun k => red (T k)
  have htwo : (2 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (PowerSeries.C (R := ZMod 2)) (show (2 : ZMod 2) = 0 by decide)
  have hu0 : U 0 = 1 := by simpa [U, red] using congrArg red (ht 0)
  have hu1 : U 1 * (1 + X * B) = X * B := by
    simpa [U, B, red] using congrArg red (ht 1)
  have hu (k : ℕ) (hk : 2 ≤ k) : U k = 0 := by
    have hf : (k.factorial : ZMod 2) = 0 :=
      (CharP.cast_eq_zero_iff _ 2 _).2 (Nat.dvd_factorial (by decide) hk)
    have hfac : (k.factorial : PowerSeries (ZMod 2)) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg (PowerSeries.C (R := ZMod 2)) hf
    have h := congrArg red (ht k)
    simp only [map_mul, map_prod, map_add, map_one, map_natCast, map_X, map_pow, hfac,
      zero_mul] at h
    apply (mul_eq_zero.mp h).resolve_right
    intro hzero
    have hc := congrArg (PowerSeries.constantCoeff (R := ZMod 2)) hzero
    simp at hc
  have hconst : coeff 0 (U 1) = 0 := by
    have h := congrArg (PowerSeries.constantCoeff (R := ZMod 2)) hu1
    simpa [coeff_zero_eq_constantCoeff] using h
  have hB : B = 1 + U 1 := by
    ext m
    have hm : coeff m B = ∑ k ∈ Finset.range (m+1), coeff m (U k) := by
      simpa [B, U, red, coeff_map] using congrArg (Int.castRingHom (ZMod 2)) (ha m)
    rw [hm, map_add]
    cases m with
    | zero => simp [hu0, hconst]
    | succ m =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp [hu0, hu, show ∀ i : ℕ, 2 ≤ i + 1 + 1 by omega]
  have heq : B * (1 + X * B) = 1 := by
    calc
      B * (1 + X * B) = (1 + U 1) * (1 + X * B) := congrArg (· * _) hB
      _ = 1 := by rw [add_mul, one_mul, hu1, add_assoc, ← two_mul, htwo, zero_mul, add_zero]
  have hb : B = 1 + B ^ 2 * X := by
    rw [mul_add, mul_one] at heq
    calc
      B = (B + B * (X * B)) + B * (X * B) := by
        rw [add_assoc, ← two_mul, htwo, zero_mul, add_zero]
      _ = 1 + B ^ 2 * X := by rw [heq]; ring
  change (coeff n A) % 2 = 1 ↔ _
  rw [← Int.odd_iff, ← ZMod.intCast_eq_one_iff_odd]
  have hm : coeff n B = ((coeff n A : ℤ) : ZMod 2) := coeff_map _ _ _
  rw [← hm, parity B hb]
  exact exists_congr fun k => by have := Nat.two_pow_pos k; omega
