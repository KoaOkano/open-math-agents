import OMAStatements.S_oeis_a218459

/-!
For the prime 102047063 the least coefficient is 779 = 19 · 41.
The displayed representation gives the upper bound. For the lower bound,
first discard coefficients for which the prime is a quadratic nonresidue
modulo the coefficient, then test the remaining possible absolute values of y.
-/

namespace QuadraticMinimum

open OMA.S_oeis_a218459

private abbrev p : ℕ := 102047063

private def modEight (d : ℕ) : Bool := d % 8 == 3 || d % 8 == 6 || d % 8 == 7

private theorem modEight_required (d x y : ℕ) (h : p = x ^ 2 + d * y ^ 2) : modEight d = true := by
  have table : ∀ i j k : Fin 8, (j.val ^ 2 + i.val * k.val ^ 2) % 8 = 7 → modEight i.val = true := by
    decide +kernel
  have hmod : (x ^ 2 + d * y ^ 2) % 8 = 7 := h ▸ rfl
  have s := table ⟨d % 8, Nat.mod_lt _ (by decide)⟩ ⟨x % 8, Nat.mod_lt _ (by decide)⟩
    ⟨y % 8, Nat.mod_lt _ (by decide)⟩
  dsimp only at s
  have same := ((Nat.mod_modEq x 8).pow 2).add ((Nat.mod_modEq d 8).mul ((Nat.mod_modEq y 8).pow 2))
  simpa only [modEight, Nat.mod_mod] using s (Eq.trans same hmod)

private def reject (d : ℕ) : Bool :=
  if modEight d && (List.range d).any (fun r => r ^ 2 % d == p % d) then
    (List.range ((p / d).sqrt + 1)).all fun y =>
      let rest := p - d * y ^ 2
      rest.sqrt ^ 2 != rest
  else true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem smaller : (List.range 778).all (fun i => reject (i + 1)) = true := by
  decide +kernel

private theorem least : a p = 779 := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨by decide, 7278, 251, by norm_num [p]⟩
  · rintro d ⟨hd, x, y, eq⟩
    by_contra! hlt
    have eqNat : p = x.natAbs ^ 2 + d * y.natAbs ^ 2 := by
      have h : (p : ℤ) = (x.natAbs : ℤ) ^ 2 + (d : ℤ) * (y.natAbs : ℤ) ^ 2 := by
        simpa only [Int.natCast_natAbs, sq_abs] using eq
      exact_mod_cast h
    have row := List.all_eq_true.mp smaller (d - 1) (List.mem_range.mpr (by omega))
    rw [show d - 1 + 1 = d by omega] at row
    have residue : (List.range d).any (fun r => r ^ 2 % d == p % d) = true := by
      refine List.any_eq_true.mpr ⟨x.natAbs % d, List.mem_range.mpr (Nat.mod_lt _ hd), beq_iff_eq.mpr ?_⟩
      rw [← Nat.pow_mod, eqNat, Nat.add_mul_mod_self_left]
    have hy : y.natAbs ≤ (p / d).sqrt := by
      apply Nat.le_sqrt'.mpr
      apply (Nat.le_div_iff_mul_le hd).mpr
      rw [Nat.mul_comm, eqNat]
      omega
    simp only [reject, modEight_required _ _ _ eqNat, residue, Bool.and_self, if_true] at row
    have hn := List.all_eq_true.mp row y.natAbs (List.mem_range.mpr (by omega))
    have he : p - d * y.natAbs ^ 2 = x.natAbs ^ 2 := by omega
    simp [he, Nat.sqrt_eq'] at hn

end QuadraticMinimum

open OMA.S_oeis_a218459 QuadraticMinimum

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a218459.main) := by
  intro h
  have hp : Nat.Prime p := by norm_num [p]
  have hc := h (Nat.count Nat.Prime p)
  rw [Nat.nth_count hp, least] at hc
  have bad := (hc ⟨389, rfl⟩ (by decide) (by norm_num)).2
  norm_num at bad
