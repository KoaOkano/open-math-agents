import OMAStatements.S_oeis_a343073

/-!
Bernat Pagès Vives observed that every successful base is coprime to the
modulus. For an odd base the tower exponent is odd. At an even modulus the
base -1 therefore fails. At an odd modulus above three the bases -2 and -4
cannot both succeed, since 4 and -4 would both have odd order.
-/

namespace TetrationTotient

open OMA.S_oeis_a343073

private def Works (n b : ℕ) : Prop := ∃ x : ℕ, 1 ≤ x ∧ tet b x ≡ 1 [MOD n]

private theorem tower_pos {b : ℕ} (hb : 0 < b) (x : ℕ) : 0 < tet b x := by
  cases x with
  | zero => exact Nat.zero_lt_one
  | succ x => exact pow_pos hb _

private theorem tower_odd {b : ℕ} (hb : Odd b) (x : ℕ) : Odd (tet b x) := by
  cases x with
  | zero => exact odd_one
  | succ x => exact hb.pow

private theorem power_witness {n b : ℕ} (hb : 0 < b) (h : Works n b) :
    ∃ r : ℕ, 0 < r ∧ (Odd b → Odd r) ∧ (b : ZMod n)^r = 1 := by
  obtain ⟨x, hx, hmod⟩ := h
  obtain ⟨x, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
  refine ⟨tet b x, tower_pos hb x, fun ho => tower_odd ho _, ?_⟩
  simpa [tet] using (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod

private theorem all_bases {n : ℕ} (hn : 2 ≤ n) :
    a n = n.totient ↔ ∀ b < n, n.Coprime b → Works n b := by
  let good : Set ℕ := {b | 0 < b ∧ b < n ∧ Works n b}
  let units := (Finset.range n).filter fun b => n.Coprime b
  have hsub : good ⊆ (units : Set ℕ) := by
    rintro b ⟨hb, hlt, h⟩
    obtain ⟨r, hr, _, he⟩ := power_witness hb h
    have hu : IsUnit ((b : ZMod n)^r) := he ▸ isUnit_one
    have hc := (ZMod.isUnit_iff_coprime b n).1 ((isUnit_pow_iff hr.ne').1 hu)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hc.symm⟩
  have hc : ((units : Set ℕ)).ncard = n.totient := Set.ncard_coe_finset _
  change good.ncard = n.totient ↔ _
  constructor
  · intro h b hlt hcop
    have eq := Set.eq_of_subset_of_ncard_le hsub (by omega) units.finite_toSet
    have hb : b ∈ good := eq.symm ▸ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hcop⟩ : b ∈ units)
    exact hb.2.2
  · intro h
    have hrev : (units : Set ℕ) ⊆ good := by
      intro b hb
      obtain ⟨hr, hg⟩ := Finset.mem_filter.mp hb
      have hlt := Finset.mem_range.mp hr
      have hpos : 0 < b := by
        by_contra! he
        have : b = 0 := by omega
        simp [this] at hg
        omega
      exact ⟨hpos, hlt, h b hlt hg⟩
    rw [Set.Subset.antisymm hsub hrev, hc]

private theorem two_nonzero {n : ℕ} (hn : 2 < n) : (2 : ZMod n) ≠ 0 := by
  intro h
  have hd := (ZMod.natCast_eq_zero_iff (2 : ℕ) n).1 (by exact_mod_cast h)
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

private theorem no_more {n : ℕ} (hn : 3 < n) (all : ∀ b < n, n.Coprime b → Works n b) : False := by
  have subcast (d : ℕ) (hd : d ≤ n) : ((n-d : ℕ) : ZMod n) = -(d : ZMod n) := by
    rw [Nat.cast_sub hd, ZMod.natCast_self, zero_sub]
  have hchar := two_nonzero (n := n) (by omega)
  rcases Nat.even_or_odd n with even | odd
  · have h := all (n-1) (by omega) ((Nat.coprime_self_sub_right (by omega)).2 (by simp))
    obtain ⟨r, _, hr, he⟩ := power_witness (by omega) h
    have hodd : Odd (n-1) := by obtain ⟨k, hk⟩ := even; exact ⟨k-1, by omega⟩
    rw [subcast 1 (by omega), Nat.cast_one, (hr hodd).neg_one_pow] at he
    exact hchar (by linear_combination -he)
  · have hc := odd.coprime_two_right
    have hc₄ : n.Coprime 4 := by simpa using hc.pow_right 2
    have h₂ := all (n-2) (by omega) ((Nat.coprime_self_sub_right (by omega)).2 hc)
    have h₄ := all (n-4) (by omega) ((Nat.coprime_self_sub_right (by omega)).2 hc₄)
    obtain ⟨k, hk⟩ := odd
    obtain ⟨r, _, hr, he⟩ := power_witness (by omega) h₂
    obtain ⟨s, _, hs, hf⟩ := power_witness (by omega) h₄
    have hodd₂ : Odd (n-2) := ⟨k-1, by omega⟩
    have hodd₄ : Odd (n-4) := ⟨k-2, by omega⟩
    rw [subcast 2 (by omega), Nat.cast_ofNat] at he
    rw [subcast 4 (by omega), Nat.cast_ofNat, (hs hodd₄).neg_pow] at hf
    have hp : (4 : ZMod n)^r = 1 := by
      calc (4 : ZMod n)^r = ((-2)^2)^r := by norm_num
        _ = ((-2)^r)^2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ = 1 := by rw [he, one_pow]
    have hm : (4 : ZMod n)^s = -1 := by linear_combination -hf
    have ha : (1 : ZMod n) = -1 := by
      calc (1 : ZMod n) = ((4 : ZMod n)^r)^s := by rw [hp, one_pow]
        _ = ((4 : ZMod n)^s)^r := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ = -1 := by rw [hm, (hr hodd₂).neg_one_pow]
    exact hchar (by linear_combination ha)

theorem result : type_of% @OMA.S_oeis_a343073.main := by
  ext n
  change (2 ≤ n ∧ a n = n.totient) ↔ n = 2 ∨ n = 3
  constructor
  · rintro ⟨hn, h⟩
    by_contra! hh
    exact no_more (by omega) ((all_bases hn).1 h)
  · rintro (rfl | rfl)
    · refine ⟨by decide, (all_bases (by decide)).2 ?_⟩
      intro b hb hc
      interval_cases b
      · exact ((by decide : ¬ Nat.Coprime 2 0) hc).elim
      · exact ⟨1, by decide, by decide⟩
    · refine ⟨by decide, (all_bases (by decide)).2 ?_⟩
      intro b hb hc
      interval_cases b
      · exact ((by decide : ¬ Nat.Coprime 3 0) hc).elim
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨2, by decide, by decide⟩

end TetrationTotient

theorem OMA.solution : type_of% @OMA.S_oeis_a343073.main := TetrationTotient.result
