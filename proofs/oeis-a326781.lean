import OMAStatements.S_oeis_a326781

/-! Disproof of Colin Barker's recurrence for Gus Wiseman's A326781.
It would put 32768 in the sequence, although its only bit has position 16. -/

namespace A326781

open OMA.S_oeis_a326781

private abbrev lowClear (m : ℕ) : Prop :=
  m.testBit 0 = false ∧ m.testBit 1 = false ∧ m.testBit 3 = false ∧ m.testBit 7 = false

private theorem low_iff {m : ℕ} (hm : m < 32768) : Good m ↔ lowClear m := by
  constructor
  · intro h
    have clear (i k : ℕ) (he : i + 1 = 2 ^ k) : m.testBit i = false := by
      cases hb : m.testBit i with
      | false => rfl
      | true => exact (h i hb ⟨k, he⟩).elim
    exact ⟨clear 0 0 rfl, clear 1 1 rfl, clear 3 2 rfl, clear 7 3 rfl⟩
  · rintro ⟨h0, h1, h3, h7⟩ i hb ⟨k, hk⟩
    have hi : i < 15 := by
      by_contra! h
      have bound : 32768 ≤ 2 ^ i := (Nat.pow_le_pow_right (by decide : 0 < 2) h : 2^15 ≤ 2^i)
      simp [Nat.testBit_eq_false_of_lt (hm.trans_le bound)] at hb
    have hk4 : k < 4 := by
      by_contra! h
      have val : 16 ≤ 2 ^ k := (Nat.pow_le_pow_right (by decide : 0 < 2) h : 2^4 ≤ 2^k)
      omega
    have pos : i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 7 := by
      interval_cases k <;> norm_num at hk <;> omega
    rcases pos with rfl | rfl | rfl | rfl <;> simp_all

private theorem initial : a 1 = 0 ∧ a 17 = 256 := by
  classical
  have hz : Good 0 := (low_iff (by decide)).2 (by decide)
  have ht : Good 256 := (low_iff (by decide)).2 (by decide)
  have hc : Nat.count Good 256 = 16 := by
    rw [Nat.count_eq_card_filter_range]
    have eq : (Finset.range 256).filter Good = (Finset.range 256).filter lowClear := by
      apply Finset.filter_congr
      intro m hm
      exact low_iff (by have := Finset.mem_range.mp hm; omega)
    rw [eq]
    decide +kernel
  exact ⟨Nat.nth_zero_of_zero hz, by simpa [a, hc] using Nat.nth_count ht⟩

end A326781

open A326781 OMA.S_oeis_a326781

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a326781.main) := by
  rintro ⟨_, rec⟩
  obtain ⟨h1, h17⟩ := initial
  have shift (j : ℕ) : a (j + 17) = a (j + 1) + 256 := by
    induction j with
    | zero => simpa [h1] using h17
    | succ j ih =>
      have h := rec (j + 18) (by omega)
      simp only [show ∀ x : ℕ, x + 18 - 1 = x + 17 by omega,
        show ∀ x : ℕ, x + 18 - 16 = x + 2 by omega,
        show ∀ x : ℕ, x + 18 - 17 = x + 1 by omega] at h
      change a (j + 18) = a (j + 2) + 256
      omega
  have predicted (k : ℕ) : a (16 * k + 1) = 256 * k := by
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      rw [Nat.mul_succ, show 16 * k + 16 + 1 = 16 * k + 17 by omega, shift, ih]
      omega
  have hbad : Nat.nth Good 2048 = 32768 := predicted 128
  have hg := Nat.nth_mem_of_ne_zero (p := Good) (n := 2048) (by omega)
  rw [hbad] at hg
  exact hg 15 (by decide) ⟨4, rfl⟩
