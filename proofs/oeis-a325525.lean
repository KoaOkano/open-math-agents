import OMAStatements.S_oeis_a325525
import Mathlib

open OMA.S_oeis_a325525

private abbrev free (n : ℕ) := ¬ 3 ∣ n ∧ ¬ 4 ∣ n

private lemma free_selected {n : ℕ} (hn : 0 < n) (hf : free n) : selected n := by
  rw [selected]
  simp [hn, hf.1, hf.2]

private abbrev hit (n : ℕ) := 3 ∣ n ∧ free (n / 3)

private lemma hit_mem {n : ℕ} (hn : 0 < n) (h : hit n) : Mem n := by
  refine ⟨hn, ?_⟩
  rw [selected]
  simp only [hn, ↓reduceDIte, ↓reduceIte]
  exact fun hs => hs.1 ⟨h.1, free_selected (by have := h.1; omega) h.2⟩

private lemma find_near (x : ℕ) : ∃ t : Fin 9, Mem (x + t.val + 1) := by
  have table : ∀ r : Fin 36, ∃ t : Fin 9, hit (r.val + t.val + 1) := by decide
  obtain ⟨t, ht⟩ := table ⟨x % 36, Nat.mod_lt _ (by decide)⟩
  refine ⟨t, hit_mem (by omega) ?_⟩
  change hit (x % 36 + t.val + 1) at ht
  unfold hit free at *; omega

private lemma exclude_eight {x : ℕ} (hx : Mem x) (hy : Mem (x + 8)) :
    ∃ t : Fin 7, Mem (x + t.val + 1) := by
  have table : ∀ r : Fin 36, free r.val ∨ free (r.val + 8) ∨
      ∃ t : Fin 7, hit (r.val + t.val + 1) := by decide
  have hx' : ¬ free x := fun h => hx.2 (free_selected hx.1 h)
  have hy' : ¬ free (x + 8) := fun h => hy.2 (free_selected hy.1 h)
  rcases table ⟨x % 36, Nat.mod_lt _ (by decide)⟩ with h | h | ⟨t, h⟩
  · change free (x % 36) at h
    exact False.elim (hx' (by unfold free at *; omega))
  · change free (x % 36 + 8) at h
    exact False.elim (hy' (by unfold free at *; omega))
  · change hit (x % 36 + t.val + 1) at h
    exact ⟨t, hit_mem (by omega) (by unfold hit free at *; omega)⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a325525.main := by
  rintro x y ⟨hxy, hx, hy, hgap⟩
  obtain ⟨t, ht⟩ := find_near x
  have hle : y - x ≤ 9 := by
    by_contra! h
    exact hgap _ (by omega) (by have := t.isLt; omega) ht
  refine ⟨by omega, hle, ?_⟩
  intro he
  obtain rfl : y = x + 8 := by omega
  obtain ⟨u, hu⟩ := exclude_eight hx hy
  exact hgap _ (by omega) (by have := u.isLt; omega) hu
