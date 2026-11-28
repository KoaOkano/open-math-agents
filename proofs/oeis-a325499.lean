import OMAStatements.S_oeis_a325499
import Mathlib

open OMA.S_oeis_a325499

private abbrev free (n : ℕ) := ¬ 2 ∣ n ∧ ¬ 3 ∣ n

private lemma free_selected {n : ℕ} (hn : 0 < n) (hf : free n) : selected n := by
  rw [selected]
  simp [hn, hf.1, hf.2]

private abbrev hit (n : ℕ) := 2 ∣ n ∧ free (n / 2) ∨ 3 ∣ n ∧ free (n / 3)

private lemma hit_mem {n : ℕ} (hn : 0 < n) (h : hit n) : Mem n := by
  refine ⟨hn, ?_⟩
  rw [selected]
  simp only [hn, ↓reduceDIte, ↓reduceIte]
  rcases h with ⟨hd, hf⟩ | ⟨hd, hf⟩
  · exact fun h => h.1 ⟨hd, free_selected (by omega) hf⟩
  · exact fun h => h.2 ⟨hd, free_selected (by omega) hf⟩

private lemma find_near (x : ℕ) : ∃ t : Fin 7, Mem (x + t.val + 1) := by
  have table : ∀ r : Fin 36, ∃ t : Fin 7, hit (r.val + t.val + 1) := by decide
  obtain ⟨t, ht⟩ := table ⟨x % 36, Nat.mod_lt _ (by decide)⟩
  refine ⟨t, hit_mem (by omega) ?_⟩
  change hit (x % 36 + t.val + 1) at ht
  unfold hit free at *; omega

theorem OMA.solution : type_of% @OMA.S_oeis_a325499.main := by
  rintro x y ⟨hxy, hx, hy, hgap⟩
  obtain ⟨t, ht⟩ := find_near x
  have hle : y - x ≤ 7 := by
    by_contra! h
    exact hgap _ (by omega) (by have := t.isLt; omega) ht
  exact ⟨by omega, hle⟩
