import OMAStatements.S_oeis_a325498
import Mathlib

open OMA.S_oeis_a325498

private abbrev free (n : ℕ) := ¬ 2 ∣ n ∧ ¬ 3 ∣ n

private lemma free_selected {n : ℕ} (hn : 0 < n) (hf : free n) : selected n := by
  rw [selected]
  simp [hn, hf.1, hf.2]

private lemma find_near (x : ℕ) : ∃ t : Fin 4, Mem (x + t.val + 1) := by
  have table : ∀ r : Fin 6, ∃ t : Fin 4, free (r.val + t.val + 1) := by decide
  obtain ⟨t, ht⟩ := table ⟨x % 6, Nat.mod_lt _ (by decide)⟩
  refine ⟨t, free_selected (by omega) ?_⟩
  change free (x % 6 + t.val + 1) at ht
  unfold free at *; omega

theorem OMA.solution : type_of% @OMA.S_oeis_a325498.main := by
  rintro x y ⟨hxy, hx, hy, hgap⟩
  obtain ⟨t, ht⟩ := find_near x
  have hle : y - x ≤ 4 := by
    by_contra! h
    exact hgap _ (by omega) (by have := t.isLt; omega) ht
  exact ⟨by omega, hle⟩
