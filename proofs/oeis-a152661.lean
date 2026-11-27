import OMAStatements.S_oeis_a152661
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open OMA.S_oeis_a152661

-- After splitting by parity, the counts are polynomials times a common factorial.
theorem OMA.solution : type_of% @OMA.S_oeis_a152661.main := by
  have half (k j : ℕ) : (2 * k + j) / 2 = k + j / 2 := by omega
  constructor <;> intro t <;>
    obtain ⟨k, hk | hk⟩ : ∃ k, t = 2 * k ∨ t = 2 * k + 1 := ⟨t / 2, by omega⟩ <;>
    subst t <;>
    simp (disch := decide) [sameParity, evenOddPairs, Nat.add_assoc, Nat.add_sub_assoc,
      half, Nat.factorial_succ] <;>
    ring
