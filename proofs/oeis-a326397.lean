import OMAStatements.S_oeis_a326397
import Mathlib.Tactic

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a326397.main) := by
  intro conjectures
  have first := conjectures.2.1 5 (by decide)
  have second := conjectures.2.2 5 (by decide)
  rw [first] at second
  norm_num at second
