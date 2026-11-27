import OMAStatements.S_oeis_a326390
import Mathlib.Tactic

open OMA.S_oeis_a326390

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a326390.main) := by
  intro conjectures
  have h := conjectures.2.2 5 (by decide)
  change (entry 5 2 : ℚ) = _ at h
  have impossible : 12 * (entry 5 2 : ℚ) = 14057 := by linarith
  have inNaturals : 12 * entry 5 2 = 14057 := by exact_mod_cast impossible
  omega
