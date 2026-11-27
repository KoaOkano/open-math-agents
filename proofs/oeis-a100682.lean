import OMAStatements.S_oeis_a100682

open OMA.S_oeis_a100682

-- The four positive exceptions greater than 1 in the source also suggest
-- using the top index N of choose(N,4). At N = 634027531 the two floors
-- still differ, even in that convention.
namespace PentatopeCounterexample

lemma values : fourthRoot (pentatope (634027531 - 3)) = 286454272 ∧
    estimate 634027531 = 286454273 ∧
    fourthRoot (pentatope 634027531) = 286454274 := by decide +kernel

end PentatopeCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a100682.main) := by
  intro h
  have claim := h 634027531 (by decide)
  rw [PentatopeCounterexample.values.2.2, PentatopeCounterexample.values.2.1] at claim
  exact (by decide : (286454274 : ℕ) ≠ 286454273) claim
