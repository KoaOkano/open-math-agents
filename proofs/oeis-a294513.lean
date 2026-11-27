import OMAStatements.S_oeis_a294513

/-! At `n = 1891`, cancelling a factor of 11 in the harmonic mean
changes the numerator predicted by Wolfdieter Lang's A294513 formula. -/

open OMA.S_oeis_a294513

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a294513.main) := by
  intro h
  exact (by decide +kernel : (a 1891 : ℚ) ≠ 2 * (b (1891 + 1) : ℚ) / ((1891 : ℚ) + 1)) (h 1891)
