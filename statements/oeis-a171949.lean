import Mathlib

/-!
# Losing positions in the game Mark-4

From n, a player may subtract 1, 2 or 3 without going below zero, or move
to floor(n/4) if this reduces n. Zero has no legal move. A P-position is
one from which every legal move reaches an N-position.

A171949 enumerates the P-positions, starting at index one with zero.
A217319 enumerates positive integers whose count of trailing binary zeros
is 2 or 3 modulo 4. This count is the exponent of 2 in the factorization.
Writing the original index as k+2 gives Shevelev's proposed shift below.
See also A. S. Fraenkel, The vile, dopey, evil and odious game players
(2012), for the general base-t game and its losing-position theorem.

https://oeis.org/A171949 · https://oeis.org/A217319 · https://doi.org/10.1016/j.disc.2011.03.032
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a171949

def losing (n : ℕ) : Prop :=
  ∀ m : ℕ, (h : m < n) → (n ≤ m+3 ∨ m = n/4) → ¬ losing m
termination_by n

def trailing (n : ℕ) : Prop := 0 < n ∧ 2 ≤ n.factorization 2 % 4

theorem main : ∀ k : ℕ, Nat.nth losing (k+1) = Nat.nth trailing k := by
  sorry

end OMA.S_oeis_a171949
