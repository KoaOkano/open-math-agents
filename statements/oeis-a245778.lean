import Mathlib

/-!
# Are all terms of A245778 record holders in A216793?

Membership in A245778 means that n/τ(n) − σ(n)/n is an integer, with
rational division. A216793 consists of the strict successive records
of gcd(n,σ(n)). Both sequences list positive integers in increasing
order, so the proposed subsequence relation is exactly set inclusion.
Sources: https://oeis.org/A245778 and https://oeis.org/A216793
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a245778

def divisorSum (n : ℕ) := ∑ d ∈ n.divisors, d

def isTerm (n : ℕ) : Prop :=
  ∃ z : ℤ, (n : ℚ) / n.divisors.card - (divisorSum n : ℚ) / n = z

def isRecord (n : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → m < n → m.gcd (divisorSum m) < n.gcd (divisorSum n)

theorem main : ∀ n : ℕ, 0 < n → isTerm n → isRecord n := by
  sorry

end OMA.S_oeis_a245778
