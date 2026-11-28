import Mathlib

/-!
# Plouffe's proposed generating function for A005377

The terms are given independently by Niederreiter's formula for base 4,
as recorded by Sean A. Irvine. N(h) counts monic irreducibles of degree h
over the field of four elements, and M(r) is its cumulative sum.
The rank is the greatest r with M(r) ≤ n. Each positive degree has a
monic irreducible, so at most n increments are needed. The first term of
the OEIS list has index 1 and contributes the constant coefficient.

The proposed rational function is stated after clearing its denominator
(X−1)², which has constant coefficient one.
Source: https://oeis.org/A005377
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a005377

def irreducibles (h : ℕ) : ℕ :=
  ((∑ d ∈ h.divisors, ArithmeticFunction.moebius (h/d) * (4 : ℤ)^d) / (h : ℤ)).toNat

def cumulative (r : ℕ) : ℕ := ∑ i ∈ Finset.range r, irreducibles (i+1)

def findRank (n : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | fuel+1, r => if cumulative (r+1) ≤ n then findRank n fuel (r+1) else r

def a (n : ℕ) : ℕ :=
  let r := findRank n n 0
  r*(n-cumulative r) + ∑ i ∈ Finset.range r, i*irreducibles (i+1)

noncomputable def generating : PowerSeries ℤ :=
  PowerSeries.mk fun n => (a (n+1) : ℤ)

open PowerSeries in
theorem main :
    generating * (X-1)^2 = X^4 * (X^2+1) * (X^4-X^2+1) := by
  sorry

end OMA.S_oeis_a005377
