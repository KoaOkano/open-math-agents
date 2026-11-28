import Mathlib

/-!
# Column entries and row sums of the consecutive-partition triangle

Column k of A286013 begins with k in the triangular row 1+⋯+k. Its
subsequent nonzero entries are k+1,k+2,… at intervals of k rows.
A partition into k distinct consecutive parts is uniquely specified by
its smallest part t+1; its parts run from t+1 through t+k. A286015 sums
the largest parts of all such partitions of n. Both indices start at 1.

Peter Munn gave the trapezoidal correspondence in the A286013 entry in 2017.
Sources: https://oeis.org/A286013 and https://oeis.org/A286015
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a286013

def partTotal (t k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (t + (i+1))

def firstRow (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (i+1)

def entry (n k : ℕ) : ℕ :=
  if firstRow k ≤ n ∧ k ∣ n - firstRow k then k + (n-firstRow k)/k else 0

def largestParts (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, ∑ t ∈ Finset.range n,
    if partTotal t (j+1) = n then t+(j+1) else 0

theorem main :
    (∀ n k : ℕ, 0 < n → 0 < k → 0 < entry n k →
      ∃! t : ℕ, partTotal t k = n ∧ entry n k = t+k) ∧
    (∀ n : ℕ, 0 < n → (∑ j ∈ Finset.range n, entry n (j+1)) = largestParts n) := by
  sorry

end OMA.S_oeis_a286013
