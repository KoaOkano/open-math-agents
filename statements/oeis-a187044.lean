import Mathlib

/-!
# Mathar's row-sum recurrence for A187044

A187044 is the sequence of row sums of A070895. That triangle starts at
row zero, has ones on its diagonal and zeros above it, and satisfies
T(n+1,k) = T(n,k) + n T(n-1,k) below its diagonal. The conjectured
third-order recurrence applies for n ≥ 3, when all four terms exist.
Sources: https://oeis.org/A187044 and https://oeis.org/A070895
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a187044

def entry : ℕ → ℕ → ℤ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | n + 2, k =>
    if k ≤ n + 1 then entry (n + 1) k + (n + 1 : ℕ) * entry n k
    else if k = n + 2 then 1 else 0

def rowSum (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), entry n k

theorem main : ∀ n : ℕ, 3 ≤ n →
    rowSum n - 2 * rowSum (n-1) + (2 - (n : ℤ)) * rowSum (n-2)
      + ((n : ℤ) - 2) * rowSum (n-3) = 0 := by
  sorry

end OMA.S_oeis_a187044
