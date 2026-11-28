import Mathlib

/-!
# Antidiagonal sums of A126885 and partial sums of A104879

A126885 has T(q,1)=1 and T(q,k+1)=q T(q,k)+k+1. Appending the
zero column T(q,0)=0 gives the same recurrence from column zero.
A134195(n) is the sum over q=0,...,n of T(q,n+1−q).

A104879(n) is the sum of row n of A104878. Its entry in column q
is 1+q+...+q^(n-q), including the initial 1 for q=0. Both row-sum
sequences start at zero. Sean A. Irvine conjectured their partial-sum
relation in July 2022.
Sources: https://oeis.org/A134195, https://oeis.org/A126885,
https://oeis.org/A104879, https://oeis.org/A104878
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a134195
open Finset

def arrayEntry (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => q * arrayEntry q k + (k+1)

def antidiagonalSum (n : ℕ) : ℕ := ∑ q ∈ range (n+1), arrayEntry q (n+1-q)

def geometric (q k : ℕ) : ℕ := ∑ j ∈ range k, q^j

def row (n : ℕ) : ℕ := ∑ q ∈ range (n+1), geometric q (n+1-q)

theorem main : ∀ n : ℕ, antidiagonalSum n = ∑ k ∈ range (n+1), row k := by
  sorry

end OMA.S_oeis_a134195
