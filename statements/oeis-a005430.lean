import Mathlib

/-!
# Mathar's inverse binomial transform of n times the central binomial coefficient

A132894 counts marked horizontal steps among all nonnegative Motzkin
prefixes of length n. Deleting the marked step leaves a prefix of length
n-1 and one of n insertion positions (Alois P. Heinz, 2013). If the
remaining prefix has j non-horizontal steps, its j positions can be
chosen arbitrarily. By the ballot/reflection formula the number of
nonnegative up/down prefixes of length j is choose(j,floor(j/2)).
This gives the unsigned sum below, independently of the signed transform.

https://oeis.org/A005430 · https://oeis.org/A132894 · https://oeis.org/A005773
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a005430

def apery (n : ℕ) : ℕ := n * (2*n).choose n

def marked (n : ℕ) : ℕ :=
  n * ∑ j ∈ Finset.range n, (n-1).choose j * j.choose (j/2)

theorem main : ∀ n : ℕ,
    (∑ k ∈ Finset.range (n+1), (-1 : ℤ)^(n-k) * n.choose k * apery k) = 2 * (marked n : ℤ) := by
  sorry

end OMA.S_oeis_a005430
