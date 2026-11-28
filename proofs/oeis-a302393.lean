import OMAStatements.S_oeis_a302393

/-!
Adding two to every part maps the partitions of 3n to the partitions of
3(n+2) with smallest part at least three, preserving all three parities.
The two missing rows have smallest parts 1 and 2. Four steps later each of
these rows has six additional entries. In pairs of consecutive middle parts,
each of the middle and largest parts contributes exactly once.
-/

namespace PartitionParity

open Finset OMA.S_oeis_a302393

private def weight (n k i : ℕ) : ℕ :=
  (k + 1) % 2 + (i + 1) % 2 + (n+i+k + 1) % 2

private def length (n k : ℕ) : ℕ := (3*n-k)/2+1-k

private def row (n k : ℕ) : ℕ := ∑ i ∈ range (length n k), weight n k (k+i)

private theorem interval (f : ℕ → ℕ) (k m : ℕ) :
    ∑ i ∈ Icc k m, f i = ∑ j ∈ range (m+1-k), f (k+j) := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]

private theorem count (n : ℕ) : a n = ∑ j ∈ range n, row n (j+1) := by
  unfold a
  rw [interval, show n+1-1=n by omega]
  apply sum_congr rfl
  intro j hj
  rw [Nat.add_comm 1 j, interval]
  unfold row length
  apply sum_congr rfl
  intro i hi
  simp only [mem_range] at hj hi
  unfold weight
  omega

private theorem translate (n k : ℕ) (hk : k ≤ n) : row (n+2) (k+2) = row n k := by
  have e : length (n+2) (k+2) = length n k := by unfold length; omega
  unfold row
  rw [e]
  apply sum_congr rfl
  intro i _
  unfold weight
  omega

private theorem boundary (n : ℕ) :
    a (n+2) = a n + row (n+2) 2 + row (n+2) 1 := by
  rw [count (n+2), count n, sum_range_succ', sum_range_succ']
  have h : (∑ i ∈ range n, row (n+2) (i+1+1+1)) = ∑ i ∈ range n, row n (i+1) := by
    apply sum_congr rfl
    intro i hi
    exact translate n (i+1) (mem_range.mp hi)
  rw [h]

private theorem pair (n k i : ℕ) :
    weight n k i + weight n k (i+1) = 2 * ((k + 1) % 2) + 2 := by
  unfold weight
  omega

private theorem six (n k i : ℕ) :
    ∑ j ∈ range 6, weight n k (i+j) = 6 * ((k + 1) % 2) + 6 := by
  have h₀ := pair n k i
  have h₂ := pair n k (i+2)
  have h₄ := pair n k (i+4)
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.add_zero]
  change weight n k i + weight n k (i+1) + weight n k (i+2) +
    weight n k (i+3) + weight n k (i+4) + weight n k (i+5) = _
  change weight n k (i+2) + weight n k (i+3) = _ at h₂
  change weight n k (i+4) + weight n k (i+5) = _ at h₄
  omega

private theorem grow (n k : ℕ) (hk : k ≤ n) :
    row (n+4) k = row n k + (6*((k + 1)%2)+6) := by
  have len : length (n+4) k = length n k + 6 := by unfold length; omega
  have same (i : ℕ) : weight (n+4) k i = weight n k i := by unfold weight; omega
  unfold row
  rw [len, sum_range_add]
  simp only [same]
  congr 1
  simpa only [Nat.add_assoc] using six n k (k+length n k)

private theorem balance (n : ℕ) : a (n+6) + a n = a (n+4) + a (n+2) + 18 := by
  have b₀ := boundary n
  have b₄ := boundary (n+4)
  change a (n+6) = a (n+4) + row (n+6) 2 + row (n+6) 1 at b₄
  have g₁ := grow (n+2) 1 (by omega)
  have g₂ := grow (n+2) 2 (by omega)
  change row (n+6) 1 = row (n+2) 1 + 6 at g₁
  change row (n+6) 2 = row (n+2) 2 + 12 at g₂
  omega

end PartitionParity

open PartitionParity OMA.S_oeis_a302393

theorem OMA.solution : type_of% @OMA.S_oeis_a302393.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k+7 := ⟨n-7, by omega⟩
  have h₀ := balance k
  have h₁ := balance (k+1)
  change a (k+7) + a (k+1) = a (k+5) + a (k+3) + 18 at h₁
  change (a (k+7) : ℤ) = a (k+6) + a (k+5) - a (k+4) + a (k+3) - a (k+2) - a (k+1) + a k
  omega
