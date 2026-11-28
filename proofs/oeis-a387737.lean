import OMAStatements.S_oeis_a387737
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Int.Interval

/-!
For a partition with r smaller parts, add the staircase 1-r, 3-r, ..., r-1
to those parts. Its sum is zero, and it converts weak order into gaps of two.
With at least two smaller parts the half-size condition leaves room for the
final gap. Two-part partitions account for the difference of one.
-/

namespace PartitionStaircase

open Finset OMA.S_oeis_a387737

private def step {r : ℕ} (i : Fin r) : ℤ := 2 * (i.val : ℤ) + 1 - r

private theorem sum_step (r : ℕ) : ∑ i : Fin r, step i = 0 := by
  have flip (i : Fin r) : step (Fin.revPerm i) = -step i := by
    change 2 * ((r - (i.val + 1) : ℕ) : ℤ) + 1 - r = -(2 * (i.val : ℤ) + 1 - r)
    have := i.isLt
    omega
  have h := Equiv.sum_comp (Fin.revPerm (n := r)) (fun i => step i)
  simp only [flip, sum_neg_distrib] at h
  omega

private def shift {r : ℕ} : (Fin r → ℤ) ≃ (Fin r → ℤ) where
  toFun f i := f i + step i
  invFun g i := g i - step i
  left_inv f := by funext i; simp
  right_inv g := by funext i; simp

private theorem shift_sum {r : ℕ} (f : Fin r → ℤ) : ∑ i, shift f i = ∑ i, f i := by
  change (∑ i, (f i + step i)) = _
  rw [sum_add_distrib, sum_step, add_zero]

private theorem shift_iff {n r : ℕ} (hr : 2 ≤ r) (f : Fin r → ℤ) :
    A n r f ↔ B n r (shift f) := by
  classical
  have large : largest n (shift f) = largest n f := by simp only [largest, shift_sum]
  unfold A B
  rw [large, shift_sum]
  change _ ↔ _ ∧ (∀ i, 2 ≤ f i + step i) ∧
    (∀ i j : Fin r, i ≤ j → f i + step i + 2 * (j.val : ℤ) ≤
      f j + step j + 2 * (i.val : ℤ)) ∧
    (∀ i, f i + step i + 2 ≤ largest n f) ∧ _
  constructor
  · rintro ⟨hlarge, hmin, hmono, hsum⟩
    refine ⟨by omega, ?_, ?_, ?_, hsum⟩
    · intro i
      have := hmin i
      unfold step
      omega
    · intro i j hij
      have := hmono hij
      unfold step
      omega
    · intro i
      let a : Fin r := ⟨0, by omega⟩
      let b : Fin r := ⟨1, by omega⟩
      obtain ⟨j, hji⟩ : ∃ j : Fin r, j ≠ i := by
        by_cases hi : a = i
        · refine ⟨b, ?_⟩
          rw [← hi]
          intro e
          have : (1 : ℕ) = 0 := congrArg Fin.val e
          omega
        · exact ⟨a, hi⟩
      have nonneg (k : Fin r) : 0 ≤ f k := by have := hmin k; omega
      have hj := single_le_sum (f := f) (fun k _ => nonneg k)
        (show j ∈ (univ : Finset (Fin r)).erase i from mem_erase.mpr ⟨hji, mem_univ _⟩)
      have decomp := add_sum_erase univ f (mem_univ i)
      have := hmin j
      have := i.isLt
      unfold step
      omega
  · rintro ⟨_, hmin, hgap, _, hsum⟩
    let a : Fin r := ⟨0, by omega⟩
    have first := hmin a
    have lower (i : Fin r) : (r : ℤ) + 1 ≤ f i := by
      have hi := hgap a i (by change 0 ≤ i.val; omega)
      change 2 ≤ f a + (2 * (0 : ℤ) + 1 - r) at first
      change f a + (2 * (0 : ℤ) + 1 - r) + 2 * (i.val : ℤ) ≤
        f i + (2 * (i.val : ℤ) + 1 - r) + 2 * 0 at hi
      omega
    have single := single_le_sum (f := f) (fun i _ => (show 0 ≤ f i by have := lower i; omega))
      (mem_univ a)
    refine ⟨by have := lower a; omega, lower, ?_, hsum⟩
    intro i j hij
    have := hgap i j hij
    unfold step at this
    omega

private theorem many {n r : ℕ} (hr : 2 ≤ r) : countA n r = countB n r := by
  apply Nat.card_congr
  exact shift.subtypeEquiv (shift_iff hr)

private theorem none {n : ℕ} (hn : 4 ≤ n) : countA n 0 = countB n 0 := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro f
  simp [A, B, largest, Monotone]
  omega

private def intervalEquiv (P : (Fin 1 → ℤ) → Prop) (u : ℤ)
    (h : ∀ f, P f ↔ f 0 ∈ Icc 2 u) : {f // P f} ≃ ↥(Icc 2 u) where
  toFun f := ⟨f.val 0, (h f.val).mp f.property⟩
  invFun x := ⟨fun _ => x.val, (h _).mpr x.property⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact congrArg f.val (Subsingleton.elim 0 i)
  right_inv _ := rfl

private theorem one {n : ℕ} (hn : 4 ≤ n) : countA n 1 = countB n 1 + 1 := by
  have ea := intervalEquiv (A n 1) ((n : ℤ) / 2) (by
    intro f
    simp [A, largest, Monotone, Fin.forall_fin_one]
    omega)
  have eb := intervalEquiv (B n 1) ((n : ℤ) / 2 - 1) (by
    intro f
    simp [B, largest, Fin.forall_fin_one]
    omega)
  unfold countA countB
  rw [Nat.card_congr ea, Nat.card_congr eb]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Int.card_Icc]
  omega

end PartitionStaircase

open Finset OMA.S_oeis_a387737 PartitionStaircase

theorem OMA.solution : type_of% @OMA.S_oeis_a387737.main := by
  intro n hn
  have pointwise (r : ℕ) : countA n r = countB n r + if r = 1 then 1 else 0 := by
    rcases r with _ | _ | r
    · simpa using none hn
    · simpa using one hn
    · simpa using many (n := n) (r := r + 2) (by omega)
  simp_rw [pointwise]
  rw [sum_add_distrib]
  simp [show 1 < n by omega]
