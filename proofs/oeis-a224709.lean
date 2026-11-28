import OMAStatements.S_oeis_a224709

/-!
Anthony Browne's strict inequality fails at n = 13344. The even integers
80080 and 80082 each have 33203 unordered partitions into two composite
numbers. Pedro Caceres reported the related prime-partition counts in
section 9 of his 2026 paper (https://hexagonmath.org/pdf/2611.00350v1).
Here the kernel counts composite pairs directly from their definition.
-/

namespace CompositePartitions

open Finset OMA.S_oeis_a224709

private def trials : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
    137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283]

private def composite (x : ℕ) : Bool :=
  trials.any fun p => decide (p < x) && (x % p == 0)

private theorem trials_cover : ∀ p : Fin 284, p.val.Prime → p.val ∈ trials := by
  decide +kernel

private theorem trials_ge_two : ∀ p ∈ trials, 2 ≤ p := by decide

private theorem composite_iff {x : ℕ} (hx : x ≤ 80082) :
    composite x = true ↔ IsComposite x := by
  simp only [composite, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨p, hp, hlt, hmod⟩
    have hmin := trials_ge_two p hp
    refine ⟨by omega, fun prime => ?_⟩
    have := prime.eq_one_or_self_of_dvd p (Nat.dvd_of_mod_eq_zero hmod)
    omega
  · rintro ⟨hpos, hnot⟩
    have hp := Nat.minFac_prime (by omega : x ≠ 1)
    have hs := Nat.minFac_sq_le_self (by omega : 0 < x) hnot
    have hsmall : x.minFac < 284 := by
      by_contra! h
      have : (284 : ℕ)^2 ≤ x.minFac^2 := Nat.pow_le_pow_left h 2
      omega
    have hlt : x.minFac < x := by
      have hl := Nat.minFac_le (by omega : 0 < x)
      have hne : x.minFac ≠ x := fun e => hnot (e ▸ hp)
      omega
    exact ⟨x.minFac, trials_cover ⟨_, hsmall⟩ hp, hlt, Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd x)⟩

private def weight (n x : ℕ) : ℕ :=
  if x ≤ n ∧ composite x = true ∧ composite (2*n-x) = true then 1 else 0

/-- Count an interval of length 2^h by bisecting it. -/
private def block (n : ℕ) (s h : ℕ) : ℕ :=
  match h with
  | 0 => weight n s
  | e+1 => block n s e + block n (s+2^e) e

private theorem block_sum (n s h : ℕ) :
    block n s h = ∑ j ∈ range (2^h), weight n (s+j) := by
  induction h generalizing s with
  | zero => simp [block]
  | succ h ih =>
    rw [block, ih, ih, pow_succ, Nat.mul_two, sum_range_add]
    simp only [Nat.add_assoc]

private theorem counts {n h : ℕ} (hn : n < 2^h) (hb : n ≤ 40041) : a n = block n 0 h := by
  rw [block_sum]
  simp only [Nat.zero_add, weight, sum_boole]
  unfold a
  apply congrArg Finset.card
  apply Finset.ext
  intro j
  simp only [mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨_, hj⟩, h₁, h₂⟩
    exact ⟨lt_of_le_of_lt hj hn, hj, (composite_iff (by omega)).2 h₁,
      (composite_iff (by omega)).2 h₂⟩
  · rintro ⟨_, hj, h₁, h₂⟩
    have hcomp := (composite_iff (x := j) (by omega)).1 h₁
    exact ⟨⟨le_of_lt hcomp.1, hj⟩, hcomp, (composite_iff (by omega)).1 h₂⟩

set_option maxHeartbeats 16000000 in
private theorem tied : block 40040 0 16 = 33203 ∧ block 40041 0 16 = 33203 := by
  decide +kernel

end CompositePartitions

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a224709.main) := by
  intro h
  have hc := (h 13344 (by decide)).1
  change OMA.S_oeis_a224709.a 40040 < OMA.S_oeis_a224709.a 40041 at hc
  rw [CompositePartitions.counts (n := 40040) (h := 16) (by decide) (by decide),
      CompositePartitions.counts (n := 40041) (h := 16) (by decide) (by decide)] at hc
  have ⟨h₀, h₁⟩ := CompositePartitions.tied
  omega
