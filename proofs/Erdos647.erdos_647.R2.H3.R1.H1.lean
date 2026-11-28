import OMAReductions.R_Erdos647_erdos_647_R2_H3_R1
import Mathlib

/-!
# Divisor obstructions for the original Erdős–Selfridge inequality

If d divides m and d² < m, then every divisor of d and its multiple
by m/d give two disjoint sets of divisors of m. At the shift n mod d
this gives a cheap obstruction to the exact problem statement. The
resulting small-modulus tests force 360360 to divide any sufficiently
large solution.

Formalization and computational certificates by @KoaOkano. Related modular
reductions for this problem were previously studied by Mian and Siddique
(arXiv:2608.17880) and by Scott Hughes in erdos647-proof-chain.
-/

open Finset ArithmeticFunction.sigma

namespace OMA.Erdos647Obstructions

/-- Every preceding integer satisfies the original Erdős–Selfridge inequality. -/
private def Good (n : ℕ) : Prop := ∀ m < n, m + σ 0 m ≤ n+2

theorem doubleDivisors {d u : ℕ} (positive : 0 < d) (sep : d < u) :
    2 * (σ 0 d) ≤ σ 0 (d*u) := by
  rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
  let D := d.divisors
  let E := D.image (fun i => u*i)
  have pu : 0 < u := by omega
  have nonzero : d*u ≠ 0 := (Nat.mul_pos positive pu).ne'
  have small {i : ℕ} (hi : i ∈ D) : i ≤ d := Nat.le_of_dvd positive (Nat.dvd_of_mem_divisors hi)
  have disj : Disjoint D E := by
    apply Finset.disjoint_left.mpr
    intro i hi he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    have posv := Nat.pos_of_mem_divisors hv
    have hu : u ≤ u*v := by simpa using Nat.mul_le_mul_left u (show 1 ≤ v by omega)
    have hs := small hi
    omega
  have inside : D ∪ E ⊆ (d*u).divisors := by
    intro i hi
    refine Nat.mem_divisors.mpr ⟨?_, nonzero⟩
    rcases Finset.mem_union.mp hi with h | h
    · exact (Nat.dvd_of_mem_divisors h).trans (dvd_mul_right d u)
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
      simpa only [mul_comm d u] using Nat.mul_dvd_mul_left u (Nat.dvd_of_mem_divisors hv)
  have same : E.card = D.card := Finset.card_image_of_injective D (fun _ _ h =>
    Nat.eq_of_mul_eq_mul_left pu h)
  have h := Finset.card_le_card inside
  rw [Finset.card_union_of_disjoint disj, same] at h
  simpa [D, two_mul] using h

private theorem residueBound {n d : ℕ} (good : Good n) (hd : 0 < d)
    (large : d*d+d ≤ n) (hr : 0 < n%d) : 2 * σ 0 d ≤ n%d + 2 := by
  let u := n/d
  have decomp : n%d + d*u = n := Nat.mod_add_div n d
  have less := Nat.mod_lt n hd
  have sep : d < u := by
    by_contra! h
    have bound := Nat.mul_le_mul_left d h
    omega
  have before : d*u < n := by omega
  have h := good (d*u) before
  have count := doubleDivisors hd sep
  omega

private theorem forceStep {n M p bound : ℕ} (good : Good n) (large : bound ≤ n)
    (start : M ∣ n) (hp : 0 < p)
    (certificate : ∀ i : Fin p, i.val ≠ 0 → ∃ d : ℕ,
      0 < d ∧ d*d+d ≤ bound ∧ d ∣ M*p ∧ 0 < (M*i.val)%d ∧
      (M*i.val)%d+2 < 2*(σ 0 d)) : M*p ∣ n := by
  obtain ⟨q,hq⟩ := start
  by_cases div : p ∣ q
  · exact hq ▸ Nat.mul_dvd_mul_left M div
  let i : Fin p := ⟨q%p, Nat.mod_lt _ hp⟩
  have hi : i.val ≠ 0 := fun h => div (Nat.dvd_of_mod_eq_zero h)
  obtain ⟨d, dpos, dlim, dm, pos, obstruction⟩ := certificate i hi
  have congr : M*i.val ≡ n [MOD d] := by
    rw [hq]
    exact ((Nat.mod_modEq q p).mul_left' M).of_dvd dm
  change (M*i.val)%d = n%d at congr
  rw [congr] at pos obstruction
  exact False.elim ((Nat.not_lt_of_ge (residueBound good dpos (dlim.trans large) pos)) obstruction)

private theorem force24 {n : ℕ} (good : ∀ m < n, m + σ 0 m ≤ n+2)
    (large : 72 ≤ n) : 24 ∣ n := by
  have step1 : 1 ∣ n := one_dvd _
  have step2 : 2 ∣ n := by
    apply forceStep (M := 1) (p := 2) good large step1 (by decide)
    intro i nonzero
    fin_cases i
    · exact (nonzero rfl).elim
    · exact ⟨2, by decide⟩
  have step4 : 4 ∣ n := by
    apply forceStep (M := 2) (p := 2) good large step2 (by decide)
    intro i nonzero
    fin_cases i
    · exact (nonzero rfl).elim
    · exact ⟨4, by decide⟩
  have step8 : 8 ∣ n := by
    apply forceStep (M := 4) (p := 2) good large step4 (by decide)
    intro i nonzero
    fin_cases i
    · exact (nonzero rfl).elim
    · exact ⟨8, by decide⟩
  have step24 : 24 ∣ n := by
    apply forceStep (M := 8) (p := 3) good large step8 (by decide)
    intro i nonzero
    fin_cases i
    · exact (nonzero rfl).elim
    · exact ⟨6, by decide⟩
    · exact ⟨3, by decide⟩
  exact step24

private theorem force2520 {n : ℕ} (good : ∀ m < n, m + σ 0 m ≤ n+2)
    (large : 1806 ≤ n) : 2520 ∣ n := by
  have step24 : 24 ∣ n := force24 good (by omega)
  have step72 : 72 ∣ n := by
    apply forceStep (M := 24) (p := 3) good large step24 (by decide)
    intro i nonzero
    fin_cases i
    · exact (nonzero rfl).elim
    · exact ⟨18, by decide⟩
    · exact ⟨9, by decide⟩
  have step360 : 360 ∣ n := by
    apply forceStep (M := 72) (p := 5) good large step72 (by decide)
    intro i nonzero
    fin_cases i
    · exact (nonzero rfl).elim
    · exact ⟨10, by decide⟩
    · exact ⟨10, by decide⟩
    · exact ⟨5, by decide⟩
    · exact ⟨15, by decide⟩
  have step2520 : 2520 ∣ n := by
    apply forceStep (M := 360) (p := 7) good large step360 (by decide)
    intro i nonzero
    fin_cases i
    · exact (nonzero rfl).elim
    · exact ⟨21, by decide⟩
    · exact ⟨42, by decide⟩
    · exact ⟨14, by decide⟩
    · exact ⟨35, by decide⟩
    · exact ⟨7, by decide⟩
    · exact ⟨14, by decide⟩
  exact step2520

theorem necessaryDivisibility {n : ℕ} (good : ∀ m < n, m + σ 0 m ≤ n+2)
    (large : 97656 ≤ n) : 360360 ∣ n := by
  have step2520 : 2520 ∣ n := force2520 good (by omega)
  have step27720 : 27720 ∣ n := by
    apply forceStep (M := 2520) (p := 11) good large step2520 (by decide)
    intro i nonzero
    fin_cases i
    · exact (nonzero rfl).elim
    · exact ⟨11, by decide⟩
    · exact ⟨22, by decide⟩
    · exact ⟨33, by decide⟩
    · exact ⟨22, by decide⟩
    · exact ⟨55, by decide⟩
    · exact ⟨66, by decide⟩
    · exact ⟨198, by decide⟩
    · exact ⟨44, by decide⟩
    · exact ⟨99, by decide⟩
    · exact ⟨110, by decide⟩
  have step360360 : 360360 ∣ n := by
    apply forceStep (M := 27720) (p := 13) good large step27720 (by decide)
    intro i nonzero
    fin_cases i
    · exact (nonzero rfl).elim
    · exact ⟨26, by decide⟩
    · exact ⟨52, by decide⟩
    · exact ⟨78, by decide⟩
    · exact ⟨39, by decide⟩
    · exact ⟨260, by decide⟩
    · exact ⟨312, by decide⟩
    · exact ⟨26, by decide⟩
    · exact ⟨78, by decide⟩
    · exact ⟨130, by decide⟩
    · exact ⟨13, by decide⟩
    · exact ⟨65, by decide⟩
    · exact ⟨117, by decide⟩
  exact step360360

private theorem smallCounterexample {n : ℕ} (good : Good n)
    (lo : 24 < n) (hi : n < 97656) : False := by
  have hit (k : ℕ) (values : List ℕ) (hk : 0 < k ∧ k < n)
      (cover : values.all (fun d => (n-k)%d == 0) = true)
      (distinct : values.Nodup) (size : k+3 ≤ values.length) : False := by
    have incl : values.toFinset ⊆ (n-k).divisors := by
      intro d hd
      have val := List.all_eq_true.mp cover d (List.mem_toFinset.mp hd)
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp val), by omega⟩
    have card := Finset.card_le_card incl
    rw [List.toFinset_card_of_nodup distinct, ← ArithmeticFunction.sigma_zero_apply] at card
    have h := good (n-k) (by omega)
    omega
  by_cases upper : n < 72
  · interval_cases n
    · exact hit 1 [1,2,3,4] (by decide) (by decide) (by decide) (by decide)
    · exact hit 2 [1,2,3,4,6] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,13,26] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,3,9,27] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,4,7] (by decide) (by decide) (by decide) (by decide)
    · exact hit 2 [1,2,4,7,14] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,3,5] (by decide) (by decide) (by decide) (by decide)
    · exact hit 2 [1,2,3,5,6] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,4,8] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,3,11,33] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,17,34] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,5,7,35] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,3,4] (by decide) (by decide) (by decide) (by decide)
    · exact hit 2 [1,2,3,4,6] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,19,38] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,3,13,39] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,4,5] (by decide) (by decide) (by decide) (by decide)
    · exact hit 2 [1,2,4,5,8] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,3,6] (by decide) (by decide) (by decide) (by decide)
    · exact hit 2 [1,2,3,6,7] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,4,11] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,3,5,9] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,23,46] (by decide) (by decide) (by decide) (by decide)
    · exact hit 3 [1,3,5,9,15,45] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,3,4] (by decide) (by decide) (by decide) (by decide)
    · exact hit 2 [1,2,3,4,6] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,5,10] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,3,17,51] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,4,13] (by decide) (by decide) (by decide) (by decide)
    · exact hit 2 [1,2,4,13,26] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,3,6] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,5,11,55] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,4,7] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,3,19,57] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,29,58] (by decide) (by decide) (by decide) (by decide)
    · exact hit 4 [1,2,4,7,8,14,28] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,3,4] (by decide) (by decide) (by decide) (by decide)
    · exact hit 2 [1,2,3,4,5] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,31,62] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,3,7,9] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,4,8] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,5,13,65] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,3,6] (by decide) (by decide) (by decide) (by decide)
    · exact hit 2 [1,2,3,6,11] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,4,17] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,3,23,69] (by decide) (by decide) (by decide) (by decide)
    · exact hit 1 [1,2,5,7] (by decide) (by decide) (by decide) (by decide)
  · by_cases mid : n < 1806
    · obtain ⟨q, rfl⟩ := force24 good (by omega)
      have qlo : 3 ≤ q := by omega
      have qhi : q ≤ 75 := by omega
      interval_cases q
      · exact hit 2 [1,2,5,7,10] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,19,95] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,7,17,119] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,11,13,143] (by decide) (by decide) (by decide) (by decide)
      · exact hit 3 [1,3,5,11,15,33] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,5,10,19] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,43,215] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,7,14,17] (by decide) (by decide) (by decide) (by decide)
      · exact hit 3 [1,3,9,29,87,261] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,7,41,287] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,5,10,31] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,67,335] (by decide) (by decide) (by decide) (by decide)
      · exact hit 3 [1,3,7,17,21,51] (by decide) (by decide) (by decide) (by decide)
      · exact hit 4 [1,2,4,5,10,19,20] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,11,37,407] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,5,10,43] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,7,13] (by decide) (by decide) (by decide) (by decide)
      · exact hit 3 [1,3,9,53,159,477] (by decide) (by decide) (by decide) (by decide)
      · exact hit 4 [1,2,4,5,10,20,25] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,17,31,527] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,19,29,551] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,23,25] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,13,23,26] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,7,89,623] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,17,19,34] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,11,61,671] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,139,695] (by decide) (by decide) (by decide) (by decide)
      · exact hit 5 [1,5,11,13,55,65,143,715] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,7,14,53] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,13,59,767] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,7,113,791] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,163,815] (by decide) (by decide) (by decide) (by decide)
      · exact hit 3 [1,3,9,27,31,93] (by decide) (by decide) (by decide) (by decide)
      · exact hit 3 [1,3,7,21,41,123] (by decide) (by decide) (by decide) (by decide)
      · exact hit 3 [1,3,5,15,59,177] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,5,7,10] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,11,17] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,7,137,959] (by decide) (by decide) (by decide) (by decide)
      · exact hit 3 [1,3,9,109,327,981] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,19,53,1007] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,5,10,103] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,211,1055] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,13,83,1079] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,19,29,38] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,7,23,49] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,5,10,23] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,25,47] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,11,109,1199] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,13,26,47] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,29,43,1247] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,31,41,1271] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,7,35] (by decide) (by decide) (by decide) (by decide)
      · exact hit 4 [1,2,4,7,14,28,47] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,17,79,1343] (by decide) (by decide) (by decide) (by decide)
      · exact hit 3 [1,3,5,7,13,15] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,13,107,1391] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,283,1415] (by decide) (by decide) (by decide) (by decide)
      · exact hit 5 [1,5,7,35,41,205,287,1435] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,7,11,19] (by decide) (by decide) (by decide) (by decide)
      · exact hit 3 [1,3,5,9,11,15] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,5,10,151] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,307,1535] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,19,38,41] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,7,14,113] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,11,22,73] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,7,233,1631] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,331,1655] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,23,73,1679] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,13,131,1703] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,11,157,1727] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,17,103,1751] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,5,25,71] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,7,257,1799] (by decide) (by decide) (by decide) (by decide)
    · obtain ⟨q, rfl⟩ := force2520 good (by omega)
      have qlo : 1 ≤ q := by omega
      have qhi : q ≤ 38 := by omega
      interval_cases q
      · exact hit 1 [1,11,229,2519] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,11,22,229] (by decide) (by decide) (by decide) (by decide)
      · exact hit 3 [1,3,11,33,229,687] (by decide) (by decide) (by decide) (by decide)
      · exact hit 4 [1,2,4,11,22,44,229] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,43,293,12599] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,13,1163,15119] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,31,569,17639] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,19,1061,20159] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,17,23,29] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,113,223,25199] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,53,523,27719] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,11,2749,30239] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,17,41,47] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,31,62,569] (by decide) (by decide) (by decide) (by decide)
      · exact hit 3 [1,3,43,129,293,879] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,23,1753,40319] (by decide) (by decide) (by decide) (by decide)
      · exact hit 3 [1,3,109,131,327,393] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,67,677,45359] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,13,29,127] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,101,499,50399] (by decide) (by decide) (by decide) (by decide)
      · exact hit 3 [1,3,31,93,569,1707] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,53,106,523] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,11,121,479] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,197,307,60479] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,73,863,62999] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,17,34,41] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,19,3581,68039] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,37,1907,70559] (by decide) (by decide) (by decide) (by decide)
      · exact hit 2 [1,2,61,122,599] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,17,4447,75599] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,191,409,78119] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,13,6203,80639] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,137,607,83159] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,11,7789,85679] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,89,991,88199] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,83,1093,90719] (by decide) (by decide) (by decide) (by decide)
      · exact hit 4 [1,2,4,11,13,22,26] (by decide) (by decide) (by decide) (by decide)
      · exact hit 1 [1,31,3089,95759] (by decide) (by decide) (by decide) (by decide)

private theorem primeOfSmallCount {q : ℕ} (large : 2 ≤ q) (bound : σ 0 q ≤ 2) :
    q.Prime := by
  apply Nat.prime_def_lt.mpr ⟨large, ?_⟩
  intro d hd hdiv
  by_contra different
  have qpos : 0 < q := by omega
  have dup : d ≠ q := hd.ne
  have qne : 1 ≠ q := by omega
  have subset : ({1,d,q} : Finset ℕ) ⊆ q.divisors := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Nat.one_mem_divisors.mpr qpos.ne'
    · exact Nat.mem_divisors.mpr ⟨hdiv, qpos.ne'⟩
    · exact Nat.mem_divisors_self _ qpos.ne'
  have count := Finset.card_le_card subset
  rw [← ArithmeticFunction.sigma_zero_apply] at count
  have diff : 1 ≠ d := Ne.symm different
  simp [diff, qne, dup] at count
  omega

private theorem minusOnePrime {n : ℕ} (good : Good n) (large : 97656 ≤ n) :
    (n-1).Prime := by
  obtain ⟨a,ha⟩ := necessaryDivisibility good large
  let q := n-1
  let p := q.minFac
  have qpos : 0 < q := by dsimp [q]; omega
  have primeP : p.Prime := Nat.minFac_prime (by dsimp [q]; omega)
  by_contra fail
  have bound : p^2 ≤ q := Nat.minFac_sq_le_self qpos fail
  have residue : p^2 % 4 = 0 ∨ p^2 % 4 = 1 := by
    have eq : p^2 % 4 = (p%4)^2 % 4 := (Nat.pow_mod _ _ _)
    rw [eq]
    have lt := Nat.mod_lt p (by decide : 0 < 4)
    interval_cases p%4 <;> decide
  have neus : p^2 ≠ q := by
    dsimp [q]
    omega
  obtain ⟨u,hu⟩ := Nat.minFac_dvd q
  change q = p*u at hu
  have sep : p < u := by
    by_contra! no
    have hle := Nat.mul_le_mul_left p no
    rw [sq] at bound neus
    omega
  have ct := doubleDivisors primeP.pos sep
  have two : σ 0 p = 2 := by
    simpa using (ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) primeP)
  rw [two, ← hu] at ct
  have forbid := good q (by dsimp [q]; omega)
  dsimp [q] at forbid ct
  omega

/-- Six explicit linear forms must be prime at every large genuine solution. -/
theorem sixPrimes {n : ℕ} (good : ∀ m < n, m + σ 0 m ≤ n+2) (large : 97656 ≤ n) :
    ∀ k ∈ ({1,2,3,4,6,12} : Finset ℕ), (n/k-1).Prime := by
  intro k hk
  rcases eq_or_ne k 1 with rfl | h1
  · simpa using minusOnePrime good large
  obtain ⟨t,ht⟩ := necessaryDivisibility good large
  have facts : k ∣ 360360 ∧ k ∣ (360360/k)^2 ∧ k+2 < 3*σ 0 k ∧ k ≤ 12 ∧ 0 < k := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
    · exact (h1 rfl).elim
    all_goals decide
  obtain ⟨div, radical, budget, small, pk⟩ := facts
  let c := 360360/k
  have restore : k*c = 360360 := Nat.mul_div_cancel' div
  have loc : n = k*(c*t) := by rw [ht, ← restore, mul_assoc]
  have quo : n/k = c*t := by rw [loc, Nat.mul_div_cancel_left _ pk]
  let q := c*t-1
  have long : 3 ≤ c*t := by
    by_contra! low
    have h := Nat.mul_le_mul small (show c*t ≤ 2 by omega)
    omega
  have succ : q+1 = c*t := by dsimp [q]; omega
  have cop : c.Coprime q := by
    let g := Nat.gcd c q
    have one : g ∣ c*t-q :=
      Nat.dvd_sub ((Nat.gcd_dvd_left c q).trans (dvd_mul_right c t)) (Nat.gcd_dvd_right c q)
    have eq : c*t-q = 1 := by omega
    rw [eq] at one
    exact Nat.dvd_one.mp one
  have copK : k.Coprime q := (cop.pow_left 2).coprime_dvd_left radical
  have before : n = k*q+k := by rw [loc, ← succ, Nat.mul_succ]
  have h := good (k*q) (by omega)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime copK] at h
  have bound : σ 0 q ≤ 2 := by
    by_contra! no
    have breach := Nat.mul_le_mul_left (σ 0 k) (show 3 ≤ σ 0 q by omega)
    omega
  rw [quo]
  exact primeOfSmallCount (q := q) (by dsimp [q]; omega) bound


private structure Rule where
  modulus : ℕ
  radius : ℕ
  valid : 0 < modulus ∧ radius+2 < 2*σ 0 modulus

private theorem checkRule (d r : ℕ) (values : List ℕ) (hd : 0 < d)
    (valid : values.all (fun a => d%a == 0) = true) (distinct : values.Nodup)
    (h : r+2 < 2*values.length) : 0 < d ∧ r+2 < 2*(σ 0 d) := by
  have incl : values.toFinset ⊆ d.divisors := by
    intro a ha
    have val := List.all_eq_true.mp valid a (List.mem_toFinset.mp ha)
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp val), hd.ne'⟩
  have card := Finset.card_le_card incl
  rw [List.toFinset_card_of_nodup distinct, ← ArithmeticFunction.sigma_zero_apply] at card
  exact ⟨hd, by omega⟩

private theorem valid_32 : 0 < 32 ∧ 9+2 < 2*σ 0 32 :=
  checkRule 32 9 [1,2,4,8,16,32]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_34 : 0 < 34 ∧ 5+2 < 2*σ 0 34 :=
  checkRule 34 5 [1,2,17,34]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_68 : 0 < 68 ∧ 9+2 < 2*σ 0 68 :=
  checkRule 68 9 [1,2,4,17,34,68]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_38 : 0 < 38 ∧ 5+2 < 2*σ 0 38 :=
  checkRule 38 5 [1,2,19,38]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_192 : 0 < 192 ∧ 25+2 < 2*σ 0 192 :=
  checkRule 192 25 [1,2,3,4,6,8,12,16,24,32,48,64,96,192]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_102 : 0 < 102 ∧ 13+2 < 2*σ 0 102 :=
  checkRule 102 13 [1,2,3,6,17,34,51,102]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_76 : 0 < 76 ∧ 9+2 < 2*σ 0 76 :=
  checkRule 76 9 [1,2,4,19,38,76]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_114 : 0 < 114 ∧ 13+2 < 2*σ 0 114 :=
  checkRule 114 13 [1,2,3,6,19,38,57,114]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_46 : 0 < 46 ∧ 5+2 < 2*σ 0 46 :=
  checkRule 46 5 [1,2,23,46]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_51 : 0 < 51 ∧ 5+2 < 2*σ 0 51 :=
  checkRule 51 5 [1,3,17,51]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_92 : 0 < 92 ∧ 9+2 < 2*σ 0 92 :=
  checkRule 92 9 [1,2,4,23,46,92]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_138 : 0 < 138 ∧ 13+2 < 2*σ 0 138 :=
  checkRule 138 13 [1,2,3,6,23,46,69,138]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_57 : 0 < 57 ∧ 5+2 < 2*σ 0 57 :=
  checkRule 57 5 [1,3,19,57]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_58 : 0 < 58 ∧ 5+2 < 2*σ 0 58 :=
  checkRule 58 5 [1,2,29,58]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_62 : 0 < 62 ∧ 5+2 < 2*σ 0 62 :=
  checkRule 62 5 [1,2,31,62]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_116 : 0 < 116 ∧ 9+2 < 2*σ 0 116 :=
  checkRule 116 9 [1,2,4,29,58,116]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_170 : 0 < 170 ∧ 13+2 < 2*σ 0 170 :=
  checkRule 170 13 [1,2,5,10,17,34,85,170]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_174 : 0 < 174 ∧ 13+2 < 2*σ 0 174 :=
  checkRule 174 13 [1,2,3,6,29,58,87,174]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_124 : 0 < 124 ∧ 9+2 < 2*σ 0 124 :=
  checkRule 124 9 [1,2,4,31,62,124]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_69 : 0 < 69 ∧ 5+2 < 2*σ 0 69 :=
  checkRule 69 5 [1,3,23,69]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_408 : 0 < 408 ∧ 29+2 < 2*σ 0 408 :=
  checkRule 408 29 [1,2,3,4,6,8,12,17,24,34,51,68,102,136,204,408]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_186 : 0 < 186 ∧ 13+2 < 2*σ 0 186 :=
  checkRule 186 13 [1,2,3,6,31,62,93,186]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_306 : 0 < 306 ∧ 21+2 < 2*σ 0 306 :=
  checkRule 306 21 [1,2,3,6,9,17,18,34,51,102,153,306]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_190 : 0 < 190 ∧ 13+2 < 2*σ 0 190 :=
  checkRule 190 13 [1,2,5,10,19,38,95,190]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_74 : 0 < 74 ∧ 5+2 < 2*σ 0 74 :=
  checkRule 74 5 [1,2,37,74]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_456 : 0 < 456 ∧ 29+2 < 2*σ 0 456 :=
  checkRule 456 29 [1,2,3,4,6,8,12,19,24,38,57,76,114,152,228,456]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_272 : 0 < 272 ∧ 17+2 < 2*σ 0 272 :=
  checkRule 272 17 [1,2,4,8,16,17,34,68,136,272]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_342 : 0 < 342 ∧ 21+2 < 2*σ 0 342 :=
  checkRule 342 21 [1,2,3,6,9,18,19,38,57,114,171,342]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_82 : 0 < 82 ∧ 5+2 < 2*σ 0 82 :=
  checkRule 82 5 [1,2,41,82]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_148 : 0 < 148 ∧ 9+2 < 2*σ 0 148 :=
  checkRule 148 9 [1,2,4,37,74,148]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_85 : 0 < 85 ∧ 5+2 < 2*σ 0 85 :=
  checkRule 85 5 [1,5,17,85]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_153 : 0 < 153 ∧ 9+2 < 2*σ 0 153 :=
  checkRule 153 9 [1,3,9,17,51,153]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_222 : 0 < 222 ∧ 13+2 < 2*σ 0 222 :=
  checkRule 222 13 [1,2,3,6,37,74,111,222]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_86 : 0 < 86 ∧ 5+2 < 2*σ 0 86 :=
  checkRule 86 5 [1,2,43,86]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_87 : 0 < 87 ∧ 5+2 < 2*σ 0 87 :=
  checkRule 87 5 [1,3,29,87]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_230 : 0 < 230 ∧ 13+2 < 2*σ 0 230 :=
  checkRule 230 13 [1,2,5,10,23,46,115,230]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_304 : 0 < 304 ∧ 17+2 < 2*σ 0 304 :=
  checkRule 304 17 [1,2,4,8,16,19,38,76,152,304]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_380 : 0 < 380 ∧ 21+2 < 2*σ 0 380 :=
  checkRule 380 21 [1,2,4,5,10,19,20,38,76,95,190,380]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_164 : 0 < 164 ∧ 9+2 < 2*σ 0 164 :=
  checkRule 164 9 [1,2,4,41,82,164]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_93 : 0 < 93 ∧ 5+2 < 2*σ 0 93 :=
  checkRule 93 5 [1,3,31,93]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_94 : 0 < 94 ∧ 5+2 < 2*σ 0 94 :=
  checkRule 94 5 [1,2,47,94]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_246 : 0 < 246 ∧ 13+2 < 2*σ 0 246 :=
  checkRule 246 13 [1,2,3,6,41,82,123,246]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_171 : 0 < 171 ∧ 9+2 < 2*σ 0 171 :=
  checkRule 171 9 [1,3,9,19,57,171]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_552 : 0 < 552 ∧ 29+2 < 2*σ 0 552 :=
  checkRule 552 29 [1,2,3,4,6,8,12,23,24,46,69,92,138,184,276,552]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_172 : 0 < 172 ∧ 9+2 < 2*σ 0 172 :=
  checkRule 172 9 [1,2,4,43,86,172]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_250 : 0 < 250 ∧ 13+2 < 2*σ 0 250 :=
  checkRule 250 13 [1,2,5,10,25,50,125,250]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_414 : 0 < 414 ∧ 21+2 < 2*σ 0 414 :=
  checkRule 414 21 [1,2,3,6,9,18,23,46,69,138,207,414]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_258 : 0 < 258 ∧ 13+2 < 2*σ 0 258 :=
  checkRule 258 13 [1,2,3,6,43,86,129,258]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_188 : 0 < 188 ∧ 9+2 < 2*σ 0 188 :=
  checkRule 188 9 [1,2,4,47,94,188]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_106 : 0 < 106 ∧ 5+2 < 2*σ 0 106 :=
  checkRule 106 5 [1,2,53,106]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_368 : 0 < 368 ∧ 17+2 < 2*σ 0 368 :=
  checkRule 368 17 [1,2,4,8,16,23,46,92,184,368]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_282 : 0 < 282 ∧ 13+2 < 2*σ 0 282 :=
  checkRule 282 13 [1,2,3,6,47,94,141,282]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_460 : 0 < 460 ∧ 21+2 < 2*σ 0 460 :=
  checkRule 460 21 [1,2,4,5,10,20,23,46,92,115,230,460]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_111 : 0 < 111 ∧ 5+2 < 2*σ 0 111 :=
  checkRule 111 5 [1,3,37,111]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_290 : 0 < 290 ∧ 13+2 < 2*σ 0 290 :=
  checkRule 290 13 [1,2,5,10,29,58,145,290]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_115 : 0 < 115 ∧ 5+2 < 2*σ 0 115 :=
  checkRule 115 5 [1,5,23,115]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_207 : 0 < 207 ∧ 9+2 < 2*σ 0 207 :=
  checkRule 207 9 [1,3,9,23,69,207]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_486 : 0 < 486 ∧ 21+2 < 2*σ 0 486 :=
  checkRule 486 21 [1,2,3,6,9,18,27,54,81,162,243,486]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_212 : 0 < 212 ∧ 9+2 < 2*σ 0 212 :=
  checkRule 212 9 [1,2,4,53,106,212]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_118 : 0 < 118 ∧ 5+2 < 2*σ 0 118 :=
  checkRule 118 5 [1,2,59,118]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_500 : 0 < 500 ∧ 21+2 < 2*σ 0 500 :=
  checkRule 500 21 [1,2,4,5,10,20,25,50,100,125,250,500]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_310 : 0 < 310 ∧ 13+2 < 2*σ 0 310 :=
  checkRule 310 13 [1,2,5,10,31,62,155,310]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_696 : 0 < 696 ∧ 29+2 < 2*σ 0 696 :=
  checkRule 696 29 [1,2,3,4,6,8,12,24,29,58,87,116,174,232,348,696]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_122 : 0 < 122 ∧ 5+2 < 2*σ 0 122 :=
  checkRule 122 5 [1,2,61,122]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_318 : 0 < 318 ∧ 13+2 < 2*σ 0 318 :=
  checkRule 318 13 [1,2,3,6,53,106,159,318]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_123 : 0 < 123 ∧ 5+2 < 2*σ 0 123 :=
  checkRule 123 5 [1,3,41,123]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_522 : 0 < 522 ∧ 21+2 < 2*σ 0 522 :=
  checkRule 522 21 [1,2,3,6,9,18,29,58,87,174,261,522]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_125 : 0 < 125 ∧ 5+2 < 2*σ 0 125 :=
  checkRule 125 5 [1,5,25,125]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_744 : 0 < 744 ∧ 29+2 < 2*σ 0 744 :=
  checkRule 744 29 [1,2,3,4,6,8,12,24,31,62,93,124,186,248,372,744]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_129 : 0 < 129 ∧ 5+2 < 2*σ 0 129 :=
  checkRule 129 5 [1,3,43,129]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_236 : 0 < 236 ∧ 9+2 < 2*σ 0 236 :=
  checkRule 236 9 [1,2,4,59,118,236]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_558 : 0 < 558 ∧ 21+2 < 2*σ 0 558 :=
  checkRule 558 21 [1,2,3,6,9,18,31,62,93,186,279,558]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_134 : 0 < 134 ∧ 5+2 < 2*σ 0 134 :=
  checkRule 134 5 [1,2,67,134]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_243 : 0 < 243 ∧ 9+2 < 2*σ 0 243 :=
  checkRule 243 9 [1,3,9,27,81,243]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_244 : 0 < 244 ∧ 9+2 < 2*σ 0 244 :=
  checkRule 244 9 [1,2,4,61,122,244]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_354 : 0 < 354 ∧ 13+2 < 2*σ 0 354 :=
  checkRule 354 13 [1,2,3,6,59,118,177,354]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_464 : 0 < 464 ∧ 17+2 < 2*σ 0 464 :=
  checkRule 464 17 [1,2,4,8,16,29,58,116,232,464]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_580 : 0 < 580 ∧ 21+2 < 2*σ 0 580 :=
  checkRule 580 21 [1,2,4,5,10,20,29,58,116,145,290,580]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_366 : 0 < 366 ∧ 13+2 < 2*σ 0 366 :=
  checkRule 366 13 [1,2,3,6,61,122,183,366]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_141 : 0 < 141 ∧ 5+2 < 2*σ 0 141 :=
  checkRule 141 5 [1,3,47,141]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_142 : 0 < 142 ∧ 5+2 < 2*σ 0 142 :=
  checkRule 142 5 [1,2,71,142]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_370 : 0 < 370 ∧ 13+2 < 2*σ 0 370 :=
  checkRule 370 13 [1,2,5,10,37,74,185,370]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_29 : 0 < 29 ∧ 1+2 < 2*σ 0 29 :=
  checkRule 29 1 [1,29]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_145 : 0 < 145 ∧ 5+2 < 2*σ 0 145 :=
  checkRule 145 5 [1,5,29,145]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_261 : 0 < 261 ∧ 9+2 < 2*σ 0 261 :=
  checkRule 261 9 [1,3,9,29,87,261]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_31 : 0 < 31 ∧ 1+2 < 2*σ 0 31 :=
  checkRule 31 1 [1,31]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_279 : 0 < 279 ∧ 9+2 < 2*σ 0 279 :=
  checkRule 279 9 [1,3,9,31,93,279]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_155 : 0 < 155 ∧ 5+2 < 2*σ 0 155 :=
  checkRule 155 5 [1,5,31,155]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_333 : 0 < 333 ∧ 9+2 < 2*σ 0 333 :=
  checkRule 333 9 [1,3,9,37,111,333]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_496 : 0 < 496 ∧ 17+2 < 2*σ 0 496 :=
  checkRule 496 17 [1,2,4,8,16,31,62,124,248,496]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_47 : 0 < 47 ∧ 1+2 < 2*σ 0 47 :=
  checkRule 47 1 [1,47]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_740 : 0 < 740 ∧ 21+2 < 2*σ 0 740 :=
  checkRule 740 21 [1,2,4,5,10,20,37,74,148,185,370,740]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_235 : 0 < 235 ∧ 5+2 < 2*σ 0 235 :=
  checkRule 235 5 [1,5,47,235]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_423 : 0 < 423 ∧ 9+2 < 2*σ 0 423 :=
  checkRule 423 9 [1,3,9,47,141,423]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_530 : 0 < 530 ∧ 13+2 < 2*σ 0 530 :=
  checkRule 530 13 [1,2,5,10,53,106,265,530]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1425 : 0 < 1425 ∧ 21+2 < 2*σ 0 1425 :=
  checkRule 1425 21 [1,3,5,15,19,25,57,75,95,285,475,1425]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1862 : 0 < 1862 ∧ 21+2 < 2*σ 0 1862 :=
  checkRule 1862 21 [1,2,7,14,19,38,49,98,133,266,931,1862]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2550 : 0 < 2550 ∧ 45+2 < 2*σ 0 2550 :=
  checkRule 2550 45 [1,2,3,5,6,10,15,17,25,30,34,50,51,75,85,102,150,170,255,425,510,850,1275,2550]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_43 : 0 < 43 ∧ 1+2 < 2*σ 0 43 :=
  checkRule 43 1 [1,43]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_177 : 0 < 177 ∧ 5+2 < 2*σ 0 177 :=
  checkRule 177 5 [1,3,59,177]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_305 : 0 < 305 ∧ 5+2 < 2*σ 0 305 :=
  checkRule 305 5 [1,5,61,305]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_512 : 0 < 512 ∧ 17+2 < 2*σ 0 512 :=
  checkRule 512 17 [1,2,4,8,16,32,64,128,256,512]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_652 : 0 < 652 ∧ 9+2 < 2*σ 0 652 :=
  checkRule 652 9 [1,2,4,163,326,652]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_678 : 0 < 678 ∧ 13+2 < 2*σ 0 678 :=
  checkRule 678 13 [1,2,3,6,113,226,339,678]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_940 : 0 < 940 ∧ 21+2 < 2*σ 0 940 :=
  checkRule 940 21 [1,2,4,5,10,20,47,94,188,235,470,940]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1128 : 0 < 1128 ∧ 29+2 < 2*σ 0 1128 :=
  checkRule 1128 29 [1,2,3,4,6,8,12,24,47,94,141,188,282,376,564,1128]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1270 : 0 < 1270 ∧ 13+2 < 2*σ 0 1270 :=
  checkRule 1270 13 [1,2,5,10,127,254,635,1270]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2468 : 0 < 2468 ∧ 9+2 < 2*σ 0 2468 :=
  checkRule 2468 9 [1,2,4,617,1234,2468]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_73 : 0 < 73 ∧ 1+2 < 2*σ 0 73 :=
  checkRule 73 1 [1,73]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_158 : 0 < 158 ∧ 5+2 < 2*σ 0 158 :=
  checkRule 158 5 [1,2,79,158]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_218 : 0 < 218 ∧ 5+2 < 2*σ 0 218 :=
  checkRule 218 5 [1,2,109,218]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_268 : 0 < 268 ∧ 9+2 < 2*σ 0 268 :=
  checkRule 268 9 [1,2,4,67,134,268]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_346 : 0 < 346 ∧ 5+2 < 2*σ 0 346 :=
  checkRule 346 5 [1,2,173,346]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_388 : 0 < 388 ∧ 9+2 < 2*σ 0 388 :=
  checkRule 388 9 [1,2,4,97,194,388]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_402 : 0 < 402 ∧ 13+2 < 2*σ 0 402 :=
  checkRule 402 13 [1,2,3,6,67,134,201,402]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_674 : 0 < 674 ∧ 5+2 < 2*σ 0 674 :=
  checkRule 674 5 [1,2,337,674]
    (by decide) (by decide) (by decide) (by decide)

private def rules : List Rule :=
  [⟨32,9,valid_32⟩,
   ⟨34,5,valid_34⟩,
   ⟨68,9,valid_68⟩,
   ⟨38,5,valid_38⟩,
   ⟨192,25,valid_192⟩,
   ⟨102,13,valid_102⟩,
   ⟨76,9,valid_76⟩,
   ⟨114,13,valid_114⟩,
   ⟨46,5,valid_46⟩,
   ⟨51,5,valid_51⟩,
   ⟨92,9,valid_92⟩,
   ⟨138,13,valid_138⟩,
   ⟨57,5,valid_57⟩,
   ⟨58,5,valid_58⟩,
   ⟨62,5,valid_62⟩,
   ⟨116,9,valid_116⟩,
   ⟨170,13,valid_170⟩,
   ⟨174,13,valid_174⟩,
   ⟨124,9,valid_124⟩,
   ⟨69,5,valid_69⟩,
   ⟨408,29,valid_408⟩,
   ⟨186,13,valid_186⟩,
   ⟨306,21,valid_306⟩,
   ⟨190,13,valid_190⟩,
   ⟨74,5,valid_74⟩,
   ⟨456,29,valid_456⟩,
   ⟨272,17,valid_272⟩,
   ⟨342,21,valid_342⟩,
   ⟨82,5,valid_82⟩,
   ⟨148,9,valid_148⟩,
   ⟨85,5,valid_85⟩,
   ⟨153,9,valid_153⟩,
   ⟨222,13,valid_222⟩,
   ⟨86,5,valid_86⟩,
   ⟨87,5,valid_87⟩,
   ⟨230,13,valid_230⟩,
   ⟨304,17,valid_304⟩,
   ⟨380,21,valid_380⟩,
   ⟨164,9,valid_164⟩,
   ⟨93,5,valid_93⟩,
   ⟨94,5,valid_94⟩,
   ⟨246,13,valid_246⟩,
   ⟨171,9,valid_171⟩,
   ⟨552,29,valid_552⟩,
   ⟨172,9,valid_172⟩,
   ⟨250,13,valid_250⟩,
   ⟨414,21,valid_414⟩,
   ⟨258,13,valid_258⟩,
   ⟨188,9,valid_188⟩,
   ⟨106,5,valid_106⟩,
   ⟨368,17,valid_368⟩,
   ⟨282,13,valid_282⟩,
   ⟨460,21,valid_460⟩,
   ⟨111,5,valid_111⟩,
   ⟨290,13,valid_290⟩,
   ⟨115,5,valid_115⟩,
   ⟨207,9,valid_207⟩,
   ⟨486,21,valid_486⟩,
   ⟨212,9,valid_212⟩,
   ⟨118,5,valid_118⟩,
   ⟨500,21,valid_500⟩,
   ⟨310,13,valid_310⟩,
   ⟨696,29,valid_696⟩,
   ⟨122,5,valid_122⟩,
   ⟨318,13,valid_318⟩,
   ⟨123,5,valid_123⟩,
   ⟨522,21,valid_522⟩,
   ⟨125,5,valid_125⟩,
   ⟨744,29,valid_744⟩,
   ⟨129,5,valid_129⟩,
   ⟨236,9,valid_236⟩,
   ⟨558,21,valid_558⟩,
   ⟨134,5,valid_134⟩,
   ⟨243,9,valid_243⟩,
   ⟨244,9,valid_244⟩,
   ⟨354,13,valid_354⟩,
   ⟨464,17,valid_464⟩,
   ⟨580,21,valid_580⟩,
   ⟨366,13,valid_366⟩,
   ⟨141,5,valid_141⟩,
   ⟨142,5,valid_142⟩,
   ⟨370,13,valid_370⟩,
   ⟨29,1,valid_29⟩,
   ⟨145,5,valid_145⟩,
   ⟨261,9,valid_261⟩,
   ⟨31,1,valid_31⟩,
   ⟨279,9,valid_279⟩,
   ⟨155,5,valid_155⟩,
   ⟨333,9,valid_333⟩,
   ⟨496,17,valid_496⟩,
   ⟨47,1,valid_47⟩,
   ⟨740,21,valid_740⟩,
   ⟨235,5,valid_235⟩,
   ⟨423,9,valid_423⟩,
   ⟨530,13,valid_530⟩,
   ⟨1425,21,valid_1425⟩,
   ⟨1862,21,valid_1862⟩,
   ⟨2550,45,valid_2550⟩,
   ⟨43,1,valid_43⟩,
   ⟨177,5,valid_177⟩,
   ⟨305,5,valid_305⟩,
   ⟨512,17,valid_512⟩,
   ⟨652,9,valid_652⟩,
   ⟨678,13,valid_678⟩,
   ⟨940,21,valid_940⟩,
   ⟨1128,29,valid_1128⟩,
   ⟨1270,13,valid_1270⟩,
   ⟨2468,9,valid_2468⟩,
   ⟨73,1,valid_73⟩,
   ⟨158,5,valid_158⟩,
   ⟨218,5,valid_218⟩,
   ⟨268,9,valid_268⟩,
   ⟨346,5,valid_346⟩,
   ⟨388,9,valid_388⟩,
   ⟨402,13,valid_402⟩,
   ⟨674,5,valid_674⟩]

private def hitAt (n : ℕ) : Bool :=
  rules.any (fun z => decide (z.modulus*z.modulus+z.modulus ≤ n ∧
    0 < n%z.modulus ∧ n%z.modulus ≤ z.radius))

private theorem contradictionOfHit {n : ℕ} (good : Good n) (hit : hitAt n = true) : False := by
  obtain ⟨z, _, yes⟩ := List.any_eq_true.mp hit
  obtain ⟨large, pos, small⟩ := of_decide_eq_true yes
  obtain ⟨hd, impossible⟩ := z.valid
  have bound := residueBound good hd large pos
  omega

private def batch (b : ℕ) : Bool :=
  (List.range 125).all (fun i => hitAt (360360*(1+125*b+i)))

private theorem batch_0 : batch 0 = true := by decide
private theorem batch_1 : batch 1 = true := by decide
private theorem batch_2 : batch 2 = true := by decide
private theorem batch_3 : batch 3 = true := by decide
private theorem batch_4 : batch 4 = true := by decide
private theorem batch_5 : batch 5 = true := by decide
private theorem batch_6 : batch 6 = true := by decide
private theorem batch_7 : batch 7 = true := by decide
private theorem batch_8 : batch 8 = true := by decide
private theorem batch_9 : batch 9 = true := by decide
private theorem batch_10 : batch 10 = true := by decide
private theorem batch_11 : batch 11 = true := by decide
private theorem batch_12 : batch 12 = true := by decide
private theorem batch_13 : batch 13 = true := by decide
private theorem batch_14 : batch 14 = true := by decide
private theorem batch_15 : batch 15 = true := by decide
private theorem batch_16 : batch 16 = true := by decide
private theorem batch_17 : batch 17 = true := by decide
private theorem batch_18 : batch 18 = true := by decide
private theorem batch_19 : batch 19 = true := by decide
private theorem batch_20 : batch 20 = true := by decide
private theorem batch_21 : batch 21 = true := by decide
private theorem batch_22 : batch 22 = true := by decide
private theorem batch_23 : batch 23 = true := by decide
private theorem batch_24 : batch 24 = true := by decide
private theorem batch_25 : batch 25 = true := by decide
private theorem batch_26 : batch 26 = true := by decide
private theorem batch_27 : batch 27 = true := by decide
private theorem batch_28 : batch 28 = true := by decide
private theorem batch_29 : batch 29 = true := by decide
private theorem batch_30 : batch 30 = true := by decide
private theorem batch_31 : batch 31 = true := by decide
private theorem batch_32 : batch 32 = true := by decide
private theorem batch_33 : batch 33 = true := by decide
private theorem batch_34 : batch 34 = true := by decide
private theorem batch_35 : batch 35 = true := by decide
private theorem batch_36 : batch 36 = true := by decide
private theorem batch_37 : batch 37 = true := by decide
private theorem batch_38 : batch 38 = true := by decide
private theorem batch_39 : batch 39 = true := by decide
private theorem batch_40 : batch 40 = true := by decide
private theorem batch_41 : batch 41 = true := by decide
private theorem batch_42 : batch 42 = true := by decide
private theorem batch_43 : batch 43 = true := by decide
private theorem batch_44 : batch 44 = true := by decide
private theorem batch_45 : batch 45 = true := by decide
private theorem batch_46 : batch 46 = true := by decide
private theorem batch_47 : batch 47 = true := by decide
private theorem batch_48 : batch 48 = true := by decide
private theorem batch_49 : batch 49 = true := by decide
private theorem batch_50 : batch 50 = true := by decide
private theorem batch_51 : batch 51 = true := by decide
private theorem batch_52 : batch 52 = true := by decide
private theorem batch_53 : batch 53 = true := by decide
private theorem batch_54 : batch 54 = true := by decide
private theorem batch_55 : batch 55 = true := by decide
private theorem batch_56 : batch 56 = true := by decide
private theorem batch_57 : batch 57 = true := by decide
private theorem batch_58 : batch 58 = true := by decide
private theorem batch_59 : batch 59 = true := by decide
private theorem batch_60 : batch 60 = true := by decide
private theorem batch_61 : batch 61 = true := by decide
private theorem batch_62 : batch 62 = true := by decide
private theorem batch_63 : batch 63 = true := by decide
private theorem batch_64 : batch 64 = true := by decide
private theorem batch_65 : batch 65 = true := by decide
private theorem batch_66 : batch 66 = true := by decide
private theorem batch_67 : batch 67 = true := by decide
private theorem batch_68 : batch 68 = true := by decide
private theorem batch_69 : batch 69 = true := by decide
private theorem batch_70 : batch 70 = true := by decide
private theorem batch_71 : batch 71 = true := by decide
private theorem batch_72 : batch 72 = true := by decide
private theorem batch_73 : batch 73 = true := by decide
private theorem batch_74 : batch 74 = true := by decide
private theorem batch_75 : batch 75 = true := by decide
private theorem batch_76 : batch 76 = true := by decide
private theorem batch_77 : batch 77 = true := by decide
private theorem batch_78 : batch 78 = true := by decide
private theorem batch_79 : batch 79 = true := by decide
private theorem batch_80 : batch 80 = true := by decide
private theorem batch_81 : batch 81 = true := by decide
private theorem batch_82 : batch 82 = true := by decide
private theorem batch_83 : batch 83 = true := by decide
private theorem batch_84 : batch 84 = true := by decide
private theorem batch_85 : batch 85 = true := by decide
private theorem batch_86 : batch 86 = true := by decide
private theorem batch_87 : batch 87 = true := by decide
private theorem batch_88 : batch 88 = true := by decide
private theorem batch_89 : batch 89 = true := by decide
private theorem batch_90 : batch 90 = true := by decide
private theorem batch_91 : batch 91 = true := by decide
private theorem batch_92 : batch 92 = true := by decide
private theorem batch_93 : batch 93 = true := by decide
private theorem batch_94 : batch 94 = true := by decide
private theorem batch_95 : batch 95 = true := by decide
private theorem batch_96 : batch 96 = true := by decide
private theorem batch_97 : batch 97 = true := by decide
private theorem batch_98 : batch 98 = true := by decide
private theorem batch_99 : batch 99 = true := by decide
private theorem batch_100 : batch 100 = true := by decide
private theorem batch_101 : batch 101 = true := by decide
private theorem batch_102 : batch 102 = true := by decide
private theorem batch_103 : batch 103 = true := by decide
private theorem batch_104 : batch 104 = true := by decide
private theorem batch_105 : batch 105 = true := by decide
private theorem batch_106 : batch 106 = true := by decide
private theorem batch_107 : batch 107 = true := by decide
private theorem batch_108 : batch 108 = true := by decide
private theorem batch_109 : batch 109 = true := by decide
private theorem batch_110 : batch 110 = true := by decide
private theorem batch_111 : batch 111 = true := by decide
private theorem batch_112 : batch 112 = true := by decide
private theorem batch_113 : batch 113 = true := by decide
private theorem batch_114 : batch 114 = true := by decide
private theorem batch_115 : batch 115 = true := by decide
private theorem batch_116 : batch 116 = true := by decide
private theorem batch_117 : batch 117 = true := by decide
private theorem batch_118 : batch 118 = true := by decide
private theorem batch_119 : batch 119 = true := by decide
private theorem batch_120 : batch 120 = true := by decide
private theorem batch_121 : batch 121 = true := by decide
private theorem batch_122 : batch 122 = true := by decide
private theorem batch_123 : batch 123 = true := by decide
private theorem batch_124 : batch 124 = true := by decide
private theorem batch_125 : batch 125 = true := by decide
private theorem batch_126 : batch 126 = true := by decide
private theorem batch_127 : batch 127 = true := by decide
private theorem batch_128 : batch 128 = true := by decide
private theorem batch_129 : batch 129 = true := by decide
private theorem batch_130 : batch 130 = true := by decide
private theorem batch_131 : batch 131 = true := by decide
private theorem batch_132 : batch 132 = true := by decide
private theorem batch_133 : batch 133 = true := by decide
private theorem batch_134 : batch 134 = true := by decide
private theorem batch_135 : batch 135 = true := by decide
private theorem batch_136 : batch 136 = true := by decide
private theorem batch_137 : batch 137 = true := by decide
private theorem batch_138 : batch 138 = true := by decide
private theorem batch_139 : batch 139 = true := by decide
private theorem batch_140 : batch 140 = true := by decide
private theorem batch_141 : batch 141 = true := by decide
private theorem batch_142 : batch 142 = true := by decide
private theorem batch_143 : batch 143 = true := by decide
private theorem batch_144 : batch 144 = true := by decide
private theorem batch_145 : batch 145 = true := by decide
private theorem batch_146 : batch 146 = true := by decide
private theorem batch_147 : batch 147 = true := by decide
private theorem batch_148 : batch 148 = true := by decide
private theorem batch_149 : batch 149 = true := by decide
private theorem batch_150 : batch 150 = true := by decide
private theorem batch_151 : batch 151 = true := by decide
private theorem batch_152 : batch 152 = true := by decide
private theorem batch_153 : batch 153 = true := by decide
private theorem batch_154 : batch 154 = true := by decide
private theorem batch_155 : batch 155 = true := by decide
private theorem batch_156 : batch 156 = true := by decide
private theorem batch_157 : batch 157 = true := by decide
private theorem batch_158 : batch 158 = true := by decide
private theorem batch_159 : batch 159 = true := by decide
private theorem batch_160 : batch 160 = true := by decide
private theorem batch_161 : batch 161 = true := by decide
private theorem batch_162 : batch 162 = true := by decide
private theorem batch_163 : batch 163 = true := by decide
private theorem batch_164 : batch 164 = true := by decide
private theorem batch_165 : batch 165 = true := by decide
private theorem batch_166 : batch 166 = true := by decide
private theorem batch_167 : batch 167 = true := by decide
private theorem batch_168 : batch 168 = true := by decide
private theorem batch_169 : batch 169 = true := by decide
private theorem batch_170 : batch 170 = true := by decide
private theorem batch_171 : batch 171 = true := by decide
private theorem batch_172 : batch 172 = true := by decide
private theorem batch_173 : batch 173 = true := by decide
private theorem batch_174 : batch 174 = true := by decide
private theorem batch_175 : batch 175 = true := by decide
private theorem batch_176 : batch 176 = true := by decide
private theorem batch_177 : batch 177 = true := by decide
private theorem batch_178 : batch 178 = true := by decide
private theorem batch_179 : batch 179 = true := by decide
private theorem batch_180 : batch 180 = true := by decide
private theorem batch_181 : batch 181 = true := by decide
private theorem batch_182 : batch 182 = true := by decide
private theorem batch_183 : batch 183 = true := by decide
private theorem batch_184 : batch 184 = true := by decide
private theorem batch_185 : batch 185 = true := by decide
private theorem batch_186 : batch 186 = true := by decide
private theorem batch_187 : batch 187 = true := by decide
private theorem batch_188 : batch 188 = true := by decide
private theorem batch_189 : batch 189 = true := by decide
private theorem batch_190 : batch 190 = true := by decide
private theorem batch_191 : batch 191 = true := by decide
private theorem batch_192 : batch 192 = true := by decide
private theorem batch_193 : batch 193 = true := by decide
private theorem batch_194 : batch 194 = true := by decide
private theorem batch_195 : batch 195 = true := by decide
private theorem batch_196 : batch 196 = true := by decide
private theorem batch_197 : batch 197 = true := by decide
private theorem batch_198 : batch 198 = true := by decide
private theorem batch_199 : batch 199 = true := by decide
private theorem batch_200 : batch 200 = true := by decide
private theorem batch_201 : batch 201 = true := by decide
private theorem batch_202 : batch 202 = true := by decide
private theorem batch_203 : batch 203 = true := by decide
private theorem batch_204 : batch 204 = true := by decide
private theorem batch_205 : batch 205 = true := by decide
private theorem batch_206 : batch 206 = true := by decide
private theorem batch_207 : batch 207 = true := by decide
private theorem batch_208 : batch 208 = true := by decide
private theorem batch_209 : batch 209 = true := by decide
private theorem batch_210 : batch 210 = true := by decide
private theorem batch_211 : batch 211 = true := by decide
private theorem batch_212 : batch 212 = true := by decide
private theorem batch_213 : batch 213 = true := by decide
private theorem batch_214 : batch 214 = true := by decide
private theorem batch_215 : batch 215 = true := by decide
private theorem batch_216 : batch 216 = true := by decide
private theorem batch_217 : batch 217 = true := by decide
private theorem batch_218 : batch 218 = true := by decide
private theorem batch_219 : batch 219 = true := by decide
private theorem batch_220 : batch 220 = true := by decide
private theorem batch_221 : batch 221 = true := by decide

private theorem singleBatch (a : ℕ) (ha : batch a = true) :
    ∀ x : ℕ, a ≤ x → x < a+1 → batch x = true := by
  intro x lo hi
  simpa only [show x = a by omega] using ha

private theorem joinBatch {a b c : ℕ}
    (h₁ : ∀ x : ℕ, a ≤ x → x < b → batch x = true)
    (h₂ : ∀ x : ℕ, b ≤ x → x < c → batch x = true) :
    ∀ x : ℕ, a ≤ x → x < c → batch x = true := by
  intro x lo hi
  by_cases left : x < b
  · exact h₁ x lo left
  · exact h₂ x (by omega) hi

private theorem allBatches : ∀ x : ℕ, 0 ≤ x → x < 222 → batch x = true :=
  joinBatch
    (joinBatch
      (joinBatch
        (joinBatch
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 0 batch_0)
                (joinBatch
                  (singleBatch 1 batch_1)
                  (singleBatch 2 batch_2)))
              (joinBatch
                (singleBatch 3 batch_3)
                (joinBatch
                  (singleBatch 4 batch_4)
                  (singleBatch 5 batch_5))))
            (joinBatch
              (joinBatch
                (singleBatch 6 batch_6)
                (joinBatch
                  (singleBatch 7 batch_7)
                  (singleBatch 8 batch_8)))
              (joinBatch
                (joinBatch
                  (singleBatch 9 batch_9)
                  (singleBatch 10 batch_10))
                (joinBatch
                  (singleBatch 11 batch_11)
                  (singleBatch 12 batch_12)))))
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 13 batch_13)
                (joinBatch
                  (singleBatch 14 batch_14)
                  (singleBatch 15 batch_15)))
              (joinBatch
                (joinBatch
                  (singleBatch 16 batch_16)
                  (singleBatch 17 batch_17))
                (joinBatch
                  (singleBatch 18 batch_18)
                  (singleBatch 19 batch_19))))
            (joinBatch
              (joinBatch
                (singleBatch 20 batch_20)
                (joinBatch
                  (singleBatch 21 batch_21)
                  (singleBatch 22 batch_22)))
              (joinBatch
                (joinBatch
                  (singleBatch 23 batch_23)
                  (singleBatch 24 batch_24))
                (joinBatch
                  (singleBatch 25 batch_25)
                  (singleBatch 26 batch_26))))))
        (joinBatch
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 27 batch_27)
                (joinBatch
                  (singleBatch 28 batch_28)
                  (singleBatch 29 batch_29)))
              (joinBatch
                (joinBatch
                  (singleBatch 30 batch_30)
                  (singleBatch 31 batch_31))
                (joinBatch
                  (singleBatch 32 batch_32)
                  (singleBatch 33 batch_33))))
            (joinBatch
              (joinBatch
                (singleBatch 34 batch_34)
                (joinBatch
                  (singleBatch 35 batch_35)
                  (singleBatch 36 batch_36)))
              (joinBatch
                (joinBatch
                  (singleBatch 37 batch_37)
                  (singleBatch 38 batch_38))
                (joinBatch
                  (singleBatch 39 batch_39)
                  (singleBatch 40 batch_40)))))
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 41 batch_41)
                (joinBatch
                  (singleBatch 42 batch_42)
                  (singleBatch 43 batch_43)))
              (joinBatch
                (joinBatch
                  (singleBatch 44 batch_44)
                  (singleBatch 45 batch_45))
                (joinBatch
                  (singleBatch 46 batch_46)
                  (singleBatch 47 batch_47))))
            (joinBatch
              (joinBatch
                (singleBatch 48 batch_48)
                (joinBatch
                  (singleBatch 49 batch_49)
                  (singleBatch 50 batch_50)))
              (joinBatch
                (joinBatch
                  (singleBatch 51 batch_51)
                  (singleBatch 52 batch_52))
                (joinBatch
                  (singleBatch 53 batch_53)
                  (singleBatch 54 batch_54)))))))
      (joinBatch
        (joinBatch
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 55 batch_55)
                (joinBatch
                  (singleBatch 56 batch_56)
                  (singleBatch 57 batch_57)))
              (joinBatch
                (joinBatch
                  (singleBatch 58 batch_58)
                  (singleBatch 59 batch_59))
                (joinBatch
                  (singleBatch 60 batch_60)
                  (singleBatch 61 batch_61))))
            (joinBatch
              (joinBatch
                (singleBatch 62 batch_62)
                (joinBatch
                  (singleBatch 63 batch_63)
                  (singleBatch 64 batch_64)))
              (joinBatch
                (joinBatch
                  (singleBatch 65 batch_65)
                  (singleBatch 66 batch_66))
                (joinBatch
                  (singleBatch 67 batch_67)
                  (singleBatch 68 batch_68)))))
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 69 batch_69)
                (joinBatch
                  (singleBatch 70 batch_70)
                  (singleBatch 71 batch_71)))
              (joinBatch
                (joinBatch
                  (singleBatch 72 batch_72)
                  (singleBatch 73 batch_73))
                (joinBatch
                  (singleBatch 74 batch_74)
                  (singleBatch 75 batch_75))))
            (joinBatch
              (joinBatch
                (singleBatch 76 batch_76)
                (joinBatch
                  (singleBatch 77 batch_77)
                  (singleBatch 78 batch_78)))
              (joinBatch
                (joinBatch
                  (singleBatch 79 batch_79)
                  (singleBatch 80 batch_80))
                (joinBatch
                  (singleBatch 81 batch_81)
                  (singleBatch 82 batch_82))))))
        (joinBatch
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 83 batch_83)
                (joinBatch
                  (singleBatch 84 batch_84)
                  (singleBatch 85 batch_85)))
              (joinBatch
                (joinBatch
                  (singleBatch 86 batch_86)
                  (singleBatch 87 batch_87))
                (joinBatch
                  (singleBatch 88 batch_88)
                  (singleBatch 89 batch_89))))
            (joinBatch
              (joinBatch
                (singleBatch 90 batch_90)
                (joinBatch
                  (singleBatch 91 batch_91)
                  (singleBatch 92 batch_92)))
              (joinBatch
                (joinBatch
                  (singleBatch 93 batch_93)
                  (singleBatch 94 batch_94))
                (joinBatch
                  (singleBatch 95 batch_95)
                  (singleBatch 96 batch_96)))))
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 97 batch_97)
                (joinBatch
                  (singleBatch 98 batch_98)
                  (singleBatch 99 batch_99)))
              (joinBatch
                (joinBatch
                  (singleBatch 100 batch_100)
                  (singleBatch 101 batch_101))
                (joinBatch
                  (singleBatch 102 batch_102)
                  (singleBatch 103 batch_103))))
            (joinBatch
              (joinBatch
                (singleBatch 104 batch_104)
                (joinBatch
                  (singleBatch 105 batch_105)
                  (singleBatch 106 batch_106)))
              (joinBatch
                (joinBatch
                  (singleBatch 107 batch_107)
                  (singleBatch 108 batch_108))
                (joinBatch
                  (singleBatch 109 batch_109)
                  (singleBatch 110 batch_110))))))))
    (joinBatch
      (joinBatch
        (joinBatch
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 111 batch_111)
                (joinBatch
                  (singleBatch 112 batch_112)
                  (singleBatch 113 batch_113)))
              (joinBatch
                (singleBatch 114 batch_114)
                (joinBatch
                  (singleBatch 115 batch_115)
                  (singleBatch 116 batch_116))))
            (joinBatch
              (joinBatch
                (singleBatch 117 batch_117)
                (joinBatch
                  (singleBatch 118 batch_118)
                  (singleBatch 119 batch_119)))
              (joinBatch
                (joinBatch
                  (singleBatch 120 batch_120)
                  (singleBatch 121 batch_121))
                (joinBatch
                  (singleBatch 122 batch_122)
                  (singleBatch 123 batch_123)))))
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 124 batch_124)
                (joinBatch
                  (singleBatch 125 batch_125)
                  (singleBatch 126 batch_126)))
              (joinBatch
                (joinBatch
                  (singleBatch 127 batch_127)
                  (singleBatch 128 batch_128))
                (joinBatch
                  (singleBatch 129 batch_129)
                  (singleBatch 130 batch_130))))
            (joinBatch
              (joinBatch
                (singleBatch 131 batch_131)
                (joinBatch
                  (singleBatch 132 batch_132)
                  (singleBatch 133 batch_133)))
              (joinBatch
                (joinBatch
                  (singleBatch 134 batch_134)
                  (singleBatch 135 batch_135))
                (joinBatch
                  (singleBatch 136 batch_136)
                  (singleBatch 137 batch_137))))))
        (joinBatch
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 138 batch_138)
                (joinBatch
                  (singleBatch 139 batch_139)
                  (singleBatch 140 batch_140)))
              (joinBatch
                (joinBatch
                  (singleBatch 141 batch_141)
                  (singleBatch 142 batch_142))
                (joinBatch
                  (singleBatch 143 batch_143)
                  (singleBatch 144 batch_144))))
            (joinBatch
              (joinBatch
                (singleBatch 145 batch_145)
                (joinBatch
                  (singleBatch 146 batch_146)
                  (singleBatch 147 batch_147)))
              (joinBatch
                (joinBatch
                  (singleBatch 148 batch_148)
                  (singleBatch 149 batch_149))
                (joinBatch
                  (singleBatch 150 batch_150)
                  (singleBatch 151 batch_151)))))
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 152 batch_152)
                (joinBatch
                  (singleBatch 153 batch_153)
                  (singleBatch 154 batch_154)))
              (joinBatch
                (joinBatch
                  (singleBatch 155 batch_155)
                  (singleBatch 156 batch_156))
                (joinBatch
                  (singleBatch 157 batch_157)
                  (singleBatch 158 batch_158))))
            (joinBatch
              (joinBatch
                (singleBatch 159 batch_159)
                (joinBatch
                  (singleBatch 160 batch_160)
                  (singleBatch 161 batch_161)))
              (joinBatch
                (joinBatch
                  (singleBatch 162 batch_162)
                  (singleBatch 163 batch_163))
                (joinBatch
                  (singleBatch 164 batch_164)
                  (singleBatch 165 batch_165)))))))
      (joinBatch
        (joinBatch
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 166 batch_166)
                (joinBatch
                  (singleBatch 167 batch_167)
                  (singleBatch 168 batch_168)))
              (joinBatch
                (joinBatch
                  (singleBatch 169 batch_169)
                  (singleBatch 170 batch_170))
                (joinBatch
                  (singleBatch 171 batch_171)
                  (singleBatch 172 batch_172))))
            (joinBatch
              (joinBatch
                (singleBatch 173 batch_173)
                (joinBatch
                  (singleBatch 174 batch_174)
                  (singleBatch 175 batch_175)))
              (joinBatch
                (joinBatch
                  (singleBatch 176 batch_176)
                  (singleBatch 177 batch_177))
                (joinBatch
                  (singleBatch 178 batch_178)
                  (singleBatch 179 batch_179)))))
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 180 batch_180)
                (joinBatch
                  (singleBatch 181 batch_181)
                  (singleBatch 182 batch_182)))
              (joinBatch
                (joinBatch
                  (singleBatch 183 batch_183)
                  (singleBatch 184 batch_184))
                (joinBatch
                  (singleBatch 185 batch_185)
                  (singleBatch 186 batch_186))))
            (joinBatch
              (joinBatch
                (singleBatch 187 batch_187)
                (joinBatch
                  (singleBatch 188 batch_188)
                  (singleBatch 189 batch_189)))
              (joinBatch
                (joinBatch
                  (singleBatch 190 batch_190)
                  (singleBatch 191 batch_191))
                (joinBatch
                  (singleBatch 192 batch_192)
                  (singleBatch 193 batch_193))))))
        (joinBatch
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 194 batch_194)
                (joinBatch
                  (singleBatch 195 batch_195)
                  (singleBatch 196 batch_196)))
              (joinBatch
                (joinBatch
                  (singleBatch 197 batch_197)
                  (singleBatch 198 batch_198))
                (joinBatch
                  (singleBatch 199 batch_199)
                  (singleBatch 200 batch_200))))
            (joinBatch
              (joinBatch
                (singleBatch 201 batch_201)
                (joinBatch
                  (singleBatch 202 batch_202)
                  (singleBatch 203 batch_203)))
              (joinBatch
                (joinBatch
                  (singleBatch 204 batch_204)
                  (singleBatch 205 batch_205))
                (joinBatch
                  (singleBatch 206 batch_206)
                  (singleBatch 207 batch_207)))))
          (joinBatch
            (joinBatch
              (joinBatch
                (singleBatch 208 batch_208)
                (joinBatch
                  (singleBatch 209 batch_209)
                  (singleBatch 210 batch_210)))
              (joinBatch
                (joinBatch
                  (singleBatch 211 batch_211)
                  (singleBatch 212 batch_212))
                (joinBatch
                  (singleBatch 213 batch_213)
                  (singleBatch 214 batch_214))))
            (joinBatch
              (joinBatch
                (singleBatch 215 batch_215)
                (joinBatch
                  (singleBatch 216 batch_216)
                  (singleBatch 217 batch_217)))
              (joinBatch
                (joinBatch
                  (singleBatch 218 batch_218)
                  (singleBatch 219 batch_219))
                (joinBatch
                  (singleBatch 220 batch_220)
                  (singleBatch 221 batch_221))))))))

private theorem checkedMultipliers (b : Fin 222) (i : Fin 125) :
    hitAt (360360*(1+125*b.val+i.val)) = true := by
  have ok := allBatches b.val (Nat.zero_le _) b.isLt
  exact List.all_eq_true.mp ok i.val (List.mem_range.mpr i.isLt)

/-- An explicit witness exists against every candidate in the full indicated range. -/
theorem counterexampleAtEach (n : ℕ) (lo : 24 < n) (hi : n ≤ 10000000000) :
    ∃ m : Fin n, n+2 < (m:ℕ) + σ 0 (m:ℕ) := by
  by_contra! h
  have good : Good n := fun m hm => h ⟨m,hm⟩
  by_cases small : n < 97656
  · exact smallCounterexample good lo small
  obtain ⟨q, hq⟩ := necessaryDivisibility good (by omega)
  have lower : 1 ≤ q := by omega
  let b : Fin 222 := ⟨(q-1)/125, by omega⟩
  let i : Fin 125 := ⟨(q-1)%125, by omega⟩
  have repr : 360360*(1+125*b.val+i.val) = n := by dsimp [b,i]; omega
  apply contradictionOfHit good
  rw [← repr]
  exact checkedMultipliers b i

/-- The finite supremum in the actual prize statement exceeds n+2. -/
theorem originalFailsUpTo (n : ℕ) (lo : 24 < n) (hi : n ≤ 10000000000) :
    ¬ (⨆ m : Fin n, (m:ℕ) + σ 0 (m:ℕ)) ≤ n+2 := by
  intro claim
  obtain ⟨m, fails⟩ := counterexampleAtEach n lo hi
  have below := le_ciSup (f := fun j : Fin n => (j:ℕ) + σ 0 (j:ℕ))
    (Set.finite_range _).bddAbove m
  exact (not_lt_of_ge (below.trans claim)) fails

/- We sieve the multiplier in blocks. Each bit of a periodic mask represents
one residue permitted by the divisor bound. The kernel checks the intersection
of the masks and the individual divisor witnesses for every bit left over. -/

private structure Column where
  period : ℕ
  mask : ℕ
  height : ℕ
  positive : 0 < period
  capacity : 1000000 + period ≤ period*2^height
  allows : ∀ q, 64 ≤ q → Good (360360*q) → mask.testBit (q%period) = true

private def certifyColumn (p mask height : ℕ) (hp : 0 < p)
    (hw : 1000000+p ≤ p*2^height) (rows : List Rule)
    (hc : (List.range p).all (fun r => mask.testBit r || rows.any (fun z => decide
      (z.modulus ∣ 360360*p ∧ z.modulus*z.modulus+z.modulus ≤ 360360*64 ∧
        0 < (360360*r)%z.modulus ∧ (360360*r)%z.modulus ≤ z.radius))) = true) : Column where
  period := p
  mask := mask
  height := height
  positive := hp
  capacity := hw
  allows := by
    intro x lower good
    obtain ok | rejected := Bool.or_eq_true_iff.mp
      (List.all_eq_true.mp hc (x%p) (List.mem_range.mpr (Nat.mod_lt _ hp)))
    · exact ok
    obtain ⟨z, _, found⟩ := List.any_eq_true.mp rejected
    obtain ⟨periodic, large, pos, small⟩ := of_decide_eq_true found
    have modEq : 360360*(x%p) ≡ 360360*x [MOD z.modulus] :=
      ((Nat.mod_modEq x p).mul_left' 360360).of_dvd periodic
    change _ = _ at modEq
    rw [modEq] at pos small
    have needed := residueBound good z.valid.1 (large.trans (Nat.mul_le_mul_left 360360 lower)) pos
    have bad := z.valid.2
    omega

private def tile (p mask : ℕ) : ℕ → ℕ
  | 0 => mask
  | h+1 => let w := tile p mask h
           w ||| (w <<< (p*2^h))

private theorem tileBit {p mask h j : ℕ} (hj : j < p*2^h)
    (hit : mask.testBit (j%p) = true) : (tile p mask h).testBit j = true := by
  induction h generalizing j with
  | zero =>
    have lt : j < p := by simpa using hj
    simpa [tile, Nat.mod_eq_of_lt lt] using hit
  | succ h ih =>
    have twice : p*2^(h+1) = p*2^h + p*2^h := by rw [pow_succ]; ring
    rw [twice] at hj
    rw [tile, Nat.testBit_or, Bool.or_eq_true_iff]
    by_cases first : j < p*2^h
    · exact Or.inl (ih first hit)
    · apply Or.inr
      have lower : p*2^h ≤ j := by omega
      have congr : (j-p*2^h)%p = j%p := by
        calc
          (j-p*2^h)%p = ((j-p*2^h)+p*2^h)%p := by simp [Nat.add_mod]
          _ = j%p := by rw [Nat.sub_add_cancel lower]
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true_iff]
      exact ⟨decide_eq_true lower, ih (by omega) (congr ▸ hit)⟩

private def blockWord (c : Column) (a : ℕ) : ℕ :=
  (tile c.period c.mask c.height) >>> (a%c.period)

private theorem wordAllows (c : Column) {a i : ℕ} (hi : i < 1000000) (ha : 64 ≤ a)
    (good : Good (360360*(a+i))) : (blockWord c a).testBit i = true := by
  rw [blockWord, Nat.testBit_shiftRight]
  have small := Nat.mod_lt a c.positive
  have cap := c.capacity
  apply tileBit (by omega)
  rw [Nat.mod_add_mod]
  exact c.allows _ (by omega) good

private def intersection (a width : ℕ) : List Column → ℕ
  | [] => (1 <<< width)-1
  | c::cs => blockWord c a &&& intersection a width cs

private theorem intersectionAllows (cs : List Column) {a i width : ℕ}
    (hi : i < width) (hw : width ≤ 1000000) (ha : 64 ≤ a) (good : Good (360360*(a+i))) :
    (intersection a width cs).testBit i = true := by
  induction cs with
  | nil => simpa [intersection, Nat.one_shiftLeft] using hi
  | cons c cs ih =>
    exact (Nat.testBit_and _ _ _).trans (Bool.and_eq_true_iff.mpr
      ⟨wordAllows c (by omega) ha good, ih⟩)

private structure Witness (a : ℕ) where
  offset : ℕ
  excludes : Good (360360*(a+offset)) → False

private def sparse {a : ℕ} : List (Witness a) → ℕ
  | [] => 0
  | row::rows => (1 <<< row.offset) ||| sparse rows

private theorem sparseExcludes {a i : ℕ} (rows : List (Witness a))
    (good : Good (360360*(a+i))) (h : (sparse rows).testBit i = true) : False := by
  induction rows with
  | nil => simp [sparse] at h
  | cons row rows ih =>
    rw [sparse, Nat.testBit_or, Bool.or_eq_true_iff, Nat.one_shiftLeft, Nat.testBit_two_pow] at h
    rcases h with eq | rest
    · have eqn := of_decide_eq_true eq
      exact row.excludes (eqn ▸ good)
    · exact ih rest

private theorem witnessRule {n d r : ℕ} (cert : 0 < d ∧ r+2 < 2*σ 0 d)
    (fits : d*d+d ≤ n ∧ 0 < n%d ∧ n%d ≤ r) (good : Good n) : False := by
  obtain ⟨large, pos, small⟩ := fits
  have need := residueBound good cert.1 large pos
  have bad := cert.2
  omega

private theorem witnessDivisors (n k : ℕ) (ds : List ℕ) (hk : 0 < k ∧ k < n)
    (hs : ds.all (fun d => (n-k)%d == 0) = true) (hd : ds.Nodup)
    (hl : k+3 ≤ ds.length) (good : Good n) : False := by
  have incl : ds.toFinset ⊆ (n-k).divisors := by
    intro d h
    have val := List.all_eq_true.mp hs d (List.mem_toFinset.mp h)
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp val), by omega⟩
  have card := Finset.card_le_card incl
  rw [List.toFinset_card_of_nodup hd, ← ArithmeticFunction.sigma_zero_apply] at card
  have bound := good (n-k) (by omega)
  omega

private theorem excludeBlock (cs : List Column) {a width : ℕ} (rows : List (Witness a))
    (hw : width ≤ 1000000) (ha : 64 ≤ a) (certificate : intersection a width cs = sparse rows)
    (i : ℕ) (hi : i < width) (good : Good (360360*(a+i))) : False := by
  have bit := intersectionAllows cs hi hw ha good
  exact sparseExcludes rows good (certificate ▸ bit)



private theorem valid_17 : 0 < 17 ∧ 1+2 < 2*σ 0 17 :=
  checkRule 17 1 [1,17]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_19 : 0 < 19 ∧ 1+2 < 2*σ 0 19 :=
  checkRule 19 1 [1,19]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_23 : 0 < 23 ∧ 1+2 < 2*σ 0 23 :=
  checkRule 23 1 [1,23]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_37 : 0 < 37 ∧ 1+2 < 2*σ 0 37 :=
  checkRule 37 1 [1,37]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_41 : 0 < 41 ∧ 1+2 < 2*σ 0 41 :=
  checkRule 41 1 [1,41]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_53 : 0 < 53 ∧ 1+2 < 2*σ 0 53 :=
  checkRule 53 1 [1,53]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_59 : 0 < 59 ∧ 1+2 < 2*σ 0 59 :=
  checkRule 59 1 [1,59]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_61 : 0 < 61 ∧ 1+2 < 2*σ 0 61 :=
  checkRule 61 1 [1,61]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_64 : 0 < 64 ∧ 11+2 < 2*σ 0 64 :=
  checkRule 64 11 [1,2,4,8,16,32,64]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_67 : 0 < 67 ∧ 1+2 < 2*σ 0 67 :=
  checkRule 67 1 [1,67]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_71 : 0 < 71 ∧ 1+2 < 2*σ 0 71 :=
  checkRule 71 1 [1,71]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_79 : 0 < 79 ∧ 1+2 < 2*σ 0 79 :=
  checkRule 79 1 [1,79]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_83 : 0 < 83 ∧ 1+2 < 2*σ 0 83 :=
  checkRule 83 1 [1,83]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_89 : 0 < 89 ∧ 1+2 < 2*σ 0 89 :=
  checkRule 89 1 [1,89]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_95 : 0 < 95 ∧ 5+2 < 2*σ 0 95 :=
  checkRule 95 5 [1,5,19,95]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_97 : 0 < 97 ∧ 1+2 < 2*σ 0 97 :=
  checkRule 97 1 [1,97]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_101 : 0 < 101 ∧ 1+2 < 2*σ 0 101 :=
  checkRule 101 1 [1,101]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_103 : 0 < 103 ∧ 1+2 < 2*σ 0 103 :=
  checkRule 103 1 [1,103]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_107 : 0 < 107 ∧ 1+2 < 2*σ 0 107 :=
  checkRule 107 1 [1,107]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_109 : 0 < 109 ∧ 1+2 < 2*σ 0 109 :=
  checkRule 109 1 [1,109]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_113 : 0 < 113 ∧ 1+2 < 2*σ 0 113 :=
  checkRule 113 1 [1,113]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_127 : 0 < 127 ∧ 1+2 < 2*σ 0 127 :=
  checkRule 127 1 [1,127]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_128 : 0 < 128 ∧ 13+2 < 2*σ 0 128 :=
  checkRule 128 13 [1,2,4,8,16,32,64,128]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_131 : 0 < 131 ∧ 1+2 < 2*σ 0 131 :=
  checkRule 131 1 [1,131]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_137 : 0 < 137 ∧ 1+2 < 2*σ 0 137 :=
  checkRule 137 1 [1,137]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_139 : 0 < 139 ∧ 1+2 < 2*σ 0 139 :=
  checkRule 139 1 [1,139]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_146 : 0 < 146 ∧ 5+2 < 2*σ 0 146 :=
  checkRule 146 5 [1,2,73,146]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_149 : 0 < 149 ∧ 1+2 < 2*σ 0 149 :=
  checkRule 149 1 [1,149]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_151 : 0 < 151 ∧ 1+2 < 2*σ 0 151 :=
  checkRule 151 1 [1,151]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_157 : 0 < 157 ∧ 1+2 < 2*σ 0 157 :=
  checkRule 157 1 [1,157]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_159 : 0 < 159 ∧ 5+2 < 2*σ 0 159 :=
  checkRule 159 5 [1,3,53,159]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_163 : 0 < 163 ∧ 1+2 < 2*σ 0 163 :=
  checkRule 163 1 [1,163]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_166 : 0 < 166 ∧ 5+2 < 2*σ 0 166 :=
  checkRule 166 5 [1,2,83,166]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_167 : 0 < 167 ∧ 1+2 < 2*σ 0 167 :=
  checkRule 167 1 [1,167]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_173 : 0 < 173 ∧ 1+2 < 2*σ 0 173 :=
  checkRule 173 1 [1,173]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_178 : 0 < 178 ∧ 5+2 < 2*σ 0 178 :=
  checkRule 178 5 [1,2,89,178]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_179 : 0 < 179 ∧ 1+2 < 2*σ 0 179 :=
  checkRule 179 1 [1,179]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_181 : 0 < 181 ∧ 1+2 < 2*σ 0 181 :=
  checkRule 181 1 [1,181]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_183 : 0 < 183 ∧ 5+2 < 2*σ 0 183 :=
  checkRule 183 5 [1,3,61,183]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_185 : 0 < 185 ∧ 5+2 < 2*σ 0 185 :=
  checkRule 185 5 [1,5,37,185]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_191 : 0 < 191 ∧ 1+2 < 2*σ 0 191 :=
  checkRule 191 1 [1,191]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_193 : 0 < 193 ∧ 1+2 < 2*σ 0 193 :=
  checkRule 193 1 [1,193]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_194 : 0 < 194 ∧ 5+2 < 2*σ 0 194 :=
  checkRule 194 5 [1,2,97,194]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_197 : 0 < 197 ∧ 1+2 < 2*σ 0 197 :=
  checkRule 197 1 [1,197]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_199 : 0 < 199 ∧ 1+2 < 2*σ 0 199 :=
  checkRule 199 1 [1,199]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_201 : 0 < 201 ∧ 5+2 < 2*σ 0 201 :=
  checkRule 201 5 [1,3,67,201]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_202 : 0 < 202 ∧ 5+2 < 2*σ 0 202 :=
  checkRule 202 5 [1,2,101,202]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_205 : 0 < 205 ∧ 5+2 < 2*σ 0 205 :=
  checkRule 205 5 [1,5,41,205]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_206 : 0 < 206 ∧ 5+2 < 2*σ 0 206 :=
  checkRule 206 5 [1,2,103,206]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_211 : 0 < 211 ∧ 1+2 < 2*σ 0 211 :=
  checkRule 211 1 [1,211]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_213 : 0 < 213 ∧ 5+2 < 2*σ 0 213 :=
  checkRule 213 5 [1,3,71,213]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_214 : 0 < 214 ∧ 5+2 < 2*σ 0 214 :=
  checkRule 214 5 [1,2,107,214]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_215 : 0 < 215 ∧ 5+2 < 2*σ 0 215 :=
  checkRule 215 5 [1,5,43,215]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_219 : 0 < 219 ∧ 5+2 < 2*σ 0 219 :=
  checkRule 219 5 [1,3,73,219]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_223 : 0 < 223 ∧ 1+2 < 2*σ 0 223 :=
  checkRule 223 1 [1,223]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_226 : 0 < 226 ∧ 5+2 < 2*σ 0 226 :=
  checkRule 226 5 [1,2,113,226]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_227 : 0 < 227 ∧ 1+2 < 2*σ 0 227 :=
  checkRule 227 1 [1,227]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_229 : 0 < 229 ∧ 1+2 < 2*σ 0 229 :=
  checkRule 229 1 [1,229]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_233 : 0 < 233 ∧ 1+2 < 2*σ 0 233 :=
  checkRule 233 1 [1,233]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_237 : 0 < 237 ∧ 5+2 < 2*σ 0 237 :=
  checkRule 237 5 [1,3,79,237]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_239 : 0 < 239 ∧ 1+2 < 2*σ 0 239 :=
  checkRule 239 1 [1,239]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_241 : 0 < 241 ∧ 1+2 < 2*σ 0 241 :=
  checkRule 241 1 [1,241]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_249 : 0 < 249 ∧ 5+2 < 2*σ 0 249 :=
  checkRule 249 5 [1,3,83,249]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_251 : 0 < 251 ∧ 1+2 < 2*σ 0 251 :=
  checkRule 251 1 [1,251]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_254 : 0 < 254 ∧ 5+2 < 2*σ 0 254 :=
  checkRule 254 5 [1,2,127,254]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_256 : 0 < 256 ∧ 15+2 < 2*σ 0 256 :=
  checkRule 256 15 [1,2,4,8,16,32,64,128,256]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_257 : 0 < 257 ∧ 1+2 < 2*σ 0 257 :=
  checkRule 257 1 [1,257]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_262 : 0 < 262 ∧ 5+2 < 2*σ 0 262 :=
  checkRule 262 5 [1,2,131,262]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_263 : 0 < 263 ∧ 1+2 < 2*σ 0 263 :=
  checkRule 263 1 [1,263]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_265 : 0 < 265 ∧ 5+2 < 2*σ 0 265 :=
  checkRule 265 5 [1,5,53,265]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_267 : 0 < 267 ∧ 5+2 < 2*σ 0 267 :=
  checkRule 267 5 [1,3,89,267]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_269 : 0 < 269 ∧ 1+2 < 2*σ 0 269 :=
  checkRule 269 1 [1,269]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_271 : 0 < 271 ∧ 1+2 < 2*σ 0 271 :=
  checkRule 271 1 [1,271]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_274 : 0 < 274 ∧ 5+2 < 2*σ 0 274 :=
  checkRule 274 5 [1,2,137,274]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_277 : 0 < 277 ∧ 1+2 < 2*σ 0 277 :=
  checkRule 277 1 [1,277]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_278 : 0 < 278 ∧ 5+2 < 2*σ 0 278 :=
  checkRule 278 5 [1,2,139,278]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_281 : 0 < 281 ∧ 1+2 < 2*σ 0 281 :=
  checkRule 281 1 [1,281]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_283 : 0 < 283 ∧ 1+2 < 2*σ 0 283 :=
  checkRule 283 1 [1,283]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_284 : 0 < 284 ∧ 9+2 < 2*σ 0 284 :=
  checkRule 284 9 [1,2,4,71,142,284]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_289 : 0 < 289 ∧ 3+2 < 2*σ 0 289 :=
  checkRule 289 3 [1,17,289]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_291 : 0 < 291 ∧ 5+2 < 2*σ 0 291 :=
  checkRule 291 5 [1,3,97,291]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_292 : 0 < 292 ∧ 9+2 < 2*σ 0 292 :=
  checkRule 292 9 [1,2,4,73,146,292]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_293 : 0 < 293 ∧ 1+2 < 2*σ 0 293 :=
  checkRule 293 1 [1,293]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_295 : 0 < 295 ∧ 5+2 < 2*σ 0 295 :=
  checkRule 295 5 [1,5,59,295]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_298 : 0 < 298 ∧ 5+2 < 2*σ 0 298 :=
  checkRule 298 5 [1,2,149,298]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_302 : 0 < 302 ∧ 5+2 < 2*σ 0 302 :=
  checkRule 302 5 [1,2,151,302]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_303 : 0 < 303 ∧ 5+2 < 2*σ 0 303 :=
  checkRule 303 5 [1,3,101,303]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_307 : 0 < 307 ∧ 1+2 < 2*σ 0 307 :=
  checkRule 307 1 [1,307]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_309 : 0 < 309 ∧ 5+2 < 2*σ 0 309 :=
  checkRule 309 5 [1,3,103,309]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_311 : 0 < 311 ∧ 1+2 < 2*σ 0 311 :=
  checkRule 311 1 [1,311]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_313 : 0 < 313 ∧ 1+2 < 2*σ 0 313 :=
  checkRule 313 1 [1,313]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_314 : 0 < 314 ∧ 5+2 < 2*σ 0 314 :=
  checkRule 314 5 [1,2,157,314]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_316 : 0 < 316 ∧ 9+2 < 2*σ 0 316 :=
  checkRule 316 9 [1,2,4,79,158,316]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_317 : 0 < 317 ∧ 1+2 < 2*σ 0 317 :=
  checkRule 317 1 [1,317]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_321 : 0 < 321 ∧ 5+2 < 2*σ 0 321 :=
  checkRule 321 5 [1,3,107,321]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_323 : 0 < 323 ∧ 5+2 < 2*σ 0 323 :=
  checkRule 323 5 [1,17,19,323]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_326 : 0 < 326 ∧ 5+2 < 2*σ 0 326 :=
  checkRule 326 5 [1,2,163,326]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_327 : 0 < 327 ∧ 5+2 < 2*σ 0 327 :=
  checkRule 327 5 [1,3,109,327]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_331 : 0 < 331 ∧ 1+2 < 2*σ 0 331 :=
  checkRule 331 1 [1,331]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_332 : 0 < 332 ∧ 9+2 < 2*σ 0 332 :=
  checkRule 332 9 [1,2,4,83,166,332]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_334 : 0 < 334 ∧ 5+2 < 2*σ 0 334 :=
  checkRule 334 5 [1,2,167,334]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_335 : 0 < 335 ∧ 5+2 < 2*σ 0 335 :=
  checkRule 335 5 [1,5,67,335]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_337 : 0 < 337 ∧ 1+2 < 2*σ 0 337 :=
  checkRule 337 1 [1,337]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_339 : 0 < 339 ∧ 5+2 < 2*σ 0 339 :=
  checkRule 339 5 [1,3,113,339]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_347 : 0 < 347 ∧ 1+2 < 2*σ 0 347 :=
  checkRule 347 1 [1,347]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_349 : 0 < 349 ∧ 1+2 < 2*σ 0 349 :=
  checkRule 349 1 [1,349]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_353 : 0 < 353 ∧ 1+2 < 2*σ 0 353 :=
  checkRule 353 1 [1,353]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_355 : 0 < 355 ∧ 5+2 < 2*σ 0 355 :=
  checkRule 355 5 [1,5,71,355]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_356 : 0 < 356 ∧ 9+2 < 2*σ 0 356 :=
  checkRule 356 9 [1,2,4,89,178,356]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_358 : 0 < 358 ∧ 5+2 < 2*σ 0 358 :=
  checkRule 358 5 [1,2,179,358]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_359 : 0 < 359 ∧ 1+2 < 2*σ 0 359 :=
  checkRule 359 1 [1,359]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_361 : 0 < 361 ∧ 3+2 < 2*σ 0 361 :=
  checkRule 361 3 [1,19,361]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_362 : 0 < 362 ∧ 5+2 < 2*σ 0 362 :=
  checkRule 362 5 [1,2,181,362]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_365 : 0 < 365 ∧ 5+2 < 2*σ 0 365 :=
  checkRule 365 5 [1,5,73,365]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_367 : 0 < 367 ∧ 1+2 < 2*σ 0 367 :=
  checkRule 367 1 [1,367]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_369 : 0 < 369 ∧ 9+2 < 2*σ 0 369 :=
  checkRule 369 9 [1,3,9,41,123,369]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_373 : 0 < 373 ∧ 1+2 < 2*σ 0 373 :=
  checkRule 373 1 [1,373]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_379 : 0 < 379 ∧ 1+2 < 2*σ 0 379 :=
  checkRule 379 1 [1,379]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_381 : 0 < 381 ∧ 5+2 < 2*σ 0 381 :=
  checkRule 381 5 [1,3,127,381]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_382 : 0 < 382 ∧ 5+2 < 2*σ 0 382 :=
  checkRule 382 5 [1,2,191,382]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_384 : 0 < 384 ∧ 29+2 < 2*σ 0 384 :=
  checkRule 384 29 [1,2,3,4,6,8,12,16,24,32,48,64,96,128,192,384]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_386 : 0 < 386 ∧ 5+2 < 2*σ 0 386 :=
  checkRule 386 5 [1,2,193,386]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_387 : 0 < 387 ∧ 9+2 < 2*σ 0 387 :=
  checkRule 387 9 [1,3,9,43,129,387]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_389 : 0 < 389 ∧ 1+2 < 2*σ 0 389 :=
  checkRule 389 1 [1,389]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_391 : 0 < 391 ∧ 5+2 < 2*σ 0 391 :=
  checkRule 391 5 [1,17,23,391]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_393 : 0 < 393 ∧ 5+2 < 2*σ 0 393 :=
  checkRule 393 5 [1,3,131,393]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_394 : 0 < 394 ∧ 5+2 < 2*σ 0 394 :=
  checkRule 394 5 [1,2,197,394]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_395 : 0 < 395 ∧ 5+2 < 2*σ 0 395 :=
  checkRule 395 5 [1,5,79,395]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_397 : 0 < 397 ∧ 1+2 < 2*σ 0 397 :=
  checkRule 397 1 [1,397]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_398 : 0 < 398 ∧ 5+2 < 2*σ 0 398 :=
  checkRule 398 5 [1,2,199,398]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_401 : 0 < 401 ∧ 1+2 < 2*σ 0 401 :=
  checkRule 401 1 [1,401]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_404 : 0 < 404 ∧ 9+2 < 2*σ 0 404 :=
  checkRule 404 9 [1,2,4,101,202,404]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_409 : 0 < 409 ∧ 1+2 < 2*σ 0 409 :=
  checkRule 409 1 [1,409]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_410 : 0 < 410 ∧ 13+2 < 2*σ 0 410 :=
  checkRule 410 13 [1,2,5,10,41,82,205,410]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_411 : 0 < 411 ∧ 5+2 < 2*σ 0 411 :=
  checkRule 411 5 [1,3,137,411]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_412 : 0 < 412 ∧ 9+2 < 2*σ 0 412 :=
  checkRule 412 9 [1,2,4,103,206,412]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_415 : 0 < 415 ∧ 5+2 < 2*σ 0 415 :=
  checkRule 415 5 [1,5,83,415]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_417 : 0 < 417 ∧ 5+2 < 2*σ 0 417 :=
  checkRule 417 5 [1,3,139,417]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_419 : 0 < 419 ∧ 1+2 < 2*σ 0 419 :=
  checkRule 419 1 [1,419]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_421 : 0 < 421 ∧ 1+2 < 2*σ 0 421 :=
  checkRule 421 1 [1,421]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_422 : 0 < 422 ∧ 5+2 < 2*σ 0 422 :=
  checkRule 422 5 [1,2,211,422]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_425 : 0 < 425 ∧ 9+2 < 2*σ 0 425 :=
  checkRule 425 9 [1,5,17,25,85,425]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_426 : 0 < 426 ∧ 13+2 < 2*σ 0 426 :=
  checkRule 426 13 [1,2,3,6,71,142,213,426]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_428 : 0 < 428 ∧ 9+2 < 2*σ 0 428 :=
  checkRule 428 9 [1,2,4,107,214,428]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_430 : 0 < 430 ∧ 13+2 < 2*σ 0 430 :=
  checkRule 430 13 [1,2,5,10,43,86,215,430]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_431 : 0 < 431 ∧ 1+2 < 2*σ 0 431 :=
  checkRule 431 1 [1,431]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_433 : 0 < 433 ∧ 1+2 < 2*σ 0 433 :=
  checkRule 433 1 [1,433]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_436 : 0 < 436 ∧ 9+2 < 2*σ 0 436 :=
  checkRule 436 9 [1,2,4,109,218,436]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_437 : 0 < 437 ∧ 5+2 < 2*σ 0 437 :=
  checkRule 437 5 [1,19,23,437]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_438 : 0 < 438 ∧ 13+2 < 2*σ 0 438 :=
  checkRule 438 13 [1,2,3,6,73,146,219,438]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_439 : 0 < 439 ∧ 1+2 < 2*σ 0 439 :=
  checkRule 439 1 [1,439]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_443 : 0 < 443 ∧ 1+2 < 2*σ 0 443 :=
  checkRule 443 1 [1,443]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_445 : 0 < 445 ∧ 5+2 < 2*σ 0 445 :=
  checkRule 445 5 [1,5,89,445]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_446 : 0 < 446 ∧ 5+2 < 2*σ 0 446 :=
  checkRule 446 5 [1,2,223,446]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_447 : 0 < 447 ∧ 5+2 < 2*σ 0 447 :=
  checkRule 447 5 [1,3,149,447]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_452 : 0 < 452 ∧ 9+2 < 2*σ 0 452 :=
  checkRule 452 9 [1,2,4,113,226,452]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_453 : 0 < 453 ∧ 5+2 < 2*σ 0 453 :=
  checkRule 453 5 [1,3,151,453]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_454 : 0 < 454 ∧ 5+2 < 2*σ 0 454 :=
  checkRule 454 5 [1,2,227,454]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_457 : 0 < 457 ∧ 1+2 < 2*σ 0 457 :=
  checkRule 457 1 [1,457]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_458 : 0 < 458 ∧ 5+2 < 2*σ 0 458 :=
  checkRule 458 5 [1,2,229,458]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_459 : 0 < 459 ∧ 13+2 < 2*σ 0 459 :=
  checkRule 459 13 [1,3,9,17,27,51,153,459]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_463 : 0 < 463 ∧ 1+2 < 2*σ 0 463 :=
  checkRule 463 1 [1,463]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_466 : 0 < 466 ∧ 5+2 < 2*σ 0 466 :=
  checkRule 466 5 [1,2,233,466]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_467 : 0 < 467 ∧ 1+2 < 2*σ 0 467 :=
  checkRule 467 1 [1,467]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_470 : 0 < 470 ∧ 13+2 < 2*σ 0 470 :=
  checkRule 470 13 [1,2,5,10,47,94,235,470]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_471 : 0 < 471 ∧ 5+2 < 2*σ 0 471 :=
  checkRule 471 5 [1,3,157,471]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_474 : 0 < 474 ∧ 13+2 < 2*σ 0 474 :=
  checkRule 474 13 [1,2,3,6,79,158,237,474]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_475 : 0 < 475 ∧ 9+2 < 2*σ 0 475 :=
  checkRule 475 9 [1,5,19,25,95,475]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_477 : 0 < 477 ∧ 9+2 < 2*σ 0 477 :=
  checkRule 477 9 [1,3,9,53,159,477]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_478 : 0 < 478 ∧ 5+2 < 2*σ 0 478 :=
  checkRule 478 5 [1,2,239,478]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_479 : 0 < 479 ∧ 1+2 < 2*σ 0 479 :=
  checkRule 479 1 [1,479]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_482 : 0 < 482 ∧ 5+2 < 2*σ 0 482 :=
  checkRule 482 5 [1,2,241,482]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_485 : 0 < 485 ∧ 5+2 < 2*σ 0 485 :=
  checkRule 485 5 [1,5,97,485]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_487 : 0 < 487 ∧ 1+2 < 2*σ 0 487 :=
  checkRule 487 1 [1,487]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_489 : 0 < 489 ∧ 5+2 < 2*σ 0 489 :=
  checkRule 489 5 [1,3,163,489]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_491 : 0 < 491 ∧ 1+2 < 2*σ 0 491 :=
  checkRule 491 1 [1,491]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_493 : 0 < 493 ∧ 5+2 < 2*σ 0 493 :=
  checkRule 493 5 [1,17,29,493]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_498 : 0 < 498 ∧ 13+2 < 2*σ 0 498 :=
  checkRule 498 13 [1,2,3,6,83,166,249,498]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_501 : 0 < 501 ∧ 5+2 < 2*σ 0 501 :=
  checkRule 501 5 [1,3,167,501]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_502 : 0 < 502 ∧ 5+2 < 2*σ 0 502 :=
  checkRule 502 5 [1,2,251,502]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_503 : 0 < 503 ∧ 1+2 < 2*σ 0 503 :=
  checkRule 503 1 [1,503]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_505 : 0 < 505 ∧ 5+2 < 2*σ 0 505 :=
  checkRule 505 5 [1,5,101,505]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_508 : 0 < 508 ∧ 9+2 < 2*σ 0 508 :=
  checkRule 508 9 [1,2,4,127,254,508]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_513 : 0 < 513 ∧ 13+2 < 2*σ 0 513 :=
  checkRule 513 13 [1,3,9,19,27,57,171,513]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_514 : 0 < 514 ∧ 5+2 < 2*σ 0 514 :=
  checkRule 514 5 [1,2,257,514]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_515 : 0 < 515 ∧ 5+2 < 2*σ 0 515 :=
  checkRule 515 5 [1,5,103,515]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_519 : 0 < 519 ∧ 5+2 < 2*σ 0 519 :=
  checkRule 519 5 [1,3,173,519]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_521 : 0 < 521 ∧ 1+2 < 2*σ 0 521 :=
  checkRule 521 1 [1,521]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_523 : 0 < 523 ∧ 1+2 < 2*σ 0 523 :=
  checkRule 523 1 [1,523]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_524 : 0 < 524 ∧ 9+2 < 2*σ 0 524 :=
  checkRule 524 9 [1,2,4,131,262,524]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_526 : 0 < 526 ∧ 5+2 < 2*σ 0 526 :=
  checkRule 526 5 [1,2,263,526]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_531 : 0 < 531 ∧ 9+2 < 2*σ 0 531 :=
  checkRule 531 9 [1,3,9,59,177,531]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_534 : 0 < 534 ∧ 13+2 < 2*σ 0 534 :=
  checkRule 534 13 [1,2,3,6,89,178,267,534]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_535 : 0 < 535 ∧ 5+2 < 2*σ 0 535 :=
  checkRule 535 5 [1,5,107,535]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_537 : 0 < 537 ∧ 5+2 < 2*σ 0 537 :=
  checkRule 537 5 [1,3,179,537]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_538 : 0 < 538 ∧ 5+2 < 2*σ 0 538 :=
  checkRule 538 5 [1,2,269,538]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_541 : 0 < 541 ∧ 1+2 < 2*σ 0 541 :=
  checkRule 541 1 [1,541]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_542 : 0 < 542 ∧ 5+2 < 2*σ 0 542 :=
  checkRule 542 5 [1,2,271,542]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_543 : 0 < 543 ∧ 5+2 < 2*σ 0 543 :=
  checkRule 543 5 [1,3,181,543]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_544 : 0 < 544 ∧ 21+2 < 2*σ 0 544 :=
  checkRule 544 21 [1,2,4,8,16,17,32,34,68,136,272,544]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_545 : 0 < 545 ∧ 5+2 < 2*σ 0 545 :=
  checkRule 545 5 [1,5,109,545]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_547 : 0 < 547 ∧ 1+2 < 2*σ 0 547 :=
  checkRule 547 1 [1,547]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_548 : 0 < 548 ∧ 9+2 < 2*σ 0 548 :=
  checkRule 548 9 [1,2,4,137,274,548]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_549 : 0 < 549 ∧ 9+2 < 2*σ 0 549 :=
  checkRule 549 9 [1,3,9,61,183,549]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_554 : 0 < 554 ∧ 5+2 < 2*σ 0 554 :=
  checkRule 554 5 [1,2,277,554]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_556 : 0 < 556 ∧ 9+2 < 2*σ 0 556 :=
  checkRule 556 9 [1,2,4,139,278,556]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_557 : 0 < 557 ∧ 1+2 < 2*σ 0 557 :=
  checkRule 557 1 [1,557]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_562 : 0 < 562 ∧ 5+2 < 2*σ 0 562 :=
  checkRule 562 5 [1,2,281,562]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_565 : 0 < 565 ∧ 5+2 < 2*σ 0 565 :=
  checkRule 565 5 [1,5,113,565]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_566 : 0 < 566 ∧ 5+2 < 2*σ 0 566 :=
  checkRule 566 5 [1,2,283,566]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_569 : 0 < 569 ∧ 1+2 < 2*σ 0 569 :=
  checkRule 569 1 [1,569]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_571 : 0 < 571 ∧ 1+2 < 2*σ 0 571 :=
  checkRule 571 1 [1,571]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_573 : 0 < 573 ∧ 5+2 < 2*σ 0 573 :=
  checkRule 573 5 [1,3,191,573]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_575 : 0 < 575 ∧ 9+2 < 2*σ 0 575 :=
  checkRule 575 9 [1,5,23,25,115,575]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_577 : 0 < 577 ∧ 1+2 < 2*σ 0 577 :=
  checkRule 577 1 [1,577]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_578 : 0 < 578 ∧ 9+2 < 2*σ 0 578 :=
  checkRule 578 9 [1,2,17,34,289,578]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_579 : 0 < 579 ∧ 5+2 < 2*σ 0 579 :=
  checkRule 579 5 [1,3,193,579]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_582 : 0 < 582 ∧ 13+2 < 2*σ 0 582 :=
  checkRule 582 13 [1,2,3,6,97,194,291,582]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_586 : 0 < 586 ∧ 5+2 < 2*σ 0 586 :=
  checkRule 586 5 [1,2,293,586]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_587 : 0 < 587 ∧ 1+2 < 2*σ 0 587 :=
  checkRule 587 1 [1,587]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_590 : 0 < 590 ∧ 13+2 < 2*σ 0 590 :=
  checkRule 590 13 [1,2,5,10,59,118,295,590]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_591 : 0 < 591 ∧ 5+2 < 2*σ 0 591 :=
  checkRule 591 5 [1,3,197,591]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_592 : 0 < 592 ∧ 17+2 < 2*σ 0 592 :=
  checkRule 592 17 [1,2,4,8,16,37,74,148,296,592]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_596 : 0 < 596 ∧ 9+2 < 2*σ 0 596 :=
  checkRule 596 9 [1,2,4,149,298,596]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_597 : 0 < 597 ∧ 5+2 < 2*σ 0 597 :=
  checkRule 597 5 [1,3,199,597]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_599 : 0 < 599 ∧ 1+2 < 2*σ 0 599 :=
  checkRule 599 1 [1,599]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_603 : 0 < 603 ∧ 9+2 < 2*σ 0 603 :=
  checkRule 603 9 [1,3,9,67,201,603]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_604 : 0 < 604 ∧ 9+2 < 2*σ 0 604 :=
  checkRule 604 9 [1,2,4,151,302,604]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_606 : 0 < 606 ∧ 13+2 < 2*σ 0 606 :=
  checkRule 606 13 [1,2,3,6,101,202,303,606]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_607 : 0 < 607 ∧ 1+2 < 2*σ 0 607 :=
  checkRule 607 1 [1,607]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_608 : 0 < 608 ∧ 21+2 < 2*σ 0 608 :=
  checkRule 608 21 [1,2,4,8,16,19,32,38,76,152,304,608]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_610 : 0 < 610 ∧ 13+2 < 2*σ 0 610 :=
  checkRule 610 13 [1,2,5,10,61,122,305,610]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_614 : 0 < 614 ∧ 5+2 < 2*σ 0 614 :=
  checkRule 614 5 [1,2,307,614]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_617 : 0 < 617 ∧ 1+2 < 2*σ 0 617 :=
  checkRule 617 1 [1,617]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_618 : 0 < 618 ∧ 13+2 < 2*σ 0 618 :=
  checkRule 618 13 [1,2,3,6,103,206,309,618]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_619 : 0 < 619 ∧ 1+2 < 2*σ 0 619 :=
  checkRule 619 1 [1,619]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_620 : 0 < 620 ∧ 21+2 < 2*σ 0 620 :=
  checkRule 620 21 [1,2,4,5,10,20,31,62,124,155,310,620]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_621 : 0 < 621 ∧ 13+2 < 2*σ 0 621 :=
  checkRule 621 13 [1,3,9,23,27,69,207,621]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_622 : 0 < 622 ∧ 5+2 < 2*σ 0 622 :=
  checkRule 622 5 [1,2,311,622]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_625 : 0 < 625 ∧ 7+2 < 2*σ 0 625 :=
  checkRule 625 7 [1,5,25,125,625]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_626 : 0 < 626 ∧ 5+2 < 2*σ 0 626 :=
  checkRule 626 5 [1,2,313,626]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_628 : 0 < 628 ∧ 9+2 < 2*σ 0 628 :=
  checkRule 628 9 [1,2,4,157,314,628]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_633 : 0 < 633 ∧ 5+2 < 2*σ 0 633 :=
  checkRule 633 5 [1,3,211,633]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_634 : 0 < 634 ∧ 5+2 < 2*σ 0 634 :=
  checkRule 634 5 [1,2,317,634]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_635 : 0 < 635 ∧ 5+2 < 2*σ 0 635 :=
  checkRule 635 5 [1,5,127,635]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_639 : 0 < 639 ∧ 9+2 < 2*σ 0 639 :=
  checkRule 639 9 [1,3,9,71,213,639]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_641 : 0 < 641 ∧ 1+2 < 2*σ 0 641 :=
  checkRule 641 1 [1,641]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_642 : 0 < 642 ∧ 13+2 < 2*σ 0 642 :=
  checkRule 642 13 [1,2,3,6,107,214,321,642]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_643 : 0 < 643 ∧ 1+2 < 2*σ 0 643 :=
  checkRule 643 1 [1,643]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_646 : 0 < 646 ∧ 13+2 < 2*σ 0 646 :=
  checkRule 646 13 [1,2,17,19,34,38,323,646]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_653 : 0 < 653 ∧ 1+2 < 2*σ 0 653 :=
  checkRule 653 1 [1,653]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_654 : 0 < 654 ∧ 13+2 < 2*σ 0 654 :=
  checkRule 654 13 [1,2,3,6,109,218,327,654]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_655 : 0 < 655 ∧ 5+2 < 2*σ 0 655 :=
  checkRule 655 5 [1,5,131,655]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_656 : 0 < 656 ∧ 17+2 < 2*σ 0 656 :=
  checkRule 656 17 [1,2,4,8,16,41,82,164,328,656]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_657 : 0 < 657 ∧ 9+2 < 2*σ 0 657 :=
  checkRule 657 9 [1,3,9,73,219,657]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_659 : 0 < 659 ∧ 1+2 < 2*σ 0 659 :=
  checkRule 659 1 [1,659]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_662 : 0 < 662 ∧ 5+2 < 2*σ 0 662 :=
  checkRule 662 5 [1,2,331,662]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_666 : 0 < 666 ∧ 21+2 < 2*σ 0 666 :=
  checkRule 666 21 [1,2,3,6,9,18,37,74,111,222,333,666]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_668 : 0 < 668 ∧ 9+2 < 2*σ 0 668 :=
  checkRule 668 9 [1,2,4,167,334,668]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_669 : 0 < 669 ∧ 5+2 < 2*σ 0 669 :=
  checkRule 669 5 [1,3,223,669]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_670 : 0 < 670 ∧ 13+2 < 2*σ 0 670 :=
  checkRule 670 13 [1,2,5,10,67,134,335,670]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_673 : 0 < 673 ∧ 1+2 < 2*σ 0 673 :=
  checkRule 673 1 [1,673]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_677 : 0 < 677 ∧ 1+2 < 2*σ 0 677 :=
  checkRule 677 1 [1,677]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_681 : 0 < 681 ∧ 5+2 < 2*σ 0 681 :=
  checkRule 681 5 [1,3,227,681]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_685 : 0 < 685 ∧ 5+2 < 2*σ 0 685 :=
  checkRule 685 5 [1,5,137,685]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_687 : 0 < 687 ∧ 5+2 < 2*σ 0 687 :=
  checkRule 687 5 [1,3,229,687]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_688 : 0 < 688 ∧ 17+2 < 2*σ 0 688 :=
  checkRule 688 17 [1,2,4,8,16,43,86,172,344,688]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_691 : 0 < 691 ∧ 1+2 < 2*σ 0 691 :=
  checkRule 691 1 [1,691]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_692 : 0 < 692 ∧ 9+2 < 2*σ 0 692 :=
  checkRule 692 9 [1,2,4,173,346,692]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_694 : 0 < 694 ∧ 5+2 < 2*σ 0 694 :=
  checkRule 694 5 [1,2,347,694]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_695 : 0 < 695 ∧ 5+2 < 2*σ 0 695 :=
  checkRule 695 5 [1,5,139,695]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_698 : 0 < 698 ∧ 5+2 < 2*σ 0 698 :=
  checkRule 698 5 [1,2,349,698]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_699 : 0 < 699 ∧ 5+2 < 2*σ 0 699 :=
  checkRule 699 5 [1,3,233,699]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_701 : 0 < 701 ∧ 1+2 < 2*σ 0 701 :=
  checkRule 701 1 [1,701]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_706 : 0 < 706 ∧ 5+2 < 2*σ 0 706 :=
  checkRule 706 5 [1,2,353,706]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_710 : 0 < 710 ∧ 13+2 < 2*σ 0 710 :=
  checkRule 710 13 [1,2,5,10,71,142,355,710]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_711 : 0 < 711 ∧ 9+2 < 2*σ 0 711 :=
  checkRule 711 9 [1,3,9,79,237,711]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_716 : 0 < 716 ∧ 9+2 < 2*σ 0 716 :=
  checkRule 716 9 [1,2,4,179,358,716]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_717 : 0 < 717 ∧ 5+2 < 2*σ 0 717 :=
  checkRule 717 5 [1,3,239,717]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_718 : 0 < 718 ∧ 5+2 < 2*σ 0 718 :=
  checkRule 718 5 [1,2,359,718]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_722 : 0 < 722 ∧ 9+2 < 2*σ 0 722 :=
  checkRule 722 9 [1,2,19,38,361,722]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_723 : 0 < 723 ∧ 5+2 < 2*σ 0 723 :=
  checkRule 723 5 [1,3,241,723]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_724 : 0 < 724 ∧ 9+2 < 2*σ 0 724 :=
  checkRule 724 9 [1,2,4,181,362,724]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_729 : 0 < 729 ∧ 11+2 < 2*σ 0 729 :=
  checkRule 729 11 [1,3,9,27,81,243,729]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_730 : 0 < 730 ∧ 13+2 < 2*σ 0 730 :=
  checkRule 730 13 [1,2,5,10,73,146,365,730]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_733 : 0 < 733 ∧ 1+2 < 2*σ 0 733 :=
  checkRule 733 1 [1,733]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_734 : 0 < 734 ∧ 5+2 < 2*σ 0 734 :=
  checkRule 734 5 [1,2,367,734]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_736 : 0 < 736 ∧ 21+2 < 2*σ 0 736 :=
  checkRule 736 21 [1,2,4,8,16,23,32,46,92,184,368,736]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_738 : 0 < 738 ∧ 21+2 < 2*σ 0 738 :=
  checkRule 738 21 [1,2,3,6,9,18,41,82,123,246,369,738]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_743 : 0 < 743 ∧ 1+2 < 2*σ 0 743 :=
  checkRule 743 1 [1,743]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_745 : 0 < 745 ∧ 5+2 < 2*σ 0 745 :=
  checkRule 745 5 [1,5,149,745]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_746 : 0 < 746 ∧ 5+2 < 2*σ 0 746 :=
  checkRule 746 5 [1,2,373,746]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_747 : 0 < 747 ∧ 9+2 < 2*σ 0 747 :=
  checkRule 747 9 [1,3,9,83,249,747]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_751 : 0 < 751 ∧ 1+2 < 2*σ 0 751 :=
  checkRule 751 1 [1,751]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_752 : 0 < 752 ∧ 17+2 < 2*σ 0 752 :=
  checkRule 752 17 [1,2,4,8,16,47,94,188,376,752]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_753 : 0 < 753 ∧ 5+2 < 2*σ 0 753 :=
  checkRule 753 5 [1,3,251,753]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_755 : 0 < 755 ∧ 5+2 < 2*σ 0 755 :=
  checkRule 755 5 [1,5,151,755]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_757 : 0 < 757 ∧ 1+2 < 2*σ 0 757 :=
  checkRule 757 1 [1,757]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_758 : 0 < 758 ∧ 5+2 < 2*σ 0 758 :=
  checkRule 758 5 [1,2,379,758]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_761 : 0 < 761 ∧ 1+2 < 2*σ 0 761 :=
  checkRule 761 1 [1,761]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_762 : 0 < 762 ∧ 13+2 < 2*σ 0 762 :=
  checkRule 762 13 [1,2,3,6,127,254,381,762]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_764 : 0 < 764 ∧ 9+2 < 2*σ 0 764 :=
  checkRule 764 9 [1,2,4,191,382,764]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_766 : 0 < 766 ∧ 5+2 < 2*σ 0 766 :=
  checkRule 766 5 [1,2,383,766]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_768 : 0 < 768 ∧ 33+2 < 2*σ 0 768 :=
  checkRule 768 33 [1,2,3,4,6,8,12,16,24,32,48,64,96,128,192,256,384,768]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_771 : 0 < 771 ∧ 5+2 < 2*σ 0 771 :=
  checkRule 771 5 [1,3,257,771]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_772 : 0 < 772 ∧ 9+2 < 2*σ 0 772 :=
  checkRule 772 9 [1,2,4,193,386,772]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_773 : 0 < 773 ∧ 1+2 < 2*σ 0 773 :=
  checkRule 773 1 [1,773]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_774 : 0 < 774 ∧ 21+2 < 2*σ 0 774 :=
  checkRule 774 21 [1,2,3,6,9,18,43,86,129,258,387,774]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_778 : 0 < 778 ∧ 5+2 < 2*σ 0 778 :=
  checkRule 778 5 [1,2,389,778]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_782 : 0 < 782 ∧ 13+2 < 2*σ 0 782 :=
  checkRule 782 13 [1,2,17,23,34,46,391,782]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_783 : 0 < 783 ∧ 13+2 < 2*σ 0 783 :=
  checkRule 783 13 [1,3,9,27,29,87,261,783]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_785 : 0 < 785 ∧ 5+2 < 2*σ 0 785 :=
  checkRule 785 5 [1,5,157,785]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_786 : 0 < 786 ∧ 13+2 < 2*σ 0 786 :=
  checkRule 786 13 [1,2,3,6,131,262,393,786]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_788 : 0 < 788 ∧ 9+2 < 2*σ 0 788 :=
  checkRule 788 9 [1,2,4,197,394,788]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_789 : 0 < 789 ∧ 5+2 < 2*σ 0 789 :=
  checkRule 789 5 [1,3,263,789]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_790 : 0 < 790 ∧ 13+2 < 2*σ 0 790 :=
  checkRule 790 13 [1,2,5,10,79,158,395,790]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_794 : 0 < 794 ∧ 5+2 < 2*σ 0 794 :=
  checkRule 794 5 [1,2,397,794]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_796 : 0 < 796 ∧ 9+2 < 2*σ 0 796 :=
  checkRule 796 9 [1,2,4,199,398,796]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_801 : 0 < 801 ∧ 9+2 < 2*σ 0 801 :=
  checkRule 801 9 [1,3,9,89,267,801]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_802 : 0 < 802 ∧ 5+2 < 2*σ 0 802 :=
  checkRule 802 5 [1,2,401,802]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_807 : 0 < 807 ∧ 5+2 < 2*σ 0 807 :=
  checkRule 807 5 [1,3,269,807]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_813 : 0 < 813 ∧ 5+2 < 2*σ 0 813 :=
  checkRule 813 5 [1,3,271,813]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_815 : 0 < 815 ∧ 5+2 < 2*σ 0 815 :=
  checkRule 815 5 [1,5,163,815]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_816 : 0 < 816 ∧ 37+2 < 2*σ 0 816 :=
  checkRule 816 37 [1,2,3,4,6,8,12,16,17,24,34,48,51,68,102,136,204,272,408,816]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_818 : 0 < 818 ∧ 5+2 < 2*σ 0 818 :=
  checkRule 818 5 [1,2,409,818]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_820 : 0 < 820 ∧ 21+2 < 2*σ 0 820 :=
  checkRule 820 21 [1,2,4,5,10,20,41,82,164,205,410,820]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_822 : 0 < 822 ∧ 13+2 < 2*σ 0 822 :=
  checkRule 822 13 [1,2,3,6,137,274,411,822]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_829 : 0 < 829 ∧ 1+2 < 2*σ 0 829 :=
  checkRule 829 1 [1,829]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_830 : 0 < 830 ∧ 13+2 < 2*σ 0 830 :=
  checkRule 830 13 [1,2,5,10,83,166,415,830]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_831 : 0 < 831 ∧ 5+2 < 2*σ 0 831 :=
  checkRule 831 5 [1,3,277,831]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_833 : 0 < 833 ∧ 9+2 < 2*σ 0 833 :=
  checkRule 833 9 [1,7,17,49,119,833]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_834 : 0 < 834 ∧ 13+2 < 2*σ 0 834 :=
  checkRule 834 13 [1,2,3,6,139,278,417,834]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_835 : 0 < 835 ∧ 5+2 < 2*σ 0 835 :=
  checkRule 835 5 [1,5,167,835]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_837 : 0 < 837 ∧ 13+2 < 2*σ 0 837 :=
  checkRule 837 13 [1,3,9,27,31,93,279,837]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_838 : 0 < 838 ∧ 5+2 < 2*σ 0 838 :=
  checkRule 838 5 [1,2,419,838]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_842 : 0 < 842 ∧ 5+2 < 2*σ 0 842 :=
  checkRule 842 5 [1,2,421,842]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_843 : 0 < 843 ∧ 5+2 < 2*σ 0 843 :=
  checkRule 843 5 [1,3,281,843]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_844 : 0 < 844 ∧ 9+2 < 2*σ 0 844 :=
  checkRule 844 9 [1,2,4,211,422,844]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_846 : 0 < 846 ∧ 21+2 < 2*σ 0 846 :=
  checkRule 846 21 [1,2,3,6,9,18,47,94,141,282,423,846]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_848 : 0 < 848 ∧ 17+2 < 2*σ 0 848 :=
  checkRule 848 17 [1,2,4,8,16,53,106,212,424,848]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_849 : 0 < 849 ∧ 5+2 < 2*σ 0 849 :=
  checkRule 849 5 [1,3,283,849]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_850 : 0 < 850 ∧ 21+2 < 2*σ 0 850 :=
  checkRule 850 21 [1,2,5,10,17,25,34,50,85,170,425,850]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_860 : 0 < 860 ∧ 21+2 < 2*σ 0 860 :=
  checkRule 860 21 [1,2,4,5,10,20,43,86,172,215,430,860]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_862 : 0 < 862 ∧ 5+2 < 2*σ 0 862 :=
  checkRule 862 5 [1,2,431,862]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_865 : 0 < 865 ∧ 5+2 < 2*σ 0 865 :=
  checkRule 865 5 [1,5,173,865]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_866 : 0 < 866 ∧ 5+2 < 2*σ 0 866 :=
  checkRule 866 5 [1,2,433,866]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_867 : 0 < 867 ∧ 9+2 < 2*σ 0 867 :=
  checkRule 867 9 [1,3,17,51,289,867]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_873 : 0 < 873 ∧ 9+2 < 2*σ 0 873 :=
  checkRule 873 9 [1,3,9,97,291,873]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_874 : 0 < 874 ∧ 13+2 < 2*σ 0 874 :=
  checkRule 874 13 [1,2,19,23,38,46,437,874]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_878 : 0 < 878 ∧ 5+2 < 2*σ 0 878 :=
  checkRule 878 5 [1,2,439,878]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_879 : 0 < 879 ∧ 5+2 < 2*σ 0 879 :=
  checkRule 879 5 [1,3,293,879]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_886 : 0 < 886 ∧ 5+2 < 2*σ 0 886 :=
  checkRule 886 5 [1,2,443,886]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_888 : 0 < 888 ∧ 29+2 < 2*σ 0 888 :=
  checkRule 888 29 [1,2,3,4,6,8,12,24,37,74,111,148,222,296,444,888]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_890 : 0 < 890 ∧ 13+2 < 2*σ 0 890 :=
  checkRule 890 13 [1,2,5,10,89,178,445,890]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_892 : 0 < 892 ∧ 9+2 < 2*σ 0 892 :=
  checkRule 892 9 [1,2,4,223,446,892]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_894 : 0 < 894 ∧ 13+2 < 2*σ 0 894 :=
  checkRule 894 13 [1,2,3,6,149,298,447,894]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_895 : 0 < 895 ∧ 5+2 < 2*σ 0 895 :=
  checkRule 895 5 [1,5,179,895]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_898 : 0 < 898 ∧ 5+2 < 2*σ 0 898 :=
  checkRule 898 5 [1,2,449,898]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_905 : 0 < 905 ∧ 5+2 < 2*σ 0 905 :=
  checkRule 905 5 [1,5,181,905]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_906 : 0 < 906 ∧ 13+2 < 2*σ 0 906 :=
  checkRule 906 13 [1,2,3,6,151,302,453,906]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_908 : 0 < 908 ∧ 9+2 < 2*σ 0 908 :=
  checkRule 908 9 [1,2,4,227,454,908]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_909 : 0 < 909 ∧ 9+2 < 2*σ 0 909 :=
  checkRule 909 9 [1,3,9,101,303,909]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_911 : 0 < 911 ∧ 1+2 < 2*σ 0 911 :=
  checkRule 911 1 [1,911]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_912 : 0 < 912 ∧ 37+2 < 2*σ 0 912 :=
  checkRule 912 37 [1,2,3,4,6,8,12,16,19,24,38,48,57,76,114,152,228,304,456,912]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_914 : 0 < 914 ∧ 5+2 < 2*σ 0 914 :=
  checkRule 914 5 [1,2,457,914]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_916 : 0 < 916 ∧ 9+2 < 2*σ 0 916 :=
  checkRule 916 9 [1,2,4,229,458,916]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_918 : 0 < 918 ∧ 29+2 < 2*σ 0 918 :=
  checkRule 918 29 [1,2,3,6,9,17,18,27,34,51,54,102,153,306,459,918]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_921 : 0 < 921 ∧ 5+2 < 2*σ 0 921 :=
  checkRule 921 5 [1,3,307,921]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_922 : 0 < 922 ∧ 5+2 < 2*σ 0 922 :=
  checkRule 922 5 [1,2,461,922]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_926 : 0 < 926 ∧ 5+2 < 2*σ 0 926 :=
  checkRule 926 5 [1,2,463,926]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_927 : 0 < 927 ∧ 9+2 < 2*σ 0 927 :=
  checkRule 927 9 [1,3,9,103,309,927]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_931 : 0 < 931 ∧ 9+2 < 2*σ 0 931 :=
  checkRule 931 9 [1,7,19,49,133,931]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_932 : 0 < 932 ∧ 9+2 < 2*σ 0 932 :=
  checkRule 932 9 [1,2,4,233,466,932]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_933 : 0 < 933 ∧ 5+2 < 2*σ 0 933 :=
  checkRule 933 5 [1,3,311,933]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_934 : 0 < 934 ∧ 5+2 < 2*σ 0 934 :=
  checkRule 934 5 [1,2,467,934]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_939 : 0 < 939 ∧ 5+2 < 2*σ 0 939 :=
  checkRule 939 5 [1,3,313,939]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_942 : 0 < 942 ∧ 13+2 < 2*σ 0 942 :=
  checkRule 942 13 [1,2,3,6,157,314,471,942]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_944 : 0 < 944 ∧ 17+2 < 2*σ 0 944 :=
  checkRule 944 17 [1,2,4,8,16,59,118,236,472,944]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_947 : 0 < 947 ∧ 1+2 < 2*σ 0 947 :=
  checkRule 947 1 [1,947]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_950 : 0 < 950 ∧ 21+2 < 2*σ 0 950 :=
  checkRule 950 21 [1,2,5,10,19,25,38,50,95,190,475,950]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_951 : 0 < 951 ∧ 5+2 < 2*σ 0 951 :=
  checkRule 951 5 [1,3,317,951]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_954 : 0 < 954 ∧ 21+2 < 2*σ 0 954 :=
  checkRule 954 21 [1,2,3,6,9,18,53,106,159,318,477,954]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_955 : 0 < 955 ∧ 5+2 < 2*σ 0 955 :=
  checkRule 955 5 [1,5,191,955]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_956 : 0 < 956 ∧ 9+2 < 2*σ 0 956 :=
  checkRule 956 9 [1,2,4,239,478,956]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_958 : 0 < 958 ∧ 5+2 < 2*σ 0 958 :=
  checkRule 958 5 [1,2,479,958]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_963 : 0 < 963 ∧ 9+2 < 2*σ 0 963 :=
  checkRule 963 9 [1,3,9,107,321,963]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_964 : 0 < 964 ∧ 9+2 < 2*σ 0 964 :=
  checkRule 964 9 [1,2,4,241,482,964]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_965 : 0 < 965 ∧ 5+2 < 2*σ 0 965 :=
  checkRule 965 5 [1,5,193,965]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_969 : 0 < 969 ∧ 13+2 < 2*σ 0 969 :=
  checkRule 969 13 [1,3,17,19,51,57,323,969]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_970 : 0 < 970 ∧ 13+2 < 2*σ 0 970 :=
  checkRule 970 13 [1,2,5,10,97,194,485,970]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_974 : 0 < 974 ∧ 5+2 < 2*σ 0 974 :=
  checkRule 974 5 [1,2,487,974]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_976 : 0 < 976 ∧ 17+2 < 2*σ 0 976 :=
  checkRule 976 17 [1,2,4,8,16,61,122,244,488,976]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_978 : 0 < 978 ∧ 13+2 < 2*σ 0 978 :=
  checkRule 978 13 [1,2,3,6,163,326,489,978]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_981 : 0 < 981 ∧ 9+2 < 2*σ 0 981 :=
  checkRule 981 9 [1,3,9,109,327,981]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_982 : 0 < 982 ∧ 5+2 < 2*σ 0 982 :=
  checkRule 982 5 [1,2,491,982]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_983 : 0 < 983 ∧ 1+2 < 2*σ 0 983 :=
  checkRule 983 1 [1,983]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_984 : 0 < 984 ∧ 29+2 < 2*σ 0 984 :=
  checkRule 984 29 [1,2,3,4,6,8,12,24,41,82,123,164,246,328,492,984]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_985 : 0 < 985 ∧ 5+2 < 2*σ 0 985 :=
  checkRule 985 5 [1,5,197,985]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_986 : 0 < 986 ∧ 13+2 < 2*σ 0 986 :=
  checkRule 986 13 [1,2,17,29,34,58,493,986]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_991 : 0 < 991 ∧ 1+2 < 2*σ 0 991 :=
  checkRule 991 1 [1,991]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_993 : 0 < 993 ∧ 5+2 < 2*σ 0 993 :=
  checkRule 993 5 [1,3,331,993]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_995 : 0 < 995 ∧ 5+2 < 2*σ 0 995 :=
  checkRule 995 5 [1,5,199,995]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_998 : 0 < 998 ∧ 5+2 < 2*σ 0 998 :=
  checkRule 998 5 [1,2,499,998]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1002 : 0 < 1002 ∧ 13+2 < 2*σ 0 1002 :=
  checkRule 1002 13 [1,2,3,6,167,334,501,1002]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1004 : 0 < 1004 ∧ 9+2 < 2*σ 0 1004 :=
  checkRule 1004 9 [1,2,4,251,502,1004]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1006 : 0 < 1006 ∧ 5+2 < 2*σ 0 1006 :=
  checkRule 1006 5 [1,2,503,1006]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1010 : 0 < 1010 ∧ 13+2 < 2*σ 0 1010 :=
  checkRule 1010 13 [1,2,5,10,101,202,505,1010]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1011 : 0 < 1011 ∧ 5+2 < 2*σ 0 1011 :=
  checkRule 1011 5 [1,3,337,1011]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1013 : 0 < 1013 ∧ 1+2 < 2*σ 0 1013 :=
  checkRule 1013 1 [1,1013]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1017 : 0 < 1017 ∧ 9+2 < 2*σ 0 1017 :=
  checkRule 1017 9 [1,3,9,113,339,1017]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1018 : 0 < 1018 ∧ 5+2 < 2*σ 0 1018 :=
  checkRule 1018 5 [1,2,509,1018]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1021 : 0 < 1021 ∧ 1+2 < 2*σ 0 1021 :=
  checkRule 1021 1 [1,1021]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1026 : 0 < 1026 ∧ 29+2 < 2*σ 0 1026 :=
  checkRule 1026 29 [1,2,3,6,9,18,19,27,38,54,57,114,171,342,513,1026]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1028 : 0 < 1028 ∧ 9+2 < 2*σ 0 1028 :=
  checkRule 1028 9 [1,2,4,257,514,1028]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1030 : 0 < 1030 ∧ 13+2 < 2*σ 0 1030 :=
  checkRule 1030 13 [1,2,5,10,103,206,515,1030]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1031 : 0 < 1031 ∧ 1+2 < 2*σ 0 1031 :=
  checkRule 1031 1 [1,1031]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1032 : 0 < 1032 ∧ 29+2 < 2*σ 0 1032 :=
  checkRule 1032 29 [1,2,3,4,6,8,12,24,43,86,129,172,258,344,516,1032]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1038 : 0 < 1038 ∧ 13+2 < 2*σ 0 1038 :=
  checkRule 1038 13 [1,2,3,6,173,346,519,1038]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1041 : 0 < 1041 ∧ 5+2 < 2*σ 0 1041 :=
  checkRule 1041 5 [1,3,347,1041]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1046 : 0 < 1046 ∧ 5+2 < 2*σ 0 1046 :=
  checkRule 1046 5 [1,2,523,1046]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1047 : 0 < 1047 ∧ 5+2 < 2*σ 0 1047 :=
  checkRule 1047 5 [1,3,349,1047]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1052 : 0 < 1052 ∧ 9+2 < 2*σ 0 1052 :=
  checkRule 1052 9 [1,2,4,263,526,1052]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1055 : 0 < 1055 ∧ 5+2 < 2*σ 0 1055 :=
  checkRule 1055 5 [1,5,211,1055]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1059 : 0 < 1059 ∧ 5+2 < 2*σ 0 1059 :=
  checkRule 1059 5 [1,3,353,1059]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1060 : 0 < 1060 ∧ 21+2 < 2*σ 0 1060 :=
  checkRule 1060 21 [1,2,4,5,10,20,53,106,212,265,530,1060]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1062 : 0 < 1062 ∧ 21+2 < 2*σ 0 1062 :=
  checkRule 1062 21 [1,2,3,6,9,18,59,118,177,354,531,1062]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1070 : 0 < 1070 ∧ 13+2 < 2*σ 0 1070 :=
  checkRule 1070 13 [1,2,5,10,107,214,535,1070]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1072 : 0 < 1072 ∧ 17+2 < 2*σ 0 1072 :=
  checkRule 1072 17 [1,2,4,8,16,67,134,268,536,1072]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1074 : 0 < 1074 ∧ 13+2 < 2*σ 0 1074 :=
  checkRule 1074 13 [1,2,3,6,179,358,537,1074]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1076 : 0 < 1076 ∧ 9+2 < 2*σ 0 1076 :=
  checkRule 1076 9 [1,2,4,269,538,1076]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1077 : 0 < 1077 ∧ 5+2 < 2*σ 0 1077 :=
  checkRule 1077 5 [1,3,359,1077]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1082 : 0 < 1082 ∧ 5+2 < 2*σ 0 1082 :=
  checkRule 1082 5 [1,2,541,1082]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1083 : 0 < 1083 ∧ 9+2 < 2*σ 0 1083 :=
  checkRule 1083 9 [1,3,19,57,361,1083]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1084 : 0 < 1084 ∧ 9+2 < 2*σ 0 1084 :=
  checkRule 1084 9 [1,2,4,271,542,1084]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1086 : 0 < 1086 ∧ 13+2 < 2*σ 0 1086 :=
  checkRule 1086 13 [1,2,3,6,181,362,543,1086]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1088 : 0 < 1088 ∧ 25+2 < 2*σ 0 1088 :=
  checkRule 1088 25 [1,2,4,8,16,17,32,34,64,68,136,272,544,1088]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1090 : 0 < 1090 ∧ 13+2 < 2*σ 0 1090 :=
  checkRule 1090 13 [1,2,5,10,109,218,545,1090]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1094 : 0 < 1094 ∧ 5+2 < 2*σ 0 1094 :=
  checkRule 1094 5 [1,2,547,1094]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1097 : 0 < 1097 ∧ 1+2 < 2*σ 0 1097 :=
  checkRule 1097 1 [1,1097]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1098 : 0 < 1098 ∧ 21+2 < 2*σ 0 1098 :=
  checkRule 1098 21 [1,2,3,6,9,18,61,122,183,366,549,1098]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1101 : 0 < 1101 ∧ 5+2 < 2*σ 0 1101 :=
  checkRule 1101 5 [1,3,367,1101]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1104 : 0 < 1104 ∧ 37+2 < 2*σ 0 1104 :=
  checkRule 1104 37 [1,2,3,4,6,8,12,16,23,24,46,48,69,92,138,184,276,368,552,1104]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1108 : 0 < 1108 ∧ 9+2 < 2*σ 0 1108 :=
  checkRule 1108 9 [1,2,4,277,554,1108]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1114 : 0 < 1114 ∧ 5+2 < 2*σ 0 1114 :=
  checkRule 1114 5 [1,2,557,1114]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1115 : 0 < 1115 ∧ 5+2 < 2*σ 0 1115 :=
  checkRule 1115 5 [1,5,223,1115]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1119 : 0 < 1119 ∧ 5+2 < 2*σ 0 1119 :=
  checkRule 1119 5 [1,3,373,1119]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1123 : 0 < 1123 ∧ 1+2 < 2*σ 0 1123 :=
  checkRule 1123 1 [1,1123]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1124 : 0 < 1124 ∧ 9+2 < 2*σ 0 1124 :=
  checkRule 1124 9 [1,2,4,281,562,1124]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1126 : 0 < 1126 ∧ 5+2 < 2*σ 0 1126 :=
  checkRule 1126 5 [1,2,563,1126]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1127 : 0 < 1127 ∧ 9+2 < 2*σ 0 1127 :=
  checkRule 1127 9 [1,7,23,49,161,1127]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1130 : 0 < 1130 ∧ 13+2 < 2*σ 0 1130 :=
  checkRule 1130 13 [1,2,5,10,113,226,565,1130]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1132 : 0 < 1132 ∧ 9+2 < 2*σ 0 1132 :=
  checkRule 1132 9 [1,2,4,283,566,1132]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1135 : 0 < 1135 ∧ 5+2 < 2*σ 0 1135 :=
  checkRule 1135 5 [1,5,227,1135]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1136 : 0 < 1136 ∧ 17+2 < 2*σ 0 1136 :=
  checkRule 1136 17 [1,2,4,8,16,71,142,284,568,1136]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1137 : 0 < 1137 ∧ 5+2 < 2*σ 0 1137 :=
  checkRule 1137 5 [1,3,379,1137]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1138 : 0 < 1138 ∧ 5+2 < 2*σ 0 1138 :=
  checkRule 1138 5 [1,2,569,1138]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1142 : 0 < 1142 ∧ 5+2 < 2*σ 0 1142 :=
  checkRule 1142 5 [1,2,571,1142]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1143 : 0 < 1143 ∧ 9+2 < 2*σ 0 1143 :=
  checkRule 1143 9 [1,3,9,127,381,1143]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1145 : 0 < 1145 ∧ 5+2 < 2*σ 0 1145 :=
  checkRule 1145 5 [1,5,229,1145]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1146 : 0 < 1146 ∧ 13+2 < 2*σ 0 1146 :=
  checkRule 1146 13 [1,2,3,6,191,382,573,1146]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1149 : 0 < 1149 ∧ 5+2 < 2*σ 0 1149 :=
  checkRule 1149 5 [1,3,383,1149]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1150 : 0 < 1150 ∧ 21+2 < 2*σ 0 1150 :=
  checkRule 1150 21 [1,2,5,10,23,25,46,50,115,230,575,1150]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1154 : 0 < 1154 ∧ 5+2 < 2*σ 0 1154 :=
  checkRule 1154 5 [1,2,577,1154]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1156 : 0 < 1156 ∧ 15+2 < 2*σ 0 1156 :=
  checkRule 1156 15 [1,2,4,17,34,68,289,578,1156]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1158 : 0 < 1158 ∧ 13+2 < 2*σ 0 1158 :=
  checkRule 1158 13 [1,2,3,6,193,386,579,1158]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1163 : 0 < 1163 ∧ 1+2 < 2*σ 0 1163 :=
  checkRule 1163 1 [1,1163]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1165 : 0 < 1165 ∧ 5+2 < 2*σ 0 1165 :=
  checkRule 1165 5 [1,5,233,1165]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1167 : 0 < 1167 ∧ 5+2 < 2*σ 0 1167 :=
  checkRule 1167 5 [1,3,389,1167]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1168 : 0 < 1168 ∧ 17+2 < 2*σ 0 1168 :=
  checkRule 1168 17 [1,2,4,8,16,73,146,292,584,1168]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1172 : 0 < 1172 ∧ 9+2 < 2*σ 0 1172 :=
  checkRule 1172 9 [1,2,4,293,586,1172]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1173 : 0 < 1173 ∧ 13+2 < 2*σ 0 1173 :=
  checkRule 1173 13 [1,3,17,23,51,69,391,1173]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1174 : 0 < 1174 ∧ 5+2 < 2*σ 0 1174 :=
  checkRule 1174 5 [1,2,587,1174]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1179 : 0 < 1179 ∧ 9+2 < 2*σ 0 1179 :=
  checkRule 1179 9 [1,3,9,131,393,1179]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1180 : 0 < 1180 ∧ 21+2 < 2*σ 0 1180 :=
  checkRule 1180 21 [1,2,4,5,10,20,59,118,236,295,590,1180]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1182 : 0 < 1182 ∧ 13+2 < 2*σ 0 1182 :=
  checkRule 1182 13 [1,2,3,6,197,394,591,1182]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1191 : 0 < 1191 ∧ 5+2 < 2*σ 0 1191 :=
  checkRule 1191 5 [1,3,397,1191]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1194 : 0 < 1194 ∧ 13+2 < 2*σ 0 1194 :=
  checkRule 1194 13 [1,2,3,6,199,398,597,1194]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1195 : 0 < 1195 ∧ 5+2 < 2*σ 0 1195 :=
  checkRule 1195 5 [1,5,239,1195]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1198 : 0 < 1198 ∧ 5+2 < 2*σ 0 1198 :=
  checkRule 1198 5 [1,2,599,1198]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1201 : 0 < 1201 ∧ 1+2 < 2*σ 0 1201 :=
  checkRule 1201 1 [1,1201]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1202 : 0 < 1202 ∧ 5+2 < 2*σ 0 1202 :=
  checkRule 1202 5 [1,2,601,1202]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1203 : 0 < 1203 ∧ 5+2 < 2*σ 0 1203 :=
  checkRule 1203 5 [1,3,401,1203]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1205 : 0 < 1205 ∧ 5+2 < 2*σ 0 1205 :=
  checkRule 1205 5 [1,5,241,1205]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1206 : 0 < 1206 ∧ 21+2 < 2*σ 0 1206 :=
  checkRule 1206 21 [1,2,3,6,9,18,67,134,201,402,603,1206]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1214 : 0 < 1214 ∧ 5+2 < 2*σ 0 1214 :=
  checkRule 1214 5 [1,2,607,1214]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1217 : 0 < 1217 ∧ 1+2 < 2*σ 0 1217 :=
  checkRule 1217 1 [1,1217]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1220 : 0 < 1220 ∧ 21+2 < 2*σ 0 1220 :=
  checkRule 1220 21 [1,2,4,5,10,20,61,122,244,305,610,1220]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1223 : 0 < 1223 ∧ 1+2 < 2*σ 0 1223 :=
  checkRule 1223 1 [1,1223]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1226 : 0 < 1226 ∧ 5+2 < 2*σ 0 1226 :=
  checkRule 1226 5 [1,2,613,1226]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1227 : 0 < 1227 ∧ 5+2 < 2*σ 0 1227 :=
  checkRule 1227 5 [1,3,409,1227]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1228 : 0 < 1228 ∧ 9+2 < 2*σ 0 1228 :=
  checkRule 1228 9 [1,2,4,307,614,1228]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1231 : 0 < 1231 ∧ 1+2 < 2*σ 0 1231 :=
  checkRule 1231 1 [1,1231]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1233 : 0 < 1233 ∧ 9+2 < 2*σ 0 1233 :=
  checkRule 1233 9 [1,3,9,137,411,1233]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1234 : 0 < 1234 ∧ 5+2 < 2*σ 0 1234 :=
  checkRule 1234 5 [1,2,617,1234]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1238 : 0 < 1238 ∧ 5+2 < 2*σ 0 1238 :=
  checkRule 1238 5 [1,2,619,1238]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1242 : 0 < 1242 ∧ 29+2 < 2*σ 0 1242 :=
  checkRule 1242 29 [1,2,3,6,9,18,23,27,46,54,69,138,207,414,621,1242]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1244 : 0 < 1244 ∧ 9+2 < 2*σ 0 1244 :=
  checkRule 1244 9 [1,2,4,311,622,1244]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1250 : 0 < 1250 ∧ 17+2 < 2*σ 0 1250 :=
  checkRule 1250 17 [1,2,5,10,25,50,125,250,625,1250]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1251 : 0 < 1251 ∧ 9+2 < 2*σ 0 1251 :=
  checkRule 1251 9 [1,3,9,139,417,1251]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1252 : 0 < 1252 ∧ 9+2 < 2*σ 0 1252 :=
  checkRule 1252 9 [1,2,4,313,626,1252]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1255 : 0 < 1255 ∧ 5+2 < 2*σ 0 1255 :=
  checkRule 1255 5 [1,5,251,1255]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1257 : 0 < 1257 ∧ 5+2 < 2*σ 0 1257 :=
  checkRule 1257 5 [1,3,419,1257]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1263 : 0 < 1263 ∧ 5+2 < 2*σ 0 1263 :=
  checkRule 1263 5 [1,3,421,1263]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1264 : 0 < 1264 ∧ 17+2 < 2*σ 0 1264 :=
  checkRule 1264 17 [1,2,4,8,16,79,158,316,632,1264]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1266 : 0 < 1266 ∧ 13+2 < 2*σ 0 1266 :=
  checkRule 1266 13 [1,2,3,6,211,422,633,1266]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1268 : 0 < 1268 ∧ 9+2 < 2*σ 0 1268 :=
  checkRule 1268 9 [1,2,4,317,634,1268]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1272 : 0 < 1272 ∧ 29+2 < 2*σ 0 1272 :=
  checkRule 1272 29 [1,2,3,4,6,8,12,24,53,106,159,212,318,424,636,1272]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1275 : 0 < 1275 ∧ 21+2 < 2*σ 0 1275 :=
  checkRule 1275 21 [1,3,5,15,17,25,51,75,85,255,425,1275]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1278 : 0 < 1278 ∧ 21+2 < 2*σ 0 1278 :=
  checkRule 1278 21 [1,2,3,6,9,18,71,142,213,426,639,1278]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1285 : 0 < 1285 ∧ 5+2 < 2*σ 0 1285 :=
  checkRule 1285 5 [1,5,257,1285]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1286 : 0 < 1286 ∧ 5+2 < 2*σ 0 1286 :=
  checkRule 1286 5 [1,2,643,1286]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1289 : 0 < 1289 ∧ 1+2 < 2*σ 0 1289 :=
  checkRule 1289 1 [1,1289]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1292 : 0 < 1292 ∧ 21+2 < 2*σ 0 1292 :=
  checkRule 1292 21 [1,2,4,17,19,34,38,68,76,323,646,1292]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1293 : 0 < 1293 ∧ 5+2 < 2*σ 0 1293 :=
  checkRule 1293 5 [1,3,431,1293]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1299 : 0 < 1299 ∧ 5+2 < 2*σ 0 1299 :=
  checkRule 1299 5 [1,3,433,1299]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1306 : 0 < 1306 ∧ 5+2 < 2*σ 0 1306 :=
  checkRule 1306 5 [1,2,653,1306]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1310 : 0 < 1310 ∧ 13+2 < 2*σ 0 1310 :=
  checkRule 1310 13 [1,2,5,10,131,262,655,1310]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1311 : 0 < 1311 ∧ 13+2 < 2*σ 0 1311 :=
  checkRule 1311 13 [1,3,19,23,57,69,437,1311]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1314 : 0 < 1314 ∧ 21+2 < 2*σ 0 1314 :=
  checkRule 1314 21 [1,2,3,6,9,18,73,146,219,438,657,1314]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1315 : 0 < 1315 ∧ 5+2 < 2*σ 0 1315 :=
  checkRule 1315 5 [1,5,263,1315]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1317 : 0 < 1317 ∧ 5+2 < 2*σ 0 1317 :=
  checkRule 1317 5 [1,3,439,1317]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1318 : 0 < 1318 ∧ 5+2 < 2*σ 0 1318 :=
  checkRule 1318 5 [1,2,659,1318]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1322 : 0 < 1322 ∧ 5+2 < 2*σ 0 1322 :=
  checkRule 1322 5 [1,2,661,1322]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1324 : 0 < 1324 ∧ 9+2 < 2*σ 0 1324 :=
  checkRule 1324 9 [1,2,4,331,662,1324]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1328 : 0 < 1328 ∧ 17+2 < 2*σ 0 1328 :=
  checkRule 1328 17 [1,2,4,8,16,83,166,332,664,1328]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1329 : 0 < 1329 ∧ 5+2 < 2*σ 0 1329 :=
  checkRule 1329 5 [1,3,443,1329]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1338 : 0 < 1338 ∧ 13+2 < 2*σ 0 1338 :=
  checkRule 1338 13 [1,2,3,6,223,446,669,1338]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1340 : 0 < 1340 ∧ 21+2 < 2*σ 0 1340 :=
  checkRule 1340 21 [1,2,4,5,10,20,67,134,268,335,670,1340]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1341 : 0 < 1341 ∧ 9+2 < 2*σ 0 1341 :=
  checkRule 1341 9 [1,3,9,149,447,1341]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1345 : 0 < 1345 ∧ 5+2 < 2*σ 0 1345 :=
  checkRule 1345 5 [1,5,269,1345]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1347 : 0 < 1347 ∧ 5+2 < 2*σ 0 1347 :=
  checkRule 1347 5 [1,3,449,1347]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1348 : 0 < 1348 ∧ 9+2 < 2*σ 0 1348 :=
  checkRule 1348 9 [1,2,4,337,674,1348]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1354 : 0 < 1354 ∧ 5+2 < 2*σ 0 1354 :=
  checkRule 1354 5 [1,2,677,1354]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1355 : 0 < 1355 ∧ 5+2 < 2*σ 0 1355 :=
  checkRule 1355 5 [1,5,271,1355]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1359 : 0 < 1359 ∧ 9+2 < 2*σ 0 1359 :=
  checkRule 1359 9 [1,3,9,151,453,1359]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1362 : 0 < 1362 ∧ 13+2 < 2*σ 0 1362 :=
  checkRule 1362 13 [1,2,3,6,227,454,681,1362]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1366 : 0 < 1366 ∧ 5+2 < 2*σ 0 1366 :=
  checkRule 1366 5 [1,2,683,1366]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1370 : 0 < 1370 ∧ 13+2 < 2*σ 0 1370 :=
  checkRule 1370 13 [1,2,5,10,137,274,685,1370]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1371 : 0 < 1371 ∧ 5+2 < 2*σ 0 1371 :=
  checkRule 1371 5 [1,3,457,1371]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1374 : 0 < 1374 ∧ 13+2 < 2*σ 0 1374 :=
  checkRule 1374 13 [1,2,3,6,229,458,687,1374]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1383 : 0 < 1383 ∧ 5+2 < 2*σ 0 1383 :=
  checkRule 1383 5 [1,3,461,1383]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1385 : 0 < 1385 ∧ 5+2 < 2*σ 0 1385 :=
  checkRule 1385 5 [1,5,277,1385]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1388 : 0 < 1388 ∧ 9+2 < 2*σ 0 1388 :=
  checkRule 1388 9 [1,2,4,347,694,1388]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1390 : 0 < 1390 ∧ 13+2 < 2*σ 0 1390 :=
  checkRule 1390 13 [1,2,5,10,139,278,695,1390]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1392 : 0 < 1392 ∧ 37+2 < 2*σ 0 1392 :=
  checkRule 1392 37 [1,2,3,4,6,8,12,16,24,29,48,58,87,116,174,232,348,464,696,1392]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1396 : 0 < 1396 ∧ 9+2 < 2*σ 0 1396 :=
  checkRule 1396 9 [1,2,4,349,698,1396]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1398 : 0 < 1398 ∧ 13+2 < 2*σ 0 1398 :=
  checkRule 1398 13 [1,2,3,6,233,466,699,1398]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1401 : 0 < 1401 ∧ 5+2 < 2*σ 0 1401 :=
  checkRule 1401 5 [1,3,467,1401]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1405 : 0 < 1405 ∧ 5+2 < 2*σ 0 1405 :=
  checkRule 1405 5 [1,5,281,1405]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1412 : 0 < 1412 ∧ 9+2 < 2*σ 0 1412 :=
  checkRule 1412 9 [1,2,4,353,706,1412]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1413 : 0 < 1413 ∧ 9+2 < 2*σ 0 1413 :=
  checkRule 1413 9 [1,3,9,157,471,1413]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1415 : 0 < 1415 ∧ 5+2 < 2*σ 0 1415 :=
  checkRule 1415 5 [1,5,283,1415]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1416 : 0 < 1416 ∧ 29+2 < 2*σ 0 1416 :=
  checkRule 1416 29 [1,2,3,4,6,8,12,24,59,118,177,236,354,472,708,1416]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1420 : 0 < 1420 ∧ 21+2 < 2*σ 0 1420 :=
  checkRule 1420 21 [1,2,4,5,10,20,71,142,284,355,710,1420]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1421 : 0 < 1421 ∧ 9+2 < 2*σ 0 1421 :=
  checkRule 1421 9 [1,7,29,49,203,1421]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1422 : 0 < 1422 ∧ 21+2 < 2*σ 0 1422 :=
  checkRule 1422 21 [1,2,3,6,9,18,79,158,237,474,711,1422]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1424 : 0 < 1424 ∧ 17+2 < 2*σ 0 1424 :=
  checkRule 1424 17 [1,2,4,8,16,89,178,356,712,1424]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1434 : 0 < 1434 ∧ 13+2 < 2*σ 0 1434 :=
  checkRule 1434 13 [1,2,3,6,239,478,717,1434]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1436 : 0 < 1436 ∧ 9+2 < 2*σ 0 1436 :=
  checkRule 1436 9 [1,2,4,359,718,1436]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1438 : 0 < 1438 ∧ 5+2 < 2*σ 0 1438 :=
  checkRule 1438 5 [1,2,719,1438]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1444 : 0 < 1444 ∧ 15+2 < 2*σ 0 1444 :=
  checkRule 1444 15 [1,2,4,19,38,76,361,722,1444]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1445 : 0 < 1445 ∧ 9+2 < 2*σ 0 1445 :=
  checkRule 1445 9 [1,5,17,85,289,1445]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1446 : 0 < 1446 ∧ 13+2 < 2*σ 0 1446 :=
  checkRule 1446 13 [1,2,3,6,241,482,723,1446]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1454 : 0 < 1454 ∧ 5+2 < 2*σ 0 1454 :=
  checkRule 1454 5 [1,2,727,1454]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1458 : 0 < 1458 ∧ 25+2 < 2*σ 0 1458 :=
  checkRule 1458 25 [1,2,3,6,9,18,27,54,81,162,243,486,729,1458]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1460 : 0 < 1460 ∧ 21+2 < 2*σ 0 1460 :=
  checkRule 1460 21 [1,2,4,5,10,20,73,146,292,365,730,1460]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1461 : 0 < 1461 ∧ 5+2 < 2*σ 0 1461 :=
  checkRule 1461 5 [1,3,487,1461]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1464 : 0 < 1464 ∧ 29+2 < 2*σ 0 1464 :=
  checkRule 1464 29 [1,2,3,4,6,8,12,24,61,122,183,244,366,488,732,1464]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1465 : 0 < 1465 ∧ 5+2 < 2*σ 0 1465 :=
  checkRule 1465 5 [1,5,293,1465]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1466 : 0 < 1466 ∧ 5+2 < 2*σ 0 1466 :=
  checkRule 1466 5 [1,2,733,1466]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1467 : 0 < 1467 ∧ 9+2 < 2*σ 0 1467 :=
  checkRule 1467 9 [1,3,9,163,489,1467]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1468 : 0 < 1468 ∧ 9+2 < 2*σ 0 1468 :=
  checkRule 1468 9 [1,2,4,367,734,1468]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1473 : 0 < 1473 ∧ 5+2 < 2*σ 0 1473 :=
  checkRule 1473 5 [1,3,491,1473]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1479 : 0 < 1479 ∧ 13+2 < 2*σ 0 1479 :=
  checkRule 1479 13 [1,3,17,29,51,87,493,1479]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1486 : 0 < 1486 ∧ 5+2 < 2*σ 0 1486 :=
  checkRule 1486 5 [1,2,743,1486]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1487 : 0 < 1487 ∧ 1+2 < 2*σ 0 1487 :=
  checkRule 1487 1 [1,1487]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1488 : 0 < 1488 ∧ 37+2 < 2*σ 0 1488 :=
  checkRule 1488 37 [1,2,3,4,6,8,12,16,24,31,48,62,93,124,186,248,372,496,744,1488]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1490 : 0 < 1490 ∧ 13+2 < 2*σ 0 1490 :=
  checkRule 1490 13 [1,2,5,10,149,298,745,1490]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1492 : 0 < 1492 ∧ 9+2 < 2*σ 0 1492 :=
  checkRule 1492 9 [1,2,4,373,746,1492]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1494 : 0 < 1494 ∧ 21+2 < 2*σ 0 1494 :=
  checkRule 1494 21 [1,2,3,6,9,18,83,166,249,498,747,1494]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1503 : 0 < 1503 ∧ 9+2 < 2*σ 0 1503 :=
  checkRule 1503 9 [1,3,9,167,501,1503]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1506 : 0 < 1506 ∧ 13+2 < 2*σ 0 1506 :=
  checkRule 1506 13 [1,2,3,6,251,502,753,1506]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1510 : 0 < 1510 ∧ 13+2 < 2*σ 0 1510 :=
  checkRule 1510 13 [1,2,5,10,151,302,755,1510]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1516 : 0 < 1516 ∧ 9+2 < 2*σ 0 1516 :=
  checkRule 1516 9 [1,2,4,379,758,1516]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1519 : 0 < 1519 ∧ 9+2 < 2*σ 0 1519 :=
  checkRule 1519 9 [1,7,31,49,217,1519]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1532 : 0 < 1532 ∧ 9+2 < 2*σ 0 1532 :=
  checkRule 1532 9 [1,2,4,383,766,1532]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1535 : 0 < 1535 ∧ 5+2 < 2*σ 0 1535 :=
  checkRule 1535 5 [1,5,307,1535]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1536 : 0 < 1536 ∧ 37+2 < 2*σ 0 1536 :=
  checkRule 1536 37 [1,2,3,4,6,8,12,16,24,32,48,64,96,128,192,256,384,512,768,1536]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1538 : 0 < 1538 ∧ 5+2 < 2*σ 0 1538 :=
  checkRule 1538 5 [1,2,769,1538]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1542 : 0 < 1542 ∧ 13+2 < 2*σ 0 1542 :=
  checkRule 1542 13 [1,2,3,6,257,514,771,1542]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1552 : 0 < 1552 ∧ 17+2 < 2*σ 0 1552 :=
  checkRule 1552 17 [1,2,4,8,16,97,194,388,776,1552]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1555 : 0 < 1555 ∧ 5+2 < 2*σ 0 1555 :=
  checkRule 1555 5 [1,5,311,1555]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1556 : 0 < 1556 ∧ 9+2 < 2*σ 0 1556 :=
  checkRule 1556 9 [1,2,4,389,778,1556]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1557 : 0 < 1557 ∧ 9+2 < 2*σ 0 1557 :=
  checkRule 1557 9 [1,3,9,173,519,1557]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1563 : 0 < 1563 ∧ 5+2 < 2*σ 0 1563 :=
  checkRule 1563 5 [1,3,521,1563]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1564 : 0 < 1564 ∧ 21+2 < 2*σ 0 1564 :=
  checkRule 1564 21 [1,2,4,17,23,34,46,68,92,391,782,1564]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1565 : 0 < 1565 ∧ 5+2 < 2*σ 0 1565 :=
  checkRule 1565 5 [1,5,313,1565]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1566 : 0 < 1566 ∧ 29+2 < 2*σ 0 1566 :=
  checkRule 1566 29 [1,2,3,6,9,18,27,29,54,58,87,174,261,522,783,1566]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1569 : 0 < 1569 ∧ 5+2 < 2*σ 0 1569 :=
  checkRule 1569 5 [1,3,523,1569]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1570 : 0 < 1570 ∧ 13+2 < 2*σ 0 1570 :=
  checkRule 1570 13 [1,2,5,10,157,314,785,1570]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1574 : 0 < 1574 ∧ 5+2 < 2*σ 0 1574 :=
  checkRule 1574 5 [1,2,787,1574]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1578 : 0 < 1578 ∧ 13+2 < 2*σ 0 1578 :=
  checkRule 1578 13 [1,2,3,6,263,526,789,1578]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1580 : 0 < 1580 ∧ 21+2 < 2*σ 0 1580 :=
  checkRule 1580 21 [1,2,4,5,10,20,79,158,316,395,790,1580]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1585 : 0 < 1585 ∧ 5+2 < 2*σ 0 1585 :=
  checkRule 1585 5 [1,5,317,1585]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1588 : 0 < 1588 ∧ 9+2 < 2*σ 0 1588 :=
  checkRule 1588 9 [1,2,4,397,794,1588]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1602 : 0 < 1602 ∧ 21+2 < 2*σ 0 1602 :=
  checkRule 1602 21 [1,2,3,6,9,18,89,178,267,534,801,1602]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1604 : 0 < 1604 ∧ 9+2 < 2*σ 0 1604 :=
  checkRule 1604 9 [1,2,4,401,802,1604]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1608 : 0 < 1608 ∧ 29+2 < 2*σ 0 1608 :=
  checkRule 1608 29 [1,2,3,4,6,8,12,24,67,134,201,268,402,536,804,1608]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1609 : 0 < 1609 ∧ 1+2 < 2*σ 0 1609 :=
  checkRule 1609 1 [1,1609]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1611 : 0 < 1611 ∧ 9+2 < 2*σ 0 1611 :=
  checkRule 1611 9 [1,3,9,179,537,1611]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1614 : 0 < 1614 ∧ 13+2 < 2*σ 0 1614 :=
  checkRule 1614 13 [1,2,3,6,269,538,807,1614]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1616 : 0 < 1616 ∧ 17+2 < 2*σ 0 1616 :=
  checkRule 1616 17 [1,2,4,8,16,101,202,404,808,1616]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1618 : 0 < 1618 ∧ 5+2 < 2*σ 0 1618 :=
  checkRule 1618 5 [1,2,809,1618]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1619 : 0 < 1619 ∧ 1+2 < 2*σ 0 1619 :=
  checkRule 1619 1 [1,1619]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1622 : 0 < 1622 ∧ 5+2 < 2*σ 0 1622 :=
  checkRule 1622 5 [1,2,811,1622]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1623 : 0 < 1623 ∧ 5+2 < 2*σ 0 1623 :=
  checkRule 1623 5 [1,3,541,1623]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1626 : 0 < 1626 ∧ 13+2 < 2*σ 0 1626 :=
  checkRule 1626 13 [1,2,3,6,271,542,813,1626]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1629 : 0 < 1629 ∧ 9+2 < 2*σ 0 1629 :=
  checkRule 1629 9 [1,3,9,181,543,1629]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1630 : 0 < 1630 ∧ 13+2 < 2*σ 0 1630 :=
  checkRule 1630 13 [1,2,5,10,163,326,815,1630]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1632 : 0 < 1632 ∧ 45+2 < 2*σ 0 1632 :=
  checkRule 1632 45 [1,2,3,4,6,8,12,16,17,24,32,34,48,51,68,96,102,136,204,272,408,544,816,1632]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1636 : 0 < 1636 ∧ 9+2 < 2*σ 0 1636 :=
  checkRule 1636 9 [1,2,4,409,818,1636]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1642 : 0 < 1642 ∧ 5+2 < 2*σ 0 1642 :=
  checkRule 1642 5 [1,2,821,1642]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1648 : 0 < 1648 ∧ 17+2 < 2*σ 0 1648 :=
  checkRule 1648 17 [1,2,4,8,16,103,206,412,824,1648]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1654 : 0 < 1654 ∧ 5+2 < 2*σ 0 1654 :=
  checkRule 1654 5 [1,2,827,1654]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1655 : 0 < 1655 ∧ 5+2 < 2*σ 0 1655 :=
  checkRule 1655 5 [1,5,331,1655]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1658 : 0 < 1658 ∧ 5+2 < 2*σ 0 1658 :=
  checkRule 1658 5 [1,2,829,1658]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1660 : 0 < 1660 ∧ 21+2 < 2*σ 0 1660 :=
  checkRule 1660 21 [1,2,4,5,10,20,83,166,332,415,830,1660]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1662 : 0 < 1662 ∧ 13+2 < 2*σ 0 1662 :=
  checkRule 1662 13 [1,2,3,6,277,554,831,1662]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1666 : 0 < 1666 ∧ 21+2 < 2*σ 0 1666 :=
  checkRule 1666 21 [1,2,7,14,17,34,49,98,119,238,833,1666]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1669 : 0 < 1669 ∧ 1+2 < 2*σ 0 1669 :=
  checkRule 1669 1 [1,1669]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1670 : 0 < 1670 ∧ 13+2 < 2*σ 0 1670 :=
  checkRule 1670 13 [1,2,5,10,167,334,835,1670]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1671 : 0 < 1671 ∧ 5+2 < 2*σ 0 1671 :=
  checkRule 1671 5 [1,3,557,1671]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1674 : 0 < 1674 ∧ 29+2 < 2*σ 0 1674 :=
  checkRule 1674 29 [1,2,3,6,9,18,27,31,54,62,93,186,279,558,837,1674]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1676 : 0 < 1676 ∧ 9+2 < 2*σ 0 1676 :=
  checkRule 1676 9 [1,2,4,419,838,1676]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1684 : 0 < 1684 ∧ 9+2 < 2*σ 0 1684 :=
  checkRule 1684 9 [1,2,4,421,842,1684]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1685 : 0 < 1685 ∧ 5+2 < 2*σ 0 1685 :=
  checkRule 1685 5 [1,5,337,1685]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1686 : 0 < 1686 ∧ 13+2 < 2*σ 0 1686 :=
  checkRule 1686 13 [1,2,3,6,281,562,843,1686]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1689 : 0 < 1689 ∧ 5+2 < 2*σ 0 1689 :=
  checkRule 1689 5 [1,3,563,1689]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1698 : 0 < 1698 ∧ 13+2 < 2*σ 0 1698 :=
  checkRule 1698 13 [1,2,3,6,283,566,849,1698]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1704 : 0 < 1704 ∧ 29+2 < 2*σ 0 1704 :=
  checkRule 1704 29 [1,2,3,4,6,8,12,24,71,142,213,284,426,568,852,1704]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1707 : 0 < 1707 ∧ 5+2 < 2*σ 0 1707 :=
  checkRule 1707 5 [1,3,569,1707]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1712 : 0 < 1712 ∧ 17+2 < 2*σ 0 1712 :=
  checkRule 1712 17 [1,2,4,8,16,107,214,428,856,1712]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1714 : 0 < 1714 ∧ 5+2 < 2*σ 0 1714 :=
  checkRule 1714 5 [1,2,857,1714]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1718 : 0 < 1718 ∧ 5+2 < 2*σ 0 1718 :=
  checkRule 1718 5 [1,2,859,1718]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1719 : 0 < 1719 ∧ 9+2 < 2*σ 0 1719 :=
  checkRule 1719 9 [1,3,9,191,573,1719]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1721 : 0 < 1721 ∧ 1+2 < 2*σ 0 1721 :=
  checkRule 1721 1 [1,1721]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1723 : 0 < 1723 ∧ 1+2 < 2*σ 0 1723 :=
  checkRule 1723 1 [1,1723]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1724 : 0 < 1724 ∧ 9+2 < 2*σ 0 1724 :=
  checkRule 1724 9 [1,2,4,431,862,1724]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1725 : 0 < 1725 ∧ 21+2 < 2*σ 0 1725 :=
  checkRule 1725 21 [1,3,5,15,23,25,69,75,115,345,575,1725]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1726 : 0 < 1726 ∧ 5+2 < 2*σ 0 1726 :=
  checkRule 1726 5 [1,2,863,1726]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1730 : 0 < 1730 ∧ 13+2 < 2*σ 0 1730 :=
  checkRule 1730 13 [1,2,5,10,173,346,865,1730]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1732 : 0 < 1732 ∧ 9+2 < 2*σ 0 1732 :=
  checkRule 1732 9 [1,2,4,433,866,1732]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1734 : 0 < 1734 ∧ 21+2 < 2*σ 0 1734 :=
  checkRule 1734 21 [1,2,3,6,17,34,51,102,289,578,867,1734]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1735 : 0 < 1735 ∧ 5+2 < 2*σ 0 1735 :=
  checkRule 1735 5 [1,5,347,1735]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1737 : 0 < 1737 ∧ 9+2 < 2*σ 0 1737 :=
  checkRule 1737 9 [1,3,9,193,579,1737]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1744 : 0 < 1744 ∧ 17+2 < 2*σ 0 1744 :=
  checkRule 1744 17 [1,2,4,8,16,109,218,436,872,1744]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1745 : 0 < 1745 ∧ 5+2 < 2*σ 0 1745 :=
  checkRule 1745 5 [1,5,349,1745]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1746 : 0 < 1746 ∧ 21+2 < 2*σ 0 1746 :=
  checkRule 1746 21 [1,2,3,6,9,18,97,194,291,582,873,1746]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1748 : 0 < 1748 ∧ 21+2 < 2*σ 0 1748 :=
  checkRule 1748 21 [1,2,4,19,23,38,46,76,92,437,874,1748]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1752 : 0 < 1752 ∧ 29+2 < 2*σ 0 1752 :=
  checkRule 1752 29 [1,2,3,4,6,8,12,24,73,146,219,292,438,584,876,1752]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1754 : 0 < 1754 ∧ 5+2 < 2*σ 0 1754 :=
  checkRule 1754 5 [1,2,877,1754]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1758 : 0 < 1758 ∧ 13+2 < 2*σ 0 1758 :=
  checkRule 1758 13 [1,2,3,6,293,586,879,1758]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1761 : 0 < 1761 ∧ 5+2 < 2*σ 0 1761 :=
  checkRule 1761 5 [1,3,587,1761]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1765 : 0 < 1765 ∧ 5+2 < 2*σ 0 1765 :=
  checkRule 1765 5 [1,5,353,1765]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1772 : 0 < 1772 ∧ 9+2 < 2*σ 0 1772 :=
  checkRule 1772 9 [1,2,4,443,886,1772]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1773 : 0 < 1773 ∧ 9+2 < 2*σ 0 1773 :=
  checkRule 1773 9 [1,3,9,197,591,1773]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1776 : 0 < 1776 ∧ 37+2 < 2*σ 0 1776 :=
  checkRule 1776 37 [1,2,3,4,6,8,12,16,24,37,48,74,111,148,222,296,444,592,888,1776]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1779 : 0 < 1779 ∧ 5+2 < 2*σ 0 1779 :=
  checkRule 1779 5 [1,3,593,1779]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1780 : 0 < 1780 ∧ 21+2 < 2*σ 0 1780 :=
  checkRule 1780 21 [1,2,4,5,10,20,89,178,356,445,890,1780]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1790 : 0 < 1790 ∧ 13+2 < 2*σ 0 1790 :=
  checkRule 1790 13 [1,2,5,10,179,358,895,1790]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1791 : 0 < 1791 ∧ 9+2 < 2*σ 0 1791 :=
  checkRule 1791 9 [1,3,9,199,597,1791]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1796 : 0 < 1796 ∧ 9+2 < 2*σ 0 1796 :=
  checkRule 1796 9 [1,2,4,449,898,1796]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1797 : 0 < 1797 ∧ 5+2 < 2*σ 0 1797 :=
  checkRule 1797 5 [1,3,599,1797]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1803 : 0 < 1803 ∧ 5+2 < 2*σ 0 1803 :=
  checkRule 1803 5 [1,3,601,1803]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1805 : 0 < 1805 ∧ 9+2 < 2*σ 0 1805 :=
  checkRule 1805 9 [1,5,19,95,361,1805]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1808 : 0 < 1808 ∧ 17+2 < 2*σ 0 1808 :=
  checkRule 1808 17 [1,2,4,8,16,113,226,452,904,1808]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1810 : 0 < 1810 ∧ 13+2 < 2*σ 0 1810 :=
  checkRule 1810 13 [1,2,5,10,181,362,905,1810]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1813 : 0 < 1813 ∧ 9+2 < 2*σ 0 1813 :=
  checkRule 1813 9 [1,7,37,49,259,1813]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1818 : 0 < 1818 ∧ 21+2 < 2*σ 0 1818 :=
  checkRule 1818 21 [1,2,3,6,9,18,101,202,303,606,909,1818]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1821 : 0 < 1821 ∧ 5+2 < 2*σ 0 1821 :=
  checkRule 1821 5 [1,3,607,1821]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1824 : 0 < 1824 ∧ 45+2 < 2*σ 0 1824 :=
  checkRule 1824 45 [1,2,3,4,6,8,12,16,19,24,32,38,48,57,76,96,114,152,228,304,456,608,912,1824]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1828 : 0 < 1828 ∧ 9+2 < 2*σ 0 1828 :=
  checkRule 1828 9 [1,2,4,457,914,1828]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1835 : 0 < 1835 ∧ 5+2 < 2*σ 0 1835 :=
  checkRule 1835 5 [1,5,367,1835]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1836 : 0 < 1836 ∧ 45+2 < 2*σ 0 1836 :=
  checkRule 1836 45 [1,2,3,4,6,9,12,17,18,27,34,36,51,54,68,102,108,153,204,306,459,612,918,1836]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1838 : 0 < 1838 ∧ 5+2 < 2*σ 0 1838 :=
  checkRule 1838 5 [1,2,919,1838]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1839 : 0 < 1839 ∧ 5+2 < 2*σ 0 1839 :=
  checkRule 1839 5 [1,3,613,1839]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1842 : 0 < 1842 ∧ 13+2 < 2*σ 0 1842 :=
  checkRule 1842 13 [1,2,3,6,307,614,921,1842]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1844 : 0 < 1844 ∧ 9+2 < 2*σ 0 1844 :=
  checkRule 1844 9 [1,2,4,461,922,1844]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1852 : 0 < 1852 ∧ 9+2 < 2*σ 0 1852 :=
  checkRule 1852 9 [1,2,4,463,926,1852]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1854 : 0 < 1854 ∧ 21+2 < 2*σ 0 1854 :=
  checkRule 1854 21 [1,2,3,6,9,18,103,206,309,618,927,1854]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1857 : 0 < 1857 ∧ 5+2 < 2*σ 0 1857 :=
  checkRule 1857 5 [1,3,619,1857]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1858 : 0 < 1858 ∧ 5+2 < 2*σ 0 1858 :=
  checkRule 1858 5 [1,2,929,1858]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1865 : 0 < 1865 ∧ 5+2 < 2*σ 0 1865 :=
  checkRule 1865 5 [1,5,373,1865]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1866 : 0 < 1866 ∧ 13+2 < 2*σ 0 1866 :=
  checkRule 1866 13 [1,2,3,6,311,622,933,1866]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1868 : 0 < 1868 ∧ 9+2 < 2*σ 0 1868 :=
  checkRule 1868 9 [1,2,4,467,934,1868]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1875 : 0 < 1875 ∧ 17+2 < 2*σ 0 1875 :=
  checkRule 1875 17 [1,3,5,15,25,75,125,375,625,1875]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1878 : 0 < 1878 ∧ 13+2 < 2*σ 0 1878 :=
  checkRule 1878 13 [1,2,3,6,313,626,939,1878]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1879 : 0 < 1879 ∧ 1+2 < 2*σ 0 1879 :=
  checkRule 1879 1 [1,1879]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1894 : 0 < 1894 ∧ 5+2 < 2*σ 0 1894 :=
  checkRule 1894 5 [1,2,947,1894]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1895 : 0 < 1895 ∧ 5+2 < 2*σ 0 1895 :=
  checkRule 1895 5 [1,5,379,1895]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1896 : 0 < 1896 ∧ 29+2 < 2*σ 0 1896 :=
  checkRule 1896 29 [1,2,3,4,6,8,12,24,79,158,237,316,474,632,948,1896]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1899 : 0 < 1899 ∧ 9+2 < 2*σ 0 1899 :=
  checkRule 1899 9 [1,3,9,211,633,1899]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1902 : 0 < 1902 ∧ 13+2 < 2*σ 0 1902 :=
  checkRule 1902 13 [1,2,3,6,317,634,951,1902]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1906 : 0 < 1906 ∧ 5+2 < 2*σ 0 1906 :=
  checkRule 1906 5 [1,2,953,1906]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1910 : 0 < 1910 ∧ 13+2 < 2*σ 0 1910 :=
  checkRule 1910 13 [1,2,5,10,191,382,955,1910]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1915 : 0 < 1915 ∧ 5+2 < 2*σ 0 1915 :=
  checkRule 1915 5 [1,5,383,1915]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1923 : 0 < 1923 ∧ 5+2 < 2*σ 0 1923 :=
  checkRule 1923 5 [1,3,641,1923]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1926 : 0 < 1926 ∧ 21+2 < 2*σ 0 1926 :=
  checkRule 1926 21 [1,2,3,6,9,18,107,214,321,642,963,1926]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1929 : 0 < 1929 ∧ 5+2 < 2*σ 0 1929 :=
  checkRule 1929 5 [1,3,643,1929]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1930 : 0 < 1930 ∧ 13+2 < 2*σ 0 1930 :=
  checkRule 1930 13 [1,2,5,10,193,386,965,1930]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1938 : 0 < 1938 ∧ 29+2 < 2*σ 0 1938 :=
  checkRule 1938 29 [1,2,3,6,17,19,34,38,51,57,102,114,323,646,969,1938]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1940 : 0 < 1940 ∧ 21+2 < 2*σ 0 1940 :=
  checkRule 1940 21 [1,2,4,5,10,20,97,194,388,485,970,1940]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1941 : 0 < 1941 ∧ 5+2 < 2*σ 0 1941 :=
  checkRule 1941 5 [1,3,647,1941]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1942 : 0 < 1942 ∧ 5+2 < 2*σ 0 1942 :=
  checkRule 1942 5 [1,2,971,1942]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1945 : 0 < 1945 ∧ 5+2 < 2*σ 0 1945 :=
  checkRule 1945 5 [1,5,389,1945]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1954 : 0 < 1954 ∧ 5+2 < 2*σ 0 1954 :=
  checkRule 1954 5 [1,2,977,1954]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1959 : 0 < 1959 ∧ 5+2 < 2*σ 0 1959 :=
  checkRule 1959 5 [1,3,653,1959]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1962 : 0 < 1962 ∧ 21+2 < 2*σ 0 1962 :=
  checkRule 1962 21 [1,2,3,6,9,18,109,218,327,654,981,1962]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1964 : 0 < 1964 ∧ 9+2 < 2*σ 0 1964 :=
  checkRule 1964 9 [1,2,4,491,982,1964]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1968 : 0 < 1968 ∧ 37+2 < 2*σ 0 1968 :=
  checkRule 1968 37 [1,2,3,4,6,8,12,16,24,41,48,82,123,164,246,328,492,656,984,1968]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1970 : 0 < 1970 ∧ 13+2 < 2*σ 0 1970 :=
  checkRule 1970 13 [1,2,5,10,197,394,985,1970]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1972 : 0 < 1972 ∧ 21+2 < 2*σ 0 1972 :=
  checkRule 1972 21 [1,2,4,17,29,34,58,68,116,493,986,1972]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1985 : 0 < 1985 ∧ 5+2 < 2*σ 0 1985 :=
  checkRule 1985 5 [1,5,397,1985]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1986 : 0 < 1986 ∧ 13+2 < 2*σ 0 1986 :=
  checkRule 1986 13 [1,2,3,6,331,662,993,1986]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1990 : 0 < 1990 ∧ 13+2 < 2*σ 0 1990 :=
  checkRule 1990 13 [1,2,5,10,199,398,995,1990]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1992 : 0 < 1992 ∧ 29+2 < 2*σ 0 1992 :=
  checkRule 1992 29 [1,2,3,4,6,8,12,24,83,166,249,332,498,664,996,1992]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_1996 : 0 < 1996 ∧ 9+2 < 2*σ 0 1996 :=
  checkRule 1996 9 [1,2,4,499,998,1996]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2005 : 0 < 2005 ∧ 5+2 < 2*σ 0 2005 :=
  checkRule 2005 5 [1,5,401,2005]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2007 : 0 < 2007 ∧ 9+2 < 2*σ 0 2007 :=
  checkRule 2007 9 [1,3,9,223,669,2007]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2009 : 0 < 2009 ∧ 9+2 < 2*σ 0 2009 :=
  checkRule 2009 9 [1,7,41,49,287,2009]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2020 : 0 < 2020 ∧ 21+2 < 2*σ 0 2020 :=
  checkRule 2020 21 [1,2,4,5,10,20,101,202,404,505,1010,2020]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2022 : 0 < 2022 ∧ 13+2 < 2*σ 0 2022 :=
  checkRule 2022 13 [1,2,3,6,337,674,1011,2022]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2023 : 0 < 2023 ∧ 9+2 < 2*σ 0 2023 :=
  checkRule 2023 9 [1,7,17,119,289,2023]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2031 : 0 < 2031 ∧ 5+2 < 2*σ 0 2031 :=
  checkRule 2031 5 [1,3,677,2031]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2032 : 0 < 2032 ∧ 17+2 < 2*σ 0 2032 :=
  checkRule 2032 17 [1,2,4,8,16,127,254,508,1016,2032]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2034 : 0 < 2034 ∧ 21+2 < 2*σ 0 2034 :=
  checkRule 2034 21 [1,2,3,6,9,18,113,226,339,678,1017,2034]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2042 : 0 < 2042 ∧ 5+2 < 2*σ 0 2042 :=
  checkRule 2042 5 [1,2,1021,2042]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2043 : 0 < 2043 ∧ 9+2 < 2*σ 0 2043 :=
  checkRule 2043 9 [1,3,9,227,681,2043]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2045 : 0 < 2045 ∧ 5+2 < 2*σ 0 2045 :=
  checkRule 2045 5 [1,5,409,2045]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2052 : 0 < 2052 ∧ 45+2 < 2*σ 0 2052 :=
  checkRule 2052 45 [1,2,3,4,6,9,12,18,19,27,36,38,54,57,76,108,114,171,228,342,513,684,1026,2052]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2060 : 0 < 2060 ∧ 21+2 < 2*σ 0 2060 :=
  checkRule 2060 21 [1,2,4,5,10,20,103,206,412,515,1030,2060]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2061 : 0 < 2061 ∧ 9+2 < 2*σ 0 2061 :=
  checkRule 2061 9 [1,3,9,229,687,2061]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2062 : 0 < 2062 ∧ 5+2 < 2*σ 0 2062 :=
  checkRule 2062 5 [1,2,1031,2062]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2064 : 0 < 2064 ∧ 37+2 < 2*σ 0 2064 :=
  checkRule 2064 37 [1,2,3,4,6,8,12,16,24,43,48,86,129,172,258,344,516,688,1032,2064]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2066 : 0 < 2066 ∧ 5+2 < 2*σ 0 2066 :=
  checkRule 2066 5 [1,2,1033,2066]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2078 : 0 < 2078 ∧ 5+2 < 2*σ 0 2078 :=
  checkRule 2078 5 [1,2,1039,2078]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2082 : 0 < 2082 ∧ 13+2 < 2*σ 0 2082 :=
  checkRule 2082 13 [1,2,3,6,347,694,1041,2082]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2094 : 0 < 2094 ∧ 13+2 < 2*σ 0 2094 :=
  checkRule 2094 13 [1,2,3,6,349,698,1047,2094]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2095 : 0 < 2095 ∧ 5+2 < 2*σ 0 2095 :=
  checkRule 2095 5 [1,5,419,2095]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2097 : 0 < 2097 ∧ 9+2 < 2*σ 0 2097 :=
  checkRule 2097 9 [1,3,9,233,699,2097]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2102 : 0 < 2102 ∧ 5+2 < 2*σ 0 2102 :=
  checkRule 2102 5 [1,2,1051,2102]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2103 : 0 < 2103 ∧ 5+2 < 2*σ 0 2103 :=
  checkRule 2103 5 [1,3,701,2103]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2105 : 0 < 2105 ∧ 5+2 < 2*σ 0 2105 :=
  checkRule 2105 5 [1,5,421,2105]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2108 : 0 < 2108 ∧ 21+2 < 2*σ 0 2108 :=
  checkRule 2108 21 [1,2,4,17,31,34,62,68,124,527,1054,2108]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2110 : 0 < 2110 ∧ 13+2 < 2*σ 0 2110 :=
  checkRule 2110 13 [1,2,5,10,211,422,1055,2110]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2118 : 0 < 2118 ∧ 13+2 < 2*σ 0 2118 :=
  checkRule 2118 13 [1,2,3,6,353,706,1059,2118]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2127 : 0 < 2127 ∧ 5+2 < 2*σ 0 2127 :=
  checkRule 2127 5 [1,3,709,2127]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2136 : 0 < 2136 ∧ 29+2 < 2*σ 0 2136 :=
  checkRule 2136 29 [1,2,3,4,6,8,12,24,89,178,267,356,534,712,1068,2136]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2138 : 0 < 2138 ∧ 5+2 < 2*σ 0 2138 :=
  checkRule 2138 5 [1,2,1069,2138]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2140 : 0 < 2140 ∧ 21+2 < 2*σ 0 2140 :=
  checkRule 2140 21 [1,2,4,5,10,20,107,214,428,535,1070,2140]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2151 : 0 < 2151 ∧ 9+2 < 2*σ 0 2151 :=
  checkRule 2151 9 [1,3,9,239,717,2151]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2154 : 0 < 2154 ∧ 13+2 < 2*σ 0 2154 :=
  checkRule 2154 13 [1,2,3,6,359,718,1077,2154]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2155 : 0 < 2155 ∧ 5+2 < 2*σ 0 2155 :=
  checkRule 2155 5 [1,5,431,2155]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2157 : 0 < 2157 ∧ 5+2 < 2*σ 0 2157 :=
  checkRule 2157 5 [1,3,719,2157]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2165 : 0 < 2165 ∧ 5+2 < 2*σ 0 2165 :=
  checkRule 2165 5 [1,5,433,2165]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2166 : 0 < 2166 ∧ 21+2 < 2*σ 0 2166 :=
  checkRule 2166 21 [1,2,3,6,19,38,57,114,361,722,1083,2166]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2169 : 0 < 2169 ∧ 9+2 < 2*σ 0 2169 :=
  checkRule 2169 9 [1,3,9,241,723,2169]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2175 : 0 < 2175 ∧ 21+2 < 2*σ 0 2175 :=
  checkRule 2175 21 [1,3,5,15,25,29,75,87,145,435,725,2175]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2179 : 0 < 2179 ∧ 1+2 < 2*σ 0 2179 :=
  checkRule 2179 1 [1,2179]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2180 : 0 < 2180 ∧ 21+2 < 2*σ 0 2180 :=
  checkRule 2180 21 [1,2,4,5,10,20,109,218,436,545,1090,2180]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2186 : 0 < 2186 ∧ 5+2 < 2*σ 0 2186 :=
  checkRule 2186 5 [1,2,1093,2186]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2188 : 0 < 2188 ∧ 9+2 < 2*σ 0 2188 :=
  checkRule 2188 9 [1,2,4,547,1094,2188]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2192 : 0 < 2192 ∧ 17+2 < 2*σ 0 2192 :=
  checkRule 2192 17 [1,2,4,8,16,137,274,548,1096,2192]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2195 : 0 < 2195 ∧ 5+2 < 2*σ 0 2195 :=
  checkRule 2195 5 [1,5,439,2195]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2202 : 0 < 2202 ∧ 13+2 < 2*σ 0 2202 :=
  checkRule 2202 13 [1,2,3,6,367,734,1101,2202]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2204 : 0 < 2204 ∧ 21+2 < 2*σ 0 2204 :=
  checkRule 2204 21 [1,2,4,19,29,38,58,76,116,551,1102,2204]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2208 : 0 < 2208 ∧ 45+2 < 2*σ 0 2208 :=
  checkRule 2208 45 [1,2,3,4,6,8,12,16,23,24,32,46,48,69,92,96,138,184,276,368,552,736,1104,2208]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2215 : 0 < 2215 ∧ 5+2 < 2*σ 0 2215 :=
  checkRule 2215 5 [1,5,443,2215]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2218 : 0 < 2218 ∧ 5+2 < 2*σ 0 2218 :=
  checkRule 2218 5 [1,2,1109,2218]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2228 : 0 < 2228 ∧ 9+2 < 2*σ 0 2228 :=
  checkRule 2228 9 [1,2,4,557,1114,2228]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2230 : 0 < 2230 ∧ 13+2 < 2*σ 0 2230 :=
  checkRule 2230 13 [1,2,5,10,223,446,1115,2230]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2238 : 0 < 2238 ∧ 13+2 < 2*σ 0 2238 :=
  checkRule 2238 13 [1,2,3,6,373,746,1119,2238]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2245 : 0 < 2245 ∧ 5+2 < 2*σ 0 2245 :=
  checkRule 2245 5 [1,5,449,2245]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2253 : 0 < 2253 ∧ 5+2 < 2*σ 0 2253 :=
  checkRule 2253 5 [1,3,751,2253]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2254 : 0 < 2254 ∧ 21+2 < 2*σ 0 2254 :=
  checkRule 2254 21 [1,2,7,14,23,46,49,98,161,322,1127,2254]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2256 : 0 < 2256 ∧ 37+2 < 2*σ 0 2256 :=
  checkRule 2256 37 [1,2,3,4,6,8,12,16,24,47,48,94,141,188,282,376,564,752,1128,2256]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2258 : 0 < 2258 ∧ 5+2 < 2*σ 0 2258 :=
  checkRule 2258 5 [1,2,1129,2258]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2259 : 0 < 2259 ∧ 9+2 < 2*σ 0 2259 :=
  checkRule 2259 9 [1,3,9,251,753,2259]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2260 : 0 < 2260 ∧ 21+2 < 2*σ 0 2260 :=
  checkRule 2260 21 [1,2,4,5,10,20,113,226,452,565,1130,2260]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2261 : 0 < 2261 ∧ 13+2 < 2*σ 0 2261 :=
  checkRule 2261 13 [1,7,17,19,119,133,323,2261]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2270 : 0 < 2270 ∧ 13+2 < 2*σ 0 2270 :=
  checkRule 2270 13 [1,2,5,10,227,454,1135,2270]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2274 : 0 < 2274 ∧ 13+2 < 2*σ 0 2274 :=
  checkRule 2274 13 [1,2,3,6,379,758,1137,2274]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2276 : 0 < 2276 ∧ 9+2 < 2*σ 0 2276 :=
  checkRule 2276 9 [1,2,4,569,1138,2276]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2283 : 0 < 2283 ∧ 5+2 < 2*σ 0 2283 :=
  checkRule 2283 5 [1,3,761,2283]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2285 : 0 < 2285 ∧ 5+2 < 2*σ 0 2285 :=
  checkRule 2285 5 [1,5,457,2285]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2286 : 0 < 2286 ∧ 21+2 < 2*σ 0 2286 :=
  checkRule 2286 21 [1,2,3,6,9,18,127,254,381,762,1143,2286]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2290 : 0 < 2290 ∧ 13+2 < 2*σ 0 2290 :=
  checkRule 2290 13 [1,2,5,10,229,458,1145,2290]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2297 : 0 < 2297 ∧ 1+2 < 2*σ 0 2297 :=
  checkRule 2297 1 [1,2297]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2298 : 0 < 2298 ∧ 13+2 < 2*σ 0 2298 :=
  checkRule 2298 13 [1,2,3,6,383,766,1149,2298]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2303 : 0 < 2303 ∧ 9+2 < 2*σ 0 2303 :=
  checkRule 2303 9 [1,7,47,49,329,2303]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2306 : 0 < 2306 ∧ 5+2 < 2*σ 0 2306 :=
  checkRule 2306 5 [1,2,1153,2306]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2307 : 0 < 2307 ∧ 5+2 < 2*σ 0 2307 :=
  checkRule 2307 5 [1,3,769,2307]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2308 : 0 < 2308 ∧ 9+2 < 2*σ 0 2308 :=
  checkRule 2308 9 [1,2,4,577,1154,2308]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2312 : 0 < 2312 ∧ 21+2 < 2*σ 0 2312 :=
  checkRule 2312 21 [1,2,4,8,17,34,68,136,289,578,1156,2312]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2313 : 0 < 2313 ∧ 9+2 < 2*σ 0 2313 :=
  checkRule 2313 9 [1,3,9,257,771,2313]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2315 : 0 < 2315 ∧ 5+2 < 2*σ 0 2315 :=
  checkRule 2315 5 [1,5,463,2315]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2325 : 0 < 2325 ∧ 21+2 < 2*σ 0 2325 :=
  checkRule 2325 21 [1,3,5,15,25,31,75,93,155,465,775,2325]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2328 : 0 < 2328 ∧ 29+2 < 2*σ 0 2328 :=
  checkRule 2328 29 [1,2,3,4,6,8,12,24,97,194,291,388,582,776,1164,2328]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2330 : 0 < 2330 ∧ 13+2 < 2*σ 0 2330 :=
  checkRule 2330 13 [1,2,5,10,233,466,1165,2330]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2334 : 0 < 2334 ∧ 13+2 < 2*σ 0 2334 :=
  checkRule 2334 13 [1,2,3,6,389,778,1167,2334]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2339 : 0 < 2339 ∧ 1+2 < 2*σ 0 2339 :=
  checkRule 2339 1 [1,2339]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2346 : 0 < 2346 ∧ 29+2 < 2*σ 0 2346 :=
  checkRule 2346 29 [1,2,3,6,17,23,34,46,51,69,102,138,391,782,1173,2346]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2348 : 0 < 2348 ∧ 9+2 < 2*σ 0 2348 :=
  checkRule 2348 9 [1,2,4,587,1174,2348]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2351 : 0 < 2351 ∧ 1+2 < 2*σ 0 2351 :=
  checkRule 2351 1 [1,2351]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2356 : 0 < 2356 ∧ 21+2 < 2*σ 0 2356 :=
  checkRule 2356 21 [1,2,4,19,31,38,62,76,124,589,1178,2356]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2358 : 0 < 2358 ∧ 21+2 < 2*σ 0 2358 :=
  checkRule 2358 21 [1,2,3,6,9,18,131,262,393,786,1179,2358]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2367 : 0 < 2367 ∧ 9+2 < 2*σ 0 2367 :=
  checkRule 2367 9 [1,3,9,263,789,2367]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2372 : 0 < 2372 ∧ 9+2 < 2*σ 0 2372 :=
  checkRule 2372 9 [1,2,4,593,1186,2372]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2374 : 0 < 2374 ∧ 5+2 < 2*σ 0 2374 :=
  checkRule 2374 5 [1,2,1187,2374]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2382 : 0 < 2382 ∧ 13+2 < 2*σ 0 2382 :=
  checkRule 2382 13 [1,2,3,6,397,794,1191,2382]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2384 : 0 < 2384 ∧ 17+2 < 2*σ 0 2384 :=
  checkRule 2384 17 [1,2,4,8,16,149,298,596,1192,2384]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2390 : 0 < 2390 ∧ 13+2 < 2*σ 0 2390 :=
  checkRule 2390 13 [1,2,5,10,239,478,1195,2390]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2391 : 0 < 2391 ∧ 5+2 < 2*σ 0 2391 :=
  checkRule 2391 5 [1,3,797,2391]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2395 : 0 < 2395 ∧ 5+2 < 2*σ 0 2395 :=
  checkRule 2395 5 [1,5,479,2395]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2396 : 0 < 2396 ∧ 9+2 < 2*σ 0 2396 :=
  checkRule 2396 9 [1,2,4,599,1198,2396]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2402 : 0 < 2402 ∧ 5+2 < 2*σ 0 2402 :=
  checkRule 2402 5 [1,2,1201,2402]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2406 : 0 < 2406 ∧ 13+2 < 2*σ 0 2406 :=
  checkRule 2406 13 [1,2,3,6,401,802,1203,2406]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2410 : 0 < 2410 ∧ 13+2 < 2*σ 0 2410 :=
  checkRule 2410 13 [1,2,5,10,241,482,1205,2410]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2417 : 0 < 2417 ∧ 1+2 < 2*σ 0 2417 :=
  checkRule 2417 1 [1,2417]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2421 : 0 < 2421 ∧ 9+2 < 2*σ 0 2421 :=
  checkRule 2421 9 [1,3,9,269,807,2421]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2424 : 0 < 2424 ∧ 29+2 < 2*σ 0 2424 :=
  checkRule 2424 29 [1,2,3,4,6,8,12,24,101,202,303,404,606,808,1212,2424]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2426 : 0 < 2426 ∧ 5+2 < 2*σ 0 2426 :=
  checkRule 2426 5 [1,2,1213,2426]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2428 : 0 < 2428 ∧ 9+2 < 2*σ 0 2428 :=
  checkRule 2428 9 [1,2,4,607,1214,2428]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2435 : 0 < 2435 ∧ 5+2 < 2*σ 0 2435 :=
  checkRule 2435 5 [1,5,487,2435]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2439 : 0 < 2439 ∧ 9+2 < 2*σ 0 2439 :=
  checkRule 2439 9 [1,3,9,271,813,2439]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2452 : 0 < 2452 ∧ 9+2 < 2*σ 0 2452 :=
  checkRule 2452 9 [1,2,4,613,1226,2452]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2454 : 0 < 2454 ∧ 13+2 < 2*σ 0 2454 :=
  checkRule 2454 13 [1,2,3,6,409,818,1227,2454]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2455 : 0 < 2455 ∧ 5+2 < 2*σ 0 2455 :=
  checkRule 2455 5 [1,5,491,2455]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2458 : 0 < 2458 ∧ 5+2 < 2*σ 0 2458 :=
  checkRule 2458 5 [1,2,1229,2458]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2463 : 0 < 2463 ∧ 5+2 < 2*σ 0 2463 :=
  checkRule 2463 5 [1,3,821,2463]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2466 : 0 < 2466 ∧ 21+2 < 2*σ 0 2466 :=
  checkRule 2466 21 [1,2,3,6,9,18,137,274,411,822,1233,2466]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2469 : 0 < 2469 ∧ 5+2 < 2*σ 0 2469 :=
  checkRule 2469 5 [1,3,823,2469]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2472 : 0 < 2472 ∧ 29+2 < 2*σ 0 2472 :=
  checkRule 2472 29 [1,2,3,4,6,8,12,24,103,206,309,412,618,824,1236,2472]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2484 : 0 < 2484 ∧ 45+2 < 2*σ 0 2484 :=
  checkRule 2484 45 [1,2,3,4,6,9,12,18,23,27,36,46,54,69,92,108,138,207,276,414,621,828,1242,2484]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2493 : 0 < 2493 ∧ 9+2 < 2*σ 0 2493 :=
  checkRule 2493 9 [1,3,9,277,831,2493]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2495 : 0 < 2495 ∧ 5+2 < 2*σ 0 2495 :=
  checkRule 2495 5 [1,5,499,2495]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2499 : 0 < 2499 ∧ 21+2 < 2*σ 0 2499 :=
  checkRule 2499 21 [1,3,7,17,21,49,51,119,147,357,833,2499]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2500 : 0 < 2500 ∧ 27+2 < 2*σ 0 2500 :=
  checkRule 2500 27 [1,2,4,5,10,20,25,50,100,125,250,500,625,1250,2500]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2502 : 0 < 2502 ∧ 21+2 < 2*σ 0 2502 :=
  checkRule 2502 21 [1,2,3,6,9,18,139,278,417,834,1251,2502]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2510 : 0 < 2510 ∧ 13+2 < 2*σ 0 2510 :=
  checkRule 2510 13 [1,2,5,10,251,502,1255,2510]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2512 : 0 < 2512 ∧ 17+2 < 2*σ 0 2512 :=
  checkRule 2512 17 [1,2,4,8,16,157,314,628,1256,2512]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2514 : 0 < 2514 ∧ 13+2 < 2*σ 0 2514 :=
  checkRule 2514 13 [1,2,3,6,419,838,1257,2514]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2515 : 0 < 2515 ∧ 5+2 < 2*σ 0 2515 :=
  checkRule 2515 5 [1,5,503,2515]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2516 : 0 < 2516 ∧ 21+2 < 2*σ 0 2516 :=
  checkRule 2516 21 [1,2,4,17,34,37,68,74,148,629,1258,2516]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2518 : 0 < 2518 ∧ 5+2 < 2*σ 0 2518 :=
  checkRule 2518 5 [1,2,1259,2518]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2526 : 0 < 2526 ∧ 13+2 < 2*σ 0 2526 :=
  checkRule 2526 13 [1,2,3,6,421,842,1263,2526]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2527 : 0 < 2527 ∧ 9+2 < 2*σ 0 2527 :=
  checkRule 2527 9 [1,7,19,133,361,2527]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2529 : 0 < 2529 ∧ 9+2 < 2*σ 0 2529 :=
  checkRule 2529 9 [1,3,9,281,843,2529]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2539 : 0 < 2539 ∧ 1+2 < 2*σ 0 2539 :=
  checkRule 2539 1 [1,2539]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2540 : 0 < 2540 ∧ 21+2 < 2*σ 0 2540 :=
  checkRule 2540 21 [1,2,4,5,10,20,127,254,508,635,1270,2540]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2545 : 0 < 2545 ∧ 5+2 < 2*σ 0 2545 :=
  checkRule 2545 5 [1,5,509,2545]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2547 : 0 < 2547 ∧ 9+2 < 2*σ 0 2547 :=
  checkRule 2547 9 [1,3,9,283,849,2547]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2558 : 0 < 2558 ∧ 5+2 < 2*σ 0 2558 :=
  checkRule 2558 5 [1,2,1279,2558]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2568 : 0 < 2568 ∧ 29+2 < 2*σ 0 2568 :=
  checkRule 2568 29 [1,2,3,4,6,8,12,24,107,214,321,428,642,856,1284,2568]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2570 : 0 < 2570 ∧ 13+2 < 2*σ 0 2570 :=
  checkRule 2570 13 [1,2,5,10,257,514,1285,2570]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2572 : 0 < 2572 ∧ 9+2 < 2*σ 0 2572 :=
  checkRule 2572 9 [1,2,4,643,1286,2572]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2578 : 0 < 2578 ∧ 5+2 < 2*σ 0 2578 :=
  checkRule 2578 5 [1,2,1289,2578]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2586 : 0 < 2586 ∧ 13+2 < 2*σ 0 2586 :=
  checkRule 2586 13 [1,2,3,6,431,862,1293,2586]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2588 : 0 < 2588 ∧ 9+2 < 2*σ 0 2588 :=
  checkRule 2588 9 [1,2,4,647,1294,2588]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2589 : 0 < 2589 ∧ 5+2 < 2*σ 0 2589 :=
  checkRule 2589 5 [1,3,863,2589]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2594 : 0 < 2594 ∧ 5+2 < 2*σ 0 2594 :=
  checkRule 2594 5 [1,2,1297,2594]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2598 : 0 < 2598 ∧ 13+2 < 2*σ 0 2598 :=
  checkRule 2598 13 [1,2,3,6,433,866,1299,2598]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2605 : 0 < 2605 ∧ 5+2 < 2*σ 0 2605 :=
  checkRule 2605 5 [1,5,521,2605]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2606 : 0 < 2606 ∧ 5+2 < 2*σ 0 2606 :=
  checkRule 2606 5 [1,2,1303,2606]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2608 : 0 < 2608 ∧ 17+2 < 2*σ 0 2608 :=
  checkRule 2608 17 [1,2,4,8,16,163,326,652,1304,2608]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2612 : 0 < 2612 ∧ 9+2 < 2*σ 0 2612 :=
  checkRule 2612 9 [1,2,4,653,1306,2612]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2615 : 0 < 2615 ∧ 5+2 < 2*σ 0 2615 :=
  checkRule 2615 5 [1,5,523,2615]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2616 : 0 < 2616 ∧ 29+2 < 2*σ 0 2616 :=
  checkRule 2616 29 [1,2,3,4,6,8,12,24,109,218,327,436,654,872,1308,2616]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2620 : 0 < 2620 ∧ 21+2 < 2*σ 0 2620 :=
  checkRule 2620 21 [1,2,4,5,10,20,131,262,524,655,1310,2620]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2622 : 0 < 2622 ∧ 29+2 < 2*σ 0 2622 :=
  checkRule 2622 29 [1,2,3,6,19,23,38,46,57,69,114,138,437,874,1311,2622]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2630 : 0 < 2630 ∧ 13+2 < 2*σ 0 2630 :=
  checkRule 2630 13 [1,2,5,10,263,526,1315,2630]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2633 : 0 < 2633 ∧ 1+2 < 2*σ 0 2633 :=
  checkRule 2633 1 [1,2633]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2634 : 0 < 2634 ∧ 13+2 < 2*σ 0 2634 :=
  checkRule 2634 13 [1,2,3,6,439,878,1317,2634]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2636 : 0 < 2636 ∧ 9+2 < 2*σ 0 2636 :=
  checkRule 2636 9 [1,2,4,659,1318,2636]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2637 : 0 < 2637 ∧ 9+2 < 2*σ 0 2637 :=
  checkRule 2637 9 [1,3,9,293,879,2637]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2638 : 0 < 2638 ∧ 5+2 < 2*σ 0 2638 :=
  checkRule 2638 5 [1,2,1319,2638]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2654 : 0 < 2654 ∧ 5+2 < 2*σ 0 2654 :=
  checkRule 2654 5 [1,2,1327,2654]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2658 : 0 < 2658 ∧ 13+2 < 2*σ 0 2658 :=
  checkRule 2658 13 [1,2,3,6,443,886,1329,2658]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2668 : 0 < 2668 ∧ 21+2 < 2*σ 0 2668 :=
  checkRule 2668 21 [1,2,4,23,29,46,58,92,116,667,1334,2668]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2672 : 0 < 2672 ∧ 17+2 < 2*σ 0 2672 :=
  checkRule 2672 17 [1,2,4,8,16,167,334,668,1336,2672]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2682 : 0 < 2682 ∧ 21+2 < 2*σ 0 2682 :=
  checkRule 2682 21 [1,2,3,6,9,18,149,298,447,894,1341,2682]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2683 : 0 < 2683 ∧ 1+2 < 2*σ 0 2683 :=
  checkRule 2683 1 [1,2683]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2690 : 0 < 2690 ∧ 13+2 < 2*σ 0 2690 :=
  checkRule 2690 13 [1,2,5,10,269,538,1345,2690]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2693 : 0 < 2693 ∧ 1+2 < 2*σ 0 2693 :=
  checkRule 2693 1 [1,2693]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2694 : 0 < 2694 ∧ 13+2 < 2*σ 0 2694 :=
  checkRule 2694 13 [1,2,3,6,449,898,1347,2694]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2699 : 0 < 2699 ∧ 1+2 < 2*σ 0 2699 :=
  checkRule 2699 1 [1,2699]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2705 : 0 < 2705 ∧ 5+2 < 2*σ 0 2705 :=
  checkRule 2705 5 [1,5,541,2705]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2710 : 0 < 2710 ∧ 13+2 < 2*σ 0 2710 :=
  checkRule 2710 13 [1,2,5,10,271,542,1355,2710]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2712 : 0 < 2712 ∧ 29+2 < 2*σ 0 2712 :=
  checkRule 2712 29 [1,2,3,4,6,8,12,24,113,226,339,452,678,904,1356,2712]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2713 : 0 < 2713 ∧ 1+2 < 2*σ 0 2713 :=
  checkRule 2713 1 [1,2713]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2718 : 0 < 2718 ∧ 21+2 < 2*σ 0 2718 :=
  checkRule 2718 21 [1,2,3,6,9,18,151,302,453,906,1359,2718]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2720 : 0 < 2720 ∧ 45+2 < 2*σ 0 2720 :=
  checkRule 2720 45 [1,2,4,5,8,10,16,17,20,32,34,40,68,80,85,136,160,170,272,340,544,680,1360,2720]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2735 : 0 < 2735 ∧ 5+2 < 2*σ 0 2735 :=
  checkRule 2735 5 [1,5,547,2735]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2737 : 0 < 2737 ∧ 13+2 < 2*σ 0 2737 :=
  checkRule 2737 13 [1,7,17,23,119,161,391,2737]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2740 : 0 < 2740 ∧ 21+2 < 2*σ 0 2740 :=
  checkRule 2740 21 [1,2,4,5,10,20,137,274,548,685,1370,2740]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2742 : 0 < 2742 ∧ 13+2 < 2*σ 0 2742 :=
  checkRule 2742 13 [1,2,3,6,457,914,1371,2742]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2753 : 0 < 2753 ∧ 1+2 < 2*σ 0 2753 :=
  checkRule 2753 1 [1,2753]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2762 : 0 < 2762 ∧ 5+2 < 2*σ 0 2762 :=
  checkRule 2762 5 [1,2,1381,2762]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2763 : 0 < 2763 ∧ 9+2 < 2*σ 0 2763 :=
  checkRule 2763 9 [1,3,9,307,921,2763]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2764 : 0 < 2764 ∧ 9+2 < 2*σ 0 2764 :=
  checkRule 2764 9 [1,2,4,691,1382,2764]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2766 : 0 < 2766 ∧ 13+2 < 2*σ 0 2766 :=
  checkRule 2766 13 [1,2,3,6,461,922,1383,2766]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2768 : 0 < 2768 ∧ 17+2 < 2*σ 0 2768 :=
  checkRule 2768 17 [1,2,4,8,16,173,346,692,1384,2768]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2770 : 0 < 2770 ∧ 13+2 < 2*σ 0 2770 :=
  checkRule 2770 13 [1,2,5,10,277,554,1385,2770]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2775 : 0 < 2775 ∧ 21+2 < 2*σ 0 2775 :=
  checkRule 2775 21 [1,3,5,15,25,37,75,111,185,555,925,2775]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2778 : 0 < 2778 ∧ 13+2 < 2*σ 0 2778 :=
  checkRule 2778 13 [1,2,3,6,463,926,1389,2778]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2780 : 0 < 2780 ∧ 21+2 < 2*σ 0 2780 :=
  checkRule 2780 21 [1,2,4,5,10,20,139,278,556,695,1390,2780]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2785 : 0 < 2785 ∧ 5+2 < 2*σ 0 2785 :=
  checkRule 2785 5 [1,5,557,2785]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2787 : 0 < 2787 ∧ 5+2 < 2*σ 0 2787 :=
  checkRule 2787 5 [1,3,929,2787]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2788 : 0 < 2788 ∧ 21+2 < 2*σ 0 2788 :=
  checkRule 2788 21 [1,2,4,17,34,41,68,82,164,697,1394,2788]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2791 : 0 < 2791 ∧ 1+2 < 2*σ 0 2791 :=
  checkRule 2791 1 [1,2791]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2793 : 0 < 2793 ∧ 21+2 < 2*σ 0 2793 :=
  checkRule 2793 21 [1,3,7,19,21,49,57,133,147,399,931,2793]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2798 : 0 < 2798 ∧ 5+2 < 2*σ 0 2798 :=
  checkRule 2798 5 [1,2,1399,2798]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2799 : 0 < 2799 ∧ 9+2 < 2*σ 0 2799 :=
  checkRule 2799 9 [1,3,9,311,933,2799]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2802 : 0 < 2802 ∧ 13+2 < 2*σ 0 2802 :=
  checkRule 2802 13 [1,2,3,6,467,934,1401,2802]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2810 : 0 < 2810 ∧ 13+2 < 2*σ 0 2810 :=
  checkRule 2810 13 [1,2,5,10,281,562,1405,2810]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2812 : 0 < 2812 ∧ 21+2 < 2*σ 0 2812 :=
  checkRule 2812 21 [1,2,4,19,37,38,74,76,148,703,1406,2812]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2815 : 0 < 2815 ∧ 5+2 < 2*σ 0 2815 :=
  checkRule 2815 5 [1,5,563,2815]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2817 : 0 < 2817 ∧ 9+2 < 2*σ 0 2817 :=
  checkRule 2817 9 [1,3,9,313,939,2817]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2818 : 0 < 2818 ∧ 5+2 < 2*σ 0 2818 :=
  checkRule 2818 5 [1,2,1409,2818]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2823 : 0 < 2823 ∧ 5+2 < 2*σ 0 2823 :=
  checkRule 2823 5 [1,3,941,2823]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2826 : 0 < 2826 ∧ 21+2 < 2*σ 0 2826 :=
  checkRule 2826 21 [1,2,3,6,9,18,157,314,471,942,1413,2826]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2830 : 0 < 2830 ∧ 13+2 < 2*σ 0 2830 :=
  checkRule 2830 13 [1,2,5,10,283,566,1415,2830]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2836 : 0 < 2836 ∧ 9+2 < 2*σ 0 2836 :=
  checkRule 2836 9 [1,2,4,709,1418,2836]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2841 : 0 < 2841 ∧ 5+2 < 2*σ 0 2841 :=
  checkRule 2841 5 [1,3,947,2841]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2842 : 0 < 2842 ∧ 21+2 < 2*σ 0 2842 :=
  checkRule 2842 21 [1,2,7,14,29,49,58,98,203,406,1421,2842]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2845 : 0 < 2845 ∧ 5+2 < 2*σ 0 2845 :=
  checkRule 2845 5 [1,5,569,2845]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2850 : 0 < 2850 ∧ 45+2 < 2*σ 0 2850 :=
  checkRule 2850 45 [1,2,3,5,6,10,15,19,25,30,38,50,57,75,95,114,150,190,285,475,570,950,1425,2850]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2852 : 0 < 2852 ∧ 21+2 < 2*σ 0 2852 :=
  checkRule 2852 21 [1,2,4,23,31,46,62,92,124,713,1426,2852]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2853 : 0 < 2853 ∧ 9+2 < 2*σ 0 2853 :=
  checkRule 2853 9 [1,3,9,317,951,2853]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2864 : 0 < 2864 ∧ 17+2 < 2*σ 0 2864 :=
  checkRule 2864 17 [1,2,4,8,16,179,358,716,1432,2864]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2866 : 0 < 2866 ∧ 5+2 < 2*σ 0 2866 :=
  checkRule 2866 5 [1,2,1433,2866]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2874 : 0 < 2874 ∧ 13+2 < 2*σ 0 2874 :=
  checkRule 2874 13 [1,2,3,6,479,958,1437,2874]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2876 : 0 < 2876 ∧ 9+2 < 2*σ 0 2876 :=
  checkRule 2876 9 [1,2,4,719,1438,2876]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2888 : 0 < 2888 ∧ 21+2 < 2*σ 0 2888 :=
  checkRule 2888 21 [1,2,4,8,19,38,76,152,361,722,1444,2888]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2890 : 0 < 2890 ∧ 21+2 < 2*σ 0 2890 :=
  checkRule 2890 21 [1,2,5,10,17,34,85,170,289,578,1445,2890]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2894 : 0 < 2894 ∧ 5+2 < 2*σ 0 2894 :=
  checkRule 2894 5 [1,2,1447,2894]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2901 : 0 < 2901 ∧ 5+2 < 2*σ 0 2901 :=
  checkRule 2901 5 [1,3,967,2901]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2916 : 0 < 2916 ∧ 39+2 < 2*σ 0 2916 :=
  checkRule 2916 39 [1,2,3,4,6,9,12,18,27,36,54,81,108,162,243,324,486,729,972,1458,2916]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2922 : 0 < 2922 ∧ 13+2 < 2*σ 0 2922 :=
  checkRule 2922 13 [1,2,3,6,487,974,1461,2922]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2924 : 0 < 2924 ∧ 21+2 < 2*σ 0 2924 :=
  checkRule 2924 21 [1,2,4,17,34,43,68,86,172,731,1462,2924]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2930 : 0 < 2930 ∧ 13+2 < 2*σ 0 2930 :=
  checkRule 2930 13 [1,2,5,10,293,586,1465,2930]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2932 : 0 < 2932 ∧ 9+2 < 2*σ 0 2932 :=
  checkRule 2932 9 [1,2,4,733,1466,2932]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2934 : 0 < 2934 ∧ 21+2 < 2*σ 0 2934 :=
  checkRule 2934 21 [1,2,3,6,9,18,163,326,489,978,1467,2934]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2946 : 0 < 2946 ∧ 13+2 < 2*σ 0 2946 :=
  checkRule 2946 13 [1,2,3,6,491,982,1473,2946]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2949 : 0 < 2949 ∧ 5+2 < 2*σ 0 2949 :=
  checkRule 2949 5 [1,3,983,2949]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2956 : 0 < 2956 ∧ 9+2 < 2*σ 0 2956 :=
  checkRule 2956 9 [1,2,4,739,1478,2956]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2958 : 0 < 2958 ∧ 29+2 < 2*σ 0 2958 :=
  checkRule 2958 29 [1,2,3,6,17,29,34,51,58,87,102,174,493,986,1479,2958]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2978 : 0 < 2978 ∧ 5+2 < 2*σ 0 2978 :=
  checkRule 2978 5 [1,2,1489,2978]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2979 : 0 < 2979 ∧ 9+2 < 2*σ 0 2979 :=
  checkRule 2979 9 [1,3,9,331,993,2979]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2980 : 0 < 2980 ∧ 21+2 < 2*σ 0 2980 :=
  checkRule 2980 21 [1,2,4,5,10,20,149,298,596,745,1490,2980]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2994 : 0 < 2994 ∧ 13+2 < 2*σ 0 2994 :=
  checkRule 2994 13 [1,2,3,6,499,998,1497,2994]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2995 : 0 < 2995 ∧ 5+2 < 2*σ 0 2995 :=
  checkRule 2995 5 [1,5,599,2995]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_2999 : 0 < 2999 ∧ 1+2 < 2*σ 0 2999 :=
  checkRule 2999 1 [1,2999]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3006 : 0 < 3006 ∧ 21+2 < 2*σ 0 3006 :=
  checkRule 3006 21 [1,2,3,6,9,18,167,334,501,1002,1503,3006]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3018 : 0 < 3018 ∧ 13+2 < 2*σ 0 3018 :=
  checkRule 3018 13 [1,2,3,6,503,1006,1509,3018]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3020 : 0 < 3020 ∧ 21+2 < 2*σ 0 3020 :=
  checkRule 3020 21 [1,2,4,5,10,20,151,302,604,755,1510,3020]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3033 : 0 < 3033 ∧ 9+2 < 2*σ 0 3033 :=
  checkRule 3033 9 [1,3,9,337,1011,3033]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3040 : 0 < 3040 ∧ 45+2 < 2*σ 0 3040 :=
  checkRule 3040 45 [1,2,4,5,8,10,16,19,20,32,38,40,76,80,95,152,160,190,304,380,608,760,1520,3040]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3046 : 0 < 3046 ∧ 5+2 < 2*σ 0 3046 :=
  checkRule 3046 5 [1,2,1523,3046]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3048 : 0 < 3048 ∧ 29+2 < 2*σ 0 3048 :=
  checkRule 3048 29 [1,2,3,4,6,8,12,24,127,254,381,508,762,1016,1524,3048]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3054 : 0 < 3054 ∧ 13+2 < 2*σ 0 3054 :=
  checkRule 3054 13 [1,2,3,6,509,1018,1527,3054]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3056 : 0 < 3056 ∧ 17+2 < 2*σ 0 3056 :=
  checkRule 3056 17 [1,2,4,8,16,191,382,764,1528,3056]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3057 : 0 < 3057 ∧ 5+2 < 2*σ 0 3057 :=
  checkRule 3057 5 [1,3,1019,3057]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3059 : 0 < 3059 ∧ 13+2 < 2*σ 0 3059 :=
  checkRule 3059 13 [1,7,19,23,133,161,437,3059]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3062 : 0 < 3062 ∧ 5+2 < 2*σ 0 3062 :=
  checkRule 3062 5 [1,2,1531,3062]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3070 : 0 < 3070 ∧ 13+2 < 2*σ 0 3070 :=
  checkRule 3070 13 [1,2,5,10,307,614,1535,3070]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3075 : 0 < 3075 ∧ 21+2 < 2*σ 0 3075 :=
  checkRule 3075 21 [1,3,5,15,25,41,75,123,205,615,1025,3075]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3076 : 0 < 3076 ∧ 9+2 < 2*σ 0 3076 :=
  checkRule 3076 9 [1,2,4,769,1538,3076]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3085 : 0 < 3085 ∧ 5+2 < 2*σ 0 3085 :=
  checkRule 3085 5 [1,5,617,3085]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3088 : 0 < 3088 ∧ 17+2 < 2*σ 0 3088 :=
  checkRule 3088 17 [1,2,4,8,16,193,386,772,1544,3088]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3099 : 0 < 3099 ∧ 5+2 < 2*σ 0 3099 :=
  checkRule 3099 5 [1,3,1033,3099]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3110 : 0 < 3110 ∧ 13+2 < 2*σ 0 3110 :=
  checkRule 3110 13 [1,2,5,10,311,622,1555,3110]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3114 : 0 < 3114 ∧ 21+2 < 2*σ 0 3114 :=
  checkRule 3114 21 [1,2,3,6,9,18,173,346,519,1038,1557,3114]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3123 : 0 < 3123 ∧ 9+2 < 2*σ 0 3123 :=
  checkRule 3123 9 [1,3,9,347,1041,3123]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3126 : 0 < 3126 ∧ 13+2 < 2*σ 0 3126 :=
  checkRule 3126 13 [1,2,3,6,521,1042,1563,3126]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3130 : 0 < 3130 ∧ 13+2 < 2*σ 0 3130 :=
  checkRule 3130 13 [1,2,5,10,313,626,1565,3130]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3132 : 0 < 3132 ∧ 45+2 < 2*σ 0 3132 :=
  checkRule 3132 45 [1,2,3,4,6,9,12,18,27,29,36,54,58,87,108,116,174,261,348,522,783,1044,1566,3132]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3138 : 0 < 3138 ∧ 13+2 < 2*σ 0 3138 :=
  checkRule 3138 13 [1,2,3,6,523,1046,1569,3138]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3140 : 0 < 3140 ∧ 21+2 < 2*σ 0 3140 :=
  checkRule 3140 21 [1,2,4,5,10,20,157,314,628,785,1570,3140]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3141 : 0 < 3141 ∧ 9+2 < 2*σ 0 3141 :=
  checkRule 3141 9 [1,3,9,349,1047,3141]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3144 : 0 < 3144 ∧ 29+2 < 2*σ 0 3144 :=
  checkRule 3144 29 [1,2,3,4,6,8,12,24,131,262,393,524,786,1048,1572,3144]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3147 : 0 < 3147 ∧ 5+2 < 2*σ 0 3147 :=
  checkRule 3147 5 [1,3,1049,3147]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3155 : 0 < 3155 ∧ 5+2 < 2*σ 0 3155 :=
  checkRule 3155 5 [1,5,631,3155]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3170 : 0 < 3170 ∧ 13+2 < 2*σ 0 3170 :=
  checkRule 3170 13 [1,2,5,10,317,634,1585,3170]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3177 : 0 < 3177 ∧ 9+2 < 2*σ 0 3177 :=
  checkRule 3177 9 [1,3,9,353,1059,3177]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3188 : 0 < 3188 ∧ 9+2 < 2*σ 0 3188 :=
  checkRule 3188 9 [1,2,4,797,1594,3188]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3202 : 0 < 3202 ∧ 5+2 < 2*σ 0 3202 :=
  checkRule 3202 5 [1,2,1601,3202]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3214 : 0 < 3214 ∧ 5+2 < 2*σ 0 3214 :=
  checkRule 3214 5 [1,2,1607,3214]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3215 : 0 < 3215 ∧ 5+2 < 2*σ 0 3215 :=
  checkRule 3215 5 [1,5,643,3215]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3217 : 0 < 3217 ∧ 1+2 < 2*σ 0 3217 :=
  checkRule 3217 1 [1,3217]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3222 : 0 < 3222 ∧ 21+2 < 2*σ 0 3222 :=
  checkRule 3222 21 [1,2,3,6,9,18,179,358,537,1074,1611,3222]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3225 : 0 < 3225 ∧ 21+2 < 2*σ 0 3225 :=
  checkRule 3225 21 [1,3,5,15,25,43,75,129,215,645,1075,3225]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3231 : 0 < 3231 ∧ 9+2 < 2*σ 0 3231 :=
  checkRule 3231 9 [1,3,9,359,1077,3231]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3254 : 0 < 3254 ∧ 5+2 < 2*σ 0 3254 :=
  checkRule 3254 5 [1,2,1627,3254]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3258 : 0 < 3258 ∧ 21+2 < 2*σ 0 3258 :=
  checkRule 3258 21 [1,2,3,6,9,18,181,362,543,1086,1629,3258]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3260 : 0 < 3260 ∧ 21+2 < 2*σ 0 3260 :=
  checkRule 3260 21 [1,2,4,5,10,20,163,326,652,815,1630,3260]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3261 : 0 < 3261 ∧ 5+2 < 2*σ 0 3261 :=
  checkRule 3261 5 [1,3,1087,3261]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3264 : 0 < 3264 ∧ 53+2 < 2*σ 0 3264 :=
  checkRule 3264 53 [1,2,3,4,6,8,12,16,17,24,32,34,48,51,64,68,96,102,136,192,204,272,408,544,816,1088,1632,3264]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3265 : 0 < 3265 ∧ 5+2 < 2*σ 0 3265 :=
  checkRule 3265 5 [1,5,653,3265]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3274 : 0 < 3274 ∧ 5+2 < 2*σ 0 3274 :=
  checkRule 3274 5 [1,2,1637,3274]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3279 : 0 < 3279 ∧ 5+2 < 2*σ 0 3279 :=
  checkRule 3279 5 [1,3,1093,3279]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3282 : 0 < 3282 ∧ 13+2 < 2*σ 0 3282 :=
  checkRule 3282 13 [1,2,3,6,547,1094,1641,3282]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3283 : 0 < 3283 ∧ 9+2 < 2*σ 0 3283 :=
  checkRule 3283 9 [1,7,49,67,469,3283]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3284 : 0 < 3284 ∧ 9+2 < 2*σ 0 3284 :=
  checkRule 3284 9 [1,2,4,821,1642,3284]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3288 : 0 < 3288 ∧ 29+2 < 2*σ 0 3288 :=
  checkRule 3288 29 [1,2,3,4,6,8,12,24,137,274,411,548,822,1096,1644,3288]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3292 : 0 < 3292 ∧ 9+2 < 2*σ 0 3292 :=
  checkRule 3292 9 [1,2,4,823,1646,3292]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3295 : 0 < 3295 ∧ 5+2 < 2*σ 0 3295 :=
  checkRule 3295 5 [1,5,659,3295]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3303 : 0 < 3303 ∧ 9+2 < 2*σ 0 3303 :=
  checkRule 3303 9 [1,3,9,367,1101,3303]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3305 : 0 < 3305 ∧ 5+2 < 2*σ 0 3305 :=
  checkRule 3305 5 [1,5,661,3305]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3310 : 0 < 3310 ∧ 13+2 < 2*σ 0 3310 :=
  checkRule 3310 13 [1,2,5,10,331,662,1655,3310]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3319 : 0 < 3319 ∧ 1+2 < 2*σ 0 3319 :=
  checkRule 3319 1 [1,3319]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3332 : 0 < 3332 ∧ 33+2 < 2*σ 0 3332 :=
  checkRule 3332 33 [1,2,4,7,14,17,28,34,49,68,98,119,196,238,476,833,1666,3332]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3336 : 0 < 3336 ∧ 29+2 < 2*σ 0 3336 :=
  checkRule 3336 29 [1,2,3,4,6,8,12,24,139,278,417,556,834,1112,1668,3336]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3340 : 0 < 3340 ∧ 21+2 < 2*σ 0 3340 :=
  checkRule 3340 21 [1,2,4,5,10,20,167,334,668,835,1670,3340]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3342 : 0 < 3342 ∧ 13+2 < 2*σ 0 3342 :=
  checkRule 3342 13 [1,2,3,6,557,1114,1671,3342]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3348 : 0 < 3348 ∧ 45+2 < 2*σ 0 3348 :=
  checkRule 3348 45 [1,2,3,4,6,9,12,18,27,31,36,54,62,93,108,124,186,279,372,558,837,1116,1674,3348]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3357 : 0 < 3357 ∧ 9+2 < 2*σ 0 3357 :=
  checkRule 3357 9 [1,3,9,373,1119,3357]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3370 : 0 < 3370 ∧ 13+2 < 2*σ 0 3370 :=
  checkRule 3370 13 [1,2,5,10,337,674,1685,3370]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3376 : 0 < 3376 ∧ 17+2 < 2*σ 0 3376 :=
  checkRule 3376 17 [1,2,4,8,16,211,422,844,1688,3376]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3378 : 0 < 3378 ∧ 13+2 < 2*σ 0 3378 :=
  checkRule 3378 13 [1,2,3,6,563,1126,1689,3378]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3381 : 0 < 3381 ∧ 21+2 < 2*σ 0 3381 :=
  checkRule 3381 21 [1,3,7,21,23,49,69,147,161,483,1127,3381]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3385 : 0 < 3385 ∧ 5+2 < 2*σ 0 3385 :=
  checkRule 3385 5 [1,5,677,3385]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3394 : 0 < 3394 ∧ 5+2 < 2*σ 0 3394 :=
  checkRule 3394 5 [1,2,1697,3394]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3400 : 0 < 3400 ∧ 45+2 < 2*σ 0 3400 :=
  checkRule 3400 45 [1,2,4,5,8,10,17,20,25,34,40,50,68,85,100,136,170,200,340,425,680,850,1700,3400]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3411 : 0 < 3411 ∧ 9+2 < 2*σ 0 3411 :=
  checkRule 3411 9 [1,3,9,379,1137,3411]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3414 : 0 < 3414 ∧ 13+2 < 2*σ 0 3414 :=
  checkRule 3414 13 [1,2,3,6,569,1138,1707,3414]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3426 : 0 < 3426 ∧ 13+2 < 2*σ 0 3426 :=
  checkRule 3426 13 [1,2,3,6,571,1142,1713,3426]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3438 : 0 < 3438 ∧ 21+2 < 2*σ 0 3438 :=
  checkRule 3438 21 [1,2,3,6,9,18,191,382,573,1146,1719,3438]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3442 : 0 < 3442 ∧ 5+2 < 2*σ 0 3442 :=
  checkRule 3442 5 [1,2,1721,3442]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3450 : 0 < 3450 ∧ 45+2 < 2*σ 0 3450 :=
  checkRule 3450 45 [1,2,3,5,6,10,15,23,25,30,46,50,69,75,115,138,150,230,345,575,690,1150,1725,3450]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3451 : 0 < 3451 ∧ 13+2 < 2*σ 0 3451 :=
  checkRule 3451 13 [1,7,17,29,119,203,493,3451]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3460 : 0 < 3460 ∧ 21+2 < 2*σ 0 3460 :=
  checkRule 3460 21 [1,2,4,5,10,20,173,346,692,865,1730,3460]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3462 : 0 < 3462 ∧ 13+2 < 2*σ 0 3462 :=
  checkRule 3462 13 [1,2,3,6,577,1154,1731,3462]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3463 : 0 < 3463 ∧ 1+2 < 2*σ 0 3463 :=
  checkRule 3463 1 [1,3463]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3468 : 0 < 3468 ∧ 33+2 < 2*σ 0 3468 :=
  checkRule 3468 33 [1,2,3,4,6,12,17,34,51,68,102,204,289,578,867,1156,1734,3468]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3470 : 0 < 3470 ∧ 13+2 < 2*σ 0 3470 :=
  checkRule 3470 13 [1,2,5,10,347,694,1735,3470]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3474 : 0 < 3474 ∧ 21+2 < 2*σ 0 3474 :=
  checkRule 3474 21 [1,2,3,6,9,18,193,386,579,1158,1737,3474]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3479 : 0 < 3479 ∧ 9+2 < 2*σ 0 3479 :=
  checkRule 3479 9 [1,7,49,71,497,3479]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3490 : 0 < 3490 ∧ 13+2 < 2*σ 0 3490 :=
  checkRule 3490 13 [1,2,5,10,349,698,1745,3490]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3501 : 0 < 3501 ∧ 9+2 < 2*σ 0 3501 :=
  checkRule 3501 9 [1,3,9,389,1167,3501]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3525 : 0 < 3525 ∧ 21+2 < 2*σ 0 3525 :=
  checkRule 3525 21 [1,3,5,15,25,47,75,141,235,705,1175,3525]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3530 : 0 < 3530 ∧ 13+2 < 2*σ 0 3530 :=
  checkRule 3530 13 [1,2,5,10,353,706,1765,3530]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3532 : 0 < 3532 ∧ 9+2 < 2*σ 0 3532 :=
  checkRule 3532 9 [1,2,4,883,1766,3532]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3546 : 0 < 3546 ∧ 21+2 < 2*σ 0 3546 :=
  checkRule 3546 21 [1,2,3,6,9,18,197,394,591,1182,1773,3546]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3548 : 0 < 3548 ∧ 9+2 < 2*σ 0 3548 :=
  checkRule 3548 9 [1,2,4,887,1774,3548]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3553 : 0 < 3553 ∧ 13+2 < 2*σ 0 3553 :=
  checkRule 3553 13 [1,11,17,19,187,209,323,3553]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3568 : 0 < 3568 ∧ 17+2 < 2*σ 0 3568 :=
  checkRule 3568 17 [1,2,4,8,16,223,446,892,1784,3568]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3573 : 0 < 3573 ∧ 9+2 < 2*σ 0 3573 :=
  checkRule 3573 9 [1,3,9,397,1191,3573]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3576 : 0 < 3576 ∧ 29+2 < 2*σ 0 3576 :=
  checkRule 3576 29 [1,2,3,4,6,8,12,24,149,298,447,596,894,1192,1788,3576]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3578 : 0 < 3578 ∧ 5+2 < 2*σ 0 3578 :=
  checkRule 3578 5 [1,2,1789,3578]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3580 : 0 < 3580 ∧ 21+2 < 2*σ 0 3580 :=
  checkRule 3580 21 [1,2,4,5,10,20,179,358,716,895,1790,3580]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3582 : 0 < 3582 ∧ 21+2 < 2*σ 0 3582 :=
  checkRule 3582 21 [1,2,3,6,9,18,199,398,597,1194,1791,3582]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3590 : 0 < 3590 ∧ 13+2 < 2*σ 0 3590 :=
  checkRule 3590 13 [1,2,5,10,359,718,1795,3590]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3594 : 0 < 3594 ∧ 13+2 < 2*σ 0 3594 :=
  checkRule 3594 13 [1,2,3,6,599,1198,1797,3594]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3595 : 0 < 3595 ∧ 5+2 < 2*σ 0 3595 :=
  checkRule 3595 5 [1,5,719,3595]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3602 : 0 < 3602 ∧ 5+2 < 2*σ 0 3602 :=
  checkRule 3602 5 [1,2,1801,3602]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3604 : 0 < 3604 ∧ 21+2 < 2*σ 0 3604 :=
  checkRule 3604 21 [1,2,4,17,34,53,68,106,212,901,1802,3604]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3606 : 0 < 3606 ∧ 13+2 < 2*σ 0 3606 :=
  checkRule 3606 13 [1,2,3,6,601,1202,1803,3606]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3609 : 0 < 3609 ∧ 9+2 < 2*σ 0 3609 :=
  checkRule 3609 9 [1,3,9,401,1203,3609]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3610 : 0 < 3610 ∧ 21+2 < 2*σ 0 3610 :=
  checkRule 3610 21 [1,2,5,10,19,38,95,190,361,722,1805,3610]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3617 : 0 < 3617 ∧ 1+2 < 2*σ 0 3617 :=
  checkRule 3617 1 [1,3617]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3620 : 0 < 3620 ∧ 21+2 < 2*σ 0 3620 :=
  checkRule 3620 21 [1,2,4,5,10,20,181,362,724,905,1810,3620]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3624 : 0 < 3624 ∧ 29+2 < 2*σ 0 3624 :=
  checkRule 3624 29 [1,2,3,4,6,8,12,24,151,302,453,604,906,1208,1812,3624]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3626 : 0 < 3626 ∧ 21+2 < 2*σ 0 3626 :=
  checkRule 3626 21 [1,2,7,14,37,49,74,98,259,518,1813,3626]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3632 : 0 < 3632 ∧ 17+2 < 2*σ 0 3632 :=
  checkRule 3632 17 [1,2,4,8,16,227,454,908,1816,3632]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3642 : 0 < 3642 ∧ 13+2 < 2*σ 0 3642 :=
  checkRule 3642 13 [1,2,3,6,607,1214,1821,3642]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3664 : 0 < 3664 ∧ 17+2 < 2*σ 0 3664 :=
  checkRule 3664 17 [1,2,4,8,16,229,458,916,1832,3664]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3670 : 0 < 3670 ∧ 13+2 < 2*σ 0 3670 :=
  checkRule 3670 13 [1,2,5,10,367,734,1835,3670]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3678 : 0 < 3678 ∧ 13+2 < 2*σ 0 3678 :=
  checkRule 3678 13 [1,2,3,6,613,1226,1839,3678]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3680 : 0 < 3680 ∧ 45+2 < 2*σ 0 3680 :=
  checkRule 3680 45 [1,2,4,5,8,10,16,20,23,32,40,46,80,92,115,160,184,230,368,460,736,920,1840,3680]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3681 : 0 < 3681 ∧ 9+2 < 2*σ 0 3681 :=
  checkRule 3681 9 [1,3,9,409,1227,3681]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3693 : 0 < 3693 ∧ 5+2 < 2*σ 0 3693 :=
  checkRule 3693 5 [1,3,1231,3693]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3695 : 0 < 3695 ∧ 5+2 < 2*σ 0 3695 :=
  checkRule 3695 5 [1,5,739,3695]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3702 : 0 < 3702 ∧ 13+2 < 2*σ 0 3702 :=
  checkRule 3702 13 [1,2,3,6,617,1234,1851,3702]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3703 : 0 < 3703 ∧ 9+2 < 2*σ 0 3703 :=
  checkRule 3703 9 [1,7,23,161,529,3703]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3722 : 0 < 3722 ∧ 5+2 < 2*σ 0 3722 :=
  checkRule 3722 5 [1,2,1861,3722]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3724 : 0 < 3724 ∧ 33+2 < 2*σ 0 3724 :=
  checkRule 3724 33 [1,2,4,7,14,19,28,38,49,76,98,133,196,266,532,931,1862,3724]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3728 : 0 < 3728 ∧ 17+2 < 2*σ 0 3728 :=
  checkRule 3728 17 [1,2,4,8,16,233,466,932,1864,3728]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3730 : 0 < 3730 ∧ 13+2 < 2*σ 0 3730 :=
  checkRule 3730 13 [1,2,5,10,373,746,1865,3730]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3750 : 0 < 3750 ∧ 37+2 < 2*σ 0 3750 :=
  checkRule 3750 37 [1,2,3,5,6,10,15,25,30,50,75,125,150,250,375,625,750,1250,1875,3750]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3764 : 0 < 3764 ∧ 9+2 < 2*σ 0 3764 :=
  checkRule 3764 9 [1,2,4,941,1882,3764]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3768 : 0 < 3768 ∧ 29+2 < 2*σ 0 3768 :=
  checkRule 3768 29 [1,2,3,4,6,8,12,24,157,314,471,628,942,1256,1884,3768]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3771 : 0 < 3771 ∧ 9+2 < 2*σ 0 3771 :=
  checkRule 3771 9 [1,3,9,419,1257,3771]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3772 : 0 < 3772 ∧ 21+2 < 2*σ 0 3772 :=
  checkRule 3772 21 [1,2,4,23,41,46,82,92,164,943,1886,3772]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3786 : 0 < 3786 ∧ 13+2 < 2*σ 0 3786 :=
  checkRule 3786 13 [1,2,3,6,631,1262,1893,3786]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3790 : 0 < 3790 ∧ 13+2 < 2*σ 0 3790 :=
  checkRule 3790 13 [1,2,5,10,379,758,1895,3790]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3798 : 0 < 3798 ∧ 21+2 < 2*σ 0 3798 :=
  checkRule 3798 21 [1,2,3,6,9,18,211,422,633,1266,1899,3798]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3800 : 0 < 3800 ∧ 45+2 < 2*σ 0 3800 :=
  checkRule 3800 45 [1,2,4,5,8,10,19,20,25,38,40,50,76,95,100,152,190,200,380,475,760,950,1900,3800]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3805 : 0 < 3805 ∧ 5+2 < 2*σ 0 3805 :=
  checkRule 3805 5 [1,5,761,3805]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3820 : 0 < 3820 ∧ 21+2 < 2*σ 0 3820 :=
  checkRule 3820 21 [1,2,4,5,10,20,191,382,764,955,1910,3820]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3830 : 0 < 3830 ∧ 13+2 < 2*σ 0 3830 :=
  checkRule 3830 13 [1,2,5,10,383,766,1915,3830]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3837 : 0 < 3837 ∧ 5+2 < 2*σ 0 3837 :=
  checkRule 3837 5 [1,3,1279,3837]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3846 : 0 < 3846 ∧ 13+2 < 2*σ 0 3846 :=
  checkRule 3846 13 [1,2,3,6,641,1282,1923,3846]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3856 : 0 < 3856 ∧ 17+2 < 2*σ 0 3856 :=
  checkRule 3856 17 [1,2,4,8,16,241,482,964,1928,3856]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3857 : 0 < 3857 ∧ 13+2 < 2*σ 0 3857 :=
  checkRule 3857 13 [1,7,19,29,133,203,551,3857]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3860 : 0 < 3860 ∧ 21+2 < 2*σ 0 3860 :=
  checkRule 3860 21 [1,2,4,5,10,20,193,386,772,965,1930,3860]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3862 : 0 < 3862 ∧ 5+2 < 2*σ 0 3862 :=
  checkRule 3862 5 [1,2,1931,3862]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3871 : 0 < 3871 ∧ 9+2 < 2*σ 0 3871 :=
  checkRule 3871 9 [1,7,49,79,553,3871]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3876 : 0 < 3876 ∧ 45+2 < 2*σ 0 3876 :=
  checkRule 3876 45 [1,2,3,4,6,12,17,19,34,38,51,57,68,76,102,114,204,228,323,646,969,1292,1938,3876]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3879 : 0 < 3879 ∧ 9+2 < 2*σ 0 3879 :=
  checkRule 3879 9 [1,3,9,431,1293,3879]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3884 : 0 < 3884 ∧ 9+2 < 2*σ 0 3884 :=
  checkRule 3884 9 [1,2,4,971,1942,3884]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3890 : 0 < 3890 ∧ 13+2 < 2*σ 0 3890 :=
  checkRule 3890 13 [1,2,5,10,389,778,1945,3890]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3897 : 0 < 3897 ∧ 9+2 < 2*σ 0 3897 :=
  checkRule 3897 9 [1,3,9,433,1299,3897]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3909 : 0 < 3909 ∧ 5+2 < 2*σ 0 3909 :=
  checkRule 3909 5 [1,3,1303,3909]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3912 : 0 < 3912 ∧ 29+2 < 2*σ 0 3912 :=
  checkRule 3912 29 [1,2,3,4,6,8,12,24,163,326,489,652,978,1304,1956,3912]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3935 : 0 < 3935 ∧ 5+2 < 2*σ 0 3935 :=
  checkRule 3935 5 [1,5,787,3935]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3940 : 0 < 3940 ∧ 21+2 < 2*σ 0 3940 :=
  checkRule 3940 21 [1,2,4,5,10,20,197,394,788,985,1970,3940]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3954 : 0 < 3954 ∧ 13+2 < 2*σ 0 3954 :=
  checkRule 3954 13 [1,2,3,6,659,1318,1977,3954]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3963 : 0 < 3963 ∧ 5+2 < 2*σ 0 3963 :=
  checkRule 3963 5 [1,3,1321,3963]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3966 : 0 < 3966 ∧ 13+2 < 2*σ 0 3966 :=
  checkRule 3966 13 [1,2,3,6,661,1322,1983,3966]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3970 : 0 < 3970 ∧ 13+2 < 2*σ 0 3970 :=
  checkRule 3970 13 [1,2,5,10,397,794,1985,3970]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3980 : 0 < 3980 ∧ 21+2 < 2*σ 0 3980 :=
  checkRule 3980 21 [1,2,4,5,10,20,199,398,796,995,1990,3980]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3987 : 0 < 3987 ∧ 9+2 < 2*σ 0 3987 :=
  checkRule 3987 9 [1,3,9,443,1329,3987]
    (by decide) (by decide) (by decide) (by decide)

private theorem valid_3996 : 0 < 3996 ∧ 45+2 < 2*σ 0 3996 :=
  checkRule 3996 45 [1,2,3,4,6,9,12,18,27,36,37,54,74,108,111,148,222,333,444,666,999,1332,1998,3996]
    (by decide) (by decide) (by decide) (by decide)

private def column_17 : Column :=
  certifyColumn 17 4683 16 (by decide) (by decide)
    [⟨17,1,valid_17⟩,
     ⟨34,5,valid_34⟩,
     ⟨51,5,valid_51⟩,
     ⟨68,9,valid_68⟩,
     ⟨85,5,valid_85⟩,
     ⟨102,13,valid_102⟩,
     ⟨153,9,valid_153⟩,
     ⟨170,13,valid_170⟩,
     ⟨408,29,valid_408⟩] (by decide)

private def column_19 : Column :=
  certifyColumn 19 430689 16 (by decide) (by decide)
    [⟨19,1,valid_19⟩,
     ⟨38,5,valid_38⟩,
     ⟨57,5,valid_57⟩,
     ⟨76,9,valid_76⟩,
     ⟨95,5,valid_95⟩,
     ⟨114,13,valid_114⟩,
     ⟨171,9,valid_171⟩,
     ⟨190,13,valid_190⟩,
     ⟨342,21,valid_342⟩] (by decide)

private def column_23 : Column :=
  certifyColumn 23 553311 16 (by decide) (by decide)
    [⟨23,1,valid_23⟩,
     ⟨46,5,valid_46⟩,
     ⟨69,5,valid_69⟩,
     ⟨92,9,valid_92⟩,
     ⟨115,5,valid_115⟩,
     ⟨138,13,valid_138⟩,
     ⟨207,9,valid_207⟩,
     ⟨230,13,valid_230⟩,
     ⟨414,21,valid_414⟩,
     ⟨460,21,valid_460⟩] (by decide)

private def column_29 : Column :=
  certifyColumn 29 500061121 16 (by decide) (by decide)
    [⟨29,1,valid_29⟩,
     ⟨58,5,valid_58⟩,
     ⟨87,5,valid_87⟩,
     ⟨116,9,valid_116⟩,
     ⟨145,5,valid_145⟩,
     ⟨174,13,valid_174⟩,
     ⟨261,9,valid_261⟩,
     ⟨290,13,valid_290⟩,
     ⟨522,21,valid_522⟩,
     ⟨580,21,valid_580⟩,
     ⟨696,29,valid_696⟩] (by decide)

private def column_31 : Column :=
  certifyColumn 31 2129193099 15 (by decide) (by decide)
    [⟨31,1,valid_31⟩,
     ⟨62,5,valid_62⟩,
     ⟨93,5,valid_93⟩,
     ⟨124,9,valid_124⟩,
     ⟨155,5,valid_155⟩,
     ⟨186,13,valid_186⟩,
     ⟨279,9,valid_279⟩,
     ⟨310,13,valid_310⟩,
     ⟨558,21,valid_558⟩,
     ⟨620,21,valid_620⟩,
     ⟨744,29,valid_744⟩] (by decide)

private def column_37 : Column :=
  certifyColumn 37 23028561279 15 (by decide) (by decide)
    [⟨37,1,valid_37⟩,
     ⟨74,5,valid_74⟩,
     ⟨111,5,valid_111⟩,
     ⟨148,9,valid_148⟩,
     ⟨185,5,valid_185⟩,
     ⟨222,13,valid_222⟩,
     ⟨333,9,valid_333⟩,
     ⟨370,13,valid_370⟩,
     ⟨666,21,valid_666⟩,
     ⟨740,21,valid_740⟩,
     ⟨888,29,valid_888⟩] (by decide)

private def column_41 : Column :=
  certifyColumn 41 1901445140207 15 (by decide) (by decide)
    [⟨41,1,valid_41⟩,
     ⟨82,5,valid_82⟩,
     ⟨123,5,valid_123⟩,
     ⟨164,9,valid_164⟩,
     ⟨205,5,valid_205⟩,
     ⟨246,13,valid_246⟩,
     ⟨369,9,valid_369⟩,
     ⟨410,13,valid_410⟩,
     ⟨738,21,valid_738⟩,
     ⟨820,21,valid_820⟩,
     ⟨984,29,valid_984⟩] (by decide)

private def column_43 : Column :=
  certifyColumn 43 5872893810173 15 (by decide) (by decide)
    [⟨43,1,valid_43⟩,
     ⟨86,5,valid_86⟩,
     ⟨129,5,valid_129⟩,
     ⟨172,9,valid_172⟩,
     ⟨215,5,valid_215⟩,
     ⟨258,13,valid_258⟩,
     ⟨387,9,valid_387⟩,
     ⟨430,13,valid_430⟩,
     ⟨774,21,valid_774⟩,
     ⟨860,21,valid_860⟩,
     ⟨1032,29,valid_1032⟩] (by decide)

private def column_47 : Column :=
  certifyColumn 47 131285263277535 15 (by decide) (by decide)
    [⟨47,1,valid_47⟩,
     ⟨94,5,valid_94⟩,
     ⟨141,5,valid_141⟩,
     ⟨188,9,valid_188⟩,
     ⟨235,5,valid_235⟩,
     ⟨282,13,valid_282⟩,
     ⟨423,9,valid_423⟩,
     ⟨470,13,valid_470⟩,
     ⟨846,21,valid_846⟩,
     ⟨940,21,valid_940⟩,
     ⟨1128,29,valid_1128⟩] (by decide)

private def column_4 : Column :=
  certifyColumn 4 13 18 (by decide) (by decide)
    [⟨32,9,valid_32⟩] (by decide)

private def column_8 : Column :=
  certifyColumn 8 95 17 (by decide) (by decide)
    [⟨64,11,valid_64⟩,
     ⟨192,25,valid_192⟩] (by decide)

private def column_53 : Column :=
  certifyColumn 53 8406702091000799 15 (by decide) (by decide)
    [⟨53,1,valid_53⟩,
     ⟨106,5,valid_106⟩,
     ⟨159,5,valid_159⟩,
     ⟨212,9,valid_212⟩,
     ⟨265,5,valid_265⟩,
     ⟨318,13,valid_318⟩,
     ⟨477,9,valid_477⟩,
     ⟨530,13,valid_530⟩,
     ⟨954,21,valid_954⟩,
     ⟨1060,21,valid_1060⟩,
     ⟨1272,29,valid_1272⟩] (by decide)

private def column_59 : Column :=
  certifyColumn 59 125519679685115391 15 (by decide) (by decide)
    [⟨59,1,valid_59⟩,
     ⟨118,5,valid_118⟩,
     ⟨177,5,valid_177⟩,
     ⟨236,9,valid_236⟩,
     ⟨295,5,valid_295⟩,
     ⟨354,13,valid_354⟩,
     ⟨531,9,valid_531⟩,
     ⟨590,13,valid_590⟩,
     ⟨1062,21,valid_1062⟩,
     ⟨1180,21,valid_1180⟩,
     ⟨1416,29,valid_1416⟩] (by decide)

private def column_61 : Column :=
  certifyColumn 61 2228155210931232491 15 (by decide) (by decide)
    [⟨61,1,valid_61⟩,
     ⟨122,5,valid_122⟩,
     ⟨183,5,valid_183⟩,
     ⟨244,9,valid_244⟩,
     ⟨305,5,valid_305⟩,
     ⟨366,13,valid_366⟩,
     ⟨549,9,valid_549⟩,
     ⟨610,13,valid_610⟩,
     ⟨1098,21,valid_1098⟩,
     ⟨1220,21,valid_1220⟩,
     ⟨1464,29,valid_1464⟩] (by decide)

private def column_67 : Column :=
  certifyColumn 67 147573669946450438827 14 (by decide) (by decide)
    [⟨67,1,valid_67⟩,
     ⟨134,5,valid_134⟩,
     ⟨201,5,valid_201⟩,
     ⟨268,9,valid_268⟩,
     ⟨335,5,valid_335⟩,
     ⟨402,13,valid_402⟩,
     ⟨603,9,valid_603⟩,
     ⟨670,13,valid_670⟩,
     ⟨1206,21,valid_1206⟩,
     ⟨1340,21,valid_1340⟩,
     ⟨1608,29,valid_1608⟩] (by decide)

private def column_71 : Column :=
  certifyColumn 71 1574266885970558189567 14 (by decide) (by decide)
    [⟨71,1,valid_71⟩,
     ⟨142,5,valid_142⟩,
     ⟨213,5,valid_213⟩,
     ⟨284,9,valid_284⟩,
     ⟨355,5,valid_355⟩,
     ⟨426,13,valid_426⟩,
     ⟨639,9,valid_639⟩,
     ⟨710,13,valid_710⟩,
     ⟨1278,21,valid_1278⟩,
     ⟨1420,21,valid_1420⟩,
     ⟨1704,29,valid_1704⟩] (by decide)

private def column_73 : Column :=
  certifyColumn 73 6474770789226740367231 14 (by decide) (by decide)
    [⟨73,1,valid_73⟩,
     ⟨146,5,valid_146⟩,
     ⟨219,5,valid_219⟩,
     ⟨292,9,valid_292⟩,
     ⟨365,5,valid_365⟩,
     ⟨438,13,valid_438⟩,
     ⟨657,9,valid_657⟩,
     ⟨730,13,valid_730⟩,
     ⟨1314,21,valid_1314⟩,
     ⟨1460,21,valid_1460⟩,
     ⟨1752,29,valid_1752⟩] (by decide)

private def column_79 : Column :=
  certifyColumn 79 604388744528641788931755 14 (by decide) (by decide)
    [⟨79,1,valid_79⟩,
     ⟨158,5,valid_158⟩,
     ⟨237,5,valid_237⟩,
     ⟨316,9,valid_316⟩,
     ⟨395,5,valid_395⟩,
     ⟨474,13,valid_474⟩,
     ⟨711,9,valid_711⟩,
     ⟨790,13,valid_790⟩,
     ⟨1422,21,valid_1422⟩,
     ⟨1580,21,valid_1580⟩,
     ⟨1896,29,valid_1896⟩] (by decide)

private def column_83 : Column :=
  certifyColumn 83 9670078244958834844495799 14 (by decide) (by decide)
    [⟨83,1,valid_83⟩,
     ⟨166,5,valid_166⟩,
     ⟨249,5,valid_249⟩,
     ⟨332,9,valid_332⟩,
     ⟨415,5,valid_415⟩,
     ⟨498,13,valid_498⟩,
     ⟨747,9,valid_747⟩,
     ⟨830,13,valid_830⟩,
     ⟨1494,21,valid_1494⟩,
     ⟨1660,21,valid_1660⟩,
     ⟨1992,29,valid_1992⟩] (by decide)

private def column_89 : Column :=
  certifyColumn 89 5286062088274061691977727 14 (by decide) (by decide)
    [⟨89,1,valid_89⟩,
     ⟨178,5,valid_178⟩,
     ⟨267,5,valid_267⟩,
     ⟨356,9,valid_356⟩,
     ⟨445,5,valid_445⟩,
     ⟨534,13,valid_534⟩,
     ⟨801,9,valid_801⟩,
     ⟨890,13,valid_890⟩,
     ⟨1602,21,valid_1602⟩,
     ⟨1780,21,valid_1780⟩,
     ⟨2136,29,valid_2136⟩] (by decide)

private def column_97 : Column :=
  certifyColumn 97 158454813860301400957575495657 14 (by decide) (by decide)
    [⟨97,1,valid_97⟩,
     ⟨194,5,valid_194⟩,
     ⟨291,5,valid_291⟩,
     ⟨388,9,valid_388⟩,
     ⟨485,5,valid_485⟩,
     ⟨582,13,valid_582⟩,
     ⟨873,9,valid_873⟩,
     ⟨970,13,valid_970⟩,
     ⟨1746,21,valid_1746⟩,
     ⟨1940,21,valid_1940⟩,
     ⟨2328,29,valid_2328⟩] (by decide)

private def column_101 : Column :=
  certifyColumn 101 950428427368581814716463050751 14 (by decide) (by decide)
    [⟨101,1,valid_101⟩,
     ⟨202,5,valid_202⟩,
     ⟨303,5,valid_303⟩,
     ⟨404,9,valid_404⟩,
     ⟨505,5,valid_505⟩,
     ⟨606,13,valid_606⟩,
     ⟨909,9,valid_909⟩,
     ⟨1010,13,valid_1010⟩,
     ⟨1818,21,valid_1818⟩,
     ⟨2020,21,valid_2020⟩,
     ⟨2424,29,valid_2424⟩] (by decide)

private def column_103 : Column :=
  certifyColumn 103 8853128153149711301671382415359 14 (by decide) (by decide)
    [⟨103,1,valid_103⟩,
     ⟨206,5,valid_206⟩,
     ⟨309,5,valid_309⟩,
     ⟨412,9,valid_412⟩,
     ⟨515,5,valid_515⟩,
     ⟨618,13,valid_618⟩,
     ⟨927,9,valid_927⟩,
     ⟨1030,13,valid_1030⟩,
     ⟨1854,21,valid_1854⟩,
     ⟨2060,21,valid_2060⟩,
     ⟨2472,29,valid_2472⟩] (by decide)

private def column_16 : Column :=
  certifyColumn 16 57215 16 (by decide) (by decide)
    [⟨128,13,valid_128⟩,
     ⟨384,29,valid_384⟩] (by decide)

private def column_107 : Column :=
  certifyColumn 107 160981720885836222126246237036543 14 (by decide) (by decide)
    [⟨107,1,valid_107⟩,
     ⟨214,5,valid_214⟩,
     ⟨321,5,valid_321⟩,
     ⟨428,9,valid_428⟩,
     ⟨535,5,valid_535⟩,
     ⟨642,13,valid_642⟩,
     ⟨963,9,valid_963⟩,
     ⟨1070,13,valid_1070⟩,
     ⟨1926,21,valid_1926⟩,
     ⟨2140,21,valid_2140⟩,
     ⟨2568,29,valid_2568⟩] (by decide)

private def column_25 : Column :=
  certifyColumn 25 33488511 16 (by decide) (by decide)
    [⟨125,5,valid_125⟩,
     ⟨250,13,valid_250⟩,
     ⟨500,21,valid_500⟩] (by decide)

private def column_109 : Column :=
  certifyColumn 109 649034631332882712095826673926113 14 (by decide) (by decide)
    [⟨109,1,valid_109⟩,
     ⟨218,5,valid_218⟩,
     ⟨327,5,valid_327⟩,
     ⟨436,9,valid_436⟩,
     ⟨545,5,valid_545⟩,
     ⟨654,13,valid_654⟩,
     ⟨981,9,valid_981⟩,
     ⟨1090,13,valid_1090⟩,
     ⟨1962,21,valid_1962⟩,
     ⟨2180,21,valid_2180⟩,
     ⟨2616,29,valid_2616⟩] (by decide)

private def column_113 : Column :=
  certifyColumn 113 10384593711705046932518052038704801 14 (by decide) (by decide)
    [⟨113,1,valid_113⟩,
     ⟨226,5,valid_226⟩,
     ⟨339,5,valid_339⟩,
     ⟨452,9,valid_452⟩,
     ⟨565,5,valid_565⟩,
     ⟨678,13,valid_678⟩,
     ⟨1017,9,valid_1017⟩,
     ⟨1130,13,valid_1130⟩,
     ⟨2034,21,valid_2034⟩,
     ⟨2260,21,valid_2260⟩,
     ⟨2712,29,valid_2712⟩] (by decide)

private def column_127 : Column :=
  certifyColumn 127 116307448041665080622693009480203894783 13 (by decide) (by decide)
    [⟨127,1,valid_127⟩,
     ⟨254,5,valid_254⟩,
     ⟨381,5,valid_381⟩,
     ⟨508,9,valid_508⟩,
     ⟨635,5,valid_635⟩,
     ⟨762,13,valid_762⟩,
     ⟨1143,9,valid_1143⟩,
     ⟨1270,13,valid_1270⟩,
     ⟨2286,21,valid_2286⟩,
     ⟨2540,21,valid_2540⟩,
     ⟨3048,29,valid_3048⟩] (by decide)

private def column_131 : Column :=
  certifyColumn 131 2722253661931104801212578657683600568255 13 (by decide) (by decide)
    [⟨131,1,valid_131⟩,
     ⟨262,5,valid_262⟩,
     ⟨393,5,valid_393⟩,
     ⟨524,9,valid_524⟩,
     ⟨655,5,valid_655⟩,
     ⟨786,13,valid_786⟩,
     ⟨1179,9,valid_1179⟩,
     ⟨1310,13,valid_1310⟩,
     ⟨2358,21,valid_2358⟩,
     ⟨2620,21,valid_2620⟩,
     ⟨3144,29,valid_3144⟩] (by decide)

private def column_137 : Column :=
  certifyColumn 137 168779720386999224847940776541121176139775 13 (by decide) (by decide)
    [⟨137,1,valid_137⟩,
     ⟨274,5,valid_274⟩,
     ⟨411,5,valid_411⟩,
     ⟨548,9,valid_548⟩,
     ⟨685,5,valid_685⟩,
     ⟨822,13,valid_822⟩,
     ⟨1233,9,valid_1233⟩,
     ⟨1370,13,valid_1370⟩,
     ⟨2466,21,valid_2466⟩,
     ⟨2740,21,valid_2740⟩,
     ⟨3288,29,valid_3288⟩] (by decide)

private def column_139 : Column :=
  certifyColumn 139 696898199185025281132475729330949320605419 13 (by decide) (by decide)
    [⟨139,1,valid_139⟩,
     ⟨278,5,valid_278⟩,
     ⟨417,5,valid_417⟩,
     ⟨556,9,valid_556⟩,
     ⟨695,5,valid_695⟩,
     ⟨834,13,valid_834⟩,
     ⟨1251,9,valid_1251⟩,
     ⟨1390,13,valid_1390⟩,
     ⟨2502,21,valid_2502⟩,
     ⟨2780,21,valid_2780⟩,
     ⟨3336,29,valid_3336⟩] (by decide)

private def column_34 : Column :=
  certifyColumn 34 17044594687 15 (by decide) (by decide)
    [⟨272,17,valid_272⟩,
     ⟨816,37,valid_816⟩] (by decide)

private def column_149 : Column :=
  certifyColumn 149 713622144940334034114062554427163616598818815 13 (by decide) (by decide)
    [⟨149,1,valid_149⟩,
     ⟨298,5,valid_298⟩,
     ⟨447,5,valid_447⟩,
     ⟨596,9,valid_596⟩,
     ⟨745,5,valid_745⟩,
     ⟨894,13,valid_894⟩,
     ⟨1341,9,valid_1341⟩,
     ⟨1490,13,valid_1490⟩,
     ⟨2682,21,valid_2682⟩,
     ⟨2980,21,valid_2980⟩,
     ⟨3576,29,valid_3576⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_151 : Column :=
  certifyColumn 151 1905973260043946712134516695312088102615384063 13 (by decide) (by decide)
    [⟨151,1,valid_151⟩,
     ⟨302,5,valid_302⟩,
     ⟨453,5,valid_453⟩,
     ⟨604,9,valid_604⟩,
     ⟨755,5,valid_755⟩,
     ⟨906,13,valid_906⟩,
     ⟨1359,9,valid_1359⟩,
     ⟨1510,13,valid_1510⟩,
     ⟨2718,21,valid_2718⟩,
     ⟨3020,21,valid_3020⟩,
     ⟨3624,29,valid_3624⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_157 : Column :=
  certifyColumn 157 182686310784717364881260298238298796228679284607 13 (by decide) (by decide)
    [⟨157,1,valid_157⟩,
     ⟨314,5,valid_314⟩,
     ⟨471,5,valid_471⟩,
     ⟨628,9,valid_628⟩,
     ⟨785,5,valid_785⟩,
     ⟨942,13,valid_942⟩,
     ⟨1413,9,valid_1413⟩,
     ⟨1570,13,valid_1570⟩,
     ⟨2826,21,valid_2826⟩,
     ⟨3140,21,valid_3140⟩,
     ⟨3768,29,valid_3768⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_163 : Column :=
  certifyColumn 163 11314851386138552011503369684727947060694803808255 13 (by decide) (by decide)
    [⟨163,1,valid_163⟩,
     ⟨326,5,valid_326⟩,
     ⟨489,5,valid_489⟩,
     ⟨652,9,valid_652⟩,
     ⟨815,5,valid_815⟩,
     ⟨978,13,valid_978⟩,
     ⟨1467,9,valid_1467⟩,
     ⟨1630,13,valid_1630⟩,
     ⟨2934,21,valid_2934⟩,
     ⟨3260,21,valid_3260⟩,
     ⟨3912,29,valid_3912⟩] (by decide)

private def column_38 : Column :=
  certifyColumn 38 266011148287 15 (by decide) (by decide)
    [⟨304,17,valid_304⟩,
     ⟨912,37,valid_912⟩] (by decide)

private def column_27 : Column :=
  certifyColumn 27 33554431 16 (by decide) (by decide)
    [⟨243,9,valid_243⟩,
     ⟨486,21,valid_486⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_167 : Column :=
  certifyColumn 167 187049370827333528422555817161838448719460267196415 13 (by decide) (by decide)
    [⟨167,1,valid_167⟩,
     ⟨334,5,valid_334⟩,
     ⟨501,5,valid_501⟩,
     ⟨668,9,valid_668⟩,
     ⟨835,5,valid_835⟩,
     ⟨1002,13,valid_1002⟩,
     ⟨1503,9,valid_1503⟩,
     ⟨1670,13,valid_1670⟩,
     ⟨3006,21,valid_3006⟩,
     ⟨3340,21,valid_3340⟩] (by decide)

private def column_85 : Column :=
  certifyColumn 85 19323914415518954056318975 14 (by decide) (by decide)
    [⟨425,9,valid_425⟩,
     ⟨850,21,valid_850⟩,
     ⟨1275,21,valid_1275⟩,
     ⟨2550,45,valid_2550⟩,
     ⟨3400,45,valid_3400⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_173 : Column :=
  certifyColumn 173 11972621413014756705924586149611790497021399390742657 13 (by decide) (by decide)
    [⟨173,1,valid_173⟩,
     ⟨346,5,valid_346⟩,
     ⟨519,5,valid_519⟩,
     ⟨692,9,valid_692⟩,
     ⟨865,5,valid_865⟩,
     ⟨1038,13,valid_1038⟩,
     ⟨1557,9,valid_1557⟩,
     ⟨1730,13,valid_1730⟩,
     ⟨3114,21,valid_3114⟩,
     ⟨3460,21,valid_3460⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_179 : Column :=
  certifyColumn 179 766236072532449006987678005266890379208439856243931135 13 (by decide) (by decide)
    [⟨179,1,valid_179⟩,
     ⟨358,5,valid_358⟩,
     ⟨537,5,valid_537⟩,
     ⟨716,9,valid_716⟩,
     ⟨895,5,valid_895⟩,
     ⟨1074,13,valid_1074⟩,
     ⟨1611,9,valid_1611⟩,
     ⟨1790,13,valid_1790⟩,
     ⟨3222,21,valid_3222⟩,
     ⟨3580,21,valid_3580⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_181 : Column :=
  certifyColumn 181 3064967697170361176334261464406819377962325309344645119 13 (by decide) (by decide)
    [⟨181,1,valid_181⟩,
     ⟨362,5,valid_362⟩,
     ⟨543,5,valid_543⟩,
     ⟨724,9,valid_724⟩,
     ⟨905,5,valid_905⟩,
     ⟨1086,13,valid_1086⟩,
     ⟨1629,9,valid_1629⟩,
     ⟨1810,13,valid_1810⟩,
     ⟨3258,21,valid_3258⟩,
     ⟨3620,21,valid_3620⟩] (by decide)

private def column_46 : Column :=
  certifyColumn 46 65970695438335 15 (by decide) (by decide)
    [⟨368,17,valid_368⟩,
     ⟨1104,37,valid_1104⟩] (by decide)

private def column_95 : Column :=
  certifyColumn 95 34043350490052068036174675967 14 (by decide) (by decide)
    [⟨475,9,valid_475⟩,
     ⟨950,21,valid_950⟩,
     ⟨1425,21,valid_1425⟩,
     ⟨2850,45,valid_2850⟩,
     ⟨3800,45,valid_3800⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_191 : Column :=
  certifyColumn 191 3138550867670482096311329339785240958872755273844617378807 13 (by decide) (by decide)
    [⟨191,1,valid_191⟩,
     ⟨382,5,valid_382⟩,
     ⟨573,5,valid_573⟩,
     ⟨764,9,valid_764⟩,
     ⟨955,5,valid_955⟩,
     ⟨1146,13,valid_1146⟩,
     ⟨1719,9,valid_1719⟩,
     ⟨1910,13,valid_1910⟩,
     ⟨3438,21,valid_3438⟩,
     ⟨3820,21,valid_3820⟩] (by decide)

private def column_32 : Column :=
  certifyColumn 32 3749707775 15 (by decide) (by decide)
    [⟨256,15,valid_256⟩,
     ⟨768,33,valid_768⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_193 : Column :=
  certifyColumn 193 12552670786698784423125414821849402377592476727662821228415 13 (by decide) (by decide)
    [⟨193,1,valid_193⟩,
     ⟨386,5,valid_386⟩,
     ⟨579,5,valid_579⟩,
     ⟨772,9,valid_772⟩,
     ⟨965,5,valid_965⟩,
     ⟨1158,13,valid_1158⟩,
     ⟨1737,9,valid_1737⟩,
     ⟨1930,13,valid_1930⟩,
     ⟨3474,21,valid_3474⟩,
     ⟨3860,21,valid_3860⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_197 : Column :=
  certifyColumn 197 187528414344674233322762596349550983272420496206797008265215 13 (by decide) (by decide)
    [⟨197,1,valid_197⟩,
     ⟨394,5,valid_394⟩,
     ⟨591,5,valid_591⟩,
     ⟨788,9,valid_788⟩,
     ⟨985,5,valid_985⟩,
     ⟨1182,13,valid_1182⟩,
     ⟨1773,9,valid_1773⟩,
     ⟨1970,13,valid_1970⟩,
     ⟨3546,21,valid_3546⟩,
     ⟨3940,21,valid_3940⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_199 : Column :=
  certifyColumn 199 797142497389531483593423554833786086546116302472267310301183 13 (by decide) (by decide)
    [⟨199,1,valid_199⟩,
     ⟨398,5,valid_398⟩,
     ⟨597,5,valid_597⟩,
     ⟨796,9,valid_796⟩,
     ⟨995,5,valid_995⟩,
     ⟨1194,13,valid_1194⟩,
     ⟨1791,9,valid_1791⟩,
     ⟨1990,13,valid_1990⟩,
     ⟨3582,21,valid_3582⟩,
     ⟨3980,21,valid_3980⟩] (by decide)

private def column_51 : Column :=
  certifyColumn 51 2249598642943999 15 (by decide) (by decide)
    [⟨459,13,valid_459⟩,
     ⟨918,29,valid_918⟩,
     ⟨1836,45,valid_1836⟩] (by decide)

private def column_68 : Column :=
  certifyColumn 68 292823907025551359999 14 (by decide) (by decide)
    [⟨544,21,valid_544⟩,
     ⟨1632,45,valid_1632⟩,
     ⟨2720,45,valid_2720⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_323 : Column :=
  certifyColumn 323 14646768246350273410084164876880810859023885262757269491282417970871618618246495696434895272280063 12 (by decide) (by decide)
    [⟨323,5,valid_323⟩,
     ⟨646,13,valid_646⟩,
     ⟨969,13,valid_969⟩,
     ⟨1292,21,valid_1292⟩,
     ⟨1938,29,valid_1938⟩,
     ⟨2261,13,valid_2261⟩,
     ⟨3553,13,valid_3553⟩,
     ⟨3876,45,valid_3876⟩] (by decide)

private def column_57 : Column :=
  certifyColumn 57 144097595885615103 15 (by decide) (by decide)
    [⟨513,13,valid_513⟩,
     ⟨1026,29,valid_1026⟩,
     ⟨2052,45,valid_2052⟩] (by decide)

private def column_76 : Column :=
  certifyColumn 76 75484076749610886881279 14 (by decide) (by decide)
    [⟨608,21,valid_608⟩,
     ⟨1824,45,valid_1824⟩,
     ⟨3040,45,valid_3040⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_211 : Column :=
  certifyColumn 211 3291009114630439462885729339373793716228257831682194533680906239 13 (by decide) (by decide)
    [⟨211,1,valid_211⟩,
     ⟨422,5,valid_422⟩,
     ⟨633,5,valid_633⟩,
     ⟨844,9,valid_844⟩,
     ⟨1055,5,valid_1055⟩,
     ⟨1266,13,valid_1266⟩,
     ⟨1899,9,valid_1899⟩,
     ⟨2110,13,valid_2110⟩,
     ⟨3798,21,valid_3798⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_289 : Column :=
  certifyColumn 289 994525041188803250970853093110975843908341121159528068801606974335277507607322205093887 12 (by decide) (by decide)
    [⟨289,3,valid_289⟩,
     ⟨578,9,valid_578⟩,
     ⟨867,9,valid_867⟩,
     ⟨1156,15,valid_1156⟩,
     ⟨1445,9,valid_1445⟩,
     ⟨1734,21,valid_1734⟩,
     ⟨2023,9,valid_2023⟩,
     ⟨2312,21,valid_2312⟩,
     ⟨2890,21,valid_2890⟩,
     ⟨3468,33,valid_3468⟩] (by decide)

private def column_58 : Column :=
  certifyColumn 58 288230367557580799 15 (by decide) (by decide)
    [⟨464,17,valid_464⟩,
     ⟨1392,37,valid_1392⟩] (by decide)

private def column_62 : Column :=
  certifyColumn 62 4611545276643934207 14 (by decide) (by decide)
    [⟨496,17,valid_496⟩,
     ⟨1488,37,valid_1488⟩] (by decide)

private def column_64 : Column :=
  certifyColumn 64 18158513697012580351 14 (by decide) (by decide)
    [⟨512,17,valid_512⟩,
     ⟨1536,37,valid_1536⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_223 : Column :=
  certifyColumn 223 6739986591462438843418269541293782946505174485362027648804479565823 13 (by decide) (by decide)
    [⟨223,1,valid_223⟩,
     ⟨446,5,valid_446⟩,
     ⟨669,5,valid_669⟩,
     ⟨892,9,valid_892⟩,
     ⟨1115,5,valid_1115⟩,
     ⟨1338,13,valid_1338⟩,
     ⟨2007,9,valid_2007⟩,
     ⟨2230,13,valid_2230⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_227 : Column :=
  certifyColumn 227 148279706669326603251242500563089842063868886972061947272561667604479 13 (by decide) (by decide)
    [⟨227,1,valid_227⟩,
     ⟨454,5,valid_454⟩,
     ⟨681,5,valid_681⟩,
     ⟨908,9,valid_908⟩,
     ⟨1135,5,valid_1135⟩,
     ⟨1362,13,valid_1362⟩,
     ⟨2043,9,valid_2043⟩,
     ⟨2270,13,valid_2270⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_229 : Column :=
  certifyColumn 229 859335084355295699231654743752571217117636316410581167823416975163391 13 (by decide) (by decide)
    [⟨229,1,valid_229⟩,
     ⟨458,5,valid_458⟩,
     ⟨687,5,valid_687⟩,
     ⟨916,9,valid_916⟩,
     ⟨1145,5,valid_1145⟩,
     ⟨1374,13,valid_1374⟩,
     ⟨2061,9,valid_2061⟩,
     ⟨2290,13,valid_2290⟩] (by decide)

private def column_115 : Column :=
  certifyColumn 115 41211301051627159632935149167968255 14 (by decide) (by decide)
    [⟨575,9,valid_575⟩,
     ⟨1150,21,valid_1150⟩,
     ⟨1725,21,valid_1725⟩,
     ⟨3450,45,valid_3450⟩] (by decide)

private def column_69 : Column :=
  certifyColumn 69 590295810083827728255 14 (by decide) (by decide)
    [⟨621,13,valid_621⟩,
     ⟨1242,29,valid_1242⟩,
     ⟨2484,45,valid_2484⟩] (by decide)

private def column_92 : Column :=
  certifyColumn 92 4951760147918144664693104639 14 (by decide) (by decide)
    [⟨736,21,valid_736⟩,
     ⟨2208,45,valid_2208⟩,
     ⟨3680,45,valid_3680⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_233 : Column :=
  certifyColumn 233 13803492693574850449188879363264976008045080554288866926810121482797055 13 (by decide) (by decide)
    [⟨233,1,valid_233⟩,
     ⟨466,5,valid_466⟩,
     ⟨699,5,valid_699⟩,
     ⟨932,9,valid_932⟩,
     ⟨1165,5,valid_1165⟩,
     ⟨1398,13,valid_1398⟩,
     ⟨2097,9,valid_2097⟩,
     ⟨2330,13,valid_2330⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_239 : Column :=
  certifyColumn 239 883423427070460189852458740134703226850962537538951418876612420747394559 13 (by decide) (by decide)
    [⟨239,1,valid_239⟩,
     ⟨478,5,valid_478⟩,
     ⟨717,5,valid_717⟩,
     ⟨956,9,valid_956⟩,
     ⟨1195,5,valid_1195⟩,
     ⟨1434,13,valid_1434⟩,
     ⟨2151,9,valid_2151⟩,
     ⟨2390,13,valid_2390⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_241 : Column :=
  certifyColumn 241 3531968692944360009128281510685545811609720928524520567771931033930301439 13 (by decide) (by decide)
    [⟨241,1,valid_241⟩,
     ⟨482,5,valid_482⟩,
     ⟨723,5,valid_723⟩,
     ⟨964,9,valid_964⟩,
     ⟨1205,5,valid_1205⟩,
     ⟨1446,13,valid_1446⟩,
     ⟨2169,9,valid_2169⟩,
     ⟨2410,13,valid_2410⟩] (by decide)

private def column_74 : Column :=
  certifyColumn 74 18889465931478578741119 14 (by decide) (by decide)
    [⟨592,17,valid_592⟩,
     ⟨1776,37,valid_1776⟩] (by decide)

private def column_125 : Column :=
  certifyColumn 125 42535295231291998300287183137900855167 13 (by decide) (by decide)
    [⟨625,7,valid_625⟩,
     ⟨1250,17,valid_1250⟩,
     ⟨1875,17,valid_1875⟩,
     ⟨2500,27,valid_2500⟩,
     ⟨3750,37,valid_3750⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_251 : Column :=
  certifyColumn 251 3618502788665719329112703978009679458381990012997232118101384386945373700095 12 (by decide) (by decide)
    [⟨251,1,valid_251⟩,
     ⟨502,5,valid_502⟩,
     ⟨753,5,valid_753⟩,
     ⟨1004,9,valid_1004⟩,
     ⟨1255,5,valid_1255⟩,
     ⟨1506,13,valid_1506⟩,
     ⟨2259,9,valid_2259⟩,
     ⟨2510,13,valid_2510⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_257 : Column :=
  certifyColumn 257 231471100262065325081804368548919493675393563086987245039494613495812741660671 12 (by decide) (by decide)
    [⟨257,1,valid_257⟩,
     ⟨514,5,valid_514⟩,
     ⟨771,5,valid_771⟩,
     ⟨1028,9,valid_1028⟩,
     ⟨1285,5,valid_1285⟩,
     ⟨1542,13,valid_1542⟩,
     ⟨2313,9,valid_2313⟩,
     ⟨2570,13,valid_2570⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_361 : Column :=
  certifyColumn 361 4697084045538325198134762395710827071491771150846132262154737098150187480217864063209931794790975070023974399 12 (by decide) (by decide)
    [⟨361,3,valid_361⟩,
     ⟨722,9,valid_722⟩,
     ⟨1083,9,valid_1083⟩,
     ⟨1444,15,valid_1444⟩,
     ⟨1805,9,valid_1805⟩,
     ⟨2166,21,valid_2166⟩,
     ⟨2527,9,valid_2527⟩,
     ⟨2888,21,valid_2888⟩,
     ⟨3610,21,valid_3610⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_391 : Column :=
  certifyColumn 391 5043456793138493339171717132818382567050206570052850628643355073234953856850632741223146337643747538443154211542661119 12 (by decide) (by decide)
    [⟨391,5,valid_391⟩,
     ⟨782,13,valid_782⟩,
     ⟨1173,13,valid_1173⟩,
     ⟨1564,21,valid_1564⟩,
     ⟨2346,29,valid_2346⟩,
     ⟨2737,13,valid_2737⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_263 : Column :=
  certifyColumn 263 14821380354984843905739435107440589772588666045867193238307262075292534947446783 12 (by decide) (by decide)
    [⟨263,1,valid_263⟩,
     ⟨526,5,valid_526⟩,
     ⟨789,5,valid_789⟩,
     ⟨1052,9,valid_1052⟩,
     ⟨1315,5,valid_1315⟩,
     ⟨1578,13,valid_1578⟩,
     ⟨2367,9,valid_2367⟩,
     ⟨2630,13,valid_2630⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_269 : Column :=
  certifyColumn 269 948568787937099028408390466686089344205384257363703415706760386225777131445551103 12 (by decide) (by decide)
    [⟨269,1,valid_269⟩,
     ⟨538,5,valid_538⟩,
     ⟨807,5,valid_807⟩,
     ⟨1076,9,valid_1076⟩,
     ⟨1345,5,valid_1345⟩,
     ⟨1614,13,valid_1614⟩,
     ⟨2421,9,valid_2421⟩,
     ⟨2690,13,valid_2690⟩] (by decide)

private def column_81 : Column :=
  certifyColumn 81 2417851629096159154274303 14 (by decide) (by decide)
    [⟨729,11,valid_729⟩,
     ⟨1458,25,valid_1458⟩,
     ⟨2916,39,valid_2916⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_271 : Column :=
  certifyColumn 271 3557132979603506457810964050839868122037172644232182489826158286579939888238428159 12 (by decide) (by decide)
    [⟨271,1,valid_271⟩,
     ⟨542,5,valid_542⟩,
     ⟨813,5,valid_813⟩,
     ⟨1084,9,valid_1084⟩,
     ⟨1355,5,valid_1355⟩,
     ⟨1626,13,valid_1626⟩,
     ⟨2439,9,valid_2439⟩,
     ⟨2710,13,valid_2710⟩] (by decide)

private def column_82 : Column :=
  certifyColumn 82 4146237771959548497625087 14 (by decide) (by decide)
    [⟨656,17,valid_656⟩,
     ⟨1968,37,valid_1968⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_277 : Column :=
  certifyColumn 277 242831758854787905446659236589362878787654753771027215667044264783661016986991656959 12 (by decide) (by decide)
    [⟨277,1,valid_277⟩,
     ⟨554,5,valid_554⟩,
     ⟨831,5,valid_831⟩,
     ⟨1108,9,valid_1108⟩,
     ⟨1385,5,valid_1385⟩,
     ⟨1662,13,valid_1662⟩,
     ⟨2493,9,valid_2493⟩,
     ⟨2770,13,valid_2770⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_281 : Column :=
  certifyColumn 281 3885330373743608726211016235182372162947098252423321850244626647710935771000170610687 12 (by decide) (by decide)
    [⟨281,1,valid_281⟩,
     ⟨562,5,valid_562⟩,
     ⟨843,5,valid_843⟩,
     ⟨1124,9,valid_1124⟩,
     ⟨1405,5,valid_1405⟩,
     ⟨1686,13,valid_1686⟩,
     ⟨2529,9,valid_2529⟩,
     ⟨2810,13,valid_2810⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_283 : Column :=
  certifyColumn 283 15540402511111221944602392703501587853946130631709357428573099201869536660834192719871 12 (by decide) (by decide)
    [⟨283,1,valid_283⟩,
     ⟨566,5,valid_566⟩,
     ⟨849,5,valid_849⟩,
     ⟨1132,9,valid_1132⟩,
     ⟨1415,5,valid_1415⟩,
     ⟨1698,13,valid_1698⟩,
     ⟨2547,9,valid_2547⟩,
     ⟨2830,13,valid_2830⟩] (by decide)

private def column_86 : Column :=
  certifyColumn 86 77371252455336267046714879 14 (by decide) (by decide)
    [⟨688,17,valid_688⟩,
     ⟨2064,37,valid_2064⟩] (by decide)

private def column_87 : Column :=
  certifyColumn 87 154723613138898012208103423 14 (by decide) (by decide)
    [⟨783,13,valid_783⟩,
     ⟨1566,29,valid_1566⟩,
     ⟨3132,45,valid_3132⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_437 : Column :=
  certifyColumn 437 353509970629907525477718997992436308576208884422179792477969780362754299850125053730872752922997101856593355550173484315458425323519 12 (by decide) (by decide)
    [⟨437,5,valid_437⟩,
     ⟨874,13,valid_874⟩,
     ⟨1311,13,valid_1311⟩,
     ⟨1748,21,valid_1748⟩,
     ⟨2622,29,valid_2622⟩,
     ⟨3059,13,valid_3059⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_293 : Column :=
  certifyColumn 293 15914343565113144251812210047914504170451151777615787503894273716944310644619869134258175 12 (by decide) (by decide)
    [⟨293,1,valid_293⟩,
     ⟨586,5,valid_586⟩,
     ⟨879,5,valid_879⟩,
     ⟨1172,9,valid_1172⟩,
     ⟨1465,5,valid_1465⟩,
     ⟨1758,13,valid_1758⟩,
     ⟨2637,9,valid_2637⟩,
     ⟨2930,13,valid_2930⟩] (by decide)

private def column_119 : Column :=
  certifyColumn 119 664613997812668832357329208516542431 14 (by decide) (by decide)
    [⟨833,9,valid_833⟩,
     ⟨1666,21,valid_1666⟩,
     ⟨2499,21,valid_2499⟩,
     ⟨3332,33,valid_3332⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_307 : Column :=
  certifyColumn 307 260740604970814190094338738576723751508638787456492728084637303306104148310367119459812900863 12 (by decide) (by decide)
    [⟨307,1,valid_307⟩,
     ⟨614,5,valid_614⟩,
     ⟨921,5,valid_921⟩,
     ⟨1228,9,valid_1228⟩,
     ⟨1535,5,valid_1535⟩,
     ⟨1842,13,valid_1842⟩,
     ⟨2763,9,valid_2763⟩,
     ⟨3070,13,valid_3070⟩] (by decide)

private def column_93 : Column :=
  certifyColumn 93 9902311240889472781318619135 14 (by decide) (by decide)
    [⟨837,13,valid_837⟩,
     ⟨1674,29,valid_1674⟩,
     ⟨3348,45,valid_3348⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_311 : Column :=
  certifyColumn 311 4139000469457971706673265355996246940406177967538084302422653728771330049521786843198941822975 12 (by decide) (by decide)
    [⟨311,1,valid_311⟩,
     ⟨622,5,valid_622⟩,
     ⟨933,5,valid_933⟩,
     ⟨1244,9,valid_1244⟩,
     ⟨1555,5,valid_1555⟩,
     ⟨1866,13,valid_1866⟩,
     ⟨2799,9,valid_2799⟩,
     ⟨3110,13,valid_3110⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_313 : Column :=
  certifyColumn 313 16687398687049407685203397218227186969310705243283580737016746372423849656263512863510561284095 12 (by decide) (by decide)
    [⟨313,1,valid_313⟩,
     ⟨626,5,valid_626⟩,
     ⟨939,5,valid_939⟩,
     ⟨1252,9,valid_1252⟩,
     ⟨1565,5,valid_1565⟩,
     ⟨1878,13,valid_1878⟩,
     ⟨2817,9,valid_2817⟩,
     ⟨3130,13,valid_3130⟩] (by decide)

private def column_94 : Column :=
  certifyColumn 94 19807040628566084398385953759 14 (by decide) (by decide)
    [⟨752,17,valid_752⟩,
     ⟨2256,37,valid_2256⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_317 : Column :=
  certifyColumn 317 266998347661422835797400174047135327204339987146767478429917259419589074932326291071184662429695 12 (by decide) (by decide)
    [⟨317,1,valid_317⟩,
     ⟨634,5,valid_634⟩,
     ⟨951,5,valid_951⟩,
     ⟨1268,9,valid_1268⟩,
     ⟨1585,5,valid_1585⟩,
     ⟨1902,13,valid_1902⟩,
     ⟨2853,9,valid_2853⟩,
     ⟨3170,13,valid_3170⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_493 : Column :=
  certifyColumn 493 25573364124185701003887694324845232971404484263256218556528494790618494797529642471190376094377697810279725175424428719993375924918287930886853754879 11 (by decide) (by decide)
    [⟨493,5,valid_493⟩,
     ⟨986,13,valid_986⟩,
     ⟨1479,13,valid_1479⟩,
     ⟨1972,21,valid_1972⟩,
     ⟨2958,29,valid_2958⟩,
     ⟨3451,13,valid_3451⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_331 : Column :=
  certifyColumn 331 4374501449566023848744975506185299456323653563250639010410208379004061034788998431658607410928417791 12 (by decide) (by decide)
    [⟨331,1,valid_331⟩,
     ⟨662,5,valid_662⟩,
     ⟨993,5,valid_993⟩,
     ⟨1324,9,valid_1324⟩,
     ⟨1655,5,valid_1655⟩,
     ⟨1986,13,valid_1986⟩,
     ⟨2979,9,valid_2979⟩,
     ⟨3310,13,valid_3310⟩] (by decide)

private def column_133 : Column :=
  certifyColumn 133 10889035741469411841918878816199478575103 13 (by decide) (by decide)
    [⟨931,9,valid_931⟩,
     ⟨1862,21,valid_1862⟩,
     ⟨2793,21,valid_2793⟩,
     ⟨3724,33,valid_3724⟩] (by decide)

set_option maxRecDepth 8192 in
private def column_337 : Column :=
  certifyColumn 337 279968026022614739447675089817070941965912495154160327892769577642610690523258470085583875119853338623 12 (by decide) (by decide)
    [⟨337,1,valid_337⟩,
     ⟨674,5,valid_674⟩,
     ⟨1011,5,valid_1011⟩,
     ⟨1348,9,valid_1348⟩,
     ⟨1685,5,valid_1685⟩,
     ⟨2022,13,valid_2022⟩,
     ⟨3033,9,valid_3033⟩,
     ⟨3370,13,valid_3370⟩] (by decide)

private def column_136 : Column :=
  certifyColumn 136 87106969019757299942501412206146452717567 13 (by decide) (by decide)
    [⟨1088,25,valid_1088⟩,
     ⟨3264,53,valid_3264⟩] (by decide)

private def columns : List Column :=
  [column_17, column_19, column_23, column_29, column_31, column_37, column_41,
   column_43, column_47, column_4, column_8, column_53, column_59, column_61,
   column_67, column_71, column_73, column_79, column_83, column_89, column_97,
   column_101, column_103, column_16, column_107, column_25, column_109, column_113,
   column_127, column_131, column_137, column_139, column_34, column_149, column_151,
   column_157, column_163, column_38, column_27, column_167, column_85, column_173,
   column_179, column_181, column_46, column_95, column_191, column_32, column_193,
   column_197, column_199, column_51, column_68, column_323, column_57, column_76,
   column_211, column_289, column_58, column_62, column_64, column_223, column_227,
   column_229, column_115, column_69, column_92, column_233, column_239, column_241,
   column_74, column_125, column_251, column_257, column_361, column_391, column_263,
   column_269, column_81, column_271, column_82, column_277, column_281, column_283,
   column_86, column_87, column_437, column_293, column_119, column_307, column_93,
   column_311, column_313, column_94, column_317, column_493, column_331, column_133,
   column_337, column_136]

private def CheckedBlock (origin b : ℕ) : Prop :=
  ∀ i : ℕ, i < 1000000 → Good (360360*((origin+1000000*b)+i)) → False

private theorem singleChecked {origin : ℕ} (a : ℕ) (h : CheckedBlock origin a) :
    ∀ b : ℕ, a ≤ b → b < a+1 → CheckedBlock origin b := by
  intro b lo hi
  simpa only [show b = a by omega] using h

private theorem joinChecked {origin a b c : ℕ}
    (left : ∀ x : ℕ, a ≤ x → x < b → CheckedBlock origin x)
    (right : ∀ x : ℕ, b ≤ x → x < c → CheckedBlock origin x) :
    ∀ x : ℕ, a ≤ x → x < c → CheckedBlock origin x := by
  intro x lo hi
  by_cases before : x < b
  · exact left x lo before
  · exact right x (by omega) hi

private theorem failureFromBlocks {origin count n : ℕ} (originBound : 64 ≤ origin)
    (low : 360360*origin ≤ n) (high : n < 360360*(origin+1000000*count))
    (table : ∀ x : ℕ, 0 ≤ x → x < count → CheckedBlock origin x) :
    ¬ (⨆ m : Fin n, (m:ℕ)+σ 0 (m:ℕ)) ≤ n+2 := by
  intro claim
  have good : Good n := by
    intro m hm
    exact (le_ciSup (f := fun j : Fin n => (j:ℕ)+σ 0 (j:ℕ))
      (Set.finite_range _).bddAbove ⟨m,hm⟩).trans claim
  obtain ⟨q, eqn⟩ := necessaryDivisibility good (by omega)
  let b := (q-origin)/1000000
  let i := (q-origin)%1000000
  have lim : b < count := by dsimp [b]; omega
  have pos : i < 1000000 := Nat.mod_lt _ (by decide)
  have repr : 360360*((origin+1000000*b)+i) = n := by dsimp [b,i]; omega
  exact table b (Nat.zero_le _) lim i pos (repr ▸ good)



private def highPoints_0 : List (Witness 1000000000000000000) :=
  [⟨317755,witnessRule valid_1461 (by decide)⟩,
   ⟨789746,witnessRule valid_1299 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_0 : CheckedBlock 1000000000000000000 0 :=
  excludeBlock columns (a := 1000000000000000000) (width := 1000000) highPoints_0
    (by decide) (by decide) (by decide)

private def highPoints_1 : List (Witness 1000000000001000000) :=
  [⟨16875,witnessDivisors _ 3 [1,3,5927,17781,20266576682996819137,60799730048990457411] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨76995,witnessRule valid_2009 (by decide)⟩,
   ⟨550170,witnessDivisors _ 4 [1,2,4,4421,8842,17684,20377742592205305319] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨694494,witnessDivisors _ 2 [1,2,2063,4126,87338826951190166713] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨936592,witnessDivisors _ 3 [1,3,2447,7341,49088680016441611537,147266040049324834611] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_1 : CheckedBlock 1000000000000000000 1 :=
  excludeBlock columns (a := 1000000000001000000) (width := 1000000) highPoints_1
    (by decide) (by decide) (by decide)

private def highPoints_2 : List (Witness 1000000000002000000) :=
  [⟨414790,witnessDivisors _ 1 [1,43319,8318751587083501321,360360000000870193724399] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨610947,witnessDivisors _ 1 [1,45587,7904885164650906637,360360000000940880860919] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨641106,witnessDivisors _ 1 [1,7583,47522088883153336273,360360000000951748958159] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨749736,witnessRule valid_3479 (by decide)⟩,
   ⟨825912,witnessRule valid_3123 (by decide)⟩,
   ⟨865794,witnessRule valid_2348 (by decide)⟩,
   ⟨867840,witnessRule valid_698 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_2 : CheckedBlock 1000000000000000000 2 :=
  excludeBlock columns (a := 1000000000002000000) (width := 1000000) highPoints_2
    (by decide) (by decide) (by decide)

private def highPoints_3 : List (Witness 1000000000003000000) :=
  [⟨21251,witnessRule valid_2094 (by decide)⟩,
   ⟨52862,witnessRule valid_1257 (by decide)⟩,
   ⟨71803,witnessRule valid_2842 (by decide)⟩,
   ⟨312894,witnessRule valid_794 (by decide)⟩,
   ⟨340179,witnessRule valid_2325 (by decide)⟩,
   ⟨493440,witnessRule valid_2382 (by decide)⟩,
   ⟨645148,witnessRule valid_1813 (by decide)⟩,
   ⟨669826,witnessRule valid_848 (by decide)⟩,
   ⟨731675,witnessRule valid_1745 (by decide)⟩,
   ⟨772314,witnessRule valid_1328 (by decide)⟩,
   ⟨804954,witnessRule valid_866 (by decide)⟩,
   ⟨915536,witnessRule valid_706 (by decide)⟩,
   ⟨964411,witnessRule valid_1735 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_3 : CheckedBlock 1000000000000000000 3 :=
  excludeBlock columns (a := 1000000000003000000) (width := 1000000) highPoints_3
    (by decide) (by decide) (by decide)

private def highPoints_4 : List (Witness 1000000000004000000) :=
  [⟨139820,witnessRule valid_1808 (by decide)⟩,
   ⟨177022,witnessRule valid_1328 (by decide)⟩,
   ⟨717800,witnessRule valid_1461 (by decide)⟩,
   ⟨856579,witnessRule valid_2238 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_4 : CheckedBlock 1000000000000000000 4 :=
  excludeBlock columns (a := 1000000000004000000) (width := 1000000) highPoints_4
    (by decide) (by decide) (by decide)

private def highPoints_5 : List (Witness 1000000000005000000) :=
  [⟨49875,witnessDivisors _ 1 [1,4967,72550835514761379697,360360000001819772954999] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨58692,witnessRule valid_2515 (by decide)⟩,
   ⟨277211,witnessRule valid_3996 (by decide)⟩,
   ⟨288867,witnessRule valid_1101 (by decide)⟩,
   ⟨304827,witnessRule valid_3602 (by decide)⟩,
   ⟨810186,witnessRule valid_2348 (by decide)⟩,
   ⟨839763,witnessRule valid_2658 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_5 : CheckedBlock 1000000000000000000 5 :=
  excludeBlock columns (a := 1000000000005000000) (width := 1000000) highPoints_5
    (by decide) (by decide) (by decide)

private def highPoints_6 : List (Witness 1000000000006000000) :=
  [⟨3292,witnessDivisors _ 5 [1,5,21149,105745,3407820700762810027,17039103503814050135,72072000000432669261023,360360000002163346305115] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨11168,witnessRule valid_1138 (by decide)⟩,
   ⟨147531,witnessDivisors _ 2 [1,2,15859,31718,36433] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨321526,witnessRule valid_2406 (by decide)⟩,
   ⟨333160,witnessRule valid_2298 (by decide)⟩,
   ⟨735176,witnessDivisors _ 2 [1,2,2797,5594,64419020379411349307] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨736074,witnessRule valid_2175 (by decide)⟩,
   ⟨885300,witnessRule valid_1436 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_6 : CheckedBlock 1000000000000000000 6 :=
  excludeBlock columns (a := 1000000000006000000) (width := 1000000) highPoints_6
    (by decide) (by decide) (by decide)

private def highPoints_7 : List (Witness 1000000000007000000) :=
  [⟨154464,witnessRule valid_2118 (by decide)⟩,
   ⟨217012,witnessRule valid_2802 (by decide)⟩,
   ⟨358648,witnessRule valid_2586 (by decide)⟩,
   ⟨727052,witnessRule valid_1438 (by decide)⟩,
   ⟨888096,witnessRule valid_848 (by decide)⟩,
   ⟨989067,witnessRule valid_673 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_7 : CheckedBlock 1000000000000000000 7 :=
  excludeBlock columns (a := 1000000000007000000) (width := 1000000) highPoints_7
    (by decide) (by decide) (by decide)

private def highPoints_8 : List (Witness 1000000000008000000) :=
  [⟨223350,witnessRule valid_3411 (by decide)⟩,
   ⟨329288,witnessRule valid_3530 (by decide)⟩,
   ⟨368060,witnessRule valid_349 (by decide)⟩,
   ⟨650452,witnessRule valid_2876 (by decide)⟩,
   ⟨720396,witnessRule valid_1371 (by decide)⟩,
   ⟨723190,witnessRule valid_2188 (by decide)⟩,
   ⟨895380,witnessDivisors _ 5 [1,5,1327,6635,54311981914575062417,271559909572875312085,72072000000641107827359,360360000003205539136795] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨943555,witnessRule valid_2356 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_8 : CheckedBlock 1000000000000000000 8 :=
  excludeBlock columns (a := 1000000000008000000) (width := 1000000) highPoints_8
    (by decide) (by decide) (by decide)

private def highPoints_9 : List (Witness 1000000000009000000) :=
  [⟨107744,witnessRule valid_3075 (by decide)⟩,
   ⟨187644,witnessRule valid_2775 (by decide)⟩,
   ⟨192294,witnessRule valid_2308 (by decide)⟩,
   ⟨354218,witnessDivisors _ 1 [1,7867,45806533621885202237,360360000003370885998479] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨376403,witnessDivisors _ 2 [1,2,5519,11038,18899] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨675292,witnessDivisors _ 7 [1,7,31,53,217,371,1643,11501,31332927571818675613,219330493002730729291] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨742331,witnessRule valid_2463 (by decide)⟩,
   ⟨884635,witnessRule valid_523 (by decide)⟩,
   ⟨955979,witnessRule valid_2396 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_9 : CheckedBlock 1000000000000000000 9 :=
  excludeBlock columns (a := 1000000000009000000) (width := 1000000) highPoints_9
    (by decide) (by decide) (by decide)

private def highPoints_10 : List (Witness 1000000000010000000) :=
  [⟨88976,witnessRule valid_1563 (by decide)⟩,
   ⟨321875,witnessDivisors _ 6 [1,2,3,6,2551,5102,7653,15306,23543708349909812549] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨338275,witnessRule valid_1964 (by decide)⟩,
   ⟨520894,witnessRule valid_1072 (by decide)⟩,
   ⟨526499,witnessRule valid_421 (by decide)⟩,
   ⟨713924,witnessRule valid_862 (by decide)⟩,
   ⟨885811,witnessRule valid_1167 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_10 : CheckedBlock 1000000000000000000 10 :=
  excludeBlock columns (a := 1000000000010000000) (width := 1000000) highPoints_10
    (by decide) (by decide) (by decide)

private def highPoints_11 : List (Witness 1000000000011000000) :=
  [⟨81464,witnessDivisors _ 3 [1,3,1877,5631,21193,63579] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨293578,witnessDivisors _ 2 [1,2,2803,5606,64281127364265029213] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨399947,witnessRule valid_3231 (by decide)⟩,
   ⟨421659,witnessRule valid_3604 (by decide)⟩,
   ⟨545994,witnessRule valid_1072 (by decide)⟩,
   ⟨628586,witnessRule valid_706 (by decide)⟩,
   ⟨880147,witnessRule valid_2094 (by decide)⟩,
   ⟨910899,witnessRule valid_1396 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_11 : CheckedBlock 1000000000000000000 11 :=
  excludeBlock columns (a := 1000000000011000000) (width := 1000000) highPoints_11
    (by decide) (by decide) (by decide)

private def highPoints_12 : List (Witness 1000000000012000000) :=
  [⟨71572,witnessRule valid_2572 (by decide)⟩,
   ⟨156331,witnessRule valid_746 (by decide)⟩,
   ⟨341827,witnessRule valid_1654 (by decide)⟩,
   ⟨354786,witnessRule valid_3305 (by decide)⟩,
   ⟨629387,witnessDivisors _ 6 [1,2,3,6,947,1894,2841,5682,63421330518224414977] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨636595,witnessRule valid_2339 (by decide)⟩,
   ⟨694038,witnessRule valid_2787 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_12 : CheckedBlock 1000000000000000000 12 :=
  excludeBlock columns (a := 1000000000012000000) (width := 1000000) highPoints_12
    (by decide) (by decide) (by decide)

private def highPoints_13 : List (Witness 1000000000013000000) :=
  [⟨94190,witnessRule valid_1286 (by decide)⟩,
   ⟨207880,witnessRule valid_1138 (by decide)⟩,
   ⟨255962,witnessRule valid_1835 (by decide)⟩,
   ⟨580163,witnessRule valid_3530 (by decide)⟩,
   ⟨645835,witnessRule valid_3857 (by decide)⟩,
   ⟨794828,witnessRule valid_2514 (by decide)⟩,
   ⟨902387,witnessRule valid_2634 (by decide)⟩,
   ⟨951851,witnessRule valid_1396 (by decide)⟩,
   ⟨980990,witnessRule valid_2514 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_13 : CheckedBlock 1000000000000000000 13 :=
  excludeBlock columns (a := 1000000000013000000) (width := 1000000) highPoints_13
    (by decide) (by decide) (by decide)

private def highPoints_14 : List (Witness 1000000000014000000) :=
  [⟨309146,witnessRule valid_3590 (by decide)⟩,
   ⟨388828,witnessRule valid_2334 (by decide)⟩,
   ⟨430112,witnessRule valid_1299 (by decide)⟩,
   ⟨494180,witnessRule valid_1765 (by decide)⟩,
   ⟨504136,witnessDivisors _ 3 [1,3,37633,112899,3191879467534935743,9575638402604807229] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨913950,witnessRule valid_1072 (by decide)⟩,
   ⟨961612,witnessRule valid_706 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_14 : CheckedBlock 1000000000000000000 14 :=
  excludeBlock columns (a := 1000000000014000000) (width := 1000000) highPoints_14
    (by decide) (by decide) (by decide)

private def highPoints_15 : List (Witness 1000000000015000000) :=
  [⟨19480,witnessRule valid_1041 (by decide)⟩,
   ⟨264110,witnessRule valid_758 (by decide)⟩,
   ⟨292902,witnessRule valid_1072 (by decide)⟩,
   ⟨388352,witnessRule valid_3215 (by decide)⟩,
   ⟨414350,witnessRule valid_3626 (by decide)⟩,
   ⟨428004,witnessRule valid_1328 (by decide)⟩,
   ⟨524819,witnessRule valid_2775 (by decide)⟩,
   ⟨799734,witnessRule valid_2175 (by decide)⟩,
   ⟨953924,witnessRule valid_349 (by decide)⟩,
   ⟨993387,witnessRule valid_1383 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_15 : CheckedBlock 1000000000000000000 15 :=
  excludeBlock columns (a := 1000000000015000000) (width := 1000000) highPoints_15
    (by decide) (by decide) (by decide)

private def highPoints_16 : List (Witness 1000000000016000000) :=
  [⟨5072,witnessRule valid_974 (by decide)⟩,
   ⟨112331,witnessRule valid_3381 (by decide)⟩,
   ⟨285563,witnessRule valid_2516 (by decide)⟩,
   ⟨295480,witnessDivisors _ 2 [1,2,97169,194338,1854295094144594671] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨349112,witnessRule valid_1724 (by decide)⟩,
   ⟨459742,witnessDivisors _ 1 [1,12157,29642181459729491867,360360000005931432627119] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨492394,witnessRule valid_3357 (by decide)⟩,
   ⟨756971,witnessRule valid_2254 (by decide)⟩,
   ⟨767992,witnessRule valid_1648 (by decide)⟩,
   ⟨824803,witnessDivisors _ 2 [1,2,11489,22978,15682827052226607451] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨888202,witnessRule valid_3590 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_16 : CheckedBlock 1000000000000000000 16 :=
  excludeBlock columns (a := 1000000000016000000) (width := 1000000) highPoints_16
    (by decide) (by decide) (by decide)

private def highPoints_17 : List (Witness 1000000000017000000) :=
  [⟨1442,witnessDivisors _ 1 [1,35027,10288063494051064597,360360000006126639639119] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨5227,witnessRule valid_2138 (by decide)⟩,
   ⟨227451,witnessRule valid_1388 (by decide)⟩,
   ⟨476784,witnessRule valid_1813 (by decide)⟩,
   ⟨955850,witnessRule valid_2066 (by decide)⟩,
   ⟨996792,witnessRule valid_2455 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_17 : CheckedBlock 1000000000000000000 17 :=
  excludeBlock columns (a := 1000000000017000000) (width := 1000000) highPoints_17
    (by decide) (by decide) (by decide)

private def highPoints_18 : List (Witness 1000000000018000000) :=
  [⟨50755,witnessRule valid_3678 (by decide)⟩,
   ⟨113723,witnessRule valid_3790 (by decide)⟩,
   ⟨290611,witnessRule valid_2788 (by decide)⟩,
   ⟨426235,witnessRule valid_3501 (by decide)⟩,
   ⟨472299,witnessRule valid_2154 (by decide)⟩,
   ⟨666700,witnessRule valid_706 (by decide)⟩,
   ⟨702286,witnessRule valid_1857 (by decide)⟩,
   ⟨751779,witnessRule valid_3138 (by decide)⟩,
   ⟨888028,witnessRule valid_701 (by decide)⟩,
   ⟨889000,witnessRule valid_2742 (by decide)⟩,
   ⟨987212,witnessRule valid_802 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_18 : CheckedBlock 1000000000000000000 18 :=
  excludeBlock columns (a := 1000000000018000000) (width := 1000000) highPoints_18
    (by decide) (by decide) (by decide)

private def highPoints_19 : List (Witness 1000000000019000000) :=
  [⟨91028,witnessRule valid_1556 (by decide)⟩,
   ⟨247612,witnessRule valid_886 (by decide)⟩,
   ⟨291778,witnessRule valid_3830 (by decide)⟩,
   ⟨362867,witnessRule valid_751 (by decide)⟩,
   ⟨503440,witnessRule valid_1473 (by decide)⟩,
   ⟨563886,witnessRule valid_3177 (by decide)⟩,
   ⟨569048,witnessRule valid_1879 (by decide)⟩,
   ⟨651011,witnessDivisors _ 1 [1,9739,37747,41263] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_19 : CheckedBlock 1000000000000000000 19 :=
  excludeBlock columns (a := 1000000000019000000) (width := 1000000) highPoints_19
    (by decide) (by decide) (by decide)

private def highPoints_20 : List (Witness 1000000000020000000) :=
  [⟨32236,witnessDivisors _ 1 [1,18181,33547,609918007] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨149763,witnessRule valid_1383 (by decide)⟩,
   ⟨379076,witnessRule valid_3254 (by decide)⟩,
   ⟨416059,witnessDivisors _ 3 [1,3,11113,33339,10808962476599691983,32426887429799075949] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨433238,witnessRule valid_2283 (by decide)⟩,
   ⟨965187,witnessRule valid_2307 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_20 : CheckedBlock 1000000000000000000 20 :=
  excludeBlock columns (a := 1000000000020000000) (width := 1000000) highPoints_20
    (by decide) (by decide) (by decide)

private def highPoints_21 : List (Witness 1000000000021000000) :=
  [⟨11402,witnessRule valid_2154 (by decide)⟩,
   ⟨107667,witnessRule valid_698 (by decide)⟩,
   ⟨224610,witnessRule valid_1895 (by decide)⟩,
   ⟨271618,witnessDivisors _ 3 [1,3,23879,71637,5030361405525991321,15091084216577973963] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨404600,witnessRule valid_2228 (by decide)⟩,
   ⟨408760,witnessRule valid_3411 (by decide)⟩,
   ⟨433971,witnessRule valid_3274 (by decide)⟩,
   ⟨656090,witnessDivisors _ 2 [1,2,2179,4358,82689307023360254381] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨924795,witnessRule valid_2823 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_21 : CheckedBlock 1000000000000000000 21 :=
  excludeBlock columns (a := 1000000000021000000) (width := 1000000) highPoints_21
    (by decide) (by decide) (by decide)

private def highPoints_22 : List (Witness 1000000000022000000) :=
  [⟨375938,witnessRule valid_2526 (by decide)⟩,
   ⟨386146,witnessRule valid_3695 (by decide)⟩,
   ⟨472926,witnessRule valid_2228 (by decide)⟩,
   ⟨775684,witnessRule valid_1077 (by decide)⟩,
   ⟨962619,witnessRule valid_3231 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_22 : CheckedBlock 1000000000000000000 22 :=
  excludeBlock columns (a := 1000000000022000000) (width := 1000000) highPoints_22
    (by decide) (by decide) (by decide)

private def highPoints_23 : List (Witness 1000000000023000000) :=
  [⟨7811,witnessRule valid_1486 (by decide)⟩,
   ⟨325651,witnessDivisors _ 3 [1,3,1637,4911,73378130728651116187,220134392185953348561] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨616748,witnessRule valid_347 (by decide)⟩,
   ⟨641324,witnessRule valid_2775 (by decide)⟩,
   ⟨661611,witnessRule valid_359 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_23 : CheckedBlock 1000000000000000000 23 :=
  excludeBlock columns (a := 1000000000023000000) (width := 1000000) highPoints_23
    (by decide) (by decide) (by decide)

private def highPoints_24 : List (Witness 1000000000024000000) :=
  [⟨179986,witnessRule valid_746 (by decide)⟩,
   ⟨182996,witnessRule valid_944 (by decide)⟩,
   ⟨450354,witnessRule valid_1257 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_24 : CheckedBlock 1000000000000000000 24 :=
  excludeBlock columns (a := 1000000000024000000) (width := 1000000) highPoints_24
    (by decide) (by decide) (by decide)

private def highPoints_25 : List (Witness 1000000000025000000) :=
  [⟨103970,witnessRule valid_433 (by decide)⟩,
   ⟨132610,witnessRule valid_1136 (by decide)⟩,
   ⟨384340,witnessDivisors _ 2 [1,2,2351,4702,76639727777360166049] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨457990,witnessRule valid_3442 (by decide)⟩,
   ⟨574131,witnessRule valid_3076 (by decide)⟩,
   ⟨587476,witnessDivisors _ 6 [1,2,3,6,3121,6242,9363,18726,19243832105586922079] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨713930,witnessRule valid_3702 (by decide)⟩,
   ⟨738354,witnessRule valid_1149 (by decide)⟩,
   ⟨762811,witnessRule valid_3681 (by decide)⟩,
   ⟨787387,witnessRule valid_1519 (by decide)⟩,
   ⟨907923,witnessRule valid_1538 (by decide)⟩,
   ⟨999939,witnessRule valid_2325 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_25 : CheckedBlock 1000000000000000000 25 :=
  excludeBlock columns (a := 1000000000025000000) (width := 1000000) highPoints_25
    (by decide) (by decide) (by decide)

private def highPoints_26 : List (Witness 1000000000026000000) :=
  [⟨283680,witnessRule valid_2672 (by decide)⟩,
   ⟨284348,witnessRule valid_2672 (by decide)⟩,
   ⟨611395,witnessRule valid_3018 (by decide)⟩,
   ⟨655798,witnessRule valid_2994 (by decide)⟩,
   ⟨696771,witnessRule valid_2516 (by decide)⟩,
   ⟨702922,witnessRule valid_718 (by decide)⟩,
   ⟨789226,witnessRule valid_3414 (by decide)⟩,
   ⟨999612,witnessRule valid_2545 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_26 : CheckedBlock 1000000000000000000 26 :=
  excludeBlock columns (a := 1000000000026000000) (width := 1000000) highPoints_26
    (by decide) (by decide) (by decide)

private def highPoints_27 : List (Witness 1000000000027000000) :=
  [⟨201804,witnessRule valid_2842 (by decide)⟩,
   ⟨358952,witnessRule valid_1059 (by decide)⟩,
   ⟨385110,witnessRule valid_1047 (by decide)⟩,
   ⟨583596,witnessRule valid_491 (by decide)⟩,
   ⟨726356,witnessRule valid_862 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_27 : CheckedBlock 1000000000000000000 27 :=
  excludeBlock columns (a := 1000000000027000000) (width := 1000000) highPoints_27
    (by decide) (by decide) (by decide)

private def highPoints_28 : List (Witness 1000000000028000000) :=
  [⟨64810,witnessRule valid_3381 (by decide)⟩,
   ⟨309156,witnessRule valid_3996 (by decide)⟩,
   ⟨401936,witnessRule valid_1127 (by decide)⟩,
   ⟨465075,witnessRule valid_2798 (by decide)⟩,
   ⟨546403,witnessRule valid_1532 (by decide)⟩,
   ⟨746940,witnessRule valid_3996 (by decide)⟩,
   ⟨973051,witnessRule valid_2253 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_28 : CheckedBlock 1000000000000000000 28 :=
  excludeBlock columns (a := 1000000000028000000) (width := 1000000) highPoints_28
    (by decide) (by decide) (by decide)

private def highPoints_29 : List (Witness 1000000000029000000) :=
  [⟨52192,witnessRule valid_1865 (by decide)⟩,
   ⟨85864,witnessRule valid_1329 (by decide)⟩,
   ⟨150435,witnessDivisors _ 5 [1,5,34147,170735,2110639294875126077,10553196474375630385,72072000002100930151319,360360000010504650756595] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨170920,witnessRule valid_1329 (by decide)⟩,
   ⟨315610,witnessRule valid_1492 (by decide)⟩,
   ⟨418740,witnessRule valid_3376 (by decide)⟩,
   ⟨520267,witnessRule valid_1735 (by decide)⟩,
   ⟨552003,witnessDivisors _ 3 [1,3,2341,7023,26261,78783] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨609390,witnessRule valid_1636 (by decide)⟩,
   ⟨636204,witnessRule valid_2768 (by decide)⟩,
   ⟨666864,witnessRule valid_976 (by decide)⟩,
   ⟨688531,witnessRule valid_1945 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_29 : CheckedBlock 1000000000000000000 29 :=
  excludeBlock columns (a := 1000000000029000000) (width := 1000000) highPoints_29
    (by decide) (by decide) (by decide)

private def highPoints_30 : List (Witness 1000000000030000000) :=
  [⟨160884,witnessRule valid_838 (by decide)⟩,
   ⟨184596,witnessRule valid_934 (by decide)⟩,
   ⟨712364,witnessDivisors _ 3 [1,3,3457,4639,10371,13917] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨890142,witnessRule valid_1136 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_30 : CheckedBlock 1000000000000000000 30 :=
  excludeBlock columns (a := 1000000000030000000) (width := 1000000) highPoints_30
    (by decide) (by decide) (by decide)

private def highPoints_31 : List (Witness 1000000000031000000) :=
  [⟨185635,witnessRule valid_659 (by decide)⟩,
   ⟨200494,witnessRule valid_1328 (by decide)⟩,
   ⟨321587,witnessRule valid_2108 (by decide)⟩,
   ⟨361262,witnessDivisors _ 4 [1,2,4,29009,58018,116036,3105587921087432731] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨452320,witnessRule valid_706 (by decide)⟩,
   ⟨470122,witnessRule valid_3617 (by decide)⟩,
   ⟨649038,witnessRule valid_758 (by decide)⟩,
   ⟨693930,witnessRule valid_3018 (by decide)⟩,
   ⟨745123,witnessRule valid_838 (by decide)⟩,
   ⟨795080,witnessRule valid_2764 (by decide)⟩,
   ⟨867964,witnessRule valid_3214 (by decide)⟩,
   ⟨894830,witnessDivisors _ 2 [1,2,10771,21542,16728251787739932269] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨947187,witnessRule valid_2082 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_31 : CheckedBlock 1000000000000000000 31 :=
  excludeBlock columns (a := 1000000000031000000) (width := 1000000) highPoints_31
    (by decide) (by decide) (by decide)

private def highPoints_32 : List (Witness 1000000000032000000) :=
  [⟨182490,witnessDivisors _ 7 [1,7,29,203,25031,175217,725899,5081293,70918957047270701,496432699330894907] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨204938,witnessRule valid_3594 (by decide)⟩,
   ⟨329347,witnessDivisors _ 1 [1,16649,21644543216508511231,360360000011650203484919] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨571334,witnessRule valid_734 (by decide)⟩,
   ⟨634120,witnessRule valid_3730 (by decide)⟩,
   ⟨652220,witnessRule valid_1136 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_32 : CheckedBlock 1000000000000000000 32 :=
  excludeBlock columns (a := 1000000000032000000) (width := 1000000) highPoints_32
    (by decide) (by decide) (by decide)

private def highPoints_33 : List (Witness 1000000000033000000) :=
  [⟨224298,witnessRule valid_2598 (by decide)⟩,
   ⟨330443,witnessRule valid_3099 (by decide)⟩,
   ⟨360395,witnessRule valid_3681 (by decide)⟩,
   ⟨468764,witnessRule valid_3897 (by decide)⟩,
   ⟨531636,witnessDivisors _ 5 [1,5,13687,68435,5265726602061568793,26328633010307843965,72072000002416692069791,360360000012083460348955] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨578040,witnessRule valid_3342 (by decide)⟩,
   ⟨578476,witnessRule valid_2713 (by decide)⟩,
   ⟨904811,witnessRule valid_3909 (by decide)⟩,
   ⟨920771,witnessRule valid_2396 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_33 : CheckedBlock 1000000000000000000 33 :=
  excludeBlock columns (a := 1000000000033000000) (width := 1000000) highPoints_33
    (by decide) (by decide) (by decide)

private def highPoints_34 : List (Witness 1000000000034000000) :=
  [⟨280859,witnessRule valid_2775 (by decide)⟩,
   ⟨545051,witnessRule valid_2785 (by decide)⟩,
   ⟨624588,witnessRule valid_643 (by decide)⟩,
   ⟨656531,witnessRule valid_2802 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_34 : CheckedBlock 1000000000000000000 34 :=
  excludeBlock columns (a := 1000000000034000000) (width := 1000000) highPoints_34
    (by decide) (by decide) (by decide)

private def highPoints_35 : List (Witness 1000000000035000000) :=
  [⟨414686,witnessRule valid_2395 (by decide)⟩,
   ⟨572236,witnessRule valid_2526 (by decide)⟩,
   ⟨633986,witnessRule valid_2785 (by decide)⟩,
   ⟨719555,witnessRule valid_389 (by decide)⟩,
   ⟨869572,witnessRule valid_1538 (by decide)⟩,
   ⟨985843,witnessRule valid_2516 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_35 : CheckedBlock 1000000000000000000 35 :=
  excludeBlock columns (a := 1000000000035000000) (width := 1000000) highPoints_35
    (by decide) (by decide) (by decide)

private def highPoints_36 : List (Witness 1000000000036000000) :=
  [⟨4770,witnessRule valid_2202 (by decide)⟩,
   ⟨158971,witnessRule valid_2454 (by decide)⟩,
   ⟨354276,witnessRule valid_3897 (by decide)⟩,
   ⟨482275,witnessDivisors _ 7 [1,7,241,1181,1687,8267,284621,1992347,180872107124485219,1266104749871396533] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨748126,witnessRule valid_1744 (by decide)⟩,
   ⟨777026,witnessRule valid_3284 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_36 : CheckedBlock 1000000000000000000 36 :=
  excludeBlock columns (a := 1000000000036000000) (width := 1000000) highPoints_36
    (by decide) (by decide) (by decide)

private def highPoints_37 : List (Witness 1000000000037000000) :=
  [⟨4186,witnessRule valid_3231 (by decide)⟩,
   ⟨21276,witnessRule valid_1136 (by decide)⟩,
   ⟨258163,witnessRule valid_2374 (by decide)⟩,
   ⟨679627,witnessRule valid_2082 (by decide)⟩,
   ⟨743590,witnessRule valid_2095 (by decide)⟩,
   ⟨760312,witnessRule valid_944 (by decide)⟩,
   ⟨828334,witnessDivisors _ 1 [1,95989,3754180166619423251,360360000013631818440239] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨902318,witnessRule valid_2298 (by decide)⟩,
   ⟨927779,witnessRule valid_1198 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_37 : CheckedBlock 1000000000000000000 37 :=
  excludeBlock columns (a := 1000000000037000000) (width := 1000000) highPoints_37
    (by decide) (by decide) (by decide)

private def highPoints_38 : List (Witness 1000000000038000000) :=
  [⟨8642,witnessRule valid_2105 (by decide)⟩,
   ⟨100470,witnessRule valid_1114 (by decide)⟩,
   ⟨132142,witnessRule valid_1136 (by decide)⟩,
   ⟨157942,witnessRule valid_976 (by decide)⟩,
   ⟨247795,witnessRule valid_2094 (by decide)⟩,
   ⟨527315,witnessRule valid_2654 (by decide)⟩,
   ⟨548947,witnessRule valid_3594 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_38 : CheckedBlock 1000000000000000000 38 :=
  excludeBlock columns (a := 1000000000038000000) (width := 1000000) highPoints_38
    (by decide) (by decide) (by decide)

private def highPoints_39 : List (Witness 1000000000039000000) :=
  [⟨16340,witnessRule valid_1486 (by decide)⟩,
   ⟨130571,witnessRule valid_1198 (by decide)⟩,
   ⟨260763,witnessDivisors _ 4 [1,2,4,11083,22166,44332,8128665524094288743] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨316996,witnessDivisors _ 5 [1,5,22003,110015,3275553333765107237,16377766668825536185,72072000002833654535711,360360000014168272678555] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨402835,witnessRule valid_3123 (by decide)⟩,
   ⟨415352,witnessRule valid_3054 (by decide)⟩,
   ⟨623042,witnessRule valid_3966 (by decide)⟩,
   ⟨794155,witnessRule valid_838 (by decide)⟩,
   ⟨839579,witnessRule valid_2325 (by decide)⟩,
   ⟨863651,witnessRule valid_3123 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_39 : CheckedBlock 1000000000000000000 39 :=
  excludeBlock columns (a := 1000000000039000000) (width := 1000000) highPoints_39
    (by decide) (by decide) (by decide)

private def highPoints_40 : List (Witness 1000000000040000000) :=
  [⟨352784,witnessRule valid_379 (by decide)⟩,
   ⟨744770,witnessRule valid_2586 (by decide)⟩,
   ⟨880404,witnessRule valid_3730 (by decide)⟩,
   ⟨996715,witnessRule valid_409 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_40 : CheckedBlock 1000000000000000000 40 :=
  excludeBlock columns (a := 1000000000040000000) (width := 1000000) highPoints_40
    (by decide) (by decide) (by decide)

private def highPoints_41 : List (Witness 1000000000041000000) :=
  [⟨252678,witnessRule valid_694 (by decide)⟩,
   ⟨578172,witnessRule valid_2082 (by decide)⟩,
   ⟨587822,witnessRule valid_2218 (by decide)⟩,
   ⟨811579,witnessRule valid_2204 (by decide)⟩,
   ⟨848240,witnessRule valid_3786 (by decide)⟩,
   ⟨848936,witnessRule valid_353 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_41 : CheckedBlock 1000000000000000000 41 :=
  excludeBlock columns (a := 1000000000041000000) (width := 1000000) highPoints_41
    (by decide) (by decide) (by decide)

private def highPoints_42 : List (Witness 1000000000042000000) :=
  [⟨158240,witnessRule valid_349 (by decide)⟩,
   ⟨313518,witnessRule valid_778 (by decide)⟩,
   ⟨549336,witnessRule valid_1136 (by decide)⟩,
   ⟨717410,witnessRule valid_2192 (by decide)⟩,
   ⟨872200,witnessRule valid_2005 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_42 : CheckedBlock 1000000000000000000 42 :=
  excludeBlock columns (a := 1000000000042000000) (width := 1000000) highPoints_42
    (by decide) (by decide) (by decide)

private def highPoints_43 : List (Witness 1000000000043000000) :=
  [⟨96640,witnessRule valid_694 (by decide)⟩,
   ⟨184598,witnessRule valid_2778 (by decide)⟩,
   ⟨432294,witnessDivisors _ 4 [1,2,4,9839,18443,19678,36886] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨545259,witnessDivisors _ 1 [1,4793,75184644276171911023,360360000015691969533239] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨694678,witnessRule valid_1396 (by decide)⟩,
   ⟨755251,witnessRule valid_2516 (by decide)⟩,
   ⟨802851,witnessDivisors _ 1 [1,12043,29922776718075628613,360360000015784795386359] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨868800,witnessRule valid_1136 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_43 : CheckedBlock 1000000000000000000 43 :=
  excludeBlock columns (a := 1000000000043000000) (width := 1000000) highPoints_43
    (by decide) (by decide) (by decide)

private def highPoints_44 : List (Witness 1000000000044000000) :=
  [⟨31243,witnessRule valid_2999 (by decide)⟩,
   ⟨157531,witnessRule valid_1684 (by decide)⟩,
   ⟨168836,witnessRule valid_3670 (by decide)⟩,
   ⟨250872,witnessDivisors _ 1 [1,51991,6931199631012026009,360360000015946244233919] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨295996,witnessRule valid_1072 (by decide)⟩,
   ⟨425626,witnessRule valid_2045 (by decide)⟩,
   ⟨677244,witnessRule valid_3225 (by decide)⟩,
   ⟨696998,witnessRule valid_347 (by decide)⟩,
   ⟨861354,witnessRule valid_976 (by decide)⟩,
   ⟨996906,witnessRule valid_2165 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_44 : CheckedBlock 1000000000000000000 44 :=
  excludeBlock columns (a := 1000000000044000000) (width := 1000000) highPoints_44
    (by decide) (by decide) (by decide)

private def highPoints_45 : List (Witness 1000000000045000000) :=
  [⟨6627,witnessRule valid_2306 (by decide)⟩,
   ⟨87635,witnessRule valid_1082 (by decide)⟩,
   ⟨342986,witnessRule valid_2154 (by decide)⟩,
   ⟨464242,witnessRule valid_1622 (by decide)⟩,
   ⟨488070,witnessRule valid_1217 (by decide)⟩,
   ⟨628923,witnessRule valid_1796 (by decide)⟩,
   ⟨923930,witnessRule valid_3871 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_45 : CheckedBlock 1000000000000000000 45 :=
  excludeBlock columns (a := 1000000000045000000) (width := 1000000) highPoints_45
    (by decide) (by decide) (by decide)

private def highPoints_46 : List (Witness 1000000000046000000) :=
  [⟨53915,witnessDivisors _ 2 [1,2,9311,18622,32413] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨241102,witnessRule valid_401 (by decide)⟩,
   ⟨245315,witnessRule valid_2103 (by decide)⟩,
   ⟨401596,witnessRule valid_1421 (by decide)⟩,
   ⟨553970,witnessRule valid_2956 (by decide)⟩,
   ⟨612144,witnessRule valid_3357 (by decide)⟩,
   ⟨641072,witnessRule valid_479 (by decide)⟩,
   ⟨774179,witnessRule valid_2518 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_46 : CheckedBlock 1000000000000000000 46 :=
  excludeBlock columns (a := 1000000000046000000) (width := 1000000) highPoints_46
    (by decide) (by decide) (by decide)

private def highPoints_47 : List (Witness 1000000000047000000) :=
  [⟨163051,witnessRule valid_673 (by decide)⟩,
   ⟨180170,witnessRule valid_898 (by decide)⟩,
   ⟨275906,witnessRule valid_1041 (by decide)⟩,
   ⟨290251,witnessRule valid_3530 (by decide)⟩,
   ⟨364147,witnessDivisors _ 7 [1,7,19,133,9923,69461,188537,1319759,273049852296569407,1911348966075985849] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨420426,witnessRule valid_746 (by decide)⟩,
   ⟨658179,witnessDivisors _ 3 [1,3,57713,173139,2081333495152300183,6244000485456900549] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨663696,witnessRule valid_2009 (by decide)⟩,
   ⟨809476,witnessRule valid_3670 (by decide)⟩,
   ⟨896712,witnessRule valid_1532 (by decide)⟩,
   ⟨975187,witnessRule valid_982 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_47 : CheckedBlock 1000000000000000000 47 :=
  excludeBlock columns (a := 1000000000047000000) (width := 1000000) highPoints_47
    (by decide) (by decide) (by decide)

private def highPoints_48 : List (Witness 1000000000048000000) :=
  [⟨596628,witnessRule valid_976 (by decide)⟩,
   ⟨621056,witnessDivisors _ 5 [1,5,5927,8971,29635,44855,53171117,265855585] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨838226,witnessRule valid_3632 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_48 : CheckedBlock 1000000000000000000 48 :=
  excludeBlock columns (a := 1000000000048000000) (width := 1000000) highPoints_48
    (by decide) (by decide) (by decide)

private def highPoints_49 : List (Witness 1000000000049000000) :=
  [⟨37522,witnessRule valid_2458 (by decide)⟩,
   ⟨49360,witnessRule valid_1401 (by decide)⟩,
   ⟨528686,witnessRule valid_3381 (by decide)⟩,
   ⟨757192,witnessRule valid_3126 (by decide)⟩,
   ⟨763598,witnessRule valid_1072 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_49 : CheckedBlock 1000000000000000000 49 :=
  excludeBlock columns (a := 1000000000049000000) (width := 1000000) highPoints_49
    (by decide) (by decide) (by decide)

private def highPoints_50 : List (Witness 1000000000050000000) :=
  [⟨13470,witnessRule valid_3018 (by decide)⟩,
   ⟨42540,witnessRule valid_2102 (by decide)⟩,
   ⟨83940,witnessRule valid_848 (by decide)⟩,
   ⟨371076,witnessRule valid_802 (by decide)⟩,
   ⟨373476,witnessRule valid_3357 (by decide)⟩,
   ⟨503347,witnessRule valid_3987 (by decide)⟩,
   ⟨832179,witnessRule valid_2325 (by decide)⟩,
   ⟨841630,witnessRule valid_3670 (by decide)⟩,
   ⟨850306,witnessRule valid_1712 (by decide)⟩,
   ⟨894288,witnessRule valid_3381 (by decide)⟩,
   ⟨965595,witnessRule valid_773 (by decide)⟩,
   ⟨982096,witnessRule valid_2615 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_50 : CheckedBlock 1000000000000000000 50 :=
  excludeBlock columns (a := 1000000000050000000) (width := 1000000) highPoints_50
    (by decide) (by decide) (by decide)

private def highPoints_51 : List (Witness 1000000000051000000) :=
  [⟨73460,witnessRule valid_1046 (by decide)⟩,
   ⟨299330,witnessDivisors _ 1 [1,11243,32051943433112712493,360360000018486226558799] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨534046,witnessRule valid_2045 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_51 : CheckedBlock 1000000000000000000 51 :=
  excludeBlock columns (a := 1000000000051000000) (width := 1000000) highPoints_51
    (by decide) (by decide) (by decide)

private def highPoints_52 : List (Witness 1000000000052000000) :=
  [⟨331851,witnessDivisors _ 1 [1,42071,8565520192504535329,360360000018858305826359] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨377830,witnessRule valid_802 (by decide)⟩,
   ⟨582592,witnessDivisors _ 2 [1,2,73877,147754,2438918743444838467] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨943060,witnessDivisors _ 1 [1,13397,26898559380389532067,360360000019078561101599] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_52 : CheckedBlock 1000000000000000000 52 :=
  excludeBlock columns (a := 1000000000052000000) (width := 1000000) highPoints_52
    (by decide) (by decide) (by decide)

private def highPoints_53 : List (Witness 1000000000053000000) :=
  [⟨50446,witnessRule valid_421 (by decide)⟩,
   ⟨61672,witnessRule valid_766 (by decide)⟩,
   ⟨82531,witnessDivisors _ 5 [1,5,30689,153445,2348463619010908279,11742318095054541395,72072000003825764174231,360360000019128820871155] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨256251,witnessRule valid_3141 (by decide)⟩,
   ⟨280147,witnessRule valid_3381 (by decide)⟩,
   ⟨578171,witnessRule valid_2894 (by decide)⟩,
   ⟨706499,witnessRule valid_706 (by decide)⟩,
   ⟨752626,witnessRule valid_1306 (by decide)⟩,
   ⟨760803,witnessRule valid_2901 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_53 : CheckedBlock 1000000000000000000 53 :=
  excludeBlock columns (a := 1000000000053000000) (width := 1000000) highPoints_53
    (by decide) (by decide) (by decide)

private def highPoints_54 : List (Witness 1000000000054000000) :=
  [⟨491352,witnessRule valid_2658 (by decide)⟩,
   ⟨703826,witnessRule valid_3590 (by decide)⟩,
   ⟨802115,witnessRule valid_1895 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_54 : CheckedBlock 1000000000000000000 54 :=
  excludeBlock columns (a := 1000000000054000000) (width := 1000000) highPoints_54
    (by decide) (by decide) (by decide)

private def highPoints_55 : List (Witness 1000000000055000000) :=
  [⟨219499,witnessRule valid_1201 (by decide)⟩,
   ⟨308726,witnessRule valid_2118 (by decide)⟩,
   ⟨393675,witnessRule valid_1556 (by decide)⟩,
   ⟨517922,witnessRule valid_3702 (by decide)⟩,
   ⟨575892,witnessRule valid_2995 (by decide)⟩,
   ⟨641410,witnessRule valid_1264 (by decide)⟩,
   ⟨690676,witnessRule valid_3594 (by decide)⟩,
   ⟨717112,witnessRule valid_1519 (by decide)⟩,
   ⟨804202,witnessRule valid_758 (by decide)⟩,
   ⟨815898,witnessRule valid_2095 (by decide)⟩,
   ⟨818024,witnessRule valid_2768 (by decide)⟩,
   ⟨944852,witnessRule valid_1765 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_55 : CheckedBlock 1000000000000000000 55 :=
  excludeBlock columns (a := 1000000000055000000) (width := 1000000) highPoints_55
    (by decide) (by decide) (by decide)

private def highPoints_56 : List (Witness 1000000000056000000) :=
  [⟨79580,witnessRule valid_3996 (by decide)⟩,
   ⟨148662,witnessRule valid_2815 (by decide)⟩,
   ⟨198387,witnessRule valid_866 (by decide)⟩,
   ⟨369946,witnessRule valid_1013 (by decide)⟩,
   ⟨399027,witnessRule valid_3857 (by decide)⟩,
   ⟨453336,witnessDivisors _ 1 [1,7853,45888195596631035803,360360000020343524160959] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨568752,witnessRule valid_2276 (by decide)⟩,
   ⟨602562,witnessRule valid_2042 (by decide)⟩,
   ⟨627331,witnessRule valid_2845 (by decide)⟩,
   ⟨704659,witnessRule valid_1723 (by decide)⟩,
   ⟨812184,witnessRule valid_848 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_56 : CheckedBlock 1000000000000000000 56 :=
  excludeBlock columns (a := 1000000000056000000) (width := 1000000) highPoints_56
    (by decide) (by decide) (by decide)

private def highPoints_57 : List (Witness 1000000000057000000) :=
  [⟨80336,witnessRule valid_1724 (by decide)⟩,
   ⟨145355,witnessRule valid_1263 (by decide)⟩,
   ⟨150098,witnessRule valid_3548 (by decide)⟩,
   ⟨223787,witnessRule valid_886 (by decide)⟩,
   ⟨316820,witnessRule valid_1123 (by decide)⟩,
   ⟨430830,witnessDivisors _ 2 [1,2,34519,69038,5219734059803235521] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨657186,witnessRule valid_1438 (by decide)⟩,
   ⟨671763,witnessRule valid_2382 (by decide)⟩,
   ⟨722726,witnessRule valid_944 (by decide)⟩,
   ⟨920414,witnessRule valid_848 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_57 : CheckedBlock 1000000000000000000 57 :=
  excludeBlock columns (a := 1000000000057000000) (width := 1000000) highPoints_57
    (by decide) (by decide) (by decide)

private def highPoints_58 : List (Witness 1000000000058000000) :=
  [⟨9652,witnessRule valid_778 (by decide)⟩,
   ⟨65987,witnessRule valid_818 (by decide)⟩,
   ⟨105835,witnessRule valid_1047 (by decide)⟩,
   ⟨169050,witnessRule valid_359 (by decide)⟩,
   ⟨208300,witnessRule valid_2836 (by decide)⟩,
   ⟨208427,witnessRule valid_1046 (by decide)⟩,
   ⟨229210,witnessRule valid_1796 (by decide)⟩,
   ⟨329371,witnessRule valid_1604 (by decide)⟩,
   ⟨412915,witnessRule valid_349 (by decide)⟩,
   ⟨738915,witnessRule valid_2788 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_58 : CheckedBlock 1000000000000000000 58 :=
  excludeBlock columns (a := 1000000000058000000) (width := 1000000) highPoints_58
    (by decide) (by decide) (by decide)

private def highPoints_59 : List (Witness 1000000000059000000) :=
  [⟨438876,witnessRule valid_2254 (by decide)⟩,
   ⟨561667,witnessRule valid_3722 (by decide)⟩,
   ⟨693400,witnessRule valid_1985 (by decide)⟩,
   ⟨755586,witnessRule valid_1018 (by decide)⟩,
   ⟨860827,witnessDivisors _ 2 [1,2,2683,5366,67156168472152711073] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨954764,witnessRule valid_1168 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_59 : CheckedBlock 1000000000000000000 59 :=
  excludeBlock columns (a := 1000000000059000000) (width := 1000000) highPoints_59
    (by decide) (by decide) (by decide)

private def highPoints_60 : List (Witness 1000000000060000000) :=
  [⟨12638,witnessRule valid_1136 (by decide)⟩,
   ⟨28320,witnessDivisors _ 2 [1,2,7867,15734,22903266812103203597] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨349952,witnessRule valid_3126 (by decide)⟩,
   ⟨440595,witnessRule valid_1492 (by decide)⟩,
   ⟨444528,witnessRule valid_838 (by decide)⟩,
   ⟨534486,witnessRule valid_349 (by decide)⟩,
   ⟨721147,witnessDivisors _ 5 [1,5,2543,12715,28341329140533344281,141706645702666721405,72072000004376294506583,360360000021881472532915] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨741002,witnessRule valid_746 (by decide)⟩,
   ⟨814672,witnessRule valid_1744 (by decide)⟩,
   ⟨829088,witnessRule valid_922 (by decide)⟩,
   ⟨939806,witnessRule valid_1126 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_60 : CheckedBlock 1000000000000000000 60 :=
  excludeBlock columns (a := 1000000000060000000) (width := 1000000) highPoints_60
    (by decide) (by decide) (by decide)

private def highPoints_61 : List (Witness 1000000000061000000) :=
  [⟨2190,witnessRule valid_3381 (by decide)⟩,
   ⟨132003,witnessRule valid_2932 (by decide)⟩,
   ⟨193406,witnessRule valid_1618 (by decide)⟩,
   ⟨488424,witnessRule valid_706 (by decide)⟩,
   ⟨590348,witnessRule valid_694 (by decide)⟩,
   ⟨721670,witnessDivisors _ 1 [1,11497,31343828826845439767,360360000022242021001199] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨773571,witnessRule valid_3772 (by decide)⟩,
   ⟨791206,witnessRule valid_3062 (by decide)⟩,
   ⟨792690,witnessRule valid_1059 (by decide)⟩,
   ⟨814643,witnessRule valid_718 (by decide)⟩,
   ⟨859739,witnessRule valid_2094 (by decide)⟩,
   ⟨986536,witnessRule valid_1127 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_61 : CheckedBlock 1000000000000000000 61 :=
  excludeBlock columns (a := 1000000000061000000) (width := 1000000) highPoints_61
    (by decide) (by decide) (by decide)

private def highPoints_62 : List (Witness 1000000000062000000) :=
  [⟨24276,witnessRule valid_1191 (by decide)⟩,
   ⟨69850,witnessRule valid_1119 (by decide)⟩,
   ⟨185555,witnessRule valid_599 (by decide)⟩,
   ⟨278046,witnessDivisors _ 2 [1,2,4211,6581,8422] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨413896,witnessRule valid_3790 (by decide)⟩,
   ⟨549746,witnessRule valid_2406 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_62 : CheckedBlock 1000000000000000000 62 :=
  excludeBlock columns (a := 1000000000062000000) (width := 1000000) highPoints_62
    (by decide) (by decide) (by decide)

private def highPoints_63 : List (Witness 1000000000063000000) :=
  [⟨161236,witnessRule valid_641 (by decide)⟩,
   ⟨242252,witnessDivisors _ 3 [1,3,16691,50073,7196692828925568229,21590078486776704687] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨412592,witnessRule valid_848 (by decide)⟩,
   ⟨478292,witnessRule valid_2298 (by decide)⟩,
   ⟨715764,witnessRule valid_3202 (by decide)⟩,
   ⟨831619,witnessRule valid_347 (by decide)⟩,
   ⟨863384,witnessDivisors _ 2 [1,2,6047,12094,29796593353978320577] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_63 : CheckedBlock 1000000000000000000 63 :=
  excludeBlock columns (a := 1000000000063000000) (width := 1000000) highPoints_63
    (by decide) (by decide) (by decide)

private def highPoints_64 : List (Witness 1000000000064000000) :=
  [⟨376659,witnessRule valid_2775 (by decide)⟩,
   ⟨493027,witnessRule valid_958 (by decide)⟩,
   ⟨724179,witnessRule valid_982 (by decide)⟩,
   ⟨876048,witnessRule valid_802 (by decide)⟩,
   ⟨894955,witnessRule valid_1114 (by decide)⟩,
   ⟨995312,witnessRule valid_3381 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_64 : CheckedBlock 1000000000000000000 64 :=
  excludeBlock columns (a := 1000000000064000000) (width := 1000000) highPoints_64
    (by decide) (by decide) (by decide)

private def highPoints_65 : List (Witness 1000000000065000000) :=
  [⟨169539,witnessRule valid_3225 (by decide)⟩,
   ⟨312200,witnessDivisors _ 6 [1,2,3,6,18127,36254,54381,108762,3313289568264061937] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨394356,witnessDivisors _ 1 [1,5881,61275293321470074839,360360000023565510128159] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨726315,witnessRule valid_3830 (by decide)⟩,
   ⟨784018,witnessDivisors _ 2 [1,2,28433,36017,56866] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨859204,witnessRule valid_1136 (by decide)⟩,
   ⟨917531,witnessRule valid_467 (by decide)⟩,
   ⟨927130,witnessRule valid_431 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_65 : CheckedBlock 1000000000000000000 65 :=
  excludeBlock columns (a := 1000000000065000000) (width := 1000000) highPoints_65
    (by decide) (by decide) (by decide)

private def highPoints_66 : List (Witness 1000000000066000000) :=
  [⟨55435,witnessRule valid_2238 (by decide)⟩,
   ⟨134388,witnessDivisors _ 4 [1,2,4,17827,35654,71308,5053570427214789197] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨388924,witnessRule valid_2254 (by decide)⟩,
   ⟨530556,witnessRule valid_1412 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_66 : CheckedBlock 1000000000000000000 66 :=
  excludeBlock columns (a := 1000000000066000000) (width := 1000000) highPoints_66
    (by decide) (by decide) (by decide)

private def highPoints_67 : List (Witness 1000000000067000000) :=
  [⟨433772,witnessRule valid_944 (by decide)⟩,
   ⟨579236,witnessRule valid_2215 (by decide)⟩,
   ⟨716227,witnessRule valid_3703 (by decide)⟩,
   ⟨744594,witnessRule valid_1168 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_67 : CheckedBlock 1000000000000000000 67 :=
  excludeBlock columns (a := 1000000000067000000) (width := 1000000) highPoints_67
    (by decide) (by decide) (by decide)

private def highPoints_68 : List (Witness 1000000000068000000) :=
  [⟨545915,witnessRule valid_2598 (by decide)⟩,
   ⟨754899,witnessRule valid_2668 (by decide)⟩,
   ⟨796288,witnessRule valid_1072 (by decide)⟩,
   ⟨859531,witnessRule valid_1894 (by decide)⟩,
   ⟨895347,witnessRule valid_2636 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_68 : CheckedBlock 1000000000000000000 68 :=
  excludeBlock columns (a := 1000000000068000000) (width := 1000000) highPoints_68
    (by decide) (by decide) (by decide)

private def highPoints_69 : List (Witness 1000000000069000000) :=
  [⟨69739,witnessRule valid_2775 (by decide)⟩,
   ⟨85747,witnessRule valid_457 (by decide)⟩,
   ⟨197771,witnessRule valid_1347 (by decide)⟩,
   ⟨226518,witnessRule valid_2285 (by decide)⟩,
   ⟨282092,witnessRule valid_2228 (by decide)⟩,
   ⟨508248,witnessDivisors _ 8 [1,2,4,8,4073,8146,16292,32584,11059415664898354783,22118831329796709566,44237662659593419132] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨527588,witnessRule valid_3805 (by decide)⟩,
   ⟨709250,witnessRule valid_1136 (by decide)⟩,
   ⟨830211,witnessRule valid_778 (by decide)⟩,
   ⟨907227,witnessRule valid_2694 (by decide)⟩,
   ⟨935920,witnessRule valid_3411 (by decide)⟩,
   ⟨948860,witnessRule valid_1487 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_69 : CheckedBlock 1000000000000000000 69 :=
  excludeBlock columns (a := 1000000000069000000) (width := 1000000) highPoints_69
    (by decide) (by decide) (by decide)

private def highPoints_70 : List (Witness 1000000000070000000) :=
  [⟨196822,witnessRule valid_2994 (by decide)⟩,
   ⟨248754,witnessRule valid_2215 (by decide)⟩,
   ⟨337656,witnessRule valid_2612 (by decide)⟩,
   ⟨365371,witnessRule valid_1895 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_70 : CheckedBlock 1000000000000000000 70 :=
  excludeBlock columns (a := 1000000000070000000) (width := 1000000) highPoints_70
    (by decide) (by decide) (by decide)

private def highPoints_71 : List (Witness 1000000000071000000) :=
  [⟨290506,witnessRule valid_1797 (by decide)⟩,
   ⟨325406,witnessRule valid_1203 (by decide)⟩,
   ⟨368578,witnessRule valid_521 (by decide)⟩,
   ⟨557190,witnessDivisors _ 1 [1,18181,19820691932555214179,360360000025786348988399] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨580168,witnessRule valid_3862 (by decide)⟩,
   ⟨776000,witnessRule valid_521 (by decide)⟩,
   ⟨881046,witnessRule valid_3215 (by decide)⟩,
   ⟨911147,witnessRule valid_2539 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_71 : CheckedBlock 1000000000000000000 71 :=
  excludeBlock columns (a := 1000000000071000000) (width := 1000000) highPoints_71
    (by decide) (by decide) (by decide)

private def highPoints_72 : List (Witness 1000000000072000000) :=
  [⟨34128,witnessRule valid_2245 (by decide)⟩,
   ⟨226979,witnessRule valid_2202 (by decide)⟩,
   ⟨282920,witnessRule valid_2334 (by decide)⟩,
   ⟨418067,witnessRule valid_718 (by decide)⟩,
   ⟨528134,witnessRule valid_1264 (by decide)⟩,
   ⟨710147,witnessRule valid_2042 (by decide)⟩,
   ⟨889571,witnessRule valid_1077 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_72 : CheckedBlock 1000000000000000000 72 :=
  excludeBlock columns (a := 1000000000072000000) (width := 1000000) highPoints_72
    (by decide) (by decide) (by decide)

private def highPoints_73 : List (Witness 1000000000073000000) :=
  [⟨730827,witnessDivisors _ 2 [1,2,10651,21302,16916721435854363009] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨758764,witnessDivisors _ 2 [1,2,4019,8038,44832047776384636501] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_73 : CheckedBlock 1000000000000000000 73 :=
  excludeBlock columns (a := 1000000000073000000) (width := 1000000) highPoints_73
    (by decide) (by decide) (by decide)

private def highPoints_74 : List (Witness 1000000000074000000) :=
  [⟨58395,witnessRule valid_1654 (by decide)⟩,
   ⟨66274,witnessRule valid_1648 (by decide)⟩,
   ⟨69402,witnessRule valid_3056 (by decide)⟩,
   ⟨121867,witnessRule valid_2463 (by decide)⟩,
   ⟨437571,witnessRule valid_3357 (by decide)⟩,
   ⟨585162,witnessRule valid_944 (by decide)⟩,
   ⟨685870,witnessRule valid_718 (by decide)⟩,
   ⟨688562,witnessDivisors _ 7 [1,7,23,161,193,1351,4439,31073,11597206578924299881,81180446052470099167] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨864654,witnessRule valid_3378 (by decide)⟩,
   ⟨883464,witnessRule valid_2175 (by decide)⟩,
   ⟨913800,witnessRule valid_1519 (by decide)⟩,
   ⟨948668,witnessDivisors _ 2 [1,2,30637,61274,5881124131393551947] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_74 : CheckedBlock 1000000000000000000 74 :=
  excludeBlock columns (a := 1000000000074000000) (width := 1000000) highPoints_74
    (by decide) (by decide) (by decide)

private def highPoints_75 : List (Witness 1000000000075000000) :=
  [⟨3739,witnessRule valid_3018 (by decide)⟩,
   ⟨148196,witnessRule valid_2766 (by decide)⟩,
   ⟨171124,witnessRule valid_758 (by decide)⟩,
   ⟨174920,witnessRule valid_1059 (by decide)⟩,
   ⟨573587,witnessDivisors _ 3 [1,3,1549,4647,77546804395789476611,232640413187368429833] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨688380,witnessRule valid_914 (by decide)⟩,
   ⟨711072,witnessRule valid_3303 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_75 : CheckedBlock 1000000000000000000 75 :=
  excludeBlock columns (a := 1000000000075000000) (width := 1000000) highPoints_75
    (by decide) (by decide) (by decide)

private def highPoints_76 : List (Witness 1000000000076000000) :=
  [⟨15027,witnessRule valid_1658 (by decide)⟩,
   ⟨87684,witnessRule valid_2514 (by decide)⟩,
   ⟨174640,witnessRule valid_3786 (by decide)⟩,
   ⟨277747,witnessRule valid_2094 (by decide)⟩,
   ⟨344203,witnessRule valid_607 (by decide)⟩,
   ⟨597934,witnessRule valid_2254 (by decide)⟩,
   ⟨659488,witnessRule valid_1839 (by decide)⟩,
   ⟨840331,witnessRule valid_3303 (by decide)⟩,
   ⟨852820,witnessRule valid_734 (by decide)⟩,
   ⟨983644,witnessRule valid_2175 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_76 : CheckedBlock 1000000000000000000 76 :=
  excludeBlock columns (a := 1000000000076000000) (width := 1000000) highPoints_76
    (by decide) (by decide) (by decide)

private def highPoints_77 : List (Witness 1000000000077000000) :=
  [⟨72222,witnessRule valid_1299 (by decide)⟩,
   ⟨91795,witnessDivisors _ 1 [1,7193,50098707080186403343,360360000027780799246199] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨119992,witnessRule valid_1735 (by decide)⟩,
   ⟨124387,witnessRule valid_3018 (by decide)⟩,
   ⟨188752,witnessRule valid_1006 (by decide)⟩,
   ⟨430718,witnessRule valid_976 (by decide)⟩,
   ⟨565795,witnessRule valid_878 (by decide)⟩,
   ⟨610210,witnessRule valid_944 (by decide)⟩,
   ⟨632656,witnessDivisors _ 4 [1,2,4,20627,41254,82508,4367576477771557957] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨761646,witnessRule valid_2454 (by decide)⟩,
   ⟨931538,witnessRule valid_2094 (by decide)⟩,
   ⟨950196,witnessRule valid_1226 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_77 : CheckedBlock 1000000000000000000 77 :=
  excludeBlock columns (a := 1000000000077000000) (width := 1000000) highPoints_77
    (by decide) (by decide) (by decide)

private def highPoints_78 : List (Witness 1000000000078000000) :=
  [⟨451,witnessRule valid_569 (by decide)⟩,
   ⟨102678,witnessRule valid_1137 (by decide)⟩,
   ⟨473856,witnessRule valid_2578 (by decide)⟩,
   ⟨751636,witnessRule valid_1174 (by decide)⟩,
   ⟨878124,witnessRule valid_659 (by decide)⟩,
   ⟨896243,witnessDivisors _ 1 [1,7103,44893,318874979] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨955278,witnessRule valid_2545 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_78 : CheckedBlock 1000000000000000000 78 :=
  excludeBlock columns (a := 1000000000078000000) (width := 1000000) highPoints_78
    (by decide) (by decide) (by decide)

private def highPoints_79 : List (Witness 1000000000079000000) :=
  [⟨127123,witnessRule valid_2391 (by decide)⟩,
   ⟨137000,witnessRule valid_3319 (by decide)⟩,
   ⟨182784,witnessRule valid_2526 (by decide)⟩,
   ⟨273955,witnessRule valid_2949 (by decide)⟩,
   ⟨449163,witnessRule valid_866 (by decide)⟩,
   ⟨629651,witnessRule valid_2238 (by decide)⟩,
   ⟨662920,witnessRule valid_2815 (by decide)⟩,
   ⟨682142,witnessRule valid_866 (by decide)⟩,
   ⟨755140,witnessRule valid_379 (by decide)⟩,
   ⟨759795,witnessRule valid_1018 (by decide)⟩,
   ⟨881736,witnessRule valid_2297 (by decide)⟩,
   ⟨908596,witnessRule valid_1329 (by decide)⟩,
   ⟨945520,witnessRule valid_2694 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_79 : CheckedBlock 1000000000000000000 79 :=
  excludeBlock columns (a := 1000000000079000000) (width := 1000000) highPoints_79
    (by decide) (by decide) (by decide)

private def highPoints_80 : List (Witness 1000000000080000000) :=
  [⟨14211,witnessRule valid_2283 (by decide)⟩,
   ⟨122634,witnessDivisors _ 5 [1,5,5281,26405,13647415263354402287,68237076316772011435,72072000005774598477647,360360000028872992388235] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨198030,witnessRule valid_3292 (by decide)⟩,
   ⟨437730,witnessRule valid_367 (by decide)⟩,
   ⟨442379,witnessRule valid_2812 (by decide)⟩,
   ⟨564555,witnessRule valid_2426 (by decide)⟩,
   ⟨682130,witnessRule valid_1895 (by decide)⟩,
   ⟨693296,witnessRule valid_1865 (by decide)⟩,
   ⟨731643,witnessRule valid_734 (by decide)⟩,
   ⟨747288,witnessRule valid_976 (by decide)⟩,
   ⟨784147,witnessRule valid_2298 (by decide)⟩,
   ⟨934818,witnessRule valid_1168 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_80 : CheckedBlock 1000000000000000000 80 :=
  excludeBlock columns (a := 1000000000080000000) (width := 1000000) highPoints_80
    (by decide) (by decide) (by decide)

private def highPoints_81 : List (Witness 1000000000081000000) :=
  [⟨293798,witnessRule valid_1072 (by decide)⟩,
   ⟨305659,witnessRule valid_2175 (by decide)⟩,
   ⟨792686,witnessRule valid_347 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_81 : CheckedBlock 1000000000000000000 81 :=
  excludeBlock columns (a := 1000000000081000000) (width := 1000000) highPoints_81
    (by decide) (by decide) (by decide)

private def highPoints_82 : List (Witness 1000000000082000000) :=
  [⟨327331,witnessDivisors _ 3 [1,3,12323,36969,82757,248271] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨459522,witnessRule valid_1468 (by decide)⟩,
   ⟨490310,witnessRule valid_743 (by decide)⟩,
   ⟨913060,witnessDivisors _ 3 [1,3,1459,4377,82330363269334829861,246991089808004489583] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_82 : CheckedBlock 1000000000000000000 82 :=
  excludeBlock columns (a := 1000000000082000000) (width := 1000000) highPoints_82
    (by decide) (by decide) (by decide)

private def highPoints_83 : List (Witness 1000000000083000000) :=
  [⟨589870,witnessDivisors _ 5 [1,5,94777,473885,760437658989253607,3802188294946268035,72072000006024489110639,360360000030122445553195] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨715670,witnessRule valid_976 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_83 : CheckedBlock 1000000000000000000 83 :=
  excludeBlock columns (a := 1000000000083000000) (width := 1000000) highPoints_83
    (by decide) (by decide) (by decide)

private def highPoints_84 : List (Witness 1000000000084000000) :=
  [⟨88355,witnessRule valid_2105 (by decide)⟩,
   ⟨196472,witnessRule valid_976 (by decide)⟩,
   ⟨314342,witnessRule valid_2254 (by decide)⟩,
   ⟨350755,witnessRule valid_3141 (by decide)⟩,
   ⟨386880,witnessRule valid_2082 (by decide)⟩,
   ⟨442122,witnessRule valid_2351 (by decide)⟩,
   ⟨561170,witnessRule valid_706 (by decide)⟩,
   ⟨637290,witnessRule valid_848 (by decide)⟩,
   ⟨640419,witnessRule valid_1227 (by decide)⟩,
   ⟨643212,witnessRule valid_1006 (by decide)⟩,
   ⟨776912,witnessRule valid_3057 (by decide)⟩,
   ⟨927928,witnessDivisors _ 5 [1,5,25,12583,62915,314575,1145545577463576661,5727727887317883305] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨933000,witnessRule valid_2245 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_84 : CheckedBlock 1000000000000000000 84 :=
  excludeBlock columns (a := 1000000000084000000) (width := 1000000) highPoints_84
    (by decide) (by decide) (by decide)

private def highPoints_85 : List (Witness 1000000000085000000) :=
  [⟨42171,witnessDivisors _ 2 [1,2,33749,67498,5338824854523775471] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨132795,witnessRule valid_2812 (by decide)⟩,
   ⟨425835,witnessRule valid_1658 (by decide)⟩,
   ⟨529162,witnessDivisors _ 1 [1,13751,26206094104488494569,360360000030821288818319] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨558220,witnessRule valid_2683 (by decide)⟩,
   ⟨596354,witnessRule valid_2175 (by decide)⟩,
   ⟨794390,witnessRule valid_1945 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_85 : CheckedBlock 1000000000000000000 85 :=
  excludeBlock columns (a := 1000000000085000000) (width := 1000000) highPoints_85
    (by decide) (by decide) (by decide)

private def highPoints_86 : List (Witness 1000000000086000000) :=
  [⟨33942,witnessRule valid_2672 (by decide)⟩,
   ⟨187067,witnessRule valid_1142 (by decide)⟩,
   ⟨283460,witnessRule valid_3126 (by decide)⟩,
   ⟨290475,witnessRule valid_2005 (by decide)⟩,
   ⟨433842,witnessRule valid_2512 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_86 : CheckedBlock 1000000000000000000 86 :=
  excludeBlock columns (a := 1000000000086000000) (width := 1000000) highPoints_86
    (by decide) (by decide) (by decide)

private def highPoints_87 : List (Witness 1000000000087000000) :=
  [⟨118140,witnessRule valid_3056 (by decide)⟩,
   ⟨316490,witnessDivisors _ 2 [1,2,47147,94294,3821664157119916117] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨374404,witnessRule valid_2495 (by decide)⟩,
   ⟨419434,witnessRule valid_2215 (by decide)⟩,
   ⟨692310,witnessRule valid_1047 (by decide)⟩,
   ⟨807490,witnessRule valid_1436 (by decide)⟩,
   ⟨963596,witnessRule valid_1289 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_87 : CheckedBlock 1000000000000000000 87 :=
  excludeBlock columns (a := 1000000000087000000) (width := 1000000) highPoints_87
    (by decide) (by decide) (by decide)

private def highPoints_88 : List (Witness 1000000000088000000) :=
  [⟨128246,witnessRule valid_557 (by decide)⟩,
   ⟨314427,witnessRule valid_1942 (by decide)⟩,
   ⟨329019,witnessRule valid_2186 (by decide)⟩,
   ⟨338576,witnessDivisors _ 1 [1,9431,38210157992984168089,360360000031833689247359] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨533138,witnessRule valid_3126 (by decide)⟩,
   ⟨595650,witnessRule valid_1895 (by decide)⟩,
   ⟨844587,witnessRule valid_2298 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_88 : CheckedBlock 1000000000000000000 88 :=
  excludeBlock columns (a := 1000000000088000000) (width := 1000000) highPoints_88
    (by decide) (by decide) (by decide)

private def highPoints_89 : List (Witness 1000000000089000000) :=
  [⟨100590,witnessRule valid_2118 (by decide)⟩,
   ⟨146002,witnessRule valid_379 (by decide)⟩,
   ⟨555300,witnessRule valid_1137 (by decide)⟩,
   ⟨570118,witnessDivisors _ 3 [1,3,1543,4629,77848347382215918713,233545042146647756139] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨895838,witnessRule valid_1735 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_89 : CheckedBlock 1000000000000000000 89 :=
  excludeBlock columns (a := 1000000000089000000) (width := 1000000) highPoints_89
    (by decide) (by decide) (by decide)

private def highPoints_90 : List (Witness 1000000000090000000) :=
  [⟨48510,witnessRule valid_347 (by decide)⟩,
   ⟨65980,witnessRule valid_2694 (by decide)⟩,
   ⟨103768,witnessRule valid_1328 (by decide)⟩,
   ⟨164030,witnessRule valid_818 (by decide)⟩,
   ⟨209984,witnessRule valid_2526 (by decide)⟩,
   ⟨308227,witnessRule valid_641 (by decide)⟩,
   ⟨314979,witnessRule valid_1852 (by decide)⟩,
   ⟨641475,witnessRule valid_3530 (by decide)⟩,
   ⟨719012,witnessRule valid_746 (by decide)⟩,
   ⟨766550,witnessRule valid_3857 (by decide)⟩,
   ⟨903731,witnessRule valid_2866 (by decide)⟩,
   ⟨988924,witnessRule valid_349 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_90 : CheckedBlock 1000000000000000000 90 :=
  excludeBlock columns (a := 1000000000090000000) (width := 1000000) highPoints_90
    (by decide) (by decide) (by decide)

private def highPoints_91 : List (Witness 1000000000091000000) :=
  [⟨82642,witnessRule valid_547 (by decide)⟩,
   ⟨283452,witnessRule valid_3996 (by decide)⟩,
   ⟨517786,witnessRule valid_1454 (by decide)⟩,
   ⟨577642,witnessRule valid_3966 (by decide)⟩,
   ⟨586856,witnessRule valid_3728 (by decide)⟩,
   ⟨603346,witnessRule valid_2705 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_91 : CheckedBlock 1000000000000000000 91 :=
  excludeBlock columns (a := 1000000000091000000) (width := 1000000) highPoints_91
    (by decide) (by decide) (by decide)

private def highPoints_92 : List (Witness 1000000000092000000) :=
  [⟨14554,witnessRule valid_3790 (by decide)⟩,
   ⟨530280,witnessRule valid_2699 (by decide)⟩,
   ⟨679506,witnessRule valid_3305 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_92 : CheckedBlock 1000000000000000000 92 :=
  excludeBlock columns (a := 1000000000092000000) (width := 1000000) highPoints_92
    (by decide) (by decide) (by decide)

private def highPoints_93 : List (Witness 1000000000093000000) :=
  [⟨132995,witnessRule valid_694 (by decide)⟩,
   ⟨147763,witnessDivisors _ 2 [1,2,3557,7114,50655046392123520927] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨253610,witnessRule valid_1906 (by decide)⟩,
   ⟨277115,witnessRule valid_886 (by decide)⟩,
   ⟨430206,witnessRule valid_1941 (by decide)⟩,
   ⟨448056,witnessDivisors _ 1 [1,4603,78288073003188125453,360360000033674941460159] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨753915,witnessRule valid_1154 (by decide)⟩,
   ⟨804804,witnessRule valid_2175 (by decide)⟩,
   ⟨875147,witnessDivisors _ 1 [1,9601,37533590254538990519,360360000033828847972919] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_93 : CheckedBlock 1000000000000000000 93 :=
  excludeBlock columns (a := 1000000000093000000) (width := 1000000) highPoints_93
    (by decide) (by decide) (by decide)

private def highPoints_94 : List (Witness 1000000000094000000) :=
  [⟨316011,witnessRule valid_3730 (by decide)⟩,
   ⟨320774,witnessRule valid_347 (by decide)⟩,
   ⟨375826,witnessRule valid_1424 (by decide)⟩,
   ⟨820027,witnessRule valid_2179 (by decide)⟩,
   ⟨867075,witnessRule valid_766 (by decide)⟩,
   ⟨910603,witnessRule valid_1466 (by decide)⟩,
   ⟨932244,witnessRule valid_3996 (by decide)⟩,
   ⟨942118,witnessRule valid_746 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_94 : CheckedBlock 1000000000000000000 94 :=
  excludeBlock columns (a := 1000000000094000000) (width := 1000000) highPoints_94
    (by decide) (by decide) (by decide)

private def highPoints_95 : List (Witness 1000000000095000000) :=
  [⟨274352,witnessRule valid_2082 (by decide)⟩,
   ⟨883003,witnessRule valid_2634 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_95 : CheckedBlock 1000000000000000000 95 :=
  excludeBlock columns (a := 1000000000095000000) (width := 1000000) highPoints_95
    (by decide) (by decide) (by decide)

private def highPoints_96 : List (Witness 1000000000096000000) :=
  [⟨9355,witnessRule valid_1844 (by decide)⟩,
   ⟨106964,witnessRule valid_3225 (by decide)⟩,
   ⟨279820,witnessRule valid_3790 (by decide)⟩,
   ⟨462672,witnessRule valid_3261 (by decide)⟩,
   ⟨573104,witnessRule valid_3490 (by decide)⟩,
   ⟨868867,witnessRule valid_1954 (by decide)⟩,
   ⟨996835,witnessRule valid_3282 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_96 : CheckedBlock 1000000000000000000 96 :=
  excludeBlock columns (a := 1000000000096000000) (width := 1000000) highPoints_96
    (by decide) (by decide) (by decide)

private def highPoints_97 : List (Witness 1000000000097000000) :=
  [⟨74643,witnessRule valid_2406 (by decide)⟩,
   ⟨542971,witnessDivisors _ 1 [1,48383,7448070604037587273,360360000035150585029559] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨682586,witnessDivisors _ 1 [1,16747,21517883802185519597,360360000035200896690959] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨709627,witnessRule valid_1119 (by decide)⟩,
   ⟨770768,witnessDivisors _ 4 [1,2,4,9929,19858,39716,9073421292054403111] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨973955,witnessRule valid_1723 (by decide)⟩,
   ⟨978568,witnessRule valid_976 (by decide)⟩,
   ⟨982846,witnessRule valid_2303 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_97 : CheckedBlock 1000000000000000000 97 :=
  excludeBlock columns (a := 1000000000097000000) (width := 1000000) highPoints_97
    (by decide) (by decide) (by decide)

private def highPoints_98 : List (Witness 1000000000098000000) :=
  [⟨85747,witnessRule valid_1588 (by decide)⟩,
   ⟨90184,witnessRule valid_2384 (by decide)⟩,
   ⟨378328,witnessRule valid_944 (by decide)⟩,
   ⟨603272,witnessRule valid_2315 (by decide)⟩,
   ⟨673420,witnessRule valid_397 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_98 : CheckedBlock 1000000000000000000 98 :=
  excludeBlock columns (a := 1000000000098000000) (width := 1000000) highPoints_98
    (by decide) (by decide) (by decide)

private def highPoints_99 : List (Witness 1000000000099000000) :=
  [⟨219227,witnessRule valid_911 (by decide)⟩,
   ⟨384926,witnessRule valid_2922 (by decide)⟩,
   ⟨600538,witnessRule valid_1046 (by decide)⟩,
   ⟨769738,witnessRule valid_1227 (by decide)⟩,
   ⟨977156,witnessRule valid_2766 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem highBlock_99 : CheckedBlock 1000000000000000000 99 :=
  excludeBlock columns (a := 1000000000099000000) (width := 1000000) highPoints_99
    (by decide) (by decide) (by decide)

private theorem highTable : ∀ x : ℕ, 0 ≤ x → x < 100 → CheckedBlock 1000000000000000000 x :=
  joinChecked
    (joinChecked
      (joinChecked
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 0 highBlock_0)
              (joinChecked
                (singleChecked 1 highBlock_1)
                (singleChecked 2 highBlock_2)))
            (joinChecked
              (singleChecked 3 highBlock_3)
              (joinChecked
                (singleChecked 4 highBlock_4)
                (singleChecked 5 highBlock_5))))
          (joinChecked
            (joinChecked
              (singleChecked 6 highBlock_6)
              (joinChecked
                (singleChecked 7 highBlock_7)
                (singleChecked 8 highBlock_8)))
            (joinChecked
              (singleChecked 9 highBlock_9)
              (joinChecked
                (singleChecked 10 highBlock_10)
                (singleChecked 11 highBlock_11)))))
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 12 highBlock_12)
              (joinChecked
                (singleChecked 13 highBlock_13)
                (singleChecked 14 highBlock_14)))
            (joinChecked
              (singleChecked 15 highBlock_15)
              (joinChecked
                (singleChecked 16 highBlock_16)
                (singleChecked 17 highBlock_17))))
          (joinChecked
            (joinChecked
              (singleChecked 18 highBlock_18)
              (joinChecked
                (singleChecked 19 highBlock_19)
                (singleChecked 20 highBlock_20)))
            (joinChecked
              (joinChecked
                (singleChecked 21 highBlock_21)
                (singleChecked 22 highBlock_22))
              (joinChecked
                (singleChecked 23 highBlock_23)
                (singleChecked 24 highBlock_24))))))
      (joinChecked
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 25 highBlock_25)
              (joinChecked
                (singleChecked 26 highBlock_26)
                (singleChecked 27 highBlock_27)))
            (joinChecked
              (singleChecked 28 highBlock_28)
              (joinChecked
                (singleChecked 29 highBlock_29)
                (singleChecked 30 highBlock_30))))
          (joinChecked
            (joinChecked
              (singleChecked 31 highBlock_31)
              (joinChecked
                (singleChecked 32 highBlock_32)
                (singleChecked 33 highBlock_33)))
            (joinChecked
              (singleChecked 34 highBlock_34)
              (joinChecked
                (singleChecked 35 highBlock_35)
                (singleChecked 36 highBlock_36)))))
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 37 highBlock_37)
              (joinChecked
                (singleChecked 38 highBlock_38)
                (singleChecked 39 highBlock_39)))
            (joinChecked
              (singleChecked 40 highBlock_40)
              (joinChecked
                (singleChecked 41 highBlock_41)
                (singleChecked 42 highBlock_42))))
          (joinChecked
            (joinChecked
              (singleChecked 43 highBlock_43)
              (joinChecked
                (singleChecked 44 highBlock_44)
                (singleChecked 45 highBlock_45)))
            (joinChecked
              (joinChecked
                (singleChecked 46 highBlock_46)
                (singleChecked 47 highBlock_47))
              (joinChecked
                (singleChecked 48 highBlock_48)
                (singleChecked 49 highBlock_49)))))))
    (joinChecked
      (joinChecked
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 50 highBlock_50)
              (joinChecked
                (singleChecked 51 highBlock_51)
                (singleChecked 52 highBlock_52)))
            (joinChecked
              (singleChecked 53 highBlock_53)
              (joinChecked
                (singleChecked 54 highBlock_54)
                (singleChecked 55 highBlock_55))))
          (joinChecked
            (joinChecked
              (singleChecked 56 highBlock_56)
              (joinChecked
                (singleChecked 57 highBlock_57)
                (singleChecked 58 highBlock_58)))
            (joinChecked
              (singleChecked 59 highBlock_59)
              (joinChecked
                (singleChecked 60 highBlock_60)
                (singleChecked 61 highBlock_61)))))
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 62 highBlock_62)
              (joinChecked
                (singleChecked 63 highBlock_63)
                (singleChecked 64 highBlock_64)))
            (joinChecked
              (singleChecked 65 highBlock_65)
              (joinChecked
                (singleChecked 66 highBlock_66)
                (singleChecked 67 highBlock_67))))
          (joinChecked
            (joinChecked
              (singleChecked 68 highBlock_68)
              (joinChecked
                (singleChecked 69 highBlock_69)
                (singleChecked 70 highBlock_70)))
            (joinChecked
              (joinChecked
                (singleChecked 71 highBlock_71)
                (singleChecked 72 highBlock_72))
              (joinChecked
                (singleChecked 73 highBlock_73)
                (singleChecked 74 highBlock_74))))))
      (joinChecked
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 75 highBlock_75)
              (joinChecked
                (singleChecked 76 highBlock_76)
                (singleChecked 77 highBlock_77)))
            (joinChecked
              (singleChecked 78 highBlock_78)
              (joinChecked
                (singleChecked 79 highBlock_79)
                (singleChecked 80 highBlock_80))))
          (joinChecked
            (joinChecked
              (singleChecked 81 highBlock_81)
              (joinChecked
                (singleChecked 82 highBlock_82)
                (singleChecked 83 highBlock_83)))
            (joinChecked
              (singleChecked 84 highBlock_84)
              (joinChecked
                (singleChecked 85 highBlock_85)
                (singleChecked 86 highBlock_86)))))
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 87 highBlock_87)
              (joinChecked
                (singleChecked 88 highBlock_88)
                (singleChecked 89 highBlock_89)))
            (joinChecked
              (singleChecked 90 highBlock_90)
              (joinChecked
                (singleChecked 91 highBlock_91)
                (singleChecked 92 highBlock_92))))
          (joinChecked
            (joinChecked
              (singleChecked 93 highBlock_93)
              (joinChecked
                (singleChecked 94 highBlock_94)
                (singleChecked 95 highBlock_95)))
            (joinChecked
              (joinChecked
                (singleChecked 96 highBlock_96)
                (singleChecked 97 highBlock_97))
              (joinChecked
                (singleChecked 98 highBlock_98)
                (singleChecked 99 highBlock_99)))))))

private def prefixPoints_0 : List (Witness 64) :=
  [⟨296867,witnessDivisors _ 1 [1,22643,4725613,107002055159] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨310563,witnessRule valid_2791 (by decide)⟩,
   ⟨355242,witnessRule valid_2154 (by decide)⟩,
   ⟨552006,witnessRule valid_3426 (by decide)⟩,
   ⟨575262,witnessRule valid_2238 (by decide)⟩,
   ⟨673275,witnessRule valid_2175 (by decide)⟩,
   ⟨755122,witnessRule valid_848 (by decide)⟩,
   ⟨881171,witnessRule valid_443 (by decide)⟩,
   ⟨925286,witnessRule valid_2428 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_0 : CheckedBlock 64 0 :=
  excludeBlock columns (a := 64) (width := 1000000) prefixPoints_0
    (by decide) (by decide) (by decide)

private def prefixPoints_1 : List (Witness 1000064) :=
  [⟨339531,witnessRule valid_706 (by decide)⟩,
   ⟨452187,witnessRule valid_2215 (by decide)⟩,
   ⟨518283,witnessRule valid_3890 (by decide)⟩,
   ⟨572470,witnessRule valid_3075 (by decide)⟩,
   ⟨658995,witnessRule valid_3225 (by decide)⟩,
   ⟨715024,witnessRule valid_1835 (by decide)⟩,
   ⟨743762,witnessRule valid_3764 (by decide)⟩,
   ⟨779564,witnessRule valid_2215 (by decide)⟩,
   ⟨960286,witnessRule valid_3295 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_1 : CheckedBlock 64 1 :=
  excludeBlock columns (a := 1000064) (width := 1000000) prefixPoints_1
    (by decide) (by decide) (by decide)

private def prefixPoints_2 : List (Witness 2000064) :=
  [⟨290278,witnessRule valid_1726 (by decide)⟩,
   ⟨414880,witnessRule valid_758 (by decide)⟩,
   ⟨483824,witnessRule valid_523 (by decide)⟩,
   ⟨623342,witnessRule valid_1006 (by decide)⟩,
   ⟨714446,witnessRule valid_1059 (by decide)⟩,
   ⟨746898,witnessRule valid_577 (by decide)⟩,
   ⟨758742,witnessRule valid_1371 (by decide)⟩,
   ⟨798692,witnessRule valid_1072 (by decide)⟩,
   ⟨882051,witnessDivisors _ 2 [1,2,7759,8171,8191] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨918763,witnessRule valid_2845 (by decide)⟩,
   ⟨938675,witnessRule valid_2356 (by decide)⟩,
   ⟨989420,witnessRule valid_3830 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_2 : CheckedBlock 64 2 :=
  excludeBlock columns (a := 2000064) (width := 1000000) prefixPoints_2
    (by decide) (by decide) (by decide)

private def prefixPoints_3 : List (Witness 3000064) :=
  [⟨36630,witnessRule valid_2175 (by decide)⟩,
   ⟨227528,witnessRule valid_698 (by decide)⟩,
   ⟨324916,witnessRule valid_2254 (by decide)⟩,
   ⟨483242,witnessRule valid_1299 (by decide)⟩,
   ⟨565358,witnessRule valid_1732 (by decide)⟩,
   ⟨587098,witnessRule valid_2594 (by decide)⟩,
   ⟨644059,witnessRule valid_2526 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_3 : CheckedBlock 64 3 :=
  excludeBlock columns (a := 3000064) (width := 1000000) prefixPoints_3
    (by decide) (by decide) (by decide)

private def prefixPoints_4 : List (Witness 4000064) :=
  [⟨70603,witnessRule valid_1735 (by decide)⟩,
   ⟨116387,witnessRule valid_2924 (by decide)⟩,
   ⟨280446,witnessRule valid_2062 (by decide)⟩,
   ⟨476915,witnessRule valid_2118 (by decide)⟩,
   ⟨570556,witnessRule valid_1676 (by decide)⟩,
   ⟨645436,witnessRule valid_1648 (by decide)⟩,
   ⟨690466,witnessRule valid_1226 (by decide)⟩,
   ⟨707032,witnessRule valid_2612 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_4 : CheckedBlock 64 4 :=
  excludeBlock columns (a := 4000064) (width := 1000000) prefixPoints_4
    (by decide) (by decide) (by decide)

private def prefixPoints_5 : List (Witness 5000064) :=
  [⟨143346,witnessRule valid_2778 (by decide)⟩,
   ⟨178686,witnessRule valid_3730 (by decide)⟩,
   ⟨435848,witnessRule valid_1328 (by decide)⟩,
   ⟨479515,witnessRule valid_706 (by decide)⟩,
   ⟨567363,witnessRule valid_1636 (by decide)⟩,
   ⟨595147,witnessRule valid_1013 (by decide)⟩,
   ⟨597563,witnessRule valid_2605 (by decide)⟩,
   ⟨826624,witnessRule valid_1616 (by decide)⟩,
   ⟨967931,witnessRule valid_1149 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_5 : CheckedBlock 64 5 :=
  excludeBlock columns (a := 5000064) (width := 1000000) prefixPoints_5
    (by decide) (by decide) (by decide)

private def prefixPoints_6 : List (Witness 6000064) :=
  [⟨201859,witnessRule valid_1137 (by decide)⟩,
   ⟨213164,witnessRule valid_2042 (by decide)⟩,
   ⟨388876,witnessRule valid_866 (by decide)⟩,
   ⟨429099,witnessRule valid_3772 (by decide)⟩,
   ⟨519782,witnessRule valid_761 (by decide)⟩,
   ⟨535875,witnessRule valid_1636 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_6 : CheckedBlock 64 6 :=
  excludeBlock columns (a := 6000064) (width := 1000000) prefixPoints_6
    (by decide) (by decide) (by decide)

private def prefixPoints_7 : List (Witness 7000064) :=
  [⟨175500,witnessRule valid_3771 (by decide)⟩,
   ⟨749098,witnessDivisors _ 1 [1,4261,14851,44129] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨904676,witnessRule valid_944 (by decide)⟩,
   ⟨949250,witnessRule valid_1072 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_7 : CheckedBlock 64 7 :=
  excludeBlock columns (a := 7000064) (width := 1000000) prefixPoints_7
    (by decide) (by decide) (by decide)

private def prefixPoints_8 : List (Witness 8000064) :=
  [⟨64923,witnessRule valid_401 (by decide)⟩,
   ⟨141270,witnessRule valid_3470 (by decide)⟩,
   ⟨173128,witnessDivisors _ 2 [1,2,49559,99118,29715001] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨463942,witnessRule valid_359 (by decide)⟩,
   ⟨674555,witnessDivisors _ 3 [1,3,5527,16581,188528177,565584531] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_8 : CheckedBlock 64 8 :=
  excludeBlock columns (a := 8000064) (width := 1000000) prefixPoints_8
    (by decide) (by decide) (by decide)

private def prefixPoints_9 : List (Witness 9000064) :=
  [⟨88136,witnessRule valid_2094 (by decide)⟩,
   ⟨142715,witnessRule valid_3225 (by decide)⟩,
   ⟨281132,witnessRule valid_2382 (by decide)⟩,
   ⟨304830,witnessRule valid_1264 (by decide)⟩,
   ⟨318251,witnessRule valid_2818 (by decide)⟩,
   ⟨380996,witnessRule valid_2452 (by decide)⟩,
   ⟨564187,witnessRule valid_1329 (by decide)⟩,
   ⟨869558,witnessRule valid_1154 (by decide)⟩,
   ⟨957924,witnessRule valid_976 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_9 : CheckedBlock 64 9 :=
  excludeBlock columns (a := 9000064) (width := 1000000) prefixPoints_9
    (by decide) (by decide) (by decide)

private def prefixPoints_10 : List (Witness 10000064) :=
  [⟨19430,witnessDivisors _ 1 [1,7673,470562343,3610624857839] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨37116,witnessRule valid_1835 (by decide)⟩,
   ⟨324592,witnessRule valid_3123 (by decide)⟩,
   ⟨357136,witnessRule valid_2802 (by decide)⟩,
   ⟨375835,witnessDivisors _ 1 [1,8089,13487,34273] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨717190,witnessRule valid_1689 (by decide)⟩,
   ⟨736683,witnessRule valid_3996 (by decide)⟩,
   ⟨748331,witnessRule valid_1174 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_10 : CheckedBlock 64 10 :=
  excludeBlock columns (a := 10000064) (width := 1000000) prefixPoints_10
    (by decide) (by decide) (by decide)

private def prefixPoints_11 : List (Witness 11000064) :=
  [⟨221563,witnessDivisors _ 1 [1,11597,348695827,4043825505719] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨398878,witnessRule valid_1154 (by decide)⟩,
   ⟨899987,witnessRule valid_1985 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_11 : CheckedBlock 64 11 :=
  excludeBlock columns (a := 11000064) (width := 1000000) prefixPoints_11
    (by decide) (by decide) (by decide)

private def prefixPoints_12 : List (Witness 12000064) :=
  [⟨40628,witnessRule valid_3664 (by decide)⟩,
   ⟨193572,witnessRule valid_1636 (by decide)⟩,
   ⟨675630,witnessRule valid_3303 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_12 : CheckedBlock 64 12 :=
  excludeBlock columns (a := 12000064) (width := 1000000) prefixPoints_12
    (by decide) (by decide) (by decide)

private def prefixPoints_13 : List (Witness 13000064) :=
  [⟨225132,witnessRule valid_1724 (by decide)⟩,
   ⟨423346,witnessRule valid_3954 (by decide)⟩,
   ⟨427786,witnessRule valid_1803 (by decide)⟩,
   ⟨442448,witnessRule valid_3254 (by decide)⟩,
   ⟨904174,witnessDivisors _ 2 [1,2,5639,11278,444274801] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨931040,witnessRule valid_734 (by decide)⟩,
   ⟨964536,witnessRule valid_706 (by decide)⟩,
   ⟨969891,witnessRule valid_353 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_13 : CheckedBlock 64 13 :=
  excludeBlock columns (a := 13000064) (width := 1000000) prefixPoints_13
    (by decide) (by decide) (by decide)

private def prefixPoints_14 : List (Witness 14000064) :=
  [⟨86275,witnessRule valid_2108 (by decide)⟩,
   ⟨326211,witnessRule valid_3381 (by decide)⟩,
   ⟨379284,witnessRule valid_3376 (by decide)⟩,
   ⟨449987,witnessDivisors _ 1 [1,8609,604857751,5207220378359] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨459122,witnessRule valid_3394 (by decide)⟩,
   ⟨472462,witnessRule valid_3303 (by decide)⟩,
   ⟨596315,witnessRule valid_2454 (by decide)⟩,
   ⟨684171,witnessRule valid_1047 (by decide)⟩,
   ⟨759648,witnessDivisors _ 1 [1,52951,100447769,5318809816319] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨878626,witnessRule valid_2082 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_14 : CheckedBlock 64 14 :=
  excludeBlock columns (a := 14000064) (width := 1000000) prefixPoints_14
    (by decide) (by decide) (by decide)

private def prefixPoints_15 : List (Witness 15000064) :=
  [⟨101376,witnessRule valid_1264 (by decide)⟩,
   ⟨129636,witnessRule valid_3426 (by decide)⟩,
   ⟨241014,witnessRule valid_1468 (by decide)⟩,
   ⟨245650,witnessRule valid_3126 (by decide)⟩,
   ⟨246828,witnessDivisors _ 6 [1,2,3,6,63389,126778,190167,380334,14446171] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨319328,witnessRule valid_463 (by decide)⟩,
   ⟨331276,witnessRule valid_3501 (by decide)⟩,
   ⟨631156,witnessRule valid_439 (by decide)⟩,
   ⟨750096,witnessDivisors _ 2 [1,2,99877,199754,28413587] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨772811,witnessRule valid_3830 (by decide)⟩,
   ⟨800246,witnessRule valid_2082 (by decide)⟩,
   ⟨940480,witnessDivisors _ 3 [1,3,3797,11391,504287107,1512861321] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨998008,witnessRule valid_1669 (by decide)⟩,
   ⟨998075,witnessRule valid_1721 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_15 : CheckedBlock 64 15 :=
  excludeBlock columns (a := 15000064) (width := 1000000) prefixPoints_15
    (by decide) (by decide) (by decide)

private def prefixPoints_16 : List (Witness 16000064) :=
  [⟨128947,witnessRule valid_2778 (by decide)⟩,
   ⟨202438,witnessRule valid_2598 (by decide)⟩,
   ⟨270886,witnessRule valid_2005 (by decide)⟩,
   ⟨339656,witnessRule valid_443 (by decide)⟩,
   ⟨412382,witnessRule valid_848 (by decide)⟩,
   ⟨574291,witnessDivisors _ 3 [1,3,4973,14919,400344163,1201032489] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨709656,witnessRule valid_379 (by decide)⟩,
   ⟨726307,witnessRule valid_1714 (by decide)⟩,
   ⟨801835,witnessRule valid_1436 (by decide)⟩,
   ⟨905011,witnessRule valid_1718 (by decide)⟩,
   ⟨953331,witnessRule valid_1388 (by decide)⟩,
   ⟨965472,witnessRule valid_2082 (by decide)⟩,
   ⟨995587,witnessRule valid_2118 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_16 : CheckedBlock 64 16 :=
  excludeBlock columns (a := 16000064) (width := 1000000) prefixPoints_16
    (by decide) (by decide) (by decide)

private def prefixPoints_17 : List (Witness 17000064) :=
  [⟨12763,witnessRule valid_3215 (by decide)⟩,
   ⟨80176,witnessRule valid_3141 (by decide)⟩,
   ⟨368083,witnessRule valid_3138 (by decide)⟩,
   ⟨401782,witnessDivisors _ 1 [1,28949,216619891,6270929224559] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨564682,witnessRule valid_2735 (by decide)⟩,
   ⟨693154,witnessRule valid_2095 (by decide)⟩,
   ⟨798211,witnessRule valid_922 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_17 : CheckedBlock 64 17 :=
  excludeBlock columns (a := 17000064) (width := 1000000) prefixPoints_17
    (by decide) (by decide) (by decide)

private def prefixPoints_18 : List (Witness 18000064) :=
  [⟨232550,witnessRule valid_2254 (by decide)⟩,
   ⟨405298,witnessRule valid_3642 (by decide)⟩,
   ⟨504130,witnessRule valid_3996 (by decide)⟩,
   ⟨733460,witnessRule valid_2175 (by decide)⟩,
   ⟨908470,witnessRule valid_848 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_18 : CheckedBlock 64 18 :=
  excludeBlock columns (a := 18000064) (width := 1000000) prefixPoints_18
    (by decide) (by decide) (by decide)

private def prefixPoints_19 : List (Witness 19000064) :=
  [⟨97779,witnessRule valid_694 (by decide)⟩,
   ⟨493106,witnessRule valid_2791 (by decide)⟩,
   ⟨494284,witnessRule valid_2768 (by decide)⟩,
   ⟨537062,witnessRule valid_3303 (by decide)⟩,
   ⟨577726,witnessRule valid_3426 (by decide)⟩,
   ⟨656220,witnessRule valid_862 (by decide)⟩,
   ⟨657963,witnessRule valid_3830 (by decide)⟩,
   ⟨716571,witnessRule valid_3177 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_19 : CheckedBlock 64 19 :=
  excludeBlock columns (a := 19000064) (width := 1000000) prefixPoints_19
    (by decide) (by decide) (by decide)

private def prefixPoints_20 : List (Witness 20000064) :=
  [⟨74296,witnessRule valid_3670 (by decide)⟩,
   ⟨192372,witnessRule valid_1231 (by decide)⟩,
   ⟨314146,witnessRule valid_944 (by decide)⟩,
   ⟨483851,witnessRule valid_1519 (by decide)⟩,
   ⟨634392,witnessRule valid_3141 (by decide)⟩,
   ⟨755656,witnessRule valid_976 (by decide)⟩,
   ⟨877246,witnessRule valid_2768 (by decide)⟩,
   ⟨964048,witnessRule valid_1077 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_20 : CheckedBlock 64 20 :=
  excludeBlock columns (a := 20000064) (width := 1000000) prefixPoints_20
    (by decide) (by decide) (by decide)

private def prefixPoints_21 : List (Witness 21000064) :=
  [⟨381848,witnessDivisors _ 2 [1,2,7331,14662,525520789] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨548867,witnessDivisors _ 2 [1,2,7079,14158,548479501] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨637307,witnessRule valid_3830 (by decide)⟩,
   ⟨663107,witnessDivisors _ 2 [1,2,49033,98066,79604963] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨663292,witnessDivisors _ 4 [1,2,4,42043,84086,168172,46420373] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨746030,witnessDivisors _ 9 [1,3,9,941,2823,8469,925306699,2775920097,8327760291,870713603759,2612140811277,7836422433831] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨925859,witnessDivisors _ 1 [1,35089,225176711,7901225612279] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨953232,witnessRule valid_802 (by decide)⟩,
   ⟨963248,witnessRule valid_926 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_21 : CheckedBlock 64 21 :=
  excludeBlock columns (a := 21000064) (width := 1000000) prefixPoints_21
    (by decide) (by decide) (by decide)

private def prefixPoints_22 : List (Witness 22000064) :=
  [⟨79984,witnessRule valid_898 (by decide)⟩,
   ⟨282267,witnessRule valid_3678 (by decide)⟩,
   ⟨502012,witnessRule valid_1101 (by decide)⟩,
   ⟨514499,witnessRule valid_3188 (by decide)⟩,
   ⟨531940,witnessRule valid_2283 (by decide)⟩,
   ⟨870920,witnessDivisors _ 2 [1,2,21067,42134,195608957] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨897611,witnessDivisors _ 1 [1,4007,10559,195023] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_22 : CheckedBlock 64 22 :=
  excludeBlock columns (a := 22000064) (width := 1000000) prefixPoints_22
    (by decide) (by decide) (by decide)

private def prefixPoints_23 : List (Witness 23000064) :=
  [⟨245142,witnessRule valid_848 (by decide)⟩,
   ⟨259931,witnessRule valid_3884 (by decide)⟩,
   ⟨276626,witnessRule valid_1226 (by decide)⟩,
   ⟨308483,witnessRule valid_2031 (by decide)⟩,
   ⟨819158,witnessRule valid_3088 (by decide)⟩,
   ⟨939030,witnessRule valid_1127 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_23 : CheckedBlock 64 23 :=
  excludeBlock columns (a := 23000064) (width := 1000000) prefixPoints_23
    (by decide) (by decide) (by decide)

private def prefixPoints_24 : List (Witness 24000064) :=
  [⟨325347,witnessRule valid_757 (by decide)⟩,
   ⟨347115,witnessRule valid_1569 (by decide)⟩,
   ⟨449540,witnessRule valid_1047 (by decide)⟩,
   ⟨535192,witnessRule valid_1101 (by decide)⟩,
   ⟨549291,witnessRule valid_1803 (by decide)⟩,
   ⟨606170,witnessRule valid_1138 (by decide)⟩,
   ⟨675131,witnessRule valid_2356 (by decide)⟩,
   ⟨749899,witnessRule valid_2588 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_24 : CheckedBlock 64 24 :=
  excludeBlock columns (a := 24000064) (width := 1000000) prefixPoints_24
    (by decide) (by decide) (by decide)

private def prefixPoints_25 : List (Witness 25000064) :=
  [⟨34714,witnessRule valid_3857 (by decide)⟩,
   ⟨591187,witnessDivisors _ 1 [1,69737,132240607,9222063210359] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_25 : CheckedBlock 64 25 :=
  excludeBlock columns (a := 25000064) (width := 1000000) prefixPoints_25
    (by decide) (by decide) (by decide)

private def prefixPoints_26 : List (Witness 26000064) :=
  [⟨25356,witnessRule valid_766 (by decide)⟩,
   ⟨132931,witnessRule valid_541 (by decide)⟩,
   ⟨182435,witnessRule valid_3970 (by decide)⟩,
   ⟨274978,witnessRule valid_1412 (by decide)⟩,
   ⟨666562,witnessDivisors _ 10 [1,2,5,10,25,50,44987,89974,224935,449870,1124675,2249350,4272161] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨878982,witnessRule valid_3085 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_26 : CheckedBlock 64 26 :=
  excludeBlock columns (a := 26000064) (width := 1000000) prefixPoints_26
    (by decide) (by decide) (by decide)

private def prefixPoints_27 : List (Witness 27000064) :=
  [⟨161012,witnessRule valid_3578 (by decide)⟩,
   ⟨507971,witnessRule valid_2589 (by decide)⟩,
   ⟨567604,witnessRule valid_778 (by decide)⟩,
   ⟨625214,witnessRule valid_3771 (by decide)⟩,
   ⟨664626,witnessRule valid_1619 (by decide)⟩,
   ⟨667742,witnessRule valid_2202 (by decide)⟩,
   ⟨746747,witnessRule valid_2558 (by decide)⟩,
   ⟨760528,witnessRule valid_2638 (by decide)⟩,
   ⟨803306,witnessDivisors _ 1 [1,17491,572821589,10019222413199] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨844508,witnessRule valid_1149 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_27 : CheckedBlock 64 27 :=
  excludeBlock columns (a := 27000064) (width := 1000000) prefixPoints_27
    (by decide) (by decide) (by decide)

private def prefixPoints_28 : List (Witness 28000064) :=
  [⟨352970,witnessRule valid_2526 (by decide)⟩,
   ⟨364275,witnessRule valid_3525 (by decide)⟩,
   ⟨375498,witnessRule valid_998 (by decide)⟩,
   ⟨514258,witnessRule valid_1712 (by decide)⟩,
   ⟨628211,witnessRule valid_1959 (by decide)⟩,
   ⟨645322,witnessRule valid_1468 (by decide)⟩,
   ⟨656907,witnessDivisors _ 7 [1,7,1607,10903,11249,76321,84199,589393,17521121,122647847] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨733090,witnessRule valid_2775 (by decide)⟩,
   ⟨772547,witnessRule valid_733 (by decide)⟩,
   ⟨873723,witnessRule valid_922 (by decide)⟩,
   ⟨937226,witnessRule valid_2994 (by decide)⟩,
   ⟨973776,witnessRule valid_3703 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_28 : CheckedBlock 64 28 :=
  excludeBlock columns (a := 28000064) (width := 1000000) prefixPoints_28
    (by decide) (by decide) (by decide)

private def prefixPoints_29 : List (Witness 29000064) :=
  [⟨12188,witnessRule valid_3963 (by decide)⟩,
   ⟨75147,witnessRule valid_2417 (by decide)⟩,
   ⟨93340,witnessRule valid_1996 (by decide)⟩,
   ⟨143388,witnessRule valid_2274 (by decide)⟩,
   ⟨161550,witnessRule valid_944 (by decide)⟩,
   ⟨350572,witnessRule valid_2095 (by decide)⟩,
   ⟨378787,witnessDivisors _ 2 [1,2,13451,26902,393538129] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨382600,witnessRule valid_2598 (by decide)⟩,
   ⟨545772,witnessDivisors _ 2 [1,2,5953,11906,894266543] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨659828,witnessRule valid_862 (by decide)⟩,
   ⟨717756,witnessDivisors _ 4 [1,2,4,62983,125966,251932,42507953] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_29 : CheckedBlock 64 29 :=
  excludeBlock columns (a := 29000064) (width := 1000000) prefixPoints_29
    (by decide) (by decide) (by decide)

private def prefixPoints_30 : List (Witness 30000064) :=
  [⟨64091,witnessRule valid_766 (by decide)⟩,
   ⟨177458,witnessRule valid_1127 (by decide)⟩,
   ⟨357182,witnessRule valid_2787 (by decide)⟩,
   ⟨420683,witnessRule valid_974 (by decide)⟩,
   ⟨527267,witnessRule valid_1041 (by decide)⟩,
   ⟨636662,witnessRule valid_1648 (by decide)⟩,
   ⟨692162,witnessRule valid_577 (by decide)⟩,
   ⟨852426,witnessRule valid_2768 (by decide)⟩,
   ⟨874872,witnessRule valid_2766 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_30 : CheckedBlock 64 30 :=
  excludeBlock columns (a := 30000064) (width := 1000000) prefixPoints_30
    (by decide) (by decide) (by decide)

private def prefixPoints_31 : List (Witness 31000064) :=
  [⟨239411,witnessRule valid_2924 (by decide)⟩,
   ⟨734267,witnessRule valid_2742 (by decide)⟩,
   ⟨746196,witnessDivisors _ 7 [1,7,23,79,113,161,553,791,1817,2599] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨795484,witnessRule valid_3857 (by decide)⟩,
   ⟨981076,witnessDivisors _ 1 [1,23819,483845821,11524723610399] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_31 : CheckedBlock 64 31 :=
  excludeBlock columns (a := 31000064) (width := 1000000) prefixPoints_31
    (by decide) (by decide) (by decide)

private def prefixPoints_32 : List (Witness 32000064) :=
  [⟨154496,witnessRule valid_2298 (by decide)⟩,
   ⟨239331,witnessRule valid_691 (by decide)⟩,
   ⟨623208,witnessRule valid_3837 (by decide)⟩,
   ⟨654514,witnessRule valid_706 (by decide)⟩,
   ⟨657132,witnessRule valid_1985 (by decide)⟩,
   ⟨660603,witnessRule valid_3490 (by decide)⟩,
   ⟨863016,witnessRule valid_2841 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_32 : CheckedBlock 64 32 :=
  excludeBlock columns (a := 32000064) (width := 1000000) prefixPoints_32
    (by decide) (by decide) (by decide)

private def prefixPoints_33 : List (Witness 33000064) :=
  [⟨311235,witnessRule valid_2108 (by decide)⟩,
   ⟨409560,witnessRule valid_947 (by decide)⟩,
   ⟨658075,witnessRule valid_3155 (by decide)⟩,
   ⟨924536,witnessRule valid_848 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_33 : CheckedBlock 64 33 :=
  excludeBlock columns (a := 33000064) (width := 1000000) prefixPoints_33
    (by decide) (by decide) (by decide)

private def prefixPoints_34 : List (Witness 34000064) :=
  [⟨30208,witnessRule valid_3385 (by decide)⟩,
   ⟨107178,witnessRule valid_1835 (by decide)⟩,
   ⟨261748,witnessRule valid_1299 (by decide)⟩,
   ⟨267987,witnessRule valid_1609 (by decide)⟩,
   ⟨556771,witnessRule valid_1765 (by decide)⟩,
   ⟨582187,witnessRule valid_1765 (by decide)⟩,
   ⟨617651,witnessRule valid_3594 (by decide)⟩,
   ⟨749098,witnessRule valid_2864 (by decide)⟩,
   ⟨849171,witnessRule valid_2253 (by decide)⟩,
   ⟨907872,witnessDivisors _ 1 [1,4999,2516388041,12579423816959] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_34 : CheckedBlock 64 34 :=
  excludeBlock columns (a := 34000064) (width := 1000000) prefixPoints_34
    (by decide) (by decide) (by decide)

private def prefixPoints_35 : List (Witness 35000064) :=
  [⟨99088,witnessRule valid_3126 (by decide)⟩,
   ⟨285482,witnessRule valid_2384 (by decide)⟩,
   ⟨318972,witnessRule valid_1813 (by decide)⟩,
   ⟨365107,witnessRule valid_3897 (by decide)⟩,
   ⟨482778,witnessRule valid_1735 (by decide)⟩,
   ⟨503978,witnessRule valid_1424 (by decide)⟩,
   ⟨650339,witnessRule valid_802 (by decide)⟩,
   ⟨766123,witnessRule valid_3966 (by decide)⟩,
   ⟨880731,witnessRule valid_1371 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_35 : CheckedBlock 64 35 :=
  excludeBlock columns (a := 35000064) (width := 1000000) prefixPoints_35
    (by decide) (by decide) (by decide)

private def prefixPoints_36 : List (Witness 36000064) :=
  [⟨14890,witnessRule valid_571 (by decide)⟩,
   ⟨276180,witnessRule valid_1072 (by decide)⟩,
   ⟨276746,witnessDivisors _ 1 [1,14387,908647477,13072711251599] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨403498,witnessRule valid_2298 (by decide)⟩,
   ⟨571186,witnessRule valid_1808 (by decide)⟩,
   ⟨736778,witnessRule valid_958 (by decide)⟩,
   ⟨744326,witnessRule valid_2238 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_36 : CheckedBlock 64 36 :=
  excludeBlock columns (a := 36000064) (width := 1000000) prefixPoints_36
    (by decide) (by decide) (by decide)

private def prefixPoints_37 : List (Witness 37000064) :=
  [⟨249322,witnessRule valid_2157 (by decide)⟩,
   ⟨249776,witnessRule valid_3126 (by decide)⟩,
   ⟨292610,witnessRule valid_401 (by decide)⟩,
   ⟨590688,witnessRule valid_2202 (by decide)⟩,
   ⟨695932,witnessRule valid_1168 (by decide)⟩,
   ⟨807206,witnessRule valid_1745 (by decide)⟩,
   ⟨954766,witnessRule valid_1671 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_37 : CheckedBlock 64 37 :=
  excludeBlock columns (a := 37000064) (width := 1000000) prefixPoints_37
    (by decide) (by decide) (by decide)

private def prefixPoints_38 : List (Witness 38000064) :=
  [⟨329091,witnessDivisors _ 1 [1,59539,231987341,13812294295799] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨456515,witnessRule valid_3279 (by decide)⟩,
   ⟨567338,witnessRule valid_3606 (by decide)⟩,
   ⟨834091,witnessRule valid_3693 (by decide)⟩,
   ⟨989283,witnessRule valid_3805 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_38 : CheckedBlock 64 38 :=
  excludeBlock columns (a := 38000064) (width := 1000000) prefixPoints_38
    (by decide) (by decide) (by decide)

private def prefixPoints_39 : List (Witness 39000064) :=
  [⟨208728,witnessRule valid_373 (by decide)⟩,
   ⟨780483,witnessRule valid_1046 (by decide)⟩,
   ⟨802291,witnessRule valid_1412 (by decide)⟩,
   ⟨808888,witnessRule valid_3987 (by decide)⟩,
   ⟨905731,witnessDivisors _ 2 [1,2,14143,28286,508394693] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_39 : CheckedBlock 64 39 :=
  excludeBlock columns (a := 39000064) (width := 1000000) prefixPoints_39
    (by decide) (by decide) (by decide)

private def prefixPoints_40 : List (Witness 40000064) :=
  [⟨166771,witnessRule valid_2874 (by decide)⟩,
   ⟨186123,witnessDivisors _ 1 [1,55469,261073651,14481494347319] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨274483,witnessDivisors _ 4 [1,2,4,31531,63062,126124,115071959] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨347974,witnessRule valid_1214 (by decide)⟩,
   ⟨355840,witnessRule valid_643 (by decide)⟩,
   ⟨528158,witnessRule valid_1735 (by decide)⟩,
   ⟨573598,witnessRule valid_848 (by decide)⟩,
   ⟨682580,witnessRule valid_3046 (by decide)⟩,
   ⟨689386,witnessRule valid_1163 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_40 : CheckedBlock 64 40 :=
  excludeBlock columns (a := 40000064) (width := 1000000) prefixPoints_40
    (by decide) (by decide) (by decide)

private def prefixPoints_41 : List (Witness 41000064) :=
  [⟨273692,witnessRule valid_3088 (by decide)⟩,
   ⟨365187,witnessRule valid_2634 (by decide)⟩,
   ⟨416458,witnessRule valid_1101 (by decide)⟩,
   ⟨570966,witnessRule valid_2009 (by decide)⟩,
   ⟨817307,witnessDivisors _ 2 [1,2,32497,64994,231856907] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨859139,witnessRule valid_3890 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_41 : CheckedBlock 64 41 :=
  excludeBlock columns (a := 41000064) (width := 1000000) prefixPoints_41
    (by decide) (by decide) (by decide)

private def prefixPoints_42 : List (Witness 42000064) :=
  [⟨201026,witnessRule valid_1059 (by decide)⟩,
   ⟨501523,witnessRule valid_3462 (by decide)⟩,
   ⟨756620,witnessRule valid_2946 (by decide)⟩,
   ⟨788676,witnessRule valid_2372 (by decide)⟩,
   ⟨850604,witnessRule valid_2396 (by decide)⟩,
   ⟨916040,witnessRule valid_934 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_42 : CheckedBlock 64 42 :=
  excludeBlock columns (a := 42000064) (width := 1000000) prefixPoints_42
    (by decide) (by decide) (by decide)

private def prefixPoints_43 : List (Witness 43000064) :=
  [⟨98515,witnessRule valid_1126 (by decide)⟩,
   ⟨140876,witnessRule valid_2753 (by decide)⟩,
   ⟨533698,witnessRule valid_3490 (by decide)⟩,
   ⟨702364,witnessRule valid_3217 (by decide)⟩,
   ⟨752451,witnessRule valid_1138 (by decide)⟩,
   ⟨915680,witnessRule valid_944 (by decide)⟩,
   ⟨952603,witnessRule valid_1142 (by decide)⟩,
   ⟨966328,witnessRule valid_1636 (by decide)⟩,
   ⟨986680,witnessRule valid_3141 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_43 : CheckedBlock 64 43 :=
  excludeBlock columns (a := 43000064) (width := 1000000) prefixPoints_43
    (by decide) (by decide) (by decide)

private def prefixPoints_44 : List (Witness 44000064) :=
  [⟨275306,witnessRule valid_766 (by decide)⟩,
   ⟨438288,witnessRule valid_2154 (by decide)⟩,
   ⟨456636,witnessRule valid_2118 (by decide)⟩,
   ⟨757298,witnessRule valid_1532 (by decide)⟩,
   ⟨843222,witnessRule valid_1366 (by decide)⟩,
   ⟨872108,witnessRule valid_1094 (by decide)⟩,
   ⟨971124,witnessRule valid_794 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_44 : CheckedBlock 64 44 :=
  excludeBlock columns (a := 44000064) (width := 1000000) prefixPoints_44
    (by decide) (by decide) (by decide)

private def prefixPoints_45 : List (Witness 45000064) :=
  [⟨128859,witnessRule valid_2204 (by decide)⟩,
   ⟨220378,witnessRule valid_2238 (by decide)⟩,
   ⟨256492,witnessRule valid_1552 (by decide)⟩,
   ⟨285200,witnessRule valid_1119 (by decide)⟩,
   ⟨447362,witnessDivisors _ 4 [1,2,4,10271,20542,41084,398632909] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨707666,witnessRule valid_3076 (by decide)⟩,
   ⟨853484,witnessRule valid_3282 (by decide)⟩,
   ⟨983146,witnessRule valid_619 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_45 : CheckedBlock 64 45 :=
  excludeBlock columns (a := 45000064) (width := 1000000) prefixPoints_45
    (by decide) (by decide) (by decide)

private def prefixPoints_46 : List (Witness 46000064) :=
  [⟨382646,witnessRule valid_2238 (by decide)⟩,
   ⟨503272,witnessRule valid_2766 (by decide)⟩,
   ⟨609488,witnessRule valid_2078 (by decide)⟩,
   ⟨637924,witnessRule valid_3147 (by decide)⟩,
   ⟨861731,witnessRule valid_2254 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_46 : CheckedBlock 64 46 :=
  excludeBlock columns (a := 46000064) (width := 1000000) prefixPoints_46
    (by decide) (by decide) (by decide)

private def prefixPoints_47 : List (Witness 47000064) :=
  [⟨131467,witnessRule valid_3857 (by decide)⟩,
   ⟨199938,witnessRule valid_1174 (by decide)⟩,
   ⟨373072,witnessRule valid_347 (by decide)⟩,
   ⟨622530,witnessRule valid_766 (by decide)⟩,
   ⟨780046,witnessRule valid_746 (by decide)⟩,
   ⟨941976,witnessRule valid_848 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_47 : CheckedBlock 64 47 :=
  excludeBlock columns (a := 47000064) (width := 1000000) prefixPoints_47
    (by decide) (by decide) (by decide)

private def prefixPoints_48 : List (Witness 48000064) :=
  [⟨138411,witnessRule valid_617 (by decide)⟩,
   ⟨436178,witnessRule valid_2186 (by decide)⟩,
   ⟨664958,witnessRule valid_1915 (by decide)⟩,
   ⟨853508,witnessRule valid_944 (by decide)⟩,
   ⟨856458,witnessRule valid_1915 (by decide)⟩,
   ⟨871808,witnessRule valid_848 (by decide)⟩,
   ⟨906182,witnessRule valid_2155 (by decide)⟩,
   ⟨932187,witnessRule valid_842 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_48 : CheckedBlock 64 48 :=
  excludeBlock columns (a := 48000064) (width := 1000000) prefixPoints_48
    (by decide) (by decide) (by decide)

private def prefixPoints_49 : List (Witness 49000064) :=
  [⟨102788,witnessRule valid_1828 (by decide)⟩,
   ⟨175859,witnessRule valid_1796 (by decide)⟩,
   ⟨505138,witnessRule valid_1101 (by decide)⟩,
   ⟨804531,witnessDivisors _ 2 [1,2,34211,68422,262307209] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_49 : CheckedBlock 64 49 :=
  excludeBlock columns (a := 49000064) (width := 1000000) prefixPoints_49
    (by decide) (by decide) (by decide)

private def prefixPoints_50 : List (Witness 50000064) :=
  [⟨355971,witnessRule valid_2764 (by decide)⟩,
   ⟨803371,witnessRule valid_1492 (by decide)⟩,
   ⟨843267,witnessRule valid_818 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_50 : CheckedBlock 64 50 :=
  excludeBlock columns (a := 50000064) (width := 1000000) prefixPoints_50
    (by decide) (by decide) (by decide)

private def prefixPoints_51 : List (Witness 51000064) :=
  [⟨24195,witnessRule valid_1077 (by decide)⟩,
   ⟨105388,witnessRule valid_3987 (by decide)⟩,
   ⟨566008,witnessRule valid_3568 (by decide)⟩,
   ⟨694483,witnessRule valid_3695 (by decide)⟩,
   ⟨975923,witnessRule valid_746 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_51 : CheckedBlock 64 51 :=
  excludeBlock columns (a := 51000064) (width := 1000000) prefixPoints_51
    (by decide) (by decide) (by decide)

private def prefixPoints_52 : List (Witness 52000064) :=
  [⟨8147,witnessRule valid_983 (by decide)⟩,
   ⟨128334,witnessRule valid_1556 (by decide)⟩,
   ⟨247566,witnessRule valid_2842 (by decide)⟩,
   ⟨302312,witnessRule valid_1072 (by decide)⟩,
   ⟨355828,witnessRule valid_547 (by decide)⟩,
   ⟨547336,witnessRule valid_3177 (by decide)⟩,
   ⟨781820,witnessRule valid_866 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_52 : CheckedBlock 64 52 :=
  excludeBlock columns (a := 52000064) (width := 1000000) prefixPoints_52
    (by decide) (by decide) (by decide)

private def prefixPoints_53 : List (Witness 53000064) :=
  [⟨64434,witnessRule valid_3463 (by decide)⟩,
   ⟨315342,witnessRule valid_1642 (by decide)⟩,
   ⟨538648,witnessDivisors _ 3 [1,3,90007,270021,71450777,214352331] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨840982,witnessRule valid_848 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_53 : CheckedBlock 64 53 :=
  excludeBlock columns (a := 53000064) (width := 1000000) prefixPoints_53
    (by decide) (by decide) (by decide)

private def prefixPoints_54 : List (Witness 54000064) :=
  [⟨592598,witnessRule valid_3530 (by decide)⟩,
   ⟨623792,witnessRule valid_848 (by decide)⟩,
   ⟨770792,witnessRule valid_443 (by decide)⟩,
   ⟨872803,witnessDivisors _ 2 [1,2,45289,90578,218308931] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_54 : CheckedBlock 64 54 :=
  excludeBlock columns (a := 54000064) (width := 1000000) prefixPoints_54
    (by decide) (by decide) (by decide)

private def prefixPoints_55 : List (Witness 55000064) :=
  [⟨9891,witnessRule valid_1318 (by decide)⟩,
   ⟨278420,witnessRule valid_421 (by decide)⟩,
   ⟨751788,witnessRule valid_944 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_55 : CheckedBlock 64 55 :=
  excludeBlock columns (a := 55000064) (width := 1000000) prefixPoints_55
    (by decide) (by decide) (by decide)

private def prefixPoints_56 : List (Witness 56000064) :=
  [⟨324498,witnessRule valid_1623 (by decide)⟩,
   ⟨337506,witnessRule valid_758 (by decide)⟩,
   ⟨537987,witnessRule valid_1317 (by decide)⟩,
   ⟨786787,witnessRule valid_3594 (by decide)⟩,
   ⟨940578,witnessRule valid_2082 (by decide)⟩,
   ⟨999347,witnessRule valid_2762 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_56 : CheckedBlock 64 56 :=
  excludeBlock columns (a := 56000064) (width := 1000000) prefixPoints_56
    (by decide) (by decide) (by decide)

private def prefixPoints_57 : List (Witness 57000064) :=
  [⟨96091,witnessRule valid_2766 (by decide)⟩,
   ⟨157331,witnessRule valid_2694 (by decide)⟩,
   ⟨277051,witnessDivisors _ 4 [1,2,4,13859,27718,55436,372328111] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨529747,witnessDivisors _ 1 [1,4733,4380190723,20731442691959] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨777547,witnessRule valid_2154 (by decide)⟩,
   ⟨804620,witnessRule valid_1072 (by decide)⟩,
   ⟨932395,witnessDivisors _ 6 [1,2,3,6,2273,4546,6819,9059,13638] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨949707,witnessDivisors _ 1 [1,14879,1403506921,20882779477559] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨969435,witnessRule valid_1858 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_57 : CheckedBlock 64 57 :=
  excludeBlock columns (a := 57000064) (width := 1000000) prefixPoints_57
    (by decide) (by decide) (by decide)

private def prefixPoints_58 : List (Witness 58000064) :=
  [⟨82448,witnessRule valid_1136 (by decide)⟩,
   ⟨206888,witnessRule valid_746 (by decide)⟩,
   ⟨229084,witnessRule valid_3590 (by decide)⟩,
   ⟨540456,witnessRule valid_922 (by decide)⟩,
   ⟨564699,witnessRule valid_2094 (by decide)⟩,
   ⟨787342,witnessDivisors _ 1 [1,32611,649616069,21184629626159] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨797763,witnessRule valid_2454 (by decide)⟩,
   ⟨888611,witnessRule valid_1396 (by decide)⟩,
   ⟨941659,witnessRule valid_1396 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_58 : CheckedBlock 64 58 :=
  excludeBlock columns (a := 58000064) (width := 1000000) prefixPoints_58
    (by decide) (by decide) (by decide)

private def prefixPoints_59 : List (Witness 59000064) :=
  [⟨42812,witnessRule valid_3479 (by decide)⟩,
   ⟨67762,witnessRule valid_842 (by decide)⟩,
   ⟨169542,witnessRule valid_3678 (by decide)⟩,
   ⟨557816,witnessRule valid_619 (by decide)⟩,
   ⟨671126,witnessRule valid_2572 (by decide)⟩,
   ⟨854596,witnessRule valid_353 (by decide)⟩,
   ⟨949122,witnessRule valid_1047 (by decide)⟩,
   ⟨994075,witnessRule valid_2454 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_59 : CheckedBlock 64 59 :=
  excludeBlock columns (a := 59000064) (width := 1000000) prefixPoints_59
    (by decide) (by decide) (by decide)

private def prefixPoints_60 : List (Witness 60000064) :=
  [⟨18896,witnessRule valid_914 (by decide)⟩,
   ⟨21854,witnessRule valid_3490 (by decide)⟩,
   ⟨34450,witnessRule valid_2348 (by decide)⟩,
   ⟨59746,witnessRule valid_3155 (by decide)⟩,
   ⟨152504,witnessRule valid_1616 (by decide)⟩,
   ⟨257315,witnessRule valid_599 (by decide)⟩,
   ⟨269436,witnessRule valid_2238 (by decide)⟩,
   ⟨333883,witnessRule valid_1388 (by decide)⟩,
   ⟨354980,witnessRule valid_3771 (by decide)⟩,
   ⟨448664,witnessRule valid_1779 (by decide)⟩,
   ⟨765603,witnessRule valid_991 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_60 : CheckedBlock 64 60 :=
  excludeBlock columns (a := 60000064) (width := 1000000) prefixPoints_60
    (by decide) (by decide) (by decide)

private def prefixPoints_61 : List (Witness 61000064) :=
  [⟨175907,witnessRule valid_3772 (by decide)⟩,
   ⟨325235,witnessDivisors _ 2 [1,2,4691,9382,2355487609] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨369163,witnessRule valid_349 (by decide)⟩,
   ⟨540163,witnessRule valid_419 (by decide)⟩,
   ⟨725786,witnessRule valid_898 (by decide)⟩,
   ⟨775092,witnessRule valid_3303 (by decide)⟩,
   ⟨806803,witnessRule valid_1354 (by decide)⟩,
   ⟨824491,witnessRule valid_1223 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_61 : CheckedBlock 64 61 :=
  excludeBlock columns (a := 61000064) (width := 1000000) prefixPoints_61
    (by decide) (by decide) (by decide)

private def prefixPoints_62 : List (Witness 62000064) :=
  [⟨72258,witnessRule valid_3414 (by decide)⟩,
   ⟨155648,witnessRule valid_944 (by decide)⟩,
   ⟨164712,witnessRule valid_1072 (by decide)⟩,
   ⟨196816,witnessRule valid_2634 (by decide)⟩,
   ⟨492642,witnessRule valid_367 (by decide)⟩,
   ⟨653822,witnessRule valid_848 (by decide)⟩,
   ⟨664962,witnessRule valid_2118 (by decide)⟩,
   ⟨724072,witnessDivisors _ 1 [1,6907,3272516237,22603269648959] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨784200,witnessRule valid_1328 (by decide)⟩,
   ⟨794820,witnessRule valid_3790 (by decide)⟩,
   ⟨909720,witnessRule valid_1838 (by decide)⟩,
   ⟨946704,witnessRule valid_2742 (by decide)⟩,
   ⟨986886,witnessRule valid_818 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_62 : CheckedBlock 64 62 :=
  excludeBlock columns (a := 62000064) (width := 1000000) prefixPoints_62
    (by decide) (by decide) (by decide)

private def prefixPoints_63 : List (Witness 63000064) :=
  [⟨39883,witnessRule valid_3996 (by decide)⟩,
   ⟨353667,witnessRule valid_3830 (by decide)⟩,
   ⟨391548,witnessRule valid_1264 (by decide)⟩,
   ⟨517059,witnessRule valid_3085 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_63 : CheckedBlock 64 63 :=
  excludeBlock columns (a := 63000064) (width := 1000000) prefixPoints_63
    (by decide) (by decide) (by decide)

private def prefixPoints_64 : List (Witness 64000064) :=
  [⟨147266,witnessRule valid_2818 (by decide)⟩,
   ⟨267434,witnessRule valid_419 (by decide)⟩,
   ⟨363251,witnessRule valid_3470 (by decide)⟩,
   ⟨421810,witnessRule valid_2325 (by decide)⟩,
   ⟨442856,witnessDivisors _ 5 [1,5,48821,244105,95133859,475669295,4644530130239,23222650651195] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨512667,witnessDivisors _ 1 [1,37517,619660627,23247807743159] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨521595,witnessRule valid_3897 (by decide)⟩,
   ⟨631664,witnessDivisors _ 5 [1,5,25,2081,2551,10405,12755,52025] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_64 : CheckedBlock 64 64 :=
  excludeBlock columns (a := 64000064) (width := 1000000) prefixPoints_64
    (by decide) (by decide) (by decide)

private def prefixPoints_65 : List (Witness 65000064) :=
  [⟨165980,witnessRule valid_3525 (by decide)⟩,
   ⟨307131,witnessRule valid_2634 (by decide)⟩,
   ⟨562816,witnessRule valid_1041 (by decide)⟩,
   ⟨568682,witnessRule valid_2768 (by decide)⟩,
   ⟨808659,witnessRule valid_2852 (by decide)⟩,
   ⟨845555,witnessRule valid_2175 (by decide)⟩,
   ⟨920587,witnessRule valid_3470 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_65 : CheckedBlock 64 65 :=
  excludeBlock columns (a := 65000064) (width := 1000000) prefixPoints_65
    (by decide) (by decide) (by decide)

private def prefixPoints_66 : List (Witness 66000064) :=
  [⟨33235,witnessRule valid_3935 (by decide)⟩,
   ⟨76616,witnessRule valid_1808 (by decide)⟩,
   ⟨134832,witnessRule valid_3342 (by decide)⟩,
   ⟨367347,witnessDivisors _ 4 [1,2,4,15149,30298,60596,394682161] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨740738,witnessRule valid_3501 (by decide)⟩,
   ⟨835742,witnessRule valid_1929 (by decide)⟩,
   ⟨971210,witnessRule valid_934 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_66 : CheckedBlock 64 66 :=
  excludeBlock columns (a := 66000064) (width := 1000000) prefixPoints_66
    (by decide) (by decide) (by decide)

private def prefixPoints_67 : List (Witness 67000064) :=
  [⟨102260,witnessRule valid_2901 (by decide)⟩,
   ⟨190187,witnessRule valid_718 (by decide)⟩,
   ⟨194139,witnessRule valid_3879 (by decide)⟩,
   ⟨198267,witnessRule valid_3862 (by decide)⟩,
   ⟨256107,witnessRule valid_3996 (by decide)⟩,
   ⟨342603,witnessRule valid_3846 (by decide)⟩,
   ⟨853720,witnessRule valid_1388 (by decide)⟩,
   ⟨875156,witnessRule valid_2382 (by decide)⟩,
   ⟨969795,witnessRule valid_2469 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_67 : CheckedBlock 64 67 :=
  excludeBlock columns (a := 67000064) (width := 1000000) prefixPoints_67
    (by decide) (by decide) (by decide)

private def prefixPoints_68 : List (Witness 68000064) :=
  [⟨123776,witnessRule valid_1744 (by decide)⟩,
   ⟨127779,witnessRule valid_1618 (by decide)⟩,
   ⟨196882,witnessRule valid_2195 (by decide)⟩,
   ⟨214420,witnessRule valid_2175 (by decide)⟩,
   ⟨464555,witnessRule valid_2042 (by decide)⟩,
   ⟨658228,witnessRule valid_3695 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_68 : CheckedBlock 64 68 :=
  excludeBlock columns (a := 68000064) (width := 1000000) prefixPoints_68
    (by decide) (by decide) (by decide)

private def prefixPoints_69 : List (Witness 69000064) :=
  [⟨9380,witnessRule valid_2836 (by decide)⟩,
   ⟨220508,witnessRule valid_3681 (by decide)⟩,
   ⟨437456,witnessRule valid_503 (by decide)⟩,
   ⟨890796,witnessRule valid_2094 (by decide)⟩,
   ⟨974523,witnessRule valid_2238 (by decide)⟩,
   ⟨986454,witnessDivisors _ 2 [1,2,65449,130898,192671711] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_69 : CheckedBlock 64 69 :=
  excludeBlock columns (a := 69000064) (width := 1000000) prefixPoints_69
    (by decide) (by decide) (by decide)

private def prefixPoints_70 : List (Witness 70000064) :=
  [⟨218272,witnessRule valid_866 (by decide)⟩,
   ⟨242764,witnessRule valid_718 (by decide)⟩,
   ⟨393491,witnessRule valid_431 (by decide)⟩,
   ⟨792510,witnessRule valid_677 (by decide)⟩,
   ⟨902267,witnessRule valid_2155 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_70 : CheckedBlock 64 70 :=
  excludeBlock columns (a := 70000064) (width := 1000000) prefixPoints_70
    (by decide) (by decide) (by decide)

private def prefixPoints_71 : List (Witness 71000064) :=
  [⟨13866,witnessRule valid_2276 (by decide)⟩,
   ⟨118547,witnessDivisors _ 2 [1,2,10399,20798,1232248421] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨166835,witnessRule valid_1676 (by decide)⟩,
   ⟨172547,witnessRule valid_1868 (by decide)⟩,
   ⟨391771,witnessRule valid_829 (by decide)⟩,
   ⟨513712,witnessRule valid_778 (by decide)⟩,
   ⟨638795,witnessRule valid_353 (by decide)⟩,
   ⟨656092,witnessRule valid_353 (by decide)⟩,
   ⟨938131,witnessDivisors _ 3 [1,3,28283,84849,305526853,916580559] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨973658,witnessRule valid_2228 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_71 : CheckedBlock 64 71 :=
  excludeBlock columns (a := 71000064) (width := 1000000) prefixPoints_71
    (by decide) (by decide) (by decide)

private def prefixPoints_72 : List (Witness 72000064) :=
  [⟨212970,witnessRule valid_3790 (by decide)⟩,
   ⟨823148,witnessDivisors _ 1 [1,46747,561374477,26242572676319] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨930115,witnessRule valid_2204 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_72 : CheckedBlock 64 72 :=
  excludeBlock columns (a := 72000064) (width := 1000000) prefixPoints_72
    (by decide) (by decide) (by decide)

private def prefixPoints_73 : List (Witness 73000064) :=
  [⟨12046,witnessRule valid_998 (by decide)⟩,
   ⟨267590,witnessRule valid_944 (by decide)⟩,
   ⟨902260,witnessRule valid_439 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_73 : CheckedBlock 64 73 :=
  excludeBlock columns (a := 73000064) (width := 1000000) prefixPoints_73
    (by decide) (by decide) (by decide)

private def prefixPoints_74 : List (Witness 74000064) :=
  [⟨74963,witnessRule valid_1371 (by decide)⟩,
   ⟨96003,witnessDivisors _ 2 [1,2,7127,14254,1873246717] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨121050,witnessRule valid_3609 (by decide)⟩,
   ⟨474488,witnessRule valid_2082 (by decide)⟩,
   ⟨692403,witnessRule valid_1754 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_74 : CheckedBlock 64 74 :=
  excludeBlock columns (a := 74000064) (width := 1000000) prefixPoints_74
    (by decide) (by decide) (by decide)

private def prefixPoints_75 : List (Witness 75000064) :=
  [⟨36242,witnessRule valid_2382 (by decide)⟩,
   ⟨339451,witnessDivisors _ 3 [1,3,46271,138813,195582169,586746507] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨376203,witnessRule valid_379 (by decide)⟩,
   ⟨493072,witnessRule valid_848 (by decide)⟩,
   ⟨811272,witnessRule valid_1396 (by decide)⟩,
   ⟨862964,witnessRule valid_3490 (by decide)⟩,
   ⟨880666,witnessRule valid_1707 (by decide)⟩,
   ⟨942603,witnessRule valid_3357 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_75 : CheckedBlock 64 75 :=
  excludeBlock columns (a := 75000064) (width := 1000000) prefixPoints_75
    (by decide) (by decide) (by decide)

private def prefixPoints_76 : List (Witness 76000064) :=
  [⟨59288,witnessDivisors _ 6 [1,2,3,6,1229,2458,3461,3687,6922] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨146274,witnessRule valid_3856 (by decide)⟩,
   ⟨244086,witnessRule valid_2845 (by decide)⟩,
   ⟨368776,witnessRule valid_3595 (by decide)⟩,
   ⟨651508,witnessRule valid_1328 (by decide)⟩,
   ⟨816476,witnessRule valid_2705 (by decide)⟩,
   ⟨837171,witnessRule valid_1516 (by decide)⟩,
   ⟨986998,witnessRule valid_2118 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_76 : CheckedBlock 64 76 :=
  excludeBlock columns (a := 76000064) (width := 1000000) prefixPoints_76
    (by decide) (by decide) (by decide)

private def prefixPoints_77 : List (Witness 77000064) :=
  [⟨229350,witnessRule valid_1761 (by decide)⟩,
   ⟨370915,witnessRule valid_2693 (by decide)⟩,
   ⟨783547,witnessRule valid_3573 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_77 : CheckedBlock 64 77 :=
  excludeBlock columns (a := 77000064) (width := 1000000) prefixPoints_77
    (by decide) (by decide) (by decide)

private def prefixPoints_78 : List (Witness 78000064) :=
  [⟨16915,witnessRule valid_3578 (by decide)⟩,
   ⟨117707,witnessRule valid_653 (by decide)⟩,
   ⟨196304,witnessRule valid_1328 (by decide)⟩,
   ⟨212083,witnessRule valid_3490 (by decide)⟩,
   ⟨322388,witnessRule valid_3303 (by decide)⟩,
   ⟨519638,witnessRule valid_1712 (by decide)⟩,
   ⟨548136,witnessRule valid_1306 (by decide)⟩,
   ⟨564638,witnessRule valid_1097 (by decide)⟩,
   ⟨654108,witnessDivisors _ 6 [1,2,3,6,31481,62962,94443,188886,150057799] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨654995,witnessRule valid_2325 (by decide)⟩,
   ⟨872048,witnessRule valid_1226 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_78 : CheckedBlock 64 78 :=
  excludeBlock columns (a := 78000064) (width := 1000000) prefixPoints_78
    (by decide) (by decide) (by decide)

private def prefixPoints_79 : List (Witness 79000064) :=
  [⟨145686,witnessDivisors _ 4 [1,2,4,13241,26482,52964,538497139] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨310932,witnessDivisors _ 1 [1,5443,5250874613,28580510518559] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨505451,witnessRule valid_3381 (by decide)⟩,
   ⟨589891,witnessRule valid_1421 (by decide)⟩,
   ⟨876828,witnessRule valid_379 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_79 : CheckedBlock 64 79 :=
  excludeBlock columns (a := 79000064) (width := 1000000) prefixPoints_79
    (by decide) (by decide) (by decide)

private def prefixPoints_80 : List (Witness 80000064) :=
  [⟨251964,witnessRule valid_998 (by decide)⟩,
   ⟨347331,witnessRule valid_2949 (by decide)⟩,
   ⟨387428,witnessRule valid_1203 (by decide)⟩,
   ⟨519459,witnessRule valid_1167 (by decide)⟩,
   ⟨747922,witnessRule valid_3606 (by decide)⟩,
   ⟨859204,witnessRule valid_2032 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_80 : CheckedBlock 64 80 :=
  excludeBlock columns (a := 80000064) (width := 1000000) prefixPoints_80
    (by decide) (by decide) (by decide)

private def prefixPoints_81 : List (Witness 81000064) :=
  [⟨59883,witnessRule valid_1396 (by decide)⟩,
   ⟨78762,witnessDivisors _ 2 [1,2,13177,26354,1108657727] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨256248,witnessRule valid_1388 (by decide)⟩,
   ⟨307446,witnessRule valid_1168 (by decide)⟩,
   ⟨325936,witnessRule valid_878 (by decide)⟩,
   ⟨376307,witnessRule valid_1119 (by decide)⟩,
   ⟨534787,witnessDivisors _ 2 [1,2,39041,78082,376295419] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨679091,witnessRule valid_1322 (by decide)⟩,
   ⟨798539,witnessRule valid_3501 (by decide)⟩,
   ⟨838214,witnessRule valid_1616 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_81 : CheckedBlock 64 81 :=
  excludeBlock columns (a := 81000064) (width := 1000000) prefixPoints_81
    (by decide) (by decide) (by decide)

private def prefixPoints_82 : List (Witness 82000064) :=
  [⟨257091,witnessRule valid_3231 (by decide)⟩,
   ⟨306083,witnessRule valid_1306 (by decide)⟩,
   ⟨311658,witnessRule valid_2238 (by decide)⟩,
   ⟨327656,witnessRule valid_2864 (by decide)⟩,
   ⟨376763,witnessRule valid_1604 (by decide)⟩,
   ⟨384334,witnessRule valid_2608 (by decide)⟩,
   ⟨421155,witnessRule valid_2435 (by decide)⟩,
   ⟨780371,witnessRule valid_2186 (by decide)⟩,
   ⟨780870,witnessRule valid_2406 (by decide)⟩,
   ⟨984323,witnessDivisors _ 2 [1,2,2213,4426,6756496543] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_82 : CheckedBlock 64 82 :=
  excludeBlock columns (a := 82000064) (width := 1000000) prefixPoints_82
    (by decide) (by decide) (by decide)

private def prefixPoints_83 : List (Witness 83000064) :=
  [⟨205748,witnessRule valid_976 (by decide)⟩,
   ⟨314403,witnessRule valid_2118 (by decide)⟩,
   ⟨565658,witnessRule valid_3532 (by decide)⟩,
   ⟨722064,witnessRule valid_848 (by decide)⟩,
   ⟨917422,witnessRule valid_848 (by decide)⟩,
   ⟨978916,witnessRule valid_1101 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_83 : CheckedBlock 64 83 :=
  excludeBlock columns (a := 83000064) (width := 1000000) prefixPoints_83
    (by decide) (by decide) (by decide)

private def prefixPoints_84 : List (Witness 84000064) :=
  [⟨12755,witnessRule valid_2775 (by decide)⟩,
   ⟨15234,witnessDivisors _ 5 [1,5,25,823,4115,20575,1471482517,7357412585] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨167795,witnessRule valid_2636 (by decide)⟩,
   ⟨321438,witnessRule valid_976 (by decide)⟩,
   ⟨406764,witnessDivisors _ 1 [1,6947,4378414357,30416844538079] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨701739,witnessRule valid_2598 (by decide)⟩,
   ⟨777112,witnessRule valid_3501 (by decide)⟩,
   ⟨852756,witnessDivisors _ 3 [1,3,7691,23073,35521,37309] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨895403,witnessRule valid_1202 (by decide)⟩,
   ⟨964704,witnessRule valid_349 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_84 : CheckedBlock 64 84 :=
  excludeBlock columns (a := 84000064) (width := 1000000) prefixPoints_84
    (by decide) (by decide) (by decide)

private def prefixPoints_85 : List (Witness 85000064) :=
  [⟨19787,witnessRule valid_2435 (by decide)⟩,
   ⟨98675,witnessRule valid_3138 (by decide)⟩,
   ⟨511291,witnessDivisors _ 2 [1,2,4903,9806,3142450733] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨534592,witnessRule valid_886 (by decide)⟩,
   ⟨653272,witnessRule valid_1532 (by decide)⟩,
   ⟨670371,witnessRule valid_3283 (by decide)⟩,
   ⟨723723,witnessRule valid_2258 (by decide)⟩,
   ⟨827020,witnessRule valid_1835 (by decide)⟩,
   ⟨831786,witnessRule valid_2082 (by decide)⟩,
   ⟨962392,witnessRule valid_1318 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_85 : CheckedBlock 64 85 :=
  excludeBlock columns (a := 85000064) (width := 1000000) prefixPoints_85
    (by decide) (by decide) (by decide)

private def prefixPoints_86 : List (Witness 86000064) :=
  [⟨366646,witnessRule valid_397 (by decide)⟩,
   ⟨424576,witnessRule valid_3626 (by decide)⟩,
   ⟨506307,witnessRule valid_886 (by decide)⟩,
   ⟨548580,witnessDivisors _ 1 [1,38783,804184033,31188669351839] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨631851,witnessRule valid_1835 (by decide)⟩,
   ⟨879448,witnessDivisors _ 4 [1,2,4,5741,8803,11482,17606] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨956203,witnessDivisors _ 5 [1,5,93629,468145,66935587,334677935,6267112075223,31335560376115] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_86 : CheckedBlock 64 86 :=
  excludeBlock columns (a := 86000064) (width := 1000000) prefixPoints_86
    (by decide) (by decide) (by decide)

private def prefixPoints_87 : List (Witness 87000064) :=
  [⟨58008,witnessRule valid_3530 (by decide)⟩,
   ⟨112348,witnessRule valid_2005 (by decide)⟩,
   ⟨248620,witnessRule valid_698 (by decide)⟩,
   ⟨439062,witnessRule valid_3609 (by decide)⟩,
   ⟨471198,witnessRule valid_353 (by decide)⟩,
   ⟨596364,witnessRule valid_848 (by decide)⟩,
   ⟨616282,witnessRule valid_3996 (by decide)⟩,
   ⟨875163,witnessRule valid_2118 (by decide)⟩,
   ⟨992659,witnessRule valid_2994 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_87 : CheckedBlock 64 87 :=
  excludeBlock columns (a := 87000064) (width := 1000000) prefixPoints_87
    (by decide) (by decide) (by decide)

private def prefixPoints_88 : List (Witness 88000064) :=
  [⟨194174,witnessRule valid_2082 (by decide)⟩,
   ⟨219728,witnessRule valid_3282 (by decide)⟩,
   ⟨253340,witnessRule valid_2606 (by decide)⟩,
   ⟨429278,witnessRule valid_1202 (by decide)⟩,
   ⟨476912,witnessDivisors _ 2 [1,2,7681,15362,2075482559] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨539651,witnessRule valid_1396 (by decide)⟩,
   ⟨802208,witnessRule valid_2633 (by decide)⟩,
   ⟨911059,witnessRule valid_2127 (by decide)⟩,
   ⟨994092,witnessRule valid_1915 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_88 : CheckedBlock 64 88 :=
  excludeBlock columns (a := 88000064) (width := 1000000) prefixPoints_88
    (by decide) (by decide) (by decide)

private def prefixPoints_89 : List (Witness 89000064) :=
  [⟨28707,witnessRule valid_1574 (by decide)⟩,
   ⟨41040,witnessRule valid_2514 (by decide)⟩,
   ⟨233707,witnessRule valid_706 (by decide)⟩,
   ⟨952116,witnessRule valid_1744 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_89 : CheckedBlock 64 89 :=
  excludeBlock columns (a := 89000064) (width := 1000000) prefixPoints_89
    (by decide) (by decide) (by decide)

private def prefixPoints_90 : List (Witness 90000064) :=
  [⟨300531,witnessRule valid_3890 (by decide)⟩,
   ⟨364524,witnessRule valid_2384 (by decide)⟩,
   ⟨395158,witnessRule valid_619 (by decide)⟩,
   ⟨541123,witnessRule valid_1604 (by decide)⟩,
   ⟨628251,witnessRule valid_1234 (by decide)⟩,
   ⟨773715,witnessRule valid_2274 (by decide)⟩,
   ⟨903838,witnessRule valid_2334 (by decide)⟩,
   ⟨989756,witnessRule valid_2608 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_90 : CheckedBlock 64 90 :=
  excludeBlock columns (a := 90000064) (width := 1000000) prefixPoints_90
    (by decide) (by decide) (by decide)

private def prefixPoints_91 : List (Witness 91000064) :=
  [⟨229632,witnessRule valid_3381 (by decide)⟩,
   ⟨525171,witnessRule valid_1821 (by decide)⟩,
   ⟨542378,witnessRule valid_467 (by decide)⟩,
   ⟨561891,witnessRule valid_1047 (by decide)⟩,
   ⟨683163,witnessRule valid_1126 (by decide)⟩,
   ⟨833211,witnessRule valid_746 (by decide)⟩,
   ⟨928915,witnessRule valid_694 (by decide)⟩,
   ⟨950080,witnessRule valid_347 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_91 : CheckedBlock 64 91 :=
  excludeBlock columns (a := 91000064) (width := 1000000) prefixPoints_91
    (by decide) (by decide) (by decide)

private def prefixPoints_92 : List (Witness 92000064) :=
  [⟨219208,witnessRule valid_2245 (by decide)⟩,
   ⟨275988,witnessRule valid_2155 (by decide)⟩,
   ⟨417739,witnessRule valid_1396 (by decide)⟩,
   ⟨498971,witnessRule valid_1796 (by decide)⟩,
   ⟨595916,witnessRule valid_433 (by decide)⟩,
   ⟨609646,witnessRule valid_373 (by decide)⟩,
   ⟨795808,witnessRule valid_2526 (by decide)⟩,
   ⟨891682,witnessDivisors _ 9 [1,3,9,577,1731,5193,17789,53367,160101,362363,1087089,3261267] (by decide) (by decide) (by decide) (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_92 : CheckedBlock 64 92 :=
  excludeBlock columns (a := 92000064) (width := 1000000) prefixPoints_92
    (by decide) (by decide) (by decide)

private def prefixPoints_93 : List (Witness 93000064) :=
  [⟨49363,witnessDivisors _ 1 [1,7057,4751493767,33531291513719] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨256451,witnessRule valid_926 (by decide)⟩,
   ⟨340595,witnessRule valid_1779 (by decide)⟩,
   ⟨469523,witnessDivisors _ 2 [1,2,17033,34066,988748323] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨574195,witnessRule valid_706 (by decide)⟩,
   ⟨634684,witnessRule valid_2778 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_93 : CheckedBlock 64 93 :=
  excludeBlock columns (a := 93000064) (width := 1000000) prefixPoints_93
    (by decide) (by decide) (by decide)

private def prefixPoints_94 : List (Witness 94000064) :=
  [⟨63878,witnessRule valid_607 (by decide)⟩,
   ⟨262998,witnessRule valid_3378 (by decide)⟩,
   ⟨321648,witnessRule valid_3284 (by decide)⟩,
   ⟨864475,witnessRule valid_1021 (by decide)⟩,
   ⟨876132,witnessRule valid_379 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_94 : CheckedBlock 64 94 :=
  excludeBlock columns (a := 94000064) (width := 1000000) prefixPoints_94
    (by decide) (by decide) (by decide)

private def prefixPoints_95 : List (Witness 95000064) :=
  [⟨195539,witnessRule valid_766 (by decide)⟩,
   ⟨372912,witnessRule valid_1318 (by decide)⟩,
   ⟨463788,witnessRule valid_1588 (by decide)⟩,
   ⟨521656,witnessRule valid_706 (by decide)⟩,
   ⟨670955,witnessRule valid_1765 (by decide)⟩,
   ⟨699107,witnessRule valid_2356 (by decide)⟩,
   ⟨702771,witnessRule valid_1293 (by decide)⟩,
   ⟨752386,witnessRule valid_1684 (by decide)⟩,
   ⟨783076,witnessDivisors _ 2 [1,2,4903,9806,3519927833] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨827004,witnessRule valid_2406 (by decide)⟩,
   ⟨849574,witnessRule valid_3303 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_95 : CheckedBlock 64 95 :=
  excludeBlock columns (a := 95000064) (width := 1000000) prefixPoints_95
    (by decide) (by decide) (by decide)

private def prefixPoints_96 : List (Witness 96000064) :=
  [⟨21971,witnessRule valid_1942 (by decide)⟩,
   ⟨355886,witnessRule valid_848 (by decide)⟩,
   ⟨614784,witnessRule valid_2978 (by decide)⟩,
   ⟨739547,witnessRule valid_866 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_96 : CheckedBlock 64 96 :=
  excludeBlock columns (a := 96000064) (width := 1000000) prefixPoints_96
    (by decide) (by decide) (by decide)

private def prefixPoints_97 : List (Witness 97000064) :=
  [⟨505408,witnessRule valid_2254 (by decide)⟩,
   ⟨541372,witnessDivisors _ 3 [1,3,2011,6033,5826294029,17478882087] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨709171,witnessRule valid_1238 (by decide)⟩,
   ⟨747488,witnessDivisors _ 2 [1,2,4363,8726,61553] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨766716,witnessRule valid_1765 (by decide)⟩,
   ⟨790396,witnessRule valid_3138 (by decide)⟩,
   ⟨972163,witnessDivisors _ 10 [1,2,5,10,1129,2258,2749,5498,5645,11290,13745,27490,1137551] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨997286,witnessRule valid_818 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_97 : CheckedBlock 64 97 :=
  excludeBlock columns (a := 97000064) (width := 1000000) prefixPoints_97
    (by decide) (by decide) (by decide)

private def prefixPoints_98 : List (Witness 98000064) :=
  [⟨851,witnessRule valid_866 (by decide)⟩,
   ⟨22854,witnessRule valid_2118 (by decide)⟩,
   ⟨58155,witnessRule valid_1923 (by decide)⟩,
   ⟨59620,witnessRule valid_2775 (by decide)⟩,
   ⟨130334,witnessRule valid_3265 (by decide)⟩,
   ⟨424131,witnessRule valid_1149 (by decide)⟩,
   ⟨447067,witnessRule valid_2402 (by decide)⟩,
   ⟨501116,witnessRule valid_487 (by decide)⟩,
   ⟨616630,witnessRule valid_2254 (by decide)⟩,
   ⟨634724,witnessRule valid_2238 (by decide)⟩,
   ⟨792003,witnessDivisors _ 4 [1,2,4,5701,11402,22804,1561160729] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨896195,witnessDivisors _ 1 [1,5077,18917,371071] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨925538,witnessRule valid_848 (by decide)⟩,
   ⟨990835,witnessRule valid_1031 (by decide)⟩,
   ⟨997192,witnessRule valid_2514 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_98 : CheckedBlock 64 98 :=
  excludeBlock columns (a := 98000064) (width := 1000000) prefixPoints_98
    (by decide) (by decide) (by decide)

private def prefixPoints_99 : List (Witness 99000064) :=
  [⟨60571,witnessRule valid_2735 (by decide)⟩,
   ⟨118955,witnessRule valid_898 (by decide)⟩,
   ⟨223616,witnessRule valid_976 (by decide)⟩,
   ⟨297608,witnessRule valid_443 (by decide)⟩,
   ⟨322130,witnessRule valid_1689 (by decide)⟩,
   ⟨397406,witnessDivisors _ 3 [1,3,7229,21687,1651628731,4954886193] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨523796,witnessRule valid_718 (by decide)⟩,
   ⟨822474,witnessRule valid_587 (by decide)⟩,
   ⟨865283,witnessDivisors _ 2 [1,2,64871,129742,277377229] (by decide) (by decide) (by decide) (by decide)⟩,
   ⟨873378,witnessRule valid_1772 (by decide)⟩,
   ⟨959939,witnessRule valid_3790 (by decide)⟩]

set_option maxRecDepth 8192 in
private theorem prefixBlock_99 : CheckedBlock 64 99 :=
  excludeBlock columns (a := 99000064) (width := 1000000) prefixPoints_99
    (by decide) (by decide) (by decide)

private theorem prefixTable : ∀ x : ℕ, 0 ≤ x → x < 100 → CheckedBlock 64 x :=
  joinChecked
    (joinChecked
      (joinChecked
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 0 prefixBlock_0)
              (joinChecked
                (singleChecked 1 prefixBlock_1)
                (singleChecked 2 prefixBlock_2)))
            (joinChecked
              (singleChecked 3 prefixBlock_3)
              (joinChecked
                (singleChecked 4 prefixBlock_4)
                (singleChecked 5 prefixBlock_5))))
          (joinChecked
            (joinChecked
              (singleChecked 6 prefixBlock_6)
              (joinChecked
                (singleChecked 7 prefixBlock_7)
                (singleChecked 8 prefixBlock_8)))
            (joinChecked
              (singleChecked 9 prefixBlock_9)
              (joinChecked
                (singleChecked 10 prefixBlock_10)
                (singleChecked 11 prefixBlock_11)))))
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 12 prefixBlock_12)
              (joinChecked
                (singleChecked 13 prefixBlock_13)
                (singleChecked 14 prefixBlock_14)))
            (joinChecked
              (singleChecked 15 prefixBlock_15)
              (joinChecked
                (singleChecked 16 prefixBlock_16)
                (singleChecked 17 prefixBlock_17))))
          (joinChecked
            (joinChecked
              (singleChecked 18 prefixBlock_18)
              (joinChecked
                (singleChecked 19 prefixBlock_19)
                (singleChecked 20 prefixBlock_20)))
            (joinChecked
              (joinChecked
                (singleChecked 21 prefixBlock_21)
                (singleChecked 22 prefixBlock_22))
              (joinChecked
                (singleChecked 23 prefixBlock_23)
                (singleChecked 24 prefixBlock_24))))))
      (joinChecked
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 25 prefixBlock_25)
              (joinChecked
                (singleChecked 26 prefixBlock_26)
                (singleChecked 27 prefixBlock_27)))
            (joinChecked
              (singleChecked 28 prefixBlock_28)
              (joinChecked
                (singleChecked 29 prefixBlock_29)
                (singleChecked 30 prefixBlock_30))))
          (joinChecked
            (joinChecked
              (singleChecked 31 prefixBlock_31)
              (joinChecked
                (singleChecked 32 prefixBlock_32)
                (singleChecked 33 prefixBlock_33)))
            (joinChecked
              (singleChecked 34 prefixBlock_34)
              (joinChecked
                (singleChecked 35 prefixBlock_35)
                (singleChecked 36 prefixBlock_36)))))
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 37 prefixBlock_37)
              (joinChecked
                (singleChecked 38 prefixBlock_38)
                (singleChecked 39 prefixBlock_39)))
            (joinChecked
              (singleChecked 40 prefixBlock_40)
              (joinChecked
                (singleChecked 41 prefixBlock_41)
                (singleChecked 42 prefixBlock_42))))
          (joinChecked
            (joinChecked
              (singleChecked 43 prefixBlock_43)
              (joinChecked
                (singleChecked 44 prefixBlock_44)
                (singleChecked 45 prefixBlock_45)))
            (joinChecked
              (joinChecked
                (singleChecked 46 prefixBlock_46)
                (singleChecked 47 prefixBlock_47))
              (joinChecked
                (singleChecked 48 prefixBlock_48)
                (singleChecked 49 prefixBlock_49)))))))
    (joinChecked
      (joinChecked
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 50 prefixBlock_50)
              (joinChecked
                (singleChecked 51 prefixBlock_51)
                (singleChecked 52 prefixBlock_52)))
            (joinChecked
              (singleChecked 53 prefixBlock_53)
              (joinChecked
                (singleChecked 54 prefixBlock_54)
                (singleChecked 55 prefixBlock_55))))
          (joinChecked
            (joinChecked
              (singleChecked 56 prefixBlock_56)
              (joinChecked
                (singleChecked 57 prefixBlock_57)
                (singleChecked 58 prefixBlock_58)))
            (joinChecked
              (singleChecked 59 prefixBlock_59)
              (joinChecked
                (singleChecked 60 prefixBlock_60)
                (singleChecked 61 prefixBlock_61)))))
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 62 prefixBlock_62)
              (joinChecked
                (singleChecked 63 prefixBlock_63)
                (singleChecked 64 prefixBlock_64)))
            (joinChecked
              (singleChecked 65 prefixBlock_65)
              (joinChecked
                (singleChecked 66 prefixBlock_66)
                (singleChecked 67 prefixBlock_67))))
          (joinChecked
            (joinChecked
              (singleChecked 68 prefixBlock_68)
              (joinChecked
                (singleChecked 69 prefixBlock_69)
                (singleChecked 70 prefixBlock_70)))
            (joinChecked
              (joinChecked
                (singleChecked 71 prefixBlock_71)
                (singleChecked 72 prefixBlock_72))
              (joinChecked
                (singleChecked 73 prefixBlock_73)
                (singleChecked 74 prefixBlock_74))))))
      (joinChecked
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 75 prefixBlock_75)
              (joinChecked
                (singleChecked 76 prefixBlock_76)
                (singleChecked 77 prefixBlock_77)))
            (joinChecked
              (singleChecked 78 prefixBlock_78)
              (joinChecked
                (singleChecked 79 prefixBlock_79)
                (singleChecked 80 prefixBlock_80))))
          (joinChecked
            (joinChecked
              (singleChecked 81 prefixBlock_81)
              (joinChecked
                (singleChecked 82 prefixBlock_82)
                (singleChecked 83 prefixBlock_83)))
            (joinChecked
              (singleChecked 84 prefixBlock_84)
              (joinChecked
                (singleChecked 85 prefixBlock_85)
                (singleChecked 86 prefixBlock_86)))))
        (joinChecked
          (joinChecked
            (joinChecked
              (singleChecked 87 prefixBlock_87)
              (joinChecked
                (singleChecked 88 prefixBlock_88)
                (singleChecked 89 prefixBlock_89)))
            (joinChecked
              (singleChecked 90 prefixBlock_90)
              (joinChecked
                (singleChecked 91 prefixBlock_91)
                (singleChecked 92 prefixBlock_92))))
          (joinChecked
            (joinChecked
              (singleChecked 93 prefixBlock_93)
              (joinChecked
                (singleChecked 94 prefixBlock_94)
                (singleChecked 95 prefixBlock_95)))
            (joinChecked
              (joinChecked
                (singleChecked 96 prefixBlock_96)
                (singleChecked 97 prefixBlock_97))
              (joinChecked
                (singleChecked 98 prefixBlock_98)
                (singleChecked 99 prefixBlock_99)))))))

/-- Every integer in this interval violates the original prize inequality.
The upper endpoint is excluded. -/
theorem originalFailsInHighInterval (n : ℕ) (lo : 360360*10^18 ≤ n)
    (hi : n < 360360*(10^18+100000000)) :
    ¬ (⨆ m : Fin n, (m:ℕ)+σ 0 (m:ℕ)) ≤ n+2 :=
  failureFromBlocks (origin := 1000000000000000000) (count := 100)
    (by decide) lo hi highTable

/-- A continuous exclusion starting immediately after the last known solution, n=24. -/
theorem originalFailsThrough (n : ℕ) (lo : 24 < n) (hi : n ≤ 36036023063039) :
    ¬ (⨆ m : Fin n, (m:ℕ)+σ 0 (m:ℕ)) ≤ n+2 := by
  by_cases small : n ≤ 10000000000
  · exact originalFailsUpTo n lo small
  · exact failureFromBlocks (origin := 64) (count := 100) (by decide)
      (by omega) (by omega) prefixTable

end OMA.Erdos647Obstructions

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R2_H3_R1.H1 :=
  OMA.R_Erdos647_erdos_647_R2_H3_R1.sharpCoprime
