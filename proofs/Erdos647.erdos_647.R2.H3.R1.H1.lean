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


end OMA.Erdos647Obstructions

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R2_H3_R1.H1 :=
  OMA.R_Erdos647_erdos_647_R2_H3_R1.sharpCoprime
