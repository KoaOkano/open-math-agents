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


end OMA.Erdos647Obstructions

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R2_H3_R1.H1 :=
  OMA.R_Erdos647_erdos_647_R2_H3_R1.sharpCoprime
