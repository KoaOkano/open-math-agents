import OMAStatements.S_oeis_a113768
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
Let x be the cube root of the current term and y the cube root of the
next term. Their cubes differ by floor(x), while y/x tends to one.
Factoring their differences of cubes and squares shows that y²−x²
tends to 2/3. Cesàro averaging determines x²/n and hence the
asymptotic of the source sequence.
-/

open Filter Topology Finset
open OMA.S_oeis_a113768

namespace CubeRootRecurrence

noncomputable def root (n : ℕ) : ℝ := (value n : ℝ) ^ (1/3:ℝ)
noncomputable def rise (n : ℕ) : ℝ := (⌊root n⌋₊ : ℕ)

lemma growth (n : ℕ) : n+1 ≤ value n := by
  induction n with
  | zero => simp [value]
  | succ n ih =>
    have h1 : 1 ≤ (value n : ℝ) := by exact_mod_cast (show 1 ≤ value n by omega)
    have hf : 1 ≤ ⌊(value n : ℝ) ^ (1/3:ℝ)⌋₊ := by
      exact (Nat.le_floor (by simpa using Real.one_le_rpow h1 (by norm_num : 0 ≤ (1/3:ℝ))))
    change n+1+1 ≤ value n + ⌊(value n : ℝ) ^ (1/3:ℝ)⌋₊
    omega

lemma positive (n : ℕ) : 0 < (value n : ℝ) := by
  exact_mod_cast (show 0 < value n by have := growth n; omega)

lemma root_pos (n : ℕ) : 0 < root n := Real.rpow_pos_of_pos (positive n) _

lemma cube (n : ℕ) : root n ^ 3 = (value n : ℝ) := by
  unfold root
  rw [← Real.rpow_mul_natCast (positive n).le]
  norm_num

lemma next (n : ℕ) : (value (n+1) : ℝ) = (value n : ℝ) + rise n := by
  change ((value n + ⌊root n⌋₊ : ℕ) : ℝ) = _
  push_cast
  rfl

lemma root_large : Tendsto root atTop atTop := by
  have hv : Tendsto value atTop atTop := by
    apply tendsto_atTop_mono (f := id) _ tendsto_id
    intro n
    exact (Nat.le_succ n).trans (growth n)
  exact (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hv)

lemma floor_ratio : Tendsto (fun n => rise n / root n) atTop (𝓝 1) := by
  have lo := (tendsto_const_nhds (x := (1:ℝ))).sub
    (tendsto_inv_atTop_zero.comp root_large)
  rw [sub_zero] at lo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lo tendsto_const_nhds
  · filter_upwards with n
    change 1 - (root n)⁻¹ ≤ rise n / root n
    rw [le_div_iff₀ (root_pos n), sub_mul, inv_mul_cancel₀ (root_pos n).ne', one_mul]
    have hh := Nat.lt_floor_add_one (root n)
    change root n - 1 ≤ (⌊root n⌋₊ : ℝ)
    linarith
  · filter_upwards with n
    apply (div_le_iff₀ (root_pos n)).2
    simpa only [one_mul, rise] using Nat.floor_le (root_pos n).le

lemma term_ratio :
    Tendsto (fun n => (value (n+1) : ℝ) / (value n : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1:ℝ))).add
    (floor_ratio.mul ((tendsto_inv_atTop_zero.comp root_large).pow 2))
  norm_num at h
  apply h.congr
  intro n
  change 1 + (rise n/root n) * (root n^2)⁻¹ = _
  rw [next, ← cube n]
  field_simp [(root_pos n).ne']
  <;> ring

lemma root_ratio : Tendsto (fun n => root (n+1) / root n) atTop (𝓝 1) := by
  have hc := (Real.continuous_rpow_const (by norm_num : 0 ≤ (1/3:ℝ))).tendsto 1
  have h := hc.comp term_ratio
  rw [Real.one_rpow] at h
  apply h.congr
  intro n
  change ((value (n+1) : ℝ) / (value n : ℝ)) ^ (1/3:ℝ) = _
  exact Real.div_rpow (positive (n+1)).le (positive n).le _

lemma squares_step (n : ℕ) : root (n+1)^2 - root n^2 =
    (rise n / root n) * ((root (n+1)/root n)+1) /
      ((root (n+1)/root n)^2 + (root (n+1)/root n) + 1) := by
  have hcube : root (n+1)^3 - root n^3 = rise n := by rw [cube, cube, next]; ring
  rw [← hcube]
  have dpos : 0 < (root (n+1)/root n)^2 + root (n+1)/root n + 1 := by
    have hx := root_pos n
    have hy := root_pos (n+1)
    positivity
  apply (eq_div_iff dpos.ne').2
  field_simp [(root_pos n).ne']
  <;> ring

lemma step_limit : Tendsto (fun n => root (n+1)^2 - root n^2) atTop (𝓝 (2/3)) := by
  have h := (floor_ratio.mul (root_ratio.add_const 1)).div
    (((root_ratio.pow 2).add root_ratio).add_const 1) (by norm_num)
  norm_num at h
  exact h.congr fun n => (squares_step n).symm

lemma square_ratio : Tendsto (fun n : ℕ => root n^2 / ((n:ℝ)+1)) atTop (𝓝 (2/3)) := by
  have havg := step_limit.cesaro
  have hzero := tendsto_const_div_atTop_nhds_zero_nat (root 0^2)
  have h := (havg.add hzero).mul (tendsto_natCast_div_add_atTop (1:ℝ))
  rw [add_zero, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change ((n:ℝ)⁻¹ * (∑ i ∈ Finset.range n, (root (i+1)^2 - root i^2)) +
    root 0^2/(n:ℝ)) * ((n:ℝ)/((n:ℝ)+1)) = _
  rw [Finset.sum_range_sub (fun i => root i^2)]
  field_simp
  <;> ring

end CubeRootRecurrence

open CubeRootRecurrence

theorem OMA.solution : type_of% @OMA.S_oeis_a113768.main := by
  have h := square_ratio.mul square_ratio.sqrt
  apply h.congr
  intro n
  change (root n^2 / ((n:ℝ)+1)) * Real.sqrt (root n^2 / ((n:ℝ)+1)) = _
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (root_pos n).le, ← cube]
  rw [div_mul_div_comm]
  congr 1
