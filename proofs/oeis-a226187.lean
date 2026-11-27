import OMAStatements.S_oeis_a226187
import Mathlib.Tactic

open OMA.S_oeis_a226187 Filter Topology

namespace HarmonicThreshold

private lemma spec (n : ℕ) : 0 < firstAbove n ∧ (n:ℝ)/3 < (harmonic (firstAbove n):ℝ) := by
  apply Nat.sInf_mem (s := {k : ℕ | 0 < k ∧ (n:ℝ)/3 < (harmonic k:ℝ)})
  obtain ⟨k,hk⟩ := exists_nat_gt (Real.exp ((n:ℝ)/3))
  refine ⟨k+1, Nat.succ_pos _, ?_⟩
  have h := Real.log_lt_log (Real.exp_pos ((n:ℝ)/3))
    (show Real.exp ((n:ℝ)/3) < ((k+1+1:ℕ):ℝ) by push_cast; linarith)
  rw [Real.log_exp] at h
  exact h.trans_le (log_add_one_le_harmonic (k+1))

private lemma escape : Tendsto firstAbove atTop atTop := by
  have mono : Monotone (fun j : ℕ => (harmonic j:ℝ)) := by
    apply monotone_nat_of_le_succ
    intro j
    rw [harmonic_succ]
    push_cast
    exact le_add_of_nonneg_right (by positivity)
  apply tendsto_atTop.2
  intro b
  obtain ⟨N,hN⟩ := exists_nat_gt (3*(harmonic b:ℝ))
  filter_upwards [eventually_ge_atTop N] with n hn
  by_contra! hb
  have below := mono hb.le
  have above := (spec n).2
  have nn : (N:ℝ) ≤ n := by exact_mod_cast hn
  linarith

private lemma overshoot (n : ℕ) :
    (harmonic (firstAbove n):ℝ) - (n:ℝ)/3 ≤ (firstAbove n:ℝ)⁻¹ := by
  have hp := (spec n).1
  have step : firstAbove n - 1 + 1 = firstAbove n := by omega
  have prev : (harmonic (firstAbove n-1):ℝ) ≤ (n:ℝ)/3 := by
    by_contra! hh
    by_cases hz : firstAbove n - 1 = 0
    · rw [hz,harmonic_zero,Rat.cast_zero] at hh
      linarith [show (0:ℝ)≤n by positivity]
    · have bad : firstAbove n ≤ firstAbove n-1 :=
        Nat.sInf_le (show firstAbove n-1 ∈ {k : ℕ | 0<k ∧ (n:ℝ)/3<(harmonic k:ℝ)}
          from ⟨Nat.pos_of_ne_zero hz,hh⟩)
      omega
  have add := congrArg ((↑) : ℚ → ℝ) (harmonic_succ (firstAbove n-1))
  rw [step] at add
  push_cast at add
  linarith

private lemma centered : Tendsto (fun n : ℕ => Real.log (firstAbove n) - (n:ℝ)/3)
    atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
  have castLimit : Tendsto (fun n : ℕ => (firstAbove n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp escape
  have gap : Tendsto (fun n : ℕ => (harmonic (firstAbove n):ℝ) - (n:ℝ)/3) atTop (𝓝 0) :=
    squeeze_zero (fun n => sub_nonneg.mpr (spec n).2.le) overshoot
      (tendsto_inv_atTop_zero.comp castLimit)
  have h := gap.sub (Real.tendsto_harmonic_sub_log.comp escape)
  rw [zero_sub] at h
  apply h.congr
  intro n
  dsimp only [Function.comp_apply]
  ring

end HarmonicThreshold

open HarmonicThreshold

theorem OMA.solution : type_of% @OMA.S_oeis_a226187.main := by
  have sh := centered.comp (tendsto_add_atTop_nat 1)
  have h := (sh.sub centered).add (tendsto_const_nhds (x := (1:ℝ)/3))
  simp only [sub_self,zero_add] at h
  have logRatio : Tendsto (fun n : ℕ => Real.log (firstAbove (n+1)) -
      Real.log (firstAbove n)) atTop (𝓝 (1/3)) := by
    apply h.congr
    intro n
    dsimp only [Function.comp_apply]
    push_cast
    ring
  apply ((Real.continuous_exp.tendsto _).comp logRatio).congr
  intro n
  dsimp only [Function.comp_apply]
  rw [Real.exp_sub,Real.exp_log (by exact_mod_cast (spec (n+1)).1),
    Real.exp_log (by exact_mod_cast (spec n).1)]
