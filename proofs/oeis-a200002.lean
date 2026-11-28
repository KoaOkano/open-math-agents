import OMAStatements.S_oeis_a200002
import Mathlib.Tactic

open OMA.S_oeis_a200002 Filter Topology Finset

namespace CentralBinomialGrowth

private lemma logNonneg (n : ℕ) : 0 ≤ logCoeff n := by unfold logCoeff; positivity

private lemma logUpper (n : ℕ) : logCoeff n ≤ (4:ℝ)^(n^2) := by
  by_cases hz : n=0
  · subst n; norm_num [logCoeff]
  have hn : (1:ℝ) ≤ n := by exact_mod_cast (Nat.pos_of_ne_zero hz)
  have hC : (n.centralBinom:ℝ) ≤ (4:ℝ)^n := by exact_mod_cast Nat.centralBinom_le_four_pow n
  have denom : (1:ℝ) ≤ 2^n*n := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hn
  calc
    logCoeff n ≤ (n.centralBinom:ℝ)^n := div_le_self (by positivity) denom
    _ ≤ ((4:ℝ)^n)^n := pow_le_pow_left₀ (by positivity) hC n
    _ = _ := by rw [←pow_mul,sq]

private lemma logLower (n : ℕ) (hn : 0<n) :
    (4:ℝ)^(n^2) ≤ ((n:ℝ)+1)^(4*n)*logCoeff n := by
  let b : ℝ := (n:ℝ)+1
  have positive : (0:ℝ) < n := by exact_mod_cast hn
  have b1 : (1:ℝ) ≤ b := by dsimp [b]; linarith
  have c : (4:ℝ)^n ≤ (2*n+1)*(n.centralBinom:ℝ) := by
    exact_mod_cast Nat.four_pow_le_two_mul_add_one_mul_central_binom n
  have h2 : (2:ℝ) ≤ b := by dsimp [b]; exact_mod_cast (show 2≤n+1 by omega)
  have square : 2*(n:ℝ)+1 ≤ b^2 := by dsimp [b]; nlinarith [sq_nonneg (n:ℝ)]
  have nle : (n:ℝ) ≤ b^n := by
    apply le_trans (show (n:ℝ)≤b by dsimp [b]; linarith)
    simpa using (pow_le_pow_right₀ b1 (show 1≤n by omega))
  have estimate : (2*(n:ℝ)+1)^n*((2:ℝ)^n*n) ≤ b^(4*n) := by
    calc
      _ ≤ (b^2)^n*(b^n*b^n) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) square n)
          (mul_le_mul (pow_le_pow_left₀ (by norm_num) h2 n) nle (by positivity) (by positivity)) (by positivity) (by positivity)
      _ = _ := by rw [←pow_mul,←pow_add,←pow_add,show 2*n+(n+n)=4*n by omega]
  calc
    _ = ((4:ℝ)^n)^n := by rw [←pow_mul,sq]
    _ ≤ ((2*(n:ℝ)+1)*(n.centralBinom:ℝ))^n := pow_le_pow_left₀ (by positivity) c n
    _ = ((2*(n:ℝ)+1)^n*((2:ℝ)^n*n))*logCoeff n := by
      unfold logCoeff
      rw [mul_pow]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right estimate (logNonneg n)

private lemma listUpper (L : List ℕ) : (L.map logCoeff).prod ≤ (4:ℝ)^(L.sum^2) := by
  induction L with
  | nil => norm_num
  | cons k L ih =>
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    calc
      _ ≤ (4:ℝ)^(k^2)*4^(L.sum^2) :=
        mul_le_mul (logUpper k) ih
          (List.prod_nonneg (fun x hx => by obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact logNonneg i)) (by positivity)
      _ ≤ _ := by
        rw [←pow_add]
        apply pow_le_pow_right₀ (by norm_num)
        nlinarith only [Nat.zero_le (k*L.sum)]

private lemma bounds (n : ℕ) (hn : 0<n) :
    (4:ℝ)^(n^2)/((n:ℝ)+1)^(4*n) ≤ term n ∧ term n ≤ (2:ℝ)^n*4^(n^2) ∧ 0≤term n := by
  classical
  have nonneg (c : Composition n) : 0 ≤ (c.blocks.map logCoeff).prod :=
    List.prod_nonneg (fun x hx => by obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact logNonneg i)
  have single : logCoeff n ≤ term n := by
    let c : Composition n := ⟨[n],by simpa using hn,by simp⟩
    have z := single_le_sum (f:=fun d : Composition n =>
      (d.blocks.map logCoeff).prod/(d.length.factorial:ℝ))
      (fun d _ => div_nonneg (nonneg d) (by positivity)) (mem_univ c)
    simpa [c,Composition.length,term] using z
  refine ⟨?_,?_,(logNonneg n).trans single⟩
  · apply le_trans _ single
    apply (div_le_iff₀ (by positivity)).mpr
    simpa [mul_comm] using logLower n hn
  · have h (c : Composition n) : (c.blocks.map logCoeff).prod/(c.length.factorial:ℝ) ≤ (4:ℝ)^(n^2) := by
      have fact : (1:ℝ) ≤ c.length.factorial := by exact_mod_cast Nat.factorial_pos c.length
      exact (div_le_self (nonneg c) fact).trans (by simpa using listUpper c.blocks)
    calc
      term n ≤ ∑ _c : Composition n, (4:ℝ)^(n^2) := sum_le_sum (fun c _ => h c)
      _ = (2:ℝ)^(n-1)*4^(n^2) := by simp [composition_card]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)

private lemma centralRoot (n : ℕ) (hn : (0:ℝ)<n) :
    ((4:ℝ)^(n^2))^(1/(n:ℝ)^2) = 4 := by
  rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤4)]
  push_cast
  rw [show (n:ℝ)^2*(1/(n:ℝ)^2)=1 by field_simp,Real.rpow_one]

end CentralBinomialGrowth

open CentralBinomialGrowth

theorem OMA.solution : type_of% @OMA.S_oeis_a200002.main := by
  have inv : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have lg : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
  have logSmall : Tendsto (fun n : ℕ => Real.log ((n:ℝ)+1)/(n:ℝ)) atTop (𝓝 0) := by
    have bound : Tendsto (fun n : ℕ => Real.log 2/(n:ℝ)+Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (inv.const_mul (Real.log 2)).add lg
    apply squeeze_zero' _ _ bound
    · exact Eventually.of_forall (fun n => div_nonneg
        (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))) (by positivity))
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have h : (1:ℝ)≤n := by exact_mod_cast hn
      rw [←add_div,←Real.log_mul (by norm_num) (by linarith : (n:ℝ)≠0)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Real.log_le_log (by positivity) (by linarith)

  have low : Tendsto (fun n : ℕ => 4/Real.exp (4*(Real.log ((n:ℝ)+1)/(n:ℝ)))) atTop (𝓝 (4:ℝ)) := by
    have ex := (Real.continuous_exp.tendsto _).comp (logSmall.const_mul 4)
    simpa [Function.comp_def,Pi.div_def] using (tendsto_const_nhds (x:=(4:ℝ))).div ex (Real.exp_pos _).ne'
  have high : Tendsto (fun n : ℕ => (2:ℝ)^(1/(n:ℝ))*4) atTop (𝓝 (4:ℝ)) := by
    have e := (Real.continuous_const_rpow (by norm_num : (2:ℝ)≠0)).continuousAt.tendsto.comp inv
    simpa [Function.comp_def] using e.mul_const (4:ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' low high
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hp : (0:ℝ)<n := by exact_mod_cast hn
    have h := Real.rpow_le_rpow (by positivity) (bounds n hn).1 (by positivity : (0:ℝ)≤1/(n:ℝ)^2)
    rw [Real.div_rpow (by positivity) (by positivity),centralRoot n hp,
      ←Real.rpow_natCast_mul (by positivity)] at h
    have E : ((n:ℝ)+1)^(((4*n:ℕ):ℝ)*(1/(n:ℝ)^2)) = Real.exp (4*(Real.log ((n:ℝ)+1)/(n:ℝ))) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      congr 1
      push_cast
      field_simp
    rwa [E] at h
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hp : (0:ℝ)<n := by exact_mod_cast hn
    obtain ⟨_,hi,h0⟩ := bounds n hn
    have h := Real.rpow_le_rpow h0 hi (by positivity : (0:ℝ)≤1/(n:ℝ)^2)
    rw [Real.mul_rpow (by positivity) (by positivity),centralRoot n hp,
      ←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2)] at h
    rwa [show (n:ℝ)*(1/(n:ℝ)^2)=1/n by field_simp] at h
