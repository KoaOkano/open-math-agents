import OMAStatements.S_oeis_a195068
import Mathlib.Tactic

open OMA.S_oeis_a195068 Filter Topology Finset

namespace RecursiveCoefficientGrowth

private lemma initial : term 0 = 1 := by rw [term]; simp

-- Assign all remaining degree to the first of the r ordered factors.
private lemma oneChild (j t : ℕ) : (j+1)^t*term t ≤ term (j+1+t) := by
  classical
  let f : Fin (j+1) → Fin (t+1) := fun i => if i=0 then ⟨t,by omega⟩ else 0
  have values (i : Fin (j+1)) : (f i:ℕ) = if i=0 then t else 0 := by
    by_cases e : i=0 <;> simp [f,e]
  have mem : f ∈ allocations t (j+1) := by simp [allocations,values]
  have product : (∏ i, term (f i:ℕ)) = term t := by
    simp only [values,apply_ite term,initial]
    simp
  have lower := single_le_sum (f:=fun g : Fin (j+1) → Fin (t+1) => ∏ i, term (g i:ℕ))
    (fun _ _ => Nat.zero_le _) mem
  rw [product] at lower
  conv_rhs => rw [term]
  rw [dif_neg (by omega)]
  apply le_trans _ (single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (show j<j+1+t by omega)))
  let block (s : ℕ) := ∑ g ∈ allocations s (j+1), ∏ i, term (g i:ℕ)
  change _ ≤ (j+1)^(j+1+t-(j+1))*block (j+1+t-(j+1))
  rw [show j+1+t-(j+1)=t by omega]
  exact Nat.mul_le_mul_left ((j+1)^t) lower

private lemma positive (n : ℕ) : 1 ≤ term n := by
  induction n with
  | zero => simp [initial]
  | succ n ih => exact ih.trans (by simpa [add_comm] using oneChild 0 n)

private lemma lower (n : ℕ) : (3:ℝ)^((n:ℝ)*((n:ℝ)-3)/6) ≤ term n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n<3
    · have hp : (1:ℝ) ≤ term n := by exact_mod_cast positive n
      apply le_trans _ hp
      have hle : (n:ℝ) ≤ 3 := by exact_mod_cast small.le
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
        (show (n:ℝ)*((n:ℝ)-3)/6≤0 by
          exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) (by norm_num))
    · obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le (show 3≤n by omega)
      have h := ih t (by omega)
      have step : (3:ℝ)^t*(term t:ℝ) ≤ term (3+t) := by exact_mod_cast oneChild 2 t
      apply le_trans _ step
      push_cast
      rw [show (3+(t:ℝ))*(3+t-3)/6=(t:ℝ)+t*(t-3)/6 by ring,
        Real.rpow_add (by norm_num : (0:ℝ)<3),Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_left h (by positivity)

private lemma cubeBound (r : ℕ) : r^3 ≤ 3^r := by
  match r with
  | 0 | 1 | 2 => decide
  | k+3 =>
    induction k with
    | zero => decide
    | succ k ih =>
      change (k+4)^3 ≤ 3^(k+3+1)
      rw [pow_succ (3:ℕ) (k+3)]
      nlinarith only [ih,Nat.zero_le k,Nat.zero_le (k^2),Nat.zero_le (k^3)]

private lemma rootCost (r t : ℕ) :
    (r:ℝ)^t*3^((t:ℝ)^2/6) ≤ (3:ℝ)^(((r+t:ℕ):ℝ)^2/6) := by
  have k : (r:ℝ) ≤ 3^((r:ℝ)/3) := by
    apply le_of_pow_le_pow_left₀ (n:=3) (by decide) (by positivity)
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
    rw [show (r:ℝ)/3*((3:ℕ):ℝ)=r by ring,Real.rpow_natCast]
    exact_mod_cast cubeBound r
  calc
    _ ≤ (3^((r:ℝ)/3))^t*3^((t:ℝ)^2/6) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) k t) (by positivity)
    _ = 3^(((r:ℝ)/3)*t+(t:ℝ)^2/6) := by
      rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3),Real.rpow_add (by norm_num : (0:ℝ)<3)]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      nlinarith [sq_nonneg (r:ℝ)]

private noncomputable def envelope (b : ℝ) (m : ℕ) : ℝ :=
  b^(2*m)*3^((m:ℝ)^2/6)

private lemma envelopeMul (b : ℝ) (hb : 0≤b) (i j : ℕ) :
    envelope b i * envelope b j ≤ envelope b (i+j) := by
  unfold envelope
  rw [Nat.mul_add,pow_add]
  push_cast
  calc
    _ = (b^(2*i)*b^(2*j))*3^((i:ℝ)^2/6+(j:ℝ)^2/6) := by
      rw [Real.rpow_add (by norm_num : (0:ℝ)<3)]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_nonneg (show (0:ℝ) ≤ i by positivity) (show (0:ℝ) ≤ j by positivity)]

private lemma upper (n : ℕ) : (term n:ℝ) ≤ envelope ((n:ℝ)+1) n := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases zero : n=0
    · subst n; norm_num [initial,envelope]
    let b : ℝ := (n:ℝ)+1
    have b1 : 1≤b := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have each (j : ℕ) (hj : j∈range n) :
        ((j+1:ℕ):ℝ)^(n-(j+1)) *
          (∑ f ∈ allocations (n-(j+1)) (j+1), ∏ i, (term (f i:ℕ):ℝ)) ≤
          b^(2*n-1)*3^((n:ℝ)^2/6) := by
      let t := n-(j+1)
      have tj : (j+1)+t=n := by dsimp [t]; have := mem_range.mp hj; omega
      have count : ((allocations t (j+1)).card:ℝ) ≤ b^(j+1) := by
        have natCount : (allocations t (j+1)).card ≤ (t+1)^(j+1) := by
          simpa [allocations,Fintype.card_fun] using
            (card_filter_le (s:=(univ : Finset (Fin (j+1) → Fin (t+1)))) (fun f => (∑ i,(f i:ℕ))=t))
        have cardBound : (allocations t (j+1)).card ≤ (n+1)^(j+1) :=
          natCount.trans (Nat.pow_le_pow_left (by omega) _)
        dsimp [b]
        exact_mod_cast cardBound
      have products (f : Fin (j+1) → Fin (t+1)) (hf : f ∈ allocations t (j+1)) :
          (∏ i, (term (f i:ℕ):ℝ)) ≤ envelope b t := by
        have total := (mem_filter.mp hf).2
        have part (s : Finset (Fin (j+1))) :
            (∏ i ∈ s, (term (f i:ℕ):ℝ)) ≤ envelope b (∑ i ∈ s, (f i:ℕ)) := by
          induction s using Finset.induction_on with
          | empty => simp [envelope]
          | @insert x s hx hs =>
            simp only [prod_insert hx,sum_insert hx]
            have lx := (f x).isLt
            have a := ih (f x:ℕ) (by omega)
            have bx : (f x:ℝ)+1 ≤ b := by dsimp [b]; exact_mod_cast (show (f x:ℕ)+1≤n+1 by omega)
            have ax : (term (f x:ℕ):ℝ) ≤ envelope b (f x) := a.trans
              (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) bx _) (by positivity))
            exact (mul_le_mul ax hs (by positivity) (by unfold envelope; positivity)).trans
              (envelopeMul b (by linarith) _ _)
        simpa only [total] using part univ
      have summed := sum_le_sum (s:=allocations t (j+1)) (fun f hf => products f hf)
      simp only [sum_const,nsmul_eq_mul] at summed
      have scaled := (rootCost (j+1) t)
      rw [tj] at scaled
      calc
        _ ≤ ((j+1:ℕ):ℝ)^t * (b^(j+1) * envelope b t) :=
          mul_le_mul_of_nonneg_left (summed.trans (mul_le_mul_of_nonneg_right count (by unfold envelope; positivity))) (by positivity)
        _ = b^(j+1+2*t) * (((j+1:ℕ):ℝ)^t*3^((t:ℝ)^2/6)) := by
          unfold envelope; rw [pow_add]; ring
        _ ≤ _ := mul_le_mul (pow_le_pow_right₀ b1 (by omega)) scaled (by positivity) (by positivity)
    conv_lhs => rw [term]
    rw [dif_neg zero]
    push_cast
    push_cast at each
    calc
      _ ≤ ∑ _j ∈ range n, b^(2*n-1)*3^((n:ℝ)^2/6) := sum_le_sum each
      _ = (n:ℝ)*(b^(2*n-1)*3^((n:ℝ)^2/6)) := by simp
      _ ≤ b*(b^(2*n-1)*3^((n:ℝ)^2/6)) := mul_le_mul_of_nonneg_right (by dsimp [b]; linarith) (by positivity)
      _ = _ := by
        change _ = b^(2*n)*3^((n:ℝ)^2/6)
        calc
          _ = (b^(2*n-1)*b)*3^((n:ℝ)^2/6) := by ring
          _ = _ := by rw [←pow_succ,show 2*n-1+1=2*n by omega]

end RecursiveCoefficientGrowth

open RecursiveCoefficientGrowth

theorem OMA.solution : type_of% @OMA.S_oeis_a195068.main := by
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
  have low : Tendsto (fun n : ℕ => (3:ℝ)^((1:ℝ)/6-(1/2)*(1/(n:ℝ)))) atTop
      (𝓝 ((3:ℝ)^((1:ℝ)/6))) := by
    have e := (tendsto_const_nhds (x:=(1:ℝ)/6)).sub (inv.const_mul ((1:ℝ)/2))
    simpa [Function.comp_def] using
      (Real.continuous_const_rpow (by norm_num : (3:ℝ)≠0)).continuousAt.tendsto.comp e
  have high : Tendsto (fun n : ℕ => Real.exp (2*(Real.log ((n:ℝ)+1)/(n:ℝ)))*3^((1:ℝ)/6))
      atTop (𝓝 ((3:ℝ)^((1:ℝ)/6))) := by
    have e := (Real.continuous_exp.tendsto _).comp (logSmall.const_mul 2)
    simpa [Function.comp_def] using e.mul_const ((3:ℝ)^((1:ℝ)/6))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' low high
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : (0:ℝ)<n := by exact_mod_cast hn
    have h := Real.rpow_le_rpow (by positivity) (lower n) (by positivity : (0:ℝ)≤1/(n:ℝ)^2)
    rw [←Real.rpow_mul (by norm_num : (0:ℝ)≤3)] at h
    have E : (n:ℝ)*((n:ℝ)-3)/6*(1/(n:ℝ)^2)=1/6-(1/2)*(1/(n:ℝ)) := by
      field_simp [hpos.ne']
      <;> ring
    rwa [E] at h
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : (0:ℝ)<n := by exact_mod_cast hn
    have h := Real.rpow_le_rpow (by positivity) (upper n) (by positivity : (0:ℝ)≤1/(n:ℝ)^2)
    unfold envelope at h
    rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by positivity),
      ←Real.rpow_mul (by norm_num : (0:ℝ)≤3)] at h
    have A : (((n:ℝ)+1)^(((2*n:ℕ):ℝ)*(1/(n:ℝ)^2))) =
        Real.exp (2*(Real.log ((n:ℝ)+1)/(n:ℝ))) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      congr 1
      push_cast
      field_simp
      <;> ring
    have B : (n:ℝ)^2/6*(1/(n:ℝ)^2)=1/6 := by field_simp
    rwa [A,B] at h
