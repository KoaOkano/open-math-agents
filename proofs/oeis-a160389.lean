import OMAStatements.S_oeis_a160389
import Mathlib.Tactic

open OMA.S_oeis_a160389 Filter Topology

namespace HeptagonQuotient

-- The odd and even samples of this recurrence have the two independently
-- prescribed initial triples. Their common sixth-order relation is proved below.
private def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | n+3 => a (n+2)+2*a (n+1)-a n

private def P (x : ℝ) := x^3-x^2-2*x+1

private lemma rho_large : (5:ℝ)/3 < rho := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi
    (show 0 ≤ Real.pi/7 by positivity) (show Real.pi/6 ≤ Real.pi by linarith [Real.pi_pos])
    (show Real.pi/7 < Real.pi/6 by linarith [Real.pi_pos])
  rw [Real.cos_pi_div_six] at h
  have hs : (5:ℝ)/3 < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  unfold rho
  linarith

private lemma rho_root : P rho=0 := by
  let θ := Real.pi/7
  have h := congrArg Real.cos (show 2*(2*θ) = Real.pi-3*θ by dsimp [θ]; ring)
  rw [Real.cos_two_mul, Real.cos_two_mul, Real.cos_pi_sub, Real.cos_three_mul] at h
  have eq : (Real.cos θ+1)*P (2*Real.cos θ)=0 := by unfold P; nlinarith only [h]
  have hh : 5/3 < 2*Real.cos θ := rho_large
  exact (mul_eq_zero.mp eq).resolve_left (by linarith)

-- The two fractional linear transformations generate the other cubic roots.
private lemma other_roots (r : ℝ) (hr : 5/3 < r) (h : P r=0) :
    P ((r-1)/r)=0 ∧ P (1/(1-r))=0 := by
  have nz : r ≠ 0 := by linarith
  have nz' : 1-r ≠ 0 := by linarith
  unfold P at *
  constructor <;> field_simp [nz,nz'] <;> nlinarith only [h]

private noncomputable def weight (x y z : ℝ) := (2-y-z+y*z)/((x-y)*(x-z))

private lemma interpolation (r s t : ℝ) (h₁ : t<s) (h₂ : s<r) :
    weight r s t + weight s t r + weight t r s = 1 ∧
    weight r s t*r + weight s t r*s + weight t r s*t = 1 ∧
    weight r s t*r^2 + weight s t r*s^2 + weight t r s*t^2 = 2 := by
  have h₃ := lt_trans h₁ h₂
  unfold weight
  constructor
  · field_simp [sub_ne_zero.mpr h₁.ne,sub_ne_zero.mpr h₂.ne,sub_ne_zero.mpr h₃.ne,
      sub_ne_zero.mpr h₁.ne',sub_ne_zero.mpr h₂.ne',sub_ne_zero.mpr h₃.ne']
    ring
  constructor <;> field_simp [sub_ne_zero.mpr h₁.ne,sub_ne_zero.mpr h₂.ne,sub_ne_zero.mpr h₃.ne,
      sub_ne_zero.mpr h₁.ne',sub_ne_zero.mpr h₂.ne',sub_ne_zero.mpr h₃.ne'] <;> ring

private lemma powerRec (z : ℝ) (hz : P z=0) (n : ℕ) :
    z^(n+3)=z^(n+2)+2*z^(n+1)-z^n := by
  unfold P at hz
  simp only [pow_succ]
  linear_combination z^n*hz

private lemma expansion (r s t : ℝ) (hr : P r=0) (hs : P s=0) (ht : P t=0)
    (h₁ : t<s) (h₂ : s<r) (n : ℕ) :
    (a n : ℝ) = weight r s t*r^n + weight s t r*s^n + weight t r s*t^n := by
  obtain ⟨i₀,i₁,i₂⟩ := interpolation r s t h₁ h₂
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simpa [a] using i₀.symm
    | 1 => simpa [a] using i₁.symm
    | 2 => simpa [a] using i₂.symm
    | n+3 =>
      have eq : (a (n+3):ℝ)=(a (n+2):ℝ)+2*(a (n+1):ℝ)-(a n:ℝ) := by
        change ((a (n+2)+2*a (n+1)-a n : ℤ):ℝ) = _
        push_cast
        rfl
      rw [eq,ih (n+2) (by omega),ih (n+1) (by omega),ih n (by omega)]
      linear_combination -(weight r s t)*powerRec r hr n -
        (weight s t r)*powerRec s hs n - (weight t r s)*powerRec t ht n

private lemma ratio : Tendsto (fun n : ℕ => (a (n+1):ℝ)/(rho*(a n:ℝ))) atTop (𝓝 1) := by
  let r := rho
  let s := (r-1)/r
  let t := 1/(1-r)
  have hL : 5/3 < r := rho_large
  have hr : 0<r := by linarith
  have h₀ : 0<s := div_pos (by linarith) hr
  have h₁ : s<1 := (div_lt_one hr).mpr (by linarith)
  have h₂ : t<0 := div_neg_of_pos_of_neg one_pos (by linarith)
  have h₃ : -r<t := by
    dsimp [t]
    apply (lt_div_iff_of_neg (by linarith : 1-r<0)).mpr
    nlinarith [mul_pos (show 0 < r-5/3 by linarith) (show 0 < r+2/3 by linarith)]
  have smallS : |s/r|<1 := by rw [abs_div, abs_of_pos h₀, abs_of_pos hr]; exact (div_lt_one hr).mpr (by linarith)
  have smallT : |t/r|<1 := by rw [abs_div, abs_of_neg h₂, abs_of_pos hr]; exact (div_lt_one hr).mpr (by linarith)
  obtain ⟨hs,ht⟩ := other_roots r hL rho_root
  let A := weight r s t
  let B := weight s t r
  let D := weight t r s
  have hA : 0<A := by
    change 0 < (2-s-t+s*t)/((r-s)*(r-t))
    apply div_pos
    · nlinarith [mul_pos (sub_pos.mpr h₁) (show 0<1-t by linarith)]
    · apply mul_pos <;> linarith
  have scaled (n : ℕ) : (a n:ℝ)/r^n=A+B*(s/r)^n+D*(t/r)^n := by
    rw [expansion r s t rho_root hs ht (by linarith) (by linarith),div_pow s r,div_pow t r]
    change (A*r^n+B*s^n+D*t^n)/r^n=A+B*(s^n/r^n)+D*(t^n/r^n)
    field_simp [hr.ne']
  have ls := tendsto_pow_atTop_nhds_zero_of_abs_lt_one smallS
  have lt' := tendsto_pow_atTop_nhds_zero_of_abs_lt_one smallT
  have lim : Tendsto (fun n : ℕ => (a n:ℝ)/r^n) atTop (𝓝 A) := by
    have L : Tendsto (fun n : ℕ => A+B*(s/r)^n+D*(t/r)^n) atTop (𝓝 (A+B*0+D*0)) :=
      (tendsto_const_nhds.add (tendsto_const_nhds.mul ls)).add (tendsto_const_nhds.mul lt')
    simpa only [mul_zero,add_zero] using L.congr (fun n => (scaled n).symm)
  have H := (lim.comp (tendsto_add_atTop_nat 1)).div lim hA.ne'
  rw [div_self hA.ne'] at H
  apply H.congr
  intro n
  change ((a (n+1):ℝ)/r^(n+1))/((a n:ℝ)/r^n) = (a (n+1):ℝ)/(r*(a n:ℝ))
  by_cases ha : (a n:ℝ)=0
  · simp [ha]
  · rw [pow_succ]
    field_simp [ha,hr.ne']

private lemma step (n : ℕ) : a (n+3)=a (n+2)+2*a (n+1)-a n := rfl

private lemma doubleStep (n : ℕ) : a (n+6)=5*a (n+4)-6*a (n+2)+a n := by
  linarith only [step n,step (n+1),step (n+2),step (n+3)]

private lemma samples (m : ℕ) : numerator m=a (2*m+1) ∧ denominator m=a (2*m) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | n+3 =>
      have odd := doubleStep (2*n+1)
      have even := doubleStep (2*n)
      obtain ⟨h₀,g₀⟩ := ih n (by omega)
      obtain ⟨h₁,g₁⟩ := ih (n+1) (by omega)
      obtain ⟨h₂,g₂⟩ := ih (n+2) (by omega)
      change 5*numerator (n+2)-6*numerator (n+1)+numerator n=a (2*(n+3)+1) ∧
        5*denominator (n+2)-6*denominator (n+1)+denominator n=a (2*(n+3))
      rw [h₂,h₁,h₀,g₂,g₁,g₀]
      simp only [Nat.mul_add,Nat.reduceMul,Nat.add_assoc,Nat.reduceAdd,Nat.mul_one] at *
      exact ⟨odd.symm,even.symm⟩

private lemma result :
    Tendsto (fun n : ℕ => (numerator n : ℝ)/(denominator n : ℝ)) atTop (𝓝 rho) := by
  have twice : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop.2 (fun b => (eventually_ge_atTop b).mono (fun n hn => by omega))
  have L : Tendsto (fun n : ℕ => rho*((a (2*n+1):ℝ)/(rho*(a (2*n):ℝ)))) atTop (𝓝 (rho*1)) :=
    tendsto_const_nhds.mul (ratio.comp twice)
  rw [mul_one] at L
  apply L.congr
  intro n
  rw [(samples n).1,(samples n).2]
  have hr : rho ≠ 0 := by linarith [rho_large]
  by_cases zero : (a (2*n):ℝ)=0
  · simp [zero]
  · field_simp [hr,zero]

end HeptagonQuotient

theorem OMA.solution : type_of% @OMA.S_oeis_a160389.main := HeptagonQuotient.result
