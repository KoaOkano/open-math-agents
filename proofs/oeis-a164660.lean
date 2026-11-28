import OMAStatements.S_oeis_a164660
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic

open Polynomial Polynomial.Chebyshev OMA.S_oeis_a164660

namespace ChebyshevRows

private lemma monomial_moment (j : ℕ) (b : ℚ) :
    moment (monomial j b) = b / ((j:ℚ)+1) := by
  simp [moment, Polynomial.lsum_apply, Polynomial.sum_monomial_index, div_eq_inv_mul]

private lemma fundamental (P : ℚ[X]) : moment P.derivative = P.eval 1 - P.eval 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ, eval_add]; ring
  | monomial j b =>
    cases j with
    | zero => simp
    | succ j =>
      rw [derivative_monomial_succ, monomial_moment]
      simp [eval_monomial, ne_of_gt (show 0 < (j:ℚ)+1 by positivity)]

private lemma moment_U (j : ℕ) : moment (U ℚ (j:ℤ)) =
    (1-(T ℚ ((j:ℤ)+1)).eval 0)/((j:ℚ)+1) := by
  have h := fundamental (T ℚ ((j:ℤ)+1))
  rw [T_derivative_eq_U, T_eval_one, add_sub_cancel_right] at h
  have hh : (((j:ℤ)+1 : ℤ) : ℚ[X]) * U ℚ (j:ℤ) = ((j:ℚ)+1) • U ℚ (j:ℤ) := by
    simp [Algebra.smul_def]
  rw [hh, map_smul, smul_eq_mul] at h
  exact (eq_div_iff (by positivity : (j:ℚ)+1 ≠ 0)).2 (by linarith)

private lemma recur (j : ℕ) : 2*r (j+2) =
    (1-(T ℚ (((j+3:ℕ):ℤ))).eval 0)/((j:ℚ)+3) -
    (1-(T ℚ (((j+1:ℕ):ℤ))).eval 0)/((j:ℚ)+1) := by
  have h := congrArg (fun Q : ℚ[X] => moment Q) (two_mul_T_eq_U_sub_U ℚ (j:ℤ))
  simp only [two_mul, map_add, map_sub] at h
  have ha := moment_U (j+2)
  have hb := moment_U j
  simp only [r, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at ha ⊢
  convert h.trans (congrArg₂ (fun x y : ℚ => x-y) ha hb) using 1 <;> ring_nf

private lemma at_zero (j : ℕ) : (T ℚ (j:ℤ)).eval 0 =
    if j%4=0 then 1 else if j%4=2 then -1 else 0 := by
  induction j using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more j hj _ =>
    rw [Nat.cast_add, Nat.cast_ofNat, T_add_two]
    simp only [eval_sub, eval_mul, eval_X, mul_zero, zero_mul, zero_sub, hj]
    have hj4 := Nat.mod_lt j (by decide : 0<4)
    interval_cases e : j%4 <;> simp [Nat.add_mod, e]

private lemma first : r 0 = 1 ∧ r 1 = 1/2 := by
  constructor
  · change moment (T ℚ 0) = 1
    rw [T_zero, ← Polynomial.monomial_zero_one, monomial_moment]
    norm_num
  · change moment (T ℚ 1) = 1/2
    rw [T_one, ← Polynomial.monomial_one_one_eq_X, monomial_moment]
    norm_num

private lemma row_formula (n : ℕ) : r n = if n=0 then 1 else
    if n%2=0 then -1 / (((n:ℚ)-1)*((n:ℚ)+1)) else
    if n%4=1 then 1/((n:ℚ)+1) else -1/((n:ℚ)-1) := by
  rcases n with _ | _ | j
  · simpa using first.1
  · norm_num [first.2]
  · have h := recur j
    rw [at_zero, at_zero] at h
    change r (j+2) = _
    have ha : (j:ℚ)+3 ≠ 0 := by positivity
    have hb : (j:ℚ)+1 ≠ 0 := by positivity
    have hj4 := Nat.mod_lt j (by decide : 0<4)
    interval_cases e : j%4
    all_goals
      simp only [Nat.cast_add, Nat.cast_one] at *
      have e2 : j%2 = (j%4)%2 := by omega
      rw [e] at e2
      norm_num [Nat.add_mod, e, e2] at h ⊢
      field_simp [ha,hb] at h ⊢
      nlinarith

private lemma product_formula (n : ℕ) (hn : 0 < n) :
    browneProduct n = (-1:ℤ)^(n / radical n) := by
  unfold browneProduct
  calc
    _ = ∏ k ∈ Finset.Ioc 0 n, (if radical n ∣ k then (-1:ℤ) else 1) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hk0 := (Finset.mem_Ioc.mp hk).1
      have hx : 1 ≤ k^n := pow_pos hk0 n
      have d := Nat.succ_div (a:=k^n-1) (b:=n)
      rw [Nat.sub_add_cancel hx] at d
      have iff : n ∣ k^n ↔ radical n ∣ k :=
        (Nat.dvd_pow_self_iff hn.ne' hk0.ne').trans (Nat.prod_primeFactors_dvd_iff hk0.ne').symm
      by_cases h : radical n ∣ k
      · simp only [if_pos (iff.mpr h)] at d
        rw [if_pos h, d, Nat.cast_add, Nat.cast_one]
        ring
      · have hnot : ¬ n ∣ k^n := fun h' => h (iff.mp h')
        simp only [if_neg hnot, Nat.add_zero] at d
        rw [if_neg h, d]
        ring
    _ = _ := by simp [Finset.prod_ite, Nat.Ioc_filter_dvd_card_eq_div]

private lemma parity_quotient (n : ℕ) (hn : 0 < n) : 2 ∣ n / radical n ↔ 4 ∣ n := by
  have divides : radical n ∣ n := Nat.prod_primeFactors_dvd n
  have mult := Nat.div_mul_cancel divides
  have sf : Squarefree (radical n) := by
    rw [radical, ← Nat.radical_eq_prod_primeFactors]
    exact UniqueFactorizationMonoid.squarefree_radical
  have hfour : ¬ 4 ∣ radical n := (Nat.squarefree_iff_prime_squarefree.mp sf) 2 Nat.prime_two
  by_cases he : 2 ∣ n
  · have hmem : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two,he,hn.ne'⟩
    have hr : 2 ∣ radical n := Finset.dvd_prod_of_mem (fun p : ℕ => p) hmem
    have hr4 : radical n % 4 = 2 := by omega
    have mod4 := congrArg (fun t : ℕ => t%4) mult
    change (n / radical n * radical n)%4 = n%4 at mod4
    rw [Nat.mul_mod, hr4] at mod4
    omega
  · constructor
    · intro h
      exact (he (dvd_trans h (Nat.div_dvd_of_dvd divides))).elim
    · intro h
      exact (he (dvd_trans (by decide : 2 ∣ 4) h)).elim


private lemma value_as_in_source (n : ℕ) (hn : 0 < n) :
    r n = if Even n then -1/(((n:ℚ)-1)*((n:ℚ)+1)) else
      (-1:ℚ)^((n-1)/2)/(2*(2*(((n-1)/4:ℕ):ℚ)+1)) := by
  rw [row_formula, if_neg hn.ne']
  by_cases he : Even n
  · simp [he, Nat.even_iff.mp he]
  · have ho : n%2 = 1 := by
      rw [Nat.even_iff] at he
      omega
    simp only [ho, one_ne_zero, if_false, he]
    rcases (show n%4=1 ∨ n%4=3 by omega) with h | h
    · have s : Even ((n-1)/2) := Nat.even_iff.mpr (by omega)
      have d : 2*(2*(((n-1)/4:ℕ):ℚ)+1) = (n:ℚ)+1 := by
        exact_mod_cast (show 2*(2*((n-1)/4)+1)=n+1 by omega)
      simp [h, s.neg_one_pow, d]
    · have s : Odd ((n-1)/2) := Nat.odd_iff.mpr (by omega)
      have d : 2*(2*(((n-1)/4:ℕ):ℚ)+1) = (n:ℚ)-1 := by
        have h' : 2*(2*(((n-1)/4:ℕ):ℚ)+1)+1=(n:ℚ) := by
          exact_mod_cast (show 2*(2*((n-1)/4)+1)+1=n by omega)
        linarith
      simp [h, s.neg_one_pow, d]

private lemma unit_num (d : ℕ) (hd : 0 < d) : (1/(d:ℚ)).num = 1 := by
  simp [one_div, Int.sign_eq_one_of_pos (show (0:ℤ)<d by exact_mod_cast hd)]

private lemma shifted_num (n : ℕ) (hn : 0<n) :
    (r (n+1)).num = if 4 ∣ n then 1 else -1 := by
  rw [row_formula, if_neg (Nat.succ_ne_zero _)]
  by_cases even : (n+1)%2=0
  · have h : ¬ 4 ∣ n := by omega
    rw [if_pos even, if_neg h]
    have d : (((n+1:ℕ):ℚ)-1)*(((n+1:ℕ):ℚ)+1) = ((n*(n+2):ℕ):ℚ) := by
      push_cast
      ring
    rw [d, neg_div, Rat.num_neg_eq_neg_num, unit_num _ (by positivity)]
  · rw [if_neg even]
    by_cases h : 4 ∣ n
    · have h4 : (n+1)%4=1 := by omega
      rw [if_pos h4, if_pos h]
      have d : ((n+1:ℕ):ℚ)+1 = ((n+2:ℕ):ℚ) := by push_cast; ring
      rw [d, unit_num _ (by omega)]
    · have h4 : (n+1)%4≠1 := by omega
      rw [if_neg h4, if_neg h]
      have d : ((n+1:ℕ):ℚ)-1 = (n:ℚ) := by push_cast; ring
      rw [d, neg_div, Rat.num_neg_eq_neg_num, unit_num _ hn]

end ChebyshevRows

theorem OMA.solution : type_of% @OMA.S_oeis_a164660.main := by
  refine ⟨⟨ChebyshevRows.first.1, ChebyshevRows.value_as_in_source⟩, ?_⟩
  intro n hn
  refine ⟨?_, ChebyshevRows.product_formula n hn⟩
  rw [ChebyshevRows.shifted_num n hn, ChebyshevRows.product_formula n hn]
  by_cases h : 4 ∣ n
  · have e : Even (n/radical n) := even_iff_two_dvd.mpr ((ChebyshevRows.parity_quotient n hn).mpr h)
    simp [h, e.neg_one_pow]
  · have o : Odd (n/radical n) := Nat.odd_iff.mpr (by
      have odd : ¬ 2 ∣ n/radical n := fun e => h ((ChebyshevRows.parity_quotient n hn).mp e)
      omega)
    simp [h, o.neg_one_pow]
