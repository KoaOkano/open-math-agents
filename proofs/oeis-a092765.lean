import OMAStatements.S_oeis_a092765

/-!
Peter Bala's supercongruence for closed walks with steps −2, −1, 1, 2.
The step polynomial factors as (1+X)(1+X³). Pairing the factors with indices
i and J−i in each binomial coefficient produces the second power of the
modulus. For p = 2, unpaired middle factors occur together in the two
coefficients and can be paired across them.
Lean proof by KoaOkano, assisted by OpenAI Codex.
-/

namespace A092765Proof

open Finset Polynomial OMA.S_oeis_a092765

private def pairs (n : ℕ) := ((range (n+1)) ×ˢ (range (n+1))).filter fun t => t.1 + 3*t.2 = 2*n

private theorem pairs_mem {n i j : ℕ} : (i,j) ∈ pairs n ↔ i ≤ n ∧ j ≤ n ∧ i+3*j=2*n := by
  simp [pairs, and_assoc]

private theorem binpoly (r n : ℕ) : (1 + X^r : ℕ[X])^n =
    ∑ j ∈ range (n+1), monomial (r*j) (n.choose j) := by
  rw [add_comm,add_pow]; apply sum_congr rfl
  intro j _
  simp only [one_pow, mul_one, ← pow_mul]
  rw [← C_eq_natCast, X_pow_mul_C]
  exact C_mul_X_pow_eq_monomial

private theorem walk_sum (n : ℕ) : a n = ∑ t ∈ pairs n, n.choose t.1 * n.choose t.2 := by
  have e : (1+X+X^3+X^4 : ℕ[X]) = (1+X^1)*(1+X^3) := by ring
  rw [a,e,mul_pow,binpoly,binpoly,Finset.sum_mul]
  simp only [Finset.mul_sum, finsetSum_coeff, monomial_mul_monomial, coeff_monomial, one_mul,
    pairs, Finset.sum_filter, Finset.sum_product]

private def units (p k : ℕ) := (range (p*k)).filter fun i => ¬p ∣ i
private def regular (p k : ℕ) := (units p k).filter fun i => 2*i ≠ p*k

private theorem multiple_indices {p : ℕ} (hp : 0 < p) (k : ℕ) :
    (range (p*k)).filter (fun i => p ∣ i) = (range k).image (p*·) := by
  ext i
  simp only [mem_filter,mem_range,mem_image]
  constructor
  · rintro ⟨hi,t,rfl⟩
    exact ⟨t, (Nat.mul_lt_mul_left hp).mp hi, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨Nat.mul_lt_mul_of_pos_left ht hp,dvd_mul_right ..⟩

private theorem product_split {p : ℕ} (hp : 0 < p) (n k : ℕ) :
    (p*n).descFactorial (p*k) = (p^k * n.descFactorial k) *
      ∏ i ∈ units p k, (p*n-i) := by
  rw [Nat.descFactorial_eq_prod_range, ← Finset.prod_filter_mul_prod_filter_not _ (fun i => p∣i),
    multiple_indices hp, Finset.prod_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hp h)]
  simp only [← Nat.mul_sub, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← Nat.descFactorial_eq_prod_range, units]

private theorem strip {p : ℕ} (hp : 0 < p) (n k : ℕ) :
    (p*n).choose (p*k) * (∏ i ∈ units p k, (p*k-i)) =
    n.choose k * (∏ i ∈ units p k, (p*n-i)) := by
  have h := product_split hp n k
  have hd := product_split hp k k
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at h hd
  simp only [Nat.choose_self, mul_one] at hd
  rw [hd] at h
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (pow_pos hp k) k.factorial_pos)
  convert h using 1 <;> ring

-- A weight that annihilates the error for each pair also annihilates the full product error.
private theorem paired {ι R : Type*} [DecidableEq ι] [CommSemiring R] (s : Finset ι)
    (v : ι → ι) (f g : ι → R) (w : R)
    (closed : ∀ i ∈ s, v i ∈ s) (inv : ∀ i ∈ s, v (v i) = i)
    (away : ∀ i ∈ s, v i ≠ i) (eq : ∀ i ∈ s, w*(f i*f (v i)) = w*(g i*g (v i))) :
    w * ∏ i ∈ s, f i = w * ∏ i ∈ s, g i := by
  classical
  by_cases hn : s.Nonempty
  · obtain ⟨i, hi⟩ := hn
    let j := v i
    have hj := closed i hi
    have hji := away i hi
    have hje : j ∈ s.erase i := mem_erase.mpr ⟨hji,hj⟩
    let t := (s.erase i).erase j
    have sub : t ⊆ s := (erase_subset ..).trans (erase_subset ..)
    have small : t.card < s.card := (card_erase_lt_of_mem hje).trans (card_erase_lt_of_mem hi)
    have hcl (x) (hx : x ∈ t) : v x ∈ t := by
      have hxs := sub hx
      have hs := closed x hxs
      have hx' := mem_erase.mp hx
      have hx'' := mem_erase.mp hx'.2
      apply mem_erase.mpr
      refine ⟨fun e => hx''.1 ((inv x hxs).symm.trans ((congrArg v e).trans (inv i hi))), ?_⟩
      exact mem_erase.mpr ⟨fun e => hx'.1 ((inv x hxs).symm.trans (congrArg v e)), hs⟩
    have ht := paired t v f g w hcl (fun x hx => inv x (sub hx)) (fun x hx => away x (sub hx))
      (fun x hx => eq x (sub hx))
    rw [← mul_prod_erase s f hi, ← mul_prod_erase s g hi,
      ← mul_prod_erase (s.erase i) f hje, ← mul_prod_erase (s.erase i) g hje]
    change w*(f i*(f j*t.prod f)) = w*(g i*(g j*t.prod g))
    calc
      _ = (w*(f i*f j))*t.prod f := by ring
      _ = (w*(g i*g j))*t.prod f := by rw [eq i hi]
      _ = (g i*g j)*(w*t.prod f) := by ring
      _ = _ := by rw [ht]; ring
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
termination_by s.card

private theorem weight_gap {R : Type*} [CommRing R] {n k : ℕ} (hk : k ≤ n) :
    (n.choose k : R) * ((n:R)-k) = (n:R) * (n-1).choose k := by
  rw [← Nat.cast_sub hk]
  cases n with
  | zero => simp at hk; subst k; simp
  | succ n =>
    simpa only [Nat.succ_sub_one, Nat.cast_mul] using
      congrArg (Nat.cast (R := R)) ((Nat.choose_mul_succ_eq n k).symm.trans (Nat.mul_comm ..))

private theorem weight_index {R : Type*} [CommRing R] {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    (n.choose k : R) * k = (n:R) * (n-1).choose (k-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simpa only [Nat.succ_sub_one, Nat.cast_mul] using congrArg (Nat.cast (R := R)) (Nat.add_one_mul_choose_eq n k).symm

private theorem unit_data {p k i : ℕ} (hi : i ∈ units p k) : 0 < i ∧ i < p*k ∧ ¬p∣i := by
  obtain ⟨h1,h2⟩ := mem_filter.mp hi
  exact ⟨Nat.pos_of_ne_zero (fun e => h2 (e ▸ dvd_zero p)),mem_range.mp h1,h2⟩

private theorem regular_mirror {p k i : ℕ} (hi : i ∈ regular p k) : p*k-i ∈ regular p k := by
  obtain ⟨hu,he⟩ := mem_filter.mp hi
  obtain ⟨hi₀,hi₁,hp⟩ := unit_data hu
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, by omega⟩
  intro h
  have := Nat.dvd_sub (dvd_mul_right p k) h
  apply hp
  simpa only [show p*k-(p*k-i)=i by omega] using this

private theorem regular_weight {R : Type*} [CommRing R] {p n k : ℕ} (hk : k ≤ n)
    (nilpotent : ((p:R)*n)^2 = 0) :
    (n.choose k : R) * (∏ i ∈ regular p k, ((p:R)*n-i)) =
      (n.choose k : R) * (∏ i ∈ regular p k, ((p:R)*k-i)) := by
  apply paired _ (fun i => p*k-i) _ _ _ (fun _ => regular_mirror)
  · intro i hi
    have := (unit_data (mem_filter.mp hi).1).2.1
    omega
  · intro i hi
    have := (unit_data (mem_filter.mp hi).1).2.1
    have := (mem_filter.mp hi).2
    omega
  · intro i hi
    have hi' := (unit_data (mem_filter.mp hi).1).2.1
    rw [Nat.cast_sub hi'.le,Nat.cast_mul]
    have hg := weight_gap (R := R) hk
    linear_combination ((p:R)^2*n)*hg + (((n-1).choose k:R))*nilpotent

private abbrev hasMid (p k : ℕ) := p = 2 ∧ k % 2 = 1

private theorem split_mid {R : Type*} [CommMonoid R] {p : ℕ} (hp : p.Prime) (k : ℕ) (f : ℕ → R) :
    (∏ i ∈ units p k, f i) = (∏ i ∈ regular p k, f i) * (if hasMid p k then f k else 1) := by
  classical
  have fix : (units p k).filter (fun i => ¬2*i ≠ p*k) = if hasMid p k then {k} else ∅ := by
    ext i
    by_cases hp2 : p=2
    · subst p
      simp [units,hasMid,mem_filter,mem_range]
      split <;> simp_all <;> omega
    · simp only [hasMid,hp2,false_and,if_false,notMem_empty,iff_false,mem_filter,not_not]
      intro ⟨hu,hi⟩
      have hpi := (unit_data hu).2.2
      have d : p ∣ 2*i := hi ▸ dvd_mul_right p k
      rcases hp.dvd_mul.mp d with h | h
      · exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
      · exact hpi h
  rw [← Finset.prod_filter_mul_prod_filter_not (units p k) (fun i => 2*i ≠ p*k) f,fix]
  by_cases h : hasMid p k
  · simp only [if_pos h, Finset.prod_singleton, regular]
  · simp only [if_neg h, Finset.prod_empty, mul_one, regular]

private def denom (R : Type*) [CommRing R] (p k : ℕ) : R := ∏ i ∈ units p k, ((p:R)*k-i)
private def rest (R : Type*) [CommRing R] (p k : ℕ) : R := ∏ i ∈ regular p k, ((p:R)*k-i)

private theorem cast_units {R : Type*} [CommRing R] {p n k : ℕ} (hk : k ≤ n) :
    ((∏ i ∈ units p k, (p*n-i) : ℕ) : R) = ∏ i ∈ units p k, ((p:R)*n-i) := by
  push_cast
  apply prod_congr rfl
  intro i hi
  rw [Nat.cast_sub (le_trans (unit_data hi).2.1.le (Nat.mul_le_mul_left _ hk)), Nat.cast_mul]

private theorem strip_ring {R : Type*} [CommRing R] {p n k : ℕ} (hp : p.Prime) (hk : k ≤ n)
    (nilpotent : ((p:R)*n)^2 = 0) :
    ((p*n).choose (p*k) : R) * denom R p k =
    (n.choose k:R)*rest R p k*(if hasMid p k then (p:R)*n-k else 1) := by
  have h := congrArg (Nat.cast (R := R)) (strip hp.pos n k)
  simp only [Nat.cast_mul, cast_units (R := R) (p := p) (k := k) le_rfl,
    cast_units (R := R) (p := p) hk] at h
  rw [denom, h, split_mid hp k (fun i => (p:R)*n-i), ← mul_assoc, regular_weight hk nilpotent]
  rfl

private theorem joint_den {R : Type*} [CommRing R] {p n a b : ℕ} (hp : p.Prime)
    (ha : a ≤ n) (hb : b ≤ n) (rel : a+3*b=2*n) (nilpotent : ((p:R)*n)^2 = 0) :
    (((p*n).choose (p*a) : R)*((p*n).choose (p*b) : R)) * (denom R p a * denom R p b) =
      ((n.choose a : R)*(n.choose b : R)) * (denom R p a * denom R p b) := by
  have den (j : ℕ) : denom R p j = rest R p j * (if hasMid p j then (p:R)*j-j else 1) :=
    split_mid hp j _
  have flip : hasMid p a ↔ hasMid p b := by unfold hasMid; omega
  have fixed : ((n.choose a:R)*(n.choose b:R)) *
      ((if hasMid p a then (p:R)*n-a else 1) * (if hasMid p b then (p:R)*n-b else 1)) =
      ((n.choose a:R)*(n.choose b:R)) *
      ((if hasMid p a then (p:R)*a-a else 1) * (if hasMid p b then (p:R)*b-b else 1)) := by
    by_cases h : hasMid p a
    · have h' := flip.mp h
      simp only [if_pos h, if_pos h']
      obtain ⟨rfl,haodd⟩ := h
      have hbodd := h'.2
      have hr : (a:R)+3*b = 2*n := by simpa using congrArg (Nat.cast (R := R)) rel
      have wi := weight_index (R := R) (by omega : n ≠ 0) (by omega : b ≠ 0)
      have q : ((2:R)*n-a)*(2*n-b) = (2*a-a)*(2*b-b) + (2*n)*(2*b) := by
        linear_combination -(2*(n:R))*hr
      have ann : (n.choose b:R)*((2*n)*(2*b))=0 := by
        calc
          _ = 4*(n:R)*((n.choose b:R)*b) := by ring
          _ = ((2:R)*n)^2*(((n-1).choose (b-1)):R) := by rw [wi]; ring
          _ = 0 := by simpa using congrArg (· * (((n-1).choose (b-1)):R)) nilpotent
      push_cast
      rw [q]
      linear_combination (n.choose a : R) * ann
    · simp only [if_neg h, if_neg (fun hb => h (flip.mpr hb))]
  calc
    _ = (((p*n).choose (p*a):R)*denom R p a) * (((p*n).choose (p*b):R)*denom R p b) := by ring
    _ = _ := by
      rw [strip_ring hp ha nilpotent, strip_ring hp hb nilpotent, den a, den b]
      linear_combination (rest R p a * rest R p b) * fixed


private theorem denom_unit {p : ℕ} (hp : p.Prime) (e k : ℕ) :
    IsUnit (denom (ZMod (p^(2*e))) p k) := by
  apply IsUnit.prod_iff.mpr
  intro i hi
  obtain ⟨_,hlt,hnot⟩ := unit_data hi
  have hnu : ¬ p ∣ p*k-i := by
    intro h
    have := Nat.dvd_sub (dvd_mul_right p k) h
    exact hnot (by simpa only [show p*k-(p*k-i)=i by omega] using this)
  rw [← Nat.cast_mul, ← Nat.cast_sub hlt.le,ZMod.isUnit_iff_coprime]
  exact (hp.coprime_iff_not_dvd.mpr hnu).symm.pow_right _

private def timesPair (p : ℕ) (t : ℕ × ℕ) := (p*t.1, p*t.2)

private theorem times_inj {p : ℕ} (hp : 0 < p) : Function.Injective (timesPair p) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ eq
  exact Prod.ext (Nat.eq_of_mul_eq_mul_left hp (congrArg Prod.fst eq))
    (Nat.eq_of_mul_eq_mul_left hp (congrArg Prod.snd eq))

private theorem scaled_pairs {p : ℕ} (hp : 0 < p) (n : ℕ) :
    (pairs (p*n)).filter (fun t => p ∣ t.1 ∧ p ∣ t.2) = (pairs n).image (timesPair p) := by
  ext ⟨a,b⟩
  simp only [mem_filter,pairs_mem,mem_image]
  constructor
  · rintro ⟨⟨ha,hb,rel⟩,⟨i,rfl⟩,j,rfl⟩
    refine ⟨(i,j), pairs_mem.mpr ⟨Nat.le_of_mul_le_mul_left ha hp,Nat.le_of_mul_le_mul_left hb hp,?_⟩,rfl⟩
    apply Nat.eq_of_mul_eq_mul_left hp
    calc
      _ = p*i+3*(p*j) := by ring
      _ = 2*(p*n) := rel
      _ = _ := by ring
  · rintro ⟨⟨i,j⟩,h,eq⟩
    change (p*i,p*j)=(a,b) at eq
    cases eq
    obtain ⟨hi,hj,hr⟩ := pairs_mem.mp h
    refine ⟨⟨Nat.mul_le_mul_left p hi,Nat.mul_le_mul_left p hj,?_⟩,dvd_mul_right ..,dvd_mul_right ..⟩
    calc
      p*i+3*(p*j) = p*(i+3*j) := by ring
      _ = _ := by rw [hr]; ring

private theorem weight_dvd {p e N i : ℕ} (hp : p.Prime) (hN : p^e ∣ N) (hn : 0 < N)
    (hu : ¬p ∣ i) : p^e ∣ N.choose i := by
  have hi : i ≠ 0 := fun h => hu (h ▸ dvd_zero p)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  apply (hp.coprime_iff_not_dvd.mpr hu).pow_left e |>.dvd_of_dvd_mul_right
  rw [← Nat.add_one_mul_choose_eq]
  exact dvd_mul_of_dvd_left hN _

private theorem weight_zero {p e n : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hn : 0 < n)
    (hN : p^e ∣ p*n) {i j : ℕ} (rel : i+3*j=2*(p*n)) (notboth : ¬(p∣i ∧ p∣j)) :
    (((p*n).choose i : ZMod (p^(2*e))) * ((p*n).choose j : ZMod (p^(2*e)))) = 0 := by
  have hs : p ∣ i+3*j := rel ▸ dvd_mul_of_dvd_right (dvd_mul_right p n) 2
  have hiff : p ∣ i ↔ p ∣ j := by
    constructor
    · intro h
      have hy := Nat.dvd_sub hs h
      rw [show i+3*j-i=3*j by omega] at hy
      exact (hp.dvd_mul.mp hy).resolve_left (fun hd => hp3 ((Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left hp.ne_one))
    · intro h
      have hy := Nat.dvd_sub hs (dvd_mul_of_dvd_right h 3)
      simpa using hy
  have hi : ¬p ∣ i := fun h => notboth ⟨h,hiff.mp h⟩
  have hj : ¬p ∣ j := fun h => hi (hiff.mpr h)
  rw [← Nat.cast_mul,ZMod.natCast_eq_zero_iff,two_mul,pow_add]
  exact mul_dvd_mul (weight_dvd hp hN (Nat.mul_pos hp.pos hn) hi) (weight_dvd hp hN (Nat.mul_pos hp.pos hn) hj)

private theorem reduce_row {p e n : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hn : 0 < n)
    (hN : p^e ∣ p*n) : (a (p*n) : ZMod (p^(2*e))) = (a n : ZMod (p^(2*e))) := by
  let R := ZMod (p^(2*e))
  have nilpotent : ((p:R)*n)^2=0 := by
    rw [← Nat.cast_mul,← Nat.cast_pow,ZMod.natCast_eq_zero_iff,Nat.mul_comm 2 e,pow_mul]
    exact pow_dvd_pow_of_dvd hN 2
  let f := fun t : ℕ × ℕ => ((p*n).choose t.1:R)*((p*n).choose t.2:R)
  have trim : ∑ t ∈ pairs (p*n), f t = ∑ t ∈ (pairs (p*n)).filter (fun t => p∣t.1 ∧ p∣t.2), f t := by
    symm
    apply sum_subset (filter_subset ..)
    rintro ⟨i,j⟩ ht hs
    exact weight_zero hp hp3 hn hN (pairs_mem.mp ht).2.2 (fun h => hs (mem_filter.mpr ⟨ht,h⟩))
  simp only [walk_sum,Nat.cast_sum,Nat.cast_mul]
  change (∑ t ∈ pairs (p*n), f t) = _
  rw [trim,scaled_pairs hp.pos,Finset.sum_image (fun _ _ _ _ h => times_inj hp.pos h)]
  apply sum_congr rfl
  rintro ⟨i,j⟩ ht
  obtain ⟨hi,hj,hr⟩ := pairs_mem.mp ht
  apply ((denom_unit hp e i).mul (denom_unit hp e j)).mul_left_inj.mp
  exact joint_den hp hi hj hr nilpotent

end A092765Proof

open A092765Proof OMA.S_oeis_a092765 in
theorem OMA.solution : type_of% @OMA.S_oeis_a092765.main := by
  intro p n k hp hp3 hn hk
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have eq : n*p^(e+1)=p*(n*p^e) := by ring
  rw [eq, Nat.succ_sub_one, ← ZMod.natCast_eq_natCast_iff]
  apply reduce_row hp hp3 (Nat.mul_pos hn (pow_pos hp.pos _))
  rw [← eq]
  exact dvd_mul_left ..
