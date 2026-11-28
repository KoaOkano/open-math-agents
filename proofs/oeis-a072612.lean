import OMAStatements.S_oeis_a072612

/-!
Choose three disjoint finite sets of large primes so that all but a small
fraction of integers have a prime divisor of exponent one in each set.
Each of those integers has a divisor sum divisible by eight.
Few integers can then be within distance one of a divisor sum. This
contradicts the proposed upper bound for the sum of those distances.
The stronger classical estimate for the range of the divisor-sum function
is discussed by Ford and Pollack in On common values of phi and sigma, I:
https://www.ford126.web.illinois.edu/wwwpapers/common_I.pdf.
-/

namespace DivisorSumDistances

open Finset OMA.S_oeis_a072612

private noncomputable def recip (p : ℕ) : ℝ := (p : ℝ)⁻¹

private lemma recip_nonneg (p : ℕ) : 0 ≤ recip p := by unfold recip; positivity

/-- Discarding finitely many primes still leaves finite sets of arbitrarily
large reciprocal sum. Here a fixed bound suffices. -/
private lemma prime_set (F : Finset ℕ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧ Disjoint S F ∧ 1000 < ∑ p ∈ S, recip p := by
  classical
  by_contra h
  apply not_summable_one_div_on_primes
  apply summable_of_sum_le (c := 1000 + ∑ p ∈ F, recip p)
  · intro p
    exact Set.indicator_nonneg (fun k _ => by positivity) p
  · intro V
    let T := V.filter Nat.Prime
    have hd : Disjoint (T \ F) F := sdiff_disjoint
    have hbound : ∑ p ∈ T \ F, recip p ≤ 1000 := by
      apply le_of_not_gt
      intro hsum
      exact h ⟨T \ F, fun p hp => (mem_filter.mp (mem_sdiff.mp hp).1).2, hd, hsum⟩
    calc
      ∑ p ∈ V, Set.indicator {p : ℕ | Nat.Prime p} (fun p => (1 : ℝ) / p) p
          = ∑ p ∈ T, recip p := by simp [T, sum_filter, Set.indicator, recip, one_div]
      _ ≤ ∑ p ∈ (T \ F) ∪ F, recip p := by
        apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => recip_nonneg p)
        intro p hp
        by_cases hf : p ∈ F <;> simp [hf, hp]
      _ = (∑ p ∈ T \ F, recip p) + ∑ p ∈ F, recip p := sum_union hd
      _ ≤ _ := by linarith

private lemma small_totient {m : ℕ} (hm : 0 < m)
    (hs : 1000 < ∑ p ∈ m.primeFactors, recip p) : 1000 * m.totient < m := by
  have hphi : (m.totient : ℝ) = m * ∏ p ∈ m.primeFactors, (1 - recip p) := by
    unfold recip
    have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors m)
    push_cast at h
    exact h
  have hprod : (∏ p ∈ m.primeFactors, (1 - recip p)) ≤
      Real.exp (-(∑ p ∈ m.primeFactors, recip p)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ h1)
    · intro p _
      linarith [Real.add_one_le_exp (-(recip p))]
  have hexp : 1000 < Real.exp (∑ p ∈ m.primeFactors, recip p) := by
    linarith [Real.add_one_le_exp (∑ p ∈ m.primeFactors, recip p)]
  have hsmall : Real.exp (-(∑ p ∈ m.primeFactors, recip p)) < (1 : ℝ)/1000 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hexp
  have h := mul_lt_mul_of_pos_left (hprod.trans_lt hsmall) (show (0 : ℝ) < m by exact_mod_cast hm)
  rw [← hphi] at h
  exact_mod_cast (show 1000 * (m.totient : ℝ) < m by linarith)

private def modulus (s : Finset ℕ) := ∏ p ∈ s, p

private lemma select_primes (F : Finset ℕ) : ∃ s : Finset ℕ,
    (∀ p ∈ s, p.Prime ∧ 1000 < p) ∧ Disjoint s F ∧ 0 < modulus s ∧
    1000*(modulus s).totient < modulus s := by
  obtain ⟨s, hs, hd, hu⟩ := prime_set (F ∪ range 1001)
  have hm : 0 < modulus s := prod_pos fun p hp => (hs p hp).pos
  refine ⟨s, ?_, hd.mono_right (subset_union_left), hm, small_totient hm ?_⟩
  · intro p hp
    refine ⟨hs p hp, ?_⟩
    by_contra! hh
    exact disjoint_left.mp hd hp (mem_union_right _ (mem_range.mpr (by omega)))
  · apply hu.trans_le
    apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => recip_nonneg p)
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hs p hp, dvd_prod_of_mem id hp, hm.ne'⟩

/-- A prime dividing m exactly once contributes p+1 to its divisor sum. -/
private lemma extract {p m : ℕ} (hp : p.Prime) (hd : p ∣ m) (hs : ¬ p^2 ∣ m) :
    ∃ u, m = p*u ∧ sigma m = (p+1)*sigma u := by
  obtain ⟨u, rfl⟩ := hd
  have hcop : p.Coprime u := hp.coprime_iff_not_dvd.mpr (by
    rintro ⟨v, rfl⟩; exact hs ⟨v, by ring⟩)
  refine ⟨u, rfl, ?_⟩
  unfold sigma
  rw [hcop.sum_divisors_mul, Nat.Prime.divisors hp]
  rw [sum_insert (by simpa only [mem_singleton] using Ne.symm hp.ne_one), sum_singleton, Nat.add_comm 1 p]

private lemma powers_of_two (s : Finset ℕ) (m : ℕ)
    (H : ∀ p ∈ s, p.Prime ∧ 2 < p ∧ p ∣ m ∧ ¬ p^2 ∣ m) : 2^s.card ∣ sigma m := by
  induction s using Finset.induction_on generalizing m with
  | empty => simp
  | @insert p s hp ih =>
    obtain ⟨hprime, hbig, hd, hsq⟩ := H p (mem_insert_self _ _)
    obtain ⟨u, e, he⟩ := extract hprime hd hsq
    have hdiv := ih u (by
      intro q hq
      obtain ⟨hqp, hqb, hqd, hqs⟩ := H q (mem_insert_of_mem hq)
      have hne : q ≠ p := by rintro rfl; exact hp hq
      have hn : ¬ q ∣ p := fun d => hne ((Nat.prime_dvd_prime_iff_eq hqp hprime).mp d)
      have hum : u ∣ m := e ▸ dvd_mul_left _ _
      exact ⟨hqp, hqb, (hqp.dvd_mul.mp (e ▸ hqd)).resolve_left hn, fun d => hqs (d.trans hum)⟩)
    have hev : 2 ∣ p+1 := by
      have := hprime.eq_two_or_odd
      omega
    rw [card_insert_of_notMem hp, pow_succ, he, Nat.mul_comm (p+1)]
    exact Nat.mul_dvd_mul hdiv hev

private def cop (q X : ℕ) := (Icc 1 X).filter (fun m => q.Coprime m)
private def multiples (d X : ℕ) := (Icc 1 X).filter (fun m => d ∣ m)

private lemma cop_count {q X : ℕ} (hq : 0 < q) (hx : q ≤ X)
    (ht : 1000*q.totient < q) : 500*(cop q X).card ≤ X := by
  have eq : Icc 1 X = Ico 1 (1+X) := by ext k; simp; omega
  have hc := Nat.Ico_filter_coprime_le (a := q) 1 X hq.ne'
  change 500*((Icc 1 X).filter (fun m => q.Coprime m)).card ≤ X
  rw [eq]
  have mulbd := Nat.mul_le_mul_right (X/q+1) ht.le
  have divbd := Nat.div_mul_le_self X q
  nlinarith only [hc, mulbd, divbd, hx]

private lemma multiple_count (d X : ℕ) : (multiples d X).card = X/d := by
  rw [← Nat.card_multiples']
  congr 1
  ext k
  simp only [multiples, mem_filter, mem_Icc, mem_range]
  omega

private lemma recip_square_bound (s : Finset ℕ) (hs : ∀ p ∈ s, 1000 < p) :
    ∑ p ∈ s, 1/(p:ℝ)^2 ≤ 2/1000 := by
  let g (k : ℕ) := ((max k 1000 : ℕ) : ℝ)⁻¹
  have anti (k : ℕ) : g (k+1) ≤ g k := by
    apply inv_anti₀
    · exact_mod_cast (show 0 < max k 1000 by omega)
    · exact_mod_cast (show max k 1000 ≤ max (k+1) 1000 by omega)
  let m := s.sup id + 1
  calc
    ∑ p ∈ s, 1/(p:ℝ)^2 ≤ ∑ p ∈ s, 2*(g p-g (p+1)) := by
      apply sum_le_sum
      intro p hp
      have h := hs p hp
      simp only [g, max_eq_left (by omega : 1000 ≤ p), max_eq_left (by omega : 1000 ≤ p+1),
        Nat.cast_add, Nat.cast_one]
      have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      field_simp
      nlinarith only [show (1:ℝ) ≤ p by exact_mod_cast (show 1 ≤ p by omega)]
    _ ≤ ∑ p ∈ range m, 2*(g p-g (p+1)) := by
      apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => mul_nonneg (by norm_num) (sub_nonneg.mpr (anti p)))
      intro p hp
      exact mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hp))
    _ = 2*(g 0-g m) := by rw [← mul_sum, sum_range_sub']
    _ ≤ _ := by
      have h : 0 ≤ g m := by dsimp [g]; positivity
      have z : g 0 = 1/1000 := by norm_num [g]
      rw [z]; linarith

private def squares (s : Finset ℕ) (X : ℕ) := s.biUnion (fun p => multiples (p^2) X)

private lemma square_count (s : Finset ℕ) (hs : ∀ p ∈ s, 1000 < p) (X : ℕ) :
    500*(squares s X).card ≤ X := by
  have hu : (squares s X).card ≤ ∑ p ∈ s, (multiples (p^2) X).card := card_biUnion_le
  have ha : ((squares s X).card : ℝ) ≤ ∑ p ∈ s, ((X:ℝ) * (1/(p:ℝ)^2)) := by
    calc
      _ ≤ ((∑ p ∈ s, (multiples (p^2) X).card : ℕ) : ℝ) := by exact_mod_cast hu
      _ = ∑ p ∈ s, (((X / p^2 : ℕ)) : ℝ) := by simp [multiple_count]
      _ ≤ _ := by
        apply sum_le_sum
        intro p hp
        have pp : (0:ℝ) < (p:ℝ)^2 := by
          exact_mod_cast pow_pos (show 0 < p by have := hs p hp; omega) 2
        rw [mul_one_div]
        apply (le_div_iff₀ pp).mpr
        exact_mod_cast (Nat.div_mul_le_self X (p^2))
  rw [← mul_sum] at ha
  have hb := mul_le_mul_of_nonneg_left (recip_square_bound s hs) (show (0:ℝ) ≤ X by positivity)
  exact_mod_cast (show 500*((squares s X).card : ℝ) ≤ X by linarith)

private def exceptional (X : ℕ) := (Icc 1 X).filter (fun m => ¬ 8 ∣ sigma m)

private lemma exceptional_count (s t u : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 1000 < p) (ht : ∀ p ∈ t, p.Prime ∧ 1000 < p)
    (hu : ∀ p ∈ u, p.Prime ∧ 1000 < p) (hst : Disjoint s t) (hu' : Disjoint (s∪t) u)
    {X : ℕ} (Cs : 500*(cop (modulus s) X).card ≤ X)
    (Ct : 500*(cop (modulus t) X).card ≤ X) (Cu : 500*(cop (modulus u) X).card ≤ X) :
    100*(exceptional X).card ≤ X := by
  let v := (s∪t)∪u
  have hv (p) (hp : p ∈ v) : p.Prime ∧ 1000 < p := by
    rcases mem_union.mp hp with h | h
    · rcases mem_union.mp h with h | h
      · exact hs p h
      · exact ht p h
    · exact hu p h
  have sub : exceptional X ⊆ cop (modulus s) X ∪ cop (modulus t) X ∪ cop (modulus u) X ∪ squares v X := by
    intro m hm
    obtain ⟨hi, he⟩ := mem_filter.mp hm
    by_contra hn
    simp only [mem_union, not_or] at hn
    have find (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 1000 < p)
        (hc : m ∉ cop (modulus S) X) : ∃ p ∈ S, p ∣ m := by
      by_contra! hd
      apply hc
      refine mem_filter.mpr ⟨hi, Nat.Coprime.prod_left (fun p hp => ?_)⟩
      exact (hS p hp).1.coprime_iff_not_dvd.mpr (hd p hp)
    obtain ⟨p, hp, dp⟩ := find s hs hn.1.1.1
    obtain ⟨q, hq, dq⟩ := find t ht hn.1.1.2
    obtain ⟨r, hr, dr⟩ := find u hu hn.1.2
    have hpv : p ∈ v := mem_union_left _ (mem_union_left _ hp)
    have hqv : q ∈ v := mem_union_left _ (mem_union_right _ hq)
    have hrv : r ∈ v := mem_union_right _ hr
    have ns (z) (hz : z ∈ v) : ¬ z^2 ∣ m := fun d => hn.2
      (mem_biUnion.mpr ⟨z, hz, mem_filter.mpr ⟨hi, d⟩⟩)
    have pq : p ≠ q := by rintro rfl; exact disjoint_left.mp hst hp hq
    have pr : p ≠ r := by rintro rfl; exact disjoint_left.mp hu' (mem_union_left _ hp) hr
    have qr : q ≠ r := by rintro rfl; exact disjoint_left.mp hu' (mem_union_right _ hq) hr
    apply he
    have powdiv := powers_of_two {p,q,r} m (by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨(hs _ hp).1, by have := (hs _ hp).2; omega, dp, ns _ hpv⟩
      · exact ⟨(ht _ hq).1, by have := (ht _ hq).2; omega, dq, ns _ hqv⟩
      · exact ⟨(hu _ hr).1, by have := (hu _ hr).2; omega, dr, ns _ hrv⟩)
    simpa [pq, pr, qr] using powdiv
  have bound := card_le_card sub
  have h1 := card_union_le (cop (modulus s) X) (cop (modulus t) X)
  have h2 := card_union_le (cop (modulus s) X ∪ cop (modulus t) X) (cop (modulus u) X)
  have h3 := card_union_le (cop (modulus s) X ∪ cop (modulus t) X ∪ cop (modulus u) X) (squares v X)
  have hvb := square_count v (fun p hp => (hv p hp).2) X
  omega

private lemma hit_witness (n : ℕ) : ∃ m : ℕ, 1 ≤ m ∧
    a n = Int.natAbs ((n:ℤ)-(sigma m:ℤ)) := by
  exact Nat.sInf_mem (s := {d : ℕ | ∃ m : ℕ, 1 ≤ m ∧ d = Int.natAbs ((n:ℤ)-(sigma m:ℤ))})
    ⟨_, 1, by omega, rfl⟩

private lemma le_sigma (m : ℕ) (hm : 1 ≤ m) : m ≤ sigma m := by
  apply single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _)
  exact Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩

private noncomputable def hits (N : ℕ) := (Icc 1 N).filter (fun n => a n ≤ 1)

private lemma few_hits (N : ℕ) :
    (hits N).card ≤ 3*((N+1)/8+(exceptional (N+1)).card) := by
  let V := multiples 8 (N+1) ∪ (exceptional (N+1)).image sigma
  have cv : V.card ≤ (N+1)/8+(exceptional (N+1)).card := by
    have hu := card_union_le (multiples 8 (N+1)) ((exceptional (N+1)).image sigma)
    have hi : ((exceptional (N+1)).image sigma).card ≤ (exceptional (N+1)).card := card_image_le
    rw [multiple_count] at hu
    dsimp [V]
    omega
  let near (v : ℕ) := Icc (v-1) (v+1)
  have sub : hits N ⊆ V.biUnion near := by
    intro n hn
    obtain ⟨hn', hsmall⟩ := mem_filter.mp hn
    obtain ⟨hpos, htop⟩ := mem_Icc.mp hn'
    obtain ⟨m, hm, ha⟩ := hit_witness n
    rw [ha] at hsmall
    have hle := le_sigma m hm
    have upper : sigma m ≤ N+1 := by omega
    have hv : sigma m ∈ V := by
      by_cases h8 : 8 ∣ sigma m
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, upper⟩, h8⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨m, mem_filter.mpr ⟨mem_Icc.mpr ⟨hm, by omega⟩, h8⟩, rfl⟩)
    exact mem_biUnion.mpr ⟨sigma m, hv, mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have h (v : ℕ) : (near v).card ≤ 3 := by simp [near]; omega
  calc
    _ ≤ (V.biUnion near).card := card_le_card sub
    _ ≤ ∑ v ∈ V, (near v).card := card_biUnion_le
    _ ≤ ∑ _v ∈ V, 3 := sum_le_sum (fun v _ => h v)
    _ ≤ _ := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left 3 cv

private lemma total_lower (N : ℕ) : 2*(N-(hits N).card) ≤ S N := by
  let far := (Icc 1 N).filter (fun n => ¬ a n ≤ 1)
  have hc : (hits N).card + far.card = N := by
    simpa [hits, far] using (card_filter_add_card_filter_not (s := Icc 1 N) (p := fun n => a n ≤ 1))
  rw [show N-(hits N).card = far.card by omega]
  calc
    2*far.card = ∑ _k ∈ far, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ k ∈ far, a k := sum_le_sum fun k hk => by have := (mem_filter.mp hk).2; omega
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

/-- The average distance to a divisor sum is eventually at least 11/10. -/
theorem eventual_lower : ∃ n₀ : ℕ, ∀ N : ℕ, n₀ ≤ N → 11*N ≤ 10*S N := by
  obtain ⟨s, hs, _, ps, ts⟩ := select_primes ∅
  obtain ⟨t, ht, hts, pt, tt⟩ := select_primes s
  obtain ⟨u, hu, hus, pu, tu⟩ := select_primes (s∪t)
  refine ⟨modulus s + modulus t + modulus u + 100, ?_⟩
  intro N hN
  have he := exceptional_count s t u hs ht hu hts.symm hus.symm
    (cop_count ps (show modulus s ≤ N+1 by omega) ts)
    (cop_count pt (show modulus t ≤ N+1 by omega) tt)
    (cop_count pu (show modulus u ≤ N+1 by omega) tu)
  have hh := few_hits N
  have hl := total_lower N
  omega

end DivisorSumDistances

open DivisorSumDistances OMA.S_oeis_a072612

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a072612.main) := by
  rintro ⟨n₀, H⟩
  obtain ⟨m₀, hm⟩ := eventual_lower
  let N := max m₀ n₀
  have hl := hm N (le_max_left _ _)
  have lower : N ≤ S N := by omega
  have upper := (H N (le_max_right _ _)).2
  have realLower : (N:ℝ) ≤ S N := by exact_mod_cast lower
  linarith [Real.sqrt_nonneg (N:ℝ)]
