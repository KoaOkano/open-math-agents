import OMAStatements.S_oeis_a294515

/-!
Wolfdieter Lang's decagonal harmonic-mean conjecture fails at `n = 491244`.
The number of terms and the reduced numerator of their reciprocal sum are both
divisible by 19. The latter divisibility is certified by summing modulo `19^5`
after multiplying each reciprocal by `19^4`.
-/

namespace DecagonalCounterexample

open OMA.S_oeis_a294515

private abbrev scale : ℕ := 130321
private abbrev modulus : ℕ := 2476099

private def den (i : ℕ) := (i + 1) * (4 * i + 1)
private def term (i : ℕ) : ℚ := (scale : ℚ) / (den i : ℕ)

-- An unreduced fraction suffices. Keeping both entries small makes it possible
-- to check the half-million-term calculation in the kernel.
private def part (i : ℕ) : ℕ × ℕ :=
  let g := scale.gcd (den i)
  (scale / g, (den i / g) % modulus)

private def plus (u v : ℕ × ℕ) : ℕ × ℕ :=
  ((u.1 * v.2 + u.2 * v.1) % modulus, u.2 * v.2 % modulus)

private def accumulate : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, s => s
  | n + 1, s => accumulate n (plus s (part n))

private def Represents (x : ℚ) (u : ℕ × ℕ) : Prop :=
  ∃ A B : ℕ, 0 < B ∧ x = (A : ℚ) / B ∧
    A ≡ u.1 [MOD modulus] ∧ B ≡ u.2 [MOD modulus]

private theorem part_correct (i : ℕ) : Represents (term i) (part i) := by
  let g := scale.gcd (den i)
  have hd : 0 < den i := by unfold den; positivity
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hd
  have hx : scale / g * g = scale := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have hy : den i / g * g = den i := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  have hb : 0 < den i / g := by
    by_contra! h
    have := Nat.eq_zero_of_le_zero h
    simp [this] at hy
    omega
  refine ⟨scale / g, den i / g, hb, ?_, Nat.ModEq.refl _, (Nat.mod_modEq _ _).symm⟩
  unfold term
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  exact_mod_cast (show scale * (den i / g) = scale / g * den i by
    calc
      _ = (scale / g * g) * (den i / g) := by rw [hx]
      _ = scale / g * (den i / g * g) := by ring
      _ = _ := by rw [hy])

private theorem plus_correct {x y : ℚ} {u v : ℕ × ℕ}
    (hu : Represents x u) (hv : Represents y v) : Represents (x + y) (plus u v) := by
  obtain ⟨A, B, hB, rfl, hA', hB'⟩ := hu
  obtain ⟨C, D, hD, rfl, hC', hD'⟩ := hv
  refine ⟨A * D + B * C, B * D, Nat.mul_pos hB hD, ?_,
    ((hA'.mul hD').add (hB'.mul hC')).trans (Nat.mod_modEq _ _).symm,
    (hB'.mul hD').trans (Nat.mod_modEq _ _).symm⟩
  push_cast
  field_simp

private theorem accumulate_correct (n : ℕ) (x : ℚ) (s : ℕ × ℕ) (hs : Represents x s) :
    Represents (x + ∑ i ∈ Finset.range n, term i) (accumulate n s) := by
  induction n generalizing x s with
  | zero => simpa [accumulate] using hs
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_right_comm x _ _]
    exact ih _ _ (plus_correct hs (part_correct n))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem residues :
    let v := accumulate 491245 (0, 1)
    v.1 = 0 ∧ v.2 % 19 = 10 := by decide +kernel

private theorem scaled_sum (n : ℕ) :
    (scale : ℚ) * V n = ∑ i ∈ Finset.range (n + 1), term i := by
  unfold V
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [term, den, div_eq_mul_inv]

private theorem presentation : ∃ t B : ℕ, ¬19 ∣ B ∧ V 491244 = (19 * t : ℚ) / B := by
  have hs : Represents 0 (0, 1) := ⟨0, 1, by decide, by norm_num, rfl, rfl⟩
  obtain ⟨A, B, hB, hsum, hA', hB'⟩ := accumulate_correct 491245 0 (0, 1) hs
  have hA : modulus ∣ A := Nat.dvd_of_mod_eq_zero (by
    change A % modulus = (accumulate 491245 (0, 1)).1 % modulus at hA'
    simpa only [residues.1, Nat.zero_mod] using hA')
  have hB19 : B % 19 = 10 :=
    Eq.trans (hB'.of_dvd (by decide : 19 ∣ modulus)) residues.2
  obtain ⟨t, ht⟩ := hA
  refine ⟨t, B, fun h => by rw [Nat.mod_eq_zero_of_dvd h] at hB19; contradiction, ?_⟩
  rw [zero_add, ← scaled_sum 491244, ht] at hsum
  push_cast at hsum
  field_simp at hsum ⊢
  linarith only [hsum]

private theorem harmonic_sum (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 (n + 1), (1 : ℚ) / ((k : ℚ) * (4*k-3))) = V n := by
  unfold V
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1 + 1), Finset.sum_range_succ, ih]
    push_cast
    ring_nf

private theorem numerator_multiple : (19 : ℤ) ∣ (V 491244).num := by
  obtain ⟨t, B, hB, hv⟩ := presentation
  have hBn : B ≠ 0 := fun h => hB (h ▸ dvd_zero _)
  obtain ⟨c, h1, h2⟩ := Rat.num_den_mk (q := V 491244) (n := 19 * (t : ℤ))
    (d := (B : ℤ)) (by exact_mod_cast hBn) (by simpa [Rat.divInt_eq_div] using hv)
  have hnc : ¬(19 : ℤ) ∣ c := by
    intro hc
    apply hB
    exact_mod_cast (show (19 : ℤ) ∣ (B : ℤ) by rw [h2]; exact dvd_mul_of_dvd_left hc _)
  have hp : Prime (19 : ℤ) := by norm_num
  apply ((hp.dvd_mul).mp _).resolve_left hnc
  rw [← h1]
  exact dvd_mul_right _ _

private theorem impossible (q : ℚ) (hp : (19 : ℤ) ∣ q.num)
    (heq : (q.den : ℚ) = ((491245 / q : ℚ).num : ℚ) / 491245) : False := by
  let r : ℚ := 491245 / q
  have hn : (491245 : ℤ) * q.den = r.num := by
    have := (eq_div_iff (by norm_num : (491245 : ℚ) ≠ 0)).mp heq
    rw [mul_comm] at this
    exact_mod_cast this
  have hpos : (0 : ℤ) < r.num := by rw [← hn]; positivity
  have hq : q ≠ 0 := by
    intro h
    simp [r, h] at hpos
  have hqn : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hr : r = Rat.divInt (491245 * (q.den : ℤ)) q.num := by
    rw [Rat.divInt_eq_div]
    push_cast
    dsimp [r]
    conv_lhs => rw [← Rat.num_div_den q]
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  obtain ⟨c, h1, h2⟩ := Rat.num_den_mk hqn hr
  rw [hn] at h1
  have hc : c = 1 := (mul_left_inj' (ne_of_gt hpos)).mp (by simpa using h1.symm)
  rw [hc, one_mul] at h2
  have hrd : 19 ∣ r.den := by exact_mod_cast (h2 ▸ hp)
  have hrn : (19 : ℤ) ∣ r.num := by rw [← hn]; exact dvd_mul_of_dvd_left (by decide) _
  exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 19)
    (by simpa using Int.natAbs_dvd_natAbs.mpr hrn) hrd r.reduced

private theorem consequence (h : type_of% @OMA.S_oeis_a294515.main) (n : ℕ) :
    ((V n).den : ℚ) = (((((n+1 : ℕ) : ℚ) / V n).num : ℤ) : ℚ) / ((n+1 : ℕ) : ℚ) := by
  have hh := h n
  unfold a b at hh
  rw [harmonic_sum] at hh
  simpa only [Nat.cast_add, Nat.cast_one] using hh

end DecagonalCounterexample

open OMA.S_oeis_a294515 DecagonalCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a294515.main) := by
  intro h
  exact impossible (V 491244) numerator_multiple (consequence h 491244)
