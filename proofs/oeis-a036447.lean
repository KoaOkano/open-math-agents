import OMAStatements.S_oeis_a036447

/-!
# Growth of the double-and-reverse sequence

Starting at 8671, the outer two digits at each end determine whether doubling
increases the length. In every four steps the length grows twice.
-/

open OMA.S_oeis_a036447

namespace DoubleReverse

private def Valid (w : List ℕ) : Prop := ∀ d ∈ w, d < 10

private def pair (s : ℕ) : List ℕ := [s % 10, s / 10]

private theorem pair_value (s : ℕ) : Nat.ofDigits 10 (pair s) = s := by
  simpa [pair, Nat.ofDigits] using Nat.mod_add_div s 10

private theorem pair_valid {s : ℕ} (hs : s < 100) : Valid (pair s) := by
  intro d hd
  simp [pair] at hd
  rcases hd with rfl | rfl <;> omega

private def Shape (k p s x : ℕ) : Prop :=
  ∃ w : List ℕ, w.length = k ∧ Valid w ∧
    x = Nat.ofDigits 10 (pair s ++ (w ++ pair p))

/-- Doubling the middle digits preserves their width and produces at most one carry. -/
private theorem double_middle (w : List ℕ) (hw : Valid w) (c : ℕ) (hc : c ≤ 1) :
    ∃ v : List ℕ, ∃ e : ℕ, v.length = w.length ∧ Valid v ∧ e ≤ 1 ∧
      2 * Nat.ofDigits 10 w + c = Nat.ofDigits 10 v + 10 ^ w.length * e := by
  induction w generalizing c with
  | nil => exact ⟨[], c, rfl, hw, hc, by simp⟩
  | cons d w ih =>
    have hd : d < 10 := hw _ (by simp)
    obtain ⟨v, e, hv, hvd, he, h⟩ := ih (fun j hj => hw j (by simp [hj]))
      ((2 * d + c) / 10) (by omega)
    refine ⟨(2 * d + c) % 10 :: v, e, by simp [hv], ?_, he, ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · exact hvd j hj
    · simp only [Nat.ofDigits_cons, List.length_cons, pow_succ]
      have hmod := Nat.mod_add_div (2 * d + c) 10
      nlinarith only [h, hmod]

private theorem doubled_word {k p s x : ℕ} (h : Shape k p s x) (hs : s < 100)
    (hp : 0 < p) :
    ∃ v : List ℕ, ∃ e : ℕ, v.length = k ∧ Valid v ∧ e ≤ 1 ∧
      (Nat.digits 10 (2 * x)).reverse = (Nat.digits 10 (2 * p + e)).reverse ++
        (v.reverse ++ (pair ((2 * s) % 100)).reverse) := by
  obtain ⟨w, rfl, hw, rfl⟩ := h
  obtain ⟨v, e, hv, hvd, he, hval⟩ := double_middle w hw ((2 * s) / 100) (by omega)
  refine ⟨v, e, hv, hvd, he, ?_⟩
  let top := Nat.digits 10 (2 * p + e)
  have ht : top ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have good : Valid (pair ((2 * s) % 100) ++ (v ++ top)) := by
    intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact pair_valid (Nat.mod_lt _ (by decide)) _ hj
    rcases List.mem_append.mp hj with hj | hj
    · exact hvd _ hj
    · exact Nat.digits_lt_base (by decide : 1 < 10) hj
  have last : ∀ h : pair ((2 * s) % 100) ++ (v ++ top) ≠ [],
      (pair ((2 * s) % 100) ++ (v ++ top)).getLast h ≠ 0 := by
    intro hh
    rw [List.getLast_append_of_right_ne_nil _ _ (by simp [ht]),
      List.getLast_append_of_right_ne_nil _ _ ht]
    exact Nat.getLast_digit_ne_zero 10 (by omega)
  have hnum : 2 * Nat.ofDigits 10 (pair s ++ (w ++ pair p)) =
      Nat.ofDigits 10 (pair ((2 * s) % 100) ++ (v ++ top)) := by
    simp only [Nat.ofDigits_append, pair_value, show ∀ j, (pair j).length = 2 from fun _ => rfl,
      hv, top, Nat.ofDigits_digits]
    have hmod := Nat.mod_add_div (2 * s) 100
    nlinarith only [hval, hmod]
  rw [hnum, Nat.digits_ofDigits 10 (by decide) _ good last]
  simp [List.reverse_append, List.append_assoc, top]

/-- A trailing pair `71, 84, 94` gives the next leading pair `24, 86, 88` respectively.
A leading pair `24` leaves the width fixed, while `86` and `88` add one digit. -/
private theorem shape_step {k p s x : ℕ} (shape : Shape k p s x)
    (hp : p = 24 ∨ p = 86 ∨ p = 88) (hs : s = 71 ∨ s = 84 ∨ s = 94) :
    ∃ p' s' : ℕ, (if s = 71 then p' = 24 else p' = 86 ∨ p' = 88) ∧
      (if p = 24 then s' = 84 ∨ s' = 94 else s' = 71) ∧
      Shape (k + (if p = 24 then 0 else 1)) p' s'
        (Nat.ofDigits 10 (Nat.digits 10 (2 * x)).reverse) := by
  obtain ⟨v, e, hv, hvd, he, hrev⟩ := doubled_word shape (by omega) (by omega)
  have low : ∃ p' : ℕ, (if s = 71 then p' = 24 else p' = 86 ∨ p' = 88) ∧
      (pair ((2 * s) % 100)).reverse = pair p' := by
    rcases hs with rfl | rfl | rfl
    · exact ⟨24, by decide, rfl⟩
    · exact ⟨86, by decide, rfl⟩
    · exact ⟨88, by decide, rfl⟩
  obtain ⟨p', hp', hl⟩ := low
  have high : ∃ s' : ℕ, ∃ u : List ℕ,
      (if p = 24 then s' = 84 ∨ s' = 94 else s' = 71) ∧
      u.length = (if p = 24 then 0 else 1) ∧ Valid u ∧
      (Nat.digits 10 (2 * p + e)).reverse = pair s' ++ u := by
    have he' : e = 0 ∨ e = 1 := by omega
    rcases hp with rfl | rfl | rfl <;> rcases he' with rfl | rfl
    · exact ⟨84, [], by decide, rfl, by simp [Valid], by decide +kernel⟩
    · exact ⟨94, [], by decide, rfl, by simp [Valid], by decide +kernel⟩
    · exact ⟨71, [2], by decide, rfl, by simp [Valid], by decide +kernel⟩
    · exact ⟨71, [3], by decide, rfl, by simp [Valid], by decide +kernel⟩
    · exact ⟨71, [6], by decide, rfl, by simp [Valid], by decide +kernel⟩
    · exact ⟨71, [7], by decide, rfl, by simp [Valid], by decide +kernel⟩
  obtain ⟨s', u, hs', hu, hud, hh⟩ := high
  refine ⟨p', s', hp', hs', u ++ v.reverse, by simp [hu, hv, Nat.add_comm], ?_, ?_⟩
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hud d hd
    · exact hvd d (List.mem_reverse.mp hd)
  · rw [hrev, hh, hl]
    simp [List.append_assoc]

private def leadingPair (q p : ℕ) : Prop :=
  if q = 1 ∨ q = 2 then p = 24 else p = 86 ∨ p = 88

private def trailingPair (q s : ℕ) : Prop :=
  if q = 0 ∨ q = 1 then s = 71 else s = 84 ∨ s = 94

private def offset (q : ℕ) : ℕ := if q = 1 then 7 else if q = 3 then 9 else 8

/-- The index and the width of the middle block differ by a fixed offset in each phase. -/
private def orbit (n : ℕ) : Prop :=
  ∃ k p s, (leadingPair (n % 4) p ∧ trailingPair (n % 4) s ∧ n = 2 * k + offset (n % 4)) ∧
    Shape k p s (a n)

private theorem orbit_step {n : ℕ} (hn : orbit n) : orbit (n + 1) := by
  obtain ⟨k, p, s, ⟨hp, hs, hlen⟩, hw⟩ := hn
  obtain ⟨p', s', hp', hs', hw'⟩ := shape_step hw
    (by unfold leadingPair at hp; split at hp <;> omega)
    (by unfold trailingPair at hs; split at hs <;> omega)
  refine ⟨_, p', s', ?_, hw'⟩
  have hnext : (n + 1) % 4 = (n % 4 + 1) % 4 := by omega
  have hr : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hr with hr | hr | hr | hr <;>
    simp [hnext, hr, leadingPair, trailingPair, offset] at hp hs hlen ⊢ <;>
    split_ifs at hp' hs' ⊢ <;> omega

private theorem orbit_of_le (n : ℕ) (hn : 8 ≤ n) : orbit n := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨0, 86, 71, by norm_num [leadingPair, trailingPair, offset], [], rfl,
      by simp [Valid], ?_⟩
    decide +kernel
  | succ n _ ih => exact orbit_step ih

private theorem shape_bounds {k p s x : ℕ} (shape : Shape k p s x)
    (hp : 10 ≤ p) (hp' : p < 100) (hs : s < 100) :
    10 ^ (k + 3) ≤ x ∧ x < 10 ^ (k + 4) := by
  obtain ⟨w, rfl, hw, rfl⟩ := shape
  have mid := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 10) hw
  simp only [Nat.ofDigits_append, pair_value, show ∀ j, (pair j).length = 2 from fun _ => rfl,
    pow_add]
  have lo := Nat.mul_le_mul_left (10 ^ w.length) hp
  have hi := Nat.mul_le_mul_left (10 ^ w.length) (show p + 1 ≤ 100 by omega)
  constructor <;> nlinarith only [lo, hi, mid, hs, Nat.zero_le (Nat.ofDigits 10 w), Nat.zero_le s]

private theorem log_bounds (n : ℕ) (hn : 8 ≤ n) : 0 < (a n : ℝ) ∧
    (n : ℝ) * Real.log 10 - 4 * Real.log 10 ≤ 2 * Real.log (a n) ∧
    2 * Real.log (a n) ≤ (n : ℝ) * Real.log 10 + 4 * Real.log 10 := by
  obtain ⟨k, p, s, ⟨hp, hs, hlen⟩, shape⟩ := orbit_of_le n hn
  obtain ⟨lo, hi⟩ := shape_bounds shape
    (by unfold leadingPair at hp; split at hp <;> omega)
    (by unfold leadingPair at hp; split at hp <;> omega)
    (by unfold trailingPair at hs; split at hs <;> omega)
  have hnlo : 2 * k + 7 ≤ n := by unfold offset at hlen; split_ifs at hlen <;> omega
  have hnhi : n ≤ 2 * k + 9 := by unfold offset at hlen; split_ifs at hlen <;> omega
  have nrlo : 2 * (k : ℝ) + 7 ≤ n := by exact_mod_cast hnlo
  have nrhi : (n : ℝ) ≤ 2 * k + 9 := by exact_mod_cast hnhi
  have rlo : (10 : ℝ) ^ (k + 3) ≤ a n := by exact_mod_cast lo
  have rhi : (a n : ℝ) ≤ 10 ^ (k + 4) := by exact_mod_cast hi.le
  have hpos : 0 < (a n : ℝ) := lt_of_lt_of_le (by positivity) rlo
  have llo := Real.log_le_log (by positivity) rlo
  have lhi := Real.log_le_log hpos rhi
  rw [Real.log_pow] at llo lhi
  push_cast at llo lhi
  have ten : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  refine ⟨hpos, ?_, ?_⟩
  · nlinarith only [llo, mul_nonneg (sub_nonneg.mpr nrhi) ten, ten]
  · nlinarith only [lhi, mul_nonneg (sub_nonneg.mpr nrlo) ten, ten]

end DoubleReverse

open Filter Topology

theorem OMA.solution : type_of% @OMA.S_oeis_a036447.main := by
  let L := Real.log 10 / 2
  let C := 2 * Real.log 10
  have hzero : Tendsto (fun n : ℕ => C * (1 / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have lower : Tendsto (fun n : ℕ => L - C * (1 / (n : ℝ))) atTop (𝓝 L) := by
    simpa using (tendsto_const_nhds (x := L)).sub hzero
  have upper : Tendsto (fun n : ℕ => L + C * (1 / (n : ℝ))) atTop (𝓝 L) := by
    simpa using (tendsto_const_nhds (x := L)).add hzero
  have bounds : ∀ᶠ n : ℕ in atTop,
      L - C * (1 / (n : ℝ)) ≤ Real.log (a n) / n ∧
      Real.log (a n) / n ≤ L + C * (1 / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 8] with n hn
    have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    obtain ⟨_, hlo, hhi⟩ := DoubleReverse.log_bounds n hn
    have el : L - C * (1 / (n : ℝ)) = (n * L - C) / n := by field_simp
    have eu : L + C * (1 / (n : ℝ)) = (n * L + C) / n := by field_simp
    rw [el, eu]
    dsimp [L, C]
    constructor <;> apply div_le_div_of_nonneg_right _ hn'.le <;> linarith
  have hl : Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (𝓝 L) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' lower upper
      (bounds.mono fun _ h => h.1) (bounds.mono fun _ h => h.2)
  have hroot : Real.exp L = Real.sqrt 10 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10)]
    dsimp [L]
    congr 1
    ring
  rw [← hroot]
  apply (Real.continuous_exp.continuousAt.tendsto.comp hl).congr'
  filter_upwards [eventually_ge_atTop 8] with n hn
  simp only [Function.comp_apply, Real.rpow_def_of_pos (DoubleReverse.log_bounds n hn).1]
  congr 1
  ring
