import OMAStatements.S_oeis_a183702

/-!
A legal array is determined by its first row and the successive legal rows.
A legal step joins nonzero rows in distinct rational directions. The zero row
has no successors. The two possible direction multiplicities give a quadratic
recurrence for legal extensions after the first step.
-/

namespace HardinStrips

open OMA.S_oeis_a183702 Finset

private abbrev Row := Fin 2 → Fin 4

private instance (r s : Row) : Decidable (BlockOK r s) := by
  unfold BlockOK
  infer_instance

private def valid {n : ℕ} (r : Row) (x : Fin n → Row) :=
  ∀ i : Fin n, BlockOK ((Fin.cons (α := fun _ => Row) r x) i.castSucc) (x i)

private abbrev Tail (n : ℕ) (r : Row) := {x : Fin n → Row // valid r x}

private theorem valid_cons {n : ℕ} (r s : Row) (x : Fin n → Row) :
    valid r (Fin.cons s x) ↔ BlockOK r s ∧ valid s x := by
  constructor
  · intro h
    exact ⟨h 0, fun i => h i.succ⟩
  · rintro ⟨hr, hx⟩ i
    exact Fin.cases hr (fun j => hx j) i

private def splitTail (n : ℕ) (r : Row) :
    Tail (n+1) r ≃ Σ s : {s : Row // BlockOK r s}, Tail n s.val where
  toFun x := by
    have h : valid r (Fin.cons (x.val 0) (Fin.tail x.val)) := by
      simpa only [Fin.cons_self_tail] using x.property
    have ht := (valid_cons _ _ _).mp h
    exact ⟨⟨x.val 0, ht.1⟩, Fin.tail x.val, ht.2⟩
  invFun x := ⟨Fin.cons x.1.val x.2.val, (valid_cons _ _ _).mpr ⟨x.1.property, x.2.property⟩⟩
  left_inv x := Subtype.ext (Fin.cons_self_tail _)
  right_inv := by
    rintro ⟨⟨s, hs⟩, ⟨x, hx⟩⟩
    rfl

private def splitFirst (n : ℕ) :
    {x : Fin (n+1) → Row // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)} ≃
      Σ r : Row, Tail n r where
  toFun x := ⟨x.val 0, Fin.tail x.val, by
    intro i
    simpa only [Fin.cons_self_tail, Fin.tail] using x.property i⟩
  invFun x := ⟨Fin.cons x.1 x.2.val, fun i => x.2.property i⟩
  left_inv x := Subtype.ext (Fin.cons_self_tail _)
  right_inv := by rintro ⟨r, ⟨x, hx⟩⟩; rfl

private def walk : ℕ → Row → ℕ
  | 0, _ => 1
  | n+1, r => ∑ s : {s : Row // BlockOK r s}, walk n s.val

private theorem tail_count (n : ℕ) (r : Row) : Nat.card (Tail n r) = walk n r := by
  induction n generalizing r with
  | zero =>
    let _ : Unique (Tail 0 r) := {
      default := ⟨Fin.elim0, fun i => i.elim0⟩
      uniq := fun _ => Subtype.ext (Subsingleton.elim _ _) }
    exact Nat.card_unique
  | succ n ih =>
    rw [Nat.card_congr (splitTail n r), Nat.card_sigma]
    exact sum_congr rfl (fun s _ => ih s.val)

private theorem count (n : ℕ) : a n = ∑ r : Row, walk n r := by
  unfold a
  rw [Nat.card_congr (splitFirst n), Nat.card_sigma]
  exact sum_congr rfl (fun r _ => tail_count n r)

private def nonzeroWeight (r : Row) : ℕ := if r 0 = 0 ∧ r 1 = 0 then 0 else 1

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
private theorem first_two : ∀ r : Row, walk 2 r = 11 * walk 1 r + 24 * nonzeroWeight r := by
  decide

private theorem nonzero_next : ∀ r : Row,
    (∑ s : {s : Row // BlockOK r s}, nonzeroWeight s.val) = walk 1 r := by decide

private theorem walk_rec (n : ℕ) (r : Row) :
    walk (n+3) r = 11 * walk (n+2) r + 24 * walk (n+1) r := by
  induction n generalizing r with
  | zero =>
    change (∑ s : {s : Row // BlockOK r s}, walk 2 s.val) =
      11 * (∑ s : {s : Row // BlockOK r s}, walk 1 s.val) + 24 * walk 1 r
    simp only [first_two, sum_add_distrib, ← mul_sum, nonzero_next]
  | succ n ih =>
    change (∑ s : {s : Row // BlockOK r s}, walk (n+3) s.val) =
      11 * (∑ s : {s : Row // BlockOK r s}, walk (n+2) s.val) +
      24 * (∑ s : {s : Row // BlockOK r s}, walk (n+1) s.val)
    simp only [ih, sum_add_distrib, mul_sum]

private theorem count_rec (n : ℕ) : a (n+3) = 11 * a (n+2) + 24 * a (n+1) := by
  simp only [count, walk_rec n, sum_add_distrib, mul_sum]

private def terms : ℕ → ℕ
  | 0 => 192
  | 1 => 2472
  | n+2 => 11 * terms (n+1) + 24 * terms n

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
private theorem term : ∀ n, a (n+1) = terms n
  | 0 => by rw [count]; decide
  | 1 => by rw [count]; decide
  | n+2 => by rw [count_rec n, term (n+1), term n, terms]

open PowerSeries

private def coefficient : ℕ → ℚ
  | 0 => 0
  | n+1 => terms n

private theorem series_eq : PowerSeries.mk coefficient = G := by
  let F : PowerSeries ℚ := PowerSeries.mk coefficient
  change F = _
  unfold G
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp)).2
  rw [show F * (1 - 11*X - 24*X^2) =
      F - C (11 : ℚ) * (F * X^1) - C (24 : ℚ) * (F * X^2) by simp only [map_ofNat]; ring]
  rw [show (24*X*(8+15*X) : PowerSeries ℚ) = C (192 : ℚ) * X^1 + C (360 : ℚ) * X^2 by
    simp only [map_ofNat]; ring]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', F, coeff_mk]
  match n with
  | 0 | 1 | 2 => norm_num [coefficient, terms]
  | k+3 => simp [coefficient, terms]

private noncomputable def closed (n : ℕ) : ℝ :=
  (3/2) * (((11-Real.sqrt 217)/2)^n * (-73+5*Real.sqrt 217) +
    ((11+Real.sqrt 217)/2)^n * (73+5*Real.sqrt 217)) / Real.sqrt 217

private theorem closed_rec (n : ℕ) :
    closed (n+2) = 11*closed (n+1) + 24*closed n := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 217)
  have h₁ : ((11-Real.sqrt 217)/2)^2 = 11*((11-Real.sqrt 217)/2)+24 := by nlinarith
  have h₂ : ((11+Real.sqrt 217)/2)^2 = 11*((11+Real.sqrt 217)/2)+24 := by nlinarith
  unfold closed
  simp only [pow_add, pow_one, h₁, h₂]
  ring

private theorem closed_form : ∀ n, (terms n : ℝ) = closed (n+1)
  | 0 | 1 => by
    have h₀ : Real.sqrt 217 ≠ 0 := by positivity
    have h₂ := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 217)
    have h₃ : (Real.sqrt 217)^3 = 217 * Real.sqrt 217 := by rw [pow_succ, h₂]
    apply (eq_div_iff h₀).2
    norm_num [terms]
    nlinarith
  | n+2 => by
    change (↑(11 * terms (n+1) + 24 * terms n) : ℝ) = closed ((n+1)+2)
    push_cast
    rw [closed_rec, closed_form (n+1), closed_form n]

private theorem rescale (n : ℕ) : closed n =
    3 * (2 : ℝ) ^ ((-1 : ℤ) - n) *
      ((11 - Real.sqrt 217) ^ n * (-73 + 5 * Real.sqrt 217) +
      (11 + Real.sqrt 217) ^ n * (73 + 5 * Real.sqrt 217)) / Real.sqrt 217 := by
  unfold closed
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [zpow_natCast, zpow_one, zpow_neg, div_pow]
  ring

end HardinStrips

open OMA.S_oeis_a183702 HardinStrips

theorem OMA.solution : type_of% @OMA.S_oeis_a183702.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
    exact count_rec k
  · rw [← series_eq]
    ext n
    cases n <;> simp [PowerSeries.coeff_mk, coefficient, term]
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
    rw [term, closed_form, rescale]
