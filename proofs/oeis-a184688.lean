import OMAStatements.S_oeis_a184688

/-!
A legal array is determined by its first row and the successive legal rows.
Counting these extensions gives a recurrence for every possible first row.
Summing over the first row gives the recurrence for the full array count.
-/

namespace HardinStrips

open OMA.S_oeis_a184688 Finset

private abbrev Row := Fin 3 → Fin 3

private def BlockOK (r s : Row) : Prop :=
  ∀ j : Fin 2, ¬(s j.succ = r j.succ ∧ s j.succ = s j.castSucc)

private theorem good_iff {n : ℕ} (x : Fin (n+1) → Row) :
    Good x ↔ ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ) := by
  constructor
  · intro h i j
    exact h i.succ i.castSucc j.succ j.castSucc rfl rfl
  · intro h i i' j j' hi hj
    let u : Fin n := ⟨i'.val, by omega⟩
    let v : Fin 2 := ⟨j'.val, by omega⟩
    have hu : u.succ = i := Fin.ext (by change i'.val+1 = i.val; omega)
    have hv : v.succ = j := Fin.ext (by change j'.val+1 = j.val; omega)
    have hu' : u.castSucc = i' := Fin.ext rfl
    have hv' : v.castSucc = j' := Fin.ext rfl
    simpa only [hu, hv, hu', hv'] using h u v

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

private theorem count (n : ℕ) : N (n+1) = ∑ r : Row, walk n r := by
  unfold N
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x => good_iff (n := n) x)),
    Nat.card_congr (splitFirst n), Nat.card_sigma]
  exact sum_congr rfl (fun r _ => tail_count n r)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
private theorem first_two : ∀ r : Row, walk 2 r + 16 * walk 0 r = 22 * walk 1 r := by decide

private theorem walk_rec (n : ℕ) (r : Row) :
    walk (n+2) r + 16 * walk n r = 22 * walk (n+1) r := by
  induction n generalizing r with
  | zero => exact first_two r
  | succ n ih =>
    change (∑ s : {s : Row // BlockOK r s}, walk (n+2) s.val) +
      16 * (∑ s : {s : Row // BlockOK r s}, walk n s.val) =
      22 * (∑ s : {s : Row // BlockOK r s}, walk (n+1) s.val)
    simp only [mul_sum, ← sum_add_distrib, ih]

private theorem count_rec (n : ℕ) : N (n+3) + 16 * N (n+1) = 22 * N (n+2) := by
  rw [count (n+2), count n, count (n+1), mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl (fun r _ => walk_rec n r)

private def terms : ℕ → ℤ
  | 0 => 9
  | 1 => 192
  | n+2 => 22 * terms (n+1) - 16 * terms n

private theorem scaled : ∀ n, (N (n+1) : ℤ) = 3 * terms n
  | 0 => by rw [count]; decide
  | 1 => by rw [count]; decide
  | n+2 => by
    have h : (N (n+3) : ℤ) + 16 * N (n+1) = 22 * N (n+2) := by exact_mod_cast count_rec n
    rw [scaled n, scaled (n+1)] at h
    rw [terms]
    linarith

private theorem term (n : ℕ) : (a (n+1) : ℤ) = terms n := by
  have h := scaled n
  have di : (3 : ℤ) ∣ (N (n+1) : ℤ) := ⟨terms n, h⟩
  have dn : 3 ∣ N (n+1) := by exact_mod_cast di
  have e : (↑(N (n+1) / 3) : ℤ) * 3 = N (n+1) := by exact_mod_cast Nat.div_mul_cancel dn
  unfold a
  linarith

open PowerSeries

private def coefficient : ℕ → ℚ
  | 0 => 0
  | n+1 => terms n

private theorem series_eq : PowerSeries.mk coefficient = G := by
  let F : PowerSeries ℚ := PowerSeries.mk coefficient
  change F = _
  unfold G
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp)).2
  rw [show F * (1 - 22*X + 16*X^2) =
      F - C (22 : ℚ) * (F * X^1) + C (16 : ℚ) * (F * X^2) by simp only [map_ofNat]; ring]
  rw [show (3*X*(3-2*X) : PowerSeries ℚ) =
      C (9 : ℚ) * X^1 - C (6 : ℚ) * X^2 by simp only [map_ofNat]; ring]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', F, coeff_mk]
  match n with
  | 0 | 1 | 2 => norm_num [coefficient, terms]
  | k+3 => simp [coefficient, terms]

private noncomputable def closed (n : ℕ) : ℝ :=
  ((105-13*Real.sqrt 105)*(11-Real.sqrt 105)^n +
    (11+Real.sqrt 105)^n * (105+13*Real.sqrt 105)) / 560

private theorem closed_rec (n : ℕ) :
    closed (n+2) = 22*closed (n+1) - 16*closed n := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 105)
  have h₁ : (11-Real.sqrt 105)^2 = 22*(11-Real.sqrt 105)-16 := by nlinarith
  have h₂ : (11+Real.sqrt 105)^2 = 22*(11+Real.sqrt 105)-16 := by nlinarith
  unfold closed
  simp only [pow_add, pow_one, h₁, h₂]
  ring

private theorem closed_form : ∀ n, (terms n : ℝ) = closed (n+1)
  | 0 | 1 => by
    have h₂ := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 105)
    have h₃ : (Real.sqrt 105)^3 = 105 * Real.sqrt 105 := by rw [pow_succ, h₂]
    unfold closed
    apply (eq_div_iff (by norm_num : (560:ℝ) ≠ 0)).2
    norm_num [terms]
    nlinarith
  | n+2 => by
    change (↑(22 * terms (n+1) - 16 * terms n) : ℝ) = closed ((n+1)+2)
    push_cast
    rw [closed_rec, closed_form (n+1), closed_form n]

end HardinStrips

open OMA.S_oeis_a184688 HardinStrips

theorem OMA.solution : type_of% @OMA.S_oeis_a184688.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
    change (a (k+2+1) : ℤ) = 22 * a (k+1+1) - 16 * a (k+1)
    simp only [term]
    rfl
  · rw [← series_eq]
    ext n
    cases n with
    | zero => simp [PowerSeries.coeff_mk, coefficient]
    | succ n =>
      have h : (a (n+1) : ℚ) = terms n := by exact_mod_cast term n
      simpa only [PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false, coefficient] using h
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
    have h : (a (k+1) : ℝ) = terms k := by exact_mod_cast term k
    exact h.trans (closed_form k)
