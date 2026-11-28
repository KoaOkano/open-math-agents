import OMAStatements.S_oeis_a184368

/-!
A legal array is determined by its first row and the successive legal rows.
Counting these extensions gives a recurrence for every possible first row.
Summing over the first row gives the recurrence for the full array count.
-/

namespace HardinStrips

open OMA.S_oeis_a184368 Finset

private abbrev Row := Fin 2 → Fin 3

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

private theorem count (n : ℕ) : N n = ∑ r : Row, walk n r := by
  unfold N
  rw [Nat.card_congr (splitFirst n), Nat.card_sigma]
  exact sum_congr rfl (fun r _ => tail_count n r)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
private theorem walk_initial : ∀ r : Row, walk 2 r = 6 * walk 1 r + 9 * walk 0 r := by
  decide

private theorem walk_rec (n : ℕ) (r : Row) :
    walk (n+2) r = 6 * walk (n+1) r + 9 * walk n r := by
  induction n generalizing r with
  | zero => exact walk_initial r
  | succ n ih =>
    change (∑ s : {s : Row // BlockOK r s}, walk (n+2) s.val) =
      6 * (∑ s : {s : Row // BlockOK r s}, walk (n+1) s.val) +
      9 * (∑ s : {s : Row // BlockOK r s}, walk n s.val)
    simp only [ih, sum_add_distrib, mul_sum]

private theorem count_rec (n : ℕ) : N (n+2) = 6 * N (n+1) + 9 * N n := by
  simp only [count, walk_rec n, sum_add_distrib, mul_sum]

private theorem count_zero : N 0 = 9 := by rw [count]; decide
private theorem count_one : N 1 = 63 := by rw [count]; decide

private def terms : ℕ → ℕ
  | 0 => 21
  | 1 => 153
  | n+2 => 6 * terms (n+1) + 9 * terms n

private theorem scaled : ∀ n, N (n+1) = 3 * terms n
  | 0 => count_one
  | 1 => by rw [count_rec 0, count_zero, count_one]; decide
  | n+2 => by
    change N ((n+1)+2) = _
    rw [count_rec, scaled (n+1), scaled n, terms]
    ring

private theorem term (n : ℕ) : a (n+1) = terms n := by
  simp [a, scaled]

open PowerSeries

private def coefficient : ℕ → ℚ
  | 0 => 0
  | n+1 => terms n

private theorem series_eq : PowerSeries.mk coefficient = G := by
  let F : PowerSeries ℚ := PowerSeries.mk coefficient
  change F = _
  unfold G
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp)).2
  rw [show F * (1 - 6*X - 9*X^2) =
      F - C (6 : ℚ) * (F * X^1) - C (9 : ℚ) * (F * X^2) by simp only [map_ofNat]; ring]
  rw [show (3*X*(7+9*X) : PowerSeries ℚ) = C (21 : ℚ) * X^1 + C (27 : ℚ) * X^2 by
    simp only [map_ofNat]; ring]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', F, coeff_mk]
  match n with
  | 0 | 1 | 2 => norm_num [coefficient, terms]
  | k+3 =>
    simp [coefficient, terms]
    <;> ring

private noncomputable def closed (n : ℕ) : ℝ :=
  ((3-3*Real.sqrt 2)^n * (-4+3*Real.sqrt 2) +
    (3*(1+Real.sqrt 2))^n * (4+3*Real.sqrt 2)) / (2*Real.sqrt 2)

private theorem closed_rec (n : ℕ) :
    closed (n+2) = 6*closed (n+1) + 9*closed n := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h₁ : (3-3*Real.sqrt 2)^2 = 6*(3-3*Real.sqrt 2)+9 := by nlinarith
  have h₂ : (3*(1+Real.sqrt 2))^2 = 6*(3*(1+Real.sqrt 2))+9 := by nlinarith
  unfold closed
  simp only [pow_add, pow_one, h₁, h₂]
  ring

private theorem closed_form : ∀ n, (terms n : ℝ) = closed (n+1)
  | 0 | 1 => by
    have h₀ : 2 * Real.sqrt 2 ≠ 0 := by positivity
    have h₂ := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have h₃ : (Real.sqrt 2)^3 = 2 * Real.sqrt 2 := by rw [pow_succ, h₂]
    apply (eq_div_iff h₀).2
    norm_num [terms]
    nlinarith
  | n+2 => by
    change (↑(6 * terms (n+1) + 9 * terms n) : ℝ) = closed ((n+1)+2)
    push_cast
    rw [closed_rec, closed_form (n+1), closed_form n]

end HardinStrips

open OMA.S_oeis_a184368 HardinStrips

theorem OMA.solution : type_of% @OMA.S_oeis_a184368.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
    change a (k+2+1) = 6*a (k+1+1) + 9*a (k+1)
    simp only [term]
    rfl
  · rw [← series_eq]
    ext n
    cases n <;> simp [PowerSeries.coeff_mk, coefficient, term]
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
    rw [term]
    exact closed_form k
