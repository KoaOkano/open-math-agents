import OMAStatements.S_oeis_a235878

/-!
A legal array is determined by its first row and the successive legal rows.
In a sorted block the median condition forces the first two entries to agree
and the last two entries to agree. Legal neighbors therefore use the same
number of colors. A row using one, two or three colors has respectively
three, two or one possible successors.
-/

namespace HardinStrips

open OMA.S_oeis_a235878 Finset

private abbrev Row := Fin 3 → Fin 3

private instance (r s : Row) : Decidable (BlockOK r s) := by
  unfold BlockOK Med4
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

private def degree (r : Row) : ℕ :=
  if r 0 = r 1 ∧ r 1 = r 2 then 3
  else if r 0 ≠ r 1 ∧ r 1 ≠ r 2 ∧ r 0 ≠ r 2 then 1 else 2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
private theorem neighbors : ∀ r : Row, Fintype.card {s : Row // BlockOK r s} = degree r := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
private theorem same_degree : ∀ r s : Row, BlockOK r s → degree s = degree r := by
  decide

private theorem walk_degree (n : ℕ) (r : Row) : walk n r = degree r ^ n := by
  induction n generalizing r with
  | zero => simp [walk]
  | succ n ih =>
    have eq (s : {s : Row // BlockOK r s}) : walk n s.val = degree r ^ n := by
      rw [ih, same_degree r s.val s.property]
    simp only [walk, eq, sum_const, card_univ, nsmul_eq_mul, neighbors, pow_succ, Nat.mul_comm]
    exact Nat.mul_comm _ _

private theorem row_count (n : ℕ) : a n = 6 + 18 * 2^n + 3 * 3^n := by
  have pieces (r : Row) : degree r ^ n =
      (if degree r = 1 then 1 else 0) +
      (if degree r = 2 then 2^n else 0) +
      (if degree r = 3 then 3^n else 0) := by
    unfold degree
    split <;> (try split) <;> simp_all
  have d₁ : (univ.filter (fun r : Row => degree r = 1)).card = 6 := by decide
  have d₂ : (univ.filter (fun r : Row => degree r = 2)).card = 18 := by decide
  have d₃ : (univ.filter (fun r : Row => degree r = 3)).card = 3 := by decide
  simp only [count, walk_degree, pieces, sum_add_distrib, sum_ite, sum_const_zero,
    add_zero, sum_const, nsmul_eq_mul, d₁, d₂, d₃, mul_one]
  rfl

open PowerSeries

private def coefficient : ℕ → ℚ
  | 0 => 0
  | n+1 => 6 + 18 * 2^(n+1) + 3 * 3^(n+1)

private theorem series_eq : PowerSeries.mk coefficient = G := by
  let F : PowerSeries ℚ := PowerSeries.mk coefficient
  change F = _
  unfold G
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp)).2
  rw [show F * ((1-X)*(1-2*X)*(1-3*X)) =
      F - C (6 : ℚ) * (F * X^1) + C (11 : ℚ) * (F * X^2) -
      C (6 : ℚ) * (F * X^3) by simp only [map_ofNat]; ring]
  rw [show (3*X*(17-67*X+54*X^2) : PowerSeries ℚ) =
      C (51 : ℚ) * X^1 - C (201 : ℚ) * X^2 + C (162 : ℚ) * X^3 by
    simp only [map_ofNat]; ring]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', F, coeff_mk]
  match n with
  | 0 | 1 | 2 | 3 => norm_num [coefficient]
  | k+4 =>
    simp [show k+4-1=k+3 by omega, show k+4-2=k+2 by omega,
      show k+4-3=k+1 by omega, coefficient, pow_add]
    ring

end HardinStrips

open OMA.S_oeis_a235878 HardinStrips

theorem OMA.solution : type_of% @OMA.S_oeis_a235878.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
    simp only [row_count, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    simp only [show k+4-1=k+3 by omega, show k+4-2=k+2 by omega,
      show k+4-3=k+1 by omega, pow_add]
    ring
  · rw [← series_eq]
    ext n
    cases n <;> simp [PowerSeries.coeff_mk, coefficient, row_count]
  · intro n _
    rw [row_count, pow_add]
    ring
