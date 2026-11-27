import OMAStatements.S_oeis_a007018

/-!
For `N = 6m` with `m` coprime to 6, collect the unitary divisors in blocks
`j, 2j, 3j, 6j`, one for each unitary divisor `j` of `m`. Ordinarily
`j + 2j + 3j = 6j`. In the block `j = m`, removing `6m` leaves the
balanced partition `m + 2m = 3m`. Every sequence term from index two
onward is congruent to 6 modulo 36.
-/

namespace SylvesterDivisors

open Finset OMA.S_oeis_a007018

private theorem six_divisors : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide

private theorem unitary_block {m i j : ℕ} (hc : Nat.Coprime 6 m)
    (hi : i ∈ (6 : ℕ).divisors) (hj : j ∈ m.divisors) :
    (i*j).Coprime (6*m / (i*j)) ↔ j.Coprime (m/j) := by
  have hi' := (Nat.mem_divisors.mp hi).1
  have hj' := (Nat.mem_divisors.mp hj).1
  have hip := Nat.pos_of_mem_divisors hi
  have hjp := Nat.pos_of_mem_divisors hj
  have he : (6/i * (m/j)) * (i*j) = 6*m := by
    calc
      _ = (6 / i * i) * (m / j * j) := by ring
      _ = _ := by rw [Nat.div_mul_cancel hi', Nat.div_mul_cancel hj']
  have he' : 6*m / (i*j) = 6/i * (m/j) := by
    rw [← he, Nat.mul_div_cancel _ (Nat.mul_pos hip hjp)]
  have hii : i.Coprime (6/i) := by
    rw [six_divisors] at hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  have hij := (hc.coprime_dvd_left hi').coprime_dvd_right (Nat.div_dvd_of_dvd hj')
  have hji := ((hc.coprime_dvd_left (Nat.div_dvd_of_dvd hi')).coprime_dvd_right hj').symm
  simp only [he', Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right]
  tauto

private def positiveSide (m d : ℕ) : Prop := 6 ∣ d ∨ d = 3*m
private instance (m d : ℕ) : Decidable (positiveSide m d) := by unfold positiveSide; infer_instance

private def signed (m d : ℕ) : ℤ := if positiveSide m d then d else -(d : ℤ)

private def contribution (m d : ℕ) : ℤ :=
  if d ≠ 6*m ∧ d.Coprime (6*m/d) then signed m d else 0

private theorem block_sum {m j : ℕ} (hm : 0 < m) (hc : Nat.Coprime 6 m)
    (hj : j ∈ m.divisors) :
    ∑ i ∈ (6 : ℕ).divisors, contribution m (i*j) = 0 := by
  have hd := (Nat.mem_divisors.mp hj).1
  have hle := Nat.le_of_dvd hm hd
  have hj2 := Nat.prime_two.coprime_iff_not_dvd.mp
    ((hc.coprime_dvd_left (by decide : 2 ∣ 6)).coprime_dvd_right hd)
  have hj3 := Nat.prime_three.coprime_iff_not_dvd.mp
    ((hc.coprime_dvd_left (by decide : 3 ∣ 6)).coprime_dvd_right hd)
  have he (i) (hi : i ∈ (6 : ℕ).divisors) : contribution m (i*j) =
      if i*j ≠ 6*m ∧ j.Coprime (m/j) then signed m (i*j) else 0 := by
    simp only [contribution, unitary_block hc hi hj]
  rw [six_divisors]
  simp only [sum_insert (by decide : 1 ∉ ({2, 3, 6} : Finset ℕ)),
    sum_insert (by decide : 2 ∉ ({3, 6} : Finset ℕ)),
    sum_insert (by decide : 3 ∉ ({6} : Finset ℕ)), sum_singleton]
  rw [he 1 (by decide), he 2 (by decide), he 3 (by decide), he 6 (by decide)]
  by_cases hu : j.Coprime (m/j)
  · by_cases hmj : j = m
    all_goals simp (disch := omega) [signed, positiveSide, hmj]
    all_goals omega
  · simp [hu]

private theorem six_multiple (m : ℕ) (hm : 0 < m) (hc : Nat.Coprime 6 m) :
    IsUnitaryHalfZumkeller (6*m) := by
  classical
  have total : ∑ d ∈ (6*m).divisors, contribution m d = 0 := by
    rw [hc.divisors_mul]
    rw [sum_map]
    change (∑ p ∈ ((6 : ℕ).divisors ×ˢ m.divisors).attach,
      (fun x : ℕ × ℕ => contribution m (x.1*x.2)) p.val) = 0
    rw [sum_attach ((6 : ℕ).divisors ×ˢ m.divisors)
      (fun x : ℕ × ℕ => contribution m (x.1*x.2)), sum_product]
    rw [sum_comm]
    exact sum_eq_zero fun j hj => block_sum hm hc hj
  let U := unitaryProperDivisors (6*m)
  have hU : U = (6*m).divisors.filter (fun d => d ≠ 6*m ∧ d.Coprime (6*m/d)) := by
    ext d
    simp only [U, unitaryProperDivisors, mem_filter, Nat.mem_properDivisors, Nat.mem_divisors]
    have hn : 0 < 6*m := by omega
    constructor
    · rintro ⟨⟨hd, hl⟩, hg⟩
      exact ⟨⟨hd, hn.ne'⟩, hl.ne, hg⟩
    · rintro ⟨⟨hd, _⟩, hne, hg⟩
      exact ⟨⟨hd, lt_of_le_of_ne (Nat.le_of_dvd hn hd) hne⟩, hg⟩
  have balance : ∑ d ∈ U, signed m d = 0 := by
    rw [hU, sum_filter]
    exact total
  let S := U.filter (positiveSide m)
  refine ⟨S, filter_subset _ _, ?_⟩
  change ∑ d ∈ S, d = ∑ d ∈ U \ S, d
  have hrest : U \ S = U.filter (fun d => ¬positiveSide m d) := by
    ext d
    simp [S]
    tauto
  have h : (∑ d ∈ S, (d : ℤ)) - (∑ d ∈ U \ S, (d : ℤ)) = 0 := by
    rw [hrest]
    simp only [S, sum_filter, ← sum_sub_distrib]
    convert balance using 1
    apply sum_congr rfl
    intro d _
    by_cases h : positiveSide m d <;> simp [signed, h]
  apply Nat.cast_injective (R := ℤ)
  push_cast
  exact sub_eq_zero.mp h

private theorem shape (n : ℕ) : ∃ t, a (n+2) = 36*t+6 := by
  induction n with
  | zero => exact ⟨0, by decide⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨36*t^2+13*t+1, by rw [a, ht]; ring⟩

end SylvesterDivisors

open OMA.S_oeis_a007018 SylvesterDivisors

theorem OMA.solution : type_of% @OMA.S_oeis_a007018.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
  obtain ⟨t, ht⟩ := shape k
  rw [ht, show 36*t+6 = 6*(6*t+1) by ring]
  apply six_multiple _ (by omega)
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_rec]
  simp [Nat.add_mod]
