import OMAStatements.S_oeis_a077653

/-!
The initial triple (2,4,4) gives an unbounded sequence of even integers.
From a triple (2m,0,2m+2) the recurrence reaches (2m+2,0,2m+4) after
2m+3 steps. In contrast, every shifted square-root floor takes arbitrarily
large odd values.
-/

namespace EvenRecurrence

open OMA.S_oeis_a077653

private abbrev b := seq 2 4 4

private def state (n : ℕ) := (b (n+1), b (n+2), b (n+3))
private def move (v : ℤ × ℤ × ℤ) := (v.2.1, v.2.2, |v.2.2-v.2.1-v.1|)

private theorem state_succ (n : ℕ) : state (n+1) = move (state n) := rfl

private theorem two_steps {u v : ℤ} (hu : 2 ≤ u) (hv : 0 ≤ v) :
    move (move (u+2,v,u)) = (u,v+2,u-2) := by
  have e₁ : u-v-(u+2) = -(v+2) := by ring
  have e₂ : v+2-u-v = -(u-2) := by ring
  simp only [move, e₁, e₂, abs_neg, abs_of_nonneg (show 0 ≤ v+2 by omega),
    abs_of_nonneg (show 0 ≤ u-2 by omega)]

private theorem next_block (t m : ℕ) (start : state t = (2*(m:ℤ),0,2*(m:ℤ)+2)) :
    state (t+2+2*m+1) = (2*(m:ℤ)+2,0,2*(m:ℤ)+4) := by
  have block (i : ℕ) (hi : i ≤ m) : state (t+2+2*i) =
      (2*(m:ℤ)-2*i+2, 2*(i:ℤ)+2, 2*(m:ℤ)-2*i) := by
    induction i with
    | zero =>
      change move (move (state t)) = _
      simp [start, move, abs_of_nonneg (show 0 ≤ 2*(m:ℤ) by positivity)]
    | succ i ih =>
      rw [show t+2+2*(i+1) = (t+2+2*i+1)+1 by omega, state_succ, state_succ, ih (by omega)]
      rw [two_steps (by omega) (by omega)]
      push_cast
      exact Prod.ext (by ring) (Prod.ext (by ring) (by ring))
  rw [state_succ, block m le_rfl]
  simp [move]
  rw [abs_of_nonpos (by omega)]
  omega

private theorem blocks (j : ℕ) : ∃ t : ℕ, state t = (2*(j:ℤ)+6,0,2*(j:ℤ)+8) := by
  induction j with
  | zero => exact ⟨4, by decide⟩
  | succ j ih =>
    obtain ⟨t, ht⟩ := ih
    have initial : state t = (2*((j+3:ℕ):ℤ),0,2*((j+3:ℕ):ℤ)+2) := by
      rw [ht]
      push_cast
      exact Prod.ext (by ring) (Prod.ext rfl (by ring))
    refine ⟨_, (next_block t (j+3) initial).trans ?_⟩
    push_cast
    exact Prod.ext (by ring) (Prod.ext rfl (by ring))

private theorem unbounded (B : ℤ) : ∃ n : ℕ, 1 ≤ n ∧ B < b n := by
  obtain ⟨t,h⟩ := blocks B.natAbs
  have term : b (t+1) = 2*(B.natAbs:ℤ)+6 := congrArg Prod.fst h
  exact ⟨t+1, by omega, by omega⟩

private theorem even_terms : ∀ n : ℕ, 2 ∣ b n
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | n+4 => (dvd_abs _ _).mpr (dvd_sub (dvd_sub (even_terms (n+3)) (even_terms (n+2)))
      (even_terms (n+1)))

private theorem even_max (n : ℕ) : 2 ∣ maxUpTo 2 4 4 n := by
  induction n with
  | zero => exact dvd_zero _
  | succ n ih =>
    rw [maxUpTo]
    rcases le_total (maxUpTo 2 4 4 n) (b (n+1)) with h | h
    · rw [max_eq_right h]
      exact even_terms _
    · rwa [max_eq_left h]

end EvenRecurrence

open OMA.S_oeis_a077653 EvenRecurrence

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a077653.main) := by
  intro claim
  obtain ⟨N,C,h⟩ := claim 2 4 4 unbounded
  let m : ℤ := 2*((N:ℤ)+C.natAbs+2)+1
  have hm : 0 ≤ m := by dsimp [m]; omega
  have late : (N:ℤ) < m^2-C := by
    have base : (N:ℤ)+C+1 ≤ m := by dsimp [m]; omega
    nlinarith [sq_nonneg (m-1)]
  let n := (m^2-C).toNat
  have castn : (n:ℤ) = m^2-C := Int.toNat_of_nonneg (by omega)
  have square : (n:ℝ)+(C:ℝ) = (m:ℝ)^2 := by exact_mod_cast (show (n:ℤ)+C=m^2 by omega)
  have even := even_max n
  have hval : maxUpTo 2 4 4 n = ⌊Real.sqrt ((n:ℝ)+(C:ℝ))⌋ := h n (by omega)
  rw [hval, square, Real.sqrt_sq (by exact_mod_cast hm), Int.floor_intCast] at even
  dsimp [m] at even
  omega
