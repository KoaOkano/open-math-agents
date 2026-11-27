import OMAStatements.S_oeis_a057032

/-!
Tracing a position backward through the rotations gives Rémy Sigrist's
descending-divisor algorithm. Once a positive offset changes, the new
offset is a proper multiple of the divisor that triggered the change.
Thus the last change always leaves a composite number.

The shift between the two sequences, also recorded by Sean A. Irvine in
A057064, holds at every intermediate rotation.
-/

namespace ForwardRotations

open OMA.S_oeis_a057032

/-- Starting at r, visit the candidate divisors j+1, j, …, 2. -/
private def scan : ℕ → ℕ → ℕ
  | 0, r => r
  | j + 1, r => if j + 2 ∣ r then scan j (r + (j + 2)) else scan j r

private theorem evaluate (j r : ℕ) : PS (j + 1) (j + 1 + r) = scan j r + 1 := by
  induction j generalizing r with
  | zero => simp [PS, scan, Nat.add_comm]
  | succ j ih =>
    change rot (j + 1) (j + 2) (PS (j + 1)) (j + 2 + r) = scan (j + 1) r + 1
    rw [rot, if_neg (by omega), show j + 2 + r - (j + 1 + 1) = r by omega, scan]
    by_cases hd : j + 2 ∣ r
    · rw [if_pos hd, if_pos (Nat.dvd_iff_mod_eq_zero.mp hd)]
      rw [show j + 2 + r + (j + 2) - 1 = j + 1 + (r + (j + 2)) by omega, ih]
    · rw [if_neg hd, if_neg (fun he => hd (Nat.dvd_iff_mod_eq_zero.mpr he))]
      rw [show j + 2 + r - 1 = j + 1 + r by omega, ih]

private theorem scan_ge (j r : ℕ) : r ≤ scan j r := by
  induction j generalizing r with
  | zero => rfl
  | succ j ih =>
    rw [scan]
    split
    · exact (Nat.le_add_right _ _).trans (ih _)
    · exact ih _

private theorem scan_fixed (j r : ℕ) :
    scan j r = r ↔ ∀ d, 2 ≤ d → d ≤ j + 1 → ¬ d ∣ r := by
  induction j generalizing r with
  | zero =>
    simp [scan]
    intro d hd he
    omega
  | succ j ih =>
    rw [scan]
    by_cases hd : j + 2 ∣ r
    · rw [if_pos hd]
      have h := scan_ge j (r + (j + 2))
      constructor
      · intro he
        omega
      · intro hall
        exact (hall (j + 2) (by omega) (by omega) hd).elim
    · rw [if_neg hd, ih]
      constructor
      · intro hall d h₂ he
        rcases show d ≤ j + 1 ∨ d = j + 2 by omega with hle | rfl
        · exact hall d h₂ hle
        · exact hd
      · intro hall d h₂ he
        exact hall d h₂ (by omega)

private theorem scan_moved (j r : ℕ) (hr : 0 < r) :
    scan j r ≠ r → ¬ (scan j r).Prime := by
  induction j generalizing r with
  | zero => simp [scan]
  | succ j ih =>
    rw [scan]
    split
    next hd =>
      intro _
      by_cases he : scan j (r + (j + 2)) = r + (j + 2)
      · rw [he]
        intro hp
        have hdvd : j + 2 ∣ r + (j + 2) := dvd_add hd (dvd_refl _)
        rcases (Nat.dvd_prime hp).mp hdvd with h | h <;> omega
      · exact ih _ (by omega) he
    next => exact ih r hr

private theorem value (j : ℕ) : a (j + 2) = scan j (j + 2) + 1 := by
  change rot (j + 2) (j + 3) (PS (j + 2)) (j + 2) = _
  rw [rot, if_pos (le_refl _)]
  simpa only [Nat.add_zero, scan, dvd_zero, if_true, Nat.zero_add] using evaluate (j + 1) 0

private theorem prime_criterion (n : ℕ) (hn : 1 ≤ n) : (a n - 1).Prime ↔ a n = n + 1 := by
  rcases n with _ | _ | j
  · omega
  · norm_num [a, PS, rot]
  · rw [value]
    simp only [Nat.add_sub_cancel, Nat.add_left_inj]
    by_cases h : scan j (j + 2) = j + 2
    · rw [h]
      simp only [iff_true]
      apply Nat.prime_def_lt'.mpr
      exact ⟨by omega, fun d h₂ hd => (scan_fixed j (j + 2)).mp h d h₂ (by omega)⟩
    · exact iff_of_false (scan_moved j (j + 2) (by omega) h) h

private theorem shifted (m i : ℕ) : PS' m (i + 1) = PS m i + 1 := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
    cases m with
    | zero => rfl
    | succ m =>
      simp only [PS', PS, rot]
      by_cases hi : i ≤ m + 1
      · rw [if_pos (show i + 1 ≤ m + 2 by omega), if_pos hi, ih]
      · rw [if_neg (show ¬ i + 1 ≤ m + 2 by omega), if_neg hi,
            show i + 1 - (m + 2 + 1) = i - (m + 1 + 1) by omega]
        split
        next =>
          rw [show i + 1 + (m + 2) - 1 = (i + (m + 2) - 1) + 1 by omega, ih]
        next =>
          rw [show i + 1 - 1 = (i - 1) + 1 by omega, ih]

theorem result : type_of% @OMA.S_oeis_a057032.main := by
  intro n hn
  refine ⟨prime_criterion n hn, ?_⟩
  unfold a b
  rw [shifted, Nat.add_sub_cancel]

end ForwardRotations

theorem OMA.solution : type_of% @OMA.S_oeis_a057032.main :=
  ForwardRotations.result
