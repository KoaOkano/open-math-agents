import OMAStatements.S_oeis_a027984

/-!
Colin Barker's recurrence and generating function for A027984 follow directly
from the Lucas array. The left half of each row consists of Lucas numbers.
Weight the right half with these numbers and then with their one-place shift.
The two sums form a first-order system with a Fibonacci forcing term.
G. C. Greubel also recorded a Fibonacci-Lucas closed form in OEIS in 2025.
-/

namespace LucasRows

open Finset OMA.S_oeis_a027984

private def L : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | k + 2 => L (k + 1) + L k

private lemma left_half (n k : ℕ) (h : k ≤ n) : (T n k : ℤ) = L k := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    rfl
  | succ n ih =>
    rcases k with _ | _ | k
    · simp [T, L]
    · simp [T, L, show ¬ 2*(n+1) < 1 by omega, show 1 ≠ 2*(n+1) by omega]
    · have hlt : ¬ 2*(n+1) < k+2 := by omega
      have hne : k+2 ≠ 2*(n+1) := by omega
      simp only [T, if_neg hlt, Nat.add_eq_zero_iff, Nat.reduceEqDiff,
        and_false, hne, or_self, if_false, Nat.add_sub_cancel, Nat.cast_add, L]
      simpa using congrArg₂ (· + ·) (ih (k+1) (by omega)) (ih k (by omega))

private lemma outside (n j : ℕ) (h : 2*n < j) : T n j = 0 := by
  cases n with
  | zero => simp [T, show j ≠ 0 by omega]
  | succ n => simp [T, h]

private lemma last_entry (n : ℕ) : T n (2*n) = 1 := by
  cases n <;> simp [T]

private def R (n k : ℕ) : ℤ := T n (n+k)

private lemma firstR (n : ℕ) : R n 0 = L n := by
  simpa [R] using left_half n n (le_refl n)

private lemma lastR (n : ℕ) : R n (n+1) = 0 := by
  simp [R, outside _ _ (show 2*n < n+(n+1) by omega)]

private lemma shift (n k : ℕ) (h : k ≤ n) :
    R (n+1) (k+1) = R n (k+1) + R n k := by
  by_cases e : k = n
  · subst k
    rw [lastR]
    simp only [R, zero_add, show n+1+(n+1) = 2*(n+1) by omega,
      show n+n = 2*n by omega, last_entry]
  · have hlt : ¬ 2*(n+1) < n+1+(k+1) := by omega
    have hmid : ¬ (n+1+(k+1) = 0 ∨ n+1+(k+1) = 2*(n+1)) := by omega
    simp only [R, T, if_neg hlt, if_neg hmid, if_neg (show n+1+(k+1) ≠ 1 by omega),
      show n+1+(k+1)-1 = n+(k+1) by omega, show n+1+(k+1)-2 = n+k by omega, Nat.cast_add]

private def W (n : ℕ) (f : ℕ → ℤ) : ℤ := ∑ k ∈ range (n+1), f k * R n k

private lemma nextW (n : ℕ) (f : ℕ → ℤ) :
    W (n+1) f = W n f + W n (fun k => f (k+1)) + f 0 * (L (n+1) - L n) := by
  have edge : W n f = (∑ k ∈ range (n+1), f (k+1) * R n (k+1)) + f 0 * L n := by
    calc
      W n f = ∑ k ∈ range ((n+1)+1), f k * R n k := by
        rw [sum_range_succ, lastR, mul_zero, add_zero]; rfl
      _ = _ := by rw [sum_range_succ', firstR]
  have row : W (n+1) f =
      (∑ k ∈ range (n+1), f (k+1) * (R n (k+1) + R n k)) + f 0 * L (n+1) := by
    unfold W
    rw [sum_range_succ', firstR]
    congr 1
    apply sum_congr rfl
    intro k hk
    rw [shift _ _ (Nat.lt_succ_iff.mp (mem_range.mp hk))]
  simp only [mul_add, sum_add_distrib] at row
  change _ = _ + (∑ k ∈ range (n+1), f (k+1) * R n k) + _
  linear_combination row - edge

private lemma aW (n : ℕ) : a n = W n L := by
  unfold a W R
  apply sum_congr rfl
  intro k hk
  rw [left_half n k (Nat.lt_succ_iff.mp (mem_range.mp hk))]

private def b (n : ℕ) := W n (fun k => L (k+1))

private lemma nextA (n : ℕ) : a (n+1) = a n + b n + (L (n+1) - L n) := by
  rw [aW, aW, nextW]; simp only [show L 0 = 1 by rfl, one_mul]; rfl

private lemma nextB (n : ℕ) : b (n+1) = a n + 2*b n + 3*(L (n+1)-L n) := by
  have two : W n (fun k => L (k+2)) = b n + W n L := by
    simp only [W, b, L, add_mul, sum_add_distrib]
  change W (n+1) (fun k => L (k+1)) = _
  rw [nextW, two, ← aW]
  change b n + (b n + a n) + 3*(L (n+1)-L n) = _
  ring

private lemma recurrence (n : ℕ) :
    a (n+4) = 4*a (n+3) - 3*a (n+2) - 2*a (n+1) + a n := by
  have l (k : ℕ) : L (k+2) = L (k+1) + L k := rfl
  linarith only [nextA n, nextA (n+1), nextA (n+2), nextA (n+3),
    nextB n, nextB (n+1), nextB (n+2), l n, l (n+1), l (n+2)]

end LucasRows

open LucasRows OMA.S_oeis_a027984 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a027984.main := by
  constructor
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
    simpa using recurrence k
  · let F := PowerSeries.mk (fun n => (a n : ℚ))
    suffices h : F - (4:ℕ) • (F * X^1) + (3:ℕ) • (F * X^2) +
          (2:ℕ) • (F * X^3) - F * X^4 =
        X^0 + (2:ℕ) • (X^1 : PowerSeries ℚ) - X^2 - (2:ℕ) • X^3 by
      change F * _ = _
      simp only [nsmul_eq_mul, Nat.cast_ofNat] at h
      linear_combination h
    have h0 : a 0 = 1 := by decide
    have h1 : a 1 = 6 := by decide
    have h2 : a 2 = 20 := by decide
    have h3 : a 3 = 58 := by decide
    ext n
    simp only [map_add, map_sub, map_nsmul]
    simp only [nsmul_eq_mul, Nat.cast_ofNat,
      coeff_mul_X_pow', coeff_X_pow, F, coeff_mk]
    rcases n with _ | _ | _ | _ | n
    · norm_num [h0, h1, h2, h3]
    · norm_num [h0, h1, h2, h3]
    · norm_num [h0, h1, h2, h3]
    · norm_num [h0, h1, h2, h3]
    have h := congrArg (fun z : ℤ => (z : ℚ)) (recurrence n)
    push_cast at h
    simp only [show n+4-1 = n+3 by omega, show n+4-2 = n+2 by omega,
      show n+4-3 = n+1 by omega, show n+4-4 = n by omega,
      if_pos (by omega : 1 ≤ n+4), if_pos (by omega : 2 ≤ n+4),
      if_pos (by omega : 3 ≤ n+4), if_pos (by omega : 4 ≤ n+4),
      if_neg (by omega : n+4 ≠ 0), if_neg (by omega : n+4 ≠ 1),
      if_neg (by omega : n+4 ≠ 2), if_neg (by omega : n+4 ≠ 3)]
    linarith
