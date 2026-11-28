import OMAStatements.S_oeis_a228916

/-!
Václav Kotešovec's prime-index conjecture for A108300 follows from the
three-step recurrence. Terms in positions 1 modulo 3 are divisible by five,
and terms in positions 2 modulo 3 are even. Only the initial five is prime
in either class.
-/

namespace PrimePositions

open OMA.S_oeis_a228916

private theorem jump (m : ℕ) : u (m+3) = 10*u (m+1) + 3*u m := by
  rw [show u (m+3) = 3*u (m+2) + u (m+1) from rfl, u]
  ring

private theorem divisors (k : ℕ) : 5 ∣ u (3*k+1) ∧ 2 ∣ u (3*k+2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 3*(k+1)+1 = (3*k+1)+3 by omega, jump,
        show 3*(k+1)+2 = (3*k+2)+3 by omega, jump]
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    constructor
    · exact ⟨2*u (3*k+1+1) + 3*a, by rw [ha]; ring⟩
    · exact ⟨5*u (3*k+2+1) + 3*b, by rw [hb]; ring⟩

private theorem growth (k : ℕ) : k+5 ≤ u (k+1) := by
  induction k with
  | zero => decide
  | succ k ih => rw [u]; omega

private theorem index_dvd {m : ℕ} (hm : 1 < m) (hp : (u m).Prime) : 3 ∣ m := by
  have hbig : 5 < u m := by
    have h := growth (m-1)
    rw [show m-1+1 = m by omega] at h
    omega
  let k := m/3
  have hclass : 3 ∣ m ∨ m = 3*k+1 ∨ m = 3*k+2 := by dsimp [k]; omega
  rcases hclass with h | h | h
  · exact h
  · have hd : 5 ∣ u m := h ▸ (divisors k).1
    have := hp.eq_one_or_self_of_dvd 5 hd
    omega
  · have hd : 2 ∣ u m := h ▸ (divisors k).2
    have := hp.eq_one_or_self_of_dvd 2 hd
    omega

theorem result : type_of% @OMA.S_oeis_a228916.main := by
  intro n hn
  let P := fun m => (u m).Prime
  change 3 ∣ Nat.nth P (n-1)
  by_cases h : Nat.nth P (n-1) = 0
  · simp [h]
  have h₀ : Nat.nth P 0 ≠ 0 :=
    Nat.nth_ne_zero_anti (by decide : ¬ P 0) (Nat.zero_le _) h
  have hlt : Nat.nth P 0 < Nat.nth P (n-1) :=
    Nat.nth_lt_nth' (by omega) (Nat.lt_card_toFinset_of_nth_ne_zero h)
  exact index_dvd (by omega) (Nat.nth_mem_of_ne_zero h)

end PrimePositions

theorem OMA.solution : type_of% @OMA.S_oeis_a228916.main := PrimePositions.result
