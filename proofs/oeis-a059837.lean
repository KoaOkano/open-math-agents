import OMAStatements.S_oeis_a059837
import Mathlib.Tactic

open OMA.S_oeis_a059837

namespace DiagonalIndexCheck

def middle (j : ℕ) : ℤ := j.choose (j/2)

lemma even_step (k : ℕ) : middle (2*k+2) = 2*middle (2*k+1) := by
  unfold middle
  rw [show (2*k+2)/2 = k+1 by omega, show (2*k+1)/2 = k by omega,
    Nat.choose_succ_succ' (2*k+1) k, Nat.choose_symm_half]
  push_cast
  ring

lemma odd_step (k : ℕ) : ((k:ℤ)+1)*middle (2*k+1) = (2*(k:ℤ)+1)*middle (2*k) := by
  unfold middle
  rw [show (2*k+1)/2 = k by omega, show 2*k/2 = k by omega]
  have h := congrArg (fun x : ℕ => (x:ℤ)) (Nat.add_one_mul_choose_eq (2*k) k)
  rw [Nat.choose_symm_half] at h
  push_cast at h
  linear_combination -h

lemma middle_recurrence (t : ℕ) : ((t:ℤ)+3)*middle (t+2) -
    2*middle (t+1) - 4*((t:ℤ)+1)*middle t = 0 := by
  obtain ⟨k, rfl | rfl⟩ : ∃ k, t=2*k ∨ t=2*k+1 := ⟨t/2, by omega⟩
  · rw [even_step]
    push_cast
    linear_combination 4*odd_step k
  · have h := odd_step (k+1)
    rw [show 2*(k+1)+1 = 2*k+1+2 by omega, show 2*(k+1) = 2*k+1+1 by omega] at h
    push_cast at h ⊢
    linear_combination 2*h + (4*(k:ℤ)+4)*even_step k

-- The printed coefficients do give a recurrence for the zero-indexed list.
lemma zero_offset (t : ℕ) :
    ((t:ℤ)+3)*diagonal (t+2) - 2*((t:ℤ)+2)*diagonal (t+1) -
      4*((t:ℤ)+2)*((t:ℤ)+1)^2*diagonal t = 0 := by
  change ((t:ℤ)+3)*(((t+2).factorial:ℤ)*middle (t+2)) -
    2*((t:ℤ)+2)*(((t+1).factorial:ℤ)*middle (t+1)) -
    4*((t:ℤ)+2)*((t:ℤ)+1)^2*((t.factorial:ℤ)*middle t) = 0
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  linear_combination ((t:ℤ)+2)*((t:ℤ)+1)*(t.factorial:ℤ)*middle_recurrence t

end DiagonalIndexCheck

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a059837.main) := by
  intro h
  have evaluated :
      ((3:ℤ)+1)*diagonal 2 - 2*3*diagonal 1 - 4*3*(3-1)^2*diagonal 0 = -38 := by decide
  have asserted := h 0
  change ((3:ℤ)+1)*diagonal 2 - 2*3*diagonal 1 - 4*3*(3-1)^2*diagonal 0 = 0 at asserted
  omega
