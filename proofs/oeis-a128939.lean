import OMAStatements.S_oeis_a128939
import Mathlib.Tactic

open OMA.S_oeis_a128939

namespace PartitionProduct

lemma four_more (n : ℕ) (hn : 4 ≤ n) : prediction (n+4) = 4 * prediction n := by
  have hd : (n+4)/4 = n/4+1 := by omega
  have hm : (n+4)%4 = n%4 := by omega
  simp only [prediction, if_neg (show ¬ n+4 < 4 by omega), if_neg (by omega : ¬ n < 4), hd, hm]
  split_ifs
  · rw [show n/4+1-1 = n/4-1+1 by omega, pow_succ]
    ring
  · rw [pow_succ]
    ring

lemma shift_bound (a k : ℕ) (h : ∀ n < 8, a * prediction n ≤ prediction (n+k))
    (n : ℕ) : a * prediction n ≤ prediction (n+k) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n < 8
    · exact h _ small
    obtain ⟨j, rfl⟩ : ∃ j, n = j+4 := ⟨n-4, by omega⟩
    have prev := ih j (by omega)
    rw [four_more j (by omega), show j+4+k = (j+k)+4 by omega, four_more (j+k) (by omega)]
    nlinarith only [prev]

lemma one_more (n : ℕ) : prediction n ≤ prediction (n+1) := by
  simpa using shift_bound 1 1 (by intro k hk; interval_cases k <;> decide) n

lemma factor_four (n : ℕ) : 4 * prediction n ≤ prediction (n+4) :=
  shift_bound 4 4 (by intro k hk; interval_cases k <;> decide) n

lemma factor_seven (n : ℕ) : 7 * prediction n ≤ prediction (n+7) :=
  shift_bound 7 7 (by intro k hk; interval_cases k <;> decide) n

lemma add_part (p : ℕ) (hp : p % 3 = 1) (n : ℕ) :
    p * prediction n ≤ prediction (n+p) := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases small : p < 10
    · obtain rfl | rfl | rfl : p=1 ∨ p=4 ∨ p=7 := by omega
      · simpa using one_more n
      · exact factor_four n
      · exact factor_seven n
    have prev := ih (p-6) (by omega) (by omega)
    have step := factor_four (n+(p-6))
    have tail := (one_more (n+(p-6)+4)).trans (one_more (n+(p-6)+4+1))
    rw [show n+(p-6)+4+1+1 = n+p by omega] at tail
    calc
      p * prediction n ≤ (4*(p-6)) * prediction n := Nat.mul_le_mul_right _ (by omega)
      _ = 4*((p-6)*prediction n) := by ring
      _ ≤ _ := (Nat.mul_le_mul_left 4 prev).trans (step.trans tail)

lemma upper (l : List ℕ) (h : ∀ p ∈ l, p % 3 = 1) :
    l.prod ≤ prediction l.sum := by
  induction l with
  | nil => decide
  | cons p l ih =>
    have hp := h p (List.mem_cons_self ..)
    have ht := ih (fun k hk => h k (List.mem_cons_of_mem _ hk))
    rw [List.prod_cons, List.sum_cons, Nat.add_comm p l.sum]
    exact (Nat.mul_le_mul_left _ ht).trans (add_part p hp l.sum)

lemma attained (n : ℕ) : prediction n ∈ products n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n < 8
    · unfold products
      interval_cases n
      · exact ⟨[], by norm_num [prediction]⟩
      · exact ⟨[1], by norm_num [prediction]⟩
      · exact ⟨[1,1], by norm_num [prediction]⟩
      · exact ⟨[1,1,1], by norm_num [prediction]⟩
      · exact ⟨[4], by norm_num [prediction]⟩
      · exact ⟨[4,1], by norm_num [prediction]⟩
      · exact ⟨[4,1,1], by norm_num [prediction]⟩
      · exact ⟨[7], by norm_num [prediction]⟩
    obtain ⟨j, rfl⟩ : ∃ j, n = j+4 := ⟨n-4, by omega⟩
    obtain ⟨l, hl, hs, hv⟩ := ih j (by omega)
    refine ⟨4 :: l, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · decide
      · exact hl _ hp
    · simp [hs, Nat.add_comm]
    · rw [List.prod_cons, hv, four_more j (by omega)]

end PartitionProduct

theorem OMA.solution : type_of% @OMA.S_oeis_a128939.main := by
  intro n _
  refine ⟨PartitionProduct.attained n, ?_⟩
  rintro m ⟨l, hl, rfl, rfl⟩
  exact PartitionProduct.upper l hl
