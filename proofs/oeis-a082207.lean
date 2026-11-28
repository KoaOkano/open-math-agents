import OMAStatements.S_oeis_a082207

/-!
Adding a digit 1 at both ends of a decimal palindrome leaves the product
of its digits unchanged. Iteration gives infinitely many different
palindromes for every digit product already realized by a palindrome.
Murthy's example 777 has the palindromic product 343.
-/

namespace PalindromicProducts

open OMA.S_oeis_a082207

private def wrap (n : ℕ) : ℕ := Nat.ofDigits 10 ((1 :: Nat.digits 10 n) ++ [1])

private theorem wrap_digits (n : ℕ) :
    Nat.digits 10 (wrap n) = (1 :: Nat.digits 10 n) ++ [1] := by
  apply Nat.digits_ofDigits 10 (by decide)
  · intro d hd
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with (rfl | hd) | rfl
    · decide
    · exact Nat.digits_lt_base (by decide) hd
    · decide
  · intro h
    simp

private def family (s : ℕ) : ℕ → ℕ
  | 0 => s
  | n+1 => wrap (family s n)

private theorem family_properties {s : ℕ} (hs : isPalindrome s) (n : ℕ) :
    isPalindrome (family s n) ∧ digitProd (family s n) = digitProd s ∧
      (Nat.digits 10 (family s n)).length = (Nat.digits 10 s).length + 2*n := by
  induction n with
  | zero => exact ⟨hs, rfl, by simp [family]⟩
  | succ n ih =>
    obtain ⟨hpal, hprod, hlen⟩ := ih
    change (Nat.digits 10 (family s n)).reverse = _ at hpal
    change (Nat.digits 10 (family s n)).prod = _ at hprod
    simp [family, isPalindrome, digitProd, wrap_digits, hpal, hprod, hlen, Nat.mul_succ]
    omega

/-- Every decimal digit product realized by a palindrome occurs infinitely often. -/
theorem infinite_fiber {s : ℕ} (hs : isPalindrome s) :
    Set.Infinite {n : ℕ | isPalindrome n ∧ digitProd n = digitProd s} := by
  have hinj : Function.Injective (family s) := by
    intro i j hij
    have eqLen := congrArg (fun n => (Nat.digits 10 n).length) hij
    rw [(family_properties hs i).2.2, (family_properties hs j).2.2] at eqLen
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨i, rfl⟩
  exact ⟨(family_properties hs i).1, (family_properties hs i).2.1⟩

end PalindromicProducts

open OMA.S_oeis_a082207

theorem OMA.solution : type_of% @OMA.S_oeis_a082207.main := by
  have h := PalindromicProducts.infinite_fiber (s := 777) (by unfold isPalindrome; decide)
  apply h.mono
  rintro n ⟨hn, hp⟩
  refine ⟨hn, ?_, ?_⟩
  · rw [hp]
    decide
  · rw [hp]
    unfold isPalindrome
    decide
