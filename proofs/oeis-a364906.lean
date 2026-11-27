import OMAStatements.S_oeis_a364906

/-!
# A counterexample to the conjecture for OEIS A364906

The prime indices of `1547 = 7 * 13 * 17` are `4, 6, 7`. The only
nonnegative solution of `4*x + 6*y + 7*z = 17` is `(1, 1, 1)`.
The two divisors `119 = 7 * 17` and `221 = 13 * 17` both have index gcd `1`.
-/

open OMA.S_oeis_a364906

namespace A364906

private theorem factors221 : (221 : ℕ).primeFactorsList = [13, 17] := by
  rw [Nat.primeFactorsList_add_two 219]
  norm_num [Nat.primeFactorsList_prime (by decide : Nat.Prime 17)]

private theorem countAtWitness : a 1547 = 1 := by
  have factors : (1547 : ℕ).primeFactorsList = [7, 13, 17] := by
    rw [Nat.primeFactorsList_add_two 1545]
    norm_num [factors221]
  have indices : primeIndices 1547 = [4, 6, 7] := by
    rw [primeIndices, factors]
    decide +kernel
  rw [a, indices, Nat.card_eq_one_iff_exists]
  refine ⟨⟨fun _ => 1, ?_⟩, ?_⟩
  · decide
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    change (∑ i : Fin 3, c i * ([4, 6, 7] : List ℕ).get i) = 17 at hc
    rw [Fin.sum_univ_three] at hc
    change c 0 * 4 + c 1 * 6 + c 2 * 7 = 17 at hc
    have hzle : c 2 ≤ 2 := by omega
    have hz : c 2 = 1 := by interval_cases hz' : c 2 <;> omega
    have hy : c 1 = 1 := by omega
    have hx : c 0 = 1 := by omega
    funext i
    change Fin 3 at i
    fin_cases i <;> assumption

end A364906

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a364906.main) := by
  intro statement
  have hinj := ((statement 1547 (by decide)).mp A364906.countAtWitness).2
  have ha : 119 ∈ (1547 : ℕ).divisors := Nat.mem_divisors.mpr ⟨by decide, by decide⟩
  have hb : 221 ∈ (1547 : ℕ).divisors := Nat.mem_divisors.mpr ⟨by decide, by decide⟩
  have factors119 : (119 : ℕ).primeFactorsList = [7, 17] := by
    rw [Nat.primeFactorsList_add_two 117]
    norm_num [Nat.primeFactorsList_prime (by decide : Nat.Prime 17)]
  have heq : gcdIndices 119 = gcdIndices 221 := by
    simp only [gcdIndices, primeIndices, factors119, A364906.factors221]
    decide +kernel
  exact (by decide : (119 : ℕ) ≠ 221) (hinj ha hb heq)
