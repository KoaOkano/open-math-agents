import OMAStatements.S_oeis_a087324

/-!
The two conjectures about decimal nine's complements have different answers.
Strings of 6k+1 twos and sevens give infinitely many matching signatures.
The underlying repunit is coprime to both 2 and 7, so each multiplier adds
one exponent 1. The signature {2} never occurs: two positive squares cannot
sum to a string of nines.
-/

namespace NineComplement

open OMA.S_oeis_a087324

private theorem square_of_sig {n : ℕ} (hn : 0 < n) (hs : sig n = {2}) :
    ∃ a : ℕ, 0 < a ∧ n = a ^ 2 := by
  have card : n.primeFactors.card = 1 := by
    simpa [sig] using congrArg Multiset.card hs
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp card
  have ha' : a ∈ n.primeFactors := by simp [ha]
  have e : n.factorization a = 2 := by simpa [sig,ha] using hs
  refine ⟨a,Nat.pos_of_mem_primeFactors ha',?_⟩
  rw [← Nat.prod_factorization_pow_eq_self hn.ne', Nat.prod_factorization_eq_prod_primeFactors]
  simp [ha,e]

private theorem sq_res (a : ℕ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt a (by decide : 0 < 4)
  interval_cases a % 4 <;> decide

private theorem no_squares (a b d : ℕ) (ha : 0 < a) (hb : 0 < b) :
    a ^ 2 + b ^ 2 + 1 ≠ 10 ^ d := by
  intro e
  rcases d with _|(_|d)
  · simp at e
    nlinarith
  · norm_num at e
    have a2 : a ≤ 2 := by nlinarith [sq_nonneg (a : ℤ), Nat.mul_self_le_mul_self (show 1 ≤ b by omega)]
    have b2 : b ≤ 2 := by nlinarith [Nat.mul_self_le_mul_self (show 1 ≤ a by omega)]
    interval_cases a <;> interval_cases b <;> norm_num at e
  · have z : 10 ^ (d+2) % 4 = 0 := by rw [pow_add]; omega
    have eq := congrArg (fun x : ℕ => x % 4) e
    change (a ^ 2 + b ^ 2 + 1) % 4 = 10 ^ (d+2) % 4 at eq
    rw [z] at eq
    rcases sq_res a with h|h <;> rcases sq_res b with j|j <;> omega

private def rep : ℕ → ℕ
  | 0 => 1
  | k+1 => 1000000 * rep k + 111111

private theorem rep_facts (k : ℕ) :
    9 * rep k + 1 = 10 ^ (6*k+1) ∧ rep k % 2 = 1 ∧ rep k % 7 = 1 ∧ k < rep k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have ex : 6*(k+1)+1 = (6*k+1)+6 := by omega
    rw [ex, pow_add]
    norm_num only [Nat.reducePow]
    simp only [rep]
    omega

private theorem sig_mul_prime {r p : ℕ} (hp : p.Prime) (hr : r ≠ 0) (hd : ¬p ∣ r) :
    sig (p*r) = 1 ::ₘ sig r := by
  classical
  have hmem : p ∉ r.primeFactors := fun h => hd (Nat.dvd_of_mem_primeFactors h)
  have hval : (p*r).factorization p = 1 := by
    simp [Nat.factorization_mul hp.ne_zero hr, hp.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hd]
  unfold sig
  rw [Nat.primeFactors_mul hp.ne_zero hr, hp.primeFactors, Finset.singleton_union,
    Finset.insert_val_of_notMem hmem, Multiset.map_cons, hval]
  congr 1
  apply Multiset.map_congr rfl
  intro q hq
  have ne : p ≠ q := by intro e; subst q; exact hmem hq
  simp [Nat.factorization_mul hp.ne_zero hr, hp.factorization, ne]

/-- Repeated twos of lengths 1, 7, 13, ... witness the infinitude conjecture. -/
theorem infinitely_many : {n : ℕ | P n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro k
  obtain ⟨hpow,h2,h7,hk⟩ := rep_facts k
  have hr : rep k ≠ 0 := by omega
  have hlen : (Nat.digits 10 (2 * rep k)).length = 6*k+1 := by
    rw [Nat.length_digits 10 _ (by decide) (by omega)]
    congr 1
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · rw [pow_succ] at hpow
      omega
    · omega
  have hc : comp9 (2 * rep k) = 7 * rep k := by
    unfold comp9
    rw [hlen, ← hpow]
    omega
  refine ⟨2 * rep k,?_,by omega⟩
  change 1 ≤ 2 * rep k ∧ 1 ≤ comp9 (2 * rep k) ∧ sig (2 * rep k) = sig (comp9 (2 * rep k))
  rw [hc, sig_mul_prime (p := 2) (by decide) hr (by omega),
    sig_mul_prime (p := 7) (by decide) hr (by omega)]
  exact ⟨by omega, by omega, rfl⟩

end NineComplement

open NineComplement OMA.S_oeis_a087324

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a087324.main) := by
  intro h
  obtain ⟨n,⟨hn,hc,he⟩,hs⟩ := h.2 ({2} : Multiset ℕ) (by simp)
  obtain ⟨a,ha,ea⟩ := square_of_sig hn hs
  obtain ⟨b,hb,eb⟩ := square_of_sig hc (he.symm.trans hs)
  have hlt := Nat.lt_base_pow_length_digits (b := 10) (m := n) (by decide)
  apply no_squares a b (Nat.digits 10 n).length ha hb
  rw [← ea, ← eb]
  unfold comp9
  omega
