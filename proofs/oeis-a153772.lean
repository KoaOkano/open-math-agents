import OMAStatements.S_oeis_a153772

/-!
Markus Sigg formulated the third-largest question in A153772 and described
clusters by the number of odd steps (A127824 and arXiv:2012.07839). We prove
the ranking unconditionally. A path with at least two odd steps starts at
most one thirty-sixth of the pure-halving maximum. For a path with one odd
step, the number of halvings before it determines the deficit exactly.
-/

namespace CollatzRanking

open OMA.S_oeis_a153772

private def Hits (m t : ℕ) : Prop :=
  collatz^[t] m = 1 ∧ ∀ j < t, collatz^[j] m ≠ 1

private theorem prepend {m y t : ℕ} (hm : m ≠ 1) (hy : collatz m = y)
    (h : Hits y t) : Hits m (t + 1) := by
  refine ⟨by rw [Function.iterate_succ_apply, hy]; exact h.1, ?_⟩
  intro j hj
  cases j with
  | zero => simpa using hm
  | succ j =>
    rw [Function.iterate_succ_apply, hy]
    exact h.2 j (by omega)

private theorem double {m t : ℕ} (h : Hits m t) : Hits (2 * m) (t + 1) :=
  prepend (by omega) (by simp [collatz]) h

private theorem powers (k : ℕ) : Hits (2 ^ k) k := by
  induction k with
  | zero => simp [Hits]
  | succ k ih => simpa [pow_succ, Nat.mul_comm] using double ih

private theorem classify (t m : ℕ) (h : collatz^[t] m = 1) :
    m = 2 ^ t ∨ (∃ j : ℕ, 6 * m + 2 * 2 ^ j = 2 ^ t) ∨ 36 * m ≤ 2 ^ t := by
  induction t generalizing m with
  | zero => exact Or.inl (by simpa using h)
  | succ t ih =>
    rw [Function.iterate_succ_apply] at h
    rw [pow_succ]
    by_cases he : m % 2 = 0
    · simp [collatz, he] at h
      have hm : m = 2 * (m / 2) := by omega
      rcases ih (m / 2) h with h₀ | ⟨j, hj⟩ | h₂
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl ⟨j + 1, by rw [pow_succ]; omega⟩)
      · exact Or.inr (Or.inr (by omega))
    · simp [collatz, he] at h
      rcases ih (3 * m + 1) h with h₀ | ⟨j, hj⟩ | h₂
      · exact Or.inr (Or.inl ⟨0, by simp; omega⟩)
      · exact Or.inr (Or.inr (by omega))
      · exact Or.inr (Or.inr (by omega))

/-- The odd predecessors of the powers of four from 16 onwards. -/
private def oddStart : ℕ → ℕ
  | 0 => 5
  | k + 1 => 4 * oddStart k + 1

private theorem odd_data (k : ℕ) :
    5 ≤ oddStart k ∧ oddStart k % 2 = 1 ∧ 3 * oddStart k + 1 = 2 ^ (2 * k + 4) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have e : 2 * (k + 1) + 4 = (2 * k + 4) + 2 := by omega
    rw [oddStart, e, pow_add]
    norm_num
    omega

private theorem odd_hits (k : ℕ) : Hits (oddStart k) (2 * k + 5) := by
  obtain ⟨hl, ho, he⟩ := odd_data k
  exact prepend (by omega) (by simp [collatz, ho, he]) (powers (2 * k + 4))

private theorem member {n m : ℕ} (hm : 1 ≤ m) (h : Hits m (n + 1)) : m ∈ S (n + 2) := by
  exact ⟨hm, by simpa [Hits, OrbitLength] using h⟩

private theorem ranking {n third second c : ℕ} (hc : c = 1 ∨ c = 2)
    (hm : 20 ≤ third) (h₃ : 3 * third + 4 * c = 2 ^ n)
    (h₂ : 3 * second + c = 2 ^ n) (hs : second ∈ S (n + 2)) :
    {x : ℕ | x ∈ S (n + 2) ∧ third < x}.ncard = 2 := by
  have hn : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ _ _
  have hlt : third < second := by omega
  have hmax : second < 2 ^ (n + 1) := by omega
  have hset : {x : ℕ | x ∈ S (n + 2) ∧ third < x} = {2 ^ (n + 1), second} := by
    ext x
    change (x ∈ S (n + 2) ∧ third < x) ↔ x = 2 ^ (n + 1) ∨ x = second
    constructor
    · rintro ⟨hx, hgt⟩
      have hit : collatz^[n + 1] x = 1 := by simpa using hx.2.1
      rcases classify (n + 1) x hit with h | ⟨j, hj⟩ | h
      · exact Or.inl h
      · right
        have hpow : 2 ^ j < 8 := by omega
        have hjlt : j < 3 := by
          by_contra! hge
          have : 2 ^ 3 ≤ (2 : ℕ) ^ j := Nat.pow_le_pow_right (by decide) hge
          omega
        interval_cases j <;> norm_num at hj <;> omega
      · omega
    · rintro (rfl | rfl)
      · exact ⟨member (Nat.one_le_pow _ _ (by decide)) (powers (n + 1)), lt_trans hlt hmax⟩
      · exact ⟨hs, hlt⟩
  rw [hset, Set.ncard_pair hmax.ne']

private theorem even_case (k : ℕ) :
    ∃ m : ℕ, (m : ℤ) = a (2*k+6) ∧ m ∈ S (2*k+6+2) ∧
      {x : ℕ | x ∈ S (2*k+6+2) ∧ m < x}.ncard = 2 := by
  obtain ⟨hl, _, hp⟩ := odd_data k
  have hs := (odd_data (k + 1)).2.2
  have he : 2 ^ (2*k+6) = 4 * 2 ^ (2*k+4) := by
    rw [show 2*k+6 = (2*k+4)+2 by omega, pow_add]; ring
  have hi : 3 * oddStart (k + 1) + 1 = 2 ^ (2*k+6) := by
    convert hs using 1
    congr 1
  have hsMem : oddStart (k+1) ∈ S (2*k+6+2) :=
    member (by have := (odd_data (k+1)).1; omega) (by
      convert odd_hits (k+1) using 1
      omega)
  refine ⟨4 * oddStart k, ?_, member (by omega) ?_, ?_⟩
  · have z : (2 : ℤ) ^ (2*k+6) = 12 * (oddStart k : ℤ) + 4 := by
      exact_mod_cast (show 2 ^ (2*k+6) = 12 * oddStart k + 4 by omega)
    have sign : (-1 : ℤ) ^ (2*k+6) = 1 := by
      rw [pow_add, pow_mul]; norm_num
    simp only [a, z, sign, Nat.cast_mul, Nat.cast_ofNat]
    omega
  · convert double (double (odd_hits k)) using 1
    omega
  · exact ranking (c := 1) (Or.inl rfl) (by omega) (by omega) hi hsMem

private theorem odd_case (k : ℕ) :
    ∃ m : ℕ, (m : ℤ) = a (2*k+7) ∧ m ∈ S (2*k+7+2) ∧
      {x : ℕ | x ∈ S (2*k+7+2) ∧ m < x}.ncard = 2 := by
  obtain ⟨hl, _, hp⟩ := odd_data k
  have hs := (odd_data (k + 1)).2.2
  have he : 2 ^ (2*k+7) = 8 * 2 ^ (2*k+4) := by
    rw [show 2*k+7 = (2*k+4)+3 by omega, pow_add]; ring
  have he₂ : 2 ^ (2*k+7) = 2 * 2 ^ (2*(k+1)+4) := by
    rw [show 2*k+7 = (2*(k+1)+4)+1 by omega, pow_succ]; ring
  have hi : 3 * (2 * oddStart (k + 1)) + 2 = 2 ^ (2*k+7) := by omega
  have hsMem : 2 * oddStart (k+1) ∈ S (2*k+7+2) :=
    member (by have := (odd_data (k+1)).1; omega) (by
      convert double (odd_hits (k+1)) using 1
      omega)
  refine ⟨8 * oddStart k, ?_, member (by omega) ?_, ?_⟩
  · have z : (2 : ℤ) ^ (2*k+7) = 24 * (oddStart k : ℤ) + 8 := by
      exact_mod_cast (show 2 ^ (2*k+7) = 24 * oddStart k + 8 by omega)
    have sign : (-1 : ℤ) ^ (2*k+7) = -1 := by
      rw [pow_add, pow_mul]; norm_num
    simp only [a, z, sign, Nat.cast_mul, Nat.cast_ofNat]
    omega
  · convert double (double (double (odd_hits k))) using 1
    omega
  · exact ranking (c := 2) (Or.inr rfl) (by omega) (by omega) hi hsMem

theorem result : type_of% @OMA.S_oeis_a153772.main := by
  intro n hn
  let k := (n - 6) / 2
  have h : n = 2*k+6 ∨ n = 2*k+7 := by dsimp [k]; omega
  rcases h with he | ho
  · simpa only [← he] using even_case k
  · simpa only [← ho] using odd_case k

end CollatzRanking

theorem OMA.solution : type_of% @OMA.S_oeis_a153772.main := CollatzRanking.result
