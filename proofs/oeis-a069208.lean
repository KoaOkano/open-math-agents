import OMAStatements.S_oeis_a069208

open OMA.S_oeis_a069208 ArithmeticFunction

namespace PowerfulDivisorSum

def Powerful (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ 2 ∣ n

lemma powerful_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m.Coprime n) :
    Powerful (m * n) ↔ Powerful m ∧ Powerful n := by
  unfold Powerful
  rw [Nat.primeFactors_mul hm hn]
  constructor
  · intro hall
    constructor
    · intro p hp
      have hc := h.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp)
      exact (hc.pow_left 2).dvd_of_dvd_mul_right (hall p (Finset.mem_union_left _ hp))
    · intro p hp
      have hc := h.symm.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp)
      exact (hc.pow_left 2).dvd_of_dvd_mul_left (hall p (Finset.mem_union_right _ hp))
  · rintro ⟨h₁, h₂⟩ p hp
    rcases Finset.mem_union.mp hp with hpm | hpn
    · exact dvd_mul_of_dvd_left (h₁ p hpm) n
    · exact dvd_mul_of_dvd_right (h₂ p hpn) m

end PowerfulDivisorSum

open PowerfulDivisorSum

theorem OMA.solution : type_of% @OMA.S_oeis_a069208.main := by
  classical
  intro f h₁ hf
  let g : ArithmeticFunction ℤ :=
    ⟨fun n => if n = 0 then 0 else chi n * f n, by simp⟩
  have hg : g.IsMultiplicative := by
    constructor
    · change (if (1 : ℕ) = 0 then 0 else chi 1 * f 1) = 1
      simp [chi, h₁]
    · intro m n h
      by_cases hm : m = 0
      · subst m
        simp
      by_cases hn : n = 0
      · subst n
        simp
      change (if m * n = 0 then 0 else chi (m * n) * f (m * n)) =
        (if m = 0 then 0 else chi m * f m) * (if n = 0 then 0 else chi n * f n)
      simp only [if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn), hf m n h]
      have hsplit := powerful_mul hm hn h
      unfold Powerful at hsplit
      unfold chi
      split_ifs <;> simp only [zero_mul, one_mul, mul_zero] <;> tauto
  have hsum (n : ℕ) : P f n = ∑ d ∈ n.divisors, chi d * f d := by
    rw [P, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    unfold chi
    split_ifs <;> simp
  have heq (n : ℕ) : P f n = (g * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n := by
    rw [hsum, coe_mul_zeta_apply]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    simp [g, hd']
  have hprod := hg.mul (isMultiplicative_zeta.natCast (R := ℤ))
  exact ⟨⟨(heq 1).trans hprod.map_one, fun m n _ _ h => by
    simpa only [heq] using hprod.map_mul_of_coprime h⟩, fun n _ => hsum n⟩
