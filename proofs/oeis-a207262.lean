import OMAStatements.S_oeis_a207262
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace OMA.A207262

lemma oddDivisors (k : ℕ) (hk : ¬ 2 ∣ k) :
    (2 * k).divisors.filter (fun d => ¬ 2 ∣ d) = k.divisors := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero 2)
  have h2k : 2 * k ≠ 0 := Nat.mul_ne_zero (by decide) hk0
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, _⟩, hodd⟩
    exact ⟨(Nat.prime_two.coprime_iff_not_dvd.mpr hodd).symm.dvd_of_dvd_mul_left hd, hk0⟩
  · rintro ⟨hd, _⟩
    exact ⟨⟨dvd_mul_of_dvd_right hd 2, h2k⟩, fun h => hk (h.trans hd)⟩

end OMA.A207262

theorem OMA.solution : type_of% @OMA.S_oeis_a207262.main := by
  intro t
  dsimp only
  let k := 2 * t + 1
  have hk : ¬ 2 ∣ k := by dsimp [k]; omega
  have hm : 4 * t + 2 = 2 * k := by dsimp [k]; omega
  rw [hm, OMA.A207262.oddDivisors k hk]
  change ArithmeticFunction.sigma (2 * k) (2 * k) =
    (2 ^ (2 * k) + 1) * ArithmeticFunction.sigma (2 * k) k
  have htwo : ArithmeticFunction.sigma (2 * k) 2 = 2 ^ (2 * k) + 1 := by
    simp [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors, Nat.add_comm]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    (Nat.prime_two.coprime_iff_not_dvd.mpr hk), htwo]
