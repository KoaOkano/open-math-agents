import OMAStatements.S_oeis_a072933

/-!
At the proposed rounded index the two powers eventually lie on opposite
sides of 3. Thus every sufficiently large integer is an exception, and
enumerating these exceptions gives a sequence with asymptotic slope 1.
-/

namespace FloorPowerExceptions

open Filter Topology OMA.S_oeis_a072933

private theorem three_lt_exp : 3 < Real.exp (10987 / 10000) := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (10987/10000 : ℝ)) 9)
  norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem power_bounds {m k : ℕ} (hm : 10000 ≤ m) (hk : 1 ≤ k)
    (hround : (k : ℝ) ≤ (m : ℝ) * 91 / 100 + 1 / 2) :
    3 < (1 + 1 / (k : ℝ))^m ∧ (1 + 1 / (m : ℝ))^k < 3 := by
  have hm' : (10000 : ℝ) ≤ m := by exact_mod_cast hm
  have hk' : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hm0 : 0 < (m : ℝ) := by linarith
  have hkm : (k : ℝ) ≤ m := by linarith
  have loglo : 1 / ((k : ℝ)+1) ≤ Real.log (1 + 1/(k : ℝ)) := by
    have pos : 0 < 1 + 1/(k : ℝ) := by positivity
    calc
      _ = 1 - (1 + 1/(k : ℝ))⁻¹ := by field_simp; ring
      _ ≤ _ := Real.one_sub_inv_le_log_of_pos pos
  have lo : (10987/10000 : ℝ) ≤ (m : ℝ) * (1 / ((k : ℝ)+1)) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    linarith
  have loghi : Real.log (1 + 1/(m : ℝ)) ≤ 1/(m : ℝ) := by
    simpa using Real.log_le_sub_one_of_pos (show 0 < 1 + 1/(m : ℝ) by positivity)
  constructor
  · calc
      (3 : ℝ) < _ := three_lt_exp
      _ ≤ Real.exp ((m : ℝ) * Real.log (1 + 1/(k : ℝ))) :=
        Real.exp_le_exp.mpr (lo.trans (mul_le_mul_of_nonneg_left loglo hm0.le))
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  · calc
      _ = Real.exp ((k : ℝ) * Real.log (1 + 1/(m : ℝ))) := by
        rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
      _ ≤ Real.exp 1 := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ (k : ℝ) * (1/(m : ℝ)) := mul_le_mul_of_nonneg_left loghi hk'.le
          _ ≤ 1 := by rw [mul_one_div, div_le_one hm0]; exact hkm
      _ < 3 := Real.exp_one_lt_d9.trans (by norm_num)

theorem every_large {m : ℕ} (hm : 10000 ≤ m) : isTerm m := by
  refine ⟨by omega, ?_⟩
  intro eq
  let k := leastK m
  have hk : 1 ≤ k ∧ Nat.floor ((1 + 1/(k : ℚ))^m) = Nat.floor ((1 + 1/(m : ℚ))^k) := by
    exact Nat.sInf_mem (s := {j : ℕ | 1 ≤ j ∧
      Nat.floor ((1 + 1/(j : ℚ))^m) = Nat.floor ((1 + 1/(m : ℚ))^j)}) ⟨m, by omega, rfl⟩
  have r := round_le_add_half ((m : ℝ)*91/100)
  rw [← eq] at r
  have bounds := power_bounds hm hk.1 (by exact_mod_cast r)
  have left : (3 : ℚ) < (1 + 1/(k : ℚ))^m := by
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    exact bounds.1
  have right : (1 + 1/(m : ℚ))^k < (3 : ℚ) := by
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    exact bounds.2
  have h₁ : 3 ≤ Nat.floor ((1 + 1/(k : ℚ))^m) := (Nat.le_floor_iff (by positivity)).mpr left.le
  have h₂ : Nat.floor ((1 + 1/(m : ℚ))^k) < 3 := (Nat.floor_lt (by positivity)).mpr right
  omega

theorem true_limit : Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  have inf : (Set.ofPred isTerm).Infinite :=
    (Set.Ici_infinite (10000 : ℕ)).mono (fun _ h => every_large h)
  have lower (n : ℕ) : n ≤ a n := Nat.le_nth (fun hf => (inf hf).elim)
  have upper (n : ℕ) : a n ≤ n+10000 := by
    apply Nat.nth_le_of_strictMonoOn_of_mapsTo (fun j => j+10000)
    · exact fun j _ => every_large (Nat.le_add_left 10000 j)
    · exact fun _ _ _ _ h => Nat.add_lt_add_right h 10000
  have hi : Tendsto (fun n : ℕ => 1 + (10000 : ℝ)/n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (10000 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hi
  · filter_upwards [eventually_ge_atTop 1] with n hn
    apply (one_le_div (by exact_mod_cast (by omega : 0 < n))).mpr
    exact_mod_cast lower n
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [show 1 + (10000 : ℝ)/n = ((n : ℝ)+10000)/n by
      rw [add_div, div_self hpos.ne']]
    exact div_le_div_of_nonneg_right (by exact_mod_cast upper n) hpos.le

end FloorPowerExceptions

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a072933.main) := by
  intro h
  have bad := tendsto_nhds_unique FloorPowerExceptions.true_limit h
  norm_num at bad
