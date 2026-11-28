import OMAStatements.S_oeis_a129654

/-!
Ilya Gutkovskiy's conjectured generating function follows by fixing the
polygonal index r = k+1. Increasing the number of sides by one increases
the value by the triangular number k(k+1)/2. Each allowable index thus
contributes at most one representation of a fixed n.
-/

namespace PolygonalSeries

open Finset PowerSeries OMA.S_oeis_a129654

private def tri (k : ℕ) := k*(k+1)/2

private theorem tri_twice (k : ℕ) : 2 * tri k = k*(k+1) :=
  Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one k)

private theorem tri_pos {k : ℕ} (hk : 0 < k) : 0 < tri k := by
  have h := tri_twice k
  have hp : 0 < k*(k+1) := by positivity
  omega

private theorem polygonal_form (u k : ℕ) :
    polygonal (u+2) (k+1) = ((k+1 + tri k*u : ℕ) : ℤ) := by
  have ht : 2*(tri k : ℤ) = (k : ℤ)*((k : ℤ)+1) := by exact_mod_cast tri_twice k
  unfold polygonal
  push_cast
  have he : ((k : ℤ)+1) * (((u : ℤ)+2-2)*((k : ℤ)+1)-((u : ℤ)+2-4)) =
      2*((k : ℤ)+1+(tri k : ℤ)*u) := by linear_combination -(u : ℤ)*ht
  rw [he]
  omega

private def indices (n : ℕ) : Finset ℕ :=
  (Icc 1 n).filter fun k => k+1 ≤ n ∧ tri k ∣ n-(k+1)

private theorem decode {n m r : ℕ} (hm : 1 < m) (hr : 1 < r) (he : polygonal m r = n) :
    r-1 ∈ indices n ∧ m = (n-r)/tri (r-1)+2 := by
  let k := r-1
  let u := m-2
  have hk : k+1 = r := by dsimp [k]; omega
  have hu : u+2 = m := by dsimp [u]; omega
  have eqn : k+1+tri k*u = n := by
    exact_mod_cast (show ((k+1+tri k*u : ℕ) : ℤ) = n by rw [← polygonal_form, hu, hk]; exact he)
  have hp : 0 < tri k := tri_pos (by dsimp [k]; omega)
  have hdiff : n-r = tri k*u := by omega
  constructor
  · change k ∈ indices n
    apply mem_filter.mpr
    exact ⟨mem_Icc.mpr ⟨by dsimp [k]; omega, by omega⟩, by omega,
      ⟨u, by omega⟩⟩
  · change m = (n-r)/tri k+2
    rw [hdiff, Nat.mul_div_cancel_left _ hp, hu]

private theorem count_indices (n : ℕ) : a n = (indices n).card := by
  unfold a
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun p _ => p.2-1)
  · rintro ⟨m,r⟩ ⟨hm,hr,he⟩
    exact (decode hm hr he).1
  · rintro ⟨m,r⟩ ⟨m',r'⟩ ⟨hm,hr,he⟩ ⟨hm',hr',he'⟩ eqk
    change r-1 = r'-1 at eqk
    have er : r = r' := by omega
    subst r'
    have em := (decode hm hr he).2.trans (decode hm' hr' he').2.symm
    exact Prod.ext em rfl
  · intro k hk
    obtain ⟨hmem, hle, ⟨u, hu⟩⟩ := mem_filter.mp hk
    obtain ⟨hk, _⟩ := mem_Icc.mp hmem
    refine ⟨(u+2,k+1), ⟨by omega, by omega, ?_⟩, by simp⟩
    rw [polygonal_form]
    exact_mod_cast (show k+1+tri k*u = n by omega)

private theorem geom {d : ℕ} (hd : 0 < d) (j : ℕ) :
    coeff j ((1 - (X : ℚ⟦X⟧)^d)⁻¹) = if d ∣ j then 1 else 0 := by
  have hc : constantCoeff (1 - (X : ℚ⟦X⟧)^d) ≠ 0 := by simp [hd.ne']
  have he : (1 - (X : ℚ⟦X⟧)^d)⁻¹ = expand d hd.ne' (mk 1 : ℚ⟦X⟧) := by
    apply (inv_eq_iff_mul_eq_one hc).2
    simpa using congrArg (expand d hd.ne') (mk_one_mul_one_sub_eq_one ℚ)
  rw [he, coeff_expand]
  simp

theorem result : type_of% @OMA.S_oeis_a129654.main := by
  intro n _
  rw [count_indices, map_sum]
  unfold indices
  rw [Finset.natCast_card_filter]
  apply sum_congr rfl
  intro k hk
  have hp := tri_pos (mem_Icc.mp hk).1
  change (if k+1 ≤ n ∧ tri k ∣ n-(k+1) then (1 : ℚ) else 0) =
    coeff n (X * X^k * (1-X^(tri k))⁻¹)
  rw [← pow_succ', coeff_X_pow_mul', geom hp]
  split_ifs <;> simp_all

end PolygonalSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a129654.main := PolygonalSeries.result
