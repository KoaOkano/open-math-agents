import OMAStatements.S_oeis_a072348

/-!
Exactly 16 pairs of outer digits make a prime when placed around the
decimal string 4416662, contradicting the proposed strict upper bound.
-/

namespace PrimeFrames

open OMA.S_oeis_a072348

private def hits : Finset (ℕ × ℕ) :=
  {(1,1), (2,1), (2,3), (2,7), (3,3), (3,9), (4,1), (4,7),
   (5,1), (5,7), (6,9), (7,7), (8,3), (8,7), (8,9), (9,3)}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
private theorem table (r s : ℕ) (hr : 1 ≤ r) (hr' : r ≤ 9) (hs : s ≤ 9) :
    (r*100000000 + 44166620 + s).Prime ↔ (r,s) ∈ hits := by
  interval_cases r <;> interval_cases s <;> norm_num [hits]

theorem frame_count : a 4416662 = 16 := by
  let dom := Finset.Icc 1 9 ×ˢ Finset.Icc 0 9
  have inside : hits ⊆ dom := by decide
  have width : (Nat.digits 10 4416662).length = 7 := by decide
  unfold a
  rw [width]
  change (dom.filter (fun rs => (rs.1*100000000 + 44166620 + rs.2).Prime)).card = 16
  have eqset : dom.filter (fun rs => (rs.1*100000000 + 44166620 + rs.2).Prime) = hits := by
    ext ⟨r,s⟩
    rw [Finset.mem_filter]
    have key (hm : (r,s) ∈ dom) := table r s
      (Finset.mem_Icc.mp (Finset.mem_product.mp hm).1).1
      (Finset.mem_Icc.mp (Finset.mem_product.mp hm).1).2
      (Finset.mem_Icc.mp (Finset.mem_product.mp hm).2).2
    exact ⟨fun ⟨hm,hp⟩ => (key hm).mp hp, fun h => ⟨inside h, (key (inside h)).mpr h⟩⟩
  rw [eqset]
  decide

end PrimeFrames

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a072348.main) := by
  intro claim
  have h := claim 4416662 (by decide)
  rw [PrimeFrames.frame_count] at h
  omega
