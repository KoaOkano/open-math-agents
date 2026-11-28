import OMAReductions.R_erdos_132_R1_H1_R1
import Mathlib

/-!
# Rare distances on unions of lines

For n points on m ≥ 1 lines, each of the k largest distinct distances has
unordered multiplicity at most 2 m² k. This gives two rare distances when
n ≥ 4 m². Outer layers contain at most two points per line per round and a
circle meets each covering line in at most two points. A related convex-layer
localization appears in section 3 of the Erdős 132 research note:
https://erdosproblems.ai/wiki/research/erdos_132/independent/large_distance_graph_and_convex_extension

Lean formalization by Koa Okano (@KoaOkano) with OpenAI Codex.
-/

open Finset
open scoped Classical
open OMA.S_erdos_132 (pairMultiplicity rareDistances)
namespace OMA.RareLayers

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def lengths (A : Finset Plane) : Finset ℝ :=
  A.offDiag.image (fun p => dist p.1 p.2)

/-- All points that maximize distance from at least one center. -/
noncomputable def outside (A : Finset Plane) : Finset Plane :=
  A.filter (fun p => ∃ q : Plane, ∀ z ∈ A, dist z q ≤ dist p q)

noncomputable def peeled (A : Finset Plane) : ℕ → Finset Plane
  | 0 => A
  | t+1 => peeled (A \ outside A) t

private lemma peeled_subset (A : Finset Plane) (t : ℕ) : peeled A t ⊆ A := by
  induction t generalizing A with
  | zero => exact Subset.rfl
  | succ t ih => exact (ih _).trans sdiff_subset

/-- From a point that survives t layers, every center sees at least t strictly
larger distinct radii in the original set. The center need not survive peeling. -/
lemma peeledRank (A : Finset Plane) (t : ℕ) {p : Plane} (hp : p ∈ peeled A t) (q : Plane) :
    t ≤ ((A.image (fun x => dist x q)).filter (fun d => dist p q < d)).card := by
  classical
  induction t generalizing A with
  | zero => omega
  | succ t ih =>
    let R := A \ outside A
    have hpR : p ∈ R := peeled_subset R t hp
    obtain ⟨inside,notOuter⟩ := mem_sdiff.mp hpR
    obtain ⟨w, hw, far⟩ := A.exists_max_image (fun x => dist x q) ⟨p,inside⟩
    have strict : dist p q < dist w q := by
      by_contra! le
      exact notOuter (mem_filter.mpr ⟨inside,q,fun z hz => (far z hz).trans le⟩)
    let T := (R.image (fun x => dist x q)).filter (fun d => dist p q < d)
    have miss : dist w q ∉ T := by
      intro hit
      obtain ⟨z,hz,eq⟩ := mem_image.mp (mem_filter.mp hit).1
      obtain ⟨zA,zOut⟩ := mem_sdiff.mp hz
      exact zOut (mem_filter.mpr ⟨zA,q,fun y hy => (far y hy).trans_eq eq.symm⟩)
    have incl : insert (dist w q) T ⊆
        (A.image (fun x => dist x q)).filter (fun d => dist p q < d) := by
      intro d hd
      rcases mem_insert.mp hd with rfl | old
      · exact mem_filter.mpr ⟨mem_image.mpr ⟨w,hw,rfl⟩,strict⟩
      obtain ⟨hmem, larger⟩ := mem_filter.mp old
      obtain ⟨z,hz,eq⟩ := mem_image.mp hmem
      exact mem_filter.mpr ⟨mem_image.mpr ⟨z,(mem_sdiff.mp hz).1,eq⟩,larger⟩
    have size := card_le_card incl
    rw [card_insert_of_notMem miss] at size
    exact (Nat.succ_le_succ (ih R hp)).trans size

lemma endpointInLayers {A : Finset Plane} {t : ℕ} {p q : Plane} (hp : p ∈ A) (hq : q ∈ A)
    (rank : ((lengths A).filter (fun d => dist p q < d)).card < t) :
    p ∈ A \ peeled A t := by
  classical
  apply mem_sdiff.mpr ⟨hp,?_⟩
  intro deep
  have incl : (A.image (fun z => dist z q)).filter (fun d => dist p q < d) ⊆
      (lengths A).filter (fun d => dist p q < d) := by
    intro d hd
    obtain ⟨rad,greater⟩ := mem_filter.mp hd
    obtain ⟨z,hz,rfl⟩ := mem_image.mp rad
    have nz : z ≠ q := by
      intro eq
      subst z
      rw [dist_self] at greater
      exact (not_lt_of_ge dist_nonneg) greater
    exact mem_filter.mpr ⟨mem_image.mpr ⟨(z,q),mem_offDiag.mpr ⟨hz,hq,nz⟩,rfl⟩,greater⟩
  exact (not_le_of_gt rank) ((peeledRank A t deep q).trans (card_le_card incl))

private lemma topMembers (S : Finset ℝ) (k : ℕ) (enough : k ≤ S.card) :
    ∃ T ⊆ S, T.card = k ∧ ∀ d ∈ T, (S.filter (d < ·)).card < k := by
  classical
  induction k generalizing S with
  | zero => exact ⟨∅, empty_subset _, rfl, by simp⟩
  | succ k ih =>
    have pos : 0 < S.card := by omega
    let largest := S.max' (card_pos.mp pos)
    have inS : largest ∈ S := S.max'_mem _
    have smaller : k ≤ (S.erase largest).card := by rw [card_erase_of_mem inS]; omega
    obtain ⟨U,sub,size,rank⟩ := ih (S.erase largest) smaller
    have fresh : largest ∉ U := fun h => (mem_erase.mp (sub h)).1 rfl
    refine ⟨insert largest U, insert_subset inS (sub.trans (erase_subset _ _)), ?_, ?_⟩
    · rw [card_insert_of_notMem fresh, size]
    · intro d hd
      rcases mem_insert.mp hd with rfl | hd
      · have none : S.filter (largest < ·) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro y hy
          obtain ⟨inside,gt⟩ := mem_filter.mp hy
          exact (not_lt_of_ge (S.le_max' y inside)) gt
        simp [none]
      · have cover : S.filter (d < ·) ⊆ insert largest ((S.erase largest).filter (d < ·)) := by
          intro y hy
          obtain ⟨inside,gt⟩ := mem_filter.mp hy
          by_cases eq : y = largest
          · exact mem_insert.mpr (Or.inl eq)
          · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_erase.mpr ⟨eq,inside⟩,gt⟩)
        have upper := (card_le_card cover).trans (card_insert_le _ _)
        have old := rank d hd
        omega

/-! ## Point sets covered by a finite family of lines -/

private lemma fewOnLine (T : Finset Plane) (line : Collinear ℝ (T : Set Plane))
    (extreme : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ¬ Sbtw ℝ a b c) : T.card ≤ 2 := by
  by_contra! big
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := Finset.two_lt_card_iff.mp big
  have triple : Collinear ℝ ({a,b,c} : Set Plane) := by
    apply Collinear.subset _ line
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  rcases triple.wbtw_or_wbtw_or_wbtw with mid | mid | mid
  · exact extreme a ha b hb c hc ⟨mid,ab.symm,bc⟩
  · exact extreme b hb c hc a ha ⟨mid,bc.symm,ac.symm⟩
  · exact extreme c hc a ha b hb ⟨mid,ac,ab⟩

private lemma coverCard (W : Finset Plane) (C : Finset (Finset Plane))
    (covered : W ⊆ C.biUnion id) (two : ∀ L ∈ C, (W ∩ L).card ≤ 2) :
    W.card ≤ 2*C.card := by
  classical
  have sub : W ⊆ C.biUnion (fun L => W ∩ L) := by
    intro z hz
    obtain ⟨L,hL,hzL⟩ := mem_biUnion.mp (covered hz)
    exact mem_biUnion.mpr ⟨L,hL,mem_inter.mpr ⟨hz,hzL⟩⟩
  calc
    W.card ≤ (C.biUnion (fun L => W ∩ L)).card := card_le_card sub
    _ ≤ ∑ L ∈ C, (W ∩ L).card := card_biUnion_le
    _ ≤ ∑ _L ∈ C, 2 := sum_le_sum two
    _ = 2*C.card := by simp [Nat.mul_comm]

private lemma subline (W L : Finset Plane) (line : Collinear ℝ (L : Set Plane)) :
    Collinear ℝ ((W ∩ L : Finset Plane) : Set Plane) := by
  exact Collinear.subset (fun _ h => (mem_inter.mp h).2) line

private lemma outsideCover (A : Finset Plane) (C : Finset (Finset Plane))
    (covered : A ⊆ C.biUnion id) (lines : ∀ L ∈ C, Collinear ℝ (L : Set Plane)) :
    (outside A).card ≤ 2*C.card := by
  classical
  apply coverCard _ C ((filter_subset _ _).trans covered)
  intro L hL
  apply fewOnLine _ (subline _ L (lines L hL))
  intro a ha b hb c hc mid
  obtain ⟨_,q,farthest⟩ := mem_filter.mp (mem_inter.mp hb).1
  have haA := (mem_filter.mp (mem_inter.mp ha).1).1
  have hcA := (mem_filter.mp (mem_inter.mp hc).1).1
  exact (not_lt_of_ge (max_le (farthest a haA) (farthest c hcA))) (mid.dist_lt_max_dist q)

private lemma layersCover (A : Finset Plane) (C : Finset (Finset Plane))
    (covered : A ⊆ C.biUnion id) (lines : ∀ L ∈ C, Collinear ℝ (L : Set Plane)) (k : ℕ) :
    (A \ peeled A k).card ≤ 2*C.card*k := by
  classical
  induction k generalizing A with
  | zero => simp [peeled]
  | succ k ih =>
    let B := A \ outside A
    have sub : A \ peeled A (k+1) ⊆ outside A ∪ (B \ peeled B k) := by
      intro z hz
      obtain ⟨ha,deep⟩ := mem_sdiff.mp hz
      by_cases outer : z ∈ outside A
      · exact mem_union_left _ outer
      · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨ha,outer⟩,deep⟩)
    have old := ih B (sdiff_subset.trans covered)
    calc
      _ ≤ _ := card_le_card sub
      _ ≤ (outside A).card + (B \ peeled B k).card := card_union_le _ _
      _ ≤ 2*C.card + 2*C.card*k := Nat.add_le_add (outsideCover A C covered lines) old
      _ = _ := by ring

private lemma neighborsCover (A : Finset Plane) (C : Finset (Finset Plane))
    (covered : A ⊆ C.biUnion id) (lines : ∀ L ∈ C, Collinear ℝ (L : Set Plane))
    (q : Plane) (d : ℝ) : (A.filter (fun p => dist p q = d)).card ≤ 2*C.card := by
  classical
  apply coverCard _ C ((filter_subset _ _).trans covered)
  intro L hL
  apply fewOnLine _ (subline _ L (lines L hL))
  intro a ha b hb c hc mid
  have strict := mid.dist_lt_max_dist q
  rw [(mem_filter.mp (mem_inter.mp ha).1).2,(mem_filter.mp (mem_inter.mp hb).1).2,
    (mem_filter.mp (mem_inter.mp hc).1).2,max_self] at strict
  exact (lt_irrefl d) strict

private lemma distinctCover (A : Finset Plane) (C : Finset (Finset Plane))
    (covered : A ⊆ C.biUnion id) (lines : ∀ L ∈ C, Collinear ℝ (L : Set Plane))
    (ne : A.Nonempty) : A.card - 1 ≤ (lengths A).card * (2*C.card) := by
  classical
  obtain ⟨p,hp⟩ := ne
  let B := A.erase p
  have hit : B.filter (fun z => dist z p ∈ lengths A) = B := by
    apply filter_eq_self.mpr
    intro z hz
    obtain ⟨diff,inside⟩ := mem_erase.mp hz
    exact mem_image.mpr ⟨(z,p),mem_offDiag.mpr ⟨inside,hp,diff⟩,rfl⟩
  calc
    A.card - 1 = B.card := (card_erase_of_mem hp).symm
    _ = ∑ d ∈ lengths A, (B.filter (fun z => dist z p = d)).card := by
      rw [sum_card_fiberwise_eq_card_filter,hit]
    _ ≤ ∑ _d ∈ lengths A, 2*C.card := sum_le_sum fun d _ =>
      neighborsCover B C ((erase_subset _ _).trans covered) lines p d
    _ = _ := by simp

/-- If the n points lie on m lines, each of their k largest distinct distances
occurs in at most 2 m² k unordered pairs. The lines can have arbitrary directions. -/
theorem topMultiplicityCover (A : Finset Plane) (C : Finset (Finset Plane))
    (covered : A ⊆ C.biUnion id) (lines : ∀ L ∈ C, Collinear ℝ (L : Set Plane))
    (k : ℕ) (d : ℝ) (rank : ((lengths A).filter (d < ·)).card < k) :
    pairMultiplicity A d ≤ 2*C.card^2*k := by
  classical
  let W := A \ peeled A k
  let G := (W ×ˢ A).filter (fun p => dist p.2 p.1 = d)
  have incl : A.offDiag.filter (fun p => dist p.1 p.2 = d) ⊆ G := by
    intro p hp
    obtain ⟨pair,eq⟩ := mem_filter.mp hp
    obtain ⟨a,b,_⟩ := mem_offDiag.mp pair
    exact mem_filter.mpr ⟨mem_product.mpr ⟨endpointInLayers a b (by simpa only [eq] using rank),b⟩,
      (dist_comm _ _).trans eq⟩
  have counted : G.card ≤ 2 * (2*C.card^2*k) := by
    calc
      G.card = ∑ x ∈ W, (A.filter (fun z => dist z x = d)).card := by
        simp only [G,card_filter,sum_product]
      _ ≤ ∑ _x ∈ W, 2*C.card := sum_le_sum fun x _ => neighborsCover A C covered lines x d
      _ = W.card * (2*C.card) := by simp
      _ ≤ (2*C.card*k) * (2*C.card) := Nat.mul_le_mul_right _ (layersCover A C covered lines k)
      _ = _ := by ring
  have twice := (card_le_card incl).trans counted
  change (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card / 2 ≤ 2*C.card^2*k
  omega

/-- A cover by m ≥ 1 collinear pieces forces at least k rare distances when
the point count reaches 2 m² k. -/
theorem lineCoverRare (A : Finset Plane) (C : Finset (Finset Plane)) (nonempty : C.Nonempty)
    (covered : A ⊆ C.biUnion id) (lines : ∀ L ∈ C, Collinear ℝ (L : Set Plane))
    (k : ℕ) (many : 2*C.card^2*k ≤ A.card) : k ≤ (rareDistances A).card := by
  classical
  rcases k with _ | t
  · exact Nat.zero_le _
  have pos : 0 < C.card := card_pos.mpr nonempty
  have ne : A.Nonempty := card_pos.mp ((Nat.mul_pos (Nat.mul_pos (by decide) (pow_pos pos 2))
    (Nat.succ_pos t)).trans_le many)
  have enough : t+1 ≤ (lengths A).card := by
    by_contra! few
    have h := distinctCover A C covered lines ne
    have weak := Nat.mul_le_mul_right (2*C.card) (show (lengths A).card ≤ t by omega)
    have sq : C.card ≤ C.card^2 := by simpa [pow_two] using Nat.le_mul_self C.card
    have lower := (Nat.mul_le_mul_right (t+1) (Nat.mul_le_mul_left 2 sq)).trans many
    rw [Nat.mul_succ, Nat.mul_comm (2*C.card) t] at lower
    omega
  obtain ⟨T,sub,size,rank⟩ := topMembers (lengths A) (t+1) enough
  rw [← size]
  apply card_le_card
  intro d hd
  refine mem_filter.mpr ⟨sub hd,OMA.R_erdos_132_R1.multiplicity_pos (sub hd),?_⟩
  exact (topMultiplicityCover A C covered lines _ d (rank d hd)).trans many

end OMA.RareLayers

theorem OMA.solution : OMA.R_erdos_132_R1_H1_R1.H2 := by
  intro A C ne covered lines size
  apply OMA.RareLayers.lineCoverRare A C ne covered lines 2
  linarith
