import OMAReductions.R_erdos_132_R1_H2_R1
import Mathlib

/-!
# Rare distances on complete planar grids

For any two linearly independent axes and any two strictly increasing sequences
of coordinates, an N-point complete grid has at least k rare distances whenever
N ≥ 128 k³. A rare distance occurs on at least one and at most N unordered pairs.

For a pair spanning a given coordinate rectangle, the aligned diagonal is at
least as long. Extending a side of this rectangle strictly increases the aligned
diagonal. Consequently the endpoints of the 2k largest distinct distances lie
among at most 16 k² corner points. Counting all pairs at these distances proves
the bound. The original problem allows arbitrary finite sets in the plane.

Formalization by Koa Okano (@KoaOkano), with OpenAI Codex. The definition of
rare distances is from the registered Erdős–Pach problem statement.
-/

open Finset Filter
open scoped Classical Topology
open OMA.S_erdos_132 (pairMultiplicity rareDistances)
namespace OMA.R_erdos_132_R1_H2_R1

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def distances (A : Finset Plane) : Finset ℝ :=
  A.offDiag.image (fun p => dist p.1 p.2)

/-- Take the largest t distinct values. Rank counts strictly larger values. -/
private theorem topSlice (D : Finset ℝ) (t : ℕ) (enough : t ≤ D.card) :
    ∃ S : Finset ℝ, S ⊆ D ∧ S.card = t ∧
      ∀ d ∈ S, (D.filter (fun v => d < v)).card < t := by
  classical
  induction t generalizing D with
  | zero => exact ⟨∅, by simp, rfl, by simp⟩
  | succ t ih =>
    have ne : D.Nonempty := Finset.card_pos.mp (by omega)
    let m := D.max' ne
    have hm : m ∈ D := D.max'_mem ne
    have small : t ≤ (D.erase m).card := by rw [Finset.card_erase_of_mem hm]; omega
    obtain ⟨S, hS, hs, rank⟩ := ih (D.erase m) small
    have miss : m ∉ S := fun h => (Finset.mem_erase.mp (hS h)).1 rfl
    refine ⟨insert m S, ?_, by simp [miss,hs], ?_⟩
    · exact Finset.insert_subset hm (hS.trans (Finset.erase_subset _ _))
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | belongs
    · have empty : D.filter (fun v => m < v) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        exact (not_lt_of_ge (D.le_max' _ (Finset.mem_filter.mp hv).1)) (Finset.mem_filter.mp hv).2
      simp [empty]
    · have incl : D.filter (fun v => d < v) ⊆ insert m ((D.erase m).filter (fun v => d < v)) := by
        intro v hv
        obtain ⟨hmem, gt⟩ := Finset.mem_filter.mp hv
        by_cases eq : v=m
        · simp [eq]
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨eq,hmem⟩,gt⟩)
      have bound := (Finset.card_le_card incl).trans (Finset.card_insert_le _ _)
      have prev := rank d belongs
      omega

/-- If all pairs at 2k selected distances use a small vertex set, at least k of
those distances occur between at most as many pairs as there are points. -/
theorem rareOfLocalized {A W : Finset Plane} {S : Finset ℝ} {k : ℕ}
    (sub : S ⊆ distances A) (size : 2*k ≤ S.card)
    (corners : ∀ p ∈ A.offDiag, dist p.1 p.2 ∈ S → p.1 ∈ W ∧ p.2 ∈ W)
    (budget : W.card * W.card ≤ 2*k*(A.card+1)) :
    k ≤ (rareDistances A).card := by
  classical
  apply rare_of_sparse sub size
  have incl : A.offDiag.filter (fun p => dist p.1 p.2 ∈ S) ⊆ W ×ˢ W := by
    intro p hp
    obtain ⟨hpair, hit⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_product.mpr (corners p hpair hit)
  exact (Finset.card_le_card incl).trans ((Finset.card_product W W).le.trans budget)

/-- Coordinates need not be equally spaced. The positive coefficients describe
the squared norm along two nonzero axes, oriented so their inner product is nonnegative. -/
structure Grid where
  point : (ℕ × ℕ) ↪ Plane
  x : ℕ → ℝ
  y : ℕ → ℝ
  monoX : StrictMono x
  monoY : StrictMono y
  xx : ℝ
  xy : ℝ
  yy : ℝ
  xx_pos : 0 < xx
  xy_nonneg : 0 ≤ xy
  yy_pos : 0 < yy
  squared : ∀ a b c d : ℕ, dist (point (a,c)) (point (b,d)) ^ 2 =
    xx*(x b-x a)^2 + xy*(x b-x a)*(y d-y c) + yy*(y d-y c)^2

noncomputable def Grid.points (G : Grid) (r s : ℕ) : Finset Plane :=
  ((Finset.range (r+1) ×ˢ Finset.range (s+1)).map G.point)

private theorem gridCard (G : Grid) (r s : ℕ) :
    (G.points r s).card = (r+1)*(s+1) := by simp [Grid.points]

private structure Box where
  left : ℕ
  right : ℕ
  lower : ℕ
  upper : ℕ

private noncomputable def Box.span (w : Box) (G : Grid) :=
  dist (G.point (w.left,w.lower)) (G.point (w.right,w.upper))

private theorem aligned (G : Grid) (i j u v : ℕ) :
    dist (G.point (i,j)) (G.point (u,v)) ≤
      (Box.mk (min i u) (max i u) (min j v) (max j v)).span G := by
  unfold Box.span
  have sq : (dist (G.point (i,j)) (G.point (u,v)))^2 ≤
      (dist (G.point (min i u,min j v)) (G.point (max i u,max j v)))^2 := by
    rw [G.squared, G.squared]
    rcases le_total i u with hi | hi <;> rcases le_total j v with hj | hj
    · simp [min_eq_left hi,max_eq_right hi,min_eq_left hj,max_eq_right hj]
    · simp only [min_eq_left hi,max_eq_right hi,min_eq_right hj,max_eq_left hj]
      have pos := mul_nonneg (mul_nonneg G.xy_nonneg (sub_nonneg.mpr (G.monoX.monotone hi)))
        (sub_nonneg.mpr (G.monoY.monotone hj))
      nlinarith
    · simp only [min_eq_right hi,max_eq_left hi,min_eq_left hj,max_eq_right hj]
      have pos := mul_nonneg (mul_nonneg G.xy_nonneg (sub_nonneg.mpr (G.monoX.monotone hi)))
        (sub_nonneg.mpr (G.monoY.monotone hj))
      nlinarith
    · simp only [min_eq_right hi,max_eq_left hi,min_eq_right hj,max_eq_left hj]
      exact le_of_eq (by ring)
  exact (sq_le_sq₀ dist_nonneg dist_nonneg).mp sq

private theorem spanStrict (G : Grid) {w z : Box}
    (wx : w.left ≤ w.right) (wy : w.lower ≤ w.upper)
    (l : z.left ≤ w.left) (r : w.right ≤ z.right)
    (b : z.lower ≤ w.lower) (t : w.upper ≤ z.upper)
    (changed : z.left < w.left ∨ w.right < z.right ∨ z.lower < w.lower ∨ w.upper < z.upper) :
    w.span G < z.span G := by
  let x := G.x w.right-G.x w.left
  let y := G.y w.upper-G.y w.lower
  let X := G.x z.right-G.x z.left
  let Y := G.y z.upper-G.y z.lower
  have px : 0 ≤ x := sub_nonneg.mpr (G.monoX.monotone wx)
  have py : 0 ≤ y := sub_nonneg.mpr (G.monoY.monotone wy)
  have lx : x ≤ X := sub_le_sub (G.monoX.monotone r) (G.monoX.monotone l)
  have ly : y ≤ Y := sub_le_sub (G.monoY.monotone t) (G.monoY.monotone b)
  have either : x < X ∨ y < Y := by
    rcases changed with h | h | h | h
    · left; dsimp [x,X]; linarith only [G.monoX.monotone r,G.monoX h]
    · left; dsimp [x,X]; linarith only [G.monoX h,G.monoX.monotone l]
    · right; dsimp [y,Y]; linarith only [G.monoY.monotone t,G.monoY h]
    · right; dsimp [y,Y]; linarith only [G.monoY h,G.monoY.monotone b]
  have xxle := mul_le_mul_of_nonneg_left ((sq_le_sq₀ px (px.trans lx)).mpr lx) G.xx_pos.le
  have yyle := mul_le_mul_of_nonneg_left ((sq_le_sq₀ py (py.trans ly)).mpr ly) G.yy_pos.le
  have cross := mul_le_mul_of_nonneg_left (mul_le_mul lx ly py (px.trans lx)) G.xy_nonneg
  apply (sq_lt_sq₀ dist_nonneg dist_nonneg).mp
  rw [G.squared, G.squared]
  change G.xx*x^2 + G.xy*x*y + G.yy*y^2 < G.xx*X^2 + G.xy*X*Y + G.yy*Y^2
  rcases either with h | h
  · have strict := mul_lt_mul_of_pos_left ((sq_lt_sq₀ px (px.trans lx)).mpr h) G.xx_pos
    linarith only [strict,yyle, (show G.xy*x*y ≤ G.xy*X*Y by simpa only [mul_assoc] using cross)]
  · have strict := mul_lt_mul_of_pos_left ((sq_lt_sq₀ py (py.trans ly)).mpr h) G.yy_pos
    linarith only [strict,xxle,(show G.xy*x*y ≤ G.xy*X*Y by simpa only [mul_assoc] using cross)]

private inductive Side | left | right | lower | upper

private def Box.room (w : Box) (r s : ℕ) : Side → ℕ
  | .left => w.left
  | .right => r-w.right
  | .lower => w.lower
  | .upper => s-w.upper

private def Box.stretch (w : Box) (side : Side) (i : ℕ) : Box :=
  match side with
  | .left => { w with left := w.left-i }
  | .right => { w with right := w.right+i }
  | .lower => { w with lower := w.lower-i }
  | .upper => { w with upper := w.upper+i }

private theorem gridMem (G : Grid) {r s i j : ℕ} (hi : i ≤ r) (hj : j ≤ s) :
    G.point (i,j) ∈ G.points r s := by
  refine Finset.mem_map.mpr ⟨(i,j), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩

/-- Successive coordinate extensions of a box provide a chain of distinct
realized distances strictly greater than the distance at its original endpoints. -/
private theorem roomLeRank (G : Grid) {r s : ℕ} (w : Box) (side : Side)
    (xorder : w.left ≤ w.right) (yorder : w.lower ≤ w.upper)
    (xbound : w.right ≤ r) (ybound : w.upper ≤ s)
    {d : ℝ} (positive : 0 ≤ d) (orig : d ≤ w.span G) :
    w.room r s side ≤ ((distances (G.points r s)).filter (fun z => d < z)).card := by
  classical
  have farther {i j : ℕ} (ij : i < j) (hi : j ≤ w.room r s side) :
      (w.stretch side i).span G < (w.stretch side j).span G := by
    apply spanStrict G <;> cases side <;> simp [Box.room,Box.stretch] at * <;> omega
  let f : Fin (w.room r s side) → ℝ := fun i => (w.stretch side (i.val+1)).span G
  have increasing : StrictMono f := by
    intro i j ij
    exact farther (by omega) (by have := j.isLt; omega)
  have incl : Finset.univ.image f ⊆ (distances (G.points r s)).filter (fun z => d < z) := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    have hi : i.val+1 ≤ w.room r s side := i.isLt
    have zero : w.stretch side 0 = w := by cases side <;> simp [Box.stretch]
    have bigger := farther (i := 0) (j := i.val+1) (by omega) hi
    rw [zero] at bigger
    have lt : d < f i := orig.trans_lt bigger
    refine Finset.mem_filter.mpr ⟨?_,lt⟩
    let v := w.stretch side (i.val+1)
    have bx : v.left ≤ r ∧ v.right ≤ r ∧ v.lower ≤ s ∧ v.upper ≤ s := by
      dsimp [v]
      cases side <;> simp [Box.stretch,Box.room] at * <;> omega
    have different : G.point (v.left,v.lower) ≠ G.point (v.right,v.upper) :=
      dist_pos.mp (positive.trans_lt lt)
    refine Finset.mem_image.mpr ⟨(G.point (v.left,v.lower),G.point (v.right,v.upper)), ?_, rfl⟩
    exact Finset.mem_offDiag.mpr ⟨gridMem G bx.1 bx.2.2.1, gridMem G bx.2.1 bx.2.2.2, different⟩
  have bound := Finset.card_le_card incl
  rwa [Finset.card_image_of_injective _ increasing.injective, Finset.card_univ, Fintype.card_fin] at bound

private def ends (r t : ℕ) : Finset ℕ :=
  Finset.range t ∪ (Finset.range t).image (fun j => r-j)

private theorem cardEnds (r t : ℕ) : (ends r t).card ≤ 2*t := by
  unfold ends
  have bound := Finset.card_union_le (Finset.range t) ((Finset.range t).image (fun j => r-j))
  have other := Finset.card_image_le (s := Finset.range t) (f := fun j => r-j)
  simp only [Finset.card_range] at bound other
  omega

private theorem memEnds {a r t : ℕ} (bound : a ≤ r) (near : a < t ∨ r-a < t) :
    a ∈ ends r t := by
  rcases near with left | right
  · exact Finset.mem_union_left _ (Finset.mem_range.mpr left)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨r-a, Finset.mem_range.mpr right, by omega⟩)

/-- For each of the t largest distances, all endpoints lie in the Cartesian
product of the t lowest and highest coordinate ranks along each axis. -/
private theorem cornerPair (G : Grid) {r s t : ℕ} {p : Plane × Plane}
    (onGrid : p ∈ (G.points r s).offDiag)
    (rank : ((distances (G.points r s)).filter (fun z => dist p.1 p.2 < z)).card < t) :
    p.1 ∈ ((ends r t ×ˢ ends s t).map G.point) ∧
    p.2 ∈ ((ends r t ×ˢ ends s t).map G.point) := by
  classical
  obtain ⟨px,py⟩ := p
  obtain ⟨memx,memy,_⟩ := Finset.mem_offDiag.mp onGrid
  obtain ⟨⟨i,j⟩,hij,rfl⟩ := Finset.mem_map.mp memx
  obtain ⟨⟨u,v⟩,huv,rfl⟩ := Finset.mem_map.mp memy
  obtain ⟨bi,bj⟩ := Finset.mem_product.mp hij
  obtain ⟨bu,bv⟩ := Finset.mem_product.mp huv
  simp only [Finset.mem_range] at bi bj bu bv
  let w := Box.mk (min i u) (max i u) (min j v) (max j v)
  have each (side : Side) : w.room r s side < t :=
    (roomLeRank G w side (by dsimp [w]; omega) (by dsimp [w]; omega)
      (by dsimp [w]; omega) (by dsimp [w]; omega) dist_nonneg (aligned G i j u v)).trans_lt rank
  have xl := each .left
  have xr := each .right
  have yl := each .lower
  have yr := each .upper
  simp only [Box.room,w] at xl xr yl yr
  constructor
  · apply Finset.mem_map.mpr
    exact ⟨(i,j),Finset.mem_product.mpr ⟨memEnds (by omega) (by omega),memEnds (by omega) (by omega)⟩,rfl⟩
  · apply Finset.mem_map.mpr
    exact ⟨(u,v),Finset.mem_product.mpr ⟨memEnds (by omega) (by omega),memEnds (by omega) (by omega)⟩,rfl⟩

/-- Uniform in both side lengths, both axes and all coordinate spacings. -/
theorem gridRare (G : Grid) (r s k : ℕ) (large : 128*k^3 ≤ (r+1)*(s+1)) :
    k ≤ (rareDistances (G.points r s)).card := by
  classical
  by_cases zero : k=0
  · simp [zero]
  have pos : 0 < k := by omega
  let A := G.points r s
  let D := distances A
  have side (m : Side) := roomLeRank G (r := r) (s := s) (Box.mk 0 0 0 0) m
    (by decide) (by decide) (Nat.zero_le _) (Nat.zero_le _)
    (d := 0) (by norm_num) (by simp [Box.span])
  have topEnough : 2*k ≤ D.card := by
    have h := Finset.card_filter_le D (fun v => (0:ℝ) < v)
    have hr := (side .right).trans h
    have hs := (side .upper).trans h
    simp only [Box.room,Nat.sub_zero] at hr hs
    by_contra! low
    have lim := Nat.mul_le_mul (show r+1 ≤ 2*k by omega) (show s+1 ≤ 2*k by omega)
    have powle : k^2 ≤ k^3 := by
      rw [pow_succ k 2]
      exact Nat.le_mul_of_pos_right _ pos
    have squarePos : 0 < k^2 := pow_pos pos _
    nlinarith only [large,lim,powle,squarePos]
  obtain ⟨S, hS, size, rank⟩ := topSlice D (2*k) topEnough
  let W := ((ends r (2*k) ×ˢ ends s (2*k)).map G.point)
  have wlim : W.card ≤ 16*k^2 := by
    calc
      W.card = (ends r (2*k)).card*(ends s (2*k)).card := by simp [W]
      _ ≤ (2*(2*k))*(2*(2*k)) := Nat.mul_le_mul (cardEnds _ _) (cardEnds _ _)
      _ = _ := by ring
  apply rareOfLocalized (S := S) (W := W) hS (by omega)
  · intro p hp hd
    exact cornerPair G hp (rank _ hd)
  · calc
      W.card*W.card ≤ (16*k^2)*(16*k^2) := Nat.mul_le_mul wlim wlim
      _ = 2*k*(128*k^3) := by ring
      _ ≤ 2*k*((G.points r s).card+1) :=
        Nat.mul_le_mul_left _ (by rw [gridCard]; omega)

open scoped InnerProductSpace in
/-- Any two independent Euclidean axes, with an acute or right included angle,
give such a chart. Reversing an axis permits this orientation for any finite grid. -/
noncomputable def gridOfAxes (o u v : Plane) (ind : LinearIndependent ℝ ![u,v])
    (angle : 0 ≤ ⟪u,v⟫_ℝ) (x y : ℕ → ℝ) (hx : StrictMono x) (hy : StrictMono y) :
    Grid where
  point := ⟨fun p => o + x p.1 • u + y p.2 • v, by
    intro a b equal
    have cancel : (x a.1-x b.1) • u + (y a.2-y b.2) • v = 0 := by
      rw [sub_smul,sub_smul]
      change o+x a.1 • u+y a.2 • v = o+x b.1 • u+y b.2 • v at equal
      have sumEq : x a.1 • u+y a.2 • v = x b.1 • u+y b.2 • v :=
        add_left_cancel (a := o) (by simpa only [add_assoc] using equal)
      calc
        _ = (x a.1 • u+y a.2 • v)-(x b.1 • u+y b.2 • v) := by abel
        _ = 0 := sub_eq_zero.mpr sumEq
    obtain ⟨one,two⟩ := LinearIndependent.pair_iff.mp ind _ _ cancel
    exact Prod.ext (hx.injective (sub_eq_zero.mp one)) (hy.injective (sub_eq_zero.mp two))⟩
  x := x
  y := y
  monoX := hx
  monoY := hy
  xx := ‖u‖^2
  xy := 2*⟪u,v⟫_ℝ
  yy := ‖v‖^2
  xx_pos := by
    have ne : u ≠ 0 := ind.ne_zero (0:Fin 2)
    exact pow_pos (norm_pos_iff.mpr ne) _
  xy_nonneg := mul_nonneg (by norm_num) angle
  yy_pos := by
    have ne : v ≠ 0 := ind.ne_zero (1:Fin 2)
    exact pow_pos (norm_pos_iff.mpr ne) _
  squared := by
    intro a b c d
    change dist (o+x a • u+y c • v) (o+x b • u+y d • v) ^ 2 = _
    rw [dist_comm,dist_eq_norm]
    have diff : o+x b • u+y d • v-(o+x a • u+y c • v) =
        (x b-x a) • u + (y d-y c) • v := by rw [sub_smul,sub_smul]; abel
    rw [diff,← real_inner_self_eq_norm_sq]
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
      real_inner_self_eq_norm_sq,real_inner_comm v u,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring

/-- This rules out any counterexample sequence consisting of increasingly large grids. -/
theorem gridGrowth (G : Grid) (r s : ℕ → ℕ)
    (grows : Tendsto (fun n => (r n+1)*(s n+1)) atTop atTop) :
    Tendsto (fun n => (rareDistances (G.points (r n) (s n))).card) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [tendsto_atTop.1 grows (128*k^3)] with n hn
  exact gridRare G _ _ _ hn

end OMA.R_erdos_132_R1_H2_R1

theorem OMA.solution : OMA.R_erdos_132_R1_H2_R1.H1 := by
  classical
  intro o u v ind angle x y hx hy r s k large
  let G := OMA.R_erdos_132_R1_H2_R1.gridOfAxes o u v ind angle x y hx hy
  have bound := OMA.R_erdos_132_R1_H2_R1.gridRare G r s k large
  have same : G.points r s = (((range (r+1)) ×ˢ (range (s+1))).image
      (fun p => o + x p.1 • u + y p.2 • v)) := by
    rw [OMA.R_erdos_132_R1_H2_R1.Grid.points, Finset.map_eq_image]
    rfl
  rw [← same]
  exact bound
