import OMAReductions.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! Formalization by KoaOkano.

A deficiency bound for the 22-vertex entry of Table 3 in Goedgebeur and
Radziszowski, *New computational upper bounds for Ramsey numbers R(3,k)*.
Deleting one vertex propagates the 16-vertex bound to orders 17 and 18.
Summing over non-neighborhoods then yields the required 59 edges.
The published table gives 60 at this order. Here the registry asks for
the weaker inequality with 59. The 15- and 16-vertex bounds are both
proved below. -/
open SimpleGraph Finset
namespace OMA.RamseyTwentyTwo

def EdgeBound (n k lower : ℕ) : Prop := ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  G.CliqueFree 3 → Gᶜ.CliqueFree k → lower ≤ G.edgeFinset.card

/-- The 15-vertex entry of the (3,6) edge table. -/
def Fifteen : Prop := EdgeBound 15 6 25

/-- The 16-vertex entry of the (3,6) edge table. -/
def Sixteen : Prop := EdgeBound 16 6 32

theorem inherited {n k lower : ℕ} (small : EdgeBound n k lower) {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : n ≤ Fintype.card V) (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree k) :
    lower ≤ G.edgeFinset.card := by
  classical
  obtain ⟨f, _⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin n)
    (s := (univ : Finset V)) (by simpa using hc)
  let e := SimpleGraph.Embedding.comap f G
  have a := small (G.comap f) (CliqueFree.comap e.isContained ht)
    (CliqueFree.comap (SimpleGraph.Embedding.complEquiv e).isContained hi)
  have b := Fintype.card_le_of_embedding e.toCopy.mapEdgeSet
  rw [(G.comap f).card_edgeSet,G.card_edgeSet] at b
  exact a.trans b

theorem deletedAverage {n k lower : ℕ} (small : EdgeBound n k lower)
    (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj] (ht : G.CliqueFree 3)
    (hi : Gᶜ.CliqueFree k) :
    (n+1)*lower + 2*G.edgeFinset.card ≤ (n+1)*G.edgeFinset.card := by
  classical
  have point (v : Fin (n+1)) : lower + G.degree v ≤ G.edgeFinset.card := by
    let S := ({v}ᶜ : Set (Fin (n+1)))
    let e := SimpleGraph.Embedding.induce (G := G) S
    have hc : n ≤ Fintype.card S := by
      change n ≤ Fintype.card ({v}ᶜ : Set (Fin (n+1)))
      rw [Fintype.card_compl_set, Fintype.card_fin, Fintype.card_unique]
      omega
    have h := inherited small (G.induce S) hc (CliqueFree.comap e.isContained ht)
      (CliqueFree.comap (SimpleGraph.Embedding.complEquiv e).isContained hi)
    change lower ≤ (G.induce {v}ᶜ).edgeFinset.card at h
    rw [G.card_edgeFinset_induce_compl_singleton,
      G.card_edgeFinset_deleteIncidenceSet] at h
    have := G.degree_le_card_edgeFinset v
    omega
  have h := Finset.sum_le_sum (s := (univ : Finset (Fin (n+1)))) (fun v _ => point v)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,G.sum_degrees_eq_twice_card_edges] using h

theorem outside {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree (k+1)) :
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin n))
    D.CliqueFree 3 ∧ Dᶜ.CliqueFree k := by
  classical
  let B := Gᶜ.neighborFinset v
  let f : B ↪ Fin n := Function.Embedding.subtype _
  let e := SimpleGraph.Embedding.comap f G
  refine ⟨CliqueFree.comap e.isContained ht, ?_⟩
  intro K hK
  have cl : Gᶜ.IsClique (K.map f) := by
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact ⟨hxy,(hK.isClique ha hb (fun eq => hxy (congrArg f eq))).2⟩
  have fresh : v ∉ K.map f := by
    rintro mem
    obtain ⟨b,_,eq⟩ := mem_map.mp mem
    exact ((Gᶜ.mem_neighborFinset _ _).mp b.property).ne eq.symm
  apply hi (insert v (K.map f))
  refine ⟨?_,by rw [card_insert_of_notMem fresh,card_map,hK.card_eq]⟩
  rw [Finset.coe_insert]
  apply cl.insert
  intro b hb _
  obtain ⟨i,_,rfl⟩ := mem_map.mp hb
  exact (Gᶜ.mem_neighborFinset _ _).mp i.property

theorem fromSmallerOrders : Fifteen → Sixteen → OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1.H1 := by
  intro b15 b16
  have b17 : EdgeBound 17 6 37 := by
    intro G _ ht hi
    have h := deletedAverage (n := 16) b16 G ht hi
    omega
  have b18 : EdgeBound 18 6 42 := by
    intro G _ ht hi
    have h := deletedAverage (n := 17) b17 G ht hi
    omega
  intro G inst ht hi
  let Z (v) := ∑ a ∈ G.neighborFinset v, G.degree a
  have point (v : Fin 22) : 37 + 4*G.degree v + Z v ≤ G.degree v ^ 2 + G.edgeFinset.card := by
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin 22))
    obtain ⟨t,i⟩ := outside (k := 6) G v ht hi
    have deg := OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1.degree_lt G ht hi v
    have size : Fintype.card B = 21-G.degree v := by
      rw [Fintype.card_coe]
      change Gᶜ.degree v = 21-G.degree v
      rw [G.degree_compl,Fintype.card_fin]
    have rem : D.edgeFinset.card + Z v ≤ G.edgeFinset.card :=
      OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1.removed G ht v
    by_cases low : G.degree v ≤ 3
    · have hc : 18 ≤ Fintype.card B := by omega
      have b := inherited b18 D hc t i
      have poly : ∀ d : Fin 4, 37+4*d.val ≤ d.val^2+42 := by decide
      have q := poly ⟨G.degree v, by omega⟩
      change 37+4*G.degree v ≤ G.degree v^2+42 at q
      omega
    · have cases : G.degree v = 4 ∨ G.degree v = 5 ∨ G.degree v = 6 := by omega
      rcases cases with h|h|h
      · have hc : 17 ≤ Fintype.card B := by omega
        have b := inherited b17 D hc t i
        rw [h]
        omega
      · have hc : 16 ≤ Fintype.card B := by omega
        have b := inherited (show EdgeBound 16 6 32 from b16) D hc t i
        rw [h]
        omega
      · have hc : 15 ≤ Fintype.card B := by omega
        have b := inherited (show EdgeBound 15 6 25 from b15) D hc t i
        rw [h]
        omega
  have s := Finset.sum_le_sum (s := (univ : Finset (Fin 22))) (fun v _ => point v)
  have z : (∑ v,Z v) = ∑ v,G.degree v^2 :=
    OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1.sum_neighbor_degrees G
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,z,G.sum_degrees_eq_twice_card_edges] at s
  omega

end OMA.RamseyTwentyTwo

/- Goedgebeur and Radziszowski, *New computational upper bounds for Ramsey
numbers R(3,k)*, Table 3, give 25 as the minimum edge count at order 15.
A supporting line for the non-neighborhood edge bound is summed over all
vertices. The two global identities count edges and length-two walks.
Table entries with value 1000 represent impossible orders. The degree
bound implies at most 37 edges for every graph in this calculation. -/
open SimpleGraph Finset
namespace OMA.RamseyFifteen
open OMA.RamseyTwentyTwo

private theorem supportingLine {n k lower A B C : ℕ} (cost : Fin (k+1) → ℕ)
    (rows : ∀ d, EdgeBound (n-1-d.val) k (cost d))
    (line : ∀ d, A*d.val+B ≤ C*(d.val^2+cost d))
    (finish : ∀ e : ℕ, 2*e ≤ n*k → A*(2*e)+n*B ≤ C*(n*e) → lower ≤ e) :
    EdgeBound n (k+1) lower := by
  intro G inst ht hi
  let Z (v) := ∑ w ∈ G.neighborFinset v, G.degree w
  have cap (v : Fin n) : G.degree v < k+1 :=
    OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1.degree_lt G ht hi v
  have point (v : Fin n) : A*G.degree v + B + C*Z v ≤
      C*G.degree v^2 + C*G.edgeFinset.card := by
    let d : Fin (k+1) := ⟨G.degree v,cap v⟩
    let S := Gᶜ.neighborFinset v
    let D := G.induce (S : Set (Fin n))
    have card : n-1-d.val ≤ Fintype.card S := by
      rw [Fintype.card_coe]
      change n-1-G.degree v ≤ Gᶜ.degree v
      rw [G.degree_compl,Fintype.card_fin]
    obtain ⟨t,i⟩ := outside (k := k) G v ht hi
    have bound := inherited (rows d) D card t i
    have rem : D.edgeFinset.card + Z v ≤ G.edgeFinset.card :=
      OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1.removed G ht v
    have lc : A*G.degree v+B ≤ C*(G.degree v^2+cost d) := line d
    have upper := Nat.mul_le_mul_left C ((Nat.add_le_add_right bound (Z v)).trans rem)
    rw [Nat.mul_add] at lc upper
    omega
  have z : (∑ v, Z v) = ∑ v, G.degree v^2 :=
    OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1.sum_neighbor_degrees G
  have h := Finset.sum_le_sum (s := (univ : Finset (Fin n))) (fun v _ => point v)
  have top := Finset.sum_le_sum (s := (univ : Finset (Fin n)))
    (f := fun v => G.degree v) (g := fun _ => k) (fun v _ => Nat.le_of_lt_succ (cap v))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,z,G.sum_degrees_eq_twice_card_edges] at h top
  apply finish _ top
  omega

private theorem zeroBound (n k : ℕ) : EdgeBound n k 0 := by
  intro G inst ht hi
  exact Nat.zero_le _

private theorem singletonBound (n : ℕ) : EdgeBound (n+1) 1 1000 := by
  intro G inst ht hi
  exact (SimpleGraph.cliqueFree_one.mp hi).elim' (0 : Fin (n+1))


private theorem entry2_3 : EdgeBound 3 2 1000 := by
  apply supportingLine (k := 1) (A := 0) (B := 1000) (C := 1)
    ![1000, 1000] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact singletonBound 1
  · exact singletonBound 0

private theorem entry2_4 : EdgeBound 4 2 1000 := by
  intro G inst ht hi
  exact inherited (entry2_3) G (by decide) ht hi

private theorem entry2_5 : EdgeBound 5 2 1000 := by
  intro G inst ht hi
  exact inherited (entry2_4) G (by decide) ht hi

private theorem entry3_6 : EdgeBound 6 3 1000 := by
  apply supportingLine (k := 2) (A := 0) (B := 1000) (C := 1)
    ![1000, 1000, 1000] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry2_5
  · exact entry2_4
  · exact entry2_3

private theorem entry3_7 : EdgeBound 7 3 1000 := by
  intro G inst ht hi
  exact inherited (entry3_6) G (by decide) ht hi

private theorem entry3_8 : EdgeBound 8 3 1000 := by
  intro G inst ht hi
  exact inherited (entry3_7) G (by decide) ht hi

private theorem entry2_2 : EdgeBound 2 2 1 := by
  apply supportingLine (k := 1) (A := 0) (B := 1) (C := 1)
    ![1000, 0] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact singletonBound 0
  · exact zeroBound 0 1

private theorem entry3_5 : EdgeBound 5 3 5 := by
  apply supportingLine (k := 2) (A := 0) (B := 5) (C := 1)
    ![1000, 1000, 1] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry2_4
  · exact entry2_3
  · exact entry2_2

private theorem entry4_9 : EdgeBound 9 4 1000 := by
  apply supportingLine (k := 3) (A := 0) (B := 14) (C := 1)
    ![1000, 1000, 1000, 5] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry3_8
  · exact entry3_7
  · exact entry3_6
  · exact entry3_5

private theorem entry4_10 : EdgeBound 10 4 1000 := by
  intro G inst ht hi
  exact inherited (entry4_9) G (by decide) ht hi

private theorem entry4_11 : EdgeBound 11 4 1000 := by
  intro G inst ht hi
  exact inherited (entry4_10) G (by decide) ht hi

private theorem entry4_12 : EdgeBound 12 4 1000 := by
  intro G inst ht hi
  exact inherited (entry4_11) G (by decide) ht hi

private theorem entry4_13 : EdgeBound 13 4 1000 := by
  intro G inst ht hi
  exact inherited (entry4_12) G (by decide) ht hi

private theorem entry5_14 : EdgeBound 14 5 1000 := by
  apply supportingLine (k := 4) (A := 0) (B := 1000) (C := 1)
    ![1000, 1000, 1000, 1000, 1000] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry4_13
  · exact entry4_12
  · exact entry4_11
  · exact entry4_10
  · exact entry4_9

private theorem entry3_4 : EdgeBound 4 3 2 := by
  apply supportingLine (k := 2) (A := 0) (B := 2) (C := 1)
    ![1000, 1, 0] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry2_3
  · exact entry2_2
  · exact zeroBound 1 2

private theorem entry4_8 : EdgeBound 8 4 10 := by
  apply supportingLine (k := 3) (A := 1) (B := 7) (C := 1)
    ![1000, 1000, 5, 2] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry3_7
  · exact entry3_6
  · exact entry3_5
  · exact entry3_4

private theorem entry5_13 : EdgeBound 13 5 26 := by
  apply supportingLine (k := 4) (A := 0) (B := 26) (C := 1)
    ![1000, 1000, 1000, 1000, 10] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry4_12
  · exact entry4_11
  · exact entry4_10
  · exact entry4_9
  · exact entry4_8

private theorem entry3_3 : EdgeBound 3 3 1 := by
  apply supportingLine (k := 2) (A := 0) (B := 1) (C := 1)
    ![1, 0, 0] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry2_2
  · exact zeroBound 1 2
  · exact zeroBound 0 2

private theorem entry4_7 : EdgeBound 7 4 6 := by
  apply supportingLine (k := 3) (A := 0) (B := 6) (C := 1)
    ![1000, 5, 2, 1] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry3_6
  · exact entry3_5
  · exact entry3_4
  · exact entry3_3

private theorem entry5_12 : EdgeBound 12 5 20 := by
  apply supportingLine (k := 4) (A := 1) (B := 16) (C := 1)
    ![1000, 1000, 1000, 10, 6] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry4_11
  · exact entry4_10
  · exact entry4_9
  · exact entry4_8
  · exact entry4_7

private theorem entry4_6 : EdgeBound 6 4 3 := by
  apply supportingLine (k := 3) (A := 0) (B := 3) (C := 1)
    ![5, 2, 1, 0] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry3_5
  · exact entry3_4
  · exact entry3_3
  · exact zeroBound 2 3

private theorem entry5_11 : EdgeBound 11 5 15 := by
  apply supportingLine (k := 4) (A := 1) (B := 12) (C := 1)
    ![1000, 1000, 10, 6, 3] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry4_10
  · exact entry4_9
  · exact entry4_8
  · exact entry4_7
  · exact entry4_6

private theorem entry4_5 : EdgeBound 5 4 2 := by
  apply supportingLine (k := 3) (A := 0) (B := 2) (C := 1)
    ![2, 1, 0, 0] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry3_4
  · exact entry3_3
  · exact zeroBound 2 3
  · exact zeroBound 1 3

private theorem entry5_10 : EdgeBound 10 5 10 := by
  apply supportingLine (k := 4) (A := 0) (B := 10) (C := 1)
    ![1000, 10, 6, 3, 2] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry4_9
  · exact entry4_8
  · exact entry4_7
  · exact entry4_6
  · exact entry4_5

private theorem entry4_4 : EdgeBound 4 4 1 := by
  apply supportingLine (k := 3) (A := 0) (B := 1) (C := 1)
    ![1, 0, 0, 0] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry3_3
  · exact zeroBound 2 3
  · exact zeroBound 1 3
  · exact zeroBound 0 3

private theorem entry5_9 : EdgeBound 9 5 7 := by
  apply supportingLine (k := 4) (A := 0) (B := 7) (C := 1)
    ![10, 6, 3, 2, 1] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry4_8
  · exact entry4_7
  · exact entry4_6
  · exact entry4_5
  · exact entry4_4

private theorem entry6_15 : EdgeBound 15 6 25 := by
  apply supportingLine (k := 5) (A := 1) (B := 21) (C := 1)
    ![1000, 26, 20, 15, 10, 7] ?_ (by decide) (by intro e he h; omega)
  intro d
  fin_cases d
  · exact entry5_14
  · exact entry5_13
  · exact entry5_12
  · exact entry5_11
  · exact entry5_10
  · exact entry5_9

end OMA.RamseyFifteen

theorem OMA.RamseyFifteen.atLeast25 : OMA.RamseyTwentyTwo.Fifteen := OMA.RamseyFifteen.entry6_15

/- Goedgebeur and Radziszowski, *New computational upper bounds for Ramsey
numbers R(3,k)*, Table 3, give 32 as the minimum number of edges of a
triangle-free 16-vertex graph without an independent six-set.

The graph encoding, minimum-degree decomposition, relabellings and smaller
graph catalogue below are adapted from Deldor14's checked 17-vertex proof
(open-math-agents #5749), which credits TheWaler's neighborhood method
(#2943). The 16-vertex reduction and the thirteen integer-weight
certificates in this file specialize the calculation to the smaller order.
The kernel checks the base catalogue and each weighted incidence inequality. -/

open SimpleGraph
namespace OMA.RamseySixteen

private def bits : List Bool → Nat
  | [] => 0
  | b::bs => 2 * bits bs + b.toNat

private theorem bits_lt (b : List Bool) : bits b < 2 ^ b.length := by
  induction b with
  | nil => decide
  | cons a l ih => cases a <;> simp [bits, pow_succ] <;> omega

private theorem bits_append (a b : List Bool) : bits (a ++ b) = bits a + 2 ^ a.length * bits b := by
  induction a with
  | nil => simp [bits]
  | cons c a ih => simp [bits, ih, pow_succ]; ring

private theorem bits_replicate_false (n : Nat) : bits (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bits, ih]

private theorem bits_replicate_true (n : Nat) : bits (List.replicate n true) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bits, pow_succ]; omega

private def encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] : List V → List Nat
  | [] => []
  | v::vs => bits (vs.map fun x => decide (G.Adj v x)) :: encode G vs

private def shifted : List Nat → List Nat
  | [] => []
  | s::ss => 2 ^ ss.length * s :: shifted ss

private def attach (blocks base : List Nat) : List Nat :=
  (2 ^ blocks.length - 1) :: (shifted blocks ++ base)

private theorem contacts {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (front base : List V) (hi : ∀ x ∈ front, ∀ y ∈ front, ¬ G.Adj x y) :
    encode G (front ++ base) =
      shifted (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) ++ encode G base := by
  induction front with
  | nil => rfl
  | cons a as ih =>
    have nh (x) (hx : x∈as) := hi a (by simp) x (by simp [hx])
    have nils : as.map (fun x => decide (G.Adj a x)) = List.replicate as.length false := by
      apply List.eq_replicate_iff.mpr
      exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [nh b hb]⟩
    simp [encode, shifted, bits_append, nils, bits_replicate_false,
      ih (fun x hx y hy => hi x (by simp [hx]) y (by simp [hy]))]

private theorem root_encoding {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (front base : List V) (hfront : ∀ x∈front, G.Adj r x)
    (hbase : ∀ x∈base, ¬ G.Adj r x) (ht : G.CliqueFree 3) :
    encode G (r::front++base) = attach
      (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) (encode G base) := by
  have hf : front.map (fun x => decide (G.Adj r x)) = List.replicate front.length true := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [hfront b hb]⟩
  have hb : base.map (fun x => decide (G.Adj r x)) = List.replicate base.length false := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [hbase b hb]⟩
  have hi (x) (hx : x ∈ front) (y) (hy : y ∈ front) (h : G.Adj x y) : False :=
    G.isIndepSet_neighborSet_of_triangleFree ht r (hfront x hx) (hfront y hy) h.ne h
  simp [encode, attach, bits_append, hf, hb, bits_replicate_false, contacts G front base hi]
  have := bits_replicate_true front.length
  omega

private def mark {V : Type*} [DecidableEq V] (vs : List V) (s : Finset V) : Nat :=
  bits (vs.map fun x => decide (x ∈ s))

private theorem bit_form (b : Bool) (n : Nat) : Nat.bit b n = 2 * n + b.toNat := by
  cases b <;> simp [Nat.bit, Nat.two_mul]

private theorem and_mask {V : Type*} (vs : List V) (f g : V → Bool) :
    bits (vs.map f) &&& bits (vs.map g) = 0 ↔ ∀ x ∈ vs, f x = true → g x = false := by
  induction vs with
  | nil => simp [bits]
  | cons a l ih =>
    simp only [List.map_cons, bits, ← bit_form, Nat.land_bit, List.forall_mem_cons]
    rw [bit_form]
    cases f a <;> cases g a <;> simp [ih]

private def ind0 (p : Nat × Nat) : Nat × Nat := (2*p.1,p.2)
private def ind1 (p : Nat × Nat) : Nat × Nat := (2*p.1+1,p.2+1)

private def inds : List Nat → List (Nat × Nat)
  | [] => [(0,0)]
  | m::rows =>
    let t := inds rows
    t.map ind0 ++ (t.filter fun p => m &&& p.1 == 0).map ind1

private theorem mark_congr {V : Type*} [DecidableEq V] (vs : List V) (s t : Finset V)
    (h : ∀ x∈vs, x∈s ↔ x∈t) : mark vs s = mark vs t := by
  unfold mark
  congr 1
  exact List.map_congr_left (fun x hx => by simp only [h x hx])

private theorem inds_sound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hn : vs.Nodup) {p : Nat × Nat} (hp : p ∈ inds (encode G vs)) :
    ∃ S : Finset V, S ⊆ vs.toFinset ∧ Gᶜ.IsClique (S : Set V) ∧ p = (mark vs S,S.card) := by
  induction vs generalizing p with
  | nil =>
    simp [encode,inds] at hp
    exact ⟨∅,by simp,by simp,by simp [hp,mark,bits]⟩
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [encode,inds,List.mem_append,List.mem_map,List.mem_filter] at hp
    rcases hp with ⟨q,hq,rfl⟩ | ⟨q,⟨hq,hd⟩,rfl⟩
    · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
      have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
      exact ⟨S,by simpa using hS.trans (Finset.subset_insert a _),hI,by simp [ind0,mark,bits,ha]⟩
    · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
      have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
      have hz := (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈S))).mp (beq_iff_eq.mp hd)
      have hi : Gᶜ.IsClique (insert a S : Finset V) := by
        rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem ha]
        refine ⟨hI,fun x hx => ⟨?_,?_⟩⟩
        · exact fun e => ha (e ▸ hx)
        · intro adj
          have := hz x (List.mem_toFinset.mp (hS hx)) (by simpa using adj)
          exact (of_decide_eq_false this) hx
      have hm := mark_congr l (insert a S) S (by intro x hx; simp [show x ≠ a from fun e => hn'.1 (e ▸ hx)])
      refine ⟨insert a S, by simpa using Finset.insert_subset_insert a hS, hi, ?_⟩
      simp [ind1,mark,bits,Finset.card_insert_of_notMem ha] at hm ⊢
      omega

private theorem inds_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hn : vs.Nodup) (S : Finset V) (hS : S ⊆ vs.toFinset) (hI : Gᶜ.IsClique (S : Set V)) :
    (mark vs S,S.card) ∈ inds (encode G vs) := by
  induction vs generalizing S with
  | nil =>
    have e : S=∅ := Finset.subset_empty.mp (by simpa using hS)
    simp [e,encode,inds,mark,bits]
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [encode,inds,List.mem_append,List.mem_map,List.mem_filter]
    by_cases ha : a ∈ S
    · let T := S.erase a
      have hT : T ⊆ l.toFinset := by
        intro x hx
        have m := Finset.mem_erase.mp hx
        have h := List.mem_cons.mp (List.mem_toFinset.mp (hS m.2))
        exact List.mem_toFinset.mpr (h.resolve_left m.1)
      have hI' := hI.subset (show (T : Set V) ⊆ (S : Set V) from Finset.erase_subset ..)
      have hmark := mark_congr l S T (by intro x hx; simp [T,show x≠a from fun e => hn'.1 (e ▸ hx)])
      have hcard : T.card + 1 = S.card := Finset.card_erase_add_one ha
      right
      refine ⟨(mark l T,T.card),⟨ih hn'.2 T hT hI', ?_⟩,?_⟩
      · apply beq_iff_eq.mpr
        apply (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈T))).mpr
        intro x _ hx
        apply decide_eq_false
        intro hm
        have hmem := Finset.mem_erase.mp hm
        exact (hI ha hmem.2 hmem.1.symm).2 (of_decide_eq_true hx)
      · simp [ind1,mark,bits,ha,hcard] at hmark ⊢
        omega
    · have hT : S ⊆ l.toFinset := by
        intro x hx
        have h := List.mem_cons.mp (List.mem_toFinset.mp (hS hx))
        exact List.mem_toFinset.mpr (h.resolve_left (fun e => ha (e ▸ hx)))
      exact Or.inl ⟨_,ih hn'.2 S hT hI,by simp [ind0,mark,bits,ha]⟩


private def countBits : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,x => (x%2) + countBits n (x/2)

private def bump (m : Nat) : List Nat → List Nat
  | [] => []
  | x::xs => (x+m%2)::bump (m/2) xs

private def degrees : List Nat → List Nat
  | [] => []
  | m::ms => countBits ms.length m :: bump m (degrees ms)

private def sizeAt {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) (x : V) :=
  (vs.filter fun y => decide (G.Adj x y)).length

private theorem half_step (x : Nat) : (2*x+1)/2=x := by omega

private theorem count_map {V : Type*} (vs : List V) (f : V → Bool) :
    countBits vs.length (bits (vs.map f)) = (vs.filter f).length := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    cases ha : f a <;> simp [countBits,bits,ha,ih,half_step]
    omega

private theorem bump_map {V : Type*} (vs : List V) (f : V → Bool) (d : V → Nat) :
    bump (bits (vs.map f)) (vs.map d) = vs.map (fun x => d x + (f x).toNat) := by
  induction vs with
  | nil => rfl
  | cons a l ih => cases ha : f a <;> simp [bump,bits,ha,ih,half_step]

private theorem encode_length {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    (encode G vs).length=vs.length := by induction vs with | nil => rfl | cons a as ih => simp [encode,ih]

private theorem degrees_encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    degrees (encode G vs) = vs.map (sizeAt G vs) := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    simp only [encode,degrees,encode_length,count_map,ih,bump_map,List.map_cons,List.cons.injEq]
    refine ⟨by simp [sizeAt], List.map_congr_left ?_⟩
    intro x _
    by_cases h : G.Adj a x <;> simp [sizeAt,h,G.adj_comm x a]

private theorem sizeAt_finset {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {vs : List V} (hn : vs.Nodup) (x : V) :
    sizeAt G vs x = (vs.toFinset.filter (G.Adj x)).card := by
  have h := List.toFinset_filter vs (fun y => decide (G.Adj x y))
  simp only [decide_eq_true_eq] at h
  rw [← h, List.toFinset_card_of_nodup (hn.filter _)]
  rfl


private def Small {V : Type*} (G : SimpleGraph V) (A : Finset V) (k : Nat) :=
  ∀ I ⊆ A, Gᶜ.IsClique (I : Set V) → I.card < k

private theorem row_mark {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (base : List V) (x : V) :
    bits (base.map fun y => decide (G.Adj x y)) = mark base (base.toFinset.filter (G.Adj x)) := by
  unfold mark
  congr 1
  exact List.map_congr_left (fun y hy => by simp [hy])

private theorem neighbors_small {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (x : V) :
    Gᶜ.IsClique ((A.filter (G.Adj x) : Finset V) : Set V) := by
  rw [G.isClique_compl]
  intro y hy z hz hn
  exact G.isIndepSet_neighborSet_of_triangleFree ht x (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2 hn

private theorem degrees_bound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (k : Nat) (hs : Small G A k)
    (l : List V) (hn : l.Nodup) (hsub : l.toFinset ⊆ A) :
    (degrees (encode G l)).all (· < k) = true := by
  rw [degrees_encode, List.all_eq_true]
  intro y hy
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hy
  simp only [decide_eq_true_eq, sizeAt_finset G hn]
  exact hs _ ((Finset.filter_subset _ _).trans hsub) (neighbors_small G ht _ x)

private def okContacts (k : Nat) (isets : List (Nat × Nat)) (cs : List Nat) : Bool :=
  isets.all fun p => p.2 + (cs.filter fun v => v &&& p.1 == 0).length < k

private theorem ok_contacts {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : Nat) (hs : Small G A k) (front base : List V)
    (hn : (front++base).Nodup) (hsub : (front++base).toFinset ⊆ A)
    (hi : Gᶜ.IsClique (front.toFinset : Set V)) :
    okContacts k (inds (encode G base)) (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) := by
  rw [okContacts,List.all_eq_true]
  intro q hq
  obtain ⟨hh,hb,hd⟩ := List.nodup_append.mp hn
  obtain ⟨S,hS,hI,rfl⟩ := inds_sound G base hb hq
  let pred (v : V) : Bool := bits (base.map fun y => decide (G.Adj v y)) &&& mark base S == 0
  let F := front.filter pred
  have hF (x) (hx : x∈F) : x∈front := (List.mem_filter.mp hx).1
  have sep (x) (hx : x∈F) (y) (hy : y∈S) : Gᶜ.Adj x y := by
    have hx' := List.mem_filter.mp hx
    have hy' := List.mem_toFinset.mp (hS hy)
    have neq : x ≠ y := hd x hx'.1 y hy'
    exact ⟨neq,fun ha => by
      have e := (and_mask base (fun z => decide (G.Adj x z)) (fun z => decide (z ∈ S))).mp
        (beq_iff_eq.mp hx'.2) y hy' (by simpa using ha)
      exact of_decide_eq_false e hy⟩
  have sub : F.toFinset ∪ S ⊆ A := by
    apply Finset.union_subset
    · exact fun x hx => hsub (by simp [hF x (List.mem_toFinset.mp hx)])
    · exact fun x hx => hsub (by simp [List.mem_toFinset.mp (hS hx)])
  have together : Gᶜ.IsClique ((F.toFinset ∪ S : Finset V) : Set V) := by
    rw [Finset.coe_union, SimpleGraph.IsClique, Set.pairwise_union]
    refine ⟨hi.subset ?_,hI,?_⟩
    · exact fun x hx => List.mem_toFinset.mpr (hF x (List.mem_toFinset.mp hx))
    · intro x hx y hy _
      exact ⟨sep x (List.mem_toFinset.mp hx) y hy,(sep x (List.mem_toFinset.mp hx) y hy).symm⟩
  have dis : Disjoint F.toFinset S := Finset.disjoint_left.mpr fun x hx hy =>
    (sep x (List.mem_toFinset.mp hx) x hy).ne rfl
  have w := hs _ sub together
  rw [Finset.card_union_of_disjoint dis,List.toFinset_card_of_nodup (hh.filter _)] at w
  simp only [decide_eq_true_eq,List.filter_map,List.length_map]
  change S.card + F.length < k
  simpa only [F, Nat.add_comm S.card] using w


private theorem bit_and {α : Type*} (l : List α) (f g : α → Bool) :
    bits (l.map f) &&& bits (l.map g) = bits (l.map fun x => f x && g x) := by
  induction l with
  | nil => simp [bits]
  | cons a l ih => simp only [List.map_cons,bits,← bit_form,Nat.land_bit,ih]

private theorem bit_or {α : Type*} (l : List α) (f g : α → Bool) :
    bits (l.map f) ||| bits (l.map g) = bits (l.map fun x => f x || g x) := by
  induction l with
  | nil => simp [bits]
  | cons a l ih => simp only [List.map_cons,bits,← bit_form,Nat.lor_bit,ih]

private def compat (I : List (Nat × Nat)) (a : Nat) := bits (I.map fun p => a &&& p.1 == 0)
private def universal (I : List (Nat × Nat)) := bits (I.map fun _=>true)
private def threshold (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (j : Nat) :=
  bits (I.map fun p => decide (k≤p.2 + (acc.filter fun a => a &&& p.1 == 0).length+j))

private theorem saturated (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (j : Nat) (h : k≤j) :
    threshold k I acc j=universal I := by
  unfold threshold universal
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [decide_eq_true_eq]; omega

private theorem threshold_cons (k : Nat) (I : List (Nat × Nat)) (a : Nat) (acc : List Nat) (j : Nat) :
    threshold k I (a::acc) j = threshold k I acc j ||| (compat I a &&& threshold k I acc (j+1)) := by
  unfold threshold compat
  rw [bit_and,bit_or]
  congr 1
  apply List.map_congr_left
  intro p _
  apply Bool.eq_iff_iff.mpr
  by_cases e : a &&& p.1=0 <;> simp [e] <;> omega

private def cells (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,j => threshold k I acc j :: cells k I acc n (j+1)

private def tick (u m : Nat) : List Nat → List Nat
  | [] => []
  | a::as => (a ||| (m &&& as.headD u)) :: tick u m as

private theorem tick_cells (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (a n j : Nat) (h : k ≤ j+n) :
    tick (universal I) (compat I a) (cells k I acc n j) = cells k I (a::acc) n j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [cells,tick,List.cons.injEq]
    refine ⟨?_,ih (j+1) (by omega)⟩
    rw [threshold_cons]
    cases n with
    | zero => simp [cells,saturated k I acc (j+1) (by omega)]
    | succ n => rfl

private theorem can_add (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (a : Nat)
    (h : okContacts k I (a::acc)) : compat I a &&& threshold k I acc 1=0 := by
  apply (and_mask I _ _).mpr
  intro p hp e
  have b := List.all_eq_true.mp h p hp
  simp only [List.filter_cons,e,if_true,List.length_cons,decide_eq_true_eq] at b
  apply decide_eq_false
  omega

private def traverse (opts : List (Nat × Nat)) (u : Nat) (ending : List (Nat × Nat) → Bool) :
    Nat → Nat → List (Nat × Nat) → List Nat → List (List (Nat × Nat))
  | 0,_,acc,_ => if ending acc then [acc] else []
  | fuel+1,lo,acc,st => opts.flatMap fun a =>
    if lo ≤ a.1 && a.2 &&& st.headD u == 0 then
      traverse opts u ending fuel a.1 (a::acc) (tick u a.2 st) else []

private theorem traverse_complete (opts : List (Nat × Nat)) (I : List (Nat × Nat)) (k : Nat) (hk : 0<k)
    (ending : List (Nat × Nat) → Bool) (next acc : List (Nat × Nat)) (lo : Nat)
    (hc : ∀ a∈next,a∈opts) (vals : ∀ a∈next,a.2=compat I a.1)
    (hl : ∀ a∈next,lo≤a.1) (hs : next.Pairwise (fun a b => a.1 ≤ b.1))
    (hg : ∀ u w,next=u++w → okContacts k I ((u.reverse++acc).map Prod.fst)) (hf : ending (next.reverse++acc)) :
    next.reverse++acc ∈ traverse opts (universal I) ending next.length lo acc (cells k I (acc.map Prod.fst) k 1) := by
  induction next generalizing acc lo with
  | nil => simpa [traverse,hf] using hf
  | cons a rest ih =>
    simp only [List.length_cons,traverse,List.mem_flatMap]
    refine ⟨a,hc a (by simp),?_⟩
    have hd : (cells k I (acc.map Prod.fst) k 1).headD (universal I)=threshold k I (acc.map Prod.fst) 1 := by
      cases k with | zero => omega | succ k => rfl
    have an := vals a (by simp)
    have allow := can_add k I (acc.map Prod.fst) a.1 (by simpa using hg [a] rest rfl)
    simp only [hl a (by simp),decide_true,Bool.true_and,an,hd,allow,beq_self_eq_true,if_true,tick_cells k I (acc.map Prod.fst) a.1 k 1 (by omega)]
    simpa [List.append_assoc] using ih (a::acc) a.1 (fun x hx => hc x (by simp [hx]))
      (fun x hx => vals x (by simp [hx])) (List.pairwise_cons.mp hs).1 (List.pairwise_cons.mp hs).2
      (by intro u w h; simpa [List.append_assoc] using hg (a::u) w (by simp [h]))
      (by simpa [List.append_assoc] using hf)


private def contactsOf {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (base front : List V) :=
  front.map fun x => bits (base.map fun y => decide (G.Adj x y))

private def usable (k d : Nat) (base : List Nat) : List Nat :=
  ((inds base).filter fun p => d ≤ p.2+1 && p.2+1 < k).map Prod.fst

private def guardRows (k : Nat) (base : List Nat) (isets : List (Nat × Nat)) (cs : List Nat) :=
  okContacts k isets cs && (degrees (shifted cs ++ base)).all (·<k)

private def tagged (k d : Nat) (base : List Nat) :=
  (usable k d base).map fun x => (x,compat (inds base) x)

private def assemble (k d : Nat) (base : List Nat) (opts : List (Nat × Nat)) (bits0 : Nat) (lims : List Nat) :=
  let ending := fun cs : List (Nat × Nat) => (degrees (attach (cs.reverse.map Prod.fst) base)).all (d≤·)
  (traverse opts bits0 ending d 0 [] lims).map (fun cs => attach (cs.reverse.map Prod.fst) base)

private def grow (k d : Nat) (base : List Nat) : List (List Nat) :=
  assemble k d base (tagged k d base) (universal (inds base)) (cells k (inds base) [] k 1)

private theorem grow_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k d : Nat) (ht : G.CliqueFree 3) (hs : Small G A k)
    (r : V) (front base : List V) (hn : (r::front++base).Nodup)
    (hall : (r::front++base).toFinset=A) (hd : front.length=d)
    (ha : ∀ x∈front,G.Adj r x) (hb : ∀ x∈base,¬G.Adj r x)
    (hcount : ∀ x∈front,d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k)
    (hmin : ∀ x∈A,d≤(A.filter (G.Adj x)).card)
    (horder : (contactsOf G base front).Pairwise (·≤·)) :
    encode G (r::front++base) ∈ grow k d (encode G base) := by
  let cs := contactsOf G base front
  have split := root_encoding G r front base ha hb ht
  change encode G (r::front++base) = attach cs (encode G base) at split
  have hbnd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have hc (s) (mem : s ∈ cs) : s ∈ usable k d (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbnd S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbnd] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have guard_ (u w : List Nat) (h : cs=u++w) : guardRows k (encode G base) (inds (encode G base)) u := by
    let sl := front.take u.length
    have hu : contactsOf G base sl = u := by
      change (front.take u.length).map _=u
      rw [List.map_take, show front.map _=u++w from h, List.take_left]
    have ssub := (List.take_sublist u.length front).append (List.Sublist.refl base)
    have nodup : (sl++base).Nodup := (List.nodup_cons.mp hn).2.sublist ssub
    have sub : (sl++base).toFinset ⊆ A := by
      intro x hx
      rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ssub.subset (List.mem_toFinset.mp hx)))
    have ha' (x) (hx : x∈sl) := ha x ((List.take_sublist u.length front).subset hx)
    have indep : Gᶜ.IsClique (sl.toFinset : Set V) := by
      rw [G.isClique_compl]
      intro x hx y hy hxy
      exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x (List.mem_toFinset.mp hx)) (ha' y (List.mem_toFinset.mp hy)) hxy
    have em := contacts G sl base (by intro x hx y hy adj; exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x hx) (ha' y hy) adj.ne adj)
    change encode G (sl++base)=shifted (contactsOf G base sl)++encode G base at em
    rw [← hu]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ok_contacts G A k hs sl base nodup sub indep,?_⟩
    rw [← em]
    exact degrees_bound G ht A k hs _ nodup sub
  have final_ : (degrees (attach cs (encode G base))).all (d≤·) = true := by
    rw [← split,degrees_encode,List.all_eq_true]
    intro n hh
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hh
    simpa only [decide_eq_true_eq,sizeAt_finset G hn,hall] using hmin x (hall ▸ List.mem_toFinset.mpr hx)
  have csl : cs.length=d := by simp [cs,contactsOf,hd]
  let base' := encode G base
  let tag (x : Nat) := (x,compat (inds base') x)
  let ts := cs.map tag
  have ret (ss : List Nat) : (ss.map tag).map Prod.fst = ss := by simp [tag,Function.comp_def]
  have tg (a) (ma : a∈ts) : a ∈ tagged k d base' := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ma
    exact List.mem_map.mpr ⟨x,hc x hx,rfl⟩
  have gg (u w : List (Nat × Nat)) (h : ts=u++w) : okContacts k (inds base') (u.reverse.map Prod.fst) := by
    let sl := cs.take u.length
    have split_ : cs=sl++cs.drop u.length := (List.take_append_drop u.length cs).symm
    have hu : sl.map tag=u := by
      change (cs.take u.length).map tag=u
      rw [List.map_take,show cs.map tag=u++w from h,List.take_left]
    have gh := Bool.and_eq_true_iff.mp (guard_ sl (cs.drop u.length) split_)
    rw [← hu,List.map_reverse,ret]
    simpa [okContacts] using gh.1
  have tslen : ts.length=d := by simp [ts,csl]
  have tsord : ts.Pairwise (fun a b => a.1 ≤ b.1) := List.pairwise_map.mpr horder
  rw [split]
  apply List.mem_map.mpr
  refine ⟨ts.reverse,?_,by simp [ts,ret]⟩
  have hk : 0<k := hs ∅ (by simp) (by simp)
  simpa only [List.append_nil,tslen,List.map_nil] using traverse_complete (tagged k d base') (inds base') k hk
    (fun u => (degrees (attach (u.reverse.map Prod.fst) base')).all (d≤·)) ts [] 0 tg
    (by intro a ha; obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha; rfl) (by simp) tsord
    (by simpa using gg) (by simpa only [List.append_nil,List.reverse_reverse,ts,ret,base'] using final_)

private def levels (norm : List Nat → List Nat) : Nat → Nat → Nat → List (List Nat)
  | 0,_,_ => []
  | k+1,n,cap => if n=0 then [[]] else
    ((List.range (min cap (min k (n-1)) + 1)).flatMap fun d =>
      (levels norm k (n-1-d) (k-1)).flatMap fun base => (grow (k+1) d base).map norm).eraseDups

private theorem sorted_neigh {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : Finset V) (base : List V) :
    ∃ l : List V, l.Nodup ∧ l.toFinset=N ∧ (contactsOf G base l).Pairwise (·≤·) := by
  let key (x : V) := bits (base.map fun y => decide (G.Adj x y))
  let ord (a b : V) := decide (key a ≤ key b)
  let l := N.toList.mergeSort ord
  have h := List.mergeSort_perm N.toList ord
  refine ⟨l,h.nodup_iff.mpr N.nodup_toList,?_,?_⟩
  · ext x
    simp [l]
  · have htr (a b c) : ord a b → ord b c → ord a c := by simp only [ord,decide_eq_true_eq]; omega
    have htot (a b) : ord a b || ord b a := by simp [ord,le_total]
    have sort_ := List.pairwise_mergeSort htr htot N.toList
    apply List.pairwise_map.mpr
    simpa only [ord,decide_eq_true_eq] using sort_

private theorem levels_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (norm : List Nat → List Nat)
    (hnorm : ∀ l : List V, ∃ l' : List V, l'.Perm l ∧ encode G l'=norm (encode G l))
    (k : Nat) (A : Finset V) (cap : Nat) (hs : Small G A k)
    (hu : A.Nonempty → ∃ x∈A,(A.filter (G.Adj x)).card ≤ cap) :
    ∃ vs : List V, vs.Nodup ∧ vs.toFinset=A ∧ encode G vs ∈ levels norm k A.card cap := by
  induction k generalizing A cap with
  | zero => have h := hs ∅ (by simp) (by simp); simp at h
  | succ k ih =>
    by_cases empty : A=∅
    · subst A; exact ⟨[],by simp,by simp,by simp [encode,levels]⟩
    have non := Finset.nonempty_iff_ne_empty.mpr empty
    obtain ⟨r,hr,hmin⟩ := A.exists_min_image (fun x => (A.filter (G.Adj x)).card) non
    let N := A.filter (G.Adj r)
    let B := A \ insert r N
    let d := N.card
    have hNr : r∉N := by simp [N]
    have hNA : N⊆A := Finset.filter_subset ..
    have hBA : B⊆A := Finset.sdiff_subset
    have hu' : d≤cap := by obtain ⟨x,hx,hh⟩ := hu non; exact (hmin x hx).trans hh
    have hdk : d≤k := Nat.le_of_lt_succ (hs N hNA (neighbors_small G ht A r))
    have hBcard : B.card + d + 1 = A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hr hNA)
      rw [Finset.card_insert_of_notMem hNr] at hh
      omega
    have rB : r∉B := by simp [B]
    have hbase (x) (hx : x∈B) : ¬G.Adj r x := by
      have h := Finset.mem_sdiff.mp hx
      exact fun ha => h.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1,ha⟩))
    have noK : Small G B k := by
      intro S hS hI
      have rn : r∉S := fun h => rB (hS h)
      have indep : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
        exact ⟨hI,fun x hx => ⟨fun e => rn (e ▸ hx),hbase x (hS hx)⟩⟩
      have hh := hs (insert r S) (Finset.insert_subset hr (hS.trans hBA)) indep
      rw [Finset.card_insert_of_notMem rn] at hh
      omega
    obtain ⟨base,hbn,hb,cls⟩ := ih B (k-1) noK (by
      rintro ⟨x,hx⟩
      have mm := noK (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
      exact ⟨x,hx,by omega⟩)
    obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
    have ha (x) (hx : x∈front) : G.Adj r x := (Finset.mem_filter.mp (hf ▸ List.mem_toFinset.mpr hx)).2
    have hnot (x) (hx : x∈base) := hbase x (hb ▸ List.mem_toFinset.mpr hx)
    have dl : front.length=d := by rw [← List.toFinset_card_of_nodup hfn,hf]
    have nodup : (r::front++base).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change r ∉ front++base
        rw [List.mem_append,not_or]
        exact ⟨fun h => hNr (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
      · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
    have cover : (r::front++base).toFinset=A := by
      ext x
      simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,Finset.mem_insert,Finset.mem_union,Finset.mem_sdiff]
      have h1 : x=r → x∈A := fun h => h ▸ hr
      have h2 : x∈N → x∈A := fun h => hNA h
      grind
    have hcount (x) (hx : x∈front) : d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k+1 := by
      have xN : x∈N := hf ▸ List.mem_toFinset.mpr hx
      have adj := ha x hx
      have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_sdiff,B]
        constructor
        · rintro ⟨yA,xy⟩
          by_cases yr : y=r
          · exact Or.inl yr
          · exact Or.inr ⟨⟨yA,not_or.mpr ⟨yr,fun yN => G.isIndepSet_neighborSet_of_triangleFree ht r adj (Finset.mem_filter.mp yN).2 xy.ne xy⟩⟩,xy⟩
        · rintro (rfl|⟨⟨yA,_⟩,xy⟩)
          · exact ⟨hr,adj.symm⟩
          · exact ⟨yA,xy⟩
      have mm := hmin x (hNA xN)
      have mx := hs (A.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht A x)
      have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
      rw [eq,Finset.card_insert_of_notMem rn] at mm mx
      rw [sizeAt_finset G hbn,hb]
      exact ⟨mm,mx⟩
    have grown := grow_complete G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    obtain ⟨l,hperm,heq⟩ := hnorm (r::front++base)
    refine ⟨l,hperm.nodup_iff.mpr nodup,?_,?_⟩
    · rw [← cover]
      ext x
      exact List.mem_toFinset.trans (hperm.mem_iff.trans List.mem_toFinset.symm)
    · rw [heq,levels,if_neg (Finset.card_ne_zero.mpr non)]
      apply List.mem_eraseDups.mpr
      apply List.mem_flatMap.mpr
      refine ⟨d,List.mem_range.mpr (by omega),List.mem_flatMap.mpr ⟨encode G base,?_,List.mem_map.mpr ⟨_,grown,rfl⟩⟩⟩
      simpa only [show A.card-1-d=B.card by omega] using cls


private def swapAt {α : Type*} : Nat → List α → List α
  | 0,x::y::xs => y::x::xs
  | i+1,x::xs => x::swapAt i xs
  | _,l => l

private theorem swap_perm {α : Type*} (i : Nat) (l : List α) : (swapAt i l).Perm l := by
  induction i generalizing l with
  | zero => cases l with | nil => rfl | cons a l => cases l with | nil => rfl | cons b l => exact List.Perm.swap a b l
  | succ i ih => cases l with | nil => rfl | cons a l => exact List.Perm.cons a (ih l)

private def exchange : Nat → Nat → Nat
  | 0,x => 4*(x/4)+2*(x%2)+((x/2)%2)
  | i+1,x => 2*exchange i (x/2)+x%2

private theorem bits_swap (i : Nat) (l : List Bool) (h : i+2≤l.length) :
    bits (swapAt i l)=exchange i (bits l) := by
  induction i generalizing l with
  | zero =>
    obtain ⟨a,b,l,rfl⟩ : ∃ a b t,l=a::b::t := by cases l with | nil => simp at h | cons a l => cases l with | nil => simp at h | cons b t => exact ⟨_,_,_,rfl⟩
    cases a <;> cases b <;> simp [swapAt,bits,exchange] <;> omega
  | succ i ih =>
    cases l with
    | nil => simp at h
    | cons a t =>
      have e := ih t (by simp at h; omega)
      cases a <;> simp [swapAt,bits,exchange,half_step,e]

private theorem swap_map {α β : Type*} (f : α→β) (i : Nat) (l : List α) :
    (swapAt i l).map f=swapAt i (l.map f) := by
  induction i generalizing l with
  | zero => cases l with | nil => rfl | cons a l => cases l <;> rfl
  | succ i ih => cases l with | nil => rfl | cons a l => simp [swapAt,ih]

private def swapCode : Nat → List Nat → List Nat
  | 0,p::q::rs => (p%2+2*q)::(p/2)::rs
  | i+1,p::rs => exchange i p :: swapCode i rs
  | _,l => l

private theorem swap_encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Nat) (l : List V) (h : i+2≤l.length) : encode G (swapAt i l) = swapCode i (encode G l) := by
  induction i generalizing l with
  | zero =>
    obtain ⟨a,b,t,rfl⟩ : ∃ a b t,l=a::b::t := by cases l with | nil => simp at h | cons a l => cases l with | nil => simp at h | cons b t => exact ⟨_,_,_,rfl⟩
    by_cases adj : G.Adj a b <;> simp [swapAt,swapCode,encode,bits,adj,G.adj_comm b a,Nat.add_comm]
    omega
  | succ i ih =>
    cases l with
    | nil => simp at h
    | cons a t =>
      have hi : i+2≤t.length := by simp at h; omega
      simp only [swapAt,encode,swap_map,swapCode,List.cons.injEq]
      exact ⟨bits_swap i _ (by simpa using hi),ih t hi⟩

private def relabel (swaps rows : List Nat) :=
  swaps.foldl (fun l i => if i+2≤l.length then swapCode i l else l) rows

private theorem relabel_real {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (swaps : List Nat) (l : List V) : ∃ l', l'.Perm l ∧ encode G l'=relabel swaps (encode G l) := by
  induction swaps generalizing l with
  | nil => exact ⟨l,.refl _,rfl⟩
  | cons i is ih =>
    by_cases hi : i+2≤l.length
    · obtain ⟨t,ht,he⟩ := ih (swapAt i l)
      exact ⟨t,ht.trans (swap_perm ..),by simpa [relabel,encode_length,hi,swap_encode G i l hi] using he⟩
    · simpa [relabel,encode_length,hi] using ih l


private def renumber : List Nat → List Nat
  | [1,2,1,0] => [2]
  | [1,2,3,2,2,1,0] => [2,4]
  | [1,4,3,2,2,1,0] => [3,2,5,4]
  | [1,8,3,2,2,1,0] => [4,3,2,3,5,4]
  | [1,9,3,2,2,1,0] => [2,4]
  | [1,12,3,2,2,1,0] => [5,4,3,2,4,3,5,4]
  | [1,16,3,2,2,1,0] => [5,4,3,2,4,3,5,4]
  | [1,17,3,2,2,1,0] => [3,2,5,4]
  | [1,18,3,2,2,1,0] => [4,3,2,3,5,4]
  | [3,2,2,3,2,1,0] => [5,4,3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,3,4]
  | [3,2,4,3,2,1,0] => [5,4,3,2,1,0,4,3,2,1,5,4,3,2,5,4,3,4]
  | [3,2,6,3,2,1,0] => [5,4,3,2,1,0,4,3,2,1,5,4,3,2,4,3]
  | [3,2,10,1,1,1,0] => [4,3,2,1,0,5,4,3,2,1,5,4,3,2,4,3]
  | [3,4,8,3,2,1,0] => [4,3,2,1,0,3,2,1,5,4,3,2,5,4,3,4]
  | [3,4,9,1,1,1,0] => [2,1,0,2,1,3,2,5]
  | [3,4,9,3,2,1,0] => [4,3,2,1,0,3,2,1,5,4,3,2,4,3]
  | [3,4,9,3,2,2,1,0] => [3,5]
  | [3,8,8,3,2,1,0] => [3,2,1,0,3,2,1,5,4,3,2,5,4,3,4]
  | [3,8,9,1,1,1,0] => [5,4,3,2,1,0,2,1,5,4,3,2]
  | [3,8,9,3,2,1,0] => [3,2,1,0,3,2,1,5,4,3,2,4,3]
  | [3,8,17,3,2,2,1,0] => [4,3,6,5]
  | [3,10,8,1,1,1,0] => [3,2,1,0,3,2,1,4,3,2,3]
  | [3,10,10,1,1,1,0] => [2,1,0,3,2,1,2,4,3,5,4,5]
  | [3,12,8,3,2,1,0] => [2,1,0,3,2,1,4,3,2,3]
  | [3,12,9,1,0,1,0] => [1,5]
  | [3,12,17,3,2,2,1,0] => [4,6]
  | [3,16,9,1,1,1,0] => [0,5,4,3,2]
  | [3,16,18,3,2,2,1,0] => [5,4,3,4,6,5]
  | [3,18,10,1,1,1,0] => [1,5,4,3,5,4,5]
  | [3,18,18,3,2,2,1,0] => [3,5,4,6]
  | [3,24,16,3,2,2,1,0] => [1,6,5,4,3,5,4,6,5]
  | [3,24,17,3,2,2,1,0] => [6,5,4,3,5,4,6,5]
  | [3,24,18,3,2,2,1,0] => [6,5,4,3,6,5,4,6,5,6]
  | [7,24,66,137,3,12,9,3,2,2,1,0] => [0,4,3,2,5,4,3,5,4,8,7,10,9]
  | [7,24,130,145,3,12,9,3,2,2,1,0] => [0,5,4,3,2,5,4,3,5,4,9,8,7,8,10,9]
  | [7,24,146,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,24,194,129,3,2,6,3,2,2,1,0] => [2,8,10]
  | [7,24,194,129,3,12,9,3,2,2,1,0] => [0,5,4,3,2,5,4,3,5,4,5,10,9,8,7,9,8,10,9]
  | [7,24,194,137,3,2,6,3,2,2,1,0] => [2,8,10]
  | [7,24,194,137,3,12,9,3,2,2,1,0] => [7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,7,6,8,7,9,8,10]
  | [7,24,194,145,3,12,9,3,2,2,1,0] => [6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,8,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,7,6,8,7,9,8,10]
  | [7,36,132,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,36,140,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,36,196,130,3,2,6,3,2,2,1,0] => [2,4,6,8,10]
  | [7,36,196,134,3,2,6,3,2,2,1,0] => [2,4,6,8,10]
  | [7,36,196,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,260,140,144,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,260,140,145,3,2,6,3,2,2,1,0] => [4,3,2,1,0,6,5,4,3,2,1,3,2,5,4,3,6,5,4,8,7,6,5,8,7,6,10,9,8,7,9,8,10,9]
  | [7,260,140,146,3,2,6,3,2,2,1,0] => [3,2,1,0,1,4,3,2,5,4,3,4,9,8,7,6,8,10,9]
  | [7,260,268,145,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,260,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,264,146,144,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,264,146,145,3,2,6,3,2,2,1,0] => [4,3,2,1,0,1,4,3,2,6,5,4,3,4,9,8,7,6,8,10,9]
  | [7,264,146,146,3,2,6,3,2,2,1,0] => [3,2,1,0,5,4,3,2,1,3,2,5,4,3,6,5,4,8,7,6,5,8,7,6,10,9,8,7,9,8,10,9]
  | [7,264,274,146,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,280,146,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,280,146,146,3,2,6,3,2,2,1,0] => [1,4,6]
  | [7,280,194,129,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,280,194,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,280,194,145,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,280,194,146,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,280,274,146,3,2,6,3,2,2,1,0] => [1,2,4,6,8,10]
  | [7,292,196,130,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,292,196,134,3,2,6,3,2,2,1,0] => [4,6]
  | [7,292,196,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,292,196,145,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,292,196,146,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,292,268,145,3,2,6,3,2,2,1,0] => [1,2,8,10]
  | [7,292,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,384,258,134,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,258,134,3,12,9,3,2,2,1,0] => [0,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,8]
  | [7,384,260,137,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,384,260,145,3,12,9,3,2,2,1,0] => [0,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,7,10,9,8,10]
  | [7,384,264,137,3,12,9,3,2,2,1,0] => [0,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,8,7,9,8,10]
  | [7,384,268,137,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,268,137,3,12,9,3,2,2,1,0] => [7,6,5,4,3,2,1,0,5,4,3,2,1,7,6,5,4,3,2,9,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,8,7,10,9,8,10]
  | [7,384,268,145,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,268,145,3,12,9,3,2,2,1,0] => [6,5,4,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,8,7,10,9,8,10]
  | [7,384,274,146,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,384,274,148,3,12,9,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,384,276,145,3,12,9,3,2,2,1,0] => [10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,388,258,134,3,2,6,3,2,2,1,0] => [4,3,2,1,0,6,5,4,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,9,8,7,8,10,9]
  | [7,388,260,137,3,2,6,3,2,2,1,0] => [4,3,2,1,0,2,1,4,3,2,6,5,4,3,5,4,10,9,8,7,6,9,8,10,9]
  | [7,388,260,145,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,388,264,137,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,388,268,137,3,2,6,3,2,2,1,0] => [1,2,8,10]
  | [7,388,268,145,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,388,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,388,274,146,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,388,274,148,3,12,9,3,2,2,1,0] => [2,1,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,388,276,145,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,392,258,134,3,2,6,3,2,2,1,0] => [3,2,1,0,2,1,4,3,2,5,4,3,5,4,10,9,8,7,6,9,8,10,9]
  | [7,392,260,137,3,2,6,3,2,2,1,0] => [3,2,1,0,5,4,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,9,8,7,8,10,9]
  | [7,392,268,137,3,2,6,3,2,2,1,0] => [2,1,2,4,6,8,10]
  | [7,392,268,145,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,392,274,146,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [15,304,164,162,82,3,2,9,1,1,1,0] => [2,1,0,10,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,6,5,4,3,6,5,7,6,8,7,9,10]
  | [15,304,196,138,73,1,6,3,2,2,1,0] => [2,1,3,2,8,10]
  | [15,584,392,268,145,3,2,6,3,2,2,1,0] => [5,7]
  | _ => []

private def normalized (g : List Nat) := relabel (renumber g) g

theorem degrees_length (g : List Nat) : (degrees g).length=g.length := by
  have step (xs : List Nat) (m : Nat) : (bump m xs).length=xs.length := by
    induction xs generalizing m with | nil => rfl | cons a xs ih => simp [bump,ih]
  induction g with | nil => rfl | cons a g ih => simp [degrees,step,ih]

theorem bump_sum (xs : List Nat) (m : Nat) : (bump m xs).sum=xs.sum+countBits xs.length m := by
  induction xs generalizing m with | nil => rfl | cons a xs ih => simp [bump,countBits,ih]; omega

def edges_ : List Nat → Nat
  | [] => 0
  | m::t => countBits t.length m + edges_ t

theorem energy (rows : List Nat) : (degrees rows).sum=2*edges_ rows := by
  induction rows with
  | nil => rfl
  | cons m t ih => simp [degrees,edges_,bump_sum,degrees_length,ih]; omega

theorem count_shift (n a j : Nat) : countBits (j+n) (2^j*a)=countBits n a := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2^(j+1)*a=2*(2^j*a) := by rw [pow_succ]; ring
    rw [Nat.succ_add,countBits,e]
    simp [ih]

theorem count_full (d n : Nat) : countBits (d+n) (2^d-1)=d := by
  induction d with
  | zero =>
    have h (t : Nat) : countBits t 0=0 := by induction t with | zero => rfl | succ k ih => simp [countBits,ih]
    simp [h]
  | succ d ih =>
    have hp : 0 < 2^d := Nat.two_pow_pos _
    have split : 2^(d+1)-1=2*(2^d-1)+1 := by rw [pow_succ]; omega
    rw [Nat.succ_add,countBits,split,half_step,ih]
    omega

theorem shifted_length (xs : List Nat) : (shifted xs).length=xs.length := by
  induction xs with | nil => rfl | cons a xs ih => simp [shifted,ih]

theorem edges_attached (xs b : List Nat) : edges_ (attach xs b) =
    xs.length + (xs.map (countBits b.length)).sum + edges_ b := by
  have h (ls : List Nat) : edges_ (shifted ls++b)=(ls.map (countBits b.length)).sum+edges_ b := by
    induction ls with
    | nil => simp [shifted]
    | cons a ls ih => simp [shifted,edges_,shifted_length,count_shift,ih,Nat.add_assoc]
  simp [attach,edges_,shifted_length,count_full,h,Nat.add_assoc]

def Extension (k d : Nat) (b cs : List Nat) : Prop :=
  cs.length = d ∧ (∀ x ∈ cs, x ∈ usable k d b) ∧ okContacts k (inds b) cs = true
theorem graphExtension {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k d : Nat) (ht : G.CliqueFree 3) (hs : Small G A k)
    (r : V) (front base : List V) (hn : (r::front++base).Nodup)
    (hall : (r::front++base).toFinset=A) (hd : front.length=d)
    (ha : ∀ x∈front,G.Adj r x) (hb : ∀ x∈base,¬G.Adj r x)
    (hcount : ∀ x∈front,d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k)
    (hmin : ∀ x∈A,d≤(A.filter (G.Adj x)).card)
    (horder : (contactsOf G base front).Pairwise (·≤·)) :
    ∃ cs, Extension k d (encode G base) cs ∧ encode G (r::front++base) = attach cs (encode G base) := by
  let cs := contactsOf G base front
  have split := root_encoding G r front base ha hb ht
  change encode G (r::front++base) = attach cs (encode G base) at split
  have hbnd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have hc (s) (mem : s ∈ cs) : s ∈ usable k d (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbnd S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbnd] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have guard_ (u w : List Nat) (h : cs=u++w) : guardRows k (encode G base) (inds (encode G base)) u := by
    let sl := front.take u.length
    have hu : contactsOf G base sl = u := by
      change (front.take u.length).map _=u
      rw [List.map_take, show front.map _=u++w from h, List.take_left]
    have ssub := (List.take_sublist u.length front).append (List.Sublist.refl base)
    have nodup : (sl++base).Nodup := (List.nodup_cons.mp hn).2.sublist ssub
    have sub : (sl++base).toFinset ⊆ A := by
      intro x hx
      rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ssub.subset (List.mem_toFinset.mp hx)))
    have ha' (x) (hx : x∈sl) := ha x ((List.take_sublist u.length front).subset hx)
    have indep : Gᶜ.IsClique (sl.toFinset : Set V) := by
      rw [G.isClique_compl]
      intro x hx y hy hxy
      exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x (List.mem_toFinset.mp hx)) (ha' y (List.mem_toFinset.mp hy)) hxy
    have em := contacts G sl base (by intro x hx y hy adj; exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x hx) (ha' y hy) adj.ne adj)
    change encode G (sl++base)=shifted (contactsOf G base sl)++encode G base at em
    rw [← hu]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ok_contacts G A k hs sl base nodup sub indep,?_⟩
    rw [← em]
    exact degrees_bound G ht A k hs _ nodup sub
  exact ⟨cs, ⟨by simp [cs,contactsOf,hd], hc,
    (Bool.and_eq_true_iff.mp (guard_ cs [] (by simp))).1⟩, split⟩

theorem rootSplitting {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (norm : List Nat → List Nat)
    (hnorm : ∀ l : List V, ∃ l' : List V, l'.Perm l ∧ encode G l'=norm (encode G l))
    (k : Nat) (A : Finset V) (non : A.Nonempty) (cap : Nat) (hs : Small G A (k+1))
    (hu : A.Nonempty → ∃ x∈A,(A.filter (G.Adj x)).card ≤ cap) :
    ∃ (vs : List V) (d : Nat) (b cs : List Nat), vs.Nodup ∧ vs.toFinset=A ∧ d≤cap ∧
      b∈levels norm k (A.card-1-d) (k-1) ∧ Extension (k+1) d b cs ∧ encode G vs=attach cs b := by
    obtain ⟨r,hr,hmin⟩ := A.exists_min_image (fun x => (A.filter (G.Adj x)).card) non
    let N := A.filter (G.Adj r)
    let B := A \ insert r N
    let d := N.card
    have hNr : r∉N := by simp [N]
    have hNA : N⊆A := Finset.filter_subset ..
    have hBA : B⊆A := Finset.sdiff_subset
    have hu' : d≤cap := by obtain ⟨x,hx,hh⟩ := hu non; exact (hmin x hx).trans hh
    have hdk : d≤k := Nat.le_of_lt_succ (hs N hNA (neighbors_small G ht A r))
    have hBcard : B.card + d + 1 = A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hr hNA)
      rw [Finset.card_insert_of_notMem hNr] at hh
      omega
    have rB : r∉B := by simp [B]
    have hbase (x) (hx : x∈B) : ¬G.Adj r x := by
      have h := Finset.mem_sdiff.mp hx
      exact fun ha => h.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1,ha⟩))
    have noK : Small G B k := by
      intro S hS hI
      have rn : r∉S := fun h => rB (hS h)
      have indep : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
        exact ⟨hI,fun x hx => ⟨fun e => rn (e ▸ hx),hbase x (hS hx)⟩⟩
      have hh := hs (insert r S) (Finset.insert_subset hr (hS.trans hBA)) indep
      rw [Finset.card_insert_of_notMem rn] at hh
      omega
    obtain ⟨base,hbn,hb,cls⟩ := levels_complete G ht norm hnorm k B (k-1) noK (by
      rintro ⟨x,hx⟩
      have mm := noK (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
      exact ⟨x,hx,by omega⟩)
    obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
    have ha (x) (hx : x∈front) : G.Adj r x := (Finset.mem_filter.mp (hf ▸ List.mem_toFinset.mpr hx)).2
    have hnot (x) (hx : x∈base) := hbase x (hb ▸ List.mem_toFinset.mpr hx)
    have dl : front.length=d := by rw [← List.toFinset_card_of_nodup hfn,hf]
    have nodup : (r::front++base).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change r ∉ front++base
        rw [List.mem_append,not_or]
        exact ⟨fun h => hNr (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
      · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
    have cover : (r::front++base).toFinset=A := by
      ext x
      simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,Finset.mem_insert,Finset.mem_union,Finset.mem_sdiff]
      have h1 : x=r → x∈A := fun h => h ▸ hr
      have h2 : x∈N → x∈A := fun h => hNA h
      grind
    have hcount (x) (hx : x∈front) : d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k+1 := by
      have xN : x∈N := hf ▸ List.mem_toFinset.mpr hx
      have adj := ha x hx
      have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_sdiff,B]
        constructor
        · rintro ⟨yA,xy⟩
          by_cases yr : y=r
          · exact Or.inl yr
          · exact Or.inr ⟨⟨yA,not_or.mpr ⟨yr,fun yN => G.isIndepSet_neighborSet_of_triangleFree ht r adj (Finset.mem_filter.mp yN).2 xy.ne xy⟩⟩,xy⟩
        · rintro (rfl|⟨⟨yA,_⟩,xy⟩)
          · exact ⟨hr,adj.symm⟩
          · exact ⟨yA,xy⟩
      have mm := hmin x (hNA xN)
      have mx := hs (A.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht A x)
      have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
      rw [eq,Finset.card_insert_of_notMem rn] at mm mx
      rw [sizeAt_finset G hbn,hb]
      exact ⟨mm,mx⟩
    obtain ⟨cs,hcs,enc⟩ := graphExtension G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    exact ⟨r::front++base, d, encode G base, cs, nodup, cover, hu', by simpa only [show A.card-1-d=B.card by omega] using cls, hcs, enc⟩


theorem density_of_packing (hnum : ∀ d ≤ 3, ∀ b ∈ levels normalized 5 (15-d) 4, ∀ cs, Extension 6 d b cs → 32 ≤ edges_ (attach cs b)) : OMA.RamseyTwentyTwo.Sixteen := by
  classical
  intro G inst ht hi
  by_contra! hsmall
  let U : Finset (Fin 16) := Finset.univ
  have bounded : Small G U 6 := by
    intro I _ hI
    by_contra! hc
    exact (hi.mono hc) I ⟨hI,rfl⟩
  have low : U.Nonempty → ∃ x∈U,(U.filter (G.Adj x)).card≤3 := by
    intro _
    by_contra! hn
    have h4 (x : Fin 16) : 4≤G.degree x := by
      have hh := hn x (Finset.mem_univ _)
      simp only [U,← SimpleGraph.neighborFinset_eq_filter,SimpleGraph.card_neighborFinset_eq_degree] at hh
      omega
    have w := Finset.sum_le_sum (s:=U) (f:=fun _=>4) (g:= fun x => G.degree x) (fun x _ => h4 x)
    have tot := G.sum_degrees_eq_twice_card_edges
    simp [U] at w
    omega
  have hn (l : List (Fin 16)) := relabel_real G (renumber (encode G l)) l
  obtain ⟨vs,d,b,cs,hv,cover,hd,hb,hcs,enc⟩ := rootSplitting G ht normalized hn 5 U (by simp [U]) 3 bounded low
  have r := hnum d hd b (by simpa [U] using hb) cs hcs
  rw [← enc] at r
  have dg : degrees (encode G vs)=vs.map (fun x => G.degree x) := by
    rw [degrees_encode]
    apply List.map_congr_left
    intro x _
    rw [sizeAt_finset G hv,cover]
    simp only [U,← SimpleGraph.neighborFinset_eq_filter,SimpleGraph.card_neighborFinset_eq_degree]
  have w := List.sum_toFinset (fun x => G.degree x) hv
  rw [cover] at w
  have tot := G.sum_degrees_eq_twice_card_edges
  have hh : 64≤(degrees (encode G vs)).sum := by rw [energy]; omega
  rw [dg,← w] at hh
  exact (by change 64 ≤ ∑ i, G.degree i at hh; omega : False)



private abbrev WeightedRow := (Nat × Nat) × Nat

private def rowScore (W : List WeightedRow) (x : Nat) : Nat :=
  ((W.filter (fun w => x &&& w.1.1 == 0)).map Prod.snd).sum

private def rowCapacity (W : List WeightedRow) : Nat :=
  (W.map fun w => (5-w.1.2)*w.2).sum

private theorem rowScore_cons (w : WeightedRow) (W : List WeightedRow) (cs : List Nat) :
    (cs.map (rowScore (w::W))).sum =
    (cs.filter (fun x => x &&& w.1.1 == 0)).length*w.2 + (cs.map (rowScore W)).sum := by
  induction cs with
  | nil => simp
  | cons x cs ih =>
    by_cases e : x &&& w.1.1 = 0
    · simp [rowScore,e,Nat.succ_mul] at ih ⊢
      omega
    · simp [rowScore,e] at ih ⊢
      omega

private theorem rowScore_le (b cs : List Nat) (W : List WeightedRow)
    (valid : ∀ w∈W,w.1∈inds b) (good : okContacts 6 (inds b) cs=true) :
    (cs.map (rowScore W)).sum ≤ rowCapacity W := by
  induction W with
  | nil =>
    have h : rowScore [] = fun _ => 0 := rfl
    simp [h,rowCapacity]
  | cons w W ih =>
    have sub := ih (fun t ht => valid t (.tail _ ht))
    have hm := of_decide_eq_true (List.all_eq_true.mp good w.1 (valid w (.head _)))
    have lecap : (cs.filter (fun x => x &&& w.1.1 == 0)).length ≤ 5-w.1.2 := by omega
    have lh := Nat.mul_le_mul_right w.2 lecap
    rw [rowScore_cons]
    change _ ≤ (5-w.1.2)*w.2 + rowCapacity W
    omega


private def checkWeights (b : List Nat) (d price low : Nat) (W : List WeightedRow) : Bool :=
  W.all (fun w => decide (w.1 ∈ inds b)) &&
  (usable 6 d b).all (fun x => decide (low ≤ countBits b.length x * price + rowScore W x)) &&
  decide ((31 - edges_ b - d) * price + rowCapacity W < d * low)

private theorem viaWeights (b cs : List Nat) (d price low : Nat) (W : List WeightedRow)
    (ext : Extension 6 d b cs) (check : checkWeights b d price low W = true) :
    32 ≤ edges_ (attach cs b) := by
  by_contra! small
  obtain ⟨len,mem,good⟩ := ext
  obtain ⟨both,last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid,opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W
    (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have add (xs : List Nat) (legal : ∀ x∈xs, x∈usable 6 d b) :
      xs.length*low ≤ (xs.map (countBits b.length)).sum*price + (xs.map (rowScore W)).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have t := ih (fun a ha => legal a (.tail x ha))
      have s := of_decide_eq_true (List.all_eq_true.mp opts x (legal x (.head _)))
      simp only [List.length_cons,Nat.succ_mul,List.map_cons,List.sum_cons,Nat.add_mul]
      omega
  have lower := add cs mem
  rw [len] at lower
  rw [edges_attached,len] at small
  have lim : (cs.map (countBits b.length)).sum ≤ 31 - edges_ b - d := by omega
  have mul := Nat.mul_le_mul_right price lim
  have strict := of_decide_eq_true last
  omega

private abbrev base13_0 : List Nat := [15, 560, 388, 274, 146, 3, 2, 6, 3, 2, 2, 1, 0]
private def base13_0Weights : List WeightedRow := [((3120,4),1), ((2352,4),1), ((3144,4),1), ((2248,4),1), ((2200,4),1), ((4676,4),1), ((4292,4),1), ((404,4),1), ((588,4),1), ((156,4),1), ((4642,4),1), ((4386,4),1), ((1074,4),1), ((1546,4),1), ((1050,4),1), ((4358,4),1), ((278,4),1), ((526,4),1), ((4481,4),1), ((2433,4),1), ((3137,4),1), ((1601,4),1), ((4289,4),1), ((4641,4),1), ((1569,4),1), ((2337,4),1)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem base13_0Checked :
    checkWeights base13_0 2 5 23 base13_0Weights = true := by decide +kernel

private abbrev base12_0 : List Nat := [7, 24, 130, 145, 3, 2, 6, 3, 2, 2, 1, 0]
private def base12_0Weights : List WeightedRow := [((1224,4),1), ((1576,4),1), ((1128,4),2), ((2244,4),1), ((2340,4),1), ((804,4),2), ((2148,4),1), ((204,4),2), ((108,4),1), ((1554,4),1), ((2322,4),2), ((786,4),1), ((2194,4),1), ((1170,4),1), ((1546,4),1), ((1162,4),1), ((2310,4),1), ((526,4),2), ((142,4),1), ((2241,4),2), ((1217,4),1), ((2337,4),1), ((801,4),1), ((2145,4),1), ((1121,4),1), ((1553,4),1), ((2321,4),1), ((785,4),2), ((1169,4),1)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem base12_0Checked :
    checkWeights base12_0 3 5 26 base12_0Weights = true := by decide +kernel

private abbrev base12_1 : List Nat := [7, 24, 146, 145, 3, 2, 6, 3, 2, 2, 1, 0]
private def base12_1Weights : List WeightedRow := [((200,3),1), ((1224,4),2), ((1576,4),2), ((2340,4),1), ((804,4),2), ((2148,4),2), ((76,3),1), ((108,4),2), ((2322,4),1), ((786,4),2), ((2194,4),2), ((1162,4),3), ((2310,4),2), ((526,4),3), ((2241,4),3), ((1121,4),2), ((2321,4),2), ((785,4),3), ((1169,4),2)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem base12_1Checked :
    checkWeights base12_1 3 5 27 base12_1Weights = true := by decide +kernel

private abbrev base12_2 : List Nat := [7, 24, 194, 145, 3, 2, 6, 3, 2, 2, 1, 0]
private def base12_2Weights : List WeightedRow := [((1224,4),8), ((1576,4),14), ((2244,4),8), ((2340,4),14), ((204,4),7), ((108,4),14), ((786,4),14), ((2194,4),5), ((1170,4),5), ((1546,4),14), ((2310,4),14), ((142,4),9), ((2241,4),8), ((801,4),9), ((2145,4),5), ((1121,4),5), ((1553,4),8), ((2321,4),8), ((785,4),7), ((1169,4),8)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem base12_2Checked :
    checkWeights base12_2 3 24 128 base12_2Weights = true := by decide +kernel

private abbrev base12_3 : List Nat := [7, 280, 146, 145, 3, 2, 6, 3, 2, 2, 1, 0]
private def base12_3Weights : List WeightedRow := [((1224,4),2), ((1576,4),1), ((2340,4),2), ((804,4),1), ((108,4),1), ((786,4),1), ((2194,4),2), ((138,3),1), ((2310,4),1), ((526,4),2), ((2241,4),1), ((1121,4),1), ((1553,4),2), ((2321,4),1), ((1169,4),1)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem base12_3Checked :
    checkWeights base12_3 3 3 15 base12_3Weights = true := by decide +kernel

private abbrev base12_4 : List Nat := [7, 280, 194, 137, 3, 2, 6, 3, 2, 2, 1, 0]
private def base12_4Weights : List WeightedRow := [((1552,3),1), ((1168,3),1), ((1096,3),1), ((1576,4),3), ((1128,4),2), ((196,3),1), ((2244,4),2), ((2340,4),2), ((2148,4),1), ((76,3),1), ((108,4),2), ((530,3),1), ((786,4),2), ((2194,4),3), ((522,3),1), ((778,4),2), ((134,3),1), ((2182,4),2), ((270,4),3), ((1217,4),3), ((801,4),2), ((2145,4),2), ((1553,4),2), ((2321,4),2), ((785,4),1), ((1169,4),2)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem base12_4Checked :
    checkWeights base12_4 3 7 36 base12_4Weights = true := by decide +kernel

private abbrev base12_5 : List Nat := [7, 24, 98, 137, 3, 12, 9, 3, 2, 2, 1, 0]
private def base12_5Weights : List WeightedRow := [((840,4),3), ((2212,4),1), ((1188,4),2), ((108,4),3), ((2322,4),1), ((786,4),1), ((1170,4),1), ((1546,4),2), ((2182,4),2), ((1038,4),1), ((2145,4),2), ((1553,4),1), ((785,4),2), ((2193,4),2), ((1169,4),1)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem base12_5Checked :
    checkWeights base12_5 3 4 19 base12_5Weights = true := by decide +kernel

private abbrev base12_6 : List Nat := [7, 132, 268, 137, 3, 12, 9, 3, 2, 2, 1, 0]
private def base12_6Weights : List WeightedRow := [((2192,3),7), ((584,3),5), ((840,4),12), ((104,3),5), ((788,4),11), ((148,3),7), ((1172,4),12), ((1548,4),17), ((2370,4),11), ((2210,4),11), ((1066,4),5), ((106,4),12), ((1158,4),8), ((1038,4),3), ((270,4),11), ((2369,4),3), ((833,4),5), ((1185,4),9), ((2145,4),17), ((1553,4),9), ((2321,4),7), ((785,4),1), ((2193,4),12)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem base12_6Checked :
    checkWeights base12_6 3 28 148 base12_6Weights = true := by decide +kernel

private abbrev base12_7 : List Nat := [7, 196, 268, 137, 3, 12, 9, 3, 2, 2, 1, 0]
private def base12_7Weights : List WeightedRow := [((2192,3),1), ((840,4),3), ((788,4),3), ((148,3),1), ((1172,4),1), ((780,4),1), ((2210,4),3), ((106,4),4), ((1158,4),1), ((1038,4),2), ((2369,4),2), ((1185,4),2), ((2145,4),1), ((1553,4),2), ((2321,4),1), ((2193,4),1)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem base12_7Checked :
    checkWeights base12_7 3 4 21 base12_7Weights = true := by decide +kernel

private abbrev base12_8 : List Nat := [7, 388, 258, 134, 3, 12, 9, 3, 2, 2, 1, 0]
private def base12_8Weights : List WeightedRow := [((1560,4),2), ((792,4),1), ((1176,4),1), ((836,4),1), ((1188,4),1), ((2370,4),1), ((2210,4),1), ((102,4),2), ((270,4),1), ((142,4),1), ((833,4),1), ((1185,4),1), ((2145,4),2), ((2321,4),1), ((2193,4),1)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem base12_8Checked :
    checkWeights base12_8 3 3 14 base12_8Weights = true := by decide +kernel

private abbrev base12_9 : List Nat := [7, 388, 268, 137, 3, 12, 9, 3, 2, 2, 1, 0]
private def base12_9Weights : List WeightedRow := [((2192,3),1), ((584,3),1), ((840,4),3), ((1064,3),2), ((788,4),3), ((1172,4),3), ((1548,4),3), ((2370,4),2), ((2210,4),4), ((106,4),4), ((134,3),2), ((270,4),2), ((2369,4),1), ((833,4),1), ((1185,4),2), ((2145,4),2), ((1553,4),3), ((2321,4),1), ((2193,4),3)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem base12_9Checked :
    checkWeights base12_9 3 6 32 base12_9Weights = true := by decide +kernel

private abbrev base12_10 : List Nat := [15, 296, 196, 140, 73, 1, 6, 3, 2, 2, 1, 0]
private def base12_10Weights : List WeightedRow := [((1232,4),1), ((808,4),1), ((1560,4),1), ((2244,4),1), ((778,4),1), ((2310,4),1), ((86,4),1), ((30,4),1), ((2241,4),1), ((1569,4),1), ((2337,4),1), ((1185,4),1)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem base12_10Checked :
    checkWeights base12_10 3 1 7 base12_10Weights = true := by decide +kernel

private abbrev base12_11 : List Nat := [15, 352, 196, 146, 82, 3, 10, 10, 1, 0, 1, 0]
private def base12_11Weights : List WeightedRow := [((1328,4),1), ((1544,3),1), ((1176,4),1), ((2308,3),1), ((404,4),1), ((204,4),1), ((2594,4),1), ((50,3),1), ((586,4),1), ((2118,4),1), ((30,4),1), ((1409,4),1), ((2625,4),1), ((193,3),1), ((1569,4),1), ((2337,4),1)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem base12_11Checked :
    checkWeights base12_11 3 2 12 base12_11Weights = true := by decide +kernel

private def atlas15 : List (List Nat) := []
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem covers15 :
    (levels normalized 5 15 4).all (fun b => decide (b∈atlas15)) = true := by decide +kernel

private theorem atDegree0 {b : List Nat} (hb : b∈levels normalized 5 15 4)
    (cs : List Nat) (_h : Extension 6 0 b cs) : 32 ≤ edges_ (attach cs b) := by
  have mem := of_decide_eq_true (List.all_eq_true.mp covers15 b hb)
  simp [atlas15] at mem

private def atlas14 : List (List Nat) := []
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem covers14 :
    (levels normalized 5 14 4).all (fun b => decide (b∈atlas14)) = true := by decide +kernel

private theorem atDegree1 {b : List Nat} (hb : b∈levels normalized 5 14 4)
    (cs : List Nat) (_h : Extension 6 1 b cs) : 32 ≤ edges_ (attach cs b) := by
  have mem := of_decide_eq_true (List.all_eq_true.mp covers14 b hb)
  simp [atlas14] at mem

private def atlas13 : List (List Nat) := [base13_0]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem covers13 :
    (levels normalized 5 13 4).all (fun b => decide (b∈atlas13)) = true := by decide +kernel

private theorem atDegree2 {b : List Nat} (hb : b∈levels normalized 5 13 4)
    (cs : List Nat) (h : Extension 6 2 b cs) : 32 ≤ edges_ (attach cs b) := by
  have mem := of_decide_eq_true (List.all_eq_true.mp covers13 b hb)
  simp only [atlas13,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl
  · exact viaWeights _ cs 2 _ _ _ h base13_0Checked

private def atlas12 : List (List Nat) := [base12_0, base12_1, base12_2, base12_3, base12_4, base12_5, base12_6, base12_7, base12_8, base12_9, base12_10, base12_11]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem covers12 :
    (levels normalized 5 12 4).all (fun b => decide (b∈atlas12)) = true := by decide +kernel

private theorem atDegree3 {b : List Nat} (hb : b∈levels normalized 5 12 4)
    (cs : List Nat) (h : Extension 6 3 b cs) : 32 ≤ edges_ (attach cs b) := by
  have mem := of_decide_eq_true (List.all_eq_true.mp covers12 b hb)
  simp only [atlas12,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact viaWeights _ cs 3 _ _ _ h base12_0Checked
  · exact viaWeights _ cs 3 _ _ _ h base12_1Checked
  · exact viaWeights _ cs 3 _ _ _ h base12_2Checked
  · exact viaWeights _ cs 3 _ _ _ h base12_3Checked
  · exact viaWeights _ cs 3 _ _ _ h base12_4Checked
  · exact viaWeights _ cs 3 _ _ _ h base12_5Checked
  · exact viaWeights _ cs 3 _ _ _ h base12_6Checked
  · exact viaWeights _ cs 3 _ _ _ h base12_7Checked
  · exact viaWeights _ cs 3 _ _ _ h base12_8Checked
  · exact viaWeights _ cs 3 _ _ _ h base12_9Checked
  · exact viaWeights _ cs 3 _ _ _ h base12_10Checked
  · exact viaWeights _ cs 3 _ _ _ h base12_11Checked

theorem atLeast32 : OMA.RamseyTwentyTwo.Sixteen := by
  apply density_of_packing
  intro d hd b hb cs h
  interval_cases d
  · exact atDegree0 hb cs h
  · exact atDegree1 hb cs h
  · exact atDegree2 hb cs h
  · exact atDegree3 hb cs h

end OMA.RamseySixteen


theorem OMA.solution : OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1.H1 :=
  OMA.RamseyTwentyTwo.fromSmallerOrders OMA.RamseyFifteen.atLeast25 OMA.RamseySixteen.atLeast32
