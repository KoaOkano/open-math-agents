import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1
import Mathlib.Data.Sym.Sym2.Order

/-!
# The upper edge count for nine-vertex triangle-good graphs

Brandt, Brinkmann and Harmuth give 27 as the largest edge count in Table 2.
We use the three 17-vertex hosts specified by @physbuzz in registry PR 8675.
If their intersection has at least 28 edges, retain exactly 28. The graph of
missing edges on the nine vertices then has two embedding-invariant counts:
its length-five walks and the sum of the cubes of its vertex degrees.
-/

-- Lean formalization: @KoaOkano.

open Finset SimpleGraph

namespace RamseyNine

private def pairs {V : Type*} [DecidableEq V] (S : Finset V) :=
  S.sym2.filter (fun e => ¬ e.IsDiag)

private lemma pairs_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (S : Finset V) : pairs (S.map f) = (pairs S).map f.sym2Map := by
  rw [pairs, Finset.sym2_map, Finset.filter_map]
  congr 1
  ext e
  simp only [pairs, mem_filter, Function.comp_apply]
  change (_ ∧ ¬(e.map f).IsDiag) ↔ (_ ∧ ¬e.IsDiag)
  rw [Sym2.isDiag_map f.injective]

private def neighbors {V : Type*} [DecidableEq V] (S : Finset V) (B : Finset (Sym2 V)) (v : V) :=
  S.filter (fun w => s(v,w) ∈ B)

private lemma neighbors_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (S : Finset V) (B : Finset (Sym2 V)) (v : V) :
    neighbors (S.map f) (B.map f.sym2Map) (f v) = (neighbors S B v).map f := by
  simp only [neighbors, Finset.filter_map]
  congr 1
  apply Finset.filter_congr
  intro w _
  change f.sym2Map s(v,w) ∈ B.map f.sym2Map ↔ _
  exact Finset.mem_map' f.sym2Map

private def signature {V : Type*} [DecidableEq V] (S : Finset V) (B : Finset (Sym2 V)) :
    Nat × Nat :=
  let N := neighbors S B
  let q := fun v => ∑ w ∈ N v, (N w).card
  (∑ v ∈ S, ∑ w ∈ N v, q v * q w, ∑ v ∈ S, (N v).card ^ 3)

private lemma signature_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (S : Finset V) (B : Finset (Sym2 V)) :
    signature (S.map f) (B.map f.sym2Map) = signature S B := by
  simp only [signature, Finset.sum_map, neighbors_map, Finset.card_map]

private def board (mask : Nat) : SimpleGraph (Fin 17) where
  Adj i j := i ≠ j ∧ mask.testBit ((min i j).val*17+(max i j).val) = false
  symm := ⟨fun i j h => ⟨h.1.symm, by simpa only [min_comm j i, max_comm j i] using h.2⟩⟩
  loopless := ⟨by simp⟩

private instance (mask : Nat) : DecidableRel (board mask).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ _ = false))

private def allowed (mask : Nat) (S : Finset (Fin 17)) :=
  S.sym2.filter (fun e => e ∈ (board mask).edgeSet)

private def BoundOn (m : Nat) (P : Nat × Nat → Bool) (S : Finset (Fin 17)) : Prop :=
  ∀ E ⊆ allowed m S, E.card = 28 → P (signature S (pairs S \ E)) = true

private lemma liftBound {m P S T} (f : Fin 17 ↪ Fin 17) (target : S.map f = T)
    (maps : ∀ i ∈ S, ∀ j ∈ S, (board m).Adj i j → (board m).Adj (f i) (f j))
    (h : BoundOn m P T) : BoundOn m P S := by
  subst T
  intro E he hc
  have inc : E.map f.sym2Map ⊆ allowed m (S.map f) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨hs,hadj⟩ := Finset.mem_filter.mp (he hx)
    refine Finset.mem_filter.mpr ⟨?_,?_⟩
    · rw [Finset.sym2_map]
      exact Finset.mem_map_of_mem _ hs
    · induction x using Sym2.ind with
      | _ i j =>
        obtain ⟨hi,hj⟩ := Finset.mk_mem_sym2_iff.mp hs
        exact maps i hi j hj hadj
  have passed := h _ inc (by simpa using hc)
  rwa [pairs_map, ← Finset.map_sdiff, signature_map] at passed

private lemma placement {m P} (h : ∀ S : Finset (Fin 17), S.card = 9 → BoundOn m P S)
    {D : SimpleGraph (Fin 9)} [DecidableRel D.Adj] (f : Fin 9 ↪ Fin 17)
    (maps : ∀ i j, D.Adj i j → (board m).Adj (f i) (f j))
    (E : Finset (Sym2 (Fin 9))) (he : E ⊆ D.edgeFinset) (hc : E.card = 28) :
    P (signature univ (pairs univ \ E)) = true := by
  let S := (univ : Finset (Fin 9)).map f
  have inc : E.map f.sym2Map ⊆ allowed m S := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · change f.sym2Map x ∈ (univ.map f).sym2
      rw [sym2_map]
      exact mem_map_of_mem _ (by simp)
    · induction x using Sym2.ind with
      | _ i j => exact maps i j (SimpleGraph.mem_edgeFinset.mp (he hx))
  have pass := h S (by simp [S]) _ inc (by simpa using hc)
  simpa only [S, pairs_map, ← Finset.map_sdiff, signature_map] using pass

private def vertexBits (S : Finset (Fin 17)) : Nat :=
  S.fold (· ||| ·) 0 (fun x => 2 ^ x.val)

private lemma vertex_insert {i : Fin 17} {S : Finset (Fin 17)} (h : i ∉ S) :
    vertexBits (insert i S) = 2^i.val ||| vertexBits S := by simp [vertexBits, h]

private lemma vertexBit (S : Finset (Fin 17)) (v : Fin 17) :
    (vertexBits S).testBit v.val = true ↔ v ∈ S := by
  induction S using Finset.induction_on with
  | empty => simp [vertexBits]
  | @insert i S hi ih =>
    rw [vertex_insert hi, Nat.testBit_or, Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, decide_eq_true_eq, ih, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl (Fin.ext h.symm)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (congrArg Fin.val h.symm)
      · exact Or.inr h



private def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => sumTo f n + f n

private lemma sumTo_eq (f : Nat → Nat) (n : Nat) :
    sumTo f n = ∑ i ∈ range n, f i := by
  induction n <;> simp [sumTo, sum_range_succ, *]

private def bitCount (x n : Nat) := sumTo (fun i => if x.testBit i then 1 else 0) n

private lemma count_split (x a b : Nat) :
    bitCount x (a+b) = bitCount x a + bitCount (x >>> a) b := by
  induction b with
  | zero => simp [bitCount, sumTo]
  | succ b ih =>
    change bitCount x (a+b) + _ = bitCount x a + (bitCount (x >>> a) b + _)
    simp only [ih, Nat.testBit_shiftRight, Nat.add_assoc]
    rfl

private lemma count_mod (x k : Nat) : bitCount (x % 2^k) k = bitCount x k := by
  simp only [bitCount, sumTo_eq]
  apply sum_congr rfl
  intro i hi
  simp [Nat.testBit_mod_two_pow, mem_range.mp hi]

private def nibble (z : Nat) := (155746543670344 >>> (3 * (z % 16))) % 8

private lemma nibble_eq (z : Nat) : nibble z = bitCount z 4 := by
  have check : ∀ i : Fin 16, nibble i.val = bitCount i.val 4 := by decide +kernel
  rw [← count_mod z 4]
  simpa [nibble, Nat.mod_mod] using check ⟨z%16, Nat.mod_lt _ (by decide)⟩

private def pop17 (z : Nat) : Nat :=
  nibble z + nibble (z >>> 4) + nibble (z >>> 8) + nibble (z >>> 12) +
    (if z.testBit 16 then 1 else 0)

private lemma pop17_eq (z : Nat) : pop17 z = bitCount z 17 := by
  have a := count_split z 4 4
  have b := count_split z 8 4
  have c := count_split z 12 4
  change _ = bitCount z 16 + _
  simp only [pop17, nibble_eq, ← a, ← b, ← c]

private lemma pop17_card (x : Nat) :
    ((univ : Finset (Fin 17)).filter (fun i => x.testBit i.val = true)).card = pop17 x := by
  rw [pop17_eq, bitCount, sumTo_eq, card_eq_sum_ones, sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if x.testBit i then 1 else 0) 17

private def orderEdge : Sym2 (Fin 17) ↪ (Σ _ : Fin 17, Fin 17) where
  toFun e := ⟨e.inf,e.sup⟩
  inj' := by
    intro x y h
    exact Sym2.inf_eq_inf_and_sup_eq_sup.mp
      ⟨congrArg (fun e : Σ _ : Fin 17, Fin 17 => e.1) h,
       congrArg (fun e : Σ _ : Fin 17, Fin 17 => e.2) h⟩

private def rowAt (rows : Array Nat) (i : Nat) := rows[i]?.getD 0

private def capacity (rows : Array Nat) (x : Nat) : Nat :=
  sumTo (fun i => if x.testBit i then pop17 (x &&& rowAt rows i) else 0) 17

private lemma capacity_bound {m} (rows : Array Nat)
    (hr : ∀ i j : Fin 17, i < j → (board m).Adj i j → (rowAt rows i.val).testBit j.val = true)
    (S : Finset (Fin 17)) : (allowed m S).card ≤ capacity rows (vertexBits S) := by
  let x := vertexBits S
  let slots (i : Fin 17) : Finset (Fin 17) :=
    if x.testBit i.val then univ.filter (fun j => (x &&& rowAt rows i.val).testBit j.val = true)
    else ∅
  have pair {i j : Fin 17} (hi : i ∈ S) (hj : j ∈ S) (ij : i < j) (ha : (board m).Adj i j) :
      j ∈ slots i := by
    have hi' := (vertexBit S i).mpr hi
    have hj' := (vertexBit S j).mpr hj
    simp [slots, x, hi', Nat.testBit_and, hj', hr i j ij ha]
  have inc : (allowed m S).map orderEdge ⊆ univ.sigma slots := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := mem_map.mp hq
    obtain ⟨vs, ha⟩ := mem_filter.mp he
    induction e using Sym2.ind with
    | _ i j =>
      obtain ⟨hi, hj⟩ := mk_mem_sym2_iff.mp vs
      change (board m).Adj i j at ha
      rcases lt_or_gt_of_ne ha.1 with hij|hji
      · have eq : orderEdge s(i,j) = ⟨i,j⟩ := by
          change (⟨min i j,max i j⟩ : Σ _ : Fin 17, Fin 17) = _
          rw [min_eq_left hij.le, max_eq_right hij.le]
        simpa [eq] using pair hi hj hij ha
      · have eq : orderEdge s(i,j) = ⟨j,i⟩ := by
          change (⟨min i j,max i j⟩ : Σ _ : Fin 17, Fin 17) = _
          rw [min_eq_right hji.le, max_eq_left hji.le]
        simpa [eq] using pair hj hi hji ha.symm
  have h := card_le_card inc
  rw [card_map, card_sigma] at h
  apply h.trans_eq
  rw [capacity, sumTo_eq, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  by_cases hi : (vertexBits S).testBit i.val = true
  · simpa only [slots, x, hi, if_true] using pop17_card (vertexBits S &&& rowAt rows i.val)
  · simp [slots, x, hi]


private structure Model (m : Nat) (P : Nat × Nat → Bool) where
  vertices : Finset (Fin 17)
  bits : Nat
  encode : bits = vertexBits vertices
  verified : BoundOn m P vertices

private def noModel (m P) : Model m P :=
  ⟨∅, 0, rfl, by
    intro E he hc
    have eq : E = ∅ := by simpa [allowed] using he
    simp [eq] at hc⟩

-- A route stores the vertex set, model index, and two inverse vertex maps.
-- The finite checks test the maps on this image of nine vertices.
private def digit (w i : Nat) : Fin 17 := Fin.ofNat 17 ((w >>> (5*i)) % 32)

private def route (book : Array (List Nat)) (x : Nat) : Nat :=
  ((book[x%257]?.getD []).find? (fun w => w % 131072 == x)).getD 0

private def passes {m P} (models : Array (Model m P)) (book : Array (List Nat))
    (rows : Array Nat) (x : Nat) : Bool :=
  if capacity rows x < 28 then true
  else
    let w := route book x
    let root := models[((w >>> 17) % 8)]?.getD (noModel m P)
    let p := digit (w >>> 20)
    let inv := digit (w >>> 105)
    decide (∀ i : Fin 17, inv (p i.val).val = i) &&
    decide (∀ i : Fin 17, x.testBit i.val = root.bits.testBit (p i.val).val) &&
    decide (∀ i : Fin 17, x.testBit i.val = true → ∀ j : Fin 17,
      x.testBit j.val = true → (board m).Adj i j → (board m).Adj (p i.val) (p j.val))

private lemma route_sound {m P} (models : Array (Model m P)) (book : Array (List Nat))
    (rows : Array Nat)
    (hr : ∀ i j : Fin 17, i < j → (board m).Adj i j → (rowAt rows i.val).testBit j.val = true)
    (S : Finset (Fin 17)) (pass : passes models book rows (vertexBits S) = true) :
    BoundOn m P S := by
  unfold passes at pass
  split at pass
  · intro E hE hc
    have size := (card_le_card hE).trans (capacity_bound rows hr S)
    omega
  · let w := route book (vertexBits S)
    let root := models[((w >>> 17) % 8)]?.getD (noModel m P)
    let p (i : Fin 17) := digit (w >>> 20) i.val
    let inv (i : Fin 17) := digit (w >>> 105) i.val
    obtain ⟨⟨hInv, hBits⟩, hEdge⟩ := by
      simpa only [Bool.and_eq_true_iff, decide_eq_true_eq] using pass
    have left : Function.LeftInverse inv p := hInv
    let emb : Fin 17 ↪ Fin 17 := ⟨p, left.injective⟩
    have same (i : Fin 17) : i ∈ S ↔ p i ∈ root.vertices := by
      rw [← vertexBit S, ← vertexBit root.vertices, ← root.encode]
      exact eq_iff_iff.mp (congrArg (· = true) (hBits i))
    apply liftBound emb _ _ root.verified
    · ext j
      obtain ⟨i,rfl⟩ := Finite.surjective_of_injective left.injective j
      change emb i ∈ S.map emb ↔ _
      rw [Finset.mem_map']
      exact same i
    · intro i hi j hj
      exact hEdge i ((vertexBit S i).mpr hi) j ((vertexBit S j).mpr hj)


-- The two directions of an undirected edge occupy symmetric matrix entries.
private def cell (i j : Fin 17) := 17*i.val + j.val

private lemma cell_inj {a b i j : Fin 17} :
    cell a b = cell i j ↔ a = i ∧ b = j := by
  constructor
  · intro h
    dsimp [cell] at h
    constructor <;> apply Fin.ext <;> omega
  · rintro ⟨rfl,rfl⟩
    rfl

private def atom (e : Sym2 (Fin 17)) : Nat :=
  Sym2.lift ⟨fun i j => 2^(cell i j) ||| 2^(cell j i), fun _ _ => Nat.or_comm _ _⟩ e

private lemma atom_bit (e : Sym2 (Fin 17)) (i j : Fin 17) :
    (atom e).testBit (cell i j) = true ↔ e = s(i,j) := by
  induction e using Sym2.ind with
  | _ a b =>
    change (2^(cell a b) ||| 2^(cell b a)).testBit _ = true ↔ _
    simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq,
      cell_inj, Sym2.eq_iff]
    tauto

private def edgeBits (B : Finset (Sym2 (Fin 17))) : Nat := B.fold (· ||| ·) 0 atom

private lemma edge_insert {e : Sym2 (Fin 17)} {B : Finset (Sym2 (Fin 17))} (h : e ∉ B) :
    edgeBits (insert e B) = atom e ||| edgeBits B := by simp [edgeBits, h]

private lemma edgeBit (B : Finset (Sym2 (Fin 17))) (i j : Fin 17) :
    (edgeBits B).testBit (cell i j) = true ↔ s(i,j) ∈ B := by
  induction B using Finset.induction_on with
  | empty => simp [edgeBits]
  | @insert e B he ih =>
    rw [edge_insert he, Nat.testBit_or, Bool.or_eq_true, atom_bit, ih, mem_insert]
    tauto

private def degreeAt (x z : Nat) (i : Fin 17) := pop17 (x &&& (z >>> (17*i.val)))

private def neighborSum (S : Finset (Fin 17)) (z : Nat) (i : Fin 17) (f : Fin 17 → Nat) :=
  ∑ j ∈ S, if z.testBit (cell i j) then f j else 0

private def measures (S : Finset (Fin 17)) (x z : Nat) : Nat × Nat :=
  let d := degreeAt x z
  let q := fun i => neighborSum S z i d
  (∑ i ∈ S, q i * neighborSum S z i q, ∑ i ∈ S, (d i)^3)

private lemma measures_eq {S : Finset (Fin 17)} {B : Finset (Sym2 (Fin 17))} {z : Nat}
    (hz : ∀ i j : Fin 17, z.testBit (cell i j) = true ↔ s(i,j) ∈ B) :
    measures S (vertexBits S) z = signature S B := by
  have hd (i : Fin 17) : degreeAt (vertexBits S) z i = (neighbors S B i).card := by
    rw [degreeAt, ← pop17_card]
    congr 1
    ext j
    simp only [neighbors, mem_filter, mem_univ, true_and, Nat.testBit_and, Bool.and_eq_true,
      vertexBit, Nat.testBit_shiftRight]
    exact and_congr_right fun _ => hz i j
  have hq (i : Fin 17) (f : Fin 17 → Nat) :
      neighborSum S z i f = ∑ j ∈ neighbors S B i, f j := by
    rw [neighbors, sum_filter, neighborSum]
    apply sum_congr rfl
    intro j _
    simp only [hz]
  simp only [measures, signature, hd, hq, Finset.mul_sum]

private def edgeScan (f : Nat → Bool) (base : Nat) :
    List (Sym2 (Fin 17)) → Nat → Bool
  | _, 0 => f base
  | [], _+1 => true
  | e::es, k+1 => edgeScan f (base ||| atom e) es k && edgeScan f base es (k+1)

private lemma edgeScan_ok {f} (base : Nat) (xs : List (Sym2 (Fin 17)))
    (F : Finset (Sym2 (Fin 17))) (hF : F ⊆ xs.toFinset)
    (ok : edgeScan f base xs F.card = true) : f (base ||| edgeBits F) = true := by
  induction xs generalizing base F with
  | nil =>
    have e : F = ∅ := by simpa using hF
    simpa [e, edgeScan, edgeBits] using ok
  | cons e es ih =>
    by_cases em : F = ∅
    · simpa [em, edgeScan, edgeBits] using ok
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero
      (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr em))
    rw [hk] at ok
    obtain ⟨take, skip⟩ := Bool.and_eq_true_iff.mp ok
    by_cases he : e ∈ F
    · have sub : F.erase e ⊆ es.toFinset := by
        intro j hj
        have h := hF (mem_of_mem_erase hj)
        simpa [ne_of_mem_erase hj] using h
      have hc : (F.erase e).card = k := by rw [card_erase_of_mem he, hk]; rfl
      have got := ih (base ||| atom e) (F.erase e) sub (hc.symm ▸ take)
      have eq : edgeBits F = atom e ||| edgeBits (F.erase e) := by
        simpa only [insert_erase he] using edge_insert (notMem_erase e F)
      simpa only [eq, Nat.or_assoc] using got
    · have sub : F ⊆ es.toFinset := by
        intro j hj
        have ne : j ≠ e := fun eq => he (eq ▸ hj)
        simpa [ne] using hF hj
      exact ih base F sub (hk ▸ skip)

private lemma edgeNode {f base e es k}
    (take : edgeScan f (base ||| atom e) es k = true) (skip : edgeScan f base es (k+1) = true) :
    edgeScan f base (e::es) (k+1) = true := Bool.and_eq_true_iff.mpr ⟨take, skip⟩

private lemma model_bound {m P S} (xs : List (Sym2 (Fin 17))) (x z k : Nat)
    (hx : x = vertexBits S) (hz : z = edgeBits (pairs S \ allowed m S))
    (covered : allowed m S ⊆ xs.toFinset) (hk : k = (allowed m S).card - 28)
    (ok : edgeScan (fun v => P (measures S x v)) z xs k = true) : BoundOn m P S := by
  subst x z k
  intro E hE hc
  let A := allowed m S
  let F := A \ E
  have hf : F ⊆ xs.toFinset := Finset.sdiff_subset.trans covered
  have sz : F.card = A.card - 28 := by rw [Finset.card_sdiff_of_subset hE, hc]
  have pass := edgeScan_ok _ xs F hf (sz.symm ▸ ok)
  rw [measures_eq (B := pairs S \ E)] at pass
  · exact pass
  · intro i j
    simp only [Nat.testBit_or, Bool.or_eq_true, edgeBit, mem_sdiff, F, A]
    have hpa : allowed m S ⊆ pairs S := by
      intro e he
      obtain ⟨hs, ha⟩ := mem_filter.mp he
      refine mem_filter.mpr ⟨hs, ?_⟩
      induction e using Sym2.ind with
      | _ a b => exact fun h => ha.1 (Sym2.mk_isDiag_iff.mp h)
    grind


-- Enumerate subsets of a given size by deciding whether to include the
-- next vertex. Each subtree can be verified as a separate kernel computation.
private def scan (f : Nat → Bool) (base : Nat) :
    List (Fin 17) → Nat → Bool
  | _, 0 => f base
  | [], _+1 => true
  | i::is, k+1 => scan f (base ||| 2^i.val) is k && scan f base is (k+1)

private lemma scan_sound {f} (base : Nat) (xs : List (Fin 17))
    (T : Finset (Fin 17)) (hT : T ⊆ xs.toFinset)
    (ok : scan f base xs T.card = true) : f (base ||| vertexBits T) = true := by
  induction xs generalizing base T with
  | nil =>
    have e : T = ∅ := by simpa using hT
    simpa [e, scan, vertexBits] using ok
  | cons i is ih =>
    by_cases em : T = ∅
    · simpa [em, scan, vertexBits] using ok
    have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr em)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    rw [hk] at ok
    obtain ⟨take, skip⟩ := Bool.and_eq_true_iff.mp ok
    by_cases hi : i ∈ T
    · have sub : T.erase i ⊆ is.toFinset := by
        intro j hj
        have h := hT (Finset.mem_of_mem_erase hj)
        simpa [Finset.ne_of_mem_erase hj] using h
      have hc : (T.erase i).card = k := by rw [Finset.card_erase_of_mem hi, hk]; rfl
      have got := ih (base ||| 2^i.val) (T.erase i) sub (hc.symm ▸ take)
      have eq : vertexBits T = 2^i.val ||| vertexBits (T.erase i) := by
        simpa only [Finset.insert_erase hi] using vertex_insert (Finset.notMem_erase i T)
      simpa only [eq, Nat.or_assoc] using got
    · have sub : T ⊆ is.toFinset := by
        intro j hj
        have ne : j ≠ i := fun eq => hi (eq ▸ hj)
        simpa [ne] using hT hj
      exact ih base T sub (hk ▸ skip)

private lemma scan_node {f base} {i : Fin 17} {is k}
    (a : scan f (base ||| 2^i.val) is k = true) (b : scan f base is (k+1) = true) :
    scan f base (i::is) (k+1) = true := Bool.and_eq_true_iff.mpr ⟨a,b⟩


private def shared (v : Nat × Nat) : Bool :=
  let b : Nat := match v.2 with
    | 88 => 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
    | 100 => 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
    | 106 => 0x10000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
    | 112 => 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
    | 118 => 0x10000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
    | 124 => 0x100000000000000000000000000000100000000000000000100000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
    | 136 => 0x10000000000010000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
    | _ => 0
  b != 0 && b.testBit v.1

private def onlyFirst (v : Nat × Nat) : Bool :=
  let b : Nat := match v.2 with
    | 58 => 0x400000100000000000000000000000000000000000000000000000000
    | 64 => 0x10000000000000000000000000000000000000000000000000000000000000000
    | 70 => 0x10000010000001000000100000000000000000000000000000000000000000000000000000000
    | 76 => 0x1000000140000000000000000000000000000000000000000000000000000000000000000000000000000
    | 82 => 0x100000000000000000000000010000040010000000000001000000000000000000000000000000000000000000000000000000000000000000
    | 88 => 0x110000000000000010101000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
    | 94 => 0x4000010000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
    | 100 => 0x4000000000000000000000000000100000040010000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000
    | 106 => 0x4000004000000000000000001000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
    | 118 => 0x10000000000000000000000000000000000000000000000000000000004000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
    | _ => 0
  b != 0 && b.testBit v.1

private def firstSig (v : Nat × Nat) := shared v || onlyFirst v


namespace First

private def mask : Nat :=
  3794289654249960540213394811365649999491732653694874493236865398263569676450744992


namespace Seed0

private def vertices : Finset (Fin 17) :=
  {0,3,6,8,10,12,13,14,16}


private def measure : Nat → Bool :=
  fun z => firstSig (measures vertices 95561 z)


private def es30 : List (Sym2 (Fin 17)) :=
  []


private def es29 : List (Sym2 (Fin 17)) :=
  s(14,16) :: es30


private def es28 : List (Sym2 (Fin 17)) :=
  s(13,16) :: es29


private def es27 : List (Sym2 (Fin 17)) :=
  s(13,14) :: es28


private def es26 : List (Sym2 (Fin 17)) :=
  s(12,16) :: es27


private def es25 : List (Sym2 (Fin 17)) :=
  s(12,14) :: es26


private def es24 : List (Sym2 (Fin 17)) :=
  s(12,13) :: es25


private def es23 : List (Sym2 (Fin 17)) :=
  s(10,16) :: es24


private def es22 : List (Sym2 (Fin 17)) :=
  s(10,14) :: es23


private def es21 : List (Sym2 (Fin 17)) :=
  s(10,13) :: es22


private def es20 : List (Sym2 (Fin 17)) :=
  s(10,12) :: es21


private def es19 : List (Sym2 (Fin 17)) :=
  s(8,16) :: es20


private def es18 : List (Sym2 (Fin 17)) :=
  s(8,14) :: es19


private def es17 : List (Sym2 (Fin 17)) :=
  s(8,12) :: es18


private def es16 : List (Sym2 (Fin 17)) :=
  s(6,16) :: es17


private def es15 : List (Sym2 (Fin 17)) :=
  s(6,14) :: es16


private def es14 : List (Sym2 (Fin 17)) :=
  s(6,12) :: es15


private def es13 : List (Sym2 (Fin 17)) :=
  s(6,8) :: es14


private def es12 : List (Sym2 (Fin 17)) :=
  s(3,16) :: es13


private def es11 : List (Sym2 (Fin 17)) :=
  s(3,14) :: es12


private def es10 : List (Sym2 (Fin 17)) :=
  s(3,13) :: es11


private def es9 : List (Sym2 (Fin 17)) :=
  s(3,12) :: es10


private def es8 : List (Sym2 (Fin 17)) :=
  s(3,10) :: es9


private def es7 : List (Sym2 (Fin 17)) :=
  s(3,8) :: es8


private def es6 : List (Sym2 (Fin 17)) :=
  s(3,6) :: es7


private def es5 : List (Sym2 (Fin 17)) :=
  s(0,13) :: es6


private def es4 : List (Sym2 (Fin 17)) :=
  s(0,12) :: es5


private def es3 : List (Sym2 (Fin 17)) :=
  s(0,10) :: es4


private def es2 : List (Sym2 (Fin 17)) :=
  s(0,8) :: es3


private def es1 : List (Sym2 (Fin 17)) :=
  s(0,6) :: es2


private def es0 : List (Sym2 (Fin 17)) :=
  s(0,3) :: es1


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk0 : edgeScan measure 0x100000000402800000000000500000024000000090040000000000008000000014048 es2 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk1 : edgeScan measure 0x100000000402800000000000500000024010000090000000000000008000000014108 es3 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk2 : edgeScan measure 0x100000000402800000000000504000024000000090000000000000008000000014408 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk3 : edgeScan measure 0x100000000402800001000000500000024000000090000000000000008000000015008 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk4 : edgeScan measure 0x100000000402820000000000500000024000000090000000000000008000000016008 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk5 : edgeScan measure 0x100000000402800000000000500000024000000090000000000000008000000014008 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk6 : edgeScan measure 0x100000000402800000000000500000024010000090040000000000000000000014140 es3 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk7 : edgeScan measure 0x100000000402800000000000504000024000000090040000000000000000000014440 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk8 : edgeScan measure 0x100000000402800001000000500000024000000090040000000000000000000015040 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk9 : edgeScan measure 0x100000000402820000000000500000024000000090040000000000000000000016040 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk10 : edgeScan measure 0x100000000402800000000000500000024000000090040000000000000000000014040 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk11 : edgeScan measure 0x100000000402800000000000504000024010000090000000000000000000000014500 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk12 : edgeScan measure 0x100000000402800001000000500000024010000090000000000000000000000015100 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk13 : edgeScan measure 0x100000000402820000000000500000024010000090000000000000000000000016100 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk14 : edgeScan measure 0x100000000402800000000000500000024010000090000000000000000000000014100 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk15 : edgeScan measure 0x100000000402800001000000504000024000000090000000000000000000000015400 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk16 : edgeScan measure 0x100000000402820000000000504000024000000090000000000000000000000016400 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk17 : edgeScan measure 0x100000000402800000000000504000024000000090000000000000000000000014400 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk18 : edgeScan measure 0x100000000402820001000000500000024000000090000000000000000000000017000 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk19 : edgeScan measure 0x100000000402800001000000500000024000000090000000000000000000000015000 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk20 : edgeScan measure 0x100000000402820000000000500000024000000090000000000000000000000016000 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk21 : edgeScan measure 0x100000000402800000000000500000024000000090200000000000200000000014000 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk22 : edgeScan measure 0x100000000402800000000000500000024080000090000000000000800000000014000 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk23 : edgeScan measure 0x100000000402800000000000520000024000000090000000000002000000000014000 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk24 : edgeScan measure 0x100000000402800008000000500000024000000090000000000008000000000014000 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk25 : edgeScan measure 0x100000000402900000000000500000024000000090000000000010000000000014000 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk26 : edgeScan measure 0x100000002402800000000000500000024000000090000000000020000000000014000 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk27 : edgeScan measure 0x900000000402800000000000500000024000000090000000000080000000000014000 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk28 : edgeScan measure 0x100000000402800000000000500000024400000094000000000000000000000014000 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk29 : edgeScan measure 0x1000000004028000400000005000000240000000d0000000000000000000000014000 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk30 : edgeScan measure 0x100000010402800000000000500000024000000190000000000000000000000014000 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk31 : edgeScan measure 0x4100000000402800000000000500000024000000490000000000000000000000014000 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk32 : edgeScan measure 0x100000000402800100000000500000034000000090000000000000000000000014000 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk33 : edgeScan measure 0x100000040402800000000000500000064000000090000000000000000000000014000 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk34 : edgeScan measure 0x10100000000402800000000000500000124000000090000000000000000000000014000 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk35 : edgeScan measure 0x100000000402800400000004500000024000000090000000000000000000000014000 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk36 : edgeScan measure 0x10000000040a800000000008500000024000000090000000000000000000000014000 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk37 : edgeScan measure 0x100000100402800000000010500000024000000090000000000000000000000014000 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk38 : edgeScan measure 0x100000000402800000000000500000024000000090000000000000000000000014000 es23 2 = true := by decide +kernel


private theorem allCases : edgeScan measure 0x100000000402800000000000500000024000000090000000000000000000000014000 es0 2 = true :=
  (edgeNode (edgeNode chunk0 (edgeNode chunk1 (edgeNode chunk2 (edgeNode chunk3 (edgeNode chunk4 chunk5))))) (edgeNode (edgeNode chunk6 (edgeNode chunk7 (edgeNode chunk8 (edgeNode chunk9 chunk10)))) (edgeNode (edgeNode chunk11 (edgeNode chunk12 (edgeNode chunk13 chunk14))) (edgeNode (edgeNode chunk15 (edgeNode chunk16 chunk17)) (edgeNode (edgeNode chunk18 chunk19) (edgeNode chunk20 (edgeNode chunk21 (edgeNode chunk22 (edgeNode chunk23 (edgeNode chunk24 (edgeNode chunk25 (edgeNode chunk26 (edgeNode chunk27 (edgeNode chunk28 (edgeNode chunk29 (edgeNode chunk30 (edgeNode chunk31 (edgeNode chunk32 (edgeNode chunk33 (edgeNode chunk34 (edgeNode chunk35 (edgeNode chunk36 (edgeNode chunk37 chunk38)))))))))))))))))))))))


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private def model : Model mask firstSig :=
  ⟨vertices,95561,by decide +kernel,
    model_bound es0 95561 0x100000000402800000000000500000024000000090000000000000000000000014000 2
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) allCases⟩


end Seed0

namespace Seed1

private def vertices : Finset (Fin 17) :=
  {0,1,2,3,4,10,12,13,14}


private def measure : Nat → Bool :=
  fun z => firstSig (measures vertices 29727 z)


private def es28 : List (Sym2 (Fin 17)) :=
  []


private def es27 : List (Sym2 (Fin 17)) :=
  s(13,14) :: es28


private def es26 : List (Sym2 (Fin 17)) :=
  s(12,14) :: es27


private def es25 : List (Sym2 (Fin 17)) :=
  s(12,13) :: es26


private def es24 : List (Sym2 (Fin 17)) :=
  s(10,14) :: es25


private def es23 : List (Sym2 (Fin 17)) :=
  s(10,13) :: es24


private def es22 : List (Sym2 (Fin 17)) :=
  s(10,12) :: es23


private def es21 : List (Sym2 (Fin 17)) :=
  s(4,12) :: es22


private def es20 : List (Sym2 (Fin 17)) :=
  s(3,14) :: es21


private def es19 : List (Sym2 (Fin 17)) :=
  s(3,13) :: es20


private def es18 : List (Sym2 (Fin 17)) :=
  s(3,12) :: es19


private def es17 : List (Sym2 (Fin 17)) :=
  s(3,10) :: es18


private def es16 : List (Sym2 (Fin 17)) :=
  s(3,4) :: es17


private def es15 : List (Sym2 (Fin 17)) :=
  s(2,13) :: es16


private def es14 : List (Sym2 (Fin 17)) :=
  s(2,10) :: es15


private def es13 : List (Sym2 (Fin 17)) :=
  s(2,4) :: es14


private def es12 : List (Sym2 (Fin 17)) :=
  s(1,13) :: es13


private def es11 : List (Sym2 (Fin 17)) :=
  s(1,12) :: es12


private def es10 : List (Sym2 (Fin 17)) :=
  s(1,10) :: es11


private def es9 : List (Sym2 (Fin 17)) :=
  s(1,4) :: es10


private def es8 : List (Sym2 (Fin 17)) :=
  s(1,3) :: es9


private def es7 : List (Sym2 (Fin 17)) :=
  s(1,2) :: es8


private def es6 : List (Sym2 (Fin 17)) :=
  s(0,13) :: es7


private def es5 : List (Sym2 (Fin 17)) :=
  s(0,12) :: es6


private def es4 : List (Sym2 (Fin 17)) :=
  s(0,10) :: es5


private def es3 : List (Sym2 (Fin 17)) :=
  s(0,4) :: es4


private def es2 : List (Sym2 (Fin 17)) :=
  s(0,3) :: es3


private def es1 : List (Sym2 (Fin 17)) :=
  s(0,2) :: es2


private def es0 : List (Sym2 (Fin 17)) :=
  s(0,1) :: es1


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk0 : edgeScan measure 0x5c00200004000000040000000000000000000000640000021402080004000 es0 0 = true := by decide +kernel


private theorem allCases : edgeScan measure 0x5c00200004000000040000000000000000000000640000021402080004000 es0 0 = true :=
  chunk0


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private def model : Model mask firstSig :=
  ⟨vertices,29727,by decide +kernel,
    model_bound es0 29727 0x5c00200004000000040000000000000000000000640000021402080004000 0
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) allCases⟩


end Seed1

namespace Seed2

private def vertices : Finset (Fin 17) :=
  {0,1,2,3,5,7,10,12,13}


private def measure : Nat → Bool :=
  fun z => firstSig (measures vertices 13487 z)


private def es28 : List (Sym2 (Fin 17)) :=
  []


private def es27 : List (Sym2 (Fin 17)) :=
  s(12,13) :: es28


private def es26 : List (Sym2 (Fin 17)) :=
  s(10,13) :: es27


private def es25 : List (Sym2 (Fin 17)) :=
  s(10,12) :: es26


private def es24 : List (Sym2 (Fin 17)) :=
  s(7,13) :: es25


private def es23 : List (Sym2 (Fin 17)) :=
  s(7,10) :: es24


private def es22 : List (Sym2 (Fin 17)) :=
  s(5,13) :: es23


private def es21 : List (Sym2 (Fin 17)) :=
  s(5,10) :: es22


private def es20 : List (Sym2 (Fin 17)) :=
  s(5,7) :: es21


private def es19 : List (Sym2 (Fin 17)) :=
  s(3,13) :: es20


private def es18 : List (Sym2 (Fin 17)) :=
  s(3,12) :: es19


private def es17 : List (Sym2 (Fin 17)) :=
  s(3,10) :: es18


private def es16 : List (Sym2 (Fin 17)) :=
  s(2,13) :: es17


private def es15 : List (Sym2 (Fin 17)) :=
  s(2,10) :: es16


private def es14 : List (Sym2 (Fin 17)) :=
  s(2,7) :: es15


private def es13 : List (Sym2 (Fin 17)) :=
  s(2,5) :: es14


private def es12 : List (Sym2 (Fin 17)) :=
  s(1,13) :: es13


private def es11 : List (Sym2 (Fin 17)) :=
  s(1,12) :: es12


private def es10 : List (Sym2 (Fin 17)) :=
  s(1,10) :: es11


private def es9 : List (Sym2 (Fin 17)) :=
  s(1,7) :: es10


private def es8 : List (Sym2 (Fin 17)) :=
  s(1,5) :: es9


private def es7 : List (Sym2 (Fin 17)) :=
  s(1,3) :: es8


private def es6 : List (Sym2 (Fin 17)) :=
  s(1,2) :: es7


private def es5 : List (Sym2 (Fin 17)) :=
  s(0,13) :: es6


private def es4 : List (Sym2 (Fin 17)) :=
  s(0,12) :: es5


private def es3 : List (Sym2 (Fin 17)) :=
  s(0,10) :: es4


private def es2 : List (Sym2 (Fin 17)) :=
  s(0,3) :: es3


private def es1 : List (Sym2 (Fin 17)) :=
  s(0,2) :: es2


private def es0 : List (Sym2 (Fin 17)) :=
  s(0,1) :: es1


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk0 : edgeScan measure 0xa40000000000000000008048000020120000005204020000000a0 es0 0 = true := by decide +kernel


private theorem allCases : edgeScan measure 0xa40000000000000000008048000020120000005204020000000a0 es0 0 = true :=
  chunk0


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private def model : Model mask firstSig :=
  ⟨vertices,13487,by decide +kernel,
    model_bound es0 13487 0xa40000000000000000008048000020120000005204020000000a0 0
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) allCases⟩


end Seed2

private def rows : Array Nat :=
  #[46430,46268,44720,95568,39744,126592,121600,126464,121344,116736,94208,114688,90112,81920,65536,0,0]


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem aligned : ∀ i j : Fin 17, i < j → (board mask).Adj i j →
    (rowAt rows i.val).testBit j.val = true := by decide +kernel


private def book : Array (List Nat) :=
  #[
[],
[0x18f1c10d7288901ca61056d7a970024ec28c887082615959,0xf02b44e531eb4a0c120c0f42da93a8c5811c20b0600a6a7,0x4e0b4ec52de8498851820043dab4a8c761464141c11a6a6],
[0x1ed5320b19ca20812e220cc80ded5b8814810251cc535758],
[],
[0x1cc834eb5250620de50082e241af5a92861c66284023a4a7],
[0x10f3418d72c8901ca31054d7a96c480f02b8881882615559],
[0x10d3416c729e520c49080ed429eb62470038e6290411cbd0,0x900218f3354b0a4e3289cf5812c3a0ad22850184ce0555b],
[0x18f1c10d72c8a01ca61052d7a97049c0c28c887082615359],
[],
[0x1f02216d330ea11469081cf8016961c6d428ae218410cbd4],
[],
[0x1b05302f1b8ab125003988f5a60d3b8a410500519830343f,0x1b051c4e2b06b02501311ef02e093b8a468941430660a4af,0x10f3418d72c8a024e32882d7a96c49cb023848184061515b],
[0xf02adee4b1aa0a0c21808f62d0969d45811c010cc10aab6],
[],
[0x10f32e0d4a9871904e080ac78d686a5503b8053104115b68],
[0x16f4c10d7308a01ca61046d7a96981dcc28c880082614b59],
[],
[],
[],
[0xf02b44e531eb2250130c0f42da93a8a4809c60b0600a4b7,0x1ac540e871062081e532d2d22a0f0b80b6086941cc53cee0],
[],
[0x1eb3b609518a41050e0306c80da17a96472507018a237589],
[0x20d7216c328e428c49081f0039eb6246d428c7290411cbe0,0x1eb43209198a4100ee0b54c80c2d7816e22507518453758a,0x1ed2ae0a49c620818e220cc80de46ad41481c241cc535b70],
[0x2f0358e52d0931ca320a007adac4a8e8298821860e1354b],
[0x18f1c1ab72428018aa208ed7a99058d2701482705061748b],
[0x1ee12ced4b148098851820083d696a14761464138c118ea6,0x1f01216d330ea29069081cf8016961c6d428c5238410cbe4],
[],
[0xed2c16c729e811069080cd429eb62467801c5218411cae4,0x30031af1ace9120ca291cf5818d48ce54104151a0e0748f,0x20f731ab1a4e8118aa200307b98d58d2741482518011748e],
[],
[],
[],
[],
[],
[],
[],
[0xef2b6085196448c4e0818c78da0428cb825c72904117ea0],
[],
[0x8f0358e52d0931ca3106007adac4a8e8298901882e13559,0x1f02216d330ea28c49081cf8016961c6d428ce290410cbf0],
[0x20f7310b1a4ed2a846080907b8ed5952c40cc0510414355b],
[0x1e959e08298831018e0b54c80c24701eb6a5483984537ca2,0xed2c16c729e820c49080cd429eb62467801c6290411caf0],
[0x2f0358e52cc9220e328a007adac4a8e5220461860e1345b,0xf02adee4b54c0a0c21808f62d276a145811c010cc108eb6],
[0x1e963608518830816e11cac80dae229eb0a408388c537ca4],
[0x1f011d6d2b0ca22069081cf8016961c656a146238410caf4,0x1ee11d6d2b10a218690820083d6961c68695462384118bb4],
[0x1901b42f538cb225003944f5a5b03a8a412026701830345f,0x8f0218e32daa0a4e328a007ad0c49cad22850184ce1315b,0x17049dee2b50c228c21802f62d27815c86914610c0108bb6],
[],
[0x17049dee2b48c0290230c2f62d27815c46894808c0608ab7,0x1cd81d6c2a906180890bc4e0c1eb6246869d443004538ab6,0x1eb49e08298831018e0b54c80c24781cb6a54839845376a2,0x1af51e092a1861904e0816c78e080396969d453104117ca8],
[0x1ed2c16c728e2080891a0cd829eb62461401c411cc534b78],
[0x1eb63608518830812e11cac80dae7a88b0a408388c5376a4],
[0x20f71dab2a5880188a188307b98858d276954410406174a3],
[],
[0xef2b60c5196448c4e0810c78dab428c0825c72904116fa0],
[0xef2c1ab724480988a1818d7a98058d27815c4120c1174a6,0x5009daf2ad89020ca20dcf5818848ce5691420c1c6074a7,0x1af51e0b2a1861904e0812c78e085b80969d4531041176a8],
[0x1af51e0b2a5861904e0810c78e085b92069d4531041175a8],
[0x20f734ec5216649065100307b9ab428c961c652080116ea2],
[0x20f71dab2a5881988a104107b98858d276954430820174a9],
[0x20f71dab2a5881988a100307b98858d276954430801174aa,0x20f734ec5216649065080507b9ab428c961c652004116ea4,0x3001daf2ad891a0ca209cf5818848ce5691423060e074ab],
[0x500b4ef5316849885181cf581a9428c761464141c106ea6],
[0x20f71dab2a5881988a080507b98858d276954430041174ac],
[0x5009daf2ad891a0ca201cf5818848ce569142341c1074ae,0x1ec42e0a49883081ae11cac80c8f6ad4e0a408388c536ba4],
[0x1af540ec72448098851816d7aa0b0392761464120c116ca6,0xef2b60c521664904e0806c78dab428c981dc50104116ea8],
[],
[0x20f72cec4a9a809885180507b90b6a54761464100c116aa6],
[],
[0x8f02d0e4b58a19ca6106007ad2869d4c28c903082e11b59,0x1ec59e092a0c41006e0b54c80c2f701696a1472184536caa],
[],
[0x1af540ec72c48098851812d7aa0b4b80761464120c1166a6,0x1ec1b609520c40816e11cac80daf229690a007708c536cac],
[],
[],
[0xef2c1ac72c490a0ca20c0d7a98b48ce5811c20a0c0164a7],
[0x1ec49e0b2a0c41006e0b54c80c2f581c96a14721845366aa],
[],
[0x8f0218e3354b0a4e328a007ad2c3a0ad22850184ce1155b,0x1ec1b60b520c40812e11cac80daf5a8890a007708c5366ac],
[0x20f71dac2ac69020ca208307b98b48ce56914240406164ab],
[],
[0x1704a1ee334ec128a41840f62d27815cd428831182008bd5,0x1ee2216d330ea114690820083d6961c6d428ae2184118bd4],
[0xef2c1ac72c490a0ca2006d7a98b48ce5811c2020c1164ae,0x5009daf2b06b0250a311cf5818938ca468941441c6064af],
[],
[],
[],
[],
[],
[],
[],
[],
[0x18f1b60b525053104e080ec78db05a928018e571041175c8],
[],
[0x1eb3b609520a4104ce0306c80da17a96971107018a2374c9,0x1ed42e0c498830814e11cac80deb6914e0a408388c534fa4],
[0x1eb332091a0a4100ee0b54c80c2d781692390751845374ca],
[],
[0x20f72ced4b14809885180507b9696a14761464100c114ea6],
[0x1ee1216d330ea290690820083d6961c6d428c52384118be4],
[],
[0x2f031ae1ace9120ca292007ad8d48ce54104151a0e1348f],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[0x1ee2216d330ea28c490820083d6961c6d428ce2904118bf0],
[],
[],
[0x20e6bcec5a86809805224506bdcb5242761462400c448bf4],
[],
[0x1b05302f1b8eb125003148f5a60d3b8a440820519830349f,0x1ee11d6d2b0ca220690820083d6961c656a1462384118af4],
[0x1901b42e52de9220e03144f42db04a8e520826701830b41f,0x17049dee2b4cc229021802f62d27815c46a14610c0108af6],
[],
[0x10f32e0d4a9851904e080ec78d686a550038e53104115bc8],
[0x20d72d0a49d8519046081f0039e86ad4c48ce5310411db48],
[],
[],
[],
[0xef2b60c5216448c4e080cc78dab428c9801c72904116ee0],
[0x4f09dae2ad89020ca20e007ad8848ce5691420c1c6134a7],
[0x1af51e0b2a5881904e080cc78e085b9276814531041174e8],
[0x1ed3ae0a494620818e220cc80de46ad417012241cc535bd0,0x16f4a20c328e428c4e081ac78c0b825cd428c72904116be0],
[0x16d4c10a71de520c460818d429e082dcc48ce6290411db50,0x1f022d0d4a98701466105cf801686a54c38cae208260db51],
[0x2f01dae2ad891a0ca20a007ad8848ce5691423060e134ab],
[0x4f0b4ee5316849885182007ada9428c761464141c112ea6],
[],
[0x20f7358b5250731483104107b9ac5a928398a418820434af,0x4f09dae2ad891a0ca202007ad8848ce569142341c1134ae,0x1ec32e0a4a083081ae11cac80c8f6ad490b808388c536ae4],
[],
[],
[0x1f022d0d4a98719446081cf801686a54c38cae310410db58],
[],
[],
[0x9003d0d5a98919ca6105cf68168524ec28c903082e0d959,0x20d73d0a5a58719446080906b9e852d2c38ca0310411d958],
[],
[],
[],
[],
[0x16f4a20d328e428c4e0818c78d60825cd428c72904115be0],
[0x9003d0d4ad8a19ca6105cf6816849d4c28c903082e0d359,0x20d73d0b4a98719446080906b9e85a54c38ca0310411d358,0x1aa6410771062081e62ad2d22a0e0bc0c58c4941cc53db60],
[0x16d4c10c729e7214661040d429eb825cc38ca6208201cb51],
[],
[0x18d1c10b7288901ca6105ed029f05a4ec28c88708261d159],
[0x20d7310b1a927289e609010239ed5a50c38cc1514402d15b,0x20d7216c328e51844903c900b9eb6246d428e0310a22cb55,0x10d3416c729e7214690804d429eb624703b8a6200411cb54],
[0x4f09dae2b06b0250a312007ad8938ca468941441c6124af],
[],
[0x1ed3c16c728a2080891a0cd829eb624617010411cc534bd8],
[0x16d4c10c729e7214460806d429eb825cc38ca6010411cb58,0x1f022d0d4b06a01ca6105cf8016969d4c28c8e408260cb59],
[],
[],
[0x16f4a20d330e428c4e0814c78d69801cd428c72904114fe0],
[],
[],
[],
[],
[0x1ed32e0c4a0830814e11cac80deb691490b808388c534ee4],
[0x1af5418b72427018a32090d7aa0c5b92039482185061750b],
[],
[0x20f7216d330ea29069080507b96961c6d428c52004114be4],
[0x10d3416c729e711069080ad429eb624703b805218411cb64],
[],
[0x18f1c1ab7242801cca2904d7a99058d2729041701061740f],
[0x16f4a20d330ea2904e0806c78d6981dcd428c50104114be8],
[0x1ac1c10a71c82081e62ad2d22a0f0ac0c48c4871cc53cb68],
[],
[],
[],
[],
[],
[],
[0x20f7358b52507218a3104107b9ac5a928394861882017519,0x20f7216d330ea28c49080907b96961c6d428c02904114bf0],
[0x10d3416c729e720c49080ad429eb624703b806290411cb70,0x300358f52d0921cc3289cf581ac4a8e8290461860e0751b],
[],
[0x1af5418b7242801cc32888d7aa0c5b92729040185061741b],
[0x1f02216d330aa11c69081cf8016961c6d2a90e218410cb74],
[0x1901a08e32daa0a4e0289ef02d1049cad2284c704c30b15b],
[0x20f7358b5250731483104107b9ac5a928398a4188202741f],
[],
[],
[],
[],
[],
[],
[],
[0x20c734e85196448c45081f0039af428cb62467290411eea0],
[],
[0x1eb2b60951cc41050e0306c80da17a9644a1c7018a237529],
[0x1eb4320919cc4100ae0b54c80c2d7816e4a087518453752a,0x1f0134ec5216649065081cf801ab428c961c65238410eea4,0x18a6c0e671062081e542d2d229d00bc0262c6941cc53eba0],
[0x1ee22d0d4a987014661060083d686a54c38cae2082619b51],
[0x18f1c1ab7242801cca208ad7a99058d2729002705061742b],
[0x20c73ce95a1a651065080506b90f5196961c65200411eca4],
[0x11032dee4b58a01ca41844f62d2869d502b8831002609b55,0x500bcec5a5a851885181cf6810b5192761464141c10eca6],
[0x16c4c0ea721e611065081ad4280f82dc961c65218411eaa4,0x30031af1aca9120ea311cf5818d48ce52090151a0e0742f,0x20f731ab1a4a811cca200307b98d58d2729102518011742e],
[0x1f012cec4a9a809885181cf8010b6a54761464138c10eaa6],
[],
[0x20e6a18a31cab124237901013dcc3acad4a9011988049b59,0x1ee22d0d4a987194460820083d686a54c38cae3104119b58],
[0x20c734eb521e64906508050439af5a8c961c65200411e6a4],
[0x500b4ec52de849885181cf401ab4a8c761464141c10e6a6],
[0x8e03d0d5a98919ca6106006bd68524ec28c903082e19959],
[0x11033c8e5b58a1a4e02882f6ad2851cb02384c304030995b],
[0x20c734eb5250620de500830239af5a92861c66284022e4a7,0x1ac540eb7244809885181ed02a0f5b92761464120c11e4a6],
[],
[],
[0x1901a08e3354b0a4e0289ef02d303a0ad2284c704c30955b],
[0x8e03d0d4ad8a19ca6106006bd6849d4c28c903082e19359],
[0x11033c8e4b58b1a8e02882f6ad28395502384c304030935b],
[],
[],
[0x1cd8310b1a927289e60900e241ed5a50c38cc1514403915b,0x1cd8216c328e51844903c8e0c1eb6246d428e0310a238b55],
[0x1704a1ee3344c0a8e428c0f62d27815cd228430a0c008b57,0x18f1b60951d053104e0816c78db002968498e57104117d48],
[],
[0x1103308e1b5eb129203942f42d2d394901382c518030915f,0x10f32e0a49d851904e081ac78c086ad504b8e53104117b48],
[0x1ee22d0d4b06a01ca61060083d6969d4c28c8e4082618b59],
[],
[0x1ea5a20931ca4105ae0306c80c8173d6d4a907018a237949],
[0x11032dee4b46c028e42844f62d2769550238434002608b5d,0x18f1b60b51d053104e0812c78db05a808498e57104117748,0x1ac540e671062081e542d2d22a0f0b80262c6941cc53cfa0],
[],
[],
[0x20f7358b5250731483104107b9ac5a928398a41882017549],
[0x300358f52d0931ca3209cf581ac4a8e8298821860e0754b,0x20f7358b5250731483100307b9ac5a928398a4188011754a],
[0x16d4c0ec721e6110650814d429eb801c961c65218411cea4,0x1eb4a20a31ca4105ae0306c80c817adcd4a907018a237349],
[0x1af5418b7242801ca3208cd7aa0c5b92728082185061744b,0x1f012ced4b14809885181cf801696a14761464138c10cea6],
[],
[0xed2c16c729e6110690810d429eb6246081dc5218411cba4],
[0x20f7218b329a909ca3208107b90c5a4ed2a882184c01714b],
[],
[0x16d4c0ec729e8118851802d429eb825c761464118011caa6],
[],
[],
[0x1ea6b20919ca20816e220cc80dcd23d614810251cc537958],
[],
[],
[],
[0x900358f52d0931ca3105cf581ac4a8e8298901882e07559,0x20f7358b5250731443080907b9ac5a928398a01904117558],
[],
[0x20f7358b524c821ca3104107b9ac5a9272a0861882017459,0x1eb6b20a19ca20812e220cc80dcd7ac814810251cc537358,0xed2c16c729e620c490810d429eb6246081dc6290411cbb0,0x1aa6410571062081e63ad2d22a0e0bc0c10d6941cc53dbc0],
[0x300358f52cc9220e3289cf581ac4a8e5220461860e0745b,0x2f0358e52d0921cc328a007adac4a8e8290461860e1351b],
[],
[0x10f3418b7288901ca3105ad7a80c5a4f02b8881882617159,0x1f011d6d2b10a21869081cf8016961c6869546238410cbb4],
[0x1901b42f5390b224e03144f5a5b03a8a820826701830351f,0x900218f32daa0a4e3289cf5810c49cad22850184ce0715b,0x1704a1ee334ac128e41840f62d27815cd229031182008b75,0x1ee2216d330aa11c690820083d6961c6d2a90e2184118b74,0x10f32e0d49d851904e0814c78d68681504b8e53104115f48],
[0xed2c16c729e8118690808d429eb62467815c0218411cab4],
[0x1ee8358b52507314831040e83dac5a928398a4188203341f,0x20d71d6c2a906180890bc500b9eb6246869d44300452cab6],
[0x1ed5a20931ca41054e0306c80de17116d4a907018a235d49],
[],
[0x20f72d0d4a98719486104107b9686a54c38ca43082015b49],
[],
[],
[],
[0x1b051c4e2ad89020c120def02e084b8e5691420b0660b4a7,0x1ed4a20b31ca41054e0306c80de1591cd4a907018a235749],
[0x18f1b60b525073104e080ac78db05a928398057104117568],
[],
[0x1eb2b609520e4104ce0306c80da17a969411c7018a237469],
[0x20f7218d32d4909ca3208107b96c4a0ed2a882184c01554b,0x20f72d0d4a98701466104907b9686a54c38ca02082615b51,0x1eb332091a0e4100ae0b54c80c2d7816943887518453746a,0x1ee134ec52166490650820083dab428c961c65238411aea4,0x18a6c0e871062081e532d2d229d00bc0b6086941cc53eae0],
[0x20e61d682988d1a809089f003cee6146b6a548304444aea6],
[],
[0x10d3416c729e511069080ed429eb62470038e5218411cbc4],
[0xf02bc4e5b1a9520c120c0f6ad09518e5811c20b0600aca7,0x4e0bcec5a5a851885182006bd0b5192761464141c11aca6],
[0x2f031ae1aca9120ea312007ad8d48ce52090151a0e1342f,0x1ed5320919ca20816e220cc80ded239614810251cc535d58],
[0x1ee12cec4a9a8098851820083d0b6a54761464138c11aaa6],
[0x20f72d0d4a98719446080907b9686a54c38ca03104115b58,0x9002d0f4b58a19ca6105cf5812869d4c28c903082e05b59,0x1ac1c10a71482081e63ad2d22a0f0ac0c10d2871cc53cbc8],
[]]


private def models : Array (Model mask firstSig) :=
  #[Seed0.model,Seed1.model,Seed2.model]


private def checkVertices : Nat → Bool :=
  passes models book rows


private def vs17 : List (Fin 17) :=
  []


private def vs16 : List (Fin 17) :=
  16 :: vs17


private def vs15 : List (Fin 17) :=
  15 :: vs16


private def vs14 : List (Fin 17) :=
  14 :: vs15


private def vs13 : List (Fin 17) :=
  13 :: vs14


private def vs12 : List (Fin 17) :=
  12 :: vs13


private def vs11 : List (Fin 17) :=
  11 :: vs12


private def vs10 : List (Fin 17) :=
  10 :: vs11


private def vs9 : List (Fin 17) :=
  9 :: vs10


private def vs8 : List (Fin 17) :=
  8 :: vs9


private def vs7 : List (Fin 17) :=
  7 :: vs8


private def vs6 : List (Fin 17) :=
  6 :: vs7


private def vs5 : List (Fin 17) :=
  5 :: vs6


private def vs4 : List (Fin 17) :=
  4 :: vs5


private def vs3 : List (Fin 17) :=
  3 :: vs4


private def vs2 : List (Fin 17) :=
  2 :: vs3


private def vs1 : List (Fin 17) :=
  1 :: vs2


private def vs0 : List (Fin 17) :=
  0 :: vs1


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk0 : scan checkVertices 127 vs7 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk1 : scan checkVertices 191 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk2 : scan checkVertices 63 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk3 : scan checkVertices 223 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk4 : scan checkVertices 95 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk5 : scan checkVertices 159 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk6 : scan checkVertices 287 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk7 : scan checkVertices 31 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk8 : scan checkVertices 239 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk9 : scan checkVertices 111 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk10 : scan checkVertices 175 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk11 : scan checkVertices 303 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk12 : scan checkVertices 47 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk13 : scan checkVertices 207 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk14 : scan checkVertices 335 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk15 : scan checkVertices 79 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk16 : scan checkVertices 399 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk17 : scan checkVertices 143 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk18 : scan checkVertices 271 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk19 : scan checkVertices 15 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk20 : scan checkVertices 247 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk21 : scan checkVertices 119 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk22 : scan checkVertices 183 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk23 : scan checkVertices 311 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk24 : scan checkVertices 55 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk25 : scan checkVertices 215 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk26 : scan checkVertices 343 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk27 : scan checkVertices 87 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk28 : scan checkVertices 407 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk29 : scan checkVertices 151 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk30 : scan checkVertices 279 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk31 : scan checkVertices 23 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk32 : scan checkVertices 231 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk33 : scan checkVertices 359 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk34 : scan checkVertices 103 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk35 : scan checkVertices 423 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk36 : scan checkVertices 167 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk37 : scan checkVertices 295 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk38 : scan checkVertices 39 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk39 : scan checkVertices 455 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk40 : scan checkVertices 199 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk41 : scan checkVertices 327 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk42 : scan checkVertices 71 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk43 : scan checkVertices 391 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk44 : scan checkVertices 135 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk45 : scan checkVertices 7 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk46 : scan checkVertices 251 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk47 : scan checkVertices 123 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk48 : scan checkVertices 187 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk49 : scan checkVertices 315 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk50 : scan checkVertices 59 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk51 : scan checkVertices 219 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk52 : scan checkVertices 347 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk53 : scan checkVertices 91 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk54 : scan checkVertices 411 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk55 : scan checkVertices 155 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk56 : scan checkVertices 283 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk57 : scan checkVertices 27 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk58 : scan checkVertices 235 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk59 : scan checkVertices 363 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk60 : scan checkVertices 107 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk61 : scan checkVertices 427 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk62 : scan checkVertices 171 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk63 : scan checkVertices 299 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk64 : scan checkVertices 43 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk65 : scan checkVertices 459 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk66 : scan checkVertices 203 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk67 : scan checkVertices 331 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk68 : scan checkVertices 75 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk69 : scan checkVertices 395 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk70 : scan checkVertices 139 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk71 : scan checkVertices 11 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk72 : scan checkVertices 243 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk73 : scan checkVertices 371 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk74 : scan checkVertices 115 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk75 : scan checkVertices 435 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk76 : scan checkVertices 179 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk77 : scan checkVertices 307 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk78 : scan checkVertices 51 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk79 : scan checkVertices 467 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk80 : scan checkVertices 211 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk81 : scan checkVertices 339 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk82 : scan checkVertices 83 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk83 : scan checkVertices 403 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk84 : scan checkVertices 147 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk85 : scan checkVertices 19 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk86 : scan checkVertices 483 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk87 : scan checkVertices 227 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk88 : scan checkVertices 355 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk89 : scan checkVertices 99 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk90 : scan checkVertices 419 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk91 : scan checkVertices 163 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk92 : scan checkVertices 35 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk93 : scan checkVertices 451 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk94 : scan checkVertices 195 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk95 : scan checkVertices 67 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk96 : scan checkVertices 131 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk97 : scan checkVertices 3 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk98 : scan checkVertices 253 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk99 : scan checkVertices 125 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk100 : scan checkVertices 189 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk101 : scan checkVertices 317 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk102 : scan checkVertices 61 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk103 : scan checkVertices 221 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk104 : scan checkVertices 349 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk105 : scan checkVertices 93 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk106 : scan checkVertices 413 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk107 : scan checkVertices 157 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk108 : scan checkVertices 285 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk109 : scan checkVertices 29 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk110 : scan checkVertices 237 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk111 : scan checkVertices 365 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk112 : scan checkVertices 109 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk113 : scan checkVertices 429 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk114 : scan checkVertices 173 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk115 : scan checkVertices 301 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk116 : scan checkVertices 45 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk117 : scan checkVertices 461 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk118 : scan checkVertices 205 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk119 : scan checkVertices 333 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk120 : scan checkVertices 77 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk121 : scan checkVertices 397 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk122 : scan checkVertices 141 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk123 : scan checkVertices 13 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk124 : scan checkVertices 245 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk125 : scan checkVertices 373 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk126 : scan checkVertices 117 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk127 : scan checkVertices 437 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk128 : scan checkVertices 181 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk129 : scan checkVertices 309 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk130 : scan checkVertices 53 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk131 : scan checkVertices 469 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk132 : scan checkVertices 213 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk133 : scan checkVertices 341 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk134 : scan checkVertices 85 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk135 : scan checkVertices 405 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk136 : scan checkVertices 149 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk137 : scan checkVertices 21 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk138 : scan checkVertices 485 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk139 : scan checkVertices 229 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk140 : scan checkVertices 357 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk141 : scan checkVertices 101 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk142 : scan checkVertices 421 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk143 : scan checkVertices 165 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk144 : scan checkVertices 37 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk145 : scan checkVertices 453 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk146 : scan checkVertices 197 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk147 : scan checkVertices 69 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk148 : scan checkVertices 133 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk149 : scan checkVertices 5 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk150 : scan checkVertices 249 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk151 : scan checkVertices 377 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk152 : scan checkVertices 121 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk153 : scan checkVertices 441 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk154 : scan checkVertices 185 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk155 : scan checkVertices 313 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk156 : scan checkVertices 57 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk157 : scan checkVertices 473 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk158 : scan checkVertices 217 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk159 : scan checkVertices 345 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk160 : scan checkVertices 89 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk161 : scan checkVertices 409 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk162 : scan checkVertices 153 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk163 : scan checkVertices 25 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk164 : scan checkVertices 489 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk165 : scan checkVertices 233 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk166 : scan checkVertices 361 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk167 : scan checkVertices 105 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk168 : scan checkVertices 425 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk169 : scan checkVertices 169 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk170 : scan checkVertices 41 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk171 : scan checkVertices 457 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk172 : scan checkVertices 201 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk173 : scan checkVertices 73 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk174 : scan checkVertices 137 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk175 : scan checkVertices 9 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk176 : scan checkVertices 497 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk177 : scan checkVertices 241 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk178 : scan checkVertices 369 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk179 : scan checkVertices 113 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk180 : scan checkVertices 433 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk181 : scan checkVertices 177 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk182 : scan checkVertices 49 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk183 : scan checkVertices 465 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk184 : scan checkVertices 209 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk185 : scan checkVertices 81 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk186 : scan checkVertices 145 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk187 : scan checkVertices 17 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk188 : scan checkVertices 481 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk189 : scan checkVertices 225 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk190 : scan checkVertices 97 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk191 : scan checkVertices 161 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk192 : scan checkVertices 33 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk193 : scan checkVertices 193 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk194 : scan checkVertices 65 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk195 : scan checkVertices 1 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk196 : scan checkVertices 254 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk197 : scan checkVertices 126 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk198 : scan checkVertices 190 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk199 : scan checkVertices 318 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk200 : scan checkVertices 62 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk201 : scan checkVertices 222 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk202 : scan checkVertices 350 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk203 : scan checkVertices 94 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk204 : scan checkVertices 414 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk205 : scan checkVertices 158 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk206 : scan checkVertices 286 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk207 : scan checkVertices 30 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk208 : scan checkVertices 238 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk209 : scan checkVertices 366 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk210 : scan checkVertices 110 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk211 : scan checkVertices 430 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk212 : scan checkVertices 174 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk213 : scan checkVertices 302 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk214 : scan checkVertices 46 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk215 : scan checkVertices 462 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk216 : scan checkVertices 206 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk217 : scan checkVertices 334 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk218 : scan checkVertices 78 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk219 : scan checkVertices 398 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk220 : scan checkVertices 142 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk221 : scan checkVertices 14 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk222 : scan checkVertices 246 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk223 : scan checkVertices 374 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk224 : scan checkVertices 118 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk225 : scan checkVertices 438 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk226 : scan checkVertices 182 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk227 : scan checkVertices 310 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk228 : scan checkVertices 54 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk229 : scan checkVertices 470 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk230 : scan checkVertices 214 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk231 : scan checkVertices 342 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk232 : scan checkVertices 86 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk233 : scan checkVertices 406 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk234 : scan checkVertices 150 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk235 : scan checkVertices 22 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk236 : scan checkVertices 486 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk237 : scan checkVertices 230 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk238 : scan checkVertices 358 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk239 : scan checkVertices 102 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk240 : scan checkVertices 422 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk241 : scan checkVertices 166 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk242 : scan checkVertices 38 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk243 : scan checkVertices 454 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk244 : scan checkVertices 198 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk245 : scan checkVertices 70 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk246 : scan checkVertices 134 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk247 : scan checkVertices 6 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk248 : scan checkVertices 250 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk249 : scan checkVertices 378 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk250 : scan checkVertices 122 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk251 : scan checkVertices 442 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk252 : scan checkVertices 186 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk253 : scan checkVertices 314 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk254 : scan checkVertices 58 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk255 : scan checkVertices 474 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk256 : scan checkVertices 218 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk257 : scan checkVertices 346 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk258 : scan checkVertices 90 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk259 : scan checkVertices 410 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk260 : scan checkVertices 154 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk261 : scan checkVertices 26 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk262 : scan checkVertices 490 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk263 : scan checkVertices 234 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk264 : scan checkVertices 362 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk265 : scan checkVertices 106 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk266 : scan checkVertices 426 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk267 : scan checkVertices 170 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk268 : scan checkVertices 42 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk269 : scan checkVertices 458 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk270 : scan checkVertices 202 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk271 : scan checkVertices 74 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk272 : scan checkVertices 138 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk273 : scan checkVertices 10 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk274 : scan checkVertices 498 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk275 : scan checkVertices 242 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk276 : scan checkVertices 370 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk277 : scan checkVertices 114 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk278 : scan checkVertices 434 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk279 : scan checkVertices 178 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk280 : scan checkVertices 50 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk281 : scan checkVertices 466 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk282 : scan checkVertices 210 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk283 : scan checkVertices 82 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk284 : scan checkVertices 146 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk285 : scan checkVertices 18 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk286 : scan checkVertices 482 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk287 : scan checkVertices 226 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk288 : scan checkVertices 98 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk289 : scan checkVertices 162 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk290 : scan checkVertices 34 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk291 : scan checkVertices 194 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk292 : scan checkVertices 66 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk293 : scan checkVertices 2 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk294 : scan checkVertices 252 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk295 : scan checkVertices 380 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk296 : scan checkVertices 124 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk297 : scan checkVertices 444 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk298 : scan checkVertices 188 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk299 : scan checkVertices 316 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk300 : scan checkVertices 60 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk301 : scan checkVertices 476 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk302 : scan checkVertices 220 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk303 : scan checkVertices 348 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk304 : scan checkVertices 92 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk305 : scan checkVertices 412 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk306 : scan checkVertices 156 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk307 : scan checkVertices 28 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk308 : scan checkVertices 492 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk309 : scan checkVertices 236 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk310 : scan checkVertices 364 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk311 : scan checkVertices 108 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk312 : scan checkVertices 428 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk313 : scan checkVertices 172 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk314 : scan checkVertices 44 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk315 : scan checkVertices 460 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk316 : scan checkVertices 204 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk317 : scan checkVertices 76 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk318 : scan checkVertices 140 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk319 : scan checkVertices 12 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk320 : scan checkVertices 500 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk321 : scan checkVertices 244 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk322 : scan checkVertices 372 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk323 : scan checkVertices 116 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk324 : scan checkVertices 436 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk325 : scan checkVertices 180 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk326 : scan checkVertices 52 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk327 : scan checkVertices 468 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk328 : scan checkVertices 212 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk329 : scan checkVertices 84 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk330 : scan checkVertices 148 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk331 : scan checkVertices 20 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk332 : scan checkVertices 484 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk333 : scan checkVertices 228 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk334 : scan checkVertices 100 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk335 : scan checkVertices 164 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk336 : scan checkVertices 36 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk337 : scan checkVertices 196 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk338 : scan checkVertices 68 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk339 : scan checkVertices 4 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk340 : scan checkVertices 504 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk341 : scan checkVertices 248 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk342 : scan checkVertices 376 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk343 : scan checkVertices 120 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk344 : scan checkVertices 440 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk345 : scan checkVertices 184 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk346 : scan checkVertices 56 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk347 : scan checkVertices 472 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk348 : scan checkVertices 216 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk349 : scan checkVertices 88 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk350 : scan checkVertices 152 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk351 : scan checkVertices 24 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk352 : scan checkVertices 488 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk353 : scan checkVertices 232 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk354 : scan checkVertices 104 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk355 : scan checkVertices 168 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk356 : scan checkVertices 40 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk357 : scan checkVertices 200 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk358 : scan checkVertices 72 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk359 : scan checkVertices 8 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk360 : scan checkVertices 496 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk361 : scan checkVertices 240 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk362 : scan checkVertices 112 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk363 : scan checkVertices 176 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk364 : scan checkVertices 48 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk365 : scan checkVertices 208 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk366 : scan checkVertices 80 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk367 : scan checkVertices 16 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk368 : scan checkVertices 224 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk369 : scan checkVertices 96 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk370 : scan checkVertices 32 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk371 : scan checkVertices 0 vs6 9 = true := by decide +kernel


private theorem allCases : scan checkVertices 0 vs0 9 = true :=
  (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk0 (scan_node chunk1 chunk2)) (scan_node (scan_node chunk3 chunk4) (scan_node chunk5 (scan_node chunk6 chunk7)))) (scan_node (scan_node (scan_node chunk8 chunk9) (scan_node chunk10 (scan_node chunk11 chunk12))) (scan_node (scan_node chunk13 (scan_node chunk14 chunk15)) (scan_node (scan_node chunk16 chunk17) (scan_node chunk18 chunk19))))) (scan_node (scan_node (scan_node (scan_node chunk20 chunk21) (scan_node chunk22 (scan_node chunk23 chunk24))) (scan_node (scan_node chunk25 (scan_node chunk26 chunk27)) (scan_node (scan_node chunk28 chunk29) (scan_node chunk30 chunk31)))) (scan_node (scan_node (scan_node chunk32 (scan_node chunk33 chunk34)) (scan_node (scan_node chunk35 chunk36) (scan_node chunk37 chunk38))) (scan_node (scan_node (scan_node chunk39 chunk40) (scan_node chunk41 chunk42)) (scan_node (scan_node chunk43 chunk44) chunk45))))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk46 chunk47) (scan_node chunk48 (scan_node chunk49 chunk50))) (scan_node (scan_node chunk51 (scan_node chunk52 chunk53)) (scan_node (scan_node chunk54 chunk55) (scan_node chunk56 chunk57)))) (scan_node (scan_node (scan_node chunk58 (scan_node chunk59 chunk60)) (scan_node (scan_node chunk61 chunk62) (scan_node chunk63 chunk64))) (scan_node (scan_node (scan_node chunk65 chunk66) (scan_node chunk67 chunk68)) (scan_node (scan_node chunk69 chunk70) chunk71)))) (scan_node (scan_node (scan_node (scan_node chunk72 (scan_node chunk73 chunk74)) (scan_node (scan_node chunk75 chunk76) (scan_node chunk77 chunk78))) (scan_node (scan_node (scan_node chunk79 chunk80) (scan_node chunk81 chunk82)) (scan_node (scan_node chunk83 chunk84) chunk85))) (scan_node (scan_node (scan_node (scan_node chunk86 chunk87) (scan_node chunk88 chunk89)) (scan_node (scan_node chunk90 chunk91) chunk92)) (scan_node (scan_node (scan_node chunk93 chunk94) chunk95) (scan_node chunk96 chunk97)))))) (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk98 chunk99) (scan_node chunk100 (scan_node chunk101 chunk102))) (scan_node (scan_node chunk103 (scan_node chunk104 chunk105)) (scan_node (scan_node chunk106 chunk107) (scan_node chunk108 chunk109)))) (scan_node (scan_node (scan_node chunk110 (scan_node chunk111 chunk112)) (scan_node (scan_node chunk113 chunk114) (scan_node chunk115 chunk116))) (scan_node (scan_node (scan_node chunk117 chunk118) (scan_node chunk119 chunk120)) (scan_node (scan_node chunk121 chunk122) chunk123)))) (scan_node (scan_node (scan_node (scan_node chunk124 (scan_node chunk125 chunk126)) (scan_node (scan_node chunk127 chunk128) (scan_node chunk129 chunk130))) (scan_node (scan_node (scan_node chunk131 chunk132) (scan_node chunk133 chunk134)) (scan_node (scan_node chunk135 chunk136) chunk137))) (scan_node (scan_node (scan_node (scan_node chunk138 chunk139) (scan_node chunk140 chunk141)) (scan_node (scan_node chunk142 chunk143) chunk144)) (scan_node (scan_node (scan_node chunk145 chunk146) chunk147) (scan_node chunk148 chunk149))))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk150 (scan_node chunk151 chunk152)) (scan_node (scan_node chunk153 chunk154) (scan_node chunk155 chunk156))) (scan_node (scan_node (scan_node chunk157 chunk158) (scan_node chunk159 chunk160)) (scan_node (scan_node chunk161 chunk162) chunk163))) (scan_node (scan_node (scan_node (scan_node chunk164 chunk165) (scan_node chunk166 chunk167)) (scan_node (scan_node chunk168 chunk169) chunk170)) (scan_node (scan_node (scan_node chunk171 chunk172) chunk173) (scan_node chunk174 chunk175)))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk176 chunk177) (scan_node chunk178 chunk179)) (scan_node (scan_node chunk180 chunk181) chunk182)) (scan_node (scan_node (scan_node chunk183 chunk184) chunk185) (scan_node chunk186 chunk187))) (scan_node (scan_node (scan_node (scan_node chunk188 chunk189) chunk190) (scan_node chunk191 chunk192)) (scan_node (scan_node chunk193 chunk194) chunk195)))))) (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk196 chunk197) (scan_node chunk198 (scan_node chunk199 chunk200))) (scan_node (scan_node chunk201 (scan_node chunk202 chunk203)) (scan_node (scan_node chunk204 chunk205) (scan_node chunk206 chunk207)))) (scan_node (scan_node (scan_node chunk208 (scan_node chunk209 chunk210)) (scan_node (scan_node chunk211 chunk212) (scan_node chunk213 chunk214))) (scan_node (scan_node (scan_node chunk215 chunk216) (scan_node chunk217 chunk218)) (scan_node (scan_node chunk219 chunk220) chunk221)))) (scan_node (scan_node (scan_node (scan_node chunk222 (scan_node chunk223 chunk224)) (scan_node (scan_node chunk225 chunk226) (scan_node chunk227 chunk228))) (scan_node (scan_node (scan_node chunk229 chunk230) (scan_node chunk231 chunk232)) (scan_node (scan_node chunk233 chunk234) chunk235))) (scan_node (scan_node (scan_node (scan_node chunk236 chunk237) (scan_node chunk238 chunk239)) (scan_node (scan_node chunk240 chunk241) chunk242)) (scan_node (scan_node (scan_node chunk243 chunk244) chunk245) (scan_node chunk246 chunk247))))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk248 (scan_node chunk249 chunk250)) (scan_node (scan_node chunk251 chunk252) (scan_node chunk253 chunk254))) (scan_node (scan_node (scan_node chunk255 chunk256) (scan_node chunk257 chunk258)) (scan_node (scan_node chunk259 chunk260) chunk261))) (scan_node (scan_node (scan_node (scan_node chunk262 chunk263) (scan_node chunk264 chunk265)) (scan_node (scan_node chunk266 chunk267) chunk268)) (scan_node (scan_node (scan_node chunk269 chunk270) chunk271) (scan_node chunk272 chunk273)))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk274 chunk275) (scan_node chunk276 chunk277)) (scan_node (scan_node chunk278 chunk279) chunk280)) (scan_node (scan_node (scan_node chunk281 chunk282) chunk283) (scan_node chunk284 chunk285))) (scan_node (scan_node (scan_node (scan_node chunk286 chunk287) chunk288) (scan_node chunk289 chunk290)) (scan_node (scan_node chunk291 chunk292) chunk293))))) (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk294 (scan_node chunk295 chunk296)) (scan_node (scan_node chunk297 chunk298) (scan_node chunk299 chunk300))) (scan_node (scan_node (scan_node chunk301 chunk302) (scan_node chunk303 chunk304)) (scan_node (scan_node chunk305 chunk306) chunk307))) (scan_node (scan_node (scan_node (scan_node chunk308 chunk309) (scan_node chunk310 chunk311)) (scan_node (scan_node chunk312 chunk313) chunk314)) (scan_node (scan_node (scan_node chunk315 chunk316) chunk317) (scan_node chunk318 chunk319)))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk320 chunk321) (scan_node chunk322 chunk323)) (scan_node (scan_node chunk324 chunk325) chunk326)) (scan_node (scan_node (scan_node chunk327 chunk328) chunk329) (scan_node chunk330 chunk331))) (scan_node (scan_node (scan_node (scan_node chunk332 chunk333) chunk334) (scan_node chunk335 chunk336)) (scan_node (scan_node chunk337 chunk338) chunk339)))) (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk340 chunk341) (scan_node chunk342 chunk343)) (scan_node (scan_node chunk344 chunk345) chunk346)) (scan_node (scan_node (scan_node chunk347 chunk348) chunk349) (scan_node chunk350 chunk351))) (scan_node (scan_node (scan_node (scan_node chunk352 chunk353) chunk354) (scan_node chunk355 chunk356)) (scan_node (scan_node chunk357 chunk358) chunk359))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk360 chunk361) chunk362) (scan_node chunk363 chunk364)) (scan_node (scan_node chunk365 chunk366) chunk367)) (scan_node (scan_node (scan_node chunk368 chunk369) chunk370) chunk371))))))


private theorem on_set (S : Finset (Fin 17)) (hs : S.card = 9) :
    BoundOn mask firstSig S := by
  apply route_sound models book rows aligned S
  have cover : vs0.toFinset = univ := by decide +kernel
  have sub : S ⊆ vs0.toFinset := by simp [cover]
  have h := scan_sound (f := checkVertices) 0 vs0 S sub (hs.symm ▸ allCases)
  simpa [checkVertices] using h


end First

namespace Second

private def mask : Nat :=
  3794304128205901233965105136443933563551981921148588106415553686027566907782081184


namespace Seed0

private def vertices : Finset (Fin 17) :=
  {0,2,4,6,8,9,12,14,16}


private def measure : Nat → Bool :=
  fun z => (fun v => !shared v) (measures vertices 86869 z)


private def es31 : List (Sym2 (Fin 17)) :=
  []


private def es30 : List (Sym2 (Fin 17)) :=
  s(12,16) :: es31


private def es29 : List (Sym2 (Fin 17)) :=
  s(12,14) :: es30


private def es28 : List (Sym2 (Fin 17)) :=
  s(9,16) :: es29


private def es27 : List (Sym2 (Fin 17)) :=
  s(9,14) :: es28


private def es26 : List (Sym2 (Fin 17)) :=
  s(9,12) :: es27


private def es25 : List (Sym2 (Fin 17)) :=
  s(8,16) :: es26


private def es24 : List (Sym2 (Fin 17)) :=
  s(8,14) :: es25


private def es23 : List (Sym2 (Fin 17)) :=
  s(8,12) :: es24


private def es22 : List (Sym2 (Fin 17)) :=
  s(8,9) :: es23


private def es21 : List (Sym2 (Fin 17)) :=
  s(6,14) :: es22


private def es20 : List (Sym2 (Fin 17)) :=
  s(6,12) :: es21


private def es19 : List (Sym2 (Fin 17)) :=
  s(6,9) :: es20


private def es18 : List (Sym2 (Fin 17)) :=
  s(6,8) :: es19


private def es17 : List (Sym2 (Fin 17)) :=
  s(4,16) :: es18


private def es16 : List (Sym2 (Fin 17)) :=
  s(4,14) :: es17


private def es15 : List (Sym2 (Fin 17)) :=
  s(4,9) :: es16


private def es14 : List (Sym2 (Fin 17)) :=
  s(4,8) :: es15


private def es13 : List (Sym2 (Fin 17)) :=
  s(4,6) :: es14


private def es12 : List (Sym2 (Fin 17)) :=
  s(2,16) :: es13


private def es11 : List (Sym2 (Fin 17)) :=
  s(2,14) :: es12


private def es10 : List (Sym2 (Fin 17)) :=
  s(2,12) :: es11


private def es9 : List (Sym2 (Fin 17)) :=
  s(2,9) :: es10


private def es8 : List (Sym2 (Fin 17)) :=
  s(2,8) :: es9


private def es7 : List (Sym2 (Fin 17)) :=
  s(2,4) :: es8


private def es6 : List (Sym2 (Fin 17)) :=
  s(0,16) :: es7


private def es5 : List (Sym2 (Fin 17)) :=
  s(0,14) :: es6


private def es4 : List (Sym2 (Fin 17)) :=
  s(0,12) :: es5


private def es3 : List (Sym2 (Fin 17)) :=
  s(0,8) :: es4


private def es2 : List (Sym2 (Fin 17)) :=
  s(0,6) :: es3


private def es1 : List (Sym2 (Fin 17)) :=
  s(0,4) :: es2


private def es0 : List (Sym2 (Fin 17)) :=
  s(0,2) :: es1


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk0 : edgeScan measure 0x404000004000000000010000000000000200000000400140000100100000010400000254 es3 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk1 : edgeScan measure 0x404000004000000000010000000000000200010000400100000100100000010400000314 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk2 : edgeScan measure 0x404000004000000000011000000000000200000000400100000100100000010400001214 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk3 : edgeScan measure 0x404000004000400000010000000000000200000000400100000100100000010400004214 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk4 : edgeScan measure 0x404100004000000000010000000000000200000000400100000100100000010400010214 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk5 : edgeScan measure 0x404000004000000000010000000000000200000000400100000100100000010400000214 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk6 : edgeScan measure 0x404000004000000000010000000000000200010000400140000100000000010400000344 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk7 : edgeScan measure 0x404000004000000000011000000000000200000000400140000100000000010400001244 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk8 : edgeScan measure 0x404000004000400000010000000000000200000000400140000100000000010400004244 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk9 : edgeScan measure 0x404100004000000000010000000000000200000000400140000100000000010400010244 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk10 : edgeScan measure 0x404000004000000000010000000000000200000000400140000100000000010400000244 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk11 : edgeScan measure 0x404000004000000000011000000000000200010000400100000100000000010400001304 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk12 : edgeScan measure 0x404000004000400000010000000000000200010000400100000100000000010400004304 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk13 : edgeScan measure 0x404100004000000000010000000000000200010000400100000100000000010400010304 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk14 : edgeScan measure 0x404000004000000000010000000000000200010000400100000100000000010400000304 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk15 : edgeScan measure 0x404000004000400000011000000000000200000000400100000100000000010400005204 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk16 : edgeScan measure 0x404100004000000000011000000000000200000000400100000100000000010400011204 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk17 : edgeScan measure 0x404000004000000000011000000000000200000000400100000100000000010400001204 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk18 : edgeScan measure 0x404100004000400000010000000000000200000000400100000100000000010400014204 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk19 : edgeScan measure 0x404000004000400000010000000000000200000000400100000100000000010400004204 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk20 : edgeScan measure 0x404100004000000000010000000000000200000000400100000100000000010400010204 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk21 : edgeScan measure 0x404000004000000000010000000000000200000000400100000100400000014400000204 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk22 : edgeScan measure 0x404000004000000000010000000000000200040000400100000100000000050400000204 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk23 : edgeScan measure 0x404000004000000000010000000000000a00000000400100000100000000090400000204 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk24 : edgeScan measure 0x404000004000000000014000000000000200000000400100000100000000410400000204 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk25 : edgeScan measure 0x404000004001000000010000000000000200000000400100000100000001010400000204 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk26 : edgeScan measure 0x404400004000000000010000000000000200000000400100000100000004010400000204 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk27 : edgeScan measure 0x404000004000000000010000000000000200000000400500000104000000010400000204 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk28 : edgeScan measure 0x404000004000000000010000000000000200100000400100000110000000010400000204 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk29 : edgeScan measure 0x404000004000000000010000000000002200000000400100000120000000010400000204 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk30 : edgeScan measure 0x404000004004000000010000000000000200000000400100000500000000010400000204 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk31 : edgeScan measure 0x405000004000000000010000000000000200000000400100001100000000010400000204 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk32 : edgeScan measure 0x404000004000000000010000000000000200400000404100000100000000010400000204 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk33 : edgeScan measure 0x404000004000000000010000000000008200000000408100000100000000010400000204 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk34 : edgeScan measure 0x404000004000000000050000000000000200000000440100000100000000010400000204 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk35 : edgeScan measure 0x404000004010000000010000000000000200000000500100000100000000010400000204 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk36 : edgeScan measure 0x404000004000000000010000000000020202000000400100000100000000010400000204 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk37 : edgeScan measure 0x404000004000000000110000000000000210000000400100000100000000010400000204 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk38 : edgeScan measure 0x404000004000000000010000000000000200000000400100000100000000010400000204 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk39 : edgeScan measure 0x404000004000000000010000000000000200010000400140000100100000010000000350 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk40 : edgeScan measure 0x404000004000000000011000000000000200000000400140000100100000010000001250 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk41 : edgeScan measure 0x404000004000400000010000000000000200000000400140000100100000010000004250 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk42 : edgeScan measure 0x404100004000000000010000000000000200000000400140000100100000010000010250 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk43 : edgeScan measure 0x404000004000000000010000000000000200000000400140000100100000010000000250 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk44 : edgeScan measure 0x404000004000000000011000000000000200010000400100000100100000010000001310 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk45 : edgeScan measure 0x404000004000400000010000000000000200010000400100000100100000010000004310 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk46 : edgeScan measure 0x404100004000000000010000000000000200010000400100000100100000010000010310 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk47 : edgeScan measure 0x404000004000000000010000000000000200010000400100000100100000010000000310 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk48 : edgeScan measure 0x404000004000400000011000000000000200000000400100000100100000010000005210 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk49 : edgeScan measure 0x404100004000000000011000000000000200000000400100000100100000010000011210 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk50 : edgeScan measure 0x404000004000000000011000000000000200000000400100000100100000010000001210 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk51 : edgeScan measure 0x404100004000400000010000000000000200000000400100000100100000010000014210 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk52 : edgeScan measure 0x404000004000400000010000000000000200000000400100000100100000010000004210 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk53 : edgeScan measure 0x404100004000000000010000000000000200000000400100000100100000010000010210 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk54 : edgeScan measure 0x404000004000000000010000000000000200000000400100000100500000014000000210 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk55 : edgeScan measure 0x404000004000000000010000000000000200040000400100000100100000050000000210 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk56 : edgeScan measure 0x404000004000000000010000000000000a00000000400100000100100000090000000210 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk57 : edgeScan measure 0x404000004000000000014000000000000200000000400100000100100000410000000210 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk58 : edgeScan measure 0x404000004001000000010000000000000200000000400100000100100001010000000210 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk59 : edgeScan measure 0x404400004000000000010000000000000200000000400100000100100004010000000210 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk60 : edgeScan measure 0x404000004000000000010000000000000200000000400500000104100000010000000210 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk61 : edgeScan measure 0x404000004000000000010000000000000200100000400100000110100000010000000210 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk62 : edgeScan measure 0x404000004000000000010000000000002200000000400100000120100000010000000210 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk63 : edgeScan measure 0x404000004004000000010000000000000200000000400100000500100000010000000210 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk64 : edgeScan measure 0x405000004000000000010000000000000200000000400100001100100000010000000210 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk65 : edgeScan measure 0x404000004000000000010000000000000200400000404100000100100000010000000210 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk66 : edgeScan measure 0x404000004000000000010000000000008200000000408100000100100000010000000210 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk67 : edgeScan measure 0x404000004000000000050000000000000200000000440100000100100000010000000210 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk68 : edgeScan measure 0x404000004010000000010000000000000200000000500100000100100000010000000210 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk69 : edgeScan measure 0x404000004000000000010000000000020202000000400100000100100000010000000210 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk70 : edgeScan measure 0x404000004000000000110000000000000210000000400100000100100000010000000210 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk71 : edgeScan measure 0x404000004000000000010000000000000200000000400100000100100000010000000210 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk72 : edgeScan measure 0x404000004000000000011000000000000200010000400140000100000000010000001340 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk73 : edgeScan measure 0x404000004000400000010000000000000200010000400140000100000000010000004340 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk74 : edgeScan measure 0x404100004000000000010000000000000200010000400140000100000000010000010340 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk75 : edgeScan measure 0x404000004000000000010000000000000200010000400140000100000000010000000340 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk76 : edgeScan measure 0x404000004000400000011000000000000200000000400140000100000000010000005240 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk77 : edgeScan measure 0x404100004000000000011000000000000200000000400140000100000000010000011240 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk78 : edgeScan measure 0x404000004000000000011000000000000200000000400140000100000000010000001240 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk79 : edgeScan measure 0x404100004000400000010000000000000200000000400140000100000000010000014240 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk80 : edgeScan measure 0x404000004000400000010000000000000200000000400140000100000000010000004240 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk81 : edgeScan measure 0x404100004000000000010000000000000200000000400140000100000000010000010240 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk82 : edgeScan measure 0x404000004000000000010000000000000200000000400140000100400000014000000240 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk83 : edgeScan measure 0x404000004000000000010000000000000200040000400140000100000000050000000240 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk84 : edgeScan measure 0x404000004000000000010000000000000a00000000400140000100000000090000000240 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk85 : edgeScan measure 0x404000004000000000014000000000000200000000400140000100000000410000000240 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk86 : edgeScan measure 0x404000004001000000010000000000000200000000400140000100000001010000000240 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk87 : edgeScan measure 0x404400004000000000010000000000000200000000400140000100000004010000000240 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk88 : edgeScan measure 0x404000004000000000010000000000000200000000400540000104000000010000000240 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk89 : edgeScan measure 0x404000004000000000010000000000000200100000400140000110000000010000000240 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk90 : edgeScan measure 0x404000004000000000010000000000002200000000400140000120000000010000000240 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk91 : edgeScan measure 0x404000004004000000010000000000000200000000400140000500000000010000000240 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk92 : edgeScan measure 0x405000004000000000010000000000000200000000400140001100000000010000000240 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk93 : edgeScan measure 0x404000004000000000010000000000000200400000404140000100000000010000000240 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk94 : edgeScan measure 0x404000004000000000010000000000008200000000408140000100000000010000000240 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk95 : edgeScan measure 0x404000004000000000050000000000000200000000440140000100000000010000000240 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk96 : edgeScan measure 0x404000004010000000010000000000000200000000500140000100000000010000000240 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk97 : edgeScan measure 0x404000004000000000010000000000020202000000400140000100000000010000000240 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk98 : edgeScan measure 0x404000004000000000110000000000000210000000400140000100000000010000000240 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk99 : edgeScan measure 0x404000004000000000010000000000000200000000400140000100000000010000000240 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk100 : edgeScan measure 0x404000004000400000011000000000000200010000400100000100000000010000005300 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk101 : edgeScan measure 0x404100004000000000011000000000000200010000400100000100000000010000011300 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk102 : edgeScan measure 0x404000004000000000011000000000000200010000400100000100000000010000001300 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk103 : edgeScan measure 0x404100004000400000010000000000000200010000400100000100000000010000014300 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk104 : edgeScan measure 0x404000004000400000010000000000000200010000400100000100000000010000004300 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk105 : edgeScan measure 0x404100004000000000010000000000000200010000400100000100000000010000010300 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk106 : edgeScan measure 0x404000004000000000010000000000000200010000400100000100400000014000000300 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk107 : edgeScan measure 0x404000004000000000010000000000000200050000400100000100000000050000000300 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk108 : edgeScan measure 0x404000004000000000010000000000000a00010000400100000100000000090000000300 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk109 : edgeScan measure 0x404000004000000000014000000000000200010000400100000100000000410000000300 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk110 : edgeScan measure 0x404000004001000000010000000000000200010000400100000100000001010000000300 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk111 : edgeScan measure 0x404400004000000000010000000000000200010000400100000100000004010000000300 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk112 : edgeScan measure 0x404000004000000000010000000000000200010000400500000104000000010000000300 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk113 : edgeScan measure 0x404000004000000000010000000000000200110000400100000110000000010000000300 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk114 : edgeScan measure 0x404000004000000000010000000000002200010000400100000120000000010000000300 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk115 : edgeScan measure 0x404000004004000000010000000000000200010000400100000500000000010000000300 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk116 : edgeScan measure 0x405000004000000000010000000000000200010000400100001100000000010000000300 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk117 : edgeScan measure 0x404000004000000000010000000000000200410000404100000100000000010000000300 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk118 : edgeScan measure 0x404000004000000000010000000000008200010000408100000100000000010000000300 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk119 : edgeScan measure 0x404000004000000000050000000000000200010000440100000100000000010000000300 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk120 : edgeScan measure 0x404000004010000000010000000000000200010000500100000100000000010000000300 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk121 : edgeScan measure 0x404000004000000000010000000000020202010000400100000100000000010000000300 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk122 : edgeScan measure 0x404000004000000000110000000000000210010000400100000100000000010000000300 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk123 : edgeScan measure 0x404000004000000000010000000000000200010000400100000100000000010000000300 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk124 : edgeScan measure 0x404100004000400000011000000000000200000000400100000100000000010000015200 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk125 : edgeScan measure 0x404000004000400000011000000000000200000000400100000100000000010000005200 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk126 : edgeScan measure 0x404100004000000000011000000000000200000000400100000100000000010000011200 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk127 : edgeScan measure 0x404000004000000000011000000000000200000000400100000100400000014000001200 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk128 : edgeScan measure 0x404000004000000000011000000000000200040000400100000100000000050000001200 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk129 : edgeScan measure 0x404000004000000000011000000000000a00000000400100000100000000090000001200 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk130 : edgeScan measure 0x404000004000000000015000000000000200000000400100000100000000410000001200 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk131 : edgeScan measure 0x404000004001000000011000000000000200000000400100000100000001010000001200 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk132 : edgeScan measure 0x404400004000000000011000000000000200000000400100000100000004010000001200 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk133 : edgeScan measure 0x404000004000000000011000000000000200000000400500000104000000010000001200 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk134 : edgeScan measure 0x404000004000000000011000000000000200100000400100000110000000010000001200 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk135 : edgeScan measure 0x404000004000000000011000000000002200000000400100000120000000010000001200 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk136 : edgeScan measure 0x404000004004000000011000000000000200000000400100000500000000010000001200 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk137 : edgeScan measure 0x405000004000000000011000000000000200000000400100001100000000010000001200 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk138 : edgeScan measure 0x404000004000000000011000000000000200400000404100000100000000010000001200 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk139 : edgeScan measure 0x404000004000000000011000000000008200000000408100000100000000010000001200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk140 : edgeScan measure 0x404000004000000000051000000000000200000000440100000100000000010000001200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk141 : edgeScan measure 0x404000004010000000011000000000000200000000500100000100000000010000001200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk142 : edgeScan measure 0x404000004000000000011000000000020202000000400100000100000000010000001200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk143 : edgeScan measure 0x404000004000000000111000000000000210000000400100000100000000010000001200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk144 : edgeScan measure 0x404000004000000000011000000000000200000000400100000100000000010000001200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk145 : edgeScan measure 0x404100004000400000010000000000000200000000400100000100000000010000014200 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk146 : edgeScan measure 0x404000004000400000010000000000000200000000400100000100400000014000004200 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk147 : edgeScan measure 0x404000004000400000010000000000000200040000400100000100000000050000004200 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk148 : edgeScan measure 0x404000004000400000010000000000000a00000000400100000100000000090000004200 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk149 : edgeScan measure 0x404000004000400000014000000000000200000000400100000100000000410000004200 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk150 : edgeScan measure 0x404000004001400000010000000000000200000000400100000100000001010000004200 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk151 : edgeScan measure 0x404400004000400000010000000000000200000000400100000100000004010000004200 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk152 : edgeScan measure 0x404000004000400000010000000000000200000000400500000104000000010000004200 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk153 : edgeScan measure 0x404000004000400000010000000000000200100000400100000110000000010000004200 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk154 : edgeScan measure 0x404000004000400000010000000000002200000000400100000120000000010000004200 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk155 : edgeScan measure 0x404000004004400000010000000000000200000000400100000500000000010000004200 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk156 : edgeScan measure 0x405000004000400000010000000000000200000000400100001100000000010000004200 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk157 : edgeScan measure 0x404000004000400000010000000000000200400000404100000100000000010000004200 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk158 : edgeScan measure 0x404000004000400000010000000000008200000000408100000100000000010000004200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk159 : edgeScan measure 0x404000004000400000050000000000000200000000440100000100000000010000004200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk160 : edgeScan measure 0x404000004010400000010000000000000200000000500100000100000000010000004200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk161 : edgeScan measure 0x404000004000400000010000000000020202000000400100000100000000010000004200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk162 : edgeScan measure 0x404000004000400000110000000000000210000000400100000100000000010000004200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk163 : edgeScan measure 0x404000004000400000010000000000000200000000400100000100000000010000004200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk164 : edgeScan measure 0x404100004000000000010000000000000200000000400100000100400000014000010200 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk165 : edgeScan measure 0x404100004000000000010000000000000200040000400100000100000000050000010200 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk166 : edgeScan measure 0x404100004000000000010000000000000a00000000400100000100000000090000010200 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk167 : edgeScan measure 0x404100004000000000014000000000000200000000400100000100000000410000010200 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk168 : edgeScan measure 0x404100004001000000010000000000000200000000400100000100000001010000010200 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk169 : edgeScan measure 0x404500004000000000010000000000000200000000400100000100000004010000010200 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk170 : edgeScan measure 0x404100004000000000010000000000000200000000400500000104000000010000010200 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk171 : edgeScan measure 0x404100004000000000010000000000000200100000400100000110000000010000010200 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk172 : edgeScan measure 0x404100004000000000010000000000002200000000400100000120000000010000010200 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk173 : edgeScan measure 0x404100004004000000010000000000000200000000400100000500000000010000010200 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk174 : edgeScan measure 0x405100004000000000010000000000000200000000400100001100000000010000010200 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk175 : edgeScan measure 0x404100004000000000010000000000000200400000404100000100000000010000010200 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk176 : edgeScan measure 0x404100004000000000010000000000008200000000408100000100000000010000010200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk177 : edgeScan measure 0x404100004000000000050000000000000200000000440100000100000000010000010200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk178 : edgeScan measure 0x404100004010000000010000000000000200000000500100000100000000010000010200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk179 : edgeScan measure 0x404100004000000000010000000000020202000000400100000100000000010000010200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk180 : edgeScan measure 0x404100004000000000110000000000000210000000400100000100000000010000010200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk181 : edgeScan measure 0x404100004000000000010000000000000200000000400100000100000000010000010200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk182 : edgeScan measure 0x404000004000000000010000000000000200040000400100000100400000054000000200 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk183 : edgeScan measure 0x404000004000000000010000000000000a00000000400100000100400000094000000200 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk184 : edgeScan measure 0x404000004000000000014000000000000200000000400100000100400000414000000200 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk185 : edgeScan measure 0x404000004001000000010000000000000200000000400100000100400001014000000200 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk186 : edgeScan measure 0x404400004000000000010000000000000200000000400100000100400004014000000200 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk187 : edgeScan measure 0x404000004000000000010000000000000200000000400500000104400000014000000200 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk188 : edgeScan measure 0x404000004000000000010000000000000200100000400100000110400000014000000200 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk189 : edgeScan measure 0x404000004000000000010000000000002200000000400100000120400000014000000200 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk190 : edgeScan measure 0x404000004004000000010000000000000200000000400100000500400000014000000200 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk191 : edgeScan measure 0x405000004000000000010000000000000200000000400100001100400000014000000200 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk192 : edgeScan measure 0x404000004000000000010000000000000200400000404100000100400000014000000200 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk193 : edgeScan measure 0x404000004000000000010000000000008200000000408100000100400000014000000200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk194 : edgeScan measure 0x404000004000000000050000000000000200000000440100000100400000014000000200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk195 : edgeScan measure 0x404000004010000000010000000000000200000000500100000100400000014000000200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk196 : edgeScan measure 0x404000004000000000010000000000020202000000400100000100400000014000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk197 : edgeScan measure 0x404000004000000000110000000000000210000000400100000100400000014000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk198 : edgeScan measure 0x404000004000000000010000000000000200000000400100000100400000014000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk199 : edgeScan measure 0x404000004000000000010000000000000a000400004001000001000000000d0000000200 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk200 : edgeScan measure 0x404000004000000000014000000000000200040000400100000100000000450000000200 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk201 : edgeScan measure 0x404000004001000000010000000000000200040000400100000100000001050000000200 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk202 : edgeScan measure 0x404400004000000000010000000000000200040000400100000100000004050000000200 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk203 : edgeScan measure 0x404000004000000000010000000000000200040000400500000104000000050000000200 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk204 : edgeScan measure 0x404000004000000000010000000000000200140000400100000110000000050000000200 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk205 : edgeScan measure 0x404000004000000000010000000000002200040000400100000120000000050000000200 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk206 : edgeScan measure 0x404000004004000000010000000000000200040000400100000500000000050000000200 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk207 : edgeScan measure 0x405000004000000000010000000000000200040000400100001100000000050000000200 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk208 : edgeScan measure 0x404000004000000000010000000000000200440000404100000100000000050000000200 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk209 : edgeScan measure 0x404000004000000000010000000000008200040000408100000100000000050000000200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk210 : edgeScan measure 0x404000004000000000050000000000000200040000440100000100000000050000000200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk211 : edgeScan measure 0x404000004010000000010000000000000200040000500100000100000000050000000200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk212 : edgeScan measure 0x404000004000000000010000000000020202040000400100000100000000050000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk213 : edgeScan measure 0x404000004000000000110000000000000210040000400100000100000000050000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk214 : edgeScan measure 0x404000004000000000010000000000000200040000400100000100000000050000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk215 : edgeScan measure 0x404000004000000000014000000000000a00000000400100000100000000490000000200 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk216 : edgeScan measure 0x404000004001000000010000000000000a00000000400100000100000001090000000200 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk217 : edgeScan measure 0x404400004000000000010000000000000a00000000400100000100000004090000000200 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk218 : edgeScan measure 0x404000004000000000010000000000000a00000000400500000104000000090000000200 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk219 : edgeScan measure 0x404000004000000000010000000000000a00100000400100000110000000090000000200 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk220 : edgeScan measure 0x404000004000000000010000000000002a00000000400100000120000000090000000200 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk221 : edgeScan measure 0x404000004004000000010000000000000a00000000400100000500000000090000000200 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk222 : edgeScan measure 0x405000004000000000010000000000000a00000000400100001100000000090000000200 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk223 : edgeScan measure 0x404000004000000000010000000000000a00400000404100000100000000090000000200 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk224 : edgeScan measure 0x404000004000000000010000000000008a00000000408100000100000000090000000200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk225 : edgeScan measure 0x404000004000000000050000000000000a00000000440100000100000000090000000200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk226 : edgeScan measure 0x404000004010000000010000000000000a00000000500100000100000000090000000200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk227 : edgeScan measure 0x404000004000000000010000000000020a02000000400100000100000000090000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk228 : edgeScan measure 0x404000004000000000110000000000000a10000000400100000100000000090000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk229 : edgeScan measure 0x404000004000000000010000000000000a00000000400100000100000000090000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk230 : edgeScan measure 0x404000004001000000014000000000000200000000400100000100000001410000000200 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk231 : edgeScan measure 0x404400004000000000014000000000000200000000400100000100000004410000000200 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk232 : edgeScan measure 0x404000004000000000014000000000000200000000400500000104000000410000000200 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk233 : edgeScan measure 0x404000004000000000014000000000000200100000400100000110000000410000000200 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk234 : edgeScan measure 0x404000004000000000014000000000002200000000400100000120000000410000000200 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk235 : edgeScan measure 0x404000004004000000014000000000000200000000400100000500000000410000000200 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk236 : edgeScan measure 0x405000004000000000014000000000000200000000400100001100000000410000000200 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk237 : edgeScan measure 0x404000004000000000014000000000000200400000404100000100000000410000000200 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk238 : edgeScan measure 0x404000004000000000014000000000008200000000408100000100000000410000000200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk239 : edgeScan measure 0x404000004000000000054000000000000200000000440100000100000000410000000200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk240 : edgeScan measure 0x404000004010000000014000000000000200000000500100000100000000410000000200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk241 : edgeScan measure 0x404000004000000000014000000000020202000000400100000100000000410000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk242 : edgeScan measure 0x404000004000000000114000000000000210000000400100000100000000410000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk243 : edgeScan measure 0x404000004000000000014000000000000200000000400100000100000000410000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk244 : edgeScan measure 0x404400004001000000010000000000000200000000400100000100000005010000000200 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk245 : edgeScan measure 0x404000004001000000010000000000000200000000400500000104000001010000000200 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk246 : edgeScan measure 0x404000004001000000010000000000000200100000400100000110000001010000000200 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk247 : edgeScan measure 0x404000004001000000010000000000002200000000400100000120000001010000000200 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk248 : edgeScan measure 0x404000004005000000010000000000000200000000400100000500000001010000000200 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk249 : edgeScan measure 0x405000004001000000010000000000000200000000400100001100000001010000000200 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk250 : edgeScan measure 0x404000004001000000010000000000000200400000404100000100000001010000000200 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk251 : edgeScan measure 0x404000004001000000010000000000008200000000408100000100000001010000000200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk252 : edgeScan measure 0x404000004001000000050000000000000200000000440100000100000001010000000200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk253 : edgeScan measure 0x404000004011000000010000000000000200000000500100000100000001010000000200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk254 : edgeScan measure 0x404000004001000000010000000000020202000000400100000100000001010000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk255 : edgeScan measure 0x404000004001000000110000000000000210000000400100000100000001010000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk256 : edgeScan measure 0x404000004001000000010000000000000200000000400100000100000001010000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk257 : edgeScan measure 0x404400004000000000010000000000000200000000400500000104000004010000000200 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk258 : edgeScan measure 0x404400004000000000010000000000000200100000400100000110000004010000000200 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk259 : edgeScan measure 0x404400004000000000010000000000002200000000400100000120000004010000000200 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk260 : edgeScan measure 0x404400004004000000010000000000000200000000400100000500000004010000000200 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk261 : edgeScan measure 0x405400004000000000010000000000000200000000400100001100000004010000000200 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk262 : edgeScan measure 0x404400004000000000010000000000000200400000404100000100000004010000000200 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk263 : edgeScan measure 0x404400004000000000010000000000008200000000408100000100000004010000000200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk264 : edgeScan measure 0x404400004000000000050000000000000200000000440100000100000004010000000200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk265 : edgeScan measure 0x404400004010000000010000000000000200000000500100000100000004010000000200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk266 : edgeScan measure 0x404400004000000000010000000000020202000000400100000100000004010000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk267 : edgeScan measure 0x404400004000000000110000000000000210000000400100000100000004010000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk268 : edgeScan measure 0x404400004000000000010000000000000200000000400100000100000004010000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk269 : edgeScan measure 0x404000004000000000010000000000000200100000400500000114000000010000000200 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk270 : edgeScan measure 0x404000004000000000010000000000002200000000400500000124000000010000000200 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk271 : edgeScan measure 0x404000004004000000010000000000000200000000400500000504000000010000000200 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk272 : edgeScan measure 0x405000004000000000010000000000000200000000400500001104000000010000000200 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk273 : edgeScan measure 0x404000004000000000010000000000000200400000404500000104000000010000000200 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk274 : edgeScan measure 0x404000004000000000010000000000008200000000408500000104000000010000000200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk275 : edgeScan measure 0x404000004000000000050000000000000200000000440500000104000000010000000200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk276 : edgeScan measure 0x404000004010000000010000000000000200000000500500000104000000010000000200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk277 : edgeScan measure 0x404000004000000000010000000000020202000000400500000104000000010000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk278 : edgeScan measure 0x404000004000000000110000000000000210000000400500000104000000010000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk279 : edgeScan measure 0x404000004000000000010000000000000200000000400500000104000000010000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk280 : edgeScan measure 0x404000004000000000010000000000002200100000400100000130000000010000000200 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk281 : edgeScan measure 0x404000004004000000010000000000000200100000400100000510000000010000000200 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk282 : edgeScan measure 0x405000004000000000010000000000000200100000400100001110000000010000000200 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk283 : edgeScan measure 0x404000004000000000010000000000000200500000404100000110000000010000000200 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk284 : edgeScan measure 0x404000004000000000010000000000008200100000408100000110000000010000000200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk285 : edgeScan measure 0x404000004000000000050000000000000200100000440100000110000000010000000200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk286 : edgeScan measure 0x404000004010000000010000000000000200100000500100000110000000010000000200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk287 : edgeScan measure 0x404000004000000000010000000000020202100000400100000110000000010000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk288 : edgeScan measure 0x404000004000000000110000000000000210100000400100000110000000010000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk289 : edgeScan measure 0x404000004000000000010000000000000200100000400100000110000000010000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk290 : edgeScan measure 0x404000004004000000010000000000002200000000400100000520000000010000000200 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk291 : edgeScan measure 0x405000004000000000010000000000002200000000400100001120000000010000000200 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk292 : edgeScan measure 0x404000004000000000010000000000002200400000404100000120000000010000000200 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk293 : edgeScan measure 0x40400000400000000001000000000000a200000000408100000120000000010000000200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk294 : edgeScan measure 0x404000004000000000050000000000002200000000440100000120000000010000000200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk295 : edgeScan measure 0x404000004010000000010000000000002200000000500100000120000000010000000200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk296 : edgeScan measure 0x404000004000000000010000000000022202000000400100000120000000010000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk297 : edgeScan measure 0x404000004000000000110000000000002210000000400100000120000000010000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk298 : edgeScan measure 0x404000004000000000010000000000002200000000400100000120000000010000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk299 : edgeScan measure 0x405000004004000000010000000000000200000000400100001500000000010000000200 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk300 : edgeScan measure 0x404000004004000000010000000000000200400000404100000500000000010000000200 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk301 : edgeScan measure 0x404000004004000000010000000000008200000000408100000500000000010000000200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk302 : edgeScan measure 0x404000004004000000050000000000000200000000440100000500000000010000000200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk303 : edgeScan measure 0x404000004014000000010000000000000200000000500100000500000000010000000200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk304 : edgeScan measure 0x404000004004000000010000000000020202000000400100000500000000010000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk305 : edgeScan measure 0x404000004004000000110000000000000210000000400100000500000000010000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk306 : edgeScan measure 0x404000004004000000010000000000000200000000400100000500000000010000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk307 : edgeScan measure 0x405000004000000000010000000000000200400000404100001100000000010000000200 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk308 : edgeScan measure 0x405000004000000000010000000000008200000000408100001100000000010000000200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk309 : edgeScan measure 0x405000004000000000050000000000000200000000440100001100000000010000000200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk310 : edgeScan measure 0x405000004010000000010000000000000200000000500100001100000000010000000200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk311 : edgeScan measure 0x405000004000000000010000000000020202000000400100001100000000010000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk312 : edgeScan measure 0x405000004000000000110000000000000210000000400100001100000000010000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk313 : edgeScan measure 0x405000004000000000010000000000000200000000400100001100000000010000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk314 : edgeScan measure 0x40400000400000000001000000000000820040000040c100000100000000010000000200 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk315 : edgeScan measure 0x404000004000000000050000000000000200400000444100000100000000010000000200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk316 : edgeScan measure 0x404000004010000000010000000000000200400000504100000100000000010000000200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk317 : edgeScan measure 0x404000004000000000010000000000020202400000404100000100000000010000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk318 : edgeScan measure 0x404000004000000000110000000000000210400000404100000100000000010000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk319 : edgeScan measure 0x404000004000000000010000000000000200400000404100000100000000010000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk320 : edgeScan measure 0x404000004000000000050000000000008200000000448100000100000000010000000200 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk321 : edgeScan measure 0x404000004010000000010000000000008200000000508100000100000000010000000200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk322 : edgeScan measure 0x404000004000000000010000000000028202000000408100000100000000010000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk323 : edgeScan measure 0x404000004000000000110000000000008210000000408100000100000000010000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk324 : edgeScan measure 0x404000004000000000010000000000008200000000408100000100000000010000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk325 : edgeScan measure 0x404000004010000000050000000000000200000000540100000100000000010000000200 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk326 : edgeScan measure 0x404000004000000000050000000000020202000000440100000100000000010000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk327 : edgeScan measure 0x404000004000000000150000000000000210000000440100000100000000010000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk328 : edgeScan measure 0x404000004000000000050000000000000200000000440100000100000000010000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk329 : edgeScan measure 0x404000004010000000010000000000020202000000500100000100000000010000000200 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk330 : edgeScan measure 0x404000004010000000110000000000000210000000500100000100000000010000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk331 : edgeScan measure 0x404000004010000000010000000000000200000000500100000100000000010000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk332 : edgeScan measure 0x404000004000000000110000000000020212000000400100000100000000010000000200 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk333 : edgeScan measure 0x404000004000000000010000000000020202000000400100000100000000010000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk334 : edgeScan measure 0x404000004000000000110000000000000210000000400100000100000000010000000200 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk335 : edgeScan measure 0x404000004040000000010000000000000240000000400100000100000000010000000200 es25 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk336 : edgeScan measure 0x404000004000000000010000000000000200000000400100000100000000010000000200 es25 3 = true := by decide +kernel


private theorem allCases : edgeScan measure 0x404000004000000000010000000000000200000000400100000100000000010000000200 es0 3 = true :=
  (edgeNode (edgeNode (edgeNode chunk0 (edgeNode chunk1 (edgeNode chunk2 (edgeNode chunk3 (edgeNode chunk4 chunk5))))) (edgeNode (edgeNode chunk6 (edgeNode chunk7 (edgeNode chunk8 (edgeNode chunk9 chunk10)))) (edgeNode (edgeNode chunk11 (edgeNode chunk12 (edgeNode chunk13 chunk14))) (edgeNode (edgeNode chunk15 (edgeNode chunk16 chunk17)) (edgeNode (edgeNode chunk18 chunk19) (edgeNode chunk20 (edgeNode chunk21 (edgeNode chunk22 (edgeNode chunk23 (edgeNode chunk24 (edgeNode chunk25 (edgeNode chunk26 (edgeNode chunk27 (edgeNode chunk28 (edgeNode chunk29 (edgeNode chunk30 (edgeNode chunk31 (edgeNode chunk32 (edgeNode chunk33 (edgeNode chunk34 (edgeNode chunk35 (edgeNode chunk36 (edgeNode chunk37 chunk38))))))))))))))))))))))) (edgeNode (edgeNode (edgeNode chunk39 (edgeNode chunk40 (edgeNode chunk41 (edgeNode chunk42 chunk43)))) (edgeNode (edgeNode chunk44 (edgeNode chunk45 (edgeNode chunk46 chunk47))) (edgeNode (edgeNode chunk48 (edgeNode chunk49 chunk50)) (edgeNode (edgeNode chunk51 chunk52) (edgeNode chunk53 (edgeNode chunk54 (edgeNode chunk55 (edgeNode chunk56 (edgeNode chunk57 (edgeNode chunk58 (edgeNode chunk59 (edgeNode chunk60 (edgeNode chunk61 (edgeNode chunk62 (edgeNode chunk63 (edgeNode chunk64 (edgeNode chunk65 (edgeNode chunk66 (edgeNode chunk67 (edgeNode chunk68 (edgeNode chunk69 (edgeNode chunk70 chunk71)))))))))))))))))))))) (edgeNode (edgeNode (edgeNode chunk72 (edgeNode chunk73 (edgeNode chunk74 chunk75))) (edgeNode (edgeNode chunk76 (edgeNode chunk77 chunk78)) (edgeNode (edgeNode chunk79 chunk80) (edgeNode chunk81 (edgeNode chunk82 (edgeNode chunk83 (edgeNode chunk84 (edgeNode chunk85 (edgeNode chunk86 (edgeNode chunk87 (edgeNode chunk88 (edgeNode chunk89 (edgeNode chunk90 (edgeNode chunk91 (edgeNode chunk92 (edgeNode chunk93 (edgeNode chunk94 (edgeNode chunk95 (edgeNode chunk96 (edgeNode chunk97 (edgeNode chunk98 chunk99))))))))))))))))))))) (edgeNode (edgeNode (edgeNode chunk100 (edgeNode chunk101 chunk102)) (edgeNode (edgeNode chunk103 chunk104) (edgeNode chunk105 (edgeNode chunk106 (edgeNode chunk107 (edgeNode chunk108 (edgeNode chunk109 (edgeNode chunk110 (edgeNode chunk111 (edgeNode chunk112 (edgeNode chunk113 (edgeNode chunk114 (edgeNode chunk115 (edgeNode chunk116 (edgeNode chunk117 (edgeNode chunk118 (edgeNode chunk119 (edgeNode chunk120 (edgeNode chunk121 (edgeNode chunk122 chunk123)))))))))))))))))))) (edgeNode (edgeNode (edgeNode chunk124 chunk125) (edgeNode chunk126 (edgeNode chunk127 (edgeNode chunk128 (edgeNode chunk129 (edgeNode chunk130 (edgeNode chunk131 (edgeNode chunk132 (edgeNode chunk133 (edgeNode chunk134 (edgeNode chunk135 (edgeNode chunk136 (edgeNode chunk137 (edgeNode chunk138 (edgeNode chunk139 (edgeNode chunk140 (edgeNode chunk141 (edgeNode chunk142 (edgeNode chunk143 chunk144))))))))))))))))))) (edgeNode (edgeNode chunk145 (edgeNode chunk146 (edgeNode chunk147 (edgeNode chunk148 (edgeNode chunk149 (edgeNode chunk150 (edgeNode chunk151 (edgeNode chunk152 (edgeNode chunk153 (edgeNode chunk154 (edgeNode chunk155 (edgeNode chunk156 (edgeNode chunk157 (edgeNode chunk158 (edgeNode chunk159 (edgeNode chunk160 (edgeNode chunk161 (edgeNode chunk162 chunk163)))))))))))))))))) (edgeNode (edgeNode chunk164 (edgeNode chunk165 (edgeNode chunk166 (edgeNode chunk167 (edgeNode chunk168 (edgeNode chunk169 (edgeNode chunk170 (edgeNode chunk171 (edgeNode chunk172 (edgeNode chunk173 (edgeNode chunk174 (edgeNode chunk175 (edgeNode chunk176 (edgeNode chunk177 (edgeNode chunk178 (edgeNode chunk179 (edgeNode chunk180 chunk181))))))))))))))))) (edgeNode (edgeNode chunk182 (edgeNode chunk183 (edgeNode chunk184 (edgeNode chunk185 (edgeNode chunk186 (edgeNode chunk187 (edgeNode chunk188 (edgeNode chunk189 (edgeNode chunk190 (edgeNode chunk191 (edgeNode chunk192 (edgeNode chunk193 (edgeNode chunk194 (edgeNode chunk195 (edgeNode chunk196 (edgeNode chunk197 chunk198)))))))))))))))) (edgeNode (edgeNode chunk199 (edgeNode chunk200 (edgeNode chunk201 (edgeNode chunk202 (edgeNode chunk203 (edgeNode chunk204 (edgeNode chunk205 (edgeNode chunk206 (edgeNode chunk207 (edgeNode chunk208 (edgeNode chunk209 (edgeNode chunk210 (edgeNode chunk211 (edgeNode chunk212 (edgeNode chunk213 chunk214))))))))))))))) (edgeNode (edgeNode chunk215 (edgeNode chunk216 (edgeNode chunk217 (edgeNode chunk218 (edgeNode chunk219 (edgeNode chunk220 (edgeNode chunk221 (edgeNode chunk222 (edgeNode chunk223 (edgeNode chunk224 (edgeNode chunk225 (edgeNode chunk226 (edgeNode chunk227 (edgeNode chunk228 chunk229)))))))))))))) (edgeNode (edgeNode chunk230 (edgeNode chunk231 (edgeNode chunk232 (edgeNode chunk233 (edgeNode chunk234 (edgeNode chunk235 (edgeNode chunk236 (edgeNode chunk237 (edgeNode chunk238 (edgeNode chunk239 (edgeNode chunk240 (edgeNode chunk241 (edgeNode chunk242 chunk243))))))))))))) (edgeNode (edgeNode chunk244 (edgeNode chunk245 (edgeNode chunk246 (edgeNode chunk247 (edgeNode chunk248 (edgeNode chunk249 (edgeNode chunk250 (edgeNode chunk251 (edgeNode chunk252 (edgeNode chunk253 (edgeNode chunk254 (edgeNode chunk255 chunk256)))))))))))) (edgeNode (edgeNode chunk257 (edgeNode chunk258 (edgeNode chunk259 (edgeNode chunk260 (edgeNode chunk261 (edgeNode chunk262 (edgeNode chunk263 (edgeNode chunk264 (edgeNode chunk265 (edgeNode chunk266 (edgeNode chunk267 chunk268))))))))))) (edgeNode (edgeNode chunk269 (edgeNode chunk270 (edgeNode chunk271 (edgeNode chunk272 (edgeNode chunk273 (edgeNode chunk274 (edgeNode chunk275 (edgeNode chunk276 (edgeNode chunk277 (edgeNode chunk278 chunk279)))))))))) (edgeNode (edgeNode chunk280 (edgeNode chunk281 (edgeNode chunk282 (edgeNode chunk283 (edgeNode chunk284 (edgeNode chunk285 (edgeNode chunk286 (edgeNode chunk287 (edgeNode chunk288 chunk289))))))))) (edgeNode (edgeNode chunk290 (edgeNode chunk291 (edgeNode chunk292 (edgeNode chunk293 (edgeNode chunk294 (edgeNode chunk295 (edgeNode chunk296 (edgeNode chunk297 chunk298)))))))) (edgeNode (edgeNode chunk299 (edgeNode chunk300 (edgeNode chunk301 (edgeNode chunk302 (edgeNode chunk303 (edgeNode chunk304 (edgeNode chunk305 chunk306))))))) (edgeNode (edgeNode chunk307 (edgeNode chunk308 (edgeNode chunk309 (edgeNode chunk310 (edgeNode chunk311 (edgeNode chunk312 chunk313)))))) (edgeNode (edgeNode chunk314 (edgeNode chunk315 (edgeNode chunk316 (edgeNode chunk317 (edgeNode chunk318 chunk319))))) (edgeNode (edgeNode chunk320 (edgeNode chunk321 (edgeNode chunk322 (edgeNode chunk323 chunk324)))) (edgeNode (edgeNode chunk325 (edgeNode chunk326 (edgeNode chunk327 chunk328))) (edgeNode (edgeNode chunk329 (edgeNode chunk330 chunk331)) (edgeNode (edgeNode chunk332 chunk333) (edgeNode chunk334 (edgeNode chunk335 chunk336)))))))))))))))))))))))))


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private def model : Model mask (fun v => !shared v) :=
  ⟨vertices,86869,by decide +kernel,
    model_bound es0 86869 0x404000004000000000010000000000000200000000400100000100000000010000000200 3
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) allCases⟩


end Seed0

namespace Seed1

private def vertices : Finset (Fin 17) :=
  {0,1,2,3,4,10,14,15,16}


private def measure : Nat → Bool :=
  fun z => (fun v => !shared v) (measures vertices 115743 z)


private def es30 : List (Sym2 (Fin 17)) :=
  []


private def es29 : List (Sym2 (Fin 17)) :=
  s(14,15) :: es30


private def es28 : List (Sym2 (Fin 17)) :=
  s(10,16) :: es29


private def es27 : List (Sym2 (Fin 17)) :=
  s(10,15) :: es28


private def es26 : List (Sym2 (Fin 17)) :=
  s(10,14) :: es27


private def es25 : List (Sym2 (Fin 17)) :=
  s(4,16) :: es26


private def es24 : List (Sym2 (Fin 17)) :=
  s(4,15) :: es25


private def es23 : List (Sym2 (Fin 17)) :=
  s(4,14) :: es24


private def es22 : List (Sym2 (Fin 17)) :=
  s(3,16) :: es23


private def es21 : List (Sym2 (Fin 17)) :=
  s(3,15) :: es22


private def es20 : List (Sym2 (Fin 17)) :=
  s(3,10) :: es21


private def es19 : List (Sym2 (Fin 17)) :=
  s(3,4) :: es20


private def es18 : List (Sym2 (Fin 17)) :=
  s(2,16) :: es19


private def es17 : List (Sym2 (Fin 17)) :=
  s(2,14) :: es18


private def es16 : List (Sym2 (Fin 17)) :=
  s(2,10) :: es17


private def es15 : List (Sym2 (Fin 17)) :=
  s(2,4) :: es16


private def es14 : List (Sym2 (Fin 17)) :=
  s(1,16) :: es15


private def es13 : List (Sym2 (Fin 17)) :=
  s(1,15) :: es14


private def es12 : List (Sym2 (Fin 17)) :=
  s(1,14) :: es13


private def es11 : List (Sym2 (Fin 17)) :=
  s(1,10) :: es12


private def es10 : List (Sym2 (Fin 17)) :=
  s(1,4) :: es11


private def es9 : List (Sym2 (Fin 17)) :=
  s(1,3) :: es10


private def es8 : List (Sym2 (Fin 17)) :=
  s(1,2) :: es9


private def es7 : List (Sym2 (Fin 17)) :=
  s(0,16) :: es8


private def es6 : List (Sym2 (Fin 17)) :=
  s(0,15) :: es7


private def es5 : List (Sym2 (Fin 17)) :=
  s(0,14) :: es6


private def es4 : List (Sym2 (Fin 17)) :=
  s(0,10) :: es5


private def es3 : List (Sym2 (Fin 17)) :=
  s(0,4) :: es4


private def es2 : List (Sym2 (Fin 17)) :=
  s(0,3) :: es3


private def es1 : List (Sym2 (Fin 17)) :=
  s(0,2) :: es2


private def es0 : List (Sym2 (Fin 17)) :=
  s(0,1) :: es1


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk0 : edgeScan measure 0xc00080024002000000000000000040000000000000000000000040020022002400020006 es2 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk1 : edgeScan measure 0xc0008002400200000000000000004000000000000000000000004002002a00200002000a es3 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk2 : edgeScan measure 0xc00080024002000000000000000040000000000000000000000040120022002000020012 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk3 : edgeScan measure 0xc00080024002000000000000000044000000000000000000000040020022002000020402 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk4 : edgeScan measure 0xc00080024002400000000000000040000000000000000000000040020022002000024002 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk5 : edgeScan measure 0xc00080024002000000000000000040000000000000000000000040020022002000020002 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk6 : edgeScan measure 0xc0008002400200000000000000004000000000000000000000004002002a00240000000c es3 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk7 : edgeScan measure 0xc00080024002000000000000000040000000000000000000000040120022002400000014 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk8 : edgeScan measure 0xc00080024002000000000000000044000000000000000000000040020022002400000404 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk9 : edgeScan measure 0xc00080024002400000000000000040000000000000000000000040020022002400004004 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk10 : edgeScan measure 0xc00080024002000000000000000040000000000000000000000040020022002400000004 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk11 : edgeScan measure 0xc0008002400200000000000000004000000000000000000000004012002a002000000018 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk12 : edgeScan measure 0xc0008002400200000000000000004400000000000000000000004002002a002000000408 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk13 : edgeScan measure 0xc0008002400240000000000000004000000000000000000000004002002a002000004008 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk14 : edgeScan measure 0xc0008002400200000000000000004000000000000000000000004002002a002000000008 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk15 : edgeScan measure 0xc00080024002000000000000000044000000000000000000000040120022002000000410 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk16 : edgeScan measure 0xc00080024002400000000000000040000000000000000000000040120022002000004010 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk17 : edgeScan measure 0xc00080024002000000000000000040000000000000000000000040120022002000000010 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk18 : edgeScan measure 0xc00080024002400000000000000044000000000000000000000040020022002000004400 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk19 : edgeScan measure 0xc00080024002000000000000000044000000000000000000000040020022002000000400 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk20 : edgeScan measure 0xc00080024002400000000000000040000000000000000000000040020022002000004000 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk21 : edgeScan measure 0xc0008002c002000000000000000040000000000000000000000040020022002000008000 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk22 : edgeScan measure 0xc00180024002000000000000000040000000000000000000000040020022002000010000 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk23 : edgeScan measure 0xc00080024002000000000000000040000000000000000000000040020022002800080000 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk24 : edgeScan measure 0xc00080024002000000000000000040000000000000000000000040020032002000100000 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk25 : edgeScan measure 0xc00080024002000000000000000040000000000000000000000040220022002000200000 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk26 : edgeScan measure 0xc00080024002000000000000000048000000000000000000000040020022002008000000 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk27 : edgeScan measure 0xc00080024002800000000000000040000000000000000000000040020022002080000000 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk28 : edgeScan measure 0xc00080034002000000000000000040000000000000000000000040020022002100000000 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk29 : edgeScan measure 0xc00280024002000000000000000040000000000000000000000040020022002200000000 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk30 : edgeScan measure 0xc00080024002000000000000000040000000000000000000000040420022006000000000 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk31 : edgeScan measure 0xc00080024002000000000000000050000000000000000000000040020022102000000000 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk32 : edgeScan measure 0xc00080024003000000000000000040000000000000000000000040020023002000000000 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk33 : edgeScan measure 0xc00480024002000000000000000040000000000000000000000040020026002000000000 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk34 : edgeScan measure 0xc000800240020000000000000000400000000000000000000000408200a2002000000000 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk35 : edgeScan measure 0xc00080024002000000000000000060000000000000000000000040022022002000000000 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk36 : edgeScan measure 0xc00080064002000000000000000040000000000000000000000040060022002000000000 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk37 : edgeScan measure 0xc008800240020000000000000000400000000000000000000000400a0022002000000000 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk38 : edgeScan measure 0xc00080024002000000000000000040000000000000000000000040020022002000000000 es23 2 = true := by decide +kernel


private theorem allCases : edgeScan measure 0xc00080024002000000000000000040000000000000000000000040020022002000000000 es0 2 = true :=
  (edgeNode (edgeNode chunk0 (edgeNode chunk1 (edgeNode chunk2 (edgeNode chunk3 (edgeNode chunk4 chunk5))))) (edgeNode (edgeNode chunk6 (edgeNode chunk7 (edgeNode chunk8 (edgeNode chunk9 chunk10)))) (edgeNode (edgeNode chunk11 (edgeNode chunk12 (edgeNode chunk13 chunk14))) (edgeNode (edgeNode chunk15 (edgeNode chunk16 chunk17)) (edgeNode (edgeNode chunk18 chunk19) (edgeNode chunk20 (edgeNode chunk21 (edgeNode chunk22 (edgeNode chunk23 (edgeNode chunk24 (edgeNode chunk25 (edgeNode chunk26 (edgeNode chunk27 (edgeNode chunk28 (edgeNode chunk29 (edgeNode chunk30 (edgeNode chunk31 (edgeNode chunk32 (edgeNode chunk33 (edgeNode chunk34 (edgeNode chunk35 (edgeNode chunk36 (edgeNode chunk37 chunk38)))))))))))))))))))))))


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private def model : Model mask (fun v => !shared v) :=
  ⟨vertices,115743,by decide +kernel,
    model_bound es0 115743 0xc00080024002000000000000000040000000000000000000000040020022002000000000 2
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) allCases⟩


end Seed1

private def rows : Array Nat :=
  #[120158,117948,87984,109936,117568,114304,64384,65024,96768,96256,126976,106496,90112,98304,32768,0,0]


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem aligned : ∀ i j : Fin 17, i < j → (board mask).Adj i j →
    (rowAt rows i.val).testBit j.val = true := by decide +kernel


private def book : Array (List Nat) :=
  #[
[0x14f3360b42447215c36040c791a25c12a3b8a61a02015655],
[0x14f4360b49807215c36044c791a25c14e3a4a61802815555,0x1e98398a6a0c4100271acae8354c0ade91a007118853aaaa,0x8c53dcd4ace628c080c0416b16f4b94341cd02804431717,0xcf8358b525c7094834080e7a1ac5a9223c0a4184c015353,0xd05358b49dc8114837840f121ac5b9474c0a4198200d4d5,0x18f2360a4ad07194c27040c789b04ad48390ae30c2015959,0x4d1bdcc5a0e6201490c0a16b1eb5106941c067404532e2e,0x12e5320b43ca6090e36804c4bc4d5ba0a21d05180c11a6a6,0x6e3b20942ca6111e16814c23c4d4816a71d05818611acac,0x1f04b50b531c510ce13008f821a95a9cc208e0298610d3d4],
[0x703b96c4b4a8119447802f1352b6114771503818010acae,0x8c541ed32d2728c480b80d6056f4b9033a8d02904025557,0x10f2b96c48e0709944680487b44b61150395c3480c112d2e,0xd02b1ca49de8091626806f4304d22d474c1c500cc10e8ea,0x10e2b20a49d66091e26806c23c4d42d5049dc500cc11a9aa],
[0x20f7358b5250731483104107b9ac5a928398a41882015355,0x4b1bdcd628e628489041016b16a7a46041cc4740a231b1d,0xaf4398b5360701883484487b52c5a84e396041802613335,0xf0235eb519c8015834844f621a45a847824ae180260d2d5],
[0xd013d8d5a5ca09c8540c0f6a16c51d222c0640b8c005357,0x16f5386c4b60801c46290287b52b8394728c416100612c2f,0xcf1360b4a80809dc560c8c791a25a5472c0600b8c815457,0xee831eb4b5480184428c2e63d2d5a14781443090061a4a7,0xee1b20a4b568019e42882c23d2d42d4781443704061a8ab,0x1f04358b51dc9114833040f821ac5a8ee488a4198200d1d5,0x10f2b92c52e0709864680487b44b4a990395c3200c112b2e,0xcf1360b53127095c34008c791a95a9023c0a01b8c115356],
[0x18f2354b4c00719502704c9789b05b144380ae30c2815559,0x12e5320b41ca6091e26806c23c4d5ba0a49d0500cc11a6aa],
[0xcf1360b5248809dc560c0c791a25a9272c0680b8c015257,0xf0235cc53cc500d624850f4b1ab22840820ee28c260cbd1,0xd0531cb49de8090a26806f4304d5b9474c08500cc10e4ea,0xb0331ca43da3209613812f4b10d22c0a13a06394610eaf0,0x20e3298523da338961401304bd0c234023396a394611bbc0],
[0xcf1360b5300909dc540c8c791a95a8e22c0600b8c815157,0x12f0360b53107194c27048c789a95aa08390a030c2e15359,0x18f2386d52e0909c46414087b5704a8e228c2e610c01191f,0x190235eb51dc90a04530c0f621b05a8e54886e090c00d0d7,0x1707354c499e8014833882f439ab83147124a4184060ccd3,0x12f0394d5b20719905104887b56953204394603082e1171d,0x6e3b20a4b4a8119e45802c23d2d12d4771503818011a8ae,0xee83169435e620d422802e43d2d6116a81c4628c011acb2,0x1107b5cc51d2508d623008f731ab22910488e028cc10cbd2],
[0xee1b20b4b548019e42882c23d2d5a14781443704061a4ab,0x7073d4d5b00911d053048f6b969530e428860818280555d],
[0xf0235cc519e8015634882f431ab22847824ae184060cad3,0x16f7360c52087014c34882c7b9ab82849390a81840614b53,0x12e7b20a4156608ce26808c73c4d42e0a21d2028cc11aab2,0x170735ec51d2510d013008f639ab82904488e0298610cbd4],
[0x7073d8d5a50a11c853040f6b96c51d2828864818200535d,0xf0235ec519c9015035882f621ab128e4824ae184060c9d3,0x6f4b90b53207118a1680887b4495a9cc39480818611333c,0x6f4b60b53107115c13008c791a95a9c8388a0818611535c,0x16f62a062a12410dc1680ec7904e8350902d472986117b84,0xaf4396c3a60620941680687b44b6112e51e060146112f38,0x18f5b9472c1a418901480c97b51073044581473146113f48],
[0x8c53dcd1ad27314480c0016b16f4b903398b0510403151f,0x1cb83dac4a8e5184061208e6c18b7a54140ce0308a434b55,0x20f3b98b6a50620023128b07b54c5852871c06188853a4ae,0xf01b9ec5b549020462902f6352b520e580c41710060a4af,0x1af0b94c58e0901d06290487b60b530e428c41481c61252f,0x70734cc59d49120257900f139ab520e54b061818800c4cf,0xcf8358b5380909c854086e7a5ac5a8e22c064004c81515b,0x16f63a0a3b505010c34844c7b52e82c48510e51802613b45,0x16e53609430a6110e37802c13da98396a21d051980119ca6],
[0x17073ccd6208a01c4548c2f6b96a81c492b0680900604b57,0x10f2b9ac52e0709883480487b58b4a850395c4180c112b36,0xd0135cc51de8095634808f431ab228474c0a01b8c10cad6,0x1cb83dac428e5180261248e6c18b7a42a40ce03088534b56],
[0x20673dab6292728483120106b98a5a5013bcc4188a03515d,0x12f0398d58e0a09c86414487b56c51e0228c24480ce1131f,0x16f53a093b105010c26846c7b44983968510e500c2613d49,0x12f1b96c4160709942680887b44b6120a3952070cc112e3a,0xee1b20942da6209e12814c23d0d4816a81c46714611acb8,0xf0235cc53cc5189614810f4b1ab22840820ee314610cbd8,0x1e9441ca61482081671b4cd8302a22dee1812811cc52bbc8],
[0xf01b96c4b5e8219422802f4352b611478144670c010acba,0x20f72d462b58438d21400507b9286b08232d472806117784,0xd013d8d5b80a0a4874146f6a56c51ca21c024038c80515f,0x149441eb698a4184470398d605405c1ee1a507310a227785,0x8d2bdcc5a4e6101480c0616b1eb5112341dd00184532d3a,0xf02356c499e8195427002f409ab61147824ae30c010ccda,0x1f06354b438e410d21300af825ae5b08a40807298610d6e4],
[0x1cb1bdac828e5104c90208a6c18b7a461410e0718a234b59,0x12f1b98a3c10501162684c97b44c22e08500e570c2613b49,0xf0235ec519c90204558c2f621ab128e58246e090060c8d7,0xcf1360c52c8909dc540c0c791ab4a8e22c0680b8c014957,0xb07354b4b1e8010c33882f439a95b14711205184060d4e3,0x14f2360c5a507315c31040c791ab54128398ae1882014755,0x1af1394b3c18501103484c97b6085b044500e51b82613745,0xaf439ac5260701882584687b58b1292e3960400c2612b39,0x18e0b60942ca6191e23814c23db04816a11d0530dc119caa,0x1e98398a2a0c2080871b56e8342c02de91a14411cc53aab8],
[0x8d2bdcc4a8e6100680c1616b1eb0254341dd02184532b3a,0x14b23dcc6a50730825040616b14b7c1283986e0148232c3b,0x1cb1c1ed33147288290208d641697a0613a8c07148224b5b,0xee1b60c4a828019e55888c23dab12547814607050618c9b,0x12f52e0833585011c33844c791286ba0b128e51802617685,0xf0235ec538c9015025846f625ab128e4820ae00c260c9d9,0x1307b8ac51d68098826806f7344b42a074958400cc10aaba,0x1307b4ec53968094823006f725ab42a07608a400cc10cada,0xcf835cc52487095624006e7b1ab229223c0a800cc114b5a],
[0x14943dcd62ce620c25040416b16a4c1ee41c662808231727,0xb07354b4bd88010c33844f4b9a85b14711205180260d4e5,0x1af12e0932985011c33850c792086a560128e51b82617585,0x12e5360b43ca6090e36004c4bda25ba0a21d05180c1196a6,0x12f52e08335c5090e36004c7a1226ba0b228e5180c117686,0x1107b4ec53969094823006f725ab428f0608a400cc10c9da],
[0x6f4b90c53607118a1580887b52b129cc394808186112b3c,0x1cb1c1ed33147284490208d641697a0613a8c0710a224b5d,0xf0235ec599ca015034844f621ab51c44824ae180260c3d5,0xd0535cb4bce8090a36004f4b1a25b94744085180c10d4e6,0x1cb83dac4a8e5080661208e6c18b7a54140ce0208c534b5c,0x6f4b98a3c10511161680c97b44c22dc8500e58186113b4c],
[0x16f0394d6220911c86194287b56a830e928c241180e10d1f,0xd00b54c59dc91208578c0f121ab530e54c064099c00c4d7,0xf0235cc519e9020655882f431ab128e58246e204060c8db,0xcf835cc52c8909c654080e7b1ab4a8e22c068204c01495b,0xee1b20a4b568219e22802c23d2d42d478144670c011a8ba,0xcf1360c5a80909dc540c8c791ab524e22c0600b8c814557,0x8d2bdcc5a927308080c0616b1eb52503399d0014443293b,0xaf4360b51987011c34844c791a85a84e3a6051802615365,0xef42e0a33585011c34844c791286ac4e828e51802617385,0x12f53a0b3b105010c26846c7b4495ba08510e500c2613749,0x16f538ac4b60811c86180287b52b8394728d841180112c3e],
[0xee835eb4b1480184428c2e63da95a1478144309006194a7,0x16f5386d4b20801c46290287b5698394728c416100611c2f,0x1af12e0943146015c438c2c792096a16a11ca30b80617487],
[0x4b1bdcd4314731429040816b1697a06a398a07408230b1f,0xcf1360c5a48a09dc540c0c791ab51d222c0680b8c014357,0xf0235ec599ca0204548c2f621ab51c458246e090060c2d7,0x20673dac5a92728403120906b98b525013bcc0188a43495d,0x12f1b8ac52e0809c86680487b44b4aa0728d84700c112a3e,0xf04398a2bcc3209616812f4b44c22c0e82146394610bbd0],
[0xd013dcd62c8a0a4674140f6b16a49ca21c028238c00495f,0x1e8141ac3ad4928c060b88d8058b4a0ef50cc02b8442c1d7,0x8d2bdcc1a927300480c1616b1eb02503399d0510453293e],
[0xf00354c599e91a0857082f409ab530e5824643040e0c4db,0x16f63a0a3b50500cc24848c7b52e82c48510e028c2613b51,0xcf8354c5b80909c854086e7a5ab530e22c064004c81455b,0x14943dcd1ace620445041816b1604c1ee41c66510a23172d,0xee1b20b4b548219e22802c23d2d5a1478144670c011a4ba],
[0xee1b60b4b148019e42882c23da95a1478144370406194ab],
[0x12f0394d60e0b09c86414487b56a3b20228c24480ce1071f,0xcf835cc5a48a09c654080e7b1ab51d222c068204c01435b,0x20673dac52d2728483120106b98b4a9013bcc4188a03455d,0x6f6394b4b60711504304087b52e5b144388a3818201354d,0x16e5360c424a6110e37802c13dab8392a21d051980118ea6],
[0x8d63dca81ca3080cb1250a6b1ee1ac2049110388c533b54,0xd013d4d6380b0a4874146f6a56a3b0a21c024038c80455f,0x12f5386d5b20801c46290287b56953a0728c41610061162f,0x1107b5cc59c8a0a4653080f731ab51cb048868204c00c1db],
[0x10f5386d5960909c46610087b562538f028d21610c01152f,0x20673dac4ad4728403120906b98b4a1413bcc0188a43435d,0xf01b9ed5b149020462902f63569520e580c4171006094af,0x1af13a0b53107014c44846c7b6095a848390a3038261334d,0xaf4398d52e0701883484487b56c4a84e396041802611b35,0x20f3b9ab6250620023128b07b58a5852871c0618885394ae],
[0x1af0b94c58e0902087298487b60b530e518444481c61243f,0xd013dcd6248b0a8674140f6b16a395221c028238c00435f,0xcf0b60c5a809121c71948c791ab524e51c020119c81445f,0x1ee8354c59c29120861940e83dab530e548c24119001849f,0xee8356c4bc280194428c4e4bdab61147814430810618ca7,0x10f2b98d52e0709883480487b56c4a850395c4180c111b36],
[0x12e0b60c42ca6191e23814c23dab4820a11d0530dc118eaa],
[0x18f5ba0a3b505188c14808c7b53072c48510e03146113b58,0x18b1c1ee6a8e510489020cd62d507a461400e4718a223b59,0x1d02b56c499e8191423802f441ab61147125c530c010ccea,0x1e94398a81482080c71b56a8342c02dee1912811cc53abc8],
[0x20673dac42d4939423110106b98b4a0ea33ca1188803415f,0x70734cc59c8a124287940f139ab51ca34b028818800c0df,0xf01b94c4b5e8014c45882f4352b13147810a3704060accb,0x14943dcd62ce618485040416b16a4c1ee41c64300a231735,0xce8316941de5091426806e43c4d6116a4c0e500cc11acca],
[0xee1b60c4ac28019e42894c23dab48147814437050618cab],
[0x1af23a0a4b107014c25846c7b60912d48390ae00c2613959],
[0x18f5c1c831062080aa4b4ed7b03070c4b0288941cc52bee0,0x14923dcd62d0730c25040416b16a4c1e83986e2808231637,0xb043d8d599ca01c834844f6a16c51c4e2a6041802605375,0x6f4b90d53207118a1580887b569129cc394808186111b3c,0xaf4360b5192720dc16004c791a25a90e3a6062806115374,0xef42e0a3352520dc16004c791226ad0e828e62806117394,0xcf83987229a3289614012e7b50c224025c0ca3946113f60],
[0x1af13a0b53107014c34848c7b6095a848390a01b82613355,0x20f3b9ac5a50620143114307b58b5112871c261880538cae,0xf01b96d63c29021462904f4b56a610e580c417010608caf,0x16f5386d6220901c46290287b56a838e928c416100610d2f,0x8c53dcd2ad2730c080c0416b16f4b903399502804431537,0xb0735ec599490204438c2f639ab520e512603090060c4e7,0x16f62206239a3508e1480ac7a50e8184d22c0a3946117ea0],
[],
[0x1103b98a23da3289613012f4b50c22c10708ca394610bbe0,0x2943dcd62d4730c85040416b16a4a1ee398642820231337,0x14f43a0b4b467214c26040c7b5225c14e390a640c2013559,0x14e5a5e8241a330981280e963d04741ab0184a394611bce0],
[0xd02b9e942ce408d826814f634444816a441c728cc10bce2,0x17063d48338e410d21680af6a44e8308b428072986107ea4,0xee431ea2c16320921680c963c4d42c8e80146394611abd0,0x1cf6a9862412328961400e97c1cc2350202cca3946117ba0],
[0x12f1ba0b53107014c26848c7b4495aa08390a070c2613359,0x20e3a98823da330961281304bd0c2340b7184a394611bae0,0x67741ac32d282082503d4d0b98b481077a866814822c4eb,0xaf4398a3c1a400d62484c97b50c22c4e5020728c2613b61],
[0xd02b5cc51de808d624808f431ab228474c1c028cc10caf2,0xd02b98a43ce408d626812f4b44c22c0a441c728cc10bae2],
[0x18f2394d5960919d06104087b570530e428d2e308201153d,0x17063d0a3392410ce1680af6a44e82d0c228072986107ba4],
[0xcf8398a3a12410d61680ae7b44c22d09540072986113b64,0x6f4ba0b53107114c16808c7b4495a9c8390a0818611335c,0xd02b98a43ce410d616812f4b44c22c0a441c7298610bae4,0x14f43a0c3a565208c16806c7b44b4412e510e60146112f58,0x1cf6ad462418328921400e97c1c86b08202cca39461177a0],
[0xaf4398d58e0a01c86484487b56c51c4e28e04480261133d,0x16f13a0c53507014c34848c7b52b82848390a01b82612b55,0x16e5360c49428118e37808c13dab83947215201990118cb6,0x16f62a083392410ce1680ac7a44e8350b228072986117aa4,0x16c53dc831c82080a91c1a16b00f8386b4a88811cc533e68,0x14e4ade8241a330981280e963d046c1cb0184a394611b6e0],
[0x18f0b94d596091a087118087b570530e518524309c01143f,0x20f3b9ac2ad2831003128307b58b485077194518804384af,0x1907b969419a418941380af735106116a12407314610bce8,0xcf839693b1a4289414006e7b50961162540c70146113d68],
[0x1103bd4b3358428d217004f689285b090728c728061077a4,0x1e9441cc6a8a2080871accd8314b0a5ee1810411cc52abd8,0xaf2396d6220a01c4648c287b56a61c4928e0e0900610b37,0xcf8398b5350911c851840e7b52c5a8e82c064118201315d,0x1af2394c4c06701502584c97b60b13144380ae40c2612d59,0x1ee834ac524e8118835802e83dab12927415841980118ab6,0x12f52e08339a408ce2600ac7a5026ba0b2280728cc1176a2],
[0x18f5ba0a3a1a4188c1480ac7b51072c49510073146113b68,0x1307b98a419a418961380af7350c22e0a12407314610bae8,0x1b02396c49de8095423006f4360b61147488ae00cc10acda,0xd02b9eb428e410d816812f634445a40a441c7298610b6e4,0xcf8394b3a18410d21680ae7b4485b089540072986113764],
[0x12f1ba0c53507014c25848c7b52b12a08390a070c2612b59,0x1cf2ad483418468d21100e97c0c86b08b029c728861176a4,0x14943dab818a4185c70304a691815c1ee1a507300a235785,0xee1b60c4ac28219e22814c23dab481478144670d0118cba,0x18f2386d5960a0a447418087b57051ca21852e610c01113f,0x14b241cd3b1283086503c2d0b1697c1075186e2140228cbb,0x14b23dcd4312730825040616b1697c10a3986e0148230d3b,0xb073d4b43586011233844f6b9285b08a11e0518026076a5,0x12e7b20a43565188c13808c73d2d42e0a110e0314611aad8,0x1905b9ea499a418901380af6351072d4412407314610b9e8],
[0x13053dcb434e6090a36004f6b1225ba0a41c85180c1076a6,0xcf839ac52567094824006e7b58b429223c0a400cc112b5a,0x149441ed62cc520c270384d6056a4c1ee1a0e62808225787,0xf01b9ec534c9015025848f6352b128e4820a070c260a9d9,0x10f3b60b32845091c36012c791a25a410728e51a0c115786,0x1307b9ac51d68094823006f7358b42a07488a400cc10aada,0x10f52e093358428ce17004c789286b970228c728061175a4,0xee1b1ea4c16520901680c963c4d42d44800e6714611a9d8],
[0xaf2392d6220a01c66588287b56a11d8928e0e2040610b3b,0xaf43a0a4b1a7010c25846c7b50912d4e3920500c2613969,0x16f538ad6260811c86180287b56a8392728d841180110e3e,0x12e0b60c51568199e23808c23dab42a071152030dc118aba,0x1107b9ac51d69094823006f7358b428f0488a400cc10a9da,0x18e5aa09419a4189e1380ac23d107356a12407314611b8e8],
[0x12f5360b43046015c438c2c791a95ba0a11ca30a00615687,0x6f4ba0c53507114c15808c7b52b129c8390a08186112b5c,0x20e3bd6a69883080482b1306bd4162c0372448390c5373a4,0x20773d696a0c418445031506b941601697a067310a2374a5,0x703b96d61429121467808f1356a610e570d208190108cbe,0x16f538ad6220911c86180287b56a838e928d841180110d3e,0x1d05b4ac519e91a0823802f441ab728e51258430c010c8fa,0xd02b98a49de8091626806f4344c22d474c1c500cc10b8ea,0x130539eb419a418981380af635045ba0a12407314610b6e8,0x12f53a0b3a1a4188c1600ac7b5025ba09510073146113768],
[0x10f5360b49c46095c460c0c791a25b95049ca30a0c015587,0x1af23a0c5206901cc55882c7b60b128e92906e404061295b,0x1af12e0943946090e3600ac7a6026a16a21c051b8c1174a6,0xb073dab4b1480184438c2f6b9895a1471160309006074a7,0xf01b9ac519e9020855882f4358b128e582464704060a8db,0x4b1bdcd2b14730489041016b1697a06039944740a230b3d,0xaf43a0b53587010c34844c7b5285a84e392051802613365,0x1ae2320a49d68095e23006c23e0d42d47488ae00cc11a8da,0x14e5b1e8241a330921280e963d0d7408b0184a394611aee0],
[0x14b23dcd1b12839845040216b1697c1073146e5100230c3f,0x12f1b8ad62e0a09c86400487b56a49e0228d84700c110b3e,0xee8354c5bc290208628c4e4bdab530e580c4408106184b7,0x10d52e093bc06095c460c4c491e26b97051ca3080c81d507,0xae2360c51c29021e65886c23dab128e548e0e00506188bb,0xd02b96c43ce408d426812f4b44b6100a441c728cc10aee2],
[0xef4360b53046015c448c2c791a95a84e81ca30a00615387,0x1af23a0c50d0901cc55844c7b60b128e82906e480261295d,0xb0339eb49d48011826846f634445a1474ba0500c260b4e9,0xaf4394b4b207010c2684687b4495b14e3920500c2613569,0x1af12e0a43986090e3480ac7a6086ac4a21c051b8c1172a6,0x1ec8396932082080a71b54e8342f601691a88811cc53b4e8],
[0xaf4398a3c12320961680c97b44c22d0e502063946113b70,0xaf2386d6260a02047598287b56a11d251860e6100610a3f,0xd02b9eb49d48091826806f634445a1474c1c500cc10b4ea,0xb03398a43da3209613812f4b50c22c0a13a06394610baf0,0xe88398a79062081262b56e5342c02c8f80c4941cc53abe0],
[0xaf2386d6220a02447598287b56a11ca91860e610061093f,0xaf43a0b531a7010c24846c7b5095a84e3920500c2613369,0x6e3b60c51429121e65808c23dab128e570d2081901188be,0xce2b169441e408d42680e943c4d6116a041c728cc11ace2],
[0xee1b60c5a829021e62888c23dab524e580c4070506184bb],
[0x1ac02e0943827219e55086c2260f6896a394660050e1e41b,0xce2b1ea4416408d22680e963c4d42c8a041c728cc11aae2],
[0x1307b96c419a418941380af7350b6120a12407314610aee8,0x12f0b94d60e0b02087298487b56a3b20518444481c61063f,0x6f4ba0b52187110c1680ac7b4485a9c939005818611336c,0xef4360a32d2520dc16004c791a24ad0e828e62806115b94,0xcf8396c3a5a4289414006e7b50b61122540c70146112f68],
[0xaf0386d6220b22447518287b56a388a9186066100e1053f,0x16f13a0d53107014c34848c7b56982848390a01b82611b55,0xf01b94d63c2b024882984f4b56a3b0a38044470106084bf,0x1af23a0c58d0a01cc54844c7b60b51c482906e480261235d,0x20f3b9ac2ad2830083128307b58b485077194418805384be,0x1107b96c49da4289413006f7350b61150488c7014610ade8],
[0xef0360b4b148199c51102c791a95a147814613080e1548f],
[0x1e9441cc32882080a71b56d8302b025ee1a88811cc52abe8,0x14e5b20941da4309e12806c23d0d7416a49847014611ace8,0xaf2386d6220b02847498287b56a394491860e610061033f,0x20f73569620e629023128107b9aa6056941cc5188803d40f,0xb03396c49de8011426846f4344b611474ba0500c260ace9,0x1905bcce53507188a14808f6ad30728483b0803146103b78],
[0xd02b96c49de8091426806f4344b611474c1c500cc10acea,0x149441ed62cc5184870384d6056a4c1ee1a0e4300a225795,0xef4360b3284520dc16012c791a25a40e828e62a06115794],
[0x12f1ba0d53107014c25848c7b56912a08390a070c2611b59,0x1e98398a32082080a71b56e8342c02de91a88811cc53aae8,0x14f438cd5a60721443604087b5625412e3b0a61902011755,0xaf43a0c525a7010c25846c7b50b1292e3920500c2612b69,0x18f5b8ca43607188a1480887b53072c4a3b0803146113a78],
[0xd02b9ec51d68091226806f6344b428874c1c500cc10aaea,0x12f5360b43046015c33848c791a95ba0a11ca01a02615695,0xcf8390c52567090a26806e7b44b4292c3c08500cc112b6a,0x1cc1a6083b4a6591e25002c2412f309ab51d0570c011ec2a,0xaf43a0a4b167208c16806c7b44942d4e392060146113978,0x1e88398a3a482080662b56e8342c02d2f50c4821cc53a9e8],
[0x149241ed62d0628c270384d6056a4c1e819cce2808225697,0xef0360b4a846215c36050c791a25a54081ca61a02e15595,0x12f5360b41c46095c36008c791a25ba0a49ca01a0c115696,0x12f5320b43846090e3680ac7a44d5ba0a21c051a0c1166a6,0xd02b9ec51d69091026806f6344b428e44c1c500cc10a9ea,0x15033dc523123409a13816f6b089041061396a3946107fc0],
[0x8c541ed3ad2628c080b84d6056f4b90351cd02804425597,0x14d42e093bc06215c36044c491e26c16e51ca6180281d515,0x6f4ba0d53107114c15808c7b569129c8390a08186111b5c,0x6f4ba0c521a7110c1580ac7b50b129c9390058186112b6c,0xcf8390b5312710ca16808e7b4495a90c3c0802986113374],
[0xef4360b53046015c34848c791a95a84e81ca01a02615395,0xce2b20a49d68091e26806c23c4d42d474c1c500cc11a8ea,0x8c541ab7a4e628c480b80d5058f5b92341cd0290402d517,0xcf8398d52c8909c654080e7b56c4a8e22c068204c01195b,0xb0338ec535e9020645882f4352b128e563a03204060a8eb],
[0xef0360b4b048219c550c2c791a958947814660a00e15497,0x29441ed62d4628c870384d6056a4a1ee19cc42820225397,0x1ed12e0a3b106495c30048c811e96acc851ca01b8221d315,0x10f3b60b53046095c34808c791a95a85071ca01a0c115396],
[0x18d0ae0943c07219c550c4c491f06896a39466081c81d417,0xcf1398d5a60a09c8540c087b56c51d222c0640b8c011357,0xcf8398d52d0911c851840e7b56c4a8e82c064118201195d,0xb0339ec5216320921680ef6344b4288903a06394610abf0],
[0x20f329c523123389a1401707b089035023396a3946117bc0,0xef2360b53048019c548c2c791a95a8478146e0a00615297,0xf043dca2b0c400da24856f6b08902c4e8214728c2607bc1,0x16f639462c12410d01680e97b44e8310402d472986113f84,0x18f23a0b521a7188c1480ac7b5105a8493900e3146113378],
[0x18f2360b51c49099c540c0c791b05a8e24946e0a0c015197,0xf01b94c5b5e9020c42882f4352b530e581043704060a4eb,0xce2b20b49d48091e26806c23c4d5a1474c1c500cc11a4ea,0x16f136083398450ce1480ac7a5a88184b228072b86115ea4,0xae331ea4416320921680e963c4d42c8a03a06394611aaf0],
[0x18d22e0a4bc07099c540c4c491f06ad423946e080c81d117,0x13053dcd42ce6090a36004f6b1624ba0a41c85180c105ea6,0xd02b9ec51d6808d226808f6344b428874c1c028cc10aaf2],
[0x17063dca2a12410da1300ef6b08e82d09009472986107bc4,0x18d0ae0942807199e57088c209f06a56a39460305c81d41b,0x1ac0ae0943947019e42886c2260f6a16a39443005c61e42b,0xcf8394d5b00911d051848e7b569530e42c060118281155d],
[0xf043dcb2a98400da2484cf6b0885a44e8014728c26077c1,0xcf8390c5352710ca15808e7b52b1290c3c0802986112b74,0x20e3bdaa59883080482b1306bd8152c0372448390c535ba4,0x14f4adc522183309a1800e27b0886c1c90196a39461177c0],
[0xcf8398d5a50a11c851840e7b56c51d282c064118201135d,0x18f0b60943946590e3100ac7a5b03216a21c05189c115ca6],
[0x707354b4b00811c867942f139a95b14728c24818080d41f,0x20f7358b424e629023128107b9ac5852a41cc5188803c50f,0x10f3b60c52c86095c34804c791ab4a85071ca8180c114b96,0xb03396c49de8209416806f4344b611474ba06014610acf8],
[0x1b073d4b2a18410d21300ef6ba085b0890094729861077c4,0x16f13a0d6208a01cc548c2c7b56a81c49290680b80610b57,0x16d0320942827119c578c8c111ed8256a394600990e1cc17,0x18f5b60a43846090e3480ac7a5b072c4a21c051a0c115aa6,0xf043dca2b0c4189a14816f6b08902c4e821473146107bc8],
[0xaf43a0c52567208c16806c7b44b4292e392060146112b78,0x20e3bdab51883081282b0506bd815a88372448380c5357a4,0x1307b8cc53568188a13808f7352b42a0713080314610aaf8,0x149441ed72cc4184a70304d629614c1ee1a087300a2257a5],
[0xcf8398d58c0a0a4874144e7b56c51ca21c024480c81115f,0xf01b94d619e9020855882f4356a130e5824647040608cdb,0xcf8394d62c6909c854080e7b56a4b0e22c064404c010d5b,0x150235cc4ade7418650880f431ab4c1463946e204400cd1b,0x13053dcb41985011a33844f6b0885ba0a124e518026076c5,0xef8394b33585011034844e7b5285b044828e51802613785,0xef42dca2c18400da2484c97b0886ac4e8014728c26173c1,0x1103bd4d5b84609123600af6a5625309071c051a0c1057a6,0x1af72d482c18410d21300e97ba086b08b0094729861176c4,0xb0339ec51d69209016806f6344b428e44ba06014610a9f8],
[0x20773dab520c418525030506b9815a8897a067300a2356a5,0x16d0320a4a087119c578c2c111ed82d49394680980e1c917,0x1b073d4b49985011033844f6ba085b144124e518026075c5],
[0x12f5360b43846090e3600ac7a5a25ba0a21c051a0c1156a6,0xb073d4d5b0480192438c2f6b96953087116030a006056a7,0x12f1ba0d6208a01cc55882c7b56a11e09290687040610b5b,0x16d0320943827519e52086c225ed8196a394620050e1cc1b,0x20773dab524c418505030506b9815a9247a067300a2355a5,0xaf43a0c5346901cc25848c7b52b128ee2920040c2612979,0xcf838ac5256809c826806e7b44b429272c18400cc112a7a,0xae3320a49d68209e16806c23c4d42d474ba06014611a8f8],
[0xf043dcb51985011a34844f6b0885a84e824e518026073c5,0x8d2c1cc3a928100660bd6d0b1eb0250750dd0218452a8fa,0x1cd83d6a41483080e61312e6c1e162c0a20d28388c5373c4,0x12f0b60c5a848019c538c8c791ab52607114600a1c614697,0xb073d4d5b0490190438c2f6b969530e4116030a006055a7,0xf01b9ed6188a025055882f6356a11ca48246870406089db,0x10f5360b4b846090e3600ac7a5a25b95021c051a0c1155a6,0x8d2bdcc82927100c80ac6a6b1eb0a503391d0018453297a],
[0x4b1bdcd83147284c90208a6b1697a061390c0740a230b5d,0xef0360c5a049219c550c2c791ab508e9814660a00e14597,0x14d2320b43c27499c500c4c491ed5c0ca3946e081021c617,0x20e3bdab4a8c4184082b0506bd815a54372047300a4353a5],
[0x20773dab6250620c25028506b98a5852879c6628082354a7,0x14d2320b4bc07419c508c4c491ed5c1463946e080481c517,0x1ed831ca4ac87418650880e831ed4ad4639468204401c91b,0x707354c4ac2811c867940f139ab4b14728c24819000cc1f,0xee1b60c51889021e55882c23dab128e58246870406188db,0xcf8392d62c8a09c654004e7b56a49d822c068200c110b5e,0x20e3bdab4a8c4180282b0506bd815a5437204730085353a6],
[0x1cd82de9431472984400c2e641e96a16a394c3090021d427,0x1cd5c1ea41462080ec224cd641e372c2a2012241cc527bd0,0xef2360c5a04a019c548c2c791ab51c498146e0a00614397,0x1907ad493b505190c27040f709306b168510e530c200f549],
[0x12d0320b53c87099c540c4c491ed5aa0239468080ce1c317,0xaf7360b53048018e448c2c7b9a95a847216030a006152a7,0x1cd5c147794620810c224cd541e3730245812241cc52fb50],
[0xcf8386d62c8a0a4474140e7b56a49ca21c028610c01095f,0x707350c52c8911c267940f139ab4a8ec28c28818800c91f],
[0x14d2320b4b807419e50886c225ed5c1463946e004481c51b],
[0x20f7358a5a50731403110307b9ac52d28398a1188043c81f,0x18d0ae0941547199e47080c209f06a16a39523305c01d42b,0x14f5b60c43846490e3080ac7a5ab740ca21c051a04114ea6],
[0x1ed4320b4a807119c51848c811ed5a54e39460118281c51d,0xcf8390d5312710ca15808e7b5691290c3c0802986111b74,0x8d63dca418a3080eb141216b1ee1ac0a22510388c533b94],
[0x707354c5a00911c867942f139ab530e928c24818080c51f,0xcf8394d60c0b0a4874144e7b56a3b0a21c024480c81055f,0xb073c6d5b149020463902f6b969520e510e0161006054af,0xef835cb4b148198a41002e7b1a95a1478148330801154ae],
[0xef0360c5a8291a1c61148c791ab524e580c203090e1449f,0x707358b4954811c267900f139ac5a14728d21818800d42f],
[0x20f7358b5250731483104107b9ac5a928398a4188203c41f,0xcf8386d6248b0a8474140e7b56a395221c028610c01035f],
[0xf043dcb530c500da24848f6b0895a84e820e028c26073d1,0x18f5ba0d51507188c14808c7b57072848391203146111b78,0xef42dca2c123209a1600c97b0826ad0e8014639461173d0],
[0xf01b96d619e9021442882f4356a610e5824437040608ceb,0x1b072dea3b0c500d024848f63a096ac44520e028c260f351,0x14e5b60c49ca8311e20806c23dab741474990500c4118cea,0xaf7354b4404620d21600e97b9a25b08a01e062a061156b4],
[0x20f7358b4292731423110107b9ac5a50a398a1188803c11f,0x16e532093a066015e46882c23c4d8396951ca3404061ad0b,0x13053dcd59c48098a36008f6b16253a07494801a0c1056b6],
[0x1b073d0b5312510ce13008f6ba095a90c208e029861073d4,0x16d5320943827019e42886c225ed8396a39443005061cc2b],
[0x10f2b986229a338961801227b50c2241032dca3946113fa0,0x20773dac4ad0620c25028506b98b4854879c6628082346a7,0x20e3bdab628c3080882a4506bd8a5a42372044380c5353b4,0x1d06bd88228e3289613012f6c1cc2240b408ca3946107ee0],
[0xb073d4d5b0490208638c2f6b969530e510e040a006054b7,0xaf4398d59a0a01c83484487b56c51c4e2a6041802611375,0xaf7360b4b048218e35002c7b9a958947216061a001154b6],
[0xb0035eb4b1c821c4650c2f621a95894728e060900e0d437],
[0x12f53988340a408d62680e97b44c23a0b0290728cc113ea2,0x1103bdca23123289a13016f6b08902d10708ca3946107be0,0x18f2360b53848098e3480ac7a5b05a8472140e1a0c1152b6,0x17063d4e320e410d21680af6ac4e83089428072986103fa4],
[0xef431ca2c12320961680c97b04d22d0e801463946116bd0],
[0x16f63948340a410d21680e97b44e8308b029072986113ea4,0x170731ea3b4c500d024848f6392d82c44520e028c260eb51,0x1cc5a9e72c12368901200c9640cf7350458142394611eb50,0x1cf6a9882412328961300e97c1cc2350b008ca3946117ae0],
[0x16c541ee6a0c41804909cad62d4f838690a0073104523ea6,0x10f2b98a341a408d62480e97b50c22c50029c728cc113ba2,0x16f53a093218410ce1680ac7b44883969228072986113da4],
[0x19022dea4b4c7195027040f609306ad443a0ae30c200f159,0x17073d0c5352510ce13008f6b92b8290c208e02986106bd4,0x1103bdcb22983289a13012f6b0885a410708ca39461077e0],
[0x16f63a0a3212410ce1680ac7b44e82d09228072986113ba4,0xf043d8d519c5011634844f6a16c2284e824e51802605bc5,0x1cd2c1ea6208308166124ed641ea22c2900dc8388c527ae4,0x16f6360a2a12410dc1300ec791ae82d09009472986115bc4],
[0x1af13969440a609143600e97b6026116a01d051b8c113ca6,0x16c53dc881882080e91b4aa6b02f8386b2240811cc533ea8,0x1cf6ad482418328921300e97c1c86b08b008ca39461176e0],
[0x20773dac1ad2831045028306b98b485077986551002344af,0xef83969321a418941600ae7b50261169828073146113da8,0x16c5390781882081e91b4aa2342f8386c5a40811cc53be28],
[0x20f7358b2a50731003128307b9ac5852839945188043c42f,0x18f5ba0a434a6090e34804c7b53072c4a21d05180c113aa6,0xaf7356c5260821843380287b9ab62927116061900114ab6,0xf043dcc534c5189614808f6b12b2284e820e03146106bd8,0x14e5a607331a4409e12806c23d09741a65a847014611bd28],
[0x10f2b94b3358438d21800427b5285b090329c728061137a4,0x149441ed32ca4184470398d605604c1ee1a907310a2257c5,0x1cd2c1eb5208308126130ed641e15a88900dc8388c5276e4,0x1d05b1ea3b4c5189014808f6412d72c44520e0314610eb58,0xef8398a321a418961480ae7b50c22c49828073146113ba8,0x1ae232093a866015e25850c23e0d1256051cae40c261ad19,0xf01b96d619e9221422802f4356a610e58244670c0108cfa,0x14f4b60b2a18430dc1100ec791a85c1c90194728861157c4,0xe883d6a71062081a62b12e6a88162c0f80c4941cc5373e0],
[0x18f1b969440a609142680e97b4506116a01d0570cc113caa,0xaf23a0d6250a01cc25846c7b56a11d282920e00c2610b79,0x16e526083b1a6011e22846c23d09839ab51c4500c261bc29,0x1ae232093ac66095e24014c23e0d4816251cae40cc11ad1a,0x18e5aa07321a4189e1480ac23d10734495a807314611bb28],
[0xef8394b43586011232844e7b5285b08a81c4518026136a5,0x18e1a6083aca6091e26814c23c50481ab51d0570cc11bc2a,0x14b241ac725073086503c2d0a98b7c1283986e214022cc3b,0x12f5360b41985011c33844c791a85ba0a124e518026156c5,0x12e1b1ea3b606015025848863d2d12e0451ca070c261ab19,0x1307b8ad61d6a0a0823006f7356a41e054898400cc108afa,0xcf838ad6256a09c824006e7b56a41d222c18400cc110b7a,0x14d5b20943827219e22806c225ed7416a3944600d011cc3a],
[0x12f53a0b434a6090e36004c7b5225ba0a21d05180c1136a6,0x1ae0b20942867019e55888c23e0d1256a39460405c61ac1b,0x1b0231ea4b8c7015025846f6260d12d443a0ae00c260e959,0x1cd2c1eb42883080e61312d641e15a40a20dc8388c5273e4,0x13053ccd5b1c80144438c2f6a16953a07130a309006056c7,0xef8394b4b586011032844e7b5285b14481c4518026135a5,0x14f4360b49d85311c31040c791a85c14e498e518820155c5,0xaf7360c5a448218e35002c7b9ab50927216061a001146b6,0x12e1b20a3b566095e24008c23d2d42e0251ca070cc11ab1a,0x12f1b98a440a609162680e97b44c22e0a01d0570cc113aaa,0x6f63969440a611141680e97b44e6116a01d058186113cac,0x1cc1a9e93c16568901200c9640cf43564500e2714611e958],
[0xd013d4d59dc90950460c0f6a162530e44c0a30b8c0055c7,0x10f2ba0b4b546090e36004c7b5225a15021dc5180c1135a6,0x1107b1aa4b967094823006f7258d42d50388a400cc10e95a,0x6f4ba0d6150a11cc15808c7b56a11dc8291208186110b7c,0xef8394b321a418921600ae7b5025b0898280731461137a8],
[0xef4360b51985011c34844c791a85a84e824e518026153c5,0xb0238ed619ea024685882f4356a11ca36260e20406088fb,0xaf23a0d6206a024c75882c7b56a11ca91920e404061097b,0xaf43a0b53586010e34844c7b5285a84e21e0518026133a5,0xee1b60c51969221e22802c23dab428e58244670c01188fa,0x6f4b98a440a611161680e97b44c22dca01d058186113aac,0x1cd2bd6a82083080e61312a6c1e162c0920dc8388c5372e4],
[0xef839ab4b1480184428c2e7b5895a1478144309006134a7,0x1ae2320a4a067019e55882c23e0d12d493946e404061a91b,0x20773dac52d2830c85008306b98b4a9077986428402344b7,0xf043ccd5b1ca0144448c2f6a16951c4e830a309006053c7,0xcf1360b49d48095c460c0c791a25a1474c0a30b8c0154c7,0x1b0231ca499e801c655882f4320d12d472a46e204060e85b,0x10f2ba0b53586090e34804c7b5285a85021dc5180c1133a6],
[0xad0320b4bc2821dc650c4c491ed5894728e060810e1c437,0x1ae12e0943147019e428c2c23e096a16a394430b8061b427,0xad2320a4b82801de65886c225ed12d4728e0e005061c83b,0x150331eb4b807215026846f6244d5c1443b8a600c280e559,0x12f53a0b430a6090e26806c7b4495ba0a21d0500cc1136aa],
[0xae42e093b146011e26846c23c496a16e51e0500c261b529,0xf043dcd530c500d624848f6b1692284e820e028c2605bd1,0x16f53a0c3212410ce1680ac7b44b83909228072986112fa4,0xaf4398a3412320961680e97b44c22d0e02a063946113bb0,0xef435ca2c12320961600c97b1a222d0e801463946115bd0],
[0x6f6394b440a611121680e97b44e5b08a01d0581861136ac,0x1b0231eb538c7015024846f6260d5a8443a0ae00c260e359,0x170735ea3b0c500d024848f639a982c44520e028c260db51],
[0x1b00314b4b9e809c853086f4260d5b14728864004ce0e45b,0x1ae0320b4a867099e54088c23e0d5a54239460404ce1a51b,0xef8398b4b548018642882e7b52c5a1478144320406134ab,0x6f63a0b4a146110e1680ac7b44e5a14921c0581861135ac],
[0xad0320b4b82821de65086c225ed5894728e060050e1c43b,0x1ae0ae0943147019e42886c23e096a16a39443005c61b42b,0x12f53a0c42ca6090e36804c7b44b4ba0a21d05180c112ea6,0x17073d0d5312510ce13008f6b9698290c208e02986105bd4],
[0xef8398b4b548018642844e7b52c5a1478144320026134ad,0x1cc1adea4c08769502004c9640cf6ad44380a870c221e159,0x6f4ba0b52186110e1680ac7b4485a9c921c0581861133ac,0xef8396c321a418941480ae7b50b61049828073146112fa8],
[0x4d1bdcb82506200ec0a8aa6b1e35852821c0674045334ae,0x1107b1cb5348909c653080f7312d5a8f028868204c00e15b,0x1ae12e0943147019e42846c23e096a16a39443038261b42d,0x16f63a0a4152610ce16808c7b44e82d0a21d202986113ab4,0x14e5b207325a4409e12806c23d0d741265a847014611af28],
[0x707354c59429120877980f139ab530e518524819000c43f,0x1ed831cb4a82811ca61808e831ed5a54728c80119011c43e,0x4d1b969820e6201ec0a8aa235e36056941c06740453b42e,0x10f2ba0c52da6090e34804c7b50b4a85021dc5180c112ba6],
[0x12f1b96c440a609142680e97b44b6120a01d0570cc112eaa,0x1ae0320b4a82811de61948c23e0d5a54728c201190e1a41f,0xf043d4d599c520d216004f6a1625308e824e628061057d4],
[0x12e1b2083aca6091e26814c23c4d4820b51d0570cc11ae2a,0xae432093ac66011e26854c23c4d4816e51e0540c261ad29,0x10f2b96c49e0609142680687b44b6115049dc500cc112daa],
[0x10e2b2093ac66091e26814c23c4d4817051dc540cc11ad2a,0x13053d8d599c8014833844f6a16c53a07124a418026056d5,0xef4360b531c500cc24848c7a1a95a84e810e028c26153d1,0x6f4b96c440a611141680e97b44b611ca01d058186112eac,0xef8394b4358620d212804e7b5285b08a81c4628061136b4],
[0xef1b96c4b60801944288287b52b61147814437040612cab,0xf003d4d599c9215036044f6a162530e4824a61802e055d5,0x1ed42e0a3b1c548cc20048c821e96acce510e028c221d351,0x10f2ba0c52566090e26806c7b44b4293021dc500cc112baa],
[0x16e5320943467019e42882c23d2d8396a39443404061ac2b,0x20f7358b2a92839803110307b9ac5a50731541188043c03f,0x10f541ab624e5184861380d7858a5b93040ce4308a02d555,0x190235ea4acc7195027040f609b04ad443a0ae30c200d959,0x10e2b20a3a566091e26806c23c4d42d3051dc500cc11ab2a],
[0xf043d8d599ca014834844f6a16c51c4e824a418026053d5,0xef4360b5192520dc16004c791a25a90e824e628061153d4,0x6f4ba0c521a6110e1580ac7b50b129c921c058186112bac,0xaf43a0b5352620ce16004c7b5225a90e21e0628061133b4,0x14f4b985221a330961800e27b50c241c90196a3946113fc0],
[0x1f04358b525c7114833040f821ac5a92e388a4198200d355,0x16f53a0c4b4a8118e41802c7b52b83947215031180112cae,0xd013d4d59dc90a08560c0f6a162530e54c0640b8c0054d7,0xd013d0d5b1ca094e34808f6a16951c4c240a01b8c1053d6],
[0x16e53209434a7119e41802c23d2d8396a39503118011ac2e,0x1ec141ab5250728c860b80d8058f5a92838cc42b8402d457,0xae4320a4b467019e45882c23d2d12d4e39603404061a92b,0xef8358b519c8014834844e7a1ac5a847824a418026152d5],
[0xf023ccd5b1ca0204548c2f6a16951c458306e09006052d7,0xef0360b51909215c36044c791a25a8e8824a61802e151d5,0x190235eb4a80719502704cf609b05a544380ae30c280d559,0x12f1ba0c52ca8098e46804c7b44b4aa0721503700c112aae],
[0xd013d8d59dca0a48540c0f6a16c51ca24c0640b8c0051d7,0x1ed42e0a4b007115c33048c811e96ad4e388a0198281d155,0x10f2b94d32d8438d21800427b5684b090329c72806111fa4],
[0x1e8141ab6292728c860b80d8058a5a50f38cc42b8402d157,0x130035eb530c7195027048f609a95aa043a0a030c2e0d359,0xef4398a2c1a400d62484c97b50c22c4e8014728c2613bc1],
[0x1907b54b4b80809c853086f725b05b14728864004c80d45b,0x1ae0b20b4a867019e42890c23e0d5a54039443405c61a52b,0x16d731ea3c08500d02484c9639ed82c44500e828c261cb51],
[0x12f53a0d42ca6090e36004c7b5624ba0a21d05180c111ea6,0x170735ec51887015034882f639ab828443a4a8184060cb53,0x12f53a0c58ca8098e46804c7b44b53a0721503480c1126ae,0x17063d0d5392410ce1300af6a56e8290c208072986105be4],
[0xcf8398a2a12410d61680ee7b44c22d09041472986113bc4,0xf023dcd6190a015634844f6b16a21c48824ae1802604bd5,0x18d22dea4c00719502704c9609f06ad44380ae30c281d159,0x1af23a0c5212610ce1580ac7b60b1290921c0e2986112bb4,0x1cb83dac3a8a3080861250e6c18b7a42050d04388c534bd4],
[0x1107b58b5380909c853086f725ac5a8f028864004c80d15b,0x170735ec51887015034844f639ab828443a4a8180260cb55,0xd013dcd61d2a095634008f6b16a21d024c0a01b8c104bd6],
[0xef8386c5b549020462902e7b52b520e580c4161006124af,0xef8396d4b1480184428c2e7b56962147814430900611ca7,0x10d7b20a4ac87095c33080c711ed4ad50388a8184c01c953,0x10f2ba0d52d86090e34804c7b5684a85021dc5180c111ba6,0x14e5b2083a5a6209e12806c23d0d7412b51c46014611ae38],
[0x1ae0b20b48d4801de62904c23e0d5a14728c41481c61a42f,0x1ee8354b4b00811c861942e83da95b14728c24118081941f,0x70735eb5300911d053048f639a95a8e428860818280d15d,0x150235cc4acc7414627840f131ab4c1463a0ae20c200cd59,0x1af23a0c52ca8098e34804c7b60b4a8472150e180c112ab6,0xd013d4d5a18428d21700ef6896853089040c72b861057e4,0xae432093ac66209e16814c23c4d4816e51e06414611ad38],
[0xef4398a2c1a418961480c97b50c22c4e801473146113bc8,0xcf8394b2a18410d21680ee7b4485b0890414729861137c4,0xef8390c53566188a14808e7b52b4284c81c803146112bb8],
[0x1cb1c1ac7a8e5105090188d5418b7a464404e0718a22cb59,0xae4320a3a566209e16806c23c4d42d2e51e06014611ab38,0x1e8141ac5a92728c060b88d8058b5250f38cc02b8442c957,0xb073d4d59988011233844f6b968530871260518026056e5,0x14943dcd82cc4184e50304a6b1614c1ee22067300a2317a5,0xae2320942c67019e26854c23c4d4816a3960e40c261ac39,0xef1b96c4b60821942280287b52b611478144670c0112cba,0xcf1354b4418428d21700e9789a85b08a040c72b861156e4,0x1cd5b1ea3c08518901480c9641ed72c44500e8314611cb58,0x18e5a9e72c1a418901480c963d107344458147314611bb48],
[0x14e5b20943467219e22802c23d2d7416a3944640c011ac3a,0x150235cc4ade831c650880f431ab4c1472986e204400cc5b,0x14e2360c4ac67419e50880c23dab4c1463946e4044018d1b,0x1af12e0732985011c34850c792086a4405a8e51b82617705,0x14b241cc6a5073082503c6d0b14b7c1283986e014822ac3b,0xd013d4d5b8e809123600af6a56253087440051b8c1056e6,0x10f2b94d5c04609123600e97b5625309001dc51a0c1117a6,0x1107b5cc52487095623006f731ab22930388a800cc10cb5a],
[0x16e5360943067019e42882c23da98396a394434040619c2b,0x12f1ba0c51568098e26808c7b44b42a072152070cc112aba],
[0xef8394d5b0480192428c2e7b56953087814430a006116a7,0x1cd1b1ea4c08759502004c9641ed32d44380a870c221c959,0x12e1b20a41567099e26808c23c4d42e0a3952070cc11aa3a,0x1307b5cc5188801c655882f731ab12a072a468204060ca5b,0x12e1b60c52087019e55882c23dab12a09394687040618b1b,0xb073d0d5998a010e34844f6b96851c4c2260518026053e5,0xae4320a4b467019e25848c23d2d12d4e3960040c261a939,0x16e629e93c06501102684c963c4e83564500e540c261b949,0x20e3bdab32883080482b1306bd815a40372848390c5353e4],
[0x1107b5cc52c8909c653080f731ab4a8f028868204c00c95b,0x8d2b98a824e6101e80ac6a235ec0ad2341dd0018453a93a,0x1e8141ac52d2728c860b80d8058b4a90f38cc42b8402c557,0xb073ccd5b1490204438c2f6b969520e51320309006054e7,0xef8394d5b0490190428c2e7b569530e4814430a006115a7,0xef2360c5990a015c34844c791ab51c48824ae18026143d5,0xef43a0b53585010c34844c7b5285a84e810e518026133c5,0x16f53a0d4b0a8118e41802c7b56983947215031180111cae,0x1e88358a724e5100660ac8e829ac0ad2f40ce0218453c95a],
[0xf023ccd621cb0284548c2f6a16a394498306e09006043d7,0x1b072de9431460144438c2f63a096a16a11ca3090060f487,0x10f52e093b446095c460c0c791226b97051ca30a0c017507,0x1ed4320b52487115c33040c811ed5a92e388a8198201c355],
[0x16e0360c4a82811de61948c23dab8254728c201190e18c1f,0xae2320a4b46801de65882c23d2d12d4728e0e404061a83b,0x20d7b1ca4ac8831c6508810731ed4ad4729868204401c85b,0x1e8141ac4ad4728c060b88d8058b4a14f38cc02b8442c357,0xcd0b20b4a80811dc578c8c111ed5a5472c060099c81c457,0x70735ec52c8911d053040f639ab4a8e428868818200c95d],
[0xef4398a2c12320961680c97b44c22d0e801463946113bd0,0x14d231eb4b8073150280462625ed5c144398ae00c281c559,0x14e42d893b5e5310628040243d2c6c16e518e520c201b549],
[0x1107b54c5b80909c853086f725ab530f028864004c80c55b,0x18e5a9e72c12320901680c963c507350458146394611bb50],
[0x16e0360c5208911de61942c23dab828e928c281180e1891f,0x70734cc52c89120277940f139ab4a8e51b028818800c85f,0x1e81358b8292728dc60900a811ac5a50f38cc12b8403c157,0x12d031eb5408719502704c9609ed5aa04380a830c2e1c359,0x1ae0b20a4956811de61808c23e0d42d4728d20119c11a83e],
[0x1ae0b20b4a86801de62888c23e0d5a54728c40405c61a43b,0x14d2320b4b80831de50886c225ed5c1472986e004481c45b,0x1107b5cc5a48a09c653080f731ab51d3028868204c00c35b,0x70735ec5a80911d053048f639ab524e428860818280c55d,0x12f53a0d58ca8098e46004c7b56253a0721503480c1116ae,0x17063d0e5352510ce13008f6ad2e8290c208e02986103bd4],
[0x6f62e093a806115c46850c7904e6a56051ca3818281750d,0xaf43a0d52d2620ce16004c7b5624a90e21e062806111bb4],
[0x70735ec5a48a11d053040f639ab51d2428868818200c35d,0x8d63d47818a3081cb1250a691ee1b0205a510388c537b14],
[0x707354c59809120877942f139ab530e51a424818080c45f,0x1ee8354c5a00911c861942e83dab530e928c24118081851f,0xef8386d5b149020462902e7b569520e580c4161006114af,0x1e88358b72927288660900e829ac5a50f38cc1214403c15b,0x1ae0b20b4954811de61808c23e0d5a14728d20119c11a43e],
[0x1ee8358b4954811c261900e83dac5a14728d21118801942f,0x18f23a0d52ca8098e34804c7b5704a8472150e180c111ab6,0xf043d8e534c5189614808f6ad2c2284e820e03146103bd8],
[0x2067358b7a9272850311010539ac5a5043bcc1188a03c15d,0x16e531e93c06501102684c963c4d83964500e540c261ad49,0x1905b9ea3b4c5189014808f6353072c44520e0314610bb58],
[0x1e8141ac72d49394660900d8298b4a0ef30ca1238402c15f,0x14f42e073352520dc16004c791226c10e5a8e62806117714],
[0x16e5360c4a067019e42882c23dab83949394434040618d2b,0x12e1b1ea3c1a501102584c963d0d12e04500e570c261ab49],
[0x20f7358b3292839423110107b9ac5a507328a1188803c05f,0x16e5320941867015e46882c23c4d8396a3a4a3404061ac4b,0x1b0239ea4b0c7015025846f6360912d443a0ae00c260b959,0x16f53a0d624a8118e41802c7b56a83927215031180110eae,0x12f53a0d59448098e36008c7b56253a07215201a0c1116b6,0xb073d0d5992a20ce16004f6b96251d0c2260628061053f4,0x18e1a9e93c16520901680c963c5043564500e6714611b958,0x1103bd8e229a3289613012f6ad0c22410708ca3946103fe0],
[0x14f42e093b446215c36040c791226c16e51ca61a02017515,0xcf8390b5312510ce16808e7b4495a90c240e029861133d4],
[0x14f4b988241a330961280e97b50c241cb0184a3946113ee0,0x18f5c10671062080aa4b4ed7a83070c4c02c8941cc52fea0],
[0x1af12e0a3b106015c34848c792096ac4851ca01b82617315,0xef8396d60c29021462904e7b56a610e580c414810610caf,0xef8394d5b0490208628c2e7b569530e580c440a006114b7,0x1ae0b1ea4c06701504588c963e0d12d44380a3405c61a94b],
[0x16e5360c48c2801de62904c23dab8394728c414810618c2f,0xae035eb4b20821c4650c2863da95894728e060900e19437],
[0xe883dca61062081662b52e6b02a22c0f80c4941cc533be0,0xd02bd8e428e410d616812f6ac4c2240a441c72986103ee4],
[0x1907a568338e408d42680af72450611ab4280728cc10fca2,0xce8298723da3289614012e4bd0c234025c0ca394611bb60],
[0x12e7b20a3b50500cc25848c73d2d12e08510e028c261ab51],
[0xd02bd8e5212410d61680ef6ac4c22909041c72986103be4,0xae0360b4b06821de65082c23da95894728e064040e1943b,0xef8396d62548218432802e7b56a62127814461900110eb6,0xcf2b98a441a408d62480e97b50c22c4a041c728cc113ae2],
[0x18e1adea4c00721502684c963c506ad44380a670c281b159,0xcf8390c5352510ce15808e7b52b1290c240e02986112bd4,0x13053d8e419a418961380af6ad0c23a0a124073146103ee8,0xe883dcb51062081262b58e6b0205a88f80c4941cc5337e0],
[0xcf2b98a4412410d61680e97b44c22d0a041c72986113ae4,0x16f62a073212410dc1680ac7904e835095a8072986117b24],
[0x1ee8350c5954911c261900e83dab520ec28d21118801852f,0x10f3b8ad62e0a09883480487b56a49c5071584180c110bb6,0x1eb62206239a3488e1500ac8250e788cd22c0a394611f6a0],
[0xf043d8e519a418961480af6ad0c2284e824073146103be8,0x16e1360c4a82801de628c8c23dab8254728c400b90618c37,0x1b0239ec4a86701502584cf6360b12544380ae40c260ad59,0x13052de8338e408d82680af624446ba0b4280728cc10f6a2,0xd02bd4e5a18410d21680ef6ac4853089041c729861037e4,0x14e5b1e93c06520901680c963c4d74164500e6414611ad58,0xef83969419a418941600ae7b5026116a824073146113ce8],
[0xef43a0c53565188c14808c7b52b4284e810e03146112bd8,0x14e5b60c42467219e22802c23dab7412a3944640c0118e3a,0x1905b9ea399a418901480af6351072c4452407314610bb68,0x14e5a6083b1a4309e12806c23d09741ab51847014611bc68],
[0x1ee4320a3b565488c11808c83d2d42cce510e0114611ab58,0x1301b9ec534c7015025848f6352b12a043a0a070c260ab59,0xcf2b94b4418410d21680e97b4485b08a041c729861136e4,0x1f062d48338e410d21680af8244e6b08b42807298610f6a4,0x1cf82d473358428d214004e7c1286b0825a8c72806117724,0xef8398a419a418961480ae7b50c22c4a824073146113ae8,0x1ae2320942867015e2584cc23e0d1256a380ae40c261ac59,0x14e5b60c4a067219e22802c23dab741493944640c0118d3a],
[0x8d541cc325072882b03c6d0b1eb1b9283a8d0014822ac5b,0xb072de943546011833882f639246a16a11e05184060f4a3,0x1107b9ac52567094823006f7358b42930388a400cc10ab5a,0x1ae2320942c67095e23014c23e0d4816a388ae40cc11ac5a,0x18b7a6083394408ce2680ac724507a1ab2280728cc11f4a2,0x18f5ba0a4a1a4188c1380ac7b51072d491100731461139e8,0x18e5aa08399a4189e1480ac23d107344b52407314611ba68],
[0x14b239ac82507309e500c2a2358b7c1283986e0940238c3b,0x12f52e083b586011c32844c791286ba0b51c451802617625,0x12e1b20a435e7014c25848c43d2d12e0a390a070c261aa59,0x12e1b60c51567099e24008c23dab42a023952070cc118b3a,0x1e88394961c82080662b56e8342a0316f48c4821cc53b968],
[0x1ae231ea4c06701502584c963e0d12d44380ae40c261a959,0x10f5360b3a446095c460c0c791a25b93051ca30a0c015707,0xe883dcb6a883080462b12e6b1415a40f80c48390c5333e4,0x130535eb431c60144438c2f621a95ba0a11ca3090060d687,0xb072de943546011833844f639246a16a11e05180260f4a5,0x1af12e093a986011c32850c792086a56051c451b82617525,0x12f52dc83b606090a3600487b1226ba0b51c85180c117626,0x12e1b20a43567095e23008c23d2d42e0a388a070cc11aa5a,0x1eb626083394410ce1680ac8244e7a1ab22807298611f4a4],
[0x1b0239ec5186901d055882f6360b128e42a46e404060a95b,0x4d7c169720c4180ac0a8ed729e36056902087340452f4a6,0x1e88398a6a4e5100860ac6e8354c0ad2f40ce4018453a95a,0x110535eb49dc60944460c0f621a25b95049ca3090c00d587,0xae2360c5246801de65882c23dab1292728e0e4040618a3b,0x16f53a0d61429120e61808c7b56a838e520d201190110cbe,0xef8394b419a418921600ae7b5025b08a8240731461136e8],
[0xae2360c5206901de65882c23dab128e928e0e404061893b,0x16e5360c4942811de61808c23dab8394728d201190118c3e,0x14b241cd1b1283984503c2d0b1697c1073146e5100228c3f,0xb0235cc519e9020675882f431ab128e51a60e204060c87b,0xaf42e0a3b586011c34844c791286ac4e51e051802617325],
[0x20d72de9431463944400c30639e96a16a31ca3090021d487,0x1ae2320a4986801de55882c23e0d12d472a46e404061a85b,0x1af12e0943147019c428c2c792096a16a394430b80617427,0x6f3b8ad6260a12086580287b56a11d2570d848180110abe,0x1307b168338e408d42680af7244d6120b4280728cc10eea2,0xb033d8e5212320961680ef6ac4c2290903a063946103bf0],
[0x1ae031eb4c06721502504c963e0d58944380a640c2e1a559,0x6e4b60c5142811de65808c23dab129c728d208190118a3e,0xe883dcb4a882080662b58e6b0205a54f80c4821cc5333e8],
[0xae32e0943147011e26846c23c496a16a3ba0500c261b469,0x1ee834ac5216911c861802e83dab428e928d84118011893e,0x1907adc941d46090a26806f730506a16a49c8500cc10f4aa,0xaf3398a4412320961680e97b44c22d0a03a063946113af0],
[0xb0035cc599e9220675082f431ab508e51a6062040e0c47b,0xae0360c5a06921de65082c23dab508e928e064040e1853b,0x12f0360b3a986195c41050c791a85a60051ca33082e1570d,0x12e1b1eb5408701502684c963c4d5aa04380a870c261a359,0x1cc2a608335e458ce25002c4412f309ab229c728c011eca2],
[0xae2360c50c29021e75984c23dab128e51860e481061883f,0x1ae0320b4a86809de53088c23e0d5a54728860404ce1a45b],
[0xcf8390d5312510ce15808e7b5691290c240e02986111bd4,0xe883dcc5a883080462b52e6b02b5240f80c48390c532be4],
[0x170531c9434e6110a37802f1312d8396a41c85198010eca6,0xef8396c419a418941480ae7b50b6104a824073146112ee8],
[0x10f5360b48c07099c56104c791a25b95039461480c81550f,0x16f1360a3b106015c34848c791a982c4851ca01b82615b15,0xef8394d60c2b024882984e7b56a3b0a38044448106104bf,0x707358b49d48118257900f139ac5a14749461818800d48f,0x1e88398b6a927288060906e8354c5a50f38cc1014443a15b,0x14e5b2083a5a4309e12806c23d0d7412b51847014611ae68],
[0x1ee8354c59429120871980e83dab530e518524119001843f,0x18f2360a3ad26095c34004c791b04ad0251cae180c115b16,0x1e88398959c82081462b46e8342c5116f48c4801cc53ad68],
[0xe883dcc4a882080662b56e6b02b0254f80c4821cc532be8],
[0x1d02b169435e6191423802f4412d6116a11dc530c010ecaa,0x1e88398a49c82080662b56e8342c02d4f48c4821cc53ab68,0xae3320942c67011e26854c23c4d4816a3ba0540c261ac69,0xcf2b96c49e0809142680687b44b611474c1c500cc112cea],
[0x14f4360b3a446215c36040c791a25c12e51ca61a02015715,0xce2b20942c67091e26814c23c4d4816a3c1c540cc11ac6a,0x1ee8350c5948a124271980e83dab51cac18528118801813f,0x18f2360a4ac47099c540c0c791b04ad423946e0a0c015917,0x14b341cc6a5072082503c6d0b14b7c1283b866014822ac6b],
[0x8c541ed4ace628c080b84d6056f4b94341cd02804425717,0x10f5360b3b046095c34808c791a95b85051ca01a0c115716,0x130531cb43ce6090a36804f4b04d5ba0a41c85180c10e6a6,0xcf2ba0c52568090e26806c7b44b42927241c500cc112aea],
[0x18e1b5ea4c08759502004c963db032d44380a870c2219959,0x1e88398a5a4e4104062b46e8342c52d2f40c47018a43a969,0xce2b20a42567091e26806c23c4d42d2a3c1c500cc11aa6a],
[0x12f0360b42847099c560c8c791a25a60a394600a0ce15617,0xef4398d59a0a01483484487b56c51c4e824a418026113d5,0x1e88398a6a4e4100262ac6e8354c0ad2f40c47018853a96a,0xaf42e0a3b52620dc16004c791226ad0e51e062806117334,0x150321c5230e3489a17816f13089040cd4396a394610fec0],
[0x8c53dab824e628dc80880a6918f5b92341cd02844035517,0xf0035eb4b1c82184550c2f621a958947814660900e0d497,0xb0731eb4b5480184438c2f6392d5a14711603090060e4a7,0x1ac0ae0943946110e3780ac1260f6a16a21c05199c11e4a6],
[0xae3320a4b46801de45882c23d2d12d472ba03404061a86b],
[0x12f0360b53047099c540c8c791a95aa02394600a0ce15317,0x1f04a9c5230c3409a13816f83089035c61216a394610fbc0,0xe883dcc6a862080862ad2e6b14b0a40f80c4441cc532bf0],
[0xae431ea3c16320921680c963c4d42c8e50206394611ab70],
[0x18f1b60b4a807099c54088c791b05a54239460704c81551b,0x677418b6a5062082503d4d0b94c5812879c66814822e4ab,0x16f629c72c10400da2484c97b08e834485814728c2617b41,0x1cc2ae0943546191e23802c2412f6a16a11dc530c011e4aa],
[0x1ae0b20b4a86801de4288cc23e0d5a54728043405c61a46b],
[0x18f2360b4a807199c51050c791b05a5403946e308281551d,0x16f63a0d5212410ce1300ac7b56e82909208072986111be4,0x15032dc523d83409a13812f4b0886c0061396a394610f7c0],
[0x8c541ed1ad27314480b80d6056f4b903398b0510402551f,0x703b1cb4b548118a47802f1312d5a14771483818010e4ae,0x170535c9430e6110a37802f131a98396a41c85198010dca6,0x1cd83d4761483081661250e6c1ea2302058d28388c537b44],
[0x12f0360b53107199c51048c791a95aa08394603082e1531d,0x1707354c4bc280188538c4f4b9ab8314711464081060cc97,0x14f2360c4ac47419c508c0c791ab4c1463946e0a04014d17,0x1307adc82a98400da2384cf730886a60b1014728c260f6c1,0x1af72d472c18400d02484c97ba086b0445814728c2617741],
[0x18f0b60b4a80819dc61148c791b05a54728c20309c81541f,0x20f7358b3a50629003128307b9ac5852851cc5188043c48f,0xf042de92a9c400d82684cf620446a56e8014728c260f5c1,0xf043cce6356a188a14808f6ad2a41c4e830803146102bf8],
[0x16f1360c52087019c548c2c791ab82849394680b80614b17,0xb0339ec52567209016806f6344b429243ba06014610ab78,0x14e235ec4ac67315028040263dab4c144398ae40c2018d59,0xae3320942c67209e16814c23c4d4816a3ba06414611ac78],
[0x1107b94d62c6909c853080f7356a4b0f028864404c008d5b,0x1b073d4b39985011034844f6ba085b044524e51802607745,0xf042dca2bcc400da24858f4b0806ac4e8214728c260f3c1,0x8d2c1cc5a507101460bc6d0b1eb5112838dd0018452ac7a,0x1b072de82a8e410d813012f63a046a40b40947298610f6c4,0x1cd83d6751483081061312e6c1e16280458d28388c537744,0xef838cc53568188a14808e7b52b42847830803146112af8,0x18f5a9c72c104189a1480c97b09073448581473146117b48],
[0x18f2360b50c0909dc64144c791b05a8e228c2e480c81511f,0x14943dab81cc4185c50304a691815c1ee4a067300a235725,0x12e1b5ec5408701502584c963dab12a04380a870c2618b59,0xae3320a42567209e16806c23c4d42d2a3ba06014611aa78,0x1cb1c1ac525062888703c2d0c18b7a92819cc4714022cc9b,0x14f235cc4ae0741865088087b1ab4c1463946e2044014d1b,0x1b072d49431e5010c33882f43a096b16a110e5184060f4c3,0xb07354b43d86011233844f4b9a85b08a11e05180260d6a5,0x1ed12e083398448ce1500ac825e8688cb228072b8611d6a4],
[0x14e2360c4ac6831de50880c23dab4c1472986e4044018c5b,0x130535cb43ce6090a36004f4b1a25ba0a41c85180c10d6a6,0x1e88398a6a4e2080862ac6e8354c0ad2f40c4401cc53a978,0x1301b9ed6188a01d055882f6356a11e042a4687040608b5b,0xad72e0943146011e33882c239e96a16a11e05184061d4a3,0xb0339ec5346901d025848f6352b128e42ba0040c260a979,0x10f2b60b3a846091c36012c791a25a41051dc51a0c115726,0x8d2c1cc4a907100660bd6d0b1eb0254838dd0218452aa7a,0x1e8839ac4a8e5100660ac8e8358b0a54f40ce02184538b5a],
[0x12f0360c5a847099c540c8c791ab52602394600a0ce14717,0x1300b54c5bdc80188538c4f4a1ab5320711464081c60c697,0x12f1b60c52087019c55882c791ab12a09394687040614b1b,0x1b072d4943d85010c33844f4ba086b16a110e5180260f4c5,0x1af02e093a985111c33050c792086a560508e51982e17545,0x8d2c1cc7a927101060ac6d531eb0a50438dd0018452a97a,0x1b072dea2a18410d21300ef63a086ac8900947298610f3c4],
[0x12f5360b43047019c428c2c791a95ba0a394430a00615627,0xf0035ec5a1c92184550c2f621ab508e9814660900e0c597,0x12e1b60c5188801de55882c23dab12a072a4687040618a5b,0x207735697a0c41844503150539a1601697a067310a23d4a5,0xae3320a4b46801de25848c23d2d12d472ba0040c261a879],
[0xb0735eb4b1480184438c2f639a95a14711603090060d4a7,0x1e8839ac5a927288060906e8358b5250f38cc1014443895b,0x10f5360b49447099c460c0c791a25b950395230a0c015527,0x1cd83d6a49ca4184061310e6c1e162d4048d07308a437345,0x1ed12e0943946610e3080ac825e66a16a21c051b8411d4a6,0x8d2b98a82507101e60ac6a235ec0ad2838dd0018453a87a,0x8d2c1cc5a928388060bc6d0b1eb5250730dd0014442a87b,0x4b1bdac828e6285c90208a6918b7a46141cc0740a234b1d],
[0xed0320b4bc28219c550c4c491ed58947814660810e1c497,0x16f0360c4a82811dc61948c791ab8254728c201190e14c1f,0x12f1b60c52c87099c54004c791ab4aa0239468700c114b1e],
[0xaf4360b53047019c448c2c791a95a84e396030a00615327,0xce835ec52c8911d051840e63dab4a8e42c068118201895d,0xf01ade9429c501182684cf620446a56a800e570c260f4c9,0x1cf82d493b505190c26040e7c1226b168510e530c2017549],
[0x1cd5bd4781462080cc2250a6c1e3730205912241cc537b50,0x1107b86d62c8a0a4473140f7356a49cb018828610c00895f,0x1cd5c1ea49ca31040c220cd641e372d4148102398a427b51,0x1905a9c82bcc3209a13812f4b0907340b12146394610fad0],
[0x16f0360c5208911dc61942c791ab828e928c281180e1491f,0x1e8839ac52d272888608c0e8358b4a90f38cc4094403855b,0x67741ab625062082503d4d0b98a5812879c66814822d4ab,0x12f0360c5a907199c51048c791ab52608394603082e1471d,0x1af1394b3b20601504484687b6095b04451ca3038261370d,0x1af72e0a3b105010c24846c7ba096ac48510e500c2617349],
[0xce0b60c52c89121e71940c23dab4a8e51c028119c01885f,0xed0320b4a828199e57088c209ed5a547814603050e1c49b,0x170535cc424e6110a37802f131ab8392a41c85198010cea6],
[0x1cf8354b49587199041040e7c1a85b14439523308201552d,0x1cd5c1ea31ca30804c2250d641e372c204a902390c527b54],
[0x12f0360c5a82819dc61148c791ab5260728c203090e1461f,0x703b5cb4b148118a47802f131a95a14771483818010d4ae,0xaf4360a3ad2620dc16004c791a24ad0e51e062806115b34],
[0x1cf8354c5a00919c861142e7c1ab530e928c24308081451f,0x707354c59c29120867940f139ab530e548c24819000c49f,0x10f5386b4b60709845610087b5225b95039461610c01350f,0xb07356c4bc280194438c4f4b9ab6114711603081060cca7,0x8d63dca49cc51840b141016b1ee1ad404a0f0308a433b15,0x16d5320943826110e3780ac125ed8396a21c05199011cca6],
[0x18f0b60b4954819dc61100c791b05a14728d21309c01542f,0xce0b60c5a809121e71948c23dab524e51c020119c81845f],
[0x12f0360c58c8a09dc64144c791ab51e0228c28480ce1431f,0x1cd5c1ea49ca20806c220cd641e372d414810221cc527b58,0x1e94418a71482081671b4cd8282c22dee1812811cc52ebc8,0xf042dca2bcc3209a16012f4b0826ac0e82146394610f3d0],
[0xd0531c941de5091626806f4304d2396a4c0e500cc10ecca,0xaf4360b3a84620dc16012c791a25a40e51e062a06115734],
[0x1af72e0a3b10500cc24848c7ba096ac48510e028c2617351,0x1e8839ac1ad49394460900e8358b4a0ef30ca1510403815f,0x67741ac5a5062094503c2d0b98b5112879c66814022ccab,0x1af1394b3b20601503484887b6095b04451ca01b82613715,0x18b1bdca69cc510489041016b1507ac604a0e4718a233b19,0x1cd2b20942c26191e23814c241ed4816a11dc530d011ccaa],
[0x16e5360c4986801de42882c23dab839472a4434040618c6b,0xee1b20943546015e45882c23d2d1216a81ca3704061ac8b,0x12f5360b43047019c32848c791a95ba0a394401a02615635],
[0xb0735ec5a5480184438c2f639ab5212711603090060c6a7,0xaf0360b4a847219c36050c791a25a540396061a02e15535,0x12f5360b41447099c36008c791a25ba0a395201a0c115636,0x1ed1320b43946490e3080ac825ed5a0ca21c051b8411c6a6],
[0x1b073d8b51907014834844f6ba0c5a8483a4a41802607355,0x1cd83d6a61ca3080861250e6c1ea62c2048d04388c537354,0x703b56c4b82811944780af125ab6114771403819010ccae,0xb0735eb4b148218433802f639a95a14711606190010d4b6,0x8d63dca49cc50806b141016b1ee1ad404a0f0208c533b1c],
[0xaf4360b53047019c34848c791a95a84e396001a02615335,0x18f5b90681062080ea4b4aa7b43070c4c22c0941cc53bea0],
[0xaf0360b4b04821dc650c2c791a95894728e060a00e15437,0x2077358b7a50620c4502830539ac5852879c66290023c4a7,0x10f2b60b53047099c34808c791a95a850395c01a0c115336,0x18f5c1c8698831002a49cad7b15070c4b0a408398852bea2,0x1d06a5e822ce3289813014f641c4481ab408ca394610fce0],
[0xf0431ca2bcc3209616812f4b04d22c0e82146394610ebd0,0x1af02e0a4b107115c33048c792096ad48388a01982e17155],
[0x16f639473220410d21680a87b44e830895a8072986113f24,0x1d06a98823ce3289613012f4c1cc2340b408ca394610fae0,0xaf2360b5304801dc648c2c791a95a84728e0e0a00615237,0x1cd1c1eb628e510489020cd641ea5a461400e4718a227359,0x18f5c1c8698830804a49cad7b15070c4b0a408390c52bea4,0x18f22dca3c105189a1480c97b0906ac48500ee3146117358,0xcf829c723123289a14016e7b089035025c0ca3946117b60,0x10e2a98623da338961801224bd0c2341032dca394611bba0],
[0x18e7a568340a408d42680e973c50611ab0290728cc11bca2,0x18f2360b5144909dc640c0c791b05a8e228d2e0a0c015137,0x1b00b14b4b9e8014c43886f4260d5b147110a3005c60e4cb,0x16f7320a3b50500cc24848c7b92d82c48510e028c2616b51],
[0x677358b82506209e50282a239ac5852879c66814023c4ab,0x1307b1ca41da508d623008f7310d22e0a488e028cc10ead2],
[0x1af0394b4b20711905184887b6095b144394601182e1351d,0x18f22e0a4b507194c27040c789306ad48390ae30c2017159,0x16c53dc869cc4180490c0a16b14f8386b4a0073104533e26,0x12e7a988340a408d62680e973c4c2360b0290728cc11baa2,0x16e525e8340a410d81680e963c44839ab02907298611bca4],
[0x16c53dc741882080a91c1a16b00f8386a5a48811cc533f28,0x1d06ade8228e3289813012f641c46a40b408ca394610f6e0,0x170535cc49c28118a37808f131ab8394749480199010ccb6,0x4d7c1c95a0c41814c09cad731e3511690a007340452bca6,0x1cb83d8a69ca3080861250e6c14c7ac2048d04388c536b54,0x18f5c1c8398820806a4b4ad7b03070c4b5240821cc52bea8],
[0x67741ac7ad28310450282d5398b4850779865810022c4af,0x1cf8350c5954919c261100e7c1ab520ec28d21308801452f,0x4d1bdcb628e628489041016b1ea5a46041cc4740a23331d,0xaf4398a3b60601163484487b52c22c4e51e051802613b25,0x16f6360a39905011c34844c791ae82c48524e51802615b45,0x20f3b58b72506200a3128307a9ac5852871c86188053c4ae,0x16e629e8340a410d21680e963c4e8348b02907298611baa4],
[0x170734ac524e8118837802f139ab8292741584198010cab6,0x10f2b60c52c87099c34804c791ab4a850395c8180c114b36,0x10f2b98a3b60609163480487b52c22c5051dc5180c113b26],
[0x1ec8392859882081471b4ae8342f5118b1a40811cc53bca8,0xaf439693b20601142684687b4496116e51e0500c2613d29,0xb072de9429a400d82384cf639046a56a1020728c260f4e1,0x16c53dc869cc4100291c0a16b14f8386b4a0071188533e2a,0x12e52de8340a408d82680e963c446ba0b0290728cc11b6a2,0x1103adca23d83289a13012f4b0886ac10708ca394610f3e0],
[0x1907b96941ca6091426806f734506116a49d0500cc10bcaa,0x1cf5b20a3b505188c14808c7c12d72c48510e03146116b58,0x1cb1c1ec6a8e510489020cd6414b7a461400e4718a226b59,0xae241ac5a506101471bc2d0bd8b5112819e0e118052ccba,0x10f2b9693b20609142680687b4496117051dc500cc113d2a,0xd052de9438e408d82680af624446b96a4400728cc10f4e2,0xce835ec52567289012006e63dab429243c0c20146118b78,0x1307b1ca434c5189613808f7312d22e0a120e0314610ead8],
[0x14943dcb69cc418445041816b1405c1ee4a067310a233725,0x14f4360b3a585311c31040c791a85c12e518e51882015745,0x1ee62d48340a410d21680e983c4e6b08b02907298611b6a4,0x14b241cd331283882503c6d0b1697c1073286e0148228c7b,0x8d53dcc424e62882b040616b1eb1b92a41cd00148232d1b,0x130535eb419c5011833844f621a45ba0a124e5180260d6c5,0xaf4398a3a60601162684687b44c22d2e51e0500c2613b29,0x14e5b60c4986821de22802c23dab741472a44640c0118c7a,0xee1b20943566215e25002c23d2d4096a81ca670c011ac9a,0x16c53dc869cc4080491c0a16b14f8386b4a007110c533e2c,0x1d05b1ea4b4c5189013808f6412d72d44120e0314610e9d8,0x1e98394861882081671b4ae8342a231eb1a40811cc53baa8],
[0x16f539894360701864288287b52c8396a394432040613c2b,0xee82de943546011832882e63d246a16a81c45184061b4a3,0x1f06354b49dc5111033040f821ae5b144488e5198200d5c5,0xb0735ec5a548218433802f639ab5212711606190010c6b6,0x4d7c1cb520c41812c09cad731e35a8890a007340452b6a6,0x10f2b94b3b60609123600487b5225b09051dc5180c113726,0x10f2b98a3a60609162680687b44c22d3051dc500cc113b2a,0x6f639693a20611141680a87b44e6116951c058186113d2c,0xd052de9438e410d81680af624446b96a44007298610f4e4],
[0x12f1b9ac5220701885588287b58b12a09394647040612b1b,0xae235ec5406901d02584c963dab128e42820e40c2618979,0x1af2320a4b907014c25846c7a60d12d48390ae00c2616959,0x12e1b60c5156809de23008c23dab42a072892070cc118a7a],
[0x6f4b98a3a20611161680a87b44c22dc951c058186113b2c,0x12f0b60c5a84801dc628c8c791ab5260728c400a1c614637,0x12f539ab432070184428c287b5895ba0a394430900613627,0xb0239ed6186a025075882f6356a11ca41a60e404060897b,0xee82de943546011832844e63d246a16a81c45180261b4a5,0xf0435eb519c5011834844f621a45a84e824e5180260d3c5,0x1e8839ac2a927100860ac6e8358b0a50f38d44018453897a,0x1b0231ca49de8095623006f4320d22d47488ae00cc10e8da,0x1cd2c16a7a08308126130ed541e162c8900dc8388c52f2e4,0x1cd83d6a41c83080a61312e6c1e162c0a48c88388c537364,0x1d06b16823ce3289413012f4c1cd6100b408ca394610eee0],
[0xb07354c5bc290208638c4f4b9ab530e510e04081060c4b7,0xd0535eb49dc80944460c0f621a25b9474c0a3090c00d4c7,0x4d7b969820c4180ec0a8aa735e36056922007340453b4a6,0xaf0360c5a04921dc650c2c791ab508e928e060a00e14537,0x4d7c1cb2a50620c0c0a8ed731e35852801d462c0442b4a7,0x1af1394b4b2070190428c287b6095b144394430b80613527,0xcf1360b4a807095c460d0c791a25a5403c0a30b8c815547,0x4b1bdcc6a8e628489041016b14b7a46041cc4740a232b1d,0x1af2320b51907015c34844c7920d5a8483a4ae1802616355,0xaf4394b3b20601122684687b4495b08e51e0500c2613729,0x4d1bdc95a0e62014c0c0a16b1e35116941c067404533c2e,0xad7320b4bc28218e35004c4b9ed5894721606181011c4b6,0x18e5aa0941ca6091e26806c23c507356a49d0500cc11b8aa,0x1ec8396851882081271b4ae8342f6288b1a40811cc53b6a8],
[0xae2360c51869021e75882c23dab128e51a60e404061887b,0x12f1b9ac52e0709885400487b58b4aa0239464700c112b1e,0x1907ad49439a4188c1380af725106b16a11007314610f4e8],
[0x12e7b168340a408d42680e973c4d6120b0290728cc11aea2,0xaf2360c5a04a01dc648c2c791ab51c4928e0e0a00614337,0xcf1360b52587095c440c0c791a85a9223c0a30b8c015347,0xf0435ca2bcc3209616012f4b1a222c0e82146394610dbd0,0x1103b1ca23da3289613012f4b10d22c10708ca394610ebe0],
[0x6f6394b3a20611121680a87b44e5b08951c05818611372c,0x1ec839692a0c4104071b54e8342f601691a147118a43b4a9,0x1cd2c1895a083101460bced0c1ec5116900dc8398452ece2],
[0x16f7360a3b10500cc24848c7b9a982c48510e028c2615b51,0x1ec839696a0c4100271a8ae8354f605691a007118853b4aa,0x1af2386c5220901c46594287b60b128e928c2e610061291f,0x67741ac52d283088503c2d0b98b4a90779864814022c4bb,0xf01b9eb4b548019842882f635245a14781443704060b4ab,0x1af0b94b4b20701904288687b6095b14439443005c61352b,0xd0535cb49de8094646080f431a25b9474c0a3204c00d4cb,0x1af2320b53907014c24846c7a60d5a848390ae00c2616359,0x16e531e8340a410d21680e963c4d8388b02907298611aea4],
[0xae0360c59869221e75082c23dab508e51a6064040e1847b,0xee83169435e6011432882e43d2d6116a81c45184061aca3,0x12f5398b4360701864284487b52c5ba0a39443200261362d,0x4d7c1cc5a0c41814909cad731eb510690a007340452aea6,0xd02b1ca43ce408d626812f4b04d22c0a441c728cc10eae2],
[0x1af1394b4b20701904284687b6095b14439443038261352d,0x6f6360b4a807115c43050c791ae5a540388a3818281554d,0x4d1bdcb520e62012c0c0a16b1e35a88941c06740453362e,0x1ec839696a0c4080471a8ae8354f605691a007110c53b4ac],
[0x17073d8d51907014834844f6b96c828483a4a41802605b55,0x8d63dca41cc3080ab141216b1ee1ac0a4a090388c533b34,0x1cb83daa61ca3080861250e6c18a7ac2048d04388c535b54,0x703b5cc5a829120a67808f131ab524e570c80819010c4be,0x4d7c1cb3a5062006c0a8ad731e35852851c06240452b4ae,0x4d1bdcb424e6200ac0c1416b1e35812a41c86740453352e],
[0x16e53209434a6110e37802c13d2d8396a21d05198011aca6,0x1e98398859882081471b4ae8342c511eb1a40811cc53aea8,0x1af0394c58e0909c86414487b60b530e228c24480ce1251f,0xaf4398b5360701864484487b52c5a84e39603200261332d,0x6f6360b52507115c43040c791ae5a928388a3818201534d,0x14f4360b3a5c520cc26040c7a1a25c12e510e628c2015751],
[0x1cf8354c594291a0871180e7c1ab530e518524309001443f,0x4d1bdcb2a5073100c0c1416b1e35812839945740443342f,0x1307b96c41ca6091426806f7344b6120a49d0500cc10aeaa,0x10f2b96c3a60609142680687b44b6113051dc500cc112f2a,0x1d06b169419e418941380af441cd6116a12407314610ece8,0x10e2b20932da4389e11814c23d0d48170329c7114611ada8],
[0x16f1398d522070188548c287b56c82849394640b80611b17,0x16f0360a4b107115c33048c791a982d48388a01982e15955,0x12e7b20a42ca6090e36804c73c4d4ae0a21d05180c11aaa6,0x1102b96c49de6091426806f4344b6115049dc500cc10adaa],
[0x15043ccd5a5c7214436040f6a1625412e3b0a61902005755,0x18f5b90a3b606188a1480887b53072c4c51c803146113b38,0x1cb1c1ed628e510489020cd6416a7a461400e4718a225b59,0xee1b20942da6011e22854c23d0d4816a81c4570c261aca9,0x1e9441ab628a310487038cd8058a5a5ee18104398a22d3d1,0x6f4b96c3a20611141680a87b44b611c951c058186112f2c,0xaf4394b3b60620d21600487b5225b08e51e062806113734,0x14f4360b3992520dc16004c791a25c10e524e62806115754,0x18f235ca3c10518961480c97b1b022c48500ee3146115b58,0x1307b1ca419a418961380af7310d22e0a12407314610eae8,0x1e98398a41882080a71b56e8342c02dea1a48811cc53aba8],
[0x20e7b169434a6391421803073d2d6116a31d0510c011acaa,0xf01b96c4b5e8019442882f4352b6114781443704060acab,0x1cf8350c5948a1a4271180e7c1ab51cac18528308801413f,0x14b43dcc6a4e620825040616b14b7c12e41c660148232d2b,0x170535cc499e8014643882f431ab83947124a3204060cccb,0x1907b54b49dc8094833080f721b05b147488a4184c00d4d3]]


private def models : Array (Model mask (fun v => !shared v)) :=
  #[Seed0.model,Seed1.model]


private def checkVertices : Nat → Bool :=
  passes models book rows


private def vs17 : List (Fin 17) :=
  []


private def vs16 : List (Fin 17) :=
  16 :: vs17


private def vs15 : List (Fin 17) :=
  15 :: vs16


private def vs14 : List (Fin 17) :=
  14 :: vs15


private def vs13 : List (Fin 17) :=
  13 :: vs14


private def vs12 : List (Fin 17) :=
  12 :: vs13


private def vs11 : List (Fin 17) :=
  11 :: vs12


private def vs10 : List (Fin 17) :=
  10 :: vs11


private def vs9 : List (Fin 17) :=
  9 :: vs10


private def vs8 : List (Fin 17) :=
  8 :: vs9


private def vs7 : List (Fin 17) :=
  7 :: vs8


private def vs6 : List (Fin 17) :=
  6 :: vs7


private def vs5 : List (Fin 17) :=
  5 :: vs6


private def vs4 : List (Fin 17) :=
  4 :: vs5


private def vs3 : List (Fin 17) :=
  3 :: vs4


private def vs2 : List (Fin 17) :=
  2 :: vs3


private def vs1 : List (Fin 17) :=
  1 :: vs2


private def vs0 : List (Fin 17) :=
  0 :: vs1


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk0 : scan checkVertices 127 vs7 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk1 : scan checkVertices 191 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk2 : scan checkVertices 63 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk3 : scan checkVertices 223 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk4 : scan checkVertices 95 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk5 : scan checkVertices 159 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk6 : scan checkVertices 287 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk7 : scan checkVertices 31 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk8 : scan checkVertices 239 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk9 : scan checkVertices 111 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk10 : scan checkVertices 175 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk11 : scan checkVertices 303 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk12 : scan checkVertices 47 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk13 : scan checkVertices 207 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk14 : scan checkVertices 335 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk15 : scan checkVertices 79 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk16 : scan checkVertices 399 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk17 : scan checkVertices 143 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk18 : scan checkVertices 271 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk19 : scan checkVertices 15 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk20 : scan checkVertices 247 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk21 : scan checkVertices 119 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk22 : scan checkVertices 183 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk23 : scan checkVertices 311 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk24 : scan checkVertices 55 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk25 : scan checkVertices 215 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk26 : scan checkVertices 343 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk27 : scan checkVertices 87 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk28 : scan checkVertices 407 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk29 : scan checkVertices 151 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk30 : scan checkVertices 279 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk31 : scan checkVertices 23 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk32 : scan checkVertices 231 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk33 : scan checkVertices 359 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk34 : scan checkVertices 103 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk35 : scan checkVertices 423 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk36 : scan checkVertices 167 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk37 : scan checkVertices 295 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk38 : scan checkVertices 39 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk39 : scan checkVertices 455 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk40 : scan checkVertices 199 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk41 : scan checkVertices 327 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk42 : scan checkVertices 71 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk43 : scan checkVertices 391 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk44 : scan checkVertices 135 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk45 : scan checkVertices 7 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk46 : scan checkVertices 251 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk47 : scan checkVertices 123 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk48 : scan checkVertices 187 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk49 : scan checkVertices 315 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk50 : scan checkVertices 59 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk51 : scan checkVertices 219 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk52 : scan checkVertices 347 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk53 : scan checkVertices 91 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk54 : scan checkVertices 411 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk55 : scan checkVertices 155 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk56 : scan checkVertices 283 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk57 : scan checkVertices 27 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk58 : scan checkVertices 235 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk59 : scan checkVertices 363 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk60 : scan checkVertices 107 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk61 : scan checkVertices 427 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk62 : scan checkVertices 171 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk63 : scan checkVertices 299 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk64 : scan checkVertices 43 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk65 : scan checkVertices 459 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk66 : scan checkVertices 203 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk67 : scan checkVertices 331 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk68 : scan checkVertices 75 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk69 : scan checkVertices 395 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk70 : scan checkVertices 139 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk71 : scan checkVertices 11 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk72 : scan checkVertices 243 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk73 : scan checkVertices 371 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk74 : scan checkVertices 115 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk75 : scan checkVertices 435 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk76 : scan checkVertices 179 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk77 : scan checkVertices 307 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk78 : scan checkVertices 51 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk79 : scan checkVertices 467 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk80 : scan checkVertices 211 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk81 : scan checkVertices 339 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk82 : scan checkVertices 83 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk83 : scan checkVertices 403 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk84 : scan checkVertices 147 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk85 : scan checkVertices 19 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk86 : scan checkVertices 483 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk87 : scan checkVertices 227 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk88 : scan checkVertices 355 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk89 : scan checkVertices 99 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk90 : scan checkVertices 419 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk91 : scan checkVertices 163 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk92 : scan checkVertices 35 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk93 : scan checkVertices 451 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk94 : scan checkVertices 195 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk95 : scan checkVertices 67 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk96 : scan checkVertices 131 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk97 : scan checkVertices 3 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk98 : scan checkVertices 253 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk99 : scan checkVertices 125 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk100 : scan checkVertices 189 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk101 : scan checkVertices 317 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk102 : scan checkVertices 61 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk103 : scan checkVertices 221 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk104 : scan checkVertices 349 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk105 : scan checkVertices 93 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk106 : scan checkVertices 413 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk107 : scan checkVertices 157 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk108 : scan checkVertices 285 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk109 : scan checkVertices 29 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk110 : scan checkVertices 237 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk111 : scan checkVertices 365 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk112 : scan checkVertices 109 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk113 : scan checkVertices 429 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk114 : scan checkVertices 173 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk115 : scan checkVertices 301 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk116 : scan checkVertices 45 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk117 : scan checkVertices 461 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk118 : scan checkVertices 205 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk119 : scan checkVertices 333 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk120 : scan checkVertices 77 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk121 : scan checkVertices 397 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk122 : scan checkVertices 141 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk123 : scan checkVertices 13 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk124 : scan checkVertices 245 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk125 : scan checkVertices 373 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk126 : scan checkVertices 117 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk127 : scan checkVertices 437 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk128 : scan checkVertices 181 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk129 : scan checkVertices 309 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk130 : scan checkVertices 53 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk131 : scan checkVertices 469 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk132 : scan checkVertices 213 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk133 : scan checkVertices 341 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk134 : scan checkVertices 85 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk135 : scan checkVertices 405 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk136 : scan checkVertices 149 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk137 : scan checkVertices 21 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk138 : scan checkVertices 485 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk139 : scan checkVertices 229 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk140 : scan checkVertices 357 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk141 : scan checkVertices 101 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk142 : scan checkVertices 421 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk143 : scan checkVertices 165 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk144 : scan checkVertices 37 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk145 : scan checkVertices 453 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk146 : scan checkVertices 197 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk147 : scan checkVertices 69 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk148 : scan checkVertices 133 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk149 : scan checkVertices 5 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk150 : scan checkVertices 249 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk151 : scan checkVertices 377 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk152 : scan checkVertices 121 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk153 : scan checkVertices 441 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk154 : scan checkVertices 185 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk155 : scan checkVertices 313 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk156 : scan checkVertices 57 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk157 : scan checkVertices 473 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk158 : scan checkVertices 217 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk159 : scan checkVertices 345 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk160 : scan checkVertices 89 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk161 : scan checkVertices 409 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk162 : scan checkVertices 153 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk163 : scan checkVertices 25 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk164 : scan checkVertices 489 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk165 : scan checkVertices 233 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk166 : scan checkVertices 361 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk167 : scan checkVertices 105 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk168 : scan checkVertices 425 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk169 : scan checkVertices 169 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk170 : scan checkVertices 41 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk171 : scan checkVertices 457 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk172 : scan checkVertices 201 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk173 : scan checkVertices 73 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk174 : scan checkVertices 137 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk175 : scan checkVertices 9 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk176 : scan checkVertices 497 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk177 : scan checkVertices 241 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk178 : scan checkVertices 369 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk179 : scan checkVertices 113 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk180 : scan checkVertices 433 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk181 : scan checkVertices 177 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk182 : scan checkVertices 49 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk183 : scan checkVertices 465 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk184 : scan checkVertices 209 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk185 : scan checkVertices 81 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk186 : scan checkVertices 145 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk187 : scan checkVertices 17 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk188 : scan checkVertices 481 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk189 : scan checkVertices 225 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk190 : scan checkVertices 97 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk191 : scan checkVertices 161 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk192 : scan checkVertices 33 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk193 : scan checkVertices 193 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk194 : scan checkVertices 65 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk195 : scan checkVertices 1 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk196 : scan checkVertices 254 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk197 : scan checkVertices 126 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk198 : scan checkVertices 190 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk199 : scan checkVertices 318 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk200 : scan checkVertices 62 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk201 : scan checkVertices 222 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk202 : scan checkVertices 350 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk203 : scan checkVertices 94 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk204 : scan checkVertices 414 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk205 : scan checkVertices 158 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk206 : scan checkVertices 286 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk207 : scan checkVertices 30 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk208 : scan checkVertices 238 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk209 : scan checkVertices 366 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk210 : scan checkVertices 110 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk211 : scan checkVertices 430 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk212 : scan checkVertices 174 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk213 : scan checkVertices 302 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk214 : scan checkVertices 46 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk215 : scan checkVertices 462 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk216 : scan checkVertices 206 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk217 : scan checkVertices 334 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk218 : scan checkVertices 78 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk219 : scan checkVertices 398 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk220 : scan checkVertices 142 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk221 : scan checkVertices 14 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk222 : scan checkVertices 246 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk223 : scan checkVertices 374 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk224 : scan checkVertices 118 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk225 : scan checkVertices 438 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk226 : scan checkVertices 182 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk227 : scan checkVertices 310 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk228 : scan checkVertices 54 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk229 : scan checkVertices 470 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk230 : scan checkVertices 214 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk231 : scan checkVertices 342 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk232 : scan checkVertices 86 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk233 : scan checkVertices 406 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk234 : scan checkVertices 150 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk235 : scan checkVertices 22 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk236 : scan checkVertices 486 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk237 : scan checkVertices 230 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk238 : scan checkVertices 358 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk239 : scan checkVertices 102 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk240 : scan checkVertices 422 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk241 : scan checkVertices 166 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk242 : scan checkVertices 38 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk243 : scan checkVertices 454 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk244 : scan checkVertices 198 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk245 : scan checkVertices 70 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk246 : scan checkVertices 134 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk247 : scan checkVertices 6 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk248 : scan checkVertices 250 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk249 : scan checkVertices 378 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk250 : scan checkVertices 122 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk251 : scan checkVertices 442 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk252 : scan checkVertices 186 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk253 : scan checkVertices 314 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk254 : scan checkVertices 58 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk255 : scan checkVertices 474 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk256 : scan checkVertices 218 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk257 : scan checkVertices 346 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk258 : scan checkVertices 90 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk259 : scan checkVertices 410 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk260 : scan checkVertices 154 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk261 : scan checkVertices 26 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk262 : scan checkVertices 490 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk263 : scan checkVertices 234 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk264 : scan checkVertices 362 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk265 : scan checkVertices 106 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk266 : scan checkVertices 426 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk267 : scan checkVertices 170 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk268 : scan checkVertices 42 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk269 : scan checkVertices 458 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk270 : scan checkVertices 202 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk271 : scan checkVertices 74 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk272 : scan checkVertices 138 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk273 : scan checkVertices 10 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk274 : scan checkVertices 498 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk275 : scan checkVertices 242 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk276 : scan checkVertices 370 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk277 : scan checkVertices 114 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk278 : scan checkVertices 434 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk279 : scan checkVertices 178 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk280 : scan checkVertices 50 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk281 : scan checkVertices 466 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk282 : scan checkVertices 210 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk283 : scan checkVertices 82 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk284 : scan checkVertices 146 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk285 : scan checkVertices 18 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk286 : scan checkVertices 482 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk287 : scan checkVertices 226 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk288 : scan checkVertices 98 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk289 : scan checkVertices 162 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk290 : scan checkVertices 34 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk291 : scan checkVertices 194 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk292 : scan checkVertices 66 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk293 : scan checkVertices 2 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk294 : scan checkVertices 252 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk295 : scan checkVertices 380 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk296 : scan checkVertices 124 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk297 : scan checkVertices 444 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk298 : scan checkVertices 188 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk299 : scan checkVertices 316 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk300 : scan checkVertices 60 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk301 : scan checkVertices 476 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk302 : scan checkVertices 220 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk303 : scan checkVertices 348 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk304 : scan checkVertices 92 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk305 : scan checkVertices 412 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk306 : scan checkVertices 156 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk307 : scan checkVertices 28 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk308 : scan checkVertices 492 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk309 : scan checkVertices 236 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk310 : scan checkVertices 364 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk311 : scan checkVertices 108 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk312 : scan checkVertices 428 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk313 : scan checkVertices 172 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk314 : scan checkVertices 44 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk315 : scan checkVertices 460 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk316 : scan checkVertices 204 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk317 : scan checkVertices 76 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk318 : scan checkVertices 140 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk319 : scan checkVertices 12 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk320 : scan checkVertices 500 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk321 : scan checkVertices 244 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk322 : scan checkVertices 372 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk323 : scan checkVertices 116 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk324 : scan checkVertices 436 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk325 : scan checkVertices 180 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk326 : scan checkVertices 52 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk327 : scan checkVertices 468 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk328 : scan checkVertices 212 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk329 : scan checkVertices 84 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk330 : scan checkVertices 148 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk331 : scan checkVertices 20 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk332 : scan checkVertices 484 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk333 : scan checkVertices 228 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk334 : scan checkVertices 100 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk335 : scan checkVertices 164 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk336 : scan checkVertices 36 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk337 : scan checkVertices 196 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk338 : scan checkVertices 68 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk339 : scan checkVertices 4 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk340 : scan checkVertices 504 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk341 : scan checkVertices 248 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk342 : scan checkVertices 376 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk343 : scan checkVertices 120 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk344 : scan checkVertices 440 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk345 : scan checkVertices 184 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk346 : scan checkVertices 56 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk347 : scan checkVertices 472 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk348 : scan checkVertices 216 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk349 : scan checkVertices 88 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk350 : scan checkVertices 152 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk351 : scan checkVertices 24 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk352 : scan checkVertices 488 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk353 : scan checkVertices 232 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk354 : scan checkVertices 104 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk355 : scan checkVertices 168 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk356 : scan checkVertices 40 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk357 : scan checkVertices 200 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk358 : scan checkVertices 72 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk359 : scan checkVertices 8 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk360 : scan checkVertices 496 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk361 : scan checkVertices 240 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk362 : scan checkVertices 112 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk363 : scan checkVertices 176 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk364 : scan checkVertices 48 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk365 : scan checkVertices 208 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk366 : scan checkVertices 80 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk367 : scan checkVertices 16 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk368 : scan checkVertices 224 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk369 : scan checkVertices 96 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk370 : scan checkVertices 32 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk371 : scan checkVertices 0 vs6 9 = true := by decide +kernel


private theorem allCases : scan checkVertices 0 vs0 9 = true :=
  (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk0 (scan_node chunk1 chunk2)) (scan_node (scan_node chunk3 chunk4) (scan_node chunk5 (scan_node chunk6 chunk7)))) (scan_node (scan_node (scan_node chunk8 chunk9) (scan_node chunk10 (scan_node chunk11 chunk12))) (scan_node (scan_node chunk13 (scan_node chunk14 chunk15)) (scan_node (scan_node chunk16 chunk17) (scan_node chunk18 chunk19))))) (scan_node (scan_node (scan_node (scan_node chunk20 chunk21) (scan_node chunk22 (scan_node chunk23 chunk24))) (scan_node (scan_node chunk25 (scan_node chunk26 chunk27)) (scan_node (scan_node chunk28 chunk29) (scan_node chunk30 chunk31)))) (scan_node (scan_node (scan_node chunk32 (scan_node chunk33 chunk34)) (scan_node (scan_node chunk35 chunk36) (scan_node chunk37 chunk38))) (scan_node (scan_node (scan_node chunk39 chunk40) (scan_node chunk41 chunk42)) (scan_node (scan_node chunk43 chunk44) chunk45))))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk46 chunk47) (scan_node chunk48 (scan_node chunk49 chunk50))) (scan_node (scan_node chunk51 (scan_node chunk52 chunk53)) (scan_node (scan_node chunk54 chunk55) (scan_node chunk56 chunk57)))) (scan_node (scan_node (scan_node chunk58 (scan_node chunk59 chunk60)) (scan_node (scan_node chunk61 chunk62) (scan_node chunk63 chunk64))) (scan_node (scan_node (scan_node chunk65 chunk66) (scan_node chunk67 chunk68)) (scan_node (scan_node chunk69 chunk70) chunk71)))) (scan_node (scan_node (scan_node (scan_node chunk72 (scan_node chunk73 chunk74)) (scan_node (scan_node chunk75 chunk76) (scan_node chunk77 chunk78))) (scan_node (scan_node (scan_node chunk79 chunk80) (scan_node chunk81 chunk82)) (scan_node (scan_node chunk83 chunk84) chunk85))) (scan_node (scan_node (scan_node (scan_node chunk86 chunk87) (scan_node chunk88 chunk89)) (scan_node (scan_node chunk90 chunk91) chunk92)) (scan_node (scan_node (scan_node chunk93 chunk94) chunk95) (scan_node chunk96 chunk97)))))) (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk98 chunk99) (scan_node chunk100 (scan_node chunk101 chunk102))) (scan_node (scan_node chunk103 (scan_node chunk104 chunk105)) (scan_node (scan_node chunk106 chunk107) (scan_node chunk108 chunk109)))) (scan_node (scan_node (scan_node chunk110 (scan_node chunk111 chunk112)) (scan_node (scan_node chunk113 chunk114) (scan_node chunk115 chunk116))) (scan_node (scan_node (scan_node chunk117 chunk118) (scan_node chunk119 chunk120)) (scan_node (scan_node chunk121 chunk122) chunk123)))) (scan_node (scan_node (scan_node (scan_node chunk124 (scan_node chunk125 chunk126)) (scan_node (scan_node chunk127 chunk128) (scan_node chunk129 chunk130))) (scan_node (scan_node (scan_node chunk131 chunk132) (scan_node chunk133 chunk134)) (scan_node (scan_node chunk135 chunk136) chunk137))) (scan_node (scan_node (scan_node (scan_node chunk138 chunk139) (scan_node chunk140 chunk141)) (scan_node (scan_node chunk142 chunk143) chunk144)) (scan_node (scan_node (scan_node chunk145 chunk146) chunk147) (scan_node chunk148 chunk149))))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk150 (scan_node chunk151 chunk152)) (scan_node (scan_node chunk153 chunk154) (scan_node chunk155 chunk156))) (scan_node (scan_node (scan_node chunk157 chunk158) (scan_node chunk159 chunk160)) (scan_node (scan_node chunk161 chunk162) chunk163))) (scan_node (scan_node (scan_node (scan_node chunk164 chunk165) (scan_node chunk166 chunk167)) (scan_node (scan_node chunk168 chunk169) chunk170)) (scan_node (scan_node (scan_node chunk171 chunk172) chunk173) (scan_node chunk174 chunk175)))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk176 chunk177) (scan_node chunk178 chunk179)) (scan_node (scan_node chunk180 chunk181) chunk182)) (scan_node (scan_node (scan_node chunk183 chunk184) chunk185) (scan_node chunk186 chunk187))) (scan_node (scan_node (scan_node (scan_node chunk188 chunk189) chunk190) (scan_node chunk191 chunk192)) (scan_node (scan_node chunk193 chunk194) chunk195)))))) (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk196 chunk197) (scan_node chunk198 (scan_node chunk199 chunk200))) (scan_node (scan_node chunk201 (scan_node chunk202 chunk203)) (scan_node (scan_node chunk204 chunk205) (scan_node chunk206 chunk207)))) (scan_node (scan_node (scan_node chunk208 (scan_node chunk209 chunk210)) (scan_node (scan_node chunk211 chunk212) (scan_node chunk213 chunk214))) (scan_node (scan_node (scan_node chunk215 chunk216) (scan_node chunk217 chunk218)) (scan_node (scan_node chunk219 chunk220) chunk221)))) (scan_node (scan_node (scan_node (scan_node chunk222 (scan_node chunk223 chunk224)) (scan_node (scan_node chunk225 chunk226) (scan_node chunk227 chunk228))) (scan_node (scan_node (scan_node chunk229 chunk230) (scan_node chunk231 chunk232)) (scan_node (scan_node chunk233 chunk234) chunk235))) (scan_node (scan_node (scan_node (scan_node chunk236 chunk237) (scan_node chunk238 chunk239)) (scan_node (scan_node chunk240 chunk241) chunk242)) (scan_node (scan_node (scan_node chunk243 chunk244) chunk245) (scan_node chunk246 chunk247))))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk248 (scan_node chunk249 chunk250)) (scan_node (scan_node chunk251 chunk252) (scan_node chunk253 chunk254))) (scan_node (scan_node (scan_node chunk255 chunk256) (scan_node chunk257 chunk258)) (scan_node (scan_node chunk259 chunk260) chunk261))) (scan_node (scan_node (scan_node (scan_node chunk262 chunk263) (scan_node chunk264 chunk265)) (scan_node (scan_node chunk266 chunk267) chunk268)) (scan_node (scan_node (scan_node chunk269 chunk270) chunk271) (scan_node chunk272 chunk273)))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk274 chunk275) (scan_node chunk276 chunk277)) (scan_node (scan_node chunk278 chunk279) chunk280)) (scan_node (scan_node (scan_node chunk281 chunk282) chunk283) (scan_node chunk284 chunk285))) (scan_node (scan_node (scan_node (scan_node chunk286 chunk287) chunk288) (scan_node chunk289 chunk290)) (scan_node (scan_node chunk291 chunk292) chunk293))))) (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk294 (scan_node chunk295 chunk296)) (scan_node (scan_node chunk297 chunk298) (scan_node chunk299 chunk300))) (scan_node (scan_node (scan_node chunk301 chunk302) (scan_node chunk303 chunk304)) (scan_node (scan_node chunk305 chunk306) chunk307))) (scan_node (scan_node (scan_node (scan_node chunk308 chunk309) (scan_node chunk310 chunk311)) (scan_node (scan_node chunk312 chunk313) chunk314)) (scan_node (scan_node (scan_node chunk315 chunk316) chunk317) (scan_node chunk318 chunk319)))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk320 chunk321) (scan_node chunk322 chunk323)) (scan_node (scan_node chunk324 chunk325) chunk326)) (scan_node (scan_node (scan_node chunk327 chunk328) chunk329) (scan_node chunk330 chunk331))) (scan_node (scan_node (scan_node (scan_node chunk332 chunk333) chunk334) (scan_node chunk335 chunk336)) (scan_node (scan_node chunk337 chunk338) chunk339)))) (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk340 chunk341) (scan_node chunk342 chunk343)) (scan_node (scan_node chunk344 chunk345) chunk346)) (scan_node (scan_node (scan_node chunk347 chunk348) chunk349) (scan_node chunk350 chunk351))) (scan_node (scan_node (scan_node (scan_node chunk352 chunk353) chunk354) (scan_node chunk355 chunk356)) (scan_node (scan_node chunk357 chunk358) chunk359))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk360 chunk361) chunk362) (scan_node chunk363 chunk364)) (scan_node (scan_node chunk365 chunk366) chunk367)) (scan_node (scan_node (scan_node chunk368 chunk369) chunk370) chunk371))))))


private theorem on_set (S : Finset (Fin 17)) (hs : S.card = 9) :
    BoundOn mask (fun v => !shared v) S := by
  apply route_sound models book rows aligned S
  have cover : vs0.toFinset = univ := by decide +kernel
  have sub : S ⊆ vs0.toFinset := by simp [cover]
  have h := scan_sound (f := checkVertices) 0 vs0 S sub (hs.symm ▸ allCases)
  simpa [checkVertices] using h


end Second

namespace Third

private def mask : Nat :=
  165643176072884037276740330230205787895060569518802011647374886495636132


namespace Seed0

private def vertices : Finset (Fin 17) :=
  {0,4,6,8,9,11,14,15,16}


private def measure : Nat → Bool :=
  fun z => (fun v => !onlyFirst v) (measures vertices 117585 z)


private def es31 : List (Sym2 (Fin 17)) :=
  []


private def es30 : List (Sym2 (Fin 17)) :=
  s(15,16) :: es31


private def es29 : List (Sym2 (Fin 17)) :=
  s(14,16) :: es30


private def es28 : List (Sym2 (Fin 17)) :=
  s(14,15) :: es29


private def es27 : List (Sym2 (Fin 17)) :=
  s(11,16) :: es28


private def es26 : List (Sym2 (Fin 17)) :=
  s(11,15) :: es27


private def es25 : List (Sym2 (Fin 17)) :=
  s(11,14) :: es26


private def es24 : List (Sym2 (Fin 17)) :=
  s(9,15) :: es25


private def es23 : List (Sym2 (Fin 17)) :=
  s(9,14) :: es24


private def es22 : List (Sym2 (Fin 17)) :=
  s(9,11) :: es23


private def es21 : List (Sym2 (Fin 17)) :=
  s(8,16) :: es22


private def es20 : List (Sym2 (Fin 17)) :=
  s(8,15) :: es21


private def es19 : List (Sym2 (Fin 17)) :=
  s(8,14) :: es20


private def es18 : List (Sym2 (Fin 17)) :=
  s(8,11) :: es19


private def es17 : List (Sym2 (Fin 17)) :=
  s(8,9) :: es18


private def es16 : List (Sym2 (Fin 17)) :=
  s(6,16) :: es17


private def es15 : List (Sym2 (Fin 17)) :=
  s(6,15) :: es16


private def es14 : List (Sym2 (Fin 17)) :=
  s(6,14) :: es15


private def es13 : List (Sym2 (Fin 17)) :=
  s(6,11) :: es14


private def es12 : List (Sym2 (Fin 17)) :=
  s(6,9) :: es13


private def es11 : List (Sym2 (Fin 17)) :=
  s(6,8) :: es12


private def es10 : List (Sym2 (Fin 17)) :=
  s(4,16) :: es11


private def es9 : List (Sym2 (Fin 17)) :=
  s(4,15) :: es10


private def es8 : List (Sym2 (Fin 17)) :=
  s(4,14) :: es9


private def es7 : List (Sym2 (Fin 17)) :=
  s(4,11) :: es8


private def es6 : List (Sym2 (Fin 17)) :=
  s(4,9) :: es7


private def es5 : List (Sym2 (Fin 17)) :=
  s(4,8) :: es6


private def es4 : List (Sym2 (Fin 17)) :=
  s(4,6) :: es5


private def es3 : List (Sym2 (Fin 17)) :=
  s(0,16) :: es4


private def es2 : List (Sym2 (Fin 17)) :=
  s(0,8) :: es3


private def es1 : List (Sym2 (Fin 17)) :=
  s(0,6) :: es2


private def es0 : List (Sym2 (Fin 17)) :=
  s(0,4) :: es1


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk0 : edgeScan measure 0x2000000800040000000000008000200020001000000004000000010000000000000cb50 es3 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk1 : edgeScan measure 0x2010000800040000000000008000200020000000000004000000010000000000001ca50 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk2 : edgeScan measure 0x2000000800040000000000008000200020000000000044000000410000000000000ca50 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk3 : edgeScan measure 0x2000000800040000000000008000200020010000000004000001010000000000000ca50 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk4 : edgeScan measure 0x2000000800040000000000008000200220000000000004000002010000000000000ca50 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk5 : edgeScan measure 0x2000000800040000000000008000200020000000000004000000010000000000000ca50 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk6 : edgeScan measure 0x2010000800040000000000008000200020001000000000000000010000000000001cb10 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk7 : edgeScan measure 0x2000000800040000000000008000200020001000000040000000410000000000000cb10 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk8 : edgeScan measure 0x2000000800040000000000008000200020011000000000000001010000000000000cb10 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk9 : edgeScan measure 0x2000000800040000000000008000200220001000000000000002010000000000000cb10 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk10 : edgeScan measure 0x2000000800040000000000008000200020001000000000000000010000000000000cb10 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk11 : edgeScan measure 0x2010000800040000000000008000200020000000000040000000410000000000001ca10 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk12 : edgeScan measure 0x2010000800040000000000008000200020010000000000000001010000000000001ca10 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk13 : edgeScan measure 0x2010000800040000000000008000200220000000000000000002010000000000001ca10 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk14 : edgeScan measure 0x2010000800040000000000008000200020000000000000000000010000000000001ca10 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk15 : edgeScan measure 0x2000000800040000000000008000200020010000000040000001410000000000000ca10 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk16 : edgeScan measure 0x2000000800040000000000008000200220000000000040000002410000000000000ca10 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk17 : edgeScan measure 0x2000000800040000000000008000200020000000000040000000410000000000000ca10 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk18 : edgeScan measure 0x2000000800040000000000008000200220010000000000000003010000000000000ca10 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk19 : edgeScan measure 0x2000000800040000000000008000200020010000000000000001010000000000000ca10 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk20 : edgeScan measure 0x2000000800040000000000008000200220000000000000000002010000000000000ca10 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk21 : edgeScan measure 0x2000000800040000000000088000200020000000000000000008010000000000000ca10 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk22 : edgeScan measure 0x2000000800440000000000008000200020000000000000000040010000000000000ca10 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk23 : edgeScan measure 0x2000008800040000000000008000200020000000000000000080010000000000000ca10 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk24 : edgeScan measure 0x2100000800040000000000008000200020000000000000000100010000000000000ca10 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk25 : edgeScan measure 0x2000000800040000000000008000200020040000000400000000010000000000000ca10 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk26 : edgeScan measure 0x2000000800040000000000008000200820000000000800000000010000000000000ca10 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk27 : edgeScan measure 0x2000000800040000000000208000200020000000002000000000010000000000000ca10 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk28 : edgeScan measure 0x2000000801040000000000008000200020000000010000000000010000000000000ca10 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk29 : edgeScan measure 0x2000020800040000000000008000200020000000020000000000010000000000000ca10 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk30 : edgeScan measure 0x2400000800040000000000008000200020000000040000000000010000000000000ca10 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk31 : edgeScan measure 0x2000000800040000000000008000202020200000000000000000010000000000000ca10 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk32 : edgeScan measure 0x2000000800040000000000808000200020800000000000000000010000000000000ca10 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk33 : edgeScan measure 0x2000000804040000000000008000200024000000000000000000010000000000000ca10 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk34 : edgeScan measure 0x2000080800040000000000008000200028000000000000000000010000000000000ca10 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk35 : edgeScan measure 0x3000000800040000000000008000200030000000000000000000010000000000000ca10 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk36 : edgeScan measure 0x2000000800040000000001008000210020000000000000000000010000000000000ca10 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk37 : edgeScan measure 0x2000000808040000000000008000280020000000000000000000010000000000000ca10 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk38 : edgeScan measure 0x2000000800040000000000008000200020000000000000000000010000000000000ca10 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk39 : edgeScan measure 0x2010000800040000000000008000200020001000000004000000000000000000001cb40 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk40 : edgeScan measure 0x2000000800040000000000008000200020001000000044000000400000000000000cb40 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk41 : edgeScan measure 0x2000000800040000000000008000200020011000000004000001000000000000000cb40 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk42 : edgeScan measure 0x2000000800040000000000008000200220001000000004000002000000000000000cb40 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk43 : edgeScan measure 0x2000000800040000000000008000200020001000000004000000000000000000000cb40 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk44 : edgeScan measure 0x2010000800040000000000008000200020000000000044000000400000000000001ca40 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk45 : edgeScan measure 0x2010000800040000000000008000200020010000000004000001000000000000001ca40 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk46 : edgeScan measure 0x2010000800040000000000008000200220000000000004000002000000000000001ca40 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk47 : edgeScan measure 0x2010000800040000000000008000200020000000000004000000000000000000001ca40 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk48 : edgeScan measure 0x2000000800040000000000008000200020010000000044000001400000000000000ca40 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk49 : edgeScan measure 0x2000000800040000000000008000200220000000000044000002400000000000000ca40 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk50 : edgeScan measure 0x2000000800040000000000008000200020000000000044000000400000000000000ca40 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk51 : edgeScan measure 0x2000000800040000000000008000200220010000000004000003000000000000000ca40 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk52 : edgeScan measure 0x2000000800040000000000008000200020010000000004000001000000000000000ca40 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk53 : edgeScan measure 0x2000000800040000000000008000200220000000000004000002000000000000000ca40 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk54 : edgeScan measure 0x2000000800040000000000088000200020000000000004000008000000000000000ca40 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk55 : edgeScan measure 0x2000000800440000000000008000200020000000000004000040000000000000000ca40 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk56 : edgeScan measure 0x2000008800040000000000008000200020000000000004000080000000000000000ca40 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk57 : edgeScan measure 0x2100000800040000000000008000200020000000000004000100000000000000000ca40 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk58 : edgeScan measure 0x2000000800040000000000008000200020040000000404000000000000000000000ca40 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk59 : edgeScan measure 0x2000000800040000000000008000200820000000000804000000000000000000000ca40 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk60 : edgeScan measure 0x2000000800040000000000208000200020000000002004000000000000000000000ca40 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk61 : edgeScan measure 0x2000000801040000000000008000200020000000010004000000000000000000000ca40 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk62 : edgeScan measure 0x2000020800040000000000008000200020000000020004000000000000000000000ca40 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk63 : edgeScan measure 0x2400000800040000000000008000200020000000040004000000000000000000000ca40 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk64 : edgeScan measure 0x2000000800040000000000008000202020200000000004000000000000000000000ca40 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk65 : edgeScan measure 0x2000000800040000000000808000200020800000000004000000000000000000000ca40 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk66 : edgeScan measure 0x2000000804040000000000008000200024000000000004000000000000000000000ca40 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk67 : edgeScan measure 0x2000080800040000000000008000200028000000000004000000000000000000000ca40 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk68 : edgeScan measure 0x3000000800040000000000008000200030000000000004000000000000000000000ca40 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk69 : edgeScan measure 0x2000000800040000000001008000210020000000000004000000000000000000000ca40 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk70 : edgeScan measure 0x2000000808040000000000008000280020000000000004000000000000000000000ca40 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk71 : edgeScan measure 0x2000000800040000000000008000200020000000000004000000000000000000000ca40 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk72 : edgeScan measure 0x2010000800040000000000008000200020001000000040000000400000000000001cb00 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk73 : edgeScan measure 0x2010000800040000000000008000200020011000000000000001000000000000001cb00 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk74 : edgeScan measure 0x2010000800040000000000008000200220001000000000000002000000000000001cb00 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk75 : edgeScan measure 0x2010000800040000000000008000200020001000000000000000000000000000001cb00 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk76 : edgeScan measure 0x2000000800040000000000008000200020011000000040000001400000000000000cb00 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk77 : edgeScan measure 0x2000000800040000000000008000200220001000000040000002400000000000000cb00 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk78 : edgeScan measure 0x2000000800040000000000008000200020001000000040000000400000000000000cb00 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk79 : edgeScan measure 0x2000000800040000000000008000200220011000000000000003000000000000000cb00 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk80 : edgeScan measure 0x2000000800040000000000008000200020011000000000000001000000000000000cb00 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk81 : edgeScan measure 0x2000000800040000000000008000200220001000000000000002000000000000000cb00 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk82 : edgeScan measure 0x2000000800040000000000088000200020001000000000000008000000000000000cb00 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk83 : edgeScan measure 0x2000000800440000000000008000200020001000000000000040000000000000000cb00 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk84 : edgeScan measure 0x2000008800040000000000008000200020001000000000000080000000000000000cb00 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk85 : edgeScan measure 0x2100000800040000000000008000200020001000000000000100000000000000000cb00 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk86 : edgeScan measure 0x2000000800040000000000008000200020041000000400000000000000000000000cb00 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk87 : edgeScan measure 0x2000000800040000000000008000200820001000000800000000000000000000000cb00 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk88 : edgeScan measure 0x2000000800040000000000208000200020001000002000000000000000000000000cb00 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk89 : edgeScan measure 0x2000000801040000000000008000200020001000010000000000000000000000000cb00 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk90 : edgeScan measure 0x2000020800040000000000008000200020001000020000000000000000000000000cb00 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk91 : edgeScan measure 0x2400000800040000000000008000200020001000040000000000000000000000000cb00 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk92 : edgeScan measure 0x2000000800040000000000008000202020201000000000000000000000000000000cb00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk93 : edgeScan measure 0x2000000800040000000000808000200020801000000000000000000000000000000cb00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk94 : edgeScan measure 0x2000000804040000000000008000200024001000000000000000000000000000000cb00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk95 : edgeScan measure 0x2000080800040000000000008000200028001000000000000000000000000000000cb00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk96 : edgeScan measure 0x3000000800040000000000008000200030001000000000000000000000000000000cb00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk97 : edgeScan measure 0x2000000800040000000001008000210020001000000000000000000000000000000cb00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk98 : edgeScan measure 0x2000000808040000000000008000280020001000000000000000000000000000000cb00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk99 : edgeScan measure 0x2000000800040000000000008000200020001000000000000000000000000000000cb00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk100 : edgeScan measure 0x2010000800040000000000008000200020010000000040000001400000000000001ca00 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk101 : edgeScan measure 0x2010000800040000000000008000200220000000000040000002400000000000001ca00 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk102 : edgeScan measure 0x2010000800040000000000008000200020000000000040000000400000000000001ca00 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk103 : edgeScan measure 0x2010000800040000000000008000200220010000000000000003000000000000001ca00 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk104 : edgeScan measure 0x2010000800040000000000008000200020010000000000000001000000000000001ca00 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk105 : edgeScan measure 0x2010000800040000000000008000200220000000000000000002000000000000001ca00 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk106 : edgeScan measure 0x2010000800040000000000088000200020000000000000000008000000000000001ca00 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk107 : edgeScan measure 0x2010000800440000000000008000200020000000000000000040000000000000001ca00 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk108 : edgeScan measure 0x2010008800040000000000008000200020000000000000000080000000000000001ca00 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk109 : edgeScan measure 0x2110000800040000000000008000200020000000000000000100000000000000001ca00 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk110 : edgeScan measure 0x2010000800040000000000008000200020040000000400000000000000000000001ca00 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk111 : edgeScan measure 0x2010000800040000000000008000200820000000000800000000000000000000001ca00 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk112 : edgeScan measure 0x2010000800040000000000208000200020000000002000000000000000000000001ca00 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk113 : edgeScan measure 0x2010000801040000000000008000200020000000010000000000000000000000001ca00 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk114 : edgeScan measure 0x2010020800040000000000008000200020000000020000000000000000000000001ca00 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk115 : edgeScan measure 0x2410000800040000000000008000200020000000040000000000000000000000001ca00 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk116 : edgeScan measure 0x2010000800040000000000008000202020200000000000000000000000000000001ca00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk117 : edgeScan measure 0x2010000800040000000000808000200020800000000000000000000000000000001ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk118 : edgeScan measure 0x2010000804040000000000008000200024000000000000000000000000000000001ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk119 : edgeScan measure 0x2010080800040000000000008000200028000000000000000000000000000000001ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk120 : edgeScan measure 0x3010000800040000000000008000200030000000000000000000000000000000001ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk121 : edgeScan measure 0x2010000800040000000001008000210020000000000000000000000000000000001ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk122 : edgeScan measure 0x2010000808040000000000008000280020000000000000000000000000000000001ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk123 : edgeScan measure 0x2010000800040000000000008000200020000000000000000000000000000000001ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk124 : edgeScan measure 0x2000000800040000000000008000200220010000000040000003400000000000000ca00 es7 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk125 : edgeScan measure 0x2000000800040000000000008000200020010000000040000001400000000000000ca00 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk126 : edgeScan measure 0x2000000800040000000000008000200220000000000040000002400000000000000ca00 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk127 : edgeScan measure 0x2000000800040000000000088000200020000000000040000008400000000000000ca00 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk128 : edgeScan measure 0x2000000800440000000000008000200020000000000040000040400000000000000ca00 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk129 : edgeScan measure 0x2000008800040000000000008000200020000000000040000080400000000000000ca00 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk130 : edgeScan measure 0x2100000800040000000000008000200020000000000040000100400000000000000ca00 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk131 : edgeScan measure 0x2000000800040000000000008000200020040000000440000000400000000000000ca00 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk132 : edgeScan measure 0x2000000800040000000000008000200820000000000840000000400000000000000ca00 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk133 : edgeScan measure 0x2000000800040000000000208000200020000000002040000000400000000000000ca00 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk134 : edgeScan measure 0x2000000801040000000000008000200020000000010040000000400000000000000ca00 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk135 : edgeScan measure 0x2000020800040000000000008000200020000000020040000000400000000000000ca00 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk136 : edgeScan measure 0x2400000800040000000000008000200020000000040040000000400000000000000ca00 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk137 : edgeScan measure 0x2000000800040000000000008000202020200000000040000000400000000000000ca00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk138 : edgeScan measure 0x2000000800040000000000808000200020800000000040000000400000000000000ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk139 : edgeScan measure 0x2000000804040000000000008000200024000000000040000000400000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk140 : edgeScan measure 0x2000080800040000000000008000200028000000000040000000400000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk141 : edgeScan measure 0x3000000800040000000000008000200030000000000040000000400000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk142 : edgeScan measure 0x2000000800040000000001008000210020000000000040000000400000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk143 : edgeScan measure 0x2000000808040000000000008000280020000000000040000000400000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk144 : edgeScan measure 0x2000000800040000000000008000200020000000000040000000400000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk145 : edgeScan measure 0x2000000800040000000000008000200220010000000000000003000000000000000ca00 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk146 : edgeScan measure 0x2000000800040000000000088000200020010000000000000009000000000000000ca00 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk147 : edgeScan measure 0x2000000800440000000000008000200020010000000000000041000000000000000ca00 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk148 : edgeScan measure 0x2000008800040000000000008000200020010000000000000081000000000000000ca00 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk149 : edgeScan measure 0x2100000800040000000000008000200020010000000000000101000000000000000ca00 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk150 : edgeScan measure 0x2000000800040000000000008000200020050000000400000001000000000000000ca00 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk151 : edgeScan measure 0x2000000800040000000000008000200820010000000800000001000000000000000ca00 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk152 : edgeScan measure 0x2000000800040000000000208000200020010000002000000001000000000000000ca00 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk153 : edgeScan measure 0x2000000801040000000000008000200020010000010000000001000000000000000ca00 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk154 : edgeScan measure 0x2000020800040000000000008000200020010000020000000001000000000000000ca00 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk155 : edgeScan measure 0x2400000800040000000000008000200020010000040000000001000000000000000ca00 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk156 : edgeScan measure 0x2000000800040000000000008000202020210000000000000001000000000000000ca00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk157 : edgeScan measure 0x2000000800040000000000808000200020810000000000000001000000000000000ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk158 : edgeScan measure 0x2000000804040000000000008000200024010000000000000001000000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk159 : edgeScan measure 0x2000080800040000000000008000200028010000000000000001000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk160 : edgeScan measure 0x3000000800040000000000008000200030010000000000000001000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk161 : edgeScan measure 0x2000000800040000000001008000210020010000000000000001000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk162 : edgeScan measure 0x2000000808040000000000008000280020010000000000000001000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk163 : edgeScan measure 0x2000000800040000000000008000200020010000000000000001000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk164 : edgeScan measure 0x200000080004000000000008800020022000000000000000000a000000000000000ca00 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk165 : edgeScan measure 0x2000000800440000000000008000200220000000000000000042000000000000000ca00 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk166 : edgeScan measure 0x2000008800040000000000008000200220000000000000000082000000000000000ca00 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk167 : edgeScan measure 0x2100000800040000000000008000200220000000000000000102000000000000000ca00 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk168 : edgeScan measure 0x2000000800040000000000008000200220040000000400000002000000000000000ca00 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk169 : edgeScan measure 0x2000000800040000000000008000200a20000000000800000002000000000000000ca00 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk170 : edgeScan measure 0x2000000800040000000000208000200220000000002000000002000000000000000ca00 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk171 : edgeScan measure 0x2000000801040000000000008000200220000000010000000002000000000000000ca00 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk172 : edgeScan measure 0x2000020800040000000000008000200220000000020000000002000000000000000ca00 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk173 : edgeScan measure 0x2400000800040000000000008000200220000000040000000002000000000000000ca00 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk174 : edgeScan measure 0x2000000800040000000000008000202220200000000000000002000000000000000ca00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk175 : edgeScan measure 0x2000000800040000000000808000200220800000000000000002000000000000000ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk176 : edgeScan measure 0x2000000804040000000000008000200224000000000000000002000000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk177 : edgeScan measure 0x2000080800040000000000008000200228000000000000000002000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk178 : edgeScan measure 0x3000000800040000000000008000200230000000000000000002000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk179 : edgeScan measure 0x2000000800040000000001008000210220000000000000000002000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk180 : edgeScan measure 0x2000000808040000000000008000280220000000000000000002000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk181 : edgeScan measure 0x2000000800040000000000008000200220000000000000000002000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk182 : edgeScan measure 0x2000000800440000000000088000200020000000000000000048000000000000000ca00 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk183 : edgeScan measure 0x2000008800040000000000088000200020000000000000000088000000000000000ca00 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk184 : edgeScan measure 0x2100000800040000000000088000200020000000000000000108000000000000000ca00 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk185 : edgeScan measure 0x2000000800040000000000088000200020040000000400000008000000000000000ca00 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk186 : edgeScan measure 0x2000000800040000000000088000200820000000000800000008000000000000000ca00 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk187 : edgeScan measure 0x2000000800040000000000288000200020000000002000000008000000000000000ca00 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk188 : edgeScan measure 0x2000000801040000000000088000200020000000010000000008000000000000000ca00 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk189 : edgeScan measure 0x2000020800040000000000088000200020000000020000000008000000000000000ca00 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk190 : edgeScan measure 0x2400000800040000000000088000200020000000040000000008000000000000000ca00 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk191 : edgeScan measure 0x2000000800040000000000088000202020200000000000000008000000000000000ca00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk192 : edgeScan measure 0x2000000800040000000000888000200020800000000000000008000000000000000ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk193 : edgeScan measure 0x2000000804040000000000088000200024000000000000000008000000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk194 : edgeScan measure 0x2000080800040000000000088000200028000000000000000008000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk195 : edgeScan measure 0x3000000800040000000000088000200030000000000000000008000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk196 : edgeScan measure 0x2000000800040000000001088000210020000000000000000008000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk197 : edgeScan measure 0x2000000808040000000000088000280020000000000000000008000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk198 : edgeScan measure 0x2000000800040000000000088000200020000000000000000008000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk199 : edgeScan measure 0x20000088004400000000000080002000200000000000000000c0000000000000000ca00 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk200 : edgeScan measure 0x2100000800440000000000008000200020000000000000000140000000000000000ca00 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk201 : edgeScan measure 0x2000000800440000000000008000200020040000000400000040000000000000000ca00 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk202 : edgeScan measure 0x2000000800440000000000008000200820000000000800000040000000000000000ca00 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk203 : edgeScan measure 0x2000000800440000000000208000200020000000002000000040000000000000000ca00 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk204 : edgeScan measure 0x2000000801440000000000008000200020000000010000000040000000000000000ca00 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk205 : edgeScan measure 0x2000020800440000000000008000200020000000020000000040000000000000000ca00 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk206 : edgeScan measure 0x2400000800440000000000008000200020000000040000000040000000000000000ca00 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk207 : edgeScan measure 0x2000000800440000000000008000202020200000000000000040000000000000000ca00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk208 : edgeScan measure 0x2000000800440000000000808000200020800000000000000040000000000000000ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk209 : edgeScan measure 0x2000000804440000000000008000200024000000000000000040000000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk210 : edgeScan measure 0x2000080800440000000000008000200028000000000000000040000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk211 : edgeScan measure 0x3000000800440000000000008000200030000000000000000040000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk212 : edgeScan measure 0x2000000800440000000001008000210020000000000000000040000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk213 : edgeScan measure 0x2000000808440000000000008000280020000000000000000040000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk214 : edgeScan measure 0x2000000800440000000000008000200020000000000000000040000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk215 : edgeScan measure 0x2100008800040000000000008000200020000000000000000180000000000000000ca00 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk216 : edgeScan measure 0x2000008800040000000000008000200020040000000400000080000000000000000ca00 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk217 : edgeScan measure 0x2000008800040000000000008000200820000000000800000080000000000000000ca00 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk218 : edgeScan measure 0x2000008800040000000000208000200020000000002000000080000000000000000ca00 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk219 : edgeScan measure 0x2000008801040000000000008000200020000000010000000080000000000000000ca00 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk220 : edgeScan measure 0x2000028800040000000000008000200020000000020000000080000000000000000ca00 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk221 : edgeScan measure 0x2400008800040000000000008000200020000000040000000080000000000000000ca00 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk222 : edgeScan measure 0x2000008800040000000000008000202020200000000000000080000000000000000ca00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk223 : edgeScan measure 0x2000008800040000000000808000200020800000000000000080000000000000000ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk224 : edgeScan measure 0x2000008804040000000000008000200024000000000000000080000000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk225 : edgeScan measure 0x2000088800040000000000008000200028000000000000000080000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk226 : edgeScan measure 0x3000008800040000000000008000200030000000000000000080000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk227 : edgeScan measure 0x2000008800040000000001008000210020000000000000000080000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk228 : edgeScan measure 0x2000008808040000000000008000280020000000000000000080000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk229 : edgeScan measure 0x2000008800040000000000008000200020000000000000000080000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk230 : edgeScan measure 0x2100000800040000000000008000200020040000000400000100000000000000000ca00 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk231 : edgeScan measure 0x2100000800040000000000008000200820000000000800000100000000000000000ca00 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk232 : edgeScan measure 0x2100000800040000000000208000200020000000002000000100000000000000000ca00 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk233 : edgeScan measure 0x2100000801040000000000008000200020000000010000000100000000000000000ca00 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk234 : edgeScan measure 0x2100020800040000000000008000200020000000020000000100000000000000000ca00 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk235 : edgeScan measure 0x2500000800040000000000008000200020000000040000000100000000000000000ca00 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk236 : edgeScan measure 0x2100000800040000000000008000202020200000000000000100000000000000000ca00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk237 : edgeScan measure 0x2100000800040000000000808000200020800000000000000100000000000000000ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk238 : edgeScan measure 0x2100000804040000000000008000200024000000000000000100000000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk239 : edgeScan measure 0x2100080800040000000000008000200028000000000000000100000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk240 : edgeScan measure 0x3100000800040000000000008000200030000000000000000100000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk241 : edgeScan measure 0x2100000800040000000001008000210020000000000000000100000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk242 : edgeScan measure 0x2100000808040000000000008000280020000000000000000100000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk243 : edgeScan measure 0x2100000800040000000000008000200020000000000000000100000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk244 : edgeScan measure 0x2000000800040000000000008000200820040000000c00000000000000000000000ca00 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk245 : edgeScan measure 0x2000000800040000000000208000200020040000002400000000000000000000000ca00 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk246 : edgeScan measure 0x2000000801040000000000008000200020040000010400000000000000000000000ca00 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk247 : edgeScan measure 0x2000020800040000000000008000200020040000020400000000000000000000000ca00 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk248 : edgeScan measure 0x2400000800040000000000008000200020040000040400000000000000000000000ca00 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk249 : edgeScan measure 0x2000000800040000000000008000202020240000000400000000000000000000000ca00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk250 : edgeScan measure 0x2000000800040000000000808000200020840000000400000000000000000000000ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk251 : edgeScan measure 0x2000000804040000000000008000200024040000000400000000000000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk252 : edgeScan measure 0x2000080800040000000000008000200028040000000400000000000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk253 : edgeScan measure 0x3000000800040000000000008000200030040000000400000000000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk254 : edgeScan measure 0x2000000800040000000001008000210020040000000400000000000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk255 : edgeScan measure 0x2000000808040000000000008000280020040000000400000000000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk256 : edgeScan measure 0x2000000800040000000000008000200020040000000400000000000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk257 : edgeScan measure 0x2000000800040000000000208000200820000000002800000000000000000000000ca00 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk258 : edgeScan measure 0x2000000801040000000000008000200820000000010800000000000000000000000ca00 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk259 : edgeScan measure 0x2000020800040000000000008000200820000000020800000000000000000000000ca00 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk260 : edgeScan measure 0x2400000800040000000000008000200820000000040800000000000000000000000ca00 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk261 : edgeScan measure 0x2000000800040000000000008000202820200000000800000000000000000000000ca00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk262 : edgeScan measure 0x2000000800040000000000808000200820800000000800000000000000000000000ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk263 : edgeScan measure 0x2000000804040000000000008000200824000000000800000000000000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk264 : edgeScan measure 0x2000080800040000000000008000200828000000000800000000000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk265 : edgeScan measure 0x3000000800040000000000008000200830000000000800000000000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk266 : edgeScan measure 0x2000000800040000000001008000210820000000000800000000000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk267 : edgeScan measure 0x2000000808040000000000008000280820000000000800000000000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk268 : edgeScan measure 0x2000000800040000000000008000200820000000000800000000000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk269 : edgeScan measure 0x2000000801040000000000208000200020000000012000000000000000000000000ca00 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk270 : edgeScan measure 0x2000020800040000000000208000200020000000022000000000000000000000000ca00 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk271 : edgeScan measure 0x2400000800040000000000208000200020000000042000000000000000000000000ca00 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk272 : edgeScan measure 0x2000000800040000000000208000202020200000002000000000000000000000000ca00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk273 : edgeScan measure 0x2000000800040000000000a08000200020800000002000000000000000000000000ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk274 : edgeScan measure 0x2000000804040000000000208000200024000000002000000000000000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk275 : edgeScan measure 0x2000080800040000000000208000200028000000002000000000000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk276 : edgeScan measure 0x3000000800040000000000208000200030000000002000000000000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk277 : edgeScan measure 0x2000000800040000000001208000210020000000002000000000000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk278 : edgeScan measure 0x2000000808040000000000208000280020000000002000000000000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk279 : edgeScan measure 0x2000000800040000000000208000200020000000002000000000000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk280 : edgeScan measure 0x2000020801040000000000008000200020000000030000000000000000000000000ca00 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk281 : edgeScan measure 0x2400000801040000000000008000200020000000050000000000000000000000000ca00 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk282 : edgeScan measure 0x2000000801040000000000008000202020200000010000000000000000000000000ca00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk283 : edgeScan measure 0x2000000801040000000000808000200020800000010000000000000000000000000ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk284 : edgeScan measure 0x2000000805040000000000008000200024000000010000000000000000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk285 : edgeScan measure 0x2000080801040000000000008000200028000000010000000000000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk286 : edgeScan measure 0x3000000801040000000000008000200030000000010000000000000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk287 : edgeScan measure 0x2000000801040000000001008000210020000000010000000000000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk288 : edgeScan measure 0x2000000809040000000000008000280020000000010000000000000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk289 : edgeScan measure 0x2000000801040000000000008000200020000000010000000000000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk290 : edgeScan measure 0x2400020800040000000000008000200020000000060000000000000000000000000ca00 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk291 : edgeScan measure 0x2000020800040000000000008000202020200000020000000000000000000000000ca00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk292 : edgeScan measure 0x2000020800040000000000808000200020800000020000000000000000000000000ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk293 : edgeScan measure 0x2000020804040000000000008000200024000000020000000000000000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk294 : edgeScan measure 0x20000a0800040000000000008000200028000000020000000000000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk295 : edgeScan measure 0x3000020800040000000000008000200030000000020000000000000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk296 : edgeScan measure 0x2000020800040000000001008000210020000000020000000000000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk297 : edgeScan measure 0x2000020808040000000000008000280020000000020000000000000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk298 : edgeScan measure 0x2000020800040000000000008000200020000000020000000000000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk299 : edgeScan measure 0x2400000800040000000000008000202020200000040000000000000000000000000ca00 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk300 : edgeScan measure 0x2400000800040000000000808000200020800000040000000000000000000000000ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk301 : edgeScan measure 0x2400000804040000000000008000200024000000040000000000000000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk302 : edgeScan measure 0x2400080800040000000000008000200028000000040000000000000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk303 : edgeScan measure 0x3400000800040000000000008000200030000000040000000000000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk304 : edgeScan measure 0x2400000800040000000001008000210020000000040000000000000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk305 : edgeScan measure 0x2400000808040000000000008000280020000000040000000000000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk306 : edgeScan measure 0x2400000800040000000000008000200020000000040000000000000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk307 : edgeScan measure 0x2000000800040000000000808000202020a00000000000000000000000000000000ca00 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk308 : edgeScan measure 0x2000000804040000000000008000202024200000000000000000000000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk309 : edgeScan measure 0x2000080800040000000000008000202028200000000000000000000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk310 : edgeScan measure 0x3000000800040000000000008000202030200000000000000000000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk311 : edgeScan measure 0x2000000800040000000001008000212020200000000000000000000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk312 : edgeScan measure 0x2000000808040000000000008000282020200000000000000000000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk313 : edgeScan measure 0x2000000800040000000000008000202020200000000000000000000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk314 : edgeScan measure 0x2000000804040000000000808000200024800000000000000000000000000000000ca00 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk315 : edgeScan measure 0x2000080800040000000000808000200028800000000000000000000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk316 : edgeScan measure 0x3000000800040000000000808000200030800000000000000000000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk317 : edgeScan measure 0x2000000800040000000001808000210020800000000000000000000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk318 : edgeScan measure 0x2000000808040000000000808000280020800000000000000000000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk319 : edgeScan measure 0x2000000800040000000000808000200020800000000000000000000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk320 : edgeScan measure 0x200008080404000000000000800020002c000000000000000000000000000000000ca00 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk321 : edgeScan measure 0x3000000804040000000000008000200034000000000000000000000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk322 : edgeScan measure 0x2000000804040000000001008000210024000000000000000000000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk323 : edgeScan measure 0x200000080c040000000000008000280024000000000000000000000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk324 : edgeScan measure 0x2000000804040000000000008000200024000000000000000000000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk325 : edgeScan measure 0x3000080800040000000000008000200038000000000000000000000000000000000ca00 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk326 : edgeScan measure 0x2000080800040000000001008000210028000000000000000000000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk327 : edgeScan measure 0x2000080808040000000000008000280028000000000000000000000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk328 : edgeScan measure 0x2000080800040000000000008000200028000000000000000000000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk329 : edgeScan measure 0x3000000800040000000001008000210030000000000000000000000000000000000ca00 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk330 : edgeScan measure 0x3000000808040000000000008000280030000000000000000000000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk331 : edgeScan measure 0x3000000800040000000000008000200030000000000000000000000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk332 : edgeScan measure 0x2000000808040000000001008000290020000000000000000000000000000000000ca00 es24 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk333 : edgeScan measure 0x2000000800040000000001008000210020000000000000000000000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk334 : edgeScan measure 0x2000000808040000000000008000280020000000000000000000000000000000000ca00 es24 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk335 : edgeScan measure 0x2000100800040000000000008000300020000000000000000000000000000000000ca00 es25 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk336 : edgeScan measure 0x2000000800040000000000008000200020000000000000000000000000000000000ca00 es25 3 = true := by decide +kernel


private theorem allCases : edgeScan measure 0x2000000800040000000000008000200020000000000000000000000000000000000ca00 es0 3 = true :=
  (edgeNode (edgeNode (edgeNode chunk0 (edgeNode chunk1 (edgeNode chunk2 (edgeNode chunk3 (edgeNode chunk4 chunk5))))) (edgeNode (edgeNode chunk6 (edgeNode chunk7 (edgeNode chunk8 (edgeNode chunk9 chunk10)))) (edgeNode (edgeNode chunk11 (edgeNode chunk12 (edgeNode chunk13 chunk14))) (edgeNode (edgeNode chunk15 (edgeNode chunk16 chunk17)) (edgeNode (edgeNode chunk18 chunk19) (edgeNode chunk20 (edgeNode chunk21 (edgeNode chunk22 (edgeNode chunk23 (edgeNode chunk24 (edgeNode chunk25 (edgeNode chunk26 (edgeNode chunk27 (edgeNode chunk28 (edgeNode chunk29 (edgeNode chunk30 (edgeNode chunk31 (edgeNode chunk32 (edgeNode chunk33 (edgeNode chunk34 (edgeNode chunk35 (edgeNode chunk36 (edgeNode chunk37 chunk38))))))))))))))))))))))) (edgeNode (edgeNode (edgeNode chunk39 (edgeNode chunk40 (edgeNode chunk41 (edgeNode chunk42 chunk43)))) (edgeNode (edgeNode chunk44 (edgeNode chunk45 (edgeNode chunk46 chunk47))) (edgeNode (edgeNode chunk48 (edgeNode chunk49 chunk50)) (edgeNode (edgeNode chunk51 chunk52) (edgeNode chunk53 (edgeNode chunk54 (edgeNode chunk55 (edgeNode chunk56 (edgeNode chunk57 (edgeNode chunk58 (edgeNode chunk59 (edgeNode chunk60 (edgeNode chunk61 (edgeNode chunk62 (edgeNode chunk63 (edgeNode chunk64 (edgeNode chunk65 (edgeNode chunk66 (edgeNode chunk67 (edgeNode chunk68 (edgeNode chunk69 (edgeNode chunk70 chunk71)))))))))))))))))))))) (edgeNode (edgeNode (edgeNode chunk72 (edgeNode chunk73 (edgeNode chunk74 chunk75))) (edgeNode (edgeNode chunk76 (edgeNode chunk77 chunk78)) (edgeNode (edgeNode chunk79 chunk80) (edgeNode chunk81 (edgeNode chunk82 (edgeNode chunk83 (edgeNode chunk84 (edgeNode chunk85 (edgeNode chunk86 (edgeNode chunk87 (edgeNode chunk88 (edgeNode chunk89 (edgeNode chunk90 (edgeNode chunk91 (edgeNode chunk92 (edgeNode chunk93 (edgeNode chunk94 (edgeNode chunk95 (edgeNode chunk96 (edgeNode chunk97 (edgeNode chunk98 chunk99))))))))))))))))))))) (edgeNode (edgeNode (edgeNode chunk100 (edgeNode chunk101 chunk102)) (edgeNode (edgeNode chunk103 chunk104) (edgeNode chunk105 (edgeNode chunk106 (edgeNode chunk107 (edgeNode chunk108 (edgeNode chunk109 (edgeNode chunk110 (edgeNode chunk111 (edgeNode chunk112 (edgeNode chunk113 (edgeNode chunk114 (edgeNode chunk115 (edgeNode chunk116 (edgeNode chunk117 (edgeNode chunk118 (edgeNode chunk119 (edgeNode chunk120 (edgeNode chunk121 (edgeNode chunk122 chunk123)))))))))))))))))))) (edgeNode (edgeNode (edgeNode chunk124 chunk125) (edgeNode chunk126 (edgeNode chunk127 (edgeNode chunk128 (edgeNode chunk129 (edgeNode chunk130 (edgeNode chunk131 (edgeNode chunk132 (edgeNode chunk133 (edgeNode chunk134 (edgeNode chunk135 (edgeNode chunk136 (edgeNode chunk137 (edgeNode chunk138 (edgeNode chunk139 (edgeNode chunk140 (edgeNode chunk141 (edgeNode chunk142 (edgeNode chunk143 chunk144))))))))))))))))))) (edgeNode (edgeNode chunk145 (edgeNode chunk146 (edgeNode chunk147 (edgeNode chunk148 (edgeNode chunk149 (edgeNode chunk150 (edgeNode chunk151 (edgeNode chunk152 (edgeNode chunk153 (edgeNode chunk154 (edgeNode chunk155 (edgeNode chunk156 (edgeNode chunk157 (edgeNode chunk158 (edgeNode chunk159 (edgeNode chunk160 (edgeNode chunk161 (edgeNode chunk162 chunk163)))))))))))))))))) (edgeNode (edgeNode chunk164 (edgeNode chunk165 (edgeNode chunk166 (edgeNode chunk167 (edgeNode chunk168 (edgeNode chunk169 (edgeNode chunk170 (edgeNode chunk171 (edgeNode chunk172 (edgeNode chunk173 (edgeNode chunk174 (edgeNode chunk175 (edgeNode chunk176 (edgeNode chunk177 (edgeNode chunk178 (edgeNode chunk179 (edgeNode chunk180 chunk181))))))))))))))))) (edgeNode (edgeNode chunk182 (edgeNode chunk183 (edgeNode chunk184 (edgeNode chunk185 (edgeNode chunk186 (edgeNode chunk187 (edgeNode chunk188 (edgeNode chunk189 (edgeNode chunk190 (edgeNode chunk191 (edgeNode chunk192 (edgeNode chunk193 (edgeNode chunk194 (edgeNode chunk195 (edgeNode chunk196 (edgeNode chunk197 chunk198)))))))))))))))) (edgeNode (edgeNode chunk199 (edgeNode chunk200 (edgeNode chunk201 (edgeNode chunk202 (edgeNode chunk203 (edgeNode chunk204 (edgeNode chunk205 (edgeNode chunk206 (edgeNode chunk207 (edgeNode chunk208 (edgeNode chunk209 (edgeNode chunk210 (edgeNode chunk211 (edgeNode chunk212 (edgeNode chunk213 chunk214))))))))))))))) (edgeNode (edgeNode chunk215 (edgeNode chunk216 (edgeNode chunk217 (edgeNode chunk218 (edgeNode chunk219 (edgeNode chunk220 (edgeNode chunk221 (edgeNode chunk222 (edgeNode chunk223 (edgeNode chunk224 (edgeNode chunk225 (edgeNode chunk226 (edgeNode chunk227 (edgeNode chunk228 chunk229)))))))))))))) (edgeNode (edgeNode chunk230 (edgeNode chunk231 (edgeNode chunk232 (edgeNode chunk233 (edgeNode chunk234 (edgeNode chunk235 (edgeNode chunk236 (edgeNode chunk237 (edgeNode chunk238 (edgeNode chunk239 (edgeNode chunk240 (edgeNode chunk241 (edgeNode chunk242 chunk243))))))))))))) (edgeNode (edgeNode chunk244 (edgeNode chunk245 (edgeNode chunk246 (edgeNode chunk247 (edgeNode chunk248 (edgeNode chunk249 (edgeNode chunk250 (edgeNode chunk251 (edgeNode chunk252 (edgeNode chunk253 (edgeNode chunk254 (edgeNode chunk255 chunk256)))))))))))) (edgeNode (edgeNode chunk257 (edgeNode chunk258 (edgeNode chunk259 (edgeNode chunk260 (edgeNode chunk261 (edgeNode chunk262 (edgeNode chunk263 (edgeNode chunk264 (edgeNode chunk265 (edgeNode chunk266 (edgeNode chunk267 chunk268))))))))))) (edgeNode (edgeNode chunk269 (edgeNode chunk270 (edgeNode chunk271 (edgeNode chunk272 (edgeNode chunk273 (edgeNode chunk274 (edgeNode chunk275 (edgeNode chunk276 (edgeNode chunk277 (edgeNode chunk278 chunk279)))))))))) (edgeNode (edgeNode chunk280 (edgeNode chunk281 (edgeNode chunk282 (edgeNode chunk283 (edgeNode chunk284 (edgeNode chunk285 (edgeNode chunk286 (edgeNode chunk287 (edgeNode chunk288 chunk289))))))))) (edgeNode (edgeNode chunk290 (edgeNode chunk291 (edgeNode chunk292 (edgeNode chunk293 (edgeNode chunk294 (edgeNode chunk295 (edgeNode chunk296 (edgeNode chunk297 chunk298)))))))) (edgeNode (edgeNode chunk299 (edgeNode chunk300 (edgeNode chunk301 (edgeNode chunk302 (edgeNode chunk303 (edgeNode chunk304 (edgeNode chunk305 chunk306))))))) (edgeNode (edgeNode chunk307 (edgeNode chunk308 (edgeNode chunk309 (edgeNode chunk310 (edgeNode chunk311 (edgeNode chunk312 chunk313)))))) (edgeNode (edgeNode chunk314 (edgeNode chunk315 (edgeNode chunk316 (edgeNode chunk317 (edgeNode chunk318 chunk319))))) (edgeNode (edgeNode chunk320 (edgeNode chunk321 (edgeNode chunk322 (edgeNode chunk323 chunk324)))) (edgeNode (edgeNode chunk325 (edgeNode chunk326 (edgeNode chunk327 chunk328))) (edgeNode (edgeNode chunk329 (edgeNode chunk330 chunk331)) (edgeNode (edgeNode chunk332 chunk333) (edgeNode chunk334 (edgeNode chunk335 chunk336)))))))))))))))))))))))))


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private def model : Model mask (fun v => !onlyFirst v) :=
  ⟨vertices,117585,by decide +kernel,
    model_bound es0 117585 0x2000000800040000000000008000200020000000000000000000000000000000000ca00 3
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) allCases⟩


end Seed0

namespace Seed1

private def vertices : Finset (Fin 17) :=
  {0,3,4,6,8,10,12,13,16}


private def measure : Nat → Bool :=
  fun z => (fun v => !onlyFirst v) (measures vertices 79193 z)


private def es30 : List (Sym2 (Fin 17)) :=
  []


private def es29 : List (Sym2 (Fin 17)) :=
  s(13,16) :: es30


private def es28 : List (Sym2 (Fin 17)) :=
  s(12,16) :: es29


private def es27 : List (Sym2 (Fin 17)) :=
  s(12,13) :: es28


private def es26 : List (Sym2 (Fin 17)) :=
  s(10,16) :: es27


private def es25 : List (Sym2 (Fin 17)) :=
  s(10,13) :: es26


private def es24 : List (Sym2 (Fin 17)) :=
  s(10,12) :: es25


private def es23 : List (Sym2 (Fin 17)) :=
  s(8,16) :: es24


private def es22 : List (Sym2 (Fin 17)) :=
  s(8,12) :: es23


private def es21 : List (Sym2 (Fin 17)) :=
  s(6,16) :: es22


private def es20 : List (Sym2 (Fin 17)) :=
  s(6,12) :: es21


private def es19 : List (Sym2 (Fin 17)) :=
  s(6,8) :: es20


private def es18 : List (Sym2 (Fin 17)) :=
  s(4,16) :: es19


private def es17 : List (Sym2 (Fin 17)) :=
  s(4,12) :: es18


private def es16 : List (Sym2 (Fin 17)) :=
  s(4,8) :: es17


private def es15 : List (Sym2 (Fin 17)) :=
  s(4,6) :: es16


private def es14 : List (Sym2 (Fin 17)) :=
  s(3,16) :: es15


private def es13 : List (Sym2 (Fin 17)) :=
  s(3,13) :: es14


private def es12 : List (Sym2 (Fin 17)) :=
  s(3,12) :: es13


private def es11 : List (Sym2 (Fin 17)) :=
  s(3,10) :: es12


private def es10 : List (Sym2 (Fin 17)) :=
  s(3,8) :: es11


private def es9 : List (Sym2 (Fin 17)) :=
  s(3,6) :: es10


private def es8 : List (Sym2 (Fin 17)) :=
  s(3,4) :: es9


private def es7 : List (Sym2 (Fin 17)) :=
  s(0,16) :: es8


private def es6 : List (Sym2 (Fin 17)) :=
  s(0,13) :: es7


private def es5 : List (Sym2 (Fin 17)) :=
  s(0,12) :: es6


private def es4 : List (Sym2 (Fin 17)) :=
  s(0,10) :: es5


private def es3 : List (Sym2 (Fin 17)) :=
  s(0,8) :: es4


private def es2 : List (Sym2 (Fin 17)) :=
  s(0,6) :: es3


private def es1 : List (Sym2 (Fin 17)) :=
  s(0,4) :: es2


private def es0 : List (Sym2 (Fin 17)) :=
  s(0,3) :: es1


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk0 : edgeScan measure 0x2a00000000000540000024000000090000000240100008000000000018 es2 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk1 : edgeScan measure 0x2a00000000000540000024000000090040000240000008000000000048 es3 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk2 : edgeScan measure 0x2a00000000000540000024010000090000000240000008000000000108 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk3 : edgeScan measure 0x2a00000000000544000024000000090000000240000008000000000408 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk4 : edgeScan measure 0x2a00001000000540000024000000090000000240000008000000001008 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk5 : edgeScan measure 0x2a00000000000540000024000000090000000240000008000000000008 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk6 : edgeScan measure 0x2a00000000000540000024000000090040000240100000000000000050 es3 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk7 : edgeScan measure 0x2a00000000000540000024010000090000000240100000000000000110 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk8 : edgeScan measure 0x2a00000000000544000024000000090000000240100000000000000410 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk9 : edgeScan measure 0x2a00001000000540000024000000090000000240100000000000001010 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk10 : edgeScan measure 0x2a00000000000540000024000000090000000240100000000000000010 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk11 : edgeScan measure 0x2a00000000000540000024010000090040000240000000000000000140 es4 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk12 : edgeScan measure 0x2a00000000000544000024000000090040000240000000000000000440 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk13 : edgeScan measure 0x2a00001000000540000024000000090040000240000000000000001040 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk14 : edgeScan measure 0x2a00000000000540000024000000090040000240000000000000000040 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk15 : edgeScan measure 0x2a00000000000544000024010000090000000240000000000000000500 es5 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk16 : edgeScan measure 0x2a00001000000540000024010000090000000240000000000000001100 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk17 : edgeScan measure 0x2a00000000000540000024010000090000000240000000000000000100 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk18 : edgeScan measure 0x2a00001000000544000024000000090000000240000000000000001400 es6 0 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk19 : edgeScan measure 0x2a00000000000544000024000000090000000240000000000000000400 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk20 : edgeScan measure 0x2a00001000000540000024000000090000000240000000000000001000 es6 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk21 : edgeScan measure 0x2a20000000000540000024000000090000000240000000000000002000 es7 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk22 : edgeScan measure 0x100000000002a00000000000540000024000000090000000240000000000000010000 es8 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk23 : edgeScan measure 0x2a00000000000540000024000000090000000240800080000000000000 es9 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk24 : edgeScan measure 0x2a00000000000540000024000000090200000240000200000000000000 es10 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk25 : edgeScan measure 0x2a00000000000540000024080000090000000240000800000000000000 es11 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk26 : edgeScan measure 0x2a00000000000560000024000000090000000240002000000000000000 es12 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk27 : edgeScan measure 0x2a00008000000540000024000000090000000240008000000000000000 es13 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk28 : edgeScan measure 0x2b00000000000540000024000000090000000240010000000000000000 es14 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk29 : edgeScan measure 0x800000000002a00000000000540000024000000090000000240080000000000000000 es15 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk30 : edgeScan measure 0x2a00000000000540000024000000090400000244000000000000000000 es16 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk31 : edgeScan measure 0x2a00000000000540000024100000090000000250000000000000000000 es17 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk32 : edgeScan measure 0x2a00010000000540000024000000090000000340000000000000000000 es18 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk33 : edgeScan measure 0x1000000000002a00000000000540000024000000090000001240000000000000000000 es19 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk34 : edgeScan measure 0x2a00000000000540000024400000094000000240000000000000000000 es20 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk35 : edgeScan measure 0x2a000400000005400000240000000d0000000240000000000000000000 es21 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk36 : edgeScan measure 0x4000000000002a00000000000540000024000000490000000240000000000000000000 es22 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk37 : edgeScan measure 0x2a00100000000540000034000000090000000240000000000000000000 es23 1 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk38 : edgeScan measure 0x2a00000000000540000024000000090000000240000000000000000000 es23 2 = true := by decide +kernel


private theorem allCases : edgeScan measure 0x2a00000000000540000024000000090000000240000000000000000000 es0 2 = true :=
  (edgeNode (edgeNode chunk0 (edgeNode chunk1 (edgeNode chunk2 (edgeNode chunk3 (edgeNode chunk4 chunk5))))) (edgeNode (edgeNode chunk6 (edgeNode chunk7 (edgeNode chunk8 (edgeNode chunk9 chunk10)))) (edgeNode (edgeNode chunk11 (edgeNode chunk12 (edgeNode chunk13 chunk14))) (edgeNode (edgeNode chunk15 (edgeNode chunk16 chunk17)) (edgeNode (edgeNode chunk18 chunk19) (edgeNode chunk20 (edgeNode chunk21 (edgeNode chunk22 (edgeNode chunk23 (edgeNode chunk24 (edgeNode chunk25 (edgeNode chunk26 (edgeNode chunk27 (edgeNode chunk28 (edgeNode chunk29 (edgeNode chunk30 (edgeNode chunk31 (edgeNode chunk32 (edgeNode chunk33 (edgeNode chunk34 (edgeNode chunk35 (edgeNode chunk36 (edgeNode chunk37 chunk38)))))))))))))))))))))))


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private def model : Model mask (fun v => !onlyFirst v) :=
  ⟨vertices,79193,by decide +kernel,
    model_bound es0 79193 0x2a00000000000540000024000000090000000240000000000000000000 2
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) allCases⟩


end Seed1

private def rows : Array Nat :=
  #[79194,13996,61088,79184,121664,61056,121600,60928,121344,51200,77824,114688,73728,65536,98304,65536,0]


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem aligned : ∀ i j : Fin 17, i < j → (board mask).Adj i j →
    (rowAt rows i.val).testBit j.val = true := by decide +kernel


private def book : Array (List Nat) :=
  #[
[],
[0x20f6b90a5a58719406104907b5c852d2c38ca03082435959],
[],
[],
[],
[0x833da45ba0961c65105486a586500ef2b86b2083015559],
[0x12833584541e570d62080e9419ac22a0f038eb28c411cbd0,0x8e5c1a961dea414c31040d43d8a71d66490b0188200cbd1],
[0x1d063da35810a31c851052f6c18e51c08298645882915359],
[],
[0x1f069dcc1290530c8b0812f831cb1a408698e42a8412cbd4,0x8f7358b51e09414c3104087b9ac5a8e6490b0188201c9d1],
[],
[0x1ed61dca1220530c8b08128831ee1ac09698e42a8413cad4,0x833da45ba0a62467288286a58651caf1b84b204101515b],
[0xf043586511e9715630804f419ac228ee82ca9180411c9d4],
[0x8e5c1a961dea414c20806d43d8a71d66490b000c410cbd8],
[],
[0x20f68d0c029c759526104907a1cb3248c38ca06882a34b59],
[0x8f7358b51e09414c2080687b9ac5a8e6490b000c411c9d8],
[],
[],
[],
[],
[],
[0x1ed61dca29203408cb08128831ee1ac0669149394413cbe0,0x1272c1a2629e871163080cd4198a22607781c51ac410cee4],
[0x20f7218b325a751423208107b90c5992d3a8a2184803354b],
[],
[0x1f06a1cc328e428c4b0812f831cb1a40d428c7290412cbe4],
[],
[0xc93b585509e87116308200419ac229e7741651a4411cae4],
[0x4f741ab6192a3a0a41802d7b98a59d0532483140010cae6],
[],
[],
[],
[],
[0x8c1bdc05360941cc5105686b12f028e6290707082b13959],
[],
[],
[],
[0x20f7358b5250731483104107b9ac5a928398a41882033559,0x1f069dcc2a9033088b0812f831cb1a40869944394412cbf0],
[],
[0x1ed61dca2a2033088b08128831ee1ac0969944394413caf0,0x8c1bdc05b60a41cc5105286b12f51c06290707082b13359],
[0x20f7198b225a851c23288107b90c599272b44a184803345b,0xf043586511e970d62080af419ac228ee82c0928c411c9f0],
[],
[0x1f0699cc228e828c4b0812f831cb1a407434ca290412caf4],
[0x1b043dc65918a1a4072882f6b20851cae1ac49304041315b],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[0xf07b4ac521c6591221802f721ab3288981d8510c0126ea6],
[],
[],
[],
[],
[0x833dc46ae0961c65105486b146480ef2b86b2083011d59],
[],
[0x17063dc36810a31c851052f6b14e81c08298645882911b59],
[],
[],
[],
[0x833dc46ae0a62467288286b14649caf1b84b204101195b,0x8c1bdc06aa0b41cc5105286b14f3a406290707082b11759],
[],
[],
[],
[0x15043dc66918b1a4072882f6b1483c0ae1ac49304041155b],
[],
[0x12833dc46c18b1a807288296b1483960f1b84b304041135b],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[0x208331443a5e570d62081b04180d2312f538eb28c411eb50],
[],
[],
[],
[0x1ed615ca11e0640c8b08128831ee1ac0649da42a8413cb34],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[0x20f7354b3a50530c82081907b9a05b128518e428c411db50,0x18f741ab52507314831040d7b9905a928398a4188200db51],
[],
[],
[0x20d5310901de570d6610490419ed2396c48ce02882a3d951,0x128341a4531e7715630804d4198922a0f3b8ab180410db54],
[],
[],
[0x168335444b207795c308048311a98314f3b8ab180411d954],
[0x18f741ab52507314820806d7b9905a928398a400c410db58],
[],
[0x20d5b10a01de570d2610490419ed72c8c48ce02882a3d351],
[0x20d5310919de57096608090419ed2396c48ce0514413d958],
[],
[0x208335843a5e570d6208150419ac2012f538eb28c411cf50],
[],
[],
[],
[0x20d5b10a19de57092608090419ed72c8c48ce0514413d358],
[0x20f7358b5250731483104107b9ac5a928398a4188201cb51],
[0x12833584541e77156310029419ac22a0f3b8ab188011cb52],
[0x20d5bd0a7258719406104906a9e872d2c38ca0308243d159],
[0x12833584541e77156308049419ac22a0f3b8ab180411cb54,0x8e5c1a9609ea41cc51840d43d8a71d6629070124200cb55],
[],
[],
[0x8f7358b50a0941cc5184087b9ac5a8e629070124201c955],
[0x20f7358b5250731482080707b9ac5a928398a400c411cb58,0x6f741ab6250a31c851040d7b98a59d2829864808200cb59],
[],
[],
[0x20d60d0a025e77156610490419ee22d2c38ca06882a3c959,0x128341a460dea71d650804d4198a21e0f2b86b480410cb5c],
[],
[],
[0x1683358450e0979dc508048311ac828ef2b86b480411c95c],
[0x128341a4531e770d62080ad4198922a0f3b80b28c410db70],
[],
[0x20d60d0b029e77152610490419ee5a48c38ca06882a3c359],
[0x168335444b20778dc2080a8311a98314f3b80b28c411d970],
[],
[0x1ed615ca11e0440ccb08128831ee1ac06491a72a8413cb64],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[0x12833584541e770d62080a9419ac22a0f3b80b28c411cb70,0x8e5c1a9615ea41cc31040d43d8a71d6629130188200cb71],
[],
[],
[0x1f0695cc1290730c8b0812f831cb1a408399a42a8412cb74,0x83396453e0961c65105a84b406628ef2b86b208301b159,0x8f7358b5160941cc3104087b9ac5a8e629130188201c971],
[],
[0x1ed615ca1220730c8b08128831ee1ac09399a42a8413ca74],
[0xb043586511e971d630804f419ac228ee2ae09180411c974],
[0x8e5c1a9615ea41cc20806d43d8a71d662913000c410cb78],
[],
[],
[0x8f7358b5160941cc2080687b9ac5a8e62913000c411c978],
[],
[],
[],
[],
[],
[0x1af7418b424e6290430814d7ba0c5812a41cc5190410eea4],
[0x20e6b10a01de558d261049043dcd32c8c48ce02882a39b51],
[],
[0x1272c182535e6711630810d4192c22a0079dc51ac410eba4],
[],
[0x20f7314b424e629043081b07b80d5b12a41cc5190411eaa4],
[0x2f7418952ce829844181ad7b80c4a967414c3112010eaa6],
[],
[0x20e6b10a19de5589260809043dcd32c8c48ce05144139b58],
[],
[0xf0634ab521e6711221802f419ae5a88981d8510c012e6a6],
[0x20e6bd0a5a58719406104906bdc852d2c38ca03082439959],
[],
[],
[],
[0x8339a45be0961c65105484b586500ef2b86b2083019559],
[],
[0x1f0639a35810a31c851052f8358e51c08298645882919359],
[],
[],
[0x1ed61dca11a0540c8b08128831ee1ac066a4e42a8413cb94,0x1272c182535e8719630808d4192c22a07795c01ac410eab4],
[0x8339a45be0a62467288284b58651caf1b84b204101915b],
[],
[],
[],
[0x20e68d0c029e7595261049043dcb3248c38ca06882a38b59],
[],
[],
[],
[],
[],
[0x1272c1a2629e6711630810d4198a2260079dc51ac410cfa4],
[],
[0x20f7358b424e629043081507b9ac5812a41cc5190411cea4],
[0x2f741a962ce8298441814d7b98a48167414c3112010cea6],
[],
[0x1093b585509e67116308200419ac229f071d651a4411cba4],
[0x4f741ab6212a398a41802d7b98a59d0931483140010cba6],
[],
[0x4f7358b54128398a4180297b9ac5a90731483140011caa6],
[],
[],
[],
[],
[],
[],
[],
[],
[0x1ed61dca29a034088b08128831ee1ac066a544394413cbb0,0x1272c1a2629e8719630808d4198a22607795c01ac410ceb4],
[0x20f7218b225a751823288107b90c5992d3944a184803351b],
[],
[0x1f06a1cc228e628c4b0812f831cb1a40d41cca290412cbb4,0x833d6453a0961c65105a86a406628ef2b86b2083017159],
[],
[0x893b585509e87196308200419ac229e7715701a4411cab4],
[0x4f741ab6112a3a0a61802d7b98a59d0530c89140010cab6],
[],
[],
[],
[],
[],
[],
[],
[],
[0x128341a4531e570d62080ed4198922a0f038eb28c410dbd0],
[],
[0x20f6b10a01dc558d26104907a1cd32c8c48ce02882a35b51],
[0xf0734ac521e6591221802f439ab3288981d8510c012aea6,0x168335444b20578dc2080e8311a98314f038eb28c411d9d0],
[],
[0x1ed61dca1160440ccb08128831ee1ac06691272a8413cbc4,0x1272c182535e871163080cd4192c22a07781c51ac410eae4],
[],
[],
[],
[0x20f6b10a19dc558926080907a1cd32c8c48ce05144135b58],
[]]


private def models : Array (Model mask (fun v => !onlyFirst v)) :=
  #[Seed0.model,Seed1.model]


private def checkVertices : Nat → Bool :=
  passes models book rows


private def vs17 : List (Fin 17) :=
  []


private def vs16 : List (Fin 17) :=
  16 :: vs17


private def vs15 : List (Fin 17) :=
  15 :: vs16


private def vs14 : List (Fin 17) :=
  14 :: vs15


private def vs13 : List (Fin 17) :=
  13 :: vs14


private def vs12 : List (Fin 17) :=
  12 :: vs13


private def vs11 : List (Fin 17) :=
  11 :: vs12


private def vs10 : List (Fin 17) :=
  10 :: vs11


private def vs9 : List (Fin 17) :=
  9 :: vs10


private def vs8 : List (Fin 17) :=
  8 :: vs9


private def vs7 : List (Fin 17) :=
  7 :: vs8


private def vs6 : List (Fin 17) :=
  6 :: vs7


private def vs5 : List (Fin 17) :=
  5 :: vs6


private def vs4 : List (Fin 17) :=
  4 :: vs5


private def vs3 : List (Fin 17) :=
  3 :: vs4


private def vs2 : List (Fin 17) :=
  2 :: vs3


private def vs1 : List (Fin 17) :=
  1 :: vs2


private def vs0 : List (Fin 17) :=
  0 :: vs1


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk0 : scan checkVertices 127 vs7 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk1 : scan checkVertices 191 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk2 : scan checkVertices 63 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk3 : scan checkVertices 223 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk4 : scan checkVertices 95 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk5 : scan checkVertices 159 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk6 : scan checkVertices 287 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk7 : scan checkVertices 31 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk8 : scan checkVertices 239 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk9 : scan checkVertices 111 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk10 : scan checkVertices 175 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk11 : scan checkVertices 303 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk12 : scan checkVertices 47 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk13 : scan checkVertices 207 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk14 : scan checkVertices 335 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk15 : scan checkVertices 79 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk16 : scan checkVertices 399 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk17 : scan checkVertices 143 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk18 : scan checkVertices 271 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk19 : scan checkVertices 15 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk20 : scan checkVertices 247 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk21 : scan checkVertices 119 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk22 : scan checkVertices 183 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk23 : scan checkVertices 311 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk24 : scan checkVertices 55 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk25 : scan checkVertices 215 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk26 : scan checkVertices 343 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk27 : scan checkVertices 87 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk28 : scan checkVertices 407 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk29 : scan checkVertices 151 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk30 : scan checkVertices 279 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk31 : scan checkVertices 23 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk32 : scan checkVertices 231 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk33 : scan checkVertices 359 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk34 : scan checkVertices 103 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk35 : scan checkVertices 423 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk36 : scan checkVertices 167 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk37 : scan checkVertices 295 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk38 : scan checkVertices 39 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk39 : scan checkVertices 455 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk40 : scan checkVertices 199 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk41 : scan checkVertices 327 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk42 : scan checkVertices 71 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk43 : scan checkVertices 391 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk44 : scan checkVertices 135 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk45 : scan checkVertices 7 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk46 : scan checkVertices 251 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk47 : scan checkVertices 123 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk48 : scan checkVertices 187 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk49 : scan checkVertices 315 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk50 : scan checkVertices 59 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk51 : scan checkVertices 219 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk52 : scan checkVertices 347 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk53 : scan checkVertices 91 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk54 : scan checkVertices 411 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk55 : scan checkVertices 155 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk56 : scan checkVertices 283 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk57 : scan checkVertices 27 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk58 : scan checkVertices 235 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk59 : scan checkVertices 363 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk60 : scan checkVertices 107 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk61 : scan checkVertices 427 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk62 : scan checkVertices 171 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk63 : scan checkVertices 299 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk64 : scan checkVertices 43 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk65 : scan checkVertices 459 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk66 : scan checkVertices 203 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk67 : scan checkVertices 331 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk68 : scan checkVertices 75 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk69 : scan checkVertices 395 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk70 : scan checkVertices 139 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk71 : scan checkVertices 11 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk72 : scan checkVertices 243 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk73 : scan checkVertices 371 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk74 : scan checkVertices 115 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk75 : scan checkVertices 435 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk76 : scan checkVertices 179 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk77 : scan checkVertices 307 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk78 : scan checkVertices 51 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk79 : scan checkVertices 467 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk80 : scan checkVertices 211 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk81 : scan checkVertices 339 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk82 : scan checkVertices 83 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk83 : scan checkVertices 403 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk84 : scan checkVertices 147 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk85 : scan checkVertices 19 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk86 : scan checkVertices 483 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk87 : scan checkVertices 227 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk88 : scan checkVertices 355 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk89 : scan checkVertices 99 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk90 : scan checkVertices 419 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk91 : scan checkVertices 163 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk92 : scan checkVertices 35 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk93 : scan checkVertices 451 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk94 : scan checkVertices 195 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk95 : scan checkVertices 67 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk96 : scan checkVertices 131 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk97 : scan checkVertices 3 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk98 : scan checkVertices 253 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk99 : scan checkVertices 125 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk100 : scan checkVertices 189 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk101 : scan checkVertices 317 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk102 : scan checkVertices 61 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk103 : scan checkVertices 221 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk104 : scan checkVertices 349 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk105 : scan checkVertices 93 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk106 : scan checkVertices 413 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk107 : scan checkVertices 157 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk108 : scan checkVertices 285 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk109 : scan checkVertices 29 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk110 : scan checkVertices 237 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk111 : scan checkVertices 365 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk112 : scan checkVertices 109 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk113 : scan checkVertices 429 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk114 : scan checkVertices 173 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk115 : scan checkVertices 301 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk116 : scan checkVertices 45 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk117 : scan checkVertices 461 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk118 : scan checkVertices 205 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk119 : scan checkVertices 333 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk120 : scan checkVertices 77 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk121 : scan checkVertices 397 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk122 : scan checkVertices 141 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk123 : scan checkVertices 13 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk124 : scan checkVertices 245 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk125 : scan checkVertices 373 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk126 : scan checkVertices 117 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk127 : scan checkVertices 437 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk128 : scan checkVertices 181 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk129 : scan checkVertices 309 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk130 : scan checkVertices 53 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk131 : scan checkVertices 469 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk132 : scan checkVertices 213 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk133 : scan checkVertices 341 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk134 : scan checkVertices 85 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk135 : scan checkVertices 405 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk136 : scan checkVertices 149 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk137 : scan checkVertices 21 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk138 : scan checkVertices 485 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk139 : scan checkVertices 229 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk140 : scan checkVertices 357 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk141 : scan checkVertices 101 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk142 : scan checkVertices 421 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk143 : scan checkVertices 165 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk144 : scan checkVertices 37 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk145 : scan checkVertices 453 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk146 : scan checkVertices 197 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk147 : scan checkVertices 69 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk148 : scan checkVertices 133 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk149 : scan checkVertices 5 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk150 : scan checkVertices 249 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk151 : scan checkVertices 377 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk152 : scan checkVertices 121 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk153 : scan checkVertices 441 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk154 : scan checkVertices 185 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk155 : scan checkVertices 313 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk156 : scan checkVertices 57 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk157 : scan checkVertices 473 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk158 : scan checkVertices 217 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk159 : scan checkVertices 345 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk160 : scan checkVertices 89 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk161 : scan checkVertices 409 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk162 : scan checkVertices 153 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk163 : scan checkVertices 25 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk164 : scan checkVertices 489 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk165 : scan checkVertices 233 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk166 : scan checkVertices 361 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk167 : scan checkVertices 105 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk168 : scan checkVertices 425 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk169 : scan checkVertices 169 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk170 : scan checkVertices 41 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk171 : scan checkVertices 457 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk172 : scan checkVertices 201 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk173 : scan checkVertices 73 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk174 : scan checkVertices 137 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk175 : scan checkVertices 9 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk176 : scan checkVertices 497 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk177 : scan checkVertices 241 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk178 : scan checkVertices 369 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk179 : scan checkVertices 113 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk180 : scan checkVertices 433 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk181 : scan checkVertices 177 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk182 : scan checkVertices 49 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk183 : scan checkVertices 465 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk184 : scan checkVertices 209 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk185 : scan checkVertices 81 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk186 : scan checkVertices 145 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk187 : scan checkVertices 17 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk188 : scan checkVertices 481 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk189 : scan checkVertices 225 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk190 : scan checkVertices 97 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk191 : scan checkVertices 161 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk192 : scan checkVertices 33 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk193 : scan checkVertices 193 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk194 : scan checkVertices 65 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk195 : scan checkVertices 1 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk196 : scan checkVertices 254 vs8 2 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk197 : scan checkVertices 126 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk198 : scan checkVertices 190 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk199 : scan checkVertices 318 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk200 : scan checkVertices 62 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk201 : scan checkVertices 222 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk202 : scan checkVertices 350 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk203 : scan checkVertices 94 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk204 : scan checkVertices 414 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk205 : scan checkVertices 158 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk206 : scan checkVertices 286 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk207 : scan checkVertices 30 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk208 : scan checkVertices 238 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk209 : scan checkVertices 366 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk210 : scan checkVertices 110 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk211 : scan checkVertices 430 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk212 : scan checkVertices 174 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk213 : scan checkVertices 302 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk214 : scan checkVertices 46 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk215 : scan checkVertices 462 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk216 : scan checkVertices 206 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk217 : scan checkVertices 334 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk218 : scan checkVertices 78 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk219 : scan checkVertices 398 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk220 : scan checkVertices 142 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk221 : scan checkVertices 14 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk222 : scan checkVertices 246 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk223 : scan checkVertices 374 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk224 : scan checkVertices 118 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk225 : scan checkVertices 438 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk226 : scan checkVertices 182 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk227 : scan checkVertices 310 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk228 : scan checkVertices 54 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk229 : scan checkVertices 470 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk230 : scan checkVertices 214 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk231 : scan checkVertices 342 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk232 : scan checkVertices 86 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk233 : scan checkVertices 406 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk234 : scan checkVertices 150 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk235 : scan checkVertices 22 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk236 : scan checkVertices 486 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk237 : scan checkVertices 230 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk238 : scan checkVertices 358 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk239 : scan checkVertices 102 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk240 : scan checkVertices 422 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk241 : scan checkVertices 166 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk242 : scan checkVertices 38 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk243 : scan checkVertices 454 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk244 : scan checkVertices 198 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk245 : scan checkVertices 70 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk246 : scan checkVertices 134 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk247 : scan checkVertices 6 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk248 : scan checkVertices 250 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk249 : scan checkVertices 378 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk250 : scan checkVertices 122 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk251 : scan checkVertices 442 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk252 : scan checkVertices 186 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk253 : scan checkVertices 314 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk254 : scan checkVertices 58 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk255 : scan checkVertices 474 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk256 : scan checkVertices 218 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk257 : scan checkVertices 346 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk258 : scan checkVertices 90 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk259 : scan checkVertices 410 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk260 : scan checkVertices 154 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk261 : scan checkVertices 26 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk262 : scan checkVertices 490 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk263 : scan checkVertices 234 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk264 : scan checkVertices 362 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk265 : scan checkVertices 106 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk266 : scan checkVertices 426 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk267 : scan checkVertices 170 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk268 : scan checkVertices 42 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk269 : scan checkVertices 458 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk270 : scan checkVertices 202 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk271 : scan checkVertices 74 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk272 : scan checkVertices 138 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk273 : scan checkVertices 10 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk274 : scan checkVertices 498 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk275 : scan checkVertices 242 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk276 : scan checkVertices 370 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk277 : scan checkVertices 114 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk278 : scan checkVertices 434 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk279 : scan checkVertices 178 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk280 : scan checkVertices 50 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk281 : scan checkVertices 466 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk282 : scan checkVertices 210 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk283 : scan checkVertices 82 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk284 : scan checkVertices 146 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk285 : scan checkVertices 18 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk286 : scan checkVertices 482 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk287 : scan checkVertices 226 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk288 : scan checkVertices 98 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk289 : scan checkVertices 162 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk290 : scan checkVertices 34 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk291 : scan checkVertices 194 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk292 : scan checkVertices 66 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk293 : scan checkVertices 2 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk294 : scan checkVertices 252 vs8 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk295 : scan checkVertices 380 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk296 : scan checkVertices 124 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk297 : scan checkVertices 444 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk298 : scan checkVertices 188 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk299 : scan checkVertices 316 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk300 : scan checkVertices 60 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk301 : scan checkVertices 476 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk302 : scan checkVertices 220 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk303 : scan checkVertices 348 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk304 : scan checkVertices 92 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk305 : scan checkVertices 412 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk306 : scan checkVertices 156 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk307 : scan checkVertices 28 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk308 : scan checkVertices 492 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk309 : scan checkVertices 236 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk310 : scan checkVertices 364 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk311 : scan checkVertices 108 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk312 : scan checkVertices 428 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk313 : scan checkVertices 172 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk314 : scan checkVertices 44 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk315 : scan checkVertices 460 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk316 : scan checkVertices 204 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk317 : scan checkVertices 76 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk318 : scan checkVertices 140 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk319 : scan checkVertices 12 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk320 : scan checkVertices 500 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk321 : scan checkVertices 244 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk322 : scan checkVertices 372 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk323 : scan checkVertices 116 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk324 : scan checkVertices 436 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk325 : scan checkVertices 180 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk326 : scan checkVertices 52 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk327 : scan checkVertices 468 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk328 : scan checkVertices 212 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk329 : scan checkVertices 84 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk330 : scan checkVertices 148 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk331 : scan checkVertices 20 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk332 : scan checkVertices 484 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk333 : scan checkVertices 228 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk334 : scan checkVertices 100 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk335 : scan checkVertices 164 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk336 : scan checkVertices 36 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk337 : scan checkVertices 196 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk338 : scan checkVertices 68 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk339 : scan checkVertices 4 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk340 : scan checkVertices 504 vs9 3 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk341 : scan checkVertices 248 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk342 : scan checkVertices 376 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk343 : scan checkVertices 120 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk344 : scan checkVertices 440 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk345 : scan checkVertices 184 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk346 : scan checkVertices 56 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk347 : scan checkVertices 472 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk348 : scan checkVertices 216 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk349 : scan checkVertices 88 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk350 : scan checkVertices 152 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk351 : scan checkVertices 24 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk352 : scan checkVertices 488 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk353 : scan checkVertices 232 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk354 : scan checkVertices 104 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk355 : scan checkVertices 168 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk356 : scan checkVertices 40 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk357 : scan checkVertices 200 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk358 : scan checkVertices 72 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk359 : scan checkVertices 8 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk360 : scan checkVertices 496 vs9 4 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk361 : scan checkVertices 240 vs9 5 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk362 : scan checkVertices 112 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk363 : scan checkVertices 176 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk364 : scan checkVertices 48 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk365 : scan checkVertices 208 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk366 : scan checkVertices 80 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk367 : scan checkVertices 16 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk368 : scan checkVertices 224 vs8 6 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk369 : scan checkVertices 96 vs8 7 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk370 : scan checkVertices 32 vs7 8 = true := by decide +kernel


set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem chunk371 : scan checkVertices 0 vs6 9 = true := by decide +kernel


private theorem allCases : scan checkVertices 0 vs0 9 = true :=
  (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk0 (scan_node chunk1 chunk2)) (scan_node (scan_node chunk3 chunk4) (scan_node chunk5 (scan_node chunk6 chunk7)))) (scan_node (scan_node (scan_node chunk8 chunk9) (scan_node chunk10 (scan_node chunk11 chunk12))) (scan_node (scan_node chunk13 (scan_node chunk14 chunk15)) (scan_node (scan_node chunk16 chunk17) (scan_node chunk18 chunk19))))) (scan_node (scan_node (scan_node (scan_node chunk20 chunk21) (scan_node chunk22 (scan_node chunk23 chunk24))) (scan_node (scan_node chunk25 (scan_node chunk26 chunk27)) (scan_node (scan_node chunk28 chunk29) (scan_node chunk30 chunk31)))) (scan_node (scan_node (scan_node chunk32 (scan_node chunk33 chunk34)) (scan_node (scan_node chunk35 chunk36) (scan_node chunk37 chunk38))) (scan_node (scan_node (scan_node chunk39 chunk40) (scan_node chunk41 chunk42)) (scan_node (scan_node chunk43 chunk44) chunk45))))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk46 chunk47) (scan_node chunk48 (scan_node chunk49 chunk50))) (scan_node (scan_node chunk51 (scan_node chunk52 chunk53)) (scan_node (scan_node chunk54 chunk55) (scan_node chunk56 chunk57)))) (scan_node (scan_node (scan_node chunk58 (scan_node chunk59 chunk60)) (scan_node (scan_node chunk61 chunk62) (scan_node chunk63 chunk64))) (scan_node (scan_node (scan_node chunk65 chunk66) (scan_node chunk67 chunk68)) (scan_node (scan_node chunk69 chunk70) chunk71)))) (scan_node (scan_node (scan_node (scan_node chunk72 (scan_node chunk73 chunk74)) (scan_node (scan_node chunk75 chunk76) (scan_node chunk77 chunk78))) (scan_node (scan_node (scan_node chunk79 chunk80) (scan_node chunk81 chunk82)) (scan_node (scan_node chunk83 chunk84) chunk85))) (scan_node (scan_node (scan_node (scan_node chunk86 chunk87) (scan_node chunk88 chunk89)) (scan_node (scan_node chunk90 chunk91) chunk92)) (scan_node (scan_node (scan_node chunk93 chunk94) chunk95) (scan_node chunk96 chunk97)))))) (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk98 chunk99) (scan_node chunk100 (scan_node chunk101 chunk102))) (scan_node (scan_node chunk103 (scan_node chunk104 chunk105)) (scan_node (scan_node chunk106 chunk107) (scan_node chunk108 chunk109)))) (scan_node (scan_node (scan_node chunk110 (scan_node chunk111 chunk112)) (scan_node (scan_node chunk113 chunk114) (scan_node chunk115 chunk116))) (scan_node (scan_node (scan_node chunk117 chunk118) (scan_node chunk119 chunk120)) (scan_node (scan_node chunk121 chunk122) chunk123)))) (scan_node (scan_node (scan_node (scan_node chunk124 (scan_node chunk125 chunk126)) (scan_node (scan_node chunk127 chunk128) (scan_node chunk129 chunk130))) (scan_node (scan_node (scan_node chunk131 chunk132) (scan_node chunk133 chunk134)) (scan_node (scan_node chunk135 chunk136) chunk137))) (scan_node (scan_node (scan_node (scan_node chunk138 chunk139) (scan_node chunk140 chunk141)) (scan_node (scan_node chunk142 chunk143) chunk144)) (scan_node (scan_node (scan_node chunk145 chunk146) chunk147) (scan_node chunk148 chunk149))))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk150 (scan_node chunk151 chunk152)) (scan_node (scan_node chunk153 chunk154) (scan_node chunk155 chunk156))) (scan_node (scan_node (scan_node chunk157 chunk158) (scan_node chunk159 chunk160)) (scan_node (scan_node chunk161 chunk162) chunk163))) (scan_node (scan_node (scan_node (scan_node chunk164 chunk165) (scan_node chunk166 chunk167)) (scan_node (scan_node chunk168 chunk169) chunk170)) (scan_node (scan_node (scan_node chunk171 chunk172) chunk173) (scan_node chunk174 chunk175)))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk176 chunk177) (scan_node chunk178 chunk179)) (scan_node (scan_node chunk180 chunk181) chunk182)) (scan_node (scan_node (scan_node chunk183 chunk184) chunk185) (scan_node chunk186 chunk187))) (scan_node (scan_node (scan_node (scan_node chunk188 chunk189) chunk190) (scan_node chunk191 chunk192)) (scan_node (scan_node chunk193 chunk194) chunk195)))))) (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk196 chunk197) (scan_node chunk198 (scan_node chunk199 chunk200))) (scan_node (scan_node chunk201 (scan_node chunk202 chunk203)) (scan_node (scan_node chunk204 chunk205) (scan_node chunk206 chunk207)))) (scan_node (scan_node (scan_node chunk208 (scan_node chunk209 chunk210)) (scan_node (scan_node chunk211 chunk212) (scan_node chunk213 chunk214))) (scan_node (scan_node (scan_node chunk215 chunk216) (scan_node chunk217 chunk218)) (scan_node (scan_node chunk219 chunk220) chunk221)))) (scan_node (scan_node (scan_node (scan_node chunk222 (scan_node chunk223 chunk224)) (scan_node (scan_node chunk225 chunk226) (scan_node chunk227 chunk228))) (scan_node (scan_node (scan_node chunk229 chunk230) (scan_node chunk231 chunk232)) (scan_node (scan_node chunk233 chunk234) chunk235))) (scan_node (scan_node (scan_node (scan_node chunk236 chunk237) (scan_node chunk238 chunk239)) (scan_node (scan_node chunk240 chunk241) chunk242)) (scan_node (scan_node (scan_node chunk243 chunk244) chunk245) (scan_node chunk246 chunk247))))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk248 (scan_node chunk249 chunk250)) (scan_node (scan_node chunk251 chunk252) (scan_node chunk253 chunk254))) (scan_node (scan_node (scan_node chunk255 chunk256) (scan_node chunk257 chunk258)) (scan_node (scan_node chunk259 chunk260) chunk261))) (scan_node (scan_node (scan_node (scan_node chunk262 chunk263) (scan_node chunk264 chunk265)) (scan_node (scan_node chunk266 chunk267) chunk268)) (scan_node (scan_node (scan_node chunk269 chunk270) chunk271) (scan_node chunk272 chunk273)))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk274 chunk275) (scan_node chunk276 chunk277)) (scan_node (scan_node chunk278 chunk279) chunk280)) (scan_node (scan_node (scan_node chunk281 chunk282) chunk283) (scan_node chunk284 chunk285))) (scan_node (scan_node (scan_node (scan_node chunk286 chunk287) chunk288) (scan_node chunk289 chunk290)) (scan_node (scan_node chunk291 chunk292) chunk293))))) (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk294 (scan_node chunk295 chunk296)) (scan_node (scan_node chunk297 chunk298) (scan_node chunk299 chunk300))) (scan_node (scan_node (scan_node chunk301 chunk302) (scan_node chunk303 chunk304)) (scan_node (scan_node chunk305 chunk306) chunk307))) (scan_node (scan_node (scan_node (scan_node chunk308 chunk309) (scan_node chunk310 chunk311)) (scan_node (scan_node chunk312 chunk313) chunk314)) (scan_node (scan_node (scan_node chunk315 chunk316) chunk317) (scan_node chunk318 chunk319)))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk320 chunk321) (scan_node chunk322 chunk323)) (scan_node (scan_node chunk324 chunk325) chunk326)) (scan_node (scan_node (scan_node chunk327 chunk328) chunk329) (scan_node chunk330 chunk331))) (scan_node (scan_node (scan_node (scan_node chunk332 chunk333) chunk334) (scan_node chunk335 chunk336)) (scan_node (scan_node chunk337 chunk338) chunk339)))) (scan_node (scan_node (scan_node (scan_node (scan_node (scan_node chunk340 chunk341) (scan_node chunk342 chunk343)) (scan_node (scan_node chunk344 chunk345) chunk346)) (scan_node (scan_node (scan_node chunk347 chunk348) chunk349) (scan_node chunk350 chunk351))) (scan_node (scan_node (scan_node (scan_node chunk352 chunk353) chunk354) (scan_node chunk355 chunk356)) (scan_node (scan_node chunk357 chunk358) chunk359))) (scan_node (scan_node (scan_node (scan_node (scan_node chunk360 chunk361) chunk362) (scan_node chunk363 chunk364)) (scan_node (scan_node chunk365 chunk366) chunk367)) (scan_node (scan_node (scan_node chunk368 chunk369) chunk370) chunk371))))))


private theorem on_set (S : Finset (Fin 17)) (hs : S.card = 9) :
    BoundOn mask (fun v => !onlyFirst v) S := by
  apply route_sound models book rows aligned S
  have cover : vs0.toFinset = univ := by decide +kernel
  have sub : S ⊆ vs0.toFinset := by simp [cover]
  have h := scan_sound (f := checkVertices) 0 vs0 S sub (hs.symm ▸ allCases)
  simpa [checkVertices] using h


end Third

theorem bound : OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1.H2 := by
  classical
  let masks := (![First.mask, Second.mask, Third.mask] : Fin 3 → Nat)
  let C (a : Fin 3) : SimpleGraph (Fin 17) :=
    { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*17+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm, by simpa only [min_comm j i, max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  intro f
  let D := ⨅ a, (C a)ᶜ.comap (f a)
  change D.Connected → D.edgeSet.ncard ≤ 27
  intro _
  by_contra! large
  have card : D.edgeSet.ncard = D.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card D.edgeSet]
    congr 1
    ext z
    simp [SimpleGraph.edgeFinset]
  obtain ⟨E, he, hc⟩ := Finset.exists_subset_card_eq (show 28 ≤ D.edgeFinset.card by omega)
  have maps (a : Fin 3) (x y : Fin 9) (h : D.Adj x y) :
      (board (masks a)).Adj (f a x) (f a y) := by
    have adj := (iInf_le (fun a => (C a)ᶜ.comap (f a)) a : D ≤ _) h
    change f a x ≠ f a y ∧ ¬ (_ ∧ _ = true) at adj
    exact ⟨adj.1, Bool.eq_false_iff.mpr (fun hb => adj.2 ⟨adj.1, hb⟩)⟩
  have a := placement First.on_set (f 0) (maps 0) E he hc
  have b := placement Second.on_set (f 1) (maps 1) E he hc
  have c := placement Third.on_set (f 2) (maps 2) E he hc
  simp only [Bool.not_eq_true'] at b c
  simp [firstSig, b, c] at a


end RamseyNine

theorem OMA.solution : OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1.H2 :=
  RamseyNine.bound
