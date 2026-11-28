import OMAReductions.R_Erdos552_erdos_552_parts_ii_R2_H2_R1
import Mathlib

/-!
# Four-cycle saturation

On a finite vertex set a quadrilateral-free graph has a quadrilateral-free
supergraph in which every missing edge closes a four-cycle. Deleting the new
edge from that cycle gives a simple path of length three in the original
graph. The edge-insertion equivalence holds for arbitrary vertex types.

Lean formalization by @KoaOkano.
-/

namespace OMA.QuadrilateralSaturation

open SimpleGraph

variable {V : Type*}

/-- An edge not incident with one of the two new endpoints was already present. -/
private theorem oldEdge (G : SimpleGraph V) {x y u v : V}
    (huv : (G ⊔ edge x y).Adj u v)
    (away : (u ≠ x ∧ u ≠ y) ∨ (v ≠ x ∧ v ≠ y)) : G.Adj u v := by
  rcases huv with old | fresh
  · exact old
  have ends := ((edge_adj x y u v).mp fresh).1
  rcases away with h | h <;> rcases ends with e | e <;> tauto

/-- If the side uv of a four-cycle is new, its other three sides form the path. -/
private theorem remainingSides (G : SimpleGraph V) {x y u v m n : V}
    (huv : (G ⊔ edge x y).Adj u v) (fresh : ¬ G.Adj u v)
    (hvm : (G ⊔ edge x y).Adj v m) (hmn : (G ⊔ edge x y).Adj m n)
    (hnu : (G ⊔ edge x y).Adj n u)
    (hmu : m ≠ u) (hmv : m ≠ v) (hnu' : n ≠ u) (hnv : n ≠ v) :
    ∃ a b, a ≠ y ∧ b ≠ x ∧ G.Adj x a ∧ G.Adj a b ∧ G.Adj b y := by
  have newEdge : (edge x y).Adj u v := (show G.Adj u v ∨ (edge x y).Adj u v from huv).resolve_left fresh
  have ends := ((edge_adj x y u v).mp newEdge).1
  have hm : m ≠ x ∧ m ≠ y := by rcases ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  have hn : n ≠ x ∧ n ≠ y := by rcases ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  have vm := oldEdge G hvm (Or.inr hm)
  have mn := oldEdge G hmn (Or.inl hm)
  have nu := oldEdge G hnu (Or.inl hn)
  rcases ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨n, m, hnv, hmu, nu.symm, mn.symm, vm.symm⟩
  · exact ⟨m, n, hmu, hnv, vm, mn, nu⟩

/-- Extract the other three edges from a four-cycle created by an insertion. -/
theorem path_of_insert (G : SimpleGraph V) {x y : V}
    (free : ¬ (cycleGraph 4).IsContained G)
    (created : (cycleGraph 4).IsContained (G ⊔ edge x y)) :
    ∃ a b, a ≠ y ∧ b ≠ x ∧ G.Adj x a ∧ G.Adj a b ∧ G.Adj b y := by
  obtain ⟨φ⟩ := created
  have ab := φ.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide)
  have bc := φ.toHom.map_adj (show (cycleGraph 4).Adj 1 2 by decide)
  have cd := φ.toHom.map_adj (show (cycleGraph 4).Adj 2 3 by decide)
  have da := φ.toHom.map_adj (show (cycleGraph 4).Adj 3 0 by decide)
  by_cases hab : G.Adj (φ 0) (φ 1)
  · by_cases hbc : G.Adj (φ 1) (φ 2)
    · by_cases hcd : G.Adj (φ 2) (φ 3)
      · by_cases hda : G.Adj (φ 3) (φ 0)
        · exfalso
          apply free
          refine ⟨⟨⟨φ, ?_⟩, φ.injective⟩⟩
          intro i j hij
          fin_cases i <;> fin_cases j <;> first
            | exact absurd hij (by decide)
            | exact hab | exact hab.symm | exact hbc | exact hbc.symm
            | exact hcd | exact hcd.symm | exact hda | exact hda.symm
        · apply remainingSides G da hda ab bc cd <;> exact φ.injective.ne (by decide)
      · apply remainingSides G cd hcd da ab bc <;> exact φ.injective.ne (by decide)
    · apply remainingSides G bc hbc cd da ab <;> exact φ.injective.ne (by decide)
  · apply remainingSides G ab hab bc cd da <;> exact φ.injective.ne (by decide)

/-- Conversely, inserting the missing side closes the specified simple path. -/
theorem insert_of_path (G : SimpleGraph V) {x y : V} (hne : x ≠ y)
    (path : ∃ a b, a ≠ y ∧ b ≠ x ∧ G.Adj x a ∧ G.Adj a b ∧ G.Adj b y) :
    (cycleGraph 4).IsContained (G ⊔ edge x y) := by
  obtain ⟨a, b, hay, hbx, hxa, hab, hby⟩ := path
  let f : Fin 4 → V := ![x, a, b, y]
  have injective : Function.Injective f := by
    intro i j eq
    have hxna := hxa.ne
    have hanb := hab.ne
    have hbny := hby.ne
    fin_cases i <;> fin_cases j <;> simp [f] at eq ⊢ <;> tauto
  refine ⟨⟨⟨f, ?_⟩, injective⟩⟩
  have side : (edge x y).Adj x y := (edge_adj x y x y).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd hij (by decide)
    | exact Or.inl hxa | exact Or.inl hxa.symm
    | exact Or.inl hab | exact Or.inl hab.symm
    | exact Or.inl hby | exact Or.inl hby.symm
    | exact Or.inr side | exact Or.inr side.symm

theorem insert_iff_path (G : SimpleGraph V) {x y : V} (hne : x ≠ y)
    (free : ¬ (cycleGraph 4).IsContained G) :
    (cycleGraph 4).IsContained (G ⊔ edge x y) ↔
      ∃ a b, a ≠ y ∧ b ≠ x ∧ G.Adj x a ∧ G.Adj a b ∧ G.Adj b y :=
  ⟨path_of_insert G free, insert_of_path G hne⟩

end OMA.QuadrilateralSaturation

open SimpleGraph OMA.QuadrilateralSaturation in
theorem OMA.solution : OMA.R_Erdos552_erdos_552_parts_ii_R2_H2_R1.H1 := by
  classical
  intro N G free
  obtain ⟨S, hGS, maximal⟩ := exists_maximal_ge_of_wellFoundedGT
    (fun T : SimpleGraph (Fin N) => ¬ (cycleGraph 4).IsContained T) G free
  refine ⟨S, hGS, maximal.1, ?_⟩
  intro x y hne missing
  apply path_of_insert S maximal.1
  by_contra stillFree
  have back : S ⊔ edge x y ≤ S := maximal.2 stillFree le_sup_left
  exact missing (back (show (S ⊔ edge x y).Adj x y from
    Or.inr ((edge_adj x y x y).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)))
