import OMAStatements.S_oeis_a081199
import Mathlib

/-!
R. H. Hardin's four-point line conjecture (OEIS A081199).
The coordinate-word double count is adapted from George Pickett (@grp06),
`proofs/oeis-a081201.lean`, in this repository (PR #13314).
Here collinearity is the usual affine collinearity in real coordinate space.
-/

namespace OMA.S_oeis_a081199

private abbrev Grid (n : ℕ) := Fin n → Fin 4

private abbrev OnLine {n : ℕ} (s : Finset (Grid n)) :=
  Collinear ℝ (toReal '' (s : Set (Grid n)))

private abbrev Symbol := Fin 4 ⊕ Bool
private abbrev Word (n : ℕ) := Fin n → Symbol

private def value : Symbol → Fin 4 → Fin 4
  | .inl a, _ => a
  | .inr true, t => t
  | .inr false, t => t.rev

private def slope : Symbol → ℤ
  | .inl _ => 0
  | .inr true => 1
  | .inr false => -1

private def point {n : ℕ} (w : Word n) (t : Fin 4) : Grid n :=
  fun i => value (w i) t

private def active {n : ℕ} (w : Word n) : Prop :=
  ∃ (i : Fin n) (b : Bool), w i = .inr b

private noncomputable def entries {n : ℕ} (w : Word n) : Finset (Grid n) := by
  classical
  exact Finset.univ.image (point w)

private theorem mem_entries {n : ℕ} {w : Word n} {p : Grid n} :
    p ∈ entries w ↔ ∃ t, point w t = p := by
  classical
  simp [entries]

private theorem cast_rev (t : Fin 4) : (t.rev : ℤ) = 3 - (t : ℤ) := by
  have ht := t.isLt
  simp only [Fin.val_rev]
  omega

private theorem value_affine (c : Symbol) (t : Fin 4) :
    (value c t : ℤ) = (value c 0 : ℤ) + (t : ℤ) * slope c := by
  rcases c with a | (_ | _)
  · simp [value, slope]
  · change (t.rev : ℤ) = ((0 : Fin 4).rev : ℤ) + (t : ℤ) * (-1)
    rw [cast_rev t, cast_rev (0 : Fin 4)]
    change 3 - (t : ℤ) = (3 - 0) + (t : ℤ) * (-1)
    ring
  · simp [value, slope]

private theorem value_active_injective (b : Bool) : Function.Injective (value (.inr b)) := by
  cases b <;> simp [value, Function.Injective]

private theorem symbol_injective :
    Function.Injective (fun c : Symbol => (value c 0, value c 3)) := by
  decide

private theorem entries_valid {n : ℕ} {w : Word n} (hw : active w) :
    (entries w).card = 4 ∧ OnLine (entries w) := by
  classical
  obtain ⟨i, b, hi⟩ := hw
  have hp : Function.Injective (point w) := by
    intro u v h
    apply value_active_injective b
    simpa [point, hi] using congrFun h i
  constructor
  · simp [entries, Finset.card_image_of_injective _ hp]
  · rw [OnLine, collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨toReal (point w 0), fun i => (slope (w i) : ℝ), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨t, rfl⟩ := mem_entries.mp hz
    refine ⟨(t : ℝ), funext fun i => ?_⟩
    change (value (w i) t : ℝ) = (t : ℝ) * (slope (w i) : ℝ) + (value (w i) 0 : ℝ)
    rw [add_comm]
    exact_mod_cast value_affine (w i) t

-- The values at parameters 0, 1, and 3 force the integral step to be 0 or ±1.
private theorem classify (a b c : Fin 4)
    (h : (c : ℤ) = (a : ℤ) + 3 * ((b : ℤ) - (a : ℤ))) :
    ∃ u : Symbol, ∀ t : Fin 4,
      (value u t : ℤ) = (a : ℤ) + (t : ℤ) * ((b : ℤ) - (a : ℤ)) := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  rcases lt_trichotomy (b : ℤ) (a : ℤ) with hlt | heq | hgt
  · refine ⟨.inr false, fun t => ?_⟩
    have hA : (a : ℤ) = 3 := by omega
    have hB : (b : ℤ) = 2 := by omega
    rw [hA, hB, show value (.inr false) t = t.rev from rfl, cast_rev]
    ring
  · refine ⟨.inl a, fun t => ?_⟩
    simp [value, heq]
  · refine ⟨.inr true, fun t => ?_⟩
    have hA : (a : ℤ) = 0 := by omega
    have hB : (b : ℤ) = 1 := by omega
    rw [hA, hB]
    change (t : ℤ) = 0 + (t : ℤ) * (1 - 0)
    ring

private theorem entries_surj {n : ℕ} {s : Finset (Grid n)}
    (hs : s.card = 4) (hl : OnLine s) :
    ∃ w : Word n, active w ∧ entries w = s := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < s.card by omega)
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (show toReal a ∈ toReal '' (s : Set (Grid n))
    from ⟨a, ha, rfl⟩)).mp hl
  have displacement (z : Grid n) (hz : z ∈ s) :
      ∃ r : ℝ, ∀ j, (z j : ℝ) - a j = r * v j := by
    obtain ⟨r, hr⟩ := hv _ ⟨z, hz, rfl⟩
    refine ⟨r, fun j => ?_⟩
    have e := congrFun hr j
    change (z j : ℝ) = r * v j + (a j : ℝ) at e
    linarith
  have hline (z : Grid n) (hz : z ∈ s) (j k : Fin n) :
      ((z j : ℤ) - a j) * ((b k : ℤ) - a k) =
        ((z k : ℤ) - a k) * ((b j : ℤ) - a j) := by
    obtain ⟨r, hr⟩ := displacement z hz
    obtain ⟨q, hq⟩ := displacement b hb
    have e : ((z j : ℝ) - a j) * ((b k : ℝ) - a k) =
        ((z k : ℝ) - a k) * ((b j : ℝ) - a j) := by
      rw [hr j, hq k, hr k, hq j]
      ring
    exact_mod_cast e
  have hsome : ∃ i, a i ≠ b i := by
    by_contra! h
    exact hab (funext h)
  obtain ⟨i, hi⟩ := hsome
  have hd : (b i : ℤ) - (a i : ℤ) ≠ 0 := by
    intro h
    apply hi
    exact Fin.ext (by exact_mod_cast (sub_eq_zero.mp h).symm)
  have hproj : Set.InjOn (fun p : Grid n => p i) (s : Set (Grid n)) := by
    intro x hx y hy hxy
    funext j
    have he : (x i : ℤ) = (y i : ℤ) := congrArg (fun q : Fin 4 => (q : ℤ)) hxy
    have hm : ((x j : ℤ) - (y j : ℤ)) * ((b i : ℤ) - (a i : ℤ)) = 0 := by
      linear_combination hline x hx j i - hline y hy j i +
        ((b j : ℤ) - (a j : ℤ)) * he
    have hval := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hd)
    exact Fin.ext (by exact_mod_cast hval)
  have hfull : (s.image (fun p : Grid n => p i)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simp [Finset.card_image_of_injOn hproj, hs])
  have hp (t : Fin 4) : ∃ x ∈ s, x i = t := by
    apply Finset.mem_image.mp
    rw [hfull]
    exact Finset.mem_univ t
  obtain ⟨x₀, hx₀, hi₀⟩ := hp 0
  obtain ⟨x₁, hx₁, hi₁⟩ := hp 1
  obtain ⟨x₃, hx₃, hi₃⟩ := hp 3
  have h₀ : (x₀ i : ℤ) = 0 := by
    simpa using congrArg (fun t : Fin 4 => (t : ℤ)) hi₀
  have h₁ : (x₁ i : ℤ) = 1 := by
    simpa using congrArg (fun t : Fin 4 => (t : ℤ)) hi₁
  have h₃ : (x₃ i : ℤ) = 3 := by
    simpa using congrArg (fun t : Fin 4 => (t : ℤ)) hi₃
  have haff (z : Grid n) (hz : z ∈ s) (j : Fin n) :
      (z j : ℤ) = (x₀ j : ℤ) + (z i : ℤ) * ((x₁ j : ℤ) - (x₀ j : ℤ)) := by
    have h0 := hline x₀ hx₀ j i
    have h1 := hline x₁ hx₁ j i
    rw [h₀] at h0
    rw [h₁] at h1
    have hm : ((z j : ℤ) - ((x₀ j : ℤ) + (z i : ℤ) * ((x₁ j : ℤ) - (x₀ j : ℤ)))) *
        ((b i : ℤ) - (a i : ℤ)) = 0 := by
      linear_combination hline z hz j i - h0 - (z i : ℤ) * (h1 - h0)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hd)
  have hc (j : Fin n) :
      ∃ u : Symbol, ∀ t : Fin 4,
        (value u t : ℤ) = (x₀ j : ℤ) + (t : ℤ) * ((x₁ j : ℤ) - (x₀ j : ℤ)) :=
    classify _ _ _ (by simpa [h₃] using haff x₃ hx₃ j)
  choose w hw using hc
  have he (z : Grid n) (hz : z ∈ s) : point w (z i) = z := by
    funext j
    exact Fin.ext (by exact_mod_cast (hw j (z i)).trans (haff z hz j).symm)
  refine ⟨w, ?_, ?_⟩
  · cases e : w i with
    | inl c =>
      have e₀ := congrFun (he x₀ hx₀) i
      have e₁ := congrFun (he x₁ hx₁) i
      simp [point, e, value, hi₀, hi₁] at e₀ e₁
      exact ((by decide : (0 : Fin 4) ≠ 1) (e₀.symm.trans e₁)).elim
    | inr b => exact ⟨i, b, e⟩
  · ext z
    rw [mem_entries]
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨y, hy, hiy⟩ := hp t
      have hyPoint : point w t = y := by simpa [hiy] using he y hy
      rwa [hyPoint]
    · intro hz
      exact ⟨z i, he z hz⟩

private def flip : Symbol → Symbol
  | .inl a => .inl a
  | .inr b => .inr (!b)

private def reverse {n : ℕ} (w : Word n) : Word n := fun i => flip (w i)

private theorem reverse_reverse {n : ℕ} (w : Word n) : reverse (reverse w) = w := by
  funext i
  rcases h : w i with a | b <;> simp [reverse, flip, h]

private theorem reverse_point {n : ℕ} (w : Word n) (t : Fin 4) :
    point (reverse w) t = point w t.rev := by
  funext i
  rcases h : w i with a | (_ | _) <;> simp [point, reverse, flip, value, h]

private theorem entries_reverse {n : ℕ} (w : Word n) : entries (reverse w) = entries w := by
  ext z
  simp only [mem_entries, reverse_point]
  exact ⟨fun ⟨t, ht⟩ => ⟨t.rev, ht⟩, fun ⟨t, ht⟩ => ⟨t.rev, by simpa using ht⟩⟩

private theorem reverse_active {n : ℕ} {w : Word n} (h : active w) : active (reverse w) := by
  obtain ⟨i, b, hb⟩ := h
  exact ⟨i, !b, by simp [reverse, flip, hb]⟩

private theorem reverse_ne {n : ℕ} {w : Word n} (h : active w) : w ≠ reverse w := by
  obtain ⟨i, b, hb⟩ := h
  intro he
  have hi := congrFun he i
  cases b <;> simp [reverse, flip, hb] at hi

private theorem entries_fiber {n : ℕ} {w v : Word n} (hw : active w)
    (hv : entries v = entries w) : v = w ∨ v = reverse w := by
  obtain ⟨i, b, hb⟩ := hw
  have h_aligned (u : Word n) (hu : entries u = entries w) (hi : u i = .inr b) : u = w := by
    have hp (t : Fin 4) : point u t = point w t := by
      have hm : point u t ∈ entries w := by
        rw [← hu]
        exact mem_entries.mpr ⟨t, rfl⟩
      obtain ⟨k, hk⟩ := mem_entries.mp hm
      have hkt : k = t := value_active_injective b (by simpa [point, hb, hi] using congrFun hk i)
      exact hkt ▸ hk.symm
    funext j
    exact symbol_injective (Prod.ext (congrFun (hp 0) j) (congrFun (hp 3) j))
  have hvar : ∃ c, v i = .inr c := by
    cases hi : v i with
    | inr c => exact ⟨c, rfl⟩
    | inl a =>
      have hp (t : Fin 4) : value (.inr b) t = a := by
        have hm : point w t ∈ entries v := by
          rw [hv]
          exact mem_entries.mpr ⟨t, rfl⟩
        obtain ⟨k, hk⟩ := mem_entries.mp hm
        simpa [point, hb, hi, value] using (congrFun hk i).symm
      exact ((by decide : (0 : Fin 4) ≠ 1)
        (value_active_injective b ((hp 0).trans (hp 1).symm))).elim
  obtain ⟨c, hc⟩ := hvar
  by_cases he : c = b
  · exact Or.inl (h_aligned v hv (by simpa [he] using hc))
  · right
    have hf : (!c) = b := by cases c <;> cases b <;> simp_all
    have hrev := h_aligned (reverse v) ((entries_reverse v).trans hv) (by
      change flip (v i) = .inr b
      rw [hc]
      exact congrArg Sum.inr hf)
    simpa only [reverse_reverse] using congrArg reverse hrev

private noncomputable def words (n : ℕ) : Finset (Word n) := by
  classical
  exact Finset.univ.filter active

private noncomputable def lines (n : ℕ) : Finset (Finset (Grid n)) := by
  classical
  exact Finset.univ.filter (fun s => s.card = 4 ∧ OnLine s)

private theorem words_card (n : ℕ) : (words n).card = 6 ^ n - 4 ^ n := by
  classical
  let f : Grid n → Word n := fun a i => .inl (a i)
  have hf : Function.Injective f := by
    intro x y h
    funext i
    exact Sum.inl.inj (congrFun h i)
  have hrest : (Finset.univ.filter (fun w : Word n => ¬ active w)) =
      (Finset.univ : Finset (Grid n)).image f := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      have hi (i : Fin n) : ∃ a : Fin 4, w i = .inl a := by
        cases e : w i with
        | inl a => exact ⟨a, rfl⟩
        | inr b => exact (h ⟨i, b, e⟩).elim
      choose a ha using hi
      exact ⟨a, funext fun i => (ha i).symm⟩
    · rintro ⟨a, rfl⟩ ⟨i, b, hb⟩
      cases hb
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Word n)))
    (p := active)
  rw [hrest, Finset.card_image_of_injective _ hf] at h
  simpa [words, Fintype.card_pi_const] using (Nat.eq_sub_of_add_eq h)

private theorem twice_lines (n : ℕ) : (words n).card = (lines n).card * 2 := by
  classical
  have hmap : ∀ w ∈ words n, entries w ∈ lines n := by
    intro w hw
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, entries_valid (Finset.mem_filter.mp hw).2⟩
  have htwo (s : Finset (Grid n)) (hs : s ∈ lines n) :
      ((words n).filter fun w => entries w = s).card = 2 := by
    have hls := (Finset.mem_filter.mp hs).2
    obtain ⟨w, hw, he⟩ := entries_surj hls.1 hls.2
    have hpair : ((words n).filter fun v => entries v = s) = {w, reverse w} := by
      ext v
      simp only [Finset.mem_filter, words, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨_, hv⟩
        exact entries_fiber hw (hv.trans he.symm)
      · rintro (rfl | rfl)
        · exact ⟨hw, he⟩
        · exact ⟨reverse_active hw, (entries_reverse w).trans he⟩
    rw [hpair]
    exact Finset.card_pair_eq_two_iff.mpr (reverse_ne hw)
  rw [Finset.card_eq_sum_card_fiberwise (f := entries) (t := lines n) hmap]
  calc
    _ = ∑ s ∈ lines n, (2 : ℕ) := Finset.sum_congr rfl htwo
    _ = _ := by simp

end OMA.S_oeis_a081199

open OMA.S_oeis_a081199 in
theorem OMA.solution : type_of% @OMA.S_oeis_a081199.main := by
  intro n
  classical
  have hc : lineCount n = (lines n).card := by
    unfold lineCount
    rw [← Set.ncard_coe_finset (lines n)]
    congr 1
    ext s
    simp [lines, OnLine]
  rw [hc]
  have h := (twice_lines n).symm.trans (words_card n)
  omega
