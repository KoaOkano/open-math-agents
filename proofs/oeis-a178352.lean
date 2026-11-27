import OMAStatements.S_oeis_a178352

/-!
Count ordered collinear triples by the affine parameter of the third point on
the line through the first two. A coordinate where the first two points differ
determines this parameter as a rational number. For a fixed parameter, choices
in the n coordinates are independent. Exactly 6^n choices are constant triples.

Enumerating the 216 possible columns gives 27 parameters. Their numbers of
admissible columns are 8, 10, 12 and 18, with multiplicities 12, 6, 6 and 3.
Each collinear three-element subset has six orderings.
-/

namespace SixPointGrid

open Finset OMA.S_oeis_a178352

private abbrev Grid (n : ℕ) := Fin n → Fin 6
private abbrev Triple (n : ℕ) := Fin 3 → Grid n
private abbrev Column := Fin 3 → Fin 6
private abbrev val (x : Fin 6) : ℚ := x.val
private def col {n} (f : Triple n) (j : Fin n) : Column := fun i => f i j
private def slope (u : Column) : ℚ := (val (u 2) - val (u 0)) / (val (u 1) - val (u 0))
private def slopes : Finset ℚ := (((univ : Finset Column).image slope).erase 0).erase 1
private def fits (t : ℚ) (u : Column) := val (u 2) - val (u 0) = t * (val (u 1) - val (u 0))
private instance (t u) : Decidable (fits t u) := by unfold fits; infer_instance
private def options (t : ℚ) : Finset Column := univ.filter (fits t)
private abbrev Pack (n : ℕ) (t : ℚ) := Fin n → ↥(options t)
private def unpack {n t} (g : Pack n t) : Triple n := fun i j => (g j).val i
private abbrev Off (n : ℕ) (t : ℚ) := {g : Pack n t // unpack g 0 ≠ unpack g 1}

private theorem val_inj : Function.Injective val := by
  intro a b h; apply Fin.ext; unfold val at h; exact_mod_cast h

private theorem coord_ne {n} {p q : Grid n} (h : p ≠ q) : ∃ j, p j ≠ q j := by
  by_contra! hc
  exact h (funext hc)

private theorem unpack_inj {n t} : Function.Injective (@unpack n t) := by
  intro g h he; funext j; apply Subtype.ext; funext i
  exact congrFun (congrFun he i) j

private theorem unpack_fits {n t} (g : Pack n t) (j : Fin n) : fits t (col (unpack g) j) :=
  (mem_filter.mp (g j).property).2

private theorem slope_nontrivial {t : ℚ} (ht : t ∈ slopes) : t ≠ 0 ∧ t ≠ 1 :=
  ⟨(mem_erase.mp (mem_erase.mp ht).2).1, (mem_erase.mp ht).1⟩

private theorem unpack_injective {n t} (ht : t ∈ slopes) (g : Off n t) : Function.Injective (unpack g.val) := by
  let f := unpack g.val
  have h01 : f 0 ≠ f 1 := g.property
  obtain ⟨j,hj⟩ := coord_ne h01
  have hn : val (f 1 j) - val (f 0 j) ≠ 0 := sub_ne_zero.mpr (fun h => hj (val_inj h).symm)
  have eqn := unpack_fits g.val j
  change val (f 2 j) - val (f 0 j) = t * (val (f 1 j) - val (f 0 j)) at eqn
  obtain ⟨ht0,ht1⟩ := slope_nontrivial ht
  have h02 : f 0 ≠ f 2 := by
    intro he; rw [← he,sub_self] at eqn
    exact (mul_ne_zero ht0 hn) eqn.symm
  have h12 : f 1 ≠ f 2 := by
    intro he; rw [← he] at eqn
    apply ht1; apply mul_right_cancel₀ hn; simpa using eqn.symm
  change Function.Injective f
  intro i k he
  fin_cases i <;> fin_cases k <;> simp_all

private def realSet {n} (f : Triple n) : Set (Fin n → ℝ) := Set.range (fun i => toReal (f i))
private abbrev Ordered (n : ℕ) := {f : Triple n // Function.Injective f ∧ Collinear ℝ (realSet f)}

private theorem collinear_pack {n t} (g : Pack n t) : Collinear ℝ (realSet (unpack g)) := by
  let f := unpack g
  refine (collinear_iff_exists_forall_eq_smul_vadd _).mpr ?_
  refine ⟨toReal (f 0), toReal (f 1) - toReal (f 0), ?_⟩
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact ⟨0, by simp [f]⟩
  · exact ⟨1, by simp [f]⟩
  · refine ⟨(t : ℝ), ?_⟩
    funext j
    have h := unpack_fits g j
    change val (f 2 j) - val (f 0 j) = t * (val (f 1 j) - val (f 0 j)) at h
    have e : (toReal (f 2) j) - toReal (f 0) j = (t : ℝ) * (toReal (f 1) j - toReal (f 0) j) := by
      have c := congrArg (fun z : ℚ => (z : ℝ)) h
      simpa [toReal, val] using c
    change toReal (f 2) j = (t : ℝ) * (toReal (f 1) j - toReal (f 0) j) + toReal (f 0) j
    linarith

private theorem slope_exists {n} (f : Ordered n) : ∃ t ∈ slopes, ∀ j, fits t (col f.val j) := by
  let p := f.val
  have h01 : p 0 ≠ p 1 := f.property.1.ne (by decide)
  obtain ⟨j,hj⟩ := coord_ne h01
  have hr : toReal (p 0) ≠ toReal (p 1) := by
    intro h; apply hj; apply Fin.ext; have e := congrFun h j; unfold toReal at e; exact_mod_cast e
  have mem (i : Fin 3) : toReal (p i) ∈ realSet p := ⟨i,rfl⟩
  have line := f.property.2.mem_affineSpan_of_mem_of_ne (mem 0) (mem 1) (mem 2) hr
  obtain ⟨r,eq⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp line
  have coord (k : Fin n) : toReal (p 2) k - toReal (p 0) k = r * (toReal (p 1) k - toReal (p 0) k) := by
    rw [AffineMap.lineMap_apply_module'] at eq
    have h := congrFun eq k
    change r * (toReal (p 1) k - toReal (p 0) k) + toReal (p 0) k = toReal (p 2) k at h
    linarith
  let t := slope (col p j)
  have ht : (t : ℝ) = r := by
    dsimp [t, slope, col, val]; push_cast
    apply (div_eq_iff ?_).mpr (coord j)
    apply sub_ne_zero.mpr; intro he; apply hj; apply Fin.ext; unfold toReal at he; exact_mod_cast he.symm
  have all (k) : fits t (col p k) := by
    unfold fits val col
    have h := coord k
    rw [← ht] at h
    unfold toReal at h; exact_mod_cast h
  have tor {v : Fin 3} (hv : v = 0 ∨ v = 1) (he : t = (v.val : ℚ)) : p 2 = p v := by
    funext k; apply val_inj
    have h := all k
    change val (p 2 k) - val (p 0 k) = t * (val (p 1 k)-val (p 0 k)) at h
    rcases hv with rfl|rfl
    · have hz : t = 0 := by simpa using he
      rw [hz,zero_mul] at h
      exact sub_eq_zero.mp h
    · have ho : t = 1 := by simpa using he
      rw [ho,one_mul] at h
      exact sub_left_inj.mp h
  refine ⟨t, mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, mem_image.mpr ⟨col p j, mem_univ _,rfl⟩⟩⟩, all⟩
  · intro h; exact f.property.1.ne (by decide : (2 : Fin 3) ≠ 1) (tor (Or.inr rfl) h)
  · intro h; exact f.property.1.ne (by decide : (2 : Fin 3) ≠ 0) (tor (Or.inl rfl) h)

private def send {n} (v : Σ t : ↥slopes, Off n t.val) : Ordered n :=
  ⟨unpack v.2.val, unpack_injective v.1.property v.2, collinear_pack _⟩

private theorem send_bijective (n) : Function.Bijective (@send n) := by
  constructor
  · rintro ⟨⟨t,ht⟩,g⟩ ⟨⟨s,hs⟩,h⟩ eq
    have he : unpack g.val = unpack h.val := congrArg Subtype.val eq
    obtain ⟨j,hj⟩ := coord_ne g.property
    have e1 := unpack_fits g.val j
    have e2 := unpack_fits h.val j
    rw [← he] at e2
    let f := unpack g.val
    change val (f 2 j) - val (f 0 j) = t * (val (f 1 j) - val (f 0 j)) at e1
    change val (f 2 j) - val (f 0 j) = s * (val (f 1 j) - val (f 0 j)) at e2
    have ts : t = s := mul_right_cancel₀ (sub_ne_zero.mpr (fun h => hj (val_inj h).symm)) (e1.symm.trans e2)
    subst s
    have gh : g = h := Subtype.ext (unpack_inj he)
    cases gh
    rfl
  · intro f
    obtain ⟨t,ht,e⟩ := slope_exists f
    let g : Pack n t := fun j => ⟨col f.val j, mem_filter.mpr ⟨mem_univ _,e j⟩⟩
    have h : unpack g 0 ≠ unpack g 1 := f.property.1.ne (by decide : (0 : Fin 3) ≠ 1)
    exact ⟨⟨⟨t,ht⟩,⟨g,h⟩⟩,Subtype.ext rfl⟩

private abbrev Diag (n : ℕ) (t : ℚ) := {g : Pack n t // unpack g 0 = unpack g 1}

private theorem diagonal_const {n t} (g : Diag n t) (i : Fin 3) : unpack g.val i = unpack g.val 0 := by
  fin_cases i
  · rfl
  · exact g.property.symm
  · funext j; apply val_inj
    have h := unpack_fits g.val j
    change val (unpack g.val 2 j) - val (unpack g.val 0 j) =
      t * (val (unpack g.val 1 j) - val (unpack g.val 0 j)) at h
    rw [← g.property,sub_self,mul_zero] at h
    exact sub_eq_zero.mp h

private theorem diagonal_bijective (n t) :
    Function.Bijective (fun g : Diag n t => unpack g.val 0) := by
  constructor
  · intro g h he
    apply Subtype.ext
    apply unpack_inj
    funext i
    exact (diagonal_const g i).trans (he.trans (diagonal_const h i).symm)
  · intro p
    let g : Pack n t := fun j => ⟨fun _ => p j, mem_filter.mpr ⟨mem_univ _,by simp [fits]⟩⟩
    exact ⟨⟨g,rfl⟩,rfl⟩

private theorem count_off (n t) : Nat.card (Off n t) + 6^n = (options t).card ^ n := by
  classical
  have h := Fintype.card_congr (Equiv.ofBijective _ (diagonal_bijective n t))
  have hd : Fintype.card (Diag n t) = 6^n := by simpa [Fintype.card_fun] using h
  have ct : Fintype.card (Pack n t) = (options t).card ^ n := by simp
  have le := Fintype.card_subtype_le (fun g : Pack n t => unpack g 0 = unpack g 1)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  change Fintype.card (Diag n t) ≤ Fintype.card (Pack n t) at le
  change Fintype.card (Pack n t) - Fintype.card (Diag n t) + 6^n = _
  omega

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem tally : slopes.val.map (fun t => (options t).card) =
    Multiset.replicate 12 8 + Multiset.replicate 6 10 +
    Multiset.replicate 6 12 + Multiset.replicate 3 18 := by decide +kernel

private theorem slope_count : slopes.card = 27 := by
  have h := congrArg Multiset.card tally
  simpa using h

private theorem count_options (n : ℕ) : ∑ t ∈ slopes, (options t).card ^ n =
    12*8^n + 6*10^n + 6*12^n + 3*18^n := by
  have h := congrArg (fun m : Multiset ℕ => (m.map (fun k => k^n)).sum) tally
  simp only [Multiset.map_map, Multiset.map_add, Multiset.map_replicate, Multiset.sum_add,
    Multiset.sum_replicate, nsmul_eq_mul] at h
  exact h

private theorem ordered_count (n : ℕ) : Nat.card (Ordered n) + 27 * 6^n =
    12*8^n + 6*10^n + 6*12^n + 3*18^n := by
  classical
  have e := Nat.card_congr (Equiv.ofBijective _ (send_bijective n))
  rw [Nat.card_sigma] at e
  have h := Finset.sum_congr (s₁ := (univ : Finset ↥slopes)) rfl
    (fun (t : ↥slopes) _ => count_off n t.val)
  rw [Finset.sum_add_distrib, e] at h
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_coe,slope_count,nsmul_eq_mul,
    Finset.sum_coe_sort slopes (fun t => (options t).card ^ n),count_options] at h
  exact h

private abbrev Shapes (n : ℕ) := {s : Finset (Grid n) //
  s.card = 3 ∧ Collinear ℝ (toReal '' (s : Set (Grid n)))}

private def vertices {n} (f : Triple n) : Finset (Grid n) := univ.image f

private theorem real_vertices {n} (f : Triple n) :
    toReal '' (vertices f : Set (Grid n)) = realSet f := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨i,_,rfl⟩ := mem_image.mp hq
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨f i,mem_image.mpr ⟨i,mem_univ _,rfl⟩,rfl⟩

private def labelPoints {n} {s : Shapes n} (e : Fin 3 ≃ ↥s.val) : Triple n :=
  fun i => (e i).val

private theorem labelled_vertices {n} {s : Shapes n} (e : Fin 3 ≃ ↥s.val) :
    vertices (labelPoints e) = s.val := by
  ext p
  constructor
  · intro h
    obtain ⟨i,_,rfl⟩ := mem_image.mp h
    exact (e i).property
  · intro hp
    obtain ⟨i,hi⟩ := e.surjective ⟨p,hp⟩
    exact mem_image.mpr ⟨i,mem_univ _,congrArg Subtype.val hi⟩

private def enumerate {n} (b : Σ s : Shapes n, Fin 3 ≃ ↥s.val) : Ordered n := by
  refine ⟨labelPoints b.2,Subtype.val_injective.comp b.2.injective,?_⟩
  rw [← real_vertices, labelled_vertices]
  exact b.1.property.2

private theorem enumerate_bijective (n) : Function.Bijective (@enumerate n) := by
  constructor
  · rintro ⟨s,e⟩ ⟨v,g⟩ he
    have hf : labelPoints e = labelPoints g := congrArg Subtype.val he
    have sv : s = v := Subtype.ext ((labelled_vertices e).symm.trans
      ((congrArg vertices hf).trans (labelled_vertices g)))
    subst v
    have eg : e = g := Equiv.ext (fun i => Subtype.ext (congrFun hf i))
    cases eg
    rfl
  · intro f
    have size : (vertices f.val).card = 3 := by
      rw [vertices,card_image_of_injective _ f.property.1]
      simp
    let s : Shapes n := ⟨vertices f.val,size,by rw [real_vertices]; exact f.property.2⟩
    let g (i : Fin 3) : ↥s.val := ⟨f.val i,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩
    have hg : Function.Bijective g := by
      refine ⟨fun i j h => f.property.1 (congrArg Subtype.val h),?_⟩
      rintro ⟨p,hp⟩
      obtain ⟨i,_,hi⟩ := mem_image.mp hp
      exact ⟨i,Subtype.ext hi⟩
    exact ⟨⟨s,Equiv.ofBijective g hg⟩,Subtype.ext rfl⟩

private theorem six_orderings (n : ℕ) : Nat.card (Ordered n) = 6 * a n := by
  classical
  have six (s : Shapes n) : Nat.card (Fin 3 ≃ ↥s.val) = 6 := by
    let e : Fin 3 ≃ ↥s.val := Fintype.equivOfCardEq (by simpa using s.property.1.symm)
    rw [Nat.card_eq_fintype_card, Fintype.card_equiv e]
    decide
  have h := Nat.card_congr (Equiv.ofBijective _ (enumerate_bijective n))
  rw [Nat.card_sigma] at h
  simp_rw [six] at h
  have shape_count : Nat.card (Shapes n) = a n := rfl
  rwa [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, shape_count,
    nsmul_eq_mul, mul_comm, eq_comm] at h

end SixPointGrid

open SixPointGrid OMA.S_oeis_a178352

theorem OMA.solution : type_of% @OMA.S_oeis_a178352.main := by
  intro n
  have h := ordered_count n
  rw [six_orderings] at h
  have e : 6 * (a n : ℤ) + 27 * 6^n = 12*8^n + 6*10^n + 6*12^n + 3*18^n := by
    exact_mod_cast h
  omega
