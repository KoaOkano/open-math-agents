import FormalConjectures.GreensOpenProblems.«14»

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
# Reflection constraints for the published value W(3,17)

Ahmed, Kullmann and Snevily, Table 6 of arXiv:1102.5433, give the
palindromic breakpoints (256,279). An odd avoiding palindrome can have
length at most 255 and an even one at most 278. The hypotheses H1 and
H2 state the two spectra.

Fold each 129-site window into a palindrome of length 257, and each
140-site window into a palindrome of length 280. Any forbidden
progression in the folded word must cross its midline if the original
word avoids both progressions. H3 is the remaining ordinary upper bound
with precisely these crossing progressions available on every window.
The lower coloring at 278 is directly checked.

The ordinary value is due to Tanbir Ahmed, Integers 10 (2010), 369–377.
The interval lemmas adapt earlier Lean work by NickLeko, Halldon and
Dominic Dabish. Reflection proof and checked integration by @KoaOkano.
-/
-- Credit: @KoaOkano

open Set Green14
open scoped Classical

namespace OMA.R_Green14_W_3_17_R2

/-- Complete spectrum of reflection-symmetric avoiding colorings at odd lengths. -/
def H1 : Prop := ∀ (n : Nat) (_ : n % 2 = 1),
  (∃ c : Nat → Bool, (∀ x < n, c (n-1-x)=c x) ∧
    ∀ (b : Bool) (a d : Nat), 0 < d → a+((if b then 17 else 3)-1)*d<n →
      ∃ t < (if b then 17 else 3), c (a+t*d)=b) ↔ n ≤ 255

/-- Complete spectrum of reflection-symmetric avoiding colorings at even lengths. -/
def H2 : Prop := ∀ (n : Nat) (_ : n % 2 = 0),
  (∃ c : Nat → Bool, (∀ x < n, c (n-1-x)=c x) ∧
    ∀ (b : Bool) (a d : Nat), 0 < d → a+((if b then 17 else 3)-1)*d<n →
      ∃ t < (if b then 17 else 3), c (a+t*d)=b) ↔ n ≤ 278

/-- Every relevant window of an avoiding coloring would have a progression
crossing the reflection axis of its extension. -/
def H3 : Prop := ∀ c : Nat → Bool,
  (∀ n h o : Nat, ((n=257 ∧ h=129) ∨ (n=280 ∧ h=140)) → o+h ≤ 279 →
    ∃ (b : Bool) (a d : Nat), 0<d ∧ a<h ∧ h≤a+(if b then 2 else 16)*d ∧
      a+(if b then 2 else 16)*d<n ∧ ∀ t≤(if b then 2 else 16),
        c (o+min (a+t*d) (n-1-(a+t*d)))=b) →
  ∃ (b : Bool) (a d : Nat), 0<d ∧ a+(if b then 2 else 16)*d<279 ∧
    ∀ t≤(if b then 2 else 16), c (a+t*d)=b

theorem mixedMonoAPGuaranteeSet_upward (k r : ℕ) {M N : ℕ} (hMN : M ≤ N)
    (hM : M ∈ mixedMonoAPGuaranteeSet k r) :
    N ∈ mixedMonoAPGuaranteeSet k r := by
  intro coloring
  let emb : Icc 1 M ↪ Icc 1 N :=
    ⟨fun x ↦ ⟨x, x.2.1, x.2.2.trans hMN⟩, by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : Icc 1 N ↦ (z : Nat)) h⟩
  let restricted : Icc 1 M → Fin 2 := fun x ↦ coloring (emb x)
  rcases hM restricted with hzero | hone
  · left
    rcases hzero with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨emb y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]
      exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy
  · right
    rcases hone with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨emb y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]
      exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy

/-- One bad coloring of `{1, ..., N}` proves the numerical lower bound
`W(k,r) ≥ N+1`. -/
private theorem W_ge_succ_of_not_mem (k r N : ℕ)
    (hne : (mixedMonoAPGuaranteeSet k r).Nonempty) (hbad : N ∉ mixedMonoAPGuaranteeSet k r) :
    N + 1 ≤ W k r := by
  rw [W]
  apply le_csInf hne
  intro b hb
  by_contra hle
  have hbN : b ≤ N := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hle)
  exact hbad (mixedMonoAPGuaranteeSet_upward k r hbN hb)

private lemma progression_at {N k a d : Nat} (hd : 0 < d)
    (c : Icc 1 N → Fin 2) (color : Fin 2)
    (bound : ∀ i : Fin k, a+i.val*d < N)
    (mono : ∀ (i : Fin k) (hi : a+i.val*d < N), c ⟨a+i.val*d+1, by constructor <;> omega⟩ = color) :
    ∃ s : Finset (Icc 1 N), ({(z : Nat) | z ∈ s}).IsAPOfLength k ∧
      ∀ z ∈ s, c z = color := by
  classical
  let value (i : Fin k) := a + i.val*d + 1
  have inj : Function.Injective value := by
    intro i j h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hd (by simpa [value] using h)
  let point : Fin k ↪ Icc 1 N := ⟨fun i => ⟨value i, by
    have := bound i
    dsimp [value]
    constructor <;> omega⟩, fun i j h => inj (congrArg Subtype.val h)⟩
  let s := Finset.univ.map point
  have eqs : ({(z : Nat) | z ∈ s} : Set Nat) = range value := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hy
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨point i,Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩,rfl⟩
  refine ⟨s, ?_, ?_⟩
  · rw [eqs]
    refine ⟨a+1,d,?_,?_⟩
    · rw [ENat.card_coe_set_eq, ← Set.image_univ, inj.encard_image]
      simp
    · ext z
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨i.val,by exact_mod_cast i.isLt,by simp [value]; omega⟩
      · rintro ⟨i,hi,rfl⟩
        exact ⟨⟨i,by exact_mod_cast hi⟩,by simp [value]; omega⟩
  · intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hz
    exact mono i (bound i)


private lemma extract_progression {N k : ℕ} (hk : 2 ≤ k) (q : ℕ → Fin 2) (col : Fin 2)
    (h : ∃ s : Finset (Icc 1 N), ({(x : ℕ) | x ∈ s}).IsAPOfLength k ∧
      ∀ x ∈ s, q (x.val-1) = col) :
    ∃ a d : Fin N, 0 < d.val ∧ a.val + (k-1)*d.val < N ∧
      ∀ i : Fin k, q (a.val + i.val*d.val) = col := by
  obtain ⟨s,⟨a,d,hcard,hset⟩,hc⟩ := h
  have term (i : ℕ) (hi : i < k) :
      ∃ x ∈ s, (x : ℕ) = a + i*d := by
    change a + i*d ∈ ({(x : ℕ) | x ∈ s} : Set ℕ)
    rw [hset]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  obtain ⟨x₀, -, hx₀⟩ := term 0 (by omega)
  simp only [Nat.zero_mul, Nat.add_zero] at hx₀
  obtain ⟨x₁, -, hx₁⟩ := term (k-1) (by omega)
  have ha : 1 ≤ a := hx₀ ▸ x₀.property.1
  have hb : a + (k-1)*d ≤ N := hx₁ ▸ x₁.property.2
  have hpos : 0 < d := by
    by_contra! hz
    have hd : d = 0 := by omega
    have heq : ({(x : ℕ) | x ∈ s} : Set ℕ) = {a} := by
      rw [hset]
      ext z
      simp only [hd, nsmul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i,hi,rfl⟩
        rfl
      · rintro rfl
        exact ⟨0, by exact_mod_cast (show 0 < k by omega), rfl⟩
    have hone : (k : ℕ∞) = 1 := by rw [← hcard, heq]; simp
    have : k = 1 := by exact_mod_cast hone
    omega
  have hd' : d ≤ (k-1)*d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ k-1 by omega)
  refine ⟨⟨a-1,by omega⟩,⟨d,by omega⟩,hpos,by change a-1+(k-1)*d < N; omega,?_⟩
  intro i
  obtain ⟨x,hx,hval⟩ := term i.val i.isLt
  have he := hc x hx
  change q (a - 1 + i.val*d) = col
  convert he using 2 <;> omega

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
/-- The bit pattern at length 278 avoids each forbidden progression. -/
theorem lower_coloring : ∀ (b : Bool) (a d : Fin 278), 0<d.val →
    a.val+((if b then 17 else 3)-1)*d.val<278 →
    ∃ t : Fin (if b then 17 else 3), (0x2041100204100c00a04050080050000803300400028004028081400c0208100220810 : Nat).testBit (a.val+t.val*d.val)=b := by
  decide +kernel

private theorem lower_witness : 278 ∉ mixedMonoAPGuaranteeSet 3 17 := by
  let q (i : ℕ) : Fin 2 := if (0x2041100204100c00a04050080050000803300400028004028081400c0208100220810 : ℕ).testBit i then 0 else 1
  intro h
  rcases h (fun x => q (x.val-1)) with hr | hb
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 3) q 0 hr
    obtain ⟨i,hi⟩ := lower_coloring false a d hd hbound
    have hval := hc i
    simp [q,hi] at hval
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 17) q 1 hb
    obtain ⟨i,hi⟩ := lower_coloring true a d hd hbound
    have hval := hc i
    simp [q,hi] at hval

private lemma idx_val (i : ℕ) (hi : i < 279) : (Fin.ofNat 279 i).val = i :=
  Nat.mod_eq_of_lt hi


set_option maxRecDepth 10000 in
/-- The same 278-position lower witness is reflection-symmetric. -/
theorem lower_reflects : ∀ i : Fin 278,
    (0x2041100204100c00a04050080050000803300400028004028081400c0208100220810 : Nat).testBit (277-i.val) = (0x2041100204100c00a04050080050000803300400028004028081400c0208100220810 : Nat).testBit i.val := by decide +kernel

private theorem boundary (odd : H1) (even : H2) (n : Nat) (hn : n=257 ∨ n=280)
    (c : Nat → Bool) (hp : ∀ x < n, c (n-1-x)=c x) :
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a+(if b then 2 else 16)*d<n ∧
      ∀ t ≤ (if b then 2 else 16), c (a+t*d)=b := by
  classical
  by_contra bad
  have ha (b : Bool) (a d : Nat) (hd : 0<d) (he : a+((if b then 17 else 3)-1)*d<n) :
      ∃ t < (if b then 17 else 3), c (a+t*d)=b := by
    by_contra! fails
    apply bad
    cases b
    · refine ⟨true,a,d,hd,he,?_⟩
      intro t ht
      exact Bool.ne_false_iff.mp (fails t (by change t<3; change t≤2 at ht; omega))
    · refine ⟨false,a,d,hd,he,?_⟩
      intro t ht
      exact Bool.eq_false_iff.mpr (fails t (by change t<17; change t≤16 at ht; omega))
  rcases hn with rfl | rfl
  · exact (by decide : ¬257≤255) ((odd 257 (by decide)).mp ⟨c,hp,ha⟩)
  · exact (by decide : ¬280≤278) ((even 280 (by decide)).mp ⟨c,hp,ha⟩)

private lemma some_progression (h₁ : H1) (h₂ : H2) (h₃ : H3) (r : Fin 279 → Bool) :
    ∃ (b : Bool) (a d : Nat), 0<d ∧ a+(if b then 2 else 16)*d<279 ∧
      ∀ t≤(if b then 2 else 16), r (Fin.ofNat 279 (a+t*d))=b := by
  let c (x : Nat) := r (Fin.ofNat 279 x)
  change ∃ (b : Bool) (a d : Nat), 0<d ∧ a+(if b then 2 else 16)*d<279 ∧
    ∀ t≤(if b then 2 else 16), c (a+t*d)=b
  by_contra bad
  apply bad
  apply h₃ c
  intro n h o sizes room
  have len : n=257 ∨ n=280 := sizes.imp And.left And.left
  have shape : 2*h-1 ≤ n ∧ n ≤ 2*h ∧ 0<h := by rcases sizes with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  let p (x : Nat) := c (o+min x (n-1-x))
  have pal (x : Nat) (hx : x<n) : p (n-1-x)=p x := by
    dsimp [p]
    rw [show n-1-(n-1-x)=x by omega,min_comm]
  obtain ⟨b,a,d,hd,bound,mono⟩ := boundary h₁ h₂ n len p pal
  let L := if b then 2 else 16
  change a+L*d<n at bound
  change ∀ t≤L, c (o+min (a+t*d) (n-1-(a+t*d)))=b at mono
  have inside (s : Nat) (fits : s+L*d<h) (all : ∀ t≤L, c (o+(s+t*d))=b) : False := by
    apply bad
    exact ⟨b,o+s,d,hd,by change o+s+L*d<279; omega,by simpa only [Nat.add_assoc] using all⟩
  have start : a<h := by
    by_contra! rev
    let s := n-1-(a+L*d)
    apply inside s (by dsimp [s]; omega)
    intro t ht
    have md := Nat.mul_le_mul_right d ht
    have hmono := mono (L-t) (Nat.sub_le _ _)
    have mirror : min (a+(L-t)*d) (n-1-(a+(L-t)*d))=s+t*d := by
      rw [Nat.sub_mul]
      dsimp [s]
      omega
    rwa [mirror] at hmono
  have stop : h≤a+L*d := by
    by_contra! fits
    apply inside a fits
    intro t ht
    have md := Nat.mul_le_mul_right d ht
    have mirror : min (a+t*d) (n-1-(a+t*d))=a+t*d := by omega
    simpa only [mirror] using mono t ht
  exact ⟨b,a,d,hd,start,stop,bound,mono⟩

theorem main : H1 → H2 → H3 → type_of% @Green14.W_3_17 := by
  intro h₁ h₂ h₃
  have upper : 279 ∈ mixedMonoAPGuaranteeSet 3 17 := by
    intro c
    let r (i : Fin 279) := decide (c ⟨i.val+1, by constructor <;> omega⟩ = 0)
    obtain ⟨b,a,d,hd,he,hm⟩ := some_progression h₁ h₂ h₃ r
    cases b
    · right
      apply progression_at (a := a) hd c 1
      · intro i
        have := Nat.mul_le_mul_right d (show i.val ≤ 16 by omega)
        simp only [Bool.false_eq_true,if_false] at he
        omega
      · intro i hi
        have hh := hm i.val (by change i.val ≤ 16; omega)
        have hx : Fin.ofNat 279 (a+i.val*d) = ⟨a+i.val*d,hi⟩ := Fin.ext (idx_val _ hi)
        rw [hx] at hh
        dsimp only [r] at hh
        have hv : c ⟨a+i.val*d+1,by constructor <;> omega⟩ ≠ 0 := of_decide_eq_false hh
        exact (show ∀ x : Fin 2, x ≠ 0 → x = 1 by decide) _ hv
    · left
      apply progression_at (a := a) hd c 0
      · intro i
        have := Nat.mul_le_mul_right d (show i.val ≤ 2 by omega)
        simp only [if_true] at he
        omega
      · intro i hi
        have hh := hm i.val (by change i.val ≤ 2; omega)
        have hx : Fin.ofNat 279 (a+i.val*d) = ⟨a+i.val*d,hi⟩ := Fin.ext (idx_val _ hi)
        rw [hx] at hh
        dsimp only [r] at hh
        exact of_decide_eq_true hh
  exact le_antisymm (Nat.sInf_le upper)
    (W_ge_succ_of_not_mem 3 17 278 ⟨279,upper⟩ lower_witness)

end OMA.R_Green14_W_3_17_R2
