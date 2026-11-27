import OMAReductions.R_Green14_W_3_17_R2

/-! # Even palindromes avoiding progressions of lengths three and seventeen

Table 6 of Ahmed, Kullmann and Snevily (arXiv:1102.5433) gives 278 as
the largest even avoiding length. An explicit coloring attains it. At
length 280 the four cases distinguish the colors near the reflection
axis, in zero-based coordinates. Centered restriction gives the entire
even spectrum. Lean formalization by @KoaOkano. -/

namespace OMA.R_Green14_W_3_17_R2_H2_R1

def H1 : Prop := ∀ c : Nat → Bool,
  (∀ x < 280, c (280-1-x)=c x) →
  (∀ (b : Bool) (a d : Nat), 0 < d → a+((if b then 17 else 3)-1)*d < 280 → ∃ t < (if b then 17 else 3), c (a+t*d)=b) →
  c 139=true → False

def H2 : Prop := ∀ c : Nat → Bool,
  (∀ x < 280, c (280-1-x)=c x) →
  (∀ (b : Bool) (a d : Nat), 0 < d → a+((if b then 17 else 3)-1)*d < 280 → ∃ t < (if b then 17 else 3), c (a+t*d)=b) →
  c 139=false → (c 134=true ∨ c 135=true) → False

def H3 : Prop := ∀ c : Nat → Bool,
  (∀ x < 280, c (280-1-x)=c x) →
  (∀ (b : Bool) (a d : Nat), 0 < d → a+((if b then 17 else 3)-1)*d < 280 → ∃ t < (if b then 17 else 3), c (a+t*d)=b) →
  c 139=false → c 134=false → c 135=false → (c 138=true ∨ c 136=true) → False

def H4 : Prop := ∀ c : Nat → Bool,
  (∀ x < 280, c (280-1-x)=c x) →
  (∀ (b : Bool) (a d : Nat), 0 < d → a+((if b then 17 else 3)-1)*d < 280 → ∃ t < (if b then 17 else 3), c (a+t*d)=b) →
  c 139=false → c 134=false → c 135=false → c 138=false → c 136=false → False

private theorem witness : (∃ c : Nat → Bool, (∀ x < 278, c (278-1-x)=c x) ∧ (∀ (b : Bool) (a d : Nat), 0 < d → a+((if b then 17 else 3)-1)*d < 278 → ∃ t < (if b then 17 else 3), c (a+t*d)=b)) := by
  let c (i : Nat) := (0x2041100204100c00a04050080050000803300400028004028081400c0208100220810 : Nat).testBit i
  refine ⟨c, ?_, ?_⟩
  · intro x hx
    exact OMA.R_Green14_W_3_17_R2.lower_reflects ⟨x,hx⟩
  · intro b a d hd bound
    have one : 1 ≤ (if b then 17 else 3)-1 := by cases b <;> decide
    have cmp : d ≤ ((if b then 17 else 3)-1)*d := by simpa using Nat.mul_le_mul_right d one
    obtain ⟨t,ht⟩ := OMA.R_Green14_W_3_17_R2.lower_coloring b ⟨a,by omega⟩ ⟨d,by omega⟩ hd bound
    exact ⟨t.val,t.isLt,ht⟩

private theorem restrict (n m s : Nat) (eqn : m+2*s=n) (h : (∃ c : Nat → Bool, (∀ x < n, c (n-1-x)=c x) ∧ (∀ (b : Bool) (a d : Nat), 0 < d → a+((if b then 17 else 3)-1)*d < n → ∃ t < (if b then 17 else 3), c (a+t*d)=b))) :
    (∃ c : Nat → Bool, (∀ x < m, c (m-1-x)=c x) ∧ (∀ (b : Bool) (a d : Nat), 0 < d → a+((if b then 17 else 3)-1)*d < m → ∃ t < (if b then 17 else 3), c (a+t*d)=b)) := by
  obtain ⟨c,hp,ha⟩ := h
  refine ⟨fun x => c (x+s),?_,?_⟩
  · intro x hx
    change c (m-1-x+s)=c (x+s)
    rw [show m-1-x+s=n-1-(x+s) by omega]
    exact hp _ (by omega)
  · intro b a d hd he
    obtain ⟨t,ht,col⟩ := ha b (a+s) d hd (by omega)
    exact ⟨t,ht,by simpa only [Nat.add_right_comm a (t*d) s] using col⟩

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_17_R2.H2 := by
  intro first second third fourth n parity
  constructor
  · intro good
    by_contra! large
    obtain ⟨c,pal,avoid⟩ := restrict n 280 ((n-280)/2) (by omega) good
    cases a : c 139 with
    | true => exact first c pal avoid a
    | false =>
      cases b : c 134 with
      | true => exact second c pal avoid a (Or.inl b)
      | false =>
        cases e : c 135 with
        | true => exact second c pal avoid a (Or.inr e)
        | false =>
          cases f : c 138 with
          | true => exact third c pal avoid a b e (Or.inl f)
          | false =>
            cases g : c 136 with
            | true => exact third c pal avoid a b e (Or.inr g)
            | false => exact fourth c pal avoid a b e f g
  · intro small
    exact restrict 278 n ((278-n)/2) (by omega) witness

end OMA.R_Green14_W_3_17_R2_H2_R1
