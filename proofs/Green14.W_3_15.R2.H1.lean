import OMAReductions.R_Green14_W_3_15_R2

/-!
# Palindromic van der Waerden breakpoints for (3, 15)

Ahmed, Kullmann and Snevily report the breakpoints (200, 205) in Table 6
of *On the van der Waerden numbers w(2; 3, t)*, Discrete Applied
Mathematics 174 (2014). We check avoiding colorings at lengths 199 and
204 and rule out such colorings at lengths 201 and 206.

Two red positions force every site that completes a red triple to be blue.
The checker also handles progressions with just two distinct positions
after reflection. Only the long progressions forcing a red site and the
remaining binary choices need to be stored in the exhaustion trees.
-/

-- Lean formalization by @KoaOkano.

namespace PalindromicThreeFifteen
structure Rule where
  color : Bool
  mask : Nat
  deriving Inhabited


def hits (c : Nat → Bool) (r : Rule) := ∃ i, r.mask.testBit i = true ∧ c i = r.color


def pointMask (n a d : Nat) : Nat → Nat
  | 0 => 0
  | l+1 => pointMask n a d l ||| 2^(min (a+l*d) (n-1-(a+l*d)))

theorem pointMask_bit (n a d l t : Nat) (ht : t < l) :
    (pointMask n a d l).testBit (min (a+t*d) (n-1-(a+t*d))) = true := by
  induction l with
  | zero => omega
  | succ l ih =>
    rw [pointMask, Nat.testBit_or, Bool.or_eq_true]
    by_cases e : t = l
    · subst t
      right
      simp
    · exact Or.inl (ih (by omega))

def terms (k : Nat) (b : Bool) := if b then k else 3

def Avoid (n k : Nat) (c : Nat → Bool) :=
  ∀ b a d, 0 < d → a + (terms k b - 1) * d < n →
    ∃ t < terms k b, c (a + t*d) = b

def Pal (n : Nat) (c : Nat → Bool) := ∀ x < n, c (n - 1 - x) = c x

def Good (n k : Nat) := ∃ c, Pal n c ∧ Avoid n k c

private def fromAP (n k : Nat) (b : Bool) (a d : Nat) : Rule :=
  ⟨b, pointMask n a d (terms k b)⟩


theorem fromAP_hits {n k c} (hp : Pal n c) (ha : Avoid n k c) (b a d)
    (hd : 0 < d) (he : a + (terms k b - 1) * d < n) : hits c (fromAP n k b a d) := by
  obtain ⟨t, ht, hc⟩ := ha b a d hd he
  have hx : a+t*d < n :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right d (show t ≤ terms k b - 1 by omega)) a) he
  refine ⟨min (a+t*d) (n-1-(a+t*d)), pointMask_bit _ _ _ _ _ ht, ?_⟩
  rcases le_total (a+t*d) (n-1-(a+t*d)) with h | h
  · simpa only [min_eq_left h, fromAP] using hc
  · simpa only [min_eq_right h, hp _ hx, fromAP] using hc


private def maskColor (n mask x : Nat) := mask.testBit (min x (n-1-x))

private lemma ofMask {n k : Nat} (mask : Nat) (hk : 2 ≤ k)
    (test : ∀ (b : Bool) (a d : Fin n), 0 < d.val → a.val+(terms k b-1)*d.val < n →
      ∃ t : Fin (terms k b), maskColor n mask (a.val+t.val*d.val) = b) : Good n k := by
  refine ⟨maskColor n mask, ?_, ?_⟩
  · intro x hx
    simp only [maskColor, show n-1-(n-1-x) = x by omega, Nat.min_comm (n-1-x) x]
  · intro b a d hd he
    have hl : 1 ≤ terms k b - 1 := by cases b <;> simp [terms] <;> omega
    have hm : d ≤ (terms k b - 1)*d := by simpa using Nat.mul_le_mul_right d hl
    obtain ⟨t, ht⟩ := test b ⟨a, by omega⟩ ⟨d, by omega⟩ hd he
    exact ⟨t.val, t.isLt, ht⟩

/-- Removing equally many points from both ends preserves a symmetric avoiding coloring. -/
theorem restrictGood {n k : Nat} (m s : Nat) (hs : m+2*s=n) (h : Good n k) : Good m k := by
  obtain ⟨c, hp, ha⟩ := h
  refine ⟨fun x => c (x+s), ?_, ?_⟩
  · intro x hx
    change c (m-1-x+s) = c (x+s)
    rw [show m-1-x+s = n-1-(x+s) by omega]
    apply hp
    omega
  · intro b a d hd he
    obtain ⟨t, ht, hcol⟩ := ha b (a+s) d hd (by omega)
    exact ⟨t, ht, by simpa only [Nat.add_right_comm a (t*d) s] using hcol⟩


-- Two red positions force every completion to a three-term progression blue.
-- Reflection identifies a full position with its representative in the first half.
private def reflect (n x : Nat) := min x (n-1-x)

private lemma color_reflect {n c} (pal : Pal n c) {x} (h : x < n) :
    c (reflect n x) = c x := by
  rcases le_total x (n-1-x) with e|e
  · simp [reflect, min_eq_left e]
  · simpa only [reflect, min_eq_right e] using pal x h

private lemma blue_of_AP {n k c} (ha : Avoid n k c) {a d : Nat}
    (hd : 0 < d) (hb : a+2*d < n) :
    c a = false ∨ c (a+d) = false ∨ c (a+2*d) = false := by
  obtain ⟨t,ht,hit⟩ := ha false a d hd (by simpa [terms] using hb)
  change t < 3 at ht
  interval_cases t <;> simp_all

private def completions (n x y : Nat) : Nat :=
  let d := y-x
  if x < y && y < n then
    (if y+d < n then 2^(reflect n (y+d)) else 0) |||
    (if d ≤ x then 2^(reflect n (x-d)) else 0) |||
    (if d%2 = 0 then 2^(reflect n (x+d/2)) else 0)
  else 0

private def Blue (c : Nat → Bool) (m : Nat) := ∀ i, m.testBit i = true → c i = false

private lemma blue_or {c} {x y : Nat} (hx : Blue c x) (hy : Blue c y) : Blue c (x ||| y) := by
  intro i hi
  rw [Nat.testBit_or, Bool.or_eq_true] at hi
  exact hi.elim (hx i) (hy i)

private lemma blue_zero (c : Nat → Bool) : Blue c 0 := by simp [Blue]

private lemma blue_point {n c} (hp : Pal n c) {i : Nat} (hi : i < n) (h : c i = false) :
    Blue c (2^(reflect n i)) := by
  intro j hj
  rw [Nat.testBit_two_pow, decide_eq_true_eq] at hj
  subst j
  exact (color_reflect hp hi).trans h

private lemma completions_sound {n k c} (hp : Pal n c) (ha : Avoid n k c) (x y : Nat)
    (rx : c x = true) (ry : c y = true) : Blue c (completions n x y) := by
  unfold completions
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨xy,yn⟩ := h
    have hd : 0 < y-x := by omega
    apply blue_or
    · apply blue_or
      · split
        · rename_i hi
          apply blue_point hp hi
          have t := blue_of_AP ha (a := x) hd (by omega)
          rw [show x+(y-x)=y by omega, show x+2*(y-x)=y+(y-x) by omega,
            rx, ry] at t
          simpa using t
        · exact blue_zero c
      · split
        · rename_i hi
          apply blue_point hp (by omega)
          have t := blue_of_AP ha (a := x-(y-x)) hd (by omega)
          rw [show x-(y-x)+(y-x)=x by omega, show x-(y-x)+2*(y-x)=y by omega,
            rx, ry] at t
          simpa using t
        · exact blue_zero c
    · split
      · rename_i hi
        apply blue_point hp (by omega)
        have pos : 0 < (y-x)/2 := by omega
        have t := blue_of_AP ha (a := x) pos (by omega)
        rw [show x+2*((y-x)/2)=y by omega, rx, ry] at t
        simpa using t
      · exact blue_zero c
  · exact blue_zero c

private def pairMask (n p q : Nat) :=
  completions n (min p q) (max p q) ||| completions n p (n-1-q)

private lemma pair_sound {n k c} (hp : Pal n c) (ha : Avoid n k c) {p q : Nat}
    (rp : c p = true) (rq : c q = true) (hq : q < n) : Blue c (pairMask n p q) := by
  apply blue_or
  · rcases le_total p q with e|e
    · simpa only [min_eq_left e, max_eq_right e] using completions_sound hp ha p q rp rq
    · simpa only [min_eq_right e, max_eq_left e] using completions_sound hp ha q p rq rp
  · exact completions_sound hp ha _ _ rp ((hp q hq).trans rq)

-- A reflected three-term progression can have only two distinct representatives.
-- Each hint in this list is such a progression. The one uncolored bit is forced.
private def shortRule (n code : Nat) : Rule :=
  let a := code % n
  let d := code / n + 1
  if a+2*d<n then fromAP n 3 false a d else fromAP n 3 false 0 1

private lemma short_hits {n k c} (hn : 3 ≤ n) (hp : Pal n c) (ha : Avoid n k c)
    (code : Nat) : hits c (shortRule n code) := by
  unfold shortRule
  dsimp only
  split
  · exact fromAP_hits (k := k) hp ha false _ _ (Nat.succ_pos _) (by assumption)
  · exact fromAP_hits (k := k) hp ha false 0 1 (by decide) (by change 2<n; omega)

private def unaryOne (n p code : Nat) :=
  let m := (shortRule n code).mask
  let live := m ^^^ (m &&& (2^p))
  if live = 2^live.log2 then live else 0

private lemma unaryOne_sound {n k c} (hn : 3 ≤ n) (hp : Pal n c) (ha : Avoid n k c)
    {p : Nat} (rp : c p = true) (code : Nat) : Blue c (unaryOne n p code) := by
  have h := short_hits hn hp ha code
  have col : (shortRule n code).color = false := by
    unfold shortRule
    dsimp only
    split <;> rfl
  obtain ⟨j,hj,hc⟩ := h
  rw [col] at hc
  have ne : p ≠ j := by rintro rfl; simp_all
  have live : ((shortRule n code).mask ^^^ ((shortRule n code).mask &&& 2^p)).testBit j = true := by
    simp [Nat.testBit_xor, Nat.testBit_and, ne, hj]
  unfold unaryOne
  dsimp only
  split
  · rename_i eq
    intro i hi
    rw [eq, Nat.testBit_two_pow, decide_eq_true_eq] at hi live
    exact (hi ▸ live) ▸ hc
  · exact blue_zero c

private def unaryList (n p : Nat) : List Nat → Nat
  | [] => 0
  | v::vs => unaryOne n p v ||| unaryList n p vs

private lemma unary_sound {n k c} (hn : 3 ≤ n) (hp : Pal n c) (ha : Avoid n k c)
    {p : Nat} (rp : c p = true) (xs : List Nat) : Blue c (unaryList n p xs) := by
  induction xs with
  | nil => exact blue_zero c
  | cons v vs ih => exact blue_or (unaryOne_sound hn hp ha rp v) ih

private def Red (c : Nat → Bool) (r : Nat) := ∀ i, r.testBit i = true → c i = true

private def forcedPairs (n p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f+1, r =>
    if r=0 then 0 else
      let q := r.log2
      (if q<n then pairMask n p q else 0) ||| forcedPairs n p f (r % 2^q)

private lemma pairs_sound {n k c} (hp : Pal n c) (ha : Avoid n k c)
    (p f r : Nat) (rp : c p = true) (hr : Red c r) : Blue c (forcedPairs n p f r) := by
  induction f generalizing r with
  | zero => exact blue_zero c
  | succ f ih =>
    rw [forcedPairs]
    split
    · exact blue_zero c
    · rename_i nr
      apply blue_or
      · split
        · rename_i bound
          exact pair_sound hp ha rp (hr _ (Nat.testBit_log2 nr)) bound
        · exact blue_zero c
      · apply ih
        intro i hi
        rw [Nat.testBit_mod_two_pow, Bool.and_eq_true] at hi
        exact hr i hi.2

private def addedBlue (n : Nat) (unary : Nat → Nat) (r b p : Nat) :=
  b ||| unary p ||| forcedPairs n p n (r ||| 2^p)

private lemma insertRed {c r p} (hr : Red c r) (rp : c p = true) : Red c (r ||| 2^p) := by
  intro i hi
  rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq] at hi
  exact hi.elim (hr i) (fun eq => eq ▸ rp)

private lemma insertBlue {c b p} (hb : Blue c b) (bp : c p = false) : Blue c (b ||| 2^p) := by
  apply blue_or hb
  intro i hi
  rw [Nat.testBit_two_pow, decide_eq_true_eq] at hi
  exact hi ▸ bp

private structure Rules (n k : Nat) where
  unary : Nat → Nat
  unary_ok : ∀ c, Pal n c → Avoid n k c → ∀ p, c p=true → Blue c (unary p)

private lemma added_sound {n k c r b p} (U : Rules n k) (hp : Pal n c) (ha : Avoid n k c)
    (hr : Red c r) (hb : Blue c b) (rp : c p=true) : Blue c (addedBlue n U.unary r b p) :=
  blue_or (blue_or hb (U.unary_ok c hp ha p rp)) (pairs_sound hp ha _ _ _ rp (insertRed hr rp))

private def longMask (n k v : Nat) : Nat :=
  let a := v % ((n+1)/2)
  let d := v / ((n+1)/2) + 1
  if a+(k-1)*d < n then pointMask n a d k else pointMask n 0 1 k

private lemma long_hit {n k c} (hk : 0 < k) (hkn : k ≤ n) (hp : Pal n c) (ha : Avoid n k c)
    (v : Nat) : ∃ i, (longMask n k v).testBit i = true ∧ c i = true := by
  unfold longMask
  dsimp only
  split
  · exact fromAP_hits hp ha true _ _ (Nat.succ_pos _) (by assumption)
  · exact fromAP_hits hp ha true 0 1 (by decide) (by change 0+(k-1)*1<n; omega)

private def remaining (m b : Nat) := m ^^^ (m &&& b)

private lemma hit_remaining {c m b} (hb : Blue c b)
    (hm : ∃ i : Nat, m.testBit i = true ∧ c i = true) :
    ∃ i, (remaining m b).testBit i = true ∧ c i = true := by
  obtain ⟨i,hi,r⟩ := hm
  have no : b.testBit i=false := by
    cases h : b.testBit i with
    | false => rfl
    | true => simp [hb i h] at r
  exact ⟨i, by simp [remaining,Nat.testBit_xor,Nat.testBit_and,hi,no],r⟩

-- Only a long progression forcing a red coordinate has to be recorded.
private def redSteps {n k} (U : Rules n k) : Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, r, b => some (r,b)
  | f+1, stream, r, b =>
    let m := remaining (longMask n k (stream%2048)) b
    let p := m.log2
    if m = 2^p then redSteps U f (stream/2048) (r ||| 2^p) (addedBlue n U.unary r b p)
    else none

private lemma steps_sound {n k c} (U : Rules n k) (hk : 0 < k) (hkn : k ≤ n)
    (hp : Pal n c) (ha : Avoid n k c) (f stream r b rr bb : Nat)
    (hr : Red c r) (hb : Blue c b) (pass : redSteps U f stream r b = some (rr,bb)) :
    Red c rr ∧ Blue c bb := by
  induction f generalizing stream r b with
  | zero =>
    simp only [redSteps, Option.some.injEq, Prod.mk.injEq] at pass
    exact ⟨pass.1 ▸ hr, pass.2 ▸ hb⟩
  | succ f ih =>
    simp only [redSteps] at pass
    split at pass
    · rename_i eq
      obtain ⟨i,hi,ri⟩ := hit_remaining hb (long_hit hk hkn hp ha (stream%2048))
      rw [eq, Nat.testBit_two_pow, decide_eq_true_eq] at hi
      have rp := hi.symm ▸ ri
      exact ih _ _ _ (insertRed hr rp) (added_sound U hp ha hr hb rp) pass
    · contradiction

private inductive RedTree where
  | endAt (digits clash : Nat)
  | branch (digits p : Nat) (l r : RedTree)

private def redCheck {n k} (U : Rules n k) : RedTree → Nat → Nat → Bool
  | .endAt w clash, r, b =>
    match redSteps U (w.log2/11) w r b with
    | none => false
    | some (rr,bb) =>
      if clash=0 then rr &&& bb != 0 else remaining (longMask n k (clash-1)) bb == 0
  | .branch w p l t, r, b =>
    match redSteps U (w.log2/11) w r b with
    | none => false
    | some (rr,bb) => redCheck U l (rr ||| 2^p) (addedBlue n U.unary rr bb p) &&
        redCheck U t rr (bb ||| 2^p)

private def Refutes {n k} (_ : Rules n k) (r b : Nat) : Prop :=
  ∀ c, Pal n c → Avoid n k c → Red c r → Blue c b → False

private lemma checked {n k} (U : Rules n k) (hk : 0 < k) (hkn : k ≤ n) (t : RedTree) {r b}
    (pass : redCheck U t r b=true) : Refutes U r b := by
  intro c hp ha hr hb
  induction t generalizing r b with
  | endAt w clash =>
    cases e : redSteps U (w.log2/11) w r b with
    | none => simp [redCheck,e] at pass
    | some st =>
      obtain ⟨rr,bb⟩ := st
      obtain ⟨red,blue⟩ := steps_sound U hk hkn hp ha _ _ _ _ _ _ hr hb e
      simp only [redCheck,e] at pass
      split at pass
      · obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero (bne_iff_ne.mp pass)
        rw [Nat.testBit_and,Bool.and_eq_true] at hi
        simpa [blue i hi.2] using red i hi.1
      · obtain ⟨i,hi,_⟩ := hit_remaining blue (long_hit hk hkn hp ha (clash-1))
        simp [eq_of_beq pass] at hi
  | branch w p l t il it =>
    cases e : redSteps U (w.log2/11) w r b with
    | none => simp [redCheck,e] at pass
    | some st =>
      obtain ⟨rr,bb⟩ := st
      obtain ⟨red,blue⟩ := steps_sound U hk hkn hp ha _ _ _ _ _ _ hr hb e
      obtain ⟨lh,rh⟩ := Bool.and_eq_true_iff.mp (by simpa only [redCheck,e] using pass)
      cases v : c p with
      | true => exact il lh (insertRed red v) (added_sound U hp ha red blue v)
      | false => exact it rh red (insertBlue blue v)

private def cachedRules (n k : Nat) (hn : 3 ≤ n) (hints : Array (List Nat)) (values : Array Nat)
    (ok : ∀ p : Fin values.size, values[p.val]?.getD 0 = unaryList n p.val (hints[p.val]?.getD [])) :
    Rules n k where
  unary p := values[p]?.getD 0
  unary_ok := by
    intro c hp ha p hr
    by_cases h : p < values.size
    · rw [ok ⟨p,h⟩]
      exact unary_sound hn hp ha hr _
    · simpa [Array.getElem?_eq_none (by omega : values.size ≤ p)] using blue_zero c

-- Postfix words hold a node tag and a stream of long-progression indices.
private def readNode (stack : List RedTree) (word : Nat) : List RedTree :=
  let tag := word%4096
  if tag<128 then
    match stack with
    | b::r::xs => .branch (word/4096) tag r b :: xs
    | _ => []
  else .endAt (word/4096) (tag-128) :: stack

private def readTree (words : Array Nat) :=
  (words.foldl readNode []).headD (.endAt 1 0)

private def reaches {n k} (U : Rules n k) (w r b rr bb p br : Nat) :=
  match redSteps U (w.log2/11) w r b with
  | none => false
  | some (x,y) => x==rr && y==bb && addedBlue n U.unary x y p==br

private theorem join {n k} (U : Rules n k) (hk : 0<k) (hkn : k≤n) {r b}
    (w rr bb p br : Nat) (pass : reaches U w r b rr bb p br=true)
    (l : Refutes U (rr ||| 2^p) br) (t : Refutes U rr (bb ||| 2^p)) : Refutes U r b := by
  intro c hp ha hr hb
  cases e : redSteps U (w.log2/11) w r b with
  | none => simp [reaches,e] at pass
  | some st =>
    obtain ⟨x,y⟩ := st
    obtain ⟨⟨ex,ey⟩,eB⟩ := by
      simpa only [reaches,e,Bool.and_eq_true_iff,beq_iff_eq] using pass
    subst rr bb br
    obtain ⟨red,blue⟩ := steps_sound U hk hkn hp ha _ _ _ _ _ _ hr hb e
    cases v : c p with
    | false => exact t c hp ha red (insertBlue blue v)
    | true => exact l c hp ha (insertRed red v) (added_sound U hp ha red blue v)

-- Check only progressions that fit. The independent intervals of common
-- differences keep each kernel computation small.
private def allRange (p : Nat → Bool) (a : Nat) : Nat → Bool
  | 0 => true
  | k+1 => p (a+k) && allRange p a k

private def Covers (p : Nat → Bool) (a z : Nat) : Prop :=
  ∀ i, a ≤ i → i < z → p i = true

private theorem checkedRange {p} (a k : Nat) (test : allRange p a k = true) :
    Covers p a (a+k) := by
  induction k with
  | zero => intro i hlo hhi; omega
  | succ k ih =>
    obtain ⟨last, rest⟩ := Bool.and_eq_true_iff.mp test
    intro i hlo hhi
    by_cases e : i = a+k
    · simpa only [e] using last
    · exact ih rest i hlo (by omega)

private theorem mergeRanges {p a b z} (l : Covers p a b) (r : Covers p b z) :
    Covers p a z := by
  intro i hlo hhi
  rcases lt_or_ge i b with h | h
  · exact l i hlo h
  · exact r i h hhi

private def hasColor (p : Nat → Bool) : Nat → Bool
  | 0 => false
  | k+1 => p k || hasColor p k

private theorem colorExists {p} (k : Nat) (h : hasColor p k = true) :
    ∃ i < k, p i = true := by
  induction k with
  | zero => contradiction
  | succ k ih =>
    rcases Bool.or_eq_true_iff.mp h with last | rest
    · exact ⟨k, Nat.lt_succ_self _, last⟩
    · obtain ⟨i, hi, yes⟩ := ih rest
      exact ⟨i, Nat.lt_succ_of_lt hi, yes⟩

private def checkColor (n k mask : Nat) (b : Bool) (d : Nat) : Bool :=
  allRange (fun a => hasColor (fun t => maskColor n mask (a+t*d) == b) (terms k b))
    0 (n - (terms k b-1)*d)

private def checkDifference (n k mask d : Nat) : Bool :=
  checkColor n k mask false d && checkColor n k mask true d

private theorem witnessOfChecks (n k mask : Nat) (hk : 2 ≤ k)
    (pass : Covers (checkDifference n k mask) 1 n) : Good n k := by
  apply ofMask mask hk
  intro b a d hd he
  have both := Bool.and_eq_true_iff.mp (pass d.val hd d.isLt)
  have good : checkColor n k mask b d.val = true := by
    cases b
    · exact both.1
    · exact both.2
  have valid := checkedRange 0 (n-(terms k b-1)*d.val) good a.val (Nat.zero_le _) (by omega)
  obtain ⟨t, ht, hc⟩ := colorExists _ valid
  exact ⟨⟨t, ht⟩, beq_iff_eq.mp hc⟩

private def differences199 := checkDifference 199 15 0x4241000880100808243010020

set_option maxHeartbeats 3000000 in
private theorem span199_0 : Covers differences199 1 9 :=
  checkedRange 1 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span199_1 : Covers differences199 9 17 :=
  checkedRange 9 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span199_2 : Covers differences199 17 25 :=
  checkedRange 17 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span199_3 : Covers differences199 25 33 :=
  checkedRange 25 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span199_4 : Covers differences199 33 41 :=
  checkedRange 33 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span199_5 : Covers differences199 41 49 :=
  checkedRange 41 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span199_6 : Covers differences199 49 57 :=
  checkedRange 49 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span199_7 : Covers differences199 57 65 :=
  checkedRange 57 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span199_8 : Covers differences199 65 73 :=
  checkedRange 65 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span199_9 : Covers differences199 73 81 :=
  checkedRange 73 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span199_10 : Covers differences199 81 89 :=
  checkedRange 81 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span199_11 : Covers differences199 89 97 :=
  checkedRange 89 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span199_12 : Covers differences199 97 100 :=
  checkedRange 97 3 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span199_13 : Covers differences199 100 199 :=
  checkedRange 100 99 (by decide +kernel)

private theorem yes199 : Good 199 15 :=
  witnessOfChecks 199 15 0x4241000880100808243010020 (by decide) (mergeRanges (mergeRanges (mergeRanges span199_0 (mergeRanges span199_1 span199_2)) (mergeRanges (mergeRanges span199_3 span199_4) (mergeRanges span199_5 span199_6))) (mergeRanges (mergeRanges span199_7 (mergeRanges span199_8 span199_9)) (mergeRanges (mergeRanges span199_10 span199_11) (mergeRanges span199_12 span199_13))))

private def differences204 := checkDifference 204 15 0x8002005001320880090040800

set_option maxHeartbeats 3000000 in
private theorem span204_0 : Covers differences204 1 9 :=
  checkedRange 1 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span204_1 : Covers differences204 9 17 :=
  checkedRange 9 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span204_2 : Covers differences204 17 25 :=
  checkedRange 17 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span204_3 : Covers differences204 25 33 :=
  checkedRange 25 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span204_4 : Covers differences204 33 41 :=
  checkedRange 33 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span204_5 : Covers differences204 41 49 :=
  checkedRange 41 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span204_6 : Covers differences204 49 57 :=
  checkedRange 49 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span204_7 : Covers differences204 57 65 :=
  checkedRange 57 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span204_8 : Covers differences204 65 73 :=
  checkedRange 65 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span204_9 : Covers differences204 73 81 :=
  checkedRange 73 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span204_10 : Covers differences204 81 89 :=
  checkedRange 81 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span204_11 : Covers differences204 89 97 :=
  checkedRange 89 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span204_12 : Covers differences204 97 102 :=
  checkedRange 97 5 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span204_13 : Covers differences204 102 204 :=
  checkedRange 102 102 (by decide +kernel)

private theorem yes204 : Good 204 15 :=
  witnessOfChecks 204 15 0x8002005001320880090040800 (by decide) (mergeRanges (mergeRanges (mergeRanges span204_0 (mergeRanges span204_1 span204_2)) (mergeRanges (mergeRanges span204_3 span204_4) (mergeRanges span204_5 span204_6))) (mergeRanges (mergeRanges span204_7 (mergeRanges span204_8 span204_9)) (mergeRanges (mergeRanges span204_10 span204_11) (mergeRanges span204_12 span204_13))))

namespace Case201
private def hints : Array (List Nat) := #[
[19899],
[13066,19699],
[19499],
[19299],
[12667,19099],
[18899],
[18699],
[12268,18499],
[18299],
[18099],
[11869,17899],
[17699],
[17499],
[11470,17299],
[17099],
[16899],
[11071,16699],
[16499],
[16299],
[10672,16099],
[15899],
[15699],
[10273,15499],
[15299],
[15099],
[9874,14899],
[14699],
[14499],
[9475,14299],
[14099],
[13899],
[9076,13699],
[13499],
[13299],
[8677,13099],
[12899],
[12699],
[8278,12499],
[12299],
[12099],
[7879,11899],
[11699],
[11499],
[7480,11299],
[11099],
[10899],
[7081,10699],
[10499],
[10299],
[6682,10099],
[9899],
[9699],
[6283,9499],
[9299],
[9099],
[5884,8899],
[8699],
[8499],
[5485,8299],
[8099],
[7899],
[5086,7699],
[7499],
[7299],
[4687,7099],
[6899],
[6699],
[4288,6499,13066],
[6299,12667],
[6099,12268],
[3889,5899,11869],
[5699,11470],
[5499,11071],
[3490,5299,10672],
[5099,10273],
[4899,9874],
[3091,4699,9475],
[4499,9076],
[4299,8677],
[2692,4099,8278],
[3899,7879],
[3699,7480],
[2293,3499,7081],
[3299,6682],
[3099,6283],
[1894,2899,5884],
[2699,5485],
[2499,5086],
[1495,2299,4687],
[2099,4288],
[1899,3889],
[1096,1699,3490],
[1499,3091],
[1299,2692],
[697,1099,2293],
[899,1894],
[699,1495],
[298,499,1096],
[299,697],
[99,298],
[99,299,499,699,899,1099,1299,1499,1699,1899,2099,2299,2499,2699,2899,3099,3299,3499,3699,3899,4099,4299,4499,4699,4899,5099,5299,5499,5699,5899,6099,6299,6499,6699,6899,7099,7299,7499,7699,7899,8099,8299,8499,8699,8899,9099,9299,9499,9699,9899,10099,10299,10499,10699,10899,11099,11299,11499,11699,11899,12099,12299,12499,12699,12899,13099,13299,13499,13699,13899,14099,14299,14499,14699,14899,15099,15299,15499,15699,15899,16099,16299,16499,16699,16899,17099,17299,17499,17699,17899,18099,18299,18499,18699,18899,19099,19299,19499,19699,19899]]

private def values : Array Nat := #[
0x10000000000000000000000000,0x10000000080000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000000100000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000000200000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000000400000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000000800000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000001000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000002000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000004000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000008000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000010000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000020000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000040000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000080000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000100000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000200000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000400000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10000800000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10001000000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10002000000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10004000000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10008000000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10010000000000000000000000,0x10000000000000000000000000,0x10000000000000000000000000,0x10020000000000000000000002,0x10000000000000000000000010,0x10000000000000000000000080,0x10040000000000000000000400,0x10000000000000000000002000,0x10000000000000000000010000,0x10080000000000000000080000,0x10000000000000000000400000,0x10000000000000000002000000,0x10100000000000000010000000,0x10000000000000000080000000,0x10000000000000000400000000,0x10200000000000002000000000,0x10000000000000010000000000,0x10000000000000080000000000,0x10400000000000400000000000,0x10000000000002000000000000,0x10000000000010000000000000,0x10800000000080000000000000,0x10000000000400000000000000,0x10000000002000000000000000,0x11000000010000000000000000,0x10000000080000000000000000,0x10000000400000000000000000,0x12000002000000000000000000,0x10000010000000000000000000,0x10000080000000000000000000,0x14000400000000000000000000,0x10002000000000000000000000,0x10010000000000000000000000,0x18080000000000000000000000,0x10400000000000000000000000,0x12000000000000000000000000,0xfffffffffffffffffffffffff]

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def moves : Rules 201 15 :=
  cachedRules 201 15 (by decide) hints values (by decide +kernel)

private theorem finish {r b : Nat} (words : Array Nat)
    (h : redCheck moves (readTree words) r b = true) : Refutes moves r b :=
  checked moves (by decide) (by decide) _ h

private theorem branch {r b} (w rr bb p br : Nat) (pass : reaches moves w r b rr bb p br=true)
    (l : Refutes moves (rr ||| 2^p) br) (t : Refutes moves rr (bb ||| 2^p)) : Refutes moves r b :=
  join moves (by decide) (by decide) _ _ _ _ _ pass l t

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part1 : Refutes moves 0x10000000000000000000000000 0xfffffffffffffffffffffffff :=
  finish #[
4225] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part5 : Refutes moves 0x810400000000000000000000 0x17502251a10c10400000000000 :=
  finish #[
0xa6b80c84dd5d2348a,10682942,4869,13775916,11026628,28211516460,4158,4164,11075654,4183,4162,12612932,27405845640,10661955,46473695842993,
0xcc280e4010ea2f2b1,4170,4156,4680,56135299130401,25832756548,0xcc37413087d106423,4171,4153,25845777732,0x18cc369fdad648a,23958938455,4186,9330763,22693102325,
4175,4182,5164,56131322110317,46473744233796,4175,4170,0x517cbe3a90241f28427a,4141,91517185727988103,4153,4169,4183,4195,56171221897511,
52905418233155,4147,95193064886392132,4164,25833517829,5069,56135277892931,4144,57777763295910,4158,4152,0x46645a98acce61bfb5a4,25732854922,24260003236,4143,
4141,13775596,22452109849,52787592975175,4152,9330742,91384734565336183,4169,4176,4153,4882,57781302604343,0xa740fa10e91a90482,4153,10285136,
4175,4195,75754317784199527,93838525400265866,25825522732,4182,4175,4364,0x46a8e10e8cc142290546,9461840,11080747,0x1a470054890041e,57780600378396,27425052068,10306980,
11026521,9461840,4195,4183,4182,11464770,4156,4140,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part7 : Refutes moves 0x814000000000000000000000 0x1d04b670895400000000000000 :=
  finish #[
0xa8607422630bab48a,56117333889396,5164,51169532322849,0x4fe4c234a0e87a106544,4171,9031749,4162,24270536990,73853169943474550,4171,4169,4170,0xc61744ca108c09543,5164,
18498695626,4150,0xaee7551853cc09546,0x198a6ee049063b1,4162,4189,4171,26586099998,8623242,4157,4785,0xcc213b0251834d42c,4133,4187,51325676344079,
0x604a8269a28a30bab2fa,56162338386894,22550373514,44812187886330,4187,8679513,4170,4175,4171,4169,94350254077777016,49539808809649,4169,44273374368793,79524180010229928,
4171,10555592,0x86542211d42290187,4155,4169,5258,49220674139362,4142,12980796,0xb2898531630c09544,52941395305018,4171,4153,4165,8680674,
21880951158,4151,36411233862882,4153,12234825,4166,4176,23207883914,12620346,25846374965,4171,4165,0x1662d3423a8b481,4169,74109353388062020,
0x9aa4229b41d290544,12980281,12612932,9463108,4171,12235410,4126,0x18c20f1d5a843ce,8680674,4171,4169,74363838107603335,4152,4170,11464774,
4164,4148,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part9 : Refutes moves 0xc10000000000000000000000 0x17287e50c10000000000000000 :=
  finish #[
5243,12547195,9421962,4155,0x17eee80a8bab17d,11464794,4164,20884631722,18280538766,4152,25730937979,11465866,46069450765168,42762842956923,4162,
4171,4186,4156,5258,12587567,22494057795,20789589122,4150,4186,4171,12235899,25848378112,4164,9330748,4124,
20832236870,4832,12620655,4163,4155,52675528814872,4156,47939557532705,24178619123,4158,4976,24900436839,4195,12235910,9437952,
4150,4162,4156,11079770,4175,4168,5063,51167162819607,4165,22484866374,5446,13775728,10629790,4150,4186,
4168,57784452256624,4133,4188,37676797990026,5244,22695358753,18525119329,4195,11464765,4188,25847518337,11821290,13775518,11464776,
12234796,4126,98498804860621460,4170,4173,11465440,11080727,4154,4857,23482393312,4165,22661477113,0x95880aa1d468493ba,4170,4176,
10682443,11464906,22434985098,18575000711,25059848864,4140,4164,4186,17794929402,21880950856,4133,4151,4169] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part11 : Refutes moves 0x850000000000000000000000 0x1d526748d50000000000000000 :=
  finish #[
5258,5346,5258,0x65fbf77ed184e2a9148a,4161,4157,4155,57785307075532,0xbf68c2d19a5a910b5,4161,4140,13001559,0x197f18603291478,25732473679,12619815,
4141,12620615,9421962,4161,0xc095231844faef34f,4156,4140,10252852,4157,4172,5258,4961,54451673391581,10305593,10682444,
56168085328835,12620734,11841827,10194988,25845981873,4187,4163,44812189835848,27426951742,24272474801,17758982211,4170,4172,0xa918c21ce91a89487,52931717289286,
10306314,0x181210ce604930a,4173,4175,4170,4881,22683058366,4170,5070,11850682,24176648378,11075651,24270930800,11850021,51137535476870,
17752211517,4170,4172,4175,4187,36447171433798,4380,0x1986a469189f546,4180,52938265609636,4165,22584799304,4141,4148,4155,
4183,4169] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part12 : Refutes moves 0x810000000000000000000000 0x15446640810000000000000000 :=
  finish #[
21108429185,11080456,11330120,23473222487,4165,12619875,4152,94558157386879737,4297,13390610,19958415561,4165,4195,4170,52867973026452,
47505226666731,10654366,4144,49672516203846,4140,4180,5258,0xc093fc56148b4b2e7,4189,44482610263460,4172,0xc661f89ee04aef546,27424490630,54534294508870,4185,
0x8cf04b01662b4b984cd0e38a42f2,9461962,4168,4180,81288807011889828,4155,4162,4183,4195,4188,4882,8683993,4172,46425310000151,9814655,
25696130063,4147,0xb394cca44ea34b3b4,4180,13390982,11711436,9462344,4168,11055188,4183,4188,21880950883,4151,4169,5258,
9462922,4171,22332769024,38040931456138,4133,4187,52936665297466,25848377914,12980268,94832435919394018,4175,4154,56096975098624,26584502451,24270107463,
11079779,4147,11080369,11841921,10604601,94805961581982457,4164,10605692,17677013735,11465676,4140,4164,11080350,0x4143985dd025779c7312,4172,
4147,52884339561221,26586088210,4869,46250192147591,4142,11464777,4164,4882,23480788092,4165,20103324796,5244,44813739295160,4157,
23482400823,10960969,4153,4183,4195,4188,26586419870,13775518,0x900a4687564aef3ba,4164,4140,23162811248,22333153950,0x1a46d093334b370,4140,
4171,51102336009354,23482278061,77908959103865994,4187,4151,23485100874,4168,39692454601490,10960962,4183,12234851,4126,9916496,4166] (by decide +kernel)

private theorem part10 : Refutes moves 0x810000000000000000000000 0x15406640810000000000000000 :=
  branch 1 0x810000000000000000000000 0x15406640810000000000000000 90 0x1d526748d50000000000000000 (by decide +kernel) part11 part12

private theorem part8 : Refutes moves 0x810000000000000000000000 0x15006640810000000000000000 :=
  branch 1 0x810000000000000000000000 0x15006640810000000000000000 94 0x17287e50c10000000000000000 (by decide +kernel) part9 part10

private theorem part6 : Refutes moves 0x810000000000000000000000 0x15002640810000000000000000 :=
  branch 1 0x810000000000000000000000 0x15002640810000000000000000 86 0x1d04b670895400000000000000 (by decide +kernel) part7 part8

private theorem part4 : Refutes moves 0x810000000000000000000000 0x15002240810000000000000000 :=
  branch 1 0x810000000000000000000000 0x15002240810000000000000000 82 0x17502251a10c10400000000000 (by decide +kernel) part5 part6

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part15 : Refutes moves 0x250000000000000000000000 0x1d92c896750000000000000000 :=
  finish #[
25850303434,0xcbc8cc0e26289b48a,4158,27424653596,4151,27426592164,42357046797732,4151,98046253453587495,4155,27424183434,4670,12563401,21880128457,9470037,
4161,4155,0x5973492113142284211a,4168,4173,4167,11464896,98498804827037976,4174,5446,0x180348c4fae236d,11464759,90543908591695268,98482262282376327,4171,
4173,0x198ad3420aef3c1,87825588407657200,8655822,10682439,4181,54537499317069,17795314040,4156,80687392230106438,21023768631,4177,4190,4187,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part18 : Refutes moves 0x210002400000000000000000 0x17cc9894290d32c08610092400 :=
  finish #[
10174700,35362968999238,4182,35246157264292,4140,19152979270,13389980,21887681451,0x2ca9188d4726070d7349178,4138,4156,57783748415620,27425436014,4164,4140,
4182,4132,0x16928c5324c508a,0xb9174e06d0faef239,4140,0xa6406e559d315e546,4159,4151,46181656859974,19396358892,4195,0x1692408fe13c22f,0x11c730e329ae204a389e3a62ec,12619831,23485101194,
12620333,13775912,19194192936,4176,4161,4158,4140,5245,56033003213844,25847976120,4157,4158,94791002041918593,10203217,4195,
4150,4185] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part19 : Refutes moves 0x210000400000000000000000 0x15cc1886210110c00210000400 :=
  finish #[
36957398963220,0x17f1315710a4544,4185,44829152796818,19279708850,4155,52936681800451,4185,4195,47864493196614,21687628840,4188,4140,10469809,42376583467960,
9044067,11760966,24085992868,4162,20003443833,43920270734474,4176,4146,5258,5446,9471114,27425026807,4162,4176,4183,
40666130322356,22583214752,4176,22466548370,4150,4145,4195,4185,56163093721377,13390289,11781253,10203921,27382997872,4141,4162,
4155,56076261679304,4193,4185,49108625195145,75683463826543365,10555437,0x17ea84444aef23c,4140,4132,10469813,9765325,27422654529,23977546780,5540,
9749419,11834501,11464763,8687684,4174,5160,0xacd4db48d95049221,10190926,4132,52937187362023,36445510485318,10264612,4298,21687629220,21065711708,
4167,4185,4195,4182,4172,4575,23374091188,49409768223503,4164,25704612233,4182,4177,13390887,27425026987,51134929326957,
9446415,4182,4164,4167,0x1740b71d14c54dd,8688398,13390411,39464376026151,4167,4195,4182,10682444,11849813,4151,4178] (by decide +kernel)

private theorem part17 : Refutes moves 0x210000400000000000000000 0x15cc1884210110c00210000400 :=
  branch 1 0x210000400000000000000000 0x15cc1884210110c00210000400 73 0x17cc9894290d32c08610092400 (by decide +kernel) part18 part19

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part21 : Refutes moves 0x210100000000000000000000 0x15c418856d0121010000000000 :=
  finish #[
13369612,56162162971171,76957749651756165,4169,4151,5346,0xc618072f5a6cc5370,26583744699,4159,4157,24273244818,49688619499705,26584100927,4150,4164,
0x1a469ad7784141e,23481630914,4187,11466148,17712182222,4142,25009517586,0x65e9d41d699691aef427,23483176356,10306509,4177,10223677,4187,9916505,4178,
4182] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part22 : Refutes moves 0x210000000000000000000000 0x15840984610000000000000000 :=
  finish #[
56164712362269,25059848458,26586960627,8634555,4163,4162,4164,5446,27397833864,25060233281,56168013911178,4168,56168081023835,46306836906183,4158,
4164,24273245029,98108557406822771,4171,13775916,25059452324,10223678,9916475,4190,4182,0x205660b8e731315183ab094,49072798147814,0x1756cf262d233ce,10630188,4162,
4156,4168,27426592067,56165643112841,10588233,4382,4786,97828673683108889,4146,11464790,4156,4164,0x172d026613ab546,0xc09984eacddc0753e,4150,
24817669164,10883723,4162,40964613383494,4145,0x198b1856a3ab5a3,13390389,77595775634273136,47768688444742,12537901,4172,4150,4188,47495403209581,4151,
4169,24038364281,0x198acc5779d4155,21879324743,79951804135309889,23481632164,9916497,4174,4182,4190,0x16501dd3fbab235,57783780737961,4167,22426596578,25060233494,
4169,4151,4673,11850280,11850285,57782990275624,4195,11464798,4172,4180,4785,28214735422,51321775624751,4155,4183,
93852621982675988,0xa6b43f31421a7b4e6,4146,17744983060,4156,11465461,88194634284351684,4177,4187,4180,4638,51134113281143,9040824,24086340464,4150,
12235632,4146,4156,4164,0xcc27f7025a6849234,52938265625735,4168,9916489,4178,10309710,4171,4181] (by decide +kernel)

private theorem part20 : Refutes moves 0x210000000000000000000000 0x15840884610000000000000000 :=
  branch 1 0x210000000000000000000000 0x15840884610000000000000000 80 0x15c418856d0121010000000000 (by decide +kernel) part21 part22

private theorem part16 : Refutes moves 0x210000000000000000000000 0x15840884210000000000000000 :=
  branch 1 0x210000000000000000000000 0x15840884210000000000000000 70 0x15cc1884210110c00210000400 (by decide +kernel) part17 part20

private theorem part14 : Refutes moves 0x210000000000000000000000 0x15800884210000000000000000 :=
  branch 1 0x210000000000000000000000 0x15800884210000000000000000 90 0x1d92c896750000000000000000 (by decide +kernel) part15 part16

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part25 : Refutes moves 0x2010000000000400000000000 0x19e80482490010010000400010 :=
  finish #[
4838,10244869,4165,12620562,45717045011182,27384647977,12559481,11079743,4147,8635110,52939803083538,19294892817,4170,4176,4155,
4167,4161,56167823381543,10900242,12620518,10970151,4176,4181,25017353057,0x1812fe148b4824b,4156,4165,4155,27422626455,0x180902548a84222,
18031350907,56161605018944,10305616,4170,4177,4167,23474013510,8687817,11464785,4140,4172,4976,5138,0x198a3a81fcc0a46e45779ca089,4185,
4165,4688,0x1a44e7262d23541,0x180ae9820aef48a,4164,11809716,0x4cc9c598348d77b433c6,52938049143329,4167,4165,11079761,9916481,4174,4694,10311076,
10310982,22584820284,4155,25847218765,4172,4167,4185,56086127776342,43245574555044,9916505,4194,39844053972294,0xa653444fe91b91486,28212765254,9916505,
4182,0x16804ed48975488,10203638,4382,9916704,11464790,4164,4180,4976,11465374,10285558,4170,23481242008,77984551232144312,4162,
4183,4174,12620562,11027218,4183,4598,46474676990529,4180,10309706,4161,12234837,4146,4156,4176,4186] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part27 : Refutes moves 0x2010000000080000000000000 0x19e82492012002400080402080 :=
  finish #[
22683894306,19456258445,4140,18592924899,19455849507,5163,22626742844,9076793,4173,10309710,4166,19474960840,13390767,95191414830802051,4132,
56132138189839,4155,4162,47562548327186,38832016769493,4177,20640977682,22693102142,4165,95180895719236929,0x69119668a685369cc47b,4177,0x198a9ec8c2900ca,4176,4188,
4167,86564853548602501,25051075144,40743714243717,4170,4165,18960945353,0xa234eafe0e51d41d5,4185,25797661618,10224021,95185914789634603,39998554194072,4177,4167,
11464793,4164,4188,4140,4180,5446,22466528389,11079749,13390487,23482402018,4176,4167,13390583,10617591,4165,
17795314914,4140,10253074,56164853039305,4170,4167,4177,5242,39999880754309,4188,12231536,10252357,0x165c9bcaa3ab0e9,0x5cc210754a11779bd1d5,4167,
0x18c2eacdea9148a,10309690,4161,11080278,10310418,10310418,21116023570,4165,4177,4185,98461909767770985,12219618,57782201832582,10223696,9916505,
4194,4170,4186,4166,4182] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part28 : Refutes moves 0x2010000000000000000000000 0x19e80482010080400000000000 :=
  finish #[
0x83c98148dfc4c548a,12620562,38078429233923,0x174cfe1fd33d129,4194,4167,4171,10899725,10244848,4165,4838,10244848,4165,10899840,18591843649,
8987683,49638145647543,4171,4159,4165,4161,4167,4155,10970438,50910256469124,4152,13366598,18356855937,48095121969211,4154,
48096698524434,11076370,8654928,10253074,56164853039303,4170,4177,4167,4172,36102787060669,12981292,13390224,4170,10577123,10691035,
4159,11464775,0x40010f8c501177bab23c,8618372,4159,4162,10309700,10310982,93495949143070022,4155,46253597176857,4156,4694,0x3316015232ab025489d5542,0x8f298a729a1a915a4,
26588885363,77671178868274125,22693105724,4176,11466148,0x198abbd489cf42c,8675920,4171,4176,98497193234481351,4162,4167,4177,4185,4172,
11080732,0xba6699185489d5121,4181,28214735728,57776320914345,0x198abbd48ba62a3,4161,10265158,4165,4170,4185,25059463348,19213759250,25059849442,4188,
4180,0x32f844b3f800bbdd5c09248,51324936036898,0x166ee89d5918248,10309719,4171,9916501,4174,4194,4182,11849818] (by decide +kernel)

private theorem part26 : Refutes moves 0x2010000000000000000000000 0x19e80482010000400000000000 :=
  branch 1 0x2010000000000000000000000 0x19e80482010000400000000000 55 0x19e82492012002400080402080 (by decide +kernel) part27 part28

private theorem part24 : Refutes moves 0x2010000000000000000000000 0x19e80482010000000000000000 :=
  branch 1 0x2010000000000000000000000 0x19e80482010000000000000000 46 0x19e80482490010010000400010 (by decide +kernel) part25 part26

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part31 : Refutes moves 0x8010000020000000000000000 0x13a64c280980000600a0040000 :=
  finish #[
51323301983182,0xb904609fda6aef0ed,11063866,22661092011,11010121,4158,4165,22611530069,12620558,0x4dca8d66cd2691900544,4180,4150,0x17286b9c84094e3,11842311,25849512903,
11464755,24833721670,23483925521,4158,25035817714,51026359657328,4165,4177,4183,4180,11760559,0x1656e42611003c9,39283427656842,11464766,21880950868,
4151,4169,87239815410230002,27367850958,4169,87120910388737159,4156,25732862509,0x18c3025a6a79175,4151,8684677,11830598,4183,11851078,24229376951,
4140,46409129161866,4158,4151,4164,4172,20883477627,22611531078,25847948144,4150,4164,4872,5039,22553580489,57782946767712,
11759688,4155,4156,12166072,11465866,5446,22543266833,0x4cd4c04cabbda4900546,4162,4168,4150,10682452,4181,50862659506866,13390986,
19329864735,0x5cf34850c995a5bab181,4176,0x181348d0eaef23a,4148,4168,25057071674,22601986809,25001885764,4129,4143,12619975,0x5971a1812ead77a793b7,11849797,4151,
4133,4169,20881462222,87583205106840900,0x4d7462696a1a04a8e487,0xa7f200a359b348370,4183,4165,4164,4865,11723312,11309143,46188156876002,0x181348e5faef34a,0x169ae508021d225,
4162,4150,4180,12621026,13776098,49642048779016,4188,25847947953,4150,12234821,4136,9916446,4190,4194,4166,
4174] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part33 : Refutes moves 0x8012000000000000000000000 0x13bccc28a32480000000000000 :=
  finish #[
56168084583349,0xcc569abbdd590248a,4164,13390704,51320776614768,9916478,4190,5070,17725768560,17727747022,11444509,77552770435859406,4129,4153,0x166c10da6a8d3ae,
5258,11850769,22609977417,4144,4158,11079769,4175,4168] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part34 : Refutes moves 0x8010000000000000000000000 0x13a46028030000000000000000 :=
  finish #[
94095918534972548,94065581236736273,4187,0x8d08129fd05975544,4598,9696389,18610934922,9916503,0x1808d250baef541,4172,4164,4188,9917561,0x174ca39a6a30300,4187,
4151,56017409151628,0xa0ba46e5230c092f9,4864,9085703,4169,4165,4185,10580538,28213965464,4140,4188,51273400079681,13390394,27425436423,
9916460,4190,4170,51064876061834,5446,0xc6197ae9a04a782eb,4164,4150,48093544514319,4169,11079735,4154,4175,9728448,11760966,
4138,5056,9085573,12619859,4185,4297,13390986,12620746,52938235986674,4179,10687142,4194,4158,86701687858807474,11723897,
5048,97267066029249182,4179,4177,11464773,4172,4188,4180,49462273270640,44828581196719,21880950846,4151,57784568865536,10502912,5444,
0xb944093159eb4b355,4162,49436727182087,27427746567,9084972,4165,4183,4766,11035969,52714735502270,4177,12223309,21721502858,25737299268,40546273891262,
4152,24867668267,4169,4179,10195015,4163,4158,4653,20069729700,21788291159,4140,4188,4180,25850278951,52939013723456,
4178,44057024525168,0x174c6965fa8d3ae,13774917,0x86fa46bbdd34092ec,25849128256,24214909697,9409674,4146,4155,4170,4152,4140,9085060,28213965852,
4140,5258,25848365909,10682425,4163,0xb3965a2a9d328d50ebbd1834d22d,4178,4169,11079735,10309690,4176] (by decide +kernel)

private theorem part32 : Refutes moves 0x8010000000000000000000000 0x13a44028030000000000000000 :=
  branch 1 0x8010000000000000000000000 0x13a44028030000000000000000 85 0x13bccc28a32480000000000000 (by decide +kernel) part33 part34

private theorem part30 : Refutes moves 0x8010000000000000000000000 0x13a44028010000000000000000 :=
  branch 1 0x8010000000000000000000000 0x13a44028010000000000000000 65 0x13a64c280980000600a0040000 (by decide +kernel) part31 part32

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part36 : Refutes moves 0x4010000000000000000000000 0x1bf01044010000000000000000 :=
  finish #[
26586960225,0x662b4d0f2eae3089d30f,37779852424418,4148,4172,5070,26586960225,11080441,28212765552,4165,4771,0xc09734ba93c2da3b4,11079743,0x302630a8d5df48ce79d43c4,4165,
4167,4172,4175,4182,0x604ada7f068662d23541,25696945285,4155,0x17f00f541290230,4153,5258,44573246358567,4161,52931722515309,4175,25025905694,
17725428492,4173,12591299,0x166ecfe02a8453f,18516734011,4156,4148,4172,5258,4976,23483561380,4146,4156,25696843071,24128701467,
48091917516865,4162,49158503732550,12546985,22424515345,12550201,4158,28215120074,25061004708,13390892,0xb912069e604a905a4,4155,4162,4153,13390020,
25847940422,4141,13362196,17746879508,12600639,9449522,11464776,4156,4860,23483561186,4156,4869,5048,49642834531358,4177,
11006029,48091875562039,4158,4150,4178,4164,10309708,4171,4186,11466054,27425051504,4182,10506784,11834500,0xbf798aa4142230044,
4169,0x66127400b31577a913ae,87233329017459739,0xb935dea45a6a300f4,4151,10309705,4171,5258,24270087301,4162,42923151643008,0xd23812bbda69d5428,4186,4161,57784526246427,
54450097643701,0x174aa453ca87286,4165,10903634,0x29e6602efa467016f23048a,4163,93662044077233102,10265265,0x84869a8c0e79d42fa,4167,4165,4177,9150543,4185,4187,
4181] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part38 : Refutes moves 0x412000000000000000000000 0x1fa80412412480000000000000 :=
  finish #[
5164,25057416048,4164,19422704585,0x180c0d53911842b,9531797,4173,4186,13775728,9041316,0x169748e04a8729e,4144,4293,11040164,4179,
0xa8ea46bbe04912546,4188,4183,4174,45723319640208,28211975024,4165,48097489098054,28212023490,4287,57776481530638,4186,4158,4165,11079769,
4161,4168,4182,13390110,5164,9032748,4164,4159,12235418,13775590,10978234,28213138345,4170,18516338084,4165,
4150,12620211,4872,56120484053386,9510983,4177,4183,17343030214,35461499855590,13774917,25062159083,4381,23439238564,4183,4167,
11079769,4161,4168,4182,9032560,4505,25846665762,4505,11829644,4173,11464791,4164,13775728,49672493347696,12620558,
4152,25846424601,44541256175789,0xa7905f48d974092a1,25846448530,4180,4188,4179,4183,4174,4976,17653855549,13774917,4976,11068272,
8642758,4170,4165,11079751,4161,4168,4182,93648206187533634,22492549403,4882,11068836,4171,57778224853252,4188,4183,
4185,0x181331548bab419,12235914,20831605705,4376,9031964,4176,4158,4168,19422319467,28213567887,4186,12235018,12198670,37683330675082,
22691426698,4161,4159,11464770,4180,4140,4164,9379900,4136,11849780,4142] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part39 : Refutes moves 0x410000000000000000000000 0x1fa82410410000000000000000 :=
  finish #[
20882707389,56097416884894,11466054,10682436,5164,49692061659321,11079748,4154,4175,44810615534310,11465490,4148,17711043440,9486529,4174,
10309701,4171,0x94d4cb48d984090fa,51239036433263,4161,36147781629066,4156,41309074026892,11080643,52932511039973,4173,4168,10683342,4151,4169,
44811401208005,45806140437169,4146,4380,10678560,4180,4162,5070,25060205108,11465772,9495217,4170,4188,4180,12235513,
11784591,4660,8684492,4168,4174,4162,11461473,4155,0x546a3069a27c8728742c,4151,4165,10309715,9150554,4185] (by decide +kernel)

private theorem part37 : Refutes moves 0x10000000000000000000000 0x1fa00000010000000000000000 :=
  branch 2141 0x410000000000000000000000 0x1fa80410410000000000000000 85 0x1fa80412412480000000000000 (by decide +kernel) part38 part39

private theorem part35 : Refutes moves 0x10000000000000000000000 0x1ba00000010000000000000000 :=
  branch 1 0x10000000000000000000000 0x1ba00000010000000000000000 98 0x1bf01044010000000000000000 (by decide +kernel) part36 part37

private theorem part29 : Refutes moves 0x10000000000000000000000 0x13a00000010000000000000000 :=
  branch 1 0x10000000000000000000000 0x13a00000010000000000000000 99 0x13a44028010000000000000000 (by decide +kernel) part30 part35

private theorem part23 : Refutes moves 0x10000000000000000000000 0x11a00000010000000000000000 :=
  branch 1 0x10000000000000000000000 0x11a00000010000000000000000 97 0x19e80482010000000000000000 (by decide +kernel) part24 part29

private theorem part13 : Refutes moves 0x10000000000000000000000 0x11800000010000000000000000 :=
  branch 1 0x10000000000000000000000 0x11800000010000000000000000 93 0x15800884210000000000000000 (by decide +kernel) part14 part23

private theorem part3 : Refutes moves 0x10000000000000000000000 0x11000000010000000000000000 :=
  branch 1 0x10000000000000000000000 0x11000000010000000000000000 95 0x15002240810000000000000000 (by decide +kernel) part4 part13

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part43 : Refutes moves 0x400110000000000000000000 0x1439b441150440411110000000 :=
  finish #[
19428537670,28214297343,22275892170,11079779,4182,24877609714,4882,27424228112,19504276806,4185,4191,4195,12121508,13390578,52538190062711,
0x1a46245ccba9043,4144,4138,4158,22691946969,4411,0x1a467345d1d3546,4173,4179,12579263,47665540080455,57784374329419,0xd221ef48d3828f42a,4156,17695757427,
11809714,4177,5235,28211139121,25849126974,25018966980,0x691a88a448c9d32853cd,4156,4177,11079775,4161,4411,10682683,4163,4882,
95189777196491597,10281055,4179,11849825,4151,4169] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part46 : Refutes moves 0x480100000010000000000000 0x1631d492754048010401003400 :=
  finish #[
9323738,0x169069dfa1c91d9,4173,12608333,17434591911,13385799,20007965441,0xbfb1a33103da80475,12215433,4191,42528776426241,4154,4159,4174,11068742,
21016142290,0x18127248ab48427,4191,11034701,4157,4171,5438,10618181,25841910433,0xcc498645468a8d301,4192,4186,21057314891,11412090,11772659,
4186,5237,5237,86289472669078473,10301535,4174,4173,23307379375,5159,76265500017869491,4159,4153,25015096458,4163,5159,
49419532870793,10297407,13386392,47631255545157,4177,51235743614089,51240606631049,0x180c4194011508d,4177,4174,0x174c74946a8e3c1,4157,4179,4192,4186,
11079755,4161,4168] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part47 : Refutes moves 0x400100000010000000000000 0x1439d492150040010001001400 :=
  finish #[
54518621738122,22675543366,4177,0x18cb48d3ba8536f,27427746566,93889657515541422,0x19808ca91cc3085,39799610691775,4166,4177,11079749,4161,4168,19330045249,46150641816512,
4179,11080653,46030382773167,9150542,4195,4193,25839555035,4391,39257397822581,9768995,4562,25838048006,4177,4191,5257,
40984230761892,4165,52536572272825,0xcc57e80fdf92855a3,4177,11079775,4168,4161,22365152393,95191080418898114,27425051027,22534484365,4166,4159,4170,
22675858758,11354599,27427357525,11067439,4185,4502,0xc0951045546a8e2e3,4165,28215891082,22695411906,21090873443,4168,4174,4179,9069183,
25841472835,27416592851,4171,12534515,27414652021,10260555,4149,10297407,28211651155,10682463,4181,4193,0x89c4c802147962487,47628874679619,4185,
22693036801,21015356361,4173,4174,46052287689290,10870944,35222147862894,4149,4137,20100976795,56153150886623,24967172682,10952765,4137,4165,
11080271,4168,0x174ca44e20ba546,4191,20017783336,10261061,11079733,28211651155,10682463,4163,11849813,4133,4151] (by decide +kernel)

private theorem part45 : Refutes moves 0x400100000010000000000000 0x1431d492150040010001001400 :=
  branch 1 0x400100000010000000000000 0x1431d492150040010001001400 91 0x1631d492754048010401003400 (by decide +kernel) part46 part47

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part49 : Refutes moves 0x401100000000000000000000 0x15b38415144051110000000000 :=
  finish #[
12621032,5153,54554559456390,4179,26638013578,26638058634,23405962377,23408018077,25849529576,11772961,4179,10170413,4177,4155,13389875,
4131,4173,5070,49711573013627,0xbf497aff5a6c09542,8642605,4163,4169,12186660,57779524198588,11849797,5352,9008360,4156,56169661551739,
11079718,4175,4154,27425358305,42492791595754,56167965589698,9150537,4187,20921951369,11796795,4174,4138,4263,11079995,4175,
4154,42955186955402,22600818968,4173,8910150,11035880,11079755,13391080,11068648,4171,10282023,10297402,4174,26637291798,11068648,
9150533,4187,4195,4179,4193] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part51 : Refutes moves 0x400100001000000000000000 0x14359c31540051010004104001 :=
  finish #[
5033,5540,27359483107,4174,12616936,4142,4175,0xa5f98b19e91915544,9523970,52924241346940,4139,4134,27426976507,10134274,4163,
0xcc5a47301944c3351,4142,0x2505f95230289ea338a842b,18879336923,4139,23960117903,4141,4147,0xba369b0263390c5a4,4174,4165,4171,8651997,4493,26638062628,
4185,11849773,0x197a4c233ad0090,80909857510286660,11338477,4125,4131,4945,12526631,11850108,26638061641,4163,4174,23286813811,12202926,
26638831694,13390559,97411323280384465,4191,13005962,22268368102,5438,10690966,4171,24204591199,4134,4143,4152,4177,5351,
56006904997094,4163,26637288586,0x662b4c98719633bf24e7,52542972417256,4169,10691233,4191,4171,11079761,4147,4175,4161,24262480729,4676,
0x8034601ce91a81244,13004835,4124,79738306438787555,0x198148ce1a6436f,40633831731889,4142,11079741,4147,0xa5e46131633a8e244,9151233,4191,4185,10257734,52935006778114,
5062,52941422138505,18742739023,4192,4185,5352,11068742,4157,5438,5352,11068648,4192,4171,9151438,4187,
4191,4879,9151438,22693077091,4154,38389285180742,5446,38389284013382,4181,21048930383,4163,4169,4174,4193] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part53 : Refutes moves 0x400100010000100000000000 0x1535b499345151010501400110 :=
  finish #[
13390689,0x198931661a32483,27425374992,4163,4177,77984212472500373,10641772,11079725,4147,35244451955252,22693479279,4151,13387078,0x1698a46622302f4,10235995,
4143,18742829831,4185,4193,5156,24991831066,12203034,78619639363953236,4185,4179,4193,10556452,19330032391,4179,12203034,
49105378796580,19378782297,4195,4177,4174] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part54 : Refutes moves 0x400100000000100000000000 0x14319418355150010100000110 :=
  finish #[
25720607186,25698537651,0xc096911948a838361,4161,4155,9150926,72215966738879438,0x1690288e4b361eb,27425005663,4186,4193,22676992297,4856,11461481,4141,
4147,4254,36276152435474,4173,13390797,22693868493,4173,4177,97038642753306763,4967,24967881171,24967570279,4173,8642641,8613959,
4151,4161,5443,13378320,11079872,4161,4159,37749688914703,36048063931718,4181,18742796566,4143,4185,4193,5258,
54384532627650,4167,12203024,4154,0x198a7e47b897367,18447622526,4186,4177,4376,0x83a4ff31487a8e292,4192,24824083594,21668873446,4177,10216586,
22559650189,4177,18446811451,4169,4166,40915514843876,37788775588580,52935004069987,4179,4173,4193,4174,4168,12985185,98466774839927558,
4147,0x662bfa678d3290834545,4161,18431619761,57742792909774,4185,4193,42847870727021,0x81898b302329d22e0,21620122003,4192,4186,9151241,18743485200,19480539527,
4186,11849824,4187,9008170,19431854866,27384648640,0x175244948b4d3c9,11067483,4185,4192,12144920,4376,0x8ba522ea44ba8e298,4186,4192,
50843093660993,0x169ae55471ce48a,4179,4169,93875108049416767,21058868266,4169,39538739323256,4147,37786228527495,0x9067320d1488373ce,4155,4161,4153,4159,
4154,13004878,4124] (by decide +kernel)

private theorem part52 : Refutes moves 0x400100000000000000000000 0x14319410141050010000000000 :=
  branch 2799 0x400100000000100000000000 0x14319418345150010100000110 64 0x1535b499345151010501400110 (by decide +kernel) part53 part54

private theorem part50 : Refutes moves 0x400100000000000000000000 0x14319410140050010000000000 :=
  branch 1 0x400100000000000000000000 0x14319410140050010000000000 60 0x14359c31540051010004104001 (by decide +kernel) part51 part52

private theorem part48 : Refutes moves 0x400100000000000000000000 0x14318410140050010000000000 :=
  branch 1 0x400100000000000000000000 0x14318410140050010000000000 84 0x15b38415144051110000000000 (by decide +kernel) part49 part50

private theorem part44 : Refutes moves 0x400100000000000000000000 0x14318410140040010000000000 :=
  branch 1 0x400100000000000000000000 0x14318410140040010000000000 52 0x1431d492150040010001001400 (by decide +kernel) part45 part48

private theorem part42 : Refutes moves 0x400100000000000000000000 0x14318400140040010000000000 :=
  branch 1 0x400100000000000000000000 0x14318400140040010000000000 76 0x1439b441150440411110000000 (by decide +kernel) part43 part44

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part57 : Refutes moves 0x440001000000000000000000 0x141b5f44401054004400010000 :=
  finish #[
18962411660,11850890,4169,4648,20019450735,9420867,4155,25850679677,17585984650,8974391,9752624,52941423616146,11850417,21585252425,4863,
9446538,4155,38111931843623,4159,9483402,4492,11829423,24235782319,4167,19974037563,4183,4195,4173,4191,17208001861,
11321806,12621126,42457717309485,11849791,38388498191175,0x82e74d0251534d347,4151,5446,52941421740347,13004855,4136,0x169aa323384b309,4173,4181,54553177264999,
5258,26636124337,8695863,4175,12620172,19288872074,4151,11059967,4149,19347539176,0x33151734880d025a6a8847d,4159,0x180e4160484b13b,4181,4183,
11464799,4164,4172] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part59 : Refutes moves 0x400001400000000000000000 0x1c071d04901404404400015400 :=
  finish #[
4577,19759789171,23985324800,4169,22477312564,4141,4187,20832367754,0x9b58126cda328e087,4151,4158,8934632,54547649172430,20707316661,4660,
0x198a8c2048ba47d,4193,8699995,4175,4181,4183,24901620751,25846370534,4173,0xc029881c59a04f2f2,5054,25846333882,4173,0x8654be5719cb4b0d0,4140,
4149,20580688104,9847544,9150541,4191,4189,25814041248,52931840418481,11849815,4151,42613107040698,21588120897,4152,0x997980a190c84e546,0x17f8299431393b1,
0x56352200884e0484f543,4182,5249,13370298,9078081,4173,9670709,0xcc440e4160484f488,9150550,4191,4189,4183,4538,21687608049,19370403142,
4173,21880950870,4151,22544806124,0x17f813c18a8e4e8,4151,5258,35261744837958,26634056654,12619831,8712394,4177,4175,4174,26634150862,
24272859529,0xcc4210d363384c546,4174,4173,56163795305704,27424211727,26634593123,4187,9519201,4189,11464799,4148,4172,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part62 : Refutes moves 0xc00001000000010000000000 0x15273d0248511600c050010100 :=
  finish #[
0x8a298857146aef546,4662,42698824229646,86778843632714773,0x18130219cc02085,11841577,4153,23480025159,4174,4304,17845642079,4173,11465370,4140,49211757040763,
11404610,24210203779,4183,4173,10494401,9798779,56092938661965,4188,25789658060,5251,20806235070,4657,56095823491205,4140,4170,
4149,56092910744798,4177,12619862,4130,4174,24834512007,46064718509180,11849796,0x198acd0a4c0947b,12620243,49435153277394,11849802,4160,50861078541143,
8712398,13378698,0xcc1810e69ca346488,10260528,8712398,12603478,4159,10682442,4193,4175,4151,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part63 : Refutes moves 0x400001000000010000000000 0x15871d02481114004010010100 :=
  finish #[
13390586,97763173301866839,25825136811,27427349125,13767799,4114,28199113253,56166112371847,4143,9535519,4189,12619868,4174,27398537364,0x9a78bb0253c917105,
4195,91426755734349123,4159,4153,0xd218120e546a8e4de,11465487,4188,4164,0xcc580e9c26228d42b,19471107097,49638131299464,4164,4188,12613026,25847895366,
4158,40854973490219,4167,22383481994,12620827,9855443,4167,4183,45962452566503,4177,4173,4159,0xa7934f311fe34042b,20185555097,54314936795623,
4153,5258,25847976118,11042877,4145,4159,9642536,75839847671030522,4171,97552009822041004,25849521478,56109876417671,72903936152298818,9531439,4195,
98095869972742900,4145,4159,4173,22667453766,0x180d025fe114301,11464797,4164,11849820,4133,4187,72356749451916706,4303,0x169afdd46118231,0x5183f74d9025440ba546,
4193,4189,4187,47596848583803,24866063686,12207227,25002255497,4123,25036608649,4144,4129,11464761,8700490,4182,10261169,
20597109601,11059967,4170,87268209838982094,4151,52610254295729,22649929936,74776416910812201,4193,4189,4183,4177,10309723,4171,4181] (by decide +kernel)

private theorem part61 : Refutes moves 0x400001000000010000000000 0x15071d02481114004010010100 :=
  branch 1 0x400001000000010000000000 0x15071d02481114004010010100 95 0x15273d0248511600c050010100 (by decide +kernel) part62 part63

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part64 : Refutes moves 0x400001000000000000000000 0x14071d00401004014000010000 :=
  finish #[
52921086530686,11842677,40981080605834,40981080114594,25653432363,4161,4149,4762,0xada98846200a872f3,4171,11830017,21685682952,0x198a4210c90e482,4167,4195,
4173,4192,19213374004,0x17303c9a68890b3,4150,5258,10260659,4149,11063705,22667150286,4173,11464800,13004892,4148,4562,
11034888,4193,8622716,4871,0x1812134fd8263b1,4137,4143,12546254,43898117947858,4155,9405052,4169,13004855,4160,10613202,
20007154336,4183,0x3316048397ef0020384f1d2,22552809938,20971843789,4177,4282,0xcc209e8c233a8e0ba,11034679,4157,4193,74732968034104646,4140,4172,4188,
17826554420,42954231050445,18740470432,4187,4188,11850417,11002830,4177,22662247439,4785,11002727,4177,4163,94806063772005399,4140,
4148,18742022833,4301,17842885488,4187,4177,10309719,4171,4191,12234837] (by decide +kernel)

private theorem part60 : Refutes moves 0x400001000000000000000000 0x14071d00401004004000010000 :=
  branch 1 0x400001000000000000000000 0x14071d00401004004000010000 40 0x15071d02481114004010010100 (by decide +kernel) part61 part64

private theorem part58 : Refutes moves 0x400001000000000000000000 0x14071d00001004004000010000 :=
  branch 1 0x400001000000000000000000 0x14071d00001004004000010000 70 0x1c071d04901404404400015400 (by decide +kernel) part59 part60

private theorem part56 : Refutes moves 0x400001000000000000000000 0x14031d00001004004000010000 :=
  branch 1 0x400001000000000000000000 0x14031d00001004004000010000 90 0x141b5f44401054004400010000 (by decide +kernel) part57 part58

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part66 : Refutes moves 0x1400000000000000000000000 0x1c915501000000000000000000 :=
  finish #[
25059463367,0x846a42a45d59cd546,4153,28215121128,12542738,4149,9425854,12234815,22475772479,25059427157,11849798,4142,4187,11850006,94521365572104470,
25057030534,4161,11464771,10298318,22691456418,17770148436,18531110956,4166,4174,4164,4687,22298833486,8696008,4171,4177,
24180585003,20757262515,52939056935467,4140,11849788,12235515,51322571780870,4163,8684492,94134335023186800,95122727349048176,17834504247,4183,4179,4175,
54552127853685,0x17572f4242d0410,51326444913680,9064519,4170,0x1a46eae3380d14a12204a30545,4163,57783778755909,5164,0x17566aa62230370,11849795,4151,0x1a4719da6bab126,42685031838855,10683219,
4151,4163,80868204670673942,4179,4174,49705105163120,21879337744,21099238065,4174,9150547,4189,4183,4193,4187,87410886176383266,
4411,46201368539333,4163,13005448,0x633c065bc9dd772ef310,8683580,93542622049416045,11059889,8691803,4183,4179,9458448,0x18ce41518044348,4169,9151153,
4692,13390685,25017852773,4151,11465285,4164,0x4ca522812b88259ce546,9150541,4185,4179,11079767,4154,4175,25061774756,0xba1a469cd6628f546,
4173,12236008,0x17560ad1834d4e8,4169,8708151,12235488,25848377638,11079748,25058685513,4173,94633378319249993,43109805769289,4156,17843332046,4185,
4187,4189,57782980354423,8708301,4185,5352,0x1a4674c5d34d4e8,4169,56134471816513,0x19801f69188b427,11464742,0x1a47025191ce3bb,4173,0x604d237f8d34268ba361,11079771,
4175,10309725,4171,4186,4161,4181] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part69 : Refutes moves 0x500000000000010000000000 0x1d2505570c0110000011000000 :=
  finish #[
12207242,25002279957,4151,49328887186555,52936545948998,4166,4165,8676678,17767375414,4181,4180,54539149202756,25847980801,18481893445,21114405064,
4167,20136891237,22552810234,42697461367553,4173,4179,56163192099765,8659134,4164,11079750,4182,4161,27423028362,56169663181092,4154,
8679619,4173,4411,45846134141243,0xa8fa42d226283c3c1,13774908,4182,4411,37886966166948,10309716,4171,4191,22678639338,22677099658,4147,
4882,11080743,8692103,4180,4173,4171,28211192460,12620091,10682457,4193,21571687449,22558053138,4159,46206911394186,0x99a988115470a31e7,
9031964,4154,4156,4164,4694,21114429732,4180,28211524182,25850688040,25845605136,4171,9416788,4154,9056459,0x267479bff522b385d409542,
10682457,4193,4181,0x1812426918ba302,0x9b5812a005d0a30ec,43243031614884,4156,4164,0x198aa0548d232fa,12620929,0x1982e4143b420ec,9056331,9031964,4156,4164,
4388,0x602cc1522b585d409228,10682457,4181,11849807,4133,4160,4151,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part70 : Refutes moves 0x500000000000000000000000 0x1d250551000000010000000000 :=
  finish #[
73092431329358168,36359559644580,20845986954,22609592521,4151,4179,4169,4411,57781398450570,4166,9474737,0x9b004e9e94784a2b1,4170,56136869315910,10179909,
0xbf251c88204280429,4151,18740461637,4185,4179,4183,13390019,8700104,4177,28213183030,46445852598822,4185,13775623,49675662681214,4151,
9475195,52675257966753,9150547,10309719,4171,4191,25057084032,13390607,8700191,11006029,21116817477,4147,4161,13005774,4748,
0x165ca3a629062f8,0x6914c334ad005d04c228,4181,4183,11842980,5540,11842312,4158,4179,0x198948c834c5228,4879,27423433676,56166479274372,8699999,4181,
4179,11079767,4161,4175,9056854,21114794767,0x47934d0fe128518462e5,4169,13004879,5352,0x83a8cf30823b3047b,26635751624,9056351,4180,18548285637,
0xa6a05298a62a91353,17761362661,4179,26634498831,4162,42697461354661,27425767818,56145180599223,4193,10309723,4181,12234847,4146,4156,4166,
52538073470372,13005774,0x6914094602e94884d47d,4185,4181,39348994183952,8704380,13004885,9023803,0x1978fea91c09473,52917931615370,4169,13004875,9056542,4180,
4164,4170,36186316133501,0x16923c9f934d2ed,26637292490,39737684108225,4185,4181,4191,11850043,22355919537,4175,8650940,13004865,9056542,
4180,12234826,11448370,4152,4160] (by decide +kernel)

private theorem part68 : Refutes moves 0x500000000000000000000000 0x1d250551000000000000000000 :=
  branch 1 0x500000000000000000000000 0x1d250551000000000000000000 40 0x1d2505570c0110000011000000 (by decide +kernel) part69 part70

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part73 : Refutes moves 0x401000010000000000000000 0x15972595004010100500401000 :=
  finish #[
45806233093235,12616369,0x81997aca20428d486,24827277711,11038806,4165,4179,42683464331953,5257,5164,0x9ae813315d5a135a4,4122,25044997146,56168637792453,4156,
4138,4165,4164,25847214769,44808883962155,4153,13369542,0x1986e3d46c080c6,4164,20923102346,9150531,4195,4189,4183,4785,
4569,10236765,4143,4153,9150866,4195,19472650555,4154,12203024,24990426128,4183,50846266585748,4756,28212801923,4174,
9507131,4195,11079767,10309718,4171,4161] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part74 : Refutes moves 0x401000000000000000000000 0x15930505014010000000000000 :=
  finish #[
17764070726,27426592164,4130,36380818314375,25847190290,4153,4189,13390607,20837581084,4167,0x52f8379870244da9123f,51010968544018,84445161380177034,10297415,4179,
4189,4164,74179952204665578,12620919,87383773821309126,11759813,4138,4164,0x18cd31600523234,47632844100743,4130,25044997065,8667327,4167,10309700,
4161,0x29a5a44095226f8e68ba28e,4189,4193,10277149,46475417523149,4141,45949215368045,25849058066,4154,4489,17735426831,4189,4173,4164,
4842,10564148,4164,25846420600,4179,11080842,10309690,12620832,25696219734,18742444109,4193,4181,24126719095,0x17f9024e6a915a4,0xbf5136a4604b9547d,
87620375916913799,4173,4164,4189,4694,9151039,4183,0xc09388a445d230425,4175,11849813,4133,4151,4187,51316607357898,51327303733995,
4151,0x172b48ce98ba2f2,4189,36359695413937,24958002126,25042584620,0x175731543a8e420,4165,4186,13004883,4172,54378198520262,0x169ae7ce228e0bf,13004869,0xa3073e712339d5546,
4181,4161,12620750,24822653582,4189,12620562,52936691733333,4151,24822973070,4179,13774913,20832760782,51316843909684,4174,5257,
10683507,4181,49709239087850,4166,4411,0x569262804cda91bab411,9507401,4195,4179,4183,4189,52931642062148,12120545,0x19868c2049c8478,4183,
4193,74015328298406272,4182,50835740078740,4380,28212007572,4182,4179,10309916,4171,4166,13004865,11448396,4152,4136] (by decide +kernel)

private theorem part72 : Refutes moves 0x401000000000000000000000 0x15930505004010000000000000 :=
  branch 1 0x401000000000000000000000 0x15930505004010000000000000 64 0x15972595004010100500401000 (by decide +kernel) part73 part74

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part76 : Refutes moves 0x400012000000000000000000 0x15193581412410410012480000 :=
  finish #[
11079888,13775916,0x180ce7dc7a2f2f2,4174,11031108,51317830632868,4195,10309725,4191,0x5fb83271f48d9c8ba2e0,12603571,11072440,10256479,4163,57783544779148,
4161,88117804869927446,9151248,17834505260,4179,4185,4882,19397133243,19497816813,10309725,4191,4161,11448410,4152] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part77 : Refutes moves 0x400010000000000000000000 0x15193503010400400010000000 :=
  finish #[
46149819781680,10310290,50945343705776,49668329903223,13774927,4182,17847956036,35256888603410,28212802131,4173,4174,51327302562450,10302038,4179,19428778580,
4195,4191,4183,4189,18560988485,12619983,4174,0x198548d3f1d542c,21116798372,4159,4166,11079967,4581,46475481494285,4179,
4191,95121110073057753,38387710046788,43029425365389,4174,4179,4183,4189,21119513360,51288991421472,4774,12146084,10687140,4162,4156,
4182,4174,11079967,18414917026,4191,0xc09523315478ba23f,4372,22651163503,13774943,13771143,28214247815,51283148026526,0x1a4641a911c43b5,4159,4164,
25846063166,10277645,57745411708324,52935044866256,4191,4185,57779811071394,4164,4173,4174,4179,4183,11448413,4144,4152,
11768970,11079870,4161,22694245514,4144,98358072304792242,4186,24161874687,9806679,38076857545656,4185,4179,0x181245d75a8f5a4,11449482,22616781676,
51235883143236,4171,4161,4191,28212781437,25812071090,4411,23454872421,27417797001,57777463038630,10309725,4171,4161,4191,4186,
24872543157,4499,88324065055105970,4161,11448415,4144,20119707855,39689417986424,13775724,88290428370891815,4174,0x1812d25fba8530b,22693098053,9150547,4185,
4191,10682461,4163,11849825,4151] (by decide +kernel)

private theorem part75 : Refutes moves 0x400000000000000000000000 0x15111501000000000000000000 :=
  branch 2423 0x400010000000000000000000 0x15193501010400400010000000 73 0x15193581412410410012480000 (by decide +kernel) part76 part77

private theorem part71 : Refutes moves 0x400000000000000000000000 0x15110501000000000000000000 :=
  branch 1 0x400000000000000000000000 0x15110501000000000000000000 84 0x15930505004010000000000000 (by decide +kernel) part72 part75

private theorem part67 : Refutes moves 0x400000000000000000000000 0x15010501000000000000000000 :=
  branch 1 0x400000000000000000000000 0x15010501000000000000000000 92 0x1d250551000000000000000000 (by decide +kernel) part68 part71

private theorem part65 : Refutes moves 0x400000000000000000000000 0x14010501000000000000000000 :=
  branch 1 0x400000000000000000000000 0x14010501000000000000000000 96 0x1c915501000000000000000000 (by decide +kernel) part66 part67

private theorem part55 : Refutes moves 0x400000000000000000000000 0x14010500000000000000000000 :=
  branch 1 0x400000000000000000000000 0x14010500000000000000000000 72 0x14031d00001004004000010000 (by decide +kernel) part56 part65

private theorem part41 : Refutes moves 0x400000000000000000000000 0x14010400000000000000000000 :=
  branch 1 0x400000000000000000000000 0x14010400000000000000000000 80 0x14318400140040010000000000 (by decide +kernel) part42 part55

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part81 : Refutes moves 0x1000500000000000000000000 0x18771245111100550000000000 :=
  finish #[
5252,22499009674,4187,18197185262,25846064263,4191,57750034600302,25748869870,4141,25847915273,25846063885,4183,11079775,4147,4161,
13775805,0xb3a0cb48dfb0fd357,4171,56161479148475,4157,5258,0x1988ea20483c485,4159,27426591102,19302409636,9150529,4187,4191,12141894,0x17e901136ba841f,
4139,0xd230cafe110521482,0x16506fdfc9b1475,12619830,4141,0xa1498ae39333aa1db,45743847019657,0x174130e91a8c47a,4149,4173,21878252682,4193,4187,93924846943650740,9151153,
4193,8655989,5237,8656009,12619851,4141,80403239383635362,52937267766391,4171,0x4042ee454fca04cc53c4,4157,9151153,4191,11079771,4147,
4161,11464783,4172] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part83 : Refutes moves 0x1000400400000000000000000 0x10678954105400501400400400 :=
  finish #[
42494484510016,12620932,5258,10974329,4135,9150517,4195,13382788,56136877700113,18741522485,4148,5258,10163526,4135,5446,
56147448120147,9760839,0x8872cc3f4a78ba475,4187,4193,0xa629870266294f5a4,4785,22417814854,4167,27426591480,94276648082056330,4193,4195,11079771,4161,
4175,57779650335881,25842299195,0xa76813314dfa7b5a4,4139,4181,19927560462,45777416123624,46464609834404,11079751,4175,4161,5444,0x198b30e04a9136f,4147,
5245,56169658864765,4182,28207502474,9458826,4161,12621126,52938100249926,22567927894,4146,4153,4167,5444,52941406495264,4171,
10220662,0x43299f812fd4df8fc2f8,4152,4149,51273231467846,52596103808041,10682449,52936475145636,39517451125384,11079753,4182,4175,44111756247985,11080328,52941420208207,
4195,11464801,4180,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part85 : Refutes moves 0x1800400000000000000000000 0x1277e105701800400000000000 :=
  finish #[
13390513,5141,23273791684,13389867,13390983,0xb2c132b9e33a8b2f0,12619828,4141,4174,13382781,0x52f2ef7f930d9e3a4546,4173,5041,57742078231688,4173,
46257662432071,4148,19294044347,4157,4160,50828299769152,12563594,4149,19298799998,19298030727,11464749,4148,23484716170,48088570070154,0xb3a97e9f604a30546,
0x1812bbd00b4c2fe,4143,4195,23480746279,0xa898133141f8a22b1,4157,4171,4167,4169,49297712414915,25850303030,0x34854225e66a8c1a546747d,4172,77450433936999350,4158,
11079744,4154,4175,4161,46475296887926,11781538,17428140414,4144,13391266,9356222,4160,80276530640650796,4175,4163,4157,
11081030,9425472,18467557565,4163,4174,27416609534,0x1a429bd184c5543,22527644407,11845710,4179,4195,4141,0x6620406606fe91aef280,25674527660,49523417085056,
4172,0xc0937f48d77a912f7,4161,4175,4140,10220279,4882,0x82f03300548cc522a,87025453957584198,4141,4162,4147,57748382045322,49196980752924,4153,
0x1a4302661b2f17d,5444,24020739396,4149,4171,11079779,12621126,9720090,4162,25774805778,0x403331a420fa62c00419,9068740,4173,10682439,4187,
4169,4163,80939871529530692,27425436414,52937479094465,4163,4169,13776198,13775810,11076736,11464770,4148,0x9bf5df314ac523282,57781344547769,0xc07a46bbcdfa302fc,
4187,11079747,4161,4154,12234796,4146,4126] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part87 : Refutes moves 0x1002400000000000000000000 0x10e701a4541092400000000000 :=
  finish #[
12996890,0x548cc520a9a22cc06151,22351471378,56152453387388,4150,13767614,24983015968,10985513,4124,4152,4180,51096383673669,11079869,4161,44540417692434,
27427336388,95194609378939114,4161,4167,51302659544202,25846371654,9015361,4152,13390016,0x197ea45344c5151,5045,9458450,4161,11030599,11042855,
4180,4187,4163,28198687274,0x1754e61f94082a9,10986163,4159,4153,0x181331421a882ff,4163,52924242268898,0x1a47316048435a2,4163,0x6049fba469ea044c52e2,25738941860,
9015361,4150,4154,44006307026239,20749165705,19320033518,4155,4161,42283199824617,20647056105,40778861219905,11464762,4188,4140,0x662ae25d8a44ff8993cd,
5258,11081024,13767442,28195181800,4155,4167,4161,25728700747,5045,19371988103,4161,4167,28198728027,11042844,4187,
4194,0x18124ec74d21240,40469610403139,40469608002883,11042869,4187,24178660772,0xa6252253e9084248a,11464771,4172,4140,44007099552200,46480212178245,4738,10163526,
9434247,12619841,18416070701,4140,0x1a4253d77c6727c,11465275,5258,0x18cf024daa91546,4161,0x4dac5c98a0c8478932e3,4150,4158,4154,0x9fba4302477aef1e7,19187823754,
11465866,22691365128,4150,4149,4144,22618371210,4177,4187,4194,12234836,4146,4136] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part88 : Refutes moves 0x1000400000000000000000000 0x10e72104501000400000000000 :=
  finish #[
47596093609286,25003054218,52735264092722,5248,10163328,4165,4120,4175,4140,4486,22297141632,25841914246,0x9b1a46bbdf92915a2,4168,4140,
4175,4161,25850303807,11080251,13774913,0x5314bf20b314dfaef353,4976,22683424070,4158,4162,4148,25849528882,93527285227607157,5439,9459014,
4158,4161,11047474,4139,4167,19370738814,5257,0x18129da629bf4e8,11075642,4183,12234804,4136,4146,5164,45786545804021,
57781405684872,13004858,93787330427065077,4152,4158,0x29ee5fd2271cea948a7e2f1,4180,46479316288838,26637677700,19159815492,21880131642,4177,11465772,11080369,4154,
5058,52936615457457,4180,9150562,4195,4193,4187,0x99c4cd0204cbab154,5164,4859,26635924514,4150,20748103722,4180,22619919403,
0x172c9de04a8c367,4149,10683530,4193,4163,12620330,12985369,57768958530097,11464782,4188,12235819,13390892,12231131,10592335,4159,
4135,12234948,56162405880688,4152,22619918633,0xa7b98aead462ef129,4188,56162404291518,4135,4149,4173,47683595948672,0xcc4a42ffe629b52f7,0x17ff48d9a4c5280,17738895922,
56167949972032,4158,4149,4167,4194,12616246,5446,42400482542918,4167,5063,42631925880128,9015331,4150,4158,5446,
52605326480708,10990346,4139,4167,4188,5141,22569190431,4139,25712858438,10970249,0x172931544a90475,4167,12619868,12234797,4136,
9150514,4193,10309719,4171] (by decide +kernel)

private theorem part86 : Refutes moves 0x1000400000000000000000000 0x10e70104501000400000000000 :=
  branch 1 0x1000400000000000000000000 0x10e70104501000400000000000 85 0x10e701a4541092400000000000 (by decide +kernel) part87 part88

private theorem part84 : Refutes moves 0x1000400000000000000000000 0x10670104501000400000000000 :=
  branch 1 0x1000400000000000000000000 0x10670104501000400000000000 95 0x1277e105701800400000000000 (by decide +kernel) part85 part86

private theorem part82 : Refutes moves 0x1000400000000000000000000 0x10670104101000400000000000 :=
  branch 1 0x1000400000000000000000000 0x10670104101000400000000000 70 0x10678954105400501400400400 (by decide +kernel) part83 part84

private theorem part80 : Refutes moves 0x1000400000000000000000000 0x10670004101000400000000000 :=
  branch 1 0x1000400000000000000000000 0x10670004101000400000000000 80 0x18771245111100550000000000 (by decide +kernel) part81 part82

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part91 : Refutes moves 0x300400000000000000000000 0x15c980f1940300400000000000 :=
  finish #[
4856,8925836,12619814,17738903725,0x9fba4348c21bab30d,4156,4166,17542874250,10957661,21879412038,4171,37514687742821,4685,0x53f4c4694a30e60435a4,13389899,
4170,13390020,10273549,10190932,4147,4195,4177,4157,10310979,52769589797731,4131,0xadc9840bcea899488,4156,4785,0x1812a0603842546,
4165,44176357807233,21114753211,4158,4156,4163,0x8dc087026628992b1,56168757212078,0x18bae76628f9475,4158,21118357975,4130,0x19822481fa3048a,4169,94264818587964739,
27425424219,4169,4957,47765357364075,10309699,4166,51253021033500,4195,4177,4180,4182,44170664637555,11003300,17728578225,11071549,
4170,0x271d39adc41623604c671df,0x29de0482c74d48ce61d4426,4170,4185,5164,56113388876653,13004899,39294055994693,36119150154867,12234837,56117283558125,28195926705,8626957,4159,
4156,4694,46153794331676,4165,4171,4170,11448387,4176,4136,4160] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part92 : Refutes moves 0x100400000000000000000000 0x15e18011040100400000000000 :=
  finish #[
94279877177070724,12600643,22443373321,11448380,4160,11445571,27389432571,13389884,22559261727,4163,4852,0xc098092fd962ea5a2,11448375,11079720,4175,
12596550,0xc09801316021005a4,4165,4844,0xb4b74d024da8aa2f8,11079751,4175,56166506738727,10309696,4171,93782403885847197,0x198a85a04a692e2,10309828,4171,4166,
23155229537,56129487336767,13006150,27426976514,22291202825,4156,12214342,4171,13390584,51223435198997,4863,25847223056,4171,4176,10272838,
4175,4185,4180,47802233721689,13390584,0x174d3153f2914e8,0xa9198ae9a04a8c35f,4159,4166,4170,27425432698,11072364,4159,23474017037,4161,
0x1a47315462d8312,4375,11428713,4181,10190907,4132,24161883180,22693463366,20914643019,4185,4167,8769587,4195] (by decide +kernel)

private theorem part90 : Refutes moves 0x100400000000000000000000 0x15c18011040100400000000000 :=
  branch 1 0x100400000000000000000000 0x15c18011040100400000000000 93 0x15c980f1940300400000000000 (by decide +kernel) part91 part92

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part95 : Refutes moves 0x4000500000000000000000000 0x195f5250044400550000000000 :=
  finish #[
57782200972614,0x4aa2e020731577c09351,48094290650344,4147,9151043,4193,4191,28215505960,0x46500598a1e59bd2321d,0x198a2e9184085a4,11464759,4164,18200277589,88541240394695818,51231749866620,
4131,4151,52917926032301,4148,4882,0x29ae049d452348d778ba47c,4191,4189,26637968804,28213183344,23480477092,4191,4181,10293837,4170,
10253168,4147,4157,4167,4175] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part97 : Refutes moves 0x4000401000000000000000000 0x11d5e170144000441004010000 :=
  finish #[
13005675,13378411,5446,27400250398,11800631,4163,10309693,52939016917765,22569104145,0xad27e8a09c9c08487,4140,4153,10273352,0xae274c71cea0ba30c,4193,
4187,4195,13005868,11444436,5446,0x165919dd5b4a166,4163,4157,13005585,10294316,21081334828,4193,4187,11464803,4180,
45981211840958,51321542300217,52939055764117,20997448842,4193,4185,4187,13005868,12235194,10293482,26636906585,4180,4148,13386383,12215038,
10683431,4157,4155,11018682,4139,0x174d315484672fc,51237200077140,9151235,4189,4187,4185,5446,97692746305954234,4165,42235955216753,
4137,5258,87735624905048379,4177,11464793,10309676,4161,4171,4156] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part98 : Refutes moves 0x4000400000000000000000000 0x11554141044000400000000000 :=
  finish #[
10912018,36342205510791,45819931690310,4118,4173,0x198a9ad9b4c45a4,17240338919,0xa682cd02691891546,24076191140,4122,4137,4134,4119,4949,11846501,
4159,27377415283,36926489621924,8663986,4169,4170,49224857322217,4155,4173,4161,5235,17744007934,4862,57776833495596,11780163,
4161,4149,11076273,4160,0x1982a0a62b315a3,12620160,10309688,9151153,4193,4191,4181,13390761,0xc097ff005943fd417,4153,27427746944,
24967943494,10211387,4137,10212017,0xd23402ffd48230546,10683225,46461340279655,9150523,4191,4183,4181,24035648627,8836233,51300007183686,10211387,
4137,13390590,94491021184008381,8659710,4171,4163,0x5a44c59826f45d1d5475,4191,11079765,4161,4147,5164,11449388,4160,4136,
11080278,12620722,9687785,0xa01812714b329109f,4147,4189,10310417,4181,11448419,52941346636562,22695416450,25846346514,10309691,23450005599,9924668,
4180] (by decide +kernel)

private theorem part96 : Refutes moves 0x4000400000000000000000000 0x11554140044000400000000000 :=
  branch 1 0x4000400000000000000000000 0x11554140044000400000000000 72 0x11d5e170144000441004010000 (by decide +kernel) part97 part98

private theorem part94 : Refutes moves 0x4000400000000000000000000 0x11554040044000400000000000 :=
  branch 1 0x4000400000000000000000000 0x11554040044000400000000000 80 0x195f5250044400550000000000 (by decide +kernel) part95 part96

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part100 : Refutes moves 0x40400000000000000000000 0x15514004404040400000000000 :=
  finish #[
4489,19399463293,0xc67813315183385a4,4163,5352,0x198a8c2338f10c4,4168,10191537,22568042552,4162,4181,37239811322490,27424653906,17727743015,4173,
11464795,25690534840,0xcc5460a15a0467250,21881238281,4152,4157,40707667150056,0xcc580eb71d319c0a3,0xcc580e291d3409302,12218435,4152,9470549,0x180e834e63a73ae,4152,11464803,
9924652,4176,4180,5039,90543882182336966,10985543,52889095139782,38113509307624,4164,4172,12620163,4395,26638062000,4152,0x16848c19c34a4e8,
4157,4172,49487479865798,5159,23189517448,10682436,4181,0xb304fc6fe33a8c477,4149,4156,4163,19254916422,0xc049792f975a8c5a2,22692720735,4168,
11466148,4959,52853945295135,22618357831,4152,19908854640,10306321,27426975833,0x174e9da04a7e414,22568026992,0x1726a04e8c092fe,10190937,4167,9924664,4176,
91773633689309455,13005943,28211164295,11075663,4167,57779653993796,17702650147,22694244418,4152,4848,25847595475,4163,0x1a432f11827d5a4,0xa7d8133151829153d,4147,
4161,74215030344561418,9924672,8769620,4193,4195,4189] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part101 : Refutes moves 0x400000000000000000000 0x15550000000000400000000000 :=
  finish #[
5352,0xae69863b6339bf4e7,4164,13382794,5443,49574140089576,4145,4143,4141,49110285247720,23992099010,17725801196,4159,4171,0x18ce6d8512303bd,
4157,4175,44281979925922,4156,49349250400512,19910783170,5352,8925440,4144,4132,4145,4973,42710533555315,10682558,12533821,
4173,4151,18298630400,8769596,4191,80303319030780073,23439692635,10310979,11448918,10219576,4179,4189,46391916933718,4156,11449076,
0xcc24e8a25759d542c,8769621,4195,5258,0x174d01e04a30365,4181,9721155,19908088384,4171,4149,0x94598475577bab223,4156,49278898704644,22524101675,0x9541510249c9d5481,
4161,4181,56169643999707,4975,25671770869,4183,19808579641,47967605749062,24212038572,43248034426937,4166,8769596,9924707,4172,9154640] (by decide +kernel)

private theorem part99 : Refutes moves 0x400000000000000000000 0x15510000000000400000000000 :=
  branch 1 0x400000000000000000000 0x15510000000000400000000000 90 0x15514004404040400000000000 (by decide +kernel) part100 part101

private theorem part93 : Refutes moves 0x400000000000000000000 0x11510000000000400000000000 :=
  branch 1 0x400000000000000000000 0x11510000000000400000000000 98 0x11554040044000400000000000 (by decide +kernel) part94 part99

private theorem part89 : Refutes moves 0x400000000000000000000 0x11410000000000400000000000 :=
  branch 1 0x400000000000000000000 0x11410000000000400000000000 92 0x15c18011040100400000000000 (by decide +kernel) part90 part93

private theorem part79 : Refutes moves 0x400000000000000000000 0x10410000000000400000000000 :=
  branch 1 0x400000000000000000000 0x10410000000000400000000000 96 0x10670004101000400000000000 (by decide +kernel) part80 part89

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part106 : Refutes moves 0x4080010400000000000000000 0x12d7d5070524560c4090410400 :=
  finish #[
0xc0980a539a4100540,4480,11833728,11079749,4161,52733546739008,0xa71a4640dfc4c5230,4144,4972,4955,26594853739,11079737,4189,9306177,12546430,
11379467,9831186,4153,13389889,5540,28212171538,0xb4c36c4e691aeb2f2,4152,4136,4652,11834788,4192,5258,46480170693753,13774941,
0x181348dfc4c521d,28211913866,4153,10969136,4141,0xc02a466ad42290180,4167,4174,4155,4181,4195] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part107 : Refutes moves 0x4080010000000000000000000 0x12d39503402444080010000000 :=
  finish #[
11379454,23307768574,4137,44000308761723,13774882,5540,8639331,4159,27384648539,12223527,13774905,28213576439,4155,4181,20766807460,
57785306297187,11448377,4144,4160,40916304139387,12563402,0x18131862fa89486,11448377,4160,11080825,4175,4147,28212286784,0xa018c3314a74c2415,11345997,
11347270,97483311620273472,4153,4195,56166497891359,0x197cfca91c61475,4142,0xd235a49c6022eb48a,4192,4136,0xad27fabb1a2cc511b,36238614992010,10309666,19223291206,52941421196319,
4119,5346,49419548893871,4181,11448419,28212810587,4963,26587681644,4173,22626677612,4181,11079737,4182,4189,4161,
23241831750,5540,9437563,4159,4153,5540,13775634,95176228612588659,4158,4159,12980289,0x17fe9c4003362ab01074c6136d,13390879,20764496937,26586558529,
12234808,4136,0xcc280ae7a30bf73ca,54451522572477,4161,13390493,0xa1c66348e30b4341f,22694249606,4145,4159,47598483965347,94484495183233979,13774913,0x6309ab4da3fe91a903ca,4160,
4174,4195,26587657337,0x5d44048c2fdd76291479,48023241142337,4136,4652,9438035,4162,5251,23239054474,13774893,23239054756,12981386,13389858,
4144,0x165d48e308fa282,19278083187,4189,0x198902533282227,4160,4153,4195,4874,51095057433132,4147,12596450,11019384,22466486823,20856767813,
4167,4155,11448419,12234848,10309672,4171,4181,4156,4186] (by decide +kernel)

private theorem part105 : Refutes moves 0x4080010000000000000000000 0x12d39503002444080010000000 :=
  branch 1 0x4080010000000000000000000 0x12d39503002444080010000000 70 0x12d7d5070524560c4090410400 (by decide +kernel) part106 part107

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part108 : Refutes moves 0x4000010000000000000000000 0x105b8501000044000010000000 :=
  finish #[
5235,13354099,56100931785458,4145,12234811,5235,36923846452362,4155,0x8ce97f02262bab282,4126,0x47fc091aeeac672eb542,4192,4152,0x18c67fdd5893184,0xd23985314e2aeb542,
47451289072766,4156,0x691cc0756555654c5543,0x1984bac81bfd1e7,4195,36188686791795,0x40906967824691aeb489,52914470986685,98081436687140160,21711979846,4167,4149,4155,11079736,4161,
4189,4182,81040902365516930,4130,4154,27367871434,9434250,4149,13353344,12600637,4147,4135,0x28a204a9110e4f630d2353d,4154,0x99597c8b231949423,
21484623064,72943068658307632,20043076251,4189,13774899,26587344982,11849818,4169,10491202,25722082630,4155,11080322,4147,38989667013250,11080641,
19843649587,13774882,0xc0952348e30aeb2f5,23448851773,22568415989,87833031425429801,4155,4167,4565,0xba6808cb9fc291282,42887223234611,4133,4169,4160,5243,
80226236104250685,36569796489267,8717143,24983965905,51321657398124,4174,11077028,0x47eb4c988a425e3ab4e7,28215120940,11076053,11079751,4175,23449620545,4133,4169,
4160,11809714,51322538234627,4147,11081024,52924242637944,20980244520,4180,98354840695756102,35622479377063,0x18c489a629bb184,0xb28520ead75b4d485,4169,8724544,10309715,
4171,4191,4186,9421157,12620535,4141,0xa0198814291bab425,4186,4969,22687027576,4174,48025611601316,0x1978ead75c09415,25822823260,0x1728a40283ab3bd,
4186,47562546021325,11448696,4144,11018285,4167,11849806,4151,4160,25847223333,0xcc5749024ea85315c,9150548,9539679,4193,4181] (by decide +kernel)

private theorem part104 : Refutes moves 0x4000010000000000000000000 0x10538501000044000010000000 :=
  branch 1 0x4000010000000000000000000 0x10538501000044000010000000 91 0x12d39503002444080010000000 (by decide +kernel) part105 part108

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part110 : Refutes moves 0x1000010000000000000000000 0x14555400100101000010000000 :=
  finish #[
4647,25045381568,9459013,11055494,4162,4176,9539655,27427746173,10241444,4159,5070,72919767338209489,43044239651127,4173,13775057,
94422263404446351,11849791,9539639,4181,4187,4189,12236002,0x905a4348dd5b4d540,4169,11841745,13390796,10236479,4168,9539651,11071898,
8721165,4189,25060234660,8721147,4189,42934054523657,10309729,4171,4191,4181,4506,4506,51288906764453,0x87125e4fc28119254,0x604b958c2466919c4473,
4154,4179,4169,4189,0x6622767f0ea630c09416,0x1812e5630d233c7,10281541,4159,4189,22468923598,57781361812222,4189,4187,12620057,50946174948578,
4189,9539899,10309723,4161,9916511,4174,4166] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part113 : Refutes moves 0x2040010000000000000000000 0x1d791c20404182040010000000 :=
  finish #[
28199076272,0xa0d7ee97a60a7d4e2,52942194631803,19978241250,25846334185,4155,4146,4149,4167,57750949343886,54454022296186,22696149758,4161,0x40338f5dc6aa04a7d478,21586580900,
12185665,4164,4174,4168,23450391314,4365,22450988263,4943,11080556,9773121,4131,4167,4155,4391,23448851295,
4563,28213556450,11046957,4174,4155,12621122,11449106,4168,0x2979415235d72f1680a63ba,0xb34380d1975a90546,4155,11849799,4133,4169,4160,
0x18c2ea93ecbe542,26584051966,25807184169,4181,82870488078730565,22694982028,13774916,4182,4168,12215615,54488400794840,52938880271079,4174,4167,56099097035324,
45739080688198,4167,0x690c61a46b58542eb53f,0x197f01204a7b36c,11849806,4142,4169,4160,0xd22400fe9fba6d542,0x83498afe9363a6542,4131,93889589875905659,4147,5045,11080556,
4147,22692279338,4164,4176,25053766788,25052181826,9483586,91637768682353796,4168,4182,4161,11306203,47558546530838,5346,44641021502883,
4175,4155,11849799,4142,0xcc097f1859ba913ce,11449663,23447172415,4153,4144,0x18091865f4bf312,5439,44210074674493,4383,13365723,48027920797985,
4174,4183,11849799,4142,4160,42973124092761,5258,0x165b0265f8a836c,4175,0x197f0245410b4e2,4161,4167,11042905,4170,4163,
54449911960027,21797065163,0xaeb72abb8d83a94e2,4148,22442123312,4131,4177,4159,4191] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part114 : Refutes moves 0x40010000000000000000000 0x17710c00404100040010000000 :=
  finish #[
0x207e62d221e348d759ce5a2,22625969572,9814607,11079733,4161,0x18c26e5489cd36c,4163,12981198,87946729561686295,4163,11805834,25847215043,10240077,9539662,4187,
11080836,11080251,4882,0xc0952348ce21ce485,4159,4183,4164,0x662c064e0a4604b4d540,9446337,0x197cd25462913af,4168,12621120,57747053552074,22652702792,4169,
9539661,8769627,4191] (by decide +kernel)

private theorem part112 : Refutes moves 0x40010000000000000000000 0x15710c00404100040010000000 :=
  branch 1 0x40010000000000000000000 0x15710c00404100040010000000 97 0x1d791c20404182040010000000 (by decide +kernel) part113 part114

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part115 : Refutes moves 0x10000000000000000000 0x15550400000000000010000000 :=
  finish #[
12236095,11072258,4159,12620155,5439,51318101812149,0xcbf4d118497a88480,4173,9498687,4189,11849806,27367485737,49709971604799,4945,20896711723,
25789177945,4152,4159,5446,0x53a461757020ad405540,4159,40398481773307,0xa907566ed4234d223,4160,9486409,10309710,4181,4667,9630764,10278020,
4168,26585350925,11849791,0x174c212049583cc,26586112974,21617987840,4138,0x169b309959584e4,0xba967a560dd34b3ce,10309694,4176,26596889639,11449571,4176,56170408543555,
11842692,10276944,4158,12981005,25034667334,11805922,12234827,10281040,4159,4183,9539667,4181,4187,19281253418,23448745186,
4963,9027867,11849797,4169,4160,37975207089101,25041916960,9539664,8769621,4195,9154657] (by decide +kernel)

private theorem part111 : Refutes moves 0x10000000000000000000 0x15510400000000000010000000 :=
  branch 1 0x10000000000000000000 0x15510400000000000010000000 90 0x15710c00404100040010000000 (by decide +kernel) part112 part115

private theorem part109 : Refutes moves 0x10000000000000000000 0x14510400000000000010000000 :=
  branch 1 0x10000000000000000000 0x14510400000000000010000000 96 0x14555400100101000010000000 (by decide +kernel) part110 part111

private theorem part103 : Refutes moves 0x10000000000000000000 0x10510400000000000010000000 :=
  branch 1 0x10000000000000000000 0x10510400000000000010000000 98 0x10538501000044000010000000 (by decide +kernel) part104 part109

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part119 : Refutes moves 0x1080000400000000000000000 0x1a45cc52004012101080000400 :=
  finish #[
12214959,5159,13001767,4173,13389853,26638832778,21695194339,4147,11822101,0xcc51293119834b16b,27423802399,4173,4165,4149,4153,
87310175144670156,0x18ce98661cc548a,27426185782,4161,0x9a44c2b490d29117e,4147,4168,28211926248,13391069,11379850,4143,47595314238691,4949,23456850773,4159,
4161,4153,8699975,4173,4175,27407835291,24263681349,13370035,4149,4161,0x82e98948c45a91480,4154,46458244391599,4176,0xa768cf024e69d25a4,
4163,46017890533839,28215882574,0xcc30d2249fc2915a3,10911809,22693074058,4173,4189,11080260,8700663,8700107,0x174d48d66cc03b1,56082931360689,22584819793,4155,
4167,4181,27415860345,10969291,13386890,22582437002,11018321,4167,13004885,4124,4160,25652666758,5446,22349123971,24027611698,
8692259,11075661,4181,13004859,46482581779389,4855,17775772433,4173,4181,13775429,50846266516712,4134,17819312719,4173,4194,
4168,11464797,4164,4180,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part121 : Refutes moves 0x3000000400000000000000000 0x1ccf8c50014000183000000400 :=
  finish #[
97970889353577610,25738806193,0x18129c1fe1b13b2,4155,4135,44744218493968,5245,0xc095dce990e22e540,4149,11464763,4148,52940633461427,45982705398699,54551296222346,4149,
4143,52932110217973,52932109161205,4155,24983560942,22357877126,4143,91706524874871833,13004845,11079720,4147,13776196,13005680,8720436,46472192386173,
4176,4180,4182,12567587,0x198ae89fe3f9479,8704072,12227620,51287423468580,4176,0xc59438a459e409546,12620549,49418762736965,4170,21894955695,4165,
4171,4177,13386877,95191259423896902,4148,0x198a2a1449b1541,0x174411dfe1b13b1,27359445553,11809714,4168,4141,4161,26636907267,4148,20003410979,
27383493864,17834512436,4182,4177,4180,4188,39482154186054,25848718662,12612533,11080833,4147,26634145857,4175,52938251629893,91634510318203834,
51189862388958,20085019766,4147,4182,13004865,44847155540653,0xb3a4da8c9a6291546,4175,11465960,4180,22569972273,11080740,4175,0x18cf3159e2280b4,11027688,
4141,4155,56169551380919,26636907267,46099889197262,4182,4177,4180,4176,4181,11849820,4151,4169] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part123 : Refutes moves 0x1002000400000000000000000 0x12ed8c74044080111002000400 :=
  finish #[
0x181131262b425a4,0x29de62acd8ce985fe966545,25746891134,4147,4159,18912924408,27423396600,13004863,46034326967622,4169,5237,45657948443190,27424662191,4171,4167,
0x198b16446c67232,25797661363,4168,4147,0xc5945023633a9148a,46480140300666,4139,4143,4154,4161,27426497674,12583585,0x198acea0003748a,4155,4159,
41276289340152,19852448187,27366986215,49385190757696,4152,4185,35822666274112,0x8242ac02262c09280,49368008942328,46033363817598,21896496243,4171,5446,5060,21896496243,
4153,12619839,4152,4141,4195,9232473,4133,5235,79206182213006655,0x27f9144bd98ab36918ff0b8,4152,11079751,4154,4168,4182,
52666545771453,27423810296,52546236354950,27423826310,4159,4185,0x1808a44e69d2546,4168,4194,0x1984660d11c9545,24060301702,5446,10625991,10260545,4149,
4185,20187993220,27374720138,19320431754,4155,13774913,10482259,4686,18886980933,11080067,4175,13774913,4182,21048911268,4159,
4194,4168,81040897115042847,21048926994,11849826,4142,4133,4169,11851172,54551597843406,4163,0x18baa4691c67186,0x5d1d2339d19da69d2186,4169,39576274367250,
9839942,5258,21662803081,9457717,13004889,80295173393118129,4882,0x1a471765f905183,20965040187,4163,4168,11464802,4180,4164,4148,
4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part124 : Refutes moves 0x1000000400000000000000000 0x124dac50004000101000000400 :=
  finish #[
28213474121,17243976934,9360710,4152,11428679,4139,44227094013155,4141,4171,0x165548ce6c03545,5445,10298500,13389896,10932819,4139,
21050478974,4142,4160,4169,24273245317,0x169b30a339c8425,4173,5352,0x600465a4719e629c8311,11464776,4164,4148,22526363044,10302005,4163,
51270772515877,0x1748d2e049cd546,8716386,4180,25808336196,5253,27375490181,4151,4149,13382695,23970870595,28211925056,87437518180758657,4149,4171,
0x662932408e98e70513ce,20965040338,4163,9150556,4191,9539673] (by decide +kernel)

private theorem part122 : Refutes moves 0x1000000400000000000000000 0x124d8c50004000101000000400 :=
  branch 1 0x1000000400000000000000000 0x124d8c50004000101000000400 85 0x12ed8c74044080111002000400 (by decide +kernel) part123 part124

private theorem part120 : Refutes moves 0x1000000400000000000000000 0x104d8c50004000101000000400 :=
  branch 1 0x1000000400000000000000000 0x104d8c50004000101000000400 97 0x1ccf8c50014000183000000400 (by decide +kernel) part121 part122

private theorem part118 : Refutes moves 0x1000000400000000000000000 0x10458c50004000101000000400 :=
  branch 1 0x1000000400000000000000000 0x10458c50004000101000000400 91 0x1a45cc52004012101080000400 (by decide +kernel) part119 part120

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part127 : Refutes moves 0x2100000400000000000000000 0x1d4fc610010041082100000400 :=
  finish #[
46480215745187,0x17f501575c675a4,4136,4972,0x17f402262c67427,0x174ca45fd04d2f8,4176,0x5fea208ce134ea1ca18a,4165,4170,4180,5352,0x180b31633c092b3,56169534657768,11448371,
4168,4972,0x9b039948e33cc5346,4882,12555089,20939882579,4165,4170,4180,13005387,0x1a46e9a628fa4dc,0xa9128716691a32427,13005194,0x2e9a91c09360425489ca546,4175,
4180,4189,39747284530305,11080262,11448399,4176,11849800,4151,4169] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part129 : Refutes moves 0x180000400000000000000000 0x1367461e000053000180000400 :=
  finish #[
12547398,5446,52870297441320,0xa8e8130166290041d,4174,4147,4153,27377415207,17593590305,8769598,4194,52931563214244,20848370811,4165,0x60483198aa393084c540,
4180,13390202,18097681222,4153,12178146,12616734,8700958,4179,8769613,4191,0xd2302730e02cc53b5,0x9a0811489d34c5171,11453479,8769599,4191,
13390887,46187326006117,12214494,11011090,8683561,4180,4173,11079763,4168,4161,4175,22293533717,44643543692327,4165,42410163852025,
4137,52838340776697,4130,5252,22601589209,8769605,4194,0x9fb6964ce0485d171,8700336,43904810935434,19726618886,19722282107,4181,4173,0xa618126902605d427,
36500287255268,4129,4143,4157,4179,10178724,0x17286d662a7f5a4,4157,19332354810,0x1986fe9433f9353,52661408761158,8699961,4181,4180,0xc0998b014ae05d28c,
4879,8770102,82880139891307940,8683581,4181,11079763,4161,4168,4175,0x9fb1130242605d483,8700174,4577,4366,18362974430,4179,
12603479,52571586724623,4151,25010229305,13004866,46288054112729,75347428972762151,45652428740003,36787611550641,4173,0x8004feb169185d22d,22693830878,4879,56166478823809,4181,
4174,4183,4165,4179,4318,4957,36790732321303,27425050650,4175,12595756,46481788945733,4175,22599292037,10183394,10691718,
27416618107,8683581,4173,4175,18247901406,22671016674,9449866,4174,4183,11010810,4137,4151,4165,13004883,11448348,
4176,4168,4160,4136] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part130 : Refutes moves 0x100000400000000000000000 0x134f4610000041000100000400 :=
  finish #[
8770698,25832755578,10294408,4157,46424343827026,4189,17964242056,0x198901c2ea800b1,10952779,4137,4179,17964626512,57785354408879,11792976,4155,
54553175713188,4179,94583633136759366,4176,4168,4160,19272847919,28213474437,0x18073153bb46544,4171,4194,49160232670528,22601589893,4171,4165,
13005366,25808745208,54556332143637,56136878560174,4165,4183,4156,9438331,0x18125614308d1c4,4138,0x1985010ce1b5486,26636890145,4152,28213474247,11068352,
4165,10953674,0x197eb11a4958481,22669479989,4169,4151,4160,11338593,0x1a470253ca8e543,4151,10232871,17960771630,9539683,4181] (by decide +kernel)

private theorem part128 : Refutes moves 0x100000400000000000000000 0x13474610000041000100000400 :=
  branch 1 0x100000400000000000000000 0x13474610000041000100000400 91 0x1367461e000053000180000400 (by decide +kernel) part129 part130

private theorem part126 : Refutes moves 0x100000400000000000000000 0x11474610000041000100000400 :=
  branch 1 0x100000400000000000000000 0x11474610000041000100000400 97 0x1d4fc610010041082100000400 (by decide +kernel) part127 part128

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part131 : Refutes moves 0x400000000000000000 0x11550410000000000000000400 :=
  finish #[
11080240,4882,54553176056363,4143,4159,98023992363602595,27426525773,4147,4157,4872,25806037931,88246860155536308,4175,4195,4165,
12169658,25848763151,46480037299315,4175,28213964899,4140,26637292400,57782847751400,4175,0xcc58cf311a4b4d21d,52939006603861,8724524,4183,13776104,0x180748d3c2ef30f,
17877274692,4193,4181,13390027,25698133224,13006150,26634142854,4175,4179,4185,12604362,13005585,4160,0xa6a7f49be33a7d0e8,4141,
4155,5446,0xb9d4fe6da62a902a9,11464763,4140,25764876491,25848378199,17872733322,52678986462056,11849780,4169,8716885,4177,4185,13366218,
47693073900175,4141,0x5d42d87f4d0262aef1ba,4148,25018291146,4160,0x18cf024280ba546,9539673,4193,9924699,4176,5352,0x197aff1ffb4d53f,11731809,52938026238926,
5249,52937288040684,52939735597292,4155,4149,4173,4183,0x435cbf8cccc1a33fc088,10204110,4155,4135,4185,56082185569512,0x5a30f369b302004672e9,26636518350,
4181,11464763,4148,4180,51187373364362,25849446942,9020550,4159,5258,93995206066110757,4169,26636890199,9924648,4168,8770295,
11464926,46292022567869,0x18ce43c801ce307,23481249885,4168,4180,4687,21091640270,40018216710233,4575,0x169919d77c09292,9823174,4147,19538604113,12620351,
0x1699024e69d347d,41629180612691,4189,4195,4187,9154657,4194] (by decide +kernel)

private theorem part125 : Refutes moves 0x400000000000000000 0x11450410000000000000000400 :=
  branch 1 0x400000000000000000 0x11450410000000000000000400 92 0x11474610000041000100000400 (by decide +kernel) part126 part131

private theorem part117 : Refutes moves 0x400000000000000000 0x10450410000000000000000400 :=
  branch 1 0x400000000000000000 0x10450410000000000000000400 96 0x10458c50004000101000000400 (by decide +kernel) part118 part125

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part135 : Refutes moves 0x2040000010000000000000000 0x19499c30400400104082040000 :=
  finish #[
11834688,5242,24001168504,23222715047,4171,4141,4149,22500930693,94382172560655399,22557975591,4143,13389895,4131,57784533849314,5446,
25680213130,4152,0xc0426502662d23680d25faa915a2,4147,4161,17767375634,4171,4175,4750,12980427,4142,36478151333000,12620535,0x18ccd1852400423,4161,
44213207347596,4182,4167,11464793,13776198,56164856509659,38076028601570,4163,4177,13776098,46087443580230,57779528536739,10293923,4175,0x2356629b050b18691a8c5a3,
4163,4149,11464802,9924676,4168,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part136 : Refutes moves 0x2000000010000000000000000 0x184d0410400400000082000000 :=
  finish #[
13390781,56012599632050,4153,23404897111,4175,0x577133732ead3ec09369,4141,52783407469011,0x4d5d21813315d5aef166,9924668,4180,25845572839,12584074,0x197eeae30aef0fa,9924668,
4192,4478,0x80d7f03f5a5bf9544,4158,51324936889086,4141,51188237308459,21747503765,9424941,26583778320,4175,4173,5063,27385008425,4142,
11731241,4131,24213754923,4141,0x5d13aaa42395d5aef489,9924668,10309728,4181,4191,0x1812fe8debab256,10212396,24188588881,11846700,4134,10309677,
49231360079074,12236002,11846700,4150,4152,13373638,57776480801534,4181,11079755,4175,4168,4690,10294498,52935081116117,4152,
4161,11818210,25806049874,54434358674281,4152,4162,4147,4882,12604742,52872704201677,4141,43096517293382,0x181240d02955546,4138,4162,
4174,12980779,11818210,24203437282,4165,4161,20085019303,8724531,4191,4183,28213966050,4140,51316941878128,4176,4180,
27365057482,20085019018,4168,26587345857,26543760427,12619869,4185,36017633145974,54448518624394,4162,93492181863896384,0x50e273361024e13ab113,8704060,4173,0x4742ee34b2f9072d63ae,
20958589307,9474632,0x1a463f4e12261b0,4153,4189,10309721,4171,9916501,54449309135238,0x5944c54d0bbd47bab22b,45914016760688,4142,4177,25057104752,10309842,
4161,4181,0x181348d77975410,9154638,4188,4194,4182] (by decide +kernel)

private theorem part134 : Refutes moves 0x2000000010000000000000000 0x18490410400400000082000000 :=
  branch 1 0x2000000010000000000000000 0x18490410400400000082000000 90 0x19499c30400400104082040000 (by decide +kernel) part135 part136

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part139 : Refutes moves 0x4002000010000000000000000 0x12c30e11501080080444002000 :=
  finish #[
0x18b4cda30b48165,10691247,4167,24228992317,13353629,28215121122,4119,0x198b48ce8a9148a,4147,0x1983184e8846546,4171,4167,4175,47460214497513,12236093,
12980274,57783779660154,4147,22669865339,25059452042,0x1756a390d226184,4147,4189,4171,52936430846738,4137,4186,0xd234389c998b4c480,0xb484e530662a9142b,4147,
27391480869,47593715684274,4175,13775630,39570716775844,11010125,4137,4171,56095276495609,18094716042,23960544394,4165,4173,52939761091120,18096051128,
13361203,28214734889,4136,12554589,19027952555,27417318522,25848759236,4152,4159,4143,0x181318691aef3bb,4140,12620656,98033214746583707,11010102,
4165,76123056866243200,0x5190798c2eac53aef2ad,9924652,4176,4180,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part140 : Refutes moves 0x2000010000000000000000 0x16c10410400080080400002000 :=
  finish #[
49413091627846,73792530553156021,9446316,4161,4483,27425051111,10236742,11042863,4159,12234819,4126,22678254918,46445065999686,11464783,4140,
54443597648506,43869611549004,4159,5036,12227518,0x53d1498c2ce9a61ce42c,4179,4159,25043071948,4140,4148,0x1732a06049be4e2,19256087878,10302035,4169,
4179,4163,57781103080586,46086645907832,4177,4880,9396593,4143,4149,90340884086714758,4188,0x530a8c98a1f6908f72a1,0x8062668b1a10463c7,4167,13390569,
45777419374936,9400362,74536315811664002,25808736492,97200217651847711,11710505,4135,4167,57743616545353,11060362,4187,11464771,4188,28215480954,20183278717,
4171,4687,9445971,11464766,11079772,4154,9916495,4182,4174,25715315055,9823350,13389883,52941421352058,8676112,4171,
4177,0x1681185d5975489,8769626,9925488,4290,25671308045,25846837308,20330189680,22382695468,90160111973843727,10981444,8769584,9154653,4186,4188,
4192] (by decide +kernel)

private theorem part138 : Refutes moves 0x2000010000000000000000 0x12c10410400080080400002000 :=
  branch 1 0x2000010000000000000000 0x12c10410400080080400002000 98 0x12c30e11501080080444002000 (by decide +kernel) part139 part140

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part142 : Refutes moves 0x80000010000000000000000 0x12412412400000402000080000 :=
  finish #[
4691,13775110,24246871361,10281027,43211238454690,4177,4175,25850679672,40761676161400,56169662006692,4135,4157,0x2cb26002269148e308414db,28215121122,54443554108131,
4155,11464727,4164,46475417502549,0xc0469118548aef5a4,8769604,9924701,4192,22523723923,46131565786250,25059848264,0x9033f6eae04bfa22c,0x180a40262a8e47b,4150,39644201002005,
4173,12235632,4976,22602756976,4136,4185,18582303600,4168,10309724,4171,56066546451594,25656595500,84322706452636610,9924655,4168,
12981104,11006905,4136,10302026,4174,4179,42681833362349,51182540743314,10281541,8769623,4189,0x2d2e5f3303925dc2e9d542c,4176,4191,97152112608736580,
42331520668805,26585420341,25059848267,9916476,9155062,4192,4182,4194,4186] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part143 : Refutes moves 0x10000000000000000 0x12492410400000000000000000 :=
  finish #[
26527728966,90540335053432034,11464775,5446,9814385,4161,28215481200,4477,24211436111,4169,4174,9924691,4168,24205349932,49689662059658,
4157,97056247201194732,0x18c2ead7785017e,4176,4180,94487718960846050,25847129314,9924665,25058640308,21006611682,4180,0xae850f31630977307,23481627128,4174,4164,
4179,0x5d5cc50a0bbc5d9754e2,4182,4194,4186,0x538aef40b185fca8622f,8729456,4183,72742232621974280,0x604a0298b009d5977226,10309716,4176,35845826430072,52665706492784,4164,
52934324605983,4176,48087134090284,12583749,42425766282564,4163,13775280,49160273846446,4192,19306034308,10309692,4171,17860112982,9916508,4174,
4182,4194,0x21f9d31c2699185fca86291,22659454178,52818796311107,10309716,4176,13390775,57783587476425,0x1680ba1a40f75a4,4141,4147,11465208,4188,13390704,
9449854,10309710,9150554,4183,4598,0xa7e98a734baa885a4,0x198a681441be302,4148,18740531277,4194,4195,9539679] (by decide +kernel)

private theorem part141 : Refutes moves 0x10000000000000000 0x12412410400000000000000000 :=
  branch 1 0x10000000000000000 0x12412410400000000000000000 91 0x12412412400000402000080000 (by decide +kernel) part142 part143

private theorem part137 : Refutes moves 0x10000000000000000 0x12410410400000000000000000 :=
  branch 1 0x10000000000000000 0x12410410400000000000000000 85 0x12c10410400080080400002000 (by decide +kernel) part138 part141

private theorem part133 : Refutes moves 0x10000000000000000 0x10410410400000000000000000 :=
  branch 1 0x10000000000000000 0x10410410400000000000000000 97 0x18490410400400000082000000 (by decide +kernel) part134 part137

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part145 : Refutes moves 0x40000000400000000000000 0x10415454410000004004000040 :=
  finish #[
27426525818,21899236007,4149,41233015607845,76055994708074726,4183,4163,72131574191895163,27406066226,12554802,12984371,4117,19900277011,4149,0x2690fd4c32c06c5779052e7,
4164,26636862783,0x1812b9144a90540,10276949,4183,8675923,4171,4176,22301537320,0xcc41ef02420aef0fc,4164,4949,10277151,4163,27426190165,
24161101126,25706860621,8769575,9924701,4192,37959788450426,0x165c72a33cbc310,18591072941,4167,24272859903,54551522706382,17767374911,4176,4175,26636870982,
0x1000d22024098ce7e542a20541,0xb401e87e5a6c6747b,45739902059088,4175,4167,4177,11465960,4140,0x1722e9e33aef177,48095911269006,74707509264675960,0xa7e5df19ce51d4083,4165,4175,9924697,
4176,4188,0x53d0004507e6338a1178,37956635092386,4188,18112024808,18535051498,18533511935,4140,4188,22651925736,4159,4163,43217615377237,22532088091,
4171,0x32fe62a684fcbbc50c673ac,4148,0x6030405de28633b4d0c7,4133,4169,18530816876,8770792,0x173a17450c6741c,54546865087518,4177,4167,11850018,4133,4169,
0xba70babbe339773ce,4188,4192,0x5984675ded35423f6546,5255,49435126595874,4169,4153,9049320,4386,94172750065238896,4148,9150556,4191,23446540578,
0xa0d7ed19d77977428,0x17262e8bb85d370,4191,4188,9539680,4181,4193,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part147 : Refutes moves 0x4000000000400000000000000 0x10454550414040000000044000 :=
  finish #[
24113836270,18095273095,4155,94103929111503790,4192,12621126,22661861950,10150670,22670156455,8671331,4173,4171,22659731819,13390677,56166246962498,
4155,95034073432741181,4171,11849805,4133,4169,51323362243436,4136,0x18cebadd58a33ce,9924904,4188,4180,4881,48095909344017,4192,
25060983163,23450776604,26634134380,9924685,10309728,4171,17704965163,24270930691,4153,5352,0x169aa41d5aeb303,4168,4136,22451762502,24270931176,
4169,5060,0x169b3053a1bd48a,4147,11449576,4136,10309688,4191,4694,54549926970506,23481249881,4180,54550391477197,25690137361,8716347,
5446,0x1804d0da6a90301,4153,13005660,4136,0x8e53f8fee04c5c50ed357797742c,4180,4192,9151235,87194108325950602,0x173b19c51977412,4180,10309728,9539679,4193,
4187,4181] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part148 : Refutes moves 0x400000000000000 0x14454410410000000000000000 :=
  finish #[
51323362243012,0x2caa604c55186a5a6c675a2,51168743806277,0xb4d98a9f8d4d21487,0x175488a62905423,4195,4161,19346728060,0xa8598a41437a88487,4163,12234815,11464784,4180,9078086,56148069364652,
10309662,11464914,4188,87031936677475278,11464913,4180,23484331334,25061773948,11850043,17862423108,4180,10309724,4171,9539679,4193,
4181,23484330436,0x4133ab8cf024b01d5225,13005005,54546724881155,4167,4183,4176,12621032,0x159330e041aa8cf024eaaef311,4156,0x169a09073c6747c,0x1812fd936c673ac,45862526682247,4168,
11464761,54552385266732,9539679,4193,9916507,4174,21023749352,13391080,12558803,4167,23422890825,4165,54549972432198,23204693107,10232405,
11448409,10309688,4191,4176,48027980706736,25059419368,4165,10309854,4191,0xb4d5107542e91942c,4187,20309586017,4192] (by decide +kernel)

private theorem part146 : Refutes moves 0x400000000000000 0x10454410410000000000000000 :=
  branch 1 0x400000000000000 0x10454410410000000000000000 98 0x10454550414040000000044000 (by decide +kernel) part147 part148

private theorem part144 : Refutes moves 0 0x10410410410000000000000000 :=
  branch 2611 0x400000000000000 0x10414410410000000000000000 90 0x10415454410000004004000040 (by decide +kernel) part145 part146

private theorem part132 : Refutes moves 0 0x10410410400000000000000000 :=
  branch 1 0 0x10410410400000000000000000 64 0x10410410400000000000000000 (by decide +kernel) part133 part144

private theorem part116 : Refutes moves 0 0x10410410000000000000000000 :=
  branch 1 0 0x10410410000000000000000000 70 0x10450410000000000000000400 (by decide +kernel) part117 part132

private theorem part102 : Refutes moves 0 0x10410400000000000000000000 :=
  branch 1 0 0x10410400000000000000000000 76 0x10510400000000000010000000 (by decide +kernel) part103 part116

private theorem part78 : Refutes moves 0 0x10410000000000000000000000 :=
  branch 1 0 0x10410000000000000000000000 82 0x10410000000000400000000000 (by decide +kernel) part79 part102

private theorem part40 : Refutes moves 0 0x10010000000000000000000000 :=
  branch 1 0 0x10010000000000000000000000 94 0x14010400000000000000000000 (by decide +kernel) part41 part78

private theorem part2 : Refutes moves 0 0x10000000000000000000000000 :=
  branch 1 0 0x10000000000000000000000000 88 0x11000000010000000000000000 (by decide +kernel) part3 part40

private theorem part0 : Refutes moves 0 0 :=
  branch 1 0 0 100 0xfffffffffffffffffffffffff (by decide +kernel) part1 part2

private theorem noGood : ¬ Good 201 15 := by
  rintro ⟨c,hp,ha⟩
  exact part0 c hp ha (by simp [Red]) (blue_zero c)

end Case201
private theorem no201 : ¬ Good 201 15 := Case201.noGood

namespace Case206
private def hints : Array (List Nat) := #[
[],
[],
[13598],
[],
[],
[13189],
[],
[],
[12780],
[],
[],
[12371],
[],
[],
[11962],
[],
[],
[11553],
[],
[],
[11144],
[],
[],
[10735],
[],
[],
[10326],
[],
[],
[9917],
[],
[],
[9508],
[],
[],
[9099],
[],
[],
[8690],
[],
[],
[8281],
[],
[],
[7872],
[],
[],
[7463],
[],
[],
[7054],
[],
[],
[6645],
[],
[],
[6236],
[],
[],
[5827],
[],
[],
[5418],
[],
[],
[5009],
[],
[],
[4600],
[13598],
[13189],
[4191,12780],
[12371],
[11962],
[3782,11553],
[11144],
[10735],
[3373,10326],
[9917],
[9508],
[2964,9099],
[8690],
[8281],
[2555,7872],
[7463],
[7054],
[2146,6645],
[6236],
[5827],
[1737,5418],
[5009],
[4600],
[1328,4191],
[3782],
[3373],
[919,2964],
[2555],
[2146],
[510,1737],
[1328],
[919],
[101,510],
[101]]

private def values : Array Nat := #[
0,0,0x200000000000000000,0,0,0x400000000000000000,0,0,0x800000000000000000,0,0,0x1000000000000000000,0,0,0x2000000000000000000,0,0,0x4000000000000000000,0,0,0x8000000000000000000,0,0,0x10000000000000000000,0,0,0x20000000000000000000,0,0,0x40000000000000000000,0,0,0x80000000000000000000,0,0,0x100000000000000000000,0,0,0x200000000000000000000,0,0,0x400000000000000000000,0,0,0x800000000000000000000,0,0,0x1000000000000000000000,0,0,0x2000000000000000000000,0,0,0x4000000000000000000000,0,0,0x8000000000000000000000,0,0,0x10000000000000000000000,0,0,0x20000000000000000000000,0,0,0x40000000000000000000000,0,0,0x80000000000000000000000,4,32,0x100000000000000000000100,2048,16384,0x200000000000000000020000,1048576,8388608,0x400000000000000004000000,536870912,4294967296,0x800000000000000800000000,274877906944,2199023255552,0x1000000000000100000000000,0x800000000000,0x4000000000000,0x2000000000020000000000000,72057594037927936,0x800000000000000,0x4000000004000000000000000,0x20000000000000000,0x100000000000000000,0x8000000800000000000000000,0x4000000000000000000,0x20000000000000000000,0x10000100000000000000000000,0x800000000000000000000,0x4000000000000000000000,0x20020000000000000000000000,0x100000000000000000000000,0x800000000000000000000000,0x44000000000000000000000000,0x20000000000000000000000000]

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def moves : Rules 206 15 :=
  cachedRules 206 15 (by decide) hints values (by decide +kernel)

private theorem finish {r b : Nat} (words : Array Nat)
    (h : redCheck moves (readTree words) r b = true) : Refutes moves r b :=
  checked moves (by decide) (by decide) _ h

private theorem branch {r b} (w rr bb p br : Nat) (pass : reaches moves w r b rr bb p br=true)
    (l : Refutes moves (rr ||| 2^p) br) (t : Refutes moves rr (bb ||| 2^p)) : Refutes moves r b :=
  join moves (by decide) (by decide) _ _ _ _ _ pass l t

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part4 : Refutes moves 0x14006000000000000000000000 0x6bfe93354a803c000000000000 :=
  finish #[
0x19b257413ba0120,0x16b51cdd54d9304,0x19bed684fbaa2ef,22577669466,4140,10620990,4150,17510466308,4574,9385106,4133,11911223,0x568c73754d066cbbf3db,11047704,4155,
4179,4169,56595063542524,4874,22626767620,4142,8676397,0x1683365d647c560,4142,4295,22625506650,4140,4144,4875,22624363866,
11137103,4157,4150,4178,25218876051,4875,19981951945,4175,4169,4288,11105041,4155,4669,46516276945974,4179,
22800511263,9478215,4174,4162,4165,4171] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part5 : Refutes moves 0x4006000000000000000000000 0x73d2903502803c000000000000 :=
  finish #[
12276989,44626582684736,20100563618,4155,4163,13496483,19202982549,4155,0x19be6f0b20292ff,4145,4140,27645530557,0x447cd582536a061c816d,4150,41305015965018,
84498934295630397,4164,4184,21647692040,44328672925120,12317751,4158,9900114,54917281095875,19953177426,13496360,13455643,42684386649434,44325357028605,4141,
4145,4155,11076574,84606307531293125,21646119697,9900110,4184,4156,11060288,51665397474270,4162,4158,4165,4169,4176,
56515053028694,0x1a7ca79db3b548a,4158,4383,25221223467,4144,56615458656905,11075783,8654928,4166,4171,13456544,0x183e2506c1c81c5,4145,13468705,
12677271,11075612,0x8128fd365daa97421,4158,4179,0x1a7d0354f4066908d91e9134a0,4171,4195,51307130770069,44557845751028,4189,17772155949,25152557740,10707633,4171,
4165,23371801265,4757,0xbab00011a6ca89437,91245766032261319,46701849220058,0xbbe68e8842311642b,4171,11075677,4165,4176,4162,4186,4169,18380567894,
9900522,4896,4506,27625980704,9900101,4189,4171,4184,11456922,0x181b374b2298421,27626435340,4150,4157,11457501,21703988159,
0x176cbb4899190c7,4189,4174,94906418199450974,8647456,20209668165,4160,4176,12280306,9868343,4152,39497107104133,44908767998914,4184,4171,
8676314,4586,8676128,4171,21755978690,21930570138,9900099,4189,11509848,4145,49984208880673,10683528,9028384,0x19aaed14f8403c8,4160,
4162,23533178955,4140,4153,4169,4164,4156,4177] (by decide +kernel)

private theorem part3 : Refutes moves 0x4006000000000000000000000 0x63d2903502803c000000000000 :=
  branch 1 0x4006000000000000000000000 0x63d2903502803c000000000000 100 0x6bfe93354a803c000000000000 (by decide +kernel) part4 part5

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part8 : Refutes moves 0xc003000000000000000000000 0x73fe4879e1e007800000000000 :=
  finish #[
5275,27634255003,12665020,4154,4155,74116335176610453,4141,53223801082027,9449665,4161,4170,27635152012,87345746741752987,12690773,27635152032,
25874755622,4152,4141,97654677714105792,13489399,37847407039936,4176,58265604912478,4134,49435135022235,25923494879,0x1a7ca4a6c8400c6,4169,4161,4163,
4164,4170,12689981,12317471,0x176b069aab5e31f,4152,11915332,11059398,56573865599764,11530306,13489598,13493395,8627551,4155,0x801742a160929a4f7,
4169,23424106563,4135,4175,4151,4183] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part10 : Refutes moves 0xc002000100000000000000000 0x735ed87981a80c006260010000 :=
  finish #[
5472,90371424887706555,10928209,91254468679430621,56576233567163,27628008800,4166,44556075655645,4156,4177,4150,5472,47577991860885,27559687224,28429623358,
22805344539,9454367,4177,27640750847,0xc7d20937daa098363,11862073,4178,4156,4151,4169,40623657615515,11047111,4169,0xb54814b5e9ebad55b,8676702,
0x18241197c2f709b,4158,4175,8675900,17770181982,4191,4668,20897432928,25136193575,4140,4137,4150,0x1a7a08942af023c,11465378,4150,
36397378302744,95019233560613436,4151,4169,10621677,4573,27644785920,23424073764,4191,49366552147008,5164,0x182f4fe6caf00a6,4175,4143,0x19b24111089a09a,
95140545453909248,0x89a53ced9d5cdf556,0xcdf134a79dfaf0380,4143,4158,11916241,4156,4178,4165,12689481,4149,4138,4127] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part11 : Refutes moves 0xc002000000000000000000000 0x735e5051918004000000000000 :=
  finish #[
49603847103731,90776702296356083,4157,0xbad758efd3b3be37e,5275,0x19b4be26e8413d0,4161,4162,48367632659294,5258,25845961686,8667198,4171,4176,4170,
0xcdf6bc9fa0d2f749f,11502448,12690291,11502747,9453623,4156,26015252668,0x176c8514241d36e,11477867,4153,4129,23479981192,24290120855,56579638080358,19363655732,
4156,56578772902777,4143,4170,4178,4177,11027594,54928500422078,53318772748765,4139,4141,84319506796749573,4127,58231386878096,10171838,
12690878,9396255,4139,12276791,12678282,0x19bebbd0a3ab49b,11087924,4183,4158,5261,27552036186,4148,54959730028919,4895,9003283,
4157,4143,11444279,4153,4169,95265357207044352,27644359835,4150,56577774605758,24967554390,4153,27628795035,18182825312,11857964,54945687921819,
9449519,4152,4155,74221880152339489,4166,4170,0x8089bee819caf20e8,12313656,0x176eea910a99560,4178,4150,12690394,5467,24364807515,4135,
9867347,4152,20208857982,9900102,4156,4176,4184] (by decide +kernel)

private theorem part9 : Refutes moves 0xc002000000000000000000000 0x735e5051818004000000000000 :=
  branch 1 0xc002000000000000000000000 0x735e5051818004000000000000 68 0x735ed87981a80c006260010000 (by decide +kernel) part10 part11

private theorem part7 : Refutes moves 0xc002000000000000000000000 0x735e4051818004000000000000 :=
  branch 1 0xc002000000000000000000000 0x735e4051818004000000000000 84 0x73fe4879e1e007800000000000 (by decide +kernel) part8 part9

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part14 : Refutes moves 0x6002200000000000000000000 0x695fc83743c0c4444000000000 :=
  finish #[
56505094951193,18615743543,27590832604,0x1742d7455af73c7,4167,4191,4174] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part16 : Refutes moves 0x4002208000000000000000000 0x2bced9712780944d4144100000 :=
  finish #[
0x1765049704df55b,0x4ce3bc8190757006b433,13488156,27557278561,13456012,56443700310668,4155,4152,4164,18616210572,38860986601711,13476902,19857723448,21050126812,4166,
4158,4150,84759720317784436,17484559616,4144,54959841080259,9065728,23618171852,9900522,11915356,4196,4156,4178,0x18e8ee54829e249,4155,
4169] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part18 : Refutes moves 0x4002200000020000000000000 0x2b47493929c084544002240500 :=
  finish #[
20964643301,9089284,42390530433286,4133,9818702,4156,4574,23349810312,41305819313504,4167,4198,13471831,4166,5376,27591643986,
4156,10278045,20275942557,4164,4170,25010316635,0x19bc9b06b96443d,4143,12293471,56596663808498,4238,51440919111003,4155,9901107,4156,
4152,4180,4164,35347824563648,20168357312,20907053124,4130,27595236403,0x183aee66f47f2a2,4198,23263842441,9831668,4147,12293158,4152,
12305234,0x17790306d4df442bde3f95b55a,4174,9695302,4154,4150,11089242,27595240212,9089812,8646738,4170,53008634057981,5171,5158,0x19bebfe08cd948d,
4166,4174,22769426511,4155,4169,4183,4162] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part20 : Refutes moves 0x4002200000000000080000000 0x2b46483d2585a4454000400000 :=
  finish #[
54941523899840,27641975748,18616571020,24176231672,4169,4174,4178,5373,0x5aec0c521368b03a555e,20277154273,0xcda6bd04a062900c3,25119395913,4145,4175,4155,
11806046,13456442,11089042,24188286299,38127661229022,4174,4178,0x505b5e2e30454d29e3d6,4155,4169,4176,25875534886,5261,17644774541,4143,
4164,0x66e88d05a9ddd79cd238,4145,20278687072,41524024571135,0xb4305537d68897440,4144,4148,12305179,4155,11399452,11530524,11087943,11133110,22803767786,
4164,10277659,4145,9809979,4174,4166,4150,4158] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part21 : Refutes moves 0x4002200000000000000000000 0x2b4648390180a4444080000000 :=
  finish #[
26014586208,4768,25828700622,4145,13471796,49977519608045,0x6384dc0d8d644c4d955b,54909617304538,4148,26811335154,0x88729a5766cb5555d,4170,4164,4152,20003524876,
27590308305,4145,44331294917978,5472,0x182d364e6aff3d6,4150,0x512cdf5b1364aa2e824e,4135,4198,4183,4175,4167,41524050891602,13472522,13472217,
25932235052,4191,4175,4167,48103924012184,56579555431571,5466,26713646231,9900111,10637380,10638494,27645547773,21785891998,4164,4176,
0xc0d5ee50d1295b295,4150,4158,4178,4154,73096059661157126,0x8009bf1dcb017155a,27561681556,23490233686,20070233439,4147,4167,9810510,0xc7f50a56d042df560,4198,
4150,4158,4174,12210476,19331597350,52990544556302,4150,4158,87938793310240939,4145,4152,25202487886,53258891424334,8647317,4164,
4163,51223604543928,25199550724,27590755389,4153,4145,20687704738,40959907406886,4175,10278041,12608078,21047652822,4156,4164,4158,
4170,76210436743992561,10569050,18475631654,4152,4175,5373,26008601464,27592859727,4158,5158,9900513,4164,27616756876,56559017165983,
17712267299,22685540401,4148,4183,4176,4169,4165,12689474] (by decide +kernel)

private theorem part19 : Refutes moves 0x4002200000000000000000000 0x2b4648390180a4444000000000 :=
  branch 1 0x4002200000000000000000000 0x2b4648390180a4444000000000 31 0x2b46483d2585a4454000400000 (by decide +kernel) part20 part21

private theorem part17 : Refutes moves 0x4002200000000000000000000 0x2b464839018084444000000000 :=
  branch 1 0x4002200000000000000000000 0x2b464839018084444000000000 53 0x2b47493929c084544002240500 (by decide +kernel) part18 part19

private theorem part15 : Refutes moves 0x4002200000000000000000000 0x2b464831018084444000000000 :=
  branch 1 0x4002200000000000000000000 0x2b464831018084444000000000 75 0x2bced9712780944d4144100000 (by decide +kernel) part16 part17

private theorem part13 : Refutes moves 0x4002200000000000000000000 0x29464831018084444000000000 :=
  branch 1 0x4002200000000000000000000 0x29464831018084444000000000 97 0x695fc83743c0c4444000000000 (by decide +kernel) part14 part15

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part23 : Refutes moves 0x4082000000000000000000000 0x3b43569910c104000000000000 :=
  finish #[
28446470924,4974,19229410550,4163,23463985452,4179,4161,4979,11080558,47695706821774,0x168640d48844423,4166,4167,4170,0x9a774b36a6ea983dd,
46695474344223,4176,4877,22711083789,10707819,4147,4153,11088957,23574307201,11477867,4129,9515065,4198,4189,4186,
4165,44451372298428,11137318,10731594,56613192967421,8648022,11108417,51496728879995,0x1834ebe0b29f37e,4170,22584476827,4183,4189,46267561063485,0xad167036daa9542ed,
12305456,4162,24340440205,51271886090989,12689452,4149,4876,53228699137159,9515085,4198,19489084093,4166,4189,0xc7e0745a451971306,4156,
4176,4188,4160] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part26 : Refutes moves 0x4003000000008000000000000 0x696b4a9950b007840000074010 :=
  finish #[
77634661178512626,13472923,11837582,13472907,0x89e01c9f2054d90c1,56505155687565,4152,4142,4155,52957167562948,4158,4165,11830036,52938226102468,4155,
46581826306833,4150,4148,4193,0x182ad4c4bc1a0b9,24230532043,22651970188,10735678,4183,11830427,53228741534859,4162,12251931,25845584665,4167,
4170,51396241728652,27593626764,10731585,4196,53233647633085,12689595,48249885791186,12628741,25864717266,49775553540863,4151,10731582,4165,4183,
12689596,0x1834279422f82be,11837527,4141,4186,11895564,21989209534,10737086,13886336,28448117516,4165,0xcd91334fd45a31440,4148,20026684256,4134,
4174,4158,11112494,4170,4150,4191,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part28 : Refutes moves 0x4003000800000000000000000 0x6b7a4b5940e60f901c00600100 :=
  finish #[
25059521691,49655988130971,13471790,0x16a7365d5a921ce,0x1834d466cb5c4f5,4139,17561678986,35966227760266,8589355,4155,5269,27592860832,4169,22643582298,26812658438,
46490783393114,4141,4135,13071110,47817039618822,4170,20094239508,4141,4148,4150,25848001189,25848030654,24985506751,54915622348122,4162,
25990127990,4141,4135,0xc1f8ef3660483131f,10706996,4178,4196,4183,4165] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part29 : Refutes moves 0x4003000000000000000000000 0x696a4a19c0a00f800000000000 :=
  finish #[
46510507922878,76652891437839209,13472517,12690208,8672219,4175,4170,49534967845220,11059973,4193,13882124,5074,0xbbf8e6be29ea7e28c,4158,21988859983,
4196,4183,4165,4178,4969,5078,0xb559b34f5a8ae855e,53228699148367,4170,0x69f27e9ba8d91ec1430c,4165,5466,0x4b233a77f3656882f488,4152,56564940440734,
11138009,4170,4164,25940305035,12690203,4160,36200804402217,22701032895,74323796161873342,74491432277464105,4152,4173,4170,4191,4581,
27592450533,4196,27635561818,53231090791173,20166828090,4149,4153,4165,4163,4155,24248160452,0x16b810d0929348a,4151,9847558,98252558499914912,
22585582944,0x19b2a2d77a9949b,11530314,4158,4150,24382378880,12690181,53228640138592,4151,0xc1a9b2d2945a9f380,4170,4164,5566,13881542,28429276510,
9847578,4163,4191,21988859983,4165,4196,4178,17762985306,12690778,8565723,4151,4139,53232827565402,54830494667237,4151,
4876,56505171981560,17762190294,4155,4173,4170,9847957,56514222167195,9426161,10686642,11055156,52901525975890,4163,10707018,4184,
4196,10264663,4152,4142] (by decide +kernel)

private theorem part27 : Refutes moves 0x4003000000000000000000000 0x696a4a1940a00f800000000000 :=
  branch 1 0x4003000000000000000000000 0x696a4a1940a00f800000000000 71 0x6b7a4b5940e60f901c00600100 (by decide +kernel) part28 part29

private theorem part25 : Refutes moves 0x4003000000000000000000000 0x696a4a1940a007800000000000 :=
  branch 1 0x4003000000000000000000000 0x696a4a1940a007800000000000 51 0x696b4a9950b007840000074010 (by decide +kernel) part26 part27

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part31 : Refutes moves 0x4002080000000000000000000 0x296b561340900c104100000000 :=
  finish #[
46359075988618,0x1a7f051453be440,4150,53261483479819,90791659503981323,27592791085,4148,4183,4162,0x4aecd976b1f8e7b4314f,51491955365209,9089083,4164,51661004182664,13882714,
27592365213,10285098,4162,4688,25060701054,4396,0xc7e5da2ace7afd492,9900097,4176,4188,4164,10663159,5184,21839856685,0x1758b5e3ea9e55a,
4165,0xa74838bf4b8aed311,4164,4193,4188,0xcd69be9d26d22b5be,41319022908671,10285148,4152,54914018095982,4396,48335672898293,23601857678,4142,26829435524,
56596909126389,4163,9539631,4193,4198,4506,4506,41327997161772,4176,4164,9900442,4506,9901402,13472036,12689818,
12313848,11108393,4191,4198,10686532,4154,4142,4160,28430890331,48057728357517,9491902,4186,4198,49755160039617,10707008,
4165,4171,4183,4196] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part33 : Refutes moves 0x4002004000000000000000000 0x2b6a5a91028004028010020000 :=
  finish #[
13472923,5466,25989366047,11030587,4151,5272,0xae883e87a0b916169,56513398936433,27591643546,40022329881049,4141,4163,56506949243761,4148,27592803193,
0x467ba25f11f9462f2498,4129,0x1682a31a8afa55b,21930168372,4165,4184,4183,4196,24228987275,48368549433619,0xcd95f11fda510a10b,4156,4150,11457982,53266408002594,
13882523,53234484003997,8896548,4133,4139,10736989,20279543133,4133,0x69ea849b86ccb8af009c,4174,4166,44917005951835,4153,0x19bf070b8cdc363,12653920,
98990122068792466,4156,11076362,4155,4141,53157406020546,11510152,10683027,4147,4165,98045037204575065,4198,4171,4186,4196,
27591283378,19539342473,44831088251761,4188,4164,51273499657662,11510845,4153,0x5d42d18ec5c515a3d5be,4160,53262194496667,9527688,4174,4574,84076788066591284,
4174,27592475308,46508836639130,4188,4196,5181,0x19b2ec94810a429,4174,5181,12223249,25035842321,9527388,4174,4196,11134010,
4158,4155,4176,4186,4165,27643163709,21752750558,4156,12305259,24398361741,25872785818,4171,4183,9528461,0x66cc1d1d05c56eaf543d,
4148,4156,10305636,4157,4152,4162] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part35 : Refutes moves 0x4002000200000000000000000 0x294b52f5009024010480040004 :=
  finish #[
5466,37238351455581,0x8cf9b8b966c9714ff,4196,0x69ec752cb3657a8ab48e,4178,4164,23534347202,0xbbfa7b1fe0d119437,4198,5469,10572656,24113942558,86573132782359401,4586,
0x18fd4f4b4b5e4f6,20112576571,4179,4164,4295,0x5449559b2ba0528462ac,13472493,11436324,4198,4868,11882695,9850963,9089080,4188,4164,
4178,4176,4295,10687625,4148,0x1673069ae2f549e,9900231,4176,4188,38129251934618,56614602252487,9847963,4183,8676800,4961,
23508312937,4179,4188,47834999653523,4163,58229014582618,25217307513,22643601505,4150,4164,4191,10326118,4157,4167] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part36 : Refutes moves 0x4002000000000000000000000 0x294a5295208004000000000000 :=
  finish #[
0xadf9b2ed9daa305be,4960,56512639915046,4145,12698685,51153297597495,4183,11489325,4193,58241193280470,11490155,0x19b2d5455916376,4183,4193,5277,
5184,0x49fbbf4eeef17541c48a,4184,26838992127,13059229,5277,25225245853,4164,4178,10621016,4156,4138,28434075948,12607788,58228030300960,
4150,9465907,0x177856e3a9bc1b6,26754373054,4196,9527596,4171,12608363,11489672,4156,0x2d560e3a8778a6883a9e5be,4155,4179,4193,4183,
4162,4186,12653419,4876,22642004843,4183,9089099,4388,21978853668,47783567888684,4193,4196,10317884,4160,18618606732,
80434051938451863,4147,11444524,76718415392653470,4157,0x225a0fc709b49bc55b5155a,0xb385eacfa6c28c232ba8b02360f6,4196,4183,0x4042f5342a611834349f,94239902232433047,0x4a83b66b0581aa89e37b,4163,4155,10707724,
91776998609769609,11444284,13472031,9437471,4149,4155,56559815373581,51146830484535,18505556070,4174,4176,4173,21174804563,4167] (by decide +kernel)

private theorem part34 : Refutes moves 0x4002000000000000000000000 0x294a5295008004000000000000 :=
  branch 1 0x4002000000000000000000000 0x294a5295008004000000000000 69 0x294b52f5009024010480040004 (by decide +kernel) part35 part36

private theorem part32 : Refutes moves 0x4002000000000000000000000 0x294a5291008004000000000000 :=
  branch 1 0x4002000000000000000000000 0x294a5291008004000000000000 74 0x2b6a5a91028004028010020000 (by decide +kernel) part33 part34

private theorem part30 : Refutes moves 0x4002000000000000000000000 0x294a5211008004000000000000 :=
  branch 1 0x4002000000000000000000000 0x294a5211008004000000000000 79 0x296b561340900c104100000000 (by decide +kernel) part31 part32

private theorem part24 : Refutes moves 0x4002000000000000000000000 0x294a4211008004000000000000 :=
  branch 1 0x4002000000000000000000000 0x294a4211008004000000000000 84 0x696a4a1940a007800000000000 (by decide +kernel) part25 part30

private theorem part22 : Refutes moves 0x4002000000000000000000000 0x29424211008004000000000000 :=
  branch 1 0x4002000000000000000000000 0x29424211008004000000000000 91 0x3b43569910c104000000000000 (by decide +kernel) part23 part24

private theorem part12 : Refutes moves 0x4002000000000000000000000 0x29424011008004000000000000 :=
  branch 1 0x4002000000000000000000000 0x29424011008004000000000000 81 0x29464831018084444000000000 (by decide +kernel) part13 part22

private theorem part6 : Refutes moves 0x4002000000000000000000000 0x21424011008004000000000000 :=
  branch 1 0x4002000000000000000000000 0x21424011008004000000000000 99 0x735e4051818004000000000000 (by decide +kernel) part7 part12

private theorem part2 : Refutes moves 0x4002000000000000000000000 0x21420011008004000000000000 :=
  branch 1 0x4002000000000000000000000 0x21420011008004000000000000 86 0x63d2903502803c000000000000 (by decide +kernel) part3 part6

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part39 : Refutes moves 0x4100008000000000000000000 0x29ca7820840450082000100000 :=
  finish #[
13473214,0x99c14b37d12ae955a,10645544,56564914914159,5466,0x6034dc032d426cc17560,11878461,4178,22568408416,46220169422074,49831237116273,4149,10645565,4144,4169,
40084504236921,51613001814606,4169,4175,0x168f072063540bd,24329597784,4868,0xad75ad0363cae655b,9871432,4157,9564213,0x66c2f883ab9ce90b44ef,0xc1e9b28a05a1d23c2,11403470,98242777365844277,
4168,4174,4186,4175,21521868125,13881885,22578815517,56525422059561,4129,0xd3e1faa266d11f49d,4186,0x19b46723e91f1ca,20637152503,0x18ec5548fcda55a,4152,
10661968,4160,0xc6d8f45a96b11c2f5,4780,18565166432,82175135355060981,4169,4165,9552556,4587,48078813000535,11862895,4169,51305382015638,4975,
11916539,4174,10661961,4142,4178,12243013,4130,10285120,4157,4757,47970519610218,10661966,0x19b2a5e6d0b43c2,10305633,0x283e04233456134ec9de234,
4170,4175,4172,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part41 : Refutes moves 0xc000008000000000000000000 0x721eb400140018180000100000 :=
  finish #[
56444705616445,0xc07698bfdd13bf10b,4169,8720593,4177,40535207715381,72630029455283546,4161,23547142843,4174,10671450,56438019932725,4161,37685876048643,0x2029aea822dcd0a0ab55495,
4182,4591,11919809,4146,4137,12620734,19798614668,56512477368385,4168,4169,23605883968,8716496,94682574325523806,4169,4177,
4184,4189,4192,9483094,22591214367,41387740844684,4192,4176,0x19ab1d59ecd94f4,4484,0x8733773748196e2bb,4157,0x5dfd3e75aed11d29755a,4190,4169,
22683116085,4599,0xcd99ba5d8278515be,4182,4189,4184,53127236161986,8708958,4305,9949674,4192,4168,4184,8720593,0xcdf67d1f94ba3949f,
41409048736725,4157,8708881,18466460335,8729079,4190,9953489,4176,4189,4184,4192,8712402,56510213214781,26787086839,54963033125752,
4190,38125161108241,9953487,4189,4176,4184,11423840,4132,4169,4156,4177,4172] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part43 : Refutes moves 0x4000048000000000000000000 0x281bb201240412080024900000 :=
  finish #[
51478865973456,8720593,8999979,11919570,4191,4152,4155,28429320501,97745285044326610,74928901447795872,4155,27615626203,24111490205,87751204502995715,4164,
4155,0x1674241a61660b6,4149,4157,4153,9126766,4495,36580599870232,4176,4186,4583,23373406695,11509850,4153,4172,
4169,0xc1c4169eda0b555be,0x181b3760e21c28c,0x16ab361ad35c5be,4186,10346557,94166526262543203,4160,4991,48264544322022,35398500032749,21836603601,4157,10318409,4170,
4175,4190,4304,23605866979,11494247,4133,4149,94702471762927852,22452196698,23538774075,4190,0xd3d5caea1de0b436b,20319166717,48003693015647,4198,
4190,48346560962705,9949690,4172,4176,4196,4193,4189,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part45 : Refutes moves 0x4000008800000000000000000 0x281a31c20c4010180800111100 :=
  finish #[
4691,10318124,4172,0x19b28addabb6114,12317751,5086,20176531748,4172,4170,4165,13104477,10277164,19344449610,4186,4179,
8708405,49466374218582,26735576128,87692140406850805,9495212,8708166,4177,4178,4172,11133423,11133528,9023758,10256440,4160,9953786,
20385846047,4160,4184,4405,4591,23372591413,4160,20343939477,4184,4172,0x18fd1fe06a0b304,37031352918668,4145,53073298682918,0xb4f8e91fc27853433,
4179,4183,21135987646,97572560488256140,4132,26030588696,4183,0x46c02600c01d6d1c836e,27590156425,48009231066170,10674252,4151,4145,9506953,19563782552,
4189,4184,4196,0xbbc5d51cce42391dc,86822906891571536,4874,21956874793,4128,44961152431138,4182,4178,53004670670270,21954531835,4189,4196,
4184,0x1a7ace1ae04e258,4691,9937402,4184,21913399389,4157,4168,4186,4198,4192,4193] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part47 : Refutes moves 0x4000008010000000000000000 0x2a1a72428400b0080040300200 :=
  finish #[
0x168d04576afa08b,52887602849113,23281509534,4153,0x19b11f8b310336e,4155,9125944,11531128,12657127,84671696772953024,22710706255,4172,8716495,4178,4186,
53079060788089,0x59d40da7aed60897655e,4189,9552083,8708984,0xade8288b82797a55b,4189,5365,9937284,4176,52885873226231,21955321950,4168,4175,4186,
13476909,98185739177919833,8712260,56507660714372,0xd3d9b48b9d93b9500,51563206206811,4153,4145,0xbb97514f85a17e1f7,4184,4196,0x1839368e7853234,48335798363181,0x1822b94e791c2f8,9953370,
4196,52953979151707,26837115679,24337310474,48192739467476,0x53e17e5ca7788e11437e,4198,4189,4184,4196,44860566245685,4157,4175,4190,4172,
4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part49 : Refutes moves 0x4000008000200000000000000 0x283a3440850011088000110084 :=
  finish #[
11785357,26008613428,4169,0x2b566d26c37cb9c0f27e49d,11088170,4176,4172,11859000,5255,25136165840,11456586,9125964,11088271,22744584381,4164,
11456821,24993587967,4157,4130,8720593,4182,4186,4177,17474208493,0xaff474850e69d23c3,4190,9126874,44755073078336,4132,10306508,
11104565,4186,11469665,56529599571390,11001912,38762460378356,4150,4686,24329708392,4179,10346569,4170,4190,4172,11023290,
36192056259524,25067795405,40635789186093,12316708,4169,4168,58229623833438,4175,12665282,11023326,4149,8712501,4175,8713058,11912431,
11440336,11912063,4157,44960968209250,4156,4164,4962,0xc736b8ba4bd0b4495,9949263,4196,4193,4168,4176,12194973,11502433,
4175,83214140162577554,4152,9921502,4165,8725748,0xc74044ba4153ad437,44552796951423,4156,8729171,4182,44651177439646,4196,4193,4186,
4984,0x20a5ae9028fe895748ab440,4176,4510,0x50829e0a6bc48e975189,4176,4193,8549409,0x2a146ba0d428e80aeae11c5,4152,4800,12317751,4179,4169,22475416630,
0x5df2ee5fc88541a2d42b,4156,4150,23363838462,41612840399528,4198,4196,0x66d411a7a87d6e9cf560,48055231784082,4183,8724991,4388,47847371690668,4196,4168,
4176,49602941940461,21106868533,4193,4693,8724689,4183,4186,9519520,41736085353132,21149638736,4170,4175,4182,4177,
4172,4190,4184,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part50 : Refutes moves 0x4000008000000000000000000 0x281a3040850210080000100000 :=
  finish #[
0xc1c5053741e2f8225,49691987013899,4178,49690549371867,4306,8717059,4176,4178,4177,4495,24168686457,42848861790975,4145,23441667115,25219634219,
9494921,4178,4175,4157,4177,23572316469,48195927925521,4165,4176,4172,22520107757,11527031,19352842309,0xcda38035e04cd90f2,0x18146a26cc146749b05a22d0e8,
47781889393028,91673019382063677,4145,4164,4156,13472053,42813747012435,4145,0x177eb557ea3942d,9887804,4169,28434093310,13473022,18692076703,13881380,
11022518,11829557,4175,4157,4156,23308636932,0x19b2b697ea3f489,9920591,4169,24974435677,20351501461,23609066846,10744315,4169,4157,
9949263,4176,4184,4193,8729256,0x19b2ba429975306,4172,4509,56511008195730,0x93d50647cbe97e55a,4176,4172,4177,10207999,0x204e3f9c84291f94817555a,
4176,10257754,4405,10670852,21853500164,4189,4184,4198,56577774678902,10720004,4150,44965844460587,4145,18691318635,19563766646,
4184,4189,4169,4177,4991,36221539795823,4159,0x54299e4d80426d11d55a,10724224,51666863903789,11133430,4176,4172,4169,4193,
5566,0x17645d69e91d107,4184,5059,11076086,4176,10276937,4145,0x852746ed08e1d25be,56515841991828,9552766,41733872017510,4172,4177,4182,
4175,4190,11124832] (by decide +kernel)

private theorem part48 : Refutes moves 0x4000008000000000000000000 0x281a3040850010080000100000 :=
  branch 1 0x4000008000000000000000000 0x281a3040850010080000100000 57 0x283a3440850011088000110084 (by decide +kernel) part49 part50

private theorem part46 : Refutes moves 0x4000008000000000000000000 0x281a3040840010080000100000 :=
  branch 1 0x4000008000000000000000000 0x281a3040840010080000100000 64 0x2a1a72428400b0080040300200 (by decide +kernel) part47 part48

private theorem part44 : Refutes moves 0x4000008000000000000000000 0x281a3040040010080000100000 :=
  branch 1 0x4000008000000000000000000 0x281a3040040010080000100000 71 0x281a31c20c4010180800111100 (by decide +kernel) part45 part46

private theorem part42 : Refutes moves 0x4000008000000000000000000 0x281a3000040010080000100000 :=
  branch 1 0x4000008000000000000000000 0x281a3000040010080000100000 78 0x281bb201240412080024900000 (by decide +kernel) part43 part44

private theorem part40 : Refutes moves 0x4000008000000000000000000 0x201a3000040010080000100000 :=
  branch 1 0x4000008000000000000000000 0x201a3000040010080000100000 99 0x721eb400140018180000100000 (by decide +kernel) part41 part42

private theorem part38 : Refutes moves 0x4000008000000000000000000 0x200a3000040010080000100000 :=
  branch 1 0x4000008000000000000000000 0x200a3000040010080000100000 92 0x29ca7820840450082000100000 (by decide +kernel) part39 part40

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part53 : Refutes moves 0x14000200000000000000000000 0x69ee6019014280004000000000 :=
  finish #[
5279,22651130941,4155,37784156168384,10649990,4157,4163,46340293895025,0x1834bba3828c31f,4165,0x570cd953d078b2234369,4163,4789,4968,47957858796699,
11497545,4142,4968,0xae78348b57ba3924e,4169,4162,4150,4174,17868076000,26771059773,12689658,0x4674de41737e6ca934fd,4179,5469,0x177288a6e29e10b,
9457733,4163,4169,8724780,4308,4308,11924351,27643073087,24193445942,4170,53189573583148,4169,4175,4193,4180,
4308,25177293574,18054955761,21760320560,4162,4169,11530725,4150,9090188,38129228817567,4163,21913657803,20170089215,51389814924443,4169,
8728642,4179,4307,5262,0xa158e8bbc792f8167,4159,4162,8729343,11432622,0x169b0454d23312c,4169,4162,4193,0xb45207365af852379,0x18351d1168532fc,
10276961,4145,4150,4180,11124815,4167,4174,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part55 : Refutes moves 0x14000080000000000000000000 0x69bb320c401428000100000000 :=
  finish #[
4308,48265351197851,11493839,4141,4157,4861,0x1834d397090a560,4168,25992217946,5071,25989804244,4182,4190,4861,83654578176000973,
4289,4579,17878381500,12271664,4190,9478205,4168,11124805,4167,4174,22645155263,4893,0x18f30694e41c18b,9073035,4176,
4162,4174,0x180d1f17328b358,0xc1c6aab98e7c7e436,4152,0xa8b2bb1d451c1a438,4160,18614658205,4186,4190,12276781,56527041090519,0x3365ab27482906a6d3451b7,22784127733,4174,
4160,0x181b365a285312c,4186,4190,26798298071,0xc7a214b58de053119,4183,4893,24985584684,4162,11362699,11494247,4176,19414279111,11460801,
9805888,4161,11137093,4164,4157,5465,0x33653a41f8353694e053108,4183,25069048971,25949816154,0x1812cf60a8950d4,4164,18433659092,4138,4150,
4158,48259532690589,0xc6e9b26f20d0532a8,11108439,11051069,4142,4163,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part57 : Refutes moves 0x14000800000000000000000000 0x69fb22cc142800100000000000 :=
  finish #[
36361273279335,17754527167,48212872888803,4149,4163,0x18ef1c145953367,22786601242,4167,20715750272,21710787744,23614211325,4167,22702297161,4163,4150,
4889,10744783,4169,4889,9839296,4169,4165,9839296,0x5a6af65cca491d29f29d,4178,4150,4968,52954516350293,46494306345003,44863578857849,
46718225011171,24197010201,0x180cec9ab22e3c5,4145,0x95636aa7d7323a319,4168,4186,4163,0x2b7e3a47f6ae4160d1d7362,10326080,4172,4182,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part58 : Refutes moves 0x14000000000000000000000000 0x69aa2a88000000000000000000 :=
  finish #[
4683,9044555,11124813,4889,25202098659,0x168cea17335e1e3,4137,25990644100,0x47fcde444a6081962437,4169,4167,4161,36375246795140,4150,4184,
5466,5266,53231969968600,4157,4164,11080864,51615511209011,11124801,4167,48349756158941,0xb53810a70aea9143d,4156,21961671349,4169,4168,
4882,17777792157,46359259661555,11428640,4141,39672104326007,8679488,17777795765,4186,4157,4169,51443759613081,11850514,91705310304768957,4145,
18616657242,4168,4186,91669677651882744,4160,4789,36422668317365,21174804557,4167,4182,4190,4180,26030134320,39072629228293,22786601236,
4142,4150,4869,0xcd65f0a714c8aa369,4173,4163,43316054500193,22786097811,4876,22785368356,4165,4170,11125703,20170138667,9084989,
0x1756bb85504b114,4172,8724557,4178,4180,10265061,52952284651915,4180,4869,11375965,41188958794890,10305595,56424808432389,4174,4876,
18116100893,18549171244,4172,4876,23350198720,4166,5361,56423080310008,11112488,4156,25159385888,4167,10297405,4165,8728650,
4180,9117784,4193,4183] (by decide +kernel)

private theorem part56 : Refutes moves 0x14000000000000000000000000 0x69aa2288000000000000000000 :=
  branch 1 0x14000000000000000000000000 0x69aa2288000000000000000000 83 0x69fb22cc142800100000000000 (by decide +kernel) part57 part58

private theorem part54 : Refutes moves 0x14000000000000000000000000 0x69aa2208000000000000000000 :=
  branch 1 0x14000000000000000000000000 0x69aa2208000000000000000000 79 0x69bb320c401428000100000000 (by decide +kernel) part55 part56

private theorem part52 : Refutes moves 0x14000000000000000000000000 0x69aa2008000000000000000000 :=
  branch 1 0x14000000000000000000000000 0x69aa2008000000000000000000 81 0x69ee6019014280004000000000 (by decide +kernel) part53 part54

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part61 : Refutes moves 0x4800000010000000000000000 0x3012eb8a000082000240240000 :=
  finish #[
13472427,5259,0x30223e26c234ebd1129e3bf,4162,4172,91282737060741458,28447966367,54967164326040,9794709,13889574,0x5d0c7f9b34f422b4a48a,4168,4150,0x18113763829e48b,0x1a7b1cd4f1ca4f1,
0xc1d4494f66c91a0c4,4184,4192,4190,4172,17759372052,44909588832454,4153,4161,4173,9089776,10707696,8716357,8717658,48327646159529,
8708602,0x8e25d4a4d1429e10b,4165,4162,4172,4193,9069151,0x19b28b88817a31f,4189,9060561,0xbbf2cc1405217a4fd,4193,4845,90480259392967129,12702353,
4168,47726872880477,9797799,56562258100981,8945700,4131,4137,4143,20353033063,8712261,22683484917,45974742311561,17792544825,4172,4174,
4178,4173,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part63 : Refutes moves 0x6800000000000000000000000 0x7933fd08010000000000000000 :=
  finish #[
72906126040813719,13473013,10277841,11124805,4174,37761840469440,36181334873440,4175,10638194,4136,10637699,27592020765,19347628829,24421127119,4165,
4154,4145,4846,35891744932590,4156,0x19be40a3a2253c6,20177339738,4153,9089082,4164,4174,4172,4845,10658387,23539123166,
4173,4165,4798,88878528921383492,4174,4172,42933872685525,0x174b1f5afa3036f,10735673,17818104560,4174,8716496,4187,4186,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part65 : Refutes moves 0x4800000000020000000000000 0x3212690c114000104000000900 :=
  finish #[
56511808271498,13484482,22784958524,13472415,84953199456821545,4162,12194563,10658563,4147,9904318,4161,0xc122dc82e6ca9c08a,4174,4146,56613258519325,
44172552552633,4893,95265419305624229,4161,4167,0x83f9b2a4cb929749e,4148,10736397,9470648,4175,4178,4184,4172,4190,17382174871,
0xa6c8ee0f4d81cd372,4175,8716795,4177,4776,0xaf12b07341b23a19e,4175,8712489,24975516811,47733474324665,10215587,4130,8716327,91566030669021757,25216484405,
12711168,45838050751521,17851646003,4165,4175,4167,13472831,21829067259,4165,9552467,4186,4192,4190,4177,21572194872,
9888396,4165,9811188,21572194512,25921126907,9552467,4198,4190,4192,11124826,4146,4174,41154463244578,77730028374029658,4192,
8687817,4173,4305,0x177c1411e0a331d,0x30317535f5122a42704b31d,4175,4174,0x177ca5d4e2390c4,9089723,10318576,9482730,8683590,4177,4178,9953488,
0xd3f7468a17e85036b,4607,56509388358143,4178,4195,9916510,4189,4192,4184,4172,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part67 : Refutes moves 0x4800000000000000080000000 0x32126908218020410000410000 :=
  finish #[
44982461501635,4870,44312295560542,4156,0x18e4a4cb4a9e560,8708169,4178,4303,20208477325,21963305550,4155,4192,10670854,20210901780,4169,
10346700,11124817,4167,4195,18400899257,0xc1f744ead4d101556,4168,11124922,56436382618784,4168,11124934,9077029,4161,4173,4167,
27615528075,22384334173,4183,17616711954,4148,11125323,0x16b30254f1ca48c,8664026,0x16a8d645429c2f0,4153,4163,4161,4167,4893,10318419,
4190,4691,98602812562044253,4172,0x4d83ac7568e51f910376,4186,4168,4180,4192,4305,18589483495,0x176a8d825a3d0bc,4172,4195,11125235,
4991,48344681882973,4161,9470630,10736009,4177,4178,4190,17645134892,73925017820193358,4173,17627570459,12210961,48212219773725,4145,
4195,0x516a0823aa7174af92f8,9916464,4172,8716971,48327644648113,4172,8716496,23565160657,9936968,4173,4177,4180,4192,4184,
4189] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part69 : Refutes moves 0x4800000000000040000000000 0x32126918410228000288000000 :=
  finish #[
4305,4300,4891,9076933,11124813,0x4b32858188dd4e23c495,4184,4189,4195,19399545617,10264981,10265373,21779174171,4184,13471831,
22652380608,0x60f8ff8133654e1170f1,9887826,4173,4177,11444420,0xa74226ba8509de423,11124830,0x1818a5d1fa9c2af,10346791,4177,21962076934,8696204,4177,4178,
9953488,8716799,4607,56506974454271,4178,4195,4190,0x19b26897f2854fd,21788714336,4198,13472541,20068295453,82096655372141527,11047014,4183,
20377456713,4168,4189,4184,4180,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part70 : Refutes moves 0x4800000000000000000000000 0x32126908010020040080000000 :=
  finish #[
22450602633,18530735046,4170,51394496496265,17701892298,9515082,4192,4798,26726773824,8696106,4175,4174,38131695477510,18547508257,8708696,
4186,4177,4986,12210590,49575175635630,4145,4195,4504,48262617358750,4183,20377456713,4189,4192,4184,9855178,
4305,11891483,8700113,4175,4172,4184,26727584344,0x4029b439aa7a6c84e085,4183,0x54bbaf8e4eca6c96e48b,13472255,0xbab5ec5d57f4d92bb,4606,9937395,4169,
4177,4165,4184,4189,4192,11526915,5470,0xc6e47ea7a6ca890b6,4169,56506738757823,4164,4172,48190925890328,4305,12710097,
17693119627,13471816,9949392,9953779,4169,4173,4192,4189,4177,23473955097,82087722685518414,4172,10736305,0x18ec0a11223d3dd,4305,
0x19b2d5ce19dc3bd,4192,9855060,4169,4177,86781088412836342,4867,46699494872414,44626532061852,11046996,4172,4169,5259,83542427717964753,0x87053c3b66c83d55d,
4159,4162,4888,12271891,36235081884811,4156,4157,51169619935701,4184,18442085722,44658433574231,4186,0x175ea68e1979489,13472250,0x17407666c9dc1fa,
4175,4187,4172,4192,4180,21173166590,21663310901,8717367,4186,17810580440,4172,10346700,0x1814100bf048440,92221059747996337,4157,
4189,4165,4169,4173,11124817,4174,4195,4167,12689465] (by decide +kernel)

private theorem part68 : Refutes moves 0x4800000000000000000000000 0x32126908010020000080000000 :=
  branch 1 0x4800000000000000000000000 0x32126908010020000080000000 42 0x32126918410228000288000000 (by decide +kernel) part69 part70

private theorem part66 : Refutes moves 0x4800000000000000000000000 0x32126908010020000000000000 :=
  branch 1 0x4800000000000000000000000 0x32126908010020000000000000 31 0x32126908218020410000410000 (by decide +kernel) part67 part68

private theorem part64 : Refutes moves 0x4800000000000000000000000 0x32126908010000000000000000 :=
  branch 1 0x4800000000000000000000000 0x32126908010000000000000000 53 0x3212690c114000104000000900 (by decide +kernel) part65 part66

private theorem part62 : Refutes moves 0x4800000000000000000000000 0x30126908010000000000000000 :=
  branch 1 0x4800000000000000000000000 0x30126908010000000000000000 97 0x7933fd08010000000000000000 (by decide +kernel) part63 part64

private theorem part60 : Refutes moves 0x4800000000000000000000000 0x30126908000000000000000000 :=
  branch 1 0x4800000000000000000000000 0x30126908000000000000000000 64 0x3012eb8a000082000240240000 (by decide +kernel) part61 part62

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part73 : Refutes moves 0x6040000000000000000000000 0x79c3ee8b020000000000000000 :=
  finish #[
0x301e6f4dc75822608c184f1,11916013,11879367,12636716,11137064,56513291424516,4135,4149,4170,4893,9085677,53005110841643,0x19b2b9e0eb43320,93879912728188039,4155,
4152,4164,4173,98212644806640416,10658579,22809305381,4173,4165,4159,4167,47970902951258,21645246949,22584882137,4170,4164,
0xbbc47abc0e5284319,10711921,8671934,9085008,4173,4165,9851480,46477152429117,43401955066941,4187,4167,0x13bced9d5a365eebe11e8a6555,24346063815,11108645,23567135704,
9061145,4159,4153,4157,0xa9868abf91b8aa2b1,8695899,4176,4173,4180,4172] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part75 : Refutes moves 0x4240000000000000000000000 0x7bc3b68e920000000000000000 :=
  finish #[
9450653,26007729082,4174,49363998359714,95191767537402823,4188,4143,51359464944986,9061522,11083845,4157,4883,0xad82069d05203f23d,77804123436880658,4174,
4173,9507616,4703,21147988370,4174,0xc1a5da7654e1dc369,4160,4182,4187,4172] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part77 : Refutes moves 0x4040020000000000000000000 0x7bf2660a130110808004000000 :=
  finish #[
18501182712,0x88d834284e19d255e,4180,10969683,0x1742878e94122f7,4168,22467806049,4151,4855,0x1764bbdd2af855b,4166,48282448019643,4153,21023769061,4187,
4172,4167,53313786471677,97647431959999336,0x54e2749bca45aa35d4a0,4151,4156,21829797005,0xaf80d53520d22a83a70d492993c3,4170,4157,11026837,0x66caf58faa720d29216f,22645154670,49759186973458,
9519171,4187,21712356122,0x18348f148a840ab,10687355,4154,48052231447301,23465661202,9519178,4187,9932870,4176,4180,4172,4184] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part78 : Refutes moves 0x4040000000000000000000000 0x3ae2262a020000000000000000 :=
  finish #[
4484,5267,11883460,4170,4146,0xcd9538b694229f55d,4192,11883861,53094623613725,11857984,35502438433826,9450653,4149,0x31ddd0c0d6aa40e0e34f5be,4146,
95573251390510426,22761042896,4157,4192,9109606,4187,11408830,4757,42527260517725,19354394644,9109575,8442412,49848431908286,4148,83085113600501182,
4137,12690098,46374096814144,4198,39640983782358,24264537030,24121557247,11857953,4137,44830980822262,4148,9126092,4175,0x44cc06758b960e2f5284,0x18db06945a9f36e,
4157,0x9ca81a7657a91449d,9953359,4192,4180,4172,52890886513108,40550776915079,4155,90190424639083680,53074716177854,10138658,44035589722869,4132,4148,
12636205,4136,12698969,11808958,5262,36241136432173,4149,4155,4170,98433768377025497,12285070,51135959655487,23465283643,4154,4172,
4160,11858717,0x5a63b7838ed14e16623d,10657853,97649591772931039,46663530959831,10706996,4172,4153,4389,11125425,8696101,4176,9125964,4175,
10658050,27635602091,56496236962578,27635602091,4138,4129,4174,13476597,27601950142,4198,24421557593,10711097,4172,4890,0xc0d532cf9154da1ba,
4152,56525656264978,0x5df40675a0f5aa0a349e,4168,4160,4959,42666361607015,4168,21066544473,4198,99023401990812910,53229663155243,4170,9871424,4149,
4157,9110101,4175,23422952390,23424103482,4142,12689602,0xc1a75e284df1d7380,4180,4160,45977117500256,0xa749b89b0e1c7555e,44173230466006,4146,36439878991928,
9887827,9921011,4184,4188,4192,4165] (by decide +kernel)

private theorem part76 : Refutes moves 0x4040000000000000000000000 0x3ae2260a020000000000000000 :=
  branch 1 0x4040000000000000000000000 0x3ae2260a020000000000000000 77 0x7bf2660a130110808004000000 (by decide +kernel) part77 part78

private theorem part74 : Refutes moves 0x4040000000000000000000000 0x3ac2260a020000000000000000 :=
  branch 1 0x4040000000000000000000000 0x3ac2260a020000000000000000 93 0x7bc3b68e920000000000000000 (by decide +kernel) part75 part76

private theorem part72 : Refutes moves 0x4040000000000000000000000 0x38c2260a020000000000000000 :=
  branch 1 0x4040000000000000000000000 0x38c2260a020000000000000000 97 0x79c3ee8b020000000000000000 (by decide +kernel) part73 part74

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part81 : Refutes moves 0x4000100010000000000000000 0x3186220b8040a1000840280008 :=
  finish #[
10347392,9069151,4173,58263046391130,21024170777,4147,58225483440498,58225481417074,4147,78061997375431552,4179,0x51b35f7654f82910d357,4162,4180,4189,
5470,23415301462,11108406,4581,58244387726384,4173,0x60ea98222a491a23a287,4174,4187,0xa6c9bb3651b1ca0f7,0x53f1ca77e469d128b498,4198,51665328747263,4971,46475557794880,
4162,8729183,4183,4187,4180,4561,11477594,9109588,9532172,19799863704,4163,8730046,10695612,4162,9532259,
19523793862,4162,0x43853e4674f45a11c489,4183,4195,4180,4198,10266048,49550628611136,4180,13471891,56573469311437,4175,9093475,9454267,
4174,4180,5568,84590932536698206,4175,0x19b42d08f910163,4180,4195,4183,21191156587,4497,49879578653539,4190,19513434510,20317929888,
4179,4187,4183,46250549781640,54909145130430,20284391825,4175,9871447,4157,4161,4165,4173,4189,4193] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part83 : Refutes moves 0xc000100000000000000000000 0x72bea00a816060000800000000 :=
  finish #[
18476015799,11363483,72914500361466549,17878479540,4162,4174,4192,17618691107,80547755099108387,4174,8729465,4182,9483128,4163,4166,
0x8848340f4288533d7,12689618,51303817270126,8729454,4182,0x81c47ed341ac1a234,36102005453691,4145,12690069,13497389,9482452,22635212894,4170,4178,4163,
4192,9315104,46369147110746,12689491,0xc070800ecb30ac36e,41336209612994,4192,4161,4165,4173,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part85 : Refutes moves 0x4100100000000000000000000 0x38866828914820800800000000 :=
  finish #[
10736293,24403157676,10338965,4180,4175,4985,77497413623932040,4169,20167320727,9810319,87757748417065832,4183,4150,4142,4701,
18467595400,25094611744,40845384213565,4187,4175,0xa1480ea108b96a250,4161,41341000336056,9515406,4192,22641968081,44926784717407,4175,4187,4183,
4189,4177,0x18389f14c11c172,28446884695,4165,4977,17658692480,4169,4401,0x16954f90a1dc488,0x16b5364ea0b425d,4189,4190,9847265,4151,
4187,4175,10236704,17718223335,4169,22694622365,11137817,4157,51611147559977,4698,0x16a28f4580b411a,4189,4183,4175,9351259,
4510,5256,26793472554,4162,4163,17669489054,4135,11825568,4509,25830007577,4165,4157,11465108,4883,9871653,
4169,4157,10346785,4795,9126193,4189,4183,4187,4175,19203702865,12689431,4138,4127,4193] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part87 : Refutes moves 0x4000140000000000000000000 0x3897a498a14422000aa0000000 :=
  finish #[
4656,44673292936038,53190184289435,4161,4169,4676,42933022606491,4169,88893765050991855,4187,4190,25988645939,0xbb2a7c2d20d172429,4169,10277075,
19968816287,74116264929621056,12689474,23265912256,25989366527,11886651,25955459557,9556041,4187,4193,12690201,10338514,4187,12690392,17860428955,
0x49c4d5834ed0b911a15b,4192,21888225371,4166,4177,4190,4189] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part89 : Refutes moves 0x4000100000200000000000000 0x789e2448854021000c00011080 :=
  finish #[
4984,4703,22752252565,9490643,4180,4189,4177,5275,72621644421636863,75964160657314971,4159,4165,0x19bc1011bc1a2ff,13890624,11002408,
8549440,4136,10686505,4142,4148,17717072750,4180,20168828254,28431963483,24289333823,23558254615,4150,51337099272382,4169,0x25903787367e438288b449e,
4177,4175,25990575048,97619492609847998,4163,9544082,4175,27627988029,11772565,4143,11138398,4164,56578940265234,21863067943,4168,
4169,27559191118,10671446,4138,0x177d375491d942b,4177,43315274781451,4169,4190,21805920928,10285849,9531453,49604435485458,0x9a18344414c28b150,4157,
0x15baa7e6ac18691068880b4222,4175,4863,11433302,12690094,10276906,4150,51341496410303,0x2efdd43457794f97c2330bf,4150,9527369,9564574,4184,4190,4183,
4189,4180,4192,4193] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part90 : Refutes moves 0x4000100000000000000000000 0x38962048814220000800000000 :=
  finish #[
36081595547859,4797,10338899,4180,4177,4581,4863,36306416977242,9543747,4192,27592479416,4896,9126674,4189,4198,
27590788149,9126578,11510069,4180,4987,47781874999864,45014395323259,4187,4183,18523546087,4157,4165,4189,4169,4177,
72344731638030750,94510071141875906,4163,4798,4896,9126674,4189,4198,9126578,19565355317,4180,48148404372256,23440892097,20034339894,45014395323259,
4187,4183,18523545793,4157,4189,4165,4169,10567761,4125,4863,49516251304808,4187,56578664264634,4159,11109722,
11052169,51305415558177,4180,4190,22811681746,18558322010,38044268610603,4187,4190,10584641,26770268641,5163,51132099322540,4172,4180,
4190,47869441684048,36610496389913,0x1676bc93f1ca423,21779173588,4184,4172,4159,18489991655,4173,4169,4189,4165,4177,4287,
51218477970175,27626300365,0x1698bfd3b41e2ff,4156,4145,11851102,22006845723,9543753,4187,4192,46721703937366,54934420833043,10346912,4180,4190,
22701916856,4798,25010327932,21989237502,4184,17878074227,4187,4192,4180,17717462162,98036807233921329,4192,18523546087,4157,4173,
4169,12689489,4138,4182,11124833] (by decide +kernel)

private theorem part88 : Refutes moves 0x4000100000000000000000000 0x38962048814020000800000000 :=
  branch 1 0x4000100000000000000000000 0x38962048814020000800000000 57 0x789e2448854021000c00011080 (by decide +kernel) part89 part90

private theorem part86 : Refutes moves 0x4000100000000000000000000 0x38962008814020000800000000 :=
  branch 1 0x4000100000000000000000000 0x38962008814020000800000000 78 0x3897a498a14422000aa0000000 (by decide +kernel) part87 part88

private theorem part84 : Refutes moves 0x4000100000000000000000000 0x38862008814020000800000000 :=
  branch 1 0x4000100000000000000000000 0x38862008814020000800000000 92 0x38866828914820800800000000 (by decide +kernel) part85 part86

private theorem part82 : Refutes moves 0x4000100000000000000000000 0x30862008814020000800000000 :=
  branch 1 0x4000100000000000000000000 0x30862008814020000800000000 99 0x72bea00a816060000800000000 (by decide +kernel) part83 part84

private theorem part80 : Refutes moves 0x4000100000000000000000000 0x30862008804020000800000000 :=
  branch 1 0x4000100000000000000000000 0x30862008804020000800000000 64 0x3186220b8040a1000840280008 (by decide +kernel) part81 part82

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part93 : Refutes moves 0x6000000400000000000000000 0x7987f3880028000c0300000020 :=
  finish #[
4693,98177338213384667,23501992729,4142,11891086,10682434,21880238951,0xa9953870d459d21e6,4160,4150,0x1a7ed194c3af125,11891377,8699961,0x9be454d18522991d5,22808936741,
11055182,4150,18606248541,8712399,4188,4187,4179,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part95 : Refutes moves 0x5000000400000000000000000 0x32c6b988002200140280000020 :=
  finish #[
4570,0xa9037d1d14e29a4f3,4165,22787699864,11031502,20068287934,4167,93877839027467214,4152,4158,36136423105077,4845,4671,9364423,4137,
87412538851574148,4174,4146,4167,0x31d20602f36ed553da89291,4148,12689481,4182,4650,12280673,20924179511,26024198209,12689479,13890419,23507174173,
4165,23440065297,87761308953335232,4156,4148,41341090578633,4173,4172,11522226,22784139749,4167,12243519,94653600034309568,28432126751,4172,
9069621,4167,4169,87199526376539392,20135404577,8704059,4174,4182,26839457921,11125813,11018311,47786026976224,46669335458577,4169,4172,
10634395,53228765070369,53228765926433,4156,8720436,4184,0xaea534bd4560510b8,0x183ce8dda41a09a144570b41c3,4195,4173,4189,4187,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part97 : Refutes moves 0x4200000400000000000000000 0x738f318c002008840210000020 :=
  finish #[
4681,0x419800a7e5a4de29c24e,11030606,42369950151513,11059677,4179,47694978589133,0x33760d4df1cb4f4a50f4235,4161,4149,0xba8a7a5914f1cd49b,4195,97964205839327797,25990636287,4179,
0xa7d83aa711a23a3d9,4163,4174,4169,22004720483,5183,22006739636,22006850228,0x19ba8517a8a63df,4165,4155,4179,12284696,0x177c55a392fd438,11411524,
10326065,4182,13882619,56525496419566,4163,53231258551646,25993401001,56523163583549,4167,4163,4329,22802195032,4172,4190,4195,
22003634862,4174,44678080230846,22750966231,4161,21192340447,4190,4789,39639530181790,4167,8708297,4183,4174,53228706034731,18392130229,
56592613720343,11133803,4183,25220457033,4160,11112542,11055171,4150,4164,4178,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part98 : Refutes moves 0x4000000400000000000000000 0x33a63188002000040200000020 :=
  finish #[
5261,4870,49383755534570,4162,11031796,11125915,12632135,4146,4893,20865995533,4156,11076283,4162,4169,4183,
20656993005,10969837,56578697454647,4179,4162,0x24fe6ea829b870d42a9c556,4146,0xbbc8354f5ab27748d,5566,22593257953,4146,4143,4893,46391253132428,4183,
4169,44877645402897,4150,4187,4145,4862,0xa829b8bba0d2fe423,10235981,11461374,13079294,23407355035,12628045,4156,4153,19570963022,
4187,0x19bf1fce42f649b,0x18fe7226ecdf6768b5770530f2,9916503,4172,4184,10318319,22785389109,11444824,4169,4145,22786581472,0xb5f8e875d1d1d44f4,4187,4162,
4484,25093071640,4172,94412355451413552,4153,9110099,88459664896680231,4172,4187,4855,9401117,9888132,4169,4173,10347091,
21005812399,4173,4187,18690945425,4168,4198,4183,4693,36508665594461,4183,4881,18299417133,4132,5168,12628822,
10682428,20345012281,19521835608,10347101,9564762,8728678,4183,4187,46494883562651,4304,0xcdf834b79491de0d4,4190,4187,0x853044a648fa98359,9949244,
38279921001221,4169,4173,4188,4184,4177] (by decide +kernel)

private theorem part96 : Refutes moves 0x4000000400000000000000000 0x33863188002000040200000020 :=
  branch 1 0x4000000400000000000000000 0x33863188002000040200000020 93 0x738f318c002008840210000020 (by decide +kernel) part97 part98

private theorem part94 : Refutes moves 0x4000000400000000000000000 0x32863188002000040200000020 :=
  branch 1 0x4000000400000000000000000 0x32863188002000040200000020 96 0x32c6b988002200140280000020 (by decide +kernel) part95 part96

private theorem part92 : Refutes moves 0x4000000400000000000000000 0x30863188002000040200000020 :=
  branch 1 0x4000000400000000000000000 0x30863188002000040200000020 97 0x7987f3880028000c0300000020 (by decide +kernel) part93 part94

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part101 : Refutes moves 0x4008000030000000000000000 0x738e635e4c81800a0740a01400 :=
  finish #[
27592008252,4688,9953786,4188,4180,36036622983928,5466,12305557,41155351523377,4127,58265586934435,11108924,4771,20940686099,9531460,
4195,4178,4184,4703,27582862489,4178,51560797472090,24137487510,4144,20343939480,4184,4189,56509884523148,56492696638912,21812715591,
4157,4180,4175] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part102 : Refutes moves 0x4000000030000000000000000 0x7086e30e448180000140a00000 :=
  finish #[
9733154,11133986,4172,36037436560231,4890,10266046,4172,4195,4192,9442079,91565697691620286,4178,8725455,9937488,11112954,
24277795403,9490523,4174,4195,4192,4180,0xd3d9b30526d415559,4552,22570439829,26814301333,4195,4147,0x183ea45a0d3d1ba,4867,52959610225806,
4143,22566782109,4135,10649651,4139,0x21c9d900c9b536544a9e15f,4172,4190,4395,41306514384222,4190,53315242530239,12710973,11371003,23287951771,
4178,4190,4195,17876828747,4179,4193,4189,58231430549678,4507,4507,26032575147,4163,4150,9125976,4293,
17753019552,4150,46593315873253,4179,17575593201,4683,4405,10265449,4147,21024571803,4178,4184,4192,9543877,81987461658042677,
11530323,4158,4190,4167,10744506,4494,26031416096,11080550,41683875500832,4168,0x183e8b88991c2f7,4187,4190,4193,4195,
98777228331835984,82968518825878462,48370033439608,4158,46219188343680,41305080308600,4168,44867050660432,4172,4192,19562971540,4189,4193,11117151,46374842590049,
4184,41155319670105,46494885999456,17826091104,4173,4178,4179,4180,4174,4175] (by decide +kernel)

private theorem part100 : Refutes moves 0x4000000030000000000000000 0x7086630e448180000140a00000 :=
  branch 1 0x4000000030000000000000000 0x7086630e448180000140a00000 87 0x738e635e4c81800a0740a01400 (by decide +kernel) part101 part102

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part104 : Refutes moves 0x6000000020000000000000000 0x7987e31c410140000300c00000 :=
  finish #[
4954,47718910129502,28447645774,4688,0x169ab65ab9de31d,4175,4180,0xd3f35aa285529909d,11113221,17842884907,4175,4180,4396,22641164890,4179,
22634762539,22584857163,4164,11055309,45029075366584,4168,47713304097358,4688,10338510,8724559,4179,4187,4180,4189,4190,
4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part107 : Refutes moves 0x4100000020020000000000000 0x3a86692cc14900124100824100 :=
  finish #[
27603604633,25973388634,53096218739544,94663974113637226,4177,4190,4174,4673,28442465416,11133706,10264628,4190,5467,11105627,13471838,
56510908265226,10646681,13472522,21806302554,4136,10285752,4177,9064542,4178,4174,4180,4172,10744098,4390,17785786945,
4187,4177,11117325,9847186,10277663,95009319021659482,4174,4180,4187,4301,4691,11498426,4174,4701,49623440085791,
4174,4172,17826529875,4189,4187,4177,4183,4175] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part108 : Refutes moves 0x4000000020020000000000000 0x3296612c414900120100800100 :=
  finish #[
0x1a7b370db851422,53000554259320,18657002047,4189,4175,9126461,54924723602581,4184,0xd3e7426f144a1355d,17859658026,4180,11133720,4165,4169,4172,
10203422,20899549470,4169,49985089733565,74608998263428245,4162,4180,0xa0b779074d2c774a0,56512502023614,0x19b31cc5a22231b,4139,18500407605,4156,4169,11899644,
95575483071788180,4172,0x5464d9350a713db5d3ba,4133,88184807532216870,4177,4167,46029602608474,10318419,4177,4180,4195,22803763860,56510211208149,4175,
4890,0xd3f8286eda5c15422,4133,38141553583550,11116940,4151,11472990,4144,58260405982456,10207922,4148,58259683713569,13472317,4870,22592398475,
4177,4190,4172,4890,46619423261245,23365357625,4136,4144,4962,9544552,4178,86879600478188172,11473690,4136,0x40522a82aa494c91a3c3,
9125982,4177,4175,4195,10297934,11124943,10298216,4165,4174,11911745,9868539,4156,0x18dae8e6c969306,0x19be70c889d71ea,4195,
4190,11125343,21911744914,18614616360,4177,4178,4174,4172,21803541274,0xaf18e88b60f8b423d,4175,4686,39705087124338,8728657,4190,
46664519246909,0x9cd53814cba97d488,4168,4172,4189,4180,4184,4192] (by decide +kernel)

private theorem part106 : Refutes moves 0x4000000020020000000000000 0x3286612c414900120100800100 :=
  branch 1 0x4000000020020000000000000 0x3286612c414900120100800100 92 0x3a86692cc14900124100824100 (by decide +kernel) part107 part108

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part110 : Refutes moves 0x4000000020000000080000000 0x3a86610c610121010100c00000 :=
  finish #[
97657910053261522,56529656734181,11903551,42855444464982,4187,4177,4175,4671,54907994694816,4187,40771571209356,19313312914,12611676,4168,4146,
0x4b229c29aa405a28c23f,37512505148555,4881,0xc1d9ad0554b8b0311,4177,4169,21787902516,41044127900422,4158,4301,19976021239,22591214365,4180,40905839265015,10711119,
4189,4177,4184,4178,4172,18501977226,9753760,11124788,26030588966,9704797,27626357898,4179,90477145822401502,4146,4148,
9753562,49981844923541,4177,4167,4183,26695135698,0xcda352a32372904fd,10276951,10318419,4177,4180,84274205183033924,10297934,4187,10224789,
0x19b44f66fc140b3,47785238431070,4164,4156,17820140592,4174,4396,4884,22709080654,4178,10338904,4177,4187,4190,4172,
4893,41683824362644,4183,4896,21736813707,4187,4603,54911511949892,4198,10297556,10735707,4183,4190,11055515,40082943202138,
4180,11506538,4173,4168,4189,4184,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part112 : Refutes moves 0x4000000020000040000000000 0x328f610c410128000380880000 :=
  finish #[
22565688456,8708401,42574671258760,41306009428856,4177,20923818781,8704771,9814097,4135,4167,4175,4877,72834554178110004,18600288548,4158,
45030679937920,4306,8708302,4175,4180,4177,4178,4172,4884,56509222568735,4163,46664435733557,51361039569577,21091709134,4164,
0x19beeb66c9690b3,0x56ec149b25554c1d743d,4195,28450092090,21134786953,11055198,0x54e41c45ca602404d258,4179,4174,4172,4178,4177,28449993379,22570439513,0x19b2890e50b45c0,
4177,4183,4969,49823836381983,4172,5155,11138083,22643957827,0x17583fd7cafe12d,4144,48349674250923,80020572912320821,9544088,4190,4172,
4195,4177,4178,13472639,10699618,9556672,4178,4175,4673,20938642107,10285128,95689352344867893,0xbb44302b0268b436a,4175,4183,
4177,36547094619274,23608291637,4157,48209120801451,4190,9953589,9953682,9564469,4183,4190,0x9cd53814cbe97537f,4168,4172,4188,
4180,4189,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part114 : Refutes moves 0x5000000020000000000100000 0x32c6e94c410d300407a0a00880 :=
  finish #[
53121099755654,42857843188280,38209229677632,4156,4168,36580341052576,5184,37288362263712,11124815,4195,4167,11436596,12317226,18122805401,42494667210962,
11124827,4195,4188,0x9be9b056e03a8231d,4162,4134,12665705,10215989,8708792,4184,4180,72879617023362208,9482450,21837869455,4195,
4184,0x183c1d8841b3369,5163,8687921,4178,4177,93943105988448829,9470630,11133007,4158,51136126612253,26017002034,37889658962719,4195,84450164085134577,
21886570703,4184,4180,11046994,4141,4162,4169,4172] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part115 : Refutes moves 0x4000000020000000000100000 0x3386610c4109200401a0800800 :=
  finish #[
52904694325724,37890463257738,0x54153d6baead4f3bf4f5,11530313,4183,26031636681,25848729901,42676978373306,4156,4162,4180,47821986939958,5181,0x542bbc9b3024168304a0,4144,
4146,42421681058057,51391232996003,11124799,10276935,4195,10277635,21049762357,4172,23490847805,11498271,4150,4174,0xc1435e5a66c84e556,21193540381,
4195,10174920,9814581,27590451247,73093975253959097,46224259069270,10318419,4187,4190,4195,88885610108461821,4156,4163,4177,10224688,
0x183e6ccbf29c4f5,4188,51613780361723,4183,0xc7c5040760597a55d,42542015652045,4172,0x18f88a91ea91244,4198,56562288468242,0x182aef26ca982a3,10317906,21022573601,36618087797331,21887054603,
4198,4178,4183,4187,4190,0x19bad70e52822fd,22526149562,26762326718,4177,4178,17518433053,19173053783,9544553,4175,0x28c541cd67573645a29f3ba,
4177,4178,23568683864,19395617567,4175,42797935359114,46359167079199,4136,51498480956765,0x181245da88b443d,4175,4195,4177,81351067814585119,4141,
4165,4173,54865734877550,13472302,24966394621,9109598,4177,21981205850,23565489193,0xba553ebe4e18a530c,23565558446,4187,4177,13472324,12313355,
23541571665,4141,4157,4165,0x1818a09492d92fe,0xad7538b648e053369,4187,46661223977265,0x17565e974afe55b,4165,4173,0x9cd53814cbe97537f,4172,4188,4180,
4168,4189,4184] (by decide +kernel)

private theorem part113 : Refutes moves 0x4000000020000000000000000 0x3286610c410120040180800000 :=
  branch 3098 0x4000000020000000000100000 0x3286610c4109200401a0800800 96 0x32c6e94c410d300407a0a00880 (by decide +kernel) part114 part115

private theorem part111 : Refutes moves 0x4000000020000000000000000 0x3286610c410120000180800000 :=
  branch 1 0x4000000020000000000000000 0x3286610c410120000180800000 42 0x328f610c410128000380880000 (by decide +kernel) part112 part113

private theorem part109 : Refutes moves 0x4000000020000000000000000 0x3286610c410120000100800000 :=
  branch 1 0x4000000020000000000000000 0x3286610c410120000100800000 31 0x3a86610c610121010100c00000 (by decide +kernel) part110 part111

private theorem part105 : Refutes moves 0x4000000020000000000000000 0x3286610c410100000100800000 :=
  branch 1 0x4000000020000000000000000 0x3286610c410100000100800000 53 0x3286612c414900120100800100 (by decide +kernel) part106 part109

private theorem part103 : Refutes moves 0x4000000020000000000000000 0x3086610c410100000100800000 :=
  branch 1 0x4000000020000000000000000 0x3086610c410100000100800000 97 0x7987e31c410140000300c00000 (by decide +kernel) part104 part105

private theorem part99 : Refutes moves 0x4000000000000000000000000 0x30862108400000000000000000 :=
  branch 2525 0x4000000020000000000000000 0x3086610c400100000100800000 64 0x7086630e448180000140a00000 (by decide +kernel) part100 part103

private theorem part91 : Refutes moves 0x4000000000000000000000000 0x30862108000000000000000000 :=
  branch 1 0x4000000000000000000000000 0x30862108000000000000000000 70 0x30863188002000040200000020 (by decide +kernel) part92 part99

private theorem part79 : Refutes moves 0x4000000000000000000000000 0x30862008000000000000000000 :=
  branch 1 0x4000000000000000000000000 0x30862008000000000000000000 80 0x30862008804020000800000000 (by decide +kernel) part80 part91

private theorem part71 : Refutes moves 0x4000000000000000000000000 0x30822008000000000000000000 :=
  branch 1 0x4000000000000000000000000 0x30822008000000000000000000 90 0x38c2260a020000000000000000 (by decide +kernel) part72 part79

private theorem part59 : Refutes moves 0x4000000000000000000000000 0x30022008000000000000000000 :=
  branch 1 0x4000000000000000000000000 0x30022008000000000000000000 95 0x30126908000000000000000000 (by decide +kernel) part60 part71

private theorem part51 : Refutes moves 0x4000000000000000000000000 0x20022008000000000000000000 :=
  branch 1 0x4000000000000000000000000 0x20022008000000000000000000 100 0x69aa2008000000000000000000 (by decide +kernel) part52 part59

private theorem part37 : Refutes moves 0x4000000000000000000000000 0x20022000000000000000000000 :=
  branch 1 0x4000000000000000000000000 0x20022000000000000000000000 75 0x200a3000040010080000100000 (by decide +kernel) part38 part51

private theorem part1 : Refutes moves 0x4000000000000000000000000 0x20020000000000000000000000 :=
  branch 1 0x4000000000000000000000000 0x20020000000000000000000000 85 0x21420011008004000000000000 (by decide +kernel) part2 part37

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part119 : Refutes moves 0x2800000800000000000000000 0x1d305d00001100a00500000100 :=
  finish #[
5469,87414122605167657,4165,77743635348886872,4174,13485110,13481024,54771503629350,43190804600052,4183,4171,4174,13055325,4298,13472344,
9049237,4168,4160,11481572,4146,4154,13484908,36438974494143,5178,13496795,10317861,4185,4165,27593965746,26812212192,
4171,23313851252,11034698,4131,5464,9491027,4171,13497070,27644695505,17786589253,12199264,12317422,11128884,22792507880,4170,
4158,4154,11092750,4145,4168,4159,4166,4187,49557156906325,25966278080,4154,46413264827544,4159,27590439696,4177,
24407544896,56509969527774,4154,0x19b285ce69d7440,0x19b2efc51a9d42d,4154,25831978035,10638293,4154,37988644147895,4177,4183,25229628470,0x177ee966c9d7436,4165,
91806924431029594,17812153194,4165,9850957,4144,4172,4160,94801184657609167,5466,0x66e3a85c853a0a41f5bf,4165,0x93a50c0c26cb505bf,0x5431579ba0c171af35bf,4162,4138,
4154,27595629437,51667673539342,28438483518,4162,4159,98105250096239776,4160,4168,19320427869,22794899942,4885,23362576680,8712268,4183,
4177,4181,24192811446,47765459288728,13484111,73721930391376764,8716346,13890598,12264797,98379939728130097,0x21ae9fba59b2d126e85042c,0xa179ba0d82816555d,4164,4305,44385173832957,
21888127861,4148,13484108,5468,58267364753645,21878951967,23583442173,23499628635,4165,4173,4197,4168,0xc075a2a520e8502ab,93925077099934464,4172,
5466,23315067839,36560247148602,4198,4174,4190,4186,4184] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part122 : Refutes moves 0x810000810000000000000000 0x5e70cbd2040b42850b02040902 :=
  finish #[
25117712879,5566,11514351,4178,25035523210,4135,0x19b259d4d29e5be,4158,4186,11035499,9888619,4165,13472604,56561718911836,4165,
5376,0x175ed3948409500,52934191461632,4170,11034706,41477625910411,27593265944,5280,9888906,11382880,4154,11444298,4161,4185,10249184,
4874,54963882406274,4170,4187,22769013824,9528171,4171,4192,4168,4186,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part123 : Refutes moves 0x800000810000000000000000 0x1e11c9c0000302800300040102 :=
  finish #[
13472507,5466,44574992810765,4154,4198,0xd3d83b3666e53f49c,0xcdc7734fe6cbb2432,4155,25112199757,5466,0x175f01ce64d92fb,13473024,0xcd95a4eea6e41b2fb,9904191,4181,
4173,4161,9553242,21039756424,4168,5466,13472533,97763511418463282,4181,4173,27593995036,23372227258,11477077,4172,4161,
4180,4177,4185,13882717,26814305622,12292141,28434076730,58228202128442,11075638,4186,4891,46513843020735,4173,23384134714,44386014683635,
4147,4171,4177,47868654761101,4885,12292881,11445013,9105489,4172,4186,4180,44575847683007,53242707363069,4137,39196099507546,
4848,13472228,4166,4555,54789376136638,4144,4137,27594797932,4498,26840241087,11449108,10227762,4168,4158,4138,
4163,56510036669301,4155,4162,0x1818bf29f8a94fd,18597864223,9113685,4180,21085655704,56510790083224,4172,9138834,4180,47646199615800,0xa119bc8aa6c84b307,
9557338,4186,4181,25186473011,5466,0xafba76ec26cbb119a,0x1761365dd84f5bc,4181,4180,10313818,4154,10335578,4885,24304116510,0x34ec853539b276c27913495,
4192,4186,4180,11129144,21680071928,95044483008234167,4186,4177,54968842032284,0x182e4f94a29b367,22618427600,9138874,4192,4186,10350676,
10309705,4163,4168,4173,4189,4198,4178] (by decide +kernel)

private theorem part121 : Refutes moves 0x800000810000000000000000 0x1e10c9c0000302800300040102 :=
  branch 1 0x800000810000000000000000 0x1e10c9c0000302800300040102 88 0x5e70cbd2040b42850b02040902 (by decide +kernel) part122 part123

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part125 : Refutes moves 0x800008800000000000000000 0x16146982091180810100111100 :=
  finish #[
17637950499,22677922763,8716358,46390128969053,27615625791,4185,0x63fc7d37ca0571166105,41063782408980,4183,77112002980713208,11522934,4185,4164,4148,9802321,
9494735,4187,4166,4172,4233,0xbaf5a4ec94d29e3de,4172,0x86b43736ca6a9e558,27620380854,51618725606746,4164,0x17420e26ccdb3de,0xb5d4f53726da9e558,4172,4183,
95617235252647162,4180,4187,4168,46513829823053,25019499676,5376,45914251670878,12296268,9936944,4177,5170,17238602793,10314714,9936964,
4177,4233,0x97e6babf517111298,4172,4190,4178,4400,0x17651d26e41b2fb,13485408,27615909020,10272820,4144,10351250,4178,0x1763370ef96143d,
40068230365589,4187,4180,5375,46086848886108,4183,5469,0x63fcdc50536c1b972298,4177,4157,51147575489120,4178,11375474,4144,91500740725699538,
23566586367,95639217271567709,9883742,4172,4180,4197,4189,4168,4184,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part128 : Refutes moves 0x800000800020100000000000 0x1612492c114900804920020900 :=
  finish #[
4591,24974745785,0x1819064b7048491,4172,4168,13484318,46626782819672,4180,0x1743371449c611e,4148,0xa821bae84e327f253,91462244664173629,4174,22769779183,8683705,
45925348938587,23306286219,4189,10297393,4180,41477826438178,22803329795,0x18e68cd7d9d2426,4180,4174,95637413915735074,48297975243925,9859156,4166,4146,
4154,4187,4186,22654338400,75808516436665600,0x30244dcdb762a326e41b560,4172,4148,28441294176,21687993791,4166,41359783179315,47890666480394,4197,4162,
10711539,5469,56565763281474,4148,0x91a46136e9fa3d374,4172,4981,24406782627,21199937573,4174,4198,4189,4178,11342984,47628212060755,
4159,0xcdc50cb508e1d23cb,25192788743,24394400909,8716496,11481297,10309841,4168,4163,4198,4186,4178,4183,22541755744,49723963548711,
11891199,4144,4162,98632897516103103,10314812,8716990,81573785219953024,4175,4181,4177,4178,21987225809,13497109,18452051293,9024666,
27645559758,46644647400110,4187,4186,4174,4162,9564568,37988501156542,18581491917,4186,4174,4178,9867568,9916914,4189,
4197,4192,4168,4172,4180,4184] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part130 : Refutes moves 0x800000800024000000000000 0x3612690c134100904920000920 :=
  finish #[
18197516450,44364764349187,4183,18530730634,20923933557,10216416,24355263239,11444276,4153,4145,4394,4305,18597872411,46696304042772,4173,
4174,4183,4184,4172,20993380851,13472352,5276,25997415102,4178,48180266394675,4155,4954,19550160221,13471826,0x5723542224694d28c3d1,
4151,4144,4190,4172,20963431356,11116948,10297434,49987476886187,43191207313720,4186,5466,38338699961118,4165,4173,19424710964,
0x4ebaea462bf42817e55a,4177,20209684784,4168,4172,4184,4180,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part132 : Refutes moves 0x800000800020000004000000 0x1612492c114104924900000900 :=
  finish #[
4695,13485408,12694874,4148,5566,4988,51148364801373,4184,4189,4178,53096208286976,0x8006a14fcb74d908c,56509240160755,4163,4178,
12694880,5472,11133630,9544082,4198,4184,11059282,4172,4197,4190,21094044155,27592778802,46292980908627,8712602,4184,
4186,4178,11453269,44678071858525,21075248474,4178,0x183ab466c9163cb,4174,4198,4691,17845695059,4178,21829018195,41482617214301,11042886,
4161,4154,4168,5466,56510808838612,4156,35845229663007,56507663111313,4161,4298,4864,27592861024,56513407312755,4189,17793708104,
4166,4174,4186,13472818,49552275902724,9113912,4178,4190,0xc763acbca6c919429,27591697267,25107432120,8712396,4175,4178,4181,
4177,98996715144811382,17851650836,4174,5261,22501782069,13496378,9835294,4148,9564568,56505957397088,18581491917,4186,4174,4178,
18716463694,9916914,4189,4197,4192,4168,4184,4172,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part133 : Refutes moves 0x800000800020000000000000 0x1612490c114104904904000900 :=
  finish #[
5466,4877,27594437064,4159,4172,23381751125,4964,13472243,20286001751,4172,4184,4189,25020322974,25187684754,4166,
13472924,27617223067,4198,4189,56598503272716,0x1837364a9aeb493,10249068,4198,4168,4138,4163,4178,22545273327,47728749442082,23458862227,
0x183ab514a4d9362,26014212864,4198,4183,4174,4168,81840210499744339,4964,20024948058,4150,46168576586208,0xbbb9b29fd759c618b,4198,36547179983922,22500988250,
4147,4175,4168,4166,4154,0x19b8baa6fa7f0ff,23442076817,51153287287953,53241029686016,4165,4197,4148,0xc1f819040244d93c6,11522338,4156,
4891,9859867,4174,0x5752ed742a214f04949a,98418494796313542,11415622,4187,4186,4154,56510917890360,13472627,48008482062847,8712396,4175,4178,
4181,10735825,43242368963454,4174,50020108595963,25829971296,4148,9564568,41252850807382,18581491917,4186,4174,4178,9867568,9916914,
4189,4197,4192,4168,4184,4172,4180,87278675735430590,40775761904992,4124,83504958616212829,49554599572828,49881978115424,4148,4172,
4180,13472343,11518551,40125407839101,4797,23400911154,8712396,4181,4175,4172,4180,4177,49724819133888,27592475997,4183,
5468,47890725585862,0x19aebed729c610c,4183,12193859,4138,4298,24294548638,11518440,4154,4186,23581061997,53251664450202,17810977372,4189,
4183,4184,4174,4168,21518970962,4116] (by decide +kernel)

private theorem part131 : Refutes moves 0x800000800020000000000000 0x1612490c114104904900000900 :=
  branch 1 0x800000800020000000000000 0x1612490c114104904900000900 26 0x1612492c114104924900000900 (by decide +kernel) part132 part133

private theorem part129 : Refutes moves 0x800000800020000000000000 0x1612490c114100904900000900 :=
  branch 1 0x800000800020000000000000 0x1612490c114100904900000900 50 0x3612690c134100904920000920 (by decide +kernel) part130 part131

private theorem part127 : Refutes moves 0x800000800020000000000000 0x1612490c114100804900000900 :=
  branch 1 0x800000800020000000000000 0x1612490c114100804900000900 44 0x1612492c114900804920020900 (by decide +kernel) part128 part129

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part136 : Refutes moves 0x1800000800000040000000000 0x56555f182107a0c00328002100 :=
  finish #[
54935307907223,23390901696,4144,11854781,8683569,98046737761546615,91174202835424101,4164,0x2ba8d841f42271c870484fe,4181,4166,0x80252653a9fae255e,21587293630,4130,11518128,
9080891,8601983,23599899412,8691785,4181,4305,8700502,10682577,4159,22594388571,0xb3c0a09cd42b4d363,21938557013,4166,4195,4189,
4183] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part137 : Refutes moves 0x800000800000040000000000 0x17114918010320800108002100 :=
  finish #[
23389992094,0x18e54fd9c41d43d,53286027768596,4183,0xc754ef4f60e956488,4133,4137,56580435382938,27549659924,4158,0x1a7a559a9cd43c9,26814297237,11060565,4158,9506903,
4181,4166,20999639502,0x18ed37cb9117355,22476132760,4144,4181,25998541356,0x19a9055499cc2f5,4144,4877,24096388442,4181,8606549,4155,
4157,12694567,26820264220,13484080,4124,4695,9544274,44626532880983,4166,4190,4178,4183,4189,9315467,49929331807581,
4168,58265757926336,11875677,11509796,4161,4501,0xc7c5ea8f17d11f1de,4183,4178,5083,10675059,13484081,17411457999,28448126106,4168,
21779915714,4177,22793732680,4144,4154,4754,53057830121951,4173,5170,48139394675753,9113681,4186,4178,4174,12260698,
4979,49673328706906,9953338,4177,4506,0x174cd3a6cb4435f,9954653,4177,4181,17801721183,47865433101182,4195,9138482,4186,4178,
4190,11886857,13472149,51223602229653,4165,4195,23610627013,44470321300046,23564730752,4178,9949257,4173,27591283288,51223602229430,5258,
0x169a75e04b57166,11030594,4144,36101290447735,4173,4181,0xcd98328f05b8af433,4178,4186,9867568,4760,8692310,20310315085,4189,4164,
4168,4197,4180] (by decide +kernel)

private theorem part135 : Refutes moves 0x800000800000040000000000 0x16114918010320800108002100 :=
  branch 1 0x800000800000040000000000 0x16114918010320800108002100 96 0x56555f182107a0c00328002100 (by decide +kernel) part136 part137

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part140 : Refutes moves 0xa00000800000000080000000 0x165c4d5c01c13ec40140011100 :=
  finish #[
24405176522,9113902,4184,27550389387,39312050451605,11916045,4183,4151,0x82742e6c26b84e35e,9122094,4192,4180,58230599299832,95256798167405618,4183,
46701285675688,4180,0xbbc4ef3510cafb5be,24407163748,49985872704356,4163,4183,9114492,0xaeba7a7057d8af5c0,4168,9826388,4166,4162,4154] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part142 : Refutes moves 0x810000800000000080000000 0x5e704b0e059968c40102010104 :=
  finish #[
4973,23457682160,4148,26001392493,4137,10298334,4165,8582397,36086576768139,4165,26771145694,26771177960,4146,4186,4154,
56567383569564,11899965,4178,28413355357,0x8679b73714a27f491,4145,11129724,10298716,11826332,0x1a7706daeba5258,9527375,4174,4192,4165,4180,
24983536989,51167238382843,4174,97552503201973494,12264180,9515706,4174,4180,12199256,23524782265,4187,4382,4386,11486357,4187,
9859156,4174,4178,4154,0x174a26d1c8322f8,37852025148764,4161,12685494,0x19b626e6e2975be,25116619551,4180,4186,4183,0x8482ce2741a3ab4a0,17619923123,
9032066,11915445,4192,4174,4183,4382,0x19b880c898f81d2,39453833155733,4187,4180,17533330577,0xb5d064b8c1508f3ba,4154,25144586290,4139,
4178,4148,4158,4168] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part143 : Refutes moves 0x800000800000000080000000 0x16714908018128c40100010100 :=
  finish #[
4492,9938271,0x90b5fa7460804b3c5,8716364,4177,73581236363326104,0x66eada0a0a1a3e1d148b,4154,9543986,18717233746,4154,98991508955033772,18717283197,10731578,4177,
4172,4195,0xb4a77f4ee9fa810a2,90899191447303115,11128882,4305,98351819729994411,26812732261,48310465139960,21888225358,4172,4195,4183,5468,5469,
5469,11130205,4166,4180,4161,9531808,19590841388,9519515,4172,4166,4178,12694877,4794,52901643408142,4166,
4180,4680,11092859,10670484,4186,4180,4144,4795,11129490,9113658,4402,10334866,4169,4183,4178,
4174,0x19b65c88bad1231,27619603808,11494556,4157,4685,11527018,4181,4144,10736294,0xcdc5fca308d1d136a,4198,4178,4183,5184,
0xc7c454b65dfa813ba,8602370,4156,4154,39657254121681,4186,11342622,53276981695232,4183,11064162,46685749998646,4198,23541174453,9937694,4185,
88570289389036027,4144,4165,4181,4173,47716461441429,9105720,4186,11129136,11407664,72139239137993012,81469882908660607,4166,9949263,4181,
4173,9884150,4164,4172,4180,4197,4192,4168] (by decide +kernel)

private theorem part141 : Refutes moves 0x800000800000000080000000 0x16704908018128c40100010100 :=
  branch 1 0x800000800000000080000000 0x16704908018128c40100010100 88 0x5e704b0e059968c40102010104 (by decide +kernel) part142 part143

private theorem part139 : Refutes moves 0x800000800000000080000000 0x16504908018128c40100010100 :=
  branch 1 0x800000800000000080000000 0x16504908018128c40100010100 93 0x165c4d5c01c13ec40140011100 (by decide +kernel) part140 part141

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part145 : Refutes moves 0x1800000800000000000100000 0x56545f28030520c40b800001a0 :=
  finish #[
10215631,23597450686,4169,28448331094,13456114,54917241713300,4163,4130,8708298,4181,52950624842520,42646056374671,4168,9081033,26032595736,
10229182,8687688,9859159,4150,4158,4166,17786504256,11072661,22677532970,11128898,4166,8688104,24356057576,4148,25227203419,
24353514347,23524390037,4166,28433654247,0x177f050b3a9b300,23516393542,4146,4170,4187,21986869937,8717065,0x1a761291ba9d37c,4166,21200311056,21198324111,
4181,46678377587291,4159,4169,4174,4184,4183,4189] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part147 : Refutes moves 0xa00000800000000000100000 0x175c4d7c0701328489c0000122 :=
  finish #[
13882517,26727507296,13451297,51619577623593,4150,11416529,58232989955228,11416922,9756929,4129,4133,4141,11088740,4158,4183,
13104072,0x1750ef17a4d9318,4166,9506974,35726496957786,4141,0xa195e9365ae9c13c8,4158,4133,47588611051688,23238645182,47588565337534,13471787,23449251910,4146,
4163,5276,11514530,4154,4298,0x1764be8249d7375,4185,4175,9113902,4184,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part149 : Refutes moves 0x800001800000000000100000 0x5738cb2a430322c40d80000f20 :=
  finish #[
13472223,13471921,8979802,4159,4151,0x86a05d365acb5d375,53141281559898,73684160105116832,4190,4184,4178,97535912397608181,23509963162,49360126448896,43265987286165,
5466,23575852277,4175,23506031664,4184,11915340,4165,4178,0xc09a7e13caf4d9307,23573422761,0x95e812d5e6caea1a0,0xa86229364af04f491,4175,4178,4172,
0xcd90041251727f3d8,27591696593,4184,0x1a76d5d6e290560,11453016,20251648074,4165,4197,4181,4185,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part150 : Refutes moves 0x800000800000000000100000 0x17304929030120840980000120 :=
  finish #[
56615582544940,4679,11133914,4197,4183,9888906,9888223,84379924332495604,4156,4158,4157,4764,0xa1b1aa21824967423,4170,11116948,
4165,36446467256491,8688694,11133332,4165,4186,20251960095,4153,4148,25143276704,9888512,4153,48301464876170,4864,27593630191,
4154,9527353,4186,12276393,25201287647,4185,47729586823860,4174,17559590040,27593667264,19514605653,4166,4175,4187,4180,
20120187469,10253661,17643897311,10744973,4174,46533523919837,4166,4187,4180,5267,0x177e2317629d422,13471807,22792574006,4172,9564949,
27592032672,4153,17845272780,95598743220252978,4163,4174,4183,4178,13471920,56562177733070,0x175671d6882e55d,4142,12620626,27592078014,4159,
10330808,4158,4183,4178,11440536,54814220088162,44812290192234,4190,4183,48213143687953,23543517574,40039509390590,4198,11527514,9904176,
4177,4157,4181,46524625949837,27591627156,4172,27592073425,27593269755,4165,48345624974108,38334515635244,4694,21165191371,4190,4174,
9883750,72139239137993118,0x485c1715f0654a4d955e,20310380614,4185,4172,4181,4180,4197,4184] (by decide +kernel)

private theorem part148 : Refutes moves 0x800000800000000000100000 0x17304928030120840980000120 :=
  branch 1 0x800000800000000000100000 0x17304928030120840980000120 72 0x5738cb2a430322c40d80000f20 (by decide +kernel) part149 part150

private theorem part146 : Refutes moves 0x800000800000000000100000 0x17104928030120840980000120 :=
  branch 1 0x800000800000000000100000 0x17104928030120840980000120 93 0x175c4d7c0701328489c0000122 (by decide +kernel) part147 part148

private theorem part144 : Refutes moves 0x800000800000000000000000 0x16104908010120840180000100 :=
  branch 3098 0x800000800000000000100000 0x16104928030120840980000120 96 0x56545f28030520c40b800001a0 (by decide +kernel) part145 part146

private theorem part138 : Refutes moves 0x800000800000000000000000 0x16104908010120840100000100 :=
  branch 1 0x800000800000000000000000 0x16104908010120840100000100 31 0x16504908018128c40100010100 (by decide +kernel) part139 part144

private theorem part134 : Refutes moves 0x800000800000000000000000 0x16104908010120800100000100 :=
  branch 1 0x800000800000000000000000 0x16104908010120800100000100 42 0x16114918010320800108002100 (by decide +kernel) part135 part138

private theorem part126 : Refutes moves 0x800000800000000000000000 0x16104908010100800100000100 :=
  branch 1 0x800000800000000000000000 0x16104908010100800100000100 53 0x1612490c114100804900000900 (by decide +kernel) part127 part134

private theorem part124 : Refutes moves 0x800000800000000000000000 0x16104900010100800100000100 :=
  branch 1 0x800000800000000000000000 0x16104900010100800100000100 75 0x16146982091180810100111100 (by decide +kernel) part125 part126

private theorem part120 : Refutes moves 0x800000800000000000000000 0x16104900000100800100000100 :=
  branch 1 0x800000800000000000000000 0x16104900000100800100000100 64 0x1e10c9c0000302800300040102 (by decide +kernel) part121 part124

private theorem part118 : Refutes moves 0x800000800000000000000000 0x14104900000100800100000100 :=
  branch 1 0x800000800000000000000000 0x14104900000100800100000100 97 0x1d305d00001100a00500000100 (by decide +kernel) part119 part120

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part154 : Refutes moves 0x820040010000000000000000 0x367c898498e00e41a220049002 :=
  finish #[
13079319,11867375,11063339,47799817355614,4141,10986153,0xad44510393d22455c,22651940909,4172,13472908,10650395,4169,5257,25839654234,4166,
53297390690752,0xd3e53a54a0fae64fa,4149,10289221,4173,0xc0b9ae7413d28c3cb,4512,21761226076,88017509119271694,4172,4169,4192,11043128,10289464,21930091089,
4177,4153,53164148503223,0x2a306ad3e6a31f0512fc1bc,10707807,4153,26030515264,72458985862815883,4153,38334698222557,4192,4198,26796737980,18717639454,11419734,
0x16b93666da94365,88402669429977886,4198,0x18f90591b22a365,4165,4153,11518829,4162,4131,4139,4155,4171,4195,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part156 : Refutes moves 0x820041000000000000000000 0x3e78990c9de28a610430820800 :=
  finish #[
25866379945,0x18f87141b3be55e,0xc7c76f069430b736c,11518837,4155,4186,4154,37251485234522,53224772592373,4155,0x1a7cbf17621e3c5,10634283,0x89875a2dd1523049b,4178,4184,
4177,4165] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part157 : Refutes moves 0x820040000000000000000000 0x3670090599e008410020000000 :=
  finish #[
4852,56557668771260,12615711,51475378242711,12616096,12617151,25049134430,53224772878887,4171,4195,12313367,11092012,4166,4173,4187,
27574747914,5263,94913631992448344,25997316153,4154,41102043947786,0xcd7742ea9db2fc30a,4154,4187,4689,25997046717,5275,10290522,4198,44207697974618,
4154,9883718,4172,4184,4148,10683455,4495,12710590,4154,0xc1541ad451eb5c2fb,4148,4166,12313367,51653100552983,4148,
87523174625039500,4178,0x1768ce11128555a,4492,98098121255526805,4195,4178,4689,56547709862662,9564753,12283986,13472626,25864782606,9883727,4152,
4180,44670726377868,10633997,21779911337,4152,37351401944215,4178,11460707,4141,4173,4181,4192,4679,22484215127,4172,
83584145641689859,0x19acb526ab514fb,4139,56546929750790,4172,25956996350,10289464,4198,4178,53228714394580,44381165245595,12190190,24966354174,4195,4177,
20983047026,20981404530,4156,4144,4172,4152,4184,10683455,51494362485329,4192,72304061856985967,24419836497,10683045,4195,4171,
4785,20773995173,8613929,4152,8614382,4777,11019404,4148,0x1744ed44a0984fb,4149,0x5d111f4602894d29e0e9,4172,4183,4169,4155,
24356430881,98455727582102688,4195,22592017086,0x66cbaa834ef8e8296298,8626267,4156,8638653,4169,4166,4161,4162,4165] (by decide +kernel)

private theorem part155 : Refutes moves 0x820040000000000000000000 0x3670090499e008410020000000 :=
  branch 1 0x820040000000000000000000 0x3670090499e008410020000000 72 0x3e78990c9de28a610430820800 (by decide +kernel) part156 part157

private theorem part153 : Refutes moves 0x820040000000000000000000 0x3670090498e008410020000000 :=
  branch 1 0x820040000000000000000000 0x3670090498e008410020000000 64 0x367c898498e00e41a220049002 (by decide +kernel) part154 part155

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part159 : Refutes moves 0x820000010000000000000000 0x341c89c490400200a200041000 :=
  finish #[
8663327,12301653,10675546,4139,9540954,4177,4753,21779452702,4182,0x1776889121191cf,22651940966,4172,4190,11416917,49452465480345,
4147,98939593749554327,4155,5466,11116739,0x8f767c28946047427,4177,4169,46216736531612,27551215819,8692580,90902558744445510,4189,4147,9105489,
4182,4180,4800,27626414772,4190,27590243584,17409828186,12705877,11453599,4147,4895,4503,8679623,4173,4180,
4168,4171,13472528,8691911,9130060,49505616475377,36306626351899,4169,46508198688085,46506527371748,4180,4182,17241243783,13481404,11072956,
9859116,11030598,0x20c09dc1e83ee9d1b04a306,4171,4694,9844058,0xa2d83ca76041d5367,9121869,9564570,4195,4190,4192,13472408,20192535691,4172,
92132375727404067,4180,44810570932427,22651167131,46389590610330,4180,4192,52975991616672,18681717517,21166420052,4168,4173,4169,4189,4193,
4184,4198,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part161 : Refutes moves 0x8820000000000000000000000 0x77591dc5914000000000000000 :=
  finish #[
20162147466,12689876,21116867721,4161,4173,0x19bceae3c9c710c,0x1756ed97b2fe178,4173,0x60d41e76d364e61db423,4183,4169,9884256,5466,0x19bc85e0d90b440,4169,
0xcd96baed851969302,4156,8692206,9121869,4182,4172] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part163 : Refutes moves 0x822000000000000000000000 0x3c348b4cd15444000000000000 :=
  finish #[
20176011463,21199508240,4193,13471911,37462526968987,4149,25217307408,4180,56509237776988,9106098,0x1768b920d3bb130,0xbbb5c9069d541f260,21938557030,4165,4172,
4178,4190,19255768113,11088861,0xcd976041cb6910557,4180,4168,36082483097777,0xbb706459d71af342b,4138,40947674411901,18581410488,4172,4168,4178,
4162] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part165 : Refutes moves 0x820000000200000000000000 0x3c103957914000040042080010 :=
  finish #[
25981014911,53228471534352,9552366,4190,4198,9884138,11088065,4183,4162,94910093046965591,51528050405783,4187,0x66e81442ea6a9f4d7500,40974510842260,0x8d24368cc8804930a,
4175,9048139,4166,9040271,23607038654,0x175a4384f96d423,21166420384,4183,4198,4189,17701082266,10334500,18547507395,4175,4173,
9072841,10351086,4193,36422741062402,4190,4186,4182,4184,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part166 : Refutes moves 0x820000000000000000000000 0x3c102944914200000000000000 :=
  finish #[
5466,51186846503275,27594409010,4155,5169,12313649,45032240673543,4162,4172,4189,4163,5163,0x5da3a69b20e48f8b529a,4178,4186,
56420854965396,4406,91078479127368085,4193,4198,58240373986442,11034826,4159,9130187,4184,5466,10732590,4189,5466,5059,
49522795594195,4172,4178,25992991488,53227097362618,9052218,4155,4163,5279,46218430570781,4163,13471930,46216257560888,4178,4184,
11842335,17801290394,9544666,4189,4184,82163588955424095,4144,4172,4186,4193,4165,4169,0x1835065d8bba3b9,23434466057,17671492746,
9429672,4186,4159,4156,11088366,8650942,4166,4169,12706581,27590792158,4172,44865482748302,4193,58242594611904,53164913824307,
11116832,8671329,4166,25067021471,53110864450335,17683849307,4159,4163,18700919863,11461006,11092037,52920356402231,0x19bc01968afe6a6ed81b29b5bc,4166,40118930748762,
4183,4193,53108596286196,10350991,4198,17717392155,43001810104608,17780544383,0x18faa266c9df0f3,9883750,4192,4189,20980576459,11129522,4189,
10334500,8684124,4175,4169,20998632493,0x90e4eea30240a942c,4166,95607192401114271,10310126,9105505,4192,4186,4182,4180,4172,
4184,4178,11124808] (by decide +kernel)

private theorem part164 : Refutes moves 0x820000000000000000000000 0x3c102944914000000000000000 :=
  branch 1 0x820000000000000000000000 0x3c102944914000000000000000 57 0x3c103957914000040042080010 (by decide +kernel) part165 part166

private theorem part162 : Refutes moves 0x820000000000000000000000 0x3c100944914000000000000000 :=
  branch 1 0x820000000000000000000000 0x3c100944914000000000000000 85 0x3c348b4cd15444000000000000 (by decide +kernel) part163 part164

private theorem part160 : Refutes moves 0x820000000000000000000000 0x34100944914000000000000000 :=
  branch 1 0x820000000000000000000000 0x34100944914000000000000000 99 0x77591dc5914000000000000000 (by decide +kernel) part161 part162

private theorem part158 : Refutes moves 0x820000000000000000000000 0x34100944904000000000000000 :=
  branch 1 0x820000000000000000000000 0x34100944904000000000000000 64 0x341c89c490400200a200041000 (by decide +kernel) part159 part160

private theorem part152 : Refutes moves 0x820000000000000000000000 0x34100904904000000000000000 :=
  branch 1 0x820000000000000000000000 0x34100904904000000000000000 78 0x3670090498e008410020000000 (by decide +kernel) part153 part158

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part170 : Refutes moves 0x801000014000000000000000 0x3e02c1a6a4940291022a044088 :=
  finish #[
72532709591216392,0x43e41001b36603c0e36c,13484117,12223631,11076649,4141,4155,0x56f3a682106e6e3b24f6,5161,25998984435,4186,9544745,4198,4178,5170,
25958228221,25183756693,4187,4172,22687102095,53248352027409,4149,25111012113,4153,12297664,11076658,4155,0xcdc76306c8d1d6311,10231890,4198,
4179,4144,4164,56563254658089,25891078643,28430148751,4198,4187,11875581,12305364,11875180,4881,47633849627786,4147,4155,
4179,4187,51273533608889,21022532537,4187,0x1a7f1fc22843311,4166,4174,4171,27570459409,11801529,56556450341817,4147,4135,5257,
19835323742,10708314,11519326,4163,4187,10609305,4141,4135,12305047,20706956049,25958670384,4134,4178,27590811846,53250845959514,
0xcdba7b365690a64f6,4391,25019146645,4189,4178,23237563537,47596962947369,25111011421,4144,4184,4164,25102193491,58262441648979,47592737063385,12619843,
4155,9060550,21727994612,17754612876,4142,9060847,9855043,4189,4181,4157,4161,4153,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part172 : Refutes moves 0x880000014000000000000000 0x1c23f1b194900282a220044400 :=
  finish #[
5276,28449269085,4198,12649920,26696050112,11429009,4149,4147,4141,8659513,18652181545,4291,12657715,43414084920081,4198,
4179,4169,47939841668055,4153,4193,4174,27628389001,27627184597,27578445881,8696114,4174,0x16b886dde04c0c4,4300,25182912715,0xc1d9ad040efaf24ee,
9949257,4192,4188,4193,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part174 : Refutes moves 0xa00000014000000000000000 0x164bdbf4849002a80aa0055000 :=
  finish #[
10346791,18271080647,23381008986,4192,8704204,4181,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part176 : Refutes moves 0x800000414000000000000000 0x142ef1f08c94c2a00260044020 :=
  finish #[
0x175f03973290429,13103802,9556274,4178,4198,20065849730,26734793679,0x1a7a434a623955d,4168,4192,9552261,41748583994505,4178,4184,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part178 : Refutes moves 0x800000014100000000000000 0x142ad9a1d49807820220064004 :=
  finish #[
77497314522940376,0x9580510796e2ec557,4131,0x181c269084d9220,5466,95370973790377010,4169,4141,56453294158609,38332861109594,95146455280620800,0xa2d826a251f9df0c3,4178,4169,4174,
4198,4193,21195125613,27618747633,4150,4305,27611976282,13480538,0x80400cd226d97e55d,4184,4193,43311126373230,9077243,4165,4161,
4169,4181,13472041,10719633,4186,90366164868113373,19539014795,4198,38074952487662,8704204,4184,4181,4178,4174,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part179 : Refutes moves 0x800000014000000000000000 0x142ad1a0c49102800220044000 :=
  finish #[
43346966140054,26023022900,49503861724221,25841189726,10335370,8704072,4179,17853277021,21106905498,4193,4190,4195,4192,13472050,18701206589,
4155,0x20260dcd90e10785891d311,4193,27590820815,12694111,8696685,4171,8713255,11391951,13489191,9122975,4186,40121145352322,4195,4192,
4190,0x1814018eb41e255,5260,21123982476,4165,23575122005,4169,4188,4193,4177,13459861,0x181d3648a3a80c3,4165,9106583,25997013770,
53052973512030,4198,4193,4186,37627884446685,49780518392675,8688983,10326697,21150036835,4174,11866714,9565138,4198,4184,4186,
4181,4393,90500361800897597,4193,8675717,4174,4165,4171,11120721,4168,4161,0x19b91c17e4d9500,56510857859248,4144,13472529,
0x19b906dd42f3427,4170,12259634,0x69dc0b8fe759dd11d356,4195,4198,4193,9139035,58266471346841,4147,9540849,98321187950547256,4169,4172,4512,
23331852895,4172,0xd3b7653657d04b087,8712398,4186,4179,4181,4177,25204462452,23593420122,0xcd9450474d8158111,4151,4147,12304559,41102268081022,
4169,5466,0x8099b31f85997a311,4169,4603,48028144956255,4179,12305459,19574498143,43146672988576,4177,4190,4172,4195,35931767779503,
4120,4186,11034725,4131,11092750,4168,4138] (by decide +kernel)

private theorem part177 : Refutes moves 0x800000014000000000000000 0x142ad1a0c49002800220044000 :=
  branch 1 0x800000014000000000000000 0x142ad1a0c49002800220044000 56 0x142ad9a1d49807820220064004 (by decide +kernel) part178 part179

private theorem part175 : Refutes moves 0x800000014000000000000000 0x142ad1a0849002800220044000 :=
  branch 1 0x800000014000000000000000 0x142ad1a0849002800220044000 70 0x142ef1f08c94c2a00260044020 (by decide +kernel) part176 part177

private theorem part173 : Refutes moves 0x800000014000000000000000 0x140ad1a0849002800220044000 :=
  branch 1 0x800000014000000000000000 0x140ad1a0849002800220044000 93 0x164bdbf4849002a80aa0055000 (by decide +kernel) part174 part175

private theorem part171 : Refutes moves 0x800000014000000000000000 0x1402d1a0849002800220044000 :=
  branch 1 0x800000014000000000000000 0x1402d1a0849002800220044000 91 0x1c23f1b194900282a220044400 (by decide +kernel) part172 part173

private theorem part169 : Refutes moves 0x800000014000000000000000 0x1402c1a0849002800220044000 :=
  branch 1 0x800000014000000000000000 0x1402c1a0849002800220044000 84 0x3e02c1a6a4940291022a044088 (by decide +kernel) part170 part171

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part182 : Refutes moves 0x980000004000000000000000 0x7c27e935f10000828320004c00 :=
  finish #[
4294,11887770,36322018587409,4169,4291,91040030423011466,10233175,10638679,11075630,4169,4190,10637782,0x1835065afbba1d6,23432466489,4152,
4136,12215645,27619209373,10235952,25019072668,24395920145,11460687,4141,0x57881c9ac3c26da2b560,4142,0x19bed111223c125,4978,41026903627100,4175,9515204,
8700606,4178,4180,4174,4171,4177,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part184 : Refutes moves 0x901000004000000000000000 0x3e0b4936a18480830122004808 :=
  finish #[
24403604330,48131277251235,27592819665,56613174973065,4168,4587,48128040481740,0x5022f15bd3720da9055a,4141,9531444,4175,4178,4157,12690784,23255909728,
4148,13471911,18506679347,4155,97619487569851153,4683,53232054243520,9068637,4177,4181,4161,11076862,5367,9068829,4161,
4163,18576675806,0x18342a1182e94f7,0x18345a9182f14f7,4157,4189,4192,23521928340,11862681,44399896556890,8671317,4177,12689571,25988171098,24402743363,
53227076997522,74394247291359995,21786346650,10735701,4183,4189,4190,4166,4178,4171] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part186 : Refutes moves 0xd00000004000000000000000 0x7d2e59ee810000a20160006800 :=
  finish #[
27594433199,25932317359,4155,21751932247,17735873204,4181,4168,83827219470812506,5466,11862681,4165,21679653018,11453285,4139,8675363,
91703583316480206,10699634,23498846609,4162,4168,8687815,4172,4181,4178,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part187 : Refutes moves 0x900000004000000000000000 0x3c4a5924810000820120004800 :=
  finish #[
17364521836,11007134,51253819978610,4164,4174,11481964,53058662929279,23341368559,0x402b3b776b7a084d95c0,4153,11518837,4155,4186,12301457,25194042024,
4168,5062,11473574,4152,21788750808,4153,4171,4136,4181,4172,23230760384,4686,0x17788854a41648d,11518805,4147,
4178,4155,0x43441b9b8a75789cd491,21811549628,4880,44624932606831,9519191,4172,4178,4181,4175,25988223447,11035413,4166,25219999164,
51304704848952,8675391,53228773557311,0x177cea82404b37c,4174,4181,4172,24404694368,4289,0xcd9044d660d040155,48311925085339,4150,4186,4171,11518359,
25193223217,56457624277976,10661963,4184,4189,4289,22687879307,10519707,83550737838465809,37314902480318,4130,4134,4133,0x5a5ba35213660da211cf,4150,
4186,53093799650750,54882888446944,21839852200,4148,90366445347758851,0xbbb1acbb88faf155c,4184,4165,4181,4189,12231646,49912068874731,4171,56613898400428,
9528188,4171,54914649671004,51131839665020,4189,9331548,75690528359121155,9564238,25219282075,12230731,4150,10285087,4172,4147,4157,
0xc0b9b336dd016a2c0,19515412872,19588882729,4181,4183,5183,12202773,21855408520,4181,10297416,4150,0xd3b8e08226f84655d,25996611786,4181,25219999164,
0xae123eea91584d153,10326101,10338365,4172,4175,4192,4177] (by decide +kernel)

private theorem part185 : Refutes moves 0x900000004000000000000000 0x3c0a5924810000820120004800 :=
  branch 1 0x900000004000000000000000 0x3c0a5924810000820120004800 94 0x7d2e59ee810000a20160006800 (by decide +kernel) part186 part187

private theorem part183 : Refutes moves 0x900000004000000000000000 0x3c0a4924810000820120004800 :=
  branch 1 0x900000004000000000000000 0x3c0a4924810000820120004800 84 0x3e0b4936a18480830122004808 (by decide +kernel) part184 part185

private theorem part181 : Refutes moves 0x900000004000000000000000 0x3c024924810000820120004800 :=
  branch 1 0x900000004000000000000000 0x3c024924810000820120004800 91 0x7c27e935f10000828320004c00 (by decide +kernel) part182 part183

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part189 : Refutes moves 0x8800000004000000000000000 0x561b5120a10080800022044000 :=
  finish #[
11093147,18597831454,4172,26728809535,18597839625,4172,0x18285982585031c,4183,4181,56610701550430,20212416705,0x18365620d3b442b,4147,4157,0x60853f8325a4258b13cc,
4178,9077434,52932590544220,25848042158,4152,4166,5275,58197026059424,8695881,0xa9d36136c50050560,5275,9114779,4172,27591918741,28412940729,
5472,11916443,9797705,4159,4147,11915872,0x181277e0d0b1317,4172,4168,0x60d1db684d6458850248,4181,4183,4174,4186,4178,
97448607554851367,0x69eba72091f8e3bba49f,4164,49986654020755,4127,12707168,12706773,24296543391,4177,9121865,18682942224,4168,4172,0xc7f35f03a0c8b3497,8988092,
27595240591,53157405209856,87243491365442716,12259381,4144,0xcd58fd04e6f8b3106,4190,4172,19421913863,4169,4157,95042873823585435,4894,25981874572,23539961929,
4172,4168,4404,8713176,4179,0x18341417c97d48a,9936968,4177,4181,4197,4189,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part192 : Refutes moves 0x802000004000040000000000 0x1e1e4738c11214808028404090 :=
  finish #[
21986824864,27640746853,8671816,10736210,4183,12619869,4155,12707168,25841189463,0x1778d504f2fd37b,4161,4169,0x9a6536a74232f509b,48327560729184,4184,
4168,4295,5463,25947923413,10285125,4192,11510047,52972458435927,22627456349,24101609820,17399350026,4147,4131,4127,72108809563915414,
10305605,11489376,4164,90965879740920378,8676029,4169,13472638,9114589,4170,10731930,4183,43313546359270,4197,4192,4184,
4190,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part194 : Refutes moves 0x802000004020000000000000 0x1e1f412cf1100494c028244810 :=
  finish #[
4261,8663235,0xa7b04d364213ba428,4153,4174,0x1690b8e3bc092be,0x19be86422a37495,83788404435660992,10351675,4189,4163,4174,4178,11092750,45033974305739,
4172,53286011769724,4408,18720485826,23518770005,0x1a7ebccd01cd49e,4145,4155,9139646,10621320,4174,97745333491741064,4130,25159344919,19515810163,
12271694,4147,4177,4150,4197,5466,88606714739008364,4154,9900328,4168,0xafc2c2bb56a8b15c0,0x5aebba3408f0e68b72fc,84760238688244497,4168,4197,
4190,4172,4192,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part195 : Refutes moves 0x802000004000000000000000 0x1e1e4128c11024848028004010 :=
  finish #[
53120459391947,0x19b87323f29d1f2,28431725910,4145,53124166386635,4177,4180,11482161,4291,10622101,21165970206,4184,4180,4168,5258,
11122110,4503,52971134965085,54913062990702,11006003,4145,9528469,0x19bb050e91de11d,4175,4165,4192,4180,18719211662,56574847399167,4130,
39706699694956,4174,11518264,13874417,23583117722,10657864,4177,4147,10638387,41530153464991,38128539341863,4174,4180,4892,49502125233400,
21888225376,4177,4172,4184,4190,4178,11862866,40928498782971,0xad202d1dd0c827352,4139,13471790,12621146,4988,12624471,88615576253199710,
4190,12619863,17578365103,97825688493818032,4163,22570456406,0xb5d8150526c886489,4133,4141,4139,4147,4155,56442136846634,17769419926,0x182aa3c2329b364,
4152,4189,11478175,22717862771,4168,4691,18422023411,4159,5363,10285315,4147,25201296114,4175,4172,19967599962,
22737011149,4177,21547046039,27628348167,4152,27590755571,4147,4987,36270673170736,4168,9138252,4178,4184,4190,4192,
12689492,4127] (by decide +kernel)

private theorem part193 : Refutes moves 0x802000004000000000000000 0x1e1e4128c11004848028004010 :=
  branch 1 0x802000004000000000000000 0x1e1e4128c11004848028004010 53 0x1e1f412cf1100494c028244810 (by decide +kernel) part194 part195

private theorem part191 : Refutes moves 0x802000004000000000000000 0x1e1e4128c11004808028004010 :=
  branch 1 0x802000004000000000000000 0x1e1e4128c11004808028004010 42 0x1e1e4738c11214808028404090 (by decide +kernel) part192 part193

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part197 : Refutes moves 0x800040004000000000000000 0x1c726120c1a000c00020006000 :=
  finish #[
0x306803a9b8da9bd7d2e530a,0x19b6d126b34530a,0x19b89bda24db25a,0x19b89bda241a30a,11456543,23464346972,4131,88714184473154332,4154,4175,4163,8647413,22449792155,4147,12690179,
20117382490,4161,4153,56544372757151,27610825311,4172,0x19b2b68b73bc55c,9077025,4163,4161,4175,4165,0x15a50689e22a812d44540505c0,21979259669,22777418503,
4154,4172,25990649180,46531894478168,4169,0x66d950a76a505029d08e,25989051836,4193,21827485993,17853256085,4172,4183,4178,5464,27608372378,
4148,5468,8647358,4171,4165,45893590893914,80486185686713690,11129714,4152,0xa0a0510796e2ec2f0,4957,0x5052865fcbb178a9d249,4168,4152,4145,
4175,22792176498,90369927248413362,84638052137104158,4152,4172,4177,4187,48127201547710,27611616416,10662560,4178,9904204,27565417627,18105709911,
4178,9139058,11034936,4145,4152,39728666342655,49710172726428,44621718213777,9916495,4168,4172,25077780896,4408,36566657213387,4150,
9936968,0x63841a47a47cbc97e250,4172,4177,4180,4193,4197,4192,4184] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part199 : Refutes moves 0x800000004200000000000000 0x1c126171890010840020084010 :=
  finish #[
21201065303,21043299484,5171,11474076,4197,27565962095,53086840636759,4127,4133,4157,25201341481,0x5a8412a7abf884117352,4187,4178,4175,
5468,42915878310673,27577659689,4161,0xaf6084291789df311,4178,4184,35723264917659,0x4a6af126e35820290558,4155,21610571008,25202066473,4155,8663235,4166,
12689487,4127,4171,22775379094,0xc1a4e8a242584836e,4169,4853,12686266,4170,21803131665,4186,8688368,24992367761,4152,27611579261,
10724026,4193,4186,12211144,23467237673,4193,9077434,17794195653,4197,4170,4165,4175,12690876,58197026927654,8695881,
43097501271388,12690784,0xa08238a7513a394f5,4162,4187,4402,0x18fea7455917558,22736638434,0xc7f81ca7513a3f49b,8708193,4183,4187,4178,4186,22793310416,
0x5d2bb2a76b84538483c8,4171,0x1a76ec82104b36a,56477422183667,20176900983,18648617030,4186,4190,10339473,9868433,0x1834445d19dc491,9105487,4178,12694683,22720226459,
4145,11441308,58192823403761,9105481,20310380626,4189,4193,4197,4184,4192,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part200 : Refutes moves 0x800000004000000000000000 0x1c126160810200800020004000 :=
  finish #[
52937235031486,52932570153845,4179,13472137,23339795802,4141,25988588689,12690193,19470639989,4175,20117349531,9823387,25989341595,53311501989118,4166,
9904210,4192,4189,4157,4177,9336050,25094201621,4192,12694673,0x19b336dad47d3b9,8659025,36320534578622,4178,4166,12259524,
4685,41549676876547,51444459889593,12260213,22683067132,20286771276,11440189,4168,4197,4189,35777161737182,12690016,41547243446467,4197,25186512989,
4133,4144,4164,4184,5156,39607408951900,11034711,8687817,4172,0xa7b9bab69a828649f,20251202715,4168,18572674203,0x9568e4110241de2bb,4197,
4172,18593457203,21804323614,4186,5275,21787177350,8695881,12690197,20913124296,4183,0xa9d47ebd0270b1426,4172,4186,4178,12694673,
4586,10285433,21529429051,4137,4147,38160374133793,4186,10338386,36547018314526,9072835,17842864905,4177,27595617012,46684063409295,8695877,
36560230372103,4186,4190,4172,4408,11473208,4795,46688939623104,4166,4175,4168,0x5a114a4f6a413f8b7427,12694683,12223633,4145,
49711774061724,90649118108632220,9105481,9916498,4168,4172,22793396637,0xbbe39e470be97e495,4172,4177,4193,4189,4197,4184,4192,
11124820] (by decide +kernel)

private theorem part198 : Refutes moves 0x800000004000000000000000 0x1c126160810000800020004000 :=
  branch 1 0x800000004000000000000000 0x1c126160810000800020004000 57 0x1c126171890010840020084010 (by decide +kernel) part199 part200

private theorem part196 : Refutes moves 0x800000004000000000000000 0x1c126120810000800020004000 :=
  branch 1 0x800000004000000000000000 0x1c126120810000800020004000 78 0x1c726120c1a000c00020006000 (by decide +kernel) part197 part198

private theorem part190 : Refutes moves 0x800000004000000000000000 0x1c124120810000800020004000 :=
  branch 1 0x800000004000000000000000 0x1c124120810000800020004000 85 0x1e1e4128c11004808028004010 (by decide +kernel) part191 part196

private theorem part188 : Refutes moves 0x800000004000000000000000 0x14124120810000800020004000 :=
  branch 1 0x800000004000000000000000 0x14124120810000800020004000 99 0x561b5120a10080800022044000 (by decide +kernel) part189 part190

private theorem part180 : Refutes moves 0x800000004000000000000000 0x14024120810000800020004000 :=
  branch 1 0x800000004000000000000000 0x14024120810000800020004000 92 0x3c024924810000820120004800 (by decide +kernel) part181 part188

private theorem part168 : Refutes moves 0x800000004000000000000000 0x14024120800000800020004000 :=
  branch 1 0x800000004000000000000000 0x14024120800000800020004000 64 0x1402c1a0849002800220044000 (by decide +kernel) part169 part180

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part204 : Refutes moves 0x900010000020000000000000 0x3e2a592490728004c140804801 :=
  finish #[
9564314,0x1672a0a9e91f37d,0xba777735c8fc7a5be,4132,4512,48157917835413,4166,4130,4146,27592761760,9564314,40121129747802,8622496,4161,4155,
4163,9466530,19386319528,4163,25051911228,10658685,4171,0x5d3afb1d28a9a83590be,4129,4147,4174,4165,9077820,13472612,23313110362,
13472612,25217331406,4181,4177,4190,4686,0x9af9bc1340e28637c,19572511784,4190,4647,20805157547,11419711,4139,4171,22603182286,
98673393955820506,12660942,25930592462,4162,4146,4154,4510,4779,21830283929,4155,25958670411,4123,4142,4131,4186,
8704892,11063982,8704987,9565240,12673717,4145,10297934,4165,4192,4160,4190,53107608864090,13873625,17830032149,4145,
4286,44609351352510,9035863,4165,4177,5471,38079272637599,25863987497,26022638339,4198,4192,5279,12662111,9827164,4150,
11120718,4166,4159,58189628375922,8705468,12661208,11518656,4163,4162,4186,5271,10298015,4165,4302,83580858529727836,
56421576319368,4165,11128899,4166,4159,48131228951088,23384134092,44652764066849,4181,4198,39604147807372,11042879,4140,4147,4154,
4161,4168,4175] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part205 : Refutes moves 0x900000000020000000000000 0x3c024934904000004100004800 :=
  finish #[
5170,45029737629023,4168,80092023878381697,24202237082,25983054706,23516397625,4163,0x63bbaa9be8c4b3a3d365,4166,0x18dcd5852c793ba,56617259389781,40125457036157,4177,4147,
56505072194519,11031592,56505925005498,4178,4174,51248936538528,43141347316396,4152,9515600,0x19bf06489a304f2,4153,4171,4177,27593216992,13472827,
23500759456,45029754819643,4166,4168,10506318,11089242,4137,36272150783322,4155,4169,4165,4193,4186,5472,27593261440,
27593257344,4138,4154,97795488078734682,4190,12694302,8659642,4169,37787377427604,13497792,91497480492012695,4178,4187,9024078,56510210384156,
4169,37882165867295,4178,4174,4160,4168,9078112,12674010,8671278,11059495,91361712970188124,17760977307,4178,4189,9069627,
13472155,0x19b257cb384511e,4168,10506310,21932904788,12694267,79490388952420541,17759363774,4171,4163,11087944,4137,21761168733,20032271712,22769426507,
4155,4162,4190,13472924,76190374991357276,4162,4797,9061054,4163,4171,24167891704,11133416,4162,4292,17817690808,
4178,4171,4174,49753513813344,25133667260,44359835022372,12628035,4495,46525352973756,10731572,4166,4388,17784156452,4181,4174,
0xcdf5c847c269d91d9,74416239453004469,4165,4192,4190,4187,4180,4177,4175] (by decide +kernel)

private theorem part203 : Refutes moves 0x900000000020000000000000 0x3c024924904000004100004800 :=
  branch 1 0x900000000020000000000000 0x3c024924904000004100004800 76 0x3e2a592490728004c140804801 (by decide +kernel) part204 part205

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part208 : Refutes moves 0x20800040000020000000000000 0x547e432c90e194404030000834 :=
  finish #[
0x16b85626d8a83b9,23583507103,21988422043,4184,4178,4779,24194192736,11489696,4193,4172,4305,25009476960,0x4e33a15e68a26b85055d,4178,44668331656052,
4161,4175,4179,4797,11510716,24120382098,4140,13472621,24193004578,4161,4163,4168,10687447,9007806,4156,
4154,5468,19419956572,4178,22793295196,4140,0xb539be2554eb5a2a5,49468043546814,0xcd707f1da9f961495,9532379,4193,4172,51149120590385,10658761,0x1a76844e09d04f8,
4163,4193,0x66fc7c432a75ad23c37d,4172,4183,4178,4195,10650866,13472829,83197178051392148,4181,4178,11522939,4161,11522910,
21781132126,58192864752893,44703119700418,4181,48329381888862,4172,4178,22718996579,4138,4145,4175,4166,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part210 : Refutes moves 0x801040000020000000000000 0x7e76c307b0e400c24830410810 :=
  finish #[
24377804125,24171102707,4132,10580204,0xc099b6b6d1541e55a,4175,4341,17694171325,41551321407678,4155,10248262,4163,4178,18241942457,4771,
49340899784128,4173,4181,58246956630515,4130,22407127539,0xa8ca7ed291b23d2fb,4166,4178,4595,35667775889572,4187,0x1814729122363db,27575546355,11133427,
11087924,4151,4179,4162,4172] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part211 : Refutes moves 0x800040000020000000000000 0x7476510490e000404030000810 :=
  finish #[
75769744701530252,27610723075,4140,24197853350,22484533414,11517987,4147,94658502701863576,95648894562239039,4175,4165,44376115708091,10708416,48052616549130,4160,
8716364,4184,27568358847,0x19b904d39cdb0ea,4112,76465267593068988,4165,5263,10687644,4154,4148,13480692,72114134788071881,4127,49866407634161,
4153,49711792895119,0x181d35a0d9653d8,4152,4148,35605510468960,91773783340937773,4152,19933524850,41029314790748,4175,83600892597986162,4153,4135,0xa256ac8f41d03e560,
4166,4165,4162,38766604403546,56510925034349,43104778572660,4168,4165,0xad1a7ee866c850300,45863481443774,39160734757118,4130,4154,0xaf10fa0690b9cf4fd,0xbb49b2141762fb298,
4179,4147,8717471,53126474793810,9035985,10297427,4165,50011272233562,4172,4175,4177,4187,22545274106,25053467681,56507335848796,
4154,4130,0x1741364e941e303,4175,13485500,12661701,13463609,0x19b69be3d40e30a,11522631,4153,4148,0xaea9aea4c1f29e125,4165,11117724,5163,
48044547088879,10285125,10326067,4187,4172,47648505673056,10990422,12661911,53108395782808,4166,4178,4169,50014315676705,23598720140,4169,
4177,49558010819743,53165783831076,20243255373,4168,47571292901924,11034781,4145,4871,58262500795741,4155,17451275232,17416638620,4155,0x81e0434fd6a975560,
4168,4160,4172,10298424,41682274378706,4145,0x1a7f370b8979373,25049928191,98321425296647616,4175,4187,4172,9138257,4195,4184,
4193,4192] (by decide +kernel)

private theorem part209 : Refutes moves 0x800040000020000000000000 0x7476410490e000404030000810 :=
  branch 1 0x800040000020000000000000 0x7476410490e000404030000810 84 0x7e76c307b0e400c24830410810 (by decide +kernel) part210 part211

private theorem part207 : Refutes moves 0x800040000020000000000000 0x5476410490e000404030000810 :=
  branch 1 0x800040000020000000000000 0x5476410490e000404030000810 101 0x547e432c90e194404030000834 (by decide +kernel) part208 part209

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part214 : Refutes moves 0x801000000024000000000000 0x3e16e146ba4500804800412820 :=
  finish #[
5259,13472508,8638650,4160,8643744,51444439913200,4175,56454371431563,11133720,4148,4179,4172,4162,17283133579,0x50c3bc380ebd3d413495,
4153,11899679,77604598914823511,4153,9061147,11485479,4187,4171,4179,9904803,28430508820,58225683194651,4155,0xa041e68401e0402f4,4166,
4162,0x174d1fc530433b9,5466,56513299837123,4172,56510152909762,4177,4981,10707743,4177,21032166548,4198,4178,4189,12259524,
12661324,22711833075,0x19b304d4b9d6314,4178,4179,4189,4292,73305085436695309,81980194580984307,4178,25186512989,4133,4144,4153,4184,
4173] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part215 : Refutes moves 0x800000000024000000000000 0x34127144924100804800000820 :=
  finish #[
27611230574,26032480465,4183,0x869a76a09d6af44a0,4147,11915947,21832242129,4127,5466,13874522,46200411463870,4165,4150,4175,0x56d3a11a6e826c9d20eb,
27590873501,4184,4186,4192,37010800489508,0x5a13a13beb853f8b7096,4192,8716585,0x18260dce90b52ee,4192,13485000,27617177790,4193,0xc732994ed70baa099,8638653,
4165,11128913,11092743,4145,4166,4175,4173,48334211711960,17853617120,9081023,4166,4168,8683818,4298,0xb3b5354f93f9d6424,
98599754562122111,4168,8700108,4175,4184,4183,4173,4895,24193872937,46094159745604,4173,4171,17752252706,4187,23265870007,
27617944719,22802126173,4165,4175,56560814457907,46514633905498,9121840,4198,23508750908,48327601894746,4178,41749466379196,11477687,21928997553,21174784090,
4175,4195,4177,9072835,22716657956,4177,4848,50012715373426,9056314,17701900978,8696410,4173,9105489,4190,10347387,
9867871,4160,9867457,0xa13740bf4ee0443c8,9105487,4178,13492419,22743847107,4186,21030957845,20310364242,4189,4193,4168,4184,
4192,4172] (by decide +kernel)

private theorem part213 : Refutes moves 0x800000000024000000000000 0x34126144924100804800000820 :=
  branch 1 0x800000000024000000000000 0x34126144924100804800000820 84 0x3e16e146ba4500804800412820 (by decide +kernel) part214 part215

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part217 : Refutes moves 0x8800000000020000000000000 0x561b5154905004404000000881 :=
  finish #[
25196073127,0x174c8ba0835f3cf,4181,5183,56614769226897,4181,0x17762a1792fa30d,4169,4177,46207131161758,11129027,4166,11477690,0xcdf53cbe8b497143f,4160,
4197,4168,4388,8696100,4175,4394,8716586,4183,4186,56511007339358,0x2ce485cd96ba5a57697955c,27590799564,8683812,4169,4173,
4168,27594450367,11899544,4138,0xa8682c6c2099d60ba,4154,5268,11477591,8712265,4177,9900542,9113672,4186,4192,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part219 : Refutes moves 0x802000000020000000000000 0x1c17414cf05004004000240800 :=
  finish #[
22498403388,4262,26737123992,4148,13471810,13460237,8664410,4173,56512519681072,4162,4172,51429764231922,8660314,4172,27591283080,
19489825524,51608891024432,4162,4172,4177,4594,13472334,22662714526,56559998735518,4144,56608970707139,4172,4168,10547989,44243703526453,
21090910259,4177,4187,4160,4180,5259,56509240947678,4173,0x69da2a9b2a51d50b549f,4180,38300896039972,93928414684148698,19262206923,26735235470,4192,
4198,4168,19437556684,56506848203809,11515221,4155,4179,25052255578,23448428936,20125741119,4150,4154,4162,11416715,0x81283c8dddd9d630d,
44380358726413,0x34fc05b3e5e655c211df36c,4163,4168,4173,12707168,10314700,11477591,4161,4169,5466,46291414258329,48281634681431,4162,4154,
4138,20127392916,0x53f95f6ba85d1e1cd55a,9113664,4190,73089162378757065,9073041,4162,9105706,4190,4168,4180,4172,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part221 : Refutes moves 0x800000010020000000000000 0x1e12e1cc904006044200040800 :=
  finish #[
5466,11035708,13472519,27592487694,4168,4186,4180,8660314,28449686279,53282703930816,4168,4291,56458614531123,4186,4197,
4155,4172,13473116,5466,22742196723,8664410,46153134059817,4151,4144,4172,4173,23439729421,4979,9552276,4186,
20343923101,4197,4189,4180,4177,5259,0x59f4db83a85d4604555f,36354970297503,4189,4173,25938981823,22502486427,19546927868,4166,4190,
4294,38007398998624,4163,22570439144,46512107807219,4172,22801675610,4142,0x30590bcde53c2a0efafb55a,88597107047346578,4130,4163,4187,4179,4162,
4291,4885,0x60ec7c53ad14211cb08f,4198,4189,53113363391839,25904739775,4172,4400,0x17622bd79afb31c,4187,4154,47607809012016,4198,4186,
0xcdb67855dab82522d,12662103,9515068,10347098,4187,10347098,41014608384197,20806882647,46406796812760,9502811,4186,8687688,4173,22676288672,0xa117754fd4a17d373,
4172,0xd3f2fc54dab2733c6,97863979368530695,4187,18682605874,4186,4190,18648625361,84006424410304652,25196475733,9937671,4165,4169,13452053,46681641513247,
4154,17834487880,4173,4179,4184,4177,4180,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part222 : Refutes moves 0x800000000020000000000000 0x1c126144914004004000000800 :=
  finish #[
5472,21762721120,4197,22406251100,25962849233,11916446,4142,22650360771,9543750,4187,4178,0xc1d8e8845d40a4260,21202326675,12305466,4155,
4142,0x183a5c90ba933d1,88189754489299619,4155,4197,17742541475,41549726037237,4197,11915675,0x91a42ea4da829e364,4179,18498351903,4150,4178,4166,
4162,10571978,4298,11457290,10326113,4197,37332378022946,4760,0xb3922c85d389cf2f5,4192,4187,0x34ee3ccd642f074e19d92f0,25120568074,79557304594314588,44277753705710,
19461869659,4171,4173,4175,8642938,0x536a7f7680f8a9967297,9048158,4154,4166,36422690697820,25200505894,10699548,4187,9868045,20210467416,
9916495,4197,97708298473002332,4598,9421302,4291,0x97ea7ad087e048424,4177,4173,4175,4169,4885,10339384,23363817676,4189,
9056357,4156,36491443761662,4186,4178,4192,4184,11124820] (by decide +kernel)

private theorem part220 : Refutes moves 0x800000000020000000000000 0x1c126144904004004000000800 :=
  branch 1 0x800000000020000000000000 0x1c126144904004004000000800 64 0x1e12e1cc904006044200040800 (by decide +kernel) part221 part222

private theorem part218 : Refutes moves 0x800000000020000000000000 0x1c124144904004004000000800 :=
  branch 1 0x800000000020000000000000 0x1c124144904004004000000800 85 0x1c17414cf05004004000240800 (by decide +kernel) part219 part220

private theorem part216 : Refutes moves 0x800000000020000000000000 0x14124144904004004000000800 :=
  branch 1 0x800000000020000000000000 0x14124144904004004000000800 99 0x561b5154905004404000000881 (by decide +kernel) part217 part218

private theorem part212 : Refutes moves 0x800000000020000000000000 0x14124144904000004000000800 :=
  branch 1 0x800000000020000000000000 0x14124144904000004000000800 50 0x34126144924100804800000820 (by decide +kernel) part213 part216

private theorem part206 : Refutes moves 0x800000000020000000000000 0x14124104904000004000000800 :=
  branch 1 0x800000000020000000000000 0x14124104904000004000000800 78 0x5476410490e000404030000810 (by decide +kernel) part207 part212

private theorem part202 : Refutes moves 0x800000000020000000000000 0x14024104904000004000000800 :=
  branch 1 0x800000000020000000000000 0x14024104904000004000000800 92 0x3c024924904000004100004800 (by decide +kernel) part203 part206

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part226 : Refutes moves 0x904000000000100000000000 0x3e020924924820000020800804 :=
  finish #[
56479845610735,21803168828,4184,72974215769605564,0x1a7c821ae1c22b2,4154,10671452,0xc1e8114ed1891f289,4183,4192,11924017,72678793355469684,22568878494,4175,4184,
4384,49360098530458,4192,4174,11765180,27574531001,0x18ee439a0b5c55f,4166,4181,13497309,13059208,26013361600,19514233531,4181,4192,
11518030,4162,5085,11018889,22626309472,11485280,11419714,4131,4147,4163,4171,17619194144,25023414713,97899145707098795,4160,
19138720424,9556214,11518837,4171,4178,23340179872,21836674004,21937374077,4187,4174,4177,4186,4183,20790498242,4391,
4507,83058126722716517,4166,4189,4171,13091708,37921533207413,4168,11133723,4151,4162,8659227,9507711,98626490633675711,4186,
4190,4506,11878810,9036766,4159,4151,37905980744090,4168,11116957,98833937613120276,8671428,4171,4175,37727454758232,0x50fb514785985016a3d4,
4189,4153,4181,4177,4157,4169,4165] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part229 : Refutes moves 0x900000000100900000000000 0x3c02d924924824024924920004 :=
  finish #[
0x18dd36c3b1a9497,56547750310462,4184,47743362851406,76227460306166208,25999303430,11133791,11117035,4144,4169,4172,4193,4165,20915930072,21939282813,
4165,21177939089,4295,8696010,4181,4174,4175,27634234619,4389,8696010,4178,4172,9565338,11416721,4503,
23590236719,4166,4174,4162,8650896,4975,21778309307,18506384159,4174,4162,4189,4165,5276,47897704076447,4178,
53163334714322,4583,8647533,4162,4165,12689481,4127,4160,4193,4171] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part230 : Refutes moves 0x900000000100100000000000 0x3c02c924924824820920920004 :=
  finish #[
4283,17668665832,4174,11768014,24101941454,4166,56547767869896,17686258139,4157,11031708,25980990812,4178,11133723,4169,4193,
4165,4172,23590237144,53245174014844,4165,9036477,4300,8687815,4169,4174,4175,21856629392,11048092,4169,53214871597742,
4177,53241801753064,47898037581047,4165,5265,49368161911257,20194509969,4154,4162,17668653758,11133796,24403829699,39861795070831,4189,9872152,
9060542,4175,4163,4157,4169,12689477,4138,4160,4193,4171,8627055,4301,20741731371,10327194,8622156,
97888953932608283,4174,4162,4178,4988,10327388,4300,48035501741405,4169,4174,4175,13493499,21754790538,4186,41357389632668,
4172,12649815,56463480308690,4390,0x19be2948fc1929a,4181,4172,4184,17668653758,18569093326,4288,20216795332,4157,4163,4169,
4165,17407755420,18172756120,26023806002,18471974231,17767743674,4177,4157,4165,12689481,4127,4160,4193,10518603,4107] (by decide +kernel)

private theorem part228 : Refutes moves 0x900000000100100000000000 0x3c02c924924824020920920004 :=
  branch 1 0x900000000100100000000000 0x3c02c924924824020920920004 47 0x3c02d924924824024924920004 (by decide +kernel) part229 part230

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part232 : Refutes moves 0x900000000000900000000000 0x3c025924924924020124800004 :=
  finish #[
4301,11428045,4157,5265,8647825,4169,23405687964,8659432,4171,4174,4162,12685602,48311144182940,4186,8609973,
51305291703249,4165,0x19be005448970e8,23608258746,4165,12685495,4386,11526939,4189,10285125,4177,4172,4157,4279,19574923450,
4171,17711084295,25990612008,22003994908,4172,4174,4168,25051861170,5267,23391707342,53224563225372,4162,4154,4163,4388,
8696100,4181,4172,0xa186a937da8046426,4587,4587,8683817,4172,4168,4181,23388614862,12628384,0x182c47d6d95f55c,4166,4162,
0x16970684f1d21cf,36030096253105,4181,4165,0xbaa83247d7084d5bf,12685787,18589472085,10338386,4165,23591792839,8704202,21149638741,4162,4172,4190,
4192,4177,4175,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part234 : Refutes moves 0x900000000004120000000000 0x3c026d24924920804924900120 :=
  finish #[
4703,72988817289454630,4160,24327274790,54878115328768,11879266,56541315384170,4175,23338275022,8598094,73888184046424350,4168,4160,4157,4165,
4189,4184,17662321525,48174765024495,4798,44813910008792,4157,4165,4189,12223354,11130011,5471,39936470078327,9556032,4190,
4187,12661915,46682353771248,25989391111,4169,4165,9068837,21151982437,9045147,10338593,4192,4165,38027858850867,8687817,4169,
4174,4180,4172,4177,4175,4171] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part235 : Refutes moves 0x900000000004100000000000 0x3c026924924920824820800120 :=
  finish #[
53227012223842,12694877,98675039264699234,4177,4172,4510,12690475,8602578,12231454,8704051,4183,4177,4175,37323492962461,92229218568409380,
4189,9544765,5171,4301,21192368414,4162,8687911,4171,4177,4169,4175,51271158747804,94272096477221830,4159,43364374081801,
4177,11486363,0xcd4a76ea26e53f43c,10744891,4186,8635263,4160,4168,17685930874,4289,10338500,12689487,4171,37847757005092,8704201,
37731816833805,4163,4175,0xc1b5ed370ee4d70b8,8687909,4171,0x8190385985016a3d4,4193,4189,4153,4177,4169,4157,4165,4390,
53056798204988,4169,4510,8705179,4177,4175,12689614,0x8f883537826a942f2,4145,9044166,4163,4300,22450631836,22802194727,4175,
4162,94756452663464614,4300,25010356380,4162,4175,8634843,9060843,4171,0xc085cce960f3bc5c0,11120846,9871564,4169,4177,9060541,
23541166855,4187,11527018,4144,4160,4184,4157,4189,4192,10518597,4113] (by decide +kernel)

private theorem part233 : Refutes moves 0x900000000000100000000000 0x3c024924924920800020800000 :=
  branch 2301 0x900000000004100000000000 0x3c026924924920804820800120 41 0x3c026d24924920804924900120 (by decide +kernel) part234 part235

private theorem part231 : Refutes moves 0x900000000000100000000000 0x3c024924924920000020800000 :=
  branch 1 0x900000000000100000000000 0x3c024924924920000020800000 47 0x3c025924924924020124800004 (by decide +kernel) part232 part233

private theorem part227 : Refutes moves 0x900000000000100000000000 0x3c024924924820000020800000 :=
  branch 1 0x900000000000100000000000 0x3c024924924820000020800000 56 0x3c02c924924824020920920004 (by decide +kernel) part228 part231

private theorem part225 : Refutes moves 0x900000000000100000000000 0x3c020924924820000020800000 :=
  branch 1 0x900000000000100000000000 0x3c020924924820000020800000 86 0x3e020924924820000020800804 (by decide +kernel) part226 part227

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part238 : Refutes moves 0x800000000004120000000000 0x34122d20924920804924000020 :=
  finish #[
8479082,94048205775540586,4157,0x95083e1c0b4ba62f0,4133,43405200274570,4182,11915572,4891,5170,18497549451,4168,4166,4162,5082,
11133723,4162,0x16ba2505b9de55c,4182,9068744,4171,4175,4169,0x16a905a6da9e426,38076152041876,4171,25991741841,9061427,51268574332059,4187,
4159,27624346590,8622677,4159,11776297,9044565,4159,4171,9888033,4193,4153,4157,9131069,47939770954517,25227649822,
11526630,4144,4160,4168,94556892105569728,0x69fd3e4f0ed51e05030a,10334797,4174,4183,47987394289961,9556280,12214686,9139260,10313814,4174,
43403525731466,50019366466288,4186,21124080032,4169,4177,5280,0x867a76d217a11f084,11128922,18716533824,51662276112696,4183,4169,4874,84172173311107437,
43244861247557,4172,4168,4180,4192,4193,4184,4189] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part241 : Refutes moves 0x2800000000004100000020000 0x1d327db4826ba082cb3000006c :=
  finish #[
4400,18651751271,4165,18664871068,0xc10162269433b23e0,4165,4159,25229619383,56471606039502,4171,51443541902679,39617450153024,4184,11526352,0x16a93582784843d,
4169,18700144905,4190,4197,4187,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part242 : Refutes moves 0x800000000004100000020000 0x16126924824920824920000024 :=
  finish #[
9114779,17721041970,26032522283,11117318,4162,4186,4197,4303,4400,10346800,4197,4192,0xc73125040ef40955c,25938301535,4178,
8683716,9068748,4183,4169,4171,4175,88263680867284215,4305,43157318116413,4163,4178,9740490,0x66e07a6882bc24b5f0c6,4190,5088,
5088,73024003280069781,4165,4177,50014996751703,4380,4894,21199876894,4184,4180,4168,11129129,23523001312,10330585,4183,
4178,83892256591373457,4157,4151,4147,4159,11121408,56473167880489,74707528069240256,4184,4178,4894,4689,9114398,4190,
4178,4864,5070,9077339,4183,49914593501430,10330908,4168,0x177e3d45015e2ab,4177,4157,4163,12689481,4160,4138,
4171,25988203584,9855185,4305,9076934,12231454,0xb4a45507c87166423,21074124869,4184,4163,4168,4183,12264184,11133695,17794196255,
4180,4183,0x91075eeca0d4d65bc,21760738647,9887835,4157,0x1836d04542e9557,25117434846,9904210,53232037098247,46341282067398,18682180359,4178,4198,10289948,
25906754304,24371651349,0x1820ec85b9d0430,4198,4178,4892,46342925537749,9916498,4164,4172,4168,17810912007,42795718001819,9949274,20285219128,
4169,4177,4180,4184,4192,4197,4189] (by decide +kernel)

private theorem part240 : Refutes moves 0x800000000004100000020000 0x14126924824920824920000024 :=
  branch 1 0x800000000004100000020000 0x14126924824920824920000024 97 0x1d327db4826ba082cb3000006c (by decide +kernel) part241 part242

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part244 : Refutes moves 0x800000000004100000800000 0x14122930824920824820020124 :=
  finish #[
4388,23606268775,4190,5263,12305159,4165,13484220,8605883,4154,4160,4159,9114685,0xa6f9b935c520491d5,4171,22775366697,
39617450152813,4184,11505868,18530759731,17767760161,4171,4169,17852874956,4190,4197,4187,4177,11130011,56436503716097,17834906966,
4186,4174,40962103988571,56581978932180,4166,43405107999882,4182,12665527,19588134230,4186,0x91d44abe4e817d36a,4168,4189,4197,22484185481,
21863330776,22541284006,4178,0x174d371d89d649b,4164,4198,25982091737,53020207969034,4186,53020937393193,0x1834be54f175426,4197,51319400145489,4178,4198,
4168,97476970755102044,4699,87295474180342410,4180,4178,5275,25988235868,4189,9077344,9068833,4159,77698587433788571,11121415,25989051348,
4184,9532571,19445482268,4165,4163,8687817,4174,4178,4180,4175,4171,17742197226,36292692436011,0xb5d74c4445328c353,0x168ebd05329a353,
11133720,4148,4162,4186,4183,4296,8717066,46048240534588,10334417,4168,4174,4679,45016846021303,4184,18557068021,
4157,4165,4183,37854189482859,11133332,4183,9077811,25989825099,9887838,4157,4888,58241168872013,4144,24220627818,10736691,
10330187,20285218898,4184,4192,4189,4197,4177,4169,4193] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part245 : Refutes moves 0x800000000004100000000000 0x14122920824920824820820020 :=
  finish #[
25849623135,0x17786da048b109e,4186,11133232,28441682224,80695805551424650,22450631836,4197,4162,17742586747,8683815,4178,4175,4171,4169,
18698924782,27568788134,18471957549,12263487,4165,0x19b85966ebb65bf,8687909,4171,27573650781,12279996,51610586117052,4171,4159,10305842,23609417929,
4165,38071219582090,4183,4184,4187,4177,4294,0xc1b74a44d4d3bc0f4,4192,12280603,0xcdc5349bdd441a0ca,4171,51215475975612,51169590355293,43233361609763,
4180,4159,4187,4591,17760183451,0x1a7d068228a84f1,4163,4171,27619598534,11092265,20117348415,4145,4153,4157,4894,
10719821,0x19aee960d0a83ce,4171,53027522474971,10744604,9077525,4177,4171,4157,4169,21905359046,4305,25989808917,0x84f23aa74ea9da288,4174,
4163,4183,4178,20187292531,4305,0x60d41f38c438b31da0bd,4163,4183,18591871850,0xcde534ba5de1da3c3,9904210,4874,5471,9917006,11104320,
4165,12263897,22778188544,12264602,46271640343903,9916464,4172,4160,53226365583672,4178,4198,9553051,9937694,9949253,4177,
4180,4192,4197,4184,4193,10518621] (by decide +kernel)

private theorem part243 : Refutes moves 0x800000000004100000000000 0x14122920824920824820020020 :=
  branch 1 0x800000000004100000000000 0x14122920824920824820020020 23 0x14122930824920824820020124 (by decide +kernel) part244 part245

private theorem part239 : Refutes moves 0x800000000004100000000000 0x14122920824920824820000020 :=
  branch 1 0x800000000004100000000000 0x14122920824920824820000020 17 0x14126924824920824920000024 (by decide +kernel) part240 part243

private theorem part237 : Refutes moves 0x800000000004100000000000 0x14122920824920804820000020 :=
  branch 1 0x800000000004100000000000 0x14122920824920804820000020 41 0x34122d20924920804924000020 (by decide +kernel) part238 part239

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part248 : Refutes moves 0x802004000000100000000000 0x37360da8c0d82400c030024208 :=
  finish #[
5271,53232077403487,4165,12702478,4152,4892,4888,11477781,4177,4153,53231985562301,4160,4172,36203596563517,22661931189,
4138,53293280723925,47760256353521,79529262067066205,4138,12690183,28441215764,4172,4165,11047495,4148,4190,4183,10253451,21000963222,
4132,11093147,9138674,4195,4180,22624826205,24394821768,9139355,9139165,25151394290,4160,4148,18717328049,4153,4165,
4177,20277186868,22483391647,21118829218,9540182,9138257,4190,4195,5259,18683372387,0x18f8769411191c4,4195,4180,10334807,4164,
4169,4174,4183,4184,4198] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part249 : Refutes moves 0x802000000000100000000000 0x14160dacc05824000020000208 :=
  finish #[
9540748,19993043403,0x1777079411d65bc,4164,8586590,23374061745,4169,4506,11416443,0x8685c70788cc700b1,4123,4142,10711908,49448422598079,4169,
4165,4190,11518844,4163,4195,4162,17770201972,0x19bd0790417148a,9540849,4190,17593656767,11911960,8675416,4169,0xafa08cbb0e32fc30a,
4497,9036575,4159,4165,13873650,40604800103380,4187,84035063198360050,10289225,4184,4163,4189,4168,42623846949462,0x168e58e0d0b131e,
4192,10338777,40962104378610,4408,47902888280662,4165,12689495,4193,9442548,5175,9527688,4177,12197984,9859634,20195296307,
11518048,23380522048,23382884840,11513952,4138,4154,4162,4195,27618329853,11420422,0xc1a5c8ed4e835c5c0,4148,4193,11838033,25990226779,
11452485,10327389,27567313498,23516397632,4154,4162,90289206442267798,23305479035,4169,12628658,48145068541182,21988013004,4190,56579704369751,98080238706520915,
11481182,4138,4162,4195,49962929829015,53229512541131,10309683,4294,44909646341270,17767764264,4162,4180,4172,4168,4174,
20069073965,0x183507979aec30e,77385213712986989,26024137016,0x1810ef0e29d9374,4177,4197,4172,4162,43267587458001,9130965,4190,88607384787469260,9860147,4190,
25034699240,4138,4162,12689888,22659552411,12611686,4294,4295,21114414235,36388364521649,4162,4184,4180,4172,4168,
9437262,4152,4164,4182] (by decide +kernel)

private theorem part247 : Refutes moves 0x802000000000100000000000 0x14160da8c05824000020000208 :=
  branch 1 0x802000000000100000000000 0x14160da8c05824000020000208 74 0x37360da8c0d82400c030024208 (by decide +kernel) part248 part249

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part251 : Refutes moves 0x8800000000000100000000000 0x561b392880482c002020000000 :=
  finish #[
0x8e71fd3520cc1b560,0xcdf4113520c90049b,4164,5265,25980998907,4164,19328033567,4175,4169,0x3041040a383212c800b13d5,4178,4481,12669313,97746586713097251,8716361,
4183,13480585,12690057,4127,0x19bf0690441508b,4144,25990648457,4152,9437481,44126714458910,95601850988496024,4153,4157,4169,0x19be2c60d100294,
53121565131736,4300,0x16ba758278b1307,4186,4174,4183,4178,24277681504,9437773,19329237984,19329614623,4151,4157,4169,4894,
11924255,0x5044df53aa797c97548d,4160,4172,39586396701851,4178,4168,0xa0c411068802de427,0x504415776b79ab84f49b,4178,4975,0x183468c8204f55c,4183,91666516507972745,9949232,
4168,9953787,4169,4177,4197,4192,4189] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part254 : Refutes moves 0x800040020000100000000000 0x1d7e692080e834400820910408 :=
  finish #[
12211350,11354789,4147,25992999593,4138,22407114961,19523323328,4147,4305,98388483974722119,4168,4138,4178,12673908,53232011076652,
4168,21152772874,5468,23515129180,4193,4178,10265173,4152,4172,0x19babe66dc1a251,4975,25989051052,4178,4172,8716885,
54859957883751,11133720,4172,48161452303610,11105431,9138252,4178,20351091283,98454052258963954,4172,4177,4193,4180,4184,4197] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part255 : Refutes moves 0x800040000000100000000000 0x1c72292082e824400020000400 :=
  finish #[
0xa089b706e6b100082,12199356,51496038982410,4148,0x1836a24e817d362,4184,4193,43310581114303,13460544,0x46c4dc758efd44c10560,4172,4148,20804322656,98874000746431332,4154,
46527012668556,4182,4152,10519306,11912246,4168,21073359262,4192,9446351,0x8713a0a256e41a099,4193,5276,22566105473,4193,94896651108336469,
4147,8716362,4182,4184,4187,0x5a9c15a7e0e912419084,4282,56615539003982,4172,4197,4305,5468,23405777208,4193,4192,
5373,11030840,0x66fc1968ad585bc7c367,4166,4172,18717991589,5361,54913091760440,54917290128252,21930168411,4172,4166,4177,4171,4178,
19573630101,40086862258859,4168,4791,51391215817399,9917306,4160,9437280,4182,4152,51665079002054,51390411686638,4152,0x1779041ab89a307,4153,
9011878,45853602406588,20177739958,4152,4168,4160,4967,56459278360859,4182,22794952886,10290240,4178,23539962045,4164,4160,
23475626532,11034781,4145,48161448752287,4178,0x40ec1b2002dd4ba9e09c,4172,4186,4193,17852007196,24352752789,25998639697,4184,19328041756,4175,
4163,4305,0xcdc2b4bba6d900437,0x21d29f4d6414a50281dc0bc,4187,9060949,4171,4175,21990019756,0xba283ea304f1d03cb,9855043,0x80a1500edd5c7c289,38002368308572,4186,0x40141a077054e53bc31b,
20184506424,4192,4193,4197,4177,4169,4165] (by decide +kernel)

private theorem part253 : Refutes moves 0x800040000000100000000000 0x1c72292080e824400020000400 :=
  branch 1 0x800040000000100000000000 0x1c72292080e824400020000400 65 0x1d7e692080e834400820910408 (by decide +kernel) part254 part255

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part257 : Refutes moves 0x800000010000100000000000 0x1c12b9e0804866000221040000 :=
  finish #[
41027678970848,20807148592,0x93667c9b54e89a290,9130041,18648601460,4170,4186,5181,45981186777459,44257493542139,4133,4157,46576775471893,4186,21545821632,
0x19b8ec51723f181,22567712087,56458614531123,4172,4197,4186,0x1a7e9c4889001d9,21853049725,4186,4510,46679855973517,83434898208182921,21116067930,4168,4189,
4178,4198,4193,44093178356776,24129172151,8585309,44090459665649,4606,8590473,9949833,9564232,4187,4189,4186,23387730813,
46340440879439,12317271,9953696,4192,4184,4189,4391,9855273,98589499882709396,4192,4189,4165,4169,4685,25119355469,
0x81681273138a9a5bf,4197,4172,4888,44449095824313,4189,4168,10346881,39586782241843,4189,13463937,47730410856943,9060409,4157,4161,
27568087839,22004818392,0x1744efe041d91e8,84698374760687039,4165,4190,4187,58245901312665,9490729,4168,21107205062,4583,0x17782a089a972af,4190,4186,
8687713,4171,0x17767545404b0b1,8708301,4186,4184,4178,4182,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part258 : Refutes moves 0x800000000000100000000000 0x1c122960814824000020000000 :=
  finish #[
12232032,0xb419beea916afb55c,4162,24171423072,11104452,4162,0x50ca9e5f8114841112f2,4178,4169,4504,47990415389460,49603040617247,4198,9904215,94763027678090485,
4180,4189,51669433160277,22794097606,11899630,4169,4688,8716990,4183,4177,4184,0x90077f35c5084942d,9437388,18581483728,4186,
4184,4170,9438170,12317731,24985203176,10720010,4175,4187,24254211416,4165,4190,49660250420480,11133723,4197,5464,
0x19b689e3fa391cc,12263515,44754910515998,4178,46698014953784,4197,4180,4184,0x29bd0427f6849d0541163d1,4289,17760153793,9437266,4170,10518913,88285807173021853,
21190373569,19328880722,4197,12689496,4171,4193,11124822] (by decide +kernel)

private theorem part256 : Refutes moves 0x800000000000100000000000 0x1c122960804824000020000000 :=
  branch 1 0x800000000000100000000000 0x1c122960804824000020000000 64 0x1c12b9e0804866000221040000 (by decide +kernel) part257 part258

private theorem part252 : Refutes moves 0x800000000000100000000000 0x1c122920804824000020000000 :=
  branch 1 0x800000000000100000000000 0x1c122920804824000020000000 78 0x1c72292080e824400020000400 (by decide +kernel) part253 part256

private theorem part250 : Refutes moves 0x800000000000100000000000 0x14122920804824000020000000 :=
  branch 1 0x800000000000100000000000 0x14122920804824000020000000 99 0x561b392880482c002020000000 (by decide +kernel) part251 part252

private theorem part246 : Refutes moves 0x800000000000100000000000 0x14120920804824000020000000 :=
  branch 1 0x800000000000100000000000 0x14120920804824000020000000 85 0x14160da8c05824000020000208 (by decide +kernel) part247 part250

private theorem part236 : Refutes moves 0x800000000000100000000000 0x14120920804820000020000000 :=
  branch 1 0x800000000000100000000000 0x14120920804820000020000000 50 0x14122920824920804820000020 (by decide +kernel) part237 part246

private theorem part224 : Refutes moves 0x800000000000100000000000 0x14020920804820000020000000 :=
  branch 1 0x800000000000100000000000 0x14020920804820000020000000 92 0x3c020924924820000020800000 (by decide +kernel) part225 part236

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part261 : Refutes moves 0x800020010000000800000000 0x1577c18082492e100204142041 :=
  finish #[
0xafc9b259d9f4d435c,11133720,49503118660768,49449863849099,4178,4198,4172,12293466,4852,0xd3b9b69cd9c113156,11444326,13472619,0x182aa05d7bb9363,4195,4162,
4177,46275799520094,18632643330,11522737,4153,4169,0x19b8cf8dc3b9302,51614411514634,4193,9106200,51562351026385,4187,4177,4162,44277011121022,
92134009324503188,44878256616111,4172,4174,5181,23592165864,4174,18665268159,11514626,54701375296563,4172,9556026,10555477,43226069955544,4197,
4195,4198,4178,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part263 : Refutes moves 0x800800010000000800000000 0x552381a4924926300202140040 :=
  finish #[
11456709,25865212076,4153,24420406000,11891102,9953696,28438537266,0x1a7c468b5172354,4157,4165,4177,4169,4181,44072592720360,27634381446,
0x18fe10dde1105bf,4165,56596650246790,9556376,4186,4190,4193,19546973234,56421671088912,5088,27634013054,4177,9954076,46524588060957,4190,
4186,4193,4180,4873,12305161,4172,12305656,9114494,9556373,4195,4181,22006022341,21912924462,4153,4168,
21619634273,4128,4188,4182,0x1a7d064ad2e65bc,22616851504,10506331,11072760,4885,9114778,4174,4186,8589763,4559,11444687,
4193,4169,4153,18667356357,9757757,11444687,4193,10555449,4122,4494,4606,41355117184156,4186,21672448097,4197,
4188,10346891,0xa2d26b06c8811a15e,17541742761,51568056845565,47939054723765,24244240795,4190,4187,19563716786,4153,4165,4157,4193,0x17791d63f0b51db,
4595,13099518,9564670,4195,13100278,9953779,4181,4169,4180,4193,9388124,4143,4137] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part265 : Refutes moves 0x804000010000000800000000 0x362389a8924026140280140244 :=
  finish #[
11031805,17526772701,97861970624107964,4181,4198,19575706553,4153,9556168,0x19bcbcce10f73d7,9077305,19252147154,36371855737992,9855043,4157,4177,
4165,77497315561800639,73324922647922010,4198,44555450144095,8664000,49468890018751,23466070098,4172,0xd3b9bd1ba6c91f43c,0x19bcba823aed30a,4172,0xae38eaefc541db3b9,36372888396384,4192,
4165,4181,4177,4188,4169] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part267 : Refutes moves 0x800000110000000800000000 0x342bc9a1865026120204140044 :=
  finish #[
19499029850,9077695,4177,23237910823,27590415128,25984603180,84703414098272843,22651986001,4151,4190,4186,22618431796,5466,47753269457684,13492827,
19572979039,4186,4198,4193,56596903071978,13492827,21158729055,4186,22677119073,4147,4166,24152744724,46511344411492,4154,4887,
27591282998,4174,4192,9949761,4887,18591838811,0xbac414d154d84b129,4172,4169,8712398,4186,4178,4181,4177,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part269 : Refutes moves 0x800000010100000800000000 0x1433c9a1925027120200164044 :=
  finish #[
25070256415,27593261940,4154,24348832911,8717357,4187,91571091424298432,4165,4181,0xcd99bca599f04b309,4887,56507468510551,4170,49454074061684,8712397,
4181,4177,4186,4174,4606,18715701846,4174,5466,10622298,11042918,78502507256808208,4177,4187,98959782538056471,46509766604122,
4198,25110061543,4294,25846817531,4181,51419912467213,10272835,4198,4955,27592032464,4198,11101131,9061411,49419732378875,4192,
4181,0x97e150bb5479cc0aa,11477070,4172,4180,4177,4169,4193] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part270 : Refutes moves 0x800000010000000800000000 0x1423c9a0924126100200140040 :=
  finish #[
42839826879536,11018997,49569360335933,51613152363866,27592877107,4197,56506982462514,4178,4169,4198,4193,25034741082,27594048277,25203667906,21165585278,
4198,4174,4168,8697087,36478474584848,4187,17843258133,46523757528412,23304241760,21198685019,4159,4153,0x8503bea50b317a0cc,4197,4193,
4169,4181,4177,27618304488,25907061901,10506312,5568,18330579630,4186,20959826408,4153,4144,10506445,8705375,4187,
0xb3840aee826a8c3bf,49498979156456,4198,9076942,4393,17758990633,4178,4172,4171,4169,4177,47781966893265,24344048798,27591602648,4186,
4174,83070484737205696,19950842051,4168,13890332,13890229,10350791,4178,4174,0x4054d99b8a6ca715a48d,23506313809,4193,4153,4177,10555465,
20129353926,5466,9139250,8716895,4177,4186,21199896771,23507583757,76889197880132663,8663092,0xb383982a0b917a55a,4181,4177,4169,4193,
4595,4607,8712397,4178,13099092,18331849969,9131153,4186,4894,12701825,4163,0x17760b08e9670a6,4186,10350787,10334404,
95280004175733344,4180,4177,4169,26753462369,4134,4128,4197,4188,8705375,45964062007709,8700108,4178,19303235660,4155,
4170] (by decide +kernel)

private theorem part268 : Refutes moves 0x800000010000000800000000 0x1423c9a0924026100200140040 :=
  branch 1 0x800000010000000800000000 0x1423c9a0924026100200140040 56 0x1433c9a1925027120200164044 (by decide +kernel) part269 part270

private theorem part266 : Refutes moves 0x800000010000000800000000 0x1423c9a0824026100200140040 :=
  branch 1 0x800000010000000800000000 0x1423c9a0824026100200140040 68 0x342bc9a1865026120204140044 (by decide +kernel) part267 part268

private theorem part264 : Refutes moves 0x800000010000000800000000 0x142389a0824026100200140040 :=
  branch 1 0x800000010000000800000000 0x142389a0824026100200140040 86 0x362389a8924026140280140244 (by decide +kernel) part265 part266

private theorem part262 : Refutes moves 0x800000010000000800000000 0x142381a0824026100200140040 :=
  branch 1 0x800000010000000800000000 0x142381a0824026100200140040 83 0x552381a4924926300202140040 (by decide +kernel) part263 part264

private theorem part260 : Refutes moves 0x800000010000000800000000 0x14238180824026100200140040 :=
  branch 1 0x800000010000000800000000 0x14238180824026100200140040 77 0x1577c18082492e100204142041 (by decide +kernel) part261 part262

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part273 : Refutes moves 0x900000100000000800000000 0x3c0a4924834124920004904004 :=
  finish #[
4300,21887836844,4190,25133741092,24396009888,11129513,4147,4175,11506072,4584,5156,36080598086078,4147,98849190752142110,4175,
4177,4180,4165,44673259385248,13460421,27568501384,8564794,4147,10732700,4507,10732798,11030609,4186,56425049175386,53285230429240,
4177,13492712,46653756215994,4175,13496518,8672602,25136166240,46513692852831,4189,4180,4183,18573845268,4181,4177,20183209311,
46702795555491,9011279,4155,4169,4157,4165,4576,44086556976090,17552028331,4130,4165,4295,21147996329,0xcde11a59d1c9dc560,4165,
4192,12203359,58265680449675,4165,46531063611626,4172,75971276915519887,35911365152935,4147,4154,4189,12689487,4138,4171,4193] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part275 : Refutes moves 0x900000000800000800000000 0x3c034924934124904004904920 :=
  finish #[
24252621863,25831641499,4157,8704416,0x18168ac269dc198,4172,4180,8696100,39161606378456,9855657,4169,12703061,17768177862,4166,8676698,
27641143712,4181,20192698770,13095323,25018740829,4154,4183,4174,8705164,17826473100,4165,13492397,12658015,26769155423,26769519655,
4162,4178,4166,83569055062372490,21888610601,20875961274,4174,21776999295,11129411,10985542,4147,4187,4189,12689466,4138,
4193,4171,13472158,13472923,12689824,44815511044688,4172,4190,4177,8704254,35432788181685,4157,25988191377,9859366,56507601518876,
4163,4162,4166,12690197,20185334230,18548609228,8683719,4169,4174,4172,13472923,19390375053,13472028,0x94247ab444e8a5314,4178,
4172,4162,36291889501152,36235383891099,11527018,4144,4157,4181,4192,4189,10506312,4128] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part277 : Refutes moves 0x900000000000800800000000 0x3c021124934924120104904004 :=
  finish #[
28441305866,9565053,4184,9564630,20009959607,51180030464680,4138,4162,4156,18398061437,56618079511996,38008255848643,4181,4177,10232692,
4296,4506,56514961868128,25921925408,4168,4159,25922281760,4181,4153,4177,11031805,4512,9000282,4166,4156,
4870,9515474,23231193869,4184,26016998059,4187,4157,95495973134422420,11494463,4681,17643111199,18480349370,4166,4159,4162,
4157,10236479,4135,4145,4175,4150,4190,4165,11493846,0x1834bfa6d90d426,0x19b20d05283a49b,4156,4162,17351943615,12694356,
44345965761692,4156,23249134943,39762237915798,8667835,4166,4172,4165,4168,49624299708703,17784157339,9056460,4166,4172,9860250,
9048552,4168,4279,17691800447,4165,0x8917680d8b51cf0b2,4147,4157,4512,23246009499,5276,0xcdea7ca217091f296,20193316952,4172,4162,
0x34ec36a942d5068e91dc4fd,4165,4175,4192,4190,4187,18567120218,9048957,4156,5278,20085056383,4165,8614071,4156,4157,
11072265,12693685,17826087491,4174,8999113,4166,4162,0xbbc43137c4d41a433,53229637895004,4298,56511015707422,8659238,4162,4166,4172,
4168,20925490334,4297,9056460,4166,4172,4983,0x19b28f66f90d244,56505940549912,4156,4162,40862538846616,21090911387,4177,4187,
4192,4190,4165,10506319,4134,4182] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part280 : Refutes moves 0x900800000000004800000000 0x3d020324934924920100924000 :=
  finish #[
12694683,56454436565666,4156,21149062298,9527468,0x18370688b1511e8,4156,8565152,12272796,12272570,5183,51651487798237,4168,4154,10285116,
4162,4157,4147,4190,25199658035,9040279,4503,24252846277,10338364,4175,4190,17751409535,21965676740,21962014916,4159,
4163,44410536566958,9027768,4163,11526846,4189,21727621300,17659122366,4162,9416992,4587,21880627883,4184,4189,4506,
9871557,4181,5176,8635448,10256451,4150,95297322390241565,4182,4175,4187,4180,4190,4157,4165] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part281 : Refutes moves 0x900800000000000800000000 0x3d020124934924904000104000 :=
  finish #[
9531740,20010685792,40983606424928,4181,8958127,4271,52965923189206,4168,4162,4154,4156,5086,8668220,4171,54831415899383,
5077,4792,92223962448704562,4150,4154,4156,4148,10256661,9507102,4166,4797,27641578173,4162,4587,97897340099920277,
37916477723687,84804187160830932,4141,4168,4184,4181,4189,4157,4165,56610009449816,24102408944,4157,35460416197562,4270,27633545361,
9007279,4156,4166,4162,4154,12305459,49350978938011,4190,9028763,49805014327784,4189,4157,12689809,11120932,4166,
17683845611,25989858655,10297934,4150,4187,4190,4180,4165,19514557018,9769132,53226063630485,83915629593718959,4154,4162,4156,
25182826966,37649904473054,9028763,49805014327784,4189,4157,12689809,9065232,4166,17658680475,10278043,20218496046,4177,4187,4190,
4180,4175,10506309,4128,9388118] (by decide +kernel)

private theorem part279 : Refutes moves 0x900800000000000800000000 0x3d020124934924900000104000 :=
  branch 1 0x900800000000000800000000 0x3d020124934924900000104000 38 0x3d020324934924920100924000 (by decide +kernel) part280 part281

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part282 : Refutes moves 0x900000000000000800000000 0x3c020924934924900000104000 :=
  finish #[
4295,5464,0x16761a66f8471a0,4172,4181,4587,4296,51181867262439,4166,4172,4165,17761690970,77919562394297688,25863234912,38072857310556,
4166,4189,4190,8680202,19825307848,11105628,4190,49569484915960,36268099449319,4187,4163,4165,27593225266,23589024422,8638650,
4157,4159,48351267681148,12300560,12296375,51575167075364,4148,4157,4153,20800442549,0xc771220c26c9c80ac,4190,8634654,4283,36182021468740,
4144,4148,4168,4166,4150,4156,4162,19252891706] (by decide +kernel)

private theorem part278 : Refutes moves 0x900000000000000800000000 0x3c020124934924900000104000 :=
  branch 1 0x900000000000000800000000 0x3c020124934924900000104000 83 0x3d020124934924900000104000 (by decide +kernel) part279 part282

private theorem part276 : Refutes moves 0x900000000000000800000000 0x3c020124934924100000104000 :=
  branch 1 0x900000000000000800000000 0x3c020124934924100000104000 47 0x3c021124934924120104904004 (by decide +kernel) part277 part278

private theorem part274 : Refutes moves 0x900000000000000800000000 0x3c020124934124100000104000 :=
  branch 1 0x900000000000000800000000 0x3c020124934124100000104000 59 0x3c034924934124904004904920 (by decide +kernel) part275 part276

private theorem part272 : Refutes moves 0x900000000000000800000000 0x3c020124834124100000104000 :=
  branch 1 0x900000000000000800000000 0x3c020124834124100000104000 68 0x3c0a4924834124920004904004 (by decide +kernel) part273 part274

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part284 : Refutes moves 0x8800000000000000800000000 0x561b11008b4024140010100000 :=
  finish #[
5064,25194124640,4172,9900640,4168,0x56a8397765d47a1c72af,9953779,4177,4181,8712856,10309841,4168,4305,23597888152,9113809,
20209684788,4197,4168,4192,4172,53025054196791,9483319,4305,39780071310266,0x183a0d42816310e,4162,4174,4186,4154,19960313184,
53020738798360,22802547060,4151,9121865,19949499744,8712500,9953588,4169,4177,20386972815,10330889,38071254733879,4153,4178,4168,
4189,4173,38940047168860,11100670,4189,4305,22733447828,8708580,36532414927332,4168,4153,4174,4178,18573103299,0x9cc5d40f54b0a81f2,
4304,17844531799,4174,4178,4189,4169,17856033274,56470904083594,56539624109194,4153,4144,46322539885054,4156,8712786,13463761,
25874707386,36204271330655,4148,4156,11092667,11092265,10351381,4178,4183,4173,4168,4169,4760,10175122,4165,
13480594,4168,20839494795,85331192707429326,0x183e85cb1891558,4156,4162,4154,90687911019393996,21617766607,54791091413199,4169,4177,44985731454002,37856086496094,
4156,4598,11391260,4156,46681724616913,4178,4189,4168,9113996,8663538,0x8b107e3d0b096918c,4148,9437256,4155,4173,
4170,4152,12689476,4171,4182] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part287 : Refutes moves 0x806000000000000800000000 0x7e169128d3503c100000100005 :=
  finish #[
13099884,10289835,9539656,13497403,36285118354082,4168,11392352,0x3379d1b5c5baef84d9712f0,4168,4990,4594,9502913,23598269020,8651153,4163,
4159,4162,4168,11490158,4132,4169,4177,4172] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part288 : Refutes moves 0x802000000000000800000000 0x1c164108c35024100000100001 :=
  finish #[
23517164890,10346781,27592475079,9437885,17658269752,4164,4165,5466,40864142275838,18581815354,4576,27635135837,21622154188,9130040,11916250,
4147,4165,9437474,0xb4b478bcc558b155d,4184,4172,4190,4174,56508474422141,4294,10306906,4192,10338975,4884,12669727,
22735348500,54927978382008,4184,21064934746,4192,4180,11030621,4144,4183,4165,21731578132,10273352,4184,8671428,4170,
25076232767,25017832029,9900634,4168,4192,18510352570,20279091512,4184,10732403,11477693,87758006410273153,4152,4155,98589335425954202,48139530519898,
4197,0x16a93641f843197,4168,4174,11522122,4169,4180,4164,0x19be234ef29643d,4408,23379800855,46511462167131,24221422460,9859168,4174,
4170,4178,47782772945503,17675056267,4169,4576,4695,26709562220,23514419512,4198,19539415352,4172,4190,4189,4178,
4282,26755187352,48005364307002,4177,4172,11899848,11523318,4180,8630974,8646846,4170,4163,4168,8630974,21986783821,
91343153055110082,4153,4174,9826490,20124524734,4168,4170,9138363,4786,24378806944,4168,4172,9827284,49808879816896,4172,
90682997540389466,4155,8982602,4148,4150,4152,12689476,4138,4193] (by decide +kernel)

private theorem part286 : Refutes moves 0x802000000000000800000000 0x1c160108c35024100000100001 :=
  branch 1 0x802000000000000800000000 0x1c160108c35024100000100001 86 0x7e169128d3503c100000100005 (by decide +kernel) part287 part288

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part290 : Refutes moves 0x800040000000000800000000 0x1c72330083e024500020100000 :=
  finish #[
10555601,11813073,0x177e268800a8422,4175,4173,50012008808706,18346480509,17854493938,11514539,44281281209482,4143,4147,8614071,4156,4153,
4152,4154,4990,9565054,97584133662757817,25224872734,10555474,11092538,4666,94616263208427986,4156,27578445882,4155,12689480,4138,
4193,12694871,10236091,13480005,24420287448,9437367,9851265,4148,4156,4152,17624794175,21827486783,18490400977,23606591672,4164,
4152,4165,27565208343,8717079,4184,21193437393,4170,17852875642,4152,4172,4187,25988235966,22767009981,0x17451d487050314,9077223,
4171,4173,17854850203,8716978,49967023444367,11522934,4153,4164,4172,4148,4169,11522926,0x19b60ec523b2318,87933708150432923,4153,
4165,4602,19589317213,4187,12313435,27592033724,9564232,40121144959666,4172,5166,22734689135,9936968,4165,4173,4184,
4192,4193,4197] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part291 : Refutes moves 0x800000000000000800000000 0x1c122140834024100000100000 :=
  finish #[
49808426460204,93990573313168035,12202569,24251756946,4169,24992633606,49982524854965,9867337,4148,4180,0x18fc275ae9723c8,0x16ba2754f2252b8,4148,9531891,9916518,
4189,4192,0x1a7cefdd110d558,0x177ea50280b5422,4184,98004957200474280,4154,0x167212426100440,9048671,18530734568,4171,9072932,4184,4166,4170,
9494698,9859756,4154,4285,26747974290,4155,10973773,4144,9827389,11117434,9532378,4198,4187,4178,4974,
0x336ddfcdf6728cd76a3915c,23248343330,95258583496516956,4190,4165,4187,51560489768081,46203733799099,4510,10744876,4169,10670162,4187,4607,0xad95f2ee4ea0b731f,
9916510,4197,4184,4180,4192,25921487910,0xc179be9e8b91c7129,20998590872,4178,4198,26810245519,90969439784215904,5267,20998631619,4198,
4189,0x9cc9b82a02290048f,4155,4173,4170,10719525,4584,20195693816,77735149636392284,4187,8687712,4178,4887,0x1778b541da3955d,4169,
73342296171737224,25998185718,10338363,36976692798605,0xad953b06549af9433,20310380592,4189,4197,25225262118,20141765110,0x183a401088a75c0,4166,4164,5267,41359009440697,
4187,25921917996,51214725869775,4186,4192,9437973,0x1772a7537900440,10306047,4197,8695904,4173,4177,4178,4184,12689492,
4171,4193,11124822] (by decide +kernel)

private theorem part289 : Refutes moves 0x800000000000000800000000 0x1c122100834024100000100000 :=
  branch 1 0x800000000000000800000000 0x1c122100834024100000100000 78 0x1c72330083e024500020100000 (by decide +kernel) part290 part291

private theorem part285 : Refutes moves 0x800000000000000800000000 0x1c120100834024100000100000 :=
  branch 1 0x800000000000000800000000 0x1c120100834024100000100000 85 0x1c160108c35024100000100001 (by decide +kernel) part286 part289

private theorem part283 : Refutes moves 0x800000000000000800000000 0x14120100834024100000100000 :=
  branch 1 0x800000000000000800000000 0x14120100834024100000100000 99 0x561b11008b4024140010100000 (by decide +kernel) part284 part285

private theorem part271 : Refutes moves 0x800000000000000800000000 0x14020100834024100000100000 :=
  branch 1 0x800000000000000800000000 0x14020100834024100000100000 92 0x3c020124834124100000104000 (by decide +kernel) part272 part283

private theorem part259 : Refutes moves 0x800000000000000000000000 0x14020100804020100000000000 :=
  branch 2907 0x800000000000000800000000 0x14020100824024100000100000 64 0x14238180824026100200140040 (by decide +kernel) part260 part271

private theorem part223 : Refutes moves 0x800000000000000000000000 0x14020100804020000000000000 :=
  branch 1 0x800000000000000000000000 0x14020100804020000000000000 44 0x14020920804820000020000000 (by decide +kernel) part224 part259

private theorem part201 : Refutes moves 0x800000000000000000000000 0x14020100804000000000000000 :=
  branch 1 0x800000000000000000000000 0x14020100804000000000000000 53 0x14024104904000004000000800 (by decide +kernel) part202 part223

private theorem part167 : Refutes moves 0x800000000000000000000000 0x14020100800000000000000000 :=
  branch 1 0x800000000000000000000000 0x14020100800000000000000000 62 0x14024120800000800020004000 (by decide +kernel) part168 part201

private theorem part151 : Refutes moves 0x800000000000000000000000 0x14000100800000000000000000 :=
  branch 1 0x800000000000000000000000 0x14000100800000000000000000 89 0x34100904904000000000000000 (by decide +kernel) part152 part167

private theorem part117 : Refutes moves 0x800000000000000000000000 0x14000100000000000000000000 :=
  branch 1 0x800000000000000000000000 0x14000100000000000000000000 71 0x14104900000100800100000100 (by decide +kernel) part118 part151

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part295 : Refutes moves 0x28000100000000000000000000 0x57f08822002940000800000000 :=
  finish #[
47871842820580,47866094937240,4149,11412442,20159685594,4158,53060238713795,19364836386,4158,4159,4138,13472638,98993328261071739,4133,0xb546b2b9d19a3f36e,
4174,20099810460,51515660751332,45070022165457,18539529080,11128903,4161,4182,4159,4175,48092807112026,0xb4d5eb1b4e60a448f,4163,0xbbb154a18af29b427,45066655974051,
4186,4187,48276699792732,4689,9093713,4185,4163,4968,9036670,4163,98995064921825826,4137,25027519355,87419306906349818,10313802,
4154,0xa0e77737573b4b294,11466080,54725001999705,58267400106267,4142,4151,84316093998261598,4164,4159,0x168e52945cdd172,22641197928,4182,0xb590a8a7ceb10b305,4163,
4181,4187,23417688629,0x19ba58e6cae74f7,46374551803226,4185,4148,47873562407798,11899181,4165,13488820,86742437970940782,9843555,4154,44862871520016,
4181,4182,4186,4187,4485,24329695621,44862253122508,4138,10334287,4159,0x872a7e5220941d55a,0xa215d10320928835b,4175,8732973,21158031445,
4163,4168,4174,4178,4184] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part297 : Refutes moves 0x20000100800000000000000000 0x4c924824104900024804020100 :=
  finish #[
4666,79395570690273738,51577829962114,43094957069465,4140,4150,4153,0x177471e08ad4500,11129609,4168,4161,4575,0xcdf834b957d4764fb,56545278399529,4162,
4172,10633695,56513234301798,4168,12219744,5178,21777953850,4171,10272834,4154,4183,11510535,56613031957659,4503,21042881199,
22718656907,8736840,4184,4183,4186,4187,4192,47782637982863,97922854707848347,0x19b30391ba92491,46720876610608,22810587826,10289225,4168,4163,
4184,90969651125658760,22576465147,25120187440,5168,11891069,4171,4154,4172,11138096,10597152,9875528,4150,4162,21981164679,
44057182418266,5278,0xcd95f503141a983d4,4149,4156,0x17725adddba7430,4154,11109053,42662425687098,10309690,4189,4163,4183,47646114476909,25094579053,
98413288473883494,4156,4177,11485367,0x18353766ca8b1df,4871,4896,0x180cd71d78ff48f,4166,4169,0xc1a81cbb0e8299430,4143,4163,4192,21854942363,
5178,51393701205033,0x18229f4eb1db064,4169,4174,4189,4878,10195625,46410849272685,4162,4163,4306,20883547279,46596388132091,39518280422169,
4166,4169,0xcd72b4ea145c1c437,51270208549639,4196,8736979,4183,4189,4192,4184,4850,25034281735,27594048282,53231089956186,4159,
4876,0x538baf00ca497623a4f5,4163,4181,9891937,4162,4890,53275455779214,9957469,11789056,11055904,22810968672,4189,20327149656,4166,
4183,4174,4190,4187,4186,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part299 : Refutes moves 0x20000140000000000000000000 0x4c980eb8800990000aa0000000 :=
  finish #[
4504,26781087068,51514871702572,0x18393663c1b9437,12689452,4149,5181,56524112712453,4159,4196,4182,0x66e86e50cea26d35c560,17903612684,4190,13480107,
25120571749,10977349,4857,0x19ba8396ea310f1,10977970,9564223,4190,9101400,4181,4183,5181,0x43e27f4ecebd6e28d55b,4159,46254350980137,23592600535,
5466,46404892525519,9764925,4159,0x19b135e0d2fb36d,0xc6ea771b5a98a05c0,56505934648082,4164,48177933878125,4139,9506877,4184,4193,4181,88404538034717472,
4601,9929581,21593818267,4751,11109042,9543754,4192,9101400,4185,4181,10289952,11903749,4166,94726954676675739,0x1750a10573af49b,
0x5d42f36b8a7c4f0a6300,4161,4169,20201259077,4159,4183,4163] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part301 : Refutes moves 0x20002100000000000000000000 0x5cb50c68a40904210800000000 :=
  finish #[
22601520189,12702685,0x176a9e20ea8d55a,4187,4168,5275,25990657085,4192,53233645642595,10544474,5466,54898492236942,4149,4147,4143,
0x93a83536638c07084,51668692468872,4147,22719836940,4175,4168,4159,23383352666,0x63a3b29b410579afb429,9875523,4154,4170,0x175eeca6ea9f368,0xa8b9bb1bdd316b4fe,4154,
21124858143,4159,10310036,4168,35280686798080,21594944858,4143,21127602951,4154,4857,76505398797997013,11386953,4147,10334969,4168,
9540262,4973,23456510362,4168,4163,4980,28450083693,9924697,48160803615996,21980098775,10682465,9945151,4182,4190,4187,
4183] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part303 : Refutes moves 0x20000100000200000000000000 0x4c9828e0801940000c00003400 :=
  finish #[
4878,4495,0xc1738e6e4872943db,4159,21913605076,9892829,11063704,21804322916,4162,4192,4193,4847,13104372,10350635,4507,
46044434059968,4180,4192,11121244,58190535226116,11092856,0xa9d5cebfc8a1db492,4169,4159,0x1824bfc2b28d3cb,98245665211601850,25117454752,9941089,4178,4186,
4190,4182,13488431,54846953120047,4182,4878,88791595538920489,25990189854,4138,4186,4168,22483751987,4399,10719840,4168,
4169,11514741,22483800744,9863264,4147,4163,12210831,25990656966,4170,11433115,4126,42354611405408,4169,81779825883661049,4159,
9556381,4981,44966062191484,9896017,4163,75061325488178032,4182,4186,4190,4171,4183] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part305 : Refutes moves 0x20000100010000000000000000 0x4d903861882b01000809080008 :=
  finish #[
0xa6f350a49aba8d488,41627512423168,4183,0xb3c10e0bd352714fb,11445592,56476491715648,0x5dfba14fed38b7b5f36b,4154,4171,0x19b50726cb5f151,0x1a7b364b7af3300,10645578,4156,4162,9892594,
11064000,10698845,4175,11354601,8656218,5466,4955,27590804830,4171,4161,4196,4868,0x19ae86e0ea9f55b,4171,5278,
26016560474,9875535,4158,4150,11023507,5462,11875185,4159,4175,25102623507,4154,4143,11051780,21803528964,4162,
4604,10671067,24379650747,4169,22006383278,4147,20268447070,4190,4171,4175,4187,11510835,41444172214757,4187,26794340941,
0x183a8d0b823f2f9,4187,4186,22486553758,41371442214235,4169,56506823079070,0x19b34ed16a3f1e9,0x5d81709b277d070553d8,4190,4187,10309722,4178,4189,4184,
4183,4193] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part307 : Refutes moves 0x20000108000004000000000000 0x5c952861c30b22c00842100020 :=
  finish #[
13472498,12297065,90567126792250240,54877896295774,4162,11522939,4172,4156,4868,27591667901,4162,0x18f48fc8423455a,4175,4187,4169,
20361856051,27593265631,11006713,10978258,19447849922,11092044,4175,4187,4857,11379650,4169,19564966784,4182,44626532479830,56490590336250,
4187,4704,27592864352,27590484576,4190,10309723,4163,4178,4183,4193,4189] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part308 : Refutes moves 0x20000100000004000000000000 0x4c902868830b20800800100020 :=
  finish #[
11092743,9945589,4183,5373,49402530030218,56488554255292,4169,4156,0xc0e41c9f48a11d55e,4184,5470,18644570528,23506744668,10273071,11378775,
4145,4169,4177,4680,11478364,0x169d36420b563c2,4162,4172,4896,10253280,23523991933,4175,0xa0e5e4559490a00c1,4165,4159,
4157,11486165,12300896,25017549408,4177,4184,10351378,56512426631961,48176703591193,10744279,9896009,0x5493b1694298b416c431,4151,4187,4175,
4159,4183,4163,4592,46379736216310,48145991672304,4175,4185,4588,0x1676a18ad284300,4185,12252195,10646872,0xba2676ead13a94305,4196,
4187,4168,11006448,0xa7f688eac4c0a04fe,4157,4163,4159,11035029,22585274860,0xa375e4b9c89a3c1d3,4196,9925003,20325946233,4184,4187,
4186,45998346252838,0x1778a110729f430,4185,44226504909081,10350655,4694,4797,0x4a087b46eb70ea8550ba,4192,4190,18641043846,20202472110,51613940482825,22775783825,
4177,4169,9912813,4190,4159,4175,4187,4163,4183,20372624139,4605,5466,11854432,4163,44224964564027,
88933981555769844,4186,4187,4184,4189,23424070141,8738138,0xcd941c158be1d6423,4178,4184,4875,10313938,4189,0x8195a8a74ba0a21cb,4387,
20302357184,4189,4184,10273633,91910860079875418,4166,43416349475107,4147,4151,4175,4163,12689471,4127,4182,4193] (by decide +kernel)

private theorem part306 : Refutes moves 0x20000100000000000000000000 0x4c902860810b00000800000000 :=
  branch 2716 0x20000100000004000000000000 0x4c902860830b20800800100020 75 0x5c952861c30b22c00842100020 (by decide +kernel) part307 part308

private theorem part304 : Refutes moves 0x20000100000000000000000000 0x4c902860800b00000800000000 :=
  branch 1 0x20000100000000000000000000 0x4c902860800b00000800000000 64 0x4d903861882b01000809080008 (by decide +kernel) part305 part306

private theorem part302 : Refutes moves 0x20000100000000000000000000 0x4c902860800900000800000000 :=
  branch 1 0x20000100000000000000000000 0x4c902860800900000800000000 57 0x4c9828e0801940000c00003400 (by decide +kernel) part303 part304

private theorem part300 : Refutes moves 0x20000100000000000000000000 0x4c900860800900000800000000 :=
  branch 1 0x20000100000000000000000000 0x4c900860800900000800000000 85 0x5cb50c68a40904210800000000 (by decide +kernel) part301 part302

private theorem part298 : Refutes moves 0x20000100000000000000000000 0x4c900820800900000800000000 :=
  branch 1 0x20000100000000000000000000 0x4c900820800900000800000000 78 0x4c980eb8800990000aa0000000 (by decide +kernel) part299 part300

private theorem part296 : Refutes moves 0x20000100000000000000000000 0x4c900820000900000800000000 :=
  branch 1 0x20000100000000000000000000 0x4c900820000900000800000000 71 0x4c924824104900024804020100 (by decide +kernel) part297 part298

private theorem part294 : Refutes moves 0x20000100000000000000000000 0x44900820000900000800000000 :=
  branch 1 0x20000100000000000000000000 0x44900820000900000800000000 99 0x57f08822002940000800000000 (by decide +kernel) part295 part296

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part312 : Refutes moves 0x20002008004000000000000000 0x47ab0d41260806418048900090 :=
  finish #[
0x1a7a87c56cd90ae,73650220907206078,38166901952982,4156,4132,10196107,11904347,9097259,11015315,4892,51564723770140,4188,4172,4196,4175,
5465,42770262496608,12297461,9941039,4170,11916634,10195489,4130,4780,12296870,4144,4143,27643917242,26721133628,10662566,
4166,4148,23424901985,12215355,51581803803614,4166,25104208380,25101448250,11042872,4140,4180,4175,4182,4196,28414448476,
23317427136,35224129188800,4132,4177,5259,21838540931,4186,4353,0xa2b6b91ce6e9383d2,4151,10543147,4131,18082518460,23264605342,13471778,
4140,53286009390322,51609728635955,4186,4182,4600,46084348691305,26016600836,8740928,4196,23598940754,9098206,94702538132410938,25175765298,4186,
4195,4182,0x56d8a76b2bc8ed9df3c8,4173,4164,4169,4188,4183] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part314 : Refutes moves 0x28002000004000000000000000 0x57fb1d48a7088400800a940010 :=
  finish #[
24374006651,21200762014,4163,0x804369364ed9d10ea,4159,27594433301,11436823,23355847255,4169,4183,12690876,25990656565,22810530971,4159,11916236,
44313303401047,11080459,4149,4163,4142,4169,25989812507,25990570961,9113660,4186,4170,4182] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part315 : Refutes moves 0x20002000004000000000000000 0x4eab0d08260804008008900010 :=
  finish #[
4896,37217176883349,4180,23509181167,51595563869344,90193955301069979,8918171,0x183e1f4efafd49b,4188,11042897,4140,4154,11843004,0x4ce87ea76050dcbb935e,23600607928,
4169,53282797671381,11109131,4149,4163,4177,4192,4142,25989399200,4589,4700,11055708,4192,10314322,4154,
4188,4174,25993392610,0xaeaa76bf50c23c3de,4177,0xba5772745489685bc,4163,4147,4159,0x4011a640f36112ae355e,10232776,4169,87893433666085832,4182,9785895,
56510055007387,13045852,26718004379,12305466,25992991998,9114685,4170,4188,4192,4175,54719285363074,0xa8ba7e04d7d237221,21937746330,10731598,4190,
4183,4177,98976258721682779,46256207270963,22582780893,0x18153654da9d2fe,4154,4168,4175,40016328090779,12255519,9864252,9928755,4175,4183,
4601,0xba543f07d49056496,4192,4289,27594801590,12624658,18665345071,4188,0xbbc5fa5054fa92227,54725805290071,4154,87231095608570257,4168,0x31f60d2f3232158bb97f5be,4190,
4183,4174,5275,53281175135392,4173,27591939028,24170242618,4156,0xa8a9bebec230ad55a,4172,4192,10350888,25176904072,4192,98909597646419003,
9957873,48295826264279,4192,4196,4190,4183,48276015522670,24395547611,4159,0x17645a26ca9f3db,23457677408,4139,4147,4170,4163,
4186] (by decide +kernel)

private theorem part313 : Refutes moves 0x20002000004000000000000000 0x46ab0d08260804008008900010 :=
  branch 1 0x20002000004000000000000000 0x46ab0d08260804008008900010 99 0x57fb1d48a7088400800a940010 (by decide +kernel) part314 part315

private theorem part311 : Refutes moves 0x20002000004000000000000000 0x46ab0d00260804008008900010 :=
  branch 1 0x20002000004000000000000000 0x46ab0d00260804008008900010 75 0x47ab0d41260806418048900090 (by decide +kernel) part312 part313

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part317 : Refutes moves 0x20022000000000000000000000 0x44b1c724244444000000000000 :=
  finish #[
12681993,26006954761,10269853,4143,4153,11043997,12681698,80731025757663598,4166,4172,4160,44809906979997,20337115729,4186,4179,
91237755190445003,0xd3d8fea6e3e9103c3,0x5aa41a4ea6a851961499,4156,4160,20025570172,4179,58226901091671,0xc0d36ce9e089cb2f6,24329257012,24328905181,4179,4798,4992,9056844,
4164,4168,4166,5266,11043404,9113672,0xbbb1627597e1da109,4179,43330609525042,4166,4186,4190,4174] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part319 : Refutes moves 0x20002000800000000000000000 0x4cb34544344204025000400100 :=
  finish #[
10268964,56512435815194,25990251094,4160,5178,25092650144,10293318,0x5d2a9146ea657aafa260,4180,4169,4177,19985966128,11477867,53079028838500,0xa915e7045dd9d655a,
4154,4392,0xbbb14ee9c881d555d,4163,4168,23248360704,0x8d6372d5206a2a233,9113675,0x1744eac589d1087,17903252044,4173,4193,13472531,13472914,27591258700,
9908296,4183,25990628413,4889,25178047643,23456117536,8978523,12652593,18631823411,4172,0x17791f2089d643a,9098280,20226437192,4154,4166,
4190,4186] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part322 : Refutes moves 0x20002004000020000000000000 0x47b34520a4c104908110260024 :=
  finish #[
21737501445,53147739878149,37909211395417,4142,13471782,0x19b305dae4da31c,0x86881b3626d161294,44552766202750,11129628,4175,12193883,4138,4168,12624840,11916160,
4151,0xcdc7790520acd943c,4311,25856328375,25115845310,56461842940792,4163,4179,4175,4190,4195,27602813897,9479515,4174,10732382,
5466,22541636757,4144,22540542654,4190,4187,4196,9929682,11502171,4174,12260697,9417569,21827511137,4195,39507770995854,
4166,21116006500,4153,4163,4168,4183] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part323 : Refutes moves 0x20002000000020000000000000 0x44a34524a44104000000240024 :=
  finish #[
8741641,90686553789763944,0x181aa21793a7559,27568837395,9113647,11489495,4148,4193,4172,13882209,4961,13882510,11763756,56464302752828,4124,
25102242064,4138,4156,58232998769505,51564635476461,4136,25194517639,5160,0x16b336a0347d432,4129,10682408,4147,12633534,23582672013,9957427,
4186,4171,21618983303,9461975,21074125305,4168,4193,4188,4179,8742332,97518904266379959,54931090555468,11456994,4156,4160,
4172,0x19b93680453f5bc,28415738724,11055167,22645937600,4140,53199294264768,23289123993,4196,10289657,4163,4183,9462825,5258,49970328134910,
4159,0x18294fe37a37559,4966,17905997147,97862170592023998,12304456,9461839,4164,4140,4196,85299656083219606,11481593,25091399722,5466,0x16b936576168237,
19380813903,4147,4163,4155,4179,27566039736,11879584,24330785853,4195,4142,11055703,46285624177031,4190,4159,95126437509751965,
0x167cd666d2e725b,4126,10310421,27595633202,22794956875,4159,0x46a2f720cbc0210a34fd,4164,4168,53315334332976,21521478714,53191076283433,4169,0x66f9b680ca4a6cafc300,4163,
4147,0x60fa9974b1bc220a5237,4168,48110709999040,21116068736,9113672,5466,11904136,4295,0x57147d838e84548b14fc,4188,4172,4168,11469696,9515314,
9908308,4183,81736271526293701,4154,4195,4190,4186,4174,4166] (by decide +kernel)

private theorem part321 : Refutes moves 0x20002000000020000000000000 0x44a34520a44104000000240024 :=
  branch 1 0x20002000000020000000000000 0x44a34520a44104000000240024 74 0x47b34520a4c104908110260024 (by decide +kernel) part322 part323

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part326 : Refutes moves 0x20006000000000100000000000 0x46a39da4b6403c820000000a0c :=
  finish #[
9504096,47884709667577,11899839,4156,21938459203,4190,4154,44727206044023,5086,94686836487332027,46235687518766,4113,9040047,4152,4166,
4156,11138001,5180,10711718,11513926,4154,9896638,8659836,4168,44706827764291,4151,4159,4171,4163,56582951175104,
42460133569790,4154,23384150694,45020839720286,4177,4171,46374727152605,5064,24221032647,4177,10334792,4159,4174,4169,0x66d20ea76bf14fa9137b,
18406531872,23590191703,4187,4159,4896,27625894352,58192631968001,0x18140e84f94f0ea,11137082,10350673,10289230,4168,4163,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part327 : Refutes moves 0x20002000000000100000000000 0x44a34d84a44024820000000208 :=
  finish #[
4963,24397989312,4192,75099882804777351,27601187989,56530529968908,4131,95052701540021502,4168,4159,4138,11379467,12317661,11083839,22635213979,
0x18ed0694f9d05c0,9928761,4183,36254280938645,41650339049863,4192,21593350737,0x60d1d08f65e14c29f21f,4192,0x18de7417a40928f,4154,48041324610336,4159,4147,4155,
4163,9065627,4973,54894095127405,4168,9424963,49823821170014,84734913766319344,4159,9463036,10350888,4169,4168,4188,0xba81091d91bc1a3d1,
37886370641051,4150,0x18f0b9d48a8337b,4142,44230507013086,49669126878363,4164,25107772364,53173894881572,4188,4168,4173,26016089431,20957434349,4171,
12235643,47867020550923,4171,10330711,4173,4188,51663804036348,45034069029753,11502441,0xa3c8351bc51af043c,36371152368512,4169,4173,4168,4164,
4166,4159,0x1834a49074781dd,21116069019,4168,20160488224,4875,51599958725576,4138,9113687,4180,22701478753,0x18f0a44eb1df320,4173,11404227,
49364914275076,0x50a8fd760d2d41b5d55d,4138,4156,18665006141,9957468,4187,53225360876889,19304108436,4168,56562365231712,47697753666231,9875531,4150,24381518603,
8675895,20226486348,4187,4166,4195,4186,4190,4174] (by decide +kernel)

private theorem part325 : Refutes moves 0x20002000000000100000000000 0x44a30d84a44024820000000208 :=
  branch 1 0x20002000000000100000000000 0x44a30d84a44024820000000208 86 0x46a39da4b6403c820000000a0c (by decide +kernel) part326 part327

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part329 : Refutes moves 0x20002004000000000800000000 0x47b30d20f4d02490c110020001 :=
  finish #[
25990545975,0x16b8885d0bbf376,4168,0x19be00e6e4d949d,12211070,9020278,4151,4161,12276510,13467720,0x6033b59b0b75769c7112,4144,4154,4574,9864345,
4155,0x19b536572aed4fe,17904292829,0xc7c5b0a10b623d3dd,4154,0xc0d9b25b0e823c0d7,4153,4190,4196,46132521641213,23281529605,4182,45033841316250,4153,94734220191175550,
11470170,21124460623,4169,4174,4183] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part330 : Refutes moves 0x20002000000000000800000000 0x44a30504f45024104100000001 :=
  finish #[
13873528,19412713855,4159,21786227556,11515015,20267111464,4159,4163,27591504550,58196231176992,27590366248,4159,4163,42917385860136,4168,
4150,4154,27642389373,43267704189909,20840052058,4791,44916878959263,4169,11079743,4163,4177,40016522909018,36395605144520,4169,0xaed5fb0184b96125c,
4152,10596816,0x14574ee398298fe53d41a9f0bb,4177,11137917,53005411636180,10350655,10289225,4163,4168,4188,0x8052c21591ba1130c,25092494381,0xc1a2c301940afd23a,4161,
0x19b256508c1855b,4136,4169,4972,0xa9da7e845769782be,92020009400820886,10289211,4173,4896,98980102756173146,4183,4896,0xc095a6bf26c856292,4183,48330128299354,
4311,91567775763452782,21073256521,4173,4161,4155,26032173561,8983898,22693904440,4142,4192,4163,21125264424,0x16a936608c18319,4147,
46595824038766,4168,25990951477,39385112900149,4163,19973944076,12632722,18551513470,4160,90250716773630736,4169,4173,4168,11469495,8667934,
4173,0xa949b23ed7c205559,48242444313278,4160,25143771327,23555494589,4173,11497545,4150,4159,11137804,5278,8635355,4159,9081126,
4172,4168,9114393,24405181024,0xcdf422a7cef8b1380,4172,9908296,4183,9114194,21081298056,25192952114,4173,4168,20959822994,9478748,
9908296,4195,0x19b2a7caf96b4fe,4150,4154,4186,4190,4174,4182] (by decide +kernel)

private theorem part328 : Refutes moves 0x20002000000000000000000000 0x44a30500a44024100000000000 :=
  branch 2907 0x20002000000000000800000000 0x44a30500f45024104100000001 74 0x47b30d20f4d02490c110020001 (by decide +kernel) part329 part330

private theorem part324 : Refutes moves 0x20002000000000000000000000 0x44a30500a44024000000000000 :=
  branch 1 0x20002000000000000000000000 0x44a30500a44024000000000000 44 0x44a30d84a44024820000000208 (by decide +kernel) part325 part328

private theorem part320 : Refutes moves 0x20002000000000000000000000 0x44a30500a44004000000000000 :=
  branch 1 0x20002000000000000000000000 0x44a30500a44004000000000000 53 0x44a34520a44104000000240024 (by decide +kernel) part321 part324

private theorem part318 : Refutes moves 0x20002000000000000000000000 0x44a30500244004000000000000 :=
  branch 1 0x20002000000000000000000000 0x44a30500244004000000000000 71 0x4cb34544344204025000400100 (by decide +kernel) part319 part320

private theorem part316 : Refutes moves 0x20002000000000000000000000 0x44a10500244004000000000000 :=
  branch 1 0x20002000000000000000000000 0x44a10500244004000000000000 89 0x44b1c724244444000000000000 (by decide +kernel) part317 part318

private theorem part310 : Refutes moves 0x20002000000000000000000000 0x44a10500240004000000000000 :=
  branch 1 0x20002000000000000000000000 0x44a10500240004000000000000 62 0x46ab0d00260804008008900010 (by decide +kernel) part311 part316

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part334 : Refutes moves 0x20040000808000000000000000 0x47b3e5941e109042500a400901 :=
  finish #[
21201883719,20109456422,11359676,23265063696,9056329,4166,4160,0x17764e57684b31a,23464899218,4168,5468,43423957500676,4166,11510532,4180,
9728986,8696504,4180,0x60a3451470684b9d02b8,22635184200,4171,4149,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part336 : Refutes moves 0x20040000800040000000000000 0x47f1e195128218426028040190 :=
  finish #[
83406706121007869,20110881037,94202773011899545,13480005,5171,51392925782763,20120175755,4169,4151,0x19b6e99de41a49d,9823283,4157,5080,25195312278,11886639,
4144,4163,4154,11093147,9835266,25017455774,26795099196,11509808,4185,4169,4196,4180,5275,9483419,4690,
21082866539,9519185,4195,4169,49402534834923,0x19b31f0a941c2eb,0xa6a9b7062381db49b,4174,4169,49981040452066,4196,39934828725692,25184563404,4174,95437840476070546,
10662952,46081109484892,4187,21032140900,4158,4163,4173,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part338 : Refutes moves 0x20040000800000080000000000 0x4fb0e195128250434008048100 :=
  finish #[
12690781,25989767348,4158,13472923,5469,10249164,9049054,4166,4160,98706964384879546,4177,4169,11093147,40671994028212,20991030413,
4173,0x169c719752fa309,4177,4169,4145,4180,12689788,25116922938,4152,25992217842,12624461,27591577658,11121819,5261,18483115354,
4166,10273842,11509808,4169,4185,4196,12690585,25989338265,4152,95370977387876555,56509197436059,4190,4196,4690,94702523443122860,
4177,22796502362,0xc7ca770688a1df320,4169,22460134546,51252827657358,11490057,11101224,4166,4190,21032140900,4158,4173,4163,4178,
4184] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part339 : Refutes moves 0x20040000800000000000000000 0x47b0e1941280504a4008000100 :=
  finish #[
22467433031,13481115,27592873105,12665630,4143,9032755,4162,4158,4160,42992757151069,56549389173690,11900059,4165,4160,9408785,
5178,47646743303309,11092019,12317851,46530310554875,25907142693,4177,4180,4145,4169,25904329498,74704402214679230,4149,25905902362,0xc105ea8453a9cb293,
21034501255,4887,9457956,25905053790,4157,4166,4160,5277,0xa834627420829f55c,4185,98421741808382348,22760255691,4173,10314322,4154,
4174,4179,4169,4184,23346087260,10249056,27609920667,0x19b6b7c24afd3ce,4169,4177,4180,21074932401,0x19b30494fadf37e,25185613148,43178591645899,
4169,4173,4174,4184,13480790,25990911318,0x66ac1a11280d4b281173,4147,4154,46321366774238,23346164510,4166,9519968,4960,9835154,
45993474871692,4179,4169,4168,98421738352661029,44273154782046,4171,4185,4177,12693592,12640288,4126] (by decide +kernel)

private theorem part337 : Refutes moves 0x20040000800000000000000000 0x47b0e194128050424008000100 :=
  branch 1 0x20040000800000000000000000 0x47b0e194128050424008000100 43 0x4fb0e195128250434008048100 (by decide +kernel) part338 part339

private theorem part335 : Refutes moves 0x20040000800000000000000000 0x47b0e194128010424008000100 :=
  branch 1 0x20040000800000000000000000 0x47b0e194128010424008000100 54 0x47f1e195128218426028040190 (by decide +kernel) part336 part337

private theorem part333 : Refutes moves 0x20040000800000000000000000 0x47b0e194120010424008000100 :=
  branch 1 0x20040000800000000000000000 0x47b0e194120010424008000100 63 0x47b3e5941e109042500a400901 (by decide +kernel) part334 part335

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part341 : Refutes moves 0x20060000000000000000000000 0x46b9e1b483c000000000000000 :=
  finish #[
4689,21680424283,0x169aed66e40d49c,25908331161,4129,4140,46325720056093,4155,25988166430,56508265448213,0x5a2952834a74b635f1c3,4154,92189313052239003,4178,4190,
4166,4195,0xc71834bc26c9d5294,17802572374,4169,9519993,18549953692,4168,4299,48365309899932,4168,4179,27594425201,46653758239194,4150,
23357387931,58197027697521,4168,17735008737,4155,4163,21981295085,17802548080,4168,11124818,4153,4195,4174] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part343 : Refutes moves 0x20040000000020000000000000 0x46a2f1f0820104000010010024 :=
  finish #[
11055877,0x5d40025cea669db454fb,74473142209185021,4159,9818404,4160,22440186324,0x303508ad55110448a29d43d,4187,4196,4168,11854501,0x8039ac849d3292432,4178,12219342,
24423150156,4143,51255563465678,25915379907,48196630954838,4190,10249149,11490237,11128913,4159,11490343,25178907293,22618370097,4133,4187,
4196,11124808,4153,0x18f6d5e374d955d,50018530341357,4164,21116863047,4188,41445843128928,26017768093,4133,52985774331132,25874781025,20235285083,4178,
11124824,4153,9519712,11129628,4159,4166,4196,24252863831,26697245757,42765035623576,4130,4157,11121045,4166,0x57033983b1ea061df492,
10351774,22677918344,87296655667098203,4163,99062000292312012,4159,4187,4166,5466,56506790695516,11124809,4153,4188,19377992576,0xcd95ff4ec7d84b3bd,
17811752282,4188,4153,4300,8696606,0x19b29fc25a944fe,4145,4187,4196,23508001159,98035121055785737,4187,17784156463,4178,4169,
4171,4177,4179] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part345 : Refutes moves 0x20040000004000000000000000 0x46a2a990820820002400900200 :=
  finish #[
21597361211,51616240227674,4182,11100639,0xbb983a579dd3a6361,4143,44226378286138,4178,4169,13480418,23423677790,4154,10351582,11522820,4148,
4169,0xcd95d0a6e0941d2ed,11023507,25923531541,4166,83684818079687529,27626807775,10350673,4164,4169,25178088606,9835665,4140,10351364,0x183ab80e89df4ee,
11022944,25923433056,12305466,4165,9519160,4187,4190,11124809,4160,4195,4188,43093171577509,11924824,12689612,4182,
11084370,4695,36474207150853,10350653,4173,4169,4178,11043424,0x59dd3b9b30688a29c1e2,24356430502,44470335759507,4169,4163,4190,12690670,
12612380,4163,0x1673068b61c231c,4184,0x33693eb3b9b34ed4e2814f1,25010275102,5274,11125534,4153,11014208,0xcda53b01e9d9c243b,9863256,4163,4147,4159,
24119911390,0x19b71b93ea9f08a,4164,13472309,20838728349,12709955,4154,53242290353498,22692676274,4163,0x1836e960e96c35e,53228866150994,11124824,4174,4195,
22788543244,27592881291,4163,0x50653b5b0ba0b641a3ce,4182,9101613,4169,4173,4177,4187,4171] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part347 : Refutes moves 0x20040000000000100000000000 0x46a2a994aa4020820000080000 :=
  finish #[
5280,9483419,4157,9057056,0x2ea14e29f46ea2a0d1143c5,4196,4195,11854681,49723074388825,4169,5061,0x18e2b61afa3c49b,11083846,4178,0xa7c5300f8ae16c5bc,
4155,0xc7601a3520935f0f5,53232068171196,4388,9520283,4196,4178,4166,53232037119027,4188,54812618917213,11084768,50019436651361,10634383,4129,
9879652,11124811,11502449,4166,4151,4174,4159,12297265,51408471585831,48367568397060,90969439210165120,9519168,4178,4166,4979,
12260391,4154,44230580920909,11124795,5272,48370856699034,21116067899,4178,4188,4699,23615423262,4159,23489594142,0x573c1b68ad584d842559,4162,
4487,25108177694,0x60d4d8536b9cea9df181,4178,4184,4188,4164,21116875330,53056799064861,9879738,12689467,0xd3f1faa7d1e41a2b2,4883,10289939,9461817,
4188,98520751782802109,4174,4178,4182,46664384136059,43264432271564,9093202,4169,4177,4171,4173] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part348 : Refutes moves 0x20040000000000000000000000 0x46a2a190824020100000000000 :=
  finish #[
11129789,25110496402,9020349,10268735,4153,10994833,4990,23598588593,22517772357,4178,4177,4990,19498194073,11080574,4163,
4178,11056283,5275,51266084512028,12690194,8660123,4165,4163,4162,4168,22695485730,11432893,11498352,4159,11124830,
4146,4174,4160,20237624478,22520107673,0x1751366083b93c5,4155,4162,47959417435584,10711436,11138016,4150,21982413489,11079743,4177,
4178,4376,0x56c3ab8e0eca0c83e1d2,4159,25204462354,11522926,4169,4196,11125522,11125617,11457677,20143739373,11124824,23549936785,4166,
4150,4159,4174,22695482716,46598225581404,4196,48242444313026,0x183503148a9c440,4195,10555470,4116,4188,94973569453101621,44621465260988,4148,
20237231072,43247135749080,4177,4163,47782714168480,12690104,11120704,21888922566,25989828812,4153,11465883,53229613216541,4151,4159,4174,
21074931978,11056474,9007378,12689466,4160,27592836028,0x27426ca9482e28d7384b1c3,4178,4174,22719394974,37781590090528,4160,0x2ea17c4d95cea7e0d0fd3c5,9461807,4155,
4170,4182,5466,9879934,4155,24128377411,8659044,4487,19379569438,18515620444,4178,4184,4188,88079439159452127,0x177ebb4550ae37e,
4187,4177,4169,4173,11907155] (by decide +kernel)

private theorem part346 : Refutes moves 0x20040000000000000000000000 0x46a2a190824020000000000000 :=
  branch 1 0x20040000000000000000000000 0x46a2a190824020000000000000 44 0x46a2a994aa4020820000080000 (by decide +kernel) part347 part348

private theorem part344 : Refutes moves 0x20040000000000000000000000 0x46a2a190820020000000000000 :=
  branch 1 0x20040000000000000000000000 0x46a2a190820020000000000000 62 0x46a2a990820820002400900200 (by decide +kernel) part345 part346

private theorem part342 : Refutes moves 0x20040000000000000000000000 0x46a2a190820000000000000000 :=
  branch 1 0x20040000000000000000000000 0x46a2a190820000000000000000 53 0x46a2f1f0820104000010010024 (by decide +kernel) part343 part344

private theorem part340 : Refutes moves 0x20040000000000000000000000 0x46a0a190820000000000000000 :=
  branch 1 0x20040000000000000000000000 0x46a0a190820000000000000000 89 0x46b9e1b483c000000000000000 (by decide +kernel) part341 part342

private theorem part332 : Refutes moves 0x20040000000000000000000000 0x46a0a190020000000000000000 :=
  branch 1 0x20040000000000000000000000 0x46a0a190020000000000000000 71 0x47b0e194120010424008000100 (by decide +kernel) part333 part340

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part351 : Refutes moves 0x30000000800000000000000000 0x4f956114140000066000000100 :=
  finish #[
56559992414895,0x1834d58852332c0,4168,12689887,0xc1b5a91fe0d22d2af,8736846,4185,51613792322496,25991336210,0x1834ec97a2fb48b,4155,0xc1a5303f114292430,4157,4163,5468,
51614531293831,0x18f936e0735a235,4150,4175,25857999716,4136,22752166963,46480357307253,4154,4163,53223897781024,4189,4183,25195291424,25023537448,
4175,4882,25989477436,4175,0x284a0db4e74f069088552f6,17894781603,4143,20394668245,4179,4189,9876540,9941492,4187,25889993568,36458621846262,
4153,11923948,4154,10674976,0xba59b28ba0d16f313,4154,9925108,4183,9097307,4180,4166,4190,4174,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part353 : Refutes moves 0x30000040000000000000000000 0x4f8e2b0a800198000020000000 :=
  finish #[
35659499545946,10920892,12304752,13034038,4121,4141,26695578685,4122,5466,42770295616647,4122,27594441572,4136,4140,4162,
5165,23382438967,49467983520524,4141,4161,0x19b2ef20c35b55c,4140,4149,11908442,25991426527,19296060860,11083855,4157,11924827,25882260421,
0x66dc14140ec9141065c0,11083841,4184,11514422,52953642303878,4157,0x83f41d0520fcd949b,13472531,54879675048715,4145,4157,25059521775,35967064203543,11907129,4158,
4149,44674868724512,11486061,4162,4139,4131,4155,4163,4575,11887770,4162,5466,11515035,4162,11515226,
17567605914,9461807,4161,4158,0x2d366c95e8f87420ca8a293,53228691625305,11907463,4158,56506791862449,22701474780,8736835,4189,4182,4184,11416922,
13472612,23382566234,11907126,27594441484,4136,4173,11776280,0x63793e8e084a6dad849c,4159,0x93e6760b66dbbc49c,4132,73662249062216636,4140,4964,94983983656596444,
8736829,9101400,4189,98953214976254127,41645463995356,4159,4163,4175,4183] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part355 : Refutes moves 0x30100000000000000000000000 0x4f86b9c0800000000000000000 :=
  finish #[
11793563,25193628923,41202958578927,4158,4150,0x19b82917c2e8432,8699967,5058,0x286e6dd3b6b650da0a3908f,4156,10671040,51581169808730,53211390256188,11874366,4159,
0x16a6d691fa341df,4169,4157,83016330553630862,0xb5a9ad1e4af23f560,4169,0xc6f82137d1faef3dc,37853555172698,4177,0x95545ad6d7baff23a,4151,4158,56511797113038,4178,4182,
12689867,13087708,0xc1a9bf061ad8fd43d,4152,56616479305909,9064502,4162,10745178,10699439,4151,9101379,5084,46593267937568,9896010,49397311980988,
54895860359550,4127,27644765041,75878834462086299,11907108,9101356,24380371630,20301987894,4182,4190,4171,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part357 : Refutes moves 0x30000000010000000000000000 0x4f943540a82800000019800000 :=
  finish #[
13460924,26788287526,9478201,22812144095,4149,21201925463,23424906196,0x3359ddb5b4debe0521df320,4189,4159,0x21bca14da6bf3645695649a,0x9d55af368b5b5b55a,8699966,4172,4179,
5084,11924349,4162,0x167936ce8a9f248,4184,4875,25913033687,0x60c3a69b4d15af9da1d3,8736840,4189,25983038528,9098586,4184,49876307472686,4162,
4166,4182,51235940262848,0xd3b8e8cfceaa9848b,0xb3f8e88b5a735b0fd,9895971,4310,9945390,4179,4182,4190,8737264,98210530761707893,4151,4385,
27591635631,9462256,4185,4158,21862269701,4183,4179,4789,9462062,54651364000046,0x16b411da98a04fc,4171,4177,4173,21200323548,
21912551715,4171,4183,10744507,4162,4168,4169,4175,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part359 : Refutes moves 0x30000000000200000000000000 0x4f9423c0815050000000006600 :=
  finish #[
47829378527831,9957873,4187,10695545,48366014121204,4163,39675533702189,11502747,11867000,20293529672,4162,4178,4166,4890,24378781893,
4166,4597,11530741,4166,9461968,36611520721405,4190,4783,5076,0x1836544832f81bc,21904965719,4168,4169,4180,4187,
41511901385451,0xa6e2e0d69a0c1049a,4139,37388070433730,0x18140e96d89d55c,11079738,4178,9102010,22810587834,4178,4169,49659346526797,39692640821551,8708171,10695636,
4588,24380044043,4157,9097283,47954410730461,11137516,4171,36651037864239,4187,4183,4190,4182,11903936,10195931,22517772942,
4178,4170,18482385668,11874766,4159,4132,4794,44878593389133,4183,4169,19378004271,46373291864722,11465576,4183,4190,
11907158,4140,4149,4185] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part360 : Refutes moves 0x30000000000000000000000000 0x4f942140810200000000000000 :=
  finish #[
22702265689,0x19b4281d6047365,4175,11080284,49728963166791,12710844,9895984,9896331,51424920425317,4178,9101400,4175,4183,27591635631,56505901888672,
21863408409,4164,4185,0x53acd983ebd20d16f312,52933376157020,20262011860,4150,24377934804,4163,4157,9097417,4172,4168,53228009325506,22634386587,
8708694,4175,4178,53226283316081,11437211,9097414,4172,17804161782,18557526881,4159,0x50db5b5cf070ed9df1ec,4168,4189,4179,4875,
9097974,4166,24269780114,10314897,4159,0xc0644e76e0d1da120,8736840,4189,98534281427923444,39110191391309,48105865434173,4185,11530932,20301987894,4179,
4175,4187,4190,4183,11124822] (by decide +kernel)

private theorem part358 : Refutes moves 0x30000000000000000000000000 0x4f942140810000000000000000 :=
  branch 1 0x30000000000000000000000000 0x4f942140810000000000000000 57 0x4f9423c0815050000000006600 (by decide +kernel) part359 part360

private theorem part356 : Refutes moves 0x30000000000000000000000000 0x4f942140800000000000000000 :=
  branch 1 0x30000000000000000000000000 0x4f942140800000000000000000 64 0x4f943540a82800000019800000 (by decide +kernel) part357 part358

private theorem part354 : Refutes moves 0x30000000000000000000000000 0x4f842140800000000000000000 :=
  branch 1 0x30000000000000000000000000 0x4f842140800000000000000000 92 0x4f86b9c0800000000000000000 (by decide +kernel) part355 part356

private theorem part352 : Refutes moves 0x30000000000000000000000000 0x4f842100800000000000000000 :=
  branch 1 0x30000000000000000000000000 0x4f842100800000000000000000 78 0x4f8e2b0a800198000020000000 (by decide +kernel) part353 part354

private theorem part350 : Refutes moves 0x30000000000000000000000000 0x4f842100000000000000000000 :=
  branch 1 0x30000000000000000000000000 0x4f842100000000000000000000 71 0x4f956114140000066000000100 (by decide +kernel) part351 part352

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part364 : Refutes moves 0x20100008004000000000000000 0x5dc72961820c42422100900880 :=
  finish #[
41052351075484,12305466,12305466,20881519674,0x181cef26cc1b430,4139,4183,4159,4175,22575567503,12305446,27569607738,10232072,4134,24155496902,
10596377,4193,4180,4780,0x5d3a839b3074264db48d,0xa730ce6e66e283491,22518940830,4152,4868,0x14e737236a2b83aa0da9b5c230,4159,9805921,4169,4157,4141,
4149,0xa0e6725de6f95a35c,0x177823a03cdb55d,0x19bea0d0735d55c,4178,0x9b69b8ef14e84d491,4180,4175,25906258575,27608445882,10544188,51599965021223,4165,9543733,4178,
25871901950,44412902167183,13471778,0x9c236d4f66dcd949e,0x18185566ca27304,4156,4132,54880514831505,9925978,20327855450,9564208,4189,4183,0xb386965591c84d55b,0x99d9b28cd1d29b198,
51594848818528,47971633321116,19563401302,4183,4189,4175,4180,4193,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part365 : Refutes moves 0x20100008000000000000000000 0x5dc72941804442402000100000 :=
  finish #[
4780,4283,17669931988,4141,4157,25193321438,51595820778848,25192145959,19546632872,4180,4178,4189,4187,4861,94456146677453885,
5265,0x183736d4188e49a,4157,10211373,4159,5179,91921276038398905,4180,4193,58197033591966,23480877760,11530331,9876352,4178,4166,
4182,11805837,0x1672889dd2e019b,4175,36515234301086,4180,4984,18483180498,11129720,4187,4180,48089634615501,4178,4166,79566202868585402,
10211990,4861,12686302,4159,9785918,4136,4148,4156,49514750420312,90267387211924419,4180,4193,0x16b47090fcd9491,11842229,4276,
9785524,4144,4148,10696026,5068,22003565914,4157,4163,42916563760476,4148,4162,4156,4984,9876344,4178,
4182,11907142,4149,4140] (by decide +kernel)

private theorem part363 : Refutes moves 0x20100008000000000000000000 0x5dc72941800442402000100000 :=
  branch 1 0x20100008000000000000000000 0x5dc72941800442402000100000 62 0x5dc72961820c42422100900880 (by decide +kernel) part364 part365

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part367 : Refutes moves 0x28000008000000000000000000 0x57d5a54110000a500000100000 :=
  finish #[
23346590592,24387138400,4154,46085079658782,0x9a55c0844af359353,84569338221212420,11878470,10268745,4153,0x57fc6f9ae58cea9df292,4179,11908442,92098829181907509,4163,13456064,
48230060732900,4150,0x174e8fd0884e43c,4185,95113033967072606,4189,43070637412960,4172,4182,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part369 : Refutes moves 0x20000008800000000000000000 0x5c9561c7180002424000111100 :=
  finish #[
13485003,35656076551516,21704815965,4150,11511132,13484621,11423798,4172,4180,21622538903,46207920448151,4177,87062208522212187,0xcdc9b6b5e03b417754f44da9b092,4166,
10273566,4149,4144,4311,97589306740413005,94620556623963582,4190,4180,4192,4187,51252333245114,4306,10351186,4193,22776623762,
4166,4704,0x19b8ec4ef91a1f4,4187,45999247438398,20230030684,5469,0x19baa0c43cdb296,9876829,4158,4154,4146,4150,4550,27560064141,
13034846,13083998,11022360,25025179708,4183,4193,5086,0xbb50090753a97b487,4179,20260823838,12219067,25024770747,9564230,4183,4193,
9113691,4180,4192,4190,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part371 : Refutes moves 0x20000008010000000000000000 0x5e957141882022400009100200 :=
  finish #[
11907661,24388825976,24388825960,0xc1c5eed6caf29d3db,4152,4161,4166,19381204103,11129328,4154,41699478709212,4183,4178,56460191966049,10274042,
4144,51584413069579,0xa0e6b6e98260b137e,4172,4178,44754224600113,10744604,10351296,10698834,4169,0x16b65ed1a0b14ee,21000205458,20118905920,9113665,0xc1f502d6d4da34237,
4175,0x18f27682b11c43b,4183,4189,4190,4187,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part373 : Refutes moves 0x20000008000200000000000000 0x5cb521c1851042408000102404 :=
  finish #[
56577047245558,11908150,11498460,4166,4158,10351580,5076,24320537944,4183,10273748,4154,4159,4193,10351364,5469,
19270907224,4178,27609543264,5468,23357408414,4193,4139,49946320368481,12304446,4152,4182,0x16a69f20d9cc23a,53052740588285,53052739322941,4182,
20881851550,20882314298,9834593,4140,4152,4768,11424352,9113673,4178,4180,4172,8634938,40912469800284,4148,0x94b80c26c4e9cc3cb,
11907130,4892,8712795,4178,17685926859,95047752889659962,4183,43419765683264,43334066418536,4177,0x90e694a50b797b493,4170,4178,4190,4182,
58233003717070,56550199681801,12304458,10994427,90376514550216030,11464759,0xb5b37a8566da94380,4180,4166,51495276463246,25201652800,49364975072512,27610051323,11915334,4151,
8725468,4180,4183,0xadb9aced429283423,9941488,20359877392,4180,4166,4170,4178,19545809504,10978045,11129128,10670166,77944882234364112,
4169,97571061710951482,44754281812381,4183,4190,4180,4193,4192,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part375 : Refutes moves 0x20020008000004000000000000 0x5c956d65816223c00402900800 :=
  finish #[
4694,4699,0x1744a6ce396f495,11531121,56473275798376,4172,56506076492268,4193,42899619688952,4187,4183,4166,4190] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part376 : Refutes moves 0x20000008000004000000000000 0x5c972161810222c00002100000 :=
  finish #[
11023709,0xa0e9ba568bda7c48a,9806101,51611508945769,4178,4151,4165,4311,10350807,4178,4193,13467883,27585650923,4163,21807084072,
21597360209,40084654834344,10977952,23600633180,13471823,53130568414174,19589363034,4189,4183,4509,19565356378,4156,11445083,4129,4137,
4177,4169,4892,46681723040040,4178,17903993597,13472223,11130107,4154,40704509064538,87199421583701338,4193,21954540292,4187,9113687,
4178,4190,4182,4180,35412384728123,9552637,11379641,4169,4177,4487,0xcdd27c2394a2ff2fd,4166,46118604923739,8741760,4190,
4193,4182,20361785725,9114481,4180,11022991,51420686083420,4154,4987,23306642394,4129,4169,39686152852034,4182,17290097318,
19589346649,4169,18666205688,10309718,4189,4193,4178,4861,11404029,27574427919,12318044,25224877110,4180,4178,4179,
4159,19296502848,4596,0x19b6a59782ff23e,4159,4183,4166,35400925078572,23307039111,21661721055,4187,4163,11444632,23307846324,0xc6e38f3651f83c499,
11522115,4156,4172,40655573574603,56505287164590,22005203159,19565368047,4177,4169,4180,44961054077991,0x1776b9c830b13c3,4182,37299908612510,10335194,
4169,4700,8741468,4187,4182,17903211084,4163,4189,4178,4183,11907169,4140,4158] (by decide +kernel)

private theorem part374 : Refutes moves 0x20000008000000000000000000 0x5c952141810202400000100000 :=
  branch 2716 0x20000008000004000000000000 0x5c952161810222c00002100000 89 0x5c956d65816223c00402900800 (by decide +kernel) part375 part376

private theorem part372 : Refutes moves 0x20000008000000000000000000 0x5c952141810002400000100000 :=
  branch 1 0x20000008000000000000000000 0x5c952141810002400000100000 57 0x5cb521c1851042408000102404 (by decide +kernel) part373 part374

private theorem part370 : Refutes moves 0x20000008000000000000000000 0x5c952141800002400000100000 :=
  branch 1 0x20000008000000000000000000 0x5c952141800002400000100000 64 0x5e957141882022400009100200 (by decide +kernel) part371 part372

private theorem part368 : Refutes moves 0x20000008000000000000000000 0x5c952141000002400000100000 :=
  branch 1 0x20000008000000000000000000 0x5c952141000002400000100000 71 0x5c9561c7180002424000111100 (by decide +kernel) part369 part370

private theorem part366 : Refutes moves 0x20000008000000000000000000 0x54952141000002400000100000 :=
  branch 1 0x20000008000000000000000000 0x54952141000002400000100000 99 0x57d5a54110000a500000100000 (by decide +kernel) part367 part368

private theorem part362 : Refutes moves 0x20000008000000000000000000 0x54852141000002400000100000 :=
  branch 1 0x20000008000000000000000000 0x54852141000002400000100000 92 0x5dc72941800442402000100000 (by decide +kernel) part363 part366

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part379 : Refutes moves 0x20000000c00000000000000000 0x5494e10f38000002d0000001e0 :=
  finish #[
98638280896778679,44275429605946,41132307305423,9957442,4174,4306,20143317769,20141175561,10555432,4571,0x9362b4cf0b08b13d7,11079756,4149,91561024834315422,4179,
4192,4184,0x469bbc0384ed3b1a5170,12641117,9957419,12690878,0xc0ea7a7060d2fb35d,4179,25891116093,53024117818418,4156,4174,53277645084094,22702298255,4150,
4157,4184,20950602298,10228282,12641125,4139,0x9c1522ef172aed23a,4156,4172,51238300263582,4608,0x63741a47eec458a341e2,22701413532,90681658334762044,8708156,
4177,4184,4175,4174,4180,54968841200170,12689991,20989867357,4179,4178,0x1834bd1db22855d,11452999,4679,12235295,20654612923,
25201639501,4133,0xb3c9b6ef1141b9490,4140,4172,4185,9958153,20989866941,0x4e31b99bf4f59e28848d,10698782,4145,0x168ad7cbfa3f2bb,9527362,4174,4180,
12677973,53223463878840,10272805,11850317,11490163,4161,4177,44281332826320,25989870162,4174,4178,9835662,12689996,4138,21074932891,
4185,19463533723,4174,25112200350,10351666,4178,12641432,24423150443,43088597823545,4180,0x19b6845489cb0b8,44281331650773,4180,5263,0x1a7a88a0b8374f5,
4157,5263,28433281699,10272829,17886474288,4179,4773,0x19b71ea0741c4fe,4180,44573390586619,4174,9564748,40085074342476,4174,8740946,
4195,4187,4190,4192,4184,4189,4193] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part381 : Refutes moves 0x28000000400000000000000000 0x57d5a12a888000029400000020 :=
  finish #[
10229182,0xad829136d4c906110,0xadd5b14f4e0af5237,4180,4164,4882,46492493496615,11907137,4149,0x4a6c0e382a459f359432,24220636124,4157,24403142080,4179,4379,
12301362,17834905668,4180,4174,4953,22760174433,4148,4684,11907851,4185,4149,37873158095415,25907487998,87048825333777341,9834557,
43071417172032,4180,23354958389,49567583098014,22518543505,10272803,4149,18558723224,4153,8733261,48276137755322,4177,4187,10289453,10314021,
21158031573,4168,4174,4178,4179,4189] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part383 : Refutes moves 0x20080000400000000000000000 0x5df5a34a980002809004000020 :=
  finish #[
56562305254044,20883514606,98428561133454278,0x19bf0753e1cc228,0x5a2ae026e7313e4d6292,12305149,4165,4182,4152,39814484571480,4131,4149,4185,21081297761,46473033650770,
4185,4178,4861,0x86a4f8d7d703bc3cf,9113666,53281874928569,53284391552349,4144,9516071,4165,4883,4990,36497879069266,4179,4173,
4178,4193,84032926419383065,51235884740914,0x9527771f458a2a2f6,18667401995,10350681,4179,11124833,4160,4153] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part384 : Refutes moves 0x20000000400000000000000000 0x5c8ca10a880000009000000020 :=
  finish #[
4684,53227735319209,0x89c83472e0c11f2f6,4178,4180,11043579,27578061563,4641,12305367,9834562,4180,4172,10994434,24422700177,11907148,
4149,4674,0x4a6b38778bd4e0a99558,4156,20883547281,0x1670b6141af549b,11907132,4149,77557770723091219,4189,4193,4185,22518542642,4795,94625315448513095,
9552286,4184,4190,4193,12694589,25202098574,4184,0xbbc696bf548c1a43a,24388419681,4160,4174,46237372486814,53213262111613,11051996,4156,
23517570195,28450076094,4137,0xc7da7ad08af29949c,4164,23582671627,4147,91765728657928986,4180,4190,4189,24388408165,53004595954080,11052188,0xb5b364418e8051320,
4190,4185,4189,4875,21879415535,9114400,4192,21158031575,4168,4189,4402,4306,10330973,5179,51237316399707,
9564246,4192,4193,11124829,4146,4174,4188,0xa116b70691a23f2f7,91911464530342665,0x4efc6e1168b97e29c22f,4146,4139,87479490394784923,13083217,4145,
0x575c1a450ed5df9685be,4159,94866761423103021,4174,4585,22750204885,9101390,4185,4177,0xb3e5d68e53e29f431,49759179326127,49829634818498,0x2525ddb3e6a08e57da9f226,4177,9896024,
4155,9896640,24386396657,4177,4189,9929205,4182,4190,4175,4179] (by decide +kernel)

private theorem part382 : Refutes moves 0x20000000400000000000000000 0x5c84a10a880000009000000020 :=
  branch 1 0x20000000400000000000000000 0x5c84a10a880000009000000020 91 0x5df5a34a980002809004000020 (by decide +kernel) part383 part384

private theorem part380 : Refutes moves 0x20000000400000000000000000 0x5484a10a880000009000000020 :=
  branch 1 0x20000000400000000000000000 0x5484a10a880000009000000020 99 0x57d5a12a888000029400000020 (by decide +kernel) part381 part382

private theorem part378 : Refutes moves 0x20000000400000000000000000 0x5484a10a080000009000000020 :=
  branch 1 0x20000000400000000000000000 0x5484a10a080000009000000020 71 0x5494e10f38000002d0000001e0 (by decide +kernel) part379 part380

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part387 : Refutes moves 0x20000400820000000000000000 0x5ef469ac50d801024065080184 :=
  finish #[
5469,0x19b90263a41f11c,4165,17294013691,12711163,4165,54881312494752,4174,4180,5259,24399164245,4168,0x1764d22052284ee,4145,12698587,
4140,11355081,27617411656,26014881114,10674220,4145,25119314885,27618722454,0x9c747ee959da3330e,4187,4168,5168,56563144516659,12636227,4140,
4162,4174,56544429491336,13067227,0x183ecee6d90135e,11399234,4150,0xcdb51b0720fb4d3c9,54808380265404,52938119004935,26032525698,4168,0x16764060c09110a,9744428,4138,
10272822,4169,0x2d2108cd9688b7e0b913487,5469,90832244130788800,10272852,4154,13882622,9835474,21781135842,4162,4180,52937346495735,9552736,4180,
8740942,4187,4192,4183,4184] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part388 : Refutes moves 0x20000000820000000000000000 0x54946d2c504800024024000104 :=
  finish #[
44677176861227,47925067224303,4185,0xa0a4ed35c14cdc43d,0xa7683471a6e1b955e,27619992815,4133,4193,56561610920519,4159,4189,21765132666,12711258,4143,52939059352311,
0xa7675669604af449b,4163,12305854,13091901,25992228891,4133,11515228,27594453272,4144,11481956,4130,4146,4162,4154,49805106132016,
5277,24152547921,21563417169,4133,4145,12689986,4138,25090651092,0xcd96b905549299238,4143,4185,4163,37065787614552,13472925,41256805397639,
4172,0x63d2ec4230360e11137c,4163,4169,52953936393373,4307,54911569098077,4193,4183,4189,4190,4184,27592741423,88780053889577726,4163,
44281332871569,17800946272,4175,4177,25992991799,8684704,4175,0x168ae8850c1a235,4679,42503604572942,10670370,4156,25989361748,4142,4162,
10351190,0x26aa0d4095be76c270b14fb,4180,4184,25108591386,0xcd938277cb58b149e,4180,0x19b28d0b78b149b,0x19be6816e11676aefe0d4d95be,10731826,20327166040,4183,4187,4195,4190,
4174] (by decide +kernel)

private theorem part386 : Refutes moves 0x20000000820000000000000000 0x5494692c504800024024000104 :=
  branch 1 0x20000000820000000000000000 0x5494692c504800024024000104 82 0x5ef469ac50d801024065080184 (by decide +kernel) part387 part388

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part390 : Refutes moves 0x20020000020000000000000000 0x5494692cd04000024024004000 :=
  finish #[
44282918634025,54933664608738,4160,13472337,10290428,27591992560,4138,4143,4183,24130720802,47750652982222,4162,20990199130,4183,5074,
10088680,4124,12698970,4140,0x1814a1a0c2282f6,9506865,0x21a91141f81b1ba3d1d055d,87483127594124140,4159,9929205,4190,4183,4175,4195,4674,
12301658,23482822744,10310215,0xb4d9b2284240b1237,4180,4172,9072843,10351185,4189,22785282508,26703245970,0x19b210d1729c4fc,10252345,4193,23557948050,
11502365,0xcdd430a717f91c307,9912401,4187,4183,48091103081032,0x66cbab3be5ad4e0b122e,4172,9892146,38228356231965,4183,4187,4178,4190,4195,
4174] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part392 : Refutes moves 0x20000000020020000000000000 0x54866928d04904020024000024 :=
  finish #[
12625242,49395800696153,0x8de82b3659e213559,4160,4136,5466,13472311,27592032469,4184,4189,4183,0x19b4e851fcd9498,58231229125978,44449609867831,4162,
4136,18627793594,0xae89b61326c9df251,4184,4183,9843255,56511738802660,4169,4297,9843255,9113666,4180,4170,4174,5360,
25824011513,25823999014,4132,4162,13038938,11416922,4162,54723408139516,0x1764a65762fc430,11027316,4136,41251157145024,4193,4175,4184,
4178,10584832,54895204811644,13471811,9863650,23399351357,4150,9101520,4189,0xa719b7364b0bbc23a,49618426410141,4154,5158,0x1676d710f471429,9101400,
4189,9929205,4163,4190,4175,4183,48090791032156,23481237807,4187,51429763379846,54858344321494,11518656,9101378,4175,4588,
54684161430200,4175,9892041,9957872,4183,4187,4190,4178,90477099206631913,26701812699,25120584752,51441052104028,4193,4162,95048951451554867,
4178,20882358676,23555937043,4178,20301988143,4187,4183,4190,53285188026772,10309938,4178,91711799956861903,10969496,0x19b29f488af349d,4170,
4178,4303,43244877989210,4190,4183,11124827,4153,4188,4174,4195] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part394 : Refutes moves 0x20000000020000100000000000 0x5496690cd04020820024800000 :=
  finish #[
13481110,56540412084725,4183,0x8040e2d123d9784fb,26805834720,4154,23288636764,0x1756bee6d9b62f7,0x59dc7b15d36d6c1784f1,4175,4195,0xa8d5b1069dabb64fc,4139,4159,4178,
54889725685893,25117754327,4145,5065,12210743,4162,4132,9912535,4183,12239256,9532073,25067909907,4150,4163,53227127371200,
36667411210833,4190,4183,4178,4184,51496835495067,5270,25988203392,4172,4175,25989870631,0x63c2ff35c1382a0b13bf,4180,4184,11125502,
10314336,4189,77944573875512380,4177,46121206059204,49552079675857,4127,4680,22659937212,4168,4193,10183240,0x19b66d916c074f5,4168,12611780,
27611177156,13082820,54846954336960,4162,10252324,11124833,4160,4146,4685,11502449,4151,18642223985,78191157234197436,9912416,4187,
4183,11080480,22809351033,4172,9114096,44911325344050,4183,4187,4178,4190,4195,4174] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part395 : Refutes moves 0x20000000020000000000000000 0x54862908d04020100024000000 :=
  finish #[
4777,10289735,13471831,13472327,43005996037272,4184,4174,42678608564602,20858393736,10646678,9753664,4148,4144,9094490,0xb5f09136450963379,
4162,4170,12689486,44668369605592,27586032183,10253467,4144,0x17761326c9df305,4183,27594433105,41283931018395,4180,4170,4174,4184,
4182,41257696228491,0x18145860e3b2224,4145,58264848655517,4132,24346834267,12305754,4142,46718475845804,5466,0x167ea1087117426,4175,4193,4184,
4178,5466,11056285,46495942964377,9101379,4175,56512420627419,27594048058,37754585886992,4154,9895978,5466,78187259128296095,42987188323674,4163,
4175,4597,9930074,4178,0x31f5028ae9b2158ba11f3db,4193,4184,4189,4190,4183,0x5d3b5940ace4aa9c25c0,13472925,42924138714042,4168,4162,
0xcd840aec66c8ae1d6,4177,4675,20955845496,4162,42921614590365,4187,0xb483850691b4d9228,97649682478970104,4150,18565493435,9957872,4183,4187,4178,
4190,88924038128718511,23396540623,4177,9494728,40872127022528,11137488,4178,10674868,21039341982,4183,4187,4189,0x168aefcdec1c423,22584488896,
4193,26006507716,10695240,9113697,4170,23482823827,41512932459376,4187,4183,4182,4190,0xcdb0573651f9bd292,4869,27591275269,4193,
27590857112,4170,4178,4399,0xb5f37ad366c9cc55c,51322641290191,46716814168556,4193,4178,88084309274460823,41516976132510,4178,88560476444115639,4182,4187,
4190,11124823,4153,4188,4174,11907171] (by decide +kernel)

private theorem part393 : Refutes moves 0x20000000020000000000000000 0x54862908d04020000024000000 :=
  branch 1 0x20000000020000000000000000 0x54862908d04020000024000000 44 0x5496690cd04020820024800000 (by decide +kernel) part394 part395

private theorem part391 : Refutes moves 0x20000000020000000000000000 0x54862908d04000000024000000 :=
  branch 1 0x20000000020000000000000000 0x54862908d04000000024000000 53 0x54866928d04904020024000024 (by decide +kernel) part392 part393

private theorem part389 : Refutes moves 0x20000000020000000000000000 0x54842908d04000000024000000 :=
  branch 1 0x20000000020000000000000000 0x54842908d04000000024000000 89 0x5494692cd04000024024004000 (by decide +kernel) part390 part391

private theorem part385 : Refutes moves 0x20000000000000000000000000 0x54842108400000000000000000 :=
  branch 2525 0x20000000020000000000000000 0x54842908504000000024000000 71 0x5494692c504800024024000104 (by decide +kernel) part386 part389

private theorem part377 : Refutes moves 0x20000000000000000000000000 0x54842108000000000000000000 :=
  branch 1 0x20000000000000000000000000 0x54842108000000000000000000 70 0x5484a10a080000009000000020 (by decide +kernel) part378 part385

private theorem part361 : Refutes moves 0x20000000000000000000000000 0x54842100000000000000000000 :=
  branch 1 0x20000000000000000000000000 0x54842100000000000000000000 75 0x54852141000002400000100000 (by decide +kernel) part362 part377

private theorem part349 : Refutes moves 0x20000000000000000000000000 0x44842100000000000000000000 :=
  branch 1 0x20000000000000000000000000 0x44842100000000000000000000 100 0x4f842100000000000000000000 (by decide +kernel) part350 part361

private theorem part331 : Refutes moves 0x20000000000000000000000000 0x44802100000000000000000000 :=
  branch 1 0x20000000000000000000000000 0x44802100000000000000000000 90 0x46a0a190020000000000000000 (by decide +kernel) part332 part349

private theorem part309 : Refutes moves 0x20000000000000000000000000 0x44800100000000000000000000 :=
  branch 1 0x20000000000000000000000000 0x44800100000000000000000000 85 0x44a10500240004000000000000 (by decide +kernel) part310 part331

private theorem part293 : Refutes moves 0x20000000000000000000000000 0x44800000000000000000000000 :=
  branch 1 0x20000000000000000000000000 0x44800000000000000000000000 80 0x44900820000900000800000000 (by decide +kernel) part294 part309

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part400 : Refutes moves 0xa000900000000000000000000 0x25fdc03328b450124800000000 :=
  finish #[
8889093,22461805338,4170,5265,79387254902617233,10175524,26822641087,24992412831,4198,12312658,4167,4160,0xd3d11aefa082d628b,0x16bf4fd4fb4d491,9453670,
4162,4180,5265,0xc108323c04390411a,4162,5055,19890455896,18927337538,41288630662106,4170,4178,9454456,11891074,37836509053317,9445423,
4178,4349,4552,58241655021914,4149,11464778,0x182cb60812ff55c,4151,0xd3f69ad594f904359,28441306354,9454052,4174,41220941291895,4151,4160,
27557565305,27558286286,4126,24993961103,18364003184,4142,9015576,4164,4160,9446551,35238078706148,11120742,11100209,4161,4180,
4196,4175,4166] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part401 : Refutes moves 0xa000100000000000000000000 0x24fdc80220a050000800000000 :=
  finish #[
99065415733187552,51474521396565,4147,19340010848,77413272380400988,4149,0x2b5ddbcdf836101a335e357,4170,0x18241060629d55a,11896057,27593663449,18509166012,4147,10641478,9084987,
4175,4173,0x9b89bb064afcd94fc,25904685250,4163,4383,9454938,4162,9454938,56506773497084,4161,4147,4180,5174,13472822,
56505873450038,4164,4170,17687037182,4129,26821767557,23275083094,0x5dfbab9b2ef99da963c8,4161,4147,4180,25061856598,11100956,11501633,4151,
25229628470,84552523339535413,0x177e0f020a941e4,4138,11464788,23549965084,4151,4142,4198,4383,27628770347,83547407593493846,4161,0x183cd781c9042a7,4156,
4162,24973952036,53087978270910,4166,5362,23356998609,4151,11531204,4992,0x5d0b5d11f37637b58489,22584827981,4177,4164,4143,4198,
56544531837708,4483,19347588027,4152,5175,17659843533,41137316454538,23482826793,4174,4198,9826678,0x181c569af41b11a,4137,24255763904,9843062,
0x66f28b9ba898b1cd91ba,0x5db4dda7b364b1bb511a,4138,4149,0xb3a9bb37a6ccdf437,26780689375,11464745,11501606,4166,4198,0x11d3375132ef9b2ce97c0aa48f,4163,4171,4175,17247224980,
99046657747108629,4155,11129796,22792904857,4151,17859682362,4180,4181,4185,4178] (by decide +kernel)

private theorem part399 : Refutes moves 0xa000100000000000000000000 0x24fdc00220a050000800000000 :=
  branch 1 0xa000100000000000000000000 0x24fdc00220a050000800000000 83 0x25fdc03328b450124800000000 (by decide +kernel) part400 part401

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part404 : Refutes moves 0x8002900000000000000000000 0x37bcd27a893045734800000000 :=
  finish #[
12284885,24330888245,4127,5183,25958237032,9843077,4162,4166,5279,11523220,4161,20899947294,11523220,4153,48332553187521,
4184,4198,4185,4164,25195291013,25992180600,11137508,4170,4178,39333529186668,5275,9396596,9384816,20061446804,8982610,
4158,4166,4982,0x1a7eee845824556,0x86a2aebf54ca9f151,4178,4198,11457382,4124,4132,4185,4148,0x60d1376b2bc93fbb4369,19894104855,0x1a7b1fd7bbb710e,
4190,5279,21603414363,4198,36096089764920,4152,4132,12271861,41220742435784,4178,25136927504,8655912,12283972,25990620223,42709693895646,
9453604,4159,4168,4165,4162,4147,4138] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part405 : Refutes moves 0x8000900000000000000000000 0x27bce032083040124800000000 :=
  finish #[
4258,53229401453219,4175,4595,28450485089,47821236728663,72209764067980160,4154,4166,4174,38814721086514,21763875206,12660773,4145,0x1696eec3d2992fe,
19370390400,10268742,4148,4153,20796425371,0x9a46a14f5ddae51c1,4164,0x63d14076835972a8d5be,39659175444693,4184,4190,46204705603973,98597990017982857,4185,4161,
4309,9265507,0xc1a77ccf14cae53bf,4164,4309,23375302869,9887793,0xd3d8365d976af511a,4164,4161,4196,12690263,5183,51652302373719,4133,
4145,23288657246,46688151814600,9356638,4132,4126,11072751,44677174440278,4143,9482289,4166,47662437139611,4684,46683898454507,4161,
8732753,4185,4309,13083581,10269068,4184,54883753178056,11432332,46679947408437,4159,4166,84807209892267151,4185,21913399361,4168,
4174,4175,4198,4180] (by decide +kernel)

private theorem part403 : Refutes moves 0x8000900000000000000000000 0x27bcc032083040124800000000 :=
  branch 1 0x8000900000000000000000000 0x27bcc032083040124800000000 85 0x37bcd27a893045734800000000 (by decide +kernel) part404 part405

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part407 : Refutes moves 0x48000100000000000000000000 0x37b88a82002640000800000000 :=
  finish #[
12641111,5274,25907442748,13456120,25980944411,4163,4151,53059475300643,9454345,4174,4180,13472221,20875162077,9454843,4162,
4156,27590795628,13489308,53209738126682,4163,4485,39128187360602,4155,27634807173,11100209,4180,4182,4173,53228793095415,0x19bd04d4b15f3cc,
18468409390,25221239444,17726567770,4162,25019131120,0xcd927d069d353d4fe,4145,25990619601,4147,12285278,0x19b2345d1c08317,11063342,0x18340fa6c90411f,4165,4162,
9470015,4163,4160,4166,0x19bae99da41a3be,52922835375259,0x60eb3d754d526c90443c,4165,4156,4573,56582890022234,4142,27585585343,12313656,4140,
56581290631359,56582118269207,11444270,4145,4137,26822603519,21580178394,41170159526774,4140,0x1740d75db9041dd,4162,4159,4156,25103820025,22737355825,
4142,25837560002,4165,0x95f83536509a9d11f,4152,56513239466952,26720838021,4172,77458848091534780,23374889335,4982,58191164069023,4147,4152,0xcda418a741c89e49b,
4165,4159,0x169ed797d2260c2,4143,4155,4137,4173,4161,79925031451087209,0x4453509aa421aa2e5239,0x34ec840e89b306d7aafd2ff,4161,8732732,5466,51257962750336,
4161,11522918,4156,5275,27574793259,4142,13030750,24213783411,4137,49845908395452,4152,0x19b2bd5a7a96310,4140,4161,12244310,
51528689018198,4137,0xbb110ad3e6caf543b,8732724,4184,4190,4966,81349196635693926,13471815,20129355096,27594432992,4171,0x88a1d86bd72cd9239,0x19bb068820ac3be,8732747,
4184,9887830,4165,4173,4181,4185] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part410 : Refutes moves 0x8010100020000000000000000 0x67fc9e23402c4c0c1881102020 :=
  finish #[
13472045,38149721711584,56507514057385,4151,4163,0xba1116cf1a3c1a55a,5275,13472923,10700122,4175,4181,4151,13472923,12317148,4158,
25990243371,4175,9843674,5073,11863195,9843867,4158,4170,0xc1a6b2e8a3fa3f3c8,4175,4163,10646178,4144,4156,4162,
4174] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part411 : Refutes moves 0x8010100000000000000000000 0x67b09a23422848080800000000 :=
  finish #[
47957861569488,47958624932607,0x1a7cd30a4cd949b,0x4a4a7e5cf07a6c893247,4154,4148,4144,12673218,0x9381e3365dba7e2a2,4144,53295675446032,4880,56544304461244,56545186505677,4145,
98220909875753653,4196,87653949374723231,4162,4181,4174,4182,4187,0x19b2bbc8203b436,39335166685573,0x17588cd4b2f7370,4182,0xa3f5dee88512964ef,0x176d0681da28423,11129012,
37972143764535,4181,4174,4151,4163,4187,4159,25219535928,13488305,4144,77413428632962091,10616895,87660737998250468,5267,12313656,
10641482,12240222,24285287774,4164,12690197,4138,28416070908,0x53b408528eb5aac1d5bf,10641475,11128879,4175,4159,4182,10695329,10724001,
4163,11773083,22467801774,4174,41290334696491,48231866283051,4159,25158861972,25160578196,26703192142,4143,4137,54656096396331,98884241756107921,4159,
27627222175,5267,9843472,4170,4174,4580,10650592,22735867971,4159,4175,4196,4182,17368731836,21797041307,4178,
25999729818,5274,12317658,4178,0x177cd51aca2636e,11894855,4143,4170,54877034733925,0xc175bed751423a104,0xa3f6bb05d4a29d3d1,4159,4152,5278,12313656,
4170,0x19b4a04b1a962c0,9093178,4167,4175,53214101791687,17730212607,0x19b6d19af163368,4146,24264172003,4145,80487985552442716,9093183,9887823,4153,
4165,4181,4185] (by decide +kernel)

private theorem part409 : Refutes moves 0x8010100000000000000000000 0x67b09a23402848080800000000 :=
  branch 1 0x8010100000000000000000000 0x67b09a23402848080800000000 65 0x67fc9e23402c4c0c1881102020 (by decide +kernel) part410 part411

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part413 : Refutes moves 0x8000140000000000000000000 0x66b1ac92802244000aa0000000 :=
  finish #[
53246672593782,4287,0x53e8188349fa0b01a4f0,27629183167,26000225534,4148,27628770338,27609658505,4163,11055164,4177,4185,4171,0x19bb0657acd93bc,0x636897030bd66c854356,
4186,13473007,0xb5f8dceae6c9a2359,13488184,56583721747520,4139,0x34fcd1344450a7d3e85449c,4185,0xa168f41508290b320,4160,4163,4187,5466,0x168d365d134e42e,51167208773055,
47658249626584,4171,4165,10289215,18130011580,0xa78a7f0426cc6d2a1,38964913100128,28439610816,4155,0x18271e473084170,0x636cdf1089e1104d9170,4140,4138,4135,4145,
4769,12317527,9482292,4163,21075677847,0xcdf26f3641fc1a55b,77480325478953944,4145,0x16870593eb553d8,4143,54650432454835,4777,12674390,4156,25990882455,
56505120969559,4166,4168,0xcdf8270693eb55315,4143,8732737,4187,4192,4182,39141935469207,98145369254298193,4164,27625915630,22575645345,4163,
11523004,0x1747355a3226251,8720443,4182,4190,27590836817,11371868,40812602242396,4136,49746152628991,4149,42547754669211,0x19b2d387cc1e558,22582804529,9093187,
0x90b440740561720bb,4196,4161,4165,4177,4185,4173] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part415 : Refutes moves 0x8000500000000000000000000 0x66f39a4a02244002a800000000 :=
  finish #[
0x57fd3d824359701b4222,0xa7e5fee8cda2ed3c4,11522084,98984417647555725,0xcdf8de9cd791010a2,4159,53280951379296,12284688,4170,4187,4147,12690495,10273641,4159,48251453191309,
0x69e8d1014e997c1cc424,0x1a7a028e640c152,12689436,4138,0x31fca73a69bd374823b737e,46204648485453,4182,4147,25137337400,0xc1d9bc221712fd185,21745524796,4155,4173,4149,12272499,
0x69f8f0a7cbc9da41711a,4130,0xcdb1daef8809cc5c0,4159,53232892207693,23283889095,49996201456472,0x66f9431163c00f0205c0,4136,4138,4134,5159,25988825677,24285975295,12255298,
4144,81114518229742631,77445225359237603,4149,4145,4153,0x168b36d6b8f05be,10641596,8650805,11924347,0xcdb1e0be9afa26182,4149,4153,0x174cbd60d2e75bf,51236788659151,
18539528241,4175,4167,4173,44453827757212,44470314590973,97751473246225758,4159,24121554159,21041751386,4164,4172,21911388852,4186,4187,
8733376,0xba34410657d4d442b,24993506650,25906308038,4139,21963732310,4168,4163,21713216284,5461,12301280,4163,0xa9b5d4d3d7e9cc55a,4159,8732740,
9920598,4196,4173,4192,4181] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part417 : Refutes moves 0x8000120000000000000000000 0x66f19c464020c1000924000000 :=
  finish #[
25963074303,24176480916,56512402154366,72603405557790043,4163,4185,12690175,12313656,4140,25219683384,4156,4147,5050,11523020,4172,
49516915471706,22759387923,4172,4163,56543674582167,4788,27559273152,8732739,4185,4186,4181,4192,12677597,24992387732,0x177ceb54cb5d55a,
4147,4192,4992,5086,44452115661790,9842760,4162,4158,83651279484581210,4982,4476,5276,0xaf5832e857d10417c,4162,0x1a7f36c822992f7,
4143,4192,4171,4177,4306,46613442516316,0x1836e8d76b5431a,46618523972956,4153,4165,12694476,51154883957708,9482308,8732751,4192,
4187,4181,25991763294,12284974,12690495,4127,4163,48231791166093,5184,51358669579328,0x176ed41d590149e,4162,4156,4168,4158,
11915933,19423933388,4172,4306,8733024,4192,4186,4181,4463,12236118,92134017606345792,23549935706,4182,21961721083,12693900,
49763311763997,23331820700,4148,4156,53182952891135,53059401929269,4118,47819382445402,25227600525,4137,4129,28416484702,0xcdd837379df8540bf,4181,11083867,
22643000384,27635208405,4196,9453945,11137090,4156,4171,4177,10293337,4164,4149,4159] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part419 : Refutes moves 0x8000101000000000000000000 0x66b38cf2032040204808080800 :=
  finish #[
0x19ab37d712204f2,24113517614,0x175a571744df2a7,4159,49759281606943,51302070416633,4142,4158,4182,44537142620393,24109204345,4182,4480,9482630,4190,
5365,19421143703,9093220,4165,4177,4181,48227554534143,13488524,4196,5470,5462,56576810800480,4142,4156,47822036878302,
4190,11808864,20901131112,25076986734,26024563678,4153,4156,12690591,21796651971,4151,54896714392332,4170,4143,41271675209055,23598248411,
9093607,9904203,4196,4181,4177,24252921182,90744640532505376,4143,4579,10618015,24103515088,9904214,9482630,4163,4187,
10313813,4154,4164] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part420 : Refutes moves 0x8000100000000000000000000 0x66b18c63002040000800000000 :=
  finish #[
53090196115845,12313656,4137,76160406344828045,56579484292149,47834294523027,11042858,4182,4175,21743617178,9093330,4177,4181,0x19bcb5a6e94f5bf,13074916,
4182,53028345656569,47814681178968,4166,53209163711631,5077,41551295894874,4138,4142,41481017312602,56506035700892,4167,12238934,4149,4159,
11842039,11878789,56491985143026,0xb478e336110b5d49b,4142,4138,4599,0xbbe5acbfd7041a21e,20160799609,51530383573881,4147,8732772,4190,17886818693,4144,
4181,4186,10330196,4158,27591119935,0x134e9f8a4a8b46736478a2055f,13488217,0x167d4ec69139810025ac4d9310,4750,51647145825326,4196,4160,40926856716834,5466,56576292262873,
10696030,4187,4180,4144,4162,5466,0xc169bad7a6cb4c49b,11431983,4134,0x16a93657d34f489,0x19b658e6c8543d0,47949721068890,4196,4181,4595,
20320666478,0x19b258cbb0541ca,4186,4180,11847002,27593220309,4196,41548032369124,10641458,4137,4143,4185,21166420054,4164] (by decide +kernel)

private theorem part418 : Refutes moves 0x8000100000000000000000000 0x66b18c62002040000800000000 :=
  branch 1 0x8000100000000000000000000 0x66b18c62002040000800000000 72 0x66b38cf2032040204808080800 (by decide +kernel) part419 part420

private theorem part416 : Refutes moves 0x8000100000000000000000000 0x66b18c42002040000800000000 :=
  branch 1 0x8000100000000000000000000 0x66b18c42002040000800000000 77 0x66f19c464020c1000924000000 (by decide +kernel) part417 part418

private theorem part414 : Refutes moves 0x8000100000000000000000000 0x66b18842002040000800000000 :=
  branch 1 0x8000100000000000000000000 0x66b18842002040000800000000 82 0x66f39a4a02244002a800000000 (by decide +kernel) part415 part416

private theorem part412 : Refutes moves 0x8000100000000000000000000 0x66b18802002040000800000000 :=
  branch 1 0x8000100000000000000000000 0x66b18802002040000800000000 78 0x66b1ac92802244000aa0000000 (by decide +kernel) part413 part414

private theorem part408 : Refutes moves 0x8000100000000000000000000 0x66b08802002040000800000000 :=
  branch 1 0x8000100000000000000000000 0x66b08802002040000800000000 88 0x67b09a23402848080800000000 (by decide +kernel) part409 part412

private theorem part406 : Refutes moves 0x8000100000000000000000000 0x26b08802002040000800000000 :=
  branch 1 0x8000100000000000000000000 0x26b08802002040000800000000 102 0x37b88a82002640000800000000 (by decide +kernel) part407 part408

private theorem part402 : Refutes moves 0x8000100000000000000000000 0x26b08002002040000800000000 :=
  branch 1 0x8000100000000000000000000 0x26b08002002040000800000000 83 0x27bcc032083040124800000000 (by decide +kernel) part403 part406

private theorem part398 : Refutes moves 0x8000100000000000000000000 0x24b08002002040000800000000 :=
  branch 1 0x8000100000000000000000000 0x24b08002002040000800000000 97 0x24fdc00220a050000800000000 (by decide +kernel) part399 part402

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part424 : Refutes moves 0x40200100800000000000000000 0x2dde9e85486613018844020100 :=
  finish #[
19885306239,25997698394,13492297,4483,56507295183235,0x1a7b06d9f0fe183,4171,4150,49447162619326,0x180e57e0baeb55e,4162,4146,4138,21587366962,4486,
0x9b78184219f2e255a,0xbba818bc9a42fd3dd,4164,4196,4169,4193,58231289537467,0x182455a6a2f3222,23583474035,4147,4162,11482163,27593258235,4147,52989860353083,
56442131305918,4172,4196,12219350,0x406cdd774d717eae40b2,4147,19882370392,56424901026449,4196,11829289,4139,4193,23593850197,27551675738,4150,
98987921569166182,23581458813,4181,4172,24231383406,10318214,4172,5085,47734367782035,21006983223,4150,4165,4160,4155] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part425 : Refutes moves 0x40000100800000000000000000 0x2cba8281404600018804020100 :=
  finish #[
25191711783,0x946a769f8698b055a,27590997343,38810801952095,11485257,4139,56540234019879,9110972,58190406979845,11513908,11448371,4146,4178,4470,24134652977,
9109554,0x168c2c0288553be,4190,4182,84942382858494313,4681,9110371,47873527677320,4140,0xcd91d0b68e416e188,4157,4161,4145,12694160,56509013672168,
4178,0x507c7a81906a6a897091,46403708908886,28432122336,4171,4178,24411571069,0x168c2c14b29d491,4159,4161,4173,20128568371,0x50f53e9b257d7a1075bc,4171,0x96e8323ed4b29d21d,
10297421,4165,4182,83234085127132414,5060,0xb55370eed9d1721d4,9109565,4169,25882268712,49807547261992,9109569,25176015913,0x1777365a547a225,4133,0xc189b2d4449b5c1b6,
22601642036,4152,4180,54927995089107,5466,56508283708043,56575517134885,12678102,0x24ee0741268705e6ad3e222,27592863834,4152,86737493430620956,10657856,4171,11002219,
4958,46154669597349,4169,4979,44256822096945,4182,4173,4161,0x8d08308a94329d0d2,53195066118503,48318483076136,10736414,4159,10661963,4172,
4178,13472808,27627930396,10658590,4147,4159,0xbb1a7a2c115bb03d6,56512435806985,51249029272242,4172,4180,83988122871227740,4165,8745033,4192,
4193,4190,4184,4196] (by decide +kernel)

private theorem part423 : Refutes moves 0x40000100800000000000000000 0x2c9a8281404600018804020100 :=
  branch 1 0x40000100800000000000000000 0x2c9a8281404600018804020100 93 0x2dde9e85486613018844020100 (by decide +kernel) part424 part425

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part428 : Refutes moves 0x40000120010000000000000000 0x2dcc0ad5828619000926082009 :=
  finish #[
17341837971,13452024,4132,0x202e0e80d67cbd42bafd5bf,4196,4965,25957409337,4196,46199621382833,11523418,47898206536450,4171,49780512715924,49962012726617,12693593,
4150,4181,4183,4139,13472111,10707829,0x1415375032fb5fb3647d9074fb,4180,4156,25934291424,0x18213560c8fe2ff,4183,46086824477945,13472111,11518844,
4163,4178,4155,10265759,8746138,4183,10708119,0xc779b61560caf42fb,4155,4171,10347098,4180,4185,4182,4162] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part430 : Refutes moves 0x40004100010000000000000000 0x2fd8aaade28621860886080208 :=
  finish #[
13472114,77761398533100404,0x19b34f91b0a237c,23523099791,4139,4147,4163,4476,21779144920,4189,20134888798,13471803,9109797,4169,4185] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part432 : Refutes moves 0x40200100010000000000000000 0x2dd95aa58aa601200806090008 :=
  finish #[
24380817602,9429369,4147,5083,0xbba2bebce6a0a04ef,4169,23581033030,0x5af2d46b8281a42f455c,4139,4147,4155,4391,11522939,9069508,4183,
4193,5069,26706031867,20681405398,9068571,4171,25192788957,0x19b34f5ae35e493,18524299320,4137,4155,56429071795240,27632731385,13075802,87195946335896825,
11354209,4139,10326106,4162,4185] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part433 : Refutes moves 0x40000100010000000000000000 0x2da84aa1828601000806080008 :=
  finish #[
36649275782182,49694578636015,25823232607,23516394840,9044018,4163,19386794275,4183,4169,27591934820,10708314,4183,47597015118085,25982547290,0x18326dd122362ff,
4147,10187417,98361651458589337,4166,18657780676,8745033,4185,4183,4193,56584559068316,20218061980,4165,0xc0e44cd7a37c7b43c,4158,9826891,
54895003869683,22500565963,4171,13471789,0x66cc082d48989e41935c,56508435235393,4152,4137,26781520827,12297165,4164,0x336c732148deea1dd22624b,4137,11485665,4171,
4163,4147,4155,19984319046,10347379,10305999,4157,4185,0x29f975c13838bf083a881b7,4312,0x1a7c8c23c3550d8,4155,10346712,4162,39706688136340,
4181,4185,4183,27624333506,27625939551,10076249,9466825,13492616,4145,4312,43317664773372,0xaf58f0ee8ec8b021d,4169,4181,4185,
4193,4703,10077020,8746233,4184,4186,91428501852361365,4137,9110466,10707160,9109803,4181,4165,11100235,4147,
25191928200,5466,12301371,9465953,13087993,26802591066,4164,4155,4170,12259925,0x8cf6aa2a8ef4d9222,5466,9921398,8745033,4193,
4188,22777811033,4152,4166,4180,4196] (by decide +kernel)

private theorem part431 : Refutes moves 0x40000100010000000000000000 0x2d884aa1828601000806080008 :=
  branch 1 0x40000100010000000000000000 0x2d884aa1828601000806080008 93 0x2dd95aa58aa601200806090008 (by decide +kernel) part432 part433

private theorem part429 : Refutes moves 0x40000100010000000000000000 0x2d880aa1828601000806080008 :=
  branch 1 0x40000100010000000000000000 0x2d880aa1828601000806080008 86 0x2fd8aaade28621860886080208 (by decide +kernel) part430 part431

private theorem part427 : Refutes moves 0x40000100010000000000000000 0x2d880a81828601000806080008 :=
  branch 1 0x40000100010000000000000000 0x2d880a81828601000806080008 77 0x2dcc0ad5828619000926082009 (by decide +kernel) part428 part429

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part435 : Refutes moves 0x40002100000000000000000000 0x3ccc5288990604210800000000 :=
  finish #[
25990554197,0x9c574c279dd8570b5,52983448642711,0x19b453143057489,13070552,4871,84460317196501208,4185,21787562040,4172,4166,4178,4183,47631434478942,0x17408920d3be493,
0x1838d794428f421,4173,4161,0xba0834e9e38a300e8,0x6062308fabca09c1e0e8,4145,0x4b03aa5031ed7241a421,0x18f6b920d21a310,4173,11518844,4162,4155,4178,27561677575,51189241210098,
4161,0x483c7da7cd61ddbb055a,4193,53076630926389,12284581,5176,25218400648,9830469,4155,4159,4147,25220457726,54726677742939,10682434,13472526,
0xba39b34f546af336c,4162,24993891384,4142,0x19b536547afc499,56507503719184,21888225322,4165,4166,4178,22679490776,5256,22657987617,12705879,4178,
0x69eb421ce15e0b288225,25958180089,25991037985,10592307,24212992679,4188,4179,75134689217717406,4763,0xcd99bcd057e2f3489,4162,10297426,4150,4155,8746139,
10687643,4142,0x5d88577473669ea96431,4140,98639533399970644,10338370,4172,4185,4192,4170] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part437 : Refutes moves 0x40100100000000000000000000 0x2ea86680910e00800800000000 :=
  finish #[
12301351,51595664483387,4137,0x34f8693bb826d766da2b4f0,4142,5268,25996448733,4141,43055496688880,4158,54897694246234,4163,4157,10593628,11100844,
12615724,95613776327185756,10338365,4180,44401560757694,12260507,9467039,4156,4174,22735860681,4488,22776554655,4157,4165,4161,
4466,21890151566,10327486,4157,37868300780699,4165,4185,4190,23381783710,53279291711979,4149,25988563497,0x8f506f06a0b41e48d,4142,12689990,
53227163275846,9470036,4166,4172,0x6040eb2bf364e2c1a114,18417222022,11121024,10711730,4190,4196,0x483c139b2eee032fb186,4887,44934167037065,4190,4196,
25194857607,10687647,4196,0xbb78f6a3d722f42ac,4170,11043685,11129196,9830470,4159,4139,4147,4163,4486,47902233576603,4165,
0x1834a057daf4435,0x18f704ce52f44f0,10347083,4180,4192,4162,25992160600,25998643884,4166,9831090,4147,4981,5257,10327177,10297405,
4192,9109588,4173,4185,4183,4179,4171] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part439 : Refutes moves 0x40000140000000000000000000 0x2c9c26b0810660000aa0000000 :=
  finish #[
53059392742261,11363483,4141,0x19ab05a0d296299,0x19b2a5918af442e,0x60c4719b28f60d1080ea,4169,4190,4166,24095568742,9921406,4161,0x4a621f5ac0a1181dc497,22657987165,4193,
4190,10618202,4312,8745217,98696699926675821,9109569,4169,4189,11363476,11911964,4166,5076,41545540154299,9109569,4169,
8721063,19029664604,21023367651,17895153725,53227160936951,53233646933243,53231892124327,10338397,4170,4180,4192,4190,4182,4179,4185] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part440 : Refutes moves 0x40000100000000000000000000 0x2c9822c0810600000800000000 :=
  finish #[
5466,36308903630175,94275342556190143,20133323815,4157,4159,4163,56429103759700,79493902631138452,4196,0xcda9bc34ce44d92ff,25133323220,4159,13471960,13472801,
17913603108,11522102,4169,4196,4180,13472807,51238302225559,27590488766,4196,4189,13472911,51408515470375,46145858675573,4159,10616899,
4155,11510643,23240716504,41614209688713,20183711828,4189,4169,4173,4185,5255,51531085795795,5358,54864164967285,9044050,4155,
4157,24295703295,10986174,11043607,4180,4168,4196,21991625495,47662280578081,0xc1ba7abd082cd92ff,84455482355110665,4152,12689474,4193,4127,
0x177cea84a2fa3dd,8721563,0x8808e28ac28a7a16d,53228046508406,4171,9470342,4157,4166,4178,49382026273521,11412529,17862087423,4168,4180,22792570011,
4171,4173,5279,0xad438106cae2f45bc,4155,0x69ea18670eeda1c1e49b,0x16709e9a62f443d,4155,11129609,4180,4196,4401,0x16b90226ca963c4,4196,0xba8826d414e96e3c8,
0xc1a2e4d41710b031e,4171,4165,4169,0x169872a6c9025be,21779173963,4171,56593442230951,4193,4693,10683045,4183,20150157652,21110038921,53227941462807,
9920599,4196,4193,48337385333915,11101530,4168,25931125114,0xafa9bd06a6ca9d3c4,8736845,10338394,4170,4180,4190,4192,4185,
11124822] (by decide +kernel)

private theorem part438 : Refutes moves 0x40000100000000000000000000 0x2c982280810600000800000000 :=
  branch 1 0x40000100000000000000000000 0x2c982280810600000800000000 78 0x2c9c26b0810660000aa0000000 (by decide +kernel) part439 part440

private theorem part436 : Refutes moves 0x40000100000000000000000000 0x2c882280810600000800000000 :=
  branch 1 0x40000100000000000000000000 0x2c882280810600000800000000 92 0x2ea86680910e00800800000000 (by decide +kernel) part437 part438

private theorem part434 : Refutes moves 0x40000100000000000000000000 0x2c880280810600000800000000 :=
  branch 1 0x40000100000000000000000000 0x2c880280810600000800000000 85 0x3ccc5288990604210800000000 (by decide +kernel) part435 part436

private theorem part426 : Refutes moves 0x40000100000000000000000000 0x2c880280800600000800000000 :=
  branch 1 0x40000100000000000000000000 0x2c880280800600000800000000 64 0x2d880a81828601000806080008 (by decide +kernel) part427 part434

private theorem part422 : Refutes moves 0x40000100000000000000000000 0x2c880280000600000800000000 :=
  branch 1 0x40000100000000000000000000 0x2c880280000600000800000000 71 0x2c9a8281404600018804020100 (by decide +kernel) part423 part426

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part444 : Refutes moves 0x10080100800000000000000000 0x6fd76638345289442814020100 :=
  finish #[
27609494663,56547775279864,12689444,53230150808220,94513385924764733,4183,4174,9840060,11887665,4154,0x169a055d11d049d,81420214278640680,4174,4168,11891069,
51445354640352,4150,10289336,0x180d0714c9c1426,4143,0x2811d3c7aa7c3f1ab96b433,0x63753e1f872d4cbbb162,4143,4174,4183,0x1a76ebc3eb5755a,0xbbf6ab36e0e1d5430,22693904471,4149,4170,
4163] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part445 : Refutes moves 0x10000100800000000000000000 0x6c9f2018045080042804020100 :=
  finish #[
4378,83726700873889119,11354141,83162104970805409,4136,41276473873760,4153,0x18349f8e3b560fc,9117744,10994843,53227095749003,9117768,5471,27635573501,39755710812208,
4190,4192,0x337c680d61e50610a90a150,39617458152078,4179,51514056582496,0x18fe888590552ae,4192,4193,22750037440,9479119,9405408,9478527,4183,4150,
12689622,5262,10744022,4163,4175,4193,4180,0x1838ebcb79732c0,4166,5564,22695404485,4173,12280867,4139,9478842,
4174,53018573775648,0x175f1ea0d22d4ef,4168,24111392096,0x16710366fc1a2ba,4193,11363679,0x1834d7a6f9d7357,12251200,4155,17869304408,4183,4190,4182,
11415947,49346048307446,23382884848,25033495709,12251220,4155,47883508601227,4183,4190,0x219c020b2a7c3bc7fc1a5bc,4890,21703611535,4180,44757453481105,4189,
4174,0xbb69b74ec829d128e,38249480987283,24983605856,11079758,18675791196,4157,4192,28438438539,0x5d29490309dda62f4186,5062,18673389778,4183,12689501,4193,
12264309,24203490066,4193,0x1a7d0682897f320,9891927,4174,4182,4190,80171324467258619,38252853306510,21158351932,4168,11513934,21956522959,9118045,
4183,5071,0x31ea6fc0d205069afa28320,4157,43284113110067,4155,0x9d00a21557d97f186,4183,4182,11448414,4146,4163,4154,4179,4170,
4178] (by decide +kernel)

private theorem part443 : Refutes moves 0x10000100800000000000000000 0x6c972018045080042804020100 :=
  branch 1 0x10000100800000000000000000 0x6c972018045080042804020100 91 0x6fd76638345289442814020100 (by decide +kernel) part444 part445

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part447 : Refutes moves 0x10000140000000000000000000 0x6c862c9a801188000aa0000000 :=
  finish #[
0x443b438303be6cc1a161,84524054631015769,4145,0xb4f1c10220f4d9097,54668115117005,25954473306,4130,37359448507740,4177,4143,5466,27593634969,5468,0x181136e6d41649d,9044017,
4159,4163,0xb4d1df365de3a5487,4132,4162,27611993126,4379,25061090352,17595995184,56480643736345,9838659,12615741,4189,4145,0x60b355134ebdde41a440,
0x175eeca0403f9b286a0d2263d8,4137,4143,4149,4155,11449282,0x1a76bb1a0afb497,4155,22696670365,11886954,4153,8930157,4139,4135,0xc6d450415a529f42c,
4157,0xd3b834b8e0c4d9497,0xa0e6aaeaddfc7b3bb,0xb5575f365d41cd29b,0x19b2259762fb43d,4163,4162,4155,0xcdf77f04d45c1a364,24984806555,11080671,4163,4155,49430478578940,4180,
4177,4182,44435870164127,26025772384,51617168970889,4190,4188,4310,5271,21173196124,4184,9117780,4177,80168008702985467,24204547223,
25218905141,20334714941,4177,88124728609698758,23391322912,38245544394813,4155,4163,4183,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part449 : Refutes moves 0x10100100000000000000000000 0x6f84f0c8901880800800000000 :=
  finish #[
12653036,12682377,25913443465,4148,4145,0x66d40867e589a72845bf,4185,25018700570,0x1a7cec66d28455a,56547649958848,4162,4158,12673981,47955109307451,4271,
0x18df1e20b16b357,4170,4146,12660790,4145,4134,25933505180,19297711252,4163,9478930,4177,27599610515,39760461108189,4149,58242730419547,
9479327,23491244098,4158,4190,4159,25914766471,4788,12260128,10744978,4169,4163,47955391754822,4166,4150,0x18348ccb40b229b,
49465566897208,0xad48dc8fc59174172,9945155,4190,4179,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part451 : Refutes moves 0x10000100010000000000000000 0x6d942449a01881000810880008 :=
  finish #[
25024308056,46130996966542,22753817545,4163,4143,51248097756504,24214607292,56508612207854,4145,25917895007,11433117,27593519158,4162,11002137,25141331197,
21165547599,4159,4189,22761690458,99056796208837276,4189,4491,22467834728,4190,0x19b704d7f9c1088,12256199,39555980432133,12300342,4184,10641475,
4161,4143,4179,25957495866,54770136133826,47837600125721,4177,4163,97624505590411926,9478741,4177,39758839764218,4310,10744500,4169,
4175,4193,4180,0x18f5379ac23455c,0xcdb8dc9dddfcde31a,11858680,10973931,97605594155156216,4146,4143,4173,4149,44658282918956,9892619,12280876,
4189,10642292,9774428,56507671028459,21805084761,53159290729431,4175,4180,4193,23582630259,0x168b07113afb3bb,0x4b793969889d7da3f55a,4175,4193,11486061,
4139,4147,4163,4162,11420415,4889,4307,43423986275676,27609630144,10293337,4193,4189,4184,23523193625,0x1a7c9fa6dae3375,
0x19aeb8c2a977375,9478230,4189,4162,0xa2247ea64b40b2430,47902762418784,98631674885231359,20268433474,4190,4175,4183,4179,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part453 : Refutes moves 0x10000100000200000000000000 0x6c9c2248815090000c00005200 :=
  finish #[
11109031,53230342632189,0x183459208a3f36c,4169,4175,10641803,22751830695,9117778,4189,11137901,86707269083043163,51527882589220,4157,4180,4769,
0xa6e39936d103a3172,4140,0x86d68a10038a7c42b,56595828544657,9479224,4165,10616895,11003231,10994431,39317967892938,10272810,4169,4144,4139,4882,
98351611065005092,4169,4178,36996959671157,26788721327,4157,83505353899844955,4185,0x16b4a7c59170438,4159,4175,4183,4267,51511450883324,4179,
0xc7b5b8bb20d2913c2,4163,0x8828351e5dacda16e,53229445022456,25990656752,4150,4185,5277,5166,27634824036,4185,9891894,4162,24153113646,11416917,
0xcda822b8ddaaf42b4,9891907,4162,26803913883,0x17473511a1d23d4,10338358,4185,4175,4180,19414348139,8737132,4193,0x4039c5741061df01f100,48111420921183,88539828431545788,
4193,12313464,4150,9908303,4170,39315521655551,22536102568,88243874297962686,4185,10273533,4861,56616460485787,4165,4162,11920039,
11821103,4146,4161,47683761750775,4965,12690264,11421023,4163,56527872058102,12242985,10293302,8725273,4185,4184,12243829,
21064131353,9924697,4162,4178,11002548,24967110901,5359,0xb3f746ef93f2334f0,4150,4168,9117757,0xba38368cc5917443f,9945151,4175,4179,
4183,4182,4190] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part454 : Refutes moves 0x10000100000000000000000000 0x6c942048811280000800000000 :=
  finish #[
56475743654081,25162511396,25060700920,21913792575,4157,4690,9896821,0x15e8030359451a68e548a9f423,4184,4192,72376594676188216,0x1042d3437cdb7470451cba6260,4184,21199520333,4159,
12301351,25191253031,10616901,11080284,9117778,4185,4173,4183,4693,23549935987,46615160168733,43226682663785,4180,4177,9945585,
4179,4183,46614275007647,44452232303084,4162,0x93d2de0566d23455a,0x2efa0f3415331b5ad23355f,10338358,4187,11432709,0x18daa119d9c3494,4145,44291937268292,4159,4863,
25009902335,4162,11112829,0x1763079dd1df293,4189,4184,4163,4391,10309939,4189,47970917897057,18674598389,4179,4190,4187,
4183,5255,12296675,4163,22808974372,4187,0xa1606e260efa265c0,20230017703,0x6372e75ff364b141e497,84527370409189754,4163,4145,17720649050,22526387357,0x30460f34e74cd7cb11df0ea,
10313795,4189,4184,51361895506306,4775,85254347782981056,8736850,4192,11002548,11403659,21795160127,4175,4187,4190,4179,
53268024968533,9893205,54657823892214,20997341680,4159,4157,4163,5465,9839385,4157,10338787,4175,4185,4588,49964689794190,
8736849,9876135,12706765,4145,44639667725471,4159,46136793326749,0x30787e27574cd7cb11df492,4163,21124461027,4159,4184,19212165873,21795861562,4180,
41373740692538,4169,21795139777,11002536,5464,10351350,10313795,8736850,4192,94514897191682752,4175,4190,4187,4179,12689495,
4138,4149,4193,11124822] (by decide +kernel)

private theorem part452 : Refutes moves 0x10000100000000000000000000 0x6c942048811080000800000000 :=
  branch 1 0x10000100000000000000000000 0x6c942048811080000800000000 57 0x6c9c2248815090000c00005200 (by decide +kernel) part453 part454

private theorem part450 : Refutes moves 0x10000100000000000000000000 0x6c942048801080000800000000 :=
  branch 1 0x10000100000000000000000000 0x6c942048801080000800000000 64 0x6d942449a01881000810880008 (by decide +kernel) part451 part452

private theorem part448 : Refutes moves 0x10000100000000000000000000 0x6c842048801080000800000000 :=
  branch 1 0x10000100000000000000000000 0x6c842048801080000800000000 92 0x6f84f0c8901880800800000000 (by decide +kernel) part449 part450

private theorem part446 : Refutes moves 0x10000100000000000000000000 0x6c842008801080000800000000 :=
  branch 1 0x10000100000000000000000000 0x6c842008801080000800000000 78 0x6c862c9a801188000aa0000000 (by decide +kernel) part447 part448

private theorem part442 : Refutes moves 0x10000100000000000000000000 0x6c842008001080000800000000 :=
  branch 1 0x10000100000000000000000000 0x6c842008001080000800000000 71 0x6c972018045080042804020100 (by decide +kernel) part443 part446

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part457 : Refutes moves 0x2008100000000000000000000 0x7cd84032248112040800000000 :=
  finish #[
22784963742,0x9bd0ec2026ca9c09a,20916728887,4158,4189,11125110,80347244777333533,4137,4155,5466,51667051201984,4155,46476943934515,97512272868865472,4174,
4154,4592,19239351069,95564972504313999,4154,25199538948,12305466,11023229,4163,4179,4155,4185,20260365085,4157,4147,
4142,5071,11125025,4167,25226441689,0x168aed4ea3a8084,24423072629,25229214688,21132861494,4170,4175,4192,26015634585,0xc129bcd31d43bc55a,4155,
49533406799296,9891911,10286237,37545247003616,11056089,23382143958,4154,4178,4170,9736989,51150076818160,4192,4688,0x19bca710d358305,4161,
4137,24412705050,20914697373,9892432,4170,4178,11006010,4124,50016206316095,0xa9c3a8ea0e6bb9560,22601584736,4175,4189,4166,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part459 : Refutes moves 0x2000180000000000000000000 0x7ccdc24030a014000f00000000 :=
  finish #[
0xa7f0009d60934f55a,49998783952017,4139,0xc104fe0013ab4f358,25909519507,4141,4125,38728701707300,0x8084f94f96bba3498,97612380673553560,72483642952508764,4155,4143,0xa7f8f09d5af1bd438,4139,
11124819,4160,42628620075357,13493401,22543721505,4143,0x182e101dbbbe11a,4150,11124810,23281124304,49999024018264,4171,44601198834246,4147,4192,
4162,47766447964849,4494,19439071443,0xb3d0a4d2c86b5d30c,4893,0xad6064d510f23031d,4141,4153,4147,9490592,23247557006,4150,81541901021295957,4179,
54804706546461,4670,47903887615021,4188,22752653395,4149,4163,4170,4192,58240438747718,0xc7d83873d4e22b55a,4154,5277,11006807,13493079,
4135,0xd3d5393793f8521d3,9490515,4192,25057105053,0xa840a44350fc77097,10707002,4172,4171,11109124,4893,18158052415,0x19bd4f545a7f225,4124,49900794934524,
24285357203,4185,4179,46499979395635,26770367633,13885491,4307,42830105670701,4139,4179,5184,0xae46750402928b55f,49517183619161,4160,4172,
4171,4189,46595649946590,9491697,20260024413,4162,4170,4166,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part461 : Refutes moves 0x2000100800000000000000000 0x7cdad48020d010200c04020100 :=
  finish #[
4494,11101021,25227981759,10609905,8881096,76294142231175945,4171,4133,4135,4129,11400247,22792951130,11063371,4152,4166,
4307,8725158,0x66f01d7581494b29d3cf,4168,4154,4307,17861620503,4154,4307,4307,10736407,4154,4166,0x4048fb83043515230088,4153,
4171,4177,4184,11093338,0x17594fd9e4d9556,26015793924,4177,4163,5272,11092927,11128874,44394889782039,4177,4147,52903832437903,
49402578814298,4138,54928843518938,4169,27592061910,0x174ad2ce69d25c0,4150,4155,27592844027,10318622,51667744597340,54912476238805,10637387,4184,4172,
4154,4160,0x2060811475f91f1128515c0,0xd3e038148e69d72a6,4192,10318207,0x18374f69f10d2b1,9957469,5567,10318414,20260040768,4166,4174,4186,4170] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part462 : Refutes moves 0x2000100000000000000000000 0x7cc8c080a08010000800000000 :=
  finish #[
0x18371f5d2a8a361,47695161132480,4147,0xad8522eca9f470426,0x2b61de53e204a0d0fa3d354,4160,11436619,13882609,10707730,11436113,24404734715,4160,4189,11469300,24220258988,
4160,44722314801915,4150,4158,4174,4166,23615451933,10338899,4177,19202164158,53297391977099,4160,9491039,4162,4985,
9909113,4162,10347101,4185,22780568159,0x15b14f89e9020027794da25172,4160,44725569172639,88880350877922161,4162,11100238,4161,4166,4189,4180,
4763,44727171645679,21839369271,51441185891383,4157,4152,4142,10592466,8847571,0x17568addfa960d3,4154,0xa258faa742928d092,10338360,4192,4180,
10637991,0xa2b4f4b5a6ca9c154,4153,11125591,4763,9446173,4154,23424520251,4151,91412630017262938,17868792487,48231940186909,4168,4154,48109251179175,
12280776,4178,13472318,28414955706,4161,13472109,27592385109,11501657,0x19b23a57c29d0d3,11124794,11464796,4150,10306912,0x19b2a71de21a0ba,4155,
23289888978,22601584695,4145,4152,4180,12284701,25160176413,11501633,0xa7c9b2a05741dc5be,4192,95613997175657055,0x63d9ad1327717c2ff55a,4158,5086,45996821967639,
25059914592,4150,11124798,9941084,4178,4170,4174,0x16bcba14e2f8176,0x174aba140af75bc,49522795594816,11124817,48229507482970,4173,4180,80590308092408574,
22701531431,4177,53247506023872,23422952794,11124817,46666895508826,11100862,9084986,98249031778533570,23555908382,4177,46666063918232,4145,4152,4173,
9879645,4163,9912829,4186,4171,4179] (by decide +kernel)

private theorem part460 : Refutes moves 0x2000100000000000000000000 0x7cc8c080208010000800000000 :=
  branch 1 0x2000100000000000000000000 0x7cc8c080208010000800000000 71 0x7cdad48020d010200c04020100 (by decide +kernel) part461 part462

private theorem part458 : Refutes moves 0x2000100000000000000000000 0x7cc8c000208010000800000000 :=
  branch 1 0x2000100000000000000000000 0x7cc8c000208010000800000000 79 0x7ccdc24030a014000f00000000 (by decide +kernel) part459 part460

private theorem part456 : Refutes moves 0x2000100000000000000000000 0x7cc84000208010000800000000 :=
  branch 1 0x2000100000000000000000000 0x7cc84000208010000800000000 87 0x7cd84032248112040800000000 (by decide +kernel) part457 part458

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part464 : Refutes moves 0x1008100000000000000000000 0x7ee108460b010a040800000000 :=
  finish #[
25837179872,25988563523,0x182c59a0d03d22d,4158,4159,9495317,5275,25965388955,11452486,39829281682391,4154,4186,4187,39367893017374,5261,
37900874499033,4159,5261,12689900,46678082692251,4151,4159,4149,4155,51299605390080,51668676162696,4154,5275,0x16bd05c200f031e,9876632,
4178,4166,24364033170,20229234961,25925111861,4119,4135,4130,4990,25915876507,4162,20923872700,76291220815422024,4153,4680,
11477484,4172,9495024,4187,4178,4166,4990,36234424746959,4171,5275,12689900,11523227,4148,4172,88084462291018692,
4173,4149,48334928716360,44516859376696,0xd3d75b0726a41a3cd,51528622282174,8651512,4165,4172,11006713,4124,4173,48181162337724,25160024824,48280735474337,
9494585,11092743,4182,4173,4175,4166,4187,93947861501964658,46025410707738,94280292841899163,4175,4182,25988170909,17720209866,11895457,
4143,4137,0x69e8da75a2660c2db284,4154,0x1824a054a10e488,4175,11124818,4146,4167,4181,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part466 : Refutes moves 0x1080100000000000000000000 0x7ea1c842390208400800000000 :=
  finish #[
86810816241824704,24152269960,12689457,5159,5272,12678112,58246703297693,4139,12255281,4144,10637506,4178,4154,98534287013061783,24197046949,
47969939223900,4150,9036657,4161,10732393,4178,4177,4159,48194888860818,23398917088,12218417,4863,10634208,10272843,4159,
12690579,26702766847,4150,5261,0xae012c0f4aa09e0b8,4159,11124801,4167,21879394988,0x1a7c5791829c1d3,0x60d4712cce9d4e1d6089,10350650,4173,4178,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part467 : Refutes moves 0x1000100000000000000000000 0x7ea98800090008000800000000 :=
  finish #[
0x86d07403d6ea7e2a7,11391216,37131849590112,4173,4170,23463039830,8503452,4136,13891006,0xd3f69f3784ccdf49e,10272818,4863,10617025,4161,25824060472,
4150,4167,9372818,53076597399744,4167,0x176e07c104110c1,12652826,80518186748658834,4159,4154,12681264,4136,4173,4169,0x19b6405ab29c0f2,
0x18fa891afa7e499,0xb5f448ba94e2f20be,4161,4169,4153,35580191617999,21728789365,4165,9925202,4166,11007216,43267555165142,4169,40824170202158,4153,
4863,21939209371,8720459,4186,21838549179,47785254024153,21116067914,4168,4173,4178,5153,94130641350226160,80305018956100647,4148,12632122,
18390073730,0x805082731a441d76e890ba1685c0,4167,4159,5076,91209117957162028,9863230,0xbbb2d0becefafc4f7,4154,12318046,10683840,10687165,4166,4177,21073690979,
4155,9957881,4182,4190,4178,25990619625,83967958468247920,20204077847,10289207,4153,10330909,4174,0x18fa9e94e10e43f,0x5d033a2170694b16c42e,9929201,
4186,4171,4190,0xa7369d4fd442f437c,43161327035342,4166,12690372,21536297116,20335091770,20338287271,9896429,4159,4155,4167,19446285467,
46442791957471,4188,10232416,9941391,0xcde83537dd3a880ea,25989869958,20369109065,4171,4182,4186,9134158,4185,4181,4175] (by decide +kernel)

private theorem part465 : Refutes moves 0x1000100000000000000000000 0x7ea18800090008000800000000 :=
  branch 1 0x1000100000000000000000000 0x7ea18800090008000800000000 91 0x7ea1c842390208400800000000 (by decide +kernel) part466 part467

private theorem part463 : Refutes moves 0x100000000000000000000 0x7e800000000000000800000000 :=
  branch 2143 0x1000100000000000000000000 0x7ea10800090008000800000000 87 0x7ee108460b010a040800000000 (by decide +kernel) part464 part465

private theorem part455 : Refutes moves 0x100000000000000000000 0x7c800000000000000800000000 :=
  branch 1 0x100000000000000000000 0x7c800000000000000800000000 97 0x7cc84000208010000800000000 (by decide +kernel) part456 part463

private theorem part441 : Refutes moves 0x100000000000000000000 0x6c800000000000000800000000 :=
  branch 1 0x100000000000000000000 0x6c800000000000000800000000 100 0x6c842008001080000800000000 (by decide +kernel) part442 part455

private theorem part421 : Refutes moves 0x100000000000000000000 0x2c800000000000000800000000 :=
  branch 1 0x100000000000000000000 0x2c800000000000000800000000 102 0x2c880280000600000800000000 (by decide +kernel) part422 part441

private theorem part397 : Refutes moves 0x100000000000000000000 0x24800000000000000800000000 :=
  branch 1 0x100000000000000000000 0x24800000000000000800000000 99 0x24b08002002040000800000000 (by decide +kernel) part398 part421

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part471 : Refutes moves 0x10028000000000000000000000 0x27d93546205500000000000000 :=
  finish #[
9459039,56505932141706,4149,10965861,23389725759,4175,48181087237262,4162,4186,19370800285,9893010,9892733,11858590,4128,11124819,
4167,4146,4800,37833763222202,0x9508f611d722f43d6,4195,4179,25069052280,11494454,25143014263,22003950455,4153,4163,4157,23526720545,
5262,0x837756bd9db2fc49b,4163,39436629242743,0x2ed66f2755ec11e6d2fc178,11124803,4167,4146,4195,56531377308541,0xa398f2a720d1c755b,4198,4981,0x1822eb1db23317b,23432499302,
4173,4144,4160,45998391030933,0x18f6eb1dfcda31d,4139,12710685,46669377791323,4149,4157,13452061,13452219,23609066843,12238927,4149,
0xcda6b0b991f96f436,20160156717,21954491048,4195,4150,4162,4186,12318043,51664441963564,4162,4893,50016984355690,4164,4160,4794,
44775563612360,4157,4175,26034934939,5467,54898534761517,4146,4167,26032587931,53317943186205,4151,4157,0x5d0bb58f6a726c21d555,4978,24288157897,
4149,9056333,9097284,4182,4172,4166,4168] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part473 : Refutes moves 0x10060000000000000000000000 0x66c9b14a03c000000000000000 :=
  finish #[
47984735429979,12694469,53229484548975,4173,0x183506c250a3372,4166,4170,88000315292501045,9457947,4166,11375171,27632378721,4173,5461,0x18210697c04a124,
11497548,9879622,4179,4151,8618654,4388,23606973086,4144,12689480,56505768452853,10273947,4154,12689611,10314907,4154,
5275,0x19b2eda0d1d12f6,4164,0xaf95eceda0d1db25b,4173,4168,4178,4179,0x16893641e9d12f6,53229604799058,4182,53227212878027,4173,11474066,9056838,
5173,12698496,48094406914245,4168,12243012,4150,4170,94206609047269668,84882745708553372,4175,12317266,5184,98491855244432727,4164,0x1832be0e896c424,
4151,4175,4695,53002919445560,4175,0x212a3cae15e1068ed1db55f,4168,4173,4189,4179,22460604994,10314307,4189,11531114,4984,
24994767743,20112577690,8691743,4177,4170,12681820,4147,4299,10351488,9879645,4163,11124815,4153,4195,4167,
4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part475 : Refutes moves 0x10020800000000000000000000 0x27c5d162046104100000000000 :=
  finish #[
10990937,49619265766140,4168,0x66d0f680cec1d88381cf,4153,11912352,52887560107168,4163,11465866,77251040433423705,11530297,4167,4198,90654721861247542,0xb3b8351fd174062fc,
25857602519,4154,48245756249248,4167,4153,10695355,51408597356732,4160,4168,4181,4800,5266,0x2e9867ad37770460e23f246,4168,0x174cb99a2b5f2fc,
4145,5266,53229420253557,4168,11125915,4188,4160,4195,12690082,51594950341792,4167,53125763408142,11506344,4168,26747597765,
12272795,10674247,91102020397933341,4168,4175,4181,12690205,9827101,4154,11125126,19295654247,25824399406,4147,9097510,4168,
4398,98527053594256539,5255,5275,25915147121,4167,9875513,4154,9064843,9908296,4195,4198,4178,4166,4170] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part477 : Refutes moves 0x10020010000000000000000000 0x67c59b4280c012801000800000 :=
  finish #[
4600,26780738040,53229368746855,10293325,4189,4593,0xa823b4eb0b83b6252,4178,4992,97966180775342951,4173,11502449,48247248630359,4188,4604,
13493089,56513260241485,27635508362,4146,4188,88256724698395490,20268433462,4171,4187,4195,4182,4175] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part479 : Refutes moves 0x10020000200000000000000000 0x27c499d6014002044200400004 :=
  finish #[
5170,24320460223,4159,88252191804179415,4181,10699456,44877628678432,4173,4178,0x1834ea8e2c0630a,0x1776a266ca1d487,91096521003090261,0x167b06a37b5e2eb,4143,4167,
4146,13484706,94913576426382270,0x177689e0d23f1de,4168,4181,25194521735,0xa9c67654519a890a8,11126207,0xcd9438a25aba3a4f9,4157,4163,4181,11408329,95581993637024925,
4162,47580654494665,99065419725391097,4162,41186323981467,4188,9912367,4159,4167,4198,12661216,27591570205,11514336,25824399451,4147,
42967440741332,4168,26021762203,0x18350782497f30f,4195,12194956,23549039473,17767780408,36444738011914,12689611,25914336104,9097274,9941080,4195,4166,
4198,4178,4182] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part482 : Refutes moves 0x10020000040080000000000000 0x26ec9d73a07004188118210420 :=
  finish #[
83936040881468263,0x17605556e4da3b9,8693082,9945162,4171,0x19b5365ae0ad35d,27584782778,27584881514,4160,0xae677702d4e04755a,4170,4181,5259,13472907,0x19b31e173c16423,
8675366,4170,95575001246946553,20360709270,4175,4195,47943094092960,9957884,53140232963021,4152,21166399562,4184,4198,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part483 : Refutes moves 0x10020000040000000000000000 0x26ec9952a06080088108010000 :=
  finish #[
22461392027,11126106,51231824167285,13475899,95582102443709483,0x66f28e836eac56bbf29e,4159,38164539220765,0x5d5a9c9b4efce09da365,4163,4173,4198,4168,56506042044791,9037151,
13493287,23388509343,9830485,4147,4155,47957858427484,0x177f365d14da5ce2b5d5049380,4177,5271,47898072838519,20268445773,4195,4198,4175,4398,
9098205,24394359265,4173,4175,5461,4957,9458525,11124806,4160,13477114,47939679036666,4175,54676798685574,41237289935921,11472977,
4160,4173,4181,46661980575071,4854,10351463,4168,10293325,51361039541282,12669809,4143,44877837161329,4184,0x19b7054efa340f0,25226052956,
4159,56528746046614,35329732174382,4163,25848443479,20360708159,4182,4195,4175,4198,0x19b4ed20d0f710c,23283471205,25226486751,4168,4198,
21203116790,24288051754,51494277420379,4198,4159,53210596496213,23391241045,51308615143726,47905430758239,4173,4141,25981403989,4159,11124824,4160,
4181,4295,25135776817,0x9b86b8d604f160559,4159,4155,5461,23388882076,4147,12686681,19369960602,4173,23321400474,11473462,25988211673,
11473791,4168,4170,11124813,4188,4160,4181,8676209,10330805,4184,20392981664,74431238167446357,47799078470522,4178,4181,
9912817,4159,4195,4198,11059279,4137,4144] (by decide +kernel)

private theorem part481 : Refutes moves 0x10020000040000000000000000 0x26ec9952a06000088108010000 :=
  branch 1 0x10020000040000000000000000 0x26ec9952a06000088108010000 55 0x26ec9d73a07004188118210420 (by decide +kernel) part482 part483

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part484 : Refutes moves 0x10020000000000000000000000 0x26c49952244000000000000000 :=
  finish #[
11088258,22786159248,5262,48267062518440,4168,8691814,4173,0x19ad034afa9335f,20226470091,4198,0x1834a4c568a5380,4168,4166,56525461668914,5465,
27593519978,10335098,4188,4184,56491983975371,0x19b31e50d9043d7,4171,4150,4198,24354074827,11125330,49842016470175,4187,4195,9441568,
21954929234,4198,27590840519,0x181458c230ad122,9941282,4195,4198,4182,4166,4170,13492928,83646054647308942,4173,4699,11895442,
24362479818,4198,11518829,4187,4195,27590419136,13472636,9925211,4198,4195,4291,13472414,0x80015b378231075bc,4177,0x23b835baba77364ef97755f,
4198,4195,4287,9048352,4154,4160,4164,4166,11104330,4148,8680027,0x1830bb23f9070f8,43176990590208,4154,41512975582464,
4167,4195,20158124231,43346263122791,4184,4398,4475,41237289936014,4181,4167,36389061653277,4198,4195,22769426518,4151,
4155] (by decide +kernel)

private theorem part480 : Refutes moves 0x10020000000000000000000000 0x26c49952204000000000000000 :=
  branch 1 0x10020000000000000000000000 0x26c49952204000000000000000 66 0x26ec9952a06000088108010000 (by decide +kernel) part481 part484

private theorem part478 : Refutes moves 0x10020000000000000000000000 0x26c49952004000000000000000 :=
  branch 1 0x10020000000000000000000000 0x26c49952004000000000000000 69 0x27c499d6014002044200400004 (by decide +kernel) part479 part480

private theorem part476 : Refutes moves 0x10020000000000000000000000 0x26c49942004000000000000000 :=
  branch 1 0x10020000000000000000000000 0x26c49942004000000000000000 76 0x67c59b4280c012801000800000 (by decide +kernel) part477 part478

private theorem part474 : Refutes moves 0x10020000000000000000000000 0x26c49142004000000000000000 :=
  branch 1 0x10020000000000000000000000 0x26c49142004000000000000000 83 0x27c5d162046104100000000000 (by decide +kernel) part475 part476

private theorem part472 : Refutes moves 0x10020000000000000000000000 0x26c09142004000000000000000 :=
  branch 1 0x10020000000000000000000000 0x26c09142004000000000000000 90 0x66c9b14a03c000000000000000 (by decide +kernel) part473 part474

private theorem part470 : Refutes moves 0x10020000000000000000000000 0x26c01142004000000000000000 :=
  branch 1 0x10020000000000000000000000 0x26c01142004000000000000000 87 0x27d93546205500000000000000 (by decide +kernel) part471 part472

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part487 : Refutes moves 0x8060000000000000000000000 0x77d90f8503c000000000000000 :=
  finish #[
48093681522006,0x1a7abbe0d4db2f6,13481109,9815189,10227751,4143,0x1834871da4d9380,76083122644194650,11531213,17649877047,4156,4157,4163,25989001408,5072,
20897117247,4157,4152,0x60dc149b30697f845368,53223856157553,4180,4174,4172,4573,18392109725,23349798038,4138,11531121,4167,4174,
23492404575,47713769833536,0x19bc2560f9d14fb,4154,4169,20104188860,36257494250847,4169,0xbac6beb61d590b55a,0x18f6bdddb0a3294,9883726,4156,4172,4164,46684064633808,
5063,11822422,23290209343,0x174442da7afe0b8,11460664,4165,10289213,11527408,0x9bb27abc0a6a94372,27592052820,4299,11527023,49670979956789,4169,4174,
4183,4173,4189] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part489 : Refutes moves 0x8020000400000000000000000 0x37f505a100c0080a0401000020 :=
  finish #[
0x168633d749b8367,87551520319857823,4155,4884,87521560481403835,4136,42800469041720,53022640694239,4169,4155,4183,83302720522867465,47935553778843,20900717423,25991013721,
23539081483,11116601,11104311,4179,4183,25906767102,25909114011,4142,0x181c3d10e96d2f4,4152,12662011,25907552914,11042872,25991804060,0x176e8760d2f9238,
4152,11427904,9105469,4170,4180,54925169746989,0x1a7ad790ec78437,4182,4649,0x19b6d7a0d4760ea,4160,12239027,8594487,0x1759069dfa22500,4133,
9044152,4161,4163,4169,4157,0x18fe6ec7a27555c,20737618791,4141,0x183423477af93df,4160,9392999,9392999,9749351,4131,10965015,
19239379839,4160,23609783143,23605723805,4151,4145,0x8314eebe5d61c7440,4179,4169,4144,44967606838718,5566,10699025,11493443,4157,
0xa885d2eb1db2fe2b4,4144,11428814,8422350,27577283320,11808841,4179,0x16868a10eb5f3cf,24128676831,4141,4145,9122490,9883726,4172,4180,
4684,4873,47937272722265,4143,58245195817548,50020214800827,4157,4145,21031736073,9121856,4180,12616647,27584397789,0x176f02142b46309,87060541260407579,
4169,13468125,9053145,9883721,4152,4164,24210187320,0x1740d784d2fe1ee,11427896,4149,10289221,4694,44863679972210,98743332510135122,22742250359,
4180,21158015052,4169,4174,4179,4183,4198] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part491 : Refutes moves 0x8022000000000000000000000 0x35f487c1c14444000000000000 :=
  finish #[
0x16a876dd63bf25b,46578601845319,0x8ce287365449df440,91233941441663175,4156,4164,4172,9815191,9814807,0x18fb05a6f29e49b,4148,4165,80724176835891669,4152,43333932659867,
4694,4694,43333932659867,4152,10248283,11501625,4198,9843747,49532541096125,21164741572,9842886,4142,10309809,4163,4193,
24993587399,0x174706a052f843f,4159,9842887,9105474,4180,4172,4170,4182] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part493 : Refutes moves 0x8020008000000000000000000 0x75d4a581506009100400100000 :=
  finish #[
22008386509,17671492859,56480610210370,10604591,45928160294238,10695520,4156,4174,4150,13456256,56444630688717,4161,19280831838,0x1812e89a6296380,4154,
0x69ec1f9b31e26b9c655e,0xba08f6e8946b59317,4174,4138,4169,4975,49535932949370,4152,23406117759,97939431677080918,4174,4193,4184,4189,13083785,
49689744707874,4152,4782,51357709636954,25159250911,4137,4167,0xd3b2a4d1e9f2330ef,13886615,24366015551,24415135066,4134,58246838334144,4162,4152,
4167,11100944,4154,4189,4187,0x182c0c2099c6113,0x9bb826eb516a34489,4180,94913579622068807,44454753260401,10249467,4163,9769543,4152,21857416329,
26686424412,4169,21913748824,4152,4187,4182,13471931,27609552023,40915682247228,4152,4134,22651970320,4169,4165,4179,
4151,4975,49604669203802,4152,0xcd98e31bd4b9cb494,4193,0x176c7448596d251,56578898253052,46207083983529,46207081170059,4165,10289740,58243651531422,4161,4173,
4189,10290522,0x19b2a78e810b17d,4169,19424711444,39775936893998,4156,4152,9121856,4182,4180,4184,4172] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part494 : Refutes moves 0x8020000000000000000000000 0x35d42589404000000000000000 :=
  finish #[
13472322,46224260227747,4189,13472299,21635301954,87875087806337587,4179,4169,0x205a9e88451307a0d16d314,0x28766cc7d5f26eddf10849b,4157,0x1814eda0a4d71cd,49430201533474,13472832,27575571520,
4122,4140,4128,11855007,4145,0x177f06a6cc135d30790996d223,4160,10289740,4183,4198,4189,4184,9032863,10625420,8577085,
74577006010012340,4180,27592487711,84912922604200329,48349741748718,4144,56509977174911,4198,4184,4183,0xadf3ab364b1c1a22b,26837787323,0x336639bb65bf07e0d1db2b4,4189,4169,
13472436,10335380,23482822749,4167,0xa1d9b26ecb18444a0,0xc0a83cba60d1a8440,0x19b2875098444fe,0xcd943abe4ddc1a4f7,91093531133785434,9842761,4162,4170,4160,17753305651,0xc761aca150ecd936f,
27593212476,5470,53302402675861,4155,4144,4167,56512385478854,9842761,10269255,4163,4193,4183,12706364,56513402061574,4144,
0x18e8ed116adf185,4150,12690376,0xc6d83471a3d23455a,4145,10744010,4162,4169,48212965118519,4590,0xaf62105b60d289427,4183,18648608865,4184,4180,
4172,4182,10342478] (by decide +kernel)

private theorem part492 : Refutes moves 0x8020000000000000000000000 0x35d42581404000000000000000 :=
  branch 1 0x8020000000000000000000000 0x35d42581404000000000000000 75 0x75d4a581506009100400100000 (by decide +kernel) part493 part494

private theorem part490 : Refutes moves 0x8020000000000000000000000 0x35d40581404000000000000000 :=
  branch 1 0x8020000000000000000000000 0x35d40581404000000000000000 85 0x35f487c1c14444000000000000 (by decide +kernel) part491 part492

private theorem part488 : Refutes moves 0x8020000000000000000000000 0x35d40581004000000000000000 :=
  branch 1 0x8020000000000000000000000 0x35d40581004000000000000000 70 0x37f505a100c0080a0401000020 (by decide +kernel) part489 part490

private theorem part486 : Refutes moves 0x8020000000000000000000000 0x35d00581004000000000000000 :=
  branch 1 0x8020000000000000000000000 0x35d00581004000000000000000 90 0x77d90f8503c000000000000000 (by decide +kernel) part487 part488

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part497 : Refutes moves 0x40022000000000000000000000 0x3de5d318184444000000000000 :=
  finish #[
42753927008933,26721530814,54725694607634,4156,53069181841990,4147,8664407,56511773925755,4155,4161,4173,0x19b9069434d9487,25989403698,0x16a3068b6a8d487,4159,
4168,0xb46762ee942a1d3b9,0x66cb46a7a1b821bb014f,9884827,21721637060,4134,4152,21780710361,11043607,4168,22651940915,4169,4165,4193,38198746759449,
9884040,10682428,0x802834a211828549f,21719601841,4152,11863199,10683551,9105471,4174,20034741593,26703684372,22802453659,4140,4170,47762991416095,
38198007710969,53230467155196,11518031,4170,4187,4155,4179,40503355343837,11060573,58245226452315,4138,4130,94798167752291677,11104313,23325012760,
56493023298525,10707023,4147,4989,0x19b2bad1b29d3c2,4168,5087,0x1a7d368b02363d0,4147,24413979104,9105474,4174,4170,4980,0x66eb4a5b6bf20d0af48e,
4168,25841213680,8610951,4151,25991779476,22603612198,13091591,0xc0d5a651e0d15f489,4162,10686538,4142,22675903252,51479699546907,4155,46634978091993,
0x50eba668cbf20d342438,4187,25988624583,4168,21938557006,4165,4160,4166,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part500 : Refutes moves 0x40020000410000000000000000 0x3fad6918aac40808e007001020 :=
  finish #[
5467,0x81915f3590ea7a3bb,4140,38191715439352,0x1674120dc2e636c,4141,42748057457511,0x16746e1731c5176,4162,4132,4157,21518996730,11773178,94875097653391563,4190,
4137,5055,0xc1067481575c19314,4137,0x181a81609c10309,12685616,11043994,9465935,4174,4180,8692583,0x540c0e8f306d49a3030d,4190,4141,4153,
4183,94869825018155250,36426763592551,56548573073977,0x18df1ec57afc309,4178,4146,4170,13476144,54900102911130,4146,0x19a8bb17e29e188,4162,27584459623,11105033,
46323153961352,4153,4177,4873,5260,24144708957,23524786257,4162,4170,78227989953282737,11059504,0xcda9a88926b9b85bf,4129,36461152445193,11116621,
9830473,4151,4175,4183,4155] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part501 : Refutes moves 0x40020000400000000000000000 0x3fa56118a14008086001000020 :=
  finish #[
4678,20983047034,4173,0x90735506974b5448f,0x2e9c3b41e380be4252ee175,4157,25889899449,0xb509b4b914604a4fb,26787554261,4162,4151,0x1817078e2c1a22b,22594839402,98281037849609371,4155,
4179,23433237659,25990960171,23432053915,4151,10682441,4141,4153,4190,4183,46321629241912,12690779,12690589,4970,23432512373,
4155,4179,24261350250,4164,4168,4152,5166,26007339456,12689473,49692992836361,11395128,4157,0x1834d40dc28c435,0x18341294f29329e,4162,
11105143,9106586,98571140343116575,26779091926,4175,4173,4170,4856,53072416666971,23526753048,22711489493,4151,4183,9883730,4156,
4168,4884,21880190199,49534264005396,4187,4178,5260,0xb3a5a902d4f27a15c,4187,51597509108795,97548865915941553,4155,4141,12690572,9466612,
4177,46327331050333,18649674709,20939043701,4177,4183,18650461531,19388629973,18650604294,4190,11440215,9883696,4152,4180,11124808,
4153,4174,4188] (by decide +kernel)

private theorem part499 : Refutes moves 0x40020000400000000000000000 0x3fa56118a04008086001000020 :=
  branch 1 0x40020000400000000000000000 0x3fa56118a04008086001000020 64 0x3fad6918aac40808e007001020 (by decide +kernel) part500 part501

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part502 : Refutes moves 0x40020000000000000000000000 0x3d852118404000000000000000 :=
  finish #[
53231936320276,46703710340350,4178,49965355291377,12690782,13472225,0x1682bb14f23c55a,11030609,4165,4190,0x63e9385d86aa6cc1a35a,22804530047,4169,0xbb74324f4d541849b,21938435314,
11506057,4157,9867357,4156,4152,4168,22601646731,25916252641,4147,21986845447,4178,10736391,0x90843a8f60d15f17a,11124782,53226827715001,
0x1834ec26ca7130a,4187,5373,12706876,19294879801,4178,11395774,0xcda380d75d0350228,11124827,90955935935750347,11087924,4165,4179,4193,11125602,
0xba39b2a354e1c51e6,4147,0x18346b20329c3c0,53228680795169,4187,9884138,4156,4678,5180,56578915058935,4159,22786544198,22593220664,4183,4165,
4193,20758499896,11453480,0x16826de6ca19424,11030580,4144,48035512545568,11879199,4151,4169,53191940637635,91343107121206045,4159,95568301356446967,4148,
22593639274,0xd3e2dabf974a9a2be,4169,4144,4189,4878,23541519008,4798,0x18e304578a3c299,4153,4183,4165,23539930457,49982381716829,53226921243519,
4164,0x18f8d2a0d16d55a,25989403995,10736317,4177,4165,20244427530,4148,4190,4183,4193,11125915,48126050812472,22657933513,4175,
18581483603,4170,4182,4178,4168,10342478] (by decide +kernel)

private theorem part498 : Refutes moves 0x40020000000000000000000000 0x3d852118004000000000000000 :=
  branch 1 0x40020000000000000000000000 0x3d852118004000000000000000 70 0x3fa56118a04008086001000020 (by decide +kernel) part499 part502

private theorem part496 : Refutes moves 0x40020000000000000000000000 0x3d850118004000000000000000 :=
  branch 1 0x40020000000000000000000000 0x3d850118004000000000000000 85 0x3de5d318184444000000000000 (by decide +kernel) part497 part498

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part505 : Refutes moves 0x2060000000000000000000000 0x7ca94bc143c000000000000000 :=
  finish #[
0x19b2ed45129c2fb,4893,8631340,17675011319,23558352952,4150,0x1a7abfd4e16c55a,4171,4151,44296930452733,44414672934237,5466,90529983949030126,25143001142,9056325,
4172,48108434735295,11498352,4150,4167,11461405,46666911138462,4152,0x5aeadf6bcd3174cd92f6,48366938423777,4167,0x4d8ba02d0a714a04a55a,4172,4171,4887,
9057053,0x5d126e0e8e8c51aff3de,51300459803684,4126,22735401347,4148,4142,39570048115177,0x3379d14dc146a582304a3c7,4170,4171,4172,21787562781,98805366674567852,22777811012,
4152,4154,4173,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part507 : Refutes moves 0x2022000000000000000000000 0x7dacc346404444000000000000 :=
  finish #[
13484228,56564891341758,95105495093077341,4161,4188,12317750,0x66f415a7d3714d9bd5be,4878,17768547295,4171,4167,4175,4159,4475,9064736,
56558388982653,9064736,4160,4171,4178,4162,44342547682064,5466,40709563765108,4168,5471,10965167,4149,10244880,4162,
4147,21718381728,11072858,4364,22456492816,4149,4145,10245280,4162,11431987,4134,4142,11530741,4159,4406,
5068,0x1828a3e0a8b5424,4188,18701350038,9941055,9908303,4178,4190] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part508 : Refutes moves 0x2020000000000000000000000 0x7ca46340404000000000000000 :=
  finish #[
22677865438,22398628637,46442792989144,4162,42883951354614,4192,4184,22786597754,0xafe80ce894e29d16d,0x8ec77ebe54e8a1288,4164,22660362624,4145,4175,4159,
0xadf77f3669f296315,12318044,0x50aa9d9b71fe9f2ff42c,11898934,4151,0x18e2be14e53e440,48246678533269,4154,28440498453,20982182784,4142,25226323391,25227658184,22784200759,4188,
4192,4184,48246568760092,95108809253958302,11125244,4167,4188,45991404082125,27618411469,11124799,13473215,46671782462813,4167,11847005,4134,
95583811396129235,4184,9908308,4386,12280689,4159,17385882350,12280689,11124799,38296974979122,4154,4162,4170,4190,5154,
5269,53146094871586,4138,98553783423943744,9491306,4183,4192,4165,11461696,91106672712344421,9072696,41077671502606,4175,4170,0x3371a6a758e610d4e1c5153,
4678,22786544472,4160,0x50acdd747364ba29c372,0x44dcd938aa7173af7424,4142,4175,4183,9130656,10707800,44501073523776,21729141704,21729170476,4168,4131,
23346238135,9945176,4175,4183,4588,0x54e4d98fa8f05496b22d,23389762513,48245615186980,10736312,9957464,9908303,4187,4183,4170,4178,
10342494,4171] (by decide +kernel)

private theorem part506 : Refutes moves 0x2020000000000000000000000 0x7ca44340404000000000000000 :=
  branch 1 0x2020000000000000000000000 0x7ca44340404000000000000000 85 0x7dacc346404444000000000000 (by decide +kernel) part507 part508

private theorem part504 : Refutes moves 0x2020000000000000000000000 0x7ca04340404000000000000000 :=
  branch 1 0x2020000000000000000000000 0x7ca04340404000000000000000 90 0x7ca94bc143c000000000000000 (by decide +kernel) part505 part506

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part510 : Refutes moves 0x1060000000000000000000000 0x7ea91d30a3c000000000000000 :=
  finish #[
17643979727,4893,12710685,0x18354ed4310e154,0x181507d4e039300,4162,4163,4157,11121437,11124936,22777811920,9039958,4164,4168,4166,
4785,84737153760342208,19447141053,4177,4166,0x183834d1ea30166,25221256133,17409344189,19423937886,4169,39833374938462,4154,4166,4283,12690375,
22619194523,4152,4182,0xbaa9ba0dc7b9440bd,46688085979411,9863254,4151,4155,41119475925760,53231282119340,10289210,4148,4168,21116863352,26779894939,
25992201262,10313779,4893,11125438,0x1830bc0eb2ff3cd,9494614,4166,4175,11125824,0xd3d1f70614e2ff43f,21158015062,4168,4169,4174,4188,
4183] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part512 : Refutes moves 0x1020008000000000000000000 0x7e950d10206041020400100000 :=
  finish #[
22482514671,9040625,4162,18583507740,4182,22418170820,0xb434dd4f8a3288297,27617198117,0x29c29dcdd3a0a3e0aa9d559,4166,10330705,4174,4183,10253048,4856,
0x24e5370080ded3dac1c72f8,4164,12313373,4160,4167,28415685405,10253048,4169,22477403285,26032587612,4146,9495200,9891907,4162,4166,
4495,9925581,4182,13886603,53108357841963,4182,21838263645,97795500360401580,4173,4148,53160120767728,11125330,4888,9876050,4170,
4166,25943073560,49590727729660,21166420042,4173,4169,4174,4189,93954837281833200,10290336,26033746683,11821100,4155,0x8d200ea71d39d5087,9941472,
4166,22593192014,4151,4183,4190] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part513 : Refutes moves 0x1020000000000000000000000 0x7e840d18204000000000000000 :=
  finish #[
0xc1a51102daaafc1e9,9401213,44382757872412,4166,10351185,4184,4174,0x66d1ac0ec6a94f293499,21720400480,4159,20395000607,11043409,11059846,4130,53261489078851,
4159,10985984,20394214435,11518015,4155,4163,4187,24974426900,20337116205,4155,11133997,21166805791,4184,9875968,4182,
4174,4166,4190,11764781,10232978,4144,19060761755,49997957858450,94859479247253881,11124784,4188,4146,4866,4866,17787659419,
4159,4169,10252577,10985673,21000155425,11124795,4146,4167,49861584257603,17787384478,4136,49862325289544,4155,4162,4163,
12690284,27627996509,4129,40997445207487,23522321443,4159,4155,41372935324615,4148,39483150549356,20989772955,10309695,4174,25990202095,25989809103,
4168,97820618856629199,53228672119473,9928778,4175,9896995,10682967,4184,51164806116098,4182,41652830012357,0x2e89a6c76839068bc35729e,4154,4785,24973189708,
4173,4174,11125291,21122819021,4173,46630864155203,94869924860641888,9929201,4167,4163,4187,5080,10290119,22744260700,4148,
4155,4162,4169,4190,4183,0x5ae2f383e27c2384a28a,17802568268,4189,12239629,98628121144189706,4162,4888,44621683881115,4168,20370519179,
10310215,4163,0x17590551b97c360,11133720,4162,4169,9957880,4170,4187,4182,10342494,4166,4181] (by decide +kernel)

private theorem part511 : Refutes moves 0x1020000000000000000000000 0x7e840d10204000000000000000 :=
  branch 1 0x1020000000000000000000000 0x7e840d10204000000000000000 75 0x7e950d10206041020400100000 (by decide +kernel) part512 part513

private theorem part509 : Refutes moves 0x20000000000000000000000 0x7e800100004000000000000000 :=
  branch 2143 0x1020000000000000000000000 0x7e800d10204000000000000000 90 0x7ea91d30a3c000000000000000 (by decide +kernel) part510 part511

private theorem part503 : Refutes moves 0x20000000000000000000000 0x7c800100004000000000000000 :=
  branch 1 0x20000000000000000000000 0x7c800100004000000000000000 97 0x7ca04340404000000000000000 (by decide +kernel) part504 part509

private theorem part495 : Refutes moves 0x20000000000000000000000 0x3c800100004000000000000000 :=
  branch 1 0x20000000000000000000000 0x3c800100004000000000000000 102 0x3d850118004000000000000000 (by decide +kernel) part496 part503

private theorem part485 : Refutes moves 0x20000000000000000000000 0x34800100004000000000000000 :=
  branch 1 0x20000000000000000000000 0x34800100004000000000000000 99 0x35d00581004000000000000000 (by decide +kernel) part486 part495

private theorem part469 : Refutes moves 0x20000000000000000000000 0x24800100004000000000000000 :=
  branch 1 0x20000000000000000000000 0x24800100004000000000000000 100 0x26c01142004000000000000000 (by decide +kernel) part470 part485

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part517 : Refutes moves 0x10100000000020000000000000 0x2f82d984800401000100004042 :=
  finish #[
5467,11117915,27601605482,4184,4136,27602818207,25186432140,4184,20225593539,4162,4301,5274,22594045274,9875544,4158,
4301,90716395208176987,8675390,4171,4177,4174,56530548008384,12628850,54672661410967,4151,4181,9864538,53109318111424,4168,4162,
98909455282537818,4177,44209923794269,0x17765b26d2f14fc,4173,11891584,24347275459,9057248,4160,4164,4162,20302320690,4686,0x18f6814ba35f3bd,4171,
4181,9941497,4178,4186,0x183cee9d89d2424,0x1776580268b05bc,4181,23434470147,27601604859,44673770308661,4159,4157,83012496154068011,4174,58193800455228,
38042607207765,4159,0x568b3f0daec4e90b25c0,0x6369d28f62c9d0174558,4159,0x31dc344da81a5d05917f3b9,4178,4186,4171,4198,38215842346330,58196090086554,39672953541984,4140,25217708920,
4174,18676843872,38253656274060,9912402,4171,10326118,9958554,18572685619,21174804557,4165,4172,4177,4190,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part519 : Refutes moves 0x10100000004000000000000000 0x2f829ba0880220020101080800 :=
  finish #[
72279736001077828,0x4e188805eeedd304c29b,0x44402f8f2e9826162244,4169,4157,22695486612,97900659160531936,4157,4986,0x50d3489b8be5ae2e8494,4159,20152185705,8699978,4174,4171,
38969342271661,17829618748,4174,24322097845,0x1774d4dd52ee560,4165,5465,11527514,10305621,4302,11838816,12297065,51183461376873,4139,4135,
0xad8768b866fb53304,10326068,41699453551364,4165,4160,4170,4182,4157,97428249546425693,21628830091,4147,25107379546,46474566329189,4178,4170,
21110817332,53233639604511,4155,51307775501268,10297631,4155,36390932694264,4172,4170,0x34ec3bb3f5a2869dbba0311,25051508935,9896018,0x56a1d9740edcb817c43c,4182,4198,
4190,5153,18573918412,4178,9831580,51127940510565,18656993344,4189,4181,4171,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part522 : Refutes moves 0x10180000000000100000000000 0x6fa6dda1fa4022008000a00000 :=
  finish #[
11505957,9020282,4155,23606993179,4141,51598118290587,51594121425262,20227683577,4150,4170,4985,22752985959,23491625760,9478198,4171,
4159,25035511131,4491,56497015075808,25176056203,4134,4154,4159,51565447135409,25929499405,11502449,4159,4143,4151,17820045666,
0xa048362497bb5c491,9875519,4968,46495162765694,4177,0x63741a37ae9c21046497,4169,4171,4170,4172,4174] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part523 : Refutes moves 0x10100000000000100000000000 0x2f8a9981924022008000800000 :=
  finish #[
51239938417439,0x50d53b9b48e63989f489,10621216,4144,4156,21586547755,24378303531,4139,51307093873629,5163,8626850,4159,4162,4156,5076,
5371,24396382580,4151,4169,0x16b4ea9772f6560,23539884725,4169,4165,4181,4157,22654329499,27584004273,4181,91003215741034753,4162,
9458747,18423333853,4165,21149638946,4162,4698,0x6059d99be67dad22817e,4151,21812331383,4165,91879438913351964,4174,4198,4170,4182,
25988977707,0x183d351d5419105,11387867,4155,4159,22743433821,4162,4488,9036168,4151,0x1826cfdd8c1a42b,0x183535209aeb42b,4162,0x1810bf10d0fd3c0,8675387,
9109578,4173,49778890154651,44435951592800,9863455,4151,4163,0x69dc1e2d106852846560,4170,13075611,0xbbc29537e0d2f9433,4152,98745135633916198,4178,53229528499071,
53229528544127,4162,9117763,4181,0xb3f754becb80b228e,10998150,0x1834be17b0a355f,4174,11781471,53225360876477,4173,25035510743,4162,25116984261,4159,
4155,24272147803,0x94650937a0d16c55b,4151,22810575627,4170,9117991,4173,4177,0x66fd3b83537977a6a371,26804347965,27635147931,10276909,4165,4763,
0x6074de7551e0ea1dc560,9117772,9912401,25933505179,12690368,25907864206,21106466890,20335542353,4178,4186,4182,4190,4198,4171] (by decide +kernel)

private theorem part521 : Refutes moves 0x10100000000000100000000000 0x2f829981924022008000800000 :=
  branch 1 0x10100000000000100000000000 0x2f829981924022008000800000 91 0x6fa6dda1fa4022008000a00000 (by decide +kernel) part522 part523

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part524 : Refutes moves 0x10100000000000000000000000 0x2f829180804020100000000000 :=
  finish #[
13472925,5466,42925724882075,4144,27633112410,25184957786,18480779331,4162,4168,13472914,8675704,4168,0x8fd9b2d720c16236a,9425475,87908571436151166,
8699971,9109582,4181,4177,21962376345,20152132288,95441423725506933,54774945780782,95679389483910388,10256444,4150,4160,4165,56540065739530,28413228380,
0x81335ad4c7bd3b0b4,5468,51189244446040,11493417,4181,0x175b36d7b03a55a,4162,10256445,4165,19253363580,53019153392986,19389551476,4186,10257274,18623438912,
4181,4171,4179,13472733,19304932507,27594380253,0x33654f0fda7670c198a4286,4163,4157,4155,4977,22510900477,46100762371227,4168,28439225690,
11117914,4162,53225357349151,4177,4179,4172,0x226a0ccd9384bbe6c16b3dd,4150,4174,13473119,49419707766111,27591623038,4159,4155,24280167775,
11891663,24419905731,4164,4160,4162,42924126365018,24120202397,56616480916220,4165,4162,25019933318,0x1772ee902c11377,25989431362,4163,23481602920,
4150,9941492,4178,4186,5266,9467026,4153,9425195,4179,98636383627760989,9110584,25988477372,10297390,4160,4150,
21093270874,56511808258820,11493971,4165,4157,0x19b25e0e90b23c2,4171,22811316531,11501875,4159,9941492,4186,4174,4198,9942170,
0x8aa5bc2ca6d04d153,4173,58247652476143,85016500036289599,4184,0x19b22c8bfaef371,10338382,4160,12698246,9929885,41562073325643,4162,4172,4177,4187,
4182,11907166] (by decide +kernel)

private theorem part520 : Refutes moves 0x10100000000000000000000000 0x2f829180804020000000000000 :=
  branch 1 0x10100000000000000000000000 0x2f829180804020000000000000 44 0x2f829981924022008000800000 (by decide +kernel) part521 part524

private theorem part518 : Refutes moves 0x10100000000000000000000000 0x2f829180800020000000000000 :=
  branch 1 0x10100000000000000000000000 0x2f829180800020000000000000 62 0x2f829ba0880220020101080800 (by decide +kernel) part519 part520

private theorem part516 : Refutes moves 0x10100000000000000000000000 0x2f829180800000000000000000 :=
  branch 1 0x10100000000000000000000000 0x2f829180800000000000000000 53 0x2f82d984800401000100004042 (by decide +kernel) part517 part518

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part527 : Refutes moves 0x40100000000020000000000000 0x3eaa4f44800050000100004018 :=
  finish #[
49344430575871,11473770,4136,4382,20783666418,4153,43061554099546,4142,4166,12297370,25981395424,10661944,11375474,49935137977489,4137,
11916124,24406758545,11841577,24253739401,4166,4142,0x18208ad4829e3c3,4155,4165,4169,13476130,5261,26819777394,11343195,44041511584532,
9048137,4158,4156,5278,54899296048366,12202044,10285090,4157,0x17468acec9dc55a,4175,4180,11863387,9467028,0x174d371ddaeb5bc,4130,
4162,0xc0d9b4bce0eba355a,9466740,0x1776d757da2a427,4147,4183,25959052429,26014901177,4130,0x183abb1152fc23a,10297395,4175,4155,12203067,26821067095,
0x16711f5dd3a31d6,4120,0xc0c8faa417dbb41d6,4147,4155,51303888343239,4166,0xc7d80eb466d1cf126,0xd3d746ee8e7a37428,10338391,4192,4172,56455898964524,13493205,10659167,
4153,4183,13476432,13477005,0x8750cf042062303bf,4147,4183,4978,0x19b4bc4e7a3749a,4183,4160,4172,21191533919,0xcd9454a20258b01e1,4183,
4175,13476708,0xc6e8da41e6d2f1493,4168,21519864968,98572838608417414,4137,56599232709788,4169,4225,27636372255,43057451692075,4147,4172,4785,
25981477469,4192,12673977,40914809016870,4130,98353125907338299,4192,22591964012,17826512947,4173,4175,4673,39453774033882,47889917825917,4164,
4156,4989,20127396917,4138,0x19b31d8509cf55b,4172,4190,42888169623846,9109710,4183,10342479,4166,4186,4181,4171] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part529 : Refutes moves 0x40100000004000000000000000 0x3eaa0f2080a020020100600800 :=
  finish #[
12678285,5261,0xc7c67306a0ba2a5bc,4183,4147,0xa1a9b453a9ec0c290,74318645366477684,4130,39711372521915,19386721421,4155,21147968561,0x44f3a3819068231dc49f,4165,4172,
4175,25159373884,5368,54913271886495,10683039,54912417129119,4175,4172,4165,4171,0x60d23d8f8119d03aa365,4127,4147,4170,46171126801051,
53296469156794,11875487,10662475,4160,4148,36512819155611,4180,4175,58228802970192,23408521803,25905980666,9871444,4169,44433526923851,11527211,
48077144441417,4175,4180,4160,4165,43058980827831,19262140978,9441872,10342487,4186,51523075560301,25159390162,21151986256,4192,12271692,
4160,10342992,0x31b9ac9a983a8797f1cf300,21026112648,11396062,51651499066207,4172,47803047862841,10342472,9871450,4161,4165,53229595214685,4991,25179706409,
12658013,98349397344862231,20184944716,9109569,4175,4169,4171,4181] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part531 : Refutes moves 0x40100000000000100000000000 0x3eaa0f02924020280000800000 :=
  finish #[
12617151,91815546806010407,4154,11842237,4165,18509570529,12701983,4168,4157,22661898527,0x1825068230a52b8,4172,13452446,25990968467,5467,
25863447693,11862077,4165,4183,27634807753,11482463,4138,19305218941,4147,48165630615944,19305697947,10658273,4159,10297395,4165,
4155,51406824564159,28441609468,9049243,10326074,10338370,4172,4192,4170,0x9448f6ce6041d921d,26802640017,4152,90602459882312272,0x5ddc1e13a8ac26b411e0,21022933946,
56543467201114,11911252,4157,4175,4184,0xa8c81c6e20c9dc4f9,22710678111,4162,12256603,12296574,4134,90998067475374736,21604066363,25186128158,4160,
0x1a7c86826a9343c,4137,4151,4186,47799960445321,0xa9a370420e52fe35f,0x4af99c5bc3f4e79de559,4180,9871446,4157,4173,4165,5256,0xae69bc6e17f1d455b,9871436,
20766892715,21830686041,25990255288,4172,4160,13492816,53227120862251,21939348335,4168,9871424,9109565,4183,4688,10683160,4183,
9871665,10342477,4186,4171,4181] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part532 : Refutes moves 0x40100000000000000000000000 0x3eaa0700804020100000000000 :=
  finish #[
4683,0x16a2b6cb51ca43d,39536175342137,4141,4173,24146322370,0x167026da82e955c,4160,23406093241,0x19b2d28afadb31f,11505714,4157,23432519966,24304071834,22593220654,
4137,4183,53001948751196,11916735,4174,77657778769658708,56524598849986,4142,4148,21008192860,0xba32107207bbbe37f,4137,4157,24256553426,0x5ddc175cc5a9d19cf286,
4157,36511216952077,4175,4182,4180,12690579,25194050513,4162,11863391,0x1839351a5a05352,36234391568847,4157,4159,4742,41017092486286,
0xa05824e8c4c0f4428,4161,10215485,4150,4155,0xba31fb01e091dc30d,21065753755,17700630920,4168,4162,4172,25990178143,27584062513,25990255288,4160,
4172,0x5154179b33797f16a179,4157,10347871,5471,18333369498,4172,10708319,5471,25891148471,4172,13471830,5466,0x23500141200d03a6c84b0ea,10657878,
4141,4153,4183,12641328,51223602648220,19303628870,4986,25989857875,4182,4180,4160,10338795,43399386956936,4179,4169,
4175,4991,11506056,4136,53006149084505,23606264009,4175,4179,0x18342954284d43f,5465,44708447187812,4157,0xc0b09a2c0e91de36c,4175,4192,
4190,56426728981651,21879440134,56423389979211,4162,4192,11482267,9426060,91778886681285166,4174,4183,27635135071,0x5079ca460baddd285555,4183,25990959878,
21024990066,4157,10339199,4180,4160,4192,11842814,49344201696412,25989390390,4583,22476985210,46327297598311,20183711828,4175,4179,
4169,10342477,4161,4186,4181,11907147] (by decide +kernel)

private theorem part530 : Refutes moves 0x40100000000000000000000000 0x3eaa0700804020000000000000 :=
  branch 1 0x40100000000000000000000000 0x3eaa0700804020000000000000 44 0x3eaa0f02924020280000800000 (by decide +kernel) part531 part532

private theorem part528 : Refutes moves 0x40100000000000000000000000 0x3eaa0700800020000000000000 :=
  branch 1 0x40100000000000000000000000 0x3eaa0700800020000000000000 62 0x3eaa0f2080a020020100600800 (by decide +kernel) part529 part530

private theorem part526 : Refutes moves 0x40100000000000000000000000 0x3eaa0700800000000000000000 :=
  branch 1 0x40100000000000000000000000 0x3eaa0700800000000000000000 53 0x3eaa4f44800050000100004018 (by decide +kernel) part527 part528

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part535 : Refutes moves 0x2100000004000000000000000 0x7c82eb32800008020108010800 :=
  finish #[
0x81e5d2ea26e1c329b,4301,54721668031343,4157,4141,0x2b79419a04da05e6caf649a,12305263,4175,56545335489277,4136,4142,21696415166,56614783919550,4141,0x69ec169b336d15a833ba,
56613853242011,4152,4142,0xd3d6725de6dcdf085,4975,0x95a8206f4bbb473c3,4174,10285125,10305742,0x100c868de95509a75170a8d430,4168,21152788686,0x605adba7b36d4184d317,25048700060,85408813085741393,
4166,4152,10338397,4170,4175,4180,4187,17809711597,4989,22642750293,4152,9085515,4585,0xa1a5b8bf05504d5be,9945172,
4178,4175,24205423474,25964986766,4159,10285643,10707836,44828689474906,4142,4178,4187,4292,54825710829766,4178,9913400,
8704489,9945593,4190,4178,4187,10342479,4166,4186,4171] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part537 : Refutes moves 0x2100000000020000000000000 0x7c82cb1c814000040100004200 :=
  finish #[
0x16ae2a8259dc488,0xa37678892062d7493,17744949453,10342479,23592240474,48293996680052,4168,11055996,35465458962674,23390164416,9084975,46491746227042,4174,10342479,4181,
0x6038975c337ce51cf491,0x59d90d5b2b8e6f1ca424,22389208032,50011065226686,4165,25998992022,23516397622,4163,23590302302,4166,4178,4701,21026071494,25158959170,9957881,
4178,4175,4190,4187,4186] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part538 : Refutes moves 0x2100000000000000000000000 0x7c82c310804020000000000000 :=
  finish #[
54842660184953,54804423238107,4157,23565874031,4975,19273724979,8626222,4159,48242374390931,4174,4162,4688,42885468451679,22576816988,43059677073982,
13095791,23610242400,11382831,0x18e31d9a815623e,4169,9924677,4174,4178,4170,0xcdca7cb814eb504fe,87727284390196154,4142,21838287235,21023768759,4162,
4157,10592439,4670,0xb504345ecdeaff115,4166,4174,0xa9d83336d0d1d9174,12685886,97971023644828826,4143,25981457244,4162,47952985846556,4166,10338382,
4180,4170,4175,4187,17809711486,17810973277,4192,4703,23547097695,9879629,4159,0xba583cef0230fd3d5,0xae41fb3514c09e4fe,9957443,81533377960620988,
22584009572,4147,10285331,42835489124530,11924340,0x4cfd3e5dc6f579a9f3d8,11518012,4178,4170,4163,9945294,0xae48ec1354c178433,9912615,4159,4163,
10342479,4181,4186,4171,13472126,5466,19302822178,4154,4168,11055681,10342782,4161,90262712477122942,4156,20938662688,
42882379862803,4174,4889,0xc1b5c6700248fd48c,4146,9085130,10342469,4161,4175,4181,0x183306e6cbbc2ac,9007293,4156,51219625587770,4174,
48226939818382,4171,0xa6d68b36cd8c0628b,12284203,4150,51644114355253,4159,18607473022,9957580,4174,4178,40910723080568,20335943952,21190209707,97969548062880826,
9908299,4174,4186,47716306740378,11109344,4171,0x5028377468f51597337f,4166,46237146387386,0x2b4e9f2fe1faa7d41d3f28b,4171,22753047409,10326086,10264655,4157,
4192,4187,11907166,4140] (by decide +kernel)

private theorem part536 : Refutes moves 0x2100000000000000000000000 0x7c82c310804000000000000000 :=
  branch 1 0x2100000000000000000000000 0x7c82c310804000000000000000 53 0x7c82cb1c814000040100004200 (by decide +kernel) part537 part538

private theorem part534 : Refutes moves 0x2100000000000000000000000 0x7c82c310800000000000000000 :=
  branch 1 0x2100000000000000000000000 0x7c82c310800000000000000000 62 0x7c82eb32800008020108010800 (by decide +kernel) part535 part536

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part540 : Refutes moves 0x1140000000000000000000000 0x7eeb19a8aa0000000000000000 :=
  finish #[
54727405437160,11092743,4145,12703071,54932879287740,9424960,46525120037615,25873150729,4154,0x168a6f947c1a17e,11907136,4140,4149,11907559,10592543,
12697887,9020573,11128885,4168,0x16b71e05010e49d,8675523,4168,4172,4166,4169,54932828955688,0x1a76a3e0bc1a42b,4295,25988182211,4164,
4169,4166,17360254107,17385498046,26818892952,4136,4132,49949775644096,4147,11121822,0x17414fd7841c2bd,25988158236,11497540,4158,9879622,
4159,26781516648,19305706344,4140,0x4d5a8f6b61088741a3c5,4160,19446285253,0x9426b60420b9ab5c0,19948380716,41443324964937,4182,9134143,4181,4183] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part541 : Refutes moves 0x1100000000000000000000000 0x7ec70988800000000000000000 :=
  finish #[
10232586,25216443356,25052238525,92199174189679580,4141,4165,9896017,11907651,25921049457,4161,12689604,0x31c51241a086709ada3c30d,4159,0x16b6a317829e48e,20225609926,
4178,4162,4172,0x2030d340b7541194a353488,0xc1d0891d84f41a49f,4149,0xd3d768d484f41a49f,24302080666,46445996668348,24993952620,11120707,9891924,4166,4154,12702549,
53231214126232,4150,25160955134,0x177cb9dada8c11c,4144,4158,4887,22657799323,4141,8556711,51524587438871,4180,4177,51531951895585,9912382,
9957439,4183,4187,4182,58267334189320,4446,8574304,4148,52976803599515,4156,4141,98926349419271323,0x18348597d8a0558,4169,4163,
53282810917439,5275,53093607039639,4165,4296,8680603,11924439,4154,4163,4172,4189,4180,11515035,53114243752205,49862255342751,
9855060,11907145,4131,4593,79763718213681923,13889895,20044633131,4180,19189048153,20302000181,4178,9134166,4183,10232777,10232593,
24347144767,11076544,4141,95159835108360894,4178,4177,4172,11907651,24388428557,98499100117676607,4792,8700793,4173,4177,4178,
4172,4158,4881,22684640014,4159,42371181294738,4158,0x16b4bdcba0b6438,9945169,10342491,4166,4181] (by decide +kernel)

private theorem part539 : Refutes moves 0x100000000000000000000000 0x7e820100800000000000000000 :=
  branch 2143 0x1100000000000000000000000 0x7ec30988800000000000000000 90 0x7eeb19a8aa0000000000000000 (by decide +kernel) part540 part541

private theorem part533 : Refutes moves 0x100000000000000000000000 0x7c820100800000000000000000 :=
  branch 1 0x100000000000000000000000 0x7c820100800000000000000000 97 0x7c82c310800000000000000000 (by decide +kernel) part534 part539

private theorem part525 : Refutes moves 0x100000000000000000000000 0x3c820100800000000000000000 :=
  branch 1 0x100000000000000000000000 0x3c820100800000000000000000 102 0x3eaa0700800000000000000000 (by decide +kernel) part526 part533

private theorem part515 : Refutes moves 0x100000000000000000000000 0x2c820100800000000000000000 :=
  branch 1 0x100000000000000000000000 0x2c820100800000000000000000 100 0x2f829180800000000000000000 (by decide +kernel) part516 part525

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part546 : Refutes moves 0x50004000800000000000000000 0x2efba3116c012005e000800100 :=
  finish #[
9441763,18516718051,39266454360352,4151,4148,11449108,42323589854146,9441585,4171,0x50335c3714ed069051e3,4884,22708580826,4146,4158,4148,
4164,4144,0xadb13f4ecb129a2eb,48177940726243,4171,0xbbb5e6bec5829043b,4148,4155,47718907630748,4881,10257852,22685922157,4154,4171,4155,
36034898137442,25015550520,0xc7e26b4edd3bbb4fd,4144,4164,27590852988,27591582070,4145,4141,23459632271,0x19b2588838b031f,4169,4186,9466161,18499940657,
4130,23323427121,4155,11453190,48316042310406,4154,95407889596715373,0xadb7762c174a9a49d,4151,4169,4144,4384,9372925,47613257122241,21588591444,
4118,0xc755a641e381c80fa,4175,11518828,4179,4186,23541551138,4157,4160,4173,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part548 : Refutes moves 0x10004020800000000000000000 0x66fb0f151e0162146804904100 :=
  finish #[
28415210531,0x1694e8a9dcd7160,4155,13091475,4171,5184,0xb531b8d363e097496,4144,77393440963317935,4151,10293300,11375387,0x21add1239a7621033a22314,13471787,43028806546780,
38970078335351,19029251418,11046975,4183,4148,0xc7476c71e9da2d31b,4972,80369098938717428,4135,4681,0x4d2a39534a457a2fb0e9,4154,4155,4195,5175,
0x168a721afa9255f,24344810650,4166,4154,4795,10650578,0x66bb451e08a1492eb31f,4154,4195,11137114,4157,4171,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part549 : Refutes moves 0x10004000800000000000000000 0x66bb03310c0120046000800100 :=
  finish #[
0x2a0c092399b34ece44df35c,24986350847,10720608,4156,24172295119,27642254580,4146,11486061,4155,4195,4171,4534,11514732,4171,27644740853,
23431246717,4169,4139,13464312,0x1744ba53bc1c560,4195,0xd3b36abb174a2d4a0,4156,4180,4144,0xd3b2c53650e23a3e0,46251180160344,4164,4486,4896,
10724704,4169,23541551194,4160,4157,37560698847715,0xb3f8eb1d16a3a65c0,0xa825a83cdd34113c0,13873225,79925138386650269,11830101,0xd3b2840e26fa9055f,11911237,4157,4159,
0x337e39289776428aea212fc,4144,0x18e937dd3289156,54947296793946,20849943996,56595824977151,4195,0xa7c1b11f96a289133,4127,4148,4171,27641193919,12301154,10645562,4144,
56599291343595,0xa897774fe36c7955f,22006423600,4157,4181,4192,37027402199906,12682003,11051712,23566704700,4165,4491,95436070202189055,11505732,0xb4e524eed732f6427,
4141,22635066194,23365739665,53245744406799,4141,9302101,27610015072,11137817,13062219,10268740,4148,4153,49505614111999,0xcd9164a0dd12db3c2,47991180317664,
4144,4154,20152542155,4157,4403,13472051,22626763059,4155,4875,94702436720072026,11493455,4157,4192,12276586,11105335,
10289211,4158,4148,9118294,18675761931,4170,0xc0e689365730b229d,90718151008526722,27592790978,98361750277951883,23323456245,4155,4171,23515931500,4795,
10744115,4156,4175,4181,4192,21158031450,4169,4174,4179,4178,4183] (by decide +kernel)

private theorem part547 : Refutes moves 0x10004000800000000000000000 0x66bb03110c0120046000800100 :=
  branch 1 0x10004000800000000000000000 0x66bb03110c0120046000800100 77 0x66fb0f151e0162146804904100 (by decide +kernel) part548 part549

private theorem part545 : Refutes moves 0x10004000800000000000000000 0x26bb03110c0120046000800100 :=
  branch 1 0x10004000800000000000000000 0x26bb03110c0120046000800100 102 0x2efba3116c012005e000800100 (by decide +kernel) part546 part547

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part552 : Refutes moves 0x10006000004000000000000000 0x66be9305ca023c00c029080030 :=
  finish #[
51135958725885,74415622380561458,4164,5176,4770,44549632332853,19363656760,4178,4171,4156,4150,5568,24306499783,4130,17393107804,
35631637853140,4174,54708686131789,4140,13472418,44557813019484,4164,0x3369dd41e6829d66ca8a42b,4142,4156,4192,0xa079b46be3a0ea260,0x337dd353b5b736479b5a49f,4159,0x16a6e9e6c9df158,
43419582284763,51423368041428,12296252,4143,4144,13472908,21199020882,8995588,37732390405366,37734781281028,4150,13471785,11018284,4169,4190,
13472309,10617440,11075783,4172,4173,5466,0x69dc7567f36421bb7427,4190,0x17414fcacbbb2a2,4144,9896132,10616895,11514913,12190588,12285174,
4140,21201842969,4184,4173,10560765,77356575575733494,4150,0x19b2a423e28a260,4184,44530809635708,4175,4159,52953929990507,0x6054df8eaa626cafc435,18506777184,
4175,11419711,4139,4178,4195,4171,4155,4179] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part553 : Refutes moves 0x10004000004000000000000000 0x26ba2305880220004021080020 :=
  finish #[
38149722182796,0xbad8f26d26c8ac186,26798298158,56514205352237,44678073246971,4184,10723405,4186,4157,5176,44466136277382,4186,44538975327082,37939554771744,4157,
13472515,0x9388320bd44cdf171,22626313172,11493455,4157,26831851983,11887485,4162,11051895,9109592,4171,4183,4173,19414278937,98175190058005184,
4150,4875,26746007831,0x18fe89d4fa3949f,4180,4175,22809703271,77348102550783322,0xcd95cc41c540b25bc,4173,4175,4183,4179,5268,47717318234486,
44965231719258,4198,9252960,0x17685757a3ad311,18952557331,4198,9879831,9880922,81106028067587220,4165,4180,4175,4155,22694290106,84534171156866301,
45810260058779,11924045,4144,26829460064,4178,4198,84455654236562271,4175,4183,11124813,4160,4174,4195] (by decide +kernel)

private theorem part551 : Refutes moves 0x10004000004000000000000000 0x26ba0305880220004021080020 :=
  branch 1 0x10004000004000000000000000 0x26ba0305880220004021080020 85 0x66be9305ca023c00c029080030 (by decide +kernel) part552 part553

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part555 : Refutes moves 0x10004000000000100000000000 0x26ba0b218a4022008000000804 :=
  finish #[
17778046303,27635925752,17778524920,4195,4139,0x1744a7022a91560,10720018,21955244811,4144,4180,4156,0x174406d4504737a,0xb5c5cd378af2f64ee,4141,48258850825564,
25068299000,49931058696952,9838671,11137069,4164,4157,5153,0xba04401b5352e10f6,4152,4283,45810350691572,4152,22517760054,76113148017238354,0xaee5fcb513e10a560,
9117765,4171,9896243,58192783733483,45806097642844,4154,0xbaa8ff4ed7b341306,0x4338045ec0284a89d3c2,4154,4150,5153,56523523486753,4152,0x1832b6d16baa36f,0xd3b9b4ce23989f377,
4152,11022390,11079712,10309706,4178,77667859989029724,22624363389,11133003,5163,0xa83a76e819fc1f083,4155,0x56da9777f4ecb835c3c9,21074124863,4184,11526936,
11019032,39256507032721,11903680,4175,4157,28439265953,4144,46220208612416,4178,4198,0x63d1bc512ed8b129c4ef,4153,11527515,27632710519,0xaf35e93791029e2fc,
4155,4162,23522309467,56493821510024,9838642,4153,24280167197,44537463038733,4165,0x1678e81449cc2eb,5265,46116844127386,4164,4139,22743400638,
90716825618859047,4153,4165,10289903,0x5492fb8f8b997b28a55c,10330208,4178,4184,4198,25981855072,11924540,11046960,0x1a771e9afc6d450a24e804755c,18623430738,4175,
4171,4181,4169,4183] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part556 : Refutes moves 0x10004000000000000000000000 0x26ba0301884020100000000000 :=
  finish #[
43024778904521,0x47a1a7a7c10c138281de,98731546155643940,10744507,4169,4181,0x1a76a0d109cb092,5067,9459032,19371533656,10723371,4169,4181,22508516121,10269465,
36289454032319,4172,11083845,4171,4178,4198,54758604792886,44982361257206,4171,27637159055,27592774899,20135302385,39610011824609,4146,4162,
4186,24990299090,18483220856,4144,4870,9831371,81332495428871204,4180,11124797,4153,4160,11482459,56419966919540,4157,20152172832,
4160,0x19b2a7045d3e48e,41271650440540,22649962557,4175,4169,4292,36340986840097,4190,5153,44093914153109,4171,51478027023323,4162,4159,
9400798,4152,0xa3a4723dd448ac362,54943187988856,8909666,21041271658,4165,22784188464,4195,4181,8594495,11125043,4181,27592774129,51476492316979,
4170,4162,9400817,41508638671840,4181,0xcdb8fcefc9d29c42c,25151706062,40983643579738,23516005130,4195,4174,10248258,4138,13472120,27592869107,
4181,11125795,51184434873691,11059252,4130,22786204024,4162,22788543832,56508358976285,4148,95004132452778183,4171,4175,4165,4169,
56513417291007,74288582261130390,4171,0x18ea2b1731623cb,4157,5277,28416508676,53268828230527,4144,4172,11109245,9896925,9117759,10289227,4148,
0x2bb84f9c877ca0e39c7f435,46237164761967,48077146416372,4180,91659538113581712,4152,4144,41512193434373,21116088395,4174,4184,4178,4198,4183,11907155] (by decide +kernel)

private theorem part554 : Refutes moves 0x10004000000000000000000000 0x26ba0301884020000000000000 :=
  branch 1 0x10004000000000000000000000 0x26ba0301884020000000000000 44 0x26ba0b218a4022008000000804 (by decide +kernel) part555 part556

private theorem part550 : Refutes moves 0x10004000000000000000000000 0x26ba0301880020000000000000 :=
  branch 1 0x10004000000000000000000000 0x26ba0301880020000000000000 62 0x26ba0305880220004021080020 (by decide +kernel) part551 part554

private theorem part544 : Refutes moves 0x10004000000000000000000000 0x26ba0301080020000000000000 :=
  branch 1 0x10004000000000000000000000 0x26ba0301080020000000000000 71 0x26bb03110c0120046000800100 (by decide +kernel) part545 part550

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part559 : Refutes moves 0x8006000000000000000000000 0x77b291c285003c000000000000 :=
  finish #[
94447533994607672,28445930061,17735029793,4172,5176,10621517,11075644,0x18fe88548029438,4139,4150,4144,18510352538,8676704,0x19aa88023342560,4142,
0xbad9bf05e6c290493,4141,13472824,21745234984,10293325,4164,4184,23374136366,24293696382,0x1754a40e8971320,4184,4164,17770063200,0x16a8bf56d41e28d,4164,
11878898,44193773327203,4163,4184,24372433394,4138,4142,4156,4178,28417323559,8585693,23374902624,4142,11046961,53177139619260,
4168,0x1758d51aea20489,23577474400,83845568426271595,11132995,4172,4165,0x19b4675aa28b3c3,10617632,0x19bd07d45cda5bc,10617492,28414444885,21745934996,4142,11104323,
11018316,4186,4190,27600749021,0xd3b5c4a254bcdf3ba,10313818,4159,5064,51127881384913,20277207095,4168,4184,5064,58190264341564,24406316384,
11105021,9384210,11522088,11456561,4177,4172,11423943,23510365030,10248257,9900640,4184,11907144,4140,4158] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part560 : Refutes moves 0x8004000000000000000000000 0x37b22182040020000000000000 :=
  finish #[
9454554,0x8ce4f06dd4f4d955e,90614246149034549,9041242,4172,4156,9093915,4167,4179,27592761927,24387990874,56509365199431,4163,4174,4198,
27593232967,11908442,11523034,42990387958545,4179,9887820,10342469,4161,11428539,44983124599476,4179,10343388,4166,0x433cdf6b69f4d147e5bd1cd113ba175,0xd3e0fb1f8859dd55b,
4166,4702,0xcd96b71f8ee9c755b,4174,4179,39437448631542,12628163,24221049118,4160,37647520936904,10334260,4198,4702,56511797515232,10695360,
10252894,4179,4174,9916518,4180,4168,4164,27637158688,10253653,11907130,20998640303,4186,49943996248821,5258,11457674,
9470004,4187,24270197132,9932875,4172,77602970005779491,22644372346,0x5dfa848e8d6c85a22320,4163,4157,11907676,0xc139ae72d41a91500,11022924,4983,23606637323,
4166,4160,4157,10331100,4179,4163,4183,5084,37888820802710,4174,44313922548700,4148,5084,11907358,0x16baba5463505bf,
4151,54773369123615,24219874268,4168,4198,4174,4179,11081045,0x18268826f35b083,24390788448,0x8cf5a537a391c736a,4144,4139,10334807,4183,
10342483,9904203,4161,9953787,4180,4173,4177,4184] (by decide +kernel)

private theorem part558 : Refutes moves 0x8004000000000000000000000 0x37b20182040020000000000000 :=
  branch 1 0x8004000000000000000000000 0x37b20182040020000000000000 85 0x77b291c285003c000000000000 (by decide +kernel) part559 part560

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part562 : Refutes moves 0x40004000000000000000000000 0x3ed2a100600020000000000000 :=
  finish #[
17737036449,49643053016414,4177,27627610697,23505961155,11124809,4160,56592394298509,0x4dc20381cb566f4d93bf,13472313,26773131635,0x167d37a3b9b810a,4169,11907123,4167,
4140,47648489706556,13042518,12301371,4163,21746791770,4131,4167,53020662150285,46051665330732,0xcdd81cd6c2141d2f5,4163,4130,13472714,51599981807036,
9379907,11427891,4141,4133,23566738205,4160,0x5ada2446d3657c97255f,4177,4189,4676,42730120651742,4179,0x4df53b5dabc84f9082f9,19397161741,4151,
58241972605888,20309177210,4189,4192,4184,18426466889,19398264154,9868321,11124788,4174,10662673,20385862212,8745044,4189,23574725491,
23373398797,0x1754d714e16630d,8745021,4189,24369263389,11059873,4137,0x29c54e3470ae8814ba9a556,4162,4155,8745545,46670954472414,0x5acbba7627226c96942e,0xbb19b28ac2b975316,4189,
4184,11059974,4137,11907155,4140,4158,4167,27609637649,42340728181699,22484886769,24178569483,4141,13472515,22771336044,4154,
4179,9441746,4156,4144,10256959,4175,4145,87189610243359089,9867844,20352291396,4189,4192,4184,49625055466459,5466,
11076381,4172,41239725392843,4147,4187,4681,0x182ca413c29c55e,4174,81353832221180479,21986898500,4192,4184,4189,4681,21005431646,
4184,4603,46509647470985,9110073,0x9c38f8b54b897e31b,4192,4189,11124812,11907150,4158,10342471,4171,4186] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part564 : Refutes moves 0x1006000000000000000000000 0x7e9a991700a03c000000000000 :=
  finish #[
0x94a1b74fc2153b170,76706116307566960,4154,0x8e79bb37e062fd17f,58259072209973,0x19be9b97684348d,4164,0x1a7f3753747c3db,4130,4166,24320820672,4700,98045053479616898,4165,48281715762141,
58261747778231,4154,4166,4178,4189,4177,26026963617,10334377,4174,18356220893,39501017494088,21929706838,21678457617,4141,4190,
4165,4177,10584653,4704,46051682661222,0x181877d7da311b6,4184,4190,25938584421,10687453,11518040,4139,4178,20268351684,4167,
4163,4155,12697975,0x16b8824a79c13b9,4138,11518843,0x50cad55f4a257d8312f2,4150,4155,10273662,0x180eead7dbb6247,0xbab46ca30ed1d142d,4184,4178,4189,
9040739,48024135164482,4171,53295942726410,47867103613689,4177,10289641,4163,4189,17708970179,0x8f4a7c5a1461cc3db,22801712172,23531991918,4184,4178,
11907165,4140,4167,4158] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part565 : Refutes moves 0x1004000000000000000000000 0x7e9a2912008020000000000000 :=
  finish #[
0x9a82b31d4e090e37e,0x1682e988729c4f4,25821242421,46670174303102,4893,24095183718,9801809,4132,11907124,4140,4167,0x19bf045712fc17c,36034026140541,10228597,11522090,
4990,98142360126075263,4183,4144,4164,49347001873165,80784543693780021,36405536817903,4183,4155,4167,0xa095051cd799be2f2,12669992,24395834095,4139,
9495306,4190,4184,8680175,39830144090893,4190,10342471,4166,4171,4769,51169695396409,4168,11907656,24387150707,4177,
4145,24983138791,0xd3b77c599d190e49d,11124815,4160,25059795697,0x639adb2cd0626f90e423,4166,5366,72429200961642679,4156,17243259755,0x18fe0323f3bf15d,10252370,4139,
4164,56613277262223,0x19bea71df4064f6,4180,0xc7f694a723f1c74f4,11907115,4167,11764463,23239909951,4145,47870062781372,51318126510219,9855933,4145,0x18225999db4d5c0,
10252354,4164,4144,0x16883e1adaf53bc,0x1746d6cb32fd500,4145,21000205262,5084,4988,4988,54778972328901,11853905,4180,4162,11124785,
4146,10342471,4171,4186,11907678,24387150707,11087929,22802191404,0x4003a2078868e835b3c5,54792863850983,4177,11088860,9855964,4157,5164,
0xc7e4109eddaa9737b,4155,10342452,4186,11907666,0x177f071adb3b46ca68ea9db363,4173,4174,4184,4178,43384674107946,10101724,26812580299,4145,0xd3f1a51c9ad90e4f6,
21745225792,88851865044566801,4174,9134168,4175,4183,4189] (by decide +kernel)

private theorem part563 : Refutes moves 0x4000000000000000000000 0x7e920100000020000000000000 :=
  branch 2143 0x1004000000000000000000000 0x7e9a0912008020000000000000 85 0x7e9a991700a03c000000000000 (by decide +kernel) part564 part565

private theorem part561 : Refutes moves 0x4000000000000000000000 0x3e920100000020000000000000 :=
  branch 1 0x4000000000000000000000 0x3e920100000020000000000000 102 0x3ed2a100600020000000000000 (by decide +kernel) part562 part563

private theorem part557 : Refutes moves 0x4000000000000000000000 0x36920100000020000000000000 :=
  branch 1 0x4000000000000000000000 0x36920100000020000000000000 99 0x37b20182040020000000000000 (by decide +kernel) part558 part561

private theorem part543 : Refutes moves 0x4000000000000000000000 0x26920100000020000000000000 :=
  branch 1 0x4000000000000000000000 0x26920100000020000000000000 100 0x26ba0301080020000000000000 (by decide +kernel) part544 part557

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part569 : Refutes moves 0x10000804800000000000000000 0x25f3c1f03628011c2904124900 :=
  finish #[
9241848,10559626,24229823741,4168,4141,4975,37410944624063,54754276636000,9478533,4177,4153,4171,24344593656,25992999775,4151,
5061,49466171224401,8732744,4186,4193,4181,4975,35859718054101,53223523017878,81223570352223581,4163,4153,4193,11462079,5275,
52885929152883,12690287,23338558619,4169,4145,4153,18950742113,4119,4143,8733846,17887597617,4168,4978,58195305649010,4193,
4978,12264689,26811069884,24355213863,4136,0xcdb822e9978bbb0ee,4143,4163,45807853352284,26813867256,0x18f94ec7510548b,4160,8736835,4187,4193,
4978,19213816476,0xc1174eec1dc855293,4187,12210273,4132,4142,4195,0x8874da6d48535755d,41273968530382,4579,56559100011964,8736840,4186,4193,
58196215570617,94737701692658114,53224455361789,12292154,20149785340,4181,4187,51215400145885,11527034,4181,4168,4160,11395285,11527034,4168,
0x1838ec1d2855293,12210547,25009578855,4181,4168,51219577684839,4145,13099107,4125,4149,4152] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part570 : Refutes moves 0x10000800800000000000000000 0x25d34174042800142100100100 :=
  finish #[
4696,19414311387,9097309,4398,20152475862,4181,43277546004980,4160,4193,19287340285,4477,13480536,11400346,25027084318,4153,
4163,0x18f8a616f41a4f8,4149,8733272,0x19b6eec2aba6226,39677078659556,9908716,4195,4158,51256362111576,4309,4309,48069979710424,4156,4177,
4189,0x1820094ab22e28e,8737368,51407738983776,51402884380000,12689462,4171,0x8063ae70cb5c1c0d6,4158,9097315,4166,4180,4178,4186,4310,
4398,27609543728,44776133677415,4180,11137817,4171,4198,4178,22517256792,0x31b60d53b5ec3ce0d854431,4181,25997005864,40701979709878,47606873441338,47848125452657,
12689493,11137817,4156,4171,4198,13062226,4161,0x1a7d4ec36b4d500,20259558535,4178,35350251938761,19373163868,4153,23362618812,5273,
5080,11113521,4150,4163,25883132342,11473980,28412923968,4166,4178,4180,4168,12689622,47803037840153,23404926107,4168,
4178,4309,20294763655,4177,11428902,18551514254,11494555,4189,4160,13099080,4161,4149,4696,19372020893,25990656772,
20260009206,4187,4186,4178,11428824,24354878126,11055164,20259197915,4166,20295128511,20227601178,4150,23542735837,4149,4876,
0xc75508a7e0d2f1098,4189,44556210762902,0x66daf65e275c508ad49b,4178,4166,4180,4160,10629192,4146,4158,4152,4164] (by decide +kernel)

private theorem part568 : Refutes moves 0x10000800800000000000000000 0x25d34170042800142100100100 :=
  branch 1 0x10000800800000000000000000 0x25d34170042800142100100100 74 0x25f3c1f03628011c2904124900 (by decide +kernel) part569 part570

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part572 : Refutes moves 0x10000800004000000000000000 0x25d343408c2200120001880004 :=
  finish #[
26839474565,26024510514,4143,4969,25845576553,4164,12203157,4969,27644371708,11022404,9097269,4178,4170,48352809984879,53299130004338,
4171,12189889,17720636366,4150,0x18fea7ddf0ad1cd,4178,4170,0x16891fc82a99236,11924639,4145,20152185824,4149,21854679342,8732744,4193,
4181,5269,4381,58194462327138,25102622822,4164,24302875697,25940210458,5179,22645133653,4198,25099559892,13104187,4127,4488,
28448002835,4198,10297404,4175,4160,4170,4150,0x87f0d537e0f0d00e9,8541244,21626921104,9467121,12300680,9748557,4151,4171,
4143,0x50927b5244f94c1d94fd,4170,0x569c1a016a62393a77742b4e01d40a1,4152,4172,0x402b44751021ab0fb361,51217639912289,38162071380348,4180,11137817,4149,4170,0xcdb83cd4d4185548c,74467883717596209,
4171,50012706632287,9478736,17301631839,11113632,4171,0xd3b81536916a3f304,21189972040,4193,4186,4180,4187,5279,10560068,4165,
23356608990,11137774,4149,4198,19346826089,23500768395,20051911829,4149,25132618902,22760203027,4175,4150,78145954584040603,4172,4180,
11124827,4160,4181,4195] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part574 : Refutes moves 0x10000800000020000000000000 0x25d341c0946401100000804042 :=
  finish #[
28441608780,53160096289842,4150,51423068124200,4180,52948847596991,4309,12255906,8991881,10203200,12673210,4134,36204354466496,4151,4159,
4150,44588073829335,41180712702833,4165,12272885,11465576,25157710108,4165,4168,4150,21772669093,0xc0983cec66a2f02a4,4183,51596727038832,4150,
4684,44212469899451,4160,11530724,9097270,4168,4178,4170,4166,10306813,58189228647147,12301352,24380817465,4168,13043135,
54707753816421,4152,11469962,4143,0xcdf00f058682f73dd,37681754883026,4152,87127573573723296,11837835,11530312,4143,4150,4198,25027482556,56542878397791,
4142,27634684345,4869,0x16af379a6bbb361,4153,4163,4143,46104009880424,0x169acfd0d90a3bc,8736849,4186,23547171003,8737525,25881965707,8737158,
4193,4163,4169,8737650,21023768790,4172,4152,8737927,8737365,9467227,13460352,11837654,8626266,4163,4159,
10265326,23297803006,11027803,0x16be9f57c05518b,4186,4180,11472998,4136,11124808,4153,4160,4181,39344008709179,23356621977,11891454,
4163,4198,4588,36319611507364,4180,4166,22783808353,11055318,9908278,36325335364658,0x1a7683482a9c362,4160,4310,43109896876246,4166,
4186,25218891990,21769876631,10297390,11403478,47833481319460,11124790,0x2bc13510a815050e916f31d,4166,10326118,4177,4180,4187,4170,4195] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part575 : Refutes moves 0x10000800000000000000000000 0x25d34140846020100000000000 :=
  finish #[
8733437,24201409696,4165,4485,9023877,4164,12690304,11465576,8732710,4193,4150,27573625508,4976,11137904,4171,
4150,0x18343a511a9f3ce,44583055913435,8732721,8733045,21584037216,17484144853,11022421,4177,44587392332260,4150,9097262,4180,4178,4698,
25034995035,20027523968,11427886,5070,11428721,12259523,10268740,4183,4163,47800026276447,43402449954045,23339827979,4163,4142,4177,
39677127922461,46669352268452,25990980656,22786601244,9056310,4168,4164,4160,44590493323549,9467026,10629700,4152,4150,17190498670,39260591563931,
11124790,4181,90533727445987514,21189972644,9097307,4172,53074187035300,12653220,46102399779791,9097262,9875532,0x1690b6545a23433,11428323,11085043,22006834023,
10297416,10346550,20260008020,4187,4198,4186,4178,11907171] (by decide +kernel)

private theorem part573 : Refutes moves 0x10000800000000000000000000 0x25d34140846000100000000000 :=
  branch 1 0x10000800000000000000000000 0x25d34140846000100000000000 53 0x25d341c0946401100000804042 (by decide +kernel) part574 part575

private theorem part571 : Refutes moves 0x10000800000000000000000000 0x25d34140842000100000000000 :=
  branch 1 0x10000800000000000000000000 0x25d34140842000100000000000 62 0x25d343408c2200120001880004 (by decide +kernel) part572 part573

private theorem part567 : Refutes moves 0x10000800000000000000000000 0x25d34140042000100000000000 :=
  branch 1 0x10000800000000000000000000 0x25d34140042000100000000000 71 0x25d34170042800142100100100 (by decide +kernel) part568 part571

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part578 : Refutes moves 0x2002800000000000000000000 0x35ded307204405500000000000 :=
  finish #[
4488,10318500,4172,0x63aa8da7c749118b5354,4198,11043388,11908149,8663716,9850950,9105476,0x46a0ed4da1b20c41f319,79378048171225278,18700447779,4691,0x8d4814b4c340b50be,
0x4d18b51dab454da23227,4152,0x408145684a6d689d2368,4150,52967745630803,9908996,11907174,11014197,4189,4175,4333,58233845285566,4156,28448465133,10683645,
4159,18650116147,24387641949,4175,4172,4195,4167] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part580 : Refutes moves 0x2000800400000000000000000 0x35d66301200e00180180040020 :=
  finish #[
4231,9490806,4171,0xcdb3650423a95a0a5,54960661558313,4162,5469,35985083740916,20965040184,4160,4170,20820992140,12636937,4147,10682968,
0x1a7cba4ebb3c4f7,4136,4172,0x60319f8ec88ceba8355d,23474464191,4157,4149,9130292,4174,4184,0xad86a14fcd94db49c,10629282,11473080,11113221,4150,
4157,4136,4749,58249339859591,4136,52967718466719,4174,75873511109837978,4873,10203525,4162,4147,0x19bcd74820b33cc,4178,25217618487,
4144,4152,4180,9122879,9123071,4377,37866616644384,4170,4157,4171,0x177cba4da0af2a4,0x40009c5f26ed3e472377,21769171737,77202128441484351,4135,
4178,11907174,4158,4149,13890212,18072147086,23432036587,4175,10339278,5079,24345690677,4175,4145,4172,4180,
47610814846094,24421929239,0x2b603620a506749409de354,4187,11907151,4149,0xa7a042e94e535b29f,11051801,4184,88352221182669783,5084,9491407,49947218339164,24387600976,4157,
4187,9130050,4184,4180,46016375788893,4852,0xa739af1c93b2e0176,4159,4161,11473669,4890,11899467,4187,4147,5084,
11051780,4170,4149,4184,11907464,10236214,0xba3768b805a9dc3dc,4187,4170,11124820,4160,4174,4195,4167] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part581 : Refutes moves 0x2000800000000000000000000 0x35d66101600400100000000000 :=
  finish #[
4887,4686,23472067332,9106008,4172,4184,4170,4859,52970196288251,5258,49607124087948,4139,4144,44623161386327,48352064217946,
4152,4157,4172,25132987165,18652193540,8893186,0x8683a83654e1de49f,4177,4195,75698044147713372,48349649134648,4161,4173,4189,4180,
10174851,22793310884,4152,37888834859976,4174,4592,0x81083ea04e916f35a,21048975664,4172,4180,11907171,4158,4167,9851278,43147419857754,
22659588701,4175,4187,4293,24203064078,4180,0xa2334b0242229955c,11907556,4149,0x1a7a1a6389ca30b,11907568,4158,10707744,20295561696,4158,
10736312,4160,4183,4195,5084,10347462,0x24ddada6d6ac77a04a91359,4156,4142,51353625510778,21638075356,42683463209446,4164,4198,48124825662290,
4195,9105472,4180,4184,10342482,4171] (by decide +kernel)

private theorem part579 : Refutes moves 0x2000800000000000000000000 0x35d66101200400100000000000 :=
  branch 1 0x2000800000000000000000000 0x35d66101200400100000000000 70 0x35d66301200e00180180040020 (by decide +kernel) part580 part581

private theorem part577 : Refutes moves 0x2000800000000000000000000 0x35d64101200400100000000000 :=
  branch 1 0x2000800000000000000000000 0x35d64101200400100000000000 85 0x35ded307204405500000000000 (by decide +kernel) part578 part579

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part584 : Refutes moves 0x8002800000000000000000000 0x379ed350891005500000000000 :=
  finish #[
5258,49671426909630,0xd3d834101a5af248a,4161,86695106475017269,24330096833,11898948,4147,4169,11768482,11900059,4165,11768704,0xc7ea7cd7576c0a31e,4165,
9826578,4162,11907130,4158,51527924454364,23618233397,9121823,54736843391221,11908132,23465537598,21771875292,4147,11916150,48196573344732,11477054,
4153,35391440811360,18978943229,58263173063221,4170,4150,0xd3f5d0bfddd41a48b,9121845,4198,25100195072,53224636363552,9900114,4168,4164,4184] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part586 : Refutes moves 0x8000808000000000000000000 0x379ee590181008101010100000 :=
  finish #[
4382,54952479805990,49599298855308,4157,10629185,97922702562903190,4133,0x251e04cdb44704cb91cb560,0x34f8b900a446ec4e5c1618c,10268958,0x176302d11ae008c,0x181688d702ff432,4166,4190,4382,
0x182c88d7035908a,11432332,4166,11878494,4169,4151,4174,0xc1f37658d11af03da,11899776,12260696,24371950527,11899839,0xa836b336d702ff432,4150,11427903,
4157,10248280,11907129,4149,4167,49948316783662,11101056,4168,21769937671,4386,11101043,4161,0x59f4155e535e05a395bf,4198,11423816,
4169,12313948,80382536358655423,9483327,10629181,23396560958,20376273398,4189,4184,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part587 : Refutes moves 0x8000800000000000000000000 0x379e6118081000100000000000 :=
  finish #[
9454224,47921769353413,4164,5270,0xc1a5ff054e316348a,4162,10699709,44880936128709,4165,0xcd7834d4050b45185,94240213792166178,10645583,4162,4180,4198,
58257835078116,4890,47955191149016,0x511c1e13ab7dd8bbb0ef,4144,10268710,4153,47837599282316,12689996,4160,4882,98179161929646668,4157,4177,4149,
49945648533888,9949686,4189,9867829,25217249858,4157,97716401841980349,9105501,4190,4180,4184,4646,9367908,20948234288,4961,
25111012503,4144,0x16bae9911d3f500,4128,22583648844,0x80582672cb9299361,4170,4177,4157,26729624140,91311338338980914,4170,4674,0xae08169f5d8b5b0b8,0x1762d6e0d53f0b8,
4128,4164,11137495,11907206,49953148338748,9904202,4189,4177,4157,4149,13496898,19228930356,4164,10155164,10744988,
4174,11477786,95191768394355775,4148,4164,4177,38268377056511,4309,18649404068,4164,4168,0x85469c2ccbe97e2fd,4177,4189,10342484,
4161] (by decide +kernel)

private theorem part585 : Refutes moves 0x8000800000000000000000000 0x379e6110081000100000000000 :=
  branch 1 0x8000800000000000000000000 0x379e6110081000100000000000 75 0x379ee590181008101010100000 (by decide +kernel) part586 part587

private theorem part583 : Refutes moves 0x8000800000000000000000000 0x379e4110081000100000000000 :=
  branch 1 0x8000800000000000000000000 0x379e4110081000100000000000 85 0x379ed350891005500000000000 (by decide +kernel) part584 part585

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part588 : Refutes moves 0x800000000000000000000 0x3f924100000000100000000000 :=
  finish #[
94549812399682705,18474370014,11100766,11124806,4153,97758189671932672,0x9a47471ca3f2ea3c3,11522926,4156,4172,42405282169813,51652319110299,4153,10629171,22485771118,
53058645779302,4167,98983042334966940,4153,24296027291,49518450569887,37031428289080,0x9a08f53713fb5d354,4165,10629180,4158,0x1834ed1df29c3d1,10342471,4186,4181,
51646658097527,51186038788471,4138,4966,56476450268606,8954810,44266593940731,4148,4133,43384727253946,11063361,4187,4974,5084,10326812,
4157,11124827,4167,4181,0x539c0b5faa70ee9cd49b,4165,4175,4190,51254757831835,24387195570,4172,0x31f23aaf56b6d74b88572ac,4187,4975,98565763041305358,
0x901760b4cbd29c081,4153,4174,53227018351389,4190,49947485262331,4161,46664530371140,42941313819896,56578915947660,9953337,4177,8745471,4187,4606,
48212326470811,43110679814941,46664393806496,4166,10339292,8745041,4186,9916510,4168,4172,4181,8777816] (by decide +kernel)

private theorem part582 : Refutes moves 0x800000000000000000000 0x37924100000000100000000000 :=
  branch 1 0x800000000000000000000 0x37924100000000100000000000 99 0x379e4110081000100000000000 (by decide +kernel) part583 part588

private theorem part576 : Refutes moves 0x800000000000000000000 0x35924100000000100000000000 :=
  branch 1 0x800000000000000000000 0x35924100000000100000000000 97 0x35d64101200400100000000000 (by decide +kernel) part577 part582

private theorem part566 : Refutes moves 0 0x24924100000000000000000000 :=
  branch 2334 0x800000000000000000000 0x25924100000000100000000000 100 0x25d34140042000100000000000 (by decide +kernel) part567 part576

private theorem part542 : Refutes moves 0 0x24920100000000000000000000 :=
  branch 1 0 0x24920100000000000000000000 86 0x26920100000020000000000000 (by decide +kernel) part543 part566

private theorem part514 : Refutes moves 0 0x24820100000000000000000000 :=
  branch 1 0 0x24820100000000000000000000 92 0x2c820100800000000000000000 (by decide +kernel) part515 part542

private theorem part468 : Refutes moves 0 0x24800100000000000000000000 :=
  branch 1 0 0x24800100000000000000000000 89 0x24800100004000000000000000 (by decide +kernel) part469 part514

private theorem part396 : Refutes moves 0 0x24800000000000000000000000 :=
  branch 1 0 0x24800000000000000000000000 80 0x24800000000000000800000000 (by decide +kernel) part397 part468

private theorem part292 : Refutes moves 0 0x4800000000000000000000000 :=
  branch 1 0 0x4800000000000000000000000 101 0x44800000000000000000000000 (by decide +kernel) part293 part396

private theorem part116 : Refutes moves 0 0x4000000000000000000000000 :=
  branch 1 0 0x4000000000000000000000000 95 0x14000100000000000000000000 (by decide +kernel) part117 part292

private theorem part0 : Refutes moves 0 0 :=
  branch 1 0 0 98 0x20020000000000000000000000 (by decide +kernel) part1 part116

private theorem noGood : ¬ Good 206 15 := by
  rintro ⟨c,hp,ha⟩
  exact part0 c hp ha (by simp [Red]) (blue_zero c)

end Case206
private theorem no206 : ¬ Good 206 15 := Case206.noGood

/-- Table 6 of Ahmed, Kullmann and Snevily. With odd length the last
avoiding palindrome has 199 positions, and with even length it has 204. -/
theorem palindromic_3_15 (n : Nat) :
    Good n 15 ↔ (n % 2 = 0 ∧ n ≤ 204) ∨ (n % 2 = 1 ∧ n ≤ 199) := by
  constructor
  · intro h
    by_cases even : n % 2 = 0
    · left
      refine ⟨even, ?_⟩
      by_contra! large
      exact no206 (restrictGood 206 ((n-206)/2) (by omega) h)
    · right
      refine ⟨by omega, ?_⟩
      by_contra! large
      exact no201 (restrictGood 201 ((n-201)/2) (by omega) h)
  · rintro (⟨even, small⟩ | ⟨odd, small⟩)
    · exact restrictGood n ((204-n)/2) (by omega) yes204
    · exact restrictGood n ((199-n)/2) (by omega) yes199

private lemma mono_of_noGood {n : Nat} (h : ¬ Good n 15) (c : Nat → Bool) (hp : Pal n c) :
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 14)*d < n ∧
      ∀ t ≤ (if b then 2 else 14), c (a+t*d) = b := by
  classical
  by_contra bad
  apply h
  refine ⟨c, hp, ?_⟩
  intro b a d hd he
  by_contra! absent
  apply bad
  cases b
  · refine ⟨true, a, d, hd, he, ?_⟩
    intro t ht
    exact Bool.ne_false_iff.mp (absent t (by change t < 3; change t ≤ 2 at ht; omega))
  · refine ⟨false, a, d, hd, he, ?_⟩
    intro t ht
    exact Bool.eq_false_iff.mpr (absent t (by change t < 15; change t ≤ 14 at ht; omega))

end PalindromicThreeFifteen

theorem OMA.solution : OMA.R_Green14_W_3_15_R2.H1 := by
  intro n hn c hp
  apply PalindromicThreeFifteen.mono_of_noGood _ c hp
  intro h
  have := (PalindromicThreeFifteen.palindromic_3_15 n).mp h
  rcases hn with rfl | rfl <;> omega
