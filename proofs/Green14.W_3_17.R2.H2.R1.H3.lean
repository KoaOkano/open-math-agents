import OMAReductions.R_Green14_W_3_17_R2_H2_R1

/-! Case 3 of the length-280 upper bound for the palindromic (3,17)
problem, Table 6 of Ahmed, Kullmann and Snevily (arXiv:1102.5433).
The proof checks a finite branching certificate for the specified
colors near the axis of reflection. Lean formalization by @KoaOkano. -/
namespace PalindromicSeventeenEvenThird
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
    let m := remaining (longMask n k (stream%4096)) b
    let p := m.log2
    if m = 2^p then redSteps U f (stream/4096) (r ||| 2^p) (addedBlue n U.unary r b p)
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
      obtain ⟨i,hi,ri⟩ := hit_remaining hb (long_hit hk hkn hp ha (stream%4096))
      rw [eq, Nat.testBit_two_pow, decide_eq_true_eq] at hi
      have rp := hi.symm ▸ ri
      exact ih _ _ _ (insertRed hr rp) (added_sound U hp ha hr hb rp) pass
    · contradiction

private inductive RedTree where
  | endAt (digits clash : Nat)
  | branch (digits p : Nat) (l r : RedTree)

private def redCheck {n k} (U : Rules n k) : RedTree → Nat → Nat → Bool
  | .endAt w clash, r, b =>
    match redSteps U (w.log2/12) w r b with
    | none => false
    | some (rr,bb) =>
      if clash=0 then rr &&& bb != 0 else remaining (longMask n k (clash-1)) bb == 0
  | .branch w p l t, r, b =>
    match redSteps U (w.log2/12) w r b with
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
    cases e : redSteps U (w.log2/12) w r b with
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
    cases e : redSteps U (w.log2/12) w r b with
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
  let tag := word%8192
  if tag<256 then
    match stack with
    | b::r::xs => .branch (word/8192) tag r b :: xs
    | _ => []
  else .endAt (word/8192) (tag-256) :: stack

private def readTree (words : Array Nat) :=
  (words.foldl readNode []).headD (.endAt 1 0)

private def reaches {n k} (U : Rules n k) (w r b rr bb p br : Nat) :=
  match redSteps U (w.log2/12) w r b with
  | none => false
  | some (x,y) => x==rr && y==bb && addedBlue n U.unary x y p==br

private theorem join {n k} (U : Rules n k) (hk : 0<k) (hkn : k≤n) {r b}
    (w rr bb p br : Nat) (pass : reaches U w r b rr bb p br=true)
    (l : Refutes U (rr ||| 2^p) br) (t : Refutes U rr (bb ||| 2^p)) : Refutes U r b := by
  intro c hp ha hr hb
  cases e : redSteps U (w.log2/12) w r b with
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

-- Each path entry has a one-bit marker and an twelve-bit progression
-- index. A zero marker introduces a split, a color clash or a blocked
-- progression. The reconstructed tree is checked by redCheck.
private def pathBits : Nat → Nat → Nat × Nat
  | 0, bits => (1,bits)
  | fuel+1, bits =>
    if bits.testBit 0 then
      let (path,rest) := pathBits fuel (bits >>> 13)
      ((path <<< 12) ||| ((bits >>> 1)%4096),rest)
    else (1,bits >>> 1)

private def treeBits : Nat → Nat → List RedTree → List RedTree
  | 0, _, stack => stack
  | count+1, bits, stack =>
    let (path,body) := pathBits 256 bits
    if body.testBit 0 then
      let long := body.testBit 1
      let clash := if long then 1+((body >>> 2)%4096) else 0
      treeBits count (body >>> (if long then 14 else 2)) (.endAt path clash :: stack)
    else
      match stack with
      | right::left::tail =>
        treeBits count (body >>> 9) (.branch path ((body >>> 1)%256) left right :: tail)
      | _ => []

private def packedTree (count bits : Nat) :=
  (treeBits count bits []).headD (.endAt 1 0)

namespace Case280
private def hints : Array (List Nat) := #[
[25760],
[],
[],
[25203],
[],
[],
[24646],
[],
[],
[24089],
[],
[],
[23532],
[],
[],
[22975],
[],
[],
[22418],
[],
[],
[21861],
[],
[],
[21304],
[],
[],
[20747],
[],
[],
[20190],
[],
[],
[19633],
[],
[],
[19076],
[],
[],
[18519],
[],
[],
[17962],
[],
[],
[17405],
[],
[],
[16848],
[],
[],
[16291],
[],
[],
[15734],
[],
[],
[15177],
[],
[],
[14620],
[],
[],
[14063],
[],
[],
[13506],
[],
[],
[12949],
[],
[],
[12392],
[],
[],
[11835],
[],
[],
[11278],
[],
[],
[10721],
[],
[],
[10164],
[],
[],
[9607],
[],
[],
[9050],
[],
[],
[8493,25760],
[25203],
[24646],
[7936,24089],
[23532],
[22975],
[7379,22418],
[21861],
[21304],
[6822,20747],
[20190],
[19633],
[6265,19076],
[18519],
[17962],
[5708,17405],
[16848],
[16291],
[5151,15734],
[15177],
[14620],
[4594,14063],
[13506],
[12949],
[4037,12392],
[11835],
[11278],
[3480,10721],
[10164],
[9607],
[2923,9050],
[8493],
[7936],
[2366,7379],
[6822],
[6265],
[1809,5708],
[5151],
[4594],
[1252,4037],
[3480],
[2923],
[695,2366],
[1809],
[1252],
[138,695],
[138]]

private def values : Array Nat := #[
0x200000000000000000000000,0,0,0x400000000000000000000000,0,0,0x800000000000000000000000,0,0,0x1000000000000000000000000,0,0,0x2000000000000000000000000,0,0,0x4000000000000000000000000,0,0,0x8000000000000000000000000,0,0,0x10000000000000000000000000,0,0,0x20000000000000000000000000,0,0,0x40000000000000000000000000,0,0,0x80000000000000000000000000,0,0,0x100000000000000000000000000,0,0,0x200000000000000000000000000,0,0,0x400000000000000000000000000,0,0,0x800000000000000000000000000,0,0,0x1000000000000000000000000000,0,0,0x2000000000000000000000000000,0,0,0x4000000000000000000000000000,0,0,0x8000000000000000000000000000,0,0,0x10000000000000000000000000000,0,0,0x20000000000000000000000000000,0,0,0x40000000000000000000000000000,0,0,0x80000000000000000000000000000,0,0,0x100000000000000000000000000000,0,0,0x200000000000000000000000000000,0,0,0x400000000000000000000000000000,0,0,0x800000000000000000000000000000,0,0,0x1000000000000000000000000000000,0,0,0x2000000000000000000000000000000,0,0,0x4000000000000000000000000000000,0,0,0x8000000000000000000000000000000,0,0,0x10000000000000000000000000000001,8,64,0x20000000000000000000000000000200,4096,32768,0x40000000000000000000000000040000,2097152,16777216,0x80000000000000000000000008000000,1073741824,8589934592,0x100000000000000000000001000000000,549755813888,4398046511104,0x200000000000000000000200000000000,281474976710656,0x8000000000000,0x400000000000000000040000000000000,0x200000000000000,0x1000000000000000,0x800000000000000008000000000000000,0x40000000000000000,0x200000000000000000,0x1000000000000001000000000000000000,0x8000000000000000000,0x40000000000000000000,0x2000000000000200000000000000000000,0x1000000000000000000000,0x8000000000000000000000,0x4000000000040000000000000000000000,0x200000000000000000000000,0x1000000000000000000000000,0x8000000008000000000000000000000000,0x40000000000000000000000000,0x200000000000000000000000000,0x10000001000000000000000000000000000,0x8000000000000000000000000000,0x40000000000000000000000000000,0x20000200000000000000000000000000000,0x1000000000000000000000000000000,0x8000000000000000000000000000000,0x40040000000000000000000000000000000,0x200000000000000000000000000000000,0x1000000000000000000000000000000000,0x88000000000000000000000000000000000,0x40000000000000000000000000000000000]

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def moves : Rules 280 17 :=
  cachedRules 280 17 (by decide) hints values (by decide +kernel)

private theorem finish {r b : Nat} (words : Array Nat)
    (h : redCheck moves (readTree words) r b = true) : Refutes moves r b :=
  checked moves (by decide) (by decide) _ h

private theorem branch {r b} (w rr bb p br : Nat) (pass : reaches moves w r b rr bb p br=true)
    (l : Refutes moves (rr ||| 2^p) br) (t : Refutes moves rr (bb ||| 2^p)) : Refutes moves r b :=
  join moves (by decide) (by decide) _ _ _ _ _ pass l t

private abbrev Excludes := Refutes moves

private theorem splitAt {r b rr br : Nat} (w p bb : Nat)
    (right : Excludes rr (bb ||| 2^p)) (left : Excludes (rr ||| 2^p) br)
    (pass : reaches moves w r b rr bb p br=true) : Excludes r b :=
  join moves (by decide) (by decide) _ _ _ _ _ pass left right

private theorem finishCode {r b : Nat} (count bits : Nat)
    (h : redCheck moves (packedTree count bits) r b = true) : Refutes moves r b :=
  checked moves (by decide) (by decide) _ h

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part3 : Excludes 0x40000811000000000000000000000000000 0x9c66c18e312004848890322200000000000 :=
  finishCode 137 0x3c90a400fe338b83906257c15435ec4f7078a7de245901e68159cd6b4b399c0f193bf2ccdab6617727b9ace66af789ee173079c183d5920e94107883cd3ef188dd866164501076825473cd6107998341e741ed1cf0620546d72795abec3b38b98341e6e6b8c1a9e525ea504d19aaec3b306971e079a82e27b83cdd8490f841da808255514171fbded2a4527b82b66969775696ea1f8d21371caff2339add436b078dc6aff46eac2683da924dc6b62f8e439965829a8545e7ef390a915a4334e42be4f76afd187721ac25a5ab2d9437187611bd9ce27358d8563d57b4a05506aaa3905c79a42f516b093dd43ea47605c7db27b85cc2ff1cbd6a6e2288d45967a4d13f5a02d6c5017c522cd5527ba7d6517b4b53bf2c25ecea456b0b14e412a915405f162325049eeb53920e9415b0f462aca0b59e976e0f71b8dac27a1b467b3ac45ed2c55371c359523ad0aa2884ed661d883106ae434f564f13447aa4d19cd712f502a0b7399ac9659e9bb416a822bee6a2a82c9a27db6a2c19f2e3b93d4632055aaa6bd6b174511d8399ac883b8b8e9412e3cf695939345893171dac317456628152e8c92b246cd4703ea055986b031334d548aa09399bda4e4283b9cd6b33268ac1e4fbac9daaeb490dfad0b613ddfc6b16447ccc5f4a0b4b56969e3da67359aac75ed576189fbe2f4bda4b1ad61524caff9abea497b3b4b5696e427ce524bd9c7aaa09410fab3d9d8867d5983af67465ad8b23587c208d5b495a8268c3a87daaaf6b93ef3da543e1c37b5ce4f6b0ad3dc9f2c4586248d7b5bda5a9ad557b4ca31 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part5 : Excludes 0x40200810000000000000000000000000000 0x9fc75383216894844810200000000000000 :=
  finishCode 125 0x1fc792006e1a06712431198bd0c48e9eb66adad3d01ec01afda772925a772cc417b2e0981835ec6b150523cb3d400a0c4f45509a2f69986a18f48eb0ee30f30d5ed2b5383fa07dab70f5503e93f4609a32d4cdc67c5522cc3b61ac6e32688f551f32475ac761a43356c7aa91d43101f2cd548f3da5ed3248ce3b060b1eacd4540fa504e0407cb4f49fc275732a90dd840fd07b48ea5054483dcb4f268a00662ab30f62e8b81cbd81b02b5ab6831613d0737b4b56dcba7ad96723d5699d1835a7938c7aa81f9a56ec248c438dc707f400b9ace5ed451d797fd23a941661405d1256c63976057c1bd886b4b05d870d6470ebe49fb16d66a1a57b4ae0d3da0e6d45615d073518c81f268b55d8c57101e8d1812eb4b1d795ee7a9c1cc9a2b4b7b8ca090d8b56d696b4f520b84a0b1891d418c4d105faf0d619ed2d4561ac1eda8b3189624fe1cf82fd03e93f817ed5b91ba4b759e8f55a567c318962e0bc207ded341ed87a91905586ce48cbda661d938d01e93f9ed2c3d6b0c91961ebda64c1ac44107e94190023d589c6d5f4a0ad05e989c64cb96a65e9617cc5f417a42d282e43c8861e0a217767b49bece2eba35880f9462a095a39cbd463282568e5dd7b4a0064fcc60ded2a09604a9167b4b0ed27e71702cca31504ad1ce5e7337b4a0fe518a91c36ab824fd493460d68ec5760486d5ed2831407cb05 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part7 : Excludes 0x40000810020000000000000000000000000 0xbc66e187316044840813200440801000000 :=
  finishCode 85 0x851fc8019c7c0c4a73392565c139083cce673b08c2c80a98e667e5389a0954430683cd02ae5d9ab6a479a4307b85be0f3079cb6358a420891d4a0aa0ea260d6163148741ed846d3b5a3a0c584734ed68e801838cd3b7338b7e0f71fee724c81f732c1ecf831094407c5db41da465876c53711a7b0b7c152c5541db4f67b4b48662bb54c9ee93f9ac25db7b4af08c20ed68f355504ab399ed28e716fae893f9aaa80b521b0f66aab30f698fca5c141da87627bb57d7c781546309eeea30f6412b58d4162df390cc0d83fa07cdc6d2f9462d63601ac16fa0067b4a8bd46a83b397b904df70f5544272f968ef778bba815399bda507693f1eacb537b4a05544661746b120399b4ae41ab06528271349fa487fb903e941495cb5341aa40a820ed27e6a1902aa1f6a3a374fe26a1902a6bd3f8c2df37d93dd06b20ecdf6f6f961f07f4a093dd03e93f831404189cbe48cc1ed62a4f74a0abee7b4a0bcb8320545be72f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part9 : Excludes 0x40000810000008000000000000000000000 0xbc7e41c32b2045840814280401300004080 :=
  finishCode 111 0x761ac792146e1a05c198312a78b62e861738104a6db397abfe60cbd9d8beb239aaee4146e9c2649f83ce3979f9504aa22c07178e6680b9ac20f341aa09627ba8841e60f3927eb62487e5a0f682547ca4757830bc7e5311a094e432ce4dc692b079c4f73719b6d04acc388f6209545f2504c169f940583cd6731f6da7a8f94959cce07997041e724fd645b1247b11f291d5d1a7b0f6cbfe72f595cf5157f83cd89b2c8da7a7218dc60f3495bd872f81e6823dae62da3767b5abfda92c1d69ec8f966148491c448ea3e54435e9c5e405ad0d076831904b07b390c08d49f93dd88363c92b1ea9c5e49f93b574389c82f27b9cbc17b460cd8e4f78c1c8f9418a4fd7c6e16c27ba1892b841c7a921b8d5ff203ded6a0947cb16e59cc5b5465b16d4428f99a8e9f960e9f5520f1f556c4a0c83f47ca7ce50da4fdabf20fd21692b792145b13c5e0c2e7d191cea09079a09507693f8d3280b37da39d6724f78b6a83b311a0541e68158d8f239c16aa0941da0561427b932e02aa925c7b370aa2884f738bc83f35e9ccd63a93f850d7b302d84a6bda14680b1b41ecf5ad5b504b4ec1e6625079d07b8e5e93f481ec49fcaf3079b58ce4293f9ac6b3598920f3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part12 : Excludes 0x40000810800400000000000000000000000 0xbeef53a73f288ca52a50274848030210008 :=
  finishCode 15 0x3c9003d8b39901662f30b83cd8830bbda6317b57e47384d501647146ec1e527e823da66a2b4ed27e80b46ecf673689b8cfe2b39521aa88213dcbd334ed6a706da0e6e496b0ca49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part14 : Excludes 0x40000c10000400000000000000000000000 0xbc7f7383eb688c878e1822c808018200008 :=
  finishCode 9 0x1b8851a005fc0f37b4988cc5ef628be599b02d69ec57079b03c9ef182d03f13dd27eb4f870e3af (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part16 : Excludes 0x40000810000400400000000000000000000 0xbc6ee587eb209e8d0e10234a2801ca00018 :=
  finishCode 17 0x214800e5f03ccbfe6175118c7117c4b038693f9cbf183368bdad03ed57927f183927e9193fdbdae69ea4fded73555673355d062d555d0367246436e733363c4ed (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part18 : Excludes 0x40000810004400000000000000000000000 0x9c6e4583af38cdc70a106a4889030208888 :=
  finishCode 69 0x490b85d11f2c6388f606fcfc59ccd613e083c584ea2f84103f3d9cd6ab3916fa8d6381aaf0e849a2d5f60cbd9d8bed5f9646b3946eb4f641fbdbc56a86280e418e5e5ff617b17c8f71cbcbfeb239abf0a388d5f919e5ff079ace4bff03cdece6df8132c6288ba1f8961c8527e5ffa0de80b15ac1c6405b57c36e49755011f185da7a1b341fcf675a89b8da8ab3957ba5893f7b3cd5f60ba0fd82f4208620c51bb3dad6725db291edf0645a7a8dd7b5b53e60cac8cd7b34f4c165db6afc190035158bf03cc8cf277dcd7166cfd6b39405a58de3a8ba420f20b7cc2f1cbd6731b8d82f2884e5ec6232e62fb58507e717869307f390c617825e6bd4f183c49ef122e91838d7ab5149f83cded272169ec0f338ba0c6591a88630ef69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part19 : Excludes 0x40000810000400000000000000000000000 0x9c6e4583ab608cc50a10224808010200008 :=
  finishCode 97 0x59140851256941791706820c317ac8e69e83c53ef2c8ded2b358312c07893de732b90d62f3da55e73da60e72cd5662f69839c0bf6b0a03dec831a8b2c4562eb53607b0fd07ef69875ef517b4c4ed2e12480123ad02d1e2569b6c17e623317bd906202e39983c58af05d584a2df305c822e862399e51ab08d67ab537b5cd3b5a3aa07c3585a8b02fd87af6b817ed3d268a3749a3318f6789a2e6505fb926851b8680db72cc4c4662f7b1a9339ac56a5c124b8b7c1e2b3b9ec2497839bd89e39c8272151083c5a08c1c02b0dfbd8497a8dd371b4f6584af8aa24fe8c1b90d64e1b30df92f66abb9ad07f0dd5c86b276abc190a400d03d862f2ffcb0952483cc9a31f446c6b5346e9b8dec2ffc83f69ec7eb721b88822e87fb0e1d0736afad4dec7357d816d6146ecf67371a90ded302fdaae93f49fc1b369ebd862f96125ff0df9cbd542dad07536dabce0e65ff0df98be36d9b8f23705c18bd64f355c17e90b5a8c83159882fd2443106290b1d7cd5f46e9b8d8be5ff59ecf6b839b4f669ec90b41f82fe69eb57d07e62f (by decide +kernel)

private theorem part17 : Excludes 0x40000810000400000000000000000000000 0x9c6e4583ab208cc50a10224808010200008 :=
  splitAt 1 98 0x9c6e4583ab208cc50a10224808010200008 part19 part18 (by decide +kernel)

private theorem part15 : Excludes 0x40000810000400000000000000000000000 0x9c6e4583ab208c850a10224808010200008 :=
  splitAt 1 82 0x9c6e4583ab208c850a10224808010200008 part17 part16 (by decide +kernel)

private theorem part13 : Excludes 0x40000810000400000000000000000000000 0x9c6e4183ab208c850a10224808010200008 :=
  splitAt 1 118 0x9c6e4183ab208c850a10224808010200008 part15 part14 (by decide +kernel)

private theorem part11 : Excludes 0x40000810000400000000000000000000000 0x9c6e41832b208c850a10224808010200008 :=
  splitAt 1 107 0x9c6e41832b208c850a10224808010200008 part13 part12 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part21 : Excludes 0x60000810000000100000000000000000000 0x9f7f73cba3340ec68810201028002cc0001 :=
  finishCode 33 0x3d8ce0b7c1e2dc2a0617312cc23518abce83cca476adbda4d7ea0b371a506e31eacc3d7b0c7b535fbda5aaace1b8be310dc1afe505988cc4a922188217fd1bb1b8c30f06d35fa82d1bb1b8dab71b8e0e702ed1ba6e36adca1f371a91cc4b1afe312985cdc35ecd67836a82d2166e3660d81ea8f4e46e9af4f6ac0ba0e6af3695c93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part23 : Excludes 0x40000814000000100000000000000000000 0xbc7771eba33c0cce0a112ad028002680001 :=
  finishCode 37 0xcc3d8ba1c86397acae523a824e2e0f3681244116c2e0b3b3dbd43ef696ad9b8d2167a218aff9ab63636a69b8c2ee5ff591547b4c7b30528f6ded7310ded7357e0e66db9ed67c16ad9b8c6c73dadea207f69ca374dc66db57fcd5b371b10e05da374dc6922d85ff923a821f060b59fad6af0f6da72d4962dd0734312c67071e0f39aae5ff0dfa47635eb57e0d1c8dd62ba87c9a2d57 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part24 : Excludes 0x40000810000000100000000000000000000 0xbc66718723340c860810201028002480001 :=
  finishCode 149 0x1d8711985914441ac83b4620c412b50d0358741a80bf8c4a3d5621b16dec5d18c5b017e82f9ece83169db5556633d9cc4a6cd9ac6f69079b0d564eb4769cc62569582fdaaad53986ad2b05fb996838a0c5a426a135eb0ac17e8e798b6d5f598b0ada571af47aa0f3801a0079bdae35bacc548aa097b5c6b723e9b6c387358566262f8f8272f05282bd8563d57f19c6317c5d154059a91e35ebd8f6b8b82c5746ecf6b473a3767b5a39c1e66173179ade5a998be0f65c17b7a0bc91b0e1cb828e7079985cc5e7f191bad6183da39dac830d0417bdae5a1b555ed71c84e431aa63e0bda561318761282b4dc70a3f88c1895c840a9b8a42d8f6242d417356d19e58d399b56e505963497ad2b8db672f355c72f50583ce390abfe52150473b58c579ac2b53079ac541e724fe079a79497ad559ac671745f1ac71ccc17e72183ac71340ab4e640a82fdac6717801a93f6adb484e428153f8cc57504b93cdc68155f19c6b0d18326882d417ef6207e59e8b7d21720556772c6d00ad2b5a9c20f62a10a35160d9b57d07e0f35f105eb41af6055a0c669586fcd7b34ed6a2c35317cd2b611934524591045d0ff6d2b833e3cb30bcd2b49fb02e7b5b075a5660b0d9a3e6305b56e055a4fda56d575116449f93463fd9346695b08e35e9c15a7708419002d4e3899ccc1e6cc2e8c62046629ad4c17e2df5207ab354d64ed53a0e3203daa63d5055cc0b41f9cbe3999c5e49fb554e0aba288b433093f5b016b207c1e60ad399c0f3055c0f37f0c4b03cd8172d4dab6a47505b30d63400f39872d215a39cbc17e83f81e62df5a3ca43382c83f312c0f3 (by decide +kernel)

private theorem part22 : Excludes 0x40000810000000100000000000000000000 0xbc66718323340c860810201028002480001 :=
  splitAt 1 110 0xbc66718323340c860810201028002480001 part24 part23 (by decide +kernel)

private theorem part20 : Excludes 0x40000810000000000000000000000000000 0x9c66418323240c840810200000000000000 :=
  splitAt 5016 137 0x9c66718323340c860810201028002480001 part22 part21 (by decide +kernel)

private theorem part10 : Excludes 0x40000810000000000000000000000000000 0x9c66418323200c840810200000000000000 :=
  splitAt 1 94 0x9c66418323200c840810200000000000000 part20 part11 (by decide +kernel)

private theorem part8 : Excludes 0x40000810000000000000000000000000000 0x9c664183232004840810200000000000000 :=
  splitAt 1 87 0x9c664183232004840810200000000000000 part10 part9 (by decide +kernel)

private theorem part6 : Excludes 0x40000810000000000000000000000000000 0x9c664183212004840810200000000000000 :=
  splitAt 1 101 0x9c664183212004840810200000000000000 part8 part7 (by decide +kernel)

private theorem part4 : Excludes 0x40000810000000000000000000000000000 0x9c464183212004840810200000000000000 :=
  splitAt 1 129 0x9c464183212004840810200000000000000 part6 part5 (by decide +kernel)

private theorem part2 : Excludes 0x40000810000000000000000000000000000 0x9c464182212004840810200000000000000 :=
  splitAt 1 108 0x9c464182212004840810200000000000000 part4 part3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part27 : Excludes 0x60001800000000000000000000000000000 0x9ff3e7d00ff0003c0000000000000000000 :=
  finishCode 49 0x6c15c5a0e62da2d351c48cc92b720c62f5c16472d4527eb39371a0c56471b8d27e80f6d1244a0c3d3305870e410851e480ac8cc02821481305a6a4fcdc72c74b3a821591c93d5b169b07f96665ab57ba42da7b17243630755916c7f166ab4b173c8e72ffa86e5a68f4d706e1b4681542ee9895aaf2c05ecea47720caf358ea68902ccd676f6789925c795e67ab579ce675abac3e0ea5c5969aae2684b58b8e4c95a6cf69579a7e6733ad35ccf241cb92b577b5a8bd69a5c76e141b171d69a6256a7c2e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part30 : Excludes 0x60002801000000000000000000000000000 0x9ff7d7783b38015cc880500200000000000 :=
  finishCode 49 0xb4370e62c84f75b158696ad2cfb32c7deceb4d1eaac7e461001eaa86e3d4a924fb2a0983acb4d7b4c1e55e6882bfcbd32d35ed6af36adabce721bdad886b0c3d52f4b59e6616c099ca497b3ad34bd2b1f6a3ad2cb81eabda66afc1e569af679a569079edf0792f4a4adaaeb62c89418fdeb4f5a6cb5757f9f66504bdad682b2330b635362f486bc386c31696ad2d243e1eceb419a9aa2f83cad0e0f3286ded27c359e2d6b4d630f3da56c6d1ac327dd2561af941b34d54367c1af660bb584fb2d4f6b3b556 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part31 : Excludes 0x60000801000000000000000000000000000 0x9f73f1782b30000cc080100200000000000 :=
  finishCode 121 0x1f883088078ad82e2f8b0958fa20982c06510934528eba2d5e35ab48cd7e3d35a6cd5b35aacce7b5b92d3bea1b83ac3d56a166a981209f9969aa211eaca09268ad0e5d95fe7ef35a93dc7aac3b9a46c25047c9f504ec1d5ac24f76a1305f1742e1492af19cded5b583a885a015cc947695c57d579b48dc86b0768169b17752264f7960e8ed9c92a491eaa68dc3dae6adb55ded2e6558e8f4e732b56e720abcded2e655f134578c9351e9a51cf93356d5e649d3e4cf635a8b035aaef6747fc1d4b85a0e46a169a98282e7258a65846b4b517a925aab1fbded66bf50d971e72eb92d6c681a80599b8e5a5a8847aa09d9ec61a9691cb516adb9754364d15a5b70883d8e7338e4560e5dd524ce67476cd5b7b1b99da04c124523a48d8773155ab7282e50dcd5b0e1aa8c3b87a68ed5b07ab2c1d696b078b859169aa0398dc3f84f7300cb354958f561d7ca33495acd569e3d596132c961ea982dcc6e1fc583cf6f8c3b56cbe62e730baf83d5948ed5b1d793dc7ab070e17397fc15f368be2d84f749163b0f4d61260b606cb17592b56d48af510e1ad35a0540c4b3dad26aa47492a8c430f3dad24ab0158ecfe2d892b969a2e7317acce312a807c190b51969ac551de9775ab72c7d6771fbd69b0758bbb351c9eeb4d (by decide +kernel)

private theorem part29 : Excludes 0x60000801000000000000000000000000000 0x9f73d1782b30000cc080100200000000000 :=
  splitAt 1 121 0x9f73d1782b30000cc080100200000000000 part31 part30 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part33 : Excludes 0x60000800100000000000000000000000000 0x9f51f15383b020040cc8001000200000000 :=
  finishCode 123 0x408e62f0a02207314f1f449fa04569a5a99ab6b51417cfa20c502306849ee047894ef516ada04475afe3e8b3385ce4f7078bf082f481487292527eb158b1ac534fcb9954364b1962a6bd7e169f2cccf5693f58ac5a92d5abcd6663c327bc18b62cde47692cdab65ff078a07d05efc2d09027e647693241e293f7d169b2ccc1e2ec171e83ab57cc40abcf630a18b7e098cc57599b905ab63d3078be8d23a0da5c9583accd3c6abcb4d62bb57c77b41cd20540f6b356c5be5c1584b15c15f2d34bfe93f7b8caf3606ac053cab4d5838b7df48312c078ad3e495a0bd67324ad204b18a3315d69f05963d8a475ec2b4d48cabc45be7ff905eb4330a2356e521a8856a22df49fab80f1969a2df521c3d5078a90e6af83c41e32d09025893f2411061cb48e5a5a3b4fc28115a6b88a439492c0b8b83187923a581579bda569ac57521d1877b4ad35812ae288aa338e62d8c0f85ce1c32ff9b84e396664e3981e2cd476acce5b059ab4d72ec8d10b2ad3cf5b356d3cab60b35d86adcb3917397252820ad8f5a37f5a78f566a796bd9c490d4251c4cb607a90dcbb399d1dac0f52482be408abccf82a21607bdc624297253cab4d69eca495a6ad8e6338e67836e8f5495ad2d01e2e72ffa58b4b8b92941407ad2e2e4a5054467053334adcded5b7bbaccc9a3359d69ec0d6adb155232b4f8d7e9417b4b0258ae3e170c556afac1e4768594d7f23b49330505aaec57 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part35 : Excludes 0x60000800000100000000000000000000000 0x9f5553d1133828040020008cc0001000000 :=
  finishCode 73 0x1d86a2040f4a80de1cc59c16f9281c372ece673a1c824bd927e7d95a7acd683ca4bdc9724bcd7ef614958f4e078ad5d746316c490386b0187a6d5b9602e67492cf6905db99cb932d3528e12f7b4b92dc820f18f5ab014a3bf8bc3e8d5b173a4fe72ea87523a80f969e93f7d0bff247501f24fd9c5a6ad3e733b9054362c9733ce4181140690e62cc3702df6b09eeb239282b4f9eceb2391f294161fc93f0e1b99e311ad356c691ac078cc3f0e1988e7b4985e311bdae16fad81c38c46fa282e34c9b8d27ea3349ac93f258a4de04830e62762e8937696ca474778f4cb8e0f191def719ec6af34a3a91c1e2b4d80962df6a1b8671487314d2221c34a382f5506adb51e733862548eb4f8f92e6749fa03e6a6d0796a7a77c09e1c3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part36 : Excludes 0x60000800000000000000000000000000000 0x9f515151133100040000000000000000000 :=
  finishCode 87 0x2c1063f03f11fcb50b607a59c7b4c81f720ac8c386d5b3988b245c725cb4d733a07cd7ef53927e5c96adad2c9a307f398a496720b56c5bed2b1e99cc540630e62b0f85be9239eb2b4d16fd06b49bac967b4c1ad24a1c30669cc5406e07d2ec3981e95b161f353cc5e625920f3535256b4d8c02625398a4fe725ad35cbab395a79cc5b86a127f356c3820c90f4b98b62d46371985cc5ea478c4a6e396a293f7514409bc7b335f93260f2af37b48f4d27ebc33813f9ed25c958b8b9c1766bf93ef1324d7ae67836ad356c5e0b3741d437ee412ffa9145ce1bf948b399d40571ec398b682df2008eae4a0acd52561bf59acdc13de31787a52446ac1bf2ffa4bd2572cd5a7af63f8dc10055f30b9c9ee62f47ccb4d44019b20c569a0cb9a8591ce6f60cb4f5ee28e70f48b9db827bc62f47ccce3f89e2b8617492c1bf590d073461b56d27e8f92ffc1862f1ddc93749f900527f370d6356e3d5a3fdac282f690832d27f2d353bea431e9c83f4929afe5ab8f4d62a1e9 (by decide +kernel)

private theorem part34 : Excludes 0x60000800000000000000000000000000000 0x9f515151133000040000000000000000000 :=
  splitAt 1 92 0x9f515151133000040000000000000000000 part36 part35 (by decide +kernel)

private theorem part32 : Excludes 0x60000800000000000000000000000000000 0x9f515151033000040000000000000000000 :=
  splitAt 1 104 0x9f515151033000040000000000000000000 part34 part33 (by decide +kernel)

private theorem part28 : Excludes 0x60000800000000000000000000000000000 0x9f515150033000040000000000000000000 :=
  splitAt 1 108 0x9f515150033000040000000000000000000 part32 part29 (by decide +kernel)

private theorem part26 : Excludes 0x60000800000000000000000000000000000 0x9f514150033000040000000000000000000 :=
  splitAt 1 120 0x9f514150033000040000000000000000000 part28 part27 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part40 : Excludes 0x41002800000040000000000000000000000 0xbeefd75c732a89548002823048200500000 :=
  finishCode 27 0x360e633873166164f3995a9eb530668775240e1ca49510cb3d8bd2d4d503cb416158f25aae1dd59104711245a5a689e3381a3503ca1b6a6c8f9940ea49523b55568308dcb8ed675a9cd2d836a88543ea336b0a000b7925706d6ad97b5ac32c5416e92b836b56d46612b8bd28e38c3ac55cdf06d6ada4ad696d4d8bd2d55 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part41 : Excludes 0x41000800000040000000000000000000000 0xaee6e358712288048002003048200100000 :=
  finishCode 155 0x400fe440ec3e0e637030b621b05c0e62cc180504b0774997317d19e5ed41ac6f75c1c4300a33e729b0758629475a7b0be836c61d43ec5f6adac56374ad3d43ed6150fc7d96ad9cc4e63370cc3c0e20774e8511ca6b4b584c835412cd61729ce6f729ce6f6b1587110171c4d06a91992565f5495c0c540dc83b6d1246ab9f66524b0acff65ed943734ecd6ec432faa886f78e4a7eb3e1a9f41e416ed4d729c0b772a9bddcc7119c5511ff24d4c2e6233eccc316b09efda9a62f066ab09e24f66a7a474dd27135120eb1c5da9e8356ad98366b39f6540398cd67495b4863d9b56da9ed4d733d07937d9cbce626236617c560e4a7d98e5ed5fa30e0b769dc7e5268b554fb32505abe9196e1586d1ccf283522718359e832d63673331198bd9449bcb4f398ae08618047933d4da76e5f6adb0bdab71adcdef356d66b1cc4c5eda1c965939cbd2272d3d9c6e1cc6d15441dc2db49a985cc469418bd4131bec19ad4f41acaa1d8a47985ed5b300a09524a93743035f30c5462b4f4a39bde6a78e6498e825518a50b2353cc02b23a306b4f72fb56d89ac2f879318348106ab39919ee4325fb0be2d1ac8cf7e9135a7ab00c58e5e1dd41aa06e6afb68a21cbd5ff02ed6125ff39282ee6a7b59d540c4c9476a686bd24a763066618a44d83330c5a9eac2f09e205504ae5d9ace72f6a6c5f5a0ea80b37d9cbc7b73135a9ed675f1b86d1446adc7db1eda0ece66b358046b1b0e1832ce42b22307c994126f749ba09506a1dd969683b880bdb291da76731522c6f76adabfc3baa45834673137b9cbdac30775fc6505f2d8330c53398ac166b3b9760ff314e6b0a8cda9ad675e18ab3974fea1d54129b46690b14d44066a0d66adb585076d61948eb4b (by decide +kernel)

private theorem part39 : Excludes 0x41000800000040000000000000000000000 0xaee6c358712288048002003048200100000 :=
  splitAt 1 121 0xaee6c358712288048002003048200100000 part41 part40 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part43 : Excludes 0x41000801000000000000000000000000000 0xae64d3187122c1048280100200000000000 :=
  finishCode 91 0xf8388cc2c8a0398b355a5b70fa3f84f751ac7333178c2dec338e5ca6b3d412ad3658896ad436a4941dad36397af0c02d5e390a09416e72190769419b847124690b38e63b0f6f943683b179aa894793e672131198be390ac25cde8259856b4d9ac33b0b094f2caff7b7a0ed04ae67946a6d14a3b90b098e5eb4d9b8791b488200179b486306b4b640a93dcddb18349ee7a98bda4f75a69805046b3cb536a393dd69ad552f4c5e15a69cbe5a6a88ce171d58791b473124728349a294717cb966524b55d69b251da5b357d436b4d510b586503b57c5f207d9a665ed522ad35acef6f9e4731ab7317c9ee623661582face416adad34e5e3d55f230f3d6523306d392b9be6afb99d69ab4d9aae5ed854a5bd0c693dd9c7313c317b59e382ad34c2eaa23fe49ab93e489b075985f178392a51e2c2b4f5ca6d2b5a682dd65b357e0f272f495c5f56a39f664a0b55d4057fc7256b3ad352565f55a6cd4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part45 : Excludes 0x41000800008000000000000000000000000 0xae64d3535530c10c0041608004000040000 :=
  finishCode 43 0x650b86e169b00398c42a81dd398c6e9397988dccf18bdfc881f4179b57e27bb57e732c835695a02daae617390c0cd0eec2f99a7ae6f0eabb11041b6839b55c5e6c5b8e2ed5758aad2e397bb0dc3e1003c81dd6a2c2f330bb57e72fb924e62b4f8e62d2b17cb57e3d9b4b56823db397985dcc57fcb151799cbe595b4ad782ff98bd82f233d8be731397c8cf60bbb00cd87aa2f90eeaa8a498e5e623317c72f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part47 : Excludes 0x41000800000000200000000000000000000 0xae64d35951b0c1040040000090041208004 :=
  finishCode 87 0x6e1d8661885e1c970f541821c90eab28d22b0b4d062ac85f548ccb4f836c5b559ac92b1dcad3e62f98bd69a919969ee6f06687759c6d2206b1fc066be05e0bfd65b178569a73159c9af65a1978569a731521ca2149a9cbd4931cc4bdb2d2d46a73117ca826488833479328249ee7310c6c7315a6b28bc39830b85f27316d1606aba4be2f69f65ac524c94100bd06d69cb8e5ca6a1b965ab4d49b97d45f3357d69ae634be30093dc5f2da2c0d572f6ca493ecb48661eb4e4af2a4949bd1873ecb4ecbeafe368b3d944272f065988cc5eb80f263988704c02f619226a21733b51dee24f75c09ef2924382a218e5e935065a20722e8b4d66188730e5e0b983fce6f265b57d6121c36afd073584c1e527b1838f52d67374b994792731397a86e8c1c1e46166f75aba80f6f73079291382d6e3f623a4de5ab95e6306b35185cb2d301742daab00b98dee72f265c2ff4a0bdbdedf390608e932d19eaff7b79cbdd85517416db55e05dbdbe6ab8c2e691b0acd672c24e5e5ff (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part48 : Excludes 0x41000800000000000000000000000000000 0xae64c31151a0c0240000000000000000000 :=
  finishCode 135 0x1206e127eec310f03e0b203343aa1dd483cb4f495b4ee839ad349eebe188e3179c94e66e679ab681b4a09c4c39aca2f0ce358e2020e69696b438a3d541a8315b4471c92b3f2a36cc5e7252fac6f71eaa36e1eab0bd69a0b5471c58f733871569ae418e4ae675a68315288007aaaf79caa60d390a4ae495c8356d19c6b1e4066985e1799cc62da93dde458fc4f71eda51d016e6591865d539893dce2f0c2ce62b4d41acd5b27b9cc5b47f0e2f1c94c4662f399c0b98e62d5b27bb68ba0f6e3929cccbff1c5d5c59174600dee2d3969a0b91cecd5b5a6a44d6968ef9ea2b39489ad2cb7b1bdc73a7315a6bd4662db8e5ab66f75a6b2888278bc2d357c601d805ab681d5467c717263cc31477a51cdf7244cc5e731551341edc1ab398c1dd83fcb11062bd8cb8ed5b398c923c8823707db317c80b5d188f3925646725839d1832ffa405aceb356f01872c8c69f281dcbede0b4e623ad3d5ff357d8be1b3732b90c367359cc5e0c573164398a48d620eda77032cfb662f6ad98be065c62f6ada0d51cf251c39ab3d690a0d66e1cc761ac62019abc205639887552330e7ce6662f0eeb4b64fbc1d49eec4202e69ead4c3aa1dd1d9c80b317c2d30658776062ae859b8fb60bb3928f6ce668cf86163af2ff9c5dd85e1c841aa91e27b8f559c0d8c6d12e3a054c32901492a3be61ec010618830b72acd4572fb925ee2c55405a42e0eea4bd612c5f9492b4f0eeb955cdeb239caac53179aa8d3b9ab6e6549a988c9ee8818be591b56d20262f9a76b47 (by decide +kernel)

private theorem part46 : Excludes 0x41000800000000000000000000000000000 0xae64c31151a0c0040000000000000000000 :=
  splitAt 1 81 0xae64c31151a0c0040000000000000000000 part48 part47 (by decide +kernel)

private theorem part44 : Excludes 0x41000800000000000000000000000000000 0xae64c3115120c0040000000000000000000 :=
  splitAt 1 99 0xae64c3115120c0040000000000000000000 part46 part45 (by decide +kernel)

private theorem part42 : Excludes 0x41000800000000000000000000000000000 0xae64c3105120c0040000000000000000000 :=
  splitAt 1 108 0xae64c3105120c0040000000000000000000 part44 part43 (by decide +kernel)

private theorem part38 : Excludes 0x41000800000000000000000000000000000 0xae64c310512080040000000000000000000 :=
  splitAt 1 90 0xae64c310512080040000000000000000000 part42 part39 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part51 : Excludes 0x40080800020000000000000000000000000 0xad45e17c156404858013004040001000000 :=
  finishCode 65 0xec350f03601d583caa220d641d9f106209540551f450fcd6152293dd46b2c1528eb1b9ec67ef5a5b3813b9612e655a3a44da4323bc593315543e4f75f143f13dd28ea45729cd2d2d59c4d60ab096911841fc73340aa0d59c41d8e5e58ea51c19af538df69e539987152849f8716696b094ddac5538b8f545932f8d22488624dd076c53948e9355a1a930ad5aaf2d4ded2c53390cb477b4a4dd06b0759ac27f5390a48ce6693f8e26835670ec6b1226b02a8b473979ccd45f28d58aad3b8fdeaf79aaaa47390a0fd26ab4795460126ad20fc5eef13ddac3397d87b358b81cbce66b1b9cca83f58dcb4f3f8ca495a0e5ef538df637561ead1c5bea0998aab53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part53 : Excludes 0x40080800000040000000000000000000000 0xadc3e1f807260c040022022048010100000 :=
  finishCode 43 0x812206c1ac398c009e41d63999c4d4671cce0ea0c9368d06b6ad8325487287d6a6a4740ab70ec248be20ecdc6b104aa1f397c7ef58dc7a9609a925ac3291504ab4b582c825598c7132f69fbd02a8354a14132bcd67a6fb523b387219ed2b5349ab5867b4a87ce27370d0360d43da63d9a05419a1d50f2a18e4ba3061bf399ac9dab6b534919cce5a9a0d54132915076c4d98866f7390b68a45928e3db382b56ce5ec4d924a6f76e07e32c141967330f4ac461e1ad4ce2672f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part55 : Excludes 0x40080800000000080000000000000000000 0xad41d13c1fa44445000004000c080120040 :=
  finishCode 75 0xec3f0d8390d420ee7a88b7c3aa1e5751a4571ac72d4ce6283b16fbc8b399a426e349fa51dab681536fc7d583ab56d0631ccd27e7f596a67337914483dcc3b5919f152460c341da4fe20811603989fd615c97b47e2c3b98aa5ed9a5ad61593a9241864b7412cf6915c8f0528e3f18e62f2230be209506a3d5893aa1f4a3bdbe23aad4c35a8ff5a5c1ad5249fbc9ee83b3ead1877b5961435ab4b27bb60a0398c01cc60eb41fcf8206141f8564d42b390e88fa419320fcdaa81162018b0ef43a25ed926ab33818a0c9460e85816a3356c7b65d52f6a808ff9ac2f6905bac2569e6b79ab70754d174450e663db0d6ce4383a971d64b356d857390dee2b1f5a8b97e2ee93dd28f2bccdaad5b60993de0c6915444148f02cd26e9476c1ac6aac73349f832d81f2d1ce624eda0f6af159882d54669356b11c061abee6ad9fbda42a35732ad1dac2b1b9ab61359edeb1b16fac9c16a731907ea1f8196733 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part57 : Excludes 0x40080800000000000100000000000000000 0xad41c17e0f26440c0820000080008020200 :=
  finishCode 37 0x801e46b1a0389b60be39872f69dcb5383fb03cd2293506593dd06b079506b07a506b0f55662815397a0d683a9ccdf8761a8246c3634f9bdaded2a0b598a0543cab479076a1f8382b315a3b60b3b9ed31831f8ad44bda935398a4d627bb50fc2d81e57b5c0b5696ad2d8850493dd5f7281dece3d5724cf67066c73127bad2e398bc0d8358616f87557c49ac0b327ba096398c1c3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part59 : Excludes 0x40080800000000000000200000000000000 0xad41c13807e5544c0101040000100010000 :=
  finishCode 99 0x1b06a1a0601b854126f1b8d0763f10d887059c41da4fc38a36796a6a0d591a924186b1b97c67106324fcdd273305882e415b1cc53cb2c447e2e4358901bde389b68dc1cbc59341d5ac2d5b7b187a5ccf2045cc504ca475a7b56d646731265cd5b1dec7310f2988742d4c8c33dacb12b1f265b9741865ed49bce5d061ad1e061b975f8751cc49fbb0731164c83540fcd5b1d3c0ad6ada0d5ac739047aa0ad5b174410a78e37b9ccd6a3204638baf8ae2d8b23580af1edc73172ead1d0427176ad93de3f88f4d076d620c6398a4ddcba1958e6293754148f24fd87a7f14089bb6399a4dce62b23a0d6d2136f9ccd02281196c501146b166ab4b6e0e5efc1f56164bd4dee23d57b1a0d5ab73d8c13b1878e26947968e0b35f174601ab713de0de6b758f82cc15a7339076982c7c9ef0da5c7a3992dead5e27b9fbd6671a441321a541aaf8d628872f467cf5158eac25cb26b76ad9c5dea33d4641da92528e3d5985682583abc900358ba35072f7e0bdae679cca3d57b7cd2783abd8e389abfe5968f54e2eb078bba82589ee5dd94621ad (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part60 : Excludes 0x40080800000000000000000000000000000 0xad41c1380724440c0100200000000000000 :=
  finishCode 109 0x1405a6c0910360d01cc5f86e0bbb030c3d2835721b416fb8e649bc60c376b4f3979bde492b56e1a8b4acb8e93f3f0a4dd745107e3027c7b6d60fa5a5b2d3dec66f7397977637dc3e92e3c83549fad8442c7e59aaf8b4b696c0b3411a8f20d5a727132eec4a1412bc8be370d017767b4bdac32a947583a44d4931f6d076b072e3c925397a60fc370b319492b072f6a0d5ccb17b60eb3d9cb8ed5b732c3db583a308cb9a56f6b2f6bdbe579a7cd492e6515ca8c5eced03c8aa2609a05e6397a08504a9374a3b00d420c6061875564607c7e159ea0d567b0b7cfc2af76adad4d07f17749eeb316c1b8492c2df0ea87954416fc1d6591c1cd24a7336adc60e609804e0e6925397acd63f7b60c5792268257b487543cab1f966ad80b7e0f2ac7e05aad2cfd724fd504807e21e98e26f6949fb5898030d28f2d4cb572ce4e5e9239662dc24fcbdb34acb5e1e9588c0bb6b17480120389c721510e5e0cda0ea3538d224a56b0ac1419ad42480c9582c9353eda925436b07961283583ac947408b40c42881d14615f31f2d6a283558ec83b579b56dac3209562eaf37b78e9e4899b555e72d4506a762d4e3eda05472e90149bac267b7ac1d28ef69 (by decide +kernel)

private theorem part58 : Excludes 0x40080800000000000000000000000000000 0xad41c1380724440c0100000000000000000 :=
  splitAt 1 57 0xad41c1380724440c0100000000000000000 part60 part59 (by decide +kernel)

private theorem part56 : Excludes 0x40080800000000000000000000000000000 0xad41c1380724440c0000000000000000000 :=
  splitAt 1 68 0xad41c1380724440c0000000000000000000 part58 part57 (by decide +kernel)

private theorem part54 : Excludes 0x40080800000000000000000000000000000 0xad41c138072444040000000000000000000 :=
  splitAt 1 79 0xad41c138072444040000000000000000000 part56 part55 (by decide +kernel)

private theorem part52 : Excludes 0x40080800000000000000000000000000000 0xad41c138072404040000000000000000000 :=
  splitAt 1 90 0xad41c138072404040000000000000000000 part54 part53 (by decide +kernel)

private theorem part50 : Excludes 0x40080800000000000000000000000000000 0xad41c138052404040000000000000000000 :=
  splitAt 1 101 0xad41c138052404040000000000000000000 part52 part51 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part63 : Excludes 0x50000a00000000000000000000000000000 0xafed75d4057a80055000000000000000000 :=
  finishCode 39 0x6c200680c4718bc3caf6368a22b07256b1cc5b41ac1ace42b4d9584b0e5e80f907eb3998128315a6cc09407a0c54c41acc4d5a7a07d6970f557859ac1bf61ea0ecc163d54b037f13dd6132cde6ada0d43aae22b1002c8bc36883b680c47183504b2cd4e5e947963e8255a7973e390acd569e6018c1a805969ec5316d93dd63f13de (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part64 : Excludes 0x40000a00000000000000000000000000000 0xbd6875d0013200055000000000000000000 :=
  finishCode 123 0x851b47c20c7d1b017c8c2c3ab1cc57c6809eed5b9466d5b96371fed6a693d6a19817fb60d007a61fcb09e5918ad569e7312f0cb1f389ad2ce632d35b0681981fca88b478df67255b101f2cc4c46b4f398d07b8dd69352ffb536613a0fce6214d9696b4d69aacc4c2e623a0ea4f7135ac250168353909ccc5e6f6400cc290e3129c4ce5ece2487058c167058c2e7059b0060cb4d0649cc5c45919c49126b20ed45ea490dfc94746120f359dab6b4d412824e58d976e582b08da56d4f510acec35b2c15c82b531eab4100338d359abe3af398b124db660b3179fee3719cc4c1a6db064c731670587182c51f13b5abe93d36da095b0571f8398bd86f783d2b4d079b40b007a5a9b0fa58bf2d3c4bb1fecd7a4f71388a0d69e821969a4017b0fe320441e6b4d6e1a00f4c6016b1c06340ab90661ab92cb83063e083b8bda4f7079b3892340a49300cb4d6a6c1e528ea2f8fb3251c7232d35ace6f75a6c3d5276b70f82a81e95e1404009ee741cbe2e89bdd26a5ed510fcb2d258bea0b5189c945ab394d412a47599c8356b3ad249a2a0b519a51d043705ab2d4d416a33660e5f251d02ab4d928ea31837e94716a9cce62486bc9a24f75e14132054e4b360da3d89078ba20c93899cbe0f31345c8282536d832528f205569a3b9398a51e2769cbce4b17b48026f7 (by decide +kernel)

private theorem part62 : Excludes 0x40000a00000000000000000000000000000 0xad6875d0013200055000000000000000000 :=
  splitAt 1 136 0xad6875d0013200055000000000000000000 part64 part63 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part67 : Excludes 0x40100800800000000000000000000000000 0xafeb47b431380d052048040040000000000 :=
  finishCode 73 0xf2440da350bc0be5b072102a7317b4cb3941db0f54128e7987a4f7943eb424fe27bc1ce268b02d8aabc3f0ca2887315907a7357d26a83b699ca33598b585226a09948eb3172148b282527f1b8d1ceb53629a44ce63310fc39be69dacc527eb534eecb0f36a93dd87ac537b3c7fb3e88f6d780eac5ed518a824e629041ce7b492cd5eeb4f27ba4fd7448093ddc872d4472ed4d837a90d81f3dbc9a2d4d57baf08c2588155a146724dc9eea47928ea1f491a8263f8b4ac3aa9375118af3da52261d541d87567b4a82526ad82d096318a024fd7427b92b64809f456a6c0f9ea2b4f1cbabdcb47303dea2a02404f75a3cb23148bda5a8b131e405b5147b66e37b5c7f1405ad3527e82308e5a99fc6611cb5327bb60b41cc58c16fc4f749fad3e1e0cb27524ad4d6a7287dac24f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part69 : Excludes 0x50000800800000000000000000000000000 0xafff4374152800052840040040000000000 :=
  finishCode 65 0x761e06a1680f2ac84f75b11858facd4feb30ad89aa098c1a83b579c1ad618cb273d4bda4bd2b3162104521ed32d4d4670f6ded25e99c9e6256b3cb4b7b4b98c42e081b9412625317bda627ba914c46aa28765238f6d41324fd4c40db4ae7b4a4445bee557b5c825691643f103683b3f8c8cf37dbddd27e4cb311c62f40ac9133008ec637da444c4693f691545a05bf13ddb4671c8724d546262361dcb535e1506714627cba0f694750fc7f12e3b0e4fb6b2386e6f69477931e2e3ab8d8318880b7d503c181e3d10bfc34d300971d6a69018c025c7477cb27480931cc025c782eef69607ac6cc5eb535a3c60d593acc60e0ca0931298be (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part70 : Excludes 0x40000800800000000000000000000000000 0xbdd94334112800052040040040000000000 :=
  finishCode 155 0x1e06c170602141fc9005b4670b071cc43d293718598bc6170e143d3180470b251c9eefc390f207a472b30f526a0f31859d0c43584f8730bd31838236f69729ad4c9c6b31737cb4f853ed3b398b955cdea4791ce6e369dab81879a42b53271acc527f138e1449bc5f50798c2ce449fb8e6737965cb8eb4d73140262cb533f89cc56a717b5ca6e390d5ce39737b98f22d030b583c4cb49b9b549eebc28765199804fe27317b8cb1d5a7ca1d6b1c1b566a4f7398ad8cc218b5187b6b395a7bc8d42b05ed732cb2362aa3bcaff2c8ded30799ac29377b4ac8d6a2d3b9ed25ed7919c3b1105a4b97e488ac1dede93769dcc3d8c3a4d5a5af51926ae4962997d560f06d91def6f1edc1b6473b58589a5ed926aec3910207a5e466061680b904af6f7b4ad4c5be3bb927f07b30baf0961cc63071f654124f749fcb318916f6702993dd27eb31987a935185988d87f41e560a4cb30bad4c5fe30b7d09ef03cd5c63174398ca43477ac6c5beb53670fb33da5ec69f9584988dec324fdaab2d35ed2aa24d6836819cc46d494fcca07851e47d19c1ed93dc1e6c1d8df67ad59dad456132d2c6cace2f0aa1786020a8d53f2911412a4d4c2eec209617fae8b09317a8866b0ad4d3f33485ec7096540e6b724eb584c2eb356614041dcf692faac24df6b3537dcf5158dcb477b8b96587ac555a6ad8cc2c8b42c7da5ab4b8c3c5ed05ab0c6524bd9dcd6822d1e6a393ddaaa4f79ece5e97d1ac2b3193ee4f715ecf6f25886ac6cb30d53ca7d57b397b558671542e8c92327ba51d2840a9e05d196a607d37da77662fc0250bfad35666b474eeb9666ab80f4ff64f740ab98aa2d0e413dd6a71fecdf6a4535ecb4d3fdac6e5a497b4fb32c6d0373f0617927e83b079b68e630f67b09784fe273137d985c616ce2b0b338bda9478c3cb390d3ad256a27cb969a5ed2f6cb51 (by decide +kernel)

private theorem part68 : Excludes 0x40000800800000000000000000000000000 0xadd94334112800052040040040000000000 :=
  splitAt 1 136 0xadd94334112800052040040040000000000 part70 part69 (by decide +kernel)

private theorem part66 : Excludes 0x40000800800000000000000000000000000 0xadc94334112800052040040040000000000 :=
  splitAt 1 128 0xadc94334112800052040040040000000000 part68 part67 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part73 : Excludes 0x40140800040000000000000000000000000 0xbfebd7dcabb10a0d804a028100008000000 :=
  finishCode 7 0x501b06d0e622f9903e919721c4b340fc1fd042b4d981690717c93dcfdf3515ac22f9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part74 : Excludes 0x40040800040000000000000000000000000 0xbff8d358a1a10204804a008100008000000 :=
  finishCode 155 0x3e0d03007210055c451d87a8971db4791f46e0616d55962e93559dad45aaf0bfe5aba79e5abb4849ef18be4f397a5a427ef791b4761cc690cd5b5ab98bc6169e2d36735b55d9c476cc5b4f3acecbdab496adc62f8fdeb4d9602d5b732c7d935eb4b5143613c7b789e5cc5a6bc85ff85fea1f962a3b36a2b55e838cb1d27ba20ca398b4d185cd5b83893ddab72d45ac71eb522262f6adb98ec2302ff1a9c69d2f0b57c953305c953358cfdeb519aaeb174413c6ad98be696ad35ac31adcaf2e63e84c59666a33348c4b158bcda398f23b0c5396ae5ff18598be3f7be8a458fdea1f27bab8f679862e597a882adcb32f8902c5e7b1ad5d692d2372c8f6e7a8acb56aef634803233525ab73dc5a465e17b1813683cbdbcbdab2d27bb98a0370731921630b27ba32e7afa8c505e731839c5c741f8c2ce4570b45b1ede5c7401b45220f3055d60e91d4a0a466583ac1e6b0b99560f460d2323a73f0ce656d1885b0f8497ad362faa4f569b0e9c766367894ab4d4839af5ab63b387b66d58dee8017b61ed89e60fed63441eab3d4569a1779a42da280a42d8c2b8d2af511d3a4f525ed5b9c86e497a8cf518fc31264996ec3702ff607c35f39893dd023278d86a6f76adb10cc172d44fde81f731686d09da9e1804c4af639cb2f535a6bd7e7b9c94737b980578607b687313e7c9e7587b55d2231f3e3e1806d1682c4244648cac5e6afb9266ad9b54b4af732fab16d8849ec6d547185ccbea5c78daa3db51126f2ced692ac27892583cce496afac5e583ce49 (by decide +kernel)

private theorem part72 : Excludes 0x40040800040000000000000000000000000 0xbfe8d358a1a10204804a008100008000000 :=
  splitAt 1 128 0xbfe8d358a1a10204804a008100008000000 part74 part73 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part76 : Excludes 0x40000801040000000000000000000000000 0xbdecd358a1b0020480ca100308208000000 :=
  finishCode 105 0x851f4792006701e6ac340c43689218954370f4d20ea49615cd5f690abc520eb4947fac562faa49560ea1b4a3b93e50dac1d26ad239436a494a0c9df6afa81d666b07561442fa8f6e37b934562b27944aab113e79fee468b9bcfb2d67483b68f8338be0be4dc598c9df27bac1d3eea337b5cb05838a915662d61598cbe348e483b4cd3ee4f7582cd216a6a41d646716c48cc1c3476c3d3483a92560e9079a4723be2d682ac9b2b4d27bb70e62d84f737178524ce530e1b58543ea33331aab24f42e69f7696971c34725045729e76b0b8e4b1f316d282d556b0acb6727bd9d686a33522ad8d3b9282d617b1cb01596b48dcca90762d9b8b41943eb1596aed43b0ce2f8e62205ff62fcd230e1a925862b4d5d15872fcd2350d870d492d2b962b2d5daaa2b19492d2362ab55d686b576b0cd6762a982d7c5a697a66a6ad5cbd3124e3e7b56c9a2b4d2ff971e0dd870daaad616e1686709eeb0288f638386d2b16aaccd1db070dec66b7519ac1c5aad2f9c867ef58b870c9a3316d69ab6328a217b626886bda0711c73394c2d2e4372fac5522318798be661ade09f9fbd1b6b1558bd18709db10d1dae43521c872bc5ca70790cf97b526b390d60341bd28eb07732ae8ce1c161bba495ee6935732870cfdf1c1520eb4d7a8cd57 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part78 : Excludes 0x40000800040040000000000000000000000 0xbdced351a1b20a04004a002148008108008 :=
  finishCode 39 0x204852007c0e6310041e6e6338bc368731588c9075a49894c4692594369376ad9f65493308d3be6237a9c92b5a99c14c1a7314d181ea229262faaced6a29230e499711ae30ea1b729c7d96afd187737a88520ece3c8d40ee6268a924e622f93c1487afd1834f3b514386d21607ad4c96f41c5ab68ff6aaa3fe398acf641fa084e62469907e4d1582a79d6a6c0f48c9cc54c200b10e398a36dc8683f721c73180181ed02cc61e18c2c802001847ab0f6b396bcbda93d9ab62f9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part79 : Excludes 0x40000800040000000000000000000000000 0xbdcc5311a1a04204004a000100008000000 :=
  finishCode 147 0x511f049fc00d0398c02e0fa0fe480273189ee7319e46d1f48106160f389eeb318786b535b14c467cc3d0d98eed01e8c39ab6b475a6b03ce62731981eb4d398c4f7398c4f7811785012830c2c9ee73185107f356c6161e9901e90b861683f27bc28ce3b0b60c2cfff250507eb53830eb31729938d6631895cdf203dab6b623be4a0a0bd07e9a241e408c1ed6a23c3729c4e3737a41e2f6c1cd282d5b0799005b4851d87d05fed238bdad5b079a90e5b1ec0e19cc6407abc67a89345ebf1664b46e654769cc54c5e103eb3b8e62e5f96a273189c71cc41e6a03384f7521c4e317c9b8e58da42c9c6b4d981e9016a29fec5f2e6328be1cc4bb7188d8161c3276b90e605988d3bf2d4d20e62f276be8da1f090791da919491ca7132d8467fb6afce5347fa36e2fab56c996a43a007c214791cc079b02e17fad34e6260b521cd5f200ae0bc1005cc5f0e6290791970734ef9b8d43e4f7417cb60ae6696966c3d29df49ea50493b07a520ec2b62d9b8e83f85ad062b4d4b148f1cc49ee1c38e62d02d84014b1062c198926a3127ba0bd0048ed07924da7d4e632d349ef07a4e624f7969a731417a085cc651b46715c4efc623398a789231565a69c14c167cf89daa4993be625276ac464959cc4fb323fd60ea212659cc581313b5222d2d265988d9c601b45613c3e1436d57583cc0d729c8ff7a9ce4372492752328ff521c1ce58bb90d8af1876afb92647f932d3e725052324cb495ca03e0960f06418bd8e0fe73161cb0fc9eebc3025eb341e5a92d5f488a7d4bdad39398ad4e836b4eda5b277d64e7315a3c2f9 (by decide +kernel)

private theorem part77 : Excludes 0x40000800040000000000000000000000000 0xbdcc5311a1a00204004a000100008000000 :=
  splitAt 1 90 0xbdcc5311a1a00204004a000100008000000 part79 part78 (by decide +kernel)

private theorem part75 : Excludes 0x40000800040000000000000000000000000 0xbdcc5310a1a00204004a000100008000000 :=
  splitAt 1 108 0xbdcc5310a1a00204004a000100008000000 part77 part76 (by decide +kernel)

private theorem part71 : Excludes 0x40000800000000000000000000000000000 0xad484310812000040000000000000000000 :=
  splitAt 4753 126 0xbdc85310a1a00204004a000100008000000 part75 part72 (by decide +kernel)

private theorem part65 : Excludes 0x40000800000000000000000000000000000 0xad484310012000040000000000000000000 :=
  splitAt 1 107 0xad484310012000040000000000000000000 part71 part66 (by decide +kernel)

private theorem part61 : Excludes 0x40000800000000000000000000000000000 0xad484110012000040000000000000000000 :=
  splitAt 1 117 0xad484110012000040000000000000000000 part65 part62 (by decide +kernel)

private theorem part49 : Excludes 0x40000800000000000000000000000000000 0xad404110012000040000000000000000000 :=
  splitAt 1 127 0xad404110012000040000000000000000000 part61 part50 (by decide +kernel)

private theorem part37 : Excludes 0x40000800000000000000000000000000000 0xac404110012000040000000000000000000 :=
  splitAt 1 132 0xac404110012000040000000000000000000 part49 part38 (by decide +kernel)

private theorem part25 : Excludes 0x40000800000000000000000000000000000 0x8c404110012000040000000000000000000 :=
  splitAt 1 137 0x8c404110012000040000000000000000000 part37 part26 (by decide +kernel)

private theorem part1 : Excludes 0x40000800000000000000000000000000000 0x8c404100012000040000000000000000000 :=
  splitAt 1 112 0x8c404100012000040000000000000000000 part25 part2 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part83 : Excludes 0x60000081000000000000000000000000000 0x9f36dc3c2a03300cc040810200000000000 :=
  finishCode 155 0x168440e483169afe3c9043400f13218c39ba49522335856a2b1790328279072d5b721ce5f0bbac1d692d02b8a0356e0a180b5a7a3533d99ca4e562dd41cb08827521ce45386965e580ad45a9ea03a0d63182dd596cb576adad24d7f356d032b1d835a73789c236b1d5b55c9c33d9e3026af596b99563ad2b3fbc5c76ad86ed692d62b05e0b755c27fc839403855e691b55c9fe5bf0c1d18127fa09dab6d679a7ab0940c93fda573d9d4924ff6815827fc5bf16ea44ded30f4e302b497bb86ec9feb1f966ad5b1d3ad25a0530e561ab96760b34139ca41570a4e380ad25a053130500e1afe31019d94865dd41c97d4e52ae2c76403a0e630f27cd486191521ca491e29ca53e7290dcc2729501d05b05a28199a6aa276ad86ee30f2494b7ed237b5b56ce6f20dd8ab2c75a6a4ff5e1f0820beb293c1e24ff54107306649c2b399eee5f56adc5f55a4c9eb52786450725f5511fc5a4a000f16add18735fac3d20e19160fcc0d62abdbc7ab293ce032c1d49ef2410fe3400f1621843e05ba72b61dcb3b47fb59d6773dadccef691eace6716e9c3d65b292630e8273d6cb57583a90d692d0308c42a02dd89fe7376a2ca43394a603d3989e70d72ec4ff6a3bd9e579ac2534380cc597b5b90d436b4935fc9df834ac3d492d0350827722c1ad6b3a8354869a353e264bdad61eb51629c4e1587bdadc84016929823e548716c5a573da58473dbcb8e9199436c02d8827503c81958493fda8ef6b8d6a5bf2c2ad0da7aa4927f93fe6a3a01da06020c41c9f80f19676937413bc9042b00f17b5cd2b6b0a885ed3353dcce3d39c922dd5a4c606510b5149fea4394929ff413bc8f83680f1403cd610279c749feb1d958732cf6983ca01d24a1af9ed3355500e7e2480f15a49fddab73095ab730351f306ec1e2b07 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part85 : Excludes 0x60000180000000000000000000000000000 0x9f3c3e7d000ff00003c0000000000000000 :=
  finishCode 109 0x144631207b127ea8300ae2802df6819c694c0f1058a0a5072f82bde51ead35ab6b4f6a1c5c16adb50e5a682a63d6b56d63a0f1501f082037b02c41e2d5b969a737586b406024961e9acecff23cb9a4692569486f5a871705ab6b1d2e0cb4d46aac741e23d37a1f037fc4ff5a683c584509b56d63b1bfdec735351daa3d9ab6d5b969a0f116fb08c43d4e0de82b4e52a278e1ad5b4889fe641ca8f4dc7d1ab68c1d8e658d521537b18b7da4ad595a4ad45947b8c7f70d7ad35ee31ca45beae3d8e27f9cad00ef6389fe72b0d7c8377b18b7cfeeae3082df053c7295616033574d7a947836c0c57b8b13d85294789fe72b370a8501ab6d439aba81956169b1afda568ef7b486f528ec21326732b13d61272969ad181488bda4b82b09839b28fa2d3540571193359e3021630a99ca506e8397c103334a4e6e0f10a9c8ff4928f2e69583c4fcf20dcdff3d8454ae6541cbd4ce528270debe8f4348982b07296aecd4583986f528eb4f9a8b0730cdcd3d2648f2c1e273783ccb2b69fac3569e72990521bd814af6418fa3400f150128ed678292b4d6a186f5aba6bfa0e61bd477b156053b50d69ad02a8839928e7f79ab283959aad3616fa784f5969a0ab85be73761166b0294e6ec5996123d5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part88 : Excludes 0x60010080001000000000000000000000000 0x9ffe3f1dc283b10281600cc802010000200 :=
  finishCode 37 0xa22d09017093f4f11872ead35ec71afd47ad3b9ab6f63490dff2d451f236d942a38537fb56d27b3495ea2d5b681ecf2c9418af63387b56ce56b33978671ab68c39be0dbad45c48c0c0c51e9a49630324bdab2921c06473a4bcb7f23bdabb1817b4c1cce3ad2461e58e971d84a2dd38095fe725a475a4460e0680e022dd925e6bf0629c7630f0f54f6a6bf583a50651dad3523271d6accc2516e9cada87247569af69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part89 : Excludes 0x60010080000000000000000000000000000 0x9fbc3d1dc01331008040000000000000000 :=
  finishCode 133 0x340a0338be240802066414a78c420e55869fc92316e873649fb4a544341e5222d5d69fb102df6948b0639ba4466929f8ae2387020dce3706e4e56d296aeb2072b8372e63a302b417d1a4b251ce1e94783725f5640e570734e5724d5abb20ddab61c95b0e0387c1c9395a0243432504e56737483c1cd7d1247b4c1b92fa9cdc77292f4a0ad092b839a5f59ab63b96aeb5760dc97d5a44613c391f46959f8b259cc6935386a36d04e70f4c0e3a4c9a30f1812c986dd69a8db69ec59347cb387e290e524a4de49ab9060e6ad5d88651c8b41cd04e71b060be8d239ccae411ea9c6c95e71d8c0cc096adb15c582e4957169306dd4433d45ab670d49fbe8c43036464c1cd6762dd38d9c75c87116a25a99ab6e65386b53d1f30db5cca175722cb17670e81eaca2149bc1d526ad5b94868ef962f0757d18838dc1cd39bb180159ede5930dbac74b82d5b49fad364929705ab6ce29264a3a3be16facb59c4c169312856866ff51aab8c4209d693314d24a1cd599cb4d733828dab6c259426b1d5a6a476671f44d0fc599a9894290dcdf3da4e02b4362ab97e2c79c060da90724cac1d90583b0fe514a4f45bf303d6aee5f583cc4320b42d8ae24f5282d2998aea159a5293f942aa49920f07761fbdad282ea0d6e6a1a3d5682b57521c9e34fe30f356d656d238c3d069381486a228d542b35745be4d16ada7fe527b5751db181610c1bb59bb48c5befa2476380a5049a346047aad5b (by decide +kernel)

private theorem part87 : Excludes 0x60010080000000000000000000000000000 0x9fbc3d1dc00331008040000000000000000 :=
  splitAt 1 96 0x9fbc3d1dc00331008040000000000000000 part89 part88 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part91 : Excludes 0x60800080000000000000000000000000000 0x9f17bd5500c330400040000000000000000 :=
  finishCode 51 0x7a2086a19c0f4a80b334916c57fc8f55219fdce029416613c1eaac1e72e9fdd8773154312b412e4cc2547aacace032d347aae558e02b07491ab71c052827019ab6b4d1eab409a1d8b4d981a82962b9c75676b51601401f4c837579cd5b0a4accc942c0f38ea09d23b2d3500eb3354101273791ea8291f093fd0732cce681405f07d272985be83741ca02637f87656c5a0e5306ece6e8278e3a8279ed2c570ecac7478725045beb496f11c16fb40b5787d28373f1666b418feeb0787a720e56ae0c5599c3e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part93 : Excludes 0x60000080010000000000000000000000000 0x9fd53d15282b3200004cc08001000200000 :=
  finishCode 61 0x1e8681c87d03d3023f8c603c5442d1cb2527f8f4d27eb5140cc70d27f9ca66a28b758c1e9c93f6afcb4d72e9cdc5bac03108372f4c92539bacee4929cde403a0a6052bda526a937413a609a2f093f9cc693549bbe8c41c6e49f9cad27f03c5c8ea43927ee633e4c70d16ea0a500f209dfc7d1c8078a887f79ab693f5a4ab8d259eb68f58368f5414e7f7476cc55733b0347aa0a7836ed4278d5b521a885cbb3dc474eb4d1d2cb6309e834829cfee1bb83bc25b6abb03cb8ef691e9c93f6013c4714441bc1de50dbd9dab67f749f8f4cfef2d055041cac567229c356aed5b9c96e67631682b57414c5c749fad25a5320a4e532d4500e71d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part96 : Excludes 0x60400080100000000000000000000000000 0x9f9fff1f839332240cc0880100200000000 :=
  finishCode 21 0xe4240ce2d8b495a18849f9f092b9ab693d2e0c1bb6ada504fc3461c5beb4f491ab72c3ded707f3fba505ab706ee0ef16c5ab6c4149fab8700b3586f39549a2d5d3808f4e48cbd8e5a6b56cb8293f1e9cd5b5a4a4666919c0415693f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part97 : Excludes 0x60000080100000000000000000000000000 0x9fd5bd17838330000cc0080100200000000 :=
  finishCode 153 0xf43f9021a80f14f0e41f0e06a2b57c9a32d3d69b0dfd672c1f3f168265a90d67330e4fee2df4efd0775a0fc2d579eceb4d6abcc1f69ab3892170a43699c7e1725c1fda46a355a0fc33d9d49e9eba0fe6bf691bd9d44571ab718194421b33f0c2df8fee7e15a1edf1f85a46a2916fa93e0d73d4d60307f268b0a4fc671a85114866b7a30eb1749fb56d68510cd4372186647aac299a4a7e158bba8e41f02df35bcf69699b03587a6b789961bb48015e1a5927ec39491187277d1db16060ea9c41fe5a5b4cd8824cb627cd5b6b386ed788c0c4d1627b105ee2b171eab56cf41d5cd3516fb03d89e4d17b8af8b57989ed434f2ca0140c0d987ac5935ba855388c3cc4f692c1fd83eb4f83acd437b7b56cf6b34cd83ed43385c288a2151ab4ae0d9c60527ed5b58bc7f7501148c0ca494ffa93dabab42856514b4ae61dbdae30f06983fcf6362bc6056128ed5a1abb461d6123d558bc16562c9345d43e05bec0d9ab7181699b0f5a572d3d89e1bb62ccb4b0ddb107c290b626892b49ea4fe380b56e39120ed579abeb4394e1c6b48c7aad5d92332c1d9c721343816927e34ae5249c0560f2d362dfad0ac356e49f8f55cdf3da561ed5b49fbdae510b57d69ef694912832d3474ea1b7b4c93f59c9fdc15eb4d2e4cb356adad3d2823a7927e7f75a4a409a24fd5c599b4fe510a3b47aa2df62ccd23514a93d442a2995e6d5b5a6a8f5c8571666d5b81362df509cd5b83aa80aa2d3d8ab1c053bed5b59aa8ec37670193bed5b59ab57e83a86edc84d16c599a906a24f52829df949ea433fbce41524ac1e16fca0d57fa8d5883e16849ea85651ead067b4ca4f8fc2a4969fbda58848cca3b4a0a8ee (by decide +kernel)

private theorem part95 : Excludes 0x60000080100000000000000000000000000 0x9f95bd17838330000cc0080100200000000 :=
  splitAt 1 130 0x9f95bd17838330000cc0080100200000000 part97 part96 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part98 : Excludes 0x60000080000000000000000000000000000 0x9f951d15110330000040000000000000000 :=
  finishCode 41 0x1806a07e23f98c0cb4f521830d27e1e94514044149f181969e9ed2eeb90569b077a0da7c97b49ad5c827299a7ac376a2bda616fa4fde8721e40f4a88d22d445bb34cce3a0f18bba0f18e3aa159ea2a1349f9c754462127e91d9ab60f1395a01e49a8e5e5a69c04e56c42908e24bd69b3da5692d3f062a4f5445a4cd251e9ad4560f3564f66f69062b90a83484ff7b4cb4d5a886cce3a7e1a3027b37b5a8ed00f3d853e60c5599a4665a6a01d685a4ca3b49fb56e47cb07d6924ff (by decide +kernel)

private theorem part94 : Excludes 0x60000080000000000000000000000000000 0x9f951d15010330000040000000000000000 :=
  splitAt 1 104 0x9f951d15010330000040000000000000000 part98 part95 (by decide +kernel)

private theorem part92 : Excludes 0x60000080000000000000000000000000000 0x9f951d15000330000040000000000000000 :=
  splitAt 1 100 0x9f951d15000330000040000000000000000 part94 part93 (by decide +kernel)

private theorem part90 : Excludes 0x60000080000000000000000000000000000 0x9f151d15000330000040000000000000000 :=
  splitAt 1 131 0x9f151d15000330000040000000000000000 part92 part91 (by decide +kernel)

private theorem part86 : Excludes 0x60000080000000000000000000000000000 0x9f141d15000330000040000000000000000 :=
  splitAt 1 124 0x9f141d15000330000040000000000000000 part90 part87 (by decide +kernel)

private theorem part84 : Excludes 0x60000080000000000000000000000000000 0x9f141c15000330000040000000000000000 :=
  splitAt 1 116 0x9f141c15000330000040000000000000000 part86 part85 (by decide +kernel)

private theorem part82 : Excludes 0x60000080000000000000000000000000000 0x9f141c14000330000040000000000000000 :=
  splitAt 1 108 0x9f141c14000330000040000000000000000 part84 part83 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part102 : Excludes 0x40044080010000000000000000000000000 0xbd7b8c7958a9ba166064808881000200000 :=
  finishCode 59 0x78180480d4414a0e550609a88a6351e604bda5ec2c4d309828d1931bedcc6b3b839cf53595bda646b8f6c9067234a56933da56af30d60fea22a09e2cad6930b1d06eb3b858eb573702e723d55e28375a4b56d94309d1835a6b4a6732c60d676e4783facae5413c5109feca2d366aaad44afe6fb1e5acee83aad45cca7094f5a988e27acc26d539c82f716b0ac1e720bdc4b43399e0f2b4d6a9b564e01dace4909ab58589ab496a1b283ab9ea6c436b0bda4c263b59ee2d617b0d0753e59bec7b6ca34861396a23db5a4cb4d7b4b554726b3b147984cdc46033f13d5692b514f1503eb93d6595b554df71c2658eaa0ac13d66a3829c9eb351d1eb1f2daa6e47 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part104 : Excludes 0x40004080210000000000000000000000000 0xbdf68c1d4c293a143664928481084200000 :=
  finishCode 41 0xf0300fe340c4d8bc6d296a1a0a50729a298b2b8baea35309a886ed93d6f6b6adb564feab5147acb2b741ccf356541ad5b994471ac560c269e59ed6d4380aed597b4c28d3b9842f69587a8d561f1fd5ed32c3cfc724cd53628a4fd8433925aa6f22d0a221893f6a4c4ff5a4b50daa71f94e87b4b1362f1b584dff35651eaf6996a2e6f7b4c93f403ab093f37fcb335a8b9548da4638df6b0f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part105 : Excludes 0x40004080010000000000000000000000000 0xbd760c1968212a142064808081000200000 :=
  finishCode 155 0x682145a14c4c188386b0072978100561a72f698af2c571c4a0254921819cbee495abaa0f6b826ab4149fa35c9fe34f927ea4946b93d6609b4e4b3af6941da4fe0f730d4c268d727ab0ada72095901661349fa88ea240a824fc9c320eded27373920f7392d072b4d7b4a30e5d9072b0f3f2b49641dc1cd072be300a820de737ac54e6eb576511c41dcf6b6adc605cce58f41ba686139ab61af0dbce67725cd5b384b99d06e83b93d64ff7379cdc27f2ced1ae73758e9facfd720e4fab0d45cded6341bad349fe7373f14466127ee226883b725cd5b7319cad5024dc4ff8c0c2df6ada6883791c62df59da3d64f5bd8c5be9a39256c731c72b609cb4d9192d5b607a68e4186a280761aad349fe72b5f09ff35853f2c5740bad053f327ad69ac0f24db15dc45e20f73da4e5682541da68f6b9c928f55a8a02ce56b0f90165c14d11851167734e4e56b513ead07b395ac5669c9cad60e2df7b1c8f516fb00f02c09028882941cb04e621a06dab6f69a0f6c27694b04d7841bcd5b4f18c41bb49637db5656a280b9c96e206ee8c0a90daba3db8c0cd5d791983f100a83b27fd07b7b4ad5d41b3dde7249fed682d25521b16e5ab8195eee4ff40bb887216ce7b8a8d501681b651076d558faeb2b7b8a35cc26a35800ad553ebb68f5b9a4af695a8c1a4df67095a8d0696aebc871d27fd07b7b4b0758b683b6acb10e7b5b18e42f08c13fcd040da095a9341ee302d61250984e8c1cf6f628a32560e2df58aa06dd4601744f05bed5d95e280b5a48f2d0726139aba829405ad2527f3995aaab2b5a4ce55309ad366b1984d4c5a0c613412cd395aba05d06ebe1c2641dad5cc263b5a30307b405ad35784d104a6a1c0649fc1d4fd63cb621ad83cb9c82b41380bda6506b9047b70759c827eb1ceb565444d07971c05692a0d9c827eb16f9c24fc3805bf2d04e02a62c5647a92b54368e3800ab155a6ce65720b99d656b07 (by decide +kernel)

private theorem part103 : Excludes 0x40004080010000000000000000000000000 0xbd760c1948212a142064808081000200000 :=
  splitAt 1 105 0xbd760c1948212a142064808081000200000 part105 part104 (by decide +kernel)

private theorem part101 : Excludes 0x40004080010000000000000000000000000 0xbd720c1948212a142064808081000200000 :=
  splitAt 1 126 0xbd720c1948212a142064808081000200000 part103 part102 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part107 : Excludes 0x40014080000000000000000000000000000 0xbefebc15c903a910a040000000000000000 :=
  finishCode 103 0x3a0c4368a4200b024bd282be16960e4b994e5e7335e142b39750561c94c148729254531cdd84631bc380cf698c19cdc18af538ff6e65415a90e621ca491dab30ac279183927a0c53909cbd4449ec7fb41d9ccd8016fcc21521a8d4feb356e49e831581f1fdce6e5e349eb90ac240a0d944ea3d16f9c4ce42ca2303db5a6ca3b412ad3639ba0ee83a9c75bc8420f727cd45318148cbda4e6f0779ccae435a6831540f2cad1929190e4b56d016c02c0c220ddc97292540e73748cce439cbea077b4c737403a8a5a0691bc5f0e5670f524cc57834b56daba8176aacb4330b57941a6f340d87254c621ce61692ad5d4867fb9a4b2d0dab6b420a60e4b15e7209fa5ab6e4b62da0167b4a38d8aeb0750db009e340ea205d072b2d940ee49521a4fd69af6961ccd5950d9c8540f309d6858127ea079052b2d965b20a5a530776adb9ae403bda561ed5b69fa4fd6863184691945a6c1af6ada4fc7b6d55907672b04fcd5b054a4fd47b24fd846907b71c35036b4d9ab61996aecd67464ad35ed208b581ab6603407d9a0d2b514048e46834ad45ca720ec33683b80d6f69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part109 : Excludes 0x40804080000000000000000000000000000 0xbd73ac7169d128502040000000000000000 :=
  finishCode 95 0xf03a0d02a0da0fa53c8509fe71d87b6941395a466613a50418ad637893d405cd2d16fa02e696bda639b9f8701c3dd4379bd4e626ad5d89b01ec302d61989ab57415a0ae38ead09e220cc2d35b850dc2df60ea0ec57e0c50e49bde16fb56e49fbf880b907681716f92f506ee6796027fb1edb68b03301539ed2b496a99234e520c50e4a68fc0f6dacf27e5cc2a49735c907241a836694a4fe0ff398527a72916fc4bd7309ca5676da2d88e24bdab71fad02e93d392c3db6adb9ae839ac747b60c562d9fae62dac0a2208b3349fc6f749fc90278f6f960e1915a69bdd78506cd43412ac1e521a8d583b24bd60efe1f09e238d27af699ab26f783fca1b16fbda5a86b4d9856d630d79bdd27f3f0b4330d0308de356e38e82d507673740dc82b49fcf69969a93f599b56e49fb08d5b610ce5941d93fcff64ff89ff340c2378fc2d0a3587b6f6983da06d27e70d39493d64a08315a871754b8ef6927a9c947b6b41927e4f57b4c0c527aacce (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part111 : Excludes 0x400040a0000000000000000000000000000 0xbcfb0f5d59013a142255000000000000000 :=
  finishCode 27 0xf0420a80fe51c52793fd00f3925aaae49925ee6552147aa4f599cd5b6aeb56e60168404c4ff49f872520471d077404a0e57c399cd5b41bb99e834a7fdab6d5b91ca90752793fdb45f0d6f2c75ed25f927a9bece2ebc238e59993d4bf2b499282b51840bf32d44fcb13441725f9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part113 : Excludes 0x40004080800000000000000000000000000 0xbdf38c3d598128113040604040000000000 :=
  finishCode 51 0x3c0e8300b01025187b48fc527f2cecdf70f6dc8672b927ef695e168580f0302ad367b493fd27ea2951ea4fe403a88f639ed2a1551ea4fce1f2854e563ab98b6f6930293fd687e16773da4e56a1549fa7857f8b8eb3b6a4a8ed49ed538d7a7b359db965a86b49690b8f3da4e3ae6ba0f2e6f7b4ac0c02787fb9012b4d41cb30605694c93f40db4a62c5b0fd27e4f5947a60572cc81b27fbda560461c830293d67b4accded3020cfaeb4d611f80e2c72949fa06d501ed9f2e1d8b58d63a4f558ecd292e3bda527f13d5ed2c23da5ee338e527e81b49fc4f5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part115 : Excludes 0x40004080020000000000000000000000000 0xbcf32c31d94128102052010204001000000 :=
  finishCode 75 0x290b0260fe1845b45307f292f4a0acee732b045ea6d538e53397546ac591fcbc0a8351e392b925cbe3f172fce6538bb13e38bb16580841201fca93e6adaced84280941caa07fb9a4af6f60793fdab720edab741dc392837497c1ee59d968cb8ef6349fa475282fe3a0da240409497a504e1f24fdedf13fdc9272b780fc204a86e40ba90c93b397e0fe80541dab0f699a730776aca8d60fea49379c9c23083b6aec805541abaf718266e437b193fdab741dc5bee43394cd5b415b78d398e562df394b70e49927ee5f41dad5e379bf8e8420b41024ec6b1c93f51dbf093f8de672f8e5f13fdbc5f14371c4dccad5b397a01d74601ca739bd492a1b260c9f3721b56e0ef41ae5a1c1d5486da2d04ff7e144e83b9ccad5b49fbda66adb99683bbdc5ab6e479ab61c99ccae43 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part116 : Excludes 0x40004080000000000000000000000000000 0xbcf30c31cb0128102040000000000000000 :=
  finishCode 101 0x5f1a030f98ad80581c81f88fe5ed3354d27ee6b49fcc579ed2b57395a4fc812fc3783db8e3af20f6e5a89b6d3ff1685c86695497b50e83c830d3c7b1b4497c721410fc37b8ad683a9fad27e8e398127fb83fad4560f3495842c428893d699cb51720ce67692b58cdb71fddedf349525ed435e1484f0c3ab43a8b4d481b449fbc08c289dedf356d1aac1d7b0c4ff062c6b7a0fef616f119341fc9fea276ad9ca5ab73d85b4204bdbe83ab56d49ea35a0fef2370e820adab7031546ad5b9ee2d5b98b7075a30292f27fbc8ac356e60ea4bd1c6f53615a0ed0373d4dec2c4da0ea7e15a1445a6a40f224fd847b8cd4f415a0edd0471c9f937bb56d46ad5b823280527fc7379ace82b41db407d591c691938d93fd00b293d44791d0415bda651a93fe732b56e0eef69204c4ff6ad9c4e27fbd8f0420d031840972fce6516fb97e732a78b4368b4d506ca4f2becf6f3f0a925ec27e19486a353f59bdd25f1c87058ff6b4d51ac729969aa351fcc93d (by decide +kernel)

private theorem part114 : Excludes 0x40004080000000000000000000000000000 0xbcf30c31c90128102040000000000000000 :=
  splitAt 1 101 0xbcf30c31c90128102040000000000000000 part116 part115 (by decide +kernel)

private theorem part112 : Excludes 0x40004080000000000000000000000000000 0xbcf30c31490128102040000000000000000 :=
  splitAt 1 107 0xbcf30c31490128102040000000000000000 part114 part113 (by decide +kernel)

private theorem part110 : Excludes 0x40004080000000000000000000000000000 0xbcf30c11490128102040000000000000000 :=
  splitAt 1 113 0xbcf30c11490128102040000000000000000 part112 part111 (by decide +kernel)

private theorem part108 : Excludes 0x40004080000000000000000000000000000 0xbc730c11490128102040000000000000000 :=
  splitAt 1 131 0xbc730c11490128102040000000000000000 part110 part109 (by decide +kernel)

private theorem part106 : Excludes 0x40004080000000000000000000000000000 0xbc720c11490128102040000000000000000 :=
  splitAt 1 124 0xbc720c11490128102040000000000000000 part108 part107 (by decide +kernel)

private theorem part100 : Excludes 0x40004080000000000000000000000000000 0xbc720c11480128102040000000000000000 :=
  splitAt 1 100 0xbc720c11480128102040000000000000000 part106 part101 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part119 : Excludes 0x410000a0000000000000000000000000000 0xacfccf5c014532880055000000000000000 :=
  finishCode 69 0x1b4681e07c18c541a827fb60a0077527f34ec79283969ecb4d46dad0504ebe13ad5c6a4c8db2f0b105072d39816ad2f404cd4749fcd3b83b97d50124eb660df71c9506e1dd4ffcd5b735c1eda7a93f5f1c82b4d0eeac566b0bd6518734f5585a0e5e8806b64a08734e26b4d0e6c9075279c4cbeb27fce2710280b6300a29495a504183394dcaa7f983cc5a58c3b954ff3241dccf09b4b6ae656969c954272cddab61cd7c120f17e4df64f5560e4a90792565f56afc92b46db31101cbd28340e4a29998b2d2b96565f96afac566adb0dcbf29076adcd5f509ad3527f357e20681e0661200eead08090d7c8e304eb58cdef390dab65f991c6e6f7b3b13d69a93f901307791b64d147197d4bf24617e56c471b56e6279344afb313dab6d39a30ec2937b9344fcb06bcdee1dd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part121 : Excludes 0x51000080000000000000000000000000000 0xaef6ee31014528800040000000000000000 :=
  finishCode 149 0xdc3a0d6340be3902e96d1e0601a84f03ba4f5927ed571e4c93f5416027fa4fe0d48f2507724fd9849fc82b38ba4fe51db56d27f077527f302d8aa82b399a0d505724dd06a1dd61127ed5b8462d2b2e3a02dca6835591c1b9721a8781800eeb381cd6adce5d2fa8315a9b0ee58b60c59585a106a1c1905693f725c6f741591b418b2884f52e3c3c92faa0d4ff693f412d0770d4a3093f6d12451ec5c75a6a8ed0368059abeb4d69596f6626ad3640da88d2330ac356e415a0d5ab7206dab724fc98f39551aee5f5a696d55e672549fb30da278b41c4dabf2d353ff0555cba8d76afb508250d2ad3e611b954b96c4361a8046621c3d5621c1a16afbc0cc1ea68348f249fe81b0eea88b01fed27ed579cd64cb834cd572e3b9ac79317d49fe81b9076b41c89e268b4d4919c1edab0d45a0e6a136ada51d69f13d542707369ea44588735158c735cd5f51db56e6a2b56e83986f49ead455118c41ac93f2dace5541a86f5ab694783521a151124b0f5506a93f0dcc9471ea93d58c511ac4903767db90568ff9ab6b4f735c82b27a8f6da0265cb4f4a393fda83d9cd4d834b5158b6e4383bcd5b906ad2b40db40c63908813fd683b144480a494b8f239563ed5b834ce678c39624172e390d8b00982d5e0d8ad5e6a696245a609f9a9ad4d81729135d1205a0deee43816e1b149fb0ae72ec61dc969c2d0143a3065cb248b92dc86e490d8b10e729b92e8c1865c36330893f5abc19f6ad86bd62b0e9c14213d9ab6d4f69eabfd62aa22a8e418fd61af1edb30b1f8e4aaf36adc7eb49fbd7e69aa3b5ee66f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part123 : Excludes 0x41010080000000000000000000000000000 0xbefcef36c34321808040000000000000000 :=
  finishCode 29 0x3e8b60c0540470e272504bc69195f160497c72f497c721720cc557b0a8d525e9e2b07218e5e93f8f6f07b3fba02dabe5e31edc91d560fc7a8cc5b41db56c996a4361230f2855c86e65389a0950763d5920ec43483c3db6afa4870288a355249cce58aa51dab6d2341da856605bdcdc86e650629c8429f461c18a72141da90d2270734e5e733 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part125 : Excludes 0x41020080000000000000000000000000000 0xbef5de36295124810040000000000000000 :=
  finishCode 65 0x1d06a1985d1243f14872925a03803ba5e189a22c559aa8d507713ada46c228567b7b994e2682541d9ade791b068169b030d27e1dd4e0f835bc8254f106ad5f9672a2139782be732b90dab72bce2f0a09416f02f527f077502f355dede93f521a8892188d5f8ff680b6610c41db5563fbad3d47b2c8d02e2c56afc8396adc8ff695a0d5a05f1ac3069926e829162a4d504b34ed5e741a5eaa7135a7bc8be268c2251d984f100a83559cc6e95a6b9962f0ad3dabf1ade6611883dcb578c0a015ab63d541293ae05ba4fe6adad0d986f1077209567281b9ab6805247c8ed83bb4f53fe4cb5a6b55e5a6b4ad6ae4eb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part126 : Excludes 0x41000080000000000000000000000000000 0xbcf7ce30014120800040000000000000000 :=
  finishCode 119 0xd6328be3a060730fb70fe0bbda9b27b5a56a295a68c4d232b0355e3929fee40d9c965a6a4f53c6e18c83bc9ff27f86ed44eae2d366a6c1dd06ed5b9eb6b4d40cc837581cd735360eed5b620a44646a9fee147417817d8c4cc3b09d527e6f76ada01506ab4b9a8580e430ea88b4d6d0ff6e539cde4ff6adce53969f06927faa09c13d506b20ed1ff356d27f20ed845611ff356d8aa82b41d8f6e83dad350368d791dab4f491443fdc81b69dcb4f6adc0097aac1fdabe6c9476a3fd786a03bb20ed03661d5123032d3506a81b83bcf7327fad3569b202e146e0626f02f01dd389c7f5591a4fd06a9ed8d57069690a02dac2a3d41acc593999846397b50da0774fd32504e5e8278c229ffa0d22874a0b4ace0a72f851e46a0626b0368605541284d09ead23303db83bcaf78c086a60e69475a7a0a6732b90d8270737b0cb0d3fccaf3488b4ed87ab4d8fae4ff46aa44528ec238f6839bd847b69479612b4f41dd07347fa51d585f11ab13fd87af715a7a48d28ec223fe41dbd865a5cf6147fad3e40da3fd222bc278605737c6c927a93fd9871cad2e0eea92569e93f9a76a4946bb4e5ca6cc2d3e0eeb00e6f91ae4cb83ca4fdaaed2d9cded476a1b0721e40eeaf883b89fe94747fc83b50acc4372ab94cc0a81b927ed559076605403c4ff (by decide +kernel)

private theorem part124 : Excludes 0x41000080000000000000000000000000000 0xbcf5ce30014120800040000000000000000 :=
  splitAt 1 125 0xbcf5ce30014120800040000000000000000 part126 part125 (by decide +kernel)

private theorem part122 : Excludes 0x41000080000000000000000000000000000 0xbcf4ce30014120800040000000000000000 :=
  splitAt 1 124 0xbcf4ce30014120800040000000000000000 part124 part123 (by decide +kernel)

private theorem part120 : Excludes 0x41000080000000000000000000000000000 0xacf4ce30014120800040000000000000000 :=
  splitAt 1 136 0xacf4ce30014120800040000000000000000 part122 part121 (by decide +kernel)

private theorem part118 : Excludes 0x41000080000000000000000000000000000 0xacf4ce10014120800040000000000000000 :=
  splitAt 1 113 0xacf4ce10014120800040000000000000000 part120 part119 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part129 : Excludes 0x400c0080000000000000000000000000000 0xad73ed781f8170060040000000000000000 :=
  finishCode 55 0x2206e1886a1ac830c3b187c7e22fb5f1445d1a43929ccd673461c472f713e582dd69a0c5513cb2358ecd5d9a9272f5a683147b72cec18abc230ac1815b01dea881c527fcf6983aaccd647310cbaaa158f965d55838f2e6aa93d586ac5b601e05b03a2e43926ab1d05ab90e58ea44e3d6ac74162b6428f539826af758e8f6d69ed55928eb4d488cb076aeace637dcf6b514ac7587a3db17dacce17d8fc5692607969a61d6e13c4409fe7339226b4d6b0e4b3da4b96733609cc431edaf8c428566a187445d2ba2ce6621c1d542a73372cc91349bb07475b316d86a0c50e893fe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part131 : Excludes 0x40080081000000000000000000000000000 0xbf75ed382e0160848050810200000000000 :=
  finishCode 29 0x1063e8d6340be0bece132cadcbaa355a6984cc3e4ff9cbea215a6af061f57ccd5b524ad34c3aa4f969eb095a6b97d84560e5270d7b3c83b40dc9238c0ab096e1845e189f392528eb3505aa0ed04a7429262eeb0f5646b3951dce65584ca2194927335a693458468169b06ece5273741ac7015a4ac7e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part133 : Excludes 0x40081080000000000000000000000000000 0xbf77ef350c8970250840000000000000000 :=
  finishCode 35 0x9036893f4a10c40dd18741d93d4df67095617817dc7f527aa0d5945a6c6ff6968bed5ff3da56926ff405c7296b1a06220c6405f67339a5eb3337f9845a731ca5ac6d234be395b04e5a6b5748eeb2337f8f6e58ead256672b06ff9076911963ab3337f9fd659dad454c6805f720ed0166ff38da49075949280b392cd2b5a7ad355e683541ac83b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part135 : Excludes 0x400800c0000000000000000000000000000 0xafd57f390e0168050078000000000000000 :=
  finishCode 61 0x18c481f449fb58dc2682e917dbdae0a6b16d1fed534029c3d4772015345b0e1f34e4e56d53928ec0998aeb573e4b00ac0fc4feb3da5246f69a0ee8d7723cf69302a3fdac1f8b54e402a09562eb574fccc57681f4531647026c366b4f30f9bfce36c4370d627ae5a6830d06a2e917dad8605904ab4f41dc923640e57356d69f0699c831818c1b98d077356d246dc358bc030d06b20ec77741a47e25c71f8c83b629b56e5a786edb86adc5c76afa0d5ab7171e207d17c7b4cd21834bddd6aec29303b55e3809cdd604efd069733a92569ad451f8ad3662ab08d012d67b48f44e6e6ff691a5f3135aae8356a2a3b66a1b97d69ad45962e947579b1356aef69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part137 : Excludes 0x40080084000000000000000000000000000 0xadd57d71ac03624c0142108000000000000 :=
  finishCode 105 0x7b194391f45a6c409a320607480fc334a4dd2d592e098ace429478e6662b681786acd181492a4dd27f24060ff00cc5be1535959fad90560b8f397d66a0b33909cbc3771c94c3ea83a8901f907f8b82d595aba4fc9ff3564e125c183ad1832c5b56c6cf07f8c0b4ace12d59350c7eb2e0b09ce6ed456aec93f16f86eda016fab04ff39bc6f7492ac7e724ac7e3f5b56d27e4d187760b349f9ccd206417c04fc93f721b9245be61f390c4070f8fc271350685f637bb97d7c60150510b829a13463032cad27e90124a984d493460455293f384c28e65962ac57506b564e6e7c99ab29474d07b724fcc2657d9aba93f38493fe1eda404c26e638006e658c09c6c8daa0d6f1505f2045305be1ab8e6e925309b56e7b193fda7f2494c56a0d8e02b2394424d16ad8b7d3483fcf6f275b56c366d598e66d5b7a893ad506018c511bc389c4ff15a8b7d78390c4ff2e0c72172fac8e39b93fc5beb2b9ccad631f89cae27fb97d204d15869cb58d6974605a5294716fcc4f394b996389c604e52d5ba30271b6a19065127f354d66ad5b3809874c5672b9ab66115f14c6b1cf614a3984cde70a4c92a4d16ada4956c4c0e02f539cbe8ed62db56dcc6d5fa302c5b47fcc356a9b58d9436dc7eb27f981c7b71818e56d5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part138 : Excludes 0x40080080000000000000000000000000000 0xad557d750c0160040040000000000000000 :=
  finishCode 71 0x681a40f2a48bc42881b41da60d5b8e522fb3868bee27fc622c080b591c70d5a69bec7e30a31073798aa25b969a7e17238becc0f2855ac8c0cf695a69bec7e272550187b3da547ab3934ec72949fc8ff38b9ca506ac42c02e9733c4811f89704e12a817064f6bddded2d613f0ac8d8727f58902c5537f8bee303bd85c2b072240b4d6d18c389ad462e0a7ad01670949fad5e017a02dcce3d5989a835599a4fd34405a0d432f3d8d6662df9a52bc348b518dae3d537b9704e2680541ab2107598725c16a1a4fcdee7f5390a4fe3faba87e30093f36bce677b7b97d6662df599c709966658795f25935a8b02541ab4d9206d127efa1c254530f6c5beb33399c8359666fa1c2641da8ed692a139cbe80b41ab091020d5abf206cc566076adc81b1e2c62b (by decide +kernel)

private theorem part136 : Excludes 0x40080080000000000000000000000000000 0xad557d710c0160040040000000000000000 :=
  splitAt 1 110 0xad557d710c0160040040000000000000000 part138 part137 (by decide +kernel)

private theorem part134 : Excludes 0x40080080000000000000000000000000000 0xad557d310c0160040040000000000000000 :=
  splitAt 1 114 0xad557d310c0160040040000000000000000 part136 part135 (by decide +kernel)

private theorem part132 : Excludes 0x40080080000000000000000000000000000 0xad556d310c0160040040000000000000000 :=
  splitAt 1 120 0xad556d310c0160040040000000000000000 part134 part133 (by decide +kernel)

private theorem part130 : Excludes 0x40080080000000000000000000000000000 0xad556d300c0160040040000000000000000 :=
  splitAt 1 108 0xad556d300c0160040040000000000000000 part132 part131 (by decide +kernel)

private theorem part128 : Excludes 0x40080080000000000000000000000000000 0xad516d300c0160040040000000000000000 :=
  splitAt 1 126 0xad516d300c0160040040000000000000000 part130 part129 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part141 : Excludes 0x50000280000000000000000000000000000 0xaff95d750057a8001540000000000000000 :=
  finishCode 47 0x7e1a8681500f2be8d5b984ee6f2f49c3c9fed57814e3d16adc5f5477b4f41def63300ef511057356d06ab399a4a7e1611acd47aa713412b57e661341eab58e6af96fdab6c5b6a2cd5b9587d1a0077acd683ba44d476d5b1e897d4e6ed2f9ee67010cea0ecf8384c29b2cb82bdab68252fab08662bc1dce660af1e8b5162e5b57c9fe0ef641a85003a2a834f651d8f44c84f142aa60e9e4a3865c996d57735c9472facd294a3cd53174b0fe4a3b54c5d2b4d9426937275a78a8356e266b54dac64ff49bc1bb6a98ef66a997a5ac6937 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part143 : Excludes 0x40800280000000000000000000000000000 0xbd39fd7009d324401540000000000000000 :=
  finishCode 67 0x681b86c1a87e1ab72d4507281752487643d2a83303e95f03a2f638e4a0c57b9a09c9972d2456ab3b7af932e4f1cd7132c3768395a6932e0e8920cbeaa82804e18e429412fa8fa5608219862acb5183ca77c9fe4c13999c764ef932c2e330e566671d413b1563799c75a672bcd3be71b413acecbeac2428a8277e39ba0d49fe5f538eaf0a020d560400b2f28551ce7e94149fee5a6a0e4bea59737bca1b2faacee50dad26735a854fd680b2faaf072f85a28355a8c7336b1c9df59dac7ce1ebe1bdd5c5019441c92f65a6ac3639bbd8dac692b387c8275a6c81969ca506506a788236891d8fd6b4d389ad09c2d34def0f555f3069d6a2a356ad92f637ba9256a31c85ab63d55a6af0cc20ae057b56d04aa219ab7187827ec536a4bdccff691d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part144 : Excludes 0x40000280000000000000000000000000000 0xbdb85d70001320001540000000000000000 :=
  finishCode 113 0xf8340d83202b59ab691d39b8c4c7e2409851f46e06261e989fe3074d09fe5e39c8e6f339bcd3d2c9bdad69abe268fc24dd4872924beb398d44307a43d317d57c6f13c6b1072827969a61327fc9253e5c00b8c3b16d83a0a3414984c3d24ff80d2709177b54e0f4ad36147d2086206269e205e41cad34e1e4ff5b060ea078e6e5e938e98162c9c819695a05dabe6075a693fdb85b05ea5e98bea71d79148720edecf260a0d9612b4d5249344e1f209d69ace2f8702d35072a3b8e5ea497309b5d032d399c8ab23521a0956471b351871818c3a014e0aa4350697d4beb358dc2682ef392c1bb27fad44e4b20e4c2720e50372095ec189b30c828880b8fc282b3899ccc8d7307dee29ed8c0b57d63eb396a14872095442a2358e37d829569ad5b412cd5f900b356daae19d7d1a05805ea3016617861cc70f3fca0d439ac558e3a9411dcc8276aba02e41a8ad5a7af6320da330a4f969a71348e9c84ff7356ce0ab4d02ccd5b5a6a86d04b2835486cc2f083b91f2c5b1eab205e3945280b48ead264f5b1542df357cff6d5b64144681885a1b053039aa2f9a46b4d524b55ce0b356d4529379ab68392fac6067359fe4d9a83938297d5ab6e6b90769476adb56e399a44e4f2a8a4e5e825969aa21 (by decide +kernel)

private theorem part142 : Excludes 0x40000280000000000000000000000000000 0xbd385d70001320001540000000000000000 :=
  splitAt 1 131 0xbd385d70001320001540000000000000000 part144 part143 (by decide +kernel)

private theorem part140 : Excludes 0x40000280000000000000000000000000000 0xad385d70001320001540000000000000000 :=
  splitAt 1 136 0xad385d70001320001540000000000000000 part142 part141 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part148 : Excludes 0x50040080800000000000000000000000000 0xaffbcf5f118538172842404040000000000 :=
  finishCode 47 0x13c5415427a93fc5632c7d69e3b17b48f6d3bb244ded2c1d66114710904316461d19cd6f6937dbdde0e2a8f5aaeba171e7b48f6d69728f5c8f17d5c861d151ebda65a19455169a1ab94523db2e3ce6b7bba44e730bddd2224cb9aaecc300c41a81c50e8a32e2f4c1acfc23db254b04c7631234bd2f6b8c3ad0a8228c1d91de9dd1ed8f445769dd893b171d42a6fb7b4a44e7b5c1ac762c4362db9ad0c60ec8ff7b5ad3dc93390c2fa9dd711e44311df2854bea4831e8b4a5887244c2fac5b50ab1361e8b8f62418f45a86a15 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part149 : Excludes 0x40040080800000000000000000000000000 0xbd79ce5c108130132042404040000000000 :=
  finishCode 129 0x1d0781b0641806607d24096a0f00e897d63d6ad34ddaa152fac3db41bcd438b8e7f950a8f6de48513c71178189bda651e8f6c9feca2c361edac3651db155b45e169b39ad47a4ff4a0ba33d9c356c3d571aab3d9daba1a3727ca276ac9b5547abc2205f97b5c5f56accd5986272f860527fbdc66928f2da865c78c0b13fde47d214560626a217d59461ec3db62ac7ad9ac3077414b154d7a4ff3004ef3da5ec27b3839b54d6766d56514469fcf696aab54c9fe18b5a68f6cf5b41b5a4a6bd86dad536b1a788ff967683927fab0be350e414828d28ee658b8e4c12e8b0d64eea3fded2ae17d4b533d8dccac53163a0dd8ab391e6b1a0e4bd24ff4f1903c11879142aa4f37dc3db59dad249ff3e8e2308e3e5b98d69a09958e8f6c626c559c8e4ff58ea20be17d5ccb205d202e439cd7358563b0f6c9fef23e84ff87b683798a64a98ba24ff791c4831cbf1eb564a9375a49814626ac0f6d42b2d25ed23bd1e5ce43a0eed4958ead450332854c0b063c86fb96a25f5189a505f98c0a4f5302c942786fb87b6b4d27abd863d6b585aa648d36abda4bea4cb961a1c558eb68a82a84f527face61edb10e57bace56846033f3dc4b8eb4b599981547aaa308e62a8f6d7c7b4c8ef58eb50d69b244e265a30f7182aac4d5a8981458839cf71578a3fd672b1d5a106e7ad969a4639012c13 (by decide +kernel)

private theorem part147 : Excludes 0x40040080800000000000000000000000000 0xad79ce5c108130132042404040000000000 :=
  splitAt 1 136 0xad79ce5c108130132042404040000000000 part149 part148 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part151 : Excludes 0x42000080800000000000000000000000000 0xbd5fde1c14a521212140404040000000000 :=
  finishCode 19 0x721b06a1b40f4b484ff415c83b58ecd434a3a3fe41da51d8027faf8409491cc0f7b4a51d69b2f8b4d0d5d07b49b92e67109ff181816a0e941d82d650a83a58b73575eee8ef49b902527e0e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part153 : Excludes 0x40020080800000000000000000000000000 0xbf1ddf1e309124052041404040000000000 :=
  finishCode 99 0x418d82a01e9204a40c3d98aa4eb7b4b15cbeb0b7c9d707b9076882d072280b4d8211471144ea4f2fac9475a58e8e732a774fb320e5c8e9132faa8a520571abf0265ed25f541cb88f2393e735a02d63f29250330755a582d6727b155032e6535ecb4b41b97d518521ce636a2b57cfd720ed486e4762128501ac328a478a5f5401507109c28279cc2a43721c9dd1e2b9851841dcd232f09eb6724a44d46b0f15486b01c0ae3d9d3bb251cb06d238c0a09d06e8002d65149b5c9a2e65268c0b55f15c691c82741ba011878562e65730c0052c1a51d81704290e1a6bd85a8ee2348e521c606247b55641d93455c691c4d149ba77630282741ba00bc461e2f0b9949c29dd9ccaf6f8d3a9dd8c3a38ce2f8a0205e0e712a5aab1817b4a0e5ac306adc4143cf53521a8d5ac33dad18707b72f8a1ce0699c4c72f4b0f6610bead459c865e161ea4de1ba9785abea8410bc3555ac23679076e4941382d58ab391e0f2593835b90d04ebe39ae83a82d5ecea49268a0ddc47b3a0ee521bdbe83ba90e2f0b48d3fe837268b20a80765ac330f60d23e9166a77e40b9a75ed26fb16fc1e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part155 : Excludes 0x40800080800000000000000000000000000 0xbf1fee5c10c160c12040404040000000000 :=
  finishCode 17 0x6111474127e6ff38d8fa661287a49ff2d3d84ab4d780e52c00b7e41da4fc7d283b8df6a2949f87a4beb3a0d8410b4f82a28d752497d569a4f549f87a563b1aa4fae8d723897d569a93f0ecac7e2faad3566b24fce1eb4f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part157 : Excludes 0x40200080800000000000000000000000000 0xbf9fde1d128526112050404040000000000 :=
  finishCode 21 0x3a0c01cde629b154bea8371899025c40c2c4b946b9c743d23135a03d307b927e70d5a6a36e59dbd9e0f7043c8c8248d28e5c9969ec259c9283769f85f560729c1855a7a06569f2b87020dc162829607d181586c1ddaba3bb9a4a71d40cc737 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part158 : Excludes 0x40000080800000000000000000000000000 0xafbfce1c108120012040404040000000000 :=
  finishCode 153 0x410f23480ef079a06e41d93d64a3a44527ebc278b413d49fe8a2a86ff737c1d65a5ac8c34693fa0ea8cb62dac8decf310cc0ab4d49fb48e8359c75ed2c4362db51102c05f98c0ad82d01e9696c73769d9bfd27e9a232e609b9ad8b71819caa8e79696e3938ebc0b4079542b24fd84f316d285a0f81eaa4fdc7b235da9ef673868aee83aa68c13a0ea7e138eb9ad8b61899cd61352f4ac8cfc28d783ac93f7359f5519671d7b4b10e55881271d78127e70d9ede70d9a766b76c0e3b10243d2c42d071d5a6cd617b7a855ac33da549334ae30ed5f5a6b51dc7a83940cb61103a0d21025683f18449fa986f19056b4d39b97d64159c84e1969a4e191af0770dc9345887acc4c34739f8563e7370e2a0070239ded70a3deee8d72708ec5abf1c347b6b4d8b2670d611e471103720ad183f2cf69268c60630e4e15a89c75581d8d18783b9384bea9e41a51cf3da60f6f5b35bd1817b4b57563b07b4d15438ec61e8c086acfaf12a5cab41dd63ef6b0c48ec5402708ec68c3ac7ded3069524cb096919c3c36b127cfc24d149fad01bd927e737691e440dc82b270c71d5a7c481481985a15849fbc01bd5005be83b81325c12638f442773d9d1ae83b2e0931c14720ecfc31cdc5bed22b0e820ed882d8ce6f2f49c743b286393e73592a673286ada8a4e1a30f1edce3ad456afa06d69f076581330e5cd67fb38e8f4527ec2330e2206e41d9c36607c70d0bf9385a468d79ede1c55a6b9249c22df7118479198381076a3590324d158fad3d14521c7371edace5487202dcb2ce3dae268ac75486e6b8ff67375b14071ece596a2a92563eb4b835ce43695a924e3af6795e73d9d6128c250b517b3c70f1e2b9ac2f2e6b90328a2c7568395cd49386c1ee8c3c1de0f7461da92829 (by decide +kernel)

private theorem part156 : Excludes 0x40000080800000000000000000000000000 0xaf9fce1c108120012040404040000000000 :=
  splitAt 1 129 0xaf9fce1c108120012040404040000000000 part158 part157 (by decide +kernel)

private theorem part154 : Excludes 0x40000080800000000000000000000000000 0xaf1fce1c108120012040404040000000000 :=
  splitAt 1 131 0xaf1fce1c108120012040404040000000000 part156 part155 (by decide +kernel)

private theorem part152 : Excludes 0x40000080800000000000000000000000000 0xaf1dce1c108120012040404040000000000 :=
  splitAt 1 125 0xaf1dce1c108120012040404040000000000 part154 part153 (by decide +kernel)

private theorem part150 : Excludes 0x40000080800000000000000000000000000 0xad1dce1c108120012040404040000000000 :=
  splitAt 1 133 0xad1dce1c108120012040404040000000000 part152 part151 (by decide +kernel)

private theorem part146 : Excludes 0x40000080800000000000000000000000000 0xad19ce1c108120012040404040000000000 :=
  splitAt 1 126 0xad19ce1c108120012040404040000000000 part150 part147 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part161 : Excludes 0x40800080002000000000000000000000000 0xbf19ee50c1c520580048121400040001000 :=
  finishCode 75 0x168651106e169ad03a0f017d57c40bcd53270a93c58ad8356e0f48fa43a2802c7d1af13fd282705944e6a9626cf6125ead2d27e1c58107ab13ad02f34fc7aa2b36a1a71042883d537bcc4d615a38d6a2d5b60ec6a90d0ac1ce02d5b95e6d2f5a8a015492a0d6adcc2b6aea4fe086d1f460ec93f38093fd27f354e6b3b074af293f379868625ea40d024fce1f238d8b69f16a993fc3d2c278e267f7681e02c7ce634a087643d2907818b07787aa6f33fbaccdf8480de713fc3d293f27ac1e91f4c4f548208781d0560e862dcd5b38787a4dee705601606a6c4ff7b4a925012839524cf69389a05d00f1c4d8023cd0796099fa5ed23e90f4cf696c17c7b4c4d727fb15d072d5d6adc491275a02659a9c4e7b493d5f4404c941270c5f5524bc094183d2d5b4009af1f5d28306983b8316 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part163 : Excludes 0x50000080002000000000000000000000000 0xafb85e11d10568080040529000040001000 :=
  finishCode 97 0x1f85118c481d049fb70c04101cd462cd3d5148b7c3ca880b7c98f41a5ab6e43818b293dec6d5b3898796087d01df13fd26f0f4498f0b7d47b410dc3e0f63300ef275cd5b5a687945be4c7969ac0f57f93adab693796025f5509b4cdab64eb0f2a80da1e0b179ec65a3462b56cbeab4d51ea93df43105d31bcd476ac2cb60dc9c3e6aeacb60d22e96ad971e58ba8ec18ae435767259bcdec61cd402cd5b387bd8e16f8315426b4d9c92b094a393ac1decc390dc0b7cf40ecacde6adb90dc92d5b898f1c3e2e3ac8c5bab4f6adcd23440a84f8c1cd6adba0b4d50039ad679aae1ad58f8f45cc703be731b5160d30ba41dedc390cc300f8073589b0f55612b4f5a6c2df0bcca133979c3c5d21e57c09d713fd4532200ef123cb0b83d8ee565a4cb357ce49721b974e1e4ff81dea83304ff481306e07a2960745ed7356dcc2c57730cd239c92f69240b56c9c2b09163cb4d270bda458f1385ccb355d8a2d5b270b301d19ab6f697119469ecf6b6ad8b7569b04356e488b57e265bd9e366b9acb8ed5f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part165 : Excludes 0x40020080002000000000000000000000000 0xbf9c5e1ae11524090340121010040001000 :=
  finishCode 105 0x7c1a0741b01f8cd5b49f87a481280388cc170b095a1b85a69f565279cce49bb9153caf636adc72f402a795ed2c5989d68ef39797859c5d1205249346275a025ccb3d465a69385ab713857c3fcb56e62cbdae2759785c869f16ad93ae6ada925612a03305a3d4e062a7fd02ed5b59aad2d205f1606a1cf6916f9fe5072ce357e5abad3d02ef694a3a89e6ae9ba647fad3dab64eb7b4c1a6694a51c9d6d5b5a7a40be1fe5ab720e42a324fd44ee477b0a8f569a83789d6d5b671e45f09d7209d28e7a13ad3ff356cdd26b76afbd843264ad91fed5f89d6f699196b096ad93adabe723d8d576afacd65959cbd69ad438fcadc410a02d3e268b48d47aa4f5111c2f0cb0949fb56c9a2b09927ed5b584c7e17b1b887e2c2683fb48c9a2b4b6ada92566b28d5a46d239a724d16ada7c6584ad2dab64d1530e42c1a06abb57d202fac7213fcad36268a9255ff293ce5eb4d740fc6adc9e5596a9249a31c84e5ed3d041cd3d596a51dd0721985a0e5ed8348e472b9ac59b1819ab6585524b48c9a24d19ab71c15492a49947b251e046615c8205beb4d9426a4f2fac4d17b7c7e50e6b97c95ea3b607cb1541ba84d47ac0f927e0c5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part167 : Excludes 0x40400080002000000000000000000000000 0xbf9acf18c115202c0050121200040001000 :=
  finishCode 95 0xf03e0d03704097112017aa388194f8caf1366b8f56a2e6b627b9ae579b56e413ac25e450110404b92641b97d5cbed5b471c099722a4649a2837413c4d1724ac756a2f6798b2f69724b995012d5b9cca37f3fc9385612c6338881f89017093f6e169af6f96024d15a8b58e579cb01735ad454372d35492b096adad465a6c1fdeded397328b7d612d5b5b1c43f17c580cd5f584a4fcfee93fa0ee4c7524a8356a341a5696b51927f41dd6a2e3d9ed2b3749fb56d5e72c7d69ac4340e21f82f55b127ee439c92f5369f92bd28270f404ce4361cb15c5bf3085685a8c1cd6afc7f959da68ce24be380ad45edf090cb0af6959ba4fdab6d5f859ab4d6c1686adce6b16fa4fd9c83bce6b40bb56e62bb5156a3340e22982f5411142ebbe0d4595f307746bad3586ef595a7c1de72c971c5768059ed30697adbf0b4d263c7d551aa3e657cb9ae591b68c4230919691c1c56afac067b3a35d682f82c767b5c1fd1f2e3d270b0dd89ee6b96a2b3b838ab51561882689f0b51878a7e548cb38b1f949236f93cab1f380b5165a6ac3d6a3175d89eb4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part168 : Excludes 0x40000080002000000000000000000000000 0xbfda4e10c10520080040121000040001000 :=
  finishCode 89 0x388f83a04098c3a3013158c4d947b0c56fc13d6079800e46bb57c18ab4d27a98747ab3d4d27ef6130ebf08058c0af71079b56e5a5bda58529477b893d4c22e83d83016718c4d16056166690286e37b9c154371c05ece9d9583b10c997178d60eb4d2e0e85a69c061eab16d41a70549fc7e293e7b4a86d65a7016afc72148169aa01947693f389c1a649ea8d4e431cbda8aa075a6a3164f8b0ace02d45389b10da1c064a09c066abcd5b47cb10d27ec43487e2b06f33809fd6492ad0e6aead45ab6c61d9022f8a4f062cd5b492b4f662db925ed29ff680bc741b5ab6947626cd5b626cd5b062a8f51df3da47aad3d6a2a90c5b87aab4d8dd29255a147b24fd8af356df07b1a0791e0079b6891d8e0a5c7733ac74812b512fcb56c9fe09f9ab640959d97e451317d56665f97818b31024ff24ff27ac0f39a4728a520ed5b0f497e5b47b17c495cd455a89c94e66b3b86929f13f2b514e029073eccd23514a4ad88560e02d5d8fcb07b82bab337b7cb5183bac5d0727f7 (by decide +kernel)

private theorem part166 : Excludes 0x40000080002000000000000000000000000 0xbf9a4e10c10520080040121000040001000 :=
  splitAt 1 130 0xbf9a4e10c10520080040121000040001000 part168 part167 (by decide +kernel)

private theorem part164 : Excludes 0x40000080002000000000000000000000000 0xbf984e10c10520080040121000040001000 :=
  splitAt 1 125 0xbf984e10c10520080040121000040001000 part166 part165 (by decide +kernel)

private theorem part162 : Excludes 0x40000080002000000000000000000000000 0xaf984e10c10520080040121000040001000 :=
  splitAt 1 136 0xaf984e10c10520080040121000040001000 part164 part163 (by decide +kernel)

private theorem part160 : Excludes 0x40000080002000000000000000000000000 0xaf184e10c10520080040121000040001000 :=
  splitAt 1 131 0xaf184e10c10520080040121000040001000 part162 part161 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part170 : Excludes 0x40040080040000000000000000000000000 0xaf38de58b0a130068048028010008000000 :=
  finishCode 135 0x110418f83a0c8360f21025b4189aa0763dbc9fe807960ea27731d073583bd9dc86b3393cf1874a0b095cc6a272e3850e374bd9dab2e6330ec4ff7d1b871169320dc6de2f5183bc8580dfe471b58d232b1d5a4af8e43944eb01722a0658b2f739ab6d6362cc49d6b1af861d72fcaf56abb16504e4b3969a72220ae2d3540470beae618b8ed574f3b164b8f398d6aee654f3b55cb8f398dabe8272face47722ad5dc8b398d04ebe250a02d5dee73164bd2c599ee6aff732ce47413a80a299ebe5f57b1c6cd7b996c5c8af22f83135a0c8276a3ce6383993ad84ab4d629ad0627593fd50413c4eb27faf8d5b41cc5c74a3a3fe404ba0ca0c0566720dc5ea82999c57100f20dda5b0f6d222d5d9ab6a84109e2504ff5005a324f4beabe2390798fee827265c5c75a0932e612a79d69b1c1523a9e749ea50a02d5dee701f50125f5626cf736a3b98e58ab51d27aba2c763e5b0fd65a4cb1f48f6d63b06de4f3a4bc7b69e2a0f8301042504ff5a6cc51613abfcbd2d5b5a093ad00613cd5b732b03e5a6a28ba1384377356cb8eb579ab6c0f1d3b55d84f0294376c516ad93fe65104174a7ae61fb56ce0ad5b87b6c5161fa28c0f94771879452e5f6ad97d4dc531ab68e06ddcd7354d846c556ab8e9dc7b28a61edad3528e91185d2e2310aa0ba5a73356d87ed5349bb9163f0c60dcca3b9694932d50600953314587e5a171e50abdbc32b2854376d5b1edc5bd580b92528ed5b4a0c86adad5decf2c05cc2a1562a92ce580b98dee64b39cd6f73 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part172 : Excludes 0x40000081040000000000000000000000000 0xbf3cde58a2b120048048830218208000000 :=
  finishCode 135 0x3e104418fa2780f316ec9eb39bb5849fed55860ea62301c320d2369eaf84d1987ab57620a9266a4a7adcc2a29732ca436817c4a1786a09d6aa2c5e2faad5d3cb34d54925e15a6c9132c7b57dee7051dc8a9eb5148b15aab28a583ec416abb59e62a9b5dccad616adc7054ffa8a5486d5f5411c5f19c581c4413b996521b1066b0ad5e480abfe7afb585882b43690c9eb6b097d638293ad9c5f104f2404463397dc8ea493f597d66adaa0be250d42f0b5741bcd5b3f5c18957fc1e5aab201d26e837382ce616b1a06506ed61904451902e3ad0e5f828e70552791ae382c1ce72f80cd02ed49a0d2817382b99641cac0526ed02a0b43d46836a7658aa5f527f9cace6e9a28871d497cf551edac07c1fe5ac3309507327ac9fe9419816d615609fec259ab65f5414d07b6d1345007b61478e521b7497bd5639486dd90400b2f41b4dee7f94979755282e6b9ab6a1b168ad34e52a1b8bea5c762dcb0115997d5676d39940e3db6ad9c05f46e188681c45005ea9419ea67fb3948b44bea72987b6b41ca60559cdd7c620cd5b5a8b155052d5b95f2d23612ac09e2d248e73035882d236ada90dabee6f981ab016ada90d4372d0cf66e6b611bd4c3768e393e7359fddc9f39adab6d2358ea6037f8e524d16adc5d70b79fad69a38f671745f14862b196aec0d9ac6c55268c5f59ab6be3e8d029265a6a05cbae2dd180ac0a62d25ebf2bfcbc693d9686b072f1c7fb5a1b38d558ff6d61489a90c9a32d5dc872d252822f5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part174 : Excludes 0x40000080040040000000000000000000000 0xaf1cde51a0b328040068020078008018008 :=
  finishCode 149 0x3789619902303e08881d07d1c40799c8d678b8e6f73ed9fedb4382c1e91edac066adb10db464166707a523a92f83dc1e946bbd5436eb3383d2c8290e6af902502f3926834b48cff68ff4a3b56c1e69378376d5b077c4106290e691ac05abed5b204a9263fd9fee58086edab66e340882f8d5b69fc1b741c87a6587b14c81290798469e70f4c1cc812a438feed5b2d7d06d4f3a38cff21e9189c18f83c8e83e91003bd34204abe66afb56cbae3d35a8abe6834b10d5b61cce4f0dd932c7b741dcff6d028840983bc7fb265b56c7a3356e721a90dabe4eb9ab64cb077ba0fa10258b70f449fe3d189d7248a24407fb74060329260d32025aba193265c1de265af8c39441a7eac1a6e721a3152029e78fef29251db241d2824cb721a025884d1a470ba4e3a5f59c86e4941bb57c5d2af99ab70777119c541444d0ff6a4998463db380932e611b40c39609c8090f49c0673787a65249fece3b07a523b3d7d2821e98220c7d13c077902660493fc8130ba620256c6e941c902544604c1bb6aba51dab64eb9404011c681b8414ac0669f9feda5a8172fa9bde40ba41e69fb56d88706913dc6e9583a0a4fd7310c7b61e991aaaf91ed9c0510831ab6ca10247b72d0d8121bb0a0c357580b035cd6c0940bcb013fdac3e7bb86dd02f063c8fa2480ef5f0ff6d03a0b579a7e6f316b8c047b71bcd3cb2d25aab2795d0732c58b69f9bcc5d230147fcd5b5e17c6ada3be382a51dac313acfd6d007a63fdb5848126b7a20121c58b27590249d72687eb4f2cb431ed9bcc30b356c3d24ff (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part175 : Excludes 0x40000080040000000000000000000000000 0xaf1c5e11a0a160000048020010008000000 :=
  finishCode 109 0x288bc24fd10711ab6fa3e0c3d9ebed234a3a84c5d24ff0778c4d28f17d4602ce2e8f62f89a02ae48986cd28ed59969a923506cb4d275c4eb813b1eb581e4eb395c5f539bc18f8410fa340313495c5a38c1b98c3d270d268d0772d1b495666d02f8d5f87764d1413926e35e87a5ed68ff4f58fe490f1fde0fed236afb40729902e3f9204a781af9a46e5394860ab7d1a039bc301611ca4383ba505666b15a0dac0f521b40de0fa65a8a41d2821e938d9fee696a504de61e9599cfa340de4185f53949cdc7f334a45de40924ec3db180cd23862692f599b4039f984ad235219025a4741fdabefa3c9063a00ef6814531cace6e2e9180a788228a4e032765886b07940ec393fbac56621a76542a6d79abab4d395b40b613fe3959cde0f341cd3e67f927f87a51c71eb4996c43380c40737609c8e327fa41c60ec0996ae5cb174a30a02b8a2948169b309d8a2882f8b4d41bcc0f57fad5e0ff355e0aea7ae0db07740bb03d6af07a4e4724ca495abb4f5ebed5f881a0741a471025a4717849966d794925bd9c86f8440e8350409595c9f96b097d5486c550f4b03e413c4eb7aac5e95a193ad5462ac7b761fa05d246913941ab4d (by decide +kernel)

private theorem part173 : Excludes 0x40000080040000000000000000000000000 0xaf1c5e11a0a120000048020010008000000 :=
  splitAt 1 90 0xaf1c5e11a0a120000048020010008000000 part175 part174 (by decide +kernel)

private theorem part171 : Excludes 0x40000080040000000000000000000000000 0xaf1c5e10a0a120000048020010008000000 :=
  splitAt 1 108 0xaf1c5e10a0a120000048020010008000000 part173 part172 (by decide +kernel)

private theorem part169 : Excludes 0x40000080000000000000000000000000000 0xad184e10802120000040000000000000000 :=
  splitAt 4753 126 0xaf185e10a0a120000048020010008000000 part171 part170 (by decide +kernel)

private theorem part159 : Excludes 0x40000080000000000000000000000000000 0xad184e10800120000040000000000000000 :=
  splitAt 1 97 0xad184e10800120000040000000000000000 part169 part160 (by decide +kernel)

private theorem part145 : Excludes 0x40000080000000000000000000000000000 0xad184e10000120000040000000000000000 :=
  splitAt 1 107 0xad184e10000120000040000000000000000 part159 part146 (by decide +kernel)

private theorem part139 : Excludes 0x40000080000000000000000000000000000 0xad184c10000120000040000000000000000 :=
  splitAt 1 117 0xad184c10000120000040000000000000000 part145 part140 (by decide +kernel)

private theorem part127 : Excludes 0x40000080000000000000000000000000000 0xad104c10000120000040000000000000000 :=
  splitAt 1 127 0xad104c10000120000040000000000000000 part139 part128 (by decide +kernel)

private theorem part117 : Excludes 0x40000080000000000000000000000000000 0xac104c10000120000040000000000000000 :=
  splitAt 1 132 0xac104c10000120000040000000000000000 part127 part118 (by decide +kernel)

private theorem part99 : Excludes 0x40000080000000000000000000000000000 0xac100c10000120000040000000000000000 :=
  splitAt 1 122 0xac100c10000120000040000000000000000 part117 part100 (by decide +kernel)

private theorem part81 : Excludes 0x40000080000000000000000000000000000 0x8c100c10000120000040000000000000000 :=
  splitAt 1 137 0x8c100c10000120000040000000000000000 part99 part82 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part179 : Excludes 0x40200014000000000000000000000000000 0x9fc71aeb8008a4c844002a8000000000000 :=
  finishCode 113 0x1fc671ec6307df101e00891d0431e8384a483175d0bfe6a59ed257d5a5c60d892e5d50d809662497be307187400c5ef641d8397b07662dbdb67b891f5ed318340097be18bcd23b0b82a8d5f1918450ea82cfcf2385ed317ce378a875466e65a30eb1b7a9ad4e306b236219f9d1c33da60e6a1d519b56cbf67c17cd69f018e30606769fd1876adb5763066e9990501884710032505eda92b378cd5b400a4bdabec499ed2d5b5a7bd96504c5e783c9f9dab66f1681abeb43db6378b56e517826659ca8bcbb6c62e8bc071c396d3d948e0b372fc5fb2a127ed01705ed2bc30ae523a8263033d4c8e68dd378c6061dba387617ee3788ede30317ecde31819856d4f1d0a825ccabc1b0d5b481a07b49704de3357d3eaa31839c6a50529f1c6a32c24fced3f8c1a82548f029446ef69724ce432f397bd948911c2f7c5fb801ec18bacd6694ad2d03eb4b9416a4740186b35158b68f9497ae8d5b9886d456aeacd6615bb0923d9640f858da8a91d497a808e2cd6694a4acfa341cd412d57418b5160e7203e38bc8dd733b56d69692f79190630e42f69948e6db0e5a8c67b4b56d944c03969a1bc54933da433b06d8c1825cbdf1839c960a5517c1b630728cded2d5b3f230727cdee26f10c8bda527ef61961b028d27e1c7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part181 : Excludes 0x40000014000400000000000000000000000 0x8c6709eb8c2084cd00002ac808800280008 :=
  finishCode 83 0x3d8f23a8fe318d22f81db6407ce7e781ca91d072c7d7207c1e783127f103c3de72f92839087bd5ff290e0f27093f3c14f83c8394b66c8400a81c4ce42801906318398c7b4c81f16fa0c5506af855e593a0056473189e385bed3f8256f69725a9246fe6f1630e269a1ffc81ef539ac6b3d9ee21879c82709079ae0ae1ffd07ebe1bc61efbdbe8c1b58dabe2b516fb03c81f4407ff5abcc2783886fc7fec27a0e23df761646417c4918847121692f731c1cb3f397eda9b167dcc71223e66ab9bc56563172fd871e0e5c48f4318317731cb09495872d4024ac46159aa4adec307936db1251c3398d6125b383ca3866179f9dec2e639ec21cb6b3ce5f69eb98d25692f6817c450b4f23d4b7e6f1790b7ee6383965e75abce6347ace5f624b52672fa3d4b66600c5dcc741bcde28f993ef06f624a385e759169f16cc3965ef839cf69927f183 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part183 : Excludes 0x40000014100000000000000000000000000 0x8c2339eb825404c804802aa228200000000 :=
  finishCode 45 0x2207a15c7b0e62fe3a8ec103e071c1906da0e62df0f7a07c81e2df81e7103ce0ad6393c61d33849c85fc41062e93f8fcec4349fc7e759127f307414ad5b1ed97edd4838cd5b6afc1b5a7ab0136dcd576afba8820c5c3ded5b9ea206f0b197bcafb17fda72d590bbc0f318bbd8fe31906171e207876e613b15cb8ed639442a2f39087bd8c389c93f399971c7b74605a92a496ada88920ede8c0a4fdab63db839c92b49fb56dd86a4c91d62db90e3d9b58c7b7356ce261e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part185 : Excludes 0x40400014000000000000000000000000000 0x8eab78eb9006c4c888002a8000000000000 :=
  finishCode 27 0x1ec7518c0f387bcde30b7ce63318ae30866adacf4bb67311f7901e378b56cbe640f5a9cd5b50188398aa8be33892b5189bc669cb065892d5f9a7ea1f617cafb4fa97fd256c4957dcf71471b124396d5b4959bc6692872d5feb23385db923a6f1059975c3964b394128f96abb57cde25d75109a3356d217355dabe0bb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part187 : Excludes 0x40000014008000000000000000000000000 0x8e6738eb941414c800012a81100a0040000 :=
  finishCode 63 0x144442246adba1063a8be07bc7b71c25ac71cc5002b2759ead1e3899bc4e62aa1c24e667e7a0e66f11ed9bc6378c7310f7c180f18e621e783cca493f383962483230f17ed6727c7351b92d6a60f30f79f6e58ab524f667093999eae7b4ac54706a49072879dfc801ec8301e3079c3de923b0a099cba91d57fa90c1ca731940ea49397c1e6360905f0b82ec282583b398d856145839b57e0db1ece3026f193ea6db9282f693f3a7d5462ec1f098280f69378a4ae1bca3d4fce7312fdd07957f9f9c62f1f9e617b57ded2d6380970797b4c1cce6273183ce1ef6afa08c83d88018e263a19cbaf692e0a91ce632cf546698210a029247431cc5cc735263071bc5002a2f5abc731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part188 : Excludes 0x40000014000000000000000000000000000 0x8c6308eb908404c800002a8000000000000 :=
  finishCode 119 0x541648909ea50948220389b10e7b5b16d27a5fb615d07149fbda58b682f626c3b30f79cc61d9879e10881e86515c7f0e62f633893f8d2a6bf1ff901e14836c1ef41fc7c260f21bc63030485c8ad3d5238c5dc8b353cf8290b7b39f9e6af8c5dab706da0e6a4718bb38d43a80bb6b1c3b76af8b7d43f0b06523a874b832d4d43ea1d761e46afc93f035b56cde20f318bbd8e80ffe3033915ecec19623a42e0e640f722d073265af8942cae722a42d462a477b5c6bd47c9bc6624c1cda7f28c41e6fe3c10a101c5bf3dbd05ec210f7a0fe7b1a87c3cf07bda93018527ef696b19c859030102240f49fa0be3031cbe0e29e1628c1be4fac1cd3e64cb4f9cc51207a4fcffefe2d81ef64099702eda4693f6afa0bd07ea1f8996d5b408c93f5a1ab70718ffed530e98b7ce270f9e07387bde8651ec398b38fe3a84079ed293f0edc00705880ec138176d5b1f7c001d3505c733609c6d12fdc48903da66ad87bdcd67338bde1ef078c2df505b56c2ff1bc527ed5b80224841e0852307101cdd21ef18bb56dfc672307101c81e90b9ee31c5ded293f378ca0b7b487bd2170f9c62ed5b83ce7ab87ced5b5b20c7b0ec3ffc80f8507de92f83dec4783be93d7b4a4fd7c49fb56dd80e5a47634c8edcde23b7a3026f18b4693f876ef690e9876e505b56ded293f (by decide +kernel)

private theorem part186 : Excludes 0x40000014000000000000000000000000000 0x8c6308eb900404c800002a8000000000000 :=
  splitAt 1 99 0x8c6308eb900404c800002a8000000000000 part188 part187 (by decide +kernel)

private theorem part184 : Excludes 0x40000014000000000000000000000000000 0x8c2308eb900404c800002a8000000000000 :=
  splitAt 1 130 0x8c2308eb900404c800002a8000000000000 part186 part185 (by decide +kernel)

private theorem part182 : Excludes 0x40000014000000000000000000000000000 0x8c2308eb800404c800002a8000000000000 :=
  splitAt 1 104 0x8c2308eb800404c800002a8000000000000 part184 part183 (by decide +kernel)

private theorem part180 : Excludes 0x40000014000000000000000000000000000 0x8c2308eb800004c800002a8000000000000 :=
  splitAt 1 94 0x8c2308eb800004c800002a8000000000000 part182 part181 (by decide +kernel)

private theorem part178 : Excludes 0x40000014000000000000000000000000000 0x8c0308eb800004c800002a8000000000000 :=
  splitAt 1 129 0x8c0308eb800004c800002a8000000000000 part180 part179 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part191 : Excludes 0x40200010800000000000000000000000000 0xbf971e87140886816010210840000000000 :=
  finishCode 125 0x791847a1fc621706713c317a9164a1b0eded25f3260e05411d2963da66a1a914353460e5a79f062460e378abed876b3d62aad04cb87aa4cba0f6e433e2a58f539c86f618c08296692b04d501e1d181522a91ded32c3478660d921a4659ed24659ed28e7474985c62e362d0f69581943818848fa80a81774743460c36a93b9a7ec3b8c1a92527e93f8dda48d46eca310489bb491ac606ae37da4fc1471bedcbf39947aac53517c48d6ae9bc564e93f38121b247d3ef39ac91ab42887e1b093f42143b17041331bedc8a6f1811ec41202c18df60912e0b0ee62a8f563070e8560eb3348f9bec14f28c584a6f1581a77277d45e4cb37da47dcd70f0da4290d411604f123e96250d46324fd48e6f19cc6a2f7b4b88b4304d45f02c560f3556306c217b4b9ad68f1ecd3c2d553f8b02657cc60ded2a454869e89e1b8b0179d5049d920e638d6e6f10529fc564517c0a57b0c1b5593a90e3066b78ddae43731a4fcdc7290d27ef698c1b18a3183567d149fac048d8df6e43518b9852767f19cd6f613c0d47b49fc549324fdcd6d4f9cbeb33927ea497b4b9acfa3029543a5a1378c60dc87b4ba07f1981e60d50ea91c62e6e390e505a3a55ee8d53f3a91cd8721ce495a9a91567b399569f183504691787bbcc43584b59d89b1837b4a47d48aa474fbc4e37b4866d1d28fb7b4c8e9486bd8483007f11aec48b7b6c60d196a315249776518b90e2f4bda416aa35524a8c63030295276a31 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part193 : Excludes 0x40280010000000000000000000000000000 0xbfd71ba7d4288c805000200000000000000 :=
  finishCode 33 0xf43202fb5d144390ad4e61ea4fce668435763d6a03d07ef6951a932e732b90ded2b4b3e16471bc47aaf6938bb0f58aaa82375ee2d21811ed611b4c93f3f168f1775ed23bf49f9bc6479b0f5045813c49fc7170e397bd262943510b8320fce2e5fb906291f0e3c93f2f7a435ec631a450ed07b417a0c527e0bf604c721417a0c5500dacf69378a005ab73964e2e6f1857e0bf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part195 : Excludes 0x40300010000000000000000000000000000 0x9fce1e87e018a4806000200000000000000 :=
  finishCode 145 0x19c6f1ec571701f7a78842d0d2b6a2b10e8290e20f5540524cd21378ad3d2822cb3d6c6f12fda4763d6b4ec9a2f6b790f87b5c4d161ebda68c1c3d5969f28d5d0400c2cb510a92584b356da42b43a0e22e8d028bd88500dc7b4cd5d720938cde2e41969e2cb1e1cf69014bdb63063d5271c6f17b3c5fb5a7b20862a0b396b0c8011eacf657b4a006165ac8c7ab391d483707aa4e38de2e45987a09949eb586307308e0fee41378c3c31eaba06e28bda4317ee30e3876ada803c39aba2cb699cc3d1e1b4a625b8f0dab6c42f0e8356c7aaa2f946ad298786c4d836c7ad47cb90dc924d14a09bc6400ad3d90621d05d148517a8d5edb16ada5291d2edd1835a7c5fb7b48f55ab70f553f32c25492f655a7824e612c61d83ac53631c47919449fc351523b56d0625fb0ebb30e8290c80f5525f20c5282c539ccac55321a43282deb2e657adb14d1bac3d690ca4758fa3d548f2825a4a3d549fc9833083f72fcd5f05fb996378a91c17f13464a0a47507ea4310d45946a9411ea9bc659cb51672fc60d846218c5d017e4bd9ed69072eda4f49c61cb49fca42803d5271c941695c5fb8c1cc23271aa85fb7b6c4e32eda8cded32825ab693d9ab6b4f598bda4bf6c629093f501885510c05097063e7a8d433ef696a18f567b4b20d5b69fc11f7b486d52827cf9ed23b56adc1b39ab65fb2edc0a70cfbda5486adc3d5271c5db2e0bda58871125eb40b2cbf6c5b834a4e36adc81f89c68a17ec7433da5ab707b271a0bda5307b89c682f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part197 : Excludes 0x40208010000000000000000000000000000 0x9f9e1a87a618c4884100200000000000000 :=
  finishCode 147 0xa2240c62f093f3719c6adbd0f2248c5389760b952397ccc16c255c078b34f439728c651982f4367278e4a1938d4663c56119068015ad459232d572e082ccb0325058ab1810dbc1cb2ebcf697903970c4cc163079505e0dc361ab6d01705ed31bc5462a035363e2bda4fce4e33f3c3b57b485d5a0761ed31bc5893188ded2a475020db182d1a218d2719b6e7b0b5349a2a428106d857e1a90cec48d42305e3850ae457b48f5583af41a8301052c5c1836978d19724c60f3183593cf69731a8c492f3da45225c1836d0735188b75e868230718bcc17460dccb0e8d286f6930bc3017b4cf4388e8341121f9e6afa50da7ad5b17a8c058846ece63518a91c5ba60d6adc6176abc60b183aa8b2308c646064f1a9141461cb3723071bc5ab6ae460e1e18295a57250e3029a138e2e597ed48f356d69e4e3461ab6a338f5aaf9271b57c7aac224c6629a91e2c7cc2b47db0366adc604b46d2b498c60cbfe617710dc0e5a4ee7329f9cbf66f16adc487a35361e1a4ed5469fd06d8c1829630730c5ccb0ed4787181618b56e0528ed5cba1b7891c4821e86a060ec22c08c31561ea97bd286f599826e632f7a4c561324363065f37b4ce657b88f54bf6a1d89c6b352f7b08b82085e7a3069312f7a50da0721c1b505fa42e60ebd9e30707b4a0a4ed20b179cbdef698e05238bd51f341ed26307b91f2f4250e2ff985d28324ed286b8308ce3d0c5f985e8f92e0b494c1662f621907b2c7d1732829436a6b7948ae455198ab5547b4ca477b5cf5b504b49548f0b74c1aa4585baf6946acf6b35b872cc2ef69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part199 : Excludes 0x40200010080000000000000000000000000 0x9f9ffb87c10c84c24120301008040000000 :=
  finishCode 31 0x224821401868c5d23f1835ab7250d7062100283f47dcd2b306a4c647db10ec023617aa4756a724fd63f24fdab6b8340b2183548f200507e2dd4c09a3237548e80141fb18c399a5aa47611a4fc30f30ed2c76103e82f5a7cd2b4a0bd665a5b576695a505d86adbd666908f5523ac579eb293f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part201 : Excludes 0x40200018000000000000000000000000000 0x9fde9ae7880ac5a050003c0000000000000 :=
  finishCode 57 0xc63c893f891d07a1a771705ed2d5b3909c2462ea218e42709621184e1401ea938e1dab4fd21b2784bced5b2fd9705707b4ac0b1b88fea476aead455f3460cbced5b6a1cc358c19706588979d6a6d5b47dcd5b5c0c1720c4c1728d460f20fd08790b83123209e2a87214b1407b4c5e7271979e7b4c60da9a9e3523a876374bda541323edab63d596a65fb504b56c602b059a42d616ad8c3570504cf69518b574142a1d900317ec60f12320e817ee6ad8c04e26733551f06814133da548e3d58dd26e99ed2e432f38295ab6a0991f6d5b2fdd1874988c357050ec0a16a1ca1d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part204 : Excludes 0x40202010008000000000000000000000000 0xbfdf9eef9f198586c245201110080040000 :=
  finishCode 15 0x7a1a41839a8aa357d0072fc90d8c0a87548f07380228e9609b91d2631836a6c1fcbf72825ac324c4de2943a30706d2fdb488228c63032004bf6a47497cd4d378a004bf738f5ace801 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part206 : Excludes 0x60200010008000000000000000000000000 0x9f9fbfcf9c1c8cc44203301100080040000 :=
  finishCode 29 0xc23d0aa200617311ad2e7b4b50d462d428ce7b2807da9a6f16a1b49e7b49ad5a5318bd6837150378a20f699002aa3db650ea91da53250523b23884355615fa005c86a09268a808f58b42c316a38afd506aac37b6a3b91414aa31155ce610c7a7e640093463f3b585002d292f3b56d0030b74c32f69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part207 : Excludes 0x40200010008000000000000000000000000 0xbf9ebacf8c1884844201201100080040000 :=
  finishCode 157 0x1043a0f83d091f8c5e30d18bac0d01c24d86414129e22072f72fd07b723a50cb8291d7b2b0bd002f6991f294347d88c6523a00521aa49609a3e4de291d378ca474a19b882399e7b497ed48f079831af693979bc60ff3ddd28680164170397b08d4f91f28014a1bda6155cc1d7b497be119b0d5ed2e4b4a1b40a8208a1d518b04e40097ed40f391d25e8f9400ac9e8c0bda5cc2d5b47da087215913f3048dc9ef6947db10d1f7242e7b0b56d002f694f0e66c318602721735cd59517b0758b63017c194471644d1702f797ed1f7066cbe693159acf597b8c60d466c82185a17ce7b4a82d6965e3da6498ad3da532e0f696b0c7d7690a47d647358520ad439eee905498b08d42c05f396a6d677b4c60d2629436afc5f3486a48d619ed2d5b8c1b0eda572b8a0b96a6d4d8c1b57ded307f95f649f8c1b57d845813c1e1cd672f9a50cdc7a9cf698c09bc548ed5b350997316dea6f699a52c358c1a47d2c486979e7ac938d48af69a306c5b50ea403d5a306f697a9d07f4f18f55545408842143a581a306b1b4f0b584b823d59cb23714f0b584de32d3dab65f30da9eb659ab56d69e5f38c1d1877ad9f9d6a63d50da9b854308d5b431682f3bdc68c1b90dc931811ea9bc5a673da4dd2d21235cd671a8b4847860a5695a403d5a3065c17b4b5167b2cc55374b0ec7aa5e7461e85a2307359c9c63d548186b3da5cd66e97a9cd45265b4ce3026a30d49c63c39acee656218f0e6b3b994be70f0d88711a0741ed3188cc326e2a89e248d217cd8a7460d416d5b523b08e629bd6da87a9cd5d378abed2866cd94166f19ab6981bc65a9b56e265ac0ca238b3d9a56943159ac8e83fb59c36a5b594124cb695c5f359cb087a3505f369fcf698c1b56581a90d7b8a4ed69f09cded23698c19f9deb3460c2b2d5b5a7b4acc16d5fa0feb4b606d18372fb56d002943305986554490be7182da57282650d9bc5c7ad29 (by decide +kernel)

private theorem part205 : Excludes 0x40200010008000000000000000000000000 0x9f9ebacf8c1884844201201100080040000 :=
  splitAt 1 137 0x9f9ebacf8c1884844201201100080040000 part207 part206 (by decide +kernel)

private theorem part203 : Excludes 0x40200010008000000000000000000000000 0x9f9e9acf8c1884844201201100080040000 :=
  splitAt 1 121 0x9f9e9acf8c1884844201201100080040000 part205 part204 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part208 : Excludes 0x40200010000000000000000000000000000 0x9f9e9a8f888884804000200000000000000 :=
  finishCode 25 0x1201fb901dd049fac0d01ccd701e2c62f6adce4f9cd67cf9cd62f5510b03584651380ebb510739ab67ad8c1b1547aad5b981a6f18dd2d618be65c12c0caf172c8f55c4651d00ebb55e17aad46462b57c9c64e38c324d1a302733 (by decide +kernel)

private theorem part202 : Excludes 0x40200010000000000000000000000000000 0x9f9e9a8f880884804000200000000000000 :=
  splitAt 1 99 0x9f9e9a8f880884804000200000000000000 part208 part203 (by decide +kernel)

private theorem part200 : Excludes 0x40200010000000000000000000000000000 0x9f9e9a87880884804000200000000000000 :=
  splitAt 1 111 0x9f9e9a87880884804000200000000000000 part202 part201 (by decide +kernel)

private theorem part198 : Excludes 0x40200010000000000000000000000000000 0x9f9e9a87800884804000200000000000000 :=
  splitAt 1 103 0x9f9e9a87800884804000200000000000000 part200 part199 (by decide +kernel)

private theorem part196 : Excludes 0x40200010000000000000000000000000000 0x9f9e1a87800884804000200000000000000 :=
  splitAt 1 123 0x9f9e1a87800884804000200000000000000 part198 part197 (by decide +kernel)

private theorem part194 : Excludes 0x40200010000000000000000000000000000 0x9f8e1a87800884804000200000000000000 :=
  splitAt 1 128 0x9f8e1a87800884804000200000000000000 part196 part195 (by decide +kernel)

private theorem part192 : Excludes 0x40200010000000000000000000000000000 0x9f861a87800884804000200000000000000 :=
  splitAt 1 127 0x9f861a87800884804000200000000000000 part194 part193 (by decide +kernel)

private theorem part190 : Excludes 0x40200010000000000000000000000000000 0x9f861a87000884804000200000000000000 :=
  splitAt 1 107 0x9f861a87000884804000200000000000000 part192 part191 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part211 : Excludes 0x40018010000000000000000000000000000 0x9dae7c87a303c4a80300200000000000000 :=
  finishCode 77 0xbc280c61cc5d43f1a049fc00e80bbe2e89865185a8d18151db98c9dab418bcf18141582ce51dd0718c193b538462087b7c7e58c093b502ad3d500a8f4fcb3d45abeb15268a055ea31b1e302d3f58ea0edea3230b23883019a7aa1351e9fd506a1b5949e6db8b82805599b12641da3118398327e56adb4ada8a7ad9ab61b56ac970630630185224491845903970c04de282b1eda0edd040acd5f3058bd5abf2054de2d5b7418c180a40479a0e280549fc1c61eab4f5aaed459ed32cf4d7a3d52f1b57d02b20d5a562f563184670de3356c396617160c6bf49fb91e6ab8f55676f692f9c617695a30b2240d3d41a96d6232ac9d27eafb9426b3191aad2b46ea055a7a6db8d8e0bf41dc28d0400d25860260b317b88d2b91f2941405872c9a3351549ea4f8ff660b681885005dea27989293f963ac5f901693f268c80b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part213 : Excludes 0x42010010000000000000000000000000000 0xbcfabc8e858284a40200200000000000000 :=
  finishCode 53 0x5f19c57127f077c7ce3f7741abb1af4b524b31eaac5ce421df399b48ca2801df599d07940a9ba54024ed6abce4f1ea9ba495f2c960ead57509b93d47a8056a148461ccb2ccdc9e6bd51e8f55640dad18372facae363b964b6e8d549fc60e3749706119a4fd44e6e9721a43909ccd2170f2c9da8f9a3023bd48e971e49fa409e2088c1c4d603b16773dc49826e95a89ba65998f55ed32be5cbe6e90efac4658e9cc63061df470d469125718398621df599c5d18c197460da8ad58931838c1ce224fda772475ed31830efacee7b4ac8e22f01df8c0cb511eab55d06ad219edaa3b8c1ad24b8f0f5549f1834a0ac76485ad256a61df (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part215 : Excludes 0x60010010000000000000000000000000000 0x9faaae8ec1020ce00200200000000000000 :=
  finishCode 93 0xce388b6079d8c7a127e3f77b4c60b599d1812ce847c92ef692f3a4bd70611d051aca2f2f3a4bcc5e9e237662aa7b47aa5e77b4cb2d0529bc5ed3356e65138398bf0b519acef691ea8e4e7b48ef49966259a9e8dd46ecc533128f557c631401f78b1e6adb4a520ef6930c9cc5e05c108724cc577b7bda4f5ad5716faced6a2901ece592a4fd872c5116fcc23838989408b30e5ab6f6961dc6255a1b11003d0b81cc658b9ad5ed2625024c6b562a93b47aa6236ada80b82505ab3356c36ad29618b99e69d9345ac2d5b35ab4a565b351c9a258d814af6d3e39bc4e623d5378c6b56adb5756c5005bf2d4436a0994a0b189017063e7bda4c5f054476b18159dad445be4d19ed262f732b51dccb4605ed23d5592b55d6a21b56518c398aa0782d0c573e05be6a39842b2b8398f54de26bfa0e6f696109289e237660593458427cf35fa796606b56e0e2c218c0cc216adc1c60ea2dd49fcd5b16fc93f4ffb08922c84a278c2361dacb635fb4b648eb887ad91bad617b49bc45bad5b1e9829662abda4d7f308d876e20f549a33da5ace3758d6ad5b725bda5ed3390a813b45bf0759846b17604bda436af539cc2907527a4fe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part216 : Excludes 0x40010010000000000000000000000000000 0xbeaaac86810204a00200200000000000000 :=
  finishCode 157 0x6f1d48003df043387337a0d3716ed67a93f59db55d6926255023072c453da92b59ea505ac33da53feb277b4cd616ada42d27e7135717c6c1401c1cf69483a504c1a2df398a40b43f04d19cd63f716fa4fd501fbbd467b4b8f55e2c51163bda671ec1be366b9acf9ef691fbce4f897690771ead247eea02cf64a0acc5ab660130cbc02df9c9262f7b49f3d67ab53268cc4340b8308d57878a93f8c0b154c1a6f1312b98e1a89f3dec64d16abad2478a940ef65a1b0f5282d43629a5066aeb02d27ef6f05fb93dab694241e6adad5c77b06f8f9e9076adabc6838bd45cd6d5b268a80d82b89418e622df0b4cd5d61ebd4520e93f276a5047472d8ae2f86e2c9c7de6d598464c77b3976d23ac2387ab18396a62df48ebda5a848e9f96605abee0f67cf629b9958ab41ed816afba00821d06617830c9c4ce42a358e62a439a8b27fce6230167124570be6ca2f87313a07eee4f88ceb116b3b9ada8b1f5d6a6d5b8c1c3d5374b57c8f32014b0374c5c16afa01651db4f547ac62c83f761ace4537493b549e3d589daa013748dc65a39ba5ab66e999c7417c5b1ab70f147ee6235c0c33393dcb22f56ab9895c461dc9074028bd4d46acce4f72c82fe730c47904eb4f45ead5731282de6ad8fdcbe6e81b35c46abc58d72ca0d45eaa012ee6ad98360df1bc5cd6b3d3e7b966695a0d5987115c6ada0ad076a499437183398a8d68c1a47518501384a08f164839f9587b241da56d5b398abed6c3d017f0e8c5565db57dcafb895f284e30246505f976d5f69411d1c7317a1945e1d4398c0093f6811830cad46500b56e415a77e599a0554024ed9ab682b41da306e99402a3d415c90b389b56cc17242d3be301660602d223563e78f5506a805374c3d55a4cc2348bc092657c81b60eaf6958d93b5ab6835415af8e43a0e692f3999c4e83aa02d3c6b3cf7183ac60d61ee492f39c4d68f356527ef696a1bda6 (by decide +kernel)

private theorem part214 : Excludes 0x40010010000000000000000000000000000 0x9eaaac86810204a00200200000000000000 :=
  splitAt 1 137 0x9eaaac86810204a00200200000000000000 part216 part215 (by decide +kernel)

private theorem part212 : Excludes 0x40010010000000000000000000000000000 0x9caaac86810204a00200200000000000000 :=
  splitAt 1 133 0x9caaac86810204a00200200000000000000 part214 part213 (by decide +kernel)

private theorem part210 : Excludes 0x40010010000000000000000000000000000 0x9caa2c86810204a00200200000000000000 :=
  splitAt 1 123 0x9caa2c86810204a00200200000000000000 part212 part211 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part219 : Excludes 0x40408010000000000000000000000000000 0xbfaf798f322644888100200000000000000 :=
  finishCode 33 0x50200398b10e211963068bd520b182cc4a9435893f94666f157fae047b8b82c2f378a0acc2ec5f4a1919649fcd5b378abfdc466144378cd5b415a0ec39702fd04a6f19a93241d46300310b20bd4c5f209505694394449fcd5b378a0acde341c4d6e1cb30ba0956c05fc1bf0e5a8882b817ef67592a096 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part221 : Excludes 0x40400210000000000000000000000000000 0xbfabf8ce905606809084200000000000000 :=
  finishCode 67 0x801d06719430c903da5f0bd4c46731629c907311af8ca2e02f550fca47400ab86cd968e46593c2c535228565ab65c1735a50a458d9a4e1523a87e5a9c9e50348e65ede80517aa0057c630baf1b352864e1378901d5c2f9c7235a99b86f19ab692357662aa0ad8770759a7ee6b2e08ace3070f1504ac5362aab8a0328be1cc59c7107ded5f9486a1b62acd5b519a87e6116a692f95e6c53612a7d658db308c2d88251e2825e4faa8c56367ef61ec4856b1a4be83da50525f355d876a495b1841f7b88a2f907e7fb270d07b629b154fbeb0793eab0583fa925c4415c805697caf15059f958471144518cd2f523b56d0769f59672c0b584a0bd04ace318d2f3f7c9f5270a7d65228e6648cb0f60f6d5b4979bc507f28d523a3c5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part223 : Excludes 0x40400010800000000000000000000000000 0xaebfea8e14061581a020210840000000000 :=
  finishCode 91 0x2e0c43a0ce2886197b49895b0331a67287c99706f16f971d49327d49c2b1b89c28e75848b7e58d838d28610c1aca27891f4512860e39ea24e155090b39ad27ec3d7a9c82b8c3c1c5c47611cf0aecd5611b2c6a91c1c683b2e3d181960a5c77b4b0f5d83e01c6b3d93ca93f83cb15505723cc4a32cf58725c7a0f64e147dbda55c6c0f05a0fe2a20b7e57ba4a4b8e93f6020f7038cde2c39582c929a0e2b3d50f9cc58451194695a0ad02b171dcb69292e3d071473b4f60f339153ca6f1071971e398801d612f69611447bbc7db151ac1543e5c741dac16584ca1fa0e26f1651a84a13c48fab85f34a1c61e8c18b7d636afba30682b265ab910291e611ad1c5a6731519cb3d5a9a703c58996af7a306f7161dab9102887318c0ca1f5a3a4a45a6b099cca48d83da4a493f2cf476683b8423032bdcd6e0b1415ace4de20b1961a5f36b3ca33398ad4d5c631800ced1835829385842f695a38b7d02b282527ef637b4ad4cbe72786306139504ad4d4461dcf711e2a4fdcd6e658de2e23da669ea87d0560e350fca33232cf69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part224 : Excludes 0x40400010000000000000000000000000000 0x8eabea8e800604808000200000000000000 :=
  finishCode 123 0x388d207bd940f3ba073141fcb170718b7e408c92d62b8b7d70398a184073129ade586ad3daba9c3dde4f0bda5ccaaff98a7286ded2d29203c0110338c6000e1a8b984fde8c3497bda569281f3178ffc81ed02e08019a8a61730cb089e2b86176c025f35758167e7353b495a5e907398bdae8c3b93d8aaf6925da3ce6adc38b47ab494c46f69970398a609e3928707f695c605002d63927ab15482cd5b7b3a41d8c5c100320fd6869127ef03102df4a0d633d451e6a33522b14d43f302cde32c5548b24162e09afd01f3da4e628c1cc4d0268cc0b629a415002f599286a4725da4f658aae0c4340a02cf6723b56d43e60130cbf083f87be93f16faa062541fc5c769c8b1dab7250c6250d6c49fc91f40fb4fe49fb58deded5b834a91f1deab89e39002f776a4b56c58ef694f1ab64bb8306d2b4f1c822503df9ab6a336a2c7ef50f985e6adaa0d82b8d5d9cd6c21366b15c58e2df68128612cd5d62ab93d4625a1bc6479a4fd43f06f91e6d5b837cc3b407b02e7b5c1ecde2d5b50fa78e7b484cd4163df571b05018c398a4fe6288b7d502e0cc23694b14d48ed490dab54e1b4a505ac680f9692d5b41fac1d8463ef16faf8b62cf650fad4cbb6d5b25d8fbc747282c976c556ada8cd1c4f167ab537b4c5db268cf6b2c2cf69629b095636d5b5b1b0521704a0a47507f1385ccad2f89c24e19aae82f400ac1e48ca91d81606348ea507e59a5ea313f2cd63 (by decide +kernel)

private theorem part222 : Excludes 0x40400010000000000000000000000000000 0x8eabea8e000604808000200000000000000 :=
  splitAt 1 107 0x8eabea8e000604808000200000000000000 part224 part223 (by decide +kernel)

private theorem part220 : Excludes 0x40400010000000000000000000000000000 0x8eabe88e000604808000200000000000000 :=
  splitAt 1 117 0x8eabe88e000604808000200000000000000 part222 part221 (by decide +kernel)

private theorem part218 : Excludes 0x40400010000000000000000000000000000 0x8eab688e000604808000200000000000000 :=
  splitAt 1 123 0x8eab688e000604808000200000000000000 part220 part219 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part227 : Excludes 0x60001010000000000000000000000000000 0x9ffb8b869cc00ce02020200000000000000 :=
  finishCode 27 0x6f17c7907fee23f01e75c127ef6795fe90731293d50228dda0e690727aae0f698c4ab15920e4cb1dacb2b7b69ad5022b4327ab60b43962a81150fbda417e731839ca0b50eac556ae3d5791e81eac81140f98343cef69312b89071876aaf9408a4fc3ce4f59022b60aee6af9cc507f06d808637349fb57ce62f43da527e2dd8e62d5d94929f3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part229 : Excludes 0x40801010000000000000000000000000000 0xbe73abc61c8b04a12020200000000000000 :=
  finishCode 43 0x641ac610e66b2250662a876d016815943a62f0eda3e4e4261991f2721611887a140312b608c24fce627c18912f775a4b154fead53987a6f150fa87e05aac767b4bf0a35949282b617cd4771e8ed5ed2a3305a9bee47493d5056a0b8e626197b4bd0c43486255e194517c6f10e99cc5ac7287dec26fb4f9aced0566f183a6d478df67f53989bc527ee22c880b96a23db415874e37dc91f650dab073d23e3db7e1ec3179d63ad5537da90d46a9e1c26731b58cbcea1d9ac6b1d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part231 : Excludes 0x50001010000000000000000000000000000 0xaefb8ba634a014a02020200000000000000 :=
  finishCode 45 0x6f1e47603defc3d083b4a0c4ad4d898e9f52e3a50c7aa60d2e1a4b171ded2a0b2c6c1d640aa4a60e3131d27e8157b4a47de85c1cc30f4c36af694949834c4af699ed3393d23e5e71edae0ca1895eef1fc60e2a1f494a50c0df3ddc30660d479bda63e5ae0941c0a099c7aa3341f8ba521a9314f05d2c1787be943609ce3d835bda53ee83f5b13c5f1ac60bc0b74178f7c997232e0de0b57b4a4a58873dad69f0716afc1d5ed282f494b9861d9b8f48ca83f378bda48cb0ba5ed29295e08cb02fdeb28cb2cfbda4766c1350fa91d65b27dc7bef23da527eb20f6e41589fe62fa4c4fe271327ac931 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part232 : Excludes 0x40001010000000000000000000000000000 0xbef38b86148004a02020200000000000000 :=
  finishCode 123 0x7a1fc790df71c2461a3175e1c46c060eae1f8731029c5c7524c1d67b5a8cd46a7e1bc649fc21071946aa1f48f9b8cfe294250e523c1d64949add46aa1f7e143f28cd492a1f9466d82b8be1cc53c6b09eaf6b8dbe81136fcf69522a0465199fc648faf8902914dbf460523ee4f49fa8ce2f49fc648f97a5467247e1ff8c1d947e05f6d83c87317619c415a30b1d69dc6f1265ad44de31236505bda5aaae6b40ab02e836a82c7b693f7b4ce6b378a4fde4151ca1f482bda4b8ea2f41da87e5239bc5ed30ecce62d82f093f4e1184a0fead5398aa7091eab54e51aa510719ac6c3d384b48d5d9eee7fb399a82da431a4ce66f6951ab02dcd720acde27338de22a39ed2a1f2e3a8bd016fe378d63287090f7b08a82435286d479ed25a1408ac967b4bda66a4c3b57b4aced6a2c23f0e2348ca20ad604fcc8157b4bd9d23e5c2434de33da5ac6d55988f0752f3c1c6599a05546af692c127e7d19692b51a0e29432f39bee48fa505e73519437db04e48fb58e2d0bd856665a1923ed25964a1417359fc5ac306f838bda62f3d06f4188f0d492f6949fb9094358e47964a93f3f79c24e2eca354e27a9bed23ed23da6405a91d27f1bedac590e66b1d8fde80b697c1d3592b48ca27de6aac1c5ed2f671eda87e7b4a0adf86aacb498389bc527f0719692929265862e (by decide +kernel)

private theorem part230 : Excludes 0x40001010000000000000000000000000000 0xaef38b86148004a02020200000000000000 :=
  splitAt 1 136 0xaef38b86148004a02020200000000000000 part232 part231 (by decide +kernel)

private theorem part228 : Excludes 0x40001010000000000000000000000000000 0xae738b86148004a02020200000000000000 :=
  splitAt 1 131 0xae738b86148004a02020200000000000000 part230 part229 (by decide +kernel)

private theorem part226 : Excludes 0x40001010000000000000000000000000000 0x8e738b86148004a02020200000000000000 :=
  splitAt 1 137 0x8e738b86148004a02020200000000000000 part228 part227 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part235 : Excludes 0x40000051000000000000000000000000000 0x8ce79bae34004c84800aa2a200000000000 :=
  finishCode 37 0x1e4891fc6b01cf077c3deec420c2400b203a4fcf3995c869f3517815d076f69902a5018de20574059406074bda41cf20ecb8e16f9d84914463101683b4f5cb2362a9bc4b8eb399c926f16b2005f05f6e47904a5fb5a9cf69412b90ca0317edcc6f5980a6e434129bc45f705be17d879e7a1c8b122d3caa213f3b57c7ce2fb630bf7290c81e50195feb41 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part236 : Excludes 0x40000050000000000000000000000000000 0x8ce71baf00004c80000aa00000000000000 :=
  finishCode 131 0x18c4820049fbf8d603a6509a0441e240f60061a843da6378a84d3f2a49611ed31bc5ed324a6722c1ecde2f697a1d83988bed8a716adcc6825732cf6983da7e5426d62f89f98de28312fda4a683dc9f97319bc5ac5f03dec5b91ba5fb412a0c43a66f1907e7c41ee722ac254926f1412bda5cc65db8a02f69791e8852105503de0ef510a023db9c8e80b509c6f141dca2f524971dc8aa3b8a0280b18687bd64f02ace621df073877e0f39f5683aac6cf7e7311f38c1c81f003c8fe3d8d203bd740f3b08a49411ed31bc50569299cc2f6989a31fc4fce6f1722bda43df28be207a09a32c5da8a6236ad9cc461ab62084d141ac94340597edee32465ed320d4bf6c2230f778f6ed2b280b56cb22f6949d979e7b4d103d0d61eae62db56ded28353988beda8501704fc9cc5ed31bc561a90d7b4ce6389a26f141dc7317b4b0ed606b1276aa17ec7b7398cde2b437b5ce6389a26f11d0a4c57c490a02f718bf707b41d96adee32095c8ed637b8cd6346168f356ded2835378a4ecde320eded23db7a1703988bed3037162f242dc8ae617b69bc5ec6b0d07f524a0045bb357dabf3db6378b56d7c491283ebcf6b83cbda4b7e5fb521ad05686a4394926e358e35aa7e4fce6f1400c929494c801611445e140415a0ec7b73da4e62e6187b6e637b49bc5ab6f62083db90025fb0f7a02d700f7c6f13f8a376378b4be584bda4596d452fda02cf846ec80169d9bc43de8255d0a02027986aa49517ad1da5b39167b6a8bc3def69 (by decide +kernel)

private theorem part234 : Excludes 0x40000050000000000000000000000000000 0x8ce71bae00004c80000aa00000000000000 :=
  splitAt 1 108 0x8ce71bae00004c80000aa00000000000000 part236 part235 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part239 : Excludes 0x40000010300000000000000000000000000 0x9c73b8c7ce50048016802060a1e00000000 :=
  finishCode 41 0x2107a1fc7e1d87520c072ac80f172fce651ead183203a7ae7b4ac1ce62af1986a9053989cbc1e20f1a141ff903d61317cd8b6b3972fce655d0e62c82bde41f9c8614629c93b4f59ffd20a3bf9842b0f57cc9eb418b18de3f837b9842f693ef8ffc81ec82e8713927e733592ca3b2f7cb253f107f2d45ed293f5c0557250e0da83f599ad4546b2bc4b82f696acc1d544327b52861ef8501cae5f9cca1ef72fce65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part241 : Excludes 0x40000010208000000000000000000000000 0x9e7798cf1452048012012041810c1040000 :=
  finishCode 71 0x7a1e4742107f0e5f03941e2ca2e0af7398a35e524a8bd87a2d1517cd618c1b0f58a6d62789ed8e42e6b9a4a9ed5a3bda6694a8bc26ac3d09e8396312850659c97cc3de0f1740fe329245f6d4230b42e03d559ecc4362dc60d21a9438c1cc5b8c1ce6b62db4cce6306d95fe6b72fd9cc63066b7961a5fb741c442224381e4510a50e3f8bd9d252f6952487bd4931fc5ac7912872c163067090f7ae0d2f948680158bcb3d9a426fb3f8bda5486d2994927f1510a50e8c1ac9dee22bf0f7a8be245f144410df68d18726b3d6a49ccd60ae6b9906b13db1cbcfcb3575ac67f17b4ac6e6a4bdb66adb97d60a6f17b49fc4fcf1704d7e6b5694bda500312328c2278c5b9252c5b83def69a30738f5636b47500b2b41fdea6e6535fbddda525bf6ae9f8f69869e6f1265bd86 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part243 : Excludes 0x40000010200400000000000000000000000 0x9c7399c71ce084811200204889002204008 :=
  finishCode 71 0x3c8f43f90a1cbe07283c4c2e62f750e131f9ce6640f0729cce207c28de358af78310c17db02e8c1ac15cca6f13ffa3ce7329bc5ed2ca2e0c3d948706d6058b45252c0b987af614f9b58e479bdc5ac26f13f1a4b2c95ed2a2f49fa08c3d692cf691b9b585abb3dc51ba6f15a17049fac9e2eeac6ded2a01399ad453f328f5a8724345f6b1b7b4b29062a02ef49fca015999c4d06283f57ccf6959396ae6a4ad44e662d164127e72f907ee65826ef692e0ac7570512243712c5a4ad44f43ffb54e494c60e7b5a90daa68cf9442d535f1ac64081e8f3949e93f494b9adccb17ed1e6b3b3ff9e0fc1bed4032c1527ec219ed2d2559db555ab2d3b899693f500c40f49f9fbe509a0c565b3d4daaaf696109ffd06240f399c7ff7b4903e106b170207c9432fd8bbcffe83f4fcc40f3ff8bbd804ffca3d506a924bd33db60e31810d3bda460f27e47ce93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part244 : Excludes 0x40000010200000000000000000000000000 0x9c7398c714c404801200204081000000000 :=
  finishCode 91 0x3d05136515c840e62fc428ce03c560f1895687353cd7a9317b48395d0397c90b5838395a5b1f7d60a1877b4ac1cd7b103cc4a38f8b6a0e51eaa4fe147420c3178c366909ccd26283f18b9af67bbb584e66943840dd31bc52529430799af661ec60d68691f629a806006a5d035596d62e883960ff351e3060e58d571b1dd07f1ac0729895eb71c24d7a72f207a905d17a9cd290ca84b635ebda5905d1ac399c83f390a70f69521cd2949f86d5843280527f0719ed271759da4fd6773084242d498c1cb0549f9fd480e0f1510c05a1676fc27093f49dcb3337d8ed54033da60da6f1207c5b735e9bec75b0a3dae699b575cd718348fb56d63705d4982fc2d0c824fded306d54029e19286b055f1fc4f080ee8020e8c0b56588ec5f5a3cb339c9ed599c9e733836cf698c0bdad3e6b336413c417b11e7b48aad1e6f699a86d5d9ed2d2183c9bec81f0a448d632040f411f838986d67b49fd549307358db5867b4b50c99728054373085ed2d497e1ed291f9abb0730a6a8d5aab41cc75aa359062b05906240f (by decide +kernel)

private theorem part242 : Excludes 0x40000010200000000000000000000000000 0x9c7398c714c004801200204081000000000 :=
  splitAt 1 94 0x9c7398c714c004801200204081000000000 part244 part243 (by decide +kernel)

private theorem part240 : Excludes 0x40000010200000000000000000000000000 0x9c7398c7144004801200204081000000000 :=
  splitAt 1 99 0x9c7398c7144004801200204081000000000 part242 part241 (by decide +kernel)

private theorem part238 : Excludes 0x40000010200000000000000000000000000 0x9c7398c7044004801200204081000000000 :=
  splitAt 1 104 0x9c7398c7044004801200204081000000000 part240 part239 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part246 : Excludes 0x40000010100000000000000000000000000 0x8c6338c7a21004800480202020200000000 :=
  finishCode 147 0x320be3d05157f220801f8852107401e2bc03949071f95ab660b398aa8b2182d67706ed282c25892e90b4a0c73383acd5b2f99cc43df039436727fe0d65fb3fd876c1ca731880e1db8e627fb81de1ef390cfe3783db8e661ef0edac91224362fda02d07f278da7ef696ae8f4d4432d256a2d5b48f9c86891f87f2147b1e880106b1cc462e1ef077b791007bc7ab20ece6283b927f2014e62835921b0750f7c40bc3d0d40c5d8469ed183412a50dab70f55ec2b099a7ab0f2f9bda6412a4a618bb14e494a055e87b1a5720d4ff61df073ac8bc330af99856a3b7b48f55aae825509c93f599cd575149fecfa31af6306b076958f55780efbda6412ac96160a7fd49ebc3d0835881743988f5669ea43502a713611cd5b83ab57d27e943a0ea71340abda683a9c4d02a7139062ea338ba077d0631cc4e26d39961281f604cf6948fb56e0ea1ef398ba110207d5f31c4d216d5b9062d2f584cd5b1d5a8edbc078c7310f3bd0a1395f292b398a046892147f20c6f1ec711f80f7b56e3ed83bcf42e5cd6361db15630f34be0eac2560eb58e004f1cc0b398b56d25293b0778fbe398ae0f424a5c44a18c5da5f41d5a563db41ab51649fb525ed2d5b412c9432f7c7db605a416002fdc91f4058c5dab7202dec711bc7603b6815904a0e51a9c929398a47e3849cc616f8394f43d9c929590e63209562f34e502a731591783eda4a641db56ce6293f8e1293b4f59c266ad9cc56769436f1680ed970640aa4fd64b1f6d01727ac1ce8356f127f03943b71878ffe731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part250 : Excludes 0x60000010018000000000000000000000000 0x9f6f3ec6fe7c1cc0000ff003002803c0000 :=
  finishCode 41 0x1e8831b0740e63000f4e00abdae0f21e77b4988cc4a94079dcc73da5876e65a0dac0b7b4b914de2e478d6e5f30f3a82c3cf1ece839838ded2731312a28b4180e21bc5ec3503cea219c8af61517a503d39c8b0755228afc76b0759abae476aaa48aa250e47876ab011e9ad0e0e70595eceb150c5abfe7bb9eae0ea69769481cc0e3390deee1654a148b398ded22ad580ad0dcc73da5cbef77541245a0ca475ab8676156a875abb0ab4f66f779abaf6950fb56d540f3c1e67b4ac0476ab435238636 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part252 : Excludes 0x40100010018000000000000000000000000 0xaee7dcc67e7034833405a02b002803c0000 :=
  finishCode 37 0xf2388a22f080b6b1076ea356dc8f0f6d4633dae7319cc545ea497f0ac1ed87bded728bdabf292410f397cde2c537b5ce5f62987bd04a60200bc34bda926f19462e4598a6b5345178378b98e593b0ee0f6731731cc537b4b5860f735158aa7319876d49571b05c178695b57d4933da5c8e73172fd0797b4af06b7948ef692cf9cc60f3167cde2d5fa307391d3f2d5f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part253 : Excludes 0x40000010018000000000000000000000000 0xae7718c67e7014800005a003002803c0000 :=
  finishCode 133 0x741fc791e8830c46625186c73118bb5265189c260e706358f62d01ef481a5f2c6da92ec2506e247dab7048562eb058c0b4b5cba6f100ac1354a1c60d62ed47468ce65836bd9dac26f1468cf77582a47cfcf3da543ed5b5829c25704a17c498a50dcc7202d686f6980227bb41db98cd83dace65835a0edab6e47582ad4dd8711cc741ecbf683b412acf66189bc4bdf34be5a39705a92f69381c448fa105e79ece80b524bd9e517ac16711ed20a59cc6d491eda8bd6372c8922a8f60f6dac3291da92a495179b8b81bc4b4327dd8be7e79a52161894694202e6b0a095286f634a63dda02dac2e47a0f69293eda51073941291f722cd29697a926510a47de8711705248c1cbbb357d20b2e08c3066697a4a5a56d5f5f128361cc2f3f3b56cd6eb415a1ad0c49943e7e7731bda66b09f9c02338fd862e453f3cba2f8942e0c2f93c66df521a47d48eb434a1b5262e09bc4fcea4737143f3da4fceb059ed2d55617c467521a435286d2d582bda6378a4c5704117c6b20c5905d2f69968ee5d4fba50ce125ef498c5dd945e93151a9c250771beded291f2d0c6f10b88bed23e80b5a9a50e206b104b28bd6022d151a9c245f67a230a359ed26b749d990ec30f5a7f460d8a66b7378bda68c1cf7161d9beda5f1235ed27311edcc256b1ac445d2d641ce5178beded33d1103c89203cda8b17cd20b24a5182fdc9056afa4c68c1ad0c1df2a8b224892986f6c5b1d9ac6e615a4a506ab47926307b902ab1b (by decide +kernel)

private theorem part251 : Excludes 0x40000010018000000000000000000000000 0xae6718c67e7014800005a003002803c0000 :=
  splitAt 1 128 0xae6718c67e7014800005a003002803c0000 part253 part252 (by decide +kernel)

private theorem part249 : Excludes 0x40000010018000000000000000000000000 0x8e6718c67e7014800005a003002803c0000 :=
  splitAt 1 137 0x8e6718c67e7014800005a003002803c0000 part251 part250 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part254 : Excludes 0x40000010010000000000000000000000000 0x8c6318c678a014800004a00200200200000 :=
  finishCode 137 0x40051d7f2147a1e4550de303bcc2e6237b1487076c1ca0ef89127f072c62e929317c1cb881ac5c081e307494ce634a18ede482ae09424a5cc71b7da7b1817b4a924bd294345168f3dada7af6f524971dac33dac91a93f9ed2b8378be27ae4988edc5d29291ef968e7a8b90d2522df15aa4fe62f9ffd2621ab836ebe440f63c8d61f82df0ed903dcc72d5da4b3554e12b43f0b0593eef6958d8b7d27eca355637da47cd7b2789f79ed2c4751acf694fbad253ef24fc81eb81b8a00ab6583ac7585ec5f4f5d0797a99f9c396b0758ea5112202e246960cbf6f71498a50d74720ce67618872dc872c5dc8a9eb723b4960dbbd458621cb4f5cf6f7229bc436e1cb591a5f1c2436e1c73dbc1ef16fa47dcc7358e30693158da4a45bf082f9061ffe0748bbc81e96076dedf0f1c58ef7196a20e56aab50ded2c5f963640f177c3e7072c28de2d0ea360ba1f82df43127ef6f93eed211dfb4864fbbdbded25dd9abaf697a89bc5e8378a3ce62abd4d27e5dd72fc7ff831cbf3994f673dbcd529eb6298f6d8ab1fbcb2e6f1751280e9bd4e692971cdf6f6948f9ece5929f6c46334953d617362aa7dd67ab832891f82aef6949fad452522fb47bcf6f57cb9956a2a35927e7e2d06624fc9a33dbc486b0f1779ffc5df27ae30e80b692cb254058bbc982b21c24b83202da4327ddac6b51791fc891ac6c07de1ef4f5cb2716f976e721b585f86c0cc1eda02d27f18398aef699872e63945e3db87df079d4472fc2df49f9bc5016b430863f7a7e53d6f6f378b98daab2f8ae398e5248efd3d727e548718394928f5695bdbd27ed61 (by decide +kernel)

private theorem part248 : Excludes 0x40000010010000000000000000000000000 0x8c6318c6782014800004a00200200200000 :=
  splitAt 1 99 0x8c6318c6782014800004a00200200200000 part254 part249 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part255 : Excludes 0x40000010000000000000000000000000000 0x8c6318c6310004800000200000000000000 :=
  finishCode 95 0x1fc28f949dd07a1e4420c5e9e460e6128f5504ad2b6afc48e21fc640587bd04abc24f67238f55ed312353da1e787ab123887f190161ef412980d6190026f17229fc60abb0eda9280198161e72edb9958a6e4549ea788c350731695b57ded3250e3063d56b0c307711ec3988c1d0033585ecf41b4b3e8019246b1493351d27a801500fe334ee3069ed3989fc6593c60dc8a3078fe2f6360d6247e8c1b56c3ce801541603f8a089f59ed2b53690a4c63069436a6cc5f0daa4ee3071838dc7b4c1ee268c60cde24d19c8ad6242e7b4a4743cee23da502b20ed45e135967b07b300dc732c7d16179704de270391523324c58624d14a1cb278c19f45248c1c9291edb99e4f6b58d862835494b511837a1e41eabd81b595f61ef2f983bd23f06d58a69319ab67ad6a3ac0e6596a69311b9d1817b0bda5cbeb3d7b1a432d4c3ded615a9cd2b246ad2cde2f22f07c0f56606b4adabe815412bd0f6987aa83517dac8b3d7b4b4be61ab55683aa09183901671359ea7b6510a006306b277a1786afc6f1398ad4e3f8b4ae3071f8521a801 (by decide +kernel)

private theorem part247 : Excludes 0x40000010000000000000000000000000000 0x8c6318c6300004800000200000000000000 :=
  splitAt 1 100 0x8c6318c6300004800000200000000000000 part255 part248 (by decide +kernel)

private theorem part245 : Excludes 0x40000010000000000000000000000000000 0x8c6318c6200004800000200000000000000 :=
  splitAt 1 104 0x8c6318c6200004800000200000000000000 part247 part246 (by decide +kernel)

private theorem part237 : Excludes 0x40000010000000000000000000000000000 0x8c6318c6000004800000200000000000000 :=
  splitAt 1 105 0x8c6318c6000004800000200000000000000 part245 part238 (by decide +kernel)

private theorem part233 : Excludes 0x40000010000000000000000000000000000 0x8c631886000004800000200000000000000 :=
  splitAt 1 114 0x8c631886000004800000200000000000000 part237 part234 (by decide +kernel)

private theorem part225 : Excludes 0x40000010000000000000000000000000000 0x8c630886000004800000200000000000000 :=
  splitAt 1 120 0x8c630886000004800000200000000000000 part233 part226 (by decide +kernel)

private theorem part217 : Excludes 0x40000010000000000000000000000000000 0x8c230886000004800000200000000000000 :=
  splitAt 1 130 0x8c230886000004800000200000000000000 part225 part218 (by decide +kernel)

private theorem part209 : Excludes 0x40000010000000000000000000000000000 0x8c220886000004800000200000000000000 :=
  splitAt 1 124 0x8c220886000004800000200000000000000 part217 part210 (by decide +kernel)

private theorem part189 : Excludes 0x40000010000000000000000000000000000 0x8c020886000004800000200000000000000 :=
  splitAt 1 129 0x8c020886000004800000200000000000000 part209 part190 (by decide +kernel)

private theorem part177 : Excludes 0x40000010000000000000000000000000000 0x8c020882000004800000200000000000000 :=
  splitAt 1 110 0x8c020882000004800000200000000000000 part189 part178 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part259 : Excludes 0x4000c000000800000000000000000000000 0x8d573c93684178000185012000600000040 :=
  finishCode 53 0x441123f90a3203058105e6b0f92565d5527949dccf23ecbaa9190e4b40737901293f0699c6db841ac0d3720d1816a4b56da72f69470b4102034e40587247f25270e4c61d81a698290d018156c6b1ce6762db90567a0d3731b16e720ac6c1a6b3d7b5cb2549fb0d51c292d9ab672b479bda41a6c359ece8e161598741a6c03703f9293c1c9404cd5b49f8fa45cf3089e230a638892972104a7298a3ad5b927e71b8a3a825922ee43189eb8b8293173194250165270e4c80b3959286405a4fda05e1ac71cdd23eb530e49474fa33984e527d19a920d349fc527 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part261 : Excludes 0x40004000020800000000000000000000000 0x9c66ac90d84128100153012200201041040 :=
  finishCode 143 0x3f90a4191236900378305751900f7a026732a4ad67a9417b4c38b38eacf56a6c83a09ed925e7134a0a7fe593a024e3b179dd0471ab72325ccad2148cad4d06b3994e2647d9c92f6d58d810ded2b53257ba82f95403ded398e5623d8e36f6969cc4ff38d94761048200781606c0fd2f8378b4107e3072d45056835395b56e58ed18383aa004fd73da5cc693f7b8ce5f41db60b4318f5386e2f6f83fa0845be93f35bc41f405bda585f390dab6f69617cf717b4905d076e435b1507b4c13b57c8ed4fbeb3b1ac9c74de6e8311e697abe6415a015a933db51c2a0759d97e5b06f127eb518576d4916fa32659db99560ee416b1cb6378a80fe6623b56ce3a72b741e071082e83b940eb3b8272c317329ca63f7a0ee7413b3460d676c19405b90dcca801235cb51721b9960fe5f991e64177112441ab56e623a3cd832a4950da0ad85f41dc38a8f3308b11e6adb17d1e6d83e0f0204616f9045306d102294193f21e74f9ca3527ad0770f3a4fd20e941691c8394c1e70e48b7ce5323d4e1e94137fcf654a0a93d012a6079d58394ce4151aa90ce5300960d6b68c63c10814245e71cad01741d4a4ec47611017033c5e69f589ea92b173c2f3840e05818931c74de6b513f4b06638e9bcdac3356e0ea9f538ea7d66adba106370c8420d2107c7733da5cca92b59ea5041a718398923817b4a4bd78497c5f9593c92b8c1b06525ec5f069c41f927f3906306f691f4a0241a6b3b9ed2b33289b68d23707298a3a0d35e19072fc93f394b56ca1261158dce4159eb97e631ed3238519212540f9c4d27e811697cf691f89c76 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part263 : Excludes 0x40004000000840000000000000000000000 0xac468cd04b430a000101492048200800042 :=
  finishCode 157 0x440fe428f83c8da3a02f317cac0a072e3cd5b485932d27b1c4cde7149dac5e1b86adac10823ee366c1fd1925f97b4a50cc3ab255a897e649da08c13a0eaf6d3dfb1351f6e83d86623a38cf7f2325eda7df7b0c7df3799875a0581e06e0e3a4117b0d183617c1a56a24a18fd6f65268c6f76b3a4edecb3124822f61617ad468c1a08560741ed32d448327f99262d4d49db53d077460c832f61741ac208a0be068a084783460cde6da3185138a4f1838e3b356db4741484916a33da53e6713380a47525e8e03068c0834c77292b59eb78e41919318373287bded3060588ed24000d3624ce676ad9bce0ea3db389b56e7b4ca0d2f3b56c3de713691ab6de460e62da3542e27010f7c1d6379c1a68c1ad45aced5ba0c841ac7c0a4f304e3061df30e907dc4741a05001924739edac198c08ee525eb11a306b077b4c0d348ea4bd180efcb510efd1839256b3d4a0ac9e8c1949c832c6317e293877d637399ce260d36e0193149c1a6821fae61f9c143b736106260a835871d87e2e55400a045604a1cb3d3f89816307202d485e15f32835076d5b521b16cc0af71967a0d39ed2da348a8034d20600b173da4b8ee5562bac46250a0bded318172ac606417b956303207cb5ef69588c6067b48e4ce26a078daf281ce3a0d3511b86adc52741d98766ad94266e1f080128381b448fb18d220560f7949cf449dcd35729c7a9265c60e1e48b6dab7132da6693b6b3a304cb841276d4f9ab680116dcd5b0abcd5b69a949da9ad035907596a60c97b4c929265bdae26587be0ea713069cd5b293b68bc07be0eb3125ab69ff90166f360cb17dab734880169ac1ef34ab94dcaa71d250c82f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part265 : Excludes 0x40004000000800080000000000000000000 0x8c468cdc4a4148410109012101200120042 :=
  finishCode 121 0x210851b0631d4511a049fba071b71190068c1d6415b98439282b85be1c991c641f722c1db83ac1db691a05b07831fc4e027372e4c7f128e834e497c1ef265bda54027f1641d054149328bce562f33e09fc5b4680f9f41fd42ab270e48be4a4f07f91f6a156a4b04e3fdb53c6d2d4954037b1c3d8a2da1f7e2bfc1fd42ac1d2cb899ca2707f80c2e616a7b4051d8e52f6b8ffe815681a44d0e52e21cae041edce45405834e722c60e4a0a38c83e1e781a7103a0f8072564f0c14fe31819ed2a0759ead4deda6ff0f7cd6762d86f5ed26056b3c1c937fc18d49905707560e8c143de8259f07f1b4830e3714745f2305610e530bcdcc32015ed24796a4b4d5a03e0e37105cb4261d7229c6e20ba4364fca06e0ea8050bac91f38697e4e5292f83dee5f631d4511c449fba081181a61db967b250483f06320d0204589b034d67a1c960ec941837834e069ce8147658e9f04832b539402b3b404ac9ca4eb3368160641c40e4be00c96a4cb5340097065a9c60ded2801967a92f4901a72095016191a0ea00b412ad4e8c1bda41a2c2b9ed318320f834db4831a40f7834e0efb136001ac9c39292f30ea9266a3c1eda9281b179834c3b6d8240b024fd077067437a83b93ea9232082b8c1d07f30ea47e03181ad02ad67986b07583ac37369796f502a83b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part268 : Excludes 0x40004200000800000000200000000000000 0xaf6e9cd0ced3484b3101056000210481040 :=
  finishCode 33 0x418d0320da3a1103c88e0be527b2d4da6b0b0c3925099a9307250425274ecca3d5a9be0d83a0a358e1a809394b52502307f9192af90479f7cc3aa078e6ee6130eb59e730a92560f1ca482e6ff881b464060a91da0e2a13161a90d49ea43833aa0d4f5ac1c82f1bcd45ea354a1cd4d83a9c4db861146b28bd286815179b0c649eb534e2680537bc713 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part269 : Excludes 0x40004000000800000000200000000000000 0x8e468e90cac148090101052000200480040 :=
  finishCode 131 0xd82887e34093f5320c38dbe0e618a4e8116d118379ca4f837c09d730a89da432cedcc2e43730ca4f6adc08dc3208118b4ab53483a8f5ab6a4f7c1ccb41fd1eb07548bb91e5a9aa05099ab6b53410ac9e0f7c18f82c9e408ad4c83eb479cbae6547aa8366adbf8da3e0de399e2e4b56c83e1db733d0756ada044de7293c1a6f81bce3ffa4ed45f2f10752eacd5b30ea086691b46f1a074210067b08c81c6d49f241c182f6b8e56b33599c81116fbe0917818251d161cb27169ad4c3b7031c3b7079c1a6bc408f818764088b860ea5274614851ea93d6a7356d25f0759ab6b33464b11d88f232544ef817045e72044e27072549f2084a4ec2341083a071b2e0d075408bdc63efb5360ea8c12f64ecbd4dab70737b0a0960ea93b404cd5b8420ea93b40ac9d916cbd8483e81595083fc4954faa3ec7522bb408bd8659d8b7df06d102230589ea61d9ace58293e5069c4d25ec2f6adaccd406adc2c3527827523b1bfe10831a0641c4408b92e5a99cdc19a1e7395c9f991c241f5a99c6c1a7132c83e1e77b7cc3f628834d6a70c143920d36d1c47c2246420c4fccf6f412c1d4fde7291829875fc4605e6e459a92a01380a926731949dac71b24a4e2c958dc7290ed876e0f3c94196a651d841a061146b0ed563a70d048905ce52b02026838ac1cfbe6b7592b56da9f0739192e656ada8d5cc294395f2e6759dc1d500a0919ab6089 (by decide +kernel)

private theorem part267 : Excludes 0x40004000000800000000200000000000000 0x8e468c90cac148090101052000200480040 :=
  splitAt 1 117 0x8e468c90cac148090101052000200480040 part269 part268 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part271 : Excludes 0x40004001000800000000000400000000000 0x9e66ac9a6a45496ea101a12280300080840 :=
  finishCode 17 0x184891fc8316c8403df1cad49f356cbb61ef1b9cb1b27a8be460ac199a8e7eb39b8bcda0246cf6930e9face6e5c7949e7eb173c1e77c03cf0be52833da43ce701 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part273 : Excludes 0x40004200000800000000000400000000000 0xad6e9cd15a53c96a3101216080210000842 :=
  finishCode 31 0xd2428c241872b6d10371044586b1b5a9ba03a9618c80b623c1d6730a9267228bcdab6f83682f9905e6f3293ac0d4f93b2181722b025ace61d615c129410b9858129f5514c0c70de9bcdd08319020cac7615a831ce2680b8e270724a4e3e98c1c2b528ebe0e830be4f6a93d2869170e49065b40deb56e30eac44c3b2c464a0a86d6a21bd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part275 : Excludes 0x40004000008800000000000400000000000 0x8c5e9eb14e71c92901112120a0200044c40 :=
  finishCode 49 0x210851a4681bc740e567376adc1e762fb56e83fba1063e0dc1045002943a0ea1c983ac2497b4854dab7022d4e6189bccdef0754059c4e6238ee4b82291945e3e97b4b9145ced5b6d0de741d63063056adac6d6a6e61837ad5b831f00f7c305621c2c38c18f6d8871a5c5226f36adb41103a0bc106548707243df1a6e8c191d563680962186f4c0a91787526ff161c9438c187bdf06b0fd71c4c1a641f6aacc5f2e0b4853ea7eb20c9c4e069c28d2248da202c1a707bd3eb06f5076c4793da1c9069a45c3df245d887131c1320d3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part276 : Excludes 0x40004000000800000000000400000000000 0x8c468e914ac149280101212080200000840 :=
  finishCode 131 0x9042093f7c1d0641ac8810230036841f5b060af6983ceaf949e8b9c38b079decf0719676af9711b46adc1e717c833de06adc2df1cdce6f415acedcab3dad05ea3d15db681ef947a8fb9acec1949da0bde0494c3d120c8b5660c8ec588e305712046d101651d902a3050efc1d638d9cae48b970459ad399ed651d15da45ded272b591b48509ea943906a917182877e3efc1fde0581ab62df966661d1cdc3836159a5e7b49f7d6a30a3da5603efc7376b3a4c4f671a5ce6e90d1bccb1b2e08b7da46f20459dc09d6ad879c5be2cd81a6d0290b1b96a66a38752b05464b56c957310cdd28c96ada0adab72cce14711b47c10161ef514c929527cd4d83aa8a5ab68359076f8356e48bb51e527b0645a609d6ad834e169be106420e8378983c0811881a020fc28dc1c6e0eb049c9a307f6adb4ece56917464ce653f5ad4e83aa02e380c1d56a73995076737494c7ff38dc40fe2d841f3ffc7370e2cb3b49db70d0303e39ba45c1a291781a718193e68e11669cde408cf23787fb9eded5b83f9f7ce561df6d060b149dab720ae0eae616a693063ef8304e6f0a230e53943707541d8c1522ee230be169a0ec60a81b471cb276178b4dab60d385a6f02f00d39ab672b96a20d3067c6c94948bce14811b46f190395879d44f293c747289e527b7883b8e0272b6adc83540d834e3e7acece562cd81a62d3 (by decide +kernel)

private theorem part274 : Excludes 0x40004000000800000000000400000000000 0x8c468e914a4149280101212080200000840 :=
  splitAt 1 99 0x8c468e914a4149280101212080200000840 part276 part275 (by decide +kernel)

private theorem part272 : Excludes 0x40004000000800000000000400000000000 0x8c468c914a4149280101212080200000840 :=
  splitAt 1 117 0x8c468c914a4149280101212080200000840 part274 part273 (by decide +kernel)

private theorem part270 : Excludes 0x40004000000800000000000000000000000 0x8c468c904a4148080101212000200000040 :=
  splitAt 5542 108 0x8c468c904a4149280101212080200000840 part272 part271 (by decide +kernel)

private theorem part266 : Excludes 0x40004000000800000000000000000000000 0x8c468c904a4148080101012000200000040 :=
  splitAt 1 57 0x8c468c904a4148080101012000200000040 part270 part267 (by decide +kernel)

private theorem part264 : Excludes 0x40004000000800000000000000000000000 0x8c468c904a4148000101012000200000040 :=
  splitAt 1 79 0x8c468c904a4148000101012000200000040 part266 part265 (by decide +kernel)

private theorem part262 : Excludes 0x40004000000800000000000000000000000 0x8c468c904a4108000101012000200000040 :=
  splitAt 1 90 0x8c468c904a4108000101012000200000040 part264 part263 (by decide +kernel)

private theorem part260 : Excludes 0x40004000000800000000000000000000000 0x8c468c90484108000101012000200000040 :=
  splitAt 1 101 0x8c468c90484108000101012000200000040 part262 part261 (by decide +kernel)

private theorem part258 : Excludes 0x40004000000800000000000000000000000 0x8c460c90484108000101012000200000040 :=
  splitAt 1 123 0x8c460c90484108000101012000200000040 part260 part259 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part279 : Excludes 0x50004000008000000000000000000000000 0xaef638914e1908010015280020000040000 :=
  finishCode 141 0x3d89e2d05c370b4d691905014c28a9405ed33495a9b0776b385fd262943246c1c9415ce475a0a4c56865156814c72fcb476979bc52627370f7d069395a056412a98e4250dac741edb1ba51f61ef72eb16e2e5c1a43de8fb826a4899ed25997b6b9751f61ef741b47b4d06972f9fd43de6ed725cc5b593cf775a99ea6306917834b16d286f1d80f7b92e62dbda4e1eaff523ce6f6b1b974927359d8b671739992ae2e5b04c3ded63a8da3a01ef5d0a3f305ce66bc147ded7398d3eed67621b56c0c7359dcc24ed9ab651f581106412040dce6362393b47928018dfed4d6916571c7585e80b617cc2348ec14067219faca03390cfb6c17837294372fc5cb83bb59d05713b582ec83686ff9abab275a99c94a3eb0305e6238724b82d596b3942e378c7370dcce6b59e9beca3ed6368ea348de392e06987bdd0617c51f399c1de6aec1d4dd2b4741aa0adcb3356d2864ab384a08ac3a0d01c85637356d68ec1da0ea80b6acb56e1a9b564dd2b47725ce5350ea7856a6d5b6adce6b28faf0b0356d287291e0eee4b40dcc5b505a91e0d3460c70ee5f15fb68c5b967ae6b28fac08224ed01724c425741ee0d23d16aecf69692821c336e2358fe368d207bda058dcd5b5a3947ca2b30d5cd7356d6a6c1d384ac0c820962768725a9ed674611930295886c5b412932e83d9cad82683b6adc4ed83ab48a0994620d362dcb5369f9bfd8469104b359d41283b28fad02db93da6ff735c1318a16f690e4c6ff641c8530a025151e8c91f8349c360d31cace1b3995076f691ed9405a05301a734bd23e5917b49c6ce520d388c2e4341aa02ce56d5b922ed49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part281 : Excludes 0x40084000008000000000000000000000000 0xbd571bb04c3908014811200420000040000 :=
  finishCode 73 0x831d8651ac5914c680bf661f5d1ed32d1d6af394ce12f69384ce6f68150641a4b3da4a3e5011ec98adc86e1ccb41ece560d138eca1d523ad0564334ece564d18e12b27069bda61e5a32568282b315ac0d018a5a472ec709522834569b392dabae5d384cb418a2ab4d641b0580f93147dcbeb273029bb5ed23f15a1108c1cf69730942d69ab53941a39b730b98d40eb539cd680b37fc7296d1185a3820672fb16ded6b3d38ea50da431cad67a9f79826d5538e9cad606c1ec1f8947e593bda4e2e6118a3ef69732c51f3949c768c1a7ddccaa47285947da064160523c51f1f8a8c6522947cd2f3da548eb4d59e824d262b4758034b399d2764d1384c1de72aa43569a4d1641681f4c50128ab6880b8e4a80ba0d30a2d0ec2d5e51aad34e36931969ad3b9cde709503c1a5ed334bd02a0d3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part283 : Excludes 0x40004000108000000000000000000000000 0xbc5e38b2ce1c0c010691208020210840000 :=
  finishCode 51 0x1f07621464060ab60bcded33964a2a7015a6ce67069aa80d33f5cd493f5cb4d831604a082e62958bc70983fcc4358ac1dd1ea613069c62b20bb7051581a6e419a92709390bd9062d3669f979d2521ef20b970d299aba72f733ad35a7312ad20ad593fb9c25906e20ef34fded292927194549573da5ab2d493fbb164dc2f7b9be4949fddabb16cc0e29297b4a88e82087094f204390979e1e1a0ecbc720ae61587be4a0ad5ce429e2d1022d363072cb5aba1ef500b83119e30208f6ac82858873994e02d29a3061ef6ae979e3072cb43deaff83deb4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part285 : Excludes 0x40004008008000000000000000000000000 0x9e5e98d17d1809210031240060040040000 :=
  finishCode 31 0x1f0841d0550822da291439323e5ab672150ebda4a3e5c1943ad5d7b48fa4ddb1c5c7d2da2d1e5a68c14a3e82b82321bd62098adab6a476e0fd33105ab61c9522947dab7238569a7db5a99c5c5e6e82b0da290733491636b47497ca2f732cd5b271ad363ed93b588e7215c1687603825c1962ea4989dad5b94933575ea6d5b7b4cd5d58bad1ce4ad5b59ecc13731b49569ae6b6ada06c9c6d5d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part287 : Excludes 0x40004000008010000000000000000000000 0x9c5e98bc7c188a0300112600248000c0080 :=
  finishCode 81 0x421063e0e8390f6920b90650370c1560aa0b28f94066b1b90c8408821404a3e8059a4ac136aea91d0773575462d5b79174182ad3640ba325abab5369fad36518ca4589148ad2196a6d3b9cc3079d02eca278b41b8b4d3f21440bbb0c236872b064c1e7617ce47387ca2f0f3b91d88f2924dcac5f623c0691c1ac6d65a0cb85019334943ced5b1e1c0d362fb0be14531d82cac4ed4648afce1e737471abb2d4c57ea498e42d597b4cb277239cad1c065cb05271975d6a6b2d81967e3a0817390ca2f6ad832dcbf3da43ded5b8c1c60e1a687bdab6b05065c29021f01e76adce637b2ce5f1a59c7562ec2b276b56e731b10ce3ab2d968e0d33f09da6e5941a1e740b879e6adc08c8238e692bd8585f1836ad8e6ce3b077280947e14069ca0b7b4b56dac27296a3ca0b7b4897d076d2f069a05584069a90e394a90e2bca875ed2ec368f820ae58a947d0772cb43de0d3595ca31518c1ef (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part288 : Excludes 0x40004000008000000000000000000000000 0x9c5e18985c1818010011200020000040000 :=
  finishCode 145 0x1404f1052b420ddb8411f0271c28bc2a039b8dca8c9482ad35286b43523bb0b4d580d07b7248ed4e360cb9ab6e678e52b4d4a1832e5229b961cd8f2d69aec13b454b1c34afb306569ad67065bd9075969b1835229cbd6ae1ef20bbb03059cbae453949cad701fccc313edcd5d0969a6404a6e5741f0831e420f9c260f7b92ce6651f948f183065d1819edae4b737b56c1a6b1b857ad5b6d1d06c1ec068b2041f5a3d069271a50567b23d5a5b06d8e1a4e364035b07bd23a7334a0947dc4609cb1b57fa055076e499ecee6583d9c6e24609c72b6ad87bc60ad3f8e6e1e75a1f05519020fcd67692938ca170834a6723c60c82ea0b3949cad48b2c5d48f08359e730984505672b0d6c1bd276cf675248115c92e650e4b985ab72787e3d88275a1905a6c48f84190a187c8333da4c0a93b1829bee7b497066b3947ce2eb0196aed67392b9260de9ecc146d356a7b490842871b8e6e6c796ae3b37b49fadcab0035ab6a495ab8e4e741f0830e43460d60ac1128fa91c832d5b8e4ad5b9a6ad4f392c60e69a9815a670a0c165239cdce1a3f99a6651f7c1905e214790e37105c5b63055a0e37147d69b12316e732a87c83293b28fce6f5a6ce6f302bda47f262920cc51f268cb475a68c15d05a6b88d5b392b53e720a884e3b2475a6b3dc5cdef832106388bc358e818aca3f359d462c3720f947e6b3a8c5cca2e7182cc1328f98148330c14c3e51f8832d5b9ed270d28fc490634e6309ac6d68e305491ed30f2ce3681b069cb17948aa4774224384c1ef59e9c95c47b4cb177b8b53c3ce8439966ad918c9a291d9a8eb17691ab71ca5ace1e77a9cd6758b87bdccad5b (by decide +kernel)

private theorem part286 : Excludes 0x40004000008000000000000000000000000 0x9c5e18985c1808010011200020000040000 :=
  splitAt 1 88 0x9c5e18985c1808010011200020000040000 part288 part287 (by decide +kernel)

private theorem part284 : Excludes 0x40004000008000000000000000000000000 0x9c5e18905c1808010011200020000040000 :=
  splitAt 1 111 0x9c5e18905c1808010011200020000040000 part286 part285 (by decide +kernel)

private theorem part282 : Excludes 0x40004000008000000000000000000000000 0x9c5e18904c1808010011200020000040000 :=
  splitAt 1 104 0x9c5e18904c1808010011200020000040000 part284 part283 (by decide +kernel)

private theorem part280 : Excludes 0x40004000008000000000000000000000000 0x9c5618904c1808010011200020000040000 :=
  splitAt 1 127 0x9c5618904c1808010011200020000040000 part282 part281 (by decide +kernel)

private theorem part278 : Excludes 0x40004000008000000000000000000000000 0x8c5618904c1808010011200020000040000 :=
  splitAt 1 136 0x8c5618904c1808010011200020000040000 part280 part279 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part290 : Excludes 0x40014000000000000000000000000000000 0x8cceb894c88aa8000000000000000000000 :=
  finishCode 121 0x6f22053033b24fc3be1ef1f38fbe007107eeb4d927e0d30f7acf65a6a0e568e72f711440ebc08cc1cae3d5b59ded2b4d41d8b7d04268acee6adb10cff6d25969ad5b60ec4d1730b56d69a72b5a6c72b541a4324ace56da25062edac9d90471c7c77b682dd1931f1dc45a03de3df85bec1d9826c396ad8f7d3c5107be733836e93f62169a1c98e6ea3d8bceb1716fcb43a89040093f741582e0c8352719c84e6694230725838c919271979e2f3c4e36adad1d18582cf695a8938dab72cf5a4a3db60127b138ded20af41582f5ed720ad545e09dacc34963eda06c1720bd7b7cb4d0d7a325a4ad5b392cf515a1ad4c7b6b4d988e5e352782f4e66d25461546d09dacc28a45871c856a7293d2568058de68828a4bc7283569ad4d93b2af159db68cc20ee4a087056a67215a9cd5b9a7ea0d41da925781d1b46ad988cc27fe004a0367178c95e7255a9cd4305ec8c9895ed436aab9956a6e8400ac20d641d9c84e667259a8682b817af6d965ae6b1cfc1dda86d2248c2330d3b986ad5540da0edaab172cde67fb57fc805379b0d6626b99da86835379bdb6374ba0cc278733623c835390a0d658da4bd6a72905e79ec2e4f6acb50d1c58bc367592b93c73f0772c160b460dccaaf9374ac968c0c60d984f0e6718380169f9524abe4dca1b369f9c860e741ad25e94193fe6e5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part292 : Excludes 0x40005000000000000000000000000000000 0x8e63ae904c880aa00000000000000000000 :=
  finishCode 147 0x110419123f8da3882f31828f6e40587bc9eb1cdcda271b6f1ac5b1641f38fbd463171d27e62b41aa43640aa8c594800c52b8278e424ed64b282d686b3b49fd07b580a3ecfcab4359dc71b5a8ac04bf2d538fcab4383d87163f29f85f954167728c56aedc399c2871f9540eb3b580c23d503c1ee1a8bdb5cceb3b581c87b4cb512fccb4d41dca357b09ca5ed2ca24fdccf3104de661f834cf69592ad5d946b1906d106261f314b9be417a4fce66f67961e9a1fbe0e9ac94c268c34894340ac70d0e9bda6595c604e1293f394c7ef48f874df8691046410370719492f695058714c0a8159ed6697969ab1d394a4fce1a6057b4cb5130296861ed9235ed20b5164981578691905a0c0a61138dc1c55059ca54172c8a45819e81b4fcca1f067a055ed334e4ffe6ff49f981590407c6ff41fc1fe4fbad44d26b1572a9ffcdfede3483ef6d16827a879c38b1c6dcab28cd022b4228a81c6d6772d0d64b27e61bcb10527ef6593049fb046737bda5022f6789ea6bf58aa41d7049fad8da20c507ed438f6a90b49e8b9d6af3da545f2bfd6ae8117b4cfe2f0c23582f339bca1f522833c3b69e1c35ed32d4548e9432f3a47e3e5ac75692f696b1747409eb1c84e4a661ba67b4971c9eab415aba78233896ec1d5a1a4fd69ae618576a317b0c9e3735a015ed293f50ecc4972c93d569af69067c1db179b78d0358ba033ce6f206c3a681b8dc683b7e038b3da546a72949f9c3438b0f6ded22c91dfcb4d0e9a4c543b247d05693f6f1ac4f03de9059276b431efb48b230762e58afd06ad43902af6938ea8c5a9f34e498e93f7e1a44116840da82e39ba47ded281549fa47e7b4a0545b62db927e81541da47e7b49bfd27e2db9cd71fc543ec4941dbda4dd293f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part295 : Excludes 0x40204000000000001000000000000000000 0x9d471a99eaae08008200008002000408048 :=
  finishCode 37 0x7b20c741fc79083ee2204673796bd01ed4d314875db438dad366ad938d02272b17cad3605ca0454631c741763ef6d01a318ad81e82f1f8874d182f78fc522f303ce3ad61873707b464901e4f03a71234ce49dad466b3ac1d06ed4d9b471120b24a41960d30e5b201c58e1a4e341bc70d761a0640e1ab834ce05c98ae395c83749dc61349dcd4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part296 : Excludes 0x40204000000000000000000000000000000 0x9d471a914a8c08001000000000000000000 :=
  finishCode 125 0xa22d0d024fd905c1a4611740e4c0b505cba05c1414c3f1063c1bd740c5720848221c958035b3da4c52d5985824e3315c1bd1f8b48f6939bcd33414a8c548ed5b05e98ae3ef97047fe4117b200831fc182ce5f5a6bda561e8391668ffc832d230867b49cacb822cd6aac94348bad44b82839969a5c11668b367b4c5ef41c8b05ec6f20c1efc2cd20397065a6875e244a1c629179acce510a41d83ed3f173b20ec24ee17998aded30b049c6c35920ab4916097be00831fc6d0832407523ce6b3028c15053368dc3b0d62686290e9975e5a9b555cdec575a8a50e4610c4d1607b4cb25505ad44c0ab1b989a3c37b4cf698c0ac099aaa2c9735bda5416e5596a65cb5a8a50c3a672130ecc3f399874c2a72c756a2a1d523b56db46aec829069875dab70fbe7b498ac38ed5b6b20c7b1a0801b420fb7062b83a60cb0e3c931a306f695a6b0847e2b63883ef6d184628c93d061875d2572084c56b4d8c52f6989c6821395b88b4d9812a09069bd9e610ad34e3641f9c47622450fc9173e49cad0726133159cde1db97243960d3680bdf0fc5072b62e8905831ad3336dbd4c15e1cb732c7f73fbcf69494b201c58e1a4e31fca0e66d0fef3da52528390eb834d813359c72293b414b00f69581fc641052c0994628271fca09e182a87e48bb08548e3f1241813308569b205e306b53948e419 (by decide +kernel)

private theorem part294 : Excludes 0x40204000000000000000000000000000000 0x9d471a914a8c08000000000000000000000 :=
  splitAt 1 72 0x9d471a914a8c08000000000000000000000 part296 part295 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part298 : Excludes 0x40004040000000000000000000000000000 0x8ce71e98488848080808000000000000000 :=
  finishCode 63 0x1b04820049fb40fe3884195b03dec4d9ed2e450d8ad3562e3df280c93b604b15d62ec399ece9312f3ad0ce1a93b3914c5a6b4890d8e6ed439ed26ff48bcd3b395a989318c3e6ff38db70bc140522f27e58aec35412a45e4f5874c3a7315c3df107d886b0e0272b694cc1373194043dee6383df1f1c7be8215a6bf8b64403df791c4652000efad36268940502e837033c50131498ac2f714046c67eb8c19cad06e1e7479c7f7182901ca02b4d880e5c077ca03391ce56b4d60ccb170599cae20471c7f749da45d69a82720fa4c60ef940569ab620ee6948efdcc6501395871d8b72d34bf662b0e9b58fe400b6171c80ef20f9da8f0515ab6b4d182ad3641dc82717cc6292808f9d69b074cbf662b7f1073140569a2f9721ca493e49814e5270d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part300 : Excludes 0x40004004000000000000000000000000000 0x8c6319f0c8c808488008008000000000000 :=
  finishCode 151 0x3d9063f8de2d9100f7e006d082ed00c1548f205c3be839699cb4d0ef9fae5a698ad06eda2f01ef387d0732e3ad34a1307993eeb4d0e3a4fe721b925ab22df69210518cd3349f9cace0318398bec1949fad343de7b79a7f18362dbda43deb4d49fc41123b1083684176516361ef17cb54e6ada81d69aa07927f18a43bf282d6361ef3089fe6834b4e527ea490f7905d27f079c82eda24fe5ab94243deb4315cb972d35c861b16a6a4fd5ff41dded6b413dbb535acee676822476220314c41117cad0bc24fd69b2c6dab650984164341bcb9683f590e66b4d9cca7179ea2bc20fe58d942507f16ce6279c5ca12411408c83f208ad82f9170c58b41fa046524a4fd946d1bc79150397874ca1320bcc3f207d78613ca3139bad34a122c7969abc20fd022e6b943ed5b2fc98ace672d34de6c829893f981eb4138eacb505e83f395c70116fcda360c82f0a82c05090d8ca453979cae356a8c507f181927ed5b308a7de7b19c8507ee5f8c0cd593ffac1568e2df72fce655939424e3b350d41ae5f5239cadbc681406d102e839540e5714252831c4d2563c7471ce615809bdc78e70f382c1db751845103b6f6998aea1b83bb56cfee93f5abc7f70cea90d8aed82d365179c8587ec5769acb4d3fb9c04def0b9e284af0a8340ec1424c230635ab6d3938da0e4e56f63948a6e5699c1c506e8395b14c5d18b3184dac60a70df86bda7335351c2c591db97bcc266f38baad597b198ace02d49927f1224fdd864095b3495aba5a31fc9844c56a6399e580961d04e7eb394984d74694ce6361a968dabac35919230547035ef618fb68c962c9fdd06ec8353e3ed8fe63031f6e30312b469ad5b2d1872ce52de340ec25060a1a09dcca5a30e59ca527e72b6017041ba0e413341c51c2f71618979dccae6791c25e76b3b97e0e5a9893f9ac639f0df97bce03187e0d7b99589e93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part302 : Excludes 0x40004000200000000000000000000000000 0x8cf398d54c8818001600020001000000000 :=
  finishCode 115 0x842207f1bc760a26419203a903055a3c605592c93fa0f2b3341cb40da1045a9f2ced27eb53179ac3ca26b518fd2d67314af0b07941ad5b2e08b9cc5280f9ed2b3b541a06d1905907e2d6144d3c30fc82f397b0de41f95fe49fa855c7a19f59dbda5ac37fcd553089cbded27333d9cb25302bda564650a270a250e5f9cca91f4a1ad4672aa4fd67a5ef309c7ff724ce65510df73da523e943592b010a309d8427ff9ece94352493066a1c7ff7b4a90e3faacecc269431f8b20da1ffe5a6b025062629399a4ee5a8c9433ffa1893f3c1ac37da7ae7b4b57477eb1198b72d44e4ab0f7b4b56e50dc1fce666135a4bda5d06d1e4511ac37dad0e6acac6d28693f0f79c5d6860127ee6586d68e94a187247a27b39cbe5137b4a50e735b40bc3205137b4c9e116d8add05e1c153184323253c2f696a1a50d3c335653c4a1c3df5a6b99661c9ffd23e831604c1ef5c0a269e35893b4a1ad0e418a84e5a6b8e5c7b39adeda8315a6cb8308a632093b68107f34fc57e1c96a1cc21613a07dacec4d98b6d433ffb406c07258bf24fd82e3b562dcd5372480a683480c5a72d33610cd4f6b3872590751a9e9059686f691efcd299a5eb4d1efb1360f7944d3c49fb29102d34def209c75b399cb6a7b74a19cbc7be839a20309c8290d2c199 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part305 : Excludes 0x40004002010000000000000000000000000 0x8e631cdc68b888164026801088040200000 :=
  finishCode 97 0x842207f20c7b2006a1cb1d8c1a0550362b562b906480ed63303ef6c15016fa88540b1dabb2d35812f691cdc7ab58eb575abb2d35812f6f2d4b4a67b4aa04ab9ac2a33471ce47255a82d676a8398d6a32bc5ac2189395ad3649fc72b723b98da0531cc720e4dfe729481ed31cad27e8395410772095cc68375789cae307282e0f683b59dbda65abb90522e825309c48ca2c0d0250d05341a5ab670d40acd0356e6b09c3502b1c766add06940b9c35a0621a5b41a5aaab2b4fba8cce3a72b6c1745305bed2d9a866136ada81d44405cd5500eb03d48eb1d6ada096696b4a55453148e931960e9f74a1ad36583ad36722b4b48c32c75a5a9f758122f2d4584f24355f27017b1683ffcd633948f7c5be9e1f83df4a1c3bf498c8c356d02b20960d31ffd872d03105a39cca8354059ca4e568a058e7a8b915016d29386ad5e2559705c8a93f6b1c917412b41102c0b220a506e8359076a47471a9163f13c5a6cb4340aa05d417356d602a4350ea0551c730bd02a9e0b4e5a68f7d648c1ca0b523a09548b2096 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part307 : Excludes 0x40004002000040000000000000000000000 0x8e7398d4699a08124802481048020800400 :=
  finishCode 87 0x6b178511fc6adc40de41862b906e3e7203b4083b902e837530ff71bdd2866f793c7075599c48ca2c8c218ad6048bc3e95a8a50cdef278d0766e998b65d583bacad64b245cdee629504ca0787d24115b1ed3291d07e3df498cca230b03da67258fa520ab514a1b16e41ab92e519a81c16eaff9ccea4783bbf9104189e105da005bca311f3a0e4c532cacdee62b941ad01f882938eca3140ba91e402a986f79ec2a355179fde60ea38e0d26bd595ad8c13923e83f6a78f7da9f41dd1aec2149882e59488016eb41941262b523ca094989fbe834a91ce3b103f9061bde410c60d22e41120fb407f7617d07515f9c7506eb02cae604bda5a9ee4137bcb2b581437399d05eb0737b8fa4cc5a0c83f6acb4b521a6f7530d771c75486d2d15fbda649dc2bf40fba11023267b6a02d4863f120cac09e2a093b405cd4d4988f45263359d82ec492e3c91f7b4b53c7a2f6da3061ab4114628297b4c83b5058186834a05ded307b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part308 : Excludes 0x40004002000000000000000000000000000 0x8e6318d4699848124002001000000000000 :=
  finishCode 83 0x44050b841fc801bc6813c7b106e83949dcb515a6901dccb34cce36f6418e478832605414901d5049fcb253959c36730a765a9e9d9927e3f9414b59d3c203a45e583ad3527707593b2d4f6b3a055a05c169b359d89ed334a1a82437a3e9761942089845a673534c3e8f395e27e97a9b165823310569b062d36578987d676629057c9d937bad46244c178620c0a611530392b4d8daab1d8fa341c5acea43386b4cdac5318b3187c7deb82c7659dbda6395a4fdc87391dcc293f58eacec7df3574392629410cf691638fbc5bed0360c40fa4c0b1cac5bf2c1e62cb924c56917966693b76130620c229c07253b302be0d21a541ab4ce415b56d27e93f906f245e5a6b56d06ec4340ec2981c941fce63498a50ce527e0f44e5680b804a7a949fc1de7b4bd8cb82d3392622df49da79000696479a50c7af353c56a1a5a0d6f624fe10721ca0962ba8267218f05ede9d91e0ce43 (by decide +kernel)

private theorem part306 : Excludes 0x40004002000000000000000000000000000 0x8e6318d4699808124002001000000000000 :=
  splitAt 1 90 0x8e6318d4699808124002001000000000000 part308 part307 (by decide +kernel)

private theorem part304 : Excludes 0x40004002000000000000000000000000000 0x8e6318d4689808124002001000000000000 :=
  splitAt 1 100 0x8e6318d4689808124002001000000000000 part306 part305 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part309 : Excludes 0x40004000000000000000000000000000000 0x8c6318d6688808000000000000000000000 :=
  finishCode 71 0x681d428e949dac76220068bd8b3b87ce2df49f9cac83ef518b1ed5d4f59c35ede72b182a4160db8f7ce1afe418ba0f9d1c0e5b996598a01d06e902c6e2edb0bded29eb9cce9eb906e8390e5c9290edb99658d9ffc3a6f23f1002d0ec24fce57202d636305394a50e4fbad45ed28c1065ed32d453ef1fee58eb0fd016b5338ea4fe00414c83920c980c579872f691edaceda8f0b1dac29f73e3c41949fc40839860a4197e15059ec7b74fb9c3ce6e2ad8b2e5cb59e9ffd23e96132e48fa7dce127ff48fc5cb7239c25907f0a2aea2d82f30edad464188f4c5cef6b94928117b4b575666e80bcd5040786fe4189a8e41ab56d86b0f7ce4341ace66fe3d8960fbc3b681587ae7ff5a189b34a569ad635e189b058cfaae396adb4a63dbbb01bf860a0d341297be49fbd8c3967f7470a7ad2523cb83a60d3 (by decide +kernel)

private theorem part303 : Excludes 0x40004000000000000000000000000000000 0x8c6318d4688808000000000000000000000 :=
  splitAt 1 109 0x8c6318d4688808000000000000000000000 part309 part304 (by decide +kernel)

private theorem part301 : Excludes 0x40004000000000000000000000000000000 0x8c6318d4488808000000000000000000000 :=
  splitAt 1 105 0x8c6318d4488808000000000000000000000 part303 part302 (by decide +kernel)

private theorem part299 : Excludes 0x40004000000000000000000000000000000 0x8c6318d0488808000000000000000000000 :=
  splitAt 1 110 0x8c6318d0488808000000000000000000000 part301 part300 (by decide +kernel)

private theorem part297 : Excludes 0x40004000000000000000000000000000000 0x8c631890488808000000000000000000000 :=
  splitAt 1 114 0x8c631890488808000000000000000000000 part299 part298 (by decide +kernel)

private theorem part293 : Excludes 0x40004000000000000000000000000000000 0x8c431890488808000000000000000000000 :=
  splitAt 1 129 0x8c431890488808000000000000000000000 part297 part294 (by decide +kernel)

private theorem part291 : Excludes 0x40004000000000000000000000000000000 0x8c430890488808000000000000000000000 :=
  splitAt 1 120 0x8c430890488808000000000000000000000 part293 part292 (by decide +kernel)

private theorem part289 : Excludes 0x40004000000000000000000000000000000 0x8c420890488808000000000000000000000 :=
  splitAt 1 124 0x8c420890488808000000000000000000000 part291 part290 (by decide +kernel)

private theorem part277 : Excludes 0x40004000000000000000000000000000000 0x8c420890480808000000000000000000000 :=
  splitAt 1 99 0x8c420890480808000000000000000000000 part289 part278 (by decide +kernel)

private theorem part257 : Excludes 0x40004000000000000000000000000000000 0x8c420890480008000000000000000000000 :=
  splitAt 1 95 0x8c420890480008000000000000000000000 part277 part258 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part313 : Excludes 0x50000202000000000000000000000000000 0xafe759f4465280529010101000000000000 :=
  finishCode 27 0x3b1003d8f23600ef5303cabc1ffd05e90d983a7f5626a06d287202ce031704feb075263ad345d31c047bf1cad63eb4f1749c3c3ca1859a5f0753eab58ce021e564154680a160539ed60013729fbd3eab4d7228755a5f207d0563cd906a1d568130440e531839ab63897aaa0d5c8a2cb5a6a0d64158b2e379bdbdaba9f53f7b4be5a6c1d502a7ff285c0ef (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part315 : Excludes 0x50020200000000000000000000000000000 0xaff17cd6805290101000000000000000000 :=
  finishCode 79 0x741fc6819c55158311ad3e399986598586c4eb0f293ae6adb56e0f28f44c3262f661b03069c954770795287356e382a78ce2a8f6182d3d71ffd1da94316dad347be8ed9a5e7f56b18b6ce2734f569b2414e0a9437b18c6418732ce4e667ff40fa70942d084350780ef60d70df431a7cb86fb1873facc559a7ed2f61fcc391a5c1acfeb0759a5e7e58c3c1ae697a5082b923e7096adc82b4a034b34bd02a3d516dc815697b40d42f81e5430e5e0b79abeb39405ac7d27724a63899c966adcb4d389b30d22b0c235082541aad1e275acd45b63df949eb3d5a5a18e3d87aab4b5a7a8561eaa18c82cd64a18b6d69ec634f63efc1dd69ac276a28f7d2532d34f6ed45695c8e94f169f0778be67f51efb15e83b862587a7f5511cd728f47bf07b48993adab6905969a4eb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part316 : Excludes 0x50000200000000000000000000000000000 0xafe358d6005280001000000000000000000 :=
  finishCode 81 0x1a46818c5c0a3a5277f03cb0ba4c5e929a30e2e90f2b91e83b879437e62376200077c1e564096f34f4752b2716da06c3aa51f6f1eef24d5036b536ad9ca560b302e30eb27379a054a3f2d0be3d85154f18c5a6bf8aa0f7d06b27ada56d63077976c77b0f5501720acffe82b902b002c80ef3ddcc357b9cd63a0eabc358c37f34bd02b0699a5ef734f19c0437f003d8fe2780ef410cb4d3e5c83183aa45e5a69c4d34305a055a5f35246bf3dbda6a80b6a6a47d8aafc2056629a0adee741d569b002b00ef5e0e26c3d91d2c0b40a8efdab6d5793c680b6adccc1b8be356da9f1c04da2e673dba0547be5db902ad2b8fea5bd16da0d437f27ada8af23f8d603bd7c640e129e25872159cc82f5a6cd29907e82161ec60b3118746305a0bd0426238c5ed02f89118e121e5174932e2eeace43cab4d9ab2c0d40fb50d21a9430f2c513 (by decide +kernel)

private theorem part314 : Excludes 0x50000200000000000000000000000000000 0xafe158d6005280001000000000000000000 :=
  splitAt 1 125 0xafe158d6005280001000000000000000000 part316 part315 (by decide +kernel)

private theorem part312 : Excludes 0x50000200000000000000000000000000000 0xafe158d4005280001000000000000000000 :=
  splitAt 1 109 0xafe158d4005280001000000000000000000 part314 part313 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part319 : Excludes 0x51080000000000000000000000000000000 0xaef7ffb8840000000000000000000000000 :=
  finishCode 25 0x721b406eab0ca1cbc3a72d3526f288c21c965a68f6ca13356d657340c0249569f238528eb5758fca45725a3b683a931db049127eda074e5a69fed0363db724c17b83ab56cb8eb4d40dad3648bac145d29e171d647140569ab238a0283b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part320 : Excludes 0x51000000000000000000000000000000000 0xaebeea90000000000000000000000000000 :=
  finishCode 145 0x1c46f1ac7803deec3700e3073a4fe174c1a683bb11d69a93f1efb70ca2d02e94f0a16a1f948a3df5a6a50a81b266978eb5acea4583dcb0d6a988fe6a9ac360eed2f586ca316a7a51c7bf042d0a09a306b1f6ad86e4a02883db63dba3bcc02d5b551ebf41dd3ee9357b2b97e479b003ad948e2d30dca7868c18f7dab6a315a5bd8d27eb6410882d365a79bdd8beb1f480a494e80bfcb4b1ef9bdd14470cc178c185dc2feae172c98f2c7c97e4c7963e8e160ba703df585cd630d8acd45a724fc363090daa617f2e59bdd226dc2c8ec2088355c1056c5f91fe94749f98051e7310d27eb0d49ba3fe300a49527ea62d8b824fc7be7db98322e9729c59d37b9f6d94489b59e49aa87e0f693f3eda4a4def1f6d1e68f3926eb4d650c0291f85d29c171e2deabfc7bf07740ab05e49aad8ae1b2660cad3527e9014928f7d2032494dee93f470ca1f37ba44de0741b4071ab01c1928ee655989864c4ab62cc6317a87e522acc568e51382154498c7db523942d26a947541280e0c1de2e3a50c0fa48d5049236479b90d27f397e0f692948987066917c5d0a3e9a2b83db5a167b41ed2620a5523ca47969a1a9591cb3d5a7ad2e61186a437ab53904a2db41dace569ec139a661975a6a4d589ab3d289ace564411585a0c0262541da4fe83ba51d69b077928eaa2ce64a193d47b6941a9e46298bd28659992529138df648d49fa51d076a0b8b621c53129805e07c17c284839d62b147c37b2e0b4d927e619276c3db49fcf83480e7037ca018349adcb8ed5b5a68f7d27e50b312c943641a067184310c46afb944e72f593a4fe2cc9c9547ab4d276af8e4236e7b693b4e66b479abea2930cb97e5a3a8f5ab66197216030734e2693f9abf41cd4265b5305b56ce2660b8c5eb4d (by decide +kernel)

private theorem part318 : Excludes 0x51000000000000000000000000000000000 0xaeb6ea90000000000000000000000000000 :=
  splitAt 1 127 0xaeb6ea90000000000000000000000000000 part320 part319 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part323 : Excludes 0x500a0000000000000000000000000000000 0xaff5dffa855000000000000000000000000 :=
  finishCode 47 0x6e1b00f2c0d93810c4516af24c5076b355a5ab0f21ea657fad0d02a83b4a1ed739ad69a5dd498ac7e05bac7e561e462ac5dd4058b1521a825056ca29275ac8e514ad351d2c62f8ba3c880b8e427250e7ab82c596821c7266cb4105ba93e59ca02d076b3998aaa4f41da02d8ab2c8dedab4149db515e4481283909fbe6b1a4fce4aae1fae58ab4ac39ef694c1a571fac5928ed695c7eb58a9c960e7b48d82bee595a4fc1762df571647071d64702ddccab0982c2e496adb54c162b4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part324 : Excludes 0x50080000000000000000000000000000000 0xafe35fb8040000000000000000000000000 :=
  finishCode 119 0x3c8f6390dc036e06eb40bc318da320509801045f0e26947948e71d905e2c9265cb4d1e89c85a472045abe2df6adcb2b5189cac5bebe348ac21892562bcd295239fadab2b4d417a51d4631c75042e63927e737387ac364179ffd22282f8e1eb41cae720b525ab6b4d6adcb4348c61cadcbf3d44e1a9f716fad3657bcb4d57bc71d641580d7cb4d4179bdce26da3481d387b7071969672562dcb4b3809ffe69ca4fcfd6b4d440e44f1a45a6b40a62c36418972ca0270d394b70a2245e410940501693f64104b245ce568214f5ce4972fa095cc6f67480c8211aba4dce567eb927e3bf969693f5f2006405d270d8a0293f8e1a70d8e52501611a45b11ff460e0ea93f3949c6e412c1d51feb0da0ea3d13facf695b149f0f6d27e82168102249b926ed2f97c6919048fc73741f8f6ca0291f85d280b835c6ed6a1a4fc5d2d0368a41cde41facc56a6c234872b922e93f5829ca560b16ad22eb238e1ef69582ac3647f9c3e0eb245dc86a1a0730c93f395949c3aa1e56a1c917415942ce020d540dc51549f9475a049faf87019cc2d5b7b49cac5d2b279ed270f41acf694a19405036fc370c80795c870a8d69eb2339b949cb8f04adea270d1749c8c22d3438f0b7ce1a73749fce6b83894251c32c3548e7a95abbdbd05e83f2849426 (by decide +kernel)

private theorem part322 : Excludes 0x50080000000000000000000000000000000 0xafe15fb8040000000000000000000000000 :=
  splitAt 1 125 0xafe15fb8040000000000000000000000000 part324 part323 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part327 : Excludes 0x50400000800000000000000000000000000 0xafbfcadc110011052820000040000000000 :=
  finishCode 97 0x3a0f03b0e23480e3621b06103b24c2414e3aa338bd2b534fac1d630ef673eab5267b4ad4d43b24fce1eb535b1845a5bda65239ea523e71d58fc905943ef676114c5c114494a50cb07287e0eab4f230ce4750faf093f8e1a2bd482a87c3473da43232c7c976b23584c2df5a9cf6969a97a43b2d2330d82581d950fca33610b82b4d9ed2617263ce6b5f143f28ccc331b8e722a4fd4667370eccd2368cc288d82e02df56128312a3ce3f8b154c1ab539caa5c77358dde838a87d48ab05317ad1ded32d4c7b6b82a860130cad1e3d9acd5ed2a1f59ecb357b4acf658f988d43e4e19ed2625504a91d7048fcb474a1989567b188d48e2df8c1b348ec2c8f236881b41d9c6e49f9fc4c2ed599612a1d3f8a68aa1c7543f291c57a00b8952e63584a4a528691f91d317a4c0271d55169b188d43ea475a0c5f2d34b773da4c5e7f18c4693f6916850fc0ad16f9cdde4511d80b0c2cf1c3ac24f6ea0938ead1d03683b4a148f2c8dcbeb47270bda65a3b0f6584b95523ea474fa93849c32ce6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part328 : Excludes 0x50000000800000000000000000000000000 0xafeb4ad4110000052800000040000000000 :=
  finishCode 123 0xf0368d240051f293a0967308b6cc5e0df902af22e00ef317c51330c944e7b48796289bb10718fa270d699bda478272b285837c3ca50b81defc348ec3c8822b0ce20ec38b23fd226601312a5090d941671d1ea98056c5f0e3a8ef898e38f394a82cb0323ccb7b2d881b5a07b713d4e52da2a83db8c2ed599892f5b504a4a6479932e0ee71d50ec7f1489c815312a0edbc5a16c450e6e941c360eb0e6523ea475a593d60eb0ac4766c495a5ad3d1970465c7af6b0caa47c57a93f7b4c3d53f8a4fce369a2d8aa1c7528735ca317b693d514621c8cb72cbda4346e6b9c9f2825ed2c4d615c7f17379f55252f699412e4f2f4a4352871f55412f693f893d527eda338ac0f6e49ba51cc4aaa118e0029fc60ef07b1eda87d48e6237adcd5d4eec1ed69a7f127a98bd281edca0b5239bec643d14167f192528f36c1eef166490b0710e0a3be2ccad360dea87d505a1205a6a4de49faa89478072a1f5239f6e72987055456143f023cb8e937836c8f350fa91ded27f1479c7f1479c8ef4f127e947810a3d527a8f564a13c5915427a9bee58fb1551e63db30ba4ee37dad34c1a60d97062230f02c523e5e9306aa8f23da61ed9bed004eecf670c4a91dedb391519647b2e38ecded26df9ed25bd609c379735967548ef69791647607b7077a0e2f67317b075eb7317d2529dd922e599312ad89e2a8a1f9856f6959a8af583b316e1d8bda543f316d5e6f69 (by decide +kernel)

private theorem part326 : Excludes 0x50000000800000000000000000000000000 0xafab4ad4110000052800000040000000000 :=
  splitAt 1 130 0xafab4ad4110000052800000040000000000 part328 part327 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part330 : Excludes 0x50000000040000000000000000000000000 0xafa85a92a0880000014a000000008000000 :=
  finishCode 131 0x3d8f2378e23a01ef6a1b86801aeb8338c2073e270b56cc2e62f570c32f51898e3df0cccaff5ab931d683068eee4869fed476b4d6adcd5f2e3ac0630bb4f6514b9943963df305ad8a6258860f7dedf3965ccb06f4179fbd5449f8b6e5a6a4956aee6589d720c439e93f263c9135a11c3132dab69135a6abfe489b09cc4718647be0d7671945d0e40e7b92649ba8f5246d5b2e38f7d69a8c244cb4b348c7bea3d6aec3df51ec3df5a6a44e2e3cd4d3e5ad3547a93f509b56d907d208077c515671706813c4b0c2eb419cca4e15238f7d27f0d8647db4e502293f30c98bc97720c5286d5b24ccc556ad988cc1691b9ab68316112772cb4c16c49962ae4f5a6ad0527e6239687c127f002c80ef4a154275acb658dbd4569a623477cf513fd9b5d262b479cbe5f35a698967b7a0856a73dbd05e509293aa8bc2609239ab6b534a3b08d5b98a6f5151e9fec9db3d44b16d25513988e4f5c6195a9b495787d1f0691c50928ea68b6302e4a3b50d876d5b37992de489b56c5d2d239ab6625257a51e7b993ad24ad5b418cc3d17498bd3c5a1d0284ad3530671062940f7d5ff28a5ccab41275a30e5f9ccaa29513ce5972fa8a62758f7e732b90d05e4eb275cb22f0941425b0275b56e6138345ab70f7c99706cdab6931965a1c74948ba60e30345a465279f449fbe0b81474a4ef55925290593ceac2c8619722c7fb276a89da7f308d6627294f3b4f56a6d5b9a830bc62506aa93e699a51dab64eb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part332 : Excludes 0x50008000002000000000000000000000000 0xafec5b95bd0440000810528004000001000 :=
  finishCode 29 0x1c86d1d87c1f428fc1e5293aa01e549fc3d1275a80ac28564a3ac35ab661969ecb4b513b56dccf2d1d27ede388c4035540623ca3d7318ba54766195a9c93f387a810699222f696ada31527ea15402ce41488b101cd927ea4f6ad93b4c32d5b927e4ed30cc4ed8a3e4ed8a165019ab693f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part334 : Excludes 0x50002000002000000000000000000000000 0xafb9ded2d78441002001528001000001000 :=
  finishCode 37 0x104348fa360b4d27f949d5ef30645be82f4f8b56d062aff9cc2d5f1efba0d82601e55a6cf6f275a005042d239ea282f5a0b56d64624ca3d5a593acfc5a6a7c66ad9b5d5ff13ae275c811284b48d8300e22b80d14b05bea1f905ed3998124cb9abeaf75a6a085700e2cd5b6048f450624d796831875a6b02543e2df49fcf6b270ac241a2b6278b1f727ce6b6adb0c569ac5f1efb8f657d86b5cca0a16ada826408c4e1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part335 : Excludes 0x50000000002000000000000000000000000 0xafa8fa90950440000000528000000001000 :=
  finishCode 125 0x7d1c46f1f00f7c00ec03bd94071abde6a98ba569727c47be93f6a4a40d82a07e1e093f5b18a2f698692b0d174b4e431ab4b6b3cd390c6b5744da2e99ac6d5d5a5b59e7b4a8c5842af79a92a0b16fa4fdacf41c4b327a9174b5255e6b4f57bc3df5f01be3df926ae459b0276b98e83b9f3dcce70f265873527f0719ed68ff3d4b13500af83680ef63130275949d27f348d002831417c93f691a8ce6ad947da7a1d58a16da2f8e81c862769ccd24b1ba49dad3d91fe6190e6c4cb49aa4fc7aafc410be03bd402eec619376a4fce664ed392c7336c0fcb356cb8e463731ad4d27e1cd3e0c32e638692e5f3f2bdac0aa3a53e7c70f7b58f540b6d8318e43b0ae07649c32cadab693f1ef8b7d0630b7e5a6c3df49fc1de735a82ded23d15a6ae0c42a06194c098f0e64b621ad2e3ca1f7b4ad34b63305d892d533f2cb2162fa82dac71fbded6c4149d706adcf691638744c32a8258a1f948a762cb68379b35812d49837cc0958aa82e7b4ac563d99385ab6f6b711b07c1b84301b2a020167b48b7d696b4f5d18c275c93f16fab091389963d5580cd6783fad5dabeb4d7b4cb4d584b188059ed2a1551e8b7d69b357c7aac62e89041093f57dcaf32759c85ab72bdd042af79042d29591ad345beaf3928e4e15a5cd5758aad35ab6d5f87aa2df06bbe0b2318b4b51eca4f275a7b630cac9ded2b235a6af85c7969ab1b58aa4dd5ee721399abde36bb56ce265c7a0e6a3b735986569a72f7c18858ace4f595b56cc321d95a0cc494f8a4fdab6d5f969a733 (by decide +kernel)

private theorem part333 : Excludes 0x50000000002000000000000000000000000 0xafa8da90950440000000528000000001000 :=
  splitAt 1 121 0xafa8da90950440000000528000000001000 part335 part334 (by decide +kernel)

private theorem part331 : Excludes 0x50000000000000000000000000000000000 0xafa84a90840000000000000000000000000 :=
  splitAt 4753 123 0xafa85a90950440000000528000000001000 part333 part332 (by decide +kernel)

private theorem part329 : Excludes 0x50000000000000000000000000000000000 0xafa84a90800000000000000000000000000 :=
  splitAt 1 102 0xafa84a90800000000000000000000000000 part331 part330 (by decide +kernel)

private theorem part325 : Excludes 0x50000000000000000000000000000000000 0xafa84a90000000000000000000000000000 :=
  splitAt 1 107 0xafa84a90000000000000000000000000000 part329 part326 (by decide +kernel)

private theorem part321 : Excludes 0x50000000000000000000000000000000000 0xafa04a90000000000000000000000000000 :=
  splitAt 1 127 0xafa04a90000000000000000000000000000 part325 part322 (by decide +kernel)

private theorem part317 : Excludes 0x50000000000000000000000000000000000 0xaea04a90000000000000000000000000000 :=
  splitAt 1 132 0xaea04a90000000000000000000000000000 part321 part318 (by decide +kernel)

private theorem part311 : Excludes 0x50000000000000000000000000000000000 0xaea04890000000000000000000000000000 :=
  splitAt 1 117 0xaea04890000000000000000000000000000 part317 part312 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part338 : Excludes 0x40200000800000000000000000000000000 0x9d155e95100006012010000040000000000 :=
  finishCode 71 0x3f8e8391043c81e97b1bc7b4c8292e09becc4a0d920cbe90a24fc1c26fb8c4a5d19ed32d34b82623208b08fa448b80c5d7c1fcb17e4a3b55e62fa4de578c93540c9bfce5262f91fe9351fca8765238c5c7f23f98822b81064c2f0fe53ef1fa5eee8f37b4a39cc2e72b49fc4198220c6a0622b41815ca70f551c41100f183948eb4746ace55474d183615ac6d43ac22826593a8c56a673750eca316a1b4611bc1799bfe836a0e527e7374e127e5c19ed20a7612b14c7aac539284807aa8299ab2a4749fa91e271cf6904fcf713e2ad4560e1bd37fa91e49f9cdd68600e6ec3b8dfee3d49fb93cbe6819414a4fe38ec8295a3a401e95b127e9a0fc649bb91dcc67379ac2c097b49816460e1ad3f9222d29302ad3e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part341 : Excludes 0x40000041800000000000000000000000000 0x9ca5fa9e75004805a00830a3c0000000000 :=
  finishCode 41 0x429043e9083f8b1f9ed272b2808be41e2c23b10779486e437b5a47cc0a729386b38943969ab1f280a81d45eb3d94932d35612f69760b8e2f98a02311186cb536110430bbb0e6396a6b4d164a02d697281d492b53593ce4736b8b2569a8099ac62ff5a6b38e8308b098e56b35311bda4c4a8379eeeb357b49864e6f2cd4be6c23b071b9cc660d582a095016a02c7e3069af6579c1bd69ab099d8280c947302839d5440bacf67b6a0a528e911414cf69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part343 : Excludes 0x40020001800000000000000000000000000 0xbeb1c9de7010a00da0050003c0000000000 :=
  finishCode 107 0xfe3c8ce410b80bfd61328bcc3262f611e0311a80837969a9ff40c9b5e489a925ee3241569a90183cca132ccbda53f2b0949bb08a6185d69b209e0e2819270a4c54928379696819413cb05270a025612ac308a02d060d821e04620f3241431af6937da8a549e7200f65a69900418df6145730a3bc9d738f563e6fb34ec8f37b0ad3569b0506699b0f51e6ca170d578b8ef61482ad35d86abc7eb41d82ae4989f6d2871819ed3071275a0ededb34cc9a24e1584af08c13ad037021cbc2905584d07b3ed9a75636b35527c90d5a6b087a2209177b5c93b41bb17d4c41bb48e254a925ece81960ba50e0f3305dccaf6767140780dbf250dac2c3141b8af65a6b17c16b2d35a5a5e99a8e863da6413b17d6124d78bd2f6b41b9785784518c541742759c086280a49966ab4b51acb09503c606050a8d4daeb27349cf696968b2540e19f0d5ac9d40781ec3284d1feb35527a4de731a4de731b0881b9076b099ed2ec2c03d5722ce6340da3cda562bd5a6cf6959ea8be51aad1de4671d8560592e3d8bc27c9722a92540f2c7d20a81b56146b302ded20a5521a416503bd8568e6fb968e83b723c3d57b48af4bc27028f659ea43566a722e86fba0e6a2f59cbda477680b969ab23949eb39 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part344 : Excludes 0x40000001800000000000000000000000000 0x9c23c8de70000005a0000003c0000000000 :=
  finishCode 157 0x410f03202f38e52515293b18ec1475fc83224791cc7036c62f001b89f7928680762fa986c948bc1e65a6a50e0f31b26078cc17317836cdab036c1bb1c34b8f2c3cc5ef23b072b8c5e0dd85158317a8be51ab486504ad1ded3282d8be72b9aaab4d364a78b4328a82d35d84a1f827a971e8c08c447aa71b306cc42c87377b4c5c7591ad3c7b692983471c3543ea1f89eac22c8e23b03d3394c6e340db15618698bd4169318df69432f9cf691888c361c18c45ed2943b0b23f84f5551ed23112edc71b4a3ac767b4c71b306c3d5489c9dd37d98349eaa47760e530c44e56913827af6150f83cde47b4971dfc5a4c94730b83ce3031bee0eeb1d5a8a91d4164f59aaf063f8c83c85c7943e2f3188ac11879ecea315199815c73287cb8f287c6228c171e5059c34c0a7e3085c74d0e1ab399226f6958e8f6d4133da540f3da6523a4450366b7611417177563af692e39c34d532c8cc32b1d2ddbda5d0621e45c19c710c32625523cb05071ac2528270cb1d4faa91d60b250c21835947614462aca33071a0ed877247d3eaa33071971e72cac6c15ad33523c1be523838d412b099e07616631cace1e0e3550f672d2d3ee6bd7b4a87c15b3da5612b477b4c7db83dad350763db5e0dc78143ed4d8ff24e158d838d68584c72b5a6bda641dca45071aa872b1e9ce59311ac6e5b1844d14038eb17e2f49b256965c796623c548fb8e5252c8247d0332c7d3cab4f270c819582ca33584a41650fbd9de04fba926413838d60f317ded23873ebad35d8792105a3cb35412a0ece6e9e2c6d04a83b584cf715a6ac267b8c1ed3ea9298e3ab4b5501532d1d43ea47270cb47 (by decide +kernel)

private theorem part342 : Excludes 0x40000001800000000000000000000000000 0x9c21c8de70000005a0000003c0000000000 :=
  splitAt 1 125 0x9c21c8de70000005a0000003c0000000000 part344 part343 (by decide +kernel)

private theorem part340 : Excludes 0x40000001800000000000000000000000000 0x9c21c89e70000005a0000003c0000000000 :=
  splitAt 1 114 0x9c21c89e70000005a0000003c0000000000 part342 part341 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part347 : Excludes 0x40400000820000000000000000000000000 0x9e3f78bd104811413032020041041000000 :=
  finishCode 29 0x1805019c7b1032829640e360e3735cb3911eb49437a9dd8dfef61395c60149fa7d548ae8106658f9fe5ed21d91e486f67b79cddc87b2108316820cb086583b15dede7375a3ca098e6e82783826250719cde38dc41949fbd8e43480e35a9c73749fc6ff62aad4c8331bfd63693f395c93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part349 : Excludes 0x40000040820000000000000000000000000 0x9eed6abd11485801201a106043041000000 :=
  finishCode 17 0x891f474210186abde240a39c37270f2809cada849fa3be3648bccc0a6d193be6c925bacf4b8ee4596a65013958c45e020ccc53311a0a527f3c0e83da61f8a4fc832f5b928e93f078a4fe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part350 : Excludes 0x40000000820000000000000000000000000 0x9c6168f5104800012012000041041000000 :=
  finishCode 159 0x7d1e0691b4800a3a51f832246f03d230d58dc02161e8b7d81e145961ef6958da0a60f49bfe7b498bc1b60dd98a693f641547f0a1708428419079c807188a0de49ac0e70f4d003f908418ec04f67b1ac950523f949f9fe4622b1d906ea0907890647d30c36072b4866079cdd672f691f4a44e6aeabc4dfe3d55049cadf87b21406e8c46395a4de188c72b723c311523a824832e83f1082b00f10f4aa8b3d92023f1517b155ed31f247e2d2587e2b1b0ecc5131ea9895033036c8330a144e0789f85134a3c83983ca4fcfeb206528efc2d09041893f891fc186c3116918441128394cc55505a91d6a3251d416c3d928e605827af691b0bd9548e6fb477cb3b47993d5aa6e554889bfd5849bc947610dff2444912a0b311a91e7b4bf86ff8c1a62f395ca3137fbb0c2299001c6dcab28bcc0280b41d8c5d077244e0e28c450564f58c3231159061aac13d59c737c1c1489a3ce0e0bd6e5a8a87d1e6913838300448fe0c36188aa0aa23ce489accd28ea1f523b6894244e5a4a8bc9ea6fb460e0489ce554799b952273d6d2273d6ce3b3d4e302b574b8ea0b37dab06239ed27f150fa91d26e947611fc50fcf5371ca91da427d7311a82e50fc9113f8bda5ea64f5a0c89061b0c4570541d06d0c02a479eeef53317ac76523bda54127f183bcb25504ad449ea91194165c77b493d67b48bce317bda49ea61978210831ec6f17006c906567b3da563ec391f8bda60f4cce3dc649b8fe4c5e1e987f25a99ee3277e0f2b094a39864c4afc308d225083b8c3cf533f8a4fdaaa62361e9bec9d6aa4606317a4dd28ed478042a0d0e098bd2261c18bba62f49fa18b4b89d66fb275cf6911ec6fb2ce93aded260d (by decide +kernel)

private theorem part348 : Excludes 0x40000000820000000000000000000000000 0x9c6168b5104800012012000041041000000 :=
  splitAt 1 114 0x9c6168b5104800012012000041041000000 part350 part349 (by decide +kernel)

private theorem part346 : Excludes 0x40000000820000000000000000000000000 0x9c2168b5104800012012000041041000000 :=
  splitAt 1 130 0x9c2168b5104800012012000041041000000 part348 part347 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part352 : Excludes 0x40000000800400000000000000000000000 0x9e215995122080212000004840020010008 :=
  finishCode 125 0x421003f9063d80f383d241120cbb1043903f9862e5270f48c5e49fb101d9905272b39bae091793eee5f4a18fe520630d6f24148e6f6f1eda4fe0eb202ded23b387b670d67061a1ab9286623414a50e48292edb4671547d01b26173119c364fb947daab1a75ede5a95c0a3f41e45e6b4d06c98bdec75169aae0365487171ded2d3b8f96f71503a0662939ca67e1d839bc0d90f4a803db8c1aa0149f92c57449fa79648f949cb8f06d9816b4d5a6c0d9612a8058aa527761667079500eb4d394ad362858fa5f8761906f1c83f8cafb7b4ad35cc63f116f83643d2c6247e474a02ce1a93f691ed3391569a80b586cb3d8daec5328f87a43d3320d23e8b5398a63f1372947d687210816fa47e37dc1cd41ae658fb6b23629cf691ddad4d8a7348581e3f17b8c3f157bb189024fe613ad45ed2a3582a605d6ae9bec7b6b0f3d6cb1b71ca4ecdf6da2bde293a5850b1f88e3e6ae9fc4b8e9290d1bdc658eabdd687e134720e563c191de4d149f9404a3e0dd501ed32c7dcc293f2808be65a69c350167378a3e527641102939b5658eb4ed64a7f1730ad350828585ae730ac756764b3723cc0f696b91e731836ca4f1c741b6ec390f224fe5a68c5c1b3002c0a625093b8bd2943570fc49fce6f593869d252827624c1ab28fa0660eca4a5905a6b11e2f48f243bac318b8e8392cfce53486b17d69a51f364c51f41127ea2f969a80b18bca3d5a698be (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part355 : Excludes 0x40020000800008000000000000000000000 0x9e3949d7523461052081402041200500004 :=
  finishCode 39 0x1e08420c7b03d3106590317c1e91fca4c6624985c3d262f76188821900f49bee1798fa41b3206e1e2a50c1b21d906cc1e9501904a07d2b4b940e81937dad2e40cb5765a68eb53f26fb312a06523f1eb49326fb36bb20f20765ccb185d252e3d2708f245e63b395e6a2f40cb8f4bc2e6579127f0364bd3292527eb4d3f1e449f93ae30bad3507691f945ece3c90758be62f317f98bcd6f071456e6fb921a7f1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part356 : Excludes 0x40000000800008000000000000000000000 0x9c2b48d5122441012080000041200400004 :=
  finishCode 129 0x821e06d18c640a2651d85037a1c1583c9358c197cd26b460e3072c1cb82d3b61297cc1e262f69190850a3e5e793dab0d317ad345ce7377903aa8ff9a567d14159f468c1c1d5e4801d0839c73718698bd4631cdc1e2b4d8e566c9395ca315a69b25d88410132064dfeb4d07887a5d06401ca9e1a306a490ee981540f245d69a6b7a3029175a68c45223188d032be320b8142d27f0f047f21bd760e1b07a4e6eb4b91de1737b8ad348330840072b519cb25188ac1c832e479cc65e9928f083a0e458832b1da0eab4d39bb914d8e83b91fe0e74813c49fb68ce2d8f223fe4a393d45ce5f330ba50737969a4f5623ca358c0c1d5cde2bd18bc6934949fc569a4f550fca4750fca332ce9c6d69ad2449064203114514672c34e1a71b096c91f302b9be126b0ad462605840fcb1c354631aa47b68153f8cb1d39b9ade1739bfd3c1edce6f27a9c6d69aa1f946670d38dc20d22d8c40fe62f49834e56737791547b0c2ef02d3527f106548f1fc527e9059466a1d781700718fe64a1a09683c9c3527e93f9544a1467291c57b287c833079961a6b74a1a92504b1834e1a0e320cae0e83c8b1d969ac2f586b124c2e6253f8c92920cb209298be61bd4eecc3b7b0a47cdfed59808681948297cd27eb4d78190621804a037a1d9014c81b50ea4c5edf16d60f71811edba093f4a01c6943948aafb943e6ab8076afb1cdad2dea2f63524c2bd494a50c1c6d6394926c949f838d7c49fa50a33948e59d943e815903659d (by decide +kernel)

private theorem part354 : Excludes 0x40000000800008000000000000000000000 0x9c2948d5122441012080000041200400004 :=
  splitAt 1 125 0x9c2948d5122441012080000041200400004 part356 part355 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part358 : Excludes 0x40400000800000100000000000000000000 0x9e3d489f328419832022020040040488800 :=
  finishCode 79 0x108308b63e8ec31071d8e6e8a3da647395ed20a3db2708af483270d5519c15ec1ab30ba58a47943e9058b8341c504ad4f071c1e527ee833893f8d526e5521988cc5f062d04190e0cb4d50fca475d148f0b7c9c33da4382a475d13c16fa4a6583ad1d04e6bd968e9059ec2b4d71cbd84e198a293116f90653c48f97fe4a1bdc66998fe4c5eea106528735353ea3c5270a4fd1e72d358a2a47386b104194611d328249c293f5a6a91ce1e8e7948e4e149fc61e7b4a7760e2a4749f9385844a13c451262943413ca332708366413a4fd547d12c699c6bd1698ecd48aa4749fc91f48fc81b5a3b4cc5a68e785a693f511e41edc625415b000b585a6f6b517b9be7b5a4a546b17cd252827781f4601e44a01c68fb948a6c995e6a1f732a09d9c0eca9265799f9dccaa4788f6b4781c682783b29623ee523a4fe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part360 : Excludes 0x40020000800000100000000000000000000 0x9e754b97121428872001028040800488040 :=
  finishCode 97 0xf6420f0418c83b04115c16858103720ed27e0d91f8b90b278daee4749f87a5c8f244540ee6349f9b5d6a703643d294783d283b7b49f8902d0c5198ae2df49f8fc636bb0fd8aea2f964e2df6078fc47e33101e920ca44e36fac9d6a6ac236c9d6e63847669b69da4de303318ec277e06ca4fc3d2ce0b7c9d71bed04e6fba0f70db569a0d90f4ad0903c893f4f1ac702ccc2eb4d71126f028d0766fb9ed7167438a0a34f1e46117441da8be5a682b52272d3456e6a93179bed61324dd1de4d169993ad2533d9da46a2f275bc8d420ecdf7178545e8ffa3028e94619beda88c0ca2f2f08716303277dc4791847b4c94361e8eec35683b5f10c275cb0937da51d9c4eecf6d7b4a8bd4925e186a24eb2e3bda49a31b5da867146b28bd1f7178519713ac766f6b5f09d700660e26b77b49b7cdf6d23a0e6c2336bbc89e0bcc5fe4eb9486b4d8c0ca434a13c0eec4eb4a1b99648fa8bcdbe7e2d1e51787167b5b90c207a554317c4861740dc83b488c9351b6bda458269d90368252c18fe51d23f99cc3357cdae93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part361 : Excludes 0x40000000800000100000000000000000000 0x9c674897120408832000020040000488000 :=
  finishCode 133 0x781c8631d0289947528f2d347aa1e9312c21062900f13fac48d593a51e583c935990801fc6a1d0621d075524b4ec1ca1d128f87a58472ac90d28fb94d20a2e7098c51f7b0a3ee80f2e7b498bda764115a9cb538e6e72996a61e928fc1d636bad4cf6a71d28fc210a3487e1ca5e4731ad363798c450366f38d6f2d3563631137fc83ba3066a969da05ded24195a687a60085169a0e559ec6ad5248f5659e9ab5487400f64210a2280f15b0e1a9358f663d31f89b9569b39bded23f11f8c6e5394a51e49f9065d849facf640d9bb4bf230d879682785127e8e78c2e70d4888c44e6e3f9891a82b4a3bda61017cc70d39b8be649fad09027893f79169afe4484f5a0da6fb3118c4526f28d60da9473119bfc16b1c6d63ac1d9cb26b773793d5fc84114486ce551739ca4dfe6df8c0a3174739ca521b30acc0a3112e4c91f3daabc4e1af2309081f0fe1c34c5f2c741e6b21bb658e82cd69a3db612c9135a6ac760799ca5d8188c2f34a1c3db5a69bee1868c44d6f1cdd3be4f52fcc49003f8ec250311591a827aac08217e4c0a7b3801a6df838c60630ef6948f9ece7298034dbf0718c0c61ded2821c76835b0ad46b28bcfc36fc4cb4ef9c3ce3b350e4f948e7f148f9814fc4efc9dd7b49c3ce3b310e465868dcde6054a1ca0b5238c341e6ec1bee3028f6e4a3a87d48ed40f6cd93310cde6605379c71d1d9b88ac1d87e24dd45f1c3cfe31c7548f39bcc4af69517a51d2231c760e24eb523a82cd6b005dedaa3138ebda54664f5 (by decide +kernel)

private theorem part359 : Excludes 0x40000000800000100000000000000000000 0x9c654897120408832000020040000488000 :=
  splitAt 1 125 0x9c654897120408832000020040000488000 part361 part360 (by decide +kernel)

private theorem part357 : Excludes 0x40000000800000000000000000000000000 0x9c214895120408012000000040000000000 :=
  splitAt 5016 130 0x9c254897120408832000020040000488000 part359 part358 (by decide +kernel)

private theorem part353 : Excludes 0x40000000800000000000000000000000000 0x9c214895120400012000000040000000000 :=
  splitAt 1 87 0x9c214895120400012000000040000000000 part357 part354 (by decide +kernel)

private theorem part351 : Excludes 0x40000000800000000000000000000000000 0x9c214895120000012000000040000000000 :=
  splitAt 1 94 0x9c214895120000012000000040000000000 part353 part352 (by decide +kernel)

private theorem part345 : Excludes 0x40000000800000000000000000000000000 0x9c214895100000012000000040000000000 :=
  splitAt 1 101 0x9c214895100000012000000040000000000 part351 part346 (by decide +kernel)

private theorem part339 : Excludes 0x40000000800000000000000000000000000 0x9c214894100000012000000040000000000 :=
  splitAt 1 108 0x9c214894100000012000000040000000000 part345 part340 (by decide +kernel)

private theorem part337 : Excludes 0x40000000800000000000000000000000000 0x9c014894100000012000000040000000000 :=
  splitAt 1 129 0x9c014894100000012000000040000000000 part339 part338 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part365 : Excludes 0x60800001000000000000000000000000000 0x9f37f8f8a800820cc100000200000000000 :=
  finishCode 21 0x1fc741d86d01c6d02f0617510c2c92ff8b9d27b17fd69a9e3815e1bf5a697fc78f1bcd492729404b40da28cd073356dcbaa0b28eb56e5a6876e2ffad34fee5156e1b42859cde1e3876cbe670d969aa338be6a450edad35613074d48e0dd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part366 : Excludes 0x60000001000000000000000000000000000 0x9fa2c8b8a800000cc000000200000000000 :=
  finishCode 153 0xf23f8ea4001e7741e062082eac2f860146141a83749ac3bd72facec5bb05ee724971d41af690d6a90d7c570dab3d85c867295a6a01dcbf1ca6699c8395a6a01d7056108300ad3e1fb9c3cb62b3b5a8af8aa0fdc283282d8b2f69592ad0cb9341dc7aa3d5966ab255f15f30fde0e73da5edac176249cdd66ae615307eeaf19edac115a6a90d8b2af18b929357b4ad34e1b03c47febe3e0bc063e285a8cd26a9475305970fbce57391ca16b4d730c8e373182dd26a9475b169f23fc1bee45471c1ad47fc00f80ffe20bb40da2b8625413c9351f7a0e526b2065436901300c809530c16b3b9486d4d87eed02f8ae3e03ef54168519a915cbb140524a70d5a6854601ea86d24a982d0d23a0f2a491659c6c2a328bd87ad5b4a3862e47ac107616fe492a4dc9db34d569b0799ab6d4d2dfb4ad69a2cb39bcb4d522a60a2f94867297c1acf165d20e52750dcc5550dcd5f5218b9dc8781d86e17c06d837569b3585cca2dd58e942dc8b2d358c5e184651300e9ad8a499ab718159a8b24e52e659a46a21284a90e3033da5c92d5b6a29afdaae5094f98f4d69a7ef91fe5095a6cd5b838b57dcce509579ac256473925cbeb4d0e9b9965a6b0a662cabcd6121d3284af0da340c213d5947b4d1810c58b7564a71b5a6874d8230b24b8e71b7b4cba2d367b5b0a58826bf579ac243a6b3b969afc172659dad44e3ab5198b23bf5a6b90659c971d69ac2318ba3007290e99c065a6a9245931eae0ead5f8fde701394ad3526b2d2d45ea4972ead3434b171d45ef695a6bf8c6400aa0ffc82edc28c47ab0b75ed7460569ab155ab9f5e57f93d4e36b4d5313f31af435aa455239cdc7deb41b850b395c9414f1ad3548e941969a4d75a5871e293abde4fcb4f4e3a4175b184720e6eaa278e5a6a8c4fdf2d3dedeb2328f96fe5a79bc583eb23627ac261eacaff620947d412a31 (by decide +kernel)

private theorem part364 : Excludes 0x60000001000000000000000000000000000 0x9f22c8b8a800000cc000000200000000000 :=
  splitAt 1 131 0x9f22c8b8a800000cc000000200000000000 part366 part365 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part369 : Excludes 0x60100000020000000000000000000000000 0x9f87ecd1f05000044033008000001000000 :=
  finishCode 43 0x1bc741d4711b8733c7293958f5419e0dd7f0e37079c1bec231871b4a3ce67720b10503e8116adc5bd62ca0467b4af0be0756395a915980e2c72b0ea9cae410c9413959cddb88203ab1475905b03aa3ef8e52a49987ed3d541a471a9e0f2d5b3dac1ad8aa71d5239f1e5a48fbd304a3cd5b4008b9d22271b5b05cf0fbd5e723d4a12e67720b08a6142e3efb50c7de72939baa0d25837a72b83fca0b7b6b0f4a16a45878a52716fb916400a4653eaa1d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part371 : Excludes 0x60080000020000000000000000000000000 0x9f556bf1d45000018033004000001000000 :=
  finishCode 61 0xf0370c807a57041fc3f17d154293b9566a3a87d26aa477bbcc596ac8b3522335758aec394d0a3aa6244cdcb248dab2c39524a8bdc9339954133da548ac82a0a1f8daed5b41f8fc578371ec6ad971e505c605246c1116fa07cd7f1725ed2729608cf537b8a07ce5281f9cbeac268e65926ea45924673749fa4fe5a12054127eb63b082137fcf71510a03ce6ea219ec2a0998b20cf608a51d0229018e520cf5315838d9ffe6aca8bd2269353ffcd5d27ac1fe694c1dd2261c149aaa0b62f094298a455239b9641f9ffc9eb3975ed286350e3ffa4d4fc517cd6183f971d43e6e5410c9a28bd04290193eeb515abca1f948ec41903e0cf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part373 : Excludes 0x60800000020000000000000000000000000 0x9f1f7dd1d05001000833040000001000000 :=
  finishCode 7 0x410bc07a5b4072ce4116d8fa4a120e58e1f0394e6e7378c4a0e1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part375 : Excludes 0x60008000020000000000000000000000000 0x9fdc7c93f05040080133000400001000000 :=
  finishCode 27 0x1c87c1d05b03d2c83383f939bce4348e8b9dab7242dbc7d104f1c6d27e7372e0c81749fa51e47ab48d86318149fbdc5abe5ff8c0ce6741ca3bc7f2c233872941ccf614a38b9d5049fc5c1275b56e0baa4fdc8b147dea6f717418406ac737317873651ec70f6a2bdc4e5273785ce93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part376 : Excludes 0x60000000020000000000000000000000000 0x9f98e891d05000000033000000001000000 :=
  finishCode 139 0x1e0741bc6d083ece308b6188e1fb98bd40312a3d683bb0349da8370f3a0a5c46ad96967b48ef49962df4929eb646d9ad58aa2c7721d859dc1e77b48fdc39a1e79ed23f716f9866721d87514006ba4ae15ab14542a7f95a039b0b7cd7f1c758a2a02d060d372c9410e68ec6691a41cff271d694aa06bf720cc51695c6060e2e6f38ea7fe6abba87e0b1dea734b5c826e561fb15d58605cd61737c605ab68ef733c7f97b0b955cdf181610b56cd7f1834e1f30258ae73749fa40702f87f95a127f23fd26a4ed670fcf248ded2a490cba51cd7b356c39b24fcc03356c7ee93f5f1545a1603236daba935276a51e1b7c1ddab23f741bb4960e6cfa104527f03c540f3d84ffe6236319c6907ee4077e1cbf06f4e56da24d661192bd8a68199cbe9259cbe1bd821c86e1b47c1d4293bf03d59ab61bd16fa4fd44f3da49d67f99f8751edf2805a423d50de8b7da87293cd7e72b1eabdbe3fca8a5a86a4f3fcc4ed285b56d27f03c4e1f24fc1e27379f47c13040c83c50c394b1567bb9bfdabaf778dfe8d59ca6f7739b97cd033356524a3d5414c9251ea8b9dbc5f16c6d07ee3ff5a1c92f1ea98bd5f3370da2e0b57a0e21c10f39834c4ae21d81e758ad071483b99d26e9135abc9e1733a86dab2c3b8e366b5711545c126eb424fe49a871562b3da4d7e93583ba8be59dc5995a887158829132e4c6015a1bda66aea92545e9130f3ad8da2801e7904262f495b9866afa07c3ce62f40fcc1947fb11d042e45579c8ff0d8879c38a9424fd0432d0585e60150ea48da2506692a77ded2a1b3119c04a398b2d216b0b5642b26e558ad07f59d88d67b8a4060ee821 (by decide +kernel)

private theorem part374 : Excludes 0x60000000020000000000000000000000000 0x9f986891d05000000033000000001000000 :=
  splitAt 1 123 0x9f986891d05000000033000000001000000 part376 part375 (by decide +kernel)

private theorem part372 : Excludes 0x60000000020000000000000000000000000 0x9f186891d05000000033000000001000000 :=
  splitAt 1 131 0x9f186891d05000000033000000001000000 part374 part373 (by decide +kernel)

private theorem part370 : Excludes 0x60000000020000000000000000000000000 0x9f106891d05000000033000000001000000 :=
  splitAt 1 127 0x9f106891d05000000033000000001000000 part372 part371 (by decide +kernel)

private theorem part368 : Excludes 0x60000000020000000000000000000000000 0x9f006891d05000000033000000001000000 :=
  splitAt 1 128 0x9f006891d05000000033000000001000000 part370 part369 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part378 : Excludes 0x60200000000000000000000000000000000 0x9f057b91820000000000000000000000000 :=
  finishCode 135 0x2007f1ec831a020f83860f4a4fc822b4d91b6801418838527eec3400e16203d26258c5e6ff96a2ce2d80a7836660b480dc521caab33583cf6961d8f5560f2907c1704c90a8cb3b7338e5490f41cc7aac5562bce418399afc7aab3b9ed2c3d583c3d572aaccd681eac701271b56e379b9bdcce37761fb4a5b46f1680eba80b825072138cc1a902d358af2d3deee7c172abda5ab73955cab0eb46f72c35ab693f5a5ad3475b3da584293f6ada8893f9ab65b38d7b07f696a91d8166e5579ad35705007d31775a52a8315e518b15548e6e52d7cf6935fb56cd7f0d551a2f69523b4a5ab6c0d9ee2d675a6b56c37a62349fb56e3fc8b447d2837300b90dc3081e9621ecf1894c46b63e86170e5c58f62ca91ce1a93f9eda58f6ada4d47f283787f29351fccfa310de205e48eb56ce5273758127e94187f2f539282d5b2dfcd233f4b494bfece0fe60df06bd27ed5b2ffacd6836a4fdab693f9d8721ec0f4b18de308be33870d9202b4d4a39c743a6961c74f449fa03dab74604786d5ba302c116afb10672eb575ed293f3ffcb4d38da4fce6e831969b0fc527e9119abad5f7b8a00569e5c96adad35bc6adc72939ba8760d98fc527ed2308ce030e394872d69f24fce567291f4ca2f7b4a08527e93f9906e1bc5c18016ea0be1f8c606417b56d04280f9a86b4d0e9ad366ad8fc527e80f927f248cbba9135a6874db86f1a006fad892b8e56737836cc3f1eac61d27e1d538dad893f969a7ff41fb57e631a049fb496271970569ad5b0eab57e417ad35906aeca315a6938c3aad5d969af693799bce7b4a4fc13a0df (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part381 : Excludes 0x60008000000400000000000000000000000 0x9f7e5d93b2a0e000002200cc00100000008 :=
  finishCode 25 0x378c4370a624fe06a988ce5273779127f149ce56839317949e395bda649f8f4ce5272b711e46e0396c820e4c2ec1791f21e9903270d1bec81747cbdb4bfe3f92df871e1fcad0630ba855900f4a486e23e6497c1ce1e9c1c527e941495c93f838b4960d9b91d27e5bf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part382 : Excludes 0x60000000000400000000000000000000000 0x9f20cd9182a0a000000000cc00000000008 :=
  finishCode 157 0xb4278883f8b4d801f06717c7807fed003c52031044c2e7ff90425ff49fcda107d0427298c5ec4991c6a35394a4fe7a8a7648120f120fb38d0348617317c3f70f39bfe1fbca2906b982d27f2bfcc1ae4b485b905282a3d671b47e03ce92b8e3a7378c3c919407a4f5f81f7c729731c83153127f037ce6ea3d990531307d1062b0d8e1a81f927ede207e0e7ac35b8837cb1551e96fe49fc1bdac32c5547a821591a883bf8ffe93f628c0dd0e9bf0ea41893f7c1fc6f107f0fbc83e4098ffe83f07886be41f9ffd283182c7de701394839606eb78d03e0da107d1f306fce6e5ff30ba8be38da925012d2581925ff317a50650dac3c83e5ff208c0f17f1f071083e50b91c6e617b5c1e45961e7285c8f99a4a8f50f3982cb7f34a561ab39285873e0c7f2006f1f00f3c801418a4747fe41f671a46803ce8f7961e8f958b8fdcc46b0f91f2b2d4a08fdd1ef4605ccaaf906ba3e47ee91d306c93f06ba475e06401e21e93ffc93f50aa0fcfff24fe7919c6403cea03c094149fc70150aa03e495a0841820c18e6e737927ea1581ae941293c8214a09cddbc691906a038f030c19eb8208649face507e1c7927f1c3561b24fe0f4ba80e581ba7019256515395c19003f8de38841f1fb9c0635f834d23a2dd8c3c91d61fb4a5e46e1f46801e2901904262f835c6f33ffc82f0f490464a0a0c436706f858a82f208b68d2378a8036439eb5787a68317b4c81f591a48b2d92023f14108eec7a6c0da0ea24b4ff9afc3d2f69410a0c434720c561a83185baf8071d2831af41be0d79c46e1a006e87a63179c06612b154c166bd93be3c738086fcfee0e3733c941380949d8ae0e5 (by decide +kernel)

private theorem part380 : Excludes 0x60000000000400000000000000000000000 0x9f204d9182a0a000000000cc00000000008 :=
  splitAt 1 123 0x9f204d9182a0a000000000cc00000000008 part382 part381 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part385 : Excludes 0x60001000000000100000000000000000000 0x9fa2ca9b8fc402a28000000030000cc0002 :=
  finishCode 39 0x1fc791c47e03cee824fda0839c161605a494dfeb4d312988cd6b41bdcaab51305a0bd6663ff97c4a3cb1d5a6ac547eeb641be7b38b9d69a83f5a6c811599ad456c5f1844178fbd8a72cecc5e4d1963a1c5966693f317a0bda05c0b8f3da4c4a1c5595c0c135aa36e62aad5d666b43080bb902293f0609cdc38b20bd27ea1f9ece81158a82ec7dec22e882f81761d349fcaf1061aa0d020bd46313d5022a33579c6bf599bda6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part387 : Excludes 0x60800000000000100000000000000000000 0x9f3778db822402828008000000020cc1000 :=
  finishCode 31 0x104340c62c8ce13fca26909a0e60bb41386fcd7f1bfe6ad87a4a3adc185e35a947cc4a0e50f4b38923a85ff5abcf6d3d9a09d4623d3579c8277339c364139afe7f1c4751d803ecc397b4ac2527e7010729afe49f94543b69e0b9e1e3b0fe524920cdca701380cc5161f83943a7356c1bae81ca62ff9cdcc4a0e3380c737 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part389 : Excludes 0x60080000000000100000000000000000000 0x9fe15bbba60402828000080000200cc0100 :=
  finishCode 61 0x721b8681a8275c0c928e83458c5b01b22df28ea0fe733a77d8aed5b0e7a77e6adb15df45f14630f4c1ba51f387c3f181b2fa03643a7356ca2a980b7d05ed5b9ea2af32e0a3b586e3b39ccac3b5118c5a1207b127eb62d360e7071dab683f0e782ee465c605ab681116faa0f6f8e36a314779cdce5323bded2f633883f85be7ff0e78b7e41fa03ce53338d5b6110233da4d7e1cf0e9c1ce6afa0bded306da0e6b4d9ab6c63205097b13ef291d00283f62cc71d838a4de477c5c9387a91d69ace2e8f631893f903e83f0e3b10d41cdd26b28bd28eb57524b98e1f89c3639bcd5b49fb91e41fad35ab693f9ab6b4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part391 : Excludes 0x60100000000000100000000000000000000 0x9faadcdbba0402828000200000100cc0200 :=
  finishCode 27 0x791c46403cef82d8cc0b9c7df031c7df1ca4d7b2495ab69475a68324e530314192fc260b4d9416e633949c356c28ecc39503b56d43e7375a6c51d9f06318428eb0fe5a69c6ce6e811969a70f0ea8f565a69cdc3aa2df969a71b39bad082f8e1e73728fc3ef (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part393 : Excludes 0x60008000000000100000000000000000000 0x9ffc5cbbb20442828000000802000cc0010 :=
  finishCode 57 0xe4370f83a0fa07a57c28ea4d661d98bca3e62f87f2c22d85c1926a3bb0e598bd26b0fe4c4a3f9990670a3ed43dc66af831c5cec241ce36bb514776c230e5b0de581503f189f2d5d822f711eaac5d48275c8c31dd97249d73045a8ab09832e93f627b4aded34605ab62b5596c1ce6a2a4fd222935394ba060b926a73706a831e35eb514e1e7297d150621d438d9cdd27f16fd43e8ef58a8fe650fb56e386a49548ab6399e49f9c3528ea0b3949c6e505a3bd6c6a160641501648fe60db357cb924eb58bb4ae2ffc82749bd073160b56d27ed35a0dad5f69997cc396f6b926ad2b1fca09d1dec424fcb233da5cca8176ad8fe45226d739ba3e61dd828d02ed5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part394 : Excludes 0x60000000000000100000000000000000000 0x9fb8d89b820402828000000000000cc0000 :=
  finishCode 123 0x3e104107df86701e29e101d1058169ab2d9a562e7413acb67b4ac2524a5f369dc817413a20d424ddee32c056aef69721c1ce36bbda45cf2d5cdae7e2a0c62d3616fb56d62e93f69dcf711eaad35602b5749fc197580ad34f5b4605ab6b4d203d075986ef636adad34e02737203ba8e2390ec3380d77d1a00f3a60fc24dd28e3cd8dfec558996b01969aa136adacce8398fdd3c1ea8fdd02f34adab739953c35fcd67839b514726f6958ba4fd69a5c19ab6ce3483f7065c2df50dc1c158e9895a9eb43dc63d6c605a9ed2d6adad3527e6e308d5b3f00fb16fe3026b561281dc9925c74a1a5b399cd7f13245bb4604d7ec57839971ded28ef9ed2ce31862f87ee62f926eb4d485cd5b5a6b08ce2f8b6318d2d9ac262f592b994c163f75a0c2e62334dcd2d2689bfdc93461cd6ad0320c43186257b4cd5b0609c6e5a6ab89e2d08272d2cb07691bd445beb4d7b4c047691c606595a36d68318736aac568c3b994e1a70d8dc596c8db732ac1d6669441be6abc1c565ad578c4b18bd6c6816837fc4af7b4873523a737733c6a738ebda569b399dabe91d380b57e0e6ad34d7ec42d0d57380a4fe1ea9a9e58b9695676b4999c6817c5b18c30bb483f7731c0b339b9afe612a84d69a1bd729d07939ba09cbe63d55a6a606255a126a5a5960ed237a8a36d04eb4d413ce418d7ef671d18324c4b0ef66abb57c7eeb4d305ad06bf37fcd5b1ea9cdc39ab4d6afc2dd (by decide +kernel)

private theorem part392 : Excludes 0x60000000000000100000000000000000000 0x9fb8589b820402828000000000000cc0000 :=
  splitAt 1 123 0x9fb8589b820402828000000000000cc0000 part394 part393 (by decide +kernel)

private theorem part390 : Excludes 0x60000000000000100000000000000000000 0x9fa8589b820402828000000000000cc0000 :=
  splitAt 1 128 0x9fa8589b820402828000000000000cc0000 part392 part391 (by decide +kernel)

private theorem part388 : Excludes 0x60000000000000100000000000000000000 0x9fa0589b820402828000000000000cc0000 :=
  splitAt 1 127 0x9fa0589b820402828000000000000cc0000 part390 part389 (by decide +kernel)

private theorem part386 : Excludes 0x60000000000000100000000000000000000 0x9f20589b820402828000000000000cc0000 :=
  splitAt 1 131 0x9f20589b820402828000000000000cc0000 part388 part387 (by decide +kernel)

private theorem part384 : Excludes 0x60000000000000100000000000000000000 0x9f20489b820402828000000000000cc0000 :=
  splitAt 1 120 0x9f20489b820402828000000000000cc0000 part386 part385 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part396 : Excludes 0x60001000000008000000000000000000000 0x9fa6cad18ec541700000041003300008000 :=
  finishCode 31 0x12074127ef81a0b62045fc76127b2d3505e9411ffca45969a59d417ac352835fc9e31cec1c475a4f51acd18135fc1cd62ab4d153c4f5586a0bd69a821691a00f3a5068c3b124e6e6195b161f2d34d4eb3b4a08f56836c61957cc1e71ffbc8da388b0792261bd395acec3a61e76818932505a7e62f41787158770f556763ff905eaf90e0c82f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part398 : Excludes 0x60008000000008000000000000000000000 0x9f745cd3b20541500000048003300040000 :=
  finishCode 29 0x1f47c18c6f09fe51d608c93739bb0466ada87da7f07349f8fc5906e0e6f0fa4a3ec118e363e940cca311689cadd0671d46201aa4ed925660d60ca504c5e4cf962e9ed72ea85503334fcc2e619387c1cd39bb0893f9aba9352769bfda7e737387c0c7276b201e9695c7d16ad8b9c7f2c6228c4989d6d5b9222d2b49fb4ae (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part400 : Excludes 0x60000000000008080000000000000000000 0x9f20d8d5820d41d14800000003300330000 :=
  finishCode 67 0x7c20c741fc8019020fa3b6614b49507e93f50083c4822d25981b1813ffa7e51da1e9078c10c8391e4108f5507e1d128ab78da3401e76aeca2139b9474f572d45492d5b1a4c0df722b91d26a935a30eb513ffb57563a93f641ab7075521680138dc3c56ad8a6c7127017d1a46d01bb1474a3ec8391e0f4b0ddcc683f0e4942d48b0b2dc8a0db83d28311f8832e162a0fc3a3003400f1586c40761186f4e6eb0d9882e55203b08a478dfe737694c51f820e1b1474a3ee81f0638d9834e37388da3480d76803cf06d8e6ed4398868056724dcdff06d0dec1b6839c60646ab56d58741f8165c1b61e2b4949a2d5949fac5e7319b560db1bfc39b398da0692cb178c3b5750321cd6216c69fcb0f4a0acee69fc1b434a3bd6aeca15 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part402 : Excludes 0x60000000000008000000200000000000000 0x9f20dad182a541581005050003308000000 :=
  finishCode 63 0x3f0a241893f7c1a04c2084089c3629383c43cf101c7e3107ca12a3d9ea2b0d20fa045a0691d06201aea3d927a1cd386cd5b7b79cde0639bfe6ad86f60e3182d47a0d7820b932804a4e50957fcc3d1e29bfc1ba1db681f476208386b8851d612c72b0f3a8f6732c8218c38654e562bd41fc509293907e0648345a7f302d47a0d720fba0f83210036841f408c5154eccd6141f8fc4a1681141fcd47285a044a4ea458ffeb25731947483ee22b00d74a05bab1d9ed6b2535fb91cdaab4335fce4736a9fe5abad5b8daae63621a0690c601731a4f439ab33945290762ac61d27ab439abada3dbe606b57547a9eb3fc94743cece3e1187943ad5b1c49b5480ec0350e592a065c8f398c7530564daad5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part403 : Excludes 0x60000000000008000000000000000000000 0x9f20d8d1820541580000200003300000000 :=
  finishCode 135 0x4420c5a6bf8f8378fc107da0078b481e7880e737203c6bf6ad86f4fbf357480eda101d5ef28f569e5151b8cb0d285b56da0078c41151dc82f078a4fdc4751b46901aefc079d186adc6bf2769c051df289cd7ed5d1e9c7c2cae5a0b5765617c74127f391dab22d70e6980608671a5b132dab68194a39b566adb91e159ac749966ff690ce610e69804e1f1cdd88641abb1afd24a1bd0e69b56300b56d24a925988681f80e6b0664a0a8f4e1e72b69dc93d623bd9e0e66015b1abb1f3d49e9416abca29461abac5f8976a29305cc8368d03e8f679ab68312938fc4a127df907e3f1531b84179e118196660d949fb56d452a3b927e1a59852d5b49f836e28a8fc6418b68d024fe488a9143a651d0e9cf516ada3b567693f59dc94749fb190428066ad8794a3a5097502c7356d27e0e3167c61787d20e37d1f06e1905f080f391c37a2cb285945600417c3d537983c43d2da3401d58a4ed579282a0749fb9166d18c7f0a3ade2d463ff9c0477a40749fcb49733acec1e2b3b927ee834b639b87a58771cddf8723a4d60f49cad26b2c960c284c41f078a0265038394a12e2368d0079d61f0dbdea30794919b54e1a0c77e188524c3d538097ce691b55d4925db96a2b6308c81cad26b2ced032e6305ca4d66aeacedc8e1bd9c8e1cd49ac1cd68149f461d65ae676aea06439a4ed9ccea3d7f1a006b907cc2f34fcc4a81950dcd3d524a3de524836505e0c9 (by decide +kernel)

private theorem part401 : Excludes 0x60000000000008000000000000000000000 0x9f20d8d1820541580000000003300000000 :=
  splitAt 1 57 0x9f20d8d1820541580000000003300000000 part403 part402 (by decide +kernel)

private theorem part399 : Excludes 0x60000000000008000000000000000000000 0x9f20d8d1820541500000000003300000000 :=
  splitAt 1 79 0x9f20d8d1820541500000000003300000000 part401 part400 (by decide +kernel)

private theorem part397 : Excludes 0x60000000000008000000000000000000000 0x9f2058d1820541500000000003300000000 :=
  splitAt 1 123 0x9f2058d1820541500000000003300000000 part399 part398 (by decide +kernel)

private theorem part395 : Excludes 0x60000000000000000000000000000000000 0x9f204891820400100000000000000000000 :=
  splitAt 5016 120 0x9f2048d1820541500000000003300000000 part397 part396 (by decide +kernel)

private theorem part383 : Excludes 0x60000000000000000000000000000000000 0x9f204891820400000000000000000000000 :=
  splitAt 1 80 0x9f204891820400000000000000000000000 part395 part384 (by decide +kernel)

private theorem part379 : Excludes 0x60000000000000000000000000000000000 0x9f204891820000000000000000000000000 :=
  splitAt 1 94 0x9f204891820000000000000000000000000 part383 part380 (by decide +kernel)

private theorem part377 : Excludes 0x60000000000000000000000000000000000 0x9f004891820000000000000000000000000 :=
  splitAt 1 129 0x9f004891820000000000000000000000000 part379 part378 (by decide +kernel)

private theorem part367 : Excludes 0x60000000000000000000000000000000000 0x9f004891800000000000000000000000000 :=
  splitAt 1 101 0x9f004891800000000000000000000000000 part377 part368 (by decide +kernel)

private theorem part363 : Excludes 0x60000000000000000000000000000000000 0x9f004890800000000000000000000000000 :=
  splitAt 1 108 0x9f004890800000000000000000000000000 part367 part364 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part407 : Excludes 0x41020001000000000000000000000000000 0xbeb4de9ea812810c8204000200000000000 :=
  finishCode 73 0x7f17c5718c5807ceb238c321cf5a6a0e5d04ffc2ff57facacc46b2b924a1cf6a1e47c1845a68bfd697179d22eb3595ff353d68260b5a6a09e695ad35aae83761dd077696b065036d5b40bb58506ec83c8ac3087215a7c8250e7b97e584b97e17fa80b21c0c617a56968196adcc49527ad3663148728ed6460b75a6cd576aacb4d61208494cd61732c0b7494ad5e60fb0a540ea0d9ab64eb5a6985e085a6cd4f30cb5845fee83086192f3cc3b4949ade494c5f35010c3818ab1c85436b355a5b18942cc65a6a90c77e5c7275af8721816ed2d96af1b7dedab3941ab515e46518c2eecb23412b51c39eafb9a56b4d412cb239aaa5e1611e456039f2924e5e83b412b4ae0e7a4a66b0ac26 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part408 : Excludes 0x41000001000000000000000000000000000 0xbc26da98a00201048200000200000000000 :=
  finishCode 113 0x3e0e2390f23a0ec3280dd06fad360e9987d62b287dab6611831fc7afc7db6ada87d0522f518687bd78510c72f5049c9548e5095a6ce530e98bed786d143ea33640a12b1f8e66b4b623c7b3510c1cd032623168cc47969a1d3851d80f7bdbe83d82ddebe5d759aa0ed04a311591c5d7519a51e51998ad00a1df802086adc52759598a4c562fb7416c17ab18c80f9c9c3175dcca9f759cb97e59cc7d589c2c29627a8c5044a1ca331f3cb395a5ac851f5e0c26b4d8a3a1c7969ab4d948ad55850b8e84240ca0a8db45f1e46703ded5b8c561d330fd04140617da50e1d98bd54432d35a8a2fb0f7c1005582e68052808bed6732d34c03356cff23a518687bd946d1e45f03dec5983a692985f704140617dad2e0e38bd6086a3c0550b9a014a022fb17acaf7591cd5b18b87bd946d19c611fc8203de3ab969a7b341b8c1d073071d6970bec38e5b19616d5b51dc5ef5a687be0857fc8293158c445eb2ce562f16c501318759c8c5c3de62996ae61f0ef839dc86401cad5b91c6a1f41c9404a3e807906f039cb8ece388d0077c3de925969b1813848bbc7ab20961468158399c619312ab862f41bcb2757dc809276ce6f3059cbd64f0f9ce5e7f72768f36399978c5de1ef (by decide +kernel)

private theorem part406 : Excludes 0x41000001000000000000000000000000000 0xbc24da98a00201048200000200000000000 :=
  splitAt 1 125 0xbc24da98a00201048200000200000000000 part408 part407 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part410 : Excludes 0x41000000020000000000000000000000000 0xbc25eb91904004000412080000001000000 :=
  finishCode 85 0x200852087d1fc831c418bb6830d5503de7338bfe7339cdf0f9cdee913691c864143ea471a8cd5b62cc1dcfd251f69dc18b6adac460ee82760598954c413a4fd401f39ade3eba344ddb236cc0318966e01ca6198c4a7219b8781b4761203144c3ba0dd6413db144ce4251f4a0a26621776629b1551e7460dc925dd524cb274f5a40546324dc1ba1dd6d20c399a685c78d5aa492ee833d202937479ce678c09c2527ec3d62aa8be067a3be308b68bc1cbdc832c6dab6a3149bb92e506a405cca8ef8c22e43787098c320cf06cbf81dd927e62f49fc1dd49fcec07bd27f038c7cf234527e8296e01cabc07741baa31928e9019b45e0e5ee659416709518a51c98327ddcaa9018c19efd27e709477c6116f1b80f7acd6729b0f58a6b4f067a0d41bad4320b218454c72fa18e538762b4f627867c12739bd89eb23969ee4b941ae53964ee65480a4ddca739bd48e9f589eaa09 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part412 : Excludes 0x41000000000400000000000000000000000 0xbc24cbb3822080080000104820000000008 :=
  finishCode 113 0x2d0881c8c62d35443f19c49faf8ba3701b30e39cce598a3a54769df8d93063780d9877e3e77d1b80b1ce6518397bd3d62dd28a97be72f855d477397c3b70365bc7f0d9323a5a6a623169ac350161db517c80b51d835cf7f399543680b51db710a187e4a1987e405a4662eb987de46f19c06ec1d30efb70f6d81a2b4f4a1a02c1bf1efd86e61f761b8303839e30f28f5edf16d4fd71873dfc90117db17e4a1ad3cc3ef23b06139a56c1f596874c1be0d76e05f72c8c3a662f0e9c1db596c929068bb0dc378fa03441af07985ba61383cc1d97d01cf311c5de30157fcd2b6a2a02c3df038ce5f2384bfec47317a88de24fd9c06ec1d30efbc071791de61f06f987e2ce87bdd8640b6a0e7527d07538ba404e670758e129013dfc9017a896d4e2e5157d165b399c3a60d77b796d43de0d798c3f1b849fb78be3f87f7838e3e70e3c2d30e7a43651e98bc1aef80c5e405b57d476a3d303949d28313b53be2fb303c3e76e208303ca2906e949c3b7032c1c7076df45f1b817dc0dd28fc005b38e2e0e50f7cb5383ba2fb06e834606cbc8dc3b0ce035da47277d25262f0ed873ce6707bc197073d41b392dcba1d30f79cbc58b24c47ce0d1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part414 : Excludes 0x41000000000000100000000000000000000 0xbc24ca93c20c00820020000000010482000 :=
  finishCode 93 0x20c821f0761c47d1d0309b70e40bbd69b2494a3e1ef924b18a5e4314a4fe519a4d528e2f928fcb2b641fc7205fee83489e033d40f24c5286c37923ee65904ea492f0ad35ab61dd5abc9431f39a7658ba47c1869432e3a4fdc8781037356cd6e0d90ee8716399a50e517971d69a0c349fa09e58ba4fd69a2ff7905ff0c5dc87818c640a3a3e7969a1dd498c8276abc51f5a6970931927eb4d36f9ade2709efc38a4f5496cb4d6e1c8392c2fb28983065a6874d27e50992029252f7c28fa3901ef4a14457dc62337d9c95a059ec1cd397988d5f6ac1cbe62ab57e737a36c933356da4658f34db02d3d6b3d1f39cbc7cf2d3527ee43c0c8035cc1718bce4a72f305cb535a6acae4159ccd45f206d27e1df927e0d7791d00f7a4fe1f3835c18f20d439e3e7741c8523c2f506483447cf2d3527eb4d92620c3761e07d14372054a2a0dd072b88c8036527f206ce2ed5b179a47e5a6b56d27eb5758bc9315abad345e61d38e662f36e0e2f250ce6651d27ac1d3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part416 : Excludes 0x41000000008008000000000000000000000 0xbc24dad9861641109041208041208040040 :=
  finishCode 41 0x278883e8b4d7c20c761e4586c81b494b56c3de311071ba06131e4cd5b0688bd562f1f6548ed5b4a1a0662dab56c61a6e90f7b56e384a0641c60d79abf2c550321d906bb70fa2f8aa3a050b7616831bdc1ca7b38b6a8197338bed6470c445df18a5d006fc4d137b8754dd32ce588661d7901b30774e260d19d8179cb15315a066741d87901bb035d62b27b41a21d5504ca2140c8bed22318ad8821ef (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part418 : Excludes 0x41000000000008200000000000000000000 0xbc24dad9869641149040000041249208000 :=
  finishCode 107 0x781b0d216d5147c1edefa410dc039e28a8c44a3ab4d8a120c783dee2032658b83645ff076569aa4f87aa0d7791d86e1f006b8bce072a50662a9b26302705397b4e60e9ad5c1c650983ab0345f07613c82164681697460569aa130e8a93c9d6509527cb4d17f98a63749c4d69ae6583b20d95a6ba0b1787920d9303d1810f7942662ad1813829cbc1ae9e221042d35f0681f4710a12ec0bbc62f1a84c567f98bde1c1944f28f41cf2bee51e835de47d01c707bd0330f2439ab2383b2f8340b23e8e214254371ba4c5650b89d7289dac32bdcb3ea0117c98a437ac4d83de6f7374c5db51ebe8f8410da18a6188944ca3ad2d962a1bd2858bbd66b1fe418eaff0ea835e06bc819065a78883e0b4d7d1d879168728cc5f662b284838c5eb0f2540e943284a49617d9425277281c1b20d79f07d1a06d128723fc1ba527284ba02e9944230d37ba90d8b3142cdd262949a8c46068c0d906bcec3a0f2037606b87560d4c5fb314c1b6729a4d45f6513 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part420 : Excludes 0x41001000000008000008000000000000000 0xbe24cad9a68641349041041049209008040 :=
  finishCode 123 0x600784f0b3a883e0b4d7d1b4820e130c449eaa33948e1ef5f1c4470d1872eb8674bde8fb8382943243c8fb1e28c44e2713adc4390c1ef729c4871ea9c25b8791b4710c3b07bd0360c76afce531ea8bfce4a61d92867e518886f60639b6e51ab16cc56ce350d0031e0e9833cd373964d6f0750f7a3160e7a506591984e30ec590f7bc8e23e9063680c7969e1d30f7bb10418a6188ae0b23906a1bd41dcb4d8bde1cf83b68ed94426b741a832db4729c4af1ea8bfce4a3d5920a4d1621657177418e0b9063c240a89e0925107c169ae23c8da18ae0e987bdd8309c7fb83a97be519c9e32eb98ad467250c24f3d54c1a7ad0f7bc8da38861d818e1db389c4f540ac6f7519cd55063b68f2074e0f7a8c6315b16419f07593c441f05a6bc90428c6188ac8e41a87bdc450fc0c72eb98ae3031eb518b3d54e667ad0f7bc900074e06593d4dee83b93eb07b3518f56315833db4790c5329143dea098c56c590678f162ebc1d53c441f05a6b40800f56248a9149c2e6f946704181e47498ac622b4fa3026cd04591a63df97fc1067b30f7c18e220ee18898752631c94dee3b3818ef2355650fa9143de7bf9672c59 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part421 : Excludes 0x41000000000008000008000000000000000 0xbc24dad9a68441349041001049208000000 :=
  finishCode 79 0x600d86e0b6afa3e0e23c8ec4101df06e9876188942d02b20ec5f7142ca3aa3385ea0c7072c50b5f01ae907927a7175149ccd0133880c981ae60b9aaea295138735fc504c195732ad34bde709071ac8e59c874d69ad5b4413c85169ab0356da0275ce653fcb20a4f9ccab4f0d28e451db050dcca3119abee65609c1dd1ea942d44eda338d4077e065877e06bb56e3fc834548f356c5dedc3e8f82f87c98bde6292859455b46afc2f92939ba630e9bdd4271eb60da1cd51e835c39b032d89b18acdee8a3e0f517b1b88f23b0dc4100dd30ecb394ec949cc56d5b906ad5b91da629384837d69728c4a1304316618398ad647356c5ea50b9cbb2d341aef23e0ec3887eb8e4a6076adad341ba0df073ca458bde8d128493b657dad341af0407765a6a765ab662b2938346 (by decide +kernel)

private theorem part419 : Excludes 0x41000000000008000000000000000000000 0xbc24cad1868441301000000041208000000 :=
  splitAt 5279 120 0xbc24cad9a68441349041001049208000000 part421 part420 (by decide +kernel)

private theorem part417 : Excludes 0x41000000000008000000000000000000000 0xbc24cad1868441101000000041208000000 :=
  splitAt 1 81 0xbc24cad1868441101000000041208000000 part419 part418 (by decide +kernel)

private theorem part415 : Excludes 0x41000000000000000000000000000000000 0xbc24ca91820400100000000000000000000 :=
  splitAt 5016 99 0xbc24cad1860441101000000041208000000 part417 part416 (by decide +kernel)

private theorem part413 : Excludes 0x41000000000000000000000000000000000 0xbc24ca91820400000000000000000000000 :=
  splitAt 1 80 0xbc24ca91820400000000000000000000000 part415 part414 (by decide +kernel)

private theorem part411 : Excludes 0x41000000000000000000000000000000000 0xbc24ca91820000000000000000000000000 :=
  splitAt 1 94 0xbc24ca91820000000000000000000000000 part413 part412 (by decide +kernel)

private theorem part409 : Excludes 0x41000000000000000000000000000000000 0xbc24ca91800000000000000000000000000 :=
  splitAt 1 101 0xbc24ca91800000000000000000000000000 part411 part410 (by decide +kernel)

private theorem part405 : Excludes 0x41000000000000000000000000000000000 0xbc24ca90800000000000000000000000000 :=
  splitAt 1 108 0xbc24ca90800000000000000000000000000 part409 part406 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part425 : Excludes 0x400a0001000000000000000000000000000 0xbff5c9baa550a08c8014000200000000000 :=
  finishCode 91 0x3c8e42e8ac208b01c4d47b3155252825397b18b235a6d07551d9fbd69b20960e79c84e5e70218b02c2563f1878daed2b8389c9569ae4b730cb0b6b1ac0d4370ca461e05b873d25293b3417c2309d7399ce4a6d76278e6640db0a5452c59392acf67229f25cbe6d759eca2936b9c9594392b98e6adb1663021cf3f5cd2b593b9166a2a02ce4a6d79cc2b4d5f18c67160650e4ad5f9672b5357d8ead8b25a70e7a81e697acf58b2f6995f67ef730873d6831c95617354ce4a80b9a8a5c2f0c22b07ef9edeb4d489acd50768256a169a863dc5037358d63e81b9a5ed5398b2d61834ac2658fcb39527ad354043114460fdeb35164cb396a2a02da7b1818e2f206d076d233f7ac7d58480c8f351da095453357d4767ef98c2e1ac3202d2861cf5a6af8e459cc63bf0e7b50a299a7290d695a8ed286a299abe825591a50e72ead3584631785d1b805693ac1670759c7ad6183ace596149a09319882d6156163ef6b9a5a6d71629f266abb56cdae943696ad3567334b65a5b585286d2b5a6ac26 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part426 : Excludes 0x40080001000000000000000000000000000 0xbf63c9b8a40020848010000200000000000 :=
  finishCode 99 0x831a0801886e1b417db18ec14758438bc61141aa06ce367178c22c2998b2d6150f93d4a3f291c1ba8059ed2f7138e8375947617c5e169a61330f86fe518b9760e9bf0b6268d5398b63db5889c3d683f7ce415889cdd69a71395030ead3669c9425a731fbe5a69424c3a94320a4759ac7ef397a7dd6727ef969a9f72f7cc63c0ce2c9ca1223d8b1671b510b97d246729a3026112f6ca1f38db13ce4a733732cafb593ac56303874d3ee70d30f8bed7c5e1c86a190280c51f30898ad50309a446387a4d4e6ea4728ec7eb488837672093d4c0ea45523981e315874e39bb554c3e6075b1845a18174605622d233949cddccb356d672527584cd5f91fed3958893fca3abe2c061f720a2b2414bde7095799ccd5472ecc29372b56cbde501584c9056adb56e2f794053c6b041d68c3ac25cbeb4f4949875f84d1b838083763f7acd5077181969eb420d659a93453cab4d389c44036e58fb90e389836db45f1e0640e4b065d66a72128a947dc731c253ef069690a91d69a1d306db08ca3401d34fbc7295a8c80b40dc7375a5caf9900a713293836d69f27dce020dd (by decide +kernel)

private theorem part424 : Excludes 0x40080001000000000000000000000000000 0xbf61c9b8a40020848010000200000000000 :=
  splitAt 1 125 0xbf61c9b8a40020848010000200000000000 part426 part425 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part428 : Excludes 0x40280000000000000000000000000000000 0xbdd75bb1d40000000000000000000000000 :=
  finishCode 103 0x6e1d817dc1e95805dec83d8b81cbce663f1907e6e5963e93f8b82d3f4918fc5344410c607a4052271839a764b508fcf714315c3c14c5a3a8be6109ffd67b2cedcca8f386cec0f49ab5867329c2526ab519ccabc1604b99412782d1e8c1b4edc96f69376ad4d48b3d663073995a7eb27631246b2798aa80f271cc55761905e130650c22f618ad4c5a9cb1b7a9a4fd03e83185127f2d3c9a3355e615b504f665a359ab98d27ef62a0b0d92469f56ada004de683f5a7c71340f9c3e6ad92d649fbdb5ab661d315b28c6298a8187c7e33db56468315a6c81f8c18f0d622b238511c30fc4b8293f59185f649fbdb4dee73396223f15a6aa0e5f37bc83f83fc93f591af89a2b0ca240524ae639a521c772fb564ffeb4d732c7ff8e52613631bc5e03a7181927ea31732ce418e1293f5a6d0a2a0781c04e6eafb96228ff8b56f6b5a6c60d27e93f9622c6158a21ffd1ff16ad27e5ab969ae6562ba7d6732bda569ab4d99c7b1900e9cb4f390a03ce5eca248e3d6b5652021d33ffad3578518c947732c39f9eda5ef492a51dccf23bc7e272f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part431 : Excludes 0x40081000020000000000000000000000000 0xbf65ebf194c810618016004080001000000 :=
  finishCode 63 0x2d09036893f8010c670e13061d86634e63ffb13daa68ed989e9350679ade408a87d2226ff6149ccd1e712d5aa60cf50fc611579a04589efa320ac033e37f8714e6671b98b29a23ce5a8c1d6067a3cc3732084e66dc20d641d9ca419e19193ee61138d9846395bb0c81c6da80e0c611415c73359dc0cf415b2118191e6d5d614b13ce4a7335e128489ac9627aac963edac76480b6900321061c94e668e19ed2a1f2e3b0a4c22c4f0cfc8e1505971da86f158067af086244e0ff3d64fff077368a4d564b3da4f96f77479ad46480bdde27aa3ce58ea7cce132a07ff9c9682127a9b467b6b10419ec823ce62c9c74c228e191de71d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part432 : Excludes 0x40080000020000000000000000000000000 0xbd6579f1944000018012004000001000000 :=
  finishCode 115 0x801a8761900f4bd8b0300be0fc5ab72cc522261140f9c94e66e5f964eb392f0a0fe397b97cc22a82c882137ba0fd69f1bcca1271d9a52af76adad3e6adabdce2681f395cd5b308b790a298a8356cdfe72969cc93f5239705a732f09a398e470b56e0ea72b69ca4dd68f392d27f18116f9424e573995a931ffdc962df518c9017d18c5e1a42848fc6518a4d4a3aaa20fe6a9a90d816a3549bb14d26ab259226c115c190397d1817329ccd202821293a0fcac36080524ca2f6079ffd636e658d42b47607acf6506b08581e7e12d659db58c2569018c0b09dccf28358431814809ffe293b483f18a3eac0fc4e433d4d202e4962aac7e6aeae0ac0fc45bf34e526ee6549fb58ce42f6180b6e496b1a0fd58735ca435109c4d1de8a349649fb5752233d8be2c0913964a5091f89c25b87d190760a3ec6037564f20fdeef27b5eda13d488abdd5841fc60e400b956302f77488b155aa746056963bf9ed2b2762a9c865a9b54d8ae0d9540dcb277d5f6b27410ac9e6401b212d8e1e7d1408abee593b709ed9ab681b28f9475506adad3e6a4a51ce571819bc6d1b8750a3f14741baafb93ea81528f94757863164640a128ffa302d5b308a3fe308c2df59ebda5ede71b4a39c6e720b56cc22a62a072938ec7d141fb99672ea07d6a70b7dac6e47395abdd7c395a4d6523a51ce1f2826 (by decide +kernel)

private theorem part430 : Excludes 0x40080000020000000000000000000000000 0xbd6569f1944000018012004000001000000 :=
  splitAt 1 120 0xbd6569f1944000018012004000001000000 part432 part431 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part435 : Excludes 0x40880000000400000000000000000000000 0xbd71e9fdc62080020202204811000000008 :=
  finishCode 13 0xda3c0d23a8ce03641971c2439e51f8e66b4d8e260c91f4c1e957b8365a48c0c93f835a50d69a0cf0e7ad3625aad455eed5d96a2c0957ca8341ba1e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part437 : Excludes 0x40180000000400000000000000000000000 0xbfe7cfb9be2080000a03004803000000008 :=
  finishCode 15 0x6d1e4721e06301baaf7967a2df0e9987e59eb97d672e4b72ead3561f033c3a6a6187e394ac36395caf739ba9872b16fc0dd30984ee5a6a4041baaf7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part438 : Excludes 0x40080000000400000000000000000000000 0xbdf1c9b1862080000202004801000000008 :=
  finishCode 155 0x10a3e8dc2e02fb6414c6f105eb22f87219062b4f303987db462ac831389ad3e838a0c4e02929584ac00db8e2e93b6d18ab2be4e420db259cc095a6a434c0f20c4def0754949c85b457ba4fe7279454e43075922e68074e49fa45d2523bf964a18f49dad45b45a6b780dd961a1d37b5cc3d8c1a02ca2a6076b1cf6b380abfcdeea0d7b4984d683914c5a69d8862a07ff62106306f8e6f06f95ee61f303cb4f6f1888c0cb233f59ca4e6e981b36303b164e1b1819abea1b309a384d422df303cde20c4c3f1c055ee8cfa0dede2f8af73f03a6d5d9ccab157b3a4fd2033dac5bee658d4293f2d5a3842a72404e42c82a0de208437f1c843a6af78c0c71339986fe591b78a62f89a39060e99ffd2026133ffce410e9bdbe720bdc4ffe729724cc0f38093443a6e678286f514809d0c61bdd501edd06f57ba0fdedb41fd3eeb238c0a07d5ef3d4d1c2e413998fc47e320c5c8681e0761e4751b85d01b21e9611cc535a9c1a66b0c1b4e2e9015623032405a7a2df36ba03ce427331ddc725407a4fd69a1e98e4a3f11f8cd2338c60325673203ce4b1c96586cf2250e480a03d27e733417cb4d418b50e61bacd520a717407a0bda46e18c582ce63591b03c38e93f061ac06a0fc4ddb2c1568ea07720cb475a7c6d7730b15569b071d61b370ec378fc1c960f48375d45801b6b420bc7e282196a2b4d285bda6410cf697329bdd05e52787e2a60bbcc0f184d905a1ed3276630f0752e0a8f527e35d901682137bbda4e431839656f6957c874e177ad05c320b4d6d16440fa4fce4b07f9eca1d330fa0fe2e0c8212e0cb577209c25bc6405be7258fb63f137b9ffe7b7c1470a9a4050426ad0d9b68b21c4d003181c79683f896b41d50626f7 (by decide +kernel)

private theorem part436 : Excludes 0x40080000000400000000000000000000000 0xbde1c9b1862080000202004801000000008 :=
  splitAt 1 128 0xbde1c9b1862080000202004801000000008 part438 part437 (by decide +kernel)

private theorem part434 : Excludes 0x40080000000400000000000000000000000 0xbd61c9b1862080000202004801000000008 :=
  splitAt 1 131 0xbd61c9b1862080000202004801000000008 part436 part435 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part440 : Excludes 0x40080000000008000000000000000000000 0xbd6149f1860441000004000801200400000 :=
  finishCode 147 0x3e90637100340be0becc0f0fc4a162ef6a077b41c569a7d10ec8354c3b075900ab4d2899f45ec6d17c64160780e6662938ba89e6a1945520b1c863159455e07516076127e7096adc82b587c60d6868155a0874e61dc0dd5a6a4fd21b356d28734fdeee7db49f9c2521b1c4d69a0db6416006ecb3b30e98a5f8315b58e3faa0bd86aaf949fb4e658f805e0e2b4d410a98613921ab3b9056be2c850b7610572cad84a70141d981cbdf356c7b6d5b9c96b2561da0561451dc93f606c1d41aa815380c60683895f40130754029f441aada378d417063868324a3a0cf7817c28ead36303947d69b28c6245a4fd48e8115a69b4527f1475bc315c80549f83743aa72b49fc81537998a5ec391905a6a60780f6e6adbd455e68ed1f897bcc0e801410bb093f969e6a12849bccc5683130e874e49f93d5d837bcb396ad98acc3ad017be284a4fe399a0bcfb6da2c8709927e5ab732b56d1da7db284a986a1926ea3139b9ffda732495ecef6b595cd393509cad904c0a131c95002821791b42f7c6073929c8524b16a5ab66f731593d63159f8be24fdabb461ded69377b1874d6ae1818e36d5d924a6130e9af8ec2c8c8340607315bdae57da8c4e56d6387b6d639ed66f31ed981d462b2b9ab6a31314b403f19a7e509518ba8b22c03db6a1c37936da3858b2d5b914476cf517b1b56d8b2d4372ecd4936dc5ef372b58ce031cad8c7807d328043d24ff28eb789424fc19693b969a94351acb0f58aad3527f032e28f9c243d2f0340dc3381e947fcb4f697a0fc7e20c9392cb02d361f893ae05da4fd8c5c12038ba0bd1db1cce30e929579a4fdabb284cd6ed57494a8ee4829c5d27e73381b27135a6b40f2391657b833d27e1c53999f88310e0ad5e50da4fe0eb20bce672d3527e82f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part441 : Excludes 0x40080000000000000000000000000000000 0xbd6149b1860408000000000000000000000 :=
  finishCode 109 0x4187317d1d85f164303c6136e1a01eacd4928e947c5dec82c05158e2e515876f2c941aa81564160790c526d1928ea1d4929ccd27f2d35ec05dc7376ada0c5a73358dab6947379bc8f6249477f1c256c6ad8e3e5809345a9323b471f12d45bed04007138d5a1930688fc5622b3d28e8bedc85a9c0dd38794750371c3dc875127f41d41aa0db7e1ab70074ffe82b3899c04e27206e83ab56d06ae43c0dc0efe57cac94bdeb4d16f9454a3ac81c266ad9424e5e80f492c1d33ffad34e2f074ce66929907e2fb2f7874de0681d8721e46e0e4324dce660d90f4ab0713928ed5b3998b7e5a6b56ce4a3f198c6a017724fc186b624fd07f071dab7171d105a0cf6d40db56d69a3b39a8ab3d1f8b90ce0b7d841f8c1cf1f8c80f35b9c86275830e4888fc439ec62d881f905ee42e8de39766ad9faded27136af83645be733906b357d27eb4d5a6c880366695861dc82d5b5a69c4e0c3b92d036861d8ba203dac702b527e7337b4c8cb418a3bcdbf02b527e733417c6062f0acace66b014a182ede0761bc389c72106483660d71c243d2d01c9605e94752531ccdab6de0b265a6873d2620cb49fc733 (by decide +kernel)

private theorem part439 : Excludes 0x40080000000000000000000000000000000 0xbd6149b1860400000000000000000000000 :=
  splitAt 1 87 0xbd6149b1860400000000000000000000000 part441 part440 (by decide +kernel)

private theorem part433 : Excludes 0x40080000000000000000000000000000000 0xbd6149b1860000000000000000000000000 :=
  splitAt 1 94 0xbd6149b1860000000000000000000000000 part439 part434 (by decide +kernel)

private theorem part429 : Excludes 0x40080000000000000000000000000000000 0xbd6149b1840000000000000000000000000 :=
  splitAt 1 101 0xbd6149b1840000000000000000000000000 part433 part430 (by decide +kernel)

private theorem part427 : Excludes 0x40080000000000000000000000000000000 0xbd4149b1840000000000000000000000000 :=
  splitAt 1 129 0xbd4149b1840000000000000000000000000 part429 part428 (by decide +kernel)

private theorem part423 : Excludes 0x40080000000000000000000000000000000 0xbd4149b0840000000000000000000000000 :=
  splitAt 1 108 0xbd4149b0840000000000000000000000000 part427 part424 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part444 : Excludes 0x40100200000000000000000000000000000 0xbfaa5cd0e01600801000000000000000000 :=
  finishCode 145 0x1946c140820e62be3e0c8142e3159455a0309bf051d943a7372d4cd63523a49502b2d25ab6f6340b4d640e6e5c1817a82b8de6b3b9aae82b6811839bc6066ada0541932056351a0ec9dad02d3584790e6e9d9963a5c10e6a06dc8b1474f5b149cb826f30e6b08af998a682b3d6d1837b3a8d5436c23207375a6c71b0e28755037356c3ab3e1043182f9489c61328ead8821ca506b356d8171875a9b1566adabee6069195ab671b60ead356c541842edc0c71f79cde3071f7d6124e14179c3ce532cf47de3a38e36af16b187559071102b1a8d06a72938e83241832d34e1b2f8b6338f80fbe08697c815309942ce1b3d8e302d5b522ad34e6f286d4927015a6be0a1f8c5683b8596f82a0c3b904a83b314a8cd48ae2320b818a5637165c59683b8b2ea4950dac46609ad356a6d5b8c0cb1b6ad96b54167e56b19475c459140412c92541da51c597071895e835695ad360f3348d442925588c3d538dad35b4681f0821abf310c94271b30e94755c6116a69f59cc6d67629b0953eb2c6d69b2d8b420ee2edb02da4672939ba30d239816815612cc236b3a504fd720ed8a6c556afca4350da42cc3a61d9076805821b817cc51d5405f29258a12a079ac6d5b38dad0c22d83ef8e527375f198541ac7075548af558d4f07b608a0ecfca1d56b1ad1e83da8760f2d5f38db56d40f314ce36ce2d8be28760ea8fbd40722c8314a0b6081f9492d390eab4e6730a60d49522cb1b505d18183db57d48ab1b830270f497ad8ce318e80fbcd7b281d45e941167cb2758fc8055a9a4ae6adb156402a86c3aad5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part446 : Excludes 0x40800200000000000000000000000000000 0xbd3978d0891204001000000000000000000 :=
  finishCode 99 0x410e83d89e368821cc66ad982ca4e705389b30d01c8630730bd69ac4949e87343d2619402c731179982e5a6949dbc581b8404b60b41cc58a3245cdeeb4d62bc391467b0263067f7592a8bd41a7015f169f24a5436b3b3809fdca16b25966ab3b3729bde6e1a025ecc316a99c3c3d2b434be402ad35ac650b62163f04fce6270157cca2f37bc7319b48517c7d16131bcd28291d1799454a3ed01ccd84b188d4023d1064a065052d639a6a2f3398b4be72d809d4026d7524a014c322f30f4c527680e62601900a8095a09c71c05ac6af9900ad5b372a80d03b072b90122f30f497fe523b58ca3e3e96e0e622f38a165ff85e6d630f4c2f36d1f459184284a0ee6ad9feca2af734ff9cc45e6c2ba0d2b4d35eb56d66a73128acaf92938bcce63278e5a6a05ce02731741b46e184400c4662550101307650524cb9ab6a2f61eb52541739bd4361d940bcb4f41498657c61124500bfed3987a28394a09cde5015c7e1072b4b89c2d53394a91649586fdab73064d9ab0d40c9a7e0599ca4e1f2d2d2828192ffc941404cd8280d21cc4b531b356460b95a69cddab7250d69ad5b902e4e1366831ce3a8258be6737 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part448 : Excludes 0x40008200000000000000000000000000000 0xbdbc58d9a01241041000000000000000000 :=
  finishCode 135 0x280ca2f0841cc4f0820b830a3b0fa370f2230311711a06206024ed9abe737276cd3d49aa80624f9b6dab68056212172504c32d3d8c16819180ca319ab6a3328f8c1ca3a06787f28192848c45cbb17860de7d11fc8bfdb868061ad5d95f63f93069eb649db574dae1816ad9344bff2f8c4147c35320d45de6db90765d18db683b40a8fe5b86ad97a60ec8fe6395be904428e83704ed9a8a8051808c1dd869ccd451fca064a123176b1c5ef522be05278dfe737188b4f62f1b55ce02da251e177a015226819063949d0131cae17ab20ec0fe55817fb4ae3d6b56cfeb06f41ac1c62f0b515847356c75a7ad2fface5d8695c7eb6ad8bfe30334fd8766d76b1be9043e0d036880998be81927f94750330c5c3d2d499a7ed631868c45c446060341e49da6db40a8bbe69f8c04db7293d61e819276b701d98e562f5395cc4340d2585fed3f3178fe59c6a1c8fb51db4fc5fea3b9ab64eb9476a0117fc110a3e0f22c05ff1868c5da931b95a9ac3740cb05e58fad3da9260790328393958c1da030bc3014a0c5e336d982d7c670a162ef40cc839500c4ed268c9411fcac461dba7dd07272b17abe8b03b07f9820e1f28a49da8191808c459c6b1c72b1dca065ab720d4e6eb1fa0f306f2538ee49da819741b839bce393118c05ac728063879cdcff3410f8147e1fc949c6230a3407018e6e301620f8380a056412982e6a2978cbc73a0d41b6e06496de12588cda7a5e3177bdbe5a497054260c7312cd5f40d9c6c5ea737 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part450 : Excludes 0x40010200000000000000000000000000000 0xbdb8f8d4801204081000000000000000000 :=
  finishCode 151 0x208741906d198520e2672137230730bd60e3b9064986521692f8516830ca93e51aad34c171cc4de6731839ab3b969a5ff30cb28fa360301382c4d1506a92569a60b398ad363059b947ee70587ee7313f4c6d73fc8c05a037bc809180b38ae1b9650d8fdce62fc2d34b0f1af4dee7f550db04e259b4a4f9f0752c3b16d64a6f7a146d1a0711bc180c61e69fa48d032839593ca35311ad1dab6625620c2e839968e61959e9bfe41cab860b5e18c398a8d64f5ac1c7eeb4d86d72d360eab495219c2651aad3561f12cded65e36ad8fdd45e3015f104f24d45de839500e0398931e40492865a6acc51ea80b9636b075a6ac9d9c571406f0e62be460608fc60e0d69ed2769fd5ab29371fba0e584404c60e588a0ad8ab1839622be260af98de6b475a4a4d528ed239692e4f49297cd6231bcdf85f1a01fb9f88078e1e937413a49649bac44be72d3538522141eaaa0c61ba4e02af193feb5361cb8e623cd1835a9b56d1aac23374c60e13091e4f9eb1135e9d86e9900a6af57cc60d676b338dd2c841d6598c60c586c538b6e3f79106817c50124ad5b8be6b4d4a3a06418f1ba437ab4d4e0de7460c7aa72b91fed5b8c1ad36640b0680dd2fc06f586b293cfeb1833799705427310d5f2c5395f23d5626b686f389daa3d379c4ed431a0731c8ed37fa4d564379d183626a3b5cde5e33fac6d58dfe6e999c5b1b474140311c60e1e2a5045ea81930cb516263ad4d4923f7387af8ca1cdc7ee5d79aae0b95a6b98e34f8ef495e731964ab3d3879ca5013280b8202630cc61e35fbdad8a67fb50d8bd50328397117017aa8866ab9894f9741d4b526a7578a0ec996e598c4aafb740d9afa1f8e21c3cc1b1fe4b4a2f53fcc5a55a6c1be00e9694e36b4d0e69bae3fcb50d69a60141ac71d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part451 : Excludes 0x40000200000000000000000000000000000 0xbdb9d8d0801200001000000000000000000 :=
  finishCode 89 0x3a0d834041f7d08230a290e0af97056367ff2848c1c1e6bc181e4a3ac6ca127311c3c2e93ff984e30e73185fed403cce4b0bfce4b1b5d3bed4d3ffa0bce630a105de4681b47d17c17a949d43f29153eb2d4e08660e0a7f99286b39392b56e268c6cd699ad34c1a30d8ff2d5b9286b4d3828c345eb0bbe852087e1f4630622be18ae203b6873139bc70f28e9426307316dcde809690e62c4142e2e09c04e5651f8c3b2c34dfe089303ad35945f0e62ac101d69f38f4ff2a4f5a6b534dd2b0589d6a3b69aad345ff359c9d72c44bc22ff3fc9fe63988c459c631f4203ad0fc3287294a1cb4d398ac36593a025b46509c26cd961a5f34a1ad34be70b3cdab2907318e3a2bd593938649d9cc52871cc5f457160398a0264149fd62339c7502eb112f9ac9d9039ba704cb95f639d8c1b56d6466e31665869bfdab7181969b18337fcd5b398cfa2c363989cdd6971cc57c398c62b284901ca272c44e6261d (by decide +kernel)

private theorem part449 : Excludes 0x40000200000000000000000000000000000 0xbdb8d8d0801200001000000000000000000 :=
  splitAt 1 124 0xbdb8d8d0801200001000000000000000000 part451 part450 (by decide +kernel)

private theorem part447 : Excludes 0x40000200000000000000000000000000000 0xbdb858d0801200001000000000000000000 :=
  splitAt 1 123 0xbdb858d0801200001000000000000000000 part449 part448 (by decide +kernel)

private theorem part445 : Excludes 0x40000200000000000000000000000000000 0xbd3858d0801200001000000000000000000 :=
  splitAt 1 131 0xbd3858d0801200001000000000000000000 part447 part446 (by decide +kernel)

private theorem part443 : Excludes 0x40000200000000000000000000000000000 0xbd2858d0801200001000000000000000000 :=
  splitAt 1 128 0xbd2858d0801200001000000000000000000 part445 part444 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part454 : Excludes 0x40800000040000000000000000000000000 0xbd1b7ad0a08002002048100000008000000 :=
  finishCode 53 0x102410dc368d0076e3119474a4eb4428515072cb3b3799cc45e6b0785aa93d398cd5b379839568398cc49731ad4527e0e5285b600e54f3cb3b3729cc46bf356d3eeb51372bf0f61426072a4fe382c1db284bd8ec2d0647c9fdd2825ff06d838d40671846a7c93b729ad443b69f9969a13b6ada3ecc027311edc91f5199b964f3a47d4661db76127e7298c467374f3c6e548f9cc56874127eec3400e1386cc0f0f486be671b43d9c8e9372ad44c4a1d75a8cd5b4f1cb4d612c1cd3cee6f271b56d81f278da7e4e30ebb68c0f7113cf35743ae0e16705e718bcc169e79a7ed5b69fcb3b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part456 : Excludes 0x40008000040000000000000000000000000 0xbdac5a91a08040200248001000008000000 :=
  finishCode 29 0x32893f501a0398c010a398e2938c5c5ea5278e531bce59d846dee6d4f06a93b614681f4821b8309ce452899c34a4e6ff8a1231173198a4e1b1ca5d0275c2ff6ad97fc7f2ce398e1bf8bfdab70bfe18884ae6a69875426527303be0dc184683db56dcc6311285949c5f3398c622e6389da301 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part458 : Excludes 0x40100000040000000000000000000000000 0xbf8ade90a08000090048020000008000000 :=
  finishCode 57 0xde408f2388f807bd906e14c3089404c3f20c47deb1d9ee69e749f837e3989845227391526ae6306fb6071b969a9e5395a4fce62a633893596764ed521ad3601a80dc9daa0d93ce8ed49aad35f8681845f0e529e796a2d397319f1d27e72b280acf649f9cadb082127e5c7981e83f83fb914e6250b1f7c83f293cb1d25dc80f280949e285b68bc1c3e3989f7d69a50928eacf638e949ce6e50b969a61339bad0ce24fd4c69fc5e3521875c1be3ef7c1c417c9816730a51dcc734fd64b3d7d5e2d5d49ab985a9a1d747cc80f6adba0c0f524c9070eb837d68f16bdaba3ef6adad0ca24fcc53162ca2a731504cca356e5a9962ca3a731308c51d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part459 : Excludes 0x40000000040000000000000000000000000 0xbd98da90a08000000048000000008000000 :=
  finishCode 121 0x1f06f1d085082e41f7d15ff18743de2f55a0e456169a66298dc21860d366cd5747da4c4fdea139abe8fb4a1aa0f7395feb57382cd5b2e3c70530698362e3ce636ad93ad21ad5f3f5bc8dc0036690ac051de7ef5149835503b16aef63a0f21196ad9784fdee599ea2b539ab6b579ac24eb6aac60d6ad987e671e4203c28b20bfc622c2393d66d70a3a84da768ff275acf647fb48d1ab460c9827cb30893fca3a1df721f42759cc65a6947581f3025ac2d57398ad364f5a3a4fbe943398bc87224fc9d6d5b0f7971e6a68d6d69ad35960aa3d398c4eb5a6ad0f224fdd8851a818887a6398ad345feb4d962262f275a3b63039cc4a120e92c5c51d28583cd60b34b53ee3073ffad349d6411792146701e64eb88222ff208cc3d6adac763039cc4a120e9275c1e9208be9023790407bd5c1809b83f7398ac1e50daccd6773d9d83ab2d7e140f132cdeec43380b10e276b38ae3603f783bcb01596932ce62a499c86b073fbb4069fa0f2601578a0645eaa22bc6471ad45ab65d7899670d9ab6e82d030169ac23b692b02d4029e759da8ecde673149f9bce398ad05f38daeb49398a4fd3ff1bcc95eb49398ad0be24fcdc1808fdc3af1fddab67ad8bc6d3f5a6938d48630181aee8303c1af0c05ab7205db05719c6f0e6320dc7eeb41cc649f98be36b97cce62731927f035d9c5507ee98182c9a31c154927059a470798d361cf732a924ff3289dab660d (by decide +kernel)

private theorem part457 : Excludes 0x40000000040000000000000000000000000 0xbd88da90a08000000048000000008000000 :=
  splitAt 1 128 0xbd88da90a08000000048000000008000000 part459 part458 (by decide +kernel)

private theorem part455 : Excludes 0x40000000040000000000000000000000000 0xbd885a90a08000000048000000008000000 :=
  splitAt 1 123 0xbd885a90a08000000048000000008000000 part457 part456 (by decide +kernel)

private theorem part453 : Excludes 0x40000000040000000000000000000000000 0xbd085a90a08000000048000000008000000 :=
  splitAt 1 131 0xbd085a90a08000000048000000008000000 part455 part454 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part461 : Excludes 0x40800000002000000000000000000000000 0xbd196ad0850400100008120400000001000 :=
  finishCode 71 0x811b06518c398bc1043e85278a1293f83d23e91f4c0e33e0938569a0d94f127e4f5969a71793f27334029aa51d2b4d83d23e97e2086a1e03f4cd5b49f83943d2ac13d6390a4fcc3293f89d6fa0fa4e4a9f592564cb95e693f071cdc3c00db8a4e9f592566190d4c4d7495a5049eb0a388b23c0b1f760a12b4d9ab6809402ac94e1f06993f2807523a35669aa014baa4f55a1b478100b3da55f20db28aa78619969ab0f834a0e593b2f69372942cc03356ca4ef69781ab71ccca1671781cb142dd06a095b238cbaa0d507087a41b30385bc5910c3a1ed32824dd28195a5ad3d1c387cd591e3a05ce1f031d204d10326e998b670f69acf7125cb03e41bac8c18e70f1eacf69063a4fe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part463 : Excludes 0x40100000002000000000000000000000000 0xbf8b5e90a50400004040120080000001000 :=
  finishCode 83 0x821b46a1e47105f2de4084f79ab65150f7bd8611615c8f9731b56d042b4d06fa506271a826314b56e2939405c45903a320fd23282128498ad60418cd3d2939874c530224fe3879cc60ff357d48ef69400ad354670754a4ed0390c63784ff293a0467b487bd6632d35ed2731303c73169e947dec387a4fe7b487bc7de93f83df1454e6302370e41405b06815c0e8804e308b9253e22df1eaa4fce62fc23fd6972d353eab4f49fad2e6ad93467b58094692c5b4f8b4bd27eb4d398b8907b86b2b1f1ea9875504f8a301ad04ecf69599ad44007354d1c6e674fabda5c8339145123d57b4b916600e62d5b969e70f16f8fbe5f0c2261f928ed5b927ef23181ef6c120353cd497b48f143aa93f5707df1cc50432d343aabe280b612ed1c4979f1e523a465ed65a187dee5f6adac6e6ad9add48aa0b69cabc55e30fbd48eb1b9ed21a94f8b60b4d523cd5b4009cc4977360ae2cf6408a0fc7de731068c1d5523cb09 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part465 : Excludes 0x40008000002000000000000000000000000 0xbddc5a95a50440000810120004000001000 :=
  finishCode 93 0xfa428ec3c8e20c45d06a06027318e020d5502044f6c9412769cc523341c623dbdad1da5e3380a8102328be1cc527f13b5ec716a4fd29ed379bdc649ba01528271a4fe1eaa0666aca4fe5939c057c6adc9f159d9cc5ed293f2769866495ba03f98a4e731183af84b99882a3128f981cc526e59612e4529393b6398940604721b4631f0740a16527583cf693e8a84d00a93f6aba5041aaa1395f2e5b6af8f55d87418806aa9076250495b34f5426b3b177c6ad48e92b6231c1ed6667f7402acec9dad3d89da6c1f0a02015abf13b5676a3b57cca1369eacecbc72d4528e4ed732c0c739893b6356c0d52768bbca2a819927e4ed28593b6177a4fdc8681f0523ca1d1fc87a4bc7355d2321cd5f01ab178c9c69419abe0d549fcec350ca03545fe5e19abe8fb3988f567b8c08ca3407315f07f2c3798b2e63927e6d7256a607a34d6725bdad1da6b7402c8ed614a0166adb4ccfee47d895a3f9404b57e620a3b526e3f957124b358d02e7f9398b4093787f27d1942a6b7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part468 : Excludes 0x40210000002000000000000000000000000 0xbd9cfeb58d4600010460120108000001000 :=
  finishCode 27 0xde368e82f80d7260c4cb1fb8c06631a41fb938e3808f56599ad0ac35165a6a4dc7aa9e12c6839b514e0341cdab6d5f902ed5b49bb40e8073641c930528e809180ab070f87aa9374a3a0e67b8932c7ee70f260cac0c05a7f248c9c65e34a3ac6e5a4bda527ed43 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part470 : Excludes 0x40010001002000000000000000000000000 0xbdbceb9ca50704068442120208400801000 :=
  finishCode 37 0x1f4851c46203deca3002f57b5cb4d506a86d60f27cd3e71805676e5f4048c0543720e5492b2d1fbb18e42f8b335a493b63998fdd40731c80960cc1dcc325c796a69f158ac70183d9f94b8e7ad9ab6f67268ad35b472120650e66721177cc2b7b8c4ed5a1cd4f0efa494e664ed177c4ed59dc94741c8fdded24ed7220862fcd574a3ad34e4272f6712872f8fdd8631b5d6823c57b5cc317b7a015c9ef69969a4d1306cb4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part471 : Excludes 0x40010000002000000000000000000000000 0xbdbcea95850600000440120008000001000 :=
  finishCode 151 0x328ae388731851e00f7bb0ce035ce81fb9f5e588bda5603073374ad5c9969e3db65a6b57dedb359e0e66c97b4ad5e7b4b57c7aa93f670e67356ded23f74f8cd5b49f971e58bbda527e3f774167724fc5de0d7732cb070ef8fdd8c4817c7b4a4fd5e3393ce4a3f7588c7b34f8ac3d692be2cce3998fdde016fcb3b6af971d6a68db8e1eb33392cfa428de348e2286e2658bd4e021ef630fc0e2cf673999c0566693f671c9f39aded63c5399986566704133e39992ee268ac5e3809c9569a93f86026e91ea87bdd049fa8061809bce276b50c43a0da0736392835d5ff310d27e1cd4c07aac024d5cbf077d6821df91daa139682b5791da1df06ba4fd677077c1aeb4d7820806b87366ada4fce4ad5f399b4093f735c7d940cb93e7358d65ab64af91de93f4929ccd20510fc67127eb6428fa3789a0fdc9972cec3deb497b49c3cc333a0be0c05a873da630ed597b69ccd6772be6727865d24a6e51fbc9ff9256c195a8bda47ef0a2d25ed2b3b94924af876304218d5b38981c67b4ad1c326c579ed23013f4c485032b56cd9af53372bda608741605f168f13b4fd2725399ab03b18c32713691c92f4f88c04fd2a4f9ab6721180940c0180b41fa5ed3276547ac219abaf695a03dee4f924a9d9527b93e492b50c7ef1ba53fea0116fcb470f79fe640487bdb47d1ed312bd24a80506b87bc1af0fdcff31c3e14711d8180b68be07bd00b1bcdab2f6d8b2ab11379c1de8c18fdd5f26f35a8a01524b0fdd7c721b44a0c6e5097a09e0eed5b527ad44e4a7337807ef2cec9da3d5a0eed59725c5a583db56cb8e7e524c8fddc83b0c33160438ab3b5a8a41e3f287151c741ec3720434ecb98d20eae2f8b5194268073998fdd6a72d453fe0d72578b7da859dc9373978f55cbe0d7949ea13 (by decide +kernel)

private theorem part469 : Excludes 0x40010000002000000000000000000000000 0xbdbcea94850600000440120008000001000 :=
  splitAt 1 108 0xbdbcea94850600000440120008000001000 part471 part470 (by decide +kernel)

private theorem part467 : Excludes 0x40010000002000000000000000000000000 0xbd9cea94850600000440120008000001000 :=
  splitAt 1 129 0xbd9cea94850600000440120008000001000 part469 part468 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part473 : Excludes 0x40001000002000000000000000000000000 0xbfb9ca90858400204000520000800001000 :=
  finishCode 77 0x821f4761c4188ba0b20c1d20f181c9ea8f98c3b0715f148f2d5cc5262b1ff9f893f8e1e1a991d2d231ea9cc5abe4f56c170408c83136fcf67969ab575188ffd46673383de3ff079af8f20ffd3c74160726cd3d26893ace2e733541043460565a7212759cc6390801cf9eb4f57b9835945010c5a69cc4fc5a7929e36bb5368c0b57d5ef178565b30458b26e95a69f8b439cc6f7172c8f54b8e93f5a5cd5d72c8f548f7304527ed2938b9785306c165a5e10ded07347da0c561b30a4bd28fb595b165abf2cb49d6f2350e80bfd3c500e26d358e62af72f0cd5f41fb48cbc3348e3749cc47aa98340a023fdc8f1605696619240c8c32c09b5ded32d34fbe72341fac3669eba0d3d9062d5f9ed24eb398b38e20ffd5f32d2c3de2f55411047dcf6b38796c49c2601410bda60d69cc4e1ea0305e592b98d666f69398a476592accd3e28fb7111f723e548e2f50f79cc6353a915cd6821 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part474 : Excludes 0x40000000002000000000000000000000000 0xbd99da90850400000000120000000001000 :=
  finishCode 105 0xde3a10a105c83efa2c26314ac545ea1ef4317c584bc84d1a302b4d6ad9834e427333316572d5cbd30f56389bb0b41f83d536bcf636af93ad6aed5f89d6b2b306c7f97b4b56d3db1cccc3b2d34a2ace3190a101df86d1e45905fe3116c140404c731275c8ed26593ae584a3fe5a9bda540265cb4d57d949ca12731607c93f6af949c9d631186232d0d03685138a4e93f98868ff61086f5a857ccb4d1ea98743bf149e7b4bb0f23402ff188a80b3d91da937398a0dc997209c9971cc5f459102f147d696607315a30b4d9abe51f387ac051f4f8c62959ecb4d4659655ab6a01cc657ba0e56af209d69b2c8d06eb3539883cdf8791940f7b60c61cc47ab356d69a2df49fa78d22d347ab357d6af3da432e3d536bcf535abbda47aab2370b091d6cd5b2588f55a6b357d69adc2803d5735d18136bad35ede4b1500b56e8c0b4ccdaf2d356416f9fe62e3bd8d612b059636d5b7b7b90b22d5e045a7c5abe62b5a693adb05a6ab8351870ee47730b56cd2ad5f39898a669eca016afa8f65a687be760822be144c6227e98c0e93749fc731308942e2e0a4fca4e0f3 (by decide +kernel)

private theorem part472 : Excludes 0x40000000002000000000000000000000000 0xbd99ca90850400000000120000000001000 :=
  splitAt 1 120 0xbd99ca90850400000000120000000001000 part474 part473 (by decide +kernel)

private theorem part466 : Excludes 0x40000000002000000000000000000000000 0xbd98ca90850400000000120000000001000 :=
  splitAt 1 124 0xbd98ca90850400000000120000000001000 part472 part467 (by decide +kernel)

private theorem part464 : Excludes 0x40000000002000000000000000000000000 0xbd984a90850400000000120000000001000 :=
  splitAt 1 123 0xbd984a90850400000000120000000001000 part466 part465 (by decide +kernel)

private theorem part462 : Excludes 0x40000000002000000000000000000000000 0xbd884a90850400000000120000000001000 :=
  splitAt 1 128 0xbd884a90850400000000120000000001000 part464 part463 (by decide +kernel)

private theorem part460 : Excludes 0x40000000000000000000000000000000000 0xbd084a90840000000000000000000000000 :=
  splitAt 4753 131 0xbd084a90850400000000120000000001000 part462 part461 (by decide +kernel)

private theorem part452 : Excludes 0x40000000000000000000000000000000000 0xbd084a90800000000000000000000000000 :=
  splitAt 1 102 0xbd084a90800000000000000000000000000 part460 part453 (by decide +kernel)

private theorem part442 : Excludes 0x40000000000000000000000000000000000 0xbd084890800000000000000000000000000 :=
  splitAt 1 117 0xbd084890800000000000000000000000000 part452 part443 (by decide +kernel)

private theorem part422 : Excludes 0x40000000000000000000000000000000000 0xbd004890800000000000000000000000000 :=
  splitAt 1 127 0xbd004890800000000000000000000000000 part442 part423 (by decide +kernel)

private theorem part404 : Excludes 0x40000000000000000000000000000000000 0xbc004890800000000000000000000000000 :=
  splitAt 1 132 0xbc004890800000000000000000000000000 part422 part405 (by decide +kernel)

private theorem part362 : Excludes 0x40000000000000000000000000000000000 0x9c004890800000000000000000000000000 :=
  splitAt 1 137 0x9c004890800000000000000000000000000 part404 part363 (by decide +kernel)

private theorem part336 : Excludes 0x40000000000000000000000000000000000 0x9c004890000000000000000000000000000 :=
  splitAt 1 107 0x9c004890000000000000000000000000000 part362 part337 (by decide +kernel)

private theorem part310 : Excludes 0x40000000000000000000000000000000000 0x8c004890000000000000000000000000000 :=
  splitAt 1 136 0x8c004890000000000000000000000000000 part336 part311 (by decide +kernel)

private theorem part256 : Excludes 0x40000000000000000000000000000000000 0x8c000890000000000000000000000000000 :=
  splitAt 1 122 0x8c000890000000000000000000000000000 part310 part257 (by decide +kernel)

private theorem part176 : Excludes 0x40000000000000000000000000000000000 0x8c000880000000000000000000000000000 :=
  splitAt 1 112 0x8c000880000000000000000000000000000 part256 part177 (by decide +kernel)

private theorem part80 : Excludes 0x40000000000000000000000000000000000 0x8c000800000000000000000000000000000 :=
  splitAt 1 115 0x8c000800000000000000000000000000000 part176 part81 (by decide +kernel)

private theorem part0 : Excludes 0x40000000000000000000000000000000000 0x8c000000000000000000000000000000000 :=
  splitAt 1 119 0x8c000000000000000000000000000000000 part80 part1 (by decide +kernel)


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem caseBBBR (c : Nat → Bool) (hp : Pal 280 c) (ha : Avoid 280 17 c)
    (v0 : c 139 = false) (v1 : c 134 = false) (v2 : c 135 = false) (v3 : c 138 = true) : False :=
  part0 c hp ha (insertRed (by simp [Red] : Red c 0) v3) (by
      have mask : addedBlue 280 moves.unary 0 0x8c000000000000000000000000000000000 138 = 0x8c000000000000000000000000000000000 := by decide +kernel
      rw [← mask]
      exact added_sound moves hp ha (by simp [Red] : Red c 0) (insertBlue (insertBlue (insertBlue (blue_zero c) v0) v1) v2) v3)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part478 : Excludes 0x10041000800000000000000000000000000 0xcffa896211a618340902080040000000000 :=
  finishCode 137 0x3c9123a8e62c81f37c1c7b2d54c5ef691f993d43633d958be6fb30b8fcde85c124312ad367b4b9ac0aa4d5837c91394124d57b4b12616d979da4651d85b1141f9a934b3b2ce5c8a2bb7b4a335487b4c4f560eb135c8b27bded2b22d363f093d47e69016765a68d35ed281d15d9f8626aad3503a5df969ab55701585516849b863637db15470b1878fc2e6d1b4ad551dec0d37db9164898e1519a5f57c15026acf693fe93d4ffb1bec57734a4bbe9113fe9ff662aa51e27a9ff5e867154760c469e99222937526ab0c5596aa1818562d63736ad3569b17d549a62f2faca4d5a2a78a3f949ab4d526c2db5c0c4b18bd26f2d55ed26237c13c5a09ea5c380ac2d357066013ab1f9892b4f254cc4962dcb192cfc8f3494c1c543f20cd5e6f695a7c09d5b12c67114837cb19370974d69e061a0e2b1915592a6233ac7d68a299838ce6b8c3bda569ec1d89aad82e0c43707c2d05e9661653120cdaaf690daaa8c2b8daa5df5a2a87cdab2ca586a7e1968a4d55a1653247d86a0ab0daa04e7b4977e30e7406c65a5c1c49aab4328833a0e2a1f41e865614ab58ded341c49067f12bebdb4fc5a2aa8f692efb136254a8cd89b461e36a9b7c04ab29401828ded2f698506f6d621ad1554621ca302ad066a1f9ed20a32efcf695c1585b0bd31b5413e0a34a20fb17a4b4b2d34e45b169a921ff61528af51483ec6932349b560fb3064dbf355e0d24af5b0b4b41bc7622bd26acd2383e8ec5206218de63dbb915eda299723860431a4d59cc27b7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part481 : Excludes 0x10050004800000000000000000000000000 0xeef2df7239be519f08a2809240000000000 :=
  finishCode 31 0xf22a8ca302611ba8ae0fa1f3488a08d26a3f3560363348cbfe1f349aa51d267397d2221f36f2100f9a28c5126ac39783ea51436324cc9aa39783eb136163a0752844108489c1f66919ff5c9f06860de6fb589c1f67b4bdbda6e6fb7b7c5836b2a44d6c551480d5cd45401a4cc54a2bd651700d5b4ae5a69b6630f41f569af67723c9330cfc61e6b2c1f4772e457b4b985843303d69b07d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part483 : Excludes 0x10050000800000000400000000000000000 0xcef27b562bea5017080a8000c8200014030 :=
  finishCode 33 0xaa389123403f3561a8237cf69311989506693541ebf8f63969a623312974e83bc1f35a6a0cd07a5df987b1833f9a0f4c4724dd07a823526c60b419a0f5a85210845103aae330de3da544f249dcb3077526a515cb341dd1bed252efc8ef72ca37e30f3574c5ec09a0d21f372cad35fc0f9c5e9317ad3649cc1f522a0b56620ef189439a0b55a6ca270f9c625 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part484 : Excludes 0x10050000800000000000000000000000000 0xcef25b5621aa50150c02800040000000000 :=
  finishCode 131 0x7312c4f09dab2228d028ed49ea2b949a1f305698bd28b07cca03c1ec514a40b4d163cf69499c2c705a8b067b4b57da067016b30c4c5e1f38953309c6ce38f40ea50cc2075585e1a633da435a60d9cbf3da60fb2d35785a6ab107596321f38696c5b2c1800e30e2c79a07f19c0f9c625317ab02c79c7a2c783e6915839af69969a81d4a188420bbf1f7438260d40ebc8915816a60d0d0c1ad840c81e03e7352d1e2a154420ef461d21ee65465ad5683eb90ded28a1f08f12d1cf69731968e62dad14b06c1d83e6e3d8c3920ded2c1d9a6ee4f5a2ab908091e8c38144b4ae650f9a804bbe1f39ab3461da96a2b4ed92cd3c591144d1476a4f6aecc5b1aaad360fa8330e6cca2e0f2310d828fe526aa8a2987e683d0f9cc1d40ead36245149f2e7b4982dabe6fb7b4cc2f514c24d7b4a0b415e82d9452b4d621ed31ff439a6179c8ea29681fc311c62f256c5dd83ba84503aa4d406cb4d41eb28aa22907188f6d4b1e9a3bd42a3f3401a0cdc441ec1f61c8b4c528e9db1f9847683ba775ed29ef50ab1094398683e86b503af21e0a4d493cd65500bda672c98bd3ba0ada245e0c862da8566b2b986259c1f60e26fb7b4b98683eb93c966a15803707d7b5b4c5e47b4c60d49b96a43e6b839ae7b4c1bd24e5e97b4cc03301cd928a7fd163a78ac28a5476d3d96067fd465a446722a935a7aa4d92268cb50aa3f6581a855652a3b (by decide +kernel)

private theorem part482 : Excludes 0x10050000800000000000000000000000000 0xcef25b5621aa50150802800040000000000 :=
  splitAt 1 70 0xcef25b5621aa50150802800040000000000 part484 part483 (by decide +kernel)

private theorem part480 : Excludes 0x10050000800000000000000000000000000 0xcef25b5221aa50150802800040000000000 :=
  splitAt 1 110 0xcef25b5221aa50150802800040000000000 part482 part481 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part486 : Excludes 0x10040004800000000000000000000000000 0xeee39f62198411960882009240000000000 :=
  finishCode 41 0xb23304ff284a283f3858f07d59fad2d68621267399458e7fd465cb2958fbda65aabd9d545aabc8d29928e3d19006c519cc6f1440f9a0f66a4b0860e22c751fbd02bd928f071409935507aa478996c51651e86a1745a1026942d360e31354b7b07d4eec4b783896f51be8df8d664d5836c947489c04d1e0cd2501393545b6b4d4a3d06f3f8c20ba228af7896e9274a29ff6526a4cc9aaa11928e7e1481a51e6afa7a56264d5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part488 : Excludes 0x10040080800000000000000000000000000 0xeee3d94f118418160842404040000000000 :=
  finishCode 117 0x1644f16827fa30783516515a934df61d1514a8f5146519844167307da3070775aaa44d47ee4f5a6a8ee5a5bda41663f3040ce4f5a6a8ee3eecd5f09197d549a1d1651a8521d8406bda650bb90d49ad2f944ee435a7a40f6b9c8ef6957eb08d6aaf7786961d1396b91d54513ad3e839a4d5ed63f32efcb23489a3765949ff5c8ea2755114511946207e6c539646f69515a9346f73da56327353e5a44659c863c2ef0fcd646b1f9ed2d5f396988c43ddd1df461c3a27cb9d8441227304daae1d12faa9356ab2c7c3a2b55968621d44a1703feb88f21c0c3a33da5046c55722c72d41197a683ea8558aaf6996072934952e6b0e0a08d28791d82fab03659ca93528f2855672b4f8fba5e91a9cc5b50aad3d49ae599cc2d5d589aca522aa15690d44512c609c4d52f4ac8d0265df5aa8fce621ac8d22ab559196927986ab231f9b09e40997a5a85a1d45c0ffae028067b4a5156aa9030e8ad8833381ca03730a4ce500cf69481a0cd705603a2b4d9402b5561ccaf7500ad34f532d355ee901727a93528eaa2b0942e0c53836c4b357b8744beac3d38fa207a99ca2a4d2deca2b57ba40ce3da5cd71ea5aba71f5aaca4d9816299736c3637b4a04ce3ea82bdc3a2d5d92263b94a2a44e7b4c20ba25866251581b177d26ab5548abda63f9b0356aa9159226913965290357bcb130d4b14d6aa5f5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part489 : Excludes 0x10040000800000000000000000000000000 0xcee319c6018010140802000040000000000 :=
  finishCode 113 0xd22d0527750a2afe258c0338d41bf569b41bdede1a55a287cce3e1a583e6d8036e0f9ad143e700ec07ed2f96460db6a170626c0db3819c4514118a0f662da855672a4d87e707cd643c1147b7c90551ea93e2406dcd65514bda520a83d901aaf36afbda4b0a3f39ed3187419a0f60df16a58760db51faa8bc3c8b1359fa93616dad3e51fca4d6299f765a6c1f549ab13791e83f9c2770afa4c5ed21f306da4c67b487cd704f1cd7277569ef6962da50e0df2c4d856c273f8ad567b4b16da059170289bd0c23f81f393fe93b31298bcc806da2080d36ad06f62a977549ae499ed307d37da07683e9becfe283d06dcf695a698660de9e23ee69fa8ed452a2b49da8ae51fba90718c4681383ea0f4c4741f5e87f1700f9c71f31298bd1ff20f4c46b828ae40ec1c58420db0e8b03e482c1c41b6f695311049d9f4e0e4bda4fe291f6a1c60cb4307136acc278c1b5743e6c5169f87261e8ad09e448b8298aa24c528707d85b6d2f38f982dd462bc03b838ad35ed281d513c3975a6bc8aa34be16db9665a687cd22f2d357479107ac0d84968ed59ca31cc16a2b526a8a65a69f7501b2a8b4d406c5db41ea03640eba8aa460e37a87cce3e83d0f9c81d790e05159f7613c92cd23ed63a0eec57500c1a179128707cc1b64d5a0de719 (by decide +kernel)

private theorem part487 : Excludes 0x10040000800000000000000000000000000 0xcee31946018010140802000040000000000 :=
  splitAt 1 115 0xcee31946018010140802000040000000000 part489 part488 (by decide +kernel)

private theorem part485 : Excludes 0x10040000800000000000000000000000000 0xcee31942018010140802000040000000000 :=
  splitAt 1 110 0xcee31942018010140802000040000000000 part487 part486 (by decide +kernel)

private theorem part479 : Excludes 0x10040000800000000000000000000000000 0xcee21942018010140802000040000000000 :=
  splitAt 1 124 0xcee21942018010140802000040000000000 part485 part480 (by decide +kernel)

private theorem part477 : Excludes 0x10040000800000000000000000000000000 0xcee20942018010140802000040000000000 :=
  splitAt 1 120 0xcee20942018010140802000040000000000 part479 part478 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part493 : Excludes 0x10041280000000000000000000000000000 0xeffbc96790e6d8279d40000000000000000 :=
  finishCode 37 0x2e0be2802e9540bd2d538e4a4f5392cd533f0c7cb83e9355876c5527a9c9558530f415ac4f50ceac4cbd2b554a140597c0c52f4acbe59cc4c17b3b07565e9e2d360e29c4d943a147ec1d9ed65f584720c5612cb092fab28742d3630b1f8549a4d5584c2ab6a9b92dac739b5644a1507909ea3bd9c8aa39597cd2f9cae3771d3ad35aa6b03382ca39621ad56736a934e12947 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part494 : Excludes 0x10040280000000000000000000000000000 0xefe1592790c4d8221540000000000000000 :=
  finishCode 123 0xdc2a2006adae0be328a25a30aa155a69f2c7a22c52fa8ba540790bd2c824dce6723bd477075922a8ef6ab8f462758a1661c9c2526ea41775fc3ee9b9e8c2b0f565ec259ac64d59cc7075791985f1ec4f4cb2f477c61544a70938b8ef627fa51d841de81168c3ac0d1fec5583ab91e27fb8f6382b08d8a64d5492a51d8b72d14fbab4f27fac8a01d02c5275cb4d51d8e9569b392d452d63612acfd69b461418a4ff5f077b249433b348c74a9e390d5d9c8e0bf51e87454764eb27fb0029d855eca2f81979eeeb4d0dd8ba4e4725c3ab5a6830e69cd185725965d4769eb5f1947d1c017483160dda51c3773984e1318792429472fab58c56a0bf373c70949ba70c02d3e61fb9860ea1d150abdbd8722af4a0e8612cd631d29776629ad3e584830d8173525644f1507212827f86d62fa93ad7c0ddc9470dac7134e140061c2e95a6a8ec36aca31366a98abd4262ab0618e9662ab09e174b28be4000bf8b96b2f7359c145d2c20b2c3772c4d83b46160fa7dd736ca295a6a28d39928ea1351da51e69cb91d945f1f46605d2c358e660c562dc46f581a51c17f30e6736a854186b83805e91cecb0962aa51d8ab398dcc323fd706a1c0540d3f2d143721c1650187074569a1d19a72ca270a3f949a0bf9cd64b3731a85dcc71f4662b8ba4e2e937384c733 (by decide +kernel)

private theorem part492 : Excludes 0x10040280000000000000000000000000000 0xefe1492790c4d8221540000000000000000 :=
  splitAt 1 120 0xefe1492790c4d8221540000000000000000 part494 part493 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part496 : Excludes 0x11040080000000000000000000000000000 0xeef27b0bb1c418820040000000000000000 :=
  finishCode 115 0x3909e3e0b22f84ff651587119c174c60e62da93d8a6b23397a4de0da935606c9ff629ac651dea4f1f9ac05987b1843979c5e732830569ab1912dca3d6a2cb452faa93cdb7293d44ad5b5a2972e1f98ba5ec5d0e8397a8ee382b08e61dad15603293e30e1d14ff9c5dcbb1c654769c230b23733d1833feac64beaa4f2facb036adacbd47b39760fac23409b50dc2e0be0745ec3fec71f580b57d81a7173929c7e6af97d5ab707f8ba6d2b69ea0f5ab65f57b19c3fe9cbd5ef2c653d318338bac0581a0c5580cb179ab63bd41e9ff4e672935ab6d235abb70713260e2f303584a882c662f4b9b569aa2b98a6b554a3c38f5899c5d986713ff1ccc176c2b907a2e9397b57e2e5ad34e0a2e91f9b28b22a8dc0fcdfc6716ab0314e22b80f26381a03650aacbc18b461e839bd9cdeab3f5f110174c1de60ead3c792a25597cc5b5aaa0366268315b870165f0314beb0ba417716f56aecc370be288c0d942a709399ae0d6395eeb231e4acfce4e1d18c3cb455aaa4dd8052169f0b1dab6b453fe9c657059cc3c96ad97d59c8c3cb396b1acbe586cf6f2d4cd638c28f24e2e5bda306d535a2ad55946117c59fc0bb174ac8b238792a4d1f9b9b62fa8f26174b56d69a88338be3509376adc71f054cd5b2e9d07f396b56cbeab2f96468dd606ad55ab6f599602b55 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part498 : Excludes 0x100c0080000000000000000000000000000 0xefb27f0b9f8458060040000000000000000 :=
  finishCode 83 0x821886e1c45f174174b509479ed2a11411a0ccfe73d9ce4293551cc9256a1c01e8cd530618315746adce61411bda507a3f360ecc35697b58d641edca4f6a9cc0380ba073504727f507a9fd901af69877a0bf7b4cb4d389a84d44e4ff721a85f10469fd94220bb163c83d499b56e51fa49daa70fcd647217c4a142b244ce2e7256abcf6971ea44d24a7334f09ff2d3574541ed723f630a3f34a2a00e1f9bda5c46adcc4d481a8560ea5bd9206f6f7b4a85584731c3b950aa93e0eac4d49b8fcd8b7240e48ab90ba2a0c40b1da85c0176a2583a2b4d9ed2d5b9ed2a3f51cad35a4706dd24ed4380c22a891506086de6a28fadaaf24562d8b985aa6f696b1ca396ad82fc7d72455a8610a8060a009036add1857b4ad349c2d5ba30ab4d2c7d1855a693843a3240d705a6b98e1e88ba5ab72bdd69ef6b51fc2e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part501 : Excludes 0x10041090000000000000000000000000000 0xefbbcf67b0e61a232869200000000000000 :=
  finishCode 19 0x3288a3c8be0fae08174a00e839bda50660bd8bbf4614beae513f9acbc9aa4f58bbe833728c3eb174b30be3c87cb96aee633849c958027aac5e7288a75ed2b5726acb457b4b54c9ab358dca2b4598764f5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part502 : Excludes 0x10040090000000000000000000000000000 0xefa95f03b0c41a220849200000000000000 :=
  finishCode 153 0x110370a8661ab68a2d0c0390f62e9000aa49ff16a524e733053c4ff4f1b8275ad563febda4e2ec0d481c1359ed2f6761eacb4b528df05dc7cd526a0f49d6f691549f867b496b567e703154b909613fcfc32ca4bbeb237b79d0b139ed2e47591c61e3f09cccbeb3da4da313ad68ac3f51fbda574722b985ed21b18582c399a72c0370e231565268ecc9aab551749cb56ab029da7a3a737793fe69eb09d68ac51594ce653f0977c9fee44109e41d64a286cc9d64ff5d12c591c8fd4a2977dac73dacf96c093849ccd7c660beb2c5ce2ec5791bac0d50ab08dac6a3f8c3d07537aa5162ef977e1f59c4600711704e1a8600e06941c7c5d32d05cae7252faa8fe51c97d65138ba5947d1741748f6e2efb03627f89fe2fa977d3faa3971dc8f1736b094bbe5f54a05d2d459c8a5f550bce456959f85944e1ed30fac5829fd51cae8f63e85df736c3f34199cce7b4c3eb270b9b6406bda4e2ee518e124d54f4c10b22789413fd40275bda67b5a8a5c8b3da5cc728e4556d39604a58cc30e565f28e5ac692151ccb2f399cb57604a0f5a5ec5198129219cc334adabe6fd52793fce6ade228663905df801e4650e2e9ef817ec55500a8ad64596cc5550a93adeef358e0fee637b7cb2948193ac17f357d47a4eb531ac72d55ed741ac5d2d636019c72017ea8004638fad0c9d62c158b9f071738fce638c3cb016119cd4e3f2e8e4208e5809ccd28a7039c8b2d3d6aaa3d500a78b298e66a2765165283d9cd6c5b7b5894647ead14e66902a0f694e1872c3d92666f55a186c4f9b248581b02b417ee635d194671267285e0fab4105db91e7318054e068d9720d07d835c7cd581b035c80c3cf691749c249feca41ae6a2a93c7e62e97bbcc55 (by decide +kernel)

private theorem part500 : Excludes 0x10040090000000000000000000000000000 0xefa94f03b0c41a220849200000000000000 :=
  splitAt 1 120 0xefa94f03b0c41a220849200000000000000 part502 part501 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part504 : Excludes 0x10040080002000000000000000000000000 0xefab5b13d084580a0540409020040001000 :=
  finishCode 107 0x104390b23d84ff651c45a6ae0c4208e0628ba59c55122b1c1630ad5b39a9c16514c615ab67277b49c164a3ca3d397a8e636db9ae30ad5b641146afd185584a84d1fee6151db30d5f8e6ae470e89c0e6abb56e381b88e419886f6938cb10d5b730cf6951e92646d2a39723ce610439b6d887b19456103a35587a21c15a69ccd69b348c3a28336adb91e5ab9c94ffaf69926ed5b3fea075205c1c8f398dab69f17b1cc73da4e668039c82e617b48635ab6d5b8e47b1b85a6b20b22a0a3b723cd5708e9cd5a8ab17733a3647a2e479ed2e61723cf69722a3fd4025d39aa65f549bc1f6733bda5ccad5b38fcf6939ab0098240a4251c7823d12decd6362db58e6e14862dce416ad86e53d32c5d476a3d6adc1f6477b56ce3f06e4e5a925165c9115a7a8f524a72328ba2d352c66144b3da5266ec348e512b15e30ad5b2efb55dcd70f44d9a5df2a144b356ded2b09969692754147318598aef69270b55e8c2b9adc85411469ccc096ad9385c931c9d266e611e8aa8e234e51e33944e32e3b38fb8f6240d1853d4b56ded25b18e323857b4b56cbbe902e0cc0f457462058ee6b965ad390e8b986270cd5b604a7a6628b925ab64e15d16832bcc9aad5d493a5149c339166919385ab6a25 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part505 : Excludes 0x10040080000000000000000000000000000 0xefa84b1390a418020040000000000000000 :=
  finishCode 135 0x820a46fa3e0a8278aa13d49feb5585d27f31f9c1fe174b88ca370c42936581c1cd652719609a04c5d2f22a8c3f942a9474928fcde0601ab71c9e30b307652168af0300d5b8e321bb942ac4d2e5b13662d86edea3461cb9672d6ada00d29928eb455aaaa8ba200e7afa79c3763f3628c9e71e8aca528e7e3dce628c61660ebc87824dde03f0a3c6393a44e6949f2e71eb9ada52e3d9ac6b45691705a2ad555ff16f4bbe3d18c1c80372cc0a97329f853ce5f57115451dc7114f39c6528e3f3481945a2a90d5b174b50e8c2bdad83ab29393ad366abce4f393b56d3cf18393ce2e96ad97d68c1b56d68ab03651546207e6b55969a2e94118a5e5a2972d62ed2362d86ed4c561206e0c8174b8f64f3a8556aac0355e6ad92a53cf316cb96b55969a705489cd5b174c9e7626b55c70312a5c7ab4d50a8ba5e45518049ba4836393d2911596a8ed656f031463dbac5d4529e76adb9166afc1f562e5df2efc9ff4f1b8481476d5793fe705489cd5746fc7cb88f63818c1a855a86ac177e044ad156aa8a02266ad977daaf356d9c711e43b1a472d55aae91349bb70d5b949ab293939cb544b355d6aa94769ecc2737eaca47a2b555aacb5789d6d5b780a8541ab6782d361e8c615842c516515471ecc275a686edabf177cbeae3d17482a638ca906c41de62a97d4dde6fd691c7275a6c614bbee63944a72d2efb707e388c27526cb4d2709cb4e32e49a306b157b397d49c2c5151fc0a98c19f84dde4e138c82265a6938584ea3f62169b177c9c2a3f5a6c4b33dbc1fc7d63a7 (by decide +kernel)

private theorem part503 : Excludes 0x10040080000000000000000000000000000 0xefa84b13908418020040000000000000000 :=
  splitAt 1 97 0xefa84b13908418020040000000000000000 part505 part504 (by decide +kernel)

private theorem part499 : Excludes 0x10040080000000000000000000000000000 0xefa84b03908418020040000000000000000 :=
  splitAt 1 112 0xefa84b03908418020040000000000000000 part503 part500 (by decide +kernel)

private theorem part497 : Excludes 0x10040080000000000000000000000000000 0xefa04b03908418020040000000000000000 :=
  splitAt 1 127 0xefa04b03908418020040000000000000000 part499 part498 (by decide +kernel)

private theorem part495 : Excludes 0x10040080000000000000000000000000000 0xeea04b03908418020040000000000000000 :=
  splitAt 1 132 0xeea04b03908418020040000000000000000 part497 part496 (by decide +kernel)

private theorem part491 : Excludes 0x10040080000000000000000000000000000 0xeea04903908418020040000000000000000 :=
  splitAt 1 117 0xeea04903908418020040000000000000000 part495 part492 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part508 : Excludes 0x10041200000000000000000000000000000 0xcff989e790e2c8249000000000000000000 :=
  finishCode 33 0xf23d0b8461e581a894e26b4f1749834c5ec8188d7c382b30e6b4fbcf6d71ec1d4e66f65901e9e9944abc348b4589d6a475aa925627aa89662ab08dbc4f0e431ffd6aa0971efb48ce3201bf71ec46f727ad5505e0c915ac7ff5aaa435605a2ca4d41fa8960eb1ffd6aa2db944aa2b3848a7641fa78be20fc9ea80f965eb4f50fad3e597c83f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part510 : Excludes 0x10060200000000000000000000000000000 0xcfe93dc780f0d0301000000000000000000 :=
  finishCode 95 0x1003d0ce3406238c5e9e3d8aa1cce6978b6dab63df305a20a39907eb4d6afc3df6adc94316d982dec431905d101e81f26ac73316dcc39697ad3d6aaaa1588eb89aa6e73ff9f09219a5ec556adc8fd8c3a485a5eb2f926691f640e67280523e83f16da2118792727cb6adacfe1decf5f83ab4bcdced6316dae0ac2a060d42107e9c2cbe499b09e8c3ad3542e90f62ad07548fa50d65f1ffd9040fcb4f51da93d948909d7250d3d713ad69ad5793d6cc2f819f984e9213769c5d386518a716f565f0753e5a855672a391dec2993e6ad3d42a9e93ffc463613c61542ee59949ab4d7b15866110399b8ee48fa8e549ab4d834c6e71efa8ad4c5a69c164179c161e896f66b1a85d4529055138f7d69ac80b6e6ada89547e0af550bcf247c37ea2b949a91f641c059fc83f40f87445b6ba2f8d2f837e0bd5c0253461d6130715a7a855a7a831373ace6499a8555fac55969e0bd50aa8f5bc4f17c4407be4eb858ab2f6adbdbe8c3a7ac9d67ff487b4f6275b56d2665db5a6938842cfc37f24cd21e29ba0ead5b162a3761dab56d2664eb8bb6b4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part512 : Excludes 0x10040240000000000000000000000000000 0xcfe3398f84c1ca209248000000000000000 :=
  finishCode 45 0x1ec6414c5418770b6ca0282f1efa0fcec50103e9e1405fc5a6b5965aaa93e1b4c6d56ada78d499cce0b35098f7d69a1bf9a92a0400501586cd6530cac8e6adad3567e62f969a0c36917c7a0a02fe3156096b02dab67ab835982cc5ea1385ba4b3969ad63061a80781b9e6b1ac34c5ea153a18630535caee4724bc61d61ac275a7a89e59a8abcdced63317a84e305c1d5acac0b14ecf434062f8c1ace44860b61cc2af6b1b09e1578abe597823e1ef8abe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part514 : Excludes 0x10040200200000000000000000000000000 0xcff319df80c2c1245081201001000000000 :=
  finishCode 89 0xb234088144d905c1ec174cb3951ca0bd062f4186651fc1bcc5ea3f949af628e58a7393ce42b4d311d06f384ca3f51cbd0c3998a2623174a8ae15f972ce12883d8a6278f22d351db20c4c167ff86f2c82c082f4188b6e51fa8e521b163da4aa0383896fe0eb1f75cda7095a6c8214014c331706a4b58d42b395c53ad5b48fc1f602e979d247f13c6a5c09b305978d65923e6e72e585668c18e25a5e1a786e2d2f49881a62d4ace4fa2d2f697c2db584b945ac6bc2b0a62c0d5ba306d31838972d86a2db054a489e34de305b14e72bb56e8c1c1c5ab7395d612e516adca299cda5e77b190384b8f6373ac2505e721697cc3d3ffa98922f05cb0d3b0f66098b6d6132d2e0fad4983ec3bd50196a5a4a3b72d4d183259b1545b6f43f89e38f64179f74e12b4d317982d10317b20983d7e697c60cb524b33e8a086242d4c82f697bd7cb5320bdab707d9ab6f6460e7b99c260d316a5a924a17b0fbb1f85ab65dd5a6c1c505ed4983a3185969a37951fb0858a2709 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part515 : Excludes 0x10040200000000000000000000000000000 0xcfe319c7a0c0c0201000000000000000000 :=
  finishCode 87 0x6417828a949ca8551ab6f2338fe1f2e58fb14c5b658da0ea2c9389b0f5ac62998b7aa176298ef561b461d01eb4f02cca39410928569a3bd3eea78a0289e305ac35476aa16ae155982d6ab31350427137b1305c184f302cb1b075584a0850629c2ce661aad3dacb35252c4318732d3d01e82f612c7cb61cc1d5eded2f85b6b359ac6b4f7b98ad5ec4f13d7289cd7f187418ad34e269c2588a2cd6417a514fbf302dacae3b41fac2561328fd472d659816f5f629a85e526b14d782a0a3a662d15ab67dd967e7ff61db145ac6f2278c559eef07d1ef982d5c3eea78e61dc1d526707598765a93eecb3f5519c5f12c30586fd243278d8ab41d414ee5772bc9e949c8a0cf96c55697b58ca4650b7f316d2c613c945736c02d6af9f2c4eed5f969b0759826b4d4a2b38aa3d07a182cc469e398aaf6ba0eac250df93568c2b945cda9e348f86fde883acd57317c6161be920cb969437a158320c1b16fd84ad4b62ab40e479cc660d4f1d07d969ab4d9cc65bf (by decide +kernel)

private theorem part513 : Excludes 0x10040200000000000000000000000000000 0xcfe319c780c0c0201000000000000000000 :=
  splitAt 1 105 0xcfe319c780c0c0201000000000000000000 part515 part514 (by decide +kernel)

private theorem part511 : Excludes 0x10040200000000000000000000000000000 0xcfe3198780c0c0201000000000000000000 :=
  splitAt 1 114 0xcfe3198780c0c0201000000000000000000 part513 part512 (by decide +kernel)

private theorem part509 : Excludes 0x10040200000000000000000000000000000 0xcfe1198780c0c0201000000000000000000 :=
  splitAt 1 125 0xcfe1198780c0c0201000000000000000000 part511 part510 (by decide +kernel)

private theorem part507 : Excludes 0x10040200000000000000000000000000000 0xcfe1098780c0c0201000000000000000000 :=
  splitAt 1 120 0xcfe1098780c0c0201000000000000000000 part509 part508 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part518 : Excludes 0x104c0000000000000000000000000000000 0xeeb3df8baf8000000000000000000000000 :=
  finishCode 57 0x701e4711b8581ab61d3174836cd6f3594592d5f903ef695a6a085a6ebe3101d3511a72b02d3626aa935063280dab706f8f86a1126aa87544727ce6b26bca09518ad36838a03c9aa8316818861101f243daa283105d83056c4b147320bd01eb4d9ed29fd51cb56e5c1504c106320fded7250daaeb4d7a891967b4a50d69a81f6afaa0960b2658bb966306a1d407bdbe0df2cb569af6784fae6b5a6a82d6c51ccd5b4818b2522b24c5ab6d0370c4034521f356c1821d17a8cb4d418ae0b2b905e8315f165728cd6ae927a0de4e1697cb4d6ad8b1dc450bcc0d2efb56c39e9211f5aa00bb858e0bb942ed5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part520 : Excludes 0x100d0000000000000000000000000000000 0xcef27f9aa7ba00000000000000000000000 :=
  finishCode 27 0x7119c06ac1cb0e9b906ab9a46aff4019c841aeb0187a63f3276bd8e4448d5d818272f399af0c4340c55942a81d596a0f439a81d907aa03496596a8edabb1879ed2f6b5a09f3d272b2d924eb6338bc12d65a182dc5866d5877eb4350acb43060cb4141ec0b7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part522 : Excludes 0x100c0004000000000000000000000000000 0xeef39f8a8f8603820180008000000000000 :=
  finishCode 31 0x390d04205095b17062105e831409c83d7b4c8035abac072fa0e2b17399a51e501ad5ce42d5b41ecd5b2d4ca09518a0f56ae72556114389ad5e0dba0cc38f24cc12ed5b3f9cd496adc20d828883f711ab6d539022d634768fcd023177decb251d022d212d61648fcdab65df25ad071057b52569ad5b610593356cba6b571f9b56e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part523 : Excludes 0x100c0000000000000000000000000000000 0xcef31f8e878000000000000000000000000 :=
  finishCode 147 0x390d22d0527890a2af23d8a29920ad5b83a836ce26d399ac6d5b1f99e10759286c4d51ea0ce06dcf42c80db5c07e67d1987e9ff498c1ae38ba50e83a9c4ce2ef694ffce4b69fa07d0620d3681647a0a2664036d3c720c8235a6a8f510629c7174179774e67293e40ea0bd046a11923ef69837a0c505e93b38bbd0f62e00db40ec82f0e88b265959cbd6aed5985d30717b4a07569b28e60e282f891ec581e4498836e38bbd9e419ad360e32c7d69a0db4a1c83d418c83d526c1c5ab6b4d06db48b42809e1405143b16c51da93e242eecf656b1ad3c7e6f62705dd8fbeb3540fad3e30f2c34f9e81f164cd5b7b2c3f3611c44907e6b23907e3d37b0fc72cd547ab4d51ed07504da89496b0b24fc691751eb4c65a68f25c0560c8491846a88b261f9a504859ab65dd242cd5b41fcd455128b25ab61b9531846958fce164b56e69796f5ed2b4d1f9c2c95a6b0766adad347923f348bcf696c1c0601841e4a180c11f9cd6583f92d5acb1b4d8b70ded1f66d36b1bda658fb5960fe0c3721c3f35d1846a8c3f32c0cd5b7b4b90dacaa159acae22891234de376b56c7e6ba1e01cb6adc3d36b2b56e1e9830c5bb356d69b30e40121d3698a45c5920c35b1a629e06de5a6a0fc59281f907e0c1923f122d83f3840bc407bda507e9ff96465cb6b2b55e17497907f93fab2348fad3d472d6569bc93183f8ba5ab70ba5a6f0b25abef6940fa0fde85b1c441fa28d5b9682b395a5af82cb85d2f695abab019d8fde1ad3f7cd5196aed0388d80ba412727f49aa8d7607ad351f63d183ed07150aad351f6f6d6ad97766ada04502327fded2c275a6a0fe (by decide +kernel)

private theorem part521 : Excludes 0x100c0000000000000000000000000000000 0xcef31f8a878000000000000000000000000 :=
  splitAt 1 110 0xcef31f8a878000000000000000000000000 part523 part522 (by decide +kernel)

private theorem part519 : Excludes 0x100c0000000000000000000000000000000 0xcef21f8a878000000000000000000000000 :=
  splitAt 1 124 0xcef21f8a878000000000000000000000000 part521 part520 (by decide +kernel)

private theorem part517 : Excludes 0x100c0000000000000000000000000000000 0xceb21f8a878000000000000000000000000 :=
  splitAt 1 130 0xceb21f8a878000000000000000000000000 part519 part518 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part526 : Excludes 0x30041000000000000000000000000000000 0xcffaabe698e208200000000000000000000 :=
  finishCode 15 0x3789e079de85b0c4718bdccf2cad69a625838c4f55a6c1c615fa0bd0626255c106320fcc4ab62d5e7b4988d287b5c7c38c3a0f49eab4383ac15d154c1cd066f69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part528 : Excludes 0x30050000000000000000000000000000000 0xcffa7b9ee0aa00000000000000000000000 :=
  finishCode 29 0xf6388e4079d682ef835d65f1ff587e939276b4a6628b0fda5313b4bbe60d6716c5518830596a641e988d8433dbdaba5a97b5acb588570c5e9278fba8fd40ebda547b2cbdab27fd7b4ca15692b40d29984707d490bda54260c1312b56e597a49d42b36062f7215450a8354993357565a6176aec4c90e5cb4330bbdae83eb17d6861cb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part529 : Excludes 0x30040000000000000000000000000000000 0xcfe93b86808000000000000000000000000 :=
  finishCode 155 0x1f4721a064178293bd05135619c3fec9256ada51cc4662506dcb43306a0be610836dab6d42a82c9a0e2b4d0e4ad0c393356e8c2ad35ec5a1e85a6989641798354731ffd406831607cb57417b50a4388a3f81ab06f7b49c647a320b5ed306f377aa8f43da6411c6162f3c1c5ed2b577b4d07d1b5963cc5ee658378f44dfb37851d670e4f034d6ae1cb0f3834e5abce2348ec079dc028ac0d306daa09620fe581b0e58ae9214e169f3da60eaa396ad9c0c7a72cb4a2b356d49f1f0dcae8017b7ad54a2aec2a80db2dfc29b4078b6d0632d35ed2a3940ec393393ad35ab682f5c0a2a7420458132d360ded5b51ca07584741cd42a2795a6c1bd07a6bf9812b2d41e9ff5ec711bc671a80f38b6e5a19c44e5ab4d8c16c82a0be20fc36b357566a7034109405a05a79c0d042b038236a3b7b68abe6817416e983547b356d69a5df698ca3b280ce5159aac0ded2b2f2efc703306acb590440c331cd505e8217b4c71f41f94056831ffd65a703306b0e65969f8d652c3f1ef940505e83f7a184710c1662f16dcb4339aad0e3779bbe72b9865c47b4c1b33969cd4a03378e03d06258c5e0d9691ec069a08651d977c58e1cf0e5cb83d8b4d949a1c941882be5a0d185607bda501eb4d6a170671633285d6af06f38f9cd550381977e837acb56ae9ff9632b016adb38962e8a816ee62b8b1c39e9211efc71959fc7195aab290002fc9ab27f54731879a82e57591a80657eb025ab66234b1602a4f965e3bd9646f62a0b6315e3ff977d07eba2705df72bcb3f163a046509a7fe57ecc25407872e312b38b22f071939aad368c2b56e0eaa4f05e93ada7f1afd476a4f7a200359c15972bad34c166255a6c2db2d4cd5d408ae0a3b836a831306ac5e (by decide +kernel)

private theorem part527 : Excludes 0x30040000000000000000000000000000000 0xcfe83b86808000000000000000000000000 :=
  splitAt 1 124 0xcfe83b86808000000000000000000000000 part529 part528 (by decide +kernel)

private theorem part525 : Excludes 0x30040000000000000000000000000000000 0xcfe82b86808000000000000000000000000 :=
  splitAt 1 120 0xcfe82b86808000000000000000000000000 part527 part526 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part532 : Excludes 0x10064000000000000000000000000000000 0xeff90fc382fac8000000000000000000000 :=
  finishCode 39 0x3d8de3c8ce348cc073d4730305272c3f905ecc2889e1bb4e4a90589d6a2b5a6b99651ca47d3c475c5e71efad3590418c83f48fc80f85b6a3f5a6ae0c82936735c1d569ab2d069a005062aa1c0e5968aee7b4ad3630b38edab672151dac5c38f2d3414e0ab791201e8cd3f5a69cd504283f37b9c85708c2c0b32f3b17c9d6821418b50b4d7a8cb438c2ce3b3e593ae5a6a0c59039ac0a92f3a89547e6ef057bdae508979ce5a1cb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part533 : Excludes 0x10060000000000000000000000000000000 0xefa94fc280f000000000000000000000000 :=
  finishCode 137 0x380f2148d9c5b1b84a1cd5b3938f7cc5e60b7b9cb296188f7cfde5ff6a1b8136cf6314bb50cc4a71906aad0b2b87a2d5b5a6abf6039a044dead5b629c9e7607a4dcc4ab824ee5a6983564580a76e6a0bdb630a70552783653fe8df9cd6c3d382b2872370b4d4a12631ffc58a943393c0cf035c6f56ad9ffd0c4a105edc24c65ab9fbdab62ad4a1b56e7b5b0c56ae7ef691cd6372c8f7dcca931968283f275a89e2439bd5ab63d141fc00f2370ce340b8188ce6b2c55a5671f312b79043209e2f8a295279c4c17f2c5dcdb34bd21ed2f9402d534879cccf6f3d455fab43697a43c17f2d0da5e90f8c2d0750b7932ce12e57389b88d42e07099a8a71f39aad8ba2f90758e127cb392873ce332cfe835a93542f075697cf630fe6b1c1ad67e7136a4c60b5b0bbf34e51e2c25407982dac7330be320b55825eb01306b945402709392aa060d89d6b57381acb4c1b356d505d1144b230b174d5ee60d4a28e7683ab09630e60d275a4ce606b94549b20c581aa0172bcf6957b9835ab693b8c1a962e8cc2d8c8203e417acbe0e797fda8b24cd21ed4595fa3bb5aab56cbfe82f96aad3d8e66717711e040138499c3df37a9cb53c6e1477060da8ad5f39aac0e6ad969da8ad5f39acb2f396c90f39a871d7c48fd07f3ffad5438e0a7417c91f41f9b85b06a9c93359fa0fda7b02dd85eb416afb91549e3df6e1a85c0397351417e2c53969cd5bc311743e5ab80bf8e321cf490873e4879c6567f3154f005fabf650aa40d5fb461ded306f5a7b56d28a4b7612c4998c3bda630aa4f6ad9f2ce32ba293e8c2bda49d63bb407ca4f61193ad87ab620c6417873d286adb58e1dd9b45aa741be30a3bb (by decide +kernel)

private theorem part531 : Excludes 0x10060000000000000000000000000000000 0xefa90fc280f000000000000000000000000 :=
  splitAt 1 122 0xefa90fc280f000000000000000000000000 part533 part532 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part535 : Excludes 0x10048000000000000000000000000000000 0xeeea1b86889240000000000000000000000 :=
  finishCode 71 0x3e0e4348d02a851d293948e30ba0f47e6f40ba6291834e48bb88d42e05158a4671f39aaf8ca14547e720f41a72cb45b71ff47e65236979c65a5f182d4263f328acb2340f4144d84017cd63411988cc4a5235020dede1865ed320b41aa6db6a9bda6733b99e7b4a935a86115471124396bda651d972cbce9055a1b4962e5a93ded2a1148fcd3f527ad0dccb247d2865cb8e32495526c1bd10509d185526979ded26fd36dc5e77a0c17358ce3252341eb4fe5aba93cb9690539aaa85235b107b356cc4683d9ab60d5903ad5b317b88f430862fa0ded5b2d1bda4e3e3f3291b503d18a02f6938fb58e5279864e5b14047e69f198be6ef30c940610680a46c428ee17198bd6406893b5a47172dcc6c5b7b5ce636ada0ce276b880d58c5e1cb305c62f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part537 : Excludes 0x10042000000000000000000000000000000 0xefba8bc2c08421000000000000000000000 :=
  finishCode 105 0x2087c1a0700a12d2148d94671280e3a826174a91562b2d356aad63408bdcc19e94250e4868ba548e7ef85d2a1f408cb452ef93d60fb41c4bd282f27aa78b613d60e33dae0eac5b7b4ac2569e3df6e15fb241585692957ecb1550fb1358568135f194174ca1f7b4a91438eb2f8906a455238ef6416bda4bbef4380b6148d01f1ff505ed5b1efb00a21c65686adb52672cb90d82707757fbdbd69ac27a0e320366a4b88dc145638ca484e6aba1f8b6177d6af0f7d6ab309cdeb20bd8272cbd01ac2783aaca58af2085ab6ce348dc071d82741c58b6e4f7b4b4dd01e51561fcb15609a3c5ed6c5759fae0dc41ce626a7adab6c2b3889cd5ab73da4156b4d626c1ce727b0ace32c5b64124330ad06251562dcd5b4f0a46ce328de2d35481efa6881d257cc1341e93566adcf635c1ed72d5589a8238378ba49db208db81ef918e57eb97e0ee083735833c30341f4106b5589dab4d681b05a2c0cf068a3c6730b56e0e27cf174871e5aab56d14291a78e21385b0584c80f493ace4196b39969b20c5ab6d31493ae0980e066ad8ba5aca8114f8c2e96b2caf350eb4e543e9274b170711546adcb0941f9bd4e5ad82bfe3ffb52d07ec499ab67276a5a7c6624b56d07eb57943ed3995fed5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part539 : Excludes 0x10040020000000000000000000000000000 0xeebabb82c18044802001000000000000000 :=
  finishCode 121 0x7c2107a1c066208291b909e1424a4e6db8e66f69838ad35cd7161507a9f1838b7094140507f354569b07d306966640fb56da62b4d8bbed5b72150571145c09c2903493a801ad943a61957fcf677b3c3bd504a915b04b1062a45858ec41b367b4a7d630ac0951cb56e6049b360d30285acae456adb10d818653d32825406d5b9c92d2b69ca76d412d4b6a5c831501ab6b834c67b4ad35832c5f30ca589e99416351a0ee9158c2a9365a6bda565b2d35ac63df431b06e101ed22e05154f105e5f5985e3df512cd5b3178b3e8c1a8ccc4660b9422e595a6a0be3073dad49af512ffa0bdb8550a2ac228ce6ad98bcfdec55305b9ae30c92edc873dbdab70716179fbcc329e1fbd545a6a00e8378f7dec6b5714bce4f721b96630f177dea2b81455a062230b0d65ab65df5048f7cc3262f6afcb4d41f8f7e0fb3154c16d5b595c6ef8c1b155ab6623305c10d0354e604a0ccbff07151ca03dab6509293b305153fec7336adcb627886356e30ca03cbfeb8182d22b41fc7be6197b4cd82e0d0207d3eb3085ab662f541edf20fe0fb356cd670d2d416d5b48798666ad988d27334bd21e6256b1b70d220fe1ef9404a4eb8144e8c1bda5812b4d38ba0c505ebc280616a944ce5f203c7bf0b6e306b57417a03d7c6e0c4b2d547be50128ab90d017fe50eacad07ab575a69425544f1c80d5a2ad35ac65ff695cd4b3fe9c1562b174dab63df306ca2930c949dc8291a04e5a697fd07a6253909cbd9c5a6c5ff31293b6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part540 : Excludes 0x10040000000000000000000000000000000 0xeeaaaba2808000000000000000000000000 :=
  finishCode 55 0x7c03e6e42f0b2148e1f993d4a12f0348f4149d985f0a470027c64a3b56ce66f518ffa9137b5cd23419b125ab69f1406c9135a6bdcd68a7ef4a39ffe5aba0fd98384c72f291ae0b62044c5f15fd69b1836ada0fe0e3356c4934615a7e623470c60dab6b57382a906382b08f4380f51969a6233f98ba4a463f38e0a60b312bc0b8149ce5f41bd69a83f4a1a03e3979c865a6d06f293bd0e03596410ad34a46ce308a60fccc4aa4f93d6b3f62aa0fce5b3da587a58b9ab6f69174c60d16dc353596976ca0271f408a0fdb8291b2906f92467051f98ba52471835946410267cf92267051a9cd593e7a44d8bf350d1be947 (by decide +kernel)

private theorem part538 : Excludes 0x10040000000000000000000000000000000 0xeeaaab82808000000000000000000000000 :=
  splitAt 1 113 0xeeaaab82808000000000000000000000000 part540 part539 (by decide +kernel)

private theorem part536 : Excludes 0x10040000000000000000000000000000000 0xeeaa8b82808000000000000000000000000 :=
  splitAt 1 121 0xeeaa8b82808000000000000000000000000 part538 part537 (by decide +kernel)

private theorem part534 : Excludes 0x10040000000000000000000000000000000 0xeeaa0b82808000000000000000000000000 :=
  splitAt 1 123 0xeeaa0b82808000000000000000000000000 part536 part535 (by decide +kernel)

private theorem part530 : Excludes 0x10040000000000000000000000000000000 0xeea80b82808000000000000000000000000 :=
  splitAt 1 125 0xeea80b82808000000000000000000000000 part534 part531 (by decide +kernel)

private theorem part524 : Excludes 0x10040000000000000000000000000000000 0xcea80b82808000000000000000000000000 :=
  splitAt 1 137 0xcea80b82808000000000000000000000000 part530 part525 (by decide +kernel)

private theorem part516 : Excludes 0x10040000000000000000000000000000000 0xcea00b82808000000000000000000000000 :=
  splitAt 1 127 0xcea00b82808000000000000000000000000 part524 part517 (by decide +kernel)

private theorem part506 : Excludes 0x10040000000000000000000000000000000 0xcea00982808000000000000000000000000 :=
  splitAt 1 117 0xcea00982808000000000000000000000000 part516 part507 (by decide +kernel)

private theorem part490 : Excludes 0x10040000000000000000000000000000000 0xcea00902808000000000000000000000000 :=
  splitAt 1 115 0xcea00902808000000000000000000000000 part506 part491 (by decide +kernel)

private theorem part476 : Excludes 0x10040000000000000000000000000000000 0xcea00902008000000000000000000000000 :=
  splitAt 1 107 0xcea00902008000000000000000000000000 part490 part477 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part544 : Excludes 0x10028200000000000000000000000000000 0xcf6d354e8855d1141000000000000000000 :=
  finishCode 33 0xf4400e63089e18bcbcb0fd4c16f6b8bca0a71faa886196a9c5e5463a9343cad5b275c7a90f2a7a433b3403f56c017f28eda8a1d505bcd5b876e2db681906a20f73574142d5b2758f443920b187a2882b09e30be04eb17d442f2c0a1508a93457f1b9cbca4ad508a84651fb0bd622c5f5602672d54bca0a75158afcb9b392d82e8c748fb58e0eea2b2f2c0a5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part546 : Excludes 0x10008a00000000000000000000000000000 0xcfef359c0c48c5455000000000000000000 :=
  finishCode 83 0x1c8891e86a1a02028da61bc93dcc02b530f2b689219060b83ac7dd611b4bd8aa80b88ced633c1902f286fe59a93ddac741f566b13ddac61bf83eac0f6b9423183969ec22a8da28860b311b08e835b155076d63a3061bf61ea80d01b8e5a79805ab7358c9ee7834e683ab94dec65e56a8b4ce522b535ca66db80a2f6b4f09804c5ea0220d398c02d398c32b099ec6f6b480acc5805e170641a86b1c2db0e4a8ae0d482bd54523c5e569c82951050144ab1b9a96c5f41dcd5b467a8fd3c26c17365a3a0ed6363af9456835471077131d456c439826d396a9a20a3f949a6c34d6598a8ac56a5e527bcd4b2cdb5341922b54f1405311c04b9f0a2b51f8ebe6a5b59d413460c75ed4b7bbcc1960bcc5f6a58325456d673facd5141da8ada6b3075076a2b317cc2400d02f062f51fca4d41da8fe52689866988e8dac6d6527bb56c32a83b61ecc5571c93ddca6d5b41d9866042b54dac64f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part548 : Excludes 0x10008280000000000000000000000000000 0xcfe7592d8844c9445540000000000000000 :=
  finishCode 67 0x761a8662246107faac348e3e897d4e0219d40ab56d06a2e99036701157b56c32b356ce1e3d18e020c339b8795a05c1586305bad5b981a9e9054a4949fe7dd8bd2d5b6adcd298ff68ff4a39cdc9fed5b9c0681a46d0e5673762aca0116ea8f47a341a566ada0b7627f9ed61459794f840da7ae72a972c4ca825380cd2f57ea8f640da89547eb8340ac2c82e92faad3e8c2a4949c2a4f729c3d16ada88da356d67328f45d2a3b373d185000b59da7228b5918a745d32c8c9fe3d151158531344f1477356c11ec02c00af9caed5b0d0b94e8c1b9455eed5b72a972cfb73525646d5b2e581e63e8b14d652d4f80f27d16b1b155cbb358d6467db51db56d64527c5e5591ace5ca734bd402e39463c60cbcaaf7591b4661476c2396729259846c55594b4a5cdb1f6da9eb4f72ac6e5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part550 : Excludes 0x10008240000000000000000000000000000 0xcfe7398ca841c3241248000000000000000 :=
  finishCode 35 0x2f8c8380501680e571cdd6466037f16f5426d5b47696ada5e60b405a0ecc1728fdab6701848e2db157b56cc170028fe5268ba558263ca136a982adab683b0dfce0308b2358ce6eb459ab683b380c09f85d2d53387a9366b18ba5847a1fc590c1662f6b1cc3d59ab14d67283b157cd5b40a931d580cac83b3f5cb396ad8b25077356c5b6a3f395bb0d53515c3d13739c3c55f0f44dce619 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part552 : Excludes 0x10008200010000000000000000000000000 0xcff71dcc8842c1861090280104000200000 :=
  finishCode 55 0xd0348e03687377a0a3a9e19462d5b202acc67a080b1c3d18ed3949aa91e661701fe864e463b124c5e2e94948ede311b58cde26f1985ed5b5128ba5986c1e8124c6ff289879578601582899795403fab05e62fc6160d2097127cd396a8b0ae588ce53289ac6e69c8a2cbca7b7a0ee8fb1fe8ba564790a26a3f949a6e396a6b279ab66ff5e1ac6ac206c7fab559a5ec3d305cd2f5c1e46d1242b0c1707584aee6d2e5b4bded65e54f19b9dca7047d3c6a4d62ab4bd3c729360fa5cb9a5ea4d498c1a4dce497837f07d373a48da3c8c0b8e02d2f834a78e0faa11000c1bf83ec1de7b5897e736a78cb965e5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part553 : Excludes 0x10008200000000000000000000000000000 0xcf6719cc0940c1041000000000000000000 :=
  finishCode 135 0x348be38050b28a9ea683487953b2b353959cdd22f0e6563ee634948ba47fad03d0527202c62f372c5e57a1785307fa9e0ade1d6824565260b3118a72d55a6a91f6b3a47e51dcd4f5a7b1556479128305b4d63edb53563e5e5629b15549b35960ea7db5848ad683aa8ed672b1f48fcec179616da4c66a6a93da925e7661b0601a02f2bd0d43c81e569cc51359398bc7a31d02dd508d185311b54569f185966ad51311a80d4f289b52604bb4cc3529e19ab67f50e4b4cdd87a1e41feb68d678932c55692b08cc1637195ee7d1697b58daced37942ae6d6a5ac7c5b71fd589a64179daced598b96c55476cd2f681e86a1940f2a76647dad3d66a2e94f0c9115a5ad3d69f34dc5bac63576588ad4ca26e5382dad5d6b3bd0ec359e4988ff561b359c2ef460da92d675e1a06d0c4718bca26b817a6174b53e7b6b54d69e3fd6d1ace3fd305cc3b021ce22285e278af755160305b90672e822e71cacd5ca6587300cd6737fb94e6b2a78b218be168b59d44e60b96a7077a0ded67611ad4d602f4cd4f6b3c1a68378edd3c83bca01514982e0d341dcc5eb22f09e144d1816dc19f6b1982d49ef2350e513b56c5b660b699cd63054b56d606b3c0ab6b1d18383880ddab69e308a02303d18c5ea4f5512483ecb53513826c11e60b736c35304da8fe0e307d5a98b76838ac4562318bcbcf06f857ef42807c359e729899542a29b2f4b40d5d9622b538c1d071729d071526b94e838a935546adc7dd71d931cfa260b31198be (by decide +kernel)

private theorem part551 : Excludes 0x10008200000000000000000000000000000 0xcf6719cc0840c1041000000000000000000 :=
  splitAt 1 100 0xcf6719cc0840c1041000000000000000000 part553 part552 (by decide +kernel)

private theorem part549 : Excludes 0x10008200000000000000000000000000000 0xcf67198c0840c1041000000000000000000 :=
  splitAt 1 114 0xcf67198c0840c1041000000000000000000 part551 part550 (by decide +kernel)

private theorem part547 : Excludes 0x10008200000000000000000000000000000 0xcf67190c0840c1041000000000000000000 :=
  splitAt 1 115 0xcf67190c0840c1041000000000000000000 part549 part548 (by decide +kernel)

private theorem part545 : Excludes 0x10008200000000000000000000000000000 0xcf67110c0840c1041000000000000000000 :=
  splitAt 1 119 0xcf67110c0840c1041000000000000000000 part547 part546 (by decide +kernel)

private theorem part543 : Excludes 0x10008200000000000000000000000000000 0xcf65110c0840c1041000000000000000000 :=
  splitAt 1 125 0xcf65110c0840c1041000000000000000000 part545 part544 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part556 : Excludes 0x30008001000000000000000000000000000 0xcff647a61a024018e001000200000000000 :=
  finishCode 51 0x1fc791845b1dc317985d907c182f34f5cca70d699947ca4e982988c1c354030edd8bf075699b48d82f3995c8704760fac2f241a7b476f317cb7ed333dac025733bdbce1a51d0e5ab8a09982ef69264b05e232b57d862e416a0c4a9a204e293a0f60fabe20b587b149d686f698a4e4f7949ef81865c828ec5277b4ce4183ebdadab6735640c87b5c4c7514b57e69993b5a7a0819aae7e37815429396fe5a1a00ce564ed7b4ca2916ea075a9af6b8e1a73740eb90d2320c63085271eec7f35279ca4e6ef69903ab1f87ba82d28fb91e2d5a0f4e6e2dd7b4c81d289bda6387b4c4e522dd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part557 : Excludes 0x10008001000000000000000000000000000 0xef6443840a024010a001000200000000000 :=
  finishCode 141 0x7d1c8691e4711b4293c619201906dfc7019029193b6285b4c67b4892482a8dd82f6d4d1cd8ba4a16415276c93539b90559855081abe41ee7b491d5ed6c33371a00d3ee4ed610fcb200c5b65234ee985d7823ab48e6ab9474fcaf6b942a007401b58c241ee7acb56d85e943291b20f69942a7e58a3af6950ac62586d651d4119455e064154401c82329193b4a16f8310527732cc1b2ee8b8ded23fd393ce45625abfdcc6917291b58e2330d4d1749c852369ecf69131cf6f730b986721bdbc323398cf6af51593948cbd33985885e1ab70ba50463fd1dbc7ed617b1252522e961154291b91e289b98d006b154fba45e57fcc5d7a8a00ca3acc358b8148d6472bc1c7168bd9e174bda52629f78546b83da605182d58373da588551284199c6e7369cdd05a9298e6e91f903a2e9551a9b04dcb46e57386a87d0061c78dc6d4d7f184790a46c558be6623206bda658f97a542ab4b79170474cd650239055ed25f530cb53e289bda5a72415837c72d7b5b4e505af69289a4d6488944c7fac2380d0148ce1b102ce52943903680b985e2e9280900d7c461c4276c1f67b5b05d26ad5b6268ba5885b0fcb1865ab670f30ccf6958a898e6b2bda48fed5b8fc6b151749405fc710c32f809066adbda4dea8fb39ab906003b04c98e7d59ab6f6923aa93e7b486b5a62c2400da38062f305a305231cccc194f6a4a4397356e0e5b4f588291bd4657fb56dc8e0b71fab9b67a8b56d28681b8a46c44009478bd23f530c8ab61fab88d42c8761c9c98f30c5aae9234f5a89cf53312569ee49491bdad546adb48e7b5b17498e937730c6db2639ea5226af72deb209c3dae5a5a93e7b5b98c2673126263a8f4db6d5b (by decide +kernel)

private theorem part555 : Excludes 0x10008001000000000000000000000000000 0xcf6443840a024010a001000200000000000 :=
  splitAt 1 137 0xcf6443840a024010a001000200000000000 part557 part556 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part560 : Excludes 0x30008000008000000000000000000000000 0xcff4270f580540008046180040000040000 :=
  finishCode 63 0xfe3d0e62d8c238062f551f030b931e386ad145b6a6356e386ad15a671795ece0d57718bf17943ca0d50f2cf6998be617561c030cbda649183343ca4bd9a8a7b7526b56ded281d94061cd6ad87950472d5ded21e530c9895587d188441c82fab56e1eeb094e16c55416b56e5abcf6939b8795200f2c70d6adad543cb356ce1707943cb356dc8711dc641f4611c05b019ef699ab6e6516d87167818bf1bc4e16d5b50fca472f38726067bda41a7072548f1c2d8660cf1dac0cd611a4371a91e27bb94e7b49795eef287d48e4f77b49982db9ed24c753149b179ce6eb452f3cd5b0dccf696069c3c5ba1e5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part562 : Excludes 0x10028000008000000000000000000000000 0xef7d275dc8154000a444080140000040000 :=
  finishCode 33 0x3d0cc0796291bc0e6356d8bf348daae61906ab926691b55c19f388d0330f0320b55928670b0698725846901a7245d01682554123f3da4bca07d9ed24bd9aa67f56ad81f5ed27f58bce2db2cea0ec19f34fe48fa50c1a6cc3205e558ace6583d87247a294220e43855ae5f92867a9a30af69526b925ab6c3359ec3d1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part564 : Excludes 0x1000c000008000000000000000000000000 0xef77238d4a0178018054080060000040000 :=
  finishCode 123 0xee3c0d2320be2a8bc1404a16a6356d2631cdd68693b1fdcf695a1ad0e48ba98515410de2e639286a096a7a47d41307257840dc1c95049c2e699b889c0fedc0412bda60698b6ded3390dab60d39ab69f59cbec2f2f29b1c132c49386b40c2388a80fee0c395b05651fa50e48fcc2f3949c2cde3250ce36aa39088250a0282da72a47692c1356ada8440fec5f03fc1979cc6f6962fa8e5a72d5b523cf776b1834ded2d5b9ed2e636b19c2e4febda47f73009c2a07a1795d868190610392a2b9a66f69724ac15286a2b9a663d1724bda544b2935cbe91f7b4bda65158a1e04d88c4b323d169fb995ed293b52185f0f4433a7f5960a9437b48f45543d11c76104136bda54567e59aa607d0e4c139898e7d36a4a4ed277354dccf2845ab67f5580b575ed2d536adca2b7b4b40a83b0c20725a93250d42f359d68e7d169cbda5a730705ed293b1e8979e69a931dacec4772e8725a92f694f05b73da52862db8bc7b4a3266b3b575ab6e49732b94e1daa8ad276d3f6aeb80da1bfdac4f019e92985b69436a4cf6d3fa8b6e697ca256b3a4ed2631fedd86211030100b3994322d630669b8d3faa255e1905b038ad5b9caa3e3523970d85ae5352693de0668ed6523ad0e697b9bdaa60c9037a7dd49aaa308d2388bc0fec38b2325ed281527ba0eded73994bce4f727bc099729979604c979dcde3b5836c0177b48d353ee0cd5158336732a8ad5427bcf691fd979c5b6aff8fa2e5f7b4b9250764f7812a099 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part565 : Excludes 0x10008000008000000000000000000000000 0xef66630d480140008044080040000040000 :=
  finishCode 51 0x3b0e4368cc1075cc206a00e2f2948cc16d5b8a46e6208e28aa7b60509274bead5b3e8cd434ec979493a4ed2069055847f1c465200291902ded31b845d270b94c291b40625962a6176ad9c35ab72ca45b71896276948dab71405ac6935174902d784d1ab62e98e1ed6350bc2e926ccc5f17497a56ae4f7611c0691b46b0806f0148cfa3248cbea4ed49bb56cc4b24dcc2f3c052360ac7ed62fa4dc9da50b60ace397b6b17d26ed358c168ed5a7a0b4c5e52316bcd593009404806e63484ed89eeac0ba64169775ed29236a1cc173d484a52222e9174c7ed (by decide +kernel)

private theorem part563 : Excludes 0x10008000008000000000000000000000000 0xef66230d480140008044080040000040000 :=
  splitAt 1 122 0xef66230d480140008044080040000040000 part565 part564 (by decide +kernel)

private theorem part561 : Excludes 0x10008000008000000000000000000000000 0xef64230d480140008044080040000040000 :=
  splitAt 1 125 0xef64230d480140008044080040000040000 part563 part562 (by decide +kernel)

private theorem part559 : Excludes 0x10008000008000000000000000000000000 0xcf64230d480140008044080040000040000 :=
  splitAt 1 137 0xcf64230d480140008044080040000040000 part561 part560 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part568 : Excludes 0x10008400000000200000000000000000000 0xee7f337d0d825210c00000110c004080042 :=
  finishCode 31 0x398d23d052727bad162918fee841ac681487a1b4291944e5989805acef695a9b59e7b4a445b46b3cf69289b99e2f2a3a630a7357b4b59ce2318bcc32f69289948e7b4b59ce3f3da5acf1684352513396b08d4148cb97399d652d6741e9c2ce6aca2e08d7969e2e957ecf5137e900d26f17d4db6b8358e1749cd5c832445a9ea27 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part570 : Excludes 0x30008000000000200000000000000000000 0xcff417571c8054014000001008006180040 :=
  finishCode 65 0x1f07a1cc0f2b10b82f0619312bb84eb9ca2513522c9357b5b99e3f9a31d84b3d9cc46bc3e8a814754134615ea27d1522b06649bb53d5077142b3da565e4eb440fa324dd647070d1ff1afcc2ef697b5b99cdfb1f09e2e04eb49ad1850588b75ed3284da66b4f527a4dcbcb3d4584b1857b4a31d84738ec5ba9238c2bda518e4eb5e1bc289b501c981a69e3084eb058c1cb50149f1ea5ccec47723ca117b4b97457f4614e6b32078149d50463c5e58c2bda60de8a3906527b906733c615ed2d67509cd67837bda5a9741a53fae45069b98e22900d15507bac23c8b2f8e1a9355aacf6d15eb9165149795ed2a159aca9138db2b03395bda4e1b2854e6e81d8e6e3dd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part572 : Excludes 0x10028000000000200000000000000000000 0xef6d37558c955000400001100a004080140 :=
  finishCode 61 0x7a1a8291835639387543caaa2f88624464a3ab06c24ddc8b399d3e23513d4bdad4226fd7b3cb233614233d8d61ae5d463b9b561b0d36838a3fcc324eb502006209d7317ded307b37ead3d3d23d18f52f6959ecd231e0ad3dcc72c248f6f6f4f49bf5a0641c46a1b40e49cb60699c9e5413c4809d6c40f45ed334cc162e4b8db70776a6bda4f6e825a30ad336a6ad568c28afc7a2c4391e7b4b98d4220b18c2ce677b7cafd4ec979523ea154a18725c4831a838cce430699cb53c6d16a7399d8be4eb255cf6f72ea09582ec5f7b5cb3f0008afded3077918e4ad4a18afc1a6e659ea2e6348fa50e0c6a01a7247ce6ab62f8b458396b299ca2f672f2b99e7b4a3a60f6f6b837b4cda92b2f9a920d3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part573 : Excludes 0x10008000000000200000000000000000000 0xee6617550c8050004000001008004080040 :=
  finishCode 117 0xf4350c441c62f2ac5dec68c740e8794a463f5206b88d610541a30794a46d02981e5276ce655aab90e72fb16decee5f84624a77b3942d6aaf8148ca170795c8b27649daa156921020db08d0148d18371bdb683da09526b41ed186b3d07b276942d04a5e359627bbdac0871839acf07b35993dd9046178276be09378a16a453c1506a8a31e4629c3dedee459ed2e47248ce63839a31ded223d9a633d8c9ee50b723ca1100f972c5d291149aaa8c822050b49bcf5137eb59e58ca095ea28259acab4537ea51d04b420da148ddc508cb537b4944cc333dad18eb317b4ad1d2231b6e0e6e517b4b68e6284658d96d4dfa5135c034b251cbea2e959ace67270a89d66b359d28e2e96d1a0690a268c7a30691f58bbd460d270d482834ca4ed4308c02585e2786ef2dace67580bda528672d801e8c7090ac0523ef69692ca4f38c9f0e527b4be0ee9fd733a50ded2d53857eb1b486c615286f694e0e2341bded2a1147dce676b3b945ed2d533116629e2d4ded3172d4771858dfb05d5ed2d235962f3bdac5b65151fdae09c35268c1a50d89af69396b59e39ac60d22e2db834cd67692972e3062db527a415fc7120c4415437e9c65a0285b17e505a91d60741ed04a9e3412c70d6a190393b4ce7b6b16dace50b463cb4162db48aa3da683da0953c6a47285ab0d4d8e362bf5aa9c36474b59cfeb359ded2c83da66998afd2861c9285b088259286c5b98624ad60b8afd20b41cca1693b386bda62f2a31ce561c9 (by decide +kernel)

private theorem part571 : Excludes 0x10008000000000200000000000000000000 0xee6417550c8050004000001008004080040 :=
  splitAt 1 125 0xee6417550c8050004000001008004080040 part573 part572 (by decide +kernel)

private theorem part569 : Excludes 0x10008000000000200000000000000000000 0xce6417550c8050004000001008004080040 :=
  splitAt 1 137 0xce6417550c8050004000001008004080040 part571 part570 (by decide +kernel)

private theorem part567 : Excludes 0x10008000000000200000000000000000000 0xce6413550c8050004000001008004080040 :=
  splitAt 1 118 0xce6413550c8050004000001008004080040 part569 part568 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part576 : Excludes 0x10028000000000001000000000000000000 0xcf6d2765ba9540280020000088000280102 :=
  finishCode 87 0x3c0cc3d0e03509378a469476ad9c7c3aa1e58910c291c00aa2b09eb9ab7185731bdad6a661947fa51e30b23b5ab64eb488ac165a3a84549ac5d969e9116215850167b3d9c58a6015a3ce57a30ad5b59ebdae725b98aa2f89118c2e935623ce636ad98bd4271855a7c619059ce4149a93ad64831486a149f306da7a0bd3939cd62450103678356e275ad3d49ed3d9caf2cc5405b147b1bf5476b4b51dcc5d7b393ada573174dfad5790367fb92869eb6ad8fd42bf1f35cc660d8c2b55cc4a3f56adc48ac32082b4a1c1c9498c72d41aa50e0e4a06dbc6a036b2894e4e735069ad91858396f6789d67359cc6a1bc5901a6a418964fea894e4e7353fdcd3d8c4ad5b5909d72c6cc4aa4f6aca89cdde73530bc6257a158275c9ef5269864c4aa2593d7185275b56d6c6adbdae50b93ad60a1b35a3b11c7773dac9d64eb9ab6f433061787ea82b291985e317af882b92861cb498c82b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part577 : Excludes 0x10008000000000001000000000000000000 0xce660345388040280020000008000200102 :=
  finishCode 149 0xee3e0f0398da38851d293bd0aa448b81074e6b24c52528238a4683d90461b3168c929732c72d619834624419c9e7291a415252aa399e6b2b0cd0461b3732c58b761547a0a16d400560d7825d3eed430f2903482a83b926a947522c73541d86bda880081a8c245e4a19cae393b53605cab052391d280b38da0ece37202ca17368d433112399e6af93fc3ca40d20eb101e540ec3dd41eb56e27fa84e492a00c83a4ff6adb56e6198f4c9fe41b6a081b079482a81b9b4891e879128201985c8364eb8a46a47291c9476b17065128291ce573db8ba49ea9314a1b30c4148d7c1fec2d1174c1d64199bc47fac2b93ee133494833e0e3a4a471738ed632f5f37082a49eaa1f067948cb47287c19e523523cb1939b9ff49eae00fed057179ce360cf8c2c9312f393d5c0312c71b0679cade8790c4b18bd7c378c0bd16eb4f6419b57d74733c5e727a8f4dc7741ade85e1d838dc80b4159055c056148b166cfda9353ed8b8ca46937522c523522c2e9174c5236a1244a1bdb68c28255a66905737a0acf96b434fbce6f41ab59d20a737835e3b74fba8cdd86a1b4891e4206c41d661bc1fec1be06780f5a5681d3879cddac625a806291b91e276b780d18e6e6c99046c31174b98c318e1e7370678736387a074e5640d89db30cd8ba81b20db08b2148cc5e937a0ee91160c82cc16b13b49db3b112368f51906a0cd1fd906da871ccd4d371a0d4e324155e10c41da91661693b528e4ed9a62aa1bf627ba7dde83e8c901291a7f66a6b78aa0334c332bcd8369351e9a2061962fd1856b2a7f54574615aca3d3962a4f739a879528f1804c324f7 (by decide +kernel)

private theorem part575 : Excludes 0x10008000000000001000000000000000000 0xce640345388040280020000008000200102 :=
  splitAt 1 125 0xce640345388040280020000008000200102 part577 part576 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part579 : Excludes 0x30008000000000000008000000000000000 0xcff40747199240201500500000040000008 :=
  finishCode 91 0x1f0771e0731f4590a4ed4144de8737cc3b06aa0b50466250f2a708e1794e5b41c5ed2a4d2f3cf69838931e50bc1c4dfb35763eea074dfed5b0f2b50f4378b20355ab713ace4e735312cd5b312c6172f29cd5ed302fd45272739a8725504f198275a802c17b4ca3d6add0717b1cb290e5a802c1926e2bf1e8b56e3dac1d4fa2625160872e6adb509e07955438c93ada531cd5a4717d5ab6d43942a6ef40ea78aa13ad8bb0eed44a9476ad8f4cdfb359ded29239ace6fd463b48d43588a02fc19ef69988a2bb579c181728c6154729fd6b3b054e5741be0e39c6c576aa3d0641894c464f5a30a92583eb0f5edb39549ea9e1b8671cbdb4bce4f55b1edb02c4dab3d94fa2f6715f9896317b10f42e060d9422a4d0f298bcc47350bc0b6e0e2b78a25949b06da0e2aff6169c64bcaf6b944a0b1526a4de3e8b114dfa1e578188527c81d0688735c473108068a8a67b6b0b51fe5e534dc91150aa00d40386ca4f1dca8551ff1795ed7293c772a15395c0cf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part581 : Excludes 0x10008400000000000008000000000000000 0xee7e037d499242309400100000040100108 :=
  finishCode 29 0x1e0731a46509daf80f8e2f2a804806929482949d82b032c8062c18e329c350e2919c7ce5ab23407356b3cc3115fa8ecc3306f9aced438a46ca36828d8b3291139aa8ec80682d4e0e16735263c9d90978eb60f6c45291cf696aea8ee1609c66106d0a46b4583826170c6c9376d182a2bb83dc8f33128314c2e935835e937 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part583 : Excludes 0x1000a000000000000008000000000000000 0xef764f45499355201400100000044000028 :=
  finishCode 37 0x310cc3083fd7014033da60faf6b1e89794e3e52348bc9297b4c1e5731f0680a2a7358bd28fb174944dacf1cd5540d0cd5b05093b544f2d4daaec19174a80aa28543420a98d2a6d96afa0b6307356ce4f356c9fe735661c0611e0291be0a1585825e53968b06051c2bb1dcc0d116087958439ac94348bbdae2f2bda5cc068c4ed28aa78727947ad3d6a6cb45 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part585 : Excludes 0x10028000000000000008000000000000000 0xef6d274588974020140010000044000000a :=
  finishCode 75 0xf4330e03505233f2c2c16ad8fd43caa8320f6985829471e08f449d71865ed2d5b9846a2003d125324ed584a1b95e6aebda47ea5434be3e0b56ded3185962a81b6af8b050570fd49d741bd0760b340d9bbe393b56ded2b2388aa3505ff91e6a1369eaca41aa7357316c520c3262f488cb274f4c9fda0f71856ad98649d6c3d9ab6e5137eb4f49d6d2383969136ad93adccb317dc86a0358898649d6a3d486cf5f69ea44cc2e6256adbc0cc320d0350c20725ca328a5036f69494a50c172f699845f1a4058a84e41da06d38275c7f57b5d1854648f4640dac1568e5e56b3d1853e893adab6d21cd65a2b59d42e0af41aa47e595b524fa20af4a1b481cb9aa67fb4a19cb5ed22c17113c396b4be6adc615ed24eb7b5c8c7697bda523f34bcbcae22a8b61cd5193356cbcf0778776d5b275c1ee6ad93ad6232cf4ddea3d6a014e2db906a943275c82b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part586 : Excludes 0x10008000000000000008000000000000000 0xee662745089240201400100000040000008 :=
  finishCode 143 0xf4350e2105620eb30e61035f0700a17148c3cada3409058a3a527305cf699286f6b160b084ed9ed660b291a78722c562768b05862d576afa766618b48c98f3dadedf1ea56562c10f2948d90731a028a988e317a47e08fb57581aa4f7298b6d3c50a8e4669ea93c7a33dad03a4c7694944e694a894c5e8236918420daf0935903650b291a0ed85b138ca1652349ac4f7771b44f17027a989658da3a45d26fd9cdea3b3f9ac6c5d32102e97b4c52337e9795a672d2ded252337ea205232e8c61937e9fce49abdad4566196d1c4611dc1fdb40bc358e7b28714fea0a727a944d3c6a0dc482a50dbc7b6c7196b1972ded2d4f37f972e1b2b4ce30a5e52f3972e514b53d5435fc7d16999bfcfa65e7624cd675a99bfd1d26ff960a8e948fae0fe3996699a45d23e7354a1ca1398b60296a4a8ad20ab82f0aa02c4e3f4615ed25e558d829d1c4f08ae64f7bdae30b1fd5e06a0bca3d19ed2e4958d9cd5a6b3da630ab3104ccc174f7b54dcde5e76f1a673da4dc2a252f3a8ada67461519e5e72f2bda590690db73dac58272727b949d70771a733db4e6a8e9289a8ae69986a47a27276b3cf697adcf6951cbdacfea2c1289bb8c8144cbcb34fca3ea4f694c47f6199ea5ac6f6b482af0b830ce7b48b04bca0a10e4ad4e62297954562c18bca9c388d23087220d4d880189680b9ed29e37b6942d2869052f2ce5d4fbc737160b0cdec730b4576e417b5cd297b4a7f49eefe220f699862a3f4fe8254dc26fd781a84d0e4f1859ed6d3304ab59e482bda5086b3ce6f8c2bda4bca9d9982e1278c2bda4feae399656d4393c2f6b0cc82bcfea8e0b054570724a16a3f7b4cd53611a45e0a16d67968a0b9594a416378b506d3699cb2b699ce39699cf6d4f0b59cdfa50b (by decide +kernel)

private theorem part584 : Excludes 0x10008000000000000008000000000000000 0xee642745089240201400100000040000008 :=
  splitAt 1 125 0xee642745089240201400100000040000008 part586 part585 (by decide +kernel)

private theorem part582 : Excludes 0x10008000000000000008000000000000000 0xee640745089240201400100000040000008 :=
  splitAt 1 121 0xee640745089240201400100000040000008 part584 part583 (by decide +kernel)

private theorem part580 : Excludes 0x10008000000000000008000000000000000 0xee640345089240201400100000040000008 :=
  splitAt 1 118 0xee640345089240201400100000040000008 part582 part581 (by decide +kernel)

private theorem part578 : Excludes 0x10008000000000000000000000000000000 0xce640305088040201000000000000000000 :=
  splitAt 5279 137 0xce640345089240201400100000040000008 part580 part579 (by decide +kernel)

private theorem part574 : Excludes 0x10008000000000000000000000000000000 0xce640305088040200000000000000000000 :=
  splitAt 1 72 0xce640305088040200000000000000000000 part578 part575 (by decide +kernel)

private theorem part566 : Excludes 0x10008000000000000000000000000000000 0xce640305088040000000000000000000000 :=
  splitAt 1 81 0xce640305088040000000000000000000000 part574 part567 (by decide +kernel)

private theorem part558 : Excludes 0x10008000000000000000000000000000000 0xce640305080040000000000000000000000 :=
  splitAt 1 99 0xce640305080040000000000000000000000 part566 part559 (by decide +kernel)

private theorem part554 : Excludes 0x10008000000000000000000000000000000 0xce640304080040000000000000000000000 :=
  splitAt 1 108 0xce640304080040000000000000000000000 part558 part555 (by decide +kernel)

private theorem part542 : Excludes 0x10008000000000000000000000000000000 0xce640104080040000000000000000000000 :=
  splitAt 1 117 0xce640104080040000000000000000000000 part554 part543 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part590 : Excludes 0x11004020000000000000000000000000000 0xecfeb291d264488c0201000000000000000 :=
  finishCode 53 0x110390fc5a6be093f7223073dbda6ea4d522ac645a65095817c51fc0a7618c49962fc1fcddea4d698cb574f5940585b3dbd68e1b36d1f0640a3aba356c17a7259866a4d836f311662e86cd49b0b4d443f21449fb94e72a86f5ab672198072ac0c10e4af8ee39962db933d6aaa3f28fb8e672ab56dcab28f528707258c771b4721f06e162f41cc5b693b38b944ca4e50981772d1d6a63df1b2cb050d3ac041763df49fa4ee285bd447bef519866e3905ea4fd28691a9328c49eea47741ac7179ce42e6749dcf755aace43839b12cbce4f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part592 : Excludes 0x13000020000000000000000000000000000 0xecf6fe00414640980001000000000000000 :=
  finishCode 51 0xf83a0e43f8e0039db85603bad61bbe5a28f94e4215d967e6ef944e2d35a6b684ff9abeb2b5a69c94e5eb3f814a5b5595ad556ae2d389fe93f681640eebd465a6acb45a60a927fad36737c5b55158b4ce4a93f073c8c2d3651ea93d4472127e4e18a262ad969b1c85c370b4d72158399c5d31699c4c7ca8c1c960e6a8a527f24fe276b92e6e114355c2d3060a4fd44ea4f6801832beda8aa0349f87355fb24fc9da72f836e2c37209daac0f96397ad1e71cb48c5861cd514a4fe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part594 : Excludes 0x11000420000000000000000000000000000 0xee7ef209594660888421000000000000000 :=
  finishCode 77 0x1c8631444819849faa0d62b0a01c4db8600def317582a4f70e08b4dcc55119f30558ba4f760acf6f733a764c0219f9ec609f62e8f7e5aaad34deeb2f8dee2d3600e4b16d49fe2d35a9c9d9462949d49e725293cb45169aa8da34be409988d066be280c4598ba4f70d5cc4598bac45a30e9433f69c4d6ab1c1549e4ff691b8551623284d6a64ed285aa090d9ec65272e9ac658363df169949e622b06c16a3df8a122d3284c5136d1dc058c94341e9ff547a4ff058c0bb397ae0ca0706057ad1569a0b97b2ce6f3f68704cc481cc37b8f7e733aca4a16b459652e4b1e7c50b44163250b5a6c6ef697cb55741b87317c8c2c9ed732bd65eeae5d31793b51c3354d8be6f7317ab0941bdd8ab41cdcbab3f9ac61c1411d0735a6b68e5d83fcb05231a08d69a73348182f287daa6b4d37b8286737cb4d839947d05a83369bca3d6adad3478e93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part595 : Excludes 0x11000020000000000000000000000000000 0xee76f600404440880001000000000000000 :=
  finishCode 127 0x390cc36840d64174510e5eaa1c94f47c1046e5f962a1af51f97fd42ed392c7ca2b8c3abed69ab1527fcd5b5a6974e57fb12c5a60af9656ee2c80e758ac4ff5a0c7fd4a15438bacae158ad5cbfeb4d9aae7e17fe83fb55e30eb4d49fac5683fb17cbfeca228823969a7092ffa0cd657356d4620e56adca473feb52c1cac62889022093f571746505a6b606be7b5ad3547f1879aa6f6f7b5ad35ccf3d8dab6b628965a6a8fc1cf2d34e87b5cd630739bdd3d2b2b91c2a45073967672facadede08d69cad541cafe3283df725d07f721c1b4fda099724931d47ea17733c1277328b4dab7183948ed5b8c29fb435ee4b169aa87e150b2d5abb8e67a8b59548e0e73f69efe836839dea20b92a0b82da839e5aaad3570594bdad467390d657461d107a8c19d5a6839e5aa950b198b6a0e53f6b52e7b786c417282039d62ab4d9ab609f6a9b99c2bb01846aab556ad827dcc494c8235a694541cac6340ca13fd4041197d6527a8463829c16527b58a1195fa81d5a69ba5ab6b4d9c9e93f3feb288239aa6d575a6ac566abb60ca24fdb44419c5a6b20be18be498ac04176b538c5ea27580c5e7317b4c5253370d2280a413b5287039da8ab530c9cb05580c0bd073cb573f1c615602943073cb1546d97cd6ae3df02fc931073839e4410c5a6af85f3161c7e35ab8b0e6ad8b0e6adad5da46d0ba6dc2f8b57944ee393f19404c03f18b0dc8323ed5f62793e2c9db57db905abe6195abd1876a9b9240ab14041cee6593b608b60b8dbc35ab57 (by decide +kernel)

private theorem part593 : Excludes 0x11000020000000000000000000000000000 0xee76f200404440880001000000000000000 :=
  splitAt 1 118 0xee76f200404440880001000000000000000 part595 part594 (by decide +kernel)

private theorem part591 : Excludes 0x11000020000000000000000000000000000 0xec76f200404440880001000000000000000 :=
  splitAt 1 133 0xec76f200404440880001000000000000000 part593 part592 (by decide +kernel)

private theorem part589 : Excludes 0x11000020000000000000000000000000000 0xec76b200404440880001000000000000000 :=
  splitAt 1 122 0xec76b200404440880001000000000000000 part591 part590 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part598 : Excludes 0x13004000000000000000000000000000000 0xecfebebb826008000000000000000000000 :=
  finishCode 35 0x338d23000d30ef9d0aff5aba20a3987929fd2d2cd33733c4ab1dc812d68e733399c7095118c5f127e5c34de3849bd47beb4d1efca4d515944ce5a735949ab4d5f0ddb2c5ce66b4d80ce3b555169ac62385a98f7eb413739304e3eb178e5a19d0cecb17615c3c90e49305c86a18c069af0b1b8392513698d1853849c0d69a93f6a7c3c95abad4e5279fee526a85d69a93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part600 : Excludes 0x13010000000000000000000000000000000 0xecf6ffba260200000000000000000000000 :=
  finishCode 37 0x390d6370c4035d8c174bdbe2e5a0949da1df2e5caff4159c84e672d5c3beb2b8e5e1d33913c45169a92208d80f2da8b310c98e2d30b5c4c7621a76d8ba6d9944e3b9813aa27526b10a3f949a4c7927ec20f958bb2cbdeae0054a3a09527e83b727c93f6215851fc2d30d28f956c6c058724b547ea3967015f38e416a2c34edd07d527a8a659e9bed28f20d4df62e9927e1df (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part601 : Excludes 0x13000000000000000000000000000000000 0xecf7fe20000000000000000000000000000 :=
  finishCode 139 0xfe3a0e4039dc0681b86d03baa213fc7931c940825d349fb9b60a59eddabee671e4ad34e26d22889c41de51cacbcdee08f62e8f2659f974d27eb81bf67369bdc7926fd9cda6f7597ad3649fab0da358ba1f03c93979ccd5ff2d15ee6e43a0ee7a98c3b94c176b4548110589ad565a686c5226a2b811a7175aa824e38ba4dd54526c91349f93fd28ee539cde93f37da007a9942ea3f59fa4956aa88397650baca569a9255a174720cb29169a8ae8c2a4fd6527eb9a67285daceb4d27fb58ac348da37071335168735360fe727415ad156aa9c288825616c72d625a89549a83b83fc72d59fd1875a19c2e0fed67968a3915ab9ccd67edc1bde5a2a0acdfab298fd66f759fb4be71cc1fce423e569144392c81b671486a1ccf0e9dccad355959c64dfb34cc15eb4d834b59d69b27fda6ad5f969ab4d90371c9d49ab406c616993fd27e7420562e9a894e66a39174c81b51fb40b3f96820b917486ee49fb70b8350e61cb4e6a1df8a4eb179682d670dd82f5cc513a0ae4ff949c3bea118376a3941da7fc9fe4ff8a4ebc39894785aa5095d09fe6f581766f5965b353479693f0efba0e62b00dd6d144595c2d33849cccfc1e4c72f580a51ca12b574a3c9254c1a0725cb2b5199bdd69a9371e4a51d6815dca3f49f824e6b2acac34eb4d9462b2d49fad5d24a725969a1d36a1b85603ba3e58e2681b927ea22cae1699c94fc08ece5d7b7a7a528e0b9596ad5d58054c5b54a393fe690e271fad8964ff16993fe49fb70d0031627f949d68732c3cb3fda0ad47a93f5d03a71ba4796e43815f2d345a61d3 (by decide +kernel)

private theorem part599 : Excludes 0x13000000000000000000000000000000000 0xecf6fe20000000000000000000000000000 :=
  splitAt 1 124 0xecf6fe20000000000000000000000000000 part601 part600 (by decide +kernel)

private theorem part597 : Excludes 0x13000000000000000000000000000000000 0xecf6be20000000000000000000000000000 :=
  splitAt 1 122 0xecf6be20000000000000000000000000000 part599 part598 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part604 : Excludes 0x11480000000000000000000000000000000 0xeeb7f6b9a40000000000000000000000000 :=
  finishCode 59 0x721d07718c06ea887e28fe5a68b4d27eae3082d3651473312d85a1af1f5a00d5b616cd6383ad1857b1b56e58fb4e594621aa728fd657356c3a6b23a0d608d6b1b56d945abb08c4074d4672d354620b9523cb2b518a7de595acae519af0b2b034cd4951fad35ab6e5f808ec2d0c8ad353c6dc338c00335400ecac8e59ca8893f9076a1f904a6cd369a0d650fa0165118404fc9ef169ad354723eb49fcb4d51cb56d69ea1d9462b4d2daacad682a22c8e41a8fadb86713c063ac3658b8b2569a1bd919f394cb6a7bf582b55d276b4d5abcb434c60d7a93569a5d30568fad27e920facb7f35945d283b498ca39 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part606 : Excludes 0x11400800000000000000000000000000000 0xeebfa2b95508a0040000000000000000000 :=
  finishCode 139 0x3d0dc368e8338c23106238c5ed6185d64734c5cbea093df9c9c18e0cd393cd576310c066c711584b9093f94120cb0669c666b1cc491e4ad35c86a115a79865887816870764c1b0fad7861154412ace6381b55e5a6b57d61316c569ad3d1699bd66a29f0d686b2369144611cb092f9ad3d06a3eb631ac5e018eb4d9466b35412ad367b7cb353819cb56973034e16b4d59ccf03000779646591381a4fd69a1d938cb48ec27de584a87ce2283b361a9b31760f7461527ed5b6a6b59e49fa0d64413c2e1445a6bb0aa28fdaa72d1d27ea396b1c61e1e4ad2e59e8b4d27eb82a83c9595ca116b19d0e559ed6d4d6a5b995ede599732ca093d4cd33508b58d445d1b462167b17cd68e2d351fb189ef966ad4f6198fac5a693f591cb396a6ca1f169a7be59a931d47e962e0861b88030bcbc7b5cd5172481fcdeae437b7c3679edef519acf18555165746156aeb11919e11b57fb53dedf34cda9ad23919e2cf511d849fa876523b58e30ea3951fbd465a9bdbda9e2d33a1acf460cb6ab39508ae03a98162a45944691745505a6d4da30e7c36a7ac247d6c33964ed352d1ec72cd5545a0cd65504a915abf1294362a0969acd4b0c7a8ad27e60310d4d5d164f02c5ee71aadea2e499a9eaff875eda348c6032d7449f8b4e2e9a91683aa8e5ed6d6557fca116ada8ad8c5c127eaa179e3969bd52c618cc496a7b9263073d758be0038c2a8fdacac315a6ad062f3bd6e3fac60dab6a2569aa8ad886a6c93f26382c569aa4d5a6c93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part607 : Excludes 0x11400000000000000000000000000000000 0xeebfaaa8000000000000000000000000000 :=
  finishCode 59 0x3d01f3781c86001c6dc288719393b607e0b4c7bf24fe0ef359d61a4c71cdc383411acf0f7d48ea0b8c1cd4d69100169aa86f5a306d63523b535462c17988f0697b9b925a9aa091efc0a988f293f59ab9943627a28093f6a6b0ce591b12d69707b8fb6c5d519c60e729b4c4d92b0d6a89804ba6c5d6e127f0ba5833356cba66f51efa4fd387617051ca0d523f39bd02aa2b174b59e73796055eea2b5f17005ac93f5a68ba569b06ad88b317569a9055f127e3df943ea45174c6167b5a0ad42ec62d89e270b4d1efa8fe5268b4e49fa88d5b923e1c540aa0d527e38d8f6aa118348e7415ed67680fc0e0b5361b1a46d69ad675a1b59e518b59e5a6b58ce6adc066649d9c2d3df2d34332b41 (by decide +kernel)

private theorem part605 : Excludes 0x11400000000000000000000000000000000 0xeebfa2a8000000000000000000000000000 :=
  splitAt 1 119 0xeebfa2a8000000000000000000000000000 part607 part606 (by decide +kernel)

private theorem part603 : Excludes 0x11400000000000000000000000000000000 0xeeb7a2a8000000000000000000000000000 :=
  splitAt 1 127 0xeeb7a2a8000000000000000000000000000 part605 part604 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part610 : Excludes 0x11004002000000000000000000000000000 0xee7fa3b186340c40c802001000000000000 :=
  finishCode 107 0x1b8691dc76138460f840ac8255116841aa40a624fd3fb2d3567e1c55a2a8fe590942d88ad5b1b9ca4747da50d632b4d526cb3f486ad15276b435050b5aac72749d82be09e8f7d69ab554749c0e5aaa4ed8c6a11038fad3649fb56ce323df8a16a234ce617c60d49ac5d6ada0ed27e50b969ab035aac50b385ad0c62888824fd1d32c65a6682b5a6ac66415942e385c50b5c1604f16449d9c2e5aab4cce6b0739832d33594a4c5ab72cfdc76b4560eb53d65b39b56aa82b5f1c770f7d62ea315a1b8ee4fac18d42d870b699c93b2638f7d545aa942e523a50e37ec3df2e9c93b7819c550e32d5b902a71f504cd5b40aa05641a82e6518a93502a8356314444127ed42d3520b2934e32a2b985ea4d37eb56da82dec9056b3a50e30723253c2d678358f7d7067164255cb4d72882bce4f1858fea71f3dfcc1d7299c0c33ab4d3dbc7f558bb53d69ab4193fa70b0e0b1890288ee24fd0005cca3159fad556c2e9c0b91ef824e69b974d6523af949aa6200b62d5630b1efdace0af1efb926729b59d65b3595ed60b972eb5347beb4d94c69bc18f5a68ebd49a3df263cd375a6bb0b3f9412d5b6a6abfda9eb41480363359d6aa3c96a6c2a7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part611 : Excludes 0x11004000000000000000000000000000000 0xee7ea2b3822008000000000000000000000 :=
  finishCode 71 0x1063b8d207cd743907f6e42d355ff149ce4272f486c93f389ce43702db869ab3f2daad35ab651f293b18bc2916284a88b224fcf7f2c553ef1853f59c5e7b7c9f78c2972e621bdad62a93f94474127ebe08c64a1a93cdda71783ac6fd5a6a84e527944ce5f2d35a45d1c81fdac0b41c9543b291569ae41819a359526ac6e0da7094fba91d8bb205419ab424fe5a69c0e7baa935c8671b855102a0cd3909ef075968680b5a1c72d58ac1ad60480e2f06b982f07f62fbdadcb3185a0fec5f835ad3672faa871758acd4b4fbb0bcbce2db6f036341fd19e4c7515a8960d730bdab6b4d83f9c5e596c5e76ada4fcdeae431870938b9c6651f9cb569a93f4f0ce556adac6d682b175129c465a6a4fd746f07f60cf81a6b4d8e26d0356e0e494541a6527527cd37835a0d43b60d3 (by decide +kernel)

private theorem part609 : Excludes 0x11004000000000000000000000000000000 0xee7ea2b1822008000000000000000000000 :=
  splitAt 1 109 0xee7ea2b1822008000000000000000000000 part611 part610 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part615 : Excludes 0x11800402000000000000000000000000000 0xee7ffbe83f073c408c40201000000000000 :=
  finishCode 51 0x5f1545a144285b00b60b4da73356d43ed4d0d8828548f461e0dad670d8a4fe579a8cda9a3c9948ed4d59fa8c5283d09025fc0b76a7b59db8168ca3149d92fe6a6aca478eb556e1887baca454a19805287399d416f656ad974e7aaa8cdcba093518a689e12f660bb12435e682cfe354ace492ef7305bca1f5868b4683ba88b4300c62d160598b4d286a7cb4d6ad8704fdad330d8cb29579ad3662eb535a9b02e567e2d16adac0e5a114622cc5d601a9f0275ab61ad60a8b4da9b278821f6e57992fcc02d5b37babce25f9805ab69296adce6d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part617 : Excludes 0x11001402000000000000000000000000000 0xeeffeb293d66246a8c40a01000000000000 :=
  finishCode 65 0x4818c3f1ac49fa08be1d0b298fb6b5549a8ba4deeb82b82e96b3c4bf1ef82e6733aca4b972d163edac3569ee3b37bad87a0f7cba70d5630eb55479a414ba739b5acb24dd67ea459a627db2faacbd68a88190aa2509253e169f2c0dcdb18737b8eb4beac4b9c767a38ecda739b56526f7969a4bf62ecc155a6a44d6849bae05f598961c1736c09760aac8cdeee3b91e66f732075b2d2c13a7ed5949bdd6aab4f91e69350469bddb8441ac2faaf88ef924a6f71748d568c3aca4dee1b51d0caf35978ba637baca43632ca5706b18c5b1540598f7c53f1f6d1bae6d49bb0ce584c1fd2268e1943e8dd05cb92e579a87d542d141730cd43ef5d988a947581a91d68581a44e3f69806480cb0d736bdb47be7db (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part619 : Excludes 0x11000406000000000000000000000000000 0xeefff3691d0e3542a8c0a0f000000000000 :=
  finishCode 43 0x701102d122692549fcb4d58fabcd88364ce4b5819fb5ab60b969bc6f75aaaa898348935481445aab90659486bc14b172da9ac62c66522974d43e3df04fc587523b185cb720c6f56b3c1b169230f41cd1c2b55470cd49691206316aa93fa30e0b97298f7c97f1fb5c82b29631a97460dc92a09169ac647beb0982832bcc4728e13f6b53d8c570f7f02e5ab62d32e99bd6232ad55ab693f410f41d0cd3958186c5412b550bd968b039ab6a1f519c61e1d0b56cd6700858bf073597ad55463187 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part620 : Excludes 0x11000402000000000000000000000000000 0xeefff32c1d0624408840201000000000000 :=
  finishCode 123 0xc0350b81e8727650e16be398d2358aa0ba548f390c98e50b5a2caa287e721ac6548eb45285a3ee504931d63e2e985d31bde5aac61d61a4c7481002c6c7db8c3ac34a166f75a2ad5563f248e30eb2937ba3ce579a87dcc6917c620a16a1f965e2e949198060ff248d65ec49518a503c993ea60159ccc47300cf75928f0738c38f24beabe1c65cc3a07be50b586c6f7733c14b8c3a91cfb6a22d0c4598ba2cd49f9bde5869f6da5f2d1630ed8308801bde3ed8b4d68ab55479cb0d69cc3ad8c39bdd27f073961a39b6917c571542e9b98d6142cb972915a9e3df586c8e94417037eb946586b90528e5f5720cb2f3dbc2e937bad159459aac66174c1a65c166b244d8be93f300b9b6586b546306a33285a51dab739b4dfa5d359ccb3517497d594771885f168174a51e2e5ad3d8ba93f285ab8d5b928ed4d4a3cb1f3edacbd4667c2b88617d5a9aaf3963f07b95e7356cfb6c5d37ba3a5388c1c095625b174fb72d34dee93f2a1417356d65ebe2c8e5a7a91ca166b393ead67388acd50c6b3cc5d37bad2dab6947551cc49b974e6ada4fd4665d39ab693f585cc5d83da4fdab6aa380982f88ff731ab73db49eea335a126e05f927f183625974e5869b2630e8016667b6853d61ab2f3edcb29479a08e618068c1ad3dab6b0d37ba8cc2df1f6d6aa6f78c3cb292e9ad55edb460ca16b439be619ac258bab459ca6d5b (by decide +kernel)

private theorem part618 : Excludes 0x11000402000000000000000000000000000 0xeefff3281d0624408840201000000000000 :=
  splitAt 1 110 0xeefff3281d0624408840201000000000000 part620 part619 (by decide +kernel)

private theorem part616 : Excludes 0x11000402000000000000000000000000000 0xeeffe3281d0624408840201000000000000 :=
  splitAt 1 120 0xeeffe3281d0624408840201000000000000 part618 part617 (by decide +kernel)

private theorem part614 : Excludes 0x11000402000000000000000000000000000 0xee7fe3281d0624408840201000000000000 :=
  splitAt 1 131 0xee7fe3281d0624408840201000000000000 part616 part615 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part621 : Excludes 0x11000400000000000000000000000000000 0xee7ee22a190220008000000000000000000 :=
  finishCode 95 0x1a46520c201b98e407cd885505a7305419683341ea500cb961272540eb18b478b8eb4f6228b4d27ec15985adc311662e8b4ce4e0c751169f312dcd62d3504c9353dfbd4569eb4d927ee42a881d6310668ff989691b527c6166adb11561a8ff616cb4d7aba4fdeba93f98c49fcb4d284949d1440e947d0472d3c69b1ccddc6103e6e43589e3187055a7ce5515d9c8527e4ff661ebf2ca56aa09d72a8704e420a59ca6b552a0d462ecd5b5a2a88c459ab6a159ca6b396019863170169c60e2faac34382719942ab238c1acfe0e097d68c1a4fce6a9235aaa4de591a4fd81a9138beab2f5aaa80b3f49f97d683bb56e4a3a4fe27faa89e24d526ea338e4272f51188b291d64693f8c1c7356b13c3edcc3383f9c85ab672f591cc5d392b93d27e727504cc2d5a79c9dcc7403e6dc28062f393c81d58f9805cbeb4f5a6d07d49f9c9dac440e4a913969ae659cded35411abee593a0f4df691180fae5f49face58c6a127ef599cdea3b3939cb5946b3cb4f17480c65a7ba0ac39565a5a7b45d272159ac2e93fecb4f (by decide +kernel)

private theorem part613 : Excludes 0x11000400000000000000000000000000000 0xee7ee228190220008000000000000000000 :=
  splitAt 1 109 0xee7ee228190220008000000000000000000 part621 part614 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part623 : Excludes 0x11000040000000000000000000000000000 0xeef6e620809102200008000000000000000 :=
  finishCode 107 0x1b05a19449fb08d237040b62164174a7082b37ecb4d728a8e413683583fc943300ad3563320ae07386be492b70e83b8b3992860e7174ad0e2eea51ce5ab4d527cd315a69cb43e65f3834eb4d6e169ada398b207ccc33039d4520e79abe4ed306ac82e90dccc5b6afcc5ba0fe703174839c137172d89aee398dc07cc1ce9222082b2e9cb013009a4e5a0a05563307f9ee63df300974cd9339742f65d36e1e04414271cb5ab6b2270d441d63faac04e5ab358fea8350dcc82b38fcb015903731aad05683540acb19606ac0414302a5ab6ce20ee396ad049aa9253fac8ef5a1b68ee102db80f9ac8377981ad5b58ca0ad06a6a23be72ac1d5ab6c0d492ad55abe3c9967ed5b606a49526b3514fd6d5f492acfe0d727a60fef5b6adac0565a92541db70b23109c2ca639a8ba547283541dbf8f02c66415839d7c4905d2f6d96aad514158f7e729a3fe300ac35633075924691f6ada0ad057039cf6f38edeba5d340a9c0d632b2f43124b187965218358ca4d4f6f2cb41cec1d5abb68fe3a06f520587ccddb2d34c1ab4f9845b0816c8289e47face5696d5b8bba2e969bc29d0d6b56d69a88201660ead051fed5b5a6ab8b398ba6c1d926ab393f1b480e7586cb39698a4d50565d3591c2e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part625 : Excludes 0x11000002000000000000000000000000000 0xee77e760040404408800001000000000000 :=
  finishCode 157 0x370fe10560c781a4073a88b227082b6f106ac5d91b6d6759ca8ad44a8ff5a5a3fe2c0c94758ca3fcbead5b3d127e8ffa306af75a2b56d02a5d3594a00a399c765d373697d60eeaf78beae574013858c8ba63d4ad160d2825834d0775a2a35da05c194491c2e93e1ca7205472f24d630693772ac58757ba054f6f394dede6fd3dbca2b12da4d528e2e95917c415a0d527f17d528e8ff96328823fe597980565303966901ba93f906a93762ead3e49fbc0e0418ee3f890039d8427168594acfd9451169a4c79ea30738c28b3527ef519a9a5b581521a5169b94dac3f5891e8c3a44dcbae53a0e626d1b1a2076359e60aad55cce4d5477a4954449fc9475aaad3542ea3f4a3cf6b72ead356aab42d558c60170169b94e8c382d5ccf461da9b41d630e011622b99d27ee5da0e71878c3c7db72e9d8542495a725a2cae2dab59c49205f962a5b549acd672dac7ed6b3a20aa285e5a6a495944899ede51fad3566b460deba6c943154596c4c758c9bd561293557fce49584b536836b59e306d021892562128ea21b26839865d826b576ada8fcfc5a6c5873f6b94d1c307371cad5d0471cd187519c61e839b075463398a2200c0356d462a17927e5d35aba7be5a6c60d6af174dab6a3f523c0b95ab9b26052a8fd94839d06b6ad869cdeea1749fa8fd1db41d527ed5b3b144489a4953049fa93476330655eed4f69bad2e83ab0c569ea0957fcaf77329acda6f18560eb104428e5546a7cc4d508c1b5c87460cfdaa1160eb94e7b3b16c1724d5551aa3251d462d659c92a09072c0e59107014c489a4956c26aa18a3f7bac7bf71cac6588ee399ccf2bcdc722a1470acfd69b317e0feb1f0d8aa85a287e519b28b158172943056470a374362c455aba38658a8524fd6ca06c6835a7a40bab29508b13588b240b62d556530f7d1c324d5c82b2957fc3df (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part626 : Excludes 0x11000000000000000000000000000000000 0xee76e662000000000000000000000000000 :=
  finishCode 59 0x348fe104c836f03580e566174550e5e733052cb456b1c1de0d296d5108c2c71727f9bd5ab693740162b2c649feb5558ac4ff510fd7244dac693f5a293fdab69e2bfe691a4949fed578c2c9376b1c60dca6e395a2a20e013564928e5e4f493556ab13fe0c60acc2d49f87cd983f0e66c15985a93f62ecc155b1c7b3db527ea1f16da91e83ead5d43a8e1399cd5b49bb50fe1075dc49ac8235a687cc1cae8288b4d93b62db37da034e2ea42d36058a07507b07f919ee41733acb526b20f45b6947969a83d26aba0e61c2606e8395443dbca4f0cfc1de30a4ff38ba4fd948c2cd335a7b99cfe6b4d174b307c1cbd69f4614feb185969ee391e480c646bc0ab6ada48d44eb39 (by decide +kernel)

private theorem part624 : Excludes 0x11000000000000000000000000000000000 0xee76e660000000000000000000000000000 :=
  splitAt 1 109 0xee76e660000000000000000000000000000 part626 part625 (by decide +kernel)

private theorem part622 : Excludes 0x11000000000000000000000000000000000 0xee76e620000000000000000000000000000 :=
  splitAt 1 114 0xee76e620000000000000000000000000000 part624 part623 (by decide +kernel)

private theorem part612 : Excludes 0x11000000000000000000000000000000000 0xee76e220000000000000000000000000000 :=
  splitAt 1 118 0xee76e220000000000000000000000000000 part622 part613 (by decide +kernel)

private theorem part608 : Excludes 0x11000000000000000000000000000000000 0xee76a220000000000000000000000000000 :=
  splitAt 1 122 0xee76a220000000000000000000000000000 part612 part609 (by decide +kernel)

private theorem part602 : Excludes 0x11000000000000000000000000000000000 0xee36a220000000000000000000000000000 :=
  splitAt 1 130 0xee36a220000000000000000000000000000 part608 part603 (by decide +kernel)

private theorem part596 : Excludes 0x11000000000000000000000000000000000 0xec36a220000000000000000000000000000 :=
  splitAt 1 133 0xec36a220000000000000000000000000000 part602 part597 (by decide +kernel)

private theorem part588 : Excludes 0x11000000000000000000000000000000000 0xec36a200000000000000000000000000000 :=
  splitAt 1 113 0xec36a200000000000000000000000000000 part596 part589 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part630 : Excludes 0x30005000000000000000000000000000000 0xcfffa6a19e600aa00000000000000000000 :=
  finishCode 107 0x771bc691680f3b80be1c34e525b19686d4f518acada9f1b858c5b0fff203cfc6a7acfe7b696ed6aef699cce8110d8cf6d5239bc56c6316570f7cffea479406b2b98c4816c49fa58e827866a7c6145b6b4d7b4a0bded31bfc5b63df5a6c83151cacae30a5e77b68b6d3c4c169a4f590226b596569823268c296f56566ff4088afe35aacacb874169ab6258a399a6ee5d417935683ab11d6571857b6979c5b66b59002e4b27acb578c28f7d2c1ebc2db407c1d672ba0c60e24f55b0dfe9e189ab18551fc616400b18b824fd6c4b18bf354582f07f505bda435e83f0d9cf69418a87e519a045ed3190f6982fab1359fa488a2d0e8358ec5ed23d37b4cb4d968a26162ebda5683f18c44127eb6320b84616618a7be0dab41066a0bd0620bb85b680f5a6979e7aea80d69a6b59022b4d5b16af0f4c19a5e750fca47066ac0c806c6400ac5438a2db066c940335ed33175682b4d519ac5ded33115b46a169b41b5c7280f2f38b6c19a82f969b0aed01e83f641b46f16c066a0fe501a48b159aa28cd4fbad5d19b16253ee8015d0fa702ecd7e92019e50fabfded30755aba0065b1ed31fbd40683f408c9fd948e0cd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part632 : Excludes 0x30001100000000000000000000000000000 0xcfffe4ba187860222200000000000000000 :=
  finishCode 67 0xee348ea2d81e7550e56c3b85b65f3835c12311fa4fd66a7294a126f317584a93f27ab8e650fa4fd543959e8ac17cda57240569a729606b14e0fb34cc7bf39b4e522db063c1d6466831c0620b559a9ca5545616c4a3b902db72bc92541e8f75cab067d61ac2383ec9257b48f756563df961a4f52f9b303dd89eab39142c9e949f93d5102e16c5a69d0602d2e49fa895472bc2b0947949a3dd489ad3e058b5962caad3d49a099591a8c68c3b094012089063820d47e93f0dec93f63167306ac1171b8d0465f3751a85512816da08d8a724d56af185926ab1549fb608424fce4406b12e8c3abfc992b4b9eb6aff969f06b894ac4b57facd4bd724fda8521901ee8b6e691ac34b3718583ead3c16ea2b922201769ec1f4b36c82cd62f9831cbe71b8e30e273a0ff0754ed9295eee5f3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part634 : Excludes 0x30003000000000000000000000000000000 0xcffec9e079e001e00000000000000000000 :=
  finishCode 101 0x378e03b0b42287376c0e36dc30b64199b8527e0cf42127e8cd9626c2d62eb9be589c1f5545a6ad0e1eead5e0fb0f75203f6cc155a68614bd293f067cb63589636080203d68b0f7d462813819e83f57bc7ef16ea8c47bef699cdaf6d595833ce3a71d9ac6e143f291d6aa0cf16ea508139022d5f50eacad6aeda204e58ab57d6ab2c5528409ca1d7b2bda65a2a04d43ed8250b22e04f56b0bbf3db497ef6959fa04507eac2c66518ad14dcb06be5239b9565eb432883f927e0c95a69b0a09948aafd8fe2a471efb58f758192b2f57b810507e3df407ad56518b58b824082f25fcf692f5acfd94168c5eb58ca04da6f2c0dcde3732f5a045cdf0f7d6325eb737cc1b816eb4d519b60b82d8ba20bd07eb2f9ed24f52f593d67b4ad07e2e893f3fecb57835b57d07ad3d2f5b55e6e1784e0dc331747ba8cb9022a1f16ec6e1451acf3dad6522bb579cb55838bda5a6a81112dc5eb728c1bdcaea1f408a03e523a4fd65728cda9e3df5e168751b449fb9b608fad0583683d40693d56af2d3548a3dd9ed3306401a2bd504ac5c9eaa315a011f27dc5bab5749fad3565b1fbe0de2dd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part636 : Excludes 0x30001004000000000000000000000000000 0xcffee3a0396001a60802008000000000000 :=
  finishCode 81 0xde3b8da3b01e75b0e3b1cddb032102723360e29252f5aca567eb40ec65a29c6d27e8a09e62f59fc47a6a31a0d2a475a293d65a6b607e2d14bff41bd27f071902705fdc05b1ac38eb59e3728f7cbd680f364c5eb837a4fd6aabc35460b9a4d562a93738dacfd68480cd675a6a4066b3bda562ac62d880f945683f5a1acf2d54de293f58aca1f263d06b594b60b62c0ba28ad47ef579c72f7540eabfc1663d3691caff4068b6d67282f5712c590bd61af9646a0315dad3d88b23355460cc3d3501a0cd69b3d7658fbdd58bea1d50182cd8c44127e98251e69ba045a5728c5eea925409b4de83aad5daca3d35510270ec524ab154420fb0ec569af759ed6d2357faa857d9ed2d5f5a6ad5cbfed4b9866d57579acd569ab62f0d80b6d0271bcd27e81397449fc7e35a6cf6969ac1bd145e102694353e519b55d462b15928eb4da0dad2341ec9f5589ad3568a93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part639 : Excludes 0x30001002000040000000000000000000000 0xcffee1e43c6802e18c01809186020200400 :=
  finishCode 43 0x178701584d16449bae0860b75a6f3d95cceb4149ab976733ad567b49fbcb7ed651ef8f7e594823526a943e08628c60db2d5548e923441acf2d15ed2601751edb3da47bf16f5c96ca2cbe16eacbe300ad05a6309e4b4ab4505cb565246ee358c63e03df41fca453f7b17e72e9c74e8591ca2b5059c749aaa3f9416f65617c3875239c75416e4b9222a4d5418c5b05bb3da507ea453f7b95e400ca1f1efc7ef71da82d62b1fbcc022dd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part640 : Excludes 0x30001002000000000000000000000000000 0xcffee1e41c6040618400801000000000000 :=
  finishCode 137 0x3b0e03b8de348a62f070d394af83dd7b6cb3f491a8c565681196325bd7b6c6014d1785b194395b50b4d4a0f81eeb986591b99dc8ed3360dc02159a82dd82ef6d7abc0b960d87154562a5466ce613d5bda5416e478c2c1fda662dd3a182b31751fef57927e1c54a1201eeabce09cb0cd69a4bf62ebda5a672d355e70b7527eb4d0e2ad366c1d43f15849fc6165a6b4a566a3dd5a6cc5f1eeca1158fb4de83fa08563ed659ed23dd5a6a98c6360b8203d5e70b74dfe8115f169a6ff926b1855abc6163f6ad361dec6014009bfd0230f7569abc270a60f7503f24fd6529239aba1c543169a93f5f14672d5d26a62461683aa3fded31fb56033dadc8e2cb5abb52d043311cc0293f5a6970ac2d352849fc6e31ee9805bc407c81f51ca4fe058cc1941fbd5c9aaa39430fff244501ea259eaf185371a4fc7baac250c62f0a80f756c5228f7e519a0fda9f41adca20138c2ac55022b57519a3767b6a82c7bebe1f82dd62ec5eb5ab9ead27ef678fdae5d300cc156259b847bb378c62985eb58ad07172bc6150226f1407b176152a04630a6e193fb185378b1167b4a4fda6727d4172e6740fa4fcbd6e02205c2f8b4d55182b1fc522293f49bb1167bab065042913476ce570e0a4fdf05c101eac20fdacb0f7cbd2b298c2c1293d58965416afd49fa4fe5978f7d27f0f7dd46c15c49fb285eb470172d4d8b7ed4d9632c15152c3df49ab576372a444172b617ad5405babde72ec1cc736c5d946738e435ab2300d802cd4c8c2d07f57ea0fd6aa4c7803ed4b7ba9664fbb3595646e4159a9b967b6abf4ffeb55737c83f37297ae (by decide +kernel)

private theorem part638 : Excludes 0x30001002000000000000000000000000000 0xcffee1e41c6000618400801000000000000 :=
  splitAt 1 90 0xcffee1e41c6000618400801000000000000 part640 part639 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part641 : Excludes 0x30001000000000000000000000000000000 0xcffee1a6186000200000000000000000000 :=
  finishCode 11 0x2e06258c5eca188d3445230b359c2da93f5a68f4d066b0b83cef6949fa0f505b3da568693f69127f1ff5ed21e7492c4f5 (by decide +kernel)

private theorem part637 : Excludes 0x30001000000000000000000000000000000 0xcffee1a4186000200000000000000000000 :=
  splitAt 1 109 0xcffee1a4186000200000000000000000000 part641 part638 (by decide +kernel)

private theorem part635 : Excludes 0x30001000000000000000000000000000000 0xcffee1a0186000200000000000000000000 :=
  splitAt 1 110 0xcffee1a0186000200000000000000000000 part637 part636 (by decide +kernel)

private theorem part633 : Excludes 0x30001000000000000000000000000000000 0xcffec1a0186000200000000000000000000 :=
  splitAt 1 121 0xcffec1a0186000200000000000000000000 part635 part634 (by decide +kernel)

private theorem part631 : Excludes 0x30001000000000000000000000000000000 0xcffec0a0186000200000000000000000000 :=
  splitAt 1 116 0xcffec0a0186000200000000000000000000 part633 part632 (by decide +kernel)

private theorem part629 : Excludes 0x30001000000000000000000000000000000 0xcffe80a0186000200000000000000000000 :=
  splitAt 1 122 0xcffe80a0186000200000000000000000000 part631 part630 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part644 : Excludes 0x10025000000000000000000000000000000 0xef7dace19232cea00000000000000000000 :=
  finishCode 63 0x3a87e318d224fd7c6707bf073c9af20c5602d42e0c47a0ea0cf4a1a02e83aad360eb258e83207ff055c94341fa85e515d185275bd5e418a50d69adc330b2208d218883b741016e459cc280126acb155a1b98523f2d0d4574615eda7f5835ad0521a943735c1c541d8ed640aad0649d979d62b348b22c66474c1d438a82b059a0d5b46a182b317523e1cf067ac4e418873e0eb250d6aac83a0831907e1c583aca4d474b9649d62db50bcc8330e8348713399a8e67aea0560ea0c9512cf5d6913c405a0ed28728fc1366d789aaf650d4cf5d515a8e5cb30f7c122b4d59149aa2b1efcb3f41dacfe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part646 : Excludes 0x10005200000000000000000000000000000 0xef7fa4f512608ae69000000000000000000 :=
  finishCode 81 0x771a46f1505e0e1e7371d3c3df736acbc5b6a1f6420c4fb832549b39ae0e22bf82a2c49735a7de4c190394b58c641fe6a6c1dd49a80f063b68bc032459f20ee0d3280decb24360fed4f41dca3962dcafd505a895906d168b20554162db063ac0afd903ed6751f9ebe5aab57569b2cfd416a035e11854102a8354a1cb2950fa0fcbcf2bf567eb0393e41dac4d67e2db6b1eef304d6aa721505c0b5597ba0ba2d3637b9bcce26a81f86405a334b3a83f83fc81f139ad3456741d4b3ad5126a9bcd01688238f6d928680f16da8e547ec836881f9287185735a8945b71859a72d53512a03c7bf461569a943512a7893b94563df7bacd63384a8ad5849182f002449a72140aa0fd48a08f048ad0b22f00976b106aa3198260c91a7ce4f5a6c1ae623ad3578263c2b540a9c8546280f907eb4d411833061498ea3369ac02541aa8c498ed2208c628cc1172d3456a08b9a726e3982e72541f93561bcb1254726fb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part648 : Excludes 0x10005002000000000000000000000000000 0xefbfa7a116700ae0c402801000000000000 :=
  finishCode 67 0xc62d07e2d893f691c05416039ba0fe596a91d44aa4d33169aa45940680f625ca3383aa50e40fad34e527ff901ef5d940680f6a17c05cc8115a1ad5d69b250d0231bc5a45e1dc4e148f2335ed272940aa0d56c701a9f3da5056b293949cdd01f2c6605ca41565282b83aca2571cb9bd02a8357016c3916039bad3588f30cd49b0739cde6c5625a93649da07d277204569af699a9e80f4829bc5286b61ffe407acae5a6a4eda66d675b1ac64110407a7083f9eda835526ae0f6d60cc94350bc8e1621ad56594b99c7bea2b8ffea03919a4c77b4a935dc6b2cf6b26aad5da9e93b7b293567b485b56aede370b0247e7ba8704dfe83549dab04c78e528357b2c90d7b2cd53515ac067b4c1d5286b3f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part649 : Excludes 0x10005000000000000000000000000000000 0xef3fa6a312200aa00000000000000000000 :=
  finishCode 115 0xd22e9060fadbc4403e6b41c8c42d3560066c2db508935582aa39631ac3f1b849f830e2f38334bd738e672a8aec19b0759ed307360aa4fc19b1b8ded33054dc693f72102320c53fa7334fec81526aa895885a0cf75508a05419aa4d7216833ddce4af758bd6c158bcea1f066b58b41c4d1849fbda6148a05565f2d3567eb3f900227f41fbda56826acb4d624c8cd7b4b78d6312660abda4bce931067876d9860ac93f40ab114e5324fd627312565ee47486a4fd23f063b8c607cdd049faf07a20fe7b4a0ad6aab22d882b835c90d62fa04641fcf693f7d07f4089f7e4a1972daa2d65415af8f695e162b233543ea474a054f1675002b4358ac099379a0053ee2db9b85e16449fd0717b4833506a83b671ac16d83367b482f5cdb3da569a81596c4b160400a0bd47341cdcde0995a6cc2f2d0cb570a7a0860e306d5a6b8e588e0cd829e8015a69bb56c58185f1becbce2db37182f131cbcea45907e93f581105a6c3b150fc11f467bda4e2ee4f9a9693f6f1ac067c1db2f3cf6949fad35a8597ca0b5238b6d27f20adbc4403e67a320a3f520e2e125905e5e7167b4d662f979d44a80f5a0c5e75a6b58a39905e71751cc2a169cb9b589293f37dad3608384c7ff38bb4d6417a4fe (by decide +kernel)

private theorem part647 : Excludes 0x10005000000000000000000000000000000 0xef3fa6a112200aa00000000000000000000 :=
  splitAt 1 109 0xef3fa6a112200aa00000000000000000000 part649 part648 (by decide +kernel)

private theorem part645 : Excludes 0x10005000000000000000000000000000000 0xef3fa4a112200aa00000000000000000000 :=
  splitAt 1 117 0xef3fa4a112200aa00000000000000000000 part647 part646 (by decide +kernel)

private theorem part643 : Excludes 0x10005000000000000000000000000000000 0xef3da4a112200aa00000000000000000000 :=
  splitAt 1 125 0xef3da4a112200aa00000000000000000000 part645 part644 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part652 : Excludes 0x10001600000000000000000000000000000 0xef7fc96c1162802ef000000000000000000 :=
  finishCode 71 0xe63c8da2a8d6188d7c382c1f66a7bd94126c231749ccda6b2c8c9ea60d6b2c04147998358aa4f5241ce6b38293d4c1a62f6b1705305d2b2398be60149da50d1011ccd4d042ad356470eb498e917590e8501785a7b53658fa8c5ac67db47f9b960f6f75963ed4f3edb54637bb54cfdeb099cce3df7b6a03cfb666354e4079bdcdcb34bcfbab4d3d169a863dd568ad4f8dca9430bfa50e71dcf757b2ac8bc3584f55f1a9b1b9546280f5a7a91c5d283f8116e390c0a415646b4f047cd51372ad34112e3d8fff06f0d3a0fc112d82e1062d563f8a0fd69b34cc12293b1efcb55372c943045a8086001627aad3d69a0830429f0a817d41131f860f7233400e009591b4cc9eb0ba569aca1c85c1e8b4d591a6739b49eaafd0d1ab0b558deee57818af757369a4e597c1ec2eae5d0d1868e69122701fd6062b55978314e4313d497ae578e4a6e5135b9b526e4f5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part654 : Excludes 0x10003200000000000000000000000000000 0xef7fcc6450e081f59000000000000000000 :=
  finishCode 61 0x2d0bc3483fd650e6ee5989aa1bb2f48ba5cc054c3a1155a08568aa1f155cb457aece6f14297a49eae82e0929907e2e96f1c072ad0712e5ace41166ff5a69cdcfff3dd437e4d5378823e044ce0230de2f071d6c1582a0fab41de30ee5146693d49aaa09597ad15b458fce3d5a583149ead31966af6d41fb98d628c64078f7cfe33dde27ab57deeaaa1b8a31737cb4b50f96f672b82dc5d2a0980c6e3960c8ba507f31245d2bc2c8b813d583327d5276943174b596518a8266aba8c56aa2e98de706328d80ba54630f7d6aa80f466c1231ef9fbd43ea31504d07f27aad5507e7ff651cd72d545a2c318bd2b558317c3eacb03728ad1473ea1f174bdae3ff9355c7b287c9aa2d1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part655 : Excludes 0x10001200000000000000000000000000000 0xef7de464106080249000000000000000000 :=
  finishCode 159 0xcc350bc2c83f5202988e317a0d50766238c5ee8338da188e317a98ee2f82a3901e7ef48086bc7be2e93d1bc479a4a549b276d66b071a30a4d50c9a08b841d6584a07d01694369230b461d47280f405bdb660cc0595a693550c5c169b28e58be3af300b786e9969ed390439b8d69b203cfdea2595ee601174c7dd405ad35dc7d1bc581705005d280ba30e71d300b9b6526b02e736ac8d472e6f8262b09372a7ddeda2e98c3d06b2ce9c8569a2e9640c027139eda733526cb4d407c7135a69805046f1016ce2800c77d16464619ee671d486cb3551fc8cd38ea8e6159ac3569e86260ce01fcf41d4a405cc3461d2531878de709ae2d3a434d926f3480aa89f78566c0d629a981759a46191a30f07f641bc51cc71d591aa8942d0c2326ad1855a6805626ac61cde741fe26aad3630ed65605cc3b154935630ea4d6d19c7313c317af05f356094b13d5aca83b4a094b13d4e3b280a62cd475f393c78e80b96729018e3ad239ae246a02d20283b4edc935480b48ac298835727cb5572ccb42cd60599bc456a6fb9a8a4f59eaac554888ba4df6bc3965cd6f7589d607959ca0d4e2f0ba4e4283f7714c174a85e474bd9549af75394ad55cc7244549ab095a6b20601624ca4d62fad3d69b3d758bee53741cc670c4718bdac5c0c1b0ba5b058144b39ad49ac43a0fa8ef395b08dcd738f6263a76cc1ab4d39b9c75a47016838eb28737581ce6b2fac1dc0964bd5a6a509e9a0fe911132b9b4ff65f57acc2391afa445cda005922200d57ea80c9ead575a2b287fb81561bb174ab0a02985f583dc0a983fad15ac741fdabf029568a7fb83dc4d53fdb284f57abc923025a3bc5d2a3f242c4777abb9bcfc25f56919c38ea989138dae9291efa44e5a6a4ee36b868d69a5f3949a285 (by decide +kernel)

private theorem part653 : Excludes 0x10001200000000000000000000000000000 0xef7dc464106080249000000000000000000 :=
  splitAt 1 121 0xef7dc464106080249000000000000000000 part655 part654 (by decide +kernel)

private theorem part651 : Excludes 0x10001200000000000000000000000000000 0xef7dc064106080249000000000000000000 :=
  splitAt 1 118 0xef7dc064106080249000000000000000000 part653 part652 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part658 : Excludes 0x10021010000000000000000000000000000 0xef7dcfe0b0b094a02420200000000000000 :=
  finishCode 65 0x1b8791646d19c4f198317985ce131feded283b382c4eb317c93f415a50e275a0ad27f23cd25280f26aa02d056da3389e23366199c14c5e617620c4718bd684a127e815986691f384b0ce399873e83a92f5b048125b2d552871c16612b14cc1abc3603f5300c7ff5aa9bde3f7b92d02a6f78bd6ca1e89e2b89294a18f7e2f5c185620bda7b1fbd82f0758b4eb39370b4f527f305e0c417c91f05cacfd07e942d5417306b91d2d4d57bcaff230bda4bd7250d05e3f55a2c3f549fc18f2368ca2181cf418c717835c693515931d0632d14e6693f48101e83fa0eab5583acb458172b41417a0fd5c399ad160e3ad56 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part660 : Excludes 0x10003010000000000000000000000000000 0xef7fcb6078a011e0a060200000000000000 :=
  finishCode 137 0x1f8d8240bc24fd00560f42f5cc4d5a2ad55285f1546b148b07585a2b197b493d417a5eb9632f6905ec2e97b4a82507f12453ea4f5597a03e6099354bd6f69451282f5bd7626a860548a70204e039c1cc0d7073943eafd26aae0c835163e89fc55ff0ba60e32bf46de4d5523ae8ae0ba626ab4ccbd6d62f8c42502e905fc5e94a18b462d9c1fdc77395cb6683f417c91f13cc7f1232a47d6c4317c417b8ee72b92a56522e97b5d07f9652b298fc22e992528114a1945d1786e09eaa33982e3df174a50dac40ec9f558c97ad07ed3391c2f5d40e8ba61ef97ad07f24c4ffb291c9eaae2d85eb471541e3bdd660a8aad43eb199a56f570e3c3df465c8f31feb4ad252b6418f75943f071494b0bd07ec1788cf30b425ef5d6258ff5252942e09e24c61ef93d5286d63100b78bd65e91749b8b2384f27cf626abfcde2d4d4fbb17657ba47d5fed4d48fcc4b905a9f72f5a8cdb42f5ac8cc2a8f6b961a39b62eb95c16ea1f71ece6b6259f55646b4b354c6e157bc46511cb9460e692950fabde174b70ca278bc24a5287060ff5ac171d0713dfa0bd89341bdaaef6905bcf696248b8e8379bc507e35585970751748ff55eeb297b4a47dac1feaa883f5a2c2ab522c1fe60ac7f15e1545f08c4a143e9e291d64470c5b3595b4cc9ea0b991c2d4d9ed29e418ca41c505eb298176c4d2e5abf6408aca5ed23b38556b299ed22bb982aa337b4a91d646d1ed3204d69e4f5626c8e1591ad560e7357d5fa121408c1c594408cc5b3fec83f4faa7de69ea0460e283f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part661 : Excludes 0x10001010000000000000000000000000000 0xef3feb20302010202020200000000000000 :=
  finishCode 99 0xda3b0ca3301f3205b1881b5a0bd706b925a2ab6a6b985abf27bdabf28e4bd734d549a3eb721980f9906dac004cd5d7b6a4fd88a6f17b49face664d59ed259d49fb0558bab15927ede3181f32f5c93f378cb3f8c2e93f201c1f36e1d85e16840db909c105520b2054bd6a2562ea916505891d5eea17174a705eb49f91fe12da07c5d2f5d7baa3ce17481944b692980e691f58cb8ec5d241548bc415631b02f5ae088250ca18060ff356583293f3f8a50decb0555cba8f33f8af82e99a7f071927f07f9ab27db174a4fdcdb1f6c4be93f5f18bb399d4162e93d07370525cceb3537ba415cdb41cd892e41651ac4a05d2c459edae674a1b116494a005612c175a78e663edb1142f6601733d07b0dabb052328bc2d8b2285d4570759856c5b6a9d18549fc1d505ea1f591283edb16d6573d95856b296a79b5669f8dbd856b290a2d06b6229fc5a9ab297b4a7f66b3a934fd70758de2a1f6229fb4fd6bc1f8c62d08a24fd5ef41d4bd617b58fca09408a0fc362a1f731ad8c1995fa7ff41fa8fd63323841725eb3f8a98a3f836217f835aca4363250be353683aacad1c2a33523ad88cf95eeb1941fb06547ec159ed2d6753098f20be0eab298c2c14d4feb134def0758c3c7f1579a7dd3fad6751f85ee (by decide +kernel)

private theorem part659 : Excludes 0x10001010000000000000000000000000000 0xef3fcb20302010202020200000000000000 :=
  splitAt 1 121 0xef3fcb20302010202020200000000000000 part661 part660 (by decide +kernel)

private theorem part657 : Excludes 0x10001010000000000000000000000000000 0xef3dcb20302010202020200000000000000 :=
  splitAt 1 125 0xef3dcb20302010202020200000000000000 part659 part658 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part664 : Excludes 0x10401000800000000000000000000000000 0xef3fc27c132491240920080040000000000 :=
  finishCode 85 0x1684f0e479169ad22c8c40fad04b38e4c4673741ac93f30b9cde2f9c623691885c0e6e6e59cda0a1494a87ded2943737ca477b4a286c38ee386bd74d531871d9ad3ded24e162ebda61d986ae7b4b05527e4e19cde929771d8531a4550e6ef227be04cb48d27e4e11f5985d141b7cc47466a87d48eb4f386a87e49fb9163598ec43e670d49fae04bd859ea3f0dea8fe158b101f349fc7f5526a0d6731545c0c2ec15988e2b74a1a91e2708adcdcb250cc5e93f616c2b1270a4fd7056147318bd27e1bd7adca1159ca93563e0b11f5cc2d41da8fda441ac72b39bbc8b398c5ea3f71cc5e9791cc40dca3f0f9bb0c42ce61f5a0ed472a4d238c119466c61c7d69ef3dba0ecff6aa353672aa3341162b12f58fac1131384fc29a3b0aa1c75cc4f1ca471d98af514735cd67835ac8cf868cd7bad0758c386adc7b2c24b628d77bab57d703412866b39892e6f494a87e6a8cd4d372a78e62d2e494a335cdec4962fa50e30f2c24fc22b16afbda683a93553bae39 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part665 : Excludes 0x10001000800000000000000000000000000 0xef7ec270112400240900080040000000000 :=
  finishCode 145 0x3c8da3b0d432841d4f0826c6203569a9138df64f5231c6fb51f8b6c3e74182618fe291349287cd8c45127ec5d8b3a4f56a19bfc91b358cb3af6d4ee8b6d82a59d85b670d83e641320db48ac07cc806b2f9a4ab552efa4fd226b23a30f07b62297ac9eb1ff527e1f3761b856082abe20d527f248d3d291351cc8155a185b3dd586693f1cbca3f3f893556c263cc19501ad3549a71d3f13049fa51e69b9fc55c560bd691393bab3f7b2d0774eea776594d071492ad06c2d352232c6582ac4567148f2c64bd6b4549ba44cfdb0104c02b0350fa4fcfc4515c430bd6b2f810ef7562fc1de71cb8e671dac6548e17f541eeab197b2c6e18c3bda4fe2e6d985f07b492cf652faac65686f1d8621a46e0e6ed80ff5f049fad367ada87c48f232da8ac5b26a9edce364f594666f1737b608a24fdca730b543eafd38db05671cc5eb4fab95569a71b3a09eae3d87fa9dd49fb8e503a9dd9c730711fea4fdb04811449fa3165a6b0ac9eab45386828e7b4ad149ea6df57eb0551427aa33615ea87d632b4d3868af650f97ae466b94569a803386b68b22284f515bca1f5aab9bd82b287deea93f838ac660e331156327fd5a6b0565a2a4fd69ab4d927ede310b63b0941c75646d1cc27aad164fa97a5c7290d597c5e971cac267baad55ed26e17b29f86462b95521ac4996129dd158b9bd144a1545f14632d15c72a474face5360c9b9565e6e59cdf1fc660c9b95632942788013d5277277568af6592769dd7b4b707f19a6ae51736ad14bd26dfa30e8137b6a4a64ee9f85cde943984f5551b07b6b9ae519a00cfe2b454fac803401a6f187a0eeb55486c4610129fc589ab2998b6b556c1205a7ce3d7b4b16d652b552d16330add43f075856ee4f86be5eb5a5b8f6837bda49aa4f5 (by decide +kernel)

private theorem part663 : Excludes 0x10001000800000000000000000000000000 0xef3ec270112400240900080040000000000 :=
  splitAt 1 130 0xef3ec270112400240900080040000000000 part665 part664 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part667 : Excludes 0x10021000040000000000000000000000000 0xeffccefa90388528210a004200008000000 :=
  finishCode 55 0x3c8ce2a8dc17cd65b2404c2eb1789d61cf5aba49594631680e79b5e317a40527eb4d7407be90198be8e19202dc3a0b4d819e62f526c9ef5a6a4a5a47131d5fec6244d043317d27eaff9eea0cf60cb50522c0b2d400ce3d4f7a4fd22eb4d49db10b4d8c1a80191de4c73f8c01f4109835d0410ce596afa79cc1ac5391dea4d0b1b9ac9d6f8328b42a893f5a6a4c61ef828deeb13547bece2b8ba0f7e0df24c5c7625b466935438e8c317e4a1b55d19741c5262c42504d55abc4eb6afd187247b93e5aba0fe30e9439d049f93ae418ad549d7028e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part668 : Excludes 0x10001000040000000000000000000000000 0xef3eca3a90280120010a000200008000000 :=
  finishCode 115 0x1063c8d207ce08760beb2c5d62a5eb49f9c3481641b489c937201ae0ba0ba5681f5c1a669a9c3527eb4d2e5c9ef83fc5cb727b9660d2d5749f931c98f24fc9c23eb72127ec0d947e4e15a693d5abb2d5dcda2e95a1b062127ed22d88cb90667df4a1a87d69a3df39b9c8ec2d35cdb41a54127fd38d833e0d3128d632f752f5ad0e3fe93d569b13d505f13d53ee3df62169af7385d270d39ba00e4fb9c35cc5e128591b827aae0aa0b4419e90d254cf658c3ad05ed717adc9ee6d90060cf7b6a8cc4672ca4fde2a75a0b20b83708315505d291f4a18546254a335cd6a475ab91867279c76466c1bda9ab5758bd06f519bdde729a04d62e2e94b16c670fde3598952e5937089e4bd60cf7bacb1550fb70f75803236f0679b845d24d59cb2f73408b38d82bfe06793551811bc48f71cabfce3a81395fe127174b96611ebdd562a71d58bcf7371da04d3ce2e94a17027ab9b62e5ad149522e9254cb454d0bc4b0b96b55a0fe3a7370abf64f39f85cd72d551962e98c3b16deeb16f5a4791d8731b8386c3eb067876c836b60fad27f17fd6822db5abce539846c5539b8fac8363d383b64037616c6211839ba5071d7bbcb2d27aad5d30737cb1526a96f60e7123dc7292926aba0ca033e168b0c67b997a49eb1b8a1f9466d82d166a6c1fc19e93f727cb4115e97ace1a4f596ae4a3925281349fa87d262d424fd68317cd6ae5f3969a4e1 (by decide +kernel)

private theorem part666 : Excludes 0x10001000000000000000000000000000000 0xef3cc230902000200000000000000000000 :=
  splitAt 4753 125 0xef3cca3a90280120010a000200008000000 part668 part667 (by decide +kernel)

private theorem part662 : Excludes 0x10001000000000000000000000000000000 0xef3cc230102000200000000000000000000 :=
  splitAt 1 107 0xef3cc230102000200000000000000000000 part666 part663 (by decide +kernel)

private theorem part656 : Excludes 0x10001000000000000000000000000000000 0xef3cc220102000200000000000000000000 :=
  splitAt 1 112 0xef3cc220102000200000000000000000000 part662 part657 (by decide +kernel)

private theorem part650 : Excludes 0x10001000000000000000000000000000000 0xef3cc020102000200000000000000000000 :=
  splitAt 1 117 0xef3cc020102000200000000000000000000 part656 part651 (by decide +kernel)

private theorem part642 : Excludes 0x10001000000000000000000000000000000 0xef3c8020102000200000000000000000000 :=
  splitAt 1 122 0xef3c8020102000200000000000000000000 part650 part643 (by decide +kernel)

private theorem part628 : Excludes 0x10001000000000000000000000000000000 0xcf3c8020102000200000000000000000000 :=
  splitAt 1 137 0xcf3c8020102000200000000000000000000 part642 part629 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part673 : Excludes 0x10002200100040000000000000000000000 0xcfff9c6c40e0899110a88247022004c0020 :=
  finishCode 111 0xd63a0c8398d8220ce20c52c4e101e922c84d561ccd5b5a7bdae5aab95661cb16dab635593c6c3972cacbc7beb554913c4e1ab62bd6a8c4d56a8c9ff466c9036049355ab6c5b9ab692196aa80f62d9c058732d5501e83f6712c2307be562c87ef2f1982e5b8f6727b595c9f2f0a2251636fb56dc7a9e39a6ec1369ab16d63f359dc7ae513e1ca3394da66af79ab6e3d7278025ca6941f0f739a6a70183786fd3c6d3357bd06f4f196f62e58005ab6e594a286fce04d20ef123c37e5cb58f9c051472cc0735a5b9bdacb38f526706fd184d154380a702bd0df802683a9ed524ee599c7b356d8b6aa2f0d5b857a23ba0e21bf736ad2e0b4bdddaaecc06fcb9634d924ed3758f8d36735a486728b8f5abec5b2e5a8854348d5b601c7b1355eea94558fcb353f0cc3959a9d0b55a0d63a7727b15dcb24d5220e02e5cf7759abdd60dd8ac66139c04376ce39be2df9c049aac5b9672701671cc5107bed3782369316ad86fe737935524ec098e024d56adb16e60eb56ce02921650e01efa50d66b27ae0d6e556b2d06b61ccd57691cc380a50f579ca6945486a47d98118cd6558fad3dabf08c53fee4f72ac4d5580e858fc15969993560df315e30741c5ca6b35 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part675 : Excludes 0x10004200100040000000000000000000000 0xef6fb4bd42608cc31228c887022008c0020 :=
  finishCode 57 0x691dc38150510e02842389212f5063202d056d5d9812e6d4818f7dab6cc1e083b91e29276adc83b5aab56e6613c7240d3c71fc5ab69c247d2624cb924ed5d9062e51661645112072d1504a3df6ada0ed3c412c93169fd183589935567e91f61ac00b459206815498bdd625ea8849f9eaed5b48fc2db510e4418c9ff3fd976d01683f9056bc230d519c965e74a1b16d86ac81e02db466cd3726ab14584f460e628ad549aac8309e698b99d8ae83f83fc9e3736b144ffe92293641fa02d0764c79c7a945481af09e3135c972414bce943728cf6b37d935523ee4b9acec51 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part677 : Excludes 0x10800200100040000000000000000000000 0xef65fc6c89608c8330298027023000c0020 :=
  finishCode 41 0x400ba278743a06e9202c3913809c15a451037f27fd0169439287330e8069e83a8e9c77e72172ea02e2f9cc556ad9fec11ec23590e44e0ff6cc1355ca31b2d8a6d650dfc29b9876c53904ad35202a0ad3866123f11bc80a4d549cb0ee71db14da9b30ed9859144405c82b2dec943586b0e5a6eda308e481982d8aa91f9817356d8aa60b380a3c5646ad9015a5312ddeeeb453fd8b6e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part679 : Excludes 0x10100200100040000000000000000000000 0xcfedf52e606480b110a8a107022200c0020 :=
  finishCode 41 0x112330ac2c86e20ad267207deae3df41ab56c37f3d5d06ad61b8aa356c80b2ca4bb62db250cd57202c2db202c81b9ab6c6360961fee594ad1584e3df6b1506ad8b6e418a3c6237b57deae46f98127f116dcd45a0f6b450128b6cf6ed5b32138730dce960b6d653309d28a7f1906238b966a9ff6adace5cda083695b98c806fe6ada0fc5b6c0b9ab61bf0ddcd5b4f13ff06edcda19f6959c06 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part680 : Excludes 0x10000200100040000000000000000000000 0xcff5f42c0060808110288007022000c0020 :=
  finishCode 159 0x7d1fc8901debc34892288da1fed076aa21860b36fcd677bbb16d696c5b9062e5d59190167bbb48deea725512c4856d15467128b308c37ec5326a8b6d94412b99e12c85d4532d5f62db9767379356584bddc80a4d59aceb4b24290155c2029987bf96967ff613a455ab720c528aa119ab69e998462db6b2b154be64056c1103a14449149b18390169039cda59b591a0c47032ce5846831508c60e405a8fdac740cc1a9a0fd8473dd528b308cdcf06fdaae80b613cc397abb0eda9e5f39612b4b6c1103a14449149a64308e487b59506330eda623ab6adc1bf418c4d5305b0ed422c23906260b51fb4ae62a982cc172f0d43b84054a124498a6882b14dcc3b626b4de41acb4b7abb56d3fe81b93fef779076e8320a820c641fac0b2384a6a2b4819a9dccef779a46c5362bd07f6ada06daaf27fd036c83a0ba08c613dc1d424eb4f3f7b54501690d41f9c4da6f2cd506270193ff075591b51501680b926312330e82e8c82b0bc1c4da45116ab2935ab683b5949ccd384a2c81516d9f856524d5476d187589b1551ae83f59f9cce48fa07d07f2887179036d5b16dc3df691385e1185620eb399d67ed5b41aa0554440dcd5b1efcafd4a1a7a49aa1bf96aa3df605c9330dfd18746ba43d3c384b4fe606a3cc7be60b035cd3f0aeb0f58c5e1b043167f30e5056b5540fa8966adacfd07e4c7a0ef07b164ac8d02af6b8236931605a4a507e92996ab07f415b48bc28892993d6d5b41aa78b4f9a563df55104ac3992729035a59b9d87324e5206b4b6a20eb2cd523e6e7494849e699c1dd28ac274ffac8d873247d69ee6356e1ef93566adb98c8303661db97501e83f4f19c5a2ca4d4f48f7cc16d2b8db32935846b5571d9c86a0f906ba0ea36362aa5156aad454a2cc39490cb5593d2b29 (by decide +kernel)

private theorem part678 : Excludes 0x10000200100040000000000000000000000 0xcfe5f42c0060808110288007022000c0020 :=
  splitAt 1 128 0xcfe5f42c0060808110288007022000c0020 part680 part679 (by decide +kernel)

private theorem part676 : Excludes 0x10000200100040000000000000000000000 0xcf65f42c0060808110288007022000c0020 :=
  splitAt 1 131 0xcf65f42c0060808110288007022000c0020 part678 part677 (by decide +kernel)

private theorem part674 : Excludes 0x10000200100040000000000000000000000 0xcf65b42c0060808110288007022000c0020 :=
  splitAt 1 122 0xcf65b42c0060808110288007022000c0020 part676 part675 (by decide +kernel)

private theorem part672 : Excludes 0x10000200100040000000000000000000000 0xcf65942c0060808110288007022000c0020 :=
  splitAt 1 121 0xcf65942c0060808110288007022000c0020 part674 part673 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part682 : Excludes 0x10000200120000000000000000000000000 0xcf65d00f8064c2001060900410249000000 :=
  finishCode 73 0x448fa3b0f2350e4398405077cd5b16d9454b7b01a4e0a7dd6b183bdab7003200ef5605b6c219abec25737b14d02ad51418c1756afb56e7319c3fdc2db41acd5f6afcd63721dc6415028aa85673697c41de921509cd5b39083bdac7243c1ded5b92065f17acd07b418b59406e4d56ad83bd063356c7faf22c8501077a5163edb9bd49eb4f729c94569169f1455043330ac2a03f54e034b2d3cbe29455d02a330e60fe0a5594a48565334bd47709758168153efa8872591dae5d0cda06dab6c398462e5d1ef982dcc16dcd5b305a8a66adbc9003300ef541902f8b98c399402f6f41fa3ae500a3ae73149f1ffd49f41de0fed5f61ecd5b2f9b30ac17c5abf1ffd67e3dd72ec1336ad9b9debad3d945281f6adb985f1907e821500ca15 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part684 : Excludes 0x10000210100000000000000000000000000 0xef65d80da270d02010a4a02420200000000 :=
  finishCode 45 0x1e471164761983fdb90bc350d5b9a563f5202a70a276b1c7f5399a8ad66ab298a2ad5b64138373ca4d515a4cca2ab1f41fd06b3998efca169219a5e933077b56e28083bc1df2a87db077c50149cc0ef721983c17c4e0e1250b9ab29033ffcd638c1c3f52f8b58e49883bd287314d23e515077cfa06de4f1b085ac67ff62b83bdab6515661386adcc216a49c24be2c579ab690f50bb524e12d5b944aa17661382f2c5151fea4cd263278ca163fd6adc515 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part687 : Excludes 0x30000200100000000100000000000000000 0xcfedd0be26e1c400b86a800400300880001 :=
  finishCode 43 0x1e4801f46401deae2a8a813de0eb278d6125f3699a51584e5f1515cd676959b9cc16c23451741cbcd3169182b528aa2b9a9eb351eeb4c61ee8f7627b8f76499aa0782185f15a2cc233ffa43d05ef63907ef51305b155d05a2c7ff487a0fd697309d28a8605fe5a5a89d03e3df942ea2961eb60d6320fa207d65314555041fc90f7b1a84e586a93d382f8cb45499969e5a2a43d67eb29928ab3f28a8b6e530a2a8fd965283f4a2cb4f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part688 : Excludes 0x10000200100000000100000000000000000 0xef6590bc0660c4009022800400300880001 :=
  finishCode 121 0xe43b0d43d0ee0fd5f4831a47f190077af8939963e50b28aa703739272945697c3ab7b7a70f6ba30e35b49c8f7d266be24c63dba78c4a730860ee9318c3a30c398e02917601243142d28a931877e93196967ef077b48d639266903405942d66b05ee306c51482b59d3c4618170d5542ec39835a3cce269295d18170efdedec394f59c4da9f41a544e66285e515b09da44920eb314cf9a80b373c5a72eca4cd84717c5872d21c87dd966a6e72f8a51501686353e38ba33e6a793ddea2a2b49c9b9e6289bedd0641f4551406d09eec219a92c4d37db58e699cc21628a485ac6a8348c02f05f14a2a98c4d2cdc01741fb93d6aad678a2a48d71ec83f613a80c98e8cf9acf075405b8e506a515399cc4d71cb59cbe281f9aceb5561fcd3357eacfd01e2db3829cccbe32515ac6d23e83ab8e0283b4a2945528b202d06ac4d9286a03641f477128b2d560ee903077942ca2aa8210d678e5e8fd4a29cbe611a0ec9eec539eb2d67412ba0ba2a072f39986fe417bd4567f3d7e6979b5dcd67177b7acfd44613ce6b7a8a0d434b3d45a6a9c20ee00ea055272945474c82b49086fda45f14c28594542b703bd1fa90d47ec9d91a4ac7c1def23000ef69ac71361eb52522ad498c16c0245e57ba4e528ab4f9acf03be00761fc6401ded63905650116db4a64f5c1d58565e76b1b4850190568ed92620ef987b2ca5056501 (by decide +kernel)

private theorem part686 : Excludes 0x10000200100000000100000000000000000 0xcf6590bc0660c4009022800400300880001 :=
  splitAt 1 137 0xcf6590bc0660c4009022800400300880001 part688 part687 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part690 : Excludes 0x10000200100000000000200000000000000 0xcf75911c0760c8001130804400200001400 :=
  finishCode 137 0x112390fa3d0d43b0ee0ff54c077b60d63949b06f285a0c5181dfcb0d48ba8eca2b289d262b35697b4be526942d04286368a21d06df38bad2e51cac266a4b60903967306f418a8449ef0915206b4b5a7ca116b1ca114939fc5042f23580ef510e26d67967ec216ad9ccd6ab34cd87a9459a5e5155aaaf8b1f9042d657bbb59ca2aa3b9ab6b4f7716ab03bca165153a144512c725526a805f19646a115a5ac26508935415f3d74e66a3f7919c5513c6a4b58c5b720ee0fe4f7389b485159626b3f16da0545b7300d21e10779826d4b626ad549aa83b2f8a40d2c631c7b0514e42f59613945503e5159472f7538bc51551fc7337ae97c503f3535dc5f0dcb1455043289638ba00434a51590428316a4ae89c1c4d445e0e66d67967f07f2f88fd60e3251563e5f1541a6b3d4415ec5316db4bd28aa119ac62451faacfc7eb308e0ead3550b9ccda5ebc2bde83aa89501e83f59f8fd50c55105ed2f9252f6b4edb14d66b24c6697a50cbe2f63731dc7a18c077a98ce20c5abb06dd3dea176b1ad3e40fa93d427289ce8461472c4d98b6c539ab6b4b697ac26629b525ac69316710570b25ac6c5b98c5413fb316c592825408a0c59c611c2c9305b58cb7b2c8c9eea11966b20d41defa3b8be03bd69f1c0415a5154e1ab72c8d22aa3b4a2ad3d063360a22e8a3f51cacd648a8a6d28a0ad7abb09e58497c47baa82805f16a7c3dd5a5ac261eeb4cd28a3dd815a0af95e6b353059e0982a05f18fc283f461453293dc832cfd03f06ba0ea2db612a7f5a6681f58fd07759782b56aa81f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part692 : Excludes 0x30000200100000080000000000000000000 0xcfedd01f02e1c5005960a40420600618100 :=
  finishCode 41 0x79180661c84e1d82f8a31003e8ba03bd4232cd47ba90f835ca111eeaf0933834aa4d1eeace66a7a8fd66a82f4998f76077cc27508b8ed05e9331ee9456499a58d2398c83a070198aaf6f417a43d07e515a30f278d846d5b14da43dcaf029d2420ef838c0ef2dfce554189c041de0ef81df41d659fa0fcf560ef4e198730f028a9f4657ba045acab3987ba7dd373cb354998f74fbb1b94342a1528aa0c6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part693 : Excludes 0x10000200100000080000000000000000000 0xef6d901c0260c4001120a40420600408100 :=
  finishCode 153 0x390f4350ec330f20fd60c77138077a10b399c76b35417a4ccbe2743a0a113ffc6e7612c61d84683f7b9d187605b15e6b19b9d47e7034bcf9b202d84e83f1419c5e405b09db0580f051fa845d0405c92737dc1d6835c5f1a0d6f6b8df6d6559aa708412363eea4cca2a5f14a17c14dcc5528aa43650ab155ac7202ca2b34bda4590a2a9c35946c7251569ee3b9cdab0d697c1d683eb9b5ed67dd6c142b20c5a5f2c7da6ea156b2b98a1590620ef28abc8d5b98b60ef72ccd5b50ab48e62f8f7589520ef6a7a434a1651579150077a4ce69ab52d272d65922a93995ee94559caa00ef4e1ac72d15cae94572bcb459a92d6582be05d6b383bdd8831f45101debc28967aea0d5076033a0eac0d2daa515cda80b5a5ca11541385d1ab7293437e9394a2ba082f9872a4d613acfd697308549ac8248641fb4be40acb3f5e138415b9ae5a7942cfeab3550acd2f038cb4b6a686fca1680b6b3cb3f61383bd98601383c1a4541016903698cc5748fb024bb292761acb3f26aaf0f2130a81fd542317c49ab28460ead3f923ef5d26a97c45b67f18be33c8bc1f092205544801076f75a306d4951f945613ebdd5a6714549aa283a306a3f16db8edac6a22c8d5b9076d499c7a81f6ad945640fae8ee251447f3d74b96e6f7369455cdb0525016f57418c80b71d9456631a471dba096352507f248584ea158a2a70150bc50b16dca176a4b48d5b90562db9446920d65158e0280b69ac80f594c70128ab59dacf247ca2aee30f662aa0aca020ef711a45a5ca1141d92165089bb5aca6e76b1cc3d (by decide +kernel)

private theorem part691 : Excludes 0x10000200100000000000000000000000000 0xcf65901c0260c0001120a00400200000000 :=
  splitAt 5542 137 0xcf6d901c0260c4001120a40420600408100 part693 part692 (by decide +kernel)

private theorem part689 : Excludes 0x10000200100000000000000000000000000 0xcf65901c0260c0001120800400200000000 :=
  splitAt 1 57 0xcf65901c0260c0001120800400200000000 part691 part690 (by decide +kernel)

private theorem part685 : Excludes 0x10000200100000000000000000000000000 0xcf65901c0260c0001020800400200000000 :=
  splitAt 1 68 0xcf65901c0260c0001020800400200000000 part689 part686 (by decide +kernel)

private theorem part683 : Excludes 0x10000200100000000000000000000000000 0xcf65900c0260c0001020800400200000000 :=
  splitAt 1 112 0xcf65900c0260c0001020800400200000000 part685 part684 (by decide +kernel)

private theorem part681 : Excludes 0x10000200100000000000000000000000000 0xcf65900c0060c0001020800400200000000 :=
  splitAt 1 101 0xcf65900c0060c0001020800400200000000 part683 part682 (by decide +kernel)

private theorem part671 : Excludes 0x10000200100000000000000000000000000 0xcf65900c006080001020800400200000000 :=
  splitAt 1 90 0xcf65900c006080001020800400200000000 part681 part672 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part696 : Excludes 0x10004a00000000000000000000000000000 0xedefb595164889675000000000000000000 :=
  finishCode 103 0x1c8601684212c2f8ae81c992669455c1608c1c7a9613a8acdced4f38ba8e4392c6460e501931d69ac275049b9d07ea0982520c9371c1be736a8949eec8358d42f00c95a6cc1d71e872589ab4d9c7a717371c831561785a6c48d504a0ee3061a940aaa8c479406e6d2d0cc311e8acc65a6ac8bc06fe41abdddab6b1b40d8ae65a6ac6d016257944ab4d58db48ac308c820edb4598c7175a3832541328c502b4615ab6a2558db20b8350ba07254131c85413353662ba0fd406c2789ef07f984ea2558da91d100e4cb4d615cc5b58da8cc19280f9062a25384b48bc37896320d6318a33907e81b9a6a0c9504a8c541328c5266b1b944a81b499a8cd906b1063307506a0c92bdce6d5a9a8250767f1242c2756adac6d036b3d40acc822078353671dc60d0167f1400b9b6263b8f528aa4d6f0b6f240dc7a0c94a2a02e83fb53d6a6a4d928aa4d8df6c8348d62e8821c95833032541307b582a91d66200d9406c47410832501f1c5d6041da02d49b39bc9eef6b6b3c60e71c9bee698ce6759e9ffd636c8298b428e50626e3969a4679076b0200409b2d347a2a3f51c92865a6a8fe51cacc4572b3d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part698 : Excludes 0x10000a40000000000000000000000000000 0xede7f49e944982057348000000000000000 :=
  finishCode 87 0x10a400fe3a0c22b062f650c1ab42f0b4d62ac83b371b56cf4405cc55405c6e76afca11405a0958a6d2b9abec25371b14d04ad81e017d969ae675a9ac15002722c2614cb51569ab3190626e314396f5672b4b584cd575a6ad2e27b9835344f128f41fd69a4f703f9f082589ee07d6c1a62947508ca4d59cc2694edb48c82d0a213dd78598c2af41dac164f4b09549ab09405b09626ab48cbe6b4d61cb4c661da0ecbe680b960b3154076b530bca445c46710c69128e2c99076923926f20c54222c941dace67ad8e94fea175402a80c83608e20c503f177547ed5b903ec2362a9775a925dda307358d64e195698b52dab7207d876831371b08b2288d239826b3527bbddd036d5b41db3893790629471648b6deef39b504ab23418ad2cdc6d5b81862cf49b93de611906718c16ab889e030c10f1b9cb6ec47373c4f794732a037d8fcab4d40093de5a9ac81bf8572e6d3f7c61cdce80b41d9d0e399caa947263a89498f2c6d637236569a4f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part700 : Excludes 0x10000a00400000000000000000000000000 0xcff5f4f414ca80055222014008000000000 :=
  finishCode 125 0x6d2246b190741604f0e4ace1cbd54430c46b059696b23960ad352f8a0fe317a18b31960a831584a07d696a824566918f45812b53a30ae41591a7dd22aaf7928ec0d3f7acd4c1afe2e0d218bd017206d6732c15acae6b9a96721591988cfeb2d4d02b075390b48ae198ac1e0c22455272d379202d651599f7d04a4f78dd2a2308aa20d569f1f7c37ee6b9ace80b4a29f7d6632d3d456a4d584ac164a3a014fbeb3511fcb3d5a6a8fda6ab314a2b9ae5a993dd846945551467136522307f96969db36da01561341fdc9e5f161cacf5672882b09a28fe30ca44d26ed2291e504a055ab6835740c5f248e0d6d5b5829c2549b1f3d1d6923611ab6d20d4e582a515eeeb4d40da4465a6a935406a4d969ade2106198b2ea2b40da91d28a8eb6115447fca4749ab0f475f41d4c5ed3991fea478c19f7d2232c15636e82e0a818bc793357c6faa4d5989fc528ac0d9cd6915582acc5cd7237d64662359aca03412a4559c690c5eae1e02a1a0feb4d7ad9f7c37e91549cb09e4a29f7c37ea4d84d2d657bab8e5406a47059a3ae611b154be6b39501503c02b32d3d8ae9390d4cb4b41fa515672f778c1aa4d5a6b4d5646a8348c27948ac219a6e9f79416c551d5b59dbc6c1905814454144aa4d407c945523a0fda9f298922804d527bca11591980630b34cd22b30655ee945508a51e5a5a84550420be330e55ee7f1487a3ad70410c83f37bc80f2e8cb4f47fca474a39ffdab6a25641585a7a48e5a69fbcc02c5f9ab709b64809bdc2ea17d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part701 : Excludes 0x10000a00000000000000000000000000000 0xcde5f4d4544880055000000000000000000 :=
  finishCode 159 0x200741780f2c490a3383f5202988e317c6164ed9c24e4ab4d71158263c3e541da51d46692340aaa896208a0b948e2a598be4f73f7a8c59c5a6c1bf50eb11cb7b1c94f7ad23736a875413317e27b9fbce4a0b7851413317d2220b76ad9804c5eb43205d18d8e4f71ee82d55450eca31488b17e504a205d198be91185aa1ab49aa8ccb6f0a338b82bde27b9b8d69ac4730098bd5ef13dd69a623441696b4d8c02c5584d21a38c3a02ce12da278ba1e01b3922a70959075f305dc72e6f0dfb8e6737b12582ee398fded2360bb17ce2ee559cde7091c4cc495a6821d785a1586907bac24484f7818e3f5412a0d590671b005ab5364a3a40c18ea339aa29476a6b596371b4ce30f24e528aa1193b6a0949a8fd567323bd2263f5541f469080aaa022e348ad349ee939519a8ae2cbad3566a9394a297c62f9ac2569ed2461e59aa4e569a9453d4c911467c614be2a2b5a6ad3c2fb2d2d69aa2b16d901528f205417a835202b78c82e8661e0a02455272aa2c8e0df93dd6470acc4eb0d860fe007467ac2630ad31063a8fd8c672144a2831d66b06fd69e3af80fb2c25eba9f74a2ad3d4572ce49ef06fd646945632146c19c5a12060c7691cd512f8a33e373b03566ad235a7c6e758497ce59aad3d540639ea6835892cb3ed6527bb57e11fb59584b359cdc6b09727b9ad67318792729455a1b0550be28213dd017460d6a6e4fa306d675a6b55e411a6313dc102d5f987639f6a8a4872208d4569ac07f6aba02dca334c60fed5162ac8df6a88ace83fc28960fd480a662d35266b05a0f6b391d79ebd84ed4f803ab3937387566adad3568561b01f2ba0c2075560b461cbe283b4a2d1873ffc60e504ac1492a94541aa82e51993dd9058dca1d5a68b549ee1d55412c504ca31504ca1d83ecb0556154505ca3349aa51d90412c1d540acaa02dcfff355c35e5b750ea826 (by decide +kernel)

private theorem part699 : Excludes 0x10000a00000000000000000000000000000 0xcde5f4d4144880055000000000000000000 :=
  splitAt 1 106 0xcde5f4d4144880055000000000000000000 part701 part700 (by decide +kernel)

private theorem part697 : Excludes 0x10000a00000000000000000000000000000 0xcde5f494144880055000000000000000000 :=
  splitAt 1 114 0xcde5f494144880055000000000000000000 part699 part698 (by decide +kernel)

private theorem part695 : Excludes 0x10000a00000000000000000000000000000 0xcde5b494144880055000000000000000000 :=
  splitAt 1 122 0xcde5b494144880055000000000000000000 part697 part696 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part704 : Excludes 0x10024200000000000000000000000000000 0xef7dbcd79252d8521000000000000000000 :=
  finishCode 55 0x661504e1084b0be2733926694556142339b49aab4d1e88324e66b4d9586417041dcd5b51d9ccc3521bd723c46f5a6a0ed49e72f4c107700fc14ed5b4748f7d67ab312d3cd5b159a4e58c2f3ad35a7f24ed84ea2b9585f1703979ccda6b12c5ace82f15fb0e60dfb09d3db202c192705588ad4da850bce57064a80584e1c94f6c5e75a6a85d904f17c5618c397bd7651ca0d4fea3df51db9ae402acc5a85a6acc61efa4145b6d67a0d23df5a9c7135a6ba0d43db650bad4c3920c97b6c7a9728a03c57e733691457069a0ead5b727a4554731b9e6b1a84457eb4d4c169ae82983d172cc80f6a7cb27513a8fe7359feda9eb27044c1be417a85dcb23df (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part706 : Excludes 0x10120200000000000000000000000000000 0xcfe5fc66f4d490901000000000000000000 :=
  finishCode 63 0x1122b0a20fd4a86c1ab6e82bee59fad143aa8358bb7314d02a82b741056481967ab550eaa0d664016f20558762c916d8755544f126ab3f924ac0d2edb1565a2ce0338ca320d4585920b716d831d7c4407be5db95f64eb488ad35ab68624466a29b9d21e5db487c9338bb690f5a6aa01d536bc139733b56d21e9333ffcd5357ec81b6adac8c9d6c2320d5b40da8a651e98107f9a5eafd3ffa3658727ff8be25db6adcc83281d55a7ca4f69593ac15a0c750aca4f551382b19c373a18e612de488ad34bb6947969b135cbe2263969ad5b0cf93ad21f356c7ba93356126b0b155fb176dab61b35412730f7568a5f136bad36 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part708 : Excludes 0x10020201000000000000000000000000000 0xeff5fcc692d09018300c040200000000000 :=
  finishCode 49 0x7f1d06717030cc62f5f0c4707b87bed391fa9cbce27320ba208621c14533356d61a6fb5a79fed0372d3dab6c3d8c1a4eb6ad9c9569f1ea53fe4eb30693ae4a19835683b10772d2dab63df275a8ed49ec234d65a6c61d6965f348ba8f5252cc28f528b2015672d235a5c61e731b48d0c6f0be69298f6f07b1dfb55d66a6e98f52e3d6918e7d04ad57238cb271efa4ed585d1045a0e26bc293e1faacd651ea5154769439646825399ca291faa30b428ee59aa93d1df202d252825156c4c32eea3bd286a016324c4e4a93b4ffc725059c80b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part710 : Excludes 0x10020210000000000000000000000000000 0xef75fc47b0d090b01484200000000000000 :=
  finishCode 51 0xcc3a0be250c21834e12717613cb2f405c61d21e6231fac9e398c82e07334b1a57203d05ed5b942e0bf3178f7e6ad988cc47311c7be39f874e1b36ad9ccdab7188cc32c21399ad0782f05f15907ea6e79452d2b960b202d673202c7eaac20c61b9b024ff6713629a05503734adc45617826ace6b402a9356968df51d8fd506ac237880b64184f0f7d47ee6b0dfacd5aaf06fd6a7461c0e24d5969ea4d49ccb4f515a93603881cd58741ab728a5aae6192fab78ca302e8c3a7fc7bed5b52693ae6ada93e373b4fc0e6d5b3fdb56e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part711 : Excludes 0x10020200000000000000000000000000000 0xcf75fc57905090101000000000000000000 :=
  finishCode 125 0x1d06a1cc0f2ae0ce28f61efb56cc3262f6adc60d5e0c46b4d89d6d5b3fdca17526b08ce0a9054a170491cd5b51eb4f49d65f56adc947275a51e5a6ac4d49e3d16adb20b8220940f45fc670beaaf79402b53488b56dcda3df317b56e586abde735a89542e5d14809c95ab73f8a81c94c1a62f417cd354a2ac36540e4a7337a8c9114a2abde231a85d44eac339062406311a4d561b309dcd69ff98128df477ad34e12e6b26ac9eb275b56d672e63789358c323df593cb3f928eb4330a81e0d217c574591ca1548aad35272c646161eea0ec18ec09481a93d87b2d3d3db0774f169e3f5a30a38761cc1dd69b0779422b271fab20bc2b0d42d3e06386f47ea7028ed69706a569f07b900a4d541da4d5457206c9d6b3559cb93e613831d672b35613c1291348064f6b0774898f7d26b1874a2b785e120ca2c8cf4063acd68c3b98d456a3f2d3d069405b56d663185942b0777b6acd45922db4f122b28e54568fb5a7831d49e9039a859ad1855a597cdab63dd1faacc6134b98e30a913412a40d47680b87eaa4f651bc5a6a8fe526a44e6b3a7b587a93b527a496491103a15426aaf0fe24de275b14e0ee2db48fc5bd412a0ed017314d49ac0946fa4158167a993c5c10c4a1b48e275b0f528e5f3493cb533d4a0ed8468df2f9cb3598a6825481b18d2328c82a03bf4ff831e0ff13347bec5783bc3df1efc8f398464eb41d97ce5a78b2616da4a53c5e150526c7b783b8b6d3d6d5b695a0d49d6d441a683bb56d3fe2db479a7a659a8f7e0ee9ff5a7c8e97b2a4153d3293437eb35 (by decide +kernel)

private theorem part709 : Excludes 0x10020200000000000000000000000000000 0xcf75fc47905090101000000000000000000 :=
  splitAt 1 112 0xcf75fc47905090101000000000000000000 part711 part710 (by decide +kernel)

private theorem part707 : Excludes 0x10020200000000000000000000000000000 0xcf75fc46905090101000000000000000000 :=
  splitAt 1 108 0xcf75fc46905090101000000000000000000 part709 part708 (by decide +kernel)

private theorem part705 : Excludes 0x10020200000000000000000000000000000 0xcf65fc46905090101000000000000000000 :=
  splitAt 1 128 0xcf65fc46905090101000000000000000000 part707 part706 (by decide +kernel)

private theorem part703 : Excludes 0x10020200000000000000000000000000000 0xcf65bc46905090101000000000000000000 :=
  splitAt 1 122 0xcf65bc46905090101000000000000000000 part705 part704 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part713 : Excludes 0x10000280000000000000000000000000000 0xcd67d925104488001540000000000000000 :=
  finishCode 149 0x214791fc831c0077bb11230870f202990ac2bf59c40aad55cdb3d6da4692557bcd3da30ee57394b57c96f2c8d036ca2c8b4d1bfcb23626b56e57bb58e0fb356deee9d94029b9d806f03aa981c75abf2444e529159ab67b70ddb57dabf1bcc596a82bd6731c61cfc2f6b4a393fd67e71d1d5cd5b59faa0e42c8da2704ff56128a2cb9eeed5b3f0a51d61b41fd69ef773729f6e490bdddab6b2f9a7e94747ea4852430315ab69454c11b3030d28ed5b03fac8b39965e19f061ce53597b38c23d666ad931c172afd5615ef031528eb0d818ab4d59ccd5b24ea45549f1b4500ad5b40d9015d86a13c2029d04ff4120fb069c156c53621ad34e0a4bd88f2d6383eb56d69ab4d98562d1605a98e02a0b458e1e7372fac72961d82a60ddb0f68c297d5606e5725eb534ff6d2368a62a0b3f466cd5b735b024e6671d27fb9ae589b30d399426d5b399a0d5817460d4267fb730b98dab6a15059cb3f6ada0d5b461ecb4d62a9ccdab717d5506d1645c09fed339caeb2f055a514bea9459a6a0c5928ae5d965eb4d47ea485843d1006d16aac2398aae679aba5878c28a7da9a1bb9652c2306282e648a8314fbb000d476d5d586a80569ad4348405611c0061ca111749ca5cc31bc5016d5b412a8f6626b54d28eb4d378c2731459355696ac17c45d28359aa69474f5cd5b641985f07fa1e5597c7d547e9355a66d5b16893fc17b18389fe7d526ab484ff70168b1c3ce6e2d18bd2b45729c5e96afcb450f28ff49fee43b0e03001e56f1a44e09fe9213c05d3289524e4b79abe2e998730f458ae8eb5a6bd8e581ad3567e4ff27fcb4d5918b702f4be283527fae85f17bac0bf384a4cc92f05a502a0bf631806d128a921818a921818b13fcba3395569a2dd0e0b202dd174ad16491b9556269471e8a48e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part716 : Excludes 0x10004240000000000000000000000000000 0xedefbc9dd2418a4a1a48000000000000000 :=
  finishCode 73 0x851a45414c387b08c81cdd8c1efc83f061ac0bc0f454572cfe0d3285d82f0afe0d33dd4dce882006280ad360d30abdac6501400c501395a98962d03df6d0e52b4d60ecd6560cb56dc8ad495a9b916526c81f061ad0d659832d5b722b5256a6501060ad35a4b1edd622b53061a20b279422501061ad35ac7030ca02c21e8ce245d2768c994222a516dad36526b389436305b6a4f9cda81f400c6ff400cb11441a93302547aa395a6a88d439ebab27464b1347bec5750bb99e671906114c16aa18e8220c61c8c4740fb9be736b4be7b6830cb972d4c55a7a98ddb0692dba85d03e3dfa0d30304f6e50151ccb312dbac9ca0288140457f3495a7ea3d5a6ac6e6aeb16d8a2c60f7e3739fee598ad4d90501002a3d969aa4f588c82f588cb53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part717 : Excludes 0x10000240000000000000000000000000000 0xcde7f88c904182001248000000000000000 :=
  finishCode 135 0x214801c4077ba0d20ba5c04d190387af0c2278ac0b25427250d86ac43591a0ed47724a5a97030d3c586cc5b527b076586cb3169cc7295312839bb09683aa0c501682b4a1a0ae405c3d150bbd9d22eb0d5e161b202deca83b378cb39405abee47dac35672c2298a81ca53c38eb18d57604cd2383f830c46341fd662e6fa0ea835405cb356ab9284187069598ac36280acc662dabed69e501387b088318de2729641acb35260faf65387a8f4a02e6397c50164280a70ac3a0f5f963e83541dad2c5968358fb71c75a56c3562182dd672b4b630757356c4c21bf05fa4d67379c75ab6f75903eafd2edacfc5b6ec318e02d07298e6e2db8186cc207dab7206c907356e40d9c74de2b29905e3df70184460e52f73859281538e8b6e4e15859100ae61969ea2783e86b5646f6b8b5a1ad723caf76a9ac8d07f3db5c8aa2783eb56d61ad4961160b2ce5076a27969ee2400e83202dd174b500b78a022d5530e01efa0fdcab39bc31b41ad69ad2b2dbb99e515a48ca02821491ca62b8963083df5e1887248c37e2d5061d06928086fcdcf276cb96a1761aa68bc2c4616a8acd28e1bf8566501837eb41b9e4f6a8f45aa9352808b5649ab491202aca0223b8186b3d515cf57491cb43185016009072d347be0b90dfcf73928f07b8d6681f4ffb4ad0762d56c0a02e83189628880f417ad362e8abec55aa3f16acd2550ac2d5512c2ad4008b56156cb111399bb47be2d5 (by decide +kernel)

private theorem part715 : Excludes 0x10000240000000000000000000000000000 0xcde7b88c904182001248000000000000000 :=
  splitAt 1 122 0xcde7b88c904182001248000000000000000 part717 part716 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part720 : Excludes 0x10004202000000000000000000000000000 0xef6f99f516508842d012101000000000000 :=
  finishCode 71 0x378ec348a8308b81c3ce56822c081f9842c516b3aca548eb55498b05e62fac088317e6998f45273359d82ed3360bcc5f613cc5759fb4ccf0523c50b610a91e69c942d545a1a93142daa6b0418a224ee3db931d456a4d6b0fff2d547bed6793ef0696a7c93b834d0775a28afd03f460dace93b25e9ca56aaa83187e298c39628a20d4f905e4d58c2c8eb4178f7da9f06a4be2c82e05f1a0fec218c2872504282f152c9d9737b4bd01e9e11efb53e30b250e0eea113ffa3ad385a1840e497c630b1b55286c5ba0ff07f91d691f6a7a4ed857131d42ec8354e407b53d23f41fdeeaa2b3ffb48b42484fb73d5d03ec1749dad54a16b4d5812632cfda9e4bd8f6e5f19a9ed675a1505c0a165f15aacd5b83aa765a667f1410b4ce4faad55a9ab4d722d077405ad54a16b4d5c100341fd21a81f5aaa4c5acb291da9ab55 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part721 : Excludes 0x10000202000000000000000000000000000 0xcd67d9e4164080409010101000000000000 :=
  finishCode 145 0x40106428f236040517483bdeeb0795ac72514fba929761c05c03cab40ba4f531cad69a737285962e3738f7d462bc3483fd2314629e287ce3b003dab63df6adc90f8f6ed5b126d0698388de454a5bd6ad942e5a6ad0be0ff4fdf11bcb16e6347e942c5d25f19703f7a43e4fa8de58622e9586c92102ca03dab6d2300d8243d266a4780a6b2f2f8a826523ae08fd523c059174a0fd69f142d63e8eb86e2b4f3f8bb0d8380d2079590540a16d6243e14fa91d67e80f41fa516487a8c522b203d416b3f6a6aa0f51969b07f50fbdbd4629211efc935505a85e16ea0845d2be2f02e95a18af1ffcbe23e5285b7880f9462a3f8c1cb3f838b95d4168158c3c7ff1ef942d785a1501f2b99e2e6b15d03728e545707ba3069f5838b9b505e80f6f1508c3c9336a6ca39405c61e69190560a16b828c61628ba55c412cd651efa8c6518c3df16ec3df17497466248f7c5d2a8142cfb72cbd3ea1b52f8a43d24312130d39a30ad331359f6daa64c78dce7a2bf6373931dcdb207d832b4d761a8701a40f2af89e0b44a169f79a9ac4960c82de736b534c031bcc80ac3185a2b4d2e8ad08fd92526f71f2942d645e10162d159fcd675aaa0ee30f39b4f83350c0f6c31494925c16eb4348b09966a72b41a942d406b1c8eb73382c5a9e5d1058cd676905a21af967ed3795049dcb4d6a6a3f5242a02d06012e0a167dd897ab1f6a9923648fb4e563e93b967ea61e893b967ee6d9eca943584b4e5a733b09c20068c38275ab65f159f8f74e523e5851903949015185aa942dab74615a66f6b733b9060ea7dd9a66e67720b915ccf2cfd28ebe2a050b50fc921415a91c59724d54167ff93ea82b0ea942e (by decide +kernel)

private theorem part719 : Excludes 0x10000202000000000000000000000000000 0xcd6799e4164080409010101000000000000 :=
  splitAt 1 122 0xcd6799e4164080409010101000000000000 part721 part720 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part723 : Excludes 0x10000200200000000000000000000000000 0xcd7798de104280005081001001000000000 :=
  finishCode 119 0x18c5920c289c48a4260822e0b3d5a9bd07ff8e4a83f0f28ba455b247e30a4c72e5a0c503ef20f7e5a683bd69b0f7c9864164ed82581e554103ec5191d65f17b6c37d36fa856392a0c5422d638505d32c341deb4d3ee9c964f6a8a45d27098f7ad651748795e871214174b02600198bcc1ab0d0f2d0a079544f185cfba725942b0afc98283140fb58f4320cc4289e079561a0ef83ec72f51eb4e6611c1f60ee7ef3ee879639283be174ac445d31f74e121e5588b2096293e588a07d4050ac2bf527a846588a7f66aeb944e12b11526c6fb077ac46145c01ded62c3617497a647d8e5e6a8a3ac3cad659eda9ff40f8ba5b0077a58be207d05e1a394723df5a6d07d981200950ac1c569aa390f2c1c61ccb94d892b4d6238f7c5bad62f8c21cbd69b13045a27050d3988d69b00861b4b52d84ab4d6a8ace43ca713311c62f7f2147a0c4718bd985f13c37dad362f3b50c0948fc4d5628b4fcfeb394d8aee55526cf6750bb4bdcaa7f116da4ed70541903f8c82148fcb4712acb21618b9ae5a98b6d69a5e7641106c1a85403ca7f190422d5949ab535a6cd3914f8f7d892725397a0853c551862bc41de617a51c5aa7259eef1b1d69b0714f09bec5ab1bec3cb1c956370ba55f72444e121e5761d050bca395a98b54df61e54e01de9e19456a3916dc1bd6adac9c752a172dead1e0ef0f45a9e17d623a50cdf60ef (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part724 : Excludes 0x10000200000000000000000000000000000 0xcd6798c6304080001000000000000000000 :=
  finishCode 117 0x18c7a0a3a5277f1e48901dee82f8de0ba52c588c9213ffb0847be7fb969aa39593c9f70f29ffe30e82079528b293498eb31405ad4dbc30230f24cd456a398c3c933526c61e5f1bc4b037ea4da30e9451efad4e8c39f7e59397c560a39f8c3a02e8c3ba07aba30e9db5a69edc3ca2dd8c3c8f10dfb78be258929969a9f74908f7d68260ce550f29cdd69a9059cda1e5593acf5c08c3cb270f29cdd28b079683ead34dbe9f759386cc5d31873c180541a7324ed3d67377b7c61d21e9395f16231859a630696a9a4ec5d2d39a30e9f79622b3d5f1253461d3ee2e9540fdf461d242d5382e6782a0b1159ec286e78e1e737373c80b4fbc6e76a9b38aa39b6260a844dce9f70dfc285cb9252b313879ca5473202d66271d9907a0a3eec3a0e04481d50f2a0ae41d9015c8f2d5547f461d01662f202c61e51fa02d61a0ef20283262e898bdd85e18016aa3c64f6b56d64e8150e4a8fe41dc18a82d4ce1f0e654727f13959356394c1a542f06989423d1405c28d3587a20c94988f465aa9c4de8851fc8901dee0356c80ac22d3630f30ed64e72958dcd454a3b4f402702956362cb518a825683798b2e1d5ad34f570b2d416d5b490ca17378a02c80b000b760f2b30c2287e835c61d6a682b40ac61e5238b2d636b479a7a5cb626c61d26a2cb851636bc1c3ce6e5db9eeec5f57ebdd543ed259eea9f749149b20ecff6933906ab47 (by decide +kernel)

private theorem part722 : Excludes 0x10000200000000000000000000000000000 0xcd6798c6104080001000000000000000000 :=
  splitAt 1 105 0xcd6798c6104080001000000000000000000 part724 part723 (by decide +kernel)

private theorem part718 : Excludes 0x10000200000000000000000000000000000 0xcd6798c4104080001000000000000000000 :=
  splitAt 1 109 0xcd6798c4104080001000000000000000000 part722 part719 (by decide +kernel)

private theorem part714 : Excludes 0x10000200000000000000000000000000000 0xcd679884104080001000000000000000000 :=
  splitAt 1 114 0xcd679884104080001000000000000000000 part718 part715 (by decide +kernel)

private theorem part712 : Excludes 0x10000200000000000000000000000000000 0xcd679804104080001000000000000000000 :=
  splitAt 1 115 0xcd679804104080001000000000000000000 part714 part713 (by decide +kernel)

private theorem part702 : Excludes 0x10000200000000000000000000000000000 0xcd659804104080001000000000000000000 :=
  splitAt 1 125 0xcd659804104080001000000000000000000 part712 part703 (by decide +kernel)

private theorem part694 : Excludes 0x10000200000000000000000000000000000 0xcd659004104080001000000000000000000 :=
  splitAt 1 119 0xcd659004104080001000000000000000000 part702 part695 (by decide +kernel)

private theorem part670 : Excludes 0x10000200000000000000000000000000000 0xcd659004004080001000000000000000000 :=
  splitAt 1 104 0xcd659004004080001000000000000000000 part694 part671 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part727 : Excludes 0x30080040000000000000000000000000000 0xcff6fe1a8601a6010008000000000000000 :=
  finishCode 63 0x691a062168531c4394b709a2308a2d34e1e7b59ed29ff0c1a93cfdf276d03ed4516ec1f62fbbda526a2dd7b4ca11969a93f97c395c8d92808b75442fbcb4f3daa8ad472a00b2658fb03569e7e38f6ab4d123830ce561d3926e2dd711847318c4f03a6a20b0d27f1c35aa25f75a7c34f1beb544e1ab4d0ccd1874189f8deca70d49fad08ffa0eaf69732c1fc7a62c93868b264008f4ce1b24fc7a69e288b4d3f1c5d349fc1f6527a7ad6af3da5a9707d49fa4fe386b60ba24fd47f3d5d472d376ae97dce021d314dc81f418ae82c983a62c99c46813816eb4c658fa8445921ad59cb08b0d83ecf696adb0f5ed3270d82c7d696b01877ea39580c3bf164bda569a9ff9eee4c76ada006 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part728 : Excludes 0x30000040000000000000000000000000000 0xcdfeba02800186000008000000000000000 :=
  finishCode 105 0x3e0f43a00ef60127e1df074b0e638fb14415e16f8e222dd581b88a1394767350ef8b5637794058c5a12064127e88338b4d410c1df410cb0141fc50116d9c461efad35a45f1bc671eb330bca023df0efc28a4d8a025f7395c1d658aa80daba5012fbacb503f14058932d343ce8215e19c16ac2db410cb2d5abce4b5a6b48ce2201df388d07f39aa0c5aa30f4ded283f2f3b20b2d8e0671d4189c0e62fcf693db9cd4b6e82f8519c691bc280ce637b4ac5569aa2b378879d84701ed341dd82e50116d89567b486d4a027f162f979d62b2d35ed2b4d8bce942936400940562eb434d1bc3798a1e526a85c5271255ab6b1396aad296adb00b0248662d0c98f280ded2a2b3d4cf690cb861c51ac82846834a8fd002b17949a38384f6b156aeac5d606120d72d345262d55a6ca2b15fcd5d5aa9405eeee6388ec079d685116af24fd3db2365c8e1713069ca5602d5d9a8a8ef5898b74e3a5f798830ccf69501bd9d62a70f39ba88be179d27e3b99aba0a35a184e63868064b22d5b5aacd4b2ff9c3584761685aac93f39b9907a1c76607a4d524ab3f4d11df2cb524a8d9965a5f77b5cf75607ad0c3765f72fbc1b9969a8d9 (by decide +kernel)

private theorem part726 : Excludes 0x30000040000000000000000000000000000 0xcdf6ba02800186000008000000000000000 :=
  splitAt 1 127 0xcdf6ba02800186000008000000000000000 part728 part727 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part731 : Excludes 0x10080040200000000000000000000000000 0xeff7b718865122914088440201000000000 :=
  finishCode 133 0x18c481685111049fa78d02d35dc71114174ac3659ca4ee4a18b2669b9775ab66ff4a3cd5b2eea3b6698931e0e22c93f7b70e23b87c0ba5782ee9fd67b4c1d51fe6ff961af6da30ab0d6ada48e69bbda630ad5b2eea856156b0ed6aec552ee9a0d49837c8ff1cca3fe681c44505d28ff8fde8e9586ace5843f7c9d961ea4ed6370495ed24b5a0fac3d7b4b4dd2766ff498c7ef440b86e169aee1f0a8177523f2d5c5d23d146dd07d580a51dabaa1147fca117b49f8c5d2b4b8bbb07193fad5358bbb8be2a02e9058c93b2eea36562eb0195f73da506291f5a5c5dd730ec61cc6ff40f9fbd8437fcc1d46ca4ed83b0ba6641506c16041fb99e62da4c47a2d02c5e408a51e0e341d51dab174088a6d145b0bc6e1672be3da6698c1c4fde2e94edc8e96269f8d61a8c79ed2d5b586972da6f2d4c3466ed7b4ad05a05f16833da4b962e96b2cc5b049b56d636f690c1d071737bda612a89562bfbda503ef43b88ed987693117493566ada48d8a6a4d9286e6370e23d0be3202e962acf776a5a48cbbab397bbcd4b491ad894346cc03157dbdb51fe8e959cb604d59c96a4f408ac6e5a1c4d54a1a0465abb4c56029435a6c83126acb4d174af892198d02d056aeac285e121b9958b69352e5c2e958fcc4d376bb8f42202e95209aa46791b6f5961a9b4c11ed430cdc8d758fa3b4b272d0c056b1f15fcb435a1cd5b4fe8ae4fead02c5cfeb358cb969352e5cdc2789299eda2c937fa50dedb356ded27f5586b56e263bd9c592f6d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part733 : Excludes 0x10080060000000000000000000000000000 0xefb6b698e6817281400f000000000000000 :=
  finishCode 23 0x3609022893f540e1a8019aca6e35a0b1550626e389ef17760fec3b4189ca4e531c35dc68114440e1a6ed947ae492fbbda5ab626791b6d4b6b2b924beef69a0f6d4b280b4ddab67295a6ce437b4b5942b69314f12c5a693de6a58ebc593352d50732cd63263ad056aed4b8fdec55 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part734 : Excludes 0x10080040000000000000000000000000000 0xefa6b628a60122010008000000000000000 :=
  finishCode 139 0x368c23d0a2102d681f5af0b4d49fb58e40ab56da5f2bcd406818c6a28acdc731b4c186c277adc371118977581a25d13da04651fb56c5368356a2c80b174b56db8671dc5a6830d5f72c5e0fac0d38d97468c3ad5d02ac554fe8b2562f1b8e1649cad441fdb1894393fe0bf6ada4fd00327bd62e931280ad0dab6a61ca65099bfca0293b5a6a4c583b245d69a72220bc2d357c7b4c947387c589724b075ab68057b4be0f69350c50149fb9156964c7918a48f3f1b9155c631ed28a230e612fbb90e46cad3c9dac3583ed07b9cc2805387ad2e730c1f4e1ece2b08ff50bcf6b722c61cfc6c5b402a4d58c732d07d49fb04e83db975cc270f8fc6b39402b190424fddc4616c6e0f054142aa3d83ecb0d6268ee4e1e25998b68fb480a3be598b16ce1e3b98e1ec5798b70694a39406579a51da52b01928ef5996ae2e959ab58d78441586ad8ace4a386556961b172fd07d174d07d61a9405a93391e0faa2b722ad2dc0621345a0e1edc1cad26b1195ed280146c8b2c5d2e45926af696a9ad0672f82e457e2e96117c5305d2f81cdc77f2c5d07e9438c1cb1746cbd9630741a56aeb1746c9405786a106a8cf8da693f415a4a51ff3dadab69178beef69927e2e95d18c800beec01a0662cb523f140507eb57640a0320fd19f2d35cc68d9431e83e7ce5f1dfa4d477f2c367b4a0fce1a91f591cb4f41fbe0947969a8214ecc8d91ccbd9d69a3b9386a98dc1c35647397507680b486a3fe6ada006731b083fc801410b1366b2ac8d27f391526ec636080b907e93f5d10167efa30a8d92c6a4a5c8ab152fba4a67b49fbca02c02484c78010166d393b6e455a0bda67239b4cda70ba542ea2b9016f69 (by decide +kernel)

private theorem part732 : Excludes 0x10080040000000000000000000000000000 0xefa6b608a60122010008000000000000000 :=
  splitAt 1 113 0xefa6b608a60122010008000000000000000 part734 part733 (by decide +kernel)

private theorem part730 : Excludes 0x10080040000000000000000000000000000 0xefa6b608860122010008000000000000000 :=
  splitAt 1 105 0xefa6b608860122010008000000000000000 part732 part731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part737 : Excludes 0x10004040000040000000000000000000000 0xedeeb6a1c6210a88084848010a000808000 :=
  finishCode 61 0x851b4771a40f9ae8c40fee0d3179d8926f55a3ad4da7f3da5262bc1bd5ed290d9686b3f6ada43615fad0c4fe6f59ed2e4b400a50da45d19c1fdb06638f9354bb700293646cad0dca72365ab6c6356cddb2934dea4678bcf1bb549af8338dc31813792763df4869c44e6a8c1c2d687305d06a93b2f1ed31edd6830afd6c58bca0338ebd9658bc93b67110581edb310dab67b726ab17e626b10d036d5b41dcd371efac066adbb8c620463769edce223df0efb00922c663dbad4e0d24c7415ad0d10834bdde3dbc1adaba801263cb3d8f6e5cb5918c6e098339bd86a0c30e19cd502317dd00341d549a7eb418ca4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part739 : Excludes 0x10004040008000000000000000000000000 0xedfeb681c2014b09081c081020200040000 :=
  finishCode 75 0x441c0392145a6b68d22e8ee356c7f650198921f340ad069985eb17280ad0dab6a3983e6de2c0c4245e385a9348e339849569ef04c9c347a2c5f9c869ef2809cad06b391d88e099385a48f5b9892a03034ad4d016b43581003069962ea1758bc7b777214711600f9be070d4feb90e49dabf658bc70b526c50137f9e0e4b96a6b43400a5027b8b96b4358ad075280a809fd51c82565a093dd0031b8db4732cc4962f9405ab68010f9c1ae7b4ad5d002b0349db56ce170a368de0046280c1fe0eea2b37887cd40490a02b47849ef6958aad1e732a50e733bda47f65e76f14c61160378b9965a0a4edc871cdd34732cb576b1bda648bcf5758bad0d22f399562eb43331600cbd06958a931d406f695aba8ad8046ccf77263a80ca02b173f2ca036a494059069167b1b1d6865012e5c6c77b682645aa82b8b6eb53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part740 : Excludes 0x10004040000000000000000000000000000 0xedeeb681c2814a080808000000000000000 :=
  finishCode 89 0x511a449fb78e2368ee3201d70f9a93e2fba044ff717dd6a67217de38f870d69ace17de3888f2e4088fec9eedc17ddf05b0e6ae6d9042b1746cad34e6e9ef731a04646c9ca6731d0a17ddf0386ac06486940436f28fe5269405b4711881fd9bd65a3a0fe4109c0db87c1405a9c7d3582a93d252931280a4c65a6b5765a9979cbcf20fdf0591ab738ece06e675a69cd60d7140502270341dc88370e2270be1c7d22f250d65a811922e94385122f250d857285d05eb47607a0465a9a93d286a3f981e821417ad354c5a3c6f5580a50c7bec8245e38fa3245aa0b138fc88388b4d6d162328f56021df0f9b38dc0f7d2632d55022f6b4fea4ece6ac5798af0afca02b0185140386a30501694c9d951ea84e3dbac447bee439686b1351ec501711bc5903e63df460e6ab2d9ed2c5b387b04e7309cace571404b7a71f7c1b802ac5017b4b99c28a73516da0fce3e2db907ee5d8b96c4d7258afda6e5db85b63df (by decide +kernel)

private theorem part738 : Excludes 0x10004040000000000000000000000000000 0xedeeb681c2014a080808000000000000000 :=
  splitAt 1 99 0xedeeb681c2014a080808000000000000000 part740 part739 (by decide +kernel)

private theorem part736 : Excludes 0x10004040000000000000000000000000000 0xedeeb681c2010a080808000000000000000 :=
  splitAt 1 90 0xedeeb681c2010a080808000000000000000 part738 part737 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part742 : Excludes 0x10000050000000000000000000000000000 0xedaffb24a0011220000aa00000000000000 :=
  finishCode 31 0x208800a0317dc1d20ef73214611b46adc72d280a0ec8161f3671403779cd53b32c35edae45280af0f699ecac5b581a0edc8f41fc92e93f9c8a50183dce677b2b914e6a93f7b494059c4ffc3cb5098b2c3be735280cc6399ded281b368ce4139ab56e368b905cc69fc70b300a4fc5d21f365164451ed22e91f5ad3e3e1bdd4beed3da0f707f2e5b9160fad5f942ef772fbb56c5d2d459eee93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part744 : Excludes 0x10000040040000000000000000000000000 0xedaefa1380094200010a008008008000000 :=
  finishCode 71 0x6312073127f0a388ca07cc5d3102d69ad2b96825f3077a49550077b70831417cc0d30cb155a7302a581b207dac662f6e1905004c3099d69a0e9280877e5a6b4965a683a562f2d341d2ca03bc9ab315d69a40b380cc5726ab2872398b4d71214077c5e7317902c3e6ce348b478a02b530efa79e12d9bf4e6aa4f85d30a3700ef317c94383bcd5b588b0bd6232cf5ab7102dcc851ab71bfc7be0ef0f9b48dc077e280877e51dc925074c1092585d20ef6add003980ef124c25b3f593543e69259a464d50f9c937851bc802080cbcf756adad556821f3077a486198e1e60b5a0ad5da0731c1f35a69cdcbea801804ab1783e87cdab61f3849f095600280c0e95a6c501 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part746 : Excludes 0x10000040002000000000200000000000000 0xedaef21995014212001840c400020021041 :=
  finishCode 85 0xc62889624fe14691dc2fbb88da4001f38214031c3c1deb019eea1b1722a895c8b3e0e6381dee4989aaf80f7e077a0fd3df2d4d3b23df6b2c6b3242bdd53d272d6adbb8f75981eb1f0f9ace41deb4f8c1a72d6adabcd24b3db581ea3b52783a49db04428f81c467ad8e95eb2d5b0f983bdaa3356c3e6b20ba6492a93d63723bd28ea017aeb98e2fab56e14771cc7c03e70420be0779405b86b1c2e9722cd63626cc5b725b03d6ae4ed7c138077a18a3b8e5ab4f61acb2351eb9760ff24d524ad4951ec4d562bb974e1edc338d427a625dc1fdeeed63508ad2ce2272d408cb1b27bad3e1caa0149eeb0d9cce4b75a7b58d6af077ca024ed851dc801d87c1c4077b9160f9a8e5ac62e930ccd5b4fea7f626aad04e1e07d89da0ef5a7cd432809c3dd06e128801ab71264dda4f74fe97d4f06adcf5b57ba0149763c156128f20148e32c7dab718649ee4938b12af783ead3d62ad634fec4f769149b27f45d250127683a6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part747 : Excludes 0x10000040002000000000000000000000000 0xedaef210940142100008608400020001000 :=
  finishCode 147 0x6511077169b0a400e803bd8836cc8d96ad9c3d27e601511b449fa501f383ec6ed46cc7e3731a7c53b6d3793e24ed73197ddacb11ed1b24ed0f99f8e27681cd3e21f35f03e69258a02e459907c0e6b27c4dde0e9280b004ed4a167b3db5ed25d1376a4fc3beb57838c9f1500bda43beb1549fbda66269cd67b483a5246dc24fd4230acc9eec0135649bb15c4a33da5023044010a2880ef4815c49fb685f75f098e1f36b2c4ed722cf69094d07b73093b5ed2da1c3e3f1931c3e62739cca02f2769c3d5c6f1cc2fbb683df143c8d958da366731a366591b8731b469893b66ab8ba6276b55e491bdad86ae67402819e698b98e58ab99c256d3d3f2ac6d3b234b94069d92769bcdcc6f1b80f9a366276b16e7b6816da6eb5746cb92c7beb2d89dad375abc9d951e9bcdcbae6746cbe0d2236639a83a4a0271f83720a1724b99526a0e90efc8d9276c28e6370de1405ed339143e671f907e93f6f03e72c351b25f7387b18861bd6417ad4e83ebd9526b3db4fc6ba2a09c23658c725c067381a0160d8bda5c96e5d165ce47379bda5ed31c0d86b398cdeaf69280ce23986f585d21f337ac5f77aea36527e83f96a65f73878f7d4477127f003980ef6f1b44b03e64ed9cbe8d91add07b6a8b0c63e797ddeea8d9590997027daba4936adb59446b08ec8ead5b733819e6ad9f951b2e6124641f9b94b165f76ad94051df1c3cdea72da0f6d5b771cc6f1900f9be1042c8e387a4941da5016a07bf18053e273537ab52646cb99e4f8a365eca3df276a49646cbe0dc1bd41dee6d903ee4b72e9cb524b3da49ab461decaf6d6b2c00ce03bdcbb1245cce8d926aa7a646cb975aa71c3cdeae641f639aa0fd03e4f7733c703 (by decide +kernel)

private theorem part745 : Excludes 0x10000040000000000000000000000000000 0xedaef210840102000008000000000000000 :=
  splitAt 4753 57 0xedaef210940142100008408400020001000 part747 part746 (by decide +kernel)

private theorem part743 : Excludes 0x10000040000000000000000000000000000 0xedaef210800102000008000000000000000 :=
  splitAt 1 102 0xedaef210800102000008000000000000000 part745 part744 (by decide +kernel)

private theorem part741 : Excludes 0x10000040000000000000000000000000000 0xedaef200800102000008000000000000000 :=
  splitAt 1 112 0xedaef200800102000008000000000000000 part743 part742 (by decide +kernel)

private theorem part735 : Excludes 0x10000040000000000000000000000000000 0xedaeb200800102000008000000000000000 :=
  splitAt 1 122 0xedaeb200800102000008000000000000000 part741 part736 (by decide +kernel)

private theorem part729 : Excludes 0x10000040000000000000000000000000000 0xeda6b200800102000008000000000000000 :=
  splitAt 1 127 0xeda6b200800102000008000000000000000 part735 part730 (by decide +kernel)

private theorem part725 : Excludes 0x10000000000000000000000000000000000 0xcd249200000000000000000000000000000 :=
  splitAt 4490 137 0xcda6b200800102000008000000000000000 part729 part726 (by decide +kernel)

private theorem part669 : Excludes 0x10000000000000000000000000000000000 0xcd249000000000000000000000000000000 :=
  splitAt 1 117 0xcd249000000000000000000000000000000 part725 part670 (by decide +kernel)

private theorem part627 : Excludes 0x10000000000000000000000000000000000 0xcd248000000000000000000000000000000 :=
  splitAt 1 120 0xcd248000000000000000000000000000000 part669 part628 (by decide +kernel)

private theorem part587 : Excludes 0x10000000000000000000000000000000000 0xcc248000000000000000000000000000000 :=
  splitAt 1 132 0xcc248000000000000000000000000000000 part627 part588 (by decide +kernel)

private theorem part541 : Excludes 0x10000000000000000000000000000000000 0xcc240000000000000000000000000000000 :=
  splitAt 1 123 0xcc240000000000000000000000000000000 part587 part542 (by decide +kernel)

private theorem part475 : Excludes 0x10000000000000000000000000000000000 0xcc200000000000000000000000000000000 :=
  splitAt 1 126 0xcc200000000000000000000000000000000 part541 part476 (by decide +kernel)


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem caseBBBBR (c : Nat → Bool) (hp : Pal 280 c) (ha : Avoid 280 17 c)
    (v0 : c 139 = false) (v1 : c 134 = false) (v2 : c 135 = false) (v3 : c 138 = false) (v4 : c 136 = true) : False :=
  part475 c hp ha (insertRed (by simp [Red] : Red c 0) v4) (by
      have mask : addedBlue 280 moves.unary 0 0xcc000000000000000000000000000000000 136 = 0xcc200000000000000000000000000000000 := by decide +kernel
      rw [← mask]
      exact added_sound moves hp ha (by simp [Red] : Red c 0) (insertBlue (insertBlue (insertBlue (insertBlue (blue_zero c) v0) v1) v2) v3) v4)

end Case280
end PalindromicSeventeenEvenThird

open PalindromicSeventeenEvenThird

theorem OMA.solution : OMA.R_Green14_W_3_17_R2_H2_R1.H3 := by
  intro c hp ha a b e disj
  cases f : c 138 with
  | true => exact Case280.caseBBBR c hp ha a b e f
  | false => exact Case280.caseBBBBR c hp ha a b e f (disj.resolve_left (by simp [f]))
