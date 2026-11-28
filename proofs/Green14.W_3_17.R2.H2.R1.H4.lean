import OMAReductions.R_Green14_W_3_17_R2_H2_R1

/-! Case 4 of the length-280 upper bound for the palindromic (3,17)
problem, Table 6 of Ahmed, Kullmann and Snevily (arXiv:1102.5433).
The proof checks a finite branching certificate for the specified
colors near the axis of reflection. Lean formalization by @KoaOkano. -/
namespace PalindromicSeventeenEvenFourth
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

-- Data-valued declarations make the numerical reduction finish before
-- later nodes are elaborated. Each checked box contains its Lean proof.
private abbrev Box (r b : Nat) := PLift (Excludes r b)

private def endBox {r b : Nat} (count bits : Nat)
    (h : redCheck moves (packedTree count bits) r b = true) : Box r b :=
  ⟨finishCode count bits h⟩

private def splitBox {r b rr br : Nat} (w p bb : Nat)
    (right : Box rr (bb ||| 2^p)) (left : Box (rr ||| 2^p) br)
    (ok : reaches moves w r b rr bb p br=true) : Box r b :=
  ⟨splitAt w p bb right.down left.down ok⟩


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part4 : Box 0x20008801000000000000000000000000000 0xdd7b24e21a32444cc081100200000000000 :=
  endBox 149 0x2147a1d06e1885b0c4ad4188d63f24ad69e3dd58fc9416a15440eb9b669abdada6683d370cd357b5b4ce0fa6c305669a93dded66fd6a8cf6b27baa8be185d784fb8f4e27bbdad26aa453f9c4f76a05473dbd3ea8ff6999c7decf3dbd64751903d11437ea105c995e22e7371b12da673dad66b1859a6a7276ab9ed4dc393abc66af9afcdc6b4935fc4c909bc7278c2c7d91368a75acab0759ab4c57042099341d56a27d998924c96b3b90564a2e7a0fa29183ab56d545b1ccf41f5ec2f71522a0f4bfec42f883d3e148a0959c82e67153a3d5cbb399e0fa6e7373cf633eebd4411ebe359e006c1f60f2f6b1d585dd006a456b3c7d93a164641305a7a30843109078b9281d2e4d1853ecc1ac2fa601f666a7a405a9a9019ed64c98fb2f6b72e9afe0fb21072306e264b12dabe9019a466e383aa074dc73dadaca901277c1f5cab30cd85b07d371b9066b3b12d256b35173ad8923505f33b166ab4f173bd8e7a9c615aa29db393c1ac75f06b9836f53151c1ae59aad3c6df39bcd7eb4f7b0bdc45ceaa268ea24d60f327dd202803046c28f6af8f76518ac052464f7461106202fa595874a81d579c24d091b57cfbb348daaeaff989681d35fb48aa268c80f4d7c385cb2d2f3870c9ee7a0b9e2f39bf5a871dc9f539aad467b3c0a3595a91da85f05ce7c0a8e39abda5462b417b4cc158dc290760ac9f5720a41d466c8238c41e893d231a673da51c66fd6a6a407d98e16d5b0d4bdae385ac3e483b54435a7a46167b48e65ccac5d255b4cdace9f598961ada30aaff2cc8a8cfb2d65173b70c63d6e83cb5458623af592aced3b730c5ed6e5d732b59657fb99ded6a00b9dab72505ed346160e23af47cbdacbcebc2a8c413dde87507bae5385aa7350dfcd2b518acb683ac615866b430529c2e69ea495416727835a3dd71cce556afc1e4e4e4f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part6 : Box 0x20018001000000000000000000000000000 0xdf724d2a5803c00ac003000200000000000 :=
  endBox 99 0xfe3c8dc398c42906193178f7641ebda6387b08e0185d805f1aa316fcd32f6b83ca44d032839699c8094c1ab71bfd8bf293dab66e1c0c4791f2d5b513b17d85f392d1f2a4f4f6cd5f527b80ae280e4196a2a15527a025072d659676827722cb57731a0249dee677b4cc43a8e42066732a89d60e72b495a07507ab217d6733b90523a2dd3e0e1ee4b9ab65f5596cc23725b56da9f17d5ab691316e9c3d805611c5f09dee0399e69aa0e452323746d67e36a6c8f9551c05f178158c7e347fad0d28ee419cba8ff9cc270d724cd5f7319bc565ae419cbab1d631ab7399d82ac5d463ad453b715e582ad676adaa86a1c848993b70790368dcc7269259ace803492cf6f963ad5b489a3e58883ec72939baf85ff40cc839834ce633d5b995012f03807e31261db9cac9da807413b2872b41b871e8c0acadeced67724c699732a3e4562e43536401a075642dfc2dd4105232d5c0ca17f7b4c28b7b59cde695826d07afc348c2351641eb57c39672939bb28be3516387a4d45baf69a0fae636a29c3c7bb1c3dee2a413be34dc1f5ea62dd41e8f75ed306b6732a4dc5ba0b5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part8 : Box 0x20008041000000000000000000000000000 0xddf31c2a3c02c428d009208200000000000 :=
  endBox 133 0x1fc702147e1886114c570e5273740bc8396e1a5738ece4ec1998be819695bc8f42a89a188da8395c1f639aa0e6480b9047a6e5d9ccea294f6cb2341cad3ce56f6983968271739cae5f1603815c40ca01e7b4a3563f1b99ce1e7359ed271157bc8072809865647b4cb1f404a4acc3320257c5718073104e8397b4cd3130bb99e473d0757bb8b9cb2e28b403aa8c8308e63c8e67a0f26172f98b9daa30af5e45abc7ab1e9c1e58b293772e8eae388c1e58b27359eee9ed62c9405ccf24d60f281995ef079600e1b357c9dee5d9cced656ad9c357c5805cf251cbe6623413a0e5ab718bc396817590dfb3da4daa8e76b29c658930b9d4073180280ab8185854681741cba0c5f9032d2b16eb95639382cd452d3d6312173d6cb925a31d2a01d49e92b93dae4b71ca01d5c59100e83949ac6c7145a93cb93293e40cb975646b1cc5815c16aa48e48ea4d500e9239eda5b716e9bf6403a51c396e6f962ef690dd8b75ccee6f900e2d54a38ac6403b00b23516527a4bcdde70b4c138450d8f3da5a8a291151970c812a589304d630ae4147cc1f6623cc4931786656af18bda7ad5b7b4b57e4ed855cbd271f6adb18c8168d185c149e7c276e388a8045165d183cc6e71bcb1245567e37b4a32e044b49e0fa3532fac353732827589323746a67d36adbda66117c394bda605a9404396a02286d5947aa4f321ed2a299a6ed5b963e2a39a8a6d56adb58e82202dd720ca2951eb56da6313bded31f8d47ab3558fcf69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part10 : Box 0x20008001000400000000000000000000000 0xdd7b4c621a826018c023008600180020008 :=
  endBox 81 0x3c0c8370d23005276a1105f149e7194a0ca2973396150729419452aa293ce4ee5d9cceb0141ca00d44e82d699c81d6b3a0e630b2504dfad4f720b99d49eaf18e6eb0d41ea93d88851587316c30ca0e646ea89cdfa62383eca2737ea0e6720b99c5bae620e658f9bf544e62f733cb1f513c92f168a8a683ba025a668396f1884c17c38d9ca4fbb41f507ac5972ea0e5acf20de41ec1f5205f1ac40ca0e4d7f072da469f76a8b99d86e4659c8707d38697cc47b399ce1a7d96b3a7de37a97fd484019b883d723cd674fbb57e72eb995ace901982ae494fbaa8ea310e499026c314fb9bccc5e83d6e0c2f1cd5203200dc925ff4fbad8b4993ee73772ec83956188733d07941c9ca4c4ae00d9e583b545cce819698a0e5cbb399d3b71c9d82e62f733b91dd06a1b879170317c61955181b168cdfef69416a08d485b0dc324bc237306cdc281d578c9db83e9bfcdc31cdc5ba81d38dc8232f4cc47159c71b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part12 : Box 0x20008001000020000000000000000000000 0xdd7b4c6258064108c401180221004400080 :=
  endBox 95 0x1cc6917c551b8519bc083da0fa51d28fb55e599a08d07a9358e1e81758ba8c507af0370c5f9ab707d28e947d8841cc737386c80741cb80a62d8e81cddecf2bdd03af7783ba39c7ba6192cacf6957b9c3cfaf1894e36e55625c3dd126bdace1e91330ca0766116c293d18562f982cc5e2e778107b4614fd2527378d06f83ec615a9e62557cc9f541e986503a527851c07405cf07d8c4ae55926ee6f40ec82d4716070180488c2d54a3a01d0722d5900eaa242e3f38f74e22089a30a3dd4f0a05e4f6a4dce229e18c2c616621d4851a440ea0b53db348ce6f0799acef691eeb56d584007bac5990322b1729cb51489c1e65008a8d032b2d485a42e587b57d6923dd640c81e0503f3d075244bd6d3daa01630c06afcf6f5a8b12e3869275acf3d646b6d3d616af890380de3c88197b5caf18c2bd660ea91357bd075403bddd6a3359cfd29c312e736b175abf2375eeef59a30af7762ca375303f4c3815a8b59cde2d679cbab0f5c17c75154608cd3d4919c7e0eab2d5a19f9e6afbd9dab6d2341cb046386b48dab683957cd1855a8c616401b59d8bb0756adad26 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part14 : Box 0x20008001008000000000000000000000000 0xdd770e6a18066008c043100241008040000 :=
  endBox 121 0x428f4310d4290ca3a081d416ab092b6a2c71b39b947c7ba7379ccb1ca5fc791b83fe8b9cc4b41f4dfe70b83ed07d93ea7373fe9ca63febc8aa308dc3f907d8c4a623561ed294785ba737a0fb2445046a45413c8234a39865ed2dc2b05dd85ba619394ce4b7b498bda7b41f44e6c5d41b947e7417c5505bae62a062f370e6ed5b963f0693f996ae30b356e37f96ad3b6d241ce39b9ea63f9a7b5eee6fd8c2cf59317b988a1cdcc5e35d9cded5b93c2d5b8de2d3d39bb48b359ed2d3d6a29c6d61b1b4cfe66fd5f1b873154173947d07341e428e6176adcd337b4a0e510386cd5b37ea6080200e158964d222c116209eae62e9c3500f209e0fb0b9dcc37ec013733a7845ced332ffb976386b59d845b19070154173b13e7b4979d7c699c837404d185699b17d545105565e76b3cc317b49c2c7a67d39acee5d4a0cd67551142f39ca6725b974e567d3413ce655969cae618b99590700d03e1882a8461638db0456aeb018e1a3d39416b01608947e41cbc0f678e16d358697231ded2b4160a8f4decef699cc600a3eb01f88392dbd1814a3bda53c2827627d1854649bf528e9378dfa8e3da4337278500f185870a16d620e1738e47ba2dd4d100f3045eee3cb492a09e608b9760f2819 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part15 : Box 0x20008001000000000000000000000000000 0xdd730c6218866008c001000200000000000 :=
  endBox 41 0x6e09ead4144dfc38dc82d5279c2ce4e3dd905ac82e0a2228b0f9a8ab3b527a8a60ddb59c5bab0f6a6cc3b16eb56e37e9fcd49e9479a8ab3b7f1904c05cede2c071b5f182b2075072d4f8b928ff404a3fe49bbd09379416c5947f9fa6721c48f37ac1e5ccad5b7b5c1f5e8831584c16c386a51d073398e0ea729733cd3183ec1e5072913733cc314139ff5226d5b83ebdc63fea82d07a72998be839618a0f5cbb399ce528276500432c052021b349ba0f5ee31ff4e528ff (by decide +kernel)

private def part13 : Box 0x20008001000000000000000000000000000 0xdd730c6218066008c001000200000000000 :=
  splitBox 1 99 0xdd730c6218066008c001000200000000000 part15 part14 (by decide +kernel)

private def part11 : Box 0x20008001000000000000000000000000000 0xdd730c6218064008c001000200000000000 :=
  splitBox 1 89 0xdd730c6218064008c001000200000000000 part13 part12 (by decide +kernel)

private def part9 : Box 0x20008001000000000000000000000000000 0xdd730c6218024008c001000200000000000 :=
  splitBox 1 94 0xdd730c6218024008c001000200000000000 part11 part10 (by decide +kernel)

private def part7 : Box 0x20008001000000000000000000000000000 0xdd730c2218024008c001000200000000000 :=
  splitBox 1 114 0xdd730c2218024008c001000200000000000 part9 part8 (by decide +kernel)

private def part5 : Box 0x20008001000000000000000000000000000 0xdd720c2218024008c001000200000000000 :=
  splitBox 1 124 0xdd720c2218024008c001000200000000000 part7 part6 (by decide +kernel)

private def part3 : Box 0x20008001000000000000000000000000000 0xdd72042218024008c001000200000000000 :=
  splitBox 1 119 0xdd72042218024008c001000200000000000 part5 part4 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part19 : Box 0x2000c000008000001000000000000000000 0xdd5d264bb424780380d210026a000640084 :=
  endBox 75 0x851f4621dc70150730e3672b15fc0cf8c2c2bf1f4ac6504f147c1a671b740d41416072c656c277ca4d495b56d23af0147e6ad9bc68c2a91e0c4e11c3e149ac498fce6fd722b98a1194622ab8c0a505cba51f4a0c03d9422a2509bc70b4a0947dab71bc4a3ee60dee836a82d3fac3328f8296836b56e0c4716c50fc0cd515a935544a162f28c4fa706d04aac560669f4e0da3f99ed68f54fea91612a979d44b185701ca71a6497a2b91dab56c19a2b9876ad5b7317c6a6c7d372e8f0ca3ea45701cc70fe5a9f1f4d1465185b0f4cfa6c2d8e16d5b1fcc6fd7419c1fcb50827515c6d75a1b99414b3d9cdfaa2b36bc615473461585a6c28ae16db564dfac2d62ead8c339c8f18536bc6164feb0cda86017c0698724e1739bda52f776ac9c2e1e5b99d25f034d8b30a6630a3f9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part21 : Box 0x2000c000008000000000200000000000000 0xdd5d261b942578059056110060001448000 :=
  endBox 41 0x1e074190601500e48fe60db34d4bca2e71f4b4d65aa9ca54c690dfed678d8eb3f5aab13e729a474bcf34cc5ceee2d8fa391e464b0c41a671b395a88839942ef6b526c1e67b5834cff271b8ff2b454a15450148aa47836cb573ec825402339056af0790cec8f583ca825ab6a2b57f9f649df1f6544afa17967ad8ed5abae4937f9c35400ccc8293dac5e7051bb8d2353e523967568a71b39bad859d51fc2e762cc6e11d8c6156c1d8cb172ce93bc13ab43948e1a9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part23 : Box 0x2000c000008000000000000000008000000 0xdd5d260b94057841905f300060100440000 :=
  endBox 91 0x78180641d0701500e48fe4f872d55ab6c332558fa4bcab3f9ace4ab3fcad5550501884e230330cc34ad5b2f2a5043628e01ce159a5053c34614a3e1998dfae427106176568b27f5a9f1f0d6aad5b051c0418c2a784a3eb3f8e16d5b3706c31f9e0f26a962fa475a9a6fd378b56ca3f1c2dc054138360e1b0a15ab63a9413979540515c51f3fcb10589eb17414ac5e385ad0d89ee55a0f30735a1b59cdfa70d173cc116b39c2d04e83947124385cd5b156947c0f651f96031bc4dde51f771c0611052e412acbcb23253fae43069a09e5a2b90ce172d0d04ee8299062d14de339960f2d5b3779c2dc830f0c55a6f159f9c2e581b56e2cab0cc55a70b4a11845148aa470ceb9260c5b926724c26b04aa915ab6e6598624ad2ecb56e14531c0640e1ac2998bad5b403b13ca3e0d39eee807387827e6ad9bc510020ca0b3da834d8bed5b069cd29732947ca3f06556aa5c9497ad8e0308c81bfe48e979c5cec318e6ea028ad49a941919225101eb98d82aa470509f5e387b16567f1b858620a52f3b488a250c3362e86a658b833e4fead1562f06a4f6b06d4dc259d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part24 : Box 0x2000c000008000000000000000000000000 0xdd5d260b940478019052300060008040000 :=
  endBox 69 0x1e07b4ba0c8380b80fa61fcb38e6428ee0b9d3c34614bca51f62ca0a4d8038c3c32e4b17548ab57874670b90120d3404c8294e1cdec338bcad21cde5aab13e0178e4e30ad35510dc301ab618d9c826e150b9c2cdc618d949ab45377c189c1b04ef8bb26ef7b5c9fd619a9356aa4ef87271851e99c2c74313b51ea92b28f947e581acfddc531587d168a8a1cdcbb3391567e6f159fc4bd2ecb91433b2cfc14a6d78e6e7e78bcaa4d5089cad545318672c5d456097052b0ce277976543ea25256c4bd6ada8adc064140627b4a68c0ac5ca3ed5d414b9be38d92ad8bb1b5ce6e6c46162df8f4cbca6f13778f4e619ad8ca380a2b04bc737173acfe370825cbce92b812ed21b009596ae6e1522b0558ba0cd803ab1769ab0ce30b3164dc259d (by decide +kernel)

private def part22 : Box 0x2000c000008000000000000000000000000 0xdd5d260b940478019052300060000040000 :=
  splitBox 1 27 0xdd5d260b940478019052300060000040000 part24 part23 (by decide +kernel)

private def part20 : Box 0x2000c000008000000000000000000000000 0xdd5d260b940478019052100060000040000 :=
  splitBox 1 57 0xdd5d260b940478019052100060000040000 part22 part21 (by decide +kernel)

private def part18 : Box 0x2000c000008000000000000000000000000 0xdd5d260b940478018052100060000040000 :=
  splitBox 1 72 0xdd5d260b940478018052100060000040000 part20 part19 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part26 : Box 0x2004c000000000000000000000000000000 0xddf93687949af8000000000000000000000 :=
  endBox 27 0x1dc7d1c8640a26e0149d407b48fe5073179d49ef71989ea133779bbe49eb38e6790721cb160c0d3501904f4d06b6ae8fe589e7f941c94059c38cc839526c08338cc82767190396c839058a0e6396872c1a70fe49d6ce0fe53ef317cbceb4939a8f4e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part28 : Box 0x2000c000000000000008000000000000000 0xdd5d264795d278000100400000050000018 :=
  endBox 121 0xf03a0e02e00d383923e91fcbb902278a82804ff690f0293a93e733b905acf28ed27a783da5c832024bb2839527b04657f9bbd4768391c9ca1369a9bf5ed2527509c5277b4b4a67b4a3d527a5276f1a46b3cc598c2ad14e36737069b53e37fb56ded22e78f6ac4f6adbda5bc8320e31725ed2f61173a89549a92f988a92b1becf716ada4bd27b023b8a82f08a144d4233d9e0e2735275ad8727720cc4705882565149e0527514c6fd2f2b50e7b49bf5cdb3dace4ea297b4b56ca4ea00ae660da8e436692b4a0a8e66117037015a0b113aca25725b904de2d5b7b4c1a325ca8e549b2475ab6f697b4cfa3985098a4ed430466a1b574e328c7944ece3500c793d2727396a78c3793fe9fd51db106058b56c15b30449d6ca2d8c22f8b82380b18c2ce414a0a80c386a4d378c91d5a882fcdc316fd49a2ab173979ded20bf4e144b28e45cf179ce6e9c290a3952693d67acb8ed2564f59ed32505a8691c0483cb25060831d781e9c4f5736c0318c2c1c5cceb5105fba0b81b8bc2ccd6a31859ed63b57b5d185838c1c5471ed25827f67b3a41dc0370bdae0c6c6158b218da0e2f6d89eb1852dfcaff8c2acad822602c96378ad45048c2cf6b5a4a7dd8832f09806f45ce4f52d2c71b7b4c907736ba0d2395639bb99dc820cf471c8339b520e93d1aac3b14979bfc1372354bce6e1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part30 : Box 0x2000c000000000200000000000000000000 0xdd5d3f4394807c010008001418002100060 :=
  endBox 103 0x408fa2f0dc2785136409feb6200e5d9ccea29497a89e514ce411fca89c95b398d1eac83003b58e363f9737cd6750aa4bd1eb3da5682737350a12de2c65c05aac809394af8f538fcee6796aae45378a4ae618bdc5aa2a0b1fc972504f2cfd012729641b873180293b80f6987f29628a637ebda6509c8c78c29bc523af69601c04f07f2b419ed234f485a844e3293d527ad063779c6dcbb399d45293d949ea27497b78e01c6e3fc9ca4f8034c1cb837b59cde2b61f9e6179f9e4fba383f972ed0696a8b165a673045acaf694514c360de270d5412c2f2a7ae39abd45a8727ac4b6a1139a8afe736b9153d69eb980710e3341e5ed27354f5cd2541c9f9e508872dc8eb6399e0e59c65c8a8f593faf6b38cb801cb8dfb1852f2c1a41a62bf4138fe5a805fc7e75149c9ce6aa046068c2a8edca2f693f3a8a53fb3dacdfade380dc388c8034da633595ed23f9413c83787d27299845d19c6403969612e4166d25948ae4b9ed2e458dc70ab548ee4525c82b4f8508c6f1722a5062c69c9d23aa1159fbda5ed3370f692ec872639a9726 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part31 : Box 0x2000c000000000000000000000000000000 0xdd5d2603948078200008000000000000000 :=
  endBox 157 0x3c093f811dc7d1cc6e1c428e949d6771cd563a0d35c16c59dad253df28aded7062d6ae28f58bc70d541c0284ae0737699d1854a0b9960de3f95abd06f4a0bdc6512a8fdbc7007f3209ce528e28e63f3b56d49ac47944a2d58286b194f1b13dcc63f9451504f15e3289c796e6727faa8b60f2d703869cac4fb4614fa6af962ebd4542ab49616d185985a72b990059cc1b62e9cd544ee4b8e36837733b99e27f9bf56a3077393b20ce2f8c4209e8c282cc1769e209e51393adab741dd19272d1fca283f951ecc33722ce67514b53cdaf30447f24eb6716c83bc8c741bc614e4e1cb8c2ce6d41b8afd836727463ce631598294daea4d275ae0e03206e3918e1631f483343923f96a1b84a019aa02a82b9371cd375a1b56e134b9bdaa2699962ef636a8b4de371a388f594724e5515aa8d319ea20995968f4dacb3703d3964ab497b5c3d36a1b8831837231d3fab2551c9c0d905e1837231d48e0ab0da82fe60dcc336adc4e551faa8e3b93fb1851e9a7f649174451301e99488c7622b0cdaa2d5b8f566e37accaff348a7f67b5a8fdab6d4359683a9ed56ae0cd523d185641283354523a2e76a8c8f56adabfe0c839ce6d4fe833547ee51876b06b12e818c19ae0320b807261fcb38b6356e47c979c5cef6da30a5a36adb59419ae6f8e36d5b7701a7356ce368275316c551cdf029c3870628ae7b583354726e3871ee6f066b385a394660cd729ce6d127968dcba0cd988640f405682cdc8f399d44aa17512ce4772ec615863168d472a4d72ece670e5bb8e0228737096c01d4fe809dcdeb2558b833ce36f6d93eb185067ad8ba2281b78c2ca391e9a8e68c293d549b2c749eae6d89eb185592af8d43703d385720cd4a0ca3f15cc9f7592870c19b1b8564a92b (by decide +kernel)

private def part29 : Box 0x2000c000000000000000000000000000000 0xdd5d2603948078000008000000000000000 :=
  splitBox 1 81 0xdd5d2603948078000008000000000000000 part31 part30 (by decide +kernel)

private def part27 : Box 0x2000c000000000000000000000000000000 0xdd5d2603948078000000000000000000000 :=
  splitBox 1 63 0xdd5d2603948078000000000000000000000 part29 part28 (by decide +kernel)

private def part25 : Box 0x2000c000000000000000000000000000000 0xdd592603948078000000000000000000000 :=
  splitBox 1 126 0xdd592603948078000000000000000000000 part27 part26 (by decide +kernel)

private def part17 : Box 0x2000c000000000000000000000000000000 0xdd592603940078000000000000000000000 :=
  splitBox 1 99 0xdd592603940078000000000000000000000 part25 part18 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part34 : Box 0x20048000020000000000000000000000000 0xddf87c97509240094121002400001000000 :=
  endBox 47 0x3e0fa390c83a05275816c1fca0e630babfe7209bbe0fab6205e06a9f44c2e0d58fbb07d312944e740a3ad623d6731c1f5072e41733b382a99acae6341c8ad64f5c1f5a96e634fbcf6f41cb54540641d0404c83930b8fe4e3335445cea3d306c8396a8a09e7b48abd3d6d6530bc28e83386258c5e4eb9aae9eb7238744c1aa8251e275b3805593d2f716ada8f5ed2d43513a51d47b27a683ba89ce5a4eb1fca80e833883998bed2530598bdee327a4ffa0d5306b20d258daa4ed41ca8f549e5f3928ed516afcf6350997cd26e617 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part35 : Box 0x20048000000000000000000000000000000 0xddf07487129240000000000000000000000 :=
  endBox 149 0xae280f81cc5dc641c8700a4eb03383f95b1073185ded71bbcfd27e9925ef69527985e51ec61527b06f595d06f483b9b527a8c3a0be2c0501414c2af1f8a0e51c3e8d06f4f79f9d256f69869e2dd6b2830588838c6d5404988cc1aa3b8dde2af8daa81741c94045bb18bce4eaa3a88a20de5a0a08c7a6d61cd65a0872d0533388299456839515cc554f01ab2bfc39683906ac82974188497c3f93069865904f07f24f78b1ec5f47c985c993200c7571cd412b13dd886709db0ab54768232f998bd347507a720cd477026c1ab0b760ef205d052f83f8ee3e8e4320d4149d78850a266d59ece0d56ad9894c46c1f928eb1d3e89c7dd4605c6e158a985ce5a617a0e23f957cc6fd289ba851d401cb410e5ad264fbb1554568275f164157c1cb4a3cb453e8ac0c55e90b311b5967b6a7bc5ce60b311b50b21cb639a9896317830ce3e625964611a8620e6ab61894dcf06fc56b1b9cdcf185cb3739b4c2e6256a2cf691fc9bf4e6a0cd83a262536ac2af1f8b56c396527621a40dfc62f05fb14e2f982c4c5eb4381aa6177d1f05f1dc670a3a5277516771895a6272739a9d88198c5eb25515ca1161da065c8f314d07ae83109f79a7a90b4809c7cc326256412c1fc9b566b2a4049eed658e3f24d55f2c81cd418f13dc3073544be6d31377c6171fc949dd06b1c46701aab2f9ab260b57c98bc5bb2856060b1083d9a8660d3fc98bdabb1fe588501066d518be6d6551ea4d60639b65ab317cd905aac60d39387447f2ce1896317aa0e473069b9e1d581649d6e3b9a7e293 (by decide +kernel)

private def part33 : Box 0x20048000000000000000000000000000000 0xddf07487109240000000000000000000000 :=
  splitBox 1 101 0xddf07487109240000000000000000000000 part35 part34 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part38 : Box 0x20018200000000000000000000000000000 0xdffe5c1f5023c50c1000000000000000000 :=
  endBox 45 0xd2310f21cace6e9419a522dd2fa98bd073250418ae63a0a03c8bc185d143989c3669f969672ea39da971735aca90172293bd7841cc731527cd6560b832501283930bc9478b7ed3f2f99c35805017c69fcb3b6aea065072d67947680953130691ce671589c357c132ca130cdb4f504e6d996aae6747cb4d66ad9795e447cc913042ce8338e6201e39897fcc5ec0179641cb92e47ca01cd630b7521692f670dfe8078bb65e54a38f76 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part39 : Box 0x20008200000000000000000000000000000 0xdd7d541b102141041000000000000000000 :=
  endBox 139 0xe8390c007c560831dc1fcbe8b6305e504b4950328392ff9cdd402dfc9f7284a065052e539ed69011af96fd04e9f750fa4d6153b4953de8192f2a0a57855143b24d5102f29cc5413356cb3734c5242779788f59aa21736a59c890183ec6e3373a3d62f2c9015e07d2d659cce509522a91c5ce73787163ab365bb8bc3105095f0e6ed5b926ed5b96aab5593ea731473c2b583b9b9da465e539bb30bc179548f1cc564712f4fa21bf48e9cc63718b9e5aa9cdd60642141fcb1062f8e3a737730e1b09e457a731173a9870d9ab68f983cad5522723e5ab6c43582d5944a0c3594a8ac5bab2f944a92583ccb5516ab1035f9012b192ffb56d05262f49a9cdd5c157c8392ffcd5f403c70d39bbe90a3b87c20e63fc9cc4de270d6919038db90bc147d6731afda7ac4149aace61b1a05da62d3d2f9cd4360f8b9dc840bb5960bfb55e0d67ab284b57e584d1814f08b9d89e7312f2944d985e140420e62c41795247314dc72e531eeb4f66a18849a8b9d45739547ba17f93df07d504801da6217391aaa336e1247302d8a63dd2cdc6cb373a91548e841e0a217953415aa786e0254dc723bdaa29f7477cd5172ac8ef6a5966d3ef28fd846a01b2e6ab9f75a96b2327b9b836f871ed23737a7ddaaf166dacea22d467288ead6662b53e160f0df5646d6727b9b8da7b231c2e60c7640e83d5cf53501ac8d1006393dd1ab0a3e0d731017f964ae39611a8ad49ad318f56b2583a8eacdc7348ee2a85275e0a02c1f92462d50dfca3f57142b20a4d5aa3f398b566500830dcaacc1796063a8ce6aba934d8e9478e627f99072731 (by decide +kernel)

private def part37 : Box 0x20008200000000000000000000000000000 0xdd7c541b102141041000000000000000000 :=
  splitBox 1 124 0xdd7c541b102141041000000000000000000 part39 part38 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part42 : Box 0x20208000008000000000000000000000000 0xdf55774b141440048242101040000040000 :=
  endBox 13 0x380fe07c59039bc80d1738fe4e5328ace53208db8621a572845a9e7f337e97d47baaa39067339764c2ed4394232c65abed5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part44 : Box 0x20008080008000000000000000000000000 0xddf45e0f900650c0c042104040400040000 :=
  endBox 55 0x10a390e03e0fa07c58462230b313cdfad673fe9c6cdc386cd5b6aecc2d40c9bf566b30a53fa82d671a869fcb433859bf64a3b56e616b10d21ff5ed31c3ce6e11b9ee282d6a19bfdab691d370bcb1c35ab6be2066492828cd373055012c435081d905abe1b82dd471ab66f102dc8c73f3b08e695a31e37eb515846d4d6afc5e9711ab70798d36d2b24197947a66fd450ddf34ad3da803695c9ed7f1847d167eb5537126b41d4e6ed5b378b28e4585ba4ef725c17136bd0756adb914146881fe616eb56d2173d645ba2dd8e6ef6990329352e4acfd6aa1f1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part46 : Box 0x20008000028000000000000000000000000 0xdd744e9b593440088163100440001540000 :=
  endBox 33 0x1d0721b8661e041ccd5d30b8354bca1cd0f8a50fe0f745cf18bce6f1ff4dc34614c4a2e72ce833d8631cdc3e20cf7f1e07c0f9b0b6c7d23f9620e3741f5ab6b1939ba02669197fcaf341f4e36b4539bb906394bc82899a56b2962397fce6e2e75aac1696958fe5ab6809395be87c1b861739bfce1af8348017941601b28f8b9ce366ef8bcb13b528e839926e2e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part48 : Box 0x20008000008008000000000000000000000 0xdd74569b320740408042148042100040040 :=
  endBox 67 0x1f0721d07f03e2fa3108a2a89fd8e363d3419bb8a3f968a71b64103b317cbca3f962ece55616a0664faa8c47f281d39b8026489a39c5ce3f959fc7cd695a8ac7f270f949a9f5518b0b5ab683d77188387ca3128f9c6d823147d986a18851103ac5d9406aff419b0b5ab61b19246e65829aa0b62e8b9d26f34acbca6fd371ce8320c03f83f1611abf391565227934ead1458b356d2564db722cc21390a09e5881d2ca4d3179c74e6ee459ab670d594ca642870d85ce737620d8f34fc5aae6f363c5016adc72b173a5063e8a9353dee5d6ad89e45bb1834e566d76105cf1cddab7280d852935387b10e4390e5aa9cdcc1a82d387c737551142f9a51e6ae9c3582b239d67e70d9ab2afd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part49 : Box 0x20008000008000000000000000000000000 0xdd74468b120448008042100040000040000 :=
  endBox 119 0x4287317d1c8621a84a17469104682d067cf69395bda6311a90dc190f020360db34d4a3ed35962e3dd781c0491c71b0f89b8e6a7a7d5466d5b4facaf36a7a8cda6b28c60db073406ad80cf8daea2b7b49cad6833da565af0208dd08c0c9478368fe5ab61f128fd06d730b56d1de947737c06b7b49cadb8741e0695c6bf16e9bf43e2f23f8b6285e522ac2582aa4d317846660a9895ecb28c47a6c1534c9c3e6169fcd9c781dc37eb4ae5189c6da9b41cd48ac23394cc0b4889b84fe6ee30851f3e0de31bfd8473da5ab6395a3025e57b6b56c0daf694f0cc0b4779afd147007a66bf926b06d1fc9c6cfe71cde518a915b8701e40f897966a7985d68b34d5a9ed4f9ab66fd70148f282c5ce3f9492c1e672497fcfe6b196adb10a6338737370c467d78de290b6adb4ae59facfe6adc6e13119cad4c450dc385c0a35a29bc4e1b1c2d6aa0a31e9acfe47cc1e568ab099ab670b741b81fccb452779bf4c5e1f17b4cb3f477a8ac7f2882886e338d5b4320e717cd22294749bcc2d8c0c36d6169f35c836147f2d5d85ab61a4636bc1cd47eb57a0da70b9a849bcb57385a4de5416c6a19c5aba4d6463b0cd406e5f17397cd8471b5cbcaf695969eae6119b5d88b0eed876b5761ec5f3695ac01f1600e17209c7f29239822c595aaa4d67b68f2d28eb45 (by decide +kernel)

private def part47 : Box 0x20008000008000000000000000000000000 0xdd74468b120440008042100040000040000 :=
  splitBox 1 87 0xdd74468b120440008042100040000040000 part49 part48 (by decide +kernel)

private def part45 : Box 0x20008000008000000000000000000000000 0xdd74468b100440008042100040000040000 :=
  splitBox 1 101 0xdd74468b100440008042100040000040000 part47 part46 (by decide +kernel)

private def part43 : Box 0x20008000008000000000000000000000000 0xdd74460b100440008042100040000040000 :=
  splitBox 1 115 0xdd74460b100440008042100040000040000 part45 part44 (by decide +kernel)

private def part41 : Box 0x20008000008000000000000000000000000 0xdd54460b100440008042100040000040000 :=
  splitBox 1 129 0xdd54460b100440008042100040000040000 part43 part42 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part52 : Box 0x20018000000000200000000000000000000 0xdf765e5b5483c401000000500c0021000c0 :=
  endBox 55 0x1a46114c3e0e52e21c357850167e5ff91ce6f940497fe838c5ff73283451f311d50124c9500af0ca3a073147ccc1740cb56567e6d98bca819489b5750732cfcbe6b02066414a78e5f902ec4769297cd42b41c43968f9692acb5cc711ecb185c7ba0d14a0c3dd51e9cad283390dcca91d0e69c7505ad6320c4398a0034547b031ded24ed7b8c5e50639b65784a0c82d1ee9796062a31ded313b41a20d5926aa01ff5ed2809a0eed519cc5e194620e6290b9ed21cd41ebda60948025ace80730bb105dd8c5ec237b48f7545317cd42b18341aac024760de8b7669f977505af69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part55 : Box 0x20008804000000200000000000000000000 0xdf5f76c337b044c70211019098002500044 :=
  endBox 67 0x5020457174398aa8d42e0803419c1c62f29bd5ed341c56c710901d4c7e33eca3543871850e1c5e593ef4614fb2b6388483a0b23580f81f4b9066a89f64dc70716b3b9067339f660de5e59a6306f497b4ce2f2a386e2505cdf0ebded2f532f2a35409b3da5ea65e56b292b5ec3231dee25e59d062124483b90672ea074932f698b1f07d35fb90673391ec6f306f6b2c2576a69795c07a8c9f7724b4c49923f9741ccb1bd60dec2f483b57e721b535606a0bca3e9371ce431d489455ee2e7591c251838c2e747c9795c06a07f294185ceb239ed2941012cc2f05da4ad282c41b8d41b8d1bb1bd5066bc287e7b7a4d4166a472f9ce534fbae8ce20cdaa3070c15b23be0db1bd47f28ef6b2b4ce522b53c7f26e3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part56 : Box 0x20008004000000200000000000000000000 0xdf575ec334a044870010019008002500040 :=
  endBox 107 0x6f1c0451803869c6d60741acb3db45cec112ffb1050523f95e05cf2d2d882935284b4c60e5b165545e128f282d48eb2d9a7a5ff4fbace62ecb5762849cc5fc5b190394ac0900fe58b33da518f071d8b2bc231e722a3e5a7ab19173c1c60a2813c8c21cb7b2a3e53c570bfef69902e839597c1cb698872e723942578284c7315f101236f93eee491f4a0a5a67241ce6320f4e528a2c86f181178365cf6d5059f9d632af32849cc56c5520e31f9dee28332f992092f80b707159c809e08ea034fcec2f46aa58a827dd3fb203518e5b37a896ce3f3bda66215467107ac2f9eda5ff837cf6d0e5d071694ac4d25ed259006d5d0e5c1c6419c1cce62bc40883d948e1c7398b201c7732d07d69e82ed48e7d13f3cb195f1540e3c83d4fbb10d441be3f3a3d503a8c79cbaf6947ac615cbb399dcca7e72ecabce838c08a82f0b8142543b251c7e2731920620bca9f78de67e941ea08d60640fd2d338d2b0771fca4064fb97fe5959f0c4398d6af3dc5aca8f558bc9011fccb17837bf8bc349612aa4d5c8ab197b49cc57465188401c1f67b4b9252029f741eb4ce83ebda5abee5d9ccf07d7b4c6061fcb515abf352ded273183bcd5169eb515ed25d9 (by decide +kernel)

private def part54 : Box 0x20008004000000200000000000000000000 0xdf5756c334a044870010019008002500040 :=
  splitBox 1 119 0xdf5756c334a044870010019008002500040 part56 part55 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part57 : Box 0x20008000000000200000000000000000000 0xdd555647148044010000001008002100040 :=
  endBox 113 0x701f40f8bb8c8398d3f8e626ff2f2bda4a265275e1506a2141ee9c6637fb4fc37a81d38db00e5583726c738c93fe6aca48c18ae558ddf1852f2bda4e368c727f9bfe509a89c7ba1259ee2b39627b0a418a70338d93fe28e9c35a4551a827baf0af39ed21bd0638f760db031cdc3e1786b29b8d41739460da6bf3dac1b646acd654fbb95d817291526e7b57a89afdacabc350731122c5e52e49c9d4132354bca6fd062c6fd610e62e578dc683388ce8d5508aa8b2205e2f29afd26a1c36059cc526e72d730e3e5e58e62f618282947730e4f244d0727314f4c3dd811cc5e1f4398bb8833905a5e5728944ca3a6c34f6629b94548a9f51eeb9b417f1b2c7bad418968c29c7ce6ac21bf51bb3dacc4af6b9ed2c83b8a0149d4531bbded2619728c91d37ec18e225918593d2f6b0b788dcc4a94127b9bf4e32aa200e7b49cd630b1f45abe14159182fd283012d8160bf7b4b4f4bca6199ed20bf6212837107a2ad406b97638cbda54227e783ecd259066e22bfda8739b4396719377cf6b59178541ca327f4fa26fd5149c9c9d64ff5007ba5f5947ab2985bad3346eb99d8a6c253a14040eb0f64a0b905ccea3d37ec8c79a6682d3e8cc23612c61505a3dd5c1cc62184306b5062f59fcd2b1eea0f5653314dca2c2539ad07141ea375ccef69551cdb3da4c2e5d998626ef393b495641ee97d51bb3da4e4e81d9aae5d98dfaf69 (by decide +kernel)

private def part53 : Box 0x20008000000000200000000000000000000 0xdd555643148044010000001008002100040 :=
  splitBox 1 110 0xdd555643148044010000001008002100040 part57 part54 (by decide +kernel)

private def part51 : Box 0x20008000000000200000000000000000000 0xdd545643148044010000001008002100040 :=
  splitBox 1 124 0xdd545643148044010000001008002100040 part53 part52 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part60 : Box 0x20018000000000001000000000000000000 0xdf764e4bf8c3c0220080000028000300084 :=
  endBox 11 0x70150740e1e72b60acc454a09cc439aa3d988a3dd062b70a3d986672906ab57e0a1b0c4e627fd6adc1f4e52f220cdcc724ace6281d692b91e463968ce6281d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part62 : Box 0x20009000000000001000000000000000000 0xdfd746cbb8d049220080000008201200084 :=
  endBox 45 0x3b8e03088a1cad306a0e365a38972c0d3988f7419ef6b926ac3d398b0ce606c1dd03b07d312833d693189419ee8280e22b00cf387c5e916b986569f461528270f7914071cc523270f30c97a6614a50564b3dac5ba70f067b28911926a731523cd5927ac08a02d8731791844a0c62f497cc2f85ba6f104db12525eb2b93ee6f137098656c3717c485a0ce50fa91dc8b41b616e98bc9eae51a0e26e1592aa8a03a30a2dd0dba0f5283186540681d6e10671cc419a619837c731495a8fd282a03 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part64 : Box 0x20008100000000001000000000000000000 0xdd757e4bb08c40a30280000008012200084 :=
  endBox 35 0x1f46e16428ec289e1d84ff6adc3dd509b56e1eea0f5ea331756563d338db56d28f13fc7bb232d8ba9476adb809358e62947394a8fe60da82ca12d5b3789cc5cc470e62ce3506f58e3eb6244e8c2b0dd49a1cb60dc9354fecc4f37aad8ba355e8c2b5141561cb3d5c1277b8c6158170734618b9dc8ed579876c336715459128ea138e6ad5b98971c9dab63c5988ad5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part66 : Box 0x20008010000000001000000000000000000 0xdd5d5743b281486a0180200008100220084 :=
  endBox 93 0x102398a037073164188293a4ae27b9cd4c32e578ddf1cd4c32922a80998bfef519cbec49617a4bc3973dc5cbe83d51fb70b2418ce3b86fd39aad8527728cd3d60a985dcdb27f5a56e3b944ac5d695bb8e3b94727036ad93aca3a7a1c0d83728fe30b168d3fab62c562d1a4750661c341ecd458a3a70347147f41cc3866f55d0147351438e8cb91870736a2ac8bc428c42a0b61c9c9d64ff695c2c56afa89630b356df46a0e4f356d07aa2585baa398e4ed5b270c9eb50993fc9ff2a90a3108a20f4ddf2cedc82a3d8c2c91d720b99c36728a5c82e670d9cb51720b99d6a32075385511c3f3cb1d5a89c7ce07185817f357518ed5b3f3cb1d6adb50fa2a8c220f49df1cd5ab6e4173397fdcaf13bcc1b356c9dea0340eb08c42700bb56169f1bd5ab60ad1eea80b4b9abf1856aea89637aac662d1bdc5406d5f39acd5b39ac9ef6af93bd88561848c0cd5b37882b43461b72d1c2dd501b4acbeaa03836f18572bc1b7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part67 : Box 0x20008000000000001000000000000000000 0xdd555753b08040220080000008000200084 :=
  endBox 85 0x3e81f1771bc621a83949cdd06f0b9ce627fd6adc1f46cb1cc5ab6a030e5bc8be17fd7850ec2e7522c1f67b68fe5a969ef0e5af0e63398cd5b8c2c8f96b3a00c512e5f838af0be1424e1b291dab71c3469f025d1f23f95e150650a12c498deac45625c1cc7e27311f8cd5b491fc5d0bfe38b9a4ac4b72dcd458c2ce5b41ea51d8966f594162e769eae88a3283b387a6803411b391819a8ae5f733b0b5862f6f985ac45521708c0cd233feb97cfc0d9a0f408341dcb7ed652dfcc1560ace674fbb48dcca7c23d658b8fe5cc69235162ffb594dcf3dc590581a81fcb38aa0b9c77720f5a9720749de731962ef6f406a8acd333905a967311e1af02e79ab68f9398a483d3925ec33a0e28336717844154398a44d603306da56c5f518b0be62fbd8c2c6f61698b06da631cc5a96935596c6f55ab97fda969013d0dc7289501aa03419c7316919b8d01ac84083f9625c7cd8398b9ce631859abab4f0e5b789824d639893bdab71f35456731580c731 (by decide +kernel)

private def part65 : Box 0x20008000000000001000000000000000000 0xdd555743b08040220080000008000200084 :=
  splitBox 1 112 0xdd555743b08040220080000008000200084 part67 part66 (by decide +kernel)

private def part63 : Box 0x20008000000000001000000000000000000 0xdd555643b08040220080000008000200084 :=
  splitBox 1 116 0xdd555643b08040220080000008000200084 part65 part64 (by decide +kernel)

private def part61 : Box 0x20008000000000001000000000000000000 0xdd554643b08040220080000008000200084 :=
  splitBox 1 120 0xdd554643b08040220080000008000200084 part63 part62 (by decide +kernel)

private def part59 : Box 0x20008000000000001000000000000000000 0xdd544643b08040220080000008000200084 :=
  splitBox 1 124 0xdd544643b08040220080000008000200084 part61 part60 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part69 : Box 0x20018000000000000008000000000000000 0xdf764e4b5197c020110040000014000000c :=
  endBox 55 0x398ae280c41cc5b8661e07b4c9d951e9ca47ba1cd4a1fc1eec1a65a89cad2564a78c5f0714576e81cae527b0c507262f37fc92b928272939ba3e6692a0e5a4621c05411ff3db582a2bb1609cdc39b1ca5ab72cfcc5ed2b7b4a0cde4160c5ff509cf516b38b0588521ab7308c39aa03629a034c5e83d1eea4de317a48e06a985d886114c35fcd5b3949cdd427356c39a4ed839aa02f88f9922681969fa31e60aa0251ff24458866103a1cd8bcaa3d8e6e7f9527bc8a02f88199052d2550acb51404a7be6ad97951feb298e1a2c1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part71 : Box 0x20009000000000000008000000000000000 0xdfd746cb1dd249201100400000041000048 :=
  endBox 83 0xca408a03a07316a1b8691c07901820cd48cca037b4a50549a6958576699624bda52327d14a0dc302fded281d5a5cf6915d9b8c17e942a8b4940ebd8650bc1f5edae41961ae6f5789896586a08d147b4d0717378aed0470718d7f07d39ba0756c586d06f15d98bd25e5bfa0e290730c9c6e5868aec18ed22285bf943e4f536982fce362bb700e3b291d44a62339b97fe416ba08238c4a623488c2e74a39bfdb8611a8701ac520182a4d944af69311a0cd03aaa240662ac1f4c4a6237b49675046b83d6e58eabde578bd6d63b3da504683d7b4c81d312c62330cca3940ebda52832d3cbfe737526b48c22d80cf93d21b916498bce6e8a298dc1c6dccf1b849eb07d067ac4e48093260fa2bb89eb1ff5ccf07d067ba0bc2c0980714fa33d4cffaf6906797249eb291e834833cc327d18c32907067bda615dbf8b618be48e8b9dd0320c4ae558dc21211a6a404ffa6ff8dc29018ffa6bf561a4b244cffa1c557bc2c9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part73 : Box 0x20008100000000000008000000000000000 0xdd75766f119a40a11300400000040010408 :=
  endBox 61 0x3b8fa3990a144ca4ed5b9aba6d537fb8107d91aa1bd489b57646ebda47bace2f10a278c413fcffb1c6d4773045222c4356e4fea44518ec1f40eb50e60fb0a52221bd89fe9628ee7b49c6cdfa7195a8cd29527a065ab7231c9fe71b3fea80e6338731173c91349ba0e5edf41acbcaa016aea8f55050ac1a516093aded3356d47a839591a86add1813e69c0ce5a9e250a136709d6d45926ed2b983e6bf926ef69a0da911579b56c5827038e3eae2806fd8d7e2c127b9cc5646720eb24dcdfa7197d1a86b3cf71416a0ccf4605cc530d1c7b572bcb0983ac1cd84ac551ee82ad0671c0ded23dd51caa8d413dd44b24dce6a0b3944a9373dac6c55a7b0b51aa0c7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part74 : Box 0x20008000000000000008000000000000000 0xdd555743119240201100400000040000008 :=
  endBox 135 0x380b807c5605020c1f4b283f96a2c0b341e8f4d3fa7316705873dc528e7fda30271b451782e4c2e772eb0b506673183ec90740e9c6d046f69903ac15926e7291f88fe4a8661ac621ab69424760fb3dc5256f693fea074bcb31157c47c8df6616870d20270d86faf69362047d185a5e562ea7be591c1f4e1a7319646de1764bff1cdc5cf20f60faa8230e492b0cc9d62c139bbe87cda0fab233f9c1dce52e4d9edaf695a2b56e661bc7d0bca2c141ec8f9284c1ae05da3e641e9cc4bcaaa1afe173acad48ea0995fef63398af1020f4e411a494e62c43787379ed2d5b526bda6173a0747873da4bfe2e76f11471124620786b23903a94138dbb89012d9cc5947ccb23903a71b411b906622c1f669aa0e5ccee417b48b0514480cf69401a08ded3408a03b87316e16c293a386bf8c5ea274a09afe513a4bd44f1afcc328a310d439064a0b06d03a833160cf693f9b06d25ec1b98baf69160a076720c1f5ed22c1491bc4a0a3e67b4ace5cae9ef277a3e6419c6bf7b4a4adb85919c770dfa71971dc62535f985ca26c159dc6adc4eb289c1d646e8e4cd7e70348ea8e6147d106720b56c8c2c7033179ef6699b034c4a71f8bca2c15b1647d0386a25907a91d619c6f56ada8960e66f58582d679ed2f6d46e8b05b8611886712833da417e81d31198bda85618a72374c1a83d7b48f75084e1ab67cd40ea8467b8a8e5abf4615a9b3dc542e83d7b4a935ab68dd9a9ea25612c1c523ad5b0d19bbe6adbda4582d2530bbda6621ed22c183eca030dbb56d49ad25836ed5b (by decide +kernel)

private def part72 : Box 0x20008000000000000008000000000000000 0xdd555643119240201100400000040000008 :=
  splitBox 1 116 0xdd555643119240201100400000040000008 part74 part73 (by decide +kernel)

private def part70 : Box 0x20008000000000000008000000000000000 0xdd554643119240201100400000040000008 :=
  splitBox 1 120 0xdd554643119240201100400000040000008 part72 part71 (by decide +kernel)

private def part68 : Box 0x20008000000000000000000000000000000 0xdd544603108040201000000000000000000 :=
  splitBox 5279 124 0xdd544643119240201100400000040000008 part70 part69 (by decide +kernel)

private def part58 : Box 0x20008000000000000000000000000000000 0xdd544603108040200000000000000000000 :=
  splitBox 1 72 0xdd544603108040200000000000000000000 part68 part59 (by decide +kernel)

private def part50 : Box 0x20008000000000000000000000000000000 0xdd544603108040000000000000000000000 :=
  splitBox 1 81 0xdd544603108040000000000000000000000 part58 part51 (by decide +kernel)

private def part40 : Box 0x20008000000000000000000000000000000 0xdd544603100040000000000000000000000 :=
  splitBox 1 99 0xdd544603100040000000000000000000000 part50 part41 (by decide +kernel)

private def part36 : Box 0x20008000000000000000000000000000000 0xdd544403100040000000000000000000000 :=
  splitBox 1 117 0xdd544403100040000000000000000000000 part40 part37 (by decide +kernel)

private def part32 : Box 0x20008000000000000000000000000000000 0xdd504403100040000000000000000000000 :=
  splitBox 1 126 0xdd504403100040000000000000000000000 part36 part33 (by decide +kernel)

private def part16 : Box 0x20008000000000000000000000000000000 0xdd500403100040000000000000000000000 :=
  splitBox 1 122 0xdd500403100040000000000000000000000 part32 part17 (by decide +kernel)

private def part2 : Box 0x20008000000000000000000000000000000 0xdd500402100040000000000000000000000 :=
  splitBox 1 108 0xdd500402100040000000000000000000000 part16 part3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part78 : Box 0x20a04000000000000000000000000000000 0xdf4fb3f5a61408000000000000000000000 :=
  endBox 51 0x6f1b46a1dc5f01a6b4075d4448059b2d3527e7d39aba2cd5a6b56cf833974dcad677a982b5a6a1c15a6a08d2998ae3e971cb58543ea473620ff3945462a0353e58cb145ed27f9372cc5749fc2cd6adad158c6adc93f1668ae63dabd4c33af77371870569a0cb630fc5f127ece0b360ebb03e69b968dca63c31668b36166cb4d6adad36523bda49c66e35a150801903707d21c19ecaa336adabf6522acfcbb21c949f9b96413ac3e0e08b3564b1725a9e70d5a6b59e7b2a09d6a2d5b681505c19c1f4a4fe48cad345cea45948f24fdab6f69698ce5d6a8a4fded22e75a6b576495976569a2e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part79 : Box 0x20a00000000000000000000000000000000 0xdf4ff155000000000000000000000000000 :=
  endBox 155 0x1003401f16d1887319c550c4ad4188c197353d04682d612c8d1518bdd58aa1d76ada4fc197250aa280ba1835a8597c7f962ab4a507a902c6661f9fe568a93f411ab6c2591a2a47612c8d18c2b53e5a6bda5ab6ba2d0c3d9462d677b296bdab693f41eaa0a47a0e6b2f5189fccdcb07f9612f65023ac0d84ac553e1ed2d5b505c4bf406b53dedb291d65e80d8fb2f777b4b56cc1aaa2e8b446162d7b56d27e8334810266bf965e7f958cc6e5694bb8b0394166e57b4b56cff2b555a6cb4d9606ea350aa2d0d29907282d4199c0c0338c82065abb204c18aa0d96928394a1a52d359a5a3e97209fe6597b15662ac813581c81d0629fe65a28b4527e3e997c6f0c2f282d64a0c95238fa43aed679a4aa33523985d3e703256523c35a2b56d8054167731458aed5b1f4ad0b519ab693f5a6b53e581bda4d7ed5b413ad366adba8ba240a2208e6ad8b3569a93f4a17c40ea481d783ec00d09fb4c5a9ae4162ba925ed328842ab2cfd60ed6757bbda54932bc569ab457b4a08d9c5503af07d981ad5b6a5870e0fb0ebdab6d42d3658cc1f5ab6833056c7f35aac80d49fad355e2aa0ac659fac1cf82b4d5a4982d68b388e63a8da037d680eba08833406cb55505bda671cb56d69a18998aab2f6ada82da52903da66adad3527e4e39ab6d03b0cc3681d557ccd59522b9041922e75aaca21592ad89f99632b451738a261cda8d5ab670d597b30b0f83820c95d073734d568aa35517ac9615ba8c587f315c97ab1d1e3ad345cec8340c0357641982e43aada204e48ead3c18ad33969ad5b751686adcb4d419a075640d1cd5d1e1abde6adad26510e049f9a8d5d1d3c1974f9c1cd677065da52f5d96a2813839cf5b6aea04ce1e6cb4198b2da05b07830b9c3aa72b39bc6065a697643aa71b75120271c8f52ecb08569a93f48cc5db0cf8b3528316758a2b4d (by decide +kernel)

private def part77 : Box 0x20a00000000000000000000000000000000 0xdf4fb155000000000000000000000000000 :=
  splitBox 1 122 0xdf4fb155000000000000000000000000000 part79 part78 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part82 : Box 0x20300000008000000000000000000000000 0xdfcffd41f00400050602101800000040000 :=
  endBox 69 0x731d46f1c0377c8011739cace360df62168661b41eea10f658362d5f640de2b4f9eda83d82965db470de2d5b589c39b272b4fe839a98a099a8a6ef378aa883d9c8f079518ac0e69f9b89e1394786d5b611c9e5400b4ad69f359d002c558b5a2cb385b56e50da8d4ddebe310ca268e0208d69b1ed4596d5b4a39c2e5898b2dab6e41941682d483b50dc06a1c9471738f76271b13e83fa00d416d3f0eacb296ad8f74f6a2e76f1681e0ca21400ad34e1a71b62134589cf756a2a795ab694738eb56e4fc87545ce2e7928e7e17646e72924116b4d2bc8a44727348d69ad572bcad15c0621805b03aa2c5962681337985e65a6a51dbc59ac0814719ca4e1ee638fdab3f411ab0be1c36594a375a7ea214a3a00e47f9c2d46ab3f6aecb4d5a1a56d45272cd3f40eb576 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part84 : Box 0x20300080000000000000000000000000000 0xdfcdf945e68710180040000000000000000 :=
  endBox 59 0x3a8b41f8a230093f671a0700e5b0b3569a1d562163b2505ab6e4539a82fce4f286e272ac1d666d5d9c8ae63162939525ed5b497cd5b701906010671f3437a0bd0eaa90833903a72b8186b0752106720f5eef315569a823162ca4940eb10b4d9ab61c16adc72d5a6b38c02c8b07858a72d39aa38d01c7dcaf0314fc3356d8230005006c0f3f0a51c18a911471853357474e7116adc0c56aecd0320c42cbe1e082e43aab41e0b4d8c0cb2f4a38aa456a5d95a8c2b55a4ca1b6aeb38ac2d02cb492ad361eeacce691a51d69b2445ab61b35a49b96613ce5d6ab86edab6b4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part86 : Box 0x20300000010000000000000000000000000 0xdfcba9c1e088000a1808406000000200000 :=
  endBox 101 0x7e1d45a1d849fad860310e45731b78f41ff61ee9ca507aa81bd63e9bda4e1e7358fa63ef1eecd4350ea0f528f2914e32f4310a42100df91eae4b1ee9ff501ade3da47df1cddabb39753e7208c7df187928ef6938fa8bce1b0fbdbc83cc6ef8c39764e1a0d362106720f5a4b2d359c6f1000ebb1562ecb15d67ec559ed2c574a3c71937acce3803ef8f8e71f0eb834c3af0fbcdcb356deee703694b78b6258ce2b03ef3513f32cbd6aac55967e6e5523cb1d761a0380b4a6394ad5543ea47694c2b5372ca4759f9ed6611b56c7de70138ea0096309e62bb57d48eb2f5aab38913924a2cb897292596c571580d7c7ff053b385d98bb61b34f1c8f5519c61cde66f3940eb4d373a87e3dab48cbb2b4d6f16c531b41f7bb0442d341b6ac1f744c316a565e5bf96a2afd8bb6b2f8fbac235a6875c5972d35c01dad079723b914e6ab4d0679c6683c9cd5e050ec7c76adad341b6b5598aa9015a6875d485c15c39aad8d43814e1b35a8ca47373b99e30ed5b599ce6736cad35ab320f56a3208d48e4b9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part88 : Box 0x20300000000100000000000000000000000 0xdfc9abe5e1a008000a00180840600000000 :=
  endBox 59 0x380f0368ec3380d35105cea359006b4d49fb56d7c581c0bd7a230b3da587a8ff5a6c83387ba5c96ada4fdbc67194065c3ef38c875dab72cbc7deb4240b2f8ffa2cd6ada4fdecb203d66ad5b694cb356ada88b3f82d2b5549f938dab65d99ed2a0d51aa48c9c6bc2f8d5b6f19c489cc5938c8fbd2059fcc29496b13ded2b4f5978f7638d9766491ad349c693f47fcb2951a837d65e93f627c93f06fb68ec3280cf5e03ae93f969ab455a6ce579c723dd50da505abb278dcaa3ef0eba98b4d901ec5961b9c6d69f3db569ace37871983ae3ef441f438c976e6aea4ad282f699a7718749f82f4bb7357527a9415a12832c4cfdad5b49fb56e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part90 : Box 0x20300000000000010000000000000000000 0xdfc9a9e3e5a1002008000a0000001808406 :=
  endBox 55 0x380ec338dc378f02d566ad9f1dc821d10648b9c1a6ca2d80c95a6c2e75a8c3b50ebad356a32be419e3dd49eba82e7401c93f6adad343a271f5a8cd230e8a08e72aad3e0fa72b49e8b3527e3ef173ba8de2a00d336bcb4f06fa0bc59a93f969e0df3dacb2f04fb56cdea93f373c94148387554c400a848165f070505eb45417cb1950d875dab6863a881f671e005ec71f3e3c6e16a1c4e3381c61e50d870548eb555419c5aa87047df2d4415324fd6ab46060578fbd03ece328d5b927e0cb0e0c71f6aec4e359a8705ab693f6f19c47cc7350eb8fbd546abc9412d7b56cdea70340fcd5d7b4a504153356d27e735 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part91 : Box 0x20300000000000000000000000000000000 0xdfc9a9c1e18100010000000000000000000 :=
  endBox 117 0xa82d8882086418a98de20fdc0751e04307de0df069b50e166ad3d27f0b9e0e8c92f173b50e49fa4bc7de1a582d6d5d495a505f46f1d87819c70123b030527e2e7069a80cc24f474b0f7459a5d9054c72759da0f649f82fce4e92f927a2e7994694c8330eba4d649f9cb543ed559c8e90749eb4fe381b0f58761c1393834cd0781022ec356dd46f0e5b03658530744e0671f72bcaf96138745caf290d81e72d681b47501922cb927eb4d961f24fc5961c1370cd3d0a5b9b51dab4d4f1985a6b4071b81821c15d11b70aa5ab671f163ad5660fb57dbc49fcd5b393837ce3f356d27ebc310b558e361d505c87057c166ca0d396a8bd46294749fc8ff069830606cbf0b4240de24fdc0760e37037c1a6ce1cb60eb92c683cacfd9c39ac3ef2c4cf6983cacfcdea92f671ed281f85ce72d056c7035316c671941f7837e0e7ad3563f399cd87b6d185394acd459683369fb57503f338f028be521834ce5aca02e6592875d45f3dd658ca795066d3f6a1b385db9cba0b939abb0e034fe0eab4fe381c4b16e16ab359e0e6c115a7b4ace06d29396b56e40fad3da523ef701d86d07872d343ae0c5069a07e0e2ad343af2d34e4e3ef39ac3ef (by decide +kernel)

private def part89 : Box 0x20300000000000000000000000000000000 0xdfc9a9c1e18100000000000000000000000 :=
  splitBox 1 76 0xdfc9a9c1e18100000000000000000000000 part91 part90 (by decide +kernel)

private def part87 : Box 0x20300000000000000000000000000000000 0xdfc9a9c1e18000000000000000000000000 :=
  splitBox 1 92 0xdfc9a9c1e18000000000000000000000000 part89 part88 (by decide +kernel)

private def part85 : Box 0x20300000000000000000000000000000000 0xdfc9a9c1e08000000000000000000000000 :=
  splitBox 1 100 0xdfc9a9c1e08000000000000000000000000 part87 part86 (by decide +kernel)

private def part83 : Box 0x20300000000000000000000000000000000 0xdfc9a941e08000000000000000000000000 :=
  splitBox 1 115 0xdfc9a941e08000000000000000000000000 part85 part84 (by decide +kernel)

private def part81 : Box 0x20300000000000000000000000000000000 0xdfc9a941e00000000000000000000000000 :=
  splitBox 1 99 0xdfc9a941e00000000000000000000000000 part83 part82 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part94 : Box 0x20281000000000000000000000000000000 0xdf93e3b95cc850200000000000000000000 :=
  endBox 15 0x1747e19428d8706408ad345ba1d344170489b556506bddda9693f408a8267bbb56528ed4b961ae41517b545a4a93549fb68813907a0cb6b10230715422b5151ca0c56a303367b49fc4a4293f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part96 : Box 0x20280400000000000000000000000000000 0xdfd3f333d4a605008000000000000000000 :=
  endBox 73 0x190581805107e2882d0d5b7e1a7f3da4bb29235a68b3527e2c78176b4d5a7cd437b49f25eb280f6519c157c1d30618b3658fa91e3feb52dacabe2a8a498176923506cc215a7bd6d5e6c3995e6f69731a46f17c523cb3516e874d1041ec0cb7b4a085ab6ce24fda9741f5acaf65061832d01f3db561280f89c65dd98aa93f6ad830e49faf8aa34892350fc82f49f874e303356d27ea1b417b5860e9a0bdab720bd27eb42889824fd9c4f9cd51065b52d22693557146334fcb5f18191deb4d6a8a0762d7874d94441b85a6a48e7b4b52c5bad3783a67ff7303a70b75a96c5785bace2a8863da66a5a4d5a97309545ea4562aa8be6b0a925ed33596302a1f6aaa609a338d3b9aa2a2f065a4d5286a1cc5552296be6a1b15ded334a5ccf34a4b5e1d3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part97 : Box 0x20280000000000000000000000000000000 0xdf93f711540000000000000000000000000 :=
  endBox 117 0x410fc390e207c59c621247176549293f283946d7c5e0a43356d24a9476520df2d35202803290aa0d3792027f1480cd37510a42f658fe29ef7318f0d69b1c3594419cb4d28baa0c81fc641f8e267b0b574e1ed43a0fed3749fc7ff6a5a0c5bc601a9713bc7e2517621c4540a4ab40b74e1ee459ed293f690d1876aea3be69b9ca5ed293f531ac39bb59641fb50e71cc61cfc6d619c45517c164c1d3386b4953e69354a3bd9623a8f0d66b0b26386ae093f58188541c43798fc5a7741fd69af6b3e4a48da97141e5a68b75ed2d3f945f248da86e612c8cd3f730b575ed2da388ee378d6036d84671ecb2d3d03e0c30e9aa02dd3e9d07d5a5977507f07d8102b4f40fad347e320fd69af695c1804307e28a2f88834fdc8f357547eb4d721c1575a7a8adabac3b969a2c989c67c97b4ad361e18b25ed274220b4b6b0cf69526b5967bb9724592c557b8c2c959a9f8ded32e0bc138c7e2d5987869250e88f0e48096fc5bace138d88834a08e05ebda6692a0ce0e8ca60fc53841fb156164824d69b01edaca5af7b4b5466a5b4ed8841f8fc5382eecf7158ea93561b1fc563a5dd50bac76711cc771f806dbdde606c61ce6ef691f88b74e1e5250e9c2dd066c3f10ec94861dfcf5d5a89c75a963f1 (by decide +kernel)

private def part95 : Box 0x20280000000000000000000000000000000 0xdf93f311540000000000000000000000000 :=
  splitBox 1 118 0xdf93f311540000000000000000000000000 part97 part96 (by decide +kernel)

private def part93 : Box 0x20280000000000000000000000000000000 0xdf93e311540000000000000000000000000 :=
  splitBox 1 120 0xdf93e311540000000000000000000000000 part95 part94 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part99 : Box 0x20201000000000000000000000000000000 0xdf9ba18908c040200000000000000000000 :=
  endBox 111 0x7e1d4481d849fb88ca35852558102282f599cf696abad24a22625960526cb33288ac0e317ad157028d98964839ff4fe293d9ed2b6140e410a0f63f88715022b62603ff5a2c82127ca90f698ffab4d9ed2d2298b2f968a2bb96060cb0e09b865a89895022ec388b6141ca3682f87fe9078dc21d7312ad870190423ff641a0408871638db16683bb545a62b1938dce415a6b52db41ffae0ca189503b3dd5acf06f0ebc60659da045436c3ba0faa473feac654361d7489cb4d4a3ad8ec388a63b8ca1444e6e60b923a83f1ffad34b3b09e4c165258a22b3b8c5e511640a07208549b0e5c75e62f5307feb13903eb5559dc62f760c4b06996a2b0f5aa949569b358ee2d8b80ffda06d1abf280d69a0cf317aa0a4d969a821418ac3e4a0c83140ead4594305c81d065ac0e61d9b85282e2368ea340f6b91fed5f306ad34c4a0cf44103b2c643aeb4d2748ef60eb9896540dab3d94c022dd408980616eac3da4720f5a7ec59312a045847a16c305ca39317a0f6599ad44c4a83194721b7274cb4d6d1a083eca0b5a2988cc329c250a4d5a8c9fd5a2ad349d27f341e9fce419982e7b4ad35ed3282cc02b51 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part101 : Box 0x20200080000000000000000000000000000 0xdf9df105020610100040000000000000000 :=
  endBox 129 0x761c0821bc0f8b00b459abe409288945d88540a22d01c05ac39bc2dd473cb4f591cf69960693f481a4b2cfda7e93f476c8f96adb3893f3f4ce63204941ded31c0da0591c50d4a094448024096219c7bac1b7515ac1d6925116a1473356d28250328bbd6649fa505472503960eb49711bc6a18828bab0525495c17d497bda5aba2dd733cd5b497bda5abac6356d6a32c651f2d2549fb5666718c28886ee49fb53e58f8d8ac099da012dc5f55a5c8f512da50581f16bd2572d2c4dac633893f6a3ce512fa81947ba507056c9e561e9765ed2d3f905ac43208e0f163f097d5422a39495a50558052c50349797d4dc839ca25166ac75ab692f481abb41cd87e93f671eb316bd81ef776a1acedccf1f85eb2d4356105af599abac557bb97d60e73d6dabaa1763168051c1b749fb4966ad9bbd6768036ae86dda87320d0300a21004812d424fe27c9bf6492b56c786d4f49fa49672b8205c82c577b483154444127ec4356dc83392daba8072faa496597c1ce6aeb045c823c349bcc255948315606ea288b62d35ab693f2ecc719166ace5a9f1cb4bb2e42a89a2508234911061dac1e03dad349933974fe72d3d69af6995ee7f3594caf1903ab455869f8e5a2ad55305a6bd86521b4d4fc24f957bcb2315abb8a61e8b29967ec0200c3f85bae515979fe50328820e5ab317d524ad5985bb07983cc807597ae02dd924a71f381b787f998ab1877bab56d8aee6d82fb24dd8aa93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part104 : Box 0x20200810000000000000000000000000000 0xdf9db3c3a25898444810200000000000000 :=
  endBox 25 0x6f1d8711f4288945d6450169728e52569413d148b353d23b203c733359cf82d21518a0fd48e5af9472c831893f923ac3f4a0a08523b2844a06a4da0e693f281ae04f95a5c11946ea035042f690569bd5547b4b1462ffb944f9b1765d82f3c93f6ad988ca0ea47905a70b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part106 : Box 0x20200800010000000000000000000000000 0xdfdbb1d32258102c0808c04010000200000 :=
  endBox 53 0x1d87e1a86f1e846dd1871d7b52d69a93f28ba8ac3e2e22d05172928036096b94deea7b5166ad34e46adc06f3eca7f4e06e418f6ab42d85d949fb97e5268036729b99569b06d56124281c1b66b29f4e6adb99cbcf293582f34f4bb2d5f28387c527f07c587e5116a19c312c60b38f9c8d5f8c1a6d95a69c0de83d1584098ef660682358aaa1d948ea2b52691a6352c6158122b541e8b1e51ca9356c2748b1e305acee312ad0fc2d893f5a6cd3b1669ffc9f2b83387278c4ab25607cf755a6b03e6ad9c0e6a8ad34c16ce3d00cb91fec5549b832e27cc703 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part107 : Box 0x20200800000000000000000000000000000 0xdf99b1d3035010040000000000000000000 :=
  endBox 121 0x1a0760802de2e8f414456c3d0a2ea17927e3c351faa01f1859a92b8d4ef57407a4fd27f2d343e2a4d969ad5b28bc93f8fb22e70f8941d446f16c5a09f2b1f8bfe2cd407b56d27ece17fe4a3988d6733da548e80f6ad8f0da9efa356d27ef779a96f75271813e0108b3581e083901ed4d49fb56db85f181b24d55e24b131182f5ed3032cbb280f9106f1d87116c6a1472f5394228313819cd4a2ece394641f9bf4a22d602b60f8ad3542281f41f938e5a6b4dd612a11671742d4c81169e92dd6a272d288abc62929c87f39abf071381a7f569af42d01f1163c8113f9a0f46eb241c536d234febd5e6a7bdd40ff2d35aca8130f8b57d0228317e1445b127ed5b9eeab4d407b38d4356e5219f0e26ca78d69b3dd59c6e148468cc0d408b02cdfa719251cb235a6a03e3f1c5816a8a075646b4d381c81f5a6a0fdc45a8c73528392666adb5943e2831761f86f1c46a127f352ce061f128b94956c288b58d6783e2d2b40fa5043473da43e2f578096f7515ab0e43e29631466abb15c3e283f698c5d9927e5076716c5a8c2cf305b50581cd50672bc520ed236abc10e67907ac578b52d6562abda56a2b519a46b62c8e056ad3d282d41c87f38dce8336af808e483960d0665c96a8cd237e1446a127e5af9a9683340ea90deea4f941fcc232718f0da8671a9b3905acec0f40ea90d492e6f80a2d315a7a0cd03a9023466a6b02d8aed5193c6c0b8dea83f (by decide +kernel)

private def part105 : Box 0x20200800000000000000000000000000000 0xdf99b1d3025010040000000000000000000 :=
  splitBox 1 100 0xdf99b1d3025010040000000000000000000 part107 part106 (by decide +kernel)

private def part103 : Box 0x20200800000000000000000000000000000 0xdf99b1c3025010040000000000000000000 :=
  splitBox 1 112 0xdf99b1c3025010040000000000000000000 part105 part104 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part110 : Box 0x20200018000000000000000000000000000 0xdfd9bba5c00aca5050003c0000000000000 :=
  endBox 41 0x3f0c6288b224fd78671ab64fd801af692f99ff528271939aa7037d96263dd2ec8afe418b4fcfdad437b4a50671d982ce32735510cf6969fb56d706710431cd5e86aecc257b49c0cc1a8219a7f188cc16f69621e86adca316ae98347baa83575ecb2875a7ea474a0cd5b7b4b4fe5c164640e067354a0c83141fb50e7b4b99c14ed2590627036acbd09e3e860b485cd437b4a87507a58d9cbb187589c1b565ed5b4a0cd5b311be8f69485cd5b49eac4e1d2823dab6d5d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part112 : Box 0x20200010008000000000000000000000000 0xdf9fbfc9900c8c444202301100080040000 :=
  endBox 43 0x651a86018827c945db850190306c1fe73086d5c8b41fd422e4350eb90e50882954623dd7b6c6f1518d07f6a1b10e22e05256405baf5b857ed5b400a4bc57f3575283356d48ef695a1b84407ba57b925ed297b49bc5abac5f6accf77497c1ce7b2b99d462801925ee67306b5754633575e8621b8501c9e1518b53c5ba60d500fe7353dabeb234959446699bdb53c699a8c4d4f34ad466617400c7b535abda6378b10e227e66adbda525e62328d817e49e86c525e62f400b4862eca87548ad43 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part113 : Box 0x20200010000000000000000000000000000 0xdf99bb89808888404000200000000000000 :=
  endBox 121 0x64081e96298b82a0ca20bd07eec27093f9472c278a2e90b7b4acbe7b4b15d27eb2f8e06f6962bb0850c4e103edc3408e1834b5f2cd4e06f779186d5d2d7b4cd69ea2549fce3b4a0b56d69eb4b9a8ab2f927edc2b0fa3502dd4a0cc537b49c0c3473095422b3f695b4ce49f8b15f8695c51749f9c0e7b4c1fe35fac8ca2e881f8d5b331683f6c2c757ebda501eb2f49fb007a315ded3203d456b3f407c90b51ca91d48f3da5a530738f9a7fd597a4fdb451cc90b4f0c80f378a1891d597a4fcf9b398ded2d5d8c2ad3e0e71f34962f6951120440dc7e1ab6c578e06a2527ca4fd47f0b1d84e82127cc51749f9c0d042941927e4f99a7ea828c6522b14c5ba60d4108b76306b88ca3685177d20db356ce069415c15015f9c0d40720c5ed3169d10508c4b983cbd860dad5b7b4cb4f50196fe6ada0c4e06da3e890b8c1a9413f17049fb92e8c39ad5c8f1853069c0d1872cd4d6ad3f731bda65899834f9ad5b418b4fe731ac34c021496ada085a8724fcc1a92f4a0a08544481f84b127e7039ab69e53ffb9b58ae51759f96bc90f2874a2ea395c12c381b40b552d797d67b498358af2cbda06520f3098630a5bf16e85467bbabf5ed318702cb57e6adbda630ed03da630b0a4e0f2f7750ea91cffb356d47320f4a06d432d7a40a83da52c531872c5728bd07959f9c0e83c983683c8625812d29823ae451eec1fd3d251737abd0a01b06f5802ed3f607893cafad5d11bcc0f62a85dcafa7ff37ac83d72ece67 (by decide +kernel)

private def part111 : Box 0x20200010000000000000000000000000000 0xdf99bb89800888404000200000000000000 :=
  splitBox 1 99 0xdf99bb89800888404000200000000000000 part113 part112 (by decide +kernel)

private def part109 : Box 0x20200010000000000000000000000000000 0xdf99bb81800888404000200000000000000 :=
  splitBox 1 111 0xdf99bb81800888404000200000000000000 part111 part110 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part114 : Box 0x20200000000000000000000000000000000 0xdf99b991000000000000000000000000000 :=
  endBox 109 0x6f1c820c907df84b0bb20e10f89f87f19acac57508ca393059fc5a87182d845b1d462aca173f9a04cc160db4416a32d14c16a4d5a682662d4ad1542e60b838cb4d62b8d556a20db5a2836e7e1a8512303359434660b49f940d848214232c4ca2eb2f173a8463fbbda58ae701381cf699abeb2f380ad365a2b00d03f04117218c6e19c0f8ad363059c65cdb2ca569ace3a8e224fc1c32d3545eb4d9a968617666919b9d85ec472ff8e767339765ec33da4ffa83d49fb575cc73064bb25076ae9fa43e2b824fdc4480ca2f3969bd569b352d1eb398cc2ef695c19c750c2f2404c32a1d4019c44e6ada04ee5998aa630eb555a89895a96617300cd5d3f4b28ea0b75a873584fd283d3f4cd5d6a1ca1d6a5b38bc185d43b3d6d0067e95239fa64fbb50d07af77a30ec3d6aec1f4fba83d7e1d43f1e849fb901219ed25c16af9bcc1c21f167124173b52e283bda5aa2b4d9ccf34f4deac596aeb38a21969aa49173a0465a6bd083181c21f1671ab72cbd69a71f173941cf6b20c569ab007c5aaf2d34a0e5d99a46b62f0ce182e173ac8923909416515841e829e6aeb56daa25bfa0ff0915aba025243b594fba8f59eb6d5d5a6c92b69fcc296aea0ce47ab50dcaed5d4a0982da4720ce3032cddab70736ae87c482293f (by decide +kernel)

private def part108 : Box 0x20200000000000000000000000000000000 0xdf99b981000000000000000000000000000 :=
  splitBox 1 112 0xdf99b981000000000000000000000000000 part114 part109 (by decide +kernel)

private def part102 : Box 0x20200000000000000000000000000000000 0xdf99b181000000000000000000000000000 :=
  splitBox 1 119 0xdf99b181000000000000000000000000000 part108 part103 (by decide +kernel)

private def part100 : Box 0x20200000000000000000000000000000000 0xdf99b101000000000000000000000000000 :=
  splitBox 1 115 0xdf99b101000000000000000000000000000 part102 part101 (by decide +kernel)

private def part98 : Box 0x20200000000000000000000000000000000 0xdf99a101000000000000000000000000000 :=
  splitBox 1 120 0xdf99a101000000000000000000000000000 part100 part99 (by decide +kernel)

private def part92 : Box 0x20200000000000000000000000000000000 0xdf91a101000000000000000000000000000 :=
  splitBox 1 127 0xdf91a101000000000000000000000000000 part98 part93 (by decide +kernel)

private def part80 : Box 0x20200000000000000000000000000000000 0xdf81a101000000000000000000000000000 :=
  splitBox 1 128 0xdf81a101000000000000000000000000000 part92 part81 (by decide +kernel)

private def part76 : Box 0x20200000000000000000000000000000000 0xdf01a101000000000000000000000000000 :=
  splitBox 1 131 0xdf01a101000000000000000000000000000 part80 part77 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part118 : Box 0x200c0001000000000000000000000000000 0xdff2e2b40f8060a84018000200000000000 :=
  endBox 99 0x1c8882f8b4d680c8721226aa251e7b4a0f4a27351e7b49775a961a7771f078174289a281a76adcf692bfad2cdaa0b19ed341ddc8ad314edbd9cdaa937578cf6941ea4dc9ea8a069e0fb251d04707d928ef69505cb514ed8ebd4629475d18855034f20f51440eb4c6513b56c4e6b4b2ef82be69ba89e2dfa93d692d5b9a629db7b38b255e2ee3908eb9ab683d06d944d385412083bcb1f69b8615ed2089047b4c66adb544fdea3b7b3c2c9698a76d49e2b79acad5b7b4977d7445107b2cecfe6b099a6ec3b3f7a3ad07aaf99b46f15c6b1140e1874daa32cb5ed23d349acb1d7b4a28a3d8bbe3d328ac0af7b48f4e416874d65b028ded2b571e9b10bc30a658e942c166e419aa2b0d59c942d61f3e0ee340aa149d342859b564fabd85666b3b7229e0b358daad65331ab717760ea9f53f7977683aa7d53858ecd4b6a3b58560586cd5158eb905c8b27d416eb0d599cd5b41e836ca2ab62e8a026009d41ecb4f58e86a5a4320b5a632c75272b09500fdb2c2566ab1d948eb49584b50af3963a82d2eec9f55a4bd8d48eda3101d37b7d07d51382bd03a83d527c3d359dc0b5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part119 : Box 0x20040001000000000000000000000000000 0xddaaa2a4088040284008000200000000000 :=
  endBox 151 0xf83b8d6379003c0407881ed22f81e77407fe662336592abfded26012efabce7b497258b2601505cf6d36aad452c370cf6957cabccc02b4d2efac96837acd5cc2c19300af8d40ffcffb3da453aaff1dead356aee57928e6016d16c587c4e15919b85ed2b09305b287d3967683d736c35127ab09477a6d58fdec31736ad35e00efb20e0142d805a6ac8e458dfa73509bc399690c1c4e3e1a936a9b56388ca6391e731a4d47ded618332a4559dc1e4e6a5df816e9351f7ad35e064170285b68735401c71f293a70d5b93b306f5a6a7d4e3f075969a1456ada7660de3d38e32d5b2938f4e72398bd3eec475a0ad5ca3a7354212c3c1a0151af0b22f84f56b2c0a1522b5968c2b97569abe2be63f7a9156ae83d969a623a0e29f7300acb62ed8b9da05e0c032d3505aa33047c8d15a6ad464f1b94473e58b047a0f5e87b4b28601a30ae413f6acb569a82d4fac58550e82be5a0b6858b7b4af0f413d55f318656af2d3569b461cc32e518dc2b4d725b90f0320d22e0515293ac763f1c1cd01a72759988c6591a05a6c513599c9db1739c6569a8199072b4d06da00e39a836ca3aaa2b082327acf694a3988e7b4c7fd5a6af8c0355e837c1d5ed218d1648b9d69a7273fba0e4a030a15ed2f698e4e2e7404982d69ad43c0ec1c7ce5ab4d9686b4d9466da3d09a1896317a08d07a6258c5e82d5a1c1c3173ad367a16c36acd5b733a51cfde6015a6985d8848acd5b2faad34c4abe46164f1ad3548ae579ab70ebd69aa336b1b45b03ced318fee62f6adad34c16d5b806e81d312ab0c42b8a00fdd50300ad060d6ac9616e9f05df96aef6996025df591677390cc02d5116ead0e36aabe4fda3bd592d079982ee675a88fdda05b1aa3293d03283930b98bd03320e4c4ab1d907ab49 (by decide +kernel)

private def part117 : Box 0x20040001000000000000000000000000000 0xdda2a2a4088040284008000200000000000 :=
  splitBox 1 127 0xdda2a2a4088040284008000200000000000 part119 part118 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part121 : Box 0x20044000000000000000000000000000000 0xdde9a685848888000000000000000000000 :=
  endBox 89 0x1dc6f2007407fec8107d70381c821418be8f69597c527475a4ad87328ed62eb439aaaa397b49c0d907d1a45d0a02d5b984ee632efbd6ca2ad436adca3d6d1abb2d34a26a3b8c2c7f95a6a8e5abb284565ab4d51c93ac58eba300f699cc6d5d5968b1d7883ac9eb5a6b91c7a6d5b512cb4d526a7ad48480a3b1c0dee219d0c6b54604b9f7e6adb883ef5503ce3b58a0293339ab202c759dce4b6a3972524e8217b4cb4d694942e47ea4e57053178418a0fdc08005ce0b98e6ab4305cc0b98a16d5939ace03402e78e5a5014109045cdb145562a92b4109c7ca0339b4e3ee03c0bc3e8d5b2088b9d6af41acb929415a0cc1f8bceb4149e904562b203c5cef697d1ed2d224f5ab32d5ca025e79abab439abac83c0ce10043672d44e6a92b9042d5b418a20d220c584417c2e70dbac5e066a0bd69b28fd05f0b9da83e1e05a0b38b438e5a9630e66a8ad0d272a4736acd5b1e9b52c19b2d35686c2f969ad313ffbda565a1c3396a8ce15da91cffe2c7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part124 : Box 0x20041000020000000000000000000000000 0xdffae8c548d208614025002080001000000 :=
  endBox 65 0x6b1bc5f1d01fbb40b83681e795e6af94089804c4aa02a8601694c1c52efac05246d5d7b4abe56865c9919b3da4fda9f72efabe5656d22a81e74b1656d299852a4758cacbd877236c77a6b596571ff5c458ec4e90f38d2683bacada06d1507509eab1d89d2d59370b50d5feb2b14bc2b56acce6d466879dabb0d852026d55a8977e0f3ac75666b82d8da20845cf2c2519a62f0f38716733bda5612e6d966661957ca044c84f4c9417b4a3358a61e73fead86e191a2af17b0982d2566237115e327a43ce9e98462c3b5c1a0441d4300a0854673da548ae3b370ad0cc5f2875abab438c5e8218c16b1d599ad5e7b4982cc46ac2a8af19ed24f5274a91d26e9475c037b34dcc022e78fae7fd7b4b68c2391e578985ded262f71dcd5d5a8bda60ef2c95ec269f3f8b91ded2b51 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part126 : Box 0x20050000020000000000000000000000000 0xdfbaf88d40ba00054421002800001000000 :=
  endBox 65 0x1ac6715c6907eeea2a0cc228e0249d272d0356e596b574fd28370f3d07d8d4ed297b4c1e561e1e7596c8275a8b56daa21e769fcb410f3977e300abe43cea04108394f5ca4f59f989669ea45649cac0e2356e2748e464f4b0e66119894db2e49629b56dc4751b4475c91346aa84dacaa3d06b879cec5a0caf958037b3565032d3f965ad655b07172be58a66d9161b544c168198db2d5b6a8aa8d655b1846d2d9cbeb0f30bbdbe40c869669fb97dc857122b249d585916ab069547ad515abc0d73fcc0d76aec60d6710040cc829571c87b4a0e4d6b073564ab3b493b15e56126b35452269d989d2b51694b9069f839ae633069fe522ad3f98aad65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part127 : Box 0x20040000020000000000000000000000000 0xddb9f885409000014021002000001000000 :=
  endBox 95 0x3a0d6378e4103c83efa368c81475ed31c0ca2a9c1ff64f19c0d2c0b9c0274f1ac06149809e30b177ca169154e12c381aa0b2f6adcb4f3ffac5ded2d3b4f5c9ed9206e613e6abf549ea81f906f89d6f69604acb56aec57408cc09694c7ab6aebda5cceb016adbda66299ffce0660d64110701042b21045f446dc60b49ea505ea73164e32d3fa0ea5c96ad8b9d9c85165b1404bfef69311949e46fa93e3e6bd4da76b2f6ad945583f2bc5aca9ff305a50565a411280ba8ce2e09f7943ad4b3969cd578851a0305b59628e988d65b395d1db237c9d6e678c16b57721786d1a083fd075092bda5ca24eb596a874e44f1cf59381acb5cdad3191ea1815abacb428b399e12abdbded28f55ab98367b09ffdac2b2d67110317982c52b357563af71736b4c65e1f456143af71a0fef6f597b52dcdb23d60ff3095cda7e91b8cd4347aaf041120cbda63f49a7daba62328eb59646f988d9c698cb0769ba4d5072407641f47acca3d7ad945544ed43280b6896289d746a1cf6948aa4e4f573da5206f6f51eacd651e9fe648abe8e03d8e015b4c5876a477b7b545a07b4cc23596b945a86a1d5229c0e0a1c61e0448abd872c57 (by decide +kernel)

private def part125 : Box 0x20040000020000000000000000000000000 0xddb8f885409000014021002000001000000 :=
  splitBox 1 124 0xddb8f885409000014021002000001000000 part127 part126 (by decide +kernel)

private def part123 : Box 0x20040000020000000000000000000000000 0xddb8e885409000014021002000001000000 :=
  splitBox 1 120 0xddb8e885409000014021002000001000000 part125 part124 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part130 : Box 0x20040010000400000000000000000000000 0xdde8ee858ac02a410884208408800200008 :=
  endBox 41 0x378be2d8e20fbc7ee8f18e6a50b9f4691c416ecb0f58a9cd43cef02d0c0f8a16c0f93ef2044bbed4395e207acac9d3103cd3b2854566c0962bb95c80ef038840f6a122b1cd4dfb203d04324e5842c577116015dce6d8c3879c9d26239062b1f501a04641ea20c83c0fa1c64e6b1878a4ee3b49ec61e58ab8ecc46da461e71d986527a831964a811260cd432c5988d682b57305cb417b4ad5ca02735 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part132 : Box 0x20040000000440000000000000000000000 0xdda0e79502c92600008c048484808000008 :=
  endBox 79 0x2007c1ac5b12c531903ff8ffe2ef900505ed0107e61e8afc5ba703823e73571dad5ddc7f1e064083ed5d9cda82149e90445bb461d87718050423ff7117416ea086409a934796b15949ae4b9042da33860b8dc262f46fc813396c82158aa845fc771a0208c2dd6710432c54e6a3ff6a1c11f495b38813988e72d306cb4f410b4c5ec32c1d0262dd681907f1cdb2c3d022625200b0ee62ab92d6822dd396c60d781a8490da73dad60eb155a0bf881158bce6d369d187838b0de408b03d6af302d022d0320c01f8e61ea7fded23f1200ac76293a8fd42e411526c419306a50641fce839a04d63ac3d62aad89c28ae51fb0ee06dacce61d83659c39acb1d1e9d18708fbda5a62e2074e06b8b75fc5b1acb2c54f9e62f4a0b4c64ff989562ab4161dcd590e9c0d9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part134 : Box 0x20040000000400080000000000000000000 0xdda0e597428061004094018400900210028 :=
  endBox 91 0x781dc801fc7c1bc75083241f35acc5783e94541b3187987651547ec1f4fbaa17515b20d21045d428abdc68399c660e32855cda82f8c39fc6381c1bdd47a8cd478399cd51bec531dd8f4d6aed0461dacb27dcc1a9e398aad316b1c436ac3f706ba8567b3a505a7e3f75abb00e434070208e40ca08e414b1081d907ab51a0ee60d98a2e63311c7e3411b78e43e03f18fe252706db58d259406d3f5ab835d2c41ecc51401d07d3e4ae0a6358d4b8daac515aba0fd806accc511f89f8e5a5a7be6b08fc5a97303da8ec51060977c7e341bca025158a4e0d971190750803073966aa3f5089c0ce6ad63e9187942e7dd584b9b584ec5741fa4ad07f461e5a8a8ad9c560e5a5618953c734c58aaf6b612cb518c3ca393179eae01480d4fb2237478a89581e81196ae401801fc6f16c5c07eed020c650198bd07b2d4540692b311c91d0f3b400c196561e7312a0f675105b1865022b57154cde13a6067bda640e8b7506725041821e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part136 : Box 0x20040000000400000100000000000000000 0xdda0f49522a86028208c008460800000408 :=
  endBox 127 0x801bc7f1f0771d07d083241f4f7cd313fba7ac1b651506cca2b671c8203b20e47963a8392859455b45513d730ed046ae20a64f5accda7e927692cd259c8e8398be6fa2905015d1b46aeb98e8c2a0f5a530794f5b0ecff334a60f2641b56836b545a471f7c7a7391cdaa7f93c11e31b9d87e9038c3c69d501b4a59c5b1902f99cb4c16c279206b35063b09e4f1c61da8710e4396b4f68c2b55c18ec55373a40e4a2989587f13dc803303cf061fc60d27ba3c5206ea303e5ab8f4cf4140c09535fb1554563ab47ac7ab373a5159c6b1c45b03cec80fdc9db182d1aa0c769fc9eb6b2a026413ad8d3781828c369f97cc7eeae2bfe41ba51581ed3f944ea3d570c17461d44f0693fba0e56a32065c875162b34a56820d7419ba09423d5877293da62a2b83eb15547727ad87735758773574c1b04390da2b85154b1ac163977d6af074d44f28ec7a728f5ab3289d47ac0142d5c1f8c6d5694a49daa3391d8832c74daaaa177d404ffca3b6aead5ca02d23981ee410e98fc64ffa93daba3bf981e6c741f874cbbec824f62d48f4c8024ed280b58da2d8ea2e8b415ab8f2e1e9a3d67b7b91cc2e8f58b6f187131cc3b4fbc61d68257b8fd235783bb57630eb577b3cc53396c1f4c16e23687279c8e7f328a873c1b2a62b89c0fbdaab0b1dcc2f69481826491b315cf56b337b4b984a16e474b1c8ed618f56b1f61ba07ce6b003d5f306b7b4c90339ab58d4728594560f32c7507ec579edeb1d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part138 : Box 0x20050000000400000000200000000000000 0xdfb2ec9f62aa7108019c018400a44100008 :=
  endBox 41 0x1c46b19c312c8271fb874dc87411eb0b741aeb620cd38698ca3b6a1b98d49ae638346d23924ec258f9ed5d16ea28e4310aa2d883351dcc0b694b98dea65f351fb0fe493a7081d9a4a927526a0764f5c1bd386aec1de692a0e584e9454f7cb491cba7fe51db40819907260ba0faf03f8a03a04ed5b107b3155a965f34a0b4a66a8cc3b692a89d06ed2961fcc5158a8fdd273289d49eb57698cf6b62a8ad47eeb57 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part139 : Box 0x20040000000400000000200000000000000 0xdda1e49522a061080184018400840100008 :=
  endBox 131 0x1e0772007f1d0681ac2049065ecf30bc58b1875abb14e6ae985dbc64083efa41c628aa8fe526c9eb01480bcfee0d9641f4750a2a35795e2a3b527a0cd20f284d476ce284e3ffa8ece32b17a0de83f750e330f4d6ae18fa30ed63904077d0c0285b00a398ff2b578c3c80d7b7800da52e476a8c9eb6a1a03584eea3db6604ac5d822b355a7ad5d84b398d28ac275a7b4a6698b0eca02aa3685014f5cc3b41eb496723b50e393a0e5d04c0f0527d06f3f8a045b46f14c06da0fe1e9c1bc3a71f8d612b4b1f8a0ce1e5949c357142e0de5158a4f04368501586c0c36a1949d61b2ce561b2ce5c46d1f406cb98e38c879c7a65270e7cc0350e81c2ce6ab338daa7ed259a49e36ac1be6b09f7dcc26fd36ac3c19023071285949d90741f4200b58b6309e39ab15cc1682f495b50ce2c1e41ea044e6a83d9022d23981ea3f96a30712d493dcb5341bd05eea0646836a515a42b355a7ad5c9ee72d3c147f0ea49eec57610a4e547f2515d4512c94539aad5dbc5b128b28e549ac259ee30a0630ede3f8ee2f8b63d96416a4643ce3ef1ffb68ea0306595879c56b1895d016ec8115a8cc595c1b4408989657c879d07f41c564a367a30a623483a0f43cee82d8da24ae0dbac7547e62f512cb1d51ca0f65a8ac74c02a3f856ab15274a0465a8874dd46d0d7f1894c46af1409a0cd601bbc6018c3ad45cc30aa6 (by decide +kernel)

private def part137 : Box 0x20040000000400000000000000000000000 0xdda0e495028060080184008400800000008 :=
  splitBox 5542 124 0xdda0e49522a061080184018400840100008 part139 part138 (by decide +kernel)

private def part135 : Box 0x20040000000400000000000000000000000 0xdda0e495028060080084008400800000008 :=
  splitBox 1 68 0xdda0e495028060080084008400800000008 part137 part136 (by decide +kernel)

private def part133 : Box 0x20040000000400000000000000000000000 0xdda0e495028060000084008400800000008 :=
  splitBox 1 79 0xdda0e495028060000084008400800000008 part135 part134 (by decide +kernel)

private def part131 : Box 0x20040000000400000000000000000000000 0xdda0e495028020000084008400800000008 :=
  splitBox 1 90 0xdda0e495028020000084008400800000008 part133 part132 (by decide +kernel)

private def part129 : Box 0x20040000000400000000000000000000000 0xdda0e485028020000084008400800000008 :=
  splitBox 1 112 0xdda0e485028020000084008400800000008 part131 part130 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part142 : Box 0x20050000000008000000000000000000000 0xdfb2fcdd42af00400001105002100280000 :=
  endBox 101 0x1ac751c47416406ba202dd3a163b41cdab64e9508ad35472e4791c66d92dfac74172b0f6adb38d2d9c8e91105cac94ff334a60daa2b4416a30e05ab29fd51cb4ee5a1c10c42b0833491407356d6823bd69bc1ce0de9fb54726d56ada20b1d9a76b17723a84569ae47900724d5ab2d5d5a6c6d56ad93a43a67e3105e300d65741fc820c4a94207641ea3ae599abe506691d9406c53305b56dccf07358a61bd8726b4d419b90e4a0ad45ab662f741b45b0c1ab519a6e94182184741cd03ab579ab6b2d8f9ed375a18734c02d59969ab5705c9fb542b2cb5abad656218082039a833903ab07987a90f305cc5349ea3ad69b23aded65c310b4d6819c740172b139c8e3bd59f9b545ba62536ac9234eccd653fc8b759c485cd29500b02d5f290f5a8a43e6a2a80cc1735955f2c43a0ce20665158b74c5e9419ab660116e9e86d99a6e6d5515a80e086afc1bd4759f7455b34fcd7ed6551cacee4f7985d5f2d0300c43a0ac0735abb2c95acae4730098355fb1fb564ad2941ea85e515ad45a529350589fe5abb20659c460fbb2d34c02d594a3ad45067350d28eb1d401d06d51faa8ce228b5136cca013f193b5a7e8338c3ca2941e91b661ea31d69a833473c6b52d48695acab13 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part144 : Box 0x200c0000000008000000000000000000000 0xddb3f2d5878500400005001802100600000 :=
  endBox 41 0x741504c11077102282169ec51506db56ca261d19c926d369ead35b4681acb0fc4a4ece2c0e5d8a2ad655a8b59635fcc5913cc1cda62813285b574b7f3545c8ed2141f8745a077208289c3f1293836e0e8a0be6adabe43a23f1580a2b2d35066b335a8bb8de1a8e514a3ad05e0db51ec7ab969ad31963a3d3066ad341b6ee340da29364f7ad35a620c7293ac0ac3546285b91d4721bd36acb0d50f942e363ac765a6945437b289569a4f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part145 : Box 0x20040000000008000000000000000000000 0xdda9f0d5028500400001001002100200000 :=
  endBox 151 0x1003a0ee378fa106483ece1d8ec2d45a406db4963f9a3f5846d3128a9726583ad363f8a3ad68ab078c3d07162ab4dda6251506dac1d68698c69f2d4a85c0ea02f35aa074a2a7f3a0e60db67190393ad168c3ad3521eb39173ad36487ace635aad15a06d08231878dce4e13179834a3aea2d3683fabf5ab6727300acb5abb1fa5ab67cd523b20ce2d873585ce5159ab6a156989c7df4381d187839a4ada8681328aa046391d46adce57596ad5da7a70339aa21187965ed3159bb56dcaee6d670f572d444c316a47a70615ab6b435ab9cd590750802fa350c21cd56c8c3cb07417ad5cc165e2d46419b56daca7c3a30e90f583ad5d6a323e5ab68115a09ef20456a2b4d62ac60b4879bf4e6b2d36173b50ea18be6adad4568671f39ab689e1b9e612a48cc16b4d56145723b446aa39373c61da623bd3129ad63e6ad45cae62f274c9115a6b409a2c9649ba8e6523ad34c026fd969ab51821dc6d19c28997ce16aac1c80eea1455a7b2d3503ad5f9aa2b4d671542039cd6723a91d64a935285b5468c3b91c16ab1d58180440ff30738726d5d590b56d541bdce475058dae723b4a55469dc6e76a8942c4830d256961318c3b50cdab320b4d39a8ade8c3b4f418e4f7488cd3d39acb4d203be8d02f851d55126b142d10741ac4d10230b2cfbb2c4ded7009cddeb4558eac4c7827278daab4d6019005cc1bd36a87446d7012d666e45165b91cd472c4dc8eaf996067f1408ad356039acc3b4739c4507ab335a8ba890f967e1e73d5cd5b28aac4d67eea2a8da1cd4e3f0b9ce3f0744e4f07441b288320b4d680f9b2cbc3a23c103bcd5d34fa0bd402d61d8d5b4212266e782da90f8c3ce513ff9b9c58b2cbe2beac4d8aac8308e05a8b9d7455121e7ff95fa04559f976e0f313ad5fac23858ab45 (by decide +kernel)

private def part143 : Box 0x20040000000008000000000000000000000 0xdda1f0d5028500400001001002100200000 :=
  splitBox 1 127 0xdda1f0d5028500400001001002100200000 part145 part144 (by decide +kernel)

private def part141 : Box 0x20040000000008000000000000000000000 0xdda0f0d5028500400001001002100200000 :=
  splitBox 1 124 0xdda0f0d5028500400001001002100200000 part143 part142 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part147 : Box 0x200c0000000000100000000000000000000 0xddb2e39daf840a0080000a0000600840180 :=
  endBox 57 0x721c46d1e0771f006ba0be6ad9454a4e1d3974681500658b06407a0fd3ead5b523a4e56c40fcd5b7b4870ded334de0d6d5b541667356c3869334a28f4e6adad4560f07441972d34bbeb337b4874df058ec3f141fa51605c9f898300d313309c5d18ae8a2d36838b56d81e9396adcc0f720accd60e921523cb336b2ad35023355dacab4d490a8e66ad9a9c18293961c97265a8bdbded681141fa91daca5158a4ec3f601a07c14232895272a471f89f3e34dbdad2429457a88305ab7240d69a50b974711440e9b5966138fc5612a2541fb56d1ff3db561281f061be0d31440593356d042c020fc7e3315c53f0b25456f6b161cd318186d5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part148 : Box 0x20040000000000100000000000000000000 0xdda8e08d8a840a008000020000400840080 :=
  endBox 105 0x3b8be2d8fa0fbc7eef01c2e62ba4d4a1651d055c2e7478c71f173c00f03484076d1c4312c817063879d3ff41bd62a0bf49ca45649cba8da18965a6acb53fab07274a04c9d32cb58a2b4d9d4691c43f03cea45962a5df3f0ca318c2c1c56060b905fc2bb595ad0e0d713a5022b1569126b2c0cc4ab5505c9896408ad35b4781a828e8ef672bbda4e320bf37ec9370f3c4f505fabce36a82e4a170036840f711d45b03cec220ce41ead44c46a428e6417ac2505b06f96a24e98fe6b62d4631798966109eb3d9d5e282341e988cc4a1c5964a4f5408a98a83d962ef9b5502283f587caf39022b4d8c2a8fd676fa368e2149c1932d345ce1e7060c2e7597aa0783d8e408a085e041fb95e4a2b56cdab2be67b4ac0cdfb2bf4e320d9711d4591a0396aa040149acc3f1639eae698ad34e44416a2933728c1c3736b4f67b4a78cc16b51858e94561ccc5738f9005a07410c200b0fe49ca8c5222a8291e49ca82e30bb4c5a4661906adc6d50639b565a6b0e58ae939515c6e7990305cb4d5a88b9d63b166d6a21bf61fc401 (by decide +kernel)

private def part146 : Box 0x20040000000000000000000000000000000 0xdda0e085028408000000000000000000000 :=
  splitBox 5016 127 0xdda0e08d8a840a008000020000400840080 part148 part147 (by decide +kernel)

private def part140 : Box 0x20040000000000000000000000000000000 0xdda0e085028400000000000000000000000 :=
  splitBox 1 87 0xdda0e085028400000000000000000000000 part146 part141 (by decide +kernel)

private def part128 : Box 0x20040000000000000000000000000000000 0xdda0e085028000000000000000000000000 :=
  splitBox 1 94 0xdda0e085028000000000000000000000000 part140 part129 (by decide +kernel)

private def part122 : Box 0x20040000000000000000000000000000000 0xdda0e085008000000000000000000000000 :=
  splitBox 1 101 0xdda0e085008000000000000000000000000 part128 part123 (by decide +kernel)

private def part120 : Box 0x20040000000000000000000000000000000 0xdda0a085008000000000000000000000000 :=
  splitBox 1 122 0xdda0a085008000000000000000000000000 part122 part121 (by decide +kernel)

private def part116 : Box 0x20040000000000000000000000000000000 0xdda0a084008000000000000000000000000 :=
  splitBox 1 108 0xdda0a084008000000000000000000000000 part120 part117 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part152 : Box 0x20001011000000000000000000000000000 0xdfbe83e4985008686220222200000000000 :=
  endBox 125 0x791bc771a45b03cec62b03f74209f2c4b9ccec5d1eec961b85eb11fcd4d3f7b985ed2b51591cc22a59612349a30b0d2519ac17730b3050d83ace5d62e8f74d371804052a0d5d14c3f0dc517a90d5f3306cb7ef69378af8f69857e39b2df9b4e6a7a10b828d5c9739056a2c4b96560098492e672df9805ed26e15a0bd6d6798963dd72bcb2b857ed4f4fc8b756c6d1847a07ff46155ee90b31198bd8c3707fee6d9cceaf18c2970d6a2d4f8fdef698c28aae2f381564ef9ff63026197b4a81e7b8c6147fe4f97a1a86d14871894ffa7423767b48b74fda601809aa43836c6f13f99805744c1a88c2cf67595a8d54927a392ded70afda9e4f593be6f17b3acee836ad5cfa6e67578d1857b4ad8ac35564a09435646d1867276cc5e9415d0f42f5ac96471a76ded2c317b0b17671dcd47592cf696a3b555706d164312a876049a3d47a706d943b07362ea86e3daad5c0c66014214933175ed33d0c2368a0d9492c23312988d08561745a8cc5d02ca83549209393f296016d0c1cdce63505bd84fdee4b9ed2f616a6bda67b0ac960bdbda5ed32587a2a01877b8c5e7722a8cc0b727e410f38ed3f2a33578a9258bb2d05ed2de318ba0fdd942f5b59e728c1bded28cb57fa8d503a2dd504caff47197a5ca2d5f370c7fd6af8b75a85507bad2d8716b436afad04bd3357e56148f1879c76a490d7cf698c3b8ed6ae941 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part155 : Box 0x20011001020000000000000000000000000 0xdff6c9f84857226e4627200a84081000000 :=
  endBox 31 0x1a0791fc6e15850164b17ad67660130cb08ec1895ccf24dc7baa219cce1e79a56af9387acecbd6ec18bdecb391d1c671d2f5cc1b926e1e756110046c7cd83e86b526e9476a8cec460612997acf9e71d394a185eb6a3c493488b5868c0b955843f0e367372f5cd5f83e8f756aec459abf07d1eec1a64a09f74e1ec5d1eea86e1bd8f7589638b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part156 : Box 0x20001001020000000000000000000000000 0xdfe788f0485400684225200284081000000 :=
  endBox 129 0x368c62c8d03f84f5641845a05cea6260a438c32c3d4fcb4dcdfe71b6e1e858ece6d3128f7541716555f31878fbb07d466b06c7bb3a8c3b928e5eb505bda43cedc2d464fcb9b4c4ac0d720c947466b58e4b8c329070f397ae30c9ff5ed2f440062f8c321e79cda9110f3cac2a874352e7b8a7e47ba7ef606a48d26a94798222c97b4c7fd008bddcdfe3dd505c7ef3948b25fc611e47618832cec7ba0370f38b9d6c4907feaa0e2e1b9982d66739bc3cf2c7647680dcffa1e74c07dec298bd66e13feb104faf1b84ffab2b805a487838b0a47fe1e75a0e8560ffa9c35447bb30cd89f1ead61af779896c375505932c05aa3312cbd68ed962ec41164b78d63d03ff681a475130504879d853172548ac412f5ca4583eb0f6492a9152270d24ffa5eb9ca2d2b0f39ff5eef15f56561e7728ad0d6842148f0a1473ae532c2b944ffaa339ed2c2f9ed2a336816af41c45cec1750e8b9e379bc8fe461637f8f743ce2e76f0ffb1c6c59309cc7ba35187bab2b38da824e6eec378c22d0cc1c6dccf31751fec1b2e48f75ac33914c02911504bf8a359ccef695958ffd19b2be5a8e71d595ac0c83d05c95a17c1eebda6587a8cd5eec1f300cd6557cabddccea35733c3ff7b4cb3b698c28147fb99dacab0f1dac8c902ea8851fe802a0c5d9ed2e5d722a7d543ab03da6720b164b92e67524c171370bd0b4282e731a4dd45e3dd733cf6908dad5cc02e419436d4b524aa8b828cd1ff2d45cab283546a5eb7b6a3fdcab30cc7fe7ed (by decide +kernel)

private def part154 : Box 0x20001001020000000000000000000000000 0xdfe688f0485400684225200284081000000 :=
  splitBox 1 124 0xdfe688f0485400684225200284081000000 part156 part155 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part159 : Box 0x20001201000040000000000000000000000 0xdfaec1f02af9022cd209248284008240200 :=
  endBox 41 0xd03e0bc2a08018be0d79fbc16e2dd518a9160079126b13d524aa33312b584f587fe71d94662cb83164f5519c00dc2b092385ba6257b2ce6d50598bcdc83ac7d7173a48d416980b9da9b165d45ed4b695ce675b0bb7461c73e2730d98b9c7ded5f9c969477910c3009a8c2f3ebcd3d0b3c1bcd6a9073ebcd318c3bdae0de9f783bd181695b59dc731874fb943520e2a791c67ef16e8b76561e42edd1871739395ac4a0cc591cf8fbcfdea4384fe7ef85ce9e3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part161 : Box 0x20001001000048000000000000000000000 0xdfa6c3f02adb03685241249286109208208 :=
  endBox 39 0xda4109a1e8d61fcdbc492cb17125a3b55f2b57286879d6061167660b87a6a499ca2e6730cc5ff87a6d02f0de13d5833355d676a311ffacee5189bcdc77395c5ba3d39eced3d379acede47f1dc6803cea4584c24f550eb15683abdde0e6e675b15f309e58be7ef2ffb70c0d8c02c5500dd187506ad5e0e706d9ccee57948ad3d801a8b38edabe3ff286b8ee72b879d5857cb8ee05bb51c5ba3ff940ee3b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part162 : Box 0x20001001000040000000000000000000000 0xdfa683f02ad80a285201208284008200200 :=
  endBox 123 0x96378ba3585eb771e46116c0e98ffe0d79c75ed24f94fbce4b595bda541b282d26e4f90f3bda5cdb204c7def41fbe7b4a48d69650d8fdef23da45c3460502660b1e9b40d57919a08b737a8cc56f39be302d63f8ee368d00fbc3ced5f9a9ae5727abd9e466b53daaef6585ba3ff56124286ac06264ad5cdc3355ded33534fde2e7681785c148a8c3da657c9fbdabef69969ef5b7bba494fdf251ded306b95e6b0f7b4ad245bab630de362a76ca1ab01962f073620b40f6941130505a8ce303315528ec239a63353d28e625173ac765d1ed24e2b058b530e05e149280268a3147ac6014a3c61e50596b45baa2149bc6019442d659a667ef59da90da0698ce4b2faa48d63a6258c3ce5d725ac0673398bc35f18705ba98922b098286dc971fbd676a4930ccb3b9c96a075e10056146298204e30ca51d44260194171872d6a38e60cb92c35f187926eb1da30e9a3976725accd41b461da05e1007f1462dc2686e2506839b9b51eab1d599ab02b38c329257adcd2b3f7b59cc5f1b8561eec176e6a7b515acb282d61f3709259416b3b8c3d0734fca4ddb8599c2b916e9ad62cfa7dd6af18779178800592d4f963ad6583ac0858c3c36772b9a4cf566b59caf073791ed2ee2d5e1fb879d6c50ec69171da3358629db5ab9435abf15f4282e6f5abb8ee503898519a3ef (by decide +kernel)

private def part160 : Box 0x20001001000040000000000000000000000 0xdfa683f02ad802285201208284008200200 :=
  splitBox 1 87 0xdfa683f02ad802285201208284008200200 part162 part161 (by decide +kernel)

private def part158 : Box 0x20001001000040000000000000000000000 0xdfa681f02ad802285201208284008200200 :=
  splitBox 1 117 0xdfa681f02ad802285201208284008200200 part160 part159 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part165 : Box 0x20001801000000000100000000000000000 0xdff7a4f2aa74503c6288300200038030020 :=
  endBox 41 0x1fc5b1907a05ce9db9a6b06b2f998bd4673da6286979cc5ed43d0dc3a8a42e83dd8c2ca1d61eb15507aa1d98a6c3d55230f312d8ba823580ad0d747b4ca1b312b12da9b18960eb3155aae625751345d1c83286d8368233a1aaf3dad01ad4b920ed5757fcf6b406a41d5447fc923421aa334d4f56d57733d07d6a586b65a1ad5de85a4d1856ab9895467350a1b98363d31eea82e72e97aded23d3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part166 : Box 0x20001001000000000100000000000000000 0xdfa688f0aa5450286208200200030010020 :=
  endBox 155 0x1fc6f1e4751d80f3b08b61c6d346a0e56ac27e61528f75f0471cc1b73196f47feb23592ce4798364c96a1aab238c7ba50d2f5d185466a7d51c6f6916ecb512f5b50b61afe8c3bda5836b25387b98ca1aa43d0a49826eb0f60f97247baa498bd65c9592cf6d49aaf8f6916ece6349a862e8c297ae5a8af8b64003f78a1a3ff523c9e31738f747dedc3a01a9964aa095228b74c4a9834d6599b155a9e71b69acd5f6a7cd3160fb0a49eaec2b0b61fbe59a9cdc59e50d6e0b4b1c6cc4ad4f9cc32d3cb92729173b70841896317ad44c4b18bc2f73b0d0308aa1c34e6ea1d907a80d16ead5d4131f5d01ab22d5e27a8b75a85abc3ff7b3a074bbf3dacfae80d87dea098bd6c291ffa10ea2e89c290c4b62e82de5a88f7505aa80b9e411ad5d466a499487a158416b13e62ca48cfdaa496416773da5c8e2a52e4acb6560fdf02bd486a4905bcc1f5038f4e7b5a9257c54200681b8518bda63f7a8cd6ae6194fccb174918014fdea335ab8f762c2898450ab41596b07e17389ccde6585142a78d84521b47a05cec29920e3dd4fccf4307e7b6ac05222e471ee8a960c5b53d6033d9d3f23dd96029236089fbe1ee9fb60e66f37228b9d50681b47909ea6258c5ea3195859dc3dd379cb5113fc7dd46aa5045ceda248e6a598945ceac0f766a8a9253f2b519507b4af8d31943a8235aba91d342e4cc1b733ac9507aa2fa30e8ff4faad8c2461e60bb92c5cec29a0d282398370696b2b50da2687a318823571082f5b0ce503a0756732bfc3a6f6940ecc4b503ca1b60dbda6057a0754364f5524a8be1eeb78a478fdaf6939ba90e1eea925342f59c6e7b4b06c3167f335acf69 (by decide +kernel)

private def part164 : Box 0x20001001000000000100000000000000000 0xdfa680f0aa5450286208200200030010020 :=
  splitBox 1 119 0xdfa680f0aa5450286208200200030010020 part166 part165 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part167 : Box 0x20001001000000000000000000000000000 0xdfa680f00a5040284300200200000000000 :=
  endBox 99 0x82169af43a8d42e8ac208d07ad03dae38da92528ede30a6578a9249ca8ed95e22975248b9e791d85616c611fc165c60b173bda6578a40526e3dd505c5dd7b49866302b01286b407634ae7b5bd955e6f695a88f752029376e128e3dd8c331819462cc3b83dd614cd4f0f3b55e406ac5e5abb4ada0173a0364edacec5924f57adcc4f578b4080d312c62327a859e0c1abc519b2c25cdef69519a035e47f1a47403ce5eb928e62f519c7f35609c32cecc4a9473f9c62f3efcc4f27aa51d8c1ffca453f79cdc9eac1b9a7a73779200740bff0b9cc5f07d9cdad454ed9bfc34e3ff2f9976e8c0b4f43663ef17393d56405ac1a927aa8c639bbb8d23081e75f05cef67945ea49620ad5ded3162d8363c3524b06e625a81d6aeb63083ff9caa5e71738ffe59dbda5a83f167727cd492b5725165602b8f86b3b578d185159cf67620c604dfed2350b62cb6286acac5ce3d393e6c4b5abb1767b4822c7a6b519282af172a979c5ced2340a83c8737387c50d62fc70f16e8ace394879de41e9cc5d286879c1430e0e3025eb625b083938a1a5db1ff97cc7ff2d2c13250d (by decide +kernel)

private def part163 : Box 0x20001001000000000000000000000000000 0xdfa680f00a5040284200200200000000000 :=
  splitBox 1 68 0xdfa680f00a5040284200200200000000000 part167 part164 (by decide +kernel)

private def part157 : Box 0x20001001000000000000000000000000000 0xdfa680f00a5000284200200200000000000 :=
  splitBox 1 90 0xdfa680f00a5000284200200200000000000 part163 part158 (by decide +kernel)

private def part153 : Box 0x20001001000000000000000000000000000 0xdfa680f0085000284200200200000000000 :=
  splitBox 1 101 0xdfa680f0085000284200200200000000000 part157 part154 (by decide +kernel)

private def part151 : Box 0x20001001000000000000000000000000000 0xdfa680e0085000284200200200000000000 :=
  splitBox 1 112 0xdfa680e0085000284200200200000000000 part153 part152 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part170 : Box 0x20005000008000000000000000000000000 0xdfbfa6819c440aa50013100028000040000 :=
  endBox 77 0x1c45d1d027eb28d4308525561dc58bd07769f8b9c7a6b135a2a48f699492f5985ceafd85cf073988ab177b4bb88e39cdf0775a2b054e521e75b143f291d406b4d624979e0eb291d82b0b9d68a51b730d1852dfbda43c671b6f1947414573dad3fa1e7292c6160abc1cdc8e5c93ebad35ed271b0f3c2e796868017b4af8d239096208e8291548eb62b0c118d6a0a12819cde60db97519ab17627cb1735382961d1ad0d62ec23b8b61c6c5cf280d62f17256c173c8cd281ac5e2e4ad8a3162fc28d2d8ac5e0fe5c9980490f8483c9e94a0a874b62b2b5a0b78a25965a6a7515b1167b4b78ca2c050383bc12935aac5e4f4cf5709cb975aba1859a7ea1d7b4cd5d6123033974bce737173a20c49969a08fa0feb43600d4f200565ab4d9002f698c2a8fdb4696d1851d2940d23a2e74fac737 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part171 : Box 0x20005000000000000000000000000000000 0xdfafa6818cc00aa00000000000000000000 :=
  endBox 113 0xfc4820049fb78e228d65ab879c7fe5255b1243ff940c7fe28d82aea1d60bbda56aea4d92c5ab9ad67baac75c96a332f5b202ad9caa5a16aeac5d0222ad9caa5a16aeac5d505c16c6d106283f379c69569ba42d62a2e7596ca2f962ab57408bda6581ed2dc141d20f2c75666920a06698c1b46c69416a7d0777b8b57683b96fd1c6a21503c1c6464bda54920bb173879ddc5f1b41f7b88ba079d6af46149aa511835d185599c0066258b57725d0718368a55466b172f5acce71ca3d5c96d2938dac5d8671c6d62e4f56aec0c138d97ae006a150517c52538dad5d74378c51b592cd37a30ad33378c61614aac9502271b6a1c4173d1854a0879ca3652569130408c83138d8e2e696c6149ea8cd5b230a2e7a0e2f5751cbd5e5a8bd75eca811905e82fa0d65eb2889495dc5b1701f7b88a820be28dabe43ce8318003cea358a4aa35903e4f5905e831701b4737c1e748ebda569a2e7292c729512c80f292bda5c4691d00f3ae0ba204600378c2bf28d9c6e5a2b59d192f6905ca8d5a9b3da564ae6f948eb19370bda53ef2be5eca6f14e16572ccc9fa9814443732bfe30ab2b5a8b045657368bc1a84f54fecf6b05fa41c36b27f50228c380f65733ce550608aee466b99d02303053ee6e19ed28116a1c0407940ca4a2cf85cef5b919a9e1838a0be (by decide +kernel)

private def part169 : Box 0x20005000000000000000000000000000000 0xdfafa6818c400aa00000000000000000000 :=
  splitBox 1 99 0xdfafa6818c400aa00000000000000000000 part171 part170 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part174 : Box 0x20001200020000000000000000000000000 0xdfeec8d3487102649025100090001000000 :=
  endBox 69 0xe83c9002d8ec3e0c82482e7410caf93178ffd27ab0f904262f4958ffd5858e8ffcc5ed65a30f0755aaa81e305ac3e30e62f8bfe51b2ffc60b760c4aba2f051b50ecb3f523ad160e32f071b835d075491b4acb92af3a0d6d2b691a91e59f9afd26ab45761a06417c173aa00199ca2907579a04524aa33522ad56505b99d20e9471eecc0d594aa0a33a3027371ee93ad48ed5d9cceb25505a444fff2c745cec53907eb1d3ff93d5a0761f05a10232914e367375e12841fcb55523a0fe5aaa87d023317d437023d4925e938d9cdd48b20fcfe24f551ac83f681a45b07ff176c5ce72b530dc38d9ed61399f5da56d5f1eea87d3eedc3dde6059ed5eba92527e8f75abf09ccdc253cb496a8c35959d8ad47bacc0b9d601ee8d664929f5d3d24fd6acd0758c0a4dc4e70ffe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part176 : Box 0x20001000028000000000000000000000000 0xdfe6ce81597400640027100088001540000 :=
  endBox 71 0x801d0791c4581747f0a0e51b5a029262f7b4cc15690cf6949ac7b52eead8fe079e173988c7ab348528e5dd7b8b0358aa2c949bc9f9519879d5fb188ca36da3703dd8c4a6235f16c595b906173b06e720a4ae5a16c70162f3584e5673766230b3da4fdab2b1eeb586021ac4c272e63595c3dd690c36138eacadc04612838ead0b4394120cf1eea876595a91562b1c6c19e92b8e6e6e1400a91c19e94390640f74ffb2c6567eb62926731a4753f313ce485acfd21713a5436d5f58ca8d5a45316af079c5ce71b8c2ce612e48b9c7ba72b489c6e127e8f745cede2d0a62826517a7e4dc23dd38d9ca598067c2e71eeb9165048b9d6c7905930b9ce3b3dd65248dd581a1e74a3b681b1948a2c91738f76 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part178 : Box 0x20001000020040000000000000000000000 0xdfe6cb9168d802680025008084001202004 :=
  endBox 103 0x7f2006b1bc5b1b428d8fdc7fee67968293d595cf2388f698d7e93549b946c3ce923e0b2b5ab9896838b99d022e679a0501f030ca8ce838b50d022e53919ad3d838b50ded2e4b9eead5d919ab17725a60c11945e8115e143f2d549ea8cd9edb07134aa86dcaeda308dc23b683aa33562e8217b4982cc46ec0b9e495a07e838a345aba5ff541b85abce6d3ffa914c32ec2d5e7b4b57d05f1866283aa0882e0922084a0f281dcdaaff69bad5da4339b562b395d40f41fd62ab57018cd258c3b105a86e6769bbda5cdab63c8da3082e78be6623561ed2c2f9ca292528da51ca37291d6a317ad48ea0b28da4ddd8523cc1938eb94e50fa91ca37186528ea33505af0a83c84f583ac7ab379a3b45ce1e7495c4c991ea8ed173879d2571ffc3cf003b0ba25050728db4ee83aad4581a821961e6d36b28b260ead62d8c846067a9a7e50422c9067cc0b83fb52d8aa6d3a0eaaf1067a44e6128b255844126af77948a9377b4cb3362aa335aa2f75517be080287d0c522b496476b575ed33585eee5eb96464f5430fc7b2cd5d4888efe0e33d95222f69964ad475a8af07413d52033034592911606c7ff2f5ce5d725a7dd0220cf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part180 : Box 0x20001000020000000008000000000000000 0xdfe6cac94dd040600125400080003000040 :=
  endBox 137 0x76200741e4581c46e0a36fe2d83ff95e22e73118f7658e989528408c8213feb40af193d20cf37fbda683fabc54170b9c3ceb62f8b0f8bfe93d1fb8ffdb47c1c8313d4c4724ace6f203d042b83e0dc2045a01eed0714839894ffb35664f4a334ffae679656c1b692a3360e2c5d1eeaf0affa0e26b527a9bc47ba6b59c8251b9f06b16c60cc7376a28ffd062a02045b8483b407fd8dc20cf589c11d58ac1dc9e67fd919ae5193c6b3f4a20fb1fc5832737523b9be4212856119b31743627fd1eeb587379abf18160aa4752563f7279cd477b69ff5600e2c737279a88638db4aded341f419e71b39ba70bc3403dd4c126f251dcaf0b9da871afdeb6b23625ac75fc466cb330f38ffd647340aa1bfd8ab1ff561ab2b612b95da4b1afd5fe7fd1ffb1567a98ffd63adc3403dd5316c067c3ef3949cdd1472ac8cd370879ce36b3383ceda3f8b6079ded31ad630293d264d181408ac8e369833d19b3d956c3fec93d578cc1561d9ff43cf07590223ef3f6b174e368cd7c1706b0d04a1022f21ff49ea60b98a66e1905ef22c768c09afcc4a60b0f3ad8d3b905eb3f98a74605caeb0334993d47fe82169161b30bc382a1f523ab01c18c4a9118c5ebe2501e7948e7ed7f0c17278dcde3ff58cb40c45833ef614a3bdde619a3b43cf2c657c7f1ac3fecc3b312879c7eec158576937560ec4a126ec558ffa8ed85767fd98aad5d4a38aee7b4a44582a4892cecb517b4b0ecc4a1e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part181 : Box 0x20001000020000000000000000000000000 0xdfe6ca8148d04060002d000080001000000 :=
  endBox 103 0x3f893f5f16c8016871c04a363f71ffaa0ec24ae3fea4f4e56a62336417a4d60f3b99e466c1d4e52e470f3bc8e22e8923a0d2286d67717ac3cef5d8a369c330b0312c7bad5196925c927ea51e83aac760f3accda4a7d7963ad250f39bfc3cf189672ba3b58aab1d0f3af0aa0f74bd71f5d65a9f7523ad5c37b2d45a4a625378b40c559ccec0d378abc658bc1c4ffae23e0923b0a1b608cb57238ce6d408b408d19cdaa09510d0713fe833e50dbe10718de28111eed07179174690a36e02f070f38dc5eb1ee9c6e2f5a28b617ad27b391d64ac1727acb255a8a33564b20be30b3154c46f5749ec91d31797fc5cee03887017abc90750d9a6e83eb48c0027fd2e4c1c4e36d5f8ffa91d2f5b48ec340b62ce60679ca4e560cf9d0790da71ffd5e251b49186ec2993e6a49837d0774f19b9507ea216b2c7016a1a50843c87fd6812232ccd48a935599c8216aeb14d40f204507ef807066aac1fd48e4f52ccc027372c1f456e5eb5614c3e7cf5d6a5a8bda0616c8cd69486e526a9f99666d619eb683f2f59b9456eba2b051b521cf5d41f9ff528ea4941fcd65982280f (by decide +kernel)

private def part179 : Box 0x20001000020000000000000000000000000 0xdfe6ca8148d040600025000080001000000 :=
  splitBox 1 63 0xdfe6ca8148d040600025000080001000000 part181 part180 (by decide +kernel)

private def part177 : Box 0x20001000020000000000000000000000000 0xdfe6ca8148d000600025000080001000000 :=
  splitBox 1 90 0xdfe6ca8148d000600025000080001000000 part179 part178 (by decide +kernel)

private def part175 : Box 0x20001000020000000000000000000000000 0xdfe6ca81485000600025000080001000000 :=
  splitBox 1 99 0xdfe6ca81485000600025000080001000000 part177 part176 (by decide +kernel)

private def part173 : Box 0x20001000020000000000000000000000000 0xdfe6c881485000600025000080001000000 :=
  splitBox 1 117 0xdfe6c881485000600025000080001000000 part175 part174 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part184 : Box 0x20001000000440000000000000000000000 0xdfa6c581aac926200101088484020200008 :=
  endBox 37 0x100388f2378b614954c497d0756238ffd03e82f410ca251ff9445abf1ad5eca9f716e9445022d0370061920281130098645baba3d86495941d20f461d748c3acce725c1d5aca821283a0be83fac55acab1d5b12571fbc5ba831279c2dd408bc8b63791818e02a031fb8ffca06d020be30cb59603d9ffd043187751b8595c61e725b034c4b187919b163c4fe35f7b5a7dd02306f8c398950231ffde4587c0c95a4874c3ce0cf87de7ff (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part185 : Box 0x20001000000400000000000000000000000 0xdfa6c4818ac060200100088400020000008 :=
  endBox 147 0x7013c75169a7e3b893f712005b0a4a81f87fe82f599c5115b163f203c3ce72939b879e38d8b2d7c8007dee419c960c1606ad5e30341c455a7c737f8146317bdb60e273737f9446292ba100388a81495667188d256a4d417a045dc7f0e370b747fe23d96a251172ec8cd4fead83ff8c4680f281ae90719eda81183ea7f5656e4158eca638871b836c1d30f38306060cda3b80c7592c72b0f3a9365a4976d69e6e3964671b6f1605b1d051fb90658e8ebc7ee62f2928ad659193f47eeb51741c4312c6e36a79444a4a6258d7f34d630f07d691a7f5666b49292c81f1ffad8c824882148cc93d154d187379b5462ce982e30e1af733c8e34089805d4481fc49fb48e83c900079d05b41f4182c1b5958ffda08c3c0c1521ed71b8630e81d61bcf695b101b3da582a3f739ba4760ef241dcda6e1595879e16ecb2b1ffb48d414968c3831dd0586cb4f35aa04561b2d3cda6c597b2b0ee3f9acad61af2350e2033e39b879ca4ab6207e48e8fbca06ba303494f394e0fb0716168305836af1818262583ce811417ad8fe1c061f79cdd23a737819f41bd6ae80d41ebc8de2d918796a291d5018ffdb861dc6ff612ad24c4a9827f638db94e834bdae0de9f78c393f5b8680c4b18bd8772d45a631874a0c9f783e9f7502307d95e706f16e9c6d02283f6f0fc71127ef22d852540fc91d312cb6207e48e9bc616ead891d907e3f72bfc80d378ad8ee3683ff79123aa2596a2a3969ecc15946a503281c91d7117416ec4f3288b6907516ec1c66ab94964fcbdb630ef69595ce67408a4fe (by decide +kernel)

private def part183 : Box 0x20001000000400000000000000000000000 0xdfa6c4818ac020200100088400020000008 :=
  splitBox 1 90 0xdfa6c4818ac020200100088400020000008 part185 part184 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part188 : Box 0x20003000000000100000000000000000000 0xdfa6cb892b4403e080000000b8000840006 :=
  endBox 83 0xb42407e2d893f70107b203568670f39bb08d4250be203616ead55682b43721edb41cda5b07d5a2b57c7bab299abeb55378861e5a29f5da5a6f15948a467b4ca1f96523dd701d868038b20cce367375b13c5d169a35da0e682d69ac1be0e22bb417ce5389e707372ab0547eeb4d901a82f93c68117379ef60e68335a6b18be287e59482e47ee82f8576d41bc65948f74fe731756c761a070168720fce1e7377c17441fa0f6370a4750024f3696c9f552297ae723a0cc9e720cc7ee83f5a6c1c71f7a0fda04198b76522ac568368f75852c416b16c6307ff203d846a0e3a942c55abf27d5682a1fa0daa4593be4f3522cf75519bda4e1ed0388ba0b7546316bdeeab5705cabce5949b86408ac56408ad87e39be5189b94e0304228381fc6473a91d68ae55737b4071d948e813a0de8cd7299ad4d6b291d65ee538d4e59f2799c7546739bd68a813 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part190 : Box 0x20101000000000100000000000000000000 0xdfa7e8d93b6422208000200030100840202 :=
  endBox 33 0x5a1d85316c394c737750e362bb818293f5aacaf315ac6047bab4d5b038b1ead27e3dd5a69cad741eead358bb208d1b693f60da36e6d1d46b03a7079d27f2d34fbb02ed4160c927aacee40fa51dac7f1980f3b180c94a3c8cd699abce3020bb1f78b9e59fb07d2221559ecaa31400a44507ec6033e0e9832e5239ad5044a3a87e5199c765799a4d6aa925 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part192 : Box 0x20001100000000100000000000000000000 0xdfbfec990b4c4222a200000130200840002 :=
  endBox 53 0x318d63883ff681b4611a869126b031c1721e74c07bb2d350669374a3bd5e6299afd816b3358ab1560f39c6d28e80d924a1e775126eb519eea71b49aa4fd8b33dd55e6f6d5a8a91d63b079e0fb3dd58769fd3daa9140ee07d5a1b08ea34093f531a4466caf11e99c6d5e3208cdfe2e7492cb1d907ac1b5a6ac0b62cce51f93f67baad3566624d828f1817b680ed462e5537fa4fe611b45b12233d9584672b2f98b9d3037fc71b4a073b2cac7bab15969a8828acdfe3619eae5c97b2ad35c8f3dd5a842160406b91e7ba9725eda9fd7abc7ed5abcb09730bdb526ee47515a0f43cf2934fe6911 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part193 : Box 0x20001000000000100000000000000000000 0xdfb6e9890b4402208000000030000840002 :=
  endBox 107 0x1c4761ac28894956c501c9474009c74c5e82f701a4579c1e716ea48ce36e539002625408c6f18c0a77cc4b06ba3029df72a9f8d68a62538eb94dd45a0fc7f127eae3683f74a3cf7558e879cbd72cec3cf41b563a7f316e8ffc3a72e8b4d58ec625305879d066d62bc6305879c2d341cdfc6b15c0f3a4d62f5bda45ba3f74a3c04959fabcd03eaf956130581ca31409a4dc9f294758cc3d3492bda4c4ab45523ca0b611140e9a49650fa91c7a6a47922328cd26ad0368dc1896317803e091b99e0fa8cb35fa4d56aa5ff6e11ff24456769118bff182d80561d42819f8d6248da24fd6861c589ea83d58cc1c52f59c882d350bd6a33962e6b56ab98960dab179ed2d2b606a8cdeea9e39633071737ac5d81a6253d127e37b9466f69370bda6581ad45a62da2e8b41bfe61698951b682341eb40b2b8176813312b0ee3daaced0268db6e1657315563a62560fd1877b4a8c6302b42987dd9ed706d8c2a004f6a6e13789c6d69b2044f6a9fd7b6cb2b522cb55312b58f836882f596c2e7387cb2d3f17c1fbcb2d2f5c701317c6a748e9f3d472c236859d9eeab1d50bad44c5e70f969af6d729bda66d184311c2e72ffad091d969a93f48ed181839bda4e1ed61726387ad354567cf7b6cb4d (by decide +kernel)

private def part191 : Box 0x20001000000000100000000000000000000 0xdfb6e8890b4402208000000030000840002 :=
  splitBox 1 116 0xdfb6e8890b4402208000000030000840002 part193 part192 (by decide +kernel)

private def part189 : Box 0x20001000000000100000000000000000000 0xdfa6e8890b4402208000000030000840002 :=
  splitBox 1 128 0xdfa6e8890b4402208000000030000840002 part191 part190 (by decide +kernel)

private def part187 : Box 0x20001000000000100000000000000000000 0xdfa6c8890b4402208000000030000840002 :=
  splitBox 1 121 0xdfa6c8890b4402208000000030000840002 part189 part188 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part195 : Box 0x20001200000008000000000000000000000 0xdfaec0d10e6500749000241042100009000 :=
  endBox 85 0x2d09e220e82d35e46e15fb1cdd86252557c98bd5850fc4f9173acfd68aec0b9e526b17e76107f1cdc9eb20fdc451c97ce4a397ce1ffb70d03b0ac2d83dd6f1d00e2c729064b91e173ac95cc672b57cc2e76afc0c738d8b75b4791417291cfba5db1739cde41f8e6e591ac94de6da18be27a832565f1b955f293d87bb07559dbb0f2368ba0b9c17713f4fbb30a567f1afcb927295aac83f05cc81f6916c6f1b839ba42e597a0fc7feb3b515cdc3403dd64163b398d07e0b583ed1873eea91ca0ee5785ce2e793c6a475a29c6e1eea915601eeca3f27e9f06012cacc551ca8f15abb2be569ef834082250c318e3a0c9312a8cd48a525965227905ca87e006b0c5eb298dca83f518cc19372b20d60b9e4a0ac7d07ea318dcab554a3938638e9b959051fc2e7279ca393ffb9753c660b8c02525 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part197 : Box 0x20001000008008000000000000000000000 0xdfa6c6991a470074800314100a100048040 :=
  endBox 51 0x200711e47415e708c586271b3009894a22525531dc27eb48c2244e69f8f4ce36d3f92261e7370c2e787aaa03419ad3510526c5f35a6879e419a4456c61019f1c745bb1c3cbd24f3594c0cf791d05611069fc8135aaa7f547e6015b1b4281b5667b698bd25e27b9ab270f1eecb576d184173ca3f317a20801949aa31902670f72ea0f544b2c5d48ed3f387c10e429166168f753fad3f41e9c3e3f186e5a7e2e7370c73738ec73762f9b84bd2b62d0c81ca5417461dcc61c5152ad34592b4d819e72b5a2ca45400833ce3a6b5819e6e1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part199 : Box 0x20001000000048000000000000000000000 0xdfa6c3912acf03700001049086100208000 :=
  endBox 79 0x1f0801d8791a86f1b4292ad8c228fe317a80c5cec5f80b65031ffb400bb943a6196b165720453c741c50267f16a1cc411ffa04543aaf96d1fc6116c72ece67305941cc5e2e7680177204cc4a8119a625076e148b2be5026619379cb573ff9f8d0267b58a0eaf996332914c025116b16c4307fe8820bd02741b562e92b418c1ce50ead5d2169f3495c8314f9b880b996564f316ea0465b143b27cd462c5f3799c75ca73d94fe27f35aab58dc368ac3c82dd492c1d352298658630ffdbc522c7f350f8ffd64b28c4c5e813524c9f3408a0fd5f20b994627ff597c94750fa8c58bed63c89a074d02335747a6b6350d24723b5eee5ab733a50540f204525720c53e60cf3ffb40f21c765238f2d28e941b949eb3d9565f1c74f5738ec7a6ac149580680a0617186a26015ab8575ab20b962ad0715aba04e6a1a504c02c17a30ea17587a50547ed43 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part200 : Box 0x20001000000008000000000000000000000 0xdfa6c2910ac540700000041002100008000 :=
  endBox 141 0x1f89e24fd1074169ab63e0c83c881f41eca3f4189494e1f20c549b1b4cffe3ff501ca17292b88b3b85ba3dd96ae1d39676911692bb8da3c8e2074e0f3ad83ff85ce6e5387b5964fa9c6c7badc20fe065a07e4a0bb0af9387c72940fc52596c801a0690e030ffce6ee8280e2ee8ab4c023ff8a070ffcdcb079ce6ed0312e6a18b7437ab2d41ead5c55a1e787bab3b3913c6d169aec388f2350b0d87a6b2527ea0cca4ae82d8d62c3e501879d07f07191da7292ffb07e27ec1c56768ed4a3a3b63f9a4456c4a0c4f3067a0fce6f181838a83327aad8f81cde15e8b3d05e80d8bfea4d46dd071729ad4501a5e98c0a0f528406c83d5b1066b1d969ec196e1cdf1894dc31819e45b15f2c1989f2a031ffa0fd48b2cfd02320fda4681f05b149b20bc7fe73741055b282d48a947907ad43949a1c5292b58b6079d61f250505eb0f902281d288c83d583ad45604e1667236d6761a51eea7a5472e22d851146acd2558ea0f47feb3b837b06d8dc306d9cab0753709805d879200711d0530a4ab02d8511317cb0f51cb48e4769c6c34adc2be63129bfe594a8960f3ac3ca22da348ee2d8b1d87feb3b0599cad3fb20cd28e1e75a8c2c951cac0d40b9e0deacee8c0c0113efabe503a6e157ccac30ee1e2980561f179d27aa4d317b687378e360c157cc83d8dc2b554069c6ce6eba2ca6618832d03a83368101b0739666c190f3caf7 (by decide +kernel)

private def part198 : Box 0x20001000000008000000000000000000000 0xdfa6c2910ac500700000041002100008000 :=
  splitBox 1 90 0xdfa6c2910ac500700000041002100008000 part200 part199 (by decide +kernel)

private def part196 : Box 0x20001000000008000000000000000000000 0xdfa6c2910a4500700000041002100008000 :=
  splitBox 1 99 0xdfa6c2910a4500700000041002100008000 part198 part197 (by decide +kernel)

private def part194 : Box 0x20001000000000000000000000000000000 0xdfa6c0810a4400300000000000000000000 :=
  splitBox 5016 117 0xdfa6c0910a4500700000041002100008000 part196 part195 (by decide +kernel)

private def part186 : Box 0x20001000000000000000000000000000000 0xdfa6c0810a4400200000000000000000000 :=
  splitBox 1 80 0xdfa6c0810a4400200000000000000000000 part194 part187 (by decide +kernel)

private def part182 : Box 0x20001000000000000000000000000000000 0xdfa6c0810a4000200000000000000000000 :=
  splitBox 1 94 0xdfa6c0810a4000200000000000000000000 part186 part183 (by decide +kernel)

private def part172 : Box 0x20001000000000000000000000000000000 0xdfa6c081084000200000000000000000000 :=
  splitBox 1 101 0xdfa6c081084000200000000000000000000 part182 part173 (by decide +kernel)

private def part168 : Box 0x20001000000000000000000000000000000 0xdfa68081084000200000000000000000000 :=
  splitBox 1 122 0xdfa68081084000200000000000000000000 part172 part169 (by decide +kernel)

private def part150 : Box 0x20001000000000000000000000000000000 0xdfa68080084000200000000000000000000 :=
  splitBox 1 108 0xdfa68080084000200000000000000000000 part168 part151 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part204 : Box 0x20100201000000000000000000000000000 0xdfaedc7068a512885028040200000000000 :=
  endBox 107 0x369043e0d0398f21475644c0a12a4391ead5f386a3fe0fb357d22a8df641301739c3647fc1c611c9a8da46a1d6afa49638eb94d4666e78e3a2bd284aa0c013fcd4691ca436abab0f2307e587972544293739bc3dd5a8cd5b05bbc89118562b075a48f76045ad34dce7227ae6adc1d51dad3d4a3a90dabe98390649ba90d6932495676d237911f334ad69ab49173b98d6145662c8fbda57059472e6e73809c0671d9b9d69ab4340b6260e618586d335a69c3528e72962123302dce6ebe2d261dba49569b064daced335f169a76286e7b5c1f4b7e907492a4ddab71f75ccea493e38f754872c76611aced486a1b5a6b40883dae2c9c1e5ab69254a3b08e161976c7de1bb93e68f91f7b56d436b4260921c6ce528430f662aad35492c55969aa2f6adca2183c8b2dcc571185a68fbe0f3286dcaed5f579c12b4839a9e0e2a0b83ca41e72babce0f2d5f5a69cde5a6b57dcc571341f7b28f80b2d50835cd3372ba4e5466a45736c841f1e4a2b4ae0f31c8d5f9272a1d50db95dcdaa45852ac0d606d1876adb095cdaf8287671da914b7f2bc5ab66d9165b8ee373a925436d5b05ba20de2d356c386a7ce5178fbd61e72947fca2f524a309c05e659d865447b3dbd492e6787bb06f524a9157c3948b2e285a7ce720b915cce3dd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part206 : Box 0x20100280000000000000000000000000000 0xdf2cd975642710881540000000000000000 :=
  endBox 125 0x2d0ca1c8c02d358864122b02d439ade2a08fd940e2cb72aa514e6ea20e6e5aa8b2c756b5595fa7290d9cd5b165aa0de281e487a515c772c3d692d5b2f89903939226afd728cd250bfb56dd862130560e52c298dcef6359fa766373bd8c35ed5b5aacc379692913165cb2f5aa868d80641885a2c0ad0e08735002a14432cbd68a641e0b55051c9252f8a49658793d54768f99476b0f05186bd8c594cb497a8a8ecbe3139544298378ce1ed6521b9149ca72949ba51c9cb1c6d49317c49ff348cf459fc7295aab68c413fc5972cbce6eb519226b51a082f8ab0c41903dd69ed1856afb155626d5fa30ad23321c82915a0f31815aaac3e524b48dabf07566b144670dc631ab6ca2c89806cc3763c1989ec294ffc0bd71db10c83008002f58ab2d255fa6cb35acd571cfa9256ab0ac52c488c6d91d3acce57ecb49470ec64073eb0f9aaea490eab92e503ad45c97399c3aad59587cc11524b00ac2ca64a2c6043aaa21524a42e6ae9c75eeed2b2c9c00b57e8ead6aa71d6218c50dca490ea82f528f07554926b59492b0f594a495ab7338c03201d594920bd4a3c947818ac59a30ed5d1b48b2d804c19c61ccb3f5a8a51d436a494a1a5713ada572cfd6969eb27fa86e69193fce032cfce3ab2f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part208 : Box 0x20100200020000000000000000000000000 0xdf2dd8d3603502845021108010001000000 :=
  endBox 77 0xa8330b44105f16e1f439bcafd386947ca3a8a249e37393ad58490382389928ea1b7368f7630ec23589c9355aab92e25bc1e4dce9039ab62e7284c61e6ad9ed60d6a330ea9cdda08218c6e10028ead8ce320c51905e5db173ad564a3ac4d81a6e72ed93ae83cd187736a51d81a4eb604cb136ab9ffc9d67f189d68df4818b9e50ea40ca3f1879a824713dab0360d671d51987560c6abd0753799ffc5cf410d03709ed8e6eafd28f949d07f355d0028f18311e327e549281141f8b9e5b12571c754667371e0c8f1821906e1a07d128f1c6c5ce5275b122b2d3c3aa2e7728ca4f48a8755c83207d696afd173abf60c9ad1503ed5f478b4064249635a9474bb691157eb390759c831816adc61cbb69113b0a3ad5ba30236935a8465c831873ff8da66a1a79669ebd74ffeafd2edb56d6c4c144335660eaa0b6a1ad3d2563ef394ba03ef2edce51468a50587b1b9dab6cc3a107583aad5f8e368f1987ad5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part209 : Box 0x20100200000000000000000000000000000 0xdf2cd8d1622500801000000000000000000 :=
  endBox 115 0xa02d07314f1d85a6ba0d0320da07351cf142ce6e90b59fc7295978f75bc4e0e6e90f8dce3dd36bc2c5523c6f357e9b2cfba51d4a1901eea35626da7e5a56a3b348ca495979bcd4771ca639bbe8a478dca50b560be32cbd21ec23670daf281cdce0c9733cafd7b1b576087d154460a162b387baa47372a91e380c51539bb40c8032637387043aaac2209e5a30eb2f477c61e162acfcbb31f3630e6d73c1582f8a8d67a8b56c5ceb3f36bc82fa30e72b943b04340f8318ce1475302edcd5b491b585ab8daeb450eaa81dab6b4583aaa0737393ae694b50e4a39b94a3ece29262eda494192d299f067158173a484e52edca49373cd5b8dcf34ada52d5b89cac81b2e6ad8325ab72d09e220c62d357c541d80d9c5093869cddf0522c3c72858fbca121ab95fb1c3478e3ef597c0c71739c34e1b1ca5307c0e52da02d65059474dcf27cd68aa4905ac1ab524acbe5039cdd80761b838d9cdcbb324e548af6f28ea9168c0b69181928a50928ea91e2f8acbe5188fbce6ef8410a8147d8c50f9b9e61f94260d72cfd5e6a1b524a4d4f5724d5652b3f5058f1e0648326 (by decide +kernel)

private def part207 : Box 0x20100200000000000000000000000000000 0xdf2cd8d1602500801000000000000000000 :=
  splitBox 1 101 0xdf2cd8d1602500801000000000000000000 part209 part208 (by decide +kernel)

private def part205 : Box 0x20100200000000000000000000000000000 0xdf2cd851602500801000000000000000000 :=
  splitBox 1 115 0xdf2cd851602500801000000000000000000 part207 part206 (by decide +kernel)

private def part203 : Box 0x20100200000000000000000000000000000 0xdf2cd850602500801000000000000000000 :=
  splitBox 1 108 0xdf2cd850602500801000000000000000000 part205 part204 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part212 : Box 0x20c00200000000000000000000000000000 0xdf3fd478196106001000000000000000000 :=
  endBox 45 0x1dc741b8791cc600c4aa81c6d012af3904ed674a2acee37fccc350be076540611c81916897d5072a1b878a0b761ecb0939497d569b18196127295a6a09d242829736cb51599937dab65f560160728c71d41c8fa45a328bce369198e1e72b5a7c0b36adad34bfe72939bb48f6f875707d61197c418e71b39bab8d6798aab4d403a0e459f2d35d06e161f309dab69150ec9804c4aae248915493b4c659ca8bcbfed358d7e3875a7937e71c8fa4be2b4d691a86d0dc72d352725f1063ac8e2f89b8d84f291c37e945591c5f1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part214 : Box 0x20800600000000000000000000000000000 0xdf7fd9702ba51400f000000000000000000 :=
  endBox 47 0xe6368d02d8509293aca65a7acbcbfee679ecab2f3f4acfdb04f0e625ff8c16515967ed335a2b4d5aa31fdcc16b4d6c17c398b00a82e8a499a66a3162baced242a4798a2827518acbe7ba942d04eb2f94932d55676d5b9416c47523ad35a03e1802fab68d42a0d8358a6356c9fe0c583fc9f3597b0e6597cb1d9ea2d5b61e82d5876e6d27fa7fe612b0f54869df8166b4d59fb14d50587ce5713fb145676921597cd5b59da7ce35fac0dab64ff9606d5b40382cd69a9e2d250c5a696665838ac4b332c1d243359d28af53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part216 : Box 0x20800300000000000000000000000000000 0xdf7ff4d80ba945001e00000000000000000 :=
  endBox 33 0x1b8691dc285c8193869455545e09eed42103dd522cb3b4a2a4e6519a4e6522acce4fb97c55c159cb23613a40d69a731159c6b9063b9bd69aae360c01cc4dc7302504eb4d628a01e5a6b59db45a6c8273fb97cc733359d3c2d4b6ad85b500eb4d173cb0f289ad35dc620be33d94a1271b39bb685f18f5670d2d9bd74756b4d2849c364412726e3969a5f18756a47 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part217 : Box 0x20800200000000000000000000000000000 0xdd7fd550092104001000000000000000000 :=
  endBox 129 0x6c1780f8b28ae340731601dc540dc613ca47284828d43e8a428939524c8f1628acbce1a2e76b3c2d5478b14498282762bc509522b508275b165f1ca5492b3f173b99e386acfd492a0b59fc6e2455272d6781666bf1c3a82dccf06bda6a6bf597c6bf057cb4d2ffb15d67e2e76a1e45405ceee29165aa94247d31724be227ba0faa492d2a8bd69a5099cbb399c7d2d5b59fb408f1948a3e917394245cf300842a09625065a6a43c7d2933681301f48a6e39bad3546a6cb963eb4d38ea86e7aec1dcbe29275a2145a6b507dd9eeaa432ffa924bff1ca5aca27b7b2c2451409afd04ee4b58fc5ff413a203e94fbcc2f72ead35acf0d2c4669f760bb92c92727ddcc25ff39bad34d7f0a3c8dc398d03106175a0c02ee2d35ab71ca55f31afc7bab091e3c827403ac3e173cb4d28a982da03e1502fab48da1cdce3ac25904ea4962aa42d3bf243d492b439be83ca9247bab4d158cc2548eb56d686607bb2d341620ab969a6bf8286b0961da09d345a0e3a0b7969ae5d816e90f85a2b0905bb99d69a922d24b932d352165c9969a93d837e5ff5a68b9db441cce5138e949c9fe839900eb4170ee2d35b8691c83353c16a3dd285b000b196a281741c944e403accd04f14245631f64ba20b5731b85917416a944c16f2cec37ec47964b1859ca6267592a9145aaa45a0d6a0b41c86cc1564ff816adc368bc398839960e9e15928b54a265274009feb07816e5d115882de5a4acce728a01cd9702dcfd282746fc1432478b54a121bf (by decide +kernel)

private def part215 : Box 0x20800200000000000000000000000000000 0xdd7fd450092104001000000000000000000 :=
  splitBox 1 116 0xdd7fd450092104001000000000000000000 part217 part216 (by decide +kernel)

private def part213 : Box 0x20800200000000000000000000000000000 0xdd7fd050092104001000000000000000000 :=
  splitBox 1 118 0xdd7fd050092104001000000000000000000 part215 part214 (by decide +kernel)

private def part211 : Box 0x20800200000000000000000000000000000 0xdd3fd050092104001000000000000000000 :=
  splitBox 1 130 0xdd3fd050092104001000000000000000000 part213 part212 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part220 : Box 0x20012200000000000000000000000000000 0xdfbedd3c61234d191000000000000000000 :=
  endBox 37 0x1a0531884b107271b39ba05e59fb4ae4eca05d69abe398c01f8839499c817517823e51aac6588e70d5aa9cc58bf0fdce6270d96aa80741ca90e5aa9c35b0601883c039a839924e72b9ab72d34be20c9404a0e5453461d196807581b56ce567315a6a01e276c605cc6b4d395a0e594591cc6c1145a69cc544f28ee0d31fdc7ee8e769ba90d69b41f4feea292769c047eec42d3549f1c05232a29832aa3b6a7c4ed7b58fdce62b4d500ca29 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part222 : Box 0x20010300000000000000000000000000000 0xdfbcfc9d402b460a1e00000000000000000 :=
  endBox 67 0xca2f0ae3407316915038dc945395831e5099b647ba71b671667359d69a80737fc3dd5a69c065a6b40c42d888348b4d3d0e56a03942e9378db2a39394a70e559eea3dd51cb56e37f9afe723a84e30ed373949cad403243cbe2d5f38dad35033357526ad3f69ec5f3380ad35886814c540e36cc1cdd8a341e5666d232f8b4ae599c1f6509ad356c36cc4ed611ad3581aa13395a45651eb02e7ae9b654569eb6119c0569aae28ee30f163da62b4d4f5a0e569b461da06715c58124b356d26e4fd413a0e5a42f9c9156afa4e5edb356cdfe5f32f8a05d8872108820be2925800e9e983cb57dab69356afce5589fac5339597cc9fb17cd26b004cbe6d5d40c93b5a7ee42b8d438ff2d5d35fa45524ea817c6395a84e51e8f75acb3d5cdb2d5d1fbc5f1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part223 : Box 0x20010200000000000000000000000000000 0xdfbcf91c402304081000000000000000000 :=
  endBox 143 0x651805b130670a1a4f968169b185cc5eb4d8c16b4340a034a6493a844e6e60d0e6c72b5a6b0fe495b144e62b4d6b2c701694b9850367143734ccc5e731305acbe628b56cd7e6d9398ad072356e0dda0e45bab4d591edf308504ed356ada8ec15ab498fee82735fcc3f61d97d504e881c8c42d35c4292c8392fa8b74d7f34a4c4ae2260827941b079517948528e81796aa731413a05e5aab4f5abace2808c17d5012839493cd235a8b52e8c09485a9aa27837b88ec2f85214a3c6258c09bfd41a8276b3ca0d9ace8278e1a93931297d6671b0540e625215a2c945312b14522b2cbdb44c0c4a82794863ab944eb3b413b54649c9afd012d6183616e9afd5c62bcd3137fb59522ab3f8f9a71b681cc6d1546b0c2ec83b06bf48ec92f1b7cb4d306b4a639b8b754271cacdfed339cba913398983569ac42808079ab6729300bb0b4003e6b2a8953e69371ee9ca500f356d69b1b65b0630e627cf965eb0f6b3cd338dfeb4d489b10d22f871d725c2dd5a6c5f56adb586bf85ba7dd969ad672fab90b4d480b59e5a8a8ee597ad559c731a671cc47eeb4d305b585255a4b0f67a98e9d84690b583b97587b2d35cb7289d42f1813eead34d7ece340e6280617312ac0d3f877307969ea0e5904209da817921ed3d6aecb456acca2f6aead56491a4e57c3f1072937987f079506a09cbe3146e610a025ab717c4a3660b720a864122ab4350e3da9afdaa2c256af8734db3350cd7ee67984ad5164124ed43839a60d35fbe8d238e1ad5f698b544c1b260a03544e3b2794bead5d3fc8abe62bc604dcac0b9847079 (by decide +kernel)

private def part221 : Box 0x20010200000000000000000000000000000 0xdfbcf81c402304081000000000000000000 :=
  splitBox 1 116 0xdfbcf81c402304081000000000000000000 part223 part222 (by decide +kernel)

private def part219 : Box 0x20010200000000000000000000000000000 0xdfbcd81c402304081000000000000000000 :=
  splitBox 1 121 0xdfbcd81c402304081000000000000000000 part221 part220 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part225 : Box 0x20400200000000000000000000000000000 0xdfbfd418106102001000000000000000000 :=
  endBox 59 0xee398e83c841720c9cae2ff989507317a4e3ace358ca101cdc398b50e37f9c6dab6b00ace0dec1f4e36d4362993f5032d59969ab02a081939bc5f16ad86e49fb356d072a81b824b8dfed5d50fac3502ee53008c9e114ab574e6e5f1505cf7783ab4fda7a71b6aea604fd984a8390d6b154de271b5b1b039ba0e60dc97ce4e187ab33629ce6d481c1f6629ad3683e97c5cae9e16aeb08dca67f93989c6d7c2049c02dd7b5cb4d506ad24a1a5e959dca1b629ad24e3ac3d941aa435a6ab84015016c3989e8b23501cb4d49ca8ad69f1b8d22ae553c0dc734d569a903027c6e335fb09c5669f754108063c6e32f8a5159c6d0166c2392065f3371cd67523c6e7518ad84fd6b3ca2b695cb4d6a6c1fe27eb954be2b4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part228 : Box 0x22000300000000000000000000000000000 0xddfff4981aa954001e00000000000000000 :=
  endBox 35 0x3b8a0101d5c28ec7f71eeaccd69a839398aa89478a2681928086e6527a064a260b18a1294764140661886e17827bb5368c3a4e52070793988f75a8b41d5cab1875a6a40e0f20c75d20f3357d41673148aa4e5b04412067312f8cb4d8c2ce396b39b1d3eed4b6b2c7d90b7bdbdaaeb4d505c73148193dd223282d48e93527bb30bc2c1e4a38f752460b535fc9f748aa51545702ad787b1d18761ca91d26a7315b18af251584e3af691c27561fa4e58a3187 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part229 : Box 0x22000200000000000000000000000000000 0xddffd110122110001000000000000000000 :=
  endBox 143 0x6c1906a08224017213c0f8a4de71cbd4d692b4d50acf63062af0ce030e5aaa495cdf0b751de2dd93ff24943e2b4d73178523c93561fa4443e2419398b787df94728f5478a4543e241f4f03e31872f8cc17733ad34fff17c5d86203e292385ba923900e9e027e49193fd69ade2808d90ddc7bd7b8ad550531816aea44601c84ce302e5361f97c68c0ac1daba911771bc6b18020bab8ac209d0722dd82e24ff5a6a51d69b13fd6859169aa4f89feb49926eac24de7288b752023ab9692b514711f32d3520280772126f2d249fe913969ac02b84ff928e82741c9d8e4244e5a4a7fe72ab17d226d4588ca7b54a38b5569ae6276c9fe92562fca471c0c6ad72ac1e5cc6d1b88c3c2dd28e949d78280a12c599a7ad5f4889b9e05bb5145aaa0b3e1cbb399c3668f55b1c972d3582ee5d9cced5f5a05ba721fa4a17185982eb4d8c2cc1762fb05e62f9ead3eee413f4ad449ff293c302e6759d8b7510391785a1585a68ebe504b17d2269472c1a8b0b55aaeb490d9cc8251c737305dec2c5f505a4445aa91186ef41adabe9011599b9d88eb4d5e1545612470f7528e96244605a86ad8bea3162fca1d5b190043cc3148c82d475f28258bed35a0f2e6748197458bf17451c6aa2f0c8200962a01b394622d5523ad86e7982e0b72dba474fdf1859a969074919b9e0d741d47baf774918b556a324d564488829e587c61d6a21bf50eca31592ad8ae2e81b3837e919982ec17964a8f94d0e4421a7b0eadabe6e787569623d5a4738e564a0938c2d07571cc84370d57481cd23599b4d683cb92da471859413079 (by decide +kernel)

private def part227 : Box 0x22000200000000000000000000000000000 0xddffd010122110001000000000000000000 :=
  splitBox 1 116 0xddffd010122110001000000000000000000 part229 part228 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part230 : Box 0x20000200000000000000000000000000000 0xdffdd010002100001000000000000000000 :=
  endBox 131 0x3e8d803c5a0403c8f96adad54e3a1f11fc9045ac7312833594dce1f1398a08483ec407c564380ad56373a4642cf2d54dcea4f93fef5b137c61c2f6d5b5aa9456506a514be21f1731ac6e082ebc142da0390a4e05b943ac4f373ab0c4f85bac4f8e469ec7ef373a4918793e6f7748ca7fdaa2f7793ff0714f9c6e716eb40961d8a45838c5b362786ce4a0a90d20ec59940ea43503ca4362cb70621454a4eb4b9ace6f3838c9f33808e5d492bc41f65249b94a12b6391e524b05cde6a2fa0faa495a1644507bb2d34e36a3b527b40b4d89fef6b9eeec4f514865569ade2d358039ba806521c1f5cc2e51499b57d5ef316416f3044fd2c59681bc6010041cb13e62cb8ed21e6e740cb07e27fb4f411a9df521b8ed1fb3d646dab390bbc604e3a8075913ff020430207537393fcfb33165ca26e749100379c2b1373b00915928aa43835d1873fbace6373a465ab6e8340ee10059c6f1a820c93e62faa90ca42a2146cc8395d03e3181969a5f1283c6066a1cb4513397d48321f161fcd2b4f78dbd69a5f10f8bb0ce2e8d5b85ceb2f50d87c4a0ed4328c807c4a4a7e18b92c5935ad1815a2d1811c487c483ec278e621f19947315820f9cc569b057568ab4d8be2d42ca65a68675846a3527cb07e594acfd69ad5b833aa3520fb28ce1cc598203a10d23818eb4d61397c528ac8309e063b10c27949ac27969a9ef481b09e61fad35985b19083cc6bf159b4ad84aa2b591ad3d28b293584e7a240d69ad5fa0f2c3b695c6e711bc7ab478a8acdcece1b5e2f8a494fd2839203ad3e62097c4dce7f9 (by decide +kernel)

private def part226 : Box 0x20000200000000000000000000000000000 0xddfdd010002100001000000000000000000 :=
  splitBox 1 133 0xddfdd010002100001000000000000000000 part230 part227 (by decide +kernel)

private def part224 : Box 0x20000200000000000000000000000000000 0xddbdd010002100001000000000000000000 :=
  splitBox 1 130 0xddbdd010002100001000000000000000000 part226 part225 (by decide +kernel)

private def part218 : Box 0x20000200000000000000000000000000000 0xddbcd010002100001000000000000000000 :=
  splitBox 1 124 0xddbcd010002100001000000000000000000 part224 part219 (by decide +kernel)

private def part210 : Box 0x20000200000000000000000000000000000 0xdd3cd010002100001000000000000000000 :=
  splitBox 1 131 0xdd3cd010002100001000000000000000000 part218 part211 (by decide +kernel)

private def part202 : Box 0x20000200000000000000000000000000000 0xdd2cd010002100001000000000000000000 :=
  splitBox 1 128 0xdd2cd010002100001000000000000000000 part210 part203 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part233 : Box 0x20080040008000000000000000000000000 0xdfb5de321604a501480a101400200040000 :=
  endBox 27 0x1bc791d06a19c286b10e659ed27375a694950c50128f1c34fc6b355a7b56e83fa7bdaaa3d3164ac24f6b3994e629f33868b767d1a47b6c73716e9c3dab734b4e63069369ac345bac238e623f16c14c398b98e491ad3ce1a8ff98a6b4f614c73759a940569afa1c363699c3c7e32c5e730a48ca0e731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part235 : Box 0x20080041000000000000000000000000000 0xdff6da3a0e80a4894018208200000000000 :=
  endBox 61 0xb4220ec2d35a46817c3869ca4563251c57b3a0f222850d5d1ab72cd4d42701586b994bee6a193b6d5b8c3acd5a6f1404536b1f380a92638081ee5868ecd69e5f7369cd2d16eac8daa2d5b286b58b83409c0b75ecb0add4521a96a3c61e372bda60e2d5b49114524acd63f1a8f569ed5b8f56b1f966ad5b372cd5b272d07714dbda4dcaa2f741a87918016ec1d352493bca1aa2f611ac5f05bb1a85ccac590e9aa8f699c822c9158a8a6511ed21aba30e5f7723ce679ed2c299ed21c7517b085f73a03a67297b4ce5d6989fbdac2f658fde7ab4edce41584bda46c717dd49ef690e9acd4a02d43010718296b1f16e9fbd4924ef286b58b0993e66a17b4874ce3b27cc5921ab7b4a7fe7b29fbded22dd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part237 : Box 0x20080040000040000000000000000000000 0xdfb4fb930688a601006802008c010008000 :=
  endBox 47 0x571785d0e62a23885f762bc6e5288873daa3140cd4ee23b071d859251767056f248c39ed619cdef654ffa4871d9aa22c338eca11698cc3f28bb50de388a0385ba517292b007f19a4a70f607a0fe508a8ad906b1107b4c3bb16ea7951def71410b92e16eb4de7b88fc5ed2d3182b6d6516eae8c0f961a5f74ffd18150bb0fdf064180410b7883f87e24f9531aa320fdccf1ed5cbb399dacac434c5aa31ffd3d62dd491c9eb6b2c517 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part238 : Box 0x20080040000000000000000000000000000 0xdfb4da130680e4010008000000000000000 :=
  endBox 157 0x4813c49f9c888398b4d640e62d658a2e82116ecb416a8a48da62de320525061cb4f4a3c8d9731c9373e4a48c17ae62b8e21cc59c791d8386c5256b05633d9507e1cf49aca2f395cf65613b15c57aec172628b9cace52c80b767b2bda47e29eb8dcaf69621ed330eda630b0df43213d73545acac83a03f1907e5ab966ad43527b4c524730ecffe9eb69883066f14c292af8a496aec5bf16e830e694cb4f6b0a3660fb2c056aee633e48b74a0efa3b09a1c3590310a4b1cad426e616216973db5646a4f0619caca43074c57a7318a2e72b4f5b91dcc6e2300d3b9a6e7c928080c4a2e9eb9246c0b5a5b0ee600dcb284ce6283f1f8a80b35984a2dd2eea0fd69683193e6d477b6830cdaf02d4a4a0c17315c690e62c0388ba3a070f858af71517a88566b1f25cca4fd6aebda439e3a98de6b357319f3e8378ee5cc68319c8ef6ba0ee1517b4b52d45e831741f03ffc935698a0fc17b1775aca7c99cc6c0141cf932925a872364186e62f0a03e8731490c8821aa2d657913d61d39c8e5014a3a8563f19f3e5a6b20e82a0f6b8b927e327ca0447e283f14cc5011e9a07d54386b0ee60fb4a4f86a4f9852d3d61dc7c3698ba0de2d35042f5d9abaf75501b56e14d82cd49b2d34e56b39791a0292c935410c4f9506a3b545f2ce542a8215119c5717c2fbb4c66ad9cac38e72b9a62d5b288be8f234c4a231a9daa23d340fc3b36a8830e6ad8adc9f26b59aa2a13698ad34beeec3e8c40b76509ad34e365253958aae164b91c533052d69ae472e4ac04a2e2dd969a1cf7c12c5c0ffe2dd9cc683f6f1a972c34e6ed659807910632d35aa2d4328bbe83f18dcab4d6a89cdd45f2d3d0628319aa2737279ca2f37f9ca58883bcb575149bcc0ce9352839445abb293d69e3d3 (by decide +kernel)

private def part236 : Box 0x20080040000000000000000000000000000 0xdfb4da130680a4010008000000000000000 :=
  splitBox 1 90 0xdfb4da130680a4010008000000000000000 part238 part237 (by decide +kernel)

private def part234 : Box 0x20080040000000000000000000000000000 0xdfb4da120680a4010008000000000000000 :=
  splitBox 1 108 0xdfb4da120680a4010008000000000000000 part236 part235 (by decide +kernel)

private def part232 : Box 0x20080040000000000000000000000000000 0xdfb4da120600a4010008000000000000000 :=
  splitBox 1 99 0xdfb4da120600a4010008000000000000000 part234 part233 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part240 : Box 0x20010040000000000000000000000000000 0xdfbc9a0a500284802008000000000000000 :=
  endBox 113 0xe8388ec3c8c033850d6c18c28dad0a024fd03320a4bff30fe1fba9243cf244d492a1b6b1e80f3985e72e98bd013286cbced5b521a09e524ad08d993d2f693fc9c3daa272949fa5066a89c3d9c6b1c00f3b1052591de92539b9c3d00f24051f30759ab6a254f98f4d1f25f76c18931cc565e947292a4062ff9ca569ad62802879422a4d7b49c3c5ba92f7b4c70f16ea475ed31ca59c701885a0c0a55a18fdc9e670f5f18c500c11f721c1e5ac28f941397ad27e3f7600e1b41e5ab6aff524a86ce1b2ca500eb559a5aa434c0beed5b8de2a494f9c93d6ad89f543670f980671305f09f23f7949293561ca09d487286e40b97dc7eed5b8bea5f749f879e2fbb10c2358d228073767127a8078c46d299ccb354567e91d38e98be40bad0d6ae91d49e8b0e49fb155ed262f37f9cdd1b323d527a70f6316837127ee61a0eeb55414b0e5aa26ff34dc11d722b15d6aa70d61cb545acb0fdde44f0faf239ce1a2c32ffb28b4386e2e63404940ce1b2c4d6868079eda73159f9c358c511a41fba4fce1f1cdc3cee234fe59693f5ab6947580cfa308d21c366ae8fdce52b019a9694737fb38ae24d67b48fddacb24d4e1f35747ef308c43e8521cddec31bfd65ad5d46ac0a52f386e56af13f431720e500e5f36acb574e1f2364e62b4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part242 : Box 0x20000140000000000000000000000000000 0xddbdbe9a0008c40002a8000000000000000 :=
  endBox 39 0x2147d2086301e31859ac25f749f901da46119c7bbcd470f18b9dab71cace6ee5f8a021e75a6b5862e4acb4372827631ac68080eaff942ed5d57ba4fd69a7376a18833164fbe701381a4fe605ad342ce7316904db1c0d1b2b4d2fb9c04e6eb4fa0f2d3137786e50725f3670e6eb017cd69f2bdc3728375a7cf5937fad34e633575a8203b08f40b9da77358565a6d7413a9352463bb8daeb015a19cc65a69b5e492a05d26adc2d3527e40755149e50180e2947500cf5b72abda60ea0b59ed25f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part244 : Box 0x20000041000000000000000000000000000 0xddbf9b2a0c0084084008208200000000000 :=
  endBox 51 0x1ac5f1cc8207ee417791863461565aa2f078879d80551a8280a32e8c0b57d3f2d55385ad5cfcf0506485a4f5832d5f7b5c5e9722ac8ded2e6346c9404dfb079e1479123b24bc5ba50d078ab8e03107c38e22701387b188d9969b07538897dd00f209d8c451642fbac8e3f18b7540335851b33914e22b80a2e6a3c1e45bae633f3bda5abef6994360656b0cb4d6279c3d44074a205f7527cb4d527ce5d16ec7f738cad34557079c81e417078c28d203c5a0380b00a014358631c9d82e2cf8e57305d6971bd5ed272d83ccc313059c2ca1a719969a0e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part246 : Box 0x20000050000000000000000000000000000 0xddbd9b2780008c40000aa00000000000000 :=
  endBox 141 0xc6338e630040f5916839abd093f4b11f3293ded2b2d50a83c4e32a1596020e9527cf6930bc8dd59683a4e32f697a13f3283527e0f1398ae050190429f9927ef697a1ccb23e5ed293f3ff83a4e62b4293e388a4fded32085e4821f46201d30a0aae4859c44a0e94128daa8f699a523637bb8aad4567114a0c93f551707b4d075692a86dcae735388bdde2c9b5753d693f9bc2839eae4f59cd5486e3b51097dce6b395d49251196850127ec028057062bc72761cc92f731cf777b48b7525eb3f98aed42e015b9ed2c3f69e9f84e6a711581c8f95a2c1fe123897cbeec57851d87a144078a42e28b9cc4beed420fd8046c9c0d3d32c5c23290b4f2b15ce630b763e1b15ce62aa39b64ffa0c565a7036411b3289d3d73d65abaf5b078cf5b9ed2a1349f9c0c1d3043d0c003c564440ddf1c2dcc50154398a5064f69405cc327b4dc16ecb417b6a98ba2ca66afa9256531ad61d2acfe52493cd4c5c1cc695b57dc8b2d0d003181962a15d59fc7314fcac65400dac3492809cc4dc473cb433f39507e3962e26d7b4b98e83fc1e4de32cfd6aaf69398b28f230092145d882e1282e419eb2271152b12474290b524cd21731964d6825e7524c5e7400cc496f1883e0a4a28d9cc2a4d47aa366095940567e2bf69fc1fe62f9f9d247b4ac88f992825e78f6b075485893dac33dc5892d5b4918446cc12358ca5053e6c495aaa924556f699805c0e167d396069f9254b0c5eeb2835ab6f69989292310a499eee1b5485a5051b304dc556d6147ca9254431c2da5ac3167230b0dc51b2f5b3989f9ca366f19eb6d2b16b9f84a2e731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part247 : Box 0x20000040000000000000000000000000000 0xddbd9b13000084000008000000000000000 :=
  endBox 129 0x731ac68083f0a10458c078a4fe3ff9c6562f1c2cfff1c641d27318519079104303c45ceb81cc53e7140507e6f5410ac88e39ed2d515a0b52d21741c4d2ea01235ad5ded26f349fcb013ff9c641e273192570a1045d86a20838cc517078b38c578e02a11305940ca4a0659456703597c7310789b5d6ab182cdfa0f149f83a649fb20c02884095a21449fbe8f431667aeb56cfee517078b78d5b8a36517671683399e0ee71f521a466733a90e6ad941d62b25041d2d4338b8303e074936ce6aa4338fb78d5b8bd6b17380946cfef0a1ed64a0c1adab6a431d9cb417b48ac5e46f1283356deb25f728bb9b67b883c4e069199612b0183a9c0d5c46cc7e783b97dc1d3428ec3e8d4248ce03c62e4949456271f521bc8b203c5ec3390569a907527b165282b0396329198e0270359cc91958183c4e0303c563313cca0e72d9846a4914fad54dfa0f1671a8760e32e579422f69581b0e52160e95a1b0e61adb165cdaf5303cb0de3f09fddcaf1f8562aa4f581ac65d8851e86201e2de298701387a5907f96aa5bf8e06c4f3f1cf6948cb18f698dce93f7b4cc61ed635aa32e30ed6147cb56d67e93f0c6c8f9835b1656aace310de13cce032464e1e52512dc58b7b4a8f5eced5b388af8f779ac2c3749fa3e5ed22b13fbb56e589bda51f29198e1e703379b9be356a42d2820e9489cb5549f83c5e87d20ef128d8aeb5546ca48d27e0e9078b510a1c05f78dae9f96a39c7d442de1c7d8af290ded2b172fb9c66725c82739aa48d1b31fdd806716af146cfee71f41bb03e6b09c0deb6f5d596b51e5a6a84549a807 (by decide +kernel)

private def part245 : Box 0x20000040000000000000000000000000000 0xddbd9b03000084000008000000000000000 :=
  splitBox 1 112 0xddbd9b03000084000008000000000000000 part247 part246 (by decide +kernel)

private def part243 : Box 0x20000040000000000000000000000000000 0xddbd9b02000084000008000000000000000 :=
  splitBox 1 108 0xddbd9b02000084000008000000000000000 part245 part244 (by decide +kernel)

private def part241 : Box 0x20000040000000000000000000000000000 0xddbd9a02000084000008000000000000000 :=
  splitBox 1 116 0xddbd9a02000084000008000000000000000 part243 part242 (by decide +kernel)

private def part239 : Box 0x20000040000000000000000000000000000 0xddbc9a02000084000008000000000000000 :=
  splitBox 1 124 0xddbc9a02000084000008000000000000000 part241 part240 (by decide +kernel)

private def part231 : Box 0x20000000000000000000000000000000000 0xdd249200000000000000000000000000000 :=
  splitBox 4490 127 0xddb49a02000084000008000000000000000 part239 part232 (by decide +kernel)

private def part201 : Box 0x20000000000000000000000000000000000 0xdd249000000000000000000000000000000 :=
  splitBox 1 117 0xdd249000000000000000000000000000000 part231 part202 (by decide +kernel)

private def part149 : Box 0x20000000000000000000000000000000000 0xdd248000000000000000000000000000000 :=
  splitBox 1 120 0xdd248000000000000000000000000000000 part201 part150 (by decide +kernel)

private def part115 : Box 0x20000000000000000000000000000000000 0xdd208000000000000000000000000000000 :=
  splitBox 1 126 0xdd208000000000000000000000000000000 part149 part116 (by decide +kernel)

private def part75 : Box 0x20000000000000000000000000000000000 0xdd008000000000000000000000000000000 :=
  splitBox 1 129 0xdd008000000000000000000000000000000 part115 part76 (by decide +kernel)

private def part1 : Box 0x20000000000000000000000000000000000 0xdd000000000000000000000000000000000 :=
  splitBox 1 123 0xdd000000000000000000000000000000000 part75 part2 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part252 : Box 0x3002000008000000000000000000000000 0xfc8c9f57401805020064018010000040000 :=
  endBox 125 0x400d6408920e8d02bfd62acc2d360e68764a2b1c2cbc2d575212323619cca70b48e9b7e83fc1d5543f1c45aba90fa1c2ca3f241cc3e3b38e62b5541bb40e63200d10afce491c987243b28278982f750eec829530c5730ccd2b07f608b1060ff241e620a09df0821f468182330a43ba51f52125716f585260548e98ae691c81972c8344bc2095988270b068ac0e0d2b17585a6df0e4be0d01fa6385b55ca3e1d9581cb4d83f8d84e16c29398c3e55a6be104320bc26080230e217e5a0314a40b1398221dd6b0a0a6307145683fb8e5cc581c4f728fb9967adac4c3bb18196aac595a698a43bb1cc4c5206582bb0750eea09cc565b59eea3513fbb045caa61f28fb400438e16165309ac5c19a827177ac0e72f9c2cc26d02400d15a6ce5f404ac5c7928292ebcb17608ce438c0b994e16e23100d11b2c0650e4ac5c5df1819edab170e4cb47681cc7a01a2ca460671ebdd4b6ab4d30f8bbe0ef31040da1dd7ab9fe43930bbe651f0520c56d4f814ab4d385ac080120c41608cf775a6c1fdeea47ba306c1f8d4a4c10cdd07f520b3f24be3025e35a682947cae599cbee552daad55acf18347125ee399eeb183620bd6e7bab8e588641f0681600eca60d3d989ad575a69785ac3120d89ab110529c2d66334eca3e9ed969a2bd3779c2d69b348ce623e5660e626ad87cab4da0eb34d5cbed67615ad54e6270b5e190811eeb41fe306605398947da573164c2262b068ad3669ec60c1a2b1b3988346 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part254 : Box 0x3000020008000000000000000000000000 0xfcdcbf50414607180061018400100040000 :=
  endBox 23 0x330d6368b01c4dcc3979cc66a38b5525f2c65cce1dd5a0f8b41ec746f57403b12c3bab4d7a16a741ecdbac310ee9889f5829f07b60b8e8d82f1f160f6d81bdc1cf1f65cba1dd7d1aa72064a16d53893a8395a07cb2d3549b397c1ce6ef0ee82160cba8e569a6f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part256 : Box 0x3010000008000000000000000000000000 0xfcdcbffa060205004160018080000040000 :=
  endBox 59 0x358dc3d0c8035d3c390cb011b7b97d6aed2b5a69cbda0489c2ef399cb572f1a51e5a68bbd905817c680e5e7332d0c0a53fc8afd5ff3dc51c617cb4d8c1a4ad67ab474a0b94e1dcc60ce2692f069bd4e582bdc55fe82b069b4040178e069a01da8eb0558db608e034d65b2d1ce132c5d6af2d1d856d2178e8c1ad5504ae6751f834deeb2d5cb83979e0b4d615c7f75a3b9049b72cad073020f0ce632d5d68f178da8621b82e07ca922d356a7276ce624db61aa0ace631ef51db1ef49b6aa30be37d8af569a947413cb1b41ca48b023b67ab9bed0562c34f0fd69ef91dab4d008c9474f7bdd63030ee4e6292357169a09d942e731271cb29 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part258 : Box 0x3004000008000000000000000000000000 0xfc9dbf7a80600d010070018020000040000 :=
  endBox 121 0x8217c7d1a865164640e2f147cc3e62b4d1a4309c080d3580ca455aba9165a6cd4958bbdd5b08101a67099606b57581cb19729ce6f58db20e618a4e4329152172c6500eb4d5aaa0e658b9c2548ab05681805e1052941844393460562e7095aba0960b1c60e4fb947d62a72f41b9cce399ce6f308b38c82407058e4260789c672f5220d32c651eab4d5019bf56629db985e7f7382c0296279cbd3c6616058ac69d069a09d06e72f641a83909f07a2c549b731756ae0d31ddb12e5a68dce405c6141a6d61902a8175abcd5358ab52569ab4d8e0ad22cbe11cb48630aaff0e4834d056d4987171850e4acb5904f174680e0ad439918598325e16aa834d64733c70b405ad3673389464618585216b3d83fb585257460cc22d6192820d3580bc318450573994e16b550699bf65a3834da0601606a1052dc34870b82c6b57412a02c1a69e46165828e4c9b6b4d47039324649b7185a3021633858296523ac5d8b307f5aba0dd06f350a2034cfd720ad5ff205e5211c59ec9077ac8afd282b536c124069b526260b996145b94c32238b9a92d231661e1834d69b0de407e6a7729975d486412469ac3b548e9c2d282a258fea6fd501c6fd491444d11c1e1866e72fa8fe30346064ed834e58ac606 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part259 : Box 0x3000000008000000000000000000000000 0xfc85ff70000005000060018000000040000 :=
  endBox 95 0x7d1cc801bc070b200dd4f19437b9cbce633974c56a339eaf0f2565aa4730898a5445b1473251d48aa174fbcb2d4feac1565b461569aa4565178680c56731720c5ef4a3a91d6571256616ad34c0edc07563089454e5f3db5656be0375a028aa87e398a51ce631846398af8ca2c8dc187ce431cbc5dee5d985260739798a63978bbd746a1b4680e5e733414ce49477a49525f41fcdef31160d692571cb95562a1dd052ce5d41c9bdce5e9478c230755958775a8389cb2930887752437ba887c5a0f6d4f49ea02e3031bf525eb4d695c5d18c0b5860fee67731bc6c19406c87663989bde0eca0255c47160695c3e526da09d06ed63503c59226c2d5a6936d02eaff6b0c8174808f965a69c2dac820e172d5d202925695ad34e4272f5c16af355d072b1562fad5e58a8f1662f8f95ac550dee825969a70b5ab8b1662f9b34333248c78afe3306fd51120415ac6e389b056582acc504b2d34e62d618f7ab4d37bc7fb4158775a86d03bab5788fb18540aa0ace16aff397a0ae57fad3502aa23585a566f74f6d1857ba804dc827fb41dad36 (by decide +kernel)

private def part257 : Box 0x3000000008000000000000000000000000 0xfc85bf70000005000060018000000040000 :=
  splitBox 1 122 0xfc85bf70000005000060018000000040000 part259 part258 (by decide +kernel)

private def part255 : Box 0x3000000008000000000000000000000000 0xfc84bf70000005000060018000000040000 :=
  splitBox 1 124 0xfc84bf70000005000060018000000040000 part257 part256 (by decide +kernel)

private def part253 : Box 0x3000000008000000000000000000000000 0xfc84bf50000005000060018000000040000 :=
  splitBox 1 113 0xfc84bf50000005000060018000000040000 part255 part254 (by decide +kernel)

private def part251 : Box 0x3000000008000000000000000000000000 0xfc849f50000005000060018000000040000 :=
  splitBox 1 121 0xfc849f50000005000060018000000040000 part253 part252 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part262 : Box 0x3400001000000000000000000000000000 0xfcb8bee8008a25800680000200000000000 :=
  endBox 81 0x19c6b16c4f1f01f3b00b82a829b9cdeb4d0e79cb4e6afa1b36070b57c9c27271778b165a69c9c39f079a30ed372c2c1ad6ae8252709c658bf16ddec67bf388836c1c61df50039e1df2e2cd5740cb0c562f1b35b4611f0691f80efb8e669ca4bc1c6aa300d398dea735727c6f56b1a826727b0a5544708ef012dcdee5f6b29b9c14e711740e5a98038e30b1fd5cde6a76b2b996697b5963fab97dccb1859282d37071877e0efc0db09ecd2f6b1975c1620a739abe0da328e8077d64f12adacac11270b994d4e829177b93e3faa065cca82990720db41cc5d758aad5c1c672d0efcf83e8dc038da439aa06e7b88b3d06ad318e227f51e5c6f5167a06641aad34e4e7356e1384a106b0798242827616b99432a3c5600b826d9696146828500ad659ccac2d050c606402a76d866c420ad5c7b7d075053ad4c16b41f5edf41ac9b70f2d44071b70d62082ef1e2cc331e5bd86735b4dd89683b60da4f478b3175056b5387960ad9edeaff (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part264 : Box 0x3010001000000000000000000000000000 0xfcf8bf8a068b01820602000200000000000 :=
  endBox 85 0x338d63e8e23701df7a1646815c177a883e72c2c6d91459c24db341f528eb439c926d9399ac5d032b0310e5a0978d6867f5399ad0e69bb97ce42819926a2ef6407ce0ab923a73372fcb0571cb94c14e5e3737c8071f3ad8e40f9c9db242d282721623c181485a4f5cdf2bed47ab275607ce6ad9032b5739082de0e7b80e2340ac278947489c8275a69fd62e8a44d545907770f2d663317dee26d9696b5552226ed80ea0b5691540cbcd651e59bed8564ed390df702bd8bac1d62dbd8569aac02be7b7936d85734de732a84c7cac2f8f7a08b1f2a36cddab4d527ac8d22808228ecddb13b4db281b626828e37693b416a81b906ae5f81623e54118bb02d5ac24db816aa2218c81a8821bb4df62ef949e3cb50aca0278b2260a4f698c1ad59ec1d64a0b99d65a725044c7255a6a8062768bbd42a2ef95f6b4d392acb637d8bbe5969c95a86e15fe7f98e5eafb1779cbe527cb4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part266 : Box 0x3020001000000000000000000000000000 0xfce9be14189a81880604000200000000000 :=
  endBox 47 0x6b1bc731b41f3b910030a63929c85842f0c935412873c3131c7d20273580124461c18362fb92d682b575a1033136cddab4d5279ab640cb9060b6abeda8a3a36ab9785c96b02e08192f0c92339aac5e37bad5e05bacad786a15405bb88da24dd62f1cce30f3164d3b2c5d032b5740b9c8658147741ad04e81549aa4dd072e21ba649b9ba65a6ab890205cba71ba5072b43837680b9032721711637240569a6fd38ca8f671149f1c2c9d6735377ca3d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part267 : Box 0x3000001000000000000000000000000000 0xfcebbe00008a01800600000200000000000 :=
  endBox 141 0x6d1cc721a05e1a4284b8851d64165b28cd5fe0e739998a4c0af4251e518974cdf60e71f3c6fb582a915ccf28cd69ae03a0c8039d3c392c1e661bc614feac115a6b046582c614bda6f5582cd42c0b578c525f95a6d07d83ccd6146d9ba569a3e7073ce84005d38e121df073836e2fd949cc3f0f2c3b652771194393c60530fc00605737c7bf6a8839cb1727ad3c6a4f41a97e64f1b90d47a0e76915c710ba6e0350d62d5e30f877d3c302a09e056b4ad69aaa039e5889bd415b2855052b11280c2ef1f38f2e073839e4039405072e2338b2077c1cf1cd4da3181416a50181ce18395fed37737b4f4a020e7741c4073a0de5a997ecc529418bf2d42c0c4d85aa5f93f2c6ef0b1ce2380d4358e8187cddb1ea60f2b2d62c9c94c522ef5e1247310562e0b74a3ad0e83cad35ca6e5558180302b383cb9cde82927f974ce4e0b17218bb02b542a6fb4edc82b50ab94d24b239c9fec027072711acd3b500c1ddee281738f82d683ea446388a495641778d8e480a02d03260751db94e737a51d69a8e0bbd00560e06b4313650aa0d49b63e546ec7276aac6fb89fef7787ca83b60ea50dc340b013fdac561a8397b1667acad35ca6e392fcb94e608b16569ac419216e6737dc5f9625cf6f03c9c8493aa0158149ee539cde07b7bb9cbdc869ff2fcb94e73781ed8b31c94e5e46f9ca61ab4ff97e549e4ff7e1cc6901ceb418a65ab98aca0250b711053249586e629303ab8e6f8ba68175a1c819737a3b62fd9fd4e3ee22c882b969a8252fd98ad66f39b56867f562ca4dc5deb0394e737b1650321378ddef6f3f29fdd9c308cb5738f9cd43332d04142501 (by decide +kernel)

private def part265 : Box 0x3000001000000000000000000000000000 0xfce9be00008a01800600000200000000000 :=
  splitBox 1 125 0xfce9be00008a01800600000200000000000 part267 part266 (by decide +kernel)

private def part263 : Box 0x3000001000000000000000000000000000 0xfce8be00008a01800600000200000000000 :=
  splitBox 1 124 0xfce8be00008a01800600000200000000000 part265 part264 (by decide +kernel)

private def part261 : Box 0x3000001000000000000000000000000000 0xfca8be00008a01800600000200000000000 :=
  splitBox 1 130 0xfca8be00008a01800600000200000000000 part263 part262 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part270 : Box 0x3040080000000000000000000000000000 0xfcf11e2975e011820040000000000000000 :=
  endBox 57 0xfa358e0328be1bb630f8bbc186629485c0c330eb68bc3c86114f0e2ef719a57079397ad5e0e48f2439313fd7c670e2ea0240651da0e5ec32d0d202f63a30b075500a93cf9728f4ba290b308c8028fe38b9bd4e06b21c5e1d3a89ce5a4ff600e3f2d5e30741e45de6fb392b80982706054018037a93fe1e4acfe27f93fe526af8c1391de9476011ff0d2e0faa170e8974e2e8a85d806e10330744e6a913986aa1705ab90e2c4a49549a3cb47393fe0f33dc477aa4d27f9bd5ac6d100061af080934ecb2f4138744e6741e673393ace268390e6cb2f4148f24e6a809393c1b9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part271 : Box 0x3040000000000000000000000000000000 0xfca01ea9608000000000000000000000000 :=
  endBox 137 0x1b8721f0821f46d1a01f3c71f3818344a3a527641c06b17839acd3706a9cc4c566115f01a66d393c650139a987d6839a8ad62e9a93d69a3cb9cbe6e906dc2d53029cd628a9c0de838cbc83bd82a673137d9c0c1b6d4b91ea5a95abb544e622c79656fe33860583a271f39ab207f98d560751e4ad14c22703285a007314e058f16a4e063899cda7f94b150511aa33d8c58e5a9a30b1877b1c6168c3867d3c68dd97c30ead0652398ad86b1ba43a2d65398b68d61c660639cb41a272783a2735414d0693988744e6ada380e81c661f39cd419a0d50efc0c783fc92b1f39c443be71f40bcc593668744e3e735791ac515c1cb177835518398aa8c413b58bf28055fa8e72e8b006fb942a81937dca1536ca7bcdf707355fb1f2d6266fb068c2ef0e39cc5ac671f0441b438c974e72bad5cdda0bf0ef8bbe398b51e0e79cc4e4e3e77aac2af40bad54e621df177bd07cb949eb431779bb4e62a179c96a395969cc67a1948203a673170124727bc7ce629505c6ab58082e4bf6a2b947e3e7821c064198302a787177b8cc2941b9cbd633304528ed2b9246509671a0589c9f537aa01d4629234a3ac661f3b687e1bed603392dabe06f5abb51625f96a5003e4cb2f13ec8ef4012c37aaa0d579ee225b83abd8cba6a473d20d7171d416b450cfc8f558c9c254166fb9ac6d07ceb57814ee4b397b55ce12e5d92c505cf536249bec10e1b18272c4937daa83e74e19037aa39e7aaa82d2831878f9607d6a4c90b9882ca029e5a0984d65a1df314b38c80f9d1933165052c112e9ac64c22b1996af1425ec6709 (by decide +kernel)

private def part269 : Box 0x3040000000000000000000000000000000 0xfca01e29608000000000000000000000000 :=
  splitBox 1 115 0xfca01e29608000000000000000000000000 part271 part270 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part274 : Box 0x3080000000040000000000000000000000 0xfcc4fed9ac8000028020021800610000000 :=
  endBox 41 0xdc3a0e20506014a4d60d6d6101b8f24def07739887541ba0d7511b47c0e4a7318e265270eeab8039964ed5f725a7f5edab47398a2071350bcf6d526bdb66ab998d01bdc55b392dcce1dd6516af3595456731733cb2b01bd0773988f243ba0c183babc340731710dd2a47293c1fe621b4c64fab88c598723181737a0ad06a12da302e6f50b9ba5845d1640e79b4e737c60c96a6e91dd974e293987e732831d44b2cf5eba0c7293b28e21cc6314874c35f02e4e629e39a96e67595a8ccdee72f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part277 : Box 0x3000084000040000000000000000000000 0xfcdfbe092de81982e462109820680010800 :=
  endBox 23 0x1945b11c59142ee017ed67f2505caa8391d3c7e7904eb2d71164721d06b017734ccc56721399a51e37db4cc9830d3d28ed4f5968f0c23b30d43567eb737987d6ab244cc524c1695c0bb72eb886058c3e8298e2ee4362797e5cca8379caae53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part278 : Box 0x3000080000040000000000000000000000 0xfcdd9e0d2de001828060001820600010000 :=
  endBox 143 0x388ca358fa2f8b23505fb680c3e033874683b512b9963021bb3968bbda571c9ce5ad0202e27f8bbdc8740e431cbd44b010dace9ff8c1cf77608a0add0061c2ef601b44711ba0bf508cd4d61bb4f66a6a0660f2947944b3534e220c56a1787003bb24bd86a3c34159875808c1c4c138f9cd5642e9d18351ca0d50371818e2707f51c930638f8314e6ada2b0b22409ff89fe80b3749c4e04733c9ff27fa02da9b392d456d4f1e1b9be47f9ba4e26b2392e49ea5055fb34b60ef2d15cda82b374b50e8030c9b72cfc3bae6d8e329475917c511eeb205d0568390d79c8649ba0e5203edd07541ac1dd0126e950bcd4f4059bf53fe809a0ee6e941cbc8b21c8d0206cf40ee961e47fc1ee3065d1492acfd28f0f0e59fa0ae1e1b0758b67271e4c60547fa8e49831c7ce4ec02c8d03d0900774def1fe4e26839729c4ff62ccaff393b955ca64ff791ca6b438e32713415ad5641cc72f413974e3089ccdcaada34102250b21c4e40493ac9fec0380d4051e7adc6051b6f5d2fc8774182ae20240ef357c10707769eca176b1a847017ea119ccf07f51cb57e7baa8960fe0038312d2d6b0b4f5abe15f733862683c8e85472d476b0b58743a0901c94bf3399d47290b389a42e733a3058d949a2ab2fc974e46a846e0fe6e9403c90b62ca85e7ad97e51b6a3905cc7f741c87749feb00775ac83fcafd4959c95cce3a3a3026fb4703272d1523307f9632d455aab58ac240f2313e72a964da564bf3fb9ba4e42e43968b07f874e72f4a0c5879ccaf774739bbd7c681a840c91ae11a961d1b6d3b1a6ad0d02e1dd0afc0432c7a05d68a8839562c3ac54dd26ef5a2cb458dde809 (by decide +kernel)

private def part276 : Box 0x3000080000040000000000000000000000 0xfcdd9e092de001828060001820600010000 :=
  splitBox 1 110 0xfcdd9e092de001828060001820600010000 part278 part277 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part280 : Box 0x3000000800040000000000000000000000 0xfc8dde8928850062a180001840602000100 :=
  endBox 39 0x408dc328a030073171164073c82b393b80e43508c0754e3ee579032a4703b98151ff291c04b39b528e52783cc3991d8a02547f28cda42d6138fbc86ef4fac035522abec9b63c950b949e82011b239c1ce2d5293838e388b002bd8c0a71f39a8b3e1e59c44c0a0df791eeb20ee0f28393709c9c1be1d9948e6055049c9ce63174c1cef23400e16a189317e564e1dd48148b2d151cf30bd6322d596326ef0ecc735 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part281 : Box 0x3000000000040000000000000000000000 0xfc8c9e89a88000028000001800600000000 :=
  endBox 155 0xe23c8fa329023800e70efab88178e3e9473159cc57c591acb209524a5ef315a3b64a3a91d64374a7f67369cb505661d91fee6f0469bd638fbd01d781ae0df069c1d74701a60df3fbc807239cc19729ad5ce2eb03397b90f83a0ae03650771bdd67f0770eea0a4e621dd97838cc5d3396831ce628e40071f3f4d0774ffa7f5a9e6e940bb53e0c38f9cdd3202418e0d79a8441f0470e32ae4010778ba6b3d26d9c7d04e9478f8e71f368b0a6368936d2031ab56aef614a3b044186a02d060e7bd5d0329253989bb65a0873d68b073c7ce3e7839e7315914828ec6131f39c64e4ed03800c7838e72d2708344a4f1cb4afb2c5dc8707f3688f9c38ee03900c781a2c82f0e3b989e71f2f098a565b1b7c186c49965a839413af03e7963271f17794753ef0bbd5c5b17c6807cee0238e3d9862b2705d9cc502e8376a188f20e41760e79072731398ce3d96069190739cc5d07d1b481149b27f58be941398949d0448167b2505cce2c35a39c145ab236d8be9f55a9be0d6585aa8099c86e654a0810e0259bbd8623a162f839ce63149e398a38da2f87e2c9e0ee9cc500e733906e1dd920e527593acf57c398c83972fc4bf0eec08e41cc62849cc6399cb19126b94dc72d650608775d0791f07d1b4073b40d23985e93d389877527b1c8565334c4ddee670eea024deeda077560060a066725a7f55f66ed5a0cafb5a1a0665a1b90be399e461abed3fe2c357e9c94e42b2136e389a5052171c4d606a10329ff95f60c1376c93d9686e40746293ad0683f9b7c17ed03911839a628094faa91ca4e882c0d4206549b39956560b95a1860e03bbdb605c802c25ed3137797e67aec1fdcca0b96a180508cd3d721ac5d682e438f7e9ff4ffd183698899e0fe7bf (by decide +kernel)

private def part279 : Box 0x3000000000040000000000000000000000 0xfc8c9e89288000028000001800600000000 :=
  splitBox 1 107 0xfc8c9e89288000028000001800600000000 part281 part280 (by decide +kernel)

private def part275 : Box 0x3000000000040000000000000000000000 0xfc8c9e09288000028000001800600000000 :=
  splitBox 1 115 0xfc8c9e09288000028000001800600000000 part279 part276 (by decide +kernel)

private def part273 : Box 0x3000000000040000000000000000000000 0xfc849e09288000028000001800600000000 :=
  splitBox 1 127 0xfc849e09288000028000001800600000000 part275 part274 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part284 : Box 0x3200000000000200000000000000000000 0xfc861f59a49440000141000000260019000 :=
  endBox 91 0x1cc6e1b4711a87c01a20d356169a3e7315b53e2dab59c78ae539a9ed4d4a0cd456a89fddcbe1c31f3bd8b538c0e3e75a6835d486217c49e9f16054a4bc5de5d19a05811c3fcaf89620de30b31060f6d3d271b10672bb53e72bc1ee618b57d1f3311c6d3399d1da8f9303a0de624938c396d03d090073503339049c69195a69c4cba324adc8272f5a6abf65a9938ce42b4d560e430f9ce5e4e387ce93d7119406e95f647182b4db62ef30398ada0355ce412718774f9228d82d24ad614bd4c9c6d0138e37bad150721dd2dacb136a8b0a53fa3e537ba78fe3e0ca388c8075d69a0e1495ce5d4a09cbd6ab41fdca65b583fc0ab2fc82bd69b1839a6e36937b82a4e5e0e141bc1d71f3b28e23389a18ac3a6925969b1854a3a8c652284be477a845462c4330998ad43b02a5eca0b95a6b207c99aa20a9397b387bd9a969231dfa8c528ed51946307f477b4de3088384c56d4370e20774c3b1c64c56ac2406db967e72f5a29cbe58cad3471f2845abf07f5a6b8e605c97e569a62b5f1ec47169aae02ccc0ee398062493476acfe0ee37191dab3f2c9c8ed83f82cce5ed33815ae3b72ba4f45de5d1927ab4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part286 : Box 0x3004000000000200000000000000000000 0xfcac1f5b80f448000140000410060018020 :=
  endBox 81 0x3d8ca278e62d359c711e4581ca112daa05502e3e7069877d3d72c556567351f38344e43149d072b2370c4d96825b5069a93da8641edf399d6ae72f315acb649ece67284ad5e7b79cbdcbaa3128eb40ce03165a2a0e4c530724c57370d23400c583920d17c19c396c613393ac6647ab16e0fe61d30982b68c0acac1a6aa23814d9602a1136c9c0d90626ca150568724e5b2c15ea6c4d8ff2941820c0f2cb4c528299a9eb57699b0a6087d1a0591cc7b2ca0b414a0dca12513464c0a9729b04525e4ff641a86e0c230798e5e5270e4a78c5996af079397acb6608b5865199cbe303147560aa43208259232a4f37ea85527a6116e0e3300ad04a39d93c69e3dc657f9fddc8272f464c0a772bc70541ca025a0414c8396b1c92f167a4ad9c6a1a058ac82741c9c641a61c9396c0d338cb4106993d2e5d73693ad8be93d41b9b6e48ca89d27a1c981a6a15 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part288 : Box 0x3000080000000200000000000000000000 0xfcf55e4185f441800140000800160018000 :=
  endBox 95 0x1b86a1c06817c0eeb489c02f5c41f282de38fad3502a7e5a0d2c4f2daad3502f1ba569a0b94a3cb4d1f29bbe0608f957c7113c30898adea73164dee9d939782a66d1d049118497a46657fb8e549eb4d968a91957fac66608a89d69aa3d1f29cbd69b01565aa96d4dd2f5387ca61d38ca90e20f9554596c5fb177b9b4e3e5fb942ad5f817af51500a42d282b2278e5fa3020b1396a89d47a0a9942a2ef5969cb4f85969c7e690bd4d6ae71f9a42f53177b68b23408a13fda5f24dd04aa27275bd565a682cdd04714848cb99e37b9cbd27a7e79ea2b4d390a89da9b0464ddea273979c4d44f380713969ae81d07134f6cd49695b975ac22ef8e86b0d0798c186a4dd27f59a7a7e74e0e82da9606a3904a6e9508c8395a6ce3b2e8cb4d377bdbda8550f85c1656b57732c4b54a382a630f2d34deeb293159cbdc04c0c52b2d8f92c59729b8e4c220a99c72e535d165ad5f8dea05505dbd4c1527d7a0f257b6af9bd53c700e5e4ff69acc595a682be83eb4d525f368b23d4649e9cbc9fee83976485b99d69b079397858e7b7c1e4fceb4d0d2cc4f73396d4fee839 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part289 : Box 0x3000000000000200000000000000000000 0xfca45ec1809440000140000000060018000 :=
  endBox 131 0xca281041cc5b47d1f0690e272d34db671928a949da0700a2671f81bab4d6b0d18150886a41ce6e9942a72d073b48e22300d506b940d2b922680969ea8a49db25045df20255fad003060e49ef549eb4d57da4f65a6c3e506bb10b178182afb06a87547932ca4e6ab2d06abe8d4142c5df18ace06b4d8b6a9fd07387767c1a0671c06d1d0063935e5a68764e5b41f569a2a78e5a71935587655483ec71f3969c9e177a91661b9c0d6862ef396c0e306ace03d872370b4d6d1bc6801aef80344e4f184d4271af47cab2d5a0d07f5a18f9c3ab1474e320dd85de0e37c1a57184d602b2d315838cf80e99cbe580978d6ae72f9f47c1e4741bc071ad5e71ca48e30a6290e9837563702e45ded67904af7150f9b341720bd28583162708324a3a7196e047716d58561c31f383441ae1d39bc1f2c3e7068876638cc10f82c81dd8e6a62b355c9473148f943bad2035584068ac5647cb10c38ed239cbeb1547cb10d65b0f956831cd58522ef068b70aa2382ef8baeb2b2859c0c1c671f412c5130719cd5427310c5de72737acb2d05c82ac1c7043e8f6400e2039db8491d18757fa51d6565130ee8375483f0c22ce2d5d6a7460d3d2b3183b9ef6302b014a3c606149a3bd60239d9656a0b540b6b307da56a31477a51d6af18196028ef6a8c5b55959cbc3ba51d9b46a14270744a2a3e506a8e4636da46547693d289942e6f1b451dc6db40483541b27c983ab1bf588071a001d93fcc92f355cd4b83ca4f504ab158d9b079413b0441aa7f9 (by decide +kernel)

private def part287 : Box 0x3000000000000200000000000000000000 0xfca45e41809440000140000000060018000 :=
  splitBox 1 115 0xfca45e41809440000140000000060018000 part289 part288 (by decide +kernel)

private def part285 : Box 0x3000000000000200000000000000000000 0xfca41e41809440000140000000060018000 :=
  splitBox 1 122 0xfca41e41809440000140000000060018000 part287 part286 (by decide +kernel)

private def part283 : Box 0x3000000000000200000000000000000000 0xfc841e41809440000140000000060018000 :=
  splitBox 1 129 0xfc841e41809440000140000000060018000 part285 part284 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part292 : Box 0x3200000000000001000000000000000000 0xfc861f5b04824a200000a08000000009800 :=
  endBox 117 0x398e2370f23d0f63500d706ea704c19472b4d1668f94b83d039ab4d2d7c34b58dc605ec307d2d7d1836b29aacba28ff2d7cd510e6936da570254142a175a6b58c40355485f127a09b925e2ef497cd5f2e8b4c6720938c396ca308be2581cb608c8f96a5b4d4bae4e34f7cd2b6afc8f96a78f0d1db23e49729ef72bcd2b271b50c4353e728a80cb463e50e6b0d60518f0d1ced3739aac0be2580a10c3c4e34edca4d72bc60604eb17e6919c069ac01cb728ca17725a93562324ad27b3508e2d1e0e4a8ace06be2c873383fce491f39cb563741fc39292f8c3abe201e51f8afcbc692b9a468148f239da6e7350e68345ac7b20ff187c59a3e77c1ca34604dcec4130fb07cfef352cdb29190e39cd66abb4cc1420a36519c4f0e5ad02d35a6f0f9c3928171f2c3e7621cf650e6b10703315c2ef30fcf5d5a69cb66b0b5f0b341c21d33849c9560734cc586a175a6838594441605a6b4072583920a9942e0af060c1cd5817c59eca1761b9c94e66d40f9659ea85cbf20639c9609d50ba38c17593c1dd7b2b97d20e8c99cbe1dd6afc5d1720acf43ba7336e1a06b03bae22382ef6a6ce4b69db53d27a92f8ba28e2d35c73201d40692b1a7ce4b8c282ce166a80c13eb4d6b11c4a0c5a35a6a85d49a919497cb4d399ad3604fa39e302ad3415a725 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part294 : Box 0x3000080000000001000000000000000000 0xfcf53e0305e04ba00040a00000020801800 :=
  endBox 103 0x1c86e1a471124591780d9cc45625a4f549a4ff41da06cc4451016a27969aa3b6005a71c5ce6a7bd945205b497987dfc7d05df187c5a691d497b501b38e6a2c78e6681762ccb4d5959c95c0741800eead5e3818b4cc2338e418a3e591fe0c55d11c600e06a399caec5d38fa8e63f3af00bf9a7b1856258f94e6746145ded3d4f4d18151cbdc4e069c35071f902aa3938b8f9413b289d472835591805f0e67392c9fe1b3054b9b61699c657c6b124ae6f942ec5983ec7f7513c5d350b9846169a3fc3ba940b4d18681c027fb12e0eead35a5b0f95c9728a549ed2d98663e527fad3563317e549e4ff6a1fc6b1c4512c4c11f298a4e667034a160500ca4f526ad34e4b07d91aab011f2ad5cfce4ff515c9ed7bb97e549e4ff0b0c7031f29cce5a6b99586e1dd392ca2749793fdd06b1ee3026583e90b515acace2e7255d20fb2494df62d3492c7bd8c0a934df69e41f651fad349feba31762e982d56af28fdb8591706a10172cb4e6abc2c0e579452b4d2c182750360af4a0c81b162c92f58bc2ef51d86cdac6705df1c7c17eb2d91db239dcdee6d5a69c0dac497c90b59698a51cf2d3544a0b5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part296 : Box 0x3004000000000001000000000000000000 0xfcac1e9b84e04a200000a00002000401800 :=
  endBox 83 0x7b1944f1105d169ad23382d35b017724ac39e3e75a9c0c141b93de1d9b07d49eb2d5f1a8671f0527c72d512ca3f58b8f9ce131c0d65a393966282751fa935f0527b596514ac6e30a92f2899bf5a5b2c6d832c5f6e1a447acb41309987c1a71819cdf18569b9b9d452513396acb60efad05c41f3ba0711063a8a6399a806835bdb58231852bfc06302cb13d49e5274e11c6e1e4381af80d351cc5e336c9ccc39323d4db20af838ea2b83bea3f37ab70d23c80d1902a83b581c7d53968b4c1a2c0340c818a68c2ad5c3727f53968725f08213c3130630aa25384944e0ff2d5ce5ab2d82c6b41512bd5e3969b006d9a660673fac616699ac0e314834e0ef8b4db8691a0625c0d1293b200d38ba707f5279454e5b1efc0da0d3625b50e22c87111f3c0338c0944dcde72d6412171ccd683058ce12b05527ca4f906ec8242e4979c5ce6718198bad4187630f831c1a69418ff681b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part297 : Box 0x3000000000000001000000000000000000 0xfca45e8304804a200000a00000000001800 :=
  endBox 137 0xca2f1041cc5f47c190701b830298a569b1454e068d58deadc039e41d9cb4e0650981460ad37abf85c039ce5b15fca26719368ad34e5b0b4e0fe513415c7096e1a07005deac3c8a139aa26d9598a0ad2469470e6cb1b1698f945a724451972c6d44a6d905ab48f21d00d540dc1ee5a6b16d1dab4d942e2d36a8ce5f0578b4c7272d047cad224465a982d43a66d9926a0af791586911062128e9c2c8b4d1f2bd76491a0edebb2c6d42f2cc4e6a82b59ea48cd43248c39f031d89f0d5d68e7bf06ba4d528e71f817ab150eea4453847104f1b64e3ef759426b1b0588734e5ab4d8f7ef2308ce3d883b944aa3f5a68b4c39eb22d1e0df82d5036e01c4650b9a6500e1cd06a9a661559f9d48f206c1c707b98ba0e3512a8fd69a2d306ab4f60e683445a6f63805c370b4d6f1c830fc3e716983441aeb20f9da97313c1ce91d280c6d162cacb57c51dc0e72fd987c1cf3780e381ce3e738bc91d6e1c87c1a87d1bc6901bad3d87ce2ef30f8b4d65b0f9cc260e78c260d183b20e78dfaa3b06c8bbe5968b4c1af002d82ef37ec3e737eca3b40ba8a54773780e787cea2b303c0e75f0e5b039c7ce7bd98bf18358da89c3be0e7821a0497c0d158db17c5de5275f038f28a4fee5e328aa48a2747ccd2b4f7936d27ae67945292f90160d16e1a46420ff285525ea3b28a949dc07910406b839c4b32404e127fb415b55e58a825d1de83b737c3e50688b4d48f2cb53c6b4136f8b4c1cef23880e75e01bae5fa0fe51372fca4f732a93e396c05396ae5d362e9c24e660e7 (by decide +kernel)

private def part295 : Box 0x3000000000000001000000000000000000 0xfca41e8304804a200000a00000000001800 :=
  splitBox 1 122 0xfca41e8304804a200000a00000000001800 part297 part296 (by decide +kernel)

private def part293 : Box 0x3000000000000001000000000000000000 0xfca41e0304804a200000a00000000001800 :=
  splitBox 1 115 0xfca41e0304804a200000a00000000001800 part295 part294 (by decide +kernel)

private def part291 : Box 0x3000000000000001000000000000000000 0xfc841e0304804a200000a00000000001800 :=
  splitBox 1 129 0xfc841e0304804a200000a00000000001800 part293 part292 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part299 : Box 0x3200000000000000008000000000000000 0xfc861f5920d041251000005040000000000 :=
  endBox 47 0x330ba2b8d40b0459abc03460ec87243b3460e618b9043527f941c96d5a85e1a006ac1cd0eaab0b29878aa4d92171b443b20d565160471ac51cad362daa8fc5deb4d89c68098deea256b0ba31b6d27a5b57379c4c11b174567e6f793d24e3737bd0e63706119852e5930f83441ba0e1962718ac3ba3c1948a62b069bc8e22f80d306facbe523acc543eafd910054c1a151ca9093d964e3e79ac393c70330f9c0e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part301 : Box 0x3000080000000000008000000000000000 0xfcf51e5125e061a51040005000000004800 :=
  endBox 45 0x370d43d0e83001dd57148160b38fe0f94da693d8db6727399cc5d6a6cf6f7b9a474b6a61160a987e5610172474c3e3e5737936d233307cc565b562e9c9549aac2f073387ca7339a5f17e589707b5a6af00c5969a0af39698ac7ca7bd9866c5d5a6987dc460174619c5b54059844e6aa151608b4d78614c62b27f987e3fc9c86527a0ed42a2d3947abc3888ed944ae4f4a3ad3506a81b60169b0b4d8b341edcd6c15619a8a56aa4ff355ce41619a93d8ba92f405b68d600ee028b95630a0998c3c1ad20e61130f9c94deb18149fe62b96262d3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part302 : Box 0x3000000000000000008000000000000000 0xfca41ec120c040251000005000000000000 :=
  endBox 129 0x1b8821f07d1b46411828a949dd07a1ec51dd07b497877d27aa29073b58a29927a6fd8e62a3d94771cd547ab02d566999c0c12e0e78e626fd0efa4f4e6af4381000375a0073b176384a3bc5de51d531076709805a6d3309b996595a7ae30e7319cda51d3fdc70341d9cb41ceb29907651d069b20b4d9866c5d1f29cc41ce50b1f2c57960aa0ec1ba0e77a1d0641406a0e330344e6a7310eab68731623c83951e83643531ee413a3c94049c9e0689cb43aac5f9cda9473989c7c18f1cb4e62e235071f858272d068ac0a39947ab4741cad1e0e7acf6163ad347928397915c7a1ac398a06e1778354e41f2acf660d8b055fa81b51cc6fb710e132cf45a6b2941aa06c1a6afd944e2d351eb50ac20ee17783547cabe3d8b61c950371bed4729fd8976a0137d9a6627682d582a1cd515a50660ba8ad1cea393a18672d363067134fea8e5ac60acc5d392a06e37d8aee1ee82b4e622d3791d07a1c06d1ec06ab000d950bc3cb526a0ec39a2d3390ba31cc547e6d95a69b0a3987968156169cc61e59c0e59e9cd439ab8353e398b9bc3b20e33819c7e0f72c5412ee6f41c9b343b20e3651f05f01c6a2594722ef39acc15398ab80b58582731561642e8c81541da05649ec81b51c838e069cbc2c907d8e62e3d60d81658ba1df4129cd5076da0f1502ae6b8f7e1df1679c7e0efcae0b060de8b4c18f02d5abe7350ecc10f83680e7650e1272562ec73162ec2d3947f074cdf62d33988b4e1f3a8fce620e3 (by decide +kernel)

private def part300 : Box 0x3000000000000000008000000000000000 0xfca41e4120c040251000005000000000000 :=
  splitBox 1 115 0xfca41e4120c040251000005000000000000 part302 part301 (by decide +kernel)

private def part298 : Box 0x3000000000000000000000000000000000 0xfc841e01008040201000000000000000000 :=
  splitBox 5279 129 0xfc841e4120c040251000005000000000000 part300 part299 (by decide +kernel)

private def part290 : Box 0x3000000000000000000000000000000000 0xfc841e01008040200000000000000000000 :=
  splitBox 1 72 0xfc841e01008040200000000000000000000 part298 part291 (by decide +kernel)

private def part282 : Box 0x3000000000000000000000000000000000 0xfc841e01008040000000000000000000000 :=
  splitBox 1 81 0xfc841e01008040000000000000000000000 part290 part283 (by decide +kernel)

private def part272 : Box 0x3000000000000000000000000000000000 0xfc841e01008000000000000000000000000 :=
  splitBox 1 90 0xfc841e01008000000000000000000000000 part282 part273 (by decide +kernel)

private def part268 : Box 0x3000000000000000000000000000000000 0xfc801e01008000000000000000000000000 :=
  splitBox 1 126 0xfc801e01008000000000000000000000000 part272 part269 (by decide +kernel)

private def part260 : Box 0x3000000000000000000000000000000000 0xfc801e00008000000000000000000000000 :=
  splitBox 1 108 0xfc801e00008000000000000000000000000 part268 part261 (by decide +kernel)

private def part250 : Box 0x3000000000000000000000000000000000 0xfc801e00000000000000000000000000000 :=
  splitBox 1 99 0xfc801e00000000000000000000000000000 part260 part251 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part306 : Box 0x2304000000000000000000000000000000 0xfdca919fe2c608000000000000000000000 :=
  endBox 43 0x7119c68198721f8064832cf05f16a62bf9622c571ef984d6ab315d5fab1126dc8f50dfacc47de3ef9dc061b5664108f7cc0ab31315acc649ea98b63b8b278c3a0d11f7936e3ffacc568e83f627c61d38cad4ce3324ace4eb2777167f20bc1a63ef3ffc82f49f9cb5907717c30ea0466a1ac6cc563ad9ed2b4d417834d30271cb4d4008725042907969a2cd49fba893f96a6b4d069ac46309ad4d986009c72d3459ab53408a0841828817e6627a0449c6b4d627c4e349fac9e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part307 : Box 0x2300000000000000000000000000000000 0xfdcad195e00000000000000000000000000 :=
  endBox 153 0x3a8cc3905236f1b4770c57200507e0d106db40821927a1d5066b1883f8ffe93f83fcb4d695b5147ca73581bec0320af198571870e29c64c561d57e1b4522c8f5582acc5cdb04c53ea70b4a3bda6471a7c5856719309a91e83d8f953ea93f7714c1f7c83130faf04b3969a8213158abe49fa086418ad0c6240e224fddc67170760e4ea6184e30fc60e09ac1fd69a8f5587837d07f278d69a72d760e32b31812e8f5308837d3c70144ffe8d10eba4f65a6837cc260998e5aa40f0507eafb923ab2748cc4e37716c4314840798462719c6564ea31943e8210ebc4e31f7a4654632d34e3271106fa046271a4f4e5ae23b0f23b8c8037d233138cc566115f11df34956a7187309ac16671405f16a727de30e935271a4ae6abc61ce168ffa30ae6526db51560ab5389c68f552166324758b6d3d495b99630fb48e30f279d6a69352718dd647aabedaaeb53271bb861f9c8692b068a0fc1bed01cb5485e0e171879416b53626c1fe5a9a7de8c3a4d52333515f0711dc761485f0c3aac184d69b28252269473e3c6d15a68fbd84441652afd578c4b93ffad34f061cc4b93ffa3d56a71879106d169aaf1960f183598c60e4faacc6489c9471f7984cc52e431880208b2f907ea4749acc411f7acbd46283f928e3ef5a6d183165ac154664e3522b4a6838ad147de4e3407a0bdc8661580eaa90aa0f9526b461c9b6947504ca33a30e91367160aaf18ffeb495a9c8f55b148641257460d26ac5b2f6a0fd7426dcd578c3a44564e91191ead572cdcb05519b51507ea314a3cc27400a3fd69a83187832f8c6320ae02e41823bf969ac515a6c9475a2ad4e1f7ad0c8251e5a6938c1921c1165c6c75a6a44d28e0c99226947589cb3f (by decide +kernel)

private def part305 : Box 0x2300000000000000000000000000000000 0xfdca9195e00000000000000000000000000 :=
  splitBox 1 122 0xfdca9195e00000000000000000000000000 part307 part306 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part310 : Box 0x2284000000000000000000000000000000 0xfdd233db566508000000000000000000000 :=
  endBox 75 0x1b8711a46b1ccf24fd6367335a6834c196b42c0c83db60b4a82cbdaa4d7b4ad343922cd927eb4d1dacf695a6a4fcf4591601e19b4e0bdb04d8863f1505cc4d0bd8b267b4a934df73da543aa47641805a4c7330e28fc5ac30ec6297b0cb25626a4fded2d61bee30b2934c26b259842f69526b00a82d03f1166c1c9399cd3b515ad24182b5381821c952167b207d68e83f8e5ec82c0d6288a81c95f050bcb47526b92c7e29c28fe7329c4debaf659642e6751fcb117c1507b2c8017258fc5c430ec62b590ce4b7b2bd965a682edf05418570b25ed2a3f1f8bda662da8e567b3144586d6338b4074df049fbd7640f96be7b6ac9e302a035a6ac163e0ad4e3023c360ecc515a68b1d05ef5d9886c4d49fa88ec318a033ffc1c349facc65a6870e49fad35ccf070d662b4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part312 : Box 0x22c0000000000000000000000000000000 0xfdd2f971778000000000000000000000000 :=
  endBox 33 0x1b86d1bc671cc0e6c93706d8325ac5f018ab4d96669473999c5c7e32d2569a61d5c169318156769251f8ad36492bda47e3036cc0b0bbc15f174526e2ef1f8be0d61c4e417a03cc3a62b5c0c0ab4300a3f969b0691f8a68b4da0fa69f5019bed47e3c351fc9ef1f8cc2b1e1a28f6961ad183037b13478600793de92583eb580b983a61b1969a947 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part313 : Box 0x2280000000000000000000000000000000 0xfdd67151540000000000000000000000000 :=
  endBox 143 0x3e0c807e5606017c1f8a48e1779cbd8c65127ef65969a0c58c1ce399eda713733a40a21c4cc87b49ccd27e3c3a0f6f6d1ceb9568c3ad1d3ea28b25a832d3073126f200526f1f85ed33d940d25ef7b2ca3349ba914e5e7336f1cc0e9cc57166a03c196a22f893f6a1c6db49a8bbcf5b3da60fad5505dc7bd1afc605a86923177a4fe4918bbd94441dc5a6b78e63a85d9968e6d362ba4fc3a6aa1981bf04ecc2762ba80d3789725d169bce6f6a8c9f58c1ac452025d98c3a4fe1cfbdd49b65d91779f26053a48d4629011778b3675180065c61e177823c59a5d9047cf6949fb10780bbd8c6a5cc5704ec5d9588c61d667461c12b07704cd18562b82763061bf15aaf8aa2f0a31948ed3f6aca48d26a7e34fc0b716be30ac0f49fac3e8c3bda5abb185593a44e6aebda568f183927ed6370e2348ca3682ef4e01920cb26dc5d9610d1876a5b1449b693f89b6a3f512b681c1859a0d55a099f251cf921cd2eca4fd007aecd216b2b9bc1024c13e49a6e62bad45a52937177cb5149f8355b4510dc392ad361dca4fd6923b996765d1060ac1e397b574772b3d0e6b566583b59439ac5705c8ee590561b45f0e26a039abab4d0e99cbd942e1cab3db4786c5b501ad35445a9c3c37aebd9659ebdd658dc60da96b41bdd69b399c77ec3962b976527ebe35967b482e524af5d9947117c613c0b90e997096313569af6584eef6d62bbdb66afc1a5ea6f659eba0b9947eb47540fc125cf6d4f4a445cdef5762bb99581e2c39ccb1f3c586da328a1198a27c95a98f0d69a1d3511a9724fc59aa43566732ad4ded3251dc96c57859adc3203e526dcf690e692be5a9bda5636be32893705acd3149f8b3569ae5f859af75969a93f (by decide +kernel)

private def part311 : Box 0x2280000000000000000000000000000000 0xfdd27151540000000000000000000000000 :=
  splitBox 1 126 0xfdd27151540000000000000000000000000 part313 part312 (by decide +kernel)

private def part309 : Box 0x2280000000000000000000000000000000 0xfdd23151540000000000000000000000000 :=
  splitBox 1 122 0xfdd23151540000000000000000000000000 part311 part310 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part315 : Box 0x2208000000000000000000000000000000 0xfd9e1335051040000000000000000000000 :=
  endBox 93 0x7a1ac720a46d007e5946a05deb3d81a693f0e6b4ae6b3a505283138c1a28096d164791232d678bc6d5f06a9b8d518feed4f9aa290ba0d2d4506a92b649fce43e0be0fe43f23c389b61d94f7a4fd43aa47167c9f5728a936086a1480e6b083e558056f0b0cf44eea4fda8741ddee307d473ce398c1a3b60e309f495293f132936de44edca178c1c6d96b3a40a03407e9927e5d140cb08a39853639158c829568af698722f69965e58280d02cf67b2a3558bf18158cb0c506e5d11f11db012c512a3950bb57d5c04ed183050c60e6abac0e47fb57c14b232c54293758cb59659e82cd27e1cd49fcd03383f95f143b181c19680741b9880cb51fce6d725abed27f07b593a8fe7b6c1ee49eac9cc3aa2290ec350ce134630e9c2cbda2d54c183b068d27a5d5302b9be7b49875472a173d1ac5f142e93d054c38f62796ae001c60cfa2d6572ba935a6b28ae0ef28e415a88460e160aca4dc27f738584be468b5349c61c35a2cd4d271872d42ed430a60e59c2c1a6ec2906fd829ee4b5088dfd23a93d614c7f7303928e838c605acee4b699bda4dfa7f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part318 : Box 0x2210200000000000000000000000000000 0xfdda999d3e5215081000000000000000000 :=
  endBox 21 0x5f140177c81941cbd107987cab2f5a6a51c5ded61cce2f1ac6d6a6a251fb8706413ad3568441905a6af08c0704193136d5e2f6d2eccaf1060c0c95a3caf11f2936d64f136c192da35960639c4cd5b3db4dee809 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part320 : Box 0x2214000000000000000000000000000000 0xfd9e9b9b0e46a8000000000000000000000 :=
  endBox 83 0x1ac631d81fbb205c2d0e22d3583b24741a292ba0dec094a0855e7b4bdb495f18348ea80d03488e1f09415a1257069a306b3d166a4fe30728fd407034564ed37925e93f6188344f9f3da52570715a4a4bda9724bd28290302608fc1c5886f6d069a4fded2d02c760e4acf472717663e7a93569ab47389c2cd5a6a78f2320b01c4d1c397ad4e8c1b97547e2c3960b032d486816072c64196807598ad1d6076142328e6307136d6323c35aaad56069b906732ad35406d43400d18392a42c0d4f813a4c1721c92f5a6b9968c1a80b4d8c1c83704eac167b4b59dc47b6cc43068a84659ea50568e9e280b4d6316049faf9071944a2cd7b4829d072d03da413ab1b9862c2f6b3d183a0ee48d5aabda560a2cd53160526d183589bda498283904eb08b2f968ac439eea1972ecbda56072c1585ed25271a0e5ed3300f69540392e6b8bb2e6b9ebae4f968a93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part322 : Box 0x2210000800000000000000000000000000 0xfd9adf990c4646210110800040000000000 :=
  endBox 139 0x1f8630fc65127e9e1c8f22d3608711a06e128ed4460e47f936c7ca9c2c668c192bd44aa3f166a30c31981eb1d6abc60650bac7581ef758c05c0982c0fa302b1d476acec3270dcd42eaf18df6c0f69bb40afb964ea030e68b0e5c15c64059ad3d942f1812d7aced81e1cd1b9cb3b2d7b4f60e6936e51fa70f6d9a671831f2b4de0de2cd68119730c5a7ac0f0e6b4f6607b40f23001cd944a9230d8a09e08488c9472718f9561f28fd44ab1b857ac0f16686c504ea25859a3e5791604e16c72144aa391f2cd655a8bdb6473b594d5ad37967a9fd260ac3d42f2cec39ad5d9246af90e6cf23509370d8cd316238f95a52d5d271c8e7838827c982d317b2c8376a88b355c6913c166ae0b4d681905f039a8cb928eb1ba306c31618cf69582a401ab891ab557b482868c0ac751b6d3d501d0775a9bda439b370d024de0e69703e5969ab0290be0f960df3da457a6fb46dd181838c60e0ef07d8df68eda3066d95f167b39bd1960a949bad366a1a082039a4db9632b3f4a3a0267378f14586a40b0e3de938dcdeb4d1e2b95626d9a8e59a0dee556189bed632b8251e464b11d86229f967edc350f20f95a05a6c4e372fa0a6306f6949bc1f6041964d68af695019bed69b1830e6d183651405a6bc88e30c651fa51d472b3f8ba2947512b4ce8c186949c6f57965ed3d271cbe2809377b2cc5f028cf65515cf6904ebdd569af2340c024dd9040cad86ed906e92305a86c669fc5d19832a1759fac0e3070a4c356d3f161ac6568a1cd90520a9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part323 : Box 0x2210000000000000000000000000000000 0xfd9adb998c4200000000000000000000000 :=
  endBox 21 0x3905236d1a006bb507bd967a92f177834439abe30be618b4ad072b0558d8fdd25f3065012b055f1601fbb4ce256a465a9f18387cab4d8c1cd67610b18b428462f18bbc9c6c392eca4fd7c7b2c8396949a6d0322ef49bbd76698c1c584ef6d4048bbe4fe8bbe (by decide +kernel)

private def part321 : Box 0x2210000000000000000000000000000000 0xfd9adb990c4200000000000000000000000 :=
  splitBox 1 107 0xfd9adb990c4200000000000000000000000 part323 part322 (by decide +kernel)

private def part319 : Box 0x2210000000000000000000000000000000 0xfd9a9b990c4200000000000000000000000 :=
  splitBox 1 122 0xfd9a9b990c4200000000000000000000000 part321 part320 (by decide +kernel)

private def part317 : Box 0x2210000000000000000000000000000000 0xfd9a99990c4200000000000000000000000 :=
  splitBox 1 117 0xfd9a99990c4200000000000000000000000 part319 part318 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part325 : Box 0x2200800000000000000000000000000000 0xfd9f9113604110040000000000000000000 :=
  endBox 127 0xc8340f41005d8821980fcb5893789c683f291ad08e24fd6c588c2d551c9bd547e8ef8e226f54fec4c147397b45ab0a84e2292549b8ae625b97b53fab4d271a93527ecc35891d819a52363148ece41ee5a4ac6d43e4c1388819649f9c0c98320be48ca93527e83f8e2293f291b18902d893f6b0e6728ad07f07b9caae5316ab92549a983926061b59418739956c699c1c3515a0fd9c588ce53464ac94e220c36b3c907408938d69b043b107b93d2b4d7b49cccbda7139cba733732c4853f8a895e8761b8821c40fca8962919f14fe2c5b5a6930507f24f5ac6118c291a8ae583ad4527e91940fa936167a46544b200507ef2289651c9c2e14d8284367247503e5230fcaa052352107e705813a6ef4f3c37b83f938d6a32d349b6e65631ac512c2cd515827503e93f41f9c4672fa4fde43d1d88c1ce5f732a895456ba1cce04a8f0ce0ae65a3073da4e265ed512b90e04cbb0e42d81f93d1105a4cb0549f9b9d47ea4d630cc7514567ff8e6ac1789b66e7943ec1726d9c4543f305c9b6e5f515a20e6d964a2cd51caa8709048c0a53ffa91da433dd51eac62e8b42d4d9c49f892e729b99ce6b18591ea0cd969273562da4fe6049b9c19b1f656a6b43a8b624fd1eb1f14e3e7ff2919bd5472a3f6711eb1f1630a377376930569a71f615c8f5733974569ab63d763638abd4724db598c7c53768abd69af428fce6b0ae524a9016a5cc437adb13598680a4718583167d92eca4fd69ab4706592ae04eb97cffec61ffe36cad34e6ae5f93ce70b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part326 : Box 0x2200000000000000000000000000000000 0xfd9b9911000000000000000000000000000 :=
  endBox 127 0x731bc7e083241f721e87903f2c4038415b303d8aeb4d3f8a8e470b3d6c9a26ef7baad0c62d36607a4fc13a2cd52034b460da9eb4d04eb9ae5a6bddda46d4f6a2307399457a71f691c7c503fad0c62d35a849fa38be1c0c9c73d64fe3310e302c605eee72d838c1c6736acfded22cd581e4512ca393c1403f8c60e0d2bd5e72ab956246866c57a7a3dde8c1b9aded2b45597c8e270f21c4411f1fdd68aa3972ace6f3f1ed306f984e7f73d1eb31cd60e2b3f473ce6d39a9e906fa3030717b4b97d44b18163067355a1a849fa60b1985aab4d2fca8e64f7ac645aae6f949aa256a16331c45a522d54723073dd568a8e758c9fddeeb2d56306f7758cb08901c6616aacfd68af227be58c8b541b67198c0ab4993de0db1469c64c0ad03904117e1d459887e4e3324fca46b3f8ffeb4d6b1d45f0a467ff928ea09177b94638cb70b82d345ded6598beb1d8c3caf18c2cc438c39ffd66ed5f3849c8a1d969a94798bea09518a4fe2918bbdf83ffcb4d49f87e567f148dd4820a46fc3001f969081290284651cacbd6aa8e1c8f75949ab4d72ba7be58ca935eba6059eba6059eee735477c92558cb00ce102569b20dd69b1bed88492acfd607183942e7bd1e1d07d5c0812ce350e224fe7ab9cb60f72d35472b075a8b57e51cbd74b5f0771668f16166ad3547329357c204b3918780d25ef5a687e4e122ef41c8a4e5a696a56aa1f9303ad36 (by decide +kernel)

private def part324 : Box 0x2200000000000000000000000000000000 0xfd9b9111000000000000000000000000000 :=
  splitBox 1 119 0xfd9b9111000000000000000000000000000 part326 part325 (by decide +kernel)

private def part316 : Box 0x2200000000000000000000000000000000 0xfd9a9111000000000000000000000000000 :=
  splitBox 1 124 0xfd9a9111000000000000000000000000000 part324 part317 (by decide +kernel)

private def part314 : Box 0x2200000000000000000000000000000000 0xfd9a1111000000000000000000000000000 :=
  splitBox 1 123 0xfd9a1111000000000000000000000000000 part316 part315 (by decide +kernel)

private def part308 : Box 0x2200000000000000000000000000000000 0xfd921111000000000000000000000000000 :=
  splitBox 1 127 0xfd921111000000000000000000000000000 part314 part309 (by decide +kernel)

private def part304 : Box 0x2200000000000000000000000000000000 0xfd821111000000000000000000000000000 :=
  splitBox 1 128 0xfd821111000000000000000000000000000 part308 part305 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part330 : Box 0x20d0000000000000000000000000000000 0xfd7278e947ba00000000000000000000000 :=
  endBox 27 0x358bc280e81cc5b40e6c72106aacce276b0ad6862ef6d147b072d21f2d0c172da34072183a60bb5abd18336da80d4721c706a874d88570172c2796ae7cf6288b05667243d6ae6c78d42c2b493a515d0580e4b24543a67336901af177c3a6b1785de0d705fc3ab51e938c18ea3b0e99cc6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part332 : Box 0x20c0004000000000000000000000000000 0xfdf3bc6147a60a804180008000000000000 :=
  endBox 27 0x2f8d6398e8368e0348629315ad5e5a6a03ce621d3398cb01838ad352c390c82f407874e3989c9548f17ecc568313989cc62fd98ada9301acbf60bb51f98a5c0541e8560e62f6981467c9163a49528e3f19a528fd5a6a8fe7b4977c7e20b59a4af695a6a82d47e73151fc9e24cce62f619422d535a6a3f6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part333 : Box 0x20c0000000000000000000000000000000 0xfd733865478000000000000000000000000 :=
  endBox 143 0xda398d22f85276b0a2ab2380b17838e69f399b564da661f315b10e7b497ed87f203d0429e3069874c0d7177ded27315e1c0761d0398c0d56b2cc3551e9874e62ae3da66138b1d69a7315c1d04c16041fac967258695666a3d9a724b37b79f45cbb2be4f966d33899b4e5a6a93cdb73da6615b57cdb62c13899cc55c7b4c2c149ca514bbee81c4e417836d49f2d34da6bc3d0d01cc47c3144d07f036dac590c520af942a5fb515ca1141fad360e4b16cc0aa4d5817c5d0e2e9e1cce0c513a7be627c1c5abb3da4b26d5306dac768378bbe0c418c61f06dce0036e1f4a936417cbc2c90613fd88701ac1f8831630e97bdaa741f46beb51492a3fd49ad6300be17ee50a82fc5de6d3949a7e17b4accd42a9337b1d07f3f0b54cbf6a4d969328547e2f69817a1c97017060018b0f647e2ec358d298e66d535a4ad3418a61d49ad07d475b584baae678fc2c596b126b031528f3da5ec5d18069036b34e522a0bf499ab0d49836ad6198a2d533a1aa67258b1ab496b0b52669cc9036b1abc436b354dcce2ef5f1746f1d0600e4a733697cb5114e8fa563a0bf692c0c56aa97ed63ac02cce1e582fd44f1b4e0d9ad44796a4f399ac765a6c9456b1c05813430eb388c3a0b335a8a43e72fb905ed283f2858fc4d431a7cf7aa4d50ba43cc3e83f87e261f1f8c50b41f96a561f3db630eb4d2858fc5ec5317430fa0bcda730d569b07f374a3ad242c2b969ad5d824269f7b4942cc5690f7b8d07558bad5c5de62b5e17c398b10e4f1bda52662ef285a8fe4faa4cdbc69145728fd28a903177cb072fdaccd07ef698a165fb493cc4d5a8ad347e2731 (by decide +kernel)

private def part331 : Box 0x20c0000000000000000000000000000000 0xfd733861478000000000000000000000000 :=
  splitBox 1 110 0xfd733861478000000000000000000000000 part333 part332 (by decide +kernel)

private def part329 : Box 0x20c0000000000000000000000000000000 0xfd723861478000000000000000000000000 :=
  splitBox 1 124 0xfd723861478000000000000000000000000 part331 part330 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part336 : Box 0x2844000000000000000000000000000000 0xfd693d6a70d888000000000000000000000 :=
  endBox 33 0xfa398bc3a850928e8b5605a977c3b6e4f986a8276aac9eb6b0a5143b60d3293b80c82e83e9607c72f490a51587f3da58a290341ca4bcf0595c709481a49d1c4a2c1d61e5b4b5ab2d5541ccb076b1266c81cce2d4b495a8e93d5a0cc099ed26cb260b58dc3200d3607cb2d4998724e669459507b6c4b3735bd841767251639c867b4977d5015dc3e97b4c839 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part337 : Box 0x2044000000000000000000000000000000 0xfde91c2a40c888000000000000000000000 :=
  endBox 143 0x7b1cc671ac315c92728e871c3be3ef203c00d03e8e4370e01424a3a60596927114149b9e6c15020cb11e4f0ad15ed2a3f284977e37da8fd80302c9db284977d05283947ecf631ad9814a12e0201e5a6a0e4a031f9ded271f20cc83960138393981651f977e16a981569b2d44c0ad02d051d05acb4d280b09e7b49f1cbbf360e032041920faca62efad14c0ac3f9652b457b4b70b83905013818d8e7369bed47f34842be7098a028f58bf6b2d407b15d906e1647d149ea1527bc527302ad5e7b48285f46918b31fbd5fe5df5009404a2a733962ac593fcbdc4c0aa015a6c7215ab9c95ac314cb2d38b9fbd98302c5df3fc9bedcb33d4cbbe5e1302b90b22d5e5a68a849d650928ec7ef37d9fbe741c06019c204a409620a5072a25a0ea709499a51542334958127c238b2b396c9331419c256ae83704bc7095ab984d06f2cb4c260a7396b90a216a637dacae040cb2d6b1645e0c26c813fc07f1a7d822f535a49f84c22afda307185690cb513849c5d90470c223a796a2c595a4cba460e7b8b58500eb4d6a1b56630b201d192f715838604dda802389c181627f9b6549ab138c0aa177b8cd5361abda49feb299ed24ff302abf570401683177d68a70937a9c0d1451124e7339402d21692acecba6a2b500c8fd690b49568339b4e3e9335d1c82bdc7e749e9cbd24e0738bbe0339a5a8f536fad0580700e3283793fe4ff41cad460c7bda4fce5fb8c264ff4f5b38e03409e280e620dd0721cb8a4e61f8e32b1527f9cd5f4413c5271fc987cc5672d839651387f262b9ed25a350b9c2ce4ea118bf672d70142ad0187e302a93c7f2515927aa3d04bca3d (by decide +kernel)

private def part335 : Box 0x2044000000000000000000000000000000 0xfd691c2a40c888000000000000000000000 :=
  splitBox 1 131 0xfd691c2a40c888000000000000000000000 part337 part336 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part339 : Box 0x2040200000000000000000000000000000 0xfd6a5821528050201000000000000000000 :=
  endBox 153 0x1cc5e15c830e62f83d8de401187a0fe35730ead34dce513203903d6c700a3a3ef4b0c3a921969a7df71dc4797b99b9e0e8d0715a69b9ca1651d640a121bd82e27df4faad4502250b5f230f184cdcea09523c61e597ad54fbe9f55f0a170ba5472629373ca3930eba0b4d900e6ed1fba09c5deb6029e1fb9ba6626ac80ab8e66705289bd8527365c733365c1d17c1b4392c7c1284949d7c373c629285b804118c3ab4d561ca2b0f836a9d99d06b14030324e662ef670db3248cba2b4d489b10a1793fad4b2e893b66a5b68e028f40832c953fae4f599830526ae4f96663ab51ccb2562d8ef60c5f1d06705deb2592025277209c5d04ef81fe6514907cdb313b5a96f837850b8c3e5fb203b20b518a4e5fb8c2718757149b0fdcfce80705fca2b063bd8de380b82d3483eb0f964b0758b2f1854f5a45630e6e9587c52751f9b9d49a40f58ec5278c39b9e1fc949d7c293b30a01ccdcbb1b1cfcee51365a0e4b530edcd327e7413869e168b9461f4ad3564b06380c03d89e10257c6b164177c8390d7ad34c26155a0f2c3f4a38bbd0724ff9072b4d9bc5f1ac363c9473098bbd9c246ca17692a0a4df730257461fcb33487a4cd8a31c26309b383f9728c901413830d49f278d62d3564509c71751d8bbcc26bc41e67aaa51c5deb29403cb299d85f1ac38bcc117aa8bbcc26ac27f6594a85e57ea3659059fc5ed30ebdce47eabf418b2d245dedc2c82ef5013c4a0822e8c393fcdcf2bc648e93fcdce4979666085373a9356ab316cbf6a4d70180501ac1f493fe0629c4d28b309d4024ff062cb4d399a80683c975418a4ff5a69cce (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part341 : Box 0x2040000040000000000000000000000000 0xfd295ae0408020048800408000008000000 :=
  endBox 71 0x418ce370c02e1041c64e5b00378d62b840751cc3f9413a0e49d728f47f2527624c819289a0e52030d9dc9eb49289984e8c3a3c4a4e0d5289c1e67278b747f28277b0e32de177e46894743be41764162b278c796941293a87e4f1bd6e41b872c7965156b1d00efc40f4f5c5135099816578ad356a2731289b58e834040f275c509315c92b3f7977e7329844e62407275b6025b906e5092089cc53c275c837006ce6b60ec1f4c0a9db12ab994bbe5095e1b07d0e627038a16513692cb57381978547a4116d1f46b0bbe50928e89566abc61588662b735c03b54154275855604780ed6aed238ba2b4d72cc1e6093924d452d3d381cb2d177af8b4d8f9647f258907d6ae2ef06ac703821a46e0597177d3ee0db28e949dac284b9ae2ef9cc43b62d584867f9735977ce6219f878e2d13658354a12dc311e7b7852cd8e5b7413a4743960d506db281a7969a1db478c2cf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part344 : Box 0x2840010000000000000000000000000000 0xfd6a7f6254ca82050800200000000000000 :=
  endBox 51 0x370d23e0e62587090ed9474a4ed5d93ee2c76a1cd554a1444315837d9c249ff0ef5a772804bbe93359db95e50a93fded27252b0e5f39b49fe6cb6009fed619873079397ad5da433d8dac30792e8a28c03589274a2bda65a8923ce660bf05acd62bf67a9c1e49fe7e7397bdc66aaabf49fe0b58e669336519c05bc4ed05f876d653174ce664ed392cd61b2dec4a1643849c95abb355433ec47289b52683ca784ba2f69590e66a4f8fcef694a0b57660ba42dca2f69591ed292b9452c5f9402a019a5ed5327faa0f81b2e27f9beca127318bbe7257b4c731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part346 : Box 0x2050010000000000000000000000000000 0xfdba5ea845ea82240a00200000000000000 :=
  endBox 61 0x7b19c6b1a41fbb287cb921eb5705b877db4821cbf1f2d47a7257416440127ae4980f290f1de8aad23ab5787166a793d290b02c8ef4f970a0dc9eb2f8d8e02936cb4fc4cab0f5a09b66791a46c194618ca275279cc547ea4d4b05573da582ef536249becbbe4ed431b8694ad4651dbdc6592cf6905ac6d959293b4db31b664a29cc55c6520d73dc402ad554ecbda4bbe2ef398b68f71922a72548acd62c8a824f5abb0bbd6820598ba26f769fac051c62ef89da8eb276cd5d37dba0bc340d80bbcdb313b549a6d989daae2c87310e3cf690d39b6651cb976501a42d6ae4ed36cc1a35a18bbda451fc0bf1e59b66 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part347 : Box 0x2040010000000000000000000000000000 0xfdab5a2044c082040800200000000000000 :=
  endBox 107 0x5c100730dea7033c0e62d6240cbbf1f2c81ef718bbe157590bbf1838f964c1284b4a68c1903d644f09c313fd2c6017c499bdc651fc1ad232b174f4cf7151fc1d60fec51609c34936f977ce1323d4e13240d47edc338e61c7cddb1f9ded25df28e901dd0651ea7276d49a2ef5110c46ecd3b37d9c25ed32d24bbeb3b2c15fb3dc51ba7e1171a432805cce8cb7b8b48669fbda56265fb89ea9eb731942809bee1779cc5b47b1c8f50159474df6f639cda043481b28e5784b6a015268bbd80513cb5769dbdbc36a8df47acd617b7bda49fee6338c01cc480e96240d417177cd8f27a5ea6a0b9ee29038e62c02e86fb924e9334f16af1bec9feb578e2e7e158ba881679ed2d3f37da8ad1bb4615ee2d3f572086e1a0721cc6f0a3a5276b0d187163c61e6b0ac91879ed2b571e593fdec6a3c9276b08bbe6b149f0ecce325ef177bda6650bf734fca2a7191609cc57c4f1c5157b8c0817368245ed2e6071e2079cc5ea72d5d49a4ff7b1cc7b8c5b77b48fbc3b640f499c71985df04398b4149ce3314553d3103ce32b20f2e27f9196177ac8f619c9e7cb7a9a844d9a40f38c92b64f4a82d4226cd (by decide +kernel)

private def part345 : Box 0x2040010000000000000000000000000000 0xfdaa5a2044c082040800200000000000000 :=
  splitBox 1 124 0xfdaa5a2044c082040800200000000000000 part347 part346 (by decide +kernel)

private def part343 : Box 0x2040010000000000000000000000000000 0xfd2a5a2044c082040800200000000000000 :=
  splitBox 1 131 0xfd2a5a2044c082040800200000000000000 part345 part344 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part350 : Box 0x2040080800000000000000000000000000 0xfd79da3854a411320142404040000000000 :=
  endBox 75 0x831b0741806908129c2288299a8683983ea49d28a96174639a8b1d266ce2896604a0e58131745626f696d11427f9f2e6ae8f2d7c83ec2394f7a444dda8ef83ec8ff621a7bd3df2445826d3f4049cb637ab38ac2c6647eacfd24a9e3909c13fcdcf23adec2a396b0a3f657ebd8542e8d99ed29ef7bbad351c4e1ed334ecdea8ff9ed2f6991df3da4df6a1527f9815ee2f699a869474049cd49feac338a01816a839489a495906e0e071275402f63302a854c0b017cdf66fb8c05a6b708d9001d07d0b4ac3dac2f699053177ded29e2c8c813fc9d70b1d6323e9493cc0320d835865aa8fa59c05acb49500a0e411b1ef5cdaf5371ea5907993bad614759745ed2b4d4a2a0e64619059dcd612eaa805aa72d25ed2b4d1de89de2e8a775ed2b4d64126706b49260b51f4a70d5da0fa9274a29a7e1b99bee0fad5d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part352 : Box 0x2040001800000000000000000000000000 0xfd687ab2448c50b0050a0003c0000000000 :=
  endBox 83 0x7d190691b87215428ab384ed41ccb51492ac95cd734c4ff2a4f50aa10ce20e659dad25645a69bed402275a0e29274eeb16d3bb249dee29dd949e7f9735a805072ce13b5a0414c9dd7b4a0e4b333da569a60538c98165a6a805ed2ce378c0278a420dd07291185aa5b79203910520b59ed29dd928e509009c5092ef8b55ecb1424c0a2d5284d187a0e2d653fcad34c0a6fb831f0521b8302b00b4d93ba82961aac94e4e73506dce5f51d8136284812569a0db922293740c9425a040cc82949b8b0e5a4a806618836ca1300338de278c0029e698942506e8396e128f2d241b696201ca129118286b4d4eebd8d223050d69a9dd7c0f04801b66fb493c911284bda4deb41f522a509488a9164eea0a41b6a0983e9425677142637dc509928edc2e0ce37872d527cc1905aa025072a3d8e4ec806b6527bd84df6a2937dc81993b64b341bbd85452a4f3505ab2d34df683785aa839 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part353 : Box 0x2040000800000000000000000000000000 0xfd685ab1448410300102000040000000000 :=
  endBox 81 0xca3e07316d1f46807d31424a4eec293e5a89c64c0ab4d849ea155a29455d8275c0d90e89c66671a038fa774e6a3c187f2f61942eafd285c3f96819c551346d128ef628565a6ad44df61cd9222a3f95fa4ed40cb001cd9032a018df69139032da28561dca7bda7e1cd37d873655144b1bec9daa259a7eda3e0fa2a0dc1425033036ca3a4199073248c83251d540b530fa49d63f98832dc3209e338a3b56107324dc39b20dd6a2d3fa0fb0792768735504815c69dc06d4eec1c51fa7f97b48e06276a76542a6fb2e8ca0136cacec3826d996761cd37db38f22a874317e6aabda564aafd37da445246b0f8df69eb41bacee48aa025072c5f9a624a541ba0a4b531beda483ec4c1413b57457ac5f163a0e522a4c182b3183363a44506e7f9740fd2c83703f96b2c6c73e5ac949da94798929155a8cc494a3a45483291193ba839 (by decide +kernel)

private def part351 : Box 0x2040000800000000000000000000000000 0xfd685ab0448410300102000040000000000 :=
  splitBox 1 108 0xfd685ab0448410300102000040000000000 part353 part352 (by decide +kernel)

private def part349 : Box 0x2040000800000000000000000000000000 0xfd685a30448410300102000040000000000 :=
  splitBox 1 115 0xfd685a30448410300102000040000000000 part351 part350 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part354 : Box 0x2040000000000000000000000000000000 0xfd285a30c48000000000000000000000000 :=
  endBox 33 0x4105236d1c868178289c51d830a4e70393e27271fc9044c3e2d1949ef6957f8fa4ff20db671807b0e3290f8a2a92120b9c7e57c8354a2ae5f882eb5128a984606a907ca2ac83b0b22d0e38c987cc56f6242e1779724e625010ef8bbe2809c667b4901ca02719880f001cd4a171c7d3e24174e0e630674e3ed8142e4f8a0c4c5312cd69a50b06dc417 (by decide +kernel)

private def part348 : Box 0x2040000000000000000000000000000000 0xfd285a30448000000000000000000000000 :=
  splitBox 1 107 0xfd285a30448000000000000000000000000 part354 part349 (by decide +kernel)

private def part342 : Box 0x2040000000000000000000000000000000 0xfd285a20448000000000000000000000000 :=
  splitBox 1 112 0xfd285a20448000000000000000000000000 part348 part343 (by decide +kernel)

private def part340 : Box 0x2040000000000000000000000000000000 0xfd285a20408000000000000000000000000 :=
  splitBox 1 102 0xfd285a20408000000000000000000000000 part342 part341 (by decide +kernel)

private def part338 : Box 0x2040000000000000000000000000000000 0xfd285820408000000000000000000000000 :=
  splitBox 1 117 0xfd285820408000000000000000000000000 part340 part339 (by decide +kernel)

private def part334 : Box 0x2040000000000000000000000000000000 0xfd281820408000000000000000000000000 :=
  splitBox 1 122 0xfd281820408000000000000000000000000 part338 part335 (by decide +kernel)

private def part328 : Box 0x2040000000000000000000000000000000 0xfd201820408000000000000000000000000 :=
  splitBox 1 127 0xfd201820408000000000000000000000000 part334 part329 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part358 : Box 0x2008a00000000000000000000000000000 0xfd7e34ac730155455000000000000000000 :=
  endBox 73 0x6c178501987a1883988e0641d93dc36a3e54609db2015c07c019341ec9ee3f949ac83b60ba39cdb3241e276a01506a1b53e8c18b36393dcbda3f9398bd0e4310a178bda1f95268f95c06103f2c43982683b36cc6d99985b1076a3f816aa4d598c9fd26dc6c73fda935800e4c3f9515c5ed8316c601d07009b6e4193dea4d36d83247f2c424ae5269b66620cc515c0c751fa807ad96a28d5048ad4c9dad2391aab3d046c17f8d228d569a93dd456a3f7a1c8737cb0f57d831d6921f9501d0598d07d3e893dc7f2e3989ee7d18186b534778ae65a9b9bdc723f97009430ad4bca80b1f487e540590573311d89292b624ce6d817eaa3304ed5b102a69185862d5518c6d949aabec147231e83cb9556a6815 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part360 : Box 0x2018200000000000000000000000000000 0xfdf658ac1703d50c1000000000000000000 :=
  endBox 83 0x3a0be358a00bbd5c6c1c03988a464f79fe4bcaa0141ca588f9876e4ed62fca019452d3341c93b56446186303254524ed5e018f41c589294741dac4d017136e83cb4fcdb6c494d14c5e18469037f251d04a83b470db7201dacb028cdb68278db27f52f1865e83ca3e4bc6bc3809258fea94741dcb3b3faacce3f3a09cb6f41ed04a80b83cab8ce280b05924609f60ca4dd072b45944a7f5413a48ce6320ed89341e5076b13489a05578761a41f2a30a030c66ab9794fea8153989b66412a0266249cc60f6c1341dac4c8f70dfcfea8f93989794e631e0f2179419327bd0162b536c936d1f3289d47a2b589b60c95015c5f0e626dba0ea4d90df9f9d00e6c7a0fab536aba02412209b3c17851eac1e3faa05508515abc66afb4fe36da7bda852149a0c76abc6db4f7a0548f6d59041c9ef36da8ee511785f1c0599c0b149aa51d47f1b6506aa4d36cc8078b6eb3336cc947 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part361 : Box 0x2008200000000000000000000000000000 0xfd77182c130051041000000000000000000 :=
  endBox 87 0x1cc6917c720a17147d54700a02d4358b218a504f0fe4c3ee6f85de80746103705b46dac1d1c2c1ec5aa60505ac6c74918b55d01fcca13512a9345dee53900e8e0bbd3df41e58566e783d9fedcae81b9c06b1d0413c607177b500c3a0f2c1162c987cc52c599b05c149b28947f29139eeea4d83ca8960e31815caa297177cec149d3eb20ecff61f9600f7b1f6cbcad351f88326741c05e03f2a2b87f2b475a99814a26b11920e6075a8ad4e0c5e05dea118dce731373cb22f02d18f820ab2899b2e256b59cfce2d16b3c9e183c8d84d96c31700a26a01900e7f5314981560f1fd4dcef4310ec0bbd780fcac1e5009b1d47ef716af8f949ff1858fa2a296a78ad4bca7db9c96d352e89ef418ae0360ec209e30fc1e42d63f931487e58040cc90141c8fe57c694c80783ca8ed24a2898306f735a498a62cb8a8c51707962ca02c3f2f220080b03cca013738aad6672805a6b353c546e57500a8a5705f07f28e13fe2f1981daa7358c18a61f5aaca4f30eb18a3ba0f64ff41ca93da7320e431a081 (by decide +kernel)

private def part359 : Box 0x2008200000000000000000000000000000 0xfd76182c130051041000000000000000000 :=
  splitBox 1 124 0xfd76182c130051041000000000000000000 part361 part360 (by decide +kernel)

private def part357 : Box 0x2008200000000000000000000000000000 0xfd76102c130051041000000000000000000 :=
  splitBox 1 119 0xfd76102c130051041000000000000000000 part359 part358 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part364 : Box 0x200c001000000000000000000000000000 0xfd3d32ae014e7880a401800200000000000 :=
  endBox 67 0x1dc821f4721c028ab50a4293e72fb0adac673528998158c14dcb3b5279c44a26d623862b8c2cc4f62cc6163fccf533fac1adca6f69303c839403b16568e513289ca0380501514cf6941c98ad4531c6549eb11907681b5019c412d185415829506e1cb41ca38a2915fcd675a9b1653db17851c6319c60fc4eb59382c504e0ad871f07159393ae3031fecbc2827627b190718163181a0f26db41297856c69194631800e5a8ce39382d4797331062095056829960a92f9a9e941906e2bf3fdaa883950fc2cf83cc825601c9330bded26fd414b588e15fe7b49fd4bae9416b1c7f5697c7f560140414c72d41c9f566b3a0eda9339bd82269941db59d54052c83b27ba0ee (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part366 : Box 0x200c000008000000000000000000000000 0xfd35333f01407c018070010060000040000 :=
  endBox 65 0x2e0c034106397641587247e23f9661017032c7d20d30e48b56404834da4731407609eed418162ea8b560d320adfc72acf6936d9b8568a70b619c5e58c1bda4db67d172aa89063da6415936d42ea2b164c4bd1e5a4760699455d8052b9564a0b99e4689f45caad6181542f352589e387a0ee58372abddcbcb183835a85dac6d2410be2a8ee3984d9989ef6928aaf0c4f5aac611737c3cb619c119003b0b53d2e4948e97b49eee499ed29e92f6b13dd848ec82b302a095247b4b976158bd866b13ef395589e0cd7b0c07b8c1b4d504af69821ed28e2506620981d89ed258fea91d3e8987dec341adc92b1b729a41cfeb04418be390ec14556333045eee6c7627bda4e1661f7bbcc4f737bda5883285cc566119ed270b069c515069c7fb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part367 : Box 0x200c000000000000000000000000000000 0xfd35322f01c078000000000000000000000 :=
  endBox 109 0x288903b893f821cc7d1a05a4cb1b1fc9424a4ed241851567144f231e0e2a3d7b78b04e3280b947ad49812ea3d7f015f2c9542e735054ca3d7403930fa47f2d4031e41cb0b4e4e72d627c6db513b40b82f03f141dc727275a89e7b49c9d5e32024e328397b493fda4760582af18fb681b49eb9be36db59e0eeaf1599d063800d390723f938cc0d390321cb1f4a0e54062ec92b7b48b047d22c18e063f97d208731dc4f0a2a52738ccf6f2d1a89c5ab034dd8831c060147f41ed27a3f939aad883b927ab5104da47598405cd37737b8e507690793fab0f381ce033859b962f1835a88b5419a80b906a1c38796c5d04d82a49ef2788a2f0a27415c83b527c93d49ec7354058fe49fe61f87f292f30eb989e032c386711900eb5187d21bb92820bf671a839ac0c5593c8c941da89c7f21c987f2fa410d018761f493fca26d22f8b298fee93d28aa80ec1cd6513834d27ac0460e094a344db6719527c8d1509c6db520e0691d9ed2c4d8c1c62b701a8691ed3201dac6f5338c832c1a68e3da4392711900e8f54959b1e4979fd53fb20952828074139fd61dbbda41621cb0e4c3f9 (by decide +kernel)

private def part365 : Box 0x200c000000000000000000000000000000 0xfd35322f014078000000000000000000000 :=
  splitBox 1 99 0xfd35322f014078000000000000000000000 part367 part366 (by decide +kernel)

private def part363 : Box 0x200c000000000000000000000000000000 0xfd35322e014078000000000000000000000 :=
  splitBox 1 108 0xfd35322e014078000000000000000000000 part365 part364 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part369 : Box 0x2088000000000000000000000000000000 0xfdf67a65054440000000000000000000000 :=
  endBox 83 0x3e0ec3a0a207e4a171794a2a73149fa803e51778aae4eca8a5ee3149dcc302ca3b49f942ca4ea2787cae6318515293c93f6511436d9cc54472a9b168c19ab58ba0cb80370fc456e5e53dec6db631a05905df3dbc3626d349f8eb418a4ff1bcc7c9062a4fc75b312cbca2c149f9b0a2300c2d1e5c3ad729b8e58ba5e54c18bb395479627d0488f2e5c0db71ef45de5d1463ce6771c8bbcdb69a340be24d6177ae0c338f7ae552e8a7b67b4b95524619ce6f047b95625a8fc6834b0cded2e6f5112065127eae3407315605def6996623e559382b561f2894587035415e2c174145739741aa4ed177831e0e593b5a45401ab04654264ed7b1a014582ac23be41aa84e0e68696651ac6a1d8063c60e50bb06c5860d5398cb49907681b0e5b50731161c1cd146ca4d512a06d4051dc4ed6a0feb41ed88aa1360d8b0c39aa13900b13b418e1cd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part372 : Box 0x2008011000000000000000000000000000 0xfd3e7324138ac08c8501222200000000000 :=
  endBox 51 0x1063b8c44102ef691f0600a4eb2276e6afc1e5426a2938cac9e6afa76dee24db0c0cb27527a806d996a707d044b17549e8402d6593b5149b6d57509c0b559095f1425ed2a2902ad07157da785ed2a0136cb484e1906a72789c2e628082590764bb276be0e41b4e0e5c1c548ad67285a87ce33359e838850d8567fb26dce670459c4493a80b5509b720d49da7035e075f2375abeb1159e8f9502a8251cfc90b36dbb8d2016e7b8b06ded281541a82dc9da50b501645614530b4409f305d8bef71058a8f59c2c18332805ed2c5f623cf698c2c5d1500bda6276c3e5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part374 : Box 0x2008010000000000008000000000000000 0xfd3e56e503d2c00d0100204000040004108 :=
  endBox 89 0x2b8bc330731561a8521641f2a88c1b817ee49393a0ece33209521734adace6c740a936da47c0a1714560f7231d8362c105aac86d9815a9e18e3e8cb2f2b40d202b4a267d59abe5e5509b17560b00ccfaaa130a6a89566214b923a5e57b4a84d89707b691a0821642938bbe40dbd46177b175a7ad4d96a707d485a935a9ef71625c71f69ec1ece07144cbcad42a907b986a2ef3819cb549b2c9cfa22ef393944ca273b8da348b2142ca4e7db927af69501b0cce3271f9406c15619b40a42c8b1b62fcf53495a8a525ef69988ec19623cf69363a89c5deb1d9a6af693659c7e0c2859c7e36d9cb41373525667061b6e38fbda6405b06d88a0bf831e466144420a847182ac4526dc51551f8bbe5616440a949e37ea31cbca83b7a8cc4b1f2949e501a31cbcaac306d84141c8dd7a8a0d50767199ec6c199cba52751ec1ed5846118f0f9502ad42f8aff85de8dd05c8f96393949e2f2a84683d9795a051c9c0e3668bbcbf71b6c23a515293c815817e4ed (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part375 : Box 0x2008010000000000000000000000000000 0xfd3e52250380c00c0108200000000000000 :=
  endBox 133 0x9039893f57208398bb8da340e3b8bca90b1f2944ded25276a20c381c6db28a9c7cd971455ed2a13a0f6e6d28a9aa6736bda4a1670387cab21b02efa0f65e57b4a094dfb07b8e06f694129c9e30b353cd8e2ef60108820bcaee3683ad8db6e6d285949ca170f96736a9165ababfddc821b4513c7357b7b9b4a16527285c71985de8058e3307b736bb8b2149c98177938504b24f5422af19ea282549eb17e40ac1ee7b1a31d3ea6cb681ea32bc52162ef1f293fda82f28f961d39c7d44f24f5cc50178820e62d03e080589ee703293ab0d43176177a015836a271f2a0ee402b06d8baa259472c1b62ea89cafb30547ca7f540a93b5647c11c620e06a39949a91940dc28983dc72d41dc825618a8ce363b12502abe3e009b9ee21c315ca504e225154618330bbe0d66c75a4b1249da2d198360bf485b40e579256c2f513b125f01a5cd35001c1c5016a2738fa42e6af860df07720c47208381a88515293b946405b12e3071bf5edf07b7368bbe69e9bf518f2845a9e4e1412949ca2b070e1e58f94e070623884168c230cd7c62ec2ef05a8f9658ca0ed472d3d62e9b1d47f34ada9ea1359eb1747cb1b65472a399836d3d98663e5363b115426a2505fc1c36a11c820e06bc2c83e59c7673551393fd807a8c3e572b9c7d88733cd677b89b1c5de3e52c9cf51024b99d63ab5149ec9ef38fad06736a0ed8ba71f5917869ecb2d39a93fc5df202d808c2cb2d3e8a31d402d3d8c2c8f94639b1d444105df202d0368a20ed44b30cd18f2894dfad679cda7d141289354264ff (by decide +kernel)

private def part373 : Box 0x2008010000000000000000000000000000 0xfd3e52250380c00c0100200000000000000 :=
  splitBox 1 63 0xfd3e52250380c00c0100200000000000000 part375 part374 (by decide +kernel)

private def part371 : Box 0x2008010000000000000000000000000000 0xfd3e52240380c00c0100200000000000000 :=
  splitBox 1 108 0xfd3e52240380c00c0100200000000000000 part373 part372 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part378 : Box 0x2008001800000000000000000000000000 0xfd3c72b6410ec0a0c5014003c0000000000 :=
  endBox 69 0x410f83b0fa390ee07e5a028aa9051349bc9dd5a3a49657c8e4e57ca93e302d670219c44e330f95405909eece0a8661ab4acba271950ac5d105ac9dd588acf4bdab2208c4d8e3260541aa06d06b41d671cb94cbdac1985aa70b39a87e500f06160eec190519bf58be73527baa8d23384ed561084a3a3b662da76c0f64db40acaf90d585ce57da4455f2ac2c882b87cad658c0d0756afbdc55f6d5f9866f713dec1f630281b4e126e6d995f21a726d9fd5403069c9b67f7020a90ac2707f5900a4d193bab53626c0b57b8ad4e0f3348ec330c620ad06a4a7a0d65d1587aa84bba0faa4557dc5d1835a8253c5519c5198b3e62f9cb47771384962ce290827617cd23504b17cd8a71983cc7fb84f2f6f2d19384d5b05b5cdea3325dc837055a0a5a5f41f4fea829 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part380 : Box 0x2008000820000000000000000000000000 0xfd3c52f5110cd0284300500441041000000 :=
  endBox 31 0x1d07c1d86303f26c7859e1d949fb00d3f94128391f48b3e522ca4727b8fe5206018c6a127e4ed839ac459072a4f5099b01cda0d67d5616b9960e0a48d0728259246c2d83ca4dd27ea01b1e62fa01439a4ed79161f248d88b0734fc616ca13527a09d26e52749fbe0ee06f6284949ce3f15e4e32a1387ca937 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part381 : Box 0x2008000800000000000000000000000000 0xfd3c52b50304c0204100400040000000000 :=
  endBox 157 0xae390731821d04803f27e35093f4e188619cc5d0b18735ed23e54018b72c0d6aa83b732b53e2f2aca630283b3decd3583ebda473720aded2d42901cd15ec48d4eea3b6737a80cd32f69411ed2a139ede38b62ea06d82b293544ac5d561a868142f3d847ca9230e6a70c1b91dab031f29a6611882bd632d3579184415c83b69acc45476b4d6473acc6306c5d69ea8e6587bb87e34093f790a4f18191fed31363aced28e6ad8b173e0d0251e4f09424a4ed4460e025b4d5ca68ed38fb0b6476b55d426be3c8b0251d1db28e5a6a0af8c1cf6f0d3b94d6a741d630629f02c82bda87b8c8d51619ef44670d351da8d538cc3e549f9f90624fdf05918040dc9f552293847f2007801e4e1582a91568ef711e5b8e6729a9343b2d42481cd592cd4f1e5a85e7b8b1760afac6d0369e076627092f67b08f2c3b2b807361fca7d652687656449fa48a038e1682b581c70b526cb037b4936cfc631d849fbc8e8350f82c81f951cc8350eca06cd5b0fe54729c340b0073544b28e5837311561f205563b239d1da81b0e6c606512a06c3f2d0311647fa51ca4e8ed902aa33948e3f90ec949ce6b13ddc87c1a868180821f40fcb17658ca02568a4f71fccc156189c2de41f49c2e167c1d60ec9fd662ea91585a1f9254c70b27b87e58632d14a161f94e10772935226c155909b7460d0567bda3064db761644907f308f4fa27db69f9bf505670b8a0235d900a4c583aa48d03305b58626fd5819f449ef043e8f83a0527965e4f70fcbb88ed8e3ef6f28a949cdfb30b53842182b293544ac2d5611db0f9549b3d8d836be230b213b4fb723b58b68d5415bdbe0a388f51dae6f501a3552471b1e8c0b5151dac2d98be3f90fcae03e987f21cd519ca4d7379fecd8e1d9 (by decide +kernel)

private def part379 : Box 0x2008000800000000000000000000000000 0xfd3c52b50104c0204100400040000000000 :=
  splitBox 1 101 0xfd3c52b50104c0204100400040000000000 part381 part380 (by decide +kernel)

private def part377 : Box 0x2008000800000000000000000000000000 0xfd3c52b40104c0204100400040000000000 :=
  splitBox 1 108 0xfd3c52b40104c0204100400040000000000 part379 part378 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part383 : Box 0x2008000040000000000000000000000000 0xfd3d52b4810060200a00401000008000000 :=
  endBox 83 0xe4410e83e81f96309eea278e626db51d9c2ce6a93f680b3f1c8d3cf1832549b6ce168091fc9b6e476c60cfb6731385b606db8e6a7311fca684b149ac2c5492a0663eda0dcba2735771787d1d82899406396a84cc5661149fc73528aaa84eb9246a27396b605813ad27e9e98dfa6db3fdd07b51ca44e30b1b6d0726fd39ac93f285949d27f1c9db06312083127eb83dc6381936c1aa7271fcbb06c781aa7db966273138c9b1e06aaf8ba3b81c3737c0d5381c9ef15cc70371c8b44e6269d9dc6a07f31a74e627fb36383545df1cc47f2089831a7311be9fece16ca310fa2802ef49ecf531e5a5045a2a815ee2dbad5d48ee397b1acb523b0f2d602a0b500e0162b1063fca0dcba2ce136e60b92c4e6ab2b89629e789b64e10e5872e258a7dd5c38cc80741ca80b8206410f1fed66608d946670b167cb575199c2da049fae0fa0fe5dc7aac6072808bbc8cf316ce165798fb6b5740ba49562b0d9d3de501177b16e051ad5cc564f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part384 : Box 0x2008000000000000000000000000000000 0xfd3c5234850040000000000000000000000 :=
  endBox 129 0x1f0291b90e83e81f95909eea29804ed392939cd527e6fd26dc5e508e9cc53e20cb49f9bf6771a0691a8293b1667a9b0a47ca71f489c4cd47fa89d1ff289ce5a513619c9eb5139c45ea7031d3e293f1f29c45b07d127e73191ce00126da4bd49a2ef27bb58e58b9f44e62aa2c050140cc6fd41c9bf640b89a6236819c30ab474028bbd5c651b05e120398b18ee24fd7c6718573995426f693fb9a56003a84d1f2d6506aa31ded2a1391f2d6506ab59ded26d99ed23e56a7c2ef1f2bda5a0740d5b359c5de8c7066a84e6b2a31c18e942cee732b4d5686d6779118f316daa2b3b6a8cc635093f5f0197071875ed4f276ad46463a31e770197205c5a22ef242cc2d065c18d0178e838a51dace829177a08d22c84ed247ce5f619b0ac9b68055a1978d18f353cfeb136d6865e326dcb151f29fde4a0b53c9da90360a20ee62f2bda458293f771b4741ed328f518e0d5404c5e5509a01518f397c9da827402cf691f2a80e65983201159da0e60f2f6f276b38a13900ab3b588d071590c45007cb30b49daa3b771a0509b92e008b4c4fce0d1413acf491f30b5ea6d2372facee6b2ac9c9db201e23b8f95836c5d5a8a80962a8e813b5a84a0c0cb2f2a31d00a0d583dcc31838a8a52828c73f2c6d947fb4adabf0799032941492cb5149fa70ac1f0d82015206a0bca0d587cab41625c69b69ea31cd5b231c1aaa11515a31e5abb50d830b47ca90198ba9e951589a672481458ba2ef9422a2b463b68a13923aa11515a31c1aa23d803a5cd61581f527ed401ee691a3bc9b60d535118e2ef8d5a363509896c2ee69b80f68ef (by decide +kernel)

private def part382 : Box 0x2008000000000000000000000000000000 0xfd3c5234810040000000000000000000000 :=
  splitBox 1 102 0xfd3c5234810040000000000000000000000 part384 part383 (by decide +kernel)

private def part376 : Box 0x2008000000000000000000000000000000 0xfd3c5234010040000000000000000000000 :=
  splitBox 1 107 0xfd3c5234010040000000000000000000000 part382 part377 (by decide +kernel)

private def part370 : Box 0x2008000000000000000000000000000000 0xfd3c5224010040000000000000000000000 :=
  splitBox 1 112 0xfd3c5224010040000000000000000000000 part376 part371 (by decide +kernel)

private def part368 : Box 0x2008000000000000000000000000000000 0xfd345224010040000000000000000000000 :=
  splitBox 1 127 0xfd345224010040000000000000000000000 part370 part369 (by decide +kernel)

private def part362 : Box 0x2008000000000000000000000000000000 0xfd341224010040000000000000000000000 :=
  splitBox 1 122 0xfd341224010040000000000000000000000 part368 part363 (by decide +kernel)

private def part356 : Box 0x2008000000000000000000000000000000 0xfd341024010040000000000000000000000 :=
  splitBox 1 117 0xfd341024010040000000000000000000000 part362 part357 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part388 : Box 0x2004280000000000000000000000000000 0xfd7f993b166019523540000000000000000 :=
  endBox 27 0x20c641d8204b50d63956403987cc3ad21815acf2935a669fd62da0ed652c5b93fab4d9ea713fce2ed33397ad357c671803010528394feca118c0c8152f8b57568391646a9ad34c2741ed3fac5b692c0139a86d53309a936692a056302d5d4fea06e62697c4c26589902aafd6b1c604be2b4d4a2cc27062ad350723e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part389 : Box 0x2000280000000000000000000000000000 0xfd77d920162011001540000000000000000 :=
  endBox 143 0xec390c007e5b0590be2bc2f84ff6e017b0bbdee33535c7a0bb62da4f683db0d5266be370733927a2ef0b9c8f5384a02e49eb48ba258ac24cd3c380e26b809c4ba341fcfab11ac8ca90f85df183177d07f57ecb49728c1fda5690f51158384bdd63998bbe05dc9274b1a9b30e44e341e47127e7578a40d8127090a0cc39485ac1c7128eb177c189eb906ad5f3999c245de90b9ca291d1f29fd502a7335f128830e12b20bbd1bb316cb1b125dccef7146e8aae27fc1873385de72f9646e09fe7e1942b07f412ad260f6c5b9884a11c40147e82354e37381f5a931f85a6b1f855fab29560982b2996aad35855707f7b8a05647eac1cfc2b298556b4983fb58dc3802ef6418b3202d69a409314b386ed9812c3f309ad350730798c26bc238b21b9d02b20ed856e5796aaa017bbab0f228067ada05506a7d596aa6ed9eb61678dce8e300d8209d0529fd9cdea4d373c057491c629737a01d073058d626e6f314b50c01815a4204b70819a0ea83540d815e036a0a42d339be7bb8a8583ac4d492b9be204a7872390b4d6c1fc6f0812e5585de94541c93fe3848e4e4809f6d6a23f127f97c4bdf13fd03317bc8128396b1c86e0e5e80790722ef83cc37941c93fce2e2ef900e8277b8c7bd4898e749fe4095f1ac6405ded82607171f8b0467b8b5767b9b53e4899c5dbc8c0c8fd1b0cf6f384b209459692e5505a902528b39551b2c83183f13c018ad498f7ae6f3f0a3fe6a7c604f6334d5ec27bd2e8ae9183928b18157ea3f630b1ef58af181 (by decide +kernel)

private def part387 : Box 0x2000280000000000000000000000000000 0xfd779920162011001540000000000000000 :=
  splitBox 1 122 0xfd779920162011001540000000000000000 part389 part388 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part392 : Box 0x2804200000000000000000000000000000 0xfd6f95fa3b501c421000000000000000000 :=
  endBox 21 0x1003b8dc2a051f293ae05f181927c11f49c16478832569b239c1927fb7913c16ac9215a69c15505e128b27d47d2509499cd677aec73361ab59ca133601c98be27171f49c5e0e4c527 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part393 : Box 0x2004200000000000000000000000000000 0xfdee909a124018421000000000000000000 :=
  endBox 139 0x400ee3e0ce360e41065a4588c40728e949d90289acee2fcb086592a01e5a6901d04ee4101db82fccb2528994756461ac8076a6942541320a5636807969a827527c6075a69424832d62f8c63203f75011c513c2bf58882b527a9415a6ca29698b9ad6365f1397ad36526ac4564e72f493cd517b1ac6d6a68e28fe2f1a09d636b477918bf30bc13e839384ac6ce666c7814ab4d1daa515072b1b2e10132c44dd2a3948ead3568740be21c99a96b1b4a09c4d49f359d242602cf6389a8950120c9925ebe2d3524306f414a1bd8be2f8360c01004015e144a7d958db10e3ffa91d4126c7982e8e2d878136e384a8e568eac41ae15ca02d0764db405c81b5a8a8ae0eb1c24ff6c095a9a06e62d9bed076c82d8d6242e512a47507e83b9a6706f7b88b54bdaa3f5d11c733c7eb483824d67ab5369ac733408ce6f71c97b5c73018cdda7ff58db20802d85ed485c0b516aad4e7219858dcb5340a9ccd6c727c4db5a9ce4f5a9c83b661646e1857310d076b539636c4371cc34b02bac94dda7d958db17e4edb135692b4750ea8cdac6416a72504e6706b901683b4a2ac6c14b24cd69aee2c8f833851d5a05aa3ef0dac6c78c1a89d476b4d838ce554739fc60f29ff588c277513a8ed69a92b280b58d82f8c80fbd44f293d69a1b9497b0d65a6a49d6a6b424be41597c569a0c9986b2d350763ef72ace6f41597c414eb4d613c50183cacc564e3ef2fc947590661686c015730d4b4ab4d05a8abc392ac24ce3f2ad3416a1ad523cd4916a97b5ac6c1063032586b02dc9b720ed6c61169b0b548f32d4e5a6b30b1b61acb493fda0ec9b70ae56a67fb (by decide +kernel)

private def part391 : Box 0x2004200000000000000000000000000000 0xfd6e909a124018421000000000000000000 :=
  splitBox 1 131 0xfd6e909a124018421000000000000000000 part393 part392 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part396 : Box 0x2010201000000000000000000000000000 0xfdeef18c168b148a140a040200000000000 :=
  endBox 33 0x801ac711dc7005debc2b86f798b69351fba4d66b2a51ce5e8199072815982e6ed3998fdd78592c8354a3a05475f461e0ea1bf5929c24e66ae1cbcfef2d35072e4b9aca0735a6a0659c5516c49bad1e617a0e56a22c341ccb0f5a8ad3416b205564ab4d415c83b7116451186b2d3524a82b41ab38c35989a925276c82540ac4ed49a93b6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part398 : Box 0x2100201000000000000000000000000000 0xfdeff484728c12801428040200000000000 :=
  endBox 25 0x771c8590a1651d2f7cc5b402984c7df380e20b5640a98a4a0317e4a03310d04ac4d2fdb88cc2b0a45969a4f74a3936d06a92340ab90960a06149ad4d416a475a9ca1d036c5ed4015050eca455a6c9113fdb55cdce8f19a8ac4349a93de (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part400 : Box 0x2000211000000000000000000000000000 0xfd7ff18492889084148c262200000000000 :=
  endBox 59 0x339063b82ef881ee2330a22b0e42055904d188e717624c2b98c3c4f7624925e83ec61d016709587bdc6623b90821c253b72d45016644616471a87435ec490bc9b9c9ef461d3b6d458dda07505bc919373a055443713c421b4599b5166b386fd232d57363c1758c2b1252c0dfc9f7587c61d463187943ae6b9ace9f78c3a8c4dceb3350ece4f26d9b9e6613c392b11e62f82de62fc9196d19805bc8053979ccca4f2f0cc0f9683c85a4dee6cb62f9fd500a82142c5a31fed8b6c1d85733524dee7e75105deac2876518936d076661b1cff6a31a0f2285376a76d46341e5abe825a0f21755a9c1ed1ea6e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part401 : Box 0x2000201000000000000000000000000000 0xfd7ff090128810801408040200000000000 :=
  endBox 107 0x761d06703f2ee3884172e0c0ad22b09c190835492c39d02bc1e613fb065ca67f75a6ad36415c1d45aae5390327cb40d9fd66159bb50329db8d5ad5f40c8b545ab099d0325f92e13c35169abc2a8e20b56488a51dcbb2365a7a6ed626ce5d7b9b1260f2d57044c6ed72ecd654a3ab0bc1f0e21b1e2c4a44d02a5b985aa0793f297b433b1b9d22294772ace6f376b9567379bb4bdaac2f0e22388154a3b4c65a9a406621b9bdaae19d16ac7d93f7936cbdae558f76941480936d88e92f891ec472f6b58bc2d345dec1da0f66c7376a09523b1b1dee283b9036ee3585278c3e407721b8592c5f9289949d304f0c0a171969a827284cb056a6a48d24b41d42862d56a6b93ca128001ce4158b560ea8192fca09e6159815783a154518c81549197b526aa4205589b17856a6d4d9cdb0f949ee94741aa055b8550e427ba486e709dce6f04396dcec49cce6f3efac95ea738e5084a2ce3d599ad24ec83ac9f771cb9bd64a9f78032f53721343b20f32d260f33dce30eb07835ab89159cd6e394edad4dacee6b9caa38184f30753ec85cd01676248e399caa16f0b99f09159ace9f7a0d727dd22ad6461e69897bca12709177905dc8284c82937d9475cdb02d569a819 (by decide +kernel)

private def part399 : Box 0x2000201000000000000000000000000000 0xfd7ff080128810801408040200000000000 :=
  splitBox 1 112 0xfd7ff080128810801408040200000000000 part401 part400 (by decide +kernel)

private def part397 : Box 0x2000201000000000000000000000000000 0xfd6ff080128810801408040200000000000 :=
  splitBox 1 128 0xfd6ff080128810801408040200000000000 part399 part398 (by decide +kernel)

private def part395 : Box 0x2000201000000000000000000000000000 0xfd6ef080128810801408040200000000000 :=
  splitBox 1 124 0xfd6ef080128810801408040200000000000 part397 part396 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part404 : Box 0x2010200000400000000000000000000000 0xfdf6d08f960214281818082040204000008 :=
  endBox 77 0xf2390c83a0781c4ce66b43805f158ecf5d064ad349b73d749b72505667243deea4db064a10582b8b33578c6e948aa7be578ab8b51276a7fe1fbc60d28a1b751fc0bf8c182fe276a7fd0160c7621483c0cc593ad4debb24551d72c3d8729395f1fc59100e88461e15cc1e64a2b05deaa3af8c3bdd6093ac7582e597592a8e477f3dc5662a178c38bbd8c58ec4db599acc65a6c61e515a01d9c7716c5f13df06fd8723bf413a68b1d89b6b332f8d077587936d69ad45a0ea0038c3ad3504e6c749ca4550836cabc626dad3569294504ad1870dfac9520306b8afec51363a455a96e8310ce0bbd5c725c839725c8194f6ca3d5a6a5059c570fcf209d49f3564ddaf5d8bc69ef376abee4ffad350328077017c6a5cc5114897c51b22ef41ca70f55a30ec49064a02528a5f1300e059ec8eb404b59e490b100c9624d1875a9c61e613c60c75629d8be22af (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part406 : Box 0x2000600000400000000000000000000000 0xfdf7d981fa005020fc0008a04000c000008 :=
  endBox 11 0xfe3805ef85df187208907e30f0bbc81ec8309e61f8fc4e4a7824e65889c250847ec921613c3ab (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part408 : Box 0x2000240000400000000000000000000000 0xfdffd489920810605a480820c0004800008 :=
  endBox 35 0x741dc207c41f601c0620802821e0742d4d3fb1bb547306b89b66ed2e8cc5f4fe8ae5cdb461deeac473ffa8e49b66e7802307926dad34dcf27bd49a4db5b121713dd07e7ff51ca8fcf06615f71bb53fb2cf569a2b9966290140080ec41e07c2d3659eb4c40f207d4f0e403fa7f671cc61d49b06b3f5ad3587341fdaa2b3d27bb4c4dcf28fda6223b93fa90152681f40fe6e79a97030d69a085 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part410 : Box 0x2000300000400000000000000000000000 0xfdf7d4c1ba8014201e00082840006000008 :=
  endBox 111 0x7717c6f1b8203b209f79406d59490b4a4bf6b335a8942ca4e9ef8f929454fbc61d842b0f4f7c6e9526b70c817ee8c3ad44a4e5fb8c27187373cf6d2f8c1ac6ca6e96b2a37e30e5fb6f1984215c541e4490a7066370927293caf1599bd762f8cb3371cd069293a02cf7b1305cdeb4d404ac9db8404d187587a4550165273e122af5d374b59e8c3925e30f2024d8f202d3fa7bd5999ba4a4eda380c8258927374949e0eb2354d2ad6783ac78167e83bc1d524eb11005ce39598967e30e7eb94565278c3c61e404c61e2938d867b2a02ca4f1876f1885b0f433190515a8fdb8613cd3d27bb53c17e0c73b16a6d678fbe0199a7a9038c1ac9e8c3ac3ce864149aae3307bd96a294569a831d7c5023072c9d1aae4f8c39b9c9eee4f96a32c9e30e6e7587c90f37393dc18f187961ec82100c76a6c5f146a9b9d692d354a293de4fbb4d53ef2c3ce8641472c0031cfbf460d1e29151d7d1876b2ad4cfbf2c955f7187587c0c76e1345a9ce3d3fd831d666b4966230f2c3c18e5f161ccafb3fdae86e99cd6b5348ab00d578282d65628b59657100481a106e78c3c9ef5a893dd66718781331879016b25063c61e592accc9eedc208b495a8c60e1599b9c9eeb5369acf5f0d9c60d0c4413ef01c630690125081f5484fbd1870b9bd556a6d658fbe5f13f5966e30e901a306d35153c61d3eeb53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part411 : Box 0x2000200000400000000000000000000000 0xfd77d5c1920010201800082040004000008 :=
  endBox 57 0x4181f97f1dc8c3c2ef207b20a8220b0fa30e821418b30841c5d21f136cbe3183961e71347c9b9e727a465b4660f7b1c4e30681f373a4ace2f1879692a2b48c9b9e0bca8e5bc620c03a0cc51ca58d63a306a2b8c2890cb2ef6f3ffb58e234c61582e8f1363b05e0df936cd8e782c9e7a8a3d52066e7384ac907991ea099373c61d63b06fe47a9b9e8c1cd3d373b57d6a6b0f3ffc61dbc62110405c52751f8bbd49a7828ac5dec399622a3d59e8a1e4f5c61d016783205f151ec90349ca08630f202d3d69031d5c9eb418c6153de4db3508bbe6d164b23e4e0a527399b70842cce25ead45dc8c3cb251688ae637b9bde (by decide +kernel)

private def part409 : Box 0x2000200000400000000000000000000000 0xfd77d4c1920010201800082040004000008 :=
  splitBox 1 116 0xfd77d4c1920010201800082040004000008 part411 part410 (by decide +kernel)

private def part407 : Box 0x2000200000400000000000000000000000 0xfd77d481920010201800082040004000008 :=
  splitBox 1 114 0xfd77d481920010201800082040004000008 part409 part408 (by decide +kernel)

private def part405 : Box 0x2000200000400000000000000000000000 0xfd77d081920010201800082040004000008 :=
  splitBox 1 118 0xfd77d081920010201800082040004000008 part407 part406 (by decide +kernel)

private def part403 : Box 0x2000200000400000000000000000000000 0xfd76d081920010201800082040004000008 :=
  splitBox 1 124 0xfd76d081920010201800082040004000008 part405 part404 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part414 : Box 0x2010200000008000000000000000000000 0xfde6f48d170614085000304060010081000 :=
  endBox 79 0xe017088388b4d41122700368d2b9cdf1835089ba4e267a28e49b7202547e8eb9eca83b597cc5b4158b0cdb323563060c77210446dcd650389c4c1831f65032d65725c07740cb90da338e8031e3071c1563a8f93999b6647fa0251f31ccd68592c7e536ca01439a3e54614572c950130bbdd06d10773d5deba4db725a3e5077316d26ad3f40cb92dcab28f586ac5b49ab88be358e8352e69f9cbc5dee42494c0592cb51063c0b1926a82b9076937621383007ca742026374a845a426dc8097baa0ec192f7595f6f6d404831e389ba04dba306713695d1830dea85d60f0ea56a20c7161b90d63a0c3192825f13899cbcc059dcb51404a7be161a064ff3202549f2c4cff2819801c8741b447ccc3136cb0760f68052f88f96306713399b9067baa0ee3063e5174a8acdeec428ae1f2a93630305e41069ef374a0ee6ac9bb45deb3f949e83b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part415 : Box 0x2000200000008000000000000000000000 0xfd67d085170410005000200060010001000 :=
  endBox 89 0x1dc721b4691d828f949d02b172456e5f90fc83265a69065d02f8c8eb3e09c9481e5130fcb805136a06c3460c80e5f9203cb3b83fca018c18d24dce407801d874101f27d429281b2078bbc3f2d2380be350a47285b956592c1e526a81959998a56a30f9661a9784c3aa0396a280540a9b9e30e901c0f3460dcda7db40797c481e411285ad360de98747ca50b801d040dca4f376a0bd4262ef207906500203a600718bf27e5a0ea82b40cbdb6621a84cfd6835711d8591c04c0c56d29965e9473f898151df20ad1c5c0bf6941a0f681f4a0c8dd47cc1ee4a3cafb30298a5ac280ae0afd905f071985280f733acbe3f8ad3568a0c19a52b450dcad34a02e43a10607e58854110402c821418a7d648e9c5db4515c91d1f29c5c2eb28e50431b9ce5f02f47ca717620f870100a5ed926aa0b817e825523831e519c4f7402831dc074150200b58682d36136a045c441fc1ee5a6a44dcdf352cfcb07b5a6d07b3f8c1ee5a689b58b7251cbda6e790428f9 (by decide +kernel)

private def part413 : Box 0x2000200000008000000000000000000000 0xfd66d085170410005000200060010001000 :=
  splitBox 1 124 0xfd66d085170410005000200060010001000 part415 part414 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part417 : Box 0x2800200000000100000000000000000000 0xfd67f5e11b261c001088000080828005000 :=
  endBox 21 0xdc351003b81f96d0d971cbca4ed220850b40a9b2e3fdb95e1f2c6f72f89b2d02b1ccc172ee3682c9902a51f293acee48aa0eca16c402e61f2b59e49cad3507651383f2c1391bea0b05582e4dee1f9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part419 : Box 0x2000a00000000100000000000000000000 0xfde6f4a17207180550800000a8808004001 :=
  endBox 111 0x390f83a1002581f953190593cd4d407a0fd983ffa0d63739c24dcf28c5986e0e2724cda667e53739ccdace81548ac6f76a6cc2726db59db856198126c1290198aacdce4db412acee021b9ad49a0ab373a8e63929fed0426e759ec821373b10cc2d0ac3803e5489c9392f88755077320a80754be341ed07ec13960b07b699c1fe48aad24da2b05593c81f83d82f50621d57017c56143b2914bda0ab49ab08911a0fa6e758286fd66728ccdce4b7598c7fb943b07b50592dcdcee0318a82f8c2741fca314a39a865a69294dce9f583dc82569e9a8569a7ff2f6c00b2389fac9b683b609b16d28ec278d426e76e1985a1801f2a105e5928aa31984e0b949ca44e41daf8e0359e488a82d66694759dc8353739b9e400157282d246a47373965e58daccd68e93555126b1b9daa339ae306a0962bad1d6860150521081f2a096499a51e5a6a4e504ac2249d84f04fd28a81541da516412c3e56b3cb055a8a0ec7cab4d631c05a8c6d94a3831d0836ccb256b3ad4506b0a964a3b80ce2a8c81006593a0941866e74a3a4445aaafb902a6e7598a51d222c6300c82c9e200b09c176b1196a6c3f733d1852f6acc569a7df412cf7502092de0f72935422b4d4b14c72bcb2740f9b9e83da3e502a0bfa0f66e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part420 : Box 0x2000200000000100000000000000000000 0xfde6f8a1120618001080000080808004000 :=
  endBox 145 0x200741f0721d86f03f2ce37040f4fac2ef493a05526651d4b184f02e5416c402e65129bde540a26cc3485f183dc805604a0ed24e3e58d8e02b8c28bbcdce50b98ae6e7508c7ff3738bbd1bf0f953ea81b1779475b46b0a3ac8207e3979c951fb103dcce7ff38490662849beda9b1b9c52ed672079044dcf41ec5de40f20cb58be3202ef7218c397aa078348c5141dc5f137b8fdd24e827983a7f57b6b0acbe2af1828e241615a09528a3f737bc827413c6f76319c403c825589a48c7eee02c4e0269b64fead655a6c1c6030a84d04b2d35826ce0efe49cb52d04e923585d18169ba4e4d8ed4b640f47ae9bdce26a3f93de94526d9b66621b45a6d07b2f8ac6d6a63e5922b1a84db25f16a5b38aa1c8ec251d69ab1b90562c3490cb5537dc827491a51d04f2d3505720edbc6b17c413c9351fb901d984e1f01f2c60e5789ba4a4e6e7063cd673749b6590161c61d3efcf7150bad1ca272d89c20d651ca8fdb447fcb1150bad4d7c47fc1d671c9b1d69a9478c1cb4d691b8157c947302a05506a947967ab05628965d48403cafb4feb16d67ab33a0d6dc27051d47fc8df4fa97c504a81ba30e9478359f7cc3a8ff27fcb53491b90f8318d614756c6413eb20ecc3a50b541984e18af0f9524e5f14fac82b309a3768c39ffe0f6935589c6e73efa5162f89b9ca16b4d373d07b2f8ad35903fdcb13504875568a51f3149815b441ac6ad309ac15636be184e4a3a0ae70168441305a6a88947598c3e5415b09e5788b0d04b1f3c18ebe243e593a4d58420b91f7ac6e0638f9418b0325077318b40fbe0f7244c16ab4d16acb31928e605 (by decide +kernel)

private def part418 : Box 0x2000200000000100000000000000000000 0xfde6f0a1120618001080000080808004000 :=
  splitBox 1 119 0xfde6f0a1120618001080000080808004000 part420 part419 (by decide +kernel)

private def part416 : Box 0x2000200000000000000000000000000000 0xfd66d081120418001000000000000000000 :=
  splitBox 5016 131 0xfd66f0a1120618001080000080808004000 part418 part417 (by decide +kernel)

private def part412 : Box 0x2000200000000000000000000000000000 0xfd66d081120410001000000000000000000 :=
  splitBox 1 87 0xfd66d081120410001000000000000000000 part416 part413 (by decide +kernel)

private def part402 : Box 0x2000200000000000000000000000000000 0xfd66d081120010001000000000000000000 :=
  splitBox 1 94 0xfd66d081120010001000000000000000000 part412 part403 (by decide +kernel)

private def part394 : Box 0x2000200000000000000000000000000000 0xfd66d080120010001000000000000000000 :=
  splitBox 1 108 0xfd66d080120010001000000000000000000 part402 part395 (by decide +kernel)

private def part390 : Box 0x2000200000000000000000000000000000 0xfd669080120010001000000000000000000 :=
  splitBox 1 122 0xfd669080120010001000000000000000000 part394 part391 (by decide +kernel)

private def part386 : Box 0x2000200000000000000000000000000000 0xfd669000120010001000000000000000000 :=
  splitBox 1 115 0xfd669000120010001000000000000000000 part390 part387 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part423 : Box 0x2004050000000000000000000000000000 0xfdee972e46c8884e088aa00000000000000 :=
  endBox 39 0xee398ce3581df87eed827fe5269c9ce6a4db3e3a4fd644b1f083dca4f62fbda4e4e3978beef5b98be0b55149cd5476f6926dc247598b0c4e22b2320a0358a27410cb117b4a4aca029417b4c83b381a8a527eb119426a217ece0738ed65aa4d736ca019ed206149f9c0dac5514438181ce3f3a4fd403293dac6073696cd6169f936cfce93f4a0bda6039bddce3e7e749fc007036c1c87315c71e92d526ac8d55967af77618bda4e4ec1d1d7cf59039bd858bef5b4eda05528341e4e4e93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part425 : Box 0x2004040000040000000000000000000000 0xfdee961a4e48084a0848480808400808000 :=
  endBox 27 0x3b8f699eeed5972b97dcf8e1df3fbb18dc388aa25871138fc1ee60ca76c356b112fba02e57da0ed64e963008d988028e77bb936cbee7275b0bee7e1a0fe46709eac9dee2c1d7b48e9d83b3610796b2c35761ab025016c5f061bda66c0beeb11a0f6b275269005ed302162fbbc8b027f6732a93523b160dac2e433f2856cddf0758d224c1140900562ab43 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part426 : Box 0x2004040000000000000000000000000000 0xfdec961a424848480808000000000000000 :=
  endBox 143 0x440e46c169ac63b893f8019c6801871cd502e5f741b97de1fb9026501936d65a41f1f7c5012fb97de38fb40ee3e0f6995fef75204906560596c837150cf69047acb5e4200ac07eb598d06b51cad0e7bbb51c25f3da5a7670b58aad0dac7716420fac563f5a5055ff3dd56ae70b91eab154a0ac07f18c0af5b16aac0e3f8bddc9eeee400ce2d8b028ee30298a506ec639b651db8e4d5a5f71fbbd6683aacc5ed24174159c46736a05502e8376b1f0640c26aa18a4a032d5ded32bfcfde7efa0f24ab7b4ad4d45320ed036b2d591edb13b5ed27eb356d0712fb9815a432055ca281b2fba58c6228aa17dc1171c7dc7312ace4e8d98bda8153889c9db86aacb2d2f6a055076b539ca67eb7116440dcf6939aa0ec8e316160f2f6938fa055c733955ed2c6288e624fe007c1d060083ed03384012fbc71f690cd5559697de5b166341d5216a3f5268ae68c29bb562240787ef2c84ed495c0ab4a0a8ece3f0fbd622b6300d01e840147acb152fba8fdc9734856ae7357ae936e5a0ac85e3947e941348ca4d7b89ab5c727119f0801f420fb00c82d0e2bea42d02ab4130898ad84f3d6d02ab4171ccd63388984ce3f2cb4c57140415b28f56223ef7c1dc7d083ec834862c49b1c812b55314987d643e0c26f7796aef77965a8372becb2d3eba3248fef7783fc4db58b9025686f22e85ed4fea8e5eeb2d4c48f1624112b3191eab432f6b38a0209c57f2c1500eb534a09f96732a01d67a941964eb2d5a9c00e6105e1fbb00b2205cfef23d5282aff9eea93f5ab9fdcc53201d67b0b5527e3ef (by decide +kernel)

private def part424 : Box 0x2004040000000000000000000000000000 0xfdec961a424808480808000000000000000 :=
  splitBox 1 90 0xfdec961a424808480808000000000000000 part426 part425 (by decide +kernel)

private def part422 : Box 0x2004040000000000000000000000000000 0xfdec960a424808480808000000000000000 :=
  splitBox 1 112 0xfdec960a424808480808000000000000000 part424 part423 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part428 : Box 0x2000050000000000000000000000000000 0xfdeed32402888044000aa00000000000000 :=
  endBox 83 0xee400f8358ce378d403a481e8828871968127eb80bbcdbf351565af7783f9c7deef3dde36fad0e177a4fe177cc571a5c12f39a9cc527e6fd0748bbc1d305be49f9c7c9b6719074b58ae0bbd27f0fdcbef07b96861df6c14049fa78731371862d3f944e4ed623a0ee694974636cc0b551f9305a4611044edc4db6a3acc50365f7902a83b4ffc8dd615a0149daf692e01633dc4fea0b18db2a02f0f82a8d6140527b1bf43be6eb8e6af6941db0d638ca39ce62a15944e93f0efa0ecbc724fc3bed63e0da3501df48ed07b39aa84c17a0538bc707b48ea03ce331cd5077178d27e1df37ec8dd1e5a4fd076d81c0d64671d860144393a02e49fa5068c3c7ff398a4fd2827ff857272740fcc1d83da50527ee4d91ce3a160cbd5c982a4d49fbb0a22c8bc202d5ff0ebded27df57da3d50762798bee8d9247a76ce4e7ef601ee335149b68158fded2d593a42d2173da55fe815039c173 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part430 : Box 0x2000040040000000000000000000000000 0xfdedd291020860400808408008008000000 :=
  endBox 53 0x3189028093f7d0e62ee400e803a6377ad3504240920fabee2f794044ceb4d203981e315940569a4f787f32d348222b785aa4075a6af0ce1cc5dc8013c531bc6a169a40758cc4192fb8b552232d1e31583a4c0eb4d4f7cb0337ab134e6a935491c40737a9c4630b24d56a61c75a697b6476a934dea7116413df17b569a411373c7035a9c00de3d765a6a93490a6c726097dc83eee2d1d3d7181d64e41139acb4d23bd07d509987c9b6b11801bc7716071404e620e9208907d40640e6313dc802a4d89b6467398abee200a7f569a24f84aaa02a87f189b246739894058b72c0ce6292b4f3cb473e3981d26ab4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part433 : Box 0x2000041800000000000000000000000000 0xfdecf21a470c00e0050830a3c0000000000 :=
  endBox 133 0x5a0b857169ac6240d23da514710beeaa307605aa0d41426d9591857277415ac4d302c7d94edc50183e9ab416aa153fcc00ac1bb41d341ec34a8d9a0f60a19f072fc29d1ce83a51ab20a5a47112c6e0beee611de381a0d49da0a3906a0e98fd71ab409307b4929b6493f2804a02e200062bf9bd58b66054929f9602983a42caec3da5f058dc8d930283a563724dd24b098deda8d9561d8741a4591c4280c0e9415a0d56c2bec50126d94061d29f9524703a4db2e55026c0e93f29bb5c459106b316cbdb09164ed8975caa7278006afb1d2b954dda8db9caaa0140c96941d26ed671c4561a05512c492a4dd8c385b0667b4bd9502e5f7695cf657b4ac44fd707516acec3b8ae03a51c150cf69489a0a60eab532fbcf69489a0a60eaa4f9226a820560d706b5ed22855a9d0751509f6e40ca775ed2c5f38cac8d21c2ce324d98fb6c2b302a0d45ab41d4536c2b83ac71f7b4a804bee0e9302b48ec228ae2c8ba1fad0363cb9ed25f76abcba2cc62f697dc0fb38e4bdae6f9aae6c7276896e0fa6d90749fac1d3206da5691189da5f738c9c9e074ac88a258a4f6901d339bc4ce2734ee93b4bee0e982ce35357db8e5ed227350a936e147817d42a0b157dc0e950ab40a0189b69db40cad4e0ef3d6ca020e913b97e5047c0fd60e98c0a6d995f6b537b4ca1527683a55c5d1ed2d2181649b86ac4aad2b2fba386058e4e7f7369c169393b55e591a4411f440db9be074c1e6376c1ecddec5f9eda05f83d9bbc1d283b377c0e913c9c9ce23239dcde5f9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part434 : Box 0x2000040800000000000000000000000000 0xfdecf211070c00600108102040000000000 :=
  endBox 93 0xb4318e624fd5c670e62ac340e8244528e7f59076d235a697dcddab3d9a83fbc7353888b54fef03a569a7f78b6e8e715ba444ddab4d1b9c6054739fc569a6ed771404f1a05a6be0d3f944e50120cb882c39222947161cd3f6aec0e9280a805a47d1c4280a80658c974528e5d18b2a0b5492c83b36c9c4616a8e4c8328d969fb574ddb251cdb27035a69c464a389560f671f5a6bb840981d272100646c8eed0366f5590bdb27f60fa39d2fba0ecbdb27f544aae1c873151fc911376a51c5aaf695a6bb8fa3100e97a9c83b598a51da42b3d51f93041471bb522294720cc6ed512cf83b9002d1658194041d2419550fe32d34a02e6f906a3c15819fc544b1fc569ae2248e415a44d1b32d349dab296acb98ae340731561b84a39fd641da49616ac9112009045a8074cc4d39a8b55037010c2c614f074bb9003a00e98822e22c87279a6282b03ec8c983aa51c4c73d5dcaa06b6acac882b90766d1928eb21bb641d9c0e348a51da06008031024bdb316c1d291372fc0e9 (by decide +kernel)

private def part432 : Box 0x2000040800000000000000000000000000 0xfdecf210070c00600108102040000000000 :=
  splitBox 1 108 0xfdecf210070c00600108102040000000000 part434 part433 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part435 : Box 0x2000040000000000000000000000000000 0xfdecd210860800400008000000000000000 :=
  endBox 119 0x6c0a46bc2d0731631447c127e883a0b4d4c11b31f45eba2b93819045062e224f615c907e14d8ab4bdf307d402501500c0e9280a42e83ea4f4ddaa0146cbe8ee350ec31062b62dca15177b4fe276a0be280a0be303940569a7dfa0fe4f7393acb639ac00ee38841f489c9d92e88bbcba317464fea00569a9418a03003e0ee34962039045801d4c9133939005d05b130488cf7183fabed07e93d823ea11497974646ca7f55f6925489ce23a0fa34fe0ef8bbd00489a36640c9a6e488ad0503334a43bed59492b50e8300aa2d06376ad0cfcb3d5d456d3f62fc5d1156c58f5a1c1e5a52f6d6aca3667d164497cc110ef981cc569359eb6afb485a51c3be2c5905e911741f08018c200904498324f49ee80f497a0fc8cf2d0c625893f1c1c8ef2d3a0fd69aa012fb93dce6b20c569aa011f794055426dc467280a4f6770da320fc58a8318572c43b02ef276c8e75a3a50568f24fe6f127eae1c9e2fb8fbddc7c13e31c44c0e40740cc8d50efa32e46a898d1b24c130fc9f16b2b3900318fa101d885705deb15900eb111fbad5e49e936cba2ae2cb646cbda47ee82941ca366596a0651b32d0569ab578ba22ef5a6905df40efc50169ec9477258fbd69b0003a61779406 (by decide +kernel)

private def part431 : Box 0x2000040000000000000000000000000000 0xfdecd210060800400008000000000000000 :=
  splitBox 1 107 0xfdecd210060800400008000000000000000 part435 part432 (by decide +kernel)

private def part429 : Box 0x2000040000000000000000000000000000 0xfdecd210020800400008000000000000000 :=
  splitBox 1 102 0xfdecd210020800400008000000000000000 part431 part430 (by decide +kernel)

private def part427 : Box 0x2000040000000000000000000000000000 0xfdecd200020800400008000000000000000 :=
  splitBox 1 112 0xfdecd200020800400008000000000000000 part429 part428 (by decide +kernel)

private def part421 : Box 0x2000000000000000000000000000000000 0xfd249200000000000000000000000000000 :=
  splitBox 4490 122 0xfdec9200020800400008000000000000000 part427 part422 (by decide +kernel)

private def part385 : Box 0x2000000000000000000000000000000000 0xfd249000000000000000000000000000000 :=
  splitBox 1 117 0xfd249000000000000000000000000000000 part421 part386 (by decide +kernel)

private def part355 : Box 0x2000000000000000000000000000000000 0xfd241000000000000000000000000000000 :=
  splitBox 1 123 0xfd241000000000000000000000000000000 part385 part356 (by decide +kernel)

private def part327 : Box 0x2000000000000000000000000000000000 0xfd201000000000000000000000000000000 :=
  splitBox 1 126 0xfd201000000000000000000000000000000 part355 part328 (by decide +kernel)

private def part303 : Box 0x2000000000000000000000000000000000 0xfd001000000000000000000000000000000 :=
  splitBox 1 129 0xfd001000000000000000000000000000000 part327 part304 (by decide +kernel)

private def part249 : Box 0x2000000000000000000000000000000000 0xfc001000000000000000000000000000000 :=
  splitBox 1 132 0xfc001000000000000000000000000000000 part303 part250 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part440 : Box 0x1680000000000000000000000000000000 0xfe9742fff40000000000000000000000000 :=
  endBox 45 0xe8338c0032c19aa2270a60b04fc72ace43503a90d9071ecc4f591a68c4024d3ef287d67ae65a0ee9f772acd5b8c0ad4e7aca91cd9ad5b72f96be6b2a90d27ea63d8b238d9a1893e4a7dd46aa49580bbb0add8ab3d4da6ed378f92b4f896ad4b72ab54527ef00f166adad1c3b20d17709732d345ea3c5812e5175a6af00c74f16849169ab02c8e72fb0a543ac4f2799c0035a30258935596d493e90d6adcb2385922b39eb6f775188b2548eb00ace5a59b2548aa1d51cad3e518ac8e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part442 : Box 0x1480000020000000000000000000000000 0xfeb753f9a400044194000a4000001000000 :=
  endBox 79 0x18c511685d127ec02b8f60b0590066946dc9f39ad3ef356e0d6d63900ad5b791ab69420ed08523ca3562eb0b473a2c993d251b62cd06b3eac3c9761b859ecd5b41a8375ab730b4a36aa2cf68c0b9ad3eef63519acf6479804c482b23366b0cdcd6c2d41acd5b06ebb0d4b83b20cd584a0d41ba782487e298d51601cab2d4d40ea4972ac08f2e9a7cd67b1f6d6a65dd3112859e9f6e62cbddd48ec599c7a7db50fa7d66adb97e303291cda6b475a99f8a1f4fbc6d3598974d3ef3964bbae6f72fb70ec1f266a5a0941ba1d9411883c0c436167abc2501c198aa3ad7b7ca0d7a9ac6d41b3dbcd9b07060ff2834d9a5dd2d0cc0d5109b3543f1838792b4f51aa7dd492f5398aaa35541004a07927e291cd9b2d5dccb146cd9aa1f9a96e65627b94e0548036524b4dd3ca9f76e1dc6801ba089811aa430ecb526066cd5b8792511 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part444 : Box 0x1480000000400000000000000000000000 0xfeb1cabba60000088202500029000000008 :=
  endBox 33 0x741b8721d87805a703441b2c43c82f5512cb4d526c1fe5a7b94d836b4d7916428ba4fe405ad3cd4f2d3589f23ed27eb4d065cb0981862f57618828bca4d1e4cc375a6a7bca2e9e3986ee5f5a7874d3857bb70b236a06e724152860c7515c93f5a6cc62f8b4183a707587d60c7405cb4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part445 : Box 0x1480000000000000000000000000000000 0xfeb142b9a60400000000000000000000000 :=
  endBox 135 0x140510e62f01b8b6356d90621e45a6ca2551cba0e407165a783343b293f9646b4f837ab41591b0b68c3ad353deb4f591b70a3181ba2f528bca3949fb900d181aab1793fb07b7bab57ca4293f7e1ec791d04f9cc376169b34a4a0dd28bae8ce0fad8c4a1ca3957ba7bc3a66cd9286b4d1649b3648fa8e55eeb4d8592a39591ba0c424fe0ec8bd527f0f2527693b969a94369cca3117aa4fdb817ac0c7611b40e9c3eb274c0b9046cc295a093a5d07918828ba0ee17a941d47208793de81540db17588b033c5ea9c338f213cd69b3ddc56e8151f59b4e5918af588b28e569ec59063c5d749fb70e83680cd81a21bd83b2b2338da2f80c7586c6d35a6a8c56ae917a302b4d369b94d61ab4f8f92a4750f9aae519a8c569eb0d164c0c7595a50a479656a3162143f02e562b313db8681dc620187032c5eace3f00cb2ebc93150dbdac5a60dd4a1ab728252865d78b6b03749c2ce3683eb969ad5b065b101bd8a42a4d7b5c9ef5a6ac16595b12d69a805611e4781f47214c06d8374baf24c549b356e1f5949606ca93649894950365175814c5b12624e9a30e2bb0e38b1e494a45e0e3ad34baf352527e1c706dce5f584b56d27eec2889c1c8a3f2c3cd652eb9b347d693f4f7ad35f86adb90e1f5a46e30ec2d2ebca1d152cd4b49f8edd69ad5b671ec620a420b396ae0bb274aa0b158baea1d467c7bf5a6a8c65ab82e4176c1f969ab2b519ad5da7327dd48e1c3 (by decide +kernel)

private def part443 : Box 0x1480000000000000000000000000000000 0xfeb142b9a60000000000000000000000000 :=
  splitBox 1 94 0xfeb142b9a60000000000000000000000000 part445 part444 (by decide +kernel)

private def part441 : Box 0x1480000000000000000000000000000000 0xfeb142b9a40000000000000000000000000 :=
  splitBox 1 101 0xfeb142b9a40000000000000000000000000 part443 part442 (by decide +kernel)

private def part439 : Box 0x1480000000000000000000000000000000 0xfe9142b9a40000000000000000000000000 :=
  splitBox 1 129 0xfe9142b9a40000000000000000000000000 part441 part440 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part448 : Box 0x1600100000000000000000000000000000 0xfe9d82ef0f2802c00200000000000000000 :=
  endBox 113 0x350f02e0c6300d21cd5c0093c0312d8a91dcda1bd27ea50c18f1839876e6d05a93f52861cf48fc1bd49d9c7d686b127e4fd8e221d71f3a385af96a671148fc6c950f93f5ac2d79c45463175e3021d75a9cb0278ba3b8c42304f327ec60e48b8eb5286c598132d67591b8098238b39900e9295a6b0a589e931a0f2d5b40cad35253356d69ad5b8e1693149486f638593cc9faee2d35acf1fde0ef1836959fe5286a39876b291c30291f27ea7f5c05a13c4a169a703d090d790f82f9c1f63e2890630af5562ab48e046b56cd57356cf8b16d5c92a47a0fab278c0b56cb6b0144b4e5e7371cdf3d7c78ad5b380982cacc25518c6048ce6c9724a434f88c2d181364b994b4ef730c08dc6727a8c6591bd7d64f1817248accf4370e16b359c86d5b732cbc12fe735ac9e30208d518b56d6230125ca7181385cc235a797cd8c403caf749f831d605d16c27e8b3e62c979e30f1f6507200d003a415852c4f414c2cf4f20fb1f0d8169f76ad96d569a5a786da3ad50eb56dac0ebc93f0e1831c37b24fc9e6d6318b1191d2e552ebb56d5ee93f0eb8f9d74581c027ea0e65a69f9e6b3ac88e2785d759cc7f72f981f65a7c1fe7adb48deaae537af97cd69e8e2bde2f99f9d5ef3d7cbe69e2c0b4d3fccd677b9c6c983ba80d877460dace06d0c0ae8bc13f568038c48d414b4f562293f059a0a6612b53d48ee53984a5f35a5c829 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part450 : Box 0x1600400000000000000000000000000000 0xfe9f03efd8a02c008000000000000000000 :=
  endBox 29 0x3d0c42e0ca1894e232c9c19672717ab52e403a4fce22727650c4703245eab63006235f1646719593c3e7593cb4f8c3a7ce49fad4e83b8b35486719781805c12531c9ce5ab620dce328171f3c617504ca357adaf8807927e3e7065c93f6adc1f658fa7cc9f26170e3b4893f89f21d7065b9966ad87047ce93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part452 : Box 0x1602000000000000000000000000000000 0xfe9e07ff450b01000000000000000000000 :=
  endBox 91 0x691a067188066bc0c03d882749f87343b2d65949214191ced4d0d5be0c61b8711588ca1f49fc5af5a9b8f68c3a7dc976b3d57997a51cf1b649e65af49fad1d27f07159461182f239d252943510ce65900e819771ac4105ea0d1022cf5b46ba9153ee93104fcb4d781806503b2d45969a7034a18f266a2a50e4fbabece06a4791f691f495c5e958f8765f05819461118524c5d772fb5149e692949da58c62889311f3b8f672cb59d69e09b4f2cd6783f978d3560fcb4f72fb93e5a5c1fd2324f39262ce359e49fad347cee5f279a288e2d3d1f7359ce06d33a0feb4d6b3a3ed612d6791f6b096a2c4f3497a9072d2ebc8fb51a9c2d6732d3540ed2b920ed571668f9c9e69030093f36076b1fe52561d9148bdd4b6af578d8580516c4290e3d9ace4f3593a4666adb59cf8b201dccac596adcb0310d6356e039a465ace23749eacd66b3c38762cb99649e88dd672c4340f43581d917ac92b58fc919922e92b0e4bdde58fa4a413e4f35a6ad36 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part453 : Box 0x1600000000000000000000000000000000 0xfe9c27ef000000000000000000000000000 :=
  endBox 103 0x7b19c6a188311c94130c8384a36525781e86501b2af79ab61d730b94858c305b55e6ad8f9dabf38f527f359c1a652149fc521621747a0a225f38c46b538fee1d75101c206b8bcea4d6ada4fd25720a5216f4380d5f91d23e75a6a4fc1c2f7586fe7c337e97ccc2e7d79e077194070b40d63502f5360a1a931504cb1f83fa8c4d4f2cd566b16be0f2d677ada91548e601966a5af4a1a91548ed678a2ec41c0e83da3ce0fa2cd49f8694c1aaa300a315238066011a3e51e6d5747cc7bf83ccb4f479a3e5946b0a2e60d927a91d49fcb1b52398352571835a849fc51762127ef75969ec5550b9835acf2c34142289474a889038093f670c2f250ce6a625066bb8f0247e3fc8764e060d5306c91f277a41e30687659c393cd2b15da50cc1662f560c1b250c9de94399c6b1a84a1cd3d0e598bc19a6178c461c330bc62f561706212870f0c15aa17306a3a66afa50da7a9ef927a4ef4f7cd5f4a1b4f45ead63b8f4350ce0355a7b250cc1662f4a1c2f5651c030b8bd51d3357cff30799a9ed5f47496d669eb514c1a617483c829413834c78b1c643b2a0240617306a3a63fc8df658fa7d569ed3d033d0790eca87548e617 (by decide +kernel)

private def part451 : Box 0x1600000000000000000000000000000000 0xfe9c07ef000000000000000000000000000 :=
  splitBox 1 121 0xfe9c07ef000000000000000000000000000 part453 part452 (by decide +kernel)

private def part449 : Box 0x1600000000000000000000000000000000 0xfe9c03ef000000000000000000000000000 :=
  splitBox 1 118 0xfe9c03ef000000000000000000000000000 part451 part450 (by decide +kernel)

private def part447 : Box 0x1600000000000000000000000000000000 0xfe9c02ef000000000000000000000000000 :=
  splitBox 1 116 0xfe9c02ef000000000000000000000000000 part449 part448 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part455 : Box 0x1420000000000000000000000000000000 0xfeb816ac4a1000000000000000000000000 :=
  endBox 103 0x1f06c1ec7e1e4630a42b82f071f39693f60daa4ed02a731061c91f691886adc71949f9cc4186c5d9ab6b4d398831c7cf24fd69a7317a0d3b2d5d646b4f5a69c2ce62b22c070b41dcb4d414ac56727a0ed8bac2d6adcaff27ead5d54631381f3cb4d0639c7ce5ada206658ba4ed27e82706183441732065052d61f8b156816829005ce8c38344fd270b1e4a0a43b328354920d1503c70b62ec5b15a6a8349e670b5e103330c4e167315a6c70b7703b272781a2819695cb4d393aa8da340cc380c538c46827068830d6af1cc523e0bf38f8366398988ce632cb41b272d300c735398a026398834564551e83969cd5abf033527e6173009cc4fcf250c172f4380cc3b81d1404c0d5486a09640db4f639398bce620b9983273169e9c9c393245d0520d35002db3065ab67313f3c05f3179c7d1d294306abf0e834050d57122f1cb504e8375218c510ca355a69c9ce6a2bd961ab156189c2ce5b245d862c4ba0ea4a948b9c2ce5ac61c665a58f9ce5a8259696b4d385af8da348e6ab9385ab60b70e3873ce4f02dce6ad5b9012b4d38cbc850d8a42e4360d60b4d3bf2d5cb6a7311f393cc19ac41cc49e70735cbf1fdda059ecf5115e871d04e83734dc2bd5178f9d4372d0d27e827 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part458 : Box 0x1448000000000000000000000000000000 0xfeba53e9b8b240000000000000000000000 :=
  endBox 39 0xca3b8dc3682f56a0e63185c1a20799aca1cb398985ce3f205d286837501b4398b12640c872daa71bd543aa1705cac8aa072cbaef55962aa475a0bd56515bd7d412a23d864edad5d47ed5b5abcf6137abd7c176da3dce523b0bd3ee6d92d4870c1963eb05cc6f539ab70f2368aa035630ba05e497835540393c7d9300aa8d5ba0f26cd62cbd7d1e6735366cd5b8e32a00f266ada025072c8161e152b1651f31858f96f712c3bd7cbfed5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part461 : Box 0x140c000000000200000000000000000000 0xfebf3bf99db87800004400141814000a060 :=
  endBox 9 0x370a02780cb904e8396d1053185839291915fcd3339ac825413834dacf2465052827 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part462 : Box 0x1408000000000200000000000000000000 0xfebe53e915b04000004400100814000a040 :=
  endBox 151 0x328ae2f0dc1cc5886b0e6b02fd04a2f54a1c0ad519a84416a1cd671c07712c7c0baf0344e4e5b59cca8276b3871cc2f2095acf2c54db27354129c66770d0068a50dacf239da7a2996a7c8c56b3b55d1ce82599c6d10c5d0bfed639966a782ec396d23816ad519ee6f6b413b59e6ab870c3960bb5c17477016ae03dae523b0a504eaa2c562469aad48e6cd8baef6f732c6cd37aa05e6b2b5364b1f02315ff1385a56a09699b534fc5229636467a8240f649b8006a096abb53d4224a596aed4f6a696a636c9234deadc310ce0bd54231c643b328459c6a10132bdc196b0d9892817355a024c2eee350d4f96867f94a1b53e57bcb436a7b59d28761a66d4d57fd07d8c2a474b3692b50897fe037ca11624a09cbfe782705a16d5f07a8bdbd7c551b84fb9cb649492ecdeb34acd56a33671b86abc2f538c9d01cb942294183969fd98b24e1412b55e0669cb4d56ce18be62f8ee6695b70e03102f587721d93fcc4e1068aa8d578d56a3140aca01c0981f66620ad5c742f6b81761cb91c66ab5abc5d747c9b35ea3370d631062f8172aff38c8bd5c057fc7d558a9c641a2aff9f04a1c727519a39e732b48d18ad573ec8735ac4a1f05ab9bd60e5c1f5462a119282b2b05cca1f0e5c1e63fca8460fa8e72ffa91db8761a86703b29620e640ac1e41aa719412c7d96b079211986c6f5583c9aadaa282547c9aae6b2a0959c6d11f3306501261740bc7f98c02719907261767140461c8e147cb06459e3c941cb6814191aa8272ffa3e554152c5b162cb524b633dcdccad516b07926f596aef5f246ca09 (by decide +kernel)

private def part460 : Box 0x1408000000000200000000000000000000 0xfebe13e915b04000004400100814000a040 :=
  splitBox 1 122 0xfebe13e915b04000004400100814000a040 part462 part461 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part463 : Box 0x1408000000000000000000000000000000 0xfebe03e910a040200000000000000000000 :=
  endBox 129 0x3f1e849fa80dc1cc59c79144b24bd016a0317a98bcc2e88250c196d3d9a6eb1b62397a58629a20dda7b3595a9ac17364c60e6afbb8d42cb617aa50cc1b0bd501660d812eec20de2eb9fad3dea2b2ffcdc310ee3e02f5381e448fb4ce415a82549a62f50ed07d48b9c44d929178c5e4ef522a06d04f359c38a6c9317a481d99866d65405a0ec9df35880b6b3c6ab6b2975caf6a474a1871d2872b08e7a30690b699a01d3ded65277aa87c387d66f52ffa38669eb68dc461641ba06c3960cb5d145735943963eb760f4614c01748ea82586ed314a0a8ad49aac13966b2a0de3edc2b737a8ebcfd735350564ef791b4651646e07d6cc3382c18c5ed5f41a83350370bd506a93b8e46d57069b105d79622a3948ea8aded71b35aae7eb277b70c40736398a47d4722f57009df41d4006d4d482a50ce620cd06a86666959cc521ad5f57dc81960ab56ce62a3f277bb0dc358ce034d23b182ce6a8256ad9c6458320d57830ba8ce381a0d4583338aa2066473a38459e5ff50103323e50728f991f31bd45831f6da927195b140277a00ce1f65c873dc585a83938c822641ab30ec282e7b0b56cc0283539ad07b519bdc58baa0b6199cd683d9c65072cc370c1b9caef614798f1506aaa1aae505b0b5ac66f5366c8e17aaa91e5059b34d56c43d0ec0bd410f23cc3426cd620a38c3b28d190038ccc4f4149b3641cb07e41c9b3588650382703922e94317a9fe68c0a3cce061d957120695cd57065b0545762c1590e6b026d1f2931051a4a660acc2d (by decide +kernel)

private def part459 : Box 0x1408000000000000000000000000000000 0xfebe03e910a040000000000000000000000 :=
  splitBox 1 81 0xfebe03e910a040000000000000000000000 part463 part460 (by decide +kernel)

private def part457 : Box 0x1408000000000000000000000000000000 0xfeba03e910a040000000000000000000000 :=
  splitBox 1 126 0xfeba03e910a040000000000000000000000 part459 part458 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part466 : Box 0x1406000000000000000000000000000000 0xfebe92fccc2a0f000000000000000000000 :=
  endBox 87 0x1dc4f18c531801f3b408e2c071f904e71f902e2cd927ea499aa272d4111e6b058bae0d150fb9ae063b68d2340f80345ab7205d23a1c7270871e651680e38dc672fb524e23241e39ab00b4d8e5a92f91c2d4949fa41500f24fce22b4d6016068120b2d3506e8394b124385bdde4829fdd682f59a302c5d5a6b99569b358d442b1558acb01a00d1857a8f3482b28d024ecf87359d43a0d16b1c8f57acb59cfef24ad78403cb536ad81765a9a01c1a2d2368d02d80d1631283071d2333d9d282d399882a317c18c5c0e231cb438f34dd802e09e72c55cbe70b506c1de7abb56da6a70b69cc9070e3cd0356e3968b4d052c459836d63396a388299a928e36209c45823292541a72d6d1a46003860cd521c735047c7116009e7356c39270b62012f2c9d28209793e609b0e4c70b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part468 : Box 0x1402000020000000000000000000000000 0xfebbd3bc440a056014100a0100001000000 :=
  endBox 115 0x1a0671dc601405811c7241e30e1d93859c65ab6819414bb0d22bfe38c8344e17205e50fa90dab65d3393ac8961bf6393acb649fb8edab673572127f07651e7286d02e93f5e0d8551286313c2a1d4f9cb1f49fb0be3ea8f14fc5a1b06b127eda004e006a3cd00e92b83acd393eaacd58b2e3d9a92e3962fab8da201dc7327cd1cee4f593b8f4b63358dc9f461dab6c156b2b175ac403b90e479b56dccb17071158fc0d13eac1fe72493cdc86a1f69ca3cd00f356d622a095518c620cd5b1f3a87ce2282218a1f4a0cc2f473acd60ff250402317a51f28f3617b56d3c5718c068c5e9485b56c9c23e762100f0f15622d5b00897a4023280d5b471cf591dec4e1098cb1172a802c97e3bd2e9b56d4060bcc5f3f1cd70344fce93f735c711631706005a724fce4e735380e220cda306015619a3454129f359aa346504b4c60feec24fc2ff41d5eef1874a0b5466209e724ac3b2861c2e0eb2785c92b39008ca1f7bb9f55646131721785a1b0523c8f91e2b9ad866a1d381a4fcd871ece3983cb9bdab6a1d62ea8c52c381acb6471a91e0f33954d92d5b9882703518a91d807aecd373fcc604256f7559ea7dc1a21d9169847e0689c0d27ee59479cb17596b18b83387118e6a2d3927e7034713c4b127f0f9c11e8f59aa293f91ead51596c93f49078b3045a92907497b8f6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part470 : Box 0x1402001000000000000000000000000000 0xfebadabc460a25000a80400200000000000 :=
  endBox 121 0x310e8358f80bd5405b1b45a5a48d51967293d4a09c80ad495ace4517245d8bab4d3818f9e388b13e3888f9d672c62e0c0353660fac5d2767033969c86a24ece06b4da30e9078c0cd5b130bdcda6ec1b579cd3549d9c460fb2d34f86d375820fb0a6cf86907579b4d56573387118e5a9318e06c22d8a2071c15b30cd8963c59ace93d3e1a6ef63920e3c57af975e727a41e49eb595f06113c531ca739bd286c6338c0209e39aad3683c9fdda62f6b388bdde00f80255f7075364c1e40feb4d6b1ca0d5a6a70b61c9e5849c0dcb2b4b727d1814f09c9d0332d4cd92c83d9e5a3ac25ac72d353e6827680d82e9c827598ad1d3c5312c0c5cb3d04d868c13f2cf5a630af4bd2c5f59ead35843f015a8e79c725e959eb0cdaca8e79c725e959eb06decf2cf4db272394e1d99b6580421ccb1f0c15ef670d2a92541a1a59ed60af3e1cf67735ae0b033893b63138048c1a769ab56d5e6711396ab8b05838e6ab270a01d04e0b7962eb4141056734d5262d5b835ab4d6a6cb4d4989c8c01c4569ae6d9c9e5d38c0a7ddabe7c3a30270ba0fab573e1acadab718790729055abb56d69a7c35718c6b1a01f3b00d4d989ed67413a0e4fc2ebb13debf3995acae65a0d64af7aacd677b3b90daa27117c100f250ce227273f1244f9d079403b595492807a0f2827616cc315a6c1f5ed6e435b100f359d672c299804fbc90540c9c2e30f2825c7ae4f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part472 : Box 0x1402000000400000000000000000000000 0xfebec2bf460a01088080700028040000008 :=
  endBox 69 0x4416877169af83086833892978120b1c2c7672cb6781286b09940e0d1385832e5249b851451169ed3d98962d3584a4fda573dbce32d5f85ea6e1584b38a22482d31f3a4fc95b30ccdb2d65364a7cdacf0a6cfee6d969bcb434138f9d687175dabe0d149fbe0b4b969ec45819aee3a0d02502f55013ef41e43b28194a197a54c381c943699c917381b187a1c9ce23245d68f357e40ca0dd88ef033870358fd18149493cce5ab09a30293b1f3c929279a4c5042ebc8fb498831e8c0b515cd6af759ac1d9495ad3dc86019c169b40b3d8e3e943393831ce3f2bce4f2bd752767030ecb40ee3582319a9eb11498830c5eac22d4e494ac45286703969724a64f984cd27ee6b58f9c0d2870ba565a3e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part473 : Box 0x1402000000000000000000000000000000 0xfebac2bd460e01000000000000000000000 :=
  endBox 145 0x571d0398b40e4358ce0bd4e333dbc1963e77c148b1385286a47257cd6749f834568511e04e05a6723106d93818f160379ab527e3b35a98ece5a6b06c57b3dbd67a71149fb59e50f9b2527ec2278f8286e3708705252943600b3b24fd69ad2315e828d27f2d3527f00dd23ec1572a91ee4f9a4fd9c0e69f8727510d079524a09d46b353cb6ae65695ca476afad3518a803c0ce359e50f9cd522e71183cc8e748fb53522e7036b2c59f494bdad43ea470ecca1f4a18bd6781f060100396b907034605a6b4d9a565b5584a45d6132c5d22f24c6381c711601443e1c2696ad8ecc5821c7169a98b0338b6239e462b99457a3e77b7cf6b46078b1b65abed4f8b6ad6736ccb151e2c27b2d2bdad69a7e1b6438f356d27e13d8d4ec2338920af61f393cdb460038ed23815ec15988ac45982a93f23bce59051a4fd23e8fb88f6d674f9a4fd605c148f3d8c7ce9314a1b38905927e3e71d9c93f5a69cb60618f9ddc741ac6905eaa31819e0d16712533994dfaa43591cb2d2dabd6d69ac42989e13ce05ab125ca61d9494a50d2856123e7c38d4ee39735a4fcbd24f39c72a1d0ecb8e65a1805a6b4be48ba065a5f245d862d53640d9341e5eee07f522a91c57a07fa3064e1364a91543f0758e169294a1ad05c318b4d3f007b4605a4672d3559c6527ec02cae279a8c4e6a9439ab6afb388a48b031665abb0449e6d5b9657181869a6a972fac8d70519c695591975c56693f498a50c0c70e4dab6b5749fb90d628c580063b106523822d656b57364ce4f57bb56d287030e6218063125b356ce32b2389e6b4d3858765ac274c8e349eb56d83313a5eb73994e16b4d (by decide +kernel)

private def part471 : Box 0x1402000000000000000000000000000000 0xfebac2bd460a01000000000000000000000 :=
  splitBox 1 94 0xfebac2bd460a01000000000000000000000 part473 part472 (by decide +kernel)

private def part469 : Box 0x1402000000000000000000000000000000 0xfebac2bc460a01000000000000000000000 :=
  splitBox 1 108 0xfebac2bc460a01000000000000000000000 part471 part470 (by decide +kernel)

private def part467 : Box 0x1402000000000000000000000000000000 0xfebac2bc440a01000000000000000000000 :=
  splitBox 1 101 0xfebac2bc440a01000000000000000000000 part469 part468 (by decide +kernel)

private def part465 : Box 0x1402000000000000000000000000000000 0xfeba82bc440a01000000000000000000000 :=
  splitBox 1 122 0xfeba82bc440a01000000000000000000000 part467 part466 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part475 : Box 0x1440800000000000000000000000000000 0xfebaf2b9f981a2040000000000000000000 :=
  endBox 19 0x1f06e184396ba0da1c46317b56e5a69cc4c0271150fc7315a6b56c18ef63923a619388ab8c41cc584515ad368c2bdcc9d25f37a8c6f537acc428465a6a8749d2b4d8bff031c3863eb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part476 : Box 0x1400800000000000000000000000000000 0xfebea2a95100a0040000000000000000000 :=
  endBox 141 0x1d076194670a2eda149554690bcf17fc7d62cf8e625e7691c050019a8f98e629ef91f28f9a0f67315a6c9ef398b56d27e7eb9acef6b398a80c1b9456b4b3069cc584699ca0949fa06d69a7fb69acb0948eb38c4394e6ad9cd525e62328db18b83007d99abf0793939cd55430bc93f388a4fe724a0edb46615ff24fdaa28f9066979e30ba91e8c1b56ce32c01e883b8fb30791679c2d3cb288506ac2f802f0753fab56d076bc34c65238f253ca91d402a095885c184306a7967b8b0f523ae6f7b7c91d5849c0dcdf239cb6b2d0e0fe703169ac8d806e148650e327276a6d18327ca90c1969e290cfb728d4f7eb238c3ad4cd9ab5394462ec0cb05fa4fc9f2b1f8c2e7317a1404fccc5f52493e56965ff5a79cc5583f09f2a62e8b3d816ad65521a92519f41fd69a07f69bb594deb34dd545a6c5ff6a7c8cf7a8b4cd743dfc0b5503ad1d61334d60c7ad35ea25d327c8ebd27ebc3d0a027873155182f24fc116093440ba72d2cd9a0896adb10b1b93e6b4b593ac8e8c19f6e8c2c1ed27ea81f8a472e9cc156ada4fd94353cf717afbd8c196d3383fcf61366bd8da9f18bdc92d6749fb48aa23466ad8fad4620932f3a8cd941d7c0cb3f031b356d3e6b278112e556b3c93f6e1e8500c5eb27982ec4730cae907d927eb47584cd65721b59e593c60c7d65e7737bd8e2ffac24f7ec175015c4fbcb1b1f5ac8d69e7312f174591acae1f593f569f16c639ab8e56964fd511b45a07d6ce24fdcab1cd418ebc353e519a914f97353d69ac23940671183dcc33381ad3549a93f5c1b8400e6aa479a6ad575a69c0d19f3d453eea336a7ac25aaf2c2569a6f55a6c719 (by decide +kernel)

private def part474 : Box 0x1400000000000000000000000000000000 0xfebaa2a8000000000000000000000000000 :=
  splitBox 4349 126 0xfebaa2a95100a0040000000000000000000 part476 part475 (by decide +kernel)

private def part464 : Box 0x1400000000000000000000000000000000 0xfeba82a8000000000000000000000000000 :=
  splitBox 1 121 0xfeba82a8000000000000000000000000000 part474 part465 (by decide +kernel)

private def part456 : Box 0x1400000000000000000000000000000000 0xfeba02a8000000000000000000000000000 :=
  splitBox 1 123 0xfeba02a8000000000000000000000000000 part464 part457 (by decide +kernel)

private def part454 : Box 0x1400000000000000000000000000000000 0xfeb802a8000000000000000000000000000 :=
  splitBox 1 125 0xfeb802a8000000000000000000000000000 part456 part455 (by decide +kernel)

private def part446 : Box 0x1400000000000000000000000000000000 0xfe9802a8000000000000000000000000000 :=
  splitBox 1 129 0xfe9802a8000000000000000000000000000 part454 part447 (by decide +kernel)

private def part438 : Box 0x1400000000000000000000000000000000 0xfe9002a8000000000000000000000000000 :=
  splitBox 1 127 0xfe9002a8000000000000000000000000000 part446 part439 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part481 : Box 0x1003000028000000000000000000000000 0xfe65cb4d692a05e60455088198001540000 :=
  endBox 49 0xbc330c43e8b42503fd551cdf1ff412e3ad523acfe3feac66183950ec2c660c710bf29f3a0d630751aa91e5a297a60279f5548e91d141ca478320058060ec418dbe19b88faf755816ab0aacda2c5983fca49690a91d4133dccfaa90b067ad560e293cdfc48019f065568aa4759fa886183a87c19f28d5c44c124589c30100dad0402e4f3521a924c232884e87baacfe30f0295626e6b279cb419aa6f756013049169f3dcc60ed2b51aa9255e72d3c60ea216abcc5f183b58e25fa475612307 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part482 : Box 0x1003000020000000000000000000000000 0xfe454b0d608a05e00414080180001000000 :=
  endBox 119 0x5a0fc72127ec43b0f60fb5fc58fc94147a8f9c60ece13ce524b94c19f021b7e4f2b0ddcaaf5d62596be4f2ac2471ef75584c91d183a50bc28c61f386d49eb002483072eeca492e9ca1b8136b1f1f38eddec465cc336a88c1d45e13b9aa23075e10471dc9f3183a925aa2a1f523b3892232e51780be5108c1d463174daa229300e808cc0ace0c1d45f4604f7ea49622cc37126a795866f7567060e6dfa0ee1b92fcb044dc23e7479cd515e1d87d07daaa1b0e028c520067a32e83aa39d62660560aad54fab2bcdc76a2171dc7c550fb06e15d8c1e3e2a3e419e6e19cd65e15aa8aed80621540e0a503078bd2a4758cc30750f8c1e4a0333313d1e630727aac0b19989e8f3011caf37b9a87c7cf306d412fe3b0307501cdb2d2d28291d819e3e78ec15dc1d6737c1fcda68cb12cad3d6128f361bc1d672996b59c711243f15c4efa86dac2e9833e1f3a8c68c3ad56183a87d463062f0d0398d63e87bf9ecab551f38c1c2632bdd85eb235aa8f9d6c7d18be2b7965ea3550fa91d68b0176479800dcde8cb370ad55462e3d860e4f55aac6057b9cd5f4a08f9c60e0cf9cc183c3e72f0cd55597b40da35464798f9deba5d35aa9b7c9eab62d561f3ad5658bc3e72fcaf0d0320e417e5463291c60f2d5e2e9a8c568a09386eef595aa97e5cdf0a0d1ea307 (by decide +kernel)

private def part480 : Box 0x1003000020000000000000000000000000 0xfe454b0d600a05e00414080180001000000 :=
  splitBox 1 99 0xfe454b0d600a05e00414080180001000000 part482 part481 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part484 : Box 0x1002000820000000000000000000000000 0xfe49536c500b05600490180141041000000 :=
  endBox 87 0x418ce318c02c8cc1c9ce6abc2d2e40c8fd45a7305d8beb3d49fa0a649fa70cc1c7d68169cb3d293a4fc7fb003d5e3eabdd4ba68370bdcf5d2e9b9be1ac949e04581c93f293b805e949fca31737c606519ac4527eb1950ea787115011028eca1d3eba01d832c5f81100f27dc9eec17293a8763eba01d27f27dd3d65132939f9c0772cfd462b2f50f942d802e110506ac83fd826a6df7b297a4e16d218bd2d5f6d0e81f6ce59735947e6af8fb568af57806a13909ea58ec1c2d43738f47dad5f60acc4528fa9263feb94c3ba3ed692047716070ff426251f5e1892b1f91ceb4b50ead2e473b4b582e5e9966a3ed8262e62f0c8287548f0fb4c0aa014756071fe527f291d385a0e06f65827a7fd166b4c64fbb57d3caf5d0eeb10d6591966c96af9b7cffa93f58897a43bb02351527ee3b93d652783ec9e5479ac7e368c1ac122e3d3f6be8cc3483ed55204523a01e009806543e7d5835942c9c741ae616ad14a3e011a0f28f3413c1d4a267d5624b484e38a167f78baa8f341396d6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part486 : Box 0x1002000020400000000000000000000000 0xfec5132fc0080d280490380120041020408 :=
  endBox 97 0x18c5a0fc7f127eee400d20c1d1c280ac5e1699c0c1a341ae3022d372ac9eb527a3cc7ce8cb92163e7381945570471257317dcde3af381b380cd859ac5f36fcd2286e5178b4ce3339559c81190627c8f357b94551e70345caaa2f57bc2cd524b9be28a8b35fc551dc381a4be51d9cd4a2a307590dbf1cd49ef23e5dc73060e3e7921651572ac94147cc6d1066acd459a4e38a2a2cd4e180551a0381b38901cb52441cb95636f93cdcdf3124fb23e78dbe0cd771cd72cb4ff20d11839b7e737d0754ffac5e302307396bb9001c664f5b90d072e3d183a9806f9ebad5f5108f9d233174c1a2e5589e6d45393a42e0eeacd4e06e43380d12e9c3071f3974e183b385d38dbed57364a0e460e8270abc5d31189b2460efe3e8ee3490030051f183a026524ac55c7b27b5d873166b34ac19a9074a0947d4048cc9d948eacd56131aad8662538c1b485c92d61271cf655a7947d44323cd072c41183b10ec241e72aa4bcda32d3d1a2e6f71ec4f7385bb8d538e16e6b0eea09d072c459cd6a493ecb48d2d9c92a21068a886 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part488 : Box 0x1002000020000000100000000000000000 0xfe41932ce10c05a004100a0100881008010 :=
  endBox 135 0x731f47220477168308ca431fe8c1ca16515831a0308c3e77b6a8c548e30728fb60a21860e7d54839b44c22b553dfc30773798456ab34ed00eb2f067a8c5544b12827ba48a315239c4647c82360ff1784da2c420892b71ec8d150f807e468b8f60fef5b9a76063732ac8735943a92b497b94e6908ff543ad82d0ec300c450668ff5a7739adeeaa0d6afc1fe69db9ad80570f932835493183591ac9c5a6b23802e1c1393a4fd46b07f9ac2a09593ce535918334bdb2824dbeb4b6812c551047609b2a1f523b51671ea0dd282a4391a2837621fc770e22907183cb19468cafb5a7b9bc38328bc3aac2998b2a2f0688c1dfc7701a32c6460ec02c8d25ea35969e7278c1d07f6a3c1fe25cb925c86a0936f86d545e0cd94120d1014cb1f48c8f9d25e3071f3c3077f1dc4b1b080165ed01f8b55879e73549fa09d4034eca35696a765c9ed3b5aa86d50729f99abe5e169db93d6ab1c7e631641f3a70727275d187524ad3da5a8199493187275b05d6871c7d30696c2a551aabfdc9e5e15219f83f5904e8f39646e65721987e03928399ac63f540cc3bd4139cd51e7393c1a282939ac9d936fa0a4d96d5349fbf0cc3183f560dcf6f37ab484dbe7276afcb2351639a8af66a29cd61facee30896190b2f5216aafa02661839845a43357c36a8399abe8e351672c8c1da8e8399a5e30727fbf098290e589a4fcbaa6117a07fb24fc60e90b925eb2d8b926df308a42e0068754faa3fd183be8fc3d0cc07460ee8ff5ca739acbdad47497c1d649fa42d25eb178e6a92f6afc1b5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part490 : Box 0x1002000020000000000000040000000000 0xfe411b0cc10c0d280510280100009000020 :=
  endBox 87 0x408fa398d2390da29051528f9c2e308bd7648c8c1d687e0a16cc3f83fd60dc2cd49facfc60e7e232e504c1a40fe2a3521a9260ff28d4c2307987028f31f38c1d61334b4ba63e72fcb407e34865aa87747cea09403a05d406015441cac56834b12460ef6583ac3074a0253238d832f6d1f3a8258933584bf30c1ce170c1dc4280c5d34139c0c60ece2405f9413b596479ac4d0725c598bed657b6cb572fcb90c628a61fea3cca2693f7a1fc4f0c17f83aa3cd04e7d51fe8c1d67327b562ea21479ca49620b04412e611514c719183a4fdc47a1801fe8c1ce5b355da8f46060fec59388a4fe5aa984521692f5209fed638bf291d601eaf358dc9ed2b58abdde62cb51c6c2d637f200681c06c104e8396a9cb3f0e8b556385c189c0f9e3f3acfd46a3f538f97a65aaa4fc7ce3f5945f1c2ce3f0fd6682007f01a3205c60ec439266a3938c3821dd480107022527ed23046479b0a545e281271ace60eaca1d5239f167219cb525e307 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part492 : Box 0x1022000020000000000000000020000000 0xfe61972cc81d15229570481140001004001 :=
  endBox 41 0x1fc831645207eb0294fb25e13859c9e00680e06c1c0691032b2f81a23f59eae93f36fc0a7396a4fd8bf34b527f290d68ad8290d1cb39ac4ce3e77aeb9ae12a9f9d27f1cb5b0771845a1606b2f40cc3f540cc0d12f0c0d183cc1b55aba4fc3327e1c098174e0b8a92541a6959aaa071630ba72d0ce3ed45941b020d1e67d562eb555c01fac0d141486d649f8fd6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part493 : Box 0x1002000020000000000000000020000000 0xfe43130cc00c15208570080140001004000 :=
  endBox 125 0xd0398d2390aa408a476d09ff147d27f142d1f3287dc7a92f183938d2836204504bb8fe147db070167eb45183ce55834c61e83ca4fd88a6ef860ec4598bab4311662eac8b538e166df9a42c4330ec34ae8c196bd27ed611f6875410702256232d55aae30759fc3c977204413cd3b40cb584bf230728fa32e1f68c1dd862183335143ba3ed066c5ed471ac3021da762cd802ae5549f8625b43fccb551e48344a3ed8283602395e630e81959f8c1d27efe41e66b081cd04e6ef183b0de8c3974dc92aa2d0e213dddc381c93f596a0dc60eb22cb638ca9263eab57d65a93f7accb537bba4fd9c471dc2fccb55183a06506e86024638f8ebcdbed21965ad3b596c719183a3ce58bacb5c47abd183279a924ba6719183a40d3b9282f5949f97a50325f99c8632047a0a2693f87fa7fd381c93f4f9a505a8e7190eec5dd26fa4fd80701b04f0cb1760897b54863fd0e0b1061d6a785c92d611f6c30748cc30748e937da8e93f8e5a30738cb80a42604f387020911e0a42d25e5ed2fcbd100330307485c92f0eeb94e735b5852163fd927e90b925f00351e1e4b4858b293f83a93a460f0759ca6c5949fbf0907965e3fd49fa476388a903bd8dde7fd1fe9c2cbf302280b4398e423850b1feb97e627b97e71ca8f618393ce1feacfe0ea93f27060e8e1b7dc872c6586ee5396072cbdc7a16f83a8c1e1fe9efe49fb97c9c6307 (by decide +kernel)

private def part491 : Box 0x1002000020000000000000000000000000 0xfe41130cc00c05200510080140001000000 :=
  splitBox 5805 125 0xfe41130cc00c15208570080140001004000 part493 part492 (by decide +kernel)

private def part489 : Box 0x1002000020000000000000000000000000 0xfe41130cc00c05200510080100001000000 :=
  splitBox 1 42 0xfe41130cc00c05200510080100001000000 part491 part490 (by decide +kernel)

private def part487 : Box 0x1002000020000000000000000000000000 0xfe41130cc00c05200410080100001000000 :=
  splitBox 1 68 0xfe41130cc00c05200410080100001000000 part489 part488 (by decide +kernel)

private def part485 : Box 0x1002000020000000000000000000000000 0xfe41130cc00805200410080100001000000 :=
  splitBox 1 94 0xfe41130cc00805200410080100001000000 part487 part486 (by decide +kernel)

private def part483 : Box 0x1002000020000000000000000000000000 0xfe41130c400805200410080100001000000 :=
  splitBox 1 107 0xfe41130c400805200410080100001000000 part485 part484 (by decide +kernel)

private def part479 : Box 0x1002000020000000000000000000000000 0xfe41030c400805200410080100001000000 :=
  splitBox 1 120 0xfe41030c400805200410080100001000000 part483 part480 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part496 : Box 0x100a000000400000000000000000000000 0xfece4a674288550800a2300020140000008 :=
  endBox 33 0x400e8358c40c0460e9a29082348ec5e3416a50438f1b64db320b52330779abe5e3596a4fd547c1882f4c51547da0b507a8fb9286c17a3067f7271a0b507a93f500cb5340e945527ee63c0703926251547dc82349fa84e579acb5ede93f416bc0e633851568017f1c9c18e1c78e4e61f416c80d591ec72d2d03a93f30fa806062987e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part498 : Box 0x1002010000400000000000000000000000 0xfeccc2264a29010b80c0300028040200008 :=
  endBox 77 0x3e0f0300c62c8e81c9e0073060ea2195e672d4a1b55e579a924e5a9c33072d4ffd07f2fdac2495341fd3fee5f6b0899e7b7a32d4921c74f1c5ef1d9a45ce5aee3e8c4358931817e3075520f3357d02652738fa0f4a4f28d503a90d860e71f91ae6df69eb57d286c319cd65e96a29c7dd0801dc3d060ed5f949292938597a651aa835104fcce596b1b0c4bd270b761cb324adabeb4b9cd6a63b05fb9492d2b6af8ae6524a90c81c2e0f32c7e0f33486506c1e4952ba1c2c76739acfc683d498ce6b8c1aa8ee3a0940c1c11f232e3027e75939c44bd283d45166b1f9c06a02b409a0cd38579cafb388947e57db9881389c690d28f97be46b861c106c499696711624c81d6b0ad2c60ea49860ed0298ee31030151dcb1b622a075066c5f93e7079509aa8a218136803419b9665939b7d896a13903a833180a8ee0bfa92504693f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part501 : Box 0x1102000000440000000000000000000000 0xfecd827e624985088881b31022260400008 :=
  endBox 53 0x7818c55138530e3e7036b16415cc92b309a90e641b6068ac451483cce53836c1e63688dde83cb59dac2527451a7b357d64e093409b53683cc61d622f5d364a911879c7692b368ac9c2470344fa6d62b8d4d8a4e0c70e38f9d90360a4e0c757bd0793689cd5ece06b4ffc6c983cd073409abecd928d593fe527364b58cc2980c51e3cb1f30f871e58f834630fac9e5249c9ddc6b14c8c1c8132df8b2cc26e8032e068c60e4099b2628fa20093893e00d6a6a04ce168139abeb4f7d134165c5d7309987e067c3e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part502 : Box 0x1002000000440000000000000000000000 0xfedd823e624905088080b21020240400008 :=
  endBox 137 0xfa3d0ee3a0d00c1d906018c730ff341cdcded5739a9c0c3ba52759114393a388138c3d06d0eeb8f53fe7031bac8d7839b9bdebad3d0eeb9ae696a35d6121dd9a7a81998625e9012a39c3ba81328fb8f6735947c3baa62506df89e6703364a4ecbba943600e6b2925072d65a302b53279bdad2529a2286df8e065e940cc1cd3ee6c9409b12683ca7dd68f001d3ee12341c97a5544d138409a98e6b92764f36715e71b7ce6a9e58dbe6c9922e92936fc9296b2b994e6a7279e06313840cc72d388b40d62bde133974ca4e0c3410a4f0799aca90d8c1d1839026d5148b871cf462cd06d30fc60d0271838ba72d5c9e661f6718063154393b2071f611080619f0d5f409c7bf2f4acada9ee6b965ac5f83cc1b50260919cd68133df93ce066cb17596a10c3183ba5e96a2b53659387759838587765a7b57e836a04d54388c813593cc496a79b7d66b07f9a9e0916afc1b50261dd6a697a58c47138670e06e61c7e303278cba60cb71ece6b062bb8b21386137b6cb05068a7ad20f278e3020d1596c0d1530fc15cb8ee69abdd5686d4f964f1f4da0580c9175a1a05ca4e367923b18139aa41cba661f671641f3cb2d506a45ce5a735641443312404ad4f293ac5c18aa2182530797bac60cfb28395969f86df81a2b17596bb85278c3ed4f9dc5320f3032d00e51f309834628fa488241b658ab4ec766e65925e4a981967d9781a0571404139b7e385a45c3ba839730e17245dabf1cb51040cac9075943670b02dca4950697a4e4f286dcb26df0b1d0754ffb55dccad4f396a50ce4ec6317e50d833c7ceaff9eead5f (by decide +kernel)

private def part500 : Box 0x1002000000440000000000000000000000 0xfecd823e624905088080b21020240400008 :=
  splitBox 1 128 0xfecd823e624905088080b21020240400008 part502 part501 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part504 : Box 0x1002000000400000100000000000000000 0xfec49236630841a800803200600c0008018 :=
  endBox 89 0x18c6c0fc7d127ee4408ee3dbe83bad4c5f6a0136493b45a6515551acb00d43ba703169b9bc9dade3116065b5968c19efd64ec1b6228775802d7cd6530fa92459aaa359630f9c0d86f2bcc19661f904ec4f5038bed744a1c2d34a1caf3066bb8e6358515183c90d0e3831cc3e93b9abe8fb39aa8a639aa034c3ede2a88e3d07034a127b34ed01a82d71ecb1127bad2ce6ae6f8e3eb231073508fc6c349793dd01a82d6a7c6ab901aa356b1b9bc9eeb4b81968f995fed4527b9c9dc87c1f47315428ab06e38fa4ad5f670341993ddbc6216964bf95eed5f737b176735bd9d5ee941803b07d593b06d8bacc20765a5b175dc416cf6b381a89da7b208d644e0e5b2d2cd2b3d9e0e6a070e19cd5262a2734acaf783ca8d47cef67498b5552c401abfe8c3c1d540ed4f2e9a81e83ea0dda8afa140617dac5e4a1be8e6408f4147d54735d06d0eea4ad0664f76f188b032d696b4f6afcd3b622b58e066a4ac9eed63b8e8187d66b292569e5ef17da00e25abdb507a5ef468cd33839c1e569ea359006833839cb414a0a034c3ea499682d5f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part505 : Box 0x1002000000400000000000000000000000 0xfec48236420841080180300020040000008 :=
  endBox 105 0x3e8b4d7a200771ac7413417db38613276d18769bacb47ce83d4f9b57e596a4fd07ad5f877eb2d183987d2771cd527e83d28f987d546212849fc71147d9cd505a83d7c180279cafb6afb0c43ba70b4199cd58c45190419b5962d7a7cd27e711527b59649f84c601d9fdc3ba92949f9c44a3f2bcc01292941993b64f993cd27e8336718c385a09e401a4fd607bacd35623a9263030797bacc478c0a92542716d527693f59ec9ed62fad2c3ba70b7c180640e160c383bab355d0fc713cd62b1cd5caad2d927ec1b72ab9bd88ec4959ab12683c86349daa4904ba00d0669a358ee0f9e40697bd066613640e160cd966af738e6ae55419ad2e59e9c2d066d633861f818a61f988b145527e7e318f824fd9c6f16c6007ceb17925e0c37379cd58933954196a138c26917527b07da6e61f8e329438c2661f1f3cb1727986cdd877124309c1e6068978d6825e3819f07958ba48ba2506037a92562b1aae6a381b41322b9811e095385b984e381965154a0c6ab839b9bd6560c530fbc0fe40070b731b0494a50d40f0345a5b27cd82aba35365a08e4d65aa49596caf37b7a4fdabe0c5949f00250a0250c3bb280563e8fb5a7a93cda723ed682af398961dd509a8ed613031c38e3bf63077f0f9d27eb159a56d5f (by decide +kernel)

private def part503 : Box 0x1002000000400000000000000000000000 0xfec48236420841080080300020040000008 :=
  splitBox 1 68 0xfec48236420841080080300020040000008 part505 part504 (by decide +kernel)

private def part499 : Box 0x1002000000400000000000000000000000 0xfec48236420801080080300020040000008 :=
  splitBox 1 90 0xfec48236420801080080300020040000008 part503 part500 (by decide +kernel)

private def part497 : Box 0x1002000000400000000000000000000000 0xfec48226420801080080300020040000008 :=
  splitBox 1 112 0xfec48226420801080080300020040000008 part499 part498 (by decide +kernel)

private def part495 : Box 0x1002000000400000000000000000000000 0xfec40226420801080080300020040000008 :=
  splitBox 1 123 0xfec40226420801080080300020040000008 part497 part496 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part508 : Box 0x1006000000040000000000000000000000 0xfe4b921ce22c0f008000ca1000200c00000 :=
  endBox 75 0x1a0731c8411286d1466a477714370f9dab68390658344a3ab238892b6ad86dd19f049c126c5b839b53e0e7330d4f96220c16ad9b7c04b3dd4002d5b510ac6c122b537719c6adc5a14868f9d072c13921ad5b38fc3af69d86bdab7023b8d5b900e0d158193fca3e88388d5b50fc70b3ecc3c9060b96543e0cb8d2a59b0e1a4ad8c065aca66b0a87d3f21c339aaca6413c1cd43e83972cbb8da33851f72cd07772aa01cc561c7518832c1a318a5604020e718adecab55518b56d052b2d8c52d5b41ca05e518b68e23385d395f6b273889c7c19646200d4d381cd5b518c1ce60eb95c126d5b60ece576a78245ab65ed49127b41cc57a7d3049b56d25ed5ba0e6b2705cc7c9623b06412271f6adb38e2205ce332d5ce3ed318dde93d042a41658bacb5c459188724bcc568018a4bdb242dab7030ddc5918027f9fe6836b965072b15732d0736adad540db2d0d657020430a5ed671ab662b62dc9e33099cb5607278d826b41 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part510 : Box 0x1006000000000080000000000000000000 0xfe489774c32c4f000010000143004000803 :=
  endBox 85 0x1f4831f0771cc31498ad64f39bce3ea09485b8e5462e39968ab833893f943a735388b10d5b485c3b5518ce62876483a4fdaaad5b27ba4fe510dc441886adb30c02480ad506cc1548ead04393280c2d89dad3348c871e6b3ad4e4a0b60b3f9ace93f0e1cd675c0376b2f8bc6919517a4bc156b2b96329196218c279c1c7055b00a61a80a558cca212f1b48615f8725a0506acae0e4acae350bc7359d233075918a1315a3b4cd67f359c3864ed671306214426a1b6652182bd232b8071e4148afd62f13b672fb53d62e8e790529414f6cb3f052bb9023380d1285ad064a0ac5438ed67940068b53e3fca0a567f359d43ad5b5d12c166828e27b82de6ad83366adb10c60725ccb28bce6a0af608cb41279b48de2cfd8c068b0de7a89cd60d730a5ab741ad62f07f48fa88649fad5da6ae65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part512 : Box 0x1006000000000000100000000000000000 0xfe489234eb2c4f88000002000028000c010 :=
  endBox 45 0x1f0831f477164660a1662b486c01b7bac60cfa6095063832d8c39ac93f2f7cb2f522b90629600a16b57817b06d9626b2949f940649fb989634ee72f832d48a09f27bb60c603356449fac46279a4bce6b07380362bd8c1a87565739ad20ec5b50eb58d640e1c94171cc7d3361b175aaa2bd63127b31343760c51dad06d497acacbda8e3183e78fee7354139c7cfc58a8ac6620a7cd492b414a1cc2d625a0dd8824f3396cb2f41ca4c5b40e3cb2f50d947c1a20cb41cc50b6f14372c556aa1bb279870d70721ca430d9acad25e0ab514c1b3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part514 : Box 0x1006000000000000000200000000000000 0xfe489214c62d6f081100000040000500000 :=
  endBox 141 0x1443716c6ada98a43203e704f828d00f2d15aaa2bd2fcacf6309a01d8c691807c014e7f7927e93b0e3c51d8c561bb27fcc4f1c7a4fc14efa3b08e184cd45a2c5e3696c0d115fa01da6b317e0f3181524a8858bf3d9e69693cd486c6320d202b540315c94126293b5607247438e62b8da291d49f8abe3e49fe5a970790e1a4fd48501ac7169457ac5f0cab205f98b4a2bd690d073368c1e4faab0368180240fd2041922e48b696b925a5b41e6068b4b5ccb2c0da6662b73118285ca31482a4ed85b14554628398bf262b631746216c601f805382b4e6b41e60dad2d49f8676596c1e4386e629809f92763e7811900e3cb03509945549e7d3927e51349fd0758c56a4f04fb987e24ed49f245da6e93f699c515514c09f838e93b7714c0dcc93f27fa50e303004e0f2021696944ce229eb596c19d49f86e540521a004f86560f30345a927d315ebddd41ac316a4ca62508e30c64a18a24bc629b490dbe9439626b418c0c8393f4a50d80510c7d3732a0e4fa717bd9c721cc2d36fb5258627d3a0f251548ba50f839ae6a99b7d22e9436c14c098c8c55a29b7e581b10e7b5a8365899b2522eb0310c8360f807256ab178415a62b589c5b55a082b58c285c0ad6a4cb4158ac00941a07d5962eb437c14c57ed0735a2ad0414e9314a1b4019d413d079615c7d5826e82783c8345626b2f5a0829d1c53104e7f7814a9f958a8f9d6071fde0e6d498b6a9f962dc0a76c1263250d67eb4541cca315a0acb604730e5b287568250b595c62b068c62b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part515 : Box 0x1006000000000000000000000000000000 0xfe489214c22c4f080100200000000000000 :=
  endBox 119 0x150b4d1d1746adad8a431809f051a84e2f1a4fd2863e715ecd6759e978cbded2338de3e81b76c0c26d013ce589834476723162f1bd9e58c9f4e60a86ccc56b19596cc1549da4a67318c494a4ee30339b549291b69ba92661bd07941ca7b5452ee2d1646b97e4c56b134a1a6019998625ed04c9cd65c16c5218c04f828cd2b24fd2863e715ecd6759e978cbdece378e63e03e7521c9294a1984d1c49230334ccbc68270cd83462f1a09da6b2c141a2c3152486ce72fa4fc9d29ed8566b4105798ad68b250cc2662b73128169c50b498a4ed20494cb3f494cb19279c93f771d8720c2693f89feb479852b2749f825d68b1c2d27e1a78e160955d1605b17071013e0a30cdcb112f198acbf3068d4263e74b12447162b142c12e19b0d1be0ce13de3e99c2cc5714547cf06cd62ad2142e27b9c2e315bb8e233862b068c8072798a66589a4bd27ed55964e3e7589a48c1b8236f7558aa4f419b0b4da8e8c2e0a499aca51560fac4cdde92949db485018a1662b92630b4ca16b6318d37962718349fb04c34e1b3451827066c766a1f89c6c13811a6f142c767354521ae6340d225051f9626a1d522b4ee83993ddeb6527060832d1c289a4fc75f1cd5aaaf5b8c572506 (by decide +kernel)

private def part513 : Box 0x1006000000000000000000000000000000 0xfe489214c22c4f080100000000000000000 :=
  splitBox 1 57 0xfe489214c22c4f080100000000000000000 part515 part514 (by decide +kernel)

private def part511 : Box 0x1006000000000000000000000000000000 0xfe489214c22c4f080000000000000000000 :=
  splitBox 1 68 0xfe489214c22c4f080000000000000000000 part513 part512 (by decide +kernel)

private def part509 : Box 0x1006000000000000000000000000000000 0xfe489214c22c4f000000000000000000000 :=
  splitBox 1 79 0xfe489214c22c4f000000000000000000000 part511 part510 (by decide +kernel)

private def part507 : Box 0x1006000000000000000000000000000000 0xfe489214c22c0f000000000000000000000 :=
  splitBox 1 90 0xfe489214c22c0f000000000000000000000 part509 part508 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part518 : Box 0x1202800000000000000000000000000000 0xfe47d26f534d91540000000000000000000 :=
  endBox 35 0x661685618c0d88fb503b2824e220c76ada4fd03b380c020366aaa0b4e3e1d5591cd2159ab04d27ed5b0eeabde6a3a074e06ce358c63b0d5b05f9c4418a58d91969f3485a5040272825eeec1957bba0e034f66218774196e3d93e6e43732a4ad026d4d409cd4d59ac4f340987566b3a04d646019c6a7ce5f495b57d02670b39aad08820f5ab72d3527f2035256c2b948a3c96a7a04da9a93f93f341cdc76d456a7a04d69aa45 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part519 : Box 0x1202000000000000000000000000000000 0xfe464a6d430d01000000000000000000000 :=
  endBox 143 0x100418d63a0f60c1c5f69c2104f34a13440e9708236afcb4d1f3c9072f1aca5abf07d503ad3651a8b3671ecafd62d8f7c59ad5b49f8f9e057c3ed761c05a6c629315ac8a6235e609a04dabe70b39a97ed686ad9c2d27f20f4557245d885a1cc41ea45e522bdde406b48527e3ed6b3c8134a1ca477f18c593cd5b1f3a4fce2273553160571262c59812ad3341ecc29401bd7e7b2823569eb359edb390d69a49f614a8c548e82d063b30f82d0d20fb5844a104523c5ed4a1a43520518cb3f58ccc49518a4ed46b200cc0ab45615c7c5401a3ecc0a6059612711385b38c62707358e2298301181967b183523ac0cc0a735410b5eb539acab03522ac0e518a45e39aac0d642d1607291d856c4d401acd5d0012cd5f71e981565ea21524823e518b0ac9e6085a30681358cc6051f6cb4318f824fd67f1814e6a70351ac6d93f6b4f49c6e6f965e4e3580ff3250d68a60539aca355a2bb0f03e0cc3481dd6b128068a91659fb59d68a9435aaca1b98b6b03523ad149c6d5b925293f5a6b4880280a45484c929403ad35052827969a0d1597b16e47dad341a2b4d998068937e6adad3527e3ed2f4cd5b413b100cf494cb4d737a0b544328d543ea4766180065a8082990720b79eea1c16ada09c113245d68a807699a00a2f943e839597a9160e73965652a1b49f8b4523eec418e00346406b56d69a629315a90b41c9dabf0fb63071c2d4c411a02fdb59e0e3aca4596b4b941aa496b3c72d0e38b2dacf29163060bf067c0d163198396c0c75a6d07383fa32ce6ad5b165aca438ee82cd61658216046c60d02683d (by decide +kernel)

private def part517 : Box 0x1202000000000000000000000000000000 0xfe46426d430d01000000000000000000000 :=
  splitBox 1 119 0xfe46426d430d01000000000000000000000 part519 part518 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part522 : Box 0x1042080000000000000000000000000000 0xfee8570e73cc31861040000000000000000 :=
  endBox 29 0xfa3b9002e0e22d030155103a8198e6a83351dc8195aacc5b27fb004ff732c2c740e82b503b20cd4272075066d5b59f93fc6024ff9c85d18b72c5daae1d1409a0f580690c92b0e8bd46615b4860dab354a09cd62f4a505b06616ab1c9c36a0bf55162b355dac6b4d5aa9cb5aaf06de393b555ac20b5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part524 : Box 0x10020c0000000000000000000000000000 0xfefcc726c3dc01a61478000000000000000 :=
  endBox 11 0x340f83e88e0c1d544a0b5566a982fd686703695c90b7bac5e9485a4bd65a93f05fcb574fca4fce0672d058cd6114e974d27e72d9486307 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part525 : Box 0x1002080000000000000000000000000000 0xfeec4646434c01841040000000000000000 :=
  endBox 153 0x2d0cc0fd61febe8a4250ba38881d4168ba65a6a504c5692f98c4f0f827fa0365a1a4fd69a92b690cd3b927ec5b483a0352823075a6c5fb406b88d613ce174978c60ef8316d69b41dce6a6052d2cd3d51093cd545a693fe6b1b4f648eba0e2241e48c8c0460ed5f9ab64ff6b1ad340e3235cbf68235a6a3039f95fe93f69eb55d46b290ce5ab4d7d1dc6b1c4591d02fd98ad4371c2d492307396c70b5a1cd214098c1cc52d0250c62384f53a14870162f351cff2b432fcb0458b2c002de69d82fd1869dad567bb85f4b1a8139a8e0bf82f2d476b0b48669e9fe4bf2c115a1b16562f02fd686d3d581804907931b7e0e65f9595ad05d07bac7f972797a56aac5990261757bab801dd8dbec595aad18183cb93c55ae438bd2f5b57ea04d656e013fe0e73ddcbf21dd696d079732bdd5d04716c4512323879cdeafd9a8b39bd20eb559683174d026b23889a338c4362d9c9e40993ccc0b2c25c7a813735ce555249b84c0a7274a0d027aabf673781a42ea1810c2ce5372a97e56ab348dcca4ff401303e0bf207b8dbed3b0ba9c4669d93cda7713cda7a703279d07969ea68aa2e8c0204d986303aab179eee92b0c2b4b4e3ed4598b72c5ce06d57381cd2d0eeba0b23486495b4860eab53e5ab859dabe70b6b0f8591857310c3ba92b368cd5f485b53cba734b417e1dd7aec05f0eaa81dc438fc1d569eb59ce4ed82bfe1e4b48e69eb88c62a8d5f93f2b2d0629c7ce5ad01c9d3f2d3d90324eb2becd45732b99658ab9656aac41279b40e0280c41816e8191e4a0e4e40eec4eb69e93ae691a288e3516039b4f605b81b431334f5b0721b0466af974d6aa8c356e2f086de (by decide +kernel)

private def part523 : Box 0x1002080000000000000000000000000000 0xfeec4606434c01841040000000000000000 :=
  splitBox 1 114 0xfeec4606434c01841040000000000000000 part525 part524 (by decide +kernel)

private def part521 : Box 0x1002080000000000000000000000000000 0xfee84606434c01841040000000000000000 :=
  splitBox 1 126 0xfee84606434c01841040000000000000000 part523 part522 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part528 : Box 0x1022001000000000000000000000000000 0xfee0d6844a1f91080a04400200000000000 :=
  endBox 101 0x3f8f8388c62a8de1c7d5c59104e3e70e3c7356a6cb4d4a2005911039ab57e5a093ad88eb0d9a8ac1769e93ad262af79ab6d5f4a1ad0dab72d3416e4eb39acc199a8ab575a69cd5dc681bc591b45009d67279476b4d9a46727509a45e393a064ba7353d69a3e7510cd4f4a1ad34e4e3e79696917393b59e39382d5986214c1fab48d2b969ad574a1cb0d385ad3569b1a0d2b8bc2929521b4385b93e6afac3657face5673290d2768379286d5f5a6b80b41c8c22d3415f02d47eb357c7ce6ef055ca3d37782d47ead62b8d2d968e8391f3b0be732b045033181691b8f55f6d5b05ba4ee735b17c57a917377b580b787cec5f80b292970110391845a6b10d4f87ea0af631ac732cd6736c870c7ced2d80e20a336c8af54932d05acef6b94923e71fab183f55007ce827949f181904ef6b5a0cf676b3bb8a13949e3e75915462ecd5f05a8af4386e4f9abed6705ab59e7b5b93cfb20b56aab48d6378aa0f9c5573534ba6d4f0e1b1766abb125ea2d452e9b4f6623b56cbd2d578dbed450d5b174163069d8463015f02c5abf2c3569a3f55a6c3f5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part530 : Box 0x1012001000000000000000000000000000 0xfe7ad786420f49020a02400200000000000 :=
  endBox 27 0x72154501006823461dc276c1f63f38c05acea3b41cb56e623ad34db33125ab63017b9c3bf413b554602e23b8d03f0301661c06a68ff58b720a5c7b20a662db5356628cb983ac3551dbf0c42d3662d8ff5ecf316da46d4d126cd65473bdcd69ac1d62dad3662db075ace3fd1fecf6f40ead3568306cd69a301 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part532 : Box 0x1002041000000000000000000000000000 0xfef3d28cc69e01220e08608200000000000 :=
  endBox 21 0x348962205d3371dc6adb88b4d922e94317da4ee05babde05b98a617da50e5ab98ac5f688170d5b57fcc3538f97b4c52b4d39acb3d5a5984d62f23ee0fab5717d984ddc7405eb356cbde613183987e5a6828639aac55ab6b4b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part533 : Box 0x1002001000000000000000000000000000 0xfe63d2c4420e01000a00400200000000000 :=
  endBox 153 0x340ee368d204de5a6b4b47fa8334019474a3ea4144d5483100683315ecb236aa98ad2532c2617d8bee83188741c017dad050b9ab63fd5a6ad8ae02de1f3a01d43f355416ed5b3eaca33732b544ba7287ca16d5b02c816dd8388c62b403a8cc7fab4d9466d4d948e62b17db489632082142cdc6b0ca1f519a9894247e522a50d345a7cd6162da4a6414c1ce8359635686d4762682dd803e016eb418ba2d67596c9e56a5975522f06d49db56d5ee92985a26e394e3f3a8c5ab6b424a569b3dbe0dad611feacb6168b5847fb2d34a16d5587fa821a04e2a8d556b0b88b4310cc3b0a45809a3b55a1ad3569ec431fead3e0cdad350668338e06b158e16d2b0cdad35006c43943e7354a035f20f47360b76adacb568706d988ea1f385c3fd5a7a58aa1b88139066a1f519ad09a13dc75731358bad47419a0b61fead3410b2d4da8ed236a69c7dd8621641feb0c66a3ad2da9f2bdcfaad47504abde3eab51d412b4b385cb4b4a07fa7ed969682d5a7d0735a6a0cd544b0dc7f143ea336adcb4b385abece6ad5b9696b42984f74d01467359a46c43691c70b7bb8ff569a3fd98b706d69697a6691b1358b6d4d39ab30e20ff4e6b1fb5696d379066703969a83362125734b56963fd5a7cd2d7e1886707fae22a808f8bd2b4f6adb12502671138fb53e2e9ad2cb0377c0b762fc1ce62382ddab65e99026aa3f8035a0fad5b619b994e16b4d4019c45c933995006b4b6b3cb4b64105b34dd696c420b638897a507a803969ae2394e5a68ff4e16605315ad05019aca3fd5a69455ac5b1441f3a00d5b409d1812fcc6064958d36495a45d62f073510bc6adb8f672ca4ed026e438c0c9078c3978f679aa26ef721c606483978e4f8dc29174ffb994fee26d92771872fca45d3fe813 (by decide +kernel)

private def part531 : Box 0x1002001000000000000000000000000000 0xfe63d284420e01000a00400200000000000 :=
  splitBox 1 114 0xfe63d284420e01000a00400200000000000 part533 part532 (by decide +kernel)

private def part529 : Box 0x1002001000000000000000000000000000 0xfe62d284420e01000a00400200000000000 :=
  splitBox 1 124 0xfe62d284420e01000a00400200000000000 part531 part530 (by decide +kernel)

private def part527 : Box 0x1002001000000000000000000000000000 0xfe60d284420e01000a00400200000000000 :=
  splitBox 1 125 0xfe60d284420e01000a00400200000000000 part529 part528 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part536 : Box 0x1002040000008000000000000000000000 0xfef5c285d69c01221409024041008010200 :=
  endBox 21 0x1dc49fba0fa33830761120b3dd5ab60b9060ac8f5d95f707f483b594dbf24165a1b08a61cd657eabddeae0bf594a4ed62f1b7dab60b95abc6e16adac09058fc65f9314ad06621ab6c199a46b2d36f82fda8b3dd4bda719 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part538 : Box 0x1042000000008000000000000000000000 0xfee153cd768c21001001025040008210000 :=
  endBox 31 0xfa3b8fe1475c455060ec0352e3029cd52c59aca33836ad55627142ce4f02d5032b023106d943e58d28587452531878742d5b28582e66ad8746285bf8c0359627b8744e6ae236906d388c61e50facd4196a1f98332d358bed5b0e8c4f7641c40e882fe39aa4a605ca4ed6ab1878da2735 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part540 : Box 0x1002000000048000000000000000000000 0xfe6dc2cd760e01009000825040208410000 :=
  endBox 123 0x3e8ee368f041851d28fb582cb9026a31065b56c60f001b262f4ac0e7bbb56e518822d026e8200942a8c228c548ab2f8bf2b554f9c629595b08d62cbd6aa94189ea0cb71cd06b30293d546ad6584f2e59504832dac5aa97ee409832c9e724a40c26e17120c58060e6e19652c5b4a1a81dca64f3729ce6f62dc813494a50c196aa1388135809eb1b7d1f728cd8924f5a3024f5a0e718a4bf2a31522ba0e22983074012872c6548eb554a1ca739bd286c5b9284014670738c0a7f95229e83639aab0752f4a45c736605a0ead2d62d9bf6836a834e6aa62e0b552f12531194f7e04d02e8774ddeb29486b56e471a4a43ba5e96adcb2937143f28cc3bb17a5aaa917523caa2085a368a1f519b51e065a00ce172c8e23a070b51acf773ea9cd41963b39eea81339aa00c5f8ddef770eeb56d48f06d8dde1dd8c1cd5b36f877548ee22008e300711741ac518c8136ad832dc7b348c6dab1f12eb11e30f3dcdab6e597aba00d026afb8b3e8e7617a00cfb3232d0260cd3859a460ee832dab741fdc4441a8f38f53e6afb065b56ce161dd94920cb5c1eef1efc3bac2f05cb125a7735943bac2299002b0c82d55ac71ece59494a4ec17eb4b96521dd494a4ec19f13cce1693b594b58e24180d1736caf750382fce22d3d5a0c0bf58a84b657ea50e0e6d3d0eeb4f6721877523ed5ba0e6e437b6b57d40e0d15aab581d558bcd5b068a0663649c0e3d0ee833d68341fcbd307f98226a9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part541 : Box 0x1002000000008000000000000000000000 0xfe6542c5560c41001000024040008010000 :=
  endBox 81 0x761887007ea3fd5a6c1d56919048fce6549482d417a4eb9ac6a078c0bdbe0f2d5f49fb58661882c527ec61f8b224fdf47f0a26c2b98b6727401cd4b732a925a4393a85606493ad6aa819965b3e8ee250527591ac27a9f56067a9145f6afd8c0aa4760acc45063a91419f2d560ff0465a8ae4962d83349eeee3086df940293b38fad5419f1b9e0669c9df4691e06009ee51f617cc1d5a6b55e0ff307589ab09819e80362eb055546b1006b23962af578e163c99486d22b00cd51acb5557ecd57503b4ed69ed3b962aa074948f25492c63b893f6d0dc334856060c727a949d544a0a169438fda5ef52297be597ad56690a204f72ccc7ed1e4ad35ab60cb9a4361b460aaa851f907aa3158fc0cb690ca4958f93dd8bac83b84f7690c51f025cd3b72c832d07b358e820766ad8bec36b356c1167dd41e9c2d21b16563065b57bac1b4fda70b (by decide +kernel)

private def part539 : Box 0x1002000000008000000000000000000000 0xfe6542c5560c01001000024040008010000 :=
  splitBox 1 90 0xfe6542c5560c01001000024040008010000 part541 part540 (by decide +kernel)

private def part537 : Box 0x1002000000008000000000000000000000 0xfe6142c5560c01001000024040008010000 :=
  splitBox 1 126 0xfe6142c5560c01001000024040008010000 part539 part538 (by decide +kernel)

private def part535 : Box 0x1002000000008000000000000000000000 0xfe614285560c01001000024040008010000 :=
  splitBox 1 114 0xfe614285560c01001000024040008010000 part537 part536 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part543 : Box 0x1012000000000100000000000000000000 0xfe784f8f460e49000020002089010002024 :=
  endBox 57 0x1c87e1886307ea3fd5a6c0392799f347ce7f7169a788279a56b4d0e6cd67630fc69127ed62b00d16716aa7f79a46e5f6a2cd2395fb1876abad05842f15fab55691cd4f8c39fdda47353e30ed5762db38d67895ed233fbb995acf355d69ad456b19c180c7f71f38c0601cc6d95a6b994c86b15fab3f36ccd6747c8c05a9f461dace6d9690cb450e3b59da4321ac57eacfc96b2d35a9e0cf47ca39e03db580cf9ace301690c9f36b3ad15ac5100ef0c05006b575a6b56c6032bfc57b359d856d034c67b5b4847cea1305f8c0554450db32315ed6c130e3978d0660af9aca83d0e3ad36626b88b41838eb2d49f8c047cf2d1527eb4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part545 : Box 0x1022000000000100000000000000000000 0xfe61ce874a1d19000020008088810002044 :=
  endBox 79 0x100308a62509e3789314a1bf87d796823e7413a4fe0678fd6275b8edf83812448fae8e6d927ed67690bdace3e4f35aba9255449fc72d4fc9b7d682b57696cb096b0b535ace3f52e0dbf28847eb2c65acee4f7bab18f002f5a6b281d6ae72d0e3cafd8c0cd2d57fb1755fa4f35a0abce5aaa47c17e9e1e8e0230fe24a5a0781627074504e92033d6272c24d927d7524b966524c70b6abaca47eb2d8c42380a7696c6d33df8efcd8b1efd42693f968a3e71facf6f49fa84d69a1c38f7e72749fb4f4ba69291f3ca13582a8d569a0b1053b48d0380b4033d45f3dad836b551faa86e579ad5567f232ce5a5d383fc001721a8bd5e6b3f2f0ca2f6ad8fd5c85a104f03047ea91781821d148bcb4d6adac5d88661a0641d0370cb4150d8fd43bab41904f1b4e58acd3d2799b85682b4d067c6d36b3a8bce16d63200c7817a7358e3ea1b8e6a3f5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part547 : Box 0x1802000000000100000000000000000000 0xfe674bcd522c09000028000088030003004 :=
  endBox 47 0x1e06d1a4068d06d406ac55ab6e394199474a3e8c0ff4a270799612d215a6b53d252d5b968761886907fab0142e0f339bd65e93f470a50d69b24fe6a4a4a5286d224fc0ef01ed48eb3f494c93f94c3d13c594a50e1c7ad1478eb4599c5d1a4341fd45ed219c72b2f40ba91e5a0b4b5286ec287e0f32c0c1725d358a974e5a18c62127e0b589ea3fd503c1c7523b10b15819ec1341e8ff4d457eca1f523b0ad5ff033dc45913e6c2b9026b290e3a436519c943 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part548 : Box 0x1002000000000100000000000000000000 0xfee34a85420c09000020000088010002004 :=
  endBox 125 0x1c8781b4591a0640a269f38c0a8fb6158c1c7fa51f83cc7b76a4a8cdabeb4d1feb20b438051549fc03d1fe9c2cc0a62b396c307385ac09e25091745128707f8faad4d4f1a7fe0e6813699c9e3370cd237219c2d23f359d8b6605183a989a2ca5857390d02673593c6b2b735c9e3396ac55026fc3f83fd4a1c9eb39a8c1d27f23ed3d63079ab63fd9286a335a69474a3ee8358e2356e3158bec60eb02e08c2d0917053cd21413ac5c7fa93f285b38d21904ed6105c8f9d62f35860daa334a1c1e602da78d69a3fd285bf8d5b969ab2983ca91d00e3fd927eb4d530fce7f77bac6954868f9c0b302e5d8621986807fa7a077522f2914dde6e1235c76397943e1ab9286d6100996360f2e22ca4e5b174d89a171849e7d55813c2fccb457b5ad3528650b968a605737cb45891b209dac293f6909bbce4eb424fe1fe942dc45239f9e388a78e5aba45d68761c4701886b127e3fd40ec62b62dcb4d47dcc2b30298ad857305543ec434868ff460ed61907a93f1feb68d613d43870becbdeb19945eb2f2f7cb4d49fb409420100291548ee218a64a18c1e0ff250d65f175d85700308f659466943711eeb307cc0ad6750db48e24cb93cc0b304daae4f56b07cf310c60e5ef58ccc5b517a87d2871815d0711ab718ac5f63075a120b34c47ce6ef6ada4fd69ace29818b9a7aafd3708f9dacb04742be06940b974dab690548bcb01a062958bc8f35a1a45d2871fde4868f9cc56b57 (by decide +kernel)

private def part546 : Box 0x1002000000000100000000000000000000 0xfe634a85420c09000020000088010002004 :=
  splitBox 1 131 0xfe634a85420c09000020000088010002004 part548 part547 (by decide +kernel)

private def part544 : Box 0x1002000000000100000000000000000000 0xfe614a85420c09000020000088010002004 :=
  splitBox 1 125 0xfe614a85420c09000020000088010002004 part546 part545 (by decide +kernel)

private def part542 : Box 0x1002000000000000000000000000000000 0xfe604285420c09000000000000000000000 :=
  splitBox 5016 124 0xfe604a85420c09000020000088010002004 part544 part543 (by decide +kernel)

private def part534 : Box 0x1002000000000000000000000000000000 0xfe604285420c01000000000000000000000 :=
  splitBox 1 87 0xfe604285420c01000000000000000000000 part542 part535 (by decide +kernel)

private def part526 : Box 0x1002000000000000000000000000000000 0xfe604284420c01000000000000000000000 :=
  splitBox 1 108 0xfe604284420c01000000000000000000000 part534 part527 (by decide +kernel)

private def part520 : Box 0x1002000000000000000000000000000000 0xfe604204420c01000000000000000000000 :=
  splitBox 1 115 0xfe604204420c01000000000000000000000 part526 part521 (by decide +kernel)

private def part516 : Box 0x1002000000000000000000000000000000 0xfe404204420c01000000000000000000000 :=
  splitBox 1 129 0xfe404204420c01000000000000000000000 part520 part517 (by decide +kernel)

private def part506 : Box 0x1002000000000000000000000000000000 0xfe400204420c01000000000000000000000 :=
  splitBox 1 122 0xfe400204420c01000000000000000000000 part516 part507 (by decide +kernel)

private def part494 : Box 0x1002000000000000000000000000000000 0xfe400204420801000000000000000000000 :=
  splitBox 1 94 0xfe400204420801000000000000000000000 part506 part495 (by decide +kernel)

private def part478 : Box 0x1002000000000000000000000000000000 0xfe400204400801000000000000000000000 :=
  splitBox 1 101 0xfe400204400801000000000000000000000 part494 part479 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part552 : Box 0x1060002000000000000000000000000000 0xfef9360c28f704500830001000000000000 :=
  endBox 37 0xe2350aa3d071f39ac1e648fa48d5eeb5758097d56af394560282905bb409027880962fc69d0e89bdcb4341a41730750e8b600b983a2837969a7279a0441e8730def34b47ceb4d39898053841ba9365a6b55569b2025cda5d35a6c01f581c6158bed5b41b9cc640b8f9d06e0afa0eeb196278f9ce62b4537eb40b002de6a99634dee9294a1a0255c7a0ba7356ce629d9902e3e705cc6e9570fef1bbce62b558dee929 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part554 : Box 0x1820002000000000000000000000000000 0xfe553fc50c170c100c10001000000000000 :=
  endBox 61 0x811e8700e629c1f0805902aa22d0835696cb2f6168fb527ee679072a499ec26f75aa87747ead4310d00fd46e32835056b0d37ba90d02e7f79492afda0d27c949fb56d05282b9ab6c45906a93f1faa706c2408156314454106a93f60dc0896a38f25ede2d349dcc17623b40c17985e0b90e4ad5637bb58e581ad5434a83b3fbcb4d41aa0de412a0d5a05812049fc3c9414c1ae48ba0dda9ad42d56580a4fc172a2f6adc902d166b1ad5527e58b8fee93b6a6af8f420a506ed4120d5b0ee8286365c1de6aaad3d4362cd839d0776b0b9b42ca4b16adb56e15fb53588589cb3760cbdb459a1c9300b50c21c094348fca2150dc7c57abb59dacf1755442c2f9edad4f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part556 : Box 0x1020022000000000000000000000000000 0xfed52e0c2a5605181811111000000000000 :=
  endBox 69 0x1b0511686316c49fa60fe28e49deb4590122d3968b28ac5a6a4d281b409298fca8095aacd5b2f0bdac582b61b266adbdd56aea2b1f6940c7eb30cdaa67e55a6a0256c4c0cc6a1102819ba683f861dab673151f9cc6440da735560eea03526b56cba735560ee731281c731404940e398a20d03a06e99252d5b377ad543ba5f56adc7311d0acfe72fb56ce632d55fc681601f6c731494a0655c7a0beb2d156ae817398ad5e2daad3502e1dd968a3f53fbc6ef398ad14d931cc47ea0b9701a07f17c404ad5e02cb56d02ed5b9a85a1263140d69a3f5610e8498bdae1a98a0d8b24652f0b975ac23bf9ab72205dd8506d5b5f016706bcd933dbcba6e677b3b5860eee80fd602a8f9cdee5031f3c3a7029974da8f0f9c0b205d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part558 : Box 0x1028002000000000000000000000000000 0xfedd2765089f44110814001000000000000 :=
  endBox 53 0xa2240aa24fda80cec3ed2779c7e04611c771a750727fb41db4073149bcc19834a51c6d300c5cda0a9928e3c9441e8810bea7d99ab673148fcd5b1e4c1ee3ec9fed06a3c946bc819589a0d5a8781546209de71f0eece5105cb80c3798b27319acef672d18fd605c93be6118bf356d86ee516a6a51c16682b591ce51492a0dd28e7316a13870104a71f2f0c83740ca4ee0bcac85f587eab03393ac6646b9f9dede3f56f1a0581e8414a0ddcc2e8c937474bd9d26a73146bc8c99ecf18515f9cc6834a4d5847b7c06739882bd632b4537ed069928e6fd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part560 : Box 0x1020102000000000000000000000000000 0xfed5a6248f160e140a14081000000000000 :=
  endBox 39 0x36102398c61cc5e06a1a671785ab671949f9c7da440ac83b6a78b4dacf24fd02b20ed20b2d5dace83b5109fb07b900a6fd41db56d69f41ed1db06983b8fd500af0380735924a4fd6ada0ddc771f15ab64fd37ead3651fa4fc166a39460d857bc3f55a7b56ce3e7f5402bb8fe2f83df969ad5b41babde404ad35ab671f83bb4b5ab720d528f356d69ab83f8d2d9ab609d3fbc1dce5ac2288e43816e1af057a0ed1d302bd66ab359ab6b3983dce6d6a3a4dd69ad5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part562 : Box 0x102000a000000000000000000000000000 0xfef5a724883644508910055000000000000 :=
  endBox 45 0x7f1e05917037eb50cc1cd57c51a8fd585b2cb60d2c294a3b0b600c9cc428a145969abe41a64a3b5866adc7f50a8a835076937701b0480fc6a127e982c06521ac062dacf6f37bb502718b2a815834ad54c0271f5aad0696b0aa8b4d2f0ce3b398b945ee309c5acf18502da8347ead4330f42055eab2d5d1e65e11faad36617a8bce05a6bdbe624a4d67289bde7b7b58546b014d632e6d6ad980507724fdc86c07ea8158e626f7969a8358e6293f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part563 : Box 0x1020002000000000000000000000000000 0xfed5a72c081604100810001000000000000 :=
  endBox 117 0x6c1a8700a3652158167339455eea1b49ba4fce3e7d9414aa8c62d560b9a90cba63af58a9c7d44732c9477bab56e0ee83b5a2cee2cbe385c1a5ab71c2d38660e3eb4f946b187166b90e46ea3cdab6b55927ec43d0511421a07317c398aa89e24d60ef354d606b3937ba49659fc1a6415cbe1f906949a896e40ba35e40ad07558ca0ad68b20ad67f20edab6b2f83b9cc5204b0dfb2c0dab6b456b0cb1337ba09602bb55630a817415b40b02f8f420a506e04b846a2cd474a51d24a7314e2046aac1fe46488c630ad5b7b69fd504af758f8ad6758cc0a36b3c0906985a6d5b398a40d4f834c9ef131810d61a3c9404a7be7a1ac32cfd1ff0695979cc5077461502aa21cc60eb20d53de93f58ccd433050d361fc402b80d01c08179ab6a49624a0255c44102e8c99caed5b61797867b6b05dab7011d5ee6f747fa90a2f8e326f794423f5517abde37babfd436a431f3a8868c3b56d1da6f77a98fd5486b01c06f79442a353ecb2004b8d96af739a9bdcbc2839a0eed5b37bcaff1fab56ddc630fce3e7a0d271f57fc83957fcd5b624bf8b02408375a1012c2248d2d371056d4f93b6d5b60bc1dda9f39053be8ff37bc8ff57b9c90699caeb4d300c6f7834b56d82f34b5ab7077415cd2d5a69b8c5f9ac28176ada3fe696a51dac66f75a6a1898064e586a3fd672935586c82b37b974e054ac35056d55 (by decide +kernel)

private def part561 : Box 0x1020002000000000000000000000000000 0xfed5a724081604100810001000000000000 :=
  splitBox 1 111 0xfed5a724081604100810001000000000000 part563 part562 (by decide +kernel)

private def part559 : Box 0x1020002000000000000000000000000000 0xfed5a624081604100810001000000000000 :=
  splitBox 1 116 0xfed5a624081604100810001000000000000 part561 part560 (by decide +kernel)

private def part557 : Box 0x1020002000000000000000000000000000 0xfed52624081604100810001000000000000 :=
  splitBox 1 123 0xfed52624081604100810001000000000000 part559 part558 (by decide +kernel)

private def part555 : Box 0x1020002000000000000000000000000000 0xfed52604081604100810001000000000000 :=
  splitBox 1 113 0xfed52604081604100810001000000000000 part557 part556 (by decide +kernel)

private def part553 : Box 0x1020002000000000000000000000000000 0xfe552604081604100810001000000000000 :=
  splitBox 1 131 0xfe552604081604100810001000000000000 part555 part554 (by decide +kernel)

private def part551 : Box 0x1020002000000000000000000000000000 0xfe512604081604100810001000000000000 :=
  splitBox 1 126 0xfe512604081604100810001000000000000 part553 part552 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part566 : Box 0x10a0001000000000000000000000000000 0xfee4f6168d52a1880214000200000000000 :=
  endBox 89 0x1686a1943911072169abc2f83f5691180e7b4f67b7ad4d5f64eb392a93c15f3dbc9d6c4b6adce6551eac8c9d728eda5a762f8a3b5278a6e58bad0d66b24158403dcd451dda8f52862b3961a6d3571ab734b53b6e5f369ac8ca065d3460a06b0d9646a15527b0de5a0ab0bc3a03f549ac835517940c34b250c15ee824850d7b5cc0b517873e51eb0ce591acd58c5f1a4527c1b750982dc39ec599646d5f9476b2351eb1664f6b99d20a93b6f07eae826071342144328f54921cf858b399c39e6c9839eb2359aa93e1599b252027131facc6230ac28f549eb3d969ab055918b15abf020d68eb4d561a44e036eb399ab609b513ce419ac2e671629ccda5b2c1568e1b75610172c8d69a6e9733cd611c98eed69ac2328be3901cf7413ff12bda7a4eb3929cbc9d706dd86f2d04a066ed2e9b88ac270b238e26d5f691ad2d04ad427fe6069435436d2398aa03b2759c4dabe9ff6afc9ff586ac8cba7099d3fee6716493ad04b1c4df0586ca1b118ac25ab66d36adc721 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part567 : Box 0x10a0000000000000000000000000000000 0xfe64e6178d5000000000000000000000000 :=
  endBox 87 0x6a1c8561787407eae220d60e7a0ace660d738bcd5b0ee9c4ce63400f03a0ba07741b32924e66713369c0d959168630dd31eb6302b2d7329b4d49eb4d062a4fce872fd0696b09b4d6aeb4d36dac8d66b2415846b575a1cc23498b995646b57927eb4d062a4fe37493f4e671819ac2a4949f833c18ad2318e83400d7060c7250eeb56e3989b4ce4ab4d839eb2359a831ce6290d966a73106ca50e482ad3d47a73149fad343bab440093f7414c292b0ee62aad360eaa2f283ac6e5809cc605cc947061ba1002f852550bc9310609bb45933db4a06731272cd5b061b996061acd569e731711cc65168398b18f024fd647073c1b2a3d0e7c511405ad3d104f7c2ad5919b252026e95a6b08e0c9c1b54060d9591845d18c49039e9c0eed4c7aec0937aeca2562ac6c97bad075369b48d407308dc82f574301b32d3cda72c8d016a25586cb23369ba071781b21cf8ba64fd8c082455eeb4b8da2b3941a9ccc1b2b22f0a39837683541db04604cad2d016d5f927e713969a731 (by decide +kernel)

private def part565 : Box 0x10a0000000000000000000000000000000 0xfe64e6168d5000000000000000000000000 :=
  splitBox 1 108 0xfe64e6168d5000000000000000000000000 part567 part566 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part569 : Box 0x1030000000000000000000000000000000 0xfe5ca7060a1e00000000000000000000000 :=
  endBox 103 0x20c6a1bc711e82869485a0701a9a617317a8f66af9bed69a04987329db695a84e527bd45abe3e769e982d06f206d3b6b4d0e7a05d58721e8836c5033989c847da7e58b6ab4d1f3c1cce425032facc3d49f940dc0581a0571ac413a0e569b39756a7309187818281957d988e0e72bed49e7256ada88d62b87256adb90e5a6974ce6269b949f18757eb55cc17357d616c1b37d816e305b57e3f3ad3502ed01cc605fabecc5eae2d068c0abf4c16d3d1699cc6303356d5faa177a158721cc1faac4651db96569a60b398a3b62839c1569aa435a1c5f5398a4fdb02dac8ed8c39f34c1662349f9cc569b182cc5e9e2b0e4330d5b836682b5a69cbcff71a6d6562bd2f39c1569a1a7969a1b39ab6b4d581ab70724a0eac206cd2f230c57ea150a2a90cd3741cdec2d8408e21cc5bc5a2c829288ad4e2838f9e5a6a0e65a38294c5e5076f1c030cc83741c8f9e2f3cc5f317ac0ac230a0d1f6834ce5e733595c9ed6b3a095487380d4340de3080d3392cb4d060c1e6392a065072f6d942a1c93929b2657fb56cfee0d7398ad366ad873d27f07739282fe6969cc549e1cf392bd1022b8ac1cc502b2d5d056721511037306decab2d3f3abfd27eb2d8fceaff581c6254129c8439b1c8419eb19817a697461ad350360d3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part571 : Box 0x1820000000000000000000000000000000 0xfe592fc70c1000000000000000000000000 :=
  endBox 111 0x701a8611e8179ad8d03c06173119c80d937dc81b398c93f41acb1937da0ad6aabc3289e1cc4b4f2d3526260b560d97356d036b5549fc81b305c3f506cc8f35a6982dc406ac0d95a6c73139019e0d365101691f9c764bd622c93191e693f5a2b88f63400d959cca2f5a79cc569a93f0679864d531cc606a8fb4c330774e62f4408bc3080d9398a0ae49fa0d60ef24fd00ad01c4c1b2c17969a9df62f826e58f9ccd3bec224061706c988d67324b565ebe04ce736c1dcb06b4b69d873da772c36736986569a93f06caf8de318fc073d06b24fc5771c85905820d30eed036837399c08ac305e390a0acfaf35850370779ac281b905619b40dc82b392b18f041d66ad8b353c364cb4d15d826cbcec4783fce510cc8a2506b021c8c5f903683b9ab70e15a77069696c1fcbced0310b01894c5e9e24ee83ca8f49d67314a19b2e3e69c2583702fd785912840da3a636fa47d06a709275b51e49f8b4d600e7ce3b36fa47d286b2f3929cc662ea02e169a4fd944f178580e62f75a0fe35300db56c7ea60b4f5a4a5286a21c8649f982e58ab02d5fad2288a298ba694349fa02d21b1f9d492929579c93f470a50cd5324fd06a73151106b24fc0573dbce423f5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part574 : Box 0x1060080000000000000000000000000000 0xfee9360e39f014830040000000000000000 :=
  endBox 103 0x711a85c1544e1b038f9cb5000619f665a1a0a4e5f2d0d0730798732713612b48dabed82f89e02fdc0403c72f6919cd5072e4b8e5eb3f96027336b1a0a4e6b2cbc3a2809061af8b202dce6b28ed84b30ed6ae4b39ab67135a6b30d6328a3b96465f539983154041cc809397c1d150aca295a59c9d073355d985f13c651c8061ac26374ad2d04e73358bcc5591de913397a09d072d6396268292f0830da5f3d4d81ab0d611a3fd0120c338ca0e638cc00e0200702f880945106ec1196969ff397c2c558fa4ddaaeb4d9c96a114ffad08374f4c4e96aab54c792b4d0c3ce6d83b9bf658fa7a544a8d72faa0dd3fe8395916869ec099514a93c2ef355c74e5f537eb5563eba805abed3d2faac8b42f8ba2280b3509cb4b005c6fd69ebdad83ee4b58f809e1e0b4acdfad57514a93cdfb293d69a882d164ff8b14dfa9359aaed55162a18d3d606cd49733abdc97ec55981ab2228b413adc05015c527b60b4d41ca026696ad15187289da5ee43986ed2f404ad3608fb56ce5eb15374b0dc0e71c1549ec119c9e7055aa9bbd407003a320e4792b42f8a296afcd3905f9c4e2faa93660597d5a7ad5f8166b2f7b17c389b48605fad1640cc5f5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part576 : Box 0x1028080000000000000000000000000000 0xfecd3e47a9d544c14040000000000000000 :=
  endBox 31 0x1986a1a01f6a4fe3938724e4f288e22e882b5807765f50ddb0f68c2bdad87b461527f069649faf8d03288802cc55b0acdebf4615ee67c5162ac06fd89d682541ca93e6a2a4dd6ab1fdcb1e8d70579bbd204e1acf1b6d1866ef0d4aca683bc13b7aaa89e0f68256a7a3093f51dc4eb594821ce4ea3d69ea0265139b6c13a735 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part578 : Box 0x1120080000000000000000000000000000 0xfecdf6262dd104890040000000000000000 :=
  endBox 41 0x1a85516468148672d39a8756272a885246d5b9d05d1c8339743aad5f5219c7e691b57dab70fd418a71f2e1a8b139418a7274fca88594393abce4ffac65a6aa49904ab22889c2488a1fed07608f84fe6fd6aaad2cdfb355563eb420d5a5f23b5866b4f589ad3415eb2996721bb8c0c8db37ea3fda5680b5e1145a7cd6151393ad10700dfab4d96aa91369ea51da7b1f1e594b585a7a8dd944eb0d37eb5851069eaf8b4d3e3d0798c0c7c7a0f2af7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part580 : Box 0x10200a0000000000000000000000000000 0xfeddbe4e2b5405891055000000000000000 :=
  endBox 73 0x350e82d8cc140de85a00cb34ecb6a0bf2fa87747ead6077659f9c4d6ab390cdde7058e42f41e8aa380c0b62ab9963fbac556aa839527ca041de275a7fd626d3d514b57e382ad55c0697c80962cc61d69a70593daa3da0e6b4d7a1c04fecd5b59f9bbd6aa3f50ee9c4e377acfd6aa3f5382c7215a1e8521181f6ae0a4f9ab60ab158b55c5572d3507316bd27eb4d62acb4d6aba84c7eac2da30af7558ab56c562b4d49fa4894238be01e5ab71ba502e0c189330697ae93ad0132d0d8a6d5b471c0374c817039cc11a0f69fd377b56c17f20e4dd2d0380b02d080941cb60b4d697c095696ac65aaf0775a29c16696a9365a2c1ddac83bca0349fb4ecdd25a99aaaa4f5aa81cdaaed5f5d0b0033cd3b039b585aaed5f374ad0a21c1649f82ce382819549ed3d6b0b4f66ad857cbea4eb968aa2b49fb555aaed5f5aac6e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part581 : Box 0x1020080000000000000000000000000000 0xfeddb626295004810040000000000000000 :=
  endBox 107 0x360ba2c04fd8a0ede3a090146dc84f204382a88a4f7bad18169597d4dfad5759f9fedaaf2d3d87b355d69eb3f81167ea239ae6b1b0cd02aa03415a056500a09587b24d587b277cba682b49fa89023d07fb415b5561ddac7d4071686736c6143763bb7a170059cc2362aa35d1ba2c55a7c8256b0b0ed61a06596331854efa05c57ed4318b20316396b56e7ae82fc18af42f070b87dab2d96ae901374a056041804430ab4d6ad9c2d447aec8dd62a9ba54063bb629c6e9611ad3d2037eb9081596aa6e949fc0699ab6815521b78d43a0c614956838fbb83f549fa7b64fcb54d6aad21987af6f6a987765a2b48567eb559a72d570eeae0bc1c7d984a3c7c54029c2c7dad579aaf2bcc18b1c2d28ea8380d3b58106b357e0d2d2d41ba93578611c1a5abf12e5a5ab4d49aa80e5a6b55d69724fc30ed2d590bc2d3d069606ac8cdfab39811aaf1bf569683538bcd5b5aa9bf5abf205d7837ea51e38fa3fd02ae57927ed616a1d0590a1a705969a70b38cad365109cbd486b4330b20fd4e331cb4dd2b35691cf5362ac614fd2d477b0abdd69ab43396c70b5a6ae080980fef535a1b4f4e5a4eb928ee42c8c6188d5f80866e94ff9bf4ff6b4b6aa9c1544e1bb9696d615919cbce0b1859aaeb4d6959ba46a727b5a7ad55382a7fe51dac8d5ee5d3 (by decide +kernel)

private def part579 : Box 0x1020080000000000000000000000000000 0xfeddb606295004810040000000000000000 :=
  splitBox 1 113 0xfeddb606295004810040000000000000000 part581 part580 (by decide +kernel)

private def part577 : Box 0x1020080000000000000000000000000000 0xfecdb606295004810040000000000000000 :=
  splitBox 1 128 0xfecdb606295004810040000000000000000 part579 part578 (by decide +kernel)

private def part575 : Box 0x1020080000000000000000000000000000 0xfecd3606295004810040000000000000000 :=
  splitBox 1 123 0xfecd3606295004810040000000000000000 part577 part576 (by decide +kernel)

private def part573 : Box 0x1020080000000000000000000000000000 0xfec93606295004810040000000000000000 :=
  splitBox 1 126 0xfec93606295004810040000000000000000 part575 part574 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part583 : Box 0x1020010000000000000000000000000000 0xfec9668608b100820400200000000000000 :=
  endBox 121 0x3a100340c43f0625317b88f61c7e5a9b56dabee57486941ce4e5254e0e6324fd3fa92938fa50e398a4fd286afc8fb4a193ad3ff2bece62d5b962a0bd38faa89e32871f30bb8ee4f5a50d27f350de288521590e3e93f83dca35253ac8d076a3596268c3349acbd67f38ed65e71f503c71f6ad9cd5cdb02355567f24fce62b3f839e7256c1ec650e27355527e731290b58cc28872171ec8dd6adad3d83672549fb5071980b718751aacfe6aab56e51a8f9ce0a8159aaab4f49fa50d42c890d591c5b5393a0edabf1cc636dca133fdb58ac46163979434e0aee34b66af8f9ce4b357ce4f2c253beb4f521c4510dfa7277e127f28a47ced5741aa02c133293d4523e751ecd3d5aa9cc5405a0e626db9252943514a93ce431bbd21b182d426943377b50e23d8511948693f290a4fe6a2982ce5a9ff942660b494819e02d944527e7316a1546afca4340582fc39672d39aa90ac1c9d741f6acf649fa8bd4928dd947ad6105fc84140f51a30b18705fb58502a9ff69eb55dec49fc9f969a82fd49206f8396b0d1faa4fe05faf0ca28ee2758eece62b1f9626d55412a0ed7c58fcd555a78f9d27f28a5aaeb1f711a84f0e3e72d2f9c0bf6afa50d423315439e3ed398c08a20f9ce62d2b949ed4f7aea8464ffac8da7a9e3156526a844be63e747071b24fda9ec550e7b5852449fd1816ada375696d3562ab03669aa80a118be60bf49f8f9ce62940f9da57315417eb574a19ba6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part586 : Box 0x1120000400000000000000000000000000 0xfee96eb62c9089920022400008000000000 :=
  endBox 47 0x360bc2887315916841a93ae40286645a693f489cb4f3dfb56deea0d937e8f9e49f8364dfb251d00a4eb06cb58f00f9dd04501b207b968eaf7048c37f37ead1c30f230daaab5349fac8d5eed4f8512193245bd56302f5d49fb95e5a7ac7c1b2de2703e7640bc5901372c8d672c22d0d2d629caf769186a58a72bdda46b400ae839b48c322b4d461c375736c1ce302d23696d073801e0917b5b99c9d6d2d43184390bb65d3897ed2b351ca016918da5eaa8ff590dfb2c353d696277e839b48d402d678c0c1ce08d892dcced5b57bad3590405cb0d6a7a89e303009406623d2e9a7acbb7205569a6fd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part588 : Box 0x1024000400000000000000000000000000 0xfed92ed68832c8120820480008000000000 :=
  endBox 105 0x1ec681e06f13c5f19440ba0dd480e7a80e83b9ba5662a03a0ee6e9582c61657db56dcda3e76b19ba5204e1b0581d062230b3dbd3d6c5f1699c1569a5116420d334b585e713733cd3b696c1a585e8099ebaa396add185582b4b459ad2d8ff7276d5fa6fd5a69c1585f2935ab6b3d5a6ac0c428e627e94457c631052a2073d1d31ccdab65a791d28c98c2a85496341a4e66d614e0f8b0b3470a7f52dab4edaaa922bf51874615ece3bb50ac2d36a7a889c2a0f6da30a1cf6adb4edaaac4b927e1cf501ce6d40dc615ab61cf9aab185621ac32cc4dfab5348158580e26a018792c59399acbe461cd5b5a69bf49633944fb68c38349bf569ab03104f38a0ec6057683aa32569a1cf49fa78d619cce5cf374a0ee4f20ef0f9d69a6e92f3a7be8c2a3a439f06b6f18c5f167f073c7cea22482d32f3c82b49fd07558cc7bf594b99ca226fd7b7a4082b37ec5e7389acfdccf277d69af6b8349444dc3278aa218de179d7c051c7d7054a0ddd0508d06940d8f2588ec5f275cc499bc0e5c6fd41b9bf673393ae302a27057b78a29947a837614ca2983b9bbda45f0fb7230d27f06937082bc396a239b61dda06d27e901fa657ea096461bd9cfeb461501293f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part589 : Box 0x1020000400000000000000000000000000 0xfed96e96081088120020400008000000000 :=
  endBox 103 0x741a0621844f0c4662f6f1c45f01b21cf87ce9ff8e0ad616b0cb22d36364a8ecd932d341b31cc5e05c20430c944641b9cc50c06ca3fe59ead3d8532788e388837288cb236adc73141ccb2306cca4d3989444c33378f0278b036083747fc617398836584404c617696b20713969ab0d09dca3b8c2e0d9474ce6d5a7a3fce620d95e15447fc73149ab0873157bce6b5979cce5a7a4fe0d2c49927ec47398c6175e1843989903e78e26511305acfdec412c0d9305c93f900a51137eb789df9abe7133998364dc3408d8330731590d9323a50723e7591ad3d7c41cc1cf3eba4fd5ee3e7474ca256a7a4fd5eebe240672793f507280994726c950893f57c58014b24dd696d610e7ac8d0731858dd2d552f9b18b2230e6a7b4b60ee8094f5a89d84491a5a8d798aa5f3374c8095a1a9f356d636d230c8ad35013359e302d2361dd1855a59ba5ac2e23d8862f098244649aa7883996725f36adc92559ca0e65a78f9d05313f558364d07360f82c569e93762cc837488c616691c1cd02e6e925fa36cbe6839 (by decide +kernel)

private def part587 : Box 0x1020000400000000000000000000000000 0xfed92e96081088120020400008000000000 :=
  splitBox 1 122 0xfed92e96081088120020400008000000000 part589 part588 (by decide +kernel)

private def part585 : Box 0x1020000400000000000000000000000000 0xfec92e96081088120020400008000000000 :=
  splitBox 1 128 0xfec92e96081088120020400008000000000 part587 part586 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part590 : Box 0x1020000000000000000000000000000000 0xfec92696481000000000000000000000000 :=
  endBox 11 0x5905f22ff6c1485a0e328358dc20cd49fb2883b839ee4b8bb6835506c1cf3e5836419a9eb8e5a71938fc0cd (by decide +kernel)

private def part584 : Box 0x1020000000000000000000000000000000 0xfec92696081000000000000000000000000 :=
  splitBox 1 106 0xfec92696081000000000000000000000000 part590 part585 (by decide +kernel)

private def part582 : Box 0x1020000000000000000000000000000000 0xfec92686081000000000000000000000000 :=
  splitBox 1 112 0xfec92686081000000000000000000000000 part584 part583 (by decide +kernel)

private def part572 : Box 0x1020000000000000000000000000000000 0xfec92606081000000000000000000000000 :=
  splitBox 1 115 0xfec92606081000000000000000000000000 part582 part573 (by decide +kernel)

private def part570 : Box 0x1020000000000000000000000000000000 0xfe492606081000000000000000000000000 :=
  splitBox 1 131 0xfe492606081000000000000000000000000 part572 part571 (by decide +kernel)

private def part568 : Box 0x1020000000000000000000000000000000 0xfe482606081000000000000000000000000 :=
  splitBox 1 124 0xfe482606081000000000000000000000000 part570 part569 (by decide +kernel)

private def part564 : Box 0x1020000000000000000000000000000000 0xfe402606081000000000000000000000000 :=
  splitBox 1 127 0xfe402606081000000000000000000000000 part568 part565 (by decide +kernel)

private def part550 : Box 0x1020000000000000000000000000000000 0xfe402604081000000000000000000000000 :=
  splitBox 1 109 0xfe402604081000000000000000000000000 part564 part551 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part594 : Box 0x1a00002000000000000000000000000000 0xfe5f3bdd00053c000d00001000000000000 :=
  endBox 41 0xf6388ec3500e15312c49db53e0e4a47cb42b3f5aab59d200e4ac4e49fbdb66ad8726699b9763e2ac4d67eb4d6adaf8c0280aa20a506ef758172a0b6ad938d6331805ab6f57816ef7549fb56d04e9438c02807699a45e300b56da0500c0320ddee71fb52868276a1444948fb66adb8e658ca58d5b89c69e35a28e4649fad34f8aec3d0d00fb500f20dc3bad378f8ad31053a4a59048bc1c94a1c4e39052837 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part595 : Box 0x1a00000000000000000000000000000000 0xfe4e23df000000000000000000000000000 :=
  endBox 119 0x711d87c1dc781e847dc3e541e98645e67fd06a837d7c069b38d0075d3c83bc5e741ba0a66b082662f38f0e6adad3412ea475a6cafd6ada40d424fdac179826e0e5b904b3a2bb06796765aabd09e16766b3abf4df6b4d2f9985d6732cbda426fb6aa98bcbcf23a5256afd0ebb50d63280cf6112632d347862f37b11f7392ce1283d5a69a6e3ebb59dc82e671f6a3d4b47000e0eee41733a505cae3ed6507daa439442d4d179ad35ca30285442c2328be2c01d77bac0a3352c62f305a78e5da0fe8f504eb4ecbce0639eca62f69db9b6399a87d48ed3b305af873382be6194f19bed9083bc15f033bdd569e09d850ece20ce47a8fb4c461dd066bd0c80fb4ffb203527a1dd65184b20b58aab4d00fc8f54fb9ff584ac3d641ec0e4a826495b51d216b4d626cb2280b4d9ab6c5b04bb136519b56e3e28b3569ad2350c2208c19e0d30ebc83d305a0f6611e8305c6235f03af24ac9c6b4d9232d5b37bc4df72ca4bcc3292b06b835606bb50c6032d680eb985e5a6a02527e5e78c46809800c2f20e5012a62691879eaa0572eda8d412e093836d0739e85f0c2e6236adc6fb2629ccd6332ce5ab6d5b906ece340f81894c5e83d927e8fb4a18bcd69b0304e4ad42a8c8204e3058bcd94494c60b5a69fdd026c2387da60b5a2d0774a0ad345e62cd927eb4d057982d986a1847204cc1a72f1f6a39e62aac656aa60d382d07949fb15526260d (by decide +kernel)

private def part593 : Box 0x1a00000000000000000000000000000000 0xfe4e23dd000000000000000000000000000 :=
  splitBox 1 109 0xfe4e23dd000000000000000000000000000 part595 part594 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part597 : Box 0x1840000000000000000000000000000000 0xfe6233ca308000000000000000000000000 :=
  endBox 65 0x3e0ee2f0f41424a3ae23383f35a6caf759c872c5e65d59cd6b2f5a29cc5ec2ffcb2f3989cbd67f1b6dab6b45470a08ce621cb974293bd100338ca185c3b724c507a3f30b8cc53312b095cae0d593ee28361ea08c1b61db969a3f3069c1db81a6dc388d83380cb819ac83104f7398c60d398cb4d62174306a3d61dab54456a3f3163a91e048bd8d656731969a2c76519c1f9bd02f36b0cb4d317b9b61daad0d6ae3b59686b57306b4b63998bcdab6d818be39093dc3a272198405dc92f4a09cbc7e6d5b96aeb4d4199cc5c4551b01f9b804ed8e5e73106683559c0edc62f735d06d462ad5d07a813392c1d3401bd80d78e421d336dc1cb06abd88178e2662539782de (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part600 : Box 0x1804002000000000000000000000000000 0xfe7f33f0a0350c004c02001000000000000 :=
  endBox 89 0x1d86e1984e0d851102ab420d5b077127ec82981c951ac90d5aa820e042a91e7a8c1ad21ab135a6cd5b1699c8e6d8a16c5d5a6af86e30b6518b56ddc280c8fb49da8c6616809e7a8b56d19ea628d66ad8245a5a7f949da09e41cb56d68650a169439632b4d589ca1b8348725ec2a6360b4593c6b55521c93b7b8b95e5a6cb03482a4ed04a8356a1604f168413a3cd0572c0c5a61c9285ac0e523b56d68680a16b1390561c92eac93f6b2b53e504c0b7517ad366ad942d056a032082142da04013f3395d4170736adad158b6829523b56e41c9fecdef2cacd969e362d9fed006820db2d54d96a313fcc1de152acacd969e58066d5b2e9aca5602d438ee365a05d65a8fb48f898e09dc615cdea0b008c6f7580b56d3c650b486a88ee3189e24fd9c37bacfe3fba0e5ab7353e5300ff356d04eaff1e4ad5585701fdab68276a68f2527f2cb62eaac0d6aadc2f8ee356e5a6942d04e93b5d127f0ae5ab6b4d0d793de6ad870479324fd69ad5b151c827 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part601 : Box 0x1804000000000000000000000000000000 0xfe6e23f2a03008000000000000000000000 :=
  endBox 71 0x591947707f6d0320b4d988e2f36ad947ca4ed42f00cb069a0266a994756aa9eba0e683928ecd3b6a05c324bdab6515069af05159ab683b28acce291e6ad8bcc196bc13de523a0d5076d5b031cf535a6b20ce3702f3781ac33175282d5b28aaf092b399ca471e3c7334059f1d27f2505dc681edb0f04d92509293a78dc39be4ff9c4dca272f069a93e002d1c26757fb975282d51397968e6adb99c10ac5d7b7c5d3412a46523339bdedec5d41ab70a21888355d1016e5781a6c5d728c0cd835834e72b833504b034d44597cd5b62ea3d6729b955ede9e3053bc0de360bc03341a6a31927eb4d6ada055ac3390527e5b55a6bb8c8147518727952169ed5a6947dca739bd1af0738c2b0b569a843dc65a0a05569ac4b616a78be2d356833d8d462d5b392bdbe6ad9f65edf356d6562f340aa796382949c5e60cd819e2f3 (by decide +kernel)

private def part599 : Box 0x1804000000000000000000000000000000 0xfe6e23f0a03008000000000000000000000 :=
  splitBox 1 109 0xfe6e23f0a03008000000000000000000000 part601 part600 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part603 : Box 0x1800400000000000000000000000000000 0xfe6663c03a0030008000000000000000000 :=
  endBox 75 0xda388ba3604035e18c398ad0d63907a3c9284a4fc9eb1425a84a01963c98e4aa311aacd6383fa06528392ca4540ccc31661b8285cb4d293832d6883fc09b000801d492c5d60aa4fd69a9f394923c73978b2e23ca0f4c32f82f0c4b9416a0d5a6a8cca12a498ba67135a6af86198e66d4d90266c95a6b56ddc631ee331553d6d397a8876c19651d293bd5683c824da7306d065947ce62a0032d27f1cc5a6b3154c5ed5b571b8398bf8aa3e062360dc93f505a914e1251d392c7d7927e62531782f5ab7291c17a07f948a7092ff82edac5d128397a916392a06628fa344e2f2d34a3e91f8a4ea45317ad15405f0c027315a7c2d150fb56e5a1446c15449fb56e285a90e4fca50d632d5b6adcb62a8397a0da587365b484a160ab1d6c0230988ebda76b0305ac1ce58c9fb53c370def02e4fced5b505a01cba702e4deef578172d5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part604 : Box 0x1800000000000000000000000000000000 0xfe6667c0000000000000000000000000000 :=
  endBox 85 0x1c46d1b86201ca41b20ea4fe6b3835cc1a7139946c0826d6318f624fd58483cb570729cbd2830bb569a0e550154398b54e5aba08ddc7b8ce673f3a0e5ee3207648ead2e1798394e5e81d81ca0e58e4ab4d781ec5101be0e566188b31745a6a614266ad828d27ea3547cca0d733c5093feb388f5a0f28e1137b9553c2d492ff8bcd7859fc50936dce55160b08d43302f33f0e66c1598ba9f3521b05662eabfe521a4fdac47cc35f5a29ccd282e59814a9df2cead156af461d27a9e3399a4fddc7f198072a88415616d0772eaa0e458273149fb38a02cae2eac1a42d2d6341c9cc5627359504e7e7398c7ed5979b2e6ad9faca1673149f9056056c93f3989055a8661ec206b68c825072f7c0e4a9198bfe81d0728bcc4c302dd23a941398c5ff49eb600e5419cc5d5a6a4fce6282d98966f7927e731072ab8da1cc60ef2784bfe2f36b1c3b11c4942605dbc0c1998bef6f0a4855527ad5b285a4fce620e549ec7312ff988e5279ccd2820e5 (by decide +kernel)

private def part602 : Box 0x1800000000000000000000000000000000 0xfe6663c0000000000000000000000000000 :=
  splitBox 1 118 0xfe6663c0000000000000000000000000000 part604 part603 (by decide +kernel)

private def part598 : Box 0x1800000000000000000000000000000000 0xfe6623c0000000000000000000000000000 :=
  splitBox 1 122 0xfe6623c0000000000000000000000000000 part602 part599 (by decide +kernel)

private def part596 : Box 0x1800000000000000000000000000000000 0xfe6223c0000000000000000000000000000 :=
  splitBox 1 126 0xfe6223c0000000000000000000000000000 part598 part597 (by decide +kernel)

private def part592 : Box 0x1800000000000000000000000000000000 0xfe4223c0000000000000000000000000000 :=
  splitBox 1 129 0xfe4223c0000000000000000000000000000 part596 part593 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part607 : Box 0x1280000000000000000000000000000000 0xfed66259d40000000000000000000000000 :=
  endBox 149 0x3a0e23b8dc3b02fb7b17806eb54600f80651e693f518a4dc7da61100fc28f477a3cd87a0cf399b1564a387747daf63209e240701c4ce4293f949293f9543979efe517ad3d2467bf945ed515a7a88be2c36517b56d24673347fce496ada83527e8ff8ffaa49506af89a2f1181926e947531202e5394928f3a3020073699774f02eec606491c61567ad4b506d1812eecd3749faf89a07064a387064919775ab717758aaf6338ec067e51a9cbd28e61328db209258bde9473979ccd8c4d03a65afa30ae65480a51d463291d2471815a6cbc145d504779844ffb3515462a0b9aa25afa30ed514779cbd9c651900e5c8234a398ac1629478396611928e5a3927e7fd5189844c26ec328a3f9ab61dd1f6945ca4ace1f1647fa7a4e12d5b0ee946cdbf291cf8ad5b0ee8fb5905f230703154929355069cbce668234ee506ad1daaa7130e0cd5b8196937761b864018307343baac288b43283ed6b2ca3f6b2cd5b4a1cd5b6b29774e123ed8bbaa4204e5a3a4c651fa88b43d8ca28fe384ad35906adb4de523b99c36273304fc9e94f0b52d94272c83d50b82c56a70e75c96e652fcb56da6f236cd4aa39519867d48a709651906d017307f9a6ea116afa0f583f3d9630ac415089b24fc69ecb536a5ac16470829d422c82000799cce7c91e4b544bf31879ccf07f470b4dc15272f732c9e9470b52d90382c72f523c0936129c2567ad4b6d1c4631885e018aec2c8e2f6870d6724fd315a04e15ba444176b238c3e1cb5a6c9252f7987c18ebc2d0ba3b082d4c0c52b4d315a9167ad96ada7694750ecd5b2d5c947518a91cc572d35d8522a91d6051ccc4d314b0ae4a3c813470cf658c1b08d89e61f591ad00c159ec83d49f8ade6ada50c592a4787da62b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part609 : Box 0x10c0000000000000000000000000000000 0xfef27218a78000000000000000000000000 :=
  endBox 149 0x1dc6e1d0711f017daf0d41f2e398b56cc0a62b6d1ab6731526c0db512c50b06dc72583a63f3731406c1a0398be0d4149d1f734c470307f50bbd9cbba9310e8a8fe60fa3a49daa33526977439b1774e5e3bd8dee7ed276b4c5b42e9c73351eaf85dd9aa2e4128097766adb90da28fe6ad949ce5ec22d5e48b9bdd4221d1498942e6adb9065ab9bb5a62da3d8be2c872f51169a4ff38bce65156a935ab6c4183a2d4998b27170e8ad35a5f070507ab4d6a103b20f49ff293da8461b01de97e545728fc3a29db96aed5b690b000b398b2b570e8b0a6355b13da42d55440133065569ae4b988209f731685e0a02e4340b0149d3eb356cc3a731969ad5b621cb4b6ad97e5287356c7e6b4d3988fce5a7b88da340e5f969e0c3398949ce631b4dab6b351f9b56e3159cc520b27d548e5276989cc5b4711047031418330ed69aa4f27fb56e2fc8ab4c3ae23e0f618a55c399a496398a8fe62ca495ab66f71e9c4ff303bd83f3409cb4d595b92c17672f019c02d411acadcce83d7b1442e15c376ad3477f3974ba6d5b398b92e51f9bddab6e428fe399974e3989cc662082e4e5eda2908e06dd07ad49854ee4151fb90605dcd5b3988a9e523b13d8b25f96c1cc50188398b70da2e80c76adc5dd3829cbd49b356c3a2b02c8e5a78745472d318da61d16ad81de523ad349d2947818ee4368e21cbe399832c3a31c5ce5ec42c06f789d21d151c874650ecc4362da51e05cb56db4721745f107ab4d818a82305da8962748fcd69ad2f8e2e1d1062ae83c98186947274830e49bad5e50893a437aa3971169b358569e3f35f1ac32d34e660b72eecd5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part612 : Box 0x1080420000000000000000000000000000 0xfef6f2139cc63108c421000000000000000 :=
  endBox 13 0xe43b8be13fce630b4cdf672549fc7315a0e267099ab6b1b169a4fce13280d424fce6307f801a7c90219f8c9f26ed060b92e376cd5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part613 : Box 0x1080400000000000000000000000000000 0xfee662329c0221008000000000000000000 :=
  endBox 157 0x1a4651dc201ba1002f02fb5613c4a394265a69cbd8b3248d462e62b87bf9222a338c39cc4a132445462c1f8b6a83362eabee2daa0b5836b4d4199cbdcc72178518c731284b100cb593ce655a3b176616821569f07f560bde93f6adcb354eface5eea4e5614c7317ba9b4d27f17bd05ae62f8b4147d785a7cc595a6942583f2d3daa2c4560dad3589f14258b25ef293c4ff9ccab4d622a0cdc8550e851126a0c5945eb4f6ad9cc527e0cb969e721985a0c74a396d6616832c9cb1cc5ab6ee318bc27873392264f527f9f850947fc1c1524a4fd8b31f2630ea21399b20be4007218a4e72f781b83fecf63737a8f4a4e5e24068c0b97e303240540531eeb2925852c4f5a78255c97399e302901941b149d80530fc480c0118c2b4c5aa25d3517a9253483ed18583480a546a093480c6065a1a5b392541a2bb619a4fe30ad4b941a11b8c09b4c127399d202d614fb974d048013c28fc72f389aa8be150a47510cc45620c9356a9c8ff6b1b034a3f2c34e664778c1b17541abc218d55a302395523a48d26ae639765059ff548ee5d9a8e7fd5b146b1ff569ea2191ff0705442a355f1543b126ae624dd6869dca210e09ccd43e4f7510cd3b591b94ce66a1f3fecb41ff627bb906399b52da76a474f1ca739bd226721397a891838f7e913504bd8ce66f6f9492a22d0d5b6a3c93f60a9c4e720ca215829f25a8ea49771b85e05f6c61776510a4fca26c02f8a214f6c721591b56d246d2d9cba9ed696cb23390a7b58c481477303547aa4949fb20a2193fea3d8c2ce6f605b9253e6a2f4f6ca215e158492c72f284c605246509a3029111b7c93f392ad34e5eaa300a22f84f9399ca2f6ada4d5ac3070545ed5b47fca0d49a870549307da3069e13909ff527eb236ada3fdc84f0e633925cbeb4d517b51ce4272f6b0c733517ac7e (by decide +kernel)

private def part611 : Box 0x1080400000000000000000000000000000 0xfee662129c0221008000000000000000000 :=
  splitBox 1 113 0xfee662129c0221008000000000000000000 part613 part612 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part615 : Box 0x1080040000000000000000000000000000 0xfee6e610869020210008000000000000000 :=
  endBox 99 0x360b438893f5e1cc491cd5b2e9b52c5f640b398c007f5969a2fb40d941d03702bd69b0bec816c59815a0af5a69cc578501b4398b88d4102dd08018271484c3b27958b66131d4c7e349ab1351fec1383fc7bf376b56dd05b0b86a0ddb07f8bf2f6d060940cda738e4b3ec3b14fb56dc96d5b8592a4d281abee8c39bb4da6e654feb56da8611a7b356d1b60316b2b9945927e38bf26d39ab6d43885036adcd3158698a51feb397aecc59698b56ca23251d472d5b710c57102d22f39756ae6ed740817000bee376945c773064dc962cb272a7fe72fad3da44b1b42e9aa8e235040b5f162b2924c26d5f9442d2b60e88c6133ad35ab6882d3613cb925ab6e8230503509cf6d6afb0dcd922c38fc6c374a1cd5f46db925a7b38e5ab6e6f205940dc46adcb0d315a3fd6722fb3600ab2d35aca06547dcd4b281b56db47113c205940630fa8f569af83d9e02a893d66a9db6ad98754872208c06b569ad5b695ce396afc61e62cad5d18725ca3d161c7e3280ba0e4181425dd17a940c6bb23a5acab0d280b50b62f85034edc6ed355a89d62eb57527b164c3ea3d85f6d2d4f1c45a6b56e482b9bcc262fb5abcc2951eb56cc570bedab6e4b969a2fb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part617 : Box 0x1080004000000000000000000000000000 0xfee66650840a12002100008000000000000 :=
  endBox 139 0x6d1c469190209af0d43406116714c4a3a8be8c09fadab6a431e0ce65506ad5e302923477c72f69bc72f801ab60a98e664f58da307550fa48d48e947200e5e9a28890148010b4604122e5da302e53049ad4e1d89ff63025c2d3e732b0a630aa0d72ea9880178c2993bf1856a2c60589e7e2887eba3029f349fc6064fbcc298c3c6168c0c742c8c59a302b235a7a92660fc605c972924ba6d02f0a824de0ccacadab6a47284b38b018b13185283946e3029234a3a88c2d91dec456adb4de4f2a82d806f1506705a6a6049e737c61630e7c9732a7dd41aa498c0c901364c614b6a51b2dac8ef5abb3900240660d9c2630a51b3fece4b4fbc615cca901091d1876a8b92d3eeb2b960b1858c0a3bd3ef24fd8365119ede93f60db56dec56143718a549272f399b6073196028235a09c94a22725986eb39477c5ed398a4fdec641503929cbd5f72d4d05ab2b5abad4e416b28a22d3527f356ce6283d384a08e398a0b5446a59c26284b56ca131ff594731a8398a7f6580b0a5ab60bb41eb56e608b055ac6a3f4fea4fd47f390527e1b341ea884b59acad638c09ff49fe5f96ad899e6b1a36dcce7fd27fb28e62b8f61cc5c4619c62b50f9494a2ec0258503839c7bf3649bdd6aea3352382b65abad3547f392d44314a4de523a85d26f291d38511ab728e547e942cae523a8456ae62b9422e23a0a1d9a9293f28885ce50ba3b5ab6629733c93f6adad5dc451fad5e29298a5edf02e5422b576a190520fc2fc98456af34dd657356dc82a21fae5a08b4d27ed5b4a0d93292471f1871e4ad5d227292544835c93f622b56d28595ca335aba87e58aa3bc927399c096b356b2a51ca22d5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part618 : Box 0x1080000000000000000000000000000000 0xfee66654840000000000000000000000000 :=
  endBox 85 0xd4103620ab48e22c841b61194415af8a63406076adc92362cb5545f673191da4fd283a4fe374a8e4e622fb8a0ed5b41ab56e283a0d57c5a1e0650a166d38e620dd6ad8bedab732893f900a607398a4fe0ca94454662fb9466b3981baca3982fb523ca1747fb56d27ea39398a4fe5a6b176523b98f8368c814760ff1efce629ff38b9454e63356d946c138398b0a6046a8fdab650b526b1666b2b99dab693f4b138523b52e374b56cfcad61462cf65737b56e0e7356d3eae55285af8d5b733ca33737d077364b60f61cc549b356ce0a7175a6b9066ada80527eb4d8fe6d8220ca1d0b4d512ca395d1b42dacc4527fc1ed27e1b73f2ce4b60ab56d8baa3fa30ad5b49fa7649ff3104d325dd38bb56db47b09ff24fce4a6c9927e1b749fc7e560ab1758bb13fd866b4d631946c05f6725944a73149fb556725ad349feb22f0b024fca267179ab67336b0d0778c2b56d246a3d927f251e6adc614522f75399b5841ba2fb (by decide +kernel)

private def part616 : Box 0x1080000000000000000000000000000000 0xfee66650840000000000000000000000000 :=
  splitBox 1 110 0xfee66650840000000000000000000000000 part618 part617 (by decide +kernel)

private def part614 : Box 0x1080000000000000000000000000000000 0xfee66610840000000000000000000000000 :=
  splitBox 1 114 0xfee66610840000000000000000000000000 part616 part615 (by decide +kernel)

private def part610 : Box 0x1080000000000000000000000000000000 0xfee66210840000000000000000000000000 :=
  splitBox 1 118 0xfee66210840000000000000000000000000 part614 part611 (by decide +kernel)

private def part608 : Box 0x1080000000000000000000000000000000 0xfee26210840000000000000000000000000 :=
  splitBox 1 126 0xfee26210840000000000000000000000000 part610 part609 (by decide +kernel)

private def part606 : Box 0x1080000000000000000000000000000000 0xfec26210840000000000000000000000000 :=
  splitBox 1 129 0xfec26210840000000000000000000000000 part608 part607 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part622 : Box 0x1300400000000000000000000000000000 0xfecfa26bf82826008000000000000000000 :=
  endBox 97 0xe63b8c62001d75e10c518a91d493356d69e6f549a9ff65b1e01f3b20711480c6f58c0ad3cdeb392e7b2c60527e6f5a302901733cb114fb9cb6302a331f3b20dc208cc138dc074189f291d69e0cb3d1a430add69ee651e19d106d9eaab4f7b9c9f7523a91e612b485c971831e1ad3d104d178049d18383cb155492a454a38ea62f7820deeb090d3ee3a974141b24d546a9f7980441d0385ae8a641b649b832d492b4fa0e6f572d6939505acc28c6480a7e4196b235e20db356caf341e568419cd5b5a6af0af39ab6f5799474146b2d3c9ca2b7969ee393f1a0ce0dae539cdea495e160720f566aa31593d079579b925345a7a98a4024e04d8f0e1d0c3a9272acd60e72c9c742b47272acd4f4836c9475a6b97e0e670b409b80901928eb4d836c4e563174396a4d63feb94d6a6a490e1a4d66416804cd06d591a0ccffa4e352169e935964e813385bdd6121815dac2b4d8ffa097385b00c62ca6492acd416e0c54311052128e2b1969ee55614b9943625939acec0b491b99566b06c64a3cb2f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part624 : Box 0x1300080000000000000000000000000000 0xfecf666be74500980040000000000000000 :=
  endBox 33 0x3b8e02f881d9eb28235a68314c5262b5215830eb003ed59cd07b39aacfe062a036062b186a03158ab23b56aa907272ca49720c1fdebad5b5a6875657ea38dc17ec15f24fc17e3ed6a2c82348ca90dc3383ed385ca493938b2e6ada4be40982ee50da925585a09cb34f45721c51f6ba04e59672d674a08755eeb251dab670b1adcf5d0eaad35aaed5f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part625 : Box 0x1300000000000000000000000000000000 0xfecf26ebe00000000000000000000000000 :=
  endBox 153 0x380c83b82f97a1e047cc61f06a837d78497c60530eb11185a30ef5f73795e411a93f627a41d282be025649fb1651f261f04ac93f30ecb224907b925e93d461307a0bdae6f9ab6c5b0eab16e6ad8756406b59d256f4204e5a7a0f5e03dfcb4d523ac6dab6135927eb4d5e198523ce3b7bab56c59a1d547169ad5b2d7ca337bab5349ca8139a8ad4f737d06d271b51562290b6e1e06301a6ce41ce38c8334e3eb42e893f593cd5b166b94647ab9b4e06e395a69c880291e3819b07d380ba813736968e4b8fa6d5b2d7b906593ac466adc1ce59ea04c9caee24fd4c65178309a58b4d8576b5547ace5d629ac4dca259d5a6c80362ab103ed98aa08d819f200e839ad35ca609b066c1ce8c2984d69a93f06fb28ee318ce29093f0e5875d887460e30a9f71369c9d01ab4f82ab18369e96d4bf6c8310ac24bd4c6e18ab204dacf07b5a7b08c1322cb5a10441ebd960d2a4fda8ac5b406cc2b9a8ab35907a93d2fdc93d51059b16bd67ea472fdb56d4632c7d696ba1bd5ab7304d64e81341eac4e6ab97edd051148272a986a028e5a7ad553caa49518b51588695cc25370f8b23e548ed5b518d07b59ac1ce83da37566aa1d1e1ca41c080d695ca49523abcd86ac4d2fdad3da5741fc70b18160ec1f56725fb524c5fb1e1cc6250605f9c0dd059cc80d2728f0e6410062154497b70e5d88e6c55690a875a56b392719cb53c530bb6b39831f1831ebad1527f27e53f324640dad5b5a7b30a22ce47cf41f5ab62cd49fa3768c3c93f5e154381cb4b47cc1f567ea316ada91da57351d632b1f6adad3e7b68e1c7cea42f0cc2a03ed53034b0294363237527ab4b8ffa93d591a4fe04cb4ae49fa7e549293d2edcce1bd630f46056223e739ab57e594814d1ea3ed (by decide +kernel)

private def part623 : Box 0x1300000000000000000000000000000000 0xfecf266be00000000000000000000000000 :=
  splitBox 1 115 0xfecf266be00000000000000000000000000 part625 part624 (by decide +kernel)

private def part621 : Box 0x1300000000000000000000000000000000 0xfecf226be00000000000000000000000000 :=
  splitBox 1 118 0xfecf226be00000000000000000000000000 part623 part622 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part627 : Box 0x1210000000000000000000000000000000 0xfede2b4b0a4200000000000000000000000 :=
  endBox 81 0x1ec761c4283c5257a1b86a1685507da9420b6384ad3507ac82d36419a4ad68f3955ab68f55a6a0cda060168e81d839ad5b927eb4d923ae62d87218e5e90b30598bd7c6811eb0105ab67f75a38304e1262540120f356ce5ee43409c81396c591802faa4ad282a179cba0c16adca1151cce672faac6669e9c4dca6907305c62f64123b0b0ce4a93d397ad362ffa88c0350be2d1ca06b3d906ea39949b20dd68e92b49fca3f526ad1d64f24ac58694159eb70f41c4e3128c051c631681f393e66ada4fe0ef179dab6d42404f9729ce6f5a2ac666adb11e5a6a4fe6b39ccc19682787ce5ff399b70e6340619903a301317b5060b47acf532f1a0b63072845acf0693e2b4f4fe6d5f47aa0764858fb505ac82a8bc2900b12f1c9412ffc1cb923a5ff49fc1cb05897fe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part629 : Box 0x1204000000000000000000000000000000 0xfedf22d9822408000000000000000000000 :=
  endBox 127 0x761a874060ae23d85178c3a52151fc905396a09d06e613315ad8a013bd6841b82963fcad3522f2c0d6aaa31523a8452632d35422b038f8a1c9721b994bf29fd482a4ed277209cc56e22c8be3186077b1601f393f6414a4654721d39cd6d5b48c89b62daa4fc15e7f79caa82951593f5604e18848149aa42bf5a771c4d256a1149ebd8d2d9c7251148cca1169dc9195a6a845206914457ec1de4f7b56d27ed01c4e69d9fe5193392d3df2d3527ed5b7b1c96f7593ead2169ab555a6323e5b457eb10a424ae288a4f63031445acb23e5a9ee4b6a6cf5d93ead3b6aaa464bce9e2c0b4d6711ab1cbd8828392f393f544389a7be69da3e5ab6d219cbb1853df96d60ef0f9cbce9c348d3b6aac6163fcabf543a93f93c2251960aa1d364a325acf1835a2b8ed27ef6338a22d347ced3b9aaaafd6ad9c4e57ea4ae5a9ad34bcf20dddc7b17c631601f3b008e17be58ca09d06ecc0706060a50d07273341ccd4d920a93b6a5c0c1486875d80580e5f20dd072aa238a31410fa72d4deeea1f2f7c1de593832dcb2b4d8ddef7572cac6521b2c6560741ca724ed6327336b3cb3d049ac66518b00a43506ef928670b360def2d35ab66fd4efcc2f5a69bdcdc6a1ab671396520cb389cb29396ce65389ad3527f2d1520ad5b481a841c832e482b536594a02527eb19922ee4939a872d06ec0025e27ca18d5b8e2e5e7550e27399da420936adc733 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part631 : Box 0x1200800000000000000000000000000000 0xfedf624b504090040000000000000000000 :=
  endBox 89 0xec398ca0c2dd06e168317aa8a1d946270341eb55640e9c5c7da813942251751f9e8a2355e37da074a2ea2b51fb886f5901a517521abf0a6523a94169ecc81bee2c0a8451ce83d48ec1b637a97fd07adc2e8711526c83d508cd3b626c5f34099836741c46b0a2e52541ec90b406b0ac3ba5f549eb16e512a03598561b8520bea503925e5ed495b4f60ee940c7932464e2e72f520e8495bd6e40687754722b186b70735a6a42c79334f545690b98aa50348cad04fd3a144406b56e59cb9b5aaa3ed526ac8e61a82fdcdb0aad69ad4fa0f2af35a7b94547ee63a0aa291e37aa4d4bfe6236e13c06598bcd9b1cbd67b3555804f09f2e01cbc80501202c2f8102c315a6d07f83fd1833dfa44d8bf461c75e07d84da91305da4fe399ae89478e168134199e86f5928e5f35a6c947741986018c27cb880bb060bdce46e8e9d63eb4f732ce659cba7d95a7a0357c38bc733409c81d6ada4fe27ca51e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part633 : Box 0x1200400000000000000000000000000000 0xfedf6a49982024008000000000000000000 :=
  endBox 153 0x1d0711cc186b68f6320a227871739993e62ff93e6414b9ad3c2dacb090eb97fce5eca4616524acbd052b4b5a7875d2040cc9135a29a8a07948eb193dfd1833fec1f548e5ff9053072d26a5ff4d1c0489c925651044c0bde8013be3073535416f6d523c1ce62fcd4f584b56c16270279183876eb4f624b17d808c1ce656a7a835ecb460e3072ce476ea6278ae31261f3b126503ca095aaa90d6328dd8fda9c28092398620b158facd580732cd4f51a82e527f356d612ae3596413a83661bb56d27ed6537bb00839903294793beb352c39b25a9a7175a2b98da28872f2ff989569b2c0ce2e3e79404a18c300ab8ca0f9decb4615412c5f41b93e5ab73124def02040f2a09041cc3172eb17e83cb0651a24e340ca0dd6c531acb1bdd6529291f3925e05c93e522f2c0dacac4f601104a103317d56040ccb2f41cb9ae839cc3737b93e4e26e5d8dee93f597b88d4300dc3187198e6ae02c09020ce5a59ba50728195b106ed47948ad61620c935969e803923e70b7013c492c5ef37aac24db6819413a809a1c09356adc5ef40c97be414875e491b56d69e8196adc92337ab685ef03ccb0937a97cd0265a1fb66a7a8cc2e617b8fdb0738c2b59d786d1744d10c401a8c660f875d26a9476adc8d759eb0958b21d741eacf6612b0ec3aeafb491a4fe6adb56e5a7ce4f83cac9c3aeb017bd5c058cb0d6b3c1dd24682941ba3fe5a5a06569f248d5c700dc403cd5b40bae8d42d093f8053185698a09d05a833631cc060b9ae696acc4be6d65612c2b103cbd566aac8db41bc60625fc1ed04eb4d43122f01bd2865f3271c58d482a50d7405cc93f374a4fe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part636 : Box 0x1200110000000000000000000000000000 0xfedf7e490b2982424222200000000000000 :=
  endBox 91 0xda2e8d4310e2204d07ab235368c1a85d44a3c3385a881419ace91f0eba85d47ec0d9eb235f05fb944e3e922305f3377cc3b03db0f45560bf94071812c9b0ec36f235c17ea118c0a4c5246a6c70b5a78f0cbf61d72f9b4ee50e97ed23e1d7351c43f9ac8d63185fb1e1c8dd6af81ad6961cb27ecb4b4902e7019d69e3c3059c4fd581887309fad5f91baa038c0a8755f61d78c1d0796afa375eb72375c9ed610ebb15646eb57d5eee5903a9b893f05986a637481958aaa338c2c5f383cb555abeb2348a23583c36b3d1836069bf4bf68dd981aa1727eb986fd59ab0360e581be8c09f9dace8d7606cc552fdb10b03984fd46eca170ebb53646ba85c8cb075dca2c5550197ce6b0875d8c5a0fc62127ed423880d69ac8e12fd96d60e66f538f875e470a45cbe6dc2b0b4b89c67c51beb1552c728cd5f271b4ae8c2cb358c2ca4759a97ec9c65b50eba8466afb9649c69432f9875dc4591cc37ea7de72f9f9d4161d7136c5fb6b3c07d8be6a6278c23901a70b61e97cda56d45522c5fb508c5f362144523c01f482a4c4e6aa0b05c82c542ea3f6e00cb1c2c7db18791c2d4d62697ee (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part637 : Box 0x1200100000000000000000000000000000 0xfedf6e590b0802400200000000000000000 :=
  endBox 73 0x1c4188b58d41f5e5a68f9505a629315a688e1d060746ac81746babdd24ad5b488a0e65a6a3b65a5a495a0580e8488ca110ddc4fd052a0dd072742c8911969eaf79222d5791aee6d605a3b65a5b40981cd6302a48d28ed4370925981ac5339ab94e27ea06581730f542292558184702bcfe6e5750ba3b49fac0b808e153476ace4e6ad4230ac17e5801f6bd5e839b0f5eb60c13749bbc0f7314d8166e20b63fbb57e416a0cd69ab4330a3f940693f5a68fb527f2d35606015c4714441b9fde83bb56d49b181a0e707772f899e374a0e5eb3059e0e6c557adb0de3028193d1ab659391b6a1746dc8077acc7f7409b14d6848169ad024fdabf2355caa6ab40c9fde69ea3544b3235cfee0af3715c2f0f43fbc1ce6adbdcd81a06b629a35e839b4f51ab20e4b5f077035d1810b1b48669db57d06ed3d (by decide +kernel)

private def part635 : Box 0x1200100000000000000000000000000000 0xfedf6e490b0802400200000000000000000 :=
  splitBox 1 112 0xfedf6e490b0802400200000000000000000 part637 part636 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part638 : Box 0x1200000000000000000000000000000000 0xfedf6f49000000000000000000000000000 :=
  endBox 131 0x5a0626317510fc631a849fab0dc3003ed6d0a06b19969a733411b56e03087156332d34bead5b399ca172fc82b52858103a7259cced3b8232d2d411a0de2fcb56d69ac37483b68d6291185925e92b5f0e67246436ed5f9c82a035a6ac0be2c66054a85d69a6fb58ccc3d501cb4d61e82be5a6ab0b6368503411c8336adc3ed5a6a895eef349dc721dd1f6b90e839ad356c6a14851cc94128197e523328fca06903d8ba2d3565f34f459a7f9a0f6d572daa8e63fc8695283027459ada17e5ca7208dc721c5483ad5646b8b35852e43627a38db86a1a07bbc82305fa0343baac2403ed471cb45390a38e58c9cbd86f34ae0fe82346ba075232da220e031564a0ad35a02c0bea90b80b307f6afb99e589cc0d629856d7c47148671256059816605d83b82b67ac82ce48cac4e059b4f5eb20ad733cb1972a9fe51af2844beab4d471482bec8e32c48a6d69a5f94a0b810698fee83762782ce47182b63fca4bce5ed62e8ac1d0b61bddb45f0dc399b14e48c97d525f07f9ebe11d6afc60d282f770dba46650bb14d6325f562cce4b50ba8e43bb2c65986d163335156aa9072fa9cbc0f33955852a172faa4be69eacbca06b6248e5d9882a1173381e5216941511c050ba4ae392a8e58b307f94721b77adc1e6038a8452565f99c0581abf02055fa7e9515a0e4beb238d282b3f2fad07f5088204d4481c0597ad54ff320e4beb41ed6c58cb6850337dcc2551cc7c583d96bc3bb140e2d7a89567e5f5 (by decide +kernel)

private def part634 : Box 0x1200000000000000000000000000000000 0xfedf6e49000000000000000000000000000 :=
  splitBox 1 116 0xfedf6e49000000000000000000000000000 part638 part635 (by decide +kernel)

private def part632 : Box 0x1200000000000000000000000000000000 0xfedf6a49000000000000000000000000000 :=
  splitBox 1 118 0xfedf6a49000000000000000000000000000 part634 part633 (by decide +kernel)

private def part630 : Box 0x1200000000000000000000000000000000 0xfedf6249000000000000000000000000000 :=
  splitBox 1 119 0xfedf6249000000000000000000000000000 part632 part631 (by decide +kernel)

private def part628 : Box 0x1200000000000000000000000000000000 0xfedf2249000000000000000000000000000 :=
  splitBox 1 122 0xfedf2249000000000000000000000000000 part630 part629 (by decide +kernel)

private def part626 : Box 0x1200000000000000000000000000000000 0xfede2249000000000000000000000000000 :=
  splitBox 1 124 0xfede2249000000000000000000000000000 part628 part627 (by decide +kernel)

private def part620 : Box 0x1200000000000000000000000000000000 0xfece2249000000000000000000000000000 :=
  splitBox 1 128 0xfece2249000000000000000000000000000 part626 part621 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part641 : Box 0x1048000000000000000000000000000000 0xfeea3249209240000000000000000000000 :=
  endBox 77 0x7c1dc7a200761cc527c3f31858c5dd06d0626b2178640ea4bc9fe81d907a819906e83d8e33149c61ae614264019bd4c5273128ab5081d907a4ff8bf6e2328c8368e60fccc0f187ca4e6078c3e50b8c0e837315b56e728b17cfee7353038fcda0670dfb28ec9ff1854978c1506e8396d19027fb99e1be89651f252751d8c1600ed18504eb99d6260a75199845b8670a1657d8f96e6d595a38cfee5e7595c305149c19f8c2c92f18293fd06e839671d86d05f30c15c4522c8c92f6a91d28e6f538fac0a4d9ab63b50e893dcbdac4991c67313009cd640060aa398fb20a31e49bd414f1805cc711a0551b81f9b10f7184967f941e8c04c1a62f83ac91130b9b64602d2391ba2454739cc450e83d2ffb70bc0c0542b206545260d398989641ba065862a01fe6473a064e62e4b83963f39a0398a506695ac4cbfe62f4a0c60b40ec83d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part643 : Box 0x1008000000000000008000000000000000 0xfeee2241209240040000001000040000008 :=
  endBox 85 0x3d0e2368ec350313205906d786adcb4548e9845283358c5f2e6758ccc1147ca4bdf078194065c4ef1869c2ce6a40336dc8192ffa4049fe719480c5ff2018c3505b1cc5dc4a3c9231868c4dd8651bc46082a4ef2e0dea5ed05cd18346eb16ce63251e3f682e4dea71f91ba70b40a9cc526f1c7c82a4f7928edc3e0e61fb6467b94cfb230b398903462ed4348e0e8a93c9fe5f96812831f950127e5925e62f9832a1151f9cc481ae63e0f6b8fda0bb6229cc462ee41928273168163341f503b18527fa0dd032b6356e61482ad89e5f94a097e6711b47607f6c8350e62f02f918293d641ab99e5b0b431cd54768253fda4f525ef01844e4f1fed3d2a015278df672ab90527b2504a3b179c60a7199d8461a8412b201a18db67fb2f698449df41ee526b56dcde7fb77148f09ace3272d471942cc0e83b93fac41812ad6738c93dce5aee368f046162fca41d49e4f528e93d65c106eb1391c61c5479c5f915db99e36da3253d2aff526863433a305 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part645 : Box 0x1008000000000200000000000000000000 0xfeee3241049040000048001008040008040 :=
  endBox 135 0x1e8761b86a081b1055b471169f1cc544e30120db208a17d648c8c5d47aa4f730e6316d4a4e62f305a4be27f982e37060e31746bc7e53fba0de62cb28e2368e0104d40185b40731670fb320e5832c49480b4ce3f48ee4db6e678fef0772f1a39e1be97fc91a81d47ca08e3f99cc462e8c0c4cec37a97b4e632845826c5b46e8185c873dbd412c2f8fdaa1169b9bd5cc7c0e62f6b831a92f2da8c5dea316d5282e0340e41817683740cb13e5ab9fdc0c340014989266c959fb04525e31318bb50e62902f9477ce6f695ac4cc0aa0947ca3be48ec7fd473cb4f27fb70ee39830d398c527201ce515139c64e63100ce16735731945e017305dcff2b556a9a91480673137ac7e92f797cd20317fd783eca064947251c9473d7dcc6d1a05e200284944dd86f060a94194168f541ba4666f18232325aca8371fdb54da6f2324fd25ef17ccc8370d4149d1e73dc4fd2a3b182bdb651d9fa5d880123b0c1523b399c7f6d4d98625e73f4c61641ba024e3230564060abe05ce7b7a5053c65154f144f179da6334dd1f2b459a6f183412a3d4bceec388ca268c8181da0315b9466a5c615a9a837285cd65581c8256b1c1ccdeaa11413c1de05798adb8479c9d9022b07d6267f7412a406118fee7f9581ad54fef2d5da6e8378e5b3db58b250b37ea0ddc4761a85f17830f872651d93fd25e611514c7c749eacb547692f50ac7196d1cdb1f1cc0e93d4a0b280af8c0e7f79bc720c3fb7369c650727e98dfada4616404a4bc9fe8378bf2809 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part646 : Box 0x1008000000000000000000000000000000 0xfeee2241008040200008000000000000000 :=
  endBox 89 0xec24fde86e1c420ac31320db2840d740e626e3dbe58c849cfcad5b497a0de2fac60c9ff185527cd45949f1854a0b56c62eca3887eb8deaa393988c4c8268e1cc58bb41dd06e6c9471b13cbf294151fa85d648c2c83d497b906485b98d40c5d4817cb06e477ad2d866a09473a3e583723bd63f250569ed5b3f5a42e189a475ab6da398e2320d43702f91fd8c15017399d06ac339b84a0c7fb40dc1de3039fad282f6b942ed5b47a9fdcfd681b182c1de62cb4c528280728e8c15c4651781fd9eae6a7c1ed1aa83b303b56d28261d30fc9415b1ab71f5d27a83b405a4bd89f0df5cce6994059845b827a97e6483c61549e5f9a30ae23709c27a6396a0d5076f034cd1c7050541250b6ad9fdd8b308c4152a332d1b4c583ec82a8d4d619c0a96b2cc334719845ab67eb942eb620dd86713bc38b17e562eca368c22f03fb540e620978a128e1474bc720ddab7232456ed656e1ea328f41967117b19cb5a6f30c4bfe7db37a832e2769cc506f1cd5a9a731781dc6e0b4746053d630738c9474a16bc17ce4a3b56cbff30bd26f13dc12e9018bfe30d (by decide +kernel)

private def part644 : Box 0x1008000000000000000000000000000000 0xfeee2241008040000008000000000000000 :=
  splitBox 1 81 0xfeee2241008040000008000000000000000 part646 part645 (by decide +kernel)

private def part642 : Box 0x1008000000000000000000000000000000 0xfeee2241008040000000000000000000000 :=
  splitBox 1 63 0xfeee2241008040000000000000000000000 part644 part643 (by decide +kernel)

private def part640 : Box 0x1008000000000000000000000000000000 0xfeea2241008040000000000000000000000 :=
  splitBox 1 126 0xfeea2241008040000000000000000000000 part642 part641 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part650 : Box 0x1050800000000000000000000000000000 0xfefaf35a72ab92840000000000000000000 :=
  endBox 15 0xe23103f36c1b8731473203507a73130698bdac5abc0c1392a0f6725cf7139893a50473306d9488c5ff25f9c94f7f1cbe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part652 : Box 0x1040880000000000000000000000000000 0xfeebb21871c192864440000000000000000 :=
  endBox 109 0x711b84719c440e2271f7a158741942faa9364928ae53d341e5ab6947839c90161dacd528e8138306b4d274ccc1c9637dae8705893ad2d3e58f2cba6c239456802907035e1d02f682463ecad5d282195944376c1910488fce7b79f65107420eb1c5cbeab4b9ea61d18e2ee83d088355e1f9bdc569a5f5591ac48cd1871f9b0ed2566fb9a7b1873fe874683cac05a7a9198e4ac559ee22a15a6ac8c23d03f3600e672c7c3a25f5396b30b4f8e66f719cd65d3497ce3d0499ccd9c7b8c8137b193a4e6a09391de5f5801e8580cb1739997d4e67249605bb68ba308ce0fcd04702d4dda4e9409c6ed6adcb2b3f1a04c9d2a228ae51fa00741809112f6810e0aec61e01fad5cfc58bc9475ab9bd659abd447c671a56f6b9a463972c9c1cd28f079a30b1877b8c1cdaaf2d2d83a911274c947526ae8da2f8ec1cbde8382c92f2e9a04daae92f9656919409c7052fac19380ee3b50c497d4deeec290981c5e4a08ac4bdada2803b59a92c3b485a504e2f390d216d217b3c3b5508a9357c541233046dc9ea2b38bacadab7357cbeb356da5f39940fe081 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part653 : Box 0x1040800000000000000000000000000000 0xfeebb298708182040000000000000000000 :=
  endBox 51 0x801d871060adc338961c44e3eb4d985e9234fba87dac31805887a1a5b28cce62601650d23316c76ad5b0d6ad0549ad47943aa476ad9c0e6219c51c93a64919cc637ac662c06f7618cf670e8a845472b1583a235969db0c5e86c0c02d5b9a767315a6cd5b5a1ecf06960f2b4327bc60e526b58416ed5b741c46d0e5ac21c46317a80f71988e71130cac264a3bdc5ec6711488c9f75199c4540377cc195a69cc4c0261961119f282e0dad3b37b98bd9837bc7216b29bbe83f93de3889cb5004929c7c5f272d50eca455a6cd5b (by decide +kernel)

private def part651 : Box 0x1040800000000000000000000000000000 0xfeebb218708182040000000000000000000 :=
  splitBox 1 115 0xfeebb218708182040000000000000000000 part653 part652 (by decide +kernel)

private def part649 : Box 0x1040800000000000000000000000000000 0xfeeab218708182040000000000000000000 :=
  splitBox 1 124 0xfeeab218708182040000000000000000000 part651 part650 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part656 : Box 0x1104800000000000000000000000000000 0xfeefa336f0b289240000000000000000000 :=
  endBox 41 0xb23b03fb6618841ab20e55737b99e83c974deea6d1396a46528280b8ba70be64f1d183737a8cce5ae6320cc0be5b05a0ba720549ee93f169ab0ca2f08e2055ab690b9a8e05d272b5367ba91ee6a69f4c9cae6f9ab6d5b8ba6f75616cd5b2e9a054fa70175a9eb4d6619c6add1853fa9f4d41a71f066b60bc0b4e0db2c45caee6d6ad84863819b460f24e5725b12e3df9fd4fa6d5b6adc09172bad34bb6b1b5a0e0741d5eea90b169a4fd9c83ccf77503b56dca60c3737cd5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part657 : Box 0x1004800000000000000000000000000000 0xfefea310d02089240000000000000000000 :=
  endBox 131 0xf83b0e6378305780a06cc356d06b351d8ba7d91699c7e6a3a7d5c42f6ce412ceb9453d283528da0893f8deed615810004eb11e471bdd5caa5ed7aec8e399849fcd612f6a0553c33584e3271f7119c485c941388b554a365256511c28b8ae6737a5047f6a4d399cb4d69a9bb64858ec5caae6f40aa38da2c0cc2f87178e4a9828e649f820cbda7e5949a919940724fd232b4140dc73395527e6f79ab693f9c7ab2b4979c8580561bc4409f2e22e8a4025e51a9c2ce327034b6737a885492721927ed5b385c9f9737b56ce133584e0ae6f044b56d98593cc1550fb9bd486721399c1fe7359c15b8520b6b025dac21c13709c14e16da2e8a2198bad5b5a69c4dac335865a6b99601ac6140dad5b2f39c5ce66e2348dc0fec18b0224196d551d3cf516239c5d8c6c169b348540e71737aa4fdab71c9540e7a2a88a41fe3e98ac5c9219383fcc318c29c94252d2d72f979da9f281c6db1f6569aa075d1686303673dbcdded5b060b12d27ec2d9ac617f9a5a08b5a9ad3649f8e1ce12d555f1985801272c6ce4a70955174731042f3b9561d1b0653c6a336a3b546721c1ece423fb27bb12e0459c849572345c92e6b6b0979d10737cd5b4104932c6dcbed47120c9f33908fedcb3024c1165e7045c08f6adb88de0fed8027cc50d6617c3e9cb1b3849ccd88696ad1e6b0a935ac31f4dab693f988f070545e73349fb20be02ee6ad86cd256725399ab05039282713696cb4d1dca935282d5b43168e1b78e130738346d61 (by decide +kernel)

private def part655 : Box 0x1004800000000000000000000000000000 0xfeeea310d02089240000000000000000000 :=
  splitBox 1 128 0xfeeea310d02089240000000000000000000 part657 part656 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part659 : Box 0x1000820000000000000000000000000000 0xfefee300d044800c1041000000000000000 :=
  endBox 115 0xe43b0dc39840d6d0d57054d81a919515a0b5422623185b28d82cb6281a844e6266140d8bf1bdd8bf208d3ba30e93f27bb124dee1519cdec196adb125b45018038297d5233185960292f5abb55d25f2e8b41c146a7357dac282d6afd187968691d46db555400bcc8e337b97d630724fd69a7ed132a36cdeeda398d83e0ae0c2d44398b9ae7b5963ce2e80d51cae86e99026b53406ca11511457247549ad579026ae1c96397ad4ce62065a0e6b1569e9c1523a17795f6b531859cbcbfecc218ba1c5d54397b55e4099f6683cb975aaeaa1f6683cb57d6562ab5023071295ed69194a0bd467b5c61cd571879026d3d3929cbd80155ca2b48ca04daaf0739283187409a08a1151ca806f70bcc8db1e49f64e62f6b8fb31cc5cc6515c510e62da2d0aa24fc3672d34c46e67969aac1c5e2ff93e4e2f2d3649fb56c9f26f76d1b805ecd2159e98bdc058d97fdacb3d4501a8cf5a6c61e3d0deed6582ee8cf377b54e5a68135746d1a43014519f07f4099c4c173356d69a6f75a6c93f38bb56db4610e0b3584c4662f377ca33523b56ce0ac199ab660137bae8da3307a1c4d68409a888f7966ee6762eb99e1d396d4303020630ee671d3c1b6697b92d69a70590265f58dee7401fc10318791b6d550ba800e8c38304e2ec224fc616d6581826233179bbe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part662 : Box 0x1000c02000000000000000000000000000 0xfefff2605984a4078940601000000000000 :=
  endBox 31 0x6e1805c0e32ca1cb504381ac29f98deec5f5a6ce656b39bdce62b4d9ccad4f398a90e6adb58630f059d27ed5b46eb585c05510c6a3c8ff5a6ace4e62b4b6ada51d7c5a126e7319ab693f591c091398b56d69b2c8dea67316ad9f8d5b6a3cb4f49fb28f61591c141724c615acf183a0f67db927ed5b388b80f71a306b4d39893e5696b4f489a51ce037aac268c3b97c2eeb4f030c1fe13481cd1ba731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part664 : Box 0x1000c00020000000000000000000000000 0xfeeff3265800a5878401480060001000000 :=
  endBox 45 0x300c62e0e41c9ce5af639ac272f317cd615220038ca78a35966ae6f59ea7dce5e7052e1a772884fc7b7ca438c2ca47591a7de729cf6f51ab585742e200510a8d5cc733c7053179ff6382ac9e0e0b9bd202c41c2d14729ce6f317cc5d8b0a7d9524ac8cc2ea4188e3fea7e4e16e539cdef535a5988d3f2be330b03dc64f9a78d4668dd3999c2588440c32e4f9202721693bd4d6471c85c9e8ed9462b236adb9893f6b0d1857b7b9ac9eed47827293549b9c14ffaf71823e0073fe8d94c5ed47 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part666 : Box 0x1000c00200000000000000000000000000 0xfefef2325a01e007801c006001000000000 :=
  endBox 83 0xf42f084721cbee65551acb251cdea93f411b98ac370a49901ad6531793e637da44e0ff18bce62d35510cf71725b4d4dc33594c5e93f396b90c42e8b0208ce672885a9e81d8c5ed5b8e62b4d317a4fd90724ac088359d44316d5ab6b4d510c5b549fac8c2df2924e4ed474019cc66ad985cc5f1c9ce5ae6370aa18bd1c30ba3fe6b39c45a6b24dd5c4f09f2d35011c131480a90ce5e73193f32885545112225ff69bc6f549fb4de37aab073394869014f9cb537b8b4d527f395566a6ed27c9c89e3a0b4d561445809f209b927e7133999cc6591a3fe521b18a21bd5b03c127e6fb93e6b53503cd55503c6fb584b96e83c960d67204d503a81e5a798bd82eb09419c91149fac8d1c5d0db2c002c60269c9d45ed618096d5b49fbd54e4a9138e4ed5b37dc93f69b93e5d06315849fb4be37d93e56a70025a5e6fb5a5ac2558733ca21579c62f5a5b54ce6341e501a93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part667 : Box 0x1000c00000000000000000000000000000 0xfeeef2227a00a0078000000000000000000 :=
  endBox 113 0xc23004036e148620e167195a5c9015a7ad34e6280d4fccb4d631c066188550186d218e6272d690c731317a82e5a6831ce5b2ce662fb584c5e72d6b0cac380bc3989134a3a8261e49cc454f461c94a5b57a8a4fd01ae82405bc370bfe4f96a5cc5f2cdd07f4fcc8d12ffb594fb73d846dee5f5a6aa907f901a6fb8c1a8c4deaa01bed8bf1cc6307359d01ae8398a017fd88f34cd19f07f59a9cc5ea31bee0fe48d9ea707f59a9becbe72c252066127ee83987098196717966a0c5062c0c74fbd07f3df988dedef518e220cb384be0c0370c603160639c64e4ee62f1073943eafb419ad3c1967313d01972d3d02670b839cb23065ad3d64741cce1680d641bc2d1c8734e4deab0959aa80e82d3d4c27c96d66b2a51d202a49732cd65698ad1cfb29479a966f56b2caa310bc20cd5c4a3bd464889cc54633d4d69b185a0e6e5f04bd1874fbb59630a7bf5a6a51d404a15c37db99669aa81da66731503cb2791a2c31398bdc5ec724fc6c6a076b2a0ce4a39bed986410c721c80d38bad3c18ab0973103a0c5409c0cb000d07b7a99c94e13032e0ff251d07ac42d0aa13e6398a0cd07ac00b4e6ada81d46a725903ac03984f9065cb53398b53e409b53e409832d27f1f641964f9 (by decide +kernel)

private def part665 : Box 0x1000c00000000000000000000000000000 0xfeeef2225a00a0078000000000000000000 :=
  splitBox 1 105 0xfeeef2225a00a0078000000000000000000 part667 part666 (by decide +kernel)

private def part663 : Box 0x1000c00000000000000000000000000000 0xfeeef2225800a0078000000000000000000 :=
  splitBox 1 101 0xfeeef2225800a0078000000000000000000 part665 part664 (by decide +kernel)

private def part661 : Box 0x1000c00000000000000000000000000000 0xfeeef2205800a0078000000000000000000 :=
  splitBox 1 109 0xfeeef2205800a0078000000000000000000 part663 part662 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part668 : Box 0x1000800000000000000000000000000000 0xfeeee620500080040000000000000000000 :=
  endBox 65 0x390da141e2868c2c82641d6e19c20abc0c024de38c9c7d8849f946e2929fee00ca494bdad5b4f79c44a37174d27e71593ded5b52694359c62100290a8e562b251e0da92537aad364b1226521398c60e488a91cbdad674f7c6ab508cb01398b53cdea93f28bb80e63602f9185b28b4102ce6293f969ab11927a6d1272af0c22015a5724fdab683b6adc7220093f9016e6f2e99c0d843f5ce6f477c93d1c7c8ef043b14d27eb35987a40b2e9b60ca2c840b28bac7e61aa4bce4e722016524b4f4bdb348e0f293f5d200485c6ed40a97d4a365c290bc242d8471b45492805477ce555849c7d1ced5b927ee67396ca4341d97b683a9c7d84b187690a4fdaab143569a40b550816d218ba6e5147c861d27e7035e0c1b34ed1f2d2b41da8be (by decide +kernel)

private def part660 : Box 0x1000800000000000000000000000000000 0xfeeee220500080040000000000000000000 :=
  splitBox 1 118 0xfeeee220500080040000000000000000000 part668 part661 (by decide +kernel)

private def part658 : Box 0x1000800000000000000000000000000000 0xfeeee200500080040000000000000000000 :=
  splitBox 1 113 0xfeeee200500080040000000000000000000 part660 part659 (by decide +kernel)

private def part654 : Box 0x1000800000000000000000000000000000 0xfeeea200500080040000000000000000000 :=
  splitBox 1 122 0xfeeea200500080040000000000000000000 part658 part655 (by decide +kernel)

private def part648 : Box 0x1000800000000000000000000000000000 0xfeeaa200500080040000000000000000000 :=
  splitBox 1 126 0xfeeaa200500080040000000000000000000 part654 part649 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part671 : Box 0x1010020000000000000000000000000000 0xfefaab02064600480801000000000000000 :=
  endBox 125 0x3d0e6360ae3f0731721d864081ad3d903ab533929cbd69b204d6a6f0260b3d8c46b535a6c7334198f9cd93174ce1283d5a016b13e569a93f57ecb2905db907059a960bf39782ee58cad547cee43f0dc2d040d526c93f5a6a88713392c7f9725a935ab662f9012a1157db92d256afd6a0e5ea23409413929ea6483b56d5f690795fab57928290b1619c9602eb92d23ad01c858472c4d4021cd3fc9becc4a60b9a961a5527b5093f56011334dd67ed65281b08b578182afd2d2c90b8c0bd75ab6d2349ec90b6a1c87e168206a476733ad34e5e8335b0e5ee6582eef554a0a42ce4b3d55cce7f7906f18737d9ccd69a8335f15840b86b683cad35a6e5035a6c7e357dc1e56ae8195a3d0773179864c3318bdf86e1ac206b187135a169b20cd88ac4b49faf8839900e7253d0d3712fdab68138c0c8db6ada34497ee5d969ab2f9edea4f40ea8872f760e4a7e250630f34f527e819a30e83996af34ad5fef734a0a42d8040e9cbd44f293c16b0739ccaa27527b98982086c2c0b475a9a50638ba0dc16f25059c630c460167ac820dc9f3356d2828f59ab65035a6a326468a7ada622b72f3af8d21949ed551efa0dd6864149b2505ab6a4f49fcd2d696ca396adb9065a6b99da43392d47eb3d510f8281a4ae51ca4f5473250564e93d964ece2f8b00f9d06f1cbcfa71c84bceb4d7614232d3549a941389cd5b495cb11589a84528272f51fad07134a0ad360dbb1158962b19caa809 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part674 : Box 0x1004420000000000000000000000000000 0xfeffba519864288c8621000000000000000 :=
  endBox 37 0x6d18c6e09fed5b902e705060a8f4a26de28802f96168396ada09ce12e6580da3e7413ad365f190691cc48148a51f622c46357eacbd0731859192b4d50fac00839cba839561eef394c2f2d615aac1ce721bddd02ed2d600e5f20dd072e499ca6b538c2b51d89ee5d41bcb1958dc1b543ea475a6a88e82d35ab671393dad494f6cd4709acd3b1b2a50d192b4d3f4af8b0354662ead35286c4f1f3a0dd6c40bc60e377b51d48b2d5568b241569ad5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part676 : Box 0x10040a0000000000000000000000000000 0xfefbae599164089c2255000000000000000 :=
  endBox 87 0x6d18c4a1647409eaf02d88e24bc39327fd65ed5b397a465606a4cb4d4f4b56dc820c1a30ab194ffac0a2241e6ad9c5d6333904182907060ca3d58ca41d8832c6589e5f94a0a41d6849fcb4d512c0c15a1f8391445a6b0093f7bac5033f2c614fae0c11dad185625a01d0734614182817060c1c949f8eb67b3bdacbf280741b9cbdd083bce67485b56e51cba04ff6e13ff2cbc18292f513a387d7906e907497cb190dbcd5b40ba89d605216c2fcba090b8792b41497af883996aea399eeaf041b641c9aae7adb0456aebe30072f962a733989e71769dc91972ec1ed69ad618c0af8c03a0b15497cb19483ad560e71bbdab68175abad07208ee8c0c1fdeeeb4d625b175a9341ce30ad5b7acb0b51ab3954fae6e9471d0501c9194f6c6ab8c0b0b5a767e5a30ad5b7817c622c93f596940e30ab5740ba0dd206adcb45404ad366ada90e817e5945abc8e37baad5585a5030cdcb013ebc1dd6868e3355cb010c3821d6c501cb577aea8fca06c2d81727e5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part677 : Box 0x1004020000000000000000000000000000 0xfefbae909064080c0201000000000000000 :=
  endBox 73 0x6d164182a4664039424a26881c4e725b17d68ed5b28ead356a7232540293f2938f9de06717c3f15440ba09cf8618c8e3157ac0d1923b5596c614a02b57163ca31596942ca07351d3b23df8c1a9883737bce4b4fead35262905969a6e3288096adac0e4fea41549ab4d619cc5d479b4de49fa764a0690551100501683fcbf0ca2c0e69ba7f549a2d35a6b4de6a3a38c5a6e556ad86c66adc2d3969a9fd51fa4ee5a6b56d20501683fcb70c816a6589b51d2770794ec942d69b2c4d1e65a9969ae6f9a8ea114f4a8ce5a6855e471b99c392b175a6b28dc2c0b624ecbf32c0520aa4d0c3940d89f2414bf296318b641ce1ada4fd406e531db940d7c3f2b4de49fad5d27f34dd3eb28c5a6f24fcfca5032e9cb57281ac0be2d8c62d03e762cce55053b16672ab1060d8cb2b7b697e51c25f99caac47479974e729b1743168e3 (by decide +kernel)

private def part675 : Box 0x1004020000000000000000000000000000 0xfefbae109064080c0201000000000000000 :=
  splitBox 1 115 0xfefbae109064080c0201000000000000000 part677 part676 (by decide +kernel)

private def part673 : Box 0x1004020000000000000000000000000000 0xfefbaa109064080c0201000000000000000 :=
  splitBox 1 118 0xfefbaa109064080c0201000000000000000 part675 part674 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part680 : Box 0x10004a0000000000000000000000000000 0xfefbea59194420889675000000000000000 :=
  endBox 83 0x631b45409eb13fd687814037dcb4d406a06547a7e239187856306d627a4fd00e8d78e5e82d5a6a4fd65ec37a30ec59406acbd8671c4e0fa6fb49fa38f02f80c19cbeb2f41ca05d744410128134ffd077836a345ab68d19ccb03042d2ac204e7aeb8f565e71372ec46337dbd7565f20256aa7e3f0a23c093f601603a104e809377c38383c819cdd2183a0f2b4503ba2007980de6ef330def2d55eea491830718383db585cbe661b26000acbcdd25d35c110403cd5b2fab0906d9cdf183468bd7c057234500f356e3067405c637bc1ee5aa820d89ec59570ddf1bdd6aa7f741381c65a2b00b458dde827404af87617d61cdad156aac4f8c1c4bf614a01d65f356d4060110404b12e46d93e588a6f704197d457713e475a6f75aacc4f597a34567f1b858b2e39597ae8b03c0c01b268398d55cba6f7404a065027356d852b4d041b97584b461dac60930c59bddcbaf5991a30735a69ba57c43102e8395a6c8d15aab584102b4d8dde9d99ac2169 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part682 : Box 0x1000420020000000000000000000000000 0xfefbeb81984425088421481021001000000 :=
  endBox 51 0x6d1c8781b8284a7b66ad9c14a3e6256adc7052ffa8ce72e9c149eac22d8625481ac262369dcb3f4ffd06958cb9bcd92d3b46dd077614b5451e6b3d59fbdd646d88c4faf0776a89865c8481e037baf8c02c0b42065072d3b8b52d47479942da77461da62d619832d5b50fac0e83ca345ab6a1f5a1ab6e53982a08d49fb088f3a0f6d47698acbc97ee53000c3497b6ae093f23ac09d7b29805edb0635545b143ed5b82528373f3c61548e3e7732c8db16984658b27e7523a98e02c647ced518383069729b9548db05fcba606f8b12c5f135b56d7c5714c413b4de49fb1647ce8f39eda601037a34669db59527e803d965aa81c5012e5d9ab6465235bd5d27ed37 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part683 : Box 0x1000420000000000000000000000000000 0xfefbea811a4420088421000000000000000 :=
  endBox 117 0x15c720e62da3c0941424a267e794165ff05da034e12ba20ce3979666581b97d69ad6537dc72527ab58b63a03e751169b24fc9f2742405c1bdcddf0a951c30730a8b4ee3f3a36d1c2b03969a0b93f6942e30f392c282d2102192fd69a8276adc6ef40bb80b0298e6f9aa2a47614b13d48f3dcc172b4d6b2862e486a4fd67ed516b2b9968c2a434fce07f05ca50aa308a45836c943037c8275a2ca095818d465819f9e0f650b377b78f03f0817413ad862549fad1627ca43646db5947cf358b624fe5a693e47cec119cdee672e9ad341826e1969b390c6368f02d3640c9c5d27e509289b90660db17504693f27aad0fc288b624fd306109f28d19652d215a2a346622c8e15a6aca520a349988ab3f6e1a4302cd68a50b5a6c6f7581a8256aad4308be1fb5252b3f9a9650b594cd5b285c6ef5a6ad366b0e8610dd2b82989424a53eb355521ad559a62d31922e0b9377b4ee404a4151f727d4d8551a8522c1fe8c3b4c520ae4b9a62a33482ca09725ca33733a41510523c16d69881dd3ea6ef836ca47033ad15ac3a1d0374b08e5d46dcafb2ffa38501330551a3073377abee0e705a4b32833482b07e0a19bbd20a81972eba0b038bea6ef624ad14c5e9f5948e0672f9ab093f5b1a86d09f20c18c5eb45920ad3b725c60130ccd31311cafb3df98bcd926e1 (by decide +kernel)

private def part681 : Box 0x1000420000000000000000000000000000 0xfefbea81184420088421000000000000000 :=
  splitBox 1 101 0xfefbea81184420088421000000000000000 part683 part682 (by decide +kernel)

private def part679 : Box 0x1000420000000000000000000000000000 0xfefbea01184420088421000000000000000 :=
  splitBox 1 115 0xfefbea01184420088421000000000000000 part681 part680 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part686 : Box 0x10400a0000000000000000000000000000 0xfefbfe4831c4148a2055000000000000000 :=
  endBox 69 0x368b23a04ff6112c6b1632b2f527c5f56ad9cbcfe720ce513b14e0e6a3d397a7fe5a6863e30e6ef409a93542e5f97017447169a813404cd5b24ca09dab703061bbc1a504ed5f5a681ae6ada7fd026d62f8a21cbda838bbd462fab556306c2505fac666909f9e612a09cbeb1f9e406a39d8aa6fb2fab00d4280b420dd0121d18fdab4d2e9c34d50bb56c3a2981d85f96a9c82705cb165c933d5504e7e308827690c0b77b5c5a98c3c1e41732d55a42b199ab66ef2faa0dd012981d0d41f85f95f11b71fb60e60670aeac4d89e8073911af461c69b0736adad3469b461e0e6d5b7b1a7f651cbd9d107b3c5f57b5ad3562735558b2f677b5ad3640397e589e74148663d9ded6e4b91c6a032faac4d456d55949ad55969aa4d3f15c591ebe8078c2c09f0d7c1e62e9c60cd3ea17a0f2f7393b2a3f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part688 : Box 0x10000a4000000000000000000000000000 0xfeffff48a14c10882057348000000000000 :=
  endBox 73 0x661b45d144397b807255b1a04a0a06641ba8fe625a41e8c3a0658bb356d2824ff48381864a081958b2a2250941945671750147f356c9fe90783cc827620b8082798524ff8fce981d85041de6adb17506ec4162ca40c01d0f639ece5f9627acfd0326f768147f24fd42ec4f40cc1fe7b197e589eb3f627c503989ed01f8c299c965f9403a09d80508c11f59f82e5852837622cd5b51fb0a4fc834cb3f2fcad5cfeea22d0a3f982a2c7614b1760ef0155ab6b3f9852902807e2c4d0328e39ab6d39403a38e6ad8d5e413c1e56266f751fc6c96ada0ddb450148589c7f95aa97e525e9412c01572c552325036abb4e68c3ad54e0a4ff41cae8a41c15a7b20749ff209cb1ed5f00cc9e957e93fd805014441c97e6471a80dab6c299882c298deee659ab68e38c397e545693f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part690 : Box 0x10000a0400000000000000000000000000 0xfefffe4c01e480980075221408000000000 :=
  endBox 91 0xd0368942c8b413fcec497c6fb513a93dac8c2c72f8c197d5232e6ba306b4d51ebd6560741ac4720ef17d53fe9194959bde41cacbce5e5e9949b07b37da39d1c3e3c1b74ffa0dd8a7460c056f7541ca7fd8772465a8ad5f5a1b070127e721902e7f95a6a31185965e08169ea845abea01560f4612ad56033b14dc830165ccf079597bd66696a2090b9c96d55389ad35ccf242d402713601c05f0ff2c3b90726fb4615fb4605472d3d6afa7be69dbd7565f1814623033d6c4daa1151cb4f5abee84606733bd7542212b57e97d6303057d1cf303565e6fb497c0b1697a89d49e4ff6016046bc6c96aaa0dd012882d0d5b82ca8175a6c1de6ad81a4bea90205e49fad14fcb220d5b96325f55a69f8be2706c9403a80e8c2ac65a42d5558ccb137b3cd556b0cc5d471bdadac560e8740dd25e1cbd633238dccec593f2c8e36adb105ccec3782c6a276adba09624bcfcb356d68ac5d9ab67e5471a8fe46aad35ab6a3f9ab6167513a465b45a180514bdde46aa85c15a0af839cb195a6bdddd05aac6fb473974e7ac857cfcb01542b2161 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part691 : Box 0x10000a0000000000000000000000000000 0xfeffee4c414400880055000000000000000 :=
  endBox 71 0x6d081ac6340a813d627fad07e23093f5017c51ea93e30b1fdd0725e992326ab473c02d72fc60c0cad5f83ca84cbf307b9ed680383ca84d066a0230d5b925e80948ca8f549eb4d8fe6b2f4199fe507b2d34bf2b81c163fca04da7b07b90265f98c3b58e81d0821f88d748c9c140cb01d5abf356dac739955fe92f6ada46502741fd8aa11b6afb56d23292f46dcb153f3b56d026b439ae58982acbf2a1340eb9ae72fb02d8aad5f491486517c74162aafd9abe91d4a0a35683dc1e5abe7e7413ad5dd027ccc0b6a9b095283073984a91d9ac73095a7ab15650dd2b4da0da8336afc92b60194580a06d0461e62ca845a8e82741cb58c11968ac5946dc7f75a1c7f7780fc3a102e8e39852b550ae9bdc0532d160f6d5b37bc8392fcad0e3eba38cbf2ca24fd10471c9db526ad35ed70d2e8c380656265f9 (by decide +kernel)

private def part689 : Box 0x10000a0000000000000000000000000000 0xfeffee4c014400880055000000000000000 :=
  splitBox 1 106 0xfeffee4c014400880055000000000000000 part691 part690 (by decide +kernel)

private def part687 : Box 0x10000a0000000000000000000000000000 0xfeffee48014400880055000000000000000 :=
  splitBox 1 110 0xfeffee48014400880055000000000000000 part689 part688 (by decide +kernel)

private def part685 : Box 0x10000a0000000000000000000000000000 0xfefbee48014400880055000000000000000 :=
  splitBox 1 126 0xfefbee48014400880055000000000000000 part687 part686 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part692 : Box 0x1000020000000000000000000000000000 0xfefbee80004400080001000000000000000 :=
  endBox 13 0x5006223176a0e62b410353eb460c0d71873f6949ca1606b8a4e0735a125b1fcca4ea273f9cfc2e840d48bc5274f1a08c25f41fc6a707328aa84417f302cdde50b (by decide +kernel)

private def part684 : Box 0x1000020000000000000000000000000000 0xfefbee00004400080001000000000000000 :=
  splitBox 1 115 0xfefbee00004400080001000000000000000 part692 part685 (by decide +kernel)

private def part678 : Box 0x1000020000000000000000000000000000 0xfefbea00004400080001000000000000000 :=
  splitBox 1 118 0xfefbea00004400080001000000000000000 part684 part679 (by decide +kernel)

private def part672 : Box 0x1000020000000000000000000000000000 0xfefbaa00004400080001000000000000000 :=
  splitBox 1 122 0xfefbaa00004400080001000000000000000 part678 part673 (by decide +kernel)

private def part670 : Box 0x1000020000000000000000000000000000 0xfefaaa00004400080001000000000000000 :=
  splitBox 1 124 0xfefaaa00004400080001000000000000000 part672 part671 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part695 : Box 0x1140080000000000000000000000000000 0xfeebba2a3fc1108a0040000000000000000 :=
  endBox 87 0x164611546e07e6d41c46396ac7e696a93da76e01816488a4d5a8b2d3d20e5fb27faf8d62d3e16597ecc3edc390b413fda8b12cd01aa2951e9bf66ab9c9d5e7355cdfad2b393a44e58c82cd6964ff393c0c35a6bb0be2f090130fa03662dace4c0ae49969ab1f39aad3ce4f031639a9c8883d0b4d601186a1a7abc2bf669098a4c0aaa39b6612c1e60628f05a565ad4007732cfd8ab34ac8c27c7690a44dac5f0187079924ae579652c53928ee6d6b0cc59fc0c5725974d8b324955ee0c56aacc552e9abddac3399cf8e0c5314b58d82180c3520cc25fc6166b192ae0f2e411d3b166255c1e40af3585626d219c82d61589aca630b3165a5ec3d3f9a0f5a7a8c24d64739b455eed3d6b1d07d5aa9f0d5eed62f00c38c226296c1ccf00dd216a010608315403390bc203518409caf7691981565307455440120331551ce71183ccc53099c69f0aea608c1a7e13a9814af7239d1fed5398aad23 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part697 : Box 0x1104080000000000000000000000000000 0xfeefab33a5e308982040000000000000000 :=
  endBox 57 0xb23b03fb5e1b8412c72d27fa0ed445a14931fad8ba5d349f9f1e72084ae0eae535a2974dab63a791eb18149ec6160f2a1b52493fd6c5213cb392dcde7c749ea505145a189f2465cde3a7527a7fe83ac604fd6e6748cc6d160aa8a5ccee55946aa496009eae539cde72d1d3cd47737ad09032893f6e19c6f20f33584f8eb4d062b59e8c2a32569a1c97b7d07972ea804392b4d83cc6295a6b50981b262c4c1e5492dc12de50daca56aaa0150dd079729cb3f7b7b5851060169ace0b4e8c192dd216a1b52496266ad9685cde6c9485c8159eee8c969ab0441869f3485af0a441e683a8d2dc968154859814c3a98200d5b524abf6608c6056ab1819652d4f4f2a86e594bd7502ad4f58c998e4b9cce6c99cde0c3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part699 : Box 0x1100480000000000000000000000000000 0xfeefea333d4922889240000000000000000 :=
  endBox 63 0x1945d1c8201b0082d630bdf359d89ed3327f9cd5104d158046ca2138597bd28ef758bdea49989f1817bab0460e63a9839c02382324a3480b90528ec114099cd649fad072300b4d4a0dfab09986e387406af0ac2ca6489acfe30f0ddd5e73dbe30293f901ac6300bc1cb5653251d203460583f28f527e9a2bce836c60528e2cb491d181724b8e5a83d100480cb4f37ab13ce16e65396cb392f785e6627ad3ce5a9ff8dfab4f7218c7809eac02e872d51169f288630ea497298b4d2034605612e535a7b94e7b1a406302c4f8d46e437379c45cdf12fd46a5d3047af09a2c0935049c1a9611cd395918eb65a7b95630eb298c0c08f6a3ad3dca67624fc72f1cb4f8eb391d3ace6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part700 : Box 0x1100080000000000000000000000000000 0xfeefee22254100880040000000000000000 :=
  endBox 97 0xe435041320da90bc380b2181527b2d3dab6d2349793fd1cf348d7467123b13fdaaea493fecc4527fcd573fead0643007fd729ca49169b0ce60fb9545a72c8dca6d5759aa505645b14059ac9415a5a006f596128e71c1c901695a68901a30e08772ac16d828e589477b92da4607f83c974dca6ba1a8ce2d0a1b524ac893f48ccb4f691c02d9eeb187691b9bd645116849fcc4559ad06b3519fad2332d3c90330b583eb13608b48daae8ef9cdef575a79b25c72a49700bc8c0ce534fcb07d89ee53a303185491a795a566f549fc1ae30b13fdaaeb22187eb925eb4f720c93d8c29fada5692f62cc2996adb94dc72d3d651ac205af093f8e6a90b30e9c7e485a38b21394ec5a7c8e73688a8589b1cd4b5b23bcfc6d236b1c7355a79b256859127e92308a1b94927eb405a8a6473ac7d00af755a7a475eeb2c25a5680541ab9be6959a7d852a2137ab4f57445178491846e0e441da9267aba51da42d3d49acd21729acfdca734f4fd6b3f7abca1b302bd7569e90b5a5c5d3729d07959a974d783a106a8058c0d07549ab92e485cf575e0e3f34ed67eb4b921706b (by decide +kernel)

private def part698 : Box 0x1100080000000000000000000000000000 0xfeefea22254100880040000000000000000 :=
  splitBox 1 118 0xfeefea22254100880040000000000000000 part700 part699 (by decide +kernel)

private def part696 : Box 0x1100080000000000000000000000000000 0xfeefaa22254100880040000000000000000 :=
  splitBox 1 122 0xfeefaa22254100880040000000000000000 part698 part697 (by decide +kernel)

private def part694 : Box 0x1100080000000000000000000000000000 0xfeebaa22254100880040000000000000000 :=
  splitBox 1 126 0xfeebaa22254100880040000000000000000 part696 part695 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part703 : Box 0x1044080000000000000000000000000000 0xfefbbe39b1e898922040000000000000000 :=
  endBox 17 0x328d42d0e061987cc528079072b4d303b6880290c0242d25ec118e2e611614a0a58531ccdc8470e2eb179edeb1983b872505283762c91868c1abfc39272f414b0460eb1f2d8b28072c9ce4f51d974d07272f41bc611 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part705 : Box 0x1004480000000000000000000000000000 0xfefeba7199602898b240000000000000000 :=
  endBox 43 0x601bc581b441cae8a35947a7051fdb180c58e324ff6add1836b1a7e569a3c9385b4ed012d5b8dfaf8290da1bf53ff2d54e0ae4f3908fecfc50dca4340bb12e2c3c60ce4e6f7594b18da2d360628fec9ea9ff3f1ab7205dac33d44e5ab4d800e59302aa05d5fa3fb5aa8fee7c1b8650dfac62d349eb289d85b4605ccad619486ac31663f4c6156aa72f8c0cd5b57e8fecbdea35969a3fb5d1a4630e0a3fb72aca3d399c9ed5aab9560f3201ce4a93f49fca3d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part706 : Box 0x1004080000000000000000000000000000 0xfefeae31816008902040000000000000000 :=
  endBox 117 0x338ba2c0b213a4a0ed67969a82b303b4ccdc23fb5e1a86add1816b3b4ccc3a62949fcd5b062c93f741a86d0a367e2a83fb521ad36503ad0630b27b5a5aa077b0b056393b12dc9ea354839c2c7f682b946ab29521ac8da2903fb48c9fde370a504e2741dc48680b5111c72c64feed5b3fda0ad9440bd07b37bc61504ab4d303a01185902eb45412d07b471c60dedeb2937e9fdd8c4f127ea018fa6afd485a32569a6f740bad16839a054fa7185234cc453e9c1dd1aed498c2bd655fa8c95a6a42ce26b21aae6ad98ad05683b1fdb1806d9caac455a6a4fdeef2d5cdd27d3616ad35946a1d05f0a4aa8187ce3f2d0d3f2b4138fc6295a2c3c95a6af0b229062b732cf7183db0758b670b30ead3641db56d19339660e661d03ea4fdab6807927e61f5f164740c0eb4d9ab69194a0b56e5a6a788c9a30a7e9403ad35a771fa527ed3b969ab6290b0242d2826118fd2829614af11859ac293f5aabd4e6b1c61502ebc370821c463fab584feb2054e226f5982318562ca46568a83783ba46662ca01d60735c72d627a41dab683758cce5337ab93d20eca3e0d42c8517949a61d1fd987d7c74165a6295a0c51738ba4fe5a0b53630ead3527e517591a45107f6a4d969ad5b303cd3b5a6a84648c981d69a7e9927eb4d397cb4d4978fed64401c8497a88e6f9ab707538baf09e293e7209cbc9fe8e24663819b2542ac59737c57d5aa9b25cab2cb60eb1fad683978476720a8a45a64ff5278d7627fb9053d30752c4cd5b58c9685c726c9 (by decide +kernel)

private def part704 : Box 0x1004080000000000000000000000000000 0xfefeaa31816008902040000000000000000 :=
  splitBox 1 118 0xfefeaa31816008902040000000000000000 part706 part705 (by decide +kernel)

private def part702 : Box 0x1004080000000000000000000000000000 0xfefaaa31816008902040000000000000000 :=
  splitBox 1 126 0xfefaaa31816008902040000000000000000 part704 part703 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part708 : Box 0x1000180000000000000000000000000000 0xfefbea600340028003c0000000000000000 :=
  endBox 97 0x1f8761b459083a413508c4fd512ad3dc08c2c93f57b9fe569aa4d8fe6a0183c81d55eec556a04971fb40be15550b93f524662920aaf89a340b4d80ee2672f1b56dc769254a3a8e6415811cc0e9c2c0d61a0f6b353fa93f4feb20551db1fdd38736cd5b62ea054cc736cd5b46b859d1af2d35ab6d2308da2d04036e1806a18c509c0bd0629c64e5a9e1c2e0db251da42809839ad3501320a6307302cfb6e51690ad35ea3031527ed5b927e9255a6b707a2bce3ed8315a9a6fd5f00fb17bce5a82972bd07b3fcc1dd04f1f6cdea829601b8631485f0dfa719586cc1f13682cd28ed5b9cdabe2608278e5a9234a3810e6adc61daceb4d6b3c8ff396c1a569ad5b5a6c80937eab8925136c829413a48e1339f6e5a6a3fd28ec01e8ae1c2d8b3209cdeb316566b41b4ff283938caf0c6244528e5efa0e6d6727fb0a683983162f7821d30488c9236a0dc320cdccb073396b15660580dd69e6fd5a6b68ba3b08331f9981638c93a4e3301fd787009fe0c58e5a8275a6b70d4595e706b4ff9c0c543355c4e6af32fdb38e4f8256b09388a84ce5aa4f97c41bc62b4929cd528e8ff8e22735 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part709 : Box 0x1000080000000000000000000000000000 0xfefaeb20014000800040000000000000000 :=
  endBox 87 0x3e0da0c34626d62509e1c5d7411ed187699c1cd07282d2f7900ce5e8013fe627b164fc65104ed35901ad678c0c9018c3cb4f8c09ff5a9ac1f3f4cba27880100ce5ed398bde83962cc61e251bd4d0727e98e66403501008c3c5ef620a345cd6c4f1e4a0657841cabf65a6a3452224ff8c2c6c9989e90148997bd2840cae87fd65080741cd0264ff9cbf18186c706d27fb995c7b204dcbe901489a6888300913492a0e62f7ad34b6ac4f9ccad67594b8e5843f16ab183966a5ef403a09cdef359e41cb4e4bde9356b3c4f9839bdbd072923594b70d03903017e103ac2d9426f63169900c83a800fcd3c732804e126ad350321cd51d82d651dcfc2b050d9492d5f8fcf07749f9b2569a4035513c62a8fcd3b7239cddab4d0c38d364149bb51cece27882951dcd2b05acd47874a8c562d9bb483b308aa100cff3244507ab571f9b30ce358827a0eaf736ad82dc176819816ac4d9cce6ed2f1c8396abb38ec143651a904ca0ed60ee65039fa630e5e341c9c94e66c339ccaa077b7a074a2f1fa5216413 (by decide +kernel)

private def part707 : Box 0x1000080000000000000000000000000000 0xfefaea20014000800040000000000000000 :=
  splitBox 1 116 0xfefaea20014000800040000000000000000 part709 part708 (by decide +kernel)

private def part701 : Box 0x1000080000000000000000000000000000 0xfefaaa20014000800040000000000000000 :=
  splitBox 1 122 0xfefaaa20014000800040000000000000000 part707 part702 (by decide +kernel)

private def part693 : Box 0x1000000000000000000000000000000000 0xfeeaaa20000000000000000000000000000 :=
  splitBox 4349 128 0xfeeaaa20014000800040000000000000000 part701 part694 (by decide +kernel)

private def part669 : Box 0x1000000000000000000000000000000000 0xfeeaaa00000000000000000000000000000 :=
  splitBox 1 113 0xfeeaaa00000000000000000000000000000 part693 part670 (by decide +kernel)

private def part647 : Box 0x1000000000000000000000000000000000 0xfeeaa200000000000000000000000000000 :=
  splitBox 1 119 0xfeeaa200000000000000000000000000000 part669 part648 (by decide +kernel)

private def part639 : Box 0x1000000000000000000000000000000000 0xfeea2200000000000000000000000000000 :=
  splitBox 1 123 0xfeea2200000000000000000000000000000 part647 part640 (by decide +kernel)

private def part619 : Box 0x1000000000000000000000000000000000 0xfeca2200000000000000000000000000000 :=
  splitBox 1 129 0xfeca2200000000000000000000000000000 part639 part620 (by decide +kernel)

private def part605 : Box 0x1000000000000000000000000000000000 0xfec22200000000000000000000000000000 :=
  splitBox 1 127 0xfec22200000000000000000000000000000 part619 part606 (by decide +kernel)

private def part591 : Box 0x1000000000000000000000000000000000 0xfe422200000000000000000000000000000 :=
  splitBox 1 131 0xfe422200000000000000000000000000000 part605 part592 (by decide +kernel)

private def part549 : Box 0x1000000000000000000000000000000000 0xfe402200000000000000000000000000000 :=
  splitBox 1 125 0xfe402200000000000000000000000000000 part591 part550 (by decide +kernel)

private def part477 : Box 0x1000000000000000000000000000000000 0xfe400200000000000000000000000000000 :=
  splitBox 1 121 0xfe400200000000000000000000000000000 part549 part478 (by decide +kernel)

private def part437 : Box 0x1000000000000000000000000000000000 0xfe000200000000000000000000000000000 :=
  splitBox 1 130 0xfe000200000000000000000000000000000 part477 part438 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part713 : Box 0xa04000000040000000000000000000000 0xff4a98fde2140800220048a000140800000 :=
  endBox 55 0x3a0ec3a8d01500d1501ab67f99052f699a9e827621d0777b6b53d04ea2f92760d3681b46101927a0bcc757356d68aa2f965ed5b51991e64f1012c438e3ad4d49db56e7b6b59d2770bcd7c6d19c64200064a80b19945ec1751ab56d072f6d9252a1b6ada09c37f356d45e7f9967ed5d0eb832d54410d2f01640be3e971cb58543ea33801404807d2c519ab67f9399cd5b518ce3958c9cbdab6d4f9632c517b4b56d203fccb3f6adc8279ab693b69acb456adb68d0320a0031d48f20ddaba829518c8270ebb03d02f075c5e7075d073315d6a2d5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part715 : Box 0xa0c000000000000000000000000000000 0xff4d22f5665478000000000000000000000 :=
  endBox 107 0x1d8671b4641d0179b78c62c1e2ec8725ed20d349fb40f6987d2829839c15d473bddded292b2eab916578b975232f692eca4fd27f358d041b67bba87548e83738d8335dc5c18c61118494cc434a1ae80d392621cb069cb07069c93f069c0d392c5b18c733c18f1d7a4fc0ff1a4519f0732f392f412e0959886c3504ecc3549fa88c22c768398f0d262943839cc3549fc1a63659f4d85eb3f2ecbda59061039229b9ca293f59282bd276b079ed24e32eab16e47db4dcf8a6cb49fa0e5286fa2e0c82f81c96117477014a2c19ab6b19069968e7298b0583ac4d7b4c7c149f9754bab170d4d986ad5b927e941a894304acc5b5517461ac0a56adcc3549f826527f394d86ac4398b6ee3136069b1360e4cbe320b82a0a42301bd04ac09949482665aa829543f3da415e4e3681bc6acc0b940ba0e527f2cfcfef2d55252ce208d0359c9c693f9ed2a0b2cdc6db2f3c0250e5bda4fee8376a7bd864829f4d652d4f271bb8b8338ba24a506ed438fce931583c1b4fa67f78ff334a5252943839c9e32dbbd6cfee837482825604ba88ee356cf8324fd68af6949d825649dcb45 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part717 : Box 0xa04000000000080000000000000000000 0xff4884f5331448000004400101028000502 :=
  endBox 99 0x1f85118c7512066127ed4338da1cae727a83438a2f37b482f437b359c38a7c59c761bd7b4b56d1d31c960da34d57e875cb3a2bb6adbda5041f4ca456b39cac9c6b01cde6a7a0a41a73085cb2b456d19c6a039f0bcc19e0c75f1dc0e1ba01d71ddcf653998eee7b28b365a4c2896b0a3a5a76f656ad9cce607834c59ad5b592c1c96adb59da86d184735c38d71da7e4e367c162d9cac5e6cc35667278aa5a66e3d06386f48f328c60deac0b82e8a02200a17b6c5951538ec5cd7166e34eb52dcd6e53055a8764149b8dc9f1cde50eb08de3e8da1c34e570345a67338da358940325cd70eece4af65461c9df3999285ab65d99ed22f3481eeb1765ace7f9414937e7bab56ce6734ec1a6e476adb30da358fa1c95ac33da5cd6c43696ce611dab8f4b4e7c55978bcdab65d99ed22f36a7cd3f7308725ab6a0359e271b53e522b387020a5ea738f5acea216ae9fa5ed32875edb07b26fb8f61f4ae0d607259c179cf6905d8325cdb3da4f8a0d115fa8767b4be80c9504c91905ecf69503a90dac6707d32824e4a0c9179ac073381a63e9519cf6169f834d667247ded21c5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part719 : Box 0xa04000000000000100000000000000000 0xff4880f72a1c6a0800000088002000040a0 :=
  endBox 111 0x6f1ac631845d14c64037ed03b8f2330fa031d48f2874e421d783dc7c541ba05c5e729143aea33818e93b392c0c7399c93f0eb9c264678b343ae1cf85e60c7791dc6805e61d7495c09936a9c35eef2c95626b3f3fbb0260ee93f819a2f36a1073309d48e0c7386cea0326069a4fde0741a866174064a4ae609a8bdcce721604cc57237c0958fee4e39c9f313520ec1372c8255a8681d4505cd5941ba0e41a20cb500192a31948a839179cc83b06a1c145e6f77847690762da4be2eac1dd86ad598e5eee39563fbacfc1a6e6f86eef690c5b04ce12ee3e87f75aac8f5384c1ecbcf07738d9f1658cc1cd06eac280709814259b8e666e372982960e71b8da05805cf250d04e839540f038dce395229cdc50a5d96116270bcd68aa1d40b9cdcfa711e543aa317bbcd3f49f8bcdeae8176a190361ed22f37abc7f72eca8867ae9fdd86b250e0e66cb4e0fee602d85d958ed07759f979e0f741ee58eac767bbbe0e8308ac0bcce84b0e0a0a59cd64e34f1a91d67ef5996660a550eac4e0ef2cfd27ea4757ec7251e1a58a8138d3bf398546672149fa915ed324651f7354527ea1d7b49c845e729154474127e5e78e0ae6b87864e3699c919692bdb417a721 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part721 : Box 0xa04000000000000000000400000000000 0xff4880f5227449280188000000022000800 :=
  endBox 87 0x7e1d4481ac49f950b0356da0561f06409bf1cac3923e977165f24c4e364df9492d47517c1b65179b943823e989bec81a87053e0cf691799764e66b2f3e0cf570d0809626f822490a705965e2f3069ac0d03b8ce1c6e395a09d072a03207f96a7ce6b1f4a4167bbb53e7b2a8c41a2a478dc60cb4a1277353d6ab07f0489c25827034c2fe485727b40e6b902e0d12d3c0d368165f2d549be7370cecb2f59fbc0c6356db4166b38837981e0c70e3ac00d1981ed4d399b03e068ac7605cb40ee3384df9276f75065a05dd88c2cd473999c6deea0d1518c70904b9c266b0832c04b137c786f752429ccd7c179c7090eb870d607d05e64df243c5af037b9bd61e8e99eba7c157cc4b9474833d606a17076037a6f387522c9395acbe372a925ab60978bb6d5b179ae0b13967e0a5613c8272f39bce2f38bcce56ce350d60bcc19b075c787352deee5e7413c4df2f3b587178972d5b069ad16 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part723 : Box 0xa05000000000000000200000000000000 0xff49a4ffaa974aac4100000411000440000 :=
  endBox 23 0x1846a1dc179a4c6067875dcbb0aedeea4df066ba8be399e49f9c949be1d70e1be8d0228b61c35257311d27f399deeb397630a93f5a4ce4b04eb97478648b8bce5e7856a7217e03531b3418e71349fb206e9943aa47063acce3e9b17c19a2bb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part725 : Box 0xa04000000000200000200000000000000 0xff4899f5e657480c4311000411280405020 :=
  endBox 21 0x641a05801970704392ce30be5048bcce420c969fca45068ac0c2368901cbd50389ad160d281266b3834c1a7286e49d9bde390d00034d443399dee2a07380a38d07294315fcc4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part726 : Box 0xa04000000000000000200000000000000 0xff4890f5a217482c4100000411000400000 :=
  endBox 147 0x1b8542a0d5b68160641f07412c1f4af82b9858ea315238f060e4cde28c65238b1d07229f8dd21a9523af8c22b0e59a0d25796b3829437a0ab497c1d739ba0e60d0a4fd28307257c77148e2cd81a6a1d41b833650ebb893f8e1a6e38f8a2cd7d17c2c185f205d1eac5f50ea8c4bb30b35aaa2f3523ba8de23d67ba813cd520cf166b0be617ca0d064ba0900b366179764e42ce034cbcf317c0a335549630b1d20630deeb00b352772c956aac5158e979e2f3c721497ce55027b99c1a6f756a79ccc59b002f8d007267baa50d40e0d341ca05db43fbc733725cb0f59fb53d6a293f9cce93b503834d63341cdc9671b587834d27efc1b0c634093f6f1a8615cd4f2ecac9437a0c7390ca470df8acd02e72185525d926fca1b390b40b0338ee30766999c3504e839500fb3137c7d20cd8dc67254f2c6df0489f647d27f9047c0d140bb20f75069cd3f390865e8c09f4c1a670962bcf75641a8671600638bcd1ab23e4baaa335a4b0ae69f9c86390c81798121c30668b1df863150751bc49fab0c21166a4366aea83565e90d9f01f4c90d7403671ccd4420af9a0581d00dec008278bb2d33506a4c47d307987820a1517a884bb3031c5671f1475a0bd2eca83418e08f81227b1628a88527f2b0843388cfa0f2c1d1f49765a669f9510ac0f7787d29e50508665a7f280b02a0aa024604aa3163fc9f64112b558e0a0d33fcacbe69fa8be60ebd4d6aada3b814d98b6c1347d834c19b1f649be1c94a1c4df6419c58018e2f3271cb2569fcf61390c0cd81a62c7 (by decide +kernel)

private def part724 : Box 0xa04000000000000000200000000000000 0xff4890f5a217480c4100000411000400000 :=
  splitBox 1 81 0xff4890f5a217480c4100000411000400000 part726 part725 (by decide +kernel)

private def part722 : Box 0xa04000000000000000000000000000000 0xff4880f5221448080100000400000000000 :=
  splitBox 5542 120 0xff4880f5a217480c4100000411000400000 part724 part723 (by decide +kernel)

private def part720 : Box 0xa04000000000000000000000000000000 0xff4880f5221448080100000000000000000 :=
  splitBox 1 46 0xff4880f5221448080100000000000000000 part722 part721 (by decide +kernel)

private def part718 : Box 0xa04000000000000000000000000000000 0xff4880f5221448080000000000000000000 :=
  splitBox 1 68 0xff4880f5221448080000000000000000000 part720 part719 (by decide +kernel)

private def part716 : Box 0xa04000000000000000000000000000000 0xff4880f5221448000000000000000000000 :=
  splitBox 1 79 0xff4880f5221448000000000000000000000 part718 part717 (by decide +kernel)

private def part714 : Box 0xa04000000000000000000000000000000 0xff4800f5221448000000000000000000000 :=
  splitBox 1 123 0xff4800f5221448000000000000000000000 part716 part715 (by decide +kernel)

private def part712 : Box 0xa04000000000000000000000000000000 0xff4800f5221408000000000000000000000 :=
  splitBox 1 90 0xff4800f5221408000000000000000000000 part714 part713 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part729 : Box 0xb00200000000000000000000000000000 0xff4bc05de91405801000000000000000000 :=
  endBox 37 0x6d1cc791846805e6cc2916060a91c192822e8a45165ca3351aa8bc56f34cd466b4d856ea49518aca661da8d437eb4d741986518af2c353f23ed5a6832549328ce271a92411b031dd06607db0754192ba2d365229cdd45ea35611217291d68ae6f387ca33969aa47063ac360b5b9b474eb496adad3418acc340a42bce59ab0ad64ac4d5a686f564b070569b1b967378294e6eb4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part730 : Box 0xa00200000000000000000000000000000 0xff59c055291005001000000000000000000 :=
  endBox 151 0x7e1e0741e40feb40b82783e96a1986d164b356ce2662553169b41e58a2b2f413a4ed286a31904ed4d8c1c9176adacecc2eb3f984f3145ace625661446f0e2ed5b8192d5b98ab2d5417a0c57316c30bc623404c839969ad5b6d1cc5a2cb4d305b0865949cbd69ab4d87d33c8da308fa0bcd88491287718a6c5550eca3138ea91e0dfcc0b04cad24be6b4d39bbb8d02be6737bdb581a81950e9cdcb031f155e6f7761fabe4feeb4d0dfcc27271b96657ca0e569aa1d7acb9ac9c68299f45a1984b188271ad360638fb40fb022569abc310f598e1e6f30d28fb567735955f2e6b626b8f5c7b352dcd6af7380938e58167734ddca20c7414831e414c0c7681bc387cc571f6b56d04e829587c0b32ecac96380ad355c62102e839063c71b6adcc215a6a8cda81f6c819063b946791cc611d86805e6e839b65a6ad54c4ab641de01aace4756b4b39bb154be608d8e1a6fb9c9eb255aa97cda0660c4a0c98e2e94393eeb5130bad3569b1c153c5d010f031d69a6e9382b40b4d591ca0b523ac765e0c324a79a6a4df6a68e343524df9cc60c7387a50e6d969a3ed2fa8685a02eac70f1f6b8f569a7375a6cc43b0c228be5a28fb4e1a7375813f324f48f25e904886a411f0fb41232d34352ca350c22c08c0ade063ad35286099969a0c750fcb4d486a3ee5a6831cb673ddc132b4d522ad16050b05dcaea45741cc6b1885c0c331895bc6a08df356c56a7333898bcc192c218c4671303bcd5b5199ccce26be1c4cc2f2d34e2eb4d981280998aab5530b8bcda86b03823ad8e2e0c55aacb13853eb3f5a6b16e154831d69a2f3 (by decide +kernel)

private def part728 : Box 0xa00200000000000000000000000000000 0xff49c055291005001000000000000000000 :=
  splitBox 1 128 0xff49c055291005001000000000000000000 part730 part729 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part732 : Box 0xa00000800000000000000000000000000 0xff594e55000046800050000040000000000 :=
  endBox 103 0x3f0e81f81fd6a127ee63c8c23402f37bacb4d37f9895263182d666d03e86195a6ca21521abe563ab399486b4f58ecc417a6416a9247daa2194927fd94923ed611e4681cc450c4a5a185ce1a723d761ddb95cb5e47b9eea47b8df6d3b37dc6175a89ca62fa970e6f8fe6b5137dad356a32c64de31cdd7c58ec6df681eeb1f14bd248b807f07301a937deeae63c8c41bee5a8ac6568a3ed58e98956c4f169b17cd60eb5130b9f0658c8bcd5f32d45a8510ca351f69cde2f49bfce372c65cda0b35a68fb5786a1741f6b94e839829cdfe737416a0cdcdf24fd844c12038dae8b4d49fb02e166c1de5a4b955693029e0ef1fdc14eb4d39b937e166a4fda049f9c6e5a4ad35c9e82939bb50da41de11aad25c72b4d419ac760a1c48d839bda53c6c0b5a6ba0e62e0ce1b861906dc94330b8bcd666b51641802eacb4d179acec7d2b3b89c69f58c2e0db033c6d558cb5947d27f906ca03625ca91ded2b5506cae0fa350af790661c5406a209017d569ab139c8eb5514cc7f34810732cfd6330fa4daab51589c0ad37d8fa438a80d969ab195d169b0bcd05a833179cb4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part735 : Box 0xa00000048000000000000000000000000 0xff4edbd5a0100264a280145000009240000 :=
  endBox 57 0x7c2006803faf2368ce310623a0e66255b17c30b968d5d89c6a1f71ecd334f38fa5ab29f9414c60e7b9802dab6a0b9ab68096a174419cd435c06e741fc046f713fca79c7d260d352ca316ad9fe53ce2d185a31a95632d591f48fa641ec9e749d982de4761a006fb68729271d06d485b4fe8368b86271b689a310ba41b6165a9158aad436aea0cd28042cd5b3fea78d3cf073048a78e7b9ad353cea0b9ab64e3597cd5b5198ade0da099a0e6b4d6acbb070f8e3a2b79ee64e36a1b45a1946a1c4e36aea0b507af2350e0d0b56cc460d73fec4e36a1c3b92d698958a60d7271cd59729cc47404b56c9be5e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part737 : Box 0xa00000040040000000000000000000000 0xff4eda5d80900224a20014a000148008008 :=
  endBox 83 0x400f83a0b807f5e4501886d1cc5d0c1a62583fc0596b08fa5a863e99c768020665979fe58ab0fa51ae2d16aec3e92fab5767af8d3d6a23e96219c597cb3b58798bd3cf41fcdca91f9ab66e59cb291f597b03c7d2be278ce461e506b57503283930bae8d42808037abcf7758cb56da86d5ba0f338ed81e3670c1c4bd5aab95c6bf350dab6e57409c7d96a79c15876d5b681404f1032d420dde4523c5d5179b575ab7175548ee6f981ed5b9d8791ecb356d81e2f37b2d079523b03decb209dab66e5607cb075998bcdb4761a87413406b9f08136aec8195a4a4f5693292581f34fd282d03575ab720dd0326cb906f41dd81e81906baf8a359ab6a1b414875d06e7059ace5f561da982d189bed5b9052b3b7c1d0791ab73085cdec5171d8245a861d706fa000d16a3c3c17b9ac6548aba16b66a3a8d4596f5f409a7e67afa78dcdef2075e6aea91e06bc1d7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part739 : Box 0xa00000040000001000000000000000000 0xff4eca5d80826a20a0001c804000800a000 :=
  endBox 129 0xf0400ec3e0c407f54c610dff1cddab6e6f4f09be8fb9a7ef5b607938cfee4e3981ed3f90666a9969aa4747da4c5a7eda3a0e63480d758cce532d7a5041a25e9905b2505ab6d5ba0eee6f607a0dd066837961eb4d6ad937db4791c46a03aec42386605a4a53eeb4d419a0f53ef303e58ca8c5416d5b64188271a47e1a7c1fcc5e6e5055b56e4f1a7de4a186dd48f138dab6b518fdab4d6ada20bc208d5b7109c682d9ab2a473e386fd69a0d1416c93d394a8c60289fb569aca394e41e938c346b4d729c11b605826ce6e0df6518467036f278c5e61c74f3c09f737a0f49c64e39c732c65cde09f04b938da4450e44d0b5eca3108239066c23c89e3969a2f383ecb4d486a00c19f287d69ac4241e503a4f4e1b3dd419e2f38e360cf42188301a87abbdd594411c82d483ca0749eac66729b50ca208e416a81e49e9ff419ee6f96929df8c29c3d48e4a99c8a7f3519bd5deeab6268ca2f8c20bce0db871e0ff2c9507b07d5199f06004ac940229430c99b94fe63c7927a7379a04efc1a658c833d8572c660ee2a09567bab50e2241e067a835492e63d5cc172c0c5e6b0396331894c03905412ac25b651e461134460dff353d63a60b5a6ad4563b17cd69a60b5a6c62f416cb1d5a6ce39961f06949ebd5e651a84d104720ccfaf2d3540e57f416937e5a6ac74fe690793be93d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part740 : Box 0xa00000040000000000000000000000000 0xff4eca5580804220b000140000008000000 :=
  endBox 57 0xf824fe007413c0fe9c8f22d3590680e0a025960681341ea02568b3085a7720e56526234198fa66809c7185ce0a82d1f4b086382b103e95d0c4727960e6b2f6ada0cda8682d736c7f97b0a034b673084ff2a0b6ad938da0731e44019040ca91e15bb56c5e690589730736ae869e0e7356cdfe2f341c875da772d35eb68e9523a4c505b2d35ab61d785e6b4d741e47111006fb56e0ebad3501b3db497a0970ebbb0d00f061799cdc9c7308569a2f3690c08d271aca65a2c1fd46a2cb2719cdd69b071c9c61d7741cc6f1d86901aeb459ca671b2719cddee738e5a6ad6141c9bfd842d5b69ac823404ac0d05a1d7305c62376105a0ab8236a356ad9cdd2821bb903283340cc833 (by decide +kernel)

private def part738 : Box 0xa00000040000000000000000000000000 0xff4eca5580804220a000140000008000000 :=
  splitBox 1 72 0xff4eca5580804220a000140000008000000 part740 part739 (by decide +kernel)

private def part736 : Box 0xa00000040000000000000000000000000 0xff4eca5580800220a000140000008000000 :=
  splitBox 1 90 0xff4eca5580800220a000140000008000000 part738 part737 (by decide +kernel)

private def part734 : Box 0xa00000040000000000000000000000000 0xff4eca5580000220a000140000008000000 :=
  splitBox 1 99 0xff4eca5580000220a000140000008000000 part736 part735 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part742 : Box 0xa40000002000000000000000000000000 0xff4be677b48000110528000520000001000 :=
  endBox 43 0xde3a0e6338b8033564b2cec1b661906dc4e38c1a0db641c7b356e0f25d562d83157435107a4df9c82c5b839a04deef137dcaed250cbb575c82b4d95e2c42680c526fcc2b41ec1b41162b362da01e6b292e569aa338112c5b063ba0c82e0af993eac2f38987447d29e24f67a99c4da4b356d4124e3730e440169ac198972a09728c8011048b89bf07760cb56c112d4b4fab10c5f040c4b930cad466adb90585eb259a4a08b5a6c4df62169a4b998b683d692c4b9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part744 : Box 0xa01000002000000000000000000000000 0xff5c467f8c8140314028400500800001000 :=
  endBox 53 0xe824fdec6513c391e45a6ac09a186641eb99c13a5af599a0b630ca0b6067a3e65a79b7c19a84310fa350b020754872834c32b07599a08e7abad3e5a49b7deea619819f3d5deead41a80cd57cd07f72ea0f500707f89bf07d41eb975cbb2ce446e6df79019efa23a4c32f653999fce5a8b98e4efa41e698b4d5eca6df6a07db137d6668f5066b10a1d851a9df483acce6a5a77d48066968e720b99c7dab3347aa0f5eef23d51f6d31411be8d42b0f75a0f6a47731a00d8b60c76a88fb588586c4b92eaad3d07ac5b969e882784df6a8c47b5a6b98e7b6ad26698bddc1428e9159ce472d1ad3c18eb23 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part745 : Box 0xa00000002000000000000000000000000 0xff4c5675840000110028000500000001000 :=
  endBox 151 0x801f05a03fa903e893f56169b3dc418eb396a5b5947da9a3788c2d36063938d66a70126fcb35062a0cdab31f654128179072f6183dad350530315a84f1885707da881fdcf9b132d646b4d61acb23271b16e40eab8b398fee2cd35169ae479eb6b3362dbd76626c5d56adac8c18eae09763e292260e64875919fdc59ae6d89c6b237b2ad3560601206210328295e09beb518f8af7562dac8ce1ef5b374cf239ae4f8bd65ebac35599b9ae4f09c3a11c3b106e4b9969244137d666d318baaf5b6a8cc5b5919c3c97317540a7013d1860c725ca0dc18f350c9bed5b93426fa3ee83fbd6cbaa0c7409bda6694a3ed90062c0c7731aa3201dacaf53900f0735a18c511a849faf0d03a0da3988079ab61cd06a83161f6b066168ac3d69a4df6ad873459b357506ed335a683147da907a0fad5b3fbaccc1ab3e8d2035e166938d693035d69af659ab6b4d561786f07dad00b4669b87341a24ad81aa71392321cd271cd4b6b28355cc5f1f47a9c4df497938dd006bc1cd5a6c829258bda62ec834503b031525eb4d6a1787d07da90b903a4e3068c1cd06acf6da0f6f6906b938d69ada398b0035d69320649be0c79abb1ba4e660c526fcb4310e8398f23b8bc138c1aa0df583c1d52eaac1e7b4b4093f91cef6949e8fb419ac629093f1f6cb4f3fea07459b3dd544280d81a3075501b24fd05ab4d1f6831e6ada0b47da93f519cd5b271a4fc1bece328f23986c031c1beaa350deb7349548a9f1811b34a4e1e3c735018ab20b2e7adb5758b7073609bdd64099c3e068c0c5068cb4f83aa0d1 (by decide +kernel)

private def part743 : Box 0xa00000002000000000000000000000000 0xff4c4675840000110028000500000001000 :=
  splitBox 1 120 0xff4c4675840000110028000500000001000 part745 part744 (by decide +kernel)

private def part741 : Box 0xa00000000000000000000000000000000 0xff484255840000000000000000000000000 :=
  splitBox 4753 126 0xff484675840000110028000500000001000 part743 part742 (by decide +kernel)

private def part733 : Box 0xa00000000000000000000000000000000 0xff484255800000000000000000000000000 :=
  splitBox 1 102 0xff484255800000000000000000000000000 part741 part734 (by decide +kernel)

private def part731 : Box 0xa00000000000000000000000000000000 0xff484255000000000000000000000000000 :=
  splitBox 1 107 0xff484255000000000000000000000000000 part733 part732 (by decide +kernel)

private def part727 : Box 0xa00000000000000000000000000000000 0xff484055000000000000000000000000000 :=
  splitBox 1 117 0xff484055000000000000000000000000000 part731 part728 (by decide +kernel)

private def part711 : Box 0xa00000000000000000000000000000000 0xff480055000000000000000000000000000 :=
  splitBox 1 122 0xff480055000000000000000000000000000 part727 part712 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part749 : Box 0x864000000000000000000000000000000 0xff792c6334fac8000000000000000000000 :=
  endBox 61 0x671906a1cc6505e6d6073e05da4567b4a4a416ad6288de1c956af179dac6e638bcef614b167f1c849629214f1cbb293cd96d533979b2e500b51c36316a5d05c1504e07d29279aaa1b5499937c17f2cb5cda7332c9d07941cbda49be0bf73082d418b20a4baaa013979ccc9d72515205e0e420a989d60b37b4c91541c93ae0e79ccd50481ec15d873e4a2a0a6275b51e15f86ec396e63d89159652f692f3937c39ec5f9ed21cb48ac4ab839ad349be9c37891f815a2c10538b1d645809d60a9a0ea7331dacf61154cf71399bd8bc1ccd3c8c2cf6158cb56c9d6721480f833d45ab6b555abc2bf607cb577318e866ada8a49d63e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part751 : Box 0x844800000000000000000000000000000 0xff632572b499cb240000000000000000000 :=
  endBox 55 0x1ec80160641741f4cb4d1799c94e66d81c5c1870fa5acb35549eef516adae8c23287e0fcd2c5a1ad5d8733d8c1227d94a2b95e7b89f6519e0cd8576f01c25a8f358528a2bb8daa0a7466ad0d48f2d0ce133a8c22e8de258f02082c11f9a4cd68735545e739449eec81c8660bb584bce2f3151c7cb5a1979c19aa4558acb4d7b483347e6a1d94662f35e10483acd2d596979c19aa1d523b5549ef3da5206d5b7b8c0cd154cb437b4ad3574179c721481ce6d0649b2da864018b03247e7249d676b5115d833548f2d4569a1bb611901f9c92b1798336728b95c7e60a7050c4f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part753 : Box 0x844004000000000000000000000000000 0xff6b2d6230dea8809088008000000000000 :=
  endBox 21 0x2a09e1f5e2efa87c78e4f527fbc0de1425d4628b8f62efb09cff29215ab8fcc9bf309d1bf38f568a4df6aeb80d60bcd27b28cd6ae725050ca337b4c5df551c9f0eac906e610d582cc3763f3641cc40bc2f3727c0bb59f872e722acfded2915 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part754 : Box 0x844000000000000000000000000000000 0xff632c66309888000000000000000000000 :=
  endBox 139 0x781cc5d0a3a5276516448fcd437b4b495676b510e58fcd9859dcf69069a47d28ae579aba0d37b1c8f398da8e9457b8c8f541ba50e069aa0b2278ba13fd9066200741ac493c3e94a29cbcdf70fcd4523e90cfc9214a2b0261f9bda545293d48162b1fe47e683946ac3f3607ac55c8f398da8ee516aaa5147e6c82d3658e8fa51e320dd905c1cc3240dcdac3f7b4a4f47e63e975127ad5b925ef6905ea4847e67cb942a7335d128b351dac23f3478caf15abb78ba2709603161f4a4cd28b00320b40fa49bf249dcc6f69817eb436a3cc0941cb5749bec841e66aabda43920c522124f073876b0797bbb576723c00d5d731cf695009cbd6673da418afe0626736bd4dc7af695979fe50523e996af1c5dc07f2004f09bf2d347e683741cb20d630761f9831527ae6b93b2c4d1f98725052af187e67d39a4ad5b7b4ad3522a0c559dc37b37d8314392c23203f337dcf7773182fd1e33575ed33a8ca2c8a80fcdac4f16027a8f1e5a8ac5e7b2bda55f2c2f1e3a3ee50e833d686f6989eab4d9ed2e6250c235890d8e0ab0148f874c16b0bcd23ed62be6067bda562eb4d9ed248394160b50e9a70b159aba0bd26fbda6735b9b4e66d5d5e1645809ead60284fc392cb576a9cf695959c95ca33da5caed4794662f35189f8d61686722ad5da8e70558bb30e479cc6b3337db9458bef6960bcd4362fb945903705e6d5d9caef6950e979d466a1d9ed2d43392b51e6ae81a6473b8ed85e6fb736b08d42f02f326fc1c504dcb495a8ad461e39c856aa9e3a0e51969a7216aecaf91cfac9432e4f523cc733 (by decide +kernel)

private def part752 : Box 0x844000000000000000000000000000000 0xff632c62309888000000000000000000000 :=
  splitBox 1 110 0xff632c62309888000000000000000000000 part754 part753 (by decide +kernel)

private def part750 : Box 0x844000000000000000000000000000000 0xff632462309888000000000000000000000 :=
  splitBox 1 119 0xff632462309888000000000000000000000 part752 part751 (by decide +kernel)

private def part748 : Box 0x844000000000000000000000000000000 0xff612462309888000000000000000000000 :=
  splitBox 1 125 0xff612462309888000000000000000000000 part750 part749 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part757 : Box 0x840280000000000000000000000000000 0xff21e96319c054621540000000000000000 :=
  endBox 111 0x200821746b1984f0e66b3b8e26dc052648e937d84ac3d3e683149bf278741d870527fcd535a6aced6a2d5b9666e6126fa4f528581cd5b168ad349ea5f54a0cd6326fad35b85c1401f4c93d2fabb094137cc8581c7dd62ab8f683eb10cf96e633e5cd499cda7cb3eebd5565eb3b5018b71f2cf9aa156948a5e26f91bc15339acf96c5b26fad15e05c128600beae6b87c22953e6a0e5012b29980241c0b3727ac4c7d2a0196264df5a6b489c248801f8b5562ac17303e937d8a739b48cb2ce49beb298f9741f56aae6b500cb4d60ecb4d055acccbeab817d65a2a0247d2b335f1984f0df6a01961ad5b403ad3418b39ad6072bc4f9b2cbde0541706e07d2cc350e6d98aa0c50e0938661eac9521eb51613cc3f6ad82ce6ad82a5385d1a4570fc4a2b56e8c1ad35a863ab26fa78e519ab69075a6b50e69cc4df48782165a6a80b4f9ab6c217b78235012af1984f30fdcd69e330b4d6e107334e56760c526fc8279ab6cc12ce05d831540401aa73095ac68290ddcd5ba30a3ab26fb30d42d36062937e5a6ad360ddad449bee0370b3f83820c5621c0b55a693fc597356c1764ff (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part759 : Box 0x840090000000000000000000000000000 0xff60ee4210ca12430849200000000000000 :=
  endBox 107 0x1f46a1945a198419a0f6005e0e5ec22b815d9c8af69056ac6673182d58b73dc49664ff7b4998b1d514c7c169cb93e3e0a506723b5247e60b126fcd6348ea505143d1c4409b49002c8b3b9282e67168937c7e694399e26f97d5686c21cbe59dabdc17eaf79ca2f6927acb3b159b5747e672f9ab24df5a4cc0b15681bc0e700320cc2b0941c84e6607d9602e514a0bda584a0bf9216e514a08fce26f9f0e2241c7e7395d23b34b44d6b3b839c8cd72b937c7e68f19c76b2d26fa43e01d92dd6762cb6ae8fce004f0e8397b887055a8c01100b8fcd62ac43736ad4648381a562a3f39ca24df48ecb3b4a08fcc59730adcda3f36b198511803849c949eb2d5deef392dcc6f69578937c9eab23209e284e4a093ace5eb17981ae614a0b49627fad5cffb3da60f24695a1b154f8483cb572efc4ff3fed00358b61ccd1459da505cc7177cafed5586ce91d69cacee650fcf3da415a9155148fcd4531bec9ea90f87e6e8358a213ae5ab9c24e66c832872f05ec0bf606c91596aec25571506aac0a9499a50a15945291571d9bec1672c2569e943707cd98aa6fb84ab1b2c9bee45723a5806f928a0bf924e0bb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part761 : Box 0x8c0080000000000000000000000000000 0xff32e2565fc050460040000000000000000 :=
  endBox 19 0x2085d1541f9cd39399ad3438aaf1419a0f5a4578a07522b28055eeb23062ad363a15e2a2170b1d4a169ac4da3060c1406830657bce455a78314df6bc0316406ad343a25d5060cb4d61ed183481ad0c3a20c558e8316 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part763 : Box 0x840080040000000000000000000000000 0xff3aea5210c03246a040128010008000000 :=
  endBox 81 0x104328ba350b4239e09191947e63e949ead3506683d691c46707e694204c9be2898bea6e9981f24f58b670545140409a4be6ae977da7e9e209e7afac0d3ceb15374bd7e581a8092f8ff2941581cb577aaac65ebeb079026f7348ec1e581eb151f493fd682e22503f35009ea093925e705168a476382c2d1093b58d3fe7f94a0a4752083cc91d3829fe581731551ce91d5e14027fa00903607f964105341cd6aa9415818fa5a7330fdac6af1597ac766b0b9b66ada3d562ae5195e22d1468b0951ead2158acd5b6a3b5855e2e82bc4d9704c60da2d15a6cd61f080300f82d8d42505a8f1755ac2d5326fa4756aed619cc23a748eb03c9ea9e0216736a0dc12690727a8fa6483937d656b2b92824739282b57927ad21906e4ff04ac7fd7616c4017448ea4bd04f2cb5a723eb578cba3487e0facbbf41e5072b4326ab09d27b41f6366ac7527ad5b984683749eabc563ae6d95e24df2fab56d032ba2d461f5b56e62a824d5e2b1d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part764 : Box 0x840080000000000000000000000000000 0xff28e25214c010420040000000000000000 :=
  endBox 89 0x1ac650a46b4410b4d3a0bab2ccc77a80d27fa07560f06f56664ff41e9b362cc8ef411280927086b6085e1504a20027ab209dd96767254a2c8132fa977dc82f699ab6b3b72083156771c4c9fe90798b6d5b7b4ba10023f657ba04c7d25f5062cf6996760c54a0c809062b21042f8f6f962e5d54a09c94e5ef0251627f8fa5283175528b0fa40232cb49befa328d422880d5d1b8419bc09e2c8b4d578c6d548aac3547a9159402f69961a90f1f4abc65a6ad3657bad3d185a4caf7578a80547ace2d36403abc564735cb295a7c1cd6469039b86c026f41e53baf69514ad347d21c571ecc1327fa80569a5d596aa7f9404bc0bc2404ff41cc6fb727ac4d6aaa298df6aa2e81ab9ac6f69514ad347e63e98daaa2961eabc600b9f2ded25f5514ad347e72d3544f31549ea7fd641504007d307395e6f6950aac6569f34ed42aa4f4a2b70bc350ec1bee58c87456ab2d36579a40d63e7f95149f3650a9becff32d3cdf67c2454f9b12cd8aa6fb85264eb (by decide +kernel)

private def part762 : Box 0x840080000000000000000000000000000 0xff28e25210c010420040000000000000000 :=
  splitBox 1 102 0xff28e25210c010420040000000000000000 part764 part763 (by decide +kernel)

private def part760 : Box 0x840080000000000000000000000000000 0xff20e25210c010420040000000000000000 :=
  splitBox 1 127 0xff20e25210c010420040000000000000000 part762 part761 (by decide +kernel)

private def part758 : Box 0x840080000000000000000000000000000 0xff20e24210c010420040000000000000000 :=
  splitBox 1 112 0xff20e24210c010420040000000000000000 part760 part759 (by decide +kernel)

private def part756 : Box 0x840080000000000000000000000000000 0xff20e04210c010420040000000000000000 :=
  splitBox 1 117 0xff20e04210c010420040000000000000000 part758 part757 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part766 : Box 0x840000020000000000000000000000000 0xff3865c2108001014800042000001000000 :=
  endBox 149 0x1b862170560c4b183584770c5ee03582f396ae0d5291b57636a83645e6b22f0f83e84eb384ca4550eb146697b4fdac67c1b2e57cb56d6566d5493ca4f7b4c6d1607a7ace12f035766a9b025a873d64daad53291d043b8bc2f851d6b0b055180518b98e3feb575c760cf5a1a8ce692abe5ed24f511cce6383fa82419e4f59ed25df0678d7e5a8b49472e4df6ae9ff51eb27d419ec2f9cc65a37b4833ca4ec8033562f24654673dc49beaf381b6f83e904348f61474a4ef69965662306dc60e0bfb91cc46f7183ebda4a46aa2f06235abd07940cb0eca269e170140736ca3b47aa0dc00b0bcd04e12f984ee4f595c1d4df6f7189be2f3291ba80d58c4652306db08bc188d3c4f0b95e83ab56c9c2a4598768199a92185811aea358c8148d586f0e42d2f9c8e921731c3bd628cd49392988d38596ad5e6aa937c9d72d5cb5327b6628b524c46cc2d56580bdbc246d4749c93b4e4a523311c0d77c208771a4780a3b036ca4ecc358ea2785235e019f2be49eae47819f1bed61e7218e4aafd84925857b49bed6a24f58c2eaf9587a0de27a948cc2eea3205234809ee7257add07d13ba7dcf82f69623d07d519b94672ba8cd686a4538bc721579c185522948c1b69e148d5f3035cc2e0d796aef8278fa3084f5750bff148d602ffa09e167a05e6acb56c9c280982861a11f49385ac275b5262ff9b6ca467212cec5a97d1e0500a12d259412f69502a4ad986b2c927504b98ca460a791e2a09731b80cc17545e6e619ed292b80aa04d23ca587259416a477b8d07d37d9ff5656f696b16057ec7cb5ab814ded26fb2919c956ab3db4d3ad5b57eb524a466fb85e65a966119b305c6ee945257bda4e427252919f2e6aeacace0a5ff (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part768 : Box 0x840001000000000000000000000000000 0xff3262c21280c2200108000200000000000 :=
  endBox 65 0x410fe380d6330dc148de0690a3b036cc1a5274f8d07741ca46453af695a6b4c65a59c2561e6195a69cce7b4ad34a12f03e0dc183628e949d41720b4bfed5b1f994249db0fccbbf3c0dc320819905ab4d179949d8847dc82d28ec0db1f9c5094d1ed30bcd6927f3411bda62efad359c7b4c619311be04659ca2833500a0b520a50928ea89e411b48f03e0e2149d401f9b0765a893dd612d5b59abd465a6b52ce2ed5b5849c5e399c80341e8fcd69b3da47e6f8228ee250ba13d500741f5286b4d4119c5e7b6ad3544e9299eb2d617b4ad3561a51359c9c5e5a59f266b09ccdab6b4d2899c966107d7188cbfe5234f0e0270ad341b72025ab6b1f6adcdc24ce7b8836cc3290f9aca809 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part770 : Box 0x840000000400000000000000000000000 0xff2060cf128000020084200010800000008 :=
  endBox 115 0x3f8d63a8e0330f6148d3c74169b00183657b8fa4a4e619293c2cb06dace62efbda4a4ece4000cb599c733368c5273ecc25d38b98347d252769106720f4a4e0d587d3003a0c22d894188d28327ad8aa0d741e9835f07b0a4ed6187d20db419c6d54f3c69f6a18fccff3208c1ae60d168c01300e8fa4a4e6195d1845a0c5271f9977e293a4164f3acad69a1db293bc01db8a4eb4d8bbe5db1f9c00e8308ac188d90312bd872f817e733411c6db595c8138e12f03da61db8f1cc32a2949e949d0671865f44ffc5f3293a04d046b418be60bf1f9c527621d05c0c331896087b142b00ac2e60356299f345e67332939c1584293b9b6629988c5e68e39a5ea4f6101932065a92623064cb4d7019851ecb4d179831dcc31a7cbe6b4d293826e3f3b98d286a3b293ba0617969a0c92939c4c5e72d3418efa320e0149ded30fa569a2f37b4c619411b10f69966681d411acce48aa50d21e3f306db38b8247e30698bd505715e73da569a6fb311a4cc1b32024c468eb482c915034988c9be6fb06ccf693069bee087817c7c1d4293b8072f8df63e906d9cbe4119cce6919c6a5c5df39982fc3a66e99026721397ca0195eeb4d06d949dd057bc1d33929ccc18f031e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part772 : Box 0x840000000000100000000000000000000 0xff2060c39aa400000008020000420001080 :=
  endBox 61 0x3f8e03a904148da8761b8179944e31194747e71425aab20f564a5df4a1876ca3ab1989ea51d30b833e1f5876dd8820c4b1c14e422f36e1a86adc625063b5965a6b02da5e60b3129b3605db56c37f0440052737bc71331786ce311d003a0dc3e062369190397c4eb05fb56e71dad5ca3ab57920a4eb05fc7255b13c1d3c7e71e382c437e5ff710fbb39ad6525096ada82c1766d50e7816602f82edf04f1902759cbe05d8fce3f9b56cd3b0fcded2b5705d82ee384be09202ec9d6509482c4ad2f99b6e058a04e750a1251d836c0bb40982ee505abf5bc700ddb34c4e660c106482fe2d5d0756159f2d466e6b7b6949d43a0bd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part773 : Box 0x840000000000000000000000000000000 0xff2060c3128400100000000000000000000 :=
  endBox 127 0xfa1cc6087c1dc541fc28e9425c0482985c28700ad3c2b4d5ab948d68727860da5a981b6b154829cbc7d2ac1474d44b1ec597ad15985a6c7331f9c52387e6c8350d60bcc1771c85ab6c17816a47b9c8e6fb5899c85c9ee6b291cb131f9b20b399a623f33e5ac4ce0ab4d179ac4e404948c7e63f39fc61169b0bcca46d2370c82c04f7411c9f55a6a0cc7d20c7592a3e66adb94569ab028c63eca82d64ab516a5cb4d4f07d3137d69a8239a627d91f4ad36690e2f0fa49ee0c7397cb4d7f1c0590a46d40fcdb86a1c0d75a0ad5d47aa430ae5abb4a4d7a8f9595a065aba7e99682b0f920ec554f59fa549eb5781aab2388e80fcd027241cc1a7331bccb4326fb0f5682823740e4330f527ac0d9eda5f36a1a0cd28311acae463b50d05ac0d605c4ed836a31da86d2338d4b8e660c705e93b63909cbe751d06e0d97186419a0d56103b723d47d68092ff948d3c38169a80989c2c5f6adc4df270b54e404937c18f148da474018e922d3e404b56d2820bb943ac316a9b56c9c3356d69a80989bed5b5a6b70ce2e013f8e4ad59365948d23e60d317c10b6320623064c52358c8bcdaab320d60bcce4b350d42a0bf232c7cd1deb57671db5241b28098c46523580c1aa01984a52337daca6291c10b0338e01a85231799bee1ddad14d27349521eb3f2ffa065285b0df6c5f8bfe4eb9ab60bb982e0b10cecd253e6ad54df6b55817652305dc4ad1f4b56d032523 (by decide +kernel)

private def part771 : Box 0x840000000000000000000000000000000 0xff2060c3128400000000000000000000000 :=
  splitBox 1 80 0xff2060c3128400000000000000000000000 part773 part772 (by decide +kernel)

private def part769 : Box 0x840000000000000000000000000000000 0xff2060c3128000000000000000000000000 :=
  splitBox 1 94 0xff2060c3128000000000000000000000000 part771 part770 (by decide +kernel)

private def part767 : Box 0x840000000000000000000000000000000 0xff2060c2128000000000000000000000000 :=
  splitBox 1 108 0xff2060c2128000000000000000000000000 part769 part768 (by decide +kernel)

private def part765 : Box 0x840000000000000000000000000000000 0xff2060c2108000000000000000000000000 :=
  splitBox 1 101 0xff2060c2108000000000000000000000000 part767 part766 (by decide +kernel)

private def part755 : Box 0x840000000000000000000000000000000 0xff206042108000000000000000000000000 :=
  splitBox 1 115 0xff206042108000000000000000000000000 part765 part756 (by decide +kernel)

private def part747 : Box 0x840000000000000000000000000000000 0xff202042108000000000000000000000000 :=
  splitBox 1 122 0xff202042108000000000000000000000000 part755 part748 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part777 : Box 0x82c000000000000000000000000000000 0xff3d28e1645778000000000000000000000 :=
  endBox 101 0x318ea2887e3b093f5613864106a83b057c2f3836cd2948fa4c5277072415a91f87d2c3305cb38b624ee0e5b59e49d82e5262a4f92769436adbb0ac2483e981520ad415a0ed3882106abe0bcd837247da522bb985a1c59a7eb623ce1798715ec293b81a68232881b619c1cb48f834e2f28bce05faf8b62b09439a521a3056a0de057b59e49da4c58673055ab62c1701bc681b4761400698725ed32025052931918e8277b4bdc66179795ac6f69404a0e41962bf8392917414b08ec368b2f81a6825179b53659fa3cd04a7f796329eb6b1a4a4d533d4d00ad6305ac3e94128bcd84641252a1389d614d83da50c15e1cb9286f699a041ac82941c8ad47d2805949ed630df979584561b876138179c82541d8bce69aa3cc38a94357615fac647d293b4a1b1262f382956322b78214c500f40cec82959fad55a00cec8292f2cc5d692bda657fb56d67eb55179c7f9414ca0240ec20a5cc7250c196f69404a06d22f30c58bef6962e9f6d012d4d8196e63986607d255bda45e6f0338d2593b25d9616b58d05207b9a9a5d50ce8286 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part779 : Box 0xc0c000000000000000000000000000000 0xff2f21f8787878000000000000000000000 :=
  endBox 31 0x1d87716c5303971ca4e6f002a0d33923282941b9cadb46e039720a523a0d340cc9416b3a09c393359c1a71cac396ea28c67b1b4cce360d3661a925e58192e6f91e671b6e1b42f2c0c9066b59e49fad447d21c563148f353c37e2b549f8fa62f2bb8da20dd072c5f8bce0cb0e5a4ee04ac097 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part780 : Box 0x80c000000000000000000000000000000 0xff6f20e0605078000000000000000000000 :=
  endBox 157 0x1e0771b86417c700a165155303922bf928671b394acee4799cad4c5e1276b139a9ec1d378a095cbb2ced22f2765ed20b5699b40b820245e65276adc0c9498b56e064b4d584761edf046da9e0250699c0542a825179ba88c0fec52738e549eb559a6b026dac65e767127f34cded2b256b1bdbe69aa85549eda318bc32851d611d81fda78e60989155e2d5b41da4fc1a6b824c66a89f9d60e929578c9eb761ac693f069cf6940297968c09b2dea67f77b4834e2f2b28ec0fec1a73d840da9295839c6d2531cde069ae8e00fed446b1a0a586b41b41a6d250cbb0d6836834da4af699780699b0d5b58ccf690b2b17e0249b95286b19010c11b12ebda4502e537018408dce3b2e6bdbd28682539482067b4c1ed6ae7016b1a0a58bb3d844862494a1ba8ca3183fb64127e0af96aad4d680de31ca5ee3278d6aac82a0e02bfe60eb53568272b1f4af0d4d96aa07b9aceb559a9a7e762481ed04ed4f378c71b5b1bc630e56b2d9ac6941471899c14ef637b7ac5669fac5da920a99ede50960ace416a4a4fda0801d872ecc4d733b54d0122f3395a608396b1c095372cd352f3b59ca1271b8a1219385e6d63761b85e18470106a83b5d019a2f3616c3fb578cc136ad8fee6317049fb58e471ac94392d539256c806d627baa8c35a0da09761acc23a8ba328900fed867311458293f14dc80b622b0cd676c5d98c67127e8c2d26179ad4419b2c745e606f80d680b037c06b40583356770bcd0162b5832292b75127f0fedac70fa5a9a2b5179825604bb80c22e82f35b07f67378136e4b985ae416258335a058bc09504c9c6e0db39bd076b1d6314849fb4ce2beb075ed209d050b4c6522ad0d3c62a37b4ab09a3580956b1c19147a8afdea7064438b2d5c142a31839cb577b4c3fb (by decide +kernel)

private def part778 : Box 0x80c000000000000000000000000000000 0xff2f20e0605078000000000000000000000 :=
  splitBox 1 130 0xff2f20e0605078000000000000000000000 part780 part779 (by decide +kernel)

private def part776 : Box 0x80c000000000000000000000000000000 0xff2d20e0605078000000000000000000000 :=
  splitBox 1 125 0xff2d20e0605078000000000000000000000 part778 part777 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part782 : Box 0xc08000000000000000000000000000000 0xff2c41f8506040000000000000000000000 :=
  endBox 87 0x751ac690a469836871b6c0c1a623a30a7d949f8face623eb92631cc4c020cf8e6e3eb41cc93f37fbe8ec37073779107341ddee27317b4982cc5e8398dfef692f4af8bc20e4bff2785a9e4e17b4c93f5869bfdaa637d9ac6bc202683b8facc4618d5239cc5b85c1ec71b2d81a62f4a1bda625da4158aa6236a6c39b1f59fe540317c6012f29cc5b8412c943311a47d27f400f2368b6278623431402ffa28b4b8d9a5e55a7a06669cc6cd5849b2d60601edf1b8cd962cf3958fa5ac727851c24ad6a78574e6e6cd365c91d395be8ec28072b6a9c5e54a097966b2a0266a48fa66a4a00625398c0c94f0b14d48ad49660d9b0764f86a1c28b6ac9bfc51735658077100b245cd9671b4149b8e6b382c43b23e9371cd33761806e15c0eca0a639ba0e4d9734dd46273738acb3941ca024e56a63286f138d86566a7a4eda66d638bd290593c28e16b1a8ce398bb8cc1cdda930754e370756 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part784 : Box 0x808400000000000000000000000000000 0xff7c40e0624052108000000000000000000 :=
  endBox 63 0x5e1b07d0e62c8370ee13dcfbb18bd20a527419c619291ba8c15946252349f900cfbb2d3d3ea50952297a6365b944a4651d419b70ce308619275cd5949da50ca4662f065ce51306ce01f36291a0649d73565b4791d4780806c83e06db9ed2d5b41e949ca2ad5b89da823419cc5f890ab4b7aca08d066dc308515293ac1e6b2a47d8a6d5b9ec2d2f6b1b5262ffb58ca12dc282d466d5b8a3e5099ab6d53276cda3a8ba3c0403411b58e7b493b4f832cccc32c83084f7253c917291a036065929c5a30d3d87a389494948d846e0c173524a4ec5362a94553c046cd533eeb524bfed678d96d533eeb524c33358d2827ba38d4d6b3a0e669ca31c336d398fbad6359cc93f7b4924dac6523 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part785 : Box 0x808000000000000000000000000000000 0xff6c44c0404040000000000000000000000 :=
  endBox 117 0x370fa330ee07f481a3fd2f2ca016b29c045e650b293b8008f9ede4f70638bcd4000ec08957b96545666db27ba31e61db9b417ef8400f03481fd68127f208ca3a527592ce6f5a89074a2ae6f920a6f149f9cc5e474083ad01cc6387a3ed65ab4330c98bd6672d5ce02b338e02b516514050fc5e93eb8285066731737cc1349fa87cde283348fa507d79ac690b39b97a4e6f250521671b85e650b691b465083a81389da83339897a60689c3ce6ec499ab693f3799cc49da41d8bd273149f969e5abb06d1d291f2919cc43fa3f5751ac701a4291bc8da32813f93ce7311798f2d0669418de62f33f0fdb398d27e1fd9aba73138dc50949f9cdc5e713d528273149fbe8da3c8e22f0413630e626f18fce8e141187f527eaa07f66ada47507a6bf923a81d45230b390564693f4839bc5046aff83fa8a1e8a2208d7849f9b8e40eb904e627c3905ed30aecde28f515dce670fec1f4dc71cc43fa731897b3904bfe8f539887f5f0398c93f2849cc649faf0a21cc527f356cf8f2825ed2d3905cb9143fa8407f5a731bc58965e560dc6f10fec73149fbe8da2905d5a0fa2f337fb58c3fa7373fea075e4690e6f13d48261fd8b0604f058bda45e65098de31cdc3fa731927e2f30febc8da4002f35e03fa941b6e05d93ac76f356ca12b62488417ccdb717963070ebd19f06b7a8ad3cdb72d3c54f1b6cde31cc4de31c6ce621fd398c509 (by decide +kernel)

private def part783 : Box 0x808000000000000000000000000000000 0xff6c40c0404040000000000000000000000 :=
  splitBox 1 118 0xff6c40c0404040000000000000000000000 part785 part784 (by decide +kernel)

private def part781 : Box 0x808000000000000000000000000000000 0xff2c40c0404040000000000000000000000 :=
  splitBox 1 130 0xff2c40c0404040000000000000000000000 part783 part782 (by decide +kernel)

private def part775 : Box 0x808000000000000000000000000000000 0xff2c00c0404040000000000000000000000 :=
  splitBox 1 122 0xff2c00c0404040000000000000000000000 part781 part776 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part789 : Box 0x805200000000000000000000000000000 0xff2da47229110ee69000000000000000000 :=
  endBox 77 0x821cc6a174179ba0cc278a1b964a7133909ab650db4d500a4df39991e6581784c08f306941225d566164b031c9be80523ccb4d96a24df063c805541604f01270255463359d3f3032411e2bf8e2eb63089e3b85e7680e42b555a8c7d75a6a4ace2ec47736d0695a6b11e52382657874143f1fad056e515aa9cde3fda0edf47413ef34e437e92b15ace4f7299cdce671fadd023cc7175a8d069050b9ac78ebc2d5641aa82d48ea00ea614aa7de4a13c58010e08f521c83b402aced69b28d57866102b20ed3f341ecff6701736cb495416671c7565320eddc541840dfc9413879cdd46334cd48a92b387b08b2318d67878e2bf39486ed25f1ca418b242ce520c9402c2bf60bc1bf15ca4ac11e099 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part791 : Box 0x825000000000000000000000000000000 0xff75aee32c13cea00000000000000000000 :=
  endBox 25 0x308901f8c824fdfc5e05e6b55907680b89bef69389937e3998eee60d979d67e9c230c8205506a2f3946a72183ac929651867247c5e6c1524fbda569a1cf58165334bda4273360a829dab32c4c5e6d53390cb13399af8c338e6680b41d873d69b41d4daef5d405a0d569b20149be93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part793 : Box 0x805000000200000000000000000000000 0xff37a67628110aa100504c0004028000001 :=
  endBox 121 0x308cc2f0ac2708c39881541abb8821c7671c979c5e60cf394a4353f3239c5e62c9179cc47066b51e25e831527eb234083b4a15041143a4f5927ef69066a91c0431b8d3f22f30e29c6c5e71bece528e9066c729498c0354f19c2563a93f466bb8fe398b1d92629f958b833d6aa2f34a127e8d79a8eb41384ac56696c1a568680df724fce528d7927ef777bbc0cf066cd02d0c424fd05728c49ea737523cca2436415831c17af779cd66f3415c1a4b571bec592b1d6f168731dc6a0de271b40dc697474a50e0d3138419b0bcdcdf2ccd19af690629c6dcc179c0cf164b4ee83bad25ed20c540db9893f8bce2f30c3cf6949fa06d8c581185a1692b5177169b06b8e36e6d962b033ded2929405b50e6328b1d0669c26405acad69a9f996568f9965ab41384a02d27eb1d0edcb4d736bb907f819ef717368314e520c59cdac40334e2f34e4e530779a062168480e1a7373ebce6b179a4fcfaf241d6aeb6230e61c745e72c54bcf0779cdee62d067b8979d25e0cf15ccb1d3ebac556af0bce48fa47e179ad0d835893f5e19858158384a7e6495a4bd00a92f82fa8cd580c9f9066b41069925ea4783d833d1f7033e15fad35ed3230b4d83dce5947da015ed323a5504a0c7d783b9385682b57581ed30afd1ae7097b4c2bf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part795 : Box 0x805000020000000000000000000000000 0xff67a76228130bf00844040280001000000 :=
  endBox 95 0x5a18c6c0fc45127e72310c4b2f5a86e483b8e527ae519eeaee2d8b1d27aa4f6380ac66140a77d492e5341aca33616af09233093d93bea1b399a0eda8179ca494a0c9df58cb056523833501739b538450a8519ca354669c6c576c2d62eb40e01bfe0679cdd657202dcdad5315db12deb335755fa72515db12d7860aac081514ac83b399b95e7bbb95e68130700de30779442737736ca1f179c737397cb1d661383f1896c5d49ece6d047b8ed48a2912f59cde402b8edaa6fe2c8c2380e3b85e681b9ed338ed1ce0a1392cf69523b8edca26f19036e518bd6cc228542916386b0b58bab01c36399b12e386af8d62f0733510ca31179a05562f1cdd62b07f62f8bce4059235ed259d60ab0563ebc90739b8bccfc351cc503bda62f5833cff72d5d486c8400be25070f93ee733179ad5cbd72c560d27d726fc93d466cd5d524a4f45e6942d26140bdd5aba80b5abc1a658aa02cbd6822c82f3946ae414058bce58aa7dded20cf51a8bce (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part796 : Box 0x805000000000000000000000000000000 0xff27a6622a130aa00000000000000000000 :=
  endBox 89 0x308d80facfc6317c49fb78e8074deeb34fcbd6b01524b576580b95c9bea499602a075a0a47c5e7137dc064208580c2c9179833e164bb8afd9252d5d066ca499dc701a06b1a873da523e1db38d833ce1b2d3523f46067b4874da7ea3559dcd2f522bd65a5aa35066b80ee0bcd3c60dc5e76aaa434fa692939bce6f6aaa435aab2c94fa6b4d2f39f8942925603281cdf63619ca2c5d7b497ad8bb1f4ded307351ab60c62f893f540bd72d056af0428be3909c2418b033d606a6cf69466833d61e4df741ebb201527a71350da016233bda560491a8384937d68323edeeb0736b1a42d6aec8291e834c1ed28307ba0d27d73517837db9667a9a3a5eee0a14029a9e6a9bda569a8058e12a215612415fcb434a0a86d492bc3da672cbddd00a0cd96af34fdd05a1c066169ac83da4bd72d04142d35731cc33384ad04f869e34b014317ad88474cd2f380c1de50e9f4c512f6992c6b3c7052f5abe6021b1254928cd5a0bda5a673d8548a5eb (by decide +kernel)

private def part794 : Box 0x805000000000000000000000000000000 0xff27a66228130aa00000000000000000000 :=
  splitBox 1 101 0xff27a66228130aa00000000000000000000 part796 part795 (by decide +kernel)

private def part792 : Box 0x805000000000000000000000000000000 0xff27a66228110aa00000000000000000000 :=
  splitBox 1 93 0xff27a66228110aa00000000000000000000 part794 part793 (by decide +kernel)

private def part790 : Box 0x805000000000000000000000000000000 0xff25a66228110aa00000000000000000000 :=
  splitBox 1 125 0xff25a66228110aa00000000000000000000 part792 part791 (by decide +kernel)

private def part788 : Box 0x805000000000000000000000000000000 0xff25a46228110aa00000000000000000000 :=
  splitBox 1 117 0xff25a46228110aa00000000000000000000 part790 part789 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part799 : Box 0x801280000000000000000000000000000 0xff27c96609c104659d40000000000000000 :=
  endBox 61 0x3b104330d42f0b60ff480a9a38f672ca4f4e1eb298faa93d83aa90cdbf05cc18a7d552197a57c58018b1c5d666b49399ac8a02be638eacd4e4294138ec80b390d07f72c9c3dcdb27e4e3a4bd5a4a8d5a4791acf2be4e3a80b41a8b465aa9cce4959b7d6c531745803773945282a4926fa68c3b8bd270f3f5cc552f493d4e6f09fce0272b8ff691d4a097a66918453164394a6883b8ff671d3fdc83b4a083166a123b20d418a80b8e3a835042cd5359d8314e1eb4d8bd2a02d008904286865a697d6301ac59db50d3384fe0bd0629c5e5a681fda6730f5a9a07f597b0007f01dc0075999ccd486a49597cb33 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part801 : Box 0x801201000000000000000000000000000 0xff37c0c2099186249308240200000000000 :=
  endBox 65 0x7f1e4681d06e18830cc62f4fbc70530bb085ff85e6701c1523324acde693d93c431305a697cce1f020c11a6f3964a6e9736c6e9046ad345e6b3b9ca238d61ea914e1eec2782f3382cb4d6e118202c4a7380ac95ee3096480ad2f2cbc2975a6c943488025062f49385462a4562198581640d693d66a8ad3c16eb232f4cc1905babddcd6e519cdaa330d0ca2f47da925466d338d2ab4d71e93d54662799a437148738f45a2737736a87d685916471cddcda0a3510c2a37368eae60cc60519a6951e39c754862799e47617861080aa4384f283b587cb4b7359ba4e2ee82d3608dbd85646b51399ad460dfac8ce672b8a1fa302b4b0509c366a8ac8c7fa199 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part803 : Box 0x801200020000000000000000000000000 0xff65c5c3090107649804140090001000000 :=
  endBox 47 0x1e4801fc611c06805e6dc202e7b9b9b548a617312b5918195e605d7aec1d4fd6721399ad5683acb5583482660fed6359a9ccdb8517c01700d93d4c2e705390989560382a87e399b57671ead15ac67eb4f0c331c15985e0e671819eeb1870d89b5dac680536bcd027d626fc1f527a61983fc155129b58cafa93d5e0e66c420560d30b2480a0199cd683b4a0d27202d81a7177d1cd72c753f2b5112fd07f1c89a4e0d23f590762f36917c621462b43f87371feca1f6b1c1fd46a94151acb559282a358e1ab554fac5d54a08e06 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part804 : Box 0x801200000000000000000000000000000 0xff25c0c30b0104249000000000000000000 :=
  endBox 159 0x5e15c820e62fe380ec3302f3691d00bace6b0269c4d06a7335aa9fae41a97ce5a6855dace73339bcc3d50f98bcbe700370d02cbe4a1ad449ea62553169a60b38bcb136a69c4d6aa713963ab458e0a2b78366b3f27ab30b559cd6a1f3129c84e66625941670576107710141931ccda86b17c317831c56f28bda662cf519b9be5a6976e0fe931948e73741ac62f79208761a870184374c3f540a8bcdb862100b0fb4c32405389cb4d57ca785d59a96b4d27a9c4c54f1c3d48a73305dc4053909ccda46e15f31865eb6b4d402a0d5ac7416ab1c84e669e0eae23db5949be5b327a85fcdd23599cb27eb7279c3c2cf2d5569b2cece6700358ba306648b8324e26733594cf6d5a89c5c9d6b4d5a8c6fb58ca50d68ab4d8192a3169184064c91740aa0d41932d3500aaf78be69175919865a85a188761b85807fa70f969a1bd5a5caf739ba501b18fba4f558fcc434a0821e5a68234362c2370b02d5659c9bc41929294a1ba00c78e1ab35486ad549eb1bc60eb31356aa4f572cc8fb06393d5d06e145e4f5985ec5f4f9832528341fd3e6089811ad23a06df9672e595aa822613ccb4d4959bc4f821957013c5a1fc5a6b707a185c9bf0bccbe64df85e62f38be670504ccaf7063a4edb87f1a05016c30cb5070f11ac3a9374831c5e617b96930bcda970d9c5e671d3129c4e0bd97cc5e6e82c76498a02c2f60c948bc36b57b85ec18e70f89be6e9382b08fe340d4031e3178bcdb838ec7fb312ac07eb8b66e4f0b39ccc097015c2cee592d9b4be69ac1d55e67333f58bcc1930305fc741b8380c328c3536031b4d4dae701474c0333e0b4d4e2f230da5ee6d6b1a5060d273336bc733710dae481c3e69aac8c23f398c256f6126f850623291e4f9a077727831e59c832598317ce5948ea3e4e4273323cc625 (by decide +kernel)

private def part802 : Box 0x801200000000000000000000000000000 0xff25c0c3090104249000000000000000000 :=
  splitBox 1 101 0xff25c0c3090104249000000000000000000 part804 part803 (by decide +kernel)

private def part800 : Box 0x801200000000000000000000000000000 0xff25c0c2090104249000000000000000000 :=
  splitBox 1 108 0xff25c0c2090104249000000000000000000 part802 part801 (by decide +kernel)

private def part798 : Box 0x801200000000000000000000000000000 0xff25c042090104249000000000000000000 :=
  splitBox 1 115 0xff25c042090104249000000000000000000 part800 part799 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part806 : Box 0x881000000000000000000000000000000 0xff24c2664c0910200000000000000000000 :=
  endBox 59 0x1043e8f235840320e93d63849c9563b24fcdf6ec3083fd3e15c378b60c61cc56470aed27e29193c2b4383f9b7d48b2cac9eab0d5ab828d284949c3564716149ea7d5927eaff59ca4a6401ad34bd6a1f398a91627aa4fdb057038317ac9ea93f398832e50fca47741e46b128399ad07175a0c91f49f8fd594498c0cf398b15669169b3dc60d63f5405833da732bdc7ea0af8e623f5057c0bd49f86d47eb06b8bd60c749f9cc5cc6b1a00e9c92938e831c196c22e88159cd6a0d366a50c3a63eb5e12632c74e62b1d9262b4d9ed27315d127e7311f5ca0752182bd23f340c206f418ac5d9ed2f6149f9cdd69b3da527f0fad63ab49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part809 : Box 0x821010000000000000000000000000000 0xff7ccbc31c9b84a12420200000000000000 :=
  endBox 45 0xfc5a1a849fbc8a2f610d3b1feda5a3bb415985cc5eb239eda73172b98647eb17ad492a018664ef9cc5e441dc9df26f9cccbd7277de46413c399a3ee6ac98642b68c3524873ce42e2277e524a02dcb32bfc97ab135a0c1fe510b575c7673130ca2870290cbd66df96824eb02f81b49d72d5dc9eb5536f82ee521ab8dc1cc5e451acf6941598bd541facf6951a828dcd728d560399cf69735a8d41470759c46e1e4399cd2d594a0acc5ec428d4dbf41d56ab1811faac6671dc1d5652e4f91c2b2951aa50e3f2b4ece126df (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part811 : Box 0x803010000000000000000000000000000 0xff7ecb4a180f01e1a060200000000000000 :=
  endBox 107 0x350b4310ec370c00ff5c4571492c47927eb2d2f5a81e49f9bc56aea459686941416a4fe65127eb558de2731473c4f55a29bc520e5eb94927d77b4b11503a8336c15c5018c398a28afd8112f696258aecde25eb736cf6949fa39d48ad21948e6f159fa406a2ca567e93f615ce6b3eac0a357fa3ce378828d40ea1f3f12083fcc4b60aa7cd486e6b5aaa4fd43f27cd5857fcc15378aca548b247d5fa6f14d1f0401b55658aa835486e575228aae62e8dcdeef007438e5eb72ba87dcc6c140550e62941c0a45519c27740997a51f691f2d001f2d5d65280300c9b7d4664df95fa6df5618083ac0bb50faca546aa43470cb558c0c9f3409b88c041d662da8854868d19cd64f547cc6df711cdb41cd46707f518ad5cbd6a432d23033da528690d519967e83fa91d286b413f143ee3b816ea072f5a90da5b460438ee6d40182dd14710bd6c02d5e503937d4867d590269f3836c0190c0919c91e07d7109ab0b453e6a4336fcf755abb187e3e09e2404f557127e1a79eb27d705197adca3395d3bf287d1ce6e17ad6803ccc5d49f896cde291d8dbf277d27ee51378c09f2f5a50f804663988d35282a4527a867e0519b7da5b071dc9eb554a0a39d886b11c3712823ab948e7f348ead56727c1b626f8b458bb2916696828d8667f3735ad54de2c5d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part812 : Box 0x801010000000000000000000000000000 0xff7ee342180b00212020200000000000000 :=
  endBox 57 0xe23b0dc25041b20ea8093f392b984f58c3290793be62f826e4f50a5a4764a098bda4660826c635893f6200073da56567213f59c9527ac158de2e4f47cbda55fe7053f59ccc0ab39acfd6c1537896763e0b174e66b15927e7e137e399a4fdac49ec90738b9ccc9eb027ce626f1660806d631072549fce417b493d4e1261972ecc1b519a91e622b17503aa338c32cc2c073196a2c1562e9034df67096e154206ad8d6278af99ed28f930bb98683fa4fd1f2b4162ecc5d96aeaf98e42d2949f81a603a9c8527ee6308af99a5ae6348698bd6825ff5e1946c165b350e0fea1d398850673581158be619519ad0e730ad049ea61992832d0d05ab41 (by decide +kernel)

private def part810 : Box 0x801010000000000000000000000000000 0xff7ec342180b00212020200000000000000 :=
  splitBox 1 121 0xff7ec342180b00212020200000000000000 part812 part811 (by decide +kernel)

private def part808 : Box 0x801010000000000000000000000000000 0xff7cc342180b00212020200000000000000 :=
  splitBox 1 125 0xff7cc342180b00212020200000000000000 part810 part809 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part815 : Box 0x801000820000000000000000000000000 0xff6dcf72180d41e009440c00c1041000000 :=
  endBox 33 0x7d1b8790837107584451a437fa82639b97a67378ff5885b07fa0a993e693f6b097551ce7373fec9e169146b395cf8307560aa87d48e8f3857ac413d649f97a60ef3dd49ea93f504b18c2360d224fd14519cc5d27a9cdce1b07791ceb45179aca582a8e785e64f571ccd6339b9bfc5e62618ffa4f549f9676179b7093f2ceb176275b9b564662f053cc5d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part816 : Box 0x801000800000000000000000000000000 0xff2dca520a0540a00140080040000000000 :=
  endBox 151 0x27872360b4d631cc49fab8f21cc6086a114179be85eb460c1741cd252b195a8a03658ca33658ccb198bd6403498c6e53edac74c5e3eb4509bf02c49c21bd96c741a4317be80b398be73760ac0b3623c0b1736bd5d04739bcbe6f5739babe658793d608406c41b58ecb49394c00dc340a0185cdff311d8be7316a1881fac3fd584c9436158a7e37f900e7b4b4d561241d3059cc480717fc8271bfce63043c8e63b041d8be62f3354c7db498ac74c5e83358ec80d394a0cc14730660fa2617b4b17d0068335d1e4133c37f7b4985d2625f31f5b480a3736c7c3729b174f871bfdcdab1d9c729317315c630e62f224fda882118179a4a6317a50c9eb24c563260b8fae0af498a4edf4317c9f51f5900d82b233437b250c9c2f22336727b054bfe413179ac0fa24ecde31cdd19b2c4c9beb1391d27373f20049fbc8d43702f395fa943317b17e179900e50188f317da857ec93b36fcb098369a753eb2824806b3f7d1d84c05e7282cc2ea336179c6cdff07391cec2f20d9cdd05a6fb93eac5f2ffcc5f617b4080d71cc7c139bac7549293f0de82ae58ead25b07315c820e62f2370413179b056466a4fd07693f9eea8cd60abda5147d185b317505ae537379c3562730b5652f6949fa3354371f553ba0a360ac0af26fa4fe086a1905605e6cc3708a0fd4b8386b17648f9f558bb247d6aaa1f927ec1549fc8c371ead5543f28cd27e70d9ca63bb82ca4136929aa658c9cdc8267379a0606c6f140e9ca4bd73dd47d693f58eacce08611e46218ba413729cc25179c6f18e6eb1d8bd63fd7b4b08c5d981a0ab7379fece6ea1b9896f69 (by decide +kernel)

private def part814 : Box 0x801000800000000000000000000000000 0xff2dca52080540a00140080040000000000 :=
  splitBox 1 101 0xff2dca52080540a00140080040000000000 part816 part815 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part819 : Box 0x801000240000000000000000000000000 0xff3ece5b88815328204c108201248000000 :=
  endBox 17 0x32893f5e1e473163b176cc5e4f51799cc5a84fcc7d75a6ad05ca7461569a7d727ac7315a6a3a671c97cd276e53599ad3588501a849ead2650dbd5c242b57018d0693eba77d20e60b923a7d7961e8f9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part821 : Box 0x801000048000000000000000000000000 0xff2ecbdaa81103642089104208009240000 :=
  endBox 43 0xec410f2388941962a2f3209906d8430bcb5739b8bcd34680e027319862b4130c890641ea8ce839a03565ab435b1846211eb3484e626f339bb60f559686e635a0833ce1b17a63989c3d6af3109a311e49e9cdd21a3eb4979c0600168c8cd4979cc4c5e9418e6e2bd87d660b791845b1c4305a7de406c1fc596731201929e611a8cd07a6e5049ce4d201ad3609d9cc4c32d82507315f11f7286d286a45372d0732f49fcd6532d36 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part822 : Box 0x801000040000000000000000000000000 0xff2eca5aa88103202008100200008000000 :=
  endBox 137 0x1b0481e449fb88ca308ec0fac3b6a01074ff7187965a8d7611a505ca7461d23ac2362abdde168ad25b8621d87308367318e1e6194a0c7059ebab1d04898655f31cc482730841b5b05e65ff927a8cd9eeab577aecb5738293d5cc761903e05e66e99682b575e11f730c55f2a1d398b126119801c2468d5596ac5e27a97cd6aea0b98be61930b93d65a4b0ecdcab3b5a0a50b23504f55d1682731940e80326f975662d833c9bf247594370e6291f02cc05b83fc389618833ce1ef7547dad5e6a3a7d5884613450dca2f50f9b94e3ac8351e4a0833e6b0a81dcdeca0b465249cc5a8f287d3f2a1b02ccd2d50f833d006b557319461178790e625db948e2f30edaf8e6f923aa1f47ccb4d46684dd1d2d2d729982e62a8bccdca1db474c92f3729864e62e22476067906d8848ec2f349e8066179a8cdc4500836b1d828e73748c8fad282b2d923ac2362a9fece6e3eb4a0c7fd39bad0574571882f5a68ca1c05c4790faf2d3491e9df50d86ec82681385661bb5a6ce6b4f39fcd27b2d07d7919ae5127aad3491f277c916a49209a33608710e0b1fadcc624f2099075cc32c3d6ae4f57358bcd65aa499d8621e4387b98359a0e641339b97ccc5e91d87d646793be48f6b09cdde47c161e15b94929f51799c162f9a81e50fa7de02c9b9569ab51761e4821cc20db0870d96825f3179a78e59965ac495a0ad351f30065cc280d5a0ad5e27ab9ad63ab2d610ff71cdc3b6d0130e5a68b453c72d446f6b1d61188093c00f4f3ad04fae71d696a87dac273750fca338bd24f5791cc4f1cb1d305ac765a4a87e6b0a7e474eb4d (by decide +kernel)

private def part820 : Box 0x801000040000000000000000000000000 0xff2eca5aa80103202008100200008000000 :=
  splitBox 1 99 0xff2eca5aa80103202008100200008000000 part822 part821 (by decide +kernel)

private def part818 : Box 0x801000040000000000000000000000000 0xff2eca5a880103202008100200008000000 :=
  splitBox 1 105 0xff2eca5a880103202008100200008000000 part820 part819 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part823 : Box 0x801000000000000000000000000000000 0xff2cc2528c0100200000000000000000000 :=
  endBox 141 0x1b0291b18b432893f391cc441d05a6bc8e234107f969e709067906cc32fa1cc5aa31c05a6a41b38bc6a969a9c26354c28f1569cc5667106ce62ec1cc518b3db5aa20cd57c8ff507b282d462b1f818a92b4a0903569ab3392320c54fca5047ea73179162f350c81a70920db10c2d91c6a094838ff51f3033d3eae6328bc3107313816c7d0dae0cb91f6c1930c93d54626f3710bbb18654924bd8c32c197c0dbf28756ae4f55abc413821f47916af2874e1e41327acb57387b9ae50d93ad6824df9b8791a871ccda4a0cb57cba068032cdbf05449ea7c183fcb41275a7c627aa78e8175647cb59495ea2f38993ae62dcd3720981ee0fe5d5761d0399c7133879865c45d08266e99ed2b232f59f5e5a7969d646f691e3cf692f59034daf359d8923c76179865e46e1f45abcd432069c2483672193e2e5d30cab04f593bee417baa7c527a721483c9df27aa4f53e2b213ae27a833e4f8c10f22f840d58ece5d384a31659997adc828134f8a204f54eec8d57b49f05eee38126faf870f8d86f7759683164f883165e208398bc86198e129f194160615ab9c3c7fa6df26fc5e930c833608624c41b30c9c5d25f2d3cc32ca2d1042d35e471ecb49411ad04e12413590dbf23e5a6ef696b2a4f4fe73da4e0625cb4b2f4b4d64738b4589694160dab8f23da6087410c580c467839a04cbd640d2099c24beb104ce1f4605a965eb27ac1de0c7c6049164bd2f593d62f5ba104388f2399e389a77c826c4277e3879fce379c7093f9a7d63e1abe4e1e70f9006f2370c5f8e1241b620de72465ed293d524c9f56a5b98ded2b578142a1d (by decide +kernel)

private def part817 : Box 0x801000000000000000000000000000000 0xff2cc252880100200000000000000000000 :=
  splitBox 1 102 0xff2cc252880100200000000000000000000 part823 part818 (by decide +kernel)

private def part813 : Box 0x801000000000000000000000000000000 0xff2cc252080100200000000000000000000 :=
  splitBox 1 107 0xff2cc252080100200000000000000000000 part817 part814 (by decide +kernel)

private def part807 : Box 0x801000000000000000000000000000000 0xff2cc242080100200000000000000000000 :=
  splitBox 1 112 0xff2cc242080100200000000000000000000 part813 part808 (by decide +kernel)

private def part805 : Box 0x801000000000000000000000000000000 0xff24c242080100200000000000000000000 :=
  splitBox 1 127 0xff24c242080100200000000000000000000 part807 part806 (by decide +kernel)

private def part797 : Box 0x801000000000000000000000000000000 0xff24c042080100200000000000000000000 :=
  splitBox 1 117 0xff24c042080100200000000000000000000 part805 part798 (by decide +kernel)

private def part787 : Box 0x801000000000000000000000000000000 0xff248042080100200000000000000000000 :=
  splitBox 1 122 0xff248042080100200000000000000000000 part797 part788 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part825 : Box 0x900200000000000000000000000000000 0xff279049690404801000000000000000000 :=
  endBox 133 0x410ee398dc368be1cc649e9fec5e651528fb40f2149c5932054e1f1cdcdd72d35492a1b179af8f4142dab72d1480a73140ac825589ad55e8202c83b398b087379a92e55589acfd493286de8651b4398bb00bb9ab6a2f5059bc45e61bf967e509541d870188504cc4d386ad34e6e6a396aad5b584ad34de32cbe522a91d4932c4d67ed0461e5979fad46a8f11799424d470bcd1e2a8340c214241731cdd8a2b55522c70f628ad36733b58d65293961fb15dd859fc2f31e3cb2959fbb0f43700c38e1e4ff1f29015506818427fb0d6510ad54fbab4d39b9f766a1ad358051acd5b4938e9e6adad3d6528fd35199091d986ab5562d82e5626c02d3651a82ecd2b34a5303f16931c3d486a494ffcd5b497831546ad02a0b61c0650d9c75686b1c1c950d97c49ff399db859dcc2b6aead3418ac5b924f2d3568681b454018b0705402b4d27faca605d8315805a6acfe0e082e56ab2cbd69b06ee5aa93fc18af4280405835cc216ada0ecbe273141ac2f341db08a1d94625f140aa0d45e64f79492c6370cc3d00c541dca454fa875568402c92b39b97c4d4f2d45eea92750da4cd492ca308b62d0ba1ca5cdf00654665db51aad3437eb4d9416c3d2ed9cc437f1cc4bb69f98d96d5b5a691e6398ad8c21f1e483b56d2825db39b9c3e728a7d5282c09946ae516adb08ec02ae5a686fce527370dbc1bf510c9416a9b280c98e62b63b8c239ab670f39b8b2658f8f0569e7fb93f21d5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part828 : Box 0xc00200001000000000000000000000000 0xff37d0f81940060a9006008180040000200 :=
  endBox 47 0x7f1b4741e46e1405b0c32ca188d64339ad3e6d494a0b4d563e731402c9415a6c731412cd634efa0ada66b4d30598941370b3ce6e6cd7616c591ac6b1c3c73879cc5232ca1cdce63353d69a9051bcc70f8e3a0c9969a731519c731691dc482c0c738e9b36063c1f6698b965ace39759c9cc5106999b364949bfd69ac21cc55ef3d8dc72e53365cd4304db18ca3b80c7379cb073989cdc78b3b8c23576366a7cce1e72b1dfcb1f387b082c99c72a4741da7d6064c5dd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part830 : Box 0xc00300000000000000000000000000000 0xff3594f81ff007801e00000000000000000 :=
  endBox 33 0x1f4771a45a1b438d9cdd3c48797c418ed35969ac3b9cdac3f05cca1d490ad8d41c75e4063b56e61186fdee25f3270cc5589c2c2790560c76c168398a70b4d587c2cf57bac8d5ef2c35acb356c9c28eb40c937daa317ce0f283959cb48dc350939a30707559197c4dc6825063b9b6159a02d84e835371cb4d49c97c564717c5a4398c9450639cc6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part832 : Box 0xc00201000000000000000000000000000 0xff3f997819d0a6001188040200000000000 :=
  endBox 77 0xbe2b8b0280b420a5072ec1bfe7b8b53dc8a1bb39bb53e6ad8b44376d5b9a9a2bf0dda78ba209d4c05586ae5a6988d45ec559aced678c46905761986e106b18bce56b0941db28d4d8fd60b539bd07d11e80de30eb0971ea454e6f356d28b3dbdcdea476ad9b8a6205d5041dcd5b3178b44e3a7375a7cd5b0df97d454eb0980e207748aa515506114c62ac4e138e988ce6e4e1928a941966ad53387b70f42836728a4acc32a2f9282e4f9282b0d611a4791b84d0c46b499c76af9394b4e4e3a82b9cdab4d41aaa0071a0ea0b55069c04e6e5c02de6a99ca569ab099cd707d59cc61ce52d39473c9f96a8b944e3a70398819729c929311ac3e510b4de2ffad364a0ac25b473184394ca2f6a597fcc46701b96517a4bd492b1f30ccd655d0e0506ca4976184405c71d41dace6473a90d5f2915928ac259ab6af92cccf6f478a49d612809 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part833 : Box 0xc00200000000000000000000000000000 0xff359179195006001000000000000000000 :=
  endBox 155 0x160501707a07d2fe368c22d8e624862f5e0bfed5ba30e94105d9cc4e0524cb4f404b58e69bc60522ad673edbb8b4d963e0b1586a06525702c561abe2b81bb90325f541ca0660ecb70a35818aa0d8ff72d3418a5f531283164049865aa72d2d69e601404876646bc1bb414a0e5dc5717c6510528397a198398ae80c5902ad5d4a28316610b59dcdf357437f28d4fd6d356ad82ed3f32054ff67375e1cc049c907611a7e4c461d9398ae8915928aa0d72acc39478a7e598420fc2f8c61e48aa90dac701351a2915506a8be59c8764fc26fcd2f311a92412b34bcc46a357d03b2d49961a5ff404a505033286cf07a1b883cc9f5523b93d87ec576a8876567302562f8ace6727b4e501673104a8325d8661b86a1ac0eca02e5a6b9b504e1c906497c64138725385e122b02cda7262541aa0ecbc405b09dcda6259ace8e9250b96648ab4d4e3730e5a5e0b3413b28ae3b8a8209cbe31cddcc702cdeea72905ccd390dfa45524e73781766c9904e5f16b19cdd5026fce6f3119c74e6e7298376a496e1b47f1ac73018a5e78c46a4996a2163372b56d7450dca4346bcd4d613b8e418b2e8a83526628a86d84ea49490acee6b3a925ab734cd84eb4d2f8b4e4157359d04ed4370f41f81d948ec8f183d989584aa49737a05da932504e36ee330ca0316064ae8982515467356dcdad2f39ba8d5cdb24860d3291d21671b3f1ab305adcde8176acc71b2f8c0c940134210be31cddac69224766a9b0fce56941395cd53365a48a41cde2f89b35282f75a0fe4bd3669cc541b17c4176b399aa2a210dda49ce52b62a0ee1b871d2f8c73748e938661ca58d538c5e8354a2a49e41a9cc66b1ad2d2569416610571c6d06ad4991e2817 (by decide +kernel)

private def part831 : Box 0xc00200000000000000000000000000000 0xff359178195006001000000000000000000 :=
  splitBox 1 108 0xff359178195006001000000000000000000 part833 part832 (by decide +kernel)

private def part829 : Box 0xc00200000000000000000000000000000 0xff359078195006001000000000000000000 :=
  splitBox 1 116 0xff359078195006001000000000000000000 part831 part830 (by decide +kernel)

private def part827 : Box 0xc00200000000000000000000000000000 0xff359078194006001000000000000000000 :=
  splitBox 1 96 0xff359078194006001000000000000000000 part829 part828 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part836 : Box 0x804a00000000000000000000000000000 0xff7fb5f0ad104d675000000000000000000 :=
  endBox 27 0x368ba2f8dc0bcce4273369cc06383ab95d0168352f8c927064c9392f88bcc9ef2d34e2e2f36c0f0500be2d03083e9493c9f571dad3502a835610d07588ceb4d2eaa3c524e8cf902a83562ba809e0fa5863317dc76b4d504ca1d5e143b309d02a8355d169a6e99a72f57371cc275a89756592ad3502a83b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part838 : Box 0x824200000000000000000000000000000 0xff7db8732d125c521000000000000000000 :=
  endBox 19 0x5f1d04f1073245569a5f1397a88bc0bccdf65f1399a7b659fa0a646fb08829942aa35179aa082969ac94561392c5ac6c516acc0636a4b78805906a9394a297c64f0be2713969a9ed85e6915 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part840 : Box 0x804280000000000000000000000000000 0xff7f997129d00c523540000000000000000 :=
  endBox 85 0x1a0581704f07d2b427e60e4a40d072b4d41ccb0737bb68d630764839808299cd6a156b3a8564149fec2e32025bc5d17c661052839735c0c54a2b4a66ad9f89079436a4f95e330e51e28294f1c7734cd3f2af10409c15443f4c82b6adb575cb27e99abac5b2eab78b62a070f8e3a801b8b4239d4c610e4394990b4d4ecce515aab52605cca49900f1855a6c60e83d8e35ab71855a685b66acc1a60eea019ee204d48ab9b5aa6d63723ce4f57cb95c18a4bd5a1005aac8176a4b54d22b356d46ac3f9492c5762dac8a3582e2b130bea4f5cd73d4c4faa491dab789c2a0d6382e6077628b56d87e701478a49d6850dc90b48ab5240eb242cdeed6278da35765a69c85686acd183604ac1cfeed6383bc802c8d424bda9f3075abad5b9abb357649e9ccdab6702d342d33575ca6b139a6ad6371db07542ad41bdce049ecc356aeb0d6023c93d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part841 : Box 0x804200000000000000000000000000000 0xff7f98f029100c421000000000000000000 :=
  endBox 103 0x1b86d17c179c51528fb40bc149d6079170179a026498acbe404ad54fd3290d1f2d5b1f4a40e179a9264fcb4d5286809179a37e5f1684f0a16d02c0de2826395ad3527682741caa0b13969a6e548b97c569b2a0de2f0817395800657c9bdd89a83b504b91683aa43658997c4def2d5569a815904ab135aaad3550530de657d84faa0983bac4cbe32825aceb299a9e82b412b40de2a08177b6ca47387b56e4128afd83ab0298c224363f4b53d2867e99667310cde65d5834c6f76269bcd8869e2c0b078de6b5149da08a61c065178f1d21a6e992071fdce02e3b91be815379b78662c090341dc9174049f8c579cdaf7541da86e30b39b4e3a80b41d9f8809004c83b57c9c3ce3b308b020ee4a1a43641da01657ca7e492ab3b4ecad342faf2358d41bdd786d1a017981061f4b98cbaa92f4a09fa4a1280315e399a4e5ac6c358e66c5b7a8b53d27ac57540bab359d8b6701621cd4f499c907179ac08299ace733541bc613cc575aac5f17bacb036adb93da876150179b16e6a6b15d4926d7490bdb66b1ad3567e7db9266b2f50da90d69b393c6be9f7490acfd8a32915012509 (by decide +kernel)

private def part839 : Box 0x804200000000000000000000000000000 0xff7f987029100c421000000000000000000 :=
  splitBox 1 115 0xff7f987029100c421000000000000000000 part841 part840 (by decide +kernel)

private def part837 : Box 0x804200000000000000000000000000000 0xff7d987029100c421000000000000000000 :=
  splitBox 1 125 0xff7d987029100c421000000000000000000 part839 part838 (by decide +kernel)

private def part835 : Box 0x804200000000000000000000000000000 0xff7d907029100c421000000000000000000 :=
  splitBox 1 119 0xff7d907029100c421000000000000000000 part837 part836 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part843 : Box 0x800300000000000000000000000000000 0xff75d4c00b8005001e00000000000000000 :=
  endBox 137 0xfa2f0ee340da302671d9cc480a6e94828bcca4e5096c1a8398a78405365cb4d3789ba524f02e5eaf394d02ed22f8c4142de4379b56e202a0560ef02dc28e7d550fcd5b402c3618dfeb4d6ada01da86612870dcd64ab3b3989015c0380cd5b3988bcd813247d3c65152f99cc542720ad24e701398b50dc2b8405161c2f35a69cc564519cb3357cb1345e72d34dd2d8278a41cc4be26e95a6cb4b046b0d548f2c8c4a31634dc6c3f2f88bce3c15c59cc7316b3a4e5a46ada0ee83db52cbe2a09374a91d6733dde4029cc49ee835771b86d168293a4e63808bcd69a8f128ab80d5193fed656118bcce028401ee039a7fe62abdc4ff6be1f8b6380c518dd28075a6942ce02962108fd92423c7969f1ba56671f9d00eb4f8dd2b4d285a10b4d8e029275a8abe6600f05b124ee02c8da97243d69ee4f387918646a822630607d5a7b93c9bf1ba4be29e380b2337491ee1d5a0650729f79c8e7e72f9ad3dc07aece6b404a43c5e670f2d230b04e5cd6e634fbb93e6b3bd95cc707d8fba8fd5a69cdcdd2c02e8ae2a89394a2a884f71b5cd67348824630a2f3592c61e6b3a354d96003179abdc113137d84eb62f8af75510c27b97c64fbad3d3ef17c501741fc5e65895a6b93c18f0bccb1309f53ee4f77279ba540232caf77b095f418e2f35a693dd69b0bcdb8501c027bbd8e26fa3f418eb4d59cc0816a6cb4d1799ba65d0e627838092749c937e500ad3c18e4df8be2b4f7f17c4f1ca302fc00307951d9f9d0729620a566b08e404ad3505f937d84e14d95e6d5d01ca3a569e8098dd2b234a2831e0dfa515646d030e6063a0a53c61c8bce044ad34fef0758be2903 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part845 : Box 0x800680000000000000000000000000000 0xff75f9702bc01440f740000000000000000 :=
  endBox 95 0x9e2d072368b4d541b8275a80c278dca7dd51e8315476c27818aa1336b9cbe36bb30d63096365a84d47a07f8c3a01ce2e72f5e1a732c3416616337dad55033209d65302ad426c03786f798ae8f1413a0e5a9b2d55ace5f57a8c9f336586bd00ed336b174500ca3b3899cbdbc59018a2b1961e8278c393fdaa70515ab68072facd671d69e8982d5475b3155486a1b9403354d4867cd41cacbc75aba3689ff9ca6c252eea0e4e0a713500def17d5a9b209dcba6f75015e341dd3f28396a797d584b27e5ab68276a6b40fe370a01e85f5511a6ab459c7a7175a2c7d940cb30d81f36414a0256720c5414c903579ace57c735c0170dda0a543728553f2ba2b8de330d4245528aa0d9cb2d677aba90c0073964e66b3b6b39889a1e86e51d5cd6772cc04759da9253e7460d492d353eec0ab69acb49a3067dd6129cccdcb27e55e20c56ada00de2b88095aac7337aeb59debb2bcdeeae3d3999fa6399b56e7ae9ccd784a2ca1b1d682dc382f639a725dd399a51550301383f128ad679436e579ec6d5d736b9bda66d339ab6d2f6b3abc603dacfce66c3f4a2a8d5403286da66d49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def part846 : Box 0x800600000000000000000000000000000 0xff75d9c02b001400f000000000000000000 :=
  endBox 91 0x5e1b0571fc398b70da245e6b3a47ca2a527511a83b18059db1465a2ac3d492b4590455165f248548aa47490cd5b4a1b4ccbe3356d266d33581942e2f8ac3d8aed4d59f9b964fca45d606b2f6b0173359ce666f758cc9455aaa45e397949df46e165f202419251f293bc8d614263999c4d65f292521eb45284cd62e89e1c4e397977605f9ccd01328a65a7b05cf9a80937d97c5a06d006b053deda7db505b594bfe509293af86e99aceb4d474b56d416601523b56e6e13c285b56e305b54569a66356e6a4a3c5a6b23edede939697b56dab73544e66d4937bb70fa2f8b4209e5a6b53527650b28ab0051f03fcd4d4a1b9b4c028276a6cda3189e23c4a4e9d994528f35a6b4d66a7ae0005801262f1f4988e404cb3b499b58be288c51969a3e938b9ccda0232c2c506482fd87f358d267353d20a903064a7b650a9becbe2da358be1c4da0399b882a7414ca43468b4e521eaf32d9a0a6141a43e0ef34e60fa9156b39b2e50d9f6d2668096b39c0a1b949280983ecd535219f6d21e7db92666f7 (by decide +kernel)

private def part844 : Box 0x800200000000000000000000000000000 0xff75d140090004001000000000000000000 :=
  splitBox 4350 115 0xff75d9402b001400f000000000000000000 part846 part845 (by decide +kernel)

private def part842 : Box 0x800200000000000000000000000000000 0xff75d040090004001000000000000000000 :=
  splitBox 1 116 0xff75d040090004001000000000000000000 part844 part843 (by decide +kernel)

private def part834 : Box 0x800200000000000000000000000000000 0xff759040090004001000000000000000000 :=
  splitBox 1 122 0xff759040090004001000000000000000000 part842 part835 (by decide +kernel)

private def part826 : Box 0x800200000000000000000000000000000 0xff359040090004001000000000000000000 :=
  splitBox 1 130 0xff359040090004001000000000000000000 part834 part827 (by decide +kernel)

private def part824 : Box 0x800000000000000000000000000000000 0xff249040000000000000000000000000000 :=
  splitBox 4490 128 0xff259040090004001000000000000000000 part826 part825 (by decide +kernel)

private def part786 : Box 0x800000000000000000000000000000000 0xff248040000000000000000000000000000 :=
  splitBox 1 120 0xff248040000000000000000000000000000 part824 part787 (by decide +kernel)

private def part774 : Box 0x800000000000000000000000000000000 0xff240040000000000000000000000000000 :=
  splitBox 1 123 0xff240040000000000000000000000000000 part786 part775 (by decide +kernel)

private def part746 : Box 0x800000000000000000000000000000000 0xff200040000000000000000000000000000 :=
  splitBox 1 126 0xff200040000000000000000000000000000 part774 part747 (by decide +kernel)

private def part710 : Box 0 0xff000000000000000000000000000000000 :=
  splitBox 4227 129 0xff000040000000000000000000000000000 part746 part711 (by decide +kernel)

private def part436 : Box 0 0xfe000000000000000000000000000000000 :=
  splitBox 1 132 0xfe000000000000000000000000000000000 part710 part437 (by decide +kernel)

private def part248 : Box 0 0xfc000000000000000000000000000000000 :=
  splitBox 1 133 0xfc000000000000000000000000000000000 part436 part249 (by decide +kernel)

private def part0 : Box 0 0xdc000000000000000000000000000000000 :=
  splitBox 1 137 0xdc000000000000000000000000000000000 part248 part1 (by decide +kernel)


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem caseBBBBB (c : Nat → Bool) (hp : Pal 280 c) (ha : Avoid 280 17 c)
    (v0 : c 139 = false) (v1 : c 134 = false) (v2 : c 135 = false) (v3 : c 138 = false) (v4 : c 136 = false) : False :=
  part0.down c hp ha (by simp [Red] : Red c 0) (insertBlue (insertBlue (insertBlue (insertBlue (insertBlue (blue_zero c) v0) v1) v2) v3) v4)

end Case280
end PalindromicSeventeenEvenFourth

open PalindromicSeventeenEvenFourth

theorem OMA.solution : OMA.R_Green14_W_3_17_R2_H2_R1.H4 := by
  intro c hp ha a b e f g
  exact Case280.caseBBBBB c hp ha a b e f g
