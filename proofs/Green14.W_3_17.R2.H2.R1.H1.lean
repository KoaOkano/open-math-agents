import OMAReductions.R_Green14_W_3_17_R2_H2_R1

/-! Case 1 of the length-280 upper bound for the palindromic (3,17)
problem, Table 6 of Ahmed, Kullmann and Snevily (arXiv:1102.5433).
The proof checks a finite branching certificate for the specified
colors near the axis of reflection. Lean formalization by @KoaOkano. -/
namespace PalindromicSeventeenEvenFirst
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
private theorem part3 : Excludes 0xa0008040000000000000000000000000000 0x5dd94ca2f000f4201008000000000000000 :=
  finishCode 83 0x1f8751b065127eae338731701486005aa827857a70b403c2dd7b4b916723c1e4fc6b2959f8b8544b0eccdc270b7b4c0a516ebc88e27080985c2a2b526ba0d4584ced3d16e936c5ab06e4e16a1716ac2dd170b98e35686e4e162dd608cb55385b56d0122e1571807017c63104e839170c1bf38cb4c5c970b85ed291985c270b9ed3071d8c6e1a6f0b743967274903973595cc7072de46105bb0b850130af66adb985256ca280ae399e16eb52d00e28b41c9cc5887d1e416ea382e1698cd5b515b56e149b4acd7692f858b06e580641032d3d85ab0791ec969e6afc1e5acb16de16a8b759c40cc2e1500ff32d3d8230abd81ad51373ba8ce2902a3839670b393af8ca20a60e5b56e722bd85052d375a7cb23396b56c5c2ca168e6a8a8ac55e7e916e9cc550157cd511d48f65ccf2d2d882c1169b8abe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part5 : Excludes 0xa0048000000000000000000000000000000 0x5ffb74f6d09240000000000000000000000 :=
  finishCode 69 0x751d0771bc5201aab234c62dfa00e0fa70b393af8ae20e6413a91e7b7b56d03ab25404c83d592ac0817608cd3141cabc43973dc630ac4250b820b57838fc9e1733b9045c27350e897167b8a4ace6ae6785c27fd1ecc731419b6071f731cb137b4a874e62e576aca00e7b5b95d9c419c82d38f9cd520f074506682d6715435ccb1d40b8f4ce5a73552178393a004cd9ed2a096505c334c4e622e1961b398569ed3f40cb50d06f2c7554651485a7d0796afc1ac99e731694a0cd047290d439abe7fd6aea484cf83ecf53731b48e30ad65608cf53731b48dea727a5ec24cd398b50d98641600e8a87e373a0645c26e78e628174b154400b871cc5462a47571466c3d8b871850db9cc5ecf356d87ab253eed07d6989cc53df2d4543ad31398a3873151ccd5b40ba87cdceb038fbad57 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part7 : Excludes 0xa0009000000000000000000000000000000 0x5fd76ec2db4049200000000000000000000 :=
  finishCode 67 0x360c6240a424fd284d103adc20f4d7f357520e0bf398bda418ef698576f698576af789de6b951ca80c576833611b85e0182b02d87319ed22e162ccf6b5a4c616834ca4d5a8ad8919949a823854f069398a4665019cc5ed2bc330dc388ba031d06720f5677460548a731060c73141eca0305d9cc5067391d48aa391709cc554720cf654fbaccd07a82360fc2a7277a907314a07bb289419e82d066cb033d8a0cd816a4da30af6d4f096750460cf55164411a0f60df2785ed20b735c8b845bab1d9085211c40e872e277b916170872d1c5b0ec277ac7624f96fd89ef619a8a49f60fcf6762cbda611a9655abe2e1504abc56c5909ded4b9ee21cb4edcc2960fbdc45c2902f8f6916ed07d0a09afc732c594fac6b983e8b7683eb164faef67 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part9 : Excludes 0xa0008100000000000000000000000000000 0x5df576cad00b40810200000000000000000 :=
  finishCode 143 0xd8318901f8bc24fd5c670e62fe230e2f29c9cd3a81741caa03dd9a6e1bd164ca0b6a1c3dd6aeb10c8172606386f4f6b009cda6f61698a0ccb933105a7e6b90e5a065886519c4d180419bd8640e8accdde8079a4ad3f7b0b915c4591c735698c82d463d06d7b0b4a5066ce39158773594bca81741cbd8635ccd3f40c9cd4ddefe338aa270b0790661993989c7ce5aa43807357b8cc3735c8b8563a819736c12d83e9ae5ab683335cc8395e1a4b051dabaa0935c831ce62b5198b21cb063be8a4004e2f28d55ee29fd59aa8955eed29419a074e63208e3033da4f9a703398b1662e4831c37a731500d85719c3989b8e639ab2d4b1dba05daa3350d06ed239c8ed5d401903418530b8548b1812e4a0cd882c406c60de8b5650eb495a6328743973565a4a73199c650e22b1d8796833599ca31419cd2b381b28fa2a881d170cd5d398a0cce1735745c2c59398b307314a1a41ee97968c28eeda8b185983e1bd8e16e43989edc250b01ff47bac3b8fd283762c9724e1735653c31810dec6ef62ec2c962c9725ab70a328c4200d483a11040eac8a099ec6f531598b867b78ebe6a5bd8d64771a973d8499a1cb721cf530d68ebd896f5159abd46471fc403c837614cf6f504b13cd733dbd896c0307e6afbdbd0722e19a4541547b7cc1f3fea09da462e1519a9158c7a9ce656a8bd8dedec1f9ec2d2340b9ff5fc6e181b0b8541670b1c1ce656adbd4e59a8a55ee2817904ec02909c1c9ce2328cc7ba83985aab023871f906eb339ec2b3b41cc6165059cb5a47b7c2d50e5a01e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part11 : Excludes 0xa0008010000000000000000000000000000 0x5ddd576ad2004b480100200000000000000 :=
  finishCode 59 0x370c6300ce2c8c43da4e167350ddd07d398a93542283d0e1d07d5c11c7d0e3e833907aa1f583b51635f9f9e30ad8288d579ed27cd8c2a035ab673149fc6067229ec5aae3a1398c61505b357c33b18562214160c5e5508bda506682d254cc3362e9cc47bad5b84b30750299ed5ed25e5589c615cae94270900f758670b04bb293f381ce63e8b2203507a9e1943a4cd48ec616691cb73dc565e4ef6a2b57e0e7356e3028c769492e630a93f25ccd5f8c2b56d07a6c20cce627038bcac339216d82f0c41cc588b1f9d27e3dd41eb56649fa80e49f8b758869107a3dd98367119ed27e79ea21bb625a7dd286a2ca315199c2d01a82d419c7315e174398a91e6ada0f412f291d43b06f8dead3d04ac1f50061c3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part13 : Excludes 0xa0008004000000000000000000000000000 0x5fd755daf02040b60010008000000000000 :=
  finishCode 135 0x1d46c18c3f17849fc08ca3f873155148f39754562e137ab06e60ab4c5282833907a6e2a8d5b5f12c67148f0759c8af6f41b8af52173dbd8533906170b52dc8ae63627cc59698bf8ce2502e148cca0969bd06ba302e630b2a465282b1f9cc6d4b6419c7f17c170a91e46ab4c528318540bb56e5a7bd95232b1f722b28589963ea036ada8fd07a0bb627cf7158fb98da961939aca8334a0b52e0e5a80ddc4c02ff34951f24ef731b28c4293640bbd953ef18141ea0de4fbc1f438e9418deb18172f867d4072505782a204370e62385903ac2d2778f65ab698399660aac0d282b2f61ba5107d8fba83d419c6e338d5b0e5c2c9170a0ce40ea4ae52693bc7b2f6b83624ef1ec9cc58845160411a4081d920e8291ecb0a683eb90d49a81d8d72837a0e2907414a07560711033071969e83737ab0de620bdad3de1cb9fc5b11c170acd63fcad3d49af6995fa82359fad3cff307d94165e55799f260ea9fd398acfd012b458c0cf695269ff5ab6c4328a41d083d60103abe241e0d6c1f49de8373ecce65277a01e59198495a28c1b9a62c4b698c1cb730ce63170cb02401c79ed2839277ca3158fa0ddab7072d7c371ec720e54121ad523b56dfc72ec1ad41ba065c97391e302c15732ad3d48ac159ed2d456199ff5cbebe3006f59cba83740cb12e403bdbd3ee4ef9cc68096c194600e62c817966ada02565e3d983ec2513d5b56d3eaa1d2f2a4be170ad55ab7206560522bb8ae41d6170a01d0728c28243333d8c5c25c9614cf6f691c7d983c818e0ea1ad591cf716b2c1ac54ed5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part15 : Excludes 0xa2008001000000000000000000000000000 0x5dff7576d90a408bc401000200000000000 :=
  finishCode 55 0x2e0ee310ca2c81a783662dd561804715c52100e837485ca31264b13cb92c4f98b271f35cc0b761bb99c7ba809a0eae5d3de82dc7ba839608c2d5485b90630a3dd5205572d4586e90b16ab0de34ca0e416ea42b0800f75073209d21691d733c83916ac1de485bd8d6a27357b8b9267259cb5072827371cc099c01337392256a27e75838edd04e9f7720c18362cad256a28e39762df9cd504ea459a568395e14631c9c7ba727960551787316416ab28a4594669db83e8f2c3966ada0f2839627cc118c2a8c546680140b217258b22b18e1683998222b183eabc68c2a0e60fa2b1627b1761ee86ce7b4cf630e5c1f55e280741c9afe616936c39670b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part16 : Excludes 0xa0008001000000000000000000000000000 0x5ff75576d802400bc001000200000000000 :=
  finishCode 119 0x75188651483a107ac02075fc590dfb13be0fa93d393bb8b259012f67277a0dc2cf1715ec67d97b5bdbe4f08b747ba2dd876e8077f11c8c2cc591ee8b849de92b661701eeb916619b994e4ee619cc6b3538ca026385b4f5a630b747bab82a8b23482dd4fbcd2335db56d82a8230e5b0de58f866dab71850d3a38c4f98b2d5b38fa01d06e839906f20e45bab2318b23989ed31277869c38ef6985c2d5b411abc67b4abdc76e8236ada90ac3f83dd590e17278502ed5b48e9ff4e328e1ff6837b97504ea338a87b8cd5b6a8c7199ee22c9371a455076f205c99ed5b519a40d518b2ec1b7b19715ed2839627c7ab6a8a0dded3205dfc7b1cc2d522a0e504e86110d659cc6e457249ed55e6b35561696f69a0eaf69986ef6998059148550e167274fbc1b3401a0e64705c3356c34e72d41b8b866ad9cb5072d22a8e639467b4c6145c2a335c11c620c475736bd45a7b07538fad2672ec6156a22b19ea2c5d6ada0267a8a0e5013356dcc403cf6f6a5a00c5c2d22bc6403b12dab73b8ae1b88e34880740b9b9e7b1a8c54663dd81162bd511cc5505bb28c5466b00b765998b7605bc8397a88f75692b518c2c3dd5b104e83916ed0797a8acec5c2d65870aaa0f75cc69bcb4b72eb5953c6a457909df2d25676e5d730d07d046c1e6522c3dd (by decide +kernel)

private theorem part14 : Excludes 0xa0008000000000000000000000000000000 0x5dd55556d00040000000000000000000000 :=
  splitAt 4342 133 0x5df75576d802400bc001000200000000000 part16 part15 (by decide +kernel)

private theorem part12 : Excludes 0xa0008000000000000000000000000000000 0x5dd55552d00040000000000000000000000 :=
  splitAt 1 110 0x5dd55552d00040000000000000000000000 part14 part13 (by decide +kernel)

private theorem part10 : Excludes 0xa0008000000000000000000000000000000 0x5dd55542d00040000000000000000000000 :=
  splitAt 1 112 0x5dd55542d00040000000000000000000000 part12 part11 (by decide +kernel)

private theorem part8 : Excludes 0xa0008000000000000000000000000000000 0x5dd55442d00040000000000000000000000 :=
  splitAt 1 116 0x5dd55442d00040000000000000000000000 part10 part9 (by decide +kernel)

private theorem part6 : Excludes 0xa0008000000000000000000000000000000 0x5dd54442d00040000000000000000000000 :=
  splitAt 1 120 0x5dd54442d00040000000000000000000000 part8 part7 (by decide +kernel)

private theorem part4 : Excludes 0xa0008000000000000000000000000000000 0x5dd14442d00040000000000000000000000 :=
  splitAt 1 126 0x5dd14442d00040000000000000000000000 part6 part5 (by decide +kernel)

private theorem part2 : Excludes 0xa0008000000000000000000000000000000 0x5dd14402d00040000000000000000000000 :=
  splitAt 1 114 0x5dd14402d00040000000000000000000000 part4 part3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part19 : Excludes 0x90008200000000000000000000000000000 0x6ff1550cc84cc1041000000000000000000 :=
  finishCode 83 0x1f8721987007ea3fd6c103724c476e5e516d8795ab73d452523b72e18b6c37f356cdc6c1ab6b01d0a25949a5c585c6c3d51fb88620b8cdb7302cd72c530ddc4cd694b0ee83bc60cd72371156acf508461ea2297266c9171ccc6e75a3bd8e5c1b047147f293528512c60e1e88b8c99a0aba0f629787320ab6aec4cd16db28ee1e82e36c147f29350370b6e157cd5b41d8abe6ad8b6da05c1944405c6a0356d47f171547f293477b24edebe91f0e88abe0e8b28cc34896031586b358c95aa25523c61669786ed44ad5b59114584d1852e5a80d6724cd791a631edcb52d5b52696a66ad9f7635ca4154062db526ac0a25949aa038db6d5d523b56d64501585a78ede58fa8cdab63bd6adcc538db62db877ad5b1d1946adbc81bf15ac5c3605b0ac5b69e396962af96015ac2db0dfcc53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part21 : Excludes 0x80008200020000000000000000000000000 0x77b1551ac50c430c110c100410001000000 :=
  finishCode 69 0x7e1b8821c86203dac598ff23f51febc8a338c23079170c1e6308a06584791586adc2e141aa0ed6c4005c29198dcec29495cb4f6ada01e4839845036d5b680c22c599aa680983cb166151c2af6adb60e43481d95915850104ab319aa707b5198b25256a319076a039166aec1ed69692b523ca1f730b56c5930b3d2571fd5586adc2cf40aa0ed69720e5036d5b7116c3fab54e7b8a0ed256af3968ed6335ccc0d593a064fcab0340c017e63088f65032982302c98bf26118593075870a2cf6ad8b8614ab56da92d636adcb0340b83903d9170cb0f413874455f314e69f98460f22bd9a5e1a56ad9845a4451a015ab03640bb56cb86a47348cd5b3fba4adabf205c3a2a33523b56c3a316a5ab6817 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part23 : Excludes 0x80008201000000000000000000000000000 0x7db5550ac28e41079009040200000000000 :=
  finishCode 81 0x821f4711dc70164309c62b600c52802c16494accc80a81950fcb2523fc1e50723fd5a9c36b7b1b56c7fab23108e0b8c8cb20d49de919012c2a340da4bd63e825471887395cbf6a23dbe1d59fad036c4da0f28257a8bc8b820562029fd560e815880aaf13fa922683c9f9cfaa0694828ff5986e10770f95606416a72bcdcceb4f2f6a3907995f6d5b5a9a31e7b1b10da72b1b853a4ef948acc310a41015a0151cb1b50f97b5ab6b532f6cd5b50fc8296adb41079943ed5b2fca0e4927278c9df0a2dedeb536adab0a23384ef55016ed5b9072c25055a0e640ace00fd5caf0e2502af5140c8ede7b3a4a5262ce3208e0b8437f1f9da8b06fdcdb3dc4fce8391db8a766e1c4661705705c64ef815a5c5858ad5b730a8891989de83b412c93d171c1bb411052d5b968ea1f497cd65697975e471a4656a64ef (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part25 : Excludes 0x80008280000000000000000000000000000 0x75b95d69c20cc1445540000000000000000 :=
  finishCode 57 0x821f470190314c62b510c26f2238d028fc11b2bf5ab68396abc5e53fbb56d586adb0f669cc61433ab13594abf68c286360f6b56c3db330dc310b20f947faa3f9422157171ac1e155bc86c206c557356d66681540074f2ccdab62ab5c230b164dabe7e78b2680356e155b007e78b26d5f048979410b260b01fae69ebd4da72a255268635887356dab72988e395e1719f9cbf6d5783764cd8dced5b9cae1ed0cc8675b85616070198062ca255268ef43a21d935cc4cd171a0a5ab62e3944a4ef6ad8f1630b20ed23a2e3497c7fb6ae8b8dab64ef9ab6a4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part26 : Excludes 0x80008200000000000000000000000000000 0x75b15589c20c41041000000000000000000 :=
  finishCode 121 0xae3f0731821c86203dab62390a0b8e5019b9c9ded5b51c90155851cac83e52fdc5e541a9ae6373c7e741ac2e3202c8e206dab7395cff66e746bca458c2b56d5f2ee320cc18ad588c1c2e341aa0ed04157cd5b40da936171a386e78bf64db3f3a9344b31fec556c4d5128abe6ad984d44b2935076ac2c8cc13be41287645c683b6d143b460d23a2e30df9ae65c03b324ed47e917403c8154fea8adab693b9ab62e3821dc640c5318ac4af30ed6aad534829fdcc26cc340e42001d16916450eb56e35c86fda625c39ab66b9373cb1d9ebed312e18abe8c1cd65501b16dab61bf697a80e523b54cdb6cc2e091785c60b961ec81750eb56d43e5c3061a91e7e2086e1a0721880f6a8ce50e8b8c7ba3f57914440ab95e8c1b56d076d599cda6e39b61c2b56d6aaa1f23dc23372bc604faa6e7771844614c41ab56e005933cd72d3d59497ed6aa613254cc5b58182fd20a62b515cd5b1ec8b8d076d5b85c69fd923ad5b41da0d66ad87b500ae03b8a4d831ad3950eb56cc266295b2307354d4562e13eecd5b61ab40d5b87143b1fac1769fd5239fae05da7f4dcf241dac6dc230a3f9076d5b40aa880c385c6d5b41da38e8c18b8c36aa1d9ab6a39526b40c4370c80326314874500309c9f550eac86139ab6d3161dcc3d515c1f64fec60d3eaa1d05da38630998a45c317b4c52d5b (by decide +kernel)

private theorem part24 : Excludes 0x80008200000000000000000000000000000 0x75b15509c20c41041000000000000000000 :=
  splitAt 1 115 0x75b15509c20c41041000000000000000000 part26 part25 (by decide +kernel)

private theorem part22 : Excludes 0x80008200000000000000000000000000000 0x75b15508c20c41041000000000000000000 :=
  splitAt 1 108 0x75b15508c20c41041000000000000000000 part24 part23 (by decide +kernel)

private theorem part20 : Excludes 0x80008200000000000000000000000000000 0x75b15508c00c41041000000000000000000 :=
  splitAt 1 101 0x75b15508c00c41041000000000000000000 part22 part21 (by decide +kernel)

private theorem part18 : Excludes 0x80008200000000000000000000000000000 0x65b15508c00c41041000000000000000000 :=
  splitAt 1 136 0x65b15508c00c41041000000000000000000 part20 part19 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part28 : Excludes 0x80088000000000000000000000000000000 0x66974ac0c44440000000000000000000000 :=
  finishCode 153 0x821d86e1481febc03ed6d1c0314c62b41983557448bcb3d49fbda507a2e3901a90d49f97660f6a91e4f0a0f527e629701e06d03ba1ed49dc0d5277c629927f3da594451c4411a0cda45f08267318c52f63967293f315cd5339882de6ad9cc52859107ae224fe398a8c5ed26135c230341a5aa65ab6ada8c4162b059ecaa316ad9cc547f356d462629398c08d818a62099cc564f104da96613501c607315ac0a417e6308b18d82c893f561cc730ddaca8e18b47181918f06b622b92d86ed5b560f933164152f696a8b97e2d1bda5c8727a5c96d5b6adcca268d23604034a0e62dc20f4d4317153c2823518a47dec72bcd046a3149fc0bb065a87e05397bd48398a0ce5a997be7b4c1ce2ccb16543e93f0de900ce62a21506e360d5b60acf692f29ff527ed2340d4b960aa0b523a10c29989ee5f60abd8cffac5d5a7c179918e29d7b4ad4d2060acf693fe979527e84228c2da302d5d5919ff588aa42b07fd15bc48135db13daa2c29964eb3135dc7b1463ad3e6c16049fa30a430de350a8c5aa2f6315bac8ac30de6058705aa2c4f91e619f463cb5160f87058b3181267a70c3d966ac1b612c5ab9acaa0b519a309c133d245820f72d2da6ec25149966456eb47a302d53838ac7da6e0099aa6475720acf563ef539a6f41de3023b77b7a87d696ac2c0b82501bd61ec8f35239ff53c25c51ccca1f7b09f261d68add4671ff4b8ac55518c7c93febdc5662e0388ec370c80355640ecb2873198825d7171ab0a2209585b356d882e6149fc1c67308a55ec735758baf71522a87cb6324c5882ac0f16723a8fce6281541da4fe8c2a45d47e2e3398b284ef91c2a3f6ad8face62d498bcac2d6ada4fd7049f9cc5603e4cf612e28f660ef315543ed2f96962b70ecc93f398b4be6ad8b0527e731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part31 : Excludes 0x81048000000000000000000000000000000 0x7eab5279e09240000000000000000000000 :=
  finishCode 49 0xdc338b2290b831072739aad3e2e2a05d03a0d10e8a05e698a435cc760c2341f4e320cd06a871e0659c651a3307cffa71940eba0cc0345380658b06396a08be20e640ba8cdac71b6cf96d5b7b7c5a36ad86de3988fae6d1cc505c4cf2e2b51581a83d0669c7c1aa839904e0c52ccc8f341b9844e3eee320a432861106ac3f3416b046497b1541aa7318c3e0d52e2c6133f69cc41aabc0746398a4f66a2933cffa82d651547307d6a1d9ab673141ec8198176731314a90d5b691c92f2f68ac51f2a479cce2e1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part33 : Excludes 0x81008000000000200000000000000000000 0x7e8f5245c49040500040001008040c08040 :=
  finishCode 35 0xe23b1043c8bc1055887007dac818ae30e8356419ce51701b4314c61306ac1ee725abf4e0661139ac93170121b187c1aa8e9926283d621641f6987e4169c6505b2c86138e4e8379882f674fb9fa5262a47700e631fe41aa1d94e0e6271f902ad2b94622e38c0bdbdcc3859cd5417200ce62b299ede5874018fb6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part34 : Excludes 0x81008000000000000000000000000000000 0x7e8f4241c08040200000000000000000000 :=
  finishCode 149 0x3f20849fbb102370e22f04156507fa7118bf673150fc4cf3fbb80de2680d15b0c267118d7619f48e9c46140b06e396bd9e47c8774c269318bf63f5881aca356e581a504bf2a17398904d78504c2e12fcb56dc83306e0d66f53f5a90dc388bc310e00fb507b18acc3a83d9945f1c02fd835649898a548f395d89b18741aa6119ca20d1701e039ac82706aa7be50ba3ec19e61f47dc9311f6cca388a617ee41e984d42f25049df23e641ba505b8711c06d194067970e0e3a4a4d33168da7a8f3471c7e7620b56e0f6837479984d64411c72d17197ed277168ce3e9ef651a0501a38e4948775253205e6adb28a1783965c38fae8e1650e33071ce5a4033989bbe83ba7ddcda72d40baf09439ab69058c2a7bcfce81b398ac8a0390163eb4f7ca1706ac10ec3c902388aa10548266db967e1af2779c7cc5318ad03b24bd07a5f9398bc0bc370e2380c829081d81aa62b6ad9874c5303549df03551ab02fd44ac0d6ad9c0d1c728ad68a93b1f6b88c8356e497872cc56613985683d0e5a066277b80dc1c7e41ea434c3e0d540cc61362ac6f5498872dc4701605e05c324ecc3a6295311f309ad1f60c730fa45e485a076315831d646d121b17ed07a1cb50ec5fb512c931277c93b2fcb88e02c8629068c72730f9cb51f724c418e83d92767c51609c7ce5a7319ab65f90eebc8b8100c1731cb4e3313bce5b368aa3703eb0ccc70306aa8ae59393bdb80ecc0d5398c9ef50193bd40277a01648b9b3585a731366c917 (by decide +kernel)

private theorem part32 : Excludes 0x81008000000000000000000000000000000 0x7e8f4241c08040000000000000000000000 :=
  splitAt 1 81 0x7e8f4241c08040000000000000000000000 part34 part33 (by decide +kernel)

private theorem part30 : Excludes 0x81008000000000000000000000000000000 0x7e8b4241c08040000000000000000000000 :=
  splitAt 1 126 0x7e8b4241c08040000000000000000000000 part32 part31 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part37 : Excludes 0x80009010000000000000000000000000000 0x67dd6b28d3004b282120200000000000000 :=
  finishCode 61 0x811f46e1c876161f28945c640d20eae8da4616398a08d066403630b4171a4fcb47312c1732d445c71f5ce62c4b1489cc661127eba2d2e7b49b843169fd2018a167b48a167b4a7f62fda08c80673161160691286b2310ec02adaa74614776d5f41d82768c29f6e0e292949fd1852d3a0ac9decc348e8c2b55dece3f53d0db7461498e9296abc7318c293be6c09df1f6ce62c1b894e2c5591b58d077185277a4fe1fa9cc49de902b093f470bf73da49dea63db60d9b095286f6d85c66db7b4b48c224c605f872ded3280e416ab1185a0e294352382ec9dec23103b79cdb1857b8bdb5672a4d50182e56472bc5fb498ce67523ce3b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part39 : Excludes 0x80008014000000000000000000000000000 0x778f526bc220433a01102a8000000000000 :=
  finishCode 43 0x2f054410d5b5d14805dc8232019cc507b02460660a900ce62d2208d463291c3960b191c293f480ec49fb54e0d8b58dc871cc501af6391c20537a89bd4e62413398c3eb811a4821e4277c93f2019cc4826e624073162127ef63900683305d9bd64638aad1f2b5546aca0b5189bd527f287e523a8fcb868cf39893bc7d673194c49fa466277a08daae83d2fdb0ae41ea286f5927e7b37a8b0cd18e4031d9a08da481120463904ded741f507a9f749fc1f641ea7dd3ef397cbb26f5723871c396d638bca5fb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part41 : Excludes 0x80008010080000000000000000000000000 0x7d8d722cd604438805c0205008040000000 :=
  finishCode 95 0x408d8398ae39073185188821a41fa905544b41c5866d45266c93b839a40fa0b0518e93f277c7c31f5b516501a4ee277a06e4820f71ae52165e549f9c0e494cd5b49fb910a3b0c42e08151fa815e6aec60518ed5750fa8c5a8a4ef9aaf395d02afa2505e58bde943519a8c5633231e0f6a1f6aeb174806d5d98ba5c54a19b9e50ea0545970b8d27ec43e89c410900f9483a2e38bca93f508c3637b7b0ace064db878ac452f2c6066aea4fc7d6d5b20ea4fe272b0ae20eb95d27ee43b10a410d20fd483ac339896d5f0b8cf693e6b95ce06a23e8b80fad81b46160ea5852779c0d1ea2e38c2cd5b7b4cc0d162a31c9cae518feaf692c2a094596d22e08e0f9650f8b8ce062a3a302c337b18f95aae49d171ab0b23da641dbd4e36d936d866f631f2b0ce625bd84e073e8d239b6463c1c567307b4a18fad066a1f494c267277a50dab6f695a9a50e6105170a64e067eb41d8fada7b231ded2e4310da0fb57461107ad5fa30a703486a50d6233da630b0b8d27ed43a30a5d95c1cc6adc5e3736a435286d5b91aef6972ba8ce72ba4fe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part43 : Excludes 0x80008010001000000000000000000000000 0x65bf562cda2843180308230021002000200 :=
  finishCode 51 0x82214791c8388c93f20a90753fb24fc816e42e0c42688c71fea4fe731a08cd730b8ce22e630b66ad9c45262917619c93f388a87e49fbdac7fa4cf9ed293f6ada4a520ab8238ae17ece22f539866e5b49fad44fce8c2d4640ac1c662ea7dd3df1837a9ac1d585917840ac73162d8f9506af6998ba1cb51186724fd43b0aac7ca80b85c7185591440e5b54e609b174376d5398263638d727e747cabc56526db1f2ac892348d828873149fc7fb41d872e578a9151c682562024720952321cb171a91650fa0ad8170b8ded2731171ca47902a731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part44 : Excludes 0x80008010000000000000000000000000000 0x658d522cca1043080100200000000000000 :=
  finishCode 143 0x318b82c8c41cb4e6ad0250e1f58acc58a1af83967fb92629c36071f5121449fa989424ee4a19796398a4a5786aec5e548b86656a3245d78152c5e539882fe2e0b1745828c7512b990a298b079ee2415494a4ec82b176522e695a0f22a50da9794e62d3d8bb2ec330fa20841d69ec4cf05bc49da302f69839b56dedf1856a28fd5a7b10745473d8c807103e8c42c1d784f1cd5b594a08d2763ed1fe933e4fba08dcaf200d46718348bb48b3d87ea9436a2b57cbc410fce93b960ab53494d185720c399494c615f47618820ea31e41e8ff5007245d18ed5b419c3f5967ad456afa58b2360719871a449f86be160b56e2e1a7bc9def6920a9ace405905483b04eda5e7e3482b56cb96f690e3b60a244093f5e09b6d5b920a4155189cc544b105518e415a0473214821d82f2ce453e6a0b518e3fd4829054bcb100d1cf28c543e731518c25940a9794e623e5905a9f79ecef69736a0b58885118f39147fa41d411a88c339896d531f29b6c9b66db9aa6d637b88f951f30d8dcda49d401a7ddc8691448118820e8aae7b48f9417ea4d405c93f2fdc83d48cbda49dea118e6241d7b4ac1647aa465ed24ef20ea4fe59148760e17042c0e5228b8c83a3ed5f125f12ed04a3eb171ace67b4c604bca93d4128facb9b1cc50667ed171c00b82f8f20b8c9df460d0464032f7cd22e8a00fada570ff5ab6b4b6afc9316ad8ff4817356d21b183582cf6b4a19075ab6731471ed282383269052f793bde43edc9052c3a02c80690587fb17ecff704408cc2e83fd4d099f1f9ded2d536ada0ccbcb100cb8b356d01a4c58db6a4720eb56ded3208c7daa11155ca3150fa054e62d5b (by decide +kernel)

private theorem part42 : Excludes 0x80008010000000000000000000000000000 0x658d522cca0043080100200000000000000 :=
  splitAt 1 96 0x658d522cca0043080100200000000000000 part44 part43 (by decide +kernel)

private theorem part40 : Excludes 0x80008010000000000000000000000000000 0x658d522cc20043080100200000000000000 :=
  splitAt 1 103 0x658d522cc20043080100200000000000000 part42 part41 (by decide +kernel)

private theorem part38 : Excludes 0x80008010000000000000000000000000000 0x658d5228c20043080100200000000000000 :=
  splitAt 1 110 0x658d5228c20043080100200000000000000 part40 part39 (by decide +kernel)

private theorem part36 : Excludes 0x80008010000000000000000000000000000 0x658d4228c20043080100200000000000000 :=
  splitAt 1 120 0x658d4228c20043080100200000000000000 part38 part37 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part47 : Excludes 0x80048000040000000000000000000000000 0x6fab7270ca9240248230009000008000000 :=
  finishCode 65 0xdc2e0aa44071f396c00de2688094fec8036a98f664fba7de5a89fa541717b4c52afd81aa9f7419a90d81c9dbc5001aa6b99abab1d4fe9cc4c532c753ce6b95e16333dccb7a81d6ad98760df210942cccb1746160eee637a8a47d03af739ea307714bbd8cb7a7b7a0eef736ad968dec700308d82500d547dca394a1987e0e5c6b958ea4c4b8b398d0326db7b1bdbd4720d59646f07d67196a4c941501b49507307d9a4a7316ae987e08641d8551ecf41de30ac554fba0cc5b6de18a589f20a41ab06f981712cd01a833267a0f606a81b66948a05ab2a0b06ab48aa4103eb641ab70b85047460e51f9cc5ab6b22f85d790321cb309a406b99ab6809731ca39723c8093989cc6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part49 : Excludes 0x80008001040000000000000000000000000 0x6dad6252ea1240238231001208208000000 :=
  finishCode 117 0x852087d1d8550826c41188234199aee6ada78dac614f69e93bd416e459a72d5b170b98623a924cfc361e052188731085a98646730ac6dea22977b1d1859a7af6340e8a5e7a8bdbc52f356dec6f6f470faf165e0ef18572381ec9de700e66730a434dc30b86202d1a4162fca0a5cc64ef732ce63360b8b2c14f528292bcbd8dedf1017e60c69ae505291f88072a8e23c0c62c8f6f9ab6d392779c7c396735610e3f0b6dedf356c9de71f61148581013356c5c27cd158ad1e0cdc1cda47302cff62db331ab64c790326db11e896d02f04c4912e632bc92c5d8611c8b39849de3bb3fd8b6d64277bd86370923c3268fb9ee218769e82763edb4e584ad632778eed60641cc5f05b64a78962e4589ded3d8bc2e639ec63736ad93bda7b279d21ac2562ab4e5ac68e1e8e82304ef42122f24a498ec229869d9ec63b7494a45e4f3bd8dec741de263872d7c170c1ee7b1a3ed852c59731cd5b582bdc60ee4ef960731edf0e64dc2929170c6161ccbd444f2d3d8c2cb62384e5836e3eb277b88aa2c03eb6abc80939aa50da7334f67319c66005813cf250cfd2829505ce61258c5d78d72f734a18faddc7d1d8550c3e2e387964db85c672d83965ef63099b3d84396727162c4db39ac70b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part51 : Excludes 0x80008000048000000000000000000000000 0x6dad6a19eb5040208270c01040009240000 :=
  finishCode 57 0x110398bc281001cc5a0741012dc3685a03549df0f65a722796b1c3d9139cd390f6a7f481734e5ab661da146a4c7cd597900dab6ec460e308b52542ea392f7c70b06ac6b92d8b56d86e629581f430ec40b314b086cd85aab5526d8b843db289419f0354c56e8400e24282e35809de3eb512ce633f6b58d20b06d8e17033da723cb26d93be697a08d44a1ed30fc3b13e3b13d8b22cb26da0b647da0a4c3ec4f8203db41b49de7ed5811c385cd5b51c9c2e6ada89502f04f5256d5b385bb0e43e880d899e41d781cc6adb4be1e8835544b2935aae7cd067cd5b944ad63205900e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part53 : Excludes 0x80008000040000001000000000000000000 0x6dad6251ea8048202a30001048008200030 :=
  finishCode 69 0x440e62f1041cc614641f43fdcd5b2f687b4c5241d413ce636ad93bd4722e1515c41d0f69cd63159c443daee1ae606a9fee5159c4608851d8781dc0f6b88b61074c3e4778f8ee617b3b13e30ac29272bd9e5520e7067c36e4cf6d230b0edd8b2b3d1dbcc4f38cc7358399075c4834c4ef30fc004a7876f069277a80d2830edd70201968e38f925661bc1dc9de5ef899e1ed6d1640dbc9410e5acc638fb1541aa7119406e63277be904370a03a0d25a33f69fec83a4ef0f6b104134a0ca032fcc9ef277ac65006981cd68348facfd64ef403c8f941ba5049df3e8ec39841d621484c0dc501acf5cc7356d21b24361dba80d622a0390074615ab62db263cb190dbc615ab64038e5b1bf5ab60cf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part54 : Excludes 0x80008000040000000000000000000000000 0x6dad6211ca8040201230001000008000000 :=
  finishCode 91 0x88127ea0398ae3887315c208551383ecc71f39697be3099cd504700187e692a0a43da7ed9a4af7320e9c9cc3e3c159ec829393c29043b061f91c671927287b483ade100d3ef1c6499e8392779c66692a78cdb6b236871962acc3b1f5825e0d7b4949cb20a542f24ac9b66cd6d09ca1ed62cc1b7495933e62cb4a5b859170760e4efa107630987b6411c5ef69c9cb5d838cb4fe6b1a38cff60d50f69fe659fb50dd08003db20249de2cf8c524e536dc71f20eb56e277900db8761c40f69c0b82025abf13bd1ae73547cc92f8ff670b3939a7641493be3ed8face16735821007202482707791ea3eb404c110a4009318e3e2e120e87b56420ebb84e58d467fb3159fee351bdcce330738c524e5393c61f36d87b5644b0dfb1c9c99b23e4d7273535cc0d5761c40c2c4cd6ad9bf5a4673506a9075886f1384a1cd3d51fa89584411a4a650bb155a7320ce6aea07554263cb130cc8e8c5b6b5587a271f9046403 (by decide +kernel)

private theorem part52 : Excludes 0x80008000040000000000000000000000000 0x6dad6211ca8040200230001000008000000 :=
  splitAt 1 72 0x6dad6211ca8040200230001000008000000 part54 part53 (by decide +kernel)

private theorem part50 : Excludes 0x80008000040000000000000000000000000 0x6dad6211ca0040200230001000008000000 :=
  splitAt 1 99 0x6dad6211ca0040200230001000008000000 part52 part51 (by decide +kernel)

private theorem part48 : Excludes 0x80008000040000000000000000000000000 0x6dad6210ca0040200230001000008000000 :=
  splitAt 1 108 0x6dad6210ca0040200230001000008000000 part50 part49 (by decide +kernel)

private theorem part46 : Excludes 0x80008000040000000000000000000000000 0x6da96210ca0040200230001000008000000 :=
  splitAt 1 126 0x6da96210ca0040200230001000008000000 part48 part47 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part56 : Excludes 0x80048000002000000000000000000000000 0x6feb5634c4d240000d100c0024000001000 :=
  finishCode 85 0x338b82a8a41c7db069c9cd5ab72d441aad5b9c8ab517a8b56e1dbbdbc1a2d394b164800e4ebe328a399aa261f171c40d31904e3b79a62e4032e4fab59624d8abdab60c78c3ec8360de0745abb1ff60d290b40e835406b3985ea29f162caf1102d266adbd8d3ea611695cf6b34fbda5ab6e619cc69f5903a8fb83ebd441aabc3a05c585c61d183bc5956a59675672a09266ba11017163fea7c52320d5903ac4f8b2a61f59148420e33101ff503b07d9ee24ad9ed2f6981a29e1621b56c1aad83490003449370abdab68296b1cb4b266cd5b7b583556130eddbc7317806a8ede6209754c52d5b730c69f7a8c1dc99ed2fa0ee7b73feb10503a98250c41728c7ed416bd9e419bdae77178591486512826117b0cb35398bdc6650e6318ac7c06acd377a9bdc41ab3dbe6adb0a41aa6114d194691cc294fba31d04661f723ce6306acf5348c9c0c99f2844bda703 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part57 : Excludes 0x80008000002000000000000000000000000 0x65cd4614c450400008100c0004000001000 :=
  finishCode 91 0x851c8811e47407ea40d0f2c1ed06ab57e2f2b164e07100fd5d0801640f6b92662cc1a52324cf30fa505547310464c5899ec15892a49d3f4b16521723edc8aa4313e40ea0b5216d838882398960d17b1c7b1463b10499e4cf908040caf741197955ef313ce3e2e39a62b055a98795e05e03da4ad8bb2f694f1acc4e3e3ed651ed320cd3e261f385cc593fbbe8bc2c0f6791f6b0f838a785046a1730298a527f094d406907315ac04ef949a8e389de61f1f6c4ef6319c49fa90d6389de9413859c9d38551aa71cb503341be309899dac6f695f1853187daaf2016205e0e63356cc56da187e0fb41dd61a92b370a505ed327c45c7358dd06c1f449f87b50730b8cc5670b9947d21c26d98a4c3ef618d5a7f77b7a0de0ee4c593862cc71f26d8f94feaa430de7b8b1056a6461876ec3726dbdc58533dc4feae41c7d607717c7d164414cc596a8987d27f18a5032c4f4f8bd4e393bda582281962c8f964f8c727393c9f18fea93f (by decide +kernel)

private theorem part55 : Excludes 0x80008000000000000000000000000000000 0x65894210c40040000000000000000000000 :=
  splitAt 4753 126 0x65c94614c450400008100c0004000001000 part57 part56 (by decide +kernel)

private theorem part45 : Excludes 0x80008000000000000000000000000000000 0x65894210c00040000000000000000000000 :=
  splitAt 1 102 0x65894210c00040000000000000000000000 part55 part46 (by decide +kernel)

private theorem part35 : Excludes 0x80008000000000000000000000000000000 0x65894200c00040000000000000000000000 :=
  splitAt 1 112 0x65894200c00040000000000000000000000 part45 part36 (by decide +kernel)

private theorem part29 : Excludes 0x80008000000000000000000000000000000 0x64894200c00040000000000000000000000 :=
  splitAt 1 132 0x64894200c00040000000000000000000000 part35 part30 (by decide +kernel)

private theorem part27 : Excludes 0x80008000000000000000000000000000000 0x64814200c00040000000000000000000000 :=
  splitAt 1 127 0x64814200c00040000000000000000000000 part29 part28 (by decide +kernel)

private theorem part17 : Excludes 0x80008000000000000000000000000000000 0x64814000c00040000000000000000000000 :=
  splitAt 1 117 0x64814000c00040000000000000000000000 part27 part18 (by decide +kernel)

private theorem part1 : Excludes 0x80008000000000000000000000000000000 0x44814000c00040000000000000000000000 :=
  splitAt 1 137 0x44814000c00040000000000000000000000 part17 part2 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part62 : Excludes 0x80040000821000000000000000000000000 0x6e5a943955a89211c24e0320490c1184200 :=
  finishCode 105 0x1b4791f05e1cc7405b6ee390f4391635cb4fd69e6ed72c836d607282cdf6605690c7037b4c1e471eb29302acd54631c0cbaac554ee80ddee26ed7a13809acf7162aacd5cc3350cbbf3d0322bde4039814ffab0d430c0b2ce5583616066056068a3e7b4bdbcf6f3da5c8f05051faee2bf65a4861cdf6e475949815ec73a07835463769beda4392045a0bbed2f8e22e613e5c7037b485ee7309c0d8ab07d81b6d43388cd435a8a3ace4586cc23381b154bbeb0d98849158431876c534f11c72cd07d3e3b4842f66fb0cfbda66949bec136e596aecf691deb98c7166fb267c28b59d8b0c77ace2985df8f6e8fd26a93a53d30b0da4216f9ed2d61473bdc5a4391d433181b049dc8e6d90ad933ded27fd2efac1e724bda4ffb079877ab291dec7fd724cf61606a01d24400db301f4b42cbcf693768e2c6cf35760f2f690419bb499f2ca51d69e3e04a55210c3029b7e5819c451d6b4f47ec5bd581ac364799ede72fa3f56068077c0b469166ab039ec659747e96bcd7317b51d6711302c19547596f4e230239266b0a3ad1fae459a627fd26aa3872420703541ac323f5ee3060dc8e9dd274cf616b09814e2334edac2bc277560f04e56724cf302b4fe583b575cc24e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part64 : Excludes 0x90040000820000000000000000000000000 0x6ffad973559c1015c84e802041041000000 :=
  finishCode 51 0x5a1b8621707c03821cd499c7fd37d9c7c58f378a82b8d22916523b0e4ffa9334a2a48af796962db26ab0e67b49907dd98aab1f877a8eb7c1cc58fcafd83eb9145b60db1dece47262c6fb2d4c7fd541bc5d120487a4cd68b398da965a937dcb0359ab4c4e4f0a3c7a26fb06db95e83abdbdaae6fb266ad162679becf0481ccb1bb568a5a9628ab8ba06c64758b1c293359472e1b137dc1ae0d8b98d201638b6e6b1a3ae83586c581ea820070393c28eb7b4a8c499adc1f2e62a9c9c1b6c51963ed3716d836e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part66 : Excludes 0x80040008820000000000000000000000000 0x5f5ab0b75d9891d1c20e046541441000000 :=
  finishCode 23 0x7c1d861170170aa83d9393a39e118b155ac31ff630734b5ed2e618317038cb4fe519a825c8a4e91ecb4964fb9ff65198725412f619c76d5d7b89ff4e32ac2f0d2d826af71692b155a963a50dca484e99a4ac5383acb513ecc1f5cb29dd732a784cf731c4e92e18addabb0735a429dd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part67 : Excludes 0x80040000820000000000000000000000000 0x5e5a903955981011c00e002041041000000 :=
  finishCode 155 0x1dc6715c4f106f20e610481a4414a28a207262cba51522a2e12ef8726246b915c8e7277b487264f4aca49be933170bda584f3da58a23d9691447205c3036cdf62c7450b5f133cdb25df3c09d3314daa2dc39b67b6890ce5ac53274cc43b1183928ac0f6928735aba4df6a3cd478c0adc1d06dfa0fad61607c71f475c6f56079b7ce4f1815052f820070418819551385c0deb0b84e3eec398e5a598160fb2c7dcc728c4b86a47504cb03475b4c41b707363938b843a31c9c5c248991d6e636a5c20902a0e83e0780f65ed330fd28ab4561c9bedd46a1c0db7b48d9658fb8f528ac2783cab8e4398634f9becfba9334a2ab0bc3595a470a3d84e1a15aab98e157c9dd3fcb98d8a21b18df65a9570373315cff3357521ee8308bc2b04e2d15b4594a881279206f6906db9ac3a3181439b046ded2031302b4de731bda5f089174302a7a657b9fe5cdad5d57bc6f571d9bb5cc73d8431e16f86daf690bbabf499e5df4d1ed20db8ff2e636b2c5df731c1d1381bda548736c7f96a1b575cc71fe4bbeba1c0a422823f9ea69e937d981566ad296aeb70e6368ec351669b9714c0a0db69bcc5558c99107595e68f31beb9b407ad374f4c70358fb9b63f69816740f0376cd3737da089211a5c29546c9f2da7b23651e6d454fbc90f2efaa8dc2a0ae41f6518b9b4df6921499a7de096b0eda62e6369ba43cdf709a4e069218df64cd94125df4a284c5632af781b612d7b1a40cdf6e418160fb036cdf6c241f6376b1551e623d869b07d2e9acd4b8a6ed671d459178396aa01cd1decc3f2d4ad261deb57d22a91596a2e5f2d49bed3d31bec39259198a66ed2748725d072178381ca3151987443922c793d26fb59ac1497b89bb5a6f315daca915 (by decide +kernel)

private theorem part65 : Excludes 0x80040000820000000000000000000000000 0x5e5a903155981011c00e002041041000000 :=
  splitAt 1 111 0x5e5a903155981011c00e002041041000000 part67 part66 (by decide +kernel)

private theorem part63 : Excludes 0x80040000820000000000000000000000000 0x4e5a903155981011c00e002041041000000 :=
  splitAt 1 136 0x4e5a903155981011c00e002041041000000 part65 part64 (by decide +kernel)

private theorem part61 : Excludes 0x80040000820000000000000000000000000 0x4e5a903155881011c00e002041041000000 :=
  splitAt 1 96 0x4e5a903155881011c00e002041041000000 part63 part62 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part69 : Excludes 0x80040000800040000000000000000000000 0x4ecb82b14280b010e00a04007000a000100 :=
  finishCode 117 0x882047a178670e62dc300a43b0719393abc66aab4c5a4ad59170b0d46c7009dacac23692933554409c3f3396c00a4d942e93158ea4ed4133689a23f6482b4dcfe6b03409ac0e6a58fcd827250e0dad212749c4538170ac666a593a566ab199aca8fd5aab68d314f7c0db609cc2b58187459c60154393b0872d490c93b5a8b155ed323641b700285e512a4ec2ab04bc4de7b761c836db4512cd5d2efa04d8aac3b0d5cb4f69b84adac28d94ee9c45456da228f658b8a4b3512bdc4d6a3d3409bdc606d8fcce4515c7cb4a1cd5d526b38c0370a43da63709c9c5c3177ded2f6985c23f39747b4b04e1f9977d87f370b83389c31561709c44e5af23d08138e6a0db599c7f72e1bda56071cd52768135d17c5e1abaa319a7e605381c2a12e2a04d84724c566ab553029fe66989816170ad2c1b6982406051ecc0277b0b4c5ed2a17404a04e50ba00e170bc8ba348bc0fccd46e163300230c43923ec5b4a1a4c63e59c9c9aab2983a2933393977e4f7b710028ae393935541324e4e4e93994560db8f96c3949d9c9db85c0e4f247d8760db49d8b6e4099355457338dc0b6ded32ca58720db393aca67b4b90deced659706e18049d9c9e396a3f6409a47ce228a23ae3e1bda4dea38b409ad2d63f0f449ab3d95466803 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part72 : Excludes 0x80044000800000080000000000000000000 0x6fcba573728bd814d0022181411000c4022 :=
  finishCode 35 0x75154811847807e680177e7b19c0dbc600bbe91f891a94546bc7d338fc91f947ea83da578781466a311e8c4cf38fbd868378aa549b06f92667359a4ae3b51fb087038c0ab45170a846388a8c5ed2de330c516aec727499a0a6613b97c3930f65bc671456c828962748b85a7320a522ac4327487267a9b8f4df6a251ecc297 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part74 : Excludes 0x80040200800000080000000000000000000 0x4f5bc53342ee5034d0060180605000c4020 :=
  finishCode 27 0x110408e63c87318316c3eecc556a596a49d22e15159bee40c9b9cfbb41f43a22e136fcb351ec98160c7909bf358c6cac0d5129f7549a81996464e9302b10e62d8ef56aa7dd52130460362af7831ac43302a91e3eec2e183ea8ae05aad1570515a907b193c6f5159aa47d6068eb1de86951af1ae566a1d1519cb4f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part76 : Excludes 0x80040040800000080000000000000000000 0x5ecaf3b347827814c00a11a1401100c4020 :=
  finishCode 37 0x10230073180120771bc3f4b98e414b566242cb4f2efa8fcb8aaf33769cb554611caf2d3da8e703629971627489a683bb51d5459ac5df3969c6658f9a466b0ad2c7e65df601207c1bc6716473da4e5a7f9414af03d93f1cd5d621a84669f9fe5ed2f698e6ac239ed6b3f4149fa5f06e19c5a7c8e7396b4c64fe9f8dedb41f549ab4b515cd31274ad2e4fe9f8d8aab03 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part77 : Excludes 0x80040000800000080000000000000000000 0x4e4ac37342825014c0020180401000c4020 :=
  finishCode 131 0x310aa290f020b507af82c8801cd541713a4c0ae43398c8098dea73138fb30e5f839a6df88120090cd613ecb925032d3fa0ee731267ce43629b30ac17e63988714e630686398a68b8208d587911c3e1b8150bc03f396a27037b6ca3f7b496b49d341f547eae408f694fec7315a2d07d056ac7e5a88fce04731a631ad5edaf695a89714e624df9ed25c593fae4f1d88a861e88705781d8c4e9398a0a6592bd4d6a2f69998811ed2bc0d964fa977c382731628c05f37db009fd9012b558dbe9f7727c40c21800e4cf62a9cc547f1a4dcca3f35e103b10206683eb9942626b558cb584e62cc0aee83eabdd3bab4f0d887060e3309dcd6de3b0d259cd6a2b512836d20462c6fb613b9adac339ae692c60dc866fb462bd4e0479224692101f9ab8a23305df5a2cb3b2ce8b1ded23b19606b45581c719478b14500694b5860c69fe568a6fb85c3066568af0200aa3706d9398c6fb3889cc640ca00d03334ee7b4b51ce626fb583c6055a89cc5bc5713df3025ed2c5706d9cc5446aec819393aced80365cd5d838b994e4e6cb9abb0717329cc66acab8de42090228c030fe7b4a0a4e6293973099f200ded2b03398b90e626a00ce630ee5ed27318e631cc655170731c8fb838b4dcc0ab353969bd54672c7d006727963e60571ebc106370e578ff2b4b6a39c0d63341f4ff2b4b59fc7e91e1836ded32d25eda5d5 (by decide +kernel)

private theorem part75 : Excludes 0x80040000800000080000000000000000000 0x4e4ac33342825014c0020180401000c4020 :=
  splitAt 1 114 0x4e4ac33342825014c0020180401000c4020 part77 part76 (by decide +kernel)

private theorem part73 : Excludes 0x80040000800000080000000000000000000 0x4e4ac13342825014c0020180401000c4020 :=
  splitAt 1 117 0x4e4ac13342825014c0020180401000c4020 part75 part74 (by decide +kernel)

private theorem part71 : Excludes 0x80040000800000080000000000000000000 0x4e4a813342825014c0020180401000c4020 :=
  splitAt 1 122 0x4e4a813342825014c0020180401000c4020 part73 part72 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part80 : Excludes 0x80044000800000000100000000000000000 0x6fcbb4317aa9d818d282200060220004408 :=
  finishCode 29 0x1d46e18059154393977e41c9cb50733da58ae5df4e04a73dbdac30750e4b574bbe71f50bc3976ae8725005e190732c7117b48ac45b6a459ed27cb732b0ace22d5d8e223f3403c6fb1f9c0910177d07327bdac6f6b5158b8545720e65a2b68aa3496241b0843560912e1a91c5b6de28ae41c9bb641cc931 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part82 : Excludes 0x90040000800000000100000000000000000 0x6fead97357a8501cca82000060020000409 :=
  finishCode 29 0x751885d1346e1046de07052870b1dc7b41f53ba72769282c683eb0093b92721c140ec742d81d14069ae616dad3ded71becd726f50e8c2db37aaa8a22686fb158c3b336fa00d1bf357c56e6df49d9b6649d933da8b27bdc7ab45481b00f2074548b28cd4566fb16da8ce83eb58e5819b7d66aa2b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part84 : Excludes 0x80240000800000000100000000000000000 0x5f5adc3376a87618c292000860020000488 :=
  finishCode 29 0x2e89a3a8e41a88236acc0db5a2a00dbc6accb356ae92cd0128373f4cf6959fb5659c7c169f1f8ce5a3c31708b0e2e1b594356d5d9a8a3d93f1ad3d4c5c168aa479032c550d582d4d7328ac99e2e183e8f6683ea065806f105b20dd0321bd9ab2b4f9a7e82d601b840cc1d1170c8195a2ac0e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part85 : Excludes 0x80040000800000000100000000000000000 0x5e6ad03152a85018c282000060020000408 :=
  finishCode 157 0x398bc3e0731691545410440148b291cdc641466a4133da7716a5672a2b3eeb08e5158745c9ed219286b2961db4c6245c1d4498a8ae836b98e1b99f7542e1bd50bc69f69fb56437b3565676a41b0c428c5906e15e71c0c77a1bd37acf6358186c45c282d35ccd5d698a0b56333dbd2764cd621d437dcb0306da0b56071fe568a6ab8dea6b949dbd9e40cb98cd72a31771b85c224411c70337da4c527664133e5aaa0f4d72d37692b5959c39aca0b5929fe60e8b98e5a2a00da4aba34fe5058fcd0330b84df6a0b8fba6e7170a00e805763fcacfc99aa0958cb90e83e9c9d01a4cd504c488c181683eb10d286b806d6731a4c4df727be6af9c9ddc6e17006dc727170a4ee0fb0b850330b8581b0f64dea6cb551d46210331beda7e82d411b488199aba3f3259cd6583ab574df67f962161f3034df6c53592ce6337da9039d903a4af6aea06637db4ddb455134591a41e9c3f3721f0411bda6482a00d2768199a42f6983ea00deda5c37b4c93b0d3a08e62124629cc55721487b6c48938f933d05ad23da66069c0cbbec3987e7245c7e71b6527700420de2407020e528734ddcc69ef06da065277398d42e36591d707d6b2836cdf6837721a4b1839ed2b25731b8f5abb24ee607c727259974c1b6aa400ce2386b992629435159c44e3e27b9aba5df35ca50ce6a722b87039ed306d9cc670335cd07304ab98d2627118e3e2c78e4ec4368f2203574691046e63942ed5f83e9f2d21e5df83ec4b3661ed7358d06ea2b58e9bed5eea2b899a05558ead5683aa43d28b081fb500481b90e5aab524e227d79456d25515cb1941bb00ce240837791032353a0ea80383eacee0fb310dcc6b4b89669ef928a3f36ae9bee0f33dacbf2c43 (by decide +kernel)

private theorem part83 : Excludes 0x80040000800000000100000000000000000 0x5e4ad03152a85018c282000060020000408 :=
  splitAt 1 129 0x5e4ad03152a85018c282000060020000408 part85 part84 (by decide +kernel)

private theorem part81 : Excludes 0x80040000800000000100000000000000000 0x4e4ad03152a85018c282000060020000408 :=
  splitAt 1 136 0x4e4ad03152a85018c282000060020000408 part83 part82 (by decide +kernel)

private theorem part79 : Excludes 0x80040000800000000100000000000000000 0x4e4a903152a85018c282000060020000408 :=
  splitAt 1 122 0x4e4a903152a85018c282000060020000408 part81 part80 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part87 : Excludes 0x80040000800000000000200000000000000 0x4e4ac03162c05158c102500040040000080 :=
  finishCode 117 0x1c8421d46d130398a03503ac0036e1708f0568b2825cd65d506dc2e1321743f6a88727274933e523accdabaa25526b4fe4eeb9952630798fb26e141cac1d49a7315e200891dc302c8fb398a91d262b079696b236099cd5422a25522a7f640ca8443a23bd5239c4661a9c9ce62ce40072789d2d43896e7113fcc931512ab0642708c2003bd4c056b1cc4fbab550ca8ad683e93a473ab553eeaca641c9cc620518caf13eead545522b53988b6e3eead5580398b09e5aa9f750727dd9652a4da0fab451de8ad4e62a47928a5bd6a4a934e62ea3689a2f083d881b83989a6e61a8735acab3f38cbdae170ad160fab296e14c0e0b4fe83ea4c5a52b3f0d0c5ad83e86c683e8ec496e4d56f1f02e2ce6b06d9c66202e2ce6341b971634fce476a1b71003e09fd8e4e93164178561200e0a93669fb08d0329fd59fb4a683bb4fc7e7129c7624cf15b9cc581f27f47724e98e6312dcda65ad1f99c9e00398cb292749cc680163f250d49a7272749cc6393c40a61cc542f350e0eeb3f5a29bee512a91d0721a5967e2a5526c09001cc58067106f20e4e32b63b07e3a0fa6ed1f9b98d44af71a0fa4cf34fb4a563e3a9579c7f94fe8fcd6c274ca116aaad2dc872bce0fa4e94feb4a563f1c654c67180274b405c996467f941c98165a2b4a65a5ad155e727f56961b904aaf098172683e8b84c0a83996064cf61d8a067b2c1f549a9fd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part88 : Excludes 0x80040000800000000000000000000000000 0x4e4a803142805018c102200040000000000 :=
  finishCode 145 0xf42d35d472188551486e105a83d780e3f1714e6aa478e621c51f9c605274a68ce208d383f0543132c9bef213a547f293454341f4db2f020de41cacce69597157837db51658c9cc55e61c56a2ca3f83ec40bc137e15da82ded2731274c47f4fbbda58aa93b8e06a437081d06dc719398c4b726ac009c352e4fea89521e93326aab8d459ed307d06da48506e5df7313eb036d276e63a0fa2c78bbebc348e6440801cc54c06dcb3f404ad15c872c947e60db06dcd6553154594ad15cc734c457a8034f7cc577b7b10c49e2c79ede91761f8fcd54046c90f3f9ad543563f357138581d079613a4cded30f44bbe08387b20db9aca7f9398b48ae0fcd073174c58e5a9a0fa90537d836e3fcc08d21cc60038c8fcded324ed69f177d8ab397d06ea62884e9611c9fd1e1825568b34c5877441022b8c01cc59c26fcb3f0d5a0e57037dad56499b9ac38aa25a0d659796067dd594b0070338f22065885c165313a439aa1798a6d5937db4fe37db98e26faca5acab4591d67f937db20b802d60e89f761709bec9d328fd3df1ae5a4a6fb475a982e190720b559fad1587730f4e849dcb4526aa93528728fdd4591806115437ac0ab1f9b308a35863e3a0e455e2c72ef8f6641cbda4f970f458a25df4e1ed2a33949a2b5163a48646ba85dcc6b250e295ee25cb9ac786a3f5818fce003318051f8f6650b871522f285cfa70b1cdeaa4d594cb51042bda4bbeaa320ce27be47eaca507260516db9865818f4413eb29946609f531c8b20e5652b5541cc3d1 (by decide +kernel)

private theorem part86 : Excludes 0x80040000800000000000000000000000000 0x4e4a803142805018c102000040000000000 :=
  splitAt 1 57 0x4e4a803142805018c102000040000000000 part88 part87 (by decide +kernel)

private theorem part78 : Excludes 0x80040000800000000000000000000000000 0x4e4a803142805018c002000040000000000 :=
  splitAt 1 68 0x4e4a803142805018c002000040000000000 part86 part79 (by decide +kernel)

private theorem part70 : Excludes 0x80040000800000000000000000000000000 0x4e4a803142805010c002000040000000000 :=
  splitAt 1 79 0x4e4a803142805010c002000040000000000 part78 part71 (by decide +kernel)

private theorem part68 : Excludes 0x80040000800000000000000000000000000 0x4e4a803142801010c002000040000000000 :=
  splitAt 1 90 0x4e4a803142801010c002000040000000000 part70 part69 (by decide +kernel)

private theorem part60 : Excludes 0x80040000800000000000000000000000000 0x4e4a803140801010c002000040000000000 :=
  splitAt 1 101 0x4e4a803140801010c002000040000000000 part68 part61 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part92 : Excludes 0xa0044000080000000000000000000000000 0x5fdbb6b5b4c8891103d0022000040000000 :=
  finishCode 59 0xe8390c0320b8350902903d96d230b24bd282963d864a2bda66ad9ae4b52f716928f4e7b4a825ab6f71069a90b22a8941560e0609991c6d5515cb56e8c2a7de0e2d259a5a1c90e4ca4d8e060d37a8c2b94a08f651c6f1232a179ea2c29607c1c630ab2f163b56e838c61565ed617b8d185837834ded3022e8a119aa29274a2a380d39412a4d7a9c19d481a936069868e627a5041a6c8290703969a92b1eca50594526cc4f614bdc542ed5187b2b0391ead5d381b4c549a9c300aa0abd28ad5587a6703731c7ab6b2b4a4b85e169aa25a30aa4d6aeb56d608c2ca25526b576501b4a65128f4dab6aa303e7a982a5ab67af6a18f4dab73084f5ed43 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part93 : Excludes 0xa0040000080000000000000000000000000 0x5fdaf0b594c0001102d0020000040000000 :=
  finishCode 105 0x102328ae1c8731741b4721bc4701ae9459ed2703541027249d28af69969ad5f16ec83316ecb4d9ed27037b4cd5d2efad35dc741706f05bac8035dc8f41be30b249da52e47723d06d419a0ce06ba90e4268b620cdc8f249d69ef6d9812945694cd299c8ed5d723c82335c8f4d0471fb569e9274a2ba0d40b75b40e08e961deb5860dac3b6b0c7ed1eccda34a6419b4c503a7f9a0e6703694ba0da3a8ec3903d99a4a92b50e835d244a0c3d969bb54499f1325abe7031ecbe0901ff66ada91565e3d934138614cc416aaac66720b13d852a45948ed5d85525c98b8ad513fca46439ab02a0bc0f643831c0c3a2e4191bf1fa4e068df83a252390d5d54138691cb351d4a49d28a96314669bbd8cff334de30a5a059e381c1f53ee5df8e06d5f1d4c353731bd4cff2d37736c4cf7b4a915a867f9751a85c1c86d1a7f0525ed27fd6a187447b283306db20bc304659ab56c5ba1d1651c8f398c5bac418fd27e99ac26cb5268b757c69bc3d94958b75abf1c0c3729419a869f569f9ff50660db497c0db6405bb07447b2a479aba2dd (by decide +kernel)

private theorem part91 : Excludes 0xa0040000080000000000000000000000000 0x5fdab0b594c0001102d0020000040000000 :=
  splitAt 1 122 0x5fdab0b594c0001102d0020000040000000 part93 part92 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part95 : Excludes 0xa0040200000000000000000000000000000 0x5f9ae5b588ad40201000000000000000000 :=
  finishCode 105 0x102328ae170731441a05a6a98da2e8b2030e2748b7437f06f89d2a25963ad23413b15d8aa0c33716672894d731851eba91d6ab13a548a25f9816f6b16eb154186a628e61eba8461618b8549aee238b631565158b747aef00b765a2a09d48b291d87ab5515a8b7435f2d245bac82e8a8330a45948e945613cc3f1d5caf30e886fd1e3074527330e587eb2310b00b749d330fda96b4951582ada4613cc3f0dfb0fe6b28f5e413a01c7af28ada04413c59169a3d9989ed6559dac3c5bac4320c028fe837a43c39a8eb8b8ad5b274cd5b3d8cb1359dac3d906adc2b91708745acb282563aa4d274b56db4641abb0734192b20b76698970e61dac4e7318b756a3340b0390f8073561f34f568a80961bb95d04e2e1161c6b583cac3d04e9220e6170b14daa22cf85c2d5f87ae6d90e6be0920b85caf2bf5ab6c3f154b4dc5532ca5a470b0d946a1a0721886d1bc05eb1565aa9714fbad5b16ea05dcaf356daba1b316e9fa66aea894172b4d16eb78b4d698c817064b566157cb02d345c313a47af348da861b32e1cb2959fac02d587b21d18b86d65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part97 : Excludes 0xa0040800000000000000000000000000000 0x5fbbb6f48ad102040000000000000000000 :=
  finishCode 29 0x6a1b038f9cb55c1ec83365129cc56a328c4d6a19d59dca1d5a8a20d82c0a213a4dc61ccb4d4fe9f6561ed5b4fecc3937ea4e527b2cd5aca4cf485b0e47b2a41cc65a69bf53c72d3584eaf9629bda47a6b21b83d31bfcb095a6b58548ed5b72eca455a6b52c2fa6fd612ca47592a88b2287e61c870c7a6d8309e5a8a8ad43ec57163b0965199cc6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part99 : Excludes 0xa0240000000000000000000000000000000 0x5fdbafb5ac8000000000000000000000000 :=
  finishCode 43 0x1e06f1b4721ab72d35ed2817068875c1b6ca308b2985c21d7521a631bbce4e3d99ab64e969bc7196a8b00d424070b39ab5461e0a0e53d3282506ec40b7637eb56d69a4e9587cc427de5a88f5c5ba3d7964620e6ac81b4e50f8b8527a941721ab7352d07ad2d8b867196accc241be2e4b95c722d5b3f4b5645c23d99b46a103b075d69a833067af83d78d7ea0b5a6875dabf280cd7eb2953144b2c9569a4e957ccb25 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part101 : Excludes 0xa0040008000000000000000000000000000 0x5febabb4c89003d00200040000000000000 :=
  finishCode 53 0x3c0b8238735760e3ec23d9e6aeb95d0662e15a8ce517a8cb4d7b7c1bdd81ec96c658ea8756a22e14f0c2b758ea8756a2b2258bc1c659069fc3d36aca87c5c27319cc30f4d904f1786205c3185a0daa1d416a4f55eb395dab2731621947b49ff527ad3f9ab2b4d69fc3d39a7e7fd91be7314a0b5847a73544e62f51a0ded617b1ad34ffaa1f170b60bc30873105cc0bd4b1ea741cd69af69728a82d48eb4394635fad3438a6bf9ca2f696d16869fc59d154b91dcc2833491edb34fded2d5d599a4f5a571325ee3071599b95ded2d5d581c8f313c5bab5116ed06f61107a2e187a6e619cc6b25 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part103 : Excludes 0xa0040002000000000000000000000000000 0x5fabaafd9881006d0020001000000000000 :=
  finishCode 119 0x781a860154640e3e735587cc111e09cc43823d95716274615812e631daaccd0727ed9cc619d59188393ac0c84001bd48103334a53d2e4141cb90641b92ce5a6a49dc96e5d80107328ad44ad51420b532cee0eab33723ce63589b4ed7815fc3b5398a38b4d8d7eb1f24f9afe7b4cd5d587b30c82c3e0e0b0266ae9cc4e63280bc23873155134388a82e694bdac306d3b836a8e563ab5150fcb0f6b0cb1d692cb0f599c00ac1f82dd4d147f2c75cc2e474b1edf27de0d72ce64b13ef06bcbbe3d75a8c47369f9c45aba35b9a763d76b0ad34fda7115a6d185839accce22ae3d0bc1f8731451602efa8ce62bc6145ba4e937ec2dd274cb0f37eb15dab64e9968b1855a69c87e0b765a6977d69b30866138f5c5baa4d9872b0f519a0e47aeb0f964af42f0b01cc5345f094614ca4762c8f5d64ab3b4714c5a8cc4162c8f5cdc7b4ca1f523ad4427346165a89326274ac95677002203d7969a4df4fe8aee579ac3d48aa332ef977e579ad5561eb6238d20f5d4073da4576f69a0db185a0daaf39685b169a9641be35fa89435e3d74d169f0b2dcc2b513f6c2dd837b0a6165b1649d22dd91c5e07aed3f9ed2a4d05c851e7b0a8fdeda4b35e14170ed4172b02d3544b2d44f5f3d4decb06f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part104 : Excludes 0xa0040000000000000000000000000000000 0x5faaaabe888000000000000000000000000 :=
  finishCode 45 0x3281e74f16857169aa03c07315f1acb20dd00e71981b706938fc61662cb0dd69282341eaf829d96927d74018f5d00eec2900db839c82d8c2c4e9839c83d6adbe0d318e4e71f161c6d941eab80d7900e8271ebb95e1618b755c6220de731834c94106ba41e30b3dad89e8293d7835ce3f1c9c1aef82e0b01c7d485e16440c86b5a8f41e5ab6b4b69b9c9ded341d41b71c9d06f34de413cd2d06dab8b2205da8f035da970779ac2c096b2c0d7 (by decide +kernel)

private theorem part102 : Excludes 0xa0040000000000000000000000000000000 0x5faaaabc888000000000000000000000000 :=
  splitAt 1 109 0x5faaaabc888000000000000000000000000 part104 part103 (by decide +kernel)

private theorem part100 : Excludes 0xa0040000000000000000000000000000000 0x5faaaab4888000000000000000000000000 :=
  splitAt 1 111 0x5faaaab4888000000000000000000000000 part102 part101 (by decide +kernel)

private theorem part98 : Excludes 0xa0040000000000000000000000000000000 0x5f8aaab4888000000000000000000000000 :=
  splitAt 1 129 0x5f8aaab4888000000000000000000000000 part100 part99 (by decide +kernel)

private theorem part96 : Excludes 0xa0040000000000000000000000000000000 0x5f8aa2b4888000000000000000000000000 :=
  splitAt 1 119 0x5f8aa2b4888000000000000000000000000 part98 part97 (by decide +kernel)

private theorem part94 : Excludes 0xa0040000000000000000000000000000000 0x5f8aa0b4888000000000000000000000000 :=
  splitAt 1 117 0x5f8aa0b4888000000000000000000000000 part96 part95 (by decide +kernel)

private theorem part90 : Excludes 0xa0040000000000000000000000000000000 0x5f8aa0b4808000000000000000000000000 :=
  splitAt 1 103 0x5f8aa0b4808000000000000000000000000 part94 part91 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part107 : Excludes 0x90044000000000000000000000000000000 0x6bebadb3b28888000000000000000000000 :=
  finishCode 73 0x6f19c0f5b20e4330881c84192a4d9ac6c213db8f5d66ed5b72cc3d75818451fb8f616d91e64f14c6107aed4998867af5aa91e6382cc4d504930cb85aab0766b1ac0e6adc61549b309dab62db1eba20aa308b139aa6a25523b56c37e8e172e526a3ee26aa895a72151a30aa036adc60c99aa09512aa8b3f8b2e2af523ad5672190561744b0e427331dac2b5504d075735b4dd406d5d71eb5461e8b09e392b56d8b6c439aa2709157cc5b1e8b91002e89041be522ad34dee7215809ab3d4569a9314fb9c64e5ece0fcda870afce4f06b9545a148a8c356e50f933c7a3359567ea1f39aca1f6b2b596266aa8c22582db1f992ae723970d67eb0b9ed21a9589b576504a91dca2d43090718f5ed438c2aca4e4e0bd7b5c38d3938725ab73dad66ef690d0ac4ded30fcd69a735 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part110 : Excludes 0x84044800000000000000000000000000000 0x7bfbb5bdb0cb8b240000000000000000000 :=
  finishCode 41 0x390c0330963a8da0b1d87329352429450668ae6362966dab6a4d05ccc39613c615ab60c94998725906d1c7b0324e423e3399a40e5798b60b92558f64def0738172a0369693a524f352d6047145728fcfc836cd5b5a4b0fc9d21bf628b208f196928cf170bdbc99e8f189d2b49611b4621ce59241a3c5842c5157c86fc7c648398a2a030d79f846b9a72c3f6ada80d8a28f19c7ac218379b15406479651644d19c1f1abe647e86fc5c28fd9ee2c5b1dab56ce4a7098e4aa4d0e1b9ae5159ccd666a25267cf6339293a6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part111 : Excludes 0x80044800000000000000000000000000000 0x7eebb530b0c98b240000000000000000000 :=
  finishCode 147 0x1d46a1b8671806c0e3e72d6f1986d1901638334da34614b52b3b1589c94b531c2458f16a43929e95e1ac72915908c1c7af37b8f6567727ddaa67af1eccb4d943ab25170a385a1c45646b0970e392b56c71693d1f99c963e9b4867339ccc19aca2c8e658f960cd62db56d23a3f34d1985a89f4e6a99684e12d539ede69da0da381735a7dc19ab03966399b5463911c590e06c2368f699a5ad513768fcd68696cb4d471cd2d3e5a4cdab63d992662c79ec6b4d47eb68c82b08fd9ee2721399b965605d0e2ef69a0de9452f6c3f3a30ab4d0bec4ab6ad8fcded2709255cf6936dbdc51fab4d641c86d17438b8fce4a29ccdea324bdab6bc356e0e48b1e7b8b585cbaa4d1eca936376bdc527a5a9a30aa4d376ac0ba308cc0fcd43f3dbd44a8fd49c9c2543f3d449d2a456adc94561fa894bbea4320a3992562e12f6a38709827ef51134a76c71e4b3515a916523b524e12a2b85c28f16adb0767a8a8c5cbe5df6d194612001f9b304e99a42709399af0a2b93eed63485b56d48ea2b947ed534fba68d61963b1834a2b4e56a25a41ce0d4b485ed29f76b0b4ee5a6b787af948e38f51f8b1d64b24f5ca24e9390cc2258d5b6aab58528b237d3ee6b985728df8c2cf67526bd8d4666fd601c8501604b07b29459ab6709523a204e9944a709904400dcf287548ade2108e24cdacb24ad8570ed5ab70325cae92b98565a9154a8765189b9d986a160515c8cf35c93a56a2a330e49701b398b6a3305ead35a731c85aca70996a2d65390a875466a4794623d99872a39157b90802c0a472f6c725497cb028ce30b23f5856e67399b56e62da3d437e08b9ab6a3f (by decide +kernel)

private theorem part109 : Excludes 0x80044800000000000000000000000000000 0x7aebb530b0c98b240000000000000000000 :=
  splitAt 1 134 0x7aebb530b0c98b240000000000000000000 part111 part110 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part113 : Excludes 0x80044000400000000000000000000000000 0x7acbad70b088cc083800880008000000000 :=
  finishCode 71 0x19453134670c0ede399000f5d908c2c827397b10580403bdae51fa0e56271ae66adb10560e1eb781808410726b99ed2c1f7b5b485882e63583a484cc5a6c1e662c8e9dec731660f27d396aac598c2a01d6a34614deec41399ae900330881cbdc8f2cfd882e3b7b3ad349d2a479ed6c41583b13e461445a6cc1f578ad2569b2bc453e39f9c8ec4f1eccb1d5a6abc4e2f0f658b272f671bc6107aebc075cf8f35856266640091593dec1f7b49bdd19b3105a42f696b0bdb6690bda5ac28e369bb1055f33db5ab6b4d620bda5843d143b460dac24b9620ac4d652d61983e72f7b5cd5b485b9451d32ca51bed5b485ad343d6ce1f89db9cb2d5b57cad443d680740bac0da398a007adab7285ce6690b4a0a42e48ea3d641cbdae51fa0e5b448ec9410f5b56e48182cd5f30698c29c86580e428171ecc1a938bb4c6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part115 : Excludes 0x80044000020000000000000000000000000 0x7afbbc30f5888811404c002200001000000 :=
  finishCode 45 0x148581bc308ba0e43688e07ace4a8024f5cc73164e5f398c9d3391dcc272f540e441b8f6585341c583ed473e5b9451c734a506f20e5a8f399dc8e9e96b08f6506e1eb6a1c94561cbda4ff28390f5a40e617b6cc11374b0dc7b27359a4ada3a0de2a01eb5d13c860e42a319466d63984e4c36adad56518965d1faf63499bd8e61cb56e594af0c4282630b28cc76a721495b57672b9c86495b985c9f39849861eb861bc3939ebe2d0b03d48ae614fbb4dd28af618292e579cdad2d69ba4cce2f356ce4a1eb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part116 : Excludes 0x80044000000000000000000000000000000 0x7acbac30f28888000000000000000000000 :=
  finishCode 129 0x1905e0c5318ad4c6d0c3ecc400a2338725399b486587830c9d3185969aa257a9b78b4da0f2e637b883143d6801cbe837b164fd2e479edf307d69a0c50f5a7de69fc1bd89e1eb3d7c00c222093169fce47274b4fe72393a67a9ac3d6a2e6398829454789c7dcc6703d6963486578b98d266727801403c0dee73541cb4fe7b4b4dded31f2ce6b27bda773da4e3ef6999c602003f4c8394b018b2485a7f0f05cc2b07062c6164a08315cc72989a36861367204731100f5b10a2589d2807948f1c2600471806b0cf51414a40d24e83744076b284569b18551fc616515c61638493a580541cc72454e3ec3f48acf6957ecd59526cb4d384a0dc7ae3b5a30af6361fbdc41a67096120041bc839498a58f6f9a8671f594c1ae589b98cd72d5d839cd5b8c2b57476ab51274c08c207ad60733c7af6a8bd4d47e8274a1b38c09921aafd6969cd5ee3356d21a91571dcc217b493a547f20dc1a63d7732048603d6ce238d2da30ad517b59c9da7671f4b169b3dbd48ad5d41c9c9d6a34614b529037b4c208a356e736a31ce06d5561cad35a52d319ed2d5b9cda7036711c604cd2140bac083996a306d89567bb2caabe630b0835463fca515ed2d319ab67f9601c87419c069ac3e51fa0dd81f1c0daa27279aa3357522e8275a6cd59403b4a522e70369db38b83009279812e6362b9c7ce6a8e1f4e381b4ee0e74615676d531f9a0a63e9b4a524e9279cc6709 (by decide +kernel)

private theorem part114 : Excludes 0x80044000000000000000000000000000000 0x7acbac30f08888000000000000000000000 :=
  splitAt 1 101 0x7acbac30f08888000000000000000000000 part116 part115 (by decide +kernel)

private theorem part112 : Excludes 0x80044000000000000000000000000000000 0x7acbac30b08888000000000000000000000 :=
  splitAt 1 106 0x7acbac30b08888000000000000000000000 part114 part113 (by decide +kernel)

private theorem part108 : Excludes 0x80044000000000000000000000000000000 0x7acba430b08888000000000000000000000 :=
  splitAt 1 119 0x7acba430b08888000000000000000000000 part112 part109 (by decide +kernel)

private theorem part106 : Excludes 0x80044000000000000000000000000000000 0x6acba430b08888000000000000000000000 :=
  splitAt 1 136 0x6acba430b08888000000000000000000000 part108 part107 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part119 : Excludes 0x81042000000000000000000000000000000 0x7eebd33cec8c21000000000000000000000 :=
  finishCode 33 0x3b8ec328a618ad2631fddaca711396984d80409cc4d39ab1368369335ab60d1521ab7174d1f272769b9845cc471c83601a2a31920ed5b5a5a05d4129c393d2331bd5a5a5d3988341a520ec4f69ba0a504e6df9a6eb55414834580396ce4f83aa09d0527119c9ea435961b5ace5a8ed555a59c64e4ed839082032d613358548e8179cd6d5b5a59cb4e5b3584e623d7696cd21902693d066b584e22735 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part120 : Excludes 0x81040000000000000000000000000000000 0x7aabf238a08000000000000000000000000 :=
  finishCode 149 0x1cc771940f5a80ec1cc510821645f14c315c2d7303b40c81fe547334c566a2e3315b94650fb4c549b2d3566a62b6adb94547306a630ead35422aa356e4a1a8fd69aa393889c7dec727f5ab6a390de98a639ac2d7404bb0b0320c018a5ab7282404ea4d4a19c9ce3e711922e943947ed5b940661339a98ace4f0f5d9c6a218581d8550c2318384c2d371ebbd7c9d23bd3889c7d88413c3bd83cc7278e4f34ddcaf0ef5ab66115f15c2d4cd3737eac7dab6817698cb1f2d4b56dab718466e19c6019838f9cb6000669c26399b0ee170b9ae3d79714e62d53471b0388b683eb819ab012de6b0b56d4727319ab65c39ac2ca2e882d87d6d499416e593988335a631ccdcb20cd6d1d05117c398cb351f99c5cddad81c0c7831cc4ffb20b64959cbc3a2b4d969e7311f9b56e7aa8ef5cce5ed398b60881cc49d32875ab62e19ec720f47e6da328ba2a8c23503f35f107a71f806a1555a69b4416e7250e8c6d1897e7f3397ad3525f1c4d69a61f41eb51002c8ec356e5a69874c3ebe2c8e40e9ccd052705171b56e38c9fe6389ad34e6681d314c0c5590e0ab0d969a7cb497ac668c1b56d5eed2b6a1d85f1b8314b3071783a2703945728fcc3b1c0d69a1d158ccc59732ad3438272d60fcc25690981d69abe288f6f9ab6c110c6b16500e709399b50bc3b01d1877a611414c72f3939cbe6afc92b41b9cbda876181b356cba61d12f6c1a659cb99c792d636ad9c65ac727a4e26ee350ec201e0e89874e4f2f8ca12fe41cad34bde8399ab72d3477b356d47271f (by decide +kernel)

private theorem part118 : Excludes 0x81040000000000000000000000000000000 0x7aabd238a08000000000000000000000000 :=
  splitAt 1 121 0x7aabd238a08000000000000000000000000 part120 part119 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part123 : Excludes 0x80041200000000000000000000000000000 0x6b5aed71838e48249000000000000000000 :=
  finishCode 29 0x368cc2c0b4d85b6629399ab1061c85a4315b0365918b8d83ab55064a80e60e8b2c5c6b1f05dc3d79eaa2e358f970c19262b4f1cc50158398b58e16582ac5c670516aca3f6b1ad34c5741f5286b4d3d78f5ce0ab2f8e0ab4d881aa70684baa4df3149cc5602dec91f71ea8945b6a3f5c183b358cb722cb1719f765aaac8b2596aa73137bad345ba62b26fca255a69cc4dee629 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part125 : Excludes 0x80040200000000000000080000000000000 0x6b1ad53191ac44601000140000010000400 :=
  finishCode 125 0x881dc8220c7c1a8580c2318a53c315ad566a89c85246e1a6eb3fa30a9451deb14c73b2bcd6523bda306b1f531e4589aca560390ad3650e8f655f30b8c7b3328ae280c0b9ea2b0337bbd8cff2b4d398b68c3f9606721493c6f7728c7f9399ad35e4736cc55266ccc2c0e430073316bc3b941cb28b03a0f2c4d7b1978ce624af9946713df2cbce628270619cc60dccb55629c1e5652d51390c3aba0f28395979c14e629e20e6581ad1569a7313829c85981cec1d158fb564e66829965e731651b85c180171a09e41c8735b46a16770ef522e0c959dcc29735a3ad81b1859aa69176a160061a0e6515a93569b35655ef20e5c9eae20e65269cc5a730b3d472dc2c0d42e0c00b3e629a0e439a9e41d67b9acec77a2bd167bd566aeb4fe274b14e62aa4ae1de87358a6e599256cc280e41cc5a6f315439a3a59cdad510dcb90da07356c390b4de8c1b4f49d20a96a582ccf046fc5a96a5a876522b4bdec702a49be6f7274cd6505e8b3d1e32d34dee73172170591a86519816b8b8c77b03243a2b00b6e62ba8fc98716e4e80e8b58e7b1b9ac77af22c0c539a92733629ce4591d6c5398aa2e35d13c399ad5651fb0f58766db5a68f4662acb13580e0a1699a7e5bd3eea8ace6628b9406d5d0ddac7d6970e945c62db (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part128 : Excludes 0x90040200000000000100000000000000000 0x6bfbddb794ecc0209282080020000880401 :=
  finishCode 31 0xca390b82c8b4f8b862db06487445c6941c2638bb787330e8b02e359b9ad42e4cf9ee7077359b20f22b0721967273350bcb390d9cf5150f8324b971334e12a47697c3d716b8b8de46a1c8560e2ee619edab4b629b009459872d2991fad492e1ab02db594c0a9376b14cddb0a65ecac5398aa7af9cc2c2772cad3d462a47 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part129 : Excludes 0x80040200000000000100000000000000000 0x7b1ad5b190ac40201280080020000880400 :=
  finishCode 129 0x102328ae390731771bc470fc530fee8176a4cb515aaa4c478e6f791d6a47171c10f8298b2170e4f79ae47ae6076a11f70f5d2768e987ae6b9627b50e4f8fba70538bbdacc56a099aa718572c8b8cd7327bd24ec093849c85877245c5c6d4320da2c00c916ac9433d7ce3d31598ae1718b8e38bce6b171b30b0282650ea4c4e1306200607171ac4e504ad55a6f0aa543b2bf5cc65a9519a50e523b310432072183a27176f0e12c099aca6b969ec4a0325847348da6e0b3629b9ae3e5c1d4166c556f11c373ca03515a981bf8d72e6b948e7afa30a2974705c71fdd04e94385ae2e36d1e4170c6293999c25a9718ad26318a5e4722086f0e2ea83008179edaa474a2b0e51c8c2cb35495b14e8c2a8cd4629038d72d5159496a63ddb595466a47154ad88e3b89e398e4959fdd02e8024ae30716c5a73069727cc1f6a5c1cd3d79ae5256740ef6727b8f56061dc9277aac60c39ab5161dcc5398aa1cd4f19c6011e7170deca82741c8b3e620c233d9499e91925dc6ed479bd960f26058f96c1169babf47b2b35601cc724bdedaa31613a5158a2819518c6b9403984520ee4320f83c8d432849583a2a3338b8324c56de1c5d4670ad58727af8b52d65519a8c4b532cfdaa23d96049c85941ecb7862b40bc2e359c967e59fcd51523bdb63fbb5450722e3390a687090d9c5e3171981cfc69bc2a9171b5956ab3574b52b132e18abe (by decide +kernel)

private theorem part127 : Excludes 0x80040200000000000100000000000000000 0x6b1ad5b190ac40201280080020000880400 :=
  splitAt 1 136 0x6b1ad5b190ac40201280080020000880400 part129 part128 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part132 : Excludes 0x90040200000000000000000040000000000 0x6bfbdd3784cce92013000820a0800008000 :=
  finishCode 63 0x10c328d02782e364158690e42e3d948ee4705e933418ab39940701d5ac65cb493933543eb4d62acc095019334e12b4d6416731c9528ab4f1deca1f512a78aa2d354c62dc4cf1eb86fda5f2d2dac6a6304e390972d6471edc4bf06b72cb16ce8526cc35728c7cb16db90f22c0d01c24e4a2db9aa25c51e8b52e62ab545a0690e4334dcb8aa33523c1c63d7c60cdcec3961cc5c3629b40b813354c0e8ad564759ae569f358cf6ee599a92b4f46184f358c57a96121e697ac35ac69e3697cb0d6b1b00c39855e2db9c8601706b1c0a939282bc3a2ac3787334e1673393d69e2bd9c9e4d59cb2c2785b67b78b7a3d716d8f462679bb49aa2db (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part134 : Excludes 0x80240200000000000000000040000000000 0x7f5add31a49cc92013080800a0000208000 :=
  finishCode 39 0x4f1942e19c5a6a98923784df470c0f205d61306fdc7ab4f6aecf61315b544552721817662b157c1d1485a05d257181c5c6ce320b03781cd89be73341ca4be2c59ccc9beb3985a27216b2c709171a05d27b181c5c6de3408e2c093d40bad3e392ac366aecf6d1ecb14d25ed372e2ac82599ee272162ab4dd25e93d578c725154cd5d392ac1060f6638b93a4c226291ecc733692c92f315b574552b39 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part135 : Excludes 0x80040200000000000000000040000000000 0x7b3ad531848cc92013000800a0000008000 :=
  finishCode 135 0x398ca4307312e20c5a6b788e270a62934d7334bcfeeaf91ebac2640ba80d5f3358cc0eb331eba80da8681b4315cb0961e8b8c37e2af064b16e512c1c4d722e348ec4e969793a66a986fd23ad43b8c818a6315bdc6171984c3a3316dee2f511deac0721589cf6b38493366b2981dec328cdaca2e1390b68b0378ee13a66a58324e6680726fc1b389d2b1d6a59c24e66d658e42c42c0a3f85c64e9584cd4b171a4363669b9df0392c4e93159cce6f19c4f11c6016040bbe046992724e96a49c94fee61115ec7f7390cd3748ea4f5603fba3ae4958b3d1d724adc8821805d160390b52e71ea4bd072c279eda945267ac0c09982203357bb58d07271761c98458733db661d9844e42923082c398aac3b723c839518965e7b7a91dc8b06f6068b3c3a2920abd84b13a459f23cc5c2d02e0e41801d15d0f6324acd728eb47eac0b339edf1837228b8548f460d69331655fa5977b7acd627498447b24df8e4ab4f61dc93d308b90f81c5da531ec5c8a5c5735ac3548e9199eda4cf7b6cb55267ad2c55eba24765239c845527255807b32c74e2ef739edef71497b5943a2de3007e278b8209d0722e396929459c7ac820a5700e8c3d926fc73351fc92795e2a175a6a0a53c6511c83100ea6399e5aa9bdd3de5e3303a3f65a698ad2573d45aa6c5b5a6a8965a8b5758b67335a69c96403b20b5193d2725314a8fe79170641a858ec0a371dad24c521cd5a4c7098c0e62b8e667095a6ce477308aa47b218d (by decide +kernel)

private theorem part133 : Excludes 0x80040200000000000000000040000000000 0x7b1ad531848cc92013000800a0000008000 :=
  splitAt 1 129 0x7b1ad531848cc92013000800a0000008000 part135 part134 (by decide +kernel)

private theorem part131 : Excludes 0x80040200000000000000000040000000000 0x6b1ad531848cc92013000800a0000008000 :=
  splitAt 1 136 0x6b1ad531848cc92013000800a0000008000 part133 part132 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part137 : Excludes 0x90040200000000000000000000020000000 0x6bfbdd3780ccc5207100180041050400004 :=
  finishCode 71 0x1c868194591706605ae2e3390cb4f0648744e858230b30d4e0aa25526c61661a9c163074615ac62db641984f1bc390b14626a8ef569e0c52d4c49561ab8f4b5338f5612b4f3eeca03523a8943767054f12c5a6b089a2d149ab23acb96c2391d64cd8c2c2797a8972e8c29c2543b289598640b8b0744e66361a30ac095a6971521e7096f168b2826306c3f735a89548ea3f382c6b32e2c61569ac02c01d17b7c37971e9354e66b099626e3d6a8ac0ba1d073343057b01f4fbae6b3d8cb0347eb58e597a3adac7460c77a4cf5949b7e30b167e30659747e8ef5652d37791743a0e427331decc357b9cb356aea49d60550e2ec3d9812b1316dac4e4fead356273025383a09ab1f3566a9455a7b00c21928a3ab9a6ed6359a9f760bdad35ac63d76514c61cc0af16d8b5d87302bc5b62e31e8c2db (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part139 : Excludes 0x80040200000010000000000000020000000 0x7b1ad5f5808ce92071029840c3050804004 :=
  finishCode 59 0x408ca430731770b868169ac828cc5c6b098282c3d315b9ada5f287630a6f7846269f6979c84c568e0e7e6b2981d02e9e18c267dd8c29c145c69e18dce15f8c2ad35dc390c62b7a8caf96a4c61584e1d15620869bbc884314ce427dd8f768eb594a4cdeab15f4b72b1f594a98a47984ed635aaa01e0bda4cdac68f9519cc53861006b1cb0d61ca91d1f2a0310d224f43a324654666b99646c39499d1852679a7e40bb0e5804313c67184f30fdca25931d7970d2672c2584e1d17aac1493dda4cc3a2b1f61cc93347ec4cf250ac35942e1905a6ab0b3f94622a95a798ace4262b9acb28754662e36b2c6073908b8d58523cc27390b5459c1ebc817586c919 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part140 : Excludes 0x80040200000000000000000000020000000 0x7b1ad531808cd1207100180040050000004 :=
  finishCode 103 0x6520457140670e62de310c02e882941c98466139c949be2e38c523d92d4a787e1f7626fad3500ea62d345c71b7c77ab45581cc4d526d185314a01e5a6a00c4063564497c4e91688ef62749fa565f181e1689c24e131c5e18391885a6b78ee359661f984e30a4e971e8b8d00ecc13a5a8167c1d1584d185587ad45466a33947e69f89d2a339aca607403a70a63784e94fec2e3587accd49a5a98e4b289590820e131c945c70b0dea746143662e3770e6718ad98274a8963999bde5a4a8fdb44f1e45a6b1104184e47eb4c49d2709399a70a25818aa39731cd4b5198b8dabf24c568ab1d3039c24e6661391fae63274b52de48323073075a627091dea8e47b31f64df65a939998ae274ca25171ad360c3919c5a6a98c813a45c71ccce131cce2e28b8cc5262b8c0e2e367056b28950724e93eeca4d3038b8ce672d3608721e458ec2e13849c95f062cc819308ad162748655f06718b320a4c222e15a5c3d96a8ca013a669bb14d25e93d7709d341e439ae63348c1cd (by decide +kernel)

private theorem part138 : Excludes 0x80040200000000000000000000020000000 0x7b1ad531808cc1207100180040050000004 :=
  splitAt 1 88 0x7b1ad531808cc1207100180040050000004 part140 part139 (by decide +kernel)

private theorem part136 : Excludes 0x80040200000000000000000000000000000 0x6b1ad531808c40201100080040000000000 :=
  splitAt 5805 136 0x6b1ad531808cc1207100180040050000004 part138 part137 (by decide +kernel)

private theorem part130 : Excludes 0x80040200000000000000000000000000000 0x6b1ad531808c40201100080000000000000 :=
  splitAt 1 42 0x6b1ad531808c40201100080000000000000 part136 part131 (by decide +kernel)

private theorem part126 : Excludes 0x80040200000000000000000000000000000 0x6b1ad531808c40201000080000000000000 :=
  splitAt 1 68 0x6b1ad531808c40201000080000000000000 part130 part127 (by decide +kernel)

private theorem part124 : Excludes 0x80040200000000000000000000000000000 0x6b1ad531808c40201000000000000000000 :=
  splitAt 1 55 0x6b1ad531808c40201000000000000000000 part126 part125 (by decide +kernel)

private theorem part122 : Excludes 0x80040200000000000000000000000000000 0x6b1ac531808c40201000000000000000000 :=
  splitAt 1 120 0x6b1ac531808c40201000000000000000000 part124 part123 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part143 : Excludes 0x80040080040000000000000000000000000 0x6f3ae3709a80f0068070028010008000000 :=
  finishCode 85 0x4f110391845a6aa8a22983eb171c1af8c2cc571719cd630b1c44dfa2e31f9a41101b34dee8e206586f2bc4e3282772ccc1183cc6149d24d59abe3d15320fb16fc5c65d7609c81d6e1aaf1b845c6d3d89aa5cb6abb68ba288aa4103eb5205c7316d07a61396a223d411b48e30ad39512923e691b4e56a2a2576120413ce6b5269b34e0ad8440d5b923a941274b92683e8b8d233356d1e330849665cb735b56ce0a9418e0a81d6e20c58ec7277328b8ce22f6192824cd58ea0346ff3dc5a92919259a9358b73d449d2735171b68ba289040fad88515c5e34199c16309978d667069d0670fce0c6a1dc388a0de30992ce721a8aded72c1d8aed212eba01e583ac74e232cec5c6d22a8a24183eb771c86711515ca3f309a8ae51fac764a0cd636a3ac1ce223f37618871eca4d171a4be2062dc61d8c2cc4d71ec5cb1719fa4e32ee3e02e32ebcb516a3acccc56b339a8eb5136cce5f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part145 : Excludes 0x80040002040000000000000000000000000 0x7babe3f58a89004c8030009020408000000 :=
  finishCode 103 0x2f0ae3b87316f11c6a07aeb24616609b15ce4e62b607ca2b7b598a54071bde08761908c2cd5b5819bdcc56c0430a4591e26fd393b15e4789fb66a4ad160e72c3d676b45474cb33171b510c2d363149c9cc2318ad64b1859ab6b2f801bc470e6b280d49ab0268a252efcc438c293a5a925ed969a6cd274ac3cd8b1bf61838fc6f72749bf49d329162efad36186a154640e22b2410735523c7ed732b16d69a62b523cd632d8ad35823133d69b27dd48f041c9cc272d549d32c75412ee400de282c5c68199606d2159fb4e49d32d35ac2a47965eb4d943eee320a018a56070f644f31ec5676b2f6adad4640c8b5d44b2c3dab66f786164771a05305c6b634965a6b5558522cb1ebb0de5a6bd9cc3e607731c8e35879c9de008fc7274f1cd5d30fad45804713ee6fd39ab556837b09d1c6af9a0e73d7c9d27237888400b4d69cc819274a7f4fc3f6c1912ef9fb63888645a840cc9433889bde7a8977d3ee8fb9cc6c297aab13d286f5f837b78881f89fd59dd1857b1a3c60e66b925b9fb611bc1ce0df0739a726b9498cf5f2749ebe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part147 : Excludes 0x80040008040000000000000000000000000 0x6b6af2f68a9201c48230048201008000000 :=
  finishCode 77 0x430b22a8d24183f35a6c7052668b8cdfa735266ca47831f0692c61330f9c64e6a9a3b883d398d1834098b8dabaaf189d27d9127c60d86a7314099cc66a19b65f061099ad5d9ca2d61170a50ce2b34fcfd2c25849e7e96ae9cc5f0382c6fd38cb509e3494db712bd03ad435a6b58640eb50c9ab460ce0ab4d621a855128419b4882d3c099f291dea2c3d948e4d52c58f6671d8b85ac22b7880db33584e62d43969b00240c599ac281d7359c1578881ab6b49a0e257f2d2937dac3185969b0718783350dee706f5a6a07600440e0aa45a0deb4d522cb251ecaa8942d36838a91d8aad23a0e307350fb02c10341c56ab06395e1b7c1bcf5e2db38fb5764f0c1dc5b691f5e1a8551845710662db159cd5b46fa04ce627af87726e91619aa661a930c9be833880e0b137ce6261d7b7c23d7aa8e7d03a2d7374ac86e91dcc3d93988b45b01e8c3d9048c1a17af9ebe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part148 : Excludes 0x80040000040000000000000000000000000 0x6b2ae2fa8a8000048030008000008000000 :=
  finishCode 123 0x771a46c03b61eb571d0398937e165977c1b682990665df06dc809391b85a6a08e06db98646acd5b523bb0e83c110035dac700a45b6a25308b56cc52a2b4049cc56c838c3d751fc1c65a6b56d88520e85e103a2e18e629fd969a61f9282731416af9062d9100f5cf5f1cc5ecb276c912a2b16bc402dd920f06f398ad3614b972e0ee2e3411cb491e3937c9bf2d34e6262b95f234b6a3a7bc5c27317c1e05f20c732cc433939334e2262b570e2b20dd00e5b398866cb40cad366ad9334deab338e628198e62f03e0b21c7cbc734ed20ac0f5a69c9dcb72065a52b4d3d7c7311eb9c166aa9cc47aed82f0a02887315b11086147eb4170e7a8b964f5e4e96ada91d44ab4d3eccd2b6afb56cdd29e31f9c60e3d7b57cd9af71274b56e3071eed6a28cf252a0b548e2e1515a87e35cb90d63ae651f9b56e084f218374a206d98e6a92f5a6be0a478e226d998573dcc5863b91ecc310719cca83336c9c4507b13a581b1b64e6a4e947218611406711613cb4d6b0b0fe6afbdad48aa039026a2b5d2186afc4e937e9cb47d69a2d2672c8f6d02629389d26e90e1b48d48f399566672d861a8820e4409be0c01c458ab0f64e5ac5593ee3f371ecc5351f9b65a773554e22c551f9a3872d87d6907724ca115a6c1bd25ee59611648c2c9070e18fce006a9c9f71ec9c15a470134fe706f605b0ee30b354d3ee6fd3d7cb2170e6ada87dea272d1f9a409f79416b518c2b0ed87a82369cb58d43f3d4504671f (by decide +kernel)

private theorem part146 : Excludes 0x80040000040000000000000000000000000 0x6b2ae2f28a8000048030008000008000000 :=
  splitAt 1 111 0x6b2ae2f28a8000048030008000008000000 part148 part147 (by decide +kernel)

private theorem part144 : Excludes 0x80040000040000000000000000000000000 0x6b2ae2f08a8000048030008000008000000 :=
  splitAt 1 109 0x6b2ae2f08a8000048030008000008000000 part146 part145 (by decide +kernel)

private theorem part142 : Excludes 0x80040000040000000000000000000000000 0x6b2ae2708a8000048030008000008000000 :=
  splitAt 1 115 0x6b2ae2708a8000048030008000008000000 part144 part143 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part150 : Excludes 0x80041000002000000000000000000000000 0x7b5bee7087d2082045004c0020800001000 :=
  finishCode 39 0xda350be3a1061c9419f2d3525e81d171987cc56ac20761689c8546328cd69aa62d061f40ec2b3411937d69a4df969e7315a7c62b40ea0f5685216040eb6061d265c5d5398abce7b49ba625cad358b683d4f1cc81099b2d343d6731501c0cf254ca395a6a80e0679cc499b204cc3a1eb398977e2e2c61499a73137b9c85a8531642c0e6261d30fb16e579bd94dd306f95e6a25964a4e930ead367b4c4e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part152 : Excludes 0x80040000002400000000000000000000000 0x6b0bf63485da800005840c3020800001248 :=
  finishCode 93 0x8620c671485912c6d0dfa71972031334c5ed272f122ca11725a475a622319d08811c6d2004959c4e06d9ccdcc739441b6a608c447a73560fc8397b4b54589e3d99c767b17b4a38d3e28399ed25a92e288c447a7353908b8e3f9ad360de72f06dac966b2ad3cdd2735821b4800e4b13a458e7337320e720b43d681d96a2de400ae27a51c163bda638fb5667b49ec66ac933d6a2f69969aaf75a888c447a71f592c4cf38f93a544b0b1ddc74200651c88201b660795e2b51399a09e578ad449d2b09944a61f17193a60f59c956a307ac3d70b1e3999c7ce5ab2440ee3a0ca41b60f5987dcb2919171960e42465cc73da5a4a0db3908f66392c1eb495b98e6ae87aded3351569e92b59ab91e5a6836c5c68239edea391e89c94e669e2d0ee2d341ab20ddc8ee6149cc0c781b6823899e8334a283341b6da3a0b037872f399a0ce4f8ac7c1b706f8e432c241b7063786c59206d657b493a5a8ab0949c87addc730c61f419c6c53ecac9569f24e52c274ac261ebb084c3f2c25812d37 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part154 : Excludes 0x80040000002000200000000000000000000 0x6b0bd63584d4205005200c0021000c01200 :=
  finishCode 65 0x10c418ce259101bf4e3302340731487cb1f274a4f47b2f638e26d3189d293d267bd8e1e887ada8821945c182720745c6c5b39ac40e635967b898ad1ea0db398a07626ad1857b6c60d69a80d41e8ef63089cd64049cc41b710328d579ed2d315a693a4e6283995e2b3506db9468c292e41b6d42c0ee2a01d1308ad3e83887adc821b91e887ae62d97864f4ad3dca2731495ac7da6f1cc43a21eb9cda015389a7c527a3d165134740e873186a1d162da05e4149aa45a29f1398a0a63548b453e24cd9cce4df728a04cd52b4d0e8a91e062bda5ca2b4d61aa8767b4a05c1b6b4d398a4ae0e8c40ca3207316a0c3b07458564cf87b24e9397bd464878675a62b0350a818460dc9846267933e698937c34a4cf9c8a7134f8bdc5ed2d376f09ab31441aa1eb1e8c1b9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part157 : Excludes 0x84040000002000000000000040000000000 0x6b7bf6b184d4952007010e20a0080009000 :=
  finishCode 27 0x22065140640e62d0285e0e88f64e671874923293542ed31771bc6d01ab07ad42f1874e2f18751d73d4c3a2813274b68de1cce0f59cce698933dc8a1b93089846691c80f5b50e518db67254198744987357ce662a989aa6ed9672a4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part159 : Excludes 0x80840000002000000000000040000000000 0x7f4bf67294dc813007088c04a0002009000 :=
  finishCode 31 0xca2d09e350b4d5d154398ce3d50ea08d07aa420366aeba0839a0f2733153cd80ae60e88b4661a9335ea2ee1fa625c933548f360dc320733943e0db0e8a08e06d8ae4e62d318e6673106dca33411c08e81cc4e670b2d6a3352c99a0c789720db504c1d149ea4641b6725 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part161 : Excludes 0x80040000022000000000000040000000000 0x6f9bde34a5d68121470c0c20a0001119000 :=
  finishCode 27 0xe4350a4440b03686115a8c90f1de87ac4b32c95edf183599b9453d27350e8ba0719389c93d69bcde07449ab38f4e320d11dece61741b04a2c827578b91dc8a0d10e8a8ce72287ac3d7121e25c836da852055f2ce474a61138cc0872d832649b7b6b4dc3d64e9812713a43d6d65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part163 : Excludes 0x80040000002000000000200040000000000 0x6f8bd630a6d4812217005c00a0048029000 :=
  finishCode 75 0x104440ee350c82c8da18adc8741bc6c1cc79144b2d3c1b61eb5218871c6525e3c18e62b4b068a08e4048314c3a61d83d680398b671930e87ae2668abe613a7d638cb10d8b673130ea0267b0a08c3d61d130898a5bc6d204259cb3341187ad2c526820e6288b1d8131c7e839c8133099c6604671bc4003d6a02c8e266a4bcddf247499a6df9ed660740200266ad2637ba42ce66af19692d2382366d17b5c615cd660738bc1eb5a7c713274b38d42c8c81cb49d3289569e731944ab5189d273189d27319c86a1b86c184334e41a28330e8a90f6f983a80d38cb98e7b787ad543d4c475838bdbc6e280d5a7b4e42f32cd528a81d5a79336157cc27771cc512c1eb584ca25512cb09 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part164 : Excludes 0x80040000002000000000000040000000000 0x6f8bd63086d4812007002c00a0000009000 :=
  finishCode 99 0x9e2d09c2d35b06f1a4571b4163b99021fce00898a4f8e4e94fa9cc524e1eb6a1d05801a2823890a1636a893a5233058daa262b9a967f3944ac09274b2100031524f35749d2823947f302524e71f83a27357919c512a8fe6ac9cd543aaf90f5ad449d307393ead2b0f5b57e59c93a57055166b036ce5a81da30a9ef398a934c562e3266c81d584ace41b6b2258a33894a6fd38cb50aa133630e8ef507a73572898ae474b10daba81d25bcaf972892e5ca313a5bc5703d71f1dede5c74a2b55e7318b8da9690f5913c7398d5f2e512669c656a3398cc3ad42a84b996a27094faa08d066c82c0af781b661d31485fe621a504c5718384d65c540e836da0592002e2cd652668b8cfe71334e272d241b6d519ede6fd837836e04501dc398c10d428962669874c26d5f8c0e4cd274c6f53ecc4951ec9cb49d2a43506fd839c9f57288344e6b07383d6f656af981c99ad2251625b93a418e4e9961272d641604714850bcd5749e9875e406dc9db303a8fdaaf282641cb4ac7b2d5759ccf6506898ac5c7280ddc6f20406dc73150ba9343d63d1949a4e9961ef6738cb944c3aa3f8e3e731 (by decide +kernel)

private theorem part162 : Excludes 0x80040000002000000000000040000000000 0x6f8bd63086d4812007000c00a0000009000 :=
  splitAt 1 57 0x6f8bd63086d4812007000c00a0000009000 part164 part163 (by decide +kernel)

private theorem part160 : Excludes 0x80040000002000000000000040000000000 0x6f8bd63084d4812007000c00a0000009000 :=
  splitAt 1 101 0x6f8bd63084d4812007000c00a0000009000 part162 part161 (by decide +kernel)

private theorem part158 : Excludes 0x80040000002000000000000040000000000 0x6f0bd63084d4812007000c00a0000009000 :=
  splitAt 1 131 0x6f0bd63084d4812007000c00a0000009000 part160 part159 (by decide +kernel)

private theorem part156 : Excludes 0x80040000002000000000000040000000000 0x6b0bd63084d4812007000c00a0000009000 :=
  splitAt 1 134 0x6b0bd63084d4812007000c00a0000009000 part158 part157 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part166 : Excludes 0x80040000002008000000000000020000000 0x6f0bd67084d5952205095c1060c50201004 :=
  finishCode 93 0x6a168681b86c19083037a1d1348ce636a5a89569727d4ff2b4f4213883164520e5a3bd9a6272726acb4d5a8c3bd6a5c80d165ad4501b1a7d03a0d1592cf670f5b974e124d58214865128171cc5b0d68ef503b063d8e731b4c4c3a9f1986a5bd5a6b98e3feac84618dbed4b837bd9cf5e0db5849cce5a8836d613241103b87f99cd6809641305a6c3d9406c5a9512b54d69b354da44c03d6d3187a2e6358fcc1d5a7c1c5a7290f1e8cb4f4e164641283352d63eb4f475c9e9698a7a638487adcc72d35dc820c2318756971cd56971cd59c4e144b1cb49bedc0346393ad44f5f34ad0127339682e1a05a6a60ee200942f81eb9ede28d698b98d48ea1d791cc6d539a6ee4b2d4c4cd0f5cf63731b4c564b07adcc62e35a8c7b17b5a7c5a624df523cf6b50fa42e592ac8d319a96d028960f5b98cb0b1cccdeeb256710026f9fa6133a4756a2d4b266981e3eccd23 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part168 : Excludes 0x80040000002000001000000000020000000 0x6b0bd6f0c4d489202d081c0a60050041034 :=
  finishCode 55 0x40910360ca3b87318217c309cd4b41398a54851fcd6530e93a651fc1eb274c71f5820c771aa30f5c9d21eb30887462749cce26fa4643a27803460e8a8cdaa293d83a2b2291042c0e8184563f133ce2ed65399a50506724f648eabe41b6d65584c62b961aa31519a4856121eb8c52611791b86401b6d83281d1728c833728c7fd59230b30d4e67398630af510d6a0ce30b2d353d34615a623d75a787adb87b5cf636a88f5ce3283389aaf6b6988f5d9c681b440bb9165a692e581e4df0688b1e4fa9846308c0db (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part170 : Excludes 0x80040000002000000000200000020000000 0x6b0bd670a4d48b2215085c00e0050021006 :=
  finishCode 83 0x1bc5d1b04e12c58058ece3704df607c4a5261b0fd28a5ed066ad3e3ec97b4e4a1eb8232725398ad2c7b2c3f928ac39068b68b03990220e64049cc43d6b519612713604b2100461669796a5072e47730a894e66b4b9812d5d0e896a66b2c927604836ce6b2d44b52f20f6641c8354e621eb837c8237b1b52499ad3961fb14538521606a14059034a09d93e20a14a2ac7c3d717e5066b098c2294581b67358ffab09722c0db4a29ccd612f21c860f5bdae39a8f5db0880c02418733145cc62dc9f162ba89549a731526c90362b8744c570334e621eb878e90361fb1441b73d4501a6fd584b28b42e8d42c083304ec4e90de9cd6591405c230b24bc99a099050a58691389c475262bd44b5312dd28348bdac72b41b53ea4a51aace6b5a4b48d3e31859ed66914f8a807ed85722cb362cd41cc5dc46fc7134099a7ce6ac1d3158746691b16ce6a713894ab01ba4e6717549bee458e42d37 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part171 : Excludes 0x80040000002000000000000000020000000 0x6b0bd67084d4892015083c0060050001004 :=
  finishCode 95 0xd83da574691384b108163b502a95c105b291c77a1d171fc6f71dec6162749bf569ab02484d589be1bd8e272d34dfa78120b0167581292135626fb91e308b91e731c60dbc8019c7409be9f196a273306da8e6723a49ce67249cc220a18e629f1493ae0b0f964a1bd4f8984625ba90b01d0d421081d8d9ae3d0d28ef4c2306949aa4b78dd2b4d0f5cb098c1ac949d2b4d39a8694e27036d83f3dc547ee470f5a465612de3c873390720d539887acbbf3145946a1ea31c4dc8ad5f398a0ce005a6b57e1e49c4dc7f357cd3e4cd389c69f0e89e0600a7662896a453b281102d36398b789ef905ab4d58fa0b65a693a64169ba42d6719584ad353c88169a2d78e62d65872b07116ba7c4f632c7c24a72d61ca7c4e62b2270a4378ba2c26204999ff60f5ad443d7161524e9f10d2c6a95a6a50a02101a95a6c7132669ff499b1c4dca3357dcc6d318e4eb4d4f88b8d6133c9001c4e4f887ace42e5183d6b4d261cf51490b54e7b098453e2733 (by decide +kernel)

private theorem part169 : Excludes 0x80040000002000000000000000020000000 0x6b0bd67084d4892015081c0060050001004 :=
  splitAt 1 57 0x6b0bd67084d4892015081c0060050001004 part171 part170 (by decide +kernel)

private theorem part167 : Excludes 0x80040000002000000000000000020000000 0x6b0bd67084d4892005081c0060050001004 :=
  splitAt 1 72 0x6b0bd67084d4892005081c0060050001004 part169 part168 (by decide +kernel)

private theorem part165 : Excludes 0x80040000002000000000000000000000000 0x6b0bd63084d4002005000c0060000001000 :=
  splitAt 5805 87 0x6b0bd67084d4812005081c0060050001004 part167 part166 (by decide +kernel)

private theorem part155 : Excludes 0x80040000002000000000000000000000000 0x6b0bd63084d4002005000c0020000001000 :=
  splitAt 1 42 0x6b0bd63084d4002005000c0020000001000 part165 part156 (by decide +kernel)

private theorem part153 : Excludes 0x80040000002000000000000000000000000 0x6b0bd63084d4000005000c0020000001000 :=
  splitAt 1 81 0x6b0bd63084d4000005000c0020000001000 part155 part154 (by decide +kernel)

private theorem part151 : Excludes 0x80040000002000000000000000000000000 0x6b0bd63084d0000005000c0020000001000 :=
  splitAt 1 94 0x6b0bd63084d0000005000c0020000001000 part153 part152 (by decide +kernel)

private theorem part149 : Excludes 0x80040000000000000000000000000000000 0x6b0ac230848000000000000000000000000 :=
  splitAt 4753 120 0x6b0bc63084d0000005000c0020000001000 part151 part150 (by decide +kernel)

private theorem part141 : Excludes 0x80040000000000000000000000000000000 0x6b0ac230808000000000000000000000000 :=
  splitAt 1 102 0x6b0ac230808000000000000000000000000 part149 part142 (by decide +kernel)

private theorem part121 : Excludes 0x80040000000000000000000000000000000 0x6b0ac030808000000000000000000000000 :=
  splitAt 1 117 0x6b0ac030808000000000000000000000000 part141 part122 (by decide +kernel)

private theorem part117 : Excludes 0x80040000000000000000000000000000000 0x6a0ac030808000000000000000000000000 :=
  splitAt 1 132 0x6a0ac030808000000000000000000000000 part121 part118 (by decide +kernel)

private theorem part105 : Excludes 0x80040000000000000000000000000000000 0x6a0a8030808000000000000000000000000 :=
  splitAt 1 122 0x6a0a8030808000000000000000000000000 part117 part106 (by decide +kernel)

private theorem part89 : Excludes 0x80040000000000000000000000000000000 0x4a0a8030808000000000000000000000000 :=
  splitAt 1 137 0x4a0a8030808000000000000000000000000 part105 part90 (by decide +kernel)

private theorem part59 : Excludes 0x80040000000000000000000000000000000 0x4a0a8030008000000000000000000000000 :=
  splitAt 1 107 0x4a0a8030008000000000000000000000000 part89 part60 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part175 : Excludes 0x8a000010000000000000000000000000000 0x75fff0280880a3140000200000000000000 :=
  finishCode 23 0x3b0ee3a8d203a5b46a03be921cb504b34ec98280b735c825388b556358b8ed04a80b396c7318e5ae631073151fca1169c82fd626825171abf6594a095b8171c825470d87136d49b075a30a19d493a4cd89a18d0dda0ee0da9cc4e2273185b272d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part177 : Excludes 0x88000410000000000000000000000000000 0x76fdaaaa4a3123108208200000000000000 :=
  finishCode 19 0xfa348f0078c7f6c63707319ed271f39aa38637ab54c9f24cd6a9c731266c5c5398b18dc1cc60d39cb4e6a801cc637a9ebe582bdd4e62a41c2e839b9254927fd419a86e5248eee4a19cc49f2735 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part179 : Excludes 0x88000011000000000000000000000000000 0x76f5a72e988023331000222200000000000 :=
  finishCode 23 0xd23e8f4356e388902c1ce41b6113840db2883b7f07f6d639ab6f690f19b0e6b19b0e6b1b98e1fdbda6651ac73da53b671f7b8a40c38650d4e1cc3281dc86835396a81e731b2841d49079e50d494d1857b4869d1d73db4da7073361ca077b88efc79e3f5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part181 : Excludes 0x88000110000000000000000000000000000 0x76d6b6e9882333100222200000000000000 :=
  finishCode 27 0xda408d230041b1fd9bf6405a48528a8fd9016c5b9ab6e655159b64e6241d6319450bca2b416874d886a1a7f0f3c9fac551f6b15661d82a5ed24fd6a180510e6b183859a4c59a86f698c1cd3b6acb5760f7355459b1837319bf5e827eb28a11907ac0d9a4ad3b1f686c6692b496583b585abaf6904d90552624fd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part183 : Excludes 0x88000010400000000000000000000000000 0x76d6a5aba92023123100208208000000000 :=
  finishCode 73 0x5d188810a22ea35268c096ed20e93320d8fed0371ebda92d63398b187a0f3c37eb2998a65c5a306c258c0a4bd4868125e9410c2cb1b358cf7583da77d62730f5876e4f1e1ba9020b6620d8fed380ebab8963da459ab07a302b556aaa77cdfa1818c0594ce63471cb3055d6aae3b6b0c60e594c1c52c7b4931658396bd667408a22b896206ce6292193be933076ce598bc6d5b41d83b65712c0dfb56e5aaa77c79ee5996265c372ba77dcc68039ae71db56d6aad5ba0e3023d0ca28fe3d8970d65283b076878ce62e59987ad5b076906dfc4a0c82583c9335ed2d5b0f18a7e24b9335ed2d5b521886e127aac3da60c2b56d8aa1d7807eafd4978b8dcc3075dab692f401583211859fc1c62e1ac4c332d5b87421d78379ebe837b98dcdad5b0eb8f3e83897ed5fa48347cb56e561ab6d55a302b13838c8e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part184 : Excludes 0x88000010000000000000000000000000000 0x76d4a529480023100000200000000000000 :=
  finishCode 111 0x194750a425256d1cc69dd07b7b4a4343a61d75d1ab72c0dab21bb1fdbd0a61b0c8265bf93deb516adad1567738f4d872387310d1c9056adad14bf693b81db1cc5887a0a37020f3e83c9cd53d2d631fa9015487f091a3ed1dfc2ab4a0c1be838b188841be838a709e1cb567741e4f5e5cd1e7bdb65aac1ed626c3d61d8e5e7b4bda67f11c4e10773da436a9074129c456c6b10571335ab6f694a0a464ec7b48e1e09aad25ac6e63a0e2735361ce6b48391f5edaf6940dbd968c1c605ac673571ebda504ae3d9ab69f97b486d5aa6d637f1f0751805d0e5a73520ecb3f490a0ae306e3d0cfa925ab72c7483af69842044e01da711a0f6d614129b0e583a3f5cc68f34e0e2341edab30f3ded2415a04561cda8f3076a0ae5a2c1e66aca98ba2b0d5ba0f2b45503a8bc79f41ed1f2d5b503ad466ad96351e6e6383cb566731970d7872106a81b924ed5960da3e636ca06d40f0b66047518020aa782d9583cf696ad93353f320edc868f39cc6d5540da88ba206c33f29250773965ab68c357613d8aacd4341f63063bf300c4511c8ee63262cf6d1dfb565ab6b078f62d593c0dc59dc9f97b28e8498a84057659d85e4743460cb1ad5d592cf6d1528efd745315850dcd5d524b5667b48b3540e4979ab2e5f892ef69 (by decide +kernel)

private theorem part182 : Excludes 0x88000010000000000000000000000000000 0x76d4a529080023100000200000000000000 :=
  splitAt 1 106 0x76d4a529080023100000200000000000000 part184 part183 (by decide +kernel)

private theorem part180 : Excludes 0x88000010000000000000000000000000000 0x76d4a429080023100000200000000000000 :=
  splitAt 1 116 0x76d4a429080023100000200000000000000 part182 part181 (by decide +kernel)

private theorem part178 : Excludes 0x88000010000000000000000000000000000 0x76d4a428080023100000200000000000000 :=
  splitAt 1 108 0x76d4a428080023100000200000000000000 part180 part179 (by decide +kernel)

private theorem part176 : Excludes 0x88000010000000000000000000000000000 0x76d4a028080023100000200000000000000 :=
  splitAt 1 118 0x76d4a028080023100000200000000000000 part178 part177 (by decide +kernel)

private theorem part174 : Excludes 0x88000010000000000000000000000000000 0x74d4a028080023100000200000000000000 :=
  splitAt 1 133 0x74d4a028080023100000200000000000000 part176 part175 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part187 : Excludes 0x88004000400000000000000000000000000 0x76c6a0f2b12048023900080008000000000 :=
  finishCode 145 0x1942e13c81169aea2e8de0feddc671623074d4725110f1bc09829082288b315a9b56e61bb98c9166ab983e2d91aed1853dc8b6528ab276adc7af96526a35888b4c5b2e6b8af70738c2ac766adad4560b3f8de3c01e3581ab6ec0f242d32cfd02a38f4a0931659f981e8c2acbe72cc61568a8d5828f18157eb4ed65e3c96adb93e614a85e30b07351c981dab6a62c8b3187b283b303a42e59f941d60f41e5206d5b588ac0a118c0e3d927eac4e303ba9022c8dc0fec3333da4c0ed3b1ccc6076adb78ba330f0300a21f02d36718968158c2cb056b1a516616acc589f1858c2c815988290b4a2ac4630a1e38c2c1d383c7185697cd5b6b194443c6a4da30ad5b69db486598b10ba1f1657eac4630a93d27ebda66adac4e303a98ba181e283acfe62cb56e30a90b303b56e4feac4604751bc1fdbb8fe3c01e34e102b0f6528a7241ce7b48f65243079800ac373dcc1d60e718516cc1ce3e9c61582b28fe30a2d90e9ad4e4edac15aaad5b592944560b2c8a63b882b967e60741dc1b3283c1e6722a3f4ff6d65593ad4e288ac8b538bc60a5283981d9c2e1cb2726fb56ca0ea3f964e3d95e144541ab6b2208e61963ab314a0a06d056962704fd96668354a29803a99622921837c5bb14cc6047b32609c06064a2b8ee3023c959886a5cc716ee3023c95a3c6068c0cc42e893d67035312ddcae2d9288c6163d780960f22d9736ac45ac71ee567f1811e4a42d184e11f32095caf1ee60f23c91b3d0791ec933550631881698b65caf41e521651149eb58683c8f3d605a9c6ab288b916355a50588581c9f1444d57067d27b1819ed23bf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part189 : Excludes 0x89000000400000000000000000000000000 0x76e7fa90a02080123120000008000000000 :=
  finishCode 11 0x651b47103c71cc47f640b7f0e62d5b8746c5559e9fcc1ceb479ab61b351fc81507393f4e62e212de288a02d0560dd2ddc5c56b29315ab60e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part191 : Excludes 0x88080000400000000000000000000000000 0x77f6ccd4a42002223101000008000000000 :=
  finishCode 113 0x791b47116420dab0ca20ad0769ef837ed5b398b04669bb52d40461ab67314a2cf65361c6042fab33262a5168c08e3e361c60477ed5b303b28d53902ad5b283b0f4e62d538b02e596ad9445945e1405f0e62ba2e01b35a1886ad828daa3309498b312cd86f699636c115a39b0e6adb59661eb165ab67e59ab6be2d00a38b9ad5b361ad34fe71b0cfcb356cb4390fe66c398963a32ddbda544b31556371734f72e59599ad34bc35ccc250d4b155a96d65621384511c49cb56e2e2ac9d8822952e2cd5b24793156a25c59ab73155ed2d3772cce6b6515c5d178710e626079076a39969ad5b390727202d866f69581ac330b563a4fd0c0cc2d4efabe4d770734669cc65a6ca2541d93f560487b5963f2b56d28a4fd3eacd4b2e6b56d28a543609c210ca1735405d0e623d9988a6bb9ab67d55a6981e5a6ae8d5b4a2c3d9622b52648181f6302bc2b8d5b481c5817b486a5822e5949c9cc54c6b2c60712fb5249e6e5995c72cce6b46f8245272f69279ce595e0e63356ded32e8ca30a60d9ad1cc0e9279aaac2d6adb56e8c0981c99ad556f15c63124eea067e16cac0731234ce4f8c08f6490f34ddcc7460da92b4d6c0e4279c1d672cad358964c59eae6c38c09fcdcb27d535cc1a9625b0a658db06d69a1b3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part192 : Excludes 0x88000000400000000000000000000000000 0x75cec090a02000023100000008000000000 :=
  finishCode 125 0x330ca148e04501dc398a78a62d352c594cb3f6adcb132e2cafb6b28ee47b27d58d76f6b51f93ccc0e4f3969ae22b0c559606d4b59f83b505683b283c81b303ad1e6a583b569aac2588e2ca567eb4d8bc66073d7c4c51ecad3564711a0303b103d97b6c4b9589ac145c6b4d9ebb34dcd62c551ca95f56264f35a6b20a0398e233ac4dcd6d372e6ad347b246796264b969b973569a5cd969ad653e2cb4d62aac4d3c2e1645a6ad8607838c12f6adabe525eafd27982cc5c72cce508941d1c57eac76582b56d67a59f303ac161718f64c0f0f655fa4f3510a8811ab6e23c89e998aa0ed3faa0ed4c3eacd372e6b58cb8ab3f6b1ce592e2b9665aa973582339649e6c531ecacfd4c561e44b188594acfcb8b20ad8a65c39056c5387b20ed72cc4f3838b044b8a0a959f9709623e498b03b455e4f38d86c5957ebd96731bdd41da2af57eac9e6b183b564401587714c1a6cd4b61eac4da6e0ed59fa096076b0f5acb30f52828f981da92f69bcc3d262a09527aafd93d20ed288c08ea368e22f81df2018b8e2f7ad364701db0f3ce62b1159eaf0aa356ce620ed98aa0ed81db400f02c00e9526c731288a80e398c6167ba9cc4c0e7fb288b88b22d56165981c1bf0246627820568ab4d53169a7310dfca03526981cff73945406a4d171b88e8428b05987ad5b2e1ad341ae51159fc6070ebc4fd6d0f45a9a8960dbc6156aa4c562aad08e99cc24c5612c1b71e7cb2f59d8e6d69aa25 (by decide +kernel)

private theorem part190 : Excludes 0x88000000400000000000000000000000000 0x75c6c090a02000023100000008000000000 :=
  splitAt 1 127 0x75c6c090a02000023100000008000000000 part192 part191 (by decide +kernel)

private theorem part188 : Excludes 0x88000000400000000000000000000000000 0x74c6c090a02000023100000008000000000 :=
  splitAt 1 132 0x74c6c090a02000023100000008000000000 part190 part189 (by decide +kernel)

private theorem part186 : Excludes 0x88000000400000000000000000000000000 0x74c68090a02000023100000008000000000 :=
  splitAt 1 122 0x74c68090a02000023100000008000000000 part188 part187 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part194 : Excludes 0x88000200000000000000000000000000000 0x75d48511408c40001000000000000000000 :=
  finishCode 107 0x7a1c8781b86603dac4073628d8fb47faca3005e3969a517290ac866ada0ace62a62095301e7ca491e7d0797b6d07d5069734e631495c46b160620c52f241d6499a894376731076a85d64570c263a7895306b589a40ce62a49a0f2b4d6b297356530798d5af5d4999cc524e4f35a69cc657ead541da6136adc1bb30998ad48292c1f650b9cc569aa25302acbe2608ad5472b4d2fcc503398b88b2f989ab4d1eea0eca1a521281cca3c8ae1c873185169a0ed8a2e61385c69c149455f184d472c1d41aac46061b1356c770a2e8258c563d9969a62b834a5255a6a8d66b29aecc56731671e4161c2e183c946df0524c4f330893ce402c825076b78ca338b039ab61bb5a698aca425255b15828ba3665a6a0958b7280cc5662b969ac42e8b0146d808c0c6bb483b4fc3721c96aec8158c0a0ad606e61483a0966aeac0815904b18371e9235ac6b452f6872538560b9b2d1504a9078242d494959b9c6932bf5a928e7597933558581184c104ae63968a3d9308b57683ca48683c8f6541b395daba4a1412ac0b61286308b4fc5c24a190371b9d885d19c730a0eac2c6d68ed5d9ea707b510a4be2e6931504b20165a98a1662da0d4bda5cd262c17d412b564c2262b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part197 : Excludes 0x88004400000000000000000000000000000 0x76ecba72733108888000000000000000000 :=
  finishCode 43 0x7d1746f07f6cc360722a0b4d7405b29396aec6c360fa8bd89e3d90f1c4f9816ad596705b32515436a490f1b56e1eca5145b2d5b96a6b4d0f1ac6e0f1b50e524ac1569ab4360b4d6e1cc671ab70f6526270b0f1a601c18c0c8df6ad8f660e71aed206b3f8382ac356d6ab13e56323d98d871810f1b56e561ab6f6d9c7ae4f7b493e56aa9439ed27db6316a71f6c956b4d27c8b64e4ece2b056292520b3575286a2f065c943597ac6e065b56e5a693e564eb53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part199 : Excludes 0x88004000000200000000000000000000000 0x76d7a772750509000010408c40020000001 :=
  finishCode 51 0x16052130388c83b0669844bdad63384cda30239748598a4e220cd8c0c8f90699875807b4c6067369c0ce6a5170e4bb89e99cd6e3d837ad1569b41bd94600e3f18a49f2517315cd5b5a6ac88213366ad8b8503682b7f158731076f699ab62e10b0cd5b266ac741a71335ab62e1069cf69614a0edab66bb9aa61c9651dc5f1bc315945e5a6949565f3da58b6c5b9ec2d5b286b78d5b91ce72d41d94960e3356ded26f557c9cb506a9c230ce209498b46051be71172f9c881b899a703266c8df7f01a71c0d20ed5ba3020d36b2302b558d726d37b4b56d1cf1335036f69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part201 : Excludes 0x88024000000000000000000000000000000 0x77d5afbe711248000000000000000000000 :=
  finishCode 17 0x6c194166c0d328b9485c848ac1c928d834ca0f1cd47b2ca3946266b98d28ab4d0e794353856164461076945900a1ad949272d730a516402a055cc31ebd036c371df9c0da730b25c8ae63 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part203 : Excludes 0x88204000000000000000000000000000000 0x77d6bef3730608000000000000000000000 :=
  finishCode 19 0x741886717c2839495ac255cf6958d98ad63741ed826c5b5a6a8865a6b582cd9eda58959ead34a2e62b30eb00f69859ab4d28bac0b03526cf694f4a3cd89a9431dacd4762da43569b034cc56c618a564b0f0c17a1d36aecc356ada8954724fd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part205 : Excludes 0x88004000020000000000000000000000000 0x76e6b6367503081000cc400200001000000 :=
  finishCode 143 0x178611185613840ac82558148670c0ae61cd66948b85abb1cd4a36e4420c020ae7b4834c5b2d2991fa6bb8b43181495b8edab60d3588c8f36b1cc6adad4650d8b860d72d25436b299056b4528db60a2146ded3356d056f7182520d347eb5745b2d5b899a82b7c1607f19c6305c2d639692a0759d8724e6a5ed948390c0ad29a30281b692a484b771819a524c569f9c86bb9866d5b381b90d5b479c6bb266b51d85a2af9eae3d9696a464d76d4792666056f1b06b019b31741a6c5d86bb07116c946d044e1036c1595f2d2d598d0719ac6d5b8c2acc66a3b10ce206e1b6b585ed292b283acc4a36821a0b5393d2d476b0b4a60e4a4ae69f834d5fb35841a6fe338b2318a42c9e6ad8b84c2272739aa7072d907682b989e2e16adba0611920e51b308cd598c221bd1708725bc4b1c86c128a0d385b25959ab646d125bd4dcb2921511244e1a53460433e5bb41da0ae8c09845ab6611a0f306e4c22d55985ad5b308b5864839845d05b01a6945877eb31985a61160fc921308b60e43381c9308cb51837ad1deeaa1b5249cb4a0ed6356e8c0a4f52320d3381c3c1266bda5f08013828d8f6562341ece069e98c0cd5d7b4aa8721cb437339b60f67035216a70d35aba581722c60527ad5b9c8b181524cd5b308a014d772015ed293d283a9266ad984600621bc720a369c393dcd64fd9ed280b4a2a02e731b56560aa60f3e14abda49fa8d99abab314909faa239168c0b4fd49280b722d181730a81d486d3f9ed30755a9b93d636e3d722b90de3a0f6994367355248b641a6e4f9896d3f8e6a80b940e735381c71f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part206 : Excludes 0x88004000000000000000000000000000000 0x76e6a632730208000000000000000000000 :=
  finishCode 33 0x308ee0fed786b069b2d3585a91f2868b85ab661d314a604e58a2e6054a1cb4d292bda5bc6b169b23f45a60c5292874d98292a3f659dbda56a31bd49fb360b058a4a8f18342a0d58da05564e5ed5928b85b0801bc28bc525598c805495a4f4c525076f1cc6b1ab718743c6e43da4fa7290d8564cd5a4a485266a1b969af6d35d9bd49ca0c58c522d9598c61d30ec629 (by decide +kernel)

private theorem part204 : Excludes 0x88004000000000000000000000000000000 0x76e6a632710208000000000000000000000 :=
  splitAt 1 101 0x76e6a632710208000000000000000000000 part206 part205 (by decide +kernel)

private theorem part202 : Excludes 0x88004000000000000000000000000000000 0x76c6a632710208000000000000000000000 :=
  splitAt 1 129 0x76c6a632710208000000000000000000000 part204 part203 (by decide +kernel)

private theorem part200 : Excludes 0x88004000000000000000000000000000000 0x76c4a632710208000000000000000000000 :=
  splitAt 1 125 0x76c4a632710208000000000000000000000 part202 part201 (by decide +kernel)

private theorem part198 : Excludes 0x88004000000000000000000000000000000 0x76c4a632710008000000000000000000000 :=
  splitAt 1 93 0x76c4a632710008000000000000000000000 part200 part199 (by decide +kernel)

private theorem part196 : Excludes 0x88004000000000000000000000000000000 0x76c4a232710008000000000000000000000 :=
  splitAt 1 118 0x76c4a232710008000000000000000000000 part198 part197 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part208 : Excludes 0x88000000020000000000000000000000000 0x74c4d61445010000008c400000001000000 :=
  finishCode 135 0x7f2106b1f0291b60e42f01ed402c2d938fb12c3aad599216b511cf973481a71f67148517c1b96ad9844e6b002604f328dbda6524b54545ef65a0f249b6adbda479f07d879e7d56ada8bce5a9803b4e4308b13e4029c0e0f6f7593ca907900a92b7d214721ecb1b0dc9e91d6a5b8f47fa40d670c22f698e5ad65076a9260f703b58820df8fcab51074b910a2903f54b150393ab84cd838cb534a2b07e4f2a43d83f2795cdad5b1a6cf697289cd53ca921960a4cd242a8bdab65c1ab658dc1bd2425e17b8a0159c5718373da4b76e3d4a2c1e479e7279cb290f57dc3e562c9c7e6adb90f239160e6946c83a0cd839a9f1a302d5d83da42d00a4f3811f0851c838fc1d50ec9055dc7d184076b18825388c80b396a7ce722b984e5b2014a371cb4a0f037e40287543daac141c83a9e59ed2e457a9a77504ad65593c6bb5a9cc551f69ff4a361ed621c4721b020aad01dd479cd3748eb52ce222d31fea3891d879e9f396aa91d732b9adc7a57f9ab63cf388b8f52323fd6714869bc7193029cd538279c7d5479b56d45e83b396a380e76adc919597cd5b35da01641a839d68f16ed64ed5b2f6877481a8358e4e0e720abe9023c8d8103482a5407b51fb34fc4b6d439a973105c8ee6b2fcb483fd598c6d362cb91dccae610ee8b4c3bb3a0e6194861cd28d87b5f05e118308b50e0aab4fc7dad372fcb4961648fb5a6eda28805d96a6e6358db155c9ee6b621ed3350c98ab5362ab98e6b0c8f372f9b4daa3314da4ad3b61293cd580f6b083f54913f3292587a82b44181b41bcb8a6830366aa9784f5f30a6517b8f5ab6f713b099b30dc77e92390e15e867dcbf3da496a921 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part210 : Excludes 0x88080000000000000000000000000000000 0x76d4ced4460000000000000000000000000 :=
  finishCode 55 0x408fa310da0ff481ae8208d8372924c3eb4d0f6b06e5a6b0ce5a6a4ec3dad810555048f9cc43da6c59ed2d3f490bdb6369ac1cf728c2f091f8bf28039a4306dd262f69781680f6ab0c20fd4a069239ae1d1a50e5a6b9adc7ae6b8962b4d5d19c5c034e1c71dbcd2f49d8efe2f0c1a3625ad36838cd6162cb044592503281ce820ce1f694943daf8388c8298629419c4f330fb15641e831d637204d22e1d36d19062178164cb530608fb567b030505aaa350e2fc8b25a7e803694c5f9694c81d4988b3662c8ea52628138182833 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part212 : Excludes 0x89000000000000000000000000000000000 0x76efd210420000000000000000000000000 :=
  finishCode 109 0x1e4721d8711b8315c52520a9074c53039c826dc3a040d731b4073a3873195f6b3d281c7f34199cc4a072934e625c2888335a6a58503597c1af8c1d06da306d2f6d125f133503a5f9416a8838ba0e62833f6a80ca068831665089aacddeb55a306f5f170c8e7a0e682d4eda504bf20e7281b88ba3704036305c72924e4e72d521d040ea86e5248b8d6a71c2d066d3b85c6b62f0d82904f9398b0de15bb0de058c833969ad63598a81c9f2b3d905ae495218c730e4e3c989f27310d8cb298bde731406b70d5b2f7c4e53968b8d86f13e4bde6c362cb98ba1cc53031167b356d8164f95a9b59627ca98943834e8138dde4f99a426ef4c16027caa01b5965e8331e4a076158a0ccffb315503ae65967e8336d2002019c66073b5892b8c3ab278d76a0d5249cd4e624fd8e6262b073bb0e42d0880ff49e7184cc3eb4d60dc7b962c9aecd8661f401a0cdc46d1a0741dc066871e38c984d1eb204ce5b070dccb071ce63356ce3262b6c1cd734c43ba3cf398aa8e6b9aaa1b75a3a4ad026b2794c0e1c7355249c649e661339ac5ed6adad34e32e220f63968b8d69b250daca9176ad9bbc17a731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part215 : Excludes 0x88000000800040000000000000000000000 0x75cde39142c0a028e400000271002000100 :=
  finishCode 43 0x408bc2b9001cc614761e07d03da6bb907640b515c5038a2eac1e8b5589f2c3b4109f29439a8ee4f8d86c25838868d287069e38c87b5847d1d84108163cb988682b38ccb03837cc2583d900d6065c3968ab0341d8756852004a1c4f928bac0e361a0ec806b1981be1ed38cbe9003880ed6e0806d61809ae657ba869c9f27357b6ca35692c1a34a193e58766c3882640335dcb537b69bbc3da72d070c1ed (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part216 : Excludes 0x88000000800000000000000000000000000 0x75cce31142404008c400000040000000000 :=
  finishCode 153 0x440e472169b0a3e8a4408aa3b082d41ec0040d209ad4e4a1b51e6aead4e0559bbc806ec1cc65a98b643d241d0e0c91757da50d03ab030f4c525416a0f600209c41d292904e801e06703dac61cc627c9bbce4e901c2d6372d4ce623d95a3c4f954038324cd287170e5a2a4ec9f2503398cc1b15da4e600761ed3136c1c20e90f6b70e22c0e1ec9cc4dfa727166caf92669bbd28b390d8ba73138cc0d9398be8d3f9eea1b937e9c9c1d2731201c29003c0525503c3d937e9cd4da72d156327314a1a02e7b49cb4e628d99eca83b83cb4fcdfa719398be8e4428da4606209903501a81d800a071494fda40d0f6bdd66b0b574e62a492069fb600761c9306749b60e107487b5405713016c9cc4783136c383393dcb339ace4f0f0639a87041be7317619c800e4f03a4a4abc288641a86e586a73138cc4e54feca114129cc5eeb06d4e626fd393900dd85e1c8281c1ed1f2c001a19472525508b54e0a89b84342b0316a9cc4b9b34fcdde719272940d7850150398a981a1697c29b4eead14d5b1ef56065c596aa981c9e27cad5669cb8907993bad614a1bd5c9f26fd39a891e6b1bd5d21a4f92e6b90dc3b0f83e81ed50107a0df206b51e6a9825da7ed47943734bc1b271f49c8fd507b149483aaa290ce20f58c69099a735692cb53478b54d272f6d9aa6bc350e0e0a50c56e7313d16371aee0e6d592e1b08da773db4f9ad3f4a1c1c1381b0b558201a08da5f13e5eeb358d1d67310cda88b030e0c8eb40e93e630707053ba73140eae900208d07a473960a01b72d93bc806525524c197398863e23eb984a2e80d06fbb0de40051781da525611b4694c4b150d8b84e5a40b5e198412cb45398a0d545f358565ec5b4913e706ad436f699a52d2d697a86e39abdb498a4e5398a0d60dcb0ad00a5075e0e6a4030dccd3b6119cc4d7713e55f6a07 (by decide +kernel)

private theorem part214 : Excludes 0x88000000800000000000000000000000000 0x75cce31142400008c400000040000000000 :=
  splitAt 1 90 0x75cce31142400008c400000040000000000 part216 part215 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part218 : Excludes 0x88000000040000000000000000000000000 0x75cce218ca0200000231000000008000000 :=
  finishCode 129 0x85200761b07d1c4740e6318aca42525810db303b4e6241d205be0c8289641693a50661d7314b4fe6ad9c9c3ae6d99eda5e3515875d066f03a0d5d969a83d0db83b4a061ed6201dab1ba0dac2526297e56a6b1d9abaf73907a803170940c3db140ca42fa0b8657897e41da803281904d60b0b8540e3bb0e7940df4691cc201b10a02687310dbcaf9401a0cd03b30ed2864f959ea3ee837b15581a7af4a1a0f49f2b116a3c929398a8880390664f9551abb461569a82d419acbe7c1c4520e3f2cf4e4ee80f3e50db58ce3e4f96adc71f5a8b98c43d5659da79d066b3d6a3c929398a608813e5ac339958b2b4d419c8039066f5d905aa1b398bc0c62807274c0e6306d9a4a3d959ea98d3988ced3b7329ebdccb41cdac6e597b2b575a8f245d622ae26073158dcd59836ad4d4373dcd8a6d4353181728bd1e66b159fa50dac31ee522ed5d1ec9e84f9310b6f1b858166e19eea9170e78eedee7388d29879e711314987c3c68e368aa139567a3cf969a83d5a6cb00f3da5f461569ad596b0b13d8b2d61969ad3f731a0ce398bb8ec3e9023a0e203a498b250403307957db4ed6a662b0ef984c1be4c591e23cf398acf578711480ef9cc6315b16ce4e6138bf31cc5c9f2cf43be3cf8bf2b530f6837dc46c18c0f692c638c873ce6a982985e14e189f34ec982b5388e71fedeeab53258cd4369c8a3e6978e0ce5a4cd38c936c39e1b7967a1ed71148570e4ef6d96224b11628f2da86b53398af85c585c63c1385b57565f3dd40b2b557b6b54d69ab0591e24c539897bc39e58f9cb2e4f262acf4e62b3d83da711 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part219 : Excludes 0x88000000000000000000000000000000000 0x75ccc210c60000000000000000000000000 :=
  finishCode 119 0x428523801c4791bc6c0a2f1494c3b1435c8283c1ed20a941e398b60f8390bc07b590409c82339893ccc3a629570b9b1cc4deb352da72f69969a83d279a9859b9ed2a0739893cd78640e625e195f63d90dc9aee39abdb639a9b0c7b2a63904f36e1780688b8e5a68ff50470b8d69a7318f5e3cf5a6a8d560a83346ccf693988fb6506a0b5f45e1646ad98a501b133586a6131fecb228be71e9cb5232e599cd6aa29071f728c7355a6ca3561ba8bce4f0b147eaf21036281b20dc2f01ed4007eac379ece4cd4a0b104bc60fcd656adc3cf5a9b78b5392421899ed6c4140107b24856a62d9497b60f6d8246f57409b4dc5b27317b4cb53487d0797ba862492af6939887b5ab6e4370d81035c41e7c71f1fa83645b30fd47eb356c9ca7fd905a4137d1780f1ca1b5249394c2262b0f1c61f521ecb1c64e6aac1b0e6ada86d486731940ed8390e207b5bc25bc3cf38c936c3aa0d106fad4e0ea9cc45b3136c3aace220bc1c2ce6b18ace62a6395e7b2987d3e3136deda59539a877e361a4acc562e330998ae398b90de3e84c581be0e9420e426dad092198bab4d162cf693c0d04a2c6ad0b28e65c9f12c5ec31334e327351c1c6ef3dca4e4d5ab4d7b48f3d68f03a4c262c59cda8057b49c6569a613 (by decide +kernel)

private theorem part217 : Excludes 0x88000000000000000000000000000000000 0x75ccc210c20000000000000000000000000 :=
  splitAt 1 102 0x75ccc210c20000000000000000000000000 part219 part218 (by decide +kernel)

private theorem part213 : Excludes 0x88000000000000000000000000000000000 0x75ccc210420000000000000000000000000 :=
  splitAt 1 107 0x75ccc210420000000000000000000000000 part217 part214 (by decide +kernel)

private theorem part211 : Excludes 0x88000000000000000000000000000000000 0x74ccc210420000000000000000000000000 :=
  splitAt 1 132 0x74ccc210420000000000000000000000000 part213 part212 (by decide +kernel)

private theorem part209 : Excludes 0x88000000000000000000000000000000000 0x74c4c210420000000000000000000000000 :=
  splitAt 1 127 0x74c4c210420000000000000000000000000 part211 part210 (by decide +kernel)

private theorem part207 : Excludes 0x88000000000000000000000000000000000 0x74c4c210400000000000000000000000000 :=
  splitAt 1 101 0x74c4c210400000000000000000000000000 part209 part208 (by decide +kernel)

private theorem part195 : Excludes 0x88000000000000000000000000000000000 0x74c48210400000000000000000000000000 :=
  splitAt 1 122 0x74c48210400000000000000000000000000 part207 part196 (by decide +kernel)

private theorem part193 : Excludes 0x88000000000000000000000000000000000 0x74c48010400000000000000000000000000 :=
  splitAt 1 117 0x74c48010400000000000000000000000000 part195 part194 (by decide +kernel)

private theorem part185 : Excludes 0x88000000000000000000000000000000000 0x74c48010000000000000000000000000000 :=
  splitAt 1 106 0x74c48010000000000000000000000000000 part193 part186 (by decide +kernel)

private theorem part173 : Excludes 0x88000000000000000000000000000000000 0x74c48000000000000000000000000000000 :=
  splitAt 1 112 0x74c48000000000000000000000000000000 part185 part174 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part223 : Excludes 0x80200200020000000000000000000000000 0x5f54dd83251c0310300c110010001000000 :=
  finishCode 81 0xd03e0e0390dc2c01ed4016c3fca064e4b2c3525e72f5a78f665d188510a22afd856ac3f384b56ce66af394663d9012c839397b9ae8c29c5c02ec27267a87c7b2ac318b2959f9c868c2b14d84ed65582c4bb2ecb14dab7291c99eb02d3e83c9c5dab62e140c8f64f05a7cc3f628ad3e7aeb09d9c6afcb355a7c1e4a228195b07b307b98ae93d3fcad3da53390f22c0601c5ca232c7ce5ec096aece41397944504522ca477f14629e5968a9e5871ec39390a926523a8c4e849ec1b55a7a98a1ba0f24f3157ca0d8c186d5c4531682798736524946c7da51b87db146d2830fb4772b2238e224f4d458140e91961fc7f76ad9c947af2bf55fb2d3ca22b0d6b2c7216adb88ba2c11818afa0a973593cca0e4cf9ab6a49735ac3525e721497cb238c0c9e96a58dd525e7215d1e426f87b62839ec657eb507e787da1ed5618232cfd8aaafd93d290b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part225 : Excludes 0x82200200000000000000000000000000000 0x7dde9d11321c11001000000000000000000 :=
  finishCode 47 0x7c1a86e1c47a1ac0f6984e41398ad40526d07b1ec8abd0326ed98b6f6d5a6981565ed628465a3984cc52a0291e0dca0a56072cbc7b320a63158f65072c22b0960f66397981d652b3f5c1626a0029e7208b8cc0e3d9735c12f50e981c5c6d4b943a6075919c6f11c41cac1658ea91d04eb4985c706982968f53f4981c5c64cf9abeb3783dc6145c6607582ca1f41ca38ae181d60b287d072afb969a5d9578a8cc983287560ea3341c8b8d4049ed0792f1b92d422a2b1719cbd0328396b190613cb137baacfc1867335aac709593a09c58716dcdf6b2f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part227 : Excludes 0x80a00200000000000000000000000000000 0x5f5dcd552b1c05001000000000000000000 :=
  finishCode 23 0xf03081ed58167ea03683d937dcc3d399c60e0268e456967c5592cd6550eb56ce67069943a7c572cac4da026fc9191ec937e5a6b50c4340cc23ee064a87c38a3ed7305c3287d48ae518342941390c3ed5a6a926382a87d48a0c95a68686483b965cd6b55 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part229 : Excludes 0x80202200000000000000000000000000000 0x7fd6dd212f1d01111000000000000000000 :=
  finishCode 81 0x1f0701ac59188315b40b0d8c0eb391718f6568137d071691981cbb2b4f279ad3538279c9df59c981d69636395fa60759acd451ecad34c0eb4d87b262958fcc2159fa91d0321ed591a06e138171968a21946ad5f2ecac7d66ac39921a1af531042fdcd45519a4c5ecf393d276a317b3ca33518a988e356e6aba464bf6e62d3e6adb515c7aa33523ab84f3987e4f39ab65d99696a33631cc2407ae5e30fe83786fe302b0d59cb0835d98a21bf146c1716108a7e0c4ad3c37eb39856a4f39672781806c3405d9518ce613d8cafd680f63356dc8a0bf3d8c6df5115c61187e2b51f6c6df5949ec6594c7b17279b7cf6334080356e48ba91d462a62926474aca541b3914b8aa33594cd6298b0340d40b8c7af460d652e4f41c8fb499f13cd652c279486b5536fad349e6b55925eb4d1718fb60d4ad345c61cd968a3ed (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part231 : Excludes 0x80200208000000000000000000000000000 0x5fd6bd55221e41c01041040000000000000 :=
  finishCode 31 0x3d0d41a85071f687b5abf2cbd62341dc8de2e35a9b08cc368c4270e2176560171c607283bd566918b8cc0eb1398aab555615fab5598aa721171cd57303a8761d5ac4da8ad5f303ad34bb3287e6adacfc5c7181ca0ed63e0e23506298c56a4796aac2957ead4cc0f0719632a1f58d86156aad5d5a38f64e0ab538e42b2f9636a215a3941d69aa45 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part232 : Excludes 0x80200200000000000000000000000000000 0x5fd4ad09221c01001000000000000000000 :=
  finishCode 137 0x1a8561c4720a2e5217a1c7b2c0d48ec4d62d87b5a5330752863b562dad358b7288c8140d887a038ab4587ba1cd4b16072914f8b2d365a3ca476ad8f7569af42cf66b29c847da1ed5816272cf47727f94149808e79cc65d96acb0259050ec721486cd4352292e569ad256aec91f1ecb16ca2e521611584b174594acfd887216049ec2e33979ccca229a448b3985c6607390b18c5393be1bb6b28b765a7cc5561397ee2889c861d5b10dc309e61cb02d20ec5316eb09e62bace55f339acbf638390b13511b4640e838b981e1b2bdd4e42c3d72cb0f650e9f14e424b99ab6c3d303a05ce12c40b8e6adad353fa819964a6077a0f8ac41446604b15469b2bdcf62b4d59aa0e62e6b98d6a62bf1ecb1565089445c86d1446418838bace672cb14ce432be5cb2e6b25ccd5b3fb9c2588629cc5568166b287569f055daca5d96211d3354547eb4d288ad363038b8e24897bcc0e5116219c581c0288b408e2d350727179eca6b9599a8ccfaf07783dcb3969ead455fb2c8cd4a5c30ad9fdd69a8e302650b9c5e57b970e245b134680bf659395fb1857b9b0243762e32eccafd2c9ac357457ed1852ec86ec37ec398d722e32c9ad34c0f0b8cb873db630aa1f0ddbe9120b8e2fdb4ae0cda4bda572d3d42e3d938bb808e2d359c41cc6073eb95ee6a2981d1d2d3d8bb307b41c9c9630ab02587177d11f330fd48e299a30b399d8128e909bcd3d8c297ed9c680a22fa356e613a8756462e32fdb80b4d9672829604c2c559cc049146ad34bf6fa0b8e2fd9c5e (by decide +kernel)

private theorem part230 : Excludes 0x80200200000000000000000000000000000 0x5fd4ad01221c01001000000000000000000 :=
  splitAt 1 111 0x5fd4ad01221c01001000000000000000000 part232 part231 (by decide +kernel)

private theorem part228 : Excludes 0x80200200000000000000000000000000000 0x5fd48d01221c01001000000000000000000 :=
  splitAt 1 121 0x5fd48d01221c01001000000000000000000 part230 part229 (by decide +kernel)

private theorem part226 : Excludes 0x80200200000000000000000000000000000 0x5f548d01221c01001000000000000000000 :=
  splitAt 1 131 0x5f548d01221c01001000000000000000000 part228 part227 (by decide +kernel)

private theorem part224 : Excludes 0x80200200000000000000000000000000000 0x5d548d01221c01001000000000000000000 :=
  splitAt 1 133 0x5d548d01221c01001000000000000000000 part226 part225 (by decide +kernel)

private theorem part222 : Excludes 0x80200200000000000000000000000000000 0x5d548d01201c01001000000000000000000 :=
  splitAt 1 101 0x5d548d01201c01001000000000000000000 part224 part223 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part235 : Excludes 0x80200010008000000000000000000000000 0x5ed69e69014887044200e01100080040000 :=
  finishCode 65 0x194791d06a1e828b949544b204c5c6b4b5a7b4a67b4a91d462b22c0ba2805114a0cb4b518c72f471463090d672a2b526a4f45bb2895646f42ce661d8b7540724654232c0a213f510732c02358db50e30670b72ca89549af42d4e3fea8adc7a83d3e9ce3d732ace61f6bd0d43e081341ec60e58dace56372ce63749fcdcbf2d1d48aa4350b41766279a0f47da7a0b8e2fda4ed02670b6afc2e38c1ae8d2b8b9af753f9ace49e6b29829a8d7591b591833505c6d559cc2e4f6b0ce499aaa4f3581105d17827986c659cb56c7bab4b8bb31833f6b5553d2b227a649e9ff47bab2359ca909e9695d1831ac8fb4723460cbb33986306511279ace569ea42ce51ab391c7da28ba30651b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part237 : Excludes 0x80204000008000000000000000000000000 0x5cd4bed1334408050210c01020000040000 :=
  finishCode 135 0x378b02204c2d89fd6a144af6981a6f698962f6d5a6a506246a1ab72c6589eb452fc98ad053201c9826077b4cb450e4ad8a2338a39601edb07247b25033fca0a54862dc5252608b556ab0b849825d58c3a92f1e4b50e2149606997260e49fe64a0ba0c0034e30b1765052a0b986e90727ece2428d441ce59398acbc24fd292a0a627eb13e39998ad6c5a9c733170b00e5f9052c4f0e4ad5672fb0dda8741c4520a4a0d3461607460d68ee5f621b16cf40c7cc1372fad4e8c1b9664faad154485180480a06962cbe5a2c48e3d921a7d39ab2a1d486d185481c7b2d15ccb357520eb05501ac0d7c582ac665a2b5753eb2d1df437124486ca337b2ad4e30a8e789099f2d4c6e33564b06accb4d50eb566522ad35ab33da5a4ab532eca088e316e48689dd02ee495a3ad4cf41dacd5b724ac6dcbec5b876af57267c6060da90138723965cd7073a30228b255b576730a80dc92c03e05b5315ca318c1cb279cbea3183dd1818398575c92d3f5f1d0411f4267c3c3303a887a46165018eed18739ad60ab537b6c6bf5a9b58630a39596265d97b28afd65ee6b96a6afd99c581f027e9fa65979724bf22e13f4cd5d8911c3c1a8f1f151ce5d962dad1d6a6b319cd65e3711abb39adcbe705621ac6d8b690d9abab1b5f1c8b34fd43a9416aeac4e4fa9ed5ab66ef6a180890bb26298c56d3f8392b4d6adc48f699abac5b69fcd5b59fcc41735b56d6a6607 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part239 : Excludes 0x80200004008000000000000000000000000 0x5cd6fe5b0140b0340600c09010020040000 :=
  finishCode 27 0x6511074144aa397c214711647208dab6511070ad3637d940e3070b54a46f6d960a8393899446307310d03283d27eba10a388525969e0e149ece672e49ccca06c59a306b1b070948c5c318ad6724fd7f1d07c2240708b86399948c5c320de7328b0ca3652340ccd5d5a593f4a46b238c0a51b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part240 : Excludes 0x80200000008000000000000000000000000 0x5c54de55014000040200c01000000040000 :=
  finishCode 135 0x1083e0e83c81ed731ed327a5eda7f941c83641c3122c052348ccd5f5a6941cfd22e3a0e6b555a5c7f959f9445a02919ec61718f6569b13ccbb2fe358cc3505235e16027ecb4d6ad8fb4bc2629560c56b478dd2b059ab2f695a3a98b1b9ab2f69374ad4c9d261f723ca252ecbdd56464f39c45e09fa2e18bc2629258cd2572fc1b544ab1b96a62e15a1986d07daca27de416a0f584b460cffae49591bd965a6a7a56a727856364fd416a0f560791846d0f417093f6611c60e5a993f584a9e989fb316e836ad2c9e6a0460e611bdb56371816aeace50272f0ac2c03ed69dca3959c93f567318a6315933e5a993cd646cc3590a148d686a05c713ccbb252540e9c96267ad349e6b1b9eead2b27ebdb41aed017641ae1c985aeb478c1c27d83b9b7c7ca4c12f1a90ca0f9544b20f54c3209e6b27a306c257319ff42332cc48cee45694ce458509e7460d04651b650b88c1cf6d69dac6439ab4d681ed3460d49b07d0e6c1f67b4a80d49b1836b0c7c57bac6050324c18316051cc4fd692c83d40e949565f1fa58aa90b26fa5041aee83c8da388ce037560292abde48cb4eca22c0ba0da91959c96d638b9875985203ba7f796526ef1708fb5007140d046d5b281c1dd81ba9fd6b03baa418ac7db24bdeeb356c9e6af3967ee5f3feb50da2d0bc20b50669fd964e3ed315abee385a7f4c3ee229881396724f330faf0b018ae30341cd462a47302ad2e6aac6060daa31606d06d59cb97cf41709bbe409a38e6b8d4af578c0c1edeaa80758dcf758c09fb649d9814c529fd59cc4fd (by decide +kernel)

private theorem part238 : Excludes 0x80200000008000000000000000000000000 0x5c54de51014000040200c01000000040000 :=
  splitAt 1 110 0x5c54de51014000040200c01000000040000 part240 part239 (by decide +kernel)

private theorem part236 : Excludes 0x80200000008000000000000000000000000 0x5c549e51014000040200c01000000040000 :=
  splitAt 1 122 0x5c549e51014000040200c01000000040000 part238 part237 (by decide +kernel)

private theorem part234 : Excludes 0x80200000008000000000000000000000000 0x5c549e41014000040200c01000000040000 :=
  splitAt 1 112 0x5c549e41014000040200c01000000040000 part236 part235 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part243 : Excludes 0x80202000000040000000000000000000000 0x7c5fdea90d81a1000200828030040400000 :=
  finishCode 71 0x2106b1c0740a46d4370a43923a72d0f6ad3e6af8f6523248ba302d37260b52d60a2e31ecc18a099a6eb1b5a393cc973370d42909c1cd50073484bf62e3388a4ae4018f5d0271cb4f5e2e3740dfb46056961c78388f5c5c66fd988741488c0c4f36afc1cd25e93d470bf72465ed334f5344f1cc0f5239fcd026b4b93ee4f37b6a08d5b155cc0f62da00e7b2b70c0204e39687b4e6aca1c454c7b4c1a725ccf6d0f6c60d6228037b6c1ed851384318572cf53ee8037b29bd566ab4b7b6ca3130293ccf4404d18325ca00decb41cdc7af6925caf8b04606621a0dd052821e8a47615c4a97b2c6f540bb16e0e328c63031837b68ece8c1b925ac521b4393b282e390060c70e38f5e59aa4ad22f0b8cc22d5b651277460ce5a7af171987d4371ebc3baa31a30680359396bce22727 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part245 : Excludes 0x80a00000000040000000000000000000000 0x5f5cfedd8080a000220000a030140000000 :=
  finishCode 25 0x1d07c1f40f6a580e16d0f44a0c19f5a2b0ed8a6941987ec2572ca474a4720e478e5239ed3356c1b2523291c0d76d184710a46c8075d07330d58b6d5d170a4a6161cb1d2e1b57581eb02b84df41bc8395a4cd4b6aea05e41bc523 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part247 : Excludes 0x82200000000040000000000000000000000 0x7ddebf990880a0020200008830440000000 :=
  finishCode 33 0x7a1f0721a8070a785230f6ad4e4f397e4f5e7056aecb534f397e49b66f78a46c21c6616a948d1c604c61337ea8ac7b32d1e40ca8ac5c60d7291b58e4389183987ec51501875c1a6cc2f871396aad6540382ece273da4956d65060ad4e403c7a2708e388a4d8c1ca47735a01cd9671126dcb035a2c1be7b4b97e306e4962dcb451e1bda5467239d8a22d5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part249 : Excludes 0x80200000400040000000000000000000000 0x5edcfe89a0c0a2807204008038040800080 :=
  finishCode 53 0x1d071160671f4288b09e6adbda43ae0e1591c6fd1ebb4ac58a0d97d1c85101c26e1c5d6ab1a95eca90b4a0a8c548ea31948a2dd85c693d5016273095eda2dd59aa4f569e8e9923a287961b0715129c5c1b2fa24be16e875c1c2b13987ac3b1628365988413c291a3894198aa1a31ebb007e0f666b2b095a7ac57512cb2f612b4f47b2d518992c25698c3d9641b45f0e26b559aa24bf1ebad566a8aca61ebad566b2a389e2cbe1ebb0ee4a0b095a7b30fd23ac55611946d13c0e7b14e1eb948c36eb27984a523508ca3941393f4a4713f6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part251 : Excludes 0x80200020000040000000000000000000000 0x5ed4bed940a1ac010281008032040004000 :=
  finishCode 103 0x651d060210281bd0b3d8a461ed641f07f16037bc8091708f6524060cd5d4739f16390b575a6f3db5a7e91f1648f64183248ce35960f7302567aa1158989d5ed2f6b694cf6983cd073733b57590681b40eea4be5088305c97245cff25e0f5e5949bbd4230b8500369c1b546329160f3204d22ed65841ac7a224397ce4b0f6948c36f07b624641abb201ce4272f582ce5f725b5959c530d7f2ca5ab6d3750fad547af1819a6e2e1581ca1f694a91e58187b5b44a11c37d87766b2a01dcbf170c3bad65399cd310db877651fc20a01c0fe34a5abae439052a3753077f24c5aab30fcdd2fe3305e2389e1fde511a01dac6adcb277baa88e0d33496306f695a3a8de7b4b5445c32383d78fee2e150bad4da7b3dd53ce94341cb03da4a8e2cf62fcb59563ab472fccd516d11c3714067f7836e80750ccd316b0a4738f60da1b7735cf6d83697e683cb165ebaa2b587ad45b4680592d635966ad86dc182d51900ed31518b5464099bbdaab20dd422a3969b97e624321d069bb544bf307743da5f983bb24f47ae52362bc2e13fba05da6e1ed (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part252 : Excludes 0x80200000000040000000000000000000000 0x5ed4bea94080a0000200008030040000000 :=
  finishCode 115 0x3a0ca3105177a0a4b08390a479462d290f6c48b0996062e32d7cf69381b4a5ab72c24b5f07b5a5a8fcdf60dd6b1c0315cd29526834d467316d25ed29501cc5b581c48e03f862b070c9ef581bd01a398b61ed523cd6368a319856d5b694874d66b3075ab6d5d523cd5d581b68d5d0f6c9ef170bd966adbe0fa390ce03741c3071825647750696bda6e2c928d9d0b4b9a6ed3f042ad3dabf310be146d84f1fe566a523694b4fcc23348683cc1edacab352918b8569eb358a0e72d0f6946e7c1fc6e12c650e4eda358a038e225230eba38a21c45ed316bd462c43593869ded32c0e0460e4a193f5aa26058c1ce4927ea45d21b161d856e5f8c1b544a47245ce225e148d5f7181425ed3161d9c45aa2b0d50ed1835229c44c0a6139aba4fd2919cd594611a45803aee0120e11ab92630681937a93f45c2a25a0f2e491e1a85d61b06ada522e1961a61f4f7bda6692b575636b4727eb08b0148d3ef3d960f2b23170ac36692bda433ed5d607cd256ae93f610430e05a7c4fd409b04da52d5d651b461185727dc7861d37b4cd2551cc4fd2f1a4ab0d9662e5959cbd4e27eb4dcc22a63284fd57dc813609bd4e6a8a91d822bc328d62846609874d43b41cd48ed37961a61157dca11586b97e062874cc56ca308e0074c7af2d4d86ac5b6ae948d4071b6418f3da5eeab1b839b4acdb2d5d27eb97e732b5449fad5d (by decide +kernel)

private theorem part250 : Excludes 0x80200000000040000000000000000000000 0x5ed4be894080a0000200008030040000000 :=
  splitAt 1 113 0x5ed4be894080a0000200008030040000000 part252 part251 (by decide +kernel)

private theorem part248 : Excludes 0x80200000000040000000000000000000000 0x5ed4be890080a0000200008030040000000 :=
  splitAt 1 106 0x5ed4be890080a0000200008030040000000 part250 part249 (by decide +kernel)

private theorem part246 : Excludes 0x80200000000040000000000000000000000 0x5cd4be890080a0000200008030040000000 :=
  splitAt 1 133 0x5cd4be890080a0000200008030040000000 part248 part247 (by decide +kernel)

private theorem part244 : Excludes 0x80200000000040000000000000000000000 0x5c54be890080a0000200008030040000000 :=
  splitAt 1 131 0x5c54be890080a0000200008030040000000 part246 part245 (by decide +kernel)

private theorem part242 : Excludes 0x80200000000040000000000000000000000 0x5c549e890080a0000200008030040000000 :=
  splitAt 1 121 0x5c549e890080a0000200008030040000000 part244 part243 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part255 : Excludes 0x81200000000000200000000000000000000 0x7ed79e4d249040500041000000240c09000 :=
  finishCode 67 0xf4388f2398e03580dd6d1a80e9987e5a6a0cc9fb181e27e98a505b1cd5a865099f0df4e3e93141e9cd4a2ebc2583ed4f2c72f381acfd462a478c2ca4947cad3c3327033e2a92662ab28b2075d48b2d2ce5e2dd2fdb096728a915466d2b9a8aa1d612933d6028bb688e27093d6afc90b728ad35422e67984ab4d485c7c557b96d49fa713508c2e32fd8b8e4979c4d27ab23f861f81a262b39a831e315b588e031c17e91f948ea0771da4ece3e8d5948ea3149da0f63f3ad34e3eda0fb5905f174580e42b4d9072b4d81668e2d3649eac4e3dab4f562741b65a9aca569a6f78feea1141cb68e22f80d383cca1f47496d5caea47303875d5fb320d403060e4ad4e5a6a4ae30b41cd64eb295a9ad3507324c4ff2b4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part257 : Excludes 0x80204000000000200000000000000000000 0x5dd4bf85368448500001000410200c01020 :=
  finishCode 131 0xe47013c6f169ad4388d61484a4a1cf8c564cf9ab2b457b4bf87e2582e1403c60e5949f15ed2d252e1b995c8f03050733203b59276f696ac9cbda97399562712e5812b2f2ecbda506e807621605a9c1c9283c48d62c16267ad1ce42b2f8002c4d504b994bb2f69519cf69698b544c0f1c85a7ed6378d43100d37b6c92f6a8b59417e1c9541207b2d185604acbcbb2f6969f8f64d0486d07169fa91e30a5c96aab03e8c2b4b63074614bf2c0180ce2c01a996a6f697b39445012fa46158133085aaa5d90eb82ce255bdb5c8b391ded2d556b0b084bb2883da55072b8f266aabdae8c2bdae0e7a4f5052b45899ef69621a8670a0f02f5abb3da4bb2b5395069dc3d94fab4fd48ad43da586b356630b181d807b4aa0b017647b33084392d3f9ccac51597bdb6030ad14a42067948eb456a17428bb5882074cdc733ca337b4933cbf73da5cc2f659462b034a0bda548f2d55ed2a31948af697d1040ebcf6972897ed466c579ca2f690ebbda60e7b78e2368e42f80d37d1845903ae2bf927ac4196225d9288c5d95a99446390873ca2317656a6afd67018734a47ae837292c48a61875a6f2c44c26e679812d29588b58615f945dc8a51792765116019058120f20e47b21c96701673db520e8170609ec63e9bdb5aa2d65891b42e1cf6b610ad55acab275a98ab635ca4c507334a455ad4b642246a1cb27483ad4ce4272f495cd293d8ac0c99eafd96aae6359ec1cda889039318591f6b53315a8266ae9ed60de0bd5a9c3d9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part259 : Excludes 0xa0200000000000200000000000000000000 0x5f55ff07248044510001000000202d01000 :=
  finishCode 47 0xe0390fa07b5c4590a220e116ec7f95a2ac34ff3310c8238b024f584b41b499ec3b4838f6587f3095a46f69610a41d653308630ab2990733da58aeb4d26494464048365a8671bc600a36d5d941aa4958fb5445c2521581cd3f8fd2f6939a941d7c6b1a6f06e5aba91d6a88b74ff32cd52831fe437292f8a22d4328c4145c5bb14943af2c8ce28766a1b8ed63e51b39ab4fe50eb985216c094a0a83662ab08c4338c2561fcf6958f94452832cfc39f3da6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part261 : Excludes 0x80280000000000200000000000000000000 0x7fd6dec5748040500001100000a00c01400 :=
  finishCode 43 0x3e0e02f01ed621b41f6ad2e48bacf43a6b4d41998ae505b20e2328d3f83a6b4d315b4fe504984560f2824bf2d65943ed43309ad35946d13c55169aa1183a683340ecd5d711a7f074c9fa61f61bd07d3e497651f6a1189fab4d5913ef4605ccae616acac35872d65730ce635e12c62128730d4bf6f69522a8cc7da52193f2a35523a8c4bb3074ca2eca3685d99006c21416874c9e73da4bb2f699c8ec39711d0419cd512838fb4a36e619cc63ed419b99640eac9d67a3ed (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part263 : Excludes 0x80200010000000200000000000000000000 0x7fddde2d2488c3504001204000204c01000 :=
  finishCode 101 0xce350b83008e1cd59438fba0c414847db1ec507a8e7940e7b171da45d81f460d60ef69401b94507aa079186afd6afac1d9462101b02fd0073025ed29170eba7e66ae976560ec554e11c720e22740f5e6a39ff5cc479c4cf48b949669093f5ed23ed171c51b731c862178479ca453f6933c7da003899e01541693f5ed27ed28dac1e5188646267bda47db3da5887b49f9e5839fb4a3683d1ebc8f3583a8c58028d940a1b290c1f66a3abdce42d43736a92658fcd29578bda53e64cf5712c3f06c613cc577b4b10b2962bc60e518acbda424f349eacbe58fc1d72ecbda584621746129766604ac6d6964fd371ed25d9485cb4f5839f9dca3351543a7b159aac8b3583aeb4b3d8caf17b49765ed3270f22c7c9e7183967e1d75aac7af71d8645d0620e5f1819aae7f32e2c6063f9b57dc76d5fa3026e96a1946b0a2e9c0b8d4633da4e0672f9462b03609ac0e4e1586220f706d47da6c1c0d1f3302402a1195899f15abab559a533da4e06821fb649ebda47daa0b523c60647cb4a55faa31591944105c69617ed48b461567e8e9a0e31857b6a875edb41ed696721090cf6957eac7d58397c129610acfd84a5d99ed2c57 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part264 : Excludes 0x80200000000000200000000000000000000 0x7d5cde15248040500001000000200c01000 :=
  finishCode 65 0x6b1f0291ba0d43381ed4417038cac6e604b52d25e735850a0f146d8b71f15c8f2835636525308ac6e698a4bcc22f23e8ce038569b1304dfa50761cce470d49ec527a8298a22b4b8dfa93d1ecb510623566b2b0256a65d91f693cce6abc3e83ed68102f30fd48eb4d9ed32d349ab2d34bb24f39c8731d06f1a806bc280d1483c92f503a07569b310d25f133da85e20c1f687365a3c1de416a4be497cb53283b50b07899e833836c4cf47105a3ed41bc8f5836a4f585717647af130569a2e3279b901ed87daf8300ce0b86302ac7ce327354c169f27a4372703302a7a60dc9c0cff2b1f302c71158193f6 (by decide +kernel)

private theorem part262 : Excludes 0x80200000000000200000000000000000000 0x7d5cde05248040500001000000200c01000 :=
  splitAt 1 112 0x7d5cde05248040500001000000200c01000 part264 part263 (by decide +kernel)

private theorem part260 : Excludes 0x80200000000000200000000000000000000 0x7d54de05248040500001000000200c01000 :=
  splitAt 1 127 0x7d54de05248040500001000000200c01000 part262 part261 (by decide +kernel)

private theorem part258 : Excludes 0x80200000000000200000000000000000000 0x5d54de05248040500001000000200c01000 :=
  splitAt 1 137 0x5d54de05248040500001000000200c01000 part260 part259 (by decide +kernel)

private theorem part256 : Excludes 0x80200000000000200000000000000000000 0x5d549e05248040500001000000200c01000 :=
  splitAt 1 122 0x5d549e05248040500001000000200c01000 part258 part257 (by decide +kernel)

private theorem part254 : Excludes 0x80200000000000200000000000000000000 0x5c549e05248040500001000000200c01000 :=
  splitAt 1 132 0x5c549e05248040500001000000200c01000 part256 part255 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part267 : Excludes 0x82200000000000001000000000000000000 0x7dde9f1b408242202800808000000008830 :=
  finishCode 75 0x7a1c87c1980f6bc85236001c2065a0eec0f83e8f0c59a4db581c9c2902cd5811cf303cc0ae5fa0ef07137ab03d1cf181a3069e141bcb4d5201c23858f5e94126dc3d76b1a006b948c983246581ef5d40b8735ebb1fdd2330714e118521601f28b367baad3506ec43859ab4d4f1945b169af2280e51fc1f6091a09cdb22cd8c0cf7536ca01e58ca0dcdb2af99677181501ca3f1f29e8b4d69ec1cd26dac6669e8735ac61181f1c443ae5237c190598cf5d60f98ad1eb2d4d06f0b8df04c0e0718156c6205aa8e795f6f65381a8e547eb4d91ce9ef7bacb03352b4a4e22b60b0e5a6a8e547ed51904e4c1711c86701a6c8075d69b3d74786941501cb4d859ab118c26b53315875d98601a6f02dc1822cd5b0e66a039aca3d7582cd6557cac9e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part269 : Excludes 0x80202000000000001000000000000000000 0x7e56deab4d8341202800008000800808030 :=
  finishCode 95 0x1c8741c06e2106803dac22f0523838c8234f9ac6439a3ed4e1acb2cf507a6d9279b9864f9a09d00e4f39eba8170e6a08e419ad349e6c42d362d78f5c9e61dd7f194388a09e401ad363071fdc5028f341bad3e068bf8d627891949e948d61b2c147ae4f39387c11cf3d5d48e60541693cd63ea60b3506f41c546ac0f9ed6b4d7b6bd5e0eea4328a35a0ee803419ad3548f239d69b278546a9c298c42c7e8388b349e6a359ab661d8388b3563e7fd859b181302ac7cc0b281d69ac4328b0208d05a1a792764f3396cb1f0d3a70641ff648c8b34db26f56b059ad5b9232b039ac5207af46051f29413d7c5c58c0a4647aec0260a0da3068e75248d9e36f9f9d3e723856227e74e1b88c0c91759ab04dab671138fad3e3f3b56c59ab1f5315c479d07d71db4ad3e61ab1eba8d671dc917609a8cd462aa310dc231657b831d69a82d41e8fb5347c107a7b79663183591a8763030e5c9e6c0f5988b353c320b566aca38090d8c56b4d59230700bd1c2a45609acd54665fb6adc5239462b239aa262b2918fb5c0308c4f3291be0d4791e671139693ce (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part271 : Excludes 0x80a00000000000001000000000000000000 0x5f5cee5d40826020280008800000000a030 :=
  finishCode 29 0x1d0781c40f6a4f65249fdca4694106b948e6b198680a46b1d941a725062937e5a6ad8c42901a7907a2e14a0a7de7ba8f1d66682347cc80357c8b855f32d2505aa07621f4599c823416ac7e0e0a86c7dab5185c290d5a6b58cc2d3658eb5647da5234d1a7f20cd00f356d04ed3f1f2c82d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part273 : Excludes 0x80200100000000001000000000000000000 0x7ed4ae89488f40602a00008000012008030 :=
  finishCode 61 0x1c4581386219427ead8c828ad47e6f581626051f6c1d3388be0f03006299622727314c71148b95fe003a45c236f7559997e4c5283398036ccc0f0d886d5b8302cc5357db4856623ed598c8e17d194700c272d34c52e6d9ab29310ebbf8d3f69ec7e7731b56ce22d4329198466adb50c5c31c7dac7c190651067075cc52e0148e308a3861f6c60d667148d22e7270e9ad36161a85d0668e184b63ed41ec20d634fd6c5a7c3d7621b4a4a461cf291c82d87ca83d6b1a5b15fce6a1d73158fb6661e8051cb1d69fad35a525231f6b10c82c00b9515c917692caf959e8f5daca8075a9cd658c2c3d7694abe4b5ea178fae2e1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part274 : Excludes 0x80200000000000001000000000000000000 0x5ed4af09408240202800008000000008030 :=
  finishCode 157 0x388ce32851b6d0a42d639862b9ab60dd070874dc0315c1ed531c8b356dab29f36adcd597f03db03856065af98266fb40187b5827356ce22b4d721c0531a960dd070a7ce52498168c1c605ab6b4f4e1b86add07b3889c7d4c4f9ca1b473c6fb6a1b56e2437dc7e78c1970ce4ae41970700dea2cf969ed29291c1ee39ab4a51cf181563eb3560194720a2f123e8f0034e16683756062cc60548bbd0b4d907a523486cc2b8c298ac1a7072569a1ed069c2cd0f698164f2ad35a9661f48bb8108368e42280e10f68b3658fbdd5a56b396ae8b368c09816246113037a948debb3155a6ec25963eb31927a9419a533dd429a5230f6b56e7ba836c59a0e184138694b707339a421b583d9c0deeb06c563e733166a79660788de1f6b55d3ca733166bd1083811207b51e702553d3181694ac7ce06b032918b76515a28d3f833e703694b90820fb4df700760f6c2b3d8c733518b56d606b1f82bed216b09c0ce0703747da6fb891c06a8c91761598ad04730ce638c2a45da52703615b986731c61522ed29381ac660d1b56d94601e0281bd1082be6291ac9c7da1ed721cb4d6ad87747da1c9969b185166c48da2c091f9aa2b2548b8714df6f435447cb30ed5f2523483c7c56a1a434a4717e52869175e160691c82340e8715a631f5daca2ad96a288310723f8b4d670dc0b7cd5b4fe8e9cfee807731980eecb036b2a98b19921ab5396073d0917942e1ed6adcb038912631bed06729143daa177c19c0f6a01e4feb56d5f2917a0e6b036adb57561f27f5472b4d9e884134291a01c3dae6390069414f3ad4e4a0c1dd581c8072fcb90e247c2108c0c7ed6a587a5aa25236e1ab707747da7338ffb1ccdaa2523166c1ed (by decide +kernel)

private theorem part272 : Excludes 0x80200000000000001000000000000000000 0x5ed4ae09408240202800008000000008030 :=
  splitAt 1 116 0x5ed4ae09408240202800008000000008030 part274 part273 (by decide +kernel)

private theorem part270 : Excludes 0x80200000000000001000000000000000000 0x5e54ae09408240202800008000000008030 :=
  splitAt 1 131 0x5e54ae09408240202800008000000008030 part272 part271 (by decide +kernel)

private theorem part268 : Excludes 0x80200000000000001000000000000000000 0x5e548e09408240202800008000000008030 :=
  splitAt 1 121 0x5e548e09408240202800008000000008030 part270 part269 (by decide +kernel)

private theorem part266 : Excludes 0x80200000000000001000000000000000000 0x5c548e09408240202800008000000008030 :=
  splitAt 1 133 0x5c548e09408240202800008000000008030 part268 part267 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part276 : Excludes 0x80200010000000000008000000000000000 0x5ed48ee90298c3205014200040000004100 :=
  finishCode 63 0x3c8e83385176111c0e7875d044f7c3d76b0976661db0f5a5718586cac3d7b4ca256ada4bca23122707175d0b3b39ad63e8f97b49c8459afa24be58fa50563f068e8c29c8538512c2cd591ed2d5796ab1850d1c61669138661881669fb627e875e416ce4927e873c16b20f43a683d8db2d22b89c3402cd522ca47839cb4f4f18e54fdad5b1eba98f6959104720f5442d2b0d5871cd44612771fcdaae3d7907a7f3695d07d2bea4ed07a3d772cc48d47ca00d46283d5e104522ca475aaca314e1880c8d07341693cda848bc9e558f864546a8033f9cb1f3f9c90b11d8b8cb8ae594e14836c9766406bda61d0d0711ebbda504683d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part278 : Excludes 0x80200000000000080008000000000000000 0x5c548e531398413418144008400200c0100 :=
  finishCode 97 0x3c0e83e0f4420dc3081ed5c224710a46d3b8fd2b2f070b4ee5801b3356c7b2b2f9a762cd48ccd61291b56c1c20e187b2e23f8f23500e126dc50d315948e6b07b3148dc7b397cb126f55a7a065881ec94860d3390d5f683d834ce431eccf235050d8c5252169dc1bb40ca504c0e0e1721c90d0688775bc661a8166a41e48c8725cd72465052d5b581cb2f522a0a5706b07b27359ab6b31495acbe4a0cd5b661a85c15f3176416a2cd0e6830e2929765bc40cc829291c7e96ada505ed2b034b6283a0660c588ce49171b51ca4ac218d96d47581fc6f1067075c9fa819414c18d3f89fa83d85c2c40b3627e976669f98a5bc1f6c7272918b35ac2d9cd3f2918fb669f92358b67c557cc18e8388b6310517591f4483c9416b0cb5515fb16651ca935aab39ac97e1cf2919ec67b4a7f520e1d7290c1be0c8bda60fa3b137d940dac69184063872e62c8aec3aec5989fb1f3503a52315dc4fd41eb10523523cb451f6a436 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part280 : Excludes 0x80200000000000000108000000000000000 0x7c548e53129061283294400840000000080 :=
  finishCode 113 0x3a0f2358c82e8823e87056117c6f19c690a0f148457672541c875c7870617be315b16e0d39c943da2cd8a463c330f83863f4987c7860df83da5231e1bf8a427c658d833d20e92f85160b0b8c5765257b6c907166b0850720d78e4a2e35a3c0d30e78eec1b259d859ab552919c85988418441cc1d7060948c7b33da4c56f4398d4038568b17e4a06b45835283948ccd5f2daace5233247418306388dc39872d50fc9075238365abf41eda76919290c0e1581c50348cc0e11ecbd0dc3e0c207b475700ad8427e983ba79c1c2b3f2918386711bc292c0d751ac8335a3941d68f207587a523291ca03711073075c1a6b628ae69d940c50330856669177b5c18de38850306cc521581c7f961e9bede8598c4af5a98f9507a1ed727cb2f58d8285a4aa450f6cd43e0dc1c9e30f87b5ac59cc3d9291ad3e404bda61668734bb33da47b25236b1bc691847909630eec59a1c70e9948e063b50cc20762ec8b3418eb31895eb534199c9c9e733083387da52383107b1cd5abb20e60c7c1a87207568e60730fac6e27eb495066d5d907ad3f291bd0afb8e6a8fb416a0f5fc610e6ad29a3065c3241ac9ded21ab692cc5b836acec95ee5f81560a1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part282 : Excludes 0x80200000000000000008200000000000000 0x5c548e5102d2412c1315508041000000000 :=
  finishCode 105 0x6f198571a4890b3a2bb166ab0e84616281ac4ca46713390b9661f6949657e948c3a69078176181741e06e095f1764a463dd0f6c28b0145cff325049e6b4f9843397cbb262b0708ee60c7113e316747da50d292ad261d8940c763397438ad5b93e25231f6bc0604190a350e83c8a3981c25b529282c650693cc3ba7c9944a3ed070c9fd512ad14ff25b52798f962919764ff33a0d43700d78a463e50f6a0ce8398e74a46d5b50693cca2e3d98a460e1839ce59518948c7db06167506713cca22b0f87520b1291ab8e8308614831c4382cb2f0eb941ca4ab2f8a06d4283641c87a504682d41cc0e17107872cfdcca0e11ebc6ef461cb4927ea0e60c8511ab356d03a4f340c9444def07b41c32835032cc210d41766147a1817141c3da0bd419a07624523cb1b2679c4dab6b53838c1bd6adb57417a1ed9845a9c5236add12358b83d0fe3a0523283cd5b0f69c9e27eb56da5b2c3c3da3e5580def13f56a72be4e426ef070c523393c4fd0f68f951c741a60e2d551ec87b5f06a1d038fcd5b37b87b526313f5905a9c7b10709bdd6ab038505b0b0d07a4fd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part283 : Excludes 0x80200000000000000008000000000000000 0x5c548e51029041281114200040000000000 :=
  finishCode 117 0x428b4d781786b1d06adb40b0320f20ee47927059256b55389b586279b4f507a7f36f1c4470c6134a18384a2e511582c5233e9940d8173dacfd2b5540ead1ca0ef444908350523171c52546bcb2f474abf60dd94941b30384e6b2be52560d3791f05b01c21ed8a061ed968ab2f968a2cd8a46f43f81cf87da2cd291acc61f6ad1e05ebc8e8388503839c48d5819685c761c97b48b341b252568160b208c3922cd9e869fc7351f2a0f5600dec7d37b48b35072d258e6adc13ce732c1f43dab3f0e68fb459b13cdc4741bc790c2720ccb6a511070ac0f698a46c371ec87b49e62cd8e4e92f291cf6907087b5606a14c4a1cd3d62c984d0664f37f164b1fe5072b259472839964ab5129193cdbc419ca377b48b34c3f0b360f6b88e8338b61444a4aafd8376afd83aed42c05171d8c9293e9c48d48692ace0b2c4ce42d62c083383a64fd61146f073c9568fb9ed312e5ab21bd1f6af05030d2cb450e29bee1d8a50de8661846e0a46b807b5a04e039ae5f90723e52e2c11f23f8f0d072b477b4c1f5cd70f956aac1388ca2c31f2bda459b3e03d99ed25d907087b5e457ccb517b4835ded31764e0b07b41c2cc358f69166a4ae598834ce26b199886b475aa8725cdb1c656a66ef (by decide +kernel)

private theorem part281 : Excludes 0x80200000000000000008000000000000000 0x5c548e51029041281114000040000000000 :=
  splitAt 1 57 0x5c548e51029041281114000040000000000 part283 part282 (by decide +kernel)

private theorem part279 : Excludes 0x80200000000000000008000000000000000 0x5c548e51029041281014000040000000000 :=
  splitAt 1 68 0x5c548e51029041281014000040000000000 part281 part280 (by decide +kernel)

private theorem part277 : Excludes 0x80200000000000000008000000000000000 0x5c548e51029041201014000040000000000 :=
  splitAt 1 79 0x5c548e51029041201014000040000000000 part279 part278 (by decide +kernel)

private theorem part275 : Excludes 0x80200000000000000000000000000000000 0x5c548e01008040201000000000000000000 :=
  splitAt 5279 112 0x5c548e41029041201014000040000000000 part277 part276 (by decide +kernel)

private theorem part265 : Excludes 0x80200000000000000000000000000000000 0x5c548e01008040200000000000000000000 :=
  splitAt 1 72 0x5c548e01008040200000000000000000000 part275 part266 (by decide +kernel)

private theorem part253 : Excludes 0x80200000000000000000000000000000000 0x5c548e01008040000000000000000000000 :=
  splitAt 1 81 0x5c548e01008040000000000000000000000 part265 part254 (by decide +kernel)

private theorem part241 : Excludes 0x80200000000000000000000000000000000 0x5c548e01008000000000000000000000000 :=
  splitAt 1 90 0x5c548e01008000000000000000000000000 part253 part242 (by decide +kernel)

private theorem part233 : Excludes 0x80200000000000000000000000000000000 0x5c548e01000000000000000000000000000 :=
  splitAt 1 99 0x5c548e01000000000000000000000000000 part241 part234 (by decide +kernel)

private theorem part221 : Excludes 0x80200000000000000000000000000000000 0x5c548c01000000000000000000000000000 :=
  splitAt 1 117 0x5c548c01000000000000000000000000000 part233 part222 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part287 : Excludes 0x81400001000000000000000000000000000 0x7ebfbaaa800225030280000200000000000 :=
  finishCode 17 0x1900f5ad870038e517acd5696e83b092b8a1a0e327ccb39393ace66517c5805c6c29989e93b735c2b3611c6141c72c9e30a70b0d6b56e0d6838e3819cd49f27c3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part289 : Excludes 0x81004001000000000000000000000000000 0x7aefb292b02609032200800200000000000 :=
  finishCode 31 0xe23b8b207add81fda3e649e9c4d00a82b385cd5b8b16f51522ac6cc22ca3203fb582c725625b0b45c2a3393caa0d272943560a8159076c82c0a4350be0b8504397c1de6ad825568e4cf519a09e2fcb0b435b2f8b4760dcd5541cb4b63e9cc2d50f9ccdab6a21186497ac6d43eb476ada00b4d8e4292f3f2cf655a99f4e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part291 : Excludes 0x81000041000000000000000000000000000 0x7aefd2aa849231230208208200000000000 :=
  finishCode 35 0x1a4791077102c3d6962e05d3740e4e2e394929439a6e8f357dc61f5219c65dc65169b184d67b20a5ab6d3739acb4b86170551b8579c9170739c0ce5aee05ae59c839cdeb3b8ec3280e748bcb4d315b9263e2b56d85335845ae72769bc4f959abc8b4da0d647369bad2c5c20e75a5cd5b5601ced5b814ed6127cacc6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part292 : Excludes 0x81000001000000000000000000000000000 0x7ae7d242800201030200000200000000000 :=
  finishCode 133 0x79218711d86903d71ccc82641b74083a6f581ceb3938b9ccd007348fe100cdfb07ad3c6b2ca09397a8bce26be2a8d4b943ea4783dcf6f00fac15822c5d517b1765a5ac15662a4328afb8bde2e3419a40941c4dcbf41a5662b3d3fe85ce134abed45ed5b9486b3159eb56e392a884bded43308138e6640d741cc2e1c7053f9a08c1ce92f8a06705409cc83a049d988211f83d8e8d25eb4d0739c4d7c3f9bd8e59e82ad466b3d9ab6f6362a9ba4fe73a0e63b0be039dc4580c0e6118e66a499ab6d376adc6fb392a00e2fc8375a46f1940f5af81d38bde713945e8136a3a40dc1c4d61b3555672d2d59cca499ab6a2f5f1942c2c72f5a3a074e4a5ef362cd2d052b0a4e5e733389cb31650bdf20749f283348128389ace683bad2cffad639a5aa2f59ecb4b6b0b56dc4419b1666959c95aaa5ef390cb3d9a42d553f9a00d885a1d85507fab2208d066b4d9232b4b5a6c6d1441257187d69aee313e36f987cdbf41f503a92b65154267ca332f7a0ccbdf38f5ab6c5d6aa8b8da4550f050fa91d85b356d02ed65616c72d6ada05cd8421ab71a5504e81960ab1750732d2d5e6e3d735974dab68179836b23517b555ac2e59960ae496b0b56d9477154711026a60b2e0e3a4acbded5b8e22d470e39c65ac3282d68e92b1ebbb03d78c3e92b38cc5ef6a3a4ae5a5a04dd8571232e6b9ab6a4748e8f5cbab310586f287d02ee0320bc300605314a09e40ca88549307d98668f3627a8866aaa4ed006b4d30fa00e467cf6d009b93d43aa474f9b514e22803 (by decide +kernel)

private theorem part290 : Excludes 0x81000001000000000000000000000000000 0x7ae7d202800201030200000200000000000 :=
  splitAt 1 114 0x7ae7d202800201030200000200000000000 part292 part291 (by decide +kernel)

private theorem part288 : Excludes 0x81000001000000000000000000000000000 0x7ae79202800201030200000200000000000 :=
  splitAt 1 122 0x7ae79202800201030200000200000000000 part290 part289 (by decide +kernel)

private theorem part286 : Excludes 0x81000001000000000000000000000000000 0x7aa79202800201030200000200000000000 :=
  splitAt 1 130 0x7aa79202800201030200000200000000000 part288 part287 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part295 : Excludes 0x81000000028000000000000000000000000 0x7aa79b410d600500044cc88000001540000 :=
  finishCode 131 0x100410d43d0ec430dc38040d5207fa1dd485c70b49797e42ff24656aa900ff4d46a4a41e83cb8f5abee6b473ca49506b54c02713cdedaa493f3ae80e78e669199ab60e7073c06f2fc8775747114c491e450da9253c5a0e431818262b4583ebd965a2c1f640cad1568b39ace16d6278f23686f75a0e669c1ff4e17460c382b4f0e0d18369ca0268c18eb63f4bf8d499edaf75510a0e54432d3e0e0a88561b1c2d4428293f6b707a4306f7969e6d30e0a834e161c1899f0e850126f7506a83683ebdd4df673348143f0dc502ed5b3f49bdc99f1bbdab68176e1485a08eb2c7dab7181377870475a801bbc6e320260d2a1f90728170f5b56d7c7013f32d3e0d2e4940b971608ecd3b0f5b585ab68399cd6d5b8c0b88da378ec07adc87356d216b3f40a946c37b355502e9f959fa925787612832924e26815385ca498e267e99492825521b4761aa7205d25e5f94820ef0d240225b5597a87d6aa7e9389a87e523b51e37bbdd502ea1f9c7a591390ad15632d5b6d174580e26fe14447934615012819033c7c95a78f246b317156961eb6b0a095fc695c8176b1ac4da761eb38bc8156ad9bde5d1c9f4604d9a82b0f59444a36b1f8fd69e96ada055e4761cc20d9ff659c87ad4849ec1a53feb56e5a7b78e62796506ad3c3d6b02d3e0f3351d89e1a9591c6fd978761a01fea91e581a8243aab4f9c86d5b9ecab03523a28d53a0f27c76b081bd69e681903519ac21755a9cd617b2c6d1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part297 : Excludes 0x81000000020040000000000000000000000 0x7ea793992580a408840c081030201002004 :=
  finishCode 91 0x3c8fe3b8e23d0da3b01eb8001be719904e7eb83c839db8610e4ef65963e83b7bac1412e9cb4b450e4e2b796066fb59cbd96523b97cdf6d4039d7036dca0d6a3c1e502e72d8c1c0172cca3cce33069404bdd502ed2d58fc8176b0b9b68c1bd5ce5ad5b1eba0943d6ec3680e7581203978b8525f27a5eae7f9389974e4012327219c9ed5b4979c4e671ab7205da8f046452ae673fcb56d7c594cd51390a05cddf356cdeee22f01d5900a8256714932464e5a51b821e8736cb4f584b14c83af758f5e90723bb92d2565d3376ac26381ae840d330e43356cdeed5b8e42e3d92322e16adb70ec3881d1882ad4b402a0941baa339ab6733733b59481a90248713250d9b302d8a6a1f6a8a007db8f92b231e4ad3e503a925105a9c6d3598c5d3366ac35466b472e9ca1f6a89cbce67388c0290921c64e4eee286d1f3304565e8f990732d55eda6d12f6ac35745007aea1b510c6df479ad2d6ab23ccda272d9a06b148f27cda8eb550ee833543f2d15eda1dd388ac36479974cc223d7681a63287dacaa476ada05c3ba5f9875ed5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part299 : Excludes 0x81000000020000200000000000000000000 0x7aa7b3450590c450044e080000041c08010 :=
  finishCode 95 0x862087a1d871102b039c8364153fbc1415a2a4bc1ce40d7f1c46a0e038c9c9d6ab1c843d6b4b6b0cb5540b87ae306e61bf65a5b5843d69c1f1e389c614dfab4f37bc902e88178e266ef96a71fb54126ef40ba7890292637b9c8587b2925aa272f1d6ca496d1c46f1d80f5ac86bb9ec2611524a4f578397c81572bc90b83c9f1ce5ed40eb68c1bdbd4367213939c4e6b0b38b21c6649ea924e4e72f9cce611397c6114012448125ef6f96aa7136a3ca477b7a05d6ab2cf52567f91d69cbce5f2cf527a713670def1fd5486817728c9e54128725e8771fc0f5ca1b5219bf4e4e0e35301ba3ad8b8aa491e4ca0d1e2c51b0eca05e0f5bd0ec398d4593ca8f352498141b61dd073b95e5a7c1e50727f9589ac7c97e1dd6a178620c80e0a05e2dc9ff53c390c817521c3638c1ac8e0faba2603c18e42a49362c72f0f5b8ee59fa92640b9c84e5f079a0f61a941ca06563eda2f01eb481606a038320e4392d21895718583ca0e4ff2b138c2c4ab589ac667b8946c393185902e72f0e0c817 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part300 : Excludes 0x81000000020000000000000000000000000 0x7aa7930105804420040c080000001000000 :=
  finishCode 111 0xec24fe187a1b8721c462082ac00ff545f2cc54927192798b4d38588c4f35849b7e47987753e63d77f13850fc3d73888f5e4f98b4dab72d3c1a23fd9385c154584cd2b402a02ce0672d6714c5e09e680590761eb9612b3d524a4f669b9c9d00b20ee0050dc8f36a8a3e41ce4f3598d07549e9c65436a6039d48729247ae7199fc7301bf2ce4ba61eb073b58ba168733619cd2b2e3b1753e73115233356cffb1cce5e1b859138581076c0238e8c2b17506e5d349e872500f1ccd20ed5b902e907399c9196ada5043d682b399c8155d03d728245c2d5b2e9a466170b56d646e138405ae051b8ba670348cc7330f5a01e40b9ccc3d69f385a61eb2e99fadcbb41ae30a2d3399bf8f41ff66ada05c3ba0e76d1c41dacf716ad946c3d6be201e40bac662fcb175ab6d2d9cce5f96ad946d02ee23707258d8a8f351798441ba733a307356d83e8f316497e5aa2ba378e2348a60b4cd450dca2f2e9cd5b3969c643d671994c35143728bd601eb826e6b2b13ce663bf9acab1f9eae733393acf66a8a05c5a6e23f8a1b399cd5b38ca926362933e6adb890c356e8c09cb51e70f5dcdad5b362c817 (by decide +kernel)

private theorem part298 : Excludes 0x81000000020000000000000000000000000 0x7aa7930105804400040c080000001000000 :=
  splitAt 1 81 0x7aa7930105804400040c080000001000000 part300 part299 (by decide +kernel)

private theorem part296 : Excludes 0x81000000020000000000000000000000000 0x7aa7930105800400040c080000001000000 :=
  splitAt 1 90 0x7aa7930105800400040c080000001000000 part298 part297 (by decide +kernel)

private theorem part294 : Excludes 0x81000000020000000000000000000000000 0x7aa7930105000400040c080000001000000 :=
  splitAt 1 99 0x7aa7930105000400040c080000001000000 part296 part295 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part303 : Excludes 0x81004008000000000000000000000000000 0x7eefa215b33048c18020040000000000000 :=
  finishCode 61 0x144631205e127eec388d42c04fd902ab311fd97b4c3a08f98567fb1fda06ce4eb22cfe4a0acfe485a3a648e8724e0a6e18e0a71960acd615a9b9649fab1b1fdbb0bc388d5b9caec1b2f6a054c3a81b5d017b2d4c17b2d34e4b1b4569a80b377cb4d5e1d86a1c4370c70b41598acc3acc2c660deb0b60f7291569ab235864a08ec61e4a42cddf16d585ab4d37e8fee4f11080169aba1f4e6b0ad4d2626075989bdcd8b3d85282b2f1e4c606522ad4cc3a3fb71160400c52b22d163f4981dcc62cc8f93f4a91d86f0a7cfd2f6f8a0e8259632607315aa839f9632a474a0ad4d4164cf8c2cb535949f9564303c62b8c1cafd614a42d8b2629 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part305 : Excludes 0x81004800000000000000000000000000000 0x7eafb719f2e089240000000000000000000 :=
  finishCode 11 0x801c4376c517292ad050344127e74356e619bd8d43e7094fea935ab706dd47eb4d3e9c90b1589c5c5c2a1f8e42d638e3ea1d49fad345a63fb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part307 : Excludes 0x81004080000000000000000000000000000 0x7aefab59b360c8902040000000000000000 :=
  finishCode 51 0x400ec388d41c5e28b94957467134288abf6303b486471ad1504a91951102b311569aafd392b07e83cb99e30a72f5a69fe54444128328e5ab67e280e83bc1ccfd682949fa466414981cc0f46152830693fca88d42c8503471457313d1c69416b1cc113e9ad34e42c59a30aa4d399c3093f4a0c8395a6b48662e9c5db4370ff3239d69a1c93f2a4be30b2504fcab4d8c2c81741baf8ba20e55841127f461502eb5537b9c14e432d5418b34e47c67d31fdb95e5a6ad56185aac3c9060ad35ea335858960c14807f6d424fd69b41e4c3a7c7a0f2b4d062cb4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part308 : Excludes 0x81004000000000000000000000000000000 0x7aafaa99b22008000000000000000000000 :=
  finishCode 125 0x388e807ad9c761e0290af90c205d072d2da0ee2bf5a2a38d04b1859ab66076adc51137bb4b5aaab1349fca0341d9445a8861106adcb4d385b1893b8e5a3d7486cc3327ca92506ed618dee4f91ebaca640b9fe66ada45d0769fd7ba9874c52517861647819c6a20f730cd0768375239c2ce5ad5b902e83b30ecf5d526a0edab6835901324fd83671f6ad8b4d02ab4174e40ba4fc5a69319406d478c1974dab60b9741a8511804c18c27ca40c824fd8231c4d252b2f4a187154c4fecb4d3fcad55a5f27f569a7f9169bc0a81f82d33e3cd5b486ac64382d654a1cb195a6a0ddedb4614246817060b56da6f030438ab009366b1b0dd8bab4d0e0a876023b17569ad535f0a061af96523d75aac90566160640bf3245ce66a2b927e905631203e9ca1f390a4fe18593cd518c2a01d1ead51a30a80750ecd49483a8c4fa6905922e93f6717c470b6b2d3630a81741bb208396601834614e4292f969a90d377d0735a1505a6a301c135dc80959486760e6917589cb3d839aca64988305013120e0d29173828b85683e9cd2d839ac460f27f9498872569a7d393eb0734a09fe5422ce1f8802d3502e93f8c2cb536a8b4ed626809593d18569bad4d80404cb4d41c9d0c41968a9db51fac4daaab4d8e27318b430093f5f037b174d69a0b98c2cf574988b4debac452e98e6e62ea45cba6da2f85c381822e10db8ade48b8b84182a4d9ebad5b05cac08c3106690b13e0dad6159ead4d2865f95b18b328e45c2a2b0dec8231766a39ba528616970e4faa8c4fa71aed406f75 (by decide +kernel)

private theorem part306 : Excludes 0x81004000000000000000000000000000000 0x7aafaa19b22008000000000000000000000 :=
  splitAt 1 115 0x7aafaa19b22008000000000000000000000 part308 part307 (by decide +kernel)

private theorem part304 : Excludes 0x81004000000000000000000000000000000 0x7aafa219b22008000000000000000000000 :=
  splitAt 1 119 0x7aafa219b22008000000000000000000000 part306 part305 (by decide +kernel)

private theorem part302 : Excludes 0x81004000000000000000000000000000000 0x7aafa211b22008000000000000000000000 :=
  splitAt 1 111 0x7aafa211b22008000000000000000000000 part304 part303 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part310 : Excludes 0x81000080000000000000000000000000000 0x7aefc3410340c0800040000000000000000 :=
  finishCode 133 0xf2430ec370d438840d57ec3636b0b10ce6a7ed4169c2ca0e525601ac281a38ee24ad60508cc59597a0e5a432d5630ad615a69fdd1c71bbd69ab4d905a92f3829fb64069d093f5d144a5eda0f639b419b556589c2ad51fad35c4590836a20b8e471981d65e7fb41dac4e283ad345c66077a8c8d741c9fa527eb4d283a88b4d6d127e9198e0a8d1965ed55404b687f9925e46f91c6b2f83bae8413497c1b7281ad3527e705399a4665a6a887e38893f69174622cc5d148900cf46e0bdf399569ad5b57e9bf569b2cfcbdeafd5a7d06d1aab554bded5b5a68f045c70a2646bb56c382b4d37bb88ac2e8de100d8972d356aa4f938ccc3362ead5569a1c189f2b3f732c7e937a900d67f13e5103d1a8377a07641cad34e2670b5a6c40340170521cb2f510b8ee0dab396a9a0350523c15f189f20a506735848061c18d460c1406ad35b471169f1c9c806be2076382a0e503b1c155c2f7d0773fba0e5613307cbdeb4f40cb88ec3507ed927e1dd2839874a2eb0338dc141d646908b5e57eacd5abee6d83da4fd89eb39303b57e3f49c5d4572c871769ece3b50897ec5ae9e16d63f4b57cfd30b5e1f197ed443f17449fb689a17be4198f8d0132d3c792c5d9492291406c7e96adad556470731e4b68ba1c9662593e47c682d38bc0c5406a603c99a8ec5d3f6ad549f21c19ea2c455aaaf8b00b5dbc414c8391e4ce57586c83372b8f067b8b58540e80d6a035f311589682359f93e4a067338ff283949fc003fd7009e670b969a1dd69ccb09385895507ac63002d39612a0d52496d4e3eb098e2293f2dacd618c0ac25abe61f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part312 : Excludes 0x81000000000400000000000000000000000 0x7aa7c2a3020a00080000103020000000008 :=
  finishCode 141 0x218821e4691bc209900dd06b0a2f24fd2561eb5a6c93f368abec9ca517279cb4f49f9c9e30fa4fd69aec390c41074e4b1494a2f24fd40f145c1ce93f6e1ac5505c6b01cb4b57245d2766a1c4e350a81cb6a93f8c284fe49fb554da6d47724ac8d69aa498e4e93f40ec7276b1203929ccdeaf24fdeaf1ebcdeb20dd27f07d37db80b4220d62d358c761dc396c9171dfa4ecc2661f6020fb1cd566a719279c93f59ab48719419cd6549fb924bdec1b171c93f385c81d30f91fe6b2a4fce2283d385b90de35882d818e0cb6210840ec727510a92505b001c9e0eea3ec99f3d4567aafb3938b4e49d8ece498b1150061dd503ca2f49fb40d639118390260c7065a50e35d9cb41867275518c4e0e6aafb8e23183922e6df58886acf4584d181385a04d38735c375049bdb546ab1f8c1ca0d8c0b9ac2726bb385c6bb506a924e4eb0990267270e3b18c0291181927e3d738fa4ed07a73580017f1ad52862e3494a9262fd9c7d38530e224f3926293f95f68a246636f974d026d61b7e47a9b7e4949f9d485a13cb1c2d46a833171a0f580530e16a21946a6d1941ab09a302e6b2f7c2e3771fc741d86a0a220e349fc517171cf751f5b488378e4e1eb393c82749fc3eb49887add86e16457b83743a7175d64693f93c68e94a1ad364f78fad49a1d39d01f5cb4b28b949438713f569e3eb6b1d06f1d80f59c26616874cc2673306e85765a5b974fe672f0e9ab05078e0a72f7601cf23a5276725303a81e62097bd2763e3419c1eb4d01ce8e2d3cfd23e341eb4ae8c1acf48f2d51834b4ae8c1a3ec8f2d5127ec82d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part314 : Excludes 0x81000000000008000000000000000000000 0x7aa7c2a1060414001000000040c08000000 :=
  finishCode 151 0x5118c5a21849fbc9043b083b98baa3f5a6a8e482a4136d126329150121eb201bc0931969a8092e188b317569ac1598badc3b8fe3380e36adc80541a9c44e07356e40aa0ed44a0dd4facd5b40aa0eca4a9e391c2b4d0719494a2ec42cd60dca91d4621c11febf87119276b55063cec3f8c45982a511073a896608b56c1ba4f9a18791b4821ab707ac82640374106b0faca2e3eb984760bf713f547283b6a1d05c09f2d3b8bde931370cd21482ac24e5b348658f93f66b1106005c7356daae61339682e4e326e1c4650f8335ab6e041ae38898ac7373485a8e5fb388b68c379cca0c3315831d86f1cb4bde62b48bcd474a1a8cce227276a1ab718ac9f2709963ed5b79200761d0820a229e181ce6294fe9ccd82b2935ab60dd071b510413f64fe98a506641320aa709fd9cd6c5d0d893f5a57250d69a3eb51cc4136d21852080646d8b1ae5f40cc1e4e661b540ead3e7aba8849f31ccc9f31b1569e1b54989ba480720743d6ec3803fd621c1dd30298add04018b7356c5c6a31597b16e4a18b8d8b7282dab681352128440fda801c2d033460d69ea092e2c9317baad3e584ca355a78b2ce162cba18821d86a16820ab803fd640c0b18a5a972d3548b291d6aa73550dcc4350f8334e4ee5193c6b4d50f94449fa41b6a1b462080682d836aa498e4eb41d01b53e6c90535da825aaaa099a4290538ccb1f393b48658f97bc5c66e9201ba00d793c21d9071948538671fc27ea4a637aa50ce6ab238d629315a6a91e355a50d69a1b56b18b328c4f9293106387ad2634605286ec145e1e69494c0a0e75f19016ba0072f736c6f740cac7e05c82c505b39043a65b958fc917 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part315 : Excludes 0x81000000000000000000000000000000000 0x7aa7c281020408000000000000000000000 :=
  finishCode 145 0x630e62b42410c24fe08761c4790a4b2d341ce41520eb803fd315cb45523a3ed262b4d396c93185c2b4d1fea20ba02f569a931948a73541ea4c65229cd501acc2d5660da4c457690d8e5ae83b8fe2d360f59c9c1c62d381ba80b969a52528bb388358e22c1b85a6ec378e83c06ab9a4282d51fa41544a1dd06e839c3d71c95ab7306c5a61eb498c629711906217405eb11662e8b4da4324c6374c60dab60c74a1cf6f48293e5a422d36ad9c2669087052870c380883b0b4d51fc5d73818b4d0363fd781fc370cd5b4139c65ab730ce3e19b4ddc611d84a198163148ade061939638197e5abf1c0d03641d780e6b0fac5a67037bac81548b93e4806de3a0c0200e6ad94847ae4f9498c70906e839cbf3250c7aeec0b86620861c1ce5ed314b0a662082f4d8ad5b79184711b4861d81f59cb628b9cb60e9c3e306e87ad8074168b0f5c9ca517860e0720d4ba702e4c5720d5d8861aaf2894a0640d7412873164bf2917281a981ab85c23d72f0c6e96b2b58da2980c127ccb3f3828f5d63741ecb86a4727c9b166908f5d287291618821c4206a87e39a97b67329ba4a0651782d31ba5a563d7315940dac6114c05fc6ef39a86dc7aec0340719690c0c18c0cd65721a415ab66ef2fcc62b523c1d537798ad800eeca453779cd4e23245cbf30c3c8da1035d020e84d65a2ad34a069e3904626150e9ba4dc32cfcfda5037007fae2250e385a04d8b662b68148b291c3ba6bb9c868132fdcd5f385b80e818a4e2f039d89f1ba588b285c3d6517 (by decide +kernel)

private theorem part313 : Excludes 0x81000000000000000000000000000000000 0x7aa7c281020400000000000000000000000 :=
  splitAt 1 87 0x7aa7c281020400000000000000000000000 part315 part314 (by decide +kernel)

private theorem part311 : Excludes 0x81000000000000000000000000000000000 0x7aa7c281020000000000000000000000000 :=
  splitAt 1 94 0x7aa7c281020000000000000000000000000 part313 part312 (by decide +kernel)

private theorem part309 : Excludes 0x81000000000000000000000000000000000 0x7aa7c201020000000000000000000000000 :=
  splitAt 1 115 0x7aa7c201020000000000000000000000000 part311 part310 (by decide +kernel)

private theorem part301 : Excludes 0x81000000000000000000000000000000000 0x7aa78201020000000000000000000000000 :=
  splitAt 1 122 0x7aa78201020000000000000000000000000 part309 part302 (by decide +kernel)

private theorem part293 : Excludes 0x81000000000000000000000000000000000 0x7aa78201000000000000000000000000000 :=
  splitAt 1 101 0x7aa78201000000000000000000000000000 part301 part294 (by decide +kernel)

private theorem part285 : Excludes 0x81000000000000000000000000000000000 0x7aa78200000000000000000000000000000 :=
  splitAt 1 108 0x7aa78200000000000000000000000000000 part293 part286 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part319 : Excludes 0xa0005000000000000000000000000000000 0x5fefae80bf400aa00000000000000000000 :=
  finishCode 87 0x711bc5d03cf002d04fd740fc292b056501bda630ab4549fc6165a6ad156c611a7f398c7ae6b98c2c5bf7b4a8c67b2b174a4b2f896238900f5c57f3da588293f62ccf65370ad3457eb55817293f60acc4149f8afc172b13927eb5193eaa318349495b0631b449fa48a078a0e93d1e9a4bd1c601abb141d256e516aacf7117096fded292b599c5078c0ae85bf8dc2f71503941d48f30460d2f655d184283ab0a49919a7d3616b4fd626b456d13e7060585a9414faca1d69db58582a181920e067622bda45c32914762f6961164505cf6d0ae899d69a4cd255bda45c23d37b4ca490d68b857c4715f30ed5ed2a3315fb9867b4a8cd45f3da5492b4d5a1203f18049fba0b62c05030e2c2e17b4c92b4a0b0b5607b5cf6962c871585b2d3630ab4550eb0b652286f4b87172569ac02f0b2f98228cd281bda438a2bb949b2c4d822b555a6ba0b617ae0608f5ca06bc2c66060c61438af758502c1f619abe585a0c1518cd618c286f4172de399e589ad5436e503402303061548ed5d497b07e3d7bdb53eed5d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part321 : Excludes 0xa0001001000000000000000000000000000 0x5fe7e8e28b50002b4200200200000000000 :=
  finishCode 39 0x751bc7f1480f3ae8b4d907aaf39c764cd5a4a03569a2b38d26b0d7b693358b3185411ad35745a1a83d1d05a6a08d853312d45e4cd9a96c1160d9afe7b3a0758b24ef510b1767b49fcc5ba3d316ec4f97b4874ca1b3165aaeb4d5a05c30f7569a83d561a07b4c2cb725c2c9264cd3d4a09b85ed2b6378b02c82e11d5c92f2e1accc5baaa2c968c2a8cd4631858352b4d0dfc2dd1eb86ce16e8b85b85a6c6160d4b0f45bae67983ec29 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part323 : Excludes 0xa0001000000400000000000000000000000 0x5fe6ee818bca2020010008b400020000008 :=
  finishCode 35 0x2d09034893f7f1c47003ceb02d358830ec58b24fd1ebca354669ae4a4b2782bb8182e415a68ec648ca894576b0d944a51135acb5140e9495c4137ca2f165a8d569a1d3292ad84e592329411eb940cb0156cb1d6d169b20f45372d46006a1c4283c2dd292b78a6140d02741ccb86c0d1ebbdb62f5a895acb15f4b8a13f3d786bdab2d5d16ec1e7288874e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part324 : Excludes 0xa0001000000000000000000000000000000 0x5fe6e8810b4400200000000000000000000 :=
  finishCode 139 0x57200398ba0e2300ec2f8511292b682dd2e1c0b3522a77c3cef759cdb1ead3ea9df836c6143ceafd7f1a45f1b45a03ce80d907ab4d49fab0c2587a6b2f27ca82e523ae07e2cecbd72be45baf750d5cf6927ccb33907a1e75a6a4fdc83f107b2d447aeb3349fab0b4d0d3c81316e802e302a350e0a0ce599c1c4b86c0b969aa0d49fa91e41e874ca23149580680a06ea0714d733da50463dd49facbe7b6a7847bab4d6a8cc59466ac747bada2482e158ecb037b48b0cb86c0d947e3dd49fcb0f7b4ad4565eb55630fc69127e2d587ae0b92f59f5e2e4ad35666d22d35b462cc0111ebc60630a8334668f4d6a31ae507b010c34eb33721a8581066f698d725c9505bdb47ba9fd370cb4d7b68f74d7211f9462c1527eb1754161e76b0c3d327eb58d43887e079d74451802f5a98842ca6524ad3660da8bdccf2835612c1b152ad356ab2d3609fcb0959dbdb47bae475a6ad365b1606605c2b4d964a1c57b68f75eeb398cb9293f6a3bd96594b06dcc6b4d49f97ae5a6bda61cdaca4bd6b450f3ad0f69907ab4d5d16070f4e0df41c6302f6d35abda5d0801d86a16530b844f259d16ead347ba93f2839495d4288bf893f587c1e7599ca25587c6b55aaad3568441206d127e5c348b4d6b1cbb07050661e7406c83d605c3b14fcaccd676833907ab3b969ada2d345bb074c5bb28be27ca4fdac0e9c2dd1e9ca316f1b45a03ceb03838293f518c2e144161ed61963e6e15a6ad3e1529b86170a4fdb4531a427ea0ce49f874d27f003d69a83359d8b85a80f3cb4d170a0cd44b2ce43cee63969a4fd (by decide +kernel)

private theorem part322 : Excludes 0xa0001000000000000000000000000000000 0x5fe6e8810b4000200000000000000000000 :=
  splitAt 1 94 0x5fe6e8810b4000200000000000000000000 part324 part323 (by decide +kernel)

private theorem part320 : Excludes 0xa0001000000000000000000000000000000 0x5fe6e8800b4000200000000000000000000 :=
  splitAt 1 108 0x5fe6e8800b4000200000000000000000000 part322 part321 (by decide +kernel)

private theorem part318 : Excludes 0xa0001000000000000000000000000000000 0x5fe6a8800b4000200000000000000000000 :=
  splitAt 1 122 0x5fe6a8800b4000200000000000000000000 part320 part319 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part327 : Excludes 0x90005000000000000000000000000000000 0x6bfdaca133200aa00000000000000000000 :=
  finishCode 79 0x7d1d46d1bc5d03d6b20b6e0c2b93cb2a8cd15dbda47c65eb1fdad8c45923ea39526b05615da4fcf459fca4d5aac30f6971dce6d41dacbd02ae3b9647b4cc1315fa50d21a82b1fdbdae7b4a4c45b681549fb50b037893b4707af17ad49aa2b7b6d1857b4a4156aa93f0d7c9057b4a4fd5867106ac61b860eb3da47ae1af0b2c27b7bac8cd7b2b0558c370a8ce486b0ad27ec2b95fa3d78576b4549fb68ce350cc0b6dbc5601930c2336581a8c568a2a141d8a86597b04e615b98e609bdb5416b2f390a435076c2b8986afd2e1ad153c399c5c3735861d6aa3d741dce4f5aaac0835594c93b60eb9ad44a733526931e72cb9ad6aab2208835621c81b7aba8ad5faa0b52386be7baa50e7ababf5456b3f518b18ea1f8be24fd2c5907af1859eea943405a0ace672414bd69438c2c90d5a6a0ace661cf728c5eb16da4c5056be205641a873d6270b6d02a0ab96aa7336616458101683b512ce4551cbd5e40ac0cf8ff64d5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part329 : Excludes 0x80005200000000000000000000000000000 0x7bfdad50330c0ae69000000000000000000 :=
  finishCode 31 0x7d1a8711646f0c56ce2bf64efa0d5a86605290949618597c517523a0ec373145d68a6059826afd486ad35036507969a525314b306a2086fb54094f2cbc986a45860a070d6565ed5947da39d4165e140e3d7a3ece432cbdc9e503001c7212e1ad54a0693182c22732fc940c38a717522ca476c0c0ec446164858ec549b0695aa941ce2f3966728861d6927058e66503 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part331 : Excludes 0x80025000000000000000000000000000000 0x7bf5ae8c3312cea00000000000000000000 :=
  finishCode 43 0x1a83f0a06d8318ce17ad27e83b89fa931902aa4d41dac04a79252e616279785845e119b34ecdd31851daa0edcc3398deaec2d8dd206387471852f097ad84616c1cf40aa0ed1852100a4a7876ac5d9ed22bb6c2303230d4722bb62ecf6972bb607e33893f4109fb06b8dd27fb41dce6b9604e1187306c8d271369da8e549a4fd37bc73328882ce83ac615076be318ce3da65a68f5c39e1a99836e592f59c850773da4dd2187382b9ae303312c30e705 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part333 : Excludes 0x80005002000000000000000000000000000 0x7fe7ae0533500aac4402801000000000000 :=
  finishCode 53 0x2007119c5d1a827eb58e02b061f3f100a8353d7d071501a4fcf5f0aeca4a903dd65a6c61527e525a30a5259ebb2335076f692929f8e6395fa60749fa35e7b4c1d55f260741db5093f98b6605292af90695a8c6070b6cd49581ea72054a2e93b30fc8357317074160281ac9647da4fcfca93b57ccd5158ca43527e7e558076b3dd53fab5149da088e30b6622864c76b2d35cc27e547da4fdeaef6d9abaf697bab0b4a07140e3f16c2f5987d27ed598f5e4e50d1abe6156b0b5c415fc80b57c987d06ab83db6839868d85ab5162087153058ccc412bdcb4d1eba3347362bb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part335 : Excludes 0x80005020000000000000000000000000000 0x7befae5273000ea44281000000000000000 :=
  finishCode 105 0x8017c741983512037db60c630093f5d0a06d624363909686150b93dab2f6948ecf69698a3ee0e31c84b05b180730ce6348eb965cd6503239cd2f735b565ed27216a9ce4f72cb58b61c85a5f243528318548ead167b4a435ab33da60e6b4d5b0e4339ad4165035d1ed33175a9741c46be493505bda58c281b110c2d3662e8ed520ed3781823a39a8690d62ea43601bb575632b4d8c2ad071749fc1c569bcf6d5198ec5ed250349fc503630e45e0bd6b02915a6f3da45c2a0b5a8b5667b4a4fd4161979ecab1d6b286ad1f6ce330c2243658e86cd27e0c14f127e6bb96923d7374b5466acb566374a4fd21aa39919ad29523b0b527ebc2c0d617e5506278b8683486b45c341a5882c5d9416a4751ca088d59416a456aec7d3518a35585ab0278c4f6120e73575cd71817abb0b51aa9fd49da50d3ef34a569af6d4fbce6b7b6a088d54fbc1850cda435abb39adbc466ba072140d085a6cc5d5a6c90d7b493367b69f95aa318549f8714e446ac1752f5a8e68c2bd5d27ef752e0bf27c34de2669f956ab3da521a9f5921a93f6a8b607e3385eb49f86de060a4664a0b0b59c483cc1b368b04436e0c16014815db0b64a0b0b6622a4663e9a4bd8966d1608a8ce60dbda58ba2e1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part336 : Excludes 0x80005000000000000000000000000000000 0x7be7ae2233000aa00000000000000000000 :=
  finishCode 75 0x308ba2c82bb9ed24fd2f5987c7c63fb6c1bc6219c6b09e65110e7c1eb8c0c9315a6a4fd6c6a13828bb0b6622c606498ad343d6e6383d6c2d839c61526324fc3d6c1574127e51783d672529097ae399c3b17b4b0b49fa93f560c3a1eb83ac7330b5cde3f8d63001eb3f0a2eb224fded32505ed341cd472919923324fd805a2c1bd5a6a35d27e50d7b4948527f2bf4a4ab45701a8505cb4d2909815ed2629390df6b4d9ed2e59a0e2d638c0b0dd3fa93f474ca4540db50d6316e370c1d4c5661d5a6cf696c17c7b4a4fd89f4615a76e6b8c2cb2f0b7d18540db58e63501eb5f127f18a4c3eac18758871334e26c439ed28fb728c93f38b9c5e4a0a4fca2ece3da5d05a6c8fb510941ca4ab413f527f2d358bb0c208a0b948ef759c7aa033fab9ae0f6c5b93def714668914bd68fb988a517 (by decide +kernel)

private theorem part334 : Excludes 0x80005000000000000000000000000000000 0x7be7ae0233000aa00000000000000000000 :=
  splitAt 1 113 0x7be7ae0233000aa00000000000000000000 part336 part335 (by decide +kernel)

private theorem part332 : Excludes 0x80005000000000000000000000000000000 0x7be7ae0033000aa00000000000000000000 :=
  splitAt 1 109 0x7be7ae0033000aa00000000000000000000 part334 part333 (by decide +kernel)

private theorem part330 : Excludes 0x80005000000000000000000000000000000 0x7be5ae0033000aa00000000000000000000 :=
  splitAt 1 125 0x7be5ae0033000aa00000000000000000000 part332 part331 (by decide +kernel)

private theorem part328 : Excludes 0x80005000000000000000000000000000000 0x7be5ac0033000aa00000000000000000000 :=
  splitAt 1 117 0x7be5ac0033000aa00000000000000000000 part330 part329 (by decide +kernel)

private theorem part326 : Excludes 0x80005000000000000000000000000000000 0x6be5ac0033000aa00000000000000000000 :=
  splitAt 1 136 0x6be5ac0033000aa00000000000000000000 part328 part327 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part339 : Excludes 0x84001100000000000000000000000000000 0x6bffee92634b08222200000000000000000 :=
  finishCode 17 0x1986b1c4291b0b647d93a4c5261f0f5ad07319ebac4b411a4fd03abc3da6466b48ce62c11919ac5958ebdd4dd2c60f8ce629037893f466c5952f5a80c9ab3da498724c4bd64d5837aa3f8e621eb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part340 : Excludes 0x84001000000000000000000000000000000 0x6bfce902430800200000000000000000000 :=
  finishCode 153 0x881bc76180561ac281b88ce3a85211e6c83d0f5948c9871c5cc565fb0f5c3cd2fd9c5cc56721697c23f2618a9ca4673138b9ae6622a7f5276b452929cc5d4290b30d2148dca33da4e2eb1d26197ac3d6d218bf6f69419b4862e58f6cc561eb609cb4f62d97ecc56e23387218a4662b3989495c030fc62b0f5c2d77359cc638b948da4291bda639893e43d67d79ed293f1eb93e5ac72128291c62938b9c94e67187ca465238c5693f982691f5979814a0e731751ac701cc291a8fe2638f5d27e1eb6317449f8e9e7ab869c98e1bb263c2d7526cc607ad7449fb4ae3dba934bd67330ddb8ee155b04d4564c758cd0732e59ae4e66d45621685d15442198416a6860311504690d9ed24896a98a44b3a93f921ab390e2cf6951fca4d4118f8e41ea40a4d838a93f58038b28fc9aa840a85eaf1ec447e6c53dbc1c503a4c396325eb3f101ab024fc36b28fcd8b1edcd664c35018a84743130c5423cd580f4261c6fb2dca4ed6522db51f9a82db37dc2a14a1acbdacb41ed64741a565eb352dca80dbc466b4f649f931cbd6f69811293f561ac5c19816bac0941ccc98f391da96d510629c5d3fb41ed47e2db3a0e423cd986a3cd816e9a1d0ba30d6728b58c156c4d382c1ee2bc8a158b6597846623f8c2a80d8565b90d0b58d47f293598735cb353909ccd4c615cf5713fb9ac376f758b2ed63735b78b01d02db96461c551ca9349870a852861c516da8fd98430883a166ad638b3af5d2dc931c16ab4f263ca032dc8a84b872d2d68263c8cd5918f3416af7596462a153098f2d14542660dc6731bdd53ded63237c5b93d8cd5f59787145b6c6298d62c03d70dd82c6733a8fd8b7358c34eb0284659ca9345b646069dcdb304cfba037591c4c3581cc6605b67b79c8e2ab83d9c94557307615aa8fd0062dcd2f6b1ac8e6159c9659ca8e549a2db (by decide +kernel)

private theorem part338 : Excludes 0x84001000000000000000000000000000000 0x6bfce802430800200000000000000000000 :=
  splitAt 1 116 0x6bfce802430800200000000000000000000 part340 part339 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part342 : Excludes 0x90001000000000000000000000000000000 0x6f7ce820132000200000000000000000000 :=
  finishCode 111 0x3a8cc358fa148dd84fec5eb40d9054816c6100d702f5ad3e494a50c36ab35965e93f5a7c9430da8b8d784e10566c241649fa054e671c5e71dc1adabe733625c4a74059ccdd85208264153a0fdb207527f20f569af6d9a629e1838a80d046b4d551a45a0806a31988ac5d5a6bd965a6c83d40ecb4d581b48fa100e205b18b4073db04a1c0cf49f866669e9feda8a9435a6a387eba0f63d735dc90d5899fedb0253c6e9526833c5b7129c776b4d7d127e5c2e8b4d5b14815bc3c740e931e1e3c61640ea45e30b250c97a4cd406a5882d872e3c7416ca4d898ecc350a2b906a83b1fa901564171c83b6d17438bb6073357ec2b56afcb299cb2ac1b0a255aaa82614fa054d772c0c53e29f93c6914c551cc561ac5d037f1c152847148ab3f87aec53987ab3f4a18b6e3fdad3548f287e523a48b4551fca4d3fd9f7657ea80c376b4d466c5975a68f5d6aae62d345c71fece0aa1f5228a16155b4e64868f5c5b6b4d691cc550dc50fca4753148a581a30ab3f0dfb98e3fdb606bb9606a1172c9fed6aa581852ea0972c8b8d4072c0c97a7fb5a2a80e7bab4a45c6a3f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part344 : Excludes 0x80081000000000000000000000000000000 0x7f74e8e0070810200000000000000000000 :=
  finishCode 37 0x3a0d6368ba360725399c1be08fa45ca22af72019cc5673069c37e943e871758eca0941d9014c5241d286c82b1fab48d8350fa206e06498a50570fd4467302d3c67f541d906ce62b4d9036b4d986e41d7d17857080a5078a2273137bc59d5a8a0549bf144482af6996966f7398945dd8398a0ee466a054df6415369c94305aa334df64037d0e6328949fab5120a904d785a5cf6941d9cc4e849fca25591a02e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part346 : Excludes 0x80101000000000000000000000000000000 0x7f6deb10232020200000000000000000000 :=
  finishCode 47 0x330b4148d2076127edc103641a9cc6368c12b7b69aeda5e83d0dcad34e62e2368ba2b883b20193963edb8ece62b4d901b1cc569ab4d9076b038e6240d7d0d771f6cda307b5819cc47e640b5710766e1960673158fc6e1711b45a07e640b49fc7315a6a87e0f5ac0d48ad62989a35093f2f7a87e39898adeeb08c5edaa1d597b046627a4fcc3ed259ecad5327298ad69ab19948ec5b5a6b60aa2f0be1cc548b291d6073181b387ae93f233c5c36b1a0f5a8e4e55a6ad3648cc3a369ca0f49ca2e1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part348 : Excludes 0x80021000000000000000000000000000000 0x7f7de88c031084200000000000000000000 :=
  finishCode 105 0x1063a0d43804f9281b5890148d785a1a5f286ce6293f59fc6e15aab4e637b8f5e50d9cc520531a5f2c64e6293f486ad3568a7e2d35a5f2c0ce6293f697cb03581c9055a69bed69e7314819c49f8eee594a50cfb66e16b0cb457289cc4fb6b3f4a1c7316c1d45e1c83989c86382948e6119b8527e511661c0399c511291bda6405a4fcdef1444e63208b21c1598735d07b41d9c5d69ec21887db8ff688279e238b0de0eeb4d6b0d0697b586460b191e46ea7d7697cd3d61ea0156732014e42cc3605235e168398b96649f8fd53e33dd4dd2a03631c4501a4fdebb2c8c9faf698d766e9944af6d5a1a85a6abde2f58fd4fc35dcb4f7b4861d836e634f8cc1b048b9663023d789171814ed97aded2bc350d80b849fb2934dd27314b0bc317ad187098519ae517b89334dd2b4d6c1ecb24fcff66e9398a58e4f98aa5c38c2b91cf96d617359ba4bd66e99cc2e6b6c0e83909faa2551c9ba65a6b98e49f9b85eca7fb8bbe93f63119b1f5c39e36b5a697adcc70dad78571ac3989cce0e7948dd8498c8cd1fa9aa650da4fdc06b0e67148c7ea0c958cc6fb170ace64a18fd4df6733741c03998ab67b4b56419e52359aca497b4a02cfd72c8cbd693f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part349 : Excludes 0x80001000000000000000000000000000000 0x7f7ee800030000200000000000000000000 :=
  finishCode 95 0x418ea03d5c4690a2f2474a0e413201b78c03b0261940ac1d7baa4fd07a517290b582e38e6293f291b9073127cabe65a8a8863f1907649fcc22105235b127e82d37dc4f95a6c48d37dbda5ed31bece625038e62f6d416b58af9985692b5a6978ca067313829c8598690a06b4d202aca6722a0ed65e8c58df6731965e5035a6bb0ea388d81074826bc3187316b127e523941a7338c0cb4d5069335283207520f208d69ab4d9986b0e431ccc81a5235a6c93f3989035cc5e1845005c2c5593ce9415239cc5c7b29151f290d592c35746680f4bd68d55a6a874e62a63d964a1a7dd27e5eb599a4751f69e7923a83d406c8e748ea0b5986b1b86a169b2c3d2622e13909014e2f20ed4172c8ce62721399b709e395f2d65594960d1d273148fad3480aa0b9466b4d1709cc5cc691a06c0e0b291543e73159143ea453f5ca0d0dfb9662cba83427734bd3c690b3988b852873dd522e705398b58b4d8e0a94158165f06456aa5d5629cba358403730e664bda0e6f756b09aed3c670559da0f528693f8e0a83d969ab5137db58c6148dcc494cb495a8876daa72c0d63ab495a6c731406cb4d (by decide +kernel)

private theorem part347 : Excludes 0x80001000000000000000000000000000000 0x7f7ce800030000200000000000000000000 :=
  splitAt 1 125 0x7f7ce800030000200000000000000000000 part349 part348 (by decide +kernel)

private theorem part345 : Excludes 0x80001000000000000000000000000000000 0x7f6ce800030000200000000000000000000 :=
  splitAt 1 128 0x7f6ce800030000200000000000000000000 part347 part346 (by decide +kernel)

private theorem part343 : Excludes 0x80001000000000000000000000000000000 0x7f64e800030000200000000000000000000 :=
  splitAt 1 127 0x7f64e800030000200000000000000000000 part345 part344 (by decide +kernel)

private theorem part341 : Excludes 0x80001000000000000000000000000000000 0x6f64e800030000200000000000000000000 :=
  splitAt 1 136 0x6f64e800030000200000000000000000000 part343 part342 (by decide +kernel)

private theorem part337 : Excludes 0x80001000000000000000000000000000000 0x6b64e800030000200000000000000000000 :=
  splitAt 1 134 0x6b64e800030000200000000000000000000 part341 part338 (by decide +kernel)

private theorem part325 : Excludes 0x80001000000000000000000000000000000 0x6b64a800030000200000000000000000000 :=
  splitAt 1 122 0x6b64a800030000200000000000000000000 part337 part326 (by decide +kernel)

private theorem part317 : Excludes 0x80001000000000000000000000000000000 0x4b64a800030000200000000000000000000 :=
  splitAt 1 137 0x4b64a800030000200000000000000000000 part325 part318 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part354 : Excludes 0x90004202000000000000000000000000000 0x6bffb5b5365c884ed012101000000000000 :=
  finishCode 55 0x390a8378842e8b024cd28aa099ebac1d526ad567aeb506c2d08c0724be2b4d96aa3b5731ca035aac60e18504ca313d4c903526a4ed6aaa4d9ab63d15aa872500b309d6aa5f1860d85aaca09522ad5641da91d7058017324c43927e1980b59406c515301732d5416b31368c1b0852728e41a683b8f5d406c399272a09948e5f16f1845616859f8f5e05ab54d86b460d02ac5b7b2a38afd834d077152cd637b6a4ec7af354e307201567ea2318a4d0dcc4c71578f5c37320ed6aaa2b5307a30ae47aec399a5eb4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part356 : Excludes 0x90004200010000000000000000000000000 0x6ffdb59fb2ce88c61033280084000200000 :=
  finishCode 35 0x4c11c51167ab4744147f2845ab693985732d5437ea81b0c02c6d2c523cb45499b307e59acab1369b97c521b3025626b459dc4b1ab7291d68aa1192868359ab6709012cb456ad86fd6368e1989e28ad6230f5df4541623460d48f18398a323eded6b11594cb115aaa20b55944aa476ad9c26 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part357 : Excludes 0x90004200000000000000000000000000000 0x6bfdb597334c88421000000000000000000 :=
  finishCode 147 0xe4358ac2e89e430705390a58b4d47168ab02cf566328fd6632c6e5238b6d606b1394124cd1e8aa8b1b83762db53121b130c7a2b5558dc3d16618051218399aa083558dc5d950ea4e5edb3495c7b0975cd69151dab56c182ce308b803052672cfc7a22bf40ac1bf598cf518c1935500a0c94a2c3d18c1cb5541d832544580e861149ae6b944a2db23ccb0396aa2db51fa985cb968eb45860fb72c6d606a4558dcc23502db923f1839626b3f23cc882886e350d5b58180670392a119076c5b51c8f445b683b9cb2b3f38bac4e504a894e2e2db710193172d8b67239660a7a825a5eb4d6a8cd2f698c82b723bdad69aa4d15fb38c02980bd589c8d75aaa47dcdb131d69aa256a9c1715a696856060c95aab9661da8725805403931ea56aac211e8b501c985b62579ed6a1172bc1a567ef63a30a2db5aab50c203255440acb5516da8265aa9ebe2e6a37cb968050e4a983d79cd68df15fc1a567ea479aa31857b1b9659867138064aa0a1d837e9274a28f5e57ea98a03964e3613d8b5255fa3d7593c9c2876392b56deda9274a2a8894356d43b1c9564f307587ec431e8cc1d611ab67b79a5e3d76b18a7c5b647999c5510016daa10c20ee581a515a92a31522ae8cc2cc6597930d272945501cb45598acbe5a2cb31968ecc378b42e81c905ac83b49ca5154132cbd748c1cc13621acbd266e3d984ed6583da82641dc60d8b65f1581cb5571ed07b3f2b9ac76aa11499b38980b6d504103723d1613cd25609a8ad6627b79a7ec0f62bb52457f0f5c7af280ac0f4569b1a5e0f6c1d412a93457f06f984ee6d6aea935ab6a4d9ab6b4d (by decide +kernel)

private theorem part355 : Excludes 0x90004200000000000000000000000000000 0x6bfdb597324c88421000000000000000000 :=
  splitAt 1 100 0x6bfdb597324c88421000000000000000000 part357 part356 (by decide +kernel)

private theorem part353 : Excludes 0x90004200000000000000000000000000000 0x6bfdb595324c88421000000000000000000 :=
  splitAt 1 109 0x6bfdb595324c88421000000000000000000 part355 part354 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part359 : Excludes 0x90000240000000000000000000000000000 0x6bfff5ac804db2001248000000000000000 :=
  finishCode 37 0x86184077b20ce2882db26ac80b6ada0ece8508c4d55a79f01a998a6c3d8c2cb4746cb52da451104a57b85326ed6adb57e5a6ad2cb7b28e42eaa3f944ad3762aa0ed44512cb1f2dead3c9aad5b46cc1b96289355696da3088c0b6c37f0b5d276c62b8d2f85ae3d716bc0a58b962d77710016bad2e2dc9355a92d3789aa29526ac8213545aec1387aec4357ecd2f7b9a8ac7ae2a5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part361 : Excludes 0x94000200000000000000000000000000000 0x6bffd544414ca0001000000000000000000 :=
  finishCode 155 0x380d8330da0785e45513816d9e0d3784a2d656ad9795a5e72149ca4553c49168b2514e425c3390c945501cc5b1e68f5e390a7823fa30707b591a43d28a721399c9451e697c5804e12c5112729456b1c0af579b13569e3ab615cb4210740f34be2d5b96960af98267b76adbd75ab70af56964d56b1b4de609b57d66a1bf531cb341c4b96d2f1eb82be697b16e6b18f5d69eb0298d6598ae0476adb58d21eb4f498a103cd928a9399422d6361cc25761aad2d69ed630d5a51584551605c05b698298a02b03d126ac2a116b856e69eb55dac6d5b85ae0ab85623d16add07d26ab4f5abeb454913c581cc2b1589d07dd9cd6b5591e2a3f57ece576adb0adac5d14c560376b478b962d762dc5cb1eb9d03a1f766b1c1f5ab66bb9636c35382c60e6adac6c756d6316bc9e2e8922181a72e1c0856b1c3ab360c43c1a5e4c3736cafd61fb95e0aec27169cb085887460cf6f07d697a436261ad55607309e306d49501a98d22436589bdd5ab6c4d0d0b4f45aeb4511fd0771508f445aea03401a1501c7056adac0d67ab1b0a4cd5b613b14589ac2b512c7055805aed539812c5b3828f44987356d9c561606605b6ba1cbe0d29ccc5af06b52870685744f04c341dc98e9db1568f5ce0a721711a053168f307630ad5b16b9f76598b95e6b2972d86a927968e7dd6b2b56daa3356c5aed5b85b6ac310e57d8f3563e72116ba08b478532c43593cc1d490a515e46d174560343131dab62ab0dd9c14e66cc3387256adcb0d05b86ed1fb356e2e1ce3d2619c5c5aec01e08e17c510571472d6392629396adcb0992726f7515b54e49c933c2f7131d456a3f37bc8fd83dad3d80680be302fdec70e6da5e3d74a2a989439ab6b4f2e5acbc7aec5b9ac6b1f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part363 : Excludes 0x90000200040000000000000000000000000 0x6f7dfd460a4c88001132200040008000000 :=
  finishCode 57 0x1063800ef5a1585a6b987056adc5c54a18b6d20af6396063d15aab08d5b71dcafd834acf496229f16dacf61eb92c544382ca4d162b56d546a07af0b6c58b06fc58b24c58459187b250cb8ac550dda3a659eb5152863d76ab91e66adb589e2e8a21c15a4371eaf2c0e30ad6361ead3568aa476ada98b206ce59fad34ff61b759fcc0b1558b6c557315520ac0b16d9fed69b0b6c93b461587a2b15a2ad345b67b7984690d62a970d69aa23086e398d5b50ec2ad523b9465aa9fedc4531b048f8b6c376d3f8d66b556aec61671dbdbdcb334fc5b67fb6aecc5162a8b6d43b0ab548ed5b61188730f58761895a28b6c57f30d5cc59fcd6325ead3568a2db5a6cb45 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part365 : Excludes 0x90000200400000000000000000000000000 0x6f75f564a4cc80013202004008000000000 :=
  finishCode 111 0x611445915853105683b651f4168c7211719cce1498b15283909c5e6adb14c4f7302d67ed2f98aa7213912c40daa0d5784f6293490a515a932bf435e0ef8e4ad5b77150077a58a62515ab70efc37ed2f964e92784f62e3392b56d6970a7c33e7256adc72537110641ab6da3dae481b94569a5857b797c4e2ec3d399b780ef834aa3f51297c6493ca2538497c5b46415838bc1de0779ccda730a7d67ad2f1eba4e6077ac9ce1293981deba378815399a456077a8fd67f17c5ac717141de81561ebe8de03bd6443141728cce5eb355a5aa0d0460e39797154663d1508c4d5733ca0b48a86fd586d230b249c352a3361ea7a6598cd398c2a056641584e1643e169707b93d2b230c4b0f562717c56469e949ccc230d2a40d87ac53a0d272f59096341a415e3d74a2ac3538604cb4d4a2a4544832b0939987a3d79b4510f04a174384be87256adcb1b2f883bd49b356d5f62b95a6bdbe1e88b160c6adbd8e6a4a4556a60ef168cc573998b4639983bdab671777174077a70b1b5a7d185493b99e8c28b163d4bd465a59cbd636841e08817c41df09b4f524d50beb56c5a303be0c518cd3958483bd6972c26077ad2da72a1f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part366 : Excludes 0x90000200000000000000000000000000000 0x6f75d544444c80001000000000000000000 :=
  finishCode 67 0x1e456080ac80fd57426ac9335aaac7c5b61e53979ccdb0701fc0f28b6e5aab56e1c8a7a5206b351649c5e412933683dac8d25283b6c1a43518a33974f5e93b1ebad156aaae2cfe490ac4437ea2356e09aa0adca2b3f50bb03673687943cb0f5e162b80d82881e540dcd5b1ebc2db67190164c2db384cf5f1d78f5ce131c95383848efe2d5b4ac7aed5b49c8aae1dfb5147aee00ff5a05603ca820b4478f359548ed5b2d9972d3c46034f0af4b3f356c366e4f266a87658fb59564f3db499a3d72e58b8dac4f11c6507ae5e2c05cb26acd5b15ea50daa3249d827250d24e1bf604cd37493ad2cdbec8357e0dfacd437f316dab6363891e00183bb16c9aab396ada51437eb35613cc3f59aad2d5c5d14633db566a8fd49086fd23f0b4565f28cdab62d1 (by decide +kernel)

private theorem part364 : Excludes 0x90000200000000000000000000000000000 0x6f75d544044c80001000000000000000000 :=
  splitAt 1 106 0x6f75d544044c80001000000000000000000 part366 part365 (by decide +kernel)

private theorem part362 : Excludes 0x90000200000000000000000000000000000 0x6f75d544004c80001000000000000000000 :=
  splitAt 1 102 0x6f75d544004c80001000000000000000000 part364 part363 (by decide +kernel)

private theorem part360 : Excludes 0x90000200000000000000000000000000000 0x6b75d544004c80001000000000000000000 :=
  splitAt 1 134 0x6b75d544004c80001000000000000000000 part362 part361 (by decide +kernel)

private theorem part358 : Excludes 0x90000200000000000000000000000000000 0x6b75d504004c80001000000000000000000 :=
  splitAt 1 114 0x6b75d504004c80001000000000000000000 part360 part359 (by decide +kernel)

private theorem part352 : Excludes 0x90000200000000000000000000000000000 0x6b759504004c80001000000000000000000 :=
  splitAt 1 122 0x6b759504004c80001000000000000000000 part358 part353 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part369 : Excludes 0x80004208000000000000000000000000000 0x7ffeb554310c08c31061040000000000000 :=
  finishCode 57 0x1f06b1dc711a8620c566115d12568258e429f99ea692f402abf63739c85b4303b10ba141e5a9c1a638ba42d5e32d34e2eafd948ec2966174470e42b478e66b53550bf25f1965ea0b71eca096acac6d285414132d351f28e9522b288f991d2b33985318146fb594fd28d5485b915ec7282dab690b486c5f95a99c15986d17456168e725698cb1b3f29c8543b41ec252af9519ac6dc7b282548a717621c5ed50ea914dee1750c0a876522ac0ee0b8523f24c4bdb2d1d5877124597a7ce41db4dc16b460d442b29522c8357b7cc1358da91d98580e42b4d8a0eb1b904ab47495cb53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part371 : Excludes 0x80004a00000000000000000000000000000 0x79beb59830cc09675000000000000000000 :=
  finishCode 75 0x10a360ce388b02cce6adc1ed076b5152397b47b2525288b50285987251b292b68a1d948e81b5a3a87640db56d80660fb334dce12c3928197c567b140d1c430ddb28fc10aa3f9a62b4739097b68c19c85ab6e41e0da1a8c01bedc7b140cbe2804301813eacd5151892866adc81b4f4c933384b0e64f4a4cdab65f16a21828ba47662da0ec4d32cc5ee2e6b83da9350372935581ecc80541da936376b30e41e06e1c25044b1ea32505ab607f41dad1dacaa336b2c81b837cd514979fae481b8f524e83b6adc9f3523a875076717411ab72d4d036e3b9ab65ed41da876522b30e4320ba370933392a06e47ea05412723f47b317b50372c6d68e709501184b07b3022503723d5076c099472b531ec8b56376a0ed9059ec6e71ec97b589b354cdceb47 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part373 : Excludes 0x80004200080000000000000000000000000 0x79fcbd1c340c294211c0402100040000000 :=
  finishCode 93 0x1c85d12c6013886126694571ec3b572c9ccd00a835399c62b561004909c85cb2517969ab4514acfa1c8d4248594523c1630b3945d8b662b8c0cd5d613b56e83c8f66302afd736981da850fcd2949598ac99f24f630a725990561ac1dac6118c0b8f4c56825390c1e6838a3ada52c4d72ca095606ca18146bb3dc5406d5d315a08e6384ee35f6ae81f493a1479edf06f730b88ac3dc6725984d86ab4d62da0d4c27206d8b6b559b464144560e4a5039cd692771ea49e30398ad58580e42b3d9aca6110d2b07d6a7249cc0e8c3a30ab4d497a49dc4493c61359ecb132f8a82524e90d8c56d4320ca43062b28bcb4d46bc48d5a28724a2eb000061acc1c5c7b0795aa9814ff2943dbe837c605c8a92f261a4be7b7984e461ca317369fe4c0ec83e0982d361ec9814c22c03290a18ad69b145d0370abd69aba1b0c51832eb1169fb575444838abe8c0a06c3734604ff318ae412b089c1f083b5a6c517412b10b53925ed5d7b0a8460df41c583a5e3415cc1328ba47662da015a63178d67a613 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part375 : Excludes 0x80004200001000000000000000000000000 0x79bebd1a382c08429402038000840000200 :=
  finishCode 93 0x712146c1886a16028d94960840ac8258c0a7a5ac62e1302acee83da7a63065b1167ab064358e3d7ad56183711cf24bd68b2504002e616a4c6068c1b91e30a7af5a2a4be6a4b58d74530a2282181d41723d457e5d74a0cd49390c80747aa78e599ec6b258c2a3d56aa8078c2c8f56a1f058194302b10e482a05560662901bcb03397c1e45c2d623f64039c84c568023f66aeac0cb2f30adaba8256b1c8257c6e95a2a01ce423d7900e82ba0f2d2941aac0ce43201da882190370c56611861ec3358d282a1f12acaf96b29aedab707b403b54635da4f630a9f3902aa1f309a090c2c6e522a87d3c2ebcd4972c8ed500ed4b900f2475a929e2088075a3c72150f9c866a4a3f502b3e0d4260d6181544309bdbe57eac95636b49384b54e5a6c61502ab4598b66ed150cb4d50bb16d68a613403c3d78c2981dac508cb290dfad158b65e3615cb29412ad15ac6c19066160390b502e196065f94fec8075aa933e8c0acbe0ded495aaac6e6adac0d48af51170ad3568a3d7968ab55641aa317e500e721470cd65403ac0e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part376 : Excludes 0x80004200000000000000000000000000000 0x79bcbd18381c08421000000000000000000 :=
  finishCode 97 0x1604f0fc41cb88827821b0640a42b498c0a1c937d8325637310cdf65f1309c62b58dcb2548b9434a4a7e59ab6b4d281c30e24285118a4ac8358cc28ae598831ce6691d969ab4d906b2d1d636d5b924e9fd5a68726292b508296521469bc915314ac6d41ab532869495ac493cb1b30998a5cdb2d4d416c3548aa8fd266a498c2251b402cc1f399ad4ca22d4388d82e8521390cb2f510a4cca368e430d61b892b523c82b6a4b56d07734bcbe2b2f93f2b4540bb95e736c309f9597ca0b6a4a0d5a9339ad8a2ca2985d79a9250d517984dacb2874986e4f4fcb58ca1a62b5617458dc9456b29c8541aa496b1c93d8c0b95d3f22719ab69416b1a05d985d0cc47122a9274a0ca0b5a9a05dac7282d1f2b624e518281b98e5a68615a6e7e5266cb4d40b930e3f2ad1cdc8611c4edc9416ad963d1ea8175b190473c91d505c7e5281b54e5a2c90361cb56da5f302569aa092f8a78503692c8e712e933502eb4d588cd594869f8b6205d90059c93d4a0b8883b92069db6b1981d81334bd68e8f53e168e1698bae8f5697cda181d20f17c56228e38be3185 (by decide +kernel)

private theorem part374 : Excludes 0x80004200000000000000000000000000000 0x79bcbd18380c08421000000000000000000 :=
  splitAt 1 96 0x79bcbd18380c08421000000000000000000 part376 part375 (by decide +kernel)

private theorem part372 : Excludes 0x80004200000000000000000000000000000 0x79bcbd18300c08421000000000000000000 :=
  splitAt 1 103 0x79bcbd18300c08421000000000000000000 part374 part373 (by decide +kernel)

private theorem part370 : Excludes 0x80004200000000000000000000000000000 0x79bcb518300c08421000000000000000000 :=
  splitAt 1 119 0x79bcb518300c08421000000000000000000 part372 part371 (by decide +kernel)

private theorem part368 : Excludes 0x80004200000000000000000000000000000 0x79bcb510300c08421000000000000000000 :=
  splitAt 1 111 0x79bcb510300c08421000000000000000000 part370 part369 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part379 : Excludes 0xa0000201000000000000000000000000000 0x5d3fd53288ad000b5008040200000000000 :=
  finishCode 133 0x2088520c6f01e2ae3406e3903d7403a05d69b053541292b731a8cc5bb20e6731644e125706fd69ab4b524cd376ad8f5cdcf41dd3f2b4d5a5cb4d401643814c40ca3f65048b7589e375963ed5b16eb0de6b28b7569b3164332a09621ecf307d69a7dd16ea206e2a8d5b13ecf6b0c1ad3683cb4de5a68eae83eb9853e6a3560fb40e62584cd85166e713ca8c457aa4516eca1d05bb13e62cad34302b01b9e5a6b165a570e7d4421b36a1cc79194170b4c6728a90d69aa2115c86fcdc510ca337b7ca4569bab8c028760dfa0e500f2875ab73dbd646a451ee8af5986007ba2b196a2a4962ace415838ac56a22b19746214c5003768f99ab6941736c0b36ad9f0189923ac55487c29f592c1bf5228ae6611a475bc7715c601a470b7437682741ca382d594623d7403b98aa3908fda0f2b4d266a8c546609985a21bf6e169a90b8b2ee4b1d2891683c80952164a1094cb07168ad2569ab4220a02d35882e2cb0759d86a45a2e4206569341e5ca215b5a88b5683ace6d356b8ed86eb4959dad82dd85ab06b9a7a7ab599a82c7baa339aca2d55516c5217416ab4ae4eda875466b250dfa8ce83cac9574493cb2505b86fcd2323c5466b25518c1e5986e0f01eeac966a888e6838ad3548b0790aac8f148a9b9e50ead3548493cd5f83c8f7524f41e5585a05a2b3385723dd5a8c2d5599c1b365059f356d00e50d16eac08e0b3da6f41c4d729e1353a41d04eb33981b0791e2ad3e7b8a05d442a2f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part381 : Excludes 0x80400201000000000000000000000000000 0x7bbdfd0a90cc26031088040200000000000 :=
  finishCode 101 0x300d42d8ca0a9e495b4bd25e8292819436184715c495b386e354e3f2a4747ae8177aacd5341aa0ed184e1613394506ad5f93cb075736b96581b055d3cac55736b9ad1e72c25ca2c2388b02095ac702a523b0796b1cb1b4f2a47560479c829505cd5b731b0346c32c259c58035b34dd66a819167a783c59aa63d740bb56e69bacd538460ff31aed696e6d1e2b9ae5a5c1e64f2b57dcb2e23281ad96362d1171a710c2b87f50a1caf324bc1e520683b7afacc55e72c0e579cda1ad3c1edf34ddcaeb4772bcce356e517b4be0fb1eed6a66ab620b57d3cae593b1a6f2d1dac6d5b904e8297119865184171a09641da8c671da3e5ab692f584b089c2c7e41db56e83cb0f5cd741ed00ab096adc92f171ad81479aca91d6adcb4769bb70b8328ae0b5c5c6ba2c3648bac9d662af99ee6afb9672917471404e12569e2d3c59f2c7e0f2b47878ad5b71eac7d68f23ae0f32c256a66bb6208b3e0f33035ede82547218522ca1f47eb9650769194f169f1ebd1b29f37358b3dcb3352e731a095904f1256b0d859ed5b96a6b1f835c5d7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part383 : Excludes 0x84000201000000000000000000000000000 0x7bf5fd02c1ac20431808040200000000000 :=
  finishCode 51 0x388fa328b618ad80410a1a8c17edca31f74fce4c3731ad4d886c5b49ccc13261ae8e4243e49996ae0abb98564e917a0f2e4760eb57d63af6f24ba08c4396a672162d97ecc07b7cb3960eb98d5c583c4973f3ac7ce423d759cc721736cb3124bb16cbf6ba1845583c0e42b4f94423cd3eeb56d5e6d3742166334e4fba93359acb3168128b04cdcaf185593b56d662fe358d40f34be0f6e5783dcd2f430cc250c1be6b1a40c79b3dbdaa2662c8e4fcb58da5f39460f69f96519c2868aae49d8efc7ae2c938bc7178592ba249e5a3b594e42d5b399be8e478e2e2c96a5b164bf2d5162cc2e1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part385 : Excludes 0x82000201000000000000000000000000000 0x7d7ff502928c10831408040200000000000 :=
  finishCode 69 0x1c4831dc701a8510c26629592c7094f1ac71f1569a8390bccf5f8c29ef560e3e566164640c0ec42b02e32e0e5eb4d9076b1b720a01523b0719eda1bf497a0ed43f2c14fd21b3497c616266a874e5eb518266137171b20b33907272f518c3d75a6abc5666607998691581f2c2e35939cbd00a81559104266ce4150f86fc526c432fda06d28721883848b8e497a876171c293149c7e78c28b8d5e32cccdcf17ee661443c0b8384b0d669886756a683b376b4c65a9a0ec37e5ed907671756057339b435ab4d1f28b5502a0b7a30af7116aa4bd5050eca45695cb53373ae8cc209660ea5047ca72f3999fae62d85e454e2d1382b30c42014e2f2d3506af715a6c83540cc5d55058b459816ac12959397e525e3e53979ccd48382a4f65a9a3c6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part386 : Excludes 0x80000201000000000000000000000000000 0x7f75d502808c00031008040200000000000 :=
  finishCode 157 0x1063f8ac03d5946a0bc3356c7ae839286b38ee2e8839720e0b1cbd6370a35ab61bf266c8f1402b30b05966281561ec1bf6299c14e2f2e8e01cbda86805c29e59442839736cd5b733a83569f20e5243fab986731b92c936a49510ce47170d079671a0641c01d7cd2f8c286fcfb25c314fac145c2839471dc266cd637b0b944dda3d73f3b30a235261d79c5dea324e48df1857289fee6a28aacb86b22cd683c86fda8b2c9e7b8bd7da5e3af1eb8b86384c7177d1b8621e471080aee2e82e3561ab73d8c286e6362ab4dce66a82d1da5f2c7564ea316b1cb359ab683b40dc7097b7ca1d392b56ce12d5b9ec6a1d1718ff5c06a190698cb4d6b29cbcc22d658c26942d36392b56ce12a1d5a6cd37731b52d66b398c37ea1d641e4561943909ccd63730d566250d6219f7650e9fad636b236ad9c966ad98adab71844c56709837ed5b561683979c5e6ad82647eae21c5e41db16500a903899aa2218d21c5d61b0efda5681b0cfcd5b164c4cd392b56d637281dec2929164bc8cc288ba350721399b88405524c93d722ac8d41702ddab69e3852a91941da5058883bcaf941db54523a405164c83b58e9c5dab69e3202cba1d0b21c14dc128ce615239fac5a2d5b497a8859791e29df414b96437ea493f586fe83db0f5282943dc683ea8246cac3d003cd2f6b1bd8d052e23501bf9edea45524a0a669782ad3be1bf3fda4bd282d0282e414b56e4f0bab278d23a7f75a6b4107b9052c258462b07497b56d647f1886e1a83e07fa2d1923293d5320f3359543ad5b4038b4416f201d8b69414a1282a1d85a2a45586d181168b56d63f20e5032a4949e9b8d5b943e862b8a0d9cd6b0d1c18ead6963c7470c90f58fb00a0d9032839479cb23475ab83fd50fc0a315ecaf7925307541ca3cdcd63fd (by decide +kernel)

private theorem part384 : Excludes 0x80000201000000000000000000000000000 0x7d75d502808c00031008040200000000000 :=
  splitAt 1 133 0x7d75d502808c00031008040200000000000 part386 part385 (by decide +kernel)

private theorem part382 : Excludes 0x80000201000000000000000000000000000 0x7975d502808c00031008040200000000000 :=
  splitAt 1 134 0x7975d502808c00031008040200000000000 part384 part383 (by decide +kernel)

private theorem part380 : Excludes 0x80000201000000000000000000000000000 0x7935d502808c00031008040200000000000 :=
  splitAt 1 130 0x7935d502808c00031008040200000000000 part382 part381 (by decide +kernel)

private theorem part378 : Excludes 0x80000201000000000000000000000000000 0x5935d502808c00031008040200000000000 :=
  splitAt 1 137 0x5935d502808c00031008040200000000000 part380 part379 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part388 : Excludes 0x80000280000000000000000000000000000 0x593cdd61000cc0001540000000000000000 :=
  finishCode 145 0x10a4110c3e0fa4188fd921e0f10f683d5b86a1401fe87b4157354c5a292f4a09c164b1b459f9b8b4d8fcec576ada4bd804a0c3ab4878eae4a0ac0d1fab4d98aef233091d8e4283b500ff71c15ab6b4d2e28b4569b235cff67056ada5060d0b58f233070558fcd5d495a4f4e66f5781521bb49586a648782ecbe293d351805aaac0b2989be7dd41caca626fcb29613d07d7abb58d8a20b5831a81f6cd5f39797c43da5175312c589c92159fb30a21c261ec9ccd87b20a4a22d5f8a22e6b414891e0abb9adcc29271eca0a63998fd598891a41fea70f225166adbd44e6681541aa489333f11483ac8fd83c820c2f69f381230755a2b91500e5e396aab4d5a2d07947eb966415a3f4a2e8079ab707947597c569aca30083983329452f8945d9c7916932d4569a5256214c14dcb551ee93ccfef201d60692b5a6a01e5aaad356070b74be33105e38a0e92b5a69495ac290c4892178ce0ad5b8ff6d3f9ab61bb893ab4d6adad36581a7bde4650a0f18aca2ef82e81e16afca1b524b09ca369e9984e5f141cc6058732514e42933839a1e12f8b50e0145d9c58039a51b481c8398c0c9f9586a4ce0ecb56e2f8946d74670dc28886ee6ada06d23a9c06ee493ad35eba83b6a4c82b5a6a42e41db56d036921651645a6c6166ad9fad66aa0351f8b5d2825f19052a4d61ecd5b8c2b55cff293d701a86003dac279886c35526829528a3d92f8a0e564356cc350c7a01d69ab4562dbdc6302b78b4d4e121ea017c562720e4e4b2cee399a06d60f0f650365f14a0be2d41c25641f2b5266158b8d5e323f669164583d1850dda3f504b07b40acaf147e9b2e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part391 : Excludes 0x84000200020000000000000000000000000 0x7bb4d593450c6200110c300010001000000 :=
  finishCode 61 0x1a07c1b8621c86703b21e1500a369c41ee1e2ad3cf5f0b3e3022cf9a92ac288299983eb4f6ad8f15cb29c1aee2dcb07dee6b4f47ecf73837cb4f4f4a3f4942f241051b4c10322e141cc9f9308aca60dcbd55072d3da0f67bb1eca0e459ec59903260585c30790f0ae904388e4146dcd7286d84e7211cbcb4f83cb146374b56ce66d5b98a251b722c9e93088b247b3181621e4390c3c528dac0a6201d072e3d96a6b45279c1e65a38f3587f0735ab63cd698a01dfc601e43c10727218c1cf756b2b14522aa49928a8176adcf5548aa05d072195a0f23d74039c84e431a85cc62bd6a5b88f2141e28dac0f82cd65a7b164c224f3857ac27987e9456ada456389b525ac6733 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part393 : Excludes 0x80002200020000000000000000000000000 0x5f76ddab0d0c0331101c100110001000000 :=
  finishCode 55 0xf8390d4370940ff43daa07928a0f5523a8c580506ca49365d079601a0701a41ecb1464a2b56d84ea47628cd223e652483d5ab6a476adce5962b97c4f046fc5f15a5b56d87e0f59ab6c274a01ea5d591cea45155ce6b475a5052c3c1fc7014620f54a0cd6583ccd5b59ab409c28c587f0f64be29df899ef6f6adb98d8c69bcc396b2b0fd5ef0dc5a92b35903307951883d41eb287523320641ead03808e2488394038f5e5a293cc57a7d5968a3fd698cf6d499a0e5c8600be32514557460c92e7d56ad8f5c7fa6dfa0f24f36a124f0f752723fd054c9453eaa465cb24f3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part395 : Excludes 0x80800200020000000000000000000000000 0x5f75f5c30d0c0700180c140010001000000 :=
  finishCode 19 0x380d44481ed6b14932916302d5b4a29c84e66b041e67bab52543707d5108b8569f1ec53e6f75519a9155c1ecca45493a0662f88b857441dc93959fa4cce4273368181320ed02e8196adc83b3fbb70721579c927202a015a93249dab6733 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part397 : Excludes 0x80020200020000000000000000000000000 0x5ff5f5af051c1212100c101010001000000 :=
  finishCode 31 0xd4380c407b45c31f64a3707985c2c4338ac146c92f34bd8aad634128fd544258c3bf61cb4bce2ed2ba0f2c3938bcac390c098e2eb45412c1e4e5e6eda0f2f65940e8f3731ad3ce4b0795d188392c511392c7e7397b40781f24e2f41c448307b604b9858ae81b969f0797f0fcf1fdd67e86356e1df9c5cb033165ac6d5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part398 : Excludes 0x80000200020000000000000000000000000 0x5fb6f583050c0200100c100010001000000 :=
  finishCode 153 0x1fc7c1c4078b38ba2d851128da389c24f505725147af247641289ee4efa02dab6b1b415b70d42c0e42302cf0eca8ce4859fd504a92b958167a0e683ca7e5ab682b2c13d281b41392ee132c1e66ad92eda9341ed61a92b0ecab09079cda93d61eb14d02f41a56435cc2956a4b9147b2b0d495b00e6190728197aacf717228b3dac4708c89120ec224883b923a81b601c87369a9e735876587f355cdce6d998826e795e6e59728b9b669b8765cdb07647b292b89138499cb1b5a7b9ad00a82572146324bdcd69e5892ed576afc7b169b8f643b2c02483d90ec9fae62ab9b61ae89360f214d4f2a48a33963e81b4e20fb30360f2b1f519d07d83cb915b85403b2d3798729e99052d6348ea4ae891c8821a971bed00e8252029c85c4670a23146c263350c95ed57402b96504aa8280c3959ec92b604cb536a8a49d64e92b9ab68176714931f9d04b079288a016412b40ce388ae146d1c50dc6d93fba09d4c41cc933510b57d26720e60f317c5acab3f839ac393fba09dc848ac6bf694873567f41e5aa29279aa251b2f8c10ba278d41c8588202c51b6afca3151987b56060fc945288b56ce4ad239466d5b2f8b507178fba51b202aa08059872b4739997c58473155636d37392b509f99872a475189c5c3d24053718732d3cfd682b38bb56dc4608cc535189c5d0765f18e2edc380d41b01d95619c460a362958592815505c29547ecb4f735a0545930135ee2d63250acc5acb398459251b5418c30164b24e5ab6d3761cb15d38499c51149cb56e6a59445ab7314c7b2ba388d37967a511505cc256b1b0458aad5b6adcc3d8c0b38d49943e939288946d1fb388b479ab651b6adca45 (by decide +kernel)

private theorem part396 : Excludes 0x80000200020000000000000000000000000 0x5fb4f583050c0200100c100010001000000 :=
  splitAt 1 125 0x5fb4f583050c0200100c100010001000000 part398 part397 (by decide +kernel)

private theorem part394 : Excludes 0x80000200020000000000000000000000000 0x5f34f583050c0200100c100010001000000 :=
  splitAt 1 131 0x5f34f583050c0200100c100010001000000 part396 part395 (by decide +kernel)

private theorem part392 : Excludes 0x80000200020000000000000000000000000 0x5f34d583050c0200100c100010001000000 :=
  splitAt 1 121 0x5f34d583050c0200100c100010001000000 part394 part393 (by decide +kernel)

private theorem part390 : Excludes 0x80000200020000000000000000000000000 0x5b34d583050c0200100c100010001000000 :=
  splitAt 1 134 0x5b34d583050c0200100c100010001000000 part392 part391 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part401 : Excludes 0x82000200000008000000000000000000000 0x5d7ed5a5170c14005000200060c10001000 :=
  finishCode 79 0x7c1a8721a40f6b68f21b9e171a4f47ca72f38bb102d18be20bf401caf0624be22ab5aa9684e12a54665f18faab291bdc083736b8f672cb58e83cb9060f6805171a91543b0799eea12d11fc60cfaa3a14759af4be272f373bb8d62e1120b751c315b8ee135b0acbf66e7621cb034128f6616ab5948cb30756aac2b05fa094c56d24489c30083541d8b568c1b04d0322d5a306c13597aca683c8b5569a82b501805405ab06e47b22a1969a2d516acb2f5a6c2d546cce575a69fe584412d07b061a0ecddb41ed00a3d96114c589cb2972168397cb4d2f8c48da20072f36fca1d7b6c2e31d58b8e487ac0e4878b75e416e933e69cbdb542283b11acafb8c1933cfaa3ab497ac880587b28d91688b8cf632c1d21ed634872f6110462105659b927aa113fcad356522e3597d0719422b4d40ca0ec5c71bb669f8b8dc85a6b1107d902a4db37d87356ab0b0cdf682b9076d3f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part402 : Excludes 0x80000200000008000000000000000000000 0x5b34d5a1060c14001000200040c00001000 :=
  finishCode 117 0x1063c8de350ce3f8521292b580f17205872d3419272f6b2cd5d41dacbc507133dabb0796b2a7bd69ab03314cc0430517891c0698c72f4f2a0acbe21ed1faad35f4415ce4107a8b8d2871f7616e87b569a2d792861d9862247f2087201eab039c7a72f202b5883b36ccd5d733978d04b236565ea220954671b9cb8a2e341da8ce1508b8d5e720ec5c6825526c5c5373ac0c5bab1f967273348b8b5e24771fc7201eab558e125113978b8e288b68ba28766a5ad34a227096ad9ccdab730f5aa62e3402ad3569b1444a2303c67c2184e01ea1ed384c5f16ada054e672d360ea607599941e0f09cbe202941e2486143f17c5a963d907ab90a60785c7b02fd65ed5b16bb009c06d63eeac7cbe2d200fe01aa43d3f20bf2cfc0b1475a7e63030515ab6b0d3eeb0ae5aab56c5ae62b6e07b2e428ce5049ed448ec1f47eb56c3da7b19ab6d6516ea42e279ad55a86e13c0f6ad072f71ecaf35a7b56cbe290f4828ff5804014868f99606e6d3ea8aacfab39458b690589bf0fd5ac791301709ccd69b0f64b920bba0fa809597b00a623ae6ad82ed46a3d9517b56e497b4dcbe2c4d47ecb554839a55806905c28195a6ca0b122c015692ad34d6ab2f9744f184772244b0e666e2d5521f291d1f2d5b487cb034a08f66581c90f6adacfc9bf06a548eb4d6adb52e8c1ad34dbe7336ada41e523b56d67e4df1eccd5b (by decide +kernel)

private theorem part400 : Excludes 0x80000200000008000000000000000000000 0x5934d5a1060c14001000200040c00001000 :=
  splitAt 1 133 0x5934d5a1060c14001000200040c00001000 part402 part401 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part404 : Excludes 0x84000200000000100000000000000000000 0x7bb6f585c30ca8281200000080804308000 :=
  finishCode 9 0xde388ce145ce0b18aca4ac4f922e1e1399c1e1281bb872583c262b2f6c1e1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part406 : Excludes 0x80400200000000100000000000000000000 0x5fb6f58d32cc0a281002000080840300800 :=
  finishCode 43 0x388ce298511292c481bf69bcd4958da87e613b0e53be4cd8166d53588b50c038051761fc81b481873569a11b9a568c761cb09c55e9215b11c4e05bb291d462a2b526ae86e23f523b0b8d67a38f5a9ca31149c2e3523a8c6245a6a91e48b8a4e523ca315a6c488220ae58db52e62ab08d43ae6b48e8b8dc816eca3148ecd44489030e6ad34a06b3d9ac68279416c3b61e9c86e280d69ab47923aa6133662cb5954621b76b2cc3d5a3cd4b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part407 : Excludes 0x80000200000000100000000000000000000 0x5d76f585020c08281000000080800300000 :=
  finishCode 155 0xf83f90a3800f18903dacc20ee3909bde382bb8cc2cfce4605cb0347ea4cd8ab09fe581a914d76a817366b2b15d48a3958d7eb4d6a8a455ab6c5366080b2054e426f78e0ae03907207b5682e1505a6b31123687098e4a805943a9452f8ad564a2a91d1faa1d948eafd91c6720c4138b8e1cfac9d86e60741dc7fb589acfe2437dc2e3399b07e515a702e39076a1d392a4ccbe3122c6e40d800e522a988e3785b3837e82757eca1d3fd981dc8328cd67e1bf392a4ce392a09d58891b4512caf15999c24e66c22c4e412acfe0f317c543aa62516838a87c5bab3f518c94557ec5f1587accd105a1dc5a6c48d630d6415a0d45c6a25906ac4d3028b5616eb16e2f6a0eda8413c5e162d8b5544b247500f12028e3158b8c5ab352d00e2dd721a46612c402cc217278b8d43e81b4999e0ac249ce12a25a0f6e6d604a0d5c772c3d43aa251f2cb0f515a054e4b063106e79456a1d171a91d4726e78def1c14d971b9da45319c4b037e2af98ae7af1ebbd76604c1ed036f75593c6b9405b0253df07b41a8abdc7702ad06a6e79a82f8c83b290a06c3da4056d19057cc81b6978b8cbe2725390ac0e21c265a6a77d03650758ecf51691a91dab67095a6a0ee4efb0e58041dc8df402a49dab65f1523cd5b891c86b214390b10b4d8a224055b1ab71c24a066b98e12b4d390e125e3922a9ef1ebb08569ab05944ac438f64158734df64052e128b2794a2e5215a6b0082b90766fb2819bee4f7b48b3f8a2e82b41dc282e38dda521171c6ed5b14c281b48e679ab6b2f5aab586bf900ee4b83ac1234f994945865c3947eb036adb10a80734a4b2cfd87e939292cb45290cb4d (by decide +kernel)

private theorem part405 : Excludes 0x80000200000000100000000000000000000 0x5d36f585020c08281000000080800300000 :=
  splitAt 1 130 0x5d36f585020c08281000000080800300000 part407 part406 (by decide +kernel)

private theorem part403 : Excludes 0x80000200000000000000000000000000000 0x5934d581020c08001000000000000000000 :=
  splitAt 5016 134 0x5936f585020c08281000000080800300000 part405 part404 (by decide +kernel)

private theorem part399 : Excludes 0x80000200000000000000000000000000000 0x5934d581020c00001000000000000000000 :=
  splitAt 1 87 0x5934d581020c00001000000000000000000 part403 part400 (by decide +kernel)

private theorem part389 : Excludes 0x80000200000000000000000000000000000 0x5934d581000c00001000000000000000000 :=
  splitAt 1 101 0x5934d581000c00001000000000000000000 part399 part390 (by decide +kernel)

private theorem part387 : Excludes 0x80000200000000000000000000000000000 0x5934d501000c00001000000000000000000 :=
  splitAt 1 115 0x5934d501000c00001000000000000000000 part389 part388 (by decide +kernel)

private theorem part377 : Excludes 0x80000200000000000000000000000000000 0x5934d500000c00001000000000000000000 :=
  splitAt 1 108 0x5934d500000c00001000000000000000000 part387 part378 (by decide +kernel)

private theorem part367 : Excludes 0x80000200000000000000000000000000000 0x59349500000c00001000000000000000000 :=
  splitAt 1 122 0x59349500000c00001000000000000000000 part377 part368 (by decide +kernel)

private theorem part351 : Excludes 0x80000200000000000000000000000000000 0x49349500000c00001000000000000000000 :=
  splitAt 1 136 0x49349500000c00001000000000000000000 part367 part352 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part409 : Excludes 0x80000041000000000000000000000000000 0x49ad92aa840030030008208200000000000 :=
  finishCode 115 0x2247a1c0790a46fa4010420e66a5815c2c60e9303a364c260ef8803d6b4d8a1ab398e06b4d497cf69402981d1b26130f5b18a43508c38faad5b402bd94e327354710732cc4dfaf69736a016404ad35ed29c276e5a6acd54433da545ed5b5a6cd003d4e041b97165a6a7e569b1b7d5f6a435a6cd3d1ebc30f2428fa3b8ca03d43d650d85c68f39ac6b31385b556381ad2d0160f56a1702e2cc551629cb4e6ac22b0923156286a8bd486ec3da6733a885cc650d0b3ce671a98f5deca7192e05571bb5ee2e67691673073ce325f75a7cf69482a81ded3308a22e880b6adc7e70e7c6167b4970c2af3154b86f699dc670e6b077d04b41ed25e4cf2fd83a4e073500f5479c3d739a85de1ebc101eb494c0eb2f7a50e517be8ee1c0e0ef978cc261eb6e1a5b0fece0683b044cd5b2fbb18be3083d7413c1e67b4a81d4861cf7b4cf658e32735170c827791a448ecb4d4a083a43be1e7851d0078a4f62869c2e7b4ac35672735856670b074ab8e03402dd900e8274b1ed30add69a7191eba7071196469196adad2ded32987c79edad5f4958f5d8c6017437e9f8e39aad2cbeed4796120235a5b51e0e39ad67b2b58525692318727928273516eb594b9324745ba93d6b0cb4d696b994e4e2dd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part412 : Excludes 0xa0000040008000000000000000000000000 0x5dbc9ea31144b500000ad01000200040000 :=
  finishCode 71 0x1e86515c790e630a3e8ce03c5ee3356d44a5c31e99495eeb1f8dab63d316eb56e61194445c2e419eda2c941383a57c7018053104e6ad8d762dd594b502bd8e170798dfa80785bad5b85baa6240a21945eb295aa863e6b0cf2428e828ae16e9445104e1f05a5cb4d6ae93f41e2d478d727f952693f47a7285d69a0f185ab1c2c1d2c02206ef8e16a041d65a58b145ba1b935ac2bd16ecf83e8e83c88398a360f170120581c91d385acfd0126a1726385a505a5aa1b58fcd5535da09dccb0e9560691d38586e627e83c60f3399456e70b59fa0245c24f39bc6521460169b285d49a82728ba4ae508a50549a1e767167f1725ed22d5627a09c31f293528280983cef6987b2941 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part414 : Excludes 0x80004040008000000000000000000000000 0x6dfcbea1714039090818c01020200040000 :=
  finishCode 43 0x428de3e8ce358ca07adc04feb0882746054b399522e93b331ac728ac373391da5f07715fb57647dbdb499ec135159496515a0de385946dd0732c8397b4946ca4ac20506515acf4ff682793fb07adeeb2025a5aa11170a09df05e1ac610c22da2c866adb97d04af691fdad366adb04d2629430dccb4d47dc3d95a99816205a3a3ce6279c2da76c41143cd5d1b1bda490a5cb5a3cfa358f828e68c29fad67a827598987cc568278bc6a394a0a09e51ca09e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part416 : Excludes 0x80000050008000000000000000000000000 0x6baedbad01403700000ae01100280040000 :=
  finishCode 51 0xf23e104430d603bd9c0f5ae8a4258a01c2d987bac1770daad3da4b0b2d7862dc83b011ca2f2c3a98a2f9486bc2808058e62e41a30af6d621bdd60f33dacf8ea2f9eeac5b836af696b186d66adace57465108246cf69272ad3d41a7e3385a925a8f2d3c4d23636b19c2d45e4030a0cc535069fee83cb13569eb09385bda620075a4ee15293e4e622d7969e1eb88200171c5110f5c24b9ac683b385a0153fa1eb67081714444c3285c3d70c3da64efb56c5c64f307aae0d4292616ba4ec2af0b5cbf7355520ab55 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part417 : Excludes 0x80000040008000000000000000000000000 0x69acdab1014031000008c01000200040000 :=
  finishCode 149 0x6b198880a46ae3e8731741f0792087b4cd255a6ac9cc0e0e980164707aca2e1eb925f2c6deda93d30f8b8e30714960ee8294efa4bc70f41e405234f7babda5aba4f307aa788379072a079cc63d9292bdb5f47c20853138303987d1b311ac99e2cb25b8b2e118ad3614497d18359c83d4c57133e0028bc7f946cad34a4a1eb9646e8356e5a6a7f45c62b39eda7f927ec28b4d837270b1629494e173e10c400a1183d62e3077b782bf900ab390f5bda6136b50c99ef6d5a68b5e0f586e569b07adbc882147d1d80f5c10a603ace63358cb7e61f6b1cd3b315a7f66b1cd6127297bc1eae82e8d0144506f2024dfb14966a49cc57827ebd963fd8b85ab68277ba9cc5eeb20e504eb1b7d14c41bcc296aaa0658b20e92f7b50bc35662679cc4c56ec3680e96b1cb3d26dc01969d9ab683eb58ce16afb69d933e39883a5104139fee581b584962b4d40c9c2d403fdc81915bcd490f5c24f84aaca2f0a0400731851807c1d8470c2a149893f41d65253d01ea6bb9ccab03506b08ce16a1b90122c389fa5255a5c4fd292bb09c20d651cb56616183a56071bb503270b85141b2c0d86a6bb2019ec669fbd5c4e270b267b0d5f0850ff72c64d7660507a8b845ab1c2d69b12ddbc60200761f0292a4c641c93f50320f5205c4fd503c8194908064e569dce455a6ad3ded6d3b93e713f47d69f389fab4d07abe10c410da3e8dc03d5783d104a9f9969ee6514acc251e0ad3d8069dc2955a7acf5eaec0da0fab09722cb4f760d772064a36819827b300afb859e4fd3fc946d072b4b8a3681981d66bb86ff1816aea8bc9464fd (by decide +kernel)

private theorem part415 : Excludes 0x80000040008000000000000000000000000 0x69acdaa1014031000008c01000200040000 :=
  splitAt 1 112 0x69acdaa1014031000008c01000200040000 part417 part416 (by decide +kernel)

private theorem part413 : Excludes 0x80000040008000000000000000000000000 0x69ac9aa1014031000008c01000200040000 :=
  splitAt 1 122 0x69ac9aa1014031000008c01000200040000 part415 part414 (by decide +kernel)

private theorem part411 : Excludes 0x80000040008000000000000000000000000 0x49ac9aa1014031000008c01000200040000 :=
  splitAt 1 137 0x49ac9aa1014031000008c01000200040000 part413 part412 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part420 : Excludes 0xa0000040000040000000000000000000000 0x5dbc9ba30488b60000480000bc000008000 :=
  finishCode 59 0x1bc791d8851a86019c28bae83d794922e128d9cd6170be0f4239e8c0b03da7a6f5078a40d5b8bee3d92fbcd514a0b02e461b92da525f76a8b587039a52a4d16e879ded31cc4a4ac2562a83c5f416ec1e7398c5117d03bf1fdc1d2d41c6641ca09ce6a6fd839eae328ce1cc5cdb079c7ae8270d1c0f1078cd3b4139cd6078b28ba2b84f3858a7310e3b70d434866b09c45aca0c339a8b766b2b5964978b76594b09d65e735398ae09c2cd683c9aed43672d691cd5b8bee8393fbb38c03d0735074c7196b29cc456f3da5e42dbc2d56b083a53e713cded27116aacf7172bb0a52820f1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part422 : Excludes 0x80004040000040000000000000000000000 0x69eeb6a17480b8080848480038000808000 :=
  finishCode 53 0x10a3b8de3591007add05f0a2ec0f9852d6141b946e7ba9844bef0f3e6ad97dce6a93b5d114600bef0034a64f4c1e5ed2d3f61c9c9ca2e801c9da7f3da4e06c279a768d9581cc35133c1e5ed2ca4010799ed25177b5ce6d83ca015ed23fb37acf6983ca39e57e8b85ed27033fc945d787c220393cf69308b38c43925273572bc7b11fdb16e205a3ad4ca0f3da5a7e9411fdcd51725b99d037102d4da4b13f4c3e2bf9016e4b2dfa50dbc651cdb30760e2c2740297dc7f6a4d5d1ac80127a83b9ab65f76a89b46381b554b865f748cb56e0f341ed8725f741dd07b6ad81e67b4b56d6a6ee1c660ef9f1ce4f136ce6aa4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part424 : Excludes 0x80000050000040000000000000000000000 0x6dacd3ad0680b300014aa0003880000a000 :=
  finishCode 55 0x88178501a8398be0ce3009640072d38c8fae292a4ecda32925ab6b139ab61df26dbc85259a4271141283d68005c708fc6ced291f5a45ca2e0f5381cd2077e0f59b6628bbc90a07ae49eb56c8161df8dfb24f41eb0a3c8d43e0ce3b0d6206ca42735838683b6ada0ee205bdb609592458aa8d93969394e327b39252d5b46c83d4a2e5179ab63eb57ec1cf1f5b56c9e7357cdfa93b07abe0961b16594b95d06ac2738c8a4e7b6a06d06a6d98b6ef6d0efbe0c03504e5927672d39aab8a258a22b276138b8e49e8ae617183d523b308c5962e3077c1eb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part425 : Excludes 0x80000040000040000000000000000000000 0x69acd2b10480b0000048000038000008000 :=
  finishCode 109 0xd63285235e200398be8ee410f842850781ea6fd9a962d730eba10a250669b8b8ca0e2e39423352d0124fd16bc72789e67359486a2116287ae30e8f0458ae83e90a400ee145e07a8b8c1eb0ae4a2e4f315cc1eb25bc2b91659cb6162c284e981ea4fd4703bf178cc0e2b3381ebb41e44c67d91bacd258c1a0a44baf23a1004105077b4c805497a4f41ea1eb927ade238fa356e59aa4f43d6d43d96736ad2ce5a4b79cdab4f0f5cd5b402a7c672ea4f49fb355e6ad83d49e6bc328ae3387316d1d8415c2e1167a9070b87d673583ccd5158cb14c1d31cb41ea9059aca81b07ac29003e90c3380f5498c4fd292b15658f945d4932c2639a945d6131cd5606a0d2018b5638cbe9043700f5611d838cc26d5a7a095076b80076612b4ece5a7198936b09524b3880550dca496aecc0f838ad3cbef2d2d9c83c88ce412abed0562cf28db0907b87b281b4eec8d9570e5ab4f8e33079524bda4e3341e45c2f657d2006701eaec41e649893f4a36c0f91b3308b0991b26bb62997dc806a4993ca4e53689cb6 (by decide +kernel)

private theorem part423 : Excludes 0x80000040000040000000000000000000000 0x69acd2a10480b0000048000038000008000 :=
  splitAt 1 112 0x69acd2a10480b0000048000038000008000 part425 part424 (by decide +kernel)

private theorem part421 : Excludes 0x80000040000040000000000000000000000 0x69ac92a10480b0000048000038000008000 :=
  splitAt 1 122 0x69ac92a10480b0000048000038000008000 part423 part422 (by decide +kernel)

private theorem part419 : Excludes 0x80000040000040000000000000000000000 0x49ac92a10480b0000048000038000008000 :=
  splitAt 1 137 0x49ac92a10480b0000048000038000008000 part421 part420 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part428 : Excludes 0x90000040000000001000000000000000000 0x6baeb2a1d08372082828000000040200132 :=
  finishCode 39 0x184701986d0a46e679ab6b0551f93547c61eb1fdc30721cd51b3206d69a1b9899e9432fbc943690b970acc7c63fb0f5b7073592860ab9ab6a3f6703d6c03b0735075c5f726a86d62fba4a62e5a0ecf760ef928707b2fbb56d0368d97c1dc86200515c5cb0f58b8c1dede3dd6731ace43d6727a0fa7036a1b9b47af13541d70c3711858faab1f402ad3ce5ad5b89aa4d59940f5b4ae6a8ad4da62b4d267cd65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part430 : Excludes 0x80004040000000001000000000000000000 0x59ecb6a1f0a278082808000002040600030 :=
  finishCode 59 0xde428ce3b8fa3101e77417028d8efe393b98ce5ae478e325f72fbc611a0f6d292fb9c64e6a5f78a4283b923272d49e8feca3712368bc07ac7f65f78dda90741d9ae61229c0dc9693d37697dd445e1ebb1c0cbeef7541db1666b0a7a42325f7731b4dcc26f7570194498c61f5a6a60d6188f6c41308a08d2d9cce12d8e069e9838a38c372c0f471ce6d381a88ca17dd69b285ce06a4d28bb91e6a8b98e725b4a4a2e941671ccf0a056221df5a69cd43867217107b91b2e5d6099c0d69b1228fe2fb9c0cfd67038bef12320ee187e31597de6b2a41d27ad5d9622b536aec3cb4a0b6912359660f984568e3fb671acb35745c25074a0cd655a692165a6a81d83e611 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part432 : Excludes 0x80000040000400001000000000000000000 0x5dacd3a1508a70806808007080040a00038 :=
  finishCode 49 0x8519c3518062145ea07800e324b7292c8d941bb4f646c8f5c52a6f5969a7196d09e671193e707125b97dc8161eb388ce474f9c00fa3c82e3904e4033d7948ca0e0f18904c71aed69a9fb4138b8c9e60f56212830f5dcc64f34f1ecf1ebce6a3d73d7c1cf8e3252139ab582c596a61cf0f5a02e2e1b98cbeea49821ac078a46658f87aca468d993ca4e558fa366891c0611702919c4639aac460e1be8735925661f4a08a0e2fbad34e6af81c464f783a4e6a5f78db2fa3700e90d9c7353d7c93d413c735 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part433 : Excludes 0x80000040000000001000000000000000000 0x59acd2a1408670002808000000040200030 :=
  finishCode 141 0x6515c700e630c220ec2d35e44e16c51cc4fd526b0762fb948c8c717dca4a82738c864e524b56c7ae2bd29197de413c48cc348523205c83b40d97ddf0524c943393bd964f7a09ce6b1c44bef3b85234a1cd5b075c1f60d3a81ca42a496adbe10c1f0e28b83c51b2735381bc86af83265f7290ac162fbb481d790365f7607c5250589b6624701ac860a46fa400883e0b4d396c4f33098ace27983a66a5ad363159cb61599b6569a507a187d2088520027ecd6507a9c0e579b51d606b4b35dad34806d23b082b907671995f7307569ad6539ab38b4d586c82b27e94955f72cd5acab4b8e3272d27eca497c2184e1e4381b010a1cb4a2f03d4fb70b8e0f707b8bae93107483d6396b39001cd587b1495276c5594860b128bc0f546cbb04e99252a4329297be524c004db91b283b36ca8aca4a0b19f47c208761e416ac73507483c530401acab03969a941061c93d85ba2dd8e4e7038b7eb4d6adcd6526a94943be7359f0802246b01ea0eb89e6d51291941e075a980f1350d6b24653e6a2f4b185341dc9e6d5b37a8f5cbeed3796131cd5b85c154670e231cb4e4610e06d641ee29186e669da06d00b350dcdb07b61169f1a4584a1b9291a0165a7b08e4596961b941da908056aec0254739c9d27a5f79ab6c2286e412948d27b2014a47356d27a5f78909e6b059ccaa07517948c3cf3555436d51 (by decide +kernel)

private theorem part431 : Excludes 0x80000040000000001000000000000000000 0x59acd2a1408270002808000000040200030 :=
  splitAt 1 94 0x59acd2a1408270002808000000040200030 part433 part432 (by decide +kernel)

private theorem part429 : Excludes 0x80000040000000001000000000000000000 0x59ac92a1408270002808000000040200030 :=
  splitAt 1 122 0x59ac92a1408270002808000000040200030 part431 part430 (by decide +kernel)

private theorem part427 : Excludes 0x80000040000000001000000000000000000 0x49ac92a1408270002808000000040200030 :=
  splitAt 1 136 0x49ac92a1408270002808000000040200030 part429 part428 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part435 : Excludes 0x90000040000000200000000000000000000 0x6baeb2b5808172505008001000044c80000 :=
  finishCode 31 0xf4330f8148ddc86200591c8056a4a7c4e6a1eb17183bdbc58fc7350f5b50e6d262cc3539ab91616586a55e712ec74a2d7075b390c13563d4ad3da92b4d3779cd49ab1fd658fb281eb61ace4b69bad3499f34adabee4b6b2b490c07ac8172d341d7250e16b9cd5bc8603d6c399a525cb6aead55276b4d39a8f467b5c6152763d7725ce6761ab4dce6ab4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part437 : Excludes 0x80004040000000200000000000000000000 0x59ecbfa5708078581808001410040c00020 :=
  finishCode 65 0x1bc8019c85188723d18383c9235ed2e49403879ca36525601cdb1ede0f2735290a0243d71f9d073077d94702245a6be0bc24c60f5a094c3ac099276d5d83c987c3d6a1196221eb69bcd610c8a4acff29c1a87036118261779ed307b588b15c7f6d3b7b4cc57836ae6d4f2c5177b4b00e03e0700f644972c451e6d290dc9fe4e073da43d68023e63fcbda6731a7943d69c3da6690c1ece06b13891af69412d0797b487adb46b1ed334ed69ac354a0877c3d6ca39b65a69c9c7f6c006e6463a795ed2b29393b145cc33da570671a773105c8ac09517a884e4e7356214c0dab0261e0b0e4c3ef69969b309daaaf699a52c5b4718f5ce32f8338b8288661ab984c223d939ac48e618c3e61169fcb4d524a4f4c230f6569a3fb927ab53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part439 : Excludes 0x80000040020000200000000000000000000 0x5bacf2a50580f050100e005002041c00010 :=
  finishCode 83 0x891ac61180291be8ee400ce03d4e6b315d1a23d7288a36683db49436ab390f5b381eb5a5c7357b6c703733c1ed6721b54a0cd4258735690e32ae2bf47af315da43399d67eb4b9ecad5d6b1c51b591a70d618a22d6361eac7d8af314ded304651b21eb83d94441eb0c3e0fa4005919ed23d928883d5b449100b24f5c8b24ac3d6b39900ae67800dfae459cc2511722c805591ab01eb27eb496267b59499f13ce075941e187c180672006949c64e4f043da65a583d50732d2ded23a59a7eb4b8015807aac7e2d0a365ee29e50dc9c0e58fbda5cc6c390dacb1f8010c07a8d3e723970e0f251b58f96564128b867b4b91563ece35467b4b9949faac2796722a095acb18193bb079731bb83d990720eb27ecf83e8e003c5240dacf691ec9c9da6ed51670e6b20e585324ad8127030c882a625db15c3cec39620e6a71998aa51b589ce6d517b51ded2d5d404b546 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part440 : Excludes 0x80000040000000200000000000000000000 0x59acd2a5028070501008001000040c00000 :=
  finishCode 123 0xbc4307317c19c601a87d0e32727694cb0320183d600400a42b3f9012b0d9c961cf5aacd3f6a4c01123a00f5790dfb2064a460e9291c6fd40cc52337e933d69ad6583beb4583aeb5537ebc90a4004fd8a4a0f16b1607316daaa1eb291ac0e83dc523260877c9633484b7ed6516e83d614891d8821ac07ab805e3989e62b59ccc5b2fd87ac36b2c0c8169c3588250da975e381948cd73303648386e4b2309b4bde70358f83d5cc73574e061b9078a980e92c8cb3f303b07685200671886b0fd24fd28386e62df948d84b460569ad650f3cd65205a025886b22416e92262f1b52daba5233d7cd5d6b2820669b8a85aca1b9838cd4b6b2948c3d72d348164cf8ff22e3291bb0ee148ca0eb55983ac4316b93ce494c5ef524a4eca46e0448c2400523761d0283c5115a9cf730e193f481671994c6d0572b3d9256403303c7af38cad36696900df0741e482200288c0f56d1f437ec92b0f5ae02b99cae735725c4a77b69c656a6b4b8572b4d508c6ef38cad34dfb0f0525eb4d604cc2709f8d3d6724f339a83d584f178cff24cf6ae93cd25ede3c8ce348829969ae4539a873c3ce81989fab4d7c05ba8d981e2d299a96c42d3418713cd03339160e21c747cc3d9078ad35806a1ed302fca4271939aa5892f81eac27593c5110e1c0f5 (by decide +kernel)

private theorem part438 : Excludes 0x80000040000000200000000000000000000 0x59acd2a5008070501008001000040c00000 :=
  splitAt 1 101 0x59acd2a5008070501008001000040c00000 part440 part439 (by decide +kernel)

private theorem part436 : Excludes 0x80000040000000200000000000000000000 0x59ac92a5008070501008001000040c00000 :=
  splitAt 1 122 0x59ac92a5008070501008001000040c00000 part438 part437 (by decide +kernel)

private theorem part434 : Excludes 0x80000040000000000000000000000000000 0x49ac92a1008070001008000000000000000 :=
  splitAt 5279 136 0x49ac92a5008070501008001000040c00000 part436 part435 (by decide +kernel)

private theorem part426 : Excludes 0x80000040000000000000000000000000000 0x49ac92a1008070000008000000000000000 :=
  splitAt 1 72 0x49ac92a1008070000008000000000000000 part434 part427 (by decide +kernel)

private theorem part418 : Excludes 0x80000040000000000000000000000000000 0x49ac92a1008030000008000000000000000 :=
  splitAt 1 90 0x49ac92a1008030000008000000000000000 part426 part419 (by decide +kernel)

private theorem part410 : Excludes 0x80000040000000000000000000000000000 0x49ac92a1000030000008000000000000000 :=
  splitAt 1 99 0x49ac92a1000030000008000000000000000 part418 part411 (by decide +kernel)

private theorem part408 : Excludes 0x80000000000000000000000000000000000 0x49249200000000000000000000000000000 :=
  splitAt 4490 108 0x49ac92a0000030000008000000000000000 part410 part409 (by decide +kernel)

private theorem part350 : Excludes 0x80000000000000000000000000000000000 0x49249000000000000000000000000000000 :=
  splitAt 1 117 0x49249000000000000000000000000000000 part408 part351 (by decide +kernel)

private theorem part316 : Excludes 0x80000000000000000000000000000000000 0x49248000000000000000000000000000000 :=
  splitAt 1 120 0x49248000000000000000000000000000000 part350 part317 (by decide +kernel)

private theorem part284 : Excludes 0x80000000000000000000000000000000000 0x48248000000000000000000000000000000 :=
  splitAt 1 132 0x48248000000000000000000000000000000 part316 part285 (by decide +kernel)

private theorem part220 : Excludes 0x80000000000000000000000000000000000 0x48048000000000000000000000000000000 :=
  splitAt 1 129 0x48048000000000000000000000000000000 part284 part221 (by decide +kernel)

private theorem part172 : Excludes 0x80000000000000000000000000000000000 0x40048000000000000000000000000000000 :=
  splitAt 1 135 0x40048000000000000000000000000000000 part220 part173 (by decide +kernel)

private theorem part58 : Excludes 0x80000000000000000000000000000000000 0x40008000000000000000000000000000000 :=
  splitAt 1 126 0x40008000000000000000000000000000000 part172 part59 (by decide +kernel)

private theorem part0 : Excludes 0x80000000000000000000000000000000000 0x40000000000000000000000000000000000 :=
  splitAt 1 123 0x40000000000000000000000000000000000 part58 part1 (by decide +kernel)


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem caseR (c : Nat → Bool) (hp : Pal 280 c) (ha : Avoid 280 17 c)
    (v0 : c 139 = true) : False :=
  part0 c hp ha (insertRed (by simp [Red] : Red c 0) v0) (by
      have mask : addedBlue 280 moves.unary 0 0 139 = 0x40000000000000000000000000000000000 := by decide +kernel
      rw [← mask]
      exact added_sound moves hp ha (by simp [Red] : Red c 0) (blue_zero c) v0)

end Case280
end PalindromicSeventeenEvenFirst

open PalindromicSeventeenEvenFirst

theorem OMA.solution : OMA.R_Green14_W_3_17_R2_H2_R1.H1 := by
  intro c hp ha a
  exact Case280.caseR c hp ha a
