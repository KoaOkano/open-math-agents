import OMAReductions.R_Green14_W_3_17_R2_H2_R1

/-! Case 2 of the length-280 upper bound for the palindromic (3,17)
problem, Table 6 of Ahmed, Kullmann and Snevily (arXiv:1102.5433).
The proof checks a finite branching certificate for the specified
colors near the axis of reflection. Lean formalization by @KoaOkano. -/
namespace PalindromicSeventeenEvenSecond
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
private theorem part4 : Excludes 0xd0000a0000000000000000000000000000 0xf2f7fa48555d86e80055000000000000000 :=
  finishCode 9 0x328e806de59f93e4a06c62e882d816e1bd9ab60bf052c1b50de8776 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part6 : Excludes 0x50000a0800000000000000000000000000 0xbafdee4c17d502f802d5445040000000000 :=
  finishCode 55 0xd82d0f0240a3d8ff21dd49fb50e02501dd3f6c817406c1de2f0a93d01b20ccd57280e0e6d3b05982d626197843826fb416bc0e82c01dd41bc7f937d8576501c1b42ca3736afac0be46062e9a0dd072a3993fa5d3404a38760dde403c1dc0f618b0c7af8d2b9abe8173920ef235cd9216d6959ade1ae86151ae8130b696816d93ff1812e99fcdeb70d55cd7181580d42fc960e7ba804cba718183ba04cdf7142d9181a0ee9ef51cc61e1d4bd6e3030ea49861718986813501ac8b4188a4f839c161419bd9c16a4c3513ac0c2d9a8e0b11a6c7ad839b93e0eed615810273585eb30738c39785072809351aab204da5700042661452dc9b1411e4c328197e640bb9bdaaa82d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part7 : Excludes 0x50000a0000000000000000000000000000 0xbaf5aa48955502a80055000000000000000 :=
  finishCode 121 0x1b47417c58174700e4a7336c10328376adcd3d0eeb4b669eb56d86ea2981629438071776106f356d4561c940cd07389f2a4d49fad0da471785032c59413b6090350817390a4fd1b72cfd686b459e03711c6adbd7640682fe30a7e740b940e7bab515686afd185281a93d4521dd9abec22287d705fb11672aa3256af0770cf89ee5abc1dd07b2d04faed5b9b0701e85d03ba8099a8ed6372e8304e268d789f26c5406b56d68060cd5b1699fe66adb1880d9aaa2d349f940e6afad0fa260833480bf2d63835af55697a025ab7351e389cd5b9012f0360c6338b42e893f40bc1b76ad8b4d6c1dacb57527b56d47eb57949ed5b6111c060a7fe6afb56d06ef579a7a1b75f16048104eb578dd307941c97e64ffac5d687236dab690236e364b56d0120039a5707b409974d27f380b41ff6413a0b60e61bd5f120413c1e66adb5160e66e941cac5e409b4f6836b56d012d5f90268099ab68176319c501cb572e99ba507a0c149fcb4162cad5e5815c5f194413a0dc2db2cbdc720b7281b99e62cb6080974076b356c3bad5b9ecf356d8b32025b05a1a88348b4d27f18591ae5a11dead5d4073506e2d8d5b364cb45281ac6683d877567f064c9f21dd58cc817156b56e (by decide +kernel)

private theorem part5 : Excludes 0x50000a0000000000000000000000000000 0xbaf5aa48155502a80055000000000000000 :=
  splitAt 1 107 0xbaf5aa48155502a80055000000000000000 part7 part6 (by decide +kernel)

private theorem part3 : Excludes 0x50000a0000000000000000000000000000 0xb2f5aa48155502a80055000000000000000 :=
  splitAt 1 135 0xb2f5aa48155502a80055000000000000000 part5 part4 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part9 : Excludes 0x5000020020000000000000000000000000 0xb273ab90844564280501281001001000000 :=
  finishCode 75 0xf00e90e356db472128640e13185949e1c1399b38a0201c04b351c7ce8371e6c3e78c2cd47261a3cc79ac827b61769ccd00f378a3d87be0e74139366073b001c99a423e7720a01d06ee41a3060214f4b9758bec331f3a01dfc072c0e7641a80eec5f904fce4f51e9b0e4f48f3568ed4b87174721906d1fc3829ccc3930bb56a7340c0360e5d858e5f916987054040106e5b19a8e8f3404839e2dcb906052b51d04ea01fb637b84c583209f614d1850739bdcfef3594dee5d372e97e41cafe1f8e539caa8f304ea01c1ca93f7a1a7739047ce0e536fcb53169a3cd68f0b4ce12d4b6f16c04ec8f362f8f9d67b202506e5f9073a4fe073bf8ec20de0738bb58c6aac8f360c9c2527ec1991e6d61164c3cd720bf3077479a0e5073cb01ade7aca3cc5da6ed1f3a4fce12d3787ce93f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part11 : Excludes 0x5004020000000000000000000000000000 0xbaf9aa9c96e5082c0201000000000000000 :=
  finishCode 39 0x6717c531901f382e68c2b4dc11eb2d4eca05d06e2ed494c83949fb59500e90d581b46a180176940e41cb56e403a45ce13356d072a3f9a8e83905cc2ed6adac0ec36890356c5da917901293f59ecc5f494a4c435b24c5012d5b48b8b4e404a4fd22ed5b69bc503176a4fdab6d43a08c2d093b163c38148bb52d3b293f6d0bf3356ce12d5b968384cd5b8398714576da1fe66ad9c25ab7352e498a895aa2a4d056a4fc5a71c2547ea4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part13 : Excludes 0x5000021000000000000000000000000000 0xb271fe800e6701680a01084200000000000 :=
  finishCode 81 0x6b1102a1fc6adb50e02502ed410fdb12fcdd2931601a05f122ec5f0d69b166a8b1660f27dda0da6c5922e0e7813335858be7f77d183302ddac605b2e9a0cc1cad5f983292962f82ddd08718be3c79aaaa2741b8116025b58478e0b107386a626282cd67a8375f16c5a036f1c945920af4a1c1b7376974e392b0a528728f5fc6f0fc870bc7d0fce8072e9c8330728f9e072c733413b205bb48bc05b176839c16e0e7836eda0394a07306da426ed392b90660db555cce05d41cb99e83b853c0b2f635939ccc1ca0b3176b90aa1c2414f06dcbf330a65a39aaca062a32dd974dfc6a1b870128176be89316312760e76a5c09f6a8c1ce627940e5f0fcf24a583e0e59cdf0777b5be86f780b6733073a84e6af940c16ed4b8ba60e7073c3e76a118392c5f94a1b908138e4a2c98ddb320a4f81ca2ed37dc1ab281c1cd8be0e5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part15 : Excludes 0x5000020000000100000000000000000000 0xb271ea81c64d8028022100080001c00a000 :=
  finishCode 125 0x2c094370a6308ce24c5286ae3a03bf073c6c3384a85e51f8bb634eb56c3bb356ce130e368e8201e47da0b60da733384ad03e7837a3ad4168d26409a3ecfae5f91f3ab80e796ae8fb1f3b166698c1e51f6c82e81dd6b2cb536b2d07f261a8fe8399ff5ab682d871d06d16a72c5da42e4141e9ccce13062607413e4def28e4faf352d47ed5b0e8940e0e0b48588b245dcbad5b072b68b42e857b922ed4b49f9ba507ad65927f0730dea035acb0bb60e7356d6aeba2d01bd907a6c3a0e62c9409a8fe8c3b56cd86d21871b472168f390547e7336ad8394e12fe352e5ab9bb45dab579c96d4b7e20c5701ce0b989f23e746dc6f727cb5967ae92f5cce93f03ccd5b5aa8f9cfc831a960e796a63c7803e0196a8868d60713e456e0e7370a8701ab6c83690e2e8807399cb5372cc18f5d036f461c5dab1162cc18f403d07390264f9073a01dac3093cdd2833052b68e03210e0bb5bc72cc34f46d858d62a8134039ade073a4fd0272936409a01d8c494c49f1f3a08cfce0b13f3c8233f3cc2300e002e4dd324a4d922ed494cd5f374974e34fb4c5ed60e7176c3874209e62c9a7d1b66b72fc9ba5a731cce0fe1bd57dc83361bb165e0441a06adb08d2181720bf7e0d93140c7ce93f5a1ca13362b5943a20e78d922ed49fae88fb691842c7c4f90db82e49f30f9c9f30bb60e8ad0d27f0f9ce420bf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part16 : Excludes 0x5000020000000000000000000000000000 0xb271ea81064500380001000000000000000 :=
  finishCode 85 0x1e0398b5888438d5b72174561b4700e0a7216b2c2ed51497e43bb18189a307f514b064cc580deefc30c669893e41ce69fa0f24d93fcb52e073ac08024a662c9fe5285311d323ec9b33064b7293f9a62c319aca93f698a501dd949a91749d9c958c097c6a983f839527eafb8fe6d631e4ac0d43000e783baa0149da4fc362a4d8fdac318e2e7cd81121d1589a76527eb624fd2771efc1824f9073cb024a60c0a93c722d61039b0641ca3c96a017f13e407f02cc1cec19871c87e1b8761c037bc8fb390877525324fc1cada02fe7ac93651c2943389a3ee46d9bdc9a26db89f2721072b70da1a761de8bb4e42b0316650bc1e52529313320e72bfd6aaa036a5c39b0e8ad16060c4f949fc18ec13e45932becfc60e72d5c8e14a1c1fc1cb3e80e581cee011861aaa7f4d8a9d95aa940c5da93f9252e42c093b8df6725176c4f9390a4fd8449f82ee17697e6376b4c5eba4f9 (by decide +kernel)

private theorem part14 : Excludes 0x5000020000000000000000000000000000 0xb271ea81064500280001000000000000000 :=
  splitAt 1 80 0xb271ea81064500280001000000000000000 part16 part15 (by decide +kernel)

private theorem part12 : Excludes 0x5000020000000000000000000000000000 0xb271ea80064500280001000000000000000 :=
  splitAt 1 108 0xb271ea80064500280001000000000000000 part14 part13 (by decide +kernel)

private theorem part10 : Excludes 0x5000020000000000000000000000000000 0xb271aa80064500280001000000000000000 :=
  splitAt 1 122 0xb271aa80064500280001000000000000000 part12 part11 (by decide +kernel)

private theorem part8 : Excludes 0x5000020000000000000000000000000000 0xb271aa80044500280001000000000000000 :=
  splitAt 1 101 0xb271aa80044500280001000000000000000 part10 part9 (by decide +kernel)

private theorem part2 : Excludes 0x5000020000000000000000000000000000 0xb271aa00044500280001000000000000000 :=
  splitAt 1 115 0xb271aa00044500280001000000000000000 part8 part3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part20 : Excludes 0x5000080400020000000000000000000000 0xfac5be201578829450e8201518280404020 :=
  finishCode 47 0x360a23190024fd9c288c8396afca2b735a894e2ee8230f77967e3c16af958f5d83ccd3b4efb586368b536741abf1c5e30741cd44af5b6adb57e005819c7009fa4b59abe8393f4b4866afb80d21fa630b1cbdabea11807213946bc614e5e5b584da8e278da1f9da4695cd5f500c8d78c2a44672b92fe736b4ed28f357d5ef236e0f2b3f1e0b4adabee0355560400cc690b1646b7010dabee6d83985ada9f20a497ee4193b6d6741cb9b5a424bf9a42e6d025cd5f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part21 : Excludes 0x5000080400000000000000000000000000 0xbac5ba201178a29400e0201008000000000 :=
  finishCode 155 0xd63e8ca2389a2e05ef2fdae82bf5103370a4527e3e35810072bc7d33f4b0a5223277c1628d79cae7d3728cd21041c7bb69086bd27ef4400dc3a0800b5d20671fc51ccd5b3f4b0dc792c41414b60ec28fe62cb4849e6a4d59ac93f0ddc717620b106699a8fcff271798b2a4d41bbb114353e51db4f547ea11733cb1f69e9c5d06e83991aea3b49fb38d4f9882d5b414a0dd2c2dacb3551fb59dc73235d47e7f98a0e85d169ea4d986e6f7288ac7e6717440cc837059acd49fa802cd547f20dd032837983f353d8bab352daa06641bad0ba2b8a23181bb98ba2d32d114699cb4f6a2b12d8bac379a66d611e0cf776ada7b60f702b5a76b1f5a7b9b658f8f05882b4f9a42c299a66ce3486737b4ce0ee82941bb53e46ba765ace7f951fc00b83a107f816672f3998b5d9c59ac0b383fad3c3764fd5402a739bcb6b1858fe6b35055941e1f1ab8a234ce0528f8da670294596b1f5a78f06165a88bc2e8d5b8019859acc592e3944527e733414c839690c0a54a382a4e2f348598451477293d66ad5585a6b1f727ca4f736a4fd07300338b0238f420a506e511a0ee94758fc1a6288a0a641c94451c4f1e840bb30d61966a947893ad5f255c363362c615ac2e577a1a432c6528f0779c726c58c2852563f1c1566b07f4a3a781399a569e960fb954e5ee3b969e5b55899fe563334f528ee6758fad3dc07a17449ac00901858a73358f9c1563f2d2c58b205e0d2d614f0a22d618e0a2bf40ba77e71dac4dab7181963ed3d059a8a549e2c5660b45d1696a82d00b39672d6149f8b3534696c9350c1822c3463c192225c759cc60e83bb55d28eb134778eed6729ff86aa9112c0b55dabeb396aaad09115a796a6622855527eb29a302a254ffb59d3c67126b277e0da27f49fa05dac2d5f41cacbe3fc80d406ed3b91de7f9 (by decide +kernel)

private theorem part19 : Excludes 0x5000080400000000000000000000000000 0xbac5ba201178829400e0201008000000000 :=
  splitAt 1 89 0xbac5ba201178829400e0201008000000000 part21 part20 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part23 : Excludes 0x5200000400000000000000000000000000 0xfa5dbee90008829400a4000008000000000 :=
  finishCode 57 0x1d07a1c0166c4cb050a0dca220d9070ac0ba330d612c66959365a7a709397b1004391d2049508acd4a22d3da306c4759aad3c13693f9a668e96b394458c511b849fb30d2159ac5cf59486a51d27171f3c8e969ec099590b6b355d626d21474936563eb4b8c2cc5f6af8645a42d2b376ce6b6a2b485ac2fdc8e90eb8f9d64381a43053d1d2d5f62facd569ed5f982f1836aaa4fda57357d3c831443038f9cff3356d27e4d98fc3fbce5d6ad86cd02e93f67035f0afc3aed5b41b8b366ad873e0ebb4ed8c581ac27ea0a61f3a8882959acd35515973e1beac81d7380f45a7b486698acd4b9ee559acad5f928ea03002ca035a9b9b49b30739422b35690b59d0524fd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part25 : Excludes 0x5004000400000000000000000000000000 0xf278bafc80a8c81408a0080008000000000 :=
  finishCode 61 0x439062781f7624cd5b41c8f9d50364cf6f0e7acfc58ed3b589cc330e7b38d027888205d06ea3b9452e570edb0bdab6da35862e7b58c3b6d55982ea80a0e83bb12dc761db6adb485a761cf83b61cf85a693f15fc4d938bb28ce2981e38c2c07d3038f3db0526c51169dcd4f4eda805ab6c2f4b0c04feca4d6a7b59d48303a883a39b651fb56dca334d5ca334d5622e5708dc57b69aa3a47c73d660f2d2d513981d445e1506adb10903966727b9b63020a90d09446099ce6b3dd91edeea0a34efc07d1e7bdd4a225bb527cc5f1e799078280672ba8553c2d0c03383c892d3d318551d8f3ca232cfd3c4516451dca4f83cc5cf03bc605caed2d80e734bdaaac41 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part27 : Excludes 0x5000001400000000000000000000000000 0xb260faa4902a81540aa00002a8000000000 :=
  finishCode 109 0x1d068378d556b0b38ca3e8fe2b9060f1e2fd8f9db41e3c0e5168a8ec3b62d1949f244528e1f70ed827e16ba93c3a63e7839f0e320c338e665c71f3a8edab6b4f570b8f1f1e30307bd28e14b814ed5b4d147717ec5a323a4ec55147706d873e2d10d78e56248969c58a1b381668c56f19c631947d1fc6d21c0edace6696ad2ce661f71e3cc5f6ad83961c021cb39374a01c3ee3cf93b60436ada44c1ce2b3303c91149a874d3b71bdcfce8370e7bf90016ee41bb56d88ee6f9ab63c74a3c3bf6adbe8fe368cc07bc3372d2da5a7333f9cc31623811e3f3ace43eee5d9ccf20ddd0072c7f306d87de3f9a410e3e8705551643f99fa61ed936544e5cf81ca4d9696b53e62fb55c1ca6c598bad5f6178a4564059c0e551ea89d83734b5662b1b9a5ac4b397b29062c89a368d22a90778f7e011003973c5ae5ef26c87bc7b6de30de0ef87bda9f0b5cbde0b185aed5b2fd87dc5af31743ee5fb6d19c0f79b460e9836e0fbcde368ce07bc1cf078da43394c1bec1f9ab6913737837c3ee0e79b469166b348588ed5b40c83943b63e30cdcc5f6ad83945a33900db9ab60dd2e3cd5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part28 : Excludes 0x5000000400000000000000000000000000 0xb260faa10008801400a0000008000000000 :=
  finishCode 91 0x1945e144398b5900356dd87c1fc390c1f7072b78a259cb2c294a3a8fc1b6717928e607399d06268ac07de49f8b5cbde9478703ef2444f925ef38bb0c6488c1fc0fa3e31e4a4fe0fb9c5d63e72590327332f7cb1f36893641b61e37c1c86afc93f06f8395ca739bc3ee0e749fc1f76f2287603ee0dd81ceaa078da7330c5cae9114a3a93e50ac60da42e6f810219d07387bdd8364cc5f500941c1ce94783526c5058bf9063e8de438a3d86aeb1f5a3ad3c1be0e70f387dc1bf039c3c693f8e4a507073b78b4f87ce0d95d2286b0a0ed5f9cae72f01cc387362b0c630209b0cdb188e98e4a93f376c725618cfa3f0c6039478f1ccc3b6c5d93be3e306b8f8e06bb176514873c1b2dc3e80d75909b2a3d949e607477c1598c2a7b4d86d21283b9ae49fa404a0eb4074ce666d196a6f51733b115c973e8fc3b0fe3580e706fa4964a382a43ded5b4c1226f77966ae5372aa80528e0a9a3025cf2e3b9554022d38f7eb47399b56c1bafe07be0fbc6064a3b56dab7036c3eed0036502f3585052d5b968a4df (by decide +kernel)

private theorem part26 : Excludes 0x5000000400000000000000000000000000 0xb260faa00008801400a0000008000000000 :=
  splitAt 1 108 0xb260faa00008801400a0000008000000000 part28 part27 (by decide +kernel)

private theorem part24 : Excludes 0x5000000400000000000000000000000000 0xb260baa00008801400a0000008000000000 :=
  splitAt 1 122 0xb260baa00008801400a0000008000000000 part26 part25 (by decide +kernel)

private theorem part22 : Excludes 0x5000000400000000000000000000000000 0xb240baa00008801400a0000008000000000 :=
  splitAt 1 129 0xb240baa00008801400a0000008000000000 part24 part23 (by decide +kernel)

private theorem part18 : Excludes 0x5000000400000000000000000000000000 0xb240ba200008801400a0000008000000000 :=
  splitAt 1 115 0xb240ba200008801400a0000008000000000 part22 part19 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part31 : Excludes 0x5000080080000000000000000000000000 0xb2cfae62515192805042840040040000000 :=
  finishCode 67 0xca380d62f8a2187cc52b420b6596a4fdccf1a8cfa6d4d6b39394a1ab41a0f2a42d061d8a1edf1fe4b6aa4d49f945d05a7bb961b18751d9c15aab3534e0ab4288a4d9ea28236a6b51d27ed4d8a2ed2d51db8e4d9327fda5ad4d8a200406c61e302bd6cff250d409945d30470c0b13941231815a47461c3aa81366178350c0aba41ce30f38f47b6d2da30ee6b1edcb4f1edc8d75a7c1b62e3a4fdcded57302a907420f527f2035ab71aae0f2d332fd945e00411b4ee69e9cbd62e2cb9e06e2000e4ae81dd092c93f1e49c15caa72f4f4c93f7378f251483cca017b7c6058bae51527a80672ec60527ee518c3b58a22e893f622c7338c3c6114f174520e5ed45969e7fd695d181351ad3dabf316630e6118c3cb3f0549fe568a7fd8e67316527e605 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part34 : Excludes 0x5000480020000000000000000000000000 0xfae7ab31dd50ef809740690024001000000 :=
  finishCode 39 0x18c3f17449fa60700706524a51e52187053c054ca1b8c09bde0fb351dcdef558c0a86dac327e4d9318540bbdbd652ba378a00aede8381646d399ac29015a7a51e58147734be306b2983db904d8a8397a9cd6172aa4066b0b954c88c3c9017a9825cdee3ad3f6c61e2da8704e667132a11933955ac2d5b51da8f4ffabc2d561d6c61e727bd4d476a3d4c1700e0c3c91d8af0be24de04ba51daa727b630ea21524ad2dab6a358e4aa498c2c8398c3b584deeb55 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part35 : Excludes 0x5000480000000000000000000000000000 0xf2e6aa30df50a2809240000000000000000 :=
  finishCode 129 0x5d1b47a1a44d1c85a14432024792d63062a08c7c68335111c1f1af84e5062c0872f7a51c11f2886839831546adc351e503894c4be81373797bc18aa358e429012f7a04d49323b526a4e51f1b18c22f8d802dd4406293e60dda807e2cd474f313d4925b59a6626d9cba82d413cd33627bdbc376e6f404c9ff6b0830dc85a018b07f9246f511d3a92505ad67a0fe49f51a93e6521585a178416a7b68399fa50321bd1bfca1b2cacd33627a88501282d9033073561ac30b5d442a2461e8c2bd5cda2c4b414cb4b8c2a066058a4454420b1947a93f524830d30741445f09f2937949294751acd679edea3516b82dd486a22d0c6270d80a8d8970eb5ee2d5b4a38b4c12f06b5866c5d7a9cd330c9a4fdab6c29a0e67e96ada02501320e5ab6e3b9ea2f5341ca51d446317c690c93f0d797bc16e9c41ce6a3b8ed896d556b3c5d37369eed1aed5b8fd3073622a02505301cda664bf16b82dd7c3b1044c0bdeac400a21d04f9062d1816adb105cd61b1893e0c560fa01181989ec598c2c1b141cc1cc18a923a30280d627939418b203583f07f839b95d8828299cdf073061bd0b02b0bc24fe406b13e0e60c50d8a4dd8c6f230b313d01ab35062a40649fa03630b049566ac4183fa4060dac6031672b8f267a98015ab6819406b0458b3073480c0c57a8c839062b78ac400e841a61d28afc5ae4f96d075341b418ad61a0f68171d6a51d6533585c76b3940693958c41cce57728830e0e720e5852ac251e6b38b5d27f30a501ac63555b47a8ca27406831411f39b4fda93f7a8b58e7a9a7e501b06d (by decide +kernel)

private theorem part33 : Excludes 0x5000480000000000000000000000000000 0xf2e6aa30dd50a2809240000000000000000 :=
  splitAt 1 101 0xf2e6aa30dd50a2809240000000000000000 part35 part34 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part37 : Excludes 0x45000080000000000000000000000000000 0xbafcae30595122800040000000000000000 :=
  finishCode 111 0x1f47c1ac6517830fac0cc1875c87a1bc0ee864e47fb56c5a6b4b3f4cd4d404cd5b062a81e404830d1cb293d3fed576c1c874018ad5b98b61dd268b56e1edcb0d524971d27ef5382cad5b6b08f6db056018b0774e0aa35514c1dd1edb4ae1eda8d5a8ebc3c0b0290e418459841bc72f0e4c1ee69eb4e504e93f2e3cd5b49fb30d619436d5b49f8725a5f34847920a949f9f8d5b492c1dd524acb5657358cb6af6f0eec1fe83b964cd6e2bb72a8ed528ea3552498457c781743f14272cb5436d2b3979c15492721949e1dd397b78a0205cb1341a5203313e8c08775cab067ce42733524a8ee0ee9c1546abc230ac18154931b256968ff49a85965a7b13583a8ff5617c2e3d1815249f5d072d330d6a48d26ae82d2e51aa3fe5a59c08ff0aecb4f0a2cd4759cb5560e6cc29265a7a9266abbd0ac2482d74d0e0aa355118b70f6cd931ecd18ae4b9a9af6b6c11fea21404d0770e6bd7e511344307b6c1d8e4a8ff349c1bb60e86ee392b30d8281e839932c18a6a41b6839b51e05bb9bd013348d072d5f50ab48be031502f28543769df942a3db50d8726661b0397ca350e687757c6b102f358477671305b9cbc35320dd26aa435a5a8866abca43 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part39 : Excludes 0x5100080000000000000000000000000000 0xf2c5ee2a7d5102880040000000000000000 :=
  finishCode 109 0x651f4701ac5f16030fae86295a104700f540e2d3062a0b5d050dca49029c5d306285b60f307993f2901272a035a67181062a44e524b56d4360bd062a90b025061d4c105a6c5a30213b0c4b4cc752a356aacd33062b48e8c3a86d86b23fdab6c5b524a4fc18ad2394420c3721284c101abc230f57869ee5347fc605a56171409875526a6055f1d0491a4d5aab292630323fe579c604ba6a495d1388c0974d49307995eeb4f362cb0d1bf9f1ded727e49ca9a35865a5bd9cd921d5409b4ce5d1444c07c6bc2d86056aac0b55a7c1ee616a48d68524b9be616bd8e0f32bce3025d36b0cf57616ace60e65bb691c6050eab9543ab39557c5d126a92587c67e3364c9ff8d929f949f939574811141f1b516527a08d0662cb93da0bf904683d721a77355cbf680d49fcd8358d6194920bf062ad07cd89ca1b5513a4fd47ad459c76a218c0b9b56961d55e09cab428ee6a382d53ff351d2465e1524ce43c0dc2e81d53f1a8b3555cdae3b25ba86d492c619118798967fd6afa84d202a2972bce6d8c1a8d5a7b31753daa352a1f4540ffb187949e93f6b0c6068c0cd6149fb5163ddc615ac2d5f5d0fc8c0cb4549fa86d492a231166198b4d82334f4ffa7dd9ede6058c0b4f662ea8d54923cd4c1a5724dcc0af578372925 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part40 : Excludes 0x5000080000000000000000000000000000 0xf2d4ae20595002800040000000000000000 :=
  finishCode 125 0xd83a0ba141e28db28fa1495c08c0c80d30f8774c3ae443880d2fdc71769aa4fcbf7358436a93f927f3d9dcdae3b5a18f343badc390cc2f01dd581aab1c5da72e3b6adb95c3926111dace576adc38e6d71dc1a6403c615cd6837627cd558c0a8ed8c4f17c50102f0699cdad5751da8a5a42839690ce519a4334866abb4e527f3786058c0ce55413a0dd89f46147931814fcb515605d1c027eb58a4187d05b1b14c3a7e990463e3699af0da23fdacf304d07aa1798266c59012839411cbe358e02d0e30f98a51bb460c79ad2b05fb57cbf680d906e6059aaae0359077816e6ab40b98adab60c54a168501cf518348b4cfda80d5e17c364cc3559ca495826947351827316d387abc007695a35dca68ff61a823c266b4b47fc5d32e9c8d7409ad3d49f20cd20274208da57357c17e80d05fcfa368e42d0be20b5066ac187c6af00fdac2f5305594353c8c3c81940ba93d44ed61816250d934590d41f1a8d6302a04dac736ce6f05b9c4da572405cdeac204e286b58d5f737cd5530eb4ae158b555ac72cd0793dcb104c3e80930ec38d618b7a91141ca024c0b393dece50d4c158700a1abe248e524b10528e8ff8c3aa4946ec3e32dc9f8d486e02c05d39012d472eaa444c3ad5595e68ff2e9b4e4fc6d538ba67e32e9c50d5f0c3ae6d879a5fb4a3a8d6736b56d04286af86f74a3ca21397a90e6a7b51d4931cbd442937 (by decide +kernel)

private theorem part38 : Excludes 0x5000080000000000000000000000000000 0xf2c4ae20595002800040000000000000000 :=
  splitAt 1 128 0xf2c4ae20595002800040000000000000000 part40 part39 (by decide +kernel)

private theorem part36 : Excludes 0x5000080000000000000000000000000000 0xb2c4ae20595002800040000000000000000 :=
  splitAt 1 138 0xb2c4ae20595002800040000000000000000 part38 part37 (by decide +kernel)

private theorem part32 : Excludes 0x5000080000000000000000000000000000 0xb2c4aa20595002800040000000000000000 :=
  splitAt 1 118 0xb2c4aa20595002800040000000000000000 part36 part33 (by decide +kernel)

private theorem part30 : Excludes 0x5000080000000000000000000000000000 0xb2c4aa20515002800040000000000000000 :=
  splitAt 1 103 0xb2c4aa20515002800040000000000000000 part32 part31 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part43 : Excludes 0x5000009000000000000000000000000000 0xf274fae0613251428a00049200000000000 :=
  finishCode 69 0x3e0fe3a0ec3800e56d170176a189317b3c3bb4949b15862c474613db348549ee6d8137181690ab0aff989ea1b399a925ac32bfd20abe2608c1405e1595cc595c188f356d492b570d0a50d6af35358b3244cdef27655fe917489b0c66a3a8d4dee94022660ca8852769436d142700651967336a3a8be30ea21494a8ec16f1bddca28dd510a4a5945f1545c1067073941a2d105ba51e0b9b12e0e6a351cdb56da67351c16ed5b2f79fa637bb51d3c362c72f37ba51e362a44da9b0195a8e92530ea0cd44308c61f399c1872f4c23032855226c2951098450071b14c56295a0faa497a986b507a943e88420f59840e9a8d634ce57fb515ec25e3392a90e05ab57dec2a3b949e0b56a7c7339a66cc340ac02d4df734cc14a7cd397ad1e37db53c1132bfce5ea07161a49651db53dacea27816a833 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part45 : Excludes 0x5000008000008000000000000000000000 0xba74eba145d050039008040050068000040 :=
  finishCode 17 0x1d849fb80f83e86c987921dd072941e0eea98a49839a5070e6c2c305ac507072ab0a620ce40ea884e26a496d189306c4e5ee6d8dee9178792823 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part46 : Excludes 0x5000008000000000000000000000000000 0xb274eaa1411058028000040000000000000 :=
  finishCode 145 0x1945e1f4398c18ec3c06294a01cea139a428236a7a4c5ab7245cdd20a50558a4649f9d8ac2e8c4308d218e6691349282c4e672924bde937397c7332f7c61e46e82f4d6ed4f49fa4c52265ef9845c14c021d1816b382c4d8a91f4a1b4ee6ad9ef630a911362b53c162da251e1eda51e8c1b56d27ed2135bc6c5761880729cbe0ee9c5e6ad9ccd4449fcd5b690c0bd05cb8072f83ba2ed382c72f4a1be8f83c0fe3b0ba039cc3f0f8c9fa813419b087a2c061a7ad5d01b185470a4a564836c3a904c987c123393d286901836c93f3f4a3bcc3ec22e0682387bf494c1ce49fc605acaa4962c8e7d2025ef7b8c8e1608c615ebe72f4809b83db49db17e411973d4931b15862823364c8e11eda387bf362b536698ac9d8b2c119492b1b480ae861f904672f482c61f60acc2d49fa89142f8507392c3e3399c61e4f69b2549271360aa4fd8c5f127ea3b947a1b3399a48aa0f2e524973d8bf3dad4026c9503ac1669aa8eda9a921c94d930f4d8bea1b623c6c962fa7b4a0f230b81e8943451252193940e93f1dd973e283b8ee8c0941ce0aa4946ea92649fa414a0f2c0526293f781c8761f46801cadc4181dd5221c308b13e6b2ad5e3029013978a1e614a3ce3023c991dea43690c09783497556ae7334a3c611397a9072f283c6116adcd657f1a05e11e71adc9629470ee9fa45dac424062e7a3cca0e1dd6b230330a51e672f62fc93f96aa2ed283a92649f87757c5e0c85c12271818382981b163e4a7e412e94726ccaa1cbce667bf89b20a94a3c605300e096d68c1b4c5edf46151c31cbd78514ce6d479a4fdab61c15c0e267fd8136c5f479d183524a88585f1abdc76a1b6ada4fc1cec15988a93f (by decide +kernel)

private theorem part44 : Excludes 0x5000008000000000000000000000000000 0xb274eaa1411050028000040000000000000 :=
  splitAt 1 87 0xb274eaa1411050028000040000000000000 part46 part45 (by decide +kernel)

private theorem part42 : Excludes 0x5000008000000000000000000000000000 0xb274eaa0411050028000040000000000000 :=
  splitAt 1 108 0xb274eaa0411050028000040000000000000 part44 part43 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part48 : Excludes 0x5200000000000000000000000000000000 0xfa45aee9400000000000000000000000000 :=
  finishCode 95 0x20c74200651807a0c0a93b28b948522f02160db07341e9f26615a45de07a1b86701ba73387ce52513cc80349f8f9e49f984ca4a2ed8a4a93f069a4fe6d1f47819c06b8385a8b1cbd28e51b097cf613dfad1c51ed5f4779cbcfc517c9014a3946d27eb0320af78df62bb1769814e66c4394e283a3ccffa28f926e8ef579c0cf51a946d24b0924e6659d15d946d27e0d928dc7f9070be8e03280df309c61f49f875d206e127ebc033d300c8cb134779845c7312fcb3ab45736c2bb93e7033c7ce2ed631440ebb1093f04cc83d5a28b2dab72c7e26cb13565280d521a8b06d89ca3cd272c0bf87ce0cf701786b018f18445da62b4c160610c0ad00bb504f28fd0329472d7c0af27ea0664a393f5a0176b54640bb59526a947621cb3947682d60dea0dc5dad6031e1f3987da05d1072b1b90269010d5a0ccfc57b9236097b57e3068fb49fb57e72aa3ee30738ed61ae6b49fa3edb463107adc075da43235da5691726cc1ce2daa4fd22f28452869c31366a68f3547ed33815ef403660ee83853c0698726699a4ecff3356d27e1c9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part50 : Excludes 0x5080000000000000000000000000000000 0xf260fbbac40000000000000000000000000 :=
  finishCode 129 0x1c8761b87e01aefa2a80dd6910668035603a63e3695c6a151ebd9d47734b542aa3d983ab57350b56d6c4f103a1d3286a8f6720b07549e7c983a728f594631580e7a886364b57d3fed2d286b57e4ffac356462c9969672549d94356051eca213978b25493356c3a71c947c60db80190524c6113149cbce66ce361181a0d2a35491b51548652128da3868c0a51d46aa496ad874d94580c6134169435446adcc15622aa01538af65b53dfa385a8ad5f5aba3be8c0b5151c2ca2d01d3309c61f169a0b5853184dcbaa1b72598a5784d188b3175ab7181489984528eaf3a30292362298454460188b306d203181169826e0cfb175853355cffaa4969194631b84d1a8e1d3065b56e729b95503a813494cbc074d247174d636d65398a51d49320b50667bf4f9c80d729b92d05a0cb5f1343b18c480a44d44169c5d3737c3bf397a924e674605c96a215510c51128ec64606169c606510c61e737c1a4e42b27598a886303181968f1eec5a6b0d6ada854e43003201c1941b1813999e07e461649fa90da96c4248e8c09ff6303248e3fec6049b3317582ad5b8c0a88d830093f510d1875248f25aa7460564e7fd4f6b52e3d4a3cd1fe5d37a99c4d662d5b6a3a98d61a3027bf3fead1d4427135249ff647f9f24382ca2b8941cc45af356d6a683d40eb55662cb5851fe8335611ff23ed4924f947fcb235f154053ca0d72aa925ab69236a3cc11390ac8dab723fce26c83f0ec36062b364c93f30eb074186525398acc62e9a925ab661d56126b28bd28e4f969120b281cf7e0c358f8f8c3a6d81cc659ca4fd1ff2d2cba71cc4c567319ab6a43 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part52 : Excludes 0xd000000000000000000000000000000000 0xf26fbaa8400000000000000000000000000 :=
  finishCode 33 0x761e874200072c0e76505da0df272ca21398a496302b38e0078cc3b1cc4c527318c3b1cc4c52ce034e0f18bb594286cd5b30e98a564308834d8bb356dc7aa1551d8ed65603c6a613e4e06b3c5ef3988b5d442a49398c3cf416ca62785ef1e7c943488c07d57160b30bce6281d8102c5f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part54 : Excludes 0x5800000000000000000000000000000000 0xfa78bbe8400000000000000000000000000 :=
  finishCode 155 0x3b0f43e8f83800e56401b6cc32872f3998f263988f266716af201ce622ed401cb2b7359cc584511947b7c7316ad873ce123e304fcb2f6ad9cc6580873d05ab2f398c7095aba00e382a0f43b6d8370d2035ce6320f4e4a1db398c725398c7216adc83d0eda00db47c1ac06cac01cf839c2c549482fce62943390c73164147b250d49ec4788ca73161982fe398873c1aed01cc5edf2925ee30775a2a0a45a61dd49fca2f6d19c069a882ed0ed828e6adb95e6413c5f0e0a9ff9ab6e6b3fc9cbd1814cce573fcb56da9a1a16a8c7f96adac8c2d9ab6a15054a803b5923e7f9736cf6f1daad05944a1cd5b3e9b9b66aaa78ca2c05624ed2c48ba09e37bc1ccba6d33681863209c54b1bddab70684deed67413af86e1f8b419ab6a1b40ba991859ab6a35737a43457ee579ab6d83306f79606a1b05c8b4d4c51aca4948689ae8c2acad606661aa60a181358560b725eb54e30b02dd46b286d82a6f71dab56d446c146b39b589293f169af8b0298e399ab6837728829c3433944152d5b9897240d02c0d619ec28f37b7ac0cff28391d6cd61617b12502ea602a64ec9bddec2a4337bcc2f906ea43511b05d16049f8b4dab720a5cdb2795656d5b57fd07769db56d7c5814c50014e7f9905291f9a5b2795a5e0a98c2c0b7595b56d08696c9e56a4ce516adb40ca34be4fcacacff22bf580e02d0c0a73fc87264ec829d5ff3d4d6329d99682da2f8ba308e0076dee341cc5a2819416a0cc1962d18e5ea2032ce5f24fdac734c4e5f07f414832e6a3c0cb7a17c5020e702dc5a27315d0ba702dda43356e398a4ee (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part56 : Excludes 0x5020000000000000000000000000000000 0xbae8afec681000000000000000000000000 :=
  finishCode 157 0x100450fc328be1434a42e0358a6073d62b355d62b20e5907c166b0bb5186aac4b162f9a6daaea4f05ac9111ddab8c5f839c5cf83db0bd07291193b7285549ed5f0e7b05e176b4b5746c0bc30bb5226c47510a51c1b20cf28db20b00bb5a04a3c839404ad0637b81ecd8a4838d8ac196a9b56d7c5714040bb8ee62ea7adaa693741c8f9e1c2b51dc76d211e6c9476a3ca0d6178366701b45e01a6d2d8feee57151974dab62ed68039ec834b4ba71c4d88f276d697174ce0aae360ca2987316407ceb55815e0b9596c90d15f829c1732c0d406829581a03e4c1c90cea0a5edf23b5caf0775aa9b149d2b039ab6a63403e7623cd5b618b4b5ec3064cd8a90d696c809641b06adcb450e8a306f7591c5e159ccf676ada066274ac0dab6b025118794527310e7a4ed286be2d80bf8b4e0b71f39bde39882fdb46afce57728b4f5a5b13a57c5b1b46a48f9d6ab1efdabea2937bcb3f96aad49398b17e6aab56cd5ed8358a438d366b70e783341aec8036569f0bb4df7251d7c7c1785705dab0205d23f4605286925690a0dd85f0f3da8a937697ca0d488b18ae073cfef317d68f079969eb358b4ee5d482b515580e7a4de5959cbdaaf0bb67b9a45da8ee03c0c80365ac176a701cf7b7cb4b696b9766b3c61cb9eb3597c651300e7936e6b0a90d28ef63872ed236b0973e30f351d866d451e6811e09ec1cdabee672e7a7ada5ad6033e49f873d28f3dd568a73149f8bb5406c15c640e628a461e043acd477693f51ea93dca334f47ce93f514a88be24fdabf461da7a7bb3688b1e6a2cf67640f07e14523cd9a7a2c549fae85a99a7a1cf1ddbdae259b55da5ed02cbc79b28d417e6c59a56d5b6afcd2f5f147b3484b9ea2f0e7b4b66afd07b05fa7ac39e3e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part57 : Excludes 0x5000000000000000000000000000000000 0xbaeaaaa8400000000000000000000000000 :=
  finishCode 69 0xd607dde80f7bb0f6fa0e662b6ad9874e620e757194530e62b817bd1f7247da432ce6403b51d543b100f249526e983009471e4ca0d41ca925647201d02f13660d331054868376adb00b00706506934503293589b324fd6469354f17c680dc1f3a0dd00f23260f6d2d617b125ab6c318c56c438feeb572fd98ad60651d048ba32683bbd9d012d5b30eb11e307095da8ed6783b961d012d5b30eb11e6adb17d1e66c998864d16adb20a21844c571345ab67bf9656f536514c521cd55309b04e464b56c9a2d3b9683069741e07001ce6c98c0aa2f176837db05115c5d0e629099437187513a8f5492b4f9a8b24fd83b0f34e62c4d9abe3c3517ab8c81cc528f18151e7173d2466fb4a3ab093f1edc6fb1e6a47e37d8f6d66b18145da731 (by decide +kernel)

private theorem part55 : Excludes 0x5000000000000000000000000000000000 0xbae8aaa8400000000000000000000000000 :=
  splitAt 1 125 0xbae8aaa8400000000000000000000000000 part57 part56 (by decide +kernel)

private theorem part53 : Excludes 0x5000000000000000000000000000000000 0xba68aaa8400000000000000000000000000 :=
  splitAt 1 131 0xba68aaa8400000000000000000000000000 part55 part54 (by decide +kernel)

private theorem part51 : Excludes 0x5000000000000000000000000000000000 0xb268aaa8400000000000000000000000000 :=
  splitAt 1 135 0xb268aaa8400000000000000000000000000 part53 part52 (by decide +kernel)

private theorem part49 : Excludes 0x5000000000000000000000000000000000 0xb260aaa8400000000000000000000000000 :=
  splitAt 1 127 0xb260aaa8400000000000000000000000000 part51 part50 (by decide +kernel)

private theorem part47 : Excludes 0x5000000000000000000000000000000000 0xb240aaa8400000000000000000000000000 :=
  splitAt 1 129 0xb240aaa8400000000000000000000000000 part49 part48 (by decide +kernel)

private theorem part41 : Excludes 0x5000000000000000000000000000000000 0xb240aaa0400000000000000000000000000 :=
  splitAt 1 111 0xb240aaa0400000000000000000000000000 part47 part42 (by decide +kernel)

private theorem part29 : Excludes 0x5000000000000000000000000000000000 0xb240aa20400000000000000000000000000 :=
  splitAt 1 115 0xb240aa20400000000000000000000000000 part41 part30 (by decide +kernel)

private theorem part17 : Excludes 0x5000000000000000000000000000000000 0xb240aa20000000000000000000000000000 :=
  splitAt 1 106 0xb240aa20000000000000000000000000000 part29 part18 (by decide +kernel)

private theorem part1 : Excludes 0x5000000000000000000000000000000000 0xb240aa00000000000000000000000000000 :=
  splitAt 1 113 0xb240aa00000000000000000000000000000 part17 part2 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part62 : Excludes 0x24001200000080000000000000000000000 0xd3fec4d25d7924349024011612000900000 :=
  finishCode 79 0x6c17865160398b70e207145af28bca0e2799a6f06f698a044762b458a4a1b12e4b88b29946ae6d06494955f32cbc1822a15416059fd07727e86c437a8a261071946a71b83bc51b15aaca6047ad1430a81128dae89476e0a364fd9cda8cd924b2bcdcda1c5711741d8c2d727eb78dc051e1bbc1dd61e71b063b07e01e84cd3fb1878c09c6da6f348d02318116ba606e3874281183bc842d0bc1d0dc2683cd440c837fcb1d492930e83ba4ddeef0eadaced378c38b5da6f399e30e71b261a60d31835a93538d9e07d78d7ed2b3ee8a8dabf1afcfba7d783bcf77698930c79a9834f6614b07c56671b7b5c2d76b3a989a248dc230e517368b5da6f34adaaef5b8756d330c5a4dd30698cd3d733b4adaca08d250c16d695b57da5709e5a7a2d716bcc1f6afa3355e6d4d6b3b99decf27e5a9a923531946e13016bb94638dc61e6a7a44dca2d4d8e371872469f5da9e4c39cde005480a4ddcae7d78c3c61e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part63 : Excludes 0x4001200000080000000000000000000000 0xf3da8442550820349024011402000900000 :=
  finishCode 127 0xe8438f2358ba2b0a359cd69471769c84e66b0378725398c62b05f946e30f17edc0250c51b3158bb5b03ebc731261cf5b1c9b80e2298bc1c34c3e940bb479b41ec972285a0f71810e2b9b60ef39b4c230bb4c56af99c9e5891538d645da7171dacd632619c5dbc4c1685319c3719bfd4431484fbb0ad469a3857119c561546c126e9f9941a5216a6c8cd1cc9bec35a2a38c38bb68c3c7dd290a4445dad82a0b023bc56b07b93d2b03302923608d9fc6302731581b9467bba7955e707b13a9cc5a6339b5eee4c3697c5b93989bedcc698c2ed039caf93029484c81769cc608eabcd1dee552d0bd6deeed8328b0383dcd674fe9cc55e739463029e912bc8cd72c89fdca2e6d4a3c2ed6b1947c13430f9bc62ce9cc586a5fb73168b02fd1e69293f0c6f12ceaf0941cc4d87353d89a3cd5a2c4f3524967456a9228be279c61e378b53cf058050312244b2e6b37f9b7c7628a2106ff1b8c2b536ac4af408c3712508175caf2d060583026ff626ca2f302bc8ca30d6398b13438a62b290af0b03102ed838a8118c22ce394657c92852222ed3216ab23bdcab04e5cb307b736cc1180d249d0c0967502261f38db88ca2f0ee3d062b81189b0bb4e622ed98b62a91e6b8ee736c1ecc0ac4d1768ad6398b48e8c385e49fa08330faf0941d02ed873a3b51e6c2b50d882145dae6d85dac63d5e38db9b60ef1b8c9e6ce01dc0fa2eda0ee731855a595 (by decide +kernel)

private theorem part61 : Excludes 0x4001200000080000000000000000000000 0xd3da8442550820349024011402000900000 :=
  splitAt 1 137 0xd3da8442550820349024011402000900000 part63 part62 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part66 : Excludes 0x4001280000004000000000000000000000 0xebdf89665938a2259d40290826008002500 :=
  finishCode 55 0x220761946b1c030fc62b6f14c450bf63a78a427d737893ce3eb9484faf391630e0732908aae62d964ce2e5fb580a431815a731484dfebc3106056a9c4836b1946ce56861eee3eb9285ca2e57241c1ee8c29f85a7af758c2c59d8c39ca58b2e6d43033f09bcb26e515a79c5d8c3b1885a8892e261abe5cdf18580b7181614d18771d8315666725834d1873f0b13ce4aec348e0318b4330729541223293630e9e915a9cad9405cd07751fac7e83fc00183d9695cdaa3f395812e51cc1ddaaeb230ddac7e3f0c1dd47ed57394c1ee8c3b99d47e1bb58114530d87399dcde19b37fbd76733a44547ed4f8fc2f55392bdd5223235dcde7e12c9b58c6d304a447eb093db869dcae725 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part67 : Excludes 0x4001200000004000000000000000000000 0xc39b80c64928a0249000090824008002400 :=
  finishCode 141 0xec381043c9103782e76c18c7119427ec7df30f831c11741fc9d23ff736ad46380a07d8871161328e4e3673727e9f763eba93630a73738b9b8e3928ffe89230eee38886187deab141ce2ec198a0e91f98b293b38b93a6392a190719cc2c47417973cfde5079aae59b60cac75785819816db48d62c8e38e832416eb42c8cf6f34d4e6e0b53804ef394cdf741edeeea2b8d6a0b137dc487f18986f592dea45d276a62896737b59ce6ed359dc6b1a41efb2872b83ecd635018324fc3317dac7305da73311ce56d6328d39982e80f063a03e41f96767298a7456aee250e2e59c6ce6e3df591c0c1064b5910448c6187c7ff20fce6f18158b2801019cc59379a0049e683f15ecc2b064a03d07e3df6f0dff17e4e62e53398c7f11d89814302a62d0731944a0c13949cdd63f13cce622cf6b1c7f13989495b0530ec609c5cb05fa03d03f1030ae3789b0d2864f3155ca2b5129b8c37e0bf5c1101ffc4836179cc5042c4966182e525963a3ab3dd82f4e63304d603ddc0bd38b973e292b78cc0ffcde30f7d6724a78b9ed35621c5fb0bdc38c6440f20ffd0c15bcb333f7b9b4e62c5f2e79c5cb089163ad81c9522e399907ee5b83fb06600f8e65262e3b82fac1f73682f416f27cda9e931368c089479a03d07ea64483df045cb1f2328add01e83f392b600c98072b1f41fc61e60bb94cb7eb2372bb28b0032648882c4e4a86317e476c1f569eb2381928219222f2328717392c1de00cc604762931238c009608ac8cec608d07f398b16570064c3b10c0d18715b9b7d822a62180bf901e82f83ec93158e86dd07e599847e03957cc1fc17e731 (by decide +kernel)

private theorem part65 : Excludes 0x4001200000004000000000000000000000 0xc39b80464928a0249000090824008002400 :=
  splitAt 1 115 0xc39b80464928a0249000090824008002400 part67 part66 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part69 : Excludes 0x4001300000000000000000000000000000 0xc39b84d26148ac26be00000000000000000 :=
  finishCode 133 0x308aa298ba278c62c019f0d1af009b261c6f30548b6cf571bcdf815ac73772a9eae69b930c11ece4405cf810e2bd0cd93cce81679ca64a1ac8c9aa9438336d3381369296f1501d5cc592c78ffc5ce70139bb40ce1ca57865230b09cc5662db05a8f36176b28e22c361d5c1dcf762b37abce4f8c0a4349432d3e1e6c1f521a03b62cc9e95268e2c5dad63287dd9acad3162ca47cc3ebc39b61e680e45da5f98c0d185139b164de62ed9bc670e3a982f072960ec8cd176b4c47be2cf834ca394828f7e205e0b1f24363022a1173898e3ebc1de302c359eb7077480b0d6586ad3ce52bc4403cd16dc60647797ed89e2319cd66f38c3a3be2065123f3164c3ec4f96a3181379c1fe6a8a50cde7187480a4a59c05ec93716d8b9ddc7e13c379ac09e99eb2f5b2dea45d86b316c0920499c8f23bcbf27315a7ca0369a9cc620792245e1487358bb508315c7311de9cae398b16dc7a6f38e62e3d771c7b021da7a07f6b28ffcc3f07f9abe39f48093f564703047fe2e7315c089661bc7716838e82d61e6acd4e52b03076586b93d2861599c9e04d1ef9d05bd9aaeb236a5c595041831d4c7708e302249aa6f369ea50c107348c112d57056c3cd38ecee328e2187e315b78b041a6380b93ce62e591ffa935501ff82166a89c3cdd3354540620865e83bad251f673172ccb4947db386f38706283135b59477a7dd1ffa10980ed5cdb16560fec29736c383253c604dd2369a0fee515214c4409fb00c428eb231599cc410e0896a5cc1d0479cc4bdb3134e629019472731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part71 : Excludes 0x14001200000000000000000000000000000 0xcbfb81665168a4249000000000000000000 :=
  finishCode 135 0x448f2358ba330fc1c84e66d23d072b60ec93716bac7dac71eece529479c7aa031e6a0fe0dfa3bdc0691f8530e3a1bb85ae7373a1b02deca4d3eec6b18c3a414b7a5978b7307b16dac0d47e861d080f55140738f5ee670583e9a7c152821491a3be2dcb9ad0422db928e2d79042e615fe145b9acffe2db410bd5e13fb8f5c72f754a3931d85f0aac1562d7382b80de2d098268729062ce631e68b6ce5707b838a9e951f8b6c1930afcfde8ef39bb18e61c7616b8f7d6ab395c18a2d716bcbc338e6304e72288fc5ae8f34899c5c5b62d7879a947489b48e7bb85451e65bd16b8b5e142c38d168b4cd22e7176f1dc691684c150394a9072b054c1c58c3868547f293438ad319cd6d4b731ac8d26eb01cddc7730bd66ad3346682b438a251969f0774d1186c0e3a597919af750d1a80d47e2a19612d2b482bd086244d24a6fb966ad379acac1960ccc5f16db98d65985e5bd491bd6d252c1926acb3f3a0dfed4f8b729231e6c947263bdd5685c10c0e28ed65a7b11c98f09b4dc6d314668ad526f1b8c98f28fc94b3064762d4f4899bec5b6d62e07e18e6e2d741faf0de278e60ade407acbc7bed20e9e5a782fd6aac2b9ca24a95a78e9dcd71b5418ab55597c0930d9c0bf407b9b5bc1d8c71d37fa50e3f8822430aee328a0268a63782d75a122702d60ee73737fbc89359a621ab16d9c768c3cd4537996e58be3cd16dbb01c59a9e72b16d83266a7b544b7293505886861e68b6c5aeb038d62d4d49a82ac5b62d7791600e0c19b480a4dc5b68cd855292549b9fc641faf0b40ae63eeb59507ec2f05a8715a6320fd26e2db15cc83f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part73 : Excludes 0x4041200000000000000000000000000000 0xfbd885c3c18aec249000000000000000000 :=
  finishCode 15 0xf2330a60fdce427335aac80f41fb52e477b38a60fdd7841f96e649b9cc475f1cc6398c83f7c012f18447fe83f04bc3f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part75 : Excludes 0x4003200000000000000000000000000000 0xd39ec9674128a5f59000000000000000000 :=
  finishCode 53 0x358b8328d03982d77c145f396630e09b62097bce6283f064ca2f398be0a439cae5fb30fa688cb812aa43386978d487028df0498c61f41fa7ce04fbe078398921fc507f07f9cb27370c8a7cd45e0a38c22d21bfc762e51967e08f91965b983fb9b65a2b57ce6e83f580e1b461ce6e3f704d827dabf288411e7d737f8fde085e1a47616aab0304e279984565f2cbe0499b7c7fe921cc64f993ccbc6e6b521be0e4f86f262b609ce6b37fb40a2f735c6f139bb166510987d89f2ce5cd69f35218325bc6819c37f981650d9c75492467969ef7538e8ec56ab0684e62a219492185 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part76 : Excludes 0x4001200000000000000000000000000000 0xd39ca1424108a4249000000000000000000 :=
  finishCode 155 0xde300ca3184f9281b382b58b9e7310db82fc7ef0e23be6a6a50ce66e6ba0f69176a6a0bce62b239202717399c490e2e8d6330ce1c84e6651b87ff1818e56c40fde28da987428bd843828dc63718a44e1a01b8e1b11f452209705195fe466a48c7eea0d308a4ddf0731e8176b8e6349ac0c38ae6d1e6ac3569ee5185462b5728c9373029bfca3716952462c3506a88526ece398ec3e83ff176c1de39b9c3450b4604d3a90198323b15919c5c7fea639b649b823ce1b1818b32923302bb0fa2d3e83db9acb423b573687163027374c0b72b4f695ce6d1cc9eee591b4acf7716847327175e1cc6114c176aa0737968a82f0cfc48d394ad1503eb3f46188580e023cd4f4c5f98c0cf5f8472e3d12eb9ad3d341f41526117afb9adc440f9c3e47796e53d251b3088d661b0a9860572bc9472509bfdc9eb45394b9464a3a07e8c28f3dcb2e4f8c0a0bdcdaec3e07379cda3ff173aa051b1e6c7013ebc3cd1fbc3ff631dc670a370fdc7fe86298b4f85ae73340fb96505ecc4111818e4273350144b1cc56728219c7ae5938798ae398c1082298ec2e883f30f9c8639b9ccce6f27a585316e45ae7058c0c62b382809641098ad07ed220fcdaf1cc504270f398c821398c83f3749c86244f4ca3972c9494e662e7949a5256b224700e66943e87176514c60fd18149b8b5cc3ec1986d25b947798ad30308d1811cc9f86303338980bb476341dd23f181620a40683ba47e3030da458ae62f118186b26113158bb5f48c0ce6130f9d88624058834605eaad238dae13b1d8c61d1e74605002e618c3e61138bcbc1d82e758ecc4905ba44d26eca41de5819b9630ec194a3accc5aeb339852d3160cc605b05423033dacde682f41fa185072e7cc5f6a7cc1916bb411879cced5f153b0bc5ae5bf9cda731941ab1d2e78b0d28e2e7 (by decide +kernel)

private theorem part74 : Excludes 0x4001200000000000000000000000000000 0xd39c81424108a4249000000000000000000 :=
  splitAt 1 121 0xd39c81424108a4249000000000000000000 part76 part75 (by decide +kernel)

private theorem part72 : Excludes 0x4001200000000000000000000000000000 0xd39881424108a4249000000000000000000 :=
  splitAt 1 126 0xd39881424108a4249000000000000000000 part74 part73 (by decide +kernel)

private theorem part70 : Excludes 0x4001200000000000000000000000000000 0xc39881424108a4249000000000000000000 :=
  splitAt 1 136 0xc39881424108a4249000000000000000000 part72 part71 (by decide +kernel)

private theorem part68 : Excludes 0x4001200000000000000000000000000000 0xc39880424108a4249000000000000000000 :=
  splitAt 1 116 0xc39880424108a4249000000000000000000 part70 part69 (by decide +kernel)

private theorem part64 : Excludes 0x4001200000000000000000000000000000 0xc39880424108a0249000000000000000000 :=
  splitAt 1 86 0xc39880424108a0249000000000000000000 part68 part65 (by decide +kernel)

private theorem part60 : Excludes 0x4001200000000000000000000000000000 0xc3988042410820249000000000000000000 :=
  splitAt 1 91 0xc3988042410820249000000000000000000 part64 part61 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part79 : Excludes 0x24001008000000000000000000000000000 0xcbffc3824d4812321008040000000000000 :=
  finishCode 73 0x6c18c57127f102a07314c102320c49e720bcde6b158c3bda60a3c1b45ae5077916c836c2d70d98b6d242a07a6b3fa0ee7f17b48b5e6b28a861abbda52269378c3ae8d6204e0e306ce30f3da60e61a76a89354de6b57a0da0bd3d0d4623cc193e19b9507e8136b16c2e4c2db41096f640896f616da9910358507836ca2141fb17e379b17e2dcac76651c0398c1b6492bda50261c516da98f69988a83d5a2a0ce60b9ad58922db9945d0d441ead88138c3c2db736c3d3836822e1308f4dcaef695e1d8701ac16da98c599a9f0738c0ad5cb7ed5716bb4de580c61d63ad4f5abbda6406b55d24a6b5a30e17b6a7a035602b2d43124155c17b406973dc77251dace5b99caed4f35acc2f8c3852d89ed45836ac5dc76b80b9d0c617c947264b17d58696d1810d6c606733c61e0fae3b7369ff6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part81 : Excludes 0x24003000000000000000000000000000000 0xc3aecb8f696801e00000000000000000000 :=
  finishCode 29 0x6b1c0761a07216c067b0c66239c74e56831409c83d398a00502271da1c6507deb41cc503b312d62f41bd4371ff589693f838cc4f524a0fd65a1c7279b283df905e0c341fc3df5b1743988f7d4372c550668019ece80d5a19cc605f9f8813968a93f380ad071d38dc7fd83e8aed68a83d409cb45 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part83 : Excludes 0x24001800000000000000000000000000000 0xc3ffa6cb5a5a003c0000000000000000000 :=
  finishCode 37 0x881c4063c2bb49f93f4e625255b18c281b488a02fd88f3dd502707352696ed892b2d15dbdd660ac1fd27eb17170c82f0c0ce5d416a04cd6ac6370b5749fbda63e9b99d5f20c12d0c61e2c4bda4fa6f750d8d06d3989ad5b8641a46b1647207418e3d3066ad0aa30b615d8f4d0665959eeec5d371bdd5226c2d49fa4961e9a04d607bbca3f3f887145b6a4131e49fa07507a9479eb281d927e3d3066ad0b6208d82f0aec16a93f924b0f4c176813 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part85 : Excludes 0x24001020000000000000000000000000000 0xd3afae8b4c4921204081000000000000000 :=
  finishCode 61 0x6b21c6316c5307fe82f927e73769dc821395a4fcfc5a15449fae900198f42d5d8972c5e0e2c1b41eac5e38db28b17625c8110daa0f502317ac37a5eb9022c4b4119c6e59dad5d08625d0710bf8a556766b58de2982d5d2c4089f5e725abe4d8a7d38e62af97aebdd60ef0ab4176e4b6e1022ca1cc6156c1de35a871457727f519aca3a0a04107315b0d6ae619cce5c94008b9cb93399c3726c5859e8012e4ce67416a04ca062e735aa0363959cc43730b9dc06116862fc3cd3959cc45ce737398ca2b1739ffce3a503640a06a6208437320bcd631ad5ed29e912ed07f3ffac3cb7270f62f9ffe398ad8731167c6c52818b9d68371d07d49f89be838abe4b92813 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part86 : Excludes 0x24001000000000000000000000000000000 0xc3aeaaaa484800200000000000000000000 :=
  finishCode 131 0xd643910079dd86c038b0b9ca365255616c1e6c5cf1618b9ca1af41d0d01ff526f0f3528ea498d7e8ed41eb07e614ac05486e4b9656b3b170c3ff1fbc3ff7a1345b15458128ea60b6c56f1fbc16320f52223d7960293f488b60c62983cd922681f49fa0c58bf203504293f35aca3f139cf593f796fc10e2d74068b5e406870528e7406845b6f69927ef5b83fa07527f30c47bef772ded06d7b4c1c5ed66b5595ad5d0222db6103c6b62f0d00b9d34623c72b531437317ce6ef698a36c5f1b5c06b28db40729879e73758ec4fd28dba0d02980cf4d0e3615f80ea7ab5ab89f49564c91e6cb57151ce570d68f34992a1b9ed2c33625946ca84e0956b3398229e962eac7658ecc4b28dd10360ca3405253989ad649fa51c7a724fd8469150870e569824fd26f38e43628cd7b4a51c9132494a372cbdcdaaf938d86f530617c94738dae86c58236f6983bb4ad8ba2e728d9ff649fbda45cf0714dfe4fd8ffa51b7b4c10b63e0b40b9d85f1cacffa81d1e9c813617c72b60d9bc526e83d5a1a04c1ed306b4282c33489a4dcdfeba2a86420f4f5b46060fa5eb62ebda524af6998ba18b8c0c1f4bd65eb8d8b4605cda8cb5a8bda5ed32c74bd63cd6e1ed23d36a6c7ab698c605cda9478b129253e3b59cb9f1cdca1ab4260b63482bd983682349b9ca4e56aa1bfe41ea4445b60834a3b60c47806af75041871527ec2f901ac5f6a7c145489bda40461ad49b9bfd745b19439bb06e49facd5046d5f9eae93f591b1758bb3da504692560dc1dd2272d83d385b604f9acf18759fb9bd24a3d3 (by decide +kernel)

private theorem part84 : Excludes 0x24001000000000000000000000000000000 0xc3aeaa8a484800200000000000000000000 :=
  splitAt 1 113 0xc3aeaa8a484800200000000000000000000 part86 part85 (by decide +kernel)

private theorem part82 : Excludes 0x24001000000000000000000000000000000 0xc3aea28a484800200000000000000000000 :=
  splitAt 1 119 0xc3aea28a484800200000000000000000000 part84 part83 (by decide +kernel)

private theorem part80 : Excludes 0x24001000000000000000000000000000000 0xc3ae828a484800200000000000000000000 :=
  splitAt 1 121 0xc3ae828a484800200000000000000000000 part82 part81 (by decide +kernel)

private theorem part78 : Excludes 0x24001000000000000000000000000000000 0xc3ae8282484800200000000000000000000 :=
  splitAt 1 111 0xc3ae8282484800200000000000000000000 part80 part79 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part89 : Excludes 0xc001010000000000000000000000000000 0xf3bfa30a7a1860382020200000000000000 :=
  finishCode 25 0x16c560e6313e43c6503771c4550a4a1e37b4cc2f71d8f8ded320758b6f5b530de30f3d03e943486ab9187907af694069cc58632bfd40680d05aa0766b09cc4a42d61485340f1b93e59d97ed05b2d5d34551601f1a50e5a88216406abe501b316cde2b0f9ed23cd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part91 : Excludes 0x4041010000000000000000000000000000 0xabd88fc2d2ca4a282820200000000000000 :=
  finishCode 15 0x1bc8819c7907ee731907a7090f79cc66614c39087de48697ed28682d83eeb2d8e0a5c70f7abf6482b0ad2523df0f7bc881390667334a1c83d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part93 : Excludes 0x4001011000000000000000000000000000 0xabbcab46523840682a20222200000000000 :=
  finishCode 33 0x6f1f4731c45d03d61f367134517c1ce6afaccc7b6a358df64d19eb25c7378890e609a4a4f768dd7b8bda4de3042106fb580c6f1281a4358ba80d624c3a37b4940e5b174281b48b0d9866379093bd8505a8332f5bdde416a0cda8f050d01ab01580c3cd378a00cdf694387fe5036b174392c803399bb07175520db41cd01ab01596c61e83da03630f0464b7e931406b1767b4a0cc0a6055 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part94 : Excludes 0x4001010000000000000000000000000000 0xab9c8303520840282020200000000000000 :=
  finishCode 131 0x6312088127ef2450b6388c807dca2ef698e42725292cf6960ab06e08512cc2f2819c2564b312585e3ff281a4ee5879bece121f7771c45703deb01cc52631bedeb33d8585e6f192631bece123db8fe259d3719cc4e42f83587318de290d4a18ffd21b250c7ef1cc528707ce208a1d879208290ac0e6140cdf6709512cc2f378cb602fe5ab9f5d21a5037a1881e6c8d7261a035046803a30b2c0417e697919a1ab05a940dac5712531bc4e623f757fc9291ffc08f77946a90d419a4a4e62b4f98929431ffcd63c8e22f01ef1edc1b105f9cc582f357c7b673350d9c26494c3ff059cd47521a8d4de2731731280f9a0f641f8f7d2867ff85ae83f494ae88a3105eb515cf57096a0b50668cd81464c771dac80bf962ad2b16ba0b43763e383ecd5746bb4d5eeeb6395e155931da6b2c05c770433094218e41b7d8837dae083d16bc80d498bda6839a035657393da66091771cc880fc73d64de29430fb9cc563307cd2866f18a4ab55521c731881e46f1cc6203eec338e669fd2929cce39893e65aac5911f18a44e66f69731401bccb2f4989cc549324c49e6b439a42a49591a8a9311f1c5cb46ecf6b619ac05632f23489a2803e3721eb2f773f0cc336a29ccc3073dd673187cd6aa7335e149b1eec9f27310f9bddded746148fe1f360ab174e66a499eae1f7600e63286c9e6a437bbc5ef791abf07cca2ed5f89f31a9ce621f3 (by decide +kernel)

private theorem part92 : Excludes 0x4001010000000000000000000000000000 0xab9c8302520840282020200000000000000 :=
  splitAt 1 108 0xab9c8302520840282020200000000000000 part94 part93 (by decide +kernel)

private theorem part90 : Excludes 0x4001010000000000000000000000000000 0xab988302520840282020200000000000000 :=
  splitAt 1 126 0xab988302520840282020200000000000000 part92 part91 (by decide +kernel)

private theorem part88 : Excludes 0x4001010000000000000000000000000000 0xa3988302520840282020200000000000000 :=
  splitAt 1 135 0xa3988302520840282020200000000000000 part90 part89 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part97 : Excludes 0xc005000000000000000000000000000000 0xf3bfa63e61980aa00000000000000000000 :=
  finishCode 31 0xe8328ce14361769485ac2869c6e7aca045c7a629315a43638db9bd68a9296c19c6213039b946c8cf2d5dc7ab1971dac5502271b067c2ed541823005d3f270d066a0c56ae611940eb02601c58c22f57905eb570e2ad166805da6c1c6ce6ec5d9cd65a1736b9560b5c1c56aeb4199461bce535a09c6cc0e1e3314af04ab852a18b71db9b45da61138dce6b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part99 : Excludes 0x4005080000000000000000000000000000 0xbbffa61f50980ab12840000000000000000 :=
  finishCode 69 0x7e2d0ee24fdc474228620a42d2146d6038d9ca4fc33d6e3029f94f4b8edcda70912ac24171db9b56af18183bcf71308a81e71dad5cdff1c6ce371bc65ab9c34a2329256ae5218a1d0561ac290940c55b41a4bd646d836ac04fae6fb5aba7f63ebbda42f2f6991927d75a4a3358b25eb290ac8d6020e3eb8ab4c26f698bf25eb387caf12f5ac7549ae82b0e2290e524c1ee7b49f5dece4d18349bece127d7832f388ca3b8d6399e3949344e125172fd987d846913438da93646bac75ed23db7bbc6fb7b4949637dbda4dfee55671ed2e8134683ba8d4df65255801272c760f62bb27ec1ee26185e60ee8c97acc5179dc69184120c4631b6b8ed6571817b4946ce1271b394ba0c83dde834b9ac38af69390946e62ecf6915da7e67b48495ee26ff302a796390bda432251b460df670951cc179049d07b4fe930ce36f69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part100 : Excludes 0x4005000000000000000000000000000000 0xab99a69e40880aa00000000000000000000 :=
  finishCode 135 0x220771ac672041ffb081ef58190580c93149f97ad686b1d5a89c5c5dae81bfd23f1818b8e70958bc70d921a2ed74160614c8fb4fea4fcdda70939127e15d8e425eb7b4aa08cd8b422ad58bad5e0d32325cd6b013ebb4dc55a8224fd1c7bbcb5747d8ab51f70d256aef7769bc4c3599b9ad901dac52549f875cc5262b292c613811f47403eefc1c25acb1c8527e8319c7b067daa25df15da4fd94640a06b579276b2d390a0c457f029d65ab038ee7368284e66d82d5d07f3da568a7219656fa38f6314984d063145d686c1f449fb089838e63f894956929437b49bfce36e20aee7379cdc3eeba3da662eabf639ba47ded2e83da5908a038a4c398bae597ac946d82f3dc58929fd876a51b0fbc2bb0e2c2bb28db174a0714339043e82ed37dcc5d0fbc1ee60cb17546a19f2819cde053940d8bb395c1461f7378cf692e39c6d9c8a1d00fbad893192862ed0d5bda4a067e24367b497ad2633da53fa6fb176c9437b497ad907b8ca35735bda45da9a30be83dbda56a23db498c5cf83dbda53fb17aca061f77e1c46718028da9265abbdd527e5212f5c0cd49fad8d6328cc145d1c3908f8e62d966d49ae67944ac5b7b4a4fe7bbcc5d14a827ded272149fb17649f945c7c724fdc87bbc7212f5a4fce127ff905eb572f5a4fd9856120690e42b00334f023bcf6904fb4c4e129a0a3e1f1bdde3ffc4a57b48f0dee228f4f7c09f7adc03f5a49ccc19a7ff85da0cd3ffc82f6703e6d23580c38bd60cd3f1ca339b585e2db2efa4fded341cd8ba3e316d9bee5158b6d44b1ccc7c693f (by decide +kernel)

private theorem part98 : Excludes 0x4005000000000000000000000000000000 0xab99a61e40880aa00000000000000000000 :=
  splitAt 1 115 0xab99a61e40880aa00000000000000000000 part100 part99 (by decide +kernel)

private theorem part96 : Excludes 0x4005000000000000000000000000000000 0xa399a61e40880aa00000000000000000000 :=
  splitAt 1 135 0xa399a61e40880aa00000000000000000000 part98 part97 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part103 : Excludes 0x14001000800000000000000000000000000 0xebbec672513c00340b00080040000000000 :=
  finishCode 67 0x378f2398c407cd6869078616cc45551a673174dc62db419b4ce15d9b8c16a81d550b873125046b3549fa51d2222db3a0df724fd85ec5f3fea8fe0e29bed892c2f49fac09a28fcfe335347c67f19acef757bac7bb6b28f8cbd71eed646c5d466b38ac2684c794729374a3b10b439be4919ff549a9e949f8715cab135549a9e93f0c8cd49fbda5246d22685eb466c0837b49c3588a3e3488cf693fec9111f1cf59263a4fd88691684a1c83362ec1dc57670d39ba6893b902671d3a11af41cd6464d54a1d041bfd21b203505ae53a0e2b4f73787155438697ad19a4679aa238f7ba868d21b130d276f2260aa233e046a44c7c62db4a3ad09136c230f0ea5cc6c2d0e2a4fd837245c35ad83da68c39bec542d6526ab0667bb85144c2f69838c8cf4118b6d2269624fdaa31b7d2864d55aabdae62db0749866df (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part105 : Excludes 0x4001080800000000000000000000000000 0xb3cec61e509c02310b40484040000000000 :=
  finishCode 107 0x1e48a158741947109cab4248d28eb0fa0da71b40689e68c0a7e4c0ac42d0823838a80d3502c30145eb6b192dca04cdf68c3956041c61d5f24c38e1b130d9c430dff39aca367fd491a51cfc348ce3949ba4fded324dcffac41ca649f9ff588b38eded2b0d49fb38a4251d604069d87a2d441234604bd6b1d50ba04d4732c7502717e4543236c8da49f8349f5debb130e0f6c4546dac74bd6ba24fe3fea08dcaf41cc0d605b395a4fcffae2360e81f85217bac7fd5039bfd27f1818d8ab234889ff5741f1c5eb3ddcf6962da444c0ab42508c1bfd01b0779eee9117b4ad247c72c75ed2d241b4dfe9dd9ed272b5a4c9db7b4c60590570c0ab1da0ef18783d8f8ded2e3ba30e5eba3029db8c3b8ec7c6a63206ff350bf27d78df67e1f5e7b4ac742c25eb69dc8cd2f5d1815a8bda4b3b311630293f836b88ce2b09a2c8e1e6a4fc9a25ed524a4dd28e863206ed49198164fcad3d1af38e5ac29f97b4cb43b8f69876293f38d9bfcfc6afcb232f6b13540e93f59ccd3d2e3cd3346bc605eb65ed37dbda47b686270d618f765ed735ace569eb423be37d9ca561a93f0cbcb0d7358f365919344ec37f9bed1826197e6729971e0f6b5172aa35e268b585cab2d0d3b8c0a82d37fa4fdc44d0c0b316cbd734ed40f18772aa924c0a1818986185 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part107 : Excludes 0x4201000800000000000000000000000000 0xfb9dc6bb409c46300310080040000000000 :=
  finishCode 41 0x7e3c893f6216028dac7605396bc9fa2ed928e9478a42c42c0d0288639b86f5287395650d9cdcdfe83369ac6ff791d065168b145ca42ce3209378bc2923176a49628db20b026070d8762b0d919e1c56115ef2d145773da53bac439b625c8a551dee6f147c8ef821904a3c1bd71d8925ed283d1e6a4945da4fd9cde7374a3a494e6f310f59a0eee552dc9cdcdfe83d0de9bfe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part109 : Excludes 0x4001001800000000000000000000000000 0xb3aceed2403c00700b002803c0000000000 :=
  finishCode 75 0x821f067228176be8ca3889a07dc9cb0f6ce3a50d968620df741dcdfe81d4169bfe62fcf69395cc5f0fbb284e58bd65032f5c3cd619b1755871134480c9373820f746058bea0d268c61d46b07b9ed31875219bed685301471c347471bee0e7460522e5c7486c3db7b4971ce1b144388407dd946abc5eb7b49394a1a8c1b03cd695cd5f4eea335cc2c5d466cb238c0cc33477a775672041286c0316b08104bd6f694c1601abc0717369ff4e524e5302ad09dd9ed21358c0b0751de71b7b4c5891f19435345d1645b07c65bba302f770cf9cae30331742ce7fd83e9ff67b495ece6e8337acb9b5eee285a0f69174669234e3af6972b8e3e39b801dca29177b4bd65687d16038dad8605586c0a971eb4b569e38b84ae1ad1e6d181591971ded272b461ed30f34df72cd5aaf243411e5c77b4be8f6998be4a7731b17528e8330fb94362e7a4dd680fb940d8bb173ce6ef6982fe943 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part110 : Excludes 0x4001000800000000000000000000000000 0xb3acc693401c00300300080040000000000 :=
  finishCode 109 0x328de1cc6287920067147f358d63a7c348fa894fe25031769495685a2940d06727743eeb3f38d821e0fbacfda62ce3e82ed7aec3cd489ac4d4423e3272d0e2776368c61d69e4e50fba4fd6c243cb032fc9bcce3a4e583dc5ad836a774bf2fa348b61c6d9038eb94e1d8b57cbf2a359cde81392527e1bfd27f3dd5ca690d71ca92528738e503a90d6419834038a5e1925293b969e6d72f0c4f349dc6d74817049fb20ce1fc56731adc5da90d838afa283637da51cdfe911928f1b7d90482c5e1837a81ce362ed6abc69d521a8d4dc694381063b136f8bb527f0e3187e3c893f7720ef06e4b8ea2f38d87de28801caf17ad26ef7528d8bb6176c7378bd66ff79228771740fba10b031159037d828519b3da5696f698a36c331e6c8cd591c2ed4eebda519b3da56462ed72bc2497b4a4dca36c4556190461ee3460561ae6b7b4a774dfe9473028f35504a3ba01bd4eecb4f3e0c1c49870aecf7741ecdc6f691e6c6fb49b8bb63f89b8ded2b2337fbe8841cdcdfee6d894ed2b1c5caf3737c1dd836b190dec1f519af69051c3a9791881769bee28da48e386a81d19a6fb4c145f0ea4dfe4df837a7376119c395c51b176b20a607163031bc5caab45098ce597b4b9463025ad53033f3da58bab45737b1167b4c604ffaf698ffa51b (by decide +kernel)

private theorem part108 : Excludes 0x4001000800000000000000000000000000 0xb3acc692401c00300300080040000000000 :=
  splitAt 1 108 0xb3acc692401c00300300080040000000000 part110 part109 (by decide +kernel)

private theorem part106 : Excludes 0x4001000800000000000000000000000000 0xb38cc692401c00300300080040000000000 :=
  splitAt 1 129 0xb38cc692401c00300300080040000000000 part108 part107 (by decide +kernel)

private theorem part104 : Excludes 0x4001000800000000000000000000000000 0xb38cc612401c00300300080040000000000 :=
  splitAt 1 115 0xb38cc612401c00300300080040000000000 part106 part105 (by decide +kernel)

private theorem part102 : Excludes 0x4001000800000000000000000000000000 0xa38cc612401c00300300080040000000000 :=
  splitAt 1 136 0xa38cc612401c00300300080040000000000 part104 part103 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part112 : Excludes 0x4001000040000000000000000000000000 0xe388c63ac00881200408800200008000000 :=
  finishCode 133 0x10e3e9023b8e63181f37c220571781f7b0ae589a4fce6271d927e0cf8e3a93f741a47e019e83f8e3a93f16bc83f640ffb24fd01e831261c80d3ff8b2d28682d38ec0cf838e3ef62140f18440467313799c75a5b3dcce1a9e72f19845a4621e4387b611024fe39b946ca2ea628fe39ba4fe416cb578c3b9bcd8a9db31594362039bab0c41521c4a9503ce6f8c3c1b672b92a4377103e0e4596aee5130898ade4651222d3596ae5eb290a4fe386b16e6a39c3528531682b41f8658bb984e1aac12a6263b59e58b918d3de93f934691c93f731a32de449fc70d491931d6532b093f58bcb154fc9bfd24693726396f65ab8e9cc22911651f880180630a2e8138e62a2b49fa896409a4fe272c7311f19f3e398bf0c640093f7baca07176a4dca365c7919a8316214871ff60fa5ed27e8ac64f3805d26ee821883f04fc3af60cc2c32efce624fdc730bb501e51b1f79fce4a39485f86c19c7917849f948543724945da9e99c9e0cf4a1ca1b1fb833d287145c6f724945da50d671781ffa4965ab9cc475f20bdb0596c83f398977e771884d1e43799c3d780f1946e7bb8b6cc22b43a0fa7bb503ad0e308a79cc3e4f379200176c51b286b3873794862ed0f193966413039bca21521984562b1cdcc3e0cf9cdeca13960f198ad28f23bd3ce70d308ba0923900251b2908f8e466a8ad0464fd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part114 : Excludes 0xc001000002000000000000000000000000 0xf3bfe31be41814204001c06000800001000 :=
  finishCode 27 0x5b1d8620a06e4210bc1ff5904b0a366110e2bd5e72ca07deaf2c05eeee5171ec6164f4c6041425b958e946e3032c74a36e3da3026b14f4b965ed261128d871503e9e9802a29503796e58be81f28da98e627c6240b17d4420a14189ffd9c711c77395d246a82c3e8c0aced3e2b173f0a7c67b4c61d6031815a8b13e7b4c61e47798453e24f992472044a36521 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part115 : Excludes 0x4001000002000000000000000000000000 0xbb98e213c40804204001402000800001000 :=
  finishCode 139 0x410e43a0b03207096f0e66e64091407bc58b2c8c196517591c0cb2f09cc4c572045ed293f2f0c4f9362c93f608987dd87319462103b1cc4a4a7318a370ef403a0cd8c2c937009828403a3cd595a7e562e521730d8b283527e4f90fbbdd61d6a4dc9f2903f0c83e872176055b27c4e62f69281a4fcc3e4d187fed3d8a2e8ef40fa7c47fee22a8e624d5940fbc4f92929cc526f24fd27f27e49f23ff819a9f927c97ae7b491b49f273149fbda60678ffd226721731dc5b0a4b38fd26e1ef1ffb48ae033daa341f5abe5d32f59cc5946afc6c5580a04d1f707da30246746db5950221f7926aca0336398948419b450e238ee72ba9260fa93728d9485945d0a068d7985ab01409ac063f0c7d74a3cf71268c50b42e8ca2a8e2208d07ade24fe37483149d324fd6a327f4dd293f811dc71127f187cc521f76f103aa2b9c7af75398b115472d2b96a293f27ecc4b83fabdcdd2731472cf696b28aec7fe81d2a07ff3da4ffa7e3f03ff89324fd49faf0611877a1f79c8ed4b1ffb54630f1ba49d21f7406ce63b8e213f6309b18bc130e8399f7c7fe73158ec3ff398c70f4f8a3edcb2b57839abfe7b0abdcdd2813398ac0e230a60a3acad4729474feca397accb574a3a80dcc49fc6290f7ad3e72c98ad28ec62d0e624fddc8a07ff022b81f72f5c731608c7e3408ac05d0517c5216b2c8db7ae91fd246a1b9822629376a496288a86ca42f5b8c5651b506a925246e62d8731376c7e313c93e507e52590226c59eeeb17524a7e4a429237409e718a4a4a6ed398ce224fe29293e43ee4f987fe503 (by decide +kernel)

private theorem part113 : Excludes 0x4001000000000000000000000000000000 0xa388c212c40800200000000000000000000 :=
  splitAt 4753 135 0xb398e213c40804204001402000800001000 part115 part114 (by decide +kernel)

private theorem part111 : Excludes 0x4001000000000000000000000000000000 0xa388c212c00800200000000000000000000 :=
  splitAt 1 102 0xa388c212c00800200000000000000000000 part113 part112 (by decide +kernel)

private theorem part101 : Excludes 0x4001000000000000000000000000000000 0xa388c212400800200000000000000000000 :=
  splitAt 1 107 0xa388c212400800200000000000000000000 part111 part102 (by decide +kernel)

private theorem part95 : Excludes 0x4001000000000000000000000000000000 0xa3888212400800200000000000000000000 :=
  splitAt 1 122 0xa3888212400800200000000000000000000 part101 part96 (by decide +kernel)

private theorem part87 : Excludes 0x4001000000000000000000000000000000 0xa3888202400800200000000000000000000 :=
  splitAt 1 112 0xa3888202400800200000000000000000000 part95 part88 (by decide +kernel)

private theorem part77 : Excludes 0x4001000000000000000000000000000000 0x83888202400800200000000000000000000 :=
  splitAt 1 137 0x83888202400800200000000000000000000 part87 part78 (by decide +kernel)

private theorem part59 : Excludes 0x4001000000000000000000000000000000 0x83888002400800200000000000000000000 :=
  splitAt 1 117 0x83888002400800200000000000000000000 part77 part60 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part119 : Excludes 0xc200010000000000000000000000000000 0xf397b4610a08e0184000200000000000000 :=
  finishCode 83 0x3a0de350c61484a4ac358bf61d30eba30905922e82393e722b56d8265d704fce45378b10c6348ee2881d75d11c288b9b6046c60c59aa03541633277e307071166c60e4c11c4b08cb3da4352b2f5a282354071bc6306d21597d1837b497341330713f8c1c6262b4863072cfca22f69288c08d8fde5fb41f9bc6361a895ed25115103aeba0f0e04db0be04c92ee2eb97ed002c43005075201621b1907a8239c7ac497b4a08e7b4a0f5845114c41036609b8bf6e599ed2a213f9826da9b0975cc66c362daccd22ed5b57ec5cf48ba8d62e6bda54c771747309fa8e1bc63f6c61d2623cf2fdb701d73efd183486827d2860af8926d4f416cd4238a217ed42f28fcde302fded2d4f9ed29432e6ca116a7bda43ae5fb27ecf43a8aa2108e1ff505af69942e5cf8556d4f7b4875da9f285ded21d741e86d605fb4d5eeed67406ae8b1181760bda30ed4f592cd33 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part121 : Excludes 0xc000011000000000000000000000000000 0xd337bb041aa060781800222200000000000 :=
  finishCode 59 0x20c762087a190075a288c2416494a00d47aa3b5d144ef698fdeb2728186dd1bb3da562ed5b261af8e22b0e599cd6a2916bc6168c39b153b6f6959397ed740dbca29058bda6696a8a5a5b24ed452ac356e4f5bdacf765030d3c9314617c51dbf8ac28a43c6b51857eb3b8162f696a9cd5b1f1a8a4bf6d5b87c61e3514b54e838930da8ed5b0e9878dc46d17c601a8690a1ab8078d61f250cf77038ded2d4f96760e35a8cd5b071878c7c7038e6005ae0e3517c6f152196ee058c36b2e7a76dab6c471e7940dbc3b09f21e36adc4c360ba89d47b356cec419cd5b509a8ec5af34b5066a3d45105a0e54f5ca27419b56e6aa86dd4522d1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part122 : Excludes 0xc000010000000000000000000000000000 0xd337b0010a0060180000200000000000000 :=
  finishCode 125 0xf4398bc4187316a1d8512c0eb51582c4a065255614c27ca10c8292436b20fd03b20cd1b21b5945e1e341f95f651e890c34a83d475b20d002c662fc1fd47a0bf83fc823410a50e599ac1dc4075a885116a4c7e383d91b5406c5d6ada376232b11d4071b0da92d616a01cac83089402fd5ff307507a81d419c4c5140c8236a4b56c36ac3389bf166e306f7715c8f8cd86d5b7f1d8751b407283ac5b31fcd046f6189be39b378b88e8310a278bf7187283949570290c61e513a045c9f461d44ea295f12c2fdb53e5a99bc479e6f1960a4fd470c61e378b93e83f81cd03eea388ba078d4774605666f694949f8d0460999ed29297418c8c0c4f960da93cfff07f92864f9406cb478c0ca3d62fa07d07ee2350c4241628394947c724a4a427f19ed23e364036f20fd49ec1b93de6f1831d0711d4290a980eb620b9b2d5cbf65071f1d18561aa93cbf6b575abc0bd3b188527c61e1e6941dcd7461c366b5146eb98e3ee85e4a0ea2951e940e7bbc4fd41683add0416a28ae20cd705414433da41420a7058cf5d6ada90dab72885486b45949ee202ee510a90c5a2d23081299eea06705f86ddebb391c16306c5ec3137c5b2833741d86a1dc290949498741ed3e6f691f1a45c3c63e39a4771ac378c8312ebbda5ab63e30f1aa0760b65477293ded328f54773da583650748a8f8e16cb56e51eb554a22929947a1db1e7a0bd47b293c7a61e3 (by decide +kernel)

private theorem part120 : Excludes 0xc000010000000000000000000000000000 0xd337b0000a0060180000200000000000000 :=
  splitAt 1 108 0xd337b0000a0060180000200000000000000 part122 part121 (by decide +kernel)

private theorem part118 : Excludes 0xc000010000000000000000000000000000 0xd317b0000a0060180000200000000000000 :=
  splitAt 1 129 0xd317b0000a0060180000200000000000000 part120 part119 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part124 : Excludes 0xc000000800000000000000000000000000 0xd307b510005000180600000040000000000 :=
  finishCode 157 0xee400f43a8fe409042500e5075878616c9fb4ffad230906d91e2f77009c1cce5283339bb2090316cca4f510ce2078672aa8842bb1755c4650a220e3524cf694a19435ca339b4e1aa1b39bb603e18e625038e3ace0385b4292b3080d4910661e17b4ca494eece5526fce57728c1b54928333f6c1e1387c8333f6945dc8731c46a01bad81cc628387856804bcc5d419a8ed47a605924ab3b599bda4d8b3da549e9012839cc5b06a0e62b338a061e1540b73237e0de7f13799c7435728f64a1b607fd51ece3d599bda4e36923292943637fa8edb038dca3d398ad8f698e02a3b9cde5f9711a06f19c0ecc51b292945e0ec8bb628397343c20af8a0e51739bc1d96a1b06716028d94963033954e6e1c91f0a8f669c9734e56b61cae0e4945da05813fb3da430e9430e4981574411385a9a88939736cb035a2c6056223ab588c38b9ed292171db94564f0d8e481c604e36e555a2c9398219c5805dac5b9ed2a3b4a19815207281c91a17f7b4a8ed945b0e3b143574527cf6949c930e72aa45d85b3da5402e5151dad8f699676c3139bb9ac59e50d479caf97b5a7e5ed2b255d198512042888b34f059122aa3d949ee59960ac1b617b116501ad1648ad07362faca547651116cbda549f120d85e72b527c90372a9cada05b1b8387b30e63600dd481cf678c08b649ca1d5262cd82d01d5500ca4f2d6ac3ce6e903928af67272a7fe6aa83765d01bef699cde2d9506a5149cb1815cc06dc0df5e130302c947587c9454928755304fcc9015879f84e36a435d2303243decea3d50d8dde8c0acece03037d60398c1e12839445e828dab0aa249648a9cc528e763da68c1b17586291346ccf697bab1767b4b584e62b118fa6d21501b5858922d9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part127 : Excludes 0xc004400000000000000000000000000000 0xd3bf907e878188888000000000000000000 :=
  finishCode 35 0x360e63a09834883f6b2cb3f40f83243c6d4281e5218f3e064d18140f8f3d05ebe3381e3818e3cf5d034724edace2d9500c93b6a6bda5a6ad5b6a6c9451e9b56c18ed2338d41944f18148186ec9f20c55d1684a2b5365278b65ab7356e0dea93e7b4a8d49f2be3384f99ed2d5b0f18f3d6469ac0ad6ad97bda860acb116ad9fbd272b53494a50d6a73d6dab67ef690c7ef27ca4c43c6d5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part129 : Excludes 0xc004001000000000000000000000000000 0xd3b7bebe81a408603800800200000000000 :=
  finishCode 73 0x7f19c691a80f1c486e0bb53c2a16c6ada982cf98823cf7b4cc494c160578cd51727b1658673da5a5f1eed242f6971eb9ad6c7bbc5bb490ad4479ed658b76e4f5a8acf6727b8f4784c076ae6b71eb54683db0cd86ef7780eef69619c1ecb630b3dc9eb20b9d1883cc1953d5b055ab6b5157ca85549eba289cd8b24ccf730ed6728a28d5b5a8c7df62596ee30324cda85b13c2868b9d61f3ddd6767b91588f3d67b393dcb2a0184fad5b5249875a9ef6959db946057bda479eb516adb50b030061130e8e87b9876a1531389cadab6b154e0f7334b582af69499a89e51db9463031ac549ea153ddb40b42c872b65182b41ec4a24c36ad98ad49f3054956d5b982a90d8a1ac5b59398adab6f698a1ab4169174395ac9e59eb56e37fcb3d6adb50ca14361f1b56cc3a62b450c22a279476d5b964ef6969b9ca563b30dd692e59619a4cdab6607 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part131 : Excludes 0xc004100000000000000000000000000000 0xd3df9c3fa1e018208200000000000000000 :=
  finishCode 35 0x340b4298b61c6c7174604f56b1d0dd93f4e6ece2a00c372ace6b481a5163021b96add18127998760deb50cc3281bd8c3ad67062ae8c0398921625c2ed58ece59727b12d1fb1844c2306f56a3356cc2261d541ab724e4e56b259a9eb1d274c94327e9874186ca3a8ce2981d730fc4f32ddc62950bcd4f49098a4b7661f8c562ed8e025af (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part133 : Excludes 0xc004000400000000000000000000000000 0xd39797ff81a848060980080008000000000 :=
  finishCode 43 0x771a45416c68194395b3882f89429ef6adb4843868210eba93e50aa7bda42927410981c95735547c22d9600c0f01d4b9a82f4188b345b2c4306e0e39c045333da5ab6127095ae0c020453fb0494fa6b277ba9735c76afd303874c5b2a29a0f63e3303874c3af2981d35b06c7131542a511583accc79e81f6adcb3d6199445ed33125ab6b075c150410c83f1f08f3e37fac1ca225119ab6f595788f3cdfeb6298b0258d2203d05e1b796a6d21371b56c59a6e39a42d3b621c9f460d662e6d62f870dab65111f1cd5b16cb94e0e18b65ab6d2f85b28216ad8f8e59eb56c59a811 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part134 : Excludes 0xc004000000000000000000000000000000 0xd397953fc18008000000000000000000000 :=
  finishCode 129 0x1e467194750a42525771023074c1a63e385db2e8a8146dcc4c1d4418a0447c3034dc8b3125cc6c03a8a2985b28d958bad5d6c371453289e0f22ed624b11dcb324cd44e2ed6188bb683cb0c6837b11c59e2ed4516af185a0f261151ea8edc9f1b0e0f23e1514b987634881f624ca2951d834e30b2c3deea5b11739b16479c61459ef697ba834c5da982c0a438c0ce637ba9845cc70e9e7ba9ad4d62a1b8c0965da47316c069c60e4189ee63022ed395854e481c605aa6811581881f0acb671e9cdc392e6b806b1815abac666adb93ce563e19cc891305801a718a50426115b01a64b99ab707b315a0850625cd949ec5b408b280d3490c28928bb04d8b661d315a30b61f8961c0505f4605cd701a5476f5b417ce511da9cadcd741e542a6b1944e3e18a2e0d3580a2ee6b96ae1c91f0b9465ab9cada46819865168061ac061d81a21c962dc8110689cad6072d15ab60d1601c8751600688b65c771cde302b1572cbda47c2e4f8e56b157b4b9b64f2a485aa672b1f082a627986e47c2ee460e71eb9acc228210689cddab73955a5ad61410bb861f81a273758170279b0d62f6ac4505ec5b91e25ed407b9ae6b0a0bdab61bb729a98b62e09820bd487304437e83160204596ca1b5a097364a18b34c56701943713cc37ece41ce5aaa49d4364f3601aa341c476a927589cf771daba8c01f4e7b49a8528ab41493ad5e24735c6117b498a5486999abe1da81d67bb9c05cd728ecc2262b6b1a9080f8dc64f31f097b4c22be02a6315a796 (by decide +kernel)

private theorem part132 : Excludes 0xc004000000000000000000000000000000 0xd397953f818008000000000000000000000 :=
  splitAt 1 106 0xd397953f818008000000000000000000000 part134 part133 (by decide +kernel)

private theorem part130 : Excludes 0xc004000000000000000000000000000000 0xd397943f818008000000000000000000000 :=
  splitAt 1 116 0xd397943f818008000000000000000000000 part132 part131 (by decide +kernel)

private theorem part128 : Excludes 0xc004000000000000000000000000000000 0xd397943e818008000000000000000000000 :=
  splitAt 1 108 0xd397943e818008000000000000000000000 part130 part129 (by decide +kernel)

private theorem part126 : Excludes 0xc004000000000000000000000000000000 0xd397903e818008000000000000000000000 :=
  splitAt 1 118 0xd397903e818008000000000000000000000 part128 part127 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part137 : Excludes 0x2c000800000000000000000000000000000 0xd3ffd0559a1600040000000000000000000 :=
  finishCode 35 0x73140710e62f23b06c585729476ad9444a4ad42b00cb2dccd5b51aa81e41fb56d6930f85892880f850430ae5ab68139aca83f521b56e281a0fc7c2d4388ec461e58eb56d1e22e727e94859056018ea0d9ed24f90d3cd215a8bda5ab61c3819694583c207f8a225cf1e9a51da42f2388ec356e478a0b49fa52151128f13e528f28d504683d281c1bb8f72a21279a04c18282d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part139 : Excludes 0x2c080000000000000000000000000000000 0xd3f7df16840000000000000000000000000 :=
  finishCode 49 0xe6390f2388d80375940f08f4e398a8d6599b12d3daa29651745a03663d3907aa21900690185ae2c9947ac820be35aa0843c2b43009a0b64a071ff56a3181947323f4e6e80d839c7ff398b4072b83c2a019452c4b41e8b65b0501c4398bc81d385ae525387c3e19a062107f06dce6e1b78e1a70183a670d8e6e1d3711946c12472924a0e1e1290ad81b38a1ac2d905ac418c0c947524a4cc3c27e19266503 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part140 : Excludes 0x2c000000000000000000000000000000000 0xd3ffd810800000000000000000000000000 :=
  finishCode 143 0x791d87301d6bc2d8da3782e7681d0526ca136a6a07ce621e15414272844fbad5b1e69c3ce6e9839b68c281e51e2d35394a8f66ada84d9460142f1c0415a73128b9f7e6999cc5427207c0ea7dda0fa06b40f81d4e621e1740a2f1cc507e6ff9d0292c7310f0a8f652786f4e62e82d8961d8de078507e81f0dfc72969bc6b151ab4de8c29ac63021b3394a0fc3c2de146e0f0a85506252150dc1e1274ca431f094843c2d02d871b1e7c737736c0c1736ca1362c93f5c8594c8f1509a8a561e92328d945c3c29259426a3b283b98d8378ae348731611d45d03c69a240e4118f4d2727f3416cf6969acf69264a98861f7683eacfc79e82f3eed07d59f86fd07ece3536064b53669ac4f97b4878d448c0cd370d1a07d07ed5b69bc8217b4b20a822083f6810421c19ab63e1416c8eb372c4f91f0a43da86709f2b1d940e7dd41e82c5ab741fd066ce28f6599bdd54261e3514c24d01cb4dd580f1a07627cc61e83fb56d02681d398cde0f3e6ad878d74409c0b741e8b5e492b56dd04c188591bc16b82be509870505a4f92dcd18105bb53415a0b7941a3e149bc92327cac8a6132669a86cc3762d76218673dd415af759a9af599ac2f690e0a51416ec802b616ca0b50460b78c3cf69416a0cd6c731d86f1a04d03c31c74e568319ab60d18379cdc3c2bc280962084e628d9905eb178e02a015ab82a51fb071d28a82f4efc9f383c27315007c320fce62a620be41fae86a20866b09b941967f316cc6b59042d5b509850c096d616607c33da417a4f338e878437730449e673738eb281e150dc82d3988b66 (by decide +kernel)

private theorem part138 : Excludes 0x2c000000000000000000000000000000000 0xd3f7d810800000000000000000000000000 :=
  splitAt 1 127 0xd3f7d810800000000000000000000000000 part140 part139 (by decide +kernel)

private theorem part136 : Excludes 0x2c000000000000000000000000000000000 0xd3f7d010800000000000000000000000000 :=
  splitAt 1 119 0xd3f7d010800000000000000000000000000 part138 part137 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part143 : Excludes 0xc080001000000000000000000000000000 0xf3e7ff1684a020e01810000200000000000 :=
  finishCode 39 0xe2378e63201d306e9c765108f8cc3a8ff9ab63e3272984e286987cc23181dbc5a188690167460436e72939b9b1672c9b0d42a0b16ad9ff57437faf89c06dcd8716ed206d21401c8039a425035abc9438c0a40da42d42609314a1b0de6b2b13ca073da477eae2e8b479ab61b7690c7e38d868e938eb0dcec6a16a2981fbe59297e58373da498ab254a1bdae3f7ac953c04dc1b33f9c0a3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part144 : Excludes 0xc080000000000000000000000000000000 0xf387dd17840000000000000000000000000 :=
  finishCode 159 0xe6390ea3c8de3200dd6a2006503b21e140fc82f281a456386af098075503f20f568e5f98c0c83d4179cc530394c81f41fa07e417a58a82086395a0bccc40fb58e72ca9363027318d86a256adb48651fac74e628215e1945d0e62c03502d93ffcf69619a47c9caa398e1af69942e11b474a7ace6e6c3416930e8c0a40dab6ba30054310d5b622c7fd5a3ad4d8bb24cda43ffd181490c1fe587c60da8eb47051b52d63b18191fa7296adad1cb9b352d6a31816adb28737963a91f386c7296a1780f0a98611314a8067b8b595ed25074f6cd657b4a7ce50174398b887f31edc507527c82f361d06f8c0a005503618f8cde734ed06281f9a06a1c40f0b280d137fc7317adcf6958d9ff5ab6b3d9c8ad3139ba98c6320d22e0737361c8df8379cc45ae831279c6f337fc7314179b162e6b56ce6e6c398bb1735ab66c33989cada46f19416cbdae57fb06ce02607398a70c379a927016ada4cd86f1c04d8af6957fb5083d98966f34f6987cc526f39ed323ad002b2d279bddd492731621a05d03b21e138dc8fd395ad1ca36ca20fe8c09cc4a4a72b9022a6207e30faa0611315bd6e83db56d2666d7410c606476987e31587855c6f0e62b4310d41cdce031494e0330dd0625116ada4ee6ad981ce1ad5587c62c927286dd0033d9cbf26f3303b89003c86c383a6d5b292a7b61d2830cdfe737165c1d3387b59639b8f8507ee4400a2078574281b88c4b98baa0d524a48ca36d22289330becf5d8c0ad458666c59ebb18158e9bfe2dca51e7b4a7a5ab71817b4c9e928d9485885e1500ea9ff67bab56ce1e5cd395b88823a3029378c3c6c5619b58d07aca260f6990465cd38dae8a1b9896833060a40d24e0c5a0db18148ac5cd38db18ca2986138c3eba18ae30b24dd28a5cd9ab7185619c00559dbda4e1a923627ca43524c62b (by decide +kernel)

private theorem part142 : Excludes 0xc080000000000000000000000000000000 0xf387dd16840000000000000000000000000 :=
  splitAt 1 108 0xf387dd16840000000000000000000000000 part144 part143 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part147 : Excludes 0xc000300000000000000000000000000000 0xf3dfd491e1e078001e00000000000000000 :=
  finishCode 31 0x7717871148736c2ed3089875946f0c56731387d18739bad468c3a4149866f3531e46f05da9802a660f9ca60f315ed47a6b139ba84e0f702a58b2d65039a93e39b8bb6357a3f630ea4d80e2a1517697e5a06f1c438db289fda30e0c739b987c9fb4615cdae6ba30a0c11e79cddc461bcb3b2e693f56931bcd42700c4286e6d62c93f5cd661f176c4fd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part148 : Excludes 0xc000200000000000000000000000000000 0xf39fd111c18060001000000000000000000 :=
  finishCode 155 0x398ec410e23b8ca2f861f8c56c0378ce2985214fcc71b0f0c3e161acd5b398945c3c2731a30ea354fc8f843c2a398b162ed0f0b56cc3a7315b1504c128b41ee302e516b198443c2821418a58ce20bd24b146c5da8c078479b41ed2420773798536735c604b16a27671c8682307146c3c22ed9cd651b379c1e628382a671e9bcc3c27626081f8c0c6110f0a3b59c513c60628d9eee3eec1f63021e1a0f3141cc221e16f128f2044a422ed28d87866e142b3124e62d5b176a0bd0621e16f05da8218c0ce4f394c606727ad4dc4671ee720bc3b251b292b30b60764e1f20fce63145e4109cdd07ea8311e035b58d3d3079281a0bc3b2821281c1d9531303b107ebc207d5c2f0e62c1f986ec417be3ee8b5d1bf34d6303284e0fe4f9064d1814f12770325286e23382d769182327cd60e0c9058d18183ec7dd50ac60523f13e4e63247e30280f417ab8a21cc5bc671805d09f25cf8f760c949ca514193240db8581cb11064ac958869ccd5346dcb119a9aa8461dab66c38b825cf410ac0e24a9b0d6227a308ce1b8b0173cd5f2c0c15ed67728c0c948aa835a06a9c0c903bd07f08cc1f5aced636b3d07f8986b116b3a3fe064aa08834082147fc0c9476ca1369cc0c9372a3ad42741fdab64f976178580c56e42601e162cc923308a3c67278a5e306a13587a93ca36980f066149c354930798a368f19c9f183395a51d49e1e151ac51b0f0987d30581bc6e09f3183a0fe011061a51e3021c116baf091196520bb4a3c61683fb07d89ea823be16b97bcb9a3e16723028df9486947735c7dd46fb4e6477c6045ae93727cb10d4d817a2d75d14c4d1cd70e15ab61b31d5b9ae0dd84b68c2bdcdab63ab6a6964e480a8ecf77181 (by decide +kernel)

private theorem part146 : Excludes 0xc000200000000000000000000000000000 0xf39fd011c18060001000000000000000000 :=
  splitAt 1 116 0xf39fd011c18060001000000000000000000 part148 part147 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part150 : Excludes 0xc000000040000000000000000000000000 0xf30fd638800280000601800000008000000 :=
  finishCode 127 0x771cc791c86801beb42984c583ae4fd0759ca4e6ed43209a0bb5a6717b5c8e629411a0b6075c61cb129ed398c61e0759cace632c451de72b0ebc1db075ce6b0eb8bb60039bc51b075b104b790621e33878f3e00c9c343c6d2340e81c74e6e7b9a306a1b51a93cc1a2e538c3a4df4a1ac098187c9e6bc2005cd7356d1e7460d686c59380cb2d2629cc64079c059483170398cd5b37f981cc262d741fb50c82886315acf6398b56d01f356ce626075017026fcd5b37f8f849bf1bfdac341e5a4257f3f9bd75ab66ff1ecc6ff41fc18ca3c8a61c74c560eb28693f68c3a85dcdf187942ed5b836a86e16b9cddcde61330fa88639b83ad34541a4379c71d53189b28d589b28347c2a6200d0662d1a0e6a35836cb4298c22605d5946a6ff394c1b639bb389d985a2a49039c7ed58aa93e72882a505a983a0a0d8baaa351b0c7bb26fbdc5cde2b126fc1bb836b10f23a0981444a36ca251dac31cc5a4341fd24b279da827eb9918790262ed416ca3f4099fce492a20b03204f34c0d05c1681f0929683f8294dc61bb9acf07f730e86ad9cc5ac33d6cbda80f891711adcde80341686ee615a0ccbdaca398be1cc4fbf3d6dab682f262b5860ddc82d478c803a0f2c5b737a0b4e62d5b4b1ca6ca203d1e3279d856c5b6a9c6e39aa6d636ada04e419b98b578b7601700c94845dad5b91e20194f3c60d26a521 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part151 : Excludes 0xc000000000000000000000000000000000 0xf30fd210840000000000000000000000000 :=
  finishCode 139 0x830a46ee41102400c003adbc7309f2c82a0c620f6410a0fd0471a8d3da8ed47d9cc47c2a61cc683fa92503f1817b497bd1df0d9522af69398a8107f506878c0632bed4929f14169cc549323ac06af696e0b73293e0e64c34168b5d74490c7e14119f8669cc1cc7c29f154126f3da5a9e5ef41f8f85c416bc5ef477a37e398c1fd882b537119c6320fe9370f1a04e6b3ac958b32404016d4f8986d513989cc683fb90ec388c8037d9450dc61f314af02d9514cc330eab0567b49a8d436ba184d24af599a7290f406cb518c2930ce1e74368c01ff501aa823f6499bdd60ea8f363023cda302c333ffa60b1d8bf27ed83f9f846930b6505ea82b87e18e1f07f16ca51436313949cb20b5c4730383276540280d2729cc43c6a22d04e54a2c82d6b3c0c5506a48e0ff1ff6416b98ca388731314ca214eccf75697939507e11d801af75361807e0e29256adb54d05e831272c5ef314a495cc06fc0e125cd07f272984ca2e629721c46901be9459a6a83f7b4b4dce621e3398cca260801982ae4583f8f14e624e527ca49e7b49cc59040fc2d90eaad46761c46a9c8313809ffc3c651b4c0e1e1ad87c21b98e627319d8721940f0bdae47ec1fce620cd281ad26489a40d2667fd6adb98c4328507281c7311f0cd5b262cd5b6b29cc5eef2495492c0378a041fc9f29f3946af694898f8506727954920cb7b4d07f489a0fce62d658e62ee3980e581c2c828861f08785945d1c4353c82d475c1cc5a2a215abd073416bdd544839c9eb62dad45ab64bd4f8c2d99c40f0b483cd819aa21879b2d260f2945 (by decide +kernel)

private theorem part149 : Excludes 0xc000000000000000000000000000000000 0xf30fd210800000000000000000000000000 :=
  splitAt 1 102 0xf30fd210800000000000000000000000000 part151 part150 (by decide +kernel)

private theorem part145 : Excludes 0xc000000000000000000000000000000000 0xf30fd010800000000000000000000000000 :=
  splitAt 1 117 0xf30fd010800000000000000000000000000 part149 part146 (by decide +kernel)

private theorem part141 : Excludes 0xc000000000000000000000000000000000 0xf307d010800000000000000000000000000 :=
  splitAt 1 127 0xf307d010800000000000000000000000000 part145 part142 (by decide +kernel)

private theorem part135 : Excludes 0xc000000000000000000000000000000000 0xd307d010800000000000000000000000000 :=
  splitAt 1 137 0xd307d010800000000000000000000000000 part141 part136 (by decide +kernel)

private theorem part125 : Excludes 0xc000000000000000000000000000000000 0xd3079010800000000000000000000000000 :=
  splitAt 1 122 0xd3079010800000000000000000000000000 part135 part126 (by decide +kernel)

private theorem part123 : Excludes 0xc000000000000000000000000000000000 0xd3079010000000000000000000000000000 :=
  splitAt 1 107 0xd3079010000000000000000000000000000 part125 part124 (by decide +kernel)

private theorem part117 : Excludes 0xc000000000000000000000000000000000 0xd3079000000000000000000000000000000 :=
  splitAt 1 112 0xd3079000000000000000000000000000000 part123 part118 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part155 : Excludes 0x44000300000000000000000000000000000 0xb9fa9ce06156a8001e00000000000000000 :=
  finishCode 53 0x380f8328d62c062b7b0d183242a3ecde69433989875f815ac73138e9c05ec3460d5f2b091769cc5e8176cb4738e9814e62b278e3a605671bc176a80407261c809233cb27308a3fc6b2d5f86b29254f1604c140302a93e3fcb9863879ba4dd31c3e5a39ba549eb319bc5f1a01fba4966a2a4dd62282741cb516161978ce630a460e588a024e3a701063c1bd40486f64f6b56d28e5a95279cc57c398ac4671eb59cbc63f72fd9a8b0355e146a6cb094a1a58f6fa30ec276a69d04c1a30ec438c1b13447f16de0f7183615c61d8a32315ab707f5848ead2c1e6c57b83d973cf9ed4d85161341ed2866e92e7ac1e83da84cd5ed2b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part157 : Excludes 0x44000210000000000000000000000000000 0xb9fad1c2c31264881084200000000000000 :=
  finishCode 29 0x791986c0e2672163178418c2873151acc316ad9abe2339344b830718c1b17e524c60e1c8a0049a3103df06c14040fbb87318c3ca494189c15476d4589a2d5759dc831382b55e207ac3e4fca92582f187382b17c37ed57398a8ed6c631493101d07e92460e51aa50d002a435c1003357cdbf461c9b2905727903e2fdb56c5ae731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part158 : Excludes 0x44000200000000000000000000000000000 0xb9f89150411220001000000000000000000 :=
  finishCode 131 0xd83e0ee36841f204af86d7940e82f30f8bb4e4a91f8de6b51922e5f93989bcdb8200af01e1237c80f4a38bb5663290cdef368cc340713390ac118794768090628ee54531c7418a73193f26f3524a08ee1c15cc51d9bce69ea7fce63183a30ed3d36b9fdd705e18bf1abda56a493ecb55ce627cf96925cf6abb0fe2e7bf0a61c0ee2924de71245ab69ff51db066587c7316aba8ed486e61b5e1fb9cc56051dc61e6a7b03e834b93e62fb0647721bf1fbbd0e62e07317e039ac5b93b2d5b357a834de6a2f6adcc2b0d2c28aa356d41a587811a701476c1e6737d07b7b7b04c92a6f7581ab7132cfd26f71d8a02524b356cb8270f6814c4048fde387a86d45ec31988e3f7387a83657cb0247eec51380a86df0731ac4f082eac2c06f738286268c398752867f97aac0055a796e4e567018516065128392c9314a18e6e579a4a4c3ea02d2e3fca60b4791e6b09620930e30fc73730fcec2f0be1844e531eb5ab6701315b0d6395a8561289cdcc3eda285639293661b48114ff30a338c40bb5f45f0e52e4f94927d741cb066598973e59cad4d02f2b89298e36b315a3ad8e61a0f69ed7b19cad646b4b38dcf631a697e6302ac0fa358e5d9a56e6f4049b94e6e61f30ea90e0c4b4ada9a71d4ff9c34c0abe338a298e5e839735c0791baa93ce0a4d18ff26d7506a9871d268ce6b30f934673598adb45f0e3b20e47ee7215b0e271344e027139a05f10126e5816ec31988e6e5372ca1b (by decide +kernel)

private theorem part156 : Excludes 0x44000200000000000000000000000000000 0xb9f89140411220001000000000000000000 :=
  splitAt 1 112 0xb9f89140411220001000000000000000000 part158 part157 (by decide +kernel)

private theorem part154 : Excludes 0x44000200000000000000000000000000000 0xb9f89040411220001000000000000000000 :=
  splitAt 1 116 0xb9f89040411220001000000000000000000 part156 part155 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part160 : Excludes 0x44004000000000000000000000000000000 0xbbda9a0c488008000000000000000000000 :=
  finishCode 119 0xe63e0d63803ff207b08b43c87018e561ef527c93f3959cdc987460c3ded5b610c1ef6a3c90d8c1a4c43dee0360a81064fc613cf692e39c3d072c5749fae8b40b367b49cad0522df58101320e5846d0e3ac219ed31832e78f6e0ef1a5d21ac138c1bda4d2f3085ed208b9842f693959815ed30bb568176b1070d696cf690b79bed052839598971e40bb0be6b0a7ad072c22c08c2509296c1286f6985be6f149f9bc65178225b07b4c6f149fbda6378a8bcfc5d127ef698de2a2f7b4ce470d6a89ded334d60e3183268a4c5d03f1b05d127e9df985e0b3521b05e378b98e7b4823d85ea2f380dc486a8d6371b12588e4d19ec2c3125ccc4305aa93c9b3243527ef699a40f78fddab71cace02b339f07417c204ac0901f882941c932e49f9bfe5068b7d6823fcd5b5958b7d06e70d607c9eb725b56d06ea62d0a078c267297b4d07b521984d68506c0411a6ad5da42c577318b7d1c464c58769dc1dd41a8178c1cc5b5b10130b7d8a273738dcc5116fad0902c02df49fa026414b080c59ab6f6939b8ed616fca3d5139ca4c567376b17c6adb0866969c747b661341cc1a635bb085ed28095f0707304cb8ef591d9bda50727bb8e3af6962bb487e2d0c40b7d20387a8a661cb0fd27ea4f9492b2d613cbe0316607b0fd6868174d1ab70314e1ed4d9012c0f062bda683da0e5656d610628b7dab720e541aa35 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part163 : Excludes 0x44100000800000000000000000000000000 0xbbefd68c301005112208000040000000000 :=
  finishCode 63 0x1b06515c5a0e62c633093f7005be6ff8e6ea3d89b3303d486737771885c0e6eba3515c44f6c7b37b49f1d45ed63968e6f1690c6f17b4cd558f8e70d593cf694efac8d486ee277e5219c741bece2d4e5219abe268b485a76b535319038db886e3506f1381477293d45ea49517ca438c1ca276a4ace4d6f28ed27eb396a3c7f12e09bc54872924de25f9927e1d5395b08a631871b6612272d4d4922df49fc7f126ca90cb232c8d486605927e0df2ddcb35722a51d27e70f16fad0e0310c81c6ce5706b45da4d98c3c0df395837e386b88ce2d8a2f51dcd55378b51d4773d9d44f1bc49b3289cde25c7968e0df (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part165 : Excludes 0x44000001800000000000000000000000000 0xb9fdfe0e70300055aa000003c0000000000 :=
  finishCode 35 0xe83380e9731785f05daae3da662fb4ad26e837498cc5f488ac9e51aad4da8ebe1b87a205c9a3173ce083cc13b7b79eb5a8ea07524a81e521a0de586a435672d555a3cd2d5a17c5819041bb916480b5849a26fb527c1b6524a48d02f3dbd4864d149bb51e49ac1ab41b9345aaa8c2d0b358ff2a4f73128734849a20852e3ad1dee327fd1df06d1b68215aaa48d91de9dd37dacd5ec31b1dca6f6949ba51cc0a0eb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part167 : Excludes 0x44000010800000000000000000000000000 0xb9dfd687161044992200210840000000000 :=
  finishCode 99 0x2045e214398b88ee2e00eb6a160506a924de31fc5286c1781670a84de2c310a1d183378a8ed47aa356a1edf34f49b2a4351aad8b835858931b8c166d498b8293f2dccf5b49f9b8cdbf24a41d60b581d2ee3180eb3f1a849f8b7e6a2b11d492e479476a3d500ca3d524cd5f6f18c6a05bea0d9ee23b359c9b7d4863cba0e68cb6b1ace4dc670351659cabed46aa497b58f6e59c8ece735bda5aae05351aa40a2318b824fd5c4e12c52160166cc217b48244b832ce459a08f7accb1d2e7c6041071830d1bda4743026c59a5c17b48e86378868ded29c320741fc659cbd86465b4f585e6df3719fc5ac3305cdf66f137dc9433f0ac34de24659ed2863a07f19abe6fb5c150836cf770d4c60e1d9bda5ed33da664104581ed24d9371c2990d49bc660486a6378bda4fe2c499aae9437b49bc584771a8580e049d92ce8c0b065492c49498a082cd9cc637337d9ece3063c3376c5b7378a90c26f357cf665b98c0b065492c494869c02a18de2b4f8c1c3c36a0e0695c4d9268a925abf136548674460e598ac3582ed6157dc4d960b82ccdc6e8136569f46049a2c5f59ecb53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part168 : Excludes 0x44000000800000000000000000000000000 0xb9ddd615101000112200000040000000000 :=
  finishCode 67 0x741dc7d08324097917c074a68837926a93740cc6ff41ba0260ae92e541ab42506ff49f97061e6a066836b16e40ba0e568571487205c5be70461e2dca4fd3f292351aa90e491c1ee506b58477693741bb50401721780f0bc8f718996937176a4fe398a90e7b4c5c7503932d492b42a8f2240ca24fdac31f64df63db26cc5c17b4b283b39222c0f5a38f0d28f1bec9b273187664d949fabee837a40566293f1e1c731812145a0e3a731075c1b6386a4fd47a8398ff2e624073149bc82949fae893741bcb1b16fa0de7b1ad0b5193ba93f51e8b7d3ff3da41268ff2e3a51dbc58168414a30729267c923302a0de491981641bbc8817926a94738ec60596a6937 (by decide +kernel)

private theorem part166 : Excludes 0x44000000800000000000000000000000000 0xb9ddd605101000112200000040000000000 :=
  splitAt 1 112 0xb9ddd605101000112200000040000000000 part168 part167 (by decide +kernel)

private theorem part164 : Excludes 0x44000000800000000000000000000000000 0xb9ddd604101000112200000040000000000 :=
  splitAt 1 108 0xb9ddd604101000112200000040000000000 part166 part165 (by decide +kernel)

private theorem part162 : Excludes 0x44000000800000000000000000000000000 0xb9cdd604101000112200000040000000000 :=
  splitAt 1 128 0xb9cdd604101000112200000040000000000 part164 part163 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part171 : Excludes 0x44000011000000000000000000000000000 0xb9eafb8eb22044cc8800222200000000000 :=
  finishCode 13 0x1c426cca013908b5c3be1ef8001d7103d7c5b18c4607de2ab8b9ed57514930e1d1b56d4264d12e78e8e2e7b51c9b2d456afc7c736ab56c9b2a279ab6d2d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part173 : Excludes 0x44200010000000000000000000000000000 0xbbcfd6a38208c4884000200000000000000 :=
  finishCode 69 0x18c6f1dc671741f7901d07f075d486a3541fc5fb2e0a4fd4483dce67000b025612f6941797edab683149fa0be4a197ed062b8330ce2b8aa3001c3690c93f397a07c17e9099196d5b41fbd9d03e72f94868315a382cc17e72fa0e60b3371b58417e83f15cc72f371cd2b0e1a07d27e2cd8e6693f74127e5fb9ab60ad41f9ccded302f570461a4771a8a824005fb399d07f26cbda5286a0069626c9bc6155c006f18e5e8019ed2a2f15cca2f397bc85fb9eee2d7399a00664174411d0590e668e2bee36facf5a5ab4f15c97edab72004dbe2d750dc6df400a389a356e5a9b5363065fb6b3ce3d474acf42c7132dab7183371c47316b9b7d00273334cce4f4989c5d2633dde306709371ba0c82e8a35945e733430d872cd4e2e5fb879a905824e5c1725c60daaaa1b26897ee0e706da0e65fb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part175 : Excludes 0x44000010000400000000000000000000000 0xb9ead3c3aa20c4890000244888000200008 :=
  finishCode 61 0x378ee388f2077e0f7b18c8103d01f1bc47de83f1bed07f731a4fcde27ff5c17c6afa90e2fd9b7d46b1b7e510a90d8c57081e2df96a27ff58ea4fd07e3ef41fd003b0be357c1d6d2d9ed658f83fb91cdbeb1ba0fe8013f3c7334a1855e378973e30ed455118c6615c020c04f2e39cce0e61b716fa40721907e93f60cd183517a884d5ec1741fa0fe6a2ac1527ef22f8841ccd46b35153bf2c14796a2f41145f460d6a6d61524cd5f400b88b479672b4f371cd6304ba8be400a0c58c791207b4c83141f9ccc1d293f5f107ea218f9eb51399c60e524ac7527f20fd745f1abf1b7ce66821c4e582b57e517a0044933da5262801 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part176 : Excludes 0x44000010000000000000000000000000000 0xb9ead283820444880000200000000000000 :=
  finishCode 113 0x571dc398b78ce2f8f20fbcb9f34bcde2d4507587bcdc470de217f9abe5fb6add06d5a0a4c47669318dbed4d83fc60dc9ed5f851e48003de0eb881f1839aaaf694c1ac24999abeb1b486c60cde282f94369eb610a43630671383bee83dbe41fb15d27e0e90f7cec318903a093f417c93141f83a41d7130c983063c1d6b1d41fa4c651ab9adabed4d6a783acd6f06cd426d5b49fb18de330a20b7d07f02fcb8ed5b524a07d27ec420c5a4302fd81341ed4440fc3db695a4fd0631c15a5681f6abb3093fa3063cb418b485aaa733592ca22f900286e2659ccd546a2c3db6a2d07b371b556400cd3b6afbb90a378e24001ef5c081ebe2bfe6afa0045ae8c2885003357d5f7460d4926df9442a43631707e107ed2d8bf6d5b4fca90c987358dc8ed2f6adca2751e97ed27e9f99abe882d900356d00283172cd07336fb57ce664d987466d59ab6801800e6734bc9a20eb2078e8e6afa0fdf049fa4ee075a0fd1858e9ccdac32884d5eb5151ea89e7c170207c821074a0fd27f103ce27077d987917c41fc721397a08f81c4da8f316dabe80141fac76357c1ec79aa216a3be080198be831357cc4749fc60dab61b56a17060107f06d4b1b1b8c79a83f510ce5962d8f355fe93f49fd06f36fb56d07ed6141fc93f (by decide +kernel)

private theorem part174 : Excludes 0x44000010000000000000000000000000000 0xb9ead283820044880000200000000000000 :=
  splitAt 1 94 0xb9ead283820044880000200000000000000 part176 part175 (by decide +kernel)

private theorem part172 : Excludes 0x44000010000000000000000000000000000 0xb9cad283820044880000200000000000000 :=
  splitAt 1 129 0xb9cad283820044880000200000000000000 part174 part173 (by decide +kernel)

private theorem part170 : Excludes 0x44000010000000000000000000000000000 0xb9cad282820044880000200000000000000 :=
  splitAt 1 108 0xb9cad282820044880000200000000000000 part172 part171 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part179 : Excludes 0x44010000040000000000000000000000000 0xbbe8f674a88280100c48802000008000000 :=
  finishCode 99 0x378fa3b8e62b81ef26cc7013e3b10dac27311f38fdd54380bd465a0936433b3109e1c3d5c4c106ea2f9a46809607a8ed41a93f987e809691a8a649fa7ad27f1cdd223205d445c1345e1692e62f873149fc4d949bb516357b065ede93f491677348d486d479676937510a3fcc025bcb3b391eab355da8f24047b6ae328e62f87317e0386d2396a67cf94372885a4735554421bb7e1cc49fbdbe2e19b8c9b2c5f588b9be7b1b484d5f355dec64cb7a993660e3136527e961cc626c9cc649fb98ae2f0be1cc5586a3ce6f838ac45a420a9492b0e67b19b549964d94c1a570ee53cf0715939a46695b55d832d5562fa4874286e6ab932d85f286daaeb077b9cb53691ac1d7c36ac91162f8ee49b2c1794427cf440e86afc5b947f932cf869192767b1b8e4dc6f639492d579cc77141b24450321cf06a8fdd5c4f3c7d96aba4fce624b1962ad5f524a4455c521a4d64f5ac5587e93741c9b5e49ba065687d127eee2c86f36adc4cb0cfa8eda472ced705e1692d47824a6af7b782a4e62f6f9abe09b59dbdbe3e7a49669a9cc60df3584d229e759dad24e626d7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part180 : Excludes 0x44000000040000000000000000000000000 0xb9c9d630a08080000448800000008000000 :=
  finishCode 121 0x100378ee398ce4283f720ba50e0f79846261877dd085083efa29871d0f7b5567a9b98d5fe61f259ca637090d8fded5b5aba50cd7f1625a56b116919344fde7058c3f245e0f798a5b074168204a40fa24fc1d71cdd5c7aacd53521b1453f32d5df46adc81716b9cdcb0f1a7548681738ec839075a05d50810e1e8399cde737075a40c27927ec0f922320dcc560eb5f01d6d42a094310669e8b156aed239a5e827382cb0169eb56c9a281740bcd5f49aa84e6b0a795704b0802a62a081f79107ee42f86f726cc28f492b0666b0c4d960ca49413f1cc49b2d3b176c73149fc0829f9a922ed398a4fe44127e7c2085a7738e5a5a28f03ab586348b58e5a39c1520613c1c349fb6880f50dc9252d7870cb8f059435e9015a1d049fb98b824067b7962c802411417a0fddc6b3cf51407904594407a49672da7cc35ef6f9a429f34679006527c7df620bd4586e611075ba0d006ce398900481282f9ab60e930ecc3739883addc7919c5f14c59dc83f30987bc1be3ef6d127f2c6d22661106f87bd9006fb4e6731b58cc5262b615ce4569cb98c1bf1c043de1ef9ab60df7e1a471cc5a763ef38e9cdd0c261c613723b915a927313ffa03c1a3298da2e0722d4e690870d04293f41fb55d9c418c1fe521b8fe83ca4fe0fea07981e93f0e1a03e418ac16176b0fd27e731 (by decide +kernel)

private theorem part178 : Excludes 0x44000000040000000000000000000000000 0xb9c8d630a08080000448800000008000000 :=
  splitAt 1 124 0xb9c8d630a08080000448800000008000000 part180 part179 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part181 : Excludes 0x44000000000000000000000000000000000 0xb9c8d210840000000000000000000000000 :=
  finishCode 75 0x4005237c1cc740823107e0465214398bd86476b56cdca0eb0f7af81df592cf717b4a51cc5693f91feb276717c1acc0eb480a49480efc0b7e30883ad6059ad077261c60cc222c79ed2a139ee293f0f7b786079696c41491b13cc22407308c62b81d64097315c6518c3988f3649fbda43be1ef1fb87be06bb007e0b7cdcb251cde69138e663cd491c6e926c8fddbc6001af0a0f3439a93f9492b4191db132d3b3292540293f62168834cb2b7b1a3fc5be3cd3798735d04c118b1b5da9a71351ab56e7b48b5d857348cde6925390c923811b47203ded4340a0074518408cd5b2fc9365cb71264986f6740f97e683f8fbdccf2045ab67012fc9cc5ec7356d05e6d11f7c93f398bf0ae3007316adc5c7407a4fce1e2df1f7cf6b8e0307f268a0041bec2b963e62b2fc9cc5d0380c93f1f7837d28f2cf47de611 (by decide +kernel)

private theorem part177 : Excludes 0x44000000000000000000000000000000000 0xb9c8d210800000000000000000000000000 :=
  splitAt 1 102 0xb9c8d210800000000000000000000000000 part181 part178 (by decide +kernel)

private theorem part169 : Excludes 0x44000000000000000000000000000000000 0xb9c8d200800000000000000000000000000 :=
  splitAt 1 112 0xb9c8d200800000000000000000000000000 part177 part170 (by decide +kernel)

private theorem part161 : Excludes 0x44000000000000000000000000000000000 0xb9c8d200000000000000000000000000000 :=
  splitAt 1 107 0xb9c8d200000000000000000000000000000 part169 part162 (by decide +kernel)

private theorem part159 : Excludes 0x44000000000000000000000000000000000 0xb9c89200000000000000000000000000000 :=
  splitAt 1 122 0xb9c89200000000000000000000000000000 part161 part160 (by decide +kernel)

private theorem part153 : Excludes 0x44000000000000000000000000000000000 0xb9c89000000000000000000000000000000 :=
  splitAt 1 117 0xb9c89000000000000000000000000000000 part159 part154 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part185 : Excludes 0x4300010000000000000000000000000000 0xfbc9d629e218e0086000200000000000000 :=
  finishCode 115 0xc6288fc240ee24fd5c531741f7a0f66ab8b15ab62cd6adc7ad6afa0fc58ac23c86e075d986adae91839ed22cd8c2cf698c1b07630e5d946ec821272c5d905cc5d905fb08625cc1fded2f22cee41ea08507e4e51c1d18383ea83501a82141fa982cd0e1c83d6aba0b683f870d5c6d154740376e619a9aa1b5248fbc9ca82d859ad5b1f7a0fe52482fc7de3ef95868146ae4789ca83f162a0766ad93954861cf940e0bf531f41f7a6883f83ae5fb8c1ce673f6b56dcda0bf418cd5b1deb9b417ec2320e57a306c0941082e417e8c2c743aed5ba30a19d5a88e6e839b9463071876b0b95dcaf3da59c621905e1b4610163208d01a1d705fb907cd8fc307f6aba03586b27e60fed338172f69584b1360da3ef410a81e1f7a0c548583cc57731b134bf67ed406c1f67b497eded3075c7dec4150a63da4fda2a79626b1f981307d056ad2e406b1358af1ffdb45c14c5d1a8aaa026e378a0f50066e385570b2cdc6842a08e1764523461d68e4e56203431ff563707f836a00646e93968368a66401c61dd04309ca5cf8da2b09401acd5ecf011507af698c3c8034214c471d04d1442fdc1b63f68b2cde24e53f6c2cb58ccf674009394fdb41cdace5fb378c1b64008f360db1394bb2a62e06f146ec2a5165c61e2fda376699a004343187 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part186 : Excludes 0x4300000000000000000000000000000000 0xf9c9d639e00000000000000000000000000 :=
  finishCode 117 0x661dc291be8e43a0fc3200df6e17c0eaa4fe6ada51dab7357c9caf693f0b15d8af2794c56be288613272cd5b49fb0d672ea7e526a9f99b85e01b6be1875667251c32b2d4506327c6163b15c7de7ff5e190650c220c7928e62b489c93f166a51cffaca36861359ec7fd41ea51e3e3c3cd00997656a6c4f87deca2f8d5b927e3ef31498adf8476c61d510a92455f12cd07ea1b949280f308b70e624fe272a0c43aa0d9138c4b93f0abcded2d5f272875568272a085ab70b35ab7390fc3a0c803365a9875589b3ddd6a20cd6518c59ed07316683157840eacf66a2bd6d67b3da62eca4fcffab49818ae84284d9928e83f524a0fe61cc07d489a51d8c3f12053127ec519aaec2706fa03cfbee82900df409cb278c3c4db8c3c9e76adac6d844078fbd94790386e399a8af57176b48626ca0fe26ca0f6607a8bc9b2b05791dc8c3c9136109c74c223ef06fb20b83a0935a30e4db2f6a08507ebc2d4e610a04dab62ed0e1cd333efb9be0fea2195e2d55407b8e5cde2ed409c4db5907de83f26cc1c3691cda3b8f23200df627c6115a9c71d308cc373809c7590520137204da8b07f5a397b5948505db139502659b8d47187480ac147864db6aac4d926dc81339bc0df (by decide +kernel)

private theorem part184 : Excludes 0x4300000000000000000000000000000000 0xf9c9d629e00000000000000000000000000 :=
  splitAt 1 112 0xf9c9d629e00000000000000000000000000 part186 part185 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part189 : Excludes 0x4a04000000000000000000000000000000 0xfb5996fd229408000000000000000000000 :=
  finishCode 43 0x368d0358ee3a09e0344fc1f4cd5b163a4fd02ece2d883715fcb19690871c957356c59a2c7859ad5b49fc7176adb08d4075d2871c7418e71d906e8175a058f205d07293f40bc839053c7331638b35447d127ee5589b2b332ecb9bce36737166c81790725d97b4b58e81c263fba4fc1a693f83ae7f7876a5d97b4a4fd84531a04f09bf24fd06e93b7d1ca71c6c7d27371f4c4df927671d87d2d33604cc39 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part190 : Excludes 0x4a00000000000000000000000000000000 0xfb59d675000000000000000000000000000 :=
  finishCode 121 0x6b1986d0a46de398fa3a0d4036d901f4c4d90f0c1fe09ab52d4420cd352cc178c2bda5ab6709399b50d03b80c7403c8176b2c93f591cd6561a8b3507a9020e649fad3e387b5442ded4b26f8b34e2f20a4e661e1741740f08b467aca05d07ae41521a884597205cbb341cd02e0c57403c30fa4e6671326fc83d68180641bc1f4a40c0998724df837b24fc9bf20dc9bf3da5ace4d96a883841c3137dd06f1e44801c2b434893f581c8193959cdd7037fc2d11f4b48640ca0e5603020db204d072c2b59db16cff29a2a0c5b41ccc2b4fc9c75073460e6adc1b5cde4b940c9f8e8368b457c6adb083e9906e1bb51ac813946ac43489df92863e938e9cdd40479c9296ada4fc7d24df9eeac3f49fb56cbab23cc7d2929068815e72bb93cfd27ed1f4a4fc1c2de26871d8e02c2298e61cdc38f39bd81e9430ebb03e737c1b6176a40839927e6a5900e4df41ec93f7d1bc791d06a01c2da32080d524c3e9419a4fc3c2f69927e8173f6c8371f4b9b683bbdd60f681726fa4fce6e71b3f14468127ec22be6386a0b459a737166cb3381429420de0deac1d05af691e6c1b60deb16daca7377b4c1b638d9cddd06207d21e18e6e4d9982ed61607ac660eeb3f1669c349733da5ca63cd39ba0f6070b781e154160166c8371f4b02659c9f05ed20d949f8b34d3b2d2dcc26fb839a4fc1b29dd967ef6925c976527e6fb (by decide +kernel)

private theorem part188 : Excludes 0x4a00000000000000000000000000000000 0xfb599675000000000000000000000000000 :=
  splitAt 1 122 0xfb599675000000000000000000000000000 part190 part189 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part193 : Excludes 0x6280000000000000000000000000000000 0xf9d3f573540000000000000000000000000 :=
  finishCode 67 0x1f86e1a40f0b98b40375806715049283353d30b35eeb248deeeb11927e5d91e6cf6949f833524b033544630d8b461d5e2f692e6a4fc59abe3dde3848f362dcc2d72eca4d62ec83756064178521dc540c3a605607d0776138fc4b5f003d3df07749f8f0d8051fc72f0568fc542328e5cce4c19ee2c4f7b498ae3069473979ccd4573d7581e3f1399a889016ae834a51e30e6fb50bbda459a93f7bace6f0cf9ffd3dece398be1f3e6a2bda528e1d360097334ada96d5f628b92e733c1656af8e9cbb2f699ccec2b69b97659c5e13026dc8ff4a3b98a6358c35927ec4d389a03d240d5c93f1e18056838bd5d81ee39628c1de62b808d27e35f987e2cd3ffc93f1e1984e0ff3da4c5693f6e1bc1f8c0db1f4c821399a03e389a80d05e61f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part194 : Excludes 0x4280000000000000000000000000000000 0xfb939523540000000000000000000000000 :=
  finishCode 121 0xfc378f2328ce390521292b70e020fe063837574510e42f690e9bdae59ca7bd002e4f7b5c4d98e2ebe316e315ad3e401b99e4649f4c6ee6ff48697ed807a0a2eee31360ea8fc41bab4076507b176583a93f72ecd37409c61c0bb3024f927d358da04589ac5b2ecbb8e024fe7b4b1341a60dd511ab70ed60f6721486bda527eb47a0f64d9486bda5683898ed66adbda527eb538786ee3701d59a7a72b40887847e20dd671203460546af69386a51ca367e3da6628b4ddaa293f045c7fd16697647e2d37813af690f0946dc07207e2f4075639583443c2c578e565d97b4a4fc1a262b8dfec6348c424ee524a43416a0bf6b0fc417b98e49fb15d84ef67856a4b972ca085ab691713dca4926c8abd22e90d941a93f3f8a084f0770bb291f9aaa8012fda50c36b2311879eb2803254967c79ae596afa98b23da6727bdd54871832fda4c68c1b93e696b90e02881e17b4c3f149f9ccd4371cbd1df1811f8b58a61cbd44328d507e943621ed30f3417af67986b07d6adb16c5569175c107aa6245c0173da630e7f18c1a8d52871839ed24b97b3bda670127e6058c5693b94920b56e1bc701c8540192ee2983f1068b56e604b51506261f0e8c4b93159c4e1f89c86069b08d5b800681f5798fc521a62b061bb8b818aded31fc51f6d5b89d3338af789b21d305fab06a5947ee456ad93650427215309b282f9262011a0feb4b723b915780dac0bd314a4ee4178fc4e66be20bd01ed5b8e66d5b9006b1f (by decide +kernel)

private theorem part192 : Excludes 0x4280000000000000000000000000000000 0xf9939523540000000000000000000000000 :=
  splitAt 1 133 0xf9939523540000000000000000000000000 part194 part193 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part197 : Excludes 0x4200108000000000000000000000000000 0xfbdbf421694a58421210840000000000000 :=
  finishCode 37 0x298fc3804fd6515e31365a9f07d8c39f756222ed419987db47505dad6279e7b9a4fd3f64839cae93f588d187583948e5c127f2c1d262f698bf6e0328c2187debf02f455252326ccd6549bb166176948c9d25fb9ac651c0176c629751b463103a83d467d07d58da4fe30f2e0e4791bb1876adc60c36a49737482e5a67461d27e9056b3a37603bb4d49b3187489c61141ec2ed (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part199 : Excludes 0x4200180000000000000000000000000000 0xfbdfd6693a5c0a5003c0000000000000000 :=
  finishCode 37 0xe0308cc3c85234c101b20dcbda9234a3bb8b0359e729a4949fa8291e1cc3583bb16d0669253f6cf6983693f5a858105ab4f9842f692f6a04d072c5b86eb3535ed21852eca98ee2d093f89fa73727ec839613c7d926fb48dcde813416b55c9fa8399ab706d77124694727ec83962bcf77416ae8b020b49e7359d8ae4fd510167280d27ed2b9abe0b3630a849facd61e68e563065d97b4b0ae83697ee0db2035eb2d45 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part200 : Excludes 0x4200100000000000000000000000000000 0xfb9b94a9284808400200000000000000000 :=
  finishCode 155 0xee358a6101d747009e64fd6610733164a46e6b9eaaf5b6adac6cbaf18339ba50d287359dc064105261f8c52a2ba30ed45309ae0d441e647dc60ded25fb6a2bdc5286f699cc718359ab515acef719ab60413f3c60d456ca3a8e03006294a3d1877239cad0728079ab706d421b4352c3cd416c1b501aa3f8bb274359d07b3135672a117b4c9170dac61c79b461dace62b308c829701a05811c41480a61b1ac1dcdb07d39b9c6c9fa8375b09e6d358c0a7376afc4d9302b08b42a0981cae0db0b3567ac2126c97658a271b26ccbc27871b176a49640b9f4e59ca4fe3f0dc25102eb63544f4310e3b173c7871c7581312e60e6f5b58686ace3ac2b869b3dd5a961ab176973ce3af699a5618b043bdc5202947698bc8bc3507a0bb568f204d85741b5eb26a5897271d586c5cf58d86ace3a6979cab077729b08497271d5e1e86a8c8176b2a4d528e8e3da58b723256a6c2193bb3da5636901631385816c27993f52873d5c14670149dcea2889624fcfef3d5dacac572d7b4c68c1c2ed6049fdded20899a62c1d3fba30b0315e6b2b8e522e6058c1a50d506a5d18358688e527ef69736b07587e2eda306b0d878693111ca4fded25af380c4fd481446313849fa384d9166a80e515ac96604bddd66ab39531ed2931a3066f11e186ac16b460de4531287460d66ab39515bda49fb18386a6a2b6a6bddd64706d482c5d9421ed2741764fcf284569e3c591d24d959a9bc659ca0f434ab355813826cc4fd3f3cd5f50ba4c415eb35a306d2b26c9fcd07aa62480c7837652327493cde4695c1b161f9ba418e0bb27eb58cc353e6a282cded25235a0387353c9b21c39ace4d9905aea2d0aa30882d419c61e176936659eabde6b3a07459acc320b1b291b4d66a8b59cd4b233daa2f693eca04d227359cbdaa2b58db08cc2cc56a62ed8c3c2b559cbd6669aa8ae30e93789b2b3d (by decide +kernel)

private theorem part198 : Excludes 0x4200100000000000000000000000000000 0xfb9b9429284808400200000000000000000 :=
  splitAt 1 115 0xfb9b9429284808400200000000000000000 part200 part199 (by decide +kernel)

private theorem part196 : Excludes 0x4200100000000000000000000000000000 0xfb9b9421284808400200000000000000000 :=
  splitAt 1 111 0xfb9b9421284808400200000000000000000 part198 part197 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part202 : Excludes 0x4200080000000000000000000000000000 0xf9ddd521121402100040000000000000000 :=
  finishCode 55 0xe032051187f240967214770a42b027f628c9bfd032607288a0dd26b181ca232f852377128f20dc59b24960fb24fc9b62cd49fc4db291945de46f14428bb18c424fda4288b4f63f1a77dabe0b3607cf5d7ba8b366afc6fb67174695cd5f05994455059acd212ecc60e57ebda5a56b35390c359589b4ad63e5d972104660e0ace1c9417b141cbb3399dab724fd27f38f5692d57397a4fe283b18ea2e893f371cb3f24e82ccbb20b5690c0bf6617405e97666a2b8ecdbed5b722b984552c519a7b0b5dab6d576920db39145aeb556af8e86 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part204 : Excludes 0x4200800000000000000000000000000000 0xf9d995a3104210040000000000000000000 :=
  finishCode 65 0x7017064198200c28f43905230f0c9e9274b4c4e5e733274cce2982ed9ab61c341f93cca4b17b419ad4d8dee93f2f6b56d07f3da526e4c14008784a46b518b5ee39526a0fc9e681f49fbf10a33051165180610ce6d8399f4c59a5233ec945c78730d5ed2a4d6ad948c79b2c44ffa93f516bda527f2934a2ec2330ce148d50492a7a6166b11e62fac467b49bed27ec629359c60bcd2d729a4fe30eb49515870e0ff136d27ed47982ea2b8c3a79e30f248d456f595a9b083c3949a1c3291b56e6a58bb627994459c791ac283944558750e5eb25902683d69ac7dd83e9c1569318789b2823907ac6298cc13cc8cb3da63064d9417b58416a83f9a6ad2b26ca4fe41682d5ac32075a8526c83d28ba88d21905ed67392a8ad47ed6207e39796e646e9fcd422f69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part207 : Excludes 0x4200010800000000000000000000000000 0xfb9d9fa10618c6184210210840000000000 :=
  finishCode 81 0x791bc590a2ef41c0ae2cd569e90288c099ed3071166a4fe0f717663066f17b4a3a66af9f0cde2c49474c6f1624ae8b0460e166944565f24fcfe7183166c1c649fc60d672a8288980b3527ed5594061a96aac821765ed2e51965e0ad4749f9e589ac4e7b4a4fd603d14233da5626a3f7b4c379024a846306d21288a8892d9a422cd501b4ae597b945ed2c4208e41e941d70531846a110498826e246828d46af6962fa48f6ba30e93b51a92e649dc60d82ef69351627026cdf6f69029b05e62fc60c6925cf4749765ed209b7b4cf699236f77617b9b51bac5f7b4c82348c613654c6a127f02d521a943571893317daaa93f166c60e0d2acfd1d24b99a420b549f8d4e59a86a5892d21581b4edabe93f941a90d3f8a20782c07f148097306647420a38d8a4f38c1a4ed893317d8c481893317d27e6c59832d578c1a4eda561999abea63d0a234ada8a2cd9442a4949fbda68c19f9c97293f967e93b057acbc36b176541a0b5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part208 : Excludes 0x4200010000000000000000000000000000 0xfb999da18208c0084000200000000000000 :=
  finishCode 131 0x18c6f1f8207b0096145d03f24fd05e83191d22c5390b2093f41161b359ded282141f936478b0b5ded2a119c8e83d7b4b20da298ac2c87212fdce6b41f8afd42323a5062931903e83f24bc72526c9c8542f125d47e821418a088a17edb462dd07948bb91e0e67b31d5a0f5c8f41cdab639b13096a63eea0f5ed280da30e83d7e1d43f18449fa98d420c6397a9252769434b1a9f141d05eb138e5ec43946410a0f4bb33da585691772ea08507f3da5704c14c418c72f41fa20b31964a0b948bb56d042b1b922e0b16a19849892e662fb99dab60b9592d18348b9cbe055a0be307394520ad5b2839c957053126320c4bb272f417b10ce232e69aac0d85718726cad256a20b9661b42eca796733b074d86afb4f2ce6783ecd5b6adce67410b4ce0b8c61dcceaf12839764e4ab82b0a622072f905e9314189cbe41f97edccf461d07a82105686d41726dfa0fec1341082e5262f6987762a9392bc8de300cc145d74620e5ef579422d4516bb59ca220a19a8ab0985aed4538b8b5e6a2b101199ed2b4f16b9444dc3979c0d5b49dcd4f62fc1f60caa00497619595eee637b4ace5b4410e5f18598331876afac0cfe64d9382a108838f5a8a1a19ab6291960683d283cb03671702839d0c496a6c8dd8c3a004dee8dd9a9e84356e0db34ce30e5d96b0cf6960ec60da668dd9a9e5b916ba98b2310b2fa306d4f2798b5d80411abeb558dbe5fb051cd675aa9b7ded7460da66b4549dc1fc1365fb5d1abeb19279cf7583ccb55690a4c5c8ac02905d962036b0f35007353d66b353d006e59836c803 (by decide +kernel)

private theorem part206 : Excludes 0x4200010000000000000000000000000000 0xfb999da10208c0084000200000000000000 :=
  splitAt 1 107 0xfb999da10208c0084000200000000000000 part208 part207 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part209 : Excludes 0x4200000000000000000000000000000000 0xf9999db1000000000000000000000000000 :=
  finishCode 51 0x3404118832d63a841f4a1c0e149f948de46d17c670c3e7258a0e72589b2705400a0c65249c1630f1f74c3a50730fc1f641fa4ed26261f851e46f1a862bc0e128b9485e84efc70159794441c2a83da527ec098e025b572aa7f63fbb50507070ca1b17683866a160379c93f357bdad49260549da50d2c3019c62bb09e49f9c060ee90d984e7f79ed2b2f49fb09d87e7019c7290d4d1bc630e02d339a6e7f126cb4d569ec2714fd06969985649b2d6769ac93f6b39bcc59b13cd60070b08900b5563328e4dda4c15a2b9be838c60d6326ed7aea934fef3dd4d8a6ed49f936e2dbbd7565e93f (by decide +kernel)

private theorem part205 : Excludes 0x4200000000000000000000000000000000 0xf9999da1000000000000000000000000000 :=
  splitAt 1 112 0xf9999da1000000000000000000000000000 part209 part206 (by decide +kernel)

private theorem part203 : Excludes 0x4200000000000000000000000000000000 0xf99995a1000000000000000000000000000 :=
  splitAt 1 119 0xf99995a1000000000000000000000000000 part205 part204 (by decide +kernel)

private theorem part201 : Excludes 0x4200000000000000000000000000000000 0xf9999521000000000000000000000000000 :=
  splitAt 1 115 0xf9999521000000000000000000000000000 part203 part202 (by decide +kernel)

private theorem part195 : Excludes 0x4200000000000000000000000000000000 0xf9999421000000000000000000000000000 :=
  splitAt 1 116 0xf9999421000000000000000000000000000 part201 part196 (by decide +kernel)

private theorem part191 : Excludes 0x4200000000000000000000000000000000 0xf9919421000000000000000000000000000 :=
  splitAt 1 127 0xf9919421000000000000000000000000000 part195 part192 (by decide +kernel)

private theorem part187 : Excludes 0x4200000000000000000000000000000000 0xf9119421000000000000000000000000000 :=
  splitAt 1 131 0xf9119421000000000000000000000000000 part191 part188 (by decide +kernel)

private theorem part183 : Excludes 0x4200000000000000000000000000000000 0xf9019421000000000000000000000000000 :=
  splitAt 1 128 0xf9019421000000000000000000000000000 part187 part184 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part213 : Excludes 0x40c2000000000000000000000000000000 0xfbf3958787b461000000000000000000000 :=
  finishCode 23 0x1e8571c4398b50be02be0e382f4c56d0380d2d989a0d17b5c6d5613b58505f3134dbf06cc986a130e3a0866a0c3b356cc561d16a5cc1f36fb56d042ba2c01c3907ec271f882b584f2d050428310e1b508216b1c82f315a84e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part214 : Excludes 0x40c0000000000000000000000000000000 0xf972b582878000000000000000000000000 :=
  finishCode 155 0x390be2e8ac278dc1c84e5ed20f8e066874ddc6adcd6148983541b61d18e62935695c9db2ef981dab63bf398a51d446e0e66d80736398832457f187c3a65df83a69254a3b78dc3e00cd408c7314188b5e4fe9cc4e63251d203207506706f0e68fa5d4691b00e9a0465139cc41a6a278c3ef4289e7b49cc41b6c5b9ec27ef315a0fd7840fc731315987e4759c9503eb0288864187176a1063036d01e61f314bd03f19ab680f513836cdab203d44ed5b6aac6d5509b56c1a60db701e871142b0fa41b66296c1023356ce6291f9a96a016ada8e67b5a40d0426296ad97ee527ac05ed27317003a30f847e20d3501305279366508a40d042f7789b280d928682105fc18b2380d5b93fe0db30fa805fb58bcd2f41f8afd452d6392066d5701407034c1b6ce203605fa80dac673180caf6940fa0c5ab7034c1b7062f0d82b8e21cc5a05d0192d2f928a7135c121b20355f2d6190631c4d49b3dae306d55389a40d042d5b30eca25476836d042e23809db91fec43409a0f5ab60db30ea688a284e584b56d5f2a3b419a08f696adcd4741eca294949b56142c1b5252d5b51ebda5306ada0f640697e5b8493cb33696c1c6733bda507ae0388b6036d5f303250623f18bbf247e0e293949d8fc5086c0e26945411c6a1500a0c5047461da56b4b9ec25ab51ec61d8806d937e6adb584e268230e8b56e398ad8d83d0881cc5445f107ed5b4ffc80f4919bb43a65e198b6d2d2ef8b2661b93a503e83f6afc0af498a07d07ef699a9662b40fa0fd74691c42efb801d3621cd5b50a8f8cc3af6987c6d379ab60af6a1c05f126315fdccef776b0b4dc53af6962797e4c568617e5a5b34e5612b4b045cf69362b4b5a7302c477ed617b4a89c77f388d42c08c1875ac73da549ed5b49d9b166adac5ded23bf609cd5b362bda53b66c59ab6c5993b6d217b4a855ab65df9ab6731 (by decide +kernel)

private theorem part212 : Excludes 0x40c0000000000000000000000000000000 0xf9729582878000000000000000000000000 :=
  splitAt 1 121 0xf9729582878000000000000000000000000 part214 part213 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part217 : Excludes 0x14044000000000000000000000000000000 0xebfb9d8f828888000000000000000000000 :=
  finishCode 55 0x1c47919c0f9b30d2390bc1c84e4a0c9418c3ab6b1b16dab67bba0e307750a851501e3df87bf1c5ce8407970a256adcc1d626b58d407460d42ae6b1d5cd6316dab08214189f0a4d735ac0e2d0b56c76a69f87a3280d9c691d4735c0bf7b58f7c1a21c768101f03249c6b186fdab7289d243278a630ae1daa7ad8b6d5b1efa50d7051dc0af514a45d62f3da5cd66df735cf69057a085062c81a7e1dab9adeb24a96ad82b50428315307672d05ab69435a0c199475bda52c541ab7308567e7337b78f7d07eb00f7d03f356ce660c1920698398e69b9ccdab683158144f356c6a31835009c5ce66c00306481a856 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part218 : Excludes 0x4044000000000000000000000000000000 0xfb79948c808888000000000000000000000 :=
  finishCode 145 0x418ee360407701c420fb281f72fdca3b3159846735bd8dca2a3b51ec9457d1873289ded20837a8a08549a1f7490c8316a03ee66320b57561c7b1bdcbbf391e57fb56d28b391dab61ad72cca276ad9c85904c0802883c88216ada0c5cd723f4e4a2ed47ece6b62697b5a8790dab06dce6683f176a0fe064870e382b585e472198710e667d38e420cd390caf985da705417a9366ad8bb505e1c392c530cc600ffe7e41e67b4b09d6821a79eb31855958b1d9c6909d3177c19b06d91d6a2b274b1362efb56dee288268a02c08e13a4dbf23aded22b97b8c0937b1cd5147ea4cc52ad5b6adc94527493a65a038706d8daa0a77bbc1a76a5a20cc356da45a1e447e833458e3e3a0fe709526c1b6626b51e0c0b16c7c60cd790f0475c7093ecca3f526a3ae7b4b17d400e1d185512b17e30b070da5aa2557cbda62e7ad443867e260da352d4c4f178441eeec2f96822b9051cc17696870cdaa3e38386d4787671f65a5ad2d949ad55965a1c3651b4671ab7460dac24a57adad44386709949af7136ac1ce6ada49d4061959ab670936a93a5dc6519c5d1c00e7ba081781a6a3d902e8397b4c81790521db6c1c074165f0afce2ef696adb96544e0d3661905d160163c1ce513a8ec15ae6b87c6d5b949e8fb928a943965aa3b7b4ca2772c9c85242c8268b235867b7ac5dea60996ad8f8dcdb13656aed6171eb91dab702b54025b38fa6d5b6a190069ae82ed728ce6d499b56e7b7a805cda81796aee576ada288379ab6a2772bcd5b6aac5cf6b0870c19a2c7 (by decide +kernel)

private theorem part216 : Excludes 0x4044000000000000000000000000000000 0xeb79948c808888000000000000000000000 :=
  splitAt 1 136 0xeb79948c808888000000000000000000000 part218 part217 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part221 : Excludes 0x14040200000000000000000000000000000 0xebfbdd87c1c0e0201000000000000000000 :=
  finishCode 123 0x1d896298b826081f50107e9e0746513a4347bea29681ab691f9472a0347782be6a4a8e523ea15489c7338c1b56c7beb02f82db260cd5b3999364d3f1eb5ab6c358c1bd44986b5589b23df4f101e8a280d5b9652a4f5a7a89dc0389a406727ad545b6e4f965e7bb610c7131efb40e4f96131835a7a43c19234d9a5ed5b58fa51521ea02788a340a2751da51641082f43a2c399eb20af410a515985617c680e42b802fe0e8b0e605fb0fe6b1b15d63f18790427136ad82fe514b56cb9f29358327056adae0a830082158163f02a5ee71871e8ac7e728b58dc7af736ada32dab739ad246b4f68142b39ad26ed63802e7bb501a854e66d5b359c14d3eeb56d1da9e2c0be2e813da30ec1d8c2a84c986705399b8071792267dd8e2ee63410ca132619c4d60704c5cd68ed6ada3c4e0a7215f1548c1cd63584a085ab62db49b80b66adb8f5226e6b410bdae8c18b6d612d655e170541306810428318c3c7210e8b58e5a5a8ed426d5b389b40d3d9ca318369ca89da5e7130e8aa87137b9c9ef6b186fc5b6d2f3eeca038c1b56d472a038fbab13389b56c3a2733791c058142f1355aca7134928b6d86b34bce4292537dc7dd261a85d472713509cd5b6f19c3a1c0580e260c93eecf6b50bb58d472b1f837e71385aed6372ca8e45af20c506338f4e2720c5cc3185509a89dc87917c430e66a01c5dcd7032542a4d951e8326615b52daa2a1583a2981e09e2085887241547a7136b2cf73a30e831064a93437b2484192713701a40e8a8f6064ace61dea48651482f507f28454722db (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part223 : Excludes 0x4050200000000000000000000000000000 0xf9fad4e5c9aa64281000000000000000000 :=
  finishCode 21 0x3c8e8368de1c85781fbb066618a4dce621bf9aae3af14bc4d959d827d692a4f3a18b7356ce621cd37bac0b259ab60b1055b403f7487cc3172396a5ab6a030e68b5d857356d6c7716a3136549e3f769ed1873ec82a49b2f6f27486bd5f334dd64aa4f26c9ba507328a47ee731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part224 : Excludes 0x4040200000000000000000000000000000 0xf9f9d481c18060201000000000000000000 :=
  finishCode 145 0x3b8e8378da1cc481e41f56149f1ccd452e6b513c811475c1fd49eac0b5e37ba766231b16d406e03684117917c14bc725274d1871769cc648fc61d50178440e62e57947a8216ad9d84e1e85fb5138e6e243b04c2f64879826b5181725a925dd1832d4b04d8865fb51eb68733947a5fb8c3a89cbf72045705311f71abd63a2d75a8a0bd745f163b304c73718337b9ccd0420ab119c57b7b5a08522f460ded6905a30ae6d7309eecfba713671bc5e080ea0460e308b56c6e2a3d1769cc614701b43a05dab024e4dd2d3793d2a396b2c11d83eb146604b594dd3316d40661d5816132c3d49af618daa7bb584abe5206c099abea2b728ac3d49a61d661384b101328ee30e9394a2ac07413a561f38ed24ee6d51ca49e7289b1e30739b55e6af959aa49cec6d0dd32be54769d99acaaf9691d185374a41542e8093efca0370b51949e5f98dd27316e17030fca1361bacec37ab49274c6e9261a84c987398cdd27df6d0ec51dca4f700a03c18030fa8f5edf1b5630ed5f728a7a6308b96580650ff2731961a92950ba93528b461cc22e6b526c8fd374a4ee51e987ce62731961b051c4622894a1987ce62e82d84015e1105310c6ada0fcbdb2d3ce6681f512d1831769cc5a734614192f6b17697b4e62d5b398c2ed399c7ff41faf06f79ab673136acd6537baf0a0290731541606adc1a1728c08f6adce5726c93a66a89365ab6da2f82ed063c9374a3bd4649ccaf947f9f75ab65ed6f19860150491272945274cb39613868c137461cd5f068d22ab6280b39833eb4f3eed18736aacccdd31f7e501676d458232f5f154c61c9b2f5f8552b49 (by decide +kernel)

private theorem part222 : Excludes 0x4040200000000000000000000000000000 0xf9f8d481c18060201000000000000000000 :=
  splitAt 1 124 0xf9f8d481c18060201000000000000000000 part224 part223 (by decide +kernel)

private theorem part220 : Excludes 0x4040200000000000000000000000000000 0xe9f8d481c18060201000000000000000000 :=
  splitAt 1 136 0xe9f8d481c18060201000000000000000000 part222 part221 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part227 : Excludes 0x14040010000000000000000000000000000 0xebebdf82a2c052280800200000000000000 :=
  finishCode 41 0x3c8e22e81f3611c81f19366731922d01e7f3399a0cdab720bc30e2a3407c8dd5279fcce668336adb945705016453147ae5785aeb1798be1a9417c7172dcb8ee2e7bdad05e717901aba22873349ccd5b419a8a68c2bd9e0e27ef62fa0f506280d9744a1704169e81c79ab6b17411a45d9053128720fd14410962e0a4bda63069eb8c3a3f544ef69a30f305d8bef638c1bda5ab6f6790468fd66180623ca276ada0cd47a94505fa89e407ca4f817a80d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part229 : Excludes 0x4040010000400000000000000000000000 0xf968fec4aac042890884240088800200008 :=
  finishCode 63 0x20c6f1f4851d00fbad840f416c83d5149fbd03e90395f24d9527a0b62ef901c316ae077d063461c58e3ef83fc7bb5879abe30e5fb595b9b57c207ad8d00fbded7013e0da9d9838a43dccea29731a8f641fa43d906d11471dc92772ba93dcaf34bc17ef69514b15e7a8b95d022e3b9c9608172ba5890f9266d63a30ef83a0b8360b6358637bad5d60e5fb397a0c507ed41a09424a4e5f1abe30e9437b7cf6b8389abd49f1ccdcae943419a046583a8ee145b1c8f398db472bc7174a1d18794765fb1ddc7138c3c5fb6607c683386de7093999f3e837b88fa2c81db168ca29731c4d9390b501cf5a0c7254a19c967415f3243dcc63c7399862e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part231 : Excludes 0x4040011000000000000000000000000000 0xf968ff8492e442680808222200000000000 :=
  finishCode 75 0x106388de428ce07dd7c207b683ef3ddca29723873dccf02ddab7461528ad2d6a17c49db98e5abb4866adb58458b3984fdf00338da0fdc81eb179856a3d392b04e7b0b16d3b64b35910416bbd862fdc6164f5a93d04139ca0126cb9ae6af9eee26c82dcbf61df1f7c28ba368d42e08334a1277391630a7254a1af81b39a7a0b7728c5cf722b57d47692969ebdbe509b56dcc302ac29e1573999e8b221839b5302f62d79ec26f74949bde6b0cc4d494b944ec6adc6f75a885ac2f68c596aeb224c4def1878156d218e858bbd4501b351dcaf24ecd8b073509c2d72fdaf840f5b054b1ef46b6d5b6a392c4166b519ea205b527b56da8f356dc46f19c6403b6e6da0f2c2f6aabddd44e7173999f9e6adac8d5b9cb2a29736a89cdee721168b9b67319bdce42b21c9564b28ecfe72c944a3016d272d2d5149c85ab6733 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part233 : Excludes 0x4040010000008000000000000000000000 0xf968dfc182c442090805201010120200080 :=
  finishCode 107 0x10a418f8378ce3c840f711900fba80da2f8a291ddcd5b0e782fd063220811921e0b973682e66b0a0fd063284c17ee419a563bd697aa0882046527a085a041fb54e7b792cc17ed639ac7285568aaf950992cc17ed5b5c190690cf5126c82e417e82141fbe8e476d1ac734bd07a7ed921e90f9ab6e4569dc80d487b88b007dd68b356dabeb2949d8566030abf5406d5b5959bde390b68d42e8fa2c5e408a04d066b828067a89c15286e574189c16500b95dab6f51a0dae576ada04562ee6b9ab6821509a416615a4a5edeb155aba045b40fbb308238e6681390669ed52791966adbdbc172b57641586614531c84e5e743087056f1a80eda93e470bd4562ad5b949ee595aa8f8dc8f20f5cdb41fdab6dc2c9683fa93cdab311d6458ac91783fac3c162a4f7c0dab41fd4021cf494b05e0e7a90a820b5287137d1e6e6d5959c26597c69d470acad28700368be378f8418a2103d60357ca0183c9c5ce4aa2b357ca2751ea80d043338a02c8c4798622d10eda8a5403076ce42b418d5e1db83fc6c78c3bd456566f73908b5e501876ce427254918271cbd682b43168ca4f578cf638c38f2c81e821410ce6d595a588210efabe605c936507e0b99a8e1b5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part234 : Excludes 0x4040010000000000000000000000000000 0xf968de8182c44a080800200000000000000 :=
  finishCode 87 0x4187316f1f0801c4203903cdd31b1547e1df0fba0365268ef51e2be4283ef791740fbbda605ca08605fbdada433d452425d391bac5762da49c3bec21d0e434b5ac2c27928ad57871a49b6afbe9185a306f69609c61c58e1f7493c7bb69eb48528ad5f613cf691fbcb83a098298943960eb332fd9cbd06283f5d1645210420ab3a0e0b3945a5ac4d24bcf69583c61ce26d2d8e27187411acce4199cbd60e917a306b437b5a085846a14c154cb51007a0bc02ae5169e93a5262ba3680bd8e26d3b411a0cd7c7b59abe11fc60c00e9177b4b944172f69a30a917736a45e609ac1dca2f6b05ec1b5a42d5f9ac216739782acdef3da5185116af1eedca20b91e597ed64ab515f189a0b9960e0bd2fd91f6615a50d1bf187583921e509ac7415f0a2c83a34b605ea7fc766d5b5d1e4731d1852619c4e307200d07a4c37b4cd3b83693a66adb93ded30f2dc47d1bc5303b70a137e36a9c160538f1d62b3144e5ecc2c84c38e4a0b141ecf6905e815e696b914fe64c3592a84e05d873da43f3c92705d9cce (by decide +kernel)

private theorem part232 : Excludes 0x4040010000000000000000000000000000 0xf968de8182c442080800200000000000000 :=
  splitAt 1 87 0xf968de8182c442080800200000000000000 part234 part233 (by decide +kernel)

private theorem part230 : Excludes 0x4040010000000000000000000000000000 0xf968de8082c442080800200000000000000 :=
  splitAt 1 108 0xf968de8082c442080800200000000000000 part232 part231 (by decide +kernel)

private theorem part228 : Excludes 0x4040010000000000000000000000000000 0xf968de8082c042080800200000000000000 :=
  splitAt 1 94 0xf968de8082c042080800200000000000000 part230 part229 (by decide +kernel)

private theorem part226 : Excludes 0x4040010000000000000000000000000000 0xe968de8082c042080800200000000000000 :=
  splitAt 1 136 0xe968de8082c042080800200000000000000 part228 part227 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part237 : Excludes 0x14040000040000000000000000000000000 0xebeadff2808880048502808000008000000 :=
  finishCode 39 0x3c87407cd20430e0abc2a8e598fde8031e8a51db07c11df2c0d1be4c31e4a0fd642dccb293e7a8ecb5b2d556527cf0d08686838cf518342089410af09836093751dc7cf489a0fd287244d8bed5b153a44e837cca1a87ef87a29473f9a00d6416bca4f7b9c94749bc86320de203d843136568a1c71efa8ee5c0ffe0d140ec4c3165a50cd8b356d0072c65ea2b3f6ada0fc9860d1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part239 : Excludes 0x4840000040000000000000000000000000 0xf97afef290808204a400908000008000000 :=
  finishCode 49 0x3a0de350d23709e033c3b60db6adc7fd57cc1f5aaaa3b5ab8b0d6af328ce3d86357847c96680983fb54ce621db57134398a783e35abce6b0428e3d65b310dcb25df905a5d5259c1fe83ea04cff2f83086c78b6eb2f623ad5c5aa2ed601ac7356e0fe3e92efc4c3357c08d161b11ce0a2c3982e8396238fa4e0a0d740cc5cf06b836da86119c7c09870d9da5ab075ab8fa45aa2ed5213c398c83d1619e083d5abbd8646f96e56564d9357cf735959cc65a086861f48fa6257cc2378ba076d49f3dbc8ead5b2ef9cc504691785db204ce623e341bcb0726fb09d476731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part240 : Excludes 0x4040000040000000000000000000000000 0xf9e8d6f0808080048400808000008000000 :=
  finishCode 151 0x7c1d0801dc6c14c208907df440797e636298749d3184630eb38d4105d786d186f3dbcfde08916798445da9831665ab9784c22aff9a429173149fbe14bce6b0d0a3b4dee7ef5310c580fdefa036e3fc984c3ee61d8c2cb157b8b4f5452d6149db4f67b8b485ab61f7581f40fbc61d162cc4149dbd8606dac0a807dcfd31859ac29db9602d5b2efb5860beb56c3eec83284015e15c530e62da207c9d30bb49d31c168c2a0cded6b49441ab720849b341b4bc282d170a08d03f207e410af0f2280881cc49d3356d0c596c82d501a445f4596c83d501ad4540728ad606a14567cd9ab682d8c1cf513ffac3d6929358fdaa033e6d06d3ff8ecdabed5b3989ffe7714c8510c0fbaf87313ffa03d65f184d89b356c1a3175e30f877d857315d8b662b06c87dd786d0e62a22685df478cd571f1b55e0e1cd5f176c1fd07f461581e9475a4c81f771bc3efc611203877c3eebc3284c385da61d3159846243930cfbf328bc3088133989296019b55c9d22ed248d18701aa845abe5df3efc8137b1c595374bdbc9d2f23b8bc07ddb05714c398ab04e952128e7cf92261a183ecc493e7a79da5b1f3d3ced5b680343279cfd239193ced5b551a0401222b5185aea153e79fa562f00ccbc67cf5929f3e5a8a3b56827e98f9e4e96e164420343391528eb2516bad45547b1a780a98c3c7cf596a8ee0d3162dab6c1d8bc62312c5b98e5a8b56c342e456b0ac95541cf9f3cfc73d8d28ef6f8f9f2f0ae26873146fc6af4f393a5ab64d949b92266ad82a49d288306662f936526ed5b274a18562444b9f1f64f7ea2b60b92965a8ac5d45681394567cf98330e049124e96ad93647ee731 (by decide +kernel)

private theorem part238 : Excludes 0x4040000040000000000000000000000000 0xf968d6f0808080048400808000008000000 :=
  splitAt 1 131 0xf968d6f0808080048400808000008000000 part240 part239 (by decide +kernel)

private theorem part236 : Excludes 0x4040000040000000000000000000000000 0xe968d6f0808080048400808000008000000 :=
  splitAt 1 136 0xe968d6f0808080048400808000008000000 part238 part237 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part242 : Excludes 0x14040000002000000000000000000000000 0xebebff9394804400050140a020000001000 :=
  finishCode 37 0x1bc5403e698354e6b2926cbbea4f408a0c5c85d1805f124e8238e66f6b9ecf20b4e26a0058e406a85549e4c382c680d41793662efb56d2c72160620e669f19ab6a176afcf6950a8f7e3909365452d5b80c727bc2b22518c2a7c4e66d5b5c13051ec7e31e8a0c5c85f105f293ce5eaa1c4da7b293dcbaf6b411c60e47dbd45cba4c358bd07741793657c7b5c80d4a3a494e664c39046713 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part243 : Excludes 0x4040000002000000000000000000000000 0xf96bf691848004000501002020000001000 :=
  finishCode 123 0x8020c771d0208c41f6f19c4b080ec399aa2d5b0fba4e5c4493a601f7604cd654ffcd5f604a7a58133595ab6a3d83eee2260bc2f8611527cc3762c930d2268ff84d64e9261b68a01b167b4bd4daa2b253f4987d49ed239ee261f6afb594f7324053b2d51462c2335a8b57d3fef6926193a4c3ea027fe6a89f7ce62a4f03ac4c3691b57d907416c200a98a83d467b393a4e6282f41fb9081f93d27337b88334e42f698e67208ce42d658e62e4378c02909157b4a4e630b136507ab013feb595caf1858d5eb013f09d3248d69ed65586c7315a7a809012749cc62c4ac94fb28139ea273198566c56adbda5aca4e94c17c274cd5b6a5a4dce6313a5ab6d31066cd5b274a514e62bc328c81cc5a8600967356ce423e90e8b7082381b67218df7356ce66d4036da6207b903ae476adbd84df7356d88ede370e23000db64058f07447d29399a627219ec60cd0e8c90f6ada4e4e5e7c160190628c70569b9c847d2ae233640bbda40f73dc5ab6d3126fc8fd7259ff49871c4ce663e96a1c474180066836ded31c85272721969f031dd05d185f1c84e66c2f98beb335a4c9036b2a8f528a4d99c8e6fb06d9cce147715c0fbaf0ba1cc5a82efa076416a07e83fb55c3a3460d042f6b7b48fbdcc33da505e3ef5410471fc56764d9410b0a6368ad4455ad5b5e1ca304b5ed21d1409a45528a7318c1cd5f063a04d22a9455703bebc30258428ff9cdac2b493bda4e623ef9ed24d98782821 (by decide +kernel)

private theorem part241 : Excludes 0x4040000000000000000000000000000000 0xe968d690848000000000000000000000000 :=
  splitAt 4753 136 0xe96bf691848004000501002020000001000 part243 part242 (by decide +kernel)

private theorem part235 : Excludes 0x4040000000000000000000000000000000 0xe968d690808000000000000000000000000 :=
  splitAt 1 102 0xe968d690808000000000000000000000000 part241 part236 (by decide +kernel)

private theorem part225 : Excludes 0x4040000000000000000000000000000000 0xe968d680808000000000000000000000000 :=
  splitAt 1 112 0xe968d680808000000000000000000000000 part235 part226 (by decide +kernel)

private theorem part219 : Excludes 0x4040000000000000000000000000000000 0xe968d480808000000000000000000000000 :=
  splitAt 1 117 0xe968d480808000000000000000000000000 part225 part220 (by decide +kernel)

private theorem part215 : Excludes 0x4040000000000000000000000000000000 0xe9689480808000000000000000000000000 :=
  splitAt 1 122 0xe9689480808000000000000000000000000 part219 part216 (by decide +kernel)

private theorem part211 : Excludes 0x4040000000000000000000000000000000 0xe9609480808000000000000000000000000 :=
  splitAt 1 127 0xe9609480808000000000000000000000000 part215 part212 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part248 : Excludes 0x14000203000000000000000000000000000 0xc9fff9a4c7e0a150b818141e00000000000 :=
  finishCode 97 0x10a37886270740b8b4f57163ece2c03df83dd0698c3b56cf6e8eb058a446395c0ad16b8f3637282dd21a8eb700e4698af08fd499cd5b372c7ef16b9fbe2de9c045af23ad441efacd510618c90f1bcb56dcda90d84f24c74a1ca62f8ae2e0d0276e38e972d61a3df16ba436697c9471efc48942b090f486b9561a4ac35c828eb6a8b906475ac3498f2c3521ed5b84ceb0d46c8b5d30560f07a8c7dd722a43c98ed4b6b2a10d4f8e02b0d487931dc8b461cdca742c36152864e737a47e6711d62a5a0ee0af476b58d8b70a6583ad0298ec4487376b2c3df591a4c449b1c7446b187357b56c7be2d756123e8fd9aca2d73d4ce416ad8f7d1fb187921e0b759186b5a63399d23ea6448b82082d77012626f3a30e6f7609b05dee6929a30ee45722cd4b571386a8c1af6b2825da9706bd107b5c3796a5a51daa2d5b3a08c71255ed707b80024d94829fbc92ad318fbad6516bb8005b91de6f36a59e829980c2f6b816ee47722ae0ce0b5dcdf02dc7be90f9ede939729b78e6d898e90f1efab8e6d892a7ef0d79eee3f788f49b208d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part250 : Excludes 0x14000201000000000400000000000000000 0xcbfff9864fe0a07238088402001028000d0 :=
  finishCode 113 0x701d8551785305b6ae2e8d0069d24b02d436eb315a1ac6978e4e7ac80f60ef07b390ac8e6b1a89da6f3d65cd6b2348ac1ec37e7b79a5e92537fcd5b49bb40e579cda937476ce57728a78ba258ac06ad384c000f2515eaac17049825deab305d3fe93104dbdaded727fda9e5cf39bcd01c4c54324c56629ff944ee22189ff16ba404f571cdda9ec173d4c8df6a8c737513b40f6b96230774809cdd267358cf76d2f6f1c44322458fac0d02ce4df671771ecc177ad9cae30f393da04a2c14583b930ce42901395b0bdac6adc3df382bdcdacb1eddc9e9ff513a289458e56a275307bf356d3b62d73f7b56e531582f1acb131d646d31681a6f41dc98e9335a99ca544f0f7d2667bb83bcd4f1efa4e526724e4e569834907b92670773eea454e526ff9ab707748ac72539bc1dd7c5d0df6d379acaafb261a7fd262e45399a4c6698bdacf529806b66b2a4c65714c5f037f3595ab65cb4898f7d0c4e188f356d69e7ef5a3824d63eb80a2683eb53432691f6a6cd5b9ec707748fb4112461e05ba4856a70779ace4c30d682c4f9b356dca2b0d6a7b90659a8ead3fed5b7217c2e7cafb3999c5d144a144eb4f835a4c3411ab7304c7367136f08cb461dc8eb4f2c2c2a3411ecf41f586307b58fb91dab6b318c3cf6b723a08a2783dc18f6a98ead6731fbc5aeb4b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part252 : Excludes 0x14000201000000000200000000000000000 0xc9fff9c6c3e2a0513c0c440200041200054 :=
  finishCode 63 0x8913c56160382b30e01cbd3416dca296a89c74fdf1cde30ed5148bce474878065ed6b1f514a982d58fde2550df8b5e30f2c9c4ab1ca564e4c738e9c85605e1c0550c815b8b5568f461c2fa8fda30e9175f1a6b02bc7beb318b32917155ca29593a4a639bc61d6623df1efcd5b3c05ab06fda96a1585134761243091437ed3571e9c058b672b5e11db461cb9691358f8eb45af172d63e7dd3f796f616d9f760f63ad16bcb02a8bc2d02b716ab5368c385f54524d90b8ce4b6a8b4ce30ebe0b5e0d986fded71cdcde664428a2976230f348ce56d6784ea6ad3eeb48e35696fc5aea62b81a18f6e27514d8b5c7be4c79ab6d5f8c3b56e3dbb4d415eae1e02d71ef86fe514a76e14db59601ea4dd452d5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part253 : Excludes 0x14000201000000000000000000000000000 0xc9fff88643e0a0503e08040200000000000 :=
  finishCode 127 0x2d09e1d8a3b949e78300a3d8915c48baf0d33983a72573682b4162e813665939ccd62316dc7bec1d807a26172b82c5bc058a59069a0ee9212dbcd2b3dbb0bd22a2d7922f42870380b4b48bd18739ba444dca9179cae90f761c0491cf5b71ea45d8866e98c39cddcd738ed22e7338c3c3df551784c075b1ccc56e0ad928a1bf728c1bf1ef86b61efb48ca03c19850aa60bc34ddacad0310e5a59ea55f68db5a982d60d339560fa9151d2b0d60d324e42fabe02be48aa4e49b2737923eaa23c6491b94526e1bb72b9ca49b2e4f8b96e53478c28ec340b4f9c7b1873959cdce00d0c23983d9eedcaeb35380a6884316cf7b394528a263a30ee51056c5bd4e128b248c5aeb3959ac61e4a386fcdcad62682d725183a901728c04f7b9b9ae1e6c2d58c3b93e0cca44c79a2d58505aa981c0729399c9db4a2bdadacae3b48fb52671db5960e3396630f07759cb8ec9b291f48ac7330dfbb0b0338bc4282d5691cb3960ca4ed286822b0c4d6b056734cd8560b716b9d8b1193fe4af7ad9bec542d319a47071810e717615b55e261b59583abe358e8250e0df8f7c5ae9624a51bf06cda9a7df1ef9c86ad9a8a2b39aca9a1e89624a5a9b276ce3ad670d5a40e695a7fcde718782321ab4a1b4acde69459696943695a4a5aa334acde692941125293b6adcafb0d18b5d8b6b279a5671d69150727c9db7aca7fce42d2369b9eace0271d39120734ad2071fbe043af8b81eae72582ddab63df4a18b5ce4b0f7d3fe081a0e2b392e79c4d3fe943 (by decide +kernel)

private theorem part251 : Excludes 0x14000201000000000000000000000000000 0xc9fff88643e0a0503c08040200000000000 :=
  splitAt 1 69 0xc9fff88643e0a0503c08040200000000000 part253 part252 (by decide +kernel)

private theorem part249 : Excludes 0x14000201000000000000000000000000000 0xc9fff88643e0a0503808040200000000000 :=
  splitAt 1 70 0xc9fff88643e0a0503808040200000000000 part251 part250 (by decide +kernel)

private theorem part247 : Excludes 0x14000201000000000000000000000000000 0xc9fff88443e0a0503808040200000000000 :=
  splitAt 1 109 0xc9fff88443e0a0503808040200000000000 part249 part248 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part256 : Excludes 0x14000b00000000000000000000000000000 0xc9fff4b7755aa805de00000000000000000 :=
  finishCode 25 0xe43787833891549ca8ae6b3935418ed359acea2b35fb18ac031d613251569e0ad8c3c57b3ef9b8daaeb4b3d149b461dacea39a30eb42905f146fc1ab69e8ef56a68df8287183698a90bc2d4d64f0b5450f06249aad236b38eae16db594366d674d098301fc32e9470dfc2db (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part258 : Excludes 0x14000308000000000000000000000000000 0xe9fffcc77150bc0a1e51840000000000000 :=
  finishCode 47 0x2d0c6138a4f521426ba2a0b53660986015a30693b2f8b545a572c9da572c9d783efc8f3261b57e0249f7d2764a59ede0739ab64c3477a37cbe2cc270bc17c5841e6b384979cd62db8c3cd3d246b4f63d1a7b24ecfbb250da7aa624a66af96566ad93653da9170dec61d4c651a7b24a5aaf2c9e551780d9c9371648b6d28850de7237c6cad658c1b945a5693b4a1ae8e5196a71870d9c60e834c61da46d676b29306735b48c366901695a08d57156cd654a19ace69bb074982d23 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part259 : Excludes 0x14000300000000000000000000000000000 0xc9ff9c8f6150a8001e00000000000000000 :=
  finishCode 143 0xb4428e0340c2260a81ca58c395a79187922e0c751da8f5986adcc391e6a51547f293630f1879604f05b68623ccb7b398c532a13a30ee451d5cc5b598acf542b3187374f0c46714770779252a3d060a8f62bda935252d2b9252a3d527b58e2395e4778acd207285d42a2ad6ad8a8626ca3c59c6520eef5f8b2ab118c3936520294350b8b6e50bc2ad526b907e27870f6316a716f630ad376b2a3c547a88461e735b515202a25526b98e515ac465a9a8445664d9478a788828f524b0e9524ed5b591a935a6b0916141b56d202915478c1f6130a84549aa1526ca8f4e1ea81c0781c054063230f30e5ca62af527aa806585b718793dae4330e538fbac574a1bdbda6ed5f2f8b94e6958b6e6313c69ec2db6afa8edab70abe30f3187828ed2c49cc4d961aca0350a82bcb7f06fc15e5bda306a2b1e68b6d60650f45513c16da85e056a45d49b39ac15b12313651fa50da7b41de8c182bc5b6e6b922a26335f8b6dc8527a80e50a936522a6b38716a1526cb08b82982ab9662a4d0cdb57d42e9294a1a80c624861d5b53d22ea3b51ea489178c3cd6751fc60c5563cda30ed357acb91e3dda45d4005fa8fe5a7a8fe526a45650bb58cc3087402fc1823a5928b187515a93545728fdc8501ca4d604a49c36b288a6285d49af6f9cb2e6d2dba8edca62d5a30e9a0f7e527c1f41569130dfc2d551ec8f148aa8e547ec6358d04283df061b9be58886fd20aa1193fec1d0dfa44d49a1bf9a563df4a1c28cc1e88f148aa386515b14669b9ea587f39bd47e929628c2d5478a455472a3f5e12525bd92862db4a1cb0d (by decide +kernel)

private theorem part257 : Excludes 0x14000300000000000000000000000000000 0xc9ff9c876150a8001e00000000000000000 :=
  splitAt 1 111 0xc9ff9c876150a8001e00000000000000000 part259 part258 (by decide +kernel)

private theorem part255 : Excludes 0x14000300000000000000000000000000000 0xc9ff94876150a8001e00000000000000000 :=
  splitAt 1 119 0xc9ff94876150a8001e00000000000000000 part257 part256 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part261 : Excludes 0x14000210000000000000000000000000000 0xe9ffd905e340f0281084200000000000000 :=
  finishCode 143 0x39896318a62a07620bdbc407ae8ae243d141ef9c4e5a7b0e658fa8a6399abf5ab6e579cdab2905f86ce05e97c5746f11fb243d38482c7338c3bdae30ae6137b97c567f276630e46551486bcde3460ce2ee6d59f8f35c8b0f7cd8e4d93999c5d01e78330a8220842085806f0be2da243c17f315cdbe717728cc577b5d187514cd5b47ea8f4e846ec9db6b19c5e30ea2546ecd5338bc61d804e1282f8af8ae1c5da9b354da9e4d992733dbd3b31878c2ce63389b135886943c8ae1c5c90f34cc54ad4f129cc13232c1fc0464d97b7c7dd6a69b7c9b31b7e38b9365452d3989b273338bb4d68c3b56d426821661e46d1748c3c7133a0e2ee63a30707b261a8ad472a139456840f368c2b09dcae90f263c61e601a05a7c0bf490d187499ac7e3a1cd728ee30ea4d51dd18751fa98c22f0e42cbcf416bc7335aab40be30be399b1245aec4998be7138b9f358c14ab555f12530e1d8be80116ba211878de2c5f8c3ca2b7b5a4a4be3393d85ee596ad9bb45aeba330da173e8c3b124e26733501100dab53e2dcb56d892d4f8def187609ce638c2b59d893353dab6c2f9a9ee42e8be3407333c05ae742c9dc7b2085ab6a2546ecb1b598ca3b8c3a3c68c3a8ece0aa39969ea4d4f69c4d7c0d0c91746e8b5ce2ee478f769310daa8957c494cd3d6978b5d62734bda568316317c50170531acf293d84257b695b4f5452c576ad86ec5ae8a2a0a3d527a85e39997c5cc741ee62180cd87ea2905f82ad47b3909429871746fcd5f731c0ab9426c096ad9ccc3770b5c2d30a15abe5f1514b516 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part263 : Excludes 0x14000240000000000000000000000000000 0xc9ffb11dc945a2801248000000000000000 :=
  finishCode 99 0xe6318962a08c20bc7be83f4f4c7373809365946a9c2af4f4a935a5f2cfd0c61103ed2173e060830c55b2d4c56e2d54c1446988e966ada8f5eba2bfa3063a549a93666116016ac2db7713c6b2c3df597c0c3594b5967105730afdab7293455ac23482d56615c060ac4e418b58d4061b70dfb9b66ada0c45af280c37e233949e29b156a0c4ec6a4ca1749ba89d062d6315fcf5d0dcb08da428880b6d044f0f0498a6006b5a5c3d1733cc49623b9564769eed306000d735253dab5548f8f451b739bc51291f59ac0a5597ad2e1e8ad2e6978b5d61a18349d8b5e04eacbc3722d5851307613837fa30a395a5c93b57ed07b16bac35262b4b515849e0c18a95ab6882d2e1e8b05e0dcac3430693b5a5c7b739ba4c45ae2d79c4512cd6316ba8966b1a0057c561a44928b5deef2cbc5628d9054ad54e6e9238dfe0a93f0c28c6348cc2a00b93c0e6ea3b9ab6c39488cc2772babf66ada84c4cf315dab6a8356e737a4458a22679cce4a389aad5b62bc91162d82e5341e8abf603f9f84dca71d737c8ff39b830d84eafd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part265 : Excludes 0x14004200000000000000000000000000000 0xebff91dd43c0a8421000000000000000000 :=
  finishCode 115 0x6b1505c14c441d8418a588c20bd27323ec9b271d380c60e47db0e5272d0230a158e1e71d8c1cc094939cdc1928c28562e5b0d547670150bc9273999c4cdef24e505e3df905e83f66110601042d041ee250a93417272b46015ae579ebac134a2b56ce02d639ab6f75380cd39064ae8d2368d67a0fe59726cb58ce420c9610c72b380a484e5f23adc820af6a7b0860649cad89b30ad476b036ad9cad042d2330c0340ba0324cc490a4e6501b09ce572cfd84395cb3f610c781c4e0dfc1dda9292762b86fe513b58d84ec4391fad394078325ac706fce3a74368c4362d9b8e382b026152a76e737b53c5b6c574b1985310c1efb59e16d8724e2e80f6814070304192d37837e91559fac0c4d81922db064cb316b1b54e407b30a21c8522b39acb960c1399935615fad0aa41de6a4b58e307131deaf07750a86fe382bb8d2340a62a0781c3ce6eba240cfe3395dca2c196179355273069a306c093d02ff30bdace18f246c46751ca5158929e2c0b3fa306f7716da7fd44e929481ce4f5138a86735a9360f6729263ce451d5ac9c16b07b16d9cacf0486c9ff527920d1e29155412c53128ac2771cd06f4ffacbda9f2845c769ff581b9ae83db04c15a29b513a8907b9606e4f7bb8ead89b278a4f92860af942ad632deacf4fe2962c9e3f897c528a780f45caf39b4fe28f15a39236735b075caeb31 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part267 : Excludes 0x14000600000000000000000000000000000 0xc9ffd95dc542a000f000000000000000000 :=
  finishCode 101 0xe62e0c6298a82f8939417a0fd181efacbe7299364e67128d6aa6f79ec67634081f7120fb068d5fa9430618b5c1832854e42725733d07d2c7a43567f120f7e16b9c955c16babf683eb59c5321a31ef8ade514b68782a0842085ccf1f754525f1475b40a0070660ba80549ea139aa2721261a93e6989c4da06701632444192d37942ad4f9452a136a5b28b003255c15bcd4f8c3c6bf51d9b96584bd553c47eb11e58f8e2c56eb038dca7dd476a4cc2f7358d1da9332f8a3adb4850e4a82220983411858e26b055a9ac35ab63d16a4c7b1586a7b51dad356ad9c4d88f460d2729ed586b56d23e5cf960a931389a7b60e0a0051fed5b064b5268c1a514f7a0c9389a60c02b83d18c2c1c1699a4cda9eac23ee0e0b05e2f8a3ad262ac2d3e475a3ec5aeb2391d68fb48fcd6302b8db49468fd699a485b465114064a70a276a7cb356a5a03d672d2f8f0514c80f2f8973da96d4d8fba80f921e8fd921ea82709119cbad6716b97c528ab02e0ac2ca616b870530613ce6d1e88e2e737b9b46fe19b4908316392a485a5f172c5ae9476adab11223bcfbb285415a2d739982b616ba882b18296a3d3db8314e4ad5b69122b0315ccf02c60fee3b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part270 : Excludes 0x34000200100000000000000000000000000 0xcbffdddf41e3a0005868800400200000000 :=
  finishCode 39 0x358a6258a8207d42329347be2db4a2a0fd58514c4d55978f7d67ee679ab6a8280e51d9c05062b41e064293e0fb356da96a2915bc4d53eec4d551d96fe16d9afd503c1a970b6cbe282146198380d18769ab56c79ad5b815f3d7528a2db9426b42a08c289cbe2945a0fa3bd59c9c0528b05fe14d869d49ea274312c570d6727fd6961a3380cb355a5a7fda6f2d2daa2d2b3f88b6e359a7fd646915 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part271 : Excludes 0x14000200100000000000000000000000000 0xebffdddd4162a0005028800400200000000 :=
  finishCode 133 0x1e46d1ac5613c5e0e0a7133c1ab6d2b87bea4f380c2db7aba7fd47680f8e02a3f51dac0a2330c61ccd4c5c16ab41ed28ac273808b6d23e4c7a30eb096b2bdac5b62dba30eb096a58f3658f97c45b6bc1d02db6ada47e508b93d8b6f5d923e1bf949aa1754186b20bce0283158fcc3540fac4c9aad22a0781c052c2f8c4d9604cd2f2f8a08542a82f9c7a8312e5b16d4c351cd7352479a29b597a80e50a93660ff30d60f6d37735bdd5ab6d63531042a03942a81f6b1cb0288d5b8e4aa641f66af8b6d2862db9476701903e3df6ada78c62d0a8293d44eb239ac61a716d97c498f24c5ac69155c1608c1c9457bb8b6d3fe9314a1b30861c11839aca7f114da7fd21ab4b4b13ff1839eef071727868e307237da56d3771ccd2b0aa80f6306b2348ac60e099bd5d21a9ff16dca60b6deb71bed262943661eb70f3528a6fb7bad187018a887a1c0a0351fbd5e589931dacb41f479a842cd63ee8f35eae5f159acd6372aace648fb0d54c430bc6b121a9c203c7bf352d69e9a00366a889dd21ed2f586cb2f61ca43dcdb309d406b4f609c931613acbd8727015a5a0bce03251587290d420d5f41ec34a70149997c51d68c358e61a9c051db358dac531104b1062be203d24306fcfba3df59fcd335a7af0b0da0eed4b26ab56e0ef06fda672c7c7be80f41fa7070358e51da49d696b1f4f1144a2cd5b057a89d476782305f16adc4d97acb135ab7358e7aca5162f8b56cf04420ef2855a5e8213dbd1876a6bd7e3ee82a630ea2769166b28ed24eb4f48f9c056850acc39527b4ce8c18a6d3feb35 (by decide +kernel)

private theorem part269 : Excludes 0x14000200100000000000000000000000000 0xcbffdddd4162a0005028800400200000000 :=
  splitAt 1 137 0xcbffdddd4162a0005028800400200000000 part271 part270 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part272 : Excludes 0x14000200000000000000000000000000000 0xc9ffd5555140a0001000000000000000000 :=
  finishCode 101 0x10a0785a46f1506114c38eae07377305b7355d002d2b1ef8b5d252d5785632bf51e2e5959f86ed7016dc3d151fd187581a8ec5b6a61c3d24b24dc5ae8019ab63d149bab0642988ef6516016bac4e51f868e695a93d1e2d3d492cc1d828a8f34f48d55476e6349bb28a634ae4949ca45af12251cd4508c70583eb9ad86b1afe508a51e5112231354fba2db51fb56d68488cd3516dc1f5426729615c93b57ea80b42e0d6328a80b5d26f0f44e0b41f549ed5b49bb57e527a4dd607461d26f0691e8a40549ed5b8366a29527ae092985ae8cb96aa6f348086cd9c382aa81b392022d749bb4d63e6c1f45ae6bb91de7e16b17054158410a989239c72d5b604a51cfc22d750149f302528e3d150ab026610b56d246a4f9ca6c216adab0ca44894716bb9ae61a9c154233d7528f398d5b83ecd3959ea07deab41f549e02f615bc89a356e4a3bdd64ff88dd49e91116db9668c18f7d452d5b4f160527a50e699b1449aad6759ecc310d3a98b0550ab9ae37fa4360ef04e567b1835c1ac531423293503e2d7541541e89fc6410a51d84f23be30e82169aa936014ac9c5aac1d9a668ef1e8a93450f1eee30ae5171dac4501e2d5 (by decide +kernel)

private theorem part268 : Excludes 0x14000200000000000000000000000000000 0xc9ffd5554140a0001000000000000000000 :=
  splitAt 1 104 0xc9ffd5554140a0001000000000000000000 part272 part269 (by decide +kernel)

private theorem part266 : Excludes 0x14000200000000000000000000000000000 0xc9ffd1554140a0001000000000000000000 :=
  splitAt 1 118 0xc9ffd1554140a0001000000000000000000 part268 part267 (by decide +kernel)

private theorem part264 : Excludes 0x14000200000000000000000000000000000 0xc9ff91554140a0001000000000000000000 :=
  splitAt 1 122 0xc9ff91554140a0001000000000000000000 part266 part265 (by decide +kernel)

private theorem part262 : Excludes 0x14000200000000000000000000000000000 0xc9ff91154140a0001000000000000000000 :=
  splitAt 1 114 0xc9ff91154140a0001000000000000000000 part264 part263 (by decide +kernel)

private theorem part260 : Excludes 0x14000200000000000000000000000000000 0xc9ff91054140a0001000000000000000000 :=
  splitAt 1 112 0xc9ff91054140a0001000000000000000000 part262 part261 (by decide +kernel)

private theorem part254 : Excludes 0x14000200000000000000000000000000000 0xc9ff90054140a0001000000000000000000 :=
  splitAt 1 116 0xc9ff90054140a0001000000000000000000 part260 part255 (by decide +kernel)

private theorem part246 : Excludes 0x14000200000000000000000000000000000 0xc9ff90044140a0001000000000000000000 :=
  splitAt 1 108 0xc9ff90044140a0001000000000000000000 part254 part247 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part275 : Excludes 0x6010200000000000000000000000000000 0xf9f6f0ec5f0234081000000000000000000 :=
  finishCode 27 0xd63a0da28ee509c60c9b65f10649c4ce5ed82b8c61cc4f07aec3f737ba49d8a2b3ba0def5d0e0c1ed28a6af05c864e0e0a3ad28af754139bdce8404c9fd0e69bddc05110126ad9eaee410e6a8ad28f073479b461cd8e0b15158b5e6d17c063a8ae4a286fc7eeb1d9aaea2b83ea84d6221931e6acce35782e524e7316c162720252261cd398a8ee527a065072937 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part277 : Excludes 0x4010600000000000000000000000000000 0xdbf4b974cd02ac28f000000000000000000 :=
  finishCode 23 0x2246d14c3899c853851aa924be324cd64f232549eb3f490c2b108e9b95ab6a0d398b00980a7650697c5ab64f9524b609336a6cb553f49bdce627cf9cba9131489bdcdef2f8ca20e47ee5f19ab61c141393e528b356c152c0260d519452c21506a4849f29219a67064ce62d5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part279 : Excludes 0x4010300000000000000000000000000000 0xdbbe94e569422e0a1e00000000000000000 :=
  finishCode 53 0xb0270a6359e4a29bc412a71b27993f5bc651e8600e62781c062f88fdd272915630d3f0524e3a5cf578accd28a3f76b3c26b526b56cd7f1ba5503f1eeb353dc9e3f73809c3da9f30751fa9455889c75a9f1fdd22a3f7681405f160b461c7ee4d941c9c3e34ac61d3daa3b4f4a02524f06f53d272b4929c06588c7dd379c61d49e7316f17c5b1ac5e07ee947a306b311559cc5623357dc9e7e78c1ca4f3fba0e5c03f39cc51fb175cd9a83926cd0795b0e031c750133534e62b41cc504527a7b62f1ad4d20327b5ee6d67379c60cfd31ba4de6b6358e00fdd4271c74e02a03a3065f1527c91548ac3c56ad9c6d49e731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part280 : Excludes 0x4010200000000000000000000000000000 0xdbb49564490224081000000000000000000 :=
  finishCode 155 0x3c8de360c0146e24290b30781c85073293cdc691541cca3b771193205d28e70551da0e5eeb1f65492947501453293d072a8248e40b97652729258b9e3f75f0d7e7313828326733a494feef6b980651ac286b10a64489215248b5dab7286d0128c53ee9c4da57448da125e588ad4ce267c202624ba4e637ba02641cb976725a0e4e26a61bfe386a89e527a0e5304916c690586d4b96a6a2f380a4de6988f356a734c453aa493fbb545fc6adc3f749ba09ce4324dd28ebe28a648aa0e47eea298e03122d86cd37bb56e1c59c74de32d1d5c4c07eeb02c7647eb535aca2c3475c8eb96666bf16bcd5b47e9c05b0730a0eda330d627fe2f8973ce62713397b40731941aa270e69cc6506a89cde73124e6318391da6f36a5a834be27315f0dee72fa30ee454a3b98e5789f7541ad6208da1bdda7b1f3d5f62d74ffa88544e7136814922d78fd2c1750dc921c0aa292518397c2a560bcf6b83b973e30ed5b506cc1d94520ab12aa93ce5e9ff9cc272f5f144ea4f057ca2105aa9266f1c0601a058188404a0e5477283439a737398c945386a988a1cc6610a89d49ec5138d9bfdcc514c7311fbb48b299486d3d499a8863c1a42f8b56e3988fdd24f18387ee371398a05e4999cad4c51dca4f1fba8bd486c6328da1cc544f28ec7ef28358a2d4b4938fde51dc61e029a7b457a7315b18c7a07ef041cc5477293d8bf4605cde2bd527cbc29873162012ed5b898270171ec9eda30e3817b9b0c4e6f0326398b98cc1cc524513a3f4bc7290d85f41e5abed352e5a515cd62899a6a5e3513b55e527a8854865f15e1a7b290d632b452f88634e62923004f3513d1876a68b5d486a495a9c5e3510c2d7 (by decide +kernel)

private theorem part278 : Excludes 0x4010200000000000000000000000000000 0xdbb49464490224081000000000000000000 :=
  splitAt 1 116 0xdbb49464490224081000000000000000000 part280 part279 (by decide +kernel)

private theorem part276 : Excludes 0x4010200000000000000000000000000000 0xdbb49064490224081000000000000000000 :=
  splitAt 1 118 0xdbb49064490224081000000000000000000 part278 part277 (by decide +kernel)

private theorem part274 : Excludes 0x4010200000000000000000000000000000 0xd9b49064490224081000000000000000000 :=
  splitAt 1 133 0xd9b49064490224081000000000000000000 part276 part275 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part283 : Excludes 0x4000b00000000000000000000000000000 0xd9fff4a171422805de00000000000000000 :=
  finishCode 89 0x1945e160398b390a3804fd441b45205ce0c7947291359ea51e7a8b78d678c2ca392f6d1877a8cb27173b59e601845f124702ac172da330b315a3b9be6a6b09cf76c2b62da514d63309e30ee6f374c5ed6f164b2c9dacec576a6c8dd5a8b59cfbf2886028ad49a6e39272d4d8c2c5c960e9806e39422d67055c5ed135cf716afb15cb3607d49cb38b01984fd6f198301806d122ab33a30e3ab063acce51cad80c7960a1b751c9ba68c3930437f245418e7df51fa8ae6e1a6b3d7c366b495a9ad44f45a98eae6b3b5962f8b68de33118781269394a28eae582b4d549a0939a6ab518c3ad468c3a7f58048ac9393efcb53591ad8cc280882c8d69e3ab960aa035268eae08f807dabea82c268c2c1fd662d67515a514d7f34d5acea2b511aaf34d5456a4d83fcc03535aa327f4756d4f4a29afe4fe9f75a9ece3004fd5a9ce6d49ba4e446723f56469377b7ad3d5000ed07f3eeb8e568ef6349cc1f63719a556a6915 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part284 : Excludes 0x4000a00000000000000000000000000000 0xd9f5b581510220055000000000000000000 :=
  finishCode 79 0x380b8300e41005503898784be3208544b14956a69fd6a982edab71cc4a063f1290b18b62987620fdc840fb3073391de7216b2878540410e625b98db6b3115cd18569ac8ef8c29f755c023c6e36ad8bb4e62a4d9ab626d7205db1cbca0e725698c2ed7a198399d187176b4c50427130f0b56e69a8bb50425ed398b38b278e0a8211769a5e1dac1ed022b1b47e97b5ab6781496398b56da6e6f7733b594e630785880f08bb6720a364dda4992609cc646c97b5880f0c5e1176941ca36bc14863769c845da52191be721721586d10440fd1873989484e0a713661803909e0bc2004a2e5f160ec46583d9cc630f06d6398c60ca2f07b8e62c0378a2145d4c26db9ae398c61d07ee6b8e63187736c73150169341f5aae7318c1c57983ec61da56d6740fc73183dc525508a084e6283137baa0b82d9187a0f65f17209c9582e821398a0fd2731484be2c139ab6f632f89494e4b2c9e1428bc731292b57e155936d01e831 (by decide +kernel)

private theorem part282 : Excludes 0x4000a00000000000000000000000000000 0xd9f5b481510220055000000000000000000 :=
  splitAt 1 116 0xd9f5b481510220055000000000000000000 part284 part283 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part287 : Excludes 0x4480200000000000000000000000000000 0xfbb5d98bf54122401000000000000000000 :=
  finishCode 33 0x701805416c1f89c0961b954c16bc7ef398b09ca2e83f57184f30fdebb356c98682128bc1d9064c4c361c876505e5258e368110ecb70c41942ed6306094943b31818e520bb69cb54ca36ce3b0729a30272b28d94953046ccb3d598a0fe30323f630e6a1398a0bc192ba1e06e58d9aafb410a00568eb6175e3879cacd9b356e398ad3e3028015f0e62517927294541782ed8730a6524283f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part289 : Excludes 0x4080240000000000000000000000000000 0xfbf7d90acf0520c11248000000000000000 :=
  finishCode 39 0xe23b0f236061d989a62b3989484a4ae02d8605315b956286ac34e02d3784fea156a0b95518378ca3b286c3bf524c9ed71ca8f4e0262b398b98a0360c01cc507ed5b940ea495a7c2675618027cca4916bcb4f72acb314a19fbdab7250cfde83f581ab72cd58822b11f881f6761802fcad8d8140ce63356d01e83f733c0af61bb60d5b8e62c119ab6e6737fb4c66a49bb4e1ac3762c81e6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part291 : Excludes 0x4082200000000000000000000000000000 0xfbf7d9e7c53161511000000000000000000 :=
  finishCode 11 0x701a06adc90f064a0fc3c23f15e18c398b09e410a89d07e2b7963eb4f308a0c630fa8ed8c398a8867b7a0c547a921513c60e510b9acdbe93b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part292 : Excludes 0x4080200000000000000000000000000000 0xf9f5f942c50120401000000000000000000 :=
  finishCode 157 0x2e8ac278c61c4ce430a28a5948c3c83f1f893e4a1aec1c06308a8ece6e8ed945e6e5524acce499c61ce623f1158c6e58c39c054924f96c1b85803c2be0fc528f4604e66a01e07314f6c83f5a9803641f96e561b181598d1816b2c61dcaa0c969128b3dbc1926e549bca15410ac0be187e1f8a51e3027334f4c8ff6b29cc47e2e6146e30323fd05e6e597c581943998b5e2f7987c35b4605ee294761497be30fa44da45b11439b950d6394930717b7c6040ee6e571cb56dcdeb31a3030713e4acd5ab741c5662981f7659897e4e36dc46165799f763028d72dcc6068c2cd4b3eead4dc0681b07303c2982c0a60fc51ff356e30e9ed392a47d07eae20868c3acc4e4b1b951fb18191fe821064a0fd267243505ec271f8a43e729a514be2b02f898250fa1c95782f0c22b07966ae6f614a47d86e6e59636e6f48882c568e9f39696e6f30f8b26614b105276fa18463789ca4c3e6a1921e9db8c3ace437e2c94edc7257318841130570daf2d4d2665f9598af07c9960e2a54948b2549f0d55c82afb36bb9bd23f2c1d26673792771cde5a4b9bd266d22d8be1cdd6631b94bde6e5921b39bcc3e92147fcd535a9a9872565107f2434c3ef778f76d5b41fa89e410b09d4046114600e4aa3d527ac9e2cb82fd2729db91fae630ae6ada8a5252731690163310dabe0bf499b60a29120cf5d628abe6475bd85b0398c81f513c3bf541277284d05e90f49c949657ca07d426e03e81e17119438ec61d30f9c6e308af891f98b2a1538bc61e5a8ad08c28ee527b28861a74a0707b831e7ef4edc9313e4c4c384fe9db591b56cfdf07b627940d252c61888c2c0a3b3d13448bb57e2f89a8560eb513eec5935879bc6286930d42650d8fded5f378945d20717ecde22d738bb989ef8a2f071418a07ce62d2b8de2a4f584c717 (by decide +kernel)

private theorem part290 : Excludes 0x4080200000000000000000000000000000 0xf9f5d942c50120401000000000000000000 :=
  splitAt 1 121 0xf9f5d942c50120401000000000000000000 part292 part291 (by decide +kernel)

private theorem part288 : Excludes 0x4080200000000000000000000000000000 0xf9f5d902c50120401000000000000000000 :=
  splitAt 1 114 0xf9f5d902c50120401000000000000000000 part290 part289 (by decide +kernel)

private theorem part286 : Excludes 0x4080200000000000000000000000000000 0xf9b5d902c50120401000000000000000000 :=
  splitAt 1 130 0xf9b5d902c50120401000000000000000000 part288 part287 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part295 : Excludes 0x4000308000000000000000000000000000 0xf9fffcc0614038021e51840000000000000 :=
  finishCode 67 0x5e1b0651c4398b805f184731834828bb4de661d315a98a138dd2af18c18114be2d4d2fda50c5b960e9172f8c61dace91782460718c39f766adac145db1876279bcd9c509c8df83b8d849fa2ed4c1502fc81c6698b9acbe26f3608ce6b7a9b595cdb00fe302d5b509b685f9130cb1137984e5426c5b176ad46609b16d7c701ac6521430fa08942d261bd9364de68fb62ca47e30f04cd3fec375889364de67dd949ec37379ad4e627ad44d03f18b2e6d8fbf1856959bccfbb39b4de72787a3708e127ecb3b379a93dc9f237da8a4fd379b70c61bce6b2a7fc9fab3b5279f89c1bcdcc338f51be4fd735c387239cb11090a37cbe29ed27ec8df142b40e2461e480850e010b98d6227dd59d9fa491b39b5ec66f32fdcda340a434ae379ac4564e9c293e24c93f4fd3461e30f1bcd1f71ef56a3187 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part297 : Excludes 0x4000300008000000000000000000000000 0xdbbfdc8d614038601e10070001800040000 :=
  finishCode 39 0x65178890e62e01fde6ad8bb549a5f930ea7088210a3f526b4ce4a2a45e8c3b59dacf23c522e921a0f27e7482a45d4c51fd185173a85ce6ed35a30e3ab4f7c61547e72b611c04c17c4949c6d6a7187d852c4f41ca0263d1705b1252829923ea4d414c8298e6e80990529218276d353f393cd20a929701473313d052a2b387987d49b17eda05314038da0264149cde2fcc2e7176c5f9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part298 : Excludes 0x4000300000000000000000000000000000 0xd9bf9c8861c028001e00000000000000000 :=
  finishCode 159 0x338d6428407701345b166b2025842a3d38e9c0578651e8820e62e6f9012c4d176ad1e38dac0b11901261d6d05db293dab6b474ecc17103db56d2c157c71b490a02648fcaf1487a515012bc410ca13a68c3b8e523e2ed3989875477293c5dad379812d2b15eb544e36cc258d518e3690f4a293ce479b595cdf2f0cc1cc508482cb094a28f34be2b0308c39919f1876b3a93522e4fd9aceb09008cf71728c1ed272b098c184dd5f29038c3c94361ab16cfbab0f661082e6c4fd4a2a93e493a4e49e64f3978660c3a73133079ab259acf187493b1368c3b0ada9b183592ac3e8c3a844dd284270cc1e0945404cb11493c61e063abc566718796a2a398c3cb3371ca025242e6f6a6c6ad063b9bd623187851a05f16858208414a0e58431c6d28a72b176c6062468034472d67610a3c4e6e71b5315038d8bb6120b954b06c5126c9cddb8119d07701d84fd42a90326c8bb549e91580e691593ff34ace3a2ed40ba0e568487c94538d9cdc50705b4e6271d737a025b45e0e63245ce02a4f173ad0603d8ce028f1527a48683bb9b6246a7fe398d0774939c044e70a8d22a0b5489a0a5072731821c0611a05315038db6873751ecd674a1a43d28aa3b581253394d286e53928a61f737c489e23ce3fca4a5476ca389181969603b398a434c3e7dd942b39b561b1cc4ff2a3b5416c6c0e566e9960aa3d8c39cc528b1fe5476b4b582a85630ec02c1639898ad47a90f4a29ba6582a809e1cc635fa8f5ab741f4fba62b26cacc6315acf4d7ea825870160184f30fd22ed5f487a5153c6d0d7f23f586ea3b6b3c8fd8c3cd5b51dc695308b595406c0f035f9cc49b339ad696a1583ecd5b134a856527a85e2cb9afcbf2a01c3e090987d646731526a85547b07f91e2d37380b087314a16066122e6e94a1c6162f89f75242c439383ddce6b83eb98d21a6e949cc1edabf17edabf17ed4260a9374a108f17b7c7bd6959abe61cb91d4268fd8de271b (by decide +kernel)

private theorem part296 : Excludes 0x4000300000000000000000000000000000 0xd9bf9c88614028001e00000000000000000 :=
  splitAt 1 99 0xd9bf9c88614028001e00000000000000000 part298 part297 (by decide +kernel)

private theorem part294 : Excludes 0x4000300000000000000000000000000000 0xd9bf9c80614028001e00000000000000000 :=
  splitAt 1 111 0xd9bf9c80614028001e00000000000000000 part296 part295 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part301 : Excludes 0x4000290000000000000000000000000000 0xf9fddd22d310620815cd200000000000000 :=
  finishCode 45 0x6e18c5011454147aa4f6adc0bd4909ccce2e5f16adc0bd3999c5de46617c580e42a22f07256adc0b18c3d1878a0e0b1514b4e671db944a42a298fcf02adab6d3d514b4f651497c6146f1a9b359dca2e3b286945d046617c5d00db41f5ace725397c60638bb9b5cc65fb62dcf51389b9b4be2d3d9cdad5b5099c1558730b9464fca9245aed2b9ab6f712bdb91cb26e41c965099cbcbe2c428fe512a84c162c358bf6a135c0e0b2885a8af20d564f6b964a426f18be25f18a42705 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part303 : Excludes 0x4000218000000000000000000000000000 0xf9fdd9e4e300700a10c53c0000000000000 :=
  finishCode 107 0xd82b8bc330731541282f8a58f518e2eb076a6a45e00e82b402e801397a0062e7941dc8ee634a0d4346151bee6d3ee82f5426717397cc6338962d45c8f0d9c9068df8c3b59cdee81f509c0ab37bc1c60a7b56dede0ab0aea84d8471ecb037239c15a8a91723ccba428c02b05c1c4e4fca8d4fc62fc5f1283b98d492c434d62fd97c4a0f1879cb272f7b397c630f461e16bae076461e40f8b5e8c39cce2f7c61c12b2045a6a2c56b3c61d50601102f8ae0d5b807a72f253bdbd49e7f1410a9266adb68e47947aa137904c2f639c8eb1d7b7c8c2f91879ab673338ba7649b2c43902318737b819d3b2a29407ca279452d5b3999c5d045d0e83b0dee28b95f617b527819df4500f77316c736a2926cb10e71db4f64a1c28b836893146125330adc8e8df5a8a93dabec138e26a138c3ce452fd8e6e524b59e728b8ec9b25fb271287461e302e6351e9c5d426f6f850ec498b53e1d6a45c2f6a3da0f67dd8c3b53c75a917736c8df2dc8f3547b0a110c1d9252a3d722b985745315849dc2d7524b68d5f8f7ee6d2bd9615c8e5cf59382de58381852531877b0b39187514ce4705bc6166b3b91d187b7a4ee8c38f34f7f41bdc8eb1d561b416ba8f6399b0768c3ab81af964f1851a4c717 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part304 : Excludes 0x4000210000000000000000000000000000 0xf9bdd988c30060081084200000000000000 :=
  finishCode 111 0x318d8103d5c530e62961cce28b9c5d01e82f511b42818b5e4788a65062705515c91537ba0c637ba844a2f04368a138e4270528bc57b72382ad84e6f7723cf5127ca3ad505b12c3c11d683f6d1042a298e424d99ede24f723cb3928ba8ae2689c5ca06b02b09294a19bde3979bc6408c9d916bab0a4f89f290d5099c5ce42a3d9426d5b38bc28b0230a6461e6219bc4a1a92949dc10cc1e0a0368b2791d6afb397a8a558286c6f7723c2994ecb98e30ec5b475a45e286c8fd8c3c61e6a6a84ca1a9db8a1ad67475c10ac2f86f78a1a2d7735b0006386967bb389b56d69650d4edcd4d6d1a9b1c5d44e3679672e4791d650d366ab082410ba1bde382a43672385aca1b07b1b3c8eb366b95c98650d9cc23678986c137a8a082d77b8d1872fdc61e7b78a64d8ebc280f21cc5d8712082929bde399a3ae16ba7f5cd6d5b5b1002d5b727ca4d5a2d0799aa6b2f83dad3c9f2a620066adacbd804e0e02f8ad3e60b86d541ab1f71ec1b57279808eb921ef599a5ed636a9c503980790e2f2004e2652127cae8cc27090f5f0be2933046c1270028b15a5e5d772c93ce002c61e16bb9ad4865fb2fdca21498c8fd9ed6e6b (by decide +kernel)

private theorem part302 : Excludes 0x4000210000000000000000000000000000 0xf9bdd980c30060081084200000000000000 :=
  splitAt 1 111 0xf9bdd980c30060081084200000000000000 part304 part303 (by decide +kernel)

private theorem part300 : Excludes 0x4000210000000000000000000000000000 0xf9bdd900c30060081084200000000000000 :=
  splitAt 1 115 0xf9bdd900c30060081084200000000000000 part302 part301 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part306 : Excludes 0x4000280000000000000000000000000000 0xd9fd9930511022001540000000000000000 :=
  finishCode 89 0xde1026145b1584c0a1abe13e59c4d1493205cbde93772ed187524a09cdef0b5d404f2ac3636b899569e5b90aac26503cc61dc72e3b5f14c737c38f5a797bc5aeba461e05ba496481c60475a9c1509458c3ce6d737ad2e71d80b55f292197c67160500c57356dcda819414a5167b7ac3d04ee5171d97be40bb95dca2d395e1606b10c3158a4e62c9c5e3032514ff2e6d38ec9db302ad2e728b95dca33b0e41c74c3b2ccd266b516a2cb093d589c5aa724cdc76e6d58100736cc41414a0257c4f05af395d0727dd8e2e925302caf3524a4857c71dce5162da494c56e42bce6a9b135492921506cc2b46cb9459c571ac41382c641497bcc3e0b598b6829302b582d79caec4172bce6d50ac60530fc48fa3b0ac187cc3af6b94921819ccee6d8c3a18be01dd24b1ef5edf1812eb9c5d60f4605ede26b389b3836da30e92505b97bd6a26e5a30236d2f7ae89e59a46d3371ea4dcbc2705153ce6171dbd9cfd31812f0a887e9949e5b9492aced6a2be0b5e49bb8ee583b53c322a4f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part309 : Excludes 0x4000201080000000000000000000000000 0xf9bdb9f441e12040180a440310840000000 :=
  finishCode 149 0x1043e8ec358bc328d21874c568c1c4e486b8e5452d5b598b0d4e02ac2d89db9ee271339b9fbca1a9218b422897af9bdc4ae7131a6d07b261bd44e56d5b0a8cd6561aad1d605d0c22ac2887134d0e662618fba8fd0169c04e56737823b187380ca15728c605503c142b39b528af63487c945513cd5b7369c95803c14046142b293cfd31cde8c0b945cdb18194767f9728c6068379cdd80501ca2e6d5d142aa278e42f6f8fbaf6f8fba72b96c30f9cde286a4c6851945b160286a60bc34060557024734cce6e7f95989ca609180053b71875a580f601dc7295a5d1874a2a45d3b6c4380f69db380a89dea272b460543293c4c6c35626a45d5c580fbb461c4a66fb6a6b59d7448ac2311d5ac453d6a27261acc51df39ac98618b486a89e1a680f626cb945cda96181549ea154edce576a6bdbdcb3348da567f96d1745f13c392a9872f61bca4f62088ee8c3bddd3fed67720a45d49ea15958500e269c356d42a02b927318158f80b61c5b4dc6c71b95a6f18149cbdbe0fa7dd49cc9ff588ad1d68651186adc5ef7b79f7522ea1538bc91f737c7ef50abdbce2f24c5286de247cff3461d2428eb8c3c05b3729f742c2ca230ac245d276b27892b18727c9c1630f35353b672569a9785bc560e2f1fe4e2650d7a0e05919f66699ad3cdf71c5c75734d4e2f1fa4e4a782f8d61fa63929ef67b1a40d6967f9728b9b4fd33dbd47ae51401ca29218e4a7f9490c7255b1946014c27c9435a6f16e5286d6797c4105ae71d966271d9aa32d1da96ec3946366a794e567375d0b7302a568ee519ea718723ab545ac5d194366a98e579662943598cd673fcce6b2dc8b2e4989c6d4c1a6cb31498a3cce364c3922e7f9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part312 : Excludes 0x4000609000000000000000000000000000 0xd9fff9f0fde0b042f96b0c9200000000000 :=
  finishCode 47 0x891b45f144460e2e725599c4d95a8a4c6357b56d202ca2e81319286c298c3a9256225ef05ba9907792862d72f7a6118793f293748ba44524b461d1be7dd873318131118430dcad67947a2b7389973d6673dbd6a6b51431ab6c49a30e0232619c4cb9e9ff96227e9a302c49498a990a1d891f7b8cd5b733c1bd89e9479acaf71372b8ee6b2b92c0f64d92f7acce6b2a45d24ae6d6a6c61cfd28c37098288b42d450c6ad936588f35460eec497b7c1816a8864e14c8add666d519c96b0726ca4dc56eb33a30f39060fa1b3492863d85e2b75d1ab718784eec49733c61e13b96e563ac49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part313 : Excludes 0x4000209000000000000000000000000000 0xd9fdfdd069a030421849049200000000000 :=
  finishCode 135 0x1b45e2242f6c605176af82d54c1b8460ec698d18716bb92da6e93759da984d916bc5a549ab48da6f251cfd27e9926ad654ffa4dd83f399daca9373f4a4d5b8461a6734ada46f7759993656766b58fb29ff7bbbdae6b3b975303f4a836510b5954373976245f1f4711b830fa30b4140a3d38142ab538de6a490b49c8d658fbae6d578c6fb9676e615a99f74fd3348d286d3759dae892340a072813c3f49abe838a37d3feb530d5abc6736ac46837a37d82eb5358ec1dd3ff289dcdb0770a2d06f480b9b563aa272c2c27346fa182a395f70715a9b8f5ece04d37da60f6f91bea216a8c6066afa37da9a0516e1ac5d0e4b461ce668c1c5e599a7b56a2b1d8fd24d99a6eb5158eb596399ab0b82e8cc37072f3d0e0494a37e57db0c52629ff944e90160cc901513a8f50c7b3ce3d727a90e0dec2f006c1ab1478a8dcc718760ca7fe728a86ce06a7ce3b6b39fa5c774605253071617bd8e119a7b5cda5834fc9fbdcc286289d47b187733cc597229fbdc7724c558711ed72925ecf1b5d47af6b8c3b99e2e79fa630e8c370a22f8b3b561a5705b5a8ab3351e8b5cf73348e30ef6b9c76d2b8c3a8f5744914431819cdac5916ba90caf3359c5af248a2260c29983e5b76b28234e44f9cd456b3cf6b0d5c6062dfa90daa21899acf0715d124733b59e3f49f74356a07151cf632c1a89dac56183f0b5dacf3164fde5838d5e8df531308915e3399cf769058c3b594c3a61f561a631f75aca2d7460a05a89bce5999fa630f0a95a661af045a18c4f0c1cf7160bb4ce3f4ac75cc29058f76f6b30e987ded727e40b6d5b8c39bccfd261d (by decide +kernel)

private theorem part311 : Excludes 0x4000209000000000000000000000000000 0xd9fdf9d069a030421849049200000000000 :=
  splitAt 1 118 0xd9fdf9d069a030421849049200000000000 part313 part312 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part314 : Excludes 0x4000201000000000000000000000000000 0xd9bdb99849a020401808040200000000000 :=
  finishCode 45 0x428417821785f05ce2ed5816841cac1e69bc1c44ce9f94a39c6d4371195aae9234a3a49640ba4ddcdf123429223f6a6a4e5436921517ab0be140d5c8c0c70d41ca86e695a925a6e90f386a86e404b409e2b870d928a817460e1ad2b942aa4f722ce638c3a0255f71818e1aae289dac72515cdb243d7c5700a73d8ded706f39ba0a568e8394016c40c82c6167943563b39b5caf39b56c404c50d517c8097b3ab8b1198563cd05ab16d226605414a0e500560bf281951ecb331e6a51dcdb28ee527b9b5abe605 (by decide +kernel)

private theorem part310 : Excludes 0x4000201000000000000000000000000000 0xd9bdb99049a020401808040200000000000 :=
  splitAt 1 111 0xd9bdb99049a020401808040200000000000 part314 part311 (by decide +kernel)

private theorem part308 : Excludes 0x4000201000000000000000000000000000 0xd9bdb99041a020401808040200000000000 :=
  splitAt 1 103 0xd9bdb99041a020401808040200000000000 part310 part309 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part315 : Excludes 0x4000200000000000000000000000000000 0xd9bd9991410020001000000000000000000 :=
  finishCode 41 0x37841179083ebc140ca2ea1785c27316b1c9393f8bd7578613c7013029cc588729c9e5380b09e791b4671c4173a84e514a3cda466fb2f8a7cca0e862d082f3eecb3b2f8a89e0df3d8e8c097c6244f0e4b1818c5707f6af899dcce821397aa061f379c4d94188f364f2c605505a180054cd5b1309cc630ea0103aa0c549e82f2f8c606410b99dec6a152d2c6f37aca7fce62c37410a93e398b99d4c283c61f2f8c6f3398b52cc56d61cc57c50ac5fb6a8a0fd86ec59379cd5150ac6f3 (by decide +kernel)

private theorem part307 : Excludes 0x4000200000000000000000000000000000 0xd9bd9990410020001000000000000000000 :=
  splitAt 1 108 0xd9bd9990410020001000000000000000000 part315 part308 (by decide +kernel)

private theorem part305 : Excludes 0x4000200000000000000000000000000000 0xd9bd9910410020001000000000000000000 :=
  splitAt 1 115 0xd9bd9910410020001000000000000000000 part307 part306 (by decide +kernel)

private theorem part299 : Excludes 0x4000200000000000000000000000000000 0xd9bd9900410020001000000000000000000 :=
  splitAt 1 112 0xd9bd9900410020001000000000000000000 part305 part300 (by decide +kernel)

private theorem part293 : Excludes 0x4000200000000000000000000000000000 0xd9bd9800410020001000000000000000000 :=
  splitAt 1 116 0xd9bd9800410020001000000000000000000 part299 part294 (by decide +kernel)

private theorem part285 : Excludes 0x4000200000000000000000000000000000 0xd9b59800410020001000000000000000000 :=
  splitAt 1 127 0xd9b59800410020001000000000000000000 part293 part286 (by decide +kernel)

private theorem part281 : Excludes 0x4000200000000000000000000000000000 0xd9b59000410020001000000000000000000 :=
  splitAt 1 119 0xd9b59000410020001000000000000000000 part285 part282 (by decide +kernel)

private theorem part273 : Excludes 0x4000200000000000000000000000000000 0xd9b49000410020001000000000000000000 :=
  splitAt 1 124 0xd9b49000410020001000000000000000000 part281 part274 (by decide +kernel)

private theorem part245 : Excludes 0x4000200000000000000000000000000000 0xc9b49000410020001000000000000000000 :=
  splitAt 1 136 0xc9b49000410020001000000000000000000 part273 part246 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part318 : Excludes 0x24000041000000000000000000000000000 0xc9b7ba2a0c2484c84808208200000000000 :=
  finishCode 35 0xe63f8d63482d7859e4170ef879e203f3c50d207905d7c074b9b671d8addab63df15bcd5b8212c0748b9d07317dd0733da586320e459ed4300a00b5c9f250d517ce6f155a92435a7e3a0e22b7631747603a67018592b098fc6a294768adda8e7379a5b3da52462c90e9cd5b16bbb03a785ae50d074af8ae0e7e16ba09d88335858b22d7720c5f7350a365a8ea49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part319 : Excludes 0x4000041000000000000000000000000000 0xe9a7ba080c2400c00808208200000000000 :=
  finishCode 141 0x7a1fc70208291c00ba03a41d67f99ed229b2fc97dded3357d02e8394605aaf698e1ad454929c758271cdd24a4e5167c9310fbb98d64405ef87de40f0fbc290007cdd816bc0eb25dc16b2c6a365286183722cc4d16582de0d68f7c3bea3b81d21f75f01d23e3949e5fb272cd61761a8641c0581ac2fcc0062b6016c733c0af61b940da0620b596153b99ce1a5f79ab657d9eeee5d6ad8a9daca2c962c9ca637f8b25686816971434dfe70d510d07748fbda540ea27164c9317b4b58b618ae0e3276dee2d2d2869c051db0f8dab6d02d907193b6f69586bdc51dab4b3949435a6f3da4dff0778a1af69503a6882358b617ec2b71394a1ad2d5c14763e394528d7486b10e371ed305ad40ea3b378a8ee246863ded24e55b174286bda63f7ac9e0e3276dabe3bf7b89fbded2b828ee6afa4a5a7aa2987c6c03da56c7b0ca136aa8efca1a3798d8a281378a76e376a4a5ab67bb033c1edc460174286a90e6ada925a7b1bc5ab6be074e16b97edc046cc6a12339c34f7690d39bbdae3789eedacb3889a0dbe16bb56c7c65ef3039a88a1bb45af1bc563f276ded2911488c7296ad9ca6376af8e6318d0074d22341dcfde2d7586cf594a19fbcf05a3c4d957d8b5d2866ed5c123f281d6622d749897be3ddb56d3e68d962cc16727cb4845aed552f7b00ac1d04f93e4cf53494b51dcc50aca217b4ac251b2a4948fb58e46ca9255f741c540e067598b51d1db1eedac290d7f17c0fba01e40b8bb6696bda4dfee2358be268e6382c2061580874cbc66135b0c571818e52f676b0acc52627ef6adc9297b4a08940606626b4e5ed290d4a1b9566adacf52771b14fdea29527ab0f5994769ff7b3a924a1ab5393fe6051bba89d21af69696c5f7281a4c4e1a93b (by decide +kernel)

private theorem part317 : Excludes 0x4000041000000000000000000000000000 0xc9a7ba080c2400c00808208200000000000 :=
  splitAt 1 137 0xc9a7ba080c2400c00808208200000000000 part319 part318 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part321 : Excludes 0x4000040008000000000000000000000000 0xc9a7d205080411800018021000200040000 :=
  finishCode 151 0x7f2246b1c066220291b98ee1cc61420fb001f72fccd5b7ab9b943724e508dce4183e97e582307f2fccc11614b884998dda947260b12662fa7f5d8800c53149526f27e526a70f272c819491b01003b0ee3a0e203a43e727f45aea4d8142d5b4fe83ae50bc1b958a93664918ace263b58c5961b9771c4162c2d772ec0e97112471304933428de440ee3984f39ab601f6afa50ce6e41f0fb902638783ad886b0c93717692dc9e6c439ab69252f6bdd540e0eb83e624f84aaee0b56626b10d26e607074b20d2398867312f6a93658aa48ce6310398ae400731771a4075ae0a1b9632b556afad56482c6f150dc5075503ee0a59ac707b517b57c7c66e3a0f6ee3501f75c18871ae4fc62d7494a4ed48724156aa6f18307356c9e64a3801dc3f1c37951097ed6aa0eb50dc4f36a2ce63790007cd69f03ac5af07f9ab628d6b18a941d73516075b28ee1cc6148003ee6ed91d28db512a4c4832503380ce559cde5f9074a846512bb80eb83eeb058b22f5b48893f45dae8410c003a568b357c81273196aa411398c41939bc0eb7315c6a0e6300378f21c361649484a4ad5f8e02a07378b56e49d97bcc56ee3802c98bf670d38e97ee7b4b58cde2a2f94866b59a88018076124292a8be62d9c6c9e662b8e6e6ff1f8ab0c379276d5b5178fc54423f1940e9479ec26ed400a3b4a4aac1c3c5972c347c6a214f9a51d3e730dcd6b350ba2b100290c9f30fc5442507052c3a526da884e1eec23662929814c563e39a5af777b48fc540ebe356e7bbac5cc56f692fdb16e2909ad6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part323 : Excludes 0x4000040000040000000000000000000000 0xc9a792110e8400880048000408800008000 :=
  finishCode 105 0x440f4398ae3f87311f7c5235d1bc511c40db97ddaab1494bdaa2109bcf69737b56c593288507e1c341fc9f952486cd03f20c5ab6d63f9003b80e9882241f640a463f99aca83f283cd310efcc82e08838881141894963039bb66adb8883f8918571814c566a19486f5b8fc62c9725c00be141d2231bb41871c763728f8da86988b5e2cda48d4866ed91dad5b772003e1cf7751f94941d24115503eeb0251dcdf1ab4da2d579cdef59737c6ad3f8c1c53fe507880312358ee148e0016bc4f929090257c4c148708d51b270f7bb98ac9ca9354a3a4968c1bd65a4662b83fc61d2729c3d8ae9f950dc521524c00b4f9ed29112909004812be2e8935492cf693f1a4965869c3d696d23272c9dd2f6a925247209c1d2409741e4711dc290949502317bd89ac5b4a1907c7c70bb5fc60083225780ea5f76b2940c802e6f9ece2632e797dd6a735940f2d5b4a19bb5dc204c81720fb88b03004f35abcc5b521b16e6b0bddcbdad5b2fbb596236c1c46ae0c31d7a36411ef775a097ddab65ed9ab65f76adcc5740b97dde86901d25233dbd0770608b5cbee1e772acc397369f8528e82f16bbb8d22f81e7834c0b91efb5962fbad558ae93149d8b6e4a1b102b99ab64d57bac1c3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part326 : Excludes 0x14000040000000200000000000000000000 0xc9afb2318885528044080010000540a0000 :=
  finishCode 39 0xf4448cc4105234317c731246ee42870f83e60eb628c1df40fc92526cb16e580b97600586cf695a7b15c3e60eb83fc70f47fb915dc492cc4d074a49662692dd300f986560d4a0fc5af3da58a23df731bc074c1df0f983ae49b83ae7603bf03a41d6a828083f6107a2b4598ae29f59f830d1b338e671da365ed2b2f7338ac45af16fc7beda39b65008b6c3ce1f3628c93b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part327 : Excludes 0x4000040000000200000000000000000000 0xd9a79221088540800408001000050020000 :=
  finishCode 123 0x2007f1dc731bc6b0e631c043ee407207944638083ac3eee83b0d003a56c208a0be4a1a0fd2771cc58b7460d4365234179cc4a47207ce6282f30ec731075b20f21024a4b28054520e969158378cd53524a7e417ab3f5aab91e7b493cda567e1a14701e87917c075948e4918b5d1b3148da9339bce6e5234fcc817378cc432fdb58d8a2525291c2d7701d874184200a6052383fc93760c8bb5222831176c1c328dc4d9580bdb1f7c98252339893cca471cc528f41fc8025237618885140279ab8f21cc4d42929276150b57da570a85ca334adabe6c591ba7e115cb486292b00c241ee3579cc40e6d2b260a07dcda0bd588c83f418c731690cd2b736a0c4e6281f9d879188527c91316b941ca4ac0391e4fc8aac592731290bb894398b67313719c34e631b8d90700c5720c41866e31f8a0465109cc507e5fb8e62613378b20b4f8b227e35109b951fe3f141fb58616ba7cd1fea4946cb990a368ee3581f754183b1bc4e6270f41f82fe3159bc4e62c1d9cc2e634c1ac70140e8315a7cb1b2f6ac2549294705fc81f3f8c8d92c8a44d49273183dcf69131a77ce624b750d87de7710630fbd98398c1ee40f948c387380c2358b23926e0c3291ac8e71cad3d24a6e55f10c77126ac4d943670f50dc70f9aae39d6a2b1354931c3d7c61149f17ec166f5b949ea4983fb0d589a6f195faaf36b0b0d5abeb1f (by decide +kernel)

private theorem part325 : Excludes 0x4000040000000200000000000000000000 0xc9a79221088540800408001000050020000 :=
  splitAt 1 136 0xc9a79221088540800408001000050020000 part327 part326 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part329 : Excludes 0x4000040800000001000000000000000000 0xf9a7f601099640b0020a102042040200480 :=
  finishCode 29 0xae378e64001f7398b95e2fba495eea5113f8cf754898bb4bef0a348d417de007bac92550da92481252158149327ae0fab4b35786d55ef1f8d4420b5491c1635a783ae488a885eb7136cbee401074848672884d45da5070759cc608771c0074b40b19816a94739b9b4672a9364e02a2781670a41ee371946ca0e0b588026f19262525 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part331 : Excludes 0x6000040000000001000000000000000000 0xc9eff2038a8e42e0000a800000040200c00 :=
  finishCode 29 0xe6440ae378731363c1c32fb8fbdc0127c80f303948c1d3166d6361b3801dc488cc1f509a07c1d240f61106302fe0f652349bc911200a0c4a4720fc3bed23b8e224d65a9948d28e0e90efba081f81d22ad949e0bb4c0a4691189b29372fbc0e998829183a547f02fd3b72cb5cae1bb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part333 : Excludes 0x14000040000000001000000000000000000 0xcbafb201988742a8002a000000040200502 :=
  finishCode 65 0x6f1a45712c730beebe3b890da30ac136ada3643ce0eb1efb08b6148d49b0f8d07e0c187c64d526cc937491a76672b9b1507ed5b26a879c1d6ee3800eb3f0d07f46cb91526a52383ec2cb0d7c1f608eac05ab6c4d49ba48ca46ee448ca398f407cd8331f0c1d6523620e1a0c196022ad0dbc90d6101d63db9eb68dd509948debb348c59692581d61b7813a1e7075ac85230dcc12d7ada8fc9aa3e35a0cd5b7ba830ddc891c46403e60eb91b283f498c7ff291a365d8291b98e698a0c41d6d5b9a628db075c1e7698c5236adb98b6320883b8831891287173ca461f3733cc475148f7d28e911982e2b97adac7dab6b052e7c6ff7ba8f7d03e83f7a1dc58bc8d9617bddda622d7075b56e052a8fcb9e4d54a3973e053a50e07593564a3948c1d6c5b9ab6d3d26c9354a460eb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part334 : Excludes 0x4000040000000001000000000000000000 0xdba79201888640a0000a000000040200400 :=
  finishCode 127 0x400fe398ee3785238e62701075901cbee40f761c0075893e407948ce624115b0e6320fd4531cc503f1045d8621e42799cc66ad949424327ce0e2c1d593830d07ea497ac97dce62d5b7a194371c7e36ad8f8ce62c23486465b56c9b29f34078bb4a46a499436b014929005ab6d2258be17dd6c176b56d6828d9901e3859eb22338472521600a4329256aec5b80cad613718bb5cdb0af5c0524cd5b4a3948d8931cc4fc6d5b40fbb8d5b940e81720494841d6c414466ad946d49341ec802d5b290b98ae3d0de1cc5c42fbbc81c32f6ca491ed9494fc71cdcbda1b79ab670d551a631bb5ab61b341fcd31711e461ac1d36a897dca425255b17c1f8ca496b2869cc26a499ab6831527c62b510a924e1b24ed1064150341a8408ac0ec1876279b56ca0eee356e50ab52e407b54650ab56d42b1b7dab6e2356d062d3d94525073f1c3f1710a4b356ca0ef5d901ed5b362b4c51b31445a62d5b640c86a5ca1341fa4ed45280f942683f3ffcd316f11b324d4e52d5b28894854930f4ca0eae258fe17ddcc4307de7317bac7ef488a0bd49341f5ab62ed61035f148d30701c8b2365c82a01524a4d51bb2365436a4946cca1b492b56c7c71ca4e62fe368e63283ef291cf751f19cc524b148dc04c0a469378e1ee63521a496387bddcc52d5b723d07d731b56d4263e35a7c70150db56c96e9351f7a51e6ad9cc41667297f1c46a03ee2cb9ab65fb314a8841728ed986e947368b56d03f3d75eea4e5291a0fc9b31b9507e729 (by decide +kernel)

private theorem part332 : Excludes 0x4000040000000001000000000000000000 0xcba79201888640a0000a000000040200400 :=
  splitAt 1 136 0xcba79201888640a0000a000000040200400 part334 part333 (by decide +kernel)

private theorem part330 : Excludes 0x4000040000000001000000000000000000 0xc9a79201888640a0000a000000040200400 :=
  splitAt 1 133 0xc9a79201888640a0000a000000040200400 part332 part331 (by decide +kernel)

private theorem part328 : Excludes 0x4000040000000000000000000000000000 0xc9a79201088440a00008000000000000000 :=
  splitAt 5279 107 0xc9a79201088640a0000a000000040200400 part330 part329 (by decide +kernel)

private theorem part324 : Excludes 0x4000040000000000000000000000000000 0xc9a79201088440800008000000000000000 :=
  splitAt 1 81 0xc9a79201088440800008000000000000000 part328 part325 (by decide +kernel)

private theorem part322 : Excludes 0x4000040000000000000000000000000000 0xc9a79201088400800008000000000000000 :=
  splitAt 1 90 0xc9a79201088400800008000000000000000 part324 part323 (by decide +kernel)

private theorem part320 : Excludes 0x4000040000000000000000000000000000 0xc9a79201080400800008000000000000000 :=
  splitAt 1 99 0xc9a79201080400800008000000000000000 part322 part321 (by decide +kernel)

private theorem part316 : Excludes 0x4000000000000000000000000000000000 0xc9249200000000000000000000000000000 :=
  splitAt 4490 108 0xc9a79200080400800008000000000000000 part320 part317 (by decide +kernel)

private theorem part244 : Excludes 0x4000000000000000000000000000000000 0xc9249000000000000000000000000000000 :=
  splitAt 1 117 0xc9249000000000000000000000000000000 part316 part245 (by decide +kernel)

private theorem part210 : Excludes 0x4000000000000000000000000000000000 0xc9209000000000000000000000000000000 :=
  splitAt 1 126 0xc9209000000000000000000000000000000 part244 part211 (by decide +kernel)

private theorem part182 : Excludes 0x4000000000000000000000000000000000 0xc9009000000000000000000000000000000 :=
  splitAt 1 129 0xc9009000000000000000000000000000000 part210 part183 (by decide +kernel)

private theorem part152 : Excludes 0x4000000000000000000000000000000000 0x89009000000000000000000000000000000 :=
  splitAt 1 138 0x89009000000000000000000000000000000 part182 part153 (by decide +kernel)

private theorem part116 : Excludes 0x4000000000000000000000000000000000 0x81009000000000000000000000000000000 :=
  splitAt 1 135 0x81009000000000000000000000000000000 part152 part117 (by decide +kernel)

private theorem part58 : Excludes 0x4000000000000000000000000000000000 0x81008000000000000000000000000000000 :=
  splitAt 1 120 0x81008000000000000000000000000000000 part116 part59 (by decide +kernel)

private theorem part0 : Excludes 0x4000000000000000000000000000000000 0x80008000000000000000000000000000000 :=
  splitAt 1 132 0x80008000000000000000000000000000000 part58 part1 (by decide +kernel)


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem caseBR (c : Nat → Bool) (hp : Pal 280 c) (ha : Avoid 280 17 c)
    (v0 : c 139 = false) (v1 : c 134 = true) : False :=
  part0 c hp ha (insertRed (by simp [Red] : Red c 0) v1) (by
      have mask : addedBlue 280 moves.unary 0 0x80000000000000000000000000000000000 134 = 0x80008000000000000000000000000000000 := by decide +kernel
      rw [← mask]
      exact added_sound moves hp ha (by simp [Red] : Red c 0) (insertBlue (blue_zero c) v0) v1)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part338 : Excludes 0xa000410000000000000000000000000000 0xe5bf70826a81e0148208200000000000000 :=
  finishCode 49 0x572206c1d4398b70e217be3888bbce5ad2d90424c55a4a93cfbf24543bef6298c81b6662f974503e83f624c7db2c5936e481c61cdcf28f5476c496b0ec3888bbc75f1c9daaa7ef735cf69393bda66179c9ce5ad6388a80ba43bf187928aa154179f6e594b4ce3069e207e527aa098251542b2cf5c9f01cd1e282f7b6c8f1262a8555051dc2c149ca5163072c0da5ec45057b88ea3b8727396b06651ea8ed65e1df358d07f08e849521f07d83db104659edaa1540fc60cba22e9513cc5f77161f1bbd5f6d5d83f82fd42aa4f44160f17450424dba0f6b49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part340 : Excludes 0x8004410000000000000000000000000000 0xc79d32e24f01289a8288200000000000000 :=
  finishCode 87 0x318dc290c21c9ddc7b17c8903ae8e250ded32be589290d6ad9c45ea741ed892f539892f7115fb11d47b293c7f6d5b0f1a4ee440e220899ab6e65907e17f7b4caa1e8ba3da4bced358f8672d0e1c6065138f3ce2282f817ef69396a50823b8f699a669436b1aab2ccdc86d5b41fbdde60bb5560f627f7b4b4ce592bda47f702bd6c7b15040fae8b4354e058b58c5b26f589f2c2f37acf6926bb58e2f3af8a22386f59ed24ef1dbae8d202d61fd82c6617b56e2f3b4e5ed306c4b9ad536b193be2f3b58e245a07f734fc5826f569cb54d74691ed30fed6373d75ed2b275109bd67b4935deeb292528a1e3611a4811b81fda90901c2d65f1f44fe2f692d0c2b9618cf693edcf6d095c6060dad5b69cba07a288c01c2e6ad93e5dc7b6cd5b58cad14d2f3994fa6c17699bda5892d3f9276b557b4ac9e8c1bda49f29319482f3c3a162fb5758bf24a49def69524bda6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part342 : Excludes 0x8000510000000000000000000000000000 0xc6df72c3ca213010aa2a200000000000000 :=
  finishCode 73 0x102440bc388731691b82019c9e83d878ce5a5ef83c680d6adb70c627fe393a47ce5a5ef8e1680d411ce490339bd42de68278917901a92940ecd3b605cd5d57d82fdb87114c201a47e0f1a50d87b131630e1e34a13c8c0c6ef839aced22e80d4a1ae85bb942b18148f9bbd006f6d9ed291f3779fce83f9f7cb1e81337797be0f1900d880f1b1881d83fcb3d57d82f4fbea155278556605abecdde833494b0ce6ada3c5252aa278ba17cd68416c70b61da4c507af77919e81361d9cd4ddf3094e16c554a1b10b42e8f6d9ab682d41eb7080d7b4cd2d385b4ce8c2b53e302e237091f8566c3b39abdb66ad9bbe61db56c0f2e2318d5983af1858b9a8dd2f19c2dedaf6da3068036a3b585802f188377bb872740ec60e69fa47cd63397e0fad2582e707d393b5760ff3da6306d5b48b82fce16c42e8f779ab6e5f6b3b4ed6a6f69a0f62b3406a4c66b3a45e0f6d3b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part344 : Excludes 0x8000410100000000000000000000000000 0xc79d71ab4a196010a21a202820200000000 :=
  finishCode 35 0x882045e154398b70ee278735186a3ee4f5979d4768fb903e8239cbe403396a68ea2e8d5d9a92c4b411b90e6b1c1735aac0630b1b9960f71c2d492dc23ee27c85cd07e735186bd8b629825f82def716b1878cfb683f8c1c4f96b1878d067243dcbe17390c7709f25ff59fcf695aaa9267b4a8be5aa982c9f2ea1f6c7d7100da4b208505ea3b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part345 : Excludes 0x8000410000000000000000000000000000 0xc69d61825a0120108208200000000000000 :=
  finishCode 141 0x6e1885b0c32ae18be20780e6307f949f07f861aea397e174b11568ef695a9cd59174cc19513c1fdd4201c30d3939c02f551ecd59258cd2551e82fe2081178710e62ea3e8c60c353f341ece4e72d201c4f98e4e49ba0e27d162fa4ec61a7e38fe2385032c1fc98a4f941fb88f00c35cdb250ce6a693945f07f0c1b184f9a0fe7cf41fb57683f93e58c530fff356d67e617417ba8d59861ac470eb8c36400cc176a3b50c61af63181e3417c83f6a1c801401968e6ad985e208115c5b0e62f635908318a62887ff40fc6060f193e4b2eea34fe481878e30b3a8ba078d6869fcb537b4a0f504346049f28137b496ee30f2344bff073406c605ed29e461e7b2c60d8925ff8c3c1738c2b00d213e5aa70e258921e36b1cc5f7b4b05e0f197fe4a2c37f60bb0bc9f26f5a302e4904cc1b5cbe8332ffb125a47517472fcf754a2900cf4782303359dcbef6582ee9f991ba6f57b6878ded2ba359daa74604f9af75468acf5aa71b9c91b41b5c9234f373b54d6c4f1d4624b08fa17fc807200d0668eb9abac1727c878e401a0cd45f305da725ff561c427c85060f1a885007358c2826c38f7e6f53ffc1fd74840d87b1a7e1e38fe2d43524a43cf06b1c8c72019734807231c332d43421eeb243d442a498c0c493735abed1a20bb517900d067100d780d8cf6d26b9e0e5f8dce3a12c4c1e3014b9adeca923185ff69fd1836acb56deda4f940fa00627cbdb54c6409f3356d002f6d40fb183cf901a7ff41ecc49406c60d6aa4f958cb18d4341ec4f90ebc1ce8c0bdb507ae2124e60db175066d390f18fae10401c83341f97fe (by decide +kernel)

private theorem part343 : Excludes 0x8000410000000000000000000000000000 0xc69d61824a0120108208200000000000000 :=
  splitAt 1 104 0xc69d61824a0120108208200000000000000 part345 part344 (by decide +kernel)

private theorem part341 : Excludes 0x8000410000000000000000000000000000 0xc69d60824a0120108208200000000000000 :=
  splitAt 1 116 0xc69d60824a0120108208200000000000000 part343 part342 (by decide +kernel)

private theorem part339 : Excludes 0x8000410000000000000000000000000000 0xc69d20824a0120108208200000000000000 :=
  splitAt 1 122 0xc69d20824a0120108208200000000000000 part341 part340 (by decide +kernel)

private theorem part337 : Excludes 0x8000410000000000000000000000000000 0xc49d20824a0120108208200000000000000 :=
  splitAt 1 133 0xc49d20824a0120108208200000000000000 part339 part338 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part348 : Excludes 0x800c400000000000000000000000000000 0xe7bd307a07017a988000000000000000000 :=
  finishCode 131 0x751a86e19c6018c3b0e5a7355d144e93b81621c19286d4b063ca3d1fda907a30870b7d1281fdab0d6754012734d42aef69051927e49dbda527734d413717bdabb2cc5a72b5361ba4ec38334e55074037a0cb87a23e1627c6e58c2b955852c23480cb87f6be41ce6b1c605a7e2b186aaf695a9c5a16adbda5ac6c234093160ccd491f0832c7f724a5cbf3065ac68fb3e1cc699b59d8404cc94369ccf6926297be1fd9c4651e8fed8c0e0ca0151eb00ac3400a38752d5b0de8f85847b4cd356ad866525211d8bde57d616b13d8531818dcb18572aa4a58523e16b3cfa2e8d246066a99bd5ac63eb1fdb384c354e0588f85ac6c319acef696a4975c9dec3796a63e1681acf0255ed26f526b8f849df358dacac595b1507b4cb531f0829456f02bd503e8cd670c5b1647c2d399745b07f6ce1e8f699ab66fd2f3af8a802c5cab0f8410f312564f1850cdb56d852f699ab6b11631b8468ce3b588b56c7c2a0151e935e2f7b595ed32d4dab63a91f0a93e6b3c614116d39593ad4dac681ab6c02cfe51e8f8565f2cfe514c3e172aa60ac300095681287354d67a1a91f0b10d4f8722d6362ccdc188b55947aa3b6b3c106406fe15f97bd47a5efa0f6a4f4a1c19183db4ccbdf34cd800dfca3b69a8f447c20c99aced42307a2e893b5116773574136d67a302a4f01eacee51e973651eb5752861c16a4c5e7064a8f669a8275ace5e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part351 : Excludes 0x8004400800040000000000000000000000 0xe7afb37253d108a8b4146a0a41002880100 :=
  finishCode 31 0x138551b8396c703471a437a9b9649c8f8ded2b2f499acf6475b05d486c23da6303290d65ef57a0e2e656716059220393b97e27ca50e7bbbda6201f0cb25517b06662fb4cd68e7279a533da5eeeb23da4ec5d09ae9ff967a727475b9ae6a5a7fd9c837cafd8c0b8e47f6727597c9432308fedcab281d2863e1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part353 : Excludes 0x8004400000040000100000000000000000 0xc68e927adb8b08aa8004c80e012028c4002 :=
  finishCode 39 0x1cc771a47903af078d6c6111c0e3b4ce38fb05e063b07e38f8f3d07ec039941272c6da6293939a823e388c40dc460e40f93e582e3cf5a4ad456c40fca0727cbdd6503a885cbf305c79ed4f691646c09f31cd4196aa353e0e18fee69ab53e60ba0fd5f313e5eee83f72fac8d22a8c00f4c18b13e546ae5f8fa6e5f93bea436b3831470727fce6aa3550dc0c5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part355 : Excludes 0x8004400000440000000000000000000000 0xe6ae9a73dbc10ea88544ca8b01088880008 :=
  finishCode 31 0x378d2398dc078cfc32d1ce6a0c760fc81141fb70735818a8e1a8e524c6046eec1f3e9cd337279ac5492f8398862a073540fb59e1a7b925022a219a631cd544283f5a4b9ae27cad24d633db479ec4969aad249f2f82c8c023872d3e9c5ef524c81f41fc0936b38fecbdee61c4662fad2671ec1fc73e5e79ee2b510369f4c7f6e5f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part356 : Excludes 0x8004400000040000000000000000000000 0xc68e9272d38508a88104480a01000880000 :=
  finishCode 131 0x2a1b86adb38f8300e81c9dcc43079f28d582e7ef62fbda641fac6d8320b705bca1b5249c7e61bac0c230dda66d677b0c4d757ea50ded3360e63dde41fad15ed20cb1fdcb457b4b9be7bba43585f06f7b4b78ee3481d783c6e5f9c7b18183693e479ed359a9ed6787f67bf2f3b97db07c140601cc1e89c0e7bba3ada9e82f6aec1a3381b59e2dfd0737b49c0da4610db32cbd28a3d31fdc1c6372bda669693e457e9318f9f071588acf51c7316c670b97397c73e3cf7c107f30dcdcb2cf62034186eb3d98b2b3d9a9e9151fdce4f1f0ca4961bb98b6308c2f27cd07105db92503ef6915ba90e27cb97da46a5c1e3540d6b353c7330717b4a04563741cc032d4f7b4a8860f2d339492ce300dc2c8c21cd5a4524c5e71e18fec3667cf93ff071049979d692b51839ce5f3e9831cd367cf5a4ad45cc4c1b0510c60641f82de62fc7df40f83165a4a86d46ae62d856078e05b8e7d85ebe3488e06cc54f393c79e83f9acb181727cf6d6988a9d03ef5d40fcd31541b005dcb1b4088f0430b078d2664d7694ca077bac6047f6b27510a92658124699b59d1c5a8c9f3045c1be5a8878e3032c6d86e7c35a8935cfa72d55cbe4d71d9a507a3e0d356a7a0be41fb9b4fa66f54ffc4af4c1f0048cc1f5a9a04564f2cf477246159071692c9ff490ac460e71817ab9fbd28b3d5da530afd05ed474c22461bc3fb7abacf56a63b987c2b64406d99eba57b4178e3daaa7cfa0e21a34179c0e (by decide +kernel)

private theorem part354 : Excludes 0x8004400000040000000000000000000000 0xc68e9272d38108a88104480a01000880000 :=
  splitAt 1 94 0xc68e9272d38108a88104480a01000880000 part356 part355 (by decide +kernel)

private theorem part352 : Excludes 0x8004400000040000000000000000000000 0xc68e9272d38108a88004480a01000880000 :=
  splitAt 1 68 0xc68e9272d38108a88004480a01000880000 part354 part353 (by decide +kernel)

private theorem part350 : Excludes 0x8004400000040000000000000000000000 0xc68e9272538108a88004480a01000880000 :=
  splitAt 1 107 0xc68e9272538108a88004480a01000880000 part352 part351 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part359 : Excludes 0x8004400000020000100000000000000000 0xc7af907e4b4b489a8001940c80602264002 :=
  finishCode 57 0xe6358ee348d83a8e8078da01f0cb05510ad1c196c623ee6b19c4505e373a3068fb60db52589f1c4403e93b622a4c5a058dc90d40f8325a9f1b9dac6c5959fa0fd03ec1b960a3cf3819c7c3c6822609437416a63e1879ea3538fcc4f5829c7e4312763cf9abac4f8e3ea49601b0690fa739ad1e307f58d8f84196d6787c2aa34be5a89c7ded328bc9f2b255a89c4641f832d636aa198d4991e2d634e0c8880dce4f9968ea2f49dcd2f7b4ad1dca7286dcaad2f1f0cd430e0b4bd436d2270822455eb727b5286933582bddd45f0485eeaf693d4acbc382f5b964aa2f47dcf697babd6deee98318a496b1cf696acad556a20c56acc3ad7b4c1b4daf2515436d5d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part361 : Excludes 0x8004400000002000100000000000000000 0xc69cb07e4f0f688b800081d040a06046202 :=
  finishCode 51 0x1ac731b0691d05b019310318c0207d07ef6998b2d67521a8ed46ad4d9ed2d675aab5362cdbda5acf1834f9a9256ab0fed80494ca4948ab4ce721b8e5ca6e6558cb13e0f1c40ee238c419252d672f1a8d659db59deb31efe0fe4f96b3cfa348b1d9a663fb0f1a81e521ad4439f34cce4ec6300a27946a4f9393bb8e5f949e9f3818ae5f627cf694f9b97d492d2270a836093363016b281d65e2d9503cf691c3b5763069ed36ba81e61145f2d554433995ed2d4d503cb315179e88eb94867277adb59ded32ced40ea43 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part362 : Excludes 0x8004400000000000100000000000000000 0xc68c907a4b0b6a8a8000800000202044002 :=
  finishCode 149 0x318d62d8c23480c596aa0ab1fd86ac37ebc2b05e78e5ad670559fbe1d782c51c27ccb2739a8f3c34e7a1cb67abb59db84a1cf5751dbd5e731dc431b01e7b4883f27cc2d927cc4f983c6d23a8735949ec15625832c3c64f998b283f064b53e39aaced426cc20fc1433da56a22d9252ce43732ad25805109cb359c5b24f9513c73551a96fe47eb4cdd46e11c39a83162eb9c46040f1cd336b38fac93b2436242f7c93361b9bd5a72c1b6b1823e05da4e4deaa496e18847da435acb2c15492d6323cc0c96b1cf8270ea34872d54140f0b65266d498b763fb3edb58dac72d8a234961f0ac44b9ad4f0d59b9e697a86c156d630e0c4d76a4ac9627cb93da5ea1350db4e5a461016b3da47f61ab4e1ed26d99192a13727a4cd67713e49f33a110300ac24856292584517a90f20adc7c3358e0f2d591fdb4be721a4e47c2ee3da66b193e52864f99ed21e387c2d39771ac7d1602f7aa0d3f9a6a1e36208f85c8731643c6b199a7f2cfc1964f99ed2b1900cc0950c5832d60771ac411b82f78f86498b57615fcc5927c825564f397c7c209b87c30200b671eb05deea0cb1fdb8f672a9f4deea0cb69fb086a288a07691141fd832e49db565243390d6c521a925e7839cd5d8c2c1fc56ee65960b359deea5e79cca0cb6b1c1ee7b69f6dac69291fdb5647c3073940e1e36ac8f85042f160771ed3124c3c6d336b397bc2b7124dc860951fdc5ef72f832da6727cdab23fb2f7832c75b390dcca0cb699b48e659a92f69065b4e47f6c22d8a8359da6a5e75a9c5b572ab9964a1bdb51c33575276e656b3b4d5ccb019d3dad35721bd5da72d4988126331047f6c4f1fdc929 (by decide +kernel)

private theorem part360 : Excludes 0x8004400000000000100000000000000000 0xc68c907a4b0b688a8000800000202044002 :=
  splitAt 1 85 0xc68c907a4b0b688a8000800000202044002 part362 part361 (by decide +kernel)

private theorem part358 : Excludes 0x8004400000000000100000000000000000 0xc68c907a4b0b488a8000800000202044002 :=
  splitAt 1 89 0xc68c907a4b0b488a8000800000202044002 part360 part359 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part365 : Excludes 0x8004400800000000000000400000000000 0xe7acb17a035969e895102a0042000000808 :=
  finishCode 53 0x1d4661a45d108839c9211fdbda5266c62d82d93edc73527cb70b259ed290d698cf691fdb9966ac8f45ed2b2f451846e1c72ce2d462c1b93d476f6951e9c9e0e73da547a903872e6f57b4c1cd40481bda47c33d649f3047425ab0f6b3a84d30501541f0b4de7b4bd6c9266f5514d0717b4ac94e4f34dc8e27f18389bd5ed27038e6af80f4637e9c9c9f3318f8338a4f9c9e3771cb9c9c9af2c9e1f5868cdfb317c7f6ba2f0b02b01a389ae0ad0d1cb53058ac6e72a868c9aed398bb6f6d0d5a60e3950230328ec9ae3e11c7c48d71dc1bc9f24cd965e7db (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part367 : Excludes 0x8004400000400000000000400000000000 0xe6ac9873cb096be885408a8102088000808 :=
  finishCode 39 0x3a8f8300dc3a06fd39aac009b98be8011f0832e400878e627b18ba1f4e83f826c3665ef169a38e61bd46cf16d60dae653dfb93e0e21e31f0d18171eb93dccb0f86302c4187c23fb62f8f25345d1846307d66f591fa5ef0d9832e729b4ccbde9c3da5a665ef9acec4b3e9c83f839878e7b49bd5ca738f5cd6f658c0b97c79e1e36f0bc7026d6924f90f19585e3617ce65521b17dc7b290df04c018b1f6c376a3b045a0fd44f2d2505e5e394861a7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part369 : Excludes 0x8004400000000000000000440000000000 0xc68c9072830f6bfa810008c106200000888 :=
  finishCode 63 0x2c0b634809f751f46107a7312c5a61b31fdbe0b31832e2776998f4507ede30094587722d9490acc634bb17c3c68fd5a8c39f62fb56616ca43e0da933417c83f671d039acc2f417b17dabb0e1c32e0b12f3b13e1f0b50d47a98300dc338c6230735408cb25599875e04a9bf564f27b5abab470deb13d0026fd6c1a04805b330dd47a3a91e0a08c598fa62b359ec1ce62c9f4c7c2939872670304ab536258b60939967e3c169cc3916a797bc12a5d79a663eb04ab00941cd50435144f353d26228f7adc57d3818acd2627039a9b1818b7e7d351397bce2323f47d6e62d819b9c865e762486ccf4600e437eb90e408a4cd896253a0e25bf3e9b90e1fda4ce0c0c1cda72af9400ad5672cb93c3361b3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part370 : Excludes 0x8004400000000000000000400000000000 0xc68c9072830d69e88100080042000000808 :=
  finishCode 111 0x1606adab0aa2d8c2027d9c05186ae15ba0fc37ed4d9acef821883f5a9cc595249bd432ece3da66279cd5ed331658069bc4f96b3c98270942389a3000956a1b8381c735627c07f1549bd508261cc596a889e47a65cd255cb257b4b0de381b00ce318b2f98b22d339a8ea638596d6166b97e6b3ad15cbf0f0412b08280f6961bcd29358bdd4fc23c1381cb3f47597350221b18dea70b47224614c3c95aab59567ab477d186f293ded2c596b2a486836c6047631bf4e6ac0270735493c3fb60ab53ce06d4da0e61d79ed23eb381ba8ce300c6348727599c6fd7ad878c7f6a02cf67ad8acc16312ad67a3779abaf6972a8f44dfa7c3b8d67699b106065b165ac31ac500200162f8e1ded30fed6aad83da5d059ecc291f0b59cfc2d2191d61bd490b0a4752d67620c195965e3d141fba8d230108228c6251549f2d452422d9065ce5536ba485ed2d3387f6c152e6a4cc5a70fed9c1d7cc47065b1743c6f699acec6338b5189566ef0589c9d6a741cc53af6951eb9566b3c1cc112e6f1e4a0be41fba8f81e8d81bf5dc617cafd1fdad1457312aded23fb623c7117b4a7cc572d82d8f69965ec47624a0fdca7173500281157cc0b358d9c9c907032d636c4762f86cd487022507e1b3 (by decide +kernel)

private theorem part368 : Excludes 0x8004400000000000000000400000000000 0xc68c9072830d69e88100080002000000808 :=
  splitAt 1 42 0xc68c9072830d69e88100080002000000808 part370 part369 (by decide +kernel)

private theorem part366 : Excludes 0x8004400000000000000000400000000000 0xc68c9072830969e88100080002000000808 :=
  splitAt 1 94 0xc68c9072830969e88100080002000000808 part368 part367 (by decide +kernel)

private theorem part364 : Excludes 0x8004400000000000000000400000000000 0xc68c9072030969e88100080002000000808 :=
  splitAt 1 107 0xc68c9072030969e88100080002000000808 part366 part365 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part372 : Excludes 0x8004400000000200000200000000000000 0xc68db973a31148889340001514208444022 :=
  finishCode 73 0x8418c7316c4c17c41fb0878073d03f460437e915597c0b1064a84c46e1bf62cce4351a832503e0c9903e1cf8bb681f417a60ce1a0d42045443078d46a6b1802e3612c4878d64eb3f6a1d45a3c90d0eb9cd521b28d564f075d67ed4d8342d4f408b380c983aed5d949ed4d6a7ae8dc330ce308d0293e52182dd46a0c57516ab0b6567f2c1d46ad632f7ce653968314e4eb0751aa93e16c9735a9b289ce16a4f4a2c8df1f0b16549298370f537b0ad547c223d94768d7500c6060e0ca01062aa0b01e03d134185331647128014a11af0685a66945a0fe471464878e4a29e8a42d166979f4e0e66fd474ce431fd973565f358c3c6801811cc598c6fd0f1a926593cb3f6f1b81fd878dc870f2418ad639ccadc16d47f6c5f9aaae6537eb0a68c088f58b23c9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part374 : Excludes 0x8004400000400000000200000000000000 0xe6acb873cb114aa88540829500088504008 :=
  finishCode 61 0x18c7c1d46e164730e5a7352cad1811e7a93da661e351ac2372ca8315acede3480c5a3025cd16c878e204c1acf0f85cc5a8ca1b8c0a0bd43728060e328060e6e6f3f0b59d403460507e7e138fb99082a081f699c8116b1cde2d81e3618c3cf69cce491e4c5ef8c0c3c9524c40b6398b3b94765ef83f93e507e81f4c011f13e5cb3289d676dc2cee6a9ad447c3461586ed49907e81f751bc514cf6d1e793e43c6c23dc6732acedace3fb3e7cd3359dacee063ad45d088174491a4524b0665038fed86341e58be5b51f0bd5d82b13e58323fb510ac03c987c21e38e16f6d8792f570f1b13e04a972c7523fb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part376 : Excludes 0x8004400000000000000280000000000000 0xc68c9073c35d48a88150921400000505000 :=
  finishCode 85 0x3a0ce2e9102b09807063859395442a35661a05903820c58c2c73540fac3d452a3b50dcd5d8e6a81f055c735691bc2e6c9451fd928c5a61e363168f0f8563683f05d9b967219735002c15616ad9083d5e1f0a07c1074614bde5b5058c6165a9b53dd47c1986903c70b4d6c057c81f408c3c96a7878e7bbb50ce4e81f16cc1e31fdb5361d6b4bd07e81f6813058120840792b558b9ac37408a0fda670f3d8820bd393cc37408a0fc7c2e63705e02f56320c98c0ce4934bc70b58cc1e38c0b93e735a7e56ab181818ab626039d89dee65481a0fd05f3996481be098440b60f849f3353e0fe80161ba0fd6332515a9e80161b8f464a1a04507ee6280649db53505eb2f9a9aa010e08ee6050b18ba3485cd985a3fb16c82f604541476681735cd70d75aced5d62cb5668c2bd860f27df727bd6daceb0f837b30de0deaced4025cd26bab0b206f5eaf0fedc86d4d2f180463dc821deeac2d7adc1cd287021e0ff1857b0b565882c4f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part378 : Excludes 0x8004400000000000000200040000000000 0xc78c907283174afa9140089400208404080 :=
  finishCode 107 0xb02b0b22a09c3a809504eb53615fa89da9e7350decf5d6b3978d262b61d80a11cccd675279f3d68f0e65acea3d6b3ca3d26bb18dc2d8d43a9101cd54372c743c72f8c234de51eb59d4361a70dd8afe513b5349caf5d947a0c96a6c0af1e7bd665aab5356a2b1d5b09f302bd193358df47ab93e60f18fecd632d4c9461976713068146aa83600915a3c3c941f878e8c0c5e7593ad4da67313d67eb51963ad0448d6783524f95a9ac45a9f20bc7829459eea0770d0b535d4691845915fb353528a3d30d98fed305419c2628f05637317d40eb5398221e396371818c2cd5d588a5143c6a81e0b47898a3b91e0a81e5a8a0fd28a1e396c7418c2f3cf576928f3d05ef5787a2d67832e1a38c0cd591e8ac9da9e982d88620fcbb7207d5fb03256373d75622d631e0a81e6b1b57503eb2318b62a01b36a107e73594861e396364f99d43d22437eac6e698a045ac625982fa7d37bac1e362140f358d6365d793bea07810dfa3fba3022bf065acc5eaed637bace6260d006063e9c6043c681158d878e3e9ad5546aa078fde1d76aeca35 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part379 : Excludes 0x8004400000000000000200000000000000 0xc68c9072831548a88140081440000404000 :=
  finishCode 103 0xb0356d645616c541f0050828d8b313e5ccac374f9a92507ed67870ab531d793e584691a80dd9ee67abb0b5aba697988ec2d7abb5767ab82ad88272931e5a9b58c3c71e8ce370d42d163618705436d3358ea8d4e16ea3486fd262c1d76a7cb3f898a2b36a8c40922a0c37524b54e698a045a9f2cfda9f076debac37510b54e154cc2d4a2b535a9e9c238a83481a15a3ce3915ab4c671cacf589f2cf58b2f75891e17d0d0a886627935dd46919c6303c63d396a22d3598c0cb1e9c2d94a29e8dc1736839a8f4dface353e6b3ac6c162d63593d12238d5396a65ef5a8cb1b15b8f85ac6f778f7e0b1670ec5b019306fdac683f40f97be6a6ad45aa718187c281141fac7505f2045a9a5cd6c1504e186f3574342b471e09735d06aec3c1417ad1e1d4b99023a0a1b83c6d2f1b6c9ed6b3ac9d6a693b86b2d5d0eb9315eead2f9eeed5d6e19c2bec71f7bb931561eb51680912e3d95f6c153729ee56a6d4d99c58dc2b7503878d492c3793ca47f6089fbd647518c37e875e2df972c36673558dc0cb598a4567bb97341925d70d9b60ac13160f1ad143c7354dc9f28d43c64c5 (by decide +kernel)

private theorem part377 : Excludes 0x8004400000000000000200000000000000 0xc68c9072831548a88140081400000404000 :=
  splitAt 1 42 0xc68c9072831548a88140081400000404000 part379 part378 (by decide +kernel)

private theorem part375 : Excludes 0x8004400000000000000200000000000000 0xc68c9072831548a88140001400000404000 :=
  splitAt 1 55 0xc68c9072831548a88140001400000404000 part377 part376 (by decide +kernel)

private theorem part373 : Excludes 0x8004400000000000000200000000000000 0xc68c9072831148a88140001400000404000 :=
  splitAt 1 94 0xc68c9072831148a88140001400000404000 part375 part374 (by decide +kernel)

private theorem part371 : Excludes 0x8004400000000000000000000000000000 0xc68c9072030148888100000400000000000 :=
  splitAt 5542 81 0xc68c9072831148888140001400000404000 part373 part372 (by decide +kernel)

private theorem part363 : Excludes 0x8004400000000000000000000000000000 0xc68c9072030148888100000000000000000 :=
  splitAt 1 46 0xc68c9072030148888100000000000000000 part371 part364 (by decide +kernel)

private theorem part357 : Excludes 0x8004400000000000000000000000000000 0xc68c9072030148888000000000000000000 :=
  splitAt 1 68 0xc68c9072030148888000000000000000000 part363 part358 (by decide +kernel)

private theorem part349 : Excludes 0x8004400000000000000000000000000000 0xc68c9072030108888000000000000000000 :=
  splitAt 1 90 0xc68c9072030108888000000000000000000 part357 part350 (by decide +kernel)

private theorem part347 : Excludes 0x8004400000000000000000000000000000 0xc68c1072030108888000000000000000000 :=
  splitAt 1 123 0xc68c1072030108888000000000000000000 part349 part348 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part382 : Excludes 0x28000480000000000000000000000000000 0xd7dff036428f14009240000000000000000 :=
  finishCode 99 0x75180671644c0e4ed03a0aa24d6521a51d46a72d7bbce65489a90c7c2a0d737cd67583a44c186d5b5a6a51d41b1cb5486b070d3c72d551386c0e3e4f990265f55108f84beb204d41ae8260d67818692149ab0dd486a49681436f69963ac2506197d5243359d666a4356e0dead35066b3b9cde9257b4a51d046e83604f95068b667b4bdd5a670a766adaa89c2d0703541984c0b9a0ad8b22b2f1f093e5ab7164565e1b9157b50e83f82ae30f0d65ab6149468a0cc156882605f50b0cc597a993e581746045bab456ae9ee616eb575eae4f9611d04c14033165ed20a727cb5767b4b9bc5bac2559797d4fc6a400ee411b9be0e6d5b7b482adaba82389f33da5440d2cb4d0dcb575ab64f9527cc4f721885a1483e0ffa83d62cca3b69f9b95aceb1d9ed20c5492ca0147eb53d69ab51981a2dd409c1fe7b48f4d26eb1d5a8a98703732cf69614b13dccb0a2c2e6f692d1b56d88681ac8c0c0c35a697d45bace17d4383290c34ec25597a494dcf2cbd69ac02789802b569ab3f98b2c3b3f0ad4603ba98702603ad98ab1817b8931d86e9e551a9736693ad45cde0a76aea48662c81dd4360ad7aec0776a7b56e581b1556aa5c390b4d59dca3b6b38abe03b9911859ab6b29489a90e051c61d68ad5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part384 : Excludes 0x28200400000000000000000000000000000 0xd7ddf1f382a504008000000000000000000 :=
  finishCode 41 0xdc340c42506257d0c1aea0b75a9f1fcdedb353588302ad8767036405bab4d905e3e1381cb4d5b13c440c2ed33903eb4d5a2c0cb396cd336b3a0bd104c169a6fd044c4b957cb56d6aab51408a86e57cb56d6aab515a2c0c9393ad8ce32060b057ca490eba0fc98f2cfd4926424082f907e80d59fad55a858cc7fd419b5461e1b14cfe683f903ece35081d969a7273f9cd510eb9fce58c97fe59f9bd4ffe81f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part386 : Excludes 0x28000401000000000000000000000000000 0xd7fec2b20ac50028d020080200000000000 :=
  finishCode 89 0x220b41c8dc2d35e07c180790e4ee81896317a4de37eb55614eb584dfade20366ad96fc5ba3cf0f1bda657cb06cc167110d3c83d5d20e73585c763cf6238b74fe683d79163b2034dc2e6f5a4878dcdf2034e841ec606406ab034b834af6937aa51da9f17fcdea39f7b49b9548551a859101a82d6f0e6a6e5834ae390f1b53e6a7c5ff791d0312c62f5a8c1c39aaad6137ea81e393accdab6b2356c167070cbff182db8561e430cc2dd4929895404305ba5e9048d071617a7ce7b4b554d2b18116eca618bd86f1fbd1a330bdab6d6378b6078d8b31a54fdec2f521cd5b698c605cca2a726bbdb662c8a9d85e5ff985e94779184771b80f1b90619964a62f5a49b962ffca07517aa883d8be6b51396b4ce317b06ded2b1d35ac5bb7b4a81c3c6aa390a422883d591027079a30e6e516e935e0f3022d82ea439eca5bf6a58f3cd6a7111e7c71f15bc5bb37a8f3ce3ee42b8c15928af6940eb53503b1b96 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part388 : Excludes 0x28000400000008000000000000000000000 0xd7fdc0bb02950044800010010a140002000 :=
  finishCode 139 0xe8370f03a8ce35083d983307f0658f84e3e727791ac68188312c62f37ec6b19816b515a69bf43c6b62c0e3729bf4c1662f2becc3d5a6ad14c4a98204637e8f8507e6b5966e6fd618a0bda855150381b40b60f85ac6b0a89e4688b74f7282f372cb2fa0e683d2ee9835584a187720f5abac530d2a93e59fa0be41fabf547aa01419b0f669fc1cd6aa83351eb40b2f85ba60d5b19027cb9be6b29fc589f07d949f27b5852a8260a01fc547b293d69a3e1410ce3b1369fcca8500cd5b4179b954273584fc6f575a6a0be303356dca2f571e9ad3547af2220c4278ac18bd69aa80b74c1ae53a0e2e5572b9b9584b2a01259c764c3728abf4dce5cd57ed181373b9455850167f236433a60d46ccb456118b74c5f00fe30283f6aeb955ca2d5b6adcc19305ad3588561a0248ca1316eb0ecc1a6255a2cc23373c62f5b168b281cc16b45965f2d3507e3e1791845b03c72cfcc1662f599c1e3312878e5b105f20fd6ab0325ac640d040fac00bb9822b3f1f0b164c84a3c0bb59fb404d790229350f1c90f1f0cc37487acfd3448793e4ffe83d926ab4d92471815607c3135d65eb456701671fc569ac5f2ffaa07e1706419abf5c726d735acb4d839c61c7c26f58fe6ee338b2078cd8393a606fd49bcb4962ca8566ada84e0db356d4269376add181729a804e3ed42a8ba1bd6381b4a5066d61901a6f56418533105a6f41fdb84f16462cc7f37abb56d69aa4f729ca015a6bdd6839b94cfe6d613728f4e72aad358b2aa34071f5a4c937463c3857ae9fcd69a03f870a7df5a4ac1cdfa727 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part390 : Excludes 0x28000400800000100000000000000000000 0xd7fce1bb06d52a0a9c10020042002858000 :=
  finishCode 25 0x308ce340b62a09472ff98bd82b1f360da5cd8c3cafd7b482c585ab2f96aa625780c166fd8e6ac3b9816e4270ba1c0e481a4e569b135cdea903560dcb2485caac25597ad15ca3063cdca1a3372cf03da5f00c7cd35409c1cce6a6f50cbc6d927cc61e839b95d1de83d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part391 : Excludes 0x28000400000000100000000000000000000 0xd7fcc0bb82852a008800000042002850000 :=
  finishCode 135 0x3c0a21b8883a8d5b7c1b8601a841fcc4161bc1cded270339ab38b61bf60e72d45caa947417869c38692583c694731289ce3f99324b770739ed21e3381ad8e834de7b4a51cdea7ff40f878e1e7a40d22b307daca6f562cb48ce251e1e7832c3c69c16ee62ec605a9e6d97b4c1cd22ab2f8f57181490c1cded2fa0b7641693e67b493252469e33886260b4d2ffa8d65a2a51d65f1895acb24dd69a60b3eec7ff8c0868c5bab4d5b13056107e7ff85bae53837e6e53d5d1878c098bd05ec3785baea3e8f233872d83c6823a0e67032dd8f4d6c4319c4179c0e3969c0e47ec2af3f18b7507e813907ace2d87358386a4981965bb2ddcac300b63384f95a8c2dd50d9b94c166c9855ec3b67126b032565f24e584a2dd3589b9e597b9560d186fdd4671a87c1b8396c735408ca3540f9bd414f0f3c5b21e31e9c1c3721985a10670b6569a9c240e36cb95e2dfbda4d6b07316e935e3ff8b74fc72d356062dd6e14c16eb0de0dfb14d6aac558156811969ad6561ba07ce4441d45a697fe83fbda59c3ffc94730b8b76611d46716c30bc1c30f1c7353efc703264a0f56c4314c2ffad168c3a7ac5ba81f581c2dd373ac0e16e982d8b33db53ca4d77b4cdc3a89378c4a6fd39a935e312982dedb2cfc9ae1e3481a07d845f1e45b03c65ff8c169358c4aba2c66370acfc1761c7369cb29417b9be40facbcc4ad51907e1e3 (by decide +kernel)

private theorem part389 : Excludes 0x28000400000000000000000000000000000 0xd7fcc0b3028508008000000000000000000 :=
  splitAt 5016 107 0xd7fcc0bb02852a008800000042002850000 part391 part390 (by decide +kernel)

private theorem part387 : Excludes 0x28000400000000000000000000000000000 0xd7fcc0b3028500008000000000000000000 :=
  splitAt 1 87 0xd7fcc0b3028500008000000000000000000 part389 part388 (by decide +kernel)

private theorem part385 : Excludes 0x28000400000000000000000000000000000 0xd7fcc0b2028500008000000000000000000 :=
  splitAt 1 108 0xd7fcc0b2028500008000000000000000000 part387 part386 (by decide +kernel)

private theorem part383 : Excludes 0x28000400000000000000000000000000000 0xd7dcc0b2028500008000000000000000000 :=
  splitAt 1 129 0xd7dcc0b2028500008000000000000000000 part385 part384 (by decide +kernel)

private theorem part381 : Excludes 0x28000400000000000000000000000000000 0xd7dcc032028500008000000000000000000 :=
  splitAt 1 115 0xd7dcc032028500008000000000000000000 part383 part382 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part394 : Excludes 0x9002400000000000000000000000000000 0xf6ffd296da4921248000000000000000000 :=
  finishCode 21 0x388e830030740ecd5b0659cc4e4eb3d838673163018f070ce0672d5a6c731406a0f55c610e626c298b47377c3cf5a6c6ef690b594d01e78b4e6b0b4c4182d21409cb4d98b24d71a89bbe0feb476113b33064ddeb4d0609bbe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part396 : Excludes 0x9400400000000000000000000000000000 0xe6bff3ba5a8128008000000000000000000 :=
  finishCode 11 0x358ee3101e34f0c325cb9ac64f973297fc1632cf5a6a3cf8f7e72d398b00d679cca0cb3179c9ce5a6178c5f07f398832da731bd4bfe727 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part398 : Excludes 0x9000420000000000000000000000000000 0xe6fff2131a45a0488421000000000000000 :=
  finishCode 51 0x1cc6e1d0500c5eae1864e632d1e0ff2b862300b53361d07f27c9bbe0ff1b0e377c1fd68ed6583fc4f9377a18731856e5f36a128406c943419c731494a93e5a6ab85ff88174398c1fe6b2ad4e0ff3595ac7390d046b4d169a0f5a73390d685d1546e105a8337accb4d527b99605aad352844103a0798beab4d83dc0238c3c1fd89e0b10e0c60da43284c9f2b45377ad3549edc2502798bead5b5a686f501a6ef93da1bd8c3ce6559fad35d04c18427ca04e25f935e153c1fc18306dd67ef5d80ea9ff72f86dcdde2b1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part400 : Excludes 0x9000400000200000000000000000000000 0xf6eff2731e012104810004c048002000001 :=
  finishCode 69 0x6e180521a837eb987276a9c30d836878d69a731836cb4d0de98be690ba0ee39830d357cc37732b4ed69a7310f1a4064fcc605246b4d396b987318196d5b317b4864fca3bd28e9ff9816d21396bb80c5850a1e3732cb4d142832dab6bc2b062251d5c491b9839f8be66f569a9cc630f0094236e656ad86c5a6a12780429f926b9bd47924f96323032cfcdea73183c680d50169b0f24e626c3872e5ff26b9bd4bdeb41c88e2d35002f0deaa6158c3787923874d2303390cd9290172fd1813ded073724c605c863c99892e617be8c2878cbb6d4da30e6c98c28f266b3b17d203181400f05307829a1d05ef735c80d8c0c1b66b396d5a674605ace6c327c96d5acb2405a9341b4bde07f1e4b98de46068c2878cbdf4614bdf461500480c1e372fb07e480c605ace1e3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part401 : Excludes 0x9000400000000000000000000000000000 0xe6eef2321a0320008000000000000000000 :=
  finishCode 93 0x69180201b70f840072777185b2d4c5d281d186ab861940eb96e616a0cd6a683395f682d98856059b20ccb76b3140e93e56a66196b0e63356c1962e9598cc4b9aca06d72fb9943c6c42d0ac2688820cd07a5cb92029475a3c25360a86c43c69c200b4d9cca842d3524741fc9f3073416ac6e69aa48c3c6b4d9a732bed68e83341eb989c078d1c73280268c0a8349f2a435989bd546b248e58d935da9f2835ace4f972fa925780f1b97e4a3b5963f9826e3027bf480b97dcc398cb1b065878d54165d073062a04d07b07b84e691362e8ba5d0881a86e1dc732c4f95a9a83505a6251808c35f063094b348519e7bf83ea81d486b4d0589c9ce5aac3104f94fccd535a69865ccb11f60fe7b91e4a9252231cc4e6313e54c351ac52197fe620a08d40e83d2f7a0ce57da0f5637358cbfe82d6adad34e6302c52225ff416abee2f7a44528e3016a148385c8fb59898645d281d393a0b5b869acc5572fa44c5d262f1e4ce55411b524bfe0b19ac65ff317b70a43187a289ce6a6fd8fe71038e62c0b485eaad61251b165ab702c4946e514412837eb07e0d4b58505a9239662e659a76c1f48896d500673141981f66ada44544e72d488c923 (by decide +kernel)

private theorem part399 : Excludes 0x9000400000000000000000000000000000 0xe6eef2321a0120008000000000000000000 :=
  splitAt 1 93 0xe6eef2321a0120008000000000000000000 part401 part400 (by decide +kernel)

private theorem part397 : Excludes 0x9000400000000000000000000000000000 0xe6eef2121a0120008000000000000000000 :=
  splitAt 1 113 0xe6eef2121a0120008000000000000000000 part399 part398 (by decide +kernel)

private theorem part395 : Excludes 0x9000400000000000000000000000000000 0xe6aef2121a0120008000000000000000000 :=
  splitAt 1 130 0xe6aef2121a0120008000000000000000000 part397 part396 (by decide +kernel)

private theorem part393 : Excludes 0x9000400000000000000000000000000000 0xe6aed2121a0120008000000000000000000 :=
  splitAt 1 121 0xe6aed2121a0120008000000000000000000 part395 part394 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part404 : Excludes 0x8008600000000000000000000000000000 0xe5bc597b06814314f000000000000000000 :=
  finishCode 123 0x440e62b90a1cc5ac681885b05ea6e2989e0f860afb17d82e6e704897fd806a49b963dcb54c7c26e587c312a6302d63617b4e4dce5ff9a6a3e18c0c7dd6a9b5247c317fc602d2f989e5ef6b18c1cbff182c1931e0601205cd18214124b70d632030783dcd5b0d28f851ff00560f6e516ae93be0f72c0c7c260b186b20d498dcad631f0ac6672a97fdac6b0f949ea291f0b710a358560c1cdcf3575a050ac931491b16647da47d47b293cc16133947a3e16813c1f0b4fe83e935d82ed39624b58e6a4c5ff851ac7d1a0183b4e6737b58cbfe3e12ffcc81f6e51ea89d893356c9df1b9cbfe133947aa271f0b70d0428d63103071f0c91f6ae983528f350c7c2d5b1d5a50e6ae8c34c1ad60f84ba31f6d5fa2ef57ec0b55a2a4c66a49b9c9de30d372cb2f1f097fe14791846e1a0186a3fe317832568b352523e9e41c68c085347564d76a497fda933166476b58d26e1991869b9d65339bc60e3e16a07c20b59aba1c1064abf6681b8692cb071f0a8ed47a30d177c10d49a302901040a51c9df0644102d5d810230d611586b17c5305d29a2b8a2348e606ecc17352523e2b59eef34bda92d6759fcd2f5a29735ac6d639cc4f0bff1b9d2864bb96aad3548fbdde03b9b9daceb3f373c2b56a7b15547b1f45aca5e906498bcc17182e174cd63 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part406 : Excludes 0x8000600000000000100000000000000000 0xe58cc9bb42834002f0008000000028c0002 :=
  finishCode 125 0x441022f0ae4287317c2006e122f0bd461ab62985ff8ffed398bfeb3d6a9a3b4bdf354d84517cd2f8c19b9cdca1bf43160b1b9c76e81f583ca494f9acc600593c4f9180869e5b1906e103f18396222ef05dcb038c3ad1e37397bcffed679aa60c985200791b853061a82183648fa4c5588c3ca27373a8bd07e4f9373cc1f513ca153179835a0561aa741f4bfea0d49a97fe69ca445a9341f541a4f93ffcb2f69c8c1dac6119057ecb3f41fa07d9c3d1aa6ac28d669fc1ed8aac233edd07f1199b949aeafd373c2c571c935d5f7243cdcec553ed97bd493281da5e6e70d2c6d737296661a4b4bc186f574178325f05b1ac4319040103eb3d87562ef69cb54db857dcc177b68325ecb2cf53c3ffab84739ac66ad7378eac79e5ff811ac3b8fb6b3d2f7b54e147d05eb13e461ad638c5e60b5a4c5ff8c1608ba0fae4f064b54cc4b0c05b8682007d208640602c403256c177a0fe7b6c60d6a30f85eda2978dce3ab963a4738c19ffd6525ef17ac82f927660d51acf5f59f832565e1bf162ab8307052c1bf59fc83f5a2a9808fa30a4db2ffc60d6525ef41fbc8e4f9aa2f6d8c38f849f28ff60bc3e16b14c68107e81f6a8c60d59483245d2b3f9a06705d2d2284e7b298bc1926199a9ed4fa0fea156b2c1f5edaaa338e3d815e6c3476b58c34b30ed42a0ad7b9d07f7ba97352667dd6a6ac0f59a0fa60b6a7a45d276f578c1662f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part408 : Excludes 0x8000600000000080000000000000000000 0xe58dd91382c15000f500000031400804000 :=
  finishCode 133 0x398b6320a8218d020be203c214410a8062f186cb113988c36588bdb6398ac44182dc358e398830c192a034a68c2c604e623e171ed1878c0b59e30a8ff317cf6d174832504200380f65994108c1da9ed4f819282141fa98dc1d910207d5c5e1c46ad9cc5a0373c4a36998bd415f128da66c37a14710c5e9019822c597b8ac9c5eaf6d8c32c41593cc377b6be8e22d262f7b0de50ab58e7b8832542aa02c9e4808304c32a156811df2d1d67f4010a1f7683dabec5d2d5b50a98bc5df28563028df05e8304dcf1cc417b18140fcd0440a01e07318c2cd3906098bd64f1858192782c9e186acf4fb7461e3020c93c05d2a019622f6d6b283266a7cbc428a03707316815859fc9131629835f4728c6063728c363031b5d1d30c35ab65ef89f27ff6e1ab7002e82f548acafb3ffa47d68ee53961e5cd54026b46060f7183372c6063ffd1819ca2e6f177ac4568e731681b88c0c5d18c39f6dcda2ef317a687ff3e1ee30a2454f1819a632d4dacb1877b0c91f801f46e1edb03245de2f55015059ed18161b9cc47c27319ebf1816b1b59e0a0812e302afb3eea44586e98460650ab58c7c20bf8c32dc2800c905ec73105ecc378c2b4cd86f1cc5b860061a2e959008339bc6bab456ad82b5385a2cd254a2b57434b07d9ab6d639cdeb553edb41042f0d5d8176b29491a51cc826dd1816b39b9d800c8d1811f0c6066b3936e83fcd5d023a3b546ad49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part410 : Excludes 0x8000600000000000000200000000000000 0xe58cc91307914808f140001000000005000 :=
  finishCode 155 0x110408e62f10a1cc5b871208587cd6750693e460230d48bc07b31298bc5eab3b8c2eb613e66a6a3b507e5ff6b1c4d76b1881b3cd4d83cac44bde0bb177ad85b79edad4d1e78e168c3a445edad677aec2af58882ce146116c2ffc60b621b8598cd6358889ad6769431779895e03c0fbb2cf4fbb2515ac6c4f9a9ad6708ed187001a515a9a811180be0a82b082141fb404f94fcd1870648f85ac700253f23e19ac69458c3b8907f89f20c95a8ca439c9ed3715497349f2982a0b60f8630f0bbc9b682141f9e0811967a28185def6d4a2b70b0f9cb24db59997be8c2b535cd6b6030455f4605edac2f0648f3d667461e0df1817aeb41003710431030d0b6cb0359797443822ef1f0ca3b15793be6128bbe085e01772ca52469476f15051128b181986ed4d26dc616481a9268c2b4fc242a0d480b9ad2032835aba3e12e6936e671846b1306213405d82f49cb251c9cb2ca534272d18151ea44d6aa1b34a3b59e272b56d3f2a3b59486ee5aaa8f54760bd0e0d18105ab0956aaa824dc9af358c7822cb9ac6a82900a183724d7949eb3f947a4f9941a8ed51a8c34f07c0d8730b9a98175e25db4c56363c1410ad9187861ab11154a0bd6230dddeeb1812628e9e50dacfc61a0bb154b98b62c4615aa0bd0430a2046186a3be25d8bbc74f286d67e30d05d8ad4c4b070456b358e6260a834082141f98be7b683245d207b94770a340ac240659898bcc1ab1b903e2e95315fb2cfd03ea299ac64c585d23cf92762e9407a0bd401749882828ed8ab356deeeb559eb2d5b5aac0419ab60ad851cc68147b2d1cc1a62f55187b1acd49e60b5800ff1f75acef758fbab00eb587b3d5cbea0af489cb553eeabf67aeb53456a0b5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part411 : Excludes 0x8000600000000000000000000000000000 0xe58cc91302814008f100200000000000000 :=
  finishCode 153 0x80169adc3e8d6388a00c045d2e62b8861cc4dcf30bd892b0f1e786fe587c606513b0641923e11d3d185157a8ed4c730dcf1f3d03e6e78b2690f4a280ee7b6a445a9ac82a10a20bd04206d9ee657b26bb154c5ea4fa146119c40fc943317abee351b5454529435322040fa84e8c3b13d692c41500fbb2d1cbeaa4f8c3cd5b5a9abee514ad4deb7207d452a4f47dc01362fc1fc9f2b49486c28e63e062f561a8306935e581acbd22ee579606b556a0937293e30e9435a3c30d03dbd96581acbd87660d820bea6e78fbab2f18693e6373b14d905011426bc0b352782ce5a2cb0305582cd5826bcb0f5a2ad26592ab098183419328f47c24f9398c6175e19c398a89e317b0647c2c5f6aec6e751ea89d477185dcc6b19082103ec22805ff249c8216248add88e597967a7db488c61cb6ef658dcf187624a445042d398bfeae1ffd893460479e2a7a3065ff624acbe0d59f6c1667312ffc10bc34fe05aaca52469474d0fc0bbc17b8c2d18704097bc10aa8136d2434615cde7e1524d18569f9f763024dba0450150398ac0a226809f4e147b4605206b3304cacce26bb56dcdf46049ae1c1594b009839be4778b2c37219d597c2cb0dc97be165a68a3ba3028cb527a51e303293d846d590ddaca5848216532d54377290e8c1a3bdac431cc3b079eb118fbe5ef40f976e611445d230f164d246d5b0dd9d89a0e7c9ae18f924b1879ab718157cb946491c61dc762b15999d89f3965f07f1cfa7ce597a48cfba18f928ec2288d6796527dd58786cdab61b7711808c0d07f71d86fd45eb2f837eb53a0feaf1963ab2f968aba2c46594a4941761b7053b20dc20bcfbb0b2e3032cfdace7dd2c4c9477afacbd67ee39 (by decide +kernel)

private theorem part409 : Excludes 0x8000600000000000000000000000000000 0xe58cc91302814008f100000000000000000 :=
  splitAt 1 57 0xe58cc91302814008f100000000000000000 part411 part410 (by decide +kernel)

private theorem part407 : Excludes 0x8000600000000000000000000000000000 0xe58cc91302814000f100000000000000000 :=
  splitAt 1 79 0xe58cc91302814000f100000000000000000 part409 part408 (by decide +kernel)

private theorem part405 : Excludes 0x8000600000000000000000000000000000 0xe58cc91302814000f000000000000000000 :=
  splitAt 1 68 0xe58cc91302814000f000000000000000000 part407 part406 (by decide +kernel)

private theorem part403 : Excludes 0x8000600000000000000000000000000000 0xe58c491302814000f000000000000000000 :=
  splitAt 1 123 0xe58c491302814000f000000000000000000 part405 part404 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part414 : Excludes 0xa000400800000000000000000000000000 0xe5ad73122a5540288510020040000000000 :=
  finishCode 81 0x1ec391b85a6b886c3186fd720e4ef7589725bb5a8a43deaf1cc55c623c1b939887063f88f858bef5d8b76a3b5149c9d9816cc0b526bca4f631505d09ae7db96a6f694a38b052669118deab478b766f5398c9476e164710d86a0dfab01c9da771cc4372c2d9ac2731489ab098244d83302cd6069376b1ce5589ae7f17ba82cd6773dd565ea4f398a8a4e4ee6440ac1bbce62d2f871ab035a282ce5a3c5d161882d547a4c505ac1b9571cc88138398b4071f59ec0b55a3b05657caccc9b60439ee2af9599936d67a8a30b6481a5153bb3d6d384a128b1c7d4021a51c8cf5b158b9ac9b7181816a4db361d042b0b0251d6c5405627e189aec2d816a4af985a94559386b52469459eeac153dea48d741e5c0b558d924e3dcbdb4d8608b62fa444e62c5f9cb27e1263935c562d4318b22c3e52792ece6272d39ab4be83e82d498a73138fb056398b0563e89bf585a731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part416 : Excludes 0x8000480800000000000000000000000000 0xe7afe31a42d904089650424040000000000 :=
  finishCode 85 0x1683911072169b0430880d7120e73da565e30d72a900ded31bbdca6b2f186c4f98c3a40ded2ba3300ad98ba3eb4a2bda554055c3eb26bc08596a2e397b4bd6e3938fac806e4410aa34be411a0cd2851103a4c7a0faa1327ca79683ebda480604f509c40a01949e30d2ddcd2573585fd984e1544a2ac8d530e0c72d14ecf775a4c1c17bba7e66a9a4849f2f695b09af393d6a24f95a8c6e59c882154406b08d238849d965e30d72a900c9f323c5402b2f735d07318693e630334e49f2833732c4c7489a40d65e30d5b19827cb59e0e0931c5766e19cd64d70d0bdd61f0b93da522d9393c10bc100cdcb3ddcb22a0d0dcb50e38fca0d3939396205b130521c93527293e5c4821a8f39be302403186bda6381c10d22f0f59984a6c3597ad55a7f04ad1e2e4f0b4d073612b93d6673da5676dc2cce201ad453f2947393b926201b97d2029f9691542018246612bd7528a3eb729cf777bbc71f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part418 : Excludes 0x8100400800000000000000000000000000 0xf7eceb93225907088418020040000000000 :=
  finishCode 59 0x15c5e184398a983e2d0b1959782ae26bad3545f100d246e22e8b4100d2732d3416aa2f968a9478e6a4d726bcb4d5a2b88b0336ccb11201a49569b2c449ae4e5969a6f526bb90cc2e8c62702d9272cf5d201a4cce5a93950dc4036a4c9397b49b9569a403272ad072270b4d631206493a302f6971cbdb4deae399ed30739c7280d7b4a6080d89ca7cda0db181839c6e5606accce3e7f15a9c4036aace6561d9bbc9caf6939a9b5cdcaba3e862100cfe3173569a6e52e6cc155a6bc0e22d16581b5849ca70339aa1059189cad3b36b9735453293d816b4d490daee3b93bad5562a976d6ab2c0d82ab4d5e169ad4251e51ec6060dab550e0ad5638fca01 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part420 : Excludes 0x8000404800000000000000000000000000 0xe7bc6bf2165102098490829240000000000 :=
  finishCode 137 0x6716c612082ffbe8d4268ba2bee5a6b58c80683341ea10942f080d5f1144a3ad3625cabf5a9f06d7820e31fc588e6f53f8d071398cc5f5a6b0be3f8c1b49f28e16f185f13e60dad396a9c1b6480a385ee2b4d5a6c4d7617b17c7c306d985ee4972fad349f2c3187c2b4d62f9cc4806f62e84f95a3c24960bb1744aa8eb37ad06d488c9355d0ac692c8e173582c49deb315a3a88d2596a63e327782d66b19234f522d94eeb60a20f849af23849f2f5393ba4ef8deae39782206c1406f07c2731582c9457ae93e5a673d4d82b06f618b78a22e84f9503cb314520db41c5a664d7001c3977a9a035a7318137ab4e616cbda42933db5ace9f9732a0f5ee26f53809f2b3193f2b4d7b8b17d05b2d3585ee434eea40b05968e5cd4a2b4e5a460dc6c341e9b945b2e659eae07fa30ef69699b534e624f97d1a4591845e0806943604d757ecf6d69c86a4fe23b93619cc5586a5c6c34a3c1e672fbdb60e2d398c3c61e2358f85cde731597b609f9a0e2d3971cc1b4dea3e1391edad398d86e397b49bd4e81a7d1818c3b8f469f009c48ef036110250731409d0737b4935dac7248cdeaf69169ce43732a775206d63732c94726bac6c9af1cc5a66d4d7b4a51d3ba82d969a4035d0f44a1026a0d967a8ff6b3b58e47fac6d3bab3d4eec682405acf4605ed2e494eeb59e8c0bda5c92a82b8ba2cf67b4a8352667319ed26f58c3c9dd839b9ad1d6e439636c3372fb60ae2e8731541e037ac3eb16ca485f4477cf7527c9fcc9f3019e58ca3348068a2d3637ac6056324d727cc6f57d158201935e1f0b8e5632e39969a3e156121f1bd49de90f95f66f55b17427795ee36cb1748070799206233249c61cdea36f89266f58c3935deda403 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part421 : Excludes 0x8000400800000000000000000000000000 0xe7bc6396025100088410020040000000000 :=
  finishCode 141 0xd0338c23e0625317bc0d42c967b48c34e3eb473938c362018c362018b66514819d6369155a3900d58780c32e23e0a0d9aca4d77b4870569a72d393c405cd9202a0d5a9ac3c9f24c79cca2d95d1aa313e56a6b0f89f2b2589f2f02907f18dde7271f0ac6d408818bf2d4582eb051f0bda4e62f62c14d5f1ea5ac6f69732ad34d333da4b064a34639b6564b34ccdb22d9582ad3508398b9b67b4ad3472e30d5a88c36370a3ecb06b257b4a80ac36060d57184398c10d5d9acab53201ac6565ef03594382d299eb29295a392167ba9fc5a972d4d4022d9478b4a672ac1ed8161c1494ac6568a983084f97b4c3eb201b05646fa80568e403861af8440d83e87317bbc9173f98c35abb250d49f3da53ba9174a18c355c7acc9435a3900d2069396aec943201ad1e5a1106a169af83087a1a0b119606c3b48ba4a52841ecafb49dad160e0b02d7471158201ac0e38193e45b3461ce06f00b4e7b4ad4c1570c365614469bc1c127cbda6406d181032849630eb4741ec38f73593e567af69201cf8390a82b84d727cc7037b4a50c5b26d7499b0363819b5d84032cc557b2a0f5286d37907a6e5967b3da5847d1745607d6d42cbe4a193e49af41c5acb07b2ddb0955fb1f0cd4f07b0cba50d2770c34fe33944e06c3d49dad1e26b93e5a867184551e03059c7e39a8c3677220503ca49732a4a461ab0100dacf250d03b29081d940ef573859c9ded33d5dcca4035a6ac89c290e657b4cb2514693e461a6e12c1c4ef7bb8c3461b1c7e3988c362082025b306dea6e51277a4ec61a4f9969a703381c403186c403 (by decide +kernel)

private theorem part419 : Excludes 0x8000400800000000000000000000000000 0xe7bc6392025100088410020040000000000 :=
  splitAt 1 110 0xe7bc6392025100088410020040000000000 part421 part420 (by decide +kernel)

private theorem part417 : Excludes 0x8000400800000000000000000000000000 0xe7ac6392025100088410020040000000000 :=
  splitAt 1 128 0xe7ac6392025100088410020040000000000 part419 part418 (by decide +kernel)

private theorem part415 : Excludes 0x8000400800000000000000000000000000 0xe7ac6312025100088410020040000000000 :=
  splitAt 1 115 0xe7ac6312025100088410020040000000000 part417 part416 (by decide +kernel)

private theorem part413 : Excludes 0x8000400800000000000000000000000000 0xe5ac6312025100088410020040000000000 :=
  splitAt 1 133 0xe5ac6312025100088410020040000000000 part415 part414 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part424 : Excludes 0x8000480040000000000000000000000000 0xe79fe21ec20b24009241820090008000000 :=
  finishCode 85 0x208711dc88204186b38403550e4e0ab8e5aa139ab707f9acee572f7ad35ab6c03566489b574e4ed258bded59681d06708062e91e8c8f16ad9cb5ab72a840326bcd35409b9964ffad35ace4d769a82a650a854dab68d76b3a84ce4e4037208072d250068137bace653f1900ce22aa310b432082d419a61073815707f620a93e694b5565a69e8641bbd026b559cca4ef2fab1560e6c0b80f24f961134694cd477aab165ebea01c0d25694cc11587c1e58232c3c0128db96068f101bc1cdac24ef9a4b07f501006863a0d5d263c7e127cb4a61a7927c98f1f849f2b458dded5b5a1e0811406aec3d150aa93d3c00cce3d581b56d03ab4d581ce3d8c1b164dded5b7adc81d5a6b56d69b349603eb1649f2ee340e23382e9780e4f356ce5a5cb969a4d70dd93e49af356c9f288238982804f924ecf5926b97d40fb1bbdab69e06de5a6a79c9aec2589af390cdded5b2fac60e5a4abe49ae4f950dc72d393c4f9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part426 : Excludes 0x8000500040000000000000000000000000 0xe5ced2de82231400aa018800a0008000000 :=
  finishCode 91 0x3c90a408e244040357148398b38b118e4e8339ab6b115a8cc0b6adaa8ce41fe3efac1ce3ed419080230703500ca15411cd5b513bdb64f5b02dac307f57dd07f513c03b60fcc5948f97bd48670fbf2bed222b2739380de69aa84d03a9ff9ab67df83fb59d8857128398ac4567ad2993d6e6b5a4a0b5a531f7d545a1a8729c9296aea0b5066862bee3efc1fe57dcc0b58796dc0eeb49230cafb729a93cdded5b83fab8929694c8f139897907f735cf750ad927d83e7af893ed616aeb88ee350c63e01d738fcb276ad9c9d63b2d4daba83d62154416c4c5729b56d69ad5d419abee6aea44dab69e7969af756aeb0961bb8acdab69376a0e3f20cd26f3108841fd6a6e599816d5d377a0ce245c1e5a5ab496aec7df770c8527877d6a32bedca64c559ea85567b39bce63070ce0672d772146a154498a50d047356ce3ed5b967a727699b18ae1f7dac32d4d44f122da5ab4d25cb5860fed619eead5b156ad35c4550fbf293d69a72d509ca4f5a6a93e5a6ad3641eabec11a091 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part428 : Excludes 0x8100400040000000000000000000000000 0xf58eeb9fa20b06098201820080008000000 :=
  finishCode 35 0x1c46718c0ebc1df8514c0f1ad36839a0cda86a2f4d0f4401c82341ecd5ba0f29a2f05ef1e1c4db49ab57683cad1e5a6a00498b02139683f900ce62d4390668037815c6aecf5b58cc1fd6364c5398acf550440ddf2084782b4d851ac71314dca8336b0cf7735692e5abb07f3f9cb4d262b18a61fbe83f8e8d07ec0d87464e541e93965a69f8d07a6e5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part430 : Excludes 0xa000400040000000000000000000000000 0xe59dd39eaa0364008a01c00080008000000 :=
  finishCode 95 0x2d8882785c360b4d4c150400c821711dc3d039ed01bf5833244d86307f9abb17460ff30c503ef5326d9c2d6a73064ddec2f262b18a4f839e81f681863350cba273162fb90e2629bbddc393c1df396cd43891878b8ac5f1779bf4e4ea62b883f40f92ee5a9a93e59eca4f57d8bbe37e873d80521c45a3cf758c39cc45de6fd393b109817461e8c1fd67abe1cc6262a07da529ed903ef6d40fd1835a49bbc8ea4c563098b208438672d68098b0ba630741fddc7b0d07f6a7875d07e81f0efbd863989ffce22e2318c013162f7870ce5a735430fff1c463062ef5a3a07d63b070d07f022f0d01cc5307920fe3e18796d6187c247d9cd6d3969dc1fe0128f2d4c5f1ac335649b63b316297bcf48c3c1fe5a3b524766f559a76f6d5a9c1fdeead47737b05e7bab4e45ded49681884c15c177c3c35a38bbe26db5860fe3c39edad3b8c18bbe307350c78619b87865ef5718860bcf656b1ac44e62b3d23acd4340f9cc530046d1831f0c1ed49e4db83fb18d29949ed2f95f6b294f6b575a5a3cb967e80158cb925cbeafb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part431 : Excludes 0x8000400040000000000000000000000000 0xe79cc39e820304008201800080008000000 :=
  finishCode 121 0x340f2310a02f860d30ca602e9262c83f83facf58c694c81f694c7318602e23b9103382f5311c7ef27c9c9ce073155ee67ef27c8ba683fcb0539698bd8ab3dcc9ae62f27cabedf06316c4c150410c83f5322040fab8c01cc5c427cb13e8c3c1fce4f187a0fee65358bb894396aae5f9ace4f9a084f10068ef478c0178c2963dcbea275a69aa68c3963dccaa154a1cb4d2e5b97d9c5a6cd333819cd5c86d339eda703253cd5d72b9b8461a81f7d1dc0ebc9293988c347c3100d006731408a0463819c9e20771c4594c7316ac985d226917186af8c118c2eb3f83f9cc49f2d431f0c0113f1a4a5c93185d69a731359c3d15a6a435a864038c3cd5b491a85549e403398c40fa3b8c60c1ce631ffd69a6e541fa0ce398bdd569a6e56c15c1f0d07f58dad1ce62d43dd63ffabed45e8130c1ce39729b56d0027ef8e3e88318ce388981c9d07f292569aa2f417cb4d50da50e370b0bcffeb4d41fa7fe39897a5ab64d7524cc194f69264dc25e9398ad359c5b18c570e6aa1b945e9310e3a86e517a86e517826d4370f84e6ad5589ae94341fc2e9881f4791dc61061a71f9a5ec55305b59ce5a1d740fcd670f1b01021cb50471f8dcca403398a08e72193e4787356ce627114f9ce653f19c450663076315c50d9c9cdc3071cc1720bc9f2d2f9ebe9ed83f9cc4dc2a4950db18f22d81e36b3c8ed62aa08503ef77969ad676949c9d5459fc4c5500b97d046e65967e83f6ad900e (by decide +kernel)

private theorem part429 : Excludes 0x8000400040000000000000000000000000 0xe59cc39e820304008201800080008000000 :=
  splitAt 1 133 0xe59cc39e820304008201800080008000000 part431 part430 (by decide +kernel)

private theorem part427 : Excludes 0x8000400040000000000000000000000000 0xe58cc39e820304008201800080008000000 :=
  splitAt 1 128 0xe58cc39e820304008201800080008000000 part429 part428 (by decide +kernel)

private theorem part425 : Excludes 0x8000400040000000000000000000000000 0xe58cc29e820304008201800080008000000 :=
  splitAt 1 116 0xe58cc29e820304008201800080008000000 part427 part426 (by decide +kernel)

private theorem part423 : Excludes 0x8000400040000000000000000000000000 0xe58cc21e820304008201800080008000000 :=
  splitAt 1 115 0xe58cc21e820304008201800080008000000 part425 part424 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part433 : Excludes 0x8000400002008000000000000000000000 0xe5ed431ac61110078000944108240003004 :=
  finishCode 117 0x1c4781b86718c551b038f9cb5cc0efc0cb58ec0c5487b58e5a4b987270efce65174a07dab728d5f4801dc59060e2e960dd1816089ac498a5ef721b97d0031315107b1a05a6b56e83c928d2263d16b1d07d0d2a925c86e5f385c1b96adb58e1442154451eef41fd26a823419a92672f832d82b41f469aa496b1c823065936e23eb58deb2e4372f870614510c83d524b58c3c68824de46ca004597236498aa81c2d8330f841973575203103c9003184ef186b12e8c0bdb542a7f183f9c0dca2c5993daa2129e41ea7b4bde70383f939549f41e4bdf07f57dc9ff513c1b49ae801183972e41fa8545d2c61c8b41bd520641a7283f9006b4d49a8f848ff200d82e243480b90da04518923e19c864d76a5c83f23f878d69b390d1d713e47c2d8340a020fe1e09735a723e15a1493251da72c4f9c86c4f904681183f9735a72ce41c60f1b97d442d3927cce6b61bb20d041fe411b17d26ad391f0be8c3783c6823400ce4341ecd3f7d1e418393e60f1b60c4f907a81141fb0de6409f2d817a67b6ad35eae6d741fb1068c39fbc54ea2f89ae6d773150631c8410a0fd4032d4507a9f18d86ac2201b1249c7e36a4c1fd0024db87c28841fc7830f8569af57898a6e55622041ec4f95f098e6ef8c32a0147da07c98a81f9ab6f57982a4c583fc1fe7ad8e949ca4f9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part436 : Excludes 0x18000400002000000000200000000000000 0xe5be531ad71358038050c4d000200025000 :=
  finishCode 53 0xd83d8d23909c1e0a8370f57169a51498b18643821e391482122ac42c160cbbdd4bea8234199cb60f1a00c93b1f0cd624c740fb97da72ce31081f065b05683fbd756a66ef8f9f2c156a6a017ab9ea6616b4e418a2e9065a51542b1acdaa21e3174a0cc5b2f8398903183d1359ca290efa0fc98b0ba56c6319c41facc649a9c7c5d32085ab7317c98a4c77ba928e5829c7d68ef5d1748e1e7ba8ba47a2ac078d49f27b41426b30dcb576262c107a2075ebb24d60fef756a4a08dacee63dd640f97367bab525cbf41f5ac6d67731a73353cbd26b330c8ba507a0cb50ac5cd401a0cdb84f8c9d950a98645d21e39046d39 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part437 : Excludes 0x8000400002000000000200000000000000 0xf5ac4312c71118038040845000200025000 :=
  finishCode 107 0x6c1cc5e1f0398ad8a638881f41f8c06370acec9f272759dcf22887279042b3b27c877e39aa516410bc0d01cd53e334e586e4d70f1ce5f6b2cc590efbe8913941a1e359d93e67c1ec6314c71103e83f27ccb5139aacee6e1c427cc7350efbc04f99402f6da302b5183fb5249b724043bf0a400dc41fe1869865edb0f849cb41fc3c64db87c2b3b89b630d560602e65986307152193e4f9f317c3c6e23b900410d00c35781f0a9263f1a51528ed639a67187401a08e4f8cc595a88bd4e4e4f972208441785a126f07f9883181477b0b4b9ad5b878324049cab40b664a2a08d28b34cd26a4e55409cb2ced28a0c596a272d4f8cd6383f97bc9cad0280a20f85eb330b49f2a49818a7b901dc1c15a8a7e4e5aa498e5ae5f0dcc4e527cc28fa37072d860e2f5792086717c681bc26bcb5358db53d07a94727ca38947409c9012f1c1b6409a405ec2d399027078d3e2a21419ac6d1a339ad83e4f927cd1819cd6945361b53cbde8e3704ef4a2cd67465824ce4ea62d4e8389f7d86e3cf839c0856a793e6393cb51 (by decide +kernel)

private theorem part435 : Excludes 0x8000400002000000000200000000000000 0xe5ac4312c71118038040845000200025000 :=
  splitAt 1 136 0xe5ac4312c71118038040845000200025000 part437 part436 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part439 : Excludes 0x8000400002000001000000000000000000 0xe5ac4393c60918218008a44800224001201 :=
  finishCode 89 0x2205e110398c28f02d0d5b37ac0cb72fb99569af838830d907eb052f7b13cdea83f85eb2885f05309f320fd8b2b4d88fb16edebad678c08f3c1968fda0fe12b4a3b0dc5b2711691142d1082ddad07bd907ac5d71107f34cd89e703065a07e065cc4f6b2bc8e2032e732877e0ff2074dcab4727cac9507a6e59cca0cb349be0d658ffe8fd499a07c79f3dd4196ac20f64f293e56a3207dec7c18c71103e83f065c7355a4cb25802146e158710c32f6d87c307f4f98c1c7c32d356373044e1630d83fa50c1198b2e431f0bdb47c30bbe2628f8614272d07f0f197be721c1fdbc17ab17e5a69f3c9f2c2f9edab4d409b166065bd85c310b4d721c46e1eb741f5cbee657ab832c5d2d2359e47ea4cdcca1e3821a6b204deda83f6a7a0f60fb34d5c86f57631acb131d68eb5341fb97e58da0f498a83f91b24c55a98ba60ff35449625bb381a0fda4711b8065c2e958dcb476b2878d68f35456a683f306c81f40e832e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part441 : Excludes 0x8000400002000000000000040000000000 0xe5ac4312c6031a119000a4c000200001000 :=
  finishCode 127 0x110398d83d87317c18c5423030f843c682141fa98e2460503e71193e630d592b9460ff1b8588307f8c32c4b2dda85419700388fa0f865a6878c60ef02c6e6aeb17e302b471f0832e0cbad34c33208c7c2b4d4f9d1855a6ad1d8bf1f3d40ea431808c06183be90a370c379aca1e31838bd5bc6714c0f19bd660f8f3d82f2d4da6a6f56b3c92127ca389a46165a6bd840b6b53409b5968c38284fdeb0537a924e3f19f3e0de9477b09c4661b877c5def2028626d93bde02ddcb4d49c8a9e1e7b0dc137043b8e2400c00c35344909fce4a3b4fe1f0a885027378e4300803a3024e549083166aea0f51fa8136a4cd435a69bd541b3574e3e6f560105b13e50272ced07ac020f66b1a924e5a4f972126f34e51fa83d409b5263f18e9d89713949f2f61709e310b4d7c1b86710004ec7e32ddb525ac6e23b872d944e2e9411c8fd065ad4e4108eb28a503ed51174ad4dacf18345d2d358362933411b58dc86b3c4c569ba4cd0462e99a6e1e3721c416cbe0703989681f3969b6669b8e7e72f818c977187851a83f527b38f82009c310e65030cf6d2629865ac6063900672d16cb58e710c03200c98a0cb69aa3fc98b236d6a68ff9ace05d263878cc32c407064f68ba56a660d50acc4398e23701c182a6e656b3a0f41962e969ccb2704d878d07f2d4e30f34e51fa5a0b642b712749766d99a6e7357c0c330ba4e22619898a0cb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part442 : Excludes 0x8000400002000000000000000000000000 0xe5ac4312c60118019000a44040200001000 :=
  finishCode 143 0x440f69731b0780e62881b8f8356d9c6e1a0393b59e8c3b97da6e2f5388832c60f16eda66d6772fad8a635968c3bdc528e6f51e79ffd07e9479a729479cbed39408b1768c3ad1d8b24f9186a085802ddc0cb49093e56a7270f820fe83dad34dea3018bc68fd27c978e0f1ad35a4671cbf032cdb21e354180180c6e541f8b6460f353d07e8fd7abc5bb186b704f9861a9e5907a9f127cbc8fa13e66a8878c9f320767baa0fdf45f2146e1e01838bd4dcf27c5acae5f27cc3835a6bc0a4410942e8b4d9a6ad5b41ea03627cb53dab69a356c9f28df928ef61924707137acd39982a93927cb56d04731660ef8bbc9f3078d3e22f57b2145a6b176481b0458b21a527ca93e49b8b1414313bdbc601e0272b709c2a071f836cd5b697b97c37306d9ab70c353f341cc00ec376999bd5a729f1490b59e697a4d5485a138406b70c454f8c30d2fac1ce26bb0de6979b9507ab4d6adb888fd409cc1f477a44d02717d454e913861ad5b5a061b310630ec456adad35b862cc5ef186861e6ad9bd510851887220852128174cd35306a7c5ab682d41ea282e99ab61c1419bd89239cd69f1242b0556a6d5b5a69bd660aad4dec6ad832e40fad345d3388b4d30cc6f51e8cd4924cc8db5a6b56c58327c5ab6d82d36262a0041963d12ddcb4d4909c7d2224c54e188711c8822145210466f5982ab5341eb58e49a8ba43830ba4e0735260f72d4cdca9ed30c8ba580541eef2485272b470d8a07e48aad4e6a4a0f5c87b05823cf898ef5740fa454fe727b498a9f1514bd5e157a0fd3e2d679edb1875a3a7b5a72823 (by decide +kernel)

private theorem part440 : Excludes 0x8000400002000000000000000000000000 0xe5ac4312c60118019000a44000200001000 :=
  splitAt 1 42 0xe5ac4312c60118019000a44000200001000 part442 part441 (by decide +kernel)

private theorem part438 : Excludes 0x8000400002000000000000000000000000 0xe5ac4312c60118018000a44000200001000 :=
  splitAt 1 72 0xe5ac4312c60118018000a44000200001000 part440 part439 (by decide +kernel)

private theorem part434 : Excludes 0x8000400002000000000000000000000000 0xe5ac4312c60118018000844000200001000 :=
  splitAt 1 57 0xe5ac4312c60118018000844000200001000 part438 part435 (by decide +kernel)

private theorem part432 : Excludes 0x8000400000000000000000000000000000 0xe58c4212860100008000000000000000000 :=
  splitAt 4753 87 0xe5ac4312c60110018000844000200001000 part434 part433 (by decide +kernel)

private theorem part422 : Excludes 0x8000400000000000000000000000000000 0xe58c4212820100008000000000000000000 :=
  splitAt 1 102 0xe58c4212820100008000000000000000000 part432 part423 (by decide +kernel)

private theorem part412 : Excludes 0x8000400000000000000000000000000000 0xe58c4212020100008000000000000000000 :=
  splitAt 1 107 0xe58c4212020100008000000000000000000 part422 part413 (by decide +kernel)

private theorem part402 : Excludes 0x8000400000000000000000000000000000 0xe58c4012020100008000000000000000000 :=
  splitAt 1 117 0xe58c4012020100008000000000000000000 part412 part403 (by decide +kernel)

private theorem part392 : Excludes 0x8000400000000000000000000000000000 0xe48c4012020100008000000000000000000 :=
  splitAt 1 132 0xe48c4012020100008000000000000000000 part402 part393 (by decide +kernel)

private theorem part380 : Excludes 0x8000400000000000000000000000000000 0xc48c4012020100008000000000000000000 :=
  splitAt 1 137 0xc48c4012020100008000000000000000000 part392 part381 (by decide +kernel)

private theorem part346 : Excludes 0x8000400000000000000000000000000000 0xc48c0012020100008000000000000000000 :=
  splitAt 1 122 0xc48c0012020100008000000000000000000 part380 part347 (by decide +kernel)

private theorem part336 : Excludes 0x8000400000000000000000000000000000 0xc48c0002020100008000000000000000000 :=
  splitAt 1 112 0xc48c0002020100008000000000000000000 part346 part337 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part447 : Excludes 0xa0000b0000000000000000000000000000 0xe4b7f64a5daaa554005de00000000000000 :=
  finishCode 41 0x5e1686e2085707cac006de051a4cd89703a60f61b758bc18d4f7c1f521eb4362128058c4d71e286c66b1ad2453a92f72fa4cd6871bbd266c006c6625acac98e92f5ab8b6436f03a4f46011c7412c26db4b64a09bbd49b3555abb3d5d3deb57493a936106901d2b159eaf07b694a49c17ed299c7ad5d05dce655501d3239c5561ab0db8616074bd6c9af07b8409af2cee0f71f9547218926bbf81839cd60e960012f293dcd6f695a1869e6aabda549e8eb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part448 : Excludes 0x80000b0000000000000000000000000000 0xc617664a5808a450005de00000000000000 :=
  finishCode 127 0x821b862224661382fa8fb481ac02936303356deead5d05fb9266adb995abb460d42e943a0c0d949e0ed497c60d25681d2faad00ed80d681d831ab7058d44aa4d1d1cb436adb02d8ab062d00ed55149f358d066a4f93ff393d44b103a08e268941839cd472c7a0ce0db12f51ea48f58acb1d401a0cd81701adab7302c142942d0b578bea0ed40ea485f55a0c9416b0cf69526b480ed5a036f34b53d6a270538b65ebb06dd1c0cfcd3b694a505ed32c553fe92f6a1bc1023f8f63000ed660a06aff85b27e5241cb3b58ba08d4780eb07b5a8b5853057ccb5183d9b8d5f32d451f2c02a8d5b82ca6ef514ad0d6aeaff874ee6326b9bbdab63a3a0faa4f4f13d7289c9aeba312e62ead0e3f2b008c140d204e1eef0486302b4972cb585676199038d1832d792e5ed2b4909fc0a36b0c60da528034f7cd618c1b4a5006d5b37163b41fd6a2e4504fb91dab6ba391683dc1fc36ee4595427782865a1ad5d5f3398da8e8f9621685d20c4168066169b4e498ef5d033a4bd0660ed4516273dd40ca06b419a4be69c819d407250501a92b80cf021bc658b81940ce0ed83fc50372c819e207b188281bf8cc24adeaf358ded2e3d925e9339ebad531e2aa892123cc0a358b9bbe8c1a38c413bcbeb250478a6ef98805bcd637b497d5ed3391c36e6ef631506a9c2972fa935c5b2c2220b8356cde33dd417e5f569ccc3b723c0bf721c3c57b4b56dab7358deb20a1 (by decide +kernel)

private theorem part446 : Excludes 0x80000b0000000000000000000000000000 0xc417664a5808a450005de00000000000000 :=
  splitAt 1 133 0xc417664a5808a450005de00000000000000 part448 part447 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part450 : Excludes 0xa000030000000000000000000000000000 0xe4b7f4c81982a0540001e00000000000000 :=
  finishCode 91 0x410ee3f8ea3680e75a13c27149ec4289d501f282fe363a51568f31158668cda0fe4d7619b175503989b1e0db8b4d45700ad866a4d621987b6c90f05fb1747caae35665088e8c2d6a1559ec61e50bad2549a6c750aa3c650aaf0a4da0f6d6159d935ce628d98d62a25735a935685e00cb312c7cac5d9eead4786f2af14939bbc0cee829896203e40fc40c41cc417f2bf53faa4d418c5cd57e82fe83d8f9549aa2505fca15410a4ad4223e5949aa4f03881cd94690e62c0207e4ffac7549a90349c86de41fcb1d5a4ba0c4b949e81f541a772d4d28a9159cca3e55a9b60ca310731561446d09b6b49903e92b4a0a07e50bb4b5ebad2f92825d11f2a43e508a8ae0f694126dc8f941fa6081f583c8f92e69b1d062261a0e2d63621b457dc92b4a082de6258f940b6d5589b6b495a8b58d83286c1cc570377a43e05c8f1503e80f903f2a081f0dac8eb6a497349aed2f95c4f1601e782c672cad441429399267136d692b51377ce6b62fcb4751ca4cd2726ef (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part452 : Excludes 0x8080030000000000000000000000000000 0xf7957ccc1ca0b8505001e00000000000000 :=
  finishCode 129 0x811945e1f4398b68d42c9649cad24a064d7206ad08a150a270d4cb25606b58dab6f692ddcd633f7b08e7b5b9ada92d5b6a9bda63f7903602db6893b281b58626ba8a40c3350ea3109e1035423285cda6905527a50d2732c6d01e83f5d230b140d006921596a4e52072cb59074144f07da30a0bf1b4c60542eb53410a8567b6a84542eb5348fcb4230b8293db054230b2cedcd6b49410b9667b4a7bd6927ef9ac6f695a4a76e72cc81f7b49fcd042a2772cc093481bda4fe6a63a0d831081f82080b1bc481b181963a6f16a49774ffed298ffec41fbe206ac96731a7ae0fad5b3f7b10d428563789034fcb398d61ea155a8a89d67728551fab513efae8a80b665a3a0851fad4410c0d96a640d606cb0f6adbda4976d2f6b1c606641043285481b310b4410ac3683ed751444d19447107af69949a503901a84399672cac74ffac8203e72cb93cfff01058ab07f7329b0d49b30f630ac3b7b4ac9e61ea0f5ed2e45964ea2b735b0ed8aa6f18fe2ba3688e293659dbda477eb4740ec0bf378c821722c7ed4a1a085945a3c7ff28182d54c2eec7ff40fa70ac230e499a865dd1669f15a4b06d56a6b479c8f2c95a869c180d627f5472f759c7a0bf281c821817e821817ed297b4b20e828883141facee7b4ac74a06d43892e931401b57518651444a1973659dbda5692f69874291f7bac27f5a89f7c92f2c75ed27ff9a863bf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part454 : Excludes 0x8000130000000000000000000000000000 0xc65f7ccd9820b050026be00000000000000 :=
  finishCode 95 0x32902440bc330731461a8587c90f076a41480ab430ce4f683b549ed6189ae0ed3f99fce51390341da9e03b569334ee0f2b0f527a856694b585d46d1746a18858dc9eb377a0b41da813482ca4f2f983b50064c5969318116ca43d44e7f38c1ca4f2f983b41db3db42b66f1527c8c7508a9341da071039c20cc03b55c493c4054a2b0ce3f29bc520a405605cd5b419b4a498a6f12f9a47d0671015a8530bc46123eb4250d882e6c0bf1f6a708e41f63efc60da8ed61370fbf1bc402f1f3e0fee651c29bbcf9f3da5ac3460d676b42a881d7b4ce6183f827d006d259eb702fcfbec624c5444e017ed5b481ac2b3b9ed307d9a871818fbed437b4b5867b49f74d4b350c7daea2e880d8c1cd25377a89542e8136a1963646a82fd22e0755a9c7dd52681d5884717415697ce474acf4162a173f9c1ce50b97cc9483dcf6d83997cd1d2c553f9bd6e606b154dde922385f3722cd5b4f7bda5ac2901314fe74605c8af69352d181722cda03b554370be67c3db61f6b14cde29c2d4e692b5856a31ff630637d9ac25cd62118734fd61e6ef1f6ac3e6929bc6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part456 : Excludes 0x8000032000000000000000000000000000 0xc61d67c87900a0d04001f59000000000000 :=
  finishCode 127 0x2e0dc2b0c42f06017d1e06c01cacc02e648aa3ed03e2d969fcb258c19cc51e324540b205b4e062e50341fce45592b98c7ba83f9c8ed638e6290d1fab586281a50c1cb02361103d8bc3b87316a1c9276ae8395801d0c8f12e6c1c66ad8b662dd83955ff1cc5ec8318c417c83f62fc6f102f83b41cb24e51f73da528605b900320c5b0831ec6b12c77107e81f206c31783cc9fd51cc08ae3b8731837cf5d206aceda7ef5d9062d3b93d2b57418cb0306e206bda528648d881a90d580f447dcb3b0b89f440c293b4a1c3a12069cc588f3985ec5411e20e5924e40d98960e56acce45160860481ab401640b60b7881ad63486c14f2069e87c1f888017c0c28019062a255e01cf28ad6ae731723d06420a83d8f698a0673141f9cc65aa8e84de30c5c1cf2f005d398c17d5aa8e866248395446020c501cc1758c82e507e5037b6c5bb5aabd7478e4bd072b56e41fbd9c1ce31781cb022f1061cc610400ca2541fbd9616981654720e587428019cc6b17072b18317903ef65418a8466c15c881443988b6618bbdd54064ef58bc92118bbd9040b66076c60e4078b6498f3dad42f04370841034dc3203d21ea2b9a76b55862e063471c28302f9b85422a4d8200b205b253c3f52068f3e595c1ecfdef69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part458 : Excludes 0x8000034000000000000000000000000000 0xc61d6dcb9a00a2510001ee8000000000000 :=
  finishCode 85 0x88204571f4398c18f00c5d24076b06604ca3e5ed292f2ffa0ce41e97fe526ba8f63100e5419ce4f4a0b96640184ae7b4963c7122c16a9a0cd07ae599cd692b4720c69cc9456a4bda56a6a03281a78d53853a4bd4998f1dcc72d0526683f8022b1758ab965ed2fa418b813bd25631747cc28f721c1f56aee4958ac8f94313c611882ffb5092b6a4cc5f058b575a93054e623b574492d5b072b57647cb9ad1f3039525692b9a72d4949783960c4720e72d0507ed4952693bd1041fcc196adb54e41fa18c21c08a2d56361935da520bb6ae819e05dad56735a30cd865ff692c6b5735980c5d9aa68c70d8c37d6b1c1cd88ad397d18c18ba5883d9ed2a2b4068f3d07ea2320503408c92f0dbc803905af694f7cf6d37882ee57ea0c507e503841f46301caae20fe26b825d64e7ff16c9f0e8c3b06405307f6ad9ffd49aa179cc2b156adb309c2e8c40b65a7302ed8bb135e60b86c41325cd7b4cd3916ca85e4188396 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part460 : Excludes 0x8000030004000000000000000000000000 0xc71d65ceb800a1d00003e10280060008000 :=
  finishCode 115 0x1844f20c30bbd896218b81fbdb089107ed2992526e19a86317988e50326bb56deb734a520ab292818f3ddc82125327ad49e0ed661cc71bbd24283f89ae731378a43e6b0a0fce62b8440fa3b8af99a4a0ed18bba8d8351dac23499eb66b1016c1f50628f99eb68319862d619062929838cc3126bb56c1daa27862ed5b398b58620570d83989b8e370bb8d40c5e494b11e18b8ebe62fa58d5b8b9a7e55a29bbcfcb356cb9a929a207501cb2414e62d61770e62af992529ed6adad15cb339ad1e7305521e92916cc08ee3e8b438e62d615878c5c1caf02b8ba1cc616cbdb65ab940ded29038815fb2c4d836d296b0c1ee5aab0cd42a7e57b4caff0c4a47daaa5036c1aaa983d5e5ab8b6560f07d418a0fc253249e30eb07417c1f66ad9fbd8c51106283f7d1ed32d25aaa50359dbda66aac61ca0631791f2f696a1c317400af0f0220b8356d94641ec5707428312e6c7c183fbda48f741ecfca73187427c1514b9962d1c1fd832f6939883b67b49f048df3da6085701ca7ffa0fa503732bda4fcb20bd1f307f358c8f183e9cc49ae9336515c735c8fb7b49cc60c41fc5033f2c4a583f9f0564b06167683fbd6cfde317551d471ec47b3e0ad0d6ae8f982aa4d78d86c31587bd8d811be7b4c1fd693140ded2c5f894ea29 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part461 : Excludes 0x8000030000000000000000000000000000 0xc61d65ce1840a0500001e00000000000000 :=
  finishCode 47 0x2e1101864c5efa230842b8b3b5a4a85e18bbda41ca73183fc92b4a0b58c83d90641fe0858bce6341fac9462e00d8b1ab01398b4bd25681f1e3c92b398ac9545325058933da564a73123cc1236188c5d64aea41083f8ffb07f60bbda481b07f98ba81f40fcb1d83fb17d5c41fc4797b49cc407f2935ab6a15751f46615c206bd76624ac6d83681f72fbda503f356e072ac466b1bda549e82f95f6a17624b08d8188da8398c100bf8a063f5202a8463f29344dc24659256d63da61e7a8a4a0692b277cf69237cf69 (by decide +kernel)

private theorem part459 : Excludes 0x8000030000000000000000000000000000 0xc61d65ce1800a0500001e00000000000000 :=
  splitAt 1 98 0xc61d65ce1800a0500001e00000000000000 part461 part460 (by decide +kernel)

private theorem part457 : Excludes 0x8000030000000000000000000000000000 0xc61d65ca1800a0500001e00000000000000 :=
  splitAt 1 110 0xc61d65ca1800a0500001e00000000000000 part459 part458 (by decide +kernel)

private theorem part455 : Excludes 0x8000030000000000000000000000000000 0xc61d65c81800a0500001e00000000000000 :=
  splitAt 1 109 0xc61d65c81800a0500001e00000000000000 part457 part456 (by decide +kernel)

private theorem part453 : Excludes 0x8000030000000000000000000000000000 0xc61d64c81800a0500001e00000000000000 :=
  splitAt 1 116 0xc61d64c81800a0500001e00000000000000 part455 part454 (by decide +kernel)

private theorem part451 : Excludes 0x8000030000000000000000000000000000 0xc61564c81800a0500001e00000000000000 :=
  splitAt 1 127 0xc61564c81800a0500001e00000000000000 part453 part452 (by decide +kernel)

private theorem part449 : Excludes 0x8000030000000000000000000000000000 0xc41564c81800a0500001e00000000000000 :=
  splitAt 1 133 0xc41564c81800a0500001e00000000000000 part451 part450 (by decide +kernel)

private theorem part445 : Excludes 0x8000030000000000000000000000000000 0xc41564481800a0500001e00000000000000 :=
  splitAt 1 115 0xc41564481800a0500001e00000000000000 part449 part446 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part464 : Excludes 0x9000024000000000000000000000000000 0xe47fff10924c92492001248000000000000 :=
  finishCode 23 0x3980e581cf101705f95aacc596a9a47569a8e288da3d9c9b6c299c92941526cc37627cb13055b16525f220a22d3413328fd6570f256aea22708a131d45609762ec12783f846d01ae5f836ac665aab4e650b931c3633dad6aab57 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part466 : Excludes 0xb000020000000000000000000000000000 0xe4f5de14114680580001000000000000000 :=
  finishCode 93 0x1cc881946c1c8398b50d5581823e50eeac0e81980e75a147e3c989ae6b16a9974569a2798d62f577baa8955f72934792b4293635886a5422b4d735c1638c0a89549a0e79e4741ac073b085e1962eb43060ad367baad053faa4d377c0b54416816aa935ecb289569af5f93ff07958bce6f16ab38ac0f241829ff8ba2afb969a93d500ca297d1a807397e65ab82dc5aaae2d0b82d35cab16dc98a1a9058acf65279315ee741e479e1af7b6cd652dba805cdeda2c88828f51c377a483cf623d07b156ad0c112e5f89b6c4998be0b705bcc1f16aac0c216ee500abfc16e2d55c185f2d349b65d157dc6c3500abfd67b39ad6363e55a6a60b002ae26d8f3cbc2b43a30b3485a92e4305bb05d8befe17e6073b681dd49147a7e58b566d34f48215acaa846067bbad4cba24d7369c5d14ff8f266a5b5845ab039d686c07cac00774273010c37ab4d169ad365918b30e9c16aa4f485c0b52dda80493a5f96c1800ee9ee60d7b585eaab175a183060f330a4b765f90d7a608e17e5eb700fd282e6f1cb936c357399434f394c35ee5f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part468 : Excludes 0x9000020400000000000000000000000000 0xf677fe9410e4805a0121020408000000000 :=
  finishCode 19 0x20c650622d823873162cca3f6ada935ab70e81af969ad5b5f0da73ddcfe62ad0d982c5a5b2a0d5b53124053b4de049b0a62dd8e658b25dd2ddc6c38c08b4e3030396 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part469 : Excludes 0x9000020000000000000000000000000000 0xe675d614504480480001000000000000000 :=
  finishCode 157 0x721987d1d01fe9034dc640740ee9f8d5b730b76d47a30e125016ac5d85e3af035c7b94958e9e0c40016f41ccbda3cf80b6b272eac90b05ba80b224892b15ec8134a0c61e26b97b585f317cbaae4f8bf2ce1cc5ab64d79a62e55732b1258beb3da0fed65398c1dd6d0bf24cd93fed5b05ba04cf7f165586e0b72ddb56db01facb4d3988775b47f19017fb8f61e78fd416ed5b816f24ec7ea4d72eec5031fac18da3e8e63c882d969a0e71858f26624b17ce62b3d6516855105b2d35066a3d949e81d5a6ba092140c76338f52825f948e86de40997b436f2c1102805ed7aace4f497b4e6724b5558c4c00e6a4f143c5bd5aac9e94f4cd532deabfe509b58525ee4f398cb3d17fbc8fa3b8880c5d70580bea8c1f85f96aace4383cb90e690a935ac27eda30f073614ac4e23eb584ddec01bbe5a6940d69b280d65eb026050398b25f9611b0281cafd8c3ad5630f34bda731ee60e71870cfd183651445a6ca036ada934a067318fdb183596a84569a7c1f85f5737c3a746dce6f46dce6f6249cc6281b28a02d35aab16edab6731498c2396ad8f3cd570f3c4eae6f624978594072a80b4d0dbcd611e39cc432f41cdab6b411e3b4b6152b56d89291d881fc671e4281c31117fb28a0320d83087316adc5e1690ac5c16ad550608f266adad05bb9ab60b75a682de6ad96edab71cc560340b771bbd69ad5b48bab89433f1cb3d61bad1d5fb2ca4b771bbd69ad5b149c6c962fb56cbdab178d925f95a18c45905f1844619c55016e5e19686905920b2d0cbf2b17816ed82d073183fcc37361b56d4521b962cce6583fa934a065038bf2d5b698ca2539897e4a067319a62d4b740fc71bbd682d5b5a69864c5e0e7494c2db (by decide +kernel)

private theorem part467 : Excludes 0x9000020000000000000000000000000000 0xe675d614104480480001000000000000000 :=
  splitAt 1 106 0xe675d614104480480001000000000000000 part469 part468 (by decide +kernel)

private theorem part465 : Excludes 0x9000020000000000000000000000000000 0xe475d614104480480001000000000000000 :=
  splitAt 1 133 0xe475d614104480480001000000000000000 part467 part466 (by decide +kernel)

private theorem part463 : Excludes 0x9000020000000000000000000000000000 0xe475d610104480480001000000000000000 :=
  splitAt 1 110 0xe475d610104480480001000000000000000 part465 part464 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part471 : Excludes 0x28000020000000000000000000000000000 0xd75744111000a1400001000000000000000 :=
  finishCode 111 0xf03a0e43d81f1811e45801ca0ed5aac6b15a69cdc7c22e7969ade309061c74e6ed6596828311f0c91d58a8f86418a4be4189cc5686f11039bbdb60b5b56dece5c9386a0c569a2e7907e3e12ffb20b0356e419bda4b9283f1f0b4fe698a0045ce83f44188f2d350c6aec5ff419c83d281c3e141fab87374f0e625cd8fa2e610479c34bfec831661f0963e5ab8d3da965ff91f23e179190076ae0d6280821515d07f3f1a0fce623e16b0c70f41f9bce6f1886adcc3b3989cdc74735858b270d6acc6f3398bda61adad5ce62d316a597a64109bcce1ed2310bc1cace6ecc34a660683b47baa1581520ed416cf69606ac5c1da9827070d510e6327ac1dab0f527b12cb9b1cc589ec414b0e6223d9ab66d3490b50e173a70e42d46478a7adeea0ed49383b64f7c731076c18e603b45cf1cc542b28f4dde18137fb98d41bfe0deb58501a2e7509ca2740ecb4d77184531e439bb682e78e62a03311acae6a39804a0671d407c7314189cae317b2088358f6328801526cb49406940d40417d07147aa4f4b773da523b181417a0b6526a4acc329415a8cf696249c3d8c387a8082f266cf5b35aa50563a619596c6b59686b438e626e13879865b42819cc565b24bd89262f05ccc49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part474 : Excludes 0x8480020000000000000000000000000000 0xf7877d1d349490424001000000000000000 :=
  finishCode 39 0xc42a08c01663f2b58cb9ab253988754e1e71d6a0e571cc50421d5410c731395ae0a2320ca0755ab7280d49ab11398c6066ada38b514c18459e92865a3b56e302b253948d8651cad1dab67319ab707565a9c1d5731305c150641ed324ed60e3e1418a0fd748116a3243c9ae945694c19f4a1acee386cb496a0e1b140d69b1a9d5e31cc5c8f313dab6915731b0b4e1a503 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part476 : Excludes 0x8080060000000000000000000000000000 0xf7e5dc943682b141400f000000000000000 :=
  finishCode 99 0x6c15c5e190398a20c4358da2084d87356d69ab53593b4c67b5ad35ac25f9379be89179a625f9379b14e3699f9547eb4d5a9c1ee2fca085187d1882fc9bce38ec1fe723940e0f69177b6cb4716483065a39cad07ed3199074170341ac3f8b0083f6f162f1f8ce1e0c11f0c6f35a3cf696aac50336b9bcc7c32d4cde683f3b1ac4f101eda284e527b9161dfb1665a9b91e3699c35ed2d37a30ae618c19c35bc5a181b1cace1a9a2d1e3f186bce3a5959aa2917692ac6e7b492d4312b1b923ed316a5ba0b84008215307c2c379acab4141fa47e0f703060f7398e0fed53395b92507efa3100c19ac271d5159cdcda727fdacad61386939662c830568060ca276b0a854e1ac435071d9a520c138ec9ff526abfe6b08b24bf2fa308b41c3639bb508c310c81c747332d5d8529432fcb4de6b2c5f96a8c1b7164a4c51c38eb4b61569f8e80180387c5037b4ce499ed2b4d387bc8c22f00b78bc22c956230f303587aa3d272940dcc30e6cb76e65281cb4d49dcb4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part478 : Excludes 0x8180020000000000000000000000000000 0xf5e57c543cc0d040c001000000000000000 :=
  finishCode 51 0x6a1787d1802029cc61f2875501f0f94e624d79a922c91fa8756145d081a9c2109396c0c04c121e0c18b9a83f060c5cd417a8065a68304707312dc920c193016cad4e27296ee7b4c1cc326d8358a018da60778c0a0bd042b4d9eda5cd500cc02a0840b64c0740b9a90f7aecb51417a76624fbd756a27df9a526ad619ad3588aa4f969a9158182860efe40fad1e462144f0de6737599d1815a8bdddab6d61398ad35ed31cc5aaa7e5651645a6acce51eacec166a01907e731262864604da8f51fb24e569a737 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part479 : Excludes 0x8080020000000000000000000000000000 0xf5d55c54148090404001000000000000000 :=
  finishCode 117 0x4281f56f1885a1507507da72b39bad1e8c09ff501a7dd947ac0d811a850ad1877b6830549e405206ac8b8289d63b02cd6a2729949b2d4e3027296adb5466128fb505a7294d1a854081a701c7502724c5a86f5b98a6d516aecb51060aa0da1c753ff35949ae7f358ecd5b650e631fcd3ff314d6a2b538c0c13573597e51e6d29206b98982d0ca1c36045e118398bdb66ada40d47aa2785923bf928a9034614449db9964eda00cbf2b33620cd3f5a6c9ef694a00da6f328c83685f93b0592f5b89ae7df69bcd25608bda51fb24c4e63247cd4739644ce5f96a8a7094393fef6d527a49d206d83a8af13989b163efad5cf733575cd6b1d8fbed5b11e9ee5ed2b33513c9274819c35784c0e633594bf2b01881a7315c144735c93b59dad25504c160e6f3730cc4f83fc60661dcb07401cae398ca3007316f13859eca4d58ea40d28aa83a8b519ed20c158e8b653df461561ef65262accc36f3d9435f2d2477f2d4d806f1506a5c3a958db50deca9214a2a30a22856587a93d6a2d3f8f7aa4f1dfcc2d9a7e9d96aeb594bf29ff969b31645b2c4328d42d00c1363ca257ab8f95aab180a4d512c1635a6ad463072d34d8f2765686a3d487b595186b2ca15513cb57 (by decide +kernel)

private theorem part477 : Excludes 0x8080020000000000000000000000000000 0xf5c55c54148090404001000000000000000 :=
  splitAt 1 128 0xf5c55c54148090404001000000000000000 part479 part478 (by decide +kernel)

private theorem part475 : Excludes 0x8080020000000000000000000000000000 0xf5c55c14148090404001000000000000000 :=
  splitAt 1 114 0xf5c55c14148090404001000000000000000 part477 part476 (by decide +kernel)

private theorem part473 : Excludes 0x8080020000000000000000000000000000 0xf5855c14148090404001000000000000000 :=
  splitAt 1 130 0xf5855c14148090404001000000000000000 part475 part474 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part481 : Excludes 0x8000220000000000000000000000000000 0xe50d64931080c0401111000000000000000 :=
  finishCode 109 0x214821a88820c800a0707d45fe30b6720417cb28b2f880a737379ac44e6240596a71cddc8661f41f6ad1e6ae9cdc80a277967a1d5593c7291e0c94150ab702f38015030c87d5cb339ac762e6b9c7ad53969a3f5730c5d55a6b90cc1c3e07690143cb062e0b4d076a0be41fac46513b0872b85b6e6f311b54e387b58d67b356cc4a831076ba030b6f169a1f55aace6b48ab524e5617593c25cc1995a8935d69a72b9847719c69200395b56e508b4e56a6729311b20729253c2cf40fbdde8c29cc4b9b13bce62623410c5033989cacc47328c82e1001cc6512b56d25e81f2819cc683fb58d07e81f387c80f2819cc5a7328fce6235986c29e1c8e82d36006e1c8513c1dd0faa606c78182a271e8abf63988b5549e1b796a62d540fc731060c5f9527c41023907315903eaa3d949eb3d879eb53588ca4f2628abc7833a0afd837282f418879547b260a8330821154c0c10dcac9e6e1985e0e630f945aa1d55a4c0c10f2ac9e5a9c5ed74220398c94166037320bc3cab11898b09041822d5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part483 : Excludes 0x8000020800000000000000000000000000 0xe50d6f14124080480401041040000000000 :=
  finishCode 67 0x821e0882004401d21f5501b45805fef6d969a73116ab5765a6a93cdde982d360c09ab669d9cc42da6ef17fcd558e62d53722b4bc5da50336bc28d4330fa1bce206af07319aaa6ef2f08be4dae3f5571747209633055ed209b5a38b65272d2f82daf67272bda41362f936b8be67abcb4d6aa8be547b2d3503ad254f68bcce6e70f379c7376c1985a69cc4ddf1f94b9a1858dde38d581ad1549f2d347ca4c56601cb0f9481ab4d905a833074b98fa40082d881a317179cd255a69cdc81a70f5a1c8281c3f50dcc6e1272ad345f26d7281940e416c3f5272c28d244070f38e9cc6281b9666b19ea524ed397b498643b2e62bee4829cc49de60b31793e67b4ad443b215d0b2b60cc0f8639887656372d34e62a254217058ec2cf377b17d6a24d796a64db167c6ef (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part486 : Excludes 0x8100020002000000000000000000000000 0xf52d7f10f040d060c041804180010001000 :=
  finishCode 75 0x428fa410e4370da10359417cc731272c1fd05aa27949e2f96c09cb3105ab307f02ccb4d58eae90620b5a7341fcfc2d538f8307f4909fb646127b0e94e626f3387a98862382f93f7a0bc0bf41e53e2289050cf696a48be641fc1e6138a7c55f692b17caa08c33070f6e1b01e2acee6a49734e621d5272caf15a48e767b4a4cc8d30634ffed5b398935dc8721cc1557da4743aa4d74720ff390d2821b9925ee435c18c721cb497abcd5b83f9bbd6a73d8ba3909c2f0945417c8215a68fd4f9b35245f2a01944e7cd8c0ac4479e4e51faa4845b2980be5ab70dc49ca27d9a5e9f10b0b54cdaf1f345f22f987ead82e0c629882f907ecc2f082192168d97ae86d4e621d572140290f95f65cd5a8a7c6527c4c59002c61cc5eeb31056a64db407936e258c4bb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part488 : Excludes 0x8400020002000000000000000000000000 0xe5bfe718f01490660011804300010001000 :=
  finishCode 111 0x10a440ca280503620e628e0f866ada934e1f27c5002a256ada07e59dcf694789ffd03ec8360e4330a807653041fce3d16c9f840331ee5cb290f83ccc4f4f89ac5c7a81f731a731ac6306f5b1f0ac758beb5140fb04635885049aeb1d5a8a4ae6a98f85c86214062cc7b930ca30f699cbeb51724cd39358ce6b009a7c563a7ef5a8b05e387b90a827c67b4b9256769274f8cf6959da455cca70f9102a0dc6c1ab6ca260a3954098eb2d809ed51377bd5cfc2e659eaef6b98be06b377ad3590621cc71ac5c7ae4f4f4b4e43b31878022c5d3f0bdd58bb35946b2019387bdd53c381c9f39ad892b4d62fab8e618fde6b18c3b92479ee498b63398cfded39387b20b828965a6a40cfa22d9418ad0657fb98e16cb28d83101b99c86a2530c97d549aa82b84d785b2831a0ff397cddeb81fbcbc72fce6b625b4e4dded65146b994c3312ee57fb20a8280b419ebae6b41782847a27e19062e6b16c97d672fa07c5b33995eeae42e88a39ae358b4e4b7690349cb6037fa0fee5f0e8a03c5b27e2a0aff879e7ef387931e6a5963e7ad8d2dcd67ef60ab60e6240e7b5a8ad07e80f7b4c4c7595c5856a4bda435a7ef3f7c0a1387ae0d83103e16303b2b41962273162fad4505e9e996a3004582e0a17249cc4ba312ec79eb5162ccc154a0a3e4e62927 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part490 : Excludes 0x18000020002000000000000000000000000 0xe57d5710f000d0e00001c0c100010001000 :=
  finishCode 65 0x390dc3310a0795787d07eac80394b7b28548eb3da4b1e8fb258ce6b5aba7c5ab6f6418da310f22cb64edad4c81a6194f1cb339ad69ae3d9cb20038d627ef7b4a8541dad498f52c195abad341da0e59ed2b4d206c9f1262a700e55a0c18d5a6a80524ee4f96824c7527ad34962fa3c8e6b9cc6f7569497d41ca0e9851944d1063356ce1eb4d419a3c65a6b17e1e8a0c4f828319906c18c6a9ce6b5a6a0bd062d539eeab155a6b17e838a804c32a275a6cfa3c8d5381ca0ed5d0e1f34e569a83341ea50b4d9ab6e4f69cbda5c8ab2b406b991879ed2d65418b4e65d19857162b0b6569a92769ccc4b622ac565a0a0fcfdeb4d8c3c4c77b696f49aee6b7b4b4e590074a60f759ab6b4183f9fc413ec19624a0fd89320bd8631ffe0feb15 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part491 : Excludes 0x8000020002000000000000000000000000 0xf57d4710f00090600001804100010001000 :=
  finishCode 159 0x721b87d03eaf2311061035cc59dc60117f8c5dcd71c3cfc28e3281a688f5902670f3fecb4130cb98920c2d5454118596b17e83f935d64ab3b25ecd3726b863d6ae0991d7cc5f1e3ac3c78f3594d86c31587b17e7adac3d90277bb8e3d9abac4162797b67bbcb4210a01ff501a92f9eee5e93e0a5050633105ec5c1b0354c6e13879f060fe9e30be5a68f3dcd7054565a70f2ddbda479f20f569a701965af69838a5047fa7e268c81c3dcc831703f7b0be418c1c609bb9adeef1b0d86290b968294162fc019596c1cd6827c320b412ddc5f97ac97a52166c3919b06004e596c1cc9528fb61bb126016bd6478ee620083171ece4f2f4b0dcbd3307d283418f632050363140418b07e61b97a56832d34fde6e18bd2b414009cc6370c1fcbd28fb8bc2c5f7b48fd4e62bc31073172cc61972cce6b3e0b9864f8ad3565a6197d1e48301db0c5de05a097a0e55a6cd53387c93358ab10b412f62eaa4ad682b4d41e9c3e4a0b98658b92f56aee6b5a0b837169ad8242d01f093ce1e821398811e419bda52831cc47c28214a174593c8315a3acad05a83d3a1ed7356d65680d641c8b2d5cfc200b96aed8320b15a0ff1874979f850627319acaf696adcc1f400dc730bf290b497d06f3efa0fcfc338f586f20c60e6b1583fa504f82e3d9c9e831387b21062e0f22c56410940d28410ac565a0b07e398cc3762cad04a06ae30be7b6bda497a7314938a9e692b54cf82e6b1f09cc62e0bda5242b4d791dc781b0074b210a2e02ff2819ee6417a005a7f0de5686b82583e1417c6ef512c731398cb414ffac5c5ff276e09e858d62ec495a0940d69a503862e82f98beb431f09cc4616d8320b830080141080067b6ad34372b15398d07f5a6c90b49e97a67329cc5ab66d75a0c70f (by decide +kernel)

private theorem part489 : Excludes 0x8000020002000000000000000000000000 0xe57d4710f00090600001804100010001000 :=
  splitAt 1 136 0xe57d4710f00090600001804100010001000 part491 part490 (by decide +kernel)

private theorem part487 : Excludes 0x8000020002000000000000000000000000 0xe53d4710f00090600001804100010001000 :=
  splitAt 1 130 0xe53d4710f00090600001804100010001000 part489 part488 (by decide +kernel)

private theorem part485 : Excludes 0x8000020002000000000000000000000000 0xe52d4710f00090600001804100010001000 :=
  splitAt 1 128 0xe52d4710f00090600001804100010001000 part487 part486 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part493 : Excludes 0x8020020040000000000000000000000000 0xe5ddcf98d23281483201006004008000000 :=
  finishCode 31 0x1103c0e43c81f5851b4281ad4e83fac545fe6d7989eb570dbc73115ec8215a6af8f22d056aea2795f6d5351586dc5fea3d95f61b759ece455a6985db8281ac064f3c1c42c6b4d418a4c5286c1f9ebe1634189fbd69a5c3c8b4d8513db2c4d6aac5530b9bbe69fac4d002a3d0d0cafb1e88296146715416dc5cf30bb9ae7308225ab662f41fa84e49dad5dab62d58fdea27 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part495 : Excludes 0xa000020040000000000000000000000000 0xe58fd6989122a0500a01402004008000000 :=
  finishCode 73 0xda310ae410b11593b90e6b942ab4916aa7fc3eaa17945692b398c60e3f7a4f5283103a0801a89418212570207d4ddf293d69ad635aac7ef96a2e6f417abecdde981b1e5a697b60feafb26dbdde167ac01f549eb6080f95f69e9526b9ae57d936e4f0ec72ccafb4ff935d44eafb942b2bedcdef22302d5074b496737a93d42ab4d944eb13962e7bd527abedd0822045abcd555a6b96d0021f5074b181f52d7c83f26dc1932fcac0b5787c22cf8116031c8dc86b170cdc4db16ad004090407d6074a60d81b1d5c5a8cd5983fb05c7c273162fc4bb3dcc1fd49a5bb95e23cf25db50d82c0550398a0be5ab829630701653ced398c2b05d60f2d36623b5768c1936cd8ec1f2fc87d47c26e3186c754079ed3f9cde6ef6aa895e46db105a7f34a6400ad34bf2b45 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part497 : Excludes 0x8000820040000000000000000000000000 0xf79fc71c982682441243002104008000000 :=
  finishCode 25 0x410e63c08e0c2c3ea90b9c72e5349eabed67a7319ac683158aae0617596cd6157cbd556766017abc9e7248b4e4a068e39ac2e4f2f6940c3eae6278b8185d3051fcd5b5a89b8d03e8317b9c9e958ea846370a7a6737a844c4688140d406ada585f58c1c6ef8c1cf738dc6e4f727cb51 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part498 : Excludes 0x8000020040000000000000000000000000 0xe70fce18902280400201002004008000000 :=
  finishCode 145 0xd2310b4299061ca4e6ee603b4977311cc5e5f5906707d5346a0e560ed85f283d48ec3118020c74062282d8bd292b5a6cf5d6adb4fdaba0ed8c1cf756ada3545e6b014a0a0b66ada4ac5e7043c9064083116501dab57893e1675019c74a0671d9aaaf738dded5d281b68ce350e61e8623179b576409b57638eb289a07d638ea04d9074140497cd3f4a086de580a475686c259cd6d5b46ab0ee0faa335aba1b7587cc0b6ae87d5ac27f38e3a6233f9c0e50fa8e6e7ab96ed1e2b2b07287d5186e0e3ae82a81f57bac5bb58bb20f759a8ef592fca336729cf776ad97e562e8cd857a49f2fcac55b06d1d06503eaaa2c4e398ac5d026e6203e7bab0be0e2f5d92573dccfc28312f4af0f57926206b0b19cc49ae662cf60b7bd5c2c66ef9cca1f588e71f7cb769eb696b585cc6715c31198bd3cf242d64e50392572bed28260d38ea4ae606940e0c821e07afcd5d2819c346220ed2fcc9db281b51ce1a3114c168650e1aac2a8503167cb010d7931cc2ed5ba30e4c74a1ad3503f3494c2e93b55182f311d1e6617418cc2f561cc281b9ae1e39bbdebec2f30bb97e7afb8f53cf185d06281f7312632d34a0706f58b9bbd3ce6174f3cf736d2206e05e6d298e1ad470faaca65a6cd5b16dacb41ca0e583eb0441881d8dfed5d2818c441dadc440d407d59c73168179ad36416a0cdcb741b478e943576612b155ab64b95a1abc66b0b4a569a6ff9ac2b434a0973135d69b039637f92e505a0e59b87319c5c0e630f3e3066ef30b98bcdff140ce62617593c50337fc40e3d8dfee6b281b50e2faacb657dac9ca066ff (by decide +kernel)

private theorem part496 : Excludes 0x8000020040000000000000000000000000 0xe70fc618902280400201002004008000000 :=
  splitAt 1 119 0xe70fc618902280400201002004008000000 part498 part497 (by decide +kernel)

private theorem part494 : Excludes 0x8000020040000000000000000000000000 0xe50fc618902280400201002004008000000 :=
  splitAt 1 133 0xe50fc618902280400201002004008000000 part496 part495 (by decide +kernel)

private theorem part492 : Excludes 0x8000020000000000000000000000000000 0xe50d4610902080400001000000000000000 :=
  splitAt 4753 125 0xe50dc618902280400201002004008000000 part494 part493 (by decide +kernel)

private theorem part484 : Excludes 0x8000020000000000000000000000000000 0xe50d4610900080400001000000000000000 :=
  splitAt 1 97 0xe50d4610900080400001000000000000000 part492 part485 (by decide +kernel)

private theorem part482 : Excludes 0x8000020000000000000000000000000000 0xe50d4610100080400001000000000000000 :=
  splitAt 1 107 0xe50d4610100080400001000000000000000 part484 part483 (by decide +kernel)

private theorem part480 : Excludes 0x8000020000000000000000000000000000 0xe50d4410100080400001000000000000000 :=
  splitAt 1 117 0xe50d4410100080400001000000000000000 part482 part481 (by decide +kernel)

private theorem part472 : Excludes 0x8000020000000000000000000000000000 0xe5054410100080400001000000000000000 :=
  splitAt 1 127 0xe5054410100080400001000000000000000 part480 part473 (by decide +kernel)

private theorem part470 : Excludes 0x8000020000000000000000000000000000 0xc5054410100080400001000000000000000 :=
  splitAt 1 137 0xc5054410100080400001000000000000000 part472 part471 (by decide +kernel)

private theorem part462 : Excludes 0x8000020000000000000000000000000000 0xc4054410100080400001000000000000000 :=
  splitAt 1 132 0xc4054410100080400001000000000000000 part470 part463 (by decide +kernel)

private theorem part444 : Excludes 0x8000020000000000000000000000000000 0xc4054400100080400001000000000000000 :=
  splitAt 1 112 0xc4054400100080400001000000000000000 part462 part445 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part502 : Excludes 0xa000014000000000000000000000000000 0xe4bffc690aa0aa1540002a8000000000000 :=
  finishCode 31 0x399103a87317b4cd673f5a40c3be0e73d18849ecd63481c61cbf6a2b526a98be095e835a7bc37e6e72fd826e373c61e014c1ad3b690360ba03e47aa8e43bf038e106017400ac4db0c483a524e93351147f240c98e1b19206d62086b19826f6962d86ecb960e981d3316d445d098306ed457131d47e5fba306b29596ad5c3620af (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part504 : Excludes 0x18000014000000000000000000000000000 0xe63dae692a00333300002a8000000000000 :=
  finishCode 39 0x3e8da3d04c781c63eb209b081e34407d6b2f833ad533f8a8e5c873da5cbef6996c071a70b2b907ea2b51fa85e41fb53c05f461d89a7eb7b2b54d6aad4f5d1b4611980e7ab8960b6417724cc8db1ec5eba92705d9fae05dbdae6adb5655fa3bb661a7320bdc927c16ad924d866c4516cac9e26ab56de047ec9213f5c83f5c12c4e107ef6d9ab61417b4b96562e6f55a0b97d6ab3da60df0a9d626d53418a58b1769ccb5550bcd63 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part506 : Excludes 0x8008014000000000000000000000000000 0xd73c2c690e20621b01102a8000000000000 :=
  finishCode 117 0x731e8571b4398c48ba3a906104cfe7208c62ea4208d25724bd07ad639ed291969aba031791eaf6d837e5fb1d59bc4de3104c62eba2d883d8bfe6f10e5a28f698fc66f11e9a00d883e107af6d8322f6948382567b6c1f604abdb51c5b0deb17cdcc6a3f7b4c2a140696fc323359dcc6d00c5cec378b59e2e6bdb5acf1734ec595cd635abc8e3821f46d1d0209a41e05d8c5e0f335747560bb2fd9bc4de30c5ca87517448182ac45526c0b96a4ad151c0e5ca4d0e5ca256adad892356e722c604bfea4d8f9a4d758bc7cd0ccb56cb9a0bb95f67eb4fe8675ab706358e4feb12c1761cb37ab12e05ca88a398172c4951f93bd70630de32845cc61b105a9b64deac5f8de25cd0e5c5cd2ff9bc56c7d0f4470bce7c3926526b53d256a241b6272b0bd47e0b1985e6f50e5bda54c890de2f699cbec49836b4e5746adc1cb6adca119a9ed62908e24bc1633da49de92b2c1a731f45892c2f80320b17b49bc5ab73da472313bd4727d17b482be891f469cb54d4c1fdb56e2fdb59e6ad925d3fa2c19866d5b5e0a858ccd5b4febda568a941e81a98c0cb55619c34f1bbc1e429ef658c2cc1b05d86c4f87b2c475378a41c92716fdd4821c934604322d5b1f5b54d25e4131f5c071862618d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part508 : Excludes 0x8000114000000000000000000000000000 0xd65efc699a203211022a2a8000000000000 :=
  finishCode 69 0x811cc5e1b4398ae8c43490798be66f126b859c1760ed209a20921fce40997cc9bf06356e03283b49fa9406a6839858cfba4d7058c6f1355ca2b2f9b16d0266f189aed5b076904e0e717ee30241307697ee07693f5b48301db078d240eda49e2c4c60dcc607d26f8eacec727c1e62d39bc5eda0298243079365c6f1209ca62688e075e378975d42e4fd2fdb68d23986f183ae6f19826d431e1a04e3031fcd8b66f19385109fae6b9ed26f17b8a8fcde33da5ed3285c79ef617b8ba8ba348c4288813416cb316adc61d406a3f5a9c82d491ab28032f9cf691e1b50e5a9c8136acaf09e2188017cded3356cdead33a0e7185508cf69626b56e626c60e0eba48d5ba30e5f305dcd43 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part509 : Excludes 0x8000014000000000000000000000000000 0xd61cad690a00221100002a8000000000000 :=
  finishCode 103 0x418d44085212928c4e398b496594a7cdeda80f189ba902411122e83178a223fb69062eb6078cde33da568ac2f7b4cd673f8c6052574605ed2d5b0f1c1e39256511398b10b04485116b062ef699ab66f194228019ab683f48cb585e792568310ebc6067baad55ed239718bb56e3f9bdb43ae317495c5ff2888c5dcc571d4398bc0fa3480e57b4c1db209bdd6483b48b42482d96acd0734f9c614776f75619a925a5300c5cd6f6d0e7bdd5487281e839a885487104df46d14c72cb93d20ee639a9a9333788eae499b1096238cb13352478e6b18fbad6362fc6b10d79b2c78f2885486ea3e874241cfe6a0d072904e3033065cb2c5f958490f451aa90cfd72d560eb0dd439ee6b431442e599cd6f6d8f7b0730e7a43d24611a44109bf31147767eb05dcd5d8d865ff26fcc339abb0732c14472cce6b5b18448c9ac6497a385aa72c0e8c3812cf82c5b4839f7584531a426bcd297aeb985ab60bb5a2935e34e97fcde2c17988ea2f989ad534708263424ad8b7241d41ac4d94429074914c358ca490d0ce3d69cb4e63eead5541ad3f (by decide +kernel)

private theorem part507 : Excludes 0x8000014000000000000000000000000000 0xd61cac690a00221100002a8000000000000 :=
  splitAt 1 116 0xd61cac690a00221100002a8000000000000 part509 part508 (by decide +kernel)

private theorem part505 : Excludes 0x8000014000000000000000000000000000 0xd61c2c690a00221100002a8000000000000 :=
  splitAt 1 123 0xd61c2c690a00221100002a8000000000000 part507 part506 (by decide +kernel)

private theorem part503 : Excludes 0x8000014000000000000000000000000000 0xc61c2c690a00221100002a8000000000000 :=
  splitAt 1 136 0xc61c2c690a00221100002a8000000000000 part505 part504 (by decide +kernel)

private theorem part501 : Excludes 0x8000014000000000000000000000000000 0xc41c2c690a00221100002a8000000000000 :=
  splitAt 1 133 0xc41c2c690a00221100002a8000000000000 part503 part502 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part511 : Excludes 0x8008004000000000000000000000000000 0xd72c0c78062042030010008000000000000 :=
  finishCode 109 0x448f43a8da148df48209df3da4bfe83d179904d44395bda62e6bdc46fad53167b53c97a4ef7b4cce2a02ff2ff8bcd5fb41b4e626d72e6c1e623fb5260c37ac4e55409af0295cc67312e6aca636592f45268e15aa8d9605ab05585a731394be8d0348c429872b3eec3131f0b54dac671b18bc7dd6a9b58dcc5aac7311888c4e309a805cd580e62c379ace3e15a9c6ff18bbdb6358b544d962f3188c18d496b1a42e3808c5d282c4f62ca42e1f0c2ff398c10e6338d60be54c698cf6b48e9bfcc0eb62903fb8e5690b4a0b56e6b2cd336ad8fedaa63fb8e56d63e8d65860a6ff303b0a627797856ae5e19c8aa391519cdded341b5cca3fb6b1a505a6661f315b48e63966271b59eb915ac63eb395b50a413bcb9b2c9ded292b614c6ff6a7a5067d1886c0e3672958150781e81f0bdb6483c61458272341ea7f61bcb59c12ad357b49cc64feb165e87b2c901608923d3fa90749ba0f57c4720f31819ed28c9608bdadacf02ee3032cbdeca17d6a7a7f4f7293781767317b5cd316a5825507a8a2d870d401cc591e997cd8b324d50c4f17c2ffad5e0c6b16526a8c79a62be320b57a0de7311f0b1043970f86480cc415b19c60bc6e7723a80c9de2e7614ce6157ea8fd88a6f5277a80a823be3e8b12dab6b153988f85e8491c9376259cc4d2f3dadab6f6905dacae581b56cb4ec37 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part514 : Excludes 0x28000004000040000000000000000000000 0xd75c8fb0238802a50400008285080000800 :=
  finishCode 103 0x1063e0f03d1023e8d803b5705015c5b0e62d37962a701410a0fdacb2c55ed290783593cda81f09c7658ac1ce6a5cc1f58aa0fc9e73165a6ad4b60fb56ce62b6200b2290b0250589f3164e3b00856ae6f50e39c761e7a464de6c4f98b2d35928a9f31e7bda583e71d046cc1f4fcac55682de3c8b2b98b2b45487935ce626f528b9485408c0c13d487ac55cca83f1f0b07e58aa0fd74398a7e6521a7e65ab9f85ec306f28bc0e1671e46f03c71495746c16c283a7e6521a0fd0232c06302e5f6ada8853e6d679cca7d37b4a77d40ebc2d8d5b26bc92f2e4cc59907ec02d8a2f58ac6f383ac3e158aad0586f356d216f694f99fbd6c6a7c58b372b56d07ed5b92726f5408bc8d62406288a04501e5250f1ab118187a6f69286949528ec2f8e1f18760cbd853b6a3f6a0fc4a16831c0545eb575b102324f507ec1fa0dae6f3f1a0456c501062813a0e2b2b839a4f60eb204c8c7181595c6067b5c1cd8b2b2b408a03e6703c714854028bb546153ac4ce62d29358cde3c8da03959c387cd5d49e9cc546a1db4a0c08d6948f4d9c398b5961e382e4d632d87e0f1e4efa8bce1eda1c74b9325051c72c556570f84e62b41072c731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part516 : Excludes 0x9000004000040000000000000000000000 0xe46ebe3823881221a400009201280000800 :=
  finishCode 25 0x1e8851b480080641328bcb150f18c4deaf0d5d83e6052ddb98e803960738c463f5cb3f302a85dcc2ddc6290ef839dac5e16c314a89669986ed42e0479caae536b3a51d1c30fa4064ed925547ef719a6693599c25bc90760f9494c521e31fdc629 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part518 : Excludes 0x8004004000040000000000000000000000 0xe7ce8f3243c00a218408488201080800800 :=
  finishCode 67 0x440f8398f22d82f9182b53e41f9fc4c0a3fb379b10e302af0b03da6407a084c3a62962dcd5b315a9861f80ce4f341f9a078242e7b492ad6ae811380c90b5aba41e499b4cdac5e0c5318ad745916030ecded29071fd987e00699cf675969c049e6f678fa69f9a3023e1800e1f1495347b4c6f56aca484e1e5bb9aba3fb7b4c00de24763879434a2ece308a0d94423fb524c50748ccf6d8bb69f9510875c7f6d23c8de359671c8fece3a1e3591781fdb136581acbdac37ad06d41fc1b6735bdb5cbf06f7b4b56e597c1ccde6b1b5c0c841fb93e6a8a08f69807e15b408b16dcdf34c56828fd7b2b4c6256a4e51beb576a7ae0b6069e1e89bd54725e741fa20e6f983a4631bbb9ac7a2c5b3f89b0e16dc80f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part519 : Excludes 0x8000004000040000000000000000000000 0xe54cce30038002210400008201080000800 :=
  finishCode 131 0x1ac6620c291be0fa2f00158247187837bd95ab69e518ba0c501e61d314c00d80c4cc3f13cd83f1bd6272ad8d8145e418bc8d419a9ef692729435c93290c9ae6f558ab16583f001bd660fa044a42b318e62d5b5619c209ca4949ba884fc700c56a64953989434827356d62a517283ab8842f0e61e07316a5c413521b595ab70395ed2413600827316d4922a788dad4f7b49bcce1f290ce630395ed2ac210f01c094292454f1a553ca4bd5aba43e4a09b2dacb290c1ca3e15a0c4d75aba90d492a2f882694137c95f204d6ae941a20851f47c160831e430e98a45f3204ce62311398c4f36d1e4179c0e52099f89a137e7ae9c3d0264d596aea2f409c9071f0b98c5b8952d675ab8394e62a359492f218ad46b29241ca4132d9c4d751ab9be046d16c398904dd024fac5e4f29b2d4424afa306f6d36c91ad62f118deea9e557dbdd657ea7bd602d292909cc5d069ac923272a04d6a6525235cb5361ab16dabab63c86d9824e3bb58a873ca1a5176c09e72cad07eb57967ac4f60f97862909b64e62be36062b418cb574f7871ce628f193ce6f526d98767d214729cf5d6ae97cc1da413401bc857f9ebae65501877cb97071d89ab63c8a038bfe1cf732c3b315ea0c5f01e8cb1557d9bd5022afb8db300440fa24de7b4c60d86aa174a383841d2313851b46c05feae145e0e71bd4e62f75a30e9dd37aa386091bdb4dea9db2869bd628b949540520e6293785aa8df9206f657b0a51d67b0b5528e7f1882671d074be86f388264e58e622f9 (by decide +kernel)

private theorem part517 : Excludes 0x8000004000040000000000000000000000 0xe54c8e30038002210400008201080000800 :=
  splitAt 1 122 0xe54c8e30038002210400008201080000800 part519 part518 (by decide +kernel)

private theorem part515 : Excludes 0x8000004000040000000000000000000000 0xe44c8e30038002210400008201080000800 :=
  splitAt 1 132 0xe44c8e30038002210400008201080000800 part517 part516 (by decide +kernel)

private theorem part513 : Excludes 0x8000004000040000000000000000000000 0xc44c8e30038002210400008201080000800 :=
  splitAt 1 137 0xc44c8e30038002210400008201080000800 part515 part514 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part522 : Excludes 0x28000004000000080000000000000000000 0xd75d8cb1a20053854400009000000b14000 :=
  finishCode 59 0x1063a0c4338ba13ce283b78d42e05255b0e03391506283f500d00d2b04671c973585306b87c27cd9a9ef6b5a09cde6b2b8e56c640e6e83f8e021e36279cc68c084fc28706b81dae538378674e36801641783e0e623e196aed4f58cd06f98b23e141f9b5e398be8c2408de3d073741fc731076a42e2e6b56d28ac2d8b92b2f379b53ce628019ab66f32e49cdc7c3145cdeaf240851741fcb57398bdc62e48f8641fc090719442a4339894841da5218b9a0e138dc0ed741bc681d46101cab2b8b9a71b39b8f863989cde3868f8437f0394e631c36 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part524 : Excludes 0x9000004000000080000000000000000000 0xe42fbe30820c52012410009000004904800 :=
  finishCode 31 0x8320864220800c52b20c4630301f4b6a50762cb56d282c016d6582890d8b2d5b4858f243c746158b3242d67e607398b68e6428f4078d26b039da837acc2b0d0b92562eb576a98b6c79301f526b077c1ced0102d1049bc3a94a3b526597b4e568b352567e9479652d4d5aa839c827039e200f1837d21714354232d05a9ea2b06fc0e3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part526 : Excludes 0x8004004000000080000000000000000000 0xe78d8d7283405a018408009101000904002 :=
  finishCode 83 0x3e0f44a1cc6a7a20782d88017b6cd5b292a086207d05f2f699aa661d72fcd539a8881ccb2c0c73a629699a0fc5f283f8e02b176a9931d682c59907f103e82f9524c3e161ba0fda6662b6a4cd332798b6e5aa9c05a92d338209e71495a66b4131494963f0b98d82d91020fd9c3f0cc5917f941cc0f0c15457358d002d396a2207d05f261fa0e202f27998756530deda7281112d8a14d02ddcd63400ac562ddb54d0034103058dfe6296b2c0af60fb78e39925e61f38db13e4f998a608881a87916af356cbc2b3128b98745f2fa2f06e391e26294fccb575069fbd3cb0f8507ea81e0b62004e373914c0e6f34efcd31475ac9ded26f38a0ef6941f981c7f713f4a22b831880169ccb5741fac5669c8b667b49496730a00568e93d0f1b50e64400b7839e50d17cad8821942e83f4403c71859ac68118c2cd63292cc59907e801 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part527 : Excludes 0x8000004000000080000000000000000000 0xe50dcc30820052010400009000000904000 :=
  finishCode 123 0xea33106148e08881907d1787b6c73130e98a54c17cb606f58b3ae3d4fcb4e4e024f3407b0de361c82137abc8b62086418945cf9b34e5ed22d9290a70811410b56e2e6c60616cac55ed2d639ed24e52098bfde4481cf6969ca4dc1daf699a720df9bc801e06c1e45701c6b1585b2b419866f751e892163879735aa62d96b2c0e37d105b3dd5ed2b4120992f65a0837e16c838e398c1110418c82c1637f8c44c3a6290efc0e7076bc8a359492d675959c6c1ca4132ddc399483a3c40927314119c6de4851a4205c937209a08e4a3c1df074ac6e61aa085046a4996824bd263838df4852008220c7906230c4d786a07c31cc4c52a639562799cc506282194c4839b9e3eebd9ded64f37b5cd4d6814c6f1845e0e367296a05e702ecbaa1a995fab29483c7319aa6c202a66a69cc41767318e630bcda9a7319a62c5b69982bda92ba308511499cd63731a455ace7296a9c72b8a4b043210628d638d98a4e371cc4c271cc5a731ca4e62c82f8b218a5d030faa0de1b9c7c29459202a398c3cb31a0fb1853deb58dcd6a393f5acf4fd7237dace6e760186f1b9c7c306b9c7ae5561b9b9dcab3d74dce61d5f1344a3c9fd512984c7031cc5246a25356c7bd72ac61542e7318305f31cc45fe7319ac62f3 (by decide +kernel)

private theorem part525 : Excludes 0x8000004000000080000000000000000000 0xe50d8c30820052010400009000000904000 :=
  splitAt 1 122 0xe50d8c30820052010400009000000904000 part527 part526 (by decide +kernel)

private theorem part523 : Excludes 0x8000004000000080000000000000000000 0xe40d8c30820052010400009000000904000 :=
  splitAt 1 132 0xe40d8c30820052010400009000000904000 part525 part524 (by decide +kernel)

private theorem part521 : Excludes 0x8000004000000080000000000000000000 0xc40d8c30820052010400009000000904000 :=
  splitAt 1 137 0xc40d8c30820052010400009000000904000 part523 part522 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part530 : Excludes 0x28000004000000000100000000000000000 0xd75c8cb06200628f2008808000004000202 :=
  finishCode 83 0x3e8c4340de308ba1c6ce5284039605c9cc60faf656b2a8bd492d82f04f383ecb3f7b296943627313d5c83d7b6b59412ad4d517c1d6698a0f411a08da0f20ed1f086b56c830e1ef23c0e61805ee6537a9fbca4a0ed0f1cd4b927ac4b62cb07d07e8239b05abcd5129286c43c703b5a961ad7a2046c14872d5d20e0ed398b166731ad5c1da1b394860e15d180561a631ead65a5bf6a5b06c9e6a436116033045cc2919173979c78650793e7312d27a3b3497a38b6313e62ca5058b32d5e497c18ce2e8c02d8a43524b16661b86fd282833907ac37838e6f5279ad8c8352e380a5041db04fda627ff7b39bcda9727e5aca1e362cc08b41901e7310769c06419b4de34ab5454862e72ff83960483030f34dded2f7516c9cc43c60ed74180751840729c3659f9cc43b62d99492d31878e7310c5a8bd48673193e66b1072c61e2e48eacbe680338683862f9bc8d6145ca427a2d5d8672cfdedb316565e6b1625bdb62e6b0ccf9a9034a07c330dd6824f35abb90e83aa0fc7c24f3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part532 : Excludes 0x8020004000000000100000000000000000 0xe54c8db84238622b0040808008004000a02 :=
  finishCode 51 0x3a8f4358b6148de46c0f4398945c39f279cffe4db7aecb050e79ffcd63398cfd6f6d595873d9c570e63071da9313ce0ff068d656f21cc55029092465ab80be7b69ac55f63e1a00831b0570a2e52537ac9333e69cc582b00053ba5e13e6b3850d4905fe3b385866d92ffb05e4eea76d222f697b6c7eb62ec61c95ee63691506705b25cd36bcd5317997567b6935d9c6a4c2f362ecf6d179cf698daee63493b914e624e5791b0630a4ab60b6e407873cd870b6562b069e7b4979c5fe50d499ca495a096ec38e7318a422f3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part534 : Excludes 0x18000004000000000100000000000000000 0xe43e8e304e00630b8002808000004000203 :=
  finishCode 107 0x3d0d6420f8148dc8821e46a9cf69379904c1ca0ed45100411a50d6596aee6b26bb59669cbda64a14869bcb4169c9ff507af67a30ed39387acace1f34e497b131c1c6e45a0fe7c3724a8adaa66f5076bc8da065e5abbdb4fc6d370f1904dc87bacb155abb544e1e2d9487b13662da50823595cb4169aa0f4e1f24cda4852086d158201904d5c5abc0a1724c935073cc4d2e5ad05c84801ca8034e65aaa70a0172e8c386c412ab61d05cb263c1ce08e829526b1878172b293f6cc132dabdae6b3ad5d26ac13724d07f04c972da9a4c7263c0e704dc1af1e3838dcc0c7c0951d1b4c4b96b570ef839d6c5d013f0f2c0bab2b0d7931e49a825d85b0f2c12a82396ae5cb49a838df08201c6c5b873a7ed2098b66263b99660da775eca08d62db0d45b270f209bc8d2378d4b9836f691fdb58ce1e1e3611701fd978e5f96aae6558182f3db45868e101dc495379b10d6ab1fadac601245b16aeb15907ef6b2e5863c36320fe379b97c362c4d8de6e4f989ae650c5bda56c61124520bce0979ac6b416b38b3cdeb38f5c9ed3316db58d682d4f501cb176b1825c59ede203e699bda542ed63732cc5b699ad5da9e5cd410d86b3d98b6f69962ec0250d49a0fed636b2acac5b2b576b2c80f16c855e7b5ad4daca6f3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part536 : Excludes 0x8400004000000000100000000000000000 0xf42ebd384280ea0b080080a000004000242 :=
  finishCode 29 0x42906400d81cc66b3a7be306c1f0f19494a2ec2078ca1a3eb8e56d3998468141b16edcc61d72919ca4e565bb8e029413f59bd49cb078da726e7731f05001bed61cc5b4541232d398e6e933394ca0d735b4e63659cae306a439aa670f04b976e69c9cad84517c70d1f59ca4a46f579ed25bb398a926394948c7d64bd291c0e3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part537 : Excludes 0x8000004000000000100000000000000000 0xf44e8c304200620b0000808000004000202 :=
  finishCode 155 0x429063e0d62f8c8184e00315bc83fb9a669072928c4c60aea308c0148deaf3da5656d335ab9bd6483bda6373a464d86d3582f66f3483904e6a9a5049ca2f9610e57148de449ac9f925c9c3c8263135a0c823380c00c20c456c5e0a4672b2e6d1836a8ad558b673147ac39b8a467315e148398c4f34f298753cb0f84ffe4f391eaea3088238e5652338183b1cc49caa0d5211c7187507f27e6589a3fc5f27317a2101899bce17c9c3ded72034d927e317c9814e1f14945f2da408f2348f40fedbc209940e28ba81e398a90e7319bcca0e70f7416c7a0a1aa438e4683d283ca0d41ec6d98e625235b1bc1e7c91949e9cc4e1e72b5f165720f56ae92f960a523471ca2f398a0f5e852145f30aca4a5e341ebc8823283c5112ff9b0e3878465a9b07d279ac15e48014c292a90e621bda41765072e6c0b51e1c92b2f1875d48702d4e1ec23585e38dfe71b398948dacb1c34a4a729290cf2368ea3a04133801cad339826c3541ea8354871cc50471bfca46ae0bcd883989f76387a4f5acad537aece63358825c7c23e1989aa2f6a9c20e6308d63a80df8e62523681a44511fb06bcb2e6b13989c34e36b625872983fc1af5aab98e5899ac546b358ce62d4b37fca216b1cd538e62d49394837dacf41fd442f6d69cc60ded273161198394c7ed291ad56839b58ce36f699cc70736a1c1e546ad39072cb615e67b4b58c13e83d3989c3ce56ea1cc65899c6d07ac358fba7315f178309877e398ad1d4065233159f0523521403c120ed4b967b0798fd71873f5cf6d83cc61d67a919a30ea2b9a6ed393f5bdb60d6cc2f052361acb1b15eb16ce62a8298b60254b9b460cfd64953f5c25334a9b9e014bd751be7eb1f091b68c29b9cfd69ef8c3a731 (by decide +kernel)

private theorem part535 : Excludes 0x8000004000000000100000000000000000 0xf40e8c304200620b0000808000004000202 :=
  splitAt 1 130 0xf40e8c304200620b0000808000004000202 part537 part536 (by decide +kernel)

private theorem part533 : Excludes 0x8000004000000000100000000000000000 0xe40e8c304200620b0000808000004000202 :=
  splitAt 1 136 0xe40e8c304200620b0000808000004000202 part535 part534 (by decide +kernel)

private theorem part531 : Excludes 0x8000004000000000100000000000000000 0xe40c8c304200620b0000808000004000202 :=
  splitAt 1 125 0xe40c8c304200620b0000808000004000202 part533 part532 (by decide +kernel)

private theorem part529 : Excludes 0x8000004000000000100000000000000000 0xc40c8c304200620b0000808000004000202 :=
  splitAt 1 137 0xc40c8c304200620b0000808000004000202 part531 part530 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part540 : Excludes 0x18000004000000000000200000000000000 0xe43c8f300b10430b015000d000000000010 :=
  finishCode 91 0x841e8661ac7c0a46903c8de418d397d098f038c1da9039cc29372638f4626b838d07b03941da4d7965680d69cbc8fa131e071a8e41da003924ea2549bb52e5abb4cd01ed5b410be8e4310f21356387904d4859ec2d941eacae16ca08d60a94798b641362dc4d50f1acae59ea49d26ef03e0a1181d22d9071b99662dbd9526e7ed387904dac73d953fa71b2099cae14791a47d1c869cc3eb263838c8264c781da1e3611683073cbfe4c796829474a3cd632ff838df0411b90e57d82ada92831730c4a93e7b59d67a0ab7916af24dd28e4c7074ad8b419062b479f0630f06a9c811410a4883f3e1c8b398c0f67016a7ad056ae5e787a31bcda7eb176aeaf8902c54363172d0020991e8ac5e1f5b0bd0022cf400c2db7d184379ce4726aac0c3623fb395b91e35897341361b126a9c3d8c699c3cf16c82ad62b356dcc721f06901c6bc0fec7921e35aacc136adb1345b6e4f9ed6a039966998f24b972d5cb6a07f1fdc1e32098f266ad839c3bed02cae1e48e756ae947205cb3f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part542 : Excludes 0xa000004000000000000200000000000000 0xf49ddd3002384a094540009100000000010 :=
  finishCode 57 0x1083a8cc4085238219c074b20b01cc616a935e7b69cc416a93751cc9151cead4d28eb3d89b673126dc0e3166c0e1811e47219c26d838deeb0484e62a39491a4ddcd72d4ce62923839e4db0749cc56570f3ce6262b81c2c82f0d41816314a806c7872a0930c6981c7c2731488cd67058a51d644d0f0303aa0b60f8630f136d042901804ee3d4089b0e303353567a9158c2cf57157c1e630ec498d863e18c3987cd6327f49823e1526bc8de2f09a310e8c3a444c0e731508a51d40491bd86508b125eeb461cd8e9ef9473187960a6072e6b9562e6984ce62e43580e383cc7b9041824568261f314981661bc4c1596987cc0a0e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part544 : Excludes 0x8800004000000000000200000000000000 0xd62ccd70021662095140009010000000010 :=
  finishCode 73 0xe6360ae3a87317d1e478224071b56e209948c173353c7d71cae291ad05edb277414af5d510a90ca4692350a6290e38db52d492e639a965ff17996ce4a2a77ce36d4b821a86d0f832d55eea6ff5108bcd5fb2d5416aa216914c735cf5d05991b5626b3f5b0de741d5cc65cda0ea46d699c6c36b382ce821f4792246adcf6d416a8341ca41357ec1db4168395a82e6c5234f2acad05a5238dfe4d76b185b3d5d486b410cc948d902e05e64d79edad252eab966735bdd4f9ae6136bc5cd25e9c3e58b8ee43b60e379208071c4883d9ab64130edc09d897a1db595c82d821e46d0b8416a98a21946a0bb986a7298176c22d8b138152b3f394a8d6524a8861f0c92705da0b54c25e948e6ad9cdc156a4905ac0ab (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part546 : Excludes 0x8002004000000000000200000000000000 0xd7dc8d3082d463092144009000000100010 :=
  finishCode 63 0x1123e8d43e0c82c062b398c3e130ea987319486d5b37fbdd6506b56d4c5f1d4309ac5639bad05cab1734e628238e1e737398a794e03148e047a1b0530a46731279c8232f1ad5e722c737595acf5046be2900ab501c8b30d4142b4149eacf6387cb41838cd5b48eb56e6a7a0f541a4f37a10631cc4a46821907ec23300ad8a46ce029d89f390d46a831521ad5e418acad28595cb415d0fc731cc1f5a38285486a49279c5a734ab4e5ab6b158c0c7ff58aa0c5a72fa3788a2d871b6c0e6320c438f1c052823cf406cb57398cb577a1485ab9cc565730a528291990232d5d6af1cc49e6831 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part548 : Excludes 0x8100004000000000000200000000000000 0xf68cad3032114a190340009000400000010 :=
  finishCode 67 0x1083e8de308a63a870d38dc10523209c4e54919cc528e4e58c57251dac7a1cc713941be40b291c08ce2880bb0f1a4562729f4e6a98fecb13000522a2338c2b56d60a6291fdb38a0d9eba1d717cabee4f2939567a40b96c562085e190520e1f187504320c4c528ff8e624e506fa7e526e90184e23b940093943c73995a723c12729cc6731a0c4e1e4138e627cd69c9875ac751e84fcc2f9309904ca46d43e0b5390226298c0cd67521b99435a0b71fda0fe5988fed902e698ae003a924772811510c6132e6c413611d45e0a462f99cc60a70ce9cc49cb24de04d829ce6293789caba3d0bc102c8266059ab62f991ce4e55e07f6de18a401f1a8d83eb052da8f3e0f22d36a7c39f598a9260f1904e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part549 : Excludes 0x8000004000000000000200000000000000 0xd69cad30021042090140009000000000010 :=
  finishCode 109 0x378d4360f4145ca42f81cc41cb0c5d827148d6563b10beac053fa801860afa2b0f41435f0076c82d0f18c4c3c7104d07a1e3860b120f6e2098c1507b039c3c650d9e88220418bac00ed471c1a5288a8fcdff2ca528e7296201c21bf8e6e1bf907ea6038e0ff306479ea4d3989ca4e572cf59c581a4288ad81e3699c3e141fa04683cb56ce36d531f0cd536adc605d47aec1d30f1a98b6175e303176d07e277a302b311aac614e36d53135cb535b1605921051fa4646ff3984dca945400b53e49ec20d00f86508c614e56c4f9002d67582ce5371c8e1cb6b0796ad8f24e0346152330739eead5b6a7a006247c1e8291c2ff189b60e62c0d42c0e6ad82b50022f3182c206f39ab6c5941fa00564303cc5f2f3a4647932c15a7f2c5c5fe30541fa0454c670c3e5b5962aa497a9cb5731497362be98ada671810c2ad5d4872d5c60ad8338b6141d78623a8360588fee495a0f589282d83632464e62fa24f6615b56dc8a3fb209ac8b1b815ac1596a6d83d0fa2488312e683841da1b3949318785521795e1601739cc58530f85a7f2e85cd835f071510a90c1332d8b459ab6801173a0fcb9b2045ab7290d6ae0ed (by decide +kernel)

private theorem part547 : Excludes 0x8000004000000000000200000000000000 0xd68cad30021042090140009000000000010 :=
  splitAt 1 128 0xd68cad30021042090140009000000000010 part549 part548 (by decide +kernel)

private theorem part545 : Excludes 0x8000004000000000000200000000000000 0xd68c8d30021042090140009000000000010 :=
  splitAt 1 121 0xd68c8d30021042090140009000000000010 part547 part546 (by decide +kernel)

private theorem part543 : Excludes 0x8000004000000000000200000000000000 0xd60c8d30021042090140009000000000010 :=
  splitAt 1 131 0xd60c8d30021042090140009000000000010 part545 part544 (by decide +kernel)

private theorem part541 : Excludes 0x8000004000000000000200000000000000 0xd40c8d30021042090140009000000000010 :=
  splitAt 1 133 0xd40c8d30021042090140009000000000010 part543 part542 (by decide +kernel)

private theorem part539 : Excludes 0x8000004000000000000200000000000000 0xc40c8d30021042090140009000000000010 :=
  splitAt 1 136 0xc40c8d30021042090140009000000000010 part541 part540 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part551 : Excludes 0xa000004000000000000000400000000000 0xe49ddc3022384a0d4100a88002200000000 :=
  finishCode 73 0x1d4841ac810a46e8390d8038e20630e62a03949a8f1407a936478a936478873dedb2cad26e6f52dd9cc6074877e070ce4408e63300e36c1206a399266731150cf6926d8b5528f1ef4b764d7478931e0748b367b4936c1c2f659ed25bb49b9cc41d3043989a039dccb06bc39e9011e5a4dcfd72c04c56d606be5abad5526e61f263c605071cd6350c82c8629500c3ee839ae62fc60567a7eb60c8f852451cc3ab6a8acf6358a454dcea39949a7eb373c61dd0526b8e6729c1bd83ec4f1f091be250b07d89eb22e86136f1cdf41e52460a70dd86fd6ab00351ea589034ac160f34604f72e6167e72a96dd8beb054712c356c191526867474e800a4e491c1d4dce03b9202e53833a03b260ac88e2f060772dc5ab4109fad26f07986aeb3d46f8f86398acc6627a934e623e1944aa39 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part553 : Excludes 0x9000004000000000000000400000000000 0xe62ebe302208720d2102288002080000000 :=
  finishCode 21 0x1b4611448207d6e6356c82710078e30b359d89f1813f58c15ecb179cc3f293606fa5066b3acc4bfe73128b838c8165038a2e0df209c19043980e786227e28fcc56b29a0e6b014a3ad556aec2b9ecf06d0d2a936071838e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part555 : Excludes 0x8020004000000000000000400000000000 0xc74c8db06318422d8140288002000020000 :=
  finishCode 85 0x441063c8de400ce1b663f582cc39e50d17f94856c5d0a1a51754198291c90f4a2868e8c392bdcc67eb5959bd67b6924d866f6da30ee63291b58f4330a8148d74625cc5d58ba43d28ab1793fad5b398cc3362584de4fe852c2faafb57e9cc5ab6c5995faf7536cac5d6aecc2e8a8305630341ccdeaf6d4fea4ccf9b1fc67b49cc4f9a5cd3e6cf654feabedd4811845d0a462f99c8a4e5151924e1429cc45f22f98e626f54a2a0fe408b56cdea2cd291a0fe398c4892148c5f2b53810ab316ad8af4bce1ad812ed5b400cc4b6adb0a5492731173b60ba20468c3b0555fa90f398ad5c9e6a020fded339953e26f51f09bd66114932d5c15a5233f15c58aad0567b312ded2d39962b3582f38a46ae0bcd82b02b5eda903499b9867abb9ad21ecc3d0ba148de447ea515897390dab69375a0cc2f69cbc8a259cd6e63481bdb4fde90149b9fbe5a0b4e5e0631266a602ed89720fd62f2c5662eb56c98f28fd8c6c039ec2f8f9ea4d410a4de5a0acae (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part557 : Excludes 0x800000c000000000000000400000000000 0xc74e9c32ae084a0d01002f8002000000000 :=
  finishCode 89 0x1123a8f43c852330fc5e3283904e043f09af18a4deab5737acb2b279cbc150f8356d846a163706cc5b66295318bb41acdae83f5a2ac6560720fe7b498a56071bcc13ef8440b20fee30398ada06aec5898c0b98c17662958d962e37ab06d84730cb29379b91d07e3fb3f8cb53727941e49e825c366b2299102c5e837987cbc6ba31809789aa1b360ac3fb379c5cb617ac5d07e780feded30a1500207f9ed2b8398305a0dec4b62fa044f03f0c34f58a81a5cd72d5c30e6f3279cc59379c19003c8e6398e5a9981d0422f9188861672c98acde63135d1cc279af07ff582cb1b398ad4e61782ce48c854d25e0696adc1812e6984e314b987eb8166f6d6ad9ac45e673149ec6b105dc09063a8f42900e5398ad5e406b56d07a6f59ab6b02e8f22d850762ccc1b5ab8b9c123313e62cb06d6ae4f36adcb6356e0e730bc35683f37aca49398c1b38e625ff85ce507 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part559 : Excludes 0x8000004004000000000000400000000000 0xc72eec38b208660d110229800a008008000 :=
  finishCode 37 0x184822247523073574e6270d201948e007314c188b688606cc5e67c17cdcd70d5dab6e4572cce6b1ab809e0a1c1acd62e616ada58b299aca6b17b2b56c35ef578e62f5d3f5c1e68c0b98e306d651798c4e8c2cb29303a48ce6270d8301db24dd146ad98870d2d9c7310b39cc6625bd96290c7311f59c34a46ea4011024062099484a1b04359e493bda43c69372e5c6f56a7c413263bda41be8ef8c56517 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part560 : Excludes 0x8000004000000000000000400000000000 0xc70e8c382248420d0100288002000000000 :=
  finishCode 151 0x681845322438d9ca5e8205c5236c1e46715fb0f863025110f19495cd74605a6ab293f88c15493305495681130f823e182bc8b04181a9076c83d492a51c1cb124decb18141e9cc528f3da41721db595c1ad751e882134205a0f6395c00311905a525315c2f9286c72b291c089a39872b671740f18be51fb3d94a229fda302b27967a4ab91e27e16ad8a14a4a52587d65258c5672b6a1d0730a4abc0bcdacb1b2cbfe2cf8c1ce61365b4e630e5ff395a687c1cad1c730bdce6adc1f5a7292b7afce4f01bc5938c09fac2b71b2e0f2d5b05d8bce830e56b3d8622e4798bed3983c97ce20792006716c292bd050d0f1cf69076b98e5a0c30549b940e28bc10c8358c618a5ed724041be4e58399bd51fb1f848260df3879c3e62e904d60b208ce1e937398c3c12729c3cdced83e0ce4484f3730c2661f5a0d18738ab56ded2d655a0cd5b7b49f86418c62941ec2d9279be0b231668c3bda507a2a76b2984cfc7b4cc1b419b164c52c1f387a90afb8deac1f41e9bd63f12673da56aed65465c8237c1e8820fc076ae870f7b3c83137a923d046f699a72d6504bd073493c61ded2d39526c70f69cb9ae5abac55ab6d39387ac565a3a0f5266413387c48f433104148e00640626d339882d39838987cc52701962a8238c3e8fd06fa3f606fc41064104138e62317315c00c5983c6525620c4b74079395ab6c376d01c70f2c8267eb96aa0df730fc62bd94227c35269354bfe4c785627013e1acae0479174880b76c1b87f6629288b56e1f5ac660b798a5ab61e3735c80f6ad96ecc0f18ae0c811e46adc5bb076878d6c6adc5bb398a0fc79eba20765abb12d266b559acb181380c3cf070b4de4a29cc4b761d7 (by decide +kernel)

private theorem part558 : Excludes 0x8000004000000000000000400000000000 0xc70e8c382208420d0100288002000000000 :=
  splitAt 1 98 0xc70e8c382208420d0100288002000000000 part560 part559 (by decide +kernel)

private theorem part556 : Excludes 0x8000004000000000000000400000000000 0xc70e8c302208420d0100288002000000000 :=
  splitAt 1 111 0xc70e8c302208420d0100288002000000000 part558 part557 (by decide +kernel)

private theorem part554 : Excludes 0x8000004000000000000000400000000000 0xc70c8c302208420d0100288002000000000 :=
  splitAt 1 125 0xc70c8c302208420d0100288002000000000 part556 part555 (by decide +kernel)

private theorem part552 : Excludes 0x8000004000000000000000400000000000 0xc60c8c302208420d0100288002000000000 :=
  splitAt 1 132 0xc60c8c302208420d0100288002000000000 part554 part553 (by decide +kernel)

private theorem part550 : Excludes 0x8000004000000000000000000000000000 0xc40c8c30020042090100208000000000000 :=
  splitAt 5542 133 0xc40c8c302208420d0100288002000000000 part552 part551 (by decide +kernel)

private theorem part538 : Excludes 0x8000004000000000000000000000000000 0xc40c8c30020042090100008000000000000 :=
  splitAt 1 57 0xc40c8c30020042090100008000000000000 part550 part539 (by decide +kernel)

private theorem part528 : Excludes 0x8000004000000000000000000000000000 0xc40c8c30020042090000008000000000000 :=
  splitAt 1 68 0xc40c8c30020042090000008000000000000 part538 part529 (by decide +kernel)

private theorem part520 : Excludes 0x8000004000000000000000000000000000 0xc40c8c30020042010000008000000000000 :=
  splitAt 1 79 0xc40c8c30020042010000008000000000000 part528 part521 (by decide +kernel)

private theorem part512 : Excludes 0x8000004000000000000000000000000000 0xc40c8c30020002010000008000000000000 :=
  splitAt 1 90 0xc40c8c30020002010000008000000000000 part520 part513 (by decide +kernel)

private theorem part510 : Excludes 0x8000004000000000000000000000000000 0xc40c0c30020002010000008000000000000 :=
  splitAt 1 123 0xc40c0c30020002010000008000000000000 part512 part511 (by decide +kernel)

private theorem part500 : Excludes 0x8000004000000000000000000000000000 0xc40c0c20020002010000008000000000000 :=
  splitAt 1 112 0xc40c0c20020002010000008000000000000 part510 part501 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part564 : Excludes 0xa080010000000000000000000000000000 0xf5f77c650ca0a8141000200000000000000 :=
  finishCode 111 0x328e63a87316917c6d1744103a6b2585de3cb732cb437b486cc5dec43408e0bbda77202e30ea3f46ecb175a8bda561ea279016a279016b573c16673da4b9a9034b1ed31b4c35ef7195e2c5d4f7accd2c5405b30f2d2729453323070f2d3d6a2b57cca4f7b4c60c797249c5b2be16ae2fda0fc5def6d907ec43a02879a5e5d159ea8ac9b62ef6d10166c7942ab3d2fdb9ad47f2cccf0405a40e513a08492f46160e2a27350b10a43003e5691740ddcb2b62ea02c5de2a95a0c80b177936e721acb5ed20991778bbe405b48f697bbd18351eabc49825fb177a0edeef3dc5eaee6557f97eda92e6b9ed24db405a0ed74601bc690a816ca887824891541149f1a85cca81b50ac81f4f4cd2f3deb9947cb1879c9f18540fb06dcca83b7add18736993060f6d595138f95ed2ac23082587ca8351dfcd498b76e6358763da66ac9734ffe81f598cd5941fa8f66a18f954804dc29d1f280be72f9ac51d6a3d053bda5484207caa3d9cd6c5d41faccd692c839666ac826d452f69727c606592bda4136d3f412cf69491783e1036e61b1e0f67ff9c8681f72fc9e9260a7ac8f71f7ded29a202d85b2c14d86c5d0cfa07e60dc615c9f0f95585e1887b4c3e5724c23524ba93e30307b5abbda5076c83a0e59527c8217b4b93cba2b499c9ed61963b18150ac821 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part566 : Excludes 0xa000210000000000000000000000000000 0xe5ff74259a80f0141084200000000000000 :=
  finishCode 65 0x881cc5e1d0398bb8c40f96177a28622b0a27358cf5b090a8f4b6e83b2dbcc139886c5f72ba0c60f720c5cdaa2962148560ba31b9c9b63e5736ca3983da504d8f311d4720bf373cb078b9aa15412b10e83202ef44127a80f8d8e9d951fa38cba2d498b9a80f405cb5347aa487fb9016a62cf651fa934bf6b338976e6b741a85c107f39b49b6c17373ab84db1dbc3cf34cca29513a7bdc77317dcda9ef51ec903405a8a651ea02d06a2ef5f1d06105d2de2388059cdb075405a8e54561af901ea250d7c5cd41d919666174405a0d567b28ad6a6a2b8b9aa4d9bc1f29987a28ae51fa02e51cc61e5a9c61e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part567 : Excludes 0xa000010000000000000000000000000000 0xe4bf76240880a0140000200000000000000 :=
  finishCode 131 0xd42e0aa20072d610e22bc2b0922094d8f03a4982a11398bda507707b7217c26bb28e658e621b369fd1815aa8e05eb30718d62e4972f83a6692b5907b074cc5f40d935c5d2c5f9ed2c19398ba092f93fee6b07383a45d2de202d94512c1df262c9ff721c60e7b8ac940bb07b81d2f69742087b00b31b0d0760e53fd83a518363ca27398a93d88513c93d398a93542281b98371cc41c65fb9826a2751d9b1cff696300cc1c9da45117440da0eded324645460af51ecf6948cb20ca246601385e46d208183da84547a0af05eba0ee039e51e83a5cc260c143732bd4ded283f732d07d412c9e97a9bd4e074c10f63a00e7949e0e9461eef1fd5676ca2b85fb732c7318c1c5cd57f973657fa89dc928dd985ee5f26bbd6dc92a3b071cf5b26b936c5deca038d47b293e3067315268f3e4f4b28e82f8e60ba51eb1cc50770ae41c71cc5acf27ad04aa11398bb8e641ee4f5838d3d341ec7cac4993d2f6983db30c22b0ca2095dc05ec1ee2fda89d4227311749cc6508bd6e513a0ec7caf6995fa73140d839e174bda53d30684d8e1df8c3839dd07b0e3324cc1c60e9602085218838cabf6526a89d422b159016f695abaf0f61904aa4f398a02e41dc73138cc1083b9426a1126b9cc5476c1b8e62a230080b736ca4d38c935e692a0d47bb3134bf6f69412ba1043600e7691ac5e0396a11927a8f9412a0ed5e323e5892a4d982aa4f514a094e626fd8e6280b85de6fd9076731071b4d64ff935c3bea27 (by decide +kernel)

private theorem part565 : Excludes 0xa000010000000000000000000000000000 0xe4bf74240880a0140000200000000000000 :=
  splitAt 1 117 0xe4bf74240880a0140000200000000000000 part567 part566 (by decide +kernel)

private theorem part563 : Excludes 0xa000010000000000000000000000000000 0xe4b774240880a0140000200000000000000 :=
  splitAt 1 127 0xe4b774240880a0140000200000000000000 part565 part564 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part570 : Excludes 0x8200010400000000000000000000000000 0xd79eb4e70928a2924104208208000000000 :=
  finishCode 33 0x741a07a11bb1bf501e31730b988d8858144283a70d5b04ccb3f7b69f158bed557b4cc2f7b4c5835867acbda6306c4948cb486059ad143aec6395e731bda4bce8310eba0066ad9bc5604a0979cc16f6ba3061a5473941e307310ba3284fd606d18362a9f4da6ad4f0dfa3767b4bdb4be6ca2b05fb7accc0d62ac1fe3efa3a5ed2b3b0ebb58662a97cd942f9c6fd0eb97edc773584dfa5f3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part572 : Excludes 0x8200110000000000000000000000000000 0xf7d6b465c828b0504222200000000000000 :=
  finishCode 153 0xc42e8a63284fd4d11c7b4c1a750b86ecbf6da34883d9a9e7350e9c60e0589cd4de3460c7da91f73167b1bc5a52f69498b56e8c1a0b5aba7195e2306aa0fb5ab31cd5a4ac236ad97cce4f356cde2f6161dce6b378bd0b43a8ca2a8d35981ac55416a0f53840e9c9e6b3b925cca1d3954724d187727b0f47dad25629a356393c60dc923ed6617805fd07d3eec61cdced591f693168c3b155623238b319406a3f6918572c75ab63c36ae874e3072d250267277f164b34cd8c592c1d38c1cd611dab16da4aca270a2238c628ad47e5f3961eb3b05f9cd5a433156306ac2f0b41b03ed7bbcc5b69a8ed586b353ded2e5f017c1d77b4b56d44a9174a1ca2562a9cd67b482fd64a9435e1ed3187898ac351f6a98c5594229432f9ca11531ed291f87da5fb05fc640fb4f8727cc252f9bdc4ffac55727c5f37b89ff5ac33da4fbef718c2bdb492f18373597cd94531cc2fda30bc250ce037123e6f18fbec4d6ad9c2e60eb50cfbec4d46ece5f7b4c60cfbec5b735c4c546ea47db449897ce1e1b4943a66f19a4a6b1551a9b34a5826d253858f0dccb3495abaea2e852074e692b5658c0e9c3c339abd5e385a45dcc5e122ef69989ad5b732c4970cac9ef3e2bd65ab6c3548bcba1c052278d596aec61e71d9f7deee8f30cda70077898a19169db586307318fe1f7e8c1b95ce6a9c2302b53efd18369d8645ac3460e2e6c5f3732b4edeead616a1a708e300aa3f8f759ac25f369d9cd53c69d8b35a4b066dc8f3494e4f3995a4ad3b6aa97ce8c1b494de2e6369da58c03f8f69a30707b008b995c8ed252f99c2ce4e2cda0f717ce8c1b4963072788023ccbe67dfa306f596adc9c238c0358630b34ec92e7357b49734e23397da76f699cb237d262c60e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part573 : Excludes 0x8200010000000000000000000000000000 0xd794b5654808a0104000200000000000000 :=
  finishCode 121 0x378c434051b292ab062f520f81f6bd4e2dcc604ffac558c0cf699043182e601f4290c10fe318317692c735441a86f6d98be801051c61769db20882988010c7c8f37319bc545ef69047a0fcdc3110073196ac8e7460dac207b8c0bd65ac3396630718381068dd9ac27c5358b964f8b460ded26f1723a8bd07eba298a235765038b3433e8f38ffef696949bc5442d7cf696a1ac740f73da5aaaf699ac31813ffb18a21c9da8712e4ffef69166a08625cb4a5ed28019a4aa43385a7082f550b9a6e7985e8f3396a8d6618c8f37b4c48e6410fe1a81d718bb576615ac0ded33495cc26f1699a98e479a4af6941f97ed44400ce6b83db56ded334ed8c7f105e1d383dce636aca3cd85ee4f9ab2821371ed3356dc9311ddcc680117dcc639880f83aeb5191f2d250ddb56d6ab398da429ef6aeb10b0398507561e8520c5ec3ba30ec251f68d2e583bda4bba2fb631aab0f0c98ab2569982c5485416a734b476ad3f0da8ed67228f0dcc6d5d7b4b56e5069735a663c37b4b4ce05898bc5f730ec7bae6290d03d0fe02f64a08f74c1662f0bbcb5362aa0f56363dd5c18c7f016a922c0e497ad5660bb4fded2e5f615c90d621b90d6a6d63575edb460d892149732b4fc57ed3f9c864c57acb16c17b25058b7182d25ec3b9ed25ab2f3b156033bda58763ed7f148891ab2e639a76e6d39abda46267359ed23c39ed23136b0d18117da86ded2d59 (by decide +kernel)

private theorem part571 : Excludes 0x8200010000000000000000000000000000 0xd794b4654808a0104000200000000000000 :=
  splitAt 1 116 0xd794b4654808a0104000200000000000000 part573 part572 (by decide +kernel)

private theorem part569 : Excludes 0x8200010000000000000000000000000000 0xd794b4650808a0104000200000000000000 :=
  splitAt 1 106 0xd794b4650808a0104000200000000000000 part571 part570 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part576 : Excludes 0x28800010000000000000000000000000000 0xd77e7664880a28510000200000000000000 :=
  finishCode 57 0x651b0731ec398ba0d203956673da43b6a0d96826f183b6833907ab41d0c02075243515426fa90da53029d0662d99ec2a3d85b20bf922aa2116ca0ce578c1ce605828547aa27419a0b54c3509bec0b85a29df521ad466ad8b44f858ec5f5692c94105fb08c42e0ac2c7671da504bea2d141698052c317a81e0a1811c35eb179ec2a4393e61bb6ada0b4c46b0f8c2ef699cc6901cacc1736692b17524e9396d16c69dcd5d57c97cd27aaf99686c3b506ad06300c921c07c292541b2d5c5b30b662fac2d9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part578 : Excludes 0x28001010000000000000000000000000000 0xd7fe27acb85028702020200000000000000 :=
  finishCode 51 0x7b1a86c16c28d949436b24bd28262f595c625651b45603c6f414347bb18956af3da520e3d3317c94156170286bda63788b74c02aff8d62a433dac1d5a9ef695d12c592cf6962596ed40e1af57cca075968a1659dbdc4f9ef69561b4470c32a35920e93d5d185f1ed6302a35521935e517c6016d0c5f25056771fbcde27b585723d3312a5043c6c23d0b6250626b9b84e62623317aa8625483c83361dbda640e9b84e62ba2d83d30e5c2ab497a505300c6c0957b6c7ab5a1b9b56c7bbc2ab5aba4bd2822b996ae92f8e62f69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part580 : Excludes 0x28010010000000000000000000000000000 0xd7fc3eacd90228700200200000000000000 :=
  finishCode 43 0x360f63a0ca146ce63078ca4270248d596aea4e60c5a9249073da5442e436ada3c5c85abcaf9731a93d24ed25949eda328f71944ad5b2f39cc43c6a8298b15919af6d051a49c9fac6330a3d36cc8d95a8a4e5c931ff60ccb495c92d5b7b4c5e769f9315cca4fd378cc41cc4c3320cded317cdb4651a46210061e3625c92b513ca4f286ca3b30ca8f6527b10ac0e2e835bda55f23cf16ea90cc02b42d467b08f3cde28e3985e6d97b8a3c648aa8bc2c6b25 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part581 : Excludes 0x28000010000000000000000000000000000 0xd7fd3624880028500000200000000000000 :=
  finishCode 157 0x7d1ec771a8076b00c62e01e3942a72739aa20f6951ac3d32909c65cc5d03c6a2794923d358aca279a8652150da58e81c2d886f0de32c6436a51b292ae892f283cb197b68f4c98aa490dacf699ab2521524ae81e30c5c9211c5b5758960679cc648101fbda60ea1b55d14c651492be148520f141d002d3f483c5076ada7b5003317ca0ec31510a0066ac866436a9f99ed20112c6a4bc36a525741bc450a4a1e3692c3cb6acbdae731a7cdab6802488f99ed23d3497b18781c45ed346042fae61623a085cc34605c92f5b9002c5f7a9941dab6f6987a6d3f9eb2a3d6ad8f4c3c6e8078db050ac9077b4c614dfa8014a0944585f1bf588ea2951d85ce37eb50c62e0ac3da4a4272739aa8366ad9684a1a34d9eb6b33092b4b5106c0e323d39ed27312909ad63d5a49d01ad5b7b4b60f695abd06b1e99cc4a42aa28be04ab4d657fc1e4a1a8df483bd070b8a4280d398a205211dacc45377941dab6b62d5e46fbda51f294160ac4c57a1543989e8617611c62537ea4566ad9895cae93337ec907141cf776ad9eae0f21771d793f4dfa9334b180631d038cb10f42d894186d6a296ad9cc4c466fd317b606fd312a7f6160bda4e62a299ab64717b5b08d00771282d358f56d5b7b68255452a4f481ecf0b04d2f2d25ed7185592a4f65279bf6398c3d351d9bf4dfb308e6318f43a0c1b8de273130bbda650bbdc43963b7378872e51e9f073162fcd67378b56e7b4b10f428f66ada31cde23dd41e8ace6b3a4bd47ab519ab63d350bc73116ebda5787a188398a076416a7ae7b4c1d5452d5b60138510dc5b1ab6735947e92f256d06f1da8f4d3fa0bf0da9ed6622b95c17ea2939ac6f1514bda5ed33da60e5a8f5885b1d07303973d84c46c19514c90b8c2a50549e82d606ca4f7b0a0cded218d9452a3b7b49cd565727ace6ae574419438cb78f698396a2939a9cc4a42bc1cd5ab72924e62f6d9caeb15524a8864189cd45b3146ce6a521 (by decide +kernel)

private theorem part579 : Excludes 0x28000010000000000000000000000000000 0xd7fc3624880028500000200000000000000 :=
  splitAt 1 124 0xd7fc3624880028500000200000000000000 part581 part580 (by decide +kernel)

private theorem part577 : Excludes 0x28000010000000000000000000000000000 0xd7fc2624880028500000200000000000000 :=
  splitAt 1 120 0xd7fc2624880028500000200000000000000 part579 part578 (by decide +kernel)

private theorem part575 : Excludes 0x28000010000000000000000000000000000 0xd77c2624880028500000200000000000000 :=
  splitAt 1 131 0xd77c2624880028500000200000000000000 part577 part576 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part584 : Excludes 0x18020010000000000000000000000000000 0xe77d2de4e89030b00400200000000000000 :=
  finishCode 67 0x661845e13841106aea206d946d017f072d2673915cc6c457babdb528672785b26238c5eca2e01cb8e5a0b949db681cf817ed539ecada13564f498bd452a4f2e6cf755b1046d1036ca398e00aa415632d5b05f86fce6b38ecc5e60196aac1948f9c65746d1243356cc5e1bf5c1ecb02dce6ad4f8e32b178e6af693118b6639a82fd036623a880b831ed32d4d8ba71916c9cd5c8b398cb761cf16c988e78058b30cc39e2d9396ae8c1b90623bb49493550633a8b8418a259cc280530ca854e4e735621786b1ca3b7b4b56c7ea5bb85b2f69694c04b402b0655fea156ad8b65ed32b04658c32a3b9ab6c2328b624a52767fb8c5e4d58e6aa4f30bc83140fa93d5ff356cc32a4f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part586 : Excludes 0x8028010000000000000000000000000000 0xf77d25ec4e9560980500200000000000000 :=
  finishCode 19 0x1e86c1583989cb651d9fd504ada3208a28f6527c1be4fea50dab672d514a31e4f58925422d5b396b0c4e5b2b0f698c2e4ef1fab06640d9cb4e4ef0290f698396a293939cd549f28a415e9297b4c82b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part588 : Excludes 0x8820010000000000000000000000000000 0xf67cede54c9a20910400200000000000000 :=
  finishCode 67 0x5e194560e62c40fb65179865cc72314d96a2f6ada01506ac2278b4185d47b293c9bf206e3029ff49da31640d82fc39ec8356e26fa8560f3281e0fee51561841fab56e405a0d53860dcd5b517a015caf349545ef694e1a46f10816ca81e83db985a4a90f6116c83dce47317b57683db94626fcc4969fb56549f281dab2d5985b2922b0c228bd486d2f877e9ed311b0945b280b7b0c4df5118469140f250d8662d3405b684df83cc57f839bdd549ef759837281d6864df258cd49527937db46116c694c6cb6b08b64c2e623650c848fa8ee6a1a855ac734fd58510d18772cb93da7f1e0a3b4a142a8fb9edad3f147b4fe7b4b944b2ea2148ab50e7368d3d442f61541ca33dd60da8eb16c8e5e008c1ad82e1af7b4a50dedac5f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part590 : Excludes 0x8020018000000000000000000000000000 0xf6f4b5a44cb028d405003c0000000000000 :=
  finishCode 37 0x178691587f104a835283cf6938ca03e283bda5d47c1b038cae00b58e6250739aa856398b05639ab56ded2d8293e6ada06ca0e0b79ec262f40db56d88e9e1cc4b9b141dcae61750ac83172b98bde839ac3f5398941e751fc5a9cf6d7a9a924e327356c170540f07b4cd43486a0c4fe2d3fa0e6a49486a0c503f3da547650751dd073405b50d44306cded2e63405ae91879ab25070c6d187 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part591 : Excludes 0x8020010000000000000000000000000000 0xf6f4a5ac489020900400200000000000000 :=
  finishCode 123 0xca34850d290a488218be503985cfd680b5d1b469ac5f3317873d2c66035eaff816ea076b3a485ee300adacea07731c92739abda540eb577f1ee32bfcc5e90369a985d2772d5e0dea4f8c2bf8da3106174b0c5eb279ed2a2938cbda65279635ee2ee12be6ada4ec92f3e0b8233e0a4a4ed3b60b739ab58e2ddbda5c8ae6338c8db648ab68b4228a3d949ee459252a293e7d06f7b4873d2c2ddc6d33f7bda5aa69214edcfe368a29949e1a7311ab88eb9eda7357b4a81c79e8eb93b272d580d00d1ca07482a4a53b73925cbe93b7b4a8a6369bda540e9db1dfae8c42b051b661e85a0c7357b4a014c323f54e1ed320ed4867f57b4c82b51da86e51a80cc716d633009865fc6d1453293cc5eaa248a079682e499ed2c5d39a9fbe83ca81dcc2aff723bdc5b4514ca3d490cea3c0f82a8b158c2e8f31e7a81ce5a7354b107f281d272a2f393ab0a2191e6a35441cc730c60f70792c2bda5aaad5b408a3ce40dbda45b2e4330842b8a3b9ab68357b48b6528a90f9866c45527ce4960bb90d272d5b41ab686d9947a8cb949307b731ad5d1e29f39ab6a1b5a19f8c228bda531f3d492617415a78b4388f2c5f3e7bda4112e479ed28059ed282b5b1f0618985d88f28bdcaec47946aee1906e79476e576acc1e547aa4fa0f2d5936ccfe3c0ea3da638f98bce6ad02b0ee41c4c2e625266d0795279b9e50aca4f83c985dac7395e418a0acc16e63a30ef69838c605aa6d63 (by decide +kernel)

private theorem part589 : Excludes 0x8020010000000000000000000000000000 0xf6f4a5a4489020900400200000000000000 :=
  splitAt 1 111 0xf6f4a5a4489020900400200000000000000 part591 part590 (by decide +kernel)

private theorem part587 : Excludes 0x8020010000000000000000000000000000 0xf674a5a4489020900400200000000000000 :=
  splitAt 1 131 0xf674a5a4489020900400200000000000000 part589 part588 (by decide +kernel)

private theorem part585 : Excludes 0x8020010000000000000000000000000000 0xf67425a4489020900400200000000000000 :=
  splitAt 1 123 0xf67425a4489020900400200000000000000 part587 part586 (by decide +kernel)

private theorem part583 : Excludes 0x8020010000000000000000000000000000 0xe67425a4489020900400200000000000000 :=
  splitAt 1 136 0xe67425a4489020900400200000000000000 part585 part584 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part593 : Excludes 0x8400010000000000000000000000000000 0xe6b6252c080620108000200000000000000 :=
  finishCode 127 0x881ec6c188690a2251b751fc7a11e3038ce62a21bf66ad878d8361e39256d49857e8352dda03e6a4b58cc4b1cc5946014439894846ef11b4d2e9ef2dda0d5ab63eb0f1ce479ed24d7400975dcc61e31f5a3f4e63082b8cc300d5b96ae80137e8b652429331e13847ea3ce721b49502b07b40dcd2941f838d245120f33da402a82f30ba06d8c4e1eb282f724cc2f7b4b9949af3566097a7cded23cf9a4a617731b00883496503b56ce16921c9dc93356497608b71ece4f478b90d692c2f8db307b1e7a0bd40f30cdc8707b7359c2d540719b866ad9c4504b20d5946a1a46d1cc6103c66259056f6994371c9ca1ac4b8a1a28b0718bd5ed30bd5a6a6fd50d9c9ca1b06f9282d5b0719bf43c6f43e03cfa0ea5bb3939804c320e3661cd741ecc328057b4a0d5883fdc27334d96ecc327fb8de21336ad852da4611ed32d44e4ee6b71ea0ad076f699ab71c9de873188771fc17aae00b39c8e7312fa98bcdc33da4e63312638593bd1c692b4129cc5c8b1bf4e6281b415c70b17ab48a22483eb56103693d9cc6f6b277968518e83b4fec1cb60144b1adce1691798c5b1acf41ed42306f48b82cded21cb1b3cf6b83ca31da9e9057b4a09492f2c15cc68252e6bda520b3da4dfae6328d63c01e3174c0e340dcc228ae499838d0368357b4c0e36301c6d42987353ffc82f7b4c62f6979c44b77356d8bf1c2de0661844e0e172094e4e83b6adc70b39a8fadab71c9ded2d3589aa3eb385c1fe230c614dc26f13fd8ba47d682b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part596 : Excludes 0x8004010002000000000000000000000000 0xe7fe27264d0038521084a04042008001000 :=
  finishCode 1 15782 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part598 : Excludes 0x8004010200000000000000000000000000 0xf7f63e660d70381284c0224081000000000 :=
  finishCode 69 0xf6360ba378a614454827eb288e3136836b53ded23c7598a85cbf6d298fa6d43482979e0dac4d052c8eb6ae9c9cdfab3b91d6f693718c6acc3a16adac1ce4eb51441c7b3d5cbce9ed5a3b56cdfad25a306e6550bcd33626b9254427e97365839bf5ab6b517b4cb81d86027a62929c9ded2b3b5a8b50fe2d5e5a4a0bded2735527c7e1292bda5ab72d25ab71c9ded32e0b41b8a299476b495a8bf8a0d967672d7b49c9d3c7b4cc4d7ada8a547718180e6a156a4acedcb2735812706f6adad256a2f696adca297b4b18a41e0fe28a547a2bf8bf6b33393c1d67a9c614bf6b335c0dfb28ec15ea3b922f02bd452a3b7b4a90fe2a06fd4e014b27f4bf6f692e686949df356cfa2f696aec9ed6adbda5506a1ed21a562dcd5d34cc6999aba17d7b4a38f694a1c9ed041a464d2f356cfea5cd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part601 : Excludes 0x8004010020000200000000000000000000 0xf7f7bf272d21e81210c260461080d040030 :=
  finishCode 37 0x2e8c43785e78dfa51128dac0fe141c36b3555cc6d5d7b49cd560f3da504aa0d412ca0d393bda5c86c62989e20bd5fb20c544ed55942b1833c0fe33555ed2a297f0feb390deeea3b618c60ded2c2f6b0d183506b565a860110381002d5d9ed2a0d57fcd618c19c2ded2c2f4915fb2cfd492afd967e825823ef69617c8016a1ed2fe354e412a854e2272d4f1c86d2d907ed55513935d07f392585f35549aea27 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part602 : Excludes 0x8004010020000000000000000000000000 0xf7f6a6262d21683200c0600600801000000 :=
  finishCode 143 0x2488239080b40dae8f037860146e490b502d9499a9260c5ad0c477393d14625cc5d6014933da4e5af6d9ac31857b4a0fe7b6a004a22902b08219ed2b2b727b964fe31c45ed27c2d260088d7d6ae9078c2cd6162160b23649fa907530e6b0ddd6aea4383fcd25008ad0ce6aac2f0d820edfc5d1887b4cc5f288946d807223071bf5ab6a4916cbda660ba3cd492c5f8c1c8d96b23072d5dab6f6991ce6f19cd6e3d7b4c60dc826bcc175a8b9adc7af699806a1863461565aa2772ca7e546aa83186c3902283172c8b6520288cf69735bdb637ea0058be6f193bec33483c604a22e6b927af5328dbb88c278a15599cd5b5a49bf4e6a3cf51eb610719ab66c341fa3f4b76511592c7115a4aa03cf3f7cf71513a0c52666d38016f7140fa89df0720e229459ab6b3b62ea41e46cbda4e4ed5b483cf696ada70bc230f820d5546a14533ddd3d251b388aa0a159ab62d950ac4c548acc5d51e931648ab175fc6a18c7adc72739aa58ba1c2d8673da5a4af699c86f699ac2e6304cbd6c36a9e98dfa4fd6adae88a24ccde33915c86e63625b58e28db90e4f4b90ba2282d98a22c5d619b10e59968e7113f8b55567ac159cca0433889fc5aaae81e0d6318801731c00b41fbdb4e6a9f99aaa90358b9c4672c9fc525704dc46eb1723b8265ac2e4f735cb61c45abb30c5ac2f758082e654c0f84b0de2d41fc66a9c1d53f2f69483c60563251b37e9cd58c460f050ace6d288ad2547ab3f9692e6b6adbda520f1445caf1839ed2d5b8c0bd94dfad5b8fe2f69288ae8c43a0511985e9ed5988b64a368d9814ab4747ec8016adb56e7b49d8f6d985f18339aa93d85f460ce6aa3d (by decide +kernel)

private theorem part600 : Excludes 0x8004010020000000000000000000000000 0xf7f6a6262d21681200c0600600801000000 :=
  splitAt 1 81 0xf7f6a6262d21681200c0600600801000000 part602 part601 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part603 : Excludes 0x8004010000000000000000000000000000 0xe7f626262f2028120080200000000000000 :=
  finishCode 81 0x1441fda488235880b40da98d417ecbcf250ded2b2b62fc8e90018e853de2b30f1b50c03da6595b54e5a8bdb62e6bda5a8630a4b1f441067118c1ce4f6b1b9652865cd7b4ad26527bdb5ed2bc2706e20ed83b1a5ca4af690f1b56ddc7b1ed32bfca42a290f182fe4fe9c667b49485a8602206b0a42aa356d83b3da56aeaff9cc624105fa7b66b1a45d1cec1d7b4ad5e7b4a8f626bb54e527a39ded2d5b881807f0a431839eda9ef4739fc43c71819ecaa038369fc54072be4a4ab3b72cce6b5e1184e1dc41aa28d5b947a4c59aaaf5951497ec05b351d1bed5b60e9cd5ed2d627b67b4878d83ac4d6ad9f4661791f547af69441ec6ada03e58bb04d0625217b0cc1305f9486407bda51bef63a0de3f8d4078d2873964a4ab49949ef6d7b4b93e3f8a0fe474a50e2fdb9ace6b2c5d2769e3da5186a9cf6d51da09547ad43f85219c864d7396935e5139484b9b17ec9aea27837c72d48fa854bf6825 (by decide +kernel)

private theorem part599 : Excludes 0x8004010000000000000000000000000000 0xe7f626262d2028120080200000000000000 :=
  splitAt 1 101 0xe7f626262d2028120080200000000000000 part603 part600 (by decide +kernel)

private theorem part597 : Excludes 0x8004010000000000000000000000000000 0xe7f626260d2028120080200000000000000 :=
  splitAt 1 105 0xe7f626260d2028120080200000000000000 part599 part598 (by decide +kernel)

private theorem part595 : Excludes 0x8004010000000000000000000000000000 0xe7f626260d0028120080200000000000000 :=
  splitAt 1 97 0xe7f626260d0028120080200000000000000 part597 part596 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part605 : Excludes 0x8000210000000000000000000000000000 0xe7766425888060101084200000000000000 :=
  finishCode 157 0x88178731946a0e62e43a0405831dc2909fd641db56c62e8f98fa318362f9b9c9de805587c80541ac1f6040c1ed20a81b621a094a43418d03b80ed9476301561cd7317deb707148c985d04a9217ce728c1ec98a81b838c23737193f5cdad5b27ec15383da0fcbe6d5b46aa09547b209588831fc7c1d05d062e4a78c4a81f28390163fac4fd076a8f63fa93f4c32f0101518288cd5b50aa8a4a23356daa681f410a06e054c60b4a09865fc7420c5b0602ac1b64c2e6939eee83f51a9b0e83d822e0fa825a0e269361106b3565eee7fb510b95cc2ef77945ee574e1abb052e0f68f141283b6410ec40dbd6626bc616155a3cdeb6d29412ca3d41fc18405904a31353080a5f5927ad3f524a4be2fac18e83f83018626d03202fb781184f141b46060e251b51da8f5746acc1718c2ad4d42a511606c1598c0c606095b4fcde2e4f288a89d017461e83ab98cde2d2148657ca0fd44e80b283c9df6d13c6412451ea8ed1e7302d016f623f6076a3cdcd61bf9248c3ce634799bc50165f32fdc6f1076ae80ed531662b53731cf61731cc5561dc6f17b8b03528703b588741b43205a290748ca4880b94864df62ac1e66a9b58d81a80ba0d6d636b1c2d16d13c0dfc6f146382fd47aa3b491283fdc1f626f86fd8aac0b8d964c57b0937c37ee6d8b66a1505fa47e491cdb28bd0166c368e6d127d07d7b6b9154525cd513c1fe2e6b56564a8e99cc6cc390bc248405311c62f40dba00ed589c62f0dfc835513ba0d036906188d64f289c1da46f8c32ac2f8de0b45243203d42e0ed901ed4d47eca3f8c3980501e5cb9cda7dd6b3a03c35e80b9a6b165dca294572783b50160ed9e06101daa6302e83d82a4376d4d98467fb62a91e65a2c6f13fd9354bea62f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part606 : Excludes 0x8000010000000000000000000000000000 0xe6766624080020100000200000000000000 :=
  finishCode 63 0xe435106105483ad802867baac5dab67111809cc4a36820c050839a9fed1e32c74b7716ee4789cb5b00729f0731731d07b5a0ac3e69fb0c659da81d4925bb740836fe27fe6ad9fcda6a6250728c05b017dae813f9ed28014efa3adac6511408cd5b7b4b58650ac605ed27ef6adb29061cc574125c46b4f69fcdab66fd4fe93f544b1bf41dac5596769ff26ba8ec9fb356c1dada328f8102de0292c73138583b4a4318662838c05f0881b0189b005076315471dce570c59cd5581d0caff7ada0ece4ea493f0c8258f6280150da7ce83ec1edab6f619c92f69388a06d076f02c4e514a0ace6a0e7076b9881b5b10032084c5e4a7967eafd2dd9b856af16ecdc2a4f82e650730c8c06207f0a370c04a4b0becde316ed0360e7 (by decide +kernel)

private theorem part604 : Excludes 0x8000010000000000000000000000000000 0xe6766424080020100000200000000000000 :=
  splitAt 1 117 0xe6766424080020100000200000000000000 part606 part605 (by decide +kernel)

private theorem part594 : Excludes 0x8000010000000000000000000000000000 0xe6762424080020100000200000000000000 :=
  splitAt 1 122 0xe6762424080020100000200000000000000 part604 part595 (by decide +kernel)

private theorem part592 : Excludes 0x8000010000000000000000000000000000 0xe6362424080020100000200000000000000 :=
  splitAt 1 130 0xe6362424080020100000200000000000000 part594 part593 (by decide +kernel)

private theorem part582 : Excludes 0x8000010000000000000000000000000000 0xe6342424080020100000200000000000000 :=
  splitAt 1 125 0xe6342424080020100000200000000000000 part592 part583 (by decide +kernel)

private theorem part574 : Excludes 0x8000010000000000000000000000000000 0xc6342424080020100000200000000000000 :=
  splitAt 1 137 0xc6342424080020100000200000000000000 part582 part575 (by decide +kernel)

private theorem part568 : Excludes 0x8000010000000000000000000000000000 0xc6142424080020100000200000000000000 :=
  splitAt 1 129 0xc6142424080020100000200000000000000 part574 part569 (by decide +kernel)

private theorem part562 : Excludes 0x8000010000000000000000000000000000 0xc4142424080020100000200000000000000 :=
  splitAt 1 133 0xc4142424080020100000200000000000000 part568 part563 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part611 : Excludes 0x2800c000400000000000000000000000000 0xd7ff26fe97207802ad00180008000000000 :=
  finishCode 35 0x3b8c4348b624766a69ca542e1cb395a987a1c6c5030da5acec596a59b85acb06358b2f6b93faf655219c510dfa7639b6627bdac34eb495a8acce058b56d282c29960e93d1f0bda51eb359dc76a136ad9bfded3356d48510dfab2596a2d670e5b56e30b34cd67e70d9a9ef6962cb56d885511414ecf6b3e8ad2434ee6f4a09bf47a6a02e09418c2c1a96a5c0955a8cd658c2a475ab66fd7b5c9fd4a09bf6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part613 : Excludes 0x800c000400400000000000000000000000 0xe7af2cff0d207a4229629a0108188008008 :=
  finishCode 51 0x348a2188ca202d748807d6b3d856a6075a8a84e3e886fc56ab631057d9a96b512f3a7bd49a69986baa156a5ad44bce9ef1e8c4c5474b185db256c34d483acf583ec3758ead463031b4cb3a47304a9bf5745b07d609b8bceb498dc28c440f6d9692d378e026e1736a855acb23e4bceb6201103a891d3607f73db4b9a8f937eaf8a60ebe47c979cc0ec597b4caf11f0ce4547c8f8647c979d746a4c701509b58ce563fb8c1cd371e8a89d42ab07839672b5f2203e0baef6d9aa7079699b5464feac1daa70fec7f73105cd37ec61671da41d5f6d635a9bdb6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part614 : Excludes 0x800c000400000000000000000000000000 0xe7a724fe052478022900180008000000000 :=
  finishCode 111 0x69144561a0415a0ee3031ca47f672b5d033f356c7f6391942ee558c0bda5ab68244081b53208780c0e8a356ce6f23e544ef5991f2f7758ead85db8e6e7d18d3270d5b0baf356d8527296adc5d7631eef2934396d5b599ad447f7356e30ad5b856a3fb54174395aa8801c6c7d6c4fa30ad536adcc1f838ad25acf2d453d2c4f5939f4634c981ce36d5b620ca27483accdab63fb681884c14c303c8255939c6ce52a830072b699cf6d26ba7a5ed6d511e8bdb6699b17e1fdac9cbcf2094e567c260a632870d5aac6fd1e0b53cdfb046e30a8257b48f056c2c0c8f926b9f45a9e5e72c0cd6583ca3104209547b2cfc9af4605ed30798bcec0400607988e3d18c0cb556149bf4bb63fb7b4ca4f8c2b28ea1903fb631ed32cfded6d6550a97367b4a0967b5981d4c412cb1359fa89e0b0b59d62709bd04a5e7510a83c1ab6821fd65a3ad4d38560b9b181daa218d5939fd630b34ccc0ed4f82e24a18c2b4ccdfee39947e6ff67170621303c2204e168eb330d4cb273fa8f865939bfdacf1bfd64eb53058c6ff37ec1be1bbc615caeb516b1accd1f334dd6a26fd599b4d6588d0753039505cd9ed27c2608a34ce5838f44dfa6ff593d1853fab59e2f3bdb527ae57728c616 (by decide +kernel)

private theorem part612 : Excludes 0x800c000400000000000000000000000000 0xe7a724fe052078022900180008000000000 :=
  splitAt 1 94 0xe7a724fe052078022900180008000000000 part614 part613 (by decide +kernel)

private theorem part610 : Excludes 0x800c000400000000000000000000000000 0xc7a724fe052078022900180008000000000 :=
  splitAt 1 137 0xc7a724fe052078022900180008000000000 part612 part611 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part617 : Excludes 0x9004000420000000000000000000000000 0xf6afbffe8131cc120de0480208421000000 :=
  finishCode 47 0x178511a46adac89214463fda505056cc318835169c5bb83acb47588d18325da4aca2298312e5a38b4e736c604dfb3dd4a2280290b2338963106fd59fca15288a5058b301ee306a151e7b10e57947a4d71e0a505aab2094332b558f5ec41038a8ed04a7c242dcdf460447ad53581b95c0f6075531caf34bdc726c9a3071856912c039c6ab03d8f26302b3f5a2b9be696ac4c0ef05cdac2511590bb66c99256f6d736ce398c2a055a0801c9f24ad477079624b17d64169cf6537ea93dca716d45a6e3b5a3a506 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part618 : Excludes 0x8004000420000000000000000000000000 0xf7a684fe0131481209c0480208421000000 :=
  finishCode 137 0x1a0771a462150530e56d81c6e007810032d1d3daa29593a4cdab63e12c0fe320056067069b313c23a8111d894450230ec502b4605022835a0e27f14088b653bf30ddac608f499b56d606c16a32d4c7c2b3d963ad5b3f8c811582ad4d4c4c16038d9ca6303010d5f6b33361ad4ca2281593c27ecc2f8c0acfdac65e71e79446599a60b0796a6f69982a9078c092ed60ef0288bc258d5b45138262c70d8c0a09528ac61c8a3d8b76b51947ac29a3069ed369a06cdfae63985f18137ea7b542a4c541abdb650a8b656663e14b174541d44e05b29338dfa94583fc35f8c0a004dfa3bfa302e4f514a89d8c7b4ce5957cb98e3024bb1dfad25c9f4604e1a3e19693181624ca275a48f8530541601e7cc473868ee6303209588ec49410a5154c262ca158c0bda560e3cf386c60662fac1dc8ae634f19c4b09af2c0e0f28256239bf63023cf83cc0057b6a094bcec4701ad079412a89e3030b65ed2a81c3588f1b8500281140fca22f0f2356d4c6209e7313d64e6ff51d94458c1e7cb337c1eeb0dacddf18537fb0a4bcf3dd4a231bf5666a627b651e827414aa4f98926fd63162315fdc72a3b7b6a0bd692f81bfe37e94447c29df8a22f6d4f0a22c4798523cf624ac1e37ea3e5ed2f03586729a514a22d5b6c188660a22b620558bf24adcaad61009ce3b8c2b054942e55729cd6180d281113bc9df40d9b8d88ea23c0ba150e599cd62d96ada589c20567bac604a2283b4a2b18762307df410cd3783f9315217396544e921485c2d91b5c027288c60d24f242dacb39b563ae596adaf09e20adeb31f7deeee599cd680b963a041846eb07500bda520690b (by decide +kernel)

private theorem part616 : Excludes 0x8004000420000000000000000000000000 0xf6a684fe0131481209c0480208421000000 :=
  splitAt 1 132 0xf6a684fe0131481209c0480208421000000 part618 part617 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part620 : Excludes 0x8004000400000080000000000000000000 0xc68684f6832058020d00090109000805002 :=
  finishCode 157 0x420ee378d02a0c42d8d81cadd0881f04c1a6b1444c0e83f400a85e6ada42d05ece1f0511690ce5537fb53d232be38e62f182ad623460ded334851d692b6a7a08641fa98d5b880dfeb27989eb497b4ca4d052a7b6598a8e59c6ad82c65a4970d35966290b62ccd35598ae0d829880162ccb2737fb56ce36e6b8dfad4f0f1ad443c72d246f3078d5e2c595939bfe04891a4400c8cd69da02dedab49415878c7f6a2338763e0b496adc8017abc5cd475acce6adb4d6474cb077b6a854772f697b4cd5b37e878d7c4c0c0ef6d900282f9edad35589cb497b69f15cae82f400bf8ea3191034d43ae51196666ff96220b11fdc5116a79bfd67b181c37ed356a79bfe5a48fade4631d45903c6ba359e16c8fee20380ce394a0b56e380c1c6418b13ce02a2358e485a80d47ea8242dacf2854b96e6f379a0c5a6b27b6380a004c0e8150f19c0d5b9216e39380b56e4a0ac8f82a06075a8c7eb6ada0edaaa801691a9f41d5016d4fa0d6a41f0b533eace63598b485ace3fb6ada41d27a2bfa3025e37b4cd5b68098b34ed60a7820567b4b165022c298de654310d5b881705b1245901572ccca220af48ea50530485cb0569c86a568e3e17b5cd6372aa42df037ecb31418ad4e71cc1bc3425075a9cd51592bdad69281137ece5126f941da451fd06b727a49c34a83583aca3941f9bf61fdc40d8348507417c811592accc7f6b339081fdad1e3f7abc56a2f6b964b06b947e835691bc5d03c6980fed484e1662b53690c7bf72aa0558b30f25ca6e55012cd218c2ac15c7716ec0e2d356a7a0566adac8d678c0ed3b1fdb486582b10a4440e82c8d5b968ed55495a50521713f66b0acf5ab60ad967a1a169ac4d56ada3e6690981daaad35 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part623 : Excludes 0x9004000400000000000200000000000000 0xe6afbef68731c81a1960081048000400100 :=
  finishCode 23 0x348ce2c81e33c07f6d2d8792a276ad96d457f289cc0ec2f8792b05591acf0f2544ed5b1fd9191859ace9c0d968c29fd5a9ed216a7ce398c2af098356d244a168f0214baf2505c9f2cf5472a4d92165cb98bec19 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part625 : Excludes 0x8004800400000000000200000000000000 0xc79f85f68b77592e0960091008000410100 :=
  finishCode 7 0x1103c8d80f86052b56d062801288ac766adad458332505ab609d418c811 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part627 : Excludes 0x8004008400000000000200000000000000 0xe7c79df68731490f09600c3108000400109 :=
  finishCode 15 0x6c0f05d1002b639865a9b0b4b9a8215316a6c37900b075262981d1d2b07a0e6805835a37c7f66079ab65cd485c139731979dab66f3303a0c5647907f7356d0764d79426a276adcb05 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part628 : Excludes 0x8004000400000000000200000000000000 0xc7878cfe8331480a0940081008000400100 :=
  finishCode 147 0xd022898298d21bfdd438db183eb0f1b13e5a8922e627a40d3de801303cd8318e8204641f8e7e7abb93cc0eb27509a8edeaf0ea5eea3e127e981e6adad45506918c621d4395bf912078d64f2cf528b2d466ad8b65022b5187c2b3d6c149f20443c727be0f1b56deae801395b60680e880137ecd67509b56cb9b28049aed67593acf56c699b18b3d9a9ea17526a085217356d42e4d7968ed5b6a7ad466b3ac9d68e4d76adb48fe2c01e36a7c915578b53549f2d4d22a1399ab6b27501ad4c7d66a796a2d4f6b3a98b228ee4178f3cc0ea83607376adc82f485cd5b7298ebe1e7ac876348a4f2e6c9270e99cad4273db49aeb51055cd5b0e3973547ad24616588b17d60e72b50bcd338c2979d505b1a46c0e569839863f8878d042607905e1e39b063105f2085ab71bf4b9af571f09fbe485acf5622d5b5a8bc0bc150d8356d60408c3e10f1c8011fd8b34b9b12348b27982a3eb0d4cd53593acf411f448c42c0b273dccb511fdcf75408ad1d607aec83583c981e41abdd502208f84fa1850ccac9e483a004c0f46143c6801408ac0d5b83ae7b56b2b0a4c0e5115a8ac753df2055eba1d37919c752045d03c68159eea1d32888fade08c0c8f158eb56d8c4f7cc377ad975d6a283b9ed6c4074d507ba94453bf05d51d27c5485b9bc2eb277c00b23e4b9b1814efb0dcc0ef758811f3179d426607485a98b3f9062a139ab6d635b18c530c0f20bd0627019eb690b51ea49d0430230de47ca7bcc0e815485ca03380981d60462040ccb9be62c9f85022903581cf756adc9277adb0dcf6b3dd524e5cd53105f20c4c0ea0249e262a7b547a9279042701 (by decide +kernel)

private theorem part626 : Excludes 0x8004000400000000000200000000000000 0xc7878cf68331480a0940081008000400100 :=
  splitAt 1 111 0xc7878cf68331480a0940081008000400100 part628 part627 (by decide +kernel)

private theorem part624 : Excludes 0x8004000400000000000200000000000000 0xc78784f68331480a0940081008000400100 :=
  splitAt 1 119 0xc78784f68331480a0940081008000400100 part626 part625 (by decide +kernel)

private theorem part622 : Excludes 0x8004000400000000000200000000000000 0xc68784f68331480a0940081008000400100 :=
  splitAt 1 132 0xc68784f68331480a0940081008000400100 part624 part623 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part630 : Excludes 0x9004000400000000000000400000000000 0xe6aebef68328e93b092228000a080000800 :=
  finishCode 15 0x691740f1c3fb513cd3b3fd878dab6a4298ac4400977bacd5b4a09bf4c0e2bf9acf0dac062a3b6ad868d4526075d147b34cd68ed5b526acf5ab7356e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part632 : Excludes 0x8004008400000000000000400000000000 0xe7c695f68f28492f09202c210a000000800 :=
  finishCode 31 0x2f054310d5b69164790c0f2d4dc9e50741aa4ae6b0c60d6a619b62286cded32055eb6b316b3d06b279c1bded283f5a9a0d6621a01fdc1b3598ad4d6481128341ac11260741db5463efc60deb6607369b53659f9bcdeb67db9022b3341ab18f8298b62c8831405c80f69bb9460d6607509a8ecb3f13ce0d6e5172bb07e598981d6a320856a3178d476c1590165e3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part634 : Excludes 0x8004800400000000000000400000000000 0xc79e85fe0b2e492f092029000a000000820 :=
  finishCode 63 0x1e46c22058224288b48ea206e0f324cc7d63fb53106b27bdeae8316ad86fdab72e0d5b4f7c8017ab9ac5666af19ed327bcdfb123a8f00fedac32be4bcec5f6adacc56c727cf5940ab585c7734e502a6e378106b30bd3deb31736c5e7781003306c5826fd4f7a4cd6c41fcd6162492ae835b48b23c081b501ca3f0598b6528a2b587d6f039b6837a80d88eb472f3ce6d7ac9b8d472b828fe51c82b5ab683f7abc80f51fb49122e03fb371cc47839acc55f2b255a3cd2142189731747a69335b1ab7317cbb6d55451aa2f69922ac1b699c4c50d3cb516adac8b024667acb56c12ab53371b48527a09f0e1c92b6c180371cb31166a03e5a3b17d836d5b6aac6e3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part635 : Excludes 0x8004000400000000000000400000000000 0xc7868cfe0328492b090028000a000000800 :=
  finishCode 113 0x1a069188530e57121c6dac81164400c1e3303bc0b2796a6f69982a7f10f1a045c772ca50226070ebbc0ba0f8412b2cf4a22b259ed29fd288c3b15aac1d38c286a457f12338d62d466ada3f50221e3593c7f1500ad4d452af9592ac9e59e8f8637eac956669396adc48ea2e83d390361e31fd981e408878df0513c821303a48e6b8bce93393dea136ad878e531146c0dff102e8f23e04fd5a4cc1f1f0979e4f7826d1d70f3c1624f31f0cd5b1e7ce6f877ed5b6c1f04efcf573038f85482f3cb27049978c146d5b967b2d45ed2d5b8819c21120475accd8933d5cb9b1858bced4f526b56deae511964e8eb5a8b56c0c34605edaa13475b56da9ed67699c8eb526a085e481224591545e07d6f699ab682b41dac0e4f894e80b5a4b93e527a0ae7b4b56c7f683b63174601ac15d8b6589f41cded283f3e9d07550bc6060e6f69699c4c5041a3f4a22a638e66adbda411ef6ba3028156adbda56c0f1ca03380b4d640a878d740f19c0650196ed28a8fd6adcb6318ba2701a3526c2cd7adca032f39c05ed2af1965e5e772ab56d68b181c106e4f51cae8b027f6166ac649fa607811ee4f166b8e66adac8d5b907e1a3303a30d5b8fbe83f380b1859f9852e6b7bb8b65ab706f59fcc41 (by decide +kernel)

private theorem part633 : Excludes 0x8004000400000000000000400000000000 0xc78684fe0328492b090028000a000000800 :=
  splitAt 1 119 0xc78684fe0328492b090028000a000000800 part635 part634 (by decide +kernel)

private theorem part631 : Excludes 0x8004000400000000000000400000000000 0xc78684f60328492b090028000a000000800 :=
  splitAt 1 111 0xc78684f60328492b090028000a000000800 part633 part632 (by decide +kernel)

private theorem part629 : Excludes 0x8004000400000000000000000000000000 0xc68684f60320480a0900280008000000000 :=
  splitAt 5542 132 0xc68684f60328492b090028000a000000800 part631 part630 (by decide +kernel)

private theorem part621 : Excludes 0x8004000400000000000000000000000000 0xc68684f60320480a0900080008000000000 :=
  splitAt 1 57 0xc68684f60320480a0900080008000000000 part629 part622 (by decide +kernel)

private theorem part619 : Excludes 0x8004000400000000000000000000000000 0xc68684f6032048020900080008000000000 :=
  splitAt 1 79 0xc68684f6032048020900080008000000000 part621 part620 (by decide +kernel)

private theorem part615 : Excludes 0x8004000400000000000000000000000000 0xc68684f6012048020900080008000000000 :=
  splitAt 1 101 0xc68684f6012048020900080008000000000 part619 part616 (by decide +kernel)

private theorem part609 : Excludes 0x8004000400000000000000000000000000 0xc68604f6012048020900080008000000000 :=
  splitAt 1 123 0xc68604f6012048020900080008000000000 part615 part610 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part638 : Excludes 0x8004000880000000000000000000000000 0xe7c42d3e61c509081d04202044440000000 :=
  finishCode 59 0x5a1947b1845a6be8d02d83fb8e1e73780130182b576246bda56a671b302ae893ba0e2e3d1459735622c1540ac9fd49db95562331147f7022c882b9ed283b72cc3057b4a05460b2cbd58588c2cd286a84e28ba50cff6933801ed31036096145d42f359ce1f0c15476a3f514ca13387b96460a50d0e4ca3ba00611ed32095286f6991f6a138c0b9449de80526b8c1458328a5ed25e136ca8ed04a9c2b06c30564f4b175ed27d540abc0f69412a7a636c8c14e1ea2951d827e5914771cad47a07196a6f773028c1584182bda671e8d754767371adca0151d9815ed2c2331022c883b9ed281b28bcf6940a9c7588741b589a71d1828226737920d62271d1b5c6057b4a7a460a70f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part640 : Excludes 0x28004000080000000000000000000000000 0xd7dc1e37c54409000b14002000040000000 :=
  finishCode 101 0x144370a8741ab6fa2d8b2280de24ad282f578e1ee638de6d223f60698726358865ded251748eb48de3c8d5d8a2e7019242b4357569b1ed56024c55a1b11562f1c0ca2f2795abade3480d19606b454a2834d681c9d18569a8724dff07193cae556989c0da52f7798ba7037b49ed5a069076b0345883145da6ab572e4872563317245b2f779caab572dd8b64dfede348fa3a0d02086485b554a2e70f068ad898242d42f145d0220d341fb5764a0834d05e945962a0d35b18039596be50b9c045b2d5d986e1a3515ad345b306f45b30b056ae1c9069ba098145c392c37a303073381b0a5a52b156989c0e694a801bd51dcd43839ca4d5abc3e1418a044e07022808c318e8280547ab438e0682f410b59e5a6bd6d6c7d1d0379bdde8c2b4d47b2517526cb575a6b59deb6aff9a9ae615a1a7b6651d05a6ab027d9686a27483ad550032c55eb61b98e6eb3f9eb6a273819c6e068ad34b9b034c3928115a6a80f82c0c02d83e1530e073da58b2831595c9e99ed2703408a900d3969a1954a0a7b6395bda56c379c9415979cdd0625cd965e71b408ad341a32504e1f359c392b4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part642 : Excludes 0x18004000080000000000000000000000000 0xe6fc8cb7c31409000d0c002000040000000 :=
  finishCode 109 0x5a13c2e1e05a69e0c62c87d59ab670f0e4a8a547b08260b279402d4d408a085abb24ed05e9179a9a3c9661a484100af578e02e4757fa49cb6b356deb31fd562ed670e4b16e069b495a7eac270b01f54e032cbd6aa8150d286e507f3d5d632b1540aac8b17922ed5b51d9cde0dcbd6e106b3cd430e49c3c6cb2bfd4720815a0b30b23e8835694ce538399cdce1b073905e8318c2c1b940abe8b179252737386ad0649dbc054348d5b751c81fdcc2d0698b4dabb20547f6921837270f37fcb317b4ac9da6a1bd621a0841a47b2ce6b588b5343920d13879e9073947ed675c1a8739ad6621c97bbc3b5017ac9c7e728fc33720ac1a70fed885c0e6eb006f68c2a4ed286b179cd72c5d68b0feda4841e0741a0588d071722bdb52421c93878345d458acd5b16c834d01f02b586a3fb8e029456adb109c0714e6ef6d94726c39a9f0758c29a74b7b2d547f68357b68fee6ad834c37b34d5e02a1a46adbc8e5381a68151fda03e593ac6570588ce6b48fa0bd6232c5da6aaa348d00fec9af03452c71ece6b69bc1c56aaf5998b6e6b71ead8f5da0e2d35417c1b67b6ad04e06f75626bd761fdac90738e3a8351fd9c76 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part644 : Excludes 0x8024000080000000000000000000000000 0xf7d40df6c11649204904012000040000000 :=
  finishCode 113 0x780dc1d1ec6adb28de2d8ac36050d6807c30afd69a1c9417cb57595caff969a5175c169a2d996ae1c9486834d002b2781a6ac2e0d012563eab48569a0ad5a9b166595a43476b205569b07b96a6b4d6f1d44e12422d9595cb274a2ad5e7319fbd44f243d28a1c968189720d5aaab5313bd18162ca0fdb0402c5e1069872542735355fe93b50aa30b03e1021785b06105b2ac145e415a0eca2f206e0f341bda7e51750aaf8f699242b4d054ad0c9af1f560deb115a6c517068b10a0072567b2c4549eb3d96229db8d869276f158069c6065a98d65ca2a01415943502ab2391e8c2acc5ca29db4a2ad35476b539622d3b969a3851d6a056047519416c9c89219266b4d056cb436a69435ac3289d945a6c5176820f307247c2a278a2f408f6328982d35606f14c286a89e62c8284b4312a564eb43513c1ad6a69f556a720eda8e4953fa9435687034544e50d6f12c41dcb578c0b9852669456c1cd707145b28a135e51da0ee59eb555186a3c5c9418a055cd7312da8ec41418b08ca41c651e9785276943381cc29069a0d47c330a5476c59410cd3f1f0ad35946c09de50d8c0ce3b736c1cd00aa170e2b9b65a1a3ed2864d7581647b6d0758378714bc20a1728c82f3f7c82f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part646 : Excludes 0x8014000080000000000000000000000000 0xf6e69cb6d106a940190400a000040000000 :=
  finishCode 63 0x1945a13c2e1585a6b10cc3586588a89d45209d49e86e5d04f6cc2b39b943564e93d37fcb1139ba354142d5b8014c28b8ea6051b16e513bd5d3de83b944ed4d4128fec393145c7f63a308d5b691e40d1c50d415a0ec7f6b118bc693d39bb4d6051b10b118a2e5e3387a4f54273db5a4611e4731c399051943505683b1fdb53e5888294e6e5178e1eb41837ad23a0de3c893d068978e626bda51fa3fb36cc91d588b56d66327b55fe13d722978c7f67d51fdc5179c721bd6a7b48c40fed27b356cde6517989b143558611a8f1c3c76a737412b108058e1e92b49eba8b17900a0d3514ca3b6f1c838ec0d3410e1ed2596af07b6aab98e837b4fd5ff356d282b53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part647 : Excludes 0x8004000080000000000000000000000000 0xf6c70c36c10409000904002000040000000 :=
  finishCode 129 0x328b03c061d314a30d5b7b6ca4f0e48345402155944e517068ad347f70c157c2e0c56de2d35a0531e039ba4365888c163e2c3055889cac1a70c14a1ae61bce4f2a05460af5393ca387735bdc4f8af0150d8356d14811abae53921eb57836c737982a2cd588bddc60b3055ca2a01380b41181962271d7acacc4e03046c976f75839b575eb23058e6f022c8f20c1641dad0b2796a68215a6c1d6483a5053fe0d1593c4db40a9b1d3cab4d7aec5cd5a6834560521e0308bc89c2b06c230c0201502a963d6e050c604f7270f7bbb56d2423054a2bdd683cb94400a0a1735a4ad3d32464e0693d75200381ad5e4f48c156451120eb03968ac156ada3e616cc90b6aec1e64a2a0bd20e305495c30562060ab2241e69fa4ae3031c0da4a9ff9ab6d55069b4fc47b38eda4a93d47cb56c60ab2270e81c0d6c495c1b94a0a30a29876a9073ea9510714839a567bbac4585ad5b588c9276b0c5955ab86f544e1b98936e6d4839b262dda365ab7181381a056495a0ec60aa2230d5b59114350c3e13eaabfd036a3d51dbc8d659686703514bd6d07691994526f3379cc378e06e61513ac5518590f0039cf69527a09542a80581a691951dad565949ab460a815379b98e7b4a89d83e3e162ca0c5e44e15859102af698fa2811499a89d076b63407379ac2ba46066aead5e0159735ed2f599aba3058c0a045bc6c060b35741a670d860a3059641829cde5a2b56d27ad5b9652b1572aac8fe356e4a2a41d232ba34de4a2b56e6adc921 (by decide +kernel)

private theorem part645 : Excludes 0x8004000080000000000000000000000000 0xf6c60c36c10409000904002000040000000 :=
  splitAt 1 124 0xf6c60c36c10409000904002000040000000 part647 part646 (by decide +kernel)

private theorem part643 : Excludes 0x8004000080000000000000000000000000 0xf6c40c36c10409000904002000040000000 :=
  splitAt 1 125 0xf6c40c36c10409000904002000040000000 part645 part644 (by decide +kernel)

private theorem part641 : Excludes 0x8004000080000000000000000000000000 0xe6c40c36c10409000904002000040000000 :=
  splitAt 1 136 0xe6c40c36c10409000904002000040000000 part643 part642 (by decide +kernel)

private theorem part639 : Excludes 0x8004000080000000000000000000000000 0xc6c40c36c10409000904002000040000000 :=
  splitAt 1 137 0xc6c40c36c10409000904002000040000000 part641 part640 (by decide +kernel)

private theorem part637 : Excludes 0x8004000080000000000000000000000000 0xc6c40c36410409000904002000040000000 :=
  splitAt 1 107 0xc6c40c36410409000904002000040000000 part639 part638 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part650 : Excludes 0x18004008000000000000000000000000000 0xe6fc94b75f000c0d0020040000000000000 :=
  finishCode 145 0x39168440a85a6af0c4356d80581700dcc1bd15bc4d540ac0bd6b3c8357ad9bcd662b53418cf6941aac8c618878228c5d96a6a13527c203fba0d6f69410ad0e83ab0658be72d0cbc73562ea84d4763fb98bac5f396b08922d0e405ac5e60cb0bc7f6f6d898ab1560ab066727a005636c42e0c22f01b3906a0bd5a9ca2740586cdcd72d4c3924d54188e0e838b10dcc6b5358db93dcb21b35abc8311fdac8f2348c23a8a20fed7872fc1bd6099c9d06a83b4618c72fa45cde700ed42673583ace6b7b6b8f6000a02cb96e65396ad567b4935d7846017b201506a0bd942717356a6bc390c42e0f698de683f402872518727c4c5402a89e41fcf6969aa03d6833985ed283f402b90a0393d42734d5ed209769bd1837b4b4d4b970afd707b4ce5f7328724e5ad67978601acf072417a8a0256388935c98b1b9d6a6ea2e80959a6e1b37b4b17507f3995cd672d735c5cd5a9af0b1b5c18c0e4bdde60b9b9d82f179e7bbac540cf41b49426e77c17059180690e5a3fb8e4e83b121c57f6b29c9ded271187f683f8e3eb1b5905b62bd89aeb43a306d6715e8fee6216858178724cd334a1a0ec37a1c97516463162b28ed4523fb396af894298b175a182661a6b054b963fb974730c3fb60ab0b5cb32c54753173582ae639c9ed6783fb0c60dab1b2e6cb535e16ab356d02a0bd751645d162e7355a9cc1560bce452dab93e83fb064e3e5b5731c1b56365cd96a6f82c87279ccad5b05e9cb507f1c7d6363fb924396801e16dad0c47b237cb6a3fb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part652 : Excludes 0x18004000800000000000000000000000000 0xe7be25ff4b41080c1c00200040000000000 :=
  finishCode 61 0x308f83a8f0318c033071f581ed2d02201c9265c93b837a8e42ff359d27706f9cbe8354a1ae8b0586d6b4d731bdddaba2d91fda0d65a1605a6a8fe526b94e72ca3c47f63fb89aa93b87c63fb388ac07a288e598bced334948b6d49aa2b167c5e749db9be7adbda45b68151e8ae8ee0fed02b2d34e029399eeac5d481ce5572cb4bd02af6959106b0fad6c839c7375a68b3d69b2c0ee1e8d4f922e9295e169b07245b6b53947272b5a69a4615aa8e54568152e68b6cb856169aa82055407284ce56a13983b358d206a03501c0b540a9cac7f7318f69601a9f3055eaea2b5a68b64e3eb628ae6b3a93545328ed69a7111c3cf6d5a68725472a2b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part653 : Excludes 0x18004000000000000000000000000000000 0xe6bc04bfcb0008000000000000000000000 :=
  finishCode 141 0xe4348d03301e3818e0c975079f1c643c60cf61150410c5e75a69cad4c5a69356090809523ef6d4078b6ce52b279a9e4799dc7b18c751f45903c6b62e01c76b3c075380bda4e227355abce6f7b4b009ff9ac6719493a3c49ab358d6aae6f7ad9c45704714c38fb9465abbda521a82f16ccb2d6b1cb4d486acae0e6b575abc8f18e6a82f069aa8a63a0863525ac68c203d06334fdcda2db380979e59fc927481972e405b0d4dce1bf405cb4d6a7b58d646611841d96f6626a0c65aa9fee62dad35ab33dd498e0d383c61bf9a9691f2e5b58c5b60d3601076b15928af59493bda56827354b0e22d679ed2f5b407b4e6615bd6dcdeb83a8b2318aa1c9dd0396a98f6b9a627d169abda5a92a3b40fb4ce0e4acae6ad8b6d4c770393250c39320fdab7399415ed333d148550e16c22f0c1da0da7f549d8b6da6b24ed602c43982e3b57baa85da92f7583923b56b3aa8c220065a18b6da6a5e76a4cf6d69cad5c392aff89aad3572fb994392bc341185983a2db62d86f4dfe1c95415ff06956ae07d85b69041fe835ad35422d631e4a50e7714c41039320bd23e943341503d21049dc1c672ab574793352439271f8956e6f5968b6e3face6b16d9c7d276d5d8e3eb470e4b4cd05f07257861154728c1bd48ba0843422db591a672d1dab6c4d50a82bd505a3cd3341fa07e5a9b59c8f3072630741acb969436b3973503eb4353ddc5a6b56e4758f3dab723acdc680f6a8c9ff737c60deca4d75a19c645b6ea3081e35801863fb40ac34d5a3bdd5ab6b435a6a8e4dc72cc5682c5f5a6ad0651cad35a0771303879cad64f3595a6ec176b1a0fc7a2d539617071417a85c55f2d341861bf9ac62db (by decide +kernel)

private theorem part651 : Excludes 0x18004000000000000000000000000000000 0xe6bc04bf4b0008000000000000000000000 :=
  splitAt 1 107 0xe6bc04bf4b0008000000000000000000000 part653 part652 (by decide +kernel)

private theorem part649 : Excludes 0x18004000000000000000000000000000000 0xe6bc04b74b0008000000000000000000000 :=
  splitAt 1 111 0xe6bc04b74b0008000000000000000000000 part651 part650 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part656 : Excludes 0x28004100000000000000000000000000000 0xd7fe2e3ecd2858208200000000000000000 :=
  finishCode 67 0x398f82f0f60b9da46303c6f03576599b56ce36945393a60d438dc2e5162c9c6d50737cd5d5959b86386cc593709c6cf44a0e16d80ed5193359deef1852e49bfdabb1859caaf6989fae532bfcf690de93f4e32d230463938f4cdc271b38cc6e17b1e00f19cae4a2ad4549e7355d0e37350cdc24fd5a4cf6587a6f6962c9c34e36d23901e363189694551ecb3b386cc2d6acce43732a8f498aa6310c613f5ab702c4dff285cbcf0b0c146d5b6adcf6310a63184fd601481d4c6ff8399f4c25eb435a6b565aba2d938cb4819f8e52f6916cbdde500b56d42f0315abb1c6d8059160f3d75666d5b3969736500b56d28a0c5949ad67601ebb28556a22d95139c2d89f2d45ace3d3600dfb1c6544f3494e52d67 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part658 : Excludes 0x2800c000000000000000000000000000000 0xd7fd277edd0078000000000000000000000 :=
  finishCode 29 0x1cc6c0f4066b0870b5c05ced67942ab57527ad45ed272d509cd357b4c1c985ce719611e0173b53604a9c2ded27274c0dc3312d6561ad38d968e619ad5dcda4d77b5a28f698e4e4d7587ce65388b00b831872787c2735835cb3f3858725a4385c3d3386b4d663142b28ec18ac1187a692f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part660 : Excludes 0x28006000000000000000000000000000000 0xd7fc9736ed400f000000000000000000000 :=
  finishCode 53 0x1b0681cc6f1f038783358c51ecc17417a8bce6a6d738fa006524ad047c2a1381866d7279ae0c6305e5108f84e5a7116017c1f08ed658cb56d69ab175a0b56e581ad14f6ab21bcd3db3db457e91958cc4f3485b56d88ad614f6ae8907949292f50dad049e6c0359e4fcad05acf3004f338fcb2b39683163889c8b829082f3889c06838a505ed32d8b22d060e393cded29417b4c6f35aba40e5a0a506838a0bce22f82e09c2c870338f9f4e7b4871cde73da4fa6c1b5b12c7b4cc1f4ffa36527a1c71e79b890b8e1ed5b7bbc15d7b4a93decf2485ed2b437289cd479f3164122d5b7b4bda64a0a93ce1e72b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part661 : Excludes 0x28004000000000000000000000000000000 0xd7dca736cd0008000000000000000000000 :=
  finishCode 127 0x1b06f180620a42d0146ce5b46047c20cf5b05cf250519b30a565671f691c84c01a672d9eeaa431f0c6063859ad565a983596527a9247c2735965a983e0a4387c270b692cd516249735ab6a430cdd1815809ad565ae614943c70b9d4c551c8727b60d6d5b58986ec7a68a2c4d652a159476f699cc2a3b9eb67115a8b18b83002e787c271f396a38c21c45cc1e1c2e75a8c5079104f1cc5a6a086699a0c4a0f2d45a670f4e2f3ad4574620b8283ac8b4d0d9ca4348382f65248b9c9633da58360bd173b0102290b4351dcf690d99c6545f3534b370eeded23c385ce2e798473174173ac07b994924b12e4b0a4a0e923da61e1931563270b50da9252c262cb196adad34e168019eb25bf1da8f86730cd3f8c2b0ddab6b13283a924a0f0f85ed2f8308f00b9d70591ed3066561e1a55149c9ce6a982703b58e3ea2f0d2a8d672aabe4e366e1c7d5f33dad436e55500c883da569b356da6328bd8b2a495d1dc4c03c6b2b8956a35524a686b172bd1810c392ae3033da5307b4c08f5249ed66a696eded2c4b5a1acae7b4b00de328aff983ef678398ed56aeb4d7b4878ca1a982c87e28367ad9ee4e6aa497b4b595e0385cb0f6259cd51c60fca3549ec606595c1c5ed24d7623d07157fa9256a2a0d5abc6b15a8ca0d38f9cb561f34cded2b250f1b48b4078cdc527b90e262a8a4bce9419452b2b925ed651e7bda4bce50d925ed5b (by decide +kernel)

private theorem part659 : Excludes 0x28004000000000000000000000000000000 0xd7dc8736cd0008000000000000000000000 :=
  splitAt 1 121 0xd7dc8736cd0008000000000000000000000 part661 part660 (by decide +kernel)

private theorem part657 : Excludes 0x28004000000000000000000000000000000 0xd7dc0736cd0008000000000000000000000 :=
  splitAt 1 123 0xd7dc0736cd0008000000000000000000000 part659 part658 (by decide +kernel)

private theorem part655 : Excludes 0x28004000000000000000000000000000000 0xd7dc0636cd0008000000000000000000000 :=
  splitAt 1 116 0xd7dc0636cd0008000000000000000000000 part657 part656 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part663 : Excludes 0x8404000000000000000000000000000000 0xf686257e490808000000000000000000000 :=
  finishCode 123 0x1ec801b0651980699484a4a0cd90763eb9887f0a36ea3189c300711727c0d372cb5263023b539ac2106f8e56f69066cd4940ab00b518e3a7355a8cf69681c9f2d5d62e0cd1e4834e596ad8b01cacdcf1b8c7c283f83933525ac38dcd5b72c8f841a671d87c2d2398c003341a6f8179e23c80651e2e4f58b9cd58932d5d85ed5b478b93d62f06f9ab69f3727bf8c60b66692bddd056a4339a8f863858f464a2a02dcb2e4f41d9bf6393b28d22d81e304fcd6759dad35ed282b286bda6732a45ce4ea499c9e6fd3939435804e1f0660e4e73559dc7b941db93e735a925603714872d24bceb51524cb3b402a0ece3b393d076e4f9cd6a494159c9ce6ac224be5a8b93dc7ac1741dacee6c1cc7503a7034d98600192d5d8e361c98c0cd5d83d9b9dac682f23cc71b781d44e1685905b2c24606351a4547d67fb396a0ed00b2cedcbe72d7acca1b0a3cd597bbb105a4aa4348a9395ab671f50dc4e54158b64e4e0c56aeca4941587249cb1fee83db58ce227350f1b60d6348ea2f00cd39bc1c5415a0ede039ac80b385939660018ad63963a72b1f0872502b41ed256b83a8a41c2e393a608e0f860f324649de5d748fcd317b08725252b499ace93b7b49cb5a932d4518ee6d0e497347c28e34d4baf24f5ed6aff925ef698c2bb8d230be7b48724e567372e6c70b4a187154572d1c59ef691d6a0d5a438ec4d739ba0ad076b83dde49482c4e4ec1f9a6af69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part666 : Excludes 0x8094000000000000000000000000000000 0xf7c4beb65db3a8000000000000000000000 :=
  finishCode 21 0x1a46520405ac3fb6f03a7149416b378a820ee4909c74a369456c1d0069c51b625ce6541aad25ccb206d6a283b5e160b072500a83572fcd65732b6052194865077b4ce4958d86b548650d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part668 : Excludes 0x80a4000000000000000000000000000000 0xf7f58fb64d7348000000000000000000000 :=
  finishCode 29 0x360f234051b58150283c1d669db984392b531f0c1ce5a6b12cda6b1b50687251c6b0cf6d83982f5476b01598ad4dc8b398502a83f969aa49283b40983783e1598cb4d7b6ad041860d1506cb310e4ad1c1a320be50d93cd7c651077286c16a0af55160521ed331054927ef3dcb90d45219f164866e8c2b07d8b2a497b4967e5038efdaa6a4351acc11513a924fdea4f521c82b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part670 : Excludes 0x8084000800000000000000000000000000 0xf7c72f364d6108481404200040000000000 :=
  finishCode 39 0x2f098408605561a07b4a054e3b395563671b5a6ce554f9946e2929c6d3e72cc58b6b4d292c01022c8f6208525724cb0f7b4a4a4a1a94340da86e735ad3527650d3d142f3075ed29051fda4eda4527c3eb7b4a096303354cd32c5b7b49fd4a4b14963e9cb4d38ebda47f7003787838f4a36525038c72b4f6a8ee724b97ded2ca2e8d241ce622ac6d69a7d31fdacee7b4b8f5c9eb4d3e9a884fe33da569ae499ccaf6971eb965647b6cb517b4b97d28a5bb3f0a93c7f6b498e3af69 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part671 : Excludes 0x8084000000000000000000000000000000 0xf7c70e36cd2108000000000000000000000 :=
  finishCode 145 0x2f0ca2c0f699ab661d314af8de18ada0062c525068b56e16cad5ca4aba340815960aa0d9c9e9ed7bba05545e0bda302f773f0a0fcde6d82c9e38ea0041a24d7969a9eb50db56d076a43786116c1cc5d01a20d383ace43616a835242a4971ece595117441da2851b7acc72b6ae9cae500bddce57356d1933d64e528a2d0a27947682b9ab72c9dc924ab7218efda6eb22055a6f3d6506ab318de6f77511105d1ab6b23c8823d881b61bcb3b724b97c7c2a433facc59724a31e394a0ed42ab43982a0a97bbc7e128d93cded2b579c924d77b4c605a45a1bc5414872485266e820ae5249c367b4b17498b41d4392a4383fbda58ba57f960a5bb506bd6d036f5793be51b3f7a90ded3328b2348be3c861f6f07f6e63180d348bce65063bdb648bbda5c925cd944e0c56313f33db5656b51731cf69596bdb5c9207f721a0630f0063ad362e6bdb6506b9adcb339acde6f696aa9cadcb339aded2b4d58bc9175a6a4863868b6569a3fb50dd181417a00525252130fb48de3c80c55d0a4ac5d83a70739ed2b1d5a6c1b65a68b6560741805307c2b499286b2b941ab3b59dce3d89fab49379ca35962ac371f09495d0731bc681ccb34fd60281f521946c7c20cf531aa338f49e683f72cc8fd069b18a2207e0eb34de0fe821262b93d6a3185941a4c56aec081724ae8a61f8b0290d47735856a2c597a9c9ed0bbbda5896d6137fcc41283aa0c039965958f856ae945680e1f3175867185735ca0147ec1d6513bc0c041ae234b96630a9f9513c6047c2d6198b2e498c09bfe5f0fc727b9ac9fb2c55636d592d59cacde65ab8e56b494e20eb3d95ccaf697abbd96 (by decide +kernel)

private theorem part669 : Excludes 0x8084000000000000000000000000000000 0xf7c70e364d2108000000000000000000000 :=
  splitAt 1 107 0xf7c70e364d2108000000000000000000000 part671 part670 (by decide +kernel)

private theorem part667 : Excludes 0x8084000000000000000000000000000000 0xf7c50e364d2108000000000000000000000 :=
  splitAt 1 125 0xf7c50e364d2108000000000000000000000 part669 part668 (by decide +kernel)

private theorem part665 : Excludes 0x8084000000000000000000000000000000 0xf7c40e364d2108000000000000000000000 :=
  splitAt 1 124 0xf7c40e364d2108000000000000000000000 part667 part666 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part674 : Excludes 0x8014100000000000000000000000000000 0xf7de9cb7d922ba228200000000000000000 :=
  finishCode 55 0x1e4811d46914c1fdb184fd1e7cf752ddac0609bb494e1acc2d46616b9adcca835588cf754f48d94462e6b732accdaaab8290c61601bd9ab6b335a4ad0a3d96a20a327ec5e38c1ad454c161cd5b5809bfe0e72c6dcca1bd6adad466ad979e7b2ad35ab67d3491785f0586ca0f3da7f30ac15683b9ab6a13588ca3d061ca3b6914c27ece591e786ccec49cca4f592a0d66adad466adb18de34871d83aeb8460e5a493f56a20ab50bcf7162693f5ab67d36b3c0b127eb0d66adb575a664fd530e56922904f38c1c1bd621b56c57ad5b879f1bfdab61bd857ad5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part676 : Excludes 0x8114000000000000000000000000000000 0xf7cebdb67ba2a8000000000000000000000 :=
  finishCode 11 0x1ac751800698fedab73da56a61c948ccb4d6ada505bc6616530f3ce6e0c9594c3cf394a5060dcad4d4532d4ce3a3fb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part678 : Excludes 0x8016000000000000000000000000000000 0xf6dc95b6d942ef000000000000000000000 :=
  finishCode 69 0x6c14c581386609e6b8300ea0725bc5f01a29ed9edae652f1b95562e7028865a6b955a7723ad1c04dcf69598978d2565cd9636b17836ad36510826dd44d01a2c35982ae496b0acc457ed33969ab4d8136d358192ee24ad622b3d724cd2160bb9bd49e09d8db2d2330c20324e6f0af54360c3731ca13387a93e58883456a6bc2e0c2b96220a5495ad4c392d35969b2c5dcaa6ff50db780c9969a1bf39b958a2f982eb1b47125e92b9ed2b532f1b51c36741bd632d2328c00325603c0392b4d8b9ab17941ab2d62eb1762e682f569ad33969aa3b986272b0688726611606501528f59a66b4d6ada504386f699c86c33696a5059439bc2bf2f1ad34e573e8a035964f6ac55232a2949eb53e36cad5d622d5b387969e521ac456aea29 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part679 : Excludes 0x8014000000000000000000000000000000 0xf6dcb5b65902a8000000000000000000000 :=
  finishCode 111 0xd8310a6146cac283c08b0558dacbe60b8fed0360bd9486b192f3c08ca06ce5a68fed444920df3da5a8e7eb40dc1ae379a0d5a8ef692f3ce43514bda4a8727c5cd597bda417b290cac4f1105e160ac2f62fb56e5a6872469b355428ef6560aac1d60723cb256a68fed60ab07598cb4760ba90bc300d3f986ad5d58d8fec3928359a66b476adad1e616ad4525ed5b9edafa349023a8a20fed606adc8355a8abe66aa9bcd8baf69583cf69583cd67412ad4d802e6ce4f57cb98ded21c948ccb03699ac1e0e496d65a9b51ded2c490e4b28d5b8bceb4d1fd9485c8751a460019a0d35a4c0a100cb55562ed61954511501e1ab7399562eb2d6adce655a89ee5c9ed255a1b58541b41adeeab3372cb93ded33995cb3286dc92ee1e0a21879ec1704dacee0f2a4f514988e639c9e5a569fa8ed1fb25141372584a79486b434f68204772e437328f3ce06120f2a3b9abad55524cb439aaad2308fa2783fb371c82f38216724b0bd6a28f99c9307940da0ed41b1fed6228f1527a0ed6032835622b2541dad459865039f02d58973174bce83b513cde300cc1435f42e130402ad5e387b5952331c3d6932d46303290c13a8054a2a8ed452d5b9c868f1042805c032b11387cb3b5a8c8054f0a1a6c3941ae492f3ad26 (by decide +kernel)

private theorem part677 : Excludes 0x8014000000000000000000000000000000 0xf6dc95b65902a8000000000000000000000 :=
  splitAt 1 121 0xf6dc95b65902a8000000000000000000000 part679 part678 (by decide +kernel)

private theorem part675 : Excludes 0x8014000000000000000000000000000000 0xf6cc95b65902a8000000000000000000000 :=
  splitAt 1 128 0xf6cc95b65902a8000000000000000000000 part677 part676 (by decide +kernel)

private theorem part673 : Excludes 0x8014000000000000000000000000000000 0xf6cc94b65902a8000000000000000000000 :=
  splitAt 1 116 0xf6cc94b65902a8000000000000000000000 part675 part674 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part682 : Excludes 0x8026000000000000000000000000000000 0xf6fd9fb6c9535f000000000000000000000 :=
  finishCode 27 0x631643b0e5a73568144e2d3945e3e15abcc4f6adca1b0e482a538680e3eb0581a281191e2d0330d82d80d1588cc17356b58d8be0c336b830e7b4ac9d105a6cc47588cd39255978582ed2f05b8f8650dad35442b531e7c83f50daf86630de59f9c2cbc2a4957fa8bc9e6b411f0ca49960a801 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part684 : Excludes 0x8006800000000000000000000000000000 0xf6df9736c9440f740000000000000000000 :=
  finishCode 65 0x318b8238cc1c0ce3ee42280c5593c9f37359f55ac21c33e9b06d6233da49e716ed69a7d3483a7cdab64c58dc6b53729c60c766b4d279b307356f16870b3419ab1b8bda0bd355ce6b83fa8bd46ab1b44074601ab6b22487195a6cb15279a41e626ad3419af5b9636b1573693ce0c3a4906f949292f50dad049e6f7596367196f124601493354525ec2b58aad056c6c127ad479c726912798e9e348bdaded335349e698033562f04a5826a210e1ac6d6a64a596221c3279c5ed5a0a30b217b56c6f125692f6b1c70b066a37e385ac5d04651ed339960d63b5262b10d8b6e4f898ae43819af695a0b9bcfaade170902d363eaac6c71ad5b6b1b3014f9ab6b1b3eaac6e60bd06b5ab83340c26e358bc00d1dab56d636d02480cd5a6ca43279b04e6a3ad4d63609989e6b15 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part686 : Excludes 0x8006000020000000000000000000000000 0xf6ff9c3ec9410f3000d0400300001000000 :=
  finishCode 63 0x3a8c6270cc1cb4e23082e8a0d96864f3499a306d79ed271d72cc0d15a1c0d1727c611510a90c0260735741a06c18832c9d602b3159698441a2d398c229219ed290b596ac5e7b4b9acc2271d91e6b17596ba0d027ce727b8f5ed271d485b05d2820d13f7c90b380a504e0311a53fe883a0d5b5921048cbda68c18b651d6821698ca1b62fb17e380c60646cc208c2cb63878b661e7a48582eb414ffad0d4373a0b0340c02483e1068c4e9517b165492b155a0a7b66248344c22c599ac29ed69c8344e569ed923318361bac54c22d02d5672cb93c1a2e599cd6b4138dc72b308ba0b62c0d018458833524fc2e613958f85a932505ac6d49925ed63395b54e1f0a3ce500b165476611 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part687 : Excludes 0x8006000000000000000000000000000000 0xf6df9c36cb400f000000000000000000000 :=
  finishCode 105 0x2f8bc220629315b40b4d6f1cc39ba60811964f07158cbda5ab6b1b736d071588b4e5cd60c35aac4ab38dbda5ab6542d16388bda5c9e069524ac15ab66e78de69f3034a92560a7e356e50db9b68359f4e0e2939486c1cdab68037890340d49068cd3939bc1ae58a891e0e6e55380ad553e71cac1a27e300ea1c7e5ab82f562e6e7941aa492e6a42c17a9605ce0c39b646ce711581b586379a35d6572834dceb05486ac6e061a98de187d98721d4062b00ba2cae62ca47e0e6b2d2798b65ed32d5e0dac41920b073627c6e75a6b524e1f030d1c74168e11b946a8fb879e0259636b17510ae108238e61b9ce22c178b9a91f3f8ad4c30b398b1b91f683f71ecb572dac9f9596a35d44271f5a6a926631bc721d4062a70d4f96570735ab9cb4e22c02cae490ad5d69b460c23e917699b9ae373a8ed69ad63387c0c347110388b5362e6ad35cd72d4d4025cd485c4ab5069cb5d072124068b9165a0bdb523a4ab92333db4e1eb4d395cb4d581785c1ab661d4c1ed30f25062f698e6e82f59bc7377b4ba0982e0a60f85002831968ea435a6c8215a38344dff2d35442a43417ca1b475ad34e320d158dc735061ad358c5c0186b1b900290d410ad3662dca0d48eb56ce56b4d (by decide +kernel)

private theorem part685 : Excludes 0x8006000000000000000000000000000000 0xf6df9c36c9400f000000000000000000000 :=
  splitAt 1 101 0xf6df9c36c9400f000000000000000000000 part687 part686 (by decide +kernel)

private theorem part683 : Excludes 0x8006000000000000000000000000000000 0xf6df9436c9400f000000000000000000000 :=
  splitAt 1 119 0xf6df9436c9400f000000000000000000000 part685 part684 (by decide +kernel)

private theorem part681 : Excludes 0x8006000000000000000000000000000000 0xf6dd9436c9400f000000000000000000000 :=
  splitAt 1 125 0xf6dd9436c9400f000000000000000000000 part683 part682 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part689 : Excludes 0x8004880000000000000000000000000000 0xf6ffa73f490c0d346440000000000000000 :=
  finishCode 13 0x6507f720eca425255d18428db489820edc9f27ccfc2a4347cc28b8c1acb4ff672d9686a49524cf5b0b68a3d676f041fe1f0acb4036d27729b4e502a83b388a056 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part691 : Excludes 0x8004080800000000000000000000000000 0xf7efad3f49c90c183440604040000000000 :=
  finishCode 19 0x1003c051b292ba8b498fc2f69388a8063959bfe3f0bc0ea2c89c300a4f9492f694129cb5ed32094e22921961eb511fdbda569b35652667017b4ad8b4d8e6e815904ab4d415ca49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part694 : Excludes 0x8004080020010000000000000000000000 0xf6efad77e9290c18a0c247022c101081800 :=
  finishCode 47 0x1745318059130781486d59965293d497a8d4e4ed59946a93d28da8a66ae9cd502b1c7e302a1b28da925886f17828da5063739c4502a71196440ac6067b4c1fd01693d83fcd5969fce6b4f9b56e30683b3fdb30bc3a8b234fe513a4f6306f69396a0ed18381c71f28da05550625ce4f506ad5d2671819192f6938fc60628da055d46016af0b64e6a8e46067b4c1d5ac31819ccad25255946d142e6d1814a2b945aba72ba3025cd7289ac544f3574e4ed2528dad8b2356e39ba0ed68a941841cdb3915cc615d8c2a055ac27377a9c37f8c29b2565ad61415c83b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part695 : Excludes 0x8004080020000000000000000000000000 0xf6ef2c37c9091c1020c0410204001000000 :=
  finishCode 117 0x52130740c22f62e8c4400b213f4a36b1d895673549ea311839ac2d59255ad5cde6b579e0381c71f6acce5762ca92527aa2994771811f09cd5486a6310b22d5e1f0b13d8b29415a4cf53620b16561f31656ae3e18c2c70f4a08f85885b0f860127ae65a302b434f4a4bce6b1819cc27296012827d18e52a015279cd549f1ca51c631e08c2cb493e89a6561ea4f39a95f64059684d32b494839c2e2be9cd62d0b18ea200735386c09b72bb91d6928f962cad5e2ceabc5cc6b513e89bc5016c41a30aa2951dad256871c2d8c601e0301c9ee6b39aac565a88ea5ea716560f2b577b49c36627ad258bb41d630ab25388ad45cd71c3589eea3009c1cd61038f9fd628db574feb3dd496e4fd8c0cb2d37188400e03242d25ed2996a2d5d28da0ee69fad44ff6a15a0f6b1359d9c4574590f051142abc202d676a1b9ac6e5741db9665a4946e83ca504d8621a7ed5d41dd07951dc604e0283ba30294583ca8ee30320eca36d29380946e500b574e0327a5ac6b3b80174621386009faaa1c7e5abbdde58eb56ded32ced0166f309dcc1162c9ca6302d5b28db188a1d8d2289ded31c34ff6c3360fd07f5969cb630ac339c8672d6ada8a659d9cb5eb741ad8c600e22b3387c2b2d7b4ad5ded32ccdac30f8580551ebb286ce3e72d5316a3307d4769ff524bdde46fa287119ab6a3b724d1813f2c1ed04a711 (by decide +kernel)

private theorem part693 : Excludes 0x8004080020000000000000000000000000 0xf6ef2c37c9090c1020c0410204001000000 :=
  splitAt 1 88 0xf6ef2c37c9090c1020c0410204001000000 part695 part694 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part696 : Excludes 0x8004080000000000000000000000000000 0xf6ef2c37cb080c102040000000000000000 :=
  finishCode 33 0xb23a861f315ae8c00fed49f1484e6a9199476a4f5abc0c5388b10de358e578ad4418a5251f0c90749ead46514a8ed60800c52de13f67b4b59d6820c3292ae8ea13f4e232d45682b51941af672ca9bcdc8b460588318559d8624e22d034be6aebdacfa6f690609c4418ab1d93e7003005255d178524b5665aba83417a815379cb411cfc9ed8c2a05562b1859ab26f340abdd669cbda54360c3 (by decide +kernel)

private theorem part692 : Excludes 0x8004080000000000000000000000000000 0xf6ef2c37c9080c102040000000000000000 :=
  splitAt 1 101 0xf6ef2c37c9080c102040000000000000000 part696 part693 (by decide +kernel)

private theorem part690 : Excludes 0x8004080000000000000000000000000000 0xf6ef2c3749080c102040000000000000000 :=
  splitAt 1 107 0xf6ef2c3749080c102040000000000000000 part692 part691 (by decide +kernel)

private theorem part688 : Excludes 0x8004000000000000000000000000000000 0xf6cd2436490008000000000000000000000 :=
  splitAt 4476 119 0xf6ef243749080c102040000000000000000 part690 part689 (by decide +kernel)

private theorem part680 : Excludes 0x8004000000000000000000000000000000 0xf6cd0436490008000000000000000000000 :=
  splitAt 1 121 0xf6cd0436490008000000000000000000000 part688 part681 (by decide +kernel)

private theorem part672 : Excludes 0x8004000000000000000000000000000000 0xf6cc0436490008000000000000000000000 :=
  splitAt 1 124 0xf6cc0436490008000000000000000000000 part680 part673 (by decide +kernel)

private theorem part664 : Excludes 0x8004000000000000000000000000000000 0xf6c40436490008000000000000000000000 :=
  splitAt 1 127 0xf6c40436490008000000000000000000000 part672 part665 (by decide +kernel)

private theorem part662 : Excludes 0x8004000000000000000000000000000000 0xf6840436490008000000000000000000000 :=
  splitAt 1 130 0xf6840436490008000000000000000000000 part664 part663 (by decide +kernel)

private theorem part654 : Excludes 0x8004000000000000000000000000000000 0xd6840436490008000000000000000000000 :=
  splitAt 1 137 0xd6840436490008000000000000000000000 part662 part655 (by decide +kernel)

private theorem part648 : Excludes 0x8004000000000000000000000000000000 0xc6840436490008000000000000000000000 :=
  splitAt 1 136 0xc6840436490008000000000000000000000 part654 part649 (by decide +kernel)

private theorem part636 : Excludes 0x8004000000000000000000000000000000 0xc6840436410008000000000000000000000 :=
  splitAt 1 103 0xc6840436410008000000000000000000000 part648 part637 (by decide +kernel)

private theorem part608 : Excludes 0x8004000000000000000000000000000000 0xc6840436010008000000000000000000000 :=
  splitAt 1 106 0xc6840436010008000000000000000000000 part636 part609 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part700 : Excludes 0x28001100000000000000000000000000000 0xd7f764bca87850222200000000000000000 :=
  finishCode 57 0x3b8d02a0a61cadd438db02e0de93f56561e359dc4fd7507bb2c74ffa1e3661a815ab0965a88f75a97167450a38d26bad440fb27a630ac55599ad258c6d1d45303a6b61c6c24f350dab27fd59d97ccdc32ccc9fae6d61dc6d360dac747bae6d8b931876a1831d64a4fd38dcb2549ac3d32f993f5d465169b073c3c6e42e8942f0cc3f8c4b5a1c7fd2dd93258b3461daa27fd0c3ce3b83eac1cffa5bb5998b9ded331760fac3b599acce27e9ff658eb5761b98b9cdc5a4c4fd5a88ad659d8b9db46c174398b504fd476ca2b8c3a89507aa3991da0c7969ab516a107b0f745ceaa251e5a69fcd2272d356a31cc569a6e3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part702 : Excludes 0x28009000000000000000000000000000000 0xd7f647fe3c5049200000000000000000000 :=
  finishCode 21 0x3b8d435884033d38625cc5d151b084c98e1a81d39ba910718fba4d740ec1be2d1bda5847b4ad862f8e6e3dd8b46e6d38d98956416ec90730c935c7bb168e0e2c4f30c9ff67b49cac5bb1894e5662587ba731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part703 : Excludes 0x28001000000000000000000000000000000 0xd7f6c5bc285000200000000000000000000 :=
  finishCode 155 0x3c8d8328d01495fc561203394ce3a51130098958c317a03e5a69ca56767298d6b2d24e3a5110f1cb3b398accca22d0146dfc312c62f3fecb49067a68ac2c758ab41d47ba60b9042b577b4cd65466b1560eaca350ac2d050d2e1b45a6ae8a2f83c63dd41e8f760f196ee6b3aceded23dd38d8f7641eb68ee358c298f56c2562ab1643b62dd61169330947a6f698bbb3154b772c95ed2b2b6d1dc551a05d0c461d387968237adc27f466c1cded271d39b96fe380a76d69aaf11e9982c3a7078d69a62f85ceee2c96380b13ce527ef96769115a6bf8b60b764a39fbd69a62f300c2dd5a698943a71c745baac3f8d028071b926aa2f3009865306d11febe1895687352dca29357b4cd655248f7546b39456a26e17b297260df460524af651ee9895846605cec5998aa8ed1ee9ff65069ac5852b43580cd655a1bddd084e1a01eec1be26b8515ed26d3510a48d26a2c991dac55381486b51a30ef694a3a8d60eb1fb52467299ed2d0368921ca4c5ee6f9ec2b575038b0cf5f2c960e2b258e3a7019852b1d7b09ff45922e7611a05a13039bb283dd38da046067ad34fbb41c4bbaf6d517a045640679d82dd252cb57264935cffb1a4c7bb0712f4ad0e7288f75a85b1b06d018720fd01e0cf597ca2f4189c753426bca1b09eb05c78ed2d6a39fbd25671d4b10c1e3ce513f797a65a0b945437395db016eacae067acae26b9c766c1405e16c398a60941417bdde620ad0d06270189e690b5abcb1361493cd6c418cb4d4a0b8e6625c1bd20eb2b59fc4f362c9b4d05eba2d07e1ff503a2a38b7636b8992aff09fc1bd896b63da661bb94540e2bd1e7b106620c3cf7b49ff5c868164067acae257ad5cffa4d716ea607e292660fad0d45eb42d36736a32ded30711ee9a5660fbdadeeeaff838ad0e728b05deef2504fdeb2b837b13cffa80d50dc70f (by decide +kernel)

private theorem part701 : Excludes 0x28001000000000000000000000000000000 0xd7f645bc285000200000000000000000000 :=
  splitAt 1 123 0xd7f645bc285000200000000000000000000 part703 part702 (by decide +kernel)

private theorem part699 : Excludes 0x28001000000000000000000000000000000 0xd7f644bc285000200000000000000000000 :=
  splitAt 1 116 0xd7f644bc285000200000000000000000000 part701 part700 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part706 : Excludes 0x28010100000000000000000000000000000 0xd7767cbdd02a52020200000000000000000 :=
  finishCode 51 0x348a6260c61c34e36b63a89e24d43969019602a4f698cd25580b4962f9a43e692a93c18ed59928ec4328c63a8d5d87a68330e9b30b6030da87284ce6ea3d94261bd51ec7378fa6d5b1e9a08d42741d4e6ed4327eb28a3b83a67314f1a4b17cdab6925527b49662148751ccb314e0fa3dd3959ff507acc28f636cb0354260c71eeb1565009cad47a72b994751abb1cc43a6a3b96032855aba8f165188571483989ac658382b58461bd41e8f755e3359decab0741ec3dd692cb2d513abc5aba73127ecb490cda495ab6947 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part708 : Excludes 0x28012000000000000000000000000000000 0xd77c5dbcf14249000000000000000000000 :=
  finishCode 21 0x3e8c22d8a2998922dd4a083447ba72b39bb309c22892790660d138da4e5b01eec61e6a88ee45ba2d941ec83381a271b527c8f14198344e36e42900d11eec81d2f4c2dd387bda4e1f3904f38e621cd0e3cb2d3e79cc4dae4f3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part709 : Excludes 0x28010000000000000000000000000000000 0xd7747dbc500200000000000000000000000 :=
  finishCode 151 0x7b20c6c19c650a36da1cc4a428f99edad4f30bb59e691d47215406bb189115415f30efd266b0f49cbda6521ac3c79e9d99602c31386c8f1692aa89e260617521cb436a8a3e6692826c79ea1b9aa2d255a1b496500c2f0798d6ab0f8c3a8a549e70d8d6aa1349c985e06bb28b62d073128bb08a61b8e5a69cdc7bb20ce5a6a3f51fb1c7568661ed32d34e621cd59fc7cd06b9cc560341e565eb4106bb90b43e81cd69fd1874f4b50dc8ec1b3958f74e529279a86e471eeac566ad9b6522a0d7694a8060399cdce1eca2b0c02d050d7f1886d0c3320f4e370f75a9b23fd64a1e30e9cb4940ea4965abbdac3c693516eb68901969af69317878d24b2d35ac6203a68c1ca564b1f3d6026d95a882de6adb97c35e1af963a3bf592ac9638eaa8982f8c424d454b461dec2b255999c7477f0b0e30e617592ad45c8599cd2d47f8f754873086e1894c2ea4fa0e29258c3ad25edaa29a0f29255abc353509a3e5eda70f5a4ab0fe3689eb8f6b07583ca93cc3270d947b28d410ea2f721b994e572c94e1ada352e5a6b0c4d6af6959dad44c3261706ba80d83307315a15fb1ee5ab21cd16c998f699ab6a077b6a4e545eb411dccb43365b56dabb1c7568670d6216a30f1ce1e601592cd2300a822871d945e71b5aba515686c0e6eb579ab706b5aa8b6582b3da60ead555a2cf69524b51d6aeb4228d4f969ad5b503ac3ce36b0f87ba6b1940e4df8f56f714f98f1daced5b7bac6ff7b6b56dd46b1fc06ab106d99676619317b086e185d080a9c8f9623b59dccaa2758eb06e0e5b546489a609019a964ef5a4cac32872996a2a29277a0f45ba9479c863dd0e5cb2539bb08d241f63949cacffb2074c5ef698ffac41cde1ee98bd6270324e62617 (by decide +kernel)

private theorem part707 : Excludes 0x28010000000000000000000000000000000 0xd7745dbc500200000000000000000000000 :=
  splitAt 1 121 0xd7745dbc500200000000000000000000000 part709 part708 (by decide +kernel)

private theorem part705 : Excludes 0x28010000000000000000000000000000000 0xd7745cbc500200000000000000000000000 :=
  splitAt 1 116 0xd7745cbc500200000000000000000000000 part707 part706 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part712 : Excludes 0x28080100000000000000000000000000000 0xd7f77e3ca428d0100200000000000000000 :=
  finishCode 53 0x340a6260e61c34e52ca1cc60e9aa0c624e49af0b653db4615a7ef6d262cb0169fa93d546259b4e04fb11528ed219692b4d692c1d5882c4360737694c0c5527a85d05b2d34fe71818da68f149cb50c3763d34d188650e56a39969a731513a0f5ccb46060faa4f1eeb98ca1b4e398874d5c8c0ce65489a4e4da72cae493ac75202e4310840f75aab461d846c55369b994ffa80d49cc4c5732bda418eae300a80b665abb4ed24ef699a7f18502fcd3f6a1bda56571b4da7735857472138619cb4d0e9b12cfc0e98b667b496ed2433da544f3574e621d36add0756a5b94cffab4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part714 : Excludes 0x28800100000000000000000000000000000 0xd77f747c82a851000200000000000000000 :=
  finishCode 75 0x3b8c4340d2298d5b96920c54169c6ce6e9a2e872b75128ab499402c5559586467b6b154e62a3d500a3c56a3031c3b6b4d9ab682d1eeb98da360d4280ac1cc5ca7280549ed5d0de8b9e5b128173b56e26b9ac6509ac55ab66ff0decb41509ca27509c5f35138b9cdff1bfe40ead35a4731b0500c8527876ce62e6d829e04f69aa805692c250dfcb07729ad256c3f9c1db380a3c661dad043b61db944f356d69a2d9419a08e398b56d69ada348a3b96a2a4f0eda89e173ac3e571ec5d10839128a4cb9eae3af398b56d69ad42907ed9ab60b140e8f74e63137da664df8e62d4f058b60939059c1bf3988e9e6adad35b0440e62b379ed2c0d173b56c18f240dee3353dab6b4d264cc1b7b49cc45ce3dd6a1884a1837395564a2e71ee8b9e587c0179a76b49728b56d69ab25 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part715 : Excludes 0x28000100000000000000000000000000000 0xd7ff743c802850000200000000000000000 :=
  finishCode 89 0x1dc6901dac81c34e36800b5639897cd28ec4162ca789a293e0bfb56e527c1e5cb70f4dab6c45751544f5c91139a8f4e0eb34fdaa21cb0bfcb49670dc520dfeea4616627a84ce326fd500b9aa3d949ee3b9ca716fc5cee635071998b2937173a89e398a48e4a3a0767acc614992d330be9cc547a6ff731b0501a8398b68b62a82e7631d4587cb434169c7ce6ac439561eeac96045a0f661ead5cbe670b58b8d7e147a7bcf6b18783eb06d64ab491eeba8c41c2ce4e34d8d62f776258f750670798d62e65583c3dd2e4c4fd371b10f606866ad93f5284fea4dcf57165456706b92267b59ca2275044ad34dfad42d8da1e82e7053ce6f1d5ad25046a2b526ba89038e5a4fd9caad5b5a4a8e637ec7191eebd8b4d967692527ea4de6d1486a188173b8e66ad9c655e23dd4069b165a6b56ce4eaa24966ada51cfe6d678dfad4d85ce5f338cc6e3661886907bac339a9a4fd057a5155e3244d1d72d3589670b401c70b (by decide +kernel)

private theorem part713 : Excludes 0x28000100000000000000000000000000000 0xd77f743c802850000200000000000000000 :=
  splitAt 1 131 0xd77f743c802850000200000000000000000 part715 part714 (by decide +kernel)

private theorem part711 : Excludes 0x28000100000000000000000000000000000 0xd777743c802850000200000000000000000 :=
  splitAt 1 127 0xd777743c802850000200000000000000000 part713 part712 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part717 : Excludes 0x28000040000000000000000000000000000 0xd7f5dd36200285000008000000000000000 :=
  finishCode 73 0x7d1d47f1bc076b60701387b98a61cc53ff207d47ab2d50dad5e38fac816b8e069194a0a7ce3819c46485a77d282b83183d98e6272d3818d9651aad04b22f693799cc525f1cc49e66f36a1e46f19c286b10c21495a0127c5bb7b486ece6eaa1eae2ddbda4376f699c867ab7b5a8a5ed3398d81c3662c97245927313f1ce476a3874d42735858b2b41cc4fc71c04e56b4d1e9c6a149178530e629a141c12f17247a60a19a4aa299ac2b575307a71f8d45e6f39aa27e3379c2dd680e630ecd6826f316e9c3d4531c04e031c752331b9ce6270139583b5e46f1d428894860d72cb5ed2b57492a4d4e6a61797838fc2e7398ae05dd90427355a0c9f33ffb95d45ea6248b57825eb136ad9cc47c282f36b93cce3f20bd062983183e14ffc6d77b6a085ac272d6b0cb575a1c71f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part719 : Excludes 0x28008001000000000000000000000000000 0xd777577e1c824028d001000200000000000 :=
  finishCode 75 0xfe3c8e6308b63506170e5c13b83ac6146d672759298bc5ceb830062f69ad18559d872cdfad339823244dab6b81bf63939895646a1dc83e9c65acf30dded6a29513a4d6698bda507aaa1bf5ab73dad8469019aa2d5b1eec71b41ec1f5ab6c4352e39a9c44c32e6593d6b3b7b49c9d88587cd5b5a88b747ba82d600e1b0f4cdde7275a8cf69578a7ad896d42909c306e38ca0f47bac241e639a9c6ce6eb2250639a935d10623ca01838b56cbd2f679402c173f1ed272b6b2c70f2f4c72b8ec451a426b9c89c306e619a60883da4e36a4f964a91349ac7b9731b52d07b3da47a63d3905a71b1eed18183e9b4d03aa27527a90ac2e03dd5005bac3b9eca08d5a89774e6f24966ada60d41ca5ee32074b5702c52225bf834e83d83ac9db3949cdded2ac285547a7fd39bb56e2eebdde (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part721 : Excludes 0x28002001000000000000000000000000000 0xd777d774a9c801285800400200000000000 :=
  finishCode 131 0x350ca2205c1c8b82d35388311fb16eded28cb38e8b74dea71f6d1404d1645618630e6d2329ff6a39c745a24d790273da565a71d47ccc2f2e4b51d2826cb923a9ff38eb584d9702dded2d2d38ea189217b4a3f662f8f1cfdec4f9a668fd6adca42d0da1a462e4b585caa7371eeb56cffa81d6f1144b0e365c98dc65e938c9fb637182de6a39cdc7ba73596ae3dd5c1b439ab58605bad5d27ab43816ed5b595b56e550fc0ddc7016adad5cb7f1cde0de72d595a8360e39cac745a1ab6a4177640ea0f58459189f0e9c38e7370d9b4d67b3bddd5fe0b762ccf7734a89f5ece5e91cfa287c204da048cb0668c09bccbd306f98b26cb046c6cb50dc7115a1a5b3954e6e3dd3fea075805abc71f39ab16661ba7ce0e639f7b4bb88c2d8de242e388a04d03a701387ae083d96aea1b16e9c4528331656826f3551707f1ecf2d0ce6a83d96833dad65a09141e9c6e60f8f754c5c1585505ba735902680d0c7bd9e406b4b63f6acb5882d61721aa8ba359e1cdb07c1261af696cb411cfbdae6a696fce36907944e72d55075f3dac7baf695a09c7c9932bfd03a93d1eec18fe290aa2d870339abda66adc1bd65ac17490c4697bbac0545eb43728b68b228f65279c9d98625c9397bb9324f5b39bdeb6f7738d9c6e513cd5b732bddd82e71f1e79c05a0610e370f74e6ef5b98b2d5b596935d744e165b24cd28ac4fa0e27fd4909ff661134696c4d738e9cad386adc7fd26bb4b492330c5686e5726b9cdce08c3cd65596ad0d862b2d9282b570c9c9390e1b555ac271d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part722 : Excludes 0x28000001000000000000000000000000000 0xd777f774088000285000000200000000000 :=
  finishCode 105 0x3b8fe2d00e507682ae58082c4beab4d416b0098170701f0a0d51aacae8c0a4f56ae933897a6a368c22684a204d847353d676f699aceb517b882dd6573dc416ef71965a5c99ea65f5521acee2faad5d63b051d65b06d521ad25ab6b438beab83da6365b53d026b516adc1af7b4b78c00375882868f76416b0b6578c3dd619b10a42f0b80f75ac6814433d84b9292349a8b75604d059209396a2b2d98b2a499747b4a37e599a86da8f24d4f6ab33612bda66d1ed32d356768130d7c2dd0bccb3b835b09526ae430d7bda5b454178721cc59587acec9ae803961f237d8bb316561f06350b82a8ac1c7ce5a6259492b432faad36317aced6c6d0a1af699896d5557c9324c5e2e759dcb1d5a68666493b56ded2a213938f75585b11ff182ca1acc2203dd5a6cd5b5abcd3535ab59daa217f524bda51e335367b8ad352222e76d1546adc6255a6a51cc2eb83105dd8c5e4c998beb4d041c7b95a6b56cdc371cb4d6ad9c8d3ba0e21af47fbda528eb4d3f7c9130ba970e62d3524560c16d41805ab73dc53f2a491cacd656ad9b8e6ad85d5676d618f7239559d9724c463dd96a30e7c366d5b (by decide +kernel)

private theorem part720 : Excludes 0x28000001000000000000000000000000000 0xd777d774088000285000000200000000000 :=
  splitAt 1 121 0xd777d774088000285000000200000000000 part722 part721 (by decide +kernel)

private theorem part718 : Excludes 0x28000000000000000000000000000000000 0xd7555574000000000000000000000000000 :=
  splitAt 4344 123 0xd7775774088000285000000200000000000 part720 part719 (by decide +kernel)

private theorem part716 : Excludes 0x28000000000000000000000000000000000 0xd7555534000000000000000000000000000 :=
  splitAt 1 114 0xd7555534000000000000000000000000000 part718 part717 (by decide +kernel)

private theorem part710 : Excludes 0x28000000000000000000000000000000000 0xd7555434000000000000000000000000000 :=
  splitAt 1 116 0xd7555434000000000000000000000000000 part716 part711 (by decide +kernel)

private theorem part704 : Excludes 0x28000000000000000000000000000000000 0xd7545434000000000000000000000000000 :=
  splitAt 1 124 0xd7545434000000000000000000000000000 part710 part705 (by decide +kernel)

private theorem part698 : Excludes 0x28000000000000000000000000000000000 0xd7544434000000000000000000000000000 :=
  splitAt 1 120 0xd7544434000000000000000000000000000 part704 part699 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part725 : Excludes 0x8480000000000000000000000000000000 0xf6876d3d240000000000000000000000000 :=
  finishCode 77 0x80188651ec6b17417aac0e4144503728ace6251706ec1ee3988faca4b03747d6af18e62a3f380945c1bace03763809444a4af0206e5a69c0500a73106e9bce38e945ce63245ce5673717ab98da358d03a8a803541bab278d323e18c08b05ab672b722c1257bb9ee5ed27296ada0ad845309772c6cbbad5b38d8764e52c02a01d96adcd634089cacbbb2cf566341d58aad2959e9cac97304c507e51b06ec7d180f2b476068f15ed272b39b8374e6f0374a370765cc398c8011f5945c1baba1485844a2b966619a0ed85b290dcbee598c3cd5b71eb93c7c2e4398ea3d80cf38ece53353ad24e623eb06ea0ee6b1b56ce6271b39bb2081f8e521d5064b08b519ac681b3949cdd6a33c0bc3dde62eb56dcbe4d741d87555c6317461128aa43989718148a8fac18b2be522aca240e30b2d2569a4e58c2c7e18c2c7e1481a90d5f34605ccad633f0b0b49cab4d272cc21c3c3a71cad4c83ecc37165c1f6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part727 : Excludes 0x80a0000000000000000000000000000000 0xf4e4cdb4455000000000000000000000000 :=
  finishCode 155 0x1003c0f8390d807d5bc0eeae8b43940e2d3279946d7806c9f364989c55ab6b4d1faad066b18efdcca6d39585a1bc1faa5050d60dcb17162ad35262e599cd6b4d51d86ce610a1a6c9967aa212f0a90d06aa2f928ee3d6adbdc5a4619cb4d509b17438e1cf3b076f316544e90da0dab41732ad35b0581e45e09fa5255a6c1b941aac6e2ee8f8568ed0308a02d364a182e47c2c62d1e05ead341867d5969af6d5a08f265a6a32d686a0d5a08f8569b24ed45eb1b9202825292bc8d61435680e7b52605b9fbdaa6b4d4edc90d40d9b2661016f2d05286b4d9b0670a0f244c7ea947398946d68625cc5d28b87347eade1fd67abb50daaad5b06b9fd66f1586707ea50d724c935838cc0d3e7b8f4bba7f54919c40db92673282dca834ecc5d34ecc4b671ac593cf6925a82ddc9302d630f317522a8359e45e0a1ace0fd5a07b4c51b4fca4d507f146d056c22a08151c7cc1f62cc1c5cb26c3629b55589f396519b34951dec59838b8f500320fd202e3d28db90c60fd5b0067cb4d417a0c5285a6929e4a1929e7b4ac55252a2f9002b414f9cb435218b1568283f6c178651ac6f184720e620c30eac3f5491c8257b2c91139887541771785ab69474028754e621d5904a731067cd592f0a0ec38a9350eab68d62b00c3067a086510939542b2d3545f2d4cdae0d985130441486d5d94424e58369fc5eeb13960db286c9b73d5c5b2bc2b0c239082b4c07ea1cf928e2c9606d0734ff873d06a34d9ac6d2d722a4d4592b42d361fabd96492bdb5ab6ba206c593073dab7354e0da2c9561084909cac2368ba302d7c7b4c3bb7b5a86c39f1878326d2d03aca1b80d73dac512a1b03ac1b65d167b24e439f181a0db01cd86e1cf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part729 : Excludes 0xa080000000000000000000000000000000 0xf4c77c75040000000000000000000000000 :=
  finishCode 153 0x802106503eabc3988c1cc5a840aa0945932d454226297baca4d0c4a3b507724dcc52a218a562b0f95076b4d902ade2f8b2368ba2b8ea06ec5b32ccc3a6a3b818ea15818e1d3735a69181947eb4d5a4990722c3d42ab4d9ed2169874f187369b94e587987d69b2c745b260730fa389c30de350874d8bab49515a8fd4c50bb68c29578ce6b7b4c07b1dfacce5d1b4512c2d90e9b0ce58eb045eae2d968161e9018f720c7835cb4d421504b11fb2485886d169b2d4418ee6f969b2ccc18f2c96729bda430eb4d063b99651dad24c26bc2708c3da6308a0d502ad02a8611928ab17491a4d510308928e7b0a7a5ed32bfd86e83b1d3c5bb7b4a0eda05517c47f9ee626bac0526af6985b282b308c60e7b4a0ad68eb05476c34f58abda505672268ba378a8300600b65ed339adc92b0526096ed2729216acc80b582b9ad645a8c9eb69dcc597b4988b1d735cb252d5a89c33f39aded24b5592d1877b296adcd6e4972fad260eb3dc6302b49724ce6b72fbda4ec5416a2171a30e5cd8c2cb0f3dcac6e599b50c5b2945731d06a01bad02f01dd177b383e5412c9473fad181960ad229883b8c0cc375a0b595cca613622cc5d58a9b4dc872d0433ed65732984cda70bbce62bc230731508c62947fa01504aa4d83a66296f17c8c0ce4f51fad3418e1d357dce6f5a6831cf73125569b18751da93da05a0cb4d314987c3babc187deaf1755cde7f541dad0e627b995ca6ea378da0375946403a6922d3418ee6fa0ea287405b8e65a8a7fded32c44e62bc2c89ff8c2283b7b4c93562ea055ed3202d22abc0b6518363c62947fb9bd06ac33969ac4b6aaa43deaf1b1d21ed55616b0907f800b1857b492dc3aa7311f2a0d548356c8ef402a51d6626053ffc7317b4ad4e615accd89b07f402984ce6261d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part731 : Excludes 0x8280000000000000000000000000000000 0xf7d6dc75540000000000000000000000000 :=
  finishCode 59 0x1d05e0a361f56a5c93558287345f63ed531ccb34c5486823274a86d04730ed87abc3e0c81846314b10b41cae1f6b289058e3a1d3479c71d6a1b288c184d22f3135a532d35aaaf59583acce386805630ed3b479b4de30ad5d49aad08338e563ed6509fb074da87310de368a62e8ca13cc1832c45ed21bf2d7cf6958d9ca418f23cce3a737791584d181ac553fed187724b54502671d65018f245d01b1879aa283d8e56e6b969a72b2d7cf6927ebd94c3e73761ec4f36513c309ac1e0c8aced00690148bad35c9f05b496ac62886e2104b5859ab498c2c057480b93dccb39ac753399560e90183fb52deeb460cb0f07f8c3b98d1e6e65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part733 : Excludes 0x8082000000000000000000000000000000 0xf6f74cb4845041000000000000000000000 :=
  finishCode 61 0x1d0651b017daf0d41cc4de707d4c26d5b3159f8e6ad87d4c0ed4298f02d0e1df981d69a61f0faac8b4d729cb2d380987e0db3da520a1f5969b06f8de70730fa981d69a61f8c0ed44203fd6103ea7e1c6e30305bdc727ff503c1c6408a0fdcb32d0ded24f369230338f5cca2d3068a8ee5968775caa7e1c6c3eaf61c058c7bbc37341f9b0e2cfcf770cfc83f841a075169a3fd3959cde0eb1a552423a9735bda5ccb0759786507fb181ce62b20ff58c3eac9030549c0490ef7788fa7017bbd06b83f9f54e02f695d14c4e0c3f13cda87510472d35276f69595ad0c6b73165276143a306b4d16c8dcd4771f754027017358b648d32d0424e2678c0b9ad69aa618a504724c562e90530fad36 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part735 : Excludes 0x8080040000000000000000000000000000 0xf6e6ec34260221010008000000000000000 :=
  finishCode 43 0x3a8da40040b6b0a2f18ac5f6bc292661aad35ed27313029776379b58bc1c3e30298ad47727b52023c15a69c3cfc66f39ac8021017db78f81c3534398c80b482b554e3a6077b2cc296aa9c766aaa02deca5e330fc82547fc8353039875056be3e0607928e61f386c737412a4d4013316ce1ab4d387b915aab1cdded250d379b40c2400a60bec50f34a5aca09b3989c352527376a122f030cc3a72b94769478c2670d395987617db5082b9ab6613315b596398b56d042b4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part736 : Excludes 0x8080000000000000000000000000000000 0xf6e66c74040000000000000000000000000 :=
  finishCode 127 0x751a420ac2041b6f1886819438e9cdd63b3da4e62a3f2f18bed63b1b4ded29016ad87d5d083ac7010faa02e58ea4856a2bc270ba20ed24f07d528a2fb92061f59ab69018fbe2d92c3ad455e2607386bda52060dd5e0e6320d43eb0bed94591ab720d4bde2fb415a05649bb56c5f6d5b9ec17db56e06b837528f1f95acad5b0fab50bc3e0405742003ffc2536aca4d4dfe51730887d594640e632d34c56731969a613308c911651857461cc56825398b59623ac61d1ff185412a0acc22ca3a0980bece631c3528b20ec1928258e62ce35966948b0d46a92349abdb683da3bdcc6d4b412b4fdd06817417db78ac146df05303ea2b58fff187386a8bd017461da6f181506a98d4b503d181386a9263031ffe8c0c1f43eac539a86d653eead4d41a1f54fcd18138687d53cb2c74a365210fab10a6378d030ee5929c349fa7376509fb2c94c3e943380a45d69a80b9846e6b59dc5cd27eab0922856395ad4c18ec2362ab78c0d692ca11395a856692ad36063be0ca23cde0494ad36063a8f569b2c1d90583c35d386c605c9e7b9a302099835c1d4e1ac83496063a8f547680b96665ab386ba0ca298b4d0fa8bece63181cd8681f59dc6c3512be0ce07d588680a228118e562798b3ab3b8c0cb1d408a444e1ae6b902abc20564a3b52e288b10a82c8701395ac96527a02c8d30d54fbeb4d4e119b20d6302a3f592cc53253b93e302a176d104651016b51949e5d7398b93e415a3bdcd72c9569a087527ac96 (by decide +kernel)

private theorem part734 : Excludes 0x8080000000000000000000000000000000 0xf6e66c34040000000000000000000000000 :=
  splitAt 1 114 0xf6e66c34040000000000000000000000000 part736 part735 (by decide +kernel)

private theorem part732 : Excludes 0x8080000000000000000000000000000000 0xf6e64c34040000000000000000000000000 :=
  splitAt 1 121 0xf6e64c34040000000000000000000000000 part734 part733 (by decide +kernel)

private theorem part730 : Excludes 0x8080000000000000000000000000000000 0xf6c64c34040000000000000000000000000 :=
  splitAt 1 129 0xf6c64c34040000000000000000000000000 part732 part731 (by decide +kernel)

private theorem part728 : Excludes 0x8080000000000000000000000000000000 0xf4c64c34040000000000000000000000000 :=
  splitAt 1 133 0xf4c64c34040000000000000000000000000 part730 part729 (by decide +kernel)

private theorem part726 : Excludes 0x8080000000000000000000000000000000 0xf4c44c34040000000000000000000000000 :=
  splitAt 1 125 0xf4c44c34040000000000000000000000000 part728 part727 (by decide +kernel)

private theorem part724 : Excludes 0x8080000000000000000000000000000000 0xf4844c34040000000000000000000000000 :=
  splitAt 1 130 0xf4844c34040000000000000000000000000 part726 part725 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part739 : Excludes 0x9020000000000000000000000000000000 0xf46cd7b4481000000000000000000000000 :=
  finishCode 145 0x20c7c214791b46f05f22ff4f5c73538f8364e33360de2a851b290b189355abca1b39aa86e5abad166249ee4c031c9d65e5e15aaa054e62de34050d5511047f9c7dca32d0582e73562fad0639ab05d8931ee54371c9d45f1804e32c62a89c3305e938f9cb5ee72d0d23e1dd279cd0290921cd565b3524792a1b398ad0db06503ba1518d92b17398810e7b99b0c792c31962e5e1479a98c1793fec2f364ad5d43693b517b60b03838e6c35a18345687071d85ea1b8e6ad03607b98e620d1279877558661101fa82de60f97a49af1ee586e0b75a9cd4d6aaabfcb76a3557fcb3d05b8f3e279a81ce4ebc320cc281e614ac54e161dd1faaa84f357fc0d15a0ad3652484e61faad4ce160d158aad0566f354ce160d158aad05c86f1e46c19806c9cd683c9ee526a7310ee9ee683ca4d4e62b82c8a428f65279c9ce6a9c34b61e7a0ec39e72d6d186327acff720ad584e11c614caff6188f95ee2c173fa9c7d78360feb2bfd82e3e54029b0e441833073cb8ac5f5a1cd2f0e7a38c1f9ec2b3d60b936c79e6c3960a6c398b2b4d0e7b6896073da7330460f25e162cb53ce33079944eb4d26da4461e7b16562b1c2d6ae72d0689c2e58d87747ca7195c11c39abd865a682dce62b3d38fb606c396367311e0830d28f3d8569a1cf6f162eac073d47723bd24a9ff969a7199bc79094b014d8bab4d0e798bcc2e50d290b30e4356e57f82dc19a3f56c1683071ce62b41858ab576b0ca071d99cc569ac4b9ab6b4d1ee98bce62bc310b43403f5640e6303443ba6238e620d15a68bce5a6982d03691f398b68c198e62c496ad87741aea499682d5b517a0ece621dd6d13c179835d4432d15cdad5b30bb9b66ada0d584398bd5683ca0ad06a7b9a30e3c96ad8366 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part741 : Excludes 0x9400000000000000000000000000000000 0xe4bef7bc000000000000000000000000000 :=
  finishCode 59 0x1dc7c1ac071b28ce0ba617a878d0372d0c5d2ce340a041e639a946c79e60130ca90e2d8946ce6a60b9ab651139ab08b2248835737c82b728c60d6adbd7dcdef559ab660d6adcaff5a1a0159c524cb1b5069894e6a511611a856164650ff6917969a9432d8cb3183cc8f34f2a50cc1af59969a48d4a19b24c1b1b24e62f5b8e06d6078e06b8bd59c59ec6d95989864c4a5115013fb145ce6260d3c15f72d3567a5038a2f103287fb8e62521292ae8c0146d8c624c0cd83ca884e4e7355abca49624b56d88e70b388cf7330ba0ecc2f18bd88600e5b0765b4623c71140d83349ab4615ab707b300a8e507683b8e160cd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part743 : Excludes 0xb000000000000000000000000000000000 0xe4efde34000000000000000000000000000 :=
  finishCode 87 0x791cc741c8073ab00df6a104b047560a021398a51c3aa83b1f2981e3989cc639698acc0ed63387198c0e1df62ccafb30398a5a84c0e63251ce4e60541ac7315a6a8ece6a5ad9eb6835398b48de2f81df49bc607314a9366aa9cc4c3a1af928e61f38c9cb5645a6c6075139cb5a849ac1ad38fa84649bb28bc3591018a617798adc8680e5b02c4e6a0bd0eea70d234d6513ad3504a3e541daa83e56a4c72d509c7f571cad0e415a0ae174ad09c2c664a3974569a8351f2ac8b4d8156605415b94e3de80ed246605597c5d10eea3bd28e82b062ce5372aad360f22ef30faf01dd69148415a095cdf1c2d8533dc589eb43358c72d7379fd4e5b394d94680c3f030cc522ef640767399569a61f315b389a1c2d38309ad06396ad0e0e3c72d58aad06309ad34e62d0320c2986c2e3d1e49cb41a21dd396c0d15e1485a1d07f1f281b4e16611631685500471a65c72b5769b82a60ff01e5c7aa3d6a5ce651c4d07f58a8b4e83fb4ddca6735 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part745 : Excludes 0x9002000000000000000000000000000000 0xf67ed634c04801000000000000000000000 :=
  finishCode 105 0x20c681dc530c52301730c3eb824ee061a4c569b030e388ad360f31c44186b4d721986407fad8359e38cb56c18a1dd5c1002f4c0891d382ddab65ed388aa80b73dfcd478358e9dab6813621c3a760e92fdace5ed82fed5b6a38e7c75ed55388cd5b066b60ca1c66401a0b4e62b0029639a93ccbdae3d9c9ed5b7c1aab1c7d0672c8aa1c6525f070d69ad5b39ab28d5b92820c36adcb0360f778f72b2d05eb56ce624f3550deb3555aa6b572f6c90b9ab61c79cd6d4f409b99569a61f3158c1d986c07fa0d183ba3a1b87e356d9c2dda98b20f1d027017c0b29f3168a7ce60c82de60c977671ead050434033f38ed89a08b6a3b585a5b0e2c8d3353d892b2b02d9b2db44d190409b51e2eab51e364b0c5644a128302dd6564d7168cd619a9e5d52f4a08d679ac306b46ba50cbab0b2cbd2802b05d54a0b966735a7ce168c085409b60d23280d14f0e6290d878eb13696a50d6832435cde54394e737a60c0460e02c9755656a354b1a933db5a8e3c77b6c6ab624b4b5ac70799a5aafd59fb5864f29fb5686b5726fa587e3385bb039c3c7524a3ee5a6b56d23f38e4bd219f6aa81ce4f2ac5569ad5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part746 : Excludes 0x9000000000000000000000000000000000 0xe66ef634000000000000000000000000000 :=
  finishCode 67 0x390da3e041b20eaf8a27188839581b30945669473f9ca113f9c03b06b985d69a3016a1cc20ab600e54f7c5213989c44a369478e3e50d8a36313188c0e56d19477081700398c4039dac306c6191748c0558286c04b5a69cc5492b3d94526c9527c9db402ad5c3c6301174c3135e168302987423741f4d927e3381828569a1b93f1c6c33f1c4e538f8be62038c97b6736a014a4ab4d944b00440507860a3137310771835ab60e767164260c7fb6ada0ace6a0499ca61b92deac5e1aeb035686d42a8ce4606361a01526a711396ac85ad8d9292b302a01506ac259aaa8e7381a015633290d076d5b302b30b234ee6119b0c78318104da0d5783e12c40a93164a3c60567e6c38352e539402d5b6a9a51e0f3354e302d3b6119b0c7823c1947b100c4618986e658c9c7ce6a0e7 (by decide +kernel)

private theorem part744 : Excludes 0x9000000000000000000000000000000000 0xe66ed634000000000000000000000000000 :=
  splitAt 1 121 0xe66ed634000000000000000000000000000 part746 part745 (by decide +kernel)

private theorem part742 : Excludes 0x9000000000000000000000000000000000 0xe46ed634000000000000000000000000000 :=
  splitAt 1 133 0xe46ed634000000000000000000000000000 part744 part743 (by decide +kernel)

private theorem part740 : Excludes 0x9000000000000000000000000000000000 0xe42ed634000000000000000000000000000 :=
  splitAt 1 130 0xe42ed634000000000000000000000000000 part742 part741 (by decide +kernel)

private theorem part738 : Excludes 0x9000000000000000000000000000000000 0xe42cd634000000000000000000000000000 :=
  splitAt 1 125 0xe42cd634000000000000000000000000000 part740 part739 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part749 : Excludes 0x8400200000000000000000000000000000 0xf70e653d10c042001000000000000000000 :=
  finishCode 89 0x20083194771a417aad85f58e56737671ac71c6ca22b4d292c08b4d69ac9053988f86012a414b621d92e6c5117b169b1444a4ab834ce371a094c026256d10773154c46e6d9a93071526a7f5a9ac2338e6390625317b30b00765505a8ce575a38f84a23356e288cd5b28dabeca23146dc828dc1d928dca60ee640da7a439a71b39bad85f58e562659a7e597157876567a70f8dce92b28db98da308cc188cc4ad4359e0648765eaf41ad056c555a6d1855789cc43b31cc4c32a035265929804e62ee34ce5a6b524e6e71b412c83566038b03143b29828d6524a80b81ee6611abe5ab6b4d69497d49bf286d69ad29737c4df50db089820565a68734e367295b19039bb0f6373a07c39a0c5491667206d66741d43ab030d70641c867198387c8fd6a4a07c1921d58311e3352507ed393989b9d693135da72731373c981c3cdcf352507ed538dceb499a72d398192731 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part752 : Excludes 0x1a000200000000000000000000000000000 0xe5ffd43512c0d0001000000000000000000 :=
  finishCode 55 0xe43a0cc3581e55e05d2ce39be1e7a8fd422947508c8252e6c8df0d9a8fd5851fca4d41aa8fe526b58b11942eb275a68ba549b293d69ad4330d2378bc031d484f037e3e526bcb4d588d18749086fe49cc61d69b394e30e1bf5e09af461c17a3dd41ab2082293d0172c15426b5371ecb270d986ce8c3b20a3d85aa3e5058b16e2e58f3d3c3fdc4d7729a85d49ab4d510ff72cf5ca6a1752686fe83e8acd786b3c4d751fa845226937593c1bf591587715c174830e59e86fd4770b559049bc2d541dc93716acb4d508a0c45d2b1b87a22e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part754 : Excludes 0x18000240000000000000000000000000000 0xe7fff43da0c3c3001248000000000000000 :=
  finishCode 7 0xc203b5d04f4c83b30598bd58737c5f316da0ec5b717cdab7284526e4d5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part756 : Excludes 0x18000200040000000000000000000000000 0xe77dcc7f00cac8001303200040008000000 :=
  finishCode 51 0x3289e308b4d7d20c39bc0ed7414c311aca60ddad14e6f1838e56c2362aa84cdaf1f75c76c550559cdcbe6ce188e317a9366adb56e3e6a93cc1a0ed61150691a0830e5673751fca4d0c8c60d69aa986e357603683b4fbad5b729b9be0c418c0ed16dce3b0dfc1f616db58d8aa0ed055cd4f729a85507e0ed61dc1bb47883b48f334a45a25e9174ba0f2308e60b6e30598bde05001dad5d942aa4f3e0c15171e9355426e6d2fac7dd4a381c452ee4f054c1881f9222d5b492a80630cb40c20ec63f09cdcb7b30c47627c16adc831076c0a9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part757 : Excludes 0x18000200000000000000000000000000000 0xe77d447504c0c0001000000000000000000 :=
  finishCode 109 0xd42f0ce07947ea3fd5a6c60b40dcd5b781d04d03ca663c8d496b1ac860b69fc5cd48fa02cb4e5cd81dae6d69a92f4dae6e79a9e5cb407b48723c8da28860b381016d2fa0fb0756119b5da5f24e5a5f41f4f9a1bf461cdb2d35a5f0753808ede6a783b52c641707b118410a0fda5f41f498b07d9a5ee3d73586fe3738ede2628ede3809b9e3ee86fda5e5cd9a5e0ed969a5cd4f1b4500ca295a6982d701dbc4c5076b9b60ea90d4a19d03cf4ecce6f34a919c98af6b025c2656a7961de43d147f293501f28e41daa01942ade3209e031c757293d22e9295a685be262b094fba1bf48fa02c37f394d286b4d38083b41db368f2031d47f2934e5328e64079cdddc6f1a4681583869cac05f3d6e0eac0d306b154d87012dee60ed7b101720ac1da8c2f0d2f6a49c0542b41ed04a5cd9016b3f9ace1ab6b1982e0c311c62f2e683b5b4741a9f289cd86a3d37f98bd877359544ed378c0260190760ed681583b15f71f1504a2b3300a44d26eb846166adb4cc15e601317a51e6d154510c46a3f949a7a98dc60b15a6a8fe6adad3416262f6adce5541f9b8d4453103683b7accd676adbdd4c164d57bac9e96ada984c1354c173594722d63305cc3b9acaa11 (by decide +kernel)

private theorem part755 : Excludes 0x18000200000000000000000000000000000 0xe77d447500c0c0001000000000000000000 :=
  splitAt 1 102 0xe77d447500c0c0001000000000000000000 part757 part756 (by decide +kernel)

private theorem part753 : Excludes 0x18000200000000000000000000000000000 0xe77d443500c0c0001000000000000000000 :=
  splitAt 1 114 0xe77d443500c0c0001000000000000000000 part755 part754 (by decide +kernel)

private theorem part751 : Excludes 0x18000200000000000000000000000000000 0xe57d443500c0c0001000000000000000000 :=
  splitAt 1 133 0xe57d443500c0c0001000000000000000000 part753 part752 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part759 : Excludes 0x8100200000000000000000000000000000 0xf54c6c35608440801000000000000000000 :=
  finishCode 153 0x42902390cc310c80fd480aca07545f318788e28c36279f3544ed5b398a8ee407b16594540e628c1d86d76712232bf569ad2f722c4d76adabf50366e78f9ab4d26bc6e7487ad363032d34ac6aec6e73ffa3f6499b28e62b8f61cc5bc5a6984e3159c3478e6138c56d67a0e20c9315be0b4d17cc5e151398ad06b2d54c2718ae0c671cc4712222f93b079e4d7a3029eb3ffad56728c60dcaf1816adcf778c0acee41aa4458456168b20ed652825641183b0e1b460547a81f69fbd9410f4605a7ea3d41fca2769f95ee3869b9e30278207e514b16613b9a8c262d2900cab82f3361ca294a2acee2e6b28c21cc4dff2d34e526e793bef6b5a6984cd4741fd402a2f1798be5f46211883dca07398ad34e0270f6819439ba0be0dc98a569a73183cc9e54179b9e12ba81d05e7316517c570c56b4d8e629478e1b0792f1ad14e632d360f318455fb2d14daea493988be598561886807dac83681cd0eaad165a6a8d4bb70718f9eb3f6b3b08a359626c232e6a86d6aa7373f230f251dc8ea495f1ab727e4c269f9994351ca2f179984d69ac8286e6119c045f2a49802ec236520c5a6be8c82ca4c262b58fa283f521d07f3ff9736407a0bd5f328841922b5831906a1cf554089f1505e2f9670bb7251c1471ffd6aaa2f85e6fa2c8b6184d2c620ffe82f373d18139babf6722bdddab6f75373c605abb2c1cde68119ee62f9680de62f9373cb0539b976e583a0be8c3c1e569ad5b0ea8be5a06220c38db202f993ca2975a6a0fc973356d636a498317023c5f2b4d83079f20fd45f2cbdac5f0b9b136cd5ab05398984cc52a01875145a69cc56632c4cffe4b91f2cb4d96225c1cc65a6b307310eace39415a0d51e3251d2264d7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part761 : Excludes 0x8001200000000000000000000000000000 0xf77cc47d209040249000000000000000000 :=
  finishCode 53 0xfa418f83c8ee0c46189ad363988c2c7fb1cc411208b183bb86018e36835180ad8511510c93530ba88649ab50f2398c40bcd9430c937e5a4ad34e62e6b8e0294146145f2c95676ca2d36398bd6e727b9ac12acc340405736c0c5599ce3d919b07b0c8ad3452ea496a9c8fb387a9249be71b1febc8bc3306178d864a1398ac0d06a62541d9fee5819cad245b18ab1fecbe680b98aae4f95f2b4d30b9894e373284a79a6ab4d39883245e65175e1988307eaa624d51df350d3ca7ff1b48a3d68a83589aee6b694a01604cb0c4c2ec31812247900c946cc16e6d85e62ff (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part763 : Excludes 0x8010200000000000000000000000000000 0xf7dc54b5108244081000000000000000000 :=
  finishCode 85 0x7d1dc6b1bc180b48c42a0a61cad3838dabee41293f604061cb11398978e5a6831e15a9f747dab1159ea989c1c6c98b27a5ab682527eb59e1e7a8f5476731661a883cc7dd83a831c80a6b1981ac55492abed4273035846afb6d1903c147b293d9c3b0be6d25926aa3b063cd25398c825592cd3f4f797cce1a8259984e1887907fa8ef981ac554928de639897355c2f9c7b983ca4d4e628eb947a9ff9aceb116119014e62b21cc547b293d6a32805781f6c405583c4fd6d19c2e6ca3558dad34a4a507312b30b4d98aaa1357d9014c1a71b412ac9e59fc7315979c6ce52cc310aa0fb49fa1bf9a6683b6b29cc41629474f4c9132fa98bd9457184398b48a22095827356dace83b30bcb4d064b59dacf1b8cfeb1b64a42f61f3e475a4d4a42b4d610293460d28e0c741db16e252831d26b24d639893f5bc671a7f41e526a619290b285179a7e7f54f5a0ed69ad297358fd4e62e6b906ad3f3068fb6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part765 : Excludes 0x8000240000000000000000000000000000 0xf5fdd43d208241001248000000000000000 :=
  finishCode 49 0xfa3b90a340307076b946373ad34c2272b72dc9435a69c05ac7414c177c1d65a696dd6ab079309987d40315bdce11d8df5eae2af8c3ad35476a3d157c6c37afad357864164314a84e51d981d8b32d352261a1398ac46398a98b206fe30f981d5c6d00f7394c186b3159ea2007b898ae6f4feb9be835b0ddcab41d51b2c370c6b0a5986214032c441865b7a0ea80b51ea84e3739fece4500c731302a8ed69aa0394e7bbc1d415a8353029cc558302ce6f415a0d455f1ab55c185b2073155018720d4dce9474888b558571a4504a0c35a6cb53408c0c35a68bfe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part766 : Excludes 0x8000200000000000000000000000000000 0xf55d5475008040001000000000000000000 :=
  finishCode 113 0x8503eb063c8c40c2c6226e38fbed5b2f693f4e632d35a0691a838daf03f58e566110a6c6e783ab9ac18e72b994475ca3d37fad34e62379994811ec398a98b4d494cc59373b0dce0294348bca3b627c93b279c3ed4a1b0dd69aa4350c8316673598460eb1b9dca63fd8c1c0997369c048ff3545402f2350bc0bce04202c731599cb4d6adac947daf6d969ae3949da47d3c6d0e477169a72b9426b25906a3af6adc08d67906aa1339892965a88ad564b356d69ab51771a062acb4938d9cad64b1fec37f0ad5a6ad5b41ab48a3b818e71b51ec731571786a0e62ee2f81bf960a613315b10e508abec7cab4730ea90e53837eb2716a8f9526b280d49a83b26bc607489a4957c5914c79037e61f303c1e62e69ee561ee399403c1a6b0904ff66e7063c61d42ab3351e831e599cc8300da3c80c771cce4f593ad2528b232d64ee3b5a6948e559cde3cfa0ea0916a6931418f011e3deac3c79e6c771cac15ec6f1b46219079018ea4f96a318351c9fed49f2d35663461d622a3b8756b4d592cb517b69fecd8eb4d8c3cb4d593831e6a1a454018ee559cdebc18a6587a0d564b2d354566b130ec629791203181d692913363cc1f737b10569aa3b (by decide +kernel)

private theorem part764 : Excludes 0x8000200000000000000000000000000000 0xf55d5435008040001000000000000000000 :=
  splitAt 1 114 0xf55d5435008040001000000000000000000 part766 part765 (by decide +kernel)

private theorem part762 : Excludes 0x8000200000000000000000000000000000 0xf55c5435008040001000000000000000000 :=
  splitAt 1 124 0xf55c5435008040001000000000000000000 part764 part763 (by decide +kernel)

private theorem part760 : Excludes 0x8000200000000000000000000000000000 0xf55c4435008040001000000000000000000 :=
  splitAt 1 120 0xf55c4435008040001000000000000000000 part762 part761 (by decide +kernel)

private theorem part758 : Excludes 0x8000200000000000000000000000000000 0xf54c4435008040001000000000000000000 :=
  splitAt 1 128 0xf54c4435008040001000000000000000000 part760 part759 (by decide +kernel)

private theorem part750 : Excludes 0x8000200000000000000000000000000000 0xe54c4435008040001000000000000000000 :=
  splitAt 1 136 0xe54c4435008040001000000000000000000 part758 part751 (by decide +kernel)

private theorem part748 : Excludes 0x8000200000000000000000000000000000 0xe50c4435008040001000000000000000000 :=
  splitAt 1 130 0xe50c4435008040001000000000000000000 part750 part749 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part769 : Excludes 0x8020000800000000000000000000000000 0xf54c67b44050200c0401000040000000000 :=
  finishCode 47 0x1c8801f06603ea51b900a2ff4ee94347ea835317c51b286ab0a43383ed317c50d28d9fae5a6a794e62afb2868fd661898bd41a935286b78ce18be28db306c206d22b06d825e7b97319a753d6a4f8c3b50d49f2d3518a465944eb3d3fd98be5a6af0b42e83dd41a8fd47133da4d86c455a6a5149af3d960eaa5149ae8356d0e5a6d785f21598962d293e6a86da5e71949cc28d8378f81b5ca36f00be578396bdb6476a86da5eb2f6aecd2f38ca86d06b2926305c73117ca92636b8be58c492c2d538c9cd584690c9255a6bdd5ac283b492cb4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part771 : Excludes 0x8200000800000000000000000000000000 0xf51ef775004006080410000040000000000 :=
  finishCode 17 0x7c19c0fab510a1866292b98c0038459f2894e5ac47969ab515c03b2e658e06a25166ad254732934a23038547329343b2517070b785078a365079ed2619 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part773 : Excludes 0xa000000800000000000000000000000000 0xe5af7734004400280500000040000000000 :=
  finishCode 63 0x7b1dc821bc0749700df391845a6ac882b907613f80928e783cb94cc0a7319ed28d9361981530398ac0195968a7f17379815607316d06a8358e333da5476605398a84e7b2ad34c0a93741aa015a0071b481d9056c4db26ba0ad06a7358f72b3b5a6b93dcb25d15a4b48a399076b498feb10410c207d564660e633134e6a81b41dad8a038e16a4d57dcb020561f09c44bda8d9902a7319806613fb1cb43b3187a306f773f8a934e5ac47969ab51681580f2b0c61f2a0ed8871ea5eeeb477b49c4588700ad82a2d9348a515ed271140ab501f556170601480eca0ae393935e415ac82cf8e624d7405a0d459f1cc544b1cc5056c318d5a73140d876570405a0ad3d341e47b2b3b398c6ad (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part774 : Excludes 0x8000000800000000000000000000000000 0xe72e6734004000080400000040000000000 :=
  finishCode 155 0x208721b420dc41d661f020abc1004181f57714438d83b5ca7021d4728259422c02b0c2d8f52947040a3f528a815540fe341c4dfa58126aa3f528a9dd8dfab4d904af6940d8396380c0df8022041ac05962ead4462e7c2b06e32f4c91341d8e5e51f9fc5ca7244d222a3938e9b8638e9cc506af601164f4a3f58ba71b288ad3502b1ca6007c16a3394cc0251b18987d4a231c6c1bf1c0569a71b772006f0626b628ee8389804e6251b3879cdd846c0e36815904a5117b4c40b40598053b32d34a366f3969a507379c40b8a3630b7b1f0771e07316c071a8050d380b9be7ac8f84c3260183cc737670b7741d5016f6938c9445a05614059ece531f09805ed320951e741e4e363e13edc0394129cc4e0710418ce3601d98a365256120fa719393943409328d4ff671b1aeca35578b9567b8a795ed270f0ec8f84a1ad0330d20764e1f396478ab4d39b92f6510ad35a43f0e3673761eca1b8c3cc3d729927587b34a4dfece2d366a4a86d6929339986903b2c0b9eeea3916cbd5d077063dde699bda4e3e4d58fcac554919c5c09aae51a0fa09b0a8b94d87ab4d0d09cd58a7394c9af41ecf7718762ab9bce6ea4d91e2e5326b97d53468169b3da4a2e70f38eb61061cc62889c04a2ee61c06398ad265a6c50d3fdc18d8143542318bc37a83552698be39ba0d569b1cde20317c83571c8764a4a5116918456104b20d5b45516c305c6234a2c7351f5a5167b49c9cc5e94581664d55c03b2c478976711515ca397b4b966735bddcfea60b0ecb38b3d9ed26a7387ad24c32625288b088a2b071b395cf69412983524316ed68ef693959cae3eaad1d04aac3da53bb0abd3d2b4d387a0156632774e1eda338d2182cc5e83b902a7375a9c7317b49cde40ac737 (by decide +kernel)

private theorem part772 : Excludes 0x8000000800000000000000000000000000 0xe52e6734004000080400000040000000000 :=
  splitAt 1 133 0xe52e6734004000080400000040000000000 part774 part773 (by decide +kernel)

private theorem part770 : Excludes 0x8000000800000000000000000000000000 0xe50e6734004000080400000040000000000 :=
  splitAt 1 129 0xe50e6734004000080400000040000000000 part772 part771 (by decide +kernel)

private theorem part768 : Excludes 0x8000000800000000000000000000000000 0xe50c6734004000080400000040000000000 :=
  splitAt 1 125 0xe50c6734004000080400000040000000000 part770 part769 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part777 : Excludes 0x8020000040000000000000000000000000 0xe5dcc7bcc01200082201004000008000000 :=
  finishCode 125 0x220781f05f03ea7c428b415aba8f649da0c479e72d5039cd4a367359e465170290a20735508cb4d400b064e16720b161dd9fecb4f35660feb2d6b0bdd4ff71c2d65a3e1965aa073059cd4a36d63965a71139aac6e39aa8bc7c2a4917fb60f2328b018ff651706b9cc4a42aa146d307b9cd5b3fd835cc2e91149ab90b159a4a8f1721cf755abac05cc72764ff6e493dc835c9e71cc5e456184286aa8601982eb4130ba4d58883cc913317a8f64ec807d2260859863079492b38da05e6721b05d1861cf2ff98bd64248ca075a1b994ff6a07954291656353a0da9db836c3bb043cd5b7b9ab0882507cd88d2c2f4ecb93d69a0a12f49f8aff98be3cf588a86d84582cf6b5a6b58562b2c565a9b98d3ced55053a58b4d8f724b12dd9f3658ab56de47c0a1a88286ca362ff243c7fb48988d6697a79c54ab435a0c61949ab389c2b84f34b145f358569a3cf2dd9a8a079686e6b521a926050a3356873965486a1b4c108731cb43054a90d492ca279e36b96ec19eb2d0d7ad3414316edc8ea2f5f185f2cb4142a1b98929436a49b5d7c5a6c94358b8b156aef5788ca4a9004a35dcae3515a697a5262d8348f02046393a0bc1a20d729019ec42d0d69b2bfd47e60d57fc93b00f935c3432c4d18a2c55a698352765d196ae71f596a0441b2c23c90a073d705a0c1aa3d9ab6b4d5abc5bb6adac065a6ca3d7c11878038e9294a1923e617abec91f2d3672c8b1438e1c7947ab4d640c44a144eaff9ab6b27478a804c1ab5391e2a0130c97a6618ad35202a4f478ad36 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part779 : Excludes 0xa000000040000000000000000000000000 0xe58fd6bc800220000a01400000008000000 :=
  finishCode 83 0xee3c8e808f65a3a004e6a62b30383a41bed23501df6014869fc7193089cd538530e5a964003cf57fce6f83dbd8564ae6b4f4b1063efa7fd6a341ed63a11d24792de30e6c74202eb2d4630ef573fdc8c190e6f96864c551ec40a4f583c6c761b8986476a79e30eb05363caff1e7af09ff476c00b3fdc1ed246611388cb514f3c02f3efa44dee64d74ffa84da84e0e4eca1cb569b28e53d3440aff5a4d18362c9f7e015b4cd7c65126e9134fec6fd3039bf64f4935e588c40e43281f54d1683039cd65a6abee71d9cd49aee6f879e731315935d69ad42a8f77803e9ff737ad0630e3cf396ad0ce6a7618449af39ad42657d9ccb18757f8f3deb64d793fea13303cce258c81c650c260ce6f5a6c1fce5aaff1e7a0bc9af2bfc56683f1e7cb4034586b135d69a735363935e2e58ba6068b18ca1c0ce5a93d949ad4f5a88f0c3ea7317420f70b540ba91940fc1f68c2c1fcff601d83da4d60858acf7538587d52c810e167319602b43526cb579eb2801 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part781 : Excludes 0x8400000040000000000000000000000000 0xe70ee73c800200804201080000008000000 :=
  finishCode 117 0xee398f0390d8037d9406b8ba66ad9484e62c42d06592937ca22b6461e722ac3d8923c7692cb2d587c00c42c963008b44c1aca2d8c214358932924ff6a49963aa43963ab010f1a90e5998fae6818457dcd295aba79cc02b4d28d9c6ce6f00399683ec1c4e1e61928d8ba5c8b354d05e2cb387ad81e326acd4916793566b1946db4671640f1b403eb2ddc4d7624ad5d88eb4d30c833d885a6c8fb50db4bd25eb4d91f66198e02c231070d272d071165935c7d671d257c9e726b9436286c7fb28b8bd6206720c6207d700fd5e2a1b39a8bd4a1a51b651102869484af3393d63ac1f39ab56c9af1f0c23e7356307c32884e327356adc7b983cc60c7c270b4c146b2925b45018465163b17d58a63eb3e123330f5847393da86b0f8f72e3d5a8a86d25ee6d9846c3d1f5b9be055c6156a2af9737c6ff4959435e01d20c6adae0d0290a01c2d30386c4c71e8b50e1f5c60ce6a735984174b5363fdad34e1ad4d98ab3d6565672d263ce6d5959c64f86a6cc3b595b08d498e6ec2326acb8418a01c2d30000c9ef8c18b2cfc2b4d1f58f4630717d4e6a7358e371f047a2e5116897d5abb0faccc1748fad3df2d349aed35263ad367acb98cb967e1621ab71cc4c4651128db291838d627fb3889cc4a42c6300a21cd42db3d54db27fb6adad24db31b8e7b9985deeb41e47c270b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part783 : Excludes 0x8100000040000000000000000000000000 0xf74eeebca00200090201020000008000000 :=
  finishCode 17 0x2046d19420d98a63988be481673785f2d0309061c34e364e5969a92306fa51d61f2764122d5d04fb4fce62d638c3e901521b07ce1e93506f9fee06fbe0d5d8e562f306fb681d7906681306b9c6e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part785 : Excludes 0x18000000040000000000000000000000000 0xe77ece3e800a00000303000000008000000 :=
  finishCode 77 0xf23904d781ca0ed20d9075941abc4c54f7b56d3d6a1758aad5c3c60ed205b40f82600ed4d0e1a72b82ca9117af96f63f0a005246f738c4a6e116da784d500ac92500c97cd24734941db328b42789a2d35d0411a582e93f0cb551e79c9deef1f8438ea1340ec71b26bbc04d5920aaff40ea8f505b1c34e6ec2348d0129e262b8e45a271b4199cdd3440ec8f1737a47ce02823591800b4caff71c9c65ab7004e30ee430e3b536388acfdab6a010b6caff6b3b8e4e4e2e9168ca0158aa08c1a25e9174aa8b8204d647812839693565ab97a49ae2d189af2c545a22e901ec831349c1b5ca6e6f1c8a4a5247abcb15729ad0dab73d5dd05905d2963dde37eb99438f39ac9528316adbd6521b359c01ee59408c1c5ab6f777acd07f4a1b04deee4d77c1d0781cc681c7b20bc9ae0d15b1ac739ad5fa80f418ac89ff9c8681139aa0462709ab393c9aee6b1c8c4d56a99cddca6a15527b8f568b3dd5c9ee3d38d833d3ff284dab64d7257c0cf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part787 : Excludes 0x8000100040000000000000000000000000 0xf75ec63e802210000201080020008000000 :=
  finishCode 117 0x79204691a4b28f5a7e4c56aaa4d49fa40b185906df020e9bfe4f3b94c9ae30b6520c398b389fd924aa01969a8ef4feb09662aa79e59380bc06706350ee398ca0c4495f2d2526ed5d0eba0cce3b3d7d84ac5327ea68629379cc438399c65ab694738cd06d6ac9c2e6ad8c2c9fad5b879eb5348093f4616e62d81d73d1a82f9927e6ada04c586d419816e5362aa68d27a0e6af10d3b9bc9beb33257c16d612b56dca6e6f26fbd966ad9bfd6669a1c7662db0ad69280369fa0cce6f20b5ab2ca2d0881f0b4d520dc6d41cde5abac44e62c2b416bb8f5d9acef75509b56ce6e6fd9657284dab67374d1a8720c57304d8b671b41e937e38db0ac566c5b770dc334ecc0e73737ec71b8e3282d721047250ce6e83d39bc943831b05509e6d42c84d78e32735460753250d62ee53737ac5e4989f7d026ee2c87df93fe7f338e92e5a6b01ac8d31833f99c75ab739bcdfa7f3398c7df6b3ac6d6a64b95913437ec813303b966735987d20b3555644d09724d7729cf5b6ad937d026e539eb6d5b26fad0e498b609c2384f35b1c931cd5a5ae6f38ead1daaae62c5e38fac44e17356d68770e6f27b547a6ff052c8f137eb9ace4f1f7cf72b1b735b40981cd65a99bfce36d23c073758bcb5739a84fe7b6bdcce6b279c9aed5b5e1303b2306a01308ad0e513ad5e7bbb0a4d2ae6b6adacae054b9ae771c9ee6b729c4d739bb556 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part788 : Excludes 0x8000000040000000000000000000000000 0xf75ec73c800200000201000000008000000 :=
  finishCode 75 0x831dc180c3077c1e46a1c8650a3641d0faab0b4d596c50d248cc5b83797b5a06b1cc3157ca44564ae53300c1ee729ad0d94185946c747148524b460dcbe5ed6b0cf73737acecc021f5185ad3627987d588791cdf16ed3ceb33300906ca22d82d84f3398ac8be1f08f1052b56e3e79315a5ae6f495bdcc98b356d67a9e76a3b8e5c730275a5a6d98772a2171cb51dac2b1196456034323c45725e9588829db4478c7f362dc38b737acb6588b5559420eab0731286cb014a3b56e2d1b59d6669e74f3c4794f9a3c4db2911781b40fab60d2035ce6f0345a6b17a4e1f208ce5641b811b0620e62882d84df1dfc737596c9e7a0f271b57cad04e1ec02c3e69fad0cff7310b3391c69df1e39804e1eb3393b2b4d6188f1dcc2b2526fcb6106d34650e1e73793be2d1409a77e39ba86d305a6ca2f2f49cdcb760cf524a4f66188b45ac20cf067cb57 (by decide +kernel)

private theorem part786 : Excludes 0x8000000040000000000000000000000000 0xf75ec63c800200000201000000008000000 :=
  splitAt 1 116 0xf75ec63c800200000201000000008000000 part788 part787 (by decide +kernel)

private theorem part784 : Excludes 0x8000000040000000000000000000000000 0xe75ec63c800200000201000000008000000 :=
  splitAt 1 136 0xe75ec63c800200000201000000008000000 part786 part785 (by decide +kernel)

private theorem part782 : Excludes 0x8000000040000000000000000000000000 0xe74ec63c800200000201000000008000000 :=
  splitAt 1 128 0xe74ec63c800200000201000000008000000 part784 part783 (by decide +kernel)

private theorem part780 : Excludes 0x8000000040000000000000000000000000 0xe70ec63c800200000201000000008000000 :=
  splitAt 1 130 0xe70ec63c800200000201000000008000000 part782 part781 (by decide +kernel)

private theorem part778 : Excludes 0x8000000040000000000000000000000000 0xe50ec63c800200000201000000008000000 :=
  splitAt 1 133 0xe50ec63c800200000201000000008000000 part780 part779 (by decide +kernel)

private theorem part776 : Excludes 0x8000000040000000000000000000000000 0xe50cc63c800200000201000000008000000 :=
  splitAt 1 125 0xe50cc63c800200000201000000008000000 part778 part777 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part790 : Excludes 0x8400000002000000000000000000000000 0xe50ee73cc40010040010804200000001000 :=
  finishCode 119 0x3c0f8390e63400df6d0a072d34e621d9066c18c42e01d940fc601388a03e0009355ed307b398b4cdebb34cd01ef695a69cb58bf24e4e63062e0c6408703396c1ee398b996583a0fd3fb14962e6cf69398b60c4340c607443b2941967671f272d06338c6146d46b2c3d82ac4b5a89cb546b243d89670389cad22302d94a0cd2f5a8a5066b1abc6497b4bd41ace2e0961cb5ab73d74fc2e5f7329c9c7a30f85502909736596a49cb97312d22b1004966279c0c9ca2cda00831657292585ac5939a9434e44a0cb4d46170387c4bd4a08afcbeab513fac941596cb016a99c0e396c41003b8ce34051b6b1cf6930098645eac01cd65a6b5254365bb9a5ee437b4ad35ac6ca2d363818bd4e071c3d25651b918470e0270f5a6c7035a6c8d9697b38aa27ce6b1b90ded2703396a836721878d25ef778e62e636adb13ce06ee1c82e9600e064d596ae80539abda66a486e6388b56e5abad349aae4338d84180cd72fc2d95879484a36f69878ab3b16c9cc4c0727c1e37b4a835442b3b5a8c186e078d2672d256af2835ed29f1521a014c3323d617aa014e1e0d76705ea6018e1e51b5abd07b471b54500a70f561cc286b40d65897ab4d066986578402cb4d398929e5a6a48b51818a9415a6c0c54fcad0e58b9cc419a517 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part792 : Excludes 0xa000000002000000000000000000000000 0xe5cd57b4c40011000002805000000001000 :=
  finishCode 49 0x100390aa03a43ca1f51d14031cd5a72e3d727bda524ab15595c1c64f8a4956824c795fe3e57d1dc398c2ef074ab8c01cc562b3d647a2b4d4fe9c2d00b397d24af695a6a8965a686e47c270b4b1b0385b204b18e62b171f09cc62e8c8d95a0ad352439ac3e15a0b9b61f09cd51de925721bc6c01be71f9eaec2d0ea8b641b2ce2f0b4d900a92583cc7ef03a9cd49b6a0187caa41fbe1f2acc4c22c825862b491c8057b6a4d4fde83f491d0714189c0e25cac14c26bc2366398a494c52a63e84db83be61f5c18b3307d69ae6d4189cd567b31044fa4b1480ad355f741fce3e9f1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part794 : Excludes 0x8200000002000000000000000000000000 0xf74cd775c40010010020804100000001000 :=
  finishCode 27 0x1f06f03eae62e00d106fa0c65219cd4e33292590694c0c50ea8fb4c5306340b3b902706d309a4dc9cb34a67bab5745963ed65190699c1d1510ad345f26294f2cb4d582984deef1c7d6621d53ffc1851b8602da3780d1839a0d752169320f5216d591f6bdb60e6937d69b07347da4df (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part796 : Excludes 0x8020000002000000000000000000000000 0xe76c47bcc41010000300804010000001000 :=
  finishCode 95 0x400e43e1104181f57b1e4670a1a3f5903e60117fa606b191dee5962c97849af1fbdca260d1faaf0d80fd4daf41cdeda4d72f4acad05e831067a80b2b8dc24d7728ad04bd2b5789aed820be067929e5a6ad045773da49ae4ef1fab280cd50dcf695a0ad34e62f699a92d431fab101e55f07eaa8258b574a2cb4d727ac54c323cf727cb1530cad34963317dac6b4d30ca404f5339142826196a4ad3548730cd5b616b98c98e901527ad34e3272d93d64c7561686707ea9a368913067c0d72e6cf754029cc45771485ed2b4d03acf691478665c8e8ef616945c1aed836838f93caf69838bdd5a52517067835e0c5a0cd5b50dbd9500aa21492b56e26fa924b828684a6588c1c5cd69e5306a49500aa8183524a5bb9ed307183cd1818c3c400d7487c18a077b6c6d96a7cd295a6b56e7b6bc8ca14365a69485885a0c60128dbe0b4393e27ef3709cd5ab7249540eb436c1f06414c6509e6b4388d6a0146c8f8540ef69398b0be5a1a7fd0626d77b4acb6361ad0c7c2c198e3e4f336b9cc6279ad06671b41facd5b4f59cd4e3e0d917cbd8b8238d81c7d69b20c503f07339aa86ce62d67a0e7079492939569af69969a57d6ad9cd54363f56c169b2484e32a1b398a8866a7cc593989c7cfdf356c7ea0d5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part797 : Excludes 0x8000000002000000000000000000000000 0xe76e4734c40010000000804000000001000 :=
  finishCode 79 0xf23e0415781dc5e01daca0be641fa084e1e73130898a530730c22ce23b63f7a90c5f2d82587241f504283f2ddc703157c125410c83183dc7035519c83dc72d4769c0d26af759c8a703402bdde4018839118381a80650d9bcdac670f6b1c15750da42c373242ce1e8e7900b18171d9cd5883969c3e83da4f630341ed00ac42c870f36cc94139aa86e4859394e2270ba20385c51b185b10ac135630b27c5ab65bd8c1a4dc7a3356d6aeb4d396cb4d492a926185941ca42313620602ac2502e983521b9300983500b27c562a1b930c93563878ba5585e1306717c050cb2d49ab5960f1a93e83db9158b6a156a8acb6050878e1e7cf6d262a93d6af10418f83984f30fa8c1ce4f27c5ab67316adc7114f88ff6180b981f51feac80cf4a0cb57168a90e361bddd65ab57168cb2d4fca90db01fea806068879476f3da565a2e9 (by decide +kernel)

private theorem part795 : Excludes 0x8000000002000000000000000000000000 0xe76c4734c40010000000804000000001000 :=
  splitAt 1 125 0xe76c4734c40010000000804000000001000 part797 part796 (by decide +kernel)

private theorem part793 : Excludes 0x8000000002000000000000000000000000 0xe74c4734c40010000000804000000001000 :=
  splitAt 1 129 0xe74c4734c40010000000804000000001000 part795 part794 (by decide +kernel)

private theorem part791 : Excludes 0x8000000002000000000000000000000000 0xe54c4734c40010000000804000000001000 :=
  splitAt 1 133 0xe54c4734c40010000000804000000001000 part793 part792 (by decide +kernel)

private theorem part789 : Excludes 0x8000000000000000000000000000000000 0xe50c4634840000000000000000000000000 :=
  splitAt 4753 130 0xe50c4734c40010000000804000000001000 part791 part790 (by decide +kernel)

private theorem part775 : Excludes 0x8000000000000000000000000000000000 0xe50c4634800000000000000000000000000 :=
  splitAt 1 102 0xe50c4634800000000000000000000000000 part789 part776 (by decide +kernel)

private theorem part767 : Excludes 0x8000000000000000000000000000000000 0xe50c4634000000000000000000000000000 :=
  splitAt 1 107 0xe50c4634000000000000000000000000000 part775 part768 (by decide +kernel)

private theorem part747 : Excludes 0x8000000000000000000000000000000000 0xe50c4434000000000000000000000000000 :=
  splitAt 1 117 0xe50c4434000000000000000000000000000 part767 part748 (by decide +kernel)

private theorem part737 : Excludes 0x8000000000000000000000000000000000 0xe40c4434000000000000000000000000000 :=
  splitAt 1 132 0xe40c4434000000000000000000000000000 part747 part738 (by decide +kernel)

private theorem part723 : Excludes 0x8000000000000000000000000000000000 0xe4044434000000000000000000000000000 :=
  splitAt 1 127 0xe4044434000000000000000000000000000 part737 part724 (by decide +kernel)

private theorem part697 : Excludes 0x8000000000000000000000000000000000 0xc4044434000000000000000000000000000 :=
  splitAt 1 137 0xc4044434000000000000000000000000000 part723 part698 (by decide +kernel)

private theorem part607 : Excludes 0x8000000000000000000000000000000000 0xc4040434000000000000000000000000000 :=
  splitAt 1 122 0xc4040434000000000000000000000000000 part697 part608 (by decide +kernel)

private theorem part561 : Excludes 0x8000000000000000000000000000000000 0xc4040424000000000000000000000000000 :=
  splitAt 1 112 0xc4040424000000000000000000000000000 part607 part562 (by decide +kernel)

private theorem part499 : Excludes 0x8000000000000000000000000000000000 0xc4040420000000000000000000000000000 :=
  splitAt 1 110 0xc4040420000000000000000000000000000 part561 part500 (by decide +kernel)

private theorem part443 : Excludes 0x8000000000000000000000000000000000 0xc4040400000000000000000000000000000 :=
  splitAt 1 113 0xc4040400000000000000000000000000000 part499 part444 (by decide +kernel)

private theorem part335 : Excludes 0x8000000000000000000000000000000000 0xc4040000000000000000000000000000000 :=
  splitAt 1 118 0xc4040000000000000000000000000000000 part443 part336 (by decide +kernel)


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem caseBBR (c : Nat → Bool) (hp : Pal 280 c) (ha : Avoid 280 17 c)
    (v0 : c 139 = false) (v1 : c 134 = false) (v2 : c 135 = true) : False :=
  part335 c hp ha (insertRed (by simp [Red] : Red c 0) v2) (by
      have mask : addedBlue 280 moves.unary 0 0x84000000000000000000000000000000000 135 = 0xc4040000000000000000000000000000000 := by decide +kernel
      rw [← mask]
      exact added_sound moves hp ha (by simp [Red] : Red c 0) (insertBlue (insertBlue (blue_zero c) v0) v1) v2)

end Case280
end PalindromicSeventeenEvenSecond

open PalindromicSeventeenEvenSecond

theorem OMA.solution : OMA.R_Green14_W_3_17_R2_H2_R1.H2 := by
  intro c hp ha a disj
  cases b : c 134 with
  | true => exact Case280.caseBR c hp ha a b
  | false => exact Case280.caseBBR c hp ha a b (disj.resolve_left (by simp [b]))
