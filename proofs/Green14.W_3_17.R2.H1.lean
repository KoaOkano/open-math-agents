import OMAReductions.R_Green14_W_3_17_R2

/-! The odd spectrum of the palindromic (3,17) problem
in Table 6 of Ahmed, Kullmann and Snevily (arXiv:1102.5433).
An explicit coloring realizes length 255. The branching certificate
excludes length 257 and centered restriction handles every remaining
length of this parity. Lean formalization by @KoaOkano. -/
namespace PalindromicSeventeenOdd
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

private def differences255 := checkDifference 255 17 0xc4080a002400103020001280014000

set_option maxHeartbeats 3000000 in
private theorem span255_0 : Covers differences255 1 9 :=
  checkedRange 1 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_1 : Covers differences255 9 17 :=
  checkedRange 9 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_2 : Covers differences255 17 25 :=
  checkedRange 17 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_3 : Covers differences255 25 33 :=
  checkedRange 25 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_4 : Covers differences255 33 41 :=
  checkedRange 33 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_5 : Covers differences255 41 49 :=
  checkedRange 41 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_6 : Covers differences255 49 57 :=
  checkedRange 49 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_7 : Covers differences255 57 65 :=
  checkedRange 57 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_8 : Covers differences255 65 73 :=
  checkedRange 65 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_9 : Covers differences255 73 81 :=
  checkedRange 73 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_10 : Covers differences255 81 89 :=
  checkedRange 81 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_11 : Covers differences255 89 97 :=
  checkedRange 89 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_12 : Covers differences255 97 105 :=
  checkedRange 97 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_13 : Covers differences255 105 113 :=
  checkedRange 105 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_14 : Covers differences255 113 121 :=
  checkedRange 113 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_15 : Covers differences255 121 128 :=
  checkedRange 121 7 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span255_16 : Covers differences255 128 255 :=
  checkedRange 128 127 (by decide +kernel)

private theorem yes255 : Good 255 17 :=
  witnessOfChecks 255 17 0xc4080a002400103020001280014000 (by decide) (mergeRanges (mergeRanges (mergeRanges (mergeRanges span255_0 span255_1) (mergeRanges span255_2 span255_3)) (mergeRanges (mergeRanges span255_4 span255_5) (mergeRanges span255_6 span255_7))) (mergeRanges (mergeRanges (mergeRanges span255_8 span255_9) (mergeRanges span255_10 span255_11)) (mergeRanges (mergeRanges span255_12 span255_13) (mergeRanges span255_14 (mergeRanges span255_15 span255_16)))))

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

namespace Case257
private def hints : Array (List Nat) := #[
[32639],
[32383],
[21333,32127],
[31871],
[31615],
[20822,31359],
[31103],
[30847],
[20311,30591],
[30335],
[30079],
[19800,29823],
[29567],
[29311],
[19289,29055],
[28799],
[28543],
[18778,28287],
[28031],
[27775],
[18267,27519],
[27263],
[27007],
[17756,26751],
[26495],
[26239],
[17245,25983],
[25727],
[25471],
[16734,25215],
[24959],
[24703],
[16223,24447],
[24191],
[23935],
[15712,23679],
[23423],
[23167],
[15201,22911],
[22655],
[22399],
[14690,22143],
[21887],
[21631],
[14179,21375],
[21119],
[20863],
[13668,20607],
[20351],
[20095],
[13157,19839],
[19583],
[19327],
[12646,19071],
[18815],
[18559],
[12135,18303],
[18047],
[17791],
[11624,17535],
[17279],
[17023],
[11113,16767],
[16511],
[16255],
[10602,15999],
[15743],
[15487],
[10091,15231],
[14975],
[14719],
[9580,14463],
[14207],
[13951],
[9069,13695],
[13439],
[13183],
[8558,12927],
[12671],
[12415],
[8047,12159],
[11903],
[11647],
[7536,11391],
[11135],
[10879],
[7025,10623,21333],
[10367,20822],
[10111,20311],
[6514,9855,19800],
[9599,19289],
[9343,18778],
[6003,9087,18267],
[8831,17756],
[8575,17245],
[5492,8319,16734],
[8063,16223],
[7807,15712],
[4981,7551,15201],
[7295,14690],
[7039,14179],
[4470,6783,13668],
[6527,13157],
[6271,12646],
[3959,6015,12135],
[5759,11624],
[5503,11113],
[3448,5247,10602],
[4991,10091],
[4735,9580],
[2937,4479,9069],
[4223,8558],
[3967,8047],
[2426,3711,7536],
[3455,7025],
[3199,6514],
[1915,2943,6003],
[2687,5492],
[2431,4981],
[1404,2175,4470],
[1919,3959],
[1663,3448],
[893,1407,2937],
[1151,2426],
[895,1915],
[382,639,1404],
[383,893],
[127,382],
[127,383,639,895,1151,1407,1663,1919,2175,2431,2687,2943,3199,3455,3711,3967,4223,4479,4735,4991,5247,5503,5759,6015,6271,6527,6783,7039,7295,7551,7807,8063,8319,8575,8831,9087,9343,9599,9855,10111,10367,10623,10879,11135,11391,11647,11903,12159,12415,12671,12927,13183,13439,13695,13951,14207,14463,14719,14975,15231,15487,15743,15999,16255,16511,16767,17023,17279,17535,17791,18047,18303,18559,18815,19071,19327,19583,19839,20095,20351,20607,20863,21119,21375,21631,21887,22143,22399,22655,22911,23167,23423,23679,23935,24191,24447,24703,24959,25215,25471,25727,25983,26239,26495,26751,27007,27263,27519,27775,28031,28287,28543,28799,29055,29311,29567,29823,30079,30335,30591,30847,31103,31359,31615,31871,32127,32383,32639]]

private def values : Array Nat := #[
0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000000004000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000000008000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000000010000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000000020000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000000040000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000000080000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000000100000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000000200000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000000400000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000000800000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000001000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000002000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000004000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000008000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000010000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000020000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000040000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000080000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000100000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000200000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000400000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100000800000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100001000000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100002000000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100004000000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100008000000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100010000000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100020000000000000000000000000000,0x100000000000000000000000000000000,0x100000000000000000000000000000000,0x100040000000000000000000000000004,0x100000000000000000000000000000020,0x100000000000000000000000000000100,0x100080000000000000000000000000800,0x100000000000000000000000000004000,0x100000000000000000000000000020000,0x100100000000000000000000000100000,0x100000000000000000000000000800000,0x100000000000000000000000004000000,0x100200000000000000000000020000000,0x100000000000000000000000100000000,0x100000000000000000000000800000000,0x100400000000000000000004000000000,0x100000000000000000000020000000000,0x100000000000000000000100000000000,0x100800000000000000000800000000000,0x100000000000000000004000000000000,0x100000000000000000020000000000000,0x101000000000000000100000000000000,0x100000000000000000800000000000000,0x100000000000000004000000000000000,0x102000000000000020000000000000000,0x100000000000000100000000000000000,0x100000000000000800000000000000000,0x104000000000004000000000000000000,0x100000000000020000000000000000000,0x100000000000100000000000000000000,0x108000000000800000000000000000000,0x100000000004000000000000000000000,0x100000000020000000000000000000000,0x110000000100000000000000000000000,0x100000000800000000000000000000000,0x100000004000000000000000000000000,0x120000020000000000000000000000000,0x100000100000000000000000000000000,0x100000800000000000000000000000000,0x140004000000000000000000000000000,0x100020000000000000000000000000000,0x100100000000000000000000000000000,0x180800000000000000000000000000000,0x104000000000000000000000000000000,0x120000000000000000000000000000000,0xffffffffffffffffffffffffffffffff]

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def moves : Rules 257 17 :=
  cachedRules 257 17 (by decide) hints values (by decide +kernel)

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
private theorem part1 : Excludes 0x100000000000000000000000000000000 0xffffffffffffffffffffffffffffffff :=
  finishCode 1 6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part6 : Excludes 0x6020010000000000000000000000000 0x1f925fb2819c8c0460200100000000000 :=
  finishCode 81 0x1dc4a188440bb060330973430aeea20e35e3f2d5434267743bca299852695524b07643c861cf1ea824869998861a15328e3640fa1e52e21a133bc6891b99e3d34624c7750d08a05446712c0d095365248e35683292455b2994f1f29957432dca65156a99676098441004b9aa078f33ec86515695ad4933125c4a66d3acc789699a0754ca879156a408024878f6a1345328686345a8d4c6e1a1871ac43616c653713ca5f3b2a92d6851180524c0a12b5a95604f99463c2c67d4b0d1728f5e3ec1b5248e35c4f19f5686c49432c2ad3c7a5cd203aacc491898ab4f1ea49855aaa2e8a3b8c62c291b98c24212b291b69d94eea1a16014059dca6504c94c50ca78f3d0e8b1a1d88f25cd89236d8126a655a12c4406da69592e6783126120953583656b40bca296169e3d8042ac78f156b1265329d166219e3d6aec49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part8 : Excludes 0x6400010000000000000000000000000 0x159affd640145c0064000100000000000 :=
  finishCode 29 0x481805f0f1eb22b8a63e8d21694053154d8827556248a6c55a5539102a49624829cd33307dc5a2a1065a4e653289c54bec490d8ba0c49532b0760429a4d83b220410ac419c56d315aaa87ceb29695328ab41960cb9c5a881150a98ce0a4d102a619c5aa3f1be832c6d73125c5aa651b5cc49065ab80cb53164624cf1f53286c4b4a87994aa881156cf1f43cbc7e6249d65102a65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part9 : Excludes 0x6000010000000000000000000000000 0x14967f8000140c0060000100000000000 :=
  finishCode 153 0x6219c440972601c0973501303c7aa06699492f1f0c3a28f1f433c0796248215c4b293483ea49327a15510225d9c5a6992bba205e3ea8150ae151d4cb207419a865716ca65623ca4d066b8b48a257743cc81d33480bd1020cd2a3c0cd3c7bb8e83980999102c493c7ad5c1a23738f1e6855002ef1e3caef29951020cd9a0601a83c7bb8cc3a06698d0a0d1571e3f21e5676a65440a97d6572206068bc7d0633c7c19af1f985aa292d2bb8fa268a6008e213b4e41a2a5f2d2a205a8624ca5f068a995273306d893299547e0d1532c881315c0cd532b50881433cf1f2bba994d33297de3ed0348c00345942bbaf8ae169543f1d652e6c49429a5ce624a206156c78f6517c4d18c2d2928c1b92e6c492a6c971530c8179882a4b492b12583688188a7298fa1585a5600eca701e3c14ee2d820ad37532b4848a226b9c5aa1f924a09f381a6f29954a68812bbc973716a94d2840089b1e3d2e6881235a2037392e6e2d661102a1f86a6d37532c78f96aee2d4b9a00c49525c4575329e3c8a334e44e2a653ac8dcd4c526c18732d9a65c5a2a74b9a2054434cca65150a5ce156b06d4cad02809034878f5a1a8156b980cd81a2b218d2e969532a206531ad5c1970345f4651342f0b4ab57967656b62499ad4cb2d5d89267940bcc25335b49d6ae57732ec88196aea656248ccd646ee2e8d22d5e4408ab41a2a43e88822866b33ca87e5328c2c66646b40bc5a560fa8d600199348d6f1f2d2a2056770ccc8d60038c9a017121a05d83e46b106cc490a3996d6aec2d0688ab633c83354c2bbc4570689695102d434857781a257788ae2ad8c9ac3933cb508816914ca07f924a8176248a5455af1f868ec4909fc2ad (by decide +kernel)

private theorem part7 : Excludes 0x6000010000000000000000000000000 0x14927f8000140c0060000100000000000 :=
  splitAt 1 118 0x14927f8000140c0060000100000000000 part9 part8 (by decide +kernel)

private theorem part5 : Excludes 0x6000010000000000000000000000000 0x14925f8000140c0060000100000000000 :=
  splitAt 1 113 0x14925f8000140c0060000100000000000 part7 part6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part12 : Excludes 0x6000120000000000000000000000000 0x149daf81416c306180124800000000000 :=
  finishCode 41 0x2c0ce2a04b93c0e83c3a98973134ce2d4aec63f34991b6122a9944baf1f4939d0a65820e699514bc7dc5ad3b4b9af0e2d904a5a778f8a4528f380d434ee78f965ccd318fe624b89410e8794b9b4ecf05d0f0e685424c2ad4b9ce2d4e02631a650aa2a74b9a10e78f9a4dc5a2a74129f8a631258c716993e6988df470ad31868a9693c3c50f61cb4ec8daba3f8fa0a9ce8327b8b651fb4ed2df20dd86e9499682e2d3c3ca65327b8b6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part13 : Excludes 0x6000100000000000000000000000000 0x149d2783014c006000100000000000000 :=
  finishCode 153 0x14c671102c41f84b95f12d266f94cac492d29e8c497169708498c9e433150cc293c2c9710449535d4541c84b0c949716a4ed4ca2a71568e363aaa1fcf0ed400fe7129695c5a11f69db0dd28e1b1926a64f41bb8b5a7691f90fe5a55918c2d2a18981e0aa1e1c11f34ed2d27894a4c45169da5bc11334ed266789616cd3b78fb11e10aa4e4ef296942dc7394b4ba89696a17c5b14ca38d8f120899a72e2b1538a9e49d9e1de3ec473aa885471b1e1cf0f28850fe38d7d12730ab4f0ae2d3b4969560153c68542d9a6411f38b58867160540972d4380b6268f81a4cd3293980cac47412b0a5e3e5a32d3a99678f9e00659c4ec292d3b4ec8da6854c104b299528e59778fb125a7720954caf1f2afc8534b9b4ed0f2a653c14ca9c1e1c0cf34ecabe81d43ca0966168c2da7695b461293389d04ac49421a92526725cda76e030b669d9a4de3e6993a3cc250c7a5cda76d42609c165dc4f251da7627f43ca51e69da5c6433a1e4c2610b78fb4ec10b25cda76a83a8d4390a650d6cd3b01eb12455a2a1309ce270d89e1da771e1d2c720b81449e0d3b436b8ae2c7b06d86f163c2df21fda76787028c45109f8d4d89286d3c39e0c49424b8ae2c7b06cf0e91f8b1e841e0b234ed2b6371906e92161a86c48a70d4c00ad2103fa0dd6aaf1f4a3cb4378f9e0f1f417c327085c13369d86c5343118c337a18759349c87f69d914d0ff30958920ad5114cb1a4d0931d66153ca656a1f04c1783c3ac0e415fe69d968dfc2710dac4990bec49810aa65987208548f89b455b3c7cb1e933980150c10f2d3b4ede3e95d836211369da995d4331a4532a302a74a3c291612cd1f78fb1266128a45e3e871691a77312454ec2584e284961f914da76c494217403dcc35438a1fd18016cc47148b0b668fbc7de3f0a442873c7da76787 (by decide +kernel)

private theorem part11 : Excludes 0x6000100000000000000000000000000 0x149d2781014c006000100000000000000 :=
  splitAt 1 101 0x149d2781014c006000100000000000000 part13 part12 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part15 : Excludes 0x16000000000000000000000000000000 0x1c9577910000000000000000000000000 :=
  finishCode 91 0x671885818025ca80d41e3dbc342ca6505f83257c532c6692d282f436738b52e6c474a185a0999e3e88104cc9738366d4330a603257c69dcb571aaa994d325a5431c570a4587e971037b0e6716a99634c809662391342d6b574b98344e8b25c41325a5616a2056ae973751202d2831419a28d86e296951da56e4b79900c561cc96f5abb125500b7ce295aba1b4512d3b9d4651a44c0f1e0cd0688cbe5abb4ec2eed3b9403102ee78f148cc19440910d89296151aa92d873248547ac25440969504531242d2a204c57299588a291619c9229007f988e87f51381f6532b0fe624b11d88aa6590fe85b96aea6561285dcf1e0d160019295b9a7687f1c68a24f1ea61871a1776a14c068a68a016955c50fc97369da20411a78f04b9e3e046a996440a134e04614a688142020b1d954cad374b7a996624b095a76a1f624cc3f499b8b5a76a278f1ea53490b83a189285b3accd3b0d9c75942fca653aca98436684d9a7678f624b00ac1e3c15334ec31619366144440cc494b99a6589325cceb285f3c2846e09f942d2e629392e6b57 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part18 : Excludes 0x6120000000000000000000000000000 0x1f9a0fb7e1a4800000000000000000000 :=
  finishCode 31 0x1a85f18072017e8a0ab52e734ed8868815329de5c5334ed0bec49532a0a6532b10c15a78f4912c5d09c4010be78982fea352ad8a44afe87f624ca650d0ca6543f8e35282bfc38d61c91ada768811c6cc4912ca8a5a76a65580a0721892a6540103e8499c468812bf8a4669da5cd2e70dce624a5cc6e72995892c498eca1a1440c77988d678f440b12455a689 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part19 : Excludes 0x6100000000000000000000000000000 0x17982f956100000000000000000000000 :=
  finishCode 155 0x1d867174650972d42980c5590d2f38b58928812d2a206560d454147aa5343fcc2541bca8210c3f33cc8712c7aceda773c7c8dab3b9a76c49943aa6541bba88a2c856b9a760b3344a8888101fca351a98ab54aad3b9a42a3d236a8d510316950ff0a240fa88105995ad80751485a0cd69719892f1f236a94cd2aa299c52837436ad08a295633db12652fce295316c54071a14b983af1f62491ad883312631abc7d4be449806ad3b61bb1048d64499946a1c058018a78f8b165a59102a6118649282fd4cae2d2d2a20580624c67905faf0c3f9492461624cd3b532b805a5910278f530b4b220489b3064cf2c02c0d41e878290879344c94d33c9dfe69da995086a65908667969da5ccf1e38d92e267b78fa5ccf1ed3b83269733c799ae71499ed49310d52e64536517c4d0942d2b18721d6544f38ada6278f4b8a1fd89285f4018870a0de3ec493c781162bb963c55ac4961bc5772c7bc7d0e2c4963180056c46d15695364b0a4e5385299e3e03895fd2e6d3b8e0581286011025778b3678f3012c41dc925624a17da7715fd86692540fb1046e7292d24aa65293b125004b189278f236ca4b69dc57f04ec1030d1909dc5a46d624a99524b11b48d6c492c1a2056060055b2155c5ac49622a5ccb3678f301a77156d2e65438afe2ad924ac49716a1b6156b4e5292769440b00e438b63c78ab4f1f114e671a46312d30ab51020bf063b80b01981a73c7bc7e43ca8754caa499645312d338b5102c492d2928a1d96aae2951ea925e3ec49622c63351aa0bd652a610a5cf1f236acf510251f9a76a652d2867d4c5f11031e3c1625a56311027899892e2d49ca5a6716b12451718acf1e0b150eb125585f034e78f9a765a53c7cd3b61fc08b3bc9e3cb4a881 (by decide +kernel)

private theorem part17 : Excludes 0x6100000000000000000000000000000 0x17980f956100000000000000000000000 :=
  splitAt 1 113 0x17980f956100000000000000000000000 part19 part18 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part22 : Excludes 0x6030000000000000000000000000000 0x1f934fbfc1e0f00000000000000000000 :=
  finishCode 35 0xc02f8d42a00bf4c1743c3a9961569d16440a9964b088b34ed49236544091b54bf1da586e8810b3c9735ab9e1cd12982d5d102689989295b3c3b4ee493867d30441d83c38dce440ad4da769732c0ef30225a7609d910217f4115c4a0ec1b5a2046db31250fea5555164709fd8921a169acc4943fa8a5a77027428e1a1530cc49532a204343299524b389407238d59da135a76b57 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part24 : Excludes 0x6410000000000000000000000000000 0x1793e7df4164100000000000000000000 :=
  finishCode 61 0x220a61c0582f8b574b7c78705e96955052128f220433e9834ed743c38ab64a3b125c5a785440ce2d3a4c969716a20524e9834ec4ff1e1410e96f624b0c64408dad24ea82087875f1102a55987228d05eb00ba1de6156867e61fb125c5ac499c5aa550449e266248a34eea19f716a10e2d91029474b7af8e2592768816249695893268787532cc1928f8dada760bd2d2947e716a995892d3b69dc1ad532b124f0eb577714c058c8812d2b48b62b8bc3787a312436287784fea1d9492a65235cc49532867d4a734ec45e97143286c58920bf94caa659892a4b05f89fe058b125804b7c2ad05e928a29835aa5f532b124ec5329383079a7644d4b4ca5523686b5a77389443a1ad (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part25 : Excludes 0x6010000000000000000000000000000 0x1597279d4060100000000000000000000 :=
  finishCode 109 0x2e8b812e5105416aec01e1d8c65107725a45420bf33dc2ad33dca251b9c8815a999ee624a5a54a2b536118c7d017e822b8b6312652ab115a76a650d686c5dc532cc49230a2054cb2c8d892a55236a99644095362d286b54ca971946a9351b986b54cae62585a5624948e228984d44e95b807ac375aa9ce545322052d265f236c881461585f124e963156cc49532910c17ed338cf72995892d3b88c2d332afb28ee298703008815f1227249d4ca0bf2d2a60c4594c667b531ce2d49391ac8d70dccb02a654b9b005a54c017e9138f0ea658f0f25cd706a1103c16aea658f0ec4994cac3f42182fd2e6ae300c6311e31fa9948d684305fa30c49418ca5f412c613623b4ed4caaa29554cac499c4aa29315a8a605fca65235c7875aba44e493a1e54cabe30098290c2312633c82fd183f08daa518f0ec493a2ca4d8e8aa5188dac4905f91b653282fd10591c02152ab0654cab574b9a8a6315a9554cac024ee60fa0bdc5a86734385a661ca5cd38301a6b30656ae65f4b9ac08c3f88794a4c9713c3ce2d34391b433f214d6ae78733dca8260a61e1d49b3124d2ed3b33d99e6421b0fd6aed3b88dae2d532b4d671691b5a76b57 (by decide +kernel)

private theorem part23 : Excludes 0x6010000000000000000000000000000 0x1593279d4060100000000000000000000 :=
  splitAt 1 118 0x1593279d4060100000000000000000000 part25 part24 (by decide +kernel)

private theorem part21 : Excludes 0x6010000000000000000000000000000 0x1593079d4060100000000000000000000 :=
  splitAt 1 113 0x1593079d4060100000000000000000000 part23 part22 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part27 : Excludes 0x6000001100000000000000000000000 0x1591b7d10411540c0c606000111100000 :=
  finishCode 65 0x761885d1a425c9a665328dc41a2682985737d17c360b4a883104784b9b8b5a6f04154ca02550fc10594caa658a233474ecac49532cc41624825d89315fe440ae6ee25cdbc22cc24569d9a141a2661805311b40eed3b064a9960119a2da6ed3b4c10072024f05dda765672bf9a8922984ab721c452255b8b1ac49513ad89e2a8a60a45c4f389546a84d6198e3584b2996619a8d6236ce25093a8d5a477198068b12606484ae1c684ae23683254c67068730fcb4a38d60cc5a5624cee378e2398721b108791b546aa610689e26087a985646a65066c223622818d4ca46d67158065b0fe532b125a76d371b5b1262d2ca27716a9946d6c49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part29 : Excludes 0x6000001000000100000000000000000 0x1591d7930901500c0074001010000c016 :=
  finishCode 85 0xee298823888814d0477197da76c4753291b49725a504fcc4125c8345346614453299f586b389d88ea493c2827d43f306cf126539a7657f871ac1b713ba8d4388a655912bb0a4cb4ade032e06898ae25c8cd46ba19d9c459052716950c25cb4ec687311c8a67798cbec2d8696d3b6148e34ca638d8b4ad43a8d2338b6032d4cb12e4d32453804ae2550e92e4eb31a641a2ce34ee69ba874516c4925ca18c492bfb4ee69b99354cb34e41932e8d3b31097266f94c21ad860eb29622b12585b19bda8331c45328a4669d91b49720cb6612c5d1d8624c60d621a17d0fe78389e231b12420ed3b69b80e66929d5451613769daa805594aac495a9b4ec8da57f9892a2968dcd376248a1640f827c8dad3b711984f09720cb3bcc96969bb1245161158f1275952f95ce69d91b49729a1de60ce913671386854c5518869dcc4904f92e53c1a180160d69d55862789139b116618c4b943fb0b6715a1fc8dad3b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part30 : Excludes 0x6000001000000000000000000000000 0x159197910101400d00600000100000000 :=
  finishCode 93 0x260ec1e1d886a12e6ce3a8bc03346d7197d102d3b5a9a48d3b881e08943f8e36716c87f624832509331250be0d1149cd3b5aba00682c0e42885735512403fc513136a1c411ab2311e2299694686099229cc39044c87161885fe289a9855b590112b57987e19d04ead5e612cb571e10ff0ccd6a6d3b4916ae58d92d20cd61ca1fc00b3095686c39235b12584b289d4ca0d169dad5ddc5ab950c49426a2046670d0c1a32caceab027584ac491999c0ee2d5dc44409dd60469695c5a69997c0bfc0cb5248a05892a65306c07d3aa9e24112ac34828d624b4ecec065b096235a996613c09f532c12f62496010f909a3434b9b4ed6aec4270e225cddc651345f14971165102e2d6189694cfaba198661f834497223798869713a2842dc5a881068c881715c44925cad4c1a20c98972ee0676532a2054cb34dc6e6e219f6149834509b11ada6e699440ae8ee18888140bc9612d291ad4c20d18e727792d2b88de25a6612a16d0fe0cd5b12d330c4eea4538c26c254b4b0e50ff2d4da730db588e881 (by decide +kernel)

private theorem part28 : Excludes 0x6000001000000000000000000000000 0x159197910101400c00600000100000000 :=
  splitAt 1 68 0x159197910101400c00600000100000000 part30 part29 (by decide +kernel)

private theorem part26 : Excludes 0x6000000000000000000000000000000 0x159117910000000000000000000000000 :=
  splitAt 4579 92 0x159197910001400c00600000100000000 part28 part27 (by decide +kernel)

private theorem part20 : Excludes 0x6000000000000000000000000000000 0x159107910000000000000000000000000 :=
  splitAt 1 112 0x159107910000000000000000000000000 part26 part21 (by decide +kernel)

private theorem part16 : Excludes 0x6000000000000000000000000000000 0x159007910000000000000000000000000 :=
  splitAt 1 116 0x159007910000000000000000000000000 part20 part17 (by decide +kernel)

private theorem part14 : Excludes 0x6000000000000000000000000000000 0x149007910000000000000000000000000 :=
  splitAt 1 124 0x149007910000000000000000000000000 part16 part15 (by decide +kernel)

private theorem part10 : Excludes 0x6000000000000000000000000000000 0x149007810000000000000000000000000 :=
  splitAt 1 104 0x149007810000000000000000000000000 part14 part11 (by decide +kernel)

private theorem part4 : Excludes 0x6000000000000000000000000000000 0x149007800000000000000000000000000 :=
  splitAt 1 100 0x149007800000000000000000000000000 part10 part5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part34 : Excludes 0x4801010000000000000000000000000 0x17379c9235506c0149010100000000000 :=
  finishCode 73 0xa0240b61e3d9c246aa8695696c6890d0b4b64b49a24147298b238b6432b4b58926953d16aeb539a4e855531914e4b4b4e410e10f9656c43624ad5da5a963c7d6aea658d2a679081c37324682954c671644b1ec3439a54d47112d3142dc5a199886e45359dab8a658b2a391928ab55532b0954cb38b567660d616b4b588ed22d8be2281539676e2d0d09a254c721543423738296d33716b896532b4b50cad339c5ad2d3449a89838b42bf125da6614786a6b3b28bb50b61b048d13bc9596168dcd646aa25666239e14236a25306c66d9a66a6569185a60d8cda0052bea4c4f0a95958ccd391a9800da66a3f3c2a60e2d612c391532a1e58924976999980759676c43696a14d677145da85b124246bf8a65670c6318ad836e2b6219614b2262b8cf3389467238162198c50f30e46432b4b586ad335329e8007841a56d08981c585a6792c8cc2d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part36 : Excludes 0x4800014000000000000000000000000 0x1e271d96901476404c800154000000000 :=
  finishCode 47 0x1e0481ec3c7b48e63884971629da642ca5a54cb2d5d89265d512a11e512a1f4572d423886b9046689246aa06898ed2a655a189319ed2d26954b4c1075abb1250b321ada86718931a5547668924b8335463349d49a49742ccd3362499e50faba2b8da2d8f62982cb590d2b311c146b495329a2491b19e6624ac64eb2b4d24682760d68334cf3306d056613621bc7d8920cd16599e62468b15893033458a0cd858ad23888a0335681c88a3e78f91bcd12a57889aa5d78fc46f0d2a99549b2994d12695435c45362499e4d12a65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part38 : Excludes 0x4800010000000100000000000000000 0x17271d924815740048104101000025004 :=
  finishCode 133 0x3c0c0240ce1e3d4c7b16825caa82a1949a859050923634bb124aeec49954696c4972bba1f58932994aeec1b8c2627714aa1f5a3682325cad048d6605a315dd2c696cb353aa9e14017207d49ad2d526c841624bd8a6350e62d8d2d94ca68962492e45a648d624cb23318bc7d0f269725c8b4cd2f292414a4b925cc697418cf1f24b92e5981c4c697618b12419ad420849702cca651c4a92586319b5e3f051c62634b6a0cc6914cace330980b4c19aaa312507b21cda3734ddc4aa29183c44d69ba582d35315c046a11e0958db5c4f0e252cb0864712c35519c92911bb4b47129a2e8e2297669b8e24437389d88609b226c12b52e824d25315c503ec43168a98aa338d2d903209325ca68d37804a425624826dc4f34b413ed2d803636d25ca95484b3124972ce348cc2d82d306685e6226a1cc342c4386c2900b4cb436060f05e506a87d4c13c43985c65aa86b670eb0a64ac98acc26307388c17969aa1cc35a1478696e2590fab2b110824d47e81925cb18785988609f52ea56601e81155425c895632fb0d4afa09f32fcf6298e22600cd25cb18aa30d6518a99542a82b624a1cce8b28c54828198132e2778fa98c8def1f9805b1544c014a09998923739a6ef1f344cf1f34bcf1f33130532acae712a1cd8923079a367a26056d624cb2b4398816712a11c89b184c07a09704fa856624bc7c19a4b963019a982a8a621cd0faa15814246f9482a659892a4178fc6978132c49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part39 : Excludes 0x4800010000000000000000000000000 0x16271d924010640148000100000000000 :=
  finishCode 143 0x3a1ec4b9b88ce3904b9162c497066a38c4990e6b5724ba1ce716b00a034de162a8c56ae78f5d1c87c10a731250f22d115095ddc5b1235c5b1234aef125dc5a9a28081f8e7228d12da9756ae6c2f076992b2c255328b456563731c8cc49532ce2d209c6316248b456aea65500805416aeb42609030017b053c6953c78b4604fb12414b1a54d0f29941422d194cac493c79e3e427c0991b99e3da873130601892f8238d212345432d4cc622d143ecb532bb98c63c29d945a2373944a48d318c87d591a99580532ca6369195dc89b1da58861a13188b454cabc2cee42395dc6e6689830301bcf0ac496a19c47019a18790fab5724bb8b65914bb38b47125359a5a075716a975205716af21cc52a679985a8475abb1256af1a54cf2a03c0903d878f5319c7c0972960b4e2be9a55cc43cc1a142aa87615cad5c5432d5d585abce2d498b4b4ed248d69149b15c4ef22a140bc271532ad5dc5a08594cac491509234972d4330389852a577066ab0e27851ae2d526925d49b34ce624993d0d6f6298b22e8f812e414b3c7d6ae6891509a5414b0a85e3f2d5d89269524bc4b9010cf1f066a99492e4b96a14930e254cad2724b8334cd73125a36f1f5ab9a552c3d0d2aa65819ab5733c833625cbc7dec5509726898342f1f96ae689066cce3d8e2125e06692e5cc611892c61a5c92f165546f2cf4afb28fe532a164d12c49819ad22e8f62382a14accc4970fa99492ee1f8e72a65716b8b624bb12492f312491b3125c5a577 (by decide +kernel)

private theorem part37 : Excludes 0x4800010000000000000000000000000 0x16271d924010640048000100000000000 :=
  splitAt 1 68 0x16271d924010640048000100000000000 part39 part38 (by decide +kernel)

private theorem part35 : Excludes 0x4800010000000000000000000000000 0x16271d920010640048000100000000000 :=
  splitAt 1 98 0x16271d920010640048000100000000000 part37 part36 (by decide +kernel)

private theorem part33 : Excludes 0x4800010000000000000000000000000 0x16271c920010640048000100000000000 :=
  splitAt 1 108 0x16271c920010640048000100000000000 part35 part34 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part42 : Excludes 0x24001010000000000000000000000000 0x1d3bfc541592448341010100000000000 :=
  finishCode 101 0x140481343c79c0942d5d0454110208d94c6a6552eb49c30eb2b86e6b53520c969624ad4d44a187716b8b63f0dc62490838592d2277520a95d5c5314bb041c1260a113bc77d40bca6552e996e518b87d2d2a65138a48a8024e696a584ee2a410c3a994d81b9cd33520c5910dca88659db8b5c5b2995a6636b624ad5ce878fad5d8c6248dad48325a4b42a31349c0a54b4c0a5716a08a62a08813f1242514cab53902e65b531b125a4531ce2d34c8de48d72cacada969051b48c22e837d902e81d43c829d0f331254c72d4e1b990e56a738b4872879532ae8c493b0c1b532dc8793e124330d853286e6618919423e3736999e88418cee3796249195a5b06e4cb6d2338ba318a206e567b15f4cb68c205e210b485656d2198927619892c3f8ea265b33b99de008c03b4b8b8ac236373699b125a461189306e50f2d3380d61071b9809dc4a46b31295f5a5b253423e46b1b9b4cd89286119662499a4d2646596563796d14c511c5ac23d8c49831aa510dc99dd9c624cb552a48dd544b29444eed319652a511bac1b95118433bb1262b886e589315c437331246e637590f2a65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part44 : Excludes 0x24400010000000000000000000000000 0x1d3b7f644410548244000100000000000 :=
  finishCode 57 0x180681207b0f1ea22d0be0acc6d72204d328619a466611b5a2054af38b4d16699532ca410658acc52b032d2433174532b18f6194e49c9e34ee2865159b28b5791020cb053cb571bcc781065a19412b0dac8d6c1f440a1e5c5ab57731ec0659686624a975c3e68b78fcb57053b87d463029c526a232866978fce2d440832de3f2d5dc5a0a7856682240269440a99614a861d5c78f8ace716a99412aa658cd2a2318ba24063f811a699430861c52ab606d6053a904d326c19a54cae2d9e3e84f715b48e623a99678f861c6d6e2d432c6994b0ca57159a995105106d6b57532ce2d0659a641970cad03ea65624832e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part46 : Excludes 0x24000014000000000000000000000000 0x1c2f3d54951404ca64000154000000000 :=
  finishCode 99 0xca1c0d22d5d102da390b439a66577069a88922b87e18963b0a0d5a66a653c69d86228b4cd4caa1f987321f547b21de2b288fda5aa6522bca1f49cb125a5a922a0e62995b45d1846908a728c5892041022996c1a63790daa00a3592d218d6249e3c0fe45750fc96140b833e3c6c0cf40145721e548278f530a7833384e278d3b0cba0ae63c7a98c6f2a4d9cc624c0d315cc78f5a9b98e43c0d230c6624834cf1e2c53f12c3213c8aec493c7ca1f40ba5850e731243069828886190fa83d9a66c49291cf1f7212bb1cf45728619a5a8175108d0ce03516ae763c026373100690f1ea6194ca2c5235ca655b0ec3034d4ba781858ad2d430cd2d52e9e3d4c3033de0720e9b1d854ca2c5069a7878f699ca653c6a8c600cc0150c1a99419ef0240d21e3dc815cc0d33c6ca25518acee52ea8ae006985d4ca0d330bca65067b98e4368d2060e532833c1a6a82cee52e915d4cac498ebb299458aa5d94c678f532b4b6528a97457278f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part47 : Excludes 0x24000010000000000000000000000000 0x1c2f3d404410048240000100000000000 :=
  finishCode 131 0x7b19c780972d0398a0034cd0b25ccf1e4658b0a881342a5cd10480e83c79f897341ac87d712cb5371699dd83e6858aee7425ce60faf8cc1d764ae9e04d0a78d88d725351032574f024653c7a5ce440834c19f348f83c088194ca78f4b983445a2881807a25cda4f2884d32e2d0c3bc7d0f2a658ca6e2d78f9a1643c9a656aef1f9102699153c6854b9834d2840164525c78f22b91ad2e718ac8228813c7980cc25cda6f22054bae2b800a26b532b0dc0ba88194bab5769b9e3e4b9a20742809735c0e06506e678f5aba906716a205c570054c4aa65561c84611c1b99f8323986ee2d03e9e3e19180f54ca32398829028c6624833cf1ea35814aa31624a1865208d8cf1ec49986286152e833cf1e78f86e6e42908619646a350698dcc0fb220464603506995dd8c5910fa32386c6a650dab87e594a20589311946f2881681b469148067834d30526cc49716bc7c51e18778fc88114982756af3c7d50591a670055a5a00f78fa4952c278f235a808e1e3d6af3c7d496b579e3e14d40ba93da5aa2b2bbce2d440b0c651aa1acf1e9028f614a95dcf1e54298a3d00ace2d78f829c312f1f94c27815abcf1f232cb551baa20414e0d3531702f1102d02d89029750fb307411a78f232c2935328dd40b3213c19e8179c56577069a975a4149829e069b10641eb906c21f65328dcd4cb033de3e0d31b1ca65691c848019e5778f1e623c7e525a8f65209e3e520a9954a7287d86e83d (by decide +kernel)

private theorem part45 : Excludes 0x24000010000000000000000000000000 0x1c2f3d400410048240000100000000000 :=
  splitAt 1 98 0x1c2f3d400410048240000100000000000 part47 part46 (by decide +kernel)

private theorem part43 : Excludes 0x24000010000000000000000000000000 0x1c2b3d400410048240000100000000000 :=
  splitAt 1 118 0x1c2b3d400410048240000100000000000 part45 part44 (by decide +kernel)

private theorem part41 : Excludes 0x24000010000000000000000000000000 0x1c2b3c400410048240000100000000000 :=
  splitAt 1 108 0x1c2b3c400410048240000100000000000 part43 part42 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part50 : Excludes 0x84400010000000000000000000000000 0x173bdec44010542844000100000000000 :=
  finishCode 57 0x5f150281c4532b289a3405a5345cc493c79a4c196f60a8634cb12678f86d452ad0300969837af1f5ab832cf1e85992d20cb40fc9450dea205287b10c61fcf1f1bea1f4d266695d14a72c644ee0954b4ac6604ba4078f810ae1f8f1f30086b910248d3c78a842ff292c50236b440b28d2388f62682a18cd278f0de9a2cb4a7a3c7e0dea1e5a371e3de3e1bd042cf1f2a9b125a6e2950659694f1f1a150ca2a12a9cf1f69b85ccf1e48d4806d7346c30e78f515c699716824d6ae78f9805c194681443c7ad5d42b31250fac41716a20492ea2b9c5aa574409e2411b38b5102d2d8c36a15312954d882e2d0c38a54f1e4979c5a0cb3c7ad5e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part52 : Excludes 0x84001010000000000000000000000000 0x173f9c545538442941010100000000000 :=
  finishCode 41 0x50120380f1e942d5d840c3b8b633499ed102695595c881693cca2d8e21235342d2ca57624c65d532b06ccbb2995892d332814931975892d33334c66b50e8dcdc3f19a4cbac1d335969659d99e54cab2b78fad5d7c6714c4d1302d2b12634a998b539a4668734ca994d33308881230cb3b3439a556c32ec37d5a9cd33595b8b56c6d092e1bd8d26699532cd2d98861bd532cd2913bb124b4a651891a881 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part54 : Excludes 0x84000010000000100000000000000000 0x173e9d064811142c40100101000005284 :=
  finishCode 59 0xc0340903d878f531a833186f1055a5a48d44092e4aeea655b0b4a5779892873440829cd1319f63b4b89d10268925ca8c669b925cd164b9720b4b15dd463120d4cae23d8d412e50424bab8f1f440a996420984d4668319656c499e3e5a552fcf1f6249a654c5911031694d123759102a15520895624bb125e3ea651b9a588815b0c6f21dc33237d51ecc4933d8dce624ad8d379e3e48d069c5a525ca98ce2205ec5d14425cad0a298cbe873527ca49696ad3633eb4b54caa33949236194aa65f532825e713b06d89226153299f59c741c4f30d5646a5f62092e54ca0d35d14830e0547a87d25c9b08599836b3b43eb12630e9a2e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part55 : Excludes 0x84000010000000000000000000000000 0x173e9d044010042940000100000000000 :=
  finishCode 139 0x1d0e225cdec671b425cb90e81a663c7ad5c1a6b228fe437a5b52a278f624a106532a2048872d5d892699342925d402d2a996520a97492e78f4c14ca96d88a6483624b48e612af8da288c359102577069925cd26699532c0d3229c5775329e3c92e5a52bbc881069b28a6358b23a05a534acc49716a2041a68819a6a83d439b12570511c5a881595ca4106992341a7292d48296d80123750019e3d42aa41451102819909ea3f3c7a994702a658f1ec6358e4300e8240497069acee691a8f4f1eb579656873852a1b53c795dc0ff21ad8920d3624c86124ba40b57620ca653c7a996624ca653c78e05a852eb588c034c2e70dcd83728c586b3125462b570c49e3e716a8c589225d5aba08a82204f84a2c63f34c8d8d4cae80df6342b12491a87d989278f3c2ca35624a1e491a78f741b4691a833ba10661ba1dd4ca7858ed2c2933e8df65328d8cc9a78542acc493438df4d2b3125a048100540f1e6c220634492e4ad6577711b45301a687988a611f4409a2574494c1b5696914d4caa3550e92e40ff18dd43ac4943cbd88319c5aa654328a562c6b1254ca64590f2453531ec5d16425cb12634bb4b6621a16405ee2551a9236716ca4b34ba2041a718554964b9246bd8e20a8669ba2041a657725cb48d42206435a10c5428793b4c66d4409a24eab1a55a85ab95ad06b034da67388f63a04b96d0cf31a6492f348d0caa652d2a206336a1e54c65142b1a1d102a659e3e687344ba0ca034c6b304754ca497515ca3391033280d37b092ed239e3e83150ac5190ccb8b5e3ea65570972c35814a295134ca2b (by decide +kernel)

private theorem part53 : Excludes 0x84000010000000000000000000000000 0x173e9d044010042840000100000000000 :=
  splitAt 1 68 0x173e9d044010042840000100000000000 part55 part54 (by decide +kernel)

private theorem part51 : Excludes 0x84000010000000000000000000000000 0x173e9c044010042840000100000000000 :=
  splitAt 1 108 0x173e9c044010042840000100000000000 part53 part52 (by decide +kernel)

private theorem part49 : Excludes 0x84000010000000000000000000000000 0x173a9c044010042840000100000000000 :=
  splitAt 1 118 0x173a9c044010042840000100000000000 part51 part50 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part58 : Excludes 0xc000030000000000000000000000000 0x1f2a3c0480f01e03c0000f00000000000 :=
  finishCode 133 0x3a0dc6814aea5d761b06712e678f96ae0115329d74cf6a659843c7acae5abb124d2e0a7531cc49716a9964ae826413af1f3c7861e78f8dac13a973240386c1462ce2609023087343eb00083716c78f5abcd2d4aeb0d612eb125e3e78f5714c344c0993c6cd2d94ca84f481a06014772995e3eb573c7ad5e315cd2d532a5cd245f188532ad5e4b98c2e1a18276696b4b62359a1c022ae25ce0be8274506d2d99c560cbac498f1e0a1624cb573c7cd03c0803b078f530d8344bc7e5abacad85338b41a6d233612e32524f1a6795abcf1f570f1b0265c5b00fcc6684f6c12051010b21f507b034d89265d4b8ca65595b8acf1a679344861e5958dcd9c720c2b183d676b2b5aba5cc19e9738d0e0810c4c949147a5c4102e2d84bad03b0d83389734c148067cb573449e3e532ad5c19ec4941ebc7e5329e3d4cb23078f0c3cb2b1b9b4ce081ad5d29338ac12609d78f9e3c1270275e3e36b4b9a00402e0f1f5416aea42b8187716ca2b514943e320b48dc3ea2b14ac0d3851f2984cf278f68120040ca2b7169a5c30678f760ebb1db5c5aa2b0699a255c3c6ce2d053b8b6319a8ad485d12004e8136069a8ad882187069cc43532a1ae6248975c5a0d3069ca51671a04b14430214cba679251846249c86895abcd334a4800e3c6952441b21acad6e830764a682756aec438d1257704ec64f0c3861e716a8ac1a656b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part60 : Excludes 0xc000810000000000000000000000000 0x1f3afc022bd03600e0408100000000000 :=
  finishCode 29 0x941c0d02205a85aba60ac348c415329235c4f0e25c4f3124aa715dcf1ee27986aa653c790ce6249e3da814ac36b532bc7c91ac1b92e63894b2bc7d8030100052c97378f9e3dd8620cb43246a5cc6d738b54ca48d2a9829634392354ca78f4912e6c1d8106c411c4a99588f30dd47ea31624b0010f8236c4961892356aef1f3c7a546623b0752e6a65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part62 : Excludes 0xc000010800000000000000000000000 0x1f2a7ea200528601c0300108420000000 :=
  finishCode 59 0x2e094310881261d0716bb0d0360b57301e04b9a8ae6139e3d84f034e520861e6139e3d44aa2b92e20d34b9b106225b48430e0cb760c0613cc293c7a5ccaef1e3d42aa5d61bc86b3c7ba0902d5de0760f1e973830ea4d715c2410c3833e43e8a3c30e973830f29054ae78f328a40b572912e3034d07aa25531a8845329aca4d14a834e614cec3c0a018a6693b8b41a69733c7ad5db07169a262b5834d2e67a28898125e624a8cc0e7205da3ac31343b0d5a67205cc5206f61ab4ce618b10cc529738f1f2d5dd83019c4b995de7169e3cd0e3899a5ae2d343c0d3065c78f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part64 : Excludes 0xc000010020000000000000000000000 0x1f2abcc288500e00c0180300200400800 :=
  finishCode 135 0x1985016c68142aa2b781b0721d05601a680123502f152588e78f716c615435c54961b9e3cd8524c373595a5ccaee81792e678f3c7c78f96aec42d5e4b9a2065aba9956a704fc1a6e2d4409235b0721d0781806912414a832c1a6e2b9102f1f427984d4ca6c2204a6b38aca6b2875d8540cc2bba08a65250e852fb4b633681752e6d399c4ee2b33680656470dcd4aa05971699b565738accda8174b9a0872d94bea1f9c56a1d3c7c835435a1863c7a13e50ead5c1960cb9186014668e1e3de3f22054c2f1f9102c4194ca01952a8cfd0e678f9102a653c7c973715c087620ac8d43a78f5aba205b0301504b9b48da1b00d3693ca4933695dd4c32fc62b087914c24e8814b123b205d682e1d51aad063a6a8cd4ca9029857724bc88114aa995c5a49794caa65892ea298c56a3533695dd44069a1ae52f84ce315a87ccbe031699a98ac38b5102c2300a4b069ca3d24b834e621b06c1a715de41e834dd0721b4133c36b59595241a65198c56d23246a9958372d044b648d3606c70dcd0e728d5a5a453532ad88228888161ac375246b8ae1ba8c5ca2e651511c5a7a2b07c125dc572cadc4ac351b9a9954a338ae69998542bea63314cb3b025925c26a53559480ce5a9b4cdc562779862a1d716a205e06c1104012e6e81e3c90734b547aa33440ad5d1033c7c1a70225c5a187440ad5d006014c3c7a206069a874cdaa5f891ad2d51ea995e3ed22980d3519c88161ac33b826e84f411c057715a2041a6b628960af9e3dc5a88124ba876336b4ccf1eb57440a5ce (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part65 : Excludes 0xc000010000000000000000000000000 0x1f2a3c8208700600c0000100000000000 :=
  finishCode 153 0xd21695b4631845b1440daa088178866e2778f99e54ca97308cb4b4ea27811c4a78ae2209354ae9df5485abcf1f4309e3ccf2b5790c284f9886a1540ba99520360c46a10c2f1f88de64f53299e65aba1ae327943e219801545640d78f91e4f1ea579a6e615327a9950e724855c4aec9713c7ca2b5aba95d4ca8234b64a68e24f0278d680efa8a14094d4b8821652999e509e78f9e3e6795299856001a994cf286178fa92d26a29581a6c1b661c8741a8042cd3743998a41a60cb5015040186331252e656b14abc7cf1e92990e6e27514a9056ae56b696ca41022a5cd6aea215ad892295964a847235cc1b761442bbac8e4b9a975886a3f595c633988283d6248a554ca78f5b144515a95c0e7211d2e6c494b29e3e624a9952e62838e7aa65423a5cd0e674309e0699e3d2e6f1f9882929435833da876180069925e4b99e3da472d5d4ca9454b9925e2a9b0bda5a78d532832d406812e6f1f624cd2d519a984f1e9659a5a66b8f02965696b1252e6d41409e2994dc48ec3213ae9df448b25cd6aed393c69d864f1a4324f568277d3c0b3076124bc29513ea5cd4ba535927aa21d463c0b40a034ce78f95ad6ae96287e33c90d6621b4b5a4656b624bc7e62495ad2e67e33064318c49551444816af3c7d0d687d6d11428129a96133cc84f5a9c67950fcd398cf248d3a058518b4b64b08c85a3aa414b0c07369cc65d78fad5ce5b24d529a663c7e3c7a97d862d2d4814c31e3d02f28fd505214ca883b09738cf287d9a7263361ba06601ec0392bbb4ce618a49586ee2569ca1acc9e7434e652fa94d0fa9735abcf1f6a0f87814cab811ae62395dd43aa3f33cc37378f95dc91a46b926a613237bc08c15de3c7a18543aa3f3c7c93588d6a0200a4b8f1e5e34b4c27091526a615945654992e6679 (by decide +kernel)

private theorem part63 : Excludes 0xc000010000000000000000000000000 0x1f2a3c8208500600c0000100000000000 :=
  splitAt 1 89 0x1f2a3c8208500600c0000100000000000 part65 part64 (by decide +kernel)

private theorem part61 : Excludes 0xc000010000000000000000000000000 0x1f2a3c8200500600c0000100000000000 :=
  splitAt 1 95 0x1f2a3c8200500600c0000100000000000 part63 part62 (by decide +kernel)

private theorem part59 : Excludes 0xc000010000000000000000000000000 0x1f2a3c0200500600c0000100000000000 :=
  splitAt 1 107 0x1f2a3c0200500600c0000100000000000 part61 part60 (by decide +kernel)

private theorem part57 : Excludes 0xc000010000000000000000000000000 0x1f2a3c0000500600c0000100000000000 :=
  splitAt 1 101 0x1f2a3c0000500600c0000100000000000 part59 part58 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part68 : Excludes 0x4480010000000000000000000000000 0x1eba5f4c5932544044800100000000000 :=
  finishCode 49 0x68100490f1ea2198b62995344b0ca1d3c6bc7c1326991b5cf1f34299a66516c2d2b87e50e824cd32281910278d92d25a594caa22b86998cd22a7427c66933eca5d78fa204566ae3e0bc0acd4c410b4b2995c5a0a7440a5862d2a8872d8e32a65138a1ace3334b4e5aa65716c5535ab8a9e4b4a995102b574d1d053296954bb34dd6ae83d909ed2390fa447440a995a45711031a154ca2b34d0cfb1695e3f11e5102669532af083d8aa61871b59e0e2d82f6553518ca65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part69 : Excludes 0x4080010000000000000000000000000 0x1eae1d081032044040800100000000000 :=
  finishCode 149 0x1887111025c9d0e825cd4c5f1343c7c6932d298fe595a204f1e6857c0d8631506d0f442391ad83f38b5c56b4d60fce2d715a11e6239a1dc5a67b440c78f423b07e3c7ad5dc5a741716cc1f3c790e660f9e3d6aee2d44099a634295de3c7a80f029878f651702b4ca65342bc7d10265b8ad2a656919a25c5af1f5abc687342c7815c0d333c7d6ae94d8d32d3719bbc7d20532c479691951cd0a577530d33297ceda78d34ba204cf311ad4c342cf1f3c7a204b4af03a078f3c0c43378f99a56a7297cc56f1f342cf1f410e8440ad09736112c623c2b91b9a994d0e6953610b32c8c6e678f8d0a0a5311c8232bb9e3db43c799362359a145032995f06112c532c6850539a1cd2ac62288598d1246b51bc6850d0a8a62bba97cd12a519e3e577053c69922b951de3e881d0c225cdf0691446d1d0343c78f19580fd6a61a13349a6434321ccd2a33b96568230cc9a5414b19f4f1eb2334b8ae4d2b2a078f96aea6533e82954432d5c6d6b2315cc87d5918dccceea020045394ca6990c3bc7d6ae78f5abc187691c54751095dda478120510c2b93c7a8884f8c6e2b904c99ee5a9cb2378f8dccc8ac2d34c829e40c9094cdac4734bbc0b42e8d22602b93f144b1e3cefa85943eb40a029878f611a5b1d851020a334ba206430b4b413aa6596ae76190c24795329a548cb29948a65a5430948e0ab8d0cf1ebc218a658b4a64d33cb4b48d6861435a988592bbcb216969e3ccf64338e326793c7b4b4b4b299426633b344aa078f530aee5a591024538cf2c3f001c69508fb0d4cba861199b4cd4cb0e648f2f1f4409e3d68440e84302ee65d94ca87d532c28f866ef1f0c1a68a658b4af1f94ca9229064159e348d665b532a2082b8cba173440cf1f (by decide +kernel)

private theorem part67 : Excludes 0x4080010000000000000000000000000 0x1eaa1d081032044040800100000000000 :=
  splitAt 1 118 0x1eaa1d081032044040800100000000000 part69 part68 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part71 : Excludes 0x4020010000004000000000000000000 0x1eaa9c12411c840444201100804044020 :=
  finishCode 93 0xec360743c097340180630f1ea40b156771c7502eb4952f8e75e3ea61189c43378f9d5502e2d3828e31378f99b59c69013328750c23131658b4d445b14aa313813ea611cea92e532ca27713b11d032c3784cec496208b454cae4330d218de429ad4d43e879165ad083d8ca256b5512c3287cf0ac1d1aac39d50eb125c56a23007898a1648d50ec09f089c81f003967414e05d328a88447909ec1d344925d23b29956c3f180310cfaf1f053cb2b1ce9915496d2d989239d713a99604fb89ccfac2d90ce39d78fa995c4b2cad85aa3543cbe0cc34878f90ee2d1162b38c625862b599b473a66d902f0014f1e56b510f1ed33891a75590f2a498d16c491cea80803c7e3c7a876246a9956aed274c0d8511a66c21234a1704ccd12133829e6459862a653369a2543b125d3c3c4c3170a9b0a586a39d2a0b2ac2d091c65320ccd31715a40d21e3df03f0566a65903a68b40ec86194ca7852d09de56aed6029e3c2a0ae53292358c3310f33c7c92ea49153a9956c153b12624ba8f678f8296532a94de3e879 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part73 : Excludes 0x4020010000000000100000000000000 0x1eaa9c52093c844540200100004001001 :=
  finishCode 129 0x3b0d8310743c0973691c843cc2c5168ba08e2516221b0fcd0a69924b910e3429a65893027c2fe78f6316854013f19350c246b0539a563c79d9651fa0acf0aa42d0a3f9892a61326ac8c6e69e3076049b4b54a6267326c78f6714433dca3f532cc1d40c99ec2b33125445d14842acc43532b4b4d0a699052a99633d829cd333496053a1054caf0330f8348a3d90aa39d2bb8b459c51fc67b1ce9a54aef2886859892f1f34c925d2c3c7a994c2f247543e59d618b1260c3c2d33c7a90981a16532b1254c269578f861d4cb293414ef1f33dca65235a195e07c1b45d16c69144168b08a258b524973c78ccc14676994ca76994caaa19ae58c9d9491a785330eab19acc9a24134a8e754ca309865239d4909234cb734ccf1ea37169a996526b124f1e2d1162c48d5328e74fc3c7a88c49408c65b153a996618a94e24bb0c42f7308b4260f1f8f1ec4934ab68a22d8861e3e342996d2732155e3e78f2d48e7549b25750f26873c7ca651cec6872a189278f2f086b21048a6a658666a65821e6a0cce5a1a994cd2b61976620a4c4d0a7e1596531a0763c7aa090300a2061cf1e483983a09334ca99649134532a07e3a49104cd26990498a04f02c4ca2962485ec2ff0e760bd8dad444b16c74073b3c7d47aa655149a65e3f28f678fa94d84b0a9d4cac49420c2815329e3e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part74 : Excludes 0x4020010000000000000000000000000 0x1eaa9c120118844440300100000000000 :=
  finishCode 121 0x1d0440a20a03c0b57481d83c79d0373830e9735b030ea6581126273bc8e754c73074d2ac4990d648d3ba9e14cfab631867d873a099814aa3d92e6a425ccc8b1a5430e0a788dea6571291acd32cc368d8310742189736918c33b96764b8a196591a9959c525c56d624a06473a6952bbcb535309dd58922d19892d2318a20b2d8930e74d32c49873aa652b6cd3570ea8f54a2a21168b8966249a5d2e2d2390a80b2d893299492f30a56a65239892687614914d893088491a64d3c2a58c2196e1ce99e4d2a39d94a2a659a46b3b624a4f6616b46da466274b9a994cf639d3612e634b82ae65d343ca21532b68cc288d23c06997605970b4d204b0f1e0958cd2a4b712c823624b12640fa874e92a6569ba9850f2c2d8cd2b6228ac1e148a72985893299583a093873a775692c71d530a58588f1e3d892a65631744b13c3bc92363c7a99473a775891a78f526ca651699da45a7194cf1e78f88df2994cf639d481d8401803a0f1ec225cd893029459715dcd1315dc58a88280973530c0391ce824d8920990b9b48819873ac49168915e430ac8c6e6d23126022b0a54ca2d3525c39d1108255444b1806910e70e7430ec4942c8a0c58a1879892577138a9964b9825589321645966378ca2c29532a9960539e3da463126b2874b522b316298de43c8b4d0ca39d94c2973 (by decide +kernel)

private theorem part72 : Excludes 0x4020010000000000000000000000000 0x1eaa9c120118844440200100000000000 :=
  splitAt 1 56 0x1eaa9c120118844440200100000000000 part74 part73 (by decide +kernel)

private theorem part70 : Excludes 0x4000010000000000000000000000000 0x1eaa9c000010040040000100000000000 :=
  splitAt 4336 74 0x1eaa9c120118840440200100000000000 part72 part71 (by decide +kernel)

private theorem part66 : Excludes 0x4000010000000000000000000000000 0x1eaa1c000010040040000100000000000 :=
  splitAt 1 115 0x1eaa1c000010040040000100000000000 part70 part67 (by decide +kernel)

private theorem part56 : Excludes 0x4000010000000000000000000000000 0x1e2a1c000010040040000100000000000 :=
  splitAt 1 123 0x1e2a1c000010040040000100000000000 part66 part57 (by decide +kernel)

private theorem part48 : Excludes 0x4000010000000000000000000000000 0x162a1c000010040040000100000000000 :=
  splitAt 1 127 0x162a1c000010040040000100000000000 part56 part49 (by decide +kernel)

private theorem part40 : Excludes 0x4000010000000000000000000000000 0x142a1c000010040040000100000000000 :=
  splitAt 1 125 0x142a1c000010040040000100000000000 part48 part41 (by decide +kernel)

private theorem part32 : Excludes 0x4000010000000000000000000000000 0x14221c000010040040000100000000000 :=
  splitAt 1 119 0x14221c000010040040000100000000000 part40 part33 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part79 : Excludes 0x4100820000000000004000000000000 0x172824154924924124820804004000100 :=
  finishCode 27 0xf638b59c6c124761d425cb986e0785a770a85a66f1f23b9a5e4b49976087bc7da7608f4b49a5c8ef310d2d2d3b94be095532a5a549312e43c2922c096915ac6413c7a1fe34ab4ee699b1054aad315248785480f0864e3c7827d66302a48ee662c0a65344cc293c79a26621b09e34bb4d4f1ac33 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part81 : Excludes 0x4100820000000800000000000000000 0x172826114924924124824820824120104 :=
  finishCode 153 0x1307038b4b0201ec293b38ec2c0ea12e41431a243c2d33989296915aba8e61b81e1230cd3b23ba5a634bc6278c6ef1f524b1252478fca3362487854ca1e19a630785305416052180624ca650cb826e624ca6569dca3f532a186321a5ccd129739e3ec293c7a8ad9c7b1d8580f1f34cc3164b9751cc3703c2c338cba96933da5a634bcc439492c494908d70784142a650f0cec2909628c632e9a1d4cb0aa588334d5a76973622cd35049a995d43c7c73104d8785a63338f63b0d83984b9750dc0f0a5a660e91dd2d3058e78fb124d2f3a8a658d129690f0ac0c4992d22b5184ca4962098dd240f0ca3f0cba9943c3300ec290a65855266b620cc4952abc7d2e6f1f832ea6569acc2775186709dc8d67310f0b4c6671ec761b07309727e34d6698a5a43c2c4923bc6971699a5e7514cb1a252d21e1581e3f312456ac499e3e923c7e51f865d4ca1e19603a0c052b865e220b0cd4633116515bc7d88328fda6aea31263c7a995a63398ea378fe2601e1761686708d7297cf1ec3332f9cc641da99588728c58933114f1e66b9e3ec291549e3d505a118371437197c8ee98290a3f8d2ea3392d2a65698ca6504da86cf1f3124cbaa65986b30ccd0e65d7617825ca99613f8abcf1f299589302654cace2c0f1f88eec294b492e588734cde3ec493c7cd29698bb0a658ec26870cfca65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part82 : Excludes 0x4100820000000000000000000000000 0x172824114924924924824800000000000 :=
  finishCode 85 0x4c09a45c6c1c5aec270ce1806898972f1f4b9bd89812e5502adc193043c689715c78108f90d5a7678f423c37360ea86d4ba363833e97367145712e5a772995200c2c78d5329e3c30b1e354ca78f9e3e197671ec491d858189328acf1e96925c9f8ea25a588719ec0fb1976532a8fc117292c12aa654b4b1266988ad4eda1e1571fc690f030624f1af1f94aec1b9a76a3f0c49e3e61aa995d43c7c87f0ee827d4caa431260cd9e3c13e78f8312c357519c6f1cc7f15c0f09f86e24876d519c09f53282a6624b0666249e343131e04ea330d54cac0290c499e3ea3f34ab4ed4ca65d624ca654b9cc4969dbb0f1f9a7665d343867e761b04c0972c49810e33982f24350cbc19790e334ec13ea650f0ac0d82904b9624c9730d1a5ce235cc350cbb126 (by decide +kernel)

private theorem part80 : Excludes 0x4100820000000000000000000000000 0x172824114924924124824800000000000 :=
  splitAt 1 71 0x172824114924924124824800000000000 part82 part81 (by decide +kernel)

private theorem part78 : Excludes 0x4100820000000000000000000000000 0x172824114924924124820800000000000 :=
  splitAt 1 50 0x172824114924924124820800000000000 part80 part79 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part84 : Excludes 0x4000820000000000100000000000000 0x162924114920100120820900000004824 :=
  finishCode 45 0x781f0601c06f078efe3a89607850033589de518b8b50e287f621c189624a995a76435986ea57716b124f1e2a9581684a092ac358f1ef1f0cbb4ee78fa8c66249e3da771255892c1d94aa78f24ab4eccd6a219a669d9e3cd26969856aa2b731bc245c1e1420dc69dc103489a99410697352eae818992e6a314b49206433b1260cfa86d2e6787222c787343b4ee245a5ccf0eea3b01e122bc969532bc7cf1e4b934cca493c79e3e23ba5a4916ce3984b9591cd3b3c3a5cc55ea1584fe64f3c68786 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part85 : Excludes 0x4000820000000000000000000000000 0x162924110920100120920800000000000 :=
  finishCode 129 0x403c0b577c1b0701a41e3b78b41801e124a9db669b9e1d2e6d238c52e2d2359e1dd43c3a5cd0db042d8922d1087c67d8902a1b3c3a5ccf0f25cd892ec2c095b9c4a63f24092e4f0e97373128f1254cf729546e69477168ae5893299433e1e13c3ba8fe2c0e03d8cc07852d30b04d2626992c5a0f1e66b624ca310cba8c6621c0a93989e3c5521e1928e18b716c66b0f0b78a559c5a65d4b499ad44518c269050a996320ac08031264b4bc7c90278f5b1a4f28c4d262b552fce2d3aeb8ad2d28c09a6337b8b5e3ec4924ab126716bc7d9c6c127706acf1e4b9480d1738b43c2b234a3862cf1e0a9964695b245c09f0f0ac0ce3804b94b9c6771428abd2e71e1c3c32d4e78f9e1de03e11c7004c6903e0b00f1d503c7a581975503c312552d30ad631aa56da7695b9687310cc6ad334adac067d8366e2d3c7922e0f0a5a65328785c5a3c76f1cc245c1e134bca6592e6d3b044b80903e0b00f1d503c7ba818b4adc6890f092564adc96f5a9ad0e0f0b10cc6ad334ada5bd600d9c18b3c7922e0f0a5a61e3b98fe1e01e14b9c8654ada86d4ba481621a7697394bae2d532c27f518b12586731252e6d3b240922d2e70ae5a76687701c5a903e0b00f1d2df065cf1e96f960493c78f49dc92783c23c73c1300cbc78749d911624092e588a92769db4ee0cfc787 (by decide +kernel)

private theorem part83 : Excludes 0x4000820000000000000000000000000 0x162924110920100120820800000000000 :=
  splitAt 1 56 0x162924110920100120820800000000000 part85 part84 (by decide +kernel)

private theorem part77 : Excludes 0x4000820000000000000000000000000 0x162824110920100120820800000000000 :=
  splitAt 1 116 0x162824110920100120820800000000000 part83 part78 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part87 : Excludes 0x4000800000800000000000000000000 0x162924030900100820800120100020000 :=
  finishCode 145 0x340883c0b577c180701d41e3b78c278956f1f25487856c69dc78f520b4ee23099a458291d98824ab624bc7c952de122e0f09e0d211ae618a1954aa4813c3cc49230c0b14b12e678769dc49f1c0c2d11b9b4ed892de1d46240927c3c2c006ce61682c4f1e97394aaba25ce0558784972a83a8cc2994a5f04ad2e60830f09a4c3c31e1cea3259435f3c7d2e6f83c0e03783c7751a46a1ec5a03c266f94cac4951f9a2c93e57f94cab426049f51fca5569dc3899c4ea6552a8786154ca5f0f0922e390c33150da994972fe3481e155174240b1264a3a86ce52a4925ca996390a8ad49286594aaa2b8e52a4925c9186532a51d4ba47724fb78da3a8b00785e3f1a4c972a6598058055f346de3e1af61bc66f69dbc7cea311accded3b69dcc4114482d43c2e012e54cb1a4d03f1585bc624c78f25987850033ec1b33c799f62a386ac366e63a8f6378b60785a77346d2e649f34c92ac973196c93ed2310ba3f84b9329c2c1240cf1f69ba994d323815b1c0240cd3b1609a64f04b9ce2750db11c9025620c6433b89e515a5cde3f34e49027217f048a782d0a5d907af1f1608c54742481713cf1f69dbc7e532b89c62b28ade3ee27432b124702a5d989224525cb50d238ae620b89cf1a49553292add801cc59b3159e1d4cad3b154923652f9d461c4a514f1ac02d0883c7c9024b54acc65b0a1a5cd0e33684ab42fc91d309a0dd8922b53a6c91d091c97369d9e1c91698350a83a87829954930acda6e4b93c3a97669d9e05e3e4b93a8c7615b0cef3104b16f1f69d91e5e3f24cda767518ec22b978fc4b9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part89 : Excludes 0x4000800000004000000000000000000 0x142904134904900024000020104004000 :=
  finishCode 135 0x110381e05abbe0d82a0983007870cfc9471e3a5ce189c459240a5cc78e4b592e69471e3be8b4258e499b12415a48d0f092d5d43c792ad89329950bf3105c06116067148f25bcc56c2d532b8b589278f154a1563c78295892e2d624cf1f05a8b1dc5a78f9c5ac375aab1254cad3392c6d83b0c012e5a83c7a99608789e5c5af1f4adb0b6081b125e3e961f84814b9c45962498ae532a5cd89307843570dddc5af1f050a4cde3f38b4162933541744b99e1c89f286d02209f59582ac9721179c5a96d112a99489e2af344c465699a5cde07c180581504c1203c1f43c3a8878f83c2483255b48e23c7da764b5515cc2952eb126620a9954cb0785c052ecd2769d9e3c13f31248b20a54a7b6078f761f44b992d634b92e671692d60588786699b4ed29f02c4552f1f3c392d671692e433e78f3c7cc4994ca4ab69db49de3e3c74b9c78758180624c9730d59e3de3efa25cd4cb297c90287d9a766198c2e0b5624b8b496af1f69dc7874b9be0f0380d40f1d246f14cafe338980b3547f1e34ae6a5524fc74d3c68aa4e63212586e2d1621cc4931495fccde49f69dce27345a8a54c22c125ca9562b98b3493e96108621a99f49162cb83c2d3b6f1804c10873128ed229962a98afc9524b552fcd3b713a9850e219f0f0867e2a9b98a6189024b525cc6975328ae433f12d4572a5583c2a6524fa51e50d86454ca4b95818072033e4b982063070d7b4ed24157ce2733ea9943c30c4c55e67d9a761e1157b001e19a7628323782d5e3e66f9a761e16a1604009033125266f1f0d59e3d2df06ac95324cccfb078589278f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part91 : Excludes 0x14000800000000000100000000000000 0x1cb9d413cd60d04130001100000004020 :=
  finishCode 37 0xc02c0ba1e3da8058ab0457985219778f867d24e9139c5a9739b06a1e3f3124c56c2d254867d4ca1b36d12e6685904a48b78f9a6585b3c7dc56a658902e2d78fbe84b583c24a93f19c4919878fc86b21ca9952d2c4951106b25a50b24599e3e913532915e30b96a56aac49435b8b6490a01a5c459532a78e2d8f02731906e5a99686a61430b8b5f44b9a04e715b4c4a6e87d69d9a1490266990fad3b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part93 : Excludes 0x5000800000000000100000000000000 0x1dac05535db0945120000110000004020 :=
  finishCode 21 0xe84c12e618b833e7870f0ce2d34c92e5a76a826018b8f0eba338aa02d497244f90f211f157a0c643cbc7c15721e415a8a390e611ac2db25b455e83143c81de126a8ac33e6999e3e5230cfa1560f0a9941633c7c35e2af (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part95 : Excludes 0x4010800000000000100000000000000 0x15ba0417497190c520000100001004021 :=
  finishCode 53 0xd826078398787711bc51fcc4952f92e48ee1e15d033f12e547f0255805e120670326a659452a5569d9a540f7312543ea6528fc6950cf9a5669985ec0f7312546aa650bdb4ec2f729950be9730c99a5580761f44b9b38c498972697056c651532801ca3e4b515fcc4905692e5bc0c6ca65159b4ec3c2c199892d3b53282b52e7388ce3984b96f1a77122d2e61e16a033f38b4a46973532a5ce69d91ad4bb299504a65d7169a1df425ace2d0f08afe222c6875328ae433ede2a8fa065e0f092a584518ce2d056b1241620a1832ec490cbc1e1040c197 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part96 : Excludes 0x4000800000000000100000000000000 0x153814134920904120000100000004020 :=
  finishCode 135 0x300e82c03c7481683c7aa0b6065d84056cc4971682c5a77253d83a0a1620c2c769db8b5892fa378c212a634a82c43c312a54ab1204cd294f69da0c64209864cd2c495a1b4ed6c7d1a4710956a579a76a5d15dc63362487865209235892a5d9a76049985281d69db125a47b16c163c94f62482d4d0ade3c7d4cb12a45831205886461532cc490cb9a5416af1f832ea651548b05f45a1c5b1a249527e0e260f0b125c5b0784fc49189286d983a85f62086054cae2d858eb5505ac2c7716a00b036078f6616876034e83d94ca0b133d8b35e3e973532c2b3514c0933c6a9952e6f1f92e6c498c8238153282c4d2a19778f88074338d3b761d45a12c2c7cf1f23b9a5d03b1a25892a658cba1e178f9f807d88eef1f4b4b1256870d6505e0b505ac553532b125c5a1e12c7cf1f7168ae6059b8b5e3eb42a0ec154d0db11ac6a66972c7878605aa907c1a5e1b5bb069788eeb53319ce2d0f084be41e91ddd8751b43d05a6c439892e2d3a09d84cd67519c52761412b0d50330b150c624b076436b0d5c5ac414b4c761886ac4552a8785c5aec3609c2f09730d1c59725cc5836f178671a773124d2e4b9058968e624b4ec15ae2d9a7685f34a84be69d868c972ce065c58338b58920b1056cc4971682b6340f0720f0e8034ed3c2b9b8b661aa995892461412ca65624b38973415c87d42fca65621827c13f07854ca85915a956d2e6fe25cdec6a1f4168a97e716927dc5b34ed89248b86a62cb69d91ae624b4edc5b122d89246169d9e1e (by decide +kernel)

private theorem part94 : Excludes 0x4000800000000000100000000000000 0x153804134920904120000100000004020 :=
  splitAt 1 112 0x153804134920904120000100000004020 part96 part95 (by decide +kernel)

private theorem part92 : Excludes 0x4000800000000000100000000000000 0x152804134920904120000100000004020 :=
  splitAt 1 120 0x152804134920904120000100000004020 part94 part93 (by decide +kernel)

private theorem part90 : Excludes 0x4000800000000000000000000000000 0x142804030900904020000000000000000 :=
  splitAt 5184 124 0x142804134920904120000100000004020 part92 part91 (by decide +kernel)

private theorem part88 : Excludes 0x4000800000000000000000000000000 0x142804030900900020000000000000000 :=
  splitAt 1 74 0x142804030900900020000000000000000 part90 part89 (by decide +kernel)

private theorem part86 : Excludes 0x4000800000000000000000000000000 0x142804030900100020000000000000000 :=
  splitAt 1 83 0x142804030900100020000000000000000 part88 part87 (by decide +kernel)

private theorem part76 : Excludes 0x4000800000000000000000000000000 0x142804010900100020000000000000000 :=
  splitAt 1 101 0x142804010900100020000000000000000 part86 part77 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part99 : Excludes 0x4140000000000000000000000000000 0x1f2c94d54554000000000000000000000 :=
  finishCode 97 0xf6388de3381e153056a19725cb12644091de3ae81bde3e78f624b00601e3d07725cd2db24f5496a61056956d84b09b4b4a17f1b1956d2e6ce3004b965034678f2d2cf1f4b9a20455f149e0bda5ccab617f8ab61a34a104601102d83389730d1acde78f84bd4ca2af59bcf1f097a99432f312604f956c2fe973601846319c6c01620c18d0e1a34b9bc7e624a99527b310cef20ad34bc0a5624c1973c78ad62ad827d892973601485b0346ce1a56157a1c662482954cb1a1c904b98e76157a99427ece118e1899e3de3e39578fc78f189b389733a2c873130a99457695192dad292adb125946c19c600186a43c01a3410f1e9622056c23ba5ce520b486690cc41435b12589316952e7200973440c5a578f9e3d04624ca5d29191dd102c499044b9a5895190fa477624c83543ea4f62d2a90584ec496016460dc0ad2d2a80881189c5234b9868cf1eb2f821e87f498a995c5aa658a86881716b06cb4a86d4b99696440b8b432ea4338aa3002a92818532994cba19b92e678f293c84952e827d4cac494b9a5ce33ca1c604fa994f1f19454ae973 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part101 : Excludes 0x5040000000000000000000000000000 0x1f2705d54504000000000000000000000 :=
  finishCode 81 0x441504c1403c3969605e82b56ae74153e4b9a98ce04ce344b1262d2a2048a704cc55e699056a70ca25cc33f148d6ae69905682f54a31a15c5a523691bc7d4ca58328b57611c5b02b417aa629062d2a996095a9960d1cf1f6f1a4610cf734b50b2d3318da5cc5524b978fad5c186a318cbaa4d4b9bc7d6ae4b9897325cde3eb57631845d16005cac81e194825a5056998d379e3e19f532bd8b198f1267d286c629712a4754368e2995e3ec29944ec49440a98549b18a4d172994b328810f082f5cc7714c61aca63532969510298078588b29050c2f1f94c3f1ec5d0ef325154ca7852be92e4f40bcca412219d154c6f1f90e6859888687d532867d49aa63510c19f532968f1f90c2b414acac019f94ba1a343ec68591024b933033f22048dec49532b88ee3c7e48e9e34eba8812d287852825ccc49531a909698af269740ccc490d1c651 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part103 : Excludes 0x4050000000000000000000000000000 0x1db724c50445500000000000000000000 :=
  finishCode 63 0x1f4771cc6203c2881d093b82ee4b93c3a5cc31f1e1c33e0bd91024b951596957c4902ff2994e932204b4a74986861833c3a205745f09729a3785a552eca654b49a1cf0f299434b11154c6881532a51e04e9e1d102ca2e0a63833e5a5440a6094f92c692792bb05d4d0ee6378ce128496a76992d2c4990e24234b9a16cf12a212e570490eea09d515ca654b4b0ce09485056aaa658ed325a53025c86965329a254cb069588440972c1d817ea65699a49d2c6787528c30b4b1b124372a65440b0201305ab86960dc85fcf0e662d8a656f12931d74372927988a9359052c198f1a9275269d7509aa6591029273c3a2063c3a206 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part104 : Excludes 0x4040000000000000000000000000000 0x153514c50404000000000000000000000 :=
  finishCode 159 0x6c1a058078e603389737516c5d05522bb401644389e1e624a86e5aba16d06ac498f0e41794baa65440be898378787532c1e1532cc496f1247114cab2078524b2205272b57924b292d8863330a0c8294b09d251021e15abc2354a49d25102a6551acd2d187ad5d102a653c3b1261548ad4f0ede260e21e1ca05abc55b2d2cc490bfb12624fa135ec525c33324fad5d09a1e124ac84d3c3cb573bcbf87877b0d170784576b40aa543731240c6a4743e9255c4f006504a41f5188c4da6e55b523c0c30bba994d164813c3cca298ce2205887f0972ea1e1e43ea5a45761e13f0b4a1a992d2c49232c1a9435c969250ba8be3f85a53a4c96915d8785543b4c9693c4a5a63c063725bcf0ee6312678f8aed4bb251de3e5a597c6f0b4a1e189566938eaa77924bce2d78f8784f0ee6348c02d831f8f0e2b50f092ac96af1f8cd2c490f09e1cab70ad52e67870f0c7812e48f3247d2de64d3c3a5863c091e49730ad52e69333c3b48ca2f8b43a84a925a9e3e6938784b4aa655abc8815b1c4255ba8fe2c81e13c7ce2d53186d4b4aa5d8b4b1e3d8930ad4b4ac418552a65381a0532c5a5440ad5d2d330d4ab6c49440bc7d8933c7cb4aa655b1a0250a0066d928ed2778fad5cf1ec20a765ab9a245761e183c32205704903c28813a4c9693a4c78f9e3e927699a58c3c2f63381e14c18448056a495986ad276249e3d8871e35e3eb575302eb310412aa3b24aa98d2d2d0125432f2d5d43734c5892c43856af1f5ab9e3ccef20078d855266b3c7a58a21949a65d335b086899c5ac49154b10e615a995c5aa4d68120770f1ee216964408784eeb29958926954409a262468aedfc6d16af1a554ca1e115d8786344c695440c1e1 (by decide +kernel)

private theorem part102 : Excludes 0x4040000000000000000000000000000 0x153504c50404000000000000000000000 :=
  splitAt 1 112 0x153504c50404000000000000000000000 part104 part103 (by decide +kernel)

private theorem part100 : Excludes 0x4040000000000000000000000000000 0x152504c50404000000000000000000000 :=
  splitAt 1 120 0x152504c50404000000000000000000000 part102 part101 (by decide +kernel)

private theorem part98 : Excludes 0x4040000000000000000000000000000 0x152404c50404000000000000000000000 :=
  splitAt 1 116 0x152404c50404000000000000000000000 part100 part99 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part108 : Excludes 0x5800000200000000000000000000000 0x1f25cfff00002280d0016000000800000 :=
  finishCode 39 0xe03100c9600cf7030510157c9733c3ad5d30751c4b3124a9ed3b532a1cd893153c11a3739a6ed3b34acc493c3b08be1989e270c42c80bf4512e711bd89266d43c9a5d2a3312412a46f8cd71e1d85aa65429a996616b11c17eb4d92caa6362382fd49b02fd4c6a42d4e336a1e50aa68733dc8554b9a1e53054110526cc4769d9974f0ea63126237b89433ed3b510b4ee5abce254b9a546528b895646d3b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part110 : Excludes 0x25000000200000000000000000000000 0x1d2df7f18008220052094000000800000 :=
  finishCode 31 0x3a8de2200cf5817c66148f25cdc5aa573459a6538528c653440a9950aa867421ca654a138440a4d6691a0c5e3e867716a5cd48334ed086e2d520cd3b421a5cd6aee2d716ca658d32c42a08c25765329a2cd32bc1a4e5238abcf0f25cc35f31250aa973624c787157b080c9590f031e35a773c7dc5a2af5ab913e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part111 : Excludes 0x5000000200000000000000000000000 0x1f2c47f10000220050014000000800000 :=
  finishCode 157 0x3a8f6388e63281e1471645e0b4ac429764b9ad5da760bd70126b196d2e2c49157ad5e5329d09738f0ed3b7413c3c384be78fa0c589321e6624a105401604ff38956ae2af2b0a855482883108679a620bd52bad5d2e68819a76b57712cd313a295854aed3b5e1c5b25cda762af69dc7874b98abe5abb894ac2a1552096959c70180157a28641523c841390a5c425b34c48a72b895d92e27879892a474b9a95dc5b054545665b523a5c57c651882d2b089e02f55c4b0c2853c699e63b0c447532c54f32ea0ad2e6d3b062aa0a2b96aea655abc15b2a7996da76de27866b49130043c69749a89fd4431a1cf0278d32dc68778fc15d698a85563a687450943a12ba6999c569210d7a91c8a7069ce4334c52e2d3b88a61af52168062c9713439a5c50b2204cd694d5c018a97396ae02794c646b69d91bd28381cc440b18cc310c0214e334a5cd8920bd05fac066f235c81f49cb10d2e6c498f0f2995892962d5e343b4ee78f9614cf7330a4d92c269505fa58634ba1cd4c698290de060e5329e1da766955e055f3124f0e0bd7418928239a52c43418b4eccd2787043c9739a761af41ac687715a0c455e0bd69db00de3186003056af34cd2e6d3b8f0e2af69dc2af33db8ae624ad5cac2823532a5cc17a87394ca65369dad5dcc61019eb232854988d69614a4b8b51025a5580d1325cc55266b9852689716a206716831d08f25cc18eca3105a533dce2d435831450b19765189a1d4c711a770abd6ae0c92d29c0cc250b022051878fc677624b11d08669960dc67762486bd44b02f5892b01e1e69dad5d2e61af69dc0c15abc881661500d7a5ce345a1e6097bc7d2e6867970064b08b574b9c8794accc434afb4ec0f73c7ca9e2af (by decide +kernel)

private theorem part109 : Excludes 0x5000000200000000000000000000000 0x1d2c47f10000220050014000000800000 :=
  splitAt 1 125 0x1d2c47f10000220050014000000800000 part111 part110 (by decide +kernel)

private theorem part107 : Excludes 0x5000000200000000000000000000000 0x1d2447f10000220050014000000800000 :=
  splitAt 1 119 0x1d2447f10000220050014000000800000 part109 part108 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part114 : Excludes 0x84100000200000000000000000000000 0x173eccb94980200610a10400000800000 :=
  finishCode 79 0x19453164710bc2d2a50d838b510257f8cba97352fcd3b335b00e2d51fc95933d9e3d47f256589257f615c41b230a545c5a8814aca50c01c0982205685210cb38a543ad2943cacac17ec4933d9a5d0cf3c7d062637532b1254cb3124ace8791bec0c1433a90b4260c499e3e25b33da8fcd2e78f9a769734b9c78f624c973060918669da20580060ca653c799ecae73124cbe87336110265f9c5aa3f601a7719b5c5a78f498cd3b6c1c0601203a0f1ed3b8ae6973420c865063b309831264b6a5cc18e58b4b9c5a7063a1e64a8b1262b9b009c2b89e219e4b9a1e54cb28fd27a96d532c447989295105fa9952db2924acf2d0c0290a611de4b99e3cd0e697700b4f187453a4773c799e6580cbf38b5e3ea1d3c7b1252e665f9c5ac4970160524c9732b991de439a9264b9a8c6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part115 : Excludes 0x4100000200000000000000000000000 0x1f3a44b14100200610010400000800000 :=
  finishCode 153 0x7b1cc6f1a80f0b68cc380a00b045a694103cf1e28188d6c4978fa2054cb086e60db125102a654c18460110302fcd2e9c25362c2997d10297332fc58540f91ada76a3f873a477624a20417f067cacf1e3c5a698290b01a5d8930e750f22c5873aa656248b1669dc973440a19c58a18b910278f344b80c0240a61e3d04761102bc252e69d869cb169c34ce4b9b4ce715c0bd532b08e2d2b0cd31433a534e8a971624c97360d9d15d86c1304e0b1662b9892a552c1a5cda67160e0d3959e36034e637145c05152ab4ee4e13c6d10ca879716ca5f515bc7d4ca2c178fca2b420c147834e52b160a7057f6712e6c49807293950ea954b4b295da773087829897343c969644090fe50da86e048b4ed4629730cf9696440b80b01c0903b078f521303a1a6725ccae6e2b8d2e0c1597968d2e7169d2e702f62d28315983a14853034ee2d8b4a88105ecbe3286378b4a0c13712e730fd4cac1f4b9ca6531ba5352e7030583e1a794672924d2ef1f2b9a97e3b69e35e3e9730d39e3dd8611857387c18284f3369a258c408c58343e8315082d288d659da096532b0ce3b88015e3ea6569aa97cf1a5a5716b288226888169dc12f0cf8a04b4ac21a2605f9a1dc3f34ece3ae2d532867dbc711c3f34ed83e68771696953038ec82569482fcd2e0bf833f0265480cfc9733438c3e70fb4ed2e6ca2c80c55f0e82d298087d9a76f1f440a5cd1031e3cae646b8f1a847014b8a5a4ef1f440b8b4ebf3c7d2e6e2d440b4ee78f95cdc5a881581d8600d0f0aa4f1ebc3126716a5ccae6c499c5a9730d3ca653c7ad0e2d6010b3197cd2ec4982c719ad892c29 (by decide +kernel)

private theorem part113 : Excludes 0x4100000200000000000000000000000 0x173a44b14100200610010400000800000 :=
  splitAt 1 127 0x173a44b14100200610010400000800000 part115 part114 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part118 : Excludes 0x34000000200000000000000000000000 0x1cbf76a3800a2000160d0000000800000 :=
  finishCode 67 0x1a0731b06719862184581bc6001a6b61e3d0c5f12c2c29a1563338acec2e2d6169a2e716c8814b9b0b6616c061440a5cd88f19856ae973601405f0f1e933988e68b05eb11e4b9a47e34986cd85abe2cee4aeb0e52e668b34c9f89030fe033a4852ba66143ea206716a5764b8834e5abc97343e9e3c1a60d381a71e3cd0b1e3c1a6b0250902f878f4914c532a206526b116349b116440a2065f1c5b20954cac2d342bc7e716b8b65abbc7cf1ee2d9985e018a973988e0bd3c786cd28334c78f3499a2e78fa5ccf1e86b96c440b30b0299669d824cd0a699532c0d3944297180c20d3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part120 : Excludes 0x14080000200000000000000000000000 0x1ebb55fb5022200894050200000800000 :=
  finishCode 35 0x481405f0f1ee221ae06296958c532c0c16148025056f1f69da2050faa3b903311e5d85a14c0d9a2062d2b11e062a5ce623c5a5062af8922e0a655310423ccf1f440b4de5ab91e4c8a5a523ccf1f50ead0d2dea295abb46e78f969605eb78ac1e8b403048f2439988e973924f06cd2e681992e6d379e3e14f4b786bd2e6c47 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part121 : Excludes 0x14000000200000000000000000000000 0x1eb1d4a30002200014050000000800000 :=
  finishCode 133 0x711bc7517c0f0a800cb9a764ab3c7927db0670957032c89b31154ca97369db8b54cb12cd8056140250b6078f595ce2d06686cd88f34ee716a80e2d3c7c0cb78f9836208a97d88e71160f95e42ae0cb716c2515abb11c196d4300b61a664b9b8b41924ab259b0b62549694192d3b9c5a49f4b9996c192b220896169678f922de3f1695e3f1a64b4a93d92da68b69d9a4d7c531502d2b688c1a4da8345b0b67169205492a653c7cc4750eb4ed26738b54cad3b6a170532b408815abcf1f0d9a8861b9a5be68dbc7cf1e4818f1e1b3985a78f541b4460f1f30b5a76a653459a6520315cd3b349b0b4f1ec2d94048187f34ed88e48142c9914f1ed39949e645612920585ac2d923f06cd85a78f481b0681403f0f1e982d5d08e9399c5a973309a1cd892d379a76973330a509830e60b58dae440b0fca570265a76c39623c847716c881423a206716b07e39290e5102e2d4b9b11d80581204a0f1e7a378a4d410942745852ea51440a99648a8a5d4a26772598d763a28a5d4a2ee1c0de220472b19dc9664219892a25616c4ab259c1b314bb0b5b04b9c1b324bcc3569d92ad685f1bc4b0952f1f910248b616ad8f1f909ee2b2c2b124d0af1f91861686ccc7f0a05686c4978fa994d32f1f94ca84f988e9730d9ad5d1028819a6ef1f255a9952e6be2206532b4ede3ec4925592a494322057c771d4431204a10fa65b9102d3b909f2d5c93e973620902c43927268b24fcc2d34cc39569bc37369da5cc93ed3b96ae881 (by decide +kernel)

private theorem part119 : Excludes 0x14000000200000000000000000000000 0x1eb154a30002200014050000000800000 :=
  splitAt 1 115 0x1eb154a30002200014050000000800000 part121 part120 (by decide +kernel)

private theorem part117 : Excludes 0x14000000200000000000000000000000 0x1cb154a30002200014050000000800000 :=
  splitAt 1 125 0x1cb154a30002200014050000000800000 part119 part118 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part124 : Excludes 0x4090000200000000000000000000000 0x1fbf47bd1064b04892010240000800000 :=
  finishCode 35 0x1945f1c4440b4ab826088169dc6953c39a1e081957d2e619f3f00ef29354c6d4258e49399ee4b9b4ecd0ea4d9a7692723ca20510611303439f07870c1cd275269a24133294433f293549b1114c7ea653c3a204d1302fd102b8378881570d0e67b96ae9494a699ee08ec94d6f12970c8da76927343a98e6f0f0f2d5d49a6874aec971 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part126 : Excludes 0x84010000200000000000000000000000 0x17b3cca528c0304012a10040000800000 :=
  finishCode 45 0x350ca300ee12cc96a37d90f2c49343a204b4a9139c5a6875517024fa605a594aab23988a8814b99696532bb8a5592e68812d29f0a338cbea55532a6036d50ecb5752a98c676092aa60df670e9e1d2e6e2d343b0e6532b4eccf25828c6230a994f0e1975abb4ed4cb1e1dc5a197411945c130440b1262459a252e6787343c48b2d2a58d3b9a4e973245a5ce6998c9da765a5343c48b5c130541603c3b07e624860d2e6b579a769739a76b5734a913650ab4c4b4ab572afce2d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part127 : Excludes 0x4010000200000000000000000000000 0x1fb3c4a50040304012010040000800000 :=
  finishCode 129 0x771c46503c2a62c8b8169550440b60c4260e2d4a3cb574b99e1d892a519a7619f5aba60947988ec490bf9e1d26b298d6aec3f9c5a97394a2c4960126730642c6433624b11dc5a973531a5ce5c058440b89650a9585456882a07830078743cca3b5abce2596aea5169db8b52e734ed6aea517169d03739a76831392a97528f207d0aad3b9686e252b0a85545678230aa2d84816d10c450ac246b9a62971515b89650aa4d545721e54ae787987e13d43ca28c01e1e4b9b11d0f293996af348526a7c220c475abc7874b9957e624a1e54ca8559872c4950ea1e4f84b9c24550aad5d872a5d616b11dc3b3125a76c3952eaa07c340a6544187f2855892b570cfcc4750ac18f42aa19e50da5cc33ed3b4c017a91f9892855942a10b616b4ed5c4aec971541084614aea479892973136a8ee61fb8b54caa47235ce2d61f85965319c0d4220580591c38d6929a5ce3a0bf34392a510124c65f532b124f0eb5740fcc49712927d4ca17f8f0eb57344b125806a1a77312508687934392a496a787988e48b6249a25a771e1d7c56093ec01f04b5519c0bf623a1e650e82fd7028110532b4ee3c3a5cd6ae9831160958925a76a295b0c6244d69d8db6095b115c4b3107871b9cb574b9b11e532cc025ce05f99e4f0f25cd5860170250b4ee4b9a49dc5ab57716c9275c13c3c3ad5d54716cc4961f961411330fda6b30fd892e2d4b9cd838b52e7286d0f2c493c3b4962c2b11548ec49 (by decide +kernel)

private theorem part125 : Excludes 0x4010000200000000000000000000000 0x17b3c4a50040304012010040000800000 :=
  splitAt 1 127 0x17b3c4a50040304012010040000800000 part127 part126 (by decide +kernel)

private theorem part123 : Excludes 0x4010000200000000000000000000000 0x17b344a50040304012010040000800000 :=
  splitAt 1 115 0x17b344a50040304012010040000800000 part125 part124 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part129 : Excludes 0x4001000200000000000000000000000 0x15b1d4a11400640110030004000800000 :=
  finishCode 153 0xb0340903e878f6f16c561c425092accc716b4ec3c2e2b8e8a453429b11c04700a458e20531585b467b05a458e881711dc716b1165a984ace8a56733b9695102ce260631863ec4562494acd2aec1986873a2c04b60fb0b4c57081496614b90a7114c966ee368881698ca653498b1c68b1c95892a65532c4b36d1c475061734eda66c2d5328785dc610b4a8539a6646b32db10d85ad3b43cb0b6334acd6621b8b5a66c2d32dc2c769bcc4941899ac3c28655f14c5916c2d28d763a28ad4583298dc5b2205b4334c2c1612c567440cec33870196ccee2b5412ce2922da204acf34eda772205c5a8819c5a6777f1b4761bc6a15c15a8b1d18493ce2d226b10d88e5a543cbb8ca1e062d2bc7e621cc472d2c62b621b88fa2581e157185ab35969af1f8916751345cb57716bc7d345f1244a1883c0c77d3499a653c4129e063c6ad5e78f9dc6412a91d85a68b78fcc2d32d9a4dc5b3c7d88ebe2095c531db48d6685716cc19440bc7dc5268b9e3ec2d344969615a8b05bc751f45503c2a658952c4790c532c68578fc94218ca19a4d2678d8b4ae2b88d6f1f9c5b1a2de3f1a4cd32d4278ae30b678fb8b495286543caf8c2d5309025679c5ac4944092ce315a0c6714b8b661ca104902c2d0f09d360f0b0b594532cf1f25992d492b19e5f47f1bc4609561e124ac87978fcca208c4390f206f160a2054c4c1c5a41994c6c47624b09544a5672d2cf1f42ac2c1716c31d0a88ad5c5b3c7da7687933b92ade3f1a64cee881716ba840f716b50ac2584a178fc4a932099ad49b0b1c9672d4dc5665161fa894d2e2c7693c6455ab9a2543b194d4be4a1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part131 : Excludes 0x4000100200000000000000000000000 0x1539f5a10104604010110200400800000 :=
  finishCode 103 0x6514c7d1102be3785a56a1d4255b8b624f8ef5a770aa472b15543c2a8350da009669da994cb62c134ca608438b16e2d94ca8673a2ca5d623996cd3267790d658b512bd8e2d6a03c21418582c47988f0aa5bc440f0716bb0ea3c7e3c3a5cc5960d3581a771a65e3e6774b1cf1f3c3a9063159df50f2f1f3c3825e34cb4ec1a6ce3a8860b2c1a676d86ea73d9a4277d3f10c224c82533b9d34eda38539ec77d232c2b52aa8b2e33bc85534cbf8de2d01e16a17825a9a664ac8ad4ae6a1b893ed3b4412e734ecf0ec2d9e3e12b289b4ec957350bc1916532969cb162c14c1e3f346cf0ed3b9a368738f0ed3b24fc57f69d9a1528a699255aa0de3f8983a87877d01a6c49831ee2d24a8785603bec699716cce2b8e2d989278d3b69256421c49578fb095a76e2d751d84b9c0d37b10ab1a643c2be1df624aa68e2d69bca3178f8975e3f3309a3c7e52ea5ccd32f1f891676d8ca678d24ac0d308ac1212248974cc2e2d34cb50ea34ee78f962c1a6c49856a8619e3ed3b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part132 : Excludes 0x4000000200000000000000000000000 0x153155b10000200010010000000800000 :=
  finishCode 145 0x1701e3a2098310787761d44b9b50e23380d324fce2d5ab8335c5b30e64409835676d3b169a0d669dad5d6af34ec81ee2d6f1dc7b1fc6503c29a032d10338b56ae699437cc3361fc6996714cac3f9492c490659186440b126065b0e611eb0fd6ae49f065a08699390c115524a20506b0dadc5af63a82b5235cc4716596965abb4ec2fe0cd90e6c492b9960d3b96aeee388de3a86939a46973165834d94716c5a54409cf6235b8b492ac42f8973390d166992d2c4532d2c453987ee253308b0587f207d88e5a54409a66019927c8d665b440b10be25cdd424f8dce412b8ad676811532b0e6191b48c6e62d181920cd85a2ee350de3a866f893ea654408b4c1a6fa38849f064c66f2d299be412a204193310b629963459a654c23bc88162196958870b0543708854ca5a5440bf8ea3781e19a762cb5b188229ca1b3459a6588f34ee015914d4c621102c43904ad3b34c8e562d28c1e095b0b5a76d3b891688175019249f69dcd375199d145a6a65412cd3b224b06c6daec350a43f85737b19c330c0c9014809456acc29963308b45a461e188d634b240b8b42a6d3b064ce2d1b983354cb25cc93e0d37f19c342c2d30128ad5d469bcd3b716a5cc5a21079a76973691b4ee691b125fc7d19c5f1346618850dc3bd69db0b4d3267d4b9b78b20ef4cb71695437196d88ec499a765a56238ef669da5cc25648b877a973891700943c25a54b9b4ee0958b2cd32973427c513183b4ec9169736f194770196be1a16532b0e43c269969dc36b716b1246d7008da46e2d624927c3c338b58928a1a6404f207c11216362491ad87f1cd503e661 (by decide +kernel)

private theorem part130 : Excludes 0x4000000200000000000000000000000 0x153155a10000200010010000000800000 :=
  splitAt 1 104 0x153155a10000200010010000000800000 part132 part131 (by decide +kernel)

private theorem part128 : Excludes 0x4000000200000000000000000000000 0x153154a10000200010010000000800000 :=
  splitAt 1 108 0x153154a10000200010010000000800000 part130 part129 (by decide +kernel)

private theorem part122 : Excludes 0x4000000200000000000000000000000 0x153144a10000200010010000000800000 :=
  splitAt 1 112 0x153144a10000200010010000000800000 part128 part123 (by decide +kernel)

private theorem part116 : Excludes 0x4000000200000000000000000000000 0x143144a10000200010010000000800000 :=
  splitAt 1 124 0x143144a10000200010010000000800000 part122 part117 (by decide +kernel)

private theorem part112 : Excludes 0x4000000200000000000000000000000 0x143044a10000200010010000000800000 :=
  splitAt 1 116 0x143044a10000200010010000000800000 part116 part113 (by decide +kernel)

private theorem part106 : Excludes 0x4000000200000000000000000000000 0x142044a10000200010010000000800000 :=
  splitAt 1 120 0x142044a10000200010010000000800000 part112 part107 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part135 : Excludes 0xc000000004000000000000000000000 0x15207c91520001400000600c000000004 :=
  finishCode 75 0x781d058078e902c878f670a27159cd12c4934a8cae2b3b1254c714d416ee2d44099b4aceb2258da1a55241549dc6058a1b5c5b213548ec49058ca476248aa65a1ad5d8926895abc567591c5afa092e78fa934d12c4934aa08c49650e8278d94ca04d440a99605bc77d5b1e3f34cc00ae1f440a04cc5666d05ba89669ca9354ca4a9531207169695102b02976430b09cf1e61d818b1a559830018a861986e78f50ea8cd4cb3124ae73c7d2e678f741b4631847313c066b28bc2d892592c22a9058a28c49808a049427a534b4a961716c78730aa13cecf2204b4a9730c4c94d4b8969641eb1250c3358315a5b2494eba285510c75d4b9ca65624a18419a67b8b4a0cd591105c14c3c39a26532b124d2a679988ad3378fa99589266b8cf282b8172f1f2d2a20605cb085a50629d00b1022c0494b0a13c07b2585e3e679532cc49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part138 : Excludes 0x4820000004000000000000000000000 0x16a144934b20804100924004820000004 :=
  finishCode 135 0x500b07816aee0360c60f1d843c7cc4925983052db31242ae973254a44e59186cd8931a554ca4a93c7b600b9895278715fb12634aba89733c39a2653282c6693b80d82c0a83c0f83126532a5ccf0e3c776036725cd80259c2a73c7a13e52aa9942c60b99a6e787058c69578f8f1c5a3312478e7875816c3c7a4c66249a258720b1532cf1f34acf1f6c18931a55a6697315f9e1d8931a55042c05078045ad83b03c7060c4b34b9b38c479a5aa652909dd418214b98927856a0cc160ca65163c779259948416301eca4269733dc0b1344a5ccf0e2399b0581f07812e71e1c78e983a8787344c0c134a953e699a5cc1731d06625cc0d31484182a65670343148406ec39220b0e671580dda3734dc366787878ed41a2614ba99585b1484d2e400a0c00885b0581e06703663c7093ca65060951e63185a0af8182c4994c6a2581723c77c12c532cc47624b4ccc6668739cca6516090de532be09738f0e44d94ca973601b0581e076078e1b392e6ce04ce532830407715c4f0a8113b4b18d225ce06082c662399ee512c0b91e3b50439816e4b353290363c29a5dd83c3c973226ca653c3bc0b0360ec0f1c18312cd2e6ce052e53283042973124f0ad41982c19686a6500dc0b7259944e69982ccd2ec498d2a0b36998f1c1631a252e6787 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part139 : Excludes 0x4020000004000000000000000000000 0x16a944934300804000904004020000004 :=
  finishCode 93 0x441102a03c0b57701f0344c50b0b599158926953c78f1d60481d83c79dd669486cd892973624c0bd53299f653292a417a9737510bf19bd892a65624cce2582bf92e64a934a92a6059b07e259957d226a653c3b4878734ac699532c973781606c1f04b9c7871e39d0ce25cd842cec28b5329a6417a66994ca5478cfa4b38a8e1b36a1b45b1f0698ca6505b8b0589321fc16ea6594422c133492ce432a99403719a5a6646b344850e699b124d2a3c74c1a4630d2b03056033db11e694b1250f2973624cc3190c278734ab48e69ba5cd88e687060bc0f83807e0f1d98670cdea658e3a39d42fc64d532a996166b0b62b9a1b54caaa348c49892a4a95b14cb3124f0a65f8c264613a495066248afd4cab0240d41e3d9c624c1b353282f4cd304fd8921b33c2cc495b0cdf1a65e3f20a417aea20ee153a9949673c7d892c6300c47841a961714a13da3669705882e55443ecc49157998634cba82af8ca2689330c699 (by decide +kernel)

private theorem part137 : Excludes 0x4020000004000000000000000000000 0x16a144934300804000904004020000004 :=
  splitAt 1 119 0x16a144934300804000904004020000004 part139 part138 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part141 : Excludes 0x4000080004000000000000000000000 0x14b0e4914281005200024005000080004 :=
  finishCode 137 0x1c0601f05c1d058078ede1e3ddc440c5a50f0b50e2d691b4259b89602298ac72276902bc567306a19c47e5178a5614b6998c2e0c684dc472d330a5b8ae3aa9e24cfa881716969505f30fc92ac4978fad5dc5aa607862d2a205002c7cf1f6248784f1e5838b461e1259c1e178fb8b4f1e3c777140401d43c7ad5e716a9943c29634b6624a1250fe4b39e3ec4908dc50b1959a652e60d30f09a164b98785a6f1de52e64b3441d8581387412e6cc1e1caff040cc9ad1b195c11f2b9a8c60f095cd002b9c57f518c88118d84fc3c2787741c5a1e19a5ac493c3ad5c2c705ad707c1343c39786e38b6624a91dc5b31254627858b4ac49716ad5e0f0b8b4a56a653303c2c498c6249f5aba9952c624c3913bc9e158931da4c62ee2995892e2d0f0c699388cc25240b78fa3f85a56603c2a41989286d337b4b649e8da52da5738d3257f94ba64d06995fe518bf8de3e8d807856af122dc5a97315f928e2d8916a315abb125483307cca2a25716a91c966c0360a2b9102a653c38afc9442dce2d624a4866083e52eb0fd6aee2d2b8a9946f328c431a881716cb2b70fb09586e921e1cc7f31254ca63f9a5a88161ba20d81d0a625cdf44b0fc3c49e1e716a99549a8799442a65716a98e518a9767169e1d4cb1e1d482fa2c8e81695a5b21e54ca7875aba1e6515a44e5aba205c5aa2b515ce2d5329164f0e8795908d721e589227794ba5e1d0a65805e879624a86d462823488812afcc4943cb1262afc83143c92061d0a8acb4aaa350c01d663b492cd10240a8c64b998c6523ad5e3c3957ceab210d4cae2d51589f51025a5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part144 : Excludes 0x24001000004000000000000000000000 0x1cbbe49d7782504110004c24001000004 :=
  finishCode 59 0x3814c6518c5abb8b510278f83720b72b6c77d51ba5a4fc5abb48c49491bc4b4ab87518f1aa658ea21898d26a655289db65aa91ae581a8491c5b2994c4b1e3d6aad2d235ca47716bc7da4678f532ce2d5abce0348c63280b3816eec2c0da1e3da8438ce2b22ba994d26f1f1609a4e0958c2cd32617984ac49195acade3eda3c7d44325258925a1026c969532b124c572974d268553c79f89e3125e3f2994efa9693c69c878f78fc2174b49d85c5b307d46ec25581c5a76142fca6578fb11d0bf2995e3ed2d94aec2578f993458e0b13c79f80b16918924e248a372d0cc45532b116312a0c6532a996312ca65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part145 : Excludes 0x4001000004000000000000000000000 0x16b2e4997600404110004404001000004 :=
  finishCode 131 0x3f8ee3801e1480e03c7bb05a5716a204857194d4ca96952899a64b49696761b43805828819656f1f5ab844e1d0acade3ec3f92d28432b3a91e34982dd643f154624a985a58116879528a93570235c62b52e9204166b571d0ca1b699ca47623a86c8d6ca2a85a5320ca572b08e8588f0626510ac952e293550ec8791aba8554a2e2d440ad5d4c170fc716a48e025a5405abcf1f3c7be0ec368641988e687160b11e2b39a24e0032cc45712b12428614f319cc47624b11e696b07d4ca2739a66a51319b4b549a6957c12c622c2c16969de4d0eda295e624b4cc5824b39866d2d259cd2d2d4b80de350aa0b1d88f34b50da78f61c92cd0db21c6696b0b5e3e68734ab07e0c8b114582779058c923809696f1a86d1541638e46254b07e5a1b124f1ec3f5329a262549a1e3c7a1e6532ad5de3e2c13c7b78aa2d5cd2aa2b8cda589528a8762b2a85411729454c6be3507758f120b7259b787898916687531cda22882f8b527693bca156531b07cb5206f90eea47624b48b82a8b575b10ff30e5e3e96525982cc25f1e3de3e481618ce25226b124166f1f551a87009522c18ace78f52ecd330b3a995e3f349c902d419e6318959cf1ef1f532b4ce197bc7d89319e4f1ee0280981e3dd8624c679344959d47f25a50aa0b79e3e67959dad5cd43f1dc4b4af8c499c5a63344096951031a1e6129905c5a6879102641716a99625982c4b4a881531bc254c6896249a54fc43c9695a6709acc7ea1b624a86e696a996058b4b4cf2c49 (by decide +kernel)

private theorem part143 : Excludes 0x4001000004000000000000000000000 0x14b2e4997600404110004404001000004 :=
  splitAt 1 125 0x14b2e4997600404110004404001000004 part145 part144 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part146 : Excludes 0x4000000004000000000000000000000 0x14a065994200004000004004000000004 :=
  finishCode 129 0x3b0ee12e5f4731980f0b28d4368a6031c1925a59102a1d8b1eb2343fac8f034752d277d62498ae78f92cda5b1d75c5b34b525278705c9d35103212416656b1e3853e5ab8f1d892e2d9492b572458f1df0780d2f16951022b91e3b28d338f0e28f2d28314cbb318be328a603154c706950b2a652d29db643ea1654ca70240b57660c4f38b54ca82914499826b94ca9398ca6f1f9d45115415384be43e9db50b2f1f949b3c7d4ca82990fe2a797c3f0b4aa658eba78d4b4a9962a3ce1f6969985c5a8717c1e070189303245a63c7698c46b624a204372a6515f9e1c193033d98067a996153a996701b466143b189d4ca65f1c8b8b41860c97c093f0b4c78ea612a54c738b56af3c7d88ab80f1dc5b2d5cf0eea3126435bc7cd2a15b9e3e9456248afe3c3ba0f83783c77d1947f01967e1e1c3c277596aea65622b8b52d2c493b2ca3f8f0f2d5d8921e1388cd2d7169655892787065b48ee2e069952fcc45696b125102b573c3aa8e2d696c8596228c6c742a15804ed2d3c1143c385ae69ba91c722a158516e25532b46dc4b2d5dc5a9695328e454c43ea8fd4af089d102a5d9892de32875d8f028812d28314192ea3181e1622c62b1bbbc7da6eb57153b8b6532a5a4f02e2d987e75124a9db5946117c34cc0bd41100716a20466f387d88a78f1d0cc192a39d564b4b8b4f1321f589266133ea4d63c79a4dbc5303c25a591020b188d6a6543e83154c4b8cd213c7b8b4b4a881532cc4561fa1ad4920b9 (by decide +kernel)

private theorem part142 : Excludes 0x4000000004000000000000000000000 0x14a064994200004000004004000000004 :=
  splitAt 1 108 0x14a064994200004000004004000000004 part146 part143 (by decide +kernel)

private theorem part140 : Excludes 0x4000000004000000000000000000000 0x14a064914200004000004004000000004 :=
  splitAt 1 103 0x14a064914200004000004004000000004 part142 part141 (by decide +kernel)

private theorem part136 : Excludes 0x4000000004000000000000000000000 0x14a044914200004000004004000000004 :=
  splitAt 1 113 0x14a044914200004000004004000000004 part140 part137 (by decide +kernel)

private theorem part134 : Excludes 0x4000000004000000000000000000000 0x142044914200004000004004000000004 :=
  splitAt 1 123 0x142044914200004000004004000000004 part136 part135 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part150 : Excludes 0x4020000000080000100000000000000 0x16a04e971ba4800180002301205008000 :=
  finishCode 49 0x781b07c1d04c078ece34ecf0e281833ea6505f9a5c91b028625ab50c23189738f1e0b105fba82cd8d2ec419a76c494178ad5d469dca6561ba5b45722d3694c93140e9e3dd415fc769344b4ce3c7864c5120b36a10ff189d4a283769d86cc1824b5059c78f69168631887401669412d49171935a76a21519c769409b125a767759a52789498828585b3124d124b5532c1976249a5c96a81d8f1275505bb125a76c3f8eea567532b4ed8926956218c6701631a5417e7802b5a771e1d2e7180c418ca2c494b9867e3c3b126091b4ecd2a787 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part151 : Excludes 0x4020000000080000000000000000000 0x16a04e931384800080102201001008000 :=
  finishCode 157 0x77128781102e0360f82003c7580e83c7980c225cceeb030488320ad43a8615a1a76ea3180ab90fa2cd8d2e87f8166597530c77540cb125a4624c6370608accf0b350ea030505f1a5d05f34a547ac49059cd3b31b9a255043582c4e2b24f4b36d31903ad4398c4994ca0c125592d528f34ec3660c133bc0ad3c7ba0d40b1e05b92ac96ab034a66189e3c69734c5a66653581007f0f1ec2015669d8294d122b54b1c5334ec0a665d624ca65694a99605bb87e10aa0754cad29624865c16e6959892e6350d21a5e05f92d491b1a5ceea2bf8f0e689424cd2934b8acd886918c66015b19bc17e961d5650fb4ec156653343a99669d82add4329c9733c382954ca68958150157c693157c929698b10669da0bd892c378ca20a553299eceea86b944a6953c3ba0f8360f02603c77310e31e156ae75548fa51c942689833f0ae5104c12e719bd6aed3b3c3b4ee67055f34eccf6c4905fa87e6988155686a6169da80d42d5da4624c94732992d4f0b19b52766970a9cd3b3c7b50d221fe3279a1cca64ab61fc03f5329a5c58e96180ea34ccca71e250e338ae618a1fca26d3b3c4994e6a18469dc66105b8304cc334ec956901f878f69d9a2e624922e41ec9735ab82cdd4761cc4c1684b0cf6c625b63c4a076624a995a76d3b94cac49166c76540ea995892f021fe4b9b4ecb2aa65169b4ee05fc67b61183b046da7678505fa996661a861143b3c7da762af05bad0e29927a81d70fb4cc14259b31bc81d498a4f427f21fda760a1059b4ee0529e3da8781c062078e4ab8ed24b506092d6526cb5723c9a1c17e4b5620d2b31241620bf34acf1f5ab9e1cf131a5c15a3c7 (by decide +kernel)

private theorem part149 : Excludes 0x4020000000080000000000000000000 0x16a04e931384800080002201001008000 :=
  splitAt 1 56 0x16a04e931384800080002201001008000 part151 part150 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part154 : Excludes 0xc100000000080000000000000000000 0x17287edbc3a4000280080041803040000 :=
  finishCode 29 0x691b05f018aa63088812d2bc7e0d2a516611cc3b0c1b5411e030146718a5e3ea653c7a95504728fcf1e6798156921815693d92b22a98cbec377169874f1e8815f1103217dc5ac494ac86d4b4ac2220548f18a5c5ad356249a5ccbb3485892447660b4a8618afea1d624b08f1f92e6a1d154b4e6430a87547e86b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part155 : Excludes 0xc000000000080000000000000000000 0x15217cc302a4000280000001803000000 :=
  finishCode 143 0x360f0340d20f1d98520192ee1d9e440b12493e85b2d2834d2c400e232475892a6571695fd0dabe38b650d927cf0f3124a5b2995a72389716c9730699e1d1069dc973069ad5d4cb06b41a649f440b4ac4994ca9733c3b89e69da065892a65531f4440bb05a55101a6980a56490a51d0fa921946e973907a921327b8b5a4338b5b43c3c1b5532834d6841ec78753282bd4cb3105cc4c1805409064ab281437213d4ca59b989278769d993e40c8aa5a76ea1e1e43eb1241a6a5553295fe69ca4f455249f90e20d3255ba8981e8f1f90c2d3b53291e5683bbca6543e82acb171d8543687194caf1f05791e60579d85dc7d14c6d0b4acc3987c033d285329e0c49440bc7e0bba5b6014b115a76b239a76c494988a3e30ac46f532b1151020c54a8c26b69d833cf0e973440b8b652582e522a9596d184691980daae00c55a1a76787515c535430ad5d0fa3898c2a535237ca2b69dc84f33cad5d98154c1af62480c6237a89ccf2b574b9cc4703ea1f4f0e0cf69db48d3b943666b05ca4f4a6a761618c6794398d44f806799898299528624a08882204c5338b52e6d3b94c262950fcd3b523b4ee014b8b40cf34ed102a4b1bcc28f8526881066cd23e8be12ae2d2a60a4798924a14110ff38a5a768131c4b8b4f1e881690c2a9515b8b4f1e7e260b031258c42170518a91c5530a4d102d3994c62a950dc0a1532c5673c78aa4e04a17051bc6295328a4d102c459c5aa6578fa9356af3c7dc5ad3b94cada30886d9a762a94a1c53298da76a373c7ca3791020b7631700daa886716a20416e7619c56c41532b8b61549696 (by decide +kernel)

private theorem part153 : Excludes 0xc000000000080000000000000000000 0x15207cc302a4000280000001803000000 :=
  splitAt 1 116 0x15207cc302a4000280000001803000000 part155 part154 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part157 : Excludes 0x4400000000080000000000000000000 0x14b064c5c284000080800011001100000 :=
  finishCode 135 0x1d4731fc7d1dc6503c2a62a85a5740ed278505ec67d532c88194cac02e0bc2d00b73accc49435a1cd87f28cc78e69990fb0dad4bad3b3c7a97e532b124d32c03a078f6c034f1a6478ea6589026930cbc1a7490ca656249a65c07c17c1e3b38a65511a45a07220cb715c83d43e8056318a86d47f21f52d3032c4af3125a763913b49e25543bac7892cac969691b4600196d378f124b5216c63168e9e254ca78f891a4ab38144601e3f2955a76d1b60ca99435648d2c14ab2995a76b573f0c5730fd892a6596af38b5a767894b4b0fe624b4ec15a880acd7c3c386b6146a995145abb4d661f9e2586738b5892a5d94aa96924fa995806c10c3309cf0e6991598f1cfc591305f1892da34c6398a994d26a6596ae969398b4e640e9984e82969501a03c7cb57493c8818d0a67d994518cd3778fad5dc5a88153286e4cef2d5dc5a75131296857c5114ca1b98d3267d8372c498196c41440b60e03483c7650d33032d4bf21f4f0ec493bac87d651a424fca550de92d4eeb25a4b4aa3f9c5a4955aba86d4c6f1845c17c4b4ca650549695403c4cd3b493ad5cf1e48d9892633440925e52eb4ed28e5a53c79e3e69da49c1425a5349c677908211b5abb125a0650d33031478e0b94b7c9270549e3c54e6259c5a62b715a9952d25a54408acd9c6f1a07d0f1e0b70629a2e6249695a764b534ccc2753160440b4e652eb104cde699690c4b50d2b8b5e3f297c96a66f2d2c3c78d264ab (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part160 : Excludes 0x84001000000080000000000000000000 0x17bee4d916ac6201800040090a1000400 :=
  finishCode 39 0x6514c4c0b4ae81e3e246a5a51024a15a11026379e3e78f223b07d2d2695223c78f96ae8815a1846d1bc3d037a4b51c0cd313359ce527a78f9892a0310cc02acd0b34ec702c4978fcd334a3a58c8ef1dfde3e64190820ab61fc4b523bcd3b32ea56496a66b8702c4969d82ddbc70fca31499b4ec92a65d3c799e520660f1ee8230677349a97670fa5bd4bb387ca2f38b4c82d31624a995a7734cd28ee82d5e420a994902f1f94ca477 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part162 : Excludes 0x4201000000080000000000000000000 0x1cbcf6a3de84420180204029001080400 :=
  finishCode 37 0x7d14c740b4acc34ee245b0b509a4b5337922e69d92d584440ac084d9a7678f15aa92671584cc8c7309da6678f38aa59530421a8660956e299a4295942fa1fc16e5678a4ef1f52a9e3d983b0cd3b34ca1c50fe902d5e699854de3e17769dbc7e5ab865e49eb4a547ed3b15a92acec334ec956d41f8c234c642fa5a58922b55412851bc693620c68b3c79e3e41bb124ea320bc16e85f15aac0c2d8d16f1f0d49e3cd26d3192d2871 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part164 : Excludes 0x24001000000080000000000000000000 0x1cbfe4a51686402180004009209000400 :=
  finishCode 101 0x3f1644c19c624a98c225a5bc4a0e8290220549b38a5a760a396af34edc52881814662594c657d42fb08de3185358ec25a1580e4232c64569da994f1ed293b0b11e345b4ee322b10c3f96ae0a9349a80b579e3ec3f9a76a652becd295810db244d87ea650549a2d66b34a587ee2d6714c2b1284b4b28902204e43289416ea6369dbc7e0599a6650abc7d4cab573c79e3e611a86f0582b239e3eb5769da0dd69a0a996af22041468379a7685b611943b0ca415abb4ec166f1f8152d3b5ab95f6330c86d69db38e025a5886a0cde5c38ae53182dc87a46551bc51d714a2054caa379102645440ca2b8aca85f4b7a17e337b4eda8701f03e058282299564623ca1b1acb4e50827213b0905e4a3b4dc4a2881580f1f3105442567623b106417a9882f9e3ee2d440a0be312ad5dbc631946203724659c5a88105b9e3e595bc7d4ca85b9c56a652d0bc7e232b8a4ec287f490c69305bae0ca286e05b86e50bf2d5d436d3b92761b9532b78da18963c7a0dd0fe5a1500ec2e2d9a764533c7914e616c78f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part165 : Excludes 0x4001000000080000000000000000000 0x1ebee4811684400180004009001000400 :=
  finishCode 59 0xca0785647c0b4ada3503a178fc0ad6988b054ca6539872d3b5a1885c14005582b5a7730fd88ef1f612c9638f1ea5d616ca1b9892a6569d959c31734ec742c253c782bd70411d0440b10a0330e275aba86e240b094d324818c8ad3b6d1a77159cd32645816ec2561fb89e5abb0fd4cb3094582c43687e28067d698cb57512a994eb2d3b4a3862ceb3299544ad3b5abce2d50e9d64a051bc0b7532a1063c7862d2df2974582b5769db50a5d160ca653c7cce308f81e02c1551c57028d2d24774214ca19798928411359e3e716b0654cb02a4c821976249e3c3173c7cd32a65054ba078f526cd3b349b125a62969531865e69db8748ee969054ca653c7bc7d436a47 (by decide +kernel)

private theorem part163 : Excludes 0x4001000000080000000000000000000 0x1cbee4811684400180004009001000400 :=
  splitAt 1 125 0x1cbee4811684400180004009001000400 part165 part164 (by decide +kernel)

private theorem part161 : Excludes 0x4001000000080000000000000000000 0x1cbce4811684400180004009001000400 :=
  splitAt 1 117 0x1cbce4811684400180004009001000400 part163 part162 (by decide +kernel)

private theorem part159 : Excludes 0x4001000000080000000000000000000 0x14bce4811684400180004009001000400 :=
  splitAt 1 127 0x14bce4811684400180004009001000400 part161 part160 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part167 : Excludes 0x4000080000080000000000000000000 0x1ca5e58102850010800a0001021000020 :=
  finishCode 101 0x1f4771d46503c2a63405a56d078e68b8eaa78950dcd3b52e8574cfb1d54f128816d15468ec159349a99478ed311d09d65a46602bb34c54ca6931e3cd3b32985761a8c3590ae9d065b92e6a1b2cda91d30624c1af3c3b8b633e86bd4ca9a3305a55812e71e1d482d3b1e39a4d0ff30fda764ab337b12496b34ecca6965781986a16025aa126624b4ed0be49f4b99a150bf312493ea4200a3d92ca88169da16d0fe8819262d3b8d0a3c7294c81378fa454e6248b55184f2205c5ab4d4b2b30f1f92e668562498d6294a454e62e0300a20f1d8824692acf1f25cd02334e4f12c19532cc1942492d4ed27894b1d44d163b2d350b67591c89e25a42b8c96d165b4ec916109863276558e9988e34ee41dacd525296559ac3695a4b1261b4914e624a1245a2a651c89da53415f98ae328b4e4f12a65624a91c72248b9f0781c06f0f01658b45803c3acbe42d8f1d0b734c6624ad5d07686d1e3b10a5d9a76c3f4b9a86c78e69332dc3c752057ea4b9a76a3d42da1b4f061fca6569da5ccf0e973988581c04a0d16c01a14e63312435ec279102b579882973716a9957052ec0a9227ca65337cc49716a995103287cf0e5479a7697351ea204d260d3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part169 : Excludes 0x4000004000080000000000000000000 0x14a765890284004085000005001080001 :=
  finishCode 91 0xf83c0e0300e60f1d4c0f0b685a5440a5a63b4a946420a9956869dcc253c3b0b5a771e1d4c3c3ca374b49695102a8166e69d9e1c57321f5a76de0b05dc440c7871658784eeb286d07ac4509f8d0cf0e2cb3f1a771da506a87d441a7330b5a76c312d2b0fceeb34ed436e63f8c63282bf5f12c0dca91e41da1b5093347435ac334b49e1e5aba8c65ab87843c3328c612d4f0b1e2454266d854334ed6aea313c3c55f532a5a4572fa398ee2f01e15abca5d624b4ed0e62af541a6705dd88ed31530b125e3e787699cf1f6f1c055019af1f8f0ec491579a26321a5a5892aa2d5e531a4a5462a5d0d6a8c653055ee2b9892b576229da4f12f1f82f6b5752ea98de25a568650d121a58b4a6958f0f28dda76a3790fa65b54145720d4c62d27135bc7cf0e6c34ed0843e953e0af8ccc287196d4832d5dc0624c787157833d1031e1df46003c22a7819a95b25a9e3d9842019a96980eac250bfa1ce624a5a4eea76960c81f65329e25a76b5751019a88194ca2a73c7ca4b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part170 : Excludes 0x4000000000080000000000000000000 0x14a465894284000080000001001000000 :=
  finishCode 135 0x3a84b97f1f47714c0f09f8b425a5c05119443e99ee2199694636e2d427a5bd1027879c5a6374278a9d10320f457267b15cc479878e881651a82d291e605f8ae67c1c5aa1d94be64f34ba40c6114dc3f34edc5692170fcd3b153c85b5a1e06614532d4d6aed3b0628a9c572d4210d3b928ef1f4b1ad5c8f287d878ea295328f1e650cf303154cb21f5e3f19bcab2d291cc91bc18ae03c0f80b4e1e3b30c3388f22a725083154425aa51e43ea936713c96962491bc1720c54b0572a41656624a9956ae87f3c3cd3b41db126424997d2d2e03c0e6368d00b2c1a6c3385268493c3b4ec78e05992d274140ca0dda76f80b161e3a88842d0700a9d6af258d28ea538ec229378fad4d4ca9699a4205561f9195c5b2d5d83e2a7440ca6505cb4e5892b42882b9440ce2d229a1f454e837907ad3b532a0ae532831419f2f82b90dcc5a1532a5a6624ad5d102e8380ee0f1d0fb34ecf0e653069927e5ab8335a85512d324a437aa5525a9254d2b251d2d2d3b9a66b57631b4650ed325a54a6c4944086f5805208ef294cd2a67b98929698cbec49336c86b69aa94d8922a15314a6a358d2ec4992cad4330c03a0d016961e38314192a63e888125ac5a52e12d2433928ee2b827ad3971691e6530c965624969418a5a59102d3b0638325807814bf258c78e4b553134440b4ee2d2bc7e3b0cc4169dad5c93f2d5dd06010e334ecf0e3c74410e31d1d892d3b5aba87e440b4ed2d301a4c6e4492b5b4ed09287f (by decide +kernel)

private theorem part168 : Excludes 0x4000000000080000000000000000000 0x14a465890284000080000001001000000 :=
  splitAt 1 98 0x14a465890284000080000001001000000 part170 part169 (by decide +kernel)

private theorem part166 : Excludes 0x4000000000080000000000000000000 0x14a465810284000080000001001000000 :=
  splitAt 1 103 0x14a465810284000080000001001000000 part168 part167 (by decide +kernel)

private theorem part158 : Excludes 0x4000000000080000000000000000000 0x14a464810284000080000001001000000 :=
  splitAt 1 108 0x14a464810284000080000001001000000 part166 part159 (by decide +kernel)

private theorem part156 : Excludes 0x4000000000080000000000000000000 0x14a064810284000080000001001000000 :=
  splitAt 1 118 0x14a064810284000080000001001000000 part158 part157 (by decide +kernel)

private theorem part152 : Excludes 0x4000000000080000000000000000000 0x142064810284000080000001001000000 :=
  splitAt 1 123 0x142064810284000080000001001000000 part156 part153 (by decide +kernel)

private theorem part148 : Excludes 0x4000000000080000000000000000000 0x142044810284000080000001001000000 :=
  splitAt 1 113 0x142044810284000080000001001000000 part152 part149 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part173 : Excludes 0xc100000000001000000000000000000 0x17287ed9f705480005001000010600c10 :=
  finishCode 41 0x330d8348b00315463069cf43b0cd6ae18894d8c52e2d52a91ad0460cce2d78fa97cc572875e3eb4171698ce3bec189716a985e3f2994c52c49530962e4b9869dd4590d131a5453b34cde3e88133682de4409695547316c04ec0a914eb609622064b996954a6a6159134440cd2d2d2bc7e78fc88169682564409a26054ba8a619e52e729251029739a66a493a6c78d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part174 : Excludes 0xc000000000001000000000000000000 0x15217c892205480005000000000600c00 :=
  finishCode 133 0x360b8260f01e1d60681981e3a20668da924afe0c969164b3484cbea65069927d4c51ea956440a926531a8440bb05738afefa127e2d2a4874d84f2a6508eca5d41eb4dc02a0958b4aec3505738afeb609b669ba1b415e77d8f1ac314b8a13de3ed37893ea55893e0c91e3b102a99a36f1f05c86bc19b2205e3e2a96a1e068105311adc5a973066ad5c78ebe398ca2996309b8b46d6973440927c55338b4152a65691cf1f493969da473c7d2e60d36616aea3594ca625440844d2e61af51ac781067a5ce78f8f1d8073078eb2368a60335145b0d120979272c1904ac0959e3e95d8cf2f1f532b124b4b28f5e3e66b624a5b651e8335b434bc97378f99ac18a5a592e654f78f9a25a4064c0cd154c9732bfbe8ea3409822803b9a5ab571ba92d455266d344ad869548fca3315492852df3c7d6aeb62d5c1531a1c1664a994ca68778fb28be22045532995c5a4952d2ad8e2d148c2a904ac62b327b0a413b38b414a64f770a5334b4e9a4a9493a20496a5a55b15c25abc7e618a455c5a8710d4a1fe50154245cc47254ac8b834b6146b4b61949855e3ec4931acb57690cc43696b68b22c0b80aa5c5b02656ae88105291ae60c8255a4ef1f6a0b84912b6be22060dabc7d4cab579e3e86d716cf1f86e6e2d693bc7e5ab8dce78f82dc552b0328d4280b21400af624ca654a3cf1f595a56e78fb8b5456a5d716c0b753282bd863312585ac45693bc7c15e74d8efa375054b50e2d94ca96f78fcb57 (by decide +kernel)

private theorem part172 : Excludes 0xc000000000001000000000000000000 0x15207c892205480005000000000600c00 :=
  splitAt 1 116 0x15207c892205480005000000000600c00 part174 part173 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part176 : Excludes 0x4400000000001000000000000000000 0x14b044ed6b05080001010000004400440 :=
  finishCode 141 0xe83e0d8260e61e1da0701bc1e3bb80cb40cc81f2358c1c20ed3733ea985102aa312669b927d893207c05ad2d08db4dd4caa1d909e3911b5a994d32c0378a49817e13b4b1a9949524b54b1c0b96f12c5114ca49f2c4c1e108598c5492a554b4cee38881f9a5a9695148785893207d102a2984aa103532a5a589281f531dc523c3a144086761b598fe1b5a995d46d18c427c10b7149625a6ea650dca20437afa3001e178fc669532a5bda6f299493ea1d532cf1f90f21e125ac96f4adcf1f69b8f1dc075078efe3982b3714ca65493bc7ccd26990f0b48e78fa49c92b19a4d0a2a169bcf1f493ad5e651bc5b16425ab181b9814e88105bb12634989e414a6939102b5771699f5b4501d4254ad5e78fa99432f3c7d88ed2d43ca5a5dc53037a5a59102853988ed2d43ca9965abcd2d43c92a416f2308a3a88795abc62b4b4ad554ca699319b4de78fa49d2c6d2d8aaa8313428295e3eb57832ede388e6368ca065e78fad5c96a0c94b03c24012558933c7cd16b575b029f1a2da5b28f589276d92d24b583c2da3281ab91025a5062ad0bc190b570d58a9e489a5bcc2f25a54ca2a74adc2a72014ab3c7d6ae7e24814f988a6994b4b4c671699a4eda6179272a6569682e62d2b0088189560b90d5a8870218b5769bc60d514a99450259134296a634ca9255404fc819427927cc2730e5892a655149026220a8d493e613624ad5d4cac02f0b57832e1ab493c69934cce2378ca0784b4b069c17282069c56600d9c3ec455148c2d4ca78170fc00d532a5a5c5ab402dc34f3c7d4ca0a9518cb402e547b21e41461a778fcc4951aa94d4ca879 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part178 : Excludes 0x4020000000001000000000000000000 0x16a4449f2305880001000040080400402 :=
  finishCode 153 0x208ee250c02205f0741c06a078eb6368695896a2b525ac16d9a5a687429a99472b0d0de3ed330599a2495302e4f0ed8318e002e459b162cd2b1a5e4b9865e78fb50a65816e19778f86cd8533c7d2e60b3532c12351a92052e67877c1b0741e03c3b80d40f1d85328a4afe2cd532984e2ceb1254c265f41eb98a65691453127c952b6298613fb89d0e248d4b1ca61344c2b90cfa56c33f34b50f20bd0d7ba8c62b80b934bcc495328b04162a55414cc4942f9a5d4cac499052a6533da92615782e5a86d016712d458ec2d96ae66d5329a5c1671a25806c17c78fc0b305ca18c1b5aba0ae61483052e683d59dca53524985d852b579e3e84f94ca9735abbe0d8260f01e1d8005fc19f49da58c78e96378aa2f048b2bfc65f41ea9267f0b13312459687f692c57f52ab4b430b2995686a5524095fe624851e0cf86bd80254c63134392d478e0b90cecd2d318a07c42297359db78ea258687896a695344c87716392d569b306d892d2d05182c496a2b58582c0318b579e3ea6525492d4172b5792de1b325aa5ce7c1b074130780f0ec006465329a2478e96350a615e189315fd646a655a1a99632fcc297018531ce458246b860e81f39ca995892a61828e51f0cf86bdc0601e3f0304216c1b529b4dd6ae3c77516ae2c192e62d315ac4a98172b57691d405ca996624a14c5a6697436cc49157ad0a402c634ba58678fa5cd09e2cd0588b3640ca8f52e6c6350b60ad625a82ddbc344c8771639a1c5831d2586a641532a14d8930684166689336c85325ab124d2ec02d0c63600b3624c2a74b982e4b0614ca6578fad5de3f065d1825a82956af19bd0fe96f23cca65255c0b96f12e639d907687134ccb57 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part181 : Excludes 0x84001000000001000000000000000000 0x17b6f4c9366d484501000001100428400 :=
  finishCode 31 0x37896340a6125678f99e56ae6952b3c1bd42199e5a46517c32dcc4944086f496a982205087193d2d24a178fce2d5f0c9ed2d92d24954b4ce299892a65327a2054c691603b4c29d25aa5a50ca68991031a25e3f29950ee4b55516c432c0a914ea285a523bc8774a7c64142191dd4cb210d0ee5a5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part183 : Excludes 0x4201000000001000000000000000000 0x1cb4f4a9be454a0101004001108400420 :=
  finishCode 77 0x7d19477164740b4aaa3508c127c96a91f9862c4343c91ae429b11da5aae1f88228078d78fcb57235cd330a5b124167312566a75d5abcf1f61682ce245a1c5e3f02cc96a78d6613805ba30b439892d2d43b91ae6219e050a6d2d715cd33235a1de15aad82b5816e4b55c140440bc7e43bb4b4e9a4775aba10e621a1e50871d352d24a9493ad8de3304b55c091730c50e20b3696cc47436a9752d248b78f922e0ccc2b55012d28c35048b5abc877226c631429c4a9621ad5d88f34b5a87c16049056a78d9a5a9693b6c8c11ae699bc7d8924955abcf1f624a5848192d269924a98ae716bc7cd16a294b4a98f1f8916969349c87f621bc7c9167513c6ad5d645714453056b25a470a76d0d4ac0c40ad5e3f02a4f1b10a5a66f1f438b4b6624bc7d6ae46b9a5a96315a82de426a58c56ae2d8cde2b5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part184 : Excludes 0x4001000000001000000000000000000 0x1cb6f4893645480101000001100400400 :=
  finishCode 95 0xda3e0ee0b058c0f0ae05a9531c5b34b412eb57440828d88b02a5a4f2135e3ec1978fc579436c59d78f9a54cf2ee3e8b207856c6817c493ca6534982dc32f2d5ccc319f56af25a5c5a8812d29986493ad5da8381a030bc9334b1827452eb574b1c88114ba49e0cbbc7d84b3c7c15209d6917c5abc28d716bc7d4ca4a925ab8b678fa4cd6ae9339e3eb570cbbe8ee2981e16517c280b4a8778c8a96361aa5a5c5a881532be0c479e3ee2d23ba1e56af3c7ce869cc96961fa2065aac17d4b4a80aa3e0477532c641621a10d24f299584ac479e3e87953284be320b09416e831532b5098348be1285405abc199240a99661fc02f70fb11d6aa9697c091ab219e678fb8ada66c4934480ae5abb4b4cdab579e3ec479e3ee2d4b4920496ab57245ce2d78f9a5ccf2d42c05c280703c7e595a1e56ae95b3a1e3f2cac16f3c7d0eec49532a49dc5b31154ca8812b3a1954032188f21e5892a654b1a49c6e72d5da5b38a588a88161f8dcd0ca96392deb82c0be3480a3696c439054ad04f02c458152881813ab57884b38a5892781693b8b412ef1f (by decide +kernel)

private theorem part182 : Excludes 0x4001000000001000000000000000000 0x1cb4f4893645480101000001100400400 :=
  splitAt 1 117 0x1cb4f4893645480101000001100400400 part184 part183 (by decide +kernel)

private theorem part180 : Excludes 0x4001000000001000000000000000000 0x14b4f4893645480101000001100400400 :=
  splitAt 1 127 0x14b4f4893645480101000001100400400 part182 part181 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part185 : Excludes 0x4000000000001000000000000000000 0x14a465892205080001000000000400400 :=
  finishCode 113 0x188740972f82e0e01e1da81e38b4e24f8325d47f16c1658ee50ff1df5092a3d8efa881440c14786a6e63e8c012a625abf896078460f20a54ca49f32fc969532a5a624f8dcd2b70dcd27716954ca2b94ad8f1e6d1cc5abcf1f624832419ab8220ee2d5d944b4c87f2d2a20418ab61f89219850ff34b52d260f983ec45716a135686c2b854e051696a16c02f24edc5a935062c9134b7a5be2d283150e324ccb4a0c54b7ae0be34b651e87856ae29305ca5a644098ad2c6b574610878fc963250c93b78f8785e3f398fe3281e1530172a499e3e8812d28f8a498f1a951529a97e78fa9856c624a5a631ba1c54c33c7d2d2ca298961695102c498d2ac1f92d2b539e3e42533ca874172a625a633db124d2ac4994a64771ccc87f5a99a5ccf22b95c130770f0eea1695102de2996246878524525c87952ebc7c78ea6531fc49f896ad43c0e015fe61a927c5823c7595c96f70089f1ce58920cd4b4bc7c55e66210e618828d4ca6318a2659d5a19a24a27050c78ee03008819e3e3c7165c2c16f16ae61d90ce461595aced24e2a115fa15651a84bc742b5343ca995e075078e85f983248b0f08b05a8087c4952b9944e0a184bd0be5a5245b78f1f335cc4934b8335a661e15b14ca1899482631947a391 (by decide +kernel)

private theorem part179 : Excludes 0x4000000000001000000000000000000 0x14a464892205080001000000000400400 :=
  splitAt 1 108 0x14a464892205080001000000000400400 part185 part180 (by decide +kernel)

private theorem part177 : Excludes 0x4000000000001000000000000000000 0x14a444892205080001000000000400400 :=
  splitAt 1 113 0x14a444892205080001000000000400400 part179 part178 (by decide +kernel)

private theorem part175 : Excludes 0x4000000000001000000000000000000 0x14a044892205080001000000000400400 :=
  splitAt 1 118 0x14a044892205080001000000000400400 part177 part176 (by decide +kernel)

private theorem part171 : Excludes 0x4000000000000000000000000000000 0x142044810204080000000000000000000 :=
  splitAt 4942 123 0x142044892205080001000000000400400 part175 part172 (by decide +kernel)

private theorem part147 : Excludes 0x4000000000000000000000000000000 0x142044810204000000000000000000000 :=
  splitAt 1 79 0x142044810204000000000000000000000 part171 part148 (by decide +kernel)

private theorem part133 : Excludes 0x4000000000000000000000000000000 0x142044810200000000000000000000000 :=
  splitAt 1 86 0x142044810200000000000000000000000 part147 part134 (by decide +kernel)

private theorem part105 : Excludes 0x4000000000000000000000000000000 0x142044810000000000000000000000000 :=
  splitAt 1 93 0x142044810000000000000000000000000 part133 part106 (by decide +kernel)

private theorem part97 : Excludes 0x4000000000000000000000000000000 0x142004810000000000000000000000000 :=
  splitAt 1 114 0x142004810000000000000000000000000 part105 part98 (by decide +kernel)

private theorem part75 : Excludes 0x4000000000000000000000000000000 0x142004010000000000000000000000000 :=
  splitAt 1 107 0x142004010000000000000000000000000 part97 part76 (by decide +kernel)

private theorem part31 : Excludes 0x4000000000000000000000000000000 0x142004000000000000000000000000000 :=
  splitAt 1 100 0x142004000000000000000000000000000 part75 part32 (by decide +kernel)

private theorem part3 : Excludes 0x4000000000000000000000000000000 0x140004000000000000000000000000000 :=
  splitAt 1 121 0x140004000000000000000000000000000 part31 part4 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part189 : Excludes 0x1140000000000000000000000000000 0x1f4691115154000000000000000000000 :=
  finishCode 131 0x1ec711746f0972ca07857c4d1782d29c8749056b106037a8f545e971614c077621a99547b309d2e6a2f530c973056a68c498f0a9493a4868e525b12498307cb4b532a5cc8f6a4b530940a809b660da5cd4a6c495329d0c3578fc47b614b125a6697378fcc49622b0a52e73c7c336bc2a019b83467429762d2bc7d2e647b8b4ae2d78fca652d2a5cdbc5e03c2dc318c22902af5a5c0c3532868ccf223b8186a1752145f0a1d4b61a3532ca1778fa5cc6c730852e654f157868c337030e34ba5cd946b1697068c8f65a54c1103066cc5f25cdc5aa654408abe23daf0cc290ca068d7c5b174157c69705882952e7153d102c219892c1b522a994d0e8818cc671696a65148c695624cc1b9696c4334bad8ce03064b98abd89302b507b0304502f1f624ad2d1029735f055e9738146881532a5ce0c5ad2d102de25cd4034aa68a198ef2a2704ab0d6624cc2950c8256651986f1785d184590186a65815a5a5380a0440953e78fb8b54ca1a392e6e2d78fcb4b328913c346a6544034725cd04141868ddc615b11585328c5e3e88160dcf1f221ca57532ce2560dbc7c3462872d2830d86738b4b4af1f440830d2e6bc1695e3f3125696a2b1438284552c1981362874b9980a625cd4c338b5e3eb4b2d286d63bead2d4c338b54ca5a5440862d696bc308f21402a93914cac2988f6a53985297378fa5ce78fad2c346b23380a978fc47b4b9ad2c5221898cdb2cf568247b5412e721854ca1a34b9cc498a92c355a599b52e6a65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part191 : Excludes 0x1104000000000000000000000000000 0x17c4f0111505104000000000000000000 :=
  finishCode 133 0x3a8fe3c8ee3581e16118824c92b5e3f25cd893299564050cc2b4b49274b4a9025a634e818e696b4c56a681d78fa9952e6b00d5e78fa5cd25e1973e011f2995a77250c16a969244ae8b0020669d864cd3a4b96b12d302e4d3a92198d229958461dcd1f78f8e452360b5126c91b69d8906040bc7d286d3b52dc0b513ab4ec1020b59243e138532a90b0255e0cbb11649f823c8e28820807b81022af92e6d3b624bc7e716cc4952160049c2af4a1865db050cca5b716b0f5c5b3c7e157b4ed236aa3602af5a189320f5c5ad3b430b1264b5a0adc5ad3b716ce2d8e8ad2543bb125b4520962ba12b5e3f2995a76967513a5a5c5b3c7d25e957532b60ba02ee69d92e52e738b54cad3b994532cc2769db8b415a5a505c9216621e425caf8c235043b908ed314b4b10d4ca0b56b12d661b9c525a569da54cd3a9602ce52589d6716a5b6532b0d50c269d716c46134eaf8d3192d2c4353282e5a7729848c2f2278500a74d3a341988660f522b125e3e54f427a9956440eca45230bc7d88ab53050b124e6b34b503a26178fb18b2298c4994ca643611a5a4b4ac21401bd147cc49427a99543f007da76c49010cc4943eb115e3f29952d25a5924401184f15c148b116218b10d4caa35147a8d63512a731254caf1f51ea5a58933c7d4ca52f94caf1f4b3a55d64731152d2a651488a3d0ef21e564628f23086c54825cb30b42c819753016269d8b4a723855f1c8da7693f34ebc7de3f246d2ae17383168034ed2373c7c6aec4981065a5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part194 : Excludes 0x1100840000000000000000000000000 0x17ec5e117595844131084000000000000 :=
  finishCode 15 0x6c1943a11028c25cd9c0c5aa8a659a76b4b43292e4d0e2af418c85542acb4b34acb4b25cba8f1f42ac2af05592243172d2c9733c7d2e666b83c2881 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part196 : Excludes 0x1100040000080000000000000000000 0x176c5e991915040118184044008440010 :=
  finishCode 103 0xc436074388973751cc7b14c0f092e50b330f508263734bb8b51027c21ce210a1f5696b421063109c4d0fa8419056b429854f9c5a65d41a9a1cb4a7c183e530a1cc36ab4b55128b2185a7687d310c54f51aa0d5a7665d836a54f5a5845e69d9ccd69669525ccd3b814ac234409a1cf865169618b8972695532a205740c5c269344bc7d4ca68725c9a56532bc7dc45d1e3f0d9c9727a169488f2c6477a65d33c920253855e36778fa10407a8231b3c6214358ef41573c7cd0e8814a1645a5ba8e2328f6169510218b94ca3b94b4a99633d997634a878415319ed1030786440b88f6398ca3a863794ca1bd33d878564289cf1f055969508334ede3eb4d31b88f4cdb34cde3e0ab94ca69778f99ee289cf1f05599edc47b1cc5903c2a625a65329a5cb4ac23289006f449b0d9d082a650c1a10678f9e822d8c1ea6158cad346cf183c24a8414399d264ac997546b34ede3e1bd420a9952c3d0d2a74060ccf287394cad3b5a6c10778fa1ce09ca485a524450c18d9e530a01b39695102447927ad3b32ea995a77308902d06c21ae33ca8d678fb4ec3060798cd6f1f69d86d436b28f506b197455f1a246ce695 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part197 : Excludes 0x1100040000000000000000000000000 0x156c5e9111150c0110004000000000000 :=
  finishCode 109 0x5d1b034eb10ca25cdfc440ba8f6124c7633c7da6662f52d92e4cf33c7da66b4b23acf1f055a154972f1f9a66b4b25cbc7e14e924c972fa338c221960f0a8f453aca208fe213d102115840a14b6998755a5a49351ccd3340e988488ed2d32ec49378fc14b0f0825509ec1b022811c12b38a54caa61440878547b189483a82b78f98bc926881731ec7f1280f0808660d91d4e6630f78fad2d10254f9e3eca2f8c2169453b1ccdc4286778fad2c37aa458cf3197633caa8b630809d78fca657168aa429f18a5c5a54f78fad2d6973c7c12a881532cd272a7bc7d7c5314cb02ade3e5a55a5ca6578f82ad48a6798926e2398fe348ce328c63d8c2078578591544b9924d0c310b0a86194caa454b0a57643ea8bd0aaa6504cc2af3c6c771289a1e5a76e2d83062af2c2bc7e5a5a1e52e69738926942c82879e3e973440924d4cb20d5a76b4b716a2052e738b43c31d3615487841330955a76e2d0c5a5cd0ce1e1249cb22989816954cb2d2cd2e24790cae2d5a59185e3e687532b08a42f06c0a754b31135a7684733ca5ce43ca8bd696ae219e4afb4ed0f266b948b347de3e973517c97352db10d3b889e621598a5b5c5a18b14ea5cd843087510286578fa9942e6942405a5249a96e14281fd4b3111d4b6a599c5a9735e1cc69dc493157a5ce69d8a15e3f25ccd0e867 (by decide +kernel)

private theorem part195 : Excludes 0x1100040000000000000000000000000 0x156c5e911115040110004000000000000 :=
  splitAt 1 79 0x156c5e911115040110004000000000000 part197 part196 (by decide +kernel)

private theorem part193 : Excludes 0x1100040000000000000000000000000 0x156c5e111115040110004000000000000 :=
  splitAt 1 107 0x156c5e111115040110004000000000000 part195 part194 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part199 : Excludes 0x1100400000000000000000000000000 0x15e47c151140411004000000000000000 :=
  finishCode 59 0x1ac5d13c5e0d3ad2786368190f09695102f1f25ca4fd22efe3b8d807846cf3c7c6564b9624c48f2d4ac84b91abcf1f34b8d5e78fb4ce1b394bc6564b96c1884a0972bc2a0b339a769534b5ad2e78f87865a598de624b8b4d2ad3b0f0a4adf47f1e3f24fda7667925b878584435c65f4409a2510325a589334ec9468814a1780bdcd3b0f0ad2d2a69676103c2c49988a4995a5cf1f4b4b12588a5179a66f1f495be8fe21ce518929cd124b70f0ac897390c2881344a507028c631bb08c8ba881712cf1f48b8d4d69663790b2e2d49599b57852e928d50520c49d69dc287520ad2e624b38b02a04b94a9c19378fc97369dc96b599b8b4d2e8814b9cb4b716b06d662c4359a823c3c2881 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part201 : Excludes 0x1100004000000000000000000000000 0x154e56d51100514001100004000000000 :=
  finishCode 115 0xca298e222057c7f0b4af23d8c20784d2f25a496e96b9646a1934e927606392dd43f2994eaa0c724eb186971abc4610dabc7d8920c7532c81943ba92dcc7b19c791680f0a1de34e99ec18e6972a0c66b4b49a7418ec49624c4614979a5d0ef292c3c249d98920c750cc69d24e9a5d8c5714971a549324b75a9c87d62492c4d2a65194c20a334ea994d2efe308b22f02a990fa4a725bab8f6128c51f296c18e1e1063ca198ce6a5b0dc878418e29183c20c7251b98f6278c490f0927634eb11678facec18e8239a76a6534eb12418ea458d3aa5b591cc18018ec231256c421c2910d8a1e6335a91634037b21e5e3e33b2a78d5de3f060c0e265d4f174400d3a33f92d695332ec847297b4cd27e9c0a1652da186523a994d859dca57694a1accf25e153e523917488b28ad6920c79fc611204abcd3b24cb1869598921e115492b5e4336c1e1157a48c2b8cda969532ad0695925ec490519a5dc532985a62c49497a78f61a75500f0a976050a994e771276619b1254baa5d92d21e161168441643d0d2e7e19e588b299589208590f2c499504814caa5d9e3e2914aba54da76b5394baf1f148b4b6614bc7c53a9538cda2915329a5c53b3c7d462a654f07834e9976624b4cd836a6559d9ced4bb025525e9699892a5d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part202 : Excludes 0x1100000000000000000000000000000 0x154454555100000000000000000000000 :=
  finishCode 89 0xd80f0d606d12e6ee268b4b8cd60c1251bd869d060a98661abc7d696a5b42aa1e588b094e715b12588a4b934e8305c4242c88134e92e490b220471a69d791744f1b434ea9960f0831d4b71a254ca1e1651bc78fc637437ad2da766972d28304f824c9906699b115c5a47109dcd3b622814d8466879c52a615989174932e23b8ca3c7e18ba204b4ad33986668724cb0f6522831d1031d0d8464996514c671102c62580c11bec38d714cc43716969490b294cb4aa619c5ac1b8946b4b063b8b65a5b0a490aba278781a75605906aefa3b868943ccc490f0a9960b5bc7da4ec4933ca9150f31895432d271bcb12490b214d0f2d330b5bc7c2d7349de3e32f699cf1f591bc7f1847b1c478fcb4b624b8b54ca1b91dc9f01439a66f1f5a5b4ee24cb125e3e66b9c5ac4978f99ed4ca1b578fcb4b5a5cf1f0deb124b4af1f8946b4b6f14cae2d877a6378f12e2d78f913d647114c0b1cf1f5a5b8b5bc7f0f8698ca41227b12477aa65223cd31522b1243c2d3b517c867624928e69dad2d28624926669dbc7d6963578c4a4a378fb49e5a5b4edc5aa65 (by decide +kernel)

private theorem part200 : Excludes 0x1100000000000000000000000000000 0x154454551100000000000000000000000 :=
  splitAt 1 98 0x154454551100000000000000000000000 part202 part201 (by decide +kernel)

private theorem part198 : Excludes 0x1100000000000000000000000000000 0x154454151100000000000000000000000 :=
  splitAt 1 106 0x154454151100000000000000000000000 part200 part199 (by decide +kernel)

private theorem part192 : Excludes 0x1100000000000000000000000000000 0x154454111100000000000000000000000 :=
  splitAt 1 102 0x154454111100000000000000000000000 part198 part193 (by decide +kernel)

private theorem part190 : Excludes 0x1100000000000000000000000000000 0x154450111100000000000000000000000 :=
  splitAt 1 110 0x154450111100000000000000000000000 part192 part191 (by decide +kernel)

private theorem part188 : Excludes 0x1100000000000000000000000000000 0x154410111100000000000000000000000 :=
  splitAt 1 114 0x154410111100000000000000000000000 part190 part189 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part206 : Excludes 0x1805000000000000000000000000000 0x1fe5d25f3541985500000000000000000 :=
  finishCode 39 0x2d8aa2e82af5f13453282d4323296c4ea6439856d3b619ad5d2d71a756ae47184f6561532a93481ee2d52138400d82a12aec31832e967581863065ca9ea599602a0e0432b4b6044a9952a6a2d521a4ae78fa99589302254b654f0c1a54e521ac00898d3a197532a1950eeb2b96aea59321cc4949f9a74d3b31254b291b5abae8e21a75484b49b0643949a061624a9952d6a639c5ac49532bc7e48da98e52db1254cac298112a65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part208 : Excludes 0x1824000000000000000000000000000 0x1ee581df2d61924000000000000000000 :=
  finishCode 47 0x220f8260b01e1d485b12e6b570cda9960458abd44334ee48dad5d4ca2af5abcc03189539e3eb5705882e54cb18c455e69d96aeba2d8ac2b8c62a869d05c9dd6624bc7d49a769532cf1f2cab1256af0294d3a26f9a5aa6523782ecd3aa51817697368fcf1f2c4a8dd89269d05ca78a6543eca3714ba1ae601a4581485d14c7066c17244988e2f1f624866c17734b542ed3b78fb4ee23882e5e3e69d833662f157bc7d6c34eac076312455e74586da9159a4aa17532b4ee238b1254cb285d89293f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part210 : Excludes 0x1804004000000000000000000000000 0x16e7e31f0505d34005804004000000000 :=
  finishCode 35 0x7c1203c3ae8e01a752d3312527e9699892ae380a658c62a2178f91c4fc528c879526a10589262f985b29952d6c23f8d42782af4b4c879624826508325a589262f8b3af1f3c2c29d78f988678fb12510381a77060d6ae36f4f11834eb12678fa184306297985af1f49174532bc7e624a5a48cf3475c56a4d03dbc7e62498be14ba995a76f1f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part211 : Excludes 0x1804000000000000000000000000000 0x16e5a11f4501804000000000000000000 :=
  finishCode 137 0x17444097278160787238ca6505db8b52a6b5778fc953624c69d716a54d6aebe390d21a74b13211c876c45532b4ed89296905ca5a6624ca21622bc7c17245d9892471410bc7cd3af81e07e1e1c94581892a42d8b40abc33721cd4cb0234c62a6378fb46ce47066da6ed3b49fa54da773c7d42f21ad49af1f701d43316c4f184580ec157978c298c5ea653a2858583311bd03e36d3a2a456614a99542f306522b306d4ca745622cf1f532a9966116c50bcc33157803e00c983d236821238b4ee42ba0ac126e25439b10d543d055e5219a72b3553185d585325acc6252d82aa7110b499819b712c16143cacd50828579a72e2543ca935d4701546108e31d15056d3b4308abd44334ed056c434279d8a65983682f6219d1588b107d23646f61aa99588f18c4c5e8792c2866caab18bd0f2099157ac0ac290c2066cd06248abdc5b190d27ec2d4b581f6616a55d893213d2e6881d083d945ec2d52ca46da769734f189338b54b2c4998c240f83f185ae0312507b190de3e11f48da086510c44d78fcd3b510c2af624cb625ce1579c8e4b5b8b54b6c493a12a72d5da76861624ca1749fa48be290a654e158501100cda1d65ab8246610a20c49852e973416b08a63884ac49233a88614bc973416c87d624b187e22086b624ce2d78fad5da773c7d45f18c5a3a56d430a98e3178cc42da17944052ef1f9c5ab57307c84f237b11da76f1f631203f168624b46e5abb8b433686b43eb46e78fad07021848cf38a52daa5b521a566616b8b52b325b52e619b8c1e46f52db8b589246794c6c49 (by decide +kernel)

private theorem part209 : Excludes 0x1804000000000000000000000000000 0x16e5a11f0501804000000000000000000 :=
  splitAt 1 98 0x16e5a11f0501804000000000000000000 part211 part210 (by decide +kernel)

private theorem part207 : Excludes 0x1804000000000000000000000000000 0x16e5811f0501804000000000000000000 :=
  splitAt 1 113 0x16e5811f0501804000000000000000000 part209 part208 (by decide +kernel)

private theorem part205 : Excludes 0x1804000000000000000000000000000 0x16e5801f0501804000000000000000000 :=
  splitAt 1 108 0x16e5801f0501804000000000000000000 part207 part206 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part214 : Excludes 0x1800004100000000000000000000000 0x1267475e0804534031801804104100000 :=
  finishCode 147 0x174481ac641c034eb00e63c7dbc4b019a8a1a54ef318bd88eb2b5329625477311d0b2b43531989e51daf0d339686a3742c98bc552c199892a5d8d12679730e93389c82a3895328aa419aa65948e3897116c4e12d306b54cac19622a28a3192d2a6552e86b6532a5a6310a9954772994d12695440e0340d8197b88e320a9942def1f0a5b49cb5301d472228f532ad07c0a3e532bc7da66de14be34bbc7d4ba0cd361c4b190508e3915a9b89678fa97424f3c7dbc699bc7d4bb14bc19ab43949a52f52ebc7e3f1cc251106249f092230a65036c0730b9aca60358a5d86711bc0d216f101c4f308c89a96934abc7da769630ce52e89f4cbac339e3f29892228969622ce2521e816de3e2970ba8644702e27832256d7c114429cc3b3449a5cb530abd6ab0a3d88a7c389e116aa8e2710d99e62c296a4b2b2d0c01f07a1a2445b11bc45b389d4b6a2b851ee2734ba97470321652d328ad4cad3b1c8b088a1e8f80e058672ca4d2eb2992b2b3d87225799c4e5a9019cb2948ea514f878fb88d335b0846114aea318552a319656c45988e9517139a5d262c4906698be62483344af1a25bc52dcc49066a86e711b065c07119069154066b0844f82eef1f04bb0b452e29d5a123a945521cf1f6239cee78fa20c4961dce272a1a99548e65d78fcaa188613098bd89284f14ba20a659036a2f622a8b5457299548ef1f435ca2b34ba9958920cd7c06db197d892695595c537624bc7c52eb2220c2197466f34ecd2a8a2936712a994112a4750ac46f69da9951469dc69704bcc493e0fc532958600a803ccdaa63510c62f104c81b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part216 : Excludes 0x1800004000000100000000000000000 0x1267671e0505d30001814004000030101 :=
  finishCode 143 0xe61f8b2128d63125bc7c019a7c1a26532a4fd3c34bca2b3a28264d3aa158e8a6974b4947e39db4ede3e7c30c6032a935e3ea655a1c2a9347bc7da76f81f09420066254d2ce8a299413330ccd1246f98666979866a65988a73b69da4fca9f051de3e92b58184450e8024c29d50da975a769e34829d226cc23621b89c8de85360cca2b61191be60c9a5c55f25a453a5439e3e05b52eb4ecd2f34ede3e83560cb08d2b32d54ada969532b4ede3eba3d8922a89695b16008bcc4769da4fd4ca4710518275146907031da47221918ed277594ca8a0e06310962509f025566ac4778f98bc19a9618be53294442ba36d2c4b89e4a1805cc5ea65066b78d63807758d2e0cd528c853003a1e583246f3449a5d14511847295d0a66895aa96a451ec19987668934b8abe2d4a18c338146a253bab0ce34e8675c06a1c4b2935286a651548335e3f18bc13aa478d12a5d690d2f0334cc50aca6531785746da74569dc45d3179485a4a87314bb20d4378900335146316c2c14c710fdc4a7353c481154baa3169dae866d887e96969c91bc51ea3134e998a478122841048ca4753198be048c11934e988588f298c8de3091b69614c5e69d3e0cc5a9cc47532a976317851d6a6b538f85b14ca2af925ea633c298864b584354c674969ca5a640ea95da767754b4cb3522e9a75a76a1b90b266d495a5ac19a90358e01a75a772994c426973a2824c19a8798c5eae2c0d3b8132c20e061c8b4ee227a5b64a2b80d435829d50dcf1f31083341333c7e05082644ff18bdac4f0d834ea1f65289a5c13a8594a1a5ad2d30e4434aa639a6af1f43e86952d28a2d0c0028e08d9c45436c3b3449a5d0b30e45e3f34ed2d23810cac969 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part218 : Excludes 0x1800004000000000100000000000000 0x1267469e1110535101800014000004000 :=
  finishCode 137 0x1907c1b06f0f0ee2398d22c80cd6102073c7cd3a66b34ab4ce78fa45cd3a9179e3ed3334eb4e60439a5cc42aa2d08a1a550c2d3b834a85952e9a2434b18c60d28e04d132904d3aaa1a74d2a86b8426f1f526b126344a0f640d913d4bac2d624bc7cd3ade2e8a61a7564550d2ab3b98921ad14e9a26450f878fc96769999b5437167527b2884b52a253616c5512c450cf2c2d8a2ea2f040a975a5aa312ceca2f696b4ce59d8a74cf3013545e94378fa8c5a67113dc5254f5178204cf2d2d517c285157953de3eb22d86953617833cb4ce69da8c453a41d802a01d693a8bd852a31855ea659892bc15e6510ac8d6a65851578076699a194d3b388aa03350414bbc7e624a9950d696962298be532919de3ef1f98929696229a753c0c1c62f6248a5cd3aba2a8b62587695a4c775526c83d41ecc494b048318bde3e6272118c84eaa15d2cabc7e624913e510a935243317c5914cae62a8c49531ec3bcc9693ba86b660d89f50e7306c35a38930bc96978fa50cb2a6c145e4a1a78a15864ac1b3188e45a5a1a150ac60f439b88cc62391526a9464b4860de3e0cd5e1f048dc957066cf1f78fc0cd7c0d0360a2f060de3e9434b5b08e611c53c624c277528860d0f28738c2aa63066899e34ba9354a20cd9287255da42c4cc4943e860c19a86b9f05e1bc6114c3e0d2aa2588e296b36189287d944a943439c0495269b096145e616983d682d2d297a855e3e94333c945e78fa50d2d61499a5a5a150a983d4ba47178f860c19b14be78fa50d2d61836f1e3e5a1908247134b89f65a0c5a1624bc7c3060cd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part220 : Excludes 0x1800004000000000000100000000000 0x1267461f0140530905900004014000000 :=
  finishCode 125 0x1f0541bc3c3a98b22cee34e8abcd12695551a85e1145b0cdab538d3a8791579a7649fa1954cab62995a670abda4f34e5086d33336cd334b3cd270b59a75a5b04b52d24716189a74cdad62e8661b07a2c89019e5c034ea59e522acee522c8779a5af1f5329a7545b05acd3ac47989245d4a9953cd3a967946269d78f8a756c551c0532c29d2c2c46f59d99e6516a14e532998a224846f432c5a914ea8c54cab2b853a2af967629d9204b3c17b34e8876618a0c455ea65699bc7d80591846f14c6b0d126957308e2859819ac4942cc065237ce6350d22880cd522c38123781c65a9bc7c55e6219e3f0a16430a1ccfc4818929e15866908e244c669d341e3e62f949a471616c19d90aa2a378fb5828b855e86534ea0be317bc7d0ca7e358f1f624ad0e32e9a748df0cf588ea47594ca5b2378335bc693cf1f066bc7e591a06da5a29d34ea28de298b0197dcc6a154066c2a90b3ca476239e26522b11c50b291dac4b4c0cd34e806603eb1254329691c8a78b000de317896d48ec2d142b89661a9cac102b5334e81f64f07232d4dc4a2af2b09a7585b2165606a1cc066c2af408c917591859d2d2543616a5a63bab11ce834ea1f64b4ac8d686c499ac1b7b4829794ca17f066919e60c9a742fec478c5e8595a1b1254ca297 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part221 : Excludes 0x1800004000000000000000000000000 0x1267461e0100530101900104000000000 :=
  finishCode 135 0x7c16aed82c8787730946f1892c22286c1a24e833c81ae52ea9942a6d2d94ca96b03aca5d066a1ce50a983c35a15b2d491bd4ca6c2a818332eb4b650aa4f546ea159a5b259542aa650c1a98a3794ca0a145089b29050e6a5d439cd2d5a1bc4b11434a8e262c496a6066a987c183e18a892c30696b066a994d12aa3480a3008ca15307b0f4a5ee250d6ad4e50ab894a5e92f819aa57700b53295c19ab25967a92028cc5f01440b692f439b06c71290380183713c8354a1a5aca5f29754bb0c54c82a15114a4bd145502a32c954c643d42086b472284188df215419a9435a14c3e0d2aa5190e615b131a994d121a592d2a5d4e10e687d088c30d50a983c30628f532c8a250e52e8e4524311286969532acd64158486696a855886e23105c46f696a8550569430d2b507c0335c47183da42969039a9952d32d4dc4ea15147ca416415834ec18334ab4ed641aba58841a5d6c624ca5d696ca2d0adb116516a915892a5d82d6a19624aa8a2592d2a514b4c47150db0c4f82e0cc0a9a28a65520c86552ea98ba183e1aaa8544c619d616c5a988e25a980e26892389656713a1e564618332f9a254cab23981838b52c490f0d2a18359da97484f34b461aa15307ad36696a8552d32945c4ec81a0e20dbdac622ca654b4b124d3a0cd4f08c42ccc49045b08c89aa6550ca915245114cad3b810a08969dcc1b2d4cc2369db1265508cec493baca65611913d4cb308dac4f019aa2d989269d618c8730c1b4ed892aa34ec3065a19862861624c28f691c42cac94160dad04b52c4906696865328a3d892a658306c49 (by decide +kernel)

private theorem part219 : Excludes 0x1800004000000000000000000000000 0x1267461e0100530101900004000000000 :=
  splitAt 1 44 0x1267461e0100530101900004000000000 part221 part220 (by decide +kernel)

private theorem part217 : Excludes 0x1800004000000000000000000000000 0x1267461e0100530101800004000000000 :=
  splitAt 1 56 0x1267461e0100530101800004000000000 part219 part218 (by decide +kernel)

private theorem part215 : Excludes 0x1800004000000000000000000000000 0x1267461e0100530001800004000000000 :=
  splitAt 1 68 0x1267461e0100530001800004000000000 part217 part216 (by decide +kernel)

private theorem part213 : Excludes 0x1800004000000000000000000000000 0x1267461e0000530001800004000000000 :=
  splitAt 1 92 0x1267461e0000530001800004000000000 part215 part214 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part223 : Excludes 0x1800000100000000000000000000000 0x1265455e4000014030001800000100000 :=
  finishCode 27 0x1f87b0786b02904b94b9b2069731ac087696a96cd3a0c1193cf1f624cf1f6968304c6a9e21869d34bc0c9624bc7d48a69794327c030569734cda7734ee699b12588a69d4b98335c46b0972c82900c92a1ce2b518bc7ccf269714ead2e69dbc7d2e60cd9e3ed275a58ded89244d94ba2a369dad2de3e973451a772d2d2e668969dcb4b4b98a8d4ca0c1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part224 : Excludes 0x1800000000000000000000000000000 0x1265041e4100000000000000000000000 :=
  finishCode 157 0x1586a0b56e43f0f80f0d506d0f0ed219ee0608325d434ec973321a995c5b121cd3ab4b699c97334e91bdc44b9a0fe5a592e4d3b1a25a66b4b532c69d5a5a5cc192ba2c0d3b8ece9730d792e4f0f34ed892b4b05e8304d3ab4b81827876b1a44c01826611c638d92e5c5aa65237ac0d258712c4934b8abce372d2d442a633c3ac0a6596969734314cb1c6c8e2e2d969671b532a60a82987874b9ca6533d99e661988152e683f25c92e65a5a9164b9a995105813025ca5ce5a5a9952a22af624a5ce52cc787716ad2e320972c631257c716c69d5a582cd88f1a748e31c6d2e6951714b4b4cf683d8cf269d6939e1df86a1901e1b60a83887876d174064b4b6532b8b56ae4b94b9ce2d521b125c5b34cd6ae4b93e0a05814ca511986260d044a5cd6aec2d3a1cb575abc9735abce225cd8930324972ea311e32fad5cd2ec318862b3f78fa90b22587019acd2eb6296dc571645436a2d96ab28bc1021ad8c1ac491c48d5d6ae68950caf8562d5dc5aa65028c9695a6ce2b045a4a50cb2d5ccdae2d716c60d624a9754ca3575abbd8f1f5abac84b952ec82104299acd2e57990f2085716c085066bd8a412e564360d2aae19e4e45b08e259d9682a47624944c2d60b369ccd2d61896256c2caca312cea45e1c8b4b548f34dca2e313624a59d4bab628c65ab82c522f1f88a25a58c48ac66d2c499b6495ce255aba8ed54716859e693b8a4cda5a9336c5956316ae595840a60d32896752d2e2d05899b66c1902c14c541843c3aa897334aad5e48da0f58930a3ccf628f985ae2d4b9bc7e699b8b56aec494b99a5522f2d5cf0e91792e6d330599a54f0ec22d5d45718348e2c491c49a5d4bb3125c4b0d5dc5ac4933dad5cd2ac82a058260e21e1dc5b29952a6b5725ca86652d9a549732d5d2571e1dc4063ce2d78fad5c972d339e3eb575abc4b9 (by decide +kernel)

private theorem part222 : Excludes 0x1800000000000000000000000000000 0x1265041e4000000000000000000000000 :=
  splitAt 1 92 0x1265041e4000000000000000000000000 part224 part223 (by decide +kernel)

private theorem part212 : Excludes 0x1800000000000000000000000000000 0x1265041e0000000000000000000000000 :=
  splitAt 1 98 0x1265041e0000000000000000000000000 part222 part213 (by decide +kernel)

private theorem part204 : Excludes 0x1800000000000000000000000000000 0x1265001e0000000000000000000000000 :=
  splitAt 1 110 0x1265001e0000000000000000000000000 part212 part205 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part228 : Excludes 0x31004000000000000000000000000000 0x1cefd3151c31004000000000000000000 :=
  finishCode 47 0x388c4338a212e5a4430fc349a946714b4ed892a6543ea88623399a52929399a4277134ca9950c6b0a7325752e219390fac4904ac457616a9954a33475242467622b124b0aa655b174342b12604ba58547a0ad34e94e64aea5c52933484c9ad3b04aa5c4d3a6695d13c500d3a1839a7636f491a3b31254b6a6550ccc493514c051ca4b4b4bc7e624a8f4cb6f1f9892a21987e2995e3f31246df196d2927818a7295d4b8a1ade3f312452ea655d188630cb71a6417667d94ca693694ca6532da92cd3a86b8d26a65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part229 : Excludes 0x21004000000000000000000000000000 0x1dc9c2110c21004000000000000000000 :=
  finishCode 135 0xe03a8c6278d62d849324eac0980abd2e72994f0ea6594a31a74d3b2d5cf0ea654019c244bb065b8d3278d157ae8c33943267d62496a4f1b310a65945e7874b99a14f0f310d83b0b578f0e973317ca65716866d6ae78758144342c19769da96c15a699433c75d69d8abd24047cb3b69da99416b296d8930abcf0ed6308ce12c574334c96905dac0f1f8552c45232a1654ca69333eb8b6532a8f618699bdc5aa65342a68c425a648db124d266996c1892c45927ea653c3905e526ad5de3ec45532996d4cb114423231d2a6b0acafa969671884b4bb0b02cae61bb4e4d322af25c9f00b396aea6561ec94369dad5c16a19794ca0b33bbca65624a9960519a14ae2e23386a330969621d8326cc457169a654c62af25cad88c1a14e02bcca4333eb126624ca539892a6533485ce3c39a758927878972d83b02af94cac493c392e5203c39a16532b124d3af1f989217f98929e31069d3c3ca654b99a141470ccd4c265b698ca3b532996cd0acc310a2278a65349a98e334a96503ec4934ea106613986588e669531a87e613a98cd3a67d532926632da994d3b360e23b0cc12e56c232c78748d9a4cd329e38b629cb124cd2781334ca5103d9d84e7b25ccf02b62189698d3ae2d0599a4dc5b18bde3e92f34c82cd744f12af1a752a70a2417607b8ec278176198157b12623a9a64e3b1a74f0f34ed2ce19b34c8abe13d9a65886719825c864623f82ec30725cd70620c0ad31f866cf0e47f988263f51e9f8787051ca65147a5a5892a65814269d (by decide +kernel)

private theorem part227 : Excludes 0x21004000000000000000000000000000 0x1cc9c2110c21004000000000000000000 :=
  splitAt 1 124 0x1cc9c2110c21004000000000000000000 part229 part228 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part232 : Excludes 0x21000024000000000000000000000000 0x1c4fe6900902430861000924000000000 :=
  finishCode 71 0x220a01c0f82d5d904a1a76787518c47f69985fd28654f9a66e0308b3b947a4ad258acee5a189352d60cf5b0dc52bca610c1a9754413bca3159d860c51e1839462a354aeca65641e451aca650679a7489f0a3c306d3b530833c19f060d98701f06119024ca9961548cae59d833cea2a657910b315f5462a5d69dcc493c381d5a4624c69d78f85dd4c20cf624ce210c1a7878743cca5d34eb4ee5189e1e067a995986115c481e424cb4ee624a99419e69d32dc467532833d8931ced88ae212519e1c5170aa546a72792d6d27067b124f0f3e0e0308c624be4b5833c95a4b16a019f2994f03312525e49948019e92b984296769da4be624ad8c23851ea3152eab8e218d3a8794aeb4b4ae2a659876d2119e532bc7da76a610679a76 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part234 : Excludes 0x21000004000800000000000000000000 0x1c4fe69281204309a1000424840800100 :=
  finishCode 45 0x330f8380c22f04a334ec2a9258b60b579892787522cd330da9a75905413c3c3a8be34e9274afb196d892d434ed6aec49067cc2b595b4a6021b8a509ed332beca41624833c93ac82b0787312cb2b69da9958921b934ea285910dc983e622ad55892a5d696c9e2d5d283e08fea618616d27532b08b3b8a2ea610da860e69686d6696acec296a578c4aa656719006795b62339a7546b25c4ada4576414c2f213869d69dcb57227996da3b28f489f296c6e2a3d51ec65b2338a3d45b033cd3a787 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part235 : Excludes 0x21000004000000000000000000000000 0x1c4fc6120100c10821000004000000000 :=
  finishCode 125 0x128661102e0308f8320499561b0154c69d50fbc83798cb6a6569d8abcd3ad279a661834b48a45a45e019e967855e54f32dc1b96999e1e6248abd436a3592d6d2338c8033d3c51bc29734e998c4994ca87388ce65b04aca3d2caa985e3e1833114971a754c2a827044f946ea3d0518a3d47b196e51eb12590233c29734ea8d64b8a9948aed2320d82a00cf41ac9696249e1d04731256434ec49d78fb4ed892f1f9a66a47227996d4cad3b0c1c96b78f833cd3b12758929e36069d3f0f0eb22b8c49147c589714ca51531c44f512a9954cb06e5a4f34cd2d2c490dca20a65710f0e57d92d2c490dcb4ee531b4c437328c54c6a15532c0cf3c396070240b575d1906c1a769699846a4b34e8d5cf0e3579b07c14c27e12b54cb308429627d420c52f147a8f419f0a3c373168495a87d9a7606b532833c9464ad8f0ec83e0a8147e34e953da7678734ecf1f69d926549f31250fa69d61694dde3e0cf69dae80cf78f9265893185d47a5955309066532b125f06c1743c3a40ce3124d3a920abcb53296c6f2861967aa1b947a379530a8d65a18abde3e2af98924ad701ac5e1a857055e499889ea6505192b45230dc52d2d339e3e4ad5d13c50cc1b9699bc7cd3af1f9a661b9251c2af93c570b2269d3f0b52b2396a6c49523cb539c520375aa96865a9a9943729e0dbc19eb2b8af2c49516b126 (by decide +kernel)

private theorem part233 : Excludes 0x21000004000000000000000000000000 0x1c4fc6120100410821000004000000000 :=
  splitAt 1 83 0x1c4fc6120100410821000004000000000 part235 part234 (by decide +kernel)

private theorem part231 : Excludes 0x21000004000000000000000000000000 0x1c4fc6100100410821000004000000000 :=
  splitAt 1 101 0x1c4fc6100100410821000004000000000 part233 part232 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part237 : Excludes 0x21000000100000000000000000000000 0x1c49c7504004010010821000000100000 :=
  finishCode 133 0x198760c84b98f0dec624b38a278d26f1f30c9a7417eb4b25ca68a1986e2e2d5179a64d3b3c7d44ef1f969669d7b14c7113c25c9e069d297c67778fa94d44f38b548aa279c52677622bc7cd32e2d4f1e3f296c17e69d3c1a6f3c7c182841530bc7e532b49da731984ae2c2752292e4a5f28acd3aa61693b58e2318ca2e80c9471484f144ea3d19aca5b60e9a7583b278a81a75433219d696c49253b1265a5a535a768555418832d2dc5aa655a5cc498d1669d5f0fc4a0d168634ee716b124ceee2d9892b1d43bbc7da7334c5082c491b5cc3d34ca19da76a57716a576624b8b50864a74f012f31254ca73d7169a74f8435c693532b8b678fc66942aa94c19669d631804f0182a81a7487b2994d162579e3ea615a5b12550613ca61532b10612bbc7d4c2b4b624ac869d620ca45253a89e1c29a76180fc6718928a25a548b11d5e3f2d2d45e68b928631605410cf28bcd32489431c4b042d696a3d43ba19d48ad3b90a6e25144c4897168a2e60ead2cee236950cce2d4a1a767820d652db1146d6e2d33bba8693716a18652ea1f5a424656158dae4b4ca5d60e91954b6e2d581385d12e6e21f04b9620cb31696a864912d275a5a9957851ea2862f52cc44d04bbc7c912c279856e2904ba96e622aa8f228869d5a5cf1f04ba89e693cb4b52898667c114148cf1f04092241270abc52f29959069dcd27214bc7dc5229734e95e62c8a995a4eea358a655d1c5b033c92669d42cc493312833dc5af1f8912c835832f9a76f1f34e90c62279e365a585bc65ef1f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part239 : Excludes 0x21000000000100000000000000000000 0x1c49d7115104004010000010821000000 :=
  finishCode 79 0x330d43b0740f0d9c4b9bd8a6328de2d56611906dc4288134ead2c1820c97c0e8734ed69688134c9e1cd272994d32881251c4b95a5cd3b25c928e0679e1e69dbe0a829078725ccc3b624923c946c458d32a6508db884972b4b24cc6770679a7589252f92c2b4b34eb125ac61194540182d3b895a78769dcb4b256a20525f2d2cd3a69353092c49466998356787064a1e6056b8b58927875a5a205ac4f1d834ebd8c612e569712dd25f3885892a275a5a92d10264220659992dd892c625ce24992dda4f24bc93b1e1d696a82c0ce24078725cb4ee5a5a59c373246cd321235a5acd668eb125102e2d34ca5ae5a5b49e25ba5cd8929699892b4b440a60901e1de45e0d3a8a33849341ece2d43eb8b669db8b669da1f569734ece66c60a464b9b4ec19e4934b9cd3b25ca5ce580cc4b9a98a656b1102d3b96960cf69dc34b5a592265a5b4ece67033da76b4b244ca65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part240 : Excludes 0x21000000000000000000000000000000 0x1c49c6104100100000000000000000000 :=
  finishCode 129 0x6a0b56ec3603c37b14c711a425c8326067b1264b9a0897396ae881618c6996169e1d2e6b574b9c02b5ab845589272d51792e51032d5d2e60cf3c39c082160a60d5d6ae6198d16c41532b4cd10267d942aa4553134440af8b219f5e3f286da66e2d624b8b6716ce2d9892a458946c49345c3575abb80b2268379983a60f4b4a8bcc4ac3124cb48c4960ec1b950cce2d3a1bc7ce871265c5ab230c613b983d456a5d0dab125a4f0e15c5aa65711ac751b0440196782b8b573c3b8b642a923c9467518cde49996ae9679e3ec62b8bc25a6716ad5c95a4b75d1893168437267d96ae4a35f19405bc1b9716c4b1342ad5d84f1644a573c7cd0ab5760e83263816af22053c3d14bb21e4edac4942aaf80b58f0276d6310cb2974b5228b9892b553a0a5ae191a99416ac4960128060aa0881418cd1b61bb0ed0f26855abc78796ae713983a4b14b5ad5d102f8360a8220b01e1dec3809726999102a5d330ad5d6c495cd3350a9a2d4ba2439c5a92b714bc7d8c6109471d04ee24b712dc31b716bc7d6ae49d624a20678fa5cd6af3d8a4358903a893f52ec4b924ca59e623c40b62491d5e3e69924e92e493730654baf1f4b5a20523738a5a364b750a92e51032885a5a7413b8986589249d510ce2962292dc972f1f4b9a90902f04994f095a2739442e255929864e9a579624ce2d9892d27189cd23256bc7d6aec62d5d103286d2d2a5d71692ddc5b1d851027412e5204b998be714a20585a08b297a18509f311cd32f1f78fc699 (by decide +kernel)

private theorem part238 : Excludes 0x21000000000000000000000000000000 0x1c49c6104100000000000000000000000 :=
  splitAt 1 80 0x1c49c6104100000000000000000000000 part240 part239 (by decide +kernel)

private theorem part236 : Excludes 0x21000000000000000000000000000000 0x1c49c6104000000000000000000000000 :=
  splitAt 1 92 0x1c49c6104000000000000000000000000 part238 part237 (by decide +kernel)

private theorem part230 : Excludes 0x21000000000000000000000000000000 0x1c49c6100000000000000000000000000 :=
  splitAt 1 98 0x1c49c6100000000000000000000000000 part236 part231 (by decide +kernel)

private theorem part226 : Excludes 0x21000000000000000000000000000000 0x1c49c2100000000000000000000000000 :=
  splitAt 1 110 0x1c49c2100000000000000000000000000 part230 part227 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part244 : Excludes 0x1024000100000000000000000000000 0x1ec9c1d32441934814101024000100000 :=
  finishCode 101 0x7517c490cc5614cada3c8b6278aa1a7547b0a5cc5f289c87a69931395c6237bc7ccfaa639e3e0bb6189a742ef2984cfac499a76a350469a740f730c417667d624ab090278f22a869d58083334a52baa63624825c4fe297427c5851cea1f5a766279a53253411eb6380b03107238ca6973349938f1f531cd29313c86b525990e531a8d4cdef1f69d9d088190e694a9442ee973694c959595b4ed28b105d46a28f530a895892d259496a255319625a432dca3d78f9a4c55f28f494e9e3189636839d253cc27045a534513298d84ec4943eca6305db12548705d4496c4904599be32182ede456120630d3ae034ee05dbc7d0d6a638b4246f62482ecc4f1a4cc86f8190e157a8f6313b1252e6f1f34ca78f802ee253a5ce611b4b451e69905dcc49451e3f309d2420bb3b49e148fea3798920bb6d18c7c1c023f8abe51b99cc44ed3b253ae81459476855531b4b588297398928819097378fc69d624895cb533c7cd3af1f9d878fc973321822e6249a75146249a75a5b022d88321f5a46612c34cb1895992daa6303e82ec72a6358c6b298cc7e973157c97331ac395 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part246 : Excludes 0x1024000000000100000000000000000 0x1ec981d56561924000010004104810001 :=
  finishCode 53 0x701804013078fab090066d4cb11bd88e69d69bb4eda6f3a854f92d6c492588abe326b12471a69969bc69d4a9ba8da390f82f849925bb4ee71098bd0f2699691a9944cb190da76c49420ab09c2f819b691ca65624cc43710b4ecd3ad238a5f348d60054c2af0cdaf8a6588f60bb512c47b710ab0e4289669d82a4d3aa2588f619b624ca654219214d271a65b4571a4157926426711d472a69d34c9936616c93f34e92c5893285c11693f34eb4819b3f13c624b685a990f247505cc643045b0765328575c4263f05d8e3608796550f247571082e586f09c5892475 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part247 : Excludes 0x1024000000000000000000000000000 0x1ec980d12541924100000000000000000 :=
  finishCode 131 0x380807c16ae983a878763198532cf1f34c8abc95a4b1580687060c3169e299548b044de3ea5134e842e329bc7d49aa638cfa1975329264317330b0230ea346da6ee42c8ac12c490b2994d3a9678d3325cd86b2964c9a2af532a5cc1631934d32b6328b2299605282c54cb1a4c55e0b9258cd2d51ebc7d4ca47b94cae419be2589a752a635b946a66f78fac0aa287e157a9941522359e3e7234b99a74d3b3c7d886d1183f143f34dd2e6a6533482ed49a67d5b0176d1b94ca29734ca88634ec973349a99433618f94ca0b91b79a746df3e0783a87876313c258924e34ea90b00c8e69d860c3165958ca6d31237990d49ad3b8c8701f54c62af329c259157862d98521c07518c56096248592aec49532861c17269d42cc8314b582e4c87312432e0b1855e19794c73105892a6515792c5a77310a658d3219b4b9ae836f34eca6169dc65b131a995892e43c89e38069d5516c69dcf1f5328a5c55e87d8932a6520ccd3b04498d42fe1973c3866e3c3a60a4360782e8787620cd3298417619b331e3f31254ca28f94c265b233ca63435a9948cf02ed2a6d3b0cd9266532865ce842cca654b9b4ed4cb3c7d8927877c1d469dc973258a99493264d855e27b94c2693532bc7d3052138242ca653c3862ce27254da76787532c49334cb4ecf0ebe3300ad8d32a6505b9c8e78fb4ed4427799836785249a6085990fa7874b9861c336b625cceeb1934162f1f94ca47b (by decide +kernel)

private theorem part245 : Excludes 0x1024000000000000000000000000000 0x1ec980d12541924000000000000000000 :=
  splitAt 1 68 0x1ec980d12541924000000000000000000 part247 part246 (by decide +kernel)

private theorem part243 : Excludes 0x1024000000000000000000000000000 0x1ec980d12441924000000000000000000 :=
  splitAt 1 92 0x1ec980d12441924000000000000000000 part245 part244 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part250 : Excludes 0x11020004000000000000000000000000 0x1eefdf742440c11111020004000000000 :=
  finishCode 81 0xba358c82b0961a7514525a9858c3c2c5712c4a08a37989244f32dcc49051b126051a98d2b25a13a18c5519c3d10e6a3b9892d3b3b4a89678fb12507a7a3126532b4c4ed2a3b2c1892467987aa2569d94de78fa894cb662f5c0bc4a08ce83596a6c4969d94dd102d3b9e3f2205a7662f313c4678c5ed3b512b12547636f9e3ec496504432885c42b5744088e63138a5d442a51710ad5c80510306f1f5aba58c49947ad2d530996c51e4678ed265b532cac258183510b430a3d4cb21f6711b1254ca881970621ca452378c7da76b574409d894160a19852ec4911f895d44671544f10d7296d47a5a942ccc49313cf1f8cb6419624a8f54c305dd4caaa34ed48b292cb42d359496a4598625a151ea995c4eb62189e312678fad5d4ca86b2c28a5ce8511a5301f5032a6369d996d0fa5030b6624a9956a734ed85ac49526c65b435a99589203994ca297616b0b65a9a9950fac49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part251 : Excludes 0x1020004000000000000000000000000 0x1bcf46502040c10101020004000000000 :=
  finishCode 145 0x641b0541bc3c3a286e19865132fac8a654a18929c3c7c91273b851e46f984654d8846c2378fc8415a6b0f547ab22409c25807d947a271147a784899a7626d34ea4866949c663b4b89cd3ac3d9e3ea3d62488ce58c98bcf0aa3d601644b0d1248990caa6551ea99662491fd74791f834eb4c653298bc55ed3b51da984c5f3c7d4caf1f8a5ea655308abe51bac8a6196a62af2538cdc912f221ce623b89cd3ac4794c292278a65791746b1c4f0a44c464a7699a8f4d3ace21f6516b89d4b627f2d4a96e51e9c762c2b4a473a4a79a66a611c69a56694b00e01a550b321f5a4f2166530a70a65244c64d0bb8abe78f996c912b81c058338b576f10c30885a7615325b8abcd2ad33855eca34ee61a994496ed33440849e39db49da66de220580630d2af1f855e4b7344cc49948a49934ea92e694b1249469e12656434e85b639a9a558925858e8ac1b157cf1f6249a55bc220a9f298455ed333289a5614b8abccbece021e69dbc7da662af624ca3d6f12c380d2ad3b96ae881701a769e1264d3b022d836d2796a6f1f5a9cd330c1aa8e00a8e157ab0ba25069d3d149b34ec146769531b1265abcd3b526c585528acee5a999b65b1e4570546a659a768812519586320b10c96322056aef1f5328a45e3f128d102a655c0e04a16ae65184c668923f92dd1026c12b54c314bd6461534519c2cacc2321199b54ca689530c073611a994b43389441ad31532828c947198a25989204b2d49a24d2aa6567164694cd33512b124d126954512c336996e78f88cc51ee27882ed318b5238d4b08470a3cca264d78f894547a6518082921 (by decide +kernel)

private theorem part249 : Excludes 0x1020004000000000000000000000000 0x1acf46502040c10101020004000000000 :=
  splitAt 1 124 0x1acf46502040c10101020004000000000 part251 part250 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part254 : Excludes 0x41020000100000000000000000000000 0x1bcb4f517050810814441020000100000 :=
  finishCode 57 0xec220ce25cd64624cd331519a24d2ad3381829e1e84a734ead2e421a51630dc20558c988cca2f1f693ad2d584a1a76f1f86f6b4b45082b129de3e51f34eb07451e651139c591620a0c53c344b1066248a4583b358c6338bc03051425398ce620962589330754ca15b9882f1f18dad2d384b1144a051e36b9696c4990ca69d69da78a81a75c4f11454cac49253a50f1f1b5cb4b694cc4978fcc1d532c4516949da5e3ec4934eb10678fad2cd3a865983a69d4513c511544b0b527a21e678fb104af296559ec945429cc27624cb412caa99678fa1dd4cb3124b2a5a1989259d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part256 : Excludes 0x1420000100000000000000000000000 0x1ec9d5756250811854001420000100000 :=
  finishCode 147 0xf23589e36869d6516c631f0060a184a743eca45624b1040a30e75a5a5a9624b0c6330b4dc2d6337431e3f058da3628b60ebe0a82195a5b2994cc2d3740fc62f618a865892d2d94cac419a4a879060b18ae34d6147a494b125a961dcf1f12aa1f54cac272c8a1828b983ac01986696a1e42d6f1f696c69969baa8c6288bc21885960ec8736138e76696a10d893309e40fb4b589225f9432d35295b1250f2c1d69acc470b3a965a5af1f624b3866030588319a50d6a655e183b19a5882c49439acce61399a5892a82d2e611b1242aa9155329a2cf05a58dae0a5b4ed892a6103ecc1d1b5895de3eac250a2378701e8da11bd7c350d26b558b5236b5138466516a19caf236b9696b55882e36b624863544e2896d17c532c69334cb4ee78f8dad6962899485a5b1836b43ec28f41aa996389a1e6349b4ecd272994d32a1990f236b5a5b78d3b4f1647514b691d94ca1952ce8a2e3308df29950ca729947ac1d0a9a0f6624a994cfaea2d560caa1f54cae2782a628b4339a2d3c440e4181433312548a861e0a5b78fc8790b1a1f642a96a678f854d0c78fc337516967583a59d9b478fa88c41985a5a934c98be50bb11d88f3104512c4960ecf1f0a39a2d892da338de2c80c152ccc41522b12494e860dd6620a94ceaa36b94caa65894e68b4a17c5402ef11454ca69943009f289d84e6771b5cb4b624a89e3bcb4a6420b124cc2d3b3219c624a18ac0e344af296d85aa275a5b4ed4962799581b5cf1f69d94ae0a38dae511245719c317c16b50ca94ca9a1995328e3431b29954a68a09e54b310e54b33075e3f34ed4c281f0cc8e344f3307544e38d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part257 : Excludes 0x1020000100000000000000000000000 0x1ecd45506040810814001020000100000 :=
  finishCode 67 0xcc1d03c35612e69e37869d670183289cd2aa619e3eb4b69dca4b0b7bc7da66289946ab4b69999bc2273c7da66c4934aba8a4278a2751e9a55501b0c01f011a5350ce6996248255e3f34cda4f2d2d14690ca2f1f818228f620cc4978fb38d23c7e060a8b66209a663bab4dde3ec6278b4b8d3a395693c67705fb124c6b1d0b0300973671a4eea2c88598d2aa65855e2af94cb1a748de3379696ce3a8b234ee51ba98cd126954514cad3194c6b192c299b4b0b198f1f9a7616f699ad2c8deb4b82ded3b78f91be532ad2d8075012f349d696a6534a8d02af84ae47504bb49d6969e2a8c1d8d3a09731acc3d946af1f4ac994c8de8a2d2cc6b023491269d94c2097 (by decide +kernel)

private theorem part255 : Excludes 0x1020000100000000000000000000000 0x1ec945506040810814001020000100000 :=
  splitAt 1 118 0x1ec945506040810814001020000100000 part257 part256 (by decide +kernel)

private theorem part253 : Excludes 0x1020000100000000000000000000000 0x1ac945506040810814001020000100000 :=
  splitAt 1 126 0x1ac945506040810814001020000100000 part255 part254 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part259 : Excludes 0x1020000004000000000000000000000 0x1ac94c5c6140800400910001020000004 :=
  finishCode 113 0x3f0ec2503c3651b0440b20a8280ea25ccf0eb57516cc2d322a995863191585ada3487879a66e2134c9a1c18298155634bb8a545ac493a1ce294b98e76532a864d2a9738d2ab575abc69594cab574c093325cc2067875ab9a55b4343bc7e69b92656ae4a3710c11378f9d0d2e6782d5da670d5cf0ea659a66973651046b1102c62b80b9060a11e421ad5e418a2078796ae7a2d887940ccc1d322a0c4af2739821a831696b076145b4b427f14bde3eb576018c69051f312545a1993c3ad5c1720c15e094f21ac96e0b14f072b0e7545a98208e613b0c56aec49389c3175aba2062f9876a651459e1d6aeae3e062f43ccc23623bc7d4cac1d233ca17532bc7d847285d2d724ad6ae88160bc2d5cb82589d013b8a5ed1b0ab84ce69180b6423b0ec51e52f3c3cd23389be0541e1ce3b38a5a5a4b178fa59da6eae268a6582268436969215e3e499319ca65532c6335f18c33b9a65693084c226f1f015985ca5e5a1696c10f883af1f69b85acb52f836892b9e3e4b1411cc49495bc7da6f14bde3ed632882220881336c0bf3c3ad5d5c05e8304afb21e4b52c498a5e88348ec02fd6af1a254b721e54cb3104962c1d52dad5cd0e749986e47525882fd102c10cf34b4932973344b124d2a7875aba486953c3a5ce3448a44d131a2623f9a5c962c41985a22705aa4ad6ae881 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part261 : Excludes 0x1020000000104000000000000000000 0x1ac915717144820110404910811021020 :=
  finishCode 41 0x1507c0f0760f0ecc3909e0f0da76ea1a74ac31174d0e8794b9928d4cac1b945e555694b4c468a68b92e60c124cb389736314cb02d418271b8cde317343841e337b0a462e71b5329a1e69d830618582a4276d3b4e0b531a2ce3654369da5cdc8610c22d2069a7424ed3b1e1953e4c0356ca35846f90fa46743082e4182ec11be62482d52e60b58a569738a56a65818267d18ba5cd9c1e1a1e669da98416a0c1751cc2569a00ad94c287951ec31361ea045a62877056b4ec15b02b6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part262 : Excludes 0x1020000000100000000000000000000 0x1ac915517144804010004810001020000 :=
  finishCode 149 0x651043e1102e42d2de4750d3acc299624c8f0d545e12e72944af2a37083c7334b99a1e4218e74e87388545e8551e19e1d2e6cc12b63c386bd2e7210d442f82f07871cec103055a9446c69732a7b3897303fc5855329a550230954d32a65670a6f25cc1720c129bc973334a995987e1c85e17c0d38f0d47b12b4ceed3b05a82b5ac3c2cd3b0978304d3a59d825e7425ce3c3b4ed8931a749467874c0f05f0f0e035902296534ca98425e52305682d425f1dd4b5252b4b9af097308fc10b157b8a4a9e6998b230abd45e12f291a5ccf0f1e1e69da5ccf8261505a5ba8cc2995c84b3cc4934e86ac51731254b734ed2e66953c3869e1e192de5309a7417a3c3541f0751c86d114761487e178517c6895329a747464934c12e712654ca6973c3a8663999264d3a9579a766893c3924e34e9e1d4cad3794ca69d3c398ce25bb4eda6269d3c3a994d2b1e1d9c3c3829634ab126532a5ce224a8bc78669d3c38a5e34282b589246753286add8624c69d4b98f0c1832c0cc2e8bc02b6058a6078378787251c6335309684d2a4a3872b1a652e6d3b92e6d3b98921af3c3cd3b4b9b30bc11466248f0ce8f2045a6228f0609a75892d3b095ca4d3c3b4ecd0e7c390b4b661d87e19c1e1b12634b9e1c946641532cc495299a74d2b255cf0ea5390f24a325b9a74d132884d0e28594ca3633c3b30fc390ec3683c369dc82f59ab10cd0e4a3614cc493a19a75a771e1c356981f8f831257c3c39cd634982a45171a5c436a4b8506f83c878741ecd2d2ce8a2e614a8d400a0a92cec52b291b48c522a2348ae1a152e702a455f25ccc6734b4ac2d251ce99352c5a6cc4339aa98588712c6343c973 (by decide +kernel)

private theorem part260 : Excludes 0x1020000000000000000000000000000 0x1ac904506144800000000000000000000 :=
  splitAt 4821 74 0x1ac915517144800010004810001020000 part262 part261 (by decide +kernel)

private theorem part258 : Excludes 0x1020000000000000000000000000000 0x1ac904506140800000000000000000000 :=
  splitAt 1 86 0x1ac904506140800000000000000000000 part260 part259 (by decide +kernel)

private theorem part252 : Excludes 0x1020000000000000000000000000000 0x1ac904506040800000000000000000000 :=
  splitAt 1 92 0x1ac904506040800000000000000000000 part258 part253 (by decide +kernel)

private theorem part248 : Excludes 0x1020000000000000000000000000000 0x1ac904502040800000000000000000000 :=
  splitAt 1 98 0x1ac904502040800000000000000000000 part252 part249 (by decide +kernel)

private theorem part242 : Excludes 0x1020000000000000000000000000000 0x1ac900502040800000000000000000000 :=
  splitAt 1 110 0x1ac900502040800000000000000000000 part248 part243 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part266 : Excludes 0x81004080000000000000000000000000 0x16cfb933168d0a4481020000000000000 :=
  finishCode 45 0xd63c8e42f869d511982d2c65b34cae083f90aa653432a5ccf0ea3d94ca54f3bac91d2d2a28b5792e68793299d652372084ca6be2c0b23305a578fc36f6249a64f0f25cda6f066d4ca7874b9a1ee337b0d54c25a5532b0a5e3f1e1d7c337c6993ac9694eb32e0b03e0cc1e1d7c69bce25529a07c15a8796199a650ab21e52e6661532c85543ca5cd44610c65b1479a6586702b4cc32964f0eb0310e2d8d329734b128b28f58670e0548b30ad4b646f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part267 : Excludes 0x81004000000000000000000000000000 0x16cdb9190681004000000000000000000 :=
  finishCode 117 0x188720972f2358d21a7564651980d896950f724fd882a61415a99589228f69dca354239d098191669d9e1d2d2873530ca65322b4ed05f287d892a6532299bcca729952d259992d2b81e0cc1e1cb04a991866228a3d286a3569d99be60ca11de3ea53905e43b51abc7da7628f9c5a8615abb4ece8461e3ed3b532ca453918d2cca672394ca6439856c4978fa8d57c65184532c37d4b4b4941665a505da687758f125a51bec9435abb4ed383f051e37d92d2d3b9886b579a767874b3a995004b4c661230ad5e69d998451e88248787522cc29716a995a5b3c7c49ae2d521af8d2d88dea6562282e51478fb0a6141a1ae710948d0fac377c110490f0e66278a65551e448ecd31696a075892f1f34e91bc53ac231263c494bde3e28f148a5a66249a764e1e3e1bd968628f0dec9e2a8f22c0900a74cb734ed0e6f1f9892a45988aa4b52d9a7487731254b69690d89a76712b4ede3e6434b4b4c60d8a5a5e46b14c78fca4514e9a74b4a86198929590de9e8965909ea3d4acbc7d866a3d9e3e9450d8c90278ca1a75003c4bc7e4b5a4fe69da1e6622b4ec51e96b532cc494b496957c651842d2b5092f8eca4612a78a74c9b18d5e3ef1f989296994ca92f497c969624b58a61a75944b4c5a578fcc49435a5a5e3f31250d665b510d4147b0ce1c0a5a54cb0a5e (by decide +kernel)

private theorem part265 : Excludes 0x81004000000000000000000000000000 0x16cdb9110681004000000000000000000 :=
  splitAt 1 103 0x16cdb9110681004000000000000000000 part267 part266 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part269 : Excludes 0x1204000000000000000000000000000 0x1fc9e01b4c11204000000000000000000 :=
  finishCode 55 0xd83b0d612e564660b4ae01e0693334c787616c215110a0cd48ac49561704410eb25cd6ae787297cc47237866dc53020d0ee475237890e297b8a4a62c493c3b11c8ea9738ec286370071b0abcd26b579c5a7874b99a66157ac8d6268da1695c0790d260bb92d6c313b09db585b29640f60bb0cdcc3188de64513c82e4f1ab80a26611a5a4ea20b9058bc80bb3b6c3953c08e365c081718bdc5a94378f82658920b13c3821634cb806698d0a7879ac6914c660b4ab579a7666934c9a764b4b8b4316b57200d3b194c55e723691862d6aecc062da76c499a5ac2d3349a641571144ca672343a96960c5c2af (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part271 : Excludes 0x3004000000000000000000000000000 0x1fcba0f19403004000000000000000000 :=
  finishCode 113 0x2f8ca2c8a63385a5571845803626602e497252f9a76c495328a3e4b4b09d6ab38b584ea6562482e54c6562787654b492e661990e54c6c2b23fb0ae721c0249c49d25cca3b89727c25a5b4532a986497914589247f624ca4b21c9e1e05bb10b03088a02ad4c338b50ee4519892a65342a5ce5329a1547738b41433124926a653b2b90e031048925889f633482ec4fb3c7d89276299417694990a6971228c259429a1dd292a6598921131419a14f0ea3d05dae8a6360969716c0b969d92e4f0e58299669da70ac28863c2a06c876f1f04882354cb3c7e716b6065b842aa613c3a994e920bb32dc4ad5abac0a65760d2738b5a76973460d272195a7738b4d2678769dc52f716a0b5104c1b0500f0ec4990d219b25cad5d60416c4ad25cb08943714c953256a88661164256a8de051924d0f338b56ae9e2c8b578142a6524eb076615a935c5ab5769dcb5751b924e25ba995c0721206113425bac048560dc0a925cb10e1c6b12544b27049d4b4c28f622a4fe78fcc4524e92dd8873124a4619b53292bcd0aa65989219b591c0580926f1f8f0e4b93f186ef1f3c3948e3c4a98d652c49510c6434408fe78796ae19b9892ba2d5c9731e1d2d2e2d9236745418bc7c522787 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part272 : Excludes 0x1004000000000000000000000000000 0x1eeba0110401004000000000000000000 :=
  finishCode 73 0x1f00f0b58b2390c629849d13bc65b3c3bc7d4c6c4934992c4b4aaa12c455f29950563a178fca6569d996da62c49349c2af24c969412729943367872d2ae0d82c0787716c83d5aba5cd05a4b943ecd3b2c16af34ed60532cf1f4a9865d6772d4c95aba2c0ec338c22994972a3d855e65b8d3a74940ec62f34ea994d32f1f32da5a669d996cd3af1f9a76a65905ad81e0b01e1d885112e652f9a7669334cb0ce624c2af532a99643eb124912f1f69dac0a61f8ba2e04b9059c699497b12491219b244c969624a54e34c8abd2e6c4978fca65048866c55e52b851691b60cbc7ccfac491579d066f94ca8615abb4ed89312256ae9e2c0081041b11669da19505f19bd4ca7c19be4b4b1254cab0065e337b12455e69969dcc494b499bdac25cac8a216953c349b0b622ba9952e264d9242a6541fb125a47311d0ea67d5329a4e03eca65 (by decide +kernel)

private theorem part270 : Excludes 0x1004000000000000000000000000000 0x1ecba0110401004000000000000000000 :=
  splitAt 1 121 0x1ecba0110401004000000000000000000 part272 part271 (by decide +kernel)

private theorem part268 : Excludes 0x1004000000000000000000000000000 0x1ec9a0110401004000000000000000000 :=
  splitAt 1 117 0x1ec9a0110401004000000000000000000 part270 part269 (by decide +kernel)

private theorem part264 : Excludes 0x1004000000000000000000000000000 0x16c9a0110401004000000000000000000 :=
  splitAt 1 127 0x16c9a0110401004000000000000000000 part268 part265 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part275 : Excludes 0x81000804000000000000000000000000 0x12ef6e3114aa4502a1100804000000000 :=
  finishCode 103 0x1706514c7c1102ce278b573449a5c50b0a752d3220c49987ad3b52c9e1d44051c7291c0a1e6394a887e3c7e29bb4ec14687343ea9864ac8a5de3e8612378a5e69dbe0a816078750dcc1952ea8b56a635769dad5ccc3908b66c210611a89654b328c4842f1f0c1860e713a99589229d4a2a1054b70a74cc471cc237a07649eb12470320ad0c273b903ab5778fc879615b12548a9e16896d90d6a2d52ca386611be522a5954c3291669d95064a28a3d0d6951441407c16aed3b8f0ea618a16969227b12585218369dbe022d8d2ed3b60c9974f0ec23066532a0f5892297624cc4569d8a3d686118672c752d2d351479a5ccb70a3d2d265b853ace3e0a6220c227868934ba5a6429a95d45e27f52db08643ebc7d405814b734ede3ea1b523b4ee78fb4ee297a1f58926979e3ee01e89e1b0a4552d8a767138e04cf2c4590d719e588a5419892f1f435a96d88b1115443a0fc14bcc49532a1cd0faca25892256588b2594702a4b88dec45521c29769da9148de861851eba0cbe04b915d48af1f147a1ae2378a5d86725a54caf1f14ba48960e04e53256587b09154b67294a2ca3d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part276 : Excludes 0x1000804000000000000000000000000 0x1aef661004a0450021100804000000000 :=
  finishCode 123 0x731280f0a98ca2a08813e189312254ca9e2196049922548f0abde3ec49624c2af540f8157c9574b4b1248fea6552ec65b157a50d89296923fb08b57855ec4993c0b0cc492b091fda40aecd314399c8474287d94c27291a4ae8d4320e01883a1157a99640ca0f549664194cad3b621a1f546321950c32ced0ca82f624a994f0f2d5d89278798922af5c1944a150440b209e1e1d0069dc2855329225a7719e548a54d8ec246f532996d145aba976532996c9123998cb6582d4e33ca96ce76d3b326ad5d3c398ca59142993548a7619e3e87d1cca20d82a87875d12c5ab8e654331a548df09ce516a9164b4b10cca25598f026793a09a556ae8a0a3e3988e64cbe4459a76a651cc89b550440d85ab9e1ca5f250d4ca05132eb0d632da9943069e2508a310e10da4fcd2e08b62291fd584b5c093621996e10d9cf4f02ce34ed4cb1d04f1a09f94cab3196929693f1a7665d5ab8d0e6998c3445a06d621ca8308d22e8aa2783996708fea5d8ca228f4b4862610d9564692b3196929695a14c671a77291ccbe47f4b4a5846f987628f23fc46f6949cc54cb0464e6228f244bc7e69d91fd2813fc78d53292255c32f8a1652e9e35c4f11fe23fc08d244a18c22d0a61f0ce291e3289a256a7291d832a4369881d4732651522c54f237a91d4ba399948ad3b9a772044e76a47699cd3b10a99ac8dea47 (by decide +kernel)

private theorem part274 : Excludes 0x1000804000000000000000000000000 0x12ef661004a0450021100804000000000 :=
  splitAt 1 127 0x12ef661004a0450021100804000000000 part276 part275 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part278 : Excludes 0x1000800100000000000000000000000 0x12e965504480070030005000800100000 :=
  finishCode 139 0xec3f0b00f0d9c4b9b984b955012f2d2d4ca29d0f0ca5b94ca489751cc50cc0970f091be61592252db2d34126e2d78f845d696445751cc6703c2f8298f1f9a76a6534b994e522a185857194ca16b4b522a99465ed3b329ce2d322cb4b0b7b4ede3e9695328c807d883ab4b0b78cbde3e431237c645197bc7c88a8a12e52e66e398a4114ecd3b0f0a975e3ec49230c475889f312542a1e1750fc0f0a30b021de52eb1154ca67d34599866f611ce2d004a1f491283569da0bde3ea6543ecc62a8f1f8912a656248e8508e87d5d0f03504fad3192d250214e41a80dd48ea65624ce27948e969622a9954bb3c7d8926625a6047b1254ca18192d2a22c8ca1f03a104bc699532b4ee42998cc912b00616592a995c5ad3b1459a4c30b2c95c5a7a2905614a105f34ec11e69369dcf1f145b8ad64b29956ab299528417c4896198a2e69da994fc590946f18926e2d076d498a565e3f307489e68b9a769e248a2792a2d290419e34a45a5ce27620b4ed2a2d3b9696289613cd3b4a890f612981f42f2d3b345b78ce238921d7613f9e3523b1d74c37007d45eb3548ea4c51c345acd669ca5b52631a6643c8a2c0fea21989597e00fb1a2c8deb1d92a2253144c66f345a7828b923ab1d3a6a976713913d607c0f43c10aa6628be33ba96d0eea01a662278245c5af1f040ad2e13cb8b408338b412e36b78fa48da1b828b69cc86552ead2da76931041c8650c29e0432b29860268c8ca5e86560ea88c239262e2b4b694ac516699145ca01b8f1f889e9234ee78f820d4b738ae297800da76555417b474512e2d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part280 : Excludes 0x1000800004000000000000000000000 0x12e96c1c4580040420010101000800004 :=
  finishCode 65 0x1d87e1601e1a204b93812d70784f0ec494b9ad5d507c03c31a2cf0e69992e6f1f9c4b25ad0d61e13459985d45d03c29698f1a28f322c8354a0ca72d34f0e88178fcb57495a204b95abc7874a1c03e14cb220527e96b65154440bc7e1429226142c29d42ac27f43c87852573a8a80785a44414cb1a2cf02b573429e1d84650f031a6416a92f9e3e68b9102c33138ca2b43eb064f0e4893811032d5d3c142c781620c0733199d852d2d2220783e0701e1dc5b053d6aee627875d92ca0b543cb1264b2a45cec3245cf02b002d588f1d74f0244f145a2065aba866616a15589271334cbc7c16a96d923652b623b0dd102f1f05ab0b648db0dc162881 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part281 : Excludes 0x1000800000000000000000000000000 0x12e924104584040020000000000000000 :=
  finishCode 105 0x2985ab651604a1d8440ae8cc12e4e81e1878638d953dc5a0ad3c3a5ccab30785c5ab4b8f0e973661c5a740f0c3c3153cf0e9735a5c6870f08d2e532ad2da767874b9aa01e183567873e17c5a5b48e619dc6a734ec3c291786a6d3b1b5c64d69db125c5a0ad0f0c6779a76e2d0568785d86a12e6e407863c386bcf0f38b49725370f0944e0f0847da767875414cb0c2dc5a52b0d39e1dcc4703c2d39989291769db8b52a2855816ae25902278d69da8b5c5a0ad0f0c3c33c3b8b5102ce2e8923b0d412e569738b478666d90b21dd7169a5d2d2f81f07877216961e1988a6994a99a16532878415307843561ab83c21e18f8761c5ab4b14ec2a34b9a996721c5ad3b8786693986aa80784227098586a5230d59a654ca973998761f86a1601e1b68d22889419de0f0a5ccd2629790fa5370f0a5cc3c31936619a8bc9721e10f0c787988672952582d43c2b01a663c387849721e18cde78769dcb4b3c392e5f8581a45115033b948e0d39e1d0fb11bc50a0b56f1240f0b4e659a955588f34ed4c2c2d94ca561730a5729941627870d5b1250d71e1e48dc1ab5803c2787498ca61420b4ed2e6b4b9262a4b (by decide +kernel)

private theorem part279 : Excludes 0x1000800000000000000000000000000 0x12e924104580040020000000000000000 :=
  splitAt 1 86 0x12e924104580040020000000000000000 part281 part280 (by decide +kernel)

private theorem part277 : Excludes 0x1000800000000000000000000000000 0x12e924104480040020000000000000000 :=
  splitAt 1 92 0x12e924104480040020000000000000000 part279 part278 (by decide +kernel)

private theorem part273 : Excludes 0x1000000000000000000000000000000 0x124924100000000000000000000000000 :=
  splitAt 4458 98 0x12e924100480040020000000000000000 part277 part274 (by decide +kernel)

private theorem part263 : Excludes 0x1000000000000000000000000000000 0x124920100000000000000000000000000 :=
  splitAt 1 110 0x124920100000000000000000000000000 part273 part264 (by decide +kernel)

private theorem part241 : Excludes 0x1000000000000000000000000000000 0x124900100000000000000000000000000 :=
  splitAt 1 113 0x124900100000000000000000000000000 part263 part242 (by decide +kernel)

private theorem part225 : Excludes 0x1000000000000000000000000000000 0x104900100000000000000000000000000 :=
  splitAt 1 125 0x104900100000000000000000000000000 part241 part226 (by decide +kernel)

private theorem part203 : Excludes 0x1000000000000000000000000000000 0x104100100000000000000000000000000 :=
  splitAt 1 119 0x104100100000000000000000000000000 part225 part204 (by decide +kernel)

private theorem part187 : Excludes 0x1000000000000000000000000000000 0x104000100000000000000000000000000 :=
  splitAt 1 116 0x104000100000000000000000000000000 part203 part188 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part286 : Excludes 0x10034000000000000000000000000000 0x18f749b51510f74000000000000000000 :=
  finishCode 53 0x1885a1505615c0c7866d6af31252e60991539609638a52e6b57498c6274b2b0c423718fca270d4d2e6881609735d0a7635f5ab82ee226a8850da585943aa65490a8f29952c528c84d14d82ee25052b0a9d4cac49570b0b2954536a658fc4b99289031257469db08e69882b543a43f34e95e628f920d6870c1d5c6d16c6519c420b0a59531ecd2522d920da77387c27e785815a1898ae25954a6ca63697a92e5268e75a56d3b34ecb550b6b88588eae02e5a5b16554aae219a76b55696a5ce5d0306a25854e69d241ca51 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part288 : Excludes 0x10024100000000000000000000000000 0x12f750a45c11934124100000000000000 :=
  finishCode 57 0x4e1b03a1744b9a8869d7e1dc33bca43696a99454e699696ca6513791e4c4706854b2257532a8b45360ad33eca656a1487119d0fa091532b0b604cb12548618f6d1dc7e18930a854ca69334cae89e2a89024869d14dc53b14ba995e3f14ed643bacc4953282858532994216d2f29dca49134b124853299545229b70eca3f14ba994ec4808f226f55031ec4994a2c49815f299589293d831ec4923cb4b54ca4799585d14434e863e78fa994d32f1f94ca18f8d32a6534cca6577144510c69d6918e749066996d19033ea1b669b82bcd3ad3b78fcd3b9e3e21f696b1254ca76120e624b46da4626f241ca25624bc7da36a65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part290 : Excludes 0x10024000000000010000000000000000 0x10f710b55418925000100000410048010 :=
  finishCode 155 0x72174560e834eb60882d8b574b9bf00ad8cfa69969b988e4ac82944f702ed442a4d5116c771506305431984d322a7460c4f28ccd326939a76be3287a02b5c5328ecc32c4923399dc906677906b19dd892d3b69dca55056c0bb9a76a4d153a70d3b624ca650c9951da6f1604378afa045233a895a7635b0cbad5d68526ca2969b842d4ca1975b086b217c422d37532b124d32a219a6ea65526bf0ee2e067d34c9da605b89a44af043d4cad3569bcc4924182b54a31e24216a655ab9d0b425cd8c541bc460542653942e0b3083ac8ca8ed23313ca175329f82278d26c4952689f56c43154349b8863ba8415442935430b88631e867669698f5a47151cb85a1c13f510c0b308d9c8cc4f3885076a51330b124e46669943a32b69ba88c63f0a499892d371509a656af14ec536a51820f34b482e77933ea994f43209c56146ea4d4e1a76973832672396aec4990fa9737310c610c44f12e31614ac2b82f8a209ed4ab29450d6e1f9892a5143ec745624b4ed03248392e663d30da9456af34dd42ec492c2a94452e66f94cac49938391ca17521a9960bca945b0541687e118771a77120d4ca6450c9cb574b9b4dc9070a5d47619b532b4ecc372d5d2e6d3792e646588a64832bcb4ed2e6a19948aa3b30d865d506a17c6d14caee2b0693521c521512b4ed2e627b313c521512919c496297944b34ed6ae0936c110306c09101fa0f445ab574b9ad0a22e087d313cc4969da8fc8ce2278066d3b8c7ae2140ca85d44b34edc42619948a24b322a0f669d9984cfa8194e1444b9b18a259056c23233a1f48cf044da76a1d33b84fe31eb4ed44b34ed032b575b1306d032e7e34de4b9b124cfaa2310e049920cb5269905bc46714b824e69bca6534ca8de (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part291 : Excludes 0x10024000000000000000000000000000 0x10f710b41410924010000000000000000 :=
  finishCode 129 0x18078f20040441e3e741609736f16aefe2e8a658eea2a741da1b4c4313ca65427b0b54cb2f8a658d32a5588ae78571094de095848d747f14cb0a9d07686d70fcc4905da9966a16ae27b854e87f05da994d3321fddc5f150532c67d34cb506402ee1918ccda56a42a8a3594c28195a98a5da5b043d46a51f5a98e162cea0f4246c498cee0b308b848dc8360ac3d14aaaa2906a09cd6472064cc2e210aab11e591b87d032e2111ece1f313cd2d70fb11e710a5c5a5a62761acd2d710848e710998509f0ccdc42c29330a065484e0e472d4c336723815b0c8c25e147532a20b81d0b577712e6be14de05d9a6530618c86d427b8854aa2318822e2b710b4b50e2ba33887f967a0bb715c871623cee188e05d89ed4ca699624c12f5f0cc4b99a6486721c54ca86d90db10f4cc29735417c5d0d32c63126153851e69b8285892a659892e43884cc263d854ea5529bcd431242870e7425e67769584be6a12e6662e0a65650d270285a5627b696cc49134b12605d9a657034cc26913d9a66624c6995c1f8771445f014b216c336a653499a651851acb43591866c54266104eca59391866d6aec3592e2c4350ba994cc2c82e8ae34b6532829415ad2d94cac4905d866e50bb0f623cad5c3372d5d447e0c7b0a84cc26995504af29644daa650d0a8b412e457945a29b50bca65 (by decide +kernel)

private theorem part289 : Excludes 0x10024000000000000000000000000000 0x10f710b41410924000000000000000000 :=
  splitAt 1 64 0x10f710b41410924000000000000000000 part291 part290 (by decide +kernel)

private theorem part287 : Excludes 0x10024000000000000000000000000000 0x10f710a41410924000000000000000000 :=
  splitAt 1 104 0x10f710a41410924000000000000000000 part289 part288 (by decide +kernel)

private theorem part285 : Excludes 0x10024000000000000000000000000000 0x10f700a41410924000000000000000000 :=
  splitAt 1 112 0x10f700a41410924000000000000000000 part287 part286 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part294 : Excludes 0x10020104000000000000000000000000 0x12f5dc661d41815130124104000000000 :=
  finishCode 5 0x641102fc28864b7b4ec96ac2394b6a63624860c54f2945892497 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part296 : Excludes 0x10030004000000000000000000000000 0x14f5cc750541f01150030004000000000 :=
  finishCode 31 0x1c0583e8b575514cb308c14269d24a92a55c0c1cd3b1ab8a85a7734c62d0b4ec542a6534ea205f441180440a51e5328a9c952a65893e16b0bfb00183896a69d82fe881974630d3a9c2302a161fcc4928fad0da76183051ca65250b4ed87f188496aa4b153acae69db12587e739050af8c498c7a58524f92a53069dcb53250ad0e61f906549ad3b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part298 : Excludes 0x10020005000000000000000000000000 0x1cf5dc752450881151022005500000000 :=
  finishCode 63 0x6b174650d3a5e208962d5d102c31810249f532c29752db38221710ad5dc3f296cb3a31f14ba96e624989d0ff29942c6d2b440ad5d893189c442e215abba886360a2260c2d94ca2972c2a1f57c6d1dc5b0cb6395844249f2c2a496423927e24fcc3f4239616017a11d7c5412c532927e012a8b5a6ab4d2c2b0b52c3252452ea431cecc495abb11d293043588eb628b56ae153861ec492c2acae187b12510334ec05e03324facc66238a5d704b16ae8815d1b0525c5a969da9856570c3c63ed3b616c59198928c280ce389c93ea659c565a931ecba25892292d4c23618a2a5a9618a1fcb5325459c2d4c591624c84918dad4da76c2d8a2ac4914bc12f530852c66e317 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part301 : Excludes 0x10020004000100008000000000000000 0x10fd9c7c36708019140a4c0521012200c :=
  finishCode 63 0x6413c721045612834ead888129bcd3b14b92d4d850cb4d487338ac6b205d48fca614e1f850c96a669d92d588714dcc4e72969a8a9e5308164c4e53748f9285a76923884472881532c2972d4c4b394322217109a75947d052f128496aae2204b5324e5442e21233a9862ceca6514bbf0b63e8ca12ce710a20496afe24865b8b2a837630cb7308c6224672d0996e30bcc3f119b874cb634969aa4862d0996c6c2881150c65b6310532994536d359944a1044b11022a7986271b530b0960819c6c892b62882218342a21710925d6772994a92a212248e554cb3885442b6099e2cea98492e467947a962d85a19c3ac21110a98473ac3d824e31f51e805639da995842467 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part302 : Excludes 0x10020004000100000000000000000000 0x10fd9c74147080111c024805010120004 :=
  finishCode 151 0x98128d63125fc550a4526ab0a514f09428498b2269d153c23d424989d1033885047e1102fa20f624692d524310646c2e215328a2634eb4ec0faa4390fea65259ab085b8d3a8819c42be3285478c4e22122ba9954b6e2144092d53c692c37534eac66692b4c54ca2a113cc69d250a205440afb4ec96a88120bc93d2beb0c52b2a659945c1044a190440a78fc2e8a21a75d432dc71b528828d0d64a18e36e21526ca25513b8856c7d0e4b128496a385946f1a765b17c271f455096a83b909aa63426cd29618b0fe51ba1f614db884b4334ec5364a130bc87d51b8a9e408a8dcacae217e16c64052f34ec9424b547092f2985d408dcb231ce919cb8614cc23698b87523b288aa28f634ea1cd0faae0a86153a0d6513acd6532b0c42baaa34ecc4f30f4d3a53b14bb496516846cd3afc2d8ac3a84b52b2cc471cea995440d0cc31698925d88f0886435b08463ea65259b8845431a754ca5899a7669d532bf0a412d54451e8a862c4989e531b0f40f2d3b532a996490cc512c69d0adb4ed4cac218b1253769d989e2c4b4ed8c5719c532c8732a0b4a4b2a37d751c43289d8425710c4c2978b22d2551bcbe24866390a651e0a8f1cada76940a8468b30b4cb6467841ec25423a91496ab2b5d144423cc3914192d4146fe12d638da1b5496a612ce92d6530b88644092d5f45617425aa582a1525ca4d32d89f4e36a27423cd3b88cea37522ca37259b885102a4d8cb6e21440b184b59432835150a8de4a174440b1869d710cc31424b0fc542c3f9656b439836c47423951dc42a375d1a76b2b854e8479656467 (by decide +kernel)

private theorem part300 : Excludes 0x10020004000100000000000000000000 0x10fd9c741470801114024805010120004 :=
  splitAt 1 63 0x10fd9c741470801114024805010120004 part302 part301 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part303 : Excludes 0x10020004000000000000000000000000 0x10f59c741440901110020004000000000 :=
  finishCode 49 0x2e078f201905aba78be1a7544254a1859194ca71b78fa1f508f18f54ca71b78fa934b3b28f54ca87d98c78fbf0a2292e24a92858922a1551a5f12a544a7358212e2169292d4c7b20a544a29b512c643c7d0861fc39d2ca98f502ea65233aced49ac496958f083588cec49095a945544314c6c498afa87d42ccc49107c40f696b12506a2a75104fb0a24afaa3b8c7aa65721ac5607834e990d3b30bca4b24a9ced89293b4a792d6440a98549720d496a2a7551102d2b854ec2361ea9354cb01c48cea45440ca658952ca12a625ab08e5329255e3ed3b (by decide +kernel)

private theorem part299 : Excludes 0x10020004000000000000000000000000 0x10f59c741440801110020004000000000 :=
  splitAt 1 80 0x10f59c741440801110020004000000000 part303 part300 (by decide +kernel)

private theorem part297 : Excludes 0x10020004000000000000000000000000 0x10f59c740440801110020004000000000 :=
  splitAt 1 96 0x10f59c740440801110020004000000000 part299 part298 (by decide +kernel)

private theorem part295 : Excludes 0x10020004000000000000000000000000 0x10f58c740440801110020004000000000 :=
  splitAt 1 112 0x10f58c740440801110020004000000000 part297 part296 (by decide +kernel)

private theorem part293 : Excludes 0x10020004000000000000000000000000 0x10f58c640440801110020004000000000 :=
  splitAt 1 104 0x10f58c640440801110020004000000000 part295 part294 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part305 : Excludes 0x50020000000000000000000000000000 0x1af706255400800000000000000000000 :=
  finishCode 135 0x340b82b0e416ad684a036e7c2f8ca299574436cb4b34e82d452f34ec6f68815a5829634ead2d0ff1a7569688169d8deda772e8a6569d965634e82d547f30a53c51bc881610a94418269d69dcb4b060a8758c6516c06096a614ba96e624a5cd102b6278e1f8886a636249614b3a5a19893288594528916e2bca2050ff188da6aa2121495e5740dba20b033897329dcb5744082d4ed31de546e8815abcca20853b9a5e881624ca3753282fd505712932d554bec4914db88629db4b662496554aae2169784ec17f220500501a83c7a708425cdc86106f65378c7a29b624830412f3124c7a45b532a8b65a5988d87aa65060ad2e50cb0f59c78f916e436989d6960c15b031b00a4c46b19436a1c4c4f30fca6eb4b4b9c601e8b4b4b9989e6128a14d3aa5134ec0c1521a7636396965374a2c23f62496a54cab4b4912e6d6299528512c69d5a5b0946f62338c2e69d61c8305a76e2b9a76b4b14d8a6e1bdb4eddc65158440a4088312612aa88452ea6569d8ded2e66414de5328d4da76b4b5d10db2895a7629b34ea7858592e2a171ce944e78fb4ecc7ab4b9432c3d1bda5cd2e7278741a7544624a5cd242d4c46310da995876a510c2b0fe512c9230ee52aa9954ab2884639876b4b51f8a6d58528cc4943fb4ec31eb4b4b9cc3b510a409e2d869d61ecb4b52195e54ca297531cc4951b990aa288a214b9cc494a8a5652e729358473094536b4b29bcc3d532863da769733e0c83a01332994216d2f1bda5cccc5714cab558536c23984702b5c3f28b415a37b4b9918e61fb12415a973 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part307 : Excludes 0x10060000000000000000000000000000 0x14f994745407800000000000000000000 :=
  finishCode 143 0x2e09416ad9441190440be8b625ce2ce83056964a125abb0039809a20f22184bd4c2b4b526a5cdac330182523825e52b5329d26334a94d0fb04bca56b4b05cc0c15a5a5ce641b463168060bb04b522ec66958e9d254c6a5b969a74961acd37624ad2c8cb0a5d092a21232ca2105c919e61ea5cc00ab4b691829d442c493e17c5a5ad861794ca0a733b9a654cb0d8d23ec4951095f6430a47d8925a14b9ad8be288d35944ad2305399dcd32d3794c20a56310fb167509308252e6d37671442d238c2e589423910e641946d16c060961614b928496a603b04a25cd0e731244ab14dd23e04d43984be09da11e43eb12523e6012850c4b9988c4984aac35439a1f6233b12629bc91f532ad89e3a887f8cfa85f2c296752e7310cd16847987212f291a5cc8ce0a909dc3134b9b1250c4b9925e43e919c92f312560501843c7b68b6378fa328be0305e3f12d4c4f34b4942982f829778fca6540cc94f78fa9964b9a56e4b99a1547ad239696f1f493a5cc52e93b92e6a3d250ca3d5a0a05f124e6858902a6538dc4a129bbc7d2e6d23895297378f9c6e4b9a995e3e942f8ca288d62d88612ad24342b48e291a5cd4cab4190d6b4b69bb4de5328c64182a21531a98e060a986255ad2ca47055da6eb4b532ad2e060c87d250ad2db45f194530c4b5060940513923ea65760cfa91f92e652384670c7d2e691f51ecc49250af8fa140481254a11e05ea994e078fa896329b0f4e36b4b4ada896411a1f5b4512cf1f53282f54c33c7d276c4951ead890128547719850fad2d82fa94f31ebc7d24f2d2d892963 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part309 : Excludes 0x10420000000000000000000000000000 0x16f155344610800000000000000000000 :=
  finishCode 157 0xa02e0c016ad20770f1e822d0881571bc6b14ca2a1233cd253c4a0f602fb49420e5475ab9e00039876d2d3c4ad5d4be27d2a39e265ab83063c2ad5ca8ed2d8182b573c2a68693817ab5753299f54cb2d5ca8ece2d5cecb2994182b1998922a7532900ee160a22d5d28540b834cb4ae78f851da46c3d88aef1f09dcd2b78fb0f6532851cd16f1f50bcd2b78f99f58731254d0a699440bc7c31b299488ad2f52fa915a6e4b378fad5ddc4a184440b18d2f8cb667725482f5102549c7630ba8654b6713905730f5892713697a995a5b0055c52c3d697a0ad4ca0bd389cd2f05aa914952ee2d5d7c440925669799dcd326619a5aa5f68dca5f624b0e42d6a65601ac3c7b78ac28869d5f05131a14956b4b9a762a12a3cd3b5a58304c7ab4318547125ca593498a841171c4da5a579259b186603063aa9dd4f0b1a2c182d378a8f1a755869dc4b5499a5bc54f151d0034e920be0cdddc0b1cd1b2959a64a5729942c7346c2d6ee230be299634c858e68d94ad0c516c693000c39d2d4892d8925a9889aa655f1a36c499872685085c13f6b13c770d3aca308881600cd33125c4254705eaa086296e68d8a154ca68542cca652ce915d273387cb3aa5b3bac52b710a1ad4cab62687e1a65a3731244fa6612a3cd1b52ab38547342b12661ca9248af346d5c22ba8766918a84c2f348d84670cc060a18a652c2cd2d516b11e2ce95565aa96a568541a37113454ea652d0cc521ad36696b87e389ac64a4218d8ae2c49085c221610919d4873125945f16c611dc06092365a5b4ed1022a733bb98b358ed23618a8f20d58927453ba92ad69734ed892873060a0d63309d550560c1150c942b0b6378b4b9102a6169d923496a18d94ca6995a586ad88f34ed102a61440c1ab896ad3b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part310 : Excludes 0x10020000000000000000000000000000 0x14f544244400800000000000000000000 :=
  finishCode 85 0x3403c35c1c02d5a40741e3d044b9a5045d9a36547710a205442a39ce63bc90749022a13a4c48b696b1250fb09f5892822687e04ce240ad5ccfad1b89166995ab9de523b0a84a8e39d440ad5c91651d94a2571624b085b03f12e6a831256c330c68b150cf1f50b8e76714b0f4916ca250b6220565319a4d32c3b9c4248b927284f41ba874c7ac3d94aaf1f96aeca360b5744082ce2a3a5cc167115c6ae16b92e6b573a0e04b9a40ac1e3ca5f1cada76b4288547045c2a1696c4816249a4e6969e15892b62f89a189e436944c54ef1f34c99f5444b1e3e685289c84f438922d87b18f5a372095e3e83d624a1b6696bc7c54e661691cf1f313c48b04aa13c542b4b3c7a40da200ba1e3d89321acd26a352459a7544624c859345b1263f05433084d0ac4924599f4f1334dd69648b395c48b3c79f8a2d891668b342b1249172d2c72aa3d5c11044089a64b9b126153b4dcd3ab4b4812e66434eca8f348d69663d9a5a66f34ca09634cad2da46f1f (by decide +kernel)

private theorem part308 : Excludes 0x10020000000000000000000000000000 0x14f144244400800000000000000000000 :=
  splitAt 1 118 0x14f144244400800000000000000000000 part310 part309 (by decide +kernel)

private theorem part306 : Excludes 0x10020000000000000000000000000000 0x14f104244400800000000000000000000 :=
  splitAt 1 114 0x14f104244400800000000000000000000 part308 part307 (by decide +kernel)

private theorem part304 : Excludes 0x10020000000000000000000000000000 0x10f104244400800000000000000000000 :=
  splitAt 1 126 0x10f104244400800000000000000000000 part306 part305 (by decide +kernel)

private theorem part292 : Excludes 0x10020000000000000000000000000000 0x10f104240400800000000000000000000 :=
  splitAt 1 98 0x10f104240400800000000000000000000 part304 part293 (by decide +kernel)

private theorem part284 : Excludes 0x10020000000000000000000000000000 0x10f100240400800000000000000000000 :=
  splitAt 1 110 0x10f100240400800000000000000000000 part292 part285 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part314 : Excludes 0x18004800000000000000000000000000 0x1277e015b0d8604920000000000000000 :=
  finishCode 147 0x1c050100300f1e9c2e097359174513c0a95ab82b58933c7dc5a68d346ce2d593bc7d8932995856f1f5c1645d1245ab82b514427c45752fa1c5c5a38152fc871529ce2d78fad5e714a995e3e537624b8b490738a54a6c43716ad5de3e20f9c5ac490a7bc7d702c1785abae8be28f605482b413b026612b89a5c5a959947a09b624ae8b22f026994c20a9056b12604da48675985261542da995c5b38b66f17c6914cafe2455c5730b5497004dc5a96d1adcc492a4cb2b616b8a48b6251716ad062a4999d4cab8160ba2d5d7c650a8f1a6dc5a97305682d550134ce2d5328a5415219760dc297624b4edc53027432e9734b9ce2d624a70c29821697371682d41522950cbae8d37816a275922a951532b8b4c0241ce2d14ab0ad2e6de25862992daa65128b4edc5a2954c1f8532ce2d241b12614b986e611a994e4635b333ca65044ac8981f8d83125787e188301744b9a8ce30aa92416ae2d14a82a54bf151cc4ea65435b8b5a6f21f5a760a394ca07924190d669db0f5c5aa6514a9c8e68da5cda760a9978671b41c0c0b514bb4de715a87d47ae2d4b682d52e734edc5aa3f9466a6569db60962046412a9850fea2714ab107401a66119db5092d37391b4ed2e60a99a77028d4caa659c5ab4305482b4c06c1385d12e6d208fe71682d452a849908f38b59c551f8714c4834308a5d0d620f9c5a0b505acd3b89069233884969dce2d05a985669dce2d3f1a76aa2e8847716c23124198a482e295714ca4b84f3299452ac42f0ac2a0ba061c3369739892b57056b1265abb8b52e71856716a92452a97314ac0990bdb4ed6ae97314ac483 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part316 : Excludes 0x18004000200000000000000000000000 0x1a77e18f301a81400c260010000800000 :=
  finishCode 103 0x1647717c480b4abc1907429452e734ed1c4f1252e2d946e61533fb124f1a67f8a8f28dcc2a86b6249dc4cff1db505692951db4ed4069da9562a38d7cf1ec4991c139ca65422b8b5252771920701a0510f1eb424887d716c65969d8a5c9067414e1a6b38b5c524830c9b12669db8b5104b9ce2d622cd3500db884cb331252c2a634b9b4ec12f25cda76e2d6a124510d226599856d3b619a98ce826598c00cdcc494b9866e21e920da7616b96aee2d4b9a48c6350627890606113f999cd066e25864b889cd343a0c971623992e3a0b1264b989cccb27413216af3c7d8928827006f924261b5abb11dc5a973524c483716a0ae490a0840cea3f5e0c82518c624a00e019fd20408c29743e9e3cd233c7d2e7066d49ae2d5aba8082b946e8575a1b4ed6aeb439a6e92294632c95254c6a655ab8a5d4c724c5a6a483631a4b2994d2269b498cd3514ba5653869bc19b08db4edc5a97368dcd375abb8b5a7738b52e6c49532b10bc270b8280841806914712e6a2590d6e2d52f9a35e3f38b54be93142ccd2f69bad5dc5ae2d92e68599c5334dde3e859241999dc5a9038b5a3720ad44af1f43eb10e68d94dde3e82d8c1a66369bad5c906e2d4b9b4ee526a09490678f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part318 : Excludes 0x18004000004000000000000000000000 0x1277e2a57618054004007018004000004 :=
  finishCode 75 0x360882489736a1a0532b28ce2800bb14bcc495ab9e3d4bf311452ec49590497387cf1e91d419b8b47025a541dce1f5aba1b5c433115466b576f10bf0a54d371665892e037878f3919442fb0f62d2951e69b8a5660cb11470331148ba5a5059c547590edb06b5892a378c2ad2d52f82edc5aca338c62f853b8f1ea6505986d4b4ae03f0902d078f7f10c221d841285f23398f4cce5479a462978656c49415b4dd2469bc22978f89cca6a871624a0ac52ec499e3e78f8d2331248272475452c3314bb124b4b280fc1a0ce30cd00514cf1f419a954f1e46790c2a2908bcd3778fa99506680299652aa085e3ea659c42c49410ac8da6e78f99c71094de624b4b5466a49391c615622a9957c491a05329f878f716ce1f528b1248af311416e68169678fb8b54c6e2d98925a578fb8b66249e3e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part320 : Excludes 0x18004000000080000000000000000000 0x1277e0c7323c004a00001080c06001000 :=
  finishCode 81 0x1dc5f1346f0b4ad23188206d54c302e46b27314a2ae0c424f605ca4f629aa98629aa4f5fc400ec2389519cc33530a18e30db48d4bea1f532ca5f3c78e058c55108f311cce20af34da98678fc973622a89c906bc21f6690b125a763814b982ec15ed1b8f1e9735b18c671700daa1f669d8a54d3693d9c5b30ed6ae87f30aa994a6ad1d4a2a4f588b08c5c5ac4969da944f1e9654a29e3e512b12452ad3b7f1201e12469daf0c63609c1964d0645b9a3653b624a5cd0ff01d5042e2d401893119cf1e72396aec4990bea253a08e2643f9e3d09b20854be483624b40702e0881e3e391a5cd6ae801a3652f8e24c4ee213c79a6e52aa98e241a0652e678f4b9ce213c785ce4b9a70a225cd4ab120d49730cc9073c7d0e2f1f92e64835b188551785f1a6f20dcd360ad0d6920e341998e4b9a16e624a5cc1766758f1ebc21ce3c7a8dd4cb34ed89278f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part322 : Excludes 0x18004000000001100000000000000000 0x1677e39572bc5d4415400001504303818 :=
  finishCode 71 0x943f0605f1892b82d0ca2680ad510b4a6219c4261551f89ce14bb4b4c33306414a26d54186728d547e0a969bb116083845de3ece09ce41b86d5492d379e3ec31984638960c98a5252f1f68db809226827314ba986696b88412682b9a37306503268d9686d2d13fad029778f89b6056acaca6f0ccd4ca5a55517c5c1685e04db34b5886f1f0cda11415aa3f94ca62704db28f1f424ca2961ea114b4ac43852e845532cc19525a114f4391cc43219bc7c4e6549410c655714bc7d0fec319496ce2f0e03482975c17c7f036aa298f02d379842a3f84e6c43427cc1913986d5e3e09384e65a5622c69b0cda68a65929ab411c0824dfc313c78159eaca51c19ecc3b51e8c36113904d87ad355a1705e1a57310de3e62705482b588b3c7d08aa65988a9292d2985661ea9952e25a5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part323 : Excludes 0x18004000000001000000000000000000 0x1277e385729c584114000001400301800 :=
  finishCode 115 0x270602e0973680806316ae92066c15a87f8d06a65346ce2d78f96966248295346a10d2875610c76d696a995a56c218f1a381696b184579832c3d0dab4ad88a0a9695cc493c6b0ac14a9202b66149a4452ea65519ce29697bc7d8928e2c89a3f85a543acd2d43686d5862871624cf1f532b0ae51ab4b436aa3d78fa545c5b2994906f1f310c5a5498992d88ad2d78fae0d0160be2d5d345e10d2c61e3642da1d546a0a9058866e04dca65696a1d54c35014a1b59066a3d532b8b4e47387d4cac490d699666958a5d4cabc3506598d1ab43697866ca27113507aee3f8a35331cc436249c8d2c2629989233b621cc496a1245e14ca87b81528495a9866d68318550b6875696ca3543a826dc5abc38b6000b4b5892d37289a5c41520ad624c33369186d54c5112404e89b630aa1b54ca2975a1ce2d616c64b624a1fc52e0a549cc87f0548a5d243714cafe25825b985ac4732ca1fc0df348ce4665969698a66969885c5229732cc5c34b585b38a4b4ab4368d916d7c6249c8e2129d7525203b9c52e2d391b78fe2486021b5c5b348c36a0ad438bc7d705f18930a5da6ea650569966691ad5ccb32995dc5f1643b6c1ad2d2a516696920c1766034b49c78f920e716a1356af346c86645b9c5ac2d716cf1f68da0b547ed2d671546a18932515a5a48314baf8b5794521a5624b8b4b4af1f9c5a273624ad5da4734dde3ee2d2d2b8b630aa994b4abe30b614b969585b3c7d892297 (by decide +kernel)

private theorem part321 : Excludes 0x18004000000000000000000000000000 0x1277e085321c084000000000000000000 :=
  splitAt 4942 68 0x1277e385729c584014000001400301800 part323 part322 (by decide +kernel)

private theorem part319 : Excludes 0x18004000000000000000000000000000 0x1277e085321c004000000000000000000 :=
  splitAt 1 79 0x1277e085321c004000000000000000000 part321 part320 (by decide +kernel)

private theorem part317 : Excludes 0x18004000000000000000000000000000 0x1277e0853218004000000000000000000 :=
  splitAt 1 86 0x1277e0853218004000000000000000000 part319 part318 (by decide +kernel)

private theorem part315 : Excludes 0x18004000000000000000000000000000 0x1277e0853018004000000000000000000 :=
  splitAt 1 93 0x1277e0853018004000000000000000000 part317 part316 (by decide +kernel)

private theorem part313 : Excludes 0x18004000000000000000000000000000 0x1277e0053018004000000000000000000 :=
  splitAt 1 107 0x1277e0053018004000000000000000000 part315 part314 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part325 : Excludes 0x10005000000000000000000000000000 0x18f732451111005500000000000000000 :=
  finishCode 89 0x340a010078f5a16aeee3e8de1a760cb87856c0cbae867d4b4c69d43dca6528ba5a634ea99452f2525c5a0a933e9a65a47065c4eb3485c5a2976249a643c2ee065dac730d0b08154cad3b3919a743c29a1a75a5b29950c66992d2945e532ad0e05687856871a75dc731f45b03c2a22e8699650d3a0b78b4aa559c5b34ed8922974168a5e69da9952434ec96971694dda76a65715ca5f716b4eca6e5a5491a4331ac532991e5319a15a7669934eb4ee05ab188e270d3b8d32647624cd1d69cb8b669d9a64d3ac458d3a9718d3a647532ae857196aa0a334eb104679856699716b12669db0b5c526475614c34ea90e31ca994d325a5716a996716ca255329695246b14caac189e595b4ed05ae2d34eb38ba21262d4a5a4b0b2cad48aa19716a866306a8954a2c458722d3b058b8b5746b0c1b294434ae2d34eb4b588b34ec16ae2d624cd3b524b8b5dc691cc5f03c26698b4a67d0b7c69d510d3a2099a6aa5171698e4b4aa6534296965328786521c69d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part327 : Excludes 0x10004004000000000000000000000000 0x10f7a9541054005014004004000000000 :=
  finishCode 81 0x501ac3c7be8c607854c71a3454e67534eca6365054e69d69dc69b69dcc49854ed3b0bb860dfc4903c2a81989e299584310d4511496a61438c571624c67f34ece2134ece2151e9954d3b01e5a76c4951ac655153ae8d2338c2278c81e050e3312546a69d43fa8d62ceb12547b08fd02e9693b08a9d89321c454e87194c22a7331cc499a3ad3932aa8d632ab1253855174391c832ab0ae34e8a9c64719fda4153c5a9615c69d423b12671499fccaa94d8d3ae2132db126153b9082358a61a7547b2994542d3b61196958c214cc1950fa5b547ac49150905e22eb11547aa23282a114bcc45624b4ec906c49988ad3b3d1a7645794cac2b51eca654b4a4f62a0a8f4b4a69d6b1346d0b4a65b837aa3592daa614b6ca610dea58541c8a2751e90d652d9ca6516b1248872964146c338702969 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part329 : Excludes 0x10004080000000000000000000000000 0x10f729045810404081020000000000000 :=
  finishCode 133 0xfe3e8ee3801e17e1943499a7643fa994cfa5a5696c67d651382d29a7652ca1fd4ca29b532c53734ea9965ab8a6cd3a78f0cdc5a5441383a1404b9af0b22d89002958932d5d4b67455328265c5a187624ca45610b8b4132a65348ca659a6e68d34e866d6ae7c31265aba515a5a479532a883775ab8a9e23ca18e621a8b58c69da0b671699fd8922a7528c479491cc630c6319fdc5aa65348ab0a638c62e2d241a946532a896431b8b4722c638b5cc470e44b0cfea518336c212b8a5b4a770a9cd1b0a6cc47298d892f1f88cec3d318b4b49072945a0501005d0f1eb221c678f8295c5b3c7da362a731194de78fa0956aee2d591a6eb5743dcc49510c623526b58c8294669da0b5c5a69d624cd1b624c15b68db4edc5af1f9a36d2348174241cd3b3c782b4d3ae01c0a023878f49108a6598d06a65624c623946eda151e085b4ed842c49843ad3b5329e3e624c69b422866d7854104b312424ed230cdb18f1f9892627348b4be5959708219e3ec3d49e98c5e3f1c8dc06911033499dd744b9a98615394562338255c5a7e1e3e532b12529310ecf1ea02b878f4d1504b0a57604bbc7e4b982b52bac3b924a64d94c28e1a75c5b198d2e32d0a810ee694b8b56aec49338a99454e19b3212e6d2b9846c4970ecc45530b4ec15a973944640b4a67761aca3d4a2920d2e6c4934e991622ead5d892ac16959038015a2699c5a67d130c9734b9c0a74b9ce2d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part331 : Excludes 0x30004000200000000000000000000000 0x1cff331ed83a0140062c0010000800000 :=
  finishCode 63 0x240802a078f4911c532b989c1d0e2d331803e624a575a72a434b9a09668e81f447ec499a3ad39716c63929c9cf52ba693710ca5169da0958926932b0af0d22d897388ca67f528b8b4d0a6933f18473125056a3743ea9164b9b8b5a76669471c5b19fd2bb31258932886622919da76c4931caa0a2268861a64c44e10c2d3b9892c23233a885a6e973624c19b944293543ea994f0331254ca7e064e01ab4dd2e6b4d714a8eda76c4942ca9950fad3b8c325234b9a9950c2e619f54ca63d9a76c2b34db4752bb218973510f031a6d0c287d233cd3b348a0f4ec31a6d892e62f0d42e068d8d226859c5a693232a994c0431a43a0c333125842677623a0acd0a973615c4577169a14d32f1f986656d3b8cd21412b0b527331244ea72d623915cd32c3b987a13778fa5ccd32a65624a5ce2329a14d26a65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part333 : Excludes 0x10084000200000000000000000000000 0x1aff21fe5033094884240210000800000 :=
  finishCode 37 0x5317c7014ca5a53c146f1db505668578fcd3553198e5056e2d5212e7066c8af18fd6aee0240c61e3c4772495042e2d69da0f52e28614e110716cd3b521ad5d0329734d1485129915a7720648cea17944b28963229389a115d68460e82c47330c81919e8a1467b2085c3a099212cb53850af1f2129d064aeb11d683316ae19b185c10352688bd66ae1f22da5c623cb4ec84b310e5aba085a76b35430910d2e2a65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part334 : Excludes 0x10004000200000000000000000000000 0x1af7a10e5012014004240010000800000 :=
  finishCode 125 0x3b8be0785ac591a82d2aa0fc29952433124f1ea5f2b09a4d2e734ed8922973909e3d2e256144107f25cccc2e0277311c0ba723988e4679a0540f1e62988769713259a648cf34eccfb2a0d41a4d785328a5e4b999fd2e720b64b9958505b25cda842ccc494b9a994f1f24868130a638cc264b6239965a83c79c8651d8a5cd0672196ae561430a186341a7088311e0c3b8b56ae0994b9b18f1f8132c493a28266622a92611da97d6aee2d44138301244b9b18a65460d22a2347614ba9554be2979c5aa512b6c53b692b8ad44246752fca3b2bca98d004714a32515c5aa5f4b299c5c0624938f1f123c931531a4c6528b8b5452b5794c6931126a596081ad5c31ee2d52faf0921984838d36a65631893296dc5a83f33f9a4547715b500471f8338c67f24190d611fb1244de96533fa8078f86b6c49716ad5d263311dc5aa5b69db1254b7066d28b1e3ccc6483532ac8703125a069bc5371bbad5c7068dcd37318c819241b8b5c5b1e8e2d51dc4835abc87d631385e11c490ce2661a6d853288584682b41ea99518510cd39110a955842d3b90c3120dc0481405a18926913c7b4de43ea8a651ba30922d8a659846297611ca65233c74561198c54c6a29624a85e69da0f60cd913651ba994d22c49183cc4769dbc7d4cac49331b126461892483528cc33514a946 (by decide +kernel)

private theorem part332 : Excludes 0x10004000200000000000000000000000 0x1af7210e5012014004240010000800000 :=
  splitAt 1 115 0x1af7210e5012014004240010000800000 part334 part333 (by decide +kernel)

private theorem part330 : Excludes 0x10004000000000000000000000000000 0x10f7210c5010004000000000000000000 :=
  splitAt 4700 125 0x18f7210e5012014004240010000800000 part332 part331 (by decide +kernel)

private theorem part328 : Excludes 0x10004000000000000000000000000000 0x10f721045010004000000000000000000 :=
  splitAt 1 103 0x10f721045010004000000000000000000 part330 part329 (by decide +kernel)

private theorem part326 : Excludes 0x10004000000000000000000000000000 0x10f721041010004000000000000000000 :=
  splitAt 1 98 0x10f721041010004000000000000000000 part328 part327 (by decide +kernel)

private theorem part324 : Excludes 0x10004000000000000000000000000000 0x10f720041010004000000000000000000 :=
  splitAt 1 108 0x10f720041010004000000000000000000 part326 part325 (by decide +kernel)

private theorem part312 : Excludes 0x10004000000000000000000000000000 0x107720041010004000000000000000000 :=
  splitAt 1 123 0x107720041010004000000000000000000 part324 part313 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part338 : Excludes 0x30010004000000000000000000000000 0x1cffac718341101870010004000000000 :=
  finishCode 71 0x6b1c84f19434eb60aa298a653389a3437331251024578a8ed2d22ca4850b9a5ec45440a994ceac198b3b16a4372882b8b57511806c1845328a9d2d330fcf02c198b5334b632ab125a56d2f438ce1f60c82054cab4188b2a6532acc21532b4adb05e1945abcd3b5329a0cd36c02902a7438cb53528a1fd4a334ee695a994caab575abc1b969db12454e7016035796ae8c299628bacad10296f60cca65440a4cdb43716a734ed892849436b126323b0cc0e6969438b0b64b4b124a3e94f0c1ab8ca2f0762d86755f0e00dcb116346b4b5102045929e68d5abc9473469626696b0fce9ab57346b07e4a7b8a5a5aa65346a2054961b9532cb57440a887e1d863c6a5a4b12655909295b3b0965549706e6285a5bd29ea356c16ae88157128f34bccce68d695ca355a1c963 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part339 : Excludes 0x30000004000000000000000000000000 0x1cdfbc500140001830000004000000000 :=
  finishCode 145 0xc0280d61e3db47215c068835d4c346a5c61c2ad0e298a98529a95d22bca353814c4b7ca655aba204d3729956ae6719e3e68d631e4346b204679a5aa174b79a754c30e16233a205497258d6aea6532cad5e440b28a63608816d1c8624cc2b513a53588e671068835d5c6916c39187f0a448ce67f5d1e40d8a1b6624a5a50faa4d908f161549ac3f94caa4d23399fd08f216587267f326c84751ab90f2320c61a7544b3884146a6571199fd88f288588a9699892c311c2c077510b0c588e72119e33f828e791244f18434e95b6233961504b1e8c3394cac45616c5a1710b1254cac3f616cc2b6229a7524438ca650ccc6476238e15b46c19c720c4068835c6a319fd88e67f95c430e45d08ce782a0a3d530b88e532b4b44cae2380d2c4941bcb1d8b0aba1a894d8b528370d8a89d4c2f2318e29946a86b232c94d90dab4d908e56d513cd2d0d8a8d6513c0d106b998922e8a6534ecc2d43f9616619b884c8ec2d615cc4734ea789c21c66159a74c8ea4359ec83b34e991e622b90c2d8c8e67f6239d86233a985c879188b191d4ca69d06bb608a034470b257529a3859a773114e4570a023396763aea92cf02a65619cc239a5a75151aa58b319476a61624828c522a35221ca65148b60d6368b5788ce671068835ce051ac69d32cad5d102f21f869d2b0d0439a5a4c9701d58668199892d3b619cd3b624a1ccc331d0546ad3b623c0455a1b4ec8cea615716ae88151acb2543e9a0cd1aa43908ec3f94ca8811878c7da76b57 (by decide +kernel)

private theorem part337 : Excludes 0x30000004000000000000000000000000 0x1cdfac500140001830000004000000000 :=
  splitAt 1 112 0x1cdfac500140001830000004000000000 part339 part338 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part340 : Excludes 0x30000000000000000000000000000000 0x1cdf24004000000000000000000000000 :=
  finishCode 145 0x6c19c5d1c825cae03c3681227035ccb2b5753296adc5b22041ae69d532a49e69da995242d5af84c3c7d4cab3d9c5aa6132cb12651ea5a4cce95b42fca3d4ada5bde3e659333b68f234896030dc5b2d2d2def1f51ead5641a9c0465987296f43ebc7d4b23639e3ea53870ac39061a4ee61ca985e3ea1751eb90bc330d00f0d583a0b569025cd0c3151da76b4b81aec498d160d740189322052e60d73c7bc8973430c0d7023cc2b624a2056c3f11841ccb4b3309a2de4440cc4942c835c13325cd102a19983ea43440835d0b331241aed4398f22f80d74b7c69144096ad4ca9638f1e667341b40e29928e66753296ac1a278f5c12df1a4510266794caa22d2e3c7a1ad70580b566539292a174b99e3d4cb38b65a5a53d10325ccb560d73c7b40d616adcc5101ae6639a76b4b3499586233c82349aa5c4cd20c5440cb4b411a8440835e499b8b652c835d89267d81ae94280841e3cb567e199d08f019de3e87d716cc199e3ee2d6b1903a0186d37923ee2d440a57583e86143ea5cd245a5c64d690a96d4ca52333195b5c5b38850465395112bb11951028614b9a1f5a472d2dc5a973381c5b220448315b4cfe973716ad2cccf21adc5a78f2d5b30d43483c36b1cc499c669068835d50438c881398a16cd26699499cd3b3a1a5cc6130c44d262a7440a94e2d5835d70691a0400b5688181ae78f233c881624835d2e6b60a5643f835d102699440c0d72d5cb6035de3f0a9ccd2b4b34c9cc6334ad2d2e6e02e0b016ac11722052e678f06bce2d532b5078f92e6927532835e3c794361b8a20522669b5aba994b56bc1c078f2d58f0de3f2d5d7478fb0962d4b11e715b0fcd3232b716a505ab499cf1f049a994cfa88178fc933 (by decide +kernel)

private theorem part336 : Excludes 0x30000000000000000000000000000000 0x1cdf24000000000000000000000000000 :=
  splitAt 1 98 0x1cdf24000000000000000000000000000 part340 part337 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part343 : Excludes 0x10c00000000000000000000000000000 0x1e737c53c000000000000000000000000 :=
  finishCode 129 0x170561ac2d5ae8e61a75a4716cd3b33f92ac196c021067f9696d1b69d86ac91a7598cfed3b5a5b46c356a6511ec663532b4dda76b4b61fc63971694b47220c5671846c178065a60b41f8b4b891a86b43eb8b661c86ad4ab119da42a5f145b0ae233b46da761ab624c71369ba995492b4b331c531234adac47532b48c0161569734edc56d1d233923496ad3b9696d3b94bec1f71695b4197130d3b9696e2d400c82d0cc622394b6d23532b4ec48e4ab94ca631691c67f291cd3761eb4ed78691b025aad2e716b4ec356a658adb02b5697358ce3000c54816c3c7ae8aa02dd85b145cef25a9233cc2b61fa916226b0b4b0ae2d28bce2d60fa5a54cab612ce78f82dd06712a5e3eb5768dce2d18fad5dcc501b03c7c4b37169a456af12a5503318431d95a6e547716a995b061dc77968db0f4a8e67f226ca452599a0c4933fb0f6622857d4871e8903008028878f431c5a39161ec46750ccc4561e9a0e2d2a3ca19622a866527b4b485ab579866a19153b8b66158e44a1b20cd4cae2d5abbc7d432c45153ce2d1c8a80a559c5af1f5ab92a56c716951e216a5a4966a49989267f2959c4c0fad6368ce2d00cb5f0d3b2d2c93e4a960124f253da7678f09dce2d69dad2e60168153ce2d3c792cd857308dc5a78f255ae89a34de24f9a74722a19945ec4569da995a7734dd45aa65318b8b493ec02e84a1255999e4b49a75a3734dd6969e296652db8b50fa66724f9a74ccf2b0a012d454f34ecf1ee2d96962959c5a4a9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part345 : Excludes 0x50800000000000000000000000000000 0x1ad5fd420000000000000000000000000 :=
  finishCode 149 0x338c42c0ac12e5a05c1ac2d5b6823d9c56c471bda5cd8920c7066b00be3207206dccff11452ca467716c4514b2a70c491b6c60d532a5cc6db18354ca45b988e46733fb0e60dbcc2d6618c401a4260192e2d945ad3b532a5cd696f1f9c562973c78dee532999d2e678f1bdcd3b4b98326532cb4b69da5ccf1e881d09e25cda7728b5200bbcd3b490a6f2d2cd36c475328086715a48a0299545b1a6cce338b52b229751bca2d4b699c528ab82f066357118346b68b4b946e29151491465a5ca2151bcc494aca5b52450ba5b620d988d452d3b5a5a9952db27892285e14bad2e69da85c6f734ed696cc25cc19b2d5c52e1b714bcb57681902d59c01b763148ab572d0ca33696a97cd367399652a21231a895c5aa1d346cd2f78fcb57631545712469cc45b210919da76b4b5329a6d7469d9e2634e995652a919d696a49532ce2b34ea78c49424c451426bc7d4b669d713c67522da17e52cb4ed4cac4922db40c034878f697cc4978fad5c18e0cd32ccae31867596ae69132cc0cd064cb5763154131c78928ab4edc4ed354b28a5cce268d5712c33ac29b34ecc49532cd3b50b916d68269d13cc659624bc7d4ca45122db40882e0c42c05ab2d0f1e6914b9918e48ea5654a329165ab9a6dc5a78f8d068018078f591e3e9734d0a6f0e450d28458c471907c238a65908a8691bdcc49624c851434ce2d29ba68d3b4b98da61c09a750d2a45987ab193339a0e2d59e3d70490a773c7d6969735329a6d744f0cc72515a5a68d34ead2e4b99a3453668d928a962d08c0a6c6f725cc8c6d3b9c5af1f78fcb4b4b9b4ed48b30f52e669d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part347 : Excludes 0x10800040000000000000000000000000 0x1e576c420403101080004000000000000 :=
  finishCode 99 0x1a05c188580b56d83d89735d18c25ca486399c5a44d1c8bc7da5eb57348a99500346c78f4a2cc21714942dc5ab5732ccb573c7a995e4348ce2d3c7ad5c93ee2d90666715abb2078f29096695994c6c338d36a4d30bb8b549b38b54c6be1e3d4bf38b48daa652549a06474b4ce2d618942ce66357716c785618942ce0530952b57419c91351ba915c5aa630b5ca45622bc7e5179a35a5ef2348be206e338927d6ae4a96018c3c7858e4b7ad5cd1ad3b9856a63346cb573c7cb5769d9a6ccb267196ae78f58180670f1eac12e48db299522693b5a591b6532b8b52e6ac1f0a658952b4b61ec47969da49d87b2995c5aa45619a5cd885d1a453292e548b1a75a769731c89a76522927e532a5cd696601c0a65095b4ee19b9a763c2b4ecccf11b5a453129e4a9531ce2d61e85ae78f91154ca913622a5be69dbc8e6348be2d84a969dc69b2c292ad69734ed74510d3a97390fa9699c3f311d2e68195a5996452e4a149dcd3b34da1f631cb4ed28eb4b25c9a75746c18c25cb096528b4ed2de69b531cb624ee69d86954ca0a3526cf1f532af89c299510516ca4350bca2588daa17945ac47 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part349 : Excludes 0x10800004000000000000000000000000 0x1e55ec460040121010800004000000000 :=
  finishCode 85 0xe0300d03c878f641a45f0c2f25a588aa455ab832496a4a969dcf1f2419a7419a8430ce68ea5a4d3a48d32cb584679e3ec1934ea996338ad5d8328e3c7d6ae08584e2d2f5a9a0d492e68d696c675066a06c54f0335445b1a463092e9c360c478d362a75514c04ccf1f53286645233c7d4ca1ad4b7cd3b52d91b6233b4ec54ec4932cca634b79145b0246b2069b715c825047a125892d3b624cf1f521c69d6c1892d3b852a65534db4e6047b4ed4871a742de663624b4edb0571704718c690d369e03246db34ed6aec4734eb06633ab11d8331a74ceace1966066927e32c8a5e6169a756aef2168ba1965a434ea0461c4927d08f2865a771ced88aa1940da99493ed62126066b1260b4cc3f19bb11d2d2c1932c832508f290c93e0c95abc92318ba19d5ac5b0d3a969987ea652cea8e6618acc58925894b4a1c6618ad5d4ca49f12dc58524f9066623ad5da764a124f9a757c1abc22b48aaca588a2a725992d5305d0942c3996862a7205c06b5abb11454f1a75856b57 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part350 : Excludes 0x10800000000000000000000000000000 0x1e556c464000000000000000000000000 :=
  finishCode 77 0x1701e1b40ba16adec320972a65882a63969d91e4d3ab4b43fce2d34ea5cda76a2358ce38b6691a8fc92eb4b4b9831c19ac824a64b29a75697300e2d94cac4925aa12652fa994d3b2d8a2300d21235c5b28752e6c49255a5ce624b389a29964b9832588e663947e0cd4b9b4ee33198c5c5b34ed6960c93a1ca655a5b4ec192c497916c511cc32091a497624cf1f5a5a5ce532a875e3e843604791c8c4b94adca65436b4ee78fa5cd4caba298d82c0e612e5a7721b587aa6525aa51e532a5cd2b730f4d3ad3b5a5c93b34e9a76532c97359892d574671a772994972969254c391696b89cc8ea29923e6314b9a995696647624ae832f9276d3b532a51c9729c2995a6f151de3e9734adcd23624bc7d492ce3d88412e4b80b7cd3b78f831523e96f78fcd3b5a5832569724ede3e4a18192d239869d96964a925a8e2678fc48d624a96d09285b (by decide +kernel)

private theorem part348 : Excludes 0x10800000000000000000000000000000 0x1e556c460000000000000000000000000 :=
  splitAt 1 98 0x1e556c460000000000000000000000000 part350 part349 (by decide +kernel)

private theorem part346 : Excludes 0x10800000000000000000000000000000 0x1e556c420000000000000000000000000 :=
  splitAt 1 102 0x1e556c420000000000000000000000000 part348 part347 (by decide +kernel)

private theorem part344 : Excludes 0x10800000000000000000000000000000 0x1a556c420000000000000000000000000 :=
  splitAt 1 126 0x1a556c420000000000000000000000000 part346 part345 (by decide +kernel)

private theorem part342 : Excludes 0x10800000000000000000000000000000 0x1a516c420000000000000000000000000 :=
  splitAt 1 118 0x1a516c420000000000000000000000000 part344 part343 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part353 : Excludes 0x90000800000000000000000000000000 0x167fa620804a400020000000000000000 :=
  finishCode 69 0x350e4330c43283c34a1bc440ac764b292d54cb16ac97238150068f125de3e9332d5ae8295947e4b948fca49532a4a452b12e4b56be2804958952ca2e04b3522c91f69d8a85102b2394ca45769da914542d83d8a21d02a13f1a7687d9866c49513cc49947ac2089e58e989c8aec33532a5a5a6a969987ad3b98922954b4ca6530ba88c49440a47e69da1cc94229794b691f4b49e3da76be12e65a59e3da765ab24f9205887b11032d5c972969440c78f2d59e3e6f16c14bc96925092d59c6c160510f1e4b9522c881141a206522a5a50e712a4b0f3c7d88678f44092a52e722049529279696c232409e3cb56b83805ab624c9733c7a2065aba5cd7c4b10c3c7a5cc902c4990d6693498c945716b1263c7a5cd8932d2cf1e973 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part356 : Excludes 0x18000804000000000000000000000000 0x1a7fed40a0f0603038100804000000000 :=
  finishCode 71 0xb8328a62608817e11c50091a27f8d36d2f42cb1256aec4994cb026d04638962494ee697ad5da76a65348b1254033ac78f5abaa8ba34ed08e87f94966639862823412a92e41aa1b55c6911c600f1ac819d63c7ad5cd3676125a8c760949a6cec249733fca614a88e2554310712463985a6174359e3ca929313b8985e0049a4526230d13f8a54c2f002d4ca85b29a8464ee2aa28078f989269134da04e14ba11d44f185d06a8373c7a4c64a88e25405abc78f54190690dc671092ae2c965328a5d0462953c6b49643fb12508ea65610c655532a60ce299670fb12452a297398c87169db1254caa659a7684794ca849532cc8312564730cda768e28f65a99e34c2b14d50e6e1f41abf0a026078f1c4c49542cb1252c333a1b6530a1c5a764955a1c8474c14ca5479a76c49423cb532a3b4ed4cb34ed89278f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part358 : Excludes 0x18000800100000000000000000000000 0x1a7bf505e0c162002301c000800100000 :=
  finishCode 61 0xfc3b0d42803c3581303c7a3096f9696c4978fa4edc4f3115e3ed1b9a46f1f493a5cd69684260c4990924a1499a5bdbc4b1e3f1d0da76e2d4369d0e25ab8ad092d3b5a5b8ae51e8895c5ad3b3a1b4ee5a5a7074378973715cc495a592d5c5a29551ece2d3a1a47c62f151d88ac2d896ae2d3a012f34ecf1ec494b9b12678f9e3da8651585d094227d8a56a6569db124712b4b94cad3b624aa8be2996240a18496686184fb0a54a9338b4f1e2953c7c881309c2409733e12869dcb4b333cc3122db12412e78f69da586178f1ed3b14a916e69d9db4f1ec4914b8e2622dad2d4cac49624c8497169e3d696c499092f1f3c7a5cda83c7a48389852e537852af1f624ad2da7608d9696d3b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part359 : Excludes 0x18000800000000000000000000000000 0x1a7be400e1c0600020000000000000000 :=
  finishCode 111 0x68158760b56fc2503c35312c440b20601c8c199492295426a1fda6b06250dae2d519a8f6716b06d49ec435a5b4ec52aa659c5ad2314aa5ccc8611cc1b3a1b8b56969238ae60da5cd092a3f9a6ee2d3012e728cd4c31d0d303b180524a8fe14a928523e0379c3a117624a8fda76de125e715a5cc9422199452e2b4b9a47d744b9b78a4b8226d3b14aa986716cc8360743006006dd38524cb4b4b9a8ce716ad2da7738b6532a97da7629794caa5f0dba48aa28ce42fb8b589238914bb10e436a995a7738b538624cc4330a829d1022954b99e36016b10cee2a5f532a20578246cd3b5a5a1649421ab69dc5475a5b50fc330ca0f0d545010c348b8b642792ce145ce2d430a925102b579e3e0b5524c78f52aa00aa1e3d90259c69b44092056af3c7d6ab387d856a6552fb4adc5af1f399cb57440b30882d5e624a5454ca0b50dba5cd740dba20629d8a5589322065ab9e3dc0624c9733c782ce624922d2e6a62b0881661f84807869739e3ed3b04cc09d624ae8ae1d064a599fdc5a2950579b8f1f989296d78fcc49716c099624a5be246a4c6519b4bd892973716bc7da87e1a41e1920625999c633fc0af14ba9955c78fc9730578e264a2a1cd0fac49 (by decide +kernel)

private theorem part357 : Excludes 0x18000800000000000000000000000000 0x1a7be400e0c0600020000000000000000 :=
  splitAt 1 92 0x1a7be400e0c0600020000000000000000 part359 part358 (by decide +kernel)

private theorem part355 : Excludes 0x18000800000000000000000000000000 0x1a7be400a0c0600020000000000000000 :=
  splitAt 1 98 0x1a7be400a0c0600020000000000000000 part357 part356 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part361 : Excludes 0x10200800000000000000000000000000 0x1af9b604a842408020000000000000000 :=
  finishCode 155 0x3f0d4390ec310d00f0d40715cc49426b4ed46a4b924096ad9c440cc4725cad86939a76677716c6555a5b78881969648324b99be501904618024aac087f891a8813c79e0b4396a6a3d43fa56d4c28814b7b1265ab825e624991d2d2c499e3e88124fb289658ce2c4978fad5d10278f96aeb8298ca2388814e0c8f31254b24b5331a484b5690ca27616b4ecea2537801ac2d611989d23e76d61ec931313b0c585a969624a488e25a51432ab0ee1a6862544f2cd44cf1cc51c370c8e860a263138cd46aaa278c4e76d40bc529513b00d318a52e29595b08d6873289212d50e32c8d886d3b14bb4ee616a545784914c308b5886c49438b4ec52e6c238b433b6cb2351394a6096b4c5a63213669db28d22885c247e32da96cf46248da649881b4edb30c52d2d3b988ed213aea98452ea5b924116a8f661eb125a76969414c06912fae0a02385ab670d1a78f949246d24abc7d4aaf1f892ab575abc78f624a4c4966691561786c16c5a5b4ec35686f815ae2d25ab8b6530b48a22d868b9c5a11725ab4ecd26d3b969666925ace2d69d993652f9445c5a9692a3cd3b5a5b280478cd2c472a3b8b4cfe8812a3ca555109025479c3ee2d345b4eccd24b58cfae2d50110325bcf1e4952d5b48ca2504b5141c669624998d2e68815d1384b4b8a652c8a0ca6f308ca52c4950cce2d624b38c425a4d1712e452f2984cab2984cb6c425a4cff292dc5a4b9051c40b396b125102c81e0d012052e71e3cb566698972f1f4b9a5ce2d5922cf1e5ab8972c42e04b9561282d58a46621a20482b34ed2e668d91021b750120231b4ee5a5a5ccf1ef1f9892e2d852ea030d644085fd6ae78f64124623cd213ae9dc452eba14de69da0a509a951985ac2192d2881 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part362 : Excludes 0x10000800000000000000000000000000 0x1afba4008040400020000000000000000 :=
  finishCode 93 0x1d80f0b60ba3904b95e1a01e1ab0d3b8b56ca288aa1a6e1d0bc7e109b8b506aa65489ca65532c91378f92050fb12052d2859532b408416ad30499c96f51ec96969d9d0d69700f5276d3b78fa8fe532ad2d2b65016ad7c69124ea654b7cf1f713889d846b4b240999e4b7a08d2d294f8cce96f221c6671b1855de3ee42e0a02f0d00f0c90330b52e678f2d5b11e240b8ae624a97c9025ab1e1cc2d435cc494b98f0d7c3c796ac81b0875c5a6671b1bc7d4ca6679984adc5ab1e1b401578f1e733440ad5cb56b4b80fa88150158580b5696f9a7678f460f84b78d2e78fa994902b4b78fca3d9e3ea65615999d696d3b6c19455174348b08be0e84f1f151d4ca78f8a8e913619a44e619999cccf2995892c2b22bce2d619a994cce6755814ab1e3d49320d44fa66f71694ae08b84bde3eb573c7b488c1f8ba19857c70fc457615b12416a68b70fcc2b716a5a585b2189e21865149a64ac2a5f9c5a729532a206716ae8b81580b5389ce2d323b87cac2969389c5470d5b8b5a772985c5a27d615ce1d532b4ed85aa33988a1ab (by decide +kernel)

private theorem part360 : Excludes 0x10000800000000000000000000000000 0x1af9a4008040400020000000000000000 :=
  splitAt 1 117 0x1af9a4008040400020000000000000000 part362 part361 (by decide +kernel)

private theorem part354 : Excludes 0x10000800000000000000000000000000 0x1a79a4008040400020000000000000000 :=
  splitAt 1 123 0x1a79a4008040400020000000000000000 part360 part355 (by decide +kernel)

private theorem part352 : Excludes 0x10000800000000000000000000000000 0x1279a4008040400020000000000000000 :=
  splitAt 1 127 0x1279a4008040400020000000000000000 part354 part353 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part365 : Excludes 0x12000120000000000000000000000000 0x1a5dfe805249252480124800000000000 :=
  finishCode 23 0xd82c0f62b029515392e570621cd3b5a5863d44309b4a76f1f4b9ad2d29b24d5892cc3f0900f0c8cf25cc52a5359892b5504e918e4368a4452aa42d065aaa95413a291532c083716a44d2c69737e10b70a9d28e3c342fc44f624b4ed4ca86d14a9403c352fca650c5cf1f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part367 : Excludes 0x12000100000800000000000000000000 0x1a5d768630c901a204100240c80004000 :=
  finishCode 111 0x1f86a178630786d8280842706758512691640cea9639a764678412a651a3bc7d38580d36f1f9a76c2d1488a56624a9948cf11b4522d3b391747513855000324e54ca29162486c4cfe87f989291f4b0b11d0c0d8c87f233b126153b12669d91250fec47624c29133fb11c54f06c588eba3a8502c8a654214861b1612c34f438a486624b095c4e93b9a76467984a291438bc7da770a450e2a659a76291104c6594b781ec8a2a6564108499c947621185a5b11e42d99bd85b06c4d26d3b69cca6502e885585aa5b236b4ecf04a068e25b80f2d3778fa5cd696547854ef1f5a5cf1f7b0c45f0fc300cfa693942e85f78fb4ed2e6a22182a75a5cd3b233a5c585b307d852d3b49ca5866409728821897346185b307c4e646d233ce27521b07e4610c236a8fe69cb8ad4bea17412cc2d68ec46761a951da769739c57119cc96d3b2a3b07d88e4b94aec75915399f4972be3207202bd09b2d5589321b52e6f1f92e6b5597c6a1bc5329c8b231264ae8a5642d9d660d8b12652f92e5104812e618f9696d3b49cca2d056bc7e69da40d2378880a5588f286587ea2d60f8a4669db11d86aa17623c27d4b8c925325aca6516b11cc96973 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part368 : Excludes 0x12000100000000000000000000000000 0x1a5d74821049812000100000000000000 :=
  finishCode 103 0x17c591702d2a50f622059c6212d2b0069650cbc7d4ca3c325ca44e49286c471aa6569dc0a352889ac71a80270bc0f0e62499fd083239146624a5bd0fe2a794b6c4969dad2e69c8a9d89238b8d36c49611880d4a1fe71682b58923c369dca65136a1fd0ff3125696a515328dd5cc5e1b078fc96333a9a6c15734ed4cac49228c93325c8e35892a658786d3b78f92e5987e19c1e1ad2e4b786a58929692a3ca6562494ee5a5b4ed2e6a6562492e6532ae0d42205ec3f1884b4bf0a639696a6525c8f0d4771a6c972c620a61539535a7238d532c96f51ba98d981c69cee6238825e3ea655108f0c536a659c56a216c13850012308ad88e057531b8b4d0669b148c295528c3c35328a440b32874522f1f5328f0c9733d8ba0f0e25ca5a54cb0f0d47702452e63c35c1046211028834ee33fa5cc972e2d7b1a825c8f0e69d9a6d42f38a5e3ec4769d826669d9a6d90551a76721a4586b290d0fec47852ad2b90dac359ec6a1887e0972d3b96969471e1999e716a875696cc2d8789926696369da1fc54f25bda769339a5e94725cc9c25ce04e9a450ff2c95886683594ac0f6025e499ad2de3e28b32c92e412f199d0fe3c3499c3c3 (by decide +kernel)

private theorem part366 : Excludes 0x12000100000000000000000000000000 0x1a5d74821049012000100000000000000 :=
  splitAt 1 83 0x1a5d74821049012000100000000000000 part368 part367 (by decide +kernel)

private theorem part364 : Excludes 0x12000100000000000000000000000000 0x1a5d74801049012000100000000000000 :=
  splitAt 1 101 0x1a5d74801049012000100000000000000 part366 part365 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part370 : Excludes 0x10080100000000000000000000000000 0x16fd74c05221050080100000000000000 :=
  finishCode 33 0x5e1581e1ac069d4a097218b96969639e3e63994a293b69da51d696d82484b9489c8354b4a994e67142c2c687d5302a73c7d102a652d2a44e5228cbca6e153532ac0c8360ca25ccd264b969dc87f440a16e33ea9953c420d3a93392de1039276685440a108c3c7e69ba5bd4cb1a15696f1f499b4de49dad2ccd28819c5a4af5a5a5cd0834e969643691e528e66f88cea65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part372 : Excludes 0x90000100000000000000000000000000 0x167df4c41001290000100000000000000 :=
  finishCode 19 0xc43283c36f1d45b01aee2d8d3aa49250a4ee34e925e5314bf19bcb4a66f8d3b12e574750d3a881945ac49259996c37a0d52a3ce2378fb08d1024b3590966c499102d3b2d28356 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part374 : Excludes 0x10200100000000000000000000000000 0x1e7df6841881410200100000000000000 :=
  finishCode 55 0x1886a1901e1b28de288d3990b69694409234d3a4ab4d169725cda7666f25a969496b3124d3a66f8d3b0d1e24bb8b4972b4b78fa5cdec6711825ca68a619f4d331694aab1a6491682258b425ce245b46e624a5cd89324a5c5a97361ead361cab4e4aaaf1f8a8e973342cc82e8ac29869d4b9ce2d78f828506ec492d29807225ce78fa1c4917122e5a5a5ce1bac96d2a496952e729882125e78f99c4966c3b6249695102b2308633196951c5608df198c92eaa1956510822678f9856531a5a5e3f31249524b5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part376 : Excludes 0x18000100000000000000000000000000 0x1a7ff4801403018000100000000000000 :=
  finishCode 87 0x621a87e1941e1b48de2d8a6594428810da92cc1aa4a15f0d232935056f1f2d292a41ab28851026475f0ce334b4d3669d42c9204c525a55a5c647440a164d1b2204d36f1f944249534e8355bc5701aa922e869b147c69d2d2c96d852a68d440916e2d2af8b02994b4a691852e5498d36b019fd2930275c3ec494408a5d8932704c2b0c82e8881a755c4b9ad8a630c6440a1fcb4ac4904eaf882186c152b4b9886463289922d0b72d0485e87f4b8cc475a5b0a4c3687f716c939624b4e547e72b618969412a5a590feb4b245ad0be2d848b2d2cf1f691ad2d0fe5a59e3eb4b27144414a9884f104cb4b623b12413a61b90fe9713a0a1fe43fcc49427a06569734dde3e8714149cacc04a12e6643c7e69dad2d102c495c0b4ac439102c479056971616cc4969dbc7d887220588e5a54b9c9739a431cf58925a534ea5cd4c4a18931a74b4ab4b440af830f9a76f1f2d2b8b6640c034e8c3e78fa1b6289846d696c43624a166624ad2da36f1f4e01aa5a5896ad3b624a994d3668394ca4b5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part377 : Excludes 0x10000100000000000000000000000000 0x1afff4801001010000100000000000000 :=
  finishCode 73 0x6c03c2ba3204b95614c34eb289478786d3b440969578521283e149309a48ceb4b660ac1e1bc7e716b4ed2d2a639892d2961eca5149db4ed492e2d624ca4984d2d3b4a3ad2c78665592d2d22d2e4a38f0d2c665342ccd3b5a58f0df8530786b82a8e2d440a996329a9549026179226f1f489cf1f240b8b4b4a653964530497298c856467716969494524c143695b1248c7082652aa1bd4c63c39f85617863078618f9a76c49616a1f4cc322054c34cc8812d299be4b9c3c35f1a42d2b50da29952e31584d3722096184e6b4b69da5cde3f34ec52f3509231246f6c358d229359c5668d29ba92588f298cc1a7671699f510295b1e1ab09699102a4d4b7ad2cd3a74298e532bc7c2c6a658902a514899a765a5a5bc786653 (by decide +kernel)

private theorem part375 : Excludes 0x10000100000000000000000000000000 0x1a7ff4801001010000100000000000000 :=
  splitAt 1 123 0x1a7ff4801001010000100000000000000 part377 part376 (by decide +kernel)

private theorem part373 : Excludes 0x10000100000000000000000000000000 0x1a7df4801001010000100000000000000 :=
  splitAt 1 117 0x1a7df4801001010000100000000000000 part375 part374 (by decide +kernel)

private theorem part371 : Excludes 0x10000100000000000000000000000000 0x127df4801001010000100000000000000 :=
  splitAt 1 127 0x127df4801001010000100000000000000 part373 part372 (by decide +kernel)

private theorem part369 : Excludes 0x10000100000000000000000000000000 0x127d74801001010000100000000000000 :=
  splitAt 1 115 0x127d74801001010000100000000000000 part371 part370 (by decide +kernel)

private theorem part363 : Excludes 0x10000000000000000000000000000000 0x125924800000000000000000000000000 :=
  splitAt 4458 121 0x125d74801001010000100000000000000 part369 part364 (by decide +kernel)

private theorem part351 : Excludes 0x10000000000000000000000000000000 0x125924000000000000000000000000000 :=
  splitAt 1 107 0x125924000000000000000000000000000 part363 part352 (by decide +kernel)

private theorem part341 : Excludes 0x10000000000000000000000000000000 0x125124000000000000000000000000000 :=
  splitAt 1 119 0x125124000000000000000000000000000 part351 part342 (by decide +kernel)

private theorem part335 : Excludes 0x10000000000000000000000000000000 0x105124000000000000000000000000000 :=
  splitAt 1 125 0x105124000000000000000000000000000 part341 part336 (by decide +kernel)

private theorem part311 : Excludes 0x10000000000000000000000000000000 0x105120000000000000000000000000000 :=
  splitAt 1 110 0x105120000000000000000000000000000 part335 part312 (by decide +kernel)

private theorem part283 : Excludes 0x10000000000000000000000000000000 0x105100000000000000000000000000000 :=
  splitAt 1 113 0x105100000000000000000000000000000 part311 part284 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part381 : Excludes 0x40300000000000000000000000000000 0x11f4b1540f00000000000000000000000 :=
  finishCode 111 0xce310ca12e5bc6418c55018eae1a766139695102683346a206338bb882591029692d2a92634ea124ceaac196669da2050fe5a534ea4ae4a9a1b5dc591343f0b4a8818cb2f1f6249f0c419a5ef1f5a5b8b661eb084cfe88134dc1a9624b4be440aa8f1f98926714a9cf1f624bc7e62499fc17a5a5360d3ab4b92aeb4b86f6902b0b01a75043c7a58881571c3f2854a7693f0498a24ea3310d4aee1f046a8ae610b10d87725a41468229088178fc39532aa55c24f34accab11d56048bc78f624c88178fa54d4c41134440a485a5641484acc61d697bc7c4c283714ebf8f1f8d229319a5a05d4b4cc350958c3de3e05f90f2d2d31abc7d25f0a74d0725a4b4afe21de3469a0db452018e740a75e3f24bc686543696cc4343bcc35522a1e652da40802c0e41e3d22f1a74980bfce2d695a5cd69609598929730bfab0ca1a75dc348cc492d2a54e78fb1258533c7d892f1f92a6c49341a0818734eab888160dcd2d398acd586a87761acc3d43bc0892d2b0855c3b1244d0cea683560b4a81d9a62475621ad2d2e73c7d893270c4349e143a5cc8eb34bde3e8772d2b08602fb0fdc56f1f523b4b4b4a9c169589263592e614f9a4e1a32d2cc49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part384 : Excludes 0xc0120000000000000000000000000000 0x13fede6db124800000000000000000000 :=
  finishCode 37 0x681ac481746c0d3aca2a88810609d264179e2587b29067b570d2a29b8f1ee2151991746f73c7e532b4c5882c4914da9963c7b124d2a982d0a429963c7b124d2ea658f1ec492a1ca653c7b12418321e5102be2d0a40a762a1b1250ca68934ab10f1f94ca0c1522c67b624a2050ef1d14f12c3d335b1251020c1432cc3934a8305102bc2205684b9cf1f6249e3c16ac499e3e9733c79e3e134c881 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part386 : Excludes 0xc0101000000000000000000000000000 0x13fe747d016d010100000000000000000 :=
  finishCode 49 0x358ba278a61a757c32eca6578fa204d2a5a5417c8816249a558861143aa439892197433950e52db08da2d81bd9e3ec4914eb4b6624a8b6624cf1f230a96d7c520b4a6825ae532a5a48bab01a541532994f1ef1f9a66957624c9538d2aa6300ca2206624a914d2e5a5716c8773369a2548f310c48665f532b4ec8ba8815a5b8b5cc33053b31250eea6552178624c2792318a74cf321e5892a458f1e8796248a16532b00ca2f0881497cf1f532b8b4d2a197699c78f4b4cc1d69d99ed88678f34ab126716a9952d2881 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part388 : Excludes 0xc0100004000000000000000000000000 0x13fe71ed15001046c0100004000000000 :=
  finishCode 61 0x240b0340ba1e3d3c530d3a68791029c30fe4328a6d45a44598926795912d3299522ed3b32199ecb4aa65837aa42985998d0e881344b28d3b94ca29d52db06e532911510329154aea655d14c34ea5a62d2a204cc432ca6514dc86594b2c61a755c4b3c46314dbc7e2d2ca6370be2205b42d28a760dea4f669ab88d8928793c4cd2b13cbc7dbc5f1340dea9963c4a46e4d0a8734bcf12d2b8472f1f61aa5a4f0b1e25b45d16c6f17c33037a0c794cad2d697c29b710cd2d110a8b48c20c714ebc7d89243d8702d2d14ea9160deb4b589287798920c743cca5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part389 : Excludes 0xc0100000000000000000000000000000 0x13f6716c4100000000000000000000000 :=
  finishCode 129 0x1746409729031869d651bc60018ad1f9e3e29b05da54e13ec88169dbc7cb4aa5505da90be1407e2995a53117404a4634b4889e14d990549246352a9174d0336c69730ea4ad2a666d92aec02cd669aa5a4d2ec4914db12614dcc492d2cde2f80c5180176c29948af1f48d968b23c7e614a96de3f30d45370c061b9432e21695a46d5c716c61b70f9185e3e29b50ea96e12ebc7cc367754b4c61b621b8b4b4a88105d9f8b20c06a3125944b4af8ee0a6e49786f4b4aa658536c298ed2c2992a69573608848dc94349ecd3514d9694d131a5d2a72d2d2d6f1f6e1205a5a54e1bda5acc3b0015c3e77514d99b52d72995e3ed2f6e1345a59b05a54a1ca5f1c0c29b440c46151fa4be4b5bc7d946b1dc531282d2b1888168127b19edc5a69762483154b32d2dc5aa5b90f29737168316716b98c0270661e3e532a1950eed0200c81e3d43b0a7549321e5892b4b94b6a5b94cb0a7543aa496248a76624831668180521686410cf296ccd66870639e3e4b9a92589269769dc0c75329e3c18f031e43bca594e1102c029086543bb08e1bd8a7542f25ae532a92614ea90b4340b02f09e299661aad2cd2e29d570d2ec499466e1d9456c494a9997d43b1a5d8931a5d604b9c29d624c463532b0a569728c54ca78f92e6c49 (by decide +kernel)

private theorem part387 : Excludes 0xc0100000000000000000000000000000 0x13f6716c0100000000000000000000000 :=
  splitAt 1 98 0x13f6716c0100000000000000000000000 part389 part388 (by decide +kernel)

private theorem part385 : Excludes 0xc0100000000000000000000000000000 0x13f6706c0100000000000000000000000 :=
  splitAt 1 108 0x13f6706c0100000000000000000000000 part387 part386 (by decide +kernel)

private theorem part383 : Excludes 0xc0100000000000000000000000000000 0x13f6506c0100000000000000000000000 :=
  splitAt 1 113 0x13f6506c0100000000000000000000000 part385 part384 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part392 : Excludes 0x40d00000000000000000000000000000 0x1bf2f547dd00000000000000000000000 :=
  finishCode 49 0x358d2338de34080031c173286c50ef1f48d99c4d1a78f52eca5969aa99434e69b05caa8ae21de33f8a6c35a69b390c8319c96950db8ada76c49338a10e2b831ea4152eb8ae295b4ed4cb286d8725853c4a905244814caba34eda572904cea69d088c81d518b0f5486e2d520c123624a92564b18ccd3ad2d3accd2d33f82e524716c3913419a4520056b8b527f21954ba78f696ca4178fa19548eba1a0cd372994d3a9c063e5a5b4ed4ca69b532cd3b5a1a0521000d3ae892f4ab84de716bc7c53631b9c5af1f532c0b15016960b19c5a69148d9e3dc5b299634d89bd2af25ad69678f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part393 : Excludes 0x40900000000000000000000000000000 0x1bf6b1464900000000000000000000000 :=
  finishCode 155 0x19c5d19025cab0902a869d691a06f1053031d87b118c17678994ca6714a1cd3b42d9a6d0ff34ed4cad23780bb338cc35532a46d0e20c7348cf1f6249a6d54524cf1f34d99d6532b48c62f00c7532c96762499fc17a74988e2663341784b4c471495a54d89328748e2a6550cca554b4bc7d0e256d984a69b532a407c1b095792d6b4b987ea331c8a05cd2a9533389b0c4929dcd2f4a1a0be697b894af269514d99e65a58a6d25ef1f601b8521686814c440d2eb01a1d2e70a1dc5aa5b1519e3c89b1a35c5a47106399c6532b4ec18e78f441903d1a44b999e545b1e3d4ca879151ca45532c463061a5ce52f9a0d4cac4943cc95761aad2d4ca78f4f12db312431e54369da5cd45aa59690a05e084570c9eaa19fe4b69a6d45325cd05ec3d715cf1f624a5ccd3725b54cb3c7d8924634b9a90670eb4ed2e6a5d9a76973327a80d031878f6912af30f418e691987a66b532cc21335b1882590f2915204a97d2e682f3279a35e3f34ec88ec3f43b99ae532b4ed2aeb0299669d830d69678f4b99a6e063a408027078f550f8338bc7e4b5b0f6716b4ee41794eda5696b4a1cf1f69da59d384b9c19b321cc3d151a995a76c493e1244b9ca6513ac64352dce1f2c2a92488ec23716aa0bc2a8ae368691495c97369da99418e92b9a76b0150e624a5cd8932996624c103085a5cda76a6557178520cea6915a5ce2d238831e69db4ee4b9950e624a5cd78490c81c89a0cd227c312484f190cca2a653c7cf1f7169e3e321a995c5a8024068d8f1eba1a358933c7dc5a6436969de4c8738b5383a1904b9b4b6432a97522ed3b04cc917716a9750f32e87a029e6969de58931e15c5ad2d624c6433a2b8b5604e14cb34ecf1e97369dca656999e3de3f2d2dc5aa65 (by decide +kernel)

private theorem part391 : Excludes 0x40900000000000000000000000000000 0x1bf2b1464900000000000000000000000 :=
  splitAt 1 118 0x1bf2b1464900000000000000000000000 part393 part392 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part396 : Excludes 0x60100000000800000000000000000000 0x19fa34d601280a0000804031804000000 :=
  finishCode 27 0x721b46318450ccb4b34e926496ea82f00c59e3e69d5329274d3b25cda5b031418ec812650b712e589269d5a5cc496c1206412e71a6c90a78f34e92163c089150ca78f25cb4b652eb124d3667f610d3abe219d433191d46287705b991e518c647690972d1d888e40970fa5752c2c49061a9964ae9a6d696683 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part398 : Excludes 0x60100000000004000000000000000000 0x19fa14c74900940500004000100c60100 :=
  finishCode 69 0xe21a89238b4cc4314ca9e24ae348a5cde3ea4552cae8c499e3e85b4b492e418725cde3e47b31cca19696a5a4cc6ae24096998426633c791edb4136cf1f52eb0950fe409942a0ad78fa1fe521b1252d2e4307652ea5ccd3a48504cc47b25cb60ec248742c0c218d3647b33a92e52e67c318a65063c66334892c5e3f21c583ad3b5718933c7ccb2871896f19d5a7725c4972c6368ae031554522ca6534db4b63b8a85e5a0b4b587a1b934dca2f8ea2c3734eb089e02be2589a75b4624c0a5495b1050fe1b9223c209323806da76f1f417a994ea2565948ac4978fa995c848174580d3a4999872c3769d92c4f1ed3b896278f896ec202de62492c496ea8140ec3c7d4ca62590e2137697a5ccc37012587ad2f696c29b624bc7c883296de3ed2d4b9c1a3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part399 : Excludes 0x60100000000000000000000000000000 0x19fa14c60100804000000000000000000 :=
  finishCode 111 0x82390881261b05a5ac0ec2904b9338cd2d3c7a5cc95a9738d3a69d927e4ad3c7a54e6958dee78f865d78401b44a98a0678fa4bc32e4b1140c1a7497bc7cc4b0dac34e93f71092c450249992d287f34e9e3e060829dc422815a592e5a0721b45e18c61018303149624b75415c24eb8857d063cb4b710a994c36d294b4ad3e436b4ed2ae91b3c7869e4b9b4ed2ae91b220ca5b7119e3c18ac2268a81265d8711b04b49b84b961ecb4b61fa54e61e9a75c432d2d89287161cc973694b0fcaf2625984e08b4b495e4f1f25cdc46c1c5a77d92d24b942fcc4961bcc3f34eb88ec360c812e4d3b31250b6b4b849ac495aaa5a50e33125893309c11678f42dc9736249e3cd3aac2e8e21a754cb12e5a77299569678f431486716964a33c7c77d69dca653c7ca455a5a996624a10cf1ed3194caa17426831cf1e973601246c10ef1e3cd364b95e148187c92f08db4ed4ca19748dc0b734eca6534ec87705b866569734ed27e69d25caf04b95216c060868dc3f0a450b697398920b1989278f4b9b0ee4b9ad2cf1eec2c0743389730c7cc4924792e491f19d52c319d4d1a922b8a65438cc49223bc7ccb2c49888ef1f695b4ee5a5bc7c91ec62b869d929a76d516b09453669b39142f20c5a5ea59611b125842a5d945a96960ec69d (by decide +kernel)

private theorem part397 : Excludes 0x60100000000000000000000000000000 0x19fa14c60100800000000000000000000 :=
  splitAt 1 74 0x19fa14c60100800000000000000000000 part399 part398 (by decide +kernel)

private theorem part395 : Excludes 0x60100000000000000000000000000000 0x19fa14c60100000000000000000000000 :=
  splitAt 1 83 0x19fa14c60100000000000000000000000 part397 part396 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part401 : Excludes 0x40180000000000000000000000000000 0x1bfa585501e0000000000000000000000 :=
  finishCode 83 0x1ac481584f1b434eb18bc3004b125bb4ee716a8b4f1ea179c4291769d9695345712e728b49465a594cb0305c3b2205a76a5b24cb705a550bc48552da2052d734ecf1eda2b8c62904b705fcb4b34a928d2e722064b9a45cf1e68734a9265c5b12c51029692d2b28c016951031e3c6f718e4cbed3b890a9696114c6d13448bc78f440928cb4ac4348ec031497338b522e695532c78f532c9178d1288148bc65f25c92151025a53bec4b950c99e4f0278f5329265433368c2169606292c496ea81f049d7114caa459e3ea5b31ca91678fa96ca573c7c34ea625ccf82d2940b4b319ca5b5248d9428614f522cf1f50ec6331b284eda5ef1f062cd816949371a5d2e6197969696933d98e5b865180440af0695832e1a769dc9735a59e3c9732e878d94ca1a75a59e3c972953834ea656c10025ca59e69da994f1e4893b8ce2d532a0096b8f1ea65813e78d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part403 : Excludes 0x40120000000000000000000000000000 0x1bfa96451124800000000000000000000 :=
  finishCode 113 0x94328822408816b1c8610d3abc3184b1816e4b75a0c7b245d06e4993439a5d86f259cf1e86d9e3e6955a59e3cf1f02c63c7865e0d382c4f1ea8390d625ce32e9274962a4360ec069d2c624cf1f4b9a994cba871244c5a19e3ec49524865e624bc7d2372d2d2e6a4065e0d1a5ce6112e712dde3f2d2d2e6e42f0c62a086d834ed3b4aba46cf1e489258b08c3d9a7667b78f830496eec1e3da5f3c7d2e674994b678909db4bde3eb4b611d8611c69d6249264cd668734ec64f90fe1a7532b4ecf1e69d5014cb3c7cd0eb4b3c79a5e4b9b4cda76b4b501004b9c1a378f9e3d480cbc1a3624c97334bc67b060b40e42b878f96964b724caa078f9a76a6569292c52e71e3d696d3b5008f71a554ca78f151cb2f62191ed8926955a5898e481c83a1846313c5e0d3a78f89624b76f18470e74f1e67b621cf1f320b08cf1ec4953283063c799ec962a65893297334b9e3da761a7969e973532b4ecf1e69d0d3c78f5329a7496ea431264b99a245466950d19e3e4b9b90c234be060a5cc9624b76c1603a1504b99401a794ca10b834eb6258760e76516a455a5a7453ba84ee78fb4be78fb1240a3295429ed2f09dbc7c8c734bd86ad2d78f869ca0696cc1b4389905a5ef1f532b12678f950e09dbc7d4ca0c18346973 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part404 : Excludes 0x40100000000000000000000000000000 0x1bfab0440100000000000000000000000 :=
  finishCode 59 0x3281e15f164630b4ad02f04a35010ef21e48c619734dae8a65095c97334ea196532c97332392152049090a4638d3a8655328e86346bc7d0ce69d49ca1de49ca5c474269b624a1de34e91ec91ec22408818f1e485681c86c095a8818cfea6534dbc7e532a996716a2054564b9695c2a3346ad2d102ce310ec3609012e54cb2204d3a88194929697169a6d20514ca654b39a74a872995e3e881440ca653baca65696a5a51027899c86d1845309467798cc668d43ba1e510268d9696d83b0c42f04b933fce2d24e9d565aab4b4cc696934dc881893a197925ef1f4409274d3a8818f1e647331a20625c91ee (by decide +kernel)

private theorem part402 : Excludes 0x40100000000000000000000000000000 0x1bfa90440100000000000000000000000 :=
  splitAt 1 113 0x1bfa90440100000000000000000000000 part404 part403 (by decide +kernel)

private theorem part400 : Excludes 0x40100000000000000000000000000000 0x1bfa10440100000000000000000000000 :=
  splitAt 1 115 0x1bfa10440100000000000000000000000 part402 part401 (by decide +kernel)

private theorem part394 : Excludes 0x40100000000000000000000000000000 0x19fa10440100000000000000000000000 :=
  splitAt 1 125 0x19fa10440100000000000000000000000 part400 part395 (by decide +kernel)

private theorem part390 : Excludes 0x40100000000000000000000000000000 0x19f210440100000000000000000000000 :=
  splitAt 1 119 0x19f210440100000000000000000000000 part394 part391 (by decide +kernel)

private theorem part382 : Excludes 0x40100000000000000000000000000000 0x11f210440100000000000000000000000 :=
  splitAt 1 127 0x11f210440100000000000000000000000 part390 part383 (by decide +kernel)

private theorem part380 : Excludes 0x40100000000000000000000000000000 0x11f010440100000000000000000000000 :=
  splitAt 1 117 0x11f010440100000000000000000000000 part382 part381 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part408 : Excludes 0x40005000000100000000000000000000 0x195f72780c45015500014110440005000 :=
  finishCode 61 0x1243e1e4532b98f63e8b207859425bc72149a9584b4aa429465aaa5c507ea4924ca98e2b09c85492d3b94be82d4b49a753c6308ff38b5a76849624a5a4b3a49d6104cf3124ac257903cc69d6249f8ba30896940bc4b743fcd3b624b87d49ae2d896ee2d896ecc358a639a7696b62492dcd3aa4312615182d63c6b8b5a762a394a2d3b6b094f1664d3ac238b669d9e350ff308b23305a583624b7512c5a5526828da764935c0ec3c2c42b2a1a8745224ad69da97d67b38b56ab219d2d29698b4aa6348dcd3b6410069dac896b631ac244a97e716a46cb4ae2d94bec4984ef38b52360b59c56a5f71692642af122463e91b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part409 : Excludes 0x40005000000000000000000000000000 0x195f52500444105500000000000000000 :=
  finishCode 117 0x180581703c796070358b575d092712dcd3ae612ddc424cb125a77218da7729150aaa5b8f1a4994903c334ed466389321828d4ca7813c6bd8a438eda8650c5b4ec3c22a38edad63106420a98da769176249264d3a4ad59016ab559892761052878669db30d62c8499081c517532b12496e9e3d869d311c85530aca63698ca2521da5a549ae62d892278f60a8d45f25a58921e1614c78d4b4cc49532b1260f08a8c3c30656054a994f1aa1d8a1618b532b58e63c89e38869d50cce2d43c878542f312494ed3b522a155ec7d1540f08f07e2e8a631a1cd3b41d988e53284fda764196248006620942c876643532b4ecf132994c86a63311ca651a1b4ecc867e217e620a98d892e217092112bb8b50832995a3a623420c6199082c413f14c731246b7217cb4ae2d530f47b149ac498b4a879216c493528b1253459071b28952e2a436249694f0b10dc71ad31512cb221e5883296d0caa43624acf621da194c46a438d3a493731ec4f03c2a4585468419c5625769db8b58929e3126151b12622db8ac10b2c8c21604b134ecd3b5aba78a650b7cf1f614b8b4d3ae221d652696954c71685452b578d3a49d381845abbc8cc1a75c5b2994a2ef1f256b88a65215c3c1526b8b4b4328a54ab09dde3e4ad528c69d532bc7da7738b52a6f1f256ad5e (by decide +kernel)

private theorem part407 : Excludes 0x40005000000000000000000000000000 0x195f52500444005500000000000000000 :=
  splitAt 1 80 0x195f52500444005500000000000000000 part409 part408 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part411 : Excludes 0x40001004000000000000000000000000 0x11df541c0454000540401004000000000 :=
  finishCode 119 0x1f47118006d8b5540530f1ed3b8d2a7819a76a65614c6954b3a4ada6665d69dcb57481402c0f1eb234ed4b7215454668934abc8d3396ae69d41dca655212c4f0d2a8558d3ac3f9a664ad43bca65148acd612ca1e5102a65521bc4b148b34cd89287134a9a26624a99624ea99669dae070178a0306e522bc7c93a8815aba50689989234324ea204d81cec313438a96cb2214f091c54343cca6524ea2056aefe278c21e1660d92b52c60da1c678fb0b4ed328bca8734cde3e29d8ed269722184699a1e61488d0cd122619e3e6233a4a96c686c23c7d0e31a54522239948a4516b1205d13c500d3ad21e3d5c4d0b52a5d927e879242a206258cd2d592a8943724b1922ea3144092b58424e9216699a194a2f25ad892c0280581e3c3731894ea2a4d48bb4ed6aea4116622da105102a652d0828d08322054ca83b2d09e8a4293502f12c587ea65699828d4cb205d442a659a668174a9a205a7722056ae4b78e04a150440b7849d43185b2d5d4b65659a5a87796af368f1f5abb0fe69986e496e9e34cd2d311650ca77d43c95963b0845db45918478fcc4925892dd906249276438bc7e698c57d52ea0dc546f1f5014c2a1bc7d89302754bb159589321e585ac312a18d0d205aba205743c7a91641d828c133116d0bf0a8d892f1f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part414 : Excludes 0x60001000100000000000000000000000 0x197b5e1550d6010100c70001000100000 :=
  finishCode 129 0x120501ac3c7a78e6129cd3ad3b9892879516cd3b1bda507c38b6532b4ed69636b3d12d338b4c36c4152eb4ed49a44588b2d3b33174532b381b99c5ad3b624a5a48533105a76e2d30db8ae694986dc5ad319462419715a17c8b292290a22588a27872025c6a334ec11ac413a8a17c11b25a4ec3217dc564598ea228b624a91e5328a2dc570a2d892c279696d3b624a915a4f2d2c546a412c1a869dbb0a4d8296e2d253a1fc6f6a656999903698b4296928b9a7429636b253ce2d34e96864389a75a66d42d2d3c6b093b1a7524716b896624a5a54ca5a9989248943fc0691b5b8b54ca69d8b429e308bc350e62a02a37b109a4a722dc86d433ad246f709b528460f41bda07e518bc7d0aa9359e3e623716a97542aa5d904ac495a5bc7c8b32155a66f1f716aa0ba129d0e311ad0fea2f4b4825e716a508c1b837b142ce2d516a535482a5d571e3eb3192d2a455a6b4b6518851e412ad2de3e13f9a66f1f4a6c459624b8b504af1f699929d283316968539892a1943fb49d4caf1f9892a5d43fa996520825d892d27490dc5409443fb88c49424988e4b48ded48e26192d32c95a42a19523895e696916c6caa5d41bbd8a31986287150ca50d398632d2d24eb4ce78fb8b546205986d6543244a8c500370b84710da82559ace2d22dbc7e716a8060290678f916652eae837b8b4287f616c00f7169f094350b4b1b1ca6559ac87108ec11128980c5c5aa65616b1264b4b8b5e3e7c04fe52391654ca37b37114523ce1d222b8ac8b2a4150ac4594b4cb35 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part415 : Excludes 0x40001000100000000000000000000000 0x135b1e115054010100450001000100000 :=
  finishCode 53 0x1c47b05aae61e3e06d87854c52dcc471a0a91cf1e96934b9e8a6569dc78f32e99e5743c7cd3b13ba90e69d8964c46b234ce716a994d122a334aa9963368a8d84451645a5cd3b3c7a994cf66896a0cdad3b8f1ea650a9c15f289acd505269d6999e3d204017c3c7a30a6534ac2912a19a56699b4ee699a90b22a8695624c29d50cc69d624b4ec523299669dbc7e6998a44d2aa025878f5913c3818630255e3ea4552db11e41ba16ccbaa2f78fad2e414bc7c6c665d5b1e3ed6150e1bd9145c4e85b3baa5161bdca6562395f4e931c744c2f1f517b50b4b948a54369db4cd4ca06f9c4a15f69da96cafad33 (by decide +kernel)

private theorem part413 : Excludes 0x40001000100000000000000000000000 0x115b1e115054010100450001000100000 :=
  splitAt 1 125 0x115b1e115054010100450001000100000 part415 part414 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part416 : Excludes 0x40001000000000000000000000000000 0x115b14104144000100000000000000000 :=
  finishCode 157 0xfa16adc47b05aae6036e0f0a987027888152dc6974b4a8b54cb38b4c66a294b4b080af8d2aa2f8a86e2d621a5a5c3e87f611a76a65497ca5f3c098e6497a8fd944a164440a4be716b1245466954a1ce2d61a8dec546aa278c60a8d4bf3895c5ad3b05a8e26716b125a773125c5a38933dca65716b4ecd2a6038b6532a924f1b34d54cae2d3e12826184440ad2dbc532c689249c96b9236a65591bc611103312452268934aa78c6296e24ea99670fcc49440a994cba49394ca19d34e842e49f8deda6688152184590d130a458926956a13c34ec291336c0b5699c871256a4accda6e25885b94ca87f130c849517944e34e9da4f0aa65532cb634ed184f12c497950c50a8718eea87f130ca2f2d0cb3543f82d4d2a54361125e641816a13b34ab4b6007b10cc8213b438a1e661a9275102d6368c62c8ec124c962c0320881526a4be41d9855c5ab4b532a1fd69715f589295394ca8814a9cd3b12695f5102ca208c2220587f2995a66b4b256a409439a76e2d5a5a54d0ff2995c5ad334978ded847b12a730c4d3a0b70dca905498d3aa65256b8b65289a75ec2b14a31a75682d314b4b8b6497b4c5c4a57d42dcb4b34e8dd5484f095aa3b9062d2d532b8b528669d438c92f716a5acc4696934ecb4b716b20c01a75485319f085f94424995a5a4fda7722064b5c8815a5b4ecfc43cc499624a944cc1bcc88122da994f849fcb4b440c61560f9f0d42f8c829958034e9900b7618c81d1bd98e56968818c36c498a22b4150bb0fc6f69c3d881d8aca385432a46e7168e16696ad2d205a5c9534b3991e4408decc84b3a98b4b2e1102c31925ee2d289a4be30c82cdc5ac31989235961f8d4da5b296d10292f2a1c92f69d950b4b440a7893f151cc49716922590532ad3643f8dee30cb8b50ff2995c3e0a5 (by decide +kernel)

private theorem part412 : Excludes 0x40001000000000000000000000000000 0x115b14104044000100000000000000000 :=
  splitAt 1 92 0x115b14104044000100000000000000000 part416 part413 (by decide +kernel)

private theorem part410 : Excludes 0x40001000000000000000000000000000 0x115b14100044000100000000000000000 :=
  splitAt 1 98 0x115b14100044000100000000000000000 part412 part411 (by decide +kernel)

private theorem part406 : Excludes 0x40001000000000000000000000000000 0x115b10100044000100000000000000000 :=
  splitAt 1 110 0x115b10100044000100000000000000000 part410 part407 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part420 : Excludes 0x40014000010000000000000000000000 0x197f4bc1c541154050114400140000100 :=
  finishCode 39 0x220d01e1d945abb48e21a74176e61a3634896961adb8b5a5b116c536b61a6d0db34bd4ca78943898f614dc82934eb8869d624c6910f08a561adb4ed3c3b17423f94ee69799d4d3ae23981d19a5ea6533a969653294ee697b88ba33869d419c50b2ceb4bd89276d0da94ee697b87621d990c3c25a529dc69d697be8aa388c498d221d532a8a5661ea945892d2f33ac5a569794eda76871624cc2169da995a5e871 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part422 : Excludes 0x40014000000000100000000000000000 0x197d49d1e470155010000001105000440 :=
  finishCode 119 0xba278f61a75d46d1a47115c0f092e4d1b214da5b3105892655450f423f9f8ae2935a5f050d0f2e239a5aa51510c591696cc1d2d482ee696a04cb2247f83c312e49732f8ce299662482ecb4a0b14b0cc4934d96958833125ec751b4711700f092e42bb3884ae2c37311a0dc336655571882d3b8cced21033c62341b851d4cacc348b62b88a0a6d86f190d06e5712ca82ee2d0a0dd9470ec05542db0b42bb349506e2059a5e51f61d82ecb1229b31ec87165114409cc2d70f9d64f12a219c3b34bce6a5a10f0c4b925ccaa2e0d21a358833125a761a9348cbe34ee09394ed8461a922dcc49620a1160da9695ec6d1a4751c43b03c278194ca5a523fa5265329d74b4aa82b0aa2b8b81380990cda8de321845da5ea2959a990e08bb4bd45245b4f11404ba52653291fcb0b0d6e611b49504ac2d23ace2151bb11d026585532888e69d916d892c2d0cda8de62491fd5c3214c73495082c494613c183cd3b52fa1e420734eca3e1139a76c3b8e6ac476515c4f0d1a4758eda85369da1e5a3b24f58928252d2a1164b6969422f2955a7647532ab4963a2b4bc3361e123f9a6e0f0af8821694ccf34ed08a78d3b09df67311c320d1a683124e83298c44f3474c8653b69cc8213a0990d476d3b22d882e531b87da6ac4969d91fe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part423 : Excludes 0x40014000000000000000000000000000 0x197d49404450154100000000000000000 :=
  finishCode 47 0x1d07825cd704516ae7870b3c18725ca1e430f2154d361e15d1c47b1cc25c91fe34e8784d3b2b076d851e45b5329a742eed3b400a3f05acebb307452ac49532a5869d4a6cc4114da536620b125ec751a44513469da1e524400b4b02042eed3198460892d2a99529325748b729942d721543c216b88fe8799a6b308c6b65a553285dda76e2d641a5f2d5c31e4b969d92e6697861d6aec829078760ec29b34e92e431e19b6309720bb820ea655ab9a344f72d5d892e2d620be8b5725cca21422a5b4d365a50f0b076042b4ac30e4b9 (by decide +kernel)

private theorem part421 : Excludes 0x40014000000000000000000000000000 0x197d49404450154000000000000000000 :=
  splitAt 1 68 0x197d49404450154000000000000000000 part423 part422 (by decide +kernel)

private theorem part419 : Excludes 0x40014000000000000000000000000000 0x197d49404440154000000000000000000 :=
  splitAt 1 88 0x197d49404440154000000000000000000 part421 part420 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part426 : Excludes 0x48010100000000000000000000000000 0x197be5075482549010100000000000000 :=
  finishCode 57 0x531045c158440b588e1a758c338ca652d29a3583b299587a95161b9896716a13452ad3b5a17c7d014a463983a787327a135a7696d22ccc1d623a99509a973618cd3b3c3a13452a9738f0f220ac25cd2869d8dee5a5a7829588b669d716ca6522d947dac28fce1d531b125c5a4632d2b106532b8b53c1e04ff2994a76d3b5d04ff0a54d3a9a147e13f8ded85ab4b8f1a52f9696a65333a86d585d17034eab8d359c5a6332d29a348b700cd4cac4969db104b4ac3d29ac66769da1b54ae9a311e4b9903431ed3569da8ad6969492d2b4d63199df5892b8180787526c3274b99696346a4f6716b49504a5a54b9ab07879696d3b4b9a994d3a762994d3725cccce51f864e69b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part427 : Excludes 0x40010100000000000000000000000000 0x11fb85015400541010100000000000000 :=
  finishCode 119 0x3f8fa378ca078510440a109735d06f61670b5988e28fa89583ac4128fcc419892a2528fb4edac5d169734ec53637b34ea10640deda4b20954ca14769dad2ca4734ecb0b2d2e56174570d3ac61f85718b12a5f98765955a5c46369da5cd86e623989285b61e918da76682936624a98d102c2c64f624a5cda6b20bd46e585624aa02398a3e16b4b99e1cfc4b9a98e620b125883188d082ba390b01a752e738b50f278725cb8b63389695a567875812825c9e1e5a5863cb4b31258932204f0eca2988816951027419065a5b4ed2e66919c5a64143bc02d0c7a0c5696d4348ac21dd893063d893299588ec49988ea650b3c7874b9a9865598927875318546096b4c52e2e2338ca12e5044f0f0e88129dc6717169a748b30a6d544b4c66334686e64f0f0f1a75c5b34ecf0ea655c158540d3a85b8536787436a86e440a0dd943c3a1e634da5cdc5a881624c65569dc82f41ba1b4d3a85b94cab4b1b0a5cda76c4134ea205ac5614c34eb28822208811bdcd3b4b994ee69d8deda77193c84ac3d532b8b46fac492d2ac08c21de23189fd69734ed2e682f811ed2f29d918c6f67874514cab4b9a76973327a1e52db180a61e1d2e62598b4aa65716a2049732994f43c3a28e221e44ab38b58725a561cc51f8b4ac3925ccc395d0537220497288192da877 (by decide +kernel)

private theorem part425 : Excludes 0x40010100000000000000000000000000 0x117b85015400541010100000000000000 :=
  splitAt 1 123 0x117b85015400541010100000000000000 part427 part426 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part429 : Excludes 0x40010000100000000000000000000000 0x117d0f145410101001440010000100000 :=
  finishCode 145 0x711f47b05aae612e54823187852cb3125c4a461532b4ed0ee69743bc9c220b4b9a766874b99b847f82d2179520a974a472d2cd2e47f518cd3b3c6b0ed4cab222064f92e66794917c2d14ca4639482c4952e999d14412c47f624a9744ff312574438c66743fb12471253b9a7637b624b9069714ac37b69db89e2218484506a5d126999e532a5b5ec4f09729c1a75a423fa5cd29b2995872879333cc3f53291fe5a5a70b42b88c0a6c88b310549ab4b1bda97641b851d2e6c498422c4152ead2ca76d3b4b9a8de620b0e50db30fd4ca88270e425cd08641ac69d999e5189a7589328c54cae2d1bdb07652e8ded83b299569629569db0f6333b12412e1b54910932905882667532b4b630a9a7584ec41721ac333c29550d9a7589311fc6f6b4b518ce25520b08c6c6b4b05fa99538441584b9a58d3b671f4532c1675a5a1e4d3a66b343ad366209894d3a37b9696c3934ead2e0b99a746f68555d1844b1a460ec69514d9e8a6562089c6343b0f6712a1fd87e8a204e59eb07da5ac3d43ca0de60fb4b417ec41989251f14db07e62498f417e84343c9a1d584a1ac421741bdab869d7d05366518d2e45b9a7661941b82fe0a3ad2d0fed3b291cd3b5a59a2526b311d04a0bf5a59614d3ab4b93c570d3a5239a76c49138b104536c498d2e1270a194eda765239a7629b67130532cc416249a25a45712c7f0536c47904aa6331e91fc8c711854caa37800214729d95b504a5a905f94ee616ca6518594ed0831484442c23620b12558541a76d629959c45130424cc1d30c9a74cda7a02fd0531a1d87b21fc17f21b6620ad2d87e69d21dc459699ad2d6973086e3388a118e05f91fcd12d216864a282fc60f00e4d0ec41230cc1f5329944d2f11fd4caa659892c41 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part430 : Excludes 0x40010000000000000000000000000000 0x117905104500100000000000000000000 :=
  finishCode 115 0x1c42d5be8fe0b55900f0ac87874518930a54d2e0b198926718f0319e4d068815aba604b913fcc493c3a1de532a205ec6711025c9e1e5abb288e2f868d3b6c47f532b89629db1248fe69194ca475440ba8de1f8921625663195569ae1f983aa65905f195487e38590dad2d23ab20a82a87874e0e461bc92142da8854ca655338ab847f311c69b624a0bd4cb34b56c37143645994ca81352ea206512a99544b2995a6314d505ee1f532b1248fe8818084b9c5a68d4b99a365aba07e62499554c5ab822671691fd1028658cea47f64110410f0eb57906ed2d34da2041732a88e02d6624998cd1ae259a5a29513f9a4510247f9892a62d5ca7730dd456a5d440a8c652e999cd0688160822d5d50440ab87875b053668790e2a23696a1b5c4b1a1d4ca63d41dcc3d43fb07641ba1e5a5e9735412c3c398964928a6c8fe68723fc0bf05fc88192e678765104691102d62d8be2a80bf4a2cc493c2b08ced229b9892aa218c1d8b22c4129dcd2f696c571290cc4162482fda5ec499a5e22705a8a6ca7734bda46614cb30dd8920bf7f13c510b086417b8848fee2188af1a5d0f2e21420b084f12fe34bd4ca50b8ada8253c4c46167144325c48fe68934ba1066989cd4ae2c49 (by decide +kernel)

private theorem part428 : Excludes 0x40010000000000000000000000000000 0x117905104400100000000000000000000 :=
  splitAt 1 92 0x117905104400100000000000000000000 part430 part429 (by decide +kernel)

private theorem part424 : Excludes 0x40010000000000000000000000000000 0x117905004400100000000000000000000 :=
  splitAt 1 104 0x117905004400100000000000000000000 part428 part425 (by decide +kernel)

private theorem part418 : Excludes 0x40010000000000000000000000000000 0x117901004400100000000000000000000 :=
  splitAt 1 110 0x117901004400100000000000000000000 part424 part419 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part434 : Excludes 0x40020120000000000000000000000000 0x13db93a17820c55820924800000000000 :=
  finishCode 145 0xb82a0882b07873e1405804d2cc29943165898d3ac4978fcf1f9a76a654f1696813984a38d5329a748451fc64f69dca49052c97378fb4eccc3e13c532ad89a0a455c125c9394b9c849624b09e624a15678fca2560e980a23b0cc25cc537123d8926419a5eae3c7d08730fd4aad2b8a56a378c9ef1f528b1252e629b987e48f571bc4b187f045c24e97378f8a6d2e73c7d8929719892175510c97378fb0ecf8721696f2278d41a756c046ca656148a7549b31254c618f98928c33046394cad3b1b5863cf078f9cd6598a9354a2e1f231a9965269685883083569ed2f78fb30a65989248f532cf1f67031e585963eb176248a8d09330d5c87913c5b0d3ac29853a623865a18f624b4ed852a2330ba188e69d863d0e229b3d1e3f295546ea4d51fcae298e2d0bc7e69da0a678fb12549ab3139ab308718e6a38d624923d4c702a55c3d05460a978fca635a4a096088acdd892d31438cb17624a88431eac1f074230f1f5a5a5cda76cc3f8a259a5e48f697c23d90aaa4d697a94549b123da5e882d2d54134b38c499e3e5a160e918c522d2f983af1f9a5efe3c7d5c4d14a334bc91ec418c46013528b125a5e8139a5ea4d697ca4d94a248f2a1b4bd2e6f1f69db106528b125a5e48f78fab0ec2d2d104f18922574b9b4ee2a18a15a5aa6586f6e4118e58b950d4ca35369db5027f871a2a35328d4e5a38dae12bb4ec8c30046624b624cc1d61ca994a76f1f4b9a0de61eb105892a81807825cd83b2c5de3e16b14dcc1d624b0ede3e78278a63983aa6542aa1e4c9f312544216b60eca63624b1054430cac2ce973 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part436 : Excludes 0x40024100000000000000000000000000 0x13d7d3c35c40d64124100000000000000 :=
  finishCode 55 0x1505c130480f0eac1d0f1f92e6d3b590316a21814269d8536f1f3316c532a7839d946e871697986d862973148a04e3baa5cde3ea4d9842b6258e258ef25a15199e14ed318f453aa63989248f5712e6a558546a6578f82844df1dd4546f1f532998ae1a75a5aa654b1273288505239d4b9c53b78fa075a573105e3ec235804df188ca76a2d2478a6d2e6cc1c8fe0a6c8baa198d3aa4d34ecf1f9836a4d14d89be526942de3e69d695bc89735d120550d3ab6296e3b49e1453ac498116c2710fcd2d52c840c2d6a45671fc14ea96661e98f473ac23943285552cb12508721e54b2c49516a99544b1c754cac3d516a536613a98d45a29b148a5ce (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part439 : Excludes 0x42820100000000000000000000000000 0x1bd797ab98ecc46820100000000000000 :=
  finishCode 39 0x150441704c1603c3b10bc2a8a2f86ca77552d82ad2e72995a7729952e6f1f94ca0a10c1b4ee532b12588512ce2b0d0a98d696a654b9918e51ba9944c6f1f69d9989733214cad3b82eea25624ad2c2ef150e69d8dec522ba2a8bc2e07c02ac6c72895892b4b0cec76551ba1fd8928499892d3b0d0a995696b4b815f31254ca87f69dcf1f5a5a85cf83a0ecb1e2588e0af1bdb0886594520af1b6cc31130c4631b682bda76f1f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part440 : Excludes 0x40820100000000000000000000000000 0x13f397831824c44820100000000000000 :=
  finishCode 123 0x721744f17034eaa0c41e1dd85712e6b61d5653282b58930a6d0cea65151ca6561eab8a202be137a90c136a5f624bc7c5368679e3e5919c5626f522bc7d892c3d695c52b697bc7d88300c878fa5cd69734bd2c1879d2670f988d87ac3132789be311a96d8461ac85531082b583734b5696d2f522a587758f0ac492318a7652ca96d892867987aa655a58ded2e6b62a89a2289598eb27895a4c775371784acad0f1f90fe64f055993e51f9d95c5729246130c656927654a8bb0802b887f62106e595327cd2b51f82bcc7b3c7dc3f2d2da76c49327b0f5e3ee2b987ac3f69da994c9e60d845e24d0aea4554cac2314db11e78fa995876b355a49625684f0e43e1486aa2d2d6c61eca1769d8a7549b31254c6c2d987aa1769da994780baca25429b895886d2f61da85da76663c7d42e6e118e1b68966310b08d692c439c4e82531e96148c68c285d0ef16150f2c438b0aa81407c2c5e624a8fda76a375a5993d4ca882cd6611993cf0ed2230a3751fc91561185763119d1522a825697bc7e69db10880dee3c3b4ed2e6d22d2e51bad2e69da8fde3f34ecf0e8c2a874118d66b18f5c3ed3b4b9993e623841648ab11ce8ac2351dce1d69d98f5e3eb02d8aa1e1e51b8a74ec6249e1e69d816d47e62361a916ce8ac23922a787327916d6972995a76a4d310cd3b697ad2d892b0220b802860529e1d3c4b9a9964b2b08412e29d4a8c45b4f19c51169629d58bcf1f512b124b52c498ef3312415aa2198930d8d696787 (by decide +kernel)

private theorem part438 : Excludes 0x40820100000000000000000000000000 0x13d397831824c44820100000000000000 :=
  splitAt 1 121 0x13d397831824c44820100000000000000 part440 part439 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part441 : Excludes 0x40020100000000000000000000000000 0x11db97031800c44020100000000000000 :=
  finishCode 135 0x1d8440a20a825cd2433100532ab016b61ec9653c28a0cb4236369d8a6e03eb125882b427837b148c86560ec841989229169da589a278ac2280935e0112c3d984a87f2a198850ff21e504b34ed43225752ca28a5b987229b044892e14da15542ea595e0a83f184a63d969654369d8decc369218b425958a86d3b1bd916669d8cac536bc150e0bbb4ed696c3f624c64f40985ac8c6863124e461eca5952db8ae12a89b587f1c89e0f8b559a5aa4314eb08d87aac095e50cb0842e669d4b0c64f43cb0854b678998824634acb08d87aac240e430e640ea1e42e6d3b6b02e645b9872c41512a98c5070d8d844f0e7334b4b125a943c96263bca104c9e2578c4662390f2c415a1984f06f6c22d8ce0a461519e1652c89b50cf188e624b104a86c31522b0760b3c54369d98f661e993d03a543624b4ed69664390b4b421a76d31808a2a34aca1b5442b4f29da9946a608d962e543532970f1f98922a31a9b0f65328a8d63ef1f72078791a76ba2d869d438ca65623a1fd85b29945368296a118151c8255328ded69f2484c7ad314aca894546a6561eca1729d998c418a768411bda994a7721250b6ba2784519882b1f78f9a750ff0ded83a2a39e3e37b6a124597cf1f41b89fd0da29d532b10614ea589e2c5e78fad1cb5239d59bcf1f58bcf1f560c8660f05a58dac8b32994d3a17769dc50b8d3ab4b0bba995a76e2b853653b0bba99584e69d69da489e2b866228a650b5c53b432a58c279692c3114d94ee60e988584e59d624cf1f516b0e45367898af2a4560ea96583b0a6d4ca8620c6620b12661f94ec536865 (by decide +kernel)

private theorem part437 : Excludes 0x40020100000000000000000000000000 0x11d397031800c44020100000000000000 :=
  splitAt 1 119 0x11d397031800c44020100000000000000 part441 part438 (by decide +kernel)

private theorem part435 : Excludes 0x40020100000000000000000000000000 0x11d393031800c44020100000000000000 :=
  splitAt 1 110 0x11d393031800c44020100000000000000 part437 part436 (by decide +kernel)

private theorem part433 : Excludes 0x40020100000000000000000000000000 0x11d393011800c44020100000000000000 :=
  splitAt 1 101 0x11d393011800c44020100000000000000 part435 part434 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part444 : Excludes 0x48000120000000000000000000000000 0x195bf9a164824d9200124800000000000 :=
  finishCode 35 0xf22b0ec1a7560440546d3b8f0ee2d4b9a68c493b8ca1b3a0c7713a0cc3d624b4ec1aa787145ce2d3c3bb0b0368f1f8f0e0d5151aa0973570f0e74d8116f1f14ab8b6398b105a5ef1f532bc7e492c00b51099550daa6506a9e1cf0225c28b7169e1cea338b5882f1f14ab30b02688c123c52b05f4522c49946e091541892a3785222954b9cc3721db4eca6a291621c78714ab12491ed2f986ad3b78f8244f0e291 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part446 : Excludes 0x48000100100000000000000000000000 0x195bfb075412548002548100100100000 :=
  finishCode 65 0x761106b12e6923c8b6035527b30f5892e2d2d2a9944da2a3620ce2d3b8b0f58925a5532a105a338659623c87f0d88a4550716ca656248a558931695c5a37b5f02ef34ed8925a5532a1fe616cb1f624950d4ca2a38b4a0d5490546a578e8238932c986e14ab12440791a76b4f9e3ec476248de452a2a306aa3098338c498a862950d88a45a3b14d46e226d14abc7e14ac87178fbc8d62c5e59794ecd3a0d56a06f7216d4cab4b1c48a8d69710742fa87129d825d7c3e12853294ee5a5999e29d96954c7199cb4a2919a6a9490ac8a55586b174570d3abe0a5588328c54ca5a5623c921312b8b5436c4152e9696620af87c1df629d999cb4ad3b532999e2d298ce69da8c5696e2d189cc1d29d999da7636b531343b8ca657169695893307452a53b532a996 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part447 : Excludes 0x48000100000000000000000000000000 0x195bf1030502448000100000000000000 :=
  finishCode 127 0xdc298822208814c18c3c39c8ec19c5ac2a1c9736248354b4ac41987aa49057b124546d2f988e0af6b1f4624c5a54f0d1b0355a5aa579462a654905471e354caae309e6248a5584f213661ea925a76e2d60e8a8c1aad4318ae0a8e4b9bc7c91e68d348b58ba2996623912dc5a3792d29a75c5b16954cb0a8de3e9736b1e4716ca6569d8355a77299445b2995e3e4599842e257169a742a697369da68d60a8e6239a74ce24852d2b50be1a3583b311dc4ed3b532a5452da2a38ce278d988e09d69d881629d80a4f1a29569d9a6d1054130470f0eb219c5f40d8cc4934d9695404f0d362a394aee2d6139a754cb3c7da7729952e72994d360d5532c48f06a9695245d0d2229590be48f4369a750c492c5492479df649ca4de716b4ecd1a9711ba96944b269d3018834dc0d55a5bc7d2e668d81aaf1f6a0d1b1694d22a5d988eb4b3259695a8501d8346863e526ad2cb4a67178f835436b0024c36f1f532b0c4d3ab619c4efb1694d3aa6513cb12634e9215a7624f4d0d3b1df4b4a48f014cc433be9a75a8631004718453299fcd36b606c62989a74516a5f8e9ac493c3923c1ab1a74f0ed629964b9a5c41aa28b2478a8e5329a463c3923e06aa995ac480a772d3de3e97369d9214d3ac41e1cbc4b9918e5a5993c15f31263279dc64988e24f1aa8260921e1d8c50052b123cd2269b3914ca9499c5ac4933fac8d3b82165430d8b1254531524e9aa259862a630c5a994cff3c7cb4ac61a763489696532a5ce (by decide +kernel)

private theorem part445 : Excludes 0x48000100000000000000000000000000 0x195bf1030402448000100000000000000 :=
  splitAt 1 92 0x195bf1030402448000100000000000000 part447 part446 (by decide +kernel)

private theorem part443 : Excludes 0x48000100000000000000000000000000 0x195bf1010402448000100000000000000 :=
  splitAt 1 101 0x195bf1010402448000100000000000000 part445 part444 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part449 : Excludes 0x40400100000000000000000000000000 0x11f3fd414041440400100000000000000 :=
  finishCode 157 0x1fc7d1200f0b589e1e1e69da8b4d3a922f8662b8a65510d366674a8c7455a496852da7759692a31511045812da24d9846c3969da905c5b30fdc567899e3e93d3c4ca0210ae16869b78fca57333a95e0d6a68da28ae2319e25e3f095dc4ea2b4b4a565a6a9698e22d254ac98ce3c3918cf1295934d99c63c3a20b818ce34d9e1cccf2d2dc5a5958ef29695f0ef252d92b293d59bc7875c14055110519ce27137a99569668d3c389c63318a6d65ea6578fad2cd1ab558536877532ad2e3c3b30a5d8536b4b1b585de69daf078757122b28b415ea49346a68123948a26f515b4bd482c3994ca62b624b8ac4df026d48ea655a5ae0ca220821e08815d0f0ec62b80af805a6912478a6dc5b06e5e3f14ed4ca69d34dc48f49154610d227206e584338b5e3e67161cca4f69698964b4a96e716a8b5a7738b58c4c0e43c3ab8cc198cd1aa5d989273d94cac4194b666360fca2d34ebc7d4ca68d490ac34da1e63319d760dcb0767169a7583b1a75c5a8773c3a99634ea204f02d0c65569dad2c8b2a6534e9e1d983e15c14dcc494b4a99490a69d8caaa65312c48f612b4edc5a69d8785d1a769e22069d60eca174b4a96c2ee36b8a76b4b3f1882ae285633394bcc3696914d85de29d88f4c36a5d4b4a97661ea78a5d90f2e2d516999e5a7a855482bc31836b45174420ce2b0dc986d4bac4134ea1de515999d4bad398c36a59716b09d89269d93c5a58a6e42a9a74c372855892c4148174590d3aca268c61694e93186d4321bd532c25f837aa5957184b2994f0e29b319cf1f418a995c5a969620ce2d4329e1d945c1486a65910278752bcc3f69d918e319a994626d3b1b5b8b4f0e921e1d4c532a08a45870226f1b5a20506328b5e3e2558eb2a49522b1254c137c81f716a91cb4a36b8536a31 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part452 : Excludes 0x40000180000000100000000000000000 0x11d7b5a5a0045510101e0000300140440 :=
  finishCode 105 0x3c8e42e8ee1a75bc06cc1e1651f4440c7792d2b08e0c7a2055c0aec48f2b0283308da630575b478fc87f4a2b4e589293d3bc9a367d1bc770b4b0785fc5c0053297542ed3b4299954d1a9a2886231bc7da76a57420c8225b6231b10e712bc7d456c490a8c1412d2824e440923c1b2fe3789a1a343c2f1f94820ad9643a0b4aa47966ef1f52b91ee624b4c623da91cef2b01607434be0c7950d42aa4145174515aa8b479e3ec493bc9d562d29d1661eb0a650aad2e697acdca86f1f047cc4978fad2d8529a298ca3f85a5411705d110269b906ec4923d9da4d3702657469dc29b3b4a14e3b4c7699707203133104536c49242923d3c614cb4b04ab06c43710750fe8a278f1f9696d3b429b4ee14da8de1bdb4ed04ac49650943d0e931d64c841bcb4b624a18541984e95d532cc1b3108a0d0b6d4219634da9950c4a6c47178f918c91e64b815a54d231cc49247af0c495c17434db06e417b1058372994caa8a3c7e712ad2da7637b432a15643f8ded4cae2532acc41 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part453 : Excludes 0x40000180000000000000000000000000 0x11d7b1a580005501001e0000000000000 :=
  finishCode 133 0xb82a0ee1e1de46f1b4624c5a54b987841b2a5b94ca9592d287859453164490b4aae38b64b999d54ca69158031f30ed102e2d78fb125482e2d92e738b4d3aa3b831ea634b9bc7d102923f8a653acc9732479a6d0cf1a758929731c0bc7e34ea19cf8715cc494b9a99490ac3f948e69d716a68a6298e716b12490a48f2d29c8a653accc1f34da96ce931d65c5b0284d36c49721fc4f0d1a97394ca69d3bcc3439e3e97334eb0fe52ea5ccd1ac4180a625cddc716bf8f20366624a2043c2485810ec4934db10e78fb124b4a8812a0cb356219a6dfc390d1ae2583c247b32aa19e5a5a1dde3e1e132128624cb4b624cc4180862473a4b0d4d3af1f7714c7f1f46f1a80f0a6869b5a5c463242b4be69d950dc5ac4388c62692d291ee2d2b8b5893123dc5a0d9624c5a5716b4bd102fe368de3501e14d0d36463986ac49247b0d6624a5c6325b5086794bad2d2a1b1250f29619a5f1a743c2b4b98929a3f8b61a35c5b0e45a760ad52e992e5b0f4697ce2552cb87d4ba45b3e1a572d2dc4f18754b6a5d697c69d34dcfe3b8d4078508328ad89267134ec14f52e9a7678f853d4ba68d78fcd2f34ebe8973771e443ccc495228a6c1b61e15d13c3d1845410aa8a0a6da6330e50f2a1980d2849624b8b442b3125432e2d69d89b5343b4c5a55a5ca65516b8b503a063522b12548738b5c4a37b14db8b61bd8a6c12f38b50ca8555d13c610d3a2399892a5b716b0f50f2a5d86f629b4b2c9593bc999e52b8366 (by decide +kernel)

private theorem part451 : Excludes 0x40000180000000000000000000000000 0x11d7b1a580005500001e0000000000000 :=
  splitAt 1 68 0x11d7b1a580005500001e0000000000000 part453 part452 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part455 : Excludes 0x40000104000000000000000000000000 0x13d7f50f0500440440104104000000000 :=
  finishCode 135 0x771e46b1bc6101aa1e15d10ee879624c8815229a74536881942ef1f521a9869d910269d8f0ea5b531645d0b4af1f90ee6415189e1d4ae8816249a75a8338c2a3623c27d965e67f4b4a98cd3a78778fa205a8581b45b14bb34b50ca29d151b4ae62499fccff21dc2a7299474248f34e921606dc1e1531044d1102981695543c390761489de453734d4d2334ede3efe34ee14db124d3609f8522c49631345516c6d0ef31e24d371694d2316950ff0a6cb4ac025a5a4b0df4cea29b42fca65414c8715329e1d2d25a53c10c3c3bf8a658c9ea2d348923ccc78fca6578fc46369dc69b7f14ca749891e86d298cc1f52da60a81e0d41e1dfc55054719c4d1a922f8ae2995c4f308d04a87158bbc7cceab379892f1f69dab8ba19d50e330c5892c2914d9c963a2cd3559bcc4978fae8c3b870229d34eb4829d50bc877611ca1761e9d146270d0da76f22a8c61c89019c5e3f34ede3f2965892a45309ca6569d9a6c53a45b94ca69d0c1cf1f5329a75540c1cf1f5329a6c3073c7d4ca675631a834053b1a35892d2f7f154515c7856249a353c624846e69da8b4d3ac31942af1f69dcf1f4f146330c4d3a600c9e1838d0de3ea319862d3b22dce2752d9a7483efe34eda85514cb0a8cd1a9e1689222065954145aa6590e269d98632095e3ed3596aa69d516bc7de3f2994d3ac319a5ea6578f851e78fbc7e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part457 : Excludes 0x40000100010000000000000000000000 0x11d7b3895101441000104410001000100 :=
  finishCode 121 0xfe3e8f23b8e40785745616434eb305a5390c941532923d892561e1d2ab2954c8338ada52787949248f65164660b4ad2d8c36767417a99491e11782667876959e1e524923d4c728cde3ea553c3923d30390c42f247a204f0ec49431e3ee2d2d2a20481b123cce331264409e1dc8631005517432a99c5a434e9e1e78fb4ed4ca5a1715c789624a87549264f3c3cba116e624a1c4d3a9834ee78fa85d4bea5922db1253c417ca1778fa965c5719d5e3e78794b71e1cd3a45b86c6b4b62499c4f0e98220661e1dbc532923e78fa9450dad3b9e3e88159148b38b491e29b42db125bc247c66342d923e52fb287c268721a0d411c589319fc4b32204a768255a594ee1bdbc7d696c3584fad3b532b124b4ab4b50bc87f51299fd696a65412a1fe52f99d5892691440a1fe532b0a504a48f6a17c6f14ca69b90926638d36b4b348cb4b528c5a55a5a205e3ee42e80d94a158440a556214b4edc5a7875329a75893298d4cae2d4f18929699e3ee2d247b4b58471c85c5a62522cbc7cd371e1d10248f0dccf1f4409e1dc8790f852c836cd3a663c7e6249d154ca94312652aa85c6f69459886c2350bb08542f308cf85f0fc532a68c493d0b4ae279e3e53b50b88ad6967595a5c45d14da866692a965c5a8814b48a6cb4b0a6db8417c37b3c3b12569650f9e3ed2f3c3b0a6514a204f0e921e1cd45f1852a630d54ca7798c3a08d2d294c66248d8e5a5a2066248d8d696a655d12db1de4f0a27d4a2cc49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part459 : Excludes 0x40000100200000100000000000000000 0x11d7b509e034441011100280500900440 :=
  finishCode 135 0x1e46f1dc6d1fc06cb281e14f110286228aa290529b3124546a1792c2c49033a096624819cb0aa418f1a513942aa413f14af312549ab1d3aebc7e5a591ed4425852d2c29d22dca6561a96943c2fe2e0aa368663491802c2af08555a5ca4d69db0a4d368539692c4394cab4b4b6cc47151998c499c56a2143ba975a76c434b6a8ae346b4d5303f0d0624ab87c3588c11c542f28a4492855429ca65616b87659ba99569f04ecceaa5d2a1b4d6412a9954567c2d2e50aa99585aa5f831ea1d412bc7d4037142b19d54826811c622d99d48b7063de3ec359696a654915c194c745611a1946f6f1f50a99d548329065514430a8cdc50bcf1f333b12504aa573e1e3e6675a5ca65518c982f07e0a754bf150c8b636d624b08e50bbc7c8b6f1f84b6c4922db08e50bbc7c6f6a6328fa2505a5623c83178fad2d102d42a8b479a76b4f78f99c454668d571c8621c87723dc7259456c43618cd3b52e9d15697308da4287743c9215102ae34a639a916454648f390c2a369090ad3b9e3ec47532b0a4ceb291ddc6514c4d1a82d2ae0c35927269b247a2050c148c87778fb4ed42e8259a6a53b43bb895a76a179a3ac47461707f110285594aad1d4129a6d47f285d63e44742aa95589250b862687769ca85de3e291532cb4b333a85de3e8816a17c52aca175a5b0d50caa655c15461ac69b61aca179e3e45143bb11d696f1f891ec2d69dae0fe330b4b9a5eb1732a8a450a6c492479d89a2955a772d2de3e9254b8b0a6532b10ccaa92578fca2904ca1e652aa8a5e3f0a454cb2d2da76a17 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part460 : Excludes 0x40000100200000000000000000000000 0x11d7b1096030440101100200400800000 :=
  finishCode 81 0x742a0973790f0efe3e8aa078520151a00a2152ec66771685dca86667942ae1d715c96d5a4993d487193d3c06c999e58f8a8c85305cd4cae2d333950e624a96453a54390caa65148bf8ca248763e864b32c92160f096950c440b8b6712b12584240922ca8b4f1b3c8fa2781e1716ce2700291c4546d3b516aa8d2594bab4911ec64f348ca2d716b4ee624b8b545aee38b589311ed45a5a552ece1d516bc8de2d2e32ab0ed4bae2d0f091ee716923dc5b2195a76ca2d0a62964b4b1145c5ad3b969661d713b1248bb34eda56543716b4ee4c1fc3c3b78f2328fa2781e15a5ca2d5512b328ad2da68d6004df116d696e2d611993c48f38b4ceb207cefaa2d3469e363b0b4bd696485716878594148ce2552a891d0cae2d5168a466249215946248a8e5a5b4bde3e68d440bc7e697b8b48f6ca2d0a6290cb4b31248c6881716918e5a5b89d892b4b9c5a29181b6de078606ca8b510338b4b4a485 (by decide +kernel)

private theorem part458 : Excludes 0x40000100000000000000000000000000 0x11d7b1094010440000100000000000000 :=
  splitAt 4700 68 0x11d7b1096030440001100200400800000 part460 part459 (by decide +kernel)

private theorem part456 : Excludes 0x40000100000000000000000000000000 0x11d7b1094000440000100000000000000 :=
  splitAt 1 88 0x11d7b1094000440000100000000000000 part458 part457 (by decide +kernel)

private theorem part454 : Excludes 0x40000100000000000000000000000000 0x11d7b1090000440000100000000000000 :=
  splitAt 1 98 0x11d7b1090000440000100000000000000 part456 part455 (by decide +kernel)

private theorem part450 : Excludes 0x40000100000000000000000000000000 0x11d7b1010000440000100000000000000 :=
  splitAt 1 103 0x11d7b1010000440000100000000000000 part454 part451 (by decide +kernel)

private theorem part448 : Excludes 0x40000100000000000000000000000000 0x11d3b1010000440000100000000000000 :=
  splitAt 1 118 0x11d3b1010000440000100000000000000 part450 part449 (by decide +kernel)

private theorem part442 : Excludes 0x40000100000000000000000000000000 0x1153b1010000440000100000000000000 :=
  splitAt 1 123 0x1153b1010000440000100000000000000 part448 part443 (by decide +kernel)

private theorem part432 : Excludes 0x40000100000000000000000000000000 0x115391010000440000100000000000000 :=
  splitAt 1 113 0x115391010000440000100000000000000 part442 part433 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part463 : Excludes 0x40004001000000000000000000000000 0x117579590540404045000400100000000 :=
  finishCode 83 0x882a0a624fd6ae7877f013e47b8b4aa654369a0cd22e2d8c3a5a54b9b1064b991d4d3ac43d89733b6c2a371687856ae4b94f1c5b1a756af245da765a5716ae8581a7522f2d5ddc34dcd2f2d29a6e697845e18d9a34a86b575d158660d3afe3a8f63e8aa07852d319c5504abcd3b426a995a5f12e5b4697c4b953292dda771a6da3a76124299fe25b886633aa0dcb4a4b94b5cd3b4a992e4697150d08a4b969db4be48b92e598540d06d12a6ae3a8d3b92d667523892dda7719d589296b33fb4ee4b59a4669db98da3b8aa12c5f4151a0962d2988e624b87cec267169d902e624a55d85aaa34ee4ab9a454ca671532cd3b4abbb81e19a765a534dcd3b205c63969da994962ae3b8da2a84b7651893245cefa68334691263c0b4ee624969585a67586170d6da5e6912a1cd3b48ba38e607861519954ce2be124e53298e669da85e321a995a761e1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part465 : Excludes 0x60000001000000000000000000000000 0x19793d1501400000c6000000100000000 :=
  finishCode 73 0x50188440b56682f069196ae78748bbb032b89727875aba5ccf0f2d5c6564459882485440a5ccf0eb576b1b4731d85d01b23859c56c4943692e4ebb03252af032c9460c5801a84d1b291d497286d258a45c90b198e48ba205103814c5abb988816d093328c40e292b3c3b4bc1b292116631e9e1c6266593aecc2d521a8c4d3abe12dd2d31e354ca969948e92b3c3b189212dcf0f290cf0276d9a5a0c93c0c49934ea7878748bc69d570c971cc41b2c492429cc6697b4ec1aad6368ea285669da2049620d5256ae8a5d9c42d2d438a55d10291734e9d76440a206242a206441ec3c3b584b9063ca2d440a4bc1b269d440c92358a6543fce2d5a0b1256960c306aa206338c88106aa5cd892bc16096b9a76d6268ba1214193254d0e269d064c5135a5a54e33f9a75696881440cb4b5a5cd3b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part466 : Excludes 0x40000001000000000000000000000000 0x13513d110100000044000000100000000 :=
  finishCode 87 0x7718816abd88812e4b572d5cf0e94368fe3a896794ca4890f0b28c43947eb4d23aa2058931db4f1a4752d5ca3f06da2060f0c92b2d5a205ab490f0e602994e9b0434a32b551c498d52e6a5f3b8c38951fb12454725cd892b4b94caa5f69db28a63d88814503c2ba1a87879256a473a08e652d2a659456751495ca2d32fa4ae5168e6540631a5e69b96aea3143fca653c3cc492c1cc3c3ad5dd4624c1e13b8cc2d516b125a76a659a76e63a86598f1aa650f091d61519e1d4cb1e0510730f0eb57624c1e1151a99669d997e0f0950da5e639495a55d40620b02d5b8b64a28e454ba833064a45cf0eb57671b4760f0e0c934dc107522a1b497292b948ac4952aa566331b124d36973295c92b3c39a455c6a18c69dc0c94abad5ccea6916b0cb30334cb30e454cab57481002d062734ed0da92b4b3992d1441b9a750da969948e77948ac6233c3cb5748b992e4369e1da869dc65f4abad5c19278588c6a5d616997d22e7875abbb0c35903e36d532998da760c95a59e1c972d3b8196787 (by decide +kernel)

private theorem part464 : Excludes 0x40000001000000000000000000000000 0x11513d110100000044000000100000000 :=
  splitAt 1 125 0x11513d110100000044000000100000000 part466 part465 (by decide +kernel)

private theorem part462 : Excludes 0x40000001000000000000000000000000 0x115139110100000044000000100000000 :=
  splitAt 1 110 0x115139110100000044000000100000000 part464 part463 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part469 : Excludes 0x60000010010000000000000000000000 0x1979b3d0150141c60000c700100100100 :=
  finishCode 35 0x6e140621102d5b30b57247c4ad4a9a99678fba8f1f346c0d9256a55e4409c088188ea49d78fa54d6aea219a6608d710b4b58920d948ba54d986f1d44901aaa62f87e2994f4526c881624a944ce306e5102e1d8ce21b961e91edc4325a4ce2e1d6249645102b1d88f6a65624ce1f23d9f8943946ed2d531b124e05a5cc3d22db08587324fd2a63435a592c624ca50cac338749260d5258c493 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part470 : Excludes 0x60000010000000000000000000000000 0x1979b150141000c600000100000000000 :=
  finishCode 137 0x280902e078f620e02d5a98b57761102b3d8edac3d716b07d4a297332ccc1d065a9964b9996490a499195c93f242a974a769736b15c691d44d095aa812154bb2995a5b25a5103214e52ea2056ae87960fc4b733a9026044a0c587a0d5440cec3a89733b8c6595a5b08452ae2d06a836584321e5c5a4b9660c863169636b520cc4952eb096432b8b55c065a78e2d984208929da1e48b72105c5ac3d90ef2995696b8370ae16ad0f312dd102b573469a6cce32205504f15c23a922585b38b50ee099348a5a678fcb575abcd2f4b9a789737508ea0d986f64a725cc879716999c1af0decccef62e8d612e5bc6e13c611b465096283190f2881570ee325a470a879710c12323ab0f5476a6219490b299510273194cad2d29dc95748db1252d329941b291b986330e5236a65258a46e440b30de370ea2480d93f17c624a38a222078d5a6cc394b9a99623dca654b9a5ce124a20563b2d348f6e21440a5cd545c0b0aa6592e6921311b87d102c398ec2921291916e4a49e052c2c49984294d61cb87dc5a8814f1c85a5c37b4b994e4aaa8771c2a1e4ebb22052e728ed89276129ca2052bb38b5236c4925bc4939ac661bc6d16406a9f8923124cc716c8813c6a5cd4ca78d92e645d4a4a5ce716a2058c3a8cb554ae86d4ea330f4f023794912e6b4184ce619532a05e5aab87cc3290270e431264ab921452a722d2e23d9db6696a8ec5063759a5aa65696ce1f4408dd589267149792165a5b1254ca4b1338c0d54b9ae034b92e6b4b4409e064b9b8b5696c49 (by decide +kernel)

private theorem part468 : Excludes 0x60000010000000000000000000000000 0x1979b150140000c600000100000000000 :=
  splitAt 1 88 0x1979b150140000c600000100000000000 part470 part469 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part473 : Excludes 0x40800010010000000000000000000000 0x13d5b3d21501614408204508100100100 :=
  finishCode 61 0x140441885abab0cc16ade3f24bd2d6d2b9004a1cd2b4a9bc7d8c691bc095c29b285cd3313e9a6d89338b4c9f3125452c3f32ca5a55c066c82f6248a25e3e675624cfe238dc19c5d42d599d634bb4bc19a529902ec3d696bc7c8b69574a9b125e3f250c8e2675624b30f1f497c29b624a55cd23041da5ea652d5bc7e4a1a5acb56cc2c8e43125bc4b5c0cd5612ae27d9452e2d5a5a0fd44b298e2d94ca3635a59a248e32d2c6c6a63907698c3a96b716a9954c693f4514c6929969a66d716c3635a5809633f916d696363066a987a0e26338a994d12a37531a38ba34ccce2c3d824e5a9532c64361e849d4cb1a5ca16a25470ec33fb4b640da0fd4aa711987ed2d592a996212b8754aa50b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part474 : Excludes 0x40800010000000000000000000000000 0x13d5b1121010604408000100000000000 :=
  finishCode 125 0xa0240c41e3d703809725ab4e16aed3384e250b43ca5cda672995066c49716c83334da5cd9c4b9ba84b9333ce2b6248deccd6c2586f6c2143ca68a6394cab49716988d066c49518a0ce138b0f5082c495c0e06916aeae35092270675341a9886534acc494b4b0d6532cd33624a70f221950f3297453731250f20cd94bab2297660d96a4cf2199515c64b144ac8a2b8c6aa5d61e9a5d89208994569698cf227129d992cceaae278675512cd2d52091c50f2a579082917144a45e52ea98d0620cd5a0c0670a76ae3a83439a4e66714d99e54bb199da4e81b98726235268d0d4baa3186865a98e2229b432a99419a66708fcc42e8b812e5642d5aa044d8f0a0a74b9cf1f96ae9c268c494b9b0fe1b1999d082a5d1bdc6674208e467139d25436c49320f86e1382d58dee4b9a976624ad2cf4338b1256ae643889a585623a0c50f7190d4cae2d8206f1f5abb124cbb1a556aeb81c0ae2d5d644e1a8520cc4943c9a34d22a61a5e6248284cbb19e652ea995a6614f624a19e5159a0de46e1846de29751c066a8ae131a5652633126131cc31624a9966249de55c346c69170ec3436999e2589267178f980643c7d5c09da48ce199d893040d4ca0cd518c8798c46a5d12bcc49311a8c4ccf0335893299419a6676e0972ea298a5f928aa65616ad2d89269534bb30b819e5892c478246a5f69994ec8ba07f882e9730669c46532b06ccc6c434b9916e03ca5cd892a258a16a5f19d998d2e6c49 (by decide +kernel)

private theorem part472 : Excludes 0x40800010000000000000000000000000 0x13d5b1121000604408000100000000000 :=
  splitAt 1 88 0x13d5b1121000604408000100000000000 part474 part473 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part475 : Excludes 0x40000010000000000000000000000000 0x1359b1101000004400000100000000000 :=
  finishCode 129 0xd62c02d5501fc3c7ba8b2278a825ce24ead5e69787852e6b579e3eb579e3eb23105a54b2cc3d71699c4972d2d88b67712aab1256af3c7d6425caf85a59892863434a0863acb1256af3c7d98621236879894e97362492e5d41decc4914da994b4a49d191c34323ab124b4aa6589261e125cbf8f23301e124ec5a525899fe285b10ccea4932d2ad5e78fa05ccaa29b24ea80b21c07c2d5d7c4b5a46e0dea99508ac1d9042c4978fb4be29daf896b9892f1f14d9694537246de3e9434a1ce2d78fad5d2373d8ea12e60f0bb0b812e5b84911027519852b573c7a5a4f1f21dd2d33124f1e67140140333cc4978f9e3cb842ac53b1a1a5a66915c3b8c78143b9705558ea2c3d40b90a587b205d2a2097989245b5c0f1f16ad3c3c7ad36620b8b41228774b6c50b4b4b0f46d6e2d620a809031078f5c0e02d5a97e620a995102b5752ec26553294ed2e6b2258e2d84ca76114a99e5d83e12e6c4994ca37b5a5b1062a4a905893310542aa4152ecb55532a5cd70532b10e48a99e4ea288152e94ed6ae6678f1a53b33cae0c49829ea65440ad5cb56b225ce5a5b124cf29739e3ea1562110591383f12e6a431252872994d2ae2d8ec229553148244c68934aa46e592a205c5a4898f02a655314cb2d2d102c49716a456532b12586a7714b9c5e330a62b888159052aa3384b6a6520d9e0589274d80069535a5a8cd6823079886a6548d9526532a50d892c4314aa8ce331a20452b1e0510291b94cac49 (by decide +kernel)

private theorem part471 : Excludes 0x40000010000000000000000000000000 0x1351b1101000004400000100000000000 :=
  splitAt 1 119 0x1351b1101000004400000100000000000 part475 part472 (by decide +kernel)

private theorem part467 : Excludes 0x40000000000000000000000000000000 0x115111101000000000000000000000000 :=
  splitAt 4579 125 0x1151b1101000004400000100000000000 part471 part468 (by decide +kernel)

private theorem part461 : Excludes 0x40000000000000000000000000000000 0x115111100000000000000000000000000 :=
  splitAt 1 96 0x115111100000000000000000000000000 part467 part462 (by decide +kernel)

private theorem part431 : Excludes 0x40000000000000000000000000000000 0x115111000000000000000000000000000 :=
  splitAt 1 104 0x115111000000000000000000000000000 part461 part432 (by decide +kernel)

private theorem part417 : Excludes 0x40000000000000000000000000000000 0x115101000000000000000000000000000 :=
  splitAt 1 112 0x115101000000000000000000000000000 part431 part418 (by decide +kernel)

private theorem part405 : Excludes 0x40000000000000000000000000000000 0x115100000000000000000000000000000 :=
  splitAt 1 108 0x115100000000000000000000000000000 part417 part406 (by decide +kernel)

private theorem part379 : Excludes 0x40000000000000000000000000000000 0x115000000000000000000000000000000 :=
  splitAt 1 116 0x115000000000000000000000000000000 part405 part380 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part480 : Excludes 0x20500000000800000000000000000000 0x1d5a7cba5520020008805020814000000 :=
  finishCode 73 0xda330c62a09e12c5b024eb12678fa99418ad3b826e63778fa995b0480f1f312418e63714ab1162beb12434e69169cc10931b95f5a772d2c18a90308801265903c79c4e69db12569669d5a5cc80dae69db885696a1734e98dc516b4b9256c1d53298dcc6f3c7d69669d624930d830865979143f285c6f25795a5ca4350facf424b2d05892d296114b73c7c5161979e3ec49611e43c6c57946167b21e54cb3125e3e1a79e3e36b624a404938d3a78f631cc610cea493836a5c1c4ccfe493223c52b312cd2d54114430926a5b94caf1f517b4b650cbc7cee302aca572d2de3e639055aa865959ecd297109cf48b257939ec87978fb50c6200c499456459521991cf1e68d31bca2f1acb484acac49159a40c49890a69d6114442ac6593b69e34cb330bca32d2d50bc36b624a11e69dbc7d69669d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part482 : Excludes 0x20500000000000020000000000000000 0x1d5a5ca25d22800800800220000005020 :=
  finishCode 151 0x661a06d18c61018312c496ea8250d412755c0cb869d4ca6479a76c49690b8b4afa62592d28599a76b4b49fa5adb0710d3738b418ab4290e159a1ad4cb312678fb1054b60a1716a99520624c0c5435911e1598315204015c3c7a1049960ec69d6209964d3b309c10f30f4d3a96956190698ce294b49264d3aae299413b1964932c3b92573075b02615c610c5e6595a5ca1f61ea1950f2b298e3a3455a190441877299434e819521a9655878fc81961ea85d6968199e3ec235a5cf1f61eb12661da9955028158532ad0c3d9e3e1a761147b3094c6f30f678fab0f1f61fc009052a8f434e81d9846b6308c4990f25794b4c62578fb125e3f1c4d0a6ac28b678f865d89329658c6c070b1a6c1729002dda77286cf1ea31920561602429a750a738b589278f417ce2d624a99660eb604c299650b8d150f262f32caa0f1f94ca8c3c7c68b21e58931c4d4b721e58c7b1b0511cc5d19c159a55661fa995c5283152ea8b589284f439990a41987e69d408b1252061fc81152e9a75843296d45a9c2d2e69da8b4d3673d8c96e2d52cc84f4398acc70b30ecd362b35d13c57184523c0ad057b126515b4852d2a5b694c1b950da8b5a773c7dc5a18f532b12639ea8654caf1f50da8b5c5aae24848f907ab1f33a9a6cd1b38b4eda375610c81943999c436ac8240c1d8d3aae29950cb3c7ccb2a598117309d876a654814034dc69d3c7924e34eb18e630867f34da0ae598a14cefa62592d2e2922394ace264935d1843aec1a531bc96939ec77d130aa06596110833c7d4ca0a5050cf1f532a07678f989587a879 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part483 : Excludes 0x20500000000000000000000000000000 0x1d5a5ca25500800020000000000000000 :=
  finishCode 133 0x128261102cc2d2db44b4ce2d3c79a7491e4ad716c4853c79e3e481483c7865e15691ec14a499532cd3b6d11c6605027e12dd47b3c7d89278190f2879947a10b2959c4de3ec629958673884e264b7136c36b94ca0b9140bc7dc435100716980d019878f280fc532b380c592d2e61a46295b12461f3c7d45a4b790f27a3c7c96f042cd2237103294e669682858c6615c05bcf1f25b842e78f88f5892969055cf1f61ecc4978fae89e240879891e69d5714caf1f85660a7516cc254b4c639053a9950f32995e3e67534d91665329a75a7678f418c10b50db0e4c6e4b1156a995a048160640f1ec63080af896219f9a76a6524ccc39532b4ec93312c54cada320a5994ca69d062926661eb125e3ea653c6c62561b9a74d36e62b8c61896050a99416e6756c18432c9e8f1f90f2b5590ca28b532c625516b1265a09895e3ec62996624bc7cc4a0c70da989678fb124ea2a212c54cb1e3526b198501d0a654817469da11e34d9a7469f34bcaa6482b813761fc84133ab12622cc62533aa0d633ab4bde3ec82e8861a75ec522cf1f620a96462734bde3ec4178fcd2d624cd3b78fb4b661e99d5e3ea22b875133ac1b93c081be31ba85633aa4d520640f1ea65983aa450cf92c455ad3b61cca65156b18da2b8a6585664b761047b3c7d8924b1696c82b78f98dd8763858172b4320a2f9e3e45978fcc3d612ca65 (by decide +kernel)

private theorem part481 : Excludes 0x20500000000000000000000000000000 0x1d5a5ca25500800000000000000000000 :=
  splitAt 1 65 0x1d5a5ca25500800000000000000000000 part483 part482 (by decide +kernel)

private theorem part479 : Excludes 0x20500000000000000000000000000000 0x1d5a5ca25500000000000000000000000 :=
  splitAt 1 83 0x1d5a5ca25500000000000000000000000 part481 part480 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part486 : Excludes 0x20400120000000000000000000000000 0x1d793ca04841a20c10124800000000000 :=
  finishCode 57 0x3d8da2c0cc2d8d838b4d1669961cc639696b0f524f029574631c8640caa2b34b4cc3d34eb0f64b4c9279e3ee2d532b09ce626695a6cc3b5d1c8592cd2d3c0a19d2d269d50129f2cdde3e7875a5a5bd23f2d1c14a2853c3ad2d68f1e050ce73d491c5ab4b94ca96961fc69d1448acd3c322c9693b6a9963b0b1252d2ac2e8902b869d52bc87d7168a5411b3125456d2d532a11d846942b8b4b4c18c430fc314cc49532a13c6ea52b8f0ef1f1b59954a571e1de3e36b32aa99669bc36b532a996714cd2f0509cf6641203c3a1886b94cae2d045bc7d0c285994cae2d0459895e3f1955892e2d312a995c5b309d0d6f1f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part488 : Excludes 0x20400100100000000000000000000000 0x1d799c224045921440920500100100000 :=
  finishCode 125 0x5d1ac641c8430d3ad4300c274c052b34ed2b696f5717c159999e532a8ae78fa95d24266761eca652a9b8b524e66978faf8c498cce669532b8b65a5ba8ce0acc2ef348da6ea4141ea1f5c5b19a4c7b34eccd295b852ad3b601a83c1444ada5bcfc630cd338b50e6969330962411f25a542f0a2c8ca59559bce2d61ebc7d7c710e9b1db52d21b94314cb16850fac412ceca652cac52b5a5b8b5e3e9475817c43ecf1f0bb9a6569f348da6e5a10bbad2cb131655e3ebe1f87819f4cd33125a6ec1d948a87d624a96e53286e4d321339c5ab4b7b16c3f17c1c2cc39330a5a5c5a67d321c5b2d2d247168ace330a5a5a5b3075a46843330af8942c04c1a64c7b34b5876a4161ead2da470d8d87a465824665961db8b5e3eb4b610c5232a9965587ac62d2dc5a361886659552eb106592a10ccb240d696af832f92c282f047bc7d0f2265610b0f56973c7da5a5711599b09c148c631046d7307452a5538aa738ad2ba1b514aa8c6716b1051c78fa2008d0bbc32f520cd23696cd4320f625bdd45b05667e31262cabc7d28e67d295cf1f2d4ad2e78fa51ceba9693f189319f583b34ee14aa889c38b6610a0752d232f04b954c512c63c7d88f11954bad2386230474566667624a5887d989229578f8a0d69705dd62ef1f6c0d0580ccef62cce71699854ba6993bece2d68d8245c5b2c0861a2d42a77d869a37569dca5d3be9cf5c5b0cde69b85dccfae2d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part490 : Excludes 0x20400100000004000000000000000000 0x1d793c625561920500140100044820400 :=
  finishCode 67 0x1b064130560f0eb6251d7c5517469dc68d32982acd073c7da766913c6c65333eb8b6295c68d247b085c5af1f751b4532a1ae624b8b4cfac3b057cc3b985aa2b33aa95d585718c661ec751a77123c566ba19be61d9a74ceb19f4d3648f9e3ee2d348bc7e69d9a44d3b1965c5af1f69db8ae423a99587669d63174450cdf3084512c2d8cde2b3247cf1f348a5a65169a2caa6e2d5f0ac391ec610b0f5c8345c8795328acc14b1a2d4ca3719892a65346bd86618ceaa6571699f414b38b54cac219bdac348c48f624c68d78fa1f4d3738b5c5b2f8da27867d4315c5219dc652282952260af716c379696a0c50f3244e4adc645057b8b6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part491 : Excludes 0x20400100000000000000000000000000 0x1d791c224141824400100000000000000 :=
  finishCode 149 0x1584409907c368b4b7b1984316c730cde699420ca1b05386e4d36d39532c0a76a187b3c7da46c2734ea994cc647b969330f4cc667d3c0a04c14ca52b8ce230759b9e1d2c66538caa6714c0f0f247d2dea2d8a1669d329cc23532b50722486713aecd213be86d5a76a655a0c81902fa1f436a3750dac375532b4ee1ba9e1cd3abc248901a6c6d72904d3aa4186d694f532b1263469a74cc73125a76d2352ca51db03c16c3c3b18e61f8623686297b0b0b3c7c3726833379db669c9a752728538edaa59341a7074d8eda375331b48611db0f508ec418352e2d69c9a74cfec2394bad1b05786950cb1a75843198dcc5e124670d06671849e82b430a51e61c9a6413f1a74ce29e198ce271a64e7a76d52c826c56738a4c8ac49510e271a64cdf2975b4420ca1b716b4dd48263969d99bcd329e207e516a8c4d3a0af92269636d1ec5b0c4580cdee61a6543738b5a6ee1f520b4e447b34ddc3ea41224c7870d2b8b50c2c3b751842c3b34cb07e247954e60fb8b5246a0f85714ca8658d3a69b61ec69d5718431e1cd36947987ed3b3c3a4078758bc669247b4ec12b348c56664b714c69d159b085876c82b8922608619a36b4769d8254d367873bec6833b6c68d1bab086714a9950c27874910e7123d48269b61da9955c346cc3b1bab0ee4918434e9a0c4f3207d482969516a1e4c8b0dd632282bcd3ad8318c82609c1e1dd47b15c5b0d361379c5a96950aa97456667d331cc1f8cc6a6534ca1ae62499c54ca69b331c69b52ec6835d0cdf3084512f1f6208694d322b33bece2d341ab8e60a26159b8b4d06c3b8566e1f2a9a95c512a659c5aa5d715a11d87a6698f0ec1d3f13c33ea18c1d8ebac27518b12542e87752cbc7e43cb09e515b4e650ca95cd32e2d (by decide +kernel)

private theorem part489 : Excludes 0x20400100000000000000000000000000 0x1d791c224141820400100000000000000 :=
  splitAt 1 74 0x1d791c224141820400100000000000000 part491 part490 (by decide +kernel)

private theorem part487 : Excludes 0x20400100000000000000000000000000 0x1d791c224041820400100000000000000 :=
  splitAt 1 92 0x1d791c224041820400100000000000000 part489 part488 (by decide +kernel)

private theorem part485 : Excludes 0x20400100000000000000000000000000 0x1d791c204041820400100000000000000 :=
  splitAt 1 101 0x1d791c204041820400100000000000000 part487 part486 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part493 : Excludes 0x20401000000000000000000000000000 0x1dd978344092040100000000000000000 :=
  finishCode 99 0x501706e1802d59c078f6d16ae94328a1998926994409a162589a64ea315b4b22e2d78fb8b63129c4ca5678d78fb98b21f8c6312496f215543264770ecf1f349a995c5b0a2d0ce67790f2e2d78fc63952e928d432b579805e0f1e35b8e26d3b33e82b56ae1974d0cfb1c4da766993aec69d716ad5ce26d3b5abcc01c078f5a1b84d128e95b532ce2d33ea996716b125a76a238b6624b4ecd32e2d90cec4969dad2e69bb4eccc433b4ed4cb2105c5b3124d32b4b5d17c511b4624cd3b349a78c499a7609734eb12669d8cdd882c1d8d3a9699892a15520b4ed69669d59188b0cdd69649d5a5cd3b716a88be218d3b8c8ec4905999dcd0aea2a09e1a7643c9a6493ac226891f9696c3962292dcd32b838b660f92dc34b34edc5a62584eec4934cae0a612b5a7718e52d2c49988a91f69da47e5a5b4ed9459acb4d05b86941531a7584571702d0ce2d69da4fd69688125bae8c49987ec4534eb4edc5a5a12c2cc457169a7634ec57d6b1845c10a734750f20b7256a1e62c2b8b4d3a91f8a56a1969db12548a49d61118517c55542ab8b5892879716cc49624ca2f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part495 : Excludes 0x20400010000000000000000000000000 0x1d591b704400508204000100000000000 :=
  finishCode 107 0xb8370a816ad0059fcf1f3c7a55dac6115c60fc843432a99491e4ad630d3329751024b15abc71360ea204196f631866133ec93f5ab8acd1032cf41960cb8e05abc881420ce2d189a994aa632b922e4ad5ab9e3d20581503c7a55e258a5ad22f12dd6aec49922eb574b5aa0c63a857d8d364b753292255c550f031a6c14e92f88eb19c525e6853499a164979305417014b86b67139a5e6478372677346bc7d67f3c7d607b0f1e94190b41306598196e2d62499f4d3236b5a5b30a20dad5c34cb185898e82a41065999d0cb032e520c2ad420a1ddd45714cace219d8832d552d233d8216c41432b106389924d0cb032e716b1254ba67d34cad2d7c4d18832104566d2d716b0ed87a67d34cba886585660cb3c1c5b348ca76685716cc1d58e98f587a465610832e7118c716ba8cc199e532954c1962ad620c867333a994ccf21050ca8658fc43187b0e1583aa1f8b2aa65156b086232b0f41970dad4c491c5aea318a650dac4894712d33105e3e08d5a5c3714b4c3431ad822500065c4891b1ad2de3ec218aa60cb1b5b90c6199e532924d4cb032d47b312465ef1f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part496 : Excludes 0x20400000000000000000000000000000 0x1d5919314000000000000000000000000 :=
  finishCode 159 0x5c078ea03708816ace06516ae6778f0e0cb44092c634cb124f0ea8368787191c71362299558924b748dc96b6979955892c418196e2d3319215845718c2429db66248e14946a6581967135f1cc349b886440832d22f032e710a205b4511cc349832e440b12522f30ae33e832d1031595892a83687875e18448096249994ca93f34ebd892f9892685145ca65624c67d349bd8d23334ca6534286d62519c4da769e299490b312470a69d70fc87d4abb10534570d3b34ed89248524ca78c418cee69d624cd3b430b07588338b4cc6b5769da20e41e1d346e19c6a18434e83151030a2c95aa5b91026699696d3b251a206251b4ee33bc67148ba20495ab4b69da206289857d6960c36115c7109464ad691c1b969d832d6972a068594ca4b179122e8818d3ab4b86b6f6288b4b818a677349a4be62483146eb3114d3a0cb791747214434eb68f62f8c23104cd24c1909219c5ac491a9ad2d2431a65a76d398d32969624b4ecd333125c5ad3b67023325a569a86b5a5a1f5a77199da46e2d624b4ee0daa1ad4ca0cb430c6678196c413e0985106a6b4b7b144f31254ca86b3349a65244aec781716b124516a65716c1b9944e7829068590c287d0bb857c6c6da1a1643eb48d8820c3620ca2f624a8be4308d8db45516c061c28b620c0c3716c0c313cca5b624a88f62f8a819dd9c3499d863c0b8b50fa731988aa6561ca186520a8bda76e2d624b504a79c3a667061a78c49988a025136ad2c94e027988aaa3126048b8b50fa94d81863756e0187032d89338b4cceb2128c63125b4620cd23716832c93a9e34ed4cb296c70ac419a77348d48ae419a624eb076517a5c4cd2a275d0cd2c4194a6a654b48a2e (by decide +kernel)

private theorem part494 : Excludes 0x20400000000000000000000000000000 0x1d5919304000000000000000000000000 :=
  splitAt 1 100 0x1d5919304000000000000000000000000 part496 part495 (by decide +kernel)

private theorem part492 : Excludes 0x20400000000000000000000000000000 0x1d5918304000000000000000000000000 :=
  splitAt 1 108 0x1d5918304000000000000000000000000 part494 part493 (by decide +kernel)

private theorem part484 : Excludes 0x20400000000000000000000000000000 0x1d5918204000000000000000000000000 :=
  splitAt 1 104 0x1d5918204000000000000000000000000 part492 part485 (by decide +kernel)

private theorem part478 : Excludes 0x20400000000000000000000000000000 0x1d5818204000000000000000000000000 :=
  splitAt 1 116 0x1d5818204000000000000000000000000 part484 part479 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part500 : Excludes 0x20140000000800000000000000000000 0x1d5cbd9a2174020000894020805000000 :=
  finishCode 41 0x1ec621a825caf0c82576624830cd062bb3e0cea7e2d2c21725cd8929e047649a9e04b0a961532c97323d9e06490b07d2e6c4950bc663622a5ccf1eb4b0619c878f50cc9735a5a974ec247b38dcb4b520a40ae300ea1e3d0c5e108640cb284790fae2923da8b4507309589269b945ac1f23da96e23daf069b94ca6753c6c8233b6cc3f6249e056c50fc45934d99654862b5695cc49523c2b550f9c8c338d36a1961fce29312a8b4d36c3315da5ce62499c4ea21b5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part501 : Excludes 0x20100000000800000000000000000000 0x1d5c64920120020000804020804000000 :=
  finishCode 131 0x6a198621c01e1b68c22b8d81265a3b3124ab282934e8ab418aa198d3a2c7624b60f2160e3c78b452e669d410972459986e85f4b9b4c46e29739a6285f60ec78f34eb1880031548334ecf1ec49943278f986e69d25c89f6624b884e869733c79a753c25caf869d6f14ca7519892c37031ca151afa8564b9998d4cb309d456c63a8da380bc2b8a812dd6a7191d89269b24ea9166969a6d48b0595a5ac4924ebc878f5d018f0ae4d3aa198f1aa4393c5e100696c47f1bccc497109cece62a6533a8afc57f34b4cc655f7108914d3a2bf942a6836c1001afc78f346b2069b15fa11e439a85d866b239203a0c41d6909164d3a78f3410f33124acec332f1e3f34cc48a64752da8c4d8093c91b5a1849e78fb80d2d94b683b6248ad4d3a0c740048b3884d3a6715a9c69b39d9a75d44815c530c78f3a09a748f64997914cb15e58922d17109a7583f20c410a371571b4619b78c3f888e2c7532a17da5b2994e2334b54cac4990bef1f94b669d3989e05c0301883a1584b9b20b4b5d14834e8aa634d92e4e66f1f821649325c924e1669cce25c924cc6f1a44e6678f78fa28f1f33a9e3c6631cc5026d2f532924d02712e54b7388448af1f32c9a6cf1e6399696a5b1669a75a7678f5e1285608ea9738d2269d696c4b9085cd2b34ea5cccea4b934eccc3a8c2307e69d9e3c58a47b24ca004b992d669d5a59e3d74195c917624b4ec9722cb9432847401604b3c69d3c7a78721a75093192dc5277d3b8b4b64b5b124ad677d43fc76125cc69d34ec78f (by decide +kernel)

private theorem part499 : Excludes 0x20100000000800000000000000000000 0x1d5c24920120020000804020804000000 :=
  splitAt 1 114 0x1d5c24920120020000804020804000000 part501 part500 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part503 : Excludes 0x20100004000000000000000000000000 0x1d5c04920100904820100004000000000 :=
  finishCode 1 8710 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part505 : Excludes 0x20100000000000020000000000000000 0x1d5c04824920800800800020000004020 :=
  finishCode 151 0xe4350cc3603c35d19c790972e01a750ff25cc5a678f05fcb3d944ed3b43882fc70ade3002d157091f0ab4f1f2995052829891e84d0c6c48f251b7895d86ca0c5168b486716b12587a48f251a0070300581e3d141a7a106628c5c5b2994c8f05cde3ee2d716ca1b532b4ede3e63990e2d3b716cb4b4f067e5c28ae517906d4cae2d41da964d3b29963c7ca459a76a655a5b8b4d3aba388f62f04b963114418cc25716b07cce2a653c7a5cccea47f4afca6552d99fccea69d441a77294cf1e9735014caa278ae6d2f78f9ccd88205994a669d954570ce219d86ea69b3c7c1b5300eff1965e3e97334ec78f630d3a0a78f1e97323fb0ee5a5a5cda05e12e71e3c9262cd9a769733c79a6e166b30ea3089a25a61568b2c91e4995d1a4731b048bca177149e3cd3a4b9165b18c49896e87f98929739a66e2d3c792dc96f2966716a49459678f25bb60ba0b2e34e92e508f1cb543678f165a5ae3c7b60e21b84b94b16631df52d287f34ece2b495a125c52d390d4a5a4d3b2d069d5a5cc236248284512529059a126624b12605986a50fe69d34ec78f7b18025ca80902d878f64034702c414b061e624a5cc17325cc3464c2f07c318e215a5ad8a6585760a7624c0b9052ca1f532b20d23680b9624c97315aa916624a96e058b08e053b125093296d69e2094b9ad2d98710af0b63180a798920b1532c97362482952e7312418334cc2b697361ecb1f513a91414a9733016c4b9a1c60cea586624a916133b0e487209f624ad8aa06d433b1a0c5528624d61aea575c3f299569678f05eab887d92e667f43ec973 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part507 : Excludes 0x20100000000004000000000000000000 0x1d5c04824900900120004000100820100 :=
  finishCode 139 0xe21a8e438b5a8661b01e1ae8f63c84b9222c10b52d8de4f1e97334ea7087986e245952d81c61b89164e80dac78f69da5cd8050ac69d2a99e3c94728acd3ac2218973891ec218f1ea654b9cd3b78f83154cada2994e6328546f2c490dabc7d0e29698f1af62e8e012e50ab34b54caf1f4b99e3d54532911e49a98e5a5a18d4b999c5a5b19d584ad3b4b9b40a659e3e9733c78b3632acc210bc86454caf1f4b9b40b021f616292158929173c7ba848589327618892955696b0fe247a5cc5962ad69dbd8b612e59043057678f90e647b52ecb4d49cb8a5842c2188f6a414b9a5ce532a0f50fa47b6001871e3c8f73124186973581b07b18425cb90cc350de0f0c94725c45a6c219242c492518b2e247928da8516ca654aebc7d2e62d33c7c9735b1903a057678f8e3695f52e9e3e624c13b52ebc7d2e647b8e429713418f0e169b30c2348d037887389620c30dab80c0128d89325ccf1ed2d94ca47b49ac69d1e186747870f0e696c6631e1aa81b58d366634b9cf1f3c7b50c20f0d3c600d3a2c78c8ec490938d3da66f1f52cca65620b4ee24c8de4f1e2c778fc69d5329e3e7507862cb896e48543fc449696b30b42f0a4390b00f0d89328b525697369d9e3d7469da1fe224b0952564b734e92de641805b0e369733c7868c217025d8920b1624cda2d8a4b83429735178aece8517cc494b9acd652d91ed2c2a27989209f4b9b08e78fa5cd2e70f0d8005fc2b93c7ae833f94a6c495259a74a0163ca6552d911545f2095c3a027251b4ed2e734ed89278f1e1829e1a3a5ccd3a78f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part508 : Excludes 0x20100000000000000000000000000000 0x1d5c04824100804020000000000000000 :=
  finishCode 129 0x1308815a1696d4390ba0f0dec640972741a75cc4b9a99634db4be78f825632cb4bc50ee2d78fa5ce78f95ce4b9bc7cf1e49394ca78f4e15c38dc1a34b99a34d36a412e588319c46c6c418ce20c341ec287061868cf1ee412e4f1e847895a71b92e678f8786be238ba0a05607b17825caa03c334ec78f532a1962b9bc7cf1ed2d3a1ca276249264d3ae4330d3b94caa5734e8f0cae71a75e3e45994ba66350a829c36ad3b9e3e4991e1b90cc30866385a2a5d624926496e2cb818a72d249cf1f3c7a9763c79d8e4388598521a870078669d8e8678f69d8314932c49897284d750597286c97278f24ca4fe69da55cec269d34ec0bf4b9b4ed8923c35d14cb34b497286785a678f5d16c25cb4b61bcb12436a84f8186d2d53291ee532a5c54ba78f721986a1741e1bc8e21a75ec414cc494b49c8643fc78f4b4c0bf168c4a3624ba8d3b9866c494b98b2cf1e49949fcd3b3c7ae8e21a462b9a5cde3e78f25c9a763c7924e4b9bc7cf1eba3d8b612e57870eca6515d91ec33a0a74b9c47b6249e3cb131a464b982cde3e19d6610c439c47b4b9cc4952e9e3cf1f390e215d1a85a1484e118421606c1ec5e0972733821697323f99d4786c45926a9730bdc68d4b99e3e34e8f0c78712e61e18f0e34ec85f24cbc7da663c34b9c3c343fc78f1e1a78d33987278f69d924cd3a4b988f64994b59e3e25b9a0e41e9e3da66973 (by decide +kernel)

private theorem part506 : Excludes 0x20100000000000000000000000000000 0x1d5c04824100800020000000000000000 :=
  splitAt 1 74 0x1d5c04824100800020000000000000000 part508 part507 (by decide +kernel)

private theorem part504 : Excludes 0x20100000000000000000000000000000 0x1d5c04824100800000000000000000000 :=
  splitAt 1 65 0x1d5c04824100800000000000000000000 part506 part505 (by decide +kernel)

private theorem part502 : Excludes 0x20100000000000000000000000000000 0x1d5c04820100800000000000000000000 :=
  splitAt 1 98 0x1d5c04820100800000000000000000000 part504 part503 (by decide +kernel)

private theorem part498 : Excludes 0x20100000000000000000000000000000 0x1d5c04820100000000000000000000000 :=
  splitAt 1 83 0x1d5c04820100000000000000000000000 part502 part499 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part511 : Excludes 0x20040100000000000000000000000000 0x1ddd07086404830040100000000000000 :=
  finishCode 119 0x711745c0972823208813f1266787516cc49610cc624878d9a5a69b624a5a5c5a675750b1334b48f6d2d8e833c7c8cac2532128661696923125c3f10cc37296923dc1b9531c4654b4a9948931195c5ac4964150490f0ed41196424a4cd4ca7e38a60d4bc7d2d266f424c1a923db086346a4cc372e2992d247b499a48f1f4b4cc3b532948e085846ccdec21641a82e12c6be256d6c53285be15db08615dce2d610c1b9532bc7cfc78fad827d624c5a94b499850fb25a569659594cb2d2c6c6f1f197b28b83508814915415dcc4933eb8b4cea691640f1b19d457647b8ee2c3d33aba8c811ee52c8aed6052ec94978fb125c5a973346c47b624b8b54af11950c3c38926238b1254b286142cc7716a1603338aed2e73084cfaa5d291cf1f5402473c7d696e2d5209985e3f20942366774b9ad8d41f82b56913c624ce2d4b9a98ce9ae1f9892a5702dc47b969664d52bacd6396a9753c4b9c78749aa1ae716ac7587ac493211024c350b4b5b1e4690576c49987aa5178f99f5883095c5232995053213cb1286b624b0844aea6534cc9736a16c790f015d9b015b9e3e16378fc973197bc7e4b9994e0d0a994cde459884e8170a8b0854ca08d9e3e16f4b9ad8d21f8a259e3ec2533799f58771675a5af1f15d9a65e3f25cc576c219476c3d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part513 : Excludes 0x20050000000000000000000000000000 0x1d5d2558a205500000000000000000000 :=
  finishCode 99 0xb82205ab640f0380f0e662d5dcc532b2874d987a87134da49ccea96162652ea8d56c50dca3b622a97544b2d89274b4c059696a974ec330ed0e32205946f1cc49124f297436a1b9333a994e9b116437276d94ca1a5697ca658e05316ae80220528f1c6da5671b836b3125a5abc27071b9a56b63981a994821b9612c8495318c6d48274d94ca9c24833b693c871414cd27624998c637398b5765147b19d5443f14c316244faa61948eb3d696a90583ea652caa986528c07753189f4146881320e0532c963440af0800c6e2c889e54cad2b051c9274a7847e097a53d43f2985846a3152ea205ec5f0972da299509b387d83aa3d05fb0765a5a58c905312b6962d2dc5a57d984ed2d4b4a98584f110da5ab3d984e307124b4b54c2c39624a556232b8b5a6693b4912c5329308e1d0a3d530a856624a4ed2e677d90fee29640ccf25cd24eb20de652e999c36a667942b065547a66750dc1b505ea58da238a619a5a3750daa8f554221c43b61ea4ed4c6c1d61ec44371294d567ad2d0ccca3d05fce2d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part517 : Excludes 0x28040010000100000000000000000000 0x1d7fbdf82c4402d681410502829040010 :=
  finishCode 51 0x631646d0fc5515c6516c2f036ab827888147129274d8edaa519892e2d80eee2123db1254a2a6518fc973624b8b51033125476a6592c22594b9a1ccdc3a6c77d3c6ca1f439a53544b292da6e8475a586d52e68733a8cb550daa524ea32d552921b53f06eb1df50e65011ee33fb4854ca9739696a21f8ae20d4ec525c8731baa92e4399d350e7292c7c5216aa4658c2a8614b9a94d6532204cfe3219102331594ad0584720f52e667f51e9d3570511102720de63c09d4530624ca652329e36314a8f48f734b4a731e346f2a3d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part518 : Excludes 0x20040010000100000000000000000000 0x1dfd19d8244400d201410500821040010 :=
  finishCode 143 0x1c462174750972be248da29951c630d40dca94e42ca98488715b587e7e28f661f994d87f30856961b986cb21cd87e969624a98547a7e348a228f6624962547b11ed07ac490dcb12630cb8948f687d3208f6e2d291cb4b610c31f630fc5711030a0d892589440c969696acf50e6e1f9102b3d2c89655696a3b9892e1f4409194fc440cc49440cb4b58138441a44b9a386693f16633124f1a9218cfe781598c88162491edc4b25c50facc288961924283523d9195102685751344908f6585969aa65440c639910275d91026398a1613f2c2b3095d94a287d624aa8b4b0adc103528a1f5c3b370ea2a87e1883858886881624acc50e6b819fe624a945102385983e07b716b8b6440ad2d84320d587a385083a205c5b30fccfec49440b8b6624a99594531b87311027230e6526b125a6671b29199c54443eca6561c8e16532b12587f398722e86710dcca6123dce1f624a9860dc9f876d8f1a65b9c427815710c5108f6c39908ea6543e9c6e70fac75662a3d232cd2d1a1a99543f2b8723a8a3d8f02a6523da882719c424430b89e3589330f52d275d825ae2343ea99543f2e082310881431696cc268a431264b98d8c8f6ea25cd87319350d6a6534cce21342cc39430a5cc6c63859a66a4d4b9829e5328d8d2e6a4d751c42a4d88f6a4d8892b6300c629361c2a9958920a7052ca51430cc39342a5cd2e73125a43d0fc141cb4b43eb12547aa515319c0b4b232ca3d510b48d0c334b48725a15108d8d2e686190fa973691ad2d47a4118ada971 (by decide +kernel)

private theorem part516 : Excludes 0x20040010000100000000000000000000 0x1d7d19d8244400d201410500821040010 :=
  splitAt 1 123 0x1d7d19d8244400d201410500821040010 part518 part517 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part519 : Excludes 0x20040010000000000000000000000000 0x1d7d11d82404109200400100000000000 :=
  finishCode 79 0x1706e1602d59c078f4414c5abb28aa22056c5d0323299461671b051b88465948269b610c69b94cac493c0cb61e363b0a974ec330ed6c3914ba8478f02d3353291ed08f29954cb211c133287d4ba71b50da2055c4f14c4c124224c87d699948c13271b049b0e66999c6c4b287d04c9c88478e3669b532a05c8f684794ca7e1e3661f9625892c1f423a99623da1f634d91ed4caa1f8e0440cb57571c443ecc496999c6ca4668d34dba847b94cac49943f22040310b575815c3c7a5cdc5b12e46b686104a92e64912d306e4332f1f53286e623d99c589234394ca78f3c7c595906ac4942cbc7d4ca78f300f1e843c7d743f147ab6099584b16548ca01994cab4b532cb41530919544291c14771689648cac3d9c3eb4b9a66143532a48a53984a8590b7a99554716c87d716c16f (by decide +kernel)

private theorem part515 : Excludes 0x20040010000000000000000000000000 0x1d7d11d82404009200400100000000000 :=
  splitAt 1 80 0x1d7d11d82404009200400100000000000 part519 part516 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part520 : Excludes 0x20040000000000000000000000000000 0x1d5d11192004000000000000000000000 :=
  finishCode 155 0xb80f1d40381b85aba985ab571102e6248981a6ce3734bc5226593c3a91615da99545aa4b43eca1715da964d1ab624809d523c721712956cc72a454b4b4b63c6c9694239e1e6968aa508ea1f390b45114867518f1a6599a5b1d746f2a4550fc78d69686d4576a82c0787621c44b9a484b968dcd2f69ba99508f10d5c5ad1b9a5ed3739055329954b247b41ac26315da8b54ca2bb94b2343532ac0aa25cda5f28d4d1ac49946aa591adcd2b695c17f69796acf0e982a0c41e1d4c5d1ec410972bc25cd69688134cc5132a7a184b1300858928232d4a8be5a5a91589282312653299fd07a55b5a5a5cd10255b92e60c3532c823061a1852e6b4b440a996592b0ad0fec4925c830ce44409c6cab647b9292a45624ca2d532b10f63984b95b18930ad589322052e6663061ca5b44099a52e674153e5a5a5cd54154c86b32ab876061b98e1f94b665562498ae5228d0c2be55b621ec4b9b88b62d2c972d2394b667d34c830e31cb48e53280cd09294d440ad8b4b9a6ee2d4268aa58c69bcb4b42399c4ea3248661c8a6503ac34352d91ed10301d4552c4590e278d52d8aee423a96cc07112e6f63984b94a0576be2d2c21719dcd327e0cde41a9865832097622b12404b27801d883aa5b43584acb0a661864e10b716a50a21f86994b8c07d5a5998404f28ad88a95d8186c45061c107516b8b4d16a2b4f16c570552d37909ab4b716830d2bad2d94a68e1e00c394c27518186d239a6e0c3530cc491bc8aa4fc5b0ca70e14d16921626532b4b630cb12544e8292d4ca27438a8bcd322bb711ec4f0d3267715d92e529b2d2d45a10b948287d5b1b45905529a3125a5b2d052ba1b594c2a1b9696e2d061b1063a88d8d0c227943e9df62ada06589287d5b1b4620c68551386845222bb6318730d6d8828611c2b0e6136b104c8aa65435ca65 (by decide +kernel)

private theorem part514 : Excludes 0x20040000000000000000000000000000 0x1d5d11182004000000000000000000000 :=
  splitAt 1 100 0x1d5d11182004000000000000000000000 part520 part515 (by decide +kernel)

private theorem part512 : Excludes 0x20040000000000000000000000000000 0x1d5d01182004000000000000000000000 :=
  splitAt 1 112 0x1d5d01182004000000000000000000000 part514 part513 (by decide +kernel)

private theorem part510 : Excludes 0x20040000000000000000000000000000 0x1d5d01082004000000000000000000000 :=
  splitAt 1 104 0x1d5d01082004000000000000000000000 part512 part511 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part523 : Excludes 0x28014000000000000000000000000000 0x1d7fe957aaa8154000000000000000000 :=
  finishCode 25 0x1ac671545c1a434ec75d3c69a6c36a3519a3a37560ca9958929733488176532a5cd4c2c270da9a7436b2e0a81a6d4cb0a54f0e6758d3ac45333c7235a1846d47a973532aa0aa2e0921e1d6af198d89269b624c9211960c8a99452b1195892c498f0eb5396ae973 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part524 : Excludes 0x20014000000000000000000000000000 0x1ddd49508a20154000000000000000000 :=
  finishCode 139 0x338e2310b812e5105416aed21e1d94730d2338b41722bf6b1a5e2b9716c27b05ba0a54ca69d716c275156c2b9532cd2f23fb28c49695903621fa8f46b60b551ac40d21fb9892328aa1c869166150610cd2b05da1fd4ca6434ee05db4ac21720dda7669d92d2d2b228ce2162482ed2d269d624cd2f0dca99457ea8330a6569055b0afda5734ed6a6c458e46d3b695990c458e46d3b624b4ac57f311506e30769dad4e4ae86c5a762ad15fb125c3b34ad6a62b95329a75a4532c2ad15c999e532b209e358ca1a75d4619c78715f86e5c5321348ca69b338b12653299556aed2f85722bf3c399565329e1c57ed2d830605333891d45122b95aba78f2320ac22069d5415c3c391fe15cad5c136a6588fe2bf695cc495abaf0a82c0aa066c8ff34b54ca09f616c63f23fcd2d15ca9958470afda5eb43623c59159eb125104b9c787660fc751892d20e162bea99457e38594ca475986ec011d671082eda5711d5a46115c0c8c1a161eca21391a995c42d2d2c8a996620a98da5709e5506d1a5b15f58460895ab91d411325ce5712c60eca654b9a8dc12654d1c286652e72d5d4ca1a15e1845404fe0bb1b0c4755328cae1a5b4bd2e647f8a632cf568571d4530cd3b624a5cc1762ad15fb20a83080259c3ec49616a9850e297305da1081d92e687f616ce1f6249e1d88f02ed2e69739c4731246c284915f9dde4b98afd68660a3f28f5846b5734eb1248fe2b964120440d3a9738f0ee2204e512b8a4e46d313389a6c2db298da5a08b33acd2d6229a6d4ca16796ae69d92e6787 (by decide +kernel)

private theorem part522 : Excludes 0x20014000000000000000000000000000 0x1d5d49508a20154000000000000000000 :=
  splitAt 1 123 0x1d5d49508a20154000000000000000000 part524 part523 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part527 : Excludes 0x20010004000000000100000000000000 0x1d7d44f18311120864014004001004001 :=
  finishCode 77 0x13c5613034ea20bc1e1d2c15f9ceda56475944ed2d438a5a623a8044616671000a1c66998afce408fc94f6249a34caa04d88fea31346b4ac57f1a35a56d816048260cc1e1d6c450e8601462a5d346cd2b70eb0cc57ed2b8abf19c470b0afc8b2d2d624995615fab8ca28962cea994d0669b610f4696ca212cea945086879512c96922c9675c42209022ca2594a29136f19415fa5a63c0a994ceaa659a5e12f695c7878f0f228da378ae25264b8b124b3a5a923fcc490dca95cb22a47571833387d46287960fc831523b126418b4cd676a310dcca25696b125b04c1ec3c3a702b9731a56a318ce263f90e2b53624ca31532a8c67b057334ec57e69b9a56a316d12c5a9c94f39db4ed0da85f3f0e7729354c663f69da5a58921b994aec1f510a994644e14621839a76b3b532ca634a7a89659d9ceda7607d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part528 : Excludes 0x20010004000000000000000000000000 0x1d7d44708301100860110004000000000 :=
  finishCode 117 0x22058328b5753190440b6069d730f0ed3b852aa6534d8ae6695b4ed2df378f636068d8506a272af8afd446110f309dcb422718afa87983721534e0ceaa318d36a418d1b34acabe865696a78c836069d23fc2bf33a9e1d46311d46aeda2b8de36029594bad2d0da99d54ca2bf40bca65520b4b4372b2394baa655209a348ff299568734cd4822bf532ad0f62282bf70ec15b232a95d2df31254af0a54f0f0afd3c5b0d3ade2b8d81cee59db125a5a3851448ae5380c1cd2d52ea1e502f1d3545684352ea95e23fc8655a9a95d4bac239892d2d4338ae566b2885a7673b5a9a8c54ae2b9531b0440b5878739dc69b34eab8922d0675697c2b9436cd2b39db4be15f9cee2e1ac3f0d3a6a1c8969624c83b2d0a17d69b28c50e3312437284992de1b95a18931ced266b434b7b1262d09ced0daa6592d2a473a896452c669d551b0570d3ad2d3c39a362329a6ce772b00018e7696f2d09194d3ada2f88a06e54cb20c50f2a4723fb4b60b1cc3f23fb12567728c42d669d8f0e9e220520600d3ade2b8ea0f02bf104c59d3a68c6d4a213f104c47f2ce851d38710c82f6248e14caaa63870a74d09fc2bf512b886696b08d4a2a65510957d462d2b828e641166695a8c5892a6532ab00c2388fe95b3c0c3075a996454caa3194ca2b9 (by decide +kernel)

private theorem part526 : Excludes 0x20010004000000000000000000000000 0x1d7d44708301100860010004000000000 :=
  splitAt 1 56 0x1d7d44708301100860010004000000000 part528 part527 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part529 : Excludes 0x20010000000000000000000000000000 0x1d5d4440c200100000000000000000000 :=
  finishCode 103 0x330f60f0dc4560972d616ad1834eacd650aa5a58929134b7b49e499ad2d2d3312529eb4b4b19c0a62d5d282b110292378969420cd3332386c5456c41623ca15418c64742ab0dd89330c50f23850dca5a60dcb8b5bc6d183aa159a6691358e86e50ef190a5794ca91352eb1242d71289139c5ac496f0c8f1895456a5743f96855c323c879592ca2b22ca44cc8ed02e08816ad505aba08a653c39b88812c8cc1d409a1fcb433074037216cc4ac41624b106624a2050a730b58928814f066f30b58929735298e14d3ad8083e5a5a53c17e93390fec2742110283794ca2ad48fad2d2b60958d3ab4b561ac2d58a56515a1254ca69d532c33d624a4edb0420f0e881942a55f3a1b1254bab2596aaa1b532b1251027034ce1abb8b50bab576f0e9b09dd86e87f70fca2b52b8de5892ac220625c9a74b56e23388812e462f244da56b573c3ba8a21a6d4cac379a5a77d2c4b87e2ce9d35a5b11d4d22a82f8c829955c3c3b1063419a6cce334b48fea25695c47f33aad5d0cb21e4cb2e2123fb4b4d36881a6d28338ad5d06334bd1028319a5ed29884ed2d41899c51024c250a82205b445146f3105c42b5723f95b61c298964b9b07c332385710cb576416ae31392269736959e1ca1721e583a973610ad5e (by decide +kernel)

private theorem part525 : Excludes 0x20010000000000000000000000000000 0x1d5d44408200100000000000000000000 :=
  splitAt 1 98 0x1d5d44408200100000000000000000000 part529 part526 (by decide +kernel)

private theorem part521 : Excludes 0x20000000000000000000000000000000 0x1d5d40000000000000000000000000000 :=
  splitAt 4337 110 0x1d5d40408200100000000000000000000 part525 part522 (by decide +kernel)

private theorem part509 : Excludes 0x20000000000000000000000000000000 0x1d5d00000000000000000000000000000 :=
  splitAt 1 114 0x1d5d00000000000000000000000000000 part521 part510 (by decide +kernel)

private theorem part497 : Excludes 0x20000000000000000000000000000000 0x1d5c00000000000000000000000000000 :=
  splitAt 1 116 0x1d5c00000000000000000000000000000 part509 part498 (by decide +kernel)

private theorem part477 : Excludes 0x20000000000000000000000000000000 0x1d5800000000000000000000000000000 :=
  splitAt 1 118 0x1d5800000000000000000000000000000 part497 part478 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part534 : Excludes 0x88104000000000000000000000000000 0x177e7379a38c104000000000000000000 :=
  finishCode 45 0x1206b1bc34ea481b5580702a81e3cb4721f4b3624788ba86b30eccc270c49519c2953c7ca1d314a1f54be9739a76821695881c0a8ce3c7a97d43f299425286b8f1eb0300bc1e3d50514c643198a9950c25a32cd8e0614ba1652e6973989304352ca8591c0a97c53aa8246e197a5ada76a3f423960d4a73105c5af1f5a9b4ed88acc2c0b42cae697a5ccb4e597620b165a588c2629530a99525e973532cd2b78faf8a299e3ee2d519b0cd4c2c2905a98763417c4b995cda573c7da5e1b50a7cf1f697bc7e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part536 : Excludes 0x80104000010000000000000000000000 0x17d6713c83c4104051012801040000100 :=
  finishCode 131 0x300c82409c180a828856b2c1a68d3b150b0a634e98dcd3b25a4827190d886a35059bc7da76203b8d3b78fa58c458176d2b5a99a7546aa616b189338a5a5e7236149695a5f30654b7111d88ac496958cede4551ac430d3ad421cd22f34ad676917870302ccd8697cc4960ca97d856847313cc4948bb11564720d52d269d6517c128ca614b49694172861b0ae30dd3452ab126622b8846e2e299852c450b3a94d83714c4c3ad2f0b3ac8d85320bc0ead2b60ccc29710a5a4c3a5434ae591b0648ba5419c42d2b622b1242cec2961ec45d2d2b124542d3b4a9a5acb06be350a802d5c5b25a5886a6551acd3b78fa5ae69db07678fa4bd2d6d3b5f1846b1946f0176ae06f54b33c7da562a13c4ca5b037bc7d6a6a653a146b387d09eb53695c7e2985025a4f4532ab8c219856e2178fb4ad8323e2d4e78f90ec46ee2942781be78f987564684f9c52a5f591b4ad48417cc2149798dde3ea35695c6375415c78fc82f532a97c542f1f9892a65710cf1f30eb0658872995866a35519c269716a5a416aae288c40a84ec619ca49697c84f619a995852637697cb23532b87e52db114a048ecc355329702298c6ea5b78fad4de3f24756469c2a0881184c3a2a128dcc495299d65852f1f037a965a57388509e4c1a861d591b4ad09f019d86af1f80de54260b23710c64362481be30e9c8d09f3125c424c39814f946af1f829e6379c3af1f48da409c25ae2bba4be4b5bc7c5432d4d4cad2b48dbc7d904f12434ea88969497c96b69da8a50b210f922e23550cb12651aa8ce310a5a5a5685948ba54d45321f525e96b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part537 : Excludes 0x80104000000000000000000000000000 0x17d471380394104000000000000000000 :=
  finishCode 49 0x12025cbc878f540d3a9c15ae2cd968e49f990d43e1bd69d881641a891c8ba9171a1965da762899484013078fc5732c59e07416086594c25a709f853d64610b4a381802a1bd2d38d0de3e8792d3c759694a99588aa618b4ed2b78f9e2660ca995a565a778fb4be595c5a72cbac8be298ea25a4b4a6439892a6521dc635624a709e200a458542c4978fb4ad48b312454201f8536c45421c1272238da4362c494f10cf285d892461624cf1f650f4751e3f213da5a7593c4968f1f90ee931696c323697bc7dc52d310dec22d848a969 (by decide +kernel)

private theorem part535 : Excludes 0x80104000000000000000000000000000 0x17d471380384104000000000000000000 :=
  splitAt 1 88 0x17d471380384104000000000000000000 part537 part536 (by decide +kernel)

private theorem part533 : Excludes 0x80104000000000000000000000000000 0x175471380384104000000000000000000 :=
  splitAt 1 123 0x175471380384104000000000000000000 part535 part534 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part539 : Excludes 0x80100400000000000000000000000000 0x17d44d381102c01004000000000000000 :=
  finishCode 129 0x581c4621c025cb0878f591343449e85a52a0d0eb4b927ec1b9c5b388522e4779a6ac212b59a1d28651384409cae69da5cdc5b197d4aaf21f8d319466b4b1be917587684759a980a319c5aa2b61591de518864d6967358c6f24accda97394b6e2d3a296952c411642d2c97371699ad1026874e194716cd3b1a5ad2d2e68810c9cd3b1a9a5cd2db2d3569666d23bb8b52e738b4b4a68761fce2d51fa204b4aca3a88815f0d12ba169454325a4d3ac218f1e68749fc6877148a84f1e5a592d2ea308b238069761ac91769d9e3c6fb3884d0ed3b7913c700d3a251985682322e9cd545678f4c14baa31966a0911becd3b61fcd3b23ba9748ba735854278f61ec2a14b49e3c51325acd3ab41a760539a2540300f1ed3b92e6ba34ecf0b19ac2e6b4b5299a7569731250434ecb4b440b4ee5a7b8a589269d4a19441178440aa0d3b925eb4b4b5ac89816965a5bc7d22e861344b58e2d8b4a9699a62f1f7149a1dc5a91778fcb4b5a5cea228a81a25a772d2d2d66878d3a5a534ec9574a996956966c31264b5a54e5e1d4541304b5a28e2d8222a4b04699b569669734acb4b41e8235852953622c4775a59a1de3ec294a9a608a1b86975a6c86b218ad2ccdae2588bac29624c6955a5bc7e23691dd85291731ace2919791dd696f1f614a54d2d66979e3e56b22ead2d746416434e82ce69d9694d12ea00be61ea4a4ed247739598dd25666d224c9c3189615ac542049989292b61fbc7d4a6c3d8892c2978f98d6495bc7cad666d78fca3f984286169db8b4cda689 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part542 : Excludes 0x80110040000000000000000000000000 0x17f447f92911168411004000000000000 :=
  finishCode 33 0x2e8e23984b94f15c1bec6356979184b4a86543c9a5e23b8c8cd3aca210661f91ddc5266b2d286f5300b1cd3b53299b5a57069669aa2052d269d470d3aa3592e693d23ba94dd43c4cc3d440b4d5a632cd587a8817315c411804f0d2f21dd0f2aa306669799ad4ca96523ba20644183325451024774b9a95669591dcd2f21dd0f2e1f94ca67b23b9696 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part544 : Excludes 0x80100041000000000000000000000000 0x17745779c550079038014104100000000 :=
  finishCode 23 0x7418057392e6d615ccb4b220497269d697cd3b4409ccd696e23d89412e55473089b086d0d629d23ba996710a1ad42e8811b2cc4510db87547ea33942e5a523ba98ca38b634e96951029434be70f997c53a3275a5b8b634ea8ce34ea8fe692b874d3a29d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part545 : Excludes 0x80100040000000000000000000000000 0x177456791110068010004000000000000 :=
  finishCode 139 0x381206c0f1e883889737b16425ca609e15cd6833cc87d34ba914b4b299453a9598cd633951f9695a76a63b85a59102c3d9a7621994cab4b69da8fe532a1f52ca29d2b9ab09834ed0fb22056965731a5ce2d5a5a20641a9cccae666b9a76ac2f0d3b4c1cc2b9a7844d8d3a29d770e664b98c6e87d440ac5e142c7335d1ac770e6669d423ce29532a94d27b22065a5a78c6285e621a9946968312269184a7b2596437b08ce668318d2e53d34e9ccd6965a59102c2378b423069533ccb4b50e9a74ace1bd825629d699ad2da76b4b8ace0a59696d3b2b3a5a6716ad2d4ca567621b07b0e825c9a0973511e3e573226c00530e98dd4ca86750ea97cc3b285e52a9a5ce6681d78f9f0f1f610ca655314b73065a5e477716b0664414c4b9b088815517c14eb4ae714b0854caa619886e29230c629529bc7cc5338b5e3eb4b32e84666218ce5c52477519ad2cec78f95ccb4b220543a66d9102a63b8ca1a562d2a204ec521442b3cf1f710ad2cd2aa55610c6e28b90ee567903af1f230a99503b115d0f263752fa995e3eb4d96626374b4959de3e21194b20ab33da995e3e69550ecca298f6169510266b8f1269778fa19d30335c09330e9a5cd0f34bde3ea41a07437856732ec6797b1a573c7d082e21863a00332091dde3ed2b611ec5f10f2c19837a84123b8446420b06586734cde3e47751eb876102b4b5e3ec2923ba99621ea8f4656d3378fa78b234be43cbc7d48a3239e3ed2f23bbc7e23ba78c23d87a2996429b4b453a46178fa19ccc208cf1f6969185a568654b4cd2b9e3ed2f14e918660dbc7c08a04723bca5f9a5e41143399b54ca4b92b9bc7d2e678f (by decide +kernel)

private theorem part543 : Excludes 0x80100040000000000000000000000000 0x177456790110068010004000000000000 :=
  splitAt 1 96 0x177456790110068010004000000000000 part545 part544 (by decide +kernel)

private theorem part541 : Excludes 0x80100040000000000000000000000000 0x177446790110068010004000000000000 :=
  splitAt 1 112 0x177446790110068010004000000000000 part543 part542 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part548 : Excludes 0x80100024000000000000000000000000 0x175cc4fd990412e284100924000000000 :=
  finishCode 65 0x240b0380ea1e3db04e17822ec91734e9ceda765972cdaa0a5d852ad3b2c1a9950ef1a7586a08569db4ee32ecd3b59dc27769d966cd3aea1989e34ed4ca1839462a5d695a14cd3a66d9082a57150b12634b9a767915034ea0be1509175a76957530960da771174543160d68410dc3c10f30a84cda46d23bb88982d873b9e3ea65298b124cda29152ea982a19a5a67b4b49976230b4b4cf2c4939dcf1f53299b65328945c04c1486c14c2cb918661ea92e39db4b54c148bc7e32eb4b52d2f1f8cbad2d33189273b9c3ea654b4c96988c2f1f5329cec31325a5a5a8674c1bc5216034bb886624b88c522e2198929699c4267b624a95e148a5a52d33885e3ea6539da4be78fb06d4ca73b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part551 : Excludes 0x80110004000800000000000000000000 0x177ce5ef39133043c095c00e004c00100 :=
  finishCode 37 0x278ba2409c1a755c7b11813eca65624a1e5a5b214cabf2995892163836ac49624c15b532bd882270d2d5710cf2d34e761bd43cb0e6710853506273b223ce1f13fb12569a1bd4e15c711ca6539da1e437b20c4e36a6558ece2153289fd892a658f85714cac258e76c495a6a19d0f2b539a7655f624b4ee13fa1e4a0590f4532c35f2af91dd89266b532cd2f624a1064b2a9950830a55a5655f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part552 : Excludes 0x80100004000800000000000000000000 0x175c74ef110230438090400e004800100 :=
  finishCode 127 0x581a0481b03c7aa0bc2186063b4ecb4659b4e1ec2c1831e5169a760638c6e699b4ed3c590d3ad3b94b65979a760c7222a11e21fa1054560c769d965d744f127f34ec88e3690d8b12545a69d730e331d254ca46d6249e8c198e3245d33cb4a622e89dc88b296db052168410b4e597231ec619b1148ef21e4c4311de43ca86e78f99e50f258b854329054b60c74f1844e1bc433a90291948ac4939d99e48db2915892d339e3e8775b06d311b4362c4914891b678fb4b5892d3388ee65d2b3bc7d48aa5b2b3c67978fb124702c3f236bc8ba2409c1a75687b1b06f0b368239a5a1bd52db1265a3bc7cb06de34b6624a96c69f159d89259b91814ecd2d624962c53b34b589229d9643f1ec624b085a790f25a788eed2d522b4be78f969d385a1a5b2915e3f2075a5a73b0dec84314e978d2d421e3f21e4b4e59750aa95d4cb24a52ca86778f965d4cb24a52daf1f2cba8ad684e17852d965e69891dd0ee5a769dc87769dc83114eb4be532a708c1e0d821dd0f25a7945a583148ca2d19dca65223a19d45a5a752dcf1f2cda908c34ee148b4ee624cf1f5329d6482284369da40f231869d6f1cc150987622ea0bd4c20c722ec71990d6f1f2c191748ee93d9892e292c1a8d54c2c6160c5431d65a77378da2c80c7351a5b19e4692a5b516a98488f28b48db19e678f91dd4b63819a5a46d (by decide +kernel)

private theorem part550 : Excludes 0x80100004000800000000000000000000 0x175c64ef110230438090400e004800100 :=
  splitAt 1 112 0x175c64ef110230438090400e004800100 part552 part551 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part553 : Excludes 0x80100004000000000000000000000000 0x175c44ef1100904280100004000000000 :=
  finishCode 129 0x711102be3a85a5681685211034bbd86877010a7287cb4e37d52db98b3b8c4237d34ec3758d3aa659a5e6212af960dc05814cb1e3cb07398d2f9a7655f6249066712b4bd4ca36534eb80f1f8b1678f49174532b0fe335a1052d269d5308dd6692a14ccd68538cd65411beb095cc5d1ec7916c57154631680de8df4b1f296ca833805a79e3e29d34ec3459a6a1bd4b4911e001b4d440ed3b61fa5a437ac499a6a1bd4b486c62a0a5a5680d8b4ee439969d8372995ec571c4b09fd89203343ba4f46faa598c9e8311bacd81a754b3166da6b25554b6b425a46ea903c7e0d494a451269d0d4c635624b1265a7b0fcf1ef1f2c5a40b4340802a078f61cc2a1343bc7cb06961a75a5f3c7cd2e45d905e6e2a067b50bc45d089b4ecad659b063c03b420b4ec8ba69d4b4c69d4e0d3a09b9892d3b3278a85a771a763c7a90b43d8983405678cf669752ecb3b78f959cb2ec49697cf1f433a96de3f1a1cb4e59778fc58b433c73b78fa1e5892ea260b42587c3124d2e9c19ecd3b296d27b1e24e8aa652c1c78f480cf6357830678f624c2552b3b8058b8f1e60270902b835f612c66b39da0bd0a6415984aa3d08bb4ac88ec39432c73b3a2cc3d69db1265a13c5d1c034e9107a28b4543349548af1f4339e161bea1e6150a915e3e041881ea3d0a7aced45f0df54b6867694c7853b4a08c542d3b8f1e73b14ecc4978fa96c34269d (by decide +kernel)

private theorem part549 : Excludes 0x80100004000000000000000000000000 0x175c44ef1100104280100004000000000 :=
  splitAt 1 83 0x175c44ef1100104280100004000000000 part553 part550 (by decide +kernel)

private theorem part547 : Excludes 0x80100004000000000000000000000000 0x175c44ed1100104280100004000000000 :=
  splitAt 1 101 0x175c44ed1100104280100004000000000 part549 part548 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part554 : Excludes 0x80100000000000000000000000000000 0x1754446c4100000000000000000000000 :=
  finishCode 127 0x3603c3581ec7113825ca20e025cda0401503c7a1e62bbac5d1032d2c63ec238b6532960d0f2c458abed3361162f21e5e3f15dd4c624c879344a2050ef2875c0401843c79e0a821058772874b06a1d9846a1d8cda91506391750ceda160e622a9551033125866a81a26624a1e4aa6583063cd3b50bb115062a6157e43399b54cb2d2cabea8248d029954c3c7cc492d299ecd2ec498cf2b4b3c7a8c661aa08dc5a64f4189696624b4edc5a7439a668315a59e3da0701103c7ad3e18fb124cba6954b9a2065a5a20a1d8cd697334aab8697624ca27613a97c54296d922aa27134cb4b440b80703588032078f519cc330639d0d4929732c1a98577336c881519c9c25ce2bba91e4409a7569667b94ca88161acc49699ad2caee78f531ac59017f169542b2924cda88105fb4ee622a904cdaa55440a85652ea5cd466a65540d84e0e82c1940f1f69d990653288b6716831d696b4b9e3eb2258de1905dc34aa08d3b9e3e8815f10471a74b4a4479892d3b9e3ec4950eb49e69dbc7d102a5f699cb4b532b4ce440ad2de3eb4b9a765832d2c8813439d0da76f1f400e0580d03c7a0834f6d08ef2995102a4952dc879440b12652c9a75585a0d3ac499c5a87752cb126716b0a5696f1f532cf1f4b1bc320ae865d440ca495229a75c5b220652f98a6532b49e32ea875a7678f78fa98a65699a8c6621b8b54bb30d5a76a1d (by decide +kernel)

private theorem part546 : Excludes 0x80100000000000000000000000000000 0x1754446c0100000000000000000000000 :=
  splitAt 1 98 0x1754446c0100000000000000000000000 part554 part547 (by decide +kernel)

private theorem part540 : Excludes 0x80100000000000000000000000000000 0x175444680100000000000000000000000 :=
  splitAt 1 102 0x175444680100000000000000000000000 part546 part541 (by decide +kernel)

private theorem part538 : Excludes 0x80100000000000000000000000000000 0x175444280100000000000000000000000 :=
  splitAt 1 106 0x175444280100000000000000000000000 part540 part539 (by decide +kernel)

private theorem part532 : Excludes 0x80100000000000000000000000000000 0x175440280100000000000000000000000 :=
  splitAt 1 110 0x175440280100000000000000000000000 part538 part533 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part557 : Excludes 0x80c00000000000000000000000000000 0x17f30a83c000000000000000000000000 :=
  finishCode 111 0x1b0701a056078eb82e89e37069d1b5cb4b3c396ad5c3c3aa8c238892f0d089ce532a5a5a570d4d453295523a789532c92f514b4b650070329544f69692d5a20e2d819683f3c3ab89029550b334eda46b4b4358dae5a58e0643589ce4169e1cb56ce2e8cc1a7514065a4c64358e0569321f470329950fab4b24fcb4b065a966085a9940fed3b716927cd3ab82f87876714caa198882c494b4927d07aa19893ea15989296961ca4fdc452dce2d24fa8ad4320cb50cc49f52db90ba26069d3c1403c3b989631c0c49f624a996389ad2da464b594ca36b5a5b00dc0a85877299496a947624c479532b0e604fa13d43249f5328dad4870a850c3299584ad3b3c3a90c15b12348f24b58d3a5ab561704a1a05f0b56c02e8b61a7507f2d2c16e4b51b5cb4b53294b66229d1548628b5a5b8b496a83f983236b691b8b435a96b5329a765d1c85b0d3ac02916319a8748f20af25ab38aa0a1653286b545338b650d98c470249f945a96953291e64b7863c91aa43907f1174b56a4334eb90d3b893ee2d624a91496a69d4adc78f3918050ca807a1e3d7842aa08678f98c4c66a3f48dad5c16e3818c62a6594b6c2551fa46dcc4b3a8fe259a4bd0aaa65816ee2d92d6a2b52da80c02d5e51f92a50aa78f5abc92f8a56967 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part559 : Excludes 0x80420000000000000000000000000000 0x17f98b80e210800000000000000000000 :=
  finishCode 95 0x380d0320ac0f1db84817034e961e3c39d0861c087d038ca4541ec3635a5a98624f8d0c6a6b4b4b2ca615a58c1e497b46d102b4b3c396ad4cb194da5a6993c39a75a44d11840fcd2d3aa9184cc267d5c0f0f2d5d43331259461cc37d24fa204f0f12550b2d2d61c8a2e3b2a1ad706e1802d5a1878f3311031d14ecad21e2644099850c30644c4245d3c2ad26532b1254be881440cd2d52aad5d20540f1e69994ca96b4306b6b57624c83d6968204ed32925892a8299633e9a64e02e16ae14f86b627b947a715966a77513da8f5e3ea21e3da8150a4f66208a24d3249734cc915144b50681e0855532cb4933ea1e58832cd5a5a67d620ca653f0cfb2d25892e278f1271529eb4b5b85c190440b48b61e0699696ca3f34e9a15e3f312547ea6524ab0ee24ab4d45427139872a6534eb489c1a66433a1e45420a79696f1f34ca99602cad8aa1a659424aa51662086845133c7d06b0df5892289601c861ec2a161eca65254a9166249a74f0f2994f0a6994204ba69d44096ac14f2d2c6d61575a5cc49696b07c6fac23 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part561 : Excludes 0x80404000000000000000000000000000 0x1759738442c0404000000000000000000 :=
  finishCode 129 0xd0320900f1d3c340d3a542f8969624a4fce272864b4aa6550bc62150bca654b4b1252d6c498f0e69942ca1ad5443118435a1f57c52fa99643db124d32d1b8702c493c2ca656249e1d7069dc78752aac81bd90b2d1b69bb124b4a38169bc9695c16af245cf0ea555f12d31694c4334d52d2a21e1dec342c69940cca65295a4bc13ea550dac92f2d2ac0c02c878f23194422a6854192caf1f43a9a64b4aea3c8d4398a35925e94541886f5a373c7d25e6855329a164a2b4b5842f1f0d8c96d834a69993443ac5a534c9e0c21837a9651a9a8d56ae68557125e843943aa659a5e71343cca6578fad5d504814bf2d5d0fac494b4a1654ca96b510d0b1a658930985a5aa654b4a4bd8c5aba189170deb87652aa0f5c5b3125a5681f8812875624a9552d2b834ae4b5ad5d645f13478fc87533796950d2f1f9892a650dea8d514150cf1f230920e78f859e1978a8590481ec34eb48861a6442b38b548628b342b009c09961449c4e18fcd373c3a48a5b84b6c3b3bba8fdc5a9695329e1e716b18861e1e145a1ace270a552db1e1dec730d0a699145cc49389a0c4c3b3c7ca560a93c1643c3829653282a5c533c7da36713987a84f53282bd7c581cc34cb18ae3a801f94ca84705386d5e3e2a1433c879611ca65342b0f6421bc7d0ca685532a99634299be78f8a854ca84270c62602a1232c08d411a1ad83b1985062f1f2a9a15678f954d2d310bd0fac49389856c9063479a6ef1f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part563 : Excludes 0x80400100800000000000000000000000 0x177bbec4624528940a110804020000000 :=
  finishCode 31 0xe427069d6313014aa08e4b48235892b4b24bb28a63c7e4239dd4c52d2d1c0ad2d1028479e3e319696a0c4702d37848af1f697ad2cc672d2d06255369b925d78624925d0c03dcf1f4b4a18569687d69acb4b980470f0246b60b82502833c3ac664b4ad2d0e7092466f256de3e2834adc1870c3cc39141bc7d0e71d656924a1530f131985a6eb4b440b126 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part565 : Excludes 0x80400120000000000000000000000000 0x1779eeccc84128a410124800000000000 :=
  finishCode 73 0x641a45515824aa50b02e8f61a750c334cc49342b48e295ad2da6ea551b5cd235a5b4ee389b4dcf0ee2d342b8b65a5a97e7169e1cd3a9698f0ee2d6c12d2ac0a852df2d2cd3af1f908694790ce69d716b4b5583e0d3a9838b54ca25990fab4b4b7b12508f0d8da36b4b69bcd3b3c3b8b5c5b2995d4330d8532a70ae348f60a550ab216543a685432bc7e2a9b125c5a0598c7f38b5a6e5533f187b0165892c3d80bab4b5a5c7e128f63125285d1c0150a1ae78fad2d0e6c1f86d608d5a5a5a587f02350e6e251a3861d6968358d162a104ccc3b50e8a55ec4e12d2c1f984ed2543ead2d86e08d150bc7e345b8b4303250ac308e14ab0f5696f1f98768618542a5f78fa10d87a56219e61ea5a5603c108342a1e484f3874c7ea5d612c26931fb8b6345b8b6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part566 : Excludes 0x80400100000000000000000000000000 0x17792ec64841280400100000000000000 :=
  finishCode 99 0x531644a0b4ab82b0881641a45b18c25aa47e52c9a14d3a1a5326ca174b4a96e30eb0ec952a438a7a7451be9a75d45a598fe1b5829d87aa6531fc36b4aab0f5ec641383c3c969521a96587b1e1c952969909f1e1d5456093eb625b65a58dade3e4971b1cb4b69bc847418b08e4b486f558731a464092e9478d3a9699e3f123587ad3b4a3c69d7315469047731050b2a654b4a0c4952d82996430a996716b125e3f20d5892855514a44e3c3b20b821078753292cd102c259a36913712954dc4b1d15a6ed3b532cd3725a82265a5a1e54cae0398c8258b6127c51718a54ca69968d92d5c868dca336249a74f0f12d6345998b62995344c0d166299a5a1b524bb124aa72d2de3f3124aa62959347b109f31245421bd337b08980a5436a621907af1f624881631098cde3ea338c42295314a08e5a5925c37af62c0c82d8781a2d0d702bcd0a61d826aa17057a9952469689de532ad25207204ef1a750d738948baa29909e2a1522950622ea87569a6696969a154ca69d948aa655a5c55314aa99437b125d4ca4a9 (by decide +kernel)

private theorem part564 : Excludes 0x80400100000000000000000000000000 0x17792ec44841280400100000000000000 :=
  splitAt 1 101 0x17792ec44841280400100000000000000 part566 part565 (by decide +kernel)

private theorem part562 : Excludes 0x80400000000000000000000000000000 0x175926804000000000000000000000000 :=
  splitAt 4458 95 0x17792ec44041280400100000000000000 part564 part563 (by decide +kernel)

private theorem part560 : Excludes 0x80400000000000000000000000000000 0x175922804000000000000000000000000 :=
  splitAt 1 110 0x175922804000000000000000000000000 part562 part561 (by decide +kernel)

private theorem part558 : Excludes 0x80400000000000000000000000000000 0x175902804000000000000000000000000 :=
  splitAt 1 113 0x175902804000000000000000000000000 part560 part559 (by decide +kernel)

private theorem part556 : Excludes 0x80400000000000000000000000000000 0x175102804000000000000000000000000 :=
  splitAt 1 119 0x175102804000000000000000000000000 part558 part557 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part569 : Excludes 0x80041000000000000000000000000000 0x17551c46802c104100000000000000000 :=
  finishCode 99 0x68188710b56ee3002d5255c695624b8952de78f7b16c522998614e99f466f38947030255cc690d2b25a492e4b5517ce2d5a59234cf6a5d8ab678f34ab00d219ed83f1985a5ac4934a92d545f1a54cbf2915892903b878f6b16c16aa603438a2e94f62499acf0a0934409284a2f249ce360a3326a204956729987266b440a9956c440950632ea91c95671b8cb6b5753299754c2f0d1292794ca71b051a8c434328bc96a68714ecd2d4a3a975e45f1dc2549e162d2828e52d9e14d1255b96ae67916acf22d8c039895b910248d250a38b411e5182e1c5b0d9450aa454b7ae0969945a28578fa58c15e183696c60d34c85dde3ea2b92d2a5b057ad2e61f891548217378fa204c9ab43c7e054a5a5102285521ad2e142a2054c5f066e881624c699330cc4968dad2ccc31a15892a6388ce208969321102d2398922297168cbd2c65a59c5ac2578fa56cc9f3c7c37ac1f98865a5440a9964409908c31242cf05ccab62298c9e06928b99a5696e62484a9614ce292adac75692a5b983e64f6969d25145229e8277327c381696ce25621950423338940d2d2d4d16c2d2ba8c29815ac493ac86c518714c2314b194c586a291298cc350579d2661a8c9de3e933532b1252df2204362c49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part571 : Excludes 0x80040100000000000000000000000000 0x17d513468404290040100000000000000 :=
  finishCode 139 0x1c45d19c620fc25cba8f22a8863788735b17c3309e1c942c499c5aa65197cf1f78fc283435b1252d296394ca969435b78b6238d2120c91ad2b9432c4978f9e1d87a1bd42cca654b4969437b12d5a461ac85914186f4b4b0416716a1652d2a651c09695245f12d2b22994b4b3c7d892d2d891a7559a5a48378fc95b138b08ceaa4835417c50bc31f291b89586a2832d2b1254cab819865a5a2058862833c3a20f1f5a5c451716a9652b709c5b84adcf1f4b181d6522892545a0850b3bc7c8a31885e3e28361a92d4b4ac49791e3f0045886e2d51686f496a48359145b30d43625a56e14ca95b9e3eb4b621ce253c150790f0ede2d04a113bc86b440a58c8f32204e3665b8e36a654b1b12632d96951029635a1bc73189325a491a4a150145b11e506aa5d4b1a5bd23f285c50a47941aa2064b79704a1989229d1999c6d103255587a28578fb4bcb8400d05a1e3e55b41ac4b50c1a51cb4b3895482a3114e9c6d6878f860e4a39c6e246c4a138da98f1f516c283624a205cc255cc49521cee298d62c88a1695b83a4a50b622056973c7c506c49250b10e78fb124506c2992e6e2d250b124eab290cf0ec49614ce2d4b9920d892de34b63aa9de49067558ef2c0220514250b8b6254a964702f1f94b261d92b27874b9b12564441892782d07872e1853247cc4297378fa91410b30a5a5a97378f845e78fa5cd2e73c7e337b0a58360ad3ac9285a632d249067858f12497600e8b0ca51025a52559235644b9a30a43440cc4924f9a2dc5b28adc4e78734cce2541ab008e370c8220491a859987a4a961fc28361ebc7d2e6b8120d4cb029da5a26f0c8cc3d0d08a763c3a204d33127cf0e973 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part572 : Excludes 0x80040000000000000000000000000000 0x175511128004000000000000000000000 :=
  finishCode 129 0x1906e078ee22c02d55c0e82d5b3897314ec55b25ca1f4f05d0f0e381947ae2d902338b4702a2f624a98a3d9c5a787440a6029d9892787408c6697b0e825cb12642c927c53a87d4b9b9867d8022a19716922d6972914c5267d423c49f4b98a74b572e09416ad0fb156d6967874b9a2054b721f4ab69733c3a58be1d048b50cc36314e956d2e6a538cfab4b8cc265f4b989ce5a59985892973581c43a097255b86b6d233c3a5cd702c0f0ed634dd6aed2d94cac19416a11e5304eb1695c5ac298c421b5697a995646b070316944bf348da3638169bc98298653286852e6c493229e1d6af19852e6a829961ad99bd6ae7871adcb576e1dc5005aa8a1e3cb5648d94ca66d33da98678fa1cd105816c4b9b48da1a16624a545886363440925cd32c49947a77584ce87d43ec66951eb125641b0cb4b694b0a54caa4b5309a5589286338b4b9a4e66f1bea1cd4cb1e25496a615a4a88c258022d2d3b4ad2d4cac234949da65a4a87e5a499bcd0ac49440a80a658d2ad3341abc7c91a4973c796ad606714c7113025c9d16624a5cc92ec3d94ca9734c091b25cd4ca67b6248d8e5a5a5cd697310d4ca97324b92e467330d48baa65141a5cc92ee2d90fa45d336923492eb0388ee1e3c972da25ce2d2a8f4cee45d94a678988ba69996ae1774b99e3d405c0c8440fc5abac8be3125341adcd2b241a99411e27b532cc4343ec87d94cad2f047ce1f241bc7d7c61ac35b624a115852a65241c52396aea6513b910c906f1f1adcf1f0b7950a5394ca35b3b4c4432d2b12586aa65 (by decide +kernel)

private theorem part570 : Excludes 0x80040000000000000000000000000000 0x175511028004000000000000000000000 :=
  splitAt 1 104 0x175511028004000000000000000000000 part572 part571 (by decide +kernel)

private theorem part568 : Excludes 0x80040000000000000000000000000000 0x175510028004000000000000000000000 :=
  splitAt 1 108 0x175510028004000000000000000000000 part570 part569 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part573 : Excludes 0x80000000000000000000000000000000 0x175540000000000000000000000000000 :=
  finishCode 143 0xd0078d885c1dc2d5b58d40b55785a0786aa220495343ca655ab9e1ccc489cd2f51fa99514611c8813c4ac66440b4acc42981a563c39d56343a2056aed822063a29e256ae7874b9a2065aba2037d8c9e6975329e1d6aed231264408a8492aa5f98926973a1957cf0f32078792e63c32408f0e440ad5da8714ca65420a5ccf0e49f1e192e65ab9e1ce81e1b58d3b4b988f66119a7569632f6998b5588b0c5cabe27d240ad2dc46b091738b4ca24b916aae8b4b24586564b481f6598b114d0e2139a66c231ba989c916651771c45a05aade26048b4b1c67b34b957e53291145428816a09028e2995a57251c10218396468818106b5739596066b9a56a653c3a2056aea62888813d1a4b11e4702e634be255b12430b389d2d251f532b4bdc4b1c6d4ca865335cc49255a194f0e73b5c1b04c1943c3b5094785366212549944d124b5380e572d5d102ea045e185b4cce56d3b3449a7660f9884e56d3b04c8df634b9c0d3b9102b57650c7f34ec5424ab59dcd3b532b28ac2784ab344ca6543cb126420b4ec952b579102d3b892a66b6a19434ec4a925aba869794ca4958abf34cdcc6a1685b0952d812d50a70a84f0e43f9a5a745429a994cdac499a5a6874b49e074594cad3b3c3a8c62559a750cec6358c4996ae2a12459884f0a48b930714cc2504a990d87272b34e99b4f0e687891669d5abb58921a75301c0a5a4c63295c8f2a659a761a5830b25a4702c42203c36414cb12d56962a14b9a4cda767877114c5a592e4b4b0df5102a65881a63f24bad2e4b98d1d1029479585d16834eb98d2b928e18313ea9949522a18f0f34ec9570a8644092a4abe787 (by decide +kernel)

private theorem part567 : Excludes 0x80000000000000000000000000000000 0x175500000000000000000000000000000 :=
  splitAt 1 114 0x175500000000000000000000000000000 part573 part568 (by decide +kernel)

private theorem part555 : Excludes 0x80000000000000000000000000000000 0x175100000000000000000000000000000 :=
  splitAt 1 118 0x175100000000000000000000000000000 part567 part556 (by decide +kernel)

private theorem part531 : Excludes 0x80000000000000000000000000000000 0x175000000000000000000000000000000 :=
  splitAt 1 116 0x175000000000000000000000000000000 part555 part532 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part578 : Excludes 0x8140000000100000000000000000000 0x1f54bf70e954000400110502008140000 :=
  finishCode 87 0xe84e0c06512e6d6338cc3b80c3530b4b220569706d4cff0c1c2863635a5b12578640ce2980aa50fb2995032b37285c93d532ad2d0fb2d2d886861411cc19532842c35ab375a5a088e220431b2d2ccfe0ad987ad2d056cc1b2d299c56972205505314cac359696697336b0d65a58d8e5a5b0f452255b641e42ada78ce2c82a966169738b52ba82570e830ccf2c490dac6795a5a04e11fa92c186b4b41ab306e2d2e41ba1fd1032d2dc5ac49440ce1d51ea92cce2b4b2d2c81333cad2c1862a9570e36b4b51ec0c3224a1fe6249f064220662491ec6c6b4b7514cb11c50c2ae2205c3f34b4506c3d836b3124b4ab2328c8338e2d9696881061a20659b956c36b1695892b4b845ad2d34bb4cd836c495a5c55b6b19c4c0186722182a98e9ab4133691ed2ba96387e50fa17c5532995047310dc3ed335328a454cb3b8a8268871532ca61194b8b51025a5414ce2d92e288161ec471328b8b5dc621c811532b8b56968815a5ce2d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part580 : Excludes 0x8140000000001000000000000000000 0x1f54b2f19f54500004001100050200814 :=
  finishCode 53 0x6c1884e1106612e6a83281970d1b8b661482ed4cb338ca2d2e33a9a6c17ac23c7e5a59e358662a9622cc49988ad275a5bc7d945a5c675440bc7cd1aaa2582a9314cf1f619a99440a65532ea996615bc7d866c3d96aaf1f661842ad866d9c525cc1b5aab11587a29105da20633ab0a588b19562ad8aa4d1a1a396c6113c671941488aa429f3c7d0e2691697cf1f438a9955c6510db1695102691371a5f11dd0dac199e3ec21525a92e78fa99642d8aa50434d9b884994cac3323b8286619b0f4cbb3c7d6820a1532cc3b624bc7d43e88134199b605bb8b5696197 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part582 : Excludes 0x8140001000000000000000000000000 0x1f5cb2708954151300814000100000000 :=
  finishCode 143 0x1886c0c06512e6bc248dc19d4b4b2205696b21124552c2b9892a6194cae1f615b58aa190cb4ae2d983247b346830e41a8aa65308db2204f8532ca2b622830d696c41810aa2b622830d5033154532b38c202462158a2c55272216e323827dc4aa621ae696827d88b21c604fb30c221c50272c95c4aa6109ec62942db0ac1132985696c21c8a62a864304fc2a970fcc3341ab885c5a95d5aac47b4ae91de15493085f84a2e2d044ad2d88302150be822d2cf0321ac4d2c49619a536624b87d83aca2b8922a867504cc2675a58aa4d36a62c8dc169422f156dc5aa27440846e28d86c5c5a85b91027c06d650fb1250b6b4b712c1b5624bc8ea218b221ccedb20d5c5a599624b4b641ab4b641a969455217f9892b4b716830e531ac790b4aa1b90e6a65523b4b5c5ab4b42c99c6338c811716a1f5102c49969629159150624a50a621809f044ce2d4ae89a649cc2a95a59086532a16c13eb4b9e46e154523a096532b8756966555a5c4212ada995436849855247b8caaca2c8d63705a53e11026519c5ac2738dad2cab73125c5ac2994ca33f2adb125c5ac37986609b154a2056533875832e2d42d8aa42f6881591485115c43013ee1d811295d622ce2d624ad2c2ff3125c4309a5893216e716ad2c2feca2b8aa19d45531a6d046e16444084ce087a985026c49513cd2d5a0a986412b1250b73124362a616964408a466715c148b308411edc3f34bc072c4942f8ca653080e4ee275d92e265f409a87d4c28139c3ea1b61ac0516148d0da5617f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part583 : Excludes 0x8140000000000000000000000000000 0x1f54b2709954101000000000000000000 :=
  finishCode 107 0xca1e3dac7714c6e0b4a82308881624ce2d34a830ca2f38a4d36c43532b60c22d80c3223cc493be86c4ceb1a5cefa65d888e82351cad5522a69b33a865e624ae8b602ee48ab0f434a1b1620a4738a52e6197716a996624af07519c5a87d154a996611b8b4a46bc308c82b80bb148c2a962499d4ea321648dac49624c1b55a5cc4934d99d5b83e050711b58926795a5a995904b189311b586b04ee411b0d5892283924ac490d8b08c82f04718c1aa6561e830c16e2a96f1b861acd2d0d691dda660c355186b31252e61ad285ca65291a5ce143867578750d2f3124cf287d4215c614c91570f8a0c3529299a5aa5d4b9cd2d989228752eaf0a65986ad2d52e99d4cba69b622cc4969691dd4caba3780b56e1dc23bc881714cb291c49a5d344b99db648aad550bec4504db126714b1144fb2994712bc290dc0aa54bb286cd2e8810b4cc3d23bc847624a20530571892099988a94594ba9735a5c113714a205c5aa8290a654417832eb126148865cee31e35836283986a97398364775a5b125e451154622cc1b154a11d486e1837286ccbae1d987aa319836a5d624a526622a90973969629123da5ce (by decide +kernel)

private theorem part581 : Excludes 0x8140000000000000000000000000000 0x1f54b2708954101000000000000000000 :=
  splitAt 1 96 0x1f54b2708954101000000000000000000 part583 part582 (by decide +kernel)

private theorem part579 : Excludes 0x8140000000000000000000000000000 0x1f54b2708954100000000000000000000 :=
  splitAt 1 72 0x1f54b2708954100000000000000000000 part581 part580 (by decide +kernel)

private theorem part577 : Excludes 0x8140000000000000000000000000000 0x1f54b2708954000000000000000000000 :=
  splitAt 1 80 0x1f54b2708954000000000000000000000 part579 part578 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part586 : Excludes 0x8500020000000000000000000000000 0x1f7a7b48d5852a0214000800000000000 :=
  finishCode 41 0xd02c8ae1225485812069dca65396a0d543ae2d34e9e3d8451486263be92dc13b3c7c34ea6578fca5571699554ca4b734eca6525bb4ee41ab8b4d3a78f258a48a42994fc2a4ca5f256a92ce7aa038b545330f4f1ec239c3f20adc4a6553c7a8cce7a9038b4c530a5569683569d9e3d4bb30f495ab4b261205d15c34e8a56716a1ac91e1879e3eb4b435a16678fad2dc5a1899a6ae2d3bea8a54cab4b521305712004ca97e3c69a74c531e3430f062de3e87d5328dae518bc7d4ca69d31c9a76 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part588 : Excludes 0x8d00000000000000000000000000000 0x1f72e36bdd00000000000000000000000 :=
  finishCode 43 0x198681ac6f1b8143cd2d0cf9a6c17e0c74e0176aa38b65329a44d36e2d94cac49716c0279c3ec490d3b8b507ac3d53299fcd360bb5816850016a90380a29851678f4e14cb066dc5b2996145a9256971c4d46628b532b125c5ae2d80f2083518a994f1ea298d220b5716a48ae38b60579a6ca05d14caa21a7584738ad04693d611ce2d9a7731248ee47794360af716a80671695c477715a1f4f1e68d4913c5a5ce2d34e8a2da4b08dd09e0ab53282ae (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part589 : Excludes 0x8500000000000000000000000000000 0x1f5a634ad500000000000000000000000 :=
  finishCode 117 0x6b17c59134680b4ac2330c81a0e25b82ecaa7061d4ca4b1481a7702acd3a78f5015433a94d61c4ad2c156a559e3ea5f8156aa20069b427c0c750ea1ad4be67f135c86b532a97c926c498ceaa5f331585329a460c39a754af21f589216378fbc7e5a5b124cea69b701b86617425bb9868d836ae2d94ca0af34dc881716aa8b4b90d6f1f05599fd3c0dac76d3c0bc7e18aa8fc88e63329a86d496f299634d82fdc5a1b16e14c38124440b20a656914005fa92678f9e3d4933875c5b1a74cfe69b256c67534d818e338b8b598640d0702fc95b1e3e5a5b4bcd1acc29956960738f1e69d256a97e0cdc4ad4e1b8338ab8a038069b716c4ad440c36b716867d8932165c3e4ad063b80b22084b15a5c881145cd3b5a5a206421a76e2d94ba8815a58dac28318cdc42a1b70eaca427ec49716cd3b2569a6d484d19024798ce715a11d46287d69d831dc3f297589287d258b8b634eb4ec95ab4b9b849110268130675321545a5b80d3b7169a6d0fb24ad2d6a1f943f2994e9a78d78fca1f62282d54ca78d8ee2691716cb4b348b30be320e2d81620b5551e3f21cde3f0a550fb0a55453294cd1ab02a090066dc5b02c50c2d3b3c7b8b605aa8ce34d82d4f1ee2d816a68d (by decide +kernel)

private theorem part587 : Excludes 0x8500000000000000000000000000000 0x1f52634ad500000000000000000000000 :=
  splitAt 1 119 0x1f52634ad500000000000000000000000 part589 part588 (by decide +kernel)

private theorem part585 : Excludes 0x8500000000000000000000000000000 0x1f526348d500000000000000000000000 :=
  splitAt 1 101 0x1f526348d500000000000000000000000 part587 part586 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part592 : Excludes 0x8114000000000000000000000000000 0x1f546b57a19d154000000000000000000 :=
  finishCode 33 0x188300e85e12e6a427819b619c69b62491fcd3a9234ee33ab1265f1cc0569a6e624a9960269695c4b3064c8644714ab4bcabe69169dae8a559882d3b60c8a558921b14accc1969da8a4b4ae6066d3c346b8b6532b4948fec4534eb126424a8752e309fcd3a0995503361738b4ac49716b4ecd22e2d8176d3b731545d1a766912afcc453319a754cb190d89269d989213384b264369d91fcefa69d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part593 : Excludes 0x8104000000000000000000000000000 0x1f547251a10c104000000000000000000 :=
  finishCode 147 0x160601206b0f1eea3b8bc3604ad25ba7085990fa69d2c7a5ccc872995a76e2d34ea97e34eb8b54cad3b6c108191c973251960c94725cda7669d97405dc69d619cd3552ab4ed4cac494b9965d880cbca5f05b82ecb371a75505e13859032e59b3c0ca6505698a652ab105c5ad3b5217c550e47168da76e2d0548aa564134c0ad624a4fe2d1b4edc5ae2d9a76c41154ac8ce0976716b105a7676161bc731128cd3b7169e8973391c51741d820d832a49622b8b6532b8a44eea49670d06d3b4b9b8b6423a4a4552e2992b200f7319c6615462095a2a92d2c6832c582ecd07168d7465168058c6752cb82d5c5b21341764ad33a962d302569d3652f9d36621a94d4bf12b4b2e9738552cc3b89c12b4b4f25cdc5b1c8d0e25a31b8ce2b33a968d886a65348a5ce5309a6cae71c8de3e97325bb58ba33069d5e15033ac2a949fa54d89312dccea9174d14cb34ed2e64a351ec1b5532a8752e6a5569d9a3669d959d78770ae712b5a7724fcceaa658c864a3331b06d466a5569da5cd4ab0aa5dc6b1486c1a76499256ae8583622ce2951e86c545338b42df3604b7697cf1f2c7b4ee78faa8d8328b41a354ab34ecb06a3d9c5aa65622b0d4cc6b22482690c4ce2d532b10c9131cb5832e2d716c922589a21b652f8e24106a3390e2a5f716b10e7168e25856a65716cd82e8a8292d20624c96b529960de3f24bc16b294cf1b2995866a49624b8b5c5b01e5b0551783e10fa0bb3469a440cf34d48e2c3d9a76e2d5a0cc730654aae2d0b7b4ecb06c1994aa663622af0c02e8c2b909a0b305d8c3e715b4d5842471532b0f5c5ac4933acc1994cae2d624a1352434ea0ee1c4b8b6 (by decide +kernel)

private theorem part591 : Excludes 0x8104000000000000000000000000000 0x1f546251a10c104000000000000000000 :=
  splitAt 1 112 0x1f546251a10c104000000000000000000 part593 part592 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part595 : Excludes 0x8100004000000000000000000000000 0x1f5c67c08110106008100004000000000 :=
  finishCode 125 0x6514c5f1102e6169538420d366838067549fcc1b532831cf1e29594ca1b1223cc4960da99418e78f69dc78f063b38ea0dd54cb3124cf675d3be86c569f3124b461a93bebc7e624a17d4ca6754f06cb0694efa2959a6a4b734b8695cc4e1c03319a6de4427c2a943e92c634acc4933daa0c812c542b3c7d89264169d993e624bc7da77031c552e0260d021cccbf11fcf1e4b76610d609d42dc63978fa17de3f09ad242f1f9a7659b25ba78982e869788fea574b09a754834bc08d017ce1f32f9a1e099957da76d3523f9a75077097cc722957317857108624ca652bb831cf1e675341b30c0165e2d1aa857f8d362a9063cc49224a45da764ad34ec1b1513b4ecf1e69b79190701e3f166cd3a2a94811434e99e6185ad4d89255f53291d5482a15985e1b569699c6699a8557c624ca65701e3f0e2542a83d258a8562a4b4b5482a6596aa4b1063b80a4189465770639e3d904f0abf29946be69d2afca15122ca1569c8ceda66663532b40c02a078f5209629634b625199e4ee31d05a5ac358a4a1553a0a0d643e92dd504209124b1695c17f19fc639710a99443700f47124b769da0d4d3aa8320c009ae5a78a150b2a6578fa1f4b36921863a87f19f907444287d34ea9952e321cd4cad3b90e68475e150330926902994d3b08b4cbe9533b7b4ede3f10a5a5a66d2d3b08a41a763a68aa495ad3b94aeb5532fa8ae4099e3ce7ac2240a41a75a7712b505734ece77165c55265d808273b6159a75843c7a9954571a7452a66d34ec73d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part597 : Excludes 0x8100040000000000000000000000000 0x1f747640c110240810004000000000000 :=
  finishCode 151 0xd818088300973681283c7b98ca28f669999d569688178f9a3564622c2a95a5bc7c912d2d9856629716b4ade3eb4b31cc881314b4cd696f1f532c431695a8cda4ef1f7316434e8aa4d1a09d8caa64f5a5cac3c7d69f28754be6390548d76142a87549294328a6398aa2956716826569668d34ece1d697ad2d1025a5314c88104c96942270c3da5e69d5a58aa652f9a75696ca398ce1a352b334d4b4aa49716a95425f1a7543b1a74b4aa1d8d3ac01c09032878f730e4399cd3b5a5a204cc66714c1845e0c4524c881244b4ed0c2873531a76d2d986a87d5a58655102c359492ee28ce440a92669dad2d10329250fab4b908e69d621b4ed9c0a0c75150eb87d4cab4b2d2a0d50fa8818e8318a4d1268f249b4ed696ca398c819fcd1a5a59102c434279ccc552573261dc5a5986e1baa205c57050c6961ad889a47f3449a0a615ccb4b0264ca2881399c4935a5a876524ad2ce66f1f249cb4b50ebc7cae65738f1ef1f73194640d3b21f4d1a567338b4ece4590cc66711c0c5a5095ca625092280ae0c1e5a59a6c11b169425687d6978c1d4ca5a59102b4b183844e5a59694137044cd1a861986a5678d3ab4b32aa185a76a6590e687d24995cdcc55140338b3868d3c7c87315495ce34ea11e43e8aa5583c7cd3b41acd354409cccae678f3410fb1e3cae678f8e66b4b481a0520f1e9e159c5531a55a76b4b34e9a26451a761ad9c3aa654409944e9b2205c5a12b18fab0d625069d2d2cb4b440a9967169695e3f058da762a941184f11dcea2a657169695102a659e3ee2d6208694b4a94328ee2a88815f16973c7cace5a531cc4939e3e5a55616c78fca65494b8ac1562a92814bf310dc5ab4b137a995e3f3c7e5328aa4aceb20276244a8a678fad2cd050ecf1f2b3bc7e51999b4d2aa65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part598 : Excludes 0x8100000000000000000000000000000 0x1f546644c100000000000000000000000 :=
  finishCode 143 0x3b83c36514c4a0f8440930922d2d10532b06e69a8655832c332d2b8b5905a1a77157c8eec3598871695906b1bc716cd3b05f91de716b4ecabf11dd4666972c1b4edc5a78f8cdaf1f2bbaf8de1695245d148532c86d3c6c93141da9958931d0d04aa654c114328ca5533d808e498960ce86a154b9b4ed09a78f88eea5f88eede290922d86979c42d3361a9a750be87f251c295905284d11dcc35523a5cde3e83b60e831da763898d3a9a358b01694d3b15dcf1e6479606018930264aee78f622ca554b9b1261c4b8b49c716911643691b5076c33524c0c769da68e0169590671e3f1a7418ea5d9c5af1f34ebc7e4b9928d9041dca6505f9a752e72855c06713c7168315e3f216d4ca69d78fca656008dac439e3ee2d3c7b4ee621b08d3b83620bf4b14ca94b9a7687f31cca296f1847015c062a5ce52a928d383c7c7434b9ad2e5f15c532a85652fa8ac3620bf9a769734b0c38969cb0dda732994cc697352a831d442518e2652fa4e634eb49cc82a65331a5cd84791746b1802479a74abf25ccf1e95d9022d2d4b9a4887f9696c1b32fa9954931e3da6a74d523cd35714b114cbea652519d34f1f25cc94669d9243e160532bc7e5a5b4ed2e684031e3a1b4ecb06e2d818ec49331bc7da76d82c0c015de3c7b58ba29264b9b12471269d624c0c7716b1267168e25546f08eec358186663716a1fc82730a587ac499c5a85b0638e2634e91dda76b43789619b4f1f1a5c35b34b5876e2d3c7a7819d9866d2d500cc73c7d87a4714119e3c0872d1da66e1f624a8cc8e2471862260d696bc7d892167716b0f418e78f (by decide +kernel)

private theorem part596 : Excludes 0x8100000000000000000000000000000 0x1f546640c100000000000000000000000 :=
  splitAt 1 102 0x1f546640c100000000000000000000000 part598 part597 (by decide +kernel)

private theorem part594 : Excludes 0x8100000000000000000000000000000 0x1f5466408100000000000000000000000 :=
  splitAt 1 98 0x1f5466408100000000000000000000000 part596 part595 (by decide +kernel)

private theorem part590 : Excludes 0x8100000000000000000000000000000 0x1f5462408100000000000000000000000 :=
  splitAt 1 110 0x1f5462408100000000000000000000000 part594 part591 (by decide +kernel)

private theorem part584 : Excludes 0x8100000000000000000000000000000 0x1f5062408100000000000000000000000 :=
  splitAt 1 118 0x1f5062408100000000000000000000000 part590 part585 (by decide +kernel)

private theorem part576 : Excludes 0x8100000000000000000000000000000 0x1f5022408100000000000000000000000 :=
  splitAt 1 114 0x1f5022408100000000000000000000000 part584 part577 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part602 : Excludes 0x8400110000000000000000000000000 0x1f796f0c5443528484111100000000000 :=
  finishCode 115 0xca298d62c8941694c8440cb4b5c184440ab8a1d8d22e2d3199a3491ea21084972a4c30d5aab8b4c66187868ee2d41ece2d8d36861440c97310585aa15319bc7da36e2d36183b0a55882f1f970610e831a35c5a48f716c68d623cc1d716ab884248553862ea2b5329a44d1b3085482881144b08650ead2cd1a8811a3cf1f532b4dd102a2b5c1c5b0a3d0faa4952aa2058c716c87314aa48659988ed23712b104ee2e2d9892951620b50662f86c2995385718c731c5728ac52ac412a99a4491f0a55697055cc52c412a9a906042bc7d696c410da954ca40dac6836209a0e0dab4de247bc7c2eeb4b6315c5c0c53123cd36a22d2cc6721f5e3e29550dc66750ab46d441c4c49712acd2f623b10542aa3169bcc4124bb4b542b1a0cd3690260a2318a41852ab4b1c4a1cd0fac218a61c498a65a5c32f0c39d75892a31891ee2b1c4a905a36f1f5a5c90308ae27048f2a9ca655a5bc7d0d6e2d14aa97678f9b07e1d08474358dae715a97449728ad88274178fad2cdc045cf1f5a5a86dc56b55084cc236969d09814084218560716c18752ead2e78f8d1e532ad2de3ed37830eb4b134cd37532a8c54bab4b78f861e78fad2c4c321f5696a5d78f8a54dc3a108532c09961e8285482f1f52eab8f1f427b0f652ab08e61eca1d70fa995696c49840a62950da994142b4b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part603 : Excludes 0x8400100000000000000000000000000 0x1f7169094443008400100000000000000 :=
  finishCode 153 0x2e078260d61e1d3c730d3aa0311e39e9d7543648b78f96956964956a0c839169652b9a6e65533894ae69199fe532b4dd102d2d9c56629117b8a460e11769ba205696d4298ca24ee69ba47cb4a76d9a5a0a913c9e36142b48e69bad2dcc6911c5714469d99fc96b21854af12d641e927d0fb213c36a4a152fc69b53296954c440c93b055969415718a54cabe2c8771814aa1d52482accff28ccd1aa5525aa2065a592853c5d16c34eac8ae18a6532b4dc9160a5054a2065328dad69648b714c7137169a45e3ed1b24a98e6222a2046d6b4b254af8a03488e122c92a3758eba77d69bce2d423a3868378fc48f49c9cb44b33c7d2baa65716ba8e2d5719425acd3b33f9e361b6b4de423b4ee69b954d94716ab8d378cb212d988e24d190a204aa734bde3eb4b5713873174348b48881908e21969d99fc35a28933fc2712d292d669d99fdc5aa2389e0578a246d702bcd0734d661d92d4b4ae6348be24849575194532b8b60579a6cf031e35c5b1a6c15e0a98d3ac496b13c570516e2d34ebc7e411b8a491eb4b348bc7e423a8c4c1aa15491a771a6d892683144cd2b624a1f4d1ae2d250cac328a634ee4409694d3734ed89268349cc95d396a994d3a8618d069e2b869d6014c054a1be532ac84f030dae5a5b4be5a5a994b4aa630ee0d296956973104156a655f1b82d2cd3b5a5920492aba2c89e24869d75144532b181b5852a7719a5a78d32ccc4978fce29144a5b4516e2d8edac49751c5b299587b38b584e69d94cb0245a6e5a5716b58ba16869d69acc49389b4eda6eb4b60ea1f5c5a66751180613ce2952eb11da762951c4cc4943ea95e3e1c5ac49812e6595a5999e145b4dcaa734ed69622d (by decide +kernel)

private theorem part601 : Excludes 0x8400100000000000000000000000000 0x1f7169084443008400100000000000000 :=
  splitAt 1 100 0x1f7169084443008400100000000000000 part603 part602 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part604 : Excludes 0x8400000000000000000000000000000 0x1f5121184000000000000000000000000 :=
  finishCode 99 0x370ee3802d55c078eb016ace03c7ad063b8a97d4ca8812a9c91794aa10f78fb8b56aede350ca2b08a125d544e1892389716c55360eacf5a6a295594cd35592b1263b8cc495a59e3d544910471e0589287d532b07471276d852ae2d624a1f452b2974edac4914ac78f14acf1f3c798a678f8d54c96a5d6248e24b57380cc0f1d70065a4fe1b5ad2da467872d58e2634ea0f6532b4ed6967872d596ae701201e3ae89a1a75b45e1dc5f096e86b8ccec495329694b4624c62f43598a669bb125c5687d55140348c7871c49a6c6b734ed07e91794bec49532b4ee52a9696624c87d69daa0d3b866ed3512b886c12a851624999dc5a787551c5ad3b90fac499dc3c3b181b58b4ad2325bb0ce524850e69b8d6d25e69b532aa07831878755178524ca6569db0ccd1a19b4f14c619cd21594b12435209b52acb5534eb125a773114cc6a55697ca290cdb12436aa498d3a19b624ac0a6066d7c514c7135abb1241325a5513cd3960e9c4da76295624b126389ca6505d9a356ae923188402d662299d4d22aa3a869b29acc492d2a1456aec2b05dca5513fad5cb4b34ec16ac493d1892c45986269d2d289fccb31e340c31855c3ea1d05ab8b56aec49 (by decide +kernel)

private theorem part600 : Excludes 0x8400000000000000000000000000000 0x1f5121084000000000000000000000000 :=
  splitAt 1 104 0x1f5121084000000000000000000000000 part604 part601 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part607 : Excludes 0x8044000000000000000000000000000 0x1f553071280c444000000000000000000 :=
  finishCode 97 0xd82e03c7540b03c39d0b570abc9733e1ac4908f68479c4282d5329696154cd37924750f86214ca3338cb282d19da5cd543bec65934d91ee424c69b697a5cda36d37716cd2f691b46cefa771614a1452e62758b4ae2d6202cf0d6d6ae973500e9b0dd4b4a69b5ab843e2a1b12588301ac4b9ac8b6169504b0aa50dad239a6ed3785530d6e691b46ca0036c247083a0d58928592ada994e8195c343436c2a9438b00b82c0bc1e3d505a1540cbb106716a894b4a0a57516ae77d8f1a85f532a1a66b08f72d5cb4a7819945ab969605abc8c458f022a91adc2914d11c511dc490b4ac41871278d04dc76d69bcc496968224136471835a5a560c869661ab4b4b4a92047e28ba994ebb34b5ac4d1dc380b4af1f96aec3588f6c29716a995e3ec43909af1f05b86b48e2922a08719852e2d532a1165abb8b64c1242419e3671682d54cae2d816b2d5d4cae2d28bc16f125a1ed892f1f532b8b4f1e502d5da4734dcab635b9a46d1b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part608 : Excludes 0x8040000000000000000000000000000 0x1f5524300804000000000000000000000 :=
  finishCode 93 0x3b8a00b5570600b5651f96ae927532a2049563c75716ae78d871269b1c4cc038066d8d123c73c7ad0d4120524f24ed4ca4b54b9c695693ad2d2e7055c2de66b5a5a995b4532c481154a1f6518b1244f2c40f1ce85c12e6a82f07873c0cc4933f956d645a5a20608f8e2589282384b66632adcb4b42ccc4913c8aa4ab6ce2f08e0aa52432a9d461b09e05c5b2545c4a20d59eb124713211cf0f2d2d0233125832389716b38847855285b902265550188700b56c82d2e693bc7cf1e4b51e3a3878f43ec49743ecc49532b8b5e3ed42d0c802f624092d5bc421644b1c5b294569668732e86b64b9c4970d6c65d4b9a97608da9342ee973716cb4b255a995544b9c481438cc194b99905c04c0f1e3c75e092eaa0da60d4a1f5d4532cc4933cad5e624a86cd2f2974ceb3186596414ca67528fcc45255a49dc4b047ca46c4952e92ae4c078e8e24f64b6b4b47120a54b9b12492ea631255c34a91260d4b4b61c4ca6533cb30b4b4b9a0d661a9c6ca46363033c013621a0d460e34b (by decide +kernel)

private theorem part606 : Excludes 0x8040000000000000000000000000000 0x1f5520300804000000000000000000000 :=
  splitAt 1 110 0x1f5520300804000000000000000000000 part608 part607 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part611 : Excludes 0x8014000001000000000000000000000 0x1f55e9076488154000511200801400000 :=
  finishCode 33 0x1604912e6c61d88e199d54183cd3b13c9a6c36b34ed08a5a5618ca550d4b1159c624c6912d282ecd37215cb4a8431256472cad492659671a77044d4925a5908aba16958926438176c45908ad42a8e1f848ea5f69da8ecd1a6916b16477108b34ed8926755ab9694ec09ecc4543dad5d89267531ac001241b4d588ac3d05d82ee71699d4d3ab57514c82571699d56a6b5769dcb57 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part613 : Excludes 0x8014000000000100000000000000000 0x1f5569d720e9154000400001105002008 :=
  finishCode 113 0x1dc5f14c480b4a3c3c8d3b5d18c34ea10845836a28941da4c605da16d8921b5498c85b624a38e6318bc1e3649e9a352db306490678d422998d08b3124ec2c33396cc193bea8ed8670dd630a850d8321a92afa895885d1e4611ca6551fb12435284534e8a56532ad0cabe19b0d4af08454914cb1a6c4fe4758ebb14c5a423750d2ca6532cb10ce2f0c030ce42291fce460bb0cdb18ea21c6532990d466a5523f9c8e5a998d508b297d8924a28fe422a8cd4cac493b8c8453c6a994c8619b8d1a8450daca6532cb125d4631b441dcc49532b114d2247f0d8af0c45825ac493339a754ca69b2afc69d331a9943371964d3aa65624b18bc300d3b84f269b05d8da634da1c48eaac309e68e94c4f02845390a4331a0ce616b10506734758925199892833620cc49730944818923c1b0d3b420cb32cecabeba297e60cb09d8822238d1aa3b23fb06578622c68d241c643622bc855f833669d241ae855f983a47f8abec6311651f89fcd2268d525c82152fb0cc336bc2786913a0c6674b8ad0cabec4123fb006c309e714999cabe6439a3a48369db11e622ad4d83a66769da40f20a5567b3484712c1d924b21fd652971321a00ba11fd85b21c5a5a74142d9a742c334d4e82a6388f2c4169d928c03124d3702ed4bf20dcd3685b69aca656199a4435269b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part614 : Excludes 0x8014000000000000000000000000000 0x1f5569072089154100000000000000000 :=
  finishCode 127 0x2e0e61e1d643f18c624af0d429962d2ad5dc5a1a93489a6dac5f0b4b1dc4352ee2d5e23f992e049a5ce69d8a25ac510b4a37192e23894b9c971189cd3b144897432a9e2889a38b6040969430a093498c77153189fd452d2559e9d762d2a5ce5e035b02ccd228698cc6d3b4b9ad5d005e0c87298d09a68d7169a451c5ab84ae4b9b4eccc6e2d9c52829622b4ec33725cdc5a6915abaf8901695741b2ca630d29a7431f2885c5aa634b9cb574818c34ead5e23f864e716a98d2e72d5d60620c05112e6a6268b2278d6025d44338b4b4a18d9892e2d5f14cb21c4512c492d2a1c62afb8b58928e38b4122e298c2a93d12fb11d05a96d114c84d5d18c13fc85b510b8b434a2952afca63716cc021072157db4624c26514aa1c4513199d0db38a4c964a09fe34ea9958920bb90a2a1f08d849c4fea65370e833104d3a86d19bc38932cac8c453e1b45d17c69aca632d286c50bea65624c85f4b0cc49422b8b54cb084634e9694ccea658cceac2e8d620069d2d2ca6569d85cd7c391c86969d82ed2e31145a76965852ad3b23caf817369db8b508b298c4a2a65526c2211ada48ea228a65716c961716cb2b6209525892f206a44fe781906696d12dc723620c277714a8ddc5ac496a04ff0cdc2ee47934ea994f1b05dcd3a55f360c04b0abeb20a55a731465a5ae1f624a9943625a5040c84d333ce2d60cb0ac17616b595cb5369d85ad0db38b465ed3b (by decide +kernel)

private theorem part612 : Excludes 0x8014000000000000000000000000000 0x1f5569072089154000000000000000000 :=
  splitAt 1 68 0x1f5569072089154000000000000000000 part614 part613 (by decide +kernel)

private theorem part610 : Excludes 0x8014000000000000000000000000000 0x1f5569072088154000000000000000000 :=
  splitAt 1 84 0x1f5569072088154000000000000000000 part612 part611 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part615 : Excludes 0x8010000000000000000000000000000 0x1f5564060080100000000000000000000 :=
  finishCode 135 0xd03b8c40b55a85c0786c816adb0690f0eaa2c848152ec881489998ccf6c49300abf20ed22730754bac2d94bea5d440a8a5892a5f94ba9132afb124e0440cb576f096738b4d2a86d044cb5797c6414ca295922666b62492d522b1a547131a5d892b825ce240a2056ae7872d5ad0de3386798d0e9739a6655f51e957e699a5cd2e7378b8320d4298982204cb30e2494269194ca871695b4ed6aeaa217e3a8927cf0f12ad6af1e1d10267594ca8815abb50c02994d0f19ac956a5d866e78d624996547b19ac8ff2204712d42e06591e1b006750bcc85f69d925c95669d90fe74299590259c641619b4ecd2b28eda5ac4952e997619b927d58620903349d69697334e96ad704c01471a550e21833259cacf0e679988e871325a1b4d3ab57122cd3b6939204d3ab81a0d83387875a0cbb29752e6c4932592056ae0b3518c64b716a5cccba973890264b67142b38b56ae43f13ba934d2a0b332146328ddc4aa5d624a136699b8b50dab57699cc492459134d2a7876c0abf34cd2e6481988ad43983c3570ec34ecc4925aa1b4cb268363190348b4ee3c392cd4cb1695482a638d3aac320671942a73b6979284f0ed3b4e0ce3285510273b532860d483125d42a1538abe78764052b34bd2de86d34ea93639da05c81a639515a5c54ae5a5440ae0ee298be2205742d286d63c39a7584725cdc4ab4b49e9df546ec4914ac69d2af9e1d50370abed3b3c38a2618ba1b585b25cc62e289791ac610d3a167836a973906e96d696993da7725cc902d3b92e6b5523686c4c9e19592a23892409a75584b9b58d3b51bc375000b4752a2e272d2957c62ee2d34e92065a5957e (by decide +kernel)

private theorem part609 : Excludes 0x8000000000000000000000000000000 0x1f5560000000000000000000000000000 :=
  splitAt 4337 110 0x1f5560060080100000000000000000000 part615 part610 (by decide +kernel)

private theorem part605 : Excludes 0x8000000000000000000000000000000 0x1f5520000000000000000000000000000 :=
  splitAt 1 114 0x1f5520000000000000000000000000000 part609 part606 (by decide +kernel)

private theorem part599 : Excludes 0x8000000000000000000000000000000 0x1f5120000000000000000000000000000 :=
  splitAt 1 118 0x1f5120000000000000000000000000000 part605 part600 (by decide +kernel)

private theorem part575 : Excludes 0x8000000000000000000000000000000 0x1f5020000000000000000000000000000 :=
  splitAt 1 116 0x1f5020000000000000000000000000000 part599 part576 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part618 : Excludes 0x2500000000000000000000000000000 0x1fd2c8967500000000000000000000000 :=
  finishCode 147 0x771c06d18c570cc06392b496e0b790a6a6505bcb23704b1671a43c7cd3b44082cc182b02e878f139c22148ba98416228b8ce31d65c5a78f98928814814c3c7a5a67169c86719a5ef1f52cb4ae714b4ec166a3d3aca91605d99c54c145c1436989d14ce2a653c7a205c5a9696e0eb3299418eb4b5aaca3d145a994f1e9025049953022b285d6527392d2a2050039cc03b59ea8b4e26d3b624ad2cf1ec82b0b3d8e72a175a5864d42f1ce54ca37194cac495a5a99669d9e3d644a0b4a4c230b4b5810f30a2da5f38a4c66c4951ea8b48da82f94b6c494c118624a0c6145a1e42a3214d4cab3d0cba8b678fc877624a95506228b3215c5a5bc7e43ca9545173c7c8daf1f90f28817119c2d2a000b7338c78f058cae38b65329e3c15ac4994ca78f716a9656852ccc4944082b41660b98f1ee22f89a3185a56917457017687794cac4915691fe532866e05fa9948fe55388fea653419f050150a6560ecb4b432b076710b1250f2b4b5a5cc49432954c33e27f9a7619f691900cdc0bf5d14c0d8b0fe50fa995c5a9690c3ca655a5ca49624b8b54caba1a0d4c69dce2d440a5a54c3299449b2995305a18c6915c0b2cc4969d867d272c3f34d8ab5000cfcb4b62499c510247f223cc495a5a205a76d3b88fe675440c51b0c3866d89247f989269b9a7619f5f14bf312455a88105c8ab6624a205a85d0f805a82e5e3f1e3d4ca1978f1edc380d819069b063a99614391b4f1f38b5e3e287516940a2d809a865716865d4ca77f9e3e287817eb027028b8a5678f348865ce273c7d25ea652959e3dc5ae299a76c4978f9a0cd36e2d401643c7a55e0d682cd504abc96b123ce2952f9e1522ee2d5a5b4ee715ad2d2d22ad (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part620 : Excludes 0x2404000000000000000000000000000 0x1fd1c096d042404000000000000000000 :=
  finishCode 73 0xd82e0e02403c7256cb573c7ac8ea2f067190d2b5725b927534251c5a578fce2d5abc92f62499c4b4a969947e69943cbc7d6aec82c0a822019b710f0ebe16965aba1a50433884e26e2d6249dd65328ab5a4250f13311c55a5a5624ba8be0ab567b3074aa6d3b532b0764b4c36960ea1950ae5a59892bc2e8b634be13fb4ed8920b1624c0b9697947e43cb1250aa69113c99c5c45abb4ec2871c4d082c492d28686389850d5c5ab8ab64289a454cb1e1da565a55416ae47590aec313389a3430ec4986b6a65949696978f85bc93a78f1e3a00b81e3d843e08069dc9174a99b015792d6ae11c671682b50aa4b7389ca65750b4b19dc95ae298a5669969da50e7169a652d6d372d2a18b619a46b71c4c5165a569d9a14e272194b4a740c7e0af9c4dc5ac4969db4de28bb125c5aee3066715a5a5c5ad3b62492b4d3228b9c5a0b7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part622 : Excludes 0x2c00000000000000000000000000000 0x1fd384bbc000000000000000000000000 :=
  finishCode 131 0x380d82e03c7561982d5aa0901e1d697255d2ce0cb969674057e48b91c46d6b4b69db50b4b4b01961a18f12c473b4c92d8c62e2d1b8a8a588e917226cb29338a995a767875a5b78da1600cb50cca43624a45cf0eb57540f0f2994ed311b4e2616750cb125504a1cc495329e1d2d338b56aec4949fca653c3b30da2c8de1280cb3318927029954b734dc2d617369dc1770d0c28b532c023318b11d45e54d0d08db53c530ef3067587f34ec6d6371145845669c81f4eb2a65624ad5669c9e141969e312514430112b5594cae2b61fa8bd87f30fe4b4cc39715b4ec0fa6675329f09a2995696962d882d80d640d69a90e5c5622b03eb4ecf128c34e63a491b42db38accce44d8e9287569db4ee4b14459011a0911b8ce2b226b4ed48ae2b88db38b6517b4ed405c16af1e3cb56c023078f3c1144b7b4ee43ca53e61f91b589200b80aaa59714a915892947351a76a598e2605f428a9950d2e2794ca875591344b11853154044a8661b6b0fd4cad1b04aa99661fb0fe042a96e04ab12587f0675432833948ad3b8122e2b4b48cdc8daa6569bad8ba300cc2e0a802cc16ed379696c474b3857e1a5b4ed22e921987429950cb28b4516d3b432cb4b4610c5aac07f48f8a2d2d321e427f34ec35ab4b62486b6092ad550f2631429b8b5644d0f40ceb09641fa96c6e2789715cb4b516a5a45170455a4ac1f532a5a435ad3b923e7553c2ae04c25ad0c187ad2c003346d452c39139b096716b8ae532b8b669da99463ea2d8466e2d432b11c516a65516c87953296ae (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part623 : Excludes 0x2400000000000000000000000000000 0x1fd984924000000000000000000000000 :=
  finishCode 61 0x1c016ab20b80f1ce0501102a82d5cb56c4980aee211c6928d4ca52b8946a17710aa0493893a7874315c61071a05b84e6a1725b99de3b4a85e0d0cd3b895a7872d5ac8643308c312471b311c93aa453baad2c6c649d9c85a5b6886124d5469dcc41522c97169da8665259de5a76c1d945ec4169da68961914f13299433276983429394b8a86661f868588231f1a5a1849d6711013c8e3544f296d4cb292d84b299583aa2f620ab0a5394caa1961cb4ed87334dd4ca861a8755128c17769da9856966771c6c28b69bcb4b530a6878f2d59c0be19867d43bcb4b433a995c4f06750f2b4b43cc26513e924d0cb1c4c112867249ad2d0cf299569687915696ae (by decide +kernel)

private theorem part621 : Excludes 0x2400000000000000000000000000000 0x1fd184924000000000000000000000000 :=
  splitAt 1 119 0x1fd184924000000000000000000000000 part623 part622 (by decide +kernel)

private theorem part619 : Excludes 0x2400000000000000000000000000000 0x1fd180924000000000000000000000000 :=
  splitAt 1 110 0x1fd180924000000000000000000000000 part621 part620 (by decide +kernel)

private theorem part617 : Excludes 0x2400000000000000000000000000000 0x1fd080924000000000000000000000000 :=
  splitAt 1 116 0x1fd080924000000000000000000000000 part619 part618 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part627 : Excludes 0x2160000000000000000000000000000 0x1fde9ca5a3f7800000000000000000000 :=
  finishCode 37 0x32870250bc2205806218931e3d2e6c433b282b4166a658ebe77942db125e3e6875714443013e973945e9715138e354b6769909a973624a1c6517a58471aa5b3b4ca4342fb1254b71e3d804b9ca4b62482b41663006660d0b12548aa1f983aa5b0d0a5cd786019c060c67b059b126056bc7d2e61a33c7ab884d92e2c4123da5cc13aa278522c494b9b1063b4a8bc13647b4b99e3d7c5217823dc0a360dcb4b4b9b10d4ca47b054ca654b8ca35424a98589265f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part629 : Excludes 0x2140080000000000000000000000000 0x1fdeb8852376088850020000000000000 :=
  finishCode 49 0x17c651344c0b4aa03124d3728f4f1e46d63147b19fca9aa5992e6a535014c33c7ccb2a656979e3d2e7292d696a82f0ae310c498ab60ad490d1af1f9892881436a9951033125e3ec4394ca78f9496b4b8626973056a92d86a50350a4299520236c78f23dbc7e21db11585255b61aa5cc0bb10a5696051614b0d52e647b9144b9c86d78fa5352e2189600e8054b1263c791ed2e6c499a5e78f23d91ee4d194624c7854a49d24e4624c87f1a4a4d52e2903c7e716a5358920835a59e3d3841bcc1b4b9a0de4a6b1258371534ecac49 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part630 : Excludes 0x2140000000000000000000000000000 0x1fd4b88d2354000000000000000000000 :=
  finishCode 139 0x1b0680972c0240ea1e3db8650cf2be2204677111c1461b150fa994d2f026e23daf892298a65624c38d23d9694d3728b403e749624a574207148d42e5a562486c52419dc69b4d0f13287d29a74920ec76513eb1259457134490b4a529943ec49148a90ccead339486c3913e91b589228392d2881051b1248db312510229198920956e14c651d4440a85e530bc7d8925a534b9a1c13b3c7d8925a55b1b4236828d0b72994e3687f336ca654b4cea156e78f91b4cf29211b66248a448db312508516c1b13468a446868026092156d4c33c7c522f1f9c4728d547a0a332a9a6c286531840ab55532a87c14669b09fb28a626888150fca5b04496954c3097c13aa1f624ab8c62a811b9432529612b065486c493469a6d0812fcc490bfa0a4cea86309548710fc8f6529848ac33989247b624ca65426a1fd43e44994c5b1102800a4436316950fec4998931966601a0481883c7b28197624c0b1054ca656249f8a631245232994b4aaa0a46236b06e61c891584a71b69999e5d43accc1942690ed88a0a333c8a46051b10ca318b21f0c492d282c432f388569613b8cf219761cbc7de3f065d4ca0b7089cb4b343b125e3e19752061f14dc14af1f716ad2c32eb23c7e532a5a58720a9624b0e631ba5a5696ea29867943fca652ad997d10271b8c8e87f699bc7c8daca2485a5236cc4914891b6624b126148ad8a42c8c42a809f90da0a9532c87123d82bd0db3c7c5228710c7cb4b438a1fd640b1cb4b78fa9958920af5a5c5a594caca29809f92d217f624969510280309467f156d6aa84d0bfa1fd0bf38858921b159e9126 (by decide +kernel)

private theorem part628 : Excludes 0x2140000000000000000000000000000 0x1fd4b8852354000000000000000000000 :=
  splitAt 1 103 0x1fd4b8852354000000000000000000000 part630 part629 (by decide +kernel)

private theorem part626 : Excludes 0x2140000000000000000000000000000 0x1fd498852354000000000000000000000 :=
  splitAt 1 113 0x1fd498852354000000000000000000000 part628 part627 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part632 : Excludes 0x2104000000000000000000000000000 0x1fd46894b106104000000000000000000 :=
  finishCode 141 0x1c048160540f1ed82e8091927e0a314492e4b362ad6a0f02cda9964b9a1948e329952e648581225a5251a90a612b432e8a024412ad3b927e877591cd3b224ac8e59db4ed0ceea1d6652fa5a54cad3b25bac8b6291641d8c8cb4a51769d82a54bf169589286513bc8794b4945da76d425cd8931c8da7659748bcd3b771b4571485d0b06d3b24792b505f28758821b1690cc43199b8a588ae2b417b604b74e1a5f3c7caeef1f9a773c7d3c540d8258a5856b4b4ca3d614a1fd83b3c7c2de969904ae2d69d960c403d0b4ad3b78fa8b605d9d65c5334accc6837690b4b19c5852a6091e7148ced22ee2d338ce29695a5a66a1942b1504b49694cc6577983658360ecf1f716b0d6532b125c5ac272c1b4ecb4a671716cd2b1c6b124caa4852d2c485641785d0f805a82e54b33c7d4cae2992d294352cbc7da76d82b89c30ce2c79d14d1a691490f821d9a0de3f2995c4b2095a76e2d3a2ce294e1e3f19c585258f716cc4978fa995a76e2d950490b06c298cc6e2d4b4b4ed4cac19835a72382ced3b78fa50e78f95ddd4771645809624b72cbc9733218533c7cce2a4598520bb716bc7d38621e3f08b4d22655716a5cd5c39ace29532a19d0ee65515692b525f2994ce2f1f78fcba246e78f82ec972b02909c165d25f3c7d2e636d946644d52fa99525ef1f532c7454b99f0f1f94b2b2b5a9a994c869c3c7e695a4bd6a692f9e3e4477169c8d0025ca70ca290671497cf1f2c5a15678fa46d2373c7d0aa6552d1c91b0a3a0ed4c348969c71b20ed2d232590a687741d8c2d89212744097274350973641c4b219d0eed3b348866dcc0b9a996418847d89287923fc9618b4ad3b0c391fe43c860c326a5f94ca19b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part634 : Excludes 0x2100400000000000000000000000000 0x1fd44c843180421004000000000000000 :=
  finishCode 115 0xee3a8e02b8da12158c24cae8e20ab59c69dc4b9056cd3b32596951032504c2205581a1c43361a80f5a76b4b4b9c32b325993e31bb0a52e693952ace25612b4ede3e97349c9695742d2c9692d2ce2d440b88c416948db12e527e881716a206440c69758140710f1ec43389734a0972b22205c4328b586ab4b48b92c569728b661c90c4c6ee2d495b0a6624ad2d22e4b12d2b385434cd10267950fcc4359e9d6468693f715cc43236b4ece5734ccd2f3125c4671a77255c97296969dcc492d29a26624af0da2a0a612c52aee2d92d29539696f1f69da9823d904ad3b693ad2cd125a5059cb4b69d8a06440b4ee5a5b88a612e568681c5b11fcd0e6894e110294992e2973236ce2d23fcc492d2a2058c5e1004e08fe08192c2939624863d2e664b9a76b4b8cf255f96966799a769736813c344ad2e23f8a065a5a1b51022699102a632894169560440a17e5a59e3dc5b255d69692b82a687169d9e3c972962c038d62020b31241529693c7a17d0fe4b94b5c09121fc87f3c7c4b94b4b10b025ae69d9e3c9729631265a58a250da87f361093312485e957298cc4978fa1080217da77192cf1e87f50fcd3b395a005e296d66ed3b4b5818e42dacbc45ae239a7272b9a7603d9a4204913ba955a660b3495a5acf1e4b9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part637 : Excludes 0x2100024000000000000000000000000 0x1fdcdcd4290d32c086100924000000000 :=
  finishCode 69 0x1d4521b42429984ad4414cab2214e60fa135866695335acf61a2b4c463ae298086d31497969ce76b222084d983285b2cbb124d2a66b34bc73b497a16e2d1810d052b4360651868a047051a99455a6518e7724bd00581b43c7ae84b7336cc3948dbc7c55a06d90ee3251c6a46e78f8ab496f34ac55a4b78e76d3b156a9954c5b1201c6ac0a41e3da63028cb3734ecaef255d604b4a05e421a1fe78fb1248ea8174810008dcf1f4ab8a24f1eb539a7604741798d4512c4919ac96931ab1256418100624a1de78f91d4f1e3259a7685343ba0057f92a684d23a91262d38a451c20160122a40b2384ee867104b4ecb3678f2a08db0a4587e6478412f1f037991e371185a0e77219cf1e5a3236a0a669d9ceccab011c29a32541dc867294966cf1e30d8622d31 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part638 : Excludes 0x2100004000000000000000000000000 0x1fdc5cc6210110c002100004000000000 :=
  finishCode 115 0xa63888815f1b42d2ba8bc3384b1142cd3b2d3a9944e238d4b4b4ee436a994d365839e3ea6569da5a455a93f987ee296249a350760c71c6a5a4a5315352d238d57178521a04c09324b734bcc49343cc627087f98928291569a6d0ff30e4ceaf1f69d827642da49615692dce7f3c7d0ee03301a8ab52d3368687854ef1f2c19e3c96254d833238d7518c681786c0962ae031d05f0ab495a74994caa40a4642f92b52039dc78f69d91b661cae8b00ab5903c7831e516821661a95dd45b3126001928ccf2a2d5329e3dcc5e1b03413833a8ab6532969cd36a659a7658f8d068c140aa29953c690522c3588da14f9e3e34f69cc759236a1c669da78d3b78fa8b643ca96d83f123d89246d78fca650d8a49603ba1dc91e2ad156ca4343fa995a05717424ca1072213642f9b0ce3c7e39d99e4b47219d44eb43223cb21ce62d3a16d832a2d50fc73960c91b588ab5532ccc33148928b03124e72a2d8522f1f8cf2a6594b7216c48ac49247a995b042018ed3198925a333a9a0c523168da040180590f1e64790e2a1952dbc7c8ea8178c8ed33426959de3e46d19fc95369da50cace842304e2b882942fcb3b68e8da54b6c25433a13640fb09612fa86503ea4343bb12589320a54b6a59906211f09db4ede3f34ec522871 (by decide +kernel)

private theorem part636 : Excludes 0x2100004000000000000000000000000 0x1fdc5cc4210110c002100004000000000 :=
  splitAt 1 101 0x1fdc5cc4210110c002100004000000000 part638 part637 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part639 : Excludes 0x2100000000000000000000000000000 0x1fd44cc46100000000000000000000000 :=
  finishCode 117 0x2c03c37119c4409729c3809734d1dc242ce2d440923d8068188b031d0f278f519ce2d78fa8b5467031dc5a4712afca5961ab8b54ca78f43ba68c02994b4aa49817e8775a5cc494a685ee5a5a1dd24062c4993c7a99529b031cf1ed3b716b00e0160e3a1a194f1ec49817ea65344b68e02b804f945212f063997c946a55440cc49532831d4ab299426f285d102d3b32fb40c01d078f2bbc7434b9b98e219102879156a155c5b0ab5944d0e8731252e64992d2a70ba25cd90620b0d6426b4ec84f0c54cc6c1b61ac925624a20503e745037cc3771688a5892b4b69d92165d134156a5ce247b10e42fb125c5aa654d14cb1695c5b2205a07015c3c7a68c41871a973251a92e1c6a98650bb4ed2e6b4300a659696a4b42db4ecd0e2ad34bab825994aa87169da99471a88190fea6569dae897369dca5f3aaa996134cb4b440bb8ae268f1f811ea4b6249695102485247b68d033838d817e0c5560f8221696e2d942ef1f2c19945a77299542f3c7da76c1b43fca2d2bba995c5ab4b8b06c498b06b4b1c6a205b46718c5d1a760c106281e6087a90d4a62819852a2f1248905102be2d05a578fc73350bacf547a46d042ca3d43f8216594a20547a8373e14972995e3e881328ad2cb0734ed103340da2980c55a1a770214116697622ce2d52aacf567b11b5a771a5ccbe66369dca59624a16dc5aa65 (by decide +kernel)

private theorem part635 : Excludes 0x2100000000000000000000000000000 0x1fd44cc42100000000000000000000000 :=
  splitAt 1 98 0x1fd44cc42100000000000000000000000 part639 part636 (by decide +kernel)

private theorem part633 : Excludes 0x2100000000000000000000000000000 0x1fd44c842100000000000000000000000 :=
  splitAt 1 106 0x1fd44c842100000000000000000000000 part635 part634 (by decide +kernel)

private theorem part631 : Excludes 0x2100000000000000000000000000000 0x1fd448842100000000000000000000000 :=
  splitAt 1 110 0x1fd448842100000000000000000000000 part633 part632 (by decide +kernel)

private theorem part625 : Excludes 0x2100000000000000000000000000000 0x1fd408842100000000000000000000000 :=
  splitAt 1 114 0x1fd408842100000000000000000000000 part631 part626 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part643 : Excludes 0x2060100000000000000000000000000 0x1fd792a18ecf816060100000000000000 :=
  finishCode 25 0x1945c1b8611102b01e1e0ce9dd4ef20ab3c3cc490d0a9941431d146da785581640c5ca65055a9961489de50933c7c34216f3c3a99534660a03378676532a90b4b928e17778fca25624ad2cca706754ca87f8342291532a206854b9c38d5329e1d4a3306c71aa65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part644 : Excludes 0x2040100000000000000000000000000 0x1fd52281064c012040100000000000000 :=
  finishCode 157 0x671b06217025cb70a83787874b0e46a10be87f532c91f5a5a58d8932204507285c8da881624ad2d0daee208c62204c5f34ad86aa178a46849624b5036394ca95b2d2ca1762190cd4cb2d2c60e5231b1a5bd2c72204b85312b647b9c521b1614a2048db20dc8f61b10b3c94f5a5bc7cd3711ec2cef1f3c3b70f1f94ca27d4ada58cc0197cf1f716c2830b7a994f02adc85f532a2052c6787531dc60110255b9e3e91f400e85b0ab629182fe87f001ca4541485fd2d2a6582fea65943234338da888002754cb0d0de3e64f94ca9474b4cb61c6e4369c6e530fc2b1dc4b4b709a3005a55b12b66999e3e8811c6b8a6043a58c123389d4ca8712adc8374b7a2054c70694b4aaa25be531914434a45196aa54d651dc730b4aa2592de55b0d8b124cb7291524a54d630b80d2ad2e532a5bd4b664f92c6a65051c87f228b12603599dd94591500d29695c4b3095486f1f4b782bd4caf1f815e9336e071b1d551026778c8ef1f43f9de50ff19dd505b148461204e12c0b785dd6970cbde3ea6543fa126532a56c8db09154cab4b61cb0fd0fe96f532c29143f956d67b310de3e0a961fa1fca0057cc49342a4ede3e96f5a5b07d4ca96f9872b4b532cb037064256c8db059d69610b986a06b2a6993c50a3279e3e55b142859c40b02154b615b4adbc7d945313434dca25624b8b4f0a7492d2b60a01e067534da99660da946624a205c4b247d0fe67f60dcb4b44099dd892e6128b631255078fca170c79d650da87f614c00d32591eceb27499506c10db192cd16a653c39a665329407230d52e338a4cee47b2a699de38da56c8daf1f056ca81e1e2a6a90d0fe9738a9a0ad5b128540cee86d90fe7876e0a9b1075852b4b4b9c239441403c3b8b662491b523f310d2e286d9892c35528cc49 (by decide +kernel)

private theorem part642 : Excludes 0x2040100000000000000000000000000 0x1fd50281064c012040100000000000000 :=
  splitAt 1 113 0x1fd50281064c012040100000000000000 part644 part643 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part645 : Excludes 0x2040000000000000000000000000000 0x1fd500910204000000000000000000000 :=
  finishCode 149 0x370ee3602d55c078e943107416ac8f70d2cab67874b99e0a5b9102b4b4269e1cd3311ed94380f04409e1e530868543e9a217e5329de54332d5d09a1a1522a13638d9de4f0e78796aea1f61aa98546b2d5cf0ec41d09425cd0c6d12434ccb4b5328a443430e344f30e358932984696b4b322ca3560ea94d89268b2adb3084d8f0a8715a59984ef3298471a6535a586861c6a89cef2343530b109a16ad2c6d10db3c7d4ca08d3379a655c531ce272a6a99433238d32011ac3984f2f1f713b125696697866227950cc6896249914d32b02994f1f156c6c72d2d892849601b4591843bcca651489a1d9432ec78942dc73542f9d9642d9e3d0e266d8f1e6971c6b89e128a9958928715abb606412e4b563c742017b249d2c692792760bd5a5b186899a660bd532c6891b8b8957061cc8710919c6cc8ef1f5ab9e3ccf25ab521644b0d834ab9867939088721ed87ec490d6ad54f1f312435a54d983f1e3dc02e0ab73c7cd12a193e167b2d54d12f1f8c8624c9635a5a4ed0f730fd4ca1ad580b83c7a51e2ada1fe532b0fccdaf1f416b4ce78fad2d09ab4b92def1f3c7ac03c7540f1eb4298a518cd2b572d2825546e0a162087721154ca0a91adad5c32e58198b57750e4532b06623db116214b0645222919892a5904281543630a44e443109b290d0840bca191a189dd09a54d86e2c498362b62986994f10371de5892093510ca37426a06e0d8ad5d8932d8b574f0cee0b7298c87560c8e358930d6d83204990aea511ada1d5892d21f8a61e8a255b14a26a21ee4b49da4ef21a18f12b579e3e9692d299be05bae040214653282dde3eb575b106f21a50da1b1714c54d620a1a54caa658362f1f0b7b8b62d282dd29b2574f0a87b (by decide +kernel)

private theorem part641 : Excludes 0x2040000000000000000000000000000 0x1fd500810204000000000000000000000 :=
  splitAt 1 104 0x1fd500810204000000000000000000000 part645 part642 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part648 : Excludes 0x2014000010000000000000000000000 0x1fd7498dd022154050190020140000100 :=
  finishCode 101 0xb8220d02a0b57690f0eca308e202e5c5b21454ca5a5391cb3b228a99455b2995892723528a14583329948fe2ad23fc86d431990e22b8851530d22c45871ac49695990ca8594c921514ad4d657169633882ed1c6249e267149145646d2b043acee714b4ad4c60b9651a4570176e2169634db8b564734d54aab239c5ae2d8f0ab2334d9b0762cae4b8a9556572c8c6c716c643716c38d541743c3b126424a995a762ad348cd3b532990d3b040c69b531b125a56962894d229719c52b532a681f434338a5646a55540a8481a42afae8be0ab5b4532b4be620a1b48a33105892d3b69796948ff30dd78320e472ceda5ea5123fc6439892a6569db68451988a82523fa1b4ce33075a5ec492e0c8738a50fea656248ced6a6ba258723943a87f532c2ad50ecb23391af82ad05dc5a569da9948ff2f064328c49695a98691032c671321a98dc530dc56460bb60ccae25c652aac8d43ab2b8206b23261a7630794aa72319d8c1e417b1255c690abf29948a2a3b5288ab54c4d1742d2b09e716a1b48a338b42f286d8abe667333cd3b88fea65 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part649 : Excludes 0x2014000000000000000000000000000 0x1fd54988d032154000000000000000000 :=
  finishCode 157 0xe22204b93a1704b9b20bc1e1d18681686a0326e6215632aa99631ca88643aa935c5a8e34ed0c7020d4ca87b428ca3f4b0863e716ca6569da19e040b8b54ca86969db98b576508ff29956a6671346a1e65a9a9948ea93588fea65731a44510c43b899e0bb89e48ff299547705cd46ee2d2d2a5c671291fd4cae2d8b02a653c190730f0ea62f8a65989238d716969500429ce2523fa14e624ab882184fe55f624a14c03f088d892c2d53291d54cb38b4b4ae62e0ae29965268cfcabeb57346905622899c56ae451823655f624957e532b8b54765a5681a85ab91fe532a084d1a187813328ddc5aa6534db98642e08e228655611a77066ce4655f43ba8de2d29c8cabe81d21fc85769d8254b4ac496609454189219b94caae28a662294c613f9695785b10ce19b032c43b2d2ac8c4fed3580c6255697a0c61179694006a2931fb4ed4caae3487239452a6340ea1dd47f11fe5329d8c494015c13f91d5c53114588a2478436d3b94ca8772d2a074abf21dd0ae5a55e1b44515c23a89fe43ca95402334ec4fe2799476a5f0cda094b4a5a591c4d108aa659a76867623b884b4aae157e69da8fd4cb088cc7e06769d81062d2b1150aaa6569da005a50cdc47f391c55f228866d4c674220b425cd5c56127334ec8522574b8a99455a099531c877156b124f0eb8063e0cdb4ecf0ed3b902647f532a487874a6ca6313c822d2c30e3589247f571504f15823fcc494b8a99455a09966055b3124ed318f544281d532a1dc143297c55a9e1e856287649a8e344f2855433b2877594928790ccb4ee13ca1e594624c7850ccb0de710a5c5652a551c6ae07899452c47055a97d4c32d0d08230769db1252c3bcca65616b11d50205c30d624b8850263393b4a995c473124ed2ae2b02ad4b8cc4923fa9941327879892b811fe059a93544219323fca65 (by decide +kernel)

private theorem part647 : Excludes 0x2014000000000000000000000000000 0x1fd54988d022154000000000000000000 :=
  splitAt 1 88 0x1fd54988d022154000000000000000000 part649 part648 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part650 : Excludes 0x2010000000000000000000000000000 0x1fd544884020100000000000000000000 :=
  finishCode 101 0x1a05c1dc2d5b502d5661101e19a565aba996110b88585ac49440b04c16ae6898f0e9629963aaa204d0e86f88d6a21344ca654b9a205046d174431284c1102971983a46d52fb8863b4ca5f236b074ef31c6510247f946e881236c881601c430685086877344aa00139c42c4732fa99460f308e298f0eb574409a251032d5da84c0786de1e1d0cb1a250f3388b579c5a4b908ec72543ba9956aed811b6624ad5c33a7793c392e433b02cd8416a8f0d49702fcd2ac4934ba44e49d8ab5a8661c41e1b20ac2e88412e50930ab50da91f5a5a51da771e1c60eb4b532a5a455a841146532957cc7e78748fa2056969473c3c843623a20569616b820632f42492e5892787532c07b440b11d6964b9440ca65156b88d212e5844c10f2a639086787531ca6534dca51532a2052c734eccaa97302da205dc4b1102980e35277204da7696f4b9a97d227050da76a65489c14369da9954be27f8f0ea63050aa0b01e1d9425ca5ccc9734ed1029719a760636f17451dce2d69d8ab50922699c5a8814a6c237698a585a768812afac09c3889736509721678c9e881716c51369d859cc9f02bc2ce64f897215769da98d3b2d2c8814b8c1b1 (by decide +kernel)

private theorem part646 : Excludes 0x2000000000000000000000000000000 0x1fd540800000000000000000000000000 :=
  splitAt 4337 110 0x1fd540884020100000000000000000000 part650 part647 (by decide +kernel)

private theorem part640 : Excludes 0x2000000000000000000000000000000 0x1fd500800000000000000000000000000 :=
  splitAt 1 114 0x1fd500800000000000000000000000000 part646 part641 (by decide +kernel)

private theorem part624 : Excludes 0x2000000000000000000000000000000 0x1fd400800000000000000000000000000 :=
  splitAt 1 116 0x1fd400800000000000000000000000000 part640 part625 (by decide +kernel)

private theorem part616 : Excludes 0 0x1fd000000000000000000000000000000 :=
  splitAt 4216 118 0x1fd000800000000000000000000000000 part624 part617 (by decide +kernel)

private theorem part574 : Excludes 0 0x1f5000000000000000000000000000000 :=
  splitAt 1 123 0x1f5000000000000000000000000000000 part616 part575 (by decide +kernel)

private theorem part530 : Excludes 0 0x175000000000000000000000000000000 :=
  splitAt 1 127 0x175000000000000000000000000000000 part574 part531 (by decide +kernel)

private theorem part476 : Excludes 0 0x155000000000000000000000000000000 :=
  splitAt 1 125 0x155000000000000000000000000000000 part530 part477 (by decide +kernel)

private theorem part378 : Excludes 0 0x115000000000000000000000000000000 :=
  splitAt 1 126 0x115000000000000000000000000000000 part476 part379 (by decide +kernel)

private theorem part282 : Excludes 0 0x105000000000000000000000000000000 :=
  splitAt 1 124 0x105000000000000000000000000000000 part378 part283 (by decide +kernel)

private theorem part186 : Excludes 0 0x104000000000000000000000000000000 :=
  splitAt 1 120 0x104000000000000000000000000000000 part282 part187 (by decide +kernel)

private theorem part2 : Excludes 0 0x100000000000000000000000000000000 :=
  splitAt 1 122 0x100000000000000000000000000000000 part186 part3 (by decide +kernel)

private theorem part0 : Excludes 0 0 :=
  splitAt 1 128 0 part2 part1 (by decide +kernel)

private theorem noGood : ¬ Good 257 17 := by
  rintro ⟨c,hp,ha⟩
  exact part0 c hp ha (by simp [Red]) (blue_zero c)

end Case257
private theorem no257 : ¬ Good 257 17 := Case257.noGood

theorem spectrum (n : Nat) (p : n%2=1) : Good n 17 ↔ n ≤ 255 := by
  constructor
  · intro h
    by_contra! large
    exact no257 (restrictGood 257 ((n-257)/2) (by omega) h)
  · intro small
    exact restrictGood n ((255-n)/2) (by omega) yes255

end PalindromicSeventeenOdd

theorem OMA.solution : OMA.R_Green14_W_3_17_R2.H1 := PalindromicSeventeenOdd.spectrum
