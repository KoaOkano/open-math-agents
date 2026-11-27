import OMAReductions.R_Green14_W_3_16_R2

/-! The odd part of the palindromic breakpoint pair (232,237)
computed by Ahmed, Kullmann and Snevily in Table 6. A reflected coloring
attains length 231. The certificate rules out length 233, after which
centered restrictions give all lengths of the same parity. -/
-- Lean formalization by @KoaOkano.
namespace PalindromicSixteenOdd
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

private def differences231 := checkDifference 231 16 0x4008201000c808800432081004000

set_option maxHeartbeats 3000000 in
private theorem span231_0 : Covers differences231 1 9 :=
  checkedRange 1 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_1 : Covers differences231 9 17 :=
  checkedRange 9 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_2 : Covers differences231 17 25 :=
  checkedRange 17 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_3 : Covers differences231 25 33 :=
  checkedRange 25 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_4 : Covers differences231 33 41 :=
  checkedRange 33 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_5 : Covers differences231 41 49 :=
  checkedRange 41 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_6 : Covers differences231 49 57 :=
  checkedRange 49 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_7 : Covers differences231 57 65 :=
  checkedRange 57 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_8 : Covers differences231 65 73 :=
  checkedRange 65 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_9 : Covers differences231 73 81 :=
  checkedRange 73 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_10 : Covers differences231 81 89 :=
  checkedRange 81 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_11 : Covers differences231 89 97 :=
  checkedRange 89 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_12 : Covers differences231 97 105 :=
  checkedRange 97 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_13 : Covers differences231 105 113 :=
  checkedRange 105 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_14 : Covers differences231 113 116 :=
  checkedRange 113 3 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span231_15 : Covers differences231 116 231 :=
  checkedRange 116 115 (by decide +kernel)

private theorem yes231 : Good 231 16 :=
  witnessOfChecks 231 16 0x4008201000c808800432081004000 (by decide) (mergeRanges (mergeRanges (mergeRanges (mergeRanges span231_0 span231_1) (mergeRanges span231_2 span231_3)) (mergeRanges (mergeRanges span231_4 span231_5) (mergeRanges span231_6 span231_7))) (mergeRanges (mergeRanges (mergeRanges span231_8 span231_9) (mergeRanges span231_10 span231_11)) (mergeRanges (mergeRanges span231_12 span231_13) (mergeRanges span231_14 span231_15))))

namespace Case233
private def hints : Array (List Nat) := #[
[26795],
[26563],
[17477,26331],
[26099],
[25867],
[17014,25635],
[25403],
[25171],
[16551,24939],
[24707],
[24475],
[16088,24243],
[24011],
[23779],
[15625,23547],
[23315],
[23083],
[15162,22851],
[22619],
[22387],
[14699,22155],
[21923],
[21691],
[14236,21459],
[21227],
[20995],
[13773,20763],
[20531],
[20299],
[13310,20067],
[19835],
[19603],
[12847,19371],
[19139],
[18907],
[12384,18675],
[18443],
[18211],
[11921,17979],
[17747],
[17515],
[11458,17283],
[17051],
[16819],
[10995,16587],
[16355],
[16123],
[10532,15891],
[15659],
[15427],
[10069,15195],
[14963],
[14731],
[9606,14499],
[14267],
[14035],
[9143,13803],
[13571],
[13339],
[8680,13107],
[12875],
[12643],
[8217,12411],
[12179],
[11947],
[7754,11715],
[11483],
[11251],
[7291,11019],
[10787],
[10555],
[6828,10323],
[10091],
[9859],
[6365,9627],
[9395],
[9163],
[5902,8931],
[8699,17477],
[8467,17014],
[5439,8235,16551],
[8003,16088],
[7771,15625],
[4976,7539,15162],
[7307,14699],
[7075,14236],
[4513,6843,13773],
[6611,13310],
[6379,12847],
[4050,6147,12384],
[5915,11921],
[5683,11458],
[3587,5451,10995],
[5219,10532],
[4987,10069],
[3124,4755,9606],
[4523,9143],
[4291,8680],
[2661,4059,8217],
[3827,7754],
[3595,7291],
[2198,3363,6828],
[3131,6365],
[2899,5902],
[1735,2667,5439],
[2435,4976],
[2203,4513],
[1272,1971,4050],
[1739,3587],
[1507,3124],
[809,1275,2661],
[1043,2198],
[811,1735],
[346,579,1272],
[347,809],
[115,346],
[115,347,579,811,1043,1275,1507,1739,1971,2203,2435,2667,2899,3131,3363,3595,3827,4059,4291,4523,4755,4987,5219,5451,5683,5915,6147,6379,6611,6843,7075,7307,7539,7771,8003,8235,8467,8699,8931,9163,9395,9627,9859,10091,10323,10555,10787,11019,11251,11483,11715,11947,12179,12411,12643,12875,13107,13339,13571,13803,14035,14267,14499,14731,14963,15195,15427,15659,15891,16123,16355,16587,16819,17051,17283,17515,17747,17979,18211,18443,18675,18907,19139,19371,19603,19835,20067,20299,20531,20763,20995,21227,21459,21691,21923,22155,22387,22619,22851,23083,23315,23547,23779,24011,24243,24475,24707,24939,25171,25403,25635,25867,26099,26331,26563,26795]]

private def values : Array Nat := #[
0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000000040000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000000080000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000000100000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000000200000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000000400000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000000800000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000001000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000002000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000004000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000008000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000010000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000020000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000040000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000080000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000100000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000200000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000400000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100000800000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100001000000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100002000000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100004000000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100008000000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100010000000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100020000000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100040000000000000000000000000,0x100000000000000000000000000000,0x100000000000000000000000000000,0x100080000000000000000000000000,0x100000000000000000000000000004,0x100000000000000000000000000020,0x100100000000000000000000000100,0x100000000000000000000000000800,0x100000000000000000000000004000,0x100200000000000000000000020000,0x100000000000000000000000100000,0x100000000000000000000000800000,0x100400000000000000000004000000,0x100000000000000000000020000000,0x100000000000000000000100000000,0x100800000000000000000800000000,0x100000000000000000004000000000,0x100000000000000000020000000000,0x101000000000000000100000000000,0x100000000000000000800000000000,0x100000000000000004000000000000,0x102000000000000020000000000000,0x100000000000000100000000000000,0x100000000000000800000000000000,0x104000000000004000000000000000,0x100000000000020000000000000000,0x100000000000100000000000000000,0x108000000000800000000000000000,0x100000000004000000000000000000,0x100000000020000000000000000000,0x110000000100000000000000000000,0x100000000800000000000000000000,0x100000004000000000000000000000,0x120000020000000000000000000000,0x100000100000000000000000000000,0x100000800000000000000000000000,0x140004000000000000000000000000,0x100020000000000000000000000000,0x100100000000000000000000000000,0x180800000000000000000000000000,0x104000000000000000000000000000,0x120000000000000000000000000000,0xfffffffffffffffffffffffffffff]

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def moves : Rules 233 16 :=
  cachedRules 233 16 (by decide) hints values (by decide +kernel)

private theorem finish {r b : Nat} (words : Array Nat)
    (h : redCheck moves (readTree words) r b = true) : Refutes moves r b :=
  checked moves (by decide) (by decide) _ h

private theorem branch {r b} (w rr bb p br : Nat) (pass : reaches moves w r b rr bb p br=true)
    (l : Refutes moves (rr ||| 2^p) br) (t : Refutes moves rr (bb ||| 2^p)) : Refutes moves r b :=
  join moves (by decide) (by decide) _ _ _ _ _ pass l t

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part1 : Refutes moves 0x100000000000000000000000000000 0xfffffffffffffffffffffffffffff :=
  finish #[
4225] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part6 : Refutes moves 0x4801010000000000000000000000 0x17379c9235506c0149010100000000 :=
  finish #[
10417895,0x1b11998f93541ed,27235651633,55788070077964,28976293607,0x3420532c13e446ac43d8530,4145,51637389161775,4135,4207,4189,18419225290,35431973799207,11068167,4189,
14184535,59317763765874,29068153243,11035393,97127534272807438,4145,25364558607,4135,4207,30034269693,0x827af97f174c46530,10547311,4160,4175,4190,
48235777299655,0xd0d0ee1217bdfc114,59386481287829,11068488,4211,0x40bd88180a39e7bd859a,4153,4207,4189,86296241560838915,4159,4173,4187,29061707059,28029907481,
48231205077648,4160,0x178d446c5dfc428d9d77af660e,4159,4187,29058839830,21602846217,24491700303,4140,4164] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part8 : Refutes moves 0x4800014000000000000000000000 0x1e071d96901476404c800154000000 :=
  finish #[
0xd885de8017bcae126,18743284586,0x8a3bf8ec85e4b2273,0x4ea666596f585e126281,0x179280052cb21a7,4153,20636348494,4197,4189,29060297584,4752,61375672996714,4173,4167,19671659033,
59350232446151,9655805,9703499,4207,4189,8762889,0x8f8a36bbe231353d5,4174,5194,50106553893829,0x1a376217ec460fc,4187,51374177973322,4155,4190,
4757,5203,10568442,4190,4187,0x1932f590a13b438,4207,4189,11956333,4156,4204] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part10 : Refutes moves 0x4800010000000100000000000000 0x17071d924815740048104101000025 :=
  finish #[
61360199157257,13702772,0xdf8596d2ac4288438,4189,4159,48227227985298,4146,0x1ccd445714ae303,41946122651252,4180,0x27ca88b4a95abf420844100,4175,4169,4737,0xe660ee801dbca767d,
89595914066957483,0x195d2b5e04a75ff,12410937,4169,8761431,27175608742,12821121,11011489,55775733642437,4139,51293791806081,4160,4183,17945460809,4207,
4197,4963,23370941509,10616905,0x487588bf8108a3cae270,8484472,89477924574728383,0xdfc328106574b258b,4197,4183,4161,0x17516224dcae678,27259494594,55827445293253,4177,
4169,14189871,61448966891133,15103497,47480831518002,4159,13295663,51752851727180,8667659,4175,4169,9719886,4205,8762017,4197,
4187,4190,0x1b10ea24da2060a,57615082435233,17945350817,4205,4190,8762238,19724751736,44244582662364,4197,4207,4167,21643810070,10957461,
4186,5641,30033810849,21602844750,5641,0x1bf92ad7bafd290,27019989184,4169,10616910,4187,11956335,4156,4180,4204] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part11 : Refutes moves 0x4800010000000000000000000000 0x16071d924010640148000100000000 :=
  finish #[
0xacd6d5422fcb67524,50158090293653,4144,49934761358638,0x43e9f2b109853cb67347,20603662762,4183,4186,4189,11957641,36313915225609,21602844752,4170,28149580437,0xc95beeb1a514af6ea,
10567880,4170,0x1b10f490a13259c,4183,4177,11903939,9728453,4205,0x2061dbcaeb102e97bafd1b6,4181,4208,13743625,10957800,4168,57644764091913,
8761429,17945461397,4207,4197,4187,14189871,29059765068,4178,0x1854b2ec44ae0c3,29058806604,0xbacb1028c864b21a6,4197,13742145,4164,11956986,
55515466405385,0x16cf62107a1459a,4170,4160,4180,25418700188,61514898695024,4181,57642924225623,4190,5423,17764483960,14189306,29059380302,4177,
4183,4180,11523375,5518,57399951844417,4183,85477866889302214,4170,4178,4138,13743080,13742477,29061707164,4180,11957660,
13742967,23538730053,4178,98010930901951783,4163,4168,4174,4170,4164,10568130,0x1b1146d0a05b457,10616929,4197,4207,12849243,
4142] (by decide +kernel)

private theorem part9 : Refutes moves 0x4800010000000000000000000000 0x16071d924010640048000100000000 :=
  branch 1 0x4800010000000000000000000000 0x16071d924010640048000100000000 56 0x17071d924815740048104101000025 (by decide +kernel) part10 part11

private theorem part7 : Refutes moves 0x4800010000000000000000000000 0x16071d920010640048000100000000 :=
  branch 1 0x4800010000000000000000000000 0x16071d920010640048000100000000 86 0x1e071d96901476404c800154000000 (by decide +kernel) part8 part9

private theorem part5 : Refutes moves 0x4800010000000000000000000000 0x16071c920010640048000100000000 :=
  branch 1 0x4800010000000000000000000000 0x16071c920010640048000100000000 96 0x17379c9235506c0149010100000000 (by decide +kernel) part6 part7

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part14 : Refutes moves 0x4809000000000000000000000000 0x1fb1c4bbb6524a4900000000000000 :=
  finish #[
12870710,29104113158,17853093386,0x1bf8609e78b660c,4167,4179,4171,4305,19806811335,4202,4193,8709639,0x1b116344ebc75fd,4154,0x193946efe0b66ea,
13300935,4147,4167,11912935,0xdfc09d7c6c3caf5fd,11956330,11509860,4156] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part15 : Refutes moves 0x4801000000000000000000000000 0x16318c933440480100000000000000 :=
  finish #[
14193863,0xc9f7ab7f02758967a,5204,18779509391,61505526261247,4167,4171,4169,4175,11494242,4201,20212978774,18517227017,4164,26362803491,
0x5abd89bf911974d1b3d3,4164,0xd88180ba1b3af660a,4173,11509851,4156,73537421338646247,0x195cee1eaadb2d4,11956330,36509675058147,12871177,0xcae5d36217e9424c7,4193,4202,4187,
4752,44248213923453,4193,90605194277004152,4156,4170,4277,40201334130186,4171,5646,8974586,4128,9867546,4154,4142,
5319,14197363,29080720129,30035699210,4177,4157,4175,59523923022658,14210102,0xd8995f6028c94267d,4211,10950145,22424069426,11440243,4160,
4187,4208,4202,14189982,5402,55417883166439,28149141561,14189432,4173,4187,55570666651835,0xcad13f46ec551d601,0x1b157f258ae9083,0x176325e8dafd516,4159,
0x6fb497a36b6d7b942435,4207,4208,4187,29063943694,0x1b15622c692a60a,13742159,22425802250,0x1965476fbd8d67a,61361234387818,4193,4207,11956336,4172,4196,
4164,11510190,24514971253,12870621,4187,4207,5532,48339776083356,48284611743808,4165,4170,5640,61515824136805,0x5df2cb6ce142c6c4660a,30035698435,
26361000707,4162,4153,13295727,45392240559738,12870745,8716399,81126308191363237,12870476,5532,26358326335,4202,4208,13295727,11509865,
4170,21720342609,4179,4189,4190] (by decide +kernel)

private theorem part13 : Refutes moves 0x4801000000000000000000000000 0x163184933440480100000000000000 :=
  branch 1 0x4801000000000000000000000000 0x163184933440480100000000000000 99 0x1fb1c4bbb6524a4900000000000000 (by decide +kernel) part14 part15

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part17 : Refutes moves 0x14800000000000000000000000000 0x1e915dd30000000000000000000000 :=
  finish #[
0x1b152ba5218c88c15d1005b51c,4769,29977347256,28001363233,14209078,27232945675,0xcaeb13105ad44644b,4187,4167,26359165917,11509844,4156,51996327544111,55566089860733,0x188c814ce220439,
4197,0xc465f44c828855679,4183,4186,15111471,29991302670,11317315,46020501042149,61362110390794,4135,4177,29976957454,4202,0x44fd1bbe72ba20a181a6,4164,
8737659,0x6c49dbb117dc4cafa42a,42017577244280,4202,0x1a36bea20a18120,4164,4169,57642957770972,4197,4187,4762,8761560,4193,0x8996ced7220a1e1ea,4767,
10609858,29063042242,14664653,4177,55774935295153,8736847,8753239,4193,4187,74944246098043771,4174,4179,4180,4199,4189,
4205] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part19 : Refutes moves 0x5800000000000000000000000000 0x1f2505df0000000000000000000000 :=
  finish #[
14636229,17730033159,4167,14185774,5192,11522689,8732742,4182,4181,93540654374015843,17901654657,4197,4196,15098458,5641,
27242717452,4157,18733858889,4311,10617047,8728687,4183,4532,14189767,5319,0x193e801b14ad609,8745033,4189,4195,29059765447,
8753588,4189,8720590,4180,4182,26361913759,59521116693703,4173,45724810293438,4196,0x1bf814cc6a2052f,21744062778,4176,11509846,4163,
4198,4177,59488596793063,4737,0x6be3beb10bc02a2ef281,4173,8753237,28967134407,30011807022,0xcae3a8296fcaef0b3,8745023,4195,14664524,0x6be58abf8f3c9249f6e8,13295695,
61454992913272,11509859,4163,4314,17862469129,5423,82428068134638459,4173,4201,8753366,10616929,4207,4182,4177,0x399a53caf5c22e42a51b4c2,
8741078,4196,0x1bef46e2085120a,10617047,4197,4177,49833502024524,0x1beaba02bafa42f,78626220336469626,48092846339271,4197,4199,4195,0x311ac405913b7c6fcd1b273,61324093666824,
26315412337,28144144598,4197,4196,4977,0xd886b51042685337e,4183,17903517914,4197,4177,4172,11972694,4160,4176,4152] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part21 : Refutes moves 0x4810000000000000000000000000 0x179305b70448100000000000000000 :=
  finish #[
13296834,53419281412962,27238155335,4181,4180,28971685058,10588607,4180,59326502937903,4179,4205,5296,26165334229,10616919,74916883098392186,
12849825,5314,98007273587336825,4180,4195,59332142736578,14144706,28968019247,4179,4159,19722908321,11509844,4170,4198,4205,
4177,0x2eb333df63ff7d4f7d88349,59521943319638,29974589855,28137014089,9589051,4167,4177,4169,0xe663fe7be55cb1676,4143,4165,0x88ba3b7d6c44ae2a1,4146,47470081955559,
59332939592304,4138,4720,27209175811,11509829,13295697,0x655d88928bea572184c7,4169,4205,0x30ae570b988cbdd7ed884c4,4410,18733855940,8728634,4183,59486769964317,
59486759789533,4198,17844798331,4182,12776315,10617720,4172,5316,23574107318,4175,4150,38415740679471,4183,9692681,27232543920,
21720342609,4199,4195,4205,4180,0x1962496c41ff608,0xbd03ff62177854525,4181,48327425345255,0x192a15107222459,4179,4205,0xd1d87f46d102fa6e7,23573254817,5319,
21743612778,4179,4181,4183,4177,14635322,0x1b00152fac411bf,13742186,21471356098,5532,10625237,27231617108,4205,4179,5532,
36379778803201,0x194f2ba8ddf558e,4198,0xdf584a2e68da200d2,4182,36391543870767,0x5ec5fc3df4345cc25a36be89613552f,4198,4195,4180,11972689,4168,4152,4176] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part22 : Refutes moves 0x4800000000000000000000000000 0x171115930000000000000000000000 :=
  finish #[
21747291658,4736,29058418294,36355734372614,4197,4167,4169,61442494268817,29972844965,4310,10482055,11903979,11904300,8630912,4161,
4165,4177,4169,13295679,4135,0x311afb588956491104ae3eb,8761560,4195,4197,4190,17928650966,43458816042615,0x1beb621a635c52f,4161,26361914668,
0x1b0c5d49fa20273,4202,4187,47471439463073,46325158700107,10584282,4190,4195,4189,52042393400370,19911074558,8753366,4189,4190,37576938456139,
27232006598,4190,93003249059201546,12871180,9585967,21552488527,4159,4189,11509833,4163,4177,4205,4761,0x3620032183297de554b25fe,4161,
0x1b06d52c4124120,29059826775,98888412815894014,4153,8757357,4187,22473454208,0xdfc6a8b2ec52fa604,53981869020686,4189,11510297,4314,0xe671351189c93f677,4207,4187,
4190,4205,5646,13296246,4179,29978735358,0xd8895c9f6f9afa604,10585387,4189,4174,4186,29974122714,17945461376,4207,12849243,
4182,4202,52048709146120,26362828292,53990988857984,4175,8762443,4195,4197,44402798343797,20637303232,4207,13742189,14636444,29974123932,
4186,10617052,4197,35986534068657,41330396419598,40810247284122,29974691945,4179,14636444,12398764,4186,29976515996,61391886382492,10616937,11509871,
4177,12849261,11972694,4176,10170424] (by decide +kernel)

private theorem part20 : Refutes moves 0x4800000000000000000000000000 0x171105930000000000000000000000 :=
  branch 1 0x4800000000000000000000000000 0x171105930000000000000000000000 100 0x179305b70448100000000000000000 (by decide +kernel) part21 part22

private theorem part18 : Refutes moves 0x4800000000000000000000000000 0x170105930000000000000000000000 :=
  branch 1 0x4800000000000000000000000000 0x170105930000000000000000000000 108 0x1f2505df0000000000000000000000 (by decide +kernel) part19 part20

private theorem part16 : Refutes moves 0x4800000000000000000000000000 0x160105930000000000000000000000 :=
  branch 1 0x4800000000000000000000000000 0x160105930000000000000000000000 112 0x1e915dd30000000000000000000000 (by decide +kernel) part17 part18

private theorem part12 : Refutes moves 0x4800000000000000000000000000 0x160104930000000000000000000000 :=
  branch 1 0x4800000000000000000000000000 0x160104930000000000000000000000 96 0x163184933440480100000000000000 (by decide +kernel) part13 part16

private theorem part4 : Refutes moves 0x4800000000000000000000000000 0x160104920000000000000000000000 :=
  branch 1 0x4800000000000000000000000000 0x160104920000000000000000000000 88 0x16071c920010640048000100000000 (by decide +kernel) part5 part12

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part26 : Refutes moves 0x6100000000800000000000000000 0x17982f946900000a00804300184000 :=
  finish #[
35763190502917,0x17592bac444125d,59513160077810,0x449424a332bac418d2e5,4178,4138,4146,0x17837d2c442452f,43976082777045,59580101625462,29062082612,4159,4184,59519073154349,5425,
5204,22677976694,4172,4184,27235222266,24492148342,24488965750,4190,4184,51895084471028,4171,4183,4198,4180,29092009239,
11957551,59518218752052,0x989958d50614ae34f,25284531721,12420385,4154,4171,18732122325,4184,4189,13260302,55724294693599,4154,29972816628,8749269,
4190,4185,0x1afb29977b6726b,0x18829e6c44ae177,0x1b1129a574a02fa,4171,29977404937,59606992676361,4178,5423,25220154224,4171,4180,4723,26318632239,
4180,8749269,4185,4196,4184,10616926,4172,4202,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part28 : Refutes moves 0x6000100000800000000000000000 0x169d2784294c006a04100300980004 :=
  finish #[
29973763125,51471674463289,29974496781,4151,4121,29976908214,4150,10482882,0x9fab0f7d620aee51c,4151,12386526,12252223,12312798,17962009681,4141,
4161,59459933894152,14635056,61391862535330,4160,4184,10616926,4172,53405085205699,45653321699600,8770209,9642416,4183,4177,4189,
29064386056,0x195d62093bd5604,10616902,4520,0xdf475e7c493bd5257,8769590,61395551245494,0xdf57ab621101324b6,4177,4989,40449647531202,40454207816781,4165,4177,0x61ac437aa2fa5722044d,
0x18867c6572fc2e2,11444293,4154,4161,4182,4189,38522228831753,19599799820,82200855541199956,4154,4159,27230688886,0xdf57990d53fa6d1b6,4150,4198,
29975540605,26135422023,61392625922920,4196,5183,0xbacbef2b947ae7430,0xbac4eeef82eca6674,4160,4196,4154,4190,8770863,0x195c12d78afc676,10616897,4177,
4172,8769804,27231514892,14635051,5750,13297270,4190,0x9e05b422efa85d608,9654701,4177,4195,4180,5423,21746373935,4196,
14636335,36786666455922,12849252,4142,11972694,4152,4208,4184,4168] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part29 : Refutes moves 0x6000000000800000000000000000 0x149927942800000a00000300180000 :=
  finish #[
13296289,13297161,0x9d6afebbec44ae182,0x3632571ffb10f3e17c396e7,8728634,4189,4180,13263465,13288960,21748172070,5423,59366331847981,4180,11812898,4145,
14188625,29060366542,55449517482825,59515635164117,0x195cd32560c24c1,4195,8728657,4189,4183,0x195c881b5d1b27a,4152,4176,55768310646060,29986669871,27232911886,
4161,10999085,29060366388,4202,4985,98817898789405294,11444305,21746386223,8753374,4195,4190,4189,5641,29021102846,14169371,
8769754,4198,4195,12849370,53893974135006,4175,4182,4189,14636548,85183937423782980,4208,14189548,29974726153,4202,5314,
11973826,4184,55548836807874,4175,4189,4182,51274707718288,0x1bea2a620d8826e,27154305242,12849374,4182,14209117,4165,13198530,59515634599191,
4183,8769755,11972701,13742192,4164,4176,4152,4312,0xd8d18746c2c85d609,4199,14144226,13295796,0x195d1021c49a60b,4166,4157,
36055252587810,11956317,51892344939561,55366334629058,14188609,0x179562220ca53e8,10616884,0x192c12e8da203e8,28147348129,59498453517288,4168,4165,4318,4308,0x16cebd42b85936f,
10616931,4187,4190,4189,4182,4172,59357057810954,0x896a3a2ad39d88604,57404186297870,4187,4202,59314852492482,27249624040,59521011815073,27123938024,
10477628,4183,4168,4148,5096,55777778659766,4174,26318631791,11490497,10616904,4182,28146348355,0xd876aebf28da20372,4182,8769755,
4190,4199,10170461,4208,4180,4196] (by decide +kernel)

private theorem part27 : Refutes moves 0x6000000000800000000000000000 0x149927842800000a00000300180000 :=
  branch 1 0x6000000000800000000000000000 0x149927842800000a00000300180000 92 0x169d2784294c006a04100300980004 (by decide +kernel) part28 part29

private theorem part25 : Refutes moves 0x6000000000800000000000000000 0x149827842800000a00000300180000 :=
  branch 1 0x6000000000800000000000000000 0x149827842800000a00000300180000 104 0x17982f946900000a00804300184000 (by decide +kernel) part26 part27

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part32 : Refutes moves 0x4300000000800000000000000000 0x1f2cbcb14f0000080280610010c000 :=
  finish #[
22378218690,18752107714,4180,10974402,29093783163,4138,29061706478,11509844,4198,59513693221073,14663889,30031545865,0xbb4b07282fe3d820e,4162,4154,
25435542345,4175,26178724939,43649665229211,4149,18779484602,11509845,4156,4198,4852,0xb56bf92c17d58834f,0x6c658d9610e8288581ea,4185,4190,0x16d020620b673d9,
50167798195489,17903517760,4172,4192,4187] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part34 : Refutes moves 0x4200100000800000000000000000 0x1e393c210984404a06102100908004 :=
  finish #[
4769,0xe6958f7f024afa11b,4198,4301,11490934,4207,36497226380918,4982,0x192888144df53d9,97099917724922059,4168,4208,5755,0x1886dad7d368349,10506325,
4150,4190,4160,4165,48314356274367,0xafc6b0ebef9df55fd,29976081602,4152,4208,5757,4756,89429691407361301,4181,4187,29064384892,
0xaf51f77cec42ea60e,4168,4987,53689720333942,10563675,4174,4154,29976080826,5100,25395447305,4182,4186,5100,24522097858,4174,
10608713,4185,4190,4199] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part35 : Refutes moves 0x4200000000800000000000000000 0x1c293c310800000802002100108000 :=
  finish #[
41790555006129,5317,47771003364635,4191,0x16d7620fdaea676,0x1b117d57aaf83ec,4172,4186,4193,0x2795a7051a3640db3588677,21477959168,10616906,24497247193,48288227263449,4177,
0xc37beaf411051b3e4,4176,0x1b197d427d1b59a,10618043,8745036,4186,4193,4187,0x411bccb117d5738593c9,0xdf575f6216e2f51e3,61362105848409,10543195,4209,37340993087094,0xd8d9357d5074410b8,
23530410875,4190,4186,29974671787,29977413020,4177,4769,28146910402,4165,4182,61394640090306,4208,4176,4152,0x2d9d643686ac30e8d85767b,
29053318341,12371138,4177,10543986,4154,10565020,36717929309378,4185,4190,4199,5206,5746,37653919884374,11509839,4163,
4961,11510639,4177,0x1beabf02813936f,4181,11961185,0xbc677d7f0282fa29e,10608721,4209,4190,0xd845f4d9ec45f5515,11895103,49995016734003,4163,61389995017033,
14635318,12351094,4154,9670723,4190,4181,24364537139,29978727039,27107161174,4172,59569924895375,24497857622,4177,4149,4163,
4756,14665229,55320700679798,4172,14189204,59517043110889,50152493782537,4202,4172,4187,4181,59369252619223,10605545,10608718,4185,
4190,4209,59431582660105,11894957,14193279,12408328,4175,4193,61464264921743,59515053532135,9916483,4126,9048106,18775783030,0xd8c8877d64a2ee37b,
23497774056,4181,4172,51649081107652,4209,13742174,4140,10170436,4208,4180,4204] (by decide +kernel)

private theorem part33 : Refutes moves 0x4200000000800000000000000000 0x1c293c210800000802002100108000 :=
  branch 1 0x4200000000800000000000000000 0x1c293c210800000802002100108000 92 0x1e393c210984404a06102100908004 (by decide +kernel) part34 part35

private theorem part31 : Refutes moves 0x4200000000800000000000000000 0x1c283c210800000802002100108000 :=
  branch 1 0x4200000000800000000000000000 0x1c283c210800000802002100108000 104 0x1f2cbcb14f0000080280610010c000 (by decide +kernel) part32 part33

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part38 : Refutes moves 0xc100000000800000000000000000 0x172a3fd8cb00002800804180304000 :=
  finish #[
23576011845,4976,12338361,23482835470,4170,4142,17827049675,4175,4181,29063013454,27164898825,13193304,4204,49585436796421,45381090747669,
4142,13297165,53575962493364,4171,4181,12846605,0xcaecd3271b3cb1348,4165,0x1b1127c94c41522,59520995485183,0x193e4a6573674c2,4180,13312060,4142,17795810593,
0x1938bbd664ae60b,11509788,4184,4198,14206473,0x1874f36c64ae528,11957551,12394580,4165,5423,25086846698,19674858471,10059851,4165,9606222,
49728595825953,0x64a92992d0e1af3683e8,4173,9191539,4199,4181,10478769,11408360,4180,51686187946854,23576863935,4204,4149,10060656,23483278072,
4163,23483220728,23483286264,4163,4149,11956984,13304692,9191498,4199,8740949,4184,4185,4189] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part41 : Refutes moves 0xc000010000800100000000000000 0x152b3d0a4a511628c0520181308007 :=
  finish #[
18174600497,27229791527,4189,13297161,61515812107461,4165,0x6fe5880b5296583673e9,4188,4180,4297,0x184d7d334c953e7,4209,11305466,0x16b0b224dcb0174,12337255,
4133,59580578428207,4156,14627909,5189,0x1962626564b04c3,4188,4199,0xcb00f90e1e685a516,45964313388217,4180,4156,55636270724269,36429177979982,4189,
51529738147119,5198,51370303845114,4204,4189,5198,0x16cf2b894a143e9,10485868,4170,4190,11961529,50173304931849,21479745140,4135,4190,
5408,53741103334132,0x1b097f0ff4ae3e8,13234270,86151674564797743,4147,4169,13267004,4153,4175,4186,4183] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part42 : Refutes moves 0xc000010000800000000000000000 0x152b3d080a500629c0000180308000 :=
  finish #[
17788757277,9606447,4165,0x19384a6570ad0c9,4160,55773167665896,13268271,11952665,4165,59518382089519,4199,4189,13742299,4140,4188,
14190194,57651316033033,4189,59512269501275,4159,0x178146cbaa73609,4156,27171086661,12321768,12411103,4160,4165,13267683,24490370338,4165,
0x193f5fa8db4e3c7,4131,17974629897,57650344727408,4142,46063413051692,12395576,4165,4156,55356529688962,27081991129,10981445,8773853,4193,4189,
13295718,4168,4190,13296042,19671672111,4199,12764789,0x1bf3631779fe261,4153,57644765865485,5095,27232499100,4159,4165,78168895878443734,
26325542525,8765497,4193,4189,55778709288242,80725191688488349,17788765478,14663743,10982132,4156,10958450,14188869,13198192,4159,8773717,
4193,4199,28146857155,0x3270948c4bf925af9d1b370,13742281,0xcb093928efe04852d,27232498320,4209,8773695,4190,4199,0xdf1b109e5e951b0df,23362491677,0x2eb894cae4e746d778370df,4165,
11956287,4156,4164,4204,4188,27232339346,53545325396848,4165,10958345,48091719779849,9192163,4193,4181,21603260024,10547962,
21437809947,4159,13295686,42057964315625,4193,4190,4199,27234776040,29096568330,0x16d16125743a609,28144164957,4198,28146856582,0x175cbbe8da7952f,48094619985308,
4178,4156,5532,97131331105379184,4190,0x16cf7dac4c9f52f,24499582589,42134966896028,4147,0x17880da4fbd64bb,4160,4165,13267004,4153,4183,
12849220,4142,4182,4202] (by decide +kernel)

private theorem part40 : Refutes moves 0xc000010000800000000000000000 0x152b3d080a500628c0000180308000 :=
  branch 1 0xc000010000800000000000000000 0x152b3d080a500628c0000180308000 56 0x152b3d0a4a511628c0520181308007 (by decide +kernel) part41 part42

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part43 : Refutes moves 0xc000000000800000000000000000 0x152b3d090a00002800000180300000 :=
  finish #[
14635664,0xe666d10c0ca43e441,4189,0xb583317d42f2fa2d9,4191,0x507368bf8b6a20df5261,22645760891,55770395783391,4199,4190,21598525044,0xdf740a4a6facae456,0x1be84cdd94ae533,57307657081943,0x194d10efaa0f0df,
14636660,61376544437555,11055183,4186,4202,4180,61410904237023,49728594093033,10584159,4189,4199,11972702,4160,4168,55463963112966,
8741074,4185,0x6fa013260f5a57588528,0xaef17e802c436b676,4152,5641,0x195d622fa36b517,4176,43388300919664,0x5e25fc67d0b21c1330a4,4169,4193,0x6fe438b112b860afa370,4156,4163,
53945473623677,4306,14640089,27215721425,4159,55776820074102,11972698,4152,4176,5100,47972494963106,8765530,4193,4189,4198,
93855439234196564,0x2039a74ae78346e20b6b349,4176,13742745,0x30eafa933b192ba5336b4b5,4160,48276187768329,4191,10170470,4204,4188] (by decide +kernel)

private theorem part39 : Refutes moves 0xc000000000800000000000000000 0x152b3d080a00002800000180300000 :=
  branch 1 0xc000000000800000000000000000 0x152b3d080a00002800000180300000 88 0x152b3d080a500628c0000180308000 (by decide +kernel) part40 part43

private theorem part37 : Refutes moves 0xc000000000800000000000000000 0x152a3d080a00002800000180300000 :=
  branch 1 0xc000000000800000000000000000 0x152a3d080a00002800000180300000 104 0x172a3fd8cb00002800804180304000 (by decide +kernel) part38 part39

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part45 : Refutes moves 0x84000000000800000000000000000 0x17baa460080220080000010a100000 :=
  finish #[
5297,27079246929,4183,0x6c6ac1afb272130c843e,27231536638,4159,4149,94283347101836809,13296817,13296817,97344393823749398,4171,4162,4850,4858,
8750142,4184,4858,0xbcd77b42d41df534f,12849240,4142,11956320,4156,4180,4196,61515814822754,17856779441,4850,4976,8717168,
4183,4174,4172,19707889166,0x1b197eac1afa95d7d5b3aef25f,0x65704a94c9c4280c8354,4183,4185,4193,4181,26256704817,96875679300382930,61388001477499,4193,10616919,
4192,4177,10617705,10015720,0x1768f3e572204a7,10982594,4156,4192,91212868000761117,4160,4185,0x1a40322fe2e758b,0xdf3190b9c2d22052f,4192,11461826,
44536408683496,4188,53900558287727,4185,0xa5cbf34225749b6ea,0x1957621d74410db,13742176,0x52e4347acbe2572146e8,4185,57650369455298,27233416168,25286833346,55773163090300,4174,4192,
4180,18845287605,23533174873,4158,4168,4175,4193,10950158,13742834,4164,59511271195476,90408797671728758,4164,11518831,4182,
4186,27264631517,47615470985846,9622600,4175,0x1b10f1db3afa67d,4156,4191,4163,4987,30016668652,5314,22394119248,4150,11345977,
4144,4746,50221134365999,4191,4149,39604164993557,22644438096,11518625,4182,4168,4769,50221131203421,10170447,4188,4196,
4192,5192,14189544,47304286307849,4202,4193,29976080805,10563680,22528333103,55767539368702,11972703,53900591857887,4174,9208673,0x1875112c421e149,
4175,47833304216225,10604640,4180,4185,4195,4184,4200] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part48 : Refutes moves 0x24000000100800000000000000000 0x1cab24924824124804824120900100 :=
  finish #[
30007833082,29974091268,63379106116694,4192,26251076223,8721495,13295712,4124,4190,59521119528213,27231650683,4192,10618029,23589143746,4189,
14189217,11433153,21746402825,4175,4189,5174,27106722243,4193,0xb668832b97e2204c1,4192,23593612809,59520993698314,51843545826934,11473569,9667442,
14189437,8774514,4190,4199,4195,4193,4189,11956320,4156,4180,4204,4196,4172,5097,48076583583956,
4186,21746779443,61472931366409,10171106,4192,11347247,59585963476162,4196,4172,4193,10617396,55842832806070,0x8369351042f22060d,4202,5639,
55648301847421,21746393182,4184,4198,4163,4177,20832482607,11518952,4186,59592597963391,59514369831585,29990564362,4189,11956897,4148,
4204,10170578,55772771091105,47597394519565,12370795,11518516,4172,4196,4193,42662181708996,4163,4198,4184,4177,5097,
48076583583956,4186,14189497,5637,4971,59518376460817,4172,4196,4193,10618052,50159952199903,4769,4769,18841191400,4199,
4193,4189,13305026,21747742222,4174,0x1880640d9a2033f,10617256,19881813076,4189,4199,11509857,4184,4198,4163,4177,
5097,48076583584851,4186,14189869,4971,23357015557,4172,4193,59521135412518,10617051,5639,19885471239,4190,43898217039151,11509856,
4184,4198,4163,9441361,4122,4152,4140,4149] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part50 : Refutes moves 0x24000000000800100000000000000 0x1cab25924920124804120120900004 :=
  finish #[
5641,29062972461,0xd8cbf56216913e211,4195,4189,36482914952267,4170,14190203,97129451116848649,10616917,4187,23574217901,23589143201,4189,55651713811977,
4989,23439098075,4195,4189,5414,0x192cb56580c31ea,4186,48276162602287,4193,10617725,0xa76bea1791036735d,4156,4172,0x1b100282f2792a1,4769,
9679730,4198,4189,53916408427925,97135036186211503,4165,4769,12420057,18842154073,4193,4189,11956327,10170420,4208,4180,
4204,4196] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part52 : Refutes moves 0x24000000000900000000000000000 0x1cab34920924024900000124924000 :=
  finish #[
29061268092,5641,0x6fe6665181defc9fe609,4183,0xd88bf81dcff5f127c,13296247,25034622589,61458566899209,11460693,4151,4189,4165,0x1a397f170588083,24299160638,55772030199310,
4193,4181,17617531993,0x1bf8a31701fe3c7,47429270425697,10014762,4154,4146,4961,14197615,0x1b1a4fd702802e3,4163,4181,29941502158,11518156,
23594997259,29941620942,9695319,4202,4193,0x16b1436fad8d16b,10995209,61395548284207,0xc2201d7d40a2fc349,4182,14636109,0x1b10bf0c85f5361,59605196744315,11067486,4187,
4195,4181,11509857,4156,4177,4184,27231651453,4769,12358850,21746288253,17233244300,11433486,59603203392353,4163,4181,
19598017274,4177,4168,4186,4165,0x975b1b0d962ae008b,55545646835322,4177,89909200674886730,8773718,4199,4193,55770421896482,38540857705327,21743657176,
4195,4193,11973499,61515813532867,8729469,8765526,4189,0x18837d5b59b31bd,4204,4208,4184,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part53 : Refutes moves 0x24000000000800000000000000000 0x1cab24900920120900000120900000 :=
  finish #[
29064413593,59523918516532,4182,0x40180ebf813ac4358520,14209639,4139,14210132,11896334,26159253115,11067459,4183,4193,4189,0x942b112cac6ac8451,0x17aa9e9644ae211,
4157,4190,55520041866752,0x1b112b8ba9896ea,4158,12224009,29062170237,27175624789,11956267,0x9fe3eab224fd88515,21254145659,14197519,30949499833,29063045187,8704061,
4187,55777781383795,0x84ebe27cac6d886ea,5646,0x1cd29e9e557f60b,4190,29060818223,4183,4193,11956315,4196,5096,73702304474760269,5096,5096,
24366339703,0x1a2d7eac428e3c1,4193,4195,4183,11509845,14635089,4170,4184,4156,9667560,23592334313,0x195cb9db3138457,4174,8757317,
18617889212,0x192c0d6fe58851d,9704753,59523921708311,4165,4189,0x19645b455b6760e,17952006783,4198,4193,4199,4769,50152318567293,21458444509,4199,
4193,24488575199,4769,10618152,21748118383,44540304409469,4199,4189,4193,12849239,4142,4182,4202,0xaf80ff619b3c41444,27123938171,
0xcb06b12b97d22025f,4182,0x195cbf061a2060e,98883050871842095,4195,4193,4190,10617723,61386273441289,10170461,27235668189,59362845057875,23497282754,4196,4186,
0x1938b22fe0b9147,28027642697,27231203430,11972716,4168,4208,4184,13742176] (by decide +kernel)

private theorem part51 : Refutes moves 0x24000000000800000000000000000 0x1cab24900920020900000120900000 :=
  branch 1 0x24000000000800000000000000000 0x1cab24900920020900000120900000 68 0x1cab34920924024900000124924000 (by decide +kernel) part52 part53

private theorem part49 : Refutes moves 0x24000000000800000000000000000 0x1cab24900920020800000120900000 :=
  branch 1 0x24000000000800000000000000000 0x1cab24900920020800000120900000 56 0x1cab25924920124804120120900004 (by decide +kernel) part50 part51

private theorem part47 : Refutes moves 0x24000000000800000000000000000 0x1cab24900820020800000120900000 :=
  branch 1 0x24000000000800000000000000000 0x1cab24900820020800000120900000 80 0x1cab24924824124804824120900100 (by decide +kernel) part48 part49

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part55 : Refutes moves 0x4080100000800000000000000000 0x1ebb37089b24044884308100902004 :=
  finish #[
41597658071534,0x2406fe0872da5d49da20349,4987,10617276,12411324,4174,14635077,4184,4198,94127549425366646,20670809723,29957948723,61362167637043,19526566561,30034748264,
4189,4174,55720668058818,4175,4165,51736792400947,10617276,4769,47424645235579,9667451,11055548,4202,4186,4198,11972686,
4208,4184,4160,10617836,10617943,5100,44537564079393,4198,4184,0x1bf8476fd1a04a3,11490284,61388237251670,4198,4195,4189,
13295706,4157,4190,4168] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part56 : Refutes moves 0x4080000000800000000000000000 0x1eaa37189820000800208100102000 :=
  finish #[
23295841917,23299171965,13295658,14635873,0x4f5bd60faedd778572e5,4195,27081549103,4163,5532,23575004572,29976080460,4176,4184,13297052,4962,
23572345705,4185,4191,0x1beadae20cae2da,11862896,11953008,4163,4181,10478786,0x6571f2965109778535fe,4181,0x65750a882159b40c159c,0x1bea14e20afc520,0x18850d973aee3e9,4144,
4158,4200,10616922,4172,4182,15111121,13239574,4171,27114566617,0x16cca2e570bd27f,4186,4184,10982594,12850263,0xbc003c7ca21057349,
4186,11956312,4156,4769,0xacc9297f24aa20457,0x16ce6811013813e,4189,4186,4177,21519009290,5423,76405857853657929,24491700293,4164,13296122,
55722296894767,89353708612953725,4169,11956293,11510433,40443053192057,8745172,4185,4189,4186,4184,4769,30033445510,5314,53538648097769,
4961,0x1690da170279370,9678920,4198,4186,4189,4165,88859255702160789,10478241,10617273,11490152,61351932331311,4177,4165,4189,
4186,55841459782851,0x1668bbd103c967d,4165,0x195cf251013859c,11956317,4156,10170436,4208,4200,4204] (by decide +kernel)

private theorem part54 : Refutes moves 0x4000000000800000000000000000 0x1eaa24000800000800000100100000 :=
  branch 2266 0x4080000000800000000000000000 0x1eaa37089820000800208100102000 92 0x1ebb37089b24044884308100902004 (by decide +kernel) part55 part56

private theorem part46 : Refutes moves 0x4000000000800000000000000000 0x1caa24000800000800000100100000 :=
  branch 1 0x4000000000800000000000000000 0x1caa24000800000800000100100000 113 0x1cab24900820020800000120900000 (by decide +kernel) part47 part54

private theorem part44 : Refutes moves 0x4000000000800000000000000000 0x14aa24000800000800000100100000 :=
  branch 1 0x4000000000800000000000000000 0x14aa24000800000800000100100000 115 0x17baa460080220080000010a100000 (by decide +kernel) part45 part46

private theorem part36 : Refutes moves 0x4000000000800000000000000000 0x142a24000800000800000100100000 :=
  branch 1 0x4000000000800000000000000000 0x142a24000800000800000100100000 111 0x152a3d080a00002800000180300000 (by decide +kernel) part37 part44

private theorem part30 : Refutes moves 0x4000000000800000000000000000 0x142824000800000800000100100000 :=
  branch 1 0x4000000000800000000000000000 0x142824000800000800000100100000 105 0x1c283c210800000802002100108000 (by decide +kernel) part31 part36

private theorem part24 : Refutes moves 0x4000000000800000000000000000 0x140824000800000800000100100000 :=
  branch 1 0x4000000000800000000000000000 0x140824000800000800000100100000 109 0x149827842800000a00000300180000 (by decide +kernel) part25 part30

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part60 : Refutes moves 0xc000120000000000000000000000 0x153b7c8045a698c300124800000000 :=
  finish #[
4319,72977009890411334,9605314,4171,4168,0xdfc93e10620cb252f,4142,5314,0x83895ef26fab6b42a,4160,0x80fbef7d5e0424349,76362310377277049,4161,10564583,24520286291,
4190,29995062107,4532,25035624644,4186,4211,10544431,61513981531095,4171,4179,36410270069574,11509824,4177,4184] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part62 : Refutes moves 0xc100020000000000000000000000 0x172a3e50c1a49a0304000800000000 :=
  finish #[
11302193,11920907,0x96d03b2b9af368531,4157,4171,5423,0x195d0ba4acb11aa,10477643,4143,19399291879,24480048179,4158,0x1beb2b9b33d62d6,4174,11510399,
4177,4156,29086425722,59471408636543,81757583400657530,0x913b17622532fa524,4177,4149,0x186d9997d5853df,11469691,4174,23600174598,4166,4180,4187,
4202,73301735825417083,9621698,42014616495625,12849206,4162,5397,13223215,8656618,9162827,4174,5408,40357084492656,4174,4202,
0x179b27e55441127,11510076,5408,40464953603266,4174,4187,4181,0x6c40adbe327ebf4ae44d,5314,48287338860854,11468870,11956315,4204,4156,4180,
4172] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part63 : Refutes moves 0xc000020000000000000000000000 0x152b3c1000a0980300000800000000 :=
  finish #[
11888253,4934,5423,24414422093,4165,4171,4157,4934,5408,14189856,29062157600,9646141,4193,55766392534537,4170,
4171,4172,11511064,0xd1131b2c97d36712e,4172,4156,55520041362509,13235721,13702668,55520036344009,4172,4162,4174,78200285325927715,4191,
10543495,0x1ccd7f1e52fa294,0x1bf8f297d3d5294,4150,11956321,4148,0x3266bfb46b0cbea56b67130,13190120,0x9fe9392ba4f84109346db3af7349,4174,11407445,4187,4209,11493597,27232919947,
28144046279,12812509,30035633455,11498681,8650865,4170,4160,4193,4171,28144148674,42031858967511,0xd1b08c1057b2f7348,4209,4202,0x83995d2702f27367d,
0xbd25b417939af759c,11956315,4156,4204,13234395,28144047392,4171,27107161175,4156,5423,36774894396265,17956479153,13234236,57648514232592,5408,
51591688053624,4169,4160,4165,4187,8766876,42007091843246,28145870456,4168,4143,9078397,23550846012,4187,27108053056,4182,
13312106,4142,4987,4317,0xd889611057d05c52f,29976957364,23575098889,4174,4209,4181,4187,0x195ab868d85c60b,0x6515fc93eb6a8daf6433,48234857967837,4199,
4181,4412,57648515125564,4142,18799248672,27200328518,26315854711,28146901074,4177,11972710,4168,4176,14189435,61511997977686,24428885078,
27229806677,4202,5314,27106506360,27105768642,8773695,28147363942,10170448,4204,4184,4192] (by decide +kernel)

private theorem part61 : Refutes moves 0xc000020000000000000000000000 0x152a3c1000a0980300000800000000 :=
  branch 1 0xc000020000000000000000000000 0x152a3c1000a0980300000800000000 104 0x172a3e50c1a49a0304000800000000 (by decide +kernel) part62 part63

private theorem part59 : Refutes moves 0xc000020000000000000000000000 0x152a3c0000a0980300000800000000 :=
  branch 1 0xc000020000000000000000000000 0x152a3c0000a0980300000800000000 92 0x153b7c8045a698c300124800000000 (by decide +kernel) part60 part61

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part65 : Refutes moves 0x40000a0000000000000000000000 0x1c88a42480a190110002a800000000 :=
  finish #[
4723,10958342,17728697538,4172,4180,0x4213d36852c1b3b6b59c,0x6fd2fc8591089905d273,4198,4200,11510399,23577789061,41942455334409,4166,0x6c45f916a2f57d367520,4180,
4172,17688998849,10564239,4174,11957089,11973499,4208,0x6c4441426be9b3af5379,4182,4172,4200,59518411793710,0x6fce69b072ba57d88515,0xc948824fa8db6b4b7,11509856,
4163,23358791903,0x6570986ce5e1a02fa361,4184,0xd88bf57f2c1d20530,0x1b012be572ea37b,4154,50218220299439,9715935,4204,4192,23558341608,4172,4182,9281636,
4201,4205] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part68 : Refutes moves 0x84000020200000000000000000000 0x179aee28a8a2b0a110a10808080800 :=
  finish #[
0x19630d5b5df518d,23242691419,0x1beab49ec4250a3,4154,4144,0xad2beadac899924b0,10563643,10563806,11519609,23356985566,4151,4172,4196,5641,53903304032901,
4132,11501787,10564115,4184,4200,4756,48248379515766,4196,14189425,0x192ad9ec444152f,4172,10543635,24488129405,4196,4200,
0xc94582ba1b3af6304,4166,4202,4180,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part69 : Refutes moves 0x4000020200000000000000000000 0x1d8826282022b00110010808080800 :=
  finish #[
4713,12272833,0x1880ed255ae8527,4166,0x194d0e1ec441447,4172,0xbd085cbda202f042d,4174,4180,28970279916,5400,0x18712b6fab6b21b,4160,57646501856886,0x9ff3fd46de34414a5,
4162,27224142828,4160,4188,4180,5750,12800222,11972702,4968,46344148734350,4190,23530426903,53541600284894,4161,85113908619555038,
4160,4168,4172,0x5702e3082d9e8d9b3609,20829295127,4190,4188,4196,4200,5096,23592350696,4168,23590048308,4178,0x4eadf1882839a8213676,
11972802,50224711808081,40568905687124,4171,4195,21344478838,0x1844b15d736b52f,4168,26056287161,4178,48072516437165,4163,5641,59511823147849,4204,
4989,14189423,57353712886205,19832009569,4198,4204,4202,26058522700,5097,12804631,11919415,4163,4195,5313,5408,
13279548,13300577,4200,4158,12846253,4163,53879722373438,4204,4196,25422390248,0x533e690832b9b3368516,4163,48076582237161,4200,59489502823609,
48112538940828,4200,51289218934506,27147318116,4200,4196,11470128,30948655951,12411444,4156,11894884,12731575,23241311212,0x188346e121b336f,4196,
24414412904,4163,4179,0x451c4192ed9d742f6679,4166,4202,9281635,4209,4201,4205] (by decide +kernel)

private theorem part67 : Refutes moves 0x4000020200000000000000000000 0x158826282022b00110010808080800 :=
  branch 1 0x4000020200000000000000000000 0x158826282022b00110010808080800 115 0x179aee28a8a2b0a110a10808080800 (by decide +kernel) part68 part69

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part71 : Refutes moves 0x4000020000002000000000000000 0x1c886408022a900102000a00001081 :=
  finish #[
0x1b107f89ca1367a,14664671,30037017796,8675770,4172,11509839,4191,26143360413,9696125,4196,0xb67b11600a1442678,13747835,11920143,4181,10051677,
9281635,4201,57648491300470,48285513401865,4191,23416173535,4172,98212680902063071,4208,14189079,0x2d3800d80a36d9cd9938533,4180,59380939731816,5643,59327982917121,
4139,28147348347,10170428,4184,0x1bf8f35eb3674c1,0x1844125b393237d,4189,9281614,4209,4201,14188736,43966935966325,4175,59514719019262,4205,
29998040585,40602214180473,4205,4201,61317599098163,9593698,4168,35567639486914,5305,26241311917,8765553,4193,4199,5641,55567005098823,
11509839,0x61c367afb6182e85e4ad,4201,61385504433432,79753990106428505,4168,4208,4184,8643767,18548106082,4209,12853779,8676328,4969,72164352474416067,
4174,4208,4209,9642175,19748074472,4205,4189,4204,36783420502363,5100,24521684598,4204,4208,13742168,4140,
4176,21375854198,21459842573,14188656,0x276c02356cd23d902213676,0x9b3bf9621a33563ec,30032999261,14189858,24346861671,4170,4191,4205,14635635,40503029433539,4180,
27149119926,63334969259421,0xdf895746ec42e24b9,55794916644016,4180,8769649,4190,4200,77183631292867890,4531,19750752580,4156,4174,4955,23363564379,
4204,4208,20586538157,4199,4205,10616937,4182,4202,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part74 : Refutes moves 0x4400020000000008000000000000 0x14ba664c4221f0a110008880002000 :=
  finish #[
11956500,23559173757,13295709,23593674005,11519279,11510653,14663754,4163,4660,0x1684ed1e34ae515,30032999060,11972708,4176,4192,4184,
4934,23592351357,13295712,11068579,0x16d62b22036837b,4163,4171,11509921,23413884207,4189,55342755591694,0x16c0be89c36b6ea,13295728,18770223296,61419639911401,
23534954109,4124,98960918454154217,4208,11956328,4172,9281628,4209,4211] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part75 : Refutes moves 0x4000020000000008000000000000 0x148e26080220d0a100008800002000 :=
  finish #[
5408,23131411215,26055304061,0x346e573ca3ea11a4ba8e4a6,57403433112653,4150,4195,5173,13751382,27012624438,4208,4190,4184,0x1a36d9e5928652f,9102069,
5195,4934,26143359727,4171,11509815,30033765569,78205999762588479,9695331,4196,4190,4184,4163,4987,13235710,0x1a37271deb42085,
9516320,4137,4140,28995921526,24486646405,4176,4169,24182244871,23573221679,4169,11407427,4188,9102613,0xd1b25abba5736710a,23247822948,
9281564,4209,11404700,0x1a364edb39b3361,4204,23575557532,4723,0x17707ca4b05e33f,4190,13743287,11509983,14663782,4163,9282100,4209,
4195,4199,11973164,23365378495,4209,21374559533,8770972,4189,4660,20829807483,4211,20832499100,4176,13295728,4190,
4168,4318,4534,11379126,42660210284045,4188,4209,4208,11973225,0x195cf282e92f601,4180,4168,11408219,18821895225,30035190967,
9643094,4174,4168,4540,11408219,4209,4208,9692140,43747289604703,23572373723,4190,9281636,4199,4211,10616941,
4182,4192] (by decide +kernel)

private theorem part73 : Refutes moves 0x4000020000000008000000000000 0x148a26080220d0a100008800002000 :=
  branch 1 0x4000020000000008000000000000 0x148a26080220d0a100008800002000 106 0x14ba664c4221f0a110008880002000 (by decide +kernel) part74 part75

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part77 : Refutes moves 0x4001020000000000020000000000 0x14b8a4981620d2212a040820000002 :=
  finish #[
14189521,8676166,4172,5096,28150043734,4934,8680751,4171,4172,0x195cd9e514af605,4158,4202,4156,11510598,5073,
48281324115248,4201,4181,9969967,0x16ce4909fc4036f,4193,0x1b10bea173682e9,0x1bf80fa8d8453bf,22518596551,4189,61511248208847,4151,4159,4195,4171,
4163,40565146140870,21640020278,0x16a16210219e52e,24489467983,4156,29992207772,11956534,4156,61464181634678,63389333615915,47612415721844,4154,4144,55704445494575,
0x16ce2aa57209285,9969722,11407427,9281642,4201,4209] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part78 : Refutes moves 0x4000020000000000020000000000 0x148825980220922128000820000000 :=
  finish #[
24486716719,23592333753,9281755,4199,4211,0x92c95cda05e8da3e1,11502443,20832499100,4208,4200,13280236,0x16852bac41b3673,4196,48007895426001,4211,
50227727336748,59516175753500,45656803844380,20832481385,11509844,4163,4156,4184,21468230960,0x1b141dec42e1522,87371395881096713,4198,4201,21553455668,98736476985701007,
61504337454263,29975544058,23575094248,4174,9281635,4211,4201,4205,24432981057,8643560,4166,42170367796397,0x6201966cf622571326e8,4189,0xe67a37621b3cae340,
0x195d46d3e05c3d1,9281629,4205,4199,0xdf57aa48d7d3672e2,0x1a372b82e85e454,4201,48286398101001,5532,0xdf508d46e571b31b0,11972692,4168,4208,4184,4176,
29063033454,25411184137,4168,21459739948,4155,13284865,0x1a380aa5344052f,14155959,4155,4153,23376462464,0xdf55c52c64dafd601,4180,4174,4201,
59590772372764,23491686838,4168,5413,29058385308,10482988,4174,4168,10068261,10170427,43747287355956,4201,4196,4200,11510202,
59517464326418,0xdfca10f557521358b,10170446,4200,10503035,14189411,23206023813,4180,4181,28145955461,10171372,4196,4200,0x1794be9a74ae36b,26225788297,
23575561067,4179,4165,5100,50219403084657,4209,4208,4317,0x6fcd84a376217d36b234,9281648,4199,4211,4201,10616941,4182,
4202] (by decide +kernel)

private theorem part76 : Refutes moves 0x4000020000000000000000000000 0x148824080220902108000800000000 :=
  branch 3142 0x4000020000000000020000000000 0x148824980220922128000820000000 96 0x14b8a4981620d2212a040820000002 (by decide +kernel) part77 part78

private theorem part72 : Refutes moves 0x4000020000000000000000000000 0x148824080220902100000800000000 :=
  branch 1 0x4000020000000000000000000000 0x148824080220902100000800000000 51 0x148a26080220d0a100008800002000 (by decide +kernel) part73 part76

private theorem part70 : Refutes moves 0x4000020000000000000000000000 0x148824080220900100000800000000 :=
  branch 1 0x4000020000000000000000000000 0x148824080220900100000800000000 61 0x1c886408022a900102000a00001081 (by decide +kernel) part71 part72

private theorem part66 : Refutes moves 0x4000020000000000000000000000 0x148824080020900100000800000000 :=
  branch 1 0x4000020000000000000000000000 0x148824080020900100000800000000 81 0x158826282022b00110010808080800 (by decide +kernel) part67 part70

private theorem part64 : Refutes moves 0x4000020000000000000000000000 0x148824000020900100000800000000 :=
  branch 1 0x4000020000000000000000000000 0x148824000020900100000800000000 91 0x1c88a42480a190110002a800000000 (by decide +kernel) part65 part66

private theorem part58 : Refutes moves 0x4000020000000000000000000000 0x140824000020900100000800000000 :=
  branch 1 0x4000020000000000000000000000 0x140824000020900100000800000000 111 0x152a3c0000a0980300000800000000 (by decide +kernel) part59 part64

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part82 : Refutes moves 0x24000000300000000000000000000 0x1c0936b2c48cb000168b4000000f00 :=
  finish #[
4311,5314,22398878893,72363396481508289,4195,4190,12850254,8770754,23533158502,4179,4207,9659257,0x16d06582c85c3cf,4195,13722672,
22351115072,57557733012331,98327508979057968,4173,4147,41742730211395,28992349818,27038572986,61386379526670,4147,55751378712186,4140,4150,36679802631354,4192,
4190,5168,35350890419617,4142,0x55f80b367482c3b584c2,4179,0x16bc08cff42433f,12251700,12850224,11960366,4157,97085769189631170,26317111489,14184490,4161,
4163,12731809,11490607,8769619,4538,36611032823293,4192,4184,11956318,4172,4204,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part83 : Refutes moves 0x24000000100000000000000000000 0x1c0924924204900004824000000100 :=
  finish #[
5096,0x16d12b82b1b3211,4184,35213443449022,30010474689,4173,29054657730,59521121719356,4154,4142,0x6fb3d29380fe5758c0df,4156,27230638607,24486724106,4193,
4189,38322992824729,30036971713,36296710702717,4189,10170465,9646716,0xdfcb104ccc6c4352f,4154,4660,4288,14144124,17952006223,4193,4192,
4190,14173487,5754,13292621,4158,27224601012,4172,8765656,4192,11509857,4156,4184,4198,8766079,14157079,
10982594,41601600116015,4158,8773710,4982,0xc427a160259135609,8769611,11956317,4204,0xd8abed0902058860d,5399,27032565366,10170446,4180,0xdf55f1620d985d376,
4189,13214696,4148,13296241,63384544163119,26249258068,4180,4204,25398117352,5423,0x9f5b017d6573d344d,4204,29061251680,21385675970,23558780430,
4180,11489388,4172,4179,11509860,4205,4184,0x1bf9618635f9609,0x1bf962221939217,11509854,42160151328381,0x1bf831afcbc4234,8722045,0x875aff0bc2a05667a,4193,
10616926,4202,4192,19389449850,5096,12407784,4195,4193,11765366,57473579046413,13295694,0x18732ca5736709b,0xc2bbeaf561c9391e8,4202,4193,
4190,12408445,38152162219204,11509854,4163,8753716,4660,55809368864381,0xabf36726828cae518,4179,11510960,89916687276917300,4186,4193,10616926,
4202,12869728,4157,4187,4207] (by decide +kernel)

private theorem part81 : Refutes moves 0x24000000100000000000000000000 0x1c0924924004900004824000000100 :=
  branch 1 0x24000000100000000000000000000 0x1c0924924004900004824000000100 81 0x1c0936b2c48cb000168b4000000f00 (by decide +kernel) part82 part83

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part85 : Refutes moves 0x4000000900000000000000000000 0x160b24924020900104104000024900 :=
  finish #[
14189435,55375226184680,0x19556217436737b,0xcad5f57f17bafd3e8,4174,4181,4187,0x16cebda209b367a,23365378612,8765659,4199,4190,4192,5641,29061706160,
4180,23379419700,4187,29027665095,10170588,4196,0x16b5620d985d60e,5314,27224990914,4180,8770735,10616932,4187,4172,4202,
49794480919389,47642325271041,0x4069b36cf7f16e5806ea,23318217781,0x275171b52b00d9ec412f60b,11911258,4153,4193,4180,0xd8d5c7621b385a533,90612806829696521,10617396,4192,4202,4187,
12850480,20832482813,4196,0x17537d6578804c2,18518128018,11829306,0x400825009602be3674c2,53900558226604,4160,8746053,4193,4183,10171586,0x1bead9d782f64a6,4174,
4208,4195,0x13b725efad80bf1119a4132456,93070143813256826,10616944,9281617,4211,4205,4207] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part86 : Refutes moves 0x4000000100000000000000000000 0x160924920800900004004000000100 :=
  finish #[
0x57e03d95cd9cc134a310,17960374803,4195,0x1cced9e50cae3eb,5410,5410,51738528294411,4163,10170447,0x16cf2bcc905d523,4198,4195,55554439066907,76674220763239946,12869734,
4137,23438136623,17928684084,4202,4182,4177,13296616,8757471,4198,13296013,8774632,13221996,4175,90092580423189798,98036756897261054,
0xbaf9292b82b059299,4189,14636008,90626035137336170,26334078586,4189,10170446,4180,4204,4184,0x187c41d00059676,36726175302523,4177,27223189110,23322112655,
10617832,11509836,4177,83096506298897057,44485075657927,4180,4190,4204,4769,27081995133,17973306344,4190,4189,10617396,11912147,
10171259,10618159,4182,4187,80544505367659714,53499793482951,4177,55770353902429,4190,4195,4189,9281624,4201,4207,11075693] (by decide +kernel)

private theorem part84 : Refutes moves 0x4000000100000000000000000000 0x160924920000900004004000000100 :=
  branch 1 0x4000000100000000000000000000 0x160924920000900004004000000100 83 0x160b24924020900104104000024900 (by decide +kernel) part85 part86

private theorem part80 : Refutes moves 0x4000000100000000000000000000 0x140924920000900004004000000100 :=
  branch 1 0x4000000100000000000000000000 0x140924920000900004004000000100 113 0x1c0924924004900004824000000100 (by decide +kernel) part81 part84

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part91 : Refutes moves 0x4320000000000020000000000000 0x1fac96b74fac8200000200a0800026 :=
  finish #[
30018287117,30018458668,0x1cce07e2084543b,4174,4168,0xc30b09104222fa67b,4163,59511665566914,4303,98873360461829518,4190,4187,4181] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part92 : Refutes moves 0x4120000000000020000000000000 0x178a04924924820000020020800024 :=
  finish #[
15099401,0x1a329c7331fe676,11837512,9695444,4181,30017806585,13296378,37390294348642,4172,4168,9708520,9729107,4192,4199,23374513782,
0xcae758b8ac44410ba,9728066,0x98eafd2bac41421c2,0x1bf4689e7bd81c8,4172,48209984831802,20690305555,8733777,4193,4199,59517378196567,4160,4174,4180,4181,
4195,5096,51291887137881,36411450037542,4174,4168,9728891,11813755,11407816,4187,4987,53895996272837,4172,4164,4168,
27155256187,40808586331534,4987,12850043,11382860,4132,4987,50154170512578,11522124,4180,4174,4181,4202,45964357247976,4983,
4302,8691913,4172,4178,4181,55806456562111,10101267,4175,59461795628115,0x17a4d30a22fa1aa,4198,4977,5209,17870857080,4184,
4190,23575445717,29061260482,17854079949,49684855903301,4174,4180,4202,5303,11019447,4195,49693312910425,4143,4171,4211,
4181,17879245248,0xa736ce452bf2fa1c8,5206,0x16a52b8cd147429,4196,26318632239,8737641,4184,0x17b00116728895c95620855174,0xb521d4be82a2fd673,4166,4174,4180,4187,
4195,30017560774,18343765075,0x17a422afd1476e8,4202,4192,5293,9150777,4187,4181,0x195cbea185fa3e8,0x19592bafd0b034d,11935829,4159,4987,
30019797539,4187,47754737852613,0x6171fe95d9994643644a,14188745,29058466680,4184,4180,4187,4181,59519055479644,22465446193,11968581,11911231,4153,
4169,4175,4193,4199,4183,4177] (by decide +kernel)

private theorem part90 : Refutes moves 0x4120000000000020000000000000 0x178804924924820000020020800024 :=
  branch 1 0x4120000000000020000000000000 0x178804924924820000020020800024 105 0x1fac96b74fac8200000200a0800026 (by decide +kernel) part91 part92

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part95 : Refutes moves 0x4020010000100020000000000000 0x16bf1c920978860541224904845020 :=
  finish #[
5424,17403774234,55795871524143,4183,4175,9151560,13735075,55409318397441,11497539,11493433,4181,37817073148969,29035013422,10569222,13297161,
4168,22440841714,4208,4198,4189,11494703,0x4bb0aca1adaa565886e7,51289923769742,4187,11473784,0x1b165a578d89592,59538297603593,4199,4211,0x43cd1db102e9702fc286,
4165,4189,4193,20692108130,97058688076837122,4181,22289786159,55770967147157,4165,10982132,4208,12849224,4132,4182,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part96 : Refutes moves 0x4020010000000020000000000000 0x16ab1c920938960440220100840020 :=
  finish #[
61474039546963,19911967938,51838035416585,4174,11956309,5423,14169153,12420045,4180,4288,30001694220,4208,0x1960d12f9282429,4177,4159,
11433263,55772272915650,11374655,4151,4165,5423,23593226771,0xa14bf49d9444223e8,0xb67bf49da161a21c8,4163,4211,10101954,5099,27232551901,4189,
4193,0x65700a688b49b12e03e8,0x56cb6a95cbd9b38454c2,4174,13296163,11403455,8654945,4163,4166,4169,4165,4175,4168,0xd117b12b16cd87609,29992731146,
24197645834,4159,19873944617,4202,5425,12419960,4189,48230976353583,4156,4180,4204,13305460,27235184941,13304008,0xd892da625b39f20c3,
4156,4170,4174,11936963,4183,11470346,23600124904,9134961,4177,4165,55774045734065,10101267,4183,4199,23321671176,
11912494,38389885981661,11956293,4180,55772057667082,4186,4193,4189,4175,10101038,11469102,12849209,17779921971,12850470,4950,
0x502ad516c63620af8448,4165,4175,4189,0xbabbf362220b4c52f,5641,29061248194,4208,4181,12850578,36430461412072,5314,38321160966576,4174,21643948892,
11912386,38389885981661,4165,11472969,4193,4189,4168,11956303,4156,13742188,4152,4140] (by decide +kernel)

private theorem part94 : Refutes moves 0x4020010000000020000000000000 0x16ab1c920938860440220100840020 :=
  branch 1 0x4020010000000020000000000000 0x16ab1c920938860440220100840020 68 0x16bf1c920978860541224904845020 (by decide +kernel) part95 part96

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part98 : Refutes moves 0x14020000000000020000000000000 0x1eb954b70d20822000220000800020 :=
  finish #[
0x1b10b810c2fa457,0x179a839a64410d6,94793817192891586,4175,4182,9123228,19751245321,4192,98212682699011593,4156,23592334187,0x16a8da978b6737b,0x1b10bf1b384e1b3,4181,4177,
4175,0x32bac1b67af814173afc20e,23589564732,4192,4975,0x195cbf1b3855674,18782892117,0x88db112b657050676,13194870,49696062993602,13295692,27229769937,4181,4193,0x6215f395c1417721e609,
4175,36563302097787,4174,4199,4195,4190,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part99 : Refutes moves 0x4020000000000020000000000000 0x178904930920820000020000800020 :=
  finish #[
0x2b4c77d0e8847f97d367368,0x194546e572e03dd,9695674,4181,4190,0xd1bbea7e57d58836b,14189544,12406983,8709206,4182,4177,4172,48282741995131,4201,5400,
27232470105,23424009165,4193,4172,0x257d775881d81428da1e213,4175,48228433273705,4174,4190,4195,22327399703,11510199,11502429,4189,4175,
4971,43986549932878,8736978,4183,4187,13297161,89146364793274509,9179229,18799629177,4170,4172,4180,11511305,61460523767305,4195,
14652830,59530851652688,23197581388,23597495379,4183,4182,61389816914123,11510307,4163,27212977346,17881477324,17881478009,0x1a3614c2aafc678,4158,4196,
4193,11972698,4168,4152,0x1759622572183c5,10585391,14189871,0xadb7aa1dcb09fe4c3,4153,0xdf5b132b97d4ac20e,4170,4177,4159,29061272555,38371601655067,
18733921147,4175,4170,8733560,4309,48228433273945,4205,4199,4189,4180,5532,0x195d46c2a2f6676,57640978960594,4177,4180,
59589824906219,10604757,4189,0x1b104d57bafd0cd,11972714,4160,4152,12813945,0x1b112b9a24ac12d,12400137,11935850,4175,0x195cd32582fa3b7,29084632013,4202,
23594562191,29054657515,4201,0xcae28f7d5672ea3dd,4147,4175,4189,12849597,41605260821572,0x17aa5b57d13c4af,4205,13743734,17896014706,4186,4182,
11972687,10170424,4196,4204,4192] (by decide +kernel)

private theorem part97 : Refutes moves 0x4020000000000020000000000000 0x168904930920820000020000800020 :=
  branch 1 0x4020000000000020000000000000 0x168904930920820000020000800020 112 0x1eb954b70d20822000220000800020 (by decide +kernel) part98 part99

private theorem part93 : Refutes moves 0x4020000000000020000000000000 0x168904920920820000020000800020 :=
  branch 1 0x4020000000000020000000000000 0x168904920920820000020000800020 88 0x16ab1c920938860440220100840020 (by decide +kernel) part94 part97

private theorem part89 : Refutes moves 0x4020000000000020000000000000 0x168804920920820000020000800020 :=
  branch 1 0x4020000000000020000000000000 0x168804920920820000020000800020 104 0x178804924924820000020020800024 (by decide +kernel) part90 part93

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part102 : Refutes moves 0x24000100000000020000000000000 0x1c1924824904824800920000004020 :=
  finish #[
21439132952,21437363480,23572300302,4172,4174,0x32b4b10b1591621e9afa52f,0x1770f297d0c44a2,4187,4193,59317710656006,55772952937288,8684519,4173,4175,5416,
38527353767215,55774093693446,4156,4165,29994152261,5189,25267704133,4171,11972677,4184,4160,20522067237,11510186,4177,55769194332796,
47422833750522,11511412,0x186a9defac430f6,20512813818,4186,11972686,4160,8773720,4190,4202,4192,59450487448403,0x87b7a77d6c42ea27c,0x17a77d5b585d1c2,11518048,
4196,25294783343,0x1bec17a211964c1,5087,13300711,4319,21436023652,4186,4168,46185747931997,4151,4175,4147,4195,18843935356,
25437332347,4968,11518263,10616911,4192,4172,5100,61402432651529,4172,27232466096,9666761,0x8885912b85e0c6515,4193,4183,4201,
55775713649276,48283662914840,4193,14635446,47428246090172,4190,89909162532333175,5206,0xa8e1daf541ccae44b,11972713,4208,10616904,4192,12869738,4157,
4177,4187,4207] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part104 : Refutes moves 0x24000000000100020000000000000 0x1c0934924904824900824004824000 :=
  finish #[
23576900910,27238966554,55415122404515,4184,0x1b12634280c4349,4187,4181,18708259670,0x2ed162c9795e11c284ae27c,4157,41742729712726,61479449813883,90014724725077505,4145,4147,
55766530942461,0xbb595ebe9772fc609,4165,4172,4193,4207,4319,97125591219967270,0x195c6382405e591,4198,48070064735426,4207,4187,0x4f8bb81862c02e85e09b,97121993117270228,
4187,27216229448,11973499,4308,8765658,4195,4189,4187,0x4b6df7beb105b59b337d,4204,4208,4184,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part106 : Refutes moves 0x24000000004000020000000000000 0x1c0964924900924800824924000000 :=
  finish #[
55460900717294,13296925,29092995711,4189,4195,90022205968220487,4187,25115857569,59585903853755,46138001368478,4189,24486728986,23592333476,4420,73309635574358340,
4195,4190,35790235395375,4177,4187,27229656263,22343709162,13312744,26358298112,4207,4189,24488128602,4208,4180,4204,
4196,43747254124995,0x1afed9e1e588273,4147,61370692830499,43786188518677,4172,14189761,59517361877881,4172,4303,17851761640,4195,4177,4187,
4183,5423,12850152,4172,43751753282863,4989,18841584616,4187,4183,4319,12850152,17935229567,10616929,4187,4202,
0x188d6202c9b3142,21460288815,48314357330141,11972708,4168,4184,4208,4192,27103921677,10428867,63384767448367,4177,49724510577739,97586651042063559,4207,
11956275,4196,41392625054434,4319,12850152,73976113525024048,10616929,4187,4202,8770863,12850152,4172,40654912750681,10171372,4196,
4208,4184,13742176,4140,4152] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part107 : Refutes moves 0x24000000000000020000000000000 0x1c0924924904920800820000000000 :=
  finish #[
27232544269,0x8ea95c4f86322027c,4187,61393756079381,8754045,4187,48283443893555,4769,4989,29972861800,4195,4189,4207,4315,5096,
0x16cf2c91005e340,4198,4202,97716359935718267,4319,8773844,0x85e1872c110446676,4177,4187,10170462,4184,4180,4204,4196,11510966,
5754,0x17aa924f6aea37b,4168,12777082,29972615703,29094814896,12841041,4130,4190,0x1949252234b2356,53985547342706,11956312,4172,4196,55841881695097,
8774850,12850152,26319897576,4175,10617053,4207,4187,4202,53989198910758,11957551,24488576194,4177,4172,98888640035423318,10171372,
4196,4208,4184,13742176,4152,4732,43901800314378,4172,55777736761980,8680751,0x195d7d97d58867b,8716493,4187,4183,4181,
4177,4290,11953347,23555597288,4190,10616931,23575573153,48250924479560,0xdfa04a88099c41609,8765658,4195,4187,5534,11502886,53900591444079,
4204,4196,4208,4192,14652719,0xdf50a16121aafa0cc,0x1bf311978b67136,4196,4172,24486716281,12850152,4202,13295940,55773164077945,4172,
5100,0x2bea5836b883269101b352f,4204,4208,4184,13742176,9601056,4173] (by decide +kernel)

private theorem part105 : Refutes moves 0x24000000000000020000000000000 0x1c0924924900920800820000000000 :=
  branch 1 0x24000000000000020000000000000 0x1c0924924900920800820000000000 74 0x1c0964924900924800824924000000 (by decide +kernel) part106 part107

private theorem part103 : Refutes moves 0x24000000000000020000000000000 0x1c0924924900820800820000000000 :=
  branch 1 0x24000000000000020000000000000 0x1c0924924900820800820000000000 68 0x1c0934924904824900824004824000 (by decide +kernel) part104 part105

private theorem part101 : Refutes moves 0x24000000000000020000000000000 0x1c0924824900820800820000000000 :=
  branch 1 0x24000000000000020000000000000 0x1c0924824900820800820000000000 92 0x1c1924824904824800920000004020 (by decide +kernel) part102 part103

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part110 : Refutes moves 0xc000000800000020000000000000 0x172a7ea285029281803a0000820000 :=
  finish #[
18288296698,12854455,4181,11510957,4170,50159952991749,24489481026,4181,4990,36343664849079,51991597708573,4180,4156,29976957226,51683232015336,
8745044,4184,4192,4187,0x6fc443b0ab6ac4afa08a,27013518411,4175,5427,4762,0x4019894cf0b1e012929a,4162,4165,11972910,4160,0x1af8b6939c41533,
26318648838,4160,27200283707,13313065,0xc22bf0eede6b6b4ac,4184,8773696,4190,4202,4192,13742974,14152574,25321633280,25321284899,4173,
13742137,11510426,4170,38167456490894,0x1786bea4e21452b,11956303,4172,4156,27081995347,24490808183,55462926337218,4199,13742186,17910055916,50227723317471,
4204,4184,4192,4188,4200] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part111 : Refutes moves 0x4000000800000020000000000000 0x168a24820100920100120000820000 :=
  finish #[
25271841834,0x6c0436a2346c61b675fd,4172,12812537,20731818768,4196,4309,13743734,72076158341395650,4160,4200,72527919196763205,4977,0x1af910978367601,4172,
4204,11493476,4195,4208,77513632732438852,11379132,0x188cdad7d2f01a7,4188,4208,59538107819751,59537425151267,46069315973665,4160,4168,4987,
10171372,13742188,10616924,4172,4177,4762,5096,47771959538643,4160,4188,0x1964d9db585e290,4192,11936635,0x177cd9d052190df,11911262,
4169,11813599,25134470085,0x16ceb86c6af6273,4188,4202,23599384073,91210987100091481,4200,12869728,4187,0x1bec991b53443ec,11814087,26156025031,4183,
0x1a36d91a24460d5,10171372,4196,4200,8749944,57422455722595,0x17636149036b456,12869704,24525255879,13742644,24520282676,4190,4196,4188,4200,
14193075,28961055724,12869711,12871178,0x188d61cd9b6b27f,13742192,10616924,4172,4202,9281627,4211,4199] (by decide +kernel)

private theorem part109 : Refutes moves 0x4000000800000020000000000000 0x160a24820100920100120000820000 :=
  branch 1 0x4000000800000020000000000000 0x160a24820100920100120000820000 111 0x172a7ea285029281803a0000820000 (by decide +kernel) part110 part111

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part112 : Refutes moves 0x4000000000000020000000000000 0x160824820900820000020000000000 :=
  finish #[
29071332634,30951335215,45675982001103,4187,0xcafb17434c711a5ff,13210460,9192957,10567771,4160,4165,4175,8774394,57669408847372,8774158,12849254,
4142,4192,19671671306,13222111,4175,8774725,55808302105576,4189,8774499,42032009954815,39840907265102,13312064,4186,4175,5314,
4315,27175162079,4202,5405,9098654,59581242020063,4192,11956330,4156,13742188,4152,4188,4164,27246531451,5532,
12850687,4162,0x19602ed0036b0ba,17901666368,4193,28147365058,11509983,11973273,42024535712635,4202,8753375,4188,4189,4198,13742971,
0x2bea8dc9569c1410ea2252f,4174,24523023096,10609310,10170461,4192,4180,4204,4184,10085462,30018920991,10608691,0x325e4ad85440daccd446439,10912287,52044220359329,
4177,21679748295,11518625,10608726,4190,4205,10912287,0x17a6be9dd36b2f4,0x1b12d9db5a2037b,12869708,4177,0x169d098d98594c7,4190,4188,4192,
4318,11870747,12869711,4769,8770209,12869726,86491746738853158,11944909,0x6be5f792a9917e05d3c5,13295715,4190,21748626404,10170424,4208,4188,
27232506749,0x184c850644463e8,4187,5319,48283616179485,12870635,4187,0x8c8beadae8da2236a,4195,4189,10548423,11969735,53693486449303,10608726,10170461,
4196,9281624,4205,4201,11075695] (by decide +kernel)

private theorem part108 : Refutes moves 0x4000000000000020000000000000 0x160824820100820000020000000000 :=
  branch 1 0x4000000000000020000000000000 0x160824820100820000020000000000 83 0x160a24820100920100120000820000 (by decide +kernel) part109 part112

private theorem part100 : Refutes moves 0x4000000000000020000000000000 0x140824820100820000020000000000 :=
  branch 1 0x4000000000000020000000000000 0x140824820100820000020000000000 113 0x1c0924824900820800820000000000 (by decide +kernel) part101 part108

private theorem part88 : Refutes moves 0x4000000000000020000000000000 0x140804820100820000020000000000 :=
  branch 1 0x4000000000000020000000000000 0x140804820100820000020000000000 101 0x168804920920820000020000800020 (by decide +kernel) part89 part100

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part116 : Refutes moves 0x4120000000004000000000000000 0x178804924924800024004100904004 :=
  finish #[
24247985895,26156021039,4181,26318632239,13309212,4160,59520205615749,29943849960,9729107,4192,4198,4199,18402017550,14188995,42373740331464,
4163,4172,61390034728110,61390031508456,4193,0x17ac9ad712f0609,4160,4174,4181,4195,18745951535,0x16d5286c44ae60c,0x192d2bac419a131,4171,4159,
38438679643195,24487612620,4171,0x194066ac41354ad,8733560,4184,4187,4180,12715189,38392620703947,19781621257,4190,4181,5085,55635618317615,
4159,27235222833,23191934255,0x16b92bac405534d,4189,27230754313,4202,4211,0x1b112b82404d60e,40802897036918,4202,4174,4181,4201,5314,
5423,4412,18751620290,4195,4181,4180,5423,0x16cf2ba2084410a,4171,22376878525,0xdfc26d2b85d8470d2,4180,4181,4175,0x16ce68afe588448,
55825509281992,17759961832,4183,4174,0x19595fa57441363,30037018118,11469232,4174,4180,47748172252439,53900561014943,13307943,30035677640,0x16cf2b8d11414c2,4183,
4189,4211,4202,59606904587554,25434551359,0x1882f2966afd13a,4202,4174,27230728506,61513864107085,8716367,11509847,4184,4198,4163,
4205,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part118 : Refutes moves 0x4020000000004100000000000000 0x168905124904900824100104804804 :=
  finish #[
0x1a2361e50bd86e7,42367590446370,51334019839279,4169,95024136074224721,55619493036455,0x479048b10bf56acac52f,11472933,4147,4161,4175,0x1a3a23532c9652f,40519982818171,14635087,90092621186113804,
21479744342,4135,0x1b19099785f542a,0x1afc1356aa00098,8713519,29972845655,4191,4201,4183,4187,55767475130807,4172,4180,4184,18363426313,
21429359127,4159,55766561281200,4180,5410,27120640256,27231617103,0x6575f594083c5cc2b526,23548102269,40549031748475,4199,4189,4180,4205,38388725441831,
14148123,5410,13296595,4135,4151,4159,59346604712933,5423,0x195d5fdaa3640c5,61389816139857,4147,4161,59514207314117,13243443,29977396507,
12264737,4183,4175,4187,55535392515159,57315418903841,4175,76457996885193251,4211,0x195c05a5058b4af,61388048872026,61386354836106,4191,11501649,29974651333,
55768575477373,4190,4195,4184,4189,4205,51274784118282,23498171481,4549,5423,10568793,4165,4190,4205,4189,
30032548953,30036125197,55775881917961,4165,4175,13295817,11441455,4202,4852,29061252399,17759925548,4198,55714895708916,4159,4175,
4165,11956302,4156,53406912947127,0xbbbb108397884e521,4175,48282610914018,4156,27254751502,4310,36651556570742,4137,14188583,0x40649b764d9d02a1e177,4175,
14663890,4177,9187648,4174,10170462,4184,4180,4196,4204] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part119 : Refutes moves 0x4020000000004000000000000000 0x168904124104800124000100804004 :=
  finish #[
5409,90260500127880470,14202376,0x32b970d8bbf96250a36a3e3,4177,4159,4183,23382156118,14619285,4160,4181,37410626945278,11440884,0x17569e49a944183,22440793714,
83575450378273530,4190,4181,4189,12849264,4192,0x82c2316203bdf50cf,47766406809206,23575544702,4159,14618729,98279011428606931,48279939310019,4189,4190,
23578235991,29973279908,4180,4418,29976081602,4168,61391014409410,4204,4208,4192,4184,14192840,13296616,4157,82844276940502537,
27205522953,0x195611db3a14609,4205,4175,4165,13296616,29061707055,29942048265,4174,4181,55827448099363,0x16a483ec414535c,52091959015026,5209,44331370685512,
9728087,4205,4189,12849264,4192,4202,14636008,29062002294,26207707975,4159,37236086108815,8704105,4181,0xd884e37d57ea1e52f,4190,
21680624709,0x1b10139b3c414ab,0x1bea13c288c313e,4190,4180,10170688,12850806,11956538,11972716,4168,4208,4192,4184,5314,48113712895279,
5414,11502895,4175,4643,19873940552,12849264,4202,4189,30010512122,5314,27231384208,39930443043704,11296880,4174,27231462481,
26317242800,4165,24515036004,4193,4169,11956303,4156,4204,29976065658,11510070,48279939326813,4189,4190,4950,8708531,
4177,97579362175373962,4156,0x55f3b294b1044885519c,11510032,36645862740604,26321309775,4156,9187648,4174,4190,5100,38363353797798,0x1bea865b5afa1bc,10170477,
4204,4208,4192,13742168,4140,4164] (by decide +kernel)

private theorem part117 : Refutes moves 0x4020000000004000000000000000 0x168904124104800024000100804004 :=
  branch 1 0x4020000000004000000000000000 0x168904124104800024000100804004 56 0x168905124904900824100104804804 (by decide +kernel) part118 part119

private theorem part115 : Refutes moves 0x4020000000004000000000000000 0x168804124104800024000100804004 :=
  branch 1 0x4020000000004000000000000000 0x168804124104800024000100804004 104 0x178804924924800024004100904004 (by decide +kernel) part116 part117

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part122 : Refutes moves 0x24001000000004000000000000000 0x1c39ec165586d00124000010404824 :=
  finish #[
27235669513,5750,10442249,4154,4174,0xd886b12b97c3673e9,4172,5096,0xd8895d29e593674bd,24486639218,4174,4168,4547,51318975693892,4189,
13296067,4157,5197,25393600009,14635099,12818038,8680424,59523859796172,4183,4172,4174,4181,35214344869063,55655652086983,12408007,
4148,4159,27229714034,0x16812bac45f5515,0x188cd605f050604,4187,4183,4181,17828913352,4163,4191,4184,4177,59513770063151,59495408890928,
4172,11445551,27232990274,4148,0xdf688d6225758c346,4305,89920334867236039,11956275,11509836,4191,0x6fe1fb09b10ef8df9677,0x1bf310db38b54b6,0x18562d62358852b,61505453138114,4163,
50149556778180,4179,4171,4172,4174,4177,43907395515236,61510135784960,46430092756493,30009618501,11957882,47411140915729,29062620136,4207,61393665478856,
26336186678,61390979401221,4181,4187,4179,11509854,4184,13742161,4128,4140] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part123 : Refutes moves 0x24000000000004000000000000000 0x1c0925124104900124000000004824 :=
  finish #[
55837170496377,11957551,5191,0x8057a0d9ec4282433,4183,28144148591,4187,0x848440179b3c4151b,4202,5314,5168,12850245,4142,57645776245954,4163,
4175,0xbcd0830defab670f6,4156,89070365601400330,18768884601,4180,61395552916297,59522034331972,4180,29976355888,14189980,4160,46186672588181,4181,4157,
17910060115,4191,4195,4190,0x8510af46c61a20601,4177,18783876722,59522032547015,0xca1b1146cd984e605,11928529,11862223,24431198415,12869707,4147,4157,
14663765,10617832,4172,4177,0x4eb80578ebe8f80750c2,89509712987632943,26321309787,53903318188346,13750444,29104996972,19900892686,4161,11502755,17726456030,10616931,
4187,57647599874159,4196,11972716,4168,4208,4184] (by decide +kernel)

private theorem part121 : Refutes moves 0x24000000000004000000000000000 0x1c0924124104900124000000004824 :=
  branch 1 0x24000000000004000000000000000 0x1c0924124104900124000000004824 96 0x1c39ec165586d00124000010404824 (by decide +kernel) part122 part123

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part125 : Refutes moves 0x4000800000004000000000000000 0x162924124904900024000020104004 :=
  finish #[
5415,13296827,25322636919,13309014,27231617115,4184,4189,0x1b1083db39b33df,4180,49757196907497,14636008,0x5634a16ce30efac2b4c5,21552115806,4204,23557440800,
24129987887,23439967862,4174,13218465,4187,10171018,4180,4184,24495056175,53691656384956,9281644,4211,4201,4207,27233006786,
11957551,0x6571336ce83d0f1b3136,4184,4180,4767,44491476079810,93644324609930870,4208,4192,24488568111,5314,11973172,4184,4192,29976080948,
4660,20831143106,4172,9281642,4211,4201,4207,0x1052135b3c2b16a83c6d21e527,53897620988904,11974258,0x16d63046d441271,4172,0x19631061ab6b28a,79746503372649113,4196,
4204,4208,13742176,4140,4152] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part127 : Refutes moves 0x4000000800004000000000000000 0x160b24924104800124120000024004 :=
  finish #[
21645661054,14619338,17529614949,25034064047,14192697,14619285,4160,4165,72597586396013258,21191664457,4131,14619285,4160,11956309,21687673832,
4184,4156,13743080,11494264,11956980,17972858940,4202,0x175c0a57d5f54c2,26316845279,11972716,4184,4192,50206889587685,51789304640475,4184,
12849374,42658398909966,4184,50159925073308,24491701442,0x1b169597b041b131068db6b3cb,4184,4208,45519503676828,10170692,8769620,10616926,4187,4202,26360129033,
26359186064,4165,29062620797,11973172,4184,4192,89579419506050678,18820109474,4172,53899609978486,4208,98876882397802770,11973499,10616944,9281617,
4211,4205,4207] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part128 : Refutes moves 0x4000000000004000000000000000 0x160824924904800024000000004004 :=
  finish #[
10020364,14619285,4160,22494319466,4192,4317,0x18692b82e4b25ff,12849231,47863908537647,55721417434397,5532,28979152178,27115032672,11956330,4180,
4204,4164,0x5dd2db49f1045d856106,46031119418998,13239490,78437022116939041,11509850,4177,4198,0xbc195c88a8dafa2f2,9155280,27233006753,4160,27229774828,4187,
0x16d6bea5705c142,4198,0x16d746c2f1b34c2,4204,4192,4200,4184,13309017,51479147372982,8757287,0x32ba5289117b7d4299b31a5,4184,5096,8750369,4190,
0x81e3bd46db385d6e7,14635648,4736,82461145763779187,4186,4190,43969662366700,4208,4184,10616936,4202,12862635,76245880370598533,4181,0x1bf8f609cafa3cf,
4163,8749812,61504672997586,10616899,4192,8754588,53985543323866,4177,59506681767538,23574987719,10608691,44530969293800,4192,4204,4200,
13296616,13296505,0x1882b8864220521,4187,4202,55641209865397,21746393417,4177,0x9d895d46e15afa3e3,29975552861,11510871,24521683025,4196,4200,9281624,
4201,4205,11075695] (by decide +kernel)

private theorem part126 : Refutes moves 0x4000000000004000000000000000 0x160824924104800024000000004004 :=
  branch 1 0x4000000000004000000000000000 0x160824924104800024000000004004 83 0x160b24924104800124120000024004 (by decide +kernel) part127 part128

private theorem part124 : Refutes moves 0x4000000000004000000000000000 0x160824124104800024000000004004 :=
  branch 1 0x4000000000004000000000000000 0x160824124104800024000000004004 95 0x162924124904900024000020104004 (by decide +kernel) part125 part126

private theorem part120 : Refutes moves 0x4000000000004000000000000000 0x140824124104800024000000004004 :=
  branch 1 0x4000000000004000000000000000 0x140824124104800024000000004004 113 0x1c0924124104900124000000004824 (by decide +kernel) part121 part124

private theorem part114 : Refutes moves 0x4000000000004000000000000000 0x140804124104800024000000004004 :=
  branch 1 0x4000000000004000000000000000 0x140804124104800024000000004004 101 0x168804124104800024000100804004 (by decide +kernel) part115 part120

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part132 : Refutes moves 0x4020014000000000100000000000 0x1e8f1cd6993c864564220154004005 :=
  finish #[
24487843450,11957662,0xb6a694ead6c945180,10100848,4199,13291955,12223003,23295447811,11494234,4208,4166,4159,19926513161,59523905758184,4151,
59345447081032,4169,23295866377,19874652919,19648160809,24461902682,4163,4169,0x16ce8156caf6223,4187,4208,13295679,4157,4168] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part133 : Refutes moves 0x4020010000000000100000000000 0x168a1c52493c844560200100004001 :=
  finish #[
0xd889334457acaf223,0x195cbc6c42f6450,4181,0x1b137f0d14ae0fe,74498446242956572,4165,4858,11522502,4187,10982264,23549416492,9729104,4205,4199,4189,
4208,59513796665623,12338471,13288517,9982055,4166,13297277,13296503,0x178cd6afe4ac4a1,10014823,13219337,9152006,11460695,4165,4193,
12849245,4142,4192,13296616,18745046653,0x19572b851d880fa,13217895,4165,5096,5423,0x18692965749b522,9072709,0xbd808e4c85698952f,4178,4168,
4174,24492147576,5096,0x1afe2b5b3af6290,11407438,4159,0xd88b09998a294725d,15099183,30922122543,4211,4183,29061239989,61515810640859,9056338,4166,
55449493209727,11957552,4156,55732094793228,11956424,0x56caf595cbd9b3ae167d,4166,4187,4159,4180,17779029276,22191899263,13247577,0xd0a94b62e572f6195,4159,
4166,0x4ed81895d090a3af6368,0x32bec2ae126a51456b67459,4156,4204,12849264,4132,4192,4202,0x195747620b67273,11432936,52102219096829,4181,78159463215400457,0x1bf12821703e67d,
4159,4160,17776145917,29096075465,13295703,5314,24491196870,26143360635,26311595641,4187,12850245,11957335,8654908,4169,4174,
4166,49793380651497,53373529498924,4163,0x1882b66f9145609,0x40058410d106fe34452f,11935777,0xcaeb10d11b103e260,4166,4169,0xc4195c68820afc5ff,4189,4200,4165,4175,
4168,0x1750d9c522ee58e,5096,74564372168721703,11518250,4189,12849224,4192,0x802b1147620b6742c,18585228593,25040286653,26088850191,53434883785013,4159,4165,
4175,0x6c40ad882851b3cae362,4157,9539656,9564210,4155,4161,4164] (by decide +kernel)

private theorem part131 : Refutes moves 0x4020010000000000100000000000 0x168a1c52093c844560200100004001 :=
  branch 1 0x4020010000000000100000000000 0x168a1c52093c844560200100004001 86 0x1e8f1cd6993c864564220154004005 (by decide +kernel) part132 part133

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part135 : Refutes moves 0x4120000000000000100000000000 0x178804134924904120000100104000 :=
  finish #[
22546436354,48331306320165,14188617,9130984,9147368,0xd7f134ee9e6147609,11495030,27255354344,43971146662981,4199,4196,4187,5096,11957002,9695671,
4181,37402043978728,4168,4178,5096,4394,9146672,4180,12849224,4142,4162,4202,4192,4172,14189000,
23490670772,14635086,21514638639,0x1beb6210244120e,4162,55774994134310,18584335986,5096,22627645046,14635860,29975602370,26317177271,4169,4199,4159,
4202,55774991339728,4410,50160831534152,9122096,4160,4162,4166,4168,4178,4174,4180,9539660,4146,12849450,
59366501151938,24492105932,8717288,4187,4181,4180,0x1b10eb24b5f560c,0x193562257135300,4180,85911252274337052,4187,41238584587559,11494242,4159,10102049,
14635653,21417436347,40757011289718,4166,4180,4159,4199,59592581977285,11522499,0x1b11281b384d4c2,4309,47508755907765,4178,4189,4183,
4181,0x1bf929529c410d6,9146678,11509838,4163,4177,4205,4198,12849900,29060145410,11968716,12849231,9154870,4166,4180,
5409,9146678,4174,4406,0xd885fb1065005352f,4192,4183,17834521464,17880585297,9659255,4178,11956538,29058830628,61389859873413,4138,
4160,4204,24448771116,0x1beaed09cc2a60d,0x16697d6c22fd439,4201,23306659333,59518373646778,4178,4183,11509845,4177,4205,4156,9564262,
4161,4191] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part136 : Refutes moves 0x4020000000000000100000000000 0x168904130924804120000100004000 :=
  finish #[
23497667778,25193124906,4169,0xd88a3af590c2fa275,25423283067,13219010,11517994,14635094,4156,18684998850,48276112683326,13295825,23416172954,23589548100,27230204430,
78429317871150383,21720342623,4195,4199,4190,4180,29036541565,92772330561073802,4190,11461473,24487629691,4181,4175,11519497,0xbafb10d9cff11f361,
51706107765051,10084433,4163,0x1b102cd702f728f,4201,0x6fab67b10ba09e2fd2f2,5423,4278,50159919539718,14635103,4198,0xae0278bd97ba1d67d,10608718,4189,4190,
4195,37413340549559,36623061480969,19590534778,26315853923,10170454,4535,0x176a1e4252fa19a,14635089,5750,40018324566328,4306,8712396,4175,4177,
4178,4186,0x49f5f595c4bc5c9b352e,11972716,4168,4192,4208] (by decide +kernel)

private theorem part134 : Refutes moves 0x4020000000000000100000000000 0x168804130924804120000100004000 :=
  branch 1 0x4020000000000000100000000000 0x168804130924804120000100004000 104 0x178804134924904120000100104000 (by decide +kernel) part135 part136

private theorem part130 : Refutes moves 0x4020000000000000100000000000 0x168804120924804120000100004000 :=
  branch 1 0x4020000000000000100000000000 0x168804120924804120000100004000 88 0x168a1c52093c844560200100004001 (by decide +kernel) part131 part134

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part139 : Refutes moves 0x24001000000000000100000000000 0x1c39e4161da2c04124004100000010 :=
  finish #[
43786188518227,14189544,29061707056,52003885090074,4625,29058843624,4151,4163,4177,4161,4157,0xd873eb5f5773676ea,0xd8a284659a736833f,4195,5641,
27134559307,11896329,24489918509,4165,5096,8705000,4184,5096,8712399,4184,4189,4183,4177,4187,14189616,
27235238339,27233433097,4159,14635089,74263285444846895,5427,19540198921,4165,11956335,4172,5750,14189645,53756474696309,4187,89699679492167177,
4162,4154,11956750,11957103,55515465438025,29972813321,4184,29096600519,0x40a43958b11abfbc3276,17758974040,4171,4177,4168,4172,4174,
36259517825622,4961,29103097134,0x1b1163538df5349,4184,11956309,4156,0xd8db1327c9c846342,23130379568,5754,36184961771130,4168,27104405001,4189,4157,
24492147096,0x16cf7f257996609,4163,0x1b10d9c5919667d,51626094912814,4189,4181,4171,5640,0x195ad9c235880b3,23578234931,4184,4156,4177,27042714928,
14198063,4201,11490145,4172,61321367814783,5642,30033307145,25143731504,4189,4207,21462541946,0x9fe58b99af8caf349,4145,29058430589,4181,
10014795,4154,8704200,5422,13300697,5750,8716495,4187,4183,11509845,4156,4184,4177,24366318103,11957103,
4172,5096,17779028809,36411450889033,4154,4174,8704200,14189544,14189529,14189544,59518181196776,4187,4183,11509845,4156,
4184,9601105,4164,4182,4191,4170] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part140 : Refutes moves 0x24000000000000000100000000000 0x1c0925120920804124004100000000 :=
  finish #[
9643311,82844600689992769,4163,0x1b141fec6b67340,14209223,27233433097,4157,0x1b1128452b67676,4164,17960394822,4193,22466745979,39316719884010,24431522422,4165,
4187,5423,40228134822111,4170,9187423,0xba80bc2fdb3c4135a,0x1beb105b385d37d,4189,5096,48322589234698,48078412739190,4180,4186,51391284646518,55792173564745,
5424,26315862902,8769626,4195,4190,10616927,4187,4172,4182,4540,23358764097,13201852,47837936518448,4157,4163,
4171,50157896290604,0x5d958879311a514ae533,4157,10982705,9703959,4207,5641,0xd882db4342f1fe52f,8765512,4193,4198,4199,11961865,5096,
9606105,4168,4169,5191,0x1b10d62571383e8,4183,4207,55772091679720,43953413129064,4177,0x16cf2b97a85a459,4199,0x1bf87c8b4b67524,4989,24486715833,
4187,9601111,4161,4191,59503940105737,13734888,74435535759267562,4170,12849222,12850152,17943618175,4193,8773833,59514233820463,9601070,
4170,4191,10478786,98705298264802607,4189,26318164809,21462963048,4147,21461132482,10478440,13300584,4156,9601075,4161,0xcae5eabf22085c60e,
10616935,4187,4207,4202,4182,23577789529,0x178e88060c41609,10170454,43707145344062,61390083719607,4187,40270240371010,14635220,17926832553,4195,
36623096087419,4177,4187,4191,13297159,0xc2595f2b82313b147,4195,0x19647f97d3b59384f825a20530,10170454,11972716,4168,4184,4208] (by decide +kernel)

private theorem part138 : Refutes moves 0x24000000000000000100000000000 0x1c0924120920804124004100000000 :=
  branch 1 0x24000000000000000100000000000 0x1c0924120920804124004100000000 96 0x1c39e4161da2c04124004100000010 (by decide +kernel) part139 part140

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part141 : Refutes moves 0x4000000000000000100000000000 0x160824120920804120000100000000 :=
  finish #[
61395468649216,28978270847,4159,29061612847,27258127321,4171,0x195c651eb5f5609,61388831913481,74848150165091849,4202,4180,4174,4187,14148802,8668790,
10059846,12850806,27233445159,9647399,4184,4178,4187,0xd8695694e20b6752f,27229717480,9163752,4184,20608209997,10981686,11956290,11956430,
11497673,55646243467694,11493464,4166,4187,4202,4174,4180,4172,27108468233,38091163887104,26318647357,41395443626728,23542001864,17780356608,
27210056202,29027718001,4202,21518958662,4160,4170,47852354221032,0x1b1087827a22215,10170461,4184,4180,4200,98012877917943305,51324377555944,11461480,
4165,24130118165,38115033281832,4175,21514638750,17845703544,10604629,4195,4184,4174,89830541370545786,51906804204604,4159,21721691000,4200,
11519283,26318647971,4184,21512853110,21513287177,4160,5100,10171023,4180,10616936,4187,4172,4192,5645,0x1769611b43500bd,
4165,50160832996873,4175,81968733618917516,37236810216972,11518096,78452169059192911,4200,4174,14189767,10502900,4174,12849797,26315367045,10616907,
4172,14188868,0x5645885f887459c4160a,10522700,38512883053169,10617271,4187,10171372,4204,4208,4200,4192,5097,38251567218889,4177,
0x65311975cd9e57446198,53986398438361,10170461,4200,0xae175c4ed7b9b319a,25096573113,47852966089704,4168,55773198446906,4200,11961207,10616917,4172,9281642,4201,
4211,11075695] (by decide +kernel)

private theorem part137 : Refutes moves 0x4000000000000000100000000000 0x140824120920804120000100000000 :=
  branch 1 0x4000000000000000100000000000 0x140824120920804120000100000000 113 0x1c0924120920804124004100000000 (by decide +kernel) part138 part141

private theorem part129 : Refutes moves 0x4000000000000000000000000000 0x140804020100804020000000000000 :=
  branch 3028 0x4000000000000000100000000000 0x140804120920804120000100000000 101 0x168804120924804120000100004000 (by decide +kernel) part130 part137

private theorem part113 : Refutes moves 0x4000000000000000000000000000 0x140804020100800020000000000000 :=
  branch 1 0x4000000000000000000000000000 0x140804020100800020000000000000 62 0x140804124104800024000000004004 (by decide +kernel) part114 part129

private theorem part87 : Refutes moves 0x4000000000000000000000000000 0x140804020100800000000000000000 :=
  branch 1 0x4000000000000000000000000000 0x140804020100800000000000000000 53 0x140804820100820000020000000000 (by decide +kernel) part88 part113

private theorem part79 : Refutes moves 0x4000000000000000000000000000 0x140804020000800000000000000000 :=
  branch 1 0x4000000000000000000000000000 0x140804020000800000000000000000 80 0x140924920000900004004000000100 (by decide +kernel) part80 part87

private theorem part57 : Refutes moves 0x4000000000000000000000000000 0x140804000000800000000000000000 :=
  branch 1 0x4000000000000000000000000000 0x140804000000800000000000000000 89 0x140824000020900100000800000000 (by decide +kernel) part58 part79

private theorem part23 : Refutes moves 0x4000000000000000000000000000 0x140804000000000000000000000000 :=
  branch 1 0x4000000000000000000000000000 0x140804000000000000000000000000 71 0x140824000800000800000100100000 (by decide +kernel) part24 part57

private theorem part3 : Refutes moves 0x4000000000000000000000000000 0x140004000000000000000000000000 :=
  branch 1 0x4000000000000000000000000000 0x140004000000000000000000000000 107 0x160104920000000000000000000000 (by decide +kernel) part4 part23

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part146 : Refutes moves 0x8104000000001000000000000000 0x17502351b58c504004001001410200 :=
  finish #[
4930,0xdfb2532c2c284f60b,4179,61495889588726,9622037,0x195d0a547c41531,11022422,4186,4172,59557361468815,0x56a669afb63a1744267d,4173,0x8459581256a58567c,74650330831467823,4187,
4169,0x195d2b0b409260c,0x80320e035a74a052f,12252095,97551514512049671,4177,24143672621,4172,4202,9515099,9647387,61489329284290,10612813,4191,4198,
44123409162552,11457730,4974,27025506515,0x614ca1520bb65584f19a,4177,4187,4186,4304,22576427444,11485290,11514746,4162,4169,4199,
4185,4211] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part148 : Refutes moves 0x8114000000000000000000000000 0x1f506b57a19d155000000000000000 :=
  finish #[
5314,29975184578,18811721216,18827158373,4205,4177,4191,0x14dad22f92fa84910901a90355,37963128115985,9139478,14188622,5314,9605998,4174,18793603950,
4191,4177,0xd8a5201497cafb67d,4169,4199,4178] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part150 : Refutes moves 0x8104000010000000000000000000 0x17527255e10c145051030081040000 :=
  finish #[
20197627516,4987,41364742628988,4165,4138,5639,0xdfb6737d4292fa49e,11006047,4180,0x175ebb6585865ff,5206,59555364505100,4160,29079393586,55768248742632,
4192,4174,4168,81999750745772238,0x563c9bb1413c8d4b1357,4138,42205625116172,14148667,27116000304,4166,59551516942873,4161,4159,4157,4949,
29045675313,27232424895,0x194b2b9e9cac1aa,4177,4168,9515078,29975115036,59625936970484,0xd8b95d0d25057d300,55624033120546,4177,11419711,11505709,4185,4192,
4169,4987,0x1bea9fd7257d52f,11511307,4177,8725358,11514067,4169,4178,4192,10613403,4203,4191,4211] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part151 : Refutes moves 0x8104000000000000000000000000 0x17503251a11c105000000000000000 :=
  finish #[
18824589507,46459291070874,12849202,5426,0xcb1883282facae3ba,0x1beb2c6c52fa52f,10592337,4191,4198,0xd7dbf99a5d8a06531,0xdfcccd1065826b145,4142,59517352609047,22378218690,11896554,
11075909,4185,22687260997,4151,4201,4161,4173,9082377,52060509680263,9646176,4169,53277354516910,61393658160322,26183967902,4974,
26017981294,4146,11514747,10612809,4201,4211,4191,61395552519098,11075994,4179,19758241404,12825758,4186,4211,11510190,
4163,78022226626417852,4154,4148,4198,4178,22091666953,59523920888528,4191,37512792019729,4743,5630,5089,8655495,4169,
4165,13295687,4146,4157,10511329,48063975502609,4185,12849799,50030258611946,4168,0x6c42edb04be4290b5355,8716496,4177,4185,4182,
4178,74400027691754895,27210064283,27210011035,0x1b172c5dd0363ba,4157,4161,12849215,48185150280862,59362418578738,55829198058799,4173,0xc26b197d6c2b405ff,59466714142442,74857749079602482,
4169,12849243,4192,0xd8b51f2bb34c31676,14189328,4173,29973754741,29978284748,29976482746,12783707,95129568968741300,4173,4177,4169,9138480,
4162,4166,4168,4178,26318185402,4307,17812136814,4177,4178,23572316940,53280239330498,0xc1d516f48ca2904c2,11509843,12849638,23256343313,
21695164525,4211,4201,4203,4191,11956326,4180] (by decide +kernel)

private theorem part149 : Refutes moves 0x8104000000000000000000000000 0x17503251a10c105000000000000000 :=
  branch 1 0x8104000000000000000000000000 0x17503251a10c105000000000000000 76 0x17527255e10c145051030081040000 (by decide +kernel) part150 part151

private theorem part147 : Refutes moves 0x8104000000000000000000000000 0x17502251a10c105000000000000000 :=
  branch 1 0x8104000000000000000000000000 0x17502251a10c105000000000000000 100 0x1f506b57a19d155000000000000000 (by decide +kernel) part148 part149

private theorem part145 : Refutes moves 0x8104000000000000000000000000 0x17502251a10c104000000000000000 :=
  branch 1 0x8104000000000000000000000000 0x17502251a10c104000000000000000 60 0x17502351b58c504004001001410200 (by decide +kernel) part146 part147

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part155 : Refutes moves 0x18004000000001100000000000000 0x1677e39570b8554415400001504303 :=
  finish #[
4287,17736431220,14628130,0x194ceb6c420a678,4185,4155,24106271371,24230155895,5050,0xd1ab10ce612442591,4203,12406851,4157,4211,4195,
10527584,0x1afaea6535fc1ab,0xdf65b0eb48c11e4b9,4157,4163,4178,12281355,59461068616996,4168,5647,78193981288358617,4161,4141,14197044,18687231265,
14664993,0x176cd82575f7602,0x1b156388c12a678,4178,4157,13217865,4165,4187,21564523335,29058409643,0xc349371117220a347,4155,4169,28060644988,4178,
9536021,12280918,29059286321,4163,4211,0x195d7dde55fc60b,18686305803,13258832,9191635,4189,11075671,4203,4185,4179] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part156 : Refutes moves 0x18004000000001000000000000000 0x1277e3057098504114000001400301 :=
  finish #[
14664987,0x192af12c44ab67d,5641,35952166659700,4190,4140,4160,17869874127,55448384562589,4169,14190196,0xa59b0e82ac404e59c,4176,61353694396829,4191,
4173,4179,9536021,38556010210936,44164142380337,44154766295573,4191,4173,4179,5642,0x195c4aac3aed60f,4143,47696825583116,4960,21479756609,
19609083973,4190,36481078743897,4177,4195,4211,4157,9606667,4881,55554416592382,0x1b037f25720a4c5,4190,4165,4155,10528372,
55624093697543,4173,59482214949857,23290795092,4177,4157,4211,14188971,30024045874,11514283,13295731,4157,14160706,27235697641,23332746546,
4143,4211,0x9f47af629eaa905fe,13742169,95160997719535822,4174,4188,4176,43262012277927,8545908,45951827345935,4173,29060276855,4150,4160,
35952159593777,13751928,61510856299360,9609331,13295698,4157,9609642,59460140835225,61489257415983,23292577288,0x6fe3af4b3622572fb60a,4190,4185,19679948994,4165,
4167,4173,0x169d2ba4db39365,55774966617610,13742143,17535571238,49371530142194,55768954148361,73549522939933999,59624199152599,4187,4203,4211,13742163,14189143,
24105326089,17730482283,0xd8986d7f25704160f,39806306186761,4143,4179,4161,4173,0x1bef46c598b70cc,4178,4188,12849232,4142,4162] (by decide +kernel)

private theorem part154 : Refutes moves 0x18004000000001000000000000000 0x1277e3057098504014000001400301 :=
  branch 1 0x18004000000001000000000000000 0x1277e3057098504014000001400301 56 0x1677e39570b8554415400001504303 (by decide +kernel) part155 part156

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part158 : Refutes moves 0x18004800000000000000000000000 0x1277e015b0d8605920000000000000 :=
  finish #[
4629,27234247981,4159,5641,23510688705,4162,26261242725,4159,14636088,39552443515961,4160,13297161,9606665,11960383,4189,
4187,4211,5055,0xcaebead3abf3c151c,4157,0x1a23622bf1f43df,29058438210,8695881,4173,10528374,24495956935,0x1b117d6f984f1ab,4177,4187,13296043,
8488349,9610305,4193,55525949879810,4173,59329054782758,12400137,4157,9605328,4189,4159,4177,13296267,5050,0x8ec6d0d39e6a0a52f,
4160,27061863130,0x19344a9051292da,4195,4159,29976957009,4142,4162,4192,4182,13743298,61385078846658,23564817122,9122092,4170,
4178,4168,61389578409592,53436711409155,27230643009,4160,19680892101,4159,4195,0x18884a6c3441441,4132,43491162514629,8713848,13742161,36482002826761,
13743298,28966139294,17742213524,57639929868371,4168,4170,4162,11956304,4196,4164] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part160 : Refutes moves 0x18004000200000000000000000000 0x1a77e18f301a81500c260010000800 :=
  finish #[
14635659,13743080,4164,0x195746c292fb4b8,0xc996ce828953c9433,4196,4178,11957769,61392812699960,17870861178,4183,53903220208616,40315854492723,0xcb1790eb4fe36737c,4188,
13255083,51601023677742,12394564,4174,4183,4196,4178,0x1b104628dc41120,27150447243,0xd88beb2917cafb59c,4183,4190,29973717643,5750,29974991499,
13309558,4176,12849221,4132,0x6533ad25546e57d88360,4134,0x1beabd16c4221e2,98677367458587694,4174,4183,0x20225217b2556216c5f517d,18669113771,11956290,4148,11075684,
4203,4173] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part161 : Refutes moves 0x18004000000000000000000000000 0x1277e0853218005000000000000000 :=
  finish #[
14643914,0x195c46afba90357,4173,0x179525d6b4ae678,0x1933622574ad52c,4147,4136,0x657588b14966f9c97532,72887065357353690,0xc977752ba4a8505fe,4187,11956313,4188,0x195d7f2506684b9,12244491,
14643938,11956296,4164,14189436,14643938,14189498,4953,0x32892c348b10ecafbbcd6e9,4165,4183,11956339,4196,51518104917295,0x16cf2b8270c42dc,11075671,
4179,4185,14664993,19676194098,4157,0x1cd325f344ae17c,30036067631,4165,5757,25187509880,24491700285,4164,4188,42136920195499,59519928108116,
23349064663,4188,27240498697,12296263,4211,42135091480183,19673974063,46456861671628,4211,4159,4301,9191635,4195,4187,4183,
12849241,4152,4192,21562291394,21564523127,0x64b5f5b10829b3c4152e,4162,13239926,4176,13743034,25412662322,4148,21562291830,0x19337d4cc2df44d,11486055,
4183,4178,4192,4157,4211,0x1b112befa998677,29976065547,4300,61426021413749,4164,9175122,4175,29959288002,0x2931eb588beb1042904c677,4178,
5314,5163,43923645596966,4166,55434153350665,4182,0x17a6b7d76b67277,4164,4188,53901406270987,13214806,10526772,24486679842,22217426199,10847409,
98904519693636911,4182,11894864,9191539,4183,4189,11075683,4203,11509843,4170] (by decide +kernel)

private theorem part159 : Refutes moves 0x18004000000000000000000000000 0x1277e0853018005000000000000000 :=
  branch 1 0x18004000000000000000000000000 0x1277e0853018005000000000000000 81 0x1a77e18f301a81500c260010000800 (by decide +kernel) part160 part161

private theorem part157 : Refutes moves 0x18004000000000000000000000000 0x1277e0053018005000000000000000 :=
  branch 1 0x18004000000000000000000000000 0x1277e0053018005000000000000000 95 0x1277e015b0d8605920000000000000 (by decide +kernel) part158 part159

private theorem part153 : Refutes moves 0x18004000000000000000000000000 0x1277e0053018004000000000000000 :=
  branch 1 0x18004000000000000000000000000 0x1277e0053018004000000000000000 60 0x1277e3057098504014000001400301 (by decide +kernel) part154 part157

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part164 : Refutes moves 0x8014000100000000000000000000 0x195d69072088555003108014000100 :=
  finish #[
0x969252410f158860a,14188853,29062570959,4209,4179,53776351790017,5643,13296002,10444872,4180,11961289,5641,0xad8888296c41f64c2,4150,4170,
29986685409,24364949993,17641472093,4153,4163,4157,51543782490983,0xbc3845611e0d8852d,10933314,4174,4168,0xc41bea7c612442605,4163,47933431547183,4179,
51350696777227,0x21ee118f2af8eb6c55f559a,4142,0x8ec881622faa080a3,4163,82122446720685349,12849902,12853859,10444857,4150,61393623540006,55568837936758,21395808649,30951822857,4470,
10446018,4155,10518582,4148,44127857418433,4161,4153,4163,0x620c2c8847da56caf676,4136,4134,4180,29979206503,25090339883,25096135723,
4136,0x1bea14a574ad2ee,4180,4189,76176284715324583,0x98ebecebc012e64a1,4157,10528046,4180,11075643,4179,29969908930,29063041895,4178,5632,
14189175,25260642935,4174,14172244,25335268192,4157,4165,14172370,27230225255,4193,45501289693835,49896509718847,29025388043,4201,11075681,
4209,4179,0x5e63b885928afe442367,47703199548719,26320863442,9191743,4193,11075677,11509843,4163,4177,4205,4191] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part165 : Refutes moves 0x8014000000000000000000000000 0x195169072188154000000000000000 :=
  finish #[
9139945,29030831731,11829308,0xad4bea822124422ee,11075671,0x16916317d4a652d,0x405d7f6915f6faca6525,17277019429,24229422717,4177,11075651,14188615,5865,14152988,14189761,
0xad4a3910ac42fa58f,4170,4205,9605187,14189435,9192415,4189,9183551,12280133,11960645,4163,11075693,4209,4179,14189329,
98437010786157435,9175918,4187,4177,0xaf216e14ac42fb525,4169,4178,4183,4199,0x16c0a408f588522,5404,8725804,13742175,98362785958703995,4169,
4183,13743734,28146898443,23569847589,0x192a3102951b458,4188,4191,8726247,8713517,48063061143633,4157,12849246,11972714,4152] (by decide +kernel)

private theorem part163 : Refutes moves 0x8014000000000000000000000000 0x195169072088154000000000000000 :=
  branch 1 0x8014000000000000000000000000 0x195169072088154000000000000000 80 0x195d69072088555003108014000100 (by decide +kernel) part164 part165

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part167 : Refutes moves 0x8005000000000000000000000000 0x195532416208805500000000000000 :=
  finish #[
14143696,9965776,4138,13747151,4139,14202159,5644,0x1a36f32c5838219,4161,4159,4157,37199324778821,10511878,8717724,5643,
12334492,4159,4175,19256723069,25096115837,28145881149,4151,4141,4176,0xd1b77e80460290444,4173,4191,22377772664,20411622812,21562295708,
4203,0xa0abee5b4211333e9,4169,0xd7d798d5ac336067d,44085969892656,4169,41810503947568,0x1bf8f445d0c00d1,11075671,4185,11956319,4180,4172,28987560896,29978259836,
0x1b0aeea1543e591,4185,4189,61395553015527,28155740562,8679517,4173,24147322377,14190198,40038101529668,21587461533,11956291,4164,9633872,4166,
5532,10621928,4186,43418060522798,59513619222728,11075664,4179,10847208,29985788298,43512236037863,0x1beb7d8f2367267,4164,9596976,13254717,14635432,
23258575152,10612804,4176,50152444854474,11509837,4163,9277535,4198] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part169 : Refutes moves 0x8004100000000000000000000000 0x13517181640a00c104100000000000 :=
  finish #[
4953,27232108962,4179,0x1b115fde92e6674,0x1be6b7e57290609,4179,29961520431,14189408,0xae6792d82c4366674,4165,22685917299,4163,4177,30033208623,0x575b4e58f0a97d8c4602,
14626905,0x195c11efb849348,4173,23524778728,11972668,4176,11076801,13296401,55768180224785,4175,12849213,27232109762,53897681942134,4183,11973826,
4160,9277520,4202] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part170 : Refutes moves 0x8004000000000000000000000000 0x115131112008004000000000000000 :=
  finish #[
17200616295,4967,21712406025,4179,4173,12396266,98190609311524352,59521119093834,4209,11509843,4177,14644527,25411781141,0x1b0d2c0625f34c5,18825295369,
4211,4199,4175,37341907824825,9916910,4150,61423229341984,4182,9277486,4202,55339593163635,0xe6808849257181531,14665450,55349215339481,21653200965,
4211,9277547,9278770,19736253306,9278225,10490177,14189436,18792153957,4165,9277513,14635354,4442,0x188a366faa2149e,4183,4178,
23582561910,4161,4203,4201,4186,4211,59575402652531,93423879759869558,19003318369,4163,4156,18434233068,12849666,30024405490,13305026,
61494695961429,4136,59520047129569,4173,4201,5314,51686184825722,4185,4169,13742195,4164,25311553033,11458166,4987,0x179d46d76a1f37c,
4183,4203,4211,0x9617ae4c220d1b49e,95147711795565435,11457376,4157,9277529,4202,4198,5638,5399,28148244960,4183,4173,
27029353423,13295689,81947782693721612,9900526,59570555380822,4157,13742195,4526,18827916925,4191,10511416,10512103,0x192cbb5483bc52f,4209,4173,
30033904943,0x1bef46e203cc67c,12304429,0x908a377dde6133531,4199,4175,12849267,4172,4182,0x6572fa0890c68d8d9375,11972710,4168,4152,10170448] (by decide +kernel)

private theorem part168 : Refutes moves 0x8004000000000000000000000000 0x115131012008004000000000000000 :=
  branch 1 0x8004000000000000000000000000 0x115131012008004000000000000000 92 0x13517181640a00c104100000000000 (by decide +kernel) part169 part170

private theorem part166 : Refutes moves 0x8004000000000000000000000000 0x115130012008004000000000000000 :=
  branch 1 0x8004000000000000000000000000 0x115130012008004000000000000000 96 0x195532416208805500000000000000 (by decide +kernel) part167 part168

private theorem part162 : Refutes moves 0x8004000000000000000000000000 0x115120012008004000000000000000 :=
  branch 1 0x8004000000000000000000000000 0x115120012008004000000000000000 100 0x195169072088154000000000000000 (by decide +kernel) part163 part166

private theorem part152 : Refutes moves 0x8004000000000000000000000000 0x105120012008004000000000000000 :=
  branch 1 0x8004000000000000000000000000 0x105120012008004000000000000000 112 0x1277e0053018004000000000000000 (by decide +kernel) part153 part162

private theorem part144 : Refutes moves 0x8004000000000000000000000000 0x105020012008004000000000000000 :=
  branch 1 0x8004000000000000000000000000 0x105020012008004000000000000000 104 0x17502251a10c104000000000000000 (by decide +kernel) part145 part152

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part174 : Refutes moves 0x2104000000800000000000000000 0x17c82a94b106104200904a00084100 :=
  finish #[
0x1b112c51044152f,10617140,18683540674,4163,4178,92733115593119350,28031145470,27249690111,4137,43543822083372,4179,4185,9184774,24328168734,4171,
89829037381752326,4204,4168,39606751364731,29064384835,0x194a0aa1e92626d,4174,29079352382,4136,4156,43861834626356,4163,5641,53309168668925,49833526136984,
4163,11055141,11072260,4166,11956992,4156,10616940,4172,4513,9598473,9168393,4185,38130386777718,4198,4190,
0x480dfa51707ddd20360c,0x193562250927444,11956294,4148,78440929725383769,4182,4408,0x18812b9102066e8,10617330,38523656242371,0xd8895c1d455afb267,4157,10617142,4182,4178,
4185,30934553905,73417048984506968,4141,11879699,11514746,4171,11956313,4148,4204,14202374,29978284355,14636329,0x88a1d9632faace185616c5bd50a9,4168,
4141,11956266,26317267430,4171,0x183e149aa4ae0cf,92731409088016595,21737115756,4178,4198,4201,4211,4196] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part176 : Refutes moves 0x2904000000000000000000000000 0x1fd228bef906904000000000000000 :=
  finish #[
47632651293996,0xaf43b87bdabc3d1ec,8724540,17403774470,0x47581095cd2ac45850d3,17652606239,4155,4152,9860266,25095254227,14188632,59517145113074,9437234,4145,0x61bcaeb0a14975b67609,
4172,14636212,0x6c411c5ad25655cae4bc,4146,0x1b164213cbb4111,0x1694628292fb270,4178,4192,12849343,12850152,0x17a0a0d7d8b5676,4166,12382290,4172,4171,
4162,4305,8720591,4965,26360529217,4193,47635392623234,4174,0x443d0d8530cc9a851429,10616914,4202,4192,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part177 : Refutes moves 0x2104000000000000000000000000 0x17c82894b106904000000000000000 :=
  finish #[
13296214,11838767,21118588207,23254417474,4184,41592886293664,4156,4635,20621423259,4193,4171,85649816358068845,0x1beaf1d45b6712c,4156,89404871175963943,
4182,38338324493157,45602657640657,19774174514,4211,4198,4201,5750,17683514344,0x17ab2b81e21f60b,4201,4166,89383274235773774,0xac16cf62a571353e5,4201,
5750,0xc1fbf614497af42fa,10616940,4182,13198315,27074937264,0x8181ea87e584290be,9598231,10616920,4172,4202,0x539afb2470c5b3a20676,10449893,0xc3d3eed09b522052f,4172,
98904310584206169,4211,4201,4156,4166,12869728,4157,4177,74362935453025474,28978283169,5641,26359673249,4192,11956296,4769,
53313701048511,0x280f34446b10118c9048447,4174,4168,4175,14624034,0x183a3ea509926e9,4393,10870956,11354157,12869689,4147,19647362246,4168,26358247623,
5423,9629895,9101390,10616899,4172,0xcaebeb11b341356e8,26317296102,4193,4295,0x122b9a16a3424409ac5ac41258,21695062102,4166,4211,4201,4196,
91222226350925105,0x19259a0c62d42d7,30938428245,44539401617480,4161,63365434020843,23256789995,4148,47631736141075,26315813281,10616904,4182,59512570545020,18683658889,4177,
5319,61392809993192,10621003,4196,4198,11075699,4185,4173] (by decide +kernel)

private theorem part175 : Refutes moves 0x2104000000000000000000000000 0x17c02894b106904000000000000000 :=
  branch 1 0x2104000000000000000000000000 0x17c02894b106904000000000000000 107 0x1fd228bef906904000000000000000 (by decide +kernel) part176 part177

private theorem part173 : Refutes moves 0x2104000000000000000000000000 0x17c02894b106104000000000000000 :=
  branch 1 0x2104000000000000000000000000 0x17c02894b106104000000000000000 71 0x17c82a94b106104200904a00084100 (by decide +kernel) part174 part175

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part179 : Refutes moves 0x3004000000000000000000000000 0x15c980f19403004000000000000000 :=
  finish #[
14635219,5423,0x1b0e0d1e344137d,4182,4172,13296470,47769921660207,4193,80486897545405281,4197,4177,29063046445,27230142651,11075653,4730,
19626755362,40236884120533,11075670,4179,24196302018,10600659,4186,14189213,14190198,51631920255649,9556054,4156,0xd883b52c223290678,4167,4197,
21502689491,0x1b10149042124c2,4201,4163,4211,4193,4173,38201815794968,28146824822,17853645906,11518029,4186,5400,0x1a3925ebfb6a21b,0x188c25c55d1b04f,
61393626387868,0x1beb28a56a9059c,10559589,4173,12783805,51306172383372,29976977484,97972080461145498,11518161,10612822,4181,27231929865,17761785123,4175,12870497,
21670006825,4173,4186,4201,27146716677,55605970510811,4123,15107584,30940767197,4167,4161,36254088132329,4172,0x1b172b822af52a1,4881,
13288071,0x195cbc65604b287,8720460,4181,4185,4179,0x83a0a52bac40b72a1,59520090854453,93081144413807244,4174,0x19337d618c45282,4146,38208694453530,4185,26184844918,
26350687321,4148,4519,0x6c458a8532b822af5459,4172,36530754749291,4185,4179,8725265,55777736684305,4294,9594034,12869692,21670006875,4201,
4211,4193,4196,4198,0xd1d9267e5ec4411e6,0x1afcda9102123e5,13742195,8688920,27231650577,4197,13296401,27251106646,61422377931537,4172,4181,
46464418055367,27229754018,4181,4187,4186,11972691,4152,4192,4176] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part182 : Refutes moves 0x2034000000000000000000000000 0x1dd349a8d0a2f74000000000000000 :=
  finish #[
8533517,57651254900234,4163,23083308430,0x37d43a82b20cd2af935c58e,4209,55789114394230,4134,5864,17496518867,29070987302,4172,4202,5641,5404,
53905128579611,4155,4151,52098499826994,13284873,27258168837,4151,9150775,4179,4185,4177,4171,24398979721,0x16737d657587523,5423,
39422502195826,14184529,4745,59528931108120,4179,4178,11972698,4176,5305,38388971594927,26318647359,39351048921737,29061723066,4176,24104056206,
93922134288123183,8650812,4170,5415,27132789370,24523280451,9106626,9654346,4177,4174,4171,4168] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part183 : Refutes moves 0x2014000000000000000000000000 0x1dd16988d022154000000000000000 :=
  finish #[
28987122645,57650340647202,4171,93722193142776659,0x6bfbadb1146d723c82e8,11075643,4179,0x1a36baec420819f,25380893548,21500339721,11075672,4179,98588004757516607,4171,4178,
4881,51491026970010,12420619,4171,45864951252382,4168,0xdf540762029290367,4179,39261505085713,19377829274,19168113425,9463194,4130,4129,4134,
13296265,4168,21542695866,0x1bea821d5d8a3ba,4132,51803710928393,4154,4171,11506618,22393152442,4153,21504877632,0xbb4520efde42eb115,11391065,4148,
4155,4176,4199,10519746,11429157,26159637669,4172,4171,5314,13295827,4168,0x188280d733c652f,11075659,4179,5747,
20491215925,57644730089683,4185,12849235,4881,0x97795b2ba20d1b261,90370074246124958,28146840770,4185,4155,11972711,4168,4176,4152,53885957342606,
59480117372097,9654343,13743734,0x32c40ed885a8ce68ddf5311,61394524419474,8720590,4179,19775074514,4171,4178,4190,4185,5637,53990997702153,4193,
0x37d477d7f95c9b623135261,4189,22393206272,25396798066,30027310710,29095704188,22394101857,9654355,11972701,4176,10616904,4177,4202] (by decide +kernel)

private theorem part181 : Refutes moves 0x2014000000000000000000000000 0x1dd14988d022154000000000000000 :=
  branch 1 0x2014000000000000000000000000 0x1dd14988d022154000000000000000 101 0x1dd349a8d0a2f74000000000000000 (by decide +kernel) part182 part183

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part185 : Refutes moves 0x2004100000000000000000000000 0x13d51080d04a006104100000000000 :=
  finish #[
0xc933037ed4812c676,25395442992,11972723,5314,0x195e10093c41185,0x18821265736b291,4176,4168,51799826634025,11973826,4176,27233882536,11973826,10616912,4187,
4197,4172,10511884,26357305768,9031759,52013514249282,4168,4382,0x64c83c95c48050b6b4c7,4168,11973469,24522130626,4197,4172,9277536,
4210] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part186 : Refutes moves 0x2004000000000000000000000000 0x11d110909002004000000000000000 :=
  finish #[
55852430119333,11076258,5319,5192,53985564120696,26362807376,4173,8716367,4181,46460602082366,4151,4189,4203,25369375785,29977403759,
13309558,12267595,26194138091,4147,4167,91253646634854006,9277517,4202,9184313,19548947868,0x6c40c20f508a4ebd152f,55670799693076,4143,4173,4161,
52010681803864,55378000020537,78616774891422919,4147,4189,4167,27240035380,22685029680,9277517,4198,73084359889420442,92963849708799058,10896567,4201,4141,
26361864977,4167,55756829512573,0xa0692eb828daee1a8,0x192746ebeca80a1,0x1966eaa8dbcc19b,36525996482614,4185,4181,4175,0x1bea6068d8b50c2,0x6233d0beb6210fafc60d,4203,25362793885,0xbcf2297d4f24ad3eb,
4167,55410585948475,0x195162256a903db,0x4812902f249efabd8609,10559545,4163,4173,0x64ccb177a59457d1b265,0x177a59457d1b0ca,10560924,4163,10612813,9277520,4202,11956326,
4172,4164,55636676162203,0x1b100228d91c36f,52100328854383,0x45f5881226068da90608,4209,4197,0xcae6c4d717e29018d,23534409116,4178,4168,4173,0x65602a03e5ad338a116c,4730,
0x6c44ae942308fca9036b,10580051,4173,26270086302,11956304,4156,26358236131,12793244,20504446473,4185,53658236458396,4143,4173,12752284,13300916,
4156,0x5b144643eea16ea1742b,4203,4211,4769,27231650416,13296289,10560161,4193,4203,4173,5077,0x1b1746e20bd1599,10616915,29063493130,
0x1b12d9214a204c7,4177,41320716567964,10560706,4173,4203,11956339,4164,9277516,10170474,4192] (by decide +kernel)

private theorem part184 : Refutes moves 0x2004000000000000000000000000 0x11d110809002004000000000000000 :=
  branch 1 0x2004000000000000000000000000 0x11d110809002004000000000000000 92 0x13d51080d04a006104100000000000 (by decide +kernel) part185 part186

private theorem part180 : Refutes moves 0x2004000000000000000000000000 0x11d100809002004000000000000000 :=
  branch 1 0x2004000000000000000000000000 0x11d100809002004000000000000000 100 0x1dd14988d022154000000000000000 (by decide +kernel) part181 part184

private theorem part178 : Refutes moves 0x2004000000000000000000000000 0x11c100809002004000000000000000 :=
  branch 1 0x2004000000000000000000000000 0x11c100809002004000000000000000 108 0x15c980f19403004000000000000000 (by decide +kernel) part179 part180

private theorem part172 : Refutes moves 0x2004000000000000000000000000 0x11c000809002004000000000000000 :=
  branch 1 0x2004000000000000000000000000 0x11c000809002004000000000000000 104 0x17c02894b106104000000000000000 (by decide +kernel) part173 part178

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part190 : Refutes moves 0x30004004000000000000000000000 0x1cef88541974005834004004000000 :=
  finish #[
5423,0xc223cc9d2fa4ae589,0x188161c953d2361,4165,4151,29059757350,27235221703,55743374185671,4165,4167,14189844,59521163257461,20496490557,4163,4177,
23573242152,5641,29044392471,4162,10470708,11477490,4169,61395551892999,4294,55434137511427,4192,4189,29061260129,4191,4198,
4177,5643,11510870,4163,14188979,30950475042,11961645,4165,4181,11363957,4169,4183,0x185d7f16b588522,13305577,12363042,
4193,4531,0x1b116247dbca676,19290309043,11509845,4163,13295718,4168,4135,11956285,4196,4204] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part191 : Refutes moves 0x30004000000000000000000000000 0x1cef00145830004000000000000000 :=
  finish #[
10437463,11509966,11956305,14632459,61390985314717,26326073981,4151,13295683,0xbcc92f7d5b3d8a52f,26312950541,8712259,4177,13297269,5063,55417885410934,
12869727,11472977,4147,13297269,45810709153399,23533174865,4165,4189,5314,59511750791372,0x852bf92b85b932609,4168,4174,23575556287,36600432653160,
4975,23231129213,59517358646025,4183,12849243,11474223,23496827880,11518039,4168,4175,4193,4196,47595164042078,26058141898,14664998,
0xd11bf7296fe04b35e,11509835,4163,12849226,5314,0xc41bf92b8990b736c,4174,4168,59620357207327,47904786105152,12845083,14665005,0xc4257f629e1c41526,8696997,4178,
23298285643,11432017,4196,17713260040,5295,61412727251580,11956318,4204,27193279682,55772821923010,4178,22452371991,4191,4151,0x6bed8ecd37d57dc4143c,
59334884487337,49591072589546,36599444227593,89944196872299822,4164,4199,13295698,4168,0x1becd617c4ae609,98118365216753160,5081,61392813589797,11895783,4181,4147,
12849363,17872642941,4168,11956318,4156,4204,11929097,11920222,11956283,55378025194547,0xc97844149e6bd6340,4174,4178,26318164847,4175,
4151,4165,10616925,4187,4197,4192] (by decide +kernel)

private theorem part189 : Refutes moves 0x30004000000000000000000000000 0x1cef00141830004000000000000000 :=
  branch 1 0x30004000000000000000000000000 0x1cef00141830004000000000000000 86 0x1cef88541974005834004004000000 (by decide +kernel) part190 part191

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part193 : Refutes moves 0x20014000000000000000000000000 0x19ed49508a20154000000000000000 :=
  finish #[
5314,28165018047,10518714,40194678191298,4169,4163,4168,25334358436,46013180733051,18718568659,4176,25170286090,0x16d72b9e612c44b,9691208,4204,
4201,0x192f2bb345fc6ea,28983776559,4151,0x167363168dfc523,14660228,9135408,4189,4181,4171,14661129,10499593,4168,4631,11347580,
24106288764,0x1b197f1340ba3ba,4181,4169,4193,29092439454,4306,0xa4eb196202893e170,4204,4201,4180,4189,4186,11973826,4152,
28149581094,40658534716937,4187,27235221699,30036124292,4947,47600107799172,9138249,4172,11972690,11509832,4170,4163,4184,27156985353,
47789098369292,0xdfcb18936fdafa36c,12849219,0x7345fb5f7106fe13e676,4210,4189,4745,48285483164297,19647411394,4210,4189,44124301091920,4745,59516356583736,29060268344,
9592899,4745,48283574264656,19647410237,4204,4189,4186,44128871559615,4152,4176,4168,97852740768739972,14189767,11391423,4204,
90203875275821907,0x1cd265a2358867c,61511249216479,4181,11509835,11972675,4184,23573279943,49364162561769,43900835182205,4185,0x16737d68ddfb147,0x57d519b117eefa93e6ea,4186,4189,
18842945149,61392856003514,4987,44118584832862,4189,13295706,11972669,4168,10616912,4182,4187,4197] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part195 : Refutes moves 0x21004000000000000000000000000 0x1de9d2110c21004000000000000000 :=
  finish #[
89910339117167543,10617723,4177,4740,0xc45863428293582e6,17871307624,11972675,53986329962103,11510974,10616899,4177,36528968418166,4175,4189,4186,
13296620,55771973710486,4186,72152296822707944,29061260342,13295683,55772265538411,4175,53799344963882,14188852,50137212851725,4156,55777735868855,11972714,12869728,
4197,4187,27232436989,53974765757491,14188640,26360136445,4182,36393315689775,27235222726,36552548721644,23533630985,59328440697714,4202,4172,12869718,
10600539,4181,49489033064753,11490284,4186,0x1afa441b5d88534,11518733,4182,12870633,4157,21586059355,4163,4183,4201] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part197 : Refutes moves 0x20005000000000000000000000000 0x19f9525408a2005500000000000000 :=
  finish #[
51890515248431,13297052,55776823264777,12869702,4147,5097,27272610793,4199,0x16a111a4f280534,40053591180591,4166,50157217437084,4153,4148,4163,
26362360873,0x59c2c4b104c1b3caf60d,4180,59518376453280,4163,53368707383691,12350324,24488579139,0x734446a3728906a1c609,4168,4183,4191,29976064879,59549962241327,48285530149528,
5406,27274035621,4183,4181,4163,0xd0888cd5a49af1350,24346825927,4978,27235223038,22401581837,10620995,4181,4183,4178,4176,
0x37da235886cc8717aafc52f,4165,9277512,4210] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part198 : Refutes moves 0x20004000000000000000000000000 0x19f911100820004000000000000000 :=
  finish #[
20592366787,13297052,4157,0x1a2110afe4226ea,11428732,4157,0x97594abae560c652f,4195,4177,5537,44084898805141,4151,13297161,0x16ad63ac4669340,29111559914,
8548425,4140,53713449019005,4177,4197,53711523209751,57457460761903,21250900254,4195,12357713,4165,4147,24347312993,4743,30948664158,
14188617,4958,11019554,4201,41598617060551,4137,4177,11956327,26318631210,30950036304,0xc97844f5967c416ea,50039660405719,4186,4165,0x17acbd620b673df,
10616900,4197,4182,4172,10560162,23509341036,0xd882ca5d6fdc412a2,26321338999,11478215,21502152779,4168,4163,10617486,0x17b16211041f4c2,11956314,
4156,4172,48081157600414,51494362969609,4180,0x57dd88a377ed7736743e,23565833737,4201,4183,12751734,12866528,4156,26117305206,0xafc5d48725720d4aa,4201,
4183,9277512,4210,4198,12702129,11920250,10620995,0x1a370757d22037a,4177,47786386195644,11920004,4163,10617723,4177,0x187a82e57221676,
4201,0x97544146e18b6b1e2,4152,4168,61391915991897,14189079,0x734b46b116122320b3ec,11509845,4163,4946,61355364165238,11432003,23475312246,14664979,4163,
48081154450070,4171,29063046890,0xe6941b0c614a21609,4183,51376913601403,11972677,4168,4176,4193,0x196746db593c609,4288,59518409114585,4197,10618039,
9684162,4199,9684162,55859070878776,0x1858bf09e441534,11972694,11403336,4165,4193,9277516,4202,10170482,4184] (by decide +kernel)

private theorem part196 : Refutes moves 0x20004000000000000000000000000 0x19f910100820004000000000000000 :=
  branch 1 0x20004000000000000000000000000 0x19f910100820004000000000000000 96 0x19f9525408a2005500000000000000 (by decide +kernel) part197 part198

private theorem part194 : Refutes moves 0x20004000000000000000000000000 0x19e910100820004000000000000000 :=
  branch 1 0x20004000000000000000000000000 0x19e910100820004000000000000000 108 0x1de9d2110c21004000000000000000 (by decide +kernel) part195 part196

private theorem part192 : Refutes moves 0x20004000000000000000000000000 0x19e900100820004000000000000000 :=
  branch 1 0x20004000000000000000000000000 0x19e900100820004000000000000000 100 0x19ed49508a20154000000000000000 (by decide +kernel) part193 part194

private theorem part188 : Refutes moves 0x20004000000000000000000000000 0x18e900100820004000000000000000 :=
  branch 1 0x20004000000000000000000000000 0x18e900100820004000000000000000 112 0x1cef00141830004000000000000000 (by decide +kernel) part189 part192

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part201 : Refutes moves 0x80024000000000000000000000000 0x12f19980a280924000000000000000 :=
  finish #[
0x1b10b183b87b36f,13686397,30943458010,9610546,4169,23471662478,4179,4185,12849246,9630532,12301506,82726884067394629,4153,11415625,11518834,
4179,4168,11518603,0x1b102cf34441678,0x1b1199d71c411b0,5314,5426,25309672504,4174,11509824,4170,4198,11509970,0x1a36bbac45f5433,0x1beab1ac120a36f,
11509849,5423,14664643,0x1bef46d7d4ae4c2,11472990,11518010,4168,4193,11956307,4188,4156,53903285929263,10450557,27234247651,11415615,
4147,0x195c7dc50a0a606,12850152,5757,30031979585,4173,26315314152,4159,4163,4172,4165,25297928562,63378714030493,9511907,4169,
4151,11956738,9553196,11461608,4151,4179,4165,0x5ec1125dc471b3d1b67c,4140,23382619334,23499621352,4179,9277512,4198,21562307435,
0x16d76222092c534,53900590896436,4169,0x6c64b32d2dad7e0d960f,4210,40350161089730,14664675,9618626,9621579,4169,0x649bb522cbf1b58d967d,11509874,4170,4198,4284,
57645802378084,4193,12751358,51603026625696,23500075081,81221876968207222,53968171873354,11509840,9277500,10170470,4188,4184,4208] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part203 : Refutes moves 0x80004080000000000000000000000 0x12e3b12212800a4081020000000000 :=
  finish #[
53900557231407,19537355709,14181570,29079844137,4140,4162,4184,27180746251,27217527995,9593832,4168,23356956735,4165,29079786690,25437390121,
10485843,63333256664136,0xd7d96146e542dc4aa,11972652,4176,10170714,4204,4208,14188841,29059027944,4198,29061620808,30032107017,0x6c4508bf962d0536242e,11878463,
4169,4193,24394961429,11968858,4159,30020715717,0x1bf50e89636267d,4143,49824141210595,4153,55773802930522,11461259,4165,4210,0xbad2592b9e458819e,
25306317784,4442,30033355265,4170,4145,19003270665,4193,11075698,4173,4203,4179,0xb67bf90f9482fa4b5,4881,50154433340257,4165,
4193,5641,0x194a7dec2200196,0x1b099a2c4362364,4193,4169,0x1bf90f9752904b5,4179,4957,27232109762,11972679,4152,11416639,25437750109,4153,
55808398464412,0x1bf92b932b6b35d,4160,55771361313772,22685926244,4182,4186,11509843,4198,0xa0ab0b62e20b6b0b2,11510978,26318647725,4168,0x3608efbd895cda9b5afa678,23382180805,
9277547,4210,10170470,4204,4208,4184,4191] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part205 : Refutes moves 0x80404000000000000000000000000 0x17f1738c42c0404000000000000000 :=
  finish #[
25236821039,51499984250493,10528269,4150,4160,9630783,4171,5096,0x9e225821505367364,30028628968,14189523,0x560e68a15075b3d8c44a,4169,12869687,13743080,
12865580,4176,4178,4188,9208687,25269544348,27233444584,4156,40396225758511,4172,4168,4975,4425,84844495741051312,4168,
12869737,40399054943535,0xbb6bf84be232fc603,11075660,4173,4167,4179,0xdfc2d32a133afa602,11509965,4987,30034317732,30036124534,27230664317,4183,4201,
11518843,4161,4179,4203,4189,0xa905eabf17d36b4ab,4160,29063893860,59518352172660,4169,96951751763010523,4163,0x195d11ac42fa674,29958841105,9208701,
11460695,4165,4179,26019321244,27258504279,11509843,11510954,61517700072403,4203,0x2eb6fe6684a70a61edf752f,0x1bf96297d2fc34c,0xa9088d2557d4b160b,4143,4171,11972677,
4168,10170448,4188,4184] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part207 : Refutes moves 0x80004004000000000000000000000 0x12e431191284004284004004000000 :=
  finish #[
4523,0x1b10800ca12651e,4165,26208109871,77883496366511625,11972675,4208,8566281,35274353205381,11972636,12411303,4156,59520014917766,59520012695163,25418301544,
4185,5635,0x16852bac43d658b,12869692,14189767,59520247571634,11972681,11076807,4203,4185,4167,29089579510,30031467459,4167,0x16857f17036b6e9,
4200,97977626682966650,0xcae5b37f2232904aa,30034797767,4161,4167,4185,36394304197802,11509845,4163,4191,0xdf5b0d2749544660c,12870165,5403,55428433244890,
4168,4159,4165,61391546933880,9630328,11509832,14197168,45604538045607,4181,0x43ca592e2b817d49d52f,11075651,4185,11956319,0xd8abf4d525728b445,59566848983820,
4163,63388421464679,0x168562945cae67d,4201,14160835,27230662808,12869710,4137,12862635,13296045,26359693417,4185,4167,9631230,29077804094,
41604363195146,4166,29077803788,29079831306,4166,4137,25268028721,51746819465583,4135,4124,4133,14164821,4167,4244,41269441495472,
26360586773,4167,4183,26292585397,86286724942823907,4183,4179,4185,11355773,5756,97557403230987554,4168,4138,5756,0x27e6fe508b157ee8ecb0602,
14176326,4137,11970173,0x19244b2fd8c83db,4195,4185,29064413670,59523922682490,4167,0x1b16f62fd5fc4bb,0x1bf9620fca9060c,4173,5085,29060207372,9207885,
4201,9621593,4172,4163,4181,89766615991694389,20281513118,29974557170,4141,4138,61386191647488,4168,46346904130389,0x1bea7dd484311f6,61386165252425,
4183,11956296,11509836,10170428,4208,4204] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part209 : Refutes moves 0x80104000010000000000000000000 0x13e6713cc3c4104051012801040000 :=
  finish #[
14181666,55552412161547,4160,5756,0x734d8ebf8282fc2c10f6,25138062405,4171,4145,55828246762565,4138,0x1cd17ed60ace67d,23207798050,4179,4168,47308064408053,
47308037817867,12869707,4137,4147,20575138885,51756617766524,4138,49367766275141,10457922,4138,0x192b07c9612f26d,4171,4168,53338209691370,5757,
19702727179,12862625,11075657,4167,4191,0xe698557f255d850a9,12870061,4167,4137,55546758238924,27232109982,12750919,59571466073380,0x48e50d1792ba23429355,0xe6895d255480c825e,
4203,4191,8712291,4181,4179,4185,29042488149,0xbb4943282c504f60d,14635097,14148900,28967068962,4159,26030175310,0x59a58bcd23b497c45679,10981426,
4204,4168,63385402037881,25239180572,27250632313,9630104,4168,4180,4165,9540317,59403601962164,9539761,4146,4159,10044463,
12869701,4157,4147,19723105041,0x1bf69260fa7952f,4162,0x1afcf364da90344,19722404269,26118213731,4166,11330268,0x3076fa8fa061286581f7174,0xe6888d7d53fc3b122,4168,4166,
5750,29976932781,4166,5750,0x1afab0686df5457,29973738684,4168,4166,4210,12825758,0xd8a3eeb52faa7f435,0x16737d5398c85fe,8708203,4180,4179,
11509849,4184,4191,4156] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part210 : Refutes moves 0x80004000010000000000000000000 0x13e73108c2c4004040012800040000 :=
  finish #[
28148696367,19602499070,14202159,4157,53653399917873,57681839809841,12824645,4198,4186,26044048235,0x1beab8de4a0034f,11972677,4160,5644,27234215435,
14665227,29077603965,4167,4161,4173,53989201216477,9208019,4189,4181,0x176e7956a3d260c,0xc46b172b900051606,11972691,4160,29045843247,8725703,
4180,12870405,55361592780406,5410,0x9f7cd17d56acae679,22687277106,4167,0x1a377d56e2ea3ec,4193,4189,11509867,4198,4191,0x16a57f148446149,10528034,
5075,27235193316,12869715,4147,4629,20411621705,12374115,4169,4165,0x1bf8f26232903ec,0xb523eef34b18c860c,0x195c48050b6b261,10526792,4195,23443124738,
28147364354,10170432,4188,4184,26358236681,30028182831,26035205193,51817004729868,4185,4173,4179,13743740,46467211290121,9618844,4171,
12750947,26118215068,4146,4166,11973499,5756,29976974524,4186,0xdf595d1197d36b59c,10170424,4188,9277528,4198,4204] (by decide +kernel)

private theorem part208 : Refutes moves 0x80004000000000000000000000000 0x12e431084280004000000000000000 :=
  branch 2592 0x80004000010000000000000000000 0x13e63108c2c4004040012800040000 104 0x13e6713cc3c4104051012801040000 (by decide +kernel) part209 part210

private theorem part206 : Refutes moves 0x80004000000000000000000000000 0x12e431080280004000000000000000 :=
  branch 1 0x80004000000000000000000000000 0x12e431080280004000000000000000 86 0x12e431191284004284004004000000 (by decide +kernel) part207 part208

private theorem part204 : Refutes moves 0x80004000000000000000000000000 0x12e031080280004000000000000000 :=
  branch 1 0x80004000000000000000000000000 0x12e031080280004000000000000000 106 0x17f1738c42c0404000000000000000 (by decide +kernel) part205 part206

private theorem part202 : Refutes moves 0x80004000000000000000000000000 0x12e031000280004000000000000000 :=
  branch 1 0x80004000000000000000000000000 0x12e031000280004000000000000000 91 0x12e3b12212800a4081020000000000 (by decide +kernel) part203 part204

private theorem part200 : Refutes moves 0x80004000000000000000000000000 0x12e011000280004000000000000000 :=
  branch 1 0x80004000000000000000000000000 0x12e011000280004000000000000000 101 0x12f19980a280924000000000000000 (by decide +kernel) part201 part202

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part214 : Refutes moves 0x10024000000001000000000000000 0x1ae703a45490924010000041480101 :=
  finish #[
55770237154251,29058888331,4166,21480637365,14188744,0xa0a58d24afd8b73ba,4162,4166,8724684,4183,4181,61515760751797,29059310898,89183502252779023,4183,
4187,18317693180,4130,13297161,29059392818,9138251,4168,28029294314,30036136786,4165,40442916574268,49361964282110,29053662486,4169,15106115,
18687669317,10437683,11415609,4140,4168,14188751,30034632967,11342028,4185,61497601233144,26997138474,4163,35760186336304,49661700546808,10100825,
4183,11460699,4151,11518834,4168,4179,4196,4203,37308464816610,74421012498855434,0x32c657668bf99a4fb3622da,0x1940cd090c2e67d,25395873175,4199,0x84b588d89e9852341,
4179,4181,35376317182791,0x8759407c5b258e6ea,25262116947,4141,4195,4177,5423,4296,12755909,74578128382715057,4155,4199,11944915,
28145034868,4171,4183,4177,63361434387381,9425275,4157,5180,25192244179,4177,4183,43780511217268,4140,11518834,4179,
4203,4210,90098322157692425,0x68e07da372bac404134c,0xb5c0a57ee8d8b76ea,4184,4188,55768378225629,29063045527,14189871,39972255221039,4177,4171,4173,0x17757ee8d8b752f,
4188,0x6c42c60824705bd1b4ab,23499621679,4196,4210,4203,39760267526874,57685633635034,4210,36312045024082,0x56aa0ab12eee8e8b7522,18719367476,4153,13742167,4176,
5423,38340166731384,57639098937779,4171,4177,5423,19696760111,4177,13742388,23499621679,4196,4210,4203,12849235,4142,
4162,4152] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part216 : Refutes moves 0x10024100000000000000000000000 0x1af750a45c11935124100000000000 :=
  finish #[
13296509,4828,4828,20691227401,13295707,23593226301,4192,13210007,0x17932ba56af1674,4203,38233342404214,5411,55778666856639,73942956380198179,4193,
4175,0x568cae8832be4c8a5529,55774993649857,9097313,4174,4154,4162,0x3266fbdf53f82b65709b0f9,9643636,61361194210826,12849203,4192,0xdf5146b9e58c4111c,12849458,0x13f8a22c45f784c458992fc603,
4210,4175,4165,55778707972733,85272327907010168,85277899093951794,4193,4165,0x483913bf92b855c411b3,11509826,4163,4177,4170] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part218 : Refutes moves 0x11024000000000000000000000000 0x1ee791f53451925000000000000000 :=
  finish #[
4935,13301018,4169,10470682,21446190163,5629,13292618,13287497,4177,10006591,4176,19682796835,4163,4935,61505966634157,
80584422601172605,4175,12849225,17872196912,0x5e6dfc88325e56852173,11519279,4175,4203,4179,97055155392541565,5424,27232551794,11509839,4177,22548915721,
17862468466,4177,0x5e4cafa377defacae609,82070537885426066,9138257,4162,4176,4170,4182] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part220 : Refutes moves 0x10034000000000000000000000000 0x1af749b51510f75000000000000000 :=
  finish #[
14659852,13297161,4168,27134558501,0x16d52653b5886e9,11068696,9617499,4177,4171,74949372124968127,0x39a64b84e30746d2d92c60f,12849233,4152,0x6846680a47d9055f5679,77705760973816019,
4134,13702774,29010708086,30029075983,27254924918,4185,4187,11509847,12849233,5314,98877054896518448,4174,4168,4170] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part221 : Refutes moves 0x10024000000000000000000000000 0x1af710b41410925000000000000000 :=
  finish #[
59469403521422,28145860918,4166,5635,59418041652854,8724546,61389634307704,25044788854,4129,23141135990,4152,51291784987051,4166,48080239969910,13296509,
4168,4179,25117574426,25118114429,4193,12411964,4174,4183,4210,4192,44161405244155,5423,27235668836,14635901,10507094,
4195,4165,4210,12850808,74321498445919864,4174,4166,4168,96847880451155247,51601208940041,4946,23593215279,4165,4179,5641,
55786545128963,93947403138737347,4181,4151,4163,13246567,4134,4145,4287,5400,4964,57651313681926,4163,57648513794595,4179,
4175,4193,0x195d46c578b737d,4174,18703561576,55373026411597,4173,5411,0x13c8f308e4200a12b68dae3609,4175,4147,12850703,13743625,29978297170,21405115434,
12849222,11415618,4210,0xafc41529220caf356,4145,0x1bee7f1e6132609,27040465300,27040007329,4185,50107509306773,4147,4169,0x32b568877672226fa9320cf,5400,8697464,
29976957007,4152,4142,12850031,47474270320137,4185,5426,46222988219470,22565692467,4179,4185,4187,5400,59517065045186,26318193501,
4203,4175,0xcaf0a546c94932589,4174,4168,4165,4183,4192,37235697685679,9643645,61513984258483,4147,0xac67992befe2fc609,11343593,22291662456,
4179,98962791050891635,4147,9643640,4195,4183,4165,4168,10859932,5424,59523877512470,4183,0x530df792ed92572fc6e9,4203,12849266,
11509816,4163,4198,11956305] (by decide +kernel)

private theorem part219 : Refutes moves 0x10024000000000000000000000000 0x1af700b41410925000000000000000 :=
  branch 1 0x10024000000000000000000000000 0x1af700b41410925000000000000000 100 0x1af749b51510f75000000000000000 (by decide +kernel) part220 part221

private theorem part217 : Refutes moves 0x10024000000000000000000000000 0x1ae700b41410925000000000000000 :=
  branch 1 0x10024000000000000000000000000 0x1ae700b41410925000000000000000 108 0x1ee791f53451925000000000000000 (by decide +kernel) part218 part219

private theorem part215 : Refutes moves 0x10024000000000000000000000000 0x1ae700a41410925000000000000000 :=
  branch 1 0x10024000000000000000000000000 0x1ae700a41410925000000000000000 92 0x1af750a45c11935124100000000000 (by decide +kernel) part216 part217

private theorem part213 : Refutes moves 0x10024000000000000000000000000 0x1ae700a41410924000000000000000 :=
  branch 1 0x10024000000000000000000000000 0x1ae700a41410924000000000000000 60 0x1ae703a45490924010000041480101 (by decide +kernel) part214 part215

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part224 : Refutes moves 0x10804000200000000000000000000 0x1ae7e846111281c084242010000800 :=
  finish #[
26318513674,49654038827847,0x6fbd1bbeb6249520a609,4210,4170,59512590058908,17705763453,14181660,19684467532,29114724858,29063024698,4174,0x92a8552bec436751a,4148,4204,
4196,0x1a37608fe12a609,0x1788b1ac4c341ab,29978297858,11317899,4210,0x37d4fe49b8830d1b3ad628b,4162,4204,4148,5413,43234520560267,4161,43699377046583,0x68dd88bea0b57ccb134c,
27133661292,26294370342,4145,4155,4179,97039482742289021,14189307,21336180341,9609303,43917914358411,4204,4192,12755441,27147617451,4156,
53432484618531,10985531,59517278885139,0x6c4df5b10b9220b67603,4156,24490222337,0x18743f165d8860c,43924542723019,25118588994,4171,4178,4183,85974137830995572,29062123712,4174,
5424,0x17909d1e9052513,4183,12394707,51449322186246,10469443,4166,4181,0xc9994d7ddb3cb32f5,0x193c0f4fe12a34c,4166,0xc998829e96fcaf28b,0x1932f4af9d880fe,13247083,51448361186610,
21334852341,4181,4187,29012620592,14643837,4126,29012267645,11477048,4155,4162,5752,0x193346ef9b6727d,4188,55348240933864,23524782171,
4164,4183,4192,13295724,4168,4179,4157] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part225 : Refutes moves 0x10804000000000000000000000000 0x1ae768461310804000000000000000 :=
  finish #[
5314,4940,59551426565050,21517063098,4168,4173,4170,4531,82848350523991234,26318442691,50208657261507,4155,4165,23522911211,53895769338507,
4162,4178,4199,4183,8697463,48185138684108,4192,10527575,17810268811,4168,12837623,4159,5311,17768759947,4181,
4157,4165,11957530,5402,0x1b1d7f0ce1fc1b3,27056349613,11969499,4159,4199,12849239,4192,26318632457,0x195d1068dcaf67d,9642984,4183,
4168,53851662001783,0xc3e9497d57a2fb27d,4164,11912155,11509857,4184,4170,4191,4156,0x195d621b3c463ba,4747,8705000,4178,4175,
36566071223495,4191,14188743,55777738121415,4157,11510284,4163,0x188c82899367607,10616940,4192,4187] (by decide +kernel)

private theorem part223 : Refutes moves 0x10804000000000000000000000000 0x1ae768461110804000000000000000 :=
  branch 1 0x10804000000000000000000000000 0x1ae768461110804000000000000000 81 0x1ae7e846111281c084242010000800 (by decide +kernel) part224 part225

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part226 : Refutes moves 0x10004000000000000000000000000 0x1aef20041010004000000000000000 :=
  finish #[
14644636,0x18852885bd1b530,4406,0x9fc75b436fbc92673,19609105705,4152,5402,29975938352,25042075841,4166,12374081,4165,4192,4196,4162,
0x20a334d1b58d7d5029f4673,0x2ea5a45893b62de8dc410ff,4964,43355791823251,4166,21377740858,4196,4148,11076911,4179,5096,57645770711350,4170,4987,13276792,
98869469787567063,4188,0x10eb62d7d4ae0997f178afc456,4161,11075698,4179,13297277,19699139887,4185,61512029148463,53545328653610,22685917250,4170,11076019,11474557,
55772174681165,11518041,4196,10616946,4192,9281617] (by decide +kernel)

private theorem part222 : Refutes moves 0x10004000000000000000000000000 0x1ae720041010004000000000000000 :=
  branch 1 0x10004000000000000000000000000 0x1ae720041010004000000000000000 107 0x1ae768461110804000000000000000 (by decide +kernel) part223 part226

private theorem part212 : Refutes moves 0x10004000000000000000000000000 0x1ae700041010004000000000000000 :=
  branch 1 0x10004000000000000000000000000 0x1ae700041010004000000000000000 101 0x1ae700a41410924000000000000000 (by decide +kernel) part213 part222

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part229 : Refutes moves 0x40024000000000000000000000000 0x1bf742c11440924000000000000000 :=
  finish #[
26058915971,0x1684ef5dc2d44b5,4153,59520943662710,30027747574,4171,92801798666266233,27039162579,4177,36605970126454,4135,4185,4187,24181773839,37507164827900,
4171,25171588733,5400,0xd8e92f7f14328e355,4175,11509851,4177,12849219,0x1b10b52c3a5b352,29050979036,4177,47353093981232,14664752,10518609,4163,
9618504,59588932043470,0x1932b46213d860d,4189,4153,0xcaf78ebe852df50c1,12849226,4152,38203698876662,37195891062272,13300016,38203694834661,4177,4189,4171,
30023578332,30026846520,25318048597,4189,4177,4186,0xe698592b9d7d88521,13246768,4169,0x1936bb0965fc30f,10518609,11972675,4176,4168,5314,
4525,12350991,10101169,4175,12849243,0x9de01245afdc41530,0x1b1d1054121044d,13295706,59627002324367,5423,21610767996,4183,11509835,11972675,4176,
4168,0xca023926e5751b3e3,10621600,4186,22618653270,27230668406,24449316120,4145,4169,27234775473,0x177a4c257a1f609,4186,11956304,4172,4755,
43543848625449,0xd88bea755e7a4e3cb,0x56a21579e67ac44a9676,4195,0x1a36ed5093d82a2,4145,11956327,11509836,10170435,4188,4196] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part231 : Refutes moves 0x40804000000000000000000000000 0x1bf4f1420540804000000000000000 :=
  finish #[
0x9ec88d62222c29429,12752502,61387325224134,4200,59512682374774,49792700658774,4159,4177,4184,0x4f7acd95c21c2958860f,14214091,13292956,4145,61387325224457,4184,
4200,28041003632,21336712155,23449716233,4161,4145,11944923,0x4f7c460a5621b5afa67d,4163,4184,4177,0x622d88bf07bec0852112,59400854287540,5532,29004321972,
4156,4146,44010441192314,4184,4200,4877,11969509,4159,4177,11974262,98607201954493420,11485235,4157,4171,4169,
4986,11355663,0x30c56a669854d2ac436726d,4156,78159462258279618,4162,30034797533,11485265,50211461378901,11514746,24488128578,4200,4188,26125575695,22554379778,
11449865,4162,4155,5532,13219343,4182,26317120682,11326071,23196529271,4143,4146,14160496,4127,0x87b8832ba8dd8826d,22453241029,
4169,4157,4163,4145,0x9795d71061eb67602,4156,0xcb3bf6bae0ecae355,53284827018870,4171,59400648851667,0xdf89676389844152f,4162,19735806567,26319951006,11956290,
4156,4180,27182675118,26018870902,0xc92beb0eec3c3d52f,4168,0x1beabec982eb4be,4169,28147364732,10170424,4188,4200,4184,4578,11506540,
4162,23450640866,11956285,5177,86566191722583561,10170443,10616920,4177,4187,4172] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part232 : Refutes moves 0x40004000000000000000000000000 0x1bfc60400440004000000000000000 :=
  finish #[
0xd8e6cf289ec2904c2,0x1b1d7d56ec41430,53901356598110,4171,25285952378,4185,4529,0x93083b62db4290609,4185,52084066226609,0x16bc4c17a2f949e,28147363929,10170424,4196,4184,
0x1bf90a8cf2904c7,11448822,4155,45552686756936,4156,53992003420939,18335380348,55308402099066,9633869,11509845,4987,11973499,10170440,4200,10616920,
4177,4745,61392810476847,4179,21545530129,4176,11973499,51975498629769,4172,4177,0x19257d5b3cb328c,11510413,4177,0x567d1b8777d61ecae6ea,0x195cdad7d220676,
10170449,4200,49863230817147,63333231519028,29977334964,9573679,11960384,4181,4769,20698281263,4200,21586059360,4183,4193,9281636,
4201] (by decide +kernel)

private theorem part230 : Refutes moves 0x40004000000000000000000000000 0x1bf460400440004000000000000000 :=
  branch 1 0x40004000000000000000000000000 0x1bf460400440004000000000000000 107 0x1bf4f1420540804000000000000000 (by decide +kernel) part231 part232

private theorem part228 : Refutes moves 0x40004000000000000000000000000 0x1bf440400440004000000000000000 :=
  branch 1 0x40004000000000000000000000000 0x1bf440400440004000000000000000 101 0x1bf742c11440924000000000000000 (by decide +kernel) part229 part230

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part234 : Refutes moves 0x1024000000000000000000000000 0x1fe180d12441924000000000000000 :=
  finish #[
4949,24260191533,4183,4307,61385058812630,4170,4949,55768460662395,4169,0xad4bf4802574ac4b5,4159,29974594863,17870791509,4186,4182,
4196,4175,59515389084976,21627102490,4196,30031549016,17671320663,14188593,28985579017,29058475533,0x1758b8c9b21c37d,10498148,4183,4193,0x56a3d85952949b2fa0c1,
4170,4177,4163,4743,13255955,27229758551,4179,9138267,0x1a2208569588347,14188755,4282,0x1b10689ec203301,4193,4153,9138243,
36189808599226,59520072737879,59521121308883,4180,0xa003030c6fa9360ba,4175,36355206792390,29097968800,51634361790866,25209037693,4175,4189,78514639861798409,10620998,4201,
4203,4193,4196,4198,5532,0x1b1111654cae282,4146,59521077585308,4177,0x1bf4a219c8a1beb2b4d14ae355,28146012827,4186,4203,29069492898,92658584662287640,
27234775107,55755072529026,26350801570,4203,9658438,4172,12849464,0xa215970c45bafa19d,4198,11388209,47766961394993,11509836,55359935538467,81753922246841211,4171,
4169,21528749581,29037880602,46388876746998,4187,4189,44553797350251,4198,5423,17826125103,18721222745,4172,13742170,11972652,4192,
4152,4176] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part236 : Refutes moves 0x1804000000000000000000000000 0x1fe4a01f0501804000000000000000 :=
  finish #[
27277611777,28148708982,53972066402946,53971981623938,4157,57648473159066,4126,4166,4146,4302,28148217108,8717500,11509853,4191,4177,
13295799,12870523,9658449,4172,59523865305299,5180,61395603223712,4138,4163,14635500,55770163205180,4166,4146,37478150919443,29977404576,
25192260768,4175,4169,55768460300499,4152,5300,55768456589954,4174,4166,4172,14188755,37229862614646,4163,97203562937414401,49654835737903,
9138215,4166,4307,5641,29981222192,13295703,4201,0x529d85beb116c443152f,4166,26186646832,0x6c42cbbeb62a5734a513,12338456,4169,4183,5395,
29063894318,14635057,12710958,55755743618791,14635047,0x852b10d2a22a0126b,4166,9658418,4181,4175,11972708,4200,93643911256901130,29058426055,59511658418606,
4196,4181,14189767,29062534343,11509860,11972668,14636212,25086341510,14636212,74863367752349195,4147,4171,4165,17843721739,4146,
17862468807,4191,0xb52b0b6224cbad281,55392199030173,13292847,8724531,4179,5319,0x6c54aebeb62223051267,11509853,4198,27234304142,27230564742,13742131,0x188c8065704f264,
4181,12826230,11972710,4152,10616936,4182,4177,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part237 : Refutes moves 0x1004000000000000000000000000 0x1fe8a0110401004000000000000000 :=
  finish #[
10793132,41465952093814,4138,61389696885478,23574216783,10617831,14186102,18391782920,4143,28146902536,4163,10380918,47766430548272,9658432,4175,
0x817767105b5a20281,4192,0xc4477a9550022017a,0x2014429e68888802936b173,4176,0x176d7d5a858852a,0xd87beb482c42fa4b2,92997255113606774,4192,4177,17854910875,0x618df50217ce208520ab,35923797914818,4160,4192,
26318635975,21749548009,4177,11432003,11489328,4196,4186,4193,4200,11518133,11972916,4176,4535,19782566892,4192,
4202,11973826,0x187d0e9d9afc1b7,4196,4987,17869964155,12869728,11075665,4191,9281607] (by decide +kernel)

private theorem part235 : Refutes moves 0x1004000000000000000000000000 0x1fe0a0110401004000000000000000 :=
  branch 1 0x1004000000000000000000000000 0x1fe0a0110401004000000000000000 107 0x1fe4a01f0501804000000000000000 (by decide +kernel) part236 part237

private theorem part233 : Refutes moves 0x4000000000000000000000000 0x1fe000000000004000000000000000 :=
  branch 2156 0x1004000000000000000000000000 0x1fe080110401004000000000000000 101 0x1fe180d12441924000000000000000 (by decide +kernel) part234 part235

private theorem part227 : Refutes moves 0x4000000000000000000000000 0x1be000000000004000000000000000 :=
  branch 1 0x4000000000000000000000000 0x1be000000000004000000000000000 114 0x1bf440400440004000000000000000 (by decide +kernel) part228 part233

private theorem part211 : Refutes moves 0x4000000000000000000000000 0x1ae000000000004000000000000000 :=
  branch 1 0x4000000000000000000000000 0x1ae000000000004000000000000000 112 0x1ae700041010004000000000000000 (by decide +kernel) part212 part227

private theorem part199 : Refutes moves 0x4000000000000000000000000 0x12e000000000004000000000000000 :=
  branch 1 0x4000000000000000000000000 0x12e000000000004000000000000000 115 0x12e011000280004000000000000000 (by decide +kernel) part200 part211

private theorem part187 : Refutes moves 0x4000000000000000000000000 0x10e000000000004000000000000000 :=
  branch 1 0x4000000000000000000000000 0x10e000000000004000000000000000 113 0x18e900100820004000000000000000 (by decide +kernel) part188 part199

private theorem part171 : Refutes moves 0x4000000000000000000000000 0x10c000000000004000000000000000 :=
  branch 1 0x4000000000000000000000000 0x10c000000000004000000000000000 109 0x11c000809002004000000000000000 (by decide +kernel) part172 part187

private theorem part143 : Refutes moves 0x4000000000000000000000000 0x104000000000004000000000000000 :=
  branch 1 0x4000000000000000000000000 0x104000000000004000000000000000 111 0x105020012008004000000000000000 (by decide +kernel) part144 part171

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part242 : Refutes moves 0x2100024000000000000000000000 0x174c9c94290d32c086100924000000 :=
  finish #[
29060821144,59516563411096,4156,25289512457,5298,12420030,10481748,4154,4144,4736,5308,21469115442,22543757956,4156,4180,
5633,25260053321,53487957959296,4172,4154,92975242997387751,4156,45402050007313,10457129,4138,4198,4148,0xb45030f19d4588310,5310,12834537,
25286202998,4174,10408002,4156,5096,8634779,12869698,4157,12870359,26034295546,4156,51276612396095,39931329541750,4156,26360575017,
8676987,4174,4166,10035276,4175,4167,19340222969,22644737545,9631241,24206041169,4135,59599560504156,4211,4858,0x1b10a2efab6752f,
4172,4156,5423,35718982439786,59556409962867,24206041196,27231483070,4156,40396292813432,4173,4174,29046261026,55357828142599,21471258119,39857828123574,
4160,4173,4174,21471355070,12371019,55773992608384,4173,10571855,10510433,4211,4166,4201] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part244 : Refutes moves 0x80100024000000000000000000000 0x136cc4b9990412e284100924000000 :=
  finish #[
0x1cd17e532ac16e8,63370310484752,21514666074,9467625,10503689,61506462425718,12869702,4197,4167,9441925,0x9f9be23d480aef67b,4166,24204214424,4167,5756,
0x1b1cef65092d6e9,4181,10503038,55510684964361,11817036,4186,0xd88b04eae8cc29362,51631809795489,23598388861,4163,4181,12309125,4526,11276922,0x6c6ac188d481e812d3c3,
12382287,4207,4163,63363688740039,15107271,14190205,13313312,22642966607,11817013,4138,4186,13295724,4168,4135,4201,
0x1964f42facae25f,27235669280,0x6fad86965459022f06e7,4160,4167,4728,0x8ff5d027cbfc9c453,23598387832,4163,4178,0x64a5f54092b8fb9011ae,0x195d62d024b21ae,4139,48218647777925,61388004197679,
4160,11956295,4204,4196,9519616,5641,29059294511,4168,4186,40032312943901,39403493159413,10502244,4204,21402907259,0x176f2c99d446186,
53988986671970,61392508368149,11956320,4204,61392854541615,10449313,11440218,4181,4195,11509831,4177,4156] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part245 : Refutes moves 0x100024000000000000000000000 0x1b6c04900904124004100924000000 :=
  finish #[
0x3261e0668bf863ac7346609,12288152,0x1bf81156ed8a285,11956277,4148,14177803,0x1938819d44ae4b9,13287496,14665337,17335772787,0x19437f0089ea0f7,4148,72452932863525391,4151,4171,
27014886256,4180,13296263,59572657271429,4184,4169,4187,4181,4248,0x1cd347080838bf8cfafa933438,4181,40464986220156,4173,11821947,44175838844189,
13295701,11817851,82885400126952733,4181,0x60f92987b2c9a35fc456,95129567108396202,10580053,4168,4178,4186,4198,86636519927820538,51266084656642,4166,11956524,
11509836,98535043857490773,47747429148393,10613398,4171,4193,4201,5865,48331444257442,4149,10560368,10621819,9281626,8831077,4210,
4207] (by decide +kernel)

private theorem part243 : Refutes moves 0x100024000000000000000000000 0x136c04900904124004100924000000 :=
  branch 1 0x100024000000000000000000000 0x136c04900904124004100924000000 115 0x136cc4b9990412e284100924000000 (by decide +kernel) part244 part245

private theorem part241 : Refutes moves 0x100024000000000000000000000 0x134c04900904124004100924000000 :=
  branch 1 0x100024000000000000000000000 0x134c04900904124004100924000000 109 0x174c9c94290d32c086100924000000 (by decide +kernel) part242 part243

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part248 : Refutes moves 0x2100004000800000000000000000 0x154c3e86210110c302904204084800 :=
  finish #[
12314230,25217365622,4166,13226408,4876,0xdfa4ac48e4ea85176,4156,4192,4162,81925895489746324,97195786210465398,4150,22545097100,18586568310,0x177c0c1ec1354a5,
0xa8fb117d57daed1f4,4178,4192,4199,37855260345647,0x968b00d51dd0c26e7,59381736202981,4135,4189,11457274,22491124590,4189,4192,24331871307,4880,
47340592251664,4150,4192,52009631810863,4156,4166,4161,4201,4211,37876356702456,0x17872a2c191a0f6,27008729142,5641,10482614,4149,
4169,5399,5428,0xd8a58b2cd0349d37a,0x1b14beec02df529,4157,4178,4171,4419,14189191,59511533109527,4163,11464759,4209,4201,
24070034733,76745904492422427,10924093,29021996337,63334880388619,27248322059,28142101801,4163,4151,4201,14168940,0x973b1a7d493bca36c,4157,18601111625,4156,
4148,29058916873,5428,28994486797,14188625,0x187a5fdb3aef676,4166,8749161,11785850,14636113,29103952838,4150,14636113,0x2eb1ec127a1b24ec43ba4b2,4150,
27184018521,4151,8749133,4190,14635762,59604897342406,4150,0x1bead9e228584b4,10498144,4148,55772873086363,36704341537733,5096,49549221340681,59518080877310,
4154,4178,4172,10571828,4313,5406,8746618,4864,10982132,4144,11956278,4172,4204,24488551168,4171,
94144470667576254,13296597,0x47b36795cee82c12760e,4184,21737115742,4178,4183,4201,4211,4198,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part251 : Refutes moves 0x80100004200800000000000000000 0x13ee6ceb1992306780b0440e214802 :=
  finish #[
13295945,18862498993,12387390,4162,4171,4716,43625991270580,4148,13316312,4163,12383294,13316741,4174,47850269086911,17301701488,
26207245288,9207890,4181,4193,4199,4196] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part252 : Refutes moves 0x80100004000800000000000000000 0x136c64eb130230438090400e004800 :=
  finish #[
14656223,42130126758151,4192,0x194f2b82bb6719b,4204,5207,23483073623,23480869813,4186,4168,41267208782250,0x7342d32349319a2ef515,10043462,4157,4145,
0x177ab0683d883cd,24489424177,4166,5096,12273161,29978297649,53630253560025,4172,12779620,0x9decd058a18258609,0x876104160620c852f,4193,4183,4195,11408581,
29078373547,25082298993,4192,4129,9208341,4181,29064410411,0x16897ec112e8676,4145,0xcae77a9dd41b67088,4196,12861765,27232847374,12375231,11956320,
10502244,4174,4204,4149,4179,4199,8750366,96939222781210992,4948,0xad32129dec412d370,4196,4160,51488811942217,0x48f3be5d02f896d886e9,63362358083913,
47978074264186,25371181126,4162,4171,4207,4172,39498678145271,90223926011949430,4181,75157086251025264,0x9f93f4620644a9451,5069,5069,59518149915729,4181,
27091742790,4129,4162,14663791,4149,89234082039890288,21192586525,12420732,4207,10847312,0x1b107e6570c82ee,4193,4195,14663785,77389043234862714,
47735728829966,0x577dfcb1b27494a7f534,4162,14189745,20185424587,0x9f7b10052574b2261,10449325,72253658611963401,11072819,4178,4210,4192,4201,4183,14189316,
41705631417652,55854145553479,94346079032096160,4210,4192,9367630,4137,21128315388,14189876,9581854,4192,14663746,11956277,4148,4204,
11509860,4156,4163] (by decide +kernel)

private theorem part250 : Refutes moves 0x80100004000800000000000000000 0x136c64eb110230438090400e004800 :=
  branch 1 0x80100004000800000000000000000 0x136c64eb110230438090400e004800 81 0x13ee6ceb1992306780b0440e214802 (by decide +kernel) part251 part252

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part255 : Refutes moves 0x20100004000800004000000000000 0x196c24d20124124920904024804800 :=
  finish #[
0x29f2c5433becb156b58859e,23133193263,11514927,4204,4192,4981,27123811381,11830248,11400168,4178,49620036178920,4198,4193,4196,4181,
5396,11456954,4178,24491144387,0x1b1124d10a1237c,4178,4198,29078357629,29079844119,11956335,0xc96586d7ac43671a1,30034334326,48265489794024,9670981,4175,
4193,4184,4178,0xc38884bb6fe217309,14665227,9672315,4193,30036054632,10581290,4193,30033388852,55486652060524,4204,4192,11509847,
4184,4198,4177,4163] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part257 : Refutes moves 0x20100004000800000000800000000 0x196c24920124124924924024804800 :=
  finish #[
0xca7bf29f19ed88672,25085507081,4204,5065,77183664664437600,23390880744,0x1b11429032fb375,4178,4183,0xa8e28f62110a151c3,4198,4193,4181,21529965864,11456954,
4178,17286334069,29060342761,4181,49431057605908,4178,4198,5399,14663845,27088937405,4201,29077038157,55356116825725,4178,4157,
4171,48062166709174,5756,30032499335,11956303,4156,4148,4986,0xbb55047fafe217604,4193,14665007,21652280249,4193,61513907966611,47669812495881,
21502235924,4193,49570192004394,4192,4204,11509847,4184,4198,4177,4163] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part258 : Refutes moves 0x20100004000800000000000000000 0x196c24920120124924904824804800 :=
  finish #[
23132284425,11363849,19875738026,4192,4204,4988,13296471,0x60ebb4876b7d9c4a1609,11829344,0xd0ab10d2110a15211,4193,4196,4181,27090215363,4755,
0xc9485c4fe2022160b,4186,4181,30036026645,30034227642,10511663,4201,4171,5756,97944429558731379,11956303,4148,14665007,21652280249,4193,
0xc40bf32cefe2121ea,27091707168,23272191252,4193,0x6874aabf8a2d75af93c6,4192,4204,4183,55768525058577,23348614329,14663755,14665225,61462401913352,4181,27088957893,
30032433804,17911869922,4193,4183,4313,46136784197244,4201,0x6c1e69876a16fe36752f,4180,4148,4204,11509860,4156,4198,4177,
4163,0x1b119a17dcb21c2,20144145253,41260681995894,0x1b1051da42f4675,4192,21653902281,5405,29103207021,4204,4183,55841627522571,23129596904,10510433,4156,
4166,4196,4181,77160162708968262,26160137845,11457711,4178,26160136646,10621577,4178,4198,4181,0xb67cd0312fe496533,0x1929286165fc609,30036104478,
11956871,15106108,11961311,4179,4189,4171,0xba97a6b7f3449d3d7,55856206956041,49577684837546,23272191252,4193,14665011,59520918509290,0x1cd079efe3c452f,4201,
23449276516,4192,4204,4183,98839785998743041,13297051,11420975,14663732,11957885,24145982772,61511248688757,4181,21486798122,17924342629,5096,
14664680,24344544209,10621027,4186,4181,4183,4193,4201,30940307556,4184,4156,4198,4177,9441347,4128] (by decide +kernel)

private theorem part256 : Refutes moves 0x20100004000800000000000000000 0x196c24920120124924904024804800 :=
  branch 1 0x20100004000800000000000000000 0x196c24920120124924904024804800 35 0x196c24920124124924924024804800 (by decide +kernel) part257 part258

private theorem part254 : Refutes moves 0x20100004000800000000000000000 0x196c24920120124920904024804800 :=
  branch 1 0x20100004000800000000000000000 0x196c24920120124920904024804800 50 0x196c24d20124124920904024804800 (by decide +kernel) part255 part256

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part259 : Refutes moves 0x100004000800000000000000000 0x1b6c24820100104100904004004800 :=
  finish #[
29940544379,61453136544130,30011851618,4173,23366296632,4156,4178,20604023664,55356965933381,4199,19758294310,4163,10592472,4186,4181,
39929441657921,0xcae750841e93d61a4,4160,0x6c53ae5f57d4cc3673d9,0x883be215db3a212fa,4186,4188,4987,41261627528822,4144,0x6c5df401620dd75fc3c7,0xb502e2ebafe0c43e9,4181,98012815721596428,11956326,
4196,0x1be2bac625fc609,11511418,13297053,4201,11448969,13266996,4153,0x5b3aeb7ac311dd9331e2,4196,14664760,49897652388165,4173,0x176ebeafab67145,26183529339,
4186,4198,11514292,11456585,4171,4178,4199,4204,44216656990424,4986,5278,63372212928665,11509844,4156,0x5ec25b6ceb7c2c2ed4b1,
9281597,4199,0x16b108977a2112c,21753832746,19009028163,4210,4207] (by decide +kernel)

private theorem part253 : Refutes moves 0x100004000800000000000000000 0x196c24820100104100904004004800 :=
  branch 1 0x100004000800000000000000000 0x196c24820100104100904004004800 113 0x196c24920120124920904024804800 (by decide +kernel) part254 part259

private theorem part249 : Refutes moves 0x100004000800000000000000000 0x116c24820100104100904004004800 :=
  branch 1 0x100004000800000000000000000 0x116c24820100104100904004004800 115 0x136c64eb110230438090400e004800 (by decide +kernel) part250 part253

private theorem part247 : Refutes moves 0x100004000800000000000000000 0x114c24820100104100904004004800 :=
  branch 1 0x100004000800000000000000000 0x114c24820100104100904004004800 109 0x154c3e86210110c302904204084800 (by decide +kernel) part248 part249

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part260 : Refutes moves 0x100004000000000000000000000 0x114c04820100904000100004000000 :=
  finish #[
4763,4956,10593147,4183,98522963752505780,4187,4195,55853318120058,4932,12313541,13295665,11904301,30025875972,4145,4159,
5200,40052518827529,11956288,4196,0x16ceed2fd2f652f,25370256899,0x17684bd7d4a9377,4196,4163,0x16cf621782f7300,4160,4174,4201,11494249,0x1afd2a6fdb6742c,
10580968,10621000,4183,4635,59340748575819,0x1786d68cd2f6609,4187,55670084866480,4198,8831073,4210,4211,4204,22576866139,0x169f7d57b5fb526,
37374152332137,23427265272,4204,11523159,4174,8745024,4188,10559704,44130672743366,0x80f68b7c904198528,4161,0x1780f497d19830c,98982752256398151,4188,4196,
5747,0x8897ad7d6c42f435b,10621003,29061273203,0x17ad7cac4221429,23331844196,4162,4199,4204,4211,29064385515,27192316625,27193713531,11510873,98892425087062515,
0xdf26d56217d12c1f3,4183,4168,4171,4159,4162,11380233,13275995,23576469570,4137,26116785233,0x4edcacbf6a0d7436742a,12869740,5096,45551142252973,
4186,23095079129,25372038011,12869699,27190583725,4159,4152,59517378196456,4160,4174,4188,74107370472760155,59520112870247,59571785761653,9655461,
4180,4198,4183,0x16a56224b4a908f,55481107207694,11382868,10572999,5319,10592694,10621003,4183,4198,4188,11334632,0x17a6bea232213e8,
4193,98007277462013106,9281650,4205,4211,11075695,12402789] (by decide +kernel)

private theorem part246 : Refutes moves 0x100004000000000000000000000 0x114c04820100104000100004000000 :=
  branch 1 0x100004000000000000000000000 0x114c04820100104000100004000000 71 0x114c24820100104100904004004800 (by decide +kernel) part247 part260

private theorem part240 : Refutes moves 0x100004000000000000000000000 0x114c04800100104000100004000000 :=
  branch 1 0x100004000000000000000000000 0x114c04800100104000100004000000 89 0x134c04900904124004100924000000 (by decide +kernel) part241 part246

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part263 : Refutes moves 0x2500000000000000000000000000 0x1d52cc967500000000000000000000 :=
  finish #[
0xdf5a430f5b384e3e3,5423,0x5b3d8895c7fc9249d2d4,4173,27233415478,4171,0x9223ff2757d85452f,8716384,4190,20481970490,28199911738,4160,14189193,0x1b117d50452126d,4974,
23581594705,4189,4171,4174,4183,0x1b104d5ea051532,13296720,59366393910575,27231941703,9146434,4174,44127956685544,13296265,0xd210496209aaed447,8732747,
4189,11075671,4197,4179,11956434,0x19522f5ea13552d,4174,44170890994528,0x1863485ea0503e8,11075671,4197,41999483933999,0x1b1124a90df56e9,13296818,59513517102366,
4170,4190,4184,55774794618377,25141018934,4184,0x1a3529690b673c5,4156,4148,0xc96950ed4fad883e8,55768292083200,22687277118,10571847,61390984451157,55773167228103,
97620253001220303,4184,21737115742,4183,4193,4196,4203] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part266 : Refutes moves 0x8500020000000000000000000000 0x1f7a7f48d5852a0214000800000000 :=
  finish #[
5423,5538,49588405462322,8672559,4167,4173,4171,61394690770223,52066021840399,4160,5207,0x195cf4a90a100c6,11509835,4177,4156,
55342510403778,36310042960720,13217877,37722609054798,4156,13309231,27165880746,27232543687,4184,10580028,4186,5423,76440804176618907,10614049,4181,
4171,19524314047,11956542,4172,5055,13288751,4177,11956542,4172,5423,98882354912818366,4171,4191,4166,28196261948,
4158,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part267 : Refutes moves 0x8500000000000000000000000000 0x1d72674ad500000000000000000000 :=
  finish #[
13218000,0x1b152bac44a034d,55828414129011,55775933215831,9068612,4155,4979,8712599,4186,4177,4169,17847400060,57754334171781,11506757,55629082236534,
23567622350,4151,4156,4196,4169,0xb68a4326d732f4609,12402749,4203,13296709,61395554886508,4156,30036124732,61496748889391,61389942907186,4160,
10502204,4149,0x6575f55e8301022f9679,4171,0x5e05216cef5975af24c5,0x19282e42c5fc51c,0x1cd3621ddd8e95cbc82c2fb12b,8728649,4186,4188,11334615,36498096882775,11952554,4171,27232108613,
52063229842953,9192300,4421,11076693,4167,4209,4179,47493382378914,5205,18826724218,4173,4179,29977875150,52023795864337,29976466735,
4196,21609858351,4177,23524782163,4157,4171,4199,59520968480162,13766958,25403393309,4179,4167,11505877,0x1954bb45cafb311,8729454,
4181,4179,4184,30034150361,11334743,0x16cd485b384a219,4171,11075657,13284748,0x1bf92adafdfb3c7,13766724,4421,61510965347142,11957062,11960388,
4171,50171226948243,4209,4173,0x158ef01ea0c45d6f59b3af22f9,4169,4199,8749934,5423,11076248,12402765,4167,0x17a82f5792fb609,4169,0x17a81610fa2152f,
4181,4186,4196,4188,4203,4191] (by decide +kernel)

private theorem part265 : Refutes moves 0x8500000000000000000000000000 0x1d726748d500000000000000000000 :=
  branch 1 0x8500000000000000000000000000 0x1d726748d500000000000000000000 89 0x1f7a7f48d5852a0214000800000000 (by decide +kernel) part266 part267

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part270 : Refutes moves 0x20500000000004000000000000000 0x19fa5ce25d00100100044000140820 :=
  finish #[
90655224798073679,97622030207799717,4163,10552143,14656455,59523907248613,11272237,10552401,23407312981,4150,4192,0x188d63049cae602,55297675309920,0x1bf9276575f552a,4156,
4184,29977335091,97381487037146639,5408,13296454,4124,27087627901,12869717,4157,4187,23203197436,59624243840199,26360131901,11509833,0x1966bec9613867d,
4186,4192,4171,4183,4177,29114270317,29061042797,57661667434991,4139,14663755,30035698742,29104964911,4173,30034228193,4758,
9586075,4187,14664784,4135,30037017440,49867862205748,25295683675,4145,4172,4171,4181,23205794516,49590284530395,4151,27092637308,
27274929455,8691803,4181,11514720,4199,4631,0xcb25ad622572fb2f1,8716389,0x1b1d276fe13826a,82625006317696527,4168,37195520598680,98908640110802666,4192,4197,
0x1bf91190fa21436,4181,4193,4186,4183,13296278,0xbb54f4856575f56ea,4184,29977403704,4305,0x19283190fa2167d,4193,4181,4183,0xe69a3911933cae531,
27232544030,4184,4986,83055704168297528,4193,11956311,4148,4156,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part272 : Refutes moves 0x20500000000000020000000000000 0x19fa5ca25d22004800800220000005 :=
  finish #[
14153007,14169395,47288928642351,27104870605,4210,4187,27263283857,4537,55768475735347,4199,4192,4171,4183,23578236103,18845295430,
13271931,4163,4162,14635665,48185159046887,4162,11506996,61390076224373,97921123177755924,4172,4175,4177,4171,11511081,14655815,
13296947,29114717487,27235669034,9098543,4166,4162,12869692,4157,4187,23527903767,18634040188,10552401,4181,4162,4960,
27232543022,4156,23203185531,19697730426,4192,4183,4177,4171,27008730415,29058450263,9666645,0xba995d60cc48ad19f,36276798461009,10531680,4156,
0x1a292cec10414ad,97921123177755924,4177,4175,4171,13766726,4134,4146,4170,27272107529,28995912099,13768425,63370377618737,4167,28135753009,
4184,4187,41942962832687,55623076833001,23231066197,4171,4192,0x1afe857344ae4b2,57751593002511,4170,30937547975,17643386377,11956299,4148,4156,
78438069846550134,22417486359,8716384,0x1cd012a90acf88cbc97d2123bf,5641,0x362334cb33d96309c0575a2,4190,4717,10994887,4171,4929,0xd823d32b93e3c913e,4174,10580064,10621000,
4186,4193,4183,4188] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part273 : Refutes moves 0x20500000000000000000000000000 0x19fa5ca25500004020000000000000 :=
  finish #[
0xc406ad9a2bea1267d,51801511293120,25370276704,4183,11956327,61513981560553,18684997950,4156,10621590,4193,13766746,11400489,61508280100361,4156,0x362a59180bec9c2c42d6534,
0x480980bec9c2c436734f,4156,61394689954233,4192,4183,5538,61516772057341,4184,10986336,4181,26181207552,17921635518,4148,0xa7a862d9e90afa609,4170,
4156,0x1cd362a8a5fc350,97014527021790845,23574159463,29972854154,0x6fb0765e4b393e21752f,10621000,4186,4183,12402785,4140] (by decide +kernel)

private theorem part271 : Refutes moves 0x20500000000000000000000000000 0x19fa5ca25500004000000000000000 :=
  branch 1 0x20500000000000000000000000000 0x19fa5ca25500004000000000000000 53 0x19fa5ca25d22004800800220000005 (by decide +kernel) part272 part273

private theorem part269 : Refutes moves 0x20500000000000000000000000000 0x19fa5ca25500000000000000000000 :=
  branch 1 0x20500000000000000000000000000 0x19fa5ca25500000000000000000000 62 0x19fa5ce25d00100100044000140820 (by decide +kernel) part270 part271

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part274 : Refutes moves 0x500000000000000000000000000 0x1bf244005500000000000000000000 :=
  finish #[
47497083543814,17820464654,12781171,11969727,4193,4161,4169,28995908885,0x6c74469536217d4a867d,4141,4163,0x37d56658d95d274962f936e,4171,0x22f5b3ca7bf8be425af452b,23524783407,
13767656,8713519,13296720,22172320515,26034294865,9162804,4174,0x6c412295d2ca1a05151d,11957100,11505716,53979828814707,4193,4191,4189,4187,
4188,28198125966,0xa537a8d9e908bd52c,4987,47578366854447,0x195cf51a136213c,4175,18275316661,0x1b112cd9b2d134d,57667523642333,4175,4199,30036103568,27193754319,29064414514,
0xdfb598d4a54dfc352,0x1b10d4afe444223,4169,4159,4175,12402791,21670895669,10620995,4183,4191,4188,27233436302,12870741,26357321930,4181,
4177,0x57d25bbea886908bd28c,0x34864fca96ce85d10a90532,4185,9281631,4197,8831083] (by decide +kernel)

private theorem part268 : Refutes moves 0x500000000000000000000000000 0x19f244005500000000000000000000 :=
  branch 1 0x500000000000000000000000000 0x19f244005500000000000000000000 113 0x19fa5ca25500000000000000000000 (by decide +kernel) part269 part274

private theorem part264 : Refutes moves 0x500000000000000000000000000 0x197244005500000000000000000000 :=
  branch 1 0x500000000000000000000000000 0x197244005500000000000000000000 111 0x1d726748d500000000000000000000 (by decide +kernel) part265 part268

private theorem part262 : Refutes moves 0x500000000000000000000000000 0x195244005500000000000000000000 :=
  branch 1 0x500000000000000000000000000 0x195244005500000000000000000000 109 0x1d52cc967500000000000000000000 (by decide +kernel) part263 part264

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part277 : Refutes moves 0x40120000000000000000000000000 0x11fe16455124800000000000000000 :=
  finish #[
26315830248,5757,61496644933126,0xdf1bf6b86fe1fa51e,4159,12849265,72109177144423468,26318083375,10580081,10621000,0x195d7d570b674c2,81265049879344655,0x1bea4b2c42fd521,4174,38438680088886,
5096,48214022488278,10621041,4183,4211,4181,19710641241,11499017,4174,38438680088886,13296283,5096,48214022488278,4209,10621027,
4183,11509875,4163,4156,4198,5538,61325970928834,13766972,28194836796,4164,4178,4166,13767060,27234801161,50159055525167,
4174,4188,13767060,23314175721,4188,50159054553762,4171,4211,4198,53904267441786,50157178720465,9154870,4166,4178,0x362dec2e993d6217b85551e,
5645,14209686,21655008772,4148,29977404941,4146,11509832,59362843169768,11494249,4181,4209,0x195d485b3afa676,57742239704040,4987,48216762831848,
4187,4195,4181,11957442,0xcaebeb0cdb3a174c2,10621000,4178,4183,4211,4198,81968735535239904,5314,4750,23425012820,4159,
4166,11956339,12850152,5096,9154870,4178,4166,4174,5096,18701776066,5314,29059384299,11956294,38404314420418,4179,
4181,4178,13767983,11408578,11956337,26186224616,0x1a42855742f6609,4209,4770,0xe6823f4857e85529b,4189,4183,4181,52091888686606,0x1a431050ba2167a,
11509875,4163,4198,12402783,4149,4185,4158] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part279 : Refutes moves 0x40100000200000000000000000000 0x11f634446120000601100400000800 :=
  finish #[
12273161,23567631644,11378764,39961479537241,0x195d29ec72da6ea,4180,4986,5314,11506879,10461266,4189,13226057,4174,0x19667e96dafb4ab,4974,
55297614685375,42079690785950,4193,4189,4187,49657779250012,26318632457,4172,78731779888497963,97791847366554920,4156,90124089220371983,11485250,4178,8749925,
24490808738,4172,17923843252,11957438,11436108,0x53d666177486573674bc,53900561909042,8742196,11464792,4152,75168788809504271,4167,4174,4166,4187,
4180,4188,0xcb38836224e053602,27089941689,4169,55326488376836,0x9ec5db48620e6988110ac4056675,12402781,4158,0x195cf5220a1067c,5096,0x1beb0b653ca9459,4152,13296246,12420726,
8745027,21695172699,4188,4198,53899563663764,5641,23371896329,4172,97750888731924202,9622722,4172,27108500898,98505394106651737,4174,4188,
4180,4166,8746292,53678094255080,14189857,12419945,4145,27020940586,9207896,4193,4199,11076693,4167,4185,12403689,
21753803970,27273597595,0x3486492cf966885ea290363,4167,4185,9281631,4211,4209,4203] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part281 : Refutes moves 0x40100080000000000000000000000 0x19f434c4c340190040020000000000 :=
  finish #[
5096,13767874,47906613601578,4184,4198,55841795327610,0x1007075b3df99657f24e04b1a3,4173,0x1bf3271e33670912c825af94b2,11485250,4178,12850260,0xbc7096f5220a1067d,4171,0x6fe3c36cf1050d2fa097,
25187063421,12404130,21737115710,4178,4188,0xd20883486c4367456,0x1b16d9e90afa459,4198,5278,89885222015996627,4170,0xdfb6cef42fe04b51e,23465623636,4185,0x649a9059f10654afa182,
0xae56cf1050ba21514,9281618,4201,4209,4203] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part282 : Refutes moves 0x40100000000000000000000000000 0x11f4344c4300000000000000000000 :=
  finish #[
29018337713,61384345908392,4183,29097514614,14190199,25401447233,4166,4180,4763,25188402475,49627344492046,4166,4195,12869729,4147,
13186247,20544443668,4166,8717143,4181,5319,26359230791,10580053,11509857,4163,0x195c44e90bd4363,12403911,24490361142,25403838894,4181,
4180,4166,23088525622,0x196613e4aa90136,4179,89774138992874581,5641,12784808,0x1be3484fbafd2ca,4180,11075654,11509843,4156,4191,11510424,
0x1b16d9efc9917ab27a54c4652f,5205,47868621595816,11522143,4181,9281607,4211,4209,11465916,0xae9699638962eb26d,4183,93300084669846356,5754,40121300165831,53491951456327,
4146,4138,59435220181743,5423,11515183,11456585,4183,0x1768ec5722fa456,5319,10491079,11509845,23387780295,8749143,4188,4189,
4184,13296839,27234800839,27072098366,23602533897,57753421649064,4153,4195,53835547518140,4163,48098333758759,53484297831724,4183,23549511177,61497770373905,
30027305745,12402758,4149,4167,4987,43871223390420,0x5da5f50a72ba90a9027b,4167,17910039313,4195,4188,4184,4185,59522084217362,0xc33244f51485880fe,
0xa907a909cc8c3d604,4146,4881,0xbd45f4ec5480584a8,4195,4184,12404348,0x17a8bad01a9037c,4173,61508254499706,48026914575445,4157,8749841,4189,4184,
4183,4185,26360128598,0xbab95cf562321037c,4171,26281870857,0x52dcaeb1c1622321560e,4181,10581191,10621600,4181,4183,4188,27233440843,8745624,
48276164449355,4181,9281623,4209,4201,4211,10616939,4192] (by decide +kernel)

private theorem part280 : Refutes moves 0x40100000000000000000000000000 0x11f434444300000000000000000000 :=
  branch 1 0x40100000000000000000000000000 0x11f434444300000000000000000000 91 0x19f434c4c340190040020000000000 (by decide +kernel) part281 part282

private theorem part278 : Refutes moves 0x40100000000000000000000000000 0x11f434444100000000000000000000 :=
  branch 1 0x40100000000000000000000000000 0x11f434444100000000000000000000 81 0x11f634446120000601100400000800 (by decide +kernel) part279 part280

private theorem part276 : Refutes moves 0x40100000000000000000000000000 0x11f414444100000000000000000000 :=
  branch 1 0x40100000000000000000000000000 0x11f414444100000000000000000000 101 0x11fe16455124800000000000000000 (by decide +kernel) part277 part278

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part286 : Refutes moves 0x8140000000004000000000000000 0x1d44b7f4cd55000010004400502008 :=
  finish #[
29062598857,11957442,4164,5314,11392303,27230630998,4181,4166,11514641,44091783196887,4187,17904379401,4155,4185,0x84b0acd9e208bb34b,
4180,4184] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part288 : Refutes moves 0x8140000000000004000000000000 0x1d44b676c974005000010004400000 :=
  finish #[
36318940062115,36166021195276,55520063894370,4178,26320863534,76333623816783144,0xaf7939622593d6602,4201,4169,23552636431,75002229683143965,4159,0x425887b10bbc5d9335fe,4178,4184,
11956309,4204,29063017559,86429700360783372,8740949,24488461822,0xa6bb14badb3933609,12402770,18825225737,8741076,25403392088,4191,4167,4203] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part289 : Refutes moves 0x8140000000000000000000000000 0x1d44b670c954004004000000000000 :=
  finish #[
42031795042026,0x1b18eef34c9468d27170d8a59d,4132,0x1960d9ec2d8b4c2,0xdfcb14d99035851b4,29078021399,12849215,11498346,4160,4187,4181,24492156415,0xcaab154697083d6ea,4165,11522922,
13295701,4168,5647,9569917,9097291,0x1cd2806573d637e,12849257,23434289364,59563328647587,50154363466368,17843827575,4187,4181,4178,4184,
0x17ac81829a90145,5096,0x6bf83094629ec2b674c2,9154870,4178,4184,40465901093509,12402765,4149,4203,4185,27081446925,12850245,13746222,14189544,
78243059472811535,4166,4168,0x1cd2112c358a432,4149,43706204030255,0x6fe367b16f5b341334c2,0x8768716224e6685ff,0x1b115fa57133598,11960408,0x2cfabed88afc4ce174403e1,4141,4171,4205,12850481,
0xd86871621dd44152b,23316857897,61511789216604,12407784,0x1961620548480c5,4169,4171,4164,4166,4168,0x1b116156dd7e67d,4124,61513072673066,28969436671,28978709092,
4141,23373742155,4187,4167,4181,50177981550917,0x16ce312f8c4136e,27233883223,0x8fda2f105b3af252f,11419723,4169,4204,14188869,29061206341,8740939,
4186,47514219595389,59340712674498,4165,0x195cbf620d8836a,23488454977,4184,4187,40167230759107,0x653d8eb1127c2b12267d,29059732787,44005778449455,4201,0xafd75d2b829df9528,0xdf91776217e933206,
4178,4184,4181,23581566248,23312245582,11956309,4148,4204,4164,19758167551,5307,9646725,4187,48185179640906,4171,
12402758,0xc9c6cf2b8fabd4287,23466951875,11485831,4169,4178,0x31065744257f62334122373,36664277550149,4149,5096,40173845554921,25401507930,4175,11075683,4191,
4203,4167,13766745,4134] (by decide +kernel)

private theorem part287 : Refutes moves 0x8140000000000000000000000000 0x1d44b670c954004000000000000000 :=
  branch 1 0x8140000000000000000000000000 0x1d44b670c954004000000000000000 50 0x1d44b676c974005000010004400000 (by decide +kernel) part288 part289

private theorem part285 : Refutes moves 0x8140000000000000000000000000 0x1d44b670c954000000000000000000 :=
  branch 1 0x8140000000000000000000000000 0x1d44b670c954000000000000000000 62 0x1d44b7f4cd55000010004400502008 (by decide +kernel) part286 part287

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part291 : Refutes moves 0x20140000000000000000000000000 0x1ddc958a6154000000000000000000 :=
  finish #[
0xd7f95c1124b4a9604,0xca995d7ede6c41604,9684162,4193,4205,26318632451,5641,29058454151,49298183450703,9155778,4190,4184,4180,5314,14189762,
26320863446,27066110487,0x195362220d21175,10051899,8659031,4165,4175,4171,4166,13213997,26320840098,4193,12248468,11019547,17895580955,
4175,4193,11956311,50159920877870,14188852,0x19536225713c13a,4190,4184,19830960334,4175,4178,4180,28005508143,29060259997,24488968494,
4163,44095426163906,18723668749,4178,4177,0x1cd047e90bd404f,4149,4158,0x1b02819ea441528,26319987638,0xd2159d29e903583b6,4189,57750677644373,11956279,4188,
0xb67cd07d690bd4609,0x6c54417a8d9e90856513,4195,25407427778,0x100b9a44e3687a8bb62042e5a2,4143,0x1792f52c42fb5a1,21529191945,0x1b10bc9ea2fb301,4162,25194976450,4133,4151,9683017,4178,
10616926,4197] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part292 : Refutes moves 0x140000000000000000000000000 0x1fc494004154000000000000000000 :=
  finish #[
90061195550687745,41785733318156,4151,4520,12407208,4159,4193,55671917150523,57753336390850,4159,9134385,53893808160982,12850473,36328246658011,4193,
10510399,4151,4161,4171,4956,0x1882bddae36a0d6,4185,74392794075395355,29062600098,24491218006,17817702470,4178,4179,4180,0x167562e90d884ad,
5641,4298,29088211247,4124,4179,12804393,12853533,4143,4141,4153,36450410435078,0x187162290c3635c,13295818,4179,10510408,
4166,13768201,72308136967061642,4144,12850459,0x40e668064d52c42ca52f,4178,49833503368823,4141,4161,14189184,26318632219,55294705276322,10511635,4156,
12398637,55623118308328,5403,14205928,50159919514573,4178,4164,5096,29061256168,11419730,4162,4190,4183,4192,4204,
28199912411,11969469,11075649,4167,4185,0x1a4230854d8359b,29063516782,12403473,4185,4167,13296401,5538,0x2b592489b95d6229084c4b3,4173,5206,
0xcaeb11484263d5132,0x4c28b1a42131e9927442,4169,4173,4166,4175,0xc46b00126c4521607,28194439374,4185,0xd885fa142908b3370,4166,4188,10616916,4187,4197,
4288,13186353,0x1927268210a7606,11522116,12849251,0x18837f2904ae609,25401009085,4175,0x6c452178015620936455,4187,38201864205030,4166,4178,55766577558803,26236065055,
4152,48336108478679,21744164949,8831077,4205] (by decide +kernel)

private theorem part290 : Refutes moves 0x140000000000000000000000000 0x1dc494004154000000000000000000 :=
  branch 1 0x140000000000000000000000000 0x1dc494004154000000000000000000 113 0x1ddc958a6154000000000000000000 (by decide +kernel) part291 part292

private theorem part284 : Refutes moves 0x140000000000000000000000000 0x1d4494004154000000000000000000 :=
  branch 1 0x140000000000000000000000000 0x1d4494004154000000000000000000 111 0x1d44b670c954000000000000000000 (by decide +kernel) part285 part290

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part295 : Refutes moves 0x2100400000000000000000000000 0x15d44c847180421004000000000000 :=
  finish #[
10520073,51698593829973,49795476923477,4159,4177,0x897163485ea2f7676,4174,20147295417,26244027557,4162,0x6c6881b11486172e82d7,4188,23303820706,98749910756443662,4185,
10616903,4197,4769,25394545730,11957878,25395884676,44541239645374,4138,4158,4188,4148,10409158,0xa523db09e22a2034e,20556570700,12407323,
0x17ab0f5ea2205a2,11075680,4185,4167,0xc1d7a87fd74d2160b,4728,0x183abde90a90455,4185,4173,13767765,53285791634955,4139,22685905528,24488575053,4172,
12849826,44555392549247,0x1a437e65417c318ee1aa334082,4145,11957666,0x1b10f559a22144b,4178,4168,4148,0x17aaf52c42903dd,4167,0xc45cd17d510d214a8,0x1a428851044134f,53829097125494,4148,
4172,50159919526562,0x183af5220b6736a,52027005564082,12869709,4197,4167,4187,0x184f115b3a200cf,10068275,11076123,0x56719a520f51b3a20677,4177,21569273957,4203,
4171,4211,4201,4196] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part297 : Refutes moves 0x80100400000000000000000000000 0x17e44d385102c01004000000000000 :=
  finish #[
26318632457,13194761,53836411544744,8683587,4174,13767874,5083,77818849238353314,4145,4159,45573865600635,53900450104950,12402751,4149,0x1b11107345855d10f690b67455,
11497572,4201,4970,13768203,4158,14655751,21405165179,11330168,12320798,4174,27165254933,13768203,4158,28196173323,28107210807,
4145,4147,9208682,5314,25239180482,61392812266422,4168,0x1afb11620cb152c,4160,28198125668,4158,4185,5096,0x39a1a1204beb6397b2fd5a1,4174,
11957295,61391578231429,25085507190,11437227,4145,4152,4159,5420,55499218187435,4174,25403392064,4185,4173,22685917806,43385188803396,
0x1b10bea50cb025e,10833983,12742722,0x14b99a2c2a90a42bea1dc3d67d,4158,4970,0x1b1cba4fb8c8527,4183,0x183aba62358a67d,40136507413794,4168,0x5e02e983abea22bd4285,13766745,4158,25405186255,
0x57d43b87b48623290455,4191,0x57d12f7a89cd7b2fd60b,4159,4173,10616937,4177,4197] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part298 : Refutes moves 0x100400000000000000000000000 0x1de44c005100401004000000000000 :=
  finish #[
10421878,29972763823,4173,20466062521,12374410,4169,38199987957815,85485406967768587,5096,51684354311103,4192,4204,10592913,4181,4186,
5096,0x16d10f5b3c27442,4769,40703415636968,4181,4201,4186,5096,40755164939785,4186,0x17ab1190d2102fb,14214230,29003772660,4136,25396798632,
4147,26099122840,10616937,4192,4187,42066232984770,40755164939901,4186,0xd880fb7c613b6728c,0x184ed9d05a1a672,4193,0x1b067b6fe4273d9,4748,0xd8d84e3e105dfc217,9680040,
4189,4183,10616937,4192,12402779,4149,4167,18744169557,10617941,4172,0x9ed09cd9efac274c7,21747708102,4158,4188,5096,
13767858,4158,10617285,4192,35449381086169,12399815,13766753,4763,40753296598210,4197,4192,0x187650505a103e8,4161,4181,11509865,
4170,4177,5288,0x21d6fc98784f7d690afa0af,4170,11510869,61392592372603,25405149969,4158,0x309d668325211197d22034f,4172,4187,4167,12871293,61462402814240,
53452967379021,19490751676,0x6f8c4159c84905afa0c2,4191,0x457bd6844bbefaa2167a,91214734232114040,4167,9281627,4203,8831081,4209] (by decide +kernel)

private theorem part296 : Refutes moves 0x100400000000000000000000000 0x15e44c005100401004000000000000 :=
  branch 1 0x100400000000000000000000000 0x15e44c005100401004000000000000 115 0x17e44d385102c01004000000000000 (by decide +kernel) part297 part298

private theorem part294 : Refutes moves 0x100400000000000000000000000 0x15c44c005100401004000000000000 :=
  branch 1 0x100400000000000000000000000 0x15c44c005100401004000000000000 109 0x15d44c847180421004000000000000 (by decide +kernel) part295 part296

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part301 : Refutes moves 0x8101040000000000000000000000 0x17647661d311a50914104000000000 :=
  finish #[
24488908079,0xaf74e2d9e5713335c,4187,47302213960680,0x1bf8311483d452f,4149,4203,5420,0x1956b8657265348,14651438,4838,30007309612,8671323,4169,11510545,
4156,10950262,4730,12403473,4185,4288,61504464175502,4149,17742189384,4175,4169,98870755762066193,41777088886386,4166,4156,
13766724,4158,4170] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part302 : Refutes moves 0x8100040000000000000000000000 0x15647740c110240810004000000000 :=
  finish #[
81359055600358694,28197233513,48286449754897,4167,23574160351,4211,4163,11511062,27118252923,11076897,4173,11076121,0xafa40820d722f9311,4199,4211,
4185,30025949442,4515,11506773,98102533947659349,4168,4169,13766727,4158,17796244304,0xdfc5b4b7499af9532,4199,27234317249,22683095335,4169,
11457842,55772007347506,4169,4199,47300513236713,13308752,4974,23467856516,4209,0xb466d19a101afb60b,4169,4199,4211,17728148999,19707949936,
4181,11334741,36301685531511,4179,4185,13766727,11956286,4188,4180,4204,4856,14635768,5167,24173355793,13304238,
4177,14635093,10974146,11956288,4180,4156,11076432,48228341347152,4987,11076121,12410969,4156,4187,24492160289,5058,
0xadb2d50d0bd4443e8,4175,27209634997,49506220049493,4173,4203,4167,24492594114,4184,61494839686550,30034785583,40419848971329,11477083,4185,4178,
0xb67bea4cd6eae43c2,4141,4199,4211,22327464456,0xac34bf7d5eb3b7362,61391913284673,4181,11075662,24280195508,11494250,4209,21631210257,11509822,4163,
0xbc05e5486fab671b4,30028207042,14636008,13768316,61497769620241,97873941505218163,4211,4199,11509833,10973279,4160,12849260,4152,4142] (by decide +kernel)

private theorem part300 : Refutes moves 0x8100040000000000000000000000 0x15647640c110240810004000000000 :=
  branch 1 0x8100040000000000000000000000 0x15647640c110240810004000000000 96 0x17647661d311a50914104000000000 (by decide +kernel) part301 part302

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part304 : Refutes moves 0x80100040000000000000000000000 0x17e446794110068010004000000000 :=
  finish #[
97324183948288880,81792653425878642,4177,27232109438,4167,14665007,28192441167,22252852532,10457158,11509797,26361021520,30006310196,11523157,4181,11510054,
4156,4166,13766727,4158,5398,0x1bf29c734c46285,26361914210,28198125673,21513770183,13767410,27233904034,36465735976222,55664372680206,4191,23491235929,
4195,4201,4181,4167,0x577afaa437d538b6752f,4156,4204,0x6fdc414ef7d5ea5213c2,14636226,61448984155431,9622149,4169,11509830,4191,0x17a97e2c044167c,
15111798,55812984685745,4169,4174,0xd82beabf5ec2fa369,4163,13767765,29976957801,11956280,4196,4180,39252591796735,72253969762222682,12403473,10502215,
4169,13284988,0xd8e956796c5bd4513,27232989255,41278882362451,13763979,26997674033,13766985,27115549001,25209880905,4174,4204,12419502,4163,4199,
4181,4180,4881,0x1be59a1ec204149,4199,0x195c3e9a0d82676,14164930,12276142,4163,11956309,59414978917654,41328602518351,27024626545,24488931397,4178,
4160,4196,13767769,47854193145468,4173,98006799928190008,0x8c85d12b97b52167b,9622609,4163,4181,0x6fabd859d28c645211ae,0x570bb2a437d532bd616d,9573663,4163,11076478,
4167,10973261,4160,12849252,4152,10616878,4197,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part305 : Refutes moves 0x100040000000000000000000000 0x1de446404110040010004000000000 :=
  finish #[
12850152,0x193ad9e20a1252f,4178,12849811,4755,0xbd626d105e83d852a,4189,4181,0x43b50a424beca2947455,4204,4199,41634133971145,12850594,53900558237998,4183,
11509822,0xcb396110657147513,4987,11510978,0xdfb28f2b97d441604,44127955788667,4158,23348585107,4171,4204,4178,4183,0xdfc682f5220b67211,83569763885761161,0x1bf97edea2df451,
11514961,4183,4171,4199,4745,19929220290,5191,5209,25403830916,4169,4183,4171,4199,0x1882822fe04a6e9,0xbd4cd17f290c411c8,
0xc40095269ea441534,0x1cd17f1093d44c2,0x84a935106c32fb67d,4164,4204,4183,11509863,4184,4170,10616885,4197,4177,0x178e129ea2fa130,4535,14636226,
48226496372939,4166,4201,4187,21344633945,13276354,27275362506,22685917269,4191,4535,44040230932919,10616894,4187,0x32cc252ef4cb7c54844108f,0xc41066a4110521370,
53983555166410,4163,9281598,4201,8831077,4209] (by decide +kernel)

private theorem part303 : Refutes moves 0x100040000000000000000000000 0x15e446404110040010004000000000 :=
  branch 1 0x100040000000000000000000000 0x15e446404110040010004000000000 115 0x17e446794110068010004000000000 (by decide +kernel) part304 part305

private theorem part299 : Refutes moves 0x100000000000000000000000000 0x154444404100000000000000000000 :=
  branch 2485 0x100040000000000000000000000 0x156446404110040010004000000000 111 0x15647640c110240810004000000000 (by decide +kernel) part300 part303

private theorem part293 : Refutes moves 0x100000000000000000000000000 0x154444004100000000000000000000 :=
  branch 1 0x100000000000000000000000000 0x154444004100000000000000000000 94 0x15c44c005100401004000000000000 (by decide +kernel) part294 part299

private theorem part283 : Refutes moves 0x100000000000000000000000000 0x154404004100000000000000000000 :=
  branch 1 0x100000000000000000000000000 0x154404004100000000000000000000 102 0x1d4494004154000000000000000000 (by decide +kernel) part284 part293

private theorem part275 : Refutes moves 0x100000000000000000000000000 0x114404004100000000000000000000 :=
  branch 1 0x100000000000000000000000000 0x114404004100000000000000000000 114 0x11f414444100000000000000000000 (by decide +kernel) part276 part283

private theorem part261 : Refutes moves 0x100000000000000000000000000 0x114004004100000000000000000000 :=
  branch 1 0x100000000000000000000000000 0x114004004100000000000000000000 106 0x195244005500000000000000000000 (by decide +kernel) part262 part275

private theorem part239 : Refutes moves 0x100000000000000000000000000 0x114004000100000000000000000000 :=
  branch 1 0x100000000000000000000000000 0x114004000100000000000000000000 86 0x114c04800100104000100004000000 (by decide +kernel) part240 part261

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part310 : Refutes moves 0x40400100100000000000000000000 0x1173df615051541440540500100100 :=
  finish #[
5632,47288992044320,4171,4517,24497776253,11076417,22683993391,4181,4175,4185,4157,5646,13317636,4185,59361512146441,
55773736269312,93278249019426095,4183,9281611,4211,4207,97940635392934673,0x40dacc52096d6f924520,4163,13313551,95151301478991155,45556627443779,4146,4517,13317636,
4185,11838881,13313221,9998379,0x1beab321f2e65a0,13226024,0x1a2cb00c4ca760e,55773174199582,22548841988,12419145,9281603,4203,4211,4207,57301094322602,
14635302,9998765,13766746,4158,5632,0x193f63253929311,4171,23409587026,89883432530526730,14635064,24380851830,4175,0xcae588b30fb3522dc,0x5665f56b97e21f44427b,4169,
0x195c672fa92c4bf,4171,4165,47280667206959,0xc463ed252574b2603,14204985,5423,29096174439,9617509,4171,14636544,5750,22238877184,28195721264,9281626,
4209,4203,11509871,4191,4177,4170] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part312 : Refutes moves 0x40000100100000100000000000000 0x10578f01f014541010540100100100 :=
  finish #[
0x195d7d49385d311,29067748046,4814,0x1afe7dac4c3a173,4189,55510712848993,4158,14635062,0x4eb8a87aa96c205f55a2,40418071471625,0x1bea3c898262609,0x5d791e93f2b8982e65a2,4171,0x61d57c2537d6573d5600,4177,
4150,4190,4157,14635740,0xdf6be508ac4d214c1,11075634,0x1bea4a64a2fa5a2,8777809,4191,4205,23086695939,12407787,4177,9622285,57712600839560,
4157,4163,13296706,25368794387,4154,4635,51546878333467,12363274,4168,4177,4159,14185298,53681782854482,4154,0x1b12ed6c1191524,
4626,19733869175,0xbaf5884c2fac92277,10100791,4211,4171,4163,14635538,5640,61391903049216,4165,11509832,4177,4205,13766758,
4318,13767987,61395504981267,4179,27039605165,4177,10031995,0xdf5a426457d0da2dc,8781939,4203,4205,4318,55285600269942,4159,0x195c96e495f56e7,
12383507,4189,0xbaf3237d64925f311,12383507,9597021,4160,4154,43729832768787,61386874032759,4146,23409141024,4153,93229611979309788,9621931,4163,
4169,29974139612,9622289,4196,28178579704,26998404514,27263137283,4136,76407829498111251,11011049,9633853,4169,17986068547,4211,4203,
10616941,4187,4197,4207] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part313 : Refutes moves 0x40000100100000000000000000000 0x10578f015010540100540100100100 :=
  finish #[
46326982636370,5632,39744236078602,4183,4384,42368087307562,4196,19365815469,4933,13275525,4196,59447820710317,4145,4169,27191472508,
0x179f2a47dd8e345,12386413,4153,4189,4181,4163,0x805b1cb6a574a43c5,45615104856358,4175,0xa7c9496052f8403cd,4163,14636559,17721648642,4157,18498524790,
4150,4198,13297156,0x1950786c1cae609,29978321626,4153,4205,59413085324123,59515271139757,4174,14635538,29973164550,4148,4156,13766710,
4134,4170,92805522017945085,0xabeb115f2fad21179,4170,4625,27230642550,4163,4157,18503127931,11379473,4209,0x1bea9344eada430,37886555481718,4143,
9561718,92793818678534929,4177,4163,4157,46455146804527,4196,4191,0x1cd3276fad8d27b,27091740174,4161,23407772279,0x8774be644962fa367,4163,4177,
55774036952585,98870795602601486,8769651,4203,0xd884be1764e927367,4955,0xe694b3484c893033f,4169,29977334046,4163,10802806,22272987363,4196,0x5b009d4be4c0300da529,4211,
4203,10616941,4187,4207,12849253] (by decide +kernel)

private theorem part311 : Refutes moves 0x40000100100000000000000000000 0x10578f015010540000540100100100 :=
  branch 1 0x40000100100000000000000000000 0x10578f015010540000540100100100 56 0x10578f01f014541010540100100100 (by decide +kernel) part312 part313

private theorem part309 : Refutes moves 0x40000100100000000000000000000 0x10538f015010540000540100100100 :=
  branch 1 0x40000100100000000000000000000 0x10538f015010540000540100100100 106 0x1173df615051541440540500100100 (by decide +kernel) part310 part311

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part315 : Refutes moves 0x50000100000000000000000000000 0x1a57d5011101450000100000000000 :=
  finish #[
12838179,55569659593922,4135,29063042334,27232043429,4175,4163,0x1b111065712c27b,55863637448098,0x17a71065712c529,4171,4175,50106469581985,29105460530,13247679,
9617481,11509829,4156,4177,4722,5317,26319971603,4157,0x195d10659ae44c5,4141,23450997951,89562942171747519,4171,4178,4183,
55768375071938,4722,57658143909373,19699569511,4171,4183,61393727947378,0x188cbeec412c514,4183,4727,11506533,11509833,10616941,4182,4187,
4177,4197,5426,27259494827,4157,0x3264760fbb052bec444160e,4142,61391907198029,9618727,11509829,12402762,8770173,5640,27088032067,12849233,
5750,9115042,4158,4156,43887438333223,59602876686750,23581586735,4169,4178,4988,11457839,8769590,4195,4190,29973704898,
5206,25396798429,4207,4177,12407213,10617922,8659134,4169,12402764,4158,27239027571,0x8ec92e424fe4af58f,53981667788187,4182,25403392111,
4179,4167,4185,29976511682,0xcabb0f621ea1292ca,4171,26291119291,23508894123,98603449359249820,4157,4171,4190,74679952778176006,0x195d1057d290455,4167,
4987,11514747,4190,12404233,53538865717442,11075660,8777799,4193,9281631,4205,4197,4203] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part318 : Refutes moves 0x40000104001000000000000000000 0x1377d5a70590540450104145001010 :=
  finish #[
80420624833037834,23469184048,0xa885a3622fad8936e,4146,4171,0x1a404c21043e3e3,41605256500197,55469463802853,4190,4197,4169,61396520345848,9622394,4169,29063066922,
0xdfb5b52a5ae1f651e,4145,29060212020,18397745406,14193952,4187,59523912930612,4190,4197,11509875,4177,4163,5205,55469470307195,0x1beb2bdea20b1f6,
55464841688585,9281630,4211,0xafa7a8bec2f8621f6,4195,4197,4203] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part320 : Refutes moves 0x40020100001000000000000000000 0x11d7c7a15d10d440301c0045002010 :=
  finish #[
57566330368859,22278025466,97746390397776967,8697118,4175,4181,14635075,25208767768,55292811698549,0x1bf697efac41043,4132,30003467011,5642,26293478922,4169,
4175,47360516560394,55497374512652,4141,19517280323,4146,10552956,12850456,59515498112517,0xbd0ccc841e7c244c2,4163,10462720,5415,44265326634178,4175,
4163,4187,4171,4154,55787470697865,17794311331,4154,59352115082520,14176458,30024036767,4187,4175,53906047635523,12402762,4203] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part321 : Refutes moves 0x40000100001000000000000000000 0x1157a5a14510540010100045000010 :=
  finish #[
30951358876,59521020646917,26318184519,8770978,4193,47700455171368,27165294986,47703203824834,4175,13766741,0xd8cb134842eafb527,4190,22688174304,0xc9423d2924e1306ea,75411385649967429,
4171,12402782,4167,4185,0xc9cb112a21a43e271,27008706057,0xc41a4327025afa6e7,4156,4629,0x64e5fcb172a9a635c37b,4175,4145,4177,28198572667,24266105373,
0x1b11485b54aa528,4175,11505729,4211,17798038139,0x9d7882818fd20b606,4161,55667863110264,0xd88a43101aa2fb2e5,4211,48298119218141,4167,4185,76405780245952005,13181300,
12797446,4175,4129,12849888,4142,14661026,4134,53904266994194,4198,0x649585b10be9483d4277,4167,5177,59399033066550,12346220,11509835,
4163,4753,14664793,25403708937,4169,8786014,9281636,4211,4205,4203,4619,0x4c5666963614fb4923cb,61496756806491,4153,9621588,
0x43c66678eb7cfb49d4c2,5405,19733066943,4169,57751443764746,5750,59520208757808,19348051240,10489913,11456557,11505725,4171,4183,4211,0xca2b10b7620a062e0,
51391101436529,47703199962297,12402743,4185,17995728393,4198,8770168,5640,12382430,4190,51940251485708,4167,4185,0x1bf7106fad21459,25285952699,
4185,0x6105889250d1480621ae,9281636,4205,4209,10616939,4187,4207] (by decide +kernel)

private theorem part319 : Refutes moves 0x40000100001000000000000000000 0x115785a14510540010100045000010 :=
  branch 1 0x40000100001000000000000000000 0x115785a14510540010100045000010 101 0x11d7c7a15d10d440301c0045002010 (by decide +kernel) part320 part321

private theorem part317 : Refutes moves 0x40000100001000000000000000000 0x115785a10510540010100045000010 :=
  branch 1 0x40000100001000000000000000000 0x115785a10510540010100045000010 86 0x1377d5a70590540450104145001010 (by decide +kernel) part318 part319

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part324 : Refutes moves 0x40800100000000100000000000000 0x13d39503a125441810104000100120 :=
  finish #[
72738261945583107,14636307,5750,29011669842,4130,55296652784247,11837507,4175,4143,5422,0xd825a37d5a54a2588,9623043,14189843,0xb4abeb622495825a1,9597037,
4160,4163,4175,4169,0xc926d4d6ac404a133,11343152,8701014,52045093107324,49931981464767,4172,4169,4175,11510066,4163,4205,
13766737,4619,0x9f631528ec2d82598,11837524,13181559,28198905350,0x4fbe66b17111a5041189,4172,59400623673874,4187,4178,4169,28195292445,9569801,59513488585685,
4157,29060194625,10616871,4187,40360079237653,4198,4177,22470492701,98890655534495128,0xd886a8f0e53afa21d,46019571524581,4167,4161,4175,97678237804660104,
4187,14189964,29978297619,12346653,4172,4198,0x19657f28851c609,19699574045,4198,4177,0xd17beab1058d88603,0x37d6fdd8875f60a53aed272,4143,4402,29061206689,
14635213,59519301853389,4193,0xdf5b10a22232ed0cd,11509835,4205,4198,4177,24249337343,28055987833,4177,0x1cd2be8f8a015fd,13295691,4146,4157,
5311,11510975,4177,59515631502497,59513620546964,4191,10937543,4157,4193,12346671,11510433,51954444952994,4180,11477073,11419723,
4169,4190,4211,4197] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part325 : Refutes moves 0x40000100000000100000000000000 0x115b8501a105441010100000100100 :=
  finish #[
0xdf5a2f2ac93d21600,23329100999,4197,8770067,59469514031966,11392165,9605531,4159,14188625,0x32bc24bd5a3e2c50320b44b,4161,4211,4186,5423,28975432353,
59569686827538,4198,4177,17965810853,11514078,4169,59347482772546,4161,4211,8660167,14188766,25093451998,4169,10551943,4161,
11075699,12870040,26361017509,4211,39932421870555,0x1bec8408703c4c3,17737074082,4207,4161,4169,4728,28179498059,23274906273,4190,11075699,
12402771,4158,4167,4185,0x1b05620984a2532,61394670777736,38203645843068,4202,11806101,11043926,11018993,4153,4165,4171,4177,
9114030,5422,27164026492,9623046,4196,11509839,4198,28198125635,0x655d88b16da2fabd460a,0x1691621ea929455,4177,23584391583,53781214471020,4155,4190,
4320,8778385,5205,22685885292,4155,4190,4185,23449281621,4177,4191,5638,13297158,4179,9569916,4153,
12404230,11968920,4153,24463869013,4179,4167,59522925335159,55771359117928,4179,0xd0bb1d2b864220609,4172,4187,21743673874,0x733192bf696ec73d8520644312fa0ba,4191,
4198,4743,21525566749,4195,11272849,51696746976559,11509859,0xc9442160a232fa676,26359235451,4202,4187,13766737,11449211,0x1782bea4e220345,4202,
4753,4986,51855239545489,4202,4177,4171,95074723479750146,29061259937,85376024625308041,13295691,48281760449839,4169,13766750,12402726,9281625,
4211,4207,4197,4205] (by decide +kernel)

private theorem part323 : Refutes moves 0x40000100000000100000000000000 0x11538501a105441010100000100100 :=
  branch 1 0x40000100000000100000000000000 0x11538501a105441010100000100100 107 0x13d39503a125441810104000100120 (by decide +kernel) part324 part325

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part326 : Refutes moves 0x40000100000000000000000000000 0x115385010101440100100000000000 :=
  finish #[
0x1944f54882d1430,11456790,4197,36391269410312,77306482750628238,5204,24313176955,4180,61441604609221,27091697737,4129,4195,14635075,26044061187,29010875809,
27232354379,11511070,4163,27232384515,0x399ac19f72592b8c8d21676,11511092,4205,12849219,4202,4182,47289049928312,53395815728759,4211,40292904604843,19734913916,
11509854,11510865,13296937,61505612522585,4177,44540270879611,4202,9281635,4207,4205,4835,47374892335500,12730433,55378933948842,4177,
95143135548519290,4190,0xb4e030841da3d8341,23390557273,4183,48281816536117,48268306551436,4172,4202,4881,51957430461954,55690008699306,22689042862,0x188c4742ebd8604,10616925,
4172,4202,4177,5319,55689135326163,27232547924,4190,4183,10552623,22686770594,10616911,9281622,4211,4209,4207,
4625,0x16917f24eafa60f,4163,74757932262163528,4171,4753,53983584436753,4177,43288945796621,9606012,8777803,4195,0xb5e21727576a0b5fd,0x195c96c9857c602,5423,
0x1afe17c8eafb37a,4183,10616907,12849233,4172,4202,11379121,40416049816747,12849235,47700259377526,48295103971727,4177,4171,0x275c82a105a617e20df5179,29972506122,
29084549393,11509866,26309800350,11448395,11075678,4191,27181254265,12870635,22683689041,4207,12402801,4149,4167,11972715] (by decide +kernel)

private theorem part322 : Refutes moves 0x40000100000000000000000000000 0x115385010101440000100000000000 :=
  branch 1 0x40000100000000000000000000000 0x115385010101440000100000000000 56 0x11538501a105441010100000100100 (by decide +kernel) part323 part326

private theorem part316 : Refutes moves 0x40000100000000000000000000000 0x115385010100440000100000000000 :=
  branch 1 0x40000100000000000000000000000 0x115385010100440000100000000000 72 0x115785a10510540010100045000010 (by decide +kernel) part317 part322

private theorem part314 : Refutes moves 0x40000100000000000000000000000 0x105385010100440000100000000000 :=
  branch 1 0x40000100000000000000000000000 0x105385010100440000100000000000 112 0x1a57d5011101450000100000000000 (by decide +kernel) part315 part316

private theorem part308 : Refutes moves 0x40000100000000000000000000000 0x105385010000440000100000000000 :=
  branch 1 0x40000100000000000000000000000 0x105385010000440000100000000000 80 0x10538f015010540000540100100100 (by decide +kernel) part309 part314

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part330 : Refutes moves 0x20400100100000000000000000000 0x1d799c204045921440920500100100 :=
  finish #[
0x1b137dd6fd8c67d,0x1b197f16f99060a,4165,47411173941747,5647,14664989,30037042696,14643245,12375458,4160,14151759,28197151809,27171919370,4177,4171,
4165,4183,0x1a4310173581179,28200386934,0x193f439e69381ec,57750670172534,4171,4183,28199937539,29001495970,29004326306,11501673,4165,4179,5757,
55837195133408,23382106199,4147,4175,4207,0xd21beaf001e1293e7,0x1beb48653ae3122,0x1792a0a233d6122,29991952674,4175,0x1beab9d7d1235a2,0xdf5a437dd7d1381f0,4201,4198,4177,
4207,13222309,18281817374,11519261,4179,4207,28199019367,13767527,0x1cd30897e4ae4c7,4179,14151791,0x188d2cec45f758b,0x1b10a32f9d2152a,55686275778164,4179,
11509839,4163,4177,4967,20520588247,0xdf34cf095734ae1e0,4124,4179,23561037315,11445414,4147,0x5da582beb29d752e65a2,4185,4207,5645,
11428584,4171,9668109,11509871,4177,88544472679273999,48253868336424,4185,59622012011334,57358337311558,14188605,57733541602818,4165,51601236091718,93004482280457523,
11042867,4175,19677533051,4198,26218852433,4160,4180,4190,4184] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part332 : Refutes moves 0x20400100000004000000000000000 0x1d793c605561920500140100044820 :=
  finish #[
14664649,14161533,4179,20524308093,53706764649993,4181,5629,10552842,4181,19674411898,4162,4185,4183,23385326170,14160747,
4179,11445775,4964,4753,5634,11445762,4147,4179,10511663,4151,4181,22566634119,4177,4201,4183,
4207,25440085158,23583876262,4147,0x185cda176a103b7,4201,51685951726443,26086008333,4141,4413,21569274694,4201,4171,49765755618826,59584946517629,
24480121484,4201,11509835,4163,4177,55518210916860,0xcae9532c978af86ea,4193,98816524458513245,0x6fad8979f2757d17b30d,13226873,8696662,4177,4179,12775499,
11972682,4160,4184] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part333 : Refutes moves 0x20400100000000000000000000000 0x1d791c204141824400100000000000 :=
  finish #[
14665122,30034691471,4141,61515865187043,0x179a4925736b588,4184,4160,21612057467,11961537,4173,4936,0x37df333c958eb74553681a1,4157,4958,30032847147,
23147601975,97854583467271035,4181,4139,4147,4171,49588337926998,12870523,53917731161603,4171,0x2be80faddb0511a90b6b52f,4160,0x1a42daec0ae74c7,47960032719710,0x1b1d4856e9385a1,
4198,4183,0x5b5d81270841752fc37b,4175,4186,4193,4207,9192300,40297810392044,23575519658,4181,4623,5100,44262686147662,4164,
4157,0xafa4cf7d5792f9441,4162,4190,4171,13296684,4950,0x196464a543d84c7,4181,4163,0x6fb588beb7de90b6b356,51374017709119,4180,0xd7f6d6be9732f9217,4178,
4192,5647,0xd8ebef486572fa60a,29113398252,4152,4184,11972935,11449175,4190,4183,27232543824,22500918231,4183,0xcaeb0511a90b6b4a2,4160,
45757337441792,4413,24525673192,50228580262207,4190,4199,4183,29003404268,24522065410,4171,4201,4413,0x23eafbcaeb189a253df6603,11518055,11444300,
4186,4175,4193,12402799,4185] (by decide +kernel)

private theorem part331 : Refutes moves 0x20400100000000000000000000000 0x1d791c204141820400100000000000 :=
  branch 1 0x20400100000000000000000000000 0x1d791c204141820400100000000000 62 0x1d793c605561920500140100044820 (by decide +kernel) part332 part333

private theorem part329 : Refutes moves 0x20400100000000000000000000000 0x1d791c204041820400100000000000 :=
  branch 1 0x20400100000000000000000000000 0x1d791c204041820400100000000000 80 0x1d799c204045921440920500100100 (by decide +kernel) part330 part331

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part336 : Refutes moves 0x8400110000000000000000000000 0x17796f0c5443528484111100000000 :=
  finish #[
55329234101666,55777688142250,28195328845,29108753711,4167,4173,4171,0xcae78127e59521603,59450556814621,0x64fcaeb05485e6bd6515,4142,4160,12374442,13767968,12411183,
17645266003,40294997533774,4167,4162,4160,12322210,9606451,10551377,4211,4181,4171,4156,29991436613,29995073861,55658406367409,
4148,20607799352,90798242322695800,36055250056008,14205672,13295658,4179,29071372810,10568213,13766725,23216657224,0xc9c7a548533d8c60a,18812166186,4179,21643826263,
19676193425,5423,0x1bef2bafe4a7145,4172,25418699289,23407312965,4199,4211,4171,4183,4190,10568787,39257081102993,30034658829,4165,
5629,28961931921,21645541461,97274006097924840,9606209,4165,19674411898,4176,4162,4183,4211,4522,61427961860592,0x807b1327d33acc16f,4138,
12322312,20219019400,4139,42133097227552,29957898297,4165,4175,10568764,4728,23523836330,23565763644,4196,4211,12402763,13766736,
4158,80596545963271586,12411751,4183,0x17ad2c6503d4295,4176,14161199,45752940873007,4175,29001049391,13295941,29002543530,4171,12402803,11075664,
4191,4179,4167,4185] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part337 : Refutes moves 0x8400100000000000000000000000 0x17716d094443008400100000000000 :=
  finish #[
13767527,11510181,4163,0x1be747efad2134d,5750,53424994521568,4134,11322010,10909090,9356128,29975015805,80467450479645536,8527922,4139,4142,
4134,4138,11510631,4177,51602167649147,14635434,52061397946561,4175,26051080261,4160,4190,10543188,0x8ec0f5485e0348674,14648249,23328827000,
29977874463,12322425,4138,18258068113,4161,4171,28196312149,0xdf3beabc90cad8596,4171,4185,0xd215e499d7a2fa455,4177,0x195c62690afa0c8,57748654179631,0x8761deb3efac25a42132572fa3d1,
11075644,4185,0x17817d690a100a3,0xd217817d4c733e2e8,11509819,39983900500373,0x5083c0b02f517d2906e7,4167,4185,10909090,5753,9356920,17571124856,11300914,25234563095,
10604603,11510430,10543185,4189,4199,4179,0x19637d5eb4a0598,52030578201906,4190,47409311318219,4986,23508902554,4165,55720718959690,0x195cbad0c21d311,
4189,4179,4199,24296096138,4505,0x1bf81248c2903d7,4167,4175,5189,0x1bee63a4aca020a,13766731,0x2d380287bb0ebca503c4093,18829415240,11477514,85895282513036706,
10625109,4190,4175,10543193,11509863,4163,11972703,4160,4176] (by decide +kernel)

private theorem part335 : Refutes moves 0x8400100000000000000000000000 0x17716d084443008400100000000000 :=
  branch 1 0x8400100000000000000000000000 0x17716d084443008400100000000000 88 0x17796f0c5443528484111100000000 (by decide +kernel) part336 part337

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part338 : Refutes moves 0x400100000000000000000000000 0x17f10c004041000400100000000000 :=
  finish #[
13767088,14189767,13665479,19597029449,0x17a0b8e90a14215,4175,4185,0x39a4502f50614862358225d,86065984489457161,4171,28199018655,51912317376234,0x3622c73cdccc5de5752112e,4158,53989203908111,
13296709,0x195cb9e232f5445,4172,9629796,4177,4189,4201,38630396719521,13296277,13296360,0x6fe3b542899e570c8600,11444327,4196,4175,5634,
0x6fe58e4284817aafc60e,12402767,51961976652437,4197,4167,4185,4179,61356657795816,59399032190255,13272044,4173,4185,30034261513,21635461992,4192,
52094868509104,13272350,4151,4185,11490601,5757,76430667373896789,0xcb10f864a235fc17c,27256825353,4185,4201,12238935,0xdf3962f517aa134c7,4169,11501671,
4175,4189,0x8044cf7de909e116e,11974050,14635072,23301411426,13767961,4146,24524371247,11804736,61394690421594,61333295989233,4145,29020128559,14647585,
24521547825,4155,4147,4151,0x8775d560a90b6b60e,11502454,10563660,4189,13272044,0x36073334a7a8dae572904a6,4203,5417,11518281,10625131,4189,
4185,29961098325,0xe6621d2a6fe5885a2,57754353746438,4167,0x985a42f50642fc299,4175,4179,0x1ccc4821ab6b60e,5100,0x37f1ea2e72f6dae1fc43149,4164,4144,55686331675733,53934951600418,
4199,4175,4180,0x1bef485e24b34c4,13297268,55830175736652,0x192b2a56604c4b0,9629775,4180,4171,24525702447,24525279653,9999992,27231617070,4169,
0xbc7bf84bd0ea224c7,4180,4199,19726525076,61506476471817,4144,72189383361074245,0x5e234c6d72bac421d368,4199,23416619673,4167,4185,11518838,4175,11509867,
4198,4177,4170,8831064] (by decide +kernel)

private theorem part334 : Refutes moves 0x400100000000000000000000000 0x17710c004041000400100000000000 :=
  branch 1 0x400100000000000000000000000 0x17710c004041000400100000000000 111 0x17716d084443008400100000000000 (by decide +kernel) part335 part338

private theorem part328 : Refutes moves 0x400100000000000000000000000 0x15710c004041000400100000000000 :=
  branch 1 0x400100000000000000000000000 0x15710c004041000400100000000000 113 0x1d791c204041820400100000000000 (by decide +kernel) part329 part334

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part341 : Refutes moves 0x80040100000000000000000000000 0x17d516468404290040100000000000 :=
  finish #[
11879127,20473111154,38460405129627,4151,5069,24328171724,4175,4172,14188863,4134,4173,12858550,5205,0xa5e842f51a944617d,10616883,
4182,5069,49797077795684,5292,0x917886dacf8b6a2a1,12402751,12869712,11075675,4173,4167,55842797339951,12404015,11912147,53937602430237,4187,
11075660,4191,0x193a5bdea5210f8,28197155481,29061268565,4175,4179,14189653,39620169532226,55691837338265,4151,4179,4881,12358297,10616905,
4187,4769,0x195d2a2c416fa437dd102f8205,11972691,12849224,4192,13297154,10605876,12402776,29087764964,0x886b177f290d8817c,0x362efe0108836211036b174,4192,5207,42135042483718,
27230577961,4168,13275184,14665121,0xbc4a117f210b6b606,4192,55668904727532,21723906093,4199,4174,4184,14189986,55485612340745,4184,0x1842daec43d43b6,
4149,0x360414e66842dadea2903b5,4179,52026769790260,0x3274bdd8d7a8dad6d290609,12869727,4187,4167,4197,77584347666977877,17821775136,9032098,27079152262,26302754888,4154,
4174,0xca740b7edb5b35455,5757,55468447781383,4155,0xa0595110e10b6b603,4152,21520785826,4169,10616910,4192,5205,11076896,0x17a8d72235fc528,0x1bf9621b5a201ae,
4192,4177,21602844773,4199,4175,4180,4195,4205] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part343 : Refutes moves 0x20040100000000000000000000000 0x1ddd07086404830040100000000000 :=
  finish #[
37704457446450,0x17777f257441604,27229603453,4144,4142,51436899099482,28198572925,0x2ea290c4195ca317e13c60f,4190,39713694983450,4147,4189,12402767,14214539,0x26140444140d4856ccb22d0,
4175,9876176,23560135976,11427916,72363399849447919,26317186569,4201,0x16b163976af4528,12402749,4176,4185,77246533339743746,52030646650131,4195,12374646,
4169,5100,0x1a4360f332d8430,0xbafa4360f333cd359,4151,12403692,27173728336,4175,4168,9683386,4190,4184,57747799716920,0x1b0324b33282122,25262122040,
4147,79026874793342227,4190,4184,0x1783999eaad859b,0x9fba42b7c9e4ae429,12869726,4157,30034227836,23347619015,4201,5634,14189854,26134097971,4184,
23446971908,0x6c680567c02ac12f9183,89246264702559404,4201,4171,26135421416,4743,74075616453243970,4168,0xc2b7827ee572ed094,4190,4171,4157,55792218178158,26362806919,
53936481927613,53355376567492,4157,4190,13766744,12402726,4158,10616912,4177,4197] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part344 : Refutes moves 0x40100000000000000000000000 0x1fd506000404010040100000000000 :=
  finish #[
17696482065,0x2f52f9d21b10f057e3d560c,4175,59568114295977,28198122186,0x1b10f4d7e04b0c8,4172,12759119,49688468902747,0x188c132540bc141,0xca4335119423d42e5,4203,4167,13295806,18660283476,
4175,26218868808,4154,4180,0x1b1a7fc93cae5a2,5302,90041713578140854,13296834,9143275,4165,4163,11386943,4161,13767542,36483880534212,
11972697,4176,5316,23330243767,88653719466967781,4147,4141,59566812198050,4179,11973716,4168,55291708204195,0x1b10cd56c3542e5,0xb54b1762210af45a2,4190,
4199,11973716,4168,0x1b11085dd2f4455,11969469,11075649,4167,4185,11076693,0xcad88c9ae1ac43456,11972676,4743,0x83106af517dc3f35b,4190,0x17a71188ec3f122,
19575104588,0x1924f51e0bd3360,11972707,4176,4168,18809381845,11973483,4168,14189871,59519937623343,11972671,0x195cb9a15c43609,4164,4190,5316,
0xc217a962257b6b439,12869712,13766727,10616870,4182,4187,4197,8831072] (by decide +kernel)

private theorem part342 : Refutes moves 0x40100000000000000000000000 0x1dd506000404010040100000000000 :=
  branch 1 0x40100000000000000000000000 0x1dd506000404010040100000000000 113 0x1ddd07086404830040100000000000 (by decide +kernel) part343 part344

private theorem part340 : Refutes moves 0x40100000000000000000000000 0x15d506000404010040100000000000 :=
  branch 1 0x40100000000000000000000000 0x15d506000404010040100000000000 115 0x17d516468404290040100000000000 (by decide +kernel) part341 part342

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part347 : Refutes moves 0x10000104000000000000000000000 0x1655dc421141011010104104000000 :=
  finish #[
4722,5629,29973705924,14635200,85411226167501224,4175,4167,4169,9643530,9175649,19660305711,24380851399,4177,23583445063,4178,
4192,4183,97731244562298377,0x8992c710efacae4a2,4520,18811278639,4177,4166,4150,0x621df6b1049efaae417c,51851323856502,4177,4988,29063943798,5641,
53406921225847,10469463,11399223,8769590,4201,4192,0xdf57aab7ef91f160a,26158711973,8769623,0x195c44657c464c4,55792193458715,29974048958,92664575429981464,4150,0x195d7d49919a0ba,
23273124062,4169,4192,4162,25403392087,4179,4167,4203,0x17ac4cac420f219,5205,29062152391,0x1b1d2bd0a29067b,4191,0x17a883d482e460f,4155,
13296727,0x487aeb41ea425705f60c,9281631,4201,4197,4203,8778155,0x1b104a97d0da676,4207,29061260373,82555258928378203,29974655044,4155,14636228,29974697156,
4175,8778839,0x8fb88c1817d0da179,4207,4203,29978297429,0xd8e364a41ea2fa52f,21720342623,4179,4189,4184,4205] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part349 : Refutes moves 0x10000500000000000000000000000 0x1c5dd5245011110005500000000000 :=
  finish #[
17747707510,0x1bea10d5f58b606,4157,8685053,29060825286,4167,46458784927949,4184,4179,5748,12403473,13766727,4158,14188738,21551551575,
4177,0x1be7486fabca27d,8688042,4183,8655633,4167,0x1beb6242fa90525,17979908751,4177,4205,4191,29038724182,5642,29087322521,10543185,
14635091,14140502,59505776764087,4156,8700559,4179,0x1af82c5483d4456,13766727,12849214,4152,4162,13767874,44232917681785,30032470559,11432011,
4165,0x6fe2f15f948620bd4352,4185,82836953844663571,8782696,4205,29975626448,29974578594,12849884,14184484,4122,21136709026,45467751646393,11415635,4154,
29069640077,59494420304761,4162,11077132,12402801,4167,29983409103,11076470,0x5d7a68840a41ab43e676,4159,4149,0x5483d4beb48530c41376,46460686008975,4154,4161,
17986069348,4201,10616941,4187,4197,4207] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part350 : Refutes moves 0x10000100000000000000000000000 0x145554405001010000100000000000 :=
  finish #[
53903110631932,27255797149,4166,0xd218872b8ffa90357,8770321,4192,4185,0x192e84c2eafa1e4,0x1932b59483d4677,0xa095f4be5e4bd2219,4192,22684955515,23565800866,47669752432034,46455165411755,
10604623,4179,4189,4195,4185,4205,5423,12858540,4170,5423,0x927682f525752151a,4170,4158,4321,29974713762,
28196271734,9281615,4209,4205,5423,13767852,53595030696240,4154,4170,41705594749196,4604,49500711425327,11509822,4170,0x1a4310d7d0da4ac,
4199,4205,23577367418,0x1beabea17d214b6,53983571989922,4199,4174,23321818410,9040834,4142,13296723,0x18792b9e94af529,4167,4169,25389307183,
4170,0xc460c0bea570da455,4199,10616939,4192,4177,10178671] (by decide +kernel)

private theorem part348 : Refutes moves 0x10000100000000000000000000000 0x145554005001010000100000000000 :=
  branch 1 0x10000100000000000000000000000 0x145554005001010000100000000000 94 0x1c5dd5245011110005500000000000 (by decide +kernel) part349 part350

private theorem part346 : Refutes moves 0x10000100000000000000000000000 0x145554001001010000100000000000 :=
  branch 1 0x10000100000000000000000000000 0x145554001001010000100000000000 86 0x1655dc421141011010104104000000 (by decide +kernel) part347 part348

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part351 : Refutes moves 0x100000000000000000000000 0x155544000000000000100000000000 :=
  finish #[
13296507,52027038245265,29975040099,61392828151420,4160,82524209425220553,29976081134,5405,27234256381,0x4b9cae2256210a26d6ea,4144,11449647,4155,4162,11974262,
4184,51396870010599,0xa6dbeaf4d6fdfc609,44414511562833,4171,4190,8831079,4211,10524066,0x6c416b14399afaa904c3,11510510,4177,12849247,4881,0xd881e0be861290354,
0xc2c5f561e208c259d,11076475,4167,4171,4177,21469409601,10523476,14664532,0x194e59d6c0c467d,11509859,4191,4205,23576002967,4167,4149,
0x1883485483d42ee,53904266007637,26321310804,25396331938,11509831,4191,11972689,4168,4176,49834415489310,82938348492895862,4159,9655131,53920474679015,22685025910,
4177,4197,4167,61387771049154,61392811803481,4185,61391895975097,95143858773206646,10616931,11972689,8831048,4207,13201686,0xdfb0512ae21bd42ce,0x424c3f15f0be90b6b530,
4168,4160,13201572,53423231550508,4185,51651842323632,10616896,4197,5205,0x6233d41077edb5a203d1,23572430949,10178669,4190,9277526] (by decide +kernel)

private theorem part345 : Refutes moves 0x100000000000000000000000 0x145544000000000000100000000000 :=
  branch 1 0x100000000000000000000000 0x145544000000000000100000000000 112 0x145554001001010000100000000000 (by decide +kernel) part346 part351

private theorem part339 : Refutes moves 0x100000000000000000000000 0x145504000000000000100000000000 :=
  branch 1 0x100000000000000000000000 0x145504000000000000100000000000 102 0x15d506000404010040100000000000 (by decide +kernel) part340 part345

private theorem part327 : Refutes moves 0x100000000000000000000000 0x145104000000000000100000000000 :=
  branch 1 0x100000000000000000000000 0x145104000000000000100000000000 106 0x15710c004041000400100000000000 (by decide +kernel) part328 part339

private theorem part307 : Refutes moves 0x100000000000000000000000 0x105104000000000000100000000000 :=
  branch 1 0x100000000000000000000000 0x105104000000000000100000000000 114 0x105385010000440000100000000000 (by decide +kernel) part308 part327

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part355 : Refutes moves 0x10800004000000000000000000000 0x1a45cc520040121010800004000000 :=
  finish #[
0x1b04b2ec451c309,0xd82a3747657588270,0x20cc7651b95d6213e44634c,4137,4157,57650362402095,13764217,12869695,45978750199191,4163,29070497175,11068587,4189,5301,27273986475,
4181,0x16792bac4446400a39e93d634c,4147,4151,4165,4169,0x47c8fd59746e57588115,14189168,11511092,14663768,4163,0xd8e05d2bac435227d,11019131,4165,4159,
9610533,0xd1bb12eedeb588523,46186555581847,0x18414814735c597,11060189,4163,4177,4175,4183,4169,22453715915,0xd873deb293a3d244e,4178,57650343387967,24203216392,
12869682,21124543900,12359068,11509833,4163,8761425,4197,4191,4810,53990130316811,4154,11011595,35231587656461,14209807,4165,
13742161,4128,0x1af97d454afa2fb,4170,11510426,0x36268ddfb7a7118992f943b,4183,4192,4974,57648513787516,4163,0xd1b5f52b968a224b6,10584148,4179,59328254293191,
13186571,25051505950,11399263,23574184807,4189,4205,11510420,47819565015705,8762208,4187,8761562,48287356462596,29978302184,4159,23178089339,
23466061921,4171,4183,4197,29068723508,0x168b2ba4e859441,11399386,89951842828531210,4183,4171,13742181,4140,4176,5641,23230235059,
23563965018,89936415306003512,4157,4197,13742155,8753587,0xb62bed1197d20f675,28149536047,11511294,4191,29975622288,11399241,4178,25112457645,0x1b117ee8dafa534,
4163,51425615122852,4197,8762010,10625694,4179,4210,4189,4205,11956312,4180,4196,4204] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part358 : Refutes moves 0x30000004000000000100000000000 0x1ccf8cd00540021834005004000004 :=
  finish #[
63359948322075,51396871906721,0x17a52b5b3cae44b,12358712,4129,4165,4147,9200826,29103650094,4196,22224990632,12375226,23526564570,24488969077,4175,
4193,4205,4157,13297277,0x1782d9e572dd530,4141,4958,82438196340376879,4133,4159,0x1bf92856eaf2147,4185,4162,4197,14180550,
13296726,11956285,53747759276759,0x6fdd8768b2b96eaf2522,4185,27040052733,42169344394543,8765510,4189,4192,61393591792346,10470920,11956309,29053318209,13722432,
53887939830760,21446189103,37806639969910,23357891560,4165,25386550320,4163,4175,4151,89947903124440584,4197,4192,5641,25246230025,10993736,
27232101897,0x1b10afe5728e4ba,46423061578163,4145,4141,27040051983,0x17957d4234ac34c,4166,4159,4181,0x1b10041a44ae6e9,26251522348,4164,50158083249341,59607018431687,
4181,24490358063,24490366475,4141,4159,4193,14194294,27235177417,4136,51593717162869,4183,0x195cb757a05c522,4193,4192,4197,
59523923109386,50155065214589,49569360078129,9592923,4165,0xcb0b117f0992f26e9,17952014965,4193,4197,57609574314311,61496804364615,23333626485,23334995579,95096361225249619,4173,
5756,94236351348811268,4180,4159,4165,5630,11457839,11505725,4185,8765515,11509856,4184,4163,4177,4205,
4198] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part359 : Refutes moves 0x30000004000000000000000000000 0x1ccf8c500140001830100004000000 :=
  finish #[
29012661295,13297163,12322095,4205,13297163,27232994827,10469469,4141,4171,53984420037825,47781482513702,4159,4137,92869795838539042,55616727168515,
11956288,4164,5532,28145034432,4180,0x195d7ee8dafa602,4163,5643,11511307,4163,13743056,4164,0xcac4ad0e220196275,0x1bf92c0302fa4af,8765549,
4192,4196,4198,9008073,11068502,4193,28146877743,4192,4423,0x1bf52b97d27619b,0x169146db42882e5,4187,14663755,4163,27087192693,
23275808264,5406,59381862031869,4157,0xad6beb61a4eafa608,4205,4163,11957660,4164,89904722233291482,55673743635746,4164,57524529119977,25235014841,21446136135,
12362809,4184,4157,4177,55776822850428,4164,13215240,59606878500360,0xd885c8bc82e860044,4198,4193,4192,4204,4196,40307291960841,
13296714,13288526,0x1bf960a582fa303,4163,28144156753,4191,23576843329,5198,25342367010,23524773983,13742155,30028182694,28146902212,23576401068,4130,
4160,26084652668,14636668,4198,55624091013447,26360128364,4198,28147347557,4196,4180,12402796,4167,4185] (by decide +kernel)

private theorem part357 : Refutes moves 0x30000004000000000000000000000 0x1ccf8c500140001830000004000000 :=
  branch 1 0x30000004000000000000000000000 0x1ccf8c500140001830000004000000 44 0x1ccf8cd00540021834005004000004 (by decide +kernel) part358 part359

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part362 : Refutes moves 0x11020004000000000000000000000 0x1eefdf742440c11111020004000000 :=
  finish #[
0x168b2b9e4d88608,59317705020937,5423,14188723,59512454402228,4162,4154,53679864189771,4165,4158,0x1a372b94012a5ff,4163,4175,0x4950991df9a0b1d1b609,97959401716794889,
4185,5522,0xc22157621703d417e,4158,4935,25402787228,4176,4146,5402,29058426270,5423,14189871,14189871,36003709506379,4142,
4150,4154,4146,30020212015,12404342,4149,29062960431,57409821501161,11403344,11067468,4165,4183,4169,4935,55672868873614,
4169,29064385833,4128,59522034778893,4176,0x881a3b10a8d9fc361,0x1a367f24ca8c0c7,11509833,4191,4163,28148688381,74541104236028899,11509829,5414,52024941511974,
4171,94234890986300387,13287519,4155,4159,4170,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part364 : Refutes moves 0x10020005000000000000000000000 0x1efdcc752450881151022005500000 :=
  finish #[
8435212,19556466867,14635063,28147795574,4140,25423730066,14189970,51843547612680,4149,14200894,5640,0x37e8eac9db10b80952804a7,4193,10584143,4179,
28032586593,11060510,21681061979,11060510,13287904,28147793983,4176,97042617972405769,29061047593,37815871251213,80494844920545371,11509849,4191,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part365 : Refutes moves 0x10020004000000000000000000000 0x12fd8c741440801110020004000000 :=
  finish #[
0x652cac780cd6c449760c,0x166b265e0846609,4295,59516489831728,4184,4163,5414,18624407043,13287499,4159,4175,5400,97064702567966331,0x6fd2c64ed6217012c2df,4192,
4183,19685950985,14160655,11035928,4157,42306717148904,27055941135,4201,61515756140041,4145,4147,19191464051,49567401280817,9642950,11509865,
4170,4163,4198,14636553,12403994,4158,5400,11044143,12297519,9617453,4183,4177,27092616277,11010805,4175,
5634,9610761,14635081,37195706488111,37825687164418,12402722,4158,0x52ca5bb112a5ea2fa52f,4191,4177,4163,43655135516393,14189873,0x21dda2805961622c49fc52f,4151,
4201,5641,29059392125,10567761,4165,9844226,80490989136986857,4170,23355598345,44335886952169,4168,4201,0x9e33db622c4d853c6,5641,59410966848815,
10567761,12402757,4149,4140,51599311335851,53372562543898,0x14bc00afad88b1a4bd0cafa175,4177,4198,45518346473899,19723817690,12402757,4140,59538258346755,5642,
25405605494,11509856,21720342602,4179,4184,4210,4185,5532,14636434,28161257907,4160,19723793810,11509823,4170,0xa82b11474992192f1,
13743189,4140,12404124,25403827612,21720342602,4179,4185,25415341692,52050617615996,13742167,61497718841632,4163,29064413727,20654933513,4165,
0x1b10eeda2cae3e3,51530671096243,55596625773982,10969749,4153,4159,4165,13742185,61491261846615,4987,0xd88bea4bd7d58267b,0xc40b117d5e527652d,4211,10563659,10625694,
4185,4179,4184,11956338,4196,4164] (by decide +kernel)

private theorem part363 : Refutes moves 0x10020004000000000000000000000 0x12fd8c740440801110020004000000 :=
  branch 1 0x10020004000000000000000000000 0x12fd8c740440801110020004000000 84 0x1efdcc752450881151022005500000 (by decide +kernel) part364 part365

private theorem part361 : Refutes moves 0x10020004000000000000000000000 0x12ed8c740440801110020004000000 :=
  branch 1 0x10020004000000000000000000000 0x12ed8c740440801110020004000000 108 0x1eefdf742440c11111020004000000 (by decide +kernel) part362 part363

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part366 : Refutes moves 0x10000004000000000000000000000 0x124dac500040001010000004000000 :=
  finish #[
61394638554633,9610305,4187,29060334081,12322313,4187,10060865,29062153281,4167,4761,0xc3a690f517a2fb3e9,13742155,4164,4176,4185,
57644805137600,37240677815694,0x9e3a3a96734bd6184,14188635,25246229560,89674119574643874,5057,0x23cac43d67816053136808f,9605211,4171,4189,4168,4522,98611000706769322,0x8f27ab625ea58817f,
0x1b104a9b036852f,4171,4179,4163,61391654023906,25084097593,4160,5205,0x12c40ad2c4b0b16f52c42190b4,4170,4189,4210,11956313,4196,4180,
14144597,55741496951995,90098198023455677,12837821,10043455,4157,4165,5319,14198172,9609265,0x1a1b7d4933cd59c,29084525847,4181,26092557245,0x1b036390019452f,
4181,90077121179042894,4159,4185,27159679399,4629,19685029385,55803605311915,4168,4159,25387950141,4147,4165,4187,0x188caf83021352f,
0xdf8432f522321d457,4185,4204,39353834329718,12222884,45391657518715,4138,4168,80609447827317594,0x1a3aea0eebc3275,4168,11362681,4134,4155,0xc9aa2c0d25634035e,
27067451003,12289545,4130,47393902167445,73797989655233941,4155,4153,4139,45774289528215,4187,4157,29070398765,29986682146,26358612945,4165,
4157,59520096941364,13260411,27180311203,4187,4157,4175,4523,61386174637361,4210,0x50e8904a42d223588608,11362974,12402747,4167,4176,
4185,29061113129,0x1b16f528da13357,4189,5532,0xd8267d621e1bb84b6,0x18572ce2320f456,10563673,11956312,4180,9281604,4211,9724015] (by decide +kernel)

private theorem part360 : Refutes moves 0x10000004000000000000000000000 0x124d8c500040001010000004000000 :=
  branch 1 0x10000004000000000000000000000 0x124d8c500040001010000004000000 101 0x12ed8c740440801110020004000000 (by decide +kernel) part361 part366

private theorem part356 : Refutes moves 0x10000004000000000000000000000 0x104d8c500040001010000004000000 :=
  branch 1 0x10000004000000000000000000000 0x104d8c500040001010000004000000 113 0x1ccf8c500140001830000004000000 (by decide +kernel) part357 part360

private theorem part354 : Refutes moves 0x10000004000000000000000000000 0x10458c500040001010000004000000 :=
  branch 1 0x10000004000000000000000000000 0x10458c500040001010000004000000 107 0x1a45cc520040121010800004000000 (by decide +kernel) part355 part356

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part371 : Refutes moves 0x1800804100000000000000000000 0x13e7675e0ca4574031905804904100 :=
  finish #[
29062505053,22655042759,4721,14197957,9633841,4184,4181,14165052,47617247475211,0x1a3b620f7bd6354,4147,4165,23482848564,12285451,43696386106769,
4189,4165,4195,88829682900354245,0xd8826d7d64a26534c,4184,21393851472,10445233,29059826097,4177,4169,27276198782,98975891775730996,4169,55460075102704,
0xd8ab1d2717eae84a1,4180,13312049,4139,4150,4172,4153,11817854,61395553972494,4153,14635201,61389867869705,26358661987,4165,4181,
59521154867630,4135,4157,13190086,11818287,59514527761711,9659695,4184,4172,4181,36153470828728,0x1beab889093652f,5641,29062972719,4150,
27235222813,23422681729,4165,4169,13297274,20229863034,4196,0xcb2b112ba54aef122,11497521,4174,4180,4181,4195,14189871,26360435229,
9659695,4172,4181,30010933432,29062546018,4169,5062,24206943088,19785225072,4163,4196,11411889,23549956529,4180,4167,
4181,4195,13296049,23374091567,29077938615,5754,61386202474106,13312061,4142,4172,9478201,9441654,4125,4128,4137,
4152,4146] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part372 : Refutes moves 0x1800004100000000000000000000 0x136747de0804534031801804104100 :=
  finish #[
47874996950538,14636309,5750,0x195e936faafd34b,4181,4169,5163,59514150380363,5408,25051518240,4181,11407417,4173,4152,23123850761,
29079708619,4184,41497593938814,76515175860196637,4184,8761417,4196,4197,43695490429685,11497720,4984,22515397391,4197,4199,4189,
4348,11498579,4174,57655876236047,48229379502300,4140,4316,53510966641861,4171,4159,4199,5757,72840167114957688,4167,13312537,
12338813,18727855386,4167,20640899798,4153,8761836,4195,4199,13295709,4157,4135,12870173,93051850782769637,29986686039,23169541640,
13295672,24466990131,9659915,4172,4175,24197227477,4137,4207,4153,23549956411,11285703,43234572674679,0xc3a7552cafacae5fe,4135,18757715454,
4173,8745039,4197,4195,0x6c134c594996be5fc6e8,53991041909739,61504290263555,23183999979,0xdf6b14b2ec45fc5fd,12383303,4189,4171,9646191,4181,4175,
11522478,18612208917,30032450424,8761429,4197,11509859,4163,4184,4177] (by decide +kernel)

private theorem part370 : Refutes moves 0x1800004100000000000000000000 0x1367475e0804534031801804104100 :=
  branch 1 0x1800004100000000000000000000 0x1367475e0804534031801804104100 95 0x13e7675e0ca4574031905804904100 (by decide +kernel) part371 part372

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part374 : Refutes moves 0x1800004000000100000000000000 0x1367671e0505d30001814004000030 :=
  finish #[
28190614832,12313880,17694172464,17695499563,4154,4139,4163,4932,13280015,12869711,0x6232c349a2368eafa602,4163,4177,14188743,8672777,
4165,14189380,36393333020169,4181,4195,4173,36278585249988,23175087046,26362807275,26114994375,4181,4175,0x195499496d880c4,0x1b10bdd6185b0c4,4191,
4195,4190,4727,13312439,14188587,23552623893,61395553973428,72781617145275115,4165,4150,12870520,4137,4177,4721,0x81788d60ac457d4a1,
4145,9634222,4172,25312911559,0xc33beb6219a2f72e0,4153,19782366259,10076348,4157,0xc2a8895f6c103c2fd,0x18666701e84160f,4172,4171,4163,4165,
4169,53988070974985,26097226509,0x168b7d5712f752b,4153,4195,0x1b144dafac3152b,0xd8a4010c6fab45602,4154,93440716285694593,4148,4158,4146,0x1b12236c43d6268,18363036840,
4195,25312834262,38355530364206,18249625917,27056395351,20636348494,4195,12824669,4158,0xc315fad296185b51d,12792544,59328505935478,4195,26349864239,0x5eb41d877621a6201113,
4151,5319,12870526,10491389,45604553086369,26099589987,4211,4165,8745017,4189,4195,11509810,4177,4184,4191,
4156,4196] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part376 : Refutes moves 0x1800014000000000000000000000 0x1b67461e9101730119800154000000 :=
  finish #[
80350051915367945,29940098569,4171,51792952276275,0x327efe4b2be2ba02dafd084,4173,4195,0x201177bd6338b2e4a0ba67d,18620121982,4396,0xbc79336214705b09a,4195,4197,4199,10785068,
13734955,17730475315,5530,11523043,4173,4159,12394567,12791922,4138,12833980,4146,4178,5301,0x4f602288d7f2134440dc,4145,
9593336,17381304039,4133,21174843111,12751464,14188586,0x81e84d62011177453,41633067233911,4159,4195,4145,4600,20327654580,8672777,4174,
4170,4167,4173,12234932,25059377935,14188625,30922437706,89494138571718815,29063061597,4139,4153,0x23ce880465956221488f141,61504524682327,46421207642754,5423,
0x17ad5f10091a528,4153,0xd7e18162177afd303,4173,4159,4195,61453828059408,0xbd6b1d2b82dd886e7,0xd8895c16c518ab282,20330041410,4196,4158,4156,13742130,4140] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part377 : Refutes moves 0x1800004000000000000000000000 0x1367461f0100530101800004000000 :=
  finish #[
27105280415,57680930477578,9660018,28146901071,4191,59506742813563,46226679641597,11510983,4156,4153,51499957723778,0x29244bdf96c561e232fa49e,22605173505,95094452387815906,22502171407,
9658417,4178,4190,4169,4175,57639900910080,0xd19a376209b4b3513,4196,55502835406344,94595910638097696,9659913,4178,4175,27202142749,13190781,
14664221,11035157,4175,4169,0x19297f0fbc9e215,4141,11509860,4177,4191,0x1a332aa595fc37b,61393768892026,9622826,4169,11464804,4145,
0x6f8d195f44d97bafd609,4167,4173,4195,0x1b12b4dd52fa520,4312,4984,48230314070331,4169,4174,59517462107770,23600050361,30009173150,0xd895c3622f8afa49e,0xd0e5977f0602fd307,
4181,8761421,4189,4197,4199,4195,5641,35949469270192,10077003,4165,4181,5077,19730158210,14188586,0xd88bf8eaabe2fa139,
4163,4191,4737,49655753062007,4191,0x17764d9002ef52a,0x1afb62e4ed887a4cd5ddb45090,4138,11313794,4871,55863627719431,38494779929899,4145,8745037,4189,
4191,0xd147935f9e68ba4b3,23602959179,0x60ed115d8d150093030f,4190,4199,0xc1dbf216d7bae237b,4153,4167,4181,13742179,11972652,4192] (by decide +kernel)

private theorem part375 : Refutes moves 0x1800004000000000000000000000 0x1367461e0100530101800004000000 :=
  branch 1 0x1800004000000000000000000000 0x1367461e0100530101800004000000 88 0x1b67461e9101730119800154000000 (by decide +kernel) part376 part377

private theorem part373 : Refutes moves 0x1800004000000000000000000000 0x1367461e0100530001800004000000 :=
  branch 1 0x1800004000000000000000000000 0x1367461e0100530001800004000000 56 0x1367671e0505d30001814004000030 (by decide +kernel) part374 part375

private theorem part369 : Refutes moves 0x1800004000000000000000000000 0x1367461e0000530001800004000000 :=
  branch 1 0x1800004000000000000000000000 0x1367461e0000530001800004000000 80 0x1367475e0804534031801804104100 (by decide +kernel) part370 part373

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part379 : Refutes moves 0x21000004000000000000000000000 0x1d4fc6100100410821000004000000 :=
  finish #[
0x1bf22acbbd1b531,12404124,8766663,0xa7c9336202e217361,4173,0x1a1a1710fa214aa,4181,4191,4196,23358793006,0xca242f7d6c44aa361,5397,27013924039,11509835,4177,
4205,78098461157865082,22520824673,14189193,61393770366473,4177,12402755,4185,4140,5750,13293170,11067454,57558052840647,0xbbd95d622230c65fe,4185,
4197,46396614722614,0x176a3cefe4aa18ca19462fa091,4191,4163,0x56282e88d62093cae4a8,0x4f851943f11893a211ed,4183,18844829084,14664789,61514025821269,4195,14618691,0x57d5884217c6fca1a128,4171,
0x6c44464f48550f9360c7,4178,4205,4196,4181,13750801,55305359274759,4195,0x1926995da936515,59522034778188,61514901390421,0xd867a97e68dd883be,0x1b04756232e0609,8765551,4189,
14189980,0x17a97f28d05c672,0xbd468b2868d93358e,4169,4178,0x1bf8afef885ca36f510aa1a59d,4171,4181,4191,14214447,55777685939837,4171,27108516599,4175,0x19392b657cae609,
9201385,27235222832,9193193,4181,11509839,12402755,4185,5205,4760,29062153386,0xd887a909e1ddf5438,8765500,4189,0x87c6a12b90abd41b4,26348995518,
26350801117,4161,4156,0xbd488a1710fa214aa,4183,4181,4191,11972708,4168,4192,4184] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part381 : Refutes moves 0x1020004000000000000000000000 0x1bcf46502040c10101020004000000 :=
  finish #[
9598255,5423,49570320962863,59517460243501,4172,4184,55775830139067,13260079,11511078,4184,13287519,4159,4177,59515045565850,0x1b112b80a81751a,
11511066,4184,4191,4879,13255152,4145,80809613568009498,25236956463,4210,4196,4187,0x9265892bafcca5112,13287848,0x195d7e4cd2fd5fd,4180,
4187,4159,0x1bf46883c13660a,13246888,4145,39454855685085,19266049306,61391854609462,13295683,0xb6a1f12b97d4b0526,4210,4159,4177,0x68edf5080870b7a0d1b7,29060269359,
51944798966414,11497535,4180,11382861,4153,4195,13743189,41637789147436,4191,5644,0x1a360e2c593028e,4178,10572885,4171,72363460075893339,
10572076,14635083,28147795574,4140,55778694845961,21116773669,40413422407747,4173,4195,11818614,61389738829210,28147794011,0x1a3601dd658859d,10621352,4178,
48283658597897,4529,11522722,4173,4180,4195,23314145942,4171,11972703,4192,4184,4176] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part382 : Refutes moves 0x1000004000000000000000000000 0x134f66100000410001000004000000 :=
  finish #[
14636340,0x23cb3397495d7eac449417f,4172,29079397218,55847372403554,25418687105,12755016,4185,4159,27191510531,10044597,0x4761eb854f49eb4b3255,4196,43812058494475,11497521,
4187,4181,13742721,26345583660,25437274518,4137,4172,13742510,42136003818799,4154,51318640641659,55520036303460,4154,0x1b112aafad1b200,4128,
4186,9622827,12755575,11466140,11407445,4159,11972657,4168,5644,23358809602,12869708,11522478,4181,11383897,49417559819455,
23550836805,4185,4167,4176,57407961073270,9929007,18642019733,4147,0xc924d57e9001a0603,4185,10540340,48091639710061,0x96dbea7f8fb3601a2,11862083,4189,
5319,10520182,4163,74314365027710366,4174,4167,4187,4181,40240441197865,39950176879452,4169,89346033782797035,29976036660,11829315,19582145513,
12871167,4147,0x3119a45f86d746d6a2f7221,4153,4167,4187,59568794219925,13714631,26186604909,0x195c0eefaa0d0c5,4153,4163,0x19650ce5717760c,20326802735,28147363918,
4152,4168,24206488193,11404596,4172,20330505057,0x1964b80bbc3d4b4,13742122,41272226062587,13317532,4163,48096506385820,10539426,11407427,11972657,
4184,12402760,4185,4158,9281616,9724019] (by decide +kernel)

private theorem part380 : Refutes moves 0x1000004000000000000000000000 0x134f46100000410001000004000000 :=
  branch 1 0x1000004000000000000000000000 0x134f46100000410001000004000000 101 0x1bcf46502040c10101020004000000 (by decide +kernel) part381 part382

private theorem part378 : Refutes moves 0x1000004000000000000000000000 0x114f46100000410001000004000000 :=
  branch 1 0x1000004000000000000000000000 0x114f46100000410001000004000000 113 0x1d4fc6100100410821000004000000 (by decide +kernel) part379 part380

private theorem part368 : Refutes moves 0x1000004000000000000000000000 0x114746100000410001000004000000 :=
  branch 1 0x1000004000000000000000000000 0x114746100000410001000004000000 107 0x1367461e0000530001800004000000 (by decide +kernel) part369 part378

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part386 : Refutes moves 0x20011004000000000000000000000 0x1dfd447c8393111960411004000000 :=
  finish #[
0x192f466fac9f52f,14189513,27200779546,4167,4147,29018874946,61385111954259,4135,55840065843527,4197,61391889023942,4159,4193,28131849842,14665225,
61456759072048,61513951707991,4171,4153,0xcb2bf23194328c52b,4195,11509857,4163,27201660314,11068493,4193,0x193e8217d5fc447,4163,12399915,0x168b0868ec43609,
4174,13280322,25187070807,11509838,12402783,4167,5427,25033737523,4193,0x17a8ef5ec11a12c,9090133,9040156,4138,4146,9924674,
23573558357,13742168,4128,4140] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part387 : Refutes moves 0x20010004000000000000000000000 0x1d7d05708301100860010004000000 :=
  finish #[
30036985135,0x1b044f93512067d,4171,5410,45860093421170,55510578176102,4175,30036124297,14664775,61510278374377,4157,4171,29009109412,5757,41639675684123,
4195,30036063747,0x1bf799afe446528,23348592731,4157,12402789,4167,13742169,12817711,27108517063,4186,27230713120,0x1bf8d5a4ccaf276,4248,24498660989,
18262560853,4124,14190205,29063063165,4175,0x195c9b6fdc9f60b,37619577906483,4195,4201,4186,55778703692188,61495824306662,11509844,4170,4163,
4198,25247569532,27230713577,4180,11509956,4163,4965,14188869,13313545,4153,29975528634,20142351546,4201,4207,4195,
5306,57611123942682,11448767,4148,4972,43794449032474,20177146043,0x1b132bd75dfb51a,4148,11509826,4156,4163,4198,11507198,0x6fd93e93ebe96faf452f,
4157,4171,4178,12402791,4185,13296803,8675645,4175,5423,97938690670563653,4185,4199,11486075,5756,4987,
5423,0xb6888d2b96faf4517,4185,9678949,4195,4207,4198,0xbb1009096115fc60f,27125294368,13295695,27235668859,4198,40141075330685,30029075182,12402790,
55772251505087,0x1bf8f517d13e43f,49901317281511,52030699688827,23348592742,4157,4197,4199,13742169,11972652,4152,4184] (by decide +kernel)

private theorem part385 : Refutes moves 0x20010004000000000000000000000 0x1d7d04708301100860010004000000 :=
  branch 1 0x20010004000000000000000000000 0x1d7d04708301100860010004000000 96 0x1dfd447c8393111960411004000000 (by decide +kernel) part386 part387

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part388 : Refutes moves 0x10004000000000000000000000 0x177504300001100040010004000000 :=
  finish #[
51655484748649,27233436752,5641,12870741,4167,23240459206,10506655,4175,4145,28147363909,4160,12403308,89346271555962159,10522705,4174,
11974262,23548064964,11509838,0x6fad1b4dab6db520e42b,0xacb7b0ef6fab6b67c,0xc4679ebe961a2267d,4174,4190,4199,28148688509,12420045,0x657588756f1a8da1e1ea,11972687,4160,11974266,
10564471,40394412925816,4185,4190,9723982,4203,4191,5629,23573156844,4165,0x1bf929efaa0e13f,4522,51883787145642,4170,12398658,
4195,21687592020,11370590,21552006667,11437350,11428833,10609520,13295700,4190,4195,4633,5532,20604621664,4184,4195,
4633,27234775918,28147364515,4184,12402787,4158,9723984,8831083,4211] (by decide +kernel)

private theorem part384 : Refutes moves 0x10004000000000000000000000 0x157504300001100040010004000000 :=
  branch 1 0x10004000000000000000000000 0x157504300001100040010004000000 113 0x1d7d04708301100860010004000000 (by decide +kernel) part385 part388

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part391 : Refutes moves 0x40000005000000000000000000000 0x19557c152500000444000005500000 :=
  finish #[
23199855664,12870478,4177,0x1a3616efaae24be,4201,0x1955458602fa35c,0x68b3ccbeb0c5b5bd34c7,11370568,41997655192416,8762208,11456607,4190,4171,26101851439,42066340115033,
0x1a372ba13b483ec,4141,4189,61489306854921,61494093088144,50167771157807,4155,4183,0xadf84edae8d8da37a,4207,4199,29977850860,26101405084,4166,11928879,
5100,93529090493883361,4201,12402791,4185,4158,0x8fe952dadea356373,5100,18166228380,41394294838793,26016194621,4156,4177,25404290460,14636444,
0x16916228db6b37c,4192,57646684091225,4166,21570233429,4163,4156,4770,8786143,4199,4193,9724009,4191,4203] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part393 : Refutes moves 0x40001004000000000000000000000 0x11df541c1454000540401004000000 :=
  finish #[
29054547243,30035248427,4190,14185771,12870601,4147,47271837652605,29059802749,4179,14618691,0x194f118baa5f609,4190,5319,0xcae01f7f24fc4608d,0x16916356b04567d,
4173,28147793989,4140,4167,47351933158112,59519293964952,8785987,28147794146,82776101799204147,4191,4181,4193,0x734bd82ca9260fdf525c,59511249290071,0x179f2bac03c7608,
12402773,4185,5205,61396503212684,29062615266,0xc457992bd7d22152f,4181,4193,4191,4166,5319,0x4055f693f2ba2335859c,4141,25436402742,53626627776711,
11509831,4163,0x4f5cae6d01868dbd4346,23572386422,95081265260271222,4183,4191,11956321,4164,4156,23123019389,0x1a3761d3e20d42c,4173,21674050609,57456633225880,
4153,21395793533,55691837809721,27233441180,4168,4159,4195,4175,25402937768,10613610,21737935931,28144989269,4163,4175,57646685029679,
11522936,4166,4173,4195,4181,29053658633,10581300,4163,10622255,77446944407901487,0x17a97d6542fd67a,21712797766,4195,4181,5179,
25109045920,11019894,11509853,4205,0x90b7b0f52575f5597,25141892393,5750,0xa1cb117d496bc72ca,11509835,11493471,4166,11956301,4164,4156,27232527329,
0xca85fa97d70b6767a,18003288116,4197,4209] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part394 : Refutes moves 0x40000004000000000000000000000 0x115555141400000440000004000000 :=
  finish #[
59517333509310,24517280831,0x1af960169aef270,4173,59517438641349,0x18412721f51b603,23449276634,13312094,4131,4205,28147811036,13742812,0xd1b5b6ed6523d82dc,4190,12863101,
61510352487717,27175624809,4142,11956333,4156,4172,4314,17930929667,4316,27081537033,24463828159,4169,4181,12869737,4177,
4288,4962,12870526,4167,4201,28144923356,46426309363322,23542915929,4167,11956329,4156,93288740300968188,4190,4171,4157,
12870609,52099422970856,0xd8e7b0b76841964b4,20589217405,4165,4157,4171,0x22acb6c315babe42cbd4601,4185,21572019262,13313000,4164,29070542127,4979,9606003,
4165,4162,57642851923251,11506777,4162,0x62349fa36f61b3af43e1,4157,4164,4185,5205,8778402,4191,4193,4201,19482674217,
51275656094099,4147,12869939,0xd896cf9a4bad884c7,26360480955,11927581,4189,4165,27268801577,59392187531895,4171,29060248883,4148,4153,52098544518120,
4176,4707,0x885b103b2fb36852f,4171,11465704,4159,4953,23483285927,12402781,4176,27235222688,55512566261148,0xd1b20283578367608,13312052,4164,
9281593,9724009,4209,10170475] (by decide +kernel)

private theorem part392 : Refutes moves 0x40000004000000000000000000000 0x115554141400000440000004000000 :=
  branch 1 0x40000004000000000000000000000 0x115554141400000440000004000000 96 0x11df541c1454000540401004000000 (by decide +kernel) part393 part394

private theorem part390 : Refutes moves 0x40000004000000000000000000000 0x115554140400000440000004000000 :=
  branch 1 0x40000004000000000000000000000 0x115554140400000440000004000000 84 0x19557c152500000444000005500000 (by decide +kernel) part391 part392

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part395 : Refutes moves 0x4000000000000000000000 0x155514100000000000000004000000 :=
  finish #[
14653045,5399,11752046,49301871584536,4177,4171,9916485,25406480687,4140,12870950,0x194b6083cbb7522,5295,0x185cb1656b68531,4189,4171,
4165,0xbc03217f1ea4ae3d9,4135,5399,10511445,4171,4151,4201,13214696,5399,61455521280890,4171,14619574,0x6fb196be2cd56eb6860e,8630373,
4157,4165,5399,0x84115cd9e572063b6,4171,4201,13743189,11515187,51687040910639,13742173,24072271125,59625114781077,28147352883,4163,4171,
82203092714739209,0xc9676f7e4cb4ae346,4201,11486185,28147794021,4185,11956295,4172,4140,4164,4743,4743,25161008425,4163,4195,
13198421,10511772,4161,76680854588469684,11854933,52027825795955,4169,9683033,4205,4199,35401499312876,11335068,5283,9573559,25346007107,
4201,4169,59522034778557,5198,9671092,4193,4169,11972711,10170432,4184,44331369415534,0x1b1af29b3aef59c,0xcb288d619112f73e8,9622710,4169,
0x16ce4b570af6515,8831039,10170477,4184,0x50cdfcb1146d9ab676e9,4771,21721215863,4201,4174,57648513684406,53504299934431,52027951702095,10170469,0x1b17620cc25866aee28dadd2ec,0x1954ec9eb133367,
20830249051,4635,13296613,0x185ebf5701ff3eb,4174,10069069,0x68db6708a669e61273e5,4160,4163,4193,25259778550,24449311033,12334383,11944035,4161,
0x17a9259b5cac21b,10170416,19914997856,4207,4211,4203,9277553] (by decide +kernel)

private theorem part389 : Refutes moves 0x4000000000000000000000 0x115514100000000000000004000000 :=
  branch 1 0x4000000000000000000000 0x115514100000000000000004000000 114 0x115554140400000440000004000000 (by decide +kernel) part390 part395

private theorem part383 : Refutes moves 0x4000000000000000000000 0x115504100000000000000004000000 :=
  branch 1 0x4000000000000000000000 0x115504100000000000000004000000 100 0x157504300001100040010004000000 (by decide +kernel) part384 part389

private theorem part367 : Refutes moves 0x4000000000000000000000 0x114504100000000000000004000000 :=
  branch 1 0x4000000000000000000000 0x114504100000000000000004000000 108 0x114746100000410001000004000000 (by decide +kernel) part368 part383

private theorem part353 : Refutes moves 0x4000000000000000000000 0x104504100000000000000004000000 :=
  branch 1 0x4000000000000000000000 0x104504100000000000000004000000 112 0x10458c500040001010000004000000 (by decide +kernel) part354 part367

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part400 : Refutes moves 0x21400000100000000000000000000 0x1d49df754004011050821400000100 :=
  finish #[
14189767,0xb40927620fddf5435,0xd7f93b7d6c44a9595,4151,4163,0x275565d867acbf2fad8860d,55864553144956,5396,10466825,4165,29063025276,4151,4181,23381160829,4168,
4163,23477110281,5641,41947909355126,52067799385831,4179,4165,29063931187,11461130,29974605893,4153,13766743,4146,4158,0x6fa57da1127290d8827c,
0xd21beabbabed88196,39955994280534,39955992511673,12349497,4180,4163,11502232,4168,28199912731,27064763695,4168,41484120065545,0x1b18bf2fad21678,51807190491198,4163,
4177,8737659,8757466,4197,4187,4191] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part401 : Refutes moves 0x20400000100000000000000000000 0x19599c304004001040820400000100 :=
  finish #[
41948859106503,26362770377,0xd1a06d27ac42fa67d,4163,4205,13766837,40211908486781,8757335,14189855,28194464254,4183,72467189217599631,0xe66010beac421c5fe,4183,4198,
28194460539,20481971832,0x1bea0153d2fa20a,4163,57742253729051,4192,4197,13768310,49484420211877,4163,0x19537d69085544e,14188635,0x61c49e7a56210e2f50c0,11432008,4165,
4179,4207,4193,55365347100283,84834114356773732,0x6c6e690fa93d7305a60f,53984535643223,4177,4201,4183,4386,37953628119258,13766758,4158,0xd7fbf884a575214c7,
11428704,51940184843675,4187,0x6575210802e9e83d8217,4145,4171,23381571074,0xa17bec16a572e660f,23408215552,23380317698,4201,4177,4183,0xafcaff7dc2cd2160f,4315,
0xbd8bef4842d2e60c1,4171,0xcae93ef6178afc43e,9998419,4174,4158,11956314,4172,13768310,0x524a1ca437d5474462d4,4177,4987,28196304502,4173,4163,
61393686004361,29062169876,4181,0x1a437d6c428e60e,59520249800310,4145,13767842,0xd2178ea02c52fa4a2,4191,4163,14636231,61392852862473,4168,57754336085154,29975176610,
11509845,11460717,4179,4165,4210,4765,29974709544,29096174351,4187,4177,92651459622830273,0xbc788d611462fa51f,4177,4163,51962944902330,
29976909218,4140,11956338,10170436,4184,4180] (by decide +kernel)

private theorem part399 : Refutes moves 0x20400000100000000000000000000 0x19499c304004001040820400000100 :=
  branch 1 0x20400000100000000000000000000 0x19499c304004001040820400000100 108 0x1d49df754004011050821400000100 (by decide +kernel) part400 part401

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part404 : Refutes moves 0x20040000110000000000000000000 0x1c5f851a7445400415828240400111 :=
  finish #[
96816422217213091,0x5e6d81b1a75f34df952f,4124,8443626,14160407,0x1b1d63450cae6ea,4157,13766739,4158,28191524586,41309384385953,13295660,0xabf5d40b620442438,5866,30950482098,
12410941,4169,4151,4147,11752735,20591464663,4191,55481779183831,4147,5423,0xc3f95e156572e6352,4150,10170429,4184,4660,
0x8ed12a61612d21088,0xc3f30aedec68553b6,4191,29021102292,57747710436655,4197,4157,61453101168027,13295829,10170451,4208,4190,0x1bf8312fcd2159b,9200839,0x3622c0dfc04d471dbbc9147,
4165,4147,4660,4660,46214557229888,4147,20834292902,43793906939291,21295665670,4158,4150,20833821895,4157,8729903,4191,
4179,4190,4184,4631,35874764547588,5757,5636,22617318129,4175,4179,4189,4147,0x5e98335057f2c4446429,13296180,4179,
27158839357,4155,4159,4177] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part405 : Refutes moves 0x20040000100000000000000000000 0x185f05186014000410820040000100 :=
  finish #[
5641,63388419634464,9125942,28137444646,4139,30032019983,4191,5641,26164871886,12849247,4625,5425,0xa4d8830bc890b444b,4165,4159,
23409123401,4157,8741841,57742263006502,4175,0x1b100dd35d21515,0x1a43632c43d63e9,40054513939534,4175,12849225,4142,30037016979,17274201381,24498266529,14643267,
0x6526690f2ede57521266,12849202,24488128578,4180,4196,28198098445,0xbcd93d6224d4b0529,12849222,0x185d45a2093c340,11473110,46085545640717,4205,4175,4193,55611917808502,
5414,29994189902,14210328,20588324120,4183,4189,4165,25423737351,0x17ad7dc18caf113,4145,4147,0xca5bf8156fb9b3518,28197679192,4156,4180,
29993136343,28198954616,13221955,0xc3893801571af160b,4147,0xca776ebb97e4412ec,4142,4234,8418814,27089438439,4169,4163,59553341056285,30922073609,37231791145027,
26316357715,4199,55779623978389,27042305327,23534506043,0x1b1b1097e4413e9,53922356434441,98962876049355596,4210,61420335273378,22149858263,10960947,4157,4169,4163,
29991847431,8742306,10170461,11956312,10616916,4197,4207] (by decide +kernel)

private theorem part403 : Refutes moves 0x20040000100000000000000000000 0x185f05186004000410820040000100 :=
  branch 1 0x20040000100000000000000000000 0x185f05186004000410820040000100 76 0x1c5f851a7445400415828240400111 (by decide +kernel) part404 part405

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part407 : Refutes moves 0x60000000100000000000000000000 0x197d4e105014000000c60000000100 :=
  finish #[
5206,0x194f621eac46514,14651493,74333733377938518,4122,21715095814,5416,55484815700737,30008242237,4163,4832,8786656,0xc9fa412b9e621c448,4168,0x9d52428712f93044d,
4187,4181,25092384043,4625,21714199848,4147,4177,30947632425,0x9f69670e253cb267d,10539051,8785987,82762928516895819,51389205189939,52014480454286,4168,
10031171,4146,4158,4190,4178,21116179101,17998471766,4135,21387044475,29063041553,4145,13767186,4146,4158,28195296890,
57744090863226,4199,0xdf593af1d0e2fa1a2,4191,4163,13768310,14636450,57751400961654,4166,4177,13768310,11510424,4191,11956291,4148,
4156,4745,57625233494507,4162,29977404610,52047877285385,4148,13296487,27231060839,4169,4153,10616893,10519840,13767082,55838939964611,
12849206,4162,10519829,4967,59601329505342,12849245,28196339778,4207,0x5689f6beb105dc52116f,61392813167018,27233433102,4166,4168,14205141,0x1882b982a220676,
4197,11509851,4184,4191,25436487898,5073,10539537,17977184343,10170473,4196,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part408 : Refutes moves 0x20000000100000000000000000000 0x1c4d44104004000000820000000100 :=
  finish #[
57748851265971,11343369,29062145072,4156,52041232188157,12849233,48312362104101,4158,4193,0xa61a437d62086044e,10617057,4177,9277541,5423,29977874850,
61390983501103,4174,4187,5423,57754334164271,4187,0x16cf7d690ae64a6,4204,4199,23576860167,53899646096360,13295724,0xafa2bf2bafaa204a6,4187,4177,
73936686448390780,84832291227813158,0x192e0dd7d5fc4c7,4191,4177,4317,10560142,13295693,4201,0x4035f959484afe4ae27c,5403,21626086687,4161,10540308,12386525,
4189,12849209,4162,28198573137,26317943889,10052911,4183,11510199,4184,4205,36773111796807,12850257,8766099,9597033,10616905,
4197,4187,9277516,10178672,4190] (by decide +kernel)

private theorem part406 : Refutes moves 0x20000000100000000000000000000 0x184d44104004000000820000000100 :=
  branch 1 0x20000000100000000000000000000 0x184d44104004000000820000000100 114 0x197d4e105014000000c60000000100 (by decide +kernel) part407 part408

private theorem part402 : Refutes moves 0x20000000100000000000000000000 0x184d04104004000000820000000100 :=
  branch 1 0x20000000100000000000000000000 0x184d04104004000000820000000100 102 0x185f05186004000410820040000100 (by decide +kernel) part403 part406

private theorem part398 : Refutes moves 0x20000000100000000000000000000 0x184904104004000000820000000100 :=
  branch 1 0x20000000100000000000000000000 0x184904104004000000820000000100 106 0x19499c304004001040820400000100 (by decide +kernel) part399 part402

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part411 : Refutes moves 0xc00000100000000000000000000 0x12539433c000005060000c00000100 :=
  finish #[
59512577557780,4310,29059335586,4169,57422459766393,13231522,11968726,0x1a20d928d0b6201,4165,4169,61436505628951,4143,4135,4159,4151,
27099686518,8630912,13766719,23408697866,5646,14168352,59606881772957,4161,4151,14188611,38357333992427,0xdf7312d5257124367,4154,27235676581,41996782220918,
0x805181620924b320b,4151,8757325,4195,4193,4186,4197,4333,4333,61383735300333,18086208572,4193,4192,4187,0x37dd65d7d9652bac3cb3609,
8757485,4192,4277,27276743500,13230118,0xd8acd2b2efad21529,0x831b159a565c44514,4155,4145,0x193c0d257521674,8758902,4192,10584155,4169,4179,
4333,4333,4761,0x81093b7f10c35c52b,4161,61513939637203,0xcb24312cc3605a0fc,4197,4187,4193,4195,0xd8abeb7ce2306c4c5,55777776026815,0x1afb7d5ae06c20a,0x6c1b543292bafa85a0ed,
4187,4193,4190,29100525065,18091639999,53982345479691,49831670554861,4190,4193,13766747,11509798,4170,4177,4205,0xcae6c9609b3a61352,
0x195cb99b3a222e2,0xdf70a6985b385a185,4191,4187,29973750760,61384388748264,4191,0xd0a57cd7e1cd210b57d50ca1e367,4175,4170,0x1b1148565c4659d,5282,13747179,9585826,4157,
12419127,57657168495003,4173,4171,73911519100462710,13767500,9175351,12345425,4171,4135,55863637357647,0x5d9d88beb0e690c35280,11956282,4164,51956467492116,
4987,23574225896,4175,8831050,10170477,4208,4180] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part412 : Refutes moves 0x800000100000000000000000000 0x124504124000004020000800000100 :=
  finish #[
55772085519186,0x734ac400d111d79fa458,4139,0x178b27ec41b325d,4208,59620091004180,5646,23123887174,4163,4129,10031533,4146,98180988581655970,12849264,4162,
53948443096591,47359651111476,23578235968,0xcb218eef6c73d8215,4208,4189,26318630979,4156,11511081,0x1949106fc4444bf,4159,53785843123155,30034784685,8736828,4183,
0xc415fa155781b35a2,4208,26315428840,0x9030b6bf6c4367270,0x1b1a75220d886ce16d7b2e852f,4152,4201,0xcaea432a5b392a4c5,57750678561195,8761560,4189,4191,29976958227,55699689166112,4166,
19706869154,22352176200,61392808153131,10170461,4208,10616920,4197,4187,28199015715,4409,9127214,4159,4165,28198129985,61512070784418,
11407433,0x95fa431050a21e104,4190,4195,29058925647,57743154074917,4167,5863,18723718670,4183,13767876,10616870,8831072,4207,28197679984,
13767876,28138443392,4153,57741913454202,48228180587933,22375985225,4172,75870657861546732,21601108842,0xc460d8d9d07a2237e,4189,4199,4205,4190,8832087,
10568336,4195,14664891,42206613140344,4173,85766881084359317,11956335,10170444,4192,4196,61458784633118,74322495932436968,11383317,11412129,8831067,
12849263,9277536,55753218086407,30036059444,0x1a157f254cb33eb,43620151427601,4189,13295679,0xae695d10690a201a8,4187,0x1b1d629a0c2b52f,29113377958,0xc26afb1050f21d67d,4189,4199,
4316,13767846,8762019,4189,10616941,11956315,4180,19001987148,4190,4198,4210] (by decide +kernel)

private theorem part410 : Refutes moves 0x800000100000000000000000000 0x124104124000004020000800000100 :=
  branch 1 0x800000100000000000000000000 0x124104124000004020000800000100 106 0x12539433c000005060000c00000100 (by decide +kernel) part411 part412

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part416 : Refutes moves 0x41020000100000000000000000000 0x1bcb4f517050810814441020000100 :=
  finish #[
0x166d5ff3352152f,0x1a4399a1a3d8676,4154,29060810145,22568035849,4165,4183,0x1afe24c4eafa450,59522086859511,13297058,4135,14189213,0x1b0962290926260,11509823,4163,
0xd842c34850e055609,4187,4183,4191,29976957351,61480582201607,0x16c487220afa3c3,4163,4205,19583472510,91083363404731695,0x1beb63220afd596,98992352934782473,4189,4163,
4205,4187,61394691297906,8737659,13295711,4745,0xbd024d2b97d4414af,11468866,11382861,4153,4202] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part417 : Refutes moves 0x40020000100000000000000000000 0x12db0e115010800804440020000100 :=
  finish #[
46122652976431,0x1b109349644160d,4162,55777689126081,9618944,4189,0x1bf3622572db4b8,4132,8733560,20177073455,40341361476911,4189,86777049441666221,25398133586,4696,
29052404347,8732747,4189,4177,23541567603,4159,4187,4181,98976031752279115,0x1beb99ec612c37e,4171,29976957801,4152,0x195d7e6fac4144b,14635895,
12850806,4162,14636107,12862767,23365320777,4145,13766733,4158,93299976125629743,93299970415751817,13766713,0x175f60e575f567a,29976957458,28197158978,4152,
0x19316364cadb5a2,5632,17887647232,4173,14635099,0xd88b1aba2fac415a2,29976957815,45552974648738,61392811688466,0x18449dafaadb603,48337987485753,4171,4183,4174,11509826,
4177,4191,4170,13296045,29058486701,4181,27008755106,0xac4b1d2b82a9915a2,4150,4158,0x1762b10fd521347,43819681011215,96994462804173099,35191305511395,4199,
0x39a568d210134528b3d3275,28194460431,4187,4181,0x157c75d2cd7c6d4155e1bd560f,4141,4177,12849231,4132,13271821,5423,9618735,4165,4159,59597684139426,
59607982085423,9618735,11509847,4177,12849247,53906047636186,26321310426,53898291533430,0xc413ed25c2acaf2da,13766705,4158,11956319,4148,4156,55769056810618,
11957090,25111122546,4168,4175,27232322066,30923978146,4156,9499171,61513097340305,11904181,4183,4159,4175,0x2b12c4ae1beaf564f4a92eb,4173,
4163,5538,5423,28992710262,61390980785455,4205,4191,4163,9598228,0x1a437e493afd3e8,4159,4166,24491255414,24491255414,50153427150104,
11510760,4163,4191,23373742189,4153,10170453,4208,4196] (by decide +kernel)

private theorem part415 : Refutes moves 0x40020000100000000000000000000 0x12cb0e115010800804440020000100 :=
  branch 1 0x40020000100000000000000000000 0x12cb0e115010800804440020000100 108 0x1bcb4f517050810814441020000100 (by decide +kernel) part416 part417

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part419 : Refutes moves 0x1020000100000000000000000000 0x1ec945506040810814001020000100 :=
  finish #[
10069629,0xcaeb10f40cd3ac18f,4145,35884340118228,9078397,29059818579,4179,51998168184330,19559646295,52062965515785,4139,4142,14172209,4169,4151,
13297277,0x80c759622f9bcf088,4208,0x6495881377cc9257f2fb,4151,37716017840390,0xbb7b112a4792f1451,29027254897,4169,4163,59455167800841,29027263239,8736847,4191,4183,
4193,41947079775515,10069275,4171,14189855,0x1b08bbac452109d,4158,29060350838,4168,0x195c8717e0553eb,4187,4193,0x1752f5a572f80c1,14188719,5209,
29063066696,4173,4163,0x1b190d2c492352d,51528804229901,10485865,4165,14635107,5747,55312007250986,4169,11518593,4193,0xbc72152a5e79890a0,13766714,
4158,5538,0x1a42802572f84b1,4168,23532725331,4765,44471444629001,4171,8736831,11509851,4191,4205,4170,12849894,4942,
55569760698544,0x6fca0026d2bd7d5f5523,4184,43365468967423,10487301,20657202353,4189,4165,4159,13766729,4158,0xdf9101296fe4ae2e6,76478205849855170,26320441840,0x1882801432fd589,
4180,4159,4187,13297277,5314,0x1bf5105e6a8030f,13295725,53904266981872,4173,11382875,4153,10178665,4202] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part421 : Refutes moves 0x10020000100000000000000000000 0x16f915354401800805010020000100 :=
  finish #[
47386496996217,74322101657084159,5757,51597104325034,4174,4177,90590818432394088,89676025622570511,89676025622005263,4181,10544062,4159,11502443,4161,4175,
12849235,4142,76609509778526704,0x3621e92fc58cbc620afa44a,4177,51445668398014,10884290,0x167ab464cc92676,57524160095514,4159,22292538562,4165,4201,4174,12850806,
97440547839395010,4179,61388782511732,22289773430,4165,4174,0x1883265e636a678,10544765,10544655,26316304571,4171,10883141,11509838,4163,11956305,
4180,4156,15110533,59604944114293,4183,14627100,4154,5423,23533175444,4165,11509843,37413373219092,28194459924,0x1b0162097afa30f,4198,
4191,93507440205291955,57746081685754,0xa4f0f34850e92f4a2,4171,4165,13767327,11519606,28196332409,4195,4165,4175,4179,4834,36294904206203,
4170,55778651128546,4179,11937400,11502895,10883155,0xafa8577d50ca1e1b3,4170,11956323,4164,4180,35982888113212,5207,97444030430066301,4140,
47882798789701,4172,98075104478762026,5538,17894122311,10588230,4185,4195,4175,4971,0x690ca3bf57f029bc034f,10522711,23558780070,4172,29063046562,
55772175930119,27232523458,4158,25414472994,0x620cae942f5509b675a2,4164,4159,4175,10609310,4185,4195,10178643,4202,4190] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part422 : Refutes moves 0x20000100000000000000000000 0x17d904104000800804000020000100 :=
  finish #[
90756650899113016,29961520871,13316964,4185,0x1be7635e958c609,4169,4151,41740919611606,4170,86225948089914529,13297165,25295651347,4136,4190,90780685707703158,
24488128581,4180,20834292712,4761,44397975753922,4166,0xe66882eca4d35a2dd,55428400685804,10547288,4180,0x32a6fb92d4d6861712e9609,4153,4160,0x37ea1320e59ab6cda8d967d,4198,
4202,0x1b1a9905819a51b,55432355300873,13181180,0x19252b2c45f5608,4170,18501809673,10068024,4187,4151,4635,23474808226,4151,14189986,5641,
13767178,4170,4151,59522083267078,4168,4173,4193,28198143057,10580507,24488128602,4180,47644971889534,0x16cf7e25703b609,27247878204,4635,
19659416770,4157,40262484833346,4180,0x19480ed7e1b3601,14189108,50108378592342,43969605444148,4151,13766719,11386918,4161,4193,10178906,4198,
8831082,4211] (by decide +kernel)

private theorem part420 : Refutes moves 0x20000100000000000000000000 0x16d904104000800804000020000100 :=
  branch 1 0x20000100000000000000000000 0x16d904104000800804000020000100 112 0x16f915354401800805010020000100 (by decide +kernel) part421 part422

private theorem part418 : Refutes moves 0x20000100000000000000000000 0x16c904104000800804000020000100 :=
  branch 1 0x20000100000000000000000000 0x16c904104000800804000020000100 108 0x1ec945506040810814001020000100 (by decide +kernel) part419 part420

private theorem part414 : Refutes moves 0x20000100000000000000000000 0x12c904104000800804000020000100 :=
  branch 1 0x20000100000000000000000000 0x12c904104000800804000020000100 114 0x12cb0e115010800804440020000100 (by decide +kernel) part415 part418

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part424 : Refutes moves 0x8000800100000000000000000000 0x127ba414608062002200c000800100 :=
  finish #[
5055,9606771,24492593215,61386168021823,25393537659,4169,4157,14636008,29978297320,24230318451,13295697,13766717,4146,23090827994,24492594594,
4156,19431990248,24491725633,9610087,19431990248,10059819,4177,4173,4157,12850152,4162,4132,29096571619,24428843410,24488128575,
12850152,27266958530,61454893659554,4196,4184,0xbd595c93d732fd677,98180605165740752,4139,11523375,20446171856,19521471776,4177,0x4eba08b107ea53cb21aa,4139,4150,
11956281,5641,47943719109609,4164,24490808841,4132,48234909193512,4153,59517435590149,11436120,4152,4173,4202,4208,20834715143,
40092514746932,4177,0xd88a1c988901b3457,4660,24428844778,11956305,4164,13767656,29062144426,0x1b10661b3b48457,4157,4522,0xc44b18ebac43d6600,10625097,0x16d12b911358609,
4157,10567763,4190,4185,4195,5286,59522086004235,10170418,57745912448303,4169,0x1883252c411b457,53897705214440,4193,11956788,0x9ff5fb484d9a1e609,
4185,4180,4195,14189986,12850697,11956270,5314,21546407433,11494694,28196243066,10522681,4169,9277518,10178672,4198,
4202,4210] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part425 : Refutes moves 0x800100000000000000000000 0x12e924104000020020004000800100 :=
  finish #[
0x188cb11b3d213b5,55767286362949,4162,0x56211a6cebbe572fd676,4181,8791016,4199,53897496278088,61393723331180,59412228809324,26316845113,10616932,4192,4935,13768423,
28197167614,0x1a43608d9a224a6,10522718,4164,4179,15098352,59522964984676,27191046223,25385710889,10625454,53897749492357,4164,10616935,4192,4172,
42136055615665,53894055826408,4196,55812081980613,57744591639850,74181239984808669,0x17a52a5e6afd5a2,4173,4208,4187,59487726153921,0x96fa427ac952200f8,12849243,4172,44531027121782,
10178668,4190,4198,4210,93824103252578793,93816526887440929,4181,53897617086070,77913185015726367,4166,44212940387624,10616932,4192,57357414990667,5319,
9580937,4153,4165,51954369492276,0xd8488cf3e10124135,4157,4163,0x61558131311ac158c7b1485b39b318b,4204,0xac01f8da2fad21609,26316845700,4208,55480965874091,26316846387,4208,
10616875,9281642,4199,4662,45451774482040,21721220401,10178629,43711848031650,21343732587,20847824965,4164,9281629,23502291124,4277,27092615807,
4173,25371993047,0x1b109a1ec11b4c7,4157,4172,4163,0x8b44d0955655f516c,17688564346,23440883774,23561459208,61390048675103,0x80e2472b2fad8836b,4147,4144,11961305,
4157,28198142372,28197241711,10485857,4145,12797099,4139,4195,9281605,37954451784885,0x8f35941d6909eb597,10617271,12849243,4172,10540226,
12849806,22367027841,10092588,4177,0x16a083620cae2eb,10540226,55770423255928,4177,4167,9281627,10178665,8831082,4208,4210,4211] (by decide +kernel)

private theorem part423 : Refutes moves 0x100000000000000000000 0x124924104000000000000000000100 :=
  branch 2374 0x800100000000000000000000 0x126924104000020020004000800100 111 0x127ba414608062002200c000800100 (by decide +kernel) part424 part425

private theorem part413 : Refutes moves 0x100000000000000000000 0x124904104000000000000000000100 :=
  branch 1 0x100000000000000000000 0x124904104000000000000000000100 101 0x12c904104000800804000020000100 (by decide +kernel) part414 part423

private theorem part409 : Refutes moves 0x100000000000000000000 0x124104104000000000000000000100 :=
  branch 1 0x100000000000000000000 0x124104104000000000000000000100 107 0x124104124000004020000800000100 (by decide +kernel) part410 part413

private theorem part397 : Refutes moves 0x100000000000000000000 0x104104104000000000000000000100 :=
  branch 1 0x100000000000000000000 0x104104104000000000000000000100 113 0x184904104004000000820000000100 (by decide +kernel) part398 part409

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part429 : Refutes moves 0xc00000004000000000000000000 0x12535457c100000140060000c00000 :=
  finish #[
10831485,23216119983,29041668151,8697244,13743740,4704,9430653,0xcae49d420ef963597,15111687,4130,4136,4134,0x1bf83f88aca8524,4151,13743080,
4164,4156,4148,4140,59621452854795,38218038264555,45327801693821,10076244,4157,4165,11912141,27232945679,0x195d63af9af2607,4155,11514845,
4164,4197,24463762825,0x8173df24d3b669677,4129,4979,13276019,4163,21678379063,4174,4199,55443978330725,45418277364712,14156545,50159961014548,
4177,4165,20129624336,8716958,4180,4179,55778710201865,24449291550,17893257294,4192,4191,4187,13743262,0xbb5af92b828367609,4180,
26363282387,12871293,0xd88bf8d8a9034c60e,0xb4cbf92768da1d215,4179,4189,4169,9159391,28147778730,28145996970,4179,27007770727,8831021,4205,27003692444,
24382182697,8831031,4333,53842619024691,0xe695c946d7d86c5a1,8757485,4187,4193,4199,24521683045,4192,4208] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part431 : Refutes moves 0x20400000004000000000000000000 0x19495c744100100040040820400000 :=
  finish #[
5532,25370719199,4180,19632911877,23133192955,29060817751,0xd20a10b3ec4367131,11961647,4187,4157,11490159,4158,4165,4179,13743171,
4140,4859,4820,0x1a212ba8d9244c7,4187,0x5dacb395d46d29a7a372,11460657,14151749,25402938880,48252040147799,28144108409,10621019,28146881512,4158,4179,
0x1b10bc50d21f455,4171,4183,4191,4193,49623687394825,52029565886954,4179,0xd7f95d0c4b4bd4433,46394566038835,11486376,4157,11486376,53626593837546,4174,
4165,4207,4183,0x186346ec705a678,5633,29108839478,13295707,0xa67aff46c2d21560f,4161,4181,0x1b19639ea2c752f,21670830299,4207,0xc9fa363110fa2160f,4181,
4183,4191,0x183a87e8db671ea,0xdfb4cf46db3c3d303,4168,4148,59519183990992,25296135581,25294324489,4183,0x17b1116beafc609,25404289107,4168,4315,13743084,
0x17b1631773d4436,17893265470,4185,4191,51345328869911,5423,29059802071,4183,4197,52032524301615,4156,5629,8758430,4197,53481690874738,
4168,11519166,72640650730098907,10571865,4181,4193,48269222249984,98470208025507114,14152559,0x5d6446a376209227a600,4187,0x1b10f528da1a36f,4183,4181,11972705,
10170424,4204,4184,4192] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part433 : Refutes moves 0x420000004000000000000000000 0x12c955544310800040940000420000 :=
  finish #[
0xdf257d7f2fb92459d,0xd0a7817e21728e4c1,4183,5420,55719427995252,4180,4204,13742350,59615330068093,4156,43776291747331,0xdfcb039a130b6752f,4156,4204,5532,
30037038383,30033265970,4183,49471808484989,11489364,11501630,4175,4179,10436822,76391380660707542,13742135,0x1b1d2b9b3d1b379,39422552347624,59402688254947,13295719,
23414822191,29009003823,35761154331575,24080212836,15106120,0x166d2b930b6737d,10625084,4204,11461907,8728631,4187,4181,4184,4180,36552546013555,
0x6c73bba3694efdcae67d,55725280015881,4181,13742451,30001242749,4191,24462349245,57648486740971,4195,4165,13296505,5423,13309231,28144103493,4181,
11956307,4156,12402796,4149,4185,22367397491,0x29a800668beecdafc2d519c,4175,23267411343,4199,5165,5757,53454537827030,12320823,4183,
4156,0x6c62cc88b7cdb1d1b67d,4152,14206584,61513985225366,4171,0x1bf8eb09236b679,4160,47492500689558,4183,4193,25363555631,13743084,4152,5201,
10068279,4175,5641,0x8231eeb64f4d841e0,20653068322,13227530,27182638043,10621007,8736873,4193,4183,57459301216918,29095580947,37941114545427,12419151,
4145,13742451,40243214767516,4191,8720592,4179,12402775,4149,4185,5757,48201416205395,21420130379,29063491895,0x1cd146ec40555fd,59517479335215,
4168,25401147489,4211,0xc27b0362258bd43e5,19725100003,37047106220087,4180,4204,4208] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part434 : Refutes moves 0x400000004000000000000000000 0x124974544100000040040000400000 :=
  finish #[
25388847530,13218000,25388823836,52027030746524,4164,4169,4185,57640910910549,4725,0x194146d04cb13e8,4187,4300,90588909396800812,11477060,4185,
9281644,4207,17829807303,0x405aee2d307413b60595,4304,19633340624,4163,4199,4189,5319,52032559252671,4189,8712398,11972695,4168,
18317685918,4508,0x9a04d4d4223360092,4189,4181,92650684700332921,4750,11502899,49762081833849,4181,11972701,4192,9281608,4201,4333,
5423,11928521,4189,0x195746e53c9b44c,5404,0xa0d862f517a3cd528,4169,4178,4183,0x64ddfb4cf0f68db67457,4148,24486789467,10170479,4192,4204,
9724016] (by decide +kernel)

private theorem part432 : Refutes moves 0x400000004000000000000000000 0x124954544100000040040000400000 :=
  branch 1 0x400000004000000000000000000 0x124954544100000040040000400000 101 0x12c955544310800040940000420000 (by decide +kernel) part433 part434

private theorem part430 : Refutes moves 0x400000004000000000000000000 0x104954544100000040040000400000 :=
  branch 1 0x400000004000000000000000000 0x104954544100000040040000400000 113 0x19495c744100100040040820400000 (by decide +kernel) part431 part432

private theorem part428 : Refutes moves 0x400000004000000000000000000 0x104154544100000040040000400000 :=
  branch 1 0x400000004000000000000000000 0x104154544100000040040000400000 107 0x12535457c100000140060000c00000 (by decide +kernel) part429 part430

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part437 : Refutes moves 0x40020000004000000000000000000 0x10c747515140c00000900440020000 :=
  finish #[
0x476087795441dc58e6e9,0xa82cd17ec4392c532,4171,0x4796685b7632c42f752f,4208,5641,59587006334256,0x1b18822c0bb4609,13295691,4135,11522884,10961629,13295695,5865,10458165,
23551636231,4211,8732739,4189,4187,14660316,14189517,0x1b117ec963b460d,4171,36544048349555,4187,12402781,4149,4185,13743298,
53904217556271,53904217555676,28144125013,4181,4187,4185,13743298,53904217555662,53904217556604,28144125013,4181,4187,4185,26319078108,0x1bf963170a5b352,
9618140,4189,97011736350900437,4158,28147363917,4168,4208,4152,53661653906517,26018427989,23538782882,4183,4191,8737960,17898255210,
12402744,50218379760290,4173,4160,10170694,4204,4196] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part439 : Refutes moves 0x40800000004000000000000000000 0x12c5f5524140400100020440800000 :=
  finish #[
13742972,0x6fe011b10bbe533b64bb,0xbb6bf77f02daf9609,13742167,30035101198,97048705329386549,4159,8762670,12869737,4167,4187,17944040316,53450225661340,4208,4184,
0x1854d9d7dc4151a,5513,27233002357,4167,29063492663,12850802,43372076053786,63387505325360,9617447,4186,4162,11956317,0xc41a36becd9b6b437,4184,4208,
0xc9d1824aa20ca959c,0x64ec1d88346db5ca91b1,0x1a36dac609b360a,4180,10616944,4187,4172] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part440 : Refutes moves 0x40000000004000000000000000000 0x104d65504140400000000440000000 :=
  finish #[
12403997,45553919383053,13742141,17831593155,12403580,59517218820302,4155,4169,11506773,12403580,98362785955910741,4181,11972699,4152,4184,
14189980,28145779550,4141,48025958323837,4185,52025011319660,12334605,0xdfb77ab3e4baeb269,4162,10519627,11972685,4184,4168,10388533,20589528585,
0xc975bb451462826ea,4201,11972707,52033497368073,90370310182777466,4169,13743084,4152,10616921,4187,4207,0x17690cefe3564bc,13742944,0x734bb492f61101aed1a4,4183,
4185,0xcaecd346d0a85f530,4201,0xcae58a8828dc41182,5314,13312652,4186,52021441205442,4195,11956321,4172,4769,57639211197285,0xd88876d8de9a206ea,4177,
11973822,4312,0x734a20a37105b5a211ea,4181,8786015,4201,10170465,4184,4196,5205,9605328,4177,5314,57645768397909,4184,
4196,59521147356016,23483286504,13295709,0xca05d2f51b3c4116d,0xae47a8bddb3afd2e3,4173,4167,5641,11522940,23600272236,4155,20832497737,4184,4208,
52026969792838,9561133,25436328332,4153,53781216735866,9281592,28144571560,47298529858728,14189381,12833403,8790098,24521683047,4204,4196,10616944,
9724015,4209] (by decide +kernel)

private theorem part438 : Refutes moves 0x40000000004000000000000000000 0x104565504140400000000440000000 :=
  branch 1 0x40000000004000000000000000000 0x104565504140400000000440000000 107 0x12c5f5524140400100020440800000 (by decide +kernel) part439 part440

private theorem part436 : Refutes moves 0x40000000004000000000000000000 0x104545504140400000000440000000 :=
  branch 1 0x40000000004000000000000000000 0x104545504140400000000440000000 101 0x10c747515140c00000900440020000 (by decide +kernel) part437 part438

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part442 : Refutes moves 0x10000000004000000000000000000 0x144546304500040000001010000000 :=
  finish #[
12402976,36532628075125,4128,93507338954346703,4192,0x2ec6fe4420eb7ddea51b456,30941202040,4985,0x478804cd10b83d4b11b3,19749738217,4185,30032929203,0x1a397f17e28e455,4181,4175,
4201,4211,12337917,44227220808439,11502223,4175,14188627,12849203,4192,14189146,0x1b10b189920e58b,4174,19576423507,0x932698d9130bd452c,4149,
4185,0x2f256358e4c24ca8da0e609,44227397531252,23500047772,4185,12849217,11956280,4156,4196,29063492477,59522036544381,23072687391,11011592,11067453,4183,
11956315,17478292675,25406505597,53900556501082,0x1b0cf5220b67099,0x838b0ebba8dafc595,59498899444796,4142,53900556502094,4204,10616941,4187,4192,12849802,26318632457,
4196,25406058843,26318632457,4196,12403906,8782706,4196,14185337,21595845826,9281644,10616947,4187,9724015,4209,4197,
13296940,0xd1b49a27d6b21d30d,4205,44489648796970,4196,57650327508604,0x85b5f77ee8da1d30f,4199,13743080,0x37f167d86bf6d9e8dcae26c,10616893,47701366780441,5409,49929267701022,13742189,
55823782277795,4148,17946358184,4157,4183,12849255,4172,4192,0x1bf61828dcae3c2,0xe68bf8becfa9907a946e5722036c,21746684988,24167973086,26318631015,4196,4172,
0x1a37106c34ae67c,13309231,0x188288a5034e59c,4195,4187,49506171016168,0x17acb768dc4167c,0x17a8b59b3a0944e,4184,4179,4169,0xb41a36881048da3e8,9724015,4209,10178667,
4190] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part444 : Refutes moves 0x1000000004000000000000000000 0x15454c1c4100000400010001000000 :=
  finish #[
0x1690f50bfd1b591,5641,57456581912189,10571843,4166,10613403,4183,13743262,0x1b14f52c45f9a370751021a28c,12849247,49318104937291,5308,89533356675417258,4172,4189,
93080798025827415,14189767,0x563bb7b11619104b2455,4183,0x1b108810aa1f3c9,4181,4191,11972713,4168,4192,13742592,12244267,22571631774,27198538049,4175,
14665225,21276164867,10489925,4141,11464779,4166,59541101122972,11043690,12869719,28146914161,4173,4167,57644649317570,0x1a3762220b6b34b,4184,
5100,8709278,0x5dbdfc93946dd6b6b09b,23482847304,4166,10616917,4192,13743262,0xc451b4bc571b6b4a8,4168,24522958236,53335400002411,4183,40241562756041,10616937,
9723985,4203,10178673] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part445 : Refutes moves 0x4000000000000000000 0x155544104100000000000000000000 :=
  finish #[
86368760626681344,0x414ac595d106fdb6b600,13742168,53905066144822,86363037935125237,52099426121229,4189,12402761,4158,0x6fd58c020641ea5fc36c,5100,13210249,13295678,4168,0x7344995da8213b4ae67d,
55774037390316,4162,4171,0xdfb3c27d6fe2086e9,30036124053,14664310,22419268365,4201,11391069,4141,13743084,4152,13743084,11515292,4169,
10616921,4187,10178661,0x1a376202586c19b,0x194846a5684e2d7,18723816405,4207,4333,28144566556,37045983498561,4166,4173,4195,4187,0xdfcb1146ec32d851d,
0xad812e825db51b609,0xd889551057404e359,4181,4187,23245275574,4207,28147364513,4168,4192,41775229891434,8831646,4205,4333,0x6c051b76d2b90ec4167c,27041838124,
78547692941165980,8831077,11972723,4184,10178656,4190,0x426bd4a36daca31b5532,5100,76481953008379407,0xd8e5faf51a5362589,4185,55776822866807,4152,5532,5183,
0x968b1b46da12e8532,4187,4180,28148241493,28147328085,10563681,4169,10178653,4190,0x507220a36dacda9464c2,4197,43975092909219,0x195c227344b1096,4635,24180434105,
4193,4181,4163,12402999,5205,38386978407936,4177,4193,4185,5532,43870067995724,0x1a36dae4aaf7523,4160,0xb64a36f516d2e821b,4159,
4180,4152,13743189,0x16d746dea2f711e,10178645,19914997850,4211,4207,4203,9277553] (by decide +kernel)

private theorem part443 : Refutes moves 0x4000000000000000000 0x154544104100000000000000000000 :=
  branch 1 0x4000000000000000000 0x154544104100000000000000000000 108 0x15454c1c4100000400010001000000 (by decide +kernel) part444 part445

private theorem part441 : Refutes moves 0x4000000000000000000 0x144544104100000000000000000000 :=
  branch 1 0x4000000000000000000 0x144544104100000000000000000000 112 0x144546304500040000001010000000 (by decide +kernel) part442 part443

private theorem part435 : Refutes moves 0x4000000000000000000 0x104544104100000000000000000000 :=
  branch 1 0x4000000000000000000 0x104544104100000000000000000000 114 0x104545504140400000000440000000 (by decide +kernel) part436 part441

private theorem part427 : Refutes moves 0x4000000000000000000 0x104144104100000000000000000000 :=
  branch 1 0x4000000000000000000 0x104144104100000000000000000000 106 0x104154544100000040040000400000 (by decide +kernel) part428 part435

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part448 : Refutes moves 0x10800000000100000000000000000 0x1a415c564114001004000021010800 :=
  finish #[
13766976,14198049,9171701,10625106,4175,5423,28199019133,0x1bec026fad21091,20487061757,49655092609094,4187,4175,0xacba2d279795f5534,0x1b10bcafad21534,4134,
29004796773,0x1bec2fda521e60f,4175,4180,23508328766,38478522820107,0x1a412c6c520f365,10960960,8757297,4187,4192,48150791460118,0xd21bef7d57920f140,4180,47538302674446,
10076677,4157,55774767596741,8736871,11509853,4177,4191,4422,14636226,27059041095,59429433382181,29058945090,4180,29050114374,10616929,
10178661,4202] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part449 : Refutes moves 0x800000000100000000000000000 0x134114124104000004000020000800 :=
  finish #[
17561804968,59614536853003,4157,0x95f66b2b97b5212fb,4134,12850594,4172,76399386531468586,0x1a432b827855513,4189,4183,48330170302785,8741505,13766750,73900330232059188,
26320442994,57750675874465,4189,11972702,4152,4160,61510354763983,98507388054058178,23574216760,57748882150588,4190,4198,36035326673522,44003950625986,8762892,
11522150,4201,8762420,9982584,5641,21394060138,4201,4167,0x187a16ec443143d,4198,28196339802,4177,42078069282067,8754364,42668633010273,
4184,0x1952d2abe4ae607,13295825,0xc468537cc60189604,0xbb3b1ab5a57521609,12865574,12870635,0xca0beb486fb51c058d69b50b8357,8708171,4180,4175,4177,26018452783,0x5a52cc9534860ea22290,4180,
0x684669b147bc604ae3e5,41946110535074,11509844,8831057,4205,26014683418,9950366,9998573,4190,29977874523,5423,4312,48284454638090,4156,28197695570,
10170440,4192,12850594,0x998a43106c421435c,4160,21644670370,13767874,57749671068866,4160,5538,23435183191,4160,28196271298,21747753616,4177,
4197,4167,8831067,20829802607,4202,4210,4204] (by decide +kernel)

private theorem part447 : Refutes moves 0x800000000100000000000000000 0x124114124104000004000020000800 :=
  branch 1 0x800000000100000000000000000 0x124114124104000004000020000800 112 0x1a415c564114001004000021010800 (by decide +kernel) part448 part449

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part452 : Refutes moves 0x30000000000100000000000000000 0x1ccf14544114005000000001830000 :=
  finish #[
0x1bf94724bcaf591,0x195c48290851455,4183,11490586,14188745,55416959018062,8736837,4183,4193,5203,0x1b10f51721fc6e9,4141,25406083829,4122,13767765,
46187714581687,23475348674,8740933,4191,10616925,10178661] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part454 : Refutes moves 0x21000000000100000000000000000 0x1d49d7115104004010000010821000 :=
  finish #[
29977875086,36777718059667,75313269596726344,4205,11972703,13767547,30011429068,61456865404425,12849247,4202,26119115936,28198590070,11972668,4168,12404130,
57746055623660,4315,8753366,4185,4187,10178655,4190,4186] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part456 : Refutes moves 0x20001000000100000000000000000 0x195954144586004100010010820001 :=
  finish #[
5205,26119983828,8786449,43816892167681,14635079,12403319,0xdf588c7d9ea217530,4163,80433154808890548,25406952502,21737115736,4181,4183,4193,4191,
43821522673865,0x2021dac1f492be90fbd46ea,10581077,4173,13766753,0xcb37a90a69099167a,0xa53a42f50631914aa,52042400929513,28196303957,4163,4173,4193,13767178,28198508154,61463411221371,
28196336818,4171,4193,4191,28198589618,4148,4156,4166,4146,12404130,48283655476743,4191,97023813840880916,12404130,0xdf5a42f1c2821f447,
4191,4181,59554299598345,23215761014,11518023,17794462589,11460693,4165,9277523,4210] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part458 : Refutes moves 0x20000010000100000000000000000 0x195d1550454400c201000100821000 :=
  finish #[
10511056,21745395209,46326057214583,12812354,4193,10617479,0xc42b104811036859d,21530076578,4146,4157,4179,29114270903,21394966025,24498266529,12849219,
4162,18829862287,76846047829881809,28199018545,10511778,4171,4146,0xcae01563b34c2260e,0x202ac42bfcd110540368193,12402755,29062960213,5641,0xba895ef52c40c6340,4201,28196339799,
4177,4207,4167,59622400824841,0xd88bf8164c8a20435,4177,61464275248326,5314,49719148487167,4148,10616898,59610734133999,10621587,4183,25401095586,
4195,4193,4201,4198,5205,14189974,4134,0x6c451c0f081ac6bd4531,90311281991619995,0x2edefe51c3f79a1ea3d660e,4147,4183,20587766871,4743,41878356246808,
4177,13305358,28194923822,4189,13304910,0x650d8d6a19a2580c451a,4189,23262230030,43406325245015,36054381912151,4171,4151,13295675,4157,4179,
4201,24295048169,13747393,13305026,9191461,25406055377,25161852098,4171,12412098,4169,4147,4183,0x5a83d492d106572066e9,0x18839a1b43d452f,9192533,
0x1788bac623d6118,4169,4183,12284321,13296696,29993734183,12850808,13296834,10510364,4166,13766746,4134,4146,43530370867332,21255061636,
82203225457615950,4201,41876481773623,12850697,61427167819170,12402767,4140,23391454402,53899544585301,4163,0x89c884d821b3d40f9,4743,13714055,12846039,27988739267,
11010085,4175,4157,44094563030101,0x195c029ea441373,0x1a4281a20aee35e,25346007130,4160,4165,4169,10616937,4197,4207,9277516,4210] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part459 : Refutes moves 0x20000000000100000000000000000 0x195915114104004000000000820000 :=
  finish #[
28194464254,12403567,29972854178,4197,17895105621,4181,4198,29977874651,57754351343222,11519146,4207,36735117563298,4181,11972690,4168,
29977875654,14636450,14636450,29974701254,4201,4193,11972703,0x650bd4bee57e90c41432,8742634,0x1934bc9e92dd60b,22376001609,4160,57750679105981,29077988546,28194464853,
10616921,4197,9277551,4210,10170474] (by decide +kernel)

private theorem part457 : Refutes moves 0x20000000000100000000000000000 0x195915104104004000000000820000 :=
  branch 1 0x20000000000100000000000000000 0x195915104104004000000000820000 88 0x195d1550454400c201000100821000 (by decide +kernel) part458 part459

private theorem part455 : Refutes moves 0x20000000000100000000000000000 0x195914104104004000000000820000 :=
  branch 1 0x20000000000100000000000000000 0x195914104104004000000000820000 96 0x195954144586004100010010820001 (by decide +kernel) part456 part457

private theorem part453 : Refutes moves 0x20000000000100000000000000000 0x194914104104004000000000820000 :=
  branch 1 0x20000000000100000000000000000 0x194914104104004000000000820000 108 0x1d49d7115104004010000010821000 (by decide +kernel) part454 part455

private theorem part451 : Refutes moves 0x20000000000100000000000000000 0x184914104104004000000000820000 :=
  branch 1 0x20000000000100000000000000000 0x184914104104004000000000820000 112 0x1ccf14544114005000000001830000 (by decide +kernel) part452 part453

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part461 : Refutes moves 0x20000000100000000000000000 0x12c914104104800000004800000020 :=
  finish #[
25423282432,22651422217,12849231,0x851112156208bb26e,4184,13201724,29060817212,30033887653,4163,55372287341307,4179,4175,53345066946977,18753353007,92877793171632903,
4175,13766739,4146,27042283720,9156002,18748872098,4183,4184,5314,44479395116226,12402776,4149,4185,4158,4416,
5750,48077500192374,18785214526,4191,27235668176,13768310,4158,0xd884932bafad211a2,0x1798f4e575f5532,5750,52030505882683,4146,11509822,4177,18834215007,
4202,4198,18379993404,84427808575251382,75061084795397046,12849243,4202,11375921,4412,12849591,4202,4187,17398740162,0x1942a397aafc1a1,4165,
13766749,4158,0xdf726c2ee90b6b455,4160,28200358547,28200358547,11495030,4159,11972699,77168583538071158,0x855a42868dab6b676,4160,0x1beadacda8bf5a2,4178,4186,
4198,23245385926,12407650,26116223075,25211781792,17845703764,0x8797a88852f92737e,4163,4175,14635093,5423,0x1b172b9e0c9e67d,27233440843,4159,4166,
5179,4970,0x17752b974a863e5,4183,4205,59567184500015,11523593,11468870,4173,4181,5400,47615470195797,4173,52030696564338,4163,
90897905804306045,0xb625fa13dea2e9454,4181,12825903,4156,13766746,4158,10170418,23475340918,21756577398,10614390,4171,4181,28197696597,4168,
5100,0x614df37a9485b5afa531,8831078,10170477,0x1883485b59b3444,5641,0x80ab0683ec41f7364,12849257,28199912642,14189402,0x17ad6157e20f67d,12849231,13767174,12402738,4149,
4158,0x1883485b59b3455,8831064,9277549,4202,4210,4204,4208] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part463 : Refutes moves 0x10000800000100000000000000000 0x1269b454c154401020020005010000 :=
  finish #[
45657927448182,13767985,45417411470857,41680703362247,59515974488946,76183558576653170,4165,4189,4175,57743109780642,4192,9281618,4207,29087318985,0x16d0f5094c41609,
4162,27118228565,29976511791,0x1beb485e0bd3521,4177,4157,57746588128450,13263275,4193,9609360,27112306294,4179,8713300,0x5d7b687ab62c2792a52f,4163,
9195581,4180,4178,4184,26995307804,0x1b12da095521513,21744164926,4207,40305544012036,93206618839319846,4177,57734395461834,52029781300386,9281625,10178675,
4210,4202] (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part464 : Refutes moves 0x800000100000000000000000 0x136934104104000020020004000000 :=
  finish #[
13766976,17809798430,93009133310185736,9281598,4201,8687823,29075682722,27233435964,9281625,11972713,4168,5421,86148069906232612,4157,12403692,
9281607,0x5a0bd4beb4846d36b370,0x1a437d5b59b54a0,4186,4198,38936928064930,5205,24071377632,4142,29079377083,29078029506,4168,4179,11503116,11502529,
12403906,4140,52025829754050,4177,9281625,4211,26319078334,49433824568950,10178675,4198,4186,18753918227,28198572752,11973826,4160,
4152,9658798,4199,38936928064930,57748882151030,4186,10616934,4187,4172,4202,63389334955526,0x1a219a6facab609,4171,4304,12297846,
0xbbabeb29827b50093,4157,12402765,4185,22218847645,0x3999ea43394162290afd60c,4173,9634686,4184,4166,0x16c129afacae2eb,5319,26101867363,55766521205154,4180,
4181,48336153166032,4158,4167,9281763,4199,4207,5644,0x7349298532c690b686e7,4173,0x34708658b940ba5ea441591,0x1882446c42f72ca,0x7332f2b1107e20bd4219,4185,48110056379695,
4146,4173,10616903,29089551445,0x17a8eb2fa86260c,82760541218820505,10616914,57745192956015,4184,4192,8831540,23330374137,4526,9647084,4211,
4187,57748884820716,4142,12404233,29062153492,22265021741,4165,4177,25403241993,0xd0accd2a6c45212df,24524361778,4142,0x188248496a20379,8831067,20829802607,
4202,4210,4204] (by decide +kernel)

private theorem part462 : Refutes moves 0x100000000000000000 0x124934104104000000000000000000 :=
  branch 2374 0x800000100000000000000000 0x126934104104000020020004000000 112 0x1269b454c154401020020005010000 (by decide +kernel) part463 part464

private theorem part460 : Refutes moves 0x100000000000000000 0x124914104104000000000000000000 :=
  branch 1 0x100000000000000000 0x124914104104000000000000000000 101 0x12c914104104800000004800000020 (by decide +kernel) part461 part462

private theorem part450 : Refutes moves 0x100000000000000000 0x104914104104000000000000000000 :=
  branch 1 0x100000000000000000 0x104914104104000000000000000000 113 0x184914104104004000000000820000 (by decide +kernel) part451 part460

private theorem part446 : Refutes moves 0 0x104104104104000000000000000000 :=
  branch 2701 0x100000000000000000 0x104114104104000000000000000000 107 0x124114124104000004000020000800 (by decide +kernel) part447 part450

private theorem part426 : Refutes moves 0 0x104104104100000000000000000000 :=
  branch 1 0 0x104104104100000000000000000000 74 0x104144104100000000000000000000 (by decide +kernel) part427 part446

private theorem part396 : Refutes moves 0 0x104104104000000000000000000000 :=
  branch 1 0 0x104104104000000000000000000000 80 0x104104104000000000000000000100 (by decide +kernel) part397 part426

private theorem part352 : Refutes moves 0 0x104104100000000000000000000000 :=
  branch 1 0 0x104104100000000000000000000000 86 0x104504100000000000000004000000 (by decide +kernel) part353 part396

private theorem part306 : Refutes moves 0 0x104104000000000000000000000000 :=
  branch 1 0 0x104104000000000000000000000000 92 0x105104000000000000100000000000 (by decide +kernel) part307 part352

private theorem part238 : Refutes moves 0 0x104004000000000000000000000000 :=
  branch 1 0 0x104004000000000000000000000000 104 0x114004000100000000000000000000 (by decide +kernel) part239 part306

private theorem part142 : Refutes moves 0 0x104000000000000000000000000000 :=
  branch 1 0 0x104000000000000000000000000000 98 0x104000000000004000000000000000 (by decide +kernel) part143 part238

private theorem part2 : Refutes moves 0 0x100000000000000000000000000000 :=
  branch 1 0 0x100000000000000000000000000000 110 0x140004000000000000000000000000 (by decide +kernel) part3 part142

private theorem part0 : Refutes moves 0 0 :=
  branch 1 0 0 116 0xfffffffffffffffffffffffffffff (by decide +kernel) part1 part2

private theorem noGood : ¬ Good 233 16 := by
  rintro ⟨c,hp,ha⟩
  exact part0 c hp ha (by simp [Red]) (blue_zero c)

end Case233
private theorem no233 : ¬ Good 233 16 := Case233.noGood

theorem spectrum (n : Nat) (p : n%2=1) : Good n 16 ↔ n ≤ 231 := by
  constructor
  · intro h
    by_contra! large
    exact no233 (restrictGood 233 ((n-233)/2) (by omega) h)
  · intro small
    exact restrictGood n ((231-n)/2) (by omega) yes231

end PalindromicSixteenOdd

theorem OMA.solution : OMA.R_Green14_W_3_16_R2.H1 := PalindromicSixteenOdd.spectrum
