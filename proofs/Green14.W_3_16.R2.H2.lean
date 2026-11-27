import OMAReductions.R_Green14_W_3_16_R2

/-! The even part of the palindromic breakpoint pair (232,237)
computed by Ahmed, Kullmann and Snevily in Table 6. A reflected coloring
attains length 236. The certificate rules out length 238, after which
centered restrictions give all lengths of the same parity. -/
-- Lean formalization by @KoaOkano.
namespace PalindromicSixteenEven
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

private def differences236 := checkDifference 236 16 0x40120800c01000200d00432008000

set_option maxHeartbeats 3000000 in
private theorem span236_0 : Covers differences236 1 9 :=
  checkedRange 1 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_1 : Covers differences236 9 17 :=
  checkedRange 9 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_2 : Covers differences236 17 25 :=
  checkedRange 17 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_3 : Covers differences236 25 33 :=
  checkedRange 25 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_4 : Covers differences236 33 41 :=
  checkedRange 33 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_5 : Covers differences236 41 49 :=
  checkedRange 41 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_6 : Covers differences236 49 57 :=
  checkedRange 49 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_7 : Covers differences236 57 65 :=
  checkedRange 57 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_8 : Covers differences236 65 73 :=
  checkedRange 65 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_9 : Covers differences236 73 81 :=
  checkedRange 73 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_10 : Covers differences236 81 89 :=
  checkedRange 81 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_11 : Covers differences236 89 97 :=
  checkedRange 89 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_12 : Covers differences236 97 105 :=
  checkedRange 97 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_13 : Covers differences236 105 113 :=
  checkedRange 105 8 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_14 : Covers differences236 113 118 :=
  checkedRange 113 5 (by decide +kernel)

set_option maxHeartbeats 3000000 in
private theorem span236_15 : Covers differences236 118 236 :=
  checkedRange 118 118 (by decide +kernel)

private theorem yes236 : Good 236 16 :=
  witnessOfChecks 236 16 0x40120800c01000200d00432008000 (by decide) (mergeRanges (mergeRanges (mergeRanges (mergeRanges span236_0 span236_1) (mergeRanges span236_2 span236_3)) (mergeRanges (mergeRanges span236_4 span236_5) (mergeRanges span236_6 span236_7))) (mergeRanges (mergeRanges (mergeRanges span236_8 span236_9) (mergeRanges span236_10 span236_11)) (mergeRanges (mergeRanges span236_12 span236_13) (mergeRanges span236_14 span236_15))))

-- Each path entry has a one-bit marker and an eleven-bit progression
-- index. A zero marker introduces a split, a color clash or a blocked
-- progression. The reconstructed tree is checked by redCheck.
private def pathBits : Nat → Nat → Nat × Nat
  | 0, bits => (1,bits)
  | fuel+1, bits =>
    if bits.testBit 0 then
      let (path,rest) := pathBits fuel (bits >>> 12)
      ((path <<< 11) ||| ((bits >>> 1)%2048),rest)
    else (1,bits >>> 1)

private def treeBits : Nat → Nat → List RedTree → List RedTree
  | 0, _, stack => stack
  | count+1, bits, stack =>
    let (path,body) := pathBits 128 bits
    if body.testBit 0 then
      let long := body.testBit 1
      let clash := if long then 1+((body >>> 2)%2048) else 0
      treeBits count (body >>> (if long then 13 else 2)) (.endAt path clash :: stack)
    else
      match stack with
      | right::left::tail =>
        treeBits count (body >>> 8) (.branch path ((body >>> 1)%128) left right :: tail)
      | _ => []

private def packedTree (count bits : Nat) :=
  (treeBits count bits []).headD (.endAt 1 0)

namespace Case238
private def hints : Array (List Nat) := #[
[18564],
[],
[],
[18091],
[],
[],
[17618],
[],
[],
[17145],
[],
[],
[16672],
[],
[],
[16199],
[],
[],
[15726],
[],
[],
[15253],
[],
[],
[14780],
[],
[],
[14307],
[],
[],
[13834],
[],
[],
[13361],
[],
[],
[12888],
[],
[],
[12415],
[],
[],
[11942],
[],
[],
[11469],
[],
[],
[10996],
[],
[],
[10523],
[],
[],
[10050],
[],
[],
[9577],
[],
[],
[9104],
[],
[],
[8631],
[],
[],
[8158],
[],
[],
[7685],
[],
[],
[7212],
[],
[],
[6739],
[],
[],
[6266],
[18564],
[18091],
[5793,17618],
[17145],
[16672],
[5320,16199],
[15726],
[15253],
[4847,14780],
[14307],
[13834],
[4374,13361],
[12888],
[12415],
[3901,11942],
[11469],
[10996],
[3428,10523],
[10050],
[9577],
[2955,9104],
[8631],
[8158],
[2482,7685],
[7212],
[6739],
[2009,6266],
[5793],
[5320],
[1536,4847],
[4374],
[3901],
[1063,3428],
[2955],
[2482],
[590,2009],
[1536],
[1063],
[117,590],
[117]]

private def values : Array Nat := #[
0x80000000000000000000,0,0,0x100000000000000000000,0,0,0x200000000000000000000,0,0,0x400000000000000000000,0,0,0x800000000000000000000,0,0,0x1000000000000000000000,0,0,0x2000000000000000000000,0,0,0x4000000000000000000000,0,0,0x8000000000000000000000,0,0,0x10000000000000000000000,0,0,0x20000000000000000000000,0,0,0x40000000000000000000000,0,0,0x80000000000000000000000,0,0,0x100000000000000000000000,0,0,0x200000000000000000000000,0,0,0x400000000000000000000000,0,0,0x800000000000000000000000,0,0,0x1000000000000000000000000,0,0,0x2000000000000000000000000,0,0,0x4000000000000000000000000,0,0,0x8000000000000000000000000,0,0,0x10000000000000000000000000,0,0,0x20000000000000000000000000,0,0,0x40000000000000000000000000,0,0,0x80000000000000000000000000,0,0,0x100000000000000000000000000,0,0,0x200000000000000000000000000,1,8,0x400000000000000000000000040,512,4096,0x800000000000000000000008000,262144,2097152,0x1000000000000000000001000000,134217728,1073741824,0x2000000000000000000200000000,68719476736,549755813888,0x4000000000000000040000000000,35184372088832,281474976710656,0x8000000000000008000000000000,0x40000000000000,0x200000000000000,0x10000000000001000000000000000,0x8000000000000000,0x40000000000000000,0x20000000000200000000000000000,0x1000000000000000000,0x8000000000000000000,0x40000000040000000000000000000,0x200000000000000000000,0x1000000000000000000000,0x80000008000000000000000000000,0x40000000000000000000000,0x200000000000000000000000,0x100001000000000000000000000000,0x8000000000000000000000000,0x40000000000000000000000000,0x200200000000000000000000000000,0x1000000000000000000000000000,0x8000000000000000000000000000,0x440000000000000000000000000000,0x200000000000000000000000000000]

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private def moves : Rules 238 16 :=
  cachedRules 238 16 (by decide) hints values (by decide +kernel)

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
private theorem part4 : Excludes 0x40062000000000000000000000000 0x73de98350380bd4c40000000000000 :=
  finishCode 95 0x60261a090350d2d4164b2db47a43d0ffe7d3d116155e5b539a4e2b74453dcc26341d11899085b44509c8853de31287e042da8d84a6620fb547a213da2261afa766f6973e9e88d6a6f47e4accfa62b25fb3e9cacda9da22e4b31a9bc4b6cc64dbb255290f4615427b445f065e57cdf8f82683688a6ed34cb336822db27fc4ce88d6a729b273da5cb2f94cb21a0a13da22be6c2a9ef686da9d98d91f4eb539878ad5e5b4bad4d39e9bd4115a2cb3e0da9af2be9c9bab9b492be76a788da4922b6caeb53d119614ffacaf44744640fb2bb47b53ac938885a2b58565e63417c15f37d38c1a0d6a3a2210a84f4df598ce18568ab5eb7052258bc331ad2d7cccc6b31247a984c36d1f444d065bf30dacb52c6d4f445b90492036d325c624740f33162537d1574df5a5c4bc9ff68e1435a3998d52f0f6f27bbe9d322b609d3418aba2664f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part6 : Excludes 0x60022000000000000000000000000 0x695fc83743c0c44440000000000000 :=
  finishCode 21 0xc45e29190a844bcdde65e13e326c88698cbf790ef459b78c48c86213f197b77d7240ddf68b130c38cfa768ba2365b6a6fa34c7b579a1da9d405b6b5334109d17190c50c60676f1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part8 : Excludes 0x40022080000000000000000000000 0x23ced9712780944d41441000000000 :=
  finishCode 45 0x963d2c9885f360fd859bda8e88c6b6fa313f3e9a18cfa358ec4a271506dfb31b416d4d32ecddee464e1a669396f8b3b516d1b4b9059bc4663276a383f686e888c9c4fcd82327543444d2e79b431977c1f901480ed2e01a22c89c0a5987d6a6c2a9635a9d28a18d4a2dbe9ef7c6a36fda6cfa765713f1ad843d65730c44e3a030fa132fcda9d34bd2be9cb6d85ebf36a74d2fa727bcb09adc01a4ed11b5335b5f96f18907446d4f446 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part10 : Excludes 0x40022000000200000000000000000 0x2347493929c0845440022405008004 :=
  finishCode 105 0x2b1245e442d4e5948b24c1856a02ae30f1919adcc8d3234a2a11808f4617fb47cf970ef166b9ad27617e84da38c9b78c59cda318c2996aecb741693db4687796fd0568459d6936526634b7c48f62b9186e377a18d65a9e62a6632863596999caccf07a0b68eda331f2cc9ada799add0c68595da3e17d0c732266681f207c62778ae4acc30e9d765b4cec0edded27537c31cb2cb1b57c59d2cb0c718bc622a065f306ef85bc61e27e6071936dfa1dd09e646cb6a15c41d981c28d83e979307985b2d6079abdbc70be5914b04ea18d9bc40f68eb326b70c613b64793ad1c27583ea1908b39ee5a4f0bcccc64d33e98dc2fd05a1de246d1e5bed150a264027590327833459a7f96bd1fb49d65783eb33167a23368b788c9cc0f9cb2611cd4365a682c2b206dfc1fb4361a6d1f4474161a6c19b29431acb7392c68303e17d0d2de2d4316731f368b6f834d68e6b6bbad26b33459a79e84b49b920168744fe88b03aeed2220863617e0fe88b07f302363dbd1196d89fb478cc707cbdf444ef6d11331a8688c61ee5a6e6a1c2713f6155a34316a18116d26c2978343140f341 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part12 : Excludes 0x40022000000000000800000000000 0x2346483d2585a44540004000001010 :=
  finishCode 115 0x158bc622711898197d42019016f963ad465c5e96cb5bbc64dbbe98d82845ff3969743ba18da3843be9a18d5ca8378a18cd1f156f9601b347e86d96ad5cc8c59cd5f32365a32764c04b2a0c1ec0f0c9d2bd0ef306fa6fa76178c9afcbc9bc9cf970bfd94bd6d98f31910c3e43bd13e13f4c34df4c9652bcfa72df31f0ee6736575a5cb7cc7d2bda8d85f65afa2f831670ef4af4c89fad45e9428e27e86396342990ef85f1adda8be499ce17c3276a2f272c73c9e17c326d27123ad581ca7bd96da38c9d42b94496051a18c0dac2b166fa3004bf81b44beb2bd11964630be23f89f3413fd89160743168303831d65627785e6830c71672c7614b499a0b41c0ce0d2bf3105f98d6d83c5cf4469913fde64e10c6cfe8775f96af877acb696f693079c2fb47a84e2892c35b8986c8f2b5a2cc6e88cc884e97ecb3365768a6b70c765730a9a5830d4af65768a6b716711730ac52d1300e4d11a8572084c3663617da0a18cbbbe0c6b729a11b51da18b03c3be72002e3303d98e82c863306f07452e17e0fcc8843e0fd6972da4c33070ef5092462636b4108db4b9e962ceb417b97839f4e1dd376d1e70d078445d9dd2ef83f662862dcb4b977a58e29405e615959981cd6eb3188b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part14 : Excludes 0x40022000002000000001000000000 0x33565c39e588a54442a04148800442 :=
  finishCode 41 0x33980b2441f8be6c2ba0b07c814e0cbe599c994ca6da0b682d271675060709d846498464ef12af4c1be99a0d84b30778b45434168b37cb1935020ed49f2c7a1368f189c682c6434d265edbe0175a5e829a0d30c34d34da5dbc4f7b4269469a5bc5b053de4c54ff059b08e1a707d374ca62ce3178d0da265b7ccbdbbe2012b1a0c52c55a73ae6d117647d3ad1c27660e1a6a57a8602246a69c2f6934dd19335b98390c6b47 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part16 : Excludes 0x40022000000001000001000000000 0x2346dcb9d18aa44449a0000a8a1042 :=
  finishCode 39 0x6f3b138bc4622ce7adb476070a132f6df6ef6e4c3c30f122da2bd73d2cc6c826148a25a5d29f30f31a1266b7537c6b610729f459a7fcbbc682fc4e431376d463316c1a636d12ef1a08c9be8af9d85ed269ff31a683b0d03c9d166be66b6be74b7d30f205f38d6e192ef3cdda599c80ccf3769603ebe72ef68329a61cd6c64d3fe9714c535b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part17 : Excludes 0x40022000000000000001000000000 0x23464839418aa45440a00008000002 :=
  finishCode 151 0x222196a71082462a80eb30c059270be66674b28abda3c7ae9a647f697682c3ec59cb8d68a47e2aea041dd058f5e93ed145c64d397953fccbdc964a4552566b459654dd7935f3b4588ec1b6d165eb06db4bb4153fe9be2441b6c881f68f3c0923cb2da5d509c4c2309bb1ad8a98b1c3bc1269fe6b6fc2319374984c861deb412611939f2ef9184dda99db7ecc6959b47959852e91386e592a93232ca9533e9c52d95c30f54a6fad061de2cdf931f17896f8aa97fb68d33d31f6833234b2c59c326f97683a0b4ce81a0d31f2b2683130a6e9908aad4de6b768f109c462b82c7d84319bc4cce4dd89198f8cce5180b21f9c99ec2ba0b0c3a67da5d0ee99f6534c68c3c48b60c9ffa0abe7549639bc4ff62961ddb9d09718d6c17e63c61e6c13fda89209c4c2914c8c049bf022403e983341b5169f4ddbe528da0a4736a30ef2af3f2d1e2b63dbb499836d130959da60e2969bdb9188a5b4b8f85bc5b46b2b8985b7e214c0858226ec7e2682b3a2da80b267cb7aced12f68e2db2ced2bd9da6ee72f0fc6d19bc695e98332f1718c848c6319261079171a45f12a6c1994d4c534135b8778918811dcbe7a135309edd37d31375f2e341a6f96f3bd96ad3fe9be997c863b1994817132998390157e6d2d6763414055eb6079e6df4c5c4ce4d05b466ef09382049cb0c3272eed832f9bd28c9b4fd0e281f656fa62db38b2b9e6db45bbecae2fd43179bce521b46b518a55f36f1a564d065de32f241985959 (by decide +kernel)

private theorem part15 : Excludes 0x40022000000000000001000000000 0x23464839418aa44440a00008000002 :=
  splitAt 1 60 0x23464839418aa44440a00008000002 part17 part16 (by decide +kernel)

private theorem part13 : Excludes 0x40022000000000000000000000000 0x234648390180a44440800000000000 :=
  splitAt 3274 73 0x234648394188a44440a00008000002 part15 part14 (by decide +kernel)

private theorem part11 : Excludes 0x40022000000000000000000000000 0x234648390180a44440000000000000 :=
  splitAt 1 47 0x234648390180a44440000000000000 part13 part12 (by decide +kernel)

private theorem part9 : Excludes 0x40022000000000000000000000000 0x234648390180844440000000000000 :=
  splitAt 1 69 0x234648390180844440000000000000 part11 part10 (by decide +kernel)

private theorem part7 : Excludes 0x40022000000000000000000000000 0x234648310180844440000000000000 :=
  splitAt 1 91 0x234648310180844440000000000000 part9 part8 (by decide +kernel)

private theorem part5 : Excludes 0x40022000000000000000000000000 0x214648310180844440000000000000 :=
  splitAt 1 113 0x214648310180844440000000000000 part7 part6 (by decide +kernel)

private theorem part3 : Excludes 0x40022000000000000000000000000 0x214608310180844440000000000000 :=
  splitAt 1 102 0x214608310180844440000000000000 part5 part4 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part20 : Excludes 0x40028002000000000000000000000 0x23d392751098a55104c00500040000 :=
  finishCode 49 0x3014090741846c27a6744934b35bcc199d32a892326667563316ca444060c64e9be0719958a95178a9bb14c603984db56977c1fd115178a992b65df44464ed119a532314cf0f1e88b09c54a67d84ed963bba22c06a17180da229ee9cedb7a235b310dc604417d4876a576eb72614946d35da22daada3688a1a921c42e9d6d96d22db6da251ac06deb688be1946946cd9776231588af8a35b7d846c2799528da65686d8af965517971 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part22 : Excludes 0x40020006000000000000000000000 0x71c31af190b0a4050e8014003c0000 :=
  finishCode 39 0x60289c4d11a044330e4995804829a6013c29c2197707744934b6e1fed2eebb20c6d627e3342c36da5cc7d132db6deb15b358a24c80d2e6db35b77fa1cdbada457a62a66566066271323438bcd930b58d49ec26f36892d77375da6cdb69ba7e6dab2098d97a4c8f09496d1270a63fd4dd86d79ba04acc89332b8473c4a24d0184ec238818af9958c6211266133418fccd0628d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part24 : Excludes 0x40020002002000000000000000000 0x21530e71c490252104a04500840440 :=
  finishCode 95 0x6632180d4543986b6327a23285946c41316995a690296d14db897a69a65669ccde21fc54c02ef47a234af32251b197ef26566d16cfa69a655e0e9914d3791d0d5e5a84e218da31308c1cc8c8280bb71a1930d0bf370c81c86972df2ddcc7e82d26be8d35e0fda22f72cc4ddb44576e3416c1b33979f4350d664631347473171204f732f984e56584e28d4499b84cbca36655b86883995e62f4c89251b4ca80b7cc272df457c207683133441cca946da5c89251b68a836184df112f257997b67a57c22332a7fa087a22f2b84f370cca930af4da5e7179e6cf5e79a3d0adf132a99f688d379fecd8318a0602a1205e5984d3dc5ecd2e696cb2fb444a3584d3de6cb8afd116cbb445795e465e5e6146d1022de9cf683611c41c57a75dd0a04a3009b7687595af2e889a5ca7c51b31f1adce079ea5728d94f6cb9915e58a35e7ed0da533e5d116035e5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part26 : Excludes 0x40020002000001000000000000000 0x21470ef1c09224010c800c020c0040 :=
  finishCode 153 0x399c4a05b330909a4cac4148f479f903e1cc7da2287edcb2d0e88d99c98aa2e6b7a2320d6442da2384687ea2f044e87c652a2f2ef18564a6c51ba22f47d8a851fd84e87ede2c26ddf215d84f31f688a1ff4338dc51735bb444c8663628d95b791b478bc6214d6db3e5e51872d9a61ec6f2d0dc7c3f17d6309bb368bc8a6ecda2327029acccc6da2a24bf0d6e4dd6d128dad1d795125f051b309a8bb6fbdacc2651b4af1add249a0aeda8bb70a6eed0a3635b193a306b74ac845cbcbd1beac8256e97144996fb439ddfa1b45178a3631346119e45f5692634b7917c5a4d846dcb47f31f2df4df29f687da4be18147f4a7d24af2af3e88afac36d68e682f23a22f6b686cd344730a174c79ada24ed1f5663686db4b89998f966743d796caed1f616840f979464e21650b6e54ffa56d37579668d07a52309de8df5512632f9794eb25bb78c23146e88c38d6969d6d8adca51bac7c3d118a350fe99c96e321613b4ba43a3b1ac9c533d34af3c9ee65ebcb146bc8c5fe9d665edcb202cad8c9bc88f2cf0729fa2251a326c074686d2b6dcaf2312f2b7618e86c42c4b651a01200318de3f1f0dc36c6efa650184d39ed1151707bb44539ed115175e950ba90bd33098c9af4d0e310689326fb6fd413832609b599d37c569fec38da6c4b7493197a24994a24cda368cc543010e3370e88b6a9ad8c9be256e5e99956f1987611b479b8491e9858810556df329995a63e16b6d117813310895e75f57644bc66315b2df207e10da4c82d0635b885ad24ca640f995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part28 : Excludes 0x140020002000000000000000200000 0x69ef8b754393a43166800444051000 :=
  finishCode 21 0x9c522a198c4595cfa265ec2630f2db033b57be892abead2da666f6b224cc8d31f099f686b4fbd1b09af3924d68f65b12ae42690c995ad1d0d621d766449193a17d795796341b2b5cb995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part29 : Excludes 0x40020002000000000000000200000 0x31430a714093243124800440041000 :=
  finishCode 163 0x14c9a37138b0de4c2cc7c62595b867d5d0d9e7ca35125126193387625bed90e35a0da3c43e18b08b09d02706b76189a1d348c38bda24d2cb375ea280faad27443ccad37c612f5a3bf083e18e869309adb75e43306b7265cc8b018c9a24d41ed65d94b38af35b6eb76456d84e81e2b268251b3eac683a1b32ac27109c502a148b44bccc230e715e2de2e7b09791638d6ded608be6279d65a10aa2ec274cab7ae22cb4215b3e4db8ab3d3a5e50ae090c5e59ad5f550d4565b7e6f17d5449a64579e94df561915f2f3cbcbdaa8ba15cbccf86892f6bd89795e790ad844ce68af05fa6f7a388502a190c0520d0cc3e449613a1cc9561ce99585cd84f211c887944c8beac2a6a2f2b34acc1074caf12f91575a5be1bea83ad84f12f2b21034a74ac8c9840d4291b0c85a0eb022ec2928d44919384ae25b4cb99525591270866132556cfa21ca3512789b0a834300db6dd73835b25ba5edf2e28d5f5a49929f09deff43665503e5ef01401939bd4d6f41628d19328da91a8ce146cbcb40de42fccabc1d68f852f232f60f75a3e14bc8a7bda0a6832d5cbdad5cd6ba0b32b65bb495ba17ca3542f4169955e5de54281482618d0c60e266c173435176d196ac64e94e3968f682cc8b70da3cf07a0ad9eb57455e82d29da6a8bd032180804429bec2985f25550b323343b452061e449995b414d6c954a3699535bb2fa8ec21620c5ec984d6dbae28d883e265642b517e2370d8529baf6b32a10b5a3ad5da5cb56d9ed264ab32bc4cc641c8dd7a0b224d35bd1bd6946c892d87d59b05ee5f45e8e6eba94e (by decide +kernel)

private theorem part27 : Excludes 0x40020002000000000000000000000 0x21430a714092241104800400040000 :=
  splitAt 3497 116 0x21430a714093243124800440041000 part29 part28 (by decide +kernel)

private theorem part25 : Excludes 0x40020002000000000000000000000 0x21430a714092240104800400040000 :=
  splitAt 1 60 0x21430a714092240104800400040000 part27 part26 (by decide +kernel)

private theorem part23 : Excludes 0x40020002000000000000000000000 0x21430a714090240104800400040000 :=
  splitAt 1 73 0x21430a714090240104800400040000 part25 part24 (by decide +kernel)

private theorem part21 : Excludes 0x40020002000000000000000000000 0x21430a710090240104800400040000 :=
  splitAt 1 86 0x21430a710090240104800400040000 part23 part22 (by decide +kernel)

private theorem part19 : Excludes 0x40020002000000000000000000000 0x214302710090240104800400040000 :=
  splitAt 1 99 0x214302710090240104800400040000 part21 part20 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part32 : Excludes 0x140020000400000000000000000000 0x69ee0f19e2a20480058a0010000200 :=
  finishCode 47 0x151e1b0b53487128164995be2dfd15a153a222f2bcf524d65b312c07105eba2b48c6a6b8715c1a86888b6c4c22f353218dcb4787e6d4657d79cd04c26d3661398b341897b37913db057ae44f8976d16c1a65619a234c6138d04556a617b1a2adb065ded150d046298153360a279a0afbb02df17ae6ef5e90a96e196259d10ebd2f72d274cadf180eb497d10a9a5385b6656d057d12490a9883a21d79e2a45b42ada8679f98d6f15dd5eb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part34 : Excludes 0xc0020000400000000000000000000 0x737e465ba18a048006860010000200 :=
  finishCode 35 0x1147463265671106e18216d4e2ae26778dc96f82ae1c5b842ae8716ef7afad14ca68950b53b0c698cc64cc4d6db1692e95f0abb533199b042aecdda92b74c6bd2be9b09d50c84d1e18c96f9bae21e2a42aed4c29e6d56135e982acffe95f95b0abb2d5e9ad4c5b6b2da864029eb536d535ba6d82a6d4f416c217d30abb53b2d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part35 : Excludes 0x40020000400000000000000000000 0x396206192082048004820010000200 :=
  finishCode 181 0xd0672b140e2296a9ce422164d05b0842ad13ed4dbade7e96f9816d4db466542a696f605b53b53a19c4521c83c3516a782f36de88d2b946af5c402aed11a6f897a6b6f5a6b82ade2f447794df177aedb77c4be8892dc51adaa493688b09af5da9d35d853a236a61524b78cb448121d87957b9605ad4d84f0c64056e57b1883e5bc6c7fa81f31ef624c3612946c63b1781119ec7446cfe25ed4dabdbbed4e613c31b42568ed4c2adec4c5697317979bb5382441b56d46b2fb4d7b100dad34a36cde0076cb7b128de236ad84b2c32ef84251add78434b0bd219d8515d6462982d3146e88b09afbe6004e887d115e999528d9e4e20df4e80ee34ac9feccabe0bc5d15b8422ea51af97613d25e88ae7b6ad022a6a63d1199596451e2ec215a31691796eb9dfd68f435ee57af44568ea07130963bb69335bd11a63995c219e9744511513f19c4882c168ec210fd3c58abd116dbc259017445b5604b28d605d11603b09c5e5ee7096e2688c42c9ac6dbec501b14a3621eb478abb0a57ddee65eb33944f5e99b1507604f9ee57acce57dd11498644f9a27161a8985a03b2a0f86db75a98b4cca91bb09d31d90959ae531d6a732b1534c74cae82c15369ab822d34ac840be1bdfc88b7c9591799115f56080eb5a98b6984c29f6a758d4501e088be5a9ccac88af6afaa6b703ecca8a98b4cf8732b32b3e198ac0eef87507d19815b94d6c8ee6b582455cca8b4cdcb863529e88d4301305c1b44657ecddb96d34d6d3ced052ef98bb5379189986f0aba03126570a644fb53a3da63791ad4ecded1513f0c4526b378996e5c29a8f698ed4d13f31407437265619687a222cc7d2be0eb2e7041cc5da9cd292615d07bad4da162874455abad4e565f2e25c2a5116d16a72278bcc9bb68ed0a50f6a78cb4362b8f736a6f96ddf4ace14930c56d85250f2b38060130d26d6a786312f6a7688d9fb7ae14d6a62f2c46dbad4ca1db55b6e6e1a499bc5b14a1ca1e (by decide +kernel)

private theorem part33 : Excludes 0x40020000400000000000000000000 0x316206192082048004820010000200 :=
  splitAt 1 115 0x316206192082048004820010000200 part35 part34 (by decide +kernel)

private theorem part31 : Excludes 0x40020000400000000000000000000 0x216206192082048004820010000200 :=
  splitAt 1 116 0x216206192082048004820010000200 part33 part32 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part38 : Excludes 0xc0030000000000000000000000000 0x73fe4a79e5e0078000000000000000 :=
  finishCode 43 0xbc8a2430132b50b2130cc0f6a615318b2bb445b86cae4cb963d116d16d1a62d8557a66e1c0671b466e1615a24a6c2c24c32b30528418b6cdc37c8e371b466f16158295a4ea3d9591636cfb5340fa57ed1d85699649604f8bcd65b2e612b1c5c1a63d7e6d16964626245de5f768f6f1331a57663e5beb495dbbe3e307eb316cfb41acae7c95cf615 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part39 : Excludes 0xc0020000000000000000000000000 0x735e1251a580040000000000000000 :=
  finishCode 177 0x301a0a84c2418835ba20c9c60d2f446d1e7c189b8a99959ebecae89b7c1d118295bd4d2f1158b463064e4815681f36de88d95c4cda9d28da22be69eef3ad97688853c9220f08c37acb0c4c732b262cc6d36a66d8322f24c72c3131ce25918607de4b9d8632bede34d34aead8a7bcba886d83e98abbb68f378aeeaf9d85f2bb8532bf245ddd1169193dd375b553764df03b7798736916d582974453de65498dbd6b198b45a5d0db12b32a14a32690b631265620f4920b0cde34c74dad8b83f26d836e88a6dd85fa22663688ce23165f300b67caeda2331e6629bb2bb198e88e88cec4dd92198ca6c9b6bb6d8a283039caee21bc6576599c316c5b4460a5cc688da2656d26a3b5f9b3189b923bbc01eb83a1ed2765783ed8b83f443d13385f15310b23d248be6c034c215acb6d1e57e98c5e698eb2dd0d9a4c2ae393080281857436263b2d4f7d0d82ac98ed0ec2f8af1792638a9b0665342ad8545e6d4e995b47ac4a1a16a72d5c43cbacc4c71bc695f25733195fad1e39a1b131990b68b67da0b6520d732b68ebc331207b4461b5036656caed05b4bb47d0d8c402b04ae6534cabbcb6787ed6762031532ff84eef32f3595bdb855931ba140bc779b2ba656396774acd95be9d95d2c72d5be9ccacbad6963de65215768b6632881573868130cbad10f3131c98fad45bc4cc6d2e95f95db0c688789595d9894f799595da17c5ecffc29f18c1f36dbe9c55c4cb0a9308bfc9eed976cce4cac31b869a65999634f76c1263a69966658d3ddb06d4c5e624b6bb98562662adbd61930b4131d32a1a016fa20e5bd84584d3de16f09b744cac9ef2b2fa648f438cacda3b67c4dd152bd22df68310726ecc7e61f0b88e367afbd32a136de2143438afbccacc7cde2136bcb47a656cc5b86206d1e09b4cdad2e26e204285214c995b462026c5e68836137d1a1cdb5620e6f5777963b51b415b7e1cde6db6ed061ce79b6dbb41095 (by decide +kernel)

private theorem part37 : Excludes 0xc0020000000000000000000000000 0x735e0251a580040000000000000000 :=
  splitAt 1 100 0x735e0251a580040000000000000000 part39 part38 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part41 : Excludes 0x40060000000000000000000000000 0x6bd2923526803c0000000000000000 :=
  finishCode 153 0x3a1a8bc4c369a0281a83c0d6da164a51b445806266d4dbadb2e316a7688919a7bd98d2472462d4e5f386db2d8a9b53a9b696140f50bb4441b5f274467a4617cda04675a5be3cb1d2f34db4cf697697688d64943e0be9b07c10f133372d98c10f6cc454269180ab895cd2d84584eb89bb4c2cc8da59a084e855b75cc02db7053c72b931f617af3da3a138559a0d90be65e76b5d11b495f3983615427939ed0f79db2d5f3909c95dbd63100a67b0bc586d2d7cd3dcd2e5912b001da9b6da13e88af98b9d68eb96f3afa75a8e88cc1da39a5af9e88c503b4a03214bec8a16d2330ac4cbead657a1f6a2bbb1336889ade0148658d8702f9d9dcb922760dad232fab65904ae4cc5bcfcb9cd22c2a4131eae0cc559a0d13315764a8501b2dbad72642709d98397cf00be7300a6ecf8f541e1046e375b7ac8180e5e6b3b34b35b7c1859503e34ba05624012f3d7e8884f9ad84bcf5fa2213ef5f688cbcca2adb62eac076cc2fa53c27584584c2af4445e5ebe17b35bd117a5b21c697b8ad1797d3d115219c043d157a23133a1f2ddd1ebe9d31e84cd6b6a62f2a5ba2378924c3184df646c4e17cc5ee8add11ad4d83eb53d11782ecc666bbb6a6bbb688849cc68b2cf8fa226676ca830029620eb45957a3b40fc19a2657e74465f3d11aa17cb6301c14f308c688d68f15b8622f7103a129ef648998105a4e60f09c25d49a1b2ccc36bcfaccd0db4a7a1ba23a23688cc2b156beba2330ac725884f0bc9a0af9b07ce22b609db2bb446cdd80e333d11 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part43 : Excludes 0x40820000000000000000000000000 0x3b43569934c1040000000000000000 :=
  finishCode 69 0xda6a339d8a0140cc265653935b92190d32abd2a2ba22a735896297da5c4c3116bd3688cc1c1e2d26d4365683ba2324983125c6c2798d5215f96c56e5884adc4c30fac2adeba23350c52b03b1268d8b1574c8e17a90af4c4cd0dea43a0b459a90bcfd166bf340ac1adda8c83b116326a5ea5b74d1160fa2cdee583e88b891643d17e6cfe60f5156f5a2ce2ce5156076d5ac5a25c64eb98d6111877a3eac1266b731f0fb191e0ca758bce88bd89ad846d2b7166c2732a6b76835bae561f014f4d7438983bcad24c59b01da5da23132f2a4c2d97535b50b02e88b6dd2af459a7eb72e03518c19372130b62cc1e13ac0e13b3ead167167301930853cc05e609d603611a259260e7c7b315cf17909db31a246b515f740fa6f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part46 : Excludes 0x40030000001000000000000000000 0x696bca3966a0078000182840200180 :=
  finishCode 65 0x248bcc4433a167f309a90da9a96d72c91c0a9960bccc0f6a7688da3e88d6a7185db9e8ed4dbc6576989981ed4d4e6b537c79b053f662c5e581ed4fa0f4c44b0ca42a733864052cd5fa23666f86bf214b4aeb03b103fe95fd1117995d4fd7c7a574295ec69896076055398c621f0bb73832fa625abd816d11989d11a6265d62457a3d117c79759367446577a11066297d330a618c271a0b02c1534af434833da5e889a0cb76de2f170d34dec2a153bcbe5e1b1686ef7a39b870a6d058170a6869b4b9bc42a700bb74aee88aedc7c717081fc38e88da3be984ee14854d852c0f647b1b445bc58542a65766f1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part48 : Excludes 0x40030008000000000000000000000 0x6b7a4b5964e707901c006001000000 :=
  finishCode 37 0xce623a10cd06a14854e65d6615b535f9d11a9be212bb03ccb9b0a840be2296d0f60788ba69847707f43d81e62e2966af0018635f9b31b53c1f5397c4b150dc989980458e62e27e2ce62688b97508fb43e295856d0bd34cae88997e88cbbabf359fc627a2330a9fb2babf33086500205ec67d5177b539956139ec7445f55ed6163b537a682d4e5f77d5899a62c1e62165f795d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part50 : Excludes 0x40030000000080000000000000000 0x696b4a99f4b1078400000740100800 :=
  finishCode 65 0x2812c7c341514488b89f52f9efc5ac26d856c23167975945a23014b377c528b584ed2b6a72f47452b0384a8bccda214388b45d180e0a99959a4e2454e5817a07c7378cc7923cb18bccd8332ac0f4774c7da9e88b03852ce299649959b4425426c8c65c177194d79f98909387dc0303ca733129bb5a5d32e92bf4c4cca8bce2265669595f6136c1a57ecfe626e24523132b1052f9f56701374bcafcef263e315b31d118637a35db7a3960bf2a73a2334981ed31e88cd2662b640a997e5776d11a6379f7b116bb08c26ef1802078296d4c2a631683309da5d2cc1fc291f79f4622e62ed36 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part51 : Excludes 0x40030000000000000000000000000 0x696a4a19e4a10f8000000000000000 :=
  finishCode 119 0x3e338857d0d0492712eb6a6a42a5ac2b594c59d28a05314be58e95f89198f09ba6182a618da7ef92cde378d2e74af14b8531166831233c5c45e14c15240b173d2be14cc1b96573b8b68af3d43436c231e12057b90a96053419e2d8566d188bb25d22469798ab6151798a50a9681a0d2b33122d31162d34afd98be9cacc59c683197e18afbc45854ce2c9508ad8cbc2a656653426dd115b041b478b6cca8bcd2b365711648f1674c2d94922ca6e12d29b0ef2be15332b14b2492992c940b48b6cbad67e12b3176a762281685f7a65427c26f38f475a9ae7a96da9cf4315984ed4d487446613b535aba8ee8f57e7446d4fa1885e9a1c7446d4e6254854e5e7eb539897c7693b4469aecae6257e680e89c4cadd1c8c0b444bd29ae7c13f0fb2d5c38cb7cb7d8530e2bf29ba13b68f3dcda084fbd8d65315aa5ebb6136b57686cb1e14adfa97e88cb29ae4dd7b9b2bb79749c4b30a65cf979c277d587d2617b9c0614afcc152bd35a5bb8c5c3a2385215338b4ba1c5dc65362ad73e93e98b5f797995f82a65928d8118d0fb696683312a7343e844a96d0fabb74cad95c9311d09899816d4d4854b659a0b04ab03854cbf34cb535f9b444d05a4ed11973b47b24b2caec2998b3e387d61552fa1bde2c2a57e5b465dbd11b2b87d (by decide +kernel)

private theorem part49 : Excludes 0x40030000000000000000000000000 0x696a4a19e4a1078000000000000000 :=
  splitAt 1 67 0x696a4a19e4a1078000000000000000 part51 part50 (by decide +kernel)

private theorem part47 : Excludes 0x40030000000000000000000000000 0x696a4a1964a1078000000000000000 :=
  splitAt 1 87 0x696a4a1964a1078000000000000000 part49 part48 (by decide +kernel)

private theorem part45 : Excludes 0x40030000000000000000000000000 0x696a4a1964a0078000000000000000 :=
  splitAt 1 72 0x696a4a1964a0078000000000000000 part47 part46 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part53 : Excludes 0x40020800000000000000000000000 0x296b561364900c1041000000000000 :=
  finishCode 77 0xe8672d924ec290a96f1350deb303da9946c81bae60e4cb6d5ad4d0d6a6bb534cb9bac9a751d8a013ac814bcd6e43509da62707f07ea6fb07d4bd0d464e816852f35b8afa57460c256995991d11957d11a63d0d707f89b0a8481b2ed46795193a6b35b925a9c326deb4daf6f614e88bd05961eb78bc2f5d7a63601983b445f064721ae88d36be4a85ce2592db0c1b07d9bc3076a7595e88d9be0cc56c64630f34a821ae02813835bb478f9e5b460f0660f1c3132309fb53a2526d833306deb31f3bbe14da9e0ccbdda1bd609fb5396d613983ad4e97bc05417d6d054cb19335b684c5d68f0bfa0b6a69ef3235a9c4bd83e63f15b78ce0c9af9c4de5af2eccc8a1ada9be25886ba234c1c4baf9973d32b68b2cc2facde1b655ed4d81c98625e8afb47 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part55 : Excludes 0x40020008000000000000000000000 0x295a53d124c2041018004001000000 :=
  finishCode 103 0x5a25940d4222e22a1b4193e2307c6b7a2251a68745693ae88cabcc1ef27b4b6307c51a4df2db3cfc38b0ac34d96acecc8e88e88d306c03d0d11983db6dbd4d6f184dfa23307e88c667507a5900c1cfa667714a6b78534cabcde888c1cc8dc4e844319a8ec67344628760f6157454261444f78abb4466470be9a5b6dbd52d61fdc2f86f87dc1796fd0614cbefa2232715727bd4d314b3233074bcd1676a6326dd6c2b507436db75c618863f133455b57d6636a716bc4ca90e0cad5d4c369710b323a07a672d2ec29233983991d11515991b0be8858995e7d11885a2af44629751a2335d943b5dca2add704287c319ee61f65be2cc64db16d2e4cb19360760fa60d81ed4c64f515826fa6fa2cf0a7446d4c64c95e869957315d11c2931f8f8f446d4e26625d4575158880c9b57d6a6006f62bf24d2db6deba235a9931946db3447396428d96d9f06d1e65660d7deb4198393decc635bb474f7a036dda9d3074c7a226867c7688a90f42c910b6362b6dcb2d6a72c6c2aa5ba235a9cc0ed8ba23306a432c650e0df2eda7b943cc2304dfa2330aa7be88cc2b2c98ba27d81ed16957 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part57 : Excludes 0x40020040000000000000000000000 0x2b6a5a91a680040280100200000000 :=
  finishCode 141 0x9a483a087f78a61635129b2c66b727b946bd2d166976dcbb0b2681906b6d0b3fd43658bcd0faf62dcb434c52accd12ebf2dbfa2331ef096535b65b7a9f1da22c2b0fb66f688946e17c55cdcba230fba8b659fda234d69bb32a50f0e34c7c55c3ed49adc2d62dcba2326ecc79189adcb2513898fb0661f423744424df12ef4ca87ae18e88a85cc7c4fd9bda222f29bb43ecca98dd833a23a8d8143b00d14ac1fa22d9766f688c4fc52cc4d0fadab13f404dda654d6d89106d5d4365cc2af8efaa5bb455cc5cbb710c2f98574461f707dec6d46b53c1f87d6078a58e492584dfa233cfc48da9c4fb0ab6fcde34d29ee2c74cae88b6fb78c4cc2c6bb6d9e4dfa23d8d45e2d92428d7c7a575b074449be30dc34a7b78d94cda30d31c9c4b25b6b53d1160f615805617e62b6d11c317c7a69ad1f0be98e7c7c2fb537a4917ce18deb688bbb8b2d36d0d2deb3134afe14b65da23a234414e67d56c579f96262d2babb7562d9405dba575b854bd4e6f18332edcafb709a0d69ad435a9e88b50cd6ba22c4179973df0e9b5b953f45e6269c2f961515c06a239d89c5e17e5856d46b536f126f3339bd76178922f09bf446b5379193ddb9657db0695f287e8459d316dea667459bd2c6476a7a224dedb7688934afcb0adb3b178b4792dd80662c9bca1ccceb51d1152f52f942e35bd11d854240dcad9743ecbac59cbad2eb459e88d6a2a5f78539a6549a4a1f0a612d52f6c5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part58 : Excludes 0x40020000000000000000000000000 0x294a5295a480040000000000000000 :=
  finishCode 67 0x180453459a85e2e98c0a5904b34466c17bf1932617b91e5a9ac64de5750deb2d5e88b60afc8c99e7d0d3316d97a23317673b1d0b64c5cda24de32650f38c65a9cb57a22326c1fa23365b60c3272eb30a8c9b0ac7c63272eb0c9f13192096373511672cb682da9b0a930c996c2b621aedbaf0a68adc29a18ed4cd065abc2998b6eb98ba2ce22e2614cb98bbc6702af0a695f60fc2fb53341c19985687d341ec672f0dc275287039a99e946cbdb4485e521c64316ae9918998ab521899a2ae2ce067c2905dc4301b96b378ab8ad98393de2641ce82311bae78b6e56ebb07d484f649a4f66269 (by decide +kernel)

private theorem part56 : Excludes 0x40020000000000000000000000000 0x294a5291a480040000000000000000 :=
  splitAt 1 90 0x294a5291a480040000000000000000 part58 part57 (by decide +kernel)

private theorem part54 : Excludes 0x40020000000000000000000000000 0x294a52912480040000000000000000 :=
  splitAt 1 87 0x294a52912480040000000000000000 part56 part55 (by decide +kernel)

private theorem part52 : Excludes 0x40020000000000000000000000000 0x294a52112480040000000000000000 :=
  splitAt 1 95 0x294a52112480040000000000000000 part54 part53 (by decide +kernel)

private theorem part44 : Excludes 0x40020000000000000000000000000 0x294a42112480040000000000000000 :=
  splitAt 1 100 0x294a42112480040000000000000000 part52 part45 (by decide +kernel)

private theorem part42 : Excludes 0x40020000000000000000000000000 0x294242112480040000000000000000 :=
  splitAt 1 107 0x294242112480040000000000000000 part44 part43 (by decide +kernel)

private theorem part40 : Excludes 0x40020000000000000000000000000 0x294202112480040000000000000000 :=
  splitAt 1 102 0x294202112480040000000000000000 part42 part41 (by decide +kernel)

private theorem part36 : Excludes 0x40020000000000000000000000000 0x214202112480040000000000000000 :=
  splitAt 1 115 0x214202112480040000000000000000 part40 part37 (by decide +kernel)

private theorem part30 : Excludes 0x40020000000000000000000000000 0x214202112080040000000000000000 :=
  splitAt 1 82 0x214202112080040000000000000000 part36 part31 (by decide +kernel)

private theorem part18 : Excludes 0x40020000000000000000000000000 0x214202110080040000000000000000 :=
  splitAt 1 85 0x214202110080040000000000000000 part30 part19 (by decide +kernel)

private theorem part2 : Excludes 0x40020000000000000000000000000 0x214200110080040000000000000000 :=
  splitAt 1 97 0x214200110080040000000000000000 part18 part3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part62 : Excludes 0xc0003000000000000000000000000 0x72ffa48781e1e00078000000000000 :=
  finishCode 31 0x562e14ce0138d213e609b529b4985a45c45967d10976df0a1cc271b85bc4315f460f1d07c29b43b4bb47871b47a25df46f1903a28da713763fd88523dacad73ed06d060877b7b4585bc55573e216770b58a2c55cc6d6576a61331fec38cc7b6fb77862f02f14851b83154d70a62f5a5d04f69d9950c5505a5dda7665422e995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part64 : Excludes 0x41003000000000000000000000000 0x6ac66ca1d158a28078000000000000 :=
  finishCode 41 0x339189e5e1b8ddf486e1a24a025f436b494ddc2916fb47b41ca561f74356665cf16f3f141343117190c4d07808635a994a9a0a93da3c4ef2da6834c864d2654d042261717bd81eed4e7bd0939954ddad4d7365c6d1e636656d9d09959420ec65e9ffc06bf9e9661e6bf6bf933c9965c5afe7c9d6433a0682143368cb693b93eda2da1a2e32ee4cb4c693ecb1cf9eda32ef31b18535171a65458c5c6995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part65 : Excludes 0x40003000000000000000000000000 0x68d624818140a00078000000000000 :=
  finishCode 165 0xbc49388c3398b63a38132bacd0741afeb312892958c64143e4310c53419bc5734316093977b25326910b51fb4dae7da8a8ea9af41bc68977c97d3527a1de27e96e98d7d34f79ea6b13ca73973ed05bbe90dc5bf0a1b4bb3ba2966365cf9a6d3fd6fe3d396545a5bbc286313ce036fb77d37c10f10b47f6a72f7442eb20818ab7f0a6bc9a8ea18850d6a2f26b9e9ff2e7d51dc60935cf6d1a61d3ff81a00c5a944a5631646df2cdad4c4169a5e4dafdeddafeb4b844e2cf416d4de4e2aea516dfe0681736971b31a69065341295a64f29a6b5389740f341b22e7cf6f697207ae7a87cb9f4a31a0bf318dc2de2c0783b31a20d73608990c620eb53087431ce71321c0985326918535cc287bf1afecc66e1979831661509ea57b4b7a796acd0573ca570a6b452097af29550fb31b426215eddafd43ca5730bcd0370d34c7bfa1adbf29e18a4fa143218c59e10d98c4fb68252a52b4f331187c050c4ef10adbeddf64b85d09df09e97b5cf0a14c7a93c13e9578715e4c7d32a2df83fa1adc22df686cd1384eeeef52bae7cc2da5c413524be8b68d37e829a0ae7e13cd372f6b9e68315710a4ef4d34bda7fae793bb5fd33304ef18795a616d2db85afe6565cfb45a57ad2d3fd73ed065cfb836fb77bd2d14a9cf0c74933d2c42a94c4fbc4cc3a29932bc0e86b2976265505431295a46d1b82d7459da9849bddbe7cd25de09598da53e22e2ae2b69868b332109341da2b43169a1a0c905a640f093599b07c8dc9dc8de7d10c58a57804cb282a18862cf1eec9decc6b2ba61c2920d847d73f8084f28294a84ed15a4ef346a190c61a5e66295eec97e2967cf5ab883b45431 (by decide +kernel)

private theorem part63 : Excludes 0x40003000000000000000000000000 0x68c624818140a00078000000000000 :=
  splitAt 1 108 0x68c624818140a00078000000000000 part65 part64 (by decide +kernel)

private theorem part61 : Excludes 0x40003000000000000000000000000 0x60c624818140a00078000000000000 :=
  splitAt 1 115 0x60c624818140a00078000000000000 part63 part62 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part67 : Excludes 0x140002000000000000000000000000 0x69ee61110142800040000000000000 :=
  finishCode 129 0x36178ae5f1867898cc86822018aa6b2f2b07b03ca2329f2da682a6b6430d94757ad83e30f532eecbbb5fbddcbbb54b2520d0660f5ebad266d198d6f12659b46d4d734d05bbeb114b537932b778c9c1265659d5c9535977a6993dd46f2150a43f028c64ed4e6bf6e1b539f3e9a678bc82370d35d6a6b3365e667597c682dbada6da7218b66c11b85b7e41db53b2f00b8d066d37a76e16f188062e11cf07666f9f322bcac1f69b3d4b03d62d150c42f064d21649956d380bd7e6d353e499423e89fa6f5dd6af8b381957945ded4e3108882fc9978efd68b67f12eb9b688b69cdbab9b0089f981db0dbcc5766dd5e64181ed4ccce535a67817d68c0ed9b4b2e88d6a7382d4dabe5f950f9956f36d308fad1e93d3e5bb6c9046cda22e5ed0c54a43169956d397b535820aecde6f9ba232e6bd4f1253e6dd97b6070c5be4d2e8e06d390c5b8ed4e08f34125f431a984d0497def6b534312619bb5b8ec978a652230a6b5052787dacdc61ed1e6f160f5e5983f40a3b68f686b59932a5fd84e2e34b6bd748c4682d6a6d8332adde30f54c2fa2cd79651baa4b0cde731ad9b4b7359ccacd299106e3a60e2cd4149950c699534150570521b8e6366dd94f965987a9bdb76d4e5eb995c199b0d0c6d4e645afe (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part69 : Excludes 0x48002000000000000000000000000 0x315769010d00900040000000000000 :=
  finishCode 131 0x190e26d2e130ec1b1df2c934e629ac34d12252a113612b71938b6ec34cc32a4f832513187cd8a5543dbb6b4bc19b2551b0e6f35f36159444bcbcaf52f7af2f0acd2dd99891cf53649c135d0d3166c1ec2af48b39bcd7cdb76cce8776e34318c4921011330cccad8528630ef43ea7fcd9b6978339cb24b1316d05107271c2f8771716f35f360fd65e09c70beb536f36cd619b479b75ead36e253193e65e0a5507619361970361cf32d9b68af9af775958c9cf52de734824514a66566f38a59b76619271979193b0bf9978b230cdf2e8862baea6a59b68687be82b59e17b79d1fd1073d7a81d37d6a769785e862a07145e4826545b60896f35d7ad34f05b345b42264316dd6f396025c09e472862b33165903881da9b69e17a07dd2006132ebc4cb6eccab79de258e529995535d05820c0162b5b762665d7535ac54028e60f1736191939a7314a70be50f61943132fa655776d1e9a661943127dc19b31977543d83ef170b457064e08c335425fa1f50c6d2e25fa5193fd0c64ffb53ae4c1866296a694ff7997c179996b6d4e343aa30cd28cb5b6a6f82862653528da9dc2f96432190745c426c97d316c25a6f41d7998a59007bd49223b6565bf84a0fa2d6dc6686e04ff88ede667149361284ee12c2d35a982582789f91ca18dc2f92c26b0a3ad4d86583c5ceb535f9619619ad4e655b8d7e503e7af7c15d7b53619 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part71 : Excludes 0x40002080000000000000000000000 0x30ceb1412500900841041000000000 :=
  finishCode 135 0x6c3995c9271186781a0b85422466f35e552960f2953630c5b11677218d28862c129aec2f691b4d5296c3975f19708c2eeb07d34c2278336a767684f98b31acef0a6d4e08d9e9f064f4dbbd0c67a62183ecce0979578858ad5e534cb9329edc27fb529cc8d61854bc696509718f413a5dee104c4218843d15a0164bf0fa326bc4c99b8e9a4b3e6f187d6e39036fcdc74a30c9bd7c12e863c4e0682e1502958d8db0e615d110c56e1a9a540c31719646b1975d49d85631a1b3d3e82bbce88a87d27a18aeeb5fb68d6623f7853a22bba863592e0bf313bb0aa65d15a7fa2cf35fe88dc1ddeb2d6f1a69d116c3193be4e1e4ea3b8ad6bf9639e07445f4d0c5f0632fd11ec68389c0511b444a554d6b0bc5f9277b4d9abe5ee9a5abeb3fd11d11a2b693d83d856d1663369cbda7fe88a188c9bd7c4bf15b12ea53307a13c6c6c2b98b870063e60a6b68899dbe89b1aeec18b4cb85f44bd28c56e88aeef01bbe7932610c5b20a8d2b212eddf10b15b4cf181d32da8be88f3d4cb12fa22be66c77ca6401e0a4ed7f5a8d2794aa18cd0a574466ed1138f2db0d78a6b4cf360da993ecf4ad7f16736694aa87c01d1205037c98c8e9cd855bb5f26a5d9a452d1e161d116bd6edb80c3d65abbb2af34fdc2cae4ffb3fae0f85e6217ced1e7c9d11ad4db36d114ff7af983ed36caecfe00594fd119916dd5d77af (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part74 : Excludes 0x40042004000000000000000000000 0x72de31fd0328e10c62082100200000 :=
  finishCode 25 0x38164a441146f0be6cdd11427529e6087da22d3b29e52ac3329b42208c3202728ee88c7bf0e32f5e82a15c3633419775864d2eb47b445e5ed2d70668d7a9427ae551865a465f3a4d6075e5a946934ff608b3e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part76 : Excludes 0x40002004000200000000000000000 0x33d6f18909688014520a0105208010 :=
  finishCode 43 0x1acec592f14861994a54d799549835208fa6bd752d9a5d22a18a8ebd7c18b31e6c7218b0cbe0e88ca3ac3218b1b1e88cd6331ef82fa66c718c6218af17ae5ded05d11787331c1f5053318d8cfff4163ff6a13633639e6583f4018b1b194ac6143ea4f5dd431842eeda3d14a682f370d3a2240743ebd3e0cc11726431619a6124363a430cae4cc2a83b2f5e86cc6d2dd39bcdcc2b4841d9eee2cd076c1d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part77 : Excludes 0x40002004000000000000000000000 0x32d671890128a00442080100200000 :=
  finishCode 167 0x2f39932b5cbc42340c33b4905d098641d4316ed6f3b843ed2f26c731f4ac9fec6c6d9a18b646078d05854bded09b2b3415cdb317cb4317cb9e2575d8550750c781a0a8520d8e48a6b0c98d4eba1c56ac5c4c452f6a436cda43a1c4fcd75e1c63df5f38465dccb365ec31758baf2f9a18c330beb4b5c9b4d1693118ad96fe20a05d7979608be7683358cbbb58da0ab5770369706a390d8db361f65052dd5eb237169acecd8e2954dd90765dc315b3655e86934160f431ba422184c2c1f60fa099a0a09d83f853350cc0e826c1f9ca468369888814a831c2bb4d330a81ef52c1f04c1f9eae61504ec8033438801846d269fee12cbdda5c5ee0beb572f7209cc1ef37534844a18b07a18c52ba09799bcd0c6aa632a1b4e04c1b743166f336398fa936c9107cb975d7ce11007cb3ffa1c48fe1c6b479853ff5ab9f2e5d7983c545f4df2d3b698fb476dd0f58d2cf6c90d4d4d8e106c6f573c493082ed0e374da68201306e36f350f8d8de1045ab3ff90c6536d1196908a85705c6c2f3637ad7cb0c5261991a9ac0f744658c314d8de92c743bb0c862b6ef320968f459cc8cc32a6b4a68b8e88a9ad8331226c618a6c7062d724964619d6523b113f28db07e17a9ad9dcd1a2e2c1e0273cea18be9af5cb46b7e8633c1b46bd4ce2c89bb598b0ad42304c2d1b2dfd98d12300fd98d99c606d1ba1b6a2862a1f48431a6b8f042257774454d663e5c1a23c2b918261b8218a94da227febbb68ea5326eda3d30764a45a3da22f97322c2a6972f5bdcbe8cb67a236628624c3688de258ea437d340f9a0e646ceeb415abd0d7d35eb3635bf (by decide +kernel)

private theorem part75 : Excludes 0x40002004000000000000000000000 0x32d671890128800442080100200000 :=
  splitAt 1 69 0x32d671890128800442080100200000 part77 part76 (by decide +kernel)

private theorem part73 : Excludes 0x40002004000000000000000000000 0x32d631890128800442080100200000 :=
  splitAt 1 102 0x32d631890128800442080100200000 part75 part74 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part79 : Excludes 0x40002000200200000000000000000 0x33c6612f494982124102c005408040 :=
  finishCode 47 0x632a900645c339cc5eb607d6686cd5f6a6f9251e86283b077d65b4b6fa6d5f6a734d06c2a0a3b1b1a18da0ac33323369a9a8c39fad83330ab832b26c730ce4263e5d7b510c5991431b538f5dbc66157366d33414f943160701b968e585e4dbc50c49aed4fb1acb83b3216a69f34e74c8bdea79da0b69ad66a6b138da9a9ad6a618ad1ed67347862d2b230f70d064261783636f1932ccbd075abd36e3ff41d28990c49c628f405a22d0c5abe431 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part81 : Excludes 0x40002000200000400000000000000 0x32cf690f4101aa004300c800488044 :=
  finishCode 49 0x381b4c87636188be0628c9d6a26c6c32a3aba7359cc8da99b1d52e86834c8b0ab0cb61b71b70c862bf2f9f30cda9a9ae22f87fb5a9b60b59a93a18944af0ff66ed6f3b53d0d9b0dbced4e5356e387da647415864d8c316e1ccaa147afccde65e32f2da9b68cbd70e2f6e4e36a72ebb58cb1b78d32f0de34c7ae6da9a8ea94dc0906b2db530832710838f6eb476075ebb862320f7b4bbe8693be829a08c38c7ca30be271277983d7e69a2f2564ff66df5d73fdb4366193fd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part83 : Excludes 0x40002000200000000800000000000 0x3ac6610f6101a3054100c000402050 :=
  finishCode 79 0x6d38174d06c1b0db8f10c3252b1b1a18862dc0d8e61594f949df26b51431c84608fed077af61561951b431ce5212a6d0769bc2fb518b361988b6155eb9865ebd4765665c1a44e01d64cb61988b615619a22df26bc64341706a3ad457ad86464ca24d8f58863062a09c9972b2b9ad7ed4659f598a8da18be9c28651251f5c259b0615844a1866d0694d31b18f24d959863de2663f2130c44a0c6c63d04e69b341599b515998b75a6f43630636f9b2cca09e0cc5c72099a08c79a0c483287c5313fcc8e98f241c2f92bcc8f41eb3b3233fdb4d8864d04c4cc8e4ff5f9941a0d2b27d27fb08987b0bd8656666441ce566f8607172a63acccc89a0e86d78ae6c1a0eb4188b61518f619a45c218e51b5f91876156dfa64663dbc549c9f67a5b2da646cc44ed8549dd856431 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part84 : Excludes 0x40002000200000000000000000000 0x32c6610f4101a2044180c000400040 :=
  finishCode 111 0x6726571948883d2e1285e55f3883ad37434ff58653fc9ad7364f98adb530c5425e175f612b36a34b1862a94b0cda8d3061072c7b48adad45bb5bcd0c6a61844a1f0f0646828b3c41d6978532b260e2af456a76b6fde1907e730c9febc4987cac9f9c642f12ddb062de34368ad60b9596eda20e503527619a6994d5b86d2e20e7188bc76369b028f85dd85463e20f802ef1478bbc3275a9997b0ad99c65ec2a30f1075a9b0ada6ca6ad669d6f9ec2b90e66b3b1c06e394a5a8ca5710dc18f119b415b04466d05223b0770bde65b069be98d61926b36305993fe534ff49ae36318f4ff8a3fb17cae732997052987d861c64cc866a36b194d6d13f38b38fcdb44a55b76a731935296edad06d4ca554a76170b538d8e9cec2501b6f34eb985c259b8ed4e5363fd3630c5d0733597c51d90c4314d04a3f4168977c9b530c5582f5cc32d467fa64330cda9c56c18b6a727ce83b1ccbc371866d056e36a36c16d14318a3ca564314db8ffdb04d8c9c5bce3635c9a2cdf4f4156fd82dbbd0c7997cd64d10c4b5e2416f39592898d8eb456ed41d897ad15b0db8cffe3fdb5379951d363 (by decide +kernel)

private theorem part82 : Excludes 0x40002000200000000000000000000 0x32c6610f4101a2044100c000400040 :=
  splitAt 1 47 0x32c6610f4101a2044100c000400040 part84 part83 (by decide +kernel)

private theorem part80 : Excludes 0x40002000200000000000000000000 0x32c6610f4101a2004100c000400040 :=
  splitAt 1 58 0x32c6610f4101a2004100c000400040 part82 part81 (by decide +kernel)

private theorem part78 : Excludes 0x40002000000000000000000000000 0x30c621094100800040000000000000 :=
  splitAt 2605 69 0x32c6610f410182004100c000400040 part80 part79 (by decide +kernel)

private theorem part72 : Excludes 0x40002000000000000000000000000 0x30c621090100800040000000000000 :=
  splitAt 1 86 0x30c621090100800040000000000000 part78 part73 (by decide +kernel)

private theorem part70 : Excludes 0x40002000000000000000000000000 0x30c621010100800040000000000000 :=
  splitAt 1 91 0x30c621010100800040000000000000 part72 part71 (by decide +kernel)

private theorem part68 : Excludes 0x40002000000000000000000000000 0x304621010100800040000000000000 :=
  splitAt 1 111 0x304621010100800040000000000000 part70 part69 (by decide +kernel)

private theorem part66 : Excludes 0x40002000000000000000000000000 0x204621010100800040000000000000 :=
  splitAt 1 116 0x204621010100800040000000000000 part68 part67 (by decide +kernel)

private theorem part60 : Excludes 0x40002000000000000000000000000 0x204620010100800040000000000000 :=
  splitAt 1 96 0x204620010100800040000000000000 part66 part61 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part87 : Excludes 0x140000800000000000000000000000 0x69bb32044014280001000000000000 :=
  finishCode 141 0xc4531f0dcb667179d7d6f018b10730c937af9cf9f502f160619cc379c43ed46fa218631718b8037da13a222f69bb2ecd29e88b66a81c56b59da23a1abb3156bb36e1b0dba18712f5a8aebc4bd6a34cb006dd5cb877e25f426d4f445bce2b633d8ada5b5efed450d431719a8e26e26818b18435599acee5cc52ed4d846812a75a9accc56b7999ed677508ab864d40eb53a84d2d4e99109d6ed6138979acd86459e2132a70d05ad4e25db0e98398ba1c6d4c30eb37852c1ee656d4deb586459d84660e435193611dc67389a88c062816d32b2f64df2da326c26c334c1937cbd8c9bf280c27785bb986460f41679509d9739f46a934957ad45eb4cf5bb49468ab333a25665584e26f0c3a8602913174389308c18c9ae0d676f5adc7348c50220d84e2069958ad9705a774365c18ad69d8ab8cf6a737cfb539a551e9800999ab5b7621696569dd0d09761326fb2b984de26885d0d619883c0438d30765631715b4c1ee350c334b6937cc88c9861d0226e5e9b29333a5318399590165cf72997a2286b4d76a734fa56e88da1e11b5ede2b929f0b78c5b0cccad32b366ca7b79de2c1085c9a656d15acc9bd866799826f743c2655eae8959917cf972d796435b53881a645795eadf3d7934dc5a9d10332229ad9b1534774cada9cabcabcbcb6a700c048181e5039896f3607940e62dea6991a3b8186644cf572e9a582d4e40d881b479956e36dd5cbad1e7839955f3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part89 : Excludes 0x140008000000000000000000000000 0x69fb22c41428001000000000000000 :=
  finishCode 133 0xae50249906198c5c17a6895449459b021dcbacfab13731712a4ded83457afb87cd84b0db2f6b96d628928b318982fbcdbede2c262eb377afbb01d2bb4924bf98c85c1dee6c16e197b4494598afa595afd0ee29c4a64cac61bc609bd0d6130a39bb580f09e02779f7b5a6050cc26857379e1392fcda364aa4c146e613097c84b2da22dc6f6b15ef6b3eac9f34d3a22b92a6aa1f3c6b01e62e19c4539c461f565e995d0a76ef6f16e481b469be60389f8b3b29a9bf44642b6bd0a7891b43656d0accb429d84c29e60361342bb64c0cbe9734f96056135e3b278ddf0b4be1b70c113265f7a695295c9a9a57dc5d65296ef7c7b415e370c5675afe62d7de78a22de34b9beacb6d863317189235eb09853cbee2eb49f053d54cc6428160445c456097e6cd1831938a137d32a4df68899ed4e6f3e4df1c89f9764995446d1e8a5d1189fa6713510479797265b580e245eed4454a5a3e61196d5358a688cd5ac07a23347b02bddd27c4de4a33c2b5e8c9c529930a02f3b09cc5d32a7772e4a7ccb9ae4d477316ddb47fa22d7ad7b46210fab4afaf4e88997b817de7d588b605a57a93f09dabd726c279737a2d08ae5d94f95356bd6ddb2688c1201304b333d6ed3ed984d3b640f61393e52cccf49966136ed94a6613d11d46409965116af9955356058996 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part91 : Excludes 0x140080000000000000000000000000 0x6bba2ed42801000000000000000000 :=
  finishCode 123 0x15c9250370c336444f9a379c67a143287cc23340ad98167d6932eeb332b6666c0631718cbe3b79cadd32a31774c85b301589a056bd4d6a3862a222fb007e4c3d122f776a72ea28f686bb998fbddbc4d66ebeb045f70af17d51d9f3eca4cf705ea3b9a19eca6ac07bb5277d1a20ecddef65993fd8999a51114d4467bfb379446d454d65b695fc318adb517bfd00be854cc06c2685752200856f235a9e82c4583cc59a938c9d11730f16748b5a4cc3a8eafbe4351b8b246330a4f29f2948c9a2cdb1416b2f94f6bd0ad8ab81065993fd8997bf1935294596f3943d166c9400ad98b9f1dbceced6cc62db0de2695d79f8ad50f9bcdb0c62e1de0af8c2e0cf8e152beec278079f8987436b493bb789319603c85935134984b14d63104a0288da9c4b288b2db684d9fc50c9ea6b5d9611445a5b5f3625933d51196da8ed32ed4e60e5298c582a198983949c64e6140527c31aca509c5ee60ea3b799909e646646527b53d11ad36cad1165b66569758b396d193a041230c23688b79a13a22cd09068b37bd6d36dd183a64584ec2f3e76f326544580410cf67cdb3fa5b65edea68ee8ad5f5c19cc379c88a316a07308cc280c276033d899580dbcd80e5c1a62c5453e4cf5ee6d115f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part93 : Excludes 0x160000000000000000000000000000 0x69fbea800000000000000000000000 :=
  finishCode 41 0x31190ba061de2e15c0b5a00c8999cc330e3492284a2667196c48cda73232db361cd0645ac68a96056b39865f8dda3234c359fc4bcc5a22d106d8768aa265cb7b67f692f0ba22c32876bd33e6c682c3374aa5310ae605613191a0431cc32bd335eb68af4cc0a8572edaf4de2e0c323233789a0a24b70c323904318cb46451650ae191 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part94 : Excludes 0x140000000000000000000000000000 0x6baaaa800000000000000000000000 :=
  finishCode 179 0x174b66c0686b924c830ce83311674ca9a0cbbb0185e862c617d580df3e97398d95b85fa6150f7cf89be7889f1826fa65977509da36a6b2fda659774bf5ea741308c301a0bda0af4765f2b6bd2f8ede32b7378d492682de3524aee9a0e634190a605e862c4fd32ac069bb459be5a87c71d8856de2b9f1a0ae7d47eddb5a4c4fcc5930e42188b3349e21fd24cde2d634a3287adfd37d0fb167a233cc8b1a879a0cb9fa23312de2857185f560378287b48c49284e5d31a0a6ea6eda22683988c05ec41d96a70b1ccabcfcc4beac22d265f786331798b32f605a57491662d7de6afb53a6f9959738cce603d05c2781729bb309b78da265543d3765af6134dda78d672edb60afab78e88d692f1ac26a1f32b2444f86137a00d4c38636769b2de35a9a6ed9dbccc87ea1fa0cc62371700c5d11980660ed451650fc2e6c178b259fd6a2de2a4ea6b3c43bb435bc699e6ed50f9a21dda9cdba073688bc8e87e0bda9b60d140bd6a511af5b754169652619759a1706f3a2cc1fec312617c733dae0f80279b4e5ec076d4c58e2ce596505d05a625f1f6178dc30cd5179686944579bb53d1160f79fb09d4a5f0e94df2d796d4e7adb4789115f527dc688ceeb12384ebe7116c1e8b2876dbb5c0ba68afb53d1143f8a99b35f0d4d6f15c9830cc630c606fd096f350f52760366c0dba1abb2d671571c9a2914d4cced116cd79fd1181b7436266991141c276916f381b6d1f4456ce8996c37c3317a51d119a473446535899a91743ed4d8054cf44625ea3b5e59636eb61d317a22baf6a744bd92d4e8915275f345960f5ddad4d16751a08e2edaf4862b78cc0ebbaf8f30ca15e4280de343ec59a93b0ca2cb0aca4e87ef83419b7dbc56fd0aed3698b341607aa642b948b4309d10ec328768b3709a684d0c715ac3287f2c619a2ce5d74467856196a3976f446d458650ee619333a9bdabe65532f44511741a234af9a0c56b0caf4be10ae6196f187da57f43426cd057a6 (by decide +kernel)

private theorem part92 : Excludes 0x140000000000000000000000000000 0x69aaaa800000000000000000000000 :=
  splitAt 1 113 0x69aaaa800000000000000000000000 part94 part93 (by decide +kernel)

private theorem part90 : Excludes 0x140000000000000000000000000000 0x69aa2a800000000000000000000000 :=
  splitAt 1 103 0x69aa2a800000000000000000000000 part92 part91 (by decide +kernel)

private theorem part88 : Excludes 0x140000000000000000000000000000 0x69aa22800000000000000000000000 :=
  splitAt 1 99 0x69aa22800000000000000000000000 part90 part89 (by decide +kernel)

private theorem part86 : Excludes 0x140000000000000000000000000000 0x69aa22000000000000000000000000 :=
  splitAt 1 95 0x69aa22000000000000000000000000 part88 part87 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part97 : Excludes 0x41400000000000000000000000000 0x38cb6e22aa00000000000000000000 :=
  finishCode 159 0x672f9b4b80c8cd0a0ea5b34d43f453ec3bada1f1167e29baf3a8b2506e8459903e2d4687778b8b331f3cfb0c7446d47446c3178b582f0ff6d362f1c31d11b51129d11acee2ce129824b1f08776774c7b5f98fb6fd2ec69a69b2ecd9fcb6cc1e88be2812db688b6fb78be48efda22d1ef16dbf20097a63db86b850113e0b5459c04e114c2d5f0f174a7e88c31b78c3ec4aba2383385325db60da8e0bafbc3128a7407c21db6fcde2f933c091862626e96d9e4b6da220772c69da2cb31e312dbef8611817dafed9307302cc1d249a452e069b3c9029ccc2d10fa2211e86a12f618c43e88bced2acc7cc26de686a093309b66bdbdc28086b682da98c1da6d6a7676a43407c04bd2aea12f933c887825c26541a23369c43c4dda4d69b65f5c279405217c5e142f446a6d7c916ba53d88f5f12ad9d991da9d2ad36da9da22c47425dd82fa1a427322f16d0b599e17e8892ad82f69ba2340b3f860e9b542e00f87cd4bbad35e2da7e53e78bc17d11b4db5191168734fca7cb2ba2f0c41459e2df4e8132b59dafabe4da1c4a27e2beb038cc1da22a13707c48268a5f68892aa15b09a1ad01f266c34ff523c03916eec29b3bc2f5bbb4469be20f78ba0684d83ef6e13ef82e8d099a757d5e2cc0669fd093fd5f5c1fc8413014bb404dd860ddd5ebdb0d2eec2f5bb309b0a483de2debf012db5a6c40e88a97b61da8c976a5f853376b09be280e8a6fa5bf444c7d7d5f25f4d6ee6c3095b6618d29f66ebeb692882e1acde55cc7d764c06b37c29c196bda53e976f94043f34d4532d3a27e90ed45bcc17698fa5b963a021a8c1c9774e72dade612b14a5d8d36cee (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part99 : Excludes 0x40400400000000000000000000000 0x7853b6022604220200200000000000 :=
  finishCode 87 0x7136974e06b0d94db61f60171eb8639916b54592839839bd7797c920d2cd2a1a2268ad8b59fca79fca7093bb7ac56c9bb85e44b4d7442c4bb7acb1b14022598bb44537504d3763b97776a16a19efc256d36d11c1f6cb924d22068b6c6e56f57958015e5f42665625e3f9973801744694db5694e98b6f59024307ea3b995a6b95d89869365ee5ce79b99192112d84ad6b31785edea31aa7268b40141a6549dd4bd316c29c2f18dac6b21f65396f528352f9b2ed1187d6c536bcc6b2e1204534598b38985f44d065bb97579b6a189850eee98ca00c2814cf365bb49a83a13b32b206f5ad4f4156ee94df457d679b41d85a62375f73216136f58c968170d65a2b08628b2a175a9c4ba97c4bcd9b107c297a1fda234db12347b15aa1747b68792f8c8cd9adc6a7334ba5724030b683369bd3b79afbcc23366a91afbca469bb3e7930a8ba97bcdc83a65adda8773c79b97d5eec6146365eec316bd261191 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part101 : Excludes 0x40400008000000000000000000000 0x397227420240105008080001000000 :=
  finishCode 145 0x38990d05d2a06db70921bdc12d4ec257bd2836056eb6f5991b445b6ed4ca0e5ee019605517de491816a7406a580b56ac59dacfb11469f97d56ae7a769f9654cb96ac89cc7deb584eb415abb0451acf0a65e70719659958978855bb92edabe6565bbd11965b2f81dc58d03ed4f4461a5b53283b65c2606d7acaa365941b02da12a12a5e227302cd9683b536c59e86a97941ef261345bb8805dc532ecbd81584dedea6fb495f5962fbcd5e877a232f26564cbb53a578eff0be1bc23e625424a0ed1144536ba05a3591c43b445c2f9f25f4ec04a32d5c37da6d862b7620ef0714824923883b32a6ab697046da0cbc41d704cab62cc706631f3e94bd9a36566cfd6eeb3f133a22ecc4d56c2f88315b17f995984905fe2516dbd1185fdb2c2c5075076b5386f0b1924c7d4e785369ba22fa666adead88ad81bf44469456f4261a5a81aac12604a3058c48b75b7ae302c6c196c5b537879b15f3f424696c2f0b1d116dbd1188869cf07c2c6a940b849148c21e9953551779f266564867b524be4a028d2cca9aea78da9b51cb57833a234927fb32a6ab50248a2ec270b1da9b09da2332b5084309da1cfa36a663f853141d6a6bcf68b65c14564453430b58a6f2692f72d5b5eb08d5179e5ee43b7c9885b44459d6aea94031fad4da8c92dbb5f4e9862e107798f31f96fb53b4d932e56459ed4d6af4466a35ab7c9aa5c258c04457839f4e22dbb62ae2b5f4e899b53942ecc7444d0dabe43b167d117d3b41ad4e25e26542e8100b83c3da23156f3a686a1754773ad4e215e95f4e21698fc1f6b3c29c29a1bdf4d425426 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part104 : Excludes 0x60400000100000000000000000000 0x7953eeeb8200a000c0c03020000008 :=
  finishCode 29 0xb4602b170a805abe8cc261533c6bda1de62c645b06d4e9a6f2a0f86bf9af7445845b7e7954b536e1b4b96ae55c944626d065ab4cba63d84ed4d6ae6bd9e5a9a65d31f13331f529ad5b5eda9c323a22bb2dbe16b53062619169dad4d485afdb861c6d095ab52143f18d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part106 : Excludes 0x42400000100000000000000000000 0x7b53bee692008020c8402120000008 :=
  finishCode 27 0x198de562c138b6461f1706bf6df61382d5e562e10635f5605c04f02d660eb2f98f26160518598397dd3b64499856131894eda615b4580c6142d6e081f2ecb72e88b6d930a24da5cdc36a69da4c20a73cabdca2485ad35d6a3862f7216ade289368885a85acfc6036f5ad4c6242b584ed2e0ad (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part107 : Excludes 0x40400000100000000000000000000 0x3a72266282008000c0402020000008 :=
  finishCode 167 0x702a934c86b0d9719246eb86745f4d56d88a6b770c68d2e88cd62dbedbf053b629aaa29addc623a1a14edea30bbc355ec542f9a01a5541418f0c5aef16076d7f0ee7db360b78e88d13ed82de380613973b0a7445a7623d4af20fc291a5b0a62d3c177d178319d90054a15d167853612eb0db6f9d894f9f443c406503dafc695b7ca0f38c419d6db9015e2d0166db31fb439b97196c9e49225d7d62b707e7bb599b0c4146cec83f07de2eb375f5b519e2de2e7a994857d5eef7990a8582e12437b82343b0dd6d3f3c2da0be7e14c5e286b4bb0e3141e32d067b919db539659b6ca0ef8da3614941e0fdd8cc5f2789db4c78d2b67b70b02cd7e34ae87d1ad261be60e96dad0e63ed4d84e2670a6a5d261b2fb43c6662f8f4e0cb5a9be58cecb2cc0ab776a634b309b09d306b574c18d2941d43b17c613540d2b217a5a464b313713fb2f8b4dbc56acee62272d369123d6f19c4416eec293bfb2f103ad4de6da7e9aec2900d5bb003a615e9720ce8aac856fa386360fbdc9308d2ca85abb530b54a7903ed25a9698fb65f359701a5d04902d5f36b2f6e5345a63ccd29a31b85f0c6d30b194a708c6dc2d030b05abcbcd8adca30b36fd5249709e3c148530dd7a2352bbd5b4fcb6984da2331365f3ddc4200dd7a23130bcbb72bdd9a2d65e7df34fd9dca6b6ad9bc63ef2aa12907a688cbdc0d785e7dba1360fcb6cbdd26cb772f7988a535d32349a4c2fc4835ad322d3ed96f06f7330736acf9f322d3f0df12f482a1689e130d6344698369f8858976df6dbb0bcd174456be6bfd11a3bc29a8eddd65b6d465ef445b96b1677001b5fe88ca6b6fcbdc7f315b677a22c4d11b4d8ba503e60e215afe40f (by decide +kernel)

private theorem part105 : Excludes 0x40400000100000000000000000000 0x3a52266282008000c0402020000008 :=
  splitAt 1 109 0x3a52266282008000c0402020000008 part107 part106 (by decide +kernel)

private theorem part103 : Excludes 0x40400000100000000000000000000 0x3852266282008000c0402020000008 :=
  splitAt 1 113 0x3852266282008000c0402020000008 part105 part104 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part110 : Excludes 0x50400000002000000000000000000 0x7a72fe62c700011001010500a08000 :=
  finishCode 81 0x2d9acbe6802c46956ee26b99551724da93658d6ed316656d0c89a1e1c10e71371cd11a92545e5ee926523d1195da55e656c17094297d322a2f15f2de307653457b65cc2d15e1324c3170ccac57cb2c82c17094297d15a2de30613f442b65c2217e7adb43a55e85f07399597b261957860d4be41708a58096e2568ab09f183d05a94e937096d1189509f183d05a1c655e9349865ede9e55e95d89552f183b84c8d2c6d96a5f83f4c8dc2f830b05ad821030606f25dcac84fe8896cc41609b32a13fa0b2d7d29a6e930cb2f84c34a736fd268c2b1293694e97b3c3a25c26694e2b6d11099995c05c3446a16068370c656d972db0c193bd32d2caa174a7e1793bc71f4696d8ad99106bb435b3dc0b4071a53d42e5edf128897942e5b68ab0718ada17de263017bf8af (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part111 : Excludes 0x40400000002000000000000000000 0x395266428700010001010100808000 :=
  finishCode 143 0x6b2e17cc85a3888b380a84802d634b449da2f4d32b32234a6f72cb13e85a8d2c6f634b42fda0b7093ee88c68615f34867110ff794c1a5c2f8a0debf4453b65b6d1136506b7c1b0bc634ded316656b0b571a0e0f8c6bcc92f836cf03156f3374c0582d86f74872d8a62cca8d2b78d0df156ddf3bacbada89bae888ce941ceea22e34a6caeeb141cb1be2c0a16a2f15b1b5c34cdc34bde87b658d2941f63894cc6141be063744609b89f42b1e3826c01c3edebcd061f657d0ae5b17b75bb95f5ab6ef0a799542ba22c696656990e3378e14b09a8b8c8bbbc856a2f0ee31b4ca8cee42c16836b9a3e03d68ab6cb613957365435aa04dcf5e6cb4e7443c42c57d5278f5e908ab6cba6557d609f5f5a17e9918ad79da2b4d96693234cab029b2a1ad5238f93297be9bcec6eab7742fcb2bcdb126562ae6e37af7d33ed896e8eed9c4be4f0676b0f861396ee655b3dbc658dc28774afe88cd632dfd94d54ba60265636d7af8d96d0f8b29a92657d8157d6256b496a36136a3ad2576c4e7b0fc902fab02acfcd670befa30bf26eaddb59d2ca2bf4c1971b59add930c56cc067fb4cad66682dbeb5632354965f2a0877207ad9b0df45e6eb4d9edcd9412636d7c98d96410bf442c4bb59da5d30712fa23a0da712e13036b2619bbd7d665584d076891863375ba308c6dba1f20eb51afbb09b66cbeeddac2216b740a797d460c2d70666cf5f768334bba126cddfa1a13283a30b04771a24661627f0c5b85076d365abb4198fa3f09b (by decide +kernel)

private theorem part109 : Excludes 0x40400000002000000000000000000 0x385266428700010001010100808000 :=
  splitAt 1 112 0x385266428700010001010100808000 part111 part110 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part112 : Excludes 0x40400000000000000000000000000 0x385226428302000000000000000000 :=
  finishCode 95 0x71186769c0ba682a8f9b686d31cc8d9dbd7d1ea27cca9b69aed432170c0410ded8168950b5b536d56f5b4b91266562bdb6d816216a7141b6dccaa8bb7ac36d6a6dab32bbc9a045d15f6a6c0abeb0d2c57d6a69bb4ca8ceb09c57d6a634a507ac35518d90ed13c29ed65c3414cc8141e02cce43536b8af9b6d4e545db954b6613539945e654dada5695f42b44faa312d4e0994f1509be6f10ecd0698b6c16f1a3f96addce62e95ed4c246b4d7c9605ad4e6170820bfc6d70fadeb8010d892ed3705dea4daf05e7a951777385a70c426584f06652d321be6b2e034a31b05accad12b15e31b546e594854e46165ee9834dd5ab3219950b5b83e7d32adeaa72dab348a4c1d12b32a68ac88af8266d3444e86f895099b43b31703219bd61f70c665426c28513e6915f4cab708c2cc5cdbe8764fb0c2dd3217044f82d778b5630ad9f378c57d6a6c272f38c8d52e1ac6039164c8660552d09b86fa26d0eed4d425bc5816517b53 (by decide +kernel)

private theorem part108 : Excludes 0x40400000000000000000000000000 0x385226428300000000000000000000 :=
  splitAt 1 73 0x385226428300000000000000000000 part112 part109 (by decide +kernel)

private theorem part102 : Excludes 0x40400000000000000000000000000 0x385226428200000000000000000000 :=
  splitAt 1 80 0x385226428200000000000000000000 part108 part103 (by decide +kernel)

private theorem part100 : Excludes 0x40400000000000000000000000000 0x385226420200000000000000000000 :=
  splitAt 1 87 0x385226420200000000000000000000 part102 part101 (by decide +kernel)

private theorem part98 : Excludes 0x40400000000000000000000000000 0x385226020200000000000000000000 :=
  splitAt 1 94 0x385226020200000000000000000000 part100 part99 (by decide +kernel)

private theorem part96 : Excludes 0x40400000000000000000000000000 0x384226020200000000000000000000 :=
  splitAt 1 108 0x384226020200000000000000000000 part98 part97 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part115 : Excludes 0x48010000000000000000000000000 0x3a3e6b0a6024008000000000000000 :=
  finishCode 127 0x702e94492530d54d7678f818db4db0bf0a423ed4ccbd3e640f08fb53b53a29660f615be673b13828f95f9856576b319950a9989a04405de99552f6e3a6550aec290a918d289a9bec299956d309d52fa03a22960995ae371c4fcf82c2af92c3369b4c58b9be4ca72c32a8dc52091704cb80215cafd2ea506a46c0f12351fa7ecc336a77060798650ad3c6d05b533296196d3a57d864a3c966793b534cb619dc522e168f51fa15a9cb03de00c698fb536194fd975d03ea61973b535095397c98c9ed358671104b53619289b4da62c966d364cbb4b9735c1ad350ad7924dc5a9dc1b851f13f278caed83f6825cf599d34bd1a78c61b14d2097193e86d83e09731b20b89bda5a7cc4fc85651f853b8d0052c85783e51f38c1fa6198565ceb3f9397436d0708c2a73948b8682211cb499e2ed4e27e2cca3d4e583d856656b53601523be400a3e5d65f998b4fd9e8d81e95f98b78b93c56ae57e5d581d8551140b5360b975d32e6553c64f1942424586657e9899864a268124bc5f18674031a1334c4a84a9cd33cbaf1321372be1334afa9c84cc68aa72bc607a57d85665740c0f4afa97b0ad2be1533ca65c0636cfe5f30a9959a70f6b50c23a61c2a4156885c2912598bc2f1f7a9265758560a9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part117 : Excludes 0x48100000000000000000000000000 0x7a367bc22408000000000000000000 :=
  finishCode 71 0x492b940d630cf037115f299a1da2cdb0256971b4d535b533550af8abad4df4c01e56eccd4d6b031af5344a848caf846cc0edb712b93ab03857ee2d9605f382c4a07814c80288cbac31ac2af9b6a74528c6c52cc2a2034bab0a8c6c4fcc03122c2b346eb86342c4d562cea6598d18db53ce5b279c0b4140c010ed446615b538cbe245ad6b53355b84023868b4c2997bd4b03b0ac129be17f7cfa61a5758060b18a2f0d16995b051fc68a49715b6971a2cc58afd37b22b0dc32f063904f0be989a6908f95f5bba93e9a69a608d32fa63d854a06c0c03448a22b0aa9ab00d122c2aa22a6b222db2d11017f2810b19959e658566567991e109b5f38a070a68ab8997d361551b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part118 : Excludes 0x48000000000000000000000000000 0x30177b000000000000000000000000 :=
  finishCode 183 0x6d33988d65f02ee0bfe2702e1ccbc580a65b0e53937b36b86d942c556d4df258654e63733756cd93de655f34decdaea9748a1b6ccacde7786d3ad4d32d82e565426a5b895d054cbb5379d898ca66d4e963a73985619299b85e2d150b60c7ca14b5b5632f9957bd6f59e5f085b55865bd6c2161950baa4c4cbbac0f28897a20442c225ef5666619881b20afcdcb32abe6c2b3172eeccaa97db3992c52f53909da65708f07e62c276995c25a630acf76126c2b5921be6f5615093a2bc5aef160b6440976d2601f01b98586f89784683c2b2ee72c730a25b44ac38ccabb9c50d16897895a10117197b0cc57c68b66708345a49826542457f41650940f95f925b2a97852db4381ded25f25ebc9d586589145097e03ed6a62db6a7047c57d6a611e0fb047da9d818661be985343b536b3b5385866e3619904c5ca5e326d6686b787c189d464ed92eb297cbadc0e2520dacdcea850344fb6aa8ab03e11cbca9d784b0e3666b623270df2f5ad8a90b5ab6ade2e86875a9b59b0c8c985bd516c464e5666a34bd07588b5152754cba1c5a8f095e5e815890297a9cc5222e93679909da6b111ad1cbe56c6b2d869a3f5ab6cd09dba4516c6d0f8b35158ab6cd6e4914567bb86986162cd076d1e88b1856a390756c45a67bd7cf185be5602de20a2f297bd1c31f141559bd5866656210df2d5a09d1eb75b0ccf9edeb0c7dc22ce607b5336b375ba760db6f0a234ac949cb178877667276bda840b56da9c51ed4006081b314fdb4161ceb4dd0fb537b56f3a6558650ee656b5395d293533aa1bd9b5d2143e6ed8b399593cf0a662dbb665650fc46729017758a00c9da9c65f1173124e2c1f288a22cc1e89364a6502a84e2f5f288a27b0cd84f260cbcb75b7aa88b6dcbd688b592904faa5322ca9aa22d30aa3ac3332ac33287a22cd1856189453e64b116549e4c5a695bbb5360f6f5b0a57e4296d4d83eb539950a5 (by decide +kernel)

private theorem part116 : Excludes 0x48000000000000000000000000000 0x30167b000000000000000000000000 :=
  splitAt 1 104 0x30167b000000000000000000000000 part118 part117 (by decide +kernel)

private theorem part114 : Excludes 0x48000000000000000000000000000 0x30166b000000000000000000000000 :=
  splitAt 1 100 0x30166b000000000000000000000000 part116 part115 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part121 : Excludes 0xc0001000000000000000000000000 0x72bea2028060600008000000000000 :=
  finishCode 117 0xba702a944be1aae42986ca7eb346e14a94c558caa99c8146ea0f975219f4d398b7da0c9baddf5a0e31f032b1c16f92bdf25afe655bc573db168343898be12c3cf32b84e2df8533d7bdc8b7da2b70ae7b09cbd3455cca9b2db319a0dc500315bc6c232719956139a85bc6d4ef978b41195b47b0a45bcff57a498d46d7a6871c1f69dc23a73a65420708db7e87119599540d887e65584f19b8167ad4e2b4315d0a53281c56cc14d65d96bba5b081529ad4e215aee40ddc6629948b6621eae8af5355e76130c5be4114cdb963f9b476f50895117cfb479f462566565365cb7ad08b8af9957ab53583170a65e70c551ba656d25035b6c31699657288be7da3c40c4aaf3ae5a99bc2d053766bb6db3e5946ed253769960a8299e18cbb384f10b156d76c2681f2f3af3c4b2a22d77375db2f8d6b457938cca8caba17954995089a2b425620ea84a0c3e6f516309595980bcc2cd1620eb2b8ad40f9e510226345099b45a5661ce2bc20c1fe98f7b9c23c25b8412897cb41a29389e1b2e02f7adc2189b96f84166cb4dd96f3fda2bd376615aedbd62be271271825e8816cf8a9c45c0315b9616f271be4c1b7dbc621625d235a2065668738af25d8adbe701b86d2e53540d995b538a99afdb1665540e25d7716cb0556e5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part123 : Excludes 0x40001400000000000000000000000 0x3887a690a04422000aa00000000000 :=
  finishCode 85 0xda71359c0ec6e2d2e5395db1a528929bc65906961f67c3b518ad885365642ccd0faf86ac98da9b5a75f1ed4c106cde08316bb53a21aec6cb48b35dd2d8a0cca90fc59e332198b378d3537513c316c833b35ab729b2d31d6a628b31a84f6a729c8cea13d6cba4f06746974169873399955398844ad2b6a472c99593756ae95b9e491baeb513416e54f15393418fe49dd4bc04e5af3f91f1c25b51277523a8591b2e8992776e5562d5d102f7e08a27ac8149904d42d6664dda63a6d7bf7cb16b8858c05e0d42d3766974cc1a6ee265656e69d5397cf613a61e1f5a76296d066035e99b167bd6e5523b656318a5f1334559a0861c91f0a42beb4b8e10cf9f843308c99288a8a6293531e87c459f8a1fa6e861a2ceb2c998dc0b4d84288a8a74417582746263914b117282a0bd6a31163131929fad18991ad2d7dd844616 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part125 : Excludes 0x41001000000000000000000000000 0x38866a609048208008000000000000 :=
  finishCode 117 0xe26d339acbe5b2a833a34b90e0284d32a8b30bf12ea9cc6734caa8bdc2d154d0229a2c9c0a6de2e3f1c314d398db43573de2e94678bc4410a6ec92b72e30c4d3a73c3181ec85c89de065a1937534e689a73eada9a24890c7fa9a6a67539bd8be1e813750fe53329bb5190fd0ee511a67a696e1c86e28851a53354435825698cd350d698590d65b6646d4ea8d3b611be993dd3310a07261cc8ccab09afada9c47b32b3e2a865ec074c33e9d30d32b4aed3b0819feae7a7284fb09ee341409444278a46a13378b09c9bb32b29b4ca8c2940cc7c82732a502a5b2b7182819a0ffcf1ba0ebb748afaa0c7683838da9b5fb77e86c3fea42f3f6a70c2940cd09ee65634d977ad4e5b6a9ac925f0d34a2645332fa566d4eb0f8289613a5bd0d584e96fa45529a27d84e99534d23d984cc266550d6e148979a9cd80d4cd4d514e30b9f227b098c4cc06c2729ada32134a43e114ed886b6a74c89fee12a97b01b09aeccf6ea1710f65b5a984993aa90d842d7f6a6de2bd231289e32361093a9a0a27d314865f5191613a619bc54be909bb907c5b1b3d0d46468b32754af9e2e29537e3f108d27534190ad486 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part127 : Excludes 0x40001000100000000000000000000 0x399622438040a10008402800080008 :=
  finishCode 141 0xec64389acda6e3396c2878a4ef9a09a14dd314a678d43f5359e21fca36faadb72e7da9c616ae527a676f13df819573db46689bb215a29cc173e52778b8c613b78d4cf1573689fec86adca53348be4914a5b9307bb5c18a25aed49dbd4b96891a51949e2b4a24a26684d140e9766cb98336597b4356cba6441762b6496c9a3e6d110d5ad6599883365959a2aeb374358eed666cde63f0a5ad5693494fc29a20cd96cde883d079665f45e270a4c5de1e51d2896e5b637ad84e34a4f74c982949fecfa3852dead770fb84ea4f70c3196ce27f09e946c29d03cfc102a36fab10b456a0bda0c52d22d4e453529535982fad2f2db6c26dc32e7afbed2904f7140cd225e6cf7c35db355983c2d461df5215cf6dbb536f58ab9afe6354861ff2176bf8c6e1846d0640fb316f15f76bf1859f1d7ded4e185be6d319123358da9a7ebb9b6f93a861c926134275620f5cf1677602e7b2c2384f30f31a65b84336f9ece14bc3ca2b84330f85370b43b09d3f56adb7db45485b46c291756df89d6e88a70c4d28cc26de2dbe8a643f0fdb4ee10e1486193aee2f984f290b01b68b70944d4230e0613922f4c38d8534c277ea434df610e14da4d6a715784f1ecae7c388b4b01970cbef448be1da5988b018d2dd3393419d7d59b6c31514de2e0c59a4c3c9aadaa6baf86e5c299e0ccbf41e87d4dda44d338892f47c7ad4d484ce6b5342b42bb396c0c56db973cf65e2e8b3a635badad66e50c5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part129 : Excludes 0x40001000002000000000000000000 0x789e2640854021000c000110800020 :=
  finishCode 159 0x713699ce0683216c299aa2f3cfa634a4f77c995c27b07c695e7e984170f9b55b09cb6d85368ad5734be5a5ca22ef6f3f60b234105e16f885503a73303c27808d7662162acd94506c1f5d9b51930c88d765b1187c618cf4ea4f85264e47b614a81bd3aeccb56f4ed5785368e5c75a8a6eacce14df330ef651ef8995d0f90ac7c6b456e11a59f14af3e9b01d92655ebe8abb2d97a6d84f7143dc24168b244fa2ccd1d0a5212f44cc55da5ca6784f10b853455c56c48c64e96f85384f5a8a1fa6ec8b33c74367a99d85264e7bf442da0a93cd7f7cba4d06962a627777bcc3e2380e3285d34b78c2142e85f41332f6cf904d42f0a617e93e2d9a25e17f09d04d73db2ee1347c13bc36d30a7f2a47a0f4c291bbe173e85f41352388394be692b3439cc2c57c56d32b70884a160f8842e7c57a91a85824c62ef7f0bf686bb139645cf9aed4be2b54bed0d16f9857776cbb07cc2d73d4bc5bed0d99199579952f995a64545d4bdc91c582e7cc2c1e20cad5732a6172f704fe622be2fb9952dd883cf95aecbecc2e9956bb9e592a974c2509b9958cbed1ccbe23732f88c69bcff65e5e666545068879950f992be55e654cbd6be536512b3442cabc57cbdc569fec42d32b2f77c53390ad1254a4a26d9687c441c13ea0715a86abeb54613a5657062b665427e56661388394f90af0a6b5185f89b16f8ad6bbdc663096b4727d613449459b244dd68f102c264fa9bb309d92c154529522998c4bcfd8474b769748b697431e10b5dd4e6a66c075a0b08a88d42618633bdccad98b08b09da5cbcf5a4da5ccaa6ebbde4369700c345993fd4be5ee32f6df459864660352f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part131 : Excludes 0x60001000000040000000000000000 0x79dfe2c4a3ea3002880010002c0300 :=
  finishCode 3 0x190d07a93e5b572e2542262bd0ed13e1f6191539 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part133 : Excludes 0x40041000000040000000000000000 0x3a962a64934a208208001240240200 :=
  finishCode 103 0x2d139c04ddda5932154b81aae71b6d0765cf41da2b641d6a5b53b814ccdea5335a9b09c60634a6ab6cec2fac34aa475a9a9cda9d58603824ed4d84e5356db6f5b628bc13e33a4ef457b6db7aed26964c8703106aac27279cb894cbe7cb32a6adcadb77c983628cebcfd84e11715f2b61e73bdc57c40b72c13ed8b15704fb018cedf3b081f2ec94dda98d2848d31a117682bb3301d9261046db7c372db2635e461a5599b09d7063dd4eb8a04efe20d03f398841d5cf00d9b152dd03e9b63dd0f90a19b1504ca6630b9e52172e89550f08d091603984eb53da702c990aa5c0d5660c46db40fa9b5ebdb97b014349f533a93a02d4a314da13b62e1394394dd15b705cb8c05445dd5eaca25b95bd54d698d5178694d56f96c523ad4d4e46965de29bb535d997d6f90419d9a362c57c4ee68b2e3613ad7c026db74c784e4eedab04fc631164613b4197669454cd43e091b5359994cdb96d4c2466a5185 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part134 : Excludes 0x40001000000040000000000000000 0x3a966244834a200208001000240200 :=
  finishCode 117 0xb63a38132b74d6593706ab107531bcb949a278cecf0613fb8be3e11665deb4b523b4b973e523a6352da6d97dc9ecd56c85f34089ea5b309af4c3bc13712f4c714caf4a15d862b46a5abee13f0cea96f036974d06b2c98c35d6139b94a4c67770d2b4b8a15a8bb75d31bb8c8436d1368b286a5332b72f3a9cda5c82e9cac066bb598d30e34a6abacb84add84b6a6a46856d4b048c40b098fabb8c57adfcbd33cb2352d152c2230bb8b31a9be9262a6d2e6118af9846d4ee0dab0cea7e84da9c92ed10afaa9fbb8e05f2a93043b459093ad0549e93e895b53ce6216ae9710c529bb8461125b96b536e16d19b94796b53791a4f7c36f5912710b335a9b5ac56b7a94cb6dd4db6a67fadcb7cec3e238f630b2be393bb78b6fcd1f0e6cf27795ba0812f534b62c4cc55b52e2299e08b8ad5ab9e46691c24185649ac3c600d7c388195b6f56e5a56ea0093372ca7c9bb10b64a8552e06aab3b44cc48c4fb5ab7ae230a62160496a5b5398d79d527a216961c316a5b53c296e58ada61509a4c6d6a7852126d0c29d0592b56ad03d40f0c6a6db538919666d447ef415e0e27ea6dc29b4b (by decide +kernel)

private theorem part132 : Excludes 0x40001000000040000000000000000 0x3a962244834a200208001000240200 :=
  splitAt 1 102 0x3a962244834a200208001000240200 part134 part133 (by decide +kernel)

private theorem part130 : Excludes 0x40001000000000000000000000000 0x389622408142200008000000000000 :=
  splitAt 2828 113 0x38962244834a200208001000240200 part132 part131 (by decide +kernel)

private theorem part128 : Excludes 0x40001000000000000000000000000 0x389622408140200008000000000000 :=
  splitAt 1 73 0x389622408140200008000000000000 part130 part129 (by decide +kernel)

private theorem part126 : Excludes 0x40001000000000000000000000000 0x389622408040200008000000000000 :=
  splitAt 1 80 0x389622408040200008000000000000 part128 part127 (by decide +kernel)

private theorem part124 : Excludes 0x40001000000000000000000000000 0x388622408040200008000000000000 :=
  splitAt 1 108 0x388622408040200008000000000000 part126 part125 (by decide +kernel)

private theorem part122 : Excludes 0x40001000000000000000000000000 0x388622008040200008000000000000 :=
  splitAt 1 94 0x388622008040200008000000000000 part124 part123 (by decide +kernel)

private theorem part120 : Excludes 0x40001000000000000000000000000 0x308622008040200008000000000000 :=
  splitAt 1 115 0x308622008040200008000000000000 part122 part121 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part137 : Excludes 0x50000080000000000000000000000 0x32dfbb000440500a00001000000000 :=
  finishCode 51 0x198be622a0176183313207be3aebb7abcabe5dc09dec2f60f6155e3e3cbae11368281cb52e17be3dc1e8bf3a2336dbeab07c118666df6f16e56f578db446c13408fb446565f0df56b978a53877f44441e53de25866d35b7dbc658f2b4c1cc5e17d3233233618667ad12d6af7a75d7624c5d4cf667306263317533b78acccdcadeabf21835496471bd640fd1108960f6157a4d344580626689795b6cb8af6cba8ee17b50b6e5619d1192571bd6345619a3b8ff6d11277895d096cb5f9a83c05ee6f56cb8979795b95375865866d115e5277 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part139 : Excludes 0x60000080000000000000000000000 0x798ff3000500300c00001000000000 :=
  finishCode 53 0xd86336988bc061d818642f5ace6e37c18bed76638ddade7087e448da220f20fe78f532da9c59e84c0127eb15a113a23448da9de370c335444989ba94d0ee1ce6f1b4189baa3d1a812f20bd1eb66b76c59d6a6de74a745284b905d68248282f4a6b576a770be376c8b282f3769a1b76c877584490bb89f932c64c97de76b84811151670a6a6ba6d5d919334398b83d4f4f09e92d765b37446108772408fa595f2744586693e6f39b356b66968be21fc1728b32089ba63c5ce58dbb50d5376b4789bd116ddacaf44424dbcd0d50fdb0ed114dd4590b9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part141 : Excludes 0x42000080000000000000000000000 0x73cf33840403100840001000000000 :=
  finishCode 81 0x39998ae5c28089217330ca2cde361886f5a9ac84ed442ec64e719c6d1b065bbe880c3529d32cbdd85f5a9addb6085ccbaf307d92f1b0a05610ed8657265d76cf5c9ad4e7a75d76df0bb6bf9b7d46d4d668877447c37c7d05ad2f4470c6005b53965c29c2981e575de45ee50ee0bbbc5c2b13427d51194a43cea6b1930bb79d9bd74454a50ee0bb60190eef15c8c30cd82c98632eba13a87a99be1c696a1f045cb599a2a57cd44572677b7c95f3ae0deb688a8893ed8293e42750f5c9533511972631345f3427165ad4d75df1d75e27db1978b53acc5bbd44464c2eee944b83dccc17ce6bb60134b6f5271b44575eb53261b25a9dc34166a16155056bb5f35d7966503d414ffe5f39aeed4d855aee7c927134b6db (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part143 : Excludes 0x41000080000000000000000000000 0x3bee7b208404500820001000000000 :=
  finishCode 59 0x170be5a2a8de330a85ca29a2ccd02e64490b9a69a043f5338a6d4ceb51ad4f444a273934aa4828086b00887a5e62bdb4dbb5692f35a3b07b6ee0cd6a710f31e532d7b688d9bd99b0ad3994cd92490460fad4cd3692e601a6d299299b446b5329929990d6a940bc285cf3a30e5332080210c8db0f41685f5f3b53c31b3bb5397ce9565f3b53b512e18f3e92c517446956d4ed4660f299149b09c1ef0c579461ca66646b53c19a736d3435d05f1b3650553529b9a14ca2221db36596097b51991b53d1180170a6d45b4d910bf59fa208ce001139991b53c31859ecedb0dbc643b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part146 : Excludes 0xc0100080000000000000000000000 0x73beb7e07448185802001000000000 :=
  finishCode 47 0x512c9249a410d5657ec215357b9b536eb6f5c27ad4de7743546df0718bc745a9d8344640f95d51ba3b8add119f4de9d75db110b51db52e88cc6980ca4f10ae898d9e9de765c66eba61708e365a93cf6ec2a4c31e6da232bef6ea4e4c330ae88e3241146c130cc1e9c24eb4b98d17fb538246b537a785fe39246f1b4bad4ed2e6d1d1198dad4e57c5fe6f16ab3f5b24c146e78b40d6bb8ad7c17939abf0bccbe2b617e6d1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part147 : Excludes 0x40100080000000000000000000000 0x3bbe33c02448104802001000000000 :=
  finishCode 143 0x5728124dc30ce62b08768b2b8b0367c4dcde2a4ede30039e4e86a6ecc5c4dc6aade29bb5a6be0d92e06ab2bb362b52c0972ba7cef836a69babaf18b53a2062a509ed4e5ddb24d2606aaa6743bda9a9aa94d6a730a3ba2aed4daadbd6ccf18b4b538aba94e99403e40fc31b3ba5770c5b166150b856293e093b5317f60287cb674774d611b4bbcc6d2bb4d6127705b3ad4543d6ae246d2eb5150f3e7783989ad4ed1b89021da2cd42b04c310b457d99e18b67b78d99cbaf862a1f5a0a99cc4da22a1f70822d227ea1122f4b456e148bf930c71e76266b51a697d3b51a2670c652917f261a84c09862b67a75ab779a6517f2cdad46627434f2e215a07832d5e88c56c3bad9d6a38ca842055e255d11b337cb7d1b2614d10aa4eb87a795f8b3ed470a4fd695db4bb4b8c9d3754cdde7446b51d0d97552793761df445b2d79627d85641b89a30ac6aa8568a7d8ce6321de6f160f615775acff446295bc71974a22d0985706a53a655c1ad4dbd6012eb35dda9ae0e18d10b6a32eb362d166a4ec2b491a06ab317362d1dd32e88b6de88d30f1236a38c877b446d4624498627e6c5914f445857b1609a21dca52a67709841149dbd632f891427c4437d6a681ef7f222d01b16d114458ab9b170c693d03eb5343b79db8472699c511a69b05daed83d85689313618d3381cb6d9aa847e17ceef69b3170ef9c42783cf44583d855a088b4a360bcc5d28da2368f1aac3bda9b65a22818d404279855115856 (by decide +kernel)

private theorem part145 : Excludes 0x40100080000000000000000000000 0x33be33c02448104802001000000000 :=
  splitAt 1 115 0x33be33c02448104802001000000000 part147 part146 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part148 : Excludes 0x40000080000000000000000000000 0x33bf33000400100800001000000000 :=
  finishCode 95 0x5d2e1643758deea1cc373ce661864a66cded11d0d5d9b450bd6c598da1b683a2368ba236618650d64595d99c8d5617a0c73bccb0a6dd36da3c4db78d68f98ce20bcbb281ec3217a18bb86a39b4d0d512649546196d3a1f505eb5379fb417b0c339cb014dda0da22de60db688da0c39d49ebb329b62319b8b206294cc5366da5375f2f05f353481cda0896b799b685ec52c93c36d04b8bae96df56d4621625de263c75056f35d9b415f1ececfd40f5b7459eb5395dd0550536d7c7aa4d0db625e5d96edb536d3d05a5d5a966196b3b214dde0db668a4f2eb294bc9d316d874c5cb9ca1f852fab54b01b6de268a4ef87617b69a949eed4a228783334b3193b5f0ceee983c296c39a3c4cb92ef67921e70e7662a235c00ba60cefed35b7dbc660e3c9691a94566546ed354cf9940ec1b5a2cc5125368b34d31087f157144862b07da136976a6db6debd8c6144ce1e46b5360f027a22da870674466db4cb13b5c90c5864d32ec216a195d98b19336b6cb0c5 (by decide +kernel)

private theorem part144 : Excludes 0x40000080000000000000000000000 0x33be33000400100800001000000000 :=
  splitAt 1 104 0x33be33000400100800001000000000 part148 part145 (by decide +kernel)

private theorem part142 : Excludes 0x40000080000000000000000000000 0x33ae33000400100800001000000000 :=
  splitAt 1 108 0x33ae33000400100800001000000000 part144 part143 (by decide +kernel)

private theorem part140 : Excludes 0x40000080000000000000000000000 0x338e33000400100800001000000000 :=
  splitAt 1 109 0x338e33000400100800001000000000 part142 part141 (by decide +kernel)

private theorem part138 : Excludes 0x40000080000000000000000000000 0x318e33000400100800001000000000 :=
  splitAt 1 113 0x318e33000400100800001000000000 part140 part139 (by decide +kernel)

private theorem part136 : Excludes 0x40000080000000000000000000000 0x308e33000400100800001000000000 :=
  splitAt 1 112 0x308e33000400100800001000000000 part138 part137 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part151 : Excludes 0x60000004000000000000000000000 0x7987f3880028000c03000000200000 :=
  finishCode 53 0xc46c319b4ba5e17de1857a76ad6130b50bddc46030eb8bef14185d119075ab584e1a679b41d957b446d3743d84db9a1f4abbccb50b01c59bddcabcf32d5ba2230b506ad34197dc985e258446465e75db830dc0177404495e9061b445f4de2ec2188bc21a22cd0e24512681acb837111513e28a2ab5f613e88b79b69d84fa22da75a393ae88b69cbee877788c688c686c3283a4eabd2dc275c23a5c7095ac692d8654566366cda63343c259b4d425076613ca435ecc064ead421d9e2d8470a5af7444cb5e2e049d115cb6117a9a99f4468ed84c5d6515453977b0962cdbcc645ab513c2e50fe449 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part153 : Excludes 0x40040004000000000000000000000 0x729633ec0220600422002000200000 :=
  finishCode 27 0x1c0d06d2e160427ad1de15b8ed2f445b34dacdeec988375d6308da5d847102536dd7365b72cc23308c5366db88d0fa5e4b769441c4536d2d4cd84db96511619325b01aaee103e6192871a59864696a4d619aa0d2d40625bae40f6f5325903db6e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part155 : Excludes 0x40000004100000000000000000000 0x3286739a0824800402402000208208 :=
  finishCode 63 0x6b319a0ba5e339d80b9e670069709ea511f56b1535453a6997e462478e7ab7a96b1535189189b61b4101b4469ad12580cdd4deeb8c07057a24992cdeaa22bef86335ea949a6a24e10d48767748b846c1e31232b88a428eca6a87f9c70062b417dcd066db9799dc708580e4c116982686c00a96abef692d6adaab43688b01ad1a9ac87f74ae520674d567ab453355a9467a93551a57a998550fee954a21babc3ca22deb49f21fbd5e82cd62daab968926f696b3c3e1294da24f02a944ba490dd5e6e6e5615a60b7ef8c315f96e54bdb0be18e63e5f36159b157de3756038ded815e6e6f50b7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part157 : Excludes 0x40000004000200000000000000000 0x32c6f3880160001412000001208010 :=
  finishCode 71 0x73369acc65d02e60c119d1a5c4760307814d32dfa2c943d72e0c32d972cab6abd4d27d6a315ebafa1b046e88cc3d832b2ac3287f1036b619a9557e744583d3f6aa5c111637344f29390eca4ed04c02dcdad6ae6d5c235156ebd1198656ad45649645ab9b161bc2c5bd5dde79bd1161988ba90ca078170bc633115c0b944f98651274466cb43594a626d86516582e88744560190ed13d0ee5f7c45e0d0696d0af0bb8c114d853a2231282645360fb7a8c4cbdc31315f8cc45102d4305f46c235eb189c1fa2bea9c03ffb0bd4d583e90db6cdd620bf2db737ad28c32a0bf1bdb6dd92890437ba2a5bd4dee8a96db009a9a4d2daee2bcdeda86373605 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part158 : Excludes 0x40000004000000000000000000000 0x328673880120200402000000200000 :=
  finishCode 149 0x5e6d265741b0e05c2a15436bba2fbc16ec06d5a6eb245f744fa3d9b953f69b5806891d663308ea4d2614490bda4da2a580ca4e5866190b76136ed82f4deee954b01b6b09c18addaf1330cb56b08ae6cc2634abef309de3995cba30c9fecd62b5ebae9ba16e33bac6e060b07c673a0a9fb12b303b72184433bfcada84a09cb2a26ad4b37a9fec16e34af975288cab079a28608b4d0db12a68a1839cc19a254fd42e46646950fe92511a964e0182b72b0c9a2a88cb92d4aa66b7f12b2cae86b52aebda8ee2d11231408aea22bddbe7a09c31eedf3e1a66191a50295ab1a58a0543e3f51a5619a69a1a6245075eedf3cd16b88268776a32f98d2b0cc548d2dd85bf86150750eca0537619d5d75f3dc57399c0b805dcbd30dac328928b28772fbb92f1888af9ac42cc2ee25660f189a254626413619c65e2a8176c1f436b72af9930c9832f9c40a99d49adeb15315f9c8c05d91cc10e826876c03307cc1cbef789805dafacc32fa6bd3392887eb192e11c9825da81b14b0d3301dd36964d86804deb37c3141d6195f719d6f336d375ce761a3688b5bf261b4128141d3551a55a38614d5467511644f35543594a5b4dbcd1646774160ce434d47adc65366e616f5c50f6e36f35abb43576d37629694d0bd9ab74457dd80f5888b2278d2bcdd88ce5c230173b84dd97ac62626d116a04c33c4afbb722463f5b2dad0744771a23104d96b039eada58c4a2cb00d13446b4b189b2d9aeed2e22e296644c9643b5f7985944513d7ded2ed115f9189459d02dfc90314dae586a3d619b3fb43585624744568ed0618e22e6016156e544f (by decide +kernel)

private theorem part156 : Excludes 0x40000004000000000000000000000 0x328673880120000402000000200000 :=
  splitAt 1 69 0x328673880120000402000000200000 part158 part157 (by decide +kernel)

private theorem part154 : Excludes 0x40000004000000000000000000000 0x328673880020000402000000200000 :=
  splitAt 1 80 0x328673880020000402000000200000 part156 part155 (by decide +kernel)

private theorem part152 : Excludes 0x40000004000000000000000000000 0x328633880020000402000000200000 :=
  splitAt 1 102 0x328633880020000402000000200000 part154 part153 (by decide +kernel)

private theorem part150 : Excludes 0x40000004000000000000000000000 0x308633880020000402000000200000 :=
  splitAt 1 113 0x308633880020000402000000200000 part152 part151 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part160 : Excludes 0x60000000200000000000000000000 0x7987e31c400140000300c000000040 :=
  finishCode 57 0x31178c65d2c97ca805bd3105e0a96056136f19b3c2a57a7713c6bfad4dbc7096b53b3f905d79e99140c3948584584d8667d3605187307a985af5f4d7a49d532e6191870b79a21acbd2327642f832683b1a1a22afbd167530b67853af4ee2807e33ddb76da9861bc3a22a91a97e410d65e77bb0c387d984ea0e09838c8e1f5acdbcd7de28fc259a2cde2657662c1e4d0584c9666116ed6e25fc7e26864736a70fa4b30b5a0b825c7eb2bb4db0fb34be36308d0ad12680d9f117120cb9d36da5cd675a9da5d510adbb6b536d3619898e6bf7bd459 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part162 : Excludes 0x50000000200000000000000000000 0x32c6eb4c400110000500a000000040 :=
  finishCode 85 0xc4683217cb828bca5e18216facda284d67731e33a34a183340bb4e19bc575e5bc84659f995a69a4f6c16dfb06c1e7df1e5bd75eb4b413a7148ae197d99d492dbe7fb2d0d66f5c0306a831f47f4aba90afcc37cbaf4cac4bc56f32e9401a5925c103d86620e52d8ada65620ee1549959854fe6c2195986f5179950f181961be6148d6656990df30acc7e14e11a07997d15b5a691abe1cc2a8bd9298f4195b84cac81f2b2c1f32b207cacccac81e65e65f377b00b68d31374ec5906962b60b11959c4c5cf9e62732a81f2e7278d30a16232bd89c4c4c43d2ea2fec02d77682da6af9b0ccbaaf0fe61214135f399584599cb2ac02826d76c33a0b300a09b5dcb1e938ae30aed26266196e119d864a7c682c33019acce17cacaebb6fb77e17c9fa34bb495db41575c694d065d78818fa5b0504e65469585495e6199595f9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part164 : Excludes 0x40100000200000000000000000000 0x33ee63cc6009000411008020000040 :=
  finishCode 93 0xa07332170445913e62e1a528743bce5d29034b70ae4cacf9313ec3285708989a65457e2cccbf0a698b88b89fb23b1f25e4e6f14f9a3fa625e4c46ea4f99540f93e5f4e62ee0fa74cab0ca15b60da0ada2c3332b31310619804c257615f959a5748be6566568a532f94dad366562900995a44c30a63c77c117740f08350fb86402c67bdce378d696c2b2b3347cb9c41e0fd6972e632a7d360b854858cc5e4029e51d0b13ff883829c5df2148b51a6242bd43c5ff18d77437854858da9a65c14e7ff31764177983d035f05f24916b471ff98b6af7791776d1e667319601a54c215943da0d1076971175a99a0d90599a62d3c544622ca1db911782f03cc59da0cb7e8560f390ae40114ec0f532eb0529f4d85f2eab40a5a4fb0c6d4e2cf0c6789b5398798372c0f5382f3d5da9a9ae84d6a6f578634a331300ed27a88cc5c3ba93bd5cd842bb4d851ccbf18d1b4acbc4840d16769b0ef8c6d182a42bc1f6c1f40d7ab (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part166 : Excludes 0x42000000200000000000000000000 0x7387738c4001004021008400000040 :=
  finishCode 113 0x3118cbc5d339340b7d628ecc0aa6a176c86116af9076d4e5bd03ec195f75f59b7c2eec9acae5002bd13e6199a4b6c82ebee892a22dcc31a53cb8706655d7d4fceb518b3a595444d2e0af1875f582222afaacccbef32b166bef53231ac613b87317f67c389b5f799545395f864d8669955115f76f197dd4a6b53449271193b99b8a0300d2e69cf14b116c2a4fa89e87770037ad474141d50fed4d7cd83e18ec5e1a0e82cf8ebaf6a76a3682cb2cc881ad853a0f6632db4df82f3c8bdae0fd215114b2af52292ccc5c45d82804b33ead22d9de14d399a5d21d84348b323613a82da8cb9d6a740b53985c201b834bb519856cb685f97d49c54166119955e7764ca9ead85ea0a66260f436b41e179faee2713060f5d7903ecc579cf464c1d055d76a1c1fd059a841e575ecc6975b3b40fc219739a31358bd3b8271911708e97550541d984cd2e614c41d8d2d81584cd2e7d5a6250eee1306bba2cc64d03d7d4d2c62e7914456c1a57d8650eea970ce229a2ccb1e266a15bbb53615d07ad4c29570697bbc58280a4f4d336fa1db0cb6fd40995a205bc694f6dfc1fa646d4d0ec4163d15cbb53881533449 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part168 : Excludes 0x41000000200000000000000000000 0x3ba76b2cc001001041008200000040 :=
  finishCode 55 0x6b3397cb51b05e6550ed164674697b178dc5510aca4f0a66ed52100b984ccbe6572118aa45140c9ee6566f3b3f905e5e7503605991979f08c9ecfc67c98a5a9e82d32bb8d05b827ecc0222725fda89f8d6a3549e5c1bb64176f3187539b51a64658cff663c9a65661877af887991a63d0d7717c98f9a3e6550ad79ca25125f07cf686a79caccc7a1ad01b4e1876f3503ad4e5ed81741ec154be4cac82f6a615215f4e74b28c3da8b79b01cd6768b32a82e82f5c33830f14085bd8184e6dd603995187603a96e1e3d0596f6bd6dd6135f5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part170 : Excludes 0x40010000200000000000000000000 0x73bf630c402100c001108002000040 :=
  finishCode 131 0x1ccce632e9401a55e62299548a4b9cdc6bcf6a6c26dbb32b2440fad4db4e98b9736157c986f803505d03d8658154bea6f5394179955f3ad4dbb5acd0ad7a67d36c36e3b8572a0857187a309a90d852d7ad88710f58064426986d4d32e62ea496039af65ce8970018ad32fc2940fb53c1fa58ec2940f613c45917a585678bc2342b99552128f52d980d4e618c842b4fd972df5661575e5cb95d995a99308c59181584ee1a0b265c45c4f947c034164cb95f975ae35fda0b69b4bad117b8be3cfd13ea5ec0651eb933c5989e11cc5a90a0bd84731764ba6e18851ed7b265878a84cbaafba91bc65c901d995c1f793a574f96afa654f1dc1184f9a1ddb4d7dc29e4f998b6d3793a27dbb53e4a3e5f77a398666250ae2d397528f521c44c1b931f30c944aecb01df2a05127fb4b9b56e86cad853b0cb09d96c9f340897a6558650aec25d0d8adb2500a258666e35f7829db8e6198c215b47d30b4d2f120ff69b31343bcbacacd0201146d3485c2656394c871984d3e49649c5bb68855ebc239e266036ed6a0f8cddf85fa0b6a62cf10adda2d7309e33712bb300da9b03df1f0695dc294f9b5317719540fad4c12e95da517a5259271b853265640f271883d1b7660f3c7ad4f0bc5ded15ede7c14cd789b538656657397ca6610d316d42c0614e32b785f9a1c6d05b45a8686fb53c29a20ed4d03cf9e0a7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part171 : Excludes 0x40000000200000000000000000000 0x33b7730c4001000001008000000040 :=
  finishCode 75 0x170b05d3706d66f6da7167ccaae0a27b0c862df295659987d6190bd8a30ccd87a0adc732b2bb30ca81cc4e82e20dadeee29b0c5193d05ad4e18f0bdea4a4d0d7119cdc6b11260bd45929baa50094e5f399541d8633755396c197a5bc4dd42de5176031a58dd42dec9acb45986708d444dd4a257d644f98665965117a9293449375dc6b399d8c414988dd862b92772a13312c0a18a5378533bda7ea1d8d2e31ace6d319d0c5c17b41e5edb0c9a50ec316ec3e2c0c234c336ebe1cb7940d71076a6fb516dfc31ad4e8fdab5abe6566a35096136ed619281b03210769856a38ff658f0c5bcd866d36995b37c31a6f32f619d6632f8d674ca8ca85e8d2cd2a09cb4379e38b3cc4a81da9b02b09d52f1316ef3611b0cacccda7a0b6a732ac33611a07caec4c72eb7897589edb0e98b7c50184660eb516edb519af5af66136ed (by decide +kernel)

private theorem part169 : Excludes 0x40000000200000000000000000000 0x33b7630c4001000001008000000040 :=
  splitAt 1 100 0x33b7630c4001000001008000000040 part171 part170 (by decide +kernel)

private theorem part167 : Excludes 0x40000000200000000000000000000 0x33a7630c4001000001008000000040 :=
  splitAt 1 108 0x33a7630c4001000001008000000040 part169 part168 (by decide +kernel)

private theorem part165 : Excludes 0x40000000200000000000000000000 0x3387630c4001000001008000000040 :=
  splitAt 1 109 0x3387630c4001000001008000000040 part167 part166 (by decide +kernel)

private theorem part163 : Excludes 0x40000000200000000000000000000 0x3386630c4001000001008000000040 :=
  splitAt 1 104 0x3386630c4001000001008000000040 part165 part164 (by decide +kernel)

private theorem part161 : Excludes 0x40000000200000000000000000000 0x3286630c4001000001008000000040 :=
  splitAt 1 112 0x3286630c4001000001008000000040 part163 part162 (by decide +kernel)

private theorem part159 : Excludes 0x40000000000000000000000000000 0x308623084000000000000000000000 :=
  splitAt 2605 113 0x3086630c4001000001008000000040 part161 part160 (by decide +kernel)

private theorem part149 : Excludes 0x40000000000000000000000000000 0x308623080000000000000000000000 :=
  splitAt 1 86 0x308623080000000000000000000000 part159 part150 (by decide +kernel)

private theorem part135 : Excludes 0x40000000000000000000000000000 0x308623000000000000000000000000 :=
  splitAt 1 91 0x308623000000000000000000000000 part149 part136 (by decide +kernel)

private theorem part119 : Excludes 0x40000000000000000000000000000 0x308622000000000000000000000000 :=
  splitAt 1 96 0x308622000000000000000000000000 part135 part120 (by decide +kernel)

private theorem part113 : Excludes 0x40000000000000000000000000000 0x300622000000000000000000000000 :=
  splitAt 1 111 0x300622000000000000000000000000 part119 part114 (by decide +kernel)

private theorem part95 : Excludes 0x40000000000000000000000000000 0x300222000000000000000000000000 :=
  splitAt 1 106 0x300222000000000000000000000000 part113 part96 (by decide +kernel)

private theorem part85 : Excludes 0x40000000000000000000000000000 0x200222000000000000000000000000 :=
  splitAt 1 116 0x200222000000000000000000000000 part95 part86 (by decide +kernel)

private theorem part59 : Excludes 0x40000000000000000000000000000 0x200220000000000000000000000000 :=
  splitAt 1 97 0x200220000000000000000000000000 part85 part60 (by decide +kernel)

private theorem part1 : Excludes 0x40000000000000000000000000000 0x200200000000000000000000000000 :=
  splitAt 1 101 0x200200000000000000000000000000 part59 part2 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part176 : Excludes 0x201004080000000000000000000000 0x4de3a9c190b44a4224081000000000 :=
  finishCode 119 0x45270f0ac3ebe6220dbedde81325fda2842cac8b9da3c97f4888281d2caf6a10e2e6a6b4bcceeab4a96649390e20a7cb96a6a6472e5ca6845a04a08d67a11683758cc47240ddede310775840585f0b41ef444214136775b4f535617a45b444cd640e8c1ba63f4445cf0b618e8b37b5173b337a520849da22f6a66a127688e1220ecd118c3c24dec4cd5f55a1247b50818cd5dd6d0f9519dd4cd690e7a3335a44c0c126a06a372fb20df12e8a6719ac3cc50e88d31f4e611759a8acd3249c47e401a4607db4f3351618b588db4f9ed4cd45875998ac3417fded6335b4750f7d5775acad4cd6f6d1df0d4ce959d11951852e64e5674461eea43d0fd1196b335d664188c2f14b2f1d9eaf1d30b25ce88e0fda2ae3da7da7da2313e65b90d67134466175037b55332ddb43d78d85d48f6359eae5bb344698f981411c2dacf49067d5b4fd63c0456b4f409a4551bb535ff903b185f0b66913bd41b07d9a4690ed3f09a233da99aca8cd23303688a0da75bead632144d634185dd0f050fa73ad4f446c2da73b479e8e9cd4ce2d6b456dfd119c3ead4e7a2368a2e768b688cb7d21cc0d91b7dbbed16535b53ad166efc82c260744690f0a694da63b4db4fa5bf0a53b6b3306996f8a1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part178 : Excludes 0x200004080100000000000000000000 0x5e3370c318b0224204099002204008 :=
  finishCode 59 0x184d470359486179b954cd4d6e166745ab0b865b6ae0dc66ba22a3ac2f00941c10bee148769745ad39b7a99ada229d7520da0da5b6dda234b74e6c4583bfb72d99d2df85b31f69f452c4fae5c7df3024cef0ae3b1f5f42e68f7d5425a24b6cdaa4cedbf51260e6f59916a56175e396d909707f70d880377b57d2b3a16d4b11eb4b142d4b685cc4d0cabf69c2de2c2f3118266c1d116d56e5802c34466096f542f87b94fb42f446285bd6d050be53e15db4dd11335806a10bf80a6b065d62d366f1267b06742e5be267d11ba70185f42e8b34c5b42c576cfe5d56b1775 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part180 : Excludes 0x200004088000000000000000000000 0x4e3360c71990024244481911000000 :=
  finishCode 77 0xe064351ac8e4d370a3aa6b9ca739dd445ed16d3432db166f5617b0a4ceed36319c52789facf43eed369a5b5432585e617b07c324cee5e3b4d867d11c295270c9b83b1aee30b4b4a6da7cb3d22cf3fa1e44f5a6a75b72e87c62d3688f4eb7b552687d6a716b4e769f521c3d82ae88a12bc25e6b53d1133b6f58c61240dcb38803b13b6d1142f96797d2efa23e22c1ee5bed0f0396afb4da22d8274461e63cfb4d95196788fa5e65f50be2d788f9796e58a4610be2134967993d0fb0a629432ccd6cfe88bd0f77fa246946cfdb860b68f0a2865e87ae5c31d117a1f1858433d30a2e769b10d117d5b0be9a65be64ed1ea674f98b5b446011488212e11e0dca81359ee0fda7d0f74a788b846b6ac11b58884a7da222734cef6311f3222df1434b6da2e88b52c7eb0f72f783f846af97570a5b57446b3f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part182 : Excludes 0x200004080000040000000000000000 0x5c3f20e1959022c2040a1402009800 :=
  finishCode 95 0x3c30138b23ebe4389c0a637aca4ea6b844259ec5bd70be33b97b943bfc4cf2da65684b69f685be1bd199ac62b12c6176f15af8f74cb565e596246cfeb35a93c22d85e97b5cb8c401bbecd65971595c726742fb3d9dfd72ccb65cb0cb80377e1143df0eb35c2db42ed4d024ceda45e8e691ac66321c45fb60940394d432f0b689fb4fd098e2f2d3f0a68b36c10cbb53a69869a2cde470a6a6d8b30cb3c39a6cfd65ad70ed4f89909819bd54cd0be10d5cba605d1c05fb685a9ae1c9a6f46a672e1be1ad2c12f6a719aa17b0bf125164807010bf30a36197450b0bb72cb4b61248c4ac372bc8d4d385f4dad2af3e19717ab4a865ceff2d7431c196c2f90a2611826987cb3d1ae5b42d06d0b3bdd0f7b5b35b426d065468f5a462d10cb832e68287cf46a373e1d6230bc6f1955a24693e27db06d3e96b89fb4f965cbf57ed72c99e9815cb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part183 : Excludes 0x200004080000000000000000000000 0x4c3320c19190064204081000000000 :=
  finishCode 125 0xe230cd6309109a3b1e8f63387d5904a257e03151b00dd11b3342f167173de0f1d32369b66ade331f26b92dd9aef344642fc2f981b356f19938c3df5ecf50be5ae533b4d9b2e5f7445a1c07a531ed560a6670784c2da6c7ff66ad7769f521da6bbada1f6672df360e0ce6370d7728dbebcc1b78d38c24b48a4cea37598c67748b69a812a1e2c73dac7380e8b2523cde329ea36a6b9816f982432572ed114ab3f5b35891a5453443254d65100b359bc45bf0a697b6dfa5bed3d8264abb41d115cb5339c3c301207d742f80b56945ce60630f7915a55c388f70a458ee1bc96b50385cde4432572ed3e5a55279bc50bf20d080687ceeaf226769d684aa1eec791a93e5aed3e6ab5cbb3d80b432d82660642fc859380b973eba93a9acb08de5a5097791b792c5cb6f110ba615696d3de45025dd6791a58de36673c8c34c48bc8d64e04014cf426173a4751b6f1b4245ce91db7e2ff42f7d7993b07e9a4b7cbff599077fa5ac32db2d4cddfe06197d8a50cbc8358d48ab97303166812d966034c7cb3bbfcc9e31e180a24b1f938ac124bebca6d4cede366b448bd268b7325e839b58cb7cc7c0172ed1133b06f5b98b9d78e5ad72ed3694d8cef43e5bc99e5366f17d794d9bc6cf5f5ecf621f4095fb89f9b05bc693e8a589f7d7 (by decide +kernel)

private theorem part181 : Excludes 0x200004080000000000000000000000 0x4c3320c19190024204081000000000 :=
  splitAt 1 66 0x4c3320c19190024204081000000000 part183 part182 (by decide +kernel)

private theorem part179 : Excludes 0x200004080000000000000000000000 0x4c3320c11190024204081000000000 :=
  splitAt 1 87 0x4c3320c11190024204081000000000 part181 part180 (by decide +kernel)

private theorem part177 : Excludes 0x200004080000000000000000000000 0x4c3320c11090024204081000000000 :=
  splitAt 1 80 0x4c3320c11090024204081000000000 part179 part178 (by decide +kernel)

private theorem part175 : Excludes 0x200004080000000000000000000000 0x4c2320c11090024204081000000000 :=
  splitAt 1 108 0x4c2320c11090024204081000000000 part177 part176 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part186 : Excludes 0x300044000000000000000000000000 0x4faebae99998222200000000000000 :=
  finishCode 15 0x472183326b2faf30c9a4ca8cb97a12b4a4def6b54920cce88d85a9b36a6f6ac3348791b0b45cde46c2d804605ce527d0fa64ed0f173619 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part187 : Excludes 0x300004000000000000000000000000 0x4fa8e0a80198000200000000000000 :=
  finishCode 177 0x1791474632656995c8e590d24d46a8a3b050b0c8ccda9cfaec32c333ebc3cd16b6a6c326c390d46e2196d0ba69b4d9675115350c9bc58254697d5339939444cd6763cbd83211f2fa9daf7b450ca7ca8d12312a3196d9fcc9847da162bba1f31666b7877b93e628e2d5e7ebc493615c04b900e55df5ed4db45867091675a992898e937c01d96a7612911cbea17e85d6561936a61935a9bc260e115b476b16dfb537d78e52ed29ea3661ada25eb4c0a68e81b3e0c951b7b16af9bbde033385f445cc5983da9864c3ecc8cb3d122106193247d79865b8651b0c9a669371543610a3ad4d864d45f3c66499e7d78e30cd48e9db4ba4ce332693540a3b4461e62d6d4d86466499e533b537d76f18d274978923c2c192da2dc2c32dc3268d239338cc933c332da330cb70ec35190a630c864cc0ca22a3a6c2dbf3d8c40d86b1788c688c2be2e6a48a14f9a27ed4e57ed1657743ecb744679fad1f4461f65d6d353e6b2d131d11b47b44699a22c332fb276bdec5ada9c2e74cb21a89b0ca8cf9e33384b43ebe7da9d21a0333538a01c61bc6b53773a7116ba718497444665dcdb3e7c3199bc493615cc630cea2986931379b0b78d0fa4df29f377a17933851c3ec146192faf90d4522d0f7a1f16a4dea1e1930078460cced366af96797d94450da227bf2ea2ab19ac5ac9772a32fb16699768899ac59cc9c45c022914716a277596a17c4262eb4dd0fb2d313d0fa2118689ad1ccd6cfe64e68d335a3bcfe8799ae88c25eb96d12d3343ee87ea298837299a9a9b0e12966c2db4f98379f50f26fa5d8c8d69d43e2cc28e199c840348a4ea1f48b357b78bc896ed95a6bd238ccd22c40348f3226172eb5c97d8326604d865f69817d5a64cd87715c8a0cc9a88b5cf3e4cf2f7688be209a88c064cb3d69a59f687b4ccbac59d50cd69838778b3b3d8556d3f43f06e5f7444ccecd6951d0f9e7ccd744659c3265ee3137d7199 (by decide +kernel)

private theorem part185 : Excludes 0x300004000000000000000000000000 0x4fa8a0a80198000200000000000000 :=
  splitAt 1 102 0x4fa8a0a80198000200000000000000 part187 part186 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part190 : Excludes 0x208004000000200000000000000000 0x577361ac3891440240010018241000 :=
  finishCode 89 0x321acd4732f19cb0149b0bd2dea1ea6770a03e7cc0cc3384b3d5d99cc0aefd5c5ed94cd86690a4f5a38b9a9ada2d70683c2c8d56bc72fdb7aaefcc2f04b25117ee6e5b459e1d41622d77e5ed563dac9fb4975a7c12d1ea634fd5df6e5b47a98ecd6c02cf5a9d9abd8af6aefd5882581a6e527617a4401b56b53b457bd7cf9a59260659f08f6d57ab505403ad1deadb965df7abb47b536d5a92e173b4760dc2492091097d8635bd4636511a4b898ed1db6d47697d18d9818f15ea54d651606e5a1ec28d85e0148981a2d577df3e6065df8b54fda1e70b5b95866b336e5d4500a04c4603b5b9985b4d619b45b47c2da9cc815b5623e97d0a5ae5e288c3230b0c6d21e8eb4f88b8914bda624816d1f08e7c74fdb4f18d88511a6659f08fb539939798bbcb6f095dfe23ed36d164f9b4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part191 : Excludes 0x208004000000000000000000000000 0x573261882890600200000000000000 :=
  finishCode 145 0x280e85e3c2656b0fafac924a2d4f20dab2efcc9b06cc9cb8e45611f327344e85d9fbeacbf7a1767ec1b29b685a12bb08ae5e397d535b42e63d78eb86cd0b896d31742e25bce685dc3592fac2f450a88c33da1f16ad33533827cf634cebf75c664e288faf84b24d185e0991751857a9896d85c63424e2630938226d3e619d659182653318dbc61143d2aea6dc2db4f993acd65ff185af1ccb230cda320146a6b0a5940d9ad2fa31aa670c6a87c95650358b448143c28f0662cdc2db2d60d617093849e5444be5ff50f18d6094eb94d6591231ffd9ad9eb06cd969af28a26435958ce306b0be17da1767ea672a2a4f60cc3be85d9a847de25464f7287535993ad361de4ebb4d425b3f90bed3664de10ef5a690fa6be85d67f57199cc7d79a612390c61917d4fd9a66094973e6c59c3bcb4afab6673e3b4c8c2b0c851d2cf0d2c321ff5a6c59caeb4ca628c6b0ccd264ea73b317cf0893357cd931496c635b96619943b2f19c4254cd9b565f65e6791699617863d4d47af8e9fb663617cbec430966db33b7a3b096d360969b444ed7c3a8f627e64ddee7c3b5960c2512e95c97db095b55f5c63750dab299b72d786d59f5ca4d4cddfea5d7997d75058b39ed53f6d3df5ca1e90eb3f89f7cf617533c63c26067ab42f505b538012dd69a1029daa0a85fa130aeb72b6acfafa87b1b095b54a05e1eb353356e5 (by decide +kernel)

private theorem part189 : Excludes 0x208004000000000000000000000000 0x573261882890400200000000000000 :=
  splitAt 1 69 0x573261882890400200000000000000 part191 part190 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part193 : Excludes 0x200404000000000000000000000000 0x56a0e09c0292020200000000000000 :=
  finishCode 179 0x1408a3a1795499596532b8fc0918d445845a6c86a337abeb8babc3c10ac2e6a318a43b17ee08d96797d944a8b7023742eb4d6f52514e5d0b9bd653f43def6646d0b6e54e55fb821659d3b65f5f8ec800aee17da1666b6a71429db2f1da1729ef0f27eda9b7add2c1206199396d4d7ed85f48faf37a987cddf2fabffa176a7089939bd41c421ea3d9519bd5865f5eb160664a8c0af84b4ab85a28ada2faebf774dc5a9b0b98ed85ada29fb0cb616adea72be7d2fb85a1369fada36a710b535df403a9b664dbbe704b3c83685ef9e85f270cc7c22b8bab30bb68cc7b0cca263e8b516f333b0b742d7ee63ed4e5c71555fbd6642b1545fb6096e58665bd69a5e10be159a737cd619979a73b42dbd4bb7444c370be5bd2e542f6d57bbd11aa4d2003032e70478aea17b44d30b11767f2cf32666ba1f617cc9e88ae58caa17da6cc335c267861586720dcb447cb3b7ad2ad68266b327a4ae6135974c00cab7ac4cefaf31f35abdd845b0bec3986a335ab72b0cbe7cfaefaf4c9a7884da01b118661e6d114d16e5d118615f36a158b4db42d85d865f5c26d86696b8f06d35f3d85d865f5f21847aba5f50bdb95bd60085f199c47b0bd2c714b5a6b448aecc9a17d7218fcbc1a4b0bcda2c32f9b27e98ed2da9cb322c3311b003a5cc51da9851a17b78b0cbb2316a7276846cb3cbea17c9fb2a3531be7adeda999dec39984619622fdcdcb186f5787b4265365474465f653e61778788f963985e23ec9506230bcdbf6a6de2daadcb10195a1e585e59e28deadbd40963c5c29a472e77abac36fc32abbe32b377d4db16af9ebbec136461786652eec2d98f351617d6632a98476372b7a8cae8259e5f744642f8a17878b4653e5cb88f787335ac612cde32d767e146f9ec2f48e04b7d4bb1666a3684b44cb1bc3be7cb1da225ab31f28ac5e182585e9ce98fa59a545ad5bd663ea455e3a73b339bd6a185343dbd5b0bbebaf1b6ab7abebd10773a64e195eec615bd62d6185 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part195 : Excludes 0x200005000000000000000000000000 0x54b43ae800990002a8000000000000 :=
  finishCode 91 0x1ccae6b24940e030cf12c19cb538a4c9ed70e53551b5fb155a654a4c5f6b535fb36124b985c5f4d2691c4cc299a9aaf6c6c2bc6d335a5bdd93d98cd69e496bf64eab870c0f1339c0d0580a4e9ced075337c35fb27b2119a644d577c665b3e3615df8664d24d66894c5fbe052170e50f5355c3970e0a1409a73883d46d70e51b403931c9053262cd65ed3d7b57ecd8461627b619e06734154dc580a4e505032cf37ada9c3dca6cd7731efaa66b27ea17b6ad4a32ce85e4f6a4f2fd949cc9d6572f2a3650facb029ad29f166bdabf6a235a9da3ccab6ac59d95aefdc1a1487cda22e2cde0deb5a9e85d32b65b4ab69f372d95be69e4c2936a684b32b6092412b14861796facf5dce285eee65687b6bb9025b562864fdc1facf583457ea697a9425aa5733030bac617a655b3c31e6566bb9676f516f90bccd758a674cab0b863d96d48768a4c685f985336cf831c5be6e5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part197 : Excludes 0x200004004000000000000000000000 0x54e4a19a0894000290200200200000 :=
  finishCode 129 0x399acc65725885f1499ac9b0e9321c0a459f3466541432ca4ef0fae332eff4caa7eb0ca7ecefe837611a7c8658ccde10be6192938c513212d7302f9f4c899da7eda2390a44125ee90eb337cd7cfc2f9ea653f42e976d0b33bd0f8eec3f70a665448ddfed369b53f67cde06832085e19732b166cc199dcd13f53e6b3f1519678526cff21845e143bccca0b32b69b52ecbaaa674408da5453c664cfa698f4afa69b4dc24420929b5a6a17bddb7ad21b6ed3642f7a942fa5361ed0be7cf6d5ba4021ee88f879b4465ee5e6995e25e29a67cf287293a4065be7d322d174caa7ec51c04eafaf2d70adcc0d9ebe7ae5d2d7a23350a7eaf199db0cd7281a46198a331026981d117d7aa6424081285f459da6cb9630a30b4c7965d69b31eb0409acce63c6166b1a739e66605ac6d353aca050bea94818590be2cc9d649747d79bd46169ce6b16d5a5f8ee6ccf094617187df3ccda6cc7b7ad9092140a17d11f0cf217d9fd11f2f384d6633210f33e6cc9b72b65a998ca863c506563085f68b27ce878aecb3c3cd67ba1f83f098cc7e88d4208f5736aa8eb7ab6dcfaf57268f01858a365d31f4e6492faedeb688cc7d21b72cf9b16b2f2f06918ced72de665adbd61e68a198f8cee90f4450bd0be5110c7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part199 : Excludes 0x200084000200000000000000000000 0x5df439ba50d1094a04250010800040 :=
  finishCode 83 0x178ae50249a4619943ebe821de8914114250a5a1dc92e68f51bb53a5750450978910c24c2ca66faaf626773314769c698f3194099095e0e09838ceecf61734110a5b4f9044296c1c44259f5d4cd4d5e0888e5a9a08c14b322823052bccbebe83d30614b67e806823599852b7293e699c1994fd09b3f3e5b537cf403b4128a4212a205ce87730f94f965a66b1ef6535409ad35f3622e9836a120d68ad1f441494e734ccc7ca7e859eecacbcfbe1af6cf0a677486faaa6b29e96b683c45d21da7a8eda7c24ebdaa372cb03a19969fc45ed7b1a9ce2ce94460f7608197516b95fa2454165d5e7cf768918b3a4691a0f2f4abbebcbdb4cc3bc59bc1e5e2469917c3b53d07b08f06653e9c633b2f195fb539a66625e7da08074bdcbaca7d4c767f6a6f9f48c19a53de7d00e5eccaeb2d7d5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part200 : Excludes 0x200004000200000000000000000000 0x5ce4a98850d0010200250000800040 :=
  finishCode 137 0x35998ae533486c37866641f5e38bce2368dd0a4c9766195ed619a656cc6b4d6ef5df6ef97b432c32ed0f841e566d37095b7d865bc432f81c4c2065bcfd32b31f846dde526dc35a9ca68b9c29f6a6ddf847536bcfa0db0cb77bc6c9fafab6a6fae197788c3e149e2935edb536df4d76ef5df9b85864a4d69688fb4161986529378502c1904d7a9ce5eccedd0fab09d9ee831989d6a76a71e5ccacbdcbdd607632342e6a13ddc197d579f9958ef57b541742c3ee5ed9952cf94fd0b5dfb42cf4500f8160d2682f0196837367949af100eb537d79e1618f0be98de7ef050f3c2bebb0ca87c59cdbf143b0ccdc2526197246df7d79b870bd865f5e409c2fe0683081977813fa62d0be23ca4e9164c819dd30732385f26bb4cda0da699dc277a1769e6773d8b57d54bc610f050f2bb4c4e17c48ba160e67d34d369af0f1e5ccaa87d39d31769b59290ec86217a2308e01b0f788f25d94f97ba6411ea657679f5d17bd77b9e16b45d07a5525d78590249045ce8132b685e17b57cafca78b992ed29ed775a6a17d22309af4c4bc2d9ecca92eb57cbac276f9f0f765b85ed5f027d96995cc7cafc3dda2ccae11f5f80c331498cccc33217d8321549213ad71f5eb53619b53ad35abe9ced3de7e1ef42eb4d6e1409e23b2512442f985986628dea5b3e985b3da96de7f312f3378da6cc7d486676f9f4c7da6b5fb78d726167d742f6196f17d59046d350467996e142f (by decide +kernel)

private theorem part198 : Excludes 0x200004000000000000000000000000 0x54a421884090000200000000000000 :=
  splitAt 2605 103 0x5ce4298850d0010200250000800040 part200 part199 (by decide +kernel)

private theorem part196 : Excludes 0x200004000000000000000000000000 0x54a421880090000200000000000000 :=
  splitAt 1 86 0x54a421880090000200000000000000 part198 part197 (by decide +kernel)

private theorem part194 : Excludes 0x200004000000000000000000000000 0x54a420880090000200000000000000 :=
  splitAt 1 96 0x54a420880090000200000000000000 part196 part195 (by decide +kernel)

private theorem part192 : Excludes 0x200004000000000000000000000000 0x54a020880090000200000000000000 :=
  splitAt 1 106 0x54a020880090000200000000000000 part194 part193 (by decide +kernel)

private theorem part188 : Excludes 0x200004000000000000000000000000 0x542020880090000200000000000000 :=
  splitAt 1 111 0x542020880090000200000000000000 part192 part189 (by decide +kernel)

private theorem part184 : Excludes 0x200004000000000000000000000000 0x442020880090000200000000000000 :=
  splitAt 1 116 0x442020880090000200000000000000 part188 part185 (by decide +kernel)

private theorem part174 : Excludes 0x200004000000000000000000000000 0x442020800090000200000000000000 :=
  splitAt 1 91 0x442020800090000200000000000000 part184 part175 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part204 : Excludes 0x300000408000000000000000000000 0x4f9b6e1e1501980660204081000000 :=
  finishCode 65 0x228bcc84cad31f1347ab9416d4d80d845c06675a9cb2cc8ea342e8910c16f795788ada270b625d7d66915b282b6cc193322e094fa2b6646691336a73e1cb3c7aa283122c27617b6ca0cb73a1be4369a8a6064cd2304cabb7309da2c66b16737bcbabcfd16732354824b262e5a788b8b39a4a7da1f85e5eebd29af4b2d9ed0c767ec2367b68796f83ae88999ca1e7e8b39756b76e7aa309c2bb2af0fb1672af687cc1cd343e5f72659c363d9fc86edb3431c59e43699ca6064bb10de6059656f715f8965ed6991a64b2d2ea6673224cad6f4a7cb2b42645b9d306a61791b53ad36d116c76e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part206 : Excludes 0x300000c00000000000000000000000 0x4f9e1f3e8007f80001e00000000000 :=
  finishCode 35 0xf09c221f5e816a7309957cf88ed7d42766e797d499e604ce0ff308d9ed676dcf4de66b48763a1ea623bb539956f7825a9caac2dac260faf53008cc9b74b09b7260f9e1933d4b08ccad6a6f532a332b3deb738b6d67b32b6776a7b8cc68298192b4f684d9d8b6bc3be7bc2d4e666b32b446e78cd500c99deaeb3707f23b9f3d84ccd500ea5b94f98b335995437 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part207 : Excludes 0x300000400000000000000000000000 0x4f8a0e8a8001980000200000000000 :=
  finishCode 153 0x3393ca64b2a86926a3b4611a595f5dbdc666503122bf37bafad166daf37bcabc51e1747d7ca2fbd32233286f309cc8afad6a69af67ec266d35002b826e6546657dd84e5ae3699957b58664da5e114c0521f5ee84cf0cccbdb4200f89559e1743cc0c1eed3cc8e18d7367d5b534d73338ad9f56d4e995b42c666d4e91e957087995199d0522692f6a4d11a9bdadf43de7ed4df0c5aea3fb53d11a6fb539adc666d4708e2f3a737b5b536b7a976d4c59c6677194d020032618ed118b399519979f9959ade95e64c6655154940ccc59cafd1234def0b4c0c48ca230d6f4df4c9d24d47e7b27b7687adf933933cd42f495d899de7e295f5744679f94f791b44653c66729749c0ccbc210e0a64c1be6cfae846f9fa23259da98b5ccacdef2af48f6a73ebcc1bb298f9b374a1bb63a82e826566b70c978d267a91e53e6b74237cda975ef49969934d0064cf32f7afaec26e06e787da9cc1ff05dba67bd85adf5ccae7d70c916b963f17a695d6f7989b539addbde6466c7605a6682a1189a4c1ba6605613d119f0c5f5ae57de58ecb539f5ed45b25ba67108991859e6467d779197d4485ea6656d4ed4e7d79a4f25967cd8b379f17d7739416625b9deee6466e97d7b53a44b2e0faf4cab73c3ebc8d6a62fb316db2f0b51a595e66645f5df5694f7ab791995d117b5941690ec6643ecf76d92dd36a33e6c59cf9e2fb282d2340a8965c1e11497b791ad4e22e55e655f5dadeb53975877995849e53ecde1f5adde7e2cde3695d79f94f97b9897d5900c1557a65eed4e791b377d594fb3da976d4c5ae2962ced4e7b5 (by decide +kernel)

private theorem part205 : Excludes 0x300000400000000000000000000000 0x4f8a0e0a8001980000200000000000 :=
  splitAt 1 95 0x4f8a0e0a8001980000200000000000 part207 part206 (by decide +kernel)

private theorem part203 : Excludes 0x300000400000000000000000000000 0x4f8a0e0a0001980000200000000000 :=
  splitAt 1 87 0x4f8a0e0a0001980000200000000000 part205 part204 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part210 : Excludes 0x208000400040000000000000000000 0x547a4f2842a890c000209060002000 :=
  finishCode 67 0x190be652c99cd05302fe8031b13b839d85a50631abf7616ccac8250dcb375b04b0bba2a8bf714b59ec59cb5cdcad96dcb375c59d21cbff69a31b2882617cdd7a134baf9ec12c2f0ce2306bdad32b313279d9aa79d2e7ccb8410a24ceeb456a9b3f88b891c1bb425aa5f0ea73b0bdaaed145f5f3ea496179950bfb867250f452f863e3cdeea432eb60ccaebe3b6bcef71674df2eaf46eb9485f1ed368690238b39956cb6cba655f1cca679f7d5c2d179d073218e452d4a5a6cdeb3274e74beb74da2a8bbc2cd5732b19db75a8bc50cd6b53995b53ad3e6e5b85f14be296b4fa6118d995ad3cca618d995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part212 : Excludes 0x208000408000000000000000000000 0x5c7a6f0c11e190c241204081000000 :=
  finishCode 47 0x6734170aa562f8a5ed8b52a9dfa96c5594185fb7ad326a5b90a63b42e1bf4250dd4542fe54686f51528fe228bda6a1bcd764ef12f5378b5a1bc17f1438014c9b38332a347e66b32a10f10712f30865a6d16610783f00ada7ca8da6bdd8b5b6bcdef4dfa1666b32b4c644a108e7cf6d76e74d7967ed361bd35686f5ed4236e5acf6d3d7b5d1c48a3b021e9956097c78838abb8441a79cdcb8331fbc512bdba09419dc55c9e769b448e12c55d9acdcf106c132833b2896d985ae215f3e8f6d09885891 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part214 : Excludes 0x208000400000200000000000000000 0x547e472c90e1944040300008341000 :=
  finishCode 89 0x3217cd067329700bfe2411b6ca6d77ec257977cf5056f542d89c5ea651552f5e38a6e8124b85a9da12db6a5aa73607b1ad4d0b4266d4ec1b0915df8a5a1bd7b54bee0bbe9af365e12c9af6a65d6c2ed4b04b8511d0dcb43184eaefb04d3141661709d6e59baf98bdb123279bcf944a6dd6a64e3837437b04af6f12e19494144a6dd69e4e22fb04ebead28c258f8df0d83426679f7c3b4d85ac2768958745a3d0debbec12a0b3e78beb72da9f10635e0a0b4e7599b65d99d6670adb7bc317b6cd61bea433d16f78b3a6128ac29cc2d699b046bcbbddb42c09078364d68a656d76a83f99e5db961bcfdd00e1be3f7981981945690e64de5c276cce1436eb5d1ad15b95e174128993851d0b5e5deed4e61bec2f79799395db0bd74567ee1586e9900e2cc2754be49a0c2593f508e98e2964234f18b38a3d08e6e742d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part215 : Excludes 0x208000400000000000000000000000 0x547a470880e0b04000200000000000 :=
  finishCode 127 0x3c388faee8a05926564930b84b5d69e136506deadb72ca6456c2ea5375a7c56c17e9afcc169ad3ca24a6e2b64d717d0bf6cb94e66ab7d50bfba582c924aa216b6dd14a2ea2f2deb456e31b2e2ae1858ad8a59e7e6d70bf609b265053e29b17518da61853da95bac2fe7ab521ca282da0f2aa2cad77846dea17e536d9726bca1badbd5f3e4f1077b5393c496c11d35e4954b25d2f86774528ba8bcd622b65b1b5352d53933b9f3d35e64d456b1408b382fd35d4e565e8b34d7b535217a982fd486a043022dd168f37bd95d69b4debff2fb05fce0943232829e27f2cbb6b85fc55ca2f15b445b0b85f98dc52d9ecb6231b15b12f15759ee84e1284ee85af1d12c954a65f3282f2b2f59ac4ce12afd92d9418c6d022ae09d25b9b262ae095816d09da5d54e4cb67bb951896d0df41ccb86726560bf25b52fc2fa655f56214a2496ec252210bf335a6542fc96f0be5fb25ba6493401134b385fa1b92dd69b69b05fcb3d32a17e4b7ccaa537cdce4b6a5edef4ca85fccac17e4b7607659188e8885b4da9b5f1e2cd426cd6990c43730996c5b26d2e0bf5175b15b1a9b5d112f36bcca923cd7286f32b59aa90b6bd32b66b700bf6e9a5d54e65d6 (by decide +kernel)

private theorem part213 : Excludes 0x208000400000000000000000000000 0x547a470880e0904000200000000000 :=
  splitAt 1 69 0x547a470880e0904000200000000000 part215 part214 (by decide +kernel)

private theorem part211 : Excludes 0x208000400000000000000000000000 0x547a470800e0904000200000000000 :=
  splitAt 1 87 0x547a470800e0904000200000000000 part213 part212 (by decide +kernel)

private theorem part209 : Excludes 0x208000400000000000000000000000 0x547a470800a0904000200000000000 :=
  splitAt 1 78 0x547a470800a0904000200000000000 part211 part210 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part217 : Excludes 0x200001400000000000000000000000 0x54980eb8000990000aa00000000000 :=
  finishCode 181 0xe6673715ca64f2085066a26b2bb72efafbd6a6c2394b269340333c02838a3c94e5174377bdb4086f4c8a82cdd3697c0c8693416829b9a21bd6a6c2367b291c52cd56f769a2e03b99f3e2467cf8a6d80eb3d995437523a656812887798169b548dba78169748352ae12d25b08b55cd9647a86f117308b64e53515429b3cd970c665e02932f8d1fcdcb984d1b0b43bed4e1f577c6666557a6991b4b95123db539e5814be216b4ba3d5fb52d7d56e204c24314b32b452d482f1b29ebd3696a47c4e068369640cb8b3948e654a0e246611c2db4b523995b23509f62ce6054f96058576993409995a2591e0d8b3c4096cbb4ba9161f5ade5ae2ce2662ce8b397ed85e40978794161bc0f57b6656cd6b0db3285a91a1bda051594bc30eb0f9f43ebcbaefd9aafda78d69f2d681315b4cae4335069364944cad1668064b2dd344d24c1d10a2f332231263b1e2ccab64c807322d772ae7d7373aef84ed32a2f3687e282c83286ebef14742efd6a67ea2f332b44611b319bd406e4ed88b8fd5f5577e1215db43798701f8bbf282b02b09c5288c22fab4c8cc0d98b7acb3a82d32abbf37ada9b55c9185e6e5983985e8f6b539675f7d0592188073eac3eaf4ca7cc8d5118a8b4ba22cfd576f42677bb4b7d51997d5976e7c39957b55df96966cb967b2d8856b55ed617da6627960e22f6afdda9d132f6332b0fb36bbcbc59c55e5177eb535db25f2896e09ad4e3167117364d38e51b969958912898a59b962cca2676681416d4e5f727db539bde97e4b9b4f23d5f717d27daa5327832ae81814f9a2b70a5f3ccc6cd500eb5350543750590ded4de010f52cc41cca863b6dda9e62d3e6e50c7b3d9a466069b4cd699a08221bbd5c24abc6806bcea0af9f66b5a9adea82cf9ef06bbad4ed3e16b6e5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part219 : Excludes 0x200400400000000000000000000000 0x56a897980600b00200200000000000 :=
  finishCode 155 0x1a4ae3c271b07d7b2341218c6cba64f2a92419999585e5bd7426991613c199958adb0c4a0d08e20cd45bd6199b4f8665bd665580e995c637add22b6957d09523c1919996b8c6ecff0670bd846409995ad4e54580dbd73174843f25160a021bd66ea46c1332ad430a7e17a1bafac2be4ce86f2caccaaf4933933d32b616d2bf8632d783385f6a732b607bd92cc007064d458450ded4cced4e6c2f613b252acf76506bea33328b37a655ef54e7816a73cbe1797ecb5b09ccad40cc3a34132b94e64a29be60dc2d5175236f589de9930195613b0bdbd579c436c1b219c2f3ffd115dfb0bdad5bd548e6cbb2954d00cab7acbce506d97521d4e66a2506d97301a91d93294c967976d84ed4f4446549de08a2f59eda7b7ada9cdb769edb7296afbd47aa2f6a7ccca1a8adfda23696507a130bce18b65da9c2f374ca66065681cc9959421bd85f66ea46a5f85b2fbc3eafbc7f347af7af9f85e86f0cc2f7cf94874466096133e5980f06548584e590ca81a4f02576689437613c2d8785b95a250de576906a47a6dd115e768997590dd84f426995b4d403d11613437d05426185b52ad9b8a2ccab01b09c31ea6515d11331d11b05f99327344a97c48af3c663167599a76e0b9a8d9261b8d053176660328397d9bd54be492a319accac52b62b7ae17d2d666b4cab08a8aca5b2a3a0995863b0be24548d02687d8a5e659371949a4909de596b4dd11983995515981a5eeb4d8d454574454beb924d11978e20d8366550b45d6b1a231a4cc984e9a4d15729f69b32ba23302e842da65659633b51594be6562b698160d995d11437 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part222 : Excludes 0x200028400000000000000000000000 0x5dbdd70aa640955894200000000000 :=
  finishCode 39 0x333490c7d770311746d1150997b991be459cd97a232cabc72e7688da8cb28a3ca1f569576cb523c2d973989d115e38a5af8bef431b62b65e88c52cc053e6ebb519a5f4248470a7445746c1589e688c85b30629ec1b505c19dcc8da1369a5d6be367f4c8af8d69b2da62b32366303b99dcbda16e88cc1da4a65c17d788be335de84d37a91cc8c52c59b6de0dc6772899197c6596c1bc1b948e6462cdbaddee4d795d17596514f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part224 : Excludes 0x200020400800000000000000000000 0x5ebf1f18e501960813600440801000 :=
  finishCode 57 0x3719c943f148d4bea0faf2bad97520b7acabd49737abebda9c91e8dc784f260a5abf71e6bebb75bebd6a76a73ebb55b7a933c412dcaa5b85b355a96ccab72d0fb32aa5b6a714cc5a2656c258b3a5f5e92676a1a645f5d7a694fc2f33b7d5021a1bd77da86f92c9c3e1b8dcb375c52c59b31ad6a719955df7d7995a2b622c99d98f0703ebcaecd97322bbf43ecf1f560f19955df2d5a8f69c6575e3687d7b194fa4b9f1e656d4e2cf4469957d578d94f97b995ad4de1646bba98df5e5ed7467d7a24f099f08ea6dd115dfa5fb0969b4f8ddee989a6d5e9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part225 : Excludes 0x200020400000000000000000000000 0x5cbd0f08ac00940810200000000000 :=
  finishCode 157 0xce6e2f93c781a89b4be3d30686efaf1573e3a1bc32592870374b7bbe2e1a4523b3ba57580ddeec175f1973315c1978d97c653ed457d4faeb3b78d95d9838b3acee5cd7c7811877b9f5d84584d99483612e87d25a1bb64bebbe1aee78d43794f59fc1b6034379e3670d57365beba1be17cdcad9732b747e6910df8114605b4bad45e37445f5f096c25ad2f06548de13075a6cc8be100eb4bc19523d11b065e352c6d44c0ed117d7660a0d683696faef1b60cf02293487d9f5d84584db6ec315f57d7963e3426d116056e58a58b37e71298e1e3007989605437313a625815aee01fd11b5387d437a7169b35bb6ba1bbc6d85ed2aa47589e432c0a42a5afc081a2b625d0de2b66eb78f897b53b53b89408a29cce2656d096eb7d76ebb446654caed11b53b539f5dbad8467d7b53944b218beb291b6dcaeb74b7baa17d6a71d0b6db6d7989605a5cdb6d0de6f59f5d84e29833456ccab7bbebc3258d174abe88b5cb74a1bcbef1fda1be88bf2496843734997de88faf07aa72d36b6dbbdc9cb4c7a49e302e88c9ae13af46bfefaafaf355b65b74d2e6693a4904c228f82677d76f7a1ded4d8465967c76bbb536d78246d4daae1f6b377d56e9b537d76eb980df5de3697b6e96f7663c2712c7d7943a19168b4d977ed4db5dbde08ba35a8aefcb2c9e76a72eb354da9cc4d2cb85ef8f6a6f8f01898caf6da9b65d3236a768945a8cf8edb7a232eadd2813617c59da9e88b09cc5d1676a6d97a235098520d2e7a232ead92c0ac26ac5f79739f1db265cec2f9a9585f445ba6d1c4605613d0fa1ded37096d4ecdf43e6d7409b53c25a260dcc12f62bb6676f8edb77c6bbb3fad1df56d4e (by decide +kernel)

private theorem part223 : Excludes 0x200020400000000000000000000000 0x5cbd0f08a400940810200000000000 :=
  splitAt 1 83 0x5cbd0f08a400940810200000000000 part225 part224 (by decide +kernel)

private theorem part221 : Excludes 0x200020400000000000000000000000 0x5cbd0708a400940810200000000000 :=
  splitAt 1 99 0x5cbd0708a400940810200000000000 part223 part222 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part228 : Excludes 0x200200404000000000000000000000 0x56bce72e0840980990212020200000 :=
  finishCode 63 0x732f9b8c6573806d3084f928f07fa9c6d370bdbdd08e6d9a5da41b445ba50df41c04378a6d0de5e0aecf3385edeeb3e9f332b853345c4cda6a84c85a536fc9263342eb51a735a5b4124f31d423349437822168bad2cba22a0ba232de8bacb2cc8cf2b9403499558c8e6565568aba5dc29b0c7445ae56f4cee656086774cad9fd2ed39d01bded115e3b4b33bb4b978677282ccacb178eb5131b6e96f731b9f8c451542d797a9b5e66d09b3b965a428abcbd303a12d8f2cb12f539c56ccabf25885a86f144ad9eac90c5d5e1e311d114cdb0a66074457970a03a30a6b4fd1178733b995a63a2170a4faccef4445d6b3d7a9505c17a2174466546062cbb358add11 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part229 : Excludes 0x200000404000000000000000000000 0x548ee70e0840900090202020200000 :=
  finishCode 171 0x15c7845380fafa0986d17d760f57455b75865bddc5372ab309df371ccda1b4dc0a6df3e5158a55d5906650540999596b8feda8742cffc954614645416c318b3d091751890cb830e64e79b01893696cb9bd6976255797ad3e2cdb5c99f6086f060bcbcf766d3ccc65f2a86d30fb3e7b6b8c8b7b8cce42e1b06f7accdb1d08df3c30660e6c76f77bb0cba9cddcd78ecd6d11e06d360bef364861865e11d30385226af77503f1a55ed45b25b6e605816556437830789300cbb8381b6da5e1536053119a5ed1131115341960569580cf445a5d7dcc45066e19070204cf9e677a232f1b4bd166806a2b4dab8f2f1d4321340c76db6058cc7095aed00ccee139c1f4196bbda1f0d8526228474c686e904c186270a6cf74466918c259a5707d8146261f384e5a5506707d0dec2f993189e66e2f9b0369d036bcc270fb84a186197547bba1f4666d3e0116d7267a417978fc709580c6476001b6889fd80bcc9e12861afb865bddd303301995e7984e606437830f81b8da68228186197705f570204ceeaa2af9e7af3dda8aaf1da2345279c45e3b26566913370505b3fa1a5e66cfe6896d98979a916737ac34bd5a11dc32002b37ad9fc34bd5c52d6833b9a78a04d69b67f36ca04c56dc1510faf335a6bddb6bc59bddcdcb67f373b21e1a1f5a79f0a11da6a04e88da1e84769b4e73c3b7aa11a82d12497098461bd6692a320cb02cb3846cb3d14ba1f364d14ba1f2a2e88a351d8832d0b4c8da5e88a04a7cb6cda5cd2b853a2383328c319305025b66655b9d02615dc17409a595a55b9f44743e603695965605464c0b5cd14b2cf167365e14d22e1a08b3d0f9026595026a45b07d0665970a6d095056bb5058404cd66558450de0c1 (by decide +kernel)

private theorem part227 : Excludes 0x200000404000000000000000000000 0x548ce70e0840900090202020200000 :=
  splitAt 1 105 0x548ce70e0840900090202020200000 part229 part228 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part231 : Excludes 0x200200400200000000000000000000 0x579c6f2c5840980340240140080040 :=
  finishCode 61 0xe6672f9b8964f3406d3b44378a6ee12827da3fad4db9cfaeb53820e59664578d499576041d82fa176a68469f28335a9a11ca30bed0b6e7b4db0bf05eb4d6e7c84a0a6e6266e7b3f908e6569cd08e4378a6df9b46a21bbb130e7d550596683c9af48b31669280726bccad69b29e692fab2cb19dbda9a4cc1ed633ba6da656d4df8dcf211a1bda9d7ca719bde6449f4a26912bb59bccabd4b63c37cf0f6a6fcda6828086e677531d2fda9938c37d66aa0acc423995b0be91de66995c2f7cfa47ad4dea6271b53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part233 : Excludes 0x200000408200000000000000000000 0x5d9e6f2c51489002402441810c1040 :=
  finishCode 85 0xe267369b8a6065a4178f0995c2f9aedb5d3e6d4e62e6d759f843c1b9ed36409a456bbc2facd69ced36d3ed0fb4d7e351026b4d5054235642128dcfa1f278da6a04d85e8135a6c41e17bccd16748be4a22cd7b6c2fb534096f779783de2650261f6d1e6d7b5300fa2b57b6d4ed4e5ed86f8b3b4fa63f1c0bef21bb02a1bd307c5c1846c16a6d5711728299dd36da0f5a99facd729aef8edaf3ead25d323662f6b6a6bd2bc74452e132ad094459d1fd2cb853a16daf6a713ec3493ec8136a7323598e18cafe14b6cda9da7da12fab2eaa0b6a6ecb8282da9d1676a719dd2cac236a6e8944afd4c369ed2edcfa08c3425962dfb354097d54c19026cd45464c1b4f27d79f965b35a91502624679f965603d0459d2ea4fa51369b3d5c59a04e80cee6050c3a44a1f3eb4d40998b6d78699026 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part234 : Excludes 0x200000400200000000000000000000 0x558e2f08d040900000240100080040 :=
  finishCode 139 0xf08a491f5d799cb53e268220e6117bd2714370c729be6350d6508ea45869a655e5df3deee4233599b8513282ad8be7bcba01d12e992c26a0ba0dc713392840935929b307a646985ec64c18b389f4a2539eb358c3826461997b55db1999e35f5742e9576c778d97b1997c260d862dae33316681366a8133559acb6be8298f331b492faed944b08c59d48a9672af84a2cf10b2f74c409a2ccda62ceb4f922f3896a79ce6642a85374c743baef8ccbb059ea4778d7d56a9d079aed0de3490c78ced0df0a6b517bd289505b4dad1500d76d77cda699687e36bbcfd69b12297e96b2aed926930436933b9e7df562ce60e323ce6e06664373695db90dcf9e98b965143877797b83e22468b397b9dee92de7e97e5b513b991199dc672991170cc9b4c59c333c48b38a25aee22e19996565ecbaf41daef41b8ce73030d67e6c9d0ba5f52d975b4f5f70cb437af94ce63e17dca265d6d0b8b3403b356c9a97d7deb355053e5a96697d36e214a258165e9be530665b1ea3dd078636c95f743777ba18e65692d7a57a6437623e27966b14be456f322cea711993694cd967d00e4cdbe1fdc6d2bda613201c2128daef2f538d9fb3297e5bfa71a73b0c61a62ce8a352266514bb683b7bccad38cc5b31e5eb33139a736c9a73b0bea716f797b697f999cbe550da6916199995a9769c5b9e4236d9b0be2cdb5d416a43423 (by decide +kernel)

private theorem part232 : Excludes 0x200000400200000000000000000000 0x558e2f085040900000240100080040 :=
  splitAt 1 87 0x558e2f085040900000240100080040 part234 part233 (by decide +kernel)

private theorem part230 : Excludes 0x200000400000000000000000000000 0x548c27084000900000200000000000 :=
  splitAt 2605 105 0x558c2f085040900000240100080040 part232 part231 (by decide +kernel)

private theorem part226 : Excludes 0x200000400000000000000000000000 0x548c27080000900000200000000000 :=
  splitAt 1 86 0x548c27080000900000200000000000 part230 part227 (by decide +kernel)

private theorem part220 : Excludes 0x200000400000000000000000000000 0x548c07080000900000200000000000 :=
  splitAt 1 101 0x548c07080000900000200000000000 part226 part221 (by decide +kernel)

private theorem part218 : Excludes 0x200000400000000000000000000000 0x548807080000900000200000000000 :=
  splitAt 1 106 0x548807080000900000200000000000 part220 part219 (by decide +kernel)

private theorem part216 : Excludes 0x200000400000000000000000000000 0x548806080000900000200000000000 :=
  splitAt 1 96 0x548806080000900000200000000000 part218 part217 (by decide +kernel)

private theorem part208 : Excludes 0x200000400000000000000000000000 0x540806080000900000200000000000 :=
  splitAt 1 111 0x540806080000900000200000000000 part216 part209 (by decide +kernel)

private theorem part202 : Excludes 0x200000400000000000000000000000 0x440806080000900000200000000000 :=
  splitAt 1 116 0x440806080000900000200000000000 part208 part203 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part237 : Excludes 0x280001000000000000000000000000 0x57f08c620029400008000000000000 :=
  finishCode 165 0xd0582a13cd6226a2be62f9a45fb6eb9b0431da2e6e16e59bae9ce5e97af6d5d2131cdd76834bec55da9d32d08ab6c98f9b6ed4c285847597c96fad4d76663df4c9c54d65365d97c16ebad4e94d0c7785c248bc9959a2db6ed4f48dd736ad2dc9b74bad7f1c6a661eddf4d00ea450c76bf4db8b55a2c5be4db6cb16f9a2ed2e23d6bfb53cc3dbd696bd2d7e18fa1f3c0b52a8de85a68da5af4e4351a494063bc270bc74db225d95d66e4c74c6f6f4b7c388a6ccad20cc1b7e1213c55e798f6b17d326344ba795874225d32ad9ebf76a3438a25b78990d32b4b30e2bc68974bb5a5adea7baf8d3250be359da25938cc0c80632b48b304da8bc9be9d2ccbcf30a32a8975094452d0886786116bfad2de764db0c7a55b3b4d1a23e6549c699945db831c9c638b07a5a1ededdd0fa7534e86d68ec0b16b048b57c18ebd2fcae2a278bb6663302da28c2b75da0eb4ba1732a32ac0b3ca6360c30abeef5f370b77b75cd8a18f32b2cf302aedcc358f80c7b459f4ed1deded2e6d59afdbaed1e0c7179ca530656271b3b977ed45e95f4c31e70fc7c520d2c979d84af6ed9f32b59de86da3a68d98da5cd7f68f59bea2f94ca44714ce656897b534231955296afad2e65585e895c51d60d8ab8655f06995b5397b690e85edacd546e713c155898db3f30e46bfd2341ad5b2ea59403462dfd66ebe352c8b7e83da1f48a63abe22332dfaf8b65b52cee7683b75bdbb52931b6fcfa6c1b4498411eee6b59936e59e131d2d7387818cfd00e6dbb3d7d36c5a5ae21664ccde423b53824b1c662bdac2ef07c18655834cc67d3967 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part239 : Excludes 0x280000080000000000000000000000 0x5751854110000a5000001000000000 :=
  finishCode 61 0xda5d31964a65c115515e21247d38cedbd759947d38cef0bd4d5f0696333b6cbd118cedf264bb4f77c1b53103b0bf0b6d065354d6e1989e0cfc41d6a6faefa6886bf6fa7688b45da9cfaf6832f8be0da9beba26e435833f6833ebafdda9c67724b539105f5e33f6ef6bfc8358cbf6d96fae33ee88e592b0f932830f90b5abdf049c5bbe7c1a699766cd50b7445f05f5e42d6ef16390b650d4ac2eccfafa2316ab8e4e3147688bdb8aecbb2fafa23a233dbe61a033f8333ebaecb65b75aeccdea4e2fa6faed971ffbe4da9bebe9067e23e7d34d75297d70bba64614a7446533b53a23e2d6d2db3eb41d11b53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part241 : Excludes 0x288000000000000000000000000000 0x575b55480000000000000000000000 :=
  finishCode 105 0x35170b465067f1984b205d85fbebc4caa2332b5a999fd92b1b4271804c0cf9ba1a822f7ad37611aef8b4da9a88c50d696a22faf14511171910de2ec2f7c169b3c57cdda401eac49e5df7cdc2d83d536d77dde664eb5399533f8a501f5df06091995b2471e2e69b6eb5117cda2d61eccfe7abb247308a22f1716fbcbbe6b7ad63096d074db3f733f7ab9ef5e1e69b6eb78b271d079de4245f370b4cfdeae293866541f5ccfe99515544325b7426dd84765667f32a22f4afda5b5a8aabcecf9267f32b3c5e34dd6a665332b64247910c586b2b68ba4b8b5b47b53b43e62698e65651388c3c0cfe98e87b8b5091b5352536d2e716b68ef6f26de11d6578361227ff34de0dda9be9d68ef6f6a78cbe65109633b51d0bf9c592655f5e2ae1794254434dba9b5de40f64cd77995d44399513fa2d515e655105f5ece6127817f60ba131bced32afa68af32b3ebda9cf92f3a87332b29acfa68733c945d131699524b60d617a4294d6a684b2b267efaf65270a3b85f007beb967886bb9c4ccb7c4ba5ac01e1eb6a6faf441c56ccaccaccc0b54d79f5df068ad4d795542f6cb995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part243 : Excludes 0x280400000000000000000000000000 0x57f08fdc0200000000000000000000 :=
  finishCode 69 0xd05d33190ca4402c42d4ceea555fb4416ef97ed826b1608a055e11d6828834beddeda332b38a6dad4dbbf06e9c3e2a0ddf102677b79b2de96d119732479afdf5e995267a8365c886c0a66326dd36af3d43444fbe4436b1457331ac950995936c99d10d84d157283034ca8ca998cfa6ddf220ccacf1f5e0a9457443b022acfae152dd736abceaf4b09d92a14c9a4a262e6e56136cb2716034399849180dbae6e533b984eb8b63362cc9998bebbcbd2cfa222f760ba1cb7acf4afaedb6f0a63ebda9c433a22bcfa1f0a19ffccaaf3cf6e662da34cae4344699560960d0b1b2350655f26995423c2f8c7df066549370be7d7959423995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part245 : Excludes 0x280020000000000000000000000000 0x57f50548a500040000000000000000 :=
  finishCode 141 0xcc642e1688a0cfa41d0cc9958c688ce18867efaf48f536b09d48f84a840045ec2f03b439c17c31a6387ba55a92f0c692eb31b375e7c2fa638b58b8de4ecc4ffed15e76a71d0ba417d7b45c23f17d61e6a4b8b5613425ad16b3744326752432a168f82f36ad31cfaf4dba2262add743dbebe88d23d482fafa22ccd0f85469c4584cfe905f5c5a609133f5f5ac4a231387819f923da22c0b6a6d6b26dad2da3e88d20af257ed114db3ffb53b2688a6dd0f6fa785f34dd92d167d32477b7779b096d16d1f0b548fa75a2da3e734466df6d1605a99f06cffd00f436b2b7d3331d118a4e338faf609222bccacbb6de2882c134cab78b58cf93656887286f5a25ecdd096c132b6a7441c56da9d68aef3198affcc7a21ccad6358cc7c1915e5e6d4d74577ec91092375cdeb6a79c7a59b2dbc5826a697c9915e63e40333b5db4eb9bd61bc98ed4ea1853534b58b65e88a2bb58d852d6ba233ca8671d0872dbf3e4bebb68ccae88cfaed6338784a1f5c55e425611a63e6557d633f61317997d665638fc1797d37b7b0bdac70be7b7b417d75e379da65585d75744662e13779d9955e7b0442c8882e84557d3b4466574366f15e7d11613b44705df5dafdbbe9954558a687c4cf482faf588c4f34466ef7c9b447446865091a413317d3a9b7436caf446e93c0ab915d10ee14c0ab7e401b2d84e23e98b5f5b0be9b5e766f56116cb6e59e751565f59e688beba7bcf5f6a6873186f5ad070c6d4e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part246 : Excludes 0x280000000000000000000000000000 0x57d425480000000000000000000000 :=
  finishCode 127 0x563308b768c86827833f4843998357c4aea376a6a4eddf3ebd3499fa94da9c51c176de2a4f5c2f954a45921c67ab99517f0af0b1a04c0026779d0fb5333f26350f99517f6e4ca9ffd6a7862dc36a73d5bebc846f576a732b437857af685899fd32a15e162f0c29a2b620e655f5ed4e65689797542333f984cacbacf93316a371071ffda9bebe82cd699544145548592654cfeb537c9b3dab867e84785f3ebc4bd85385f14923ebe72d4e63e40f995441804acca52f771574cacacb67d4ba872ddea6732b24885a9eb11054ce86f51d2539ef61bed3e7ab3ef7bb51d6f153386549c740fafac455529ad4d4d6cde8970ad4250ad94d6d4f698ca861115df5e1854431950c7910f4832b688a25863a9ada2289760c829ac85a33ee86b1b446d3e6550b749145f59f5e69184f99e95815ac64cdd11695695a23744707e38d4879a59dac743d3e5edcc46d114cdb44628f87d7824cab01b4dd846f172d6f0ef174b5be7c9532d6f0edab32b847e358cc0b047c19b15e1d445bd5b6e824021ee511d114d77cf0079eada6ecdd4474461ee3db78bbe64319600bb529849d0669c665663c67c99e99597dc67ea1348c4517df0bed1179396b1756137b7a23e695d0f189983e223e79d7c1c2f8fce5af446c2f88f7d7862506619f (by decide +kernel)

private theorem part244 : Excludes 0x280000000000000000000000000000 0x57d405480000000000000000000000 :=
  splitAt 1 101 0x57d405480000000000000000000000 part246 part245 (by decide +kernel)

private theorem part242 : Excludes 0x280000000000000000000000000000 0x57d005480000000000000000000000 :=
  splitAt 1 106 0x57d005480000000000000000000000 part244 part243 (by decide +kernel)

private theorem part240 : Excludes 0x280000000000000000000000000000 0x575005480000000000000000000000 :=
  splitAt 1 111 0x575005480000000000000000000000 part242 part241 (by decide +kernel)

private theorem part238 : Excludes 0x280000000000000000000000000000 0x575005400000000000000000000000 :=
  splitAt 1 91 0x575005400000000000000000000000 part240 part239 (by decide +kernel)

private theorem part236 : Excludes 0x280000000000000000000000000000 0x575004400000000000000000000000 :=
  splitAt 1 96 0x575004400000000000000000000000 part238 part237 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part249 : Excludes 0x200020004000000000000000000000 0x5ca184422c00840098001000200000 :=
  finishCode 155 0x180a27134476174c6582a1b8455457e06a32084865867e535ede6cb19f7a598162d6a6dd0fb337c998f32ba194de653508f93432a68be0cbb3666f937cb64e0d04dc5f5e991b3b78b8b344ba417b79a2571e71a444bd0d9f4e645f5e1c6b4d9839916b1a58e2cd456a6319f44bbe4f1f5e319443349d2451815ebe94f7b72496e9c17b339ba705e6e96e9ac110d4216dc0a06cee6f58b319f991a59697bd45b2196a6999528d863125ee78b7b79918a5b43dedc67e59467e863d098a5624bdc4673236a3452cb2cbddc0b65824850382f536d9fc3bccaa8ae18da1f12ebcf8cd637bc6a2a1321cafbe0bbeb82dd98900cfe87d116d6312ebb3166c47a5c319f4f0c66cb9bd5b568714397d76d78a3c218faf6cbe700d25ebe6e79954d1613995934698e4d18b551574618cfa680759faf18b2e149b8d0ca9a36c964f35069311b1bce0bcbeb268c5ad31e6f2eff03dc50aecdf2d90c379a828a991d67766716ba1f59dd99d9bc7e311b16b4db666b06c3d2e14cf9366783316b2c7599be4c46c59d65680711b852d6350515a2362d6d9483853531903b74be9c40f8535c8a2ecc6f2faf8c19fb0a581697dbdcde578e19f97989d576467eb9a4786b1f5ed06e2dd31ddcc2a8ad2fcb1c8ab6e2e86f3863221a2ab43cc0ad935a5ccab01d23c8872cb4e2dd28aa33f13aa2af12a1607c9ad2d344de663d15515e1982f28ab64c530982f1eb9bcafaa21d0cf32adaf1e281cb029bccc7d2dadd2a2a6e37c2758de65be605515 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part251 : Excludes 0x200060000000000000000000000000 0x4ea39c40f4003c0000000000000000 :=
  finishCode 177 0x27180786c1f5ec14cc2220a2adb34264f728d6112ffb06658e06f00bc194f7b24f1d089aa5b35dbe9c41c56cc8d10a4ba4f74db146bcecb699de10cee98e7c350b28dc2f93ddde7096462221d325b584ec176f76a59e7584e6ab6cb5f57799aad3fd4bf0c5bdeb4544394462e13c17b539ad4d2cc926cad02631724996d8c5d06c926c14c959b0b426492428f0b62819574b3249b479b9d2ced4e55ec96a7259924855884d85f47b6a6966bd3b0b05330885a8ab28613041a5d5ed7424c5f05e6f7b064c5ed2ec9849e055e88cdcb106f3b372bcec89b84925a5d4dad6fa1ea72a162f747b85f3c6a85946da0a7fc9eed4f697acc25327982f37ba21e0bcdeec26ef73cea21af4cb9a54da16ef20b368f656886def8630b0a21db2e164b03cec836146157849e684cf269ca2f2a72f85239f2584ec317af94f6f779d9bdc53607f3175e9c2d9bdde7f43d84d7d661208b58efc8cd3ac1fc5ee98543cfb0be2874453185f45a84998b980d16a2c2d4f3e9bbca7ba85e88d60a6309cdce85a8ab8427b8a053ae8ad317a627fd68e886dd23cb536a7fda5d3350ccb63b380d92dd3a233099accf8e8afc098137ca46c072bf1ace88946acac432a46d76dea9a3a22e4d11803c1800dadeb3e49e7aec9fad662f8279f8329ee9a3174c28279f6a722bf0309607c5917d51185b5a9be4a2baecca360d44574f78c55f27a0d4b3c5a73e87cc29e8d6a385fd050b9f4cc56c2d409c19a51a519f070c6536615f2515da9e7b55d90aba2d5bdca349bdbd6315443613c176f75f5b237bb513feb538b5a517d388fad4df0619d3fd15e9a609f915f096cd11ad4f06f43d025aad84d80cd44536779a3db537d350bd11d0d915c1f6234d462d67984dc348d6a6dcaa16a5b6c3f59ed5395ed6a3db5344d8c20d824da229fe44ed4e7eab4f688da8bbcda0e12c862b531bceb72c6292ca36d0fd113f55e96abad06d2e6a7c1b3f54ff77979d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part253 : Excludes 0x204020000000000000000000000000 0x4e29d4707408040000000000000000 :=
  finishCode 127 0x6c319649e4a1e088689b24a65a9bf21de88d9733498a36d7977e1edbddaae6eb7d35d18637bcd37322a86bb9adc52ed11d45322865f76e97c2efda1314b13f0fb4b9ad8cd13c0b074115db6e6c5d11b535e90ab27b26f862f7924825a9f414968f4b4d2ab5ab6aaefc0bb18accaafb8bcb08c2f2fc5dbb445ebe65581693e2d56cb7af9955df9b15bd6d4c2ae457a0582701570c18c5a2adb2b8f3b051855b51b6e65584e7b7a55b3f98bb4d9a0a8e844fc59d2acd174a36a2f82fa6413199a01b65d14ad4f616a61da8c48f4219497536b6abdbbe9c11e966d55f59b5e6f798b5f598b97a742ed35156c1387e5a300daf2fd92da208c5af6cfaf3eaaf6a20af6c317d09e373d32ac1a4f6bf76c69bad05b9e655a9eb4b8779e5b2d46699d116c926f6444faeccf3fa22d4f68f087da9c48aeccc070ca63f1bdd8166c9a71b47b06de114891a22e656d2df5ecae89fb475df1399adc5362ce9c5f0bd3117459993e86c01ad6f6a6faebbf30945a1a83070c6d59b2e62c29d7c57fde8e0a77c38a1b64aed11e7b3166fae9ae14ec0b2bb447b65c34b04c2c7312faed970538c593de88c4f768b06109ee1870ab79d982665428c61e99286e9ad1dbde656c315f76c97d7b53793a9b5f4c9ee4d188d995d117d7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part255 : Excludes 0x200420000000000000000000000000 0x5ee1c5d06610840000000000000000 :=
  finishCode 147 0x184a05b25110b2291a97dd29815314605879899e65628ed11b336cb9202ef687e88af4b09ccabd7d4da3062ef5388c1ccac92c8a734cb04abc15614f506d5a2d69069735f19f4e55db5460e267995b43e1b914b5a6bd2af3b5fb78b6060ed0f7796af6efd64c4cf4ac0b642283076a3133ccaaefd48329fa2332b434bebaefc7c7a2383efaede33c927014b5f915b357e85b70ccab09da9af4c51212df308ccad321a60977d7611409a1a57edf5ed4ed2ed4ea63a63d2fe97e9b66542a5f94e3179e88b55e12ccab60d926569590abc2f97ee2cccecd46567815ca6461a169950ab959611613ba4b1d32a1532c74cad91f5e655bd69577af6bfa1a742c04ed4dde66564416110a9a65651388857142de150d117d7c29a57cc8d7c69b460d7c6a6d2479155afd106905bc460e8c26240d7e3073d2a26b0bcc1c306ddf304b78e88cda3682806896faf11b1f0c34c48a85d7271146e3ebf01b46616a59c176d59afdbbeb4b441d1144ba6397edb47445a080c844fc34cd82d8adcba1369734ae88b60bdbd2defa6d83372d60c6592713c44b4550ab97fe645f5dbc5f5e94dc19d11a5bd836244d4515e49389e220da0d6a76a2dc2a42c1316b43ecbccb7cc2fa22a432c75a8b70e17db278d7f2f3b78a90d434460a76035e79e2d7c660dbd69835cbb4b7d786432b02e16c1eb0fb306d23370e17aedc1280c1350a60c1a7fd31f6a344fe0dca7d667a236a331e9fefa724441a58dabd12f0669636af9c22acd5e882b0d09a1df06e63f446c198773516c1995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part257 : Excludes 0x208020000000000000000000000000 0x5c7745486410040000000000000000 :=
  finishCode 89 0x38190b05a33833fc46f7912ca37098c27578b9a1e63db9ed4d756347a593c6e796f9f56616959acfd3de63f3938281c2f9826d4d15e655f5f066609b539959c4a1f5d09660d9959aa69797c7b53995c25c2790c94290a96da9d492f16deef174a388a730cf1a3c50a08c68f6a7c474375da9d4a2faf32adab599c32e84924cfaf4a2b636a7287c291c68f4c74711b5dbdd026b33a4f77b9738166cced4cc56b53409a6da5cd027894d33ebda6da9b62b7aa04d69b28509a8fcd1dbded4e78bb4450c68edef1475a9ccad4279143048cc5a9cda9c51a2ba1cce2c0faf4caa2ab6bcdef4c4b43da9ccad99cfa6f5f32aa5f7094672813c7a3a99dbdcd1d4bd4e720faf4ca8558c7a91cdef316152daf646d5915c2acd1e6f76c782ac63df5e18f0ab96671bdd1065094577d5892df1e6c78ad98f44b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part259 : Excludes 0x200020040000000000000000000000 0x4fe74460e480049080100200000000 :=
  finishCode 93 0x9c60229647d7ce581b4510de9699545759f9bd70c65b5b6ed4e50d0b37425c235dd85edb6f8f605ffa58da6e957995963a5b6c0db73e3c41c56b6dd6a6deb4c98f9bc4dc5b3e5db281c62f218dc36a6f8f4c8d34c6779cc858218e44d281be2efcf3aa726e316b4b2a9cbd1c8ae6e3ac7a5f2c012b5a6da8e88bd8b06c37cc7beab129b65db5df93cc24695798fd11b3bb512ffacce5cd745b6e09586fb65f239d06c16f188f80a5425836576d11976ed1198b2816d1b447397ca6220cda2a426e284b5a8b70bbdb6abceaefc34c48940b75d6a6d8abb76a251aa43acb0456cba331ebdac4b53a65576ecde6f577bb538b380037c4971672edbe1d33396cc21b8c5ad6a651aa4332b268a2bda9c46c99e79ea176a69a3a228af7cb03a209705fb6097b1a63db2e58eb51b44663e53583693ed4cceea63c19d117c796398f8e5a9c48cb9b1662f3a135a8c5998ada22496bb732b2c731f6a79c44d942ed4ca352d64256f5995b53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part261 : Excludes 0x200020000040000000000000000000 0x4eef4c446608040080089000100000 :=
  finishCode 105 0x2f96c36fa04529932b70ae3302ae198630bcb74a67c9e70efa22dd7531b09da9afae18b08d8629e70fb85e31f34b04f1d92df6178bca0de88be1beab09da222f32df30b309b74bc6af397dcc27862d92bcf688b7498acf6a31e33f60a65c17ee0ab6c90a1945a9cbe2dcef874c2d36cbf61576a7702a1848a5817d584f44687d9851797c76f592d4bacc56d4d81687da67609b53c25b437445b5ed4d095bde2ced116c93196e9d0d85770be61585db27617089fa296d4c65c67fa0f874c2b0ba21e46b5376204d85e84ba22f86faba2360caecd6a2d0b4dac12c2fd0c8583016c19fc23a0a36d4e99509fad4e9969b04fa7bb7bbe0da2366e9ef10645a2d6a29e69ff0c983a2d1e07db534f77c9d11ad1e956d4f446b53c2f9346d11b53a6146cd26131f6a74cab5acb7925da9c62ad8adaf5a9d32b288636dd4c6a436a6def146119bd5097446b51b5359f9b6d4870c6656d4ed93cb53a6554e6656b5360594531d16b0cb5a6da9be4cf2a088737ba128cbbb25d65a74cfb516e94cf9766656d4d84e6f75d9197 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part262 : Excludes 0x200020000000000000000000000000 0x4ce544446440040000000000000000 :=
  finishCode 133 0x945b0d7cd3fa17028188ba2962354854e718837221b52d2dac075cb06c09be7d7267197a4197d6655b442aed4eb375f57d78a5a65510c65c65e441c66b3806cf80d85c2c14b3456855beb8cb8cfc52b986343b8a1a01933bebb11f0bd2beb684e18c3bd28d32b85edeb306db7618d28b09da9d609e34099ea41c2f7b59597d598397de5be6166139f5ed4e294c781ffd8636a6c22c26fae2f33d8afbb09855c80732b2df055da9cf2f9605e99f557ee19307364ccad86262abbf6a71170c9598c565ee905b2660df8d1f520afbb62cdd6d4b68789ccc8ca7ccab08e02e150be37ad306faf2f631e1572f7688cc18c7855d2f72df3eabdad2cb32b80ae3c297e45519fb537d7ce372d8da28ab4a6b09aecc8abb078d9afca0697d1554b6187187984ee0dc1977e362cdea2aa9060688a96d862d8b32a9aed575a5e16cb2c59a90cb3f2dac06deb4a7a90cc1ccac62d4d846d0bb4d959b42f39606f19814a05b9663301da9a96c4fc52ccad14b539bad84e655816b53b0543a032f302819839edf44626fa5b5b7df5df5ea82a231145e9a64c8da22d3f32b862c22dab296a4135ed11864b6c807a13373a12d360de88b52b68a96a84b01cfaf13ea435a3cb6c517de60e65669f00d6c5d0961169fa99c037425f5e (by decide +kernel)

private theorem part260 : Excludes 0x200020000000000000000000000000 0x4ce544446400040000000000000000 :=
  splitAt 1 78 0x4ce544446400040000000000000000 part262 part261 (by decide +kernel)

private theorem part258 : Excludes 0x200020000000000000000000000000 0x4ce544406400040000000000000000 :=
  splitAt 1 90 0x4ce544406400040000000000000000 part260 part259 (by decide +kernel)

private theorem part256 : Excludes 0x200020000000000000000000000000 0x4c6544406400040000000000000000 :=
  splitAt 1 111 0x4c6544406400040000000000000000 part258 part257 (by decide +kernel)

private theorem part254 : Excludes 0x200020000000000000000000000000 0x4c6144406400040000000000000000 :=
  splitAt 1 106 0x4c6144406400040000000000000000 part256 part255 (by decide +kernel)

private theorem part252 : Excludes 0x200020000000000000000000000000 0x4c2144406400040000000000000000 :=
  splitAt 1 110 0x4c2144406400040000000000000000 part254 part253 (by decide +kernel)

private theorem part250 : Excludes 0x200020000000000000000000000000 0x4c2104406400040000000000000000 :=
  splitAt 1 102 0x4c2104406400040000000000000000 part252 part251 (by decide +kernel)

private theorem part248 : Excludes 0x200020000000000000000000000000 0x4c2104402400040000000000000000 :=
  splitAt 1 86 0x4c2104402400040000000000000000 part250 part249 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part265 : Excludes 0x201000000040000000000000000000 0x4c822d608208000201009008000000 :=
  finishCode 175 0x7435158e222ded35990c25f0a66cf660952928944201d48666b6a6c48a2e8c9e683666b10963a98d7469553cc4a698fa5bd1130b9dd540ee164295801c290ea5ba027fd0f6f6f16b0b2d69af6e0774c9a81bd2ca3b5028f80169d69f656a1786266b14716a66b5a3da7be499ad85eb3e9e72d7349e3d2f8ac923dabe3e88d2a32deeeb0ef16747a66ab0b4db44663f0653cf066924525f67d54ebb4f335a5db446d16956d4ed36d0d3d1d0f5b9d1150b7d58a686cbb369e66ba23189cb1da9b6228c841b409acfd3cc006d0d6c1d11c19b3da9cc52f44542e96b89fa5dd1105fad35764cd69169cd42e8f6b538a3d0d98150bbe5c09f60b9a63dbca4efa722299507e59bd69f6a70f31468075a7be4c3dda9d39c2172d76a67e75a9a81c328154165939e64df26d1e4b9a1e500da16a5b981d65f134636f0b962285d67a65ac8704c2da9ca16f035a9caca01d6a6f92e05d9ad4e9b4cb6cf542f4465d997d4094d1b3ddc5b2f9b43715278d64664d666c9527da642d0532f9f364bddb7bcc7cf9e9a3a2385309ae88ccaafbcc2cc26db390da3102e4a6537eb4fd1198532d7939dd5f266166116a603521d3996cd50e245ac51f69f3c9c24ad62def4c9b54a938ccd92d985b1a893b9418ccc53444a0d098632f1aecd22c46a68833cbb313f4a2816c9e3ded32b836692a5e9ff3ccccae61c0c2eeeb03ecace0dc4faf8a85e88c9a35a9a85e88b60da226a3863027e0cbbcb09cca9a8d52c9b4b64cacbb630a16e333148019aa75cbb314767711b6776b2d4ddd6b51d116c1529b519dd697627e295f5651d36f379cc6a34148b4f0b70b9d0f9a1d76627df56371a1969950b5b64f094697dd11611351611ad4e4d1d11b4fcc1bcc1736c7bb943cd67436529b3d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part267 : Excludes 0x201000000000200000000000000000 0x4c826d648041040001000040240200 :=
  finishCode 77 0xd45b2b1d06622ddf291f5948ce610de549e0b11991679b9d4d5ba6506af374b64d48b6149fada98fda5fda88ccaef9bc8c3c16e69f6e291ac941b3b5bd6a65126ae15f144857c69ed9f59b9bcdf308a4f0588ccd22c16a7373a9acc8c97f6a6b9b0a9981d22a5fda9b5bd6a7acb81bcd802e5f830e6471a4c5aad3d6a297f48b6a76a735cb7ba88e16d3060d748b2f74b6a36a6a33216f6d0de789542996428acc9d84ba1b4dabeedaf2def272fbc46d31ebef3e6b7b92bd4e3a22dcf31facce642b1703678e05cd95cd9e9c2f6f6a6ddf6a75a2da9cde3483688c5a94cbc9d16a51e6ce6af4c9d6a669f6cb205ad40a0db86b4d88f0a36d1ad4d8266bfb2688c31e94a0e63e403c297c9323a27d8266f14ff (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part269 : Excludes 0x201000000000001000000000000000 0x4c822d449240208200008000001009 :=
  finishCode 97 0x351d0b66e116f41c4be6d0de4d6629bd119346284d6623641b5f729961315997dd04584cde4d6637988fa53d84ccd4666b148cc4f0d3cd9de466ef78d9afd42ee130903e4c51e2ee2f654be268e88bb0a561e696ba55824d42e1e697d4ff299d65f1766283295a55a2d6544a653fc25e8a38b54ff8b5a1e659df54cd542d06e51bcc3eaca16ddede3ac27d8a5664ea55e2640fce03bc17781d11a738b5299b3d906e6082326f85cbc9be9aece88c823b8ac523596436fb84d02b54a6d115338b5b4445ed7d66d9527529b60bdcc26eeb4bee86bdaaec8bddb1e365f53356d16130b734fa5f6d0db4f7b53353596d13599b5f0c53454a549c664de69830e33269312ca8e986d32b64b65d1b462830a3199e8688cc2782ea2a507309a688cb9a4cac2782f0c19a0d13fa22d6382f446aece88941e62393cb6370b04ca5f32addf2fde88be2d3ec1b775183d116136bf943ddd85e26a306f329773cbe17d38b098c1d32b6c967a23de1e285ef584e236177 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part270 : Excludes 0x201000000000000000000000000000 0x4c822d408040201000000000000000 :=
  finishCode 113 0x350fafd0b6563708b748d64a0d9dbde28935796592fc61da3c9f4a266563ef79f521b5341b34f7919b3ed4cde6f98452782c4666916051da64461e646b538678454fd6916656d4cc8e27b8a36b7b53dc68381c4da45acbea83651e5337c5f5a2d584cde584e7bb9bddf35044de57d5dfe3593793598de6f8beb0588ccc5ac4f6836beb48ac6633869e6ae7e34aada999ac5ab779ebc30f70983e4c51e2ee2f6e0b53a639f0d33d42e64e7d5b3d41b859d46f8990529a2d4a66cf628f41b9855218bc7459846a6fbe9c52cbb2f4b4a33c0da785c845aeccc2d4a282358da5c25f6b3741b323b53295303810ed4506dede1ed2fed4dbc49f66ef51d9e4f59b8cc36fcd7e6f370b66802b45ee611359a611017b97d9dd5766d4c995dd6b378b57c7a2d52cccd54a6d4e23e51b41b535c212acbea15a3336041b8c8ed4c61e646b53b63d8cde2da216edbf562c9d00a38664a0f0982f4c0afa8ccd02d4e6d199518389fb0bde1ed4495781849a43184584e80a436a7204bbcd6a72df3ddcc9b5fc16b6a732b987bbad452fdde6655825afe60688f7878a17bd2559afc2d664e5155f5199 (by decide +kernel)

private theorem part268 : Excludes 0x201000000000000000000000000000 0x4c822d408040200000000000000000 :=
  splitAt 1 60 0x4c822d408040200000000000000000 part270 part269 (by decide +kernel)

private theorem part266 : Excludes 0x201000000000000000000000000000 0x4c822d408040000000000000000000 :=
  splitAt 1 69 0x4c822d408040000000000000000000 part268 part267 (by decide +kernel)

private theorem part264 : Excludes 0x201000000000000000000000000000 0x4c822d408000000000000000000000 :=
  splitAt 1 78 0x4c822d408000000000000000000000 part266 part265 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part273 : Excludes 0x300000008000000000000000000000 0x4f9164541400000660000001000000 :=
  finishCode 103 0x67371a8ac6b3192fb0649af9b7e84d32a1932faa2232e6bf909c5836832ef7b5a99a7c51937bf180e8b54196e047d4936a669ec074bb047b43d9aa539a7c930c615d9953357cd34fa5b42ce1ee0b71979c309d16a69f3275a3afbc51c5add249387e633208328aac0736cb02c3285db6cd16b904190c994a7446b4f061d11915515e5f5865613d119679dfe64c2ee19d8151565466135cd0c9d118a5012128995c64f22b6d11967439443ba22ad69b16a16abeb132c22989afa1f43d8c1c5ad24c63f2af0c1c3bcc02d57a69676af611c2dad3d35e27f446c14c611860d1051542ce0b518359fa19628584ecfc2cf0914b5a7ca8b01a16d16b0f75a9a2685ae88df3516cc25802ee98a1ea370cf308c48cdaf2d2c4fafac48b64d32d4e9954418a36b7862c62e0bb44da2d42d57d68a34194438a19959c5835832f4c841aba9ab73cf9adef13f3d5c59d3066aea372884370d3c23e2416037cf425ad1def665622e5b689f613995a5bad175928991a656d4db1d444d5d846511603a6570c5f3742668786389fb53c19995197 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part275 : Excludes 0x200400008000000000000000000000 0x5f30e4d41200104240080001000000 :=
  finishCode 137 0x3414cdc593598c2839c61115660c099397674457d4576c176f5603d11515a547446616439877b08e29663d7d7445f8bb343dc50a6ba16adeda2374c64f17de443457b06411570c68650b56cb313a6570be2d619e613c8524cdea9aebead9711f5a6ccaafacc2c97ab632cebef66287384924f2656441521a0220d32b14b5a9b01afdd85fa232d6c22a473c86788f97d97fe95e656b04e2808ab30900c1c50cfa6bc6676bc7450cb2e88cc9d69b447b09b7ac50e1115e27e87ba456f5a730b57b7a5ae6e59675f70b58c3b259e97d86611b6e9957d352d4ff98357a6183a3d5fb951995b5399598354b518b87656259e5f6e9385fbb5396fc576655abc93508df4e689a917445abe6562ce945d321208252182627e8a55e3a5465463359bd6546701174a8a11da6d32b6833c0be4ccaca8cdca16340b255218deb046be0be9c516c60b19955b19e942c65120c2db43cc4e6545bd3b6995b4da7124995ad3ed4d08c23c02660d00d3cb4d716f96b995ad3ec938c2211858cb7edeaf17617b06adf8acc7d3a22162c1b2dfc932128c24126566096f58652295e5ffb3d5d525178b978d7ff0c6995ba4c7da22f522b68469af357b55d67adeb3842385de926b3fd0d7d3b4f684b59c2d3ec2fd0998f40969b7c99b2e63e995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part277 : Excludes 0x208000008000000000000000000000 0x5c166d441001008241000001000000 :=
  finishCode 75 0x1a0ce5c371c0c85f067ee9b40bb7c14a9a3d32767e9fef7b4c9d9fe83cd376a6dd24fb11e9af6d3096a74c0a90a9ccb5c9ff32b0819a3a73cbecc0eb368b4b36bb5cc46a9cc5aa1c947df1a84faf88b59e4dede5e69934f976534da1f3272a33e0e87bb25ce1779819934d79066cfe88f87db35455457ac05f8c7ca72f9f21ca81d0cea6711e1773c0bdb53a9a53e5a9d15e23d0e41f66974414f988f6c7a470063e98a5329aaffcf6ac2f2df3eab0bb53a12cc4d85b4c69e64ee33f90e2672a97c287995946c2c5f065039452dc68ea6ad8f69adef2f3102da3a94da6cc265617f51ba659acd8b6a6a536a7452ccae72a816331f5a9b7393aaf1d0417f7bd985ed3e5e373bb10666570be15dd0bb53a69897883b42c5de7c16d9b4d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part279 : Excludes 0x200001008000000000000000000000 0x5c966c641049000248040201000000 :=
  finishCode 101 0xdc6b2b19cd01b3f03897c0cbc213e9bbe84cd8ba17372d327a175a29bb861a26d69fa178526ee8331439bbd236918e21aba94c5136c5e998157b6409e02ef9f3d6a6413a0edb24faa6b2c73e6b7bb64ca53a05b55df6e5ad3d4749f5446e071368c46d9287455899908e58de2e58e5e36a68250ac6b9a915b662d697678b6e797960351da9ce976995533503981578e885d0b0c39792755099156999cb06d0a065f5521455943f1b96a5b6f534f8b588f441a7ca6d2cb0f729b37ac22916a7396398f6a459d67b0caf6b5a9c45d82ec22a5b48845c2511034fa2047cd0edcadead171ddda9ccaa73adccd4b69f837116f9f4e7445c59ccad6a611f31f70613a655bd6d3e22e246656b53b0129bcfd2c74e76a7670a066af52d34fad4d7a6c9b4944310bd13573696d6e97c2f4cb3c1de9f2f26b4b116d2f5a9e83b5db6ac1f32a32dabd24f77cb04b3ca3aa67143611da0c48cbeb72d285d15cd96d5b5df56503 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part280 : Excludes 0x200000008000000000000000000000 0x5c9465441000000240000001000000 :=
  finishCode 153 0x2d958ce22de8371ac52d867cd9cddf2160a60cfca7cc228aa7e74ca9a7c88616724605945e2d4d3e23e95e86734f613be5c3096a70c5a2085885dd226565cd99118b69b9734fce1ed1560bdd0bad4e23c62da7e98f9593cb287423b53367377d052067f590ef13ecb29449aba08cf9ba170eeb02da993eccad6a6a226afc4e06837184d2642e850233ea53447b73d32bb48a3915d7dc32e69189e2fbad2d16af6f2cf3270fb3dbccada2316b11fa1f0fb459c3394dd32a9ae8aa33f63279844575f582eccee99588f527af90f7294a93e84cbeb32b90da520a1e64e4a98b37ab7cf5295337651208bc7a132549efe86a8eccada22d73686c4c809c37a8ebe4c9af32b656847489812bc833a1616332adcea66a53373a0ce88b64ca8be4c832013a2332b307c4cacdcef82fa7483d5b0a571ed369a5b5f43dae67afa4688d32adce8335d258e6e987b0b34577abb065695ba5a6e5e535e614306657813c620588cf93ae88c7f60bef172fb688cc0dc293e87d4090b119fc66b263e6f70c398f88a60433035e30c1b7190e06b067f398c45582ecdbf88a5343da9394dbe4ca4f614cc8b0ba94cf250c4e21f9e7258e99145787b88f3039a1ec1734fb3d4dfb3fac710d3d3ae7b54dfacfe457e26d0c0e4578c539d2c76a730af6b48b5a9e87d6a769b38e226bd3228aa2b7688cc8c33d30b67ba22bb39cba5611550460c18715ed36f0c1b0661239852f736f0c161789dcd5f588af447865947d9ec8aa8af8c455949d15e19e529 (by decide +kernel)

private theorem part278 : Excludes 0x200000008000000000000000000000 0x5c9464441000000240000001000000 :=
  splitAt 1 96 0x5c9464441000000240000001000000 part280 part279 (by decide +kernel)

private theorem part276 : Excludes 0x200000008000000000000000000000 0x5c1464441000000240000001000000 :=
  splitAt 1 111 0x5c1464441000000240000001000000 part278 part277 (by decide +kernel)

private theorem part274 : Excludes 0x200000008000000000000000000000 0x5c1064441000000240000001000000 :=
  splitAt 1 106 0x5c1064441000000240000001000000 part276 part275 (by decide +kernel)

private theorem part272 : Excludes 0x200000008000000000000000000000 0x4c1064441000000240000001000000 :=
  splitAt 1 116 0x4c1064441000000240000001000000 part274 part273 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part283 : Excludes 0x200400000100000000000000000000 0x4e32b4f08a200000c0090020000008 :=
  finishCode 117 0xd05831964a822ac8af38c2225e02d83333eb85ad9dd6669dba12c2ebb2506faf483141d39d4832dfa2250784aa5606365ae3355d998f5fb8b3b4443c57ee28396f8a0e4938b6220bf1f3e23e6e13518b5b539826d06d116bf775609b6613a1ac5218b5b0b6d4cd4580e985321b53b5389469867bb797b418586d4fa1acde4e1f9806e1b41b0c535c2d663c99f0be91e69bc17979b4b9855fb82d5afd7ee351c2f9e65827446c2f0b56f182d70be29bc7d77e49220deb4b2aecb09a16cf1b466031617cf1710a39eade6660d6135159eed80f5913f036b75941b0bd5308e8a596ba570a75217999f369bd6e5f9246a216da6cc0ab3b85b16ac49e561f365a7a57251617787a23deae5b688fad3581679d0a498c7d6e585db86799a18c28f59d07ab8a0dea545578eb0f3335f853c3bcf52b3b0ceb3b686d30853e32c9ac7cf86161942d4666d0bef3e699ab09c32cc2705aef257678b5db7d75f778794871964c21a8cd1216231b1c921a8c51ea627ec2fa71b4b985b446d35f3f446a47b310a3c199c2dfda224cef2f5a8c59bc3da22de2c136a6fae6a2d46177d74ed9e1db1744578d67e6c5c2989f7cf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part285 : Excludes 0x208000000100000000000000000000 0x5c16f5c08820020002090400000008 :=
  finishCode 37 0xd670369a0dc6109d65d55e319f7d70bf29be2540a56e93c87b8b56e7985d77db9eb537c373beb823cbaa68ea23294d70b02ffcf32c2e33f007ab9045f3c586b539c1f9da160ef4d36a668efaedef5a9afdcfaea5217b8cb43ebc1624eb3eba8ec4f6a66faf8419f7d782ee22e86525b6b97d70bba19619f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part287 : Excludes 0x300000000100000000000000000000 0x4f943440a828000000198000000008 :=
  finishCode 121 0x359b8cc673196cd21b8ed2901924df1b3b5ccfae545e7b373676d9611a73b0965aea5ba436cc6cf12f35ca21e9290192e4b3b35f19736f2eda9cf4465ad67ea41865d12e36794064c10d7c18697b42d4d9d11b3b7ab7cfb0688d322a670f3688cc8a88d2a232fa22da348be582313233e18be851a94a99d414a6e0faf6888cbe30cd6d11b5324fd0da9cde34c74c36d0db539c692304cf618afbbeb9abc52e0fae9533cb8b8a88c4f8bec84a66aef74aecc1b7ba88c6aedaf3e799ada98bebe7ca0666a6af08c05d1e114d11893df5ec170b53865dae6a41d119ae54766b9a41197197a1c5ae69c5f5ef8b4f69f52fb088bea8e9f3cc262db82f25ccb9d9dafb8bedd3397c921ac8ccc01f5eb537bdc2d9bdcbfea4fd097d779998521845bde7cfa499f5cfa6b376b9457d0998308c15ac2767b2fb8beb09c4dfa22faf808c0cc85dc32cc270cb1a4937cc26a1ea6a69360c66d2716845588d9ead10465e196197ad3c9bd15ee114197b519e3623580d84678f6b539da9ad28c2b02d6a74e3360c5ac9065ed1142d7a97d726f6059f5c65ed1307e30199ad11b0cac278c33582de60e4d77d7267a196 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part289 : Excludes 0x200001000100000000000000000000 0x5d943c618829010008090800080008 :=
  finishCode 103 0x713596cdc68339b42958dc4a66f91837998fa234d6543d84dd911f5a9c469acb64da0cc074886302d31e6ced932d7302e11cac9b3b09d2f348be6d14a585e6e76a92896e36c9abe14c7ce4127cf5a9e14da348fc942fbda9d4e6d6aba2f9e6ae9a34c7ae8d39ca22b6d0d6f56c56c7c2986281cbdcd8b30729b3cbad2da79abd15b37ab62aeda5acbeeb6ab86d5359260a5369752e8c0c5ab6ca99b6cc303b434927b9ed57b5066b4bdc593699c6178dbca54a6688ba31abc41b5aafdae8d862a0766b6a651338a4460d9ecd65293576f5b42e96cc76d4e9056d54a738d4a73b42c4856d6195b462d690688fb4fb0a540e98fb536b536f87b96f6d4d76540ca64dbec8a673d8b0ba94af6db4b2220c5028af6a74c7a20940bf2316c985a8c30a9d72f24aec0ac26d9f3e3afbca1f1e6bf8a18b5b2378cf8f4e730b368d69e8330cb11b3894450d3e89696deb3cf8c2da9c30b5a9d39cc0730ad4b0c2da9cb1cc7df165e899b358b37978ab5ed5fb371ce35cd106ba26ce187286e79ef65665bf8835f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part290 : Excludes 0x200000000100000000000000000000 0x5c9435408820000000090000000008 :=
  finishCode 107 0x16cac66116f71acce680d9cdc5f5eb537bd8790c1b539f5ed1a06d98a24d5c67db663578a5f1f5da0b9a51282343bb47d8631574c8ae6944cb7f68b81a7c16e33fb46139f5d0e5f5e611865ac817616722b9a4c80b1439c7d7b2221c8ae50361894cda9c513acdc63331b4371d222acf76886196182fc44b955910ca6623510e4d7d114d18bd7445f5d79c67f69a0e0281c87253288729ac6b316b3ebb09f1308bc73d5be794394cd20a554d63b97d74237cf423867e7d7c666340a67225a2a85da5ccc270cce88c85aa3aa6b688c38330bb6c0af9b0cfa2bd326a2af9e8af3098cf8bad11af0ea2a33f0f36e38170d60cfce0a2432f4366c59914257d7b53a196d663291a23520d2dbebb0b9b7a94ed099e51d6176d19f5e9766df7d75055295f19c3ebd4864ce8ab6973e3a2bd93388971b3ad2860a2adf0cd68ab96d2677d76179839f5cd5de8e367c64902f50b644b5f194cd1557c650fd117d7529 (by decide +kernel)

private theorem part288 : Excludes 0x200000000100000000000000000000 0x5c9434408820000000090000000008 :=
  splitAt 1 96 0x5c9434408820000000090000000008 part290 part289 (by decide +kernel)

private theorem part286 : Excludes 0x200000000100000000000000000000 0x4c9434408820000000090000000008 :=
  splitAt 1 116 0x4c9434408820000000090000000008 part288 part287 (by decide +kernel)

private theorem part284 : Excludes 0x200000000100000000000000000000 0x4c1434408820000000090000000008 :=
  splitAt 1 111 0x4c1434408820000000090000000008 part286 part285 (by decide +kernel)

private theorem part282 : Excludes 0x200000000100000000000000000000 0x4c1034408820000000090000000008 :=
  splitAt 1 106 0x4c1034408820000000090000000008 part284 part283 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part294 : Excludes 0x200400080002000000000000000000 0x5eb1e4d18710464089011024048001 :=
  finishCode 57 0x300549c688e92b128786e1f5e20de2be3204d9db5fcc1b65965c4ef69b68498faf8cc1b0b8c1d425e67a5c2f6f1869183b33a1a705e7d76f1a41902629627d155f5eb1b850b9bc57eeb51a1c500ecce60697515e408cdc448ca0ba66b16cb33bb3789f50b96f8f3eb3789f45796f942e27dac650bd24e370faf3c177a545b3d7665f5bc5766b4d2836bf869ad353b7425e7576460e51b8d09894e24542e7887330bbe9d13f14abe369b539941cb7ca185e6f19811836f1b714cb213bc8aa5073c6df97ee63e6bf31fa5b5f4e27e2957ed136617 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part295 : Excludes 0x200400000002000000000000000000 0x4e30e4d88310400001010024008000 :=
  finishCode 175 0x451d0bcde4cad6278fc7c370f41bbf41ac5177d3970df5e18ed45826ceeb317d74435df8caeb3b7d7b2631e6644d8718ad5a78f7e90df5d84eb3726796b7d7609c04a1b7df5d7d60b552f787c2fa2b58465ae3518837c5a30174991860df5c2d579e5239e6579dafc665e666bf96d613860df5f49a07d7c222acbeab9b456a2b9a8d10630b2c68734b2b58a2b9a8853c16ba1698afaf80d24e2d0faf60ba61096e2670b126791545fe79589559bc620c26c5ddc130b18dc56cd7f26bafa8cccbea333221e12e9acde189c8afa223328af0588c6a2bcc2616b50d02f3cd96c26627365af3d2ab0ce02ead836fa7486f3abe330b9fae0d9f4d2d73272efe88859a21cf299b82838d457364433495fb3cd9746d446657edf4e409c23277199ba543193caa22bc3bda224ce142333d07999b0663dbc6b33267a5fb422acc7cbc7a2216a143a1f43ed39e0ce88cc793bda167e1777d70a77d7b19a49e4b2706a3806f19f5dbc696f199a555bc67d7d118a0c6674463516f16f19f5de138943ebcd05ddb2e98fa735f59b7e963a433516119a4830931eb3f4aab09941da22f4b59fb09e88e88d2d6bcea5f3ca4996fe5f5e94a0c26e5ad736c2f6bf5e7d6742c9a094563713c2775df9bc5827809774c8bcec3ebe0acfd2babe2d96a46333609e226cc2f8418382d4966d117c1199b0931f0cc859c31ede455d11351d09a97f4451569746660b3ac4a2a8c12c2eb3f0cccc7c3332fd858cc2d4ba6a3286ef977db854bd82577e0b5b2632c0333058859c332dc34c8e0d8c1932bf1b7ec2dd1131b6f1351b424c6c58c60e0b5 (by decide +kernel)

private theorem part293 : Excludes 0x200400000002000000000000000000 0x4e30e4d08310400001010024008000 :=
  splitAt 1 91 0x4e30e4d08310400001010024008000 part295 part294 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part297 : Excludes 0x208000000002000000000000000000 0x5c1665d18110400400000824100000 :=
  finishCode 69 0x8a3c271487d7ac6e321c0b471067cd1de969550b199531b9f2535f419c779a2ad3fd7fd8342fca55a0c1a51368b44ba01c3bc37d15b122b6369b30693acca85fc31f32b22a9a3a8dd2d62fe162317ace240368a4e2b73d2a2a8adcfa68af4b7bd7ad8be9a9a98dd4a34ce1621769af459c56cc28cfccadace26833984ac05da91d32a4fb32b147a62c01b2cec1abc6a1ea66a6b304ccacaacd9631b32ba0ce0cfbcccbe2b3e98ac1a17f69f2d8af199daf1c4ea16369f4caa2b8cfe4340b6b4c9a87a9985dcca8cf858ca17147ccae8321c0a40cfb0bca1ed372f68c7dacd0f9ebd6c5b9c624a3c9deb0a170539f7cd0f13f2df30a8af905b19f054d45fc2c5bdea697c10a7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part299 : Excludes 0x300000000002000000000000000000 0x4f9426c08150500000000066000000 :=
  finishCode 67 0x1b8cc562d14894580d3cd5ee0c270cbb77cc0afae836fab82f221b09e72d9ac7e1bcccacdc2dbf3ebccad81f5e9956ef7b19959b870c5f5e27e8a5d111976f1a6309cfaea6b8051b9ed465df5651bd6340de450ea454d786f303a5f9957b57c7c02edcc2632e4cb308a8ead3d82e1303367a2bbd8b098cba12cfaec2616f302e8318192dc33c89b8aedcd9efaeddf35f9b8b58c886166fae8aa6e364ba4d11558465356d985ed49df5eb44d250c23a133dae188bbd95cfaebb299f1ac8bbb41f5e40627199e17cf8fa1769f348e84e17e61d017714967b0c5b2543e65569689f8a519950f7c397a58145ee7d7611455 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part301 : Excludes 0x200001000002000000000000000000 0x5c9c2ce0811940000c000034000020 :=
  finishCode 59 0x19cdc662d850f357b678619b89bcf00dbecf66f187d0c38a528f111b0a6d14805b3d42dbc5157814cda612d851e536c231acb6cd34ca16bb252b59184e9ceb473f36e927db4b8c5e19dbdca5629b6b9915ec1c0b24d200a67a051b5e991349eea73b41a5961727b985e6565275edcc373c2df32aa1ebf6d03e59aad6d5f5543ed9683309b53cf87645fb915d7b686591b25ebe94f9837c1199b4b977dadeb4b5df199da71380b8728d944cf2204eebf6dcf2e1b65b53cdceb86dcf13bca17b57ec97e8b38993578b389f6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part302 : Excludes 0x200000000002000000000000000000 0x5c9425c08110400000000024000000 :=
  finishCode 145 0x2d958cc22de72d1b8c81bcdd2781668af221b09cfaebeb3ebb09854d31e8aac27a48a05dcf29088729f3c9cc88c5e12d4bf32ab9aa6722bd4e6fa6a22b9a31722ab78cfaed9e3326e3323455bebaed9448cfed1f5f394c199910d15466644317b8a24cee27d511611d66e3686e28af0cc94d947be308b3f688be4b65bebafab09c71f5f42633b7935357d39639e75e7695586752759f6136e97d7cc583088af52ec388cca93858a6bcfae7d332aa667e74bdbeba2185dcf1845e7669b7d33f37d7443a739e75445b6748e0cc302afacfaf32a33efaf217b65d9ad16633ebea8ae887358859a2aeb3899ce0642e158295a84f05ef4463f54c34d18675c3609457642eca99d34c95712313f66ed4f66f05ecf3aa36c2e17b299d39c24607329f4be17a89ad7ea36a4f640cb6a7b0c443f43de75f0515ca3e19e791779a691777d75d9cc6e030627736f5f1985c62c2f50264578834397d7e01abca1ea4e51398a81abbdac4ef2ca4cef6b13bcb2beba04d1064eefaf58b85a0d7e36f18f9c4a1bc5f5e5968976178b3b05e25e59739906c1985f44430e394d33c0ae3da7ae3cb8f534be4c6df380c3781a536cd629699c99df5f4465d9b4fc86638833f9c9c35fc8aaa0457d0f8f3c1bf446d353aed069cf0c696fa45b4b96fb44661493ded5f567158842cfd483a16de3a2269ede344bcfae9bf5a5aecd9ed9338d0f204beba26dc1aee6cb3ffacf62b542ecc4e2b13c5d98d3dbc6d364d17d7d0bc174556bf7d7b42e2b51578970457c17a2ce5bec31b41d115d9ad3d766457 (by decide +kernel)

private theorem part300 : Excludes 0x200000000002000000000000000000 0x5c9424c08110400000000024000000 :=
  splitAt 1 96 0x5c9424c08110400000000024000000 part302 part301 (by decide +kernel)

private theorem part298 : Excludes 0x200000000002000000000000000000 0x4c9424c08110400000000024000000 :=
  splitAt 1 116 0x4c9424c08110400000000024000000 part300 part299 (by decide +kernel)

private theorem part296 : Excludes 0x200000000002000000000000000000 0x4c1424c08110400000000024000000 :=
  splitAt 1 111 0x4c1424c08110400000000024000000 part298 part297 (by decide +kernel)

private theorem part292 : Excludes 0x200000000002000000000000000000 0x4c1024c08110400000000024000000 :=
  splitAt 1 106 0x4c1024c08110400000000024000000 part296 part293 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part304 : Excludes 0x220000000000040000000000000000 0x5c7464e08122208080000000089100 :=
  finishCode 69 0xde602b144b422df033970d60cf9afc6df38945505dd6f630da6db4f96f6d3eb535d96f15d9ad3e706bf360c56b78eb185eb536c136fb538c0d766d3c67ece00ed31601ebfec12de34a3192c4b933bebb04e71f5df4e0c16f133ba2b625e59585ed1a0ce5b02a66bf6130b3379b4b9afecd467dbc4d5e5e919f0af8de5f5ec65b099e6b10b7613371c85a7d12e9a233ebb2183708e452aecd69e0b72ecaeccd62a47d7c82eca04d326f7716760bcc9bddd326c276cce367c1866e26f30c5df5fb87d8b8c024d5d3ce5b6d4daa627e597b5317d3578a5942ed4cdbd7ede1a07d7b836cc16e33f68361685fbd7cdb369e15fa07cfa2942dc67c2be (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part306 : Excludes 0x200080000000040000000000000000 0x4e543662c103208000000820009000 :=
  finishCode 155 0x1d0a26f2d99845bd64cadf2784ef144afdd9bd836142db26ae513285db8d5dc8dab2e899acbdd4e73074c9e309c48da1715adea2dadd72edcabd69edd770626b1b1699347cf827d7dc9ddae627db356e55b54f38a2584eb3d6e5d63ddc4ee4faf573c8845d305f64256c9b53970da9546d0975970be70067e27d2899a6909de20e3356d57d7609a62cc75bd66b54f35c36097d7c069271687d7980c799ad6a6dea2f684b59ad39cd8a84ad8b19dda98cfae8c6afb43c362cba2e46a1abc9e666b15b536a81b62da9d852a06477539ada84bda9e6251486179a1abd30c0e3f37d7b53a5d5297d7ad4df5ec29b53a7394756d57670a5f5d3869655297c3ad4d46e30dd612f539beab52d6a64cf4baf0b83eb8cbd6a615ebf75a9ccaa8dd32a98abf615fa4d03ebeb067cfce27d289603a65584c2beb519446594d5ca2467f30bc48632656e1604cfa5cccd6d4c65c2be096a7288d9b91d932d6a704d633298ec17d7d7a216d45b670be5e759dd0f96db53720a2c6ae95b6a69a24cf5a9e17c84a6ae2fb4873eb99ada98bea93d2ae2fb6a6a530cbcba99a9abbebbc2f8faf702e1b05dae6ced44499465e9185f36ccae9ab968d6a6f3e84a6af5a98cbe825832f34267c319a3f0bdf569cd2e6d0b7c3892c2bed0602f970d20cbb01ca22bee4cefae84b0bea889abe90436d0f97ba739831757d7267a61abcaed85f6a22fa237616cbacaeb64cf2e32f34d253180e16d6138b38cd57a49666d93570a18d5c28617f3579840184d7d652709facddb66b3709f5f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part308 : Excludes 0x200100000000040000000000000000 0x4f18a4e9a10a208000002010009000 :=
  finishCode 53 0xc666379a8b44f0de61958349181a65585d16f089a34ca8cc8c0c6264e6b95bf883b436d2cf4578c66645bb33a1dd4d42c516df5e995199b2740666192a31a4b06b0bd22d6970fa112f76c126934b5beb933bebd32b70b44f02c61de4c57d732999518918d4239315f5e655f5e0999315f5e6549ee993c199916cd24d66c88335a98cca9ac42716a73eba0ca11f4341eb5150f875b5369b7abad4f0b56fdf5ed0bb53c0143bebc8b73cb5385368fe9bdf4d6fd34659e64ed2e78550fd43ebc4fd14af6edeb32a8b74c6ef97fc24d85e995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part310 : Excludes 0x200008000000040000000000000000 0x4f13e5608342209000000208009000 :=
  finishCode 17 0x2d8faebca64ca9afc8b6bea32f360b789afa2dee2e190d42fbc19232e8b6dab36da9caedb098c19afcbee8b6bea6bf2e6cb6a2dcaed0f716a85bb8b4f90654a619467c32d3e68a35d942d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part312 : Excludes 0x202000000000040000000000000000 0x4f15ae64a102208000800000809010 :=
  finishCode 87 0x662d8e8d24cadf1f5ee1bc0b76d197d6194de742e4c526797d6194de742e4c55f518b8d9ef980b85606042ce1e66d177b0a91898c867c38b56d145b379379ad4c607794c955979d84c65eb5332545b460cf82acdab84b326fae5b34cd098fce5562d6d4db64fce955ac5c2c833faca413eb42d4cd9e96e955a73b51b424597426a5d79d5d998378cbb212edcadd67df5a0bc8ca89929b3d6a6dc8e4d1b05b44fceb5351d7c30bbb5967352eb67d9da68e1485d9b7d3172eb418a1b3bad0696ed4e6a5b4b6cf26736f0bb867ed980a240184d16df5e8a36db9e75f242a66135f5b53861584d10c0802ecbcfda1e7caf3a9d76a711f147644e7a53d0649f6d4e7b5b86b2c8b6b3e4a9ab7ab6abc1026b539a4416d60937c3b4f824c586196d3e8795b5b41a53d3470be195bd5b56d066a5527d64714d67d35339e74c968a1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part314 : Excludes 0x200000010000040000000000000000 0x4e71ac68a122208900100008009020 :=
  finishCode 53 0xb24a279d044396bad4d3fd16ca554e6f92ab276b789b8bebd32b6a7bcd669184e0cb199965acce65705cd9ca64de6996888309be2b116b4b6e0ba91e0bcb4b60bb45da6c5accacb2c166f570c72edbebcc8ca476a68b73175a999acca941947ef349ac45b94b665432c66699685f78615f5d84c6168639955db7d76c5ad2f43d76d16e656f932b3c6b19bc4a6ec3145b86596f695516de5e5d118d9957d7e861278dc34ca9b3a96a9ce4298532bef45ada8c16b6636834cada9e83d31a91b09a2dc6ce9ff32a52ba8c178d9e654de580e6c1995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part315 : Excludes 0x200000000000040000000000000000 0x4e31ac618102208000000000009000 :=
  finishCode 143 0x53271bc42d44bcc5b2786e332a6835a9b0bb7085acfae52b065e1279a8c80b0cfaf6a6c264de533d094296e87cb4af231434cf2ece87d4c2b4a6b2f22bb7309a96aeccfaf6a70cb11ba133babdec478b0c50cb9c532faf649e5b115ef9840b59b0665463750c1b093e16b6ccca8cf9a8a8e941d9019f8326656dc5f032d3165fb28fc29accd316cfde4df2467d4ce617b66f3597cc86a14ce45b295535c205ac4ca506332147141a76d6a651f32a333849958a6584de167bb0c97a9a65584f7016b32a2633d4c5094ac50cdb3b8d64c5ca06f3af9219651f906e59bad766b4f8b3c2293a9ad22cbb36a35a0ea379b8c2064cf0a657d63597abad3ecddb6628516eb378a1b64f298e5c35fb45b3498a1984c2f5b2516f3002b5a9da0c4fda885eb0ba68d6a70ef36c85e8cfafbd14332bc0e86b3519829944d8d9c32d3fed0750344d295cc2f11366d1b537d79959e2fdca5ac12b9b34da7fd2dd39af88ccca2791044d95597353fed4cceda46b3b5397d7b53c0441bae51733bb379ebed065cd73679d199b530ad9b157a6e198c0226ca16fae16e33f3c6eb9f1ca05135a2e281b5344d9136be6b349307438cbd8ccccabeb864b77c1666f33c7a3acd5f5665513700157275cc8bebcc1cd7e63b6a61934ca9b3d434889ba8cc060d156fae31f4445b9b15f5e0ad863e995d46f1f5e36745b4c7a65698c9770bc2fe2aea3d521539 (by decide +kernel)

private theorem part313 : Excludes 0x200000000000040000000000000000 0x4e31ac608102208000000000009000 :=
  splitAt 1 88 0x4e31ac608102208000000000009000 part315 part314 (by decide +kernel)

private theorem part311 : Excludes 0x200000000000040000000000000000 0x4e11ac608102208000000000009000 :=
  splitAt 1 109 0x4e11ac608102208000000000009000 part313 part312 (by decide +kernel)

private theorem part309 : Excludes 0x200000000000040000000000000000 0x4e11a4608102208000000000009000 :=
  splitAt 1 99 0x4e11a4608102208000000000009000 part311 part310 (by decide +kernel)

private theorem part307 : Excludes 0x200000000000040000000000000000 0x4e10a4608102208000000000009000 :=
  splitAt 1 104 0x4e10a4608102208000000000009000 part309 part308 (by decide +kernel)

private theorem part305 : Excludes 0x200000000000040000000000000000 0x4e1024608102208000000000009000 :=
  splitAt 1 103 0x4e1024608102208000000000009000 part307 part306 (by decide +kernel)

private theorem part303 : Excludes 0x200000000000000000000000000000 0x4c1024408102000000000000000000 :=
  splitAt 2828 113 0x4c1024608102208000000000009000 part305 part304 (by decide +kernel)

private theorem part291 : Excludes 0x200000000000000000000000000000 0x4c1024408100000000000000000000 :=
  splitAt 1 73 0x4c1024408100000000000000000000 part303 part292 (by decide +kernel)

private theorem part281 : Excludes 0x200000000000000000000000000000 0x4c1024408000000000000000000000 :=
  splitAt 1 80 0x4c1024408000000000000000000000 part291 part282 (by decide +kernel)

private theorem part271 : Excludes 0x200000000000000000000000000000 0x4c1024400000000000000000000000 :=
  splitAt 1 87 0x4c1024400000000000000000000000 part281 part272 (by decide +kernel)

private theorem part263 : Excludes 0x200000000000000000000000000000 0x4c0024400000000000000000000000 :=
  splitAt 1 108 0x4c0024400000000000000000000000 part271 part264 (by decide +kernel)

private theorem part247 : Excludes 0x200000000000000000000000000000 0x4c0004400000000000000000000000 :=
  splitAt 1 101 0x4c0004400000000000000000000000 part263 part248 (by decide +kernel)

private theorem part235 : Excludes 0x200000000000000000000000000000 0x440004400000000000000000000000 :=
  splitAt 1 115 0x440004400000000000000000000000 part247 part236 (by decide +kernel)

private theorem part201 : Excludes 0x200000000000000000000000000000 0x440004000000000000000000000000 :=
  splitAt 1 94 0x440004000000000000000000000000 part235 part202 (by decide +kernel)

private theorem part173 : Excludes 0x200000000000000000000000000000 0x440000000000000000000000000000 :=
  splitAt 1 98 0x440000000000000000000000000000 part201 part174 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part320 : Excludes 0x8200400002000000000000000000 0x3e70191718e0084510620801104008 :=
  finishCode 115 0x1c0d04828130cc1a9eb250f04e14dc9c6842deebaabc794ac4c5c77a512c1b886a3a975bdda0ea5d6b3a61a62d836656d0798b0976175eba6553b6a95c3804dab29cde661154bd77f1fdd0f8fbd2f4fac4e6d0f3d7607b4d6ddd0fb06e9157e579a1f3ccccaadccdbb451a8dc9956dd09b8c852f660f04f4ed09b295a5557edbce656912c5628284db07d9ac7d7a1ef3222a97b3ccb69c13aa0b762b198a26229867d5a6f61729594684d836842bd6c2ea0b258c9c7663156842bda027345c4c994c5594ab7bc5374e6a0b58a430bb5ed4b6c1ed6edeef47539b5eb5eda8be623295429560f826d7e5f56b4f5e5993b4d8837bd0df4aefaabff37bd30d117ad7e696ed09d0bb4f97d89bad3f42eb4f05b8ad5f94e788a620f42e656a91c886b183d8564132b30baf6da7c13a13b57185e98b097d6282cbab85b52db03d71e666c95fb09b421884cacbda637156c2f60dc38eb2d8bcb4cae87b64b7bb522b6b35505421acf659da2c77620bcb5a7e87e83b45e16c37cb3d9ad4e769b6cae5022665d527709b943b17fe1c68ab6f7799b41db9e2ae6014e397569858362ad7e6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part322 : Excludes 0x8200400100000000000000000000 0x367c898498e20e41a2200490020008 :=
  finishCode 79 0x732d984aa3d1582f34bbcc5b0aa78a7ee205b6b3560f5ed6f7515a411ccf9a842c0ef02cda96c1a4c557fc606a25d25188963c29be6b96e91815ffa430baeed492536db34dedefa134adcaf94dd37d37cbfe3034afaffb0ba71d3029f36a6302bc5c78a3d08538ed4d71e98d5d54e3961964bbcf2e842f3f66366af3f60fa11e85a71b3251d86f795b802585e986d4ca6f0a63e3617b53938eccdae5ec60f5a3fa61b536f729bb8621d852a9c75a9cc3ae1994b74ae1c492dcf487598a71b0bbe6da9b0a89cc0ae24abbf70b2701c851ea0b59ea10da5b03da5cc2fa172fca1baeed69ec2ebc653686f14ddd220e84378a51220e2aed4e617601acd5a13035a7d21b45cc9d6a6f9b2c367a3032f1cbbe62b0f9f4b88f1cc596ad39affb0bd51f362d5b4f4cd6bd5e3acd4b565c5f3e31d5e303d67aa0a9c76a6c098db3d8b4ed3d38e90eb35081961 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part324 : Excludes 0x8200400000100000000000000000 0x36701b841be2084120260082080410 :=
  finishCode 119 0x6635960ac4a1e1545ffae52138eb5309b0937e3d1ca732bf882718a6d776b4fb534e39a1eb4b6f7271aa76024ed93165375a78c094dc2f373185ed947f14dd37b7b8facd4f48b32b4b8938f02d954ae4b1336b5309b5051815059b36d4c275b764f1505a6557ae50518189df8154ba3c1b346065e38af887c4687c0061fa11a30253710334c8c0e22905366034c3b74aea846a71d0bfa12baabd708ac57ccad15f2e2536bab457aeea8aaf2a9147457265658dc1697cf8fad3f545743e5394214a2e8c63b6a6d5a537276a96da9e16d683316bbe63a946e0b4c652a2a9e2e4ae0b0ca5a5fa2d315f67f088cd5aa5b493296e52c9c0181a2a4a6d4165868811814fda2065c423621f43ea496f78af0911efa21d416656b0acaa524e0dc537317a1ea7369b1f194dda0edeea72d5b14da417954995b240026db4ec27a735155f9b4f94556e6b355155399879eae5994a739f35a1c22c236cd422e08d7a3a1c54e56e6c95c9604db705a46052d63d779777f8b542356e56e650995b5b9ad4d81db8f43e0057ab6dd77f3ef6a3515539b25b05f6181871825e9266dd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part326 : Excludes 0x8200410000000000000000000000 0x3e78990c1de29a6104308208000000 :=
  finishCode 49 0x25188d0561b89fe9815fb0b422c2469848be9be584934b9cc5a848b6b73da9d32ad8f493a896481b65b9e63629b5d116da63629b5e0b6d6a663b32b317687c4de0dd5309709628ab9183d08602da6d89b29b80b69b621e60697129b1119b1ca6db666d98a6d83e6f76d9c2572291031529734caaebd85e9fb4c732b356a78bdeae8c24a25abf3a8aa4b1b269954f1b535d760fbe14dca0ae499581addced4d7e5dce505a656956b53b3f8a9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part327 : Excludes 0x8200400000000000000000000000 0x3670090519e2184100200000000000 :=
  finishCode 147 0x1c0d06426120c41a9b0339944378a59200c2f5a9b5994dc56c41b71cb0cdbb15ad6759ec43b7194dd24c7a212f6a6da72c2c2f4b0da9b7bc5225e15d6176cd6f36179b7661717d437a45ad3df1d7b57efb174c45610dec954a4023d2c2bf2133cc86f97ad4b6586505271b8138c9ff6a74b0cb0ca1770be4c0d1372e30df32652abf34c9aeee17d69f15a22b2c364d42b1d8132bd74e73d8d99d7c5f9a3d9ec696e96705b9939950999e9136d7b531da7c40e8391ca7edc1776b4f97d7b1804e5cf5188ac7329b6977601b534ff601ad4e5dca56987967973ed4d7ac3d6b417cf9953214fdb53aa59291585f9329ad4e5c54b665696b95b5b985e68fea3d89b517a65629746a3b10ddb36655b7659e9734b9b5322f057b42cc765454b6b534379956e4ca84dd6a66434ab5a5b00e22e1846c993f69550de98d4b50de601c2f938d4144bed4d0dec9486d3975f426a4ba6d4fd4e3ad4e6262073970b66229b699360f51553964531cde6f86bf367b0a8be3d1eb0aafcc9fb21bd6310dcf366b79944b6ecdd3379dc2a8f47aba8fd08c26d80583e88c2b44184bb0ad66b148e4a1bde89924d0836a4c6cbcaa0b66b2f2c56ccab7bd32b156bc942f2cc9d0de846eeb0df440cc6a11cf9adef28423b61e8cba32ba11f4aedb3148c59ac11767b598c4caebcbaf5a9cbbdb34011b37ba1ba8aa96d718068996c961509b5d1a65423e2ad776437 (by decide +kernel)

private theorem part325 : Excludes 0x8200400000000000000000000000 0x3670090419e2184100200000000000 :=
  splitAt 1 88 0x3670090419e2184100200000000000 part327 part326 (by decide +kernel)

private theorem part323 : Excludes 0x8200400000000000000000000000 0x3670090419e2084100200000000000 :=
  splitAt 1 68 0x3670090419e2084100200000000000 part325 part324 (by decide +kernel)

private theorem part321 : Excludes 0x8200400000000000000000000000 0x3670090418e2084100200000000000 :=
  splitAt 1 80 0x3670090418e2084100200000000000 part323 part322 (by decide +kernel)

private theorem part319 : Excludes 0x8200400000000000000000000000 0x3670090418e0084100200000000000 :=
  splitAt 1 73 0x3670090418e0084100200000000000 part321 part320 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part329 : Excludes 0x88200000000000000000000000000 0x77591dc51040000000000000000000 :=
  finishCode 41 0x33158d467068e5174a6226da9d32a8832b75a9cb8af6caec67e8728af28ea12c11ec1370b25726015f2834b95facd6266d4d75460e256b499416ec46f30265332a87299b5a9cca994a71c8ae6a6f018385fa6062362a5836d4e6568a14b99899448260c2f6a74caaeacc5842ccad3128734cada9c9db48b13332b2b744dc56b79a26a8e8d1ca33815b5a99a9af2a1ca2adc14d60ad3536f3823696e78b5e5353455 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part331 : Excludes 0x8220000000000000000000000000 0x3c348b4c5054440000000000000000 :=
  finishCode 105 0x2e188dc6634190ec52069d80645518f347ba5902ae9895f144d4559e35cd316883a16a12a73147291cc4a9ccbab32b0c19bc21a2bdf25485b9df0daf2b7279a91d9fc1f27770f360ba054c89a8ab485f38c9db5e57eb299f257ad485855d068f0c16f85fdbdec09735a9e13d9fd34b6baf68bfccacba384edaf8430bc854d8291546f717b6018a1e2ae4f77b19154a37413c6b790e5bdd485f184f10e88dda983da8b80fd68384ebaf6a6c2a0fe10f443cc6af2b7bb07d934154455a40559a1d316daf31703fd22d364df18b6d76f74118bbdae57c5b5e24f17f0ab441b7164a4349c4d251abf214ac0f60c85a4d836f62bd6be251b14995a57c526d4d0bc1aeb533159dee9b66545357aed4ec14828d8b5a2bd38d7549a5756895a792bf433da99a9aff93dc82813171279a99f1da169d649f6a69734cad99cc5852d22a9c4c8430a1e80dcebbf45ada9c57da9d6672efcc5b6be234068f147594b63a1c840d1433e38afda9a17848d6a668edce4eb6a7599af6c569a3b7bb63e22c1c47b19104a341deb43895b2f8af6173299ae46aed4d426cbe4e39957a328db53329 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part335 : Excludes 0x8200008000040040000000000000 0x3c106b641241209009248009200049 :=
  finishCode 49 0x38158922f3416a790b06a062e19b4418d0e2142ce1a75f989ac5fe08fc4673416cb0290a26d65ec2ef935a4a21be4c5f6de63571c6d9977e624c7423c9d660da64e60dd0623503170cd9a1d15ad672fda939a9ca8d69b67a4eba0a04d200dba11b00ca2093db79da4c3566a735ecbc715b29ab07e8338c2b20c859a21d6063e32b26560d5e39b660b1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part336 : Excludes 0x8200008000040000000000000000 0x3c1069641241209049248009200049 :=
  finishCode 145 0x10848e0100e85d624888ce5a9e8311d8b0221b0bcd9a11ede620b51fcc5da4d24a9cc50d49311e33785f450a17c47c41856087607823db0ec8580fee995c2117f18bb4da5ac2cd0668859815f960fc46822b634397d18bb3585fc2c5b0e5f9995d040171e4556c3425995823653560f8067228618f44d607b4fa65570578e17f0b1e06d2b12444582d4e81009a376c11edc79c42f94e5b0e17794e5835b668a16177c99ab510f39d8d05838888336ea2a9a1cde6dba34f356941f1358c02bbf299d9fd4a3047b79ca47652a5adbb0bff134188d40c5cdc633715b1a9a93c6a65034cab66cde6163a0c46722864414551abacbe21b88f5035d7b396a609f4aac50b008bfda0ce0c7cc028875861789de57c63d78ec2dacfd77d3c580741b4e0713b19cc464371641ab0b3ad4e2b665510d836995441915510e6ad441924bec85f11f6a685f433b06a819a9c84ad67906179b8c66db0e4fdb4d521601b53b86a2c068736e8c58cd8d3c1671a1c4bd686f936a6657212a21e42c0bf330ae0f8c78cdccad6932ea356bf34a8b07da9c72e1c0e244307e60f615b0303e16cb72fa7278d82cd60b1b4d9e5d77db6631d08d0b16d99826d4ca060b1 (by decide +kernel)

private theorem part334 : Excludes 0x8200008000040000000000000000 0x3c1069641241209009248009200049 :=
  splitAt 1 54 0x3c1069641241209009248009200049 part336 part335 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part338 : Excludes 0x8200008000000040000000000000 0x3c106b641241249001048009200008 :=
  finishCode 73 0x341c0ac49179b4b53e25822130c41a9d9fc4d6dbb30aa17b79a20cbe33768c5c40a0d856b4d95107fa559958c76d36c068730b8c18d3c1679018786ac9aec46a2e1d8ce0d398ed6634df49268ea432eb047944842a90c33765f3e09a38d5e7185e44360d9b0e802cf376b6183bcc2f88d40c5c336687456afcca4ed666a740804d2d3e99501944127b6ed6f34419b0c9eca4cd4e8f628f8ad1abb2f93f578eb19cda5811065f14550b3b09e2365cd85662d10db1e18f0b3347323a62583463f388832f1a2ac42d15abc788ac4a35868e50f299b6b847c2ff10b53275a25e64ecd6c210b1a6981cc2c62b581e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part341 : Excludes 0x8200008000000000008040000000 0x3c1069761249249241240001209008 :=
  finishCode 51 0x1c0ac49179c4b53d0583699cec4411566566ed9933539959bb69be7c1a6d0b36b3a6d862dacd06617718b993ad369b4a4c2cf43e97d5d7995601b0523402ff67f0d3b79b6ecb5cf5f0fc8588ac847d2d6167a0b0502211834395f85cda0e7d36c38a108f864d83657e8b55eb19b443869c21e347d062350167371a2a8c58cdb79c16668732b2f8ad9b71d33d67e2d6a666372fb88ce2f5cdba51e8aade70a7c558d5b03cd8684b006f79094d1d81dade31d8ab3470b1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part342 : Excludes 0x8200008000000000000040000000 0x3c1069661241249241248001008008 :=
  finishCode 143 0x242588422be0685ed341c4ce7627988dc221da4cb76a1332a5333272f5d32685e9f3534ccaa2ae21bdea61b2f52360119b5c79854d4e4a99956cd6f3b05009d63436f36dd31d9af423e52db5331de2303d32b327610e13be09a3e705de601177b3816330398ec636b8369f32a2ffb4d0763899cc45802ce99544d455443a6546add99042f86797ad4457ae6c35c7607a23f80d474caa9a9a9b79ae3c60684b60a04a225e8ad0896091838719bcdb757c6b3531db53b539b5c69f1169b5978bb8cdaf5d0cec0f88ac710d1df266019950479f26d3583e607a51301ab8d1c5de6567b5277347995983e64d09b4d0bec5838928804f33884b85f4ca8b9b61c47da9cc1b32b885b99acd154c3e6e35c753560d8a26655134d4eb53995455b850069e3430b39ace5fb80712606b531ab42fb53869cd1e606b531ab443c82fcc336dc7447afcf02c11819b3f7a64cd1cbf6b2f77979fa6f12998186ae28614118fe06d3b19ce262299a8455347aca510c6ad10e9950b3a65510d605270a7c33c47da9cdc685f60a0551a9e3436bd6f36b396e6d342cdaf60b30099046d26d3469cd0e6f34256b3c85a4cbe2dc63376872e3a7e8b9f628068e35663b5a9cca98ec3376d1ea634742544d0b39704d1f42e22b (by decide +kernel)

private theorem part340 : Excludes 0x8200008000000000000040000000 0x3c1069661241249241240001008008 :=
  splitAt 1 39 0x3c1069661241249241240001008008 part342 part341 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part344 : Excludes 0x8200008000000000009000000000 0x3c10697c1249249049040241201200 :=
  finishCode 41 0x341c0b062351d8e26d2c94cc822ab0bd6a63566a6dc7455b5cb74944a54d15602a033852512d8651edc70a3a208d5b00c68f6a6dae356d733799a1da98d3a73d326dcf6a6c023379045797edbccd0d13688371cc9d67ec2adda6a6527303b76e202ceb535391a7993ad06d35a24a4ed4ec140ce0c7b74c166d6f617d25b7483fcf76d6e16731330ae22516a70588bb9a3cf17ee8ab275955797ad356b6d4c2c5856 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part345 : Excludes 0x8200008000000000001000000000 0x3c10696c1241249049048041200200 :=
  finishCode 163 0xb4962108af41a17b4ec712c19cb2456c5376a689a8ab1472f1a20d6320657361b06da9c512dbb35caf1b74da9d0ca166f2653288760b82f8c166dba6876a7059d6a6f1b291da9b008cde42c0c03373b748c18cdb00c21b450d97b74ca35868e2ff5a9a99b7b858d6a7c45df94cd75cfaed0703b170dc713699cc85806ae2b6517353b43a2d53cd4e5745856b5328f443d0f8f84ba456cd1c6adb0db8d83e9756d7b533471ab0b3939da2469ed4eb0be3059b59da9af1cddb2218d5da999bd6a633748ce1a3843c4bac1ea2a497212a21cbc7ac347e2288cbcb6a6a66b6b5a9858d6a684b0685ed311d8ce642e1c4b2226c8ab5860d862d10618382ccd0d85e6b36e344d94551072082336eaf1b71d6a6a5b5a9e14b598cde41b8ed4e86735388faca617718bc45c3509cf03bd94a918d3c47d6a61676530d5d2bc47da9da9db4e056248bcc85a9ee2c034e8832fdc56859d8373769a1b59d31c51388ec0d5c886337290a17cd1adda5de48b11f880b39b7466cd4e6ed8676b35f1c81a9cdda3560ef2dcb61a12e7178e44d425b0a4caf21c019b86acd1ec2918f6c7acbc5deca781a1758d04917988b53c86a17c64556b318b1ab6b3a5f62b69b64e727d989a9b5bce3148c42dcc2ee66eb73045b79c9fa35696b37b8d5e20d2e97d19b5f18d4dbb581e347d0361c84ac1e356c1f37bd2231103475e3a2b5bdec299b5e8fe5e3 (by decide +kernel)

private theorem part343 : Excludes 0x8200008000000000000000000000 0x3c1069441041249041040041000000 :=
  splitAt 2673 39 0x3c10696c1241249049040041200200 part345 part344 (by decide +kernel)

private theorem part339 : Excludes 0x8200008000000000000000000000 0x3c1069441041249041040001000000 :=
  splitAt 1 30 0x3c1069441041249041040001000000 part343 part340 (by decide +kernel)

private theorem part337 : Excludes 0x8200008000000000000000000000 0x3c1069441041249001040001000000 :=
  splitAt 1 54 0x3c1069441041249001040001000000 part339 part338 (by decide +kernel)

private theorem part333 : Excludes 0x8200008000000000000000000000 0x3c1069441041209001040001000000 :=
  splitAt 1 66 0x3c1069441041209001040001000000 part337 part334 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part347 : Excludes 0x8200000100000000000000000000 0x3c1ca9c490400200a2000410000008 :=
  finishCode 119 0x703b1c4dc6831190c20d5d90a6c6065e5b536e70ad6d9a9be926d4db9d806295da5d2d4ca3db1e443457b2fa58153597b00b07d31086c2fb2f33fa618b50a3879b2f97e6917052997e581f202eb594a5caeba82da9a94da9cbd727ca7e949e42c16c97182c57954cca1d46e61553598d979583d4442a64f1615b2682908aa14b294af8cb66a3a16329aa20d70ba6e21816234f4c14d6c99b656b698d8b4709deaed4dd96a6162d7b684cc6b6ccc6c34f582d4d4262758ad509b1190cc56308337480b34e3ad4db9d486b2fa49b53d0d9b5e5ded3583f087734aaa71cbea6abc5b7b859a8acb0d326bbadeedb364c24302b5b9eb536b918152160f828e5e5615b53b090c74054a8a99bd67a9c72c2deef3f4bbda98c0cdaf30ec0365f69b597cbbda9b6b851b00d225f6c290a55f9607ba4b330302bc730baf5da132fa9aba135a9af1d97d6cc8592c115b28a856858d229261816076150b3945768f4a628ad8178e005d077cf441a45a1cbbb85b2b6def2eef9ed174b9bc3cad9a3da172c265359ecb09a3af8a209a3d65328ab07854d2177742687ba4fa693475f9b04f185eb4f5e344d2fd840cc7578c0261e94430f9c2d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part349 : Excludes 0x8200000002000000000000000000 0x3c1039579140000400420800104000 :=
  finishCode 73 0x341c0d462331580af862c66fb08ab0d5c4228c1e6a6d73443c4accac43d2cfa1a1676d2019cec14cc89a6a68ab106dd9855bccd4c2b66eda57d49cd4e21e6dd3534570ad34b82b739b8a47617e581d086d0b8672935296ed8d2e2052784359ecbecc99a9af8cddabff4caad9a8e851a12da12d872bea4e69774be051c15e89b4aaa97d2aa4fb74b66d02b4fb6c2f4e35bb99560145752f18f827c5ee5f95d5863f117cb67002c6386431e2bccda6e83a75940a9ae0dd4b646ea6732a2ff31704db00eb2312051b860bfd9ad84315384f04bcf0268e12f30abe9d5240c2ac017fb35b09ed3e2b7086b4fb09c15c25d37e967601826d85581e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part351 : Excludes 0x18200000000040000000000000000 0x7e502f76b3c20000280080083000c1 :=
  finishCode 17 0x2d960ac6d027c2a61be615a55b298ad5396158947414c8719ea45f42bd15e8f6a6342551517daf9317594b0aa8a8598c0d31d32aa72c2b488af85ed7e49de89b443 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part353 : Excludes 0x8200004000040000000000000000 0x3f3429649352882808418008200043 :=
  finishCode 29 0xce623b164d0533208aa3573e4cc694cbd7c51e88714c8d5ee298c1ef5f0c0943c10f31abaea6b220c53384be5916e697160f0b35e39b666155155dd8d4e636c8da7539c3daf1949afcb03c4ad0be4d30cf142527706998775eee21d475bb4d4ed0e50f1ab (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part354 : Excludes 0x8200000000040000000000000000 0x3d102964d342000008008008200041 :=
  finishCode 171 0xf05e682d4fb1c4da672c0be3220a2adc22bea6f7bd539295283c86a06ae29b8b5a6569253b5ebeb80d5cc2e3066a7a17457b79b5cc4cb04d90d2e09f27dcc5806ac18ea49995421183421a5ce2be4e722f17bb86a17ee18b1a761782be410c5df5fb8af9426d0e86284d0db15f6874ade4330b934a8b008598cdd821964b933b0ad3537d392e583d4e65f960f9e4b8d66331b6822ca12e303b80b1981d8045fec210a9d062339d8e2592e088689a1235a1941a7fbd2a9cbd2c35688314cdc2c0bff0c18d3ca732098baca577d826d90c275a3fa5c6985426cbe2cb1819717c99a35b35f2697d4ff177539cc304c306c1b700a78d4dbce093b204cc13ea07134d3025e08f18187398245de635c9a04b9c86235170b04bbcc2e3163374c1a74ffaca628c97e2064ff60986aec164b8057c13eba3594afdcaec6a6a73316ba3284cc5a9cd82e185f1a9b0b8faa1084fafdd85f2ddc51dc290c2b447852b00947cbaf447cb8bbd8c0d82e0b673038548c0cf5ebf76670c0cc698091a01efd0bb8642c1a86b983cc07e6342bc62c66d4e66c318309f539869ed268a15396010a9c84aed11ec12ba235765f5806067af51b0a998dae1a0dc76321601a7539860c27de4e8b5455a1e49f42a619b17da63460db4ec0c2b1748bb8bf854ad6cc1e12390b0594c356bf716b3d2d948d5ae8994c123a0c85c2c1a898d82bd85c62c66d85e18309f09194e469c2660911abb86d142e52327d860580575e793003443b43455b05b175ea430a995f825de9695f (by decide +kernel)

private theorem part352 : Excludes 0x8200000000040000000000000000 0x3d1029649342000008008008200041 :=
  splitAt 1 86 0x3d1029649342000008008008200041 part354 part353 (by decide +kernel)

private theorem part350 : Excludes 0x8200000000000000000000000000 0x3c1029449142000000000000000000 :=
  splitAt 2828 112 0x3c1029649342000008008008200041 part352 part351 (by decide +kernel)

private theorem part348 : Excludes 0x8200000000000000000000000000 0x3c1029449140000000000000000000 :=
  splitAt 1 73 0x3c1029449140000000000000000000 part350 part349 (by decide +kernel)

private theorem part346 : Excludes 0x8200000000000000000000000000 0x3c1029449040000000000000000000 :=
  splitAt 1 80 0x3c1029449040000000000000000000 part348 part347 (by decide +kernel)

private theorem part332 : Excludes 0x8200000000000000000000000000 0x3c1029441040000000000000000000 :=
  splitAt 1 87 0x3c1029441040000000000000000000 part346 part333 (by decide +kernel)

private theorem part330 : Excludes 0x8200000000000000000000000000 0x3c1009441040000000000000000000 :=
  splitAt 1 101 0x3c1009441040000000000000000000 part332 part331 (by decide +kernel)

private theorem part328 : Excludes 0x8200000000000000000000000000 0x341009441040000000000000000000 :=
  splitAt 1 115 0x341009441040000000000000000000 part330 part329 (by decide +kernel)

private theorem part318 : Excludes 0x8200000000000000000000000000 0x341009041040000000000000000000 :=
  splitAt 1 94 0x341009041040000000000000000000 part328 part319 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part357 : Excludes 0x18000008000000000000000000000 0x76565f00000500c003000001000000 :=
  finishCode 183 0x6d35994d05f2b017f70a453063ec974277347985d756007c2db499957cd347617a5a708cd1f0b5a9e62e6b5c2f995617a63209c53ce985617ad3ccae5cf0b6626c2d7b56178c5d309660d33f6096a596ae62f06d387094cfed0e6a5609c2596fb25d2096c3456f5a8ee92ecbf0bf07df3ddd6a4b88456cdb640707e8148f8e12cbcba22132adeb437c55e84d048c442da1aefe9c6826f572e0c3e384b2f2db6497263be7af1ccad92a178ac21cdc29be7854ff34753918fba45ad84ad6e89ad04e36d987bf0944ce6254266d97859baf09538d136a924b8531cf7a68aa7360a64510de62e77304d99504d9b1f08c13e6b7c23995c239a95adf09698b52fc23975e1bdb66656e15478594e581ccfe7bd7a4568acc4070e28965eb83f4cac38a25c939808b2eeccabdea1ba8aa9ca20cf9e4bb68975b09538e5d6b442219006e76f77bd97cc1e5bd5eecd165d154241b5c0de6c56094e3995ac2e8da1668ec12233614b52aebb62c11b569957ab995a0960ac4cac4bab2adb3312c13707bb9bd575e3057bba625b6662eb4d6d9b82ebbccd2c732abe732b352aefa70d22313c347a20c7c89ac12c2ef6b0f4cbae0fd37af6d31cdcb2f329b749e54185ea3f5094576b59bdf06585e95d42548e44b94d6d7a8154ce4a6ca46a72b05f181f585d3cd85e7d5871985e65742607f5f1617d04f1f3e6eb18f4e343944d0b79156d158b35b06d7966545fc2c4d1d81e9799807416cce652b0177506b7985539db9463e10d6b5a4e14b74e179a3b0ac833179b5a8aee0fe14b7a92bce30be145c256b56f5615419347a0598c5e72ea48f8469ce31ebcb35de11d62c831f4774b993b995d69f32a90724caae0d686dd74d6db360fcb1da1c0231086803b83ce84cdd6d6f08ce84b62da1c0021e34d384a826dea64b5a1b62b7ada4cb2b49a4532f2deb05dd6211a134c5ccab6baf9b7b9a3e71b660b1a51a5cdb145ff0a6a4db4fa514136f50b1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part360 : Excludes 0x28100008000000000000000000000 0x7d725fa2141940a405020001000000 :=
  finishCode 53 0xaa6b281689e218a22db09467c127508da1c6cc6cd693e95db4d6a7b535ada53959ac4125160b62f6b0bda3c4eb2baf571575a9c52c01a91097398b7bdacadf3c935f4ed07a697bd820e57577eb2b7af8b396b6d1d77ed944275b4f821f41c92d836d1e95dd0bad4df4e575836cd5894d3526da396692593ac56925c4eb12fa8b0613d6a6def67f49e1624eb4c863ded2e6db2d534d34b9da9ad6cbf75e2501631170bfd9ac9bf69f123046c59d9fa0eda2d3671a86d78d1d82631fc2d9bde94601f8adb4fa4f60d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part362 : Excludes 0x8100008100000000000000000000 0x7f72cbd2040b42850b020409020408 :=
  finishCode 41 0x35154b64f35990a6143a317ce88b5df95db538b3a69699945a25766d995f9ef53c65cd7cd3c65df347a245807114c5436cb73b4ad6a711769b4c9cd0b85385f6a713e9e33274acda7b4ce0fe14d34a78940cc0ec0f30ac01e2e891347989b3d607615c85100be3475d15fb6d560fa9a4d1d77e1f68a5d0bb3dd65d25149ebbed6b3deb7bd29c1636a6217364da6af2837b7ba88da9cd6abcadca68f54c2f9bd62ce2442c4d56d4e6f55df (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part364 : Excludes 0x8100088000000000000000000000 0x7f566b820d59c0c503021111000000 :=
  finishCode 33 0x35990b05e1e06b536d54e3b4d8718abb4f347445527535aa59ed15b69f166877105ed8936cd62b6cd6b4db4fa67944583d0ef39707244181e64eb4d60fbc5a2c5f367afa611f59fda3b07cfa778031acd5f4ed3608da85122011b4d361483dda78b9ae3d167030d9aa7cd69b6a71431361586facf62b45aeb35 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part366 : Excludes 0x8100008000200000000000000000 0x7f526f0e1549408449030409001060 :=
  finishCode 91 0x1a8ce441e8bc4e39b9ed4d75d7961154bc3008f7c9c6876f3ad9250e8774a108e15f6f7b05d2d366c9b474234e39bae6c928790ed80759087c320d1d5168f0b5c37b5bb6bdc0efe97d86fb47a6fa1bed1e16b86fb0211c9c76a62eef77534a71da9b7bbb10ed6c608f6d95b190645ae6151779442358dcf37bde2d166072813478b3981ecd6c190a619eed81d0eca05f0b57107ae3d9eda6c092f5edb3582f130281d6281d69ad92a6b67b275834c002d9368f6a72c766aacb35607883db253c57eeb47aa364c45cc0e047288e16aefb6ada9d52d4ed0750f53543b4456f7ae130824a2a82fef4b4beb7aa228afd6a6e4b4da2cc2c5b965af5967b437caaaefa5ed4b684767b0df2ab59a8bfe721be951b535bb7abad4ee99ca655108ed4e7c968931f43bb4d9a24c7d77d38ec2db533e7a1becd4fb583585f06eb534e3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part367 : Excludes 0x8100008000000000000000000000 0x7f524b0a0509608401020001000000 :=
  finishCode 171 0xbc924cad61e0e4b53c86d1092d7143afdb5ab62eb2a9a84453558a1cd560179e5db25b55ef57448164237971357bd6d54f79065bd511669b4b4b97cf43e5cc1fcd55d94c14da519a5662707dbddf4ed0f973a93583c5df38c1f3e0cb9d14b85e42fa1edcf54da641a088ad532fdb009aac4fb00c6ab34615821d6c738c1f3e09a3da1f528b73a22af2cf2ef7abbfb4ca553386ab90b4140a22cdef2bf362af9b0acf82be695f68799bb73a22eb2f9345dfa679ef54454a5aa6d0fa516c95b1b42e25dae5bdd745796d0b0b1aa6434260276d58b35c37c95fb43b9c4c5c0fef5f373cb9da6cbbf7c842229f4d65ad2a68edcf4a32f9afcd32668ed2b70ce1aad0fa88abe6c1f34d0f9b9d114d55b9ed0f445355aa9acda5e1a8bf650f2fb3d2c4bd288b35d1a5f662d81e9935d199391157cef00e7058940b03d2fb167ac871a9cd6c65ad7457ecf0e9857998970b1d6552f970d4222e23394c88373bb270db2c2b4569aad66af935a6d9acfa738087a295f058570a68b3a3fa617c1d0fad1f0bcd1c20e27db9e8910b3d85ccd5664da665c7b47355b4d313ad3648fa71aac41cf93a843b6e794cd75624b3558839462225e7c90873477c1d44b9ca06c0e6ab1aac50f69af93a87237bd8200c8b3d83ce5653de25d49ed3599746c9b3da90ed1e9ce25d7457b625e5b11e953396ba2aeb4d0b16c92278f0d445e05a95b56606d360160b3da25e9cd49ed1ed07511227d0f0758abacf5b2db267128820afe16cbbed4b69af9a0df32718fda6da6d2aa0eb15b69b616d524910355951acc620c92ca05bd5b6ed36a45c1b5b94e3b4b281d4390a0660768d8d1f43d854a0627ed3697d8971778ad883c05ae2b696b31b86fa5ae2ac2c53aeb4d6d5a73871 (by decide +kernel)

private theorem part365 : Excludes 0x8100008000000000000000000000 0x7f524b0a0509408401020001000000 :=
  splitAt 1 69 0x7f524b0a0509408401020001000000 part367 part366 (by decide +kernel)

private theorem part363 : Excludes 0x8100008000000000000000000000 0x7f524b020509408401020001000000 :=
  splitAt 1 91 0x7f524b020509408401020001000000 part365 part364 (by decide +kernel)

private theorem part361 : Excludes 0x8100008000000000000000000000 0x7f524b020409408401020001000000 :=
  splitAt 1 80 0x7f524b020409408401020001000000 part363 part362 (by decide +kernel)

private theorem part359 : Excludes 0x8100008000000000000000000000 0x7d524b020409408401020001000000 :=
  splitAt 1 113 0x7d524b020409408401020001000000 part361 part360 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part369 : Excludes 0xa000008000000000000000000000 0x375f4d540001128001400001000000 :=
  finishCode 99 0x19019b868f39489c472584fb307b0ab91d12a24fabf36a7081cc0a0c9a3d6a6e84f9a655065f4db1eb140879ad4ddec9f5dee87996c610e88c35bb63cc9cfab317597da9c68f65f692c03597d01d158995965f11947f4c9a7393ec52c3eaf9c9cf37bcb9cd2d4d3e6b4b7d33157d393e6a69993ac651e84fb4c3598a73da0be1e87d6629cf6833272c5f3a1f6d4e5ccc5604bb53b4b77b955b43e64e58db35a9af9b93294a75a9cc9d29d6a6b635a9b63d02f91cac2b09f6986993b475eb207ad268fed1df25f4d58e87b75eb4f9a2d66566167d39a0e77ba6b97527db45a8fdf4e655c89c7002cbac50d35af5dd1b111b2eb3bdc5aa7ccb636a784b2bf652993427d484bcae0d32b30a627a1f534a7cb74cc29f3da1e2b732adce90782e0d2ba626d074a6f8ac2e0da16d2b692d06f3e9cf67b4caae0cc5cb835898292cbc5df43e79fd0706d855539da0f43de367d5683b492e19a0cfccc96d2491743c5de (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part371 : Excludes 0x28000008000000000000000000000 0x3d335d00001100a005000001000000 :=
  finishCode 183 0x6e3b1a8bc65069ea817fa0f356bd2da9b5b93ab6bd285d59e2d835b9db1ed4eaa5d2c11494376b79c9270dd3455841844d29c7aa6876a60fb4c2def43be12a979a19a1d0ef7070411b4df36891877b09ecfcfed455b9849558b3c12ed369bcbe6295b25455b26c25a6f34388b8b7e64ed34d0ecadb9e6d30bfb8612296c27b5352d5399403ecb5b4de11e4be9ff7cb3fb53a1de2cc44e2fb03f5ada62ed4c2ff086875a684685fd98d6a668686370b4db643359105627fd229bcd0e07d6f7b2bad1e6f725fb479ba42fe9beb4f3433f7ad2da8def709db5d3fc2fe4ff86fa9bcbeed4c2fee1408054338687846bda5ad4b5bcc2d548e293c6ed6f388b860e5f622e1837c1acfe1dde9460f43e04f6898ad4451836c36d3ce553096a722285aa91ca2d367a9b4dad364ffc2585262ced4dacf09288229792fd116c2e9e7442a22c56c88b049427fc4bebf73cec45d9f8c1cdbb31f682a05ae12d6a765f456e84bc5cc7d9fbddb0bd285c5a9cbaa10f306da9a84d85b15b6a778d45c2f8337400bf5fba5e53fd7eeb3f6176b3af9280bfd0fad4d755b9db1ed4eb539b1dacee1689405ad98d16765ec2e9ff00b3f5fba615e2e27db4ed4e6bd79d89f617a78fa75a9b0bb59c9ff37985fe533970c230bc16a17af05d1a555bdd046d4cd0ec11494376b79d34c3070fb25dcbed27da6cba31670eefa6316d5312cc3e847af8d6a617b506b3b41a1cde6316687379b79d6a740a44a062ea94c864c5c09b696dd20fedcea85b1823e62db5df114b612847923da6d0fb6974a211f16735bcc4da9d14b529da9cf1d0c4b455dfb539a4c884545ebdf4c1a64e3b5388596da2d2ac6876a759fcc4d9fd4db6a784f69b3ca4552504eb0c87da5cdbdf084204c5687db4bb53c27b539046b53c27973977c5270869ae4e3b53c27 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part373 : Excludes 0x8000018000000000000000000000 0x773bc902400302800500000f000000 :=
  finishCode 115 0x194c46e399a8be5d0a6ca3cd1e4436a735d6c7ad4ef1841abb539ade654d754e6d4e8a3b8551c06ea2874c0ccada9bdeaf9cc2adaf4aa88bcbee12bdeda9aebc00ed2f84a22f32b6a66db54ba4c0d4af166a466aa6db28be291e0cc7af6874df6a6876f033e4cafcc5e86cf274daa1287740b8392d4ca0c1e6a5388f96b6f56eba616a716b014e0d83bd378afe12ca29bec1b8b54395d1ad0da25a26101c25a49283b53c25c02fea016a9c7594caabddb75caac4e29c7687816da1ccada49b68d1d84d45402f6694035dc23910e23c965e9623e07d88d6e9a57510df0623e2d4d76b4d8b3a656d4c1ecd54db6d4e88fc25c2886eb6835d8830ac0f661f327005f9a2d5a56d07b3fb478a19a553e65f9b4d0338a4d416d34d77712c615ad3580664e2f3b3f5f9b53b3fa23f1170aa4a371841aba0451c036dcf3136a732aa4769aa733ca421cb03cd6f6a75a9d6a7451cf1608870fb35db72cc4aefc51d32191435a9b74e86cdcb5a4e11e13d1ecb9993cf16dab16b2eb69b49b684c45be9ccab62b7ada98d5da9c3572bf5a9819c46cc5b738d5d02d1b8b8218c701fe14d995b536078a3a656d4c54e8a3995b53485a3d3160ff0f32e6d336a6dab32b28b53b4ba5ce9341ff426a3da4d9958176cfed36d4e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part375 : Excludes 0x8020008000000000000000000000 0x3f3749494013048011004001000000 :=
  finishCode 63 0x64371d8d60d5d22818480146e11cf6ad276a66b69ef0c73d8b52b06b06d6a66b651b60fb0bda99add6a688a51a503275c52da99addc3106b6a434598cdadcd4a711ec2f6a73caa4a09a743698f94da4dc1fa53b5360915dad4e536b539855ed693aa86b73c7a3ad4d85c9eec967f535da9b5ab72a20d6a6fab375b55da9d42799cba44223d0bd135a4ec294e37d5b4597e6566286d4e9954394e376687d4a2f1b2ba2eefaa84ae8d0f9a4ed3665620f0a6b53177313a038270d27886d7ad366551569b6995b53995a5741de78d995b53455b53b394074622d4e656d368ab6b96f77af95da62d7ada4e7d5b4d4fd539b53a5d698bb53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part377 : Excludes 0x8000208000000000000000000000 0x377369050249009001041041000000 :=
  finishCode 157 0xa8422809c770c41b5df3b0a5f144b0aca5ef273e9b51cca847d6a732b001ab9954399a8e2b6c862066eb531ab535a1de2cdad5bd6d4dba6b495c728fb53b8642812ab12cda99419a99b5e2066e1ab293a1de2ced4ef9887c141a7fca171676a743ecc9cb8f6a60934cad9ab51af2656293b53ce6a306689798bb43b3d6a325d299823c9c7aed12ee68776860734afd37bceb51da4cbaab62d46cc5a3621188225ec5e35132b1448d1af2536695271283b53995e65a6d49283a88b2ab138cc9d621de26b4f38912898b38a3dd0c023376a73ceda5d4c3327a8995804a8d48a1f2c0e88b4a8d22d6a68633276c201a0643b0e8d44caf32d3603d29b4311ab503868e25e8add45525462955eb1a3b0be88596bb43866c226b416a3995c8760a4eb2f2958b3ad4ed4eec27cc20f0ee51ec0f502d990e65f2a9180879a8e2b46ae65511581eb53995c1ba5aca6c66e29923b9ad6d4e65664e539b539951ab82ff205275a985fda9dd8c86235017f2eacca8cd8d5af1a8e6b5445b53995744c9cf0a83a88b15715b303138941d03516a732a4f74beb03bcbd3276a750264e539b53995b53b116a74cab748cdcf2cbe99597d5dd97940b6552657217cd4218c3ec356b836a6c0f29b3e7c598d5cbbb2a3351d36a9cda9da9dd84f99a8e22ca3c2feb5326bc258a4c6aed4ef1d8b8351d84b2d6347a850386ae2b619bb09602b8ab445 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part378 : Excludes 0x8000008000000000000000000000 0x373369210001008001000001000000 :=
  finishCode 173 0xc2642e17c37337bce4402d578e99529397d99580965d578d78e6f399502301f1ab6172939b0ea9449e1b6c0183585e5767b5973e63d8d4def6a10f0d5d84b67a29ad7ba173172bb6a732b7cbc7602f534e5336d39b4e5edb4f0bfa61975e1becd6655135b4f3910be21bb59cbdad6759ac3c7a161e36a6896d6617e3572f6be1b59cd281448a1aec0294e42f9956e35a623b158b35a2b6654a24a3e8ab6dd87da2cdb754bc9ae656656a6b9936ddc44caf621c696f5b1457b3fa6169bd68c9ada664e33f779f96f80383b0da6b634c9af5afca2abcfd3270df297a71b0aa2aafce21ec628fb47acff43ed3f0970a53e664f119cbc371c8aa89b7095facd5b4ca3e714df353e0fda7c37c41b71cb6336ed2acca944b69da6cda685f4aca269aed01c100ec361d42d1e995b4d28944d425993a8f69a6d4e6554e6a6b995ec6a33968f4c9947e22d168f64e389134789185cf0be64e52f4ff8cde656925e75f054e69932b220a2a947c03f85ea47505862223e58a428aed13529d2bc3ec59b63d4a76a72e3cc9cf3112c4576f7a92538e95e1f62ced8b8f26cd37d29d6a6f176a72e3cc9e17d14251f0c76a69fb617d34da6da9e42a140ce1b1c92f086e3570aeb6ea2bc47af9d32a52adbb64ac22be84cda6bdabe714a8f0cc2f32b2fb54ac369d925e6a4d6dd283a6b86ad7b50c696398f96c481d38d4a711d8295a23d15d106510fb4c7af2da9b0bc47cb1c336bf78475a6cc9e12a99de2f958d4612d2fb832dc6a6a33764824a3109ab5a9b04b0b926941b0bc9db326f9a507359cb1afdb71c5076a74c9d37a79b0b80fc052a6a346347359d62f8f33431da6e12b6eb71935ca8d69ad6652b30ab6ed42011488f5f99b1e64e19e655b8d7e6c450115d7ceb4d995b534ffa49a64f0a627ed4d7ce993d43d299e4f9b535f3c1fa534a3f066d36656b53 (by decide +kernel)

private theorem part376 : Excludes 0x8000008000000000000000000000 0x373369010001008001000001000000 :=
  splitAt 1 93 0x373369010001008001000001000000 part378 part377 (by decide +kernel)

private theorem part374 : Excludes 0x8000008000000000000000000000 0x373349010001008001000001000000 :=
  splitAt 1 101 0x373349010001008001000001000000 part376 part375 (by decide +kernel)

private theorem part372 : Excludes 0x8000008000000000000000000000 0x373349000001008001000001000000 :=
  splitAt 1 88 0x373349000001008001000001000000 part374 part373 (by decide +kernel)

private theorem part370 : Excludes 0x8000008000000000000000000000 0x353349000001008001000001000000 :=
  splitAt 1 113 0x353349000001008001000001000000 part372 part371 (by decide +kernel)

private theorem part368 : Excludes 0x8000008000000000000000000000 0x351349000001008001000001000000 :=
  splitAt 1 109 0x351349000001008001000001000000 part370 part369 (by decide +kernel)

private theorem part358 : Excludes 0x8000008000000000000000000000 0x351249000001008001000001000000 :=
  splitAt 1 104 0x351249000001008001000001000000 part368 part359 (by decide +kernel)

private theorem part356 : Excludes 0x8000008000000000000000000000 0x341249000001008001000001000000 :=
  splitAt 1 112 0x341249000001008001000001000000 part358 part357 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part381 : Excludes 0x28000000040000000000000000000 0x3d2275228000088000280140000000 :=
  finishCode 155 0x1b0bc502117c619d06a371841a75e382dd0fd8367c14ff61719bc21a1cbe215a17ade730b851e1145e0b5c1b9f4e24428f19540b179d9f4c9d578ea5188bab034eda728b8cda1acddbacb8682c158c65b2a015fa80a3617ad4db657c66ed9e5e5ac66c96661719b25f9b4c29dbb57c4d0d8342f644944f977c69c2be459c2631f064f118d0bd5e3977e6c9c2d5b9828c69f1970c25835016287f0c693ab0bd0d312231b2eb5a9cbbb74b54a1f85ed8359200a39e5e64ed4e1f466d7ed85db2603db331711a70a3904466e22eb531716a91a76179b1d045bded4c2f41be13d617275d65c29184b621aca2a97c18d914e576b4da6f6e7539d4599affd2b70e76a6f7b4dedef15f537a90d69b67b05fe32f9a882364c91aa698d329ad35aa5e657eecce4ff3295b15ad6cd6e36a9824bec2e2bdb122c2eddb4beda9cb62d5ad92c1b5f29be50b5ff0bfaa297ca732bedda3c7262b5ce13196c620c6b214261ce8af007802ed4db4c5b45b66b76f7b5307da2545942fe62e60dc2d9b26d98494552482db29cd35cd7b4dea5f10a025145ecce253981343ad3ea57b4d967321b4f94b6309185be2f0c463216f396c6556cc53fc94dea696ba6f309b3dad978be20bcdb332631a89216216b5492457cf5f1024eaa2aa7367b4b1a9793ab74c86ba0a4296c36d12adeedb2d734b5d69e6531368b286b34d65f2d3e7754c98815ed25f44f0b97c353c98b15f10367a86aeeb440da3bd7bd2cf5ab6a636dd4c5815ddd5b8ecf60b9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part383 : Excludes 0x18000000040000000000000000000 0x76424fa880000280003000c0000000 :=
  finishCode 125 0xbc5c2d160c85632898b4c5af8ccab0485a857d53601572cda4bac834164c15215df617311a20463cc66da2eacc2ef1b175c4dcc2cf185e5394c5904c14415e65679b45e5b06f435f566558257b5f0e6c707d9e3653492e5e31499950b50afac6802a6814c9e493382f38334caa9ccafd32b262d4c6deedaf2bec3332bb0c2f98b97cd866d1e3f9d059959a49190f6b85e2f208f0259dcb42ae3d30e82d31608b84b0c6d8323134a6e17ccada09fcaf9caecc5e7221445f36f781e4594d141e69596d79654614d166198405ab44cc3332b194b6c8c6e4350bbf526b0cccaaf985bd93404ef291a62ccab0ca21be7d31e31b85b4b9ca6b0ba91d32ac3358b051321945df609c2d931d86658cd1658e7c725d985ce194c89a2f33e19a2e0ed4c32e689abdb85b05f8c6aefd122560bf5d718d34541398666572954925939831b709403ec68b30f492c2ea732e31a2a90cc3cc127ff30b9a2cc3afdc8360c2e0fb262e12a9ccb9e16c0fadd2dd33c3affcadcb885faffc31a94d8304aefbc1386277c2d0bf6cb9959794c8e7c7b477c3a0304b75c17f32aa2ef9f616cadb44e42412817994e663582585e20cc7c75d78ca57ec5e6995995b0b57ee212879f6e9a9bd4bdf567a3a5854865d661ec256c9a6195d973 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part386 : Excludes 0x8020000140000000000000000000 0x3f1ec1a8c49006888228044110000a :=
  finishCode 95 0x6d321b8ec5e2a960900d5943b33096c29a695c35fb60997ceb4dc25a69b53860d5c59c87ebe7229cc6d30c203a1add769a892bbe35770c25a29be6d7b4d44945390452cbbf2c28571672bb5a6c817ee98d06bc258a55df865a6d846be665384b014da6af2e1219284fd964aecc2f316bbf363e12e82c22785abf6d4af8f611bbdb52da6c21abbf60b45c308336d935a6a24a29b64d30ebf728031b0a706623e235bdd7edb1ed2e4a9509b53926125865095d7ad4d826b42f2cdeb6a6daf67f432d83404f734c25915df0df5693ed0d6f54576eb97b5990c329a56daa45e66eb86598d6eb910db974150a6362f12442fc4447a2bd31adef2c21475a9e12c8aed47a4b9d9fd4df69b696fab2e3537cc6d2ba9fb83f6636a7537bcfda5caea17cadc85689b847c5a9d4c32be8570fb3cfe0cd4d20065af6a78520db1675a0b74caecb9e22c12c0a919bb539e2de7e57ed4e78b6e99a66067207a67135c25b53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part388 : Excludes 0x8020000040200000000000000000 0x370f412cf1100490c0282448101004 :=
  finishCode 95 0x6e39990be4b3091844f8a98a35e8d0eec10c28dc2d9bdd82695da49a2d658661e31704312398b7d7ced4cd6dbde699b837bc34d85edae33f1436a714abbf5a9c47ec2e10bf1a58cd9adc31a851b612da9b06e16946c9fad27051d31b0c6d26c1b6a778ec6106af6851b363a9caf9d0bf6a6053524a7fe12da9b5bd82e0a731a5d9fcba24d30c5f39e2e9be26f4368658a188482c0cc35b2dfad4e985746190db44ab49cd4b531c36aebda9cdaebe76676829adda9c9179b4b53c23104ae95da634fdb834cc7aef4614aa730c4579bdda6515e7c79739634ccdef0f716abe613f447e0fc95e20768abe613f840a5ad1de454e5609ff60f84fc5ab7bd14213f78be6126266897c3d051396833e306b0a50a95f3a24428de965f386709fc29ad165cd4be9034749f0fba7baff9ad851da3d12b64a65829a606b9876c90a30a77c2c261ed167d369b9619f4ed168796d7a3db5332382adbdeb53a3d5dfb4598735b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part390 : Excludes 0x8020000040000400000000000000 0x370e4738c112348080284040908020 :=
  finishCode 75 0x1ccc86c371d8d06706ae192852da499f55b6e9becce43535b8405165b2dbad45df1eb5343535bb45f1c88928b2dcb42fd99b31b6f43e6c9a6187c4056a12eb278b5da1ad32b7ad51366c2fa6fb416d4f38db72f3012d99a5bcb0d37af9cbcc96f2c287f68987a26db6df1c66ecce17935bb258289a096182adad5bd4d6de16a730693db65b75828d0fb2e61576670559add105e66eb4436e5443a56e196d1e98735bbe55370a5b22ce86d6a609af6e2f368e157b47b1b436ccdf0eaa6d0a1e4f15395f38c5427ed4d2dea6fb53d06e3692c539d85425cd0960a995fa1f6179c2f85142a6d4ec165b0bcda9c3ebcf85483ed4c368f2b74b9da3c46854e17d1662f32e7601a30ab8d6dbaeb2b987 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part392 : Excludes 0x8020000040000000800000000000 0x372ec128c59424c480280140111000 :=
  finishCode 99 0x1ccc86e311a0bc7625851a356b06f709f9b5d825745a4e6d78a5879ad16615b1d826e184863d1c98adef4af4dea7286aa17297c52c9ff0cb142dee6b6d46c530cc2ed934ae62b14316b0c6e789a6985426236c24309a65bea57a5383cf07de7db5e407b861220f3f21fa85a97a62c03e24f6666b72c2d2ea732c98d8d6dbdd82606135b966317b66096d76f782526cc133168772e752bcc2ed2754bc5f0a1df4e9754596f5a575f4e62e56e6f743b45982431745bdec2d07b697435609a17db2ed35e064b7a494496b7b44b3088636973d8937a2c851d4d6c1a14722cd35b06946d8492462c0d027bb4d9b5f4352ddb6d835e453dd30e6f778144d60db236bcdcb2b688731b446cfa72b714a4f6daf3eab55b7b93db0bc6b6defa0c26e220fab04fcae837a97bc8d2e69fa85ea72887052836d0ce82213e85e1535a0a15c59cb9e22a18cb0221dc1de6c2f1a335bb4ba23d3de2852a6c2db4598d8b5a634d6f43698b5ff1a37d38243182743e161c2f89b5ff1f78fae17f0bd3dcd6ea6b60d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part394 : Excludes 0x8028000040000000001000000000 0x371ed328d319a5d688a88040340002 :=
  finishCode 17 0x2c1b482682186b651b0b6ae8d2ea0cf2ef49b5495b89bdf4ca1d746a4d0730675fb4f728d8d6c68e34bb2461bd65d6b4da4d8af7d3a93656e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part395 : Excludes 0x8020000040000000001000000000 0x370e4928c310a48688a80040300002 :=
  finishCode 183 0x3c248ecb536a43209b4145943e17c7392b72e390bbe9b54d2b69e6b8f2eed532e3cb0c269774c55fb4317afb0b51657ec2a67af87d7d3459c45906ae05b7af6a97d396598cbe20c6d52be33bc8cda62d6620c651a65378b06e34170ec6106ae1e645909f97ce09fb41a935e953146ae19623419e43b2878a581742ada966d57a595b98dbe4add31a0cf642797c4c5a1dc6acca49a57ef092bb60fb6baf9e0c91c934af9d69b4c250f4b2d066f787d07d7af96c5ec6f960c8673b131b02b855af8943c3ccbfe4d315f22cb0be72d2e0a96857c15c79a142a692e7817d398d5d78a1debf4150da620d6f990c52f1aba6197cf065bdd7cec1f1a3931657515f08be32bb44ae87d33946994d4cf22caf9cba9a5c368cdde0ca644fc251a35fbaf9545f3914e2cc4d6b4da69135850e616d357cd3884363b1317994c86520c65aa657ea4f1aba626f0daf31f02ca21b49d31390da372946d31b0da6b784b20bbc8d2b609731331334ad95cc38a498cf32d14db60db5b96acbac36854b6be40d6e4435df989acae4435df2e5989863b209249e6d0c64a365fb95bc84aed6963461534aeca6d31ef1b2b72ee50f0d598cd27cfa72be51a652d495b82a5f2657c05e8696e795b287ec553088b313dcc4a58cdaf2ee8af2ef599ada8d5c5ad2ef682ece653250633b06f76b99dec6ae57e625ae6c2dad34a366142adb2721b49878d2d7edec6459b2d34b8b382a6626617319e632295635b8916e76939ebc1f46ac5e61f661eb4735b443989e653290c8b236be72190fb5a6a21994e82f00af5a6a2182bd69b2eb43bda69adcc2e2f34c34ae8d59adc50d0d30fb3c95f9aa4d6cca6d366b90a9989da3e1e4653907b98798da3d86ac6ae5e5b06d2cb63291a344d35b1a3a624ca657e881989b2b (by decide +kernel)

private theorem part393 : Excludes 0x8020000040000000000000000000 0x370e4128c110248480a80040100000 :=
  splitAt 3274 99 0x370e4128c310a48688a80040300002 part395 part394 (by decide +kernel)

private theorem part391 : Excludes 0x8020000040000000000000000000 0x370e4128c110248480280040100000 :=
  splitAt 1 47 0x370e4128c110248480280040100000 part393 part392 (by decide +kernel)

private theorem part389 : Excludes 0x8020000040000000000000000000 0x370e4128c110248080280040100000 :=
  splitAt 1 58 0x370e4128c110248080280040100000 part391 part390 (by decide +kernel)

private theorem part387 : Excludes 0x8020000040000000000000000000 0x370e4128c110048080280040100000 :=
  splitAt 1 69 0x370e4128c110048080280040100000 part389 part388 (by decide +kernel)

private theorem part385 : Excludes 0x8020000040000000000000000000 0x370e4128c010048080280040100000 :=
  splitAt 1 80 0x370e4128c010048080280040100000 part387 part386 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part397 : Excludes 0x88000000040000000000000000000 0x771b7120a000808000220440000000 :=
  finishCode 85 0xda612c9783653750bd91341f6b4bb53995b35b8582f86e732b616cc4b06b0bb5e85ab71d78c605ac17a3475a5d8372e617ed9b5a5c4dcca85fcaedc37188be0d1d9209406a1b1938d95cbbf2aaa0a06b4c6ccaaefcaab51d0a0b2d7186cc981be12afd8b8d6632ab84b31aa0075b08d77e61e64e7bbc255fb311329363a5549c609306177ab6adad1664f0b65c6634026a656ad955c19acb5835b4db4e5f3a054259e529993a696dd6f3363535a64d825b7664e7cd609b01fad83f4d6c1ad5ade68ae6c728b24aad4d331b11ed172c2f6e4b2887007c351411467ef686d33cc6da3da9c79ed5ba1b2ab534da9cb883bda5d4d3a1b6a66522c34b8d34c5aa7eb2cf32764be5e25129b01fd34e12b569e0e86a88a12e16d4cef16a6b0498da65577d7b6d06995c25a65515dbb5b8d70e971a67b4b1613cb60dc2dc44b5cf4adca69616a347409a432f932b1036499385d4624ca68a99935f3827e2a664c27e96b981967a17cd2dbd6655b1696b189 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part400 : Excludes 0x9800000040000000000000000000 0x7f27e935f00000828320004c000000 :=
  finishCode 69 0xb65f2f184c84f1b342942dd3f67a36d3b4741d9b4ed3e1850a99e591c01468372050682cbe714ad86647683af9c3ec48bd140be695f5a3e83c1fe47fa1b85f3ccc34d2eda0abe70d2643452cbecc9da9cd0f0fba0e7ea0babe614732b88c24cad3036672e2a7368b4c98b0cb8cc3929cc9c2e230b3470491b4dbcf41e7cd5394e781765f619f41d4bef1642815f3a9bc27d06cb5e0f9c19c2386796fd0d23993f6656d4e9be8677cf2817c5f29120879942ed4ed3e2962ce80f49a451d4db2e36a683abe6d9a83b434a85c3caf9d99c9ff67b434cb5bc26883b6a759ebe3cc9c0d767b4c9d1e989cac5843cbd015df5641d86904d4c598f4c58134ba65f314150641af60fb97d4eba5bb47806db4d7ce0ef0216bd981 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part402 : Excludes 0xd000000040000000000000000000 0x7f2e69ee800000a201600068000000 :=
  finishCode 29 0xc46132170079b4341c6d4cca660664c6342e42bec14813b818dadd7c5af546d4d5476a43a455f16bdd079a35f4d445b9f38ac18d77fa23e1de9b5ba62d5b5e6f77930a96dda58ccc8364d28c7eb4cf32aa664b3528a0db7be71bde2d6993617b416d4ec0a6b359851da2d4a332b846bd995863664e533 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part404 : Excludes 0x9002000040000000000000000000 0x7f6b6924cc10128a41200848010000 :=
  finishCode 61 0xc45c2817cce141ccacc2e52abe3381f1a84ff8633258de72f9b54b74d37cf9e0cb2fb3bcd24b63b7be83cf9b326d134b38a5cc9b79d12cae12b5e56f797d9931f99dd41570bde675108964b5d11edb2def2df5a9b63e11cf77326ef3451cb5b76cc9c50764be581dce6d95055ed53578b9b65bdd415a978a820dd16b67f3d7bd2d24d6a6db226b8473b9b6cd9fb6bd8261e2e1c1961750f96332946329a519bde8fe995773b53a0402285c35a6b66ccab71e41b4cf5e5034315d7a18e031533b3f0a396b6dd891993d42f14cd3e6c23b5396f81ac18708c28ec25 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part405 : Excludes 0x9000000040000000000000000000 0x3f4a6b248000008201200048000000 :=
  finishCode 175 0x5c3217ca4553508a68b250f36c85c85ad34d0224c40a6c2e5dee96ba45a5a5e8ed3eccd3162a6976b3db330b17979f3e6042c42e6a98844fb629cc16aa1714d90085cb06d12a4d744acc994d85ccd2410c4a21accac69ade710312adef14394cd5369a09818a654bdb4dbcde6628788251b130213f539bd2e83da9af9c104669953254b7a9ce31b09f09f8c9620daf4be991cc0ccac0b21e204369f6670e74e6a06bcb63a23132ac88645acdcf15fa83c59ef5b5e6057ced3e13fb47acf5794a4d7ceda5a9cf7abcb45aa62c305566a78af2998815f3a976cf66053161cca66d967b4b593a94994cd67b6cda6a2185333033d4b7bd99c50ea7328bc523132ba8981940c27e09f97ce063a6f98109fb459f2540ca676988ce5f3b0507147db28031ada74c99a6a9cbd8d32669b24a61a6d1ed2c24d72a3285af98a5d852dc732758924d14e6c1786d37a59ebda9e4c5685b2b4f397ce2d650b7a57c99519b4c0665f5e4d4bec10c6c36f35a39b65457436d0d8d350aca266e36a50240d9af8727ca15b69da3cf8f276a15af9c0e2f8769e31b7cc4562681531672158c4e83c4fb3034c1479bdf0be99e64c6270be42b189a18047013da2ccae17be4be9a15a4139e0ff03198109f99509fad4e0944b2500d36317c8621daf14168af29b8952699a4e26c6370a69619636095356d3b6582184d2def5a991cc4ab69d85f0e7a0ed8f44ab69d852d0b4e6a070e712b9cd0079d67b85348a51aa12536f8359eb429fb8c6b69d48b0daa6ac124d30c6949d02c0876a1f30b94dd6a64d330b94dd02d8876def2ebe8291cc4acca93490cd67b12aa3b14dde265686d53550f2875e462655b1eb538a98af4fdad4db4e4fd78d7b1 (by decide +kernel)

private theorem part403 : Excludes 0x9000000040000000000000000000 0x3f4a69248000008201200048000000 :=
  splitAt 1 97 0x3f4a69248000008201200048000000 part405 part404 (by decide +kernel)

private theorem part401 : Excludes 0x9000000040000000000000000000 0x3f0a69248000008201200048000000 :=
  splitAt 1 110 0x3f0a69248000008201200048000000 part403 part402 (by decide +kernel)

private theorem part399 : Excludes 0x9000000040000000000000000000 0x3f0269248000008201200048000000 :=
  splitAt 1 107 0x3f0269248000008201200048000000 part401 part400 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part407 : Excludes 0x8000400040000000000000000000 0x3f726120c0a000c000200060002000 :=
  finishCode 129 0x34190c2592a94035d375825b10ee62e8819956cda2057454268af9957c3b35b3384357b6d3ca6fb06f6e42839519ad5bd6d357968734356f589aed36e0a1714da1a9b9f61e8e29b95d0bfb597cec6235170b2bb0bd3ccd8e6557b49f4a56410cc6616cd934c32f6e16da0d32abbf69b08cb6bb64b76d49a6c6c2e506f48235e835d6660c2bda0c3481b4ec2d9930595ed993815416ed360920b83a218bf6bbf2e3344b64d358b8a56d30f14b506a9a24661f0be8915df8ca697126b8d8e2960aa351ba66cd6edb8354d32abe6de71e0b6cccaaf2cf2e6c732a1f35a9ccae2258097027af2b64dc17469550539934ff053818e053a0480d8dc0ddaf9b27fb69af2cae955b53a495f38b383e70b6cae5f6cae2cd0ef7990135f31319936cdb4463096971b319556bd993c239f3f095eee159a2620d7739406d389ad42d4bf58f6b215947e17d0c74a6b63a0f14b67f2ce513529ccacb3cd7b7cc4340a26cd677f7c7b4b9738e682c6529daf6331a0fb69f493599da7da0b2e6f3ed7a857530d95ccacafcb9dc24190be21ad51125b969619959718b35b1b41dbae61db566569826b53998dd99bccccacbca857512a92418db2b97ccd566565f3975b4fb07db2ecced367cf453b4f8a21dd32a6ab7cb4f8f5d0eed4e61c4ce95d88798bb53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part409 : Excludes 0x8000000140000000000000000000 0x3f12e1e0849002800220044000000a :=
  finishCode 141 0xda682e190c25802d60bd37337bc61bad0ca16a17a87f14de2351681aba8552c958580cdc59d67f11ebbf1234c6c45cb0af9cb0cb470ef167326be72c335eb4dcb38cdda6d2ce33643b43eaf9cc9b5e8cdaf2d28d660fd2cf30b0fa506c2f24891a28e1f696bd0dad369761f57eca0f51ac609a64d49d4cf0967cd4eb42f7cda64ecfe2470944a6493186bb69f00dcb5bc8da9b4aa17a218c6db254698728f0a788fa61ca3ea16c967a61515c61463429658f8457a246d3d15e5f37b18a25a5e59f4365c76a787d28f18d35db11acc6446947c52d2b68af0d3447be1d683a0b0fb16689b0cf434bc8da7a17f6311a86822b947832d14ba1b35ea2bd123006a2f2a00d626b6a74b3c52c33da9c0272d620761296acb3c33c48a17c48c85ebe74a7599d32851da9cc9af351185f3869a19e59e64ed4e8918b5ad4e1a6245ab698da6b993c2593206badef35bcaea2194da8de31e2ed0db4b2d1457b534fda624a6e9730bdc833250bbf2e3194a87b4cc3dc51aebca1f6a6d0f09de829e0da9da6b7bc478d5b7bd0f680f6a716b54c86a3184f76818d5119aee2ce56deadbddf3e78b7ab9870f14539bae48dab0c6b759aa8c6c95a8a60aebf74cc6620636d2e5f3b4f6f797381c66931b4459aaa15c48c0f731b166f48a5a5753c629695dc29b02f6c006a6b83e16344987977ed35bad126c86a25ae5274530bb6e582d6688575a0854da98c4d62a12cb530a513da22e5cdbde94ed070776c7a57b539b1d7ce9a6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part411 : Excludes 0x8000000042000000000000000000 0x3f1261718900108400200840100000 :=
  finishCode 109 0xda6832150d41b19b9ee24035714877a935b75bcd4a6993d0996f8a56d33299b3665664de657ce28de74cab0bd0c7166b624a68af4be9ebb6ed53095837b2758a4e64c2d585ddfe0f902399550f967459c47634366ed9952831abac682d326daec12dbb4d208dc74d34c9b04cc9cbf7304cc9ccacb5c17ac2e6f76c5e562656f9884ff828c29c9ae90da7534af9adccf1ada6f869f2be743384fa817cf58da6f5f147ad8c8aeb733c5a3a59ca3e5a3c461115d40dbaa5eeff431ca88c6b69ad1d32732736e84fd10636b35993c29ad3db0ef9acec62109687d8b3b4f6dd28928f5e5a7cbe74d369f4c9a17bd7d2df853a1ade64d6f85f3ad353fe296d3687d5f390361c8aeda766722bea37168aa2f0a1c2a67af5f3b4f995b4fb190c0b15b19745ae5bde5ae5b17819935d1b415e6664e9a6cce5353295e5a5128799599594a42c7218cb404fd2d61637c99518d96c5e658240164c5b3f7810575b15bb975968db2c1756ede6626d7fdf4e99548552656f99086d829d164626d0f5f30a54f99939f4db2c27daee26b1ab873aa4c9c13e8b3a896b82ee64e2046ae5ae0b5993 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part412 : Excludes 0x8000000040000000000000000000 0x3f1261608102008000200040000000 :=
  finishCode 125 0xda30ce830990b2391124decdb65aeb4d781a1ce554a66c170d41b9e237086b436a9cb71a278d5b0bc98b85af476a617a82f4ca93dc39d2d76a7312c2ec1b4aeb0bc40d16a5330035da6d9726245dfe636285b0ed90c751e8528c6c59d8532d74dad2b31b70b05432100363c46e1ea62838a11ab6a2f8d142c1b36cad8b69c146f52de70c7276a94b0bb0200ac6e36c3be450c5aa5ec9aab461472eeb47682832a6ac14758c4051d28c9f24ef2ee04736e89ae14c3cc48c48d2ef0fb452be0988cb3c3c851f62f988d443eda0b2fadc76a6be652b3273d4941cc9d4d30fba0b2628d5cb5c3ecdc73262c3d87a584365ae28ca3c6aeb0be727fae8c3ccbe6f935094631a94a30d5a2bc51a17c5ac51b66b4b42fac641b4e5036995d16d38416946d4e23e22d1ab1abb0b694628e2d6cfe5d11ab6e386ae69b83558c642d4e51b43b459c62d8d6a631ba0b27ccb8aefd2e231b6a7900a75edb416d4d4d5836d4e973c8452ca4e15e8b296b2e3c3bbe0a788c6e434188d4436c33686a176357488622c928c86a697454c9ce16a89f32b2d71a5a2ca2cd8cbe4f2b031350b53a6542a655627d99588fad3e655f06b09f34ca935da9ad8c9db14864cab41d85e13e8576a74b984fd16b58879a2d69965cc9f7096a697b7 (by decide +kernel)

private theorem part410 : Excludes 0x8000000040000000000000000000 0x3f1261608100008000200040000000 :=
  splitAt 1 73 0x3f1261608100008000200040000000 part412 part411 (by decide +kernel)

private theorem part408 : Excludes 0x8000000040000000000000000000 0x3f1261608000008000200040000000 :=
  splitAt 1 80 0x3f1261608000008000200040000000 part410 part409 (by decide +kernel)

private theorem part406 : Excludes 0x8000000040000000000000000000 0x3f1261208000008000200040000000 :=
  splitAt 1 94 0x3f1261208000008000200040000000 part408 part407 (by decide +kernel)

private theorem part398 : Excludes 0x8000000040000000000000000000 0x3f0261208000008000200040000000 :=
  splitAt 1 108 0x3f0261208000008000200040000000 part406 part399 (by decide +kernel)

private theorem part396 : Excludes 0x8000000040000000000000000000 0x370261208000008000200040000000 :=
  splitAt 1 115 0x370261208000008000200040000000 part398 part397 (by decide +kernel)

private theorem part384 : Excludes 0x8000000040000000000000000000 0x370241208000008000200040000000 :=
  splitAt 1 101 0x370241208000008000200040000000 part396 part385 (by decide +kernel)

private theorem part382 : Excludes 0x8000000040000000000000000000 0x360241208000008000200040000000 :=
  splitAt 1 112 0x360241208000008000200040000000 part384 part383 (by decide +kernel)

private theorem part380 : Excludes 0x8000000040000000000000000000 0x340241208000008000200040000000 :=
  splitAt 1 113 0x340241208000008000200040000000 part382 part381 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part415 : Excludes 0x88000000000200000000000000000 0x761b51149050004040000008811000 :=
  finishCode 93 0xe06d2c194ba1b1cc0cf9ac1285a6e788c20d1caecdd7846dab30e9c617f3033b9c37cbba82bddcc3d22cdea81a9c7a0b6a7b835ba40d1d913deb530a5c2f80e70a626d75498e2560ab862f51b8c459068e218450375b7285f9bac9c6b7710f2ab282be7cb3192e3616cbb8f7a71b00d6138e5de69b5df9618495eae61c9c64e396b5df69b7bb9b55ead41658538c2ff0b67ab9719870bfa45930915f36ada9b7a9bada9cf9ec03949a3d5da2cf9f10315f16b617da3a71d15edab5b220f0c2271d85a64f2e330e17add6b09434db51d16a7451aefc3cd68f2ab5a9848993cb0d4a2f036a6a03279f0661e6063295118fdcc9e2842f6636585f4e9877a50bd4e382f6e82bf2efc5abdebe79ba85ad92d4e7977818872716eb6f57bbad4f11741a396b9b94d2c2d70964db7a52716f534ba04024869614b2ddb0ab6ab7aca8cbbac2b485c9b0bd4d428ed1e85f9676e50a3ad25805b9739a8ca5e02fe21e86f61544118f6f5a1bd8550dc63e8959745b2d15460c2d42be18318f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part418 : Excludes 0x8020400000200000000000000000 0x7c77410cf0f0044850302408101004 :=
  finishCode 103 0x6133988b8502496a704db75a96a9ce435920e044ac68689e6b7106cb94bd8266c709b5dd9ae5b5d4bcd6ea61ad365d426d4be18f488290c61aae5ed7c77d5e0364d84a8a714ad573cfd1fe11e0dcc2ef4790e048359744535fbad4f09585d6c6c25b53784934166ab307863b53c23a8fd38f0b69060f445c59a316566e5b3fc25b3f96c6c25b4d4536f7b08f095ae6c235dd977c82fccf3edca8a6f8f4c6c3188f466284cb388d7315f2ebb7bbeac4dd30edeef473e3e16d69b6a6f8f12b7c66612d30f0db6a6bbf2ef6a7612a1bc40cb0c57c22a9c609e13348b05a9d2eedee85a1336a737be16d2baf47a0a7f6ccb539b1c13c266636c0d4b01f84c96dd69b84ad8e07f607a4418064e342bc25a636ab7c77d5c83d1adccc2f69b8466b768b034dc35967f2eada9c4aa29e11d1676a6d57a0a6b769b611da9afdd9fc7732e76a68777035b9165f1ed64124166709f9a18afda9ae8aefe225046b617b6bb7bb54d68f85e1336660b308fcd8e1338835bc2397e50dd676b53c2d06b69b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part419 : Excludes 0x8020000000200000000000000000 0x3c07414cf050040040002408001004 :=
  finishCode 169 0x31190b870361d8c20d3d82c8d974aeb6a93d8c5855bc185c9ecd6d32e79fd05b53c2db09510598f8402c2635aeeb3388bb539715dfa4445d1676a743dd68f16ad7730f6a6e89043177e1f6a3d329b45c2782461f5aded4ed4e6e7b45a63ad4e1f5b56d1e586b537d36eb327a2cdf4c62e8033784873a2bdbd54e513d65e5d14e343133788b9e2ccddb96c0a730558c3e1278e852db459f4ed1e7c9a5c513d2fec27b5361579d6e75ff948585dadc2ac61fb1c4a458381281abce37bd0f6132f4a68e51adcf36384cd6a70c9430bcd8e13268edef9c25d942515df0e24b9598266d4e6e71ab6b9a1b6d4ca346ae9128b03e0265a5eb537a53476c796e61b693ed4dbde7af6c7b53ac10db12b6a72f8da9d489e4a2d4e5d76e7269337b0364c776b5b6a6ba24d29c7008d97bc5da9d99d14715f6a687666ef0617938ed4e25661e5a3405c1b50943bdc521d118b81a3cb220d0f271da9b00b0aeb14e609b6f70a992be03386f4575390a9ba534cd8e8af11ed8f5c1b1e5f9615ba048d1431468aabaf597da9d31a153249e502e8a726535a9a20c51cafd2bf226da980fcd26bd72bf312a471476a72bf054d821a687b23f9711778a30a30a945556451e86d11b31b6a7048e435940965c10c4c3e0a344f88fad4e63e26e91700a3a18c5cd16481e4e30994d335ba2576960a4762e051ac03051d9fc9ef8476a7117269d97b04934afdcf636a651b70b53453b415b570964fda67b3fd050a3819c295806814835b1738a06d16c27043a6d985b3f137d05b53a4610c3e26928189181ad3af0967b1d05c1b6d5922f2416a710153ad141ac57db91235a3c51834b42d68abaf450851d11ec0214ac895f9f0f095a4e5657ad7e571eb4795f607 (by decide +kernel)

private theorem part417 : Excludes 0x8020000000200000000000000000 0x3c07410cf050040040002408001004 :=
  splitAt 1 94 0x3c07410cf050040040002408001004 part419 part418 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part422 : Excludes 0x19000000000200000000000000000 0x7e436fac944000014100004c003200 :=
  finishCode 45 0xc85e2e030705785ad129958aa6722d6329a3fc2d6f750918d98f8266ca6c1b961a5dc636b104347c1ba63621f095825f56053ad2542663456e515877b9bdcd1d75e05d14f96f975ea964ac0c6c129567c77c36095df7d5b08e887971ac3b9d30f4af85b2c2deea12a7297f44ae11c43cc3c11995898da17c7be5c706d77d7edf364e1881977971680ad9dfc646f871dfe16c4eefab58539861581c2a461660f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part424 : Excludes 0x9800000000200000000000000000 0x7d26e935f0400000414000c8001300 :=
  finishCode 33 0x2d964be5e309440a50a9820c2c5acbd6f0f4e6d474c2c33c32cbd784f68ada7b80a37cd985494e5b1869867177187a64bed6a630a13ac2b296a9cf1027709e6c3607275a5e53f6812e30b58c3a97cc0c16f48b253183d8570be7b124db47097b5385fed1db0eb2b4ff18778320c8ed4e98e87b7d5253a9b65c65666d3a6378d50b5dd993 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part426 : Excludes 0xd000000000200000000000000000 0x7d2e6deed040000051000058001a00 :=
  finishCode 31 0x5c30990b5386342e42bd5815231b84f354cc6e13d6a6dcf600379b9e1a622dba623c965edc28c61e50f8d059ba5b1ed4c965d8dcf2ab288da9b74802d0fa01a1236a76a727cc12c14c5ed85f54454d6014827ba90e96d46ed267d37b5987a43a7327ba635826916a73e9993b73cf0406b4951178bb534e5b53b41df4d7c6327535 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part428 : Excludes 0x9010000000200000000000000000 0x3f4fe936b0c4808041004148001202 :=
  finishCode 31 0x5225910a6307b0acc6cdee51e4d74c33c5be9947e22f967b3738c4947d6181c25e7b78b509f01bb0a4c05e2c236cd53e642b607726d17e7110c73d8cbe8c6a97947e129a6b537d5b4581870becfe18d3e428eb625fd32f965f3c5cc78548c6cb7cb4731e13ed8e66f147a97935cfa76a70f38878bacf5f4c6257ac2a4a3db4eb47189 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part430 : Excludes 0x9002000000200000000000000000 0x7f4b7924dc5012004102004c001200 :=
  finishCode 53 0xc45f36964d4141d830a66d95055ed5356a16ad85a863a0ef5efa6a0abbf373cf177e617c2da976d2750e8845e2c068edef04994ab0bb53c06206adce52a52b4c6b7bd28c12330ec2e52a52b30bcc0305193eea2e178960c3d5210c032a32ee8489a3848d6a6dcf3d5c33af2d948f7c47da9da9cbcb3ddb6ca7fc22d96a704cb6ba81c44eba345ac30740963c2408622d736989fd6a785f68b4b3b0bcc9a8184984bc029ce6d3b43b0bd2fe5bd85ed36985b53c25533 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part431 : Excludes 0x9000000000200000000000000000 0x3d4a7b249040000041000048001200 :=
  finishCode 139 0x170be55290def1438c685aa29a2cd031089f780b582e4a6e18da26e9ce1890b5a46811256b65176c7059b3d8736f729b0b9b64b5d2b6f7b10331a162a0b4c68faa99d1fd1032fb68ed725361730c9a482c086b58c2f9b4c5fed969352293493ab69ca2b3e7846848c6351c4aa32310bbaf7b1a3b74b4cc51b47b84315f85f27e94cb03b74d68ea731a3b7bbdec13edef300e8368a170c1a9c8c1c68f303ea38978986812ce97d8b5b496c39556152991879819854a666156d39795f1185177232260540daed07369d9ec39bccd2fb594d2ab692f9ada6f9f59ebe7c13f6a3b19cd05e1b4e86d8af28d2998c5f1905360a33d8a1dc4daf6ca086251c8c886d895b358f3e9bc89cbddace6d36f7b6313096b358877735096b79b6621ddcdace6d3509ad4dbdda81332e8aebd2dc39c3c2da7852d8f0aba5fc4ada9a84b7b8f0d8534baa1253760be282d31aa6b546f7889c806d4e26c25eccec295d13473019b267928a6306b04e0dc126ee73eab69ca6b847342b69a87a9ad02a97cb021dc32d266175e3b4989a6586b535098878819a9ccddb1d4249a65183719bd97d2ee66f363d97df2519cb258063608be316b5a4c36be49f6cc2d39cc2cf929db5a4c51c5ad8024e8876d3617509a28e2d447ec2d6d30996179855f117d86362d624b (by decide +kernel)

private theorem part429 : Excludes 0x9000000000200000000000000000 0x3d4a79249040000041000048001200 :=
  splitAt 1 97 0x3d4a79249040000041000048001200 part431 part430 (by decide +kernel)

private theorem part427 : Excludes 0x9000000000200000000000000000 0x3d4a69249040000041000048001200 :=
  splitAt 1 100 0x3d4a69249040000041000048001200 part429 part428 (by decide +kernel)

private theorem part425 : Excludes 0x9000000000200000000000000000 0x3d0a69249040000041000048001200 :=
  splitAt 1 110 0x3d0a69249040000041000048001200 part427 part426 (by decide +kernel)

private theorem part423 : Excludes 0x9000000000200000000000000000 0x3d0269249040000041000048001200 :=
  splitAt 1 107 0x3d0269249040000041000048001200 part425 part424 (by decide +kernel)

private theorem part421 : Excludes 0x9000000000200000000000000000 0x3c0269249040000041000048001200 :=
  splitAt 1 112 0x3c0269249040000041000048001200 part423 part422 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part434 : Excludes 0x18000400000200000000000000000 0x7e7eef0496f000c14030000c103000 :=
  finishCode 57 0x3217caa05fcc6c136c0231accac0abcdeebbf2e337acbcadeed976492442e0e44c39dd61bd855b95bd650c2b3debc2a8bbc2cbcb4cb0202c13286f317027b6baebb64bc1dce1e38732015d14e35d19c8c84a303cba20ab15367f6c6a7a925b9df3d7e67756d5003ad15dcc25e206256e0f2f28abe7cb19910f284bb9b64b6ca71ca12ee6deeb2b363c43bb984ca4190d97493454a6584ec43829b64d84aba312a13b3c01568af4e3437acadef65d6814c5d7823425ee03c3682e17b0aa61a97b00df30be6a77b198dc2f843c104bdf08e98d18d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part436 : Excludes 0x8010400000200000000000000000 0x7f76e307b0e400c248304108101002 :=
  finishCode 29 0xd06b2e17ca2147dd2d3e5c718d97d35d7a3a5d5f1ed3ea6d973b4760190303cda685660f36384eafcb10d753f6b35c2f859e5750b7186bb48882fcd9ecf3f2fb4df59a818d66b2cebd6f6b297dc21bec2942bc2f95198d60f8696079853263662eb53423d05a57e626d4e6e7c296d9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part438 : Excludes 0x28000400000200000000000000000 0x7d76750c99e801444030000a105000 :=
  finishCode 77 0xd652309708628ad656d928b2dce86b7c961ad3de642fc935166b16a704ea8bbc19079303389dd2ab69be7c39cc9c9c6da70df2d6d2ae32f931b0c685fc82510c6d798ba254265bdecf6c296b36d3661e4c0ce08623b6a6da6d9369f5a9a7184cd84622adaf0cd0588a414d38db4d78db4e873aa412f9604316d7acade642757ee2966e74ff9436bc9fedcf6a708eda689fb6484ccc8977a5f68fdb5d82688782ff4154ac5929be18552d09b925a2c126a72e0b4f96c61a5e1d076cad3fdb4e5f652fb2b6e521c17c92459cb8da1ef9ab636878c2984ca2ada69c6613271e87a8a832ca2ae0981ad35a8e64eb4db2b70441e13035999a1a8bd302c4b4da9856c4c86d3cc26b4da6f687d05321acac4ceb35c279517cd185 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part439 : Excludes 0x8000400000200000000000000000 0x7f76710490e0004040300008101000 :=
  finishCode 169 0x359a0b8612815436b7858b4e1b410d4e57750d4dd51661853622f457b6aa1ab75c09edab4e73bada9bbf9b9a2994dd02c164363ac5f026d83e5ed5c18a565c960fbe621836295762f1b4cd68b32768b1eeca8a1bcd52dce0a3889614ad91e92a35a9b00e13bddcdb2d361236178f7bde821be7cbbad3700d09ad158066057e5f3e5ae9614ae12d69ac02bbf612a99cbe580a6e88d3359aa1daff9b6cb9cbdaf6369e8772efd32204db66266f7d059ade6265768810357b560d61736da614db21f8a0b03110dc12604fa739dcdb64b3e21d75ec2511fb5304377390deccdbdda9e3076d75d19b261bd75eb53113ce621f97c42d98201b1ea496e7a6f97798d4a218d6a623b30ebbe9ab683b64e12cc3a18cb280ec43186282c3de0cad922332efe178f7d37cdcfa0a3debbf002ca0b85b85e28f4debbea004b813c466c236c7644325024b537af1e82b73e3240d929533b9ae8b69e17c13383702ce17da0a27ed2f2ef2f6af190baf2ef82baf6d85b1eeb69af6bb9c952d92622da6132c1abf77090437d6a7326c2a856893546019e6426d81d14ed910942f2cce6bb6e57cf5e5b3da1bed3dbdd08e8736f5b3398da2beccdba5b96055881505be5505f686fc2f86db5398743b98d9e0daf09fc57da9b51a0d6f028d2daebc3be272ba30db0df353aebe83092036b3736034138de91097d8c87415f1de1e98d5b9321d057a3c25accde1f4165deb53c2d98752192682d6a72c2f9adead8b69f613cb3af5d92cce5eba6f8bbc034c1f08c4fe816436309d98569beb2bb454378c322605505ef2ee983a16d69b84af77612e11cf7710aa437cbe70d2c2af05e5ad3de15bd5b2ed1e24db4d423a0492cd426ed1e7a9971c1bad361a6607b35 (by decide +kernel)

private theorem part437 : Excludes 0x8000400000200000000000000000 0x7d76710490e0004040300008101000 :=
  splitAt 1 113 0x7d76710490e0004040300008101000 part439 part438 (by decide +kernel)

private theorem part435 : Excludes 0x8000400000200000000000000000 0x7d76610490e0004040300008101000 :=
  splitAt 1 100 0x7d76610490e0004040300008101000 part437 part436 (by decide +kernel)

private theorem part433 : Excludes 0x8000400000200000000000000000 0x7c76610490e0004040300008101000 :=
  splitAt 1 112 0x7c76610490e0004040300008101000 part435 part434 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part441 : Excludes 0x8000000100200000000000000000 0x3e12e1cc9040020442000408001008 :=
  finishCode 165 0xd070321b8ec6a36835784921409ba949bc3d6a6efedaa0b72dceb2c11c69b983f0bd4a5796672ebaf6da9851cbdb70964c0cf2ec036a72efcbf33e6d217e60a36019259ec313686d8adcabd7612e136964b01b6a2acbe26f60135a6aefc51da9e16a24dc2546b2f88f5210b5373509acbf0b585e54687b6c56e50b5da6230be7990a342d8a397ec28c28ec4612e1ac0b577f9b2d83c66c2fec8336b47682bbfcb3b07cbec6db59785dd6359a884322e0daf84f2718cdcb8d69369abbf2e35a48cdafdca8cc2b666bbe337b45d1982428e19b9b666f795560fda490db5b16b535b9a22ecbe189453c61b6c17a16a63f682af8a169b9dd311b4ec583196a7054a2ac929985334ac50947a169aeca13a0f271be19a3947be1b9e95d87bb3335d8a134797798d88fad4ca3cd76e12c9778cdd806b131b1ae8548c6cbf3a1b5a9d94b5b9aee120015316b614b5cc33af5c59d85385e3121472fcb5bdc2911c9659ec31ac0ec1f6a7051afc851d11ec0214b6a724b53a1e57ae2d56e6069c25b53b11d8a45c2d4e78b6d96e760128f7c597ca6cdefa0b2c331af1737bda9cafd65f4c6da9b6c99bb00d34c9ab6a770321a2d54561e583c2a42d6c12e32f6a5db0ba26a20a84d65385b492bbe17f90ba63298163a8946e1b6583e6d74496e59b5d77e5df86366366eb449dc6b0a1e449d437ad99c14e7ef667053a71a11d116d8b842a36bf76098140e82c65f2e29d6a36d8b26be0de82a24b64d6a731a893b8a6562e931b36c853e32cce86995f5c76e778b6156d93479e2e6270a6a695c998d60f891acf6d3d854d1e635bde0a7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part443 : Excludes 0x8000000002200000000000000000 0x3c1261559160820440000808101000 :=
  finishCode 143 0x70371a0c86a389b4960d59b19b5e72f8c1ef0f5a1c52a18da1c863271ca8c13f88980cd8d599dc862f92f27307df3094e72f5c57a27a2ca94cc2b5219a5833c6872a3692da686a89e33634fc4da537cc2f85eda61366b66d77ca6132c4fb0e705ac39cf4b2ab8444982d663ed098911836d30a3c65225910d6307b0a84bc51efa6f63622b1ac607a57c9f5156607b0a5b9d15425e5c7b451854e3607c4562997c5f982a49adebe4577d368709f4e35f9b479b4d38d7e42a698bf2b06d388a56c661445695915b6875a34555a392bd6e5b4da1debe59e96f5f9c46b29851ebd73c9a7c8c493e854c9cefa6bd689b2d8854af5eb01a6b45b474f95b9acf449c01ecce5657af594c4e3826c9f50ae4e75234e7894c5df217c8c6b3508928b34c8afa9a4035e061be64cd1d4a42c678151b3475e586fa256d98cd4058c40a065669859675e5d0fb416cce615a1e55624dd0f86f99341d5b18ba69ccf0cfdca074145fddd6347b355e56cbb3d811f0be2cdb2c2c5167518c88303b7bd2d6d4e86abcb0dfacb459b26566b47687d059e653ac26d38e20f274be84dcb5eb026d0d6895b3db4156c4c7cf0eb0f88c5b0d1df2617788b0a78b3acf4936cd5f066157c90a9a57d85426d83ec2712986e614f2948bfc162d96bdb05a857851cda631790b2682256c251836cb4570af18fba5502c427e6078818dd30a0d712aba30ded932e8cc2d516e617f60761579996e5b657945fc60e88226c152c1ec2b6c5f9a57c26e57e097 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part445 : Excludes 0x18000000000240000000000000000 0x7e526f4697c300816800000c3030c0 :=
  finishCode 69 0xc8682c170ac4c5d4c6f0b66adeaba28ae15e31f100bb983c2fdbaf68f9f263bbf980846a2b92bcbf39ca62f1b642fd15c8d698b86f019011b295d7c2fad3f414044066ca565695f873d051efb350bf44d823d1d0e6d4af3e9c32e2bf6f0942ead312db2c1ba88874c7ad3e9a44ce2277a3b06e205f5492ef94c5df0b50bf09188170b538662e21e2d621eba530f116b705d16079e5e1cdbaf09e196885c1796797c2f8656ebd079654064045b26ca6195426053865065b8341b956ee0536eb5bb9e154b44360195d1b83decc02f9abc6d9019aca662d75e62eb29b05d05f60991890afac5c1ea66d97cf09b17f8604ce16da0b312db30df2ebcc2b85f682cc4b6c8c6ed2e830b3038548c6a2bc42d26c2f86f0975d760198d825d3c65d423618560f09f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part447 : Excludes 0x8100000000240000000000000000 0x7d1267c6b74b008048012418201060 :=
  finishCode 37 0xdc6b32160459ac412d4e4315fb9828dc06ab776a612f6a72e4d31af824eb6a7168cc3a1dbe2613cac5b0246636a3fa6f0a72d99ede5d581d83e635f0581e98d42b7c1971829df06e16a74ae853ae3d2e76a72bf5a9bd7b0a846db2e990d405893ac83a5022ff307d31a14e9e3686caabd4940b7ad6a714b31ac2b70b53a63425e1dc5fc29d6c6989b53097 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part448 : Excludes 0x8000000000240000000000000000 0x3d1361449343008048000008201040 :=
  finishCode 149 0xe26d32170dc583106a66d7741ab42d9104a0e7814ffb25d30be6d30a3b539746c2f993879ec622903570c449785a205ef6d4d4b657687378598144fad4db554e70910345a9baa2ccb2f8bbb2efc48c32d32711ebbb6a7612a966721ac549bac51cbcb152893548e16ad67ef5ec1f66611ab935a6b4db00ca8b6cc3dabcad3769b2a285b22a9a98c59b5ee351601abb2014d11f6a7136d46a52a67843d3985d43de8eca66c3b530938795dfaf974943c2a8bbec1a6db457a1d832cf0316b8372e71b6848da9d8366da8aebbf605e2eabcec6528636a6ee7612e86da4b51e0dda9c86354ba3b9cfa609e6dac479da2bed4ddcd4270be7c9b535b1a1ce2bc13d74515ed4c24e60d609ba583b110c434ad0ef2ba14e51e6ba85a8ab7080300afcd11e0c34b38c6da9da9c6bb143361c5a9aecb05de601523a23de76634d76386bad4c445ac122f4b14726acc6cb9211a122f3b59fcc6905c47848e22f970971948d3fe5dd804a3e9110091d05975de7ed2571e7af9426626509091539b53b214809f860c6acd2d1675089edeb0d5c54cdea15f48ba5f31814b2c8b59edd83df4e8b588f5c9a23ddfdf05edc27e8b527db41426e2d67b727ddc5c351481a7aa0cda24e13d6a64bebbf14b2a3443c17f48c25a7d4db0eea2e15e893280a396c5f3460cd0e8910a30b5b5154c24302fe61e7d35095b95e3b2998249d608bbf21884cd65360d85fb51c6536a785af26bab3c183a1bc2657eda268a50b5b53 (by decide +kernel)

private theorem part446 : Excludes 0x8000000000240000000000000000 0x3d1261449343008048000008201040 :=
  splitAt 1 104 0x3d1261449343008048000008201040 part448 part447 (by decide +kernel)

private theorem part444 : Excludes 0x8000000000200000000000000000 0x3c1261449142000040000008001000 :=
  splitAt 2828 112 0x3c1261449343008048000008201040 part446 part445 (by decide +kernel)

private theorem part442 : Excludes 0x8000000000200000000000000000 0x3c1261449140000040000008001000 :=
  splitAt 1 73 0x3c1261449140000040000008001000 part444 part443 (by decide +kernel)

private theorem part440 : Excludes 0x8000000000200000000000000000 0x3c1261449040000040000008001000 :=
  splitAt 1 80 0x3c1261449040000040000008001000 part442 part441 (by decide +kernel)

private theorem part432 : Excludes 0x8000000000200000000000000000 0x3c1261049040000040000008001000 :=
  splitAt 1 94 0x3c1261049040000040000008001000 part440 part433 (by decide +kernel)

private theorem part420 : Excludes 0x8000000000200000000000000000 0x3c0261049040000040000008001000 :=
  splitAt 1 108 0x3c0261049040000040000008001000 part432 part421 (by decide +kernel)

private theorem part416 : Excludes 0x8000000000200000000000000000 0x3c0241049040000040000008001000 :=
  splitAt 1 101 0x3c0241049040000040000008001000 part420 part417 (by decide +kernel)

private theorem part414 : Excludes 0x8000000000200000000000000000 0x340241049040000040000008001000 :=
  splitAt 1 115 0x340241049040000040000008001000 part416 part415 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part452 : Excludes 0x29000000000001000000000000000 0x7d22df349248a00002208000001280 :=
  finishCode 47 0x5f359b8a065113ef13271a385cc82cae0854c54498837bca1732769f599e10a08ca2e68e89305885ae81f01561722f33e98bcc2f30c6de340a1759acb3b668c385b84bc68e1636c5398615a3609390582a8dd321ab79de10d6cf608b78108b82366e7435b64314e63476e9aa262cf32daf67ad9a1eb0fa9e2a08e129fbd52c1786cd4c59a9d37c61da9e0974c59a9e206cd64df3c52cd97d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part454 : Excludes 0x2c000000000001000000000000000 0x7d3a5df0a068a00002280000000680 :=
  finishCode 35 0x194a042308c336417f82f42bdb8e5ed6dd18b7d39b75b8c62f40f423f9bcdb7709a8b205ed33cbf62fb0e2bf70bec15edc7448da2cfe9778ad17f0af0899a342545f7514c0bd25b82c463622e61732d25b0b5863709440ab1798c5496d510c9755b1ad2dae420709e88b87db4b5b1869b09ed2dae462e7d3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part455 : Excludes 0x28000000000001000000000000000 0x3d725d308048a00002200000000280 :=
  finishCode 155 0x1a8ec6835834f84be5a2410e312d99485fa24d002fe1966689edaf5a3d24b6bca2f31b5a6cade13a1fc17f20865510d5ae6b456e36eda24becd7368e4b6d7359a845d67adc64b728ac44309ea3f88152f50b7e5b262ed1e4c56e93f7c25b45b42c134cb66cdb4fa45a6d69e59b842d5ad4e5df612c36b66d28a04920994905f0226d1e5978b35d11714ff6096d79bddf3dc09ff3e7b73c02e2da4bf2a2d5add34934c3844b73d84e11368d0ba545e665f42762ae4ff7996cd6e374481f3e5d125b609b4685cb8816cd7ad2f84b843683809c02ec2f30f31af9f686e39e5c96e64e2b5b257eeb45b4dd073298978adaa3d281586cdd0b896c24c25f096b31b3d99325b8abc235ee12c4b732630a4b730220dc74aa92dc55d96cdc769e4b630a98b59a8c284b92dc42d2e4c532125b9519937a98166d361c4c86d3f5968aa1a3c1628a68b334bc224c56c68e16369f610cc9d99b0cc15e68ef89a5510fc2568adb3d8697c118dbc30cd4a2f7b455da3db198c324eb667687b0b9fbbc0d0df84315b67b65b3e0b0bb0ce13b0cc31a87f6cb4fb09e59df346142c611789430ce87c96f67b13268f66b610c4cd9fd67b167133697346d9adf309600bfa40cd9f1ca2edd28a769b2d1cb892d994d22d36a3d3bb5176d76f7523a1b496ec168940cdc3185e6e9a0049d696d9a9fe48eb5b684a58b04cb59f18b8c13b04943c5d84ec332e2c2ec330b8be0cc3384f2086044adad69a2e2daf123c4bede70cdb0cda3097844f82d42bf43e5396e38a5185453a859096c2760a37bba295a1788b379798653feb3f6f39b76ccc2245c4636617 (by decide +kernel)

private theorem part453 : Excludes 0x28000000000001000000000000000 0x3d325d308048a00002200000000280 :=
  splitAt 1 110 0x3d325d308048a00002200000000280 part455 part454 (by decide +kernel)

private theorem part451 : Excludes 0x28000000000001000000000000000 0x3d225d308048a00002200000000280 :=
  splitAt 1 108 0x3d225d308048a00002200000000280 part453 part452 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part458 : Excludes 0x8060000000001000000000000000 0x76069da8c2583c000020000a0c0200 :=
  finishCode 125 0xda6c3414cb0492a886e883845099f1d485bdeb47601b478d6e2b625daa5f56a178a022ad97cd536869fe51a6b7aca6996c619ca35aa70b6a0297cf8ed526b764329a5d402d807425f1df562adaa67c77659279488abb478a36945315796d1e6a989961582adaa64f7936df4ca37994874311b9ef0d6b68f221da3c98b2e3657616a21bbdca2fb8804ada91d1fc01f4aedcb2bedcb3c5d30cb0d50b845aa21c3dcdcb4a335ac11298b68ebafb8e64f24954b0284a96d94d2bf4df15b4df684cafcd2c089b146bead91b9608177b4430818f2ed1510e96128d019a2b5e7e8fdf54a368051aa2f440e84cef2046dcb60b2f9b9743d134d6c2aed1698d5e560194591b960ab443b0685c6b730f5a3cc5da4d2c26b6dca15754b86e1aa67b71796159e5a3cf16dca4f6dcb055d28c036fa698adef30af5e2f368a63a108ec2da676f772364af2c03a2d7a1edcb28d0f979658422d796d0f7a4b0da174c368a2d6bcaacb458445adf43c48e63625ec2d5c39aa743d75ee184b2583401561073cfa8bbea946888d68ed934ce2f748746e1b9dade8814ff5237d3a9262356e9b47961945db9e539517699a636d165c5bdd3de86d6f776581b65bddb968817b117b247acac2ae5f360f6e7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part460 : Excludes 0x8020000100001000000000000000 0x3e16dda8c058660802210403080208 :=
  finishCode 79 0x6e3b1a0e05806af08acb83d1eb21928b230bc9308e1f1987b4dd0b9616e5c259a5e2ae9bf08e0291016a98691f7a49a6f0459ec66350fdb962b61c5ec617998d92441ec61071f798d4196e596187de61dec66878636078b325b1eb87d44358262b691ac6b5a1c58257b5126495400d820622d48496e2945e708eb4d7b1803622e1c70b629496e5c60f5a3f2f5437c2db3f61725b869b42c3f405d7b708e2ad0dee18497190ae2cd125bde6019715df98d6a79bdf694cbc52110512e5d625d6d96f7617a1ee62f42f42698b6174377a55011e11f78d95d0ab5213479e35f0c47e78d95db296b561707f9f0de8cd1f816834791270b63e99738698a55e5c2797b5bddaa6d160c25c1f566d544925b7a319b17997edf0d75e25b25b9b55b5e498487b9a9580542575e609a79a09458110e1f67b14eb5b14416177d5d0ba1e661db967c38ad457179a61c9ec96f42625b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part462 : Excludes 0x8020000000001400000000000000 0x36064fb8c15a244900280002888220 :=
  finishCode 61 0xe66e339b4d04a2f0a2f2eb225aee8d5c46b91aa54e5126b3302da635126f16671468c38cd8559adc8931025b2f46a5bc0c8550a1e891601459b4530d1d126cb625bb3325b9796212f3442b0baf2e85d666f6f4adcb0c48b0aca6cc2a2f390e03d1c68e8b268f0c3855b0ac98b12268fc0c8522d131b364a1fa2cc3bd85e2f310a6b687e3573549add22a012b4b0c488b5cafc9e7354bc8842c68e157649e583401526a7226cb9d10a12a4f74c0919e961a656d10dba663491e5c6869b474437a59b542ae5c6b4735be058068e56e97743987145735b98d820e5dd3f918b0ab (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part463 : Excludes 0x8020000000001000000000000000 0x36064da8c158240400200002080200 :=
  finishCode 173 0x48732657596864532a8daedcf4453985e656c2442777190601981d16491e973d0b0a960786996cde96d2e2342a6c0892a2f3d89a3bd1e12cef6dab31b54bc642408b331b221855c59c48d1ed2ef696fa6d6edca156a734489a3c52cf3ea732b68b2d6e89335b9a3dc0d1e8791878916f7879585e634cdd0eee190ce6e220a73605172ff9e46585ec61ee6b51ab02bbc203d47ef03146357202ffb478d6d77f42eb33b477a36b5961b435f4e6349a57b660935b425a5cd4e658640356b874b1a03cc7d2bcf02f47547a394e4d6c24cd6eb46e2a034667efa7451cb8b0bc4b73e98c5d810de44b6171598bfc78df4dad510ed1b0905e096ec1a0ce0c5c317ed1561b695b6f77a59e346ae0990ab85fe31b83279bde56c22ccfd77e95b7d3327b499e95dedbdc6ae247581234bba2cafd9add78b05c3216418b19b82ad4b697719b0a9a5de6c94557818556caccde6364930f2968b8cbbe17cc0ed9289e847e5c1316c95409b981c2a690ba35a6b6b8c3994cbf69ff03d9a3cf0a36309c2d94d6d798f5fb98fa536c1286099b5c5fee02e34598c3b42d2b69a70db60dcadcc6b73c625134a4042be0c9ec2d3371879b9e61607f5178cde09acc1ba2065c57ec2ae2dfb06c7e4c86cced341678185b0b8be98b8c9cb0390d9044c5d64c3c2f32eb2e6bf62b31ada26da1712e6b764d0b824924190179a5c4c657ee61e31997728da2b661cca65dd7ee1ab4d39e8de06ccd7acd6d15d0de32935bc8685afdc6b712f226c568d5cbbf2e331ba0b0642986b7d8bc4c5c6536570cf16a3568af24329a5de576869865a6d31a65316b2f5da6cc68d5d313212a9ccb8d90987982657e (by decide +kernel)

private theorem part461 : Excludes 0x8020000000001000000000000000 0x36064da8c158240000200002080200 :=
  splitAt 1 58 0x36064da8c158240000200002080200 part463 part462 (by decide +kernel)

private theorem part459 : Excludes 0x8020000000001000000000000000 0x36064da8c058240000200002080200 :=
  splitAt 1 80 0x36064da8c058240000200002080200 part461 part460 (by decide +kernel)

private theorem part457 : Excludes 0x8020000000001000000000000000 0x36060da8c058240000200002080200 :=
  splitAt 1 102 0x36060da8c058240000200002080200 part459 part458 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part466 : Excludes 0x9000080000001000000000000000 0x3f46a924925ce00120209020001220 :=
  finishCode 87 0x552e1007259268c0f0444f8c74d3768bd6a17610b79be4c17345ac4683daf5ab2f8bbb342959939af664e9616c398d97da64ca6759202950919bcca666a799393adaf74140a458369344bd8d345adb4dbceb0e861517b88b8cddf25f4ca3e41b07ba5dd855f4eb3d08d6154ff821ca558576889ede7361da794dbe9c52b30a85ca29d0ef67ac2b487a4d183ca566bd9618b368f5e44a56f188a06b0a567d350ba64c5de61e347d6049d32769ea6b3033ba849cb3849c8b385e10facc43e9c17253769f440be1972d327a07a3bcd16ba1a61a10268ed5a532d7b88347a5c4a6c7a64c56170934c5825c237b1b4be126d67b48a116a0aa4e53778781acf69cd40cd1ca66210400ba64dacc22c88e2061ff6b350b3cf808441531422d101ff451bc08429f9da3c4fa2f77818782e69ce7d526b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part468 : Excludes 0x9000000100001000000000000000 0x3e02b9ec9248620812218480001208 :=
  finishCode 41 0x311a0b8612b016b64aa056cf106e34d18d29bacbcd35bdec2d5c36b941b29bd43c8c50253714359790da90be7ed144629b6b99b6759a86018a55de6869993b2f8a57bb0a399393ac28e79a8c2593802ab594d24beacad94d9a6b3299eb493296b941b5fb685975f09542420420661729bb0304ca06a6adef2efaebd34994c1022e20ff0a6a62d94d817ee6c952727b6d985c64c50a3185 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part470 : Excludes 0x9040000000001000000000000000 0x3e02292c9348200000208008041200 :=
  finishCode 83 0x1649e612f954924d2982fb0c2c11ec653934534db83eacd9a15aa37366bd8d6063652d0a9a559e4d8546160a9b86d33958d04a0a6e9be8817b17855e52775174e1b09d7942b6f0f9f3648568acd2d74b649aa0b2c3440a62cc994dd95d4baa5215b48b5a4a93b5c856de1b2629b51bd079b24a6f5154b84402766156ed981c276d3e6ed28734da65c34167b37ba8bbd494cd37d2d6f9edb2def326def281da7845826d84a10ed674b6532a1304e9a6d502466d929509d97d87bdb5d3fc9f6c154b856028e0ad615ad3d7adb36d3e29b6d36f334db4f9acca6d46f71d834d8a6d48e34d34db5988d461338ee7440e83d37a8494694dcf05ee50f087b3d9b8ca567cd6f76d9a45802453fe7bd8a16d36f38a19f3d3165b16f37879a66d0dbcca4d4be (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part471 : Excludes 0x9000000000001000000000000000 0x3e02692c9348200000208000001200 :=
  finishCode 179 0xe85e3f265509644c5aa522b13cb8296d13f3032e2bf615213a83712e93db0484cbc6cfa7692d6edaeda6dda15f34607a2cc5b4d3581e9a026c0b268adba16b61291c0be4adcbf6a36163085a3a64d40dbdd0d65d16d92997b196d422c5fed36c1b1ff86529b98f7c35fb0b96f7975d40d745ef549f1178a422cc16a30616b042cc2ef6322cb0beb30954b26d209249a304d84a836a732e212268a69b7cc805cc31a89f47b296b00cc38c6a0dd2fb326c02f9e13f227df3113c0a950f9f07095b8d06c5f5b8e18d8a4e6f309f407a643eca52856c0e13f14b054857e0dd496122a7289fa0da702e053266f2e885ccb8cba21732039a3cdee1733272e8ed2a8bf6dcf11cd97b79ae884eda6d2b2a0613f5e2c830b0548518c3c16f2d704eeb309c0dc5f2e0d7305885ca27d526167736e334d781aca577ca4f5188aa36bd2ed102de6132c0f65f281b7bcb7cde6c0eddb04eb6ec69b7018382d663e4e16f717d41bda04ccdaebf61370c3e12c97818582c46166e3945d4be64e09379909dc2592a970be4d2982eb1a684e8c2a15cc2b67a15215e69b123361d9e854a2784fcc2a1330be9a6df2e1a00af5fb9f0ca6e64e03f98d6c9449ec52296e6c929b51b29ba56e7d55fbac045cf02dee68ef0301fda1b5b94ceb33966b22794d949843c86aa734d2502d7045849ae8c13213f0c3d92a948ac61027583e7ab53934518d4ff9804245b666886b0ba9a6b0ac16f0c68c2c3291846c90b1a555e5cd1e64ca650d4d1e29b9ae42e6b1a0ec0c3d2dcf5252abcb4c9be6c68e1631f4b59bc0845be6d6308f8f51ecc0c40a8bb722ce7ab9812957cd879a555ead3fc2166b9967435293 (by decide +kernel)

private theorem part469 : Excludes 0x9000000000001000000000000000 0x3e02292c9348200000208000001200 :=
  splitAt 1 102 0x3e02292c9348200000208000001200 part471 part470 (by decide +kernel)

private theorem part467 : Excludes 0x9000000000001000000000000000 0x3e02292c9248200000208000001200 :=
  splitAt 1 80 0x3e02292c9248200000208000001200 part469 part468 (by decide +kernel)

private theorem part465 : Excludes 0x9000000000001000000000000000 0x3e0229249248200000208000001200 :=
  splitAt 1 91 0x3e0229249248200000208000001200 part467 part466 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part473 : Excludes 0x88000000000001000000000000000 0x761b39288048280020200000000220 :=
  finishCode 95 0x7036984b85917817e6da6f6f9f685a82af2d42caed149c698d44397dac188373d40d1cdc617b2eb131d83281adc7786e3d585ac3cd47a4b7a1f65ef9e98b4b5ccab56c40da16f9ef5617e4b744901b6d828024f05fe16d9acb9b0bccaa62d2eac2f2e73bca62cc585eb5692dda7d2e64c732a17e17f131ccae22c164bc5a3c3468968af544376dd820c5c5b8c9c696bb47363951acc585e6550dea164b8221938cb872eec02bbf616cc68b8c3cc3464b63475a3bd5938dc280f4b030092dd3266c6dbaf574caccac1126c730343c8b8be6b00c1177e99561708983e65354cf0b5b76654247112d73729a585a8d1d930924be520626c0c1f052cb5d652c02dcb32a4b7541b9634b96b827e993881995535b0bed1c5cd80709585e4b9ba21e6d0fb2f25b32999522fa2061e695125bb2d76685c1132fb663262aeec3cca8e85d96d2df68e4b79cbe5902fc2d618d975896e9886f220b0ad32b70183a6542be1c6345995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part475 : Excludes 0x8000400000001000000000000000 0x3e72292080e8204000200004000a00 :=
  finishCode 165 0xe0612c954a2500d573190901bd84ecba332a12b2ea86b166b774ca84ac4ccc1ec0f32ad9b610a97a62e859b9b6ea29d6970d230b1666f7a0b05c3106f7586e3942e654a2665628f885c219f55b35b76f9907605faf6d4e6d32876f636635a7b56b66a1bd85f69769f32b107371ccae17d84a06ad5abbe5368766eb7cb848265660145342b8b3615ad3d14c20e97798d99543bb35a65741acec580a6c7868816b399589737b1e1933d0d65f5ef66542fe37bae1accc392417c4357cfb42d415795125b16a5b99388599af2d2d607f4c6a82cbca89286ae494372d37c10f327687e83d3255602d0ffd0724d505785b43e8fed156ee5c621247221192dd32769ab3f4ca92dc4b92dd69b85b438db298daf2d8b64ccacb632ef6834ad980da7c4cdc3306e78843529b94e69bdb9d1667cf96180ae92741d4269bf11a803580f5ed6655b74a6e9266175090917b1a656cd50eee1a8b255358c037c8014a9b1d302c2b2fb1b1cc0b4cc03732a6c6c2ac2b6b281d87414ac37cf52d92bcb32af532f2b64935c9fe6c6baf4c6aefcb894a92dd31b69a6b6bca86f40b0620d8db36295995437b2b9af5b771168f27fb7481a94abd5c4b735ee85e11a1b94ad4280de7262a1bb6e9b1e621f65fbd0b6bd4378a56bda246c2f6bd283ec583116443710d97b66565ddb9e2b40d603f9959036ed84a4b732adc6bda0af2f309698d9956e7a636185db4bbcc3b7be85d31adaf64aa412d868b7c98794e42fc636e013b12da9cacacd4ad4edb212b32b7ca605fcafd0e286f85f4b8843caec00a0030e312ec0f7050b94e49de5760bf871995cc5f26565df0bf6a7846d7461c625e65698ef7363b6ca70be7a11c4ccbcb200bf90dc96f42650b5390bf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part477 : Excludes 0x8000000100001000000000000000 0x3e12b9e08048620002210400000208 :=
  finishCode 117 0xd06a31198c2220c6e616e177701ab5d7a64ed3466d80640baf36baefaebdd8c26b371c0b214dd22c0d932f2a87a998c4cbcad6adce983537c5ab6abbf8c4994d221e6d074c5d0bb4177f6d96e70f1a9bcca5dfec089735a856c47cdaa8876036da413dca1e6e7616b5eda4c6520fe6e7107ca1ebca52b846d582b4614db5806c26d04065332933653758e49183c96e1896e5301896ddfecd6d3e1de8a56b55277b50a5601b8401806246b4d61587db42e64ed362cd77e533b2703092a343db6a85a8c29b6dc36988ec141c8ab349235ecc9cb7647f6922e2c2f459d84b617b44c59851851d84b262a25b5eb44c68a16a31a89770926d290f77452cb9a20be7bf28fe6177875219738a37878dcd105f842b537c47c5199485ad0f748da43ec52cc2cd7a4b7433e179b9c16b2e703fa20ea37154883d02a628160160fb6621b6698d0ad699a57deaed34a0664e02d88bb35891615e05b2885031173e78c69aacadcf9f31b303a93be7d6cb04c9c846bca15a1634c7bda635ba579698dd64d25c65e5885347535b4d896cd1e96789182c4d54616 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part479 : Excludes 0x8000000002001000000000000000 0x3f122971c148200400a00800100200 :=
  finishCode 71 0x5b331a0995da6a0d8cdce40356c034d302bcc7b79ca8cd9b2fba16f3314b379a2bea1593268b213e33731f02bca8c4b722c84feb3515409f9164a1ef9667299af2afdad8d0e2d924b6a0712f2eb2d8a62c5584f8c4940c4b6163b4c85410be6f3601363373c2670ded70e27b2937a34cc7eef46d6f616a87d28cbbac2b9c88379c51ea2ea5e41f3ceb618c6be4b6ea2a944d54b26205ee6156f70ad27dce5a3d2d6312c0368f052b4cc40d216d617bb4569988150f6b9acaecae6d727db268320a6b30a9b19bdc40a3e50b60f6158b3b09db0df4dbce5d581f7188be552211573e0d9ab07b0ab03ca6afa7ac8ab94d579626546e266347a1c62ad81d81eb337c194cdf4c5fd43e3e5417295363 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part480 : Excludes 0x8000000000001000000000000000 0x3e122960814a200000200000000200 :=
  finishCode 137 0x380c33b4d059309609a44cd32a5326f66bb5037bc46a11562d66d987998d9959455e464c5b4f18d42f18da656656c2188f0bf29935db05c2a10cb2dd84fa2a9b1d51e93460f44b85c5b75e4ec198b37979a265f512d12ec2d9b754cd12fb15080221d99c836c0311f146baf599b4cd6870fb32a3578374b3af2a7f935ae1b00dc2c1507643ca209a99b9b0bc952d86612953379e17ea31132b4c5a62844b6ea208d5e72004f6bbb3e6c3ed1174cacc5c88298b32ba8cc6106ae23e5d18810319745315eadab6d0b08b4c5295cc044cf7b2e689e053291c40cc5a9ca62be7d5331041aba65577d85f08a1f4b9b71cef2de714d84894dc10e3579c3558859ad2eec2ac036ca49a1ded3e63581ca065d6607527459b317c5bba1f62942a506665462513f21a8a4762c83572a335ab0acc5cbbaf5f5a79a5ccaa1aaf5c61332af6e356e8435827e656196435ac4cac51c13f11f45acd23928a4046c1236c800be829d317102697143a172d8a62c3ce8398ca73d0cb69f142fa71035a7b03a628be848c31358a45922014a1fb0008bd8eebd2adab72da7b0abd2cdab69e98b0bba879f3c98ab82b6adab69ec0695b42ddfd066604f760098b69f617b4cc5ada7d9cd06d2514c4437bd981c9dd12e62600d98b087785a55995c2f0bf5e5912e9948b65809c632560709f86da62585657e28c9dc9de607989a6557ac9dd8560bb0a997758542b46161c65ed8999950ad (by decide +kernel)

private theorem part478 : Excludes 0x8000000000001000000000000000 0x3e1229608148200000200000000200 :=
  splitAt 1 73 0x3e1229608148200000200000000200 part480 part479 (by decide +kernel)

private theorem part476 : Excludes 0x8000000000001000000000000000 0x3e1229608048200000200000000200 :=
  splitAt 1 80 0x3e1229608048200000200000000200 part478 part477 (by decide +kernel)

private theorem part474 : Excludes 0x8000000000001000000000000000 0x3e1229208048200000200000000200 :=
  splitAt 1 94 0x3e1229208048200000200000000200 part476 part475 (by decide +kernel)

private theorem part472 : Excludes 0x8000000000001000000000000000 0x361229208048200000200000000200 :=
  splitAt 1 115 0x361229208048200000200000000200 part474 part473 (by decide +kernel)

private theorem part464 : Excludes 0x8000000000001000000000000000 0x360229208048200000200000000200 :=
  splitAt 1 108 0x360229208048200000200000000200 part472 part465 (by decide +kernel)

private theorem part456 : Excludes 0x8000000000001000000000000000 0x360209208048200000200000000200 :=
  splitAt 1 101 0x360209208048200000200000000200 part464 part457 (by decide +kernel)

private theorem part450 : Excludes 0x8000000000001000000000000000 0x340209208048200000200000000200 :=
  splitAt 1 113 0x340209208048200000200000000200 part456 part451 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part482 : Excludes 0x28000000000000008000000000000 0x3d2255008640245000011000000000 :=
  finishCode 147 0x1b0ca5e281a0619d46e2d034e66f22cb04c68617e17b0c5da02be183799985f196890058a71d4ca2fe4b7ac7818d1d164d1e88389962551e767c1b4d983626708643fb454df2750a7a22d07516719acc25c02f46366170b55f1ad4e49a8b53b852bcbfe2e311634e80f19baf1cf76c2f68c239e2c53e295824cdc69e609a6f938ed4c28c96c2d469ecbe5d53471a7d65c241604494353439ef61ce995b8c96ea65a05a21984f5a9c36a8aa2cc4dbd4d47b84ef9f4968b30e728d005fcd5ad9aa165b72ffd9984ada3cb2e17f69a5ff2ead37bcc8c685fe32f831b2ff85fc82a84b74a737bb71c41d6a708ada7c39d0025e6ed609a4174c650096e60dc759ac52a7184b84ecddb4d75a98c2c48d4a665a68740169a22e2454e422c1e6d057bd7cf404b3c4a630b3260e367b69f5482685ca2a30a83aa5f366cc0d667b8d05e2e1201971a74e3a22db5c96d09eb33453943223140337347873857df4d0ee926269c6431f066f7b499addb5e7965f532b0493ada4d2bfa0b4a6f4b6933c5bd2da993a9a3d97c862132f836a770aa21ad15f6a61368a70c5ffad351262bdbded4e6d72dbb4d449517c64a22b6b531796d76f7099ad4c5e4246a534498d1d166402ff12dd52181469cb186be98bcd6a6317599ee3597caa224bcccf9e16a8b30bf05b92a9a3d510d54e66936f308ba64e1cef0a7305893a9a384ecdda127945e392fdb5e64c9546342e45fe255 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part486 : Excludes 0x9040000000000208000000000000 0x3e0205249249249040241041041049 :=
  finishCode 77 0x2a259d6077781245e462d4e09540a9983c5dd09e5165f0af8438b3a93d0bf4e768f37bd9a84ecc2b64a604cc13a1531a6849c2cf6ca5d82b617e51b4d3c27a5daa296c15368f0b5c92200ff03ccb7d142d4f213a87d229964b85e2d96098051e502b617b527c21a99c5ee63e85f289dc68109eb29283091a95db9d09c5c68820ec2eef5f13e84b8bdd5309e7d56dd34508ba1cc9dea81231a6be3ca6b04167909c59e09394501c0d6f3da983a798afd80c5e7d552f8d367d5307289b478a26d964a64a029df1eb4728d079b35b09ecac2a60adb43517acf67b526bb4f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part489 : Excludes 0x9048000000000048000000000000 0x3f0203249249249201009240249249 :=
  finishCode 153 0x168a83655078f29b49a412494034d7b19075b8e26d3f67d5a03d30966ddc23b0b4115b8daf6c236a5a7cd0e2f6f3edbaa5f0bdf61f364272997b78c8eb11370ba93e992c84f60a4461ede0a528716727bb094294a07096287b2fa1b485d09f41b47d58c8ca35ec6993323c21a17da1664ea940b249209346a6d27869b84b14393d852cf9250f587d585d429d3e607f175539b0945dcd3427e3111b610b4bbc9cc08bda13bd2c50f4c6978fc427425ed3e03f79f6c3b65226014aa471449898f3d85b36ec2fc83b3452f85ce26d3cec86e309627b293b43803daf411f09cd34826c2334dca680c8e299993b43e85f6853239a5024964aa413696034da4342d84a7ea64614a50384b143b42cfa662a0ff5889b85d429d4ce325b4f9e7db8c25f29a0323a64ca6e64ec219f5626c21689baa38142e0976dd6e328f948c294a6e92551f5629334d2939e8e293115c23da76260532f9b293bcbcd873db991991d69ea0734aa4920964da580d367984b14393d87dd84e14a50ef6f3bd801e1283fd6226e1750a7c2585d680f6320eb71c4d94dcfaa9fb286878095e7cc0c9ec59c24c25ea0382c8dc72fb3d18528b9c45e956a4700a9448828528f6d84794c23a2bca665f62a607389bec65309e7cd29917b8c8db0e7b7323 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part491 : Excludes 0x9048000000000009000000000000 0x3f0201a49249249240201248049209 :=
  finishCode 61 0x8c50321b8aa411b89fb04ea0ea13d22b1288af890428c5ec28e895a2068af8a16ddb8592982f704b84e8bdcd0f69e51313701ad69f136dbb0c823d0a6e89b68507907307f85eed1e4e77b1a4585aca26993053582654a627b34d8fd6694c921a6c2e2f4704b9f093e944c7c29e6dbaf8313e947d93095492447c51e69b84f053949c507040c0e784923d26904315829cd3429e6dd539a6d829cd3610302f03553928f80d429df3e8a10a3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part492 : Excludes 0x9048000000000008000000000000 0x3f0201249249249241001040041009 :=
  finishCode 167 0x2a0c1544b3a058341949a6d1e8a470518b9b6ead1c4f6132dc7587a393b425c9f4c9689550201f263131376c38b5a5f5f244dd45687b8b5a44f041eb4568325727b865a586cbda0e92e85fc2db474fd7a585ec2349ef0884e7a3048d1fbbda9c8b8d65f34b2491ef66ad88f34d0a59e8c29f0965b11613df8a3f392897da61854e23c214c6e8afb2b9829aca1efab44ad520924b261269b4b01a6cf1f1e31553928727b78d9f24294a1e8fe3158afc80b2d1362f684e2eb502319028785ed09de4e7b70790a7a2d6cbca3ea00b8c4b24fa507502682c344d848a79c62f4c9a908b0b8170c82df8bdde8c4bc4de9051305193ec08b00a0185cde785b1debea83983681ecd7af6b69f35e852ca2614c9a049cd0ef3e53660612ed2f273da7cd862ce4f736e84cc13b40704c3436d0f2178a9c27781143993323993a17e26c50eb04fb3eaa94d0e652b4926954b261209b4b01a6d2306e31b0a5281c258a1ecae86d8afac52228e8791730a5325a2861945d6325895a604ec12f0e73cfb71be7c147404279b8e26c215486779a04c2510c89b821664e50316b68593dcc6de368a978129ba811098613cf9a646627a0b478a666063bfd03dbd0cb16b2c361384fbbfc40652b0f716ae0da5520130a03e4c626d86dc7347c7853d3adaf708f094a6e2d3d074eb7912030a781ce95c7cec812f3d1852cc9d85b2a2f6a537612c14e14710c23931e64f095ed4296 (by decide +kernel)

private theorem part490 : Excludes 0x9048000000000008000000000000 0x3f0201249249249240001040041009 :=
  splitAt 1 48 0x3f0201249249249240001040041009 part492 part491 (by decide +kernel)

private theorem part488 : Excludes 0x9048000000000008000000000000 0x3f0201249249249200001040041009 :=
  splitAt 1 54 0x3f0201249249249200001040041009 part490 part489 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part495 : Excludes 0x9040000000008048000000000000 0x3e021b249249241201249241248041 :=
  finishCode 137 0xd830124d078e49b8e05611118b53645f2a8dbb08dbdacc7a0e8b3d31efaad0759e8b3d9ac1165ea69b278c6278d0b4bea7e842c36d15ec2b29cd51ab66f334d89b80fc054064bd4b8ca66a92b313b8bccc7d1364f75a99a6c01c131f379991a5ecc2b67aeeb27984bb6ec42610bf2eeda998dda9c51b6a742f856c93815844532d4ec813304ebdacd869cb4626134173821d42e17b41d983d8565399a551ab66f334d043a25617e5dd299aa2e0c2fa156def562d96411ba5642b4456c2d1733239b0e6ed50fdc50359348625230dbb281cb1845d9ac4dc4acf328def26ca848c6b03d4c2def47f0dadcf371da9cd0ad4e03f13724aa0bed6a669b67b4beb6bc53360aa143cbba1572fb0bdca8cbbb6a748984b5cdc612f6a75a7940cacd6a7549a149c30a5270c6bc8c98f4d32434dad4c5e5bce27be0492b088aa5a9ed2d3e1794e509d8c6e79103d984626931f1468b9842991d8432eea9c94cc02f69e15b54293981cd36d262ebb4f993dc6b3392b314dda7ca529e7616caca9ac086dc7545eb85f42ada160ad323 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part496 : Excludes 0x9040000000008008000000000000 0x3e0219249249241241049041048001 :=
  finishCode 83 0x30e0259c92b088a45a9d529964099827424e2759395e4687b6b7167aa29cd4c67ab43db59cd2a93c8c4c226e427085179a98d3f585652d615909e64ea496f789b085aa296cc2b2a34d2c99c34d41ba64d4a62999a370bd40c20617e5eb2997040280f27056b79991bc3c536277640978296d26c2f5298296a831b1a2855c39c2f6dae29f409a5829158aa4c2c8dc7213da185184bc030661633230936e3173824dbb60ad98f09d98f859ec9546ed8d15a9e98f3e941b6b38a65bcc6166dd8c6e2d4e08b8a96f742734dad4db9c5c40de7abb53171644406364ff1430ad82ae17b27d323aa4f258e3450ad18d34d8a4d01e (by decide +kernel)

private theorem part494 : Excludes 0x9040000000008008000000000000 0x3e0219249249241201049041048001 :=
  splitAt 1 54 0x3e0219249249241201049041048001 part496 part495 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part497 : Excludes 0x9040000000000008000000000000 0x3e0209249249249200001040040001 :=
  finishCode 61 0xe0124c92b0bc985a9cd2794c08509985e42aea3fc2734da617d3a1b4d341fec02f72ee9918afd2a2bbb5460f9a14d341e66859a592a94ca404ac2f213a30b272c69ba028d9f1cc6e7b58214a3631bb244269b45118a64d341d615907faa3c9d326b9ec2a53703acc9c32d31ea532b20ff03cd52696cac5930866f31850a50a9a03e3c2f6dc73273eae16e11cb1cb66ddad7aeeb4a6b71a85d85abba5365375e2b111b44d991856854cd225686588d17d32398541dddfecbe2bec1b895c236f7539 (by decide +kernel)

private theorem part493 : Excludes 0x9040000000000008000000000000 0x3e0209249249241200001040040001 :=
  splitAt 1 63 0x3e0209249249241200001040040001 part497 part494 (by decide +kernel)

private theorem part487 : Excludes 0x9040000000000008000000000000 0x3e0201249249241200001040040001 :=
  splitAt 1 99 0x3e0201249249241200001040040001 part493 part488 (by decide +kernel)

private theorem part485 : Excludes 0x9040000000000008000000000000 0x3e0201249249241000001040040001 :=
  splitAt 1 57 0x3e0201249249241000001040040001 part487 part486 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part498 : Excludes 0x8040000000000008000000000000 0x361201209240241000001000040001 :=
  finishCode 135 0x6539978a070186769900a39094d8cdcf39d87b5804709df0d3fd134a3dc16c4ff7919f25b742a5f26a3f97e5b765b1b459636ed289c8402416434b5279f4c29e17eb252ecfa6a3b136a4f137287aeed905ee8736cb533887990fa64fb31f528ad8b73da7c6272c6def4c0a982b515c9de50f6b0b1d30a79837d13365b12ef87c0c26424934b25c0db510e29b6eb249910da96ca4a6ec0fab03fda99b9d32cb620ff6a65366eb1499b99b9d34c61aea2acd7a1532a33bfbe19478c6c51f24c62c223e407283b538a3ec591ef645542f6ad9106286d4cee6b498a114f171b537bd90b6c9d85299e6619c1b4a3d75e6d74c7853de651368ab457d0702c9606cb36dc1b9f1ed4d0de2b4a6e6a5b0440dced4e1677c7233ad4de8ed4e8afa5729b925514e6615b4f8976db2773456db9dd62776cb6eb8d170885f3ddb759bd9b6d010962d62713637bdae184b23414b609d6eb6cbb06d381ccdc616cdea6b64f650f480119e2f4270b4295bd49ef11847441da9a2ae84c492dea8ab300b7a85292ec13e15614b0b98bacf17656deb60da5e294e35b28d7c79e7ea57b297d589b8a9173a0443d68a5df4c4da9d83696406d91541c6b294414f74f7a284c5c28cd2d0beb53b2bb03cfca134d715a88285bcc98ba1b509e8edbdde2e4397d3 (by decide +kernel)

private theorem part484 : Excludes 0x8040000000000008000000000000 0x360201209240241000001000040001 :=
  splitAt 1 108 0x360201209240241000001000040001 part498 part485 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part501 : Excludes 0x18000000100000008000000000000 0x7663cfa182402f1003005c00400008 :=
  finishCode 37 0xd8532f164d4225a2ad530960bf6079598d1c2ff0be0b5ca532c002f77142f0e16abfe17ebe32ffc425086ebff455b0bc55c17f2ffd92f13c765422adbd64f17c744d013a214025a557ad85661744dd4641e360ab0bfa42cacf1a4b6c2b317023e13800caea5dcb76be216af8f05fc55b0baf8cbff900759f5542585c2d5856255 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part503 : Excludes 0x9000000100000008000000000000 0x3f23e1e482412618120014c0400008 :=
  finishCode 85 0xc6541f92825592562c96a7007d5a5f453e23d06d9069b2ab187b0bcb7a5fd2c72aad7b3033e3a5fb0bb2223d2fe8a19615b3a69a58659d06ec93c8026ac0570c6b46172bd680e837ac5c7828e18ccdd8252ce4bd86330f8679e2d78c0ae18f095475f1e96707334db116cd405ad94d6a669a53669b594d21cf229d73265365272dcc459a6e126990b80c6c82e16a89354609ad4cd3543e9939a9d0acd346360b5c843350c2e0e729acb7c5060e7692a6b141d34d6a650754c24d2e1b8b26b0d372148b149a29853c51f48b140bcfbeaeb01ce77996b08129b4537d5b09e8a50a534d29b978cd36d9b8c86a1e1e86777f27b29ba6f829e9be78b51528fc21949e2962cc29e9a68b529bd45c1f184f4b0947c4f9a38b0da1a14652ac13356c51bccc1474c29596780bc3feca549d4a5f56c27 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part505 : Excludes 0x8010000100000008000000000000 0x3f33c1c7a244269002081400c0400c :=
  finishCode 71 0x5d329849a630d76a1207212dcb7d2a2bd666f2e3bc5b63c31947e2257678b28f44d455c2597ae19a842b5f99855e2ec25a6997e463750f871a3947d2308c29e5768a5a579af694fb150c4561155a568678b30a52838918a3c0ce109b5320313786725b42f920c6bc5cdaf4d36a7a85d792bd8552bec198638cde19c96d7e4637195096203d6a68aac030ce4b69c72fc851a2acb35129b5a6947b07b0ab42d4e283b33b29c19b498b3b538a0ed365f9951851e64d38cd1ca0d0b699505c7b096d4c28d15710f1737ba25ae3d84b6a76a73c5854e2290f8747632868f8cb2f28f8ada63ed4de2eb2fa57ed4e1c6cbe8b333788bb53a22ca3dbde5216b778bb5395fa62e79188bb53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part506 : Excludes 0x8000000100000008000000000000 0x3733d1808240261002001400400008 :=
  finishCode 135 0x6132974b2630db6c1a837b51b9a962662b6d4d0dca6ed4e44b8990bf896c1fe6eb4e3a5344937bd6631de60b5373b530bfd40d1c5372e7040b0b9b9d88d634068db54a6d38c2fe976c279616ebc279eef08c597b1101ab684c04beb3d03d5b1b358b308169b6cb60f9dff415ed5a1e6c56f54a99dfe926245776cd6d131f2dce13b65acbca8b0ab62a718cdb62dcca46b222d49e29343f6f5ad4e2ce48d4b5a9bbfb6aeb3b0eff2ead9e949aead48b539a71b6ad6a7b8ec6224835764b854148dd72c6d50fdb08c5e662d14e7a397ad81d14d4869be5ff6b74536b543fb0529cd4a84715b4d7352c82586d4d6c64e377ba6f86377ba41acba16ecf3e96384a893132c132eb3d1b55a1fac2d363d5a6bc1b6ab60529cfab4d78c871a264b767d59776a124453a18ca06d4db15bd6f0f23682e12e0dd29a1793d946e12cbab3c8946c92c91090375bd8cd8f6a74a74d6d8f3bd8bcc45d6a6a42d4b2c32eea71da9dd180c13477459a65d35902c06e4b6f630cdb55b9318deb84f2f8b65a1792db65d69a14b4d6fab445b0ba21f631160d4294c34685a3578cb222098fd84b83369313ec128ab85f611bccc48d4e6507846f3285b65f22199f8d18d5ea23900b2f828d7e5857296a7532bbaa94da9cc1367f433851b00cb5d13f833692c2e1476a768d45c2c916719b8cdb00c8066d34e5c76f796788b5979af659db5e8b3ad2585c96e18e8b39795bb5d7 (by decide +kernel)

private theorem part504 : Excludes 0x8000000100000008000000000000 0x3733c1808240261002001400400008 :=
  splitAt 1 100 0x3733c1808240261002001400400008 part506 part505 (by decide +kernel)

private theorem part502 : Excludes 0x8000000100000008000000000000 0x3723c1808240261002001400400008 :=
  splitAt 1 108 0x3723c1808240261002001400400008 part504 part503 (by decide +kernel)

private theorem part500 : Excludes 0x8000000100000008000000000000 0x3623c1808240261002001400400008 :=
  splitAt 1 112 0x3623c1808240261002001400400008 part502 part501 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part508 : Excludes 0x8000080000000008000000000000 0x360661008350a41100001000000800 :=
  finishCode 111 0x7336178e030ce83719096fb066535a9c66d1646acd8f59d8c4366d106de651251f00891ad3571c56d7e69969936cda517d3a18dbce2cd7e4c3eb3595160f61525b37b8d8f5954866e32167b303be9b07a2ce221de94d8836156978b37d3607acf65467af60d51b7d352794d57fe013b4510bb4f8836cb53551b8b3a545855b2e50c2b05fa859a3c4bc4ee17fc0d05c0a2644929b37b36baa443c5366db0e744ab5994dc92a887f4599aaa1acd76deb1675a7b65c402ff0bea53437641a2cbbb0e715e9c7684822cb2a0fcc812ad5024687329b44f431a414dc9eea4e8920f7191bd2c68edbb7cd65522a669787329b44f431a4341c2c689253725fd2021ed050931730858a666f3d054bf08bc8612f97024d983659d12513e2a66a729b860b0d12a107136113439b53d832de686268eb8319b944b6ecd32184865f2e18844988794141dc9adf568a95eb8875e3b0b621ca6e9ce2f36f3887be35ecf8e1de97e536a6a8934e7439979b79df2d4e5f15112f389ae6dd4bfa2362d781b4c25c068e0bd36b0bf8db5f065353634e31a390de4410bf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part511 : Excludes 0x8000400000000408000000000000 0x3e6a531883f2265000381000400324 :=
  finishCode 33 0x38148906c10d6a97c09593b5bae22cd56295164d6e003539a653554498225bae556c25b537bb449b2552206aaa7322cb5ab7ad99cbf26f735aa8bb7ada3c86ea2ea73137b0ca29cc1f22d210a6f66d66b7454d37a96da994dcdbb64a65d328f9f0c2a9c9a2d414b609d6eb52d97ac23660761516978598542fd4b5e1e887895515539 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part512 : Excludes 0x8000000000000408000000000000 0x3e0241588342261000181000000020 :=
  finishCode 151 0x6c320c33648839380deb54d04b06ac5e661543f6b544f28dad4dad51650fe615347ad4d0d5ad6ccc6acd1e25752dc196150abe0375d82d06968934b0a2c8bd92db0bcbcb4b0a1f8d5d95c43c4ae68e4b7c0a868310a5b0cd8d5d80a36b3335b459acced4ed0c0f36a8bfa71d32a2cb03d4770fb6a6f4b5a9a27b5ab5ac13e15768c476368356be32ffc5ac9c6bba33730bc9c712a8b251b0d5d22a14cc21ad4e234254297381532c35a9b0a989d6579cb2b8d1d4e6d4d8545e6975b53973a2156e42145e6d4f18fc96550956f964c2296d6a689e31a2f22e313eaf1cc2e862bbb44a83cb03ca01e6347ca4c9c512a23667701119cac4a2d4f6954c44014e5af69857bb8b55c7a584a0e61688f617993a63d3fed241de23c0b67818b5b4998596389f7217c95191242e62566832995dd88f5dda23e63ed0f34d529b53d6582697cc2561125e7e09926b98fb43c624d3585e27d28da58d2fed0e616a8a5b22cd2abcbc51f356a8abcbca8ca7213f640ab82bd4e60b5a4582c9540af8d1427e601172938bfda3d653a0b2d697f6828458b9df30954315b436d1ed4c635167716a73dec54e82c1672d76a76a743eda394ae82cc9da0b68f6a747b5369a685bd92a960be6e029e6889e2eb1a6947c4eb459c489a6846cde613e69b439c57a78a27d2219344b19e0585dec54a50d728b5730bbc0a93bcbe86d84ef022fe30f3270f0a938bfbc0bc0d5408594554e626e517299 (by decide +kernel)

private theorem part510 : Excludes 0x8000000000000408000000000000 0x3e0241188342261000181000000020 :=
  splitAt 1 94 0x3e0241188342261000181000000020 part512 part511 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part514 : Excludes 0x88000000000000008800000000000 0x761b51088bc02454c2191100000000 :=
  finishCode 101 0xda5938174ca613186f66db780b582f659ec236b5a6b0bf9619eed38dbd71960b862115e60d1a3a812dd4ca1466c785f379a99cc2d15a4b68963472218d1c6c750c6621836a538ad35b443095981db5427cd6c68e35bb0225cbfe48f19fbe9d95de2a128c64c2c6b667e84a87267f1389ada71d825368ad4e3b3d36baa05fcf820eb4c219607d397da5e65366062b5e5e1e53c1b499817bb940cc7e1c60bf1a3aa1b5938a66cf2f4da2d20eb5e2a12833f89c50950e42beb4f979457be6502d69638ab44b0bf31f97fc55ec2f8ab18590dc2fe0120ba0abd8180c1b3519b98d1b61e17c2066e768af52de6c1ab3745ad35ad8bb988690abd485f97fd31360c45a4d0ce2060e2bfe17e86e0df27baf1993d65f16a17f60ac59ada1e1265ff136bfec1a4b71b9af1d97c67f13760ac622e834669705aca6c9c6f82d9748b247028ecb624160fc2f529601acbe00d3716dc2fda2aeed96c9c730b13700b499ad62d657ecb6b3d535a54663e26d77468e5ae6db4e30b51a3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part516 : Excludes 0x9000000000000008800000000000 0x3e02412d83c1345482081144000000 :=
  finishCode 157 0x9654318302556c5f34152fe09c0946d106e9815e3617431859c0fe2df98143b4138b7e9be26db1ea6f14398041cdcf2d62cf67b37bdf34175970dc700c6e44996b44f945a4cdcf4de15f55298e8918b327b6b7b0b40fc83df0e606cd660d31b8fd5395bde03db3db35aa4d2c958099827463634db4385cc23583609d503822c59dbde5148aa4c2691809341d8d1c59d85e69334d8a18d1de9428df045ff69345399e7c2962469b5bb69b63478275836347167aa3e9c64a95767a89e9fa0f330bdc2a8f3f3c9c488c384ea27de1ec6c2d103b4f51b78185f85d679f87334dbe6d2510cb49b415bde27c1cd78d835ea611b4596096d7b83d8d13615f6934398bed501ce6154316b782e591a0b004b41d24d94b6ba78c0f35060122e097f54b2447c83714231213b844599dfc2dd3f45cebc0c3c172c2f3e69f8a24de3501335a4cc7d94cb0cc7c61b4b0de2b148945c295e6b718317386284d4ae80f2c62cec1b2c719bdc1166c230b5189b10a13443d37be9854e11cddb447cc78a1da4a7ed78b84a2c988c25536816a15369328a96bca8a0dbe0c98369263f05a851c30748189828c62629598346260b5d44c7d2c310f2f1d51f5618d3454fd96189dc0fdf1ca6ef984dc6d2192845993f41cd78d835dfe01b023b474fd77f9b1ca6c6371068f05ca24d68e31305ada3c68ec12c8779b0be5bd775adc95e34728d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part517 : Excludes 0x8000000000000008800000000000 0x3e12410883c0245482081100000000 :=
  finishCode 151 0x5e329a0619c87036950dc1ad9b5b06d2a21474ca35684b6e3518889f977466c2fc6af39d896149e12d2fb2f2bba8632d7306a27ceff0be8b26f686321fe11a8e96b8ad37bc198c7ca0cdeeaa61062677f0b544f459a8562546a654e30a3337173979904db9d83f0be535993b4743196ba58db2d38c6aed174609863c2bc2d5ed6a6f0bf34752fa2ac2fee920b440096f68152bd765f431cc2c38b79ad8c89b4b7e7113618dc4212cb7c507132b628574bec31a85e89bd834790e49f61de6e7c45d02a625b0b1aa70358fa722cca6d30a68f293c68f132a4f4b58c68c2e237118ec212c87235668f68b819bb65d4928b3693439bbdd2484cdc0d6e52d6cb095b8190d04306ad4be4e3b2fa3b60da577d3b851dd11a336bf3477352da4b03d4768b2f8368584fa26e82c9e2bfed8e133609012dc2fe2c689b36ad4764b688750b24c4cc0f16a12a147204e39834bfe7b55ff6ab093459da146cc1b0c7596839e17a2cf034194ba592e06da89335ab7a94d9bdd80a6d0dec1b6a58ad6a5ac110f05f9b994dd60aa1b5c48c51289ed6b224842c5694dcb3da0b2d689ed6adea537acb8480d6e8b36cb43f449aa04acbfef3ea728b2f6328bd8218bff52ba84b7bb06bcfc133546d79bde9950eddeea6b35baa914b20ea2cb7acd97a0ba4429928437517858d8354bc6367c78ab6b5a2654242fe2ad85d7fe09918d7a39f542fdb2e6d725b09b (by decide +kernel)

private theorem part515 : Excludes 0x8000000000000008800000000000 0x3e02410883c0245482081100000000 :=
  splitAt 1 108 0x3e02410883c0245482081100000000 part517 part516 (by decide +kernel)

private theorem part513 : Excludes 0x8000000000000008000000000000 0x360241088340241400001000000000 :=
  splitAt 3274 115 0x3602410883c0245482081100000000 part515 part514 (by decide +kernel)

private theorem part509 : Excludes 0x8000000000000008000000000000 0x360241088340241000001000000000 :=
  splitAt 1 58 0x360241088340241000001000000000 part513 part510 (by decide +kernel)

private theorem part507 : Excludes 0x8000000000000008000000000000 0x360241008340241000001000000000 :=
  splitAt 1 91 0x360241008340241000001000000000 part509 part508 (by decide +kernel)

private theorem part499 : Excludes 0x8000000000000008000000000000 0x360241008240241000001000000000 :=
  splitAt 1 80 0x360241008240241000001000000000 part507 part500 (by decide +kernel)

private theorem part483 : Excludes 0x8000000000000008000000000000 0x360201008240241000001000000000 :=
  splitAt 1 102 0x360201008240241000001000000000 part499 part484 (by decide +kernel)

private theorem part481 : Excludes 0x8000000000000000000000000000 0x340201008040201000000000000000 :=
  splitAt 3051 113 0x340201008240241000001000000000 part483 part482 (by decide +kernel)

private theorem part449 : Excludes 0x8000000000000000000000000000 0x340201008040200000000000000000 :=
  splitAt 1 60 0x340201008040200000000000000000 part481 part450 (by decide +kernel)

private theorem part413 : Excludes 0x8000000000000000000000000000 0x340201008040000000000000000000 :=
  splitAt 1 69 0x340201008040000000000000000000 part449 part414 (by decide +kernel)

private theorem part379 : Excludes 0x8000000000000000000000000000 0x340201008000000000000000000000 :=
  splitAt 1 78 0x340201008000000000000000000000 part413 part380 (by decide +kernel)

private theorem part355 : Excludes 0x8000000000000000000000000000 0x340201000000000000000000000000 :=
  splitAt 1 87 0x340201000000000000000000000000 part379 part356 (by decide +kernel)

private theorem part317 : Excludes 0x8000000000000000000000000000 0x340001000000000000000000000000 :=
  splitAt 1 105 0x340001000000000000000000000000 part355 part318 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part521 : Excludes 0x100200008000000000000000000000 0x26d111520440201420040001000000 :=
  finishCode 171 0x198b65017988995ac5a251a8183ce5a9d16b86269e8866ced3337bcc59abcc1c11e886dbb22b8cb859ea221d86158ada96e25ccad15ccaeec43181d10f0b6b535114cd45722d511b425bb6916b5323f443a79289a226e85c11aa6ad9ade7cc8ab99190965b5b662668e22bb6ec1672cad9b37bcd872daa6a8ab107a6a342ec2d7cb5e5615763e8da176a72f72cf2da9da85f16b4bae17addca8da9c51cc2b16b4abb03d62d188d60c1e709965afc2d957d11a6f98344335f9a4c5ca226ae4cb2db60bcf9a88669fa8c644181e1ee5353338b5a55e62eb4dd0f983333d114efd11a2d423cccfb1ac7859854cad0b65d662678ddb688843a21cb6cdc6c2b20a6f823e1962849a4ccd85698388d965804f25b641b33342f6e397e4ccee94c9a22ac56c11adbaa6bcc8ad9bde5b74468858ad991b4456742cdb3621a2207f254d9eaced97b7bc4bcb3b5bc4de2aadef9cc65620168601895c9a581c65cd9e21d86158a398062b48fe601c31a5ed81c9a501d10d83e6d7b531973676f7981f44512eb150b42dec9b32fba2385a32e6be9df4c98b92c6ca48ad447446196596d1100b9a5c04da7d7250b5af49bd72626f97bd11ac580d5e5ee697b53197764b6ca22f9f25acb6d15aa4ed92deea6b9cb4542c067f0cbe3185635f5f91e3a9474470b5444d7d3bc46e51d137983d11c2135f36fc6288c3ff0cb4d36a7842886c2a8ab24944bac85b313147608659bb418ed1196dc27511511b0c5bcf09e6240965c14ef51153534fc476339509422ac0328872c0f18ba94b03c62f0c8e37bcb3da2315a11b2cf684c9c2f33a22dae2f710d44a8d652a66c02ec899ad4e59f4462b6d3e5bdb53d11981e9a74465e544b9a36eda236a611aa6bcc5272cb85ee2b743e945b25bdf446c2f8ad17b8e441bde60f6155a450d863a169b36a64d32f7322c0f685da9b738bdcdaec024d394607c278ccd4d4c3ed0f4f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part523 : Excludes 0x180200000000000000000000000000 0x67f014c38040000000000000000000 :=
  finishCode 175 0x63339a0ba532288968ab98ca4caea14765298af9bbd3b65ce6af8af6f1c03d34465d78e6522ae6e3d11535d11b446535b28d6752ea8e932b77d3c8a542d889b84a4059b9098e5468afa73946ecf66f1981b4998d865ea056265630946ef6e18719b762a50368735f9b53b539b4691709daf5b756767838af6dd51b8007446d4db45bbed110b344d5e0cbd010132b6a7267acdd48af7ed3af4e0ff60dbdfbdcda9bd3d31af733ccc3f10e66e16efd44cad1076a769287232f286dfb4450e66569a21cbb14a6d4e899d118ab331b4985a70c6d4ccc6d11c27527ca53268a3b2948cbd84ea4eb9f2678a7da9cc68cbaf5d80b45b29015615b103454a7bc55cca8bdb70d32b1caa2b230bd7487430ae10d10fa22de367ade3688bf13be6d1b5397598b86fb44621ed4d85695dd1185ed81d85731207b985fd3be210df52f926c56b68d4e76a729aaebc55c83445b0f97538b00a77d21a36b53097b53a21657e2ac126c21b53987a444256ed110958ab6016158e29ad6a6da2c0facb37ad4e62ecde2636e1947657f594ca0455a88a9aa11d10f32b69f4f221eb536bf6ef8459ec67ef7385b4add21da9ba098de9ec2d0a133f9957b9ad4e61ee158cc688d48e84a15e30632e15b28d8bdc01bce5270af425846634442be24f9a44dc11ad7b0e3082d66e2fa15eec6c4b10961134249885b43d475af6906d0fb49d118999a3d3c2fb30f59ba77d10ba1ef2ac0a0456cd05f66cd6f37bfa214b2db0ed45efeb29d0d8c644f6d4ecbe30e8d0fa916656d0c59d46e9068839ee6575f472950527535ac216d66eddadc632ed3b539b76e88bcbd32b688a9903465ccff4466f1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part525 : Excludes 0x100220000000000000000000000000 0x2ee49342c244440000000000000000 :=
  finishCode 89 0x3b188cc5a23869f7c5eb8de5b86c13cd044bd42cbe8ad19743944d8a9969eceed4e2b48de085d0ba65508d7ac65d3be69fb53d0ba654de74463812b3ea9b8b03b70b78d234468fe4f797337126f7a3a6565ccdc741508022ad210e74464f76e79759ae66f7b6225e88c6b2baf3ead022a617b0859e37bd15a6b20b337be62798caa1b0b70cc2b48f5a9cc8b77c39d2ae4deddede354c64cad316bd6c0ed7f4c4cca8b9cbaa10c51cd7e49e4934c59999ace22d160aa0cbd2029dade2696e7881ad462a57ade8eb53a6f9957d5337a455318dcf52099bb7b927b07cc0cde182be123a13530e86d9be88988e16a58da1b67fa2206f440ccae88c66f14895893ddde7d1b538e5222124615995b44491e28c245d1863684cc88afbbdda1ab932ca48f6a30bae84c67310d11b379f56ceeb3faa4817ad81e656d093397bf7d18b58ce625493e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part527 : Excludes 0x101200000000000000000000000000 0x2fc0f0c29240000000000000000000 :=
  finishCode 179 0x1d8d66a3118cac5b2306e26f2d051b8259dbd1cadd4e784e60a29f687a13267bc6b78cc0f09accada8b79d22386df66f30aa10d6a2de6a67a231c824f144708de3a234b0caada9beacb0d6a368887db5eaf5b617ade36c27a71d116bf88db426cf5bc7447416a7a228373eab46c49f2d7326baf09dcc8cc6a8d9b89bcd62386bf4cb04cac14ea6b32b210b77caba88cb6d9acda2dbb3234b735e8518c3d323911b3e7cb6cbda94a99c487a2332318ec57ccad329132b303a94a9abc6c3f2bd66c2a3b84a446308642161597b51bb84a7c52cd5084bd699131d6d1a6461b6d0ea73b356d19e56106e6f36b379f7c38c610d15f2d73268372f596a91ed6874bb152bd732b52cb59a8de32191cc21a8d82e1580b3940c1c4cba23370b51c4a32d7a232fabc62370d2ec4a20a74e72decde3692d63059b70b77d68c25602ce206d11b3f995183d11b446b3f09b6cfc31ad0d2e6cfdb0ecddbcd06f446e9489a20d851d9dd32b692ddadc7667618da8b61b68d32b66eda769304db67b6fd61b860a37bd9bced970b4583001421674bd8c3a75c99f32269f32b3c7e4b6c2eada2dc332b35fcf5649b32abc484d26542566ef1818b5ad4f09c9bdef6513482048d22c7df1476a6f9e2c75a9b71b0acda311ef7a63b4b8937e16d2cab9e2c6dc64def6b1f5e0ce189a7937b78b68da9cd1b67eddac03a22c2a69f8cb458301400b3a44c25f66e92691877a594cb92c1f12b4cab74c57cf34466b997d993265acbea44f2a90c1812699778ce6645b9e6563f187998d971a61e88fb499956b79e132c30267368713291ed12b32ad7216748c047253e9653399956076159e5a8cf22faac024d2ddb191da1b00d32692b734e9328c0da8d2cb4c8d9de13934c72cede8eb37d093397a3ac14cc056029e995187d119bcc5d697708b23d243861e6462a6655086895995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part530 : Excludes 0x500200000100000000000000000000 0x2fdd3c5aa2c80000a0168010000008 :=
  finishCode 45 0xc067291108e37bc672c1ec2ad86e9b4242b6d4c65f445806684d215ad7b3ead94d4c765a0ce5f2e0b36f7a5ba2d742c95c5c6337181269865ef97492685cd5b16b2c2672303680ad901c2cecbe867d1177fb37c31197b4470b53557acce6cbdb167700867851d7ad01cf4ed0b6b9b29a1e4435686d3f0c6e95098da9642bd01c65e1015f59fb74d94b6b857d653693532684af60ba6a840d978bee71016b51c276d72695b39b6492db5ecd624b269 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part531 : Excludes 0x100200000100000000000000000000 0x6edc3442a0480000a0108010000008 :=
  finishCode 141 0xc6663397cac5b3806e26f2d0a44f146f09e8857d526fb29ad465965d709f4184f3c6d94bd1cf1bc6b536cfa4921dacde5d4b47425b865eb9e358065cdf0ee1488e1b7cc5d66ed22de2c2ac03616a99e88c71f8bd74ca71b42d157445bc544742e6bfa71d099756f1c27a2b510f446208afa22b3b367c42c56cbbd86310b520a88b56a219b79b8d48455a25db2583dbdcd9ec174d00cbc1f6007653a1689a8aafc6b9b42e2b5efdae65ebd118adb5379bc179ae6d462b6cbf446b536b9b3bac522a06af70b6532c10c1978436cbcdcfa2b8329acb6a9ad69eb830c7659bcf9adb32af3d6bddc32f277cf5a32f2f7442d21cb6da4bdfc72f90c535b37a626d4c2bdaf66470be001a736bd8ada1bda9e421b53ba531eb4b4612db37505b496b9c035ed69232f6932d3da4d4bea3b08b51a9ced25ae5eb5ba70c68710af96d6b9ce5d2213cbe4610dd15cd6575ed1153388382b5b2645760f6158ad88305facec3d744693c2b508d1542b605353535944ba45f238dcf1a4da4a94b7bca064df692a66dcf5a4c41b7bc42d65ea3aecbe4d1ae6d096bd0ad51d53546293d34d6a315b17baded27b7bd9dca0715b107521be7a93df2991cb05614a54d709e1976bda28d727445d958511942f0d5dbc698bc2795fa55e6e14219ac705f446647392af3689afa77d2be6af505336c2dec32f2c3a231e8d94823aceadeb5ea16bcf8cbadecee6842d7b68944c8d4b6d7b3166ae6bf1c421a53db8465e647446003a5b1976bd98b946e596cbe42d7ab7cf35f (by decide +kernel)

private theorem part529 : Excludes 0x100200000100000000000000000000 0x2edc3442a0480000a0108010000008 :=
  splitAt 1 118 0x2edc3442a0480000a0108010000008 part531 part530 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part534 : Excludes 0x100240000000040000000000000000 0x2ef83a6b9949a02000008248010801 :=
  finishCode 27 0x1a0ec623008ab70ac5a8cb7ad130e215a2f6f9b4b6da8b5c8bed66ea6ad9addb10b133489a4f14d427e8ad503a1c603b85f6d9b5150387192e6cedae6f8f9b4b69aca94c91855f362698a35cfa55f0856f70148607829583df56887a576ddb2fad4c604285ae65cf51d535359 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part536 : Excludes 0x100200000000240000000000000000 0x2ed079ea814581a000048208430841 :=
  finishCode 41 0x339a8d6762991473039b09b8e22e06f34826f98565d6c2795d6f15ebb3baa8d87137b68b0aaebca3748964abc32ebcac2a167059d6a24cb68d0058cb0c30f142c2b377c3d600a2376a6da289ac2abf34c96370d45b46b496ef8604996c01673cab70a2bb78d323378da4a26b68dc1ea6b51b3f2650af6e4d2cbed25b4e98db5397568fa5d51168fa62ecec266a73 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part538 : Excludes 0x100200000000040000001000000000 0x2ed0796a9150a0a008028088010a41 :=
  finishCode 61 0xce76351acbe53255e529607361371c44f0de7410e2da3226a8dcde2bd715ba1f4c8b61b66a5ccc5d5146e98b615141acbe53d46f11b498b9ae62556f510d154d9e615b413c4556b19b4510c2ce8797cdc316079a342c460583db8bcc4368dc110d6f6955b29a20609942f6eda2d6ca50bd10f0b66f396535142f44db4622c0c1f379b668cbcabc2332f6bd65c312ab421669732f2c36a03caba10b03d205c6d0b6cd6f36076156ad9b35a66e160da057da8cde63075210969572658954219625ccd72b5f443a12d99cd2c1b4b3385f6cbc265bcc92e5bd881b49a5dc3185b5446d2743ec2fb51957 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part539 : Excludes 0x100200000000040000000000000000 0x2ed0786a8140a02000009008010801 :=
  finishCode 133 0x5e672657b13c6e681ac5b44526c2759d3794b936142f8819e9d2e4d8573f592cd4620d865d66f344d871379b53a96d75d81e62e2650953514e19bbcde6b089ac1f137b7784a937cb9f48c46b309e371379b0602d0c2b2fc858b0acbf23e3687cc6d2dda9e0bd6a72b6f9f0c5f98a9b09e645a3508709e5355cfc278dc4de600ac31d860696ed4d73d7ae28e96db532575f9c0366cc1e1671535836815f344ed85f5b35bb5d910b5a8e87d2eb6a75218bec11486af4c5a768bed2be6aea228435a9c57f63419c9e6a10bd10d81e26f94f9b0dbb71160c022a9bccf4ec1ed9b48b499a76646cf67a7d0bb29b49be400dc705e7cd253a56c2cf05d83e6ad5bda6303ae12e65bd7a94b996f6cd6a43991ac5c3017cb33a62c9942bec16a3379da4c84ad5b82eb7b48761abb4ed692b82db36932e0cbbae0cd72d3ab4f692dcb2f9e9e5d6d25b768997a76f3099a64d1ae5e9e94fb2fc1708db51ad2694f7a7c4600de6d361810b160fa6211d2b62e21433c977a4389bd2e61dd68da43a43b42d73de9d4d581f1168c05830832edb34a7d9bb79857da6c25edbb66ed8748805a6d2af862166c0ed5b5a6e85e18d97b07895c3c62db65ebd734ac4add8621424cb2c96d803e28e5c5e9c5f626ec310a1ad466910a43894e9be8a1d0b181b51a96eb29181607 (by decide +kernel)

private theorem part537 : Excludes 0x100200000000040000000000000000 0x2ed0786a8140a02000008008010801 :=
  splitAt 1 36 0x2ed0786a8140a02000008008010801 part539 part538 (by decide +kernel)

private theorem part535 : Excludes 0x100200000000040000000000000000 0x2ed0786a8140802000008008010801 :=
  splitAt 1 69 0x2ed0786a8140802000008008010801 part537 part536 (by decide +kernel)

private theorem part533 : Excludes 0x100200000000040000000000000000 0x2ed0386a8140802000008008010801 :=
  splitAt 1 102 0x2ed0386a8140802000008008010801 part535 part534 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part541 : Excludes 0x100240000002000000000000000000 0x2efd3a438949340000530042004800 :=
  finishCode 45 0xec67311509e22abb2f91c51d90e4d66510bf44c8bdb74a1ca99cb5f363b7ba1ca93c873002318ccdba6b6520d65e9a23455aebe88d157688d132baf7c533a9ccc2db0cd670013f2d3a17b61ae7d0bf66b0ce47b34be618c4caa3aa6b486d79b8d40e26e6a3425c17b3b8859ba549db5e90f4b519b742b580583ee8d8737b8568bdcdcedd3745ebad45e7dbb5b8dae6265 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part543 : Excludes 0x100200080002000000000000000000 0x6ef47742c560152084421042044001 :=
  finishCode 27 0x16894680d3ea160c60cba77d4be89addb277a21c6bf3131af8bfd66e5b3a22c2b4e384e6cf70d05829166ed7b536fc2118f8c613b0acb6da1b4d2de32a2da3288a77c36cb6b0ada22f5a6deb93688b68c725b66f36c16e1c27265615d0688f01e36b516f332ba9168858abc27533601 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part545 : Excludes 0x100200000002200000000000000000 0x2ed073ca8164970000460242424040 :=
  finishCode 45 0xd656311d8a65c0dc62658c67306e3716e16ef357ad46575a3ecbea5f6d195db46335015f2bb3da9bcca7d4874bb313522a77b68d2d8c1cb2b41bc695d989b3bb09ed45b45b85726b5118f265ec4f298d83370a82a8e9b0c6291e6ef7c3aa4afd84eda32bad67436d39b69cf1aa23546d397ad856d3e7d54efa47ec688cb2796835189b913691d856d0f965a5da47a97544621e0b389b37906b8ccc5fe0af (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part547 : Excludes 0x100200000002000400000000000000 0x2ed072cba1403480204a00c2004801 :=
  finishCode 67 0x1d8ce6b3518cc4680dc4de6782232e7cb9a26d61e369916bf98b69d8ccf00bd74c5e84b00c42cb3ad1ad7f70c03e8cf37a232e72faa3abd6c2b4c699a1cdf44d854754d6b13ca479f469c5f0dbc664678d6bf4b9973e26ceeea4577fa5f361b4470d7e992db3dac4aa9ab6ed322dc72998cbb5fd6a3322a6adc78cb45c238167586e190e664dbc65f635195593be17ed0f45735198b8d450e6976683d11183265c64bdcf728ae162dbb04c8cbd22b1709a0c1932cf6a8434e3347857da1c6af4e331774a71aca42be256b3fa71d11c315bd9bb71168ac3b8d676dd215e4ca32f13760be88b5c857cd0996b3b6016f3b379b8e6ed615 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part548 : Excludes 0x100200000002000000000000000000 0x2ed0724a8140340400420042004000 :=
  finishCode 183 0x2f3b132b9cc66b35188a6520dc705e5034396f7367ba682556c178676b95bd4558659dc0ded732bf5a8d86348a32f6534b6873a03799460113546eb516cd98bd09ad44016ca567546db3661551b98ba925afd46ef93c8c1b0a17c972dc2a37546cd9e257adace00fa456d199186da47c044acd1aeeed9abd6c1f31718c2d802eca5ddc16e2a6916c02717ad856906a71a479f46906a717d1da4a25566b18ad4394434e358d15ada34b74c9e84c55b70859df02ce6e1955ac0f7f058a2acf2f8d633689a7c8878636a2d1888c3d8ca66f6a32edc269f80b0371cdda32f7c5bd9445b456f65c9d0d77b8d7c8f6c17c6f388f41ce6465954d5ace23d421a1b6256c0463371e18d2db68265a64460e55e95db3b5bb265ac523011818398b940e57609f88f5b9cd5e79677455c56a12907d65348f48a32ec09e212d6a215e49f107157800af8ccf4262298afb296b7965a91e2bdaddbded188ac6b065e304cab4344acc8d4deb4e49e4a75d258447059d38b79927b56cd8f538c43999c4ad521b482679b6ed7d15eb615699a25691d8562656f3ec5a35988d4672906f32c3676b79bdf05e887d03610e59118c3197aeca5a7ed4621e626455a4719783ddab691e21e69d643c4a817acbeea7389bb519ae64ef98ba4563006aef1335bb738cbb73d13752fcc8b5bb7bcf22aec173338ad425c0351d31366f52db62589df748c3e8c0083e41b443a4715ba71a17ed4621e62eb516dd59d0afac4010e6683b29333a4798b183ad46b29333c31897b518bbe17dbbe21ccae8ad4434e281d4baf12f36a0a73a26df44c0cc6d46e4a75cf4ef7d1d01a7e0bc8aa166886c2b3dfda6d2fd610be99312b3b3c6d9a9b8acec3d2eef322d7fa1f28dda2c188c3182cecdcccd3bc65de26a737ad3336adad3705c93f4442cecde265333 (by decide +kernel)

private theorem part546 : Excludes 0x100200000002000000000000000000 0x2ed0724a8140340000420042004000 :=
  splitAt 1 58 0x2ed0724a8140340000420042004000 part548 part547 (by decide +kernel)

private theorem part544 : Excludes 0x100200000002000000000000000000 0x2ed0724a8140140000420042004000 :=
  splitAt 1 69 0x2ed0724a8140140000420042004000 part546 part545 (by decide +kernel)

private theorem part542 : Excludes 0x100200000002000000000000000000 0x2ed072428140140000420042004000 :=
  splitAt 1 91 0x2ed072428140140000420042004000 part544 part543 (by decide +kernel)

private theorem part540 : Excludes 0x100200000000000000000000000000 0x2ed030428140040000000000000000 :=
  splitAt 2828 102 0x2ed032428140140000420042004000 part542 part541 (by decide +kernel)

private theorem part532 : Excludes 0x100200000000000000000000000000 0x2ed030428140000000000000000000 :=
  splitAt 1 66 0x2ed030428140000000000000000000 part540 part533 (by decide +kernel)

private theorem part528 : Excludes 0x100200000000000000000000000000 0x2ed030428040000000000000000000 :=
  splitAt 1 80 0x2ed030428040000000000000000000 part532 part529 (by decide +kernel)

private theorem part526 : Excludes 0x100200000000000000000000000000 0x2ec030428040000000000000000000 :=
  splitAt 1 108 0x2ec030428040000000000000000000 part528 part527 (by decide +kernel)

private theorem part524 : Excludes 0x100200000000000000000000000000 0x2ec010428040000000000000000000 :=
  splitAt 1 101 0x2ec010428040000000000000000000 part526 part525 (by decide +kernel)

private theorem part522 : Excludes 0x100200000000000000000000000000 0x26c010428040000000000000000000 :=
  splitAt 1 115 0x26c010428040000000000000000000 part524 part523 (by decide +kernel)

private theorem part520 : Excludes 0x100200000000000000000000000000 0x26c010420040000000000000000000 :=
  splitAt 1 87 0x26c010420040000000000000000000 part522 part521 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part551 : Excludes 0x101001000000000000000000000000 0x2f86f0889018808008000000000000 :=
  finishCode 115 0x1d8dc633594cbc1b0da0684dc516650f8a9b3593a708f0f2fada9b6c8d0bc3c9db2e332b84ba5a06861cec25a714e96f1379b3593a6636b4f43b379231ad4da865ae654de578dcbc4f138c07274ccab60b68ce2d4e90de330f5239908508c2d11f2fac11b0ac8c4c3cd298b9a0ff302cbbc5a8a7d1236a766b447cbbc47d2eeb9b4b8d2cc4fda9be7c626564e95e9253a234cf5eae996a7688b5981705e88d34fa65573e99049e4d0c8696e1619958b3185b2d9a86654276245f3d3a6995787b537cf605a5ecc86d4ed465e99958778b3b53a65a9cf3093231378c2d2228e0957bd98d85c628e909d3309b5fc5acc8bdebc6cb9f4e3274ccae127830b377b78be3937b1305e8b38775db5e914f973c54e23d6fe8a39716efd6612a94c453995980d4d5abe8a99958d7d125f06bea1f4c6a8ed4e72f70cb2db185dba65584e61cd3dbbf0911f4c6937b01c5ad54d6400d24686d1e995a5998d96551b98da8984a64c1d48f4e32c30cb31a4de30abd35a9937d3260e2539878a509d88ba55661e59691e9c66569069838a532726f977a5f8d246871954ba4cac8b24d233b327134a27cb5d14713689233b2e35499593665dd0ed1651268b5337971 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part553 : Excludes 0x101000000040000000000000000000 0x2f829ba08802000201010808000000 :=
  finishCode 153 0x359b4b6653b033ba8cc082da2332a87ed331366c26e33c89b89bcd657d685fcc521ef60b543f6d3a234d466e3b85a9c67312b32616b147450c4ac4d99cf637168964f09be5cbd11351361c41bcc156c0adaf188b59a6509e26e2bd78d27688823ccac47c5ac36dc223e0a58b59a64de63618dc6a968865823814a156d45cb349241a1e62d6cced11b53a6567914349b479366655b9e6f7b536a9b446d4db9c2ae8e137cd5366e2f3a2345ada22692d72b9770b44b21889f15f5a9a24b5ce88c24645e0ae99e9d28931033d1da9a24cb3446179b53ad4661e590c17990ecce50ee1791359f0e635f1ed4c9a68168aa662908776a3369aec9b7a2cc51496a667ba1b123da8a588a2e18b60d6a31032c3a236a73719884e5fb349d9bcc3b6e8faa74e88e5175e6c3a516dd881a5848cdf1f0b6d4e9a653b110c4359d31b143a1a4caf6b3bada3c5ac39be1c39ceeaa52a0b2e305cbe1da1ad82f470e7785279ace2865469719a6502e643f6ed88db446d4636f82e711a8bc28ec1726de6f30bf5a9da3a1d9b4a27c16a89f1b0c40de2d9180b79e309b60cfaa4dedc7137cd8267b348a5126067b3c5d97c788b623743656e687d1111b21b971d0da5f74460088b0366d0f74bb69f1429d6be743de86d9bc51da9beada0b6a2ddb48b4e6baebaf4c6d9ba2107628e4eb7b56d3b53b4fa975b06d4e8778a55d7b64d279305db1857c7ad4e635f1e995253a56db4e0930f3ccc48bd4cd8732b34b3db379b4db76cee (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part555 : Excludes 0x101000000000200000000000000000 0x2f82d9848044010001000040420200 :=
  finishCode 157 0xd66e3b1a8c45e1b06de6f2f88e2e1476007d11a474bf68f6df9e321bbf416b53c1b77b8815ddb45a914497444996205776a47d11b53b08dc32f5da9a27c40c70996a454314e15ebb53b09cefe88d8816e144fc25c26954449b6227da89b4cbd6342eeb5a9be3e88db1c86d32d7440e11cf8f282da9a5f8f7a2cd6cb4f80469c6d46594da468668c8783e1da8d0e748a97e2cf1531033c6d9fd228b3d6a312af8ea0a2cf520da658c2b3deb64b7bca7d2eebf2d8f2ef2f5e88da8e12e165b224a27cf2f16933789b0b68db29c6c23b5319979f361049b0b6049991b53b491a189bb6550d857ae4317cfa9ced16d116d3b535ddc25d311640b56bf981623e2d4d44685bc6b49a1b4d4513ee08763eb100da4e88b02a2cc57d65ed4750ba521eee1837bd0a3b51878d04db4ed36d0cd462d623ed366bfb5118388b8d45bbea970a45a8c8a68b394b6591d8bd633b2fb19cda8a5fd2a289e6732eecc9da885aaeeda2217289f2e345aa67e84c40e88da8da9a27d01a0876f0b2fb4919dad4ed4455da4e19d8a38676d4c03e6e9d11269b2f19db85d21cea71b535e519d0b926591274468a1b497b119dc24b6d6a615633b60ca4d2f11c1877e28ec51d48a80311b4b6b9ab4f36992ca5fc2a7a0a646d676a72ca45a9d0ef14b2aed92dd32ef35cd39c30f59cda2269311e30f2cc27b444966d4db9cd26d4eb25b32978a4058bddc30e147a07e3e223d736b53253c235cdacee9ce113993b5187b4bda976cee5f5e948a66e02765967bdb516c37a98779736d45b4ed46965b519f366d39618bbc91c54dafecec61c2ae39785eb61587b9f1ed4e64db86d46b538d3dbc65ddb3b6df34f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part558 : Excludes 0x101800000000001000000000000000 0x6fa6dda1fa4022008000a000003010 :=
  finishCode 41 0x2f168b65c290de32fa9a7851e117de0ab0b77e4f223c586c2341bd119bcdbce87b79fb0b6905bb66557d584e7869edc335eaeebe3c5acbbba22fc725913a691707a30ae88c67ac02f9f3cb937e88aebc0fe4df0cb349cc3af5cb8c0fede3708e688d166c2ba234c6cda6de64df32b44fb0aaeee88db278f41717c79bcc26694fd11b0b69ce655b4dbce2ce1656dd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part560 : Excludes 0x105000000000001000000000000000 0x2faf99abb260220080088000001410 :=
  finishCode 19 0x1d8c25302ac6874461794e9a6549bef13cb45326566f351d1710a3ca35253eb29995b2b1876cd8b39bce6570b698db47995187995a1945c5bced11173b49b299956a9a2cdbce655b74676 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part562 : Excludes 0x501000000000001000000000000000 0x2fea9f839240222880008000001016 :=
  finishCode 47 0x652e93419daa522388a62cb26a99eb0ab76c2cb3e399eb5ee807be987449a45d11a710b9449a91744697f0c697d87db510b917baa4b2696843f7d5acbe5f664d13f446339b516a9b3fb06e1f580583f05e97d4597c79126d154b65d2781572c693ad253a6d44ce50ed68e7c39877c726986d88d6656d0d68644f5eb995459c179f0c5170c491d1650ee5148744bbcd6edee66fa0d0da28628dba6a5f44997793a7446905e8d79679f9718e431856339b3798545e7446 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part564 : Excludes 0x101400000000001000000000000000 0x6fcbb989ba40220080008800005010 :=
  finishCode 53 0xda612e9981a1b85a1bce4530b57e4f13a50fed1135189facbf446995b43a655bc705e6f3d114e9611b45c10edf08b332b597e88b08bc3d67f32b65f6935a6e86b50e88e0be18b09af2cde5db995bc4f2d0e351b4941bd119eeed26ca40f65dbc176898e4f21978351b499b85bc426e7979bc680307132ccac02914bb3e7851bddd97d69b11f667051d025100d119f36790d3538e888c184ed94d32af2f448d38b6ee88c52d7435182d46240a6c316b161345943b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part565 : Excludes 0x101000000000001000000000000000 0x6fce99819240220080008000001010 :=
  finishCode 139 0x178c4662b1689e1af9bcbf1a8e3055eba738a151d6e16f1b23b1b3696b7c399351dc2d97adb7c9965869930b9725c2c8bbb4c23b9476636315d116bf3050b9b446cddaff290f328eb79e18b5e98ad863a22d7f67710331b28eb5edb3286e3740b993a46869132b287a8dcadd69f2eebbada34ca937c71c89d328eaf5b03d22ca36de3a2314b521a93e888d0ca366e26f36cca5a068678beac23653287e889acda1cdb2a1e6b359ee88a74cf09beb29d113596039b9ec91cca52260a528c17b527a678c06d3d75ed4575e95bc27b445dd68b526551da43614046b3eac40aebaf2dc1d8c1e603687a08d34c40da1ed4f10359bd34e168a49f8cc1f4a385ba23a13688bdac40842c5a9239f8a74cbcba2348904905eecd6093b4fc2f8a13f1a4f97670bc0cd43c24e7b5881161b4361e5ed5766d94caa1ac8d09b0bdac4df2d75a1a62e88bdadc241845e227a1f842cd6234332b68f0d0cb5da4c7230dbf042b78d22d0e94f127b096d0f446d26655b75ace5aeb47995b2944fa656966d11b496d16f14e9b847201985ddd11b09ed3ed1d125b3df0dbc5d84833ea987cf6b2a383798085b44664d13dbc5f0e17388180688a74ca06f6b842d1b049e87a8ecde29d384cc5c2e887f48b4be8f7b6e8d0da2a93c44fd118da57ae5f705eb3796197674465ebc2d80c5415f1db74685f56d11a456dd5051a19e4b2a86c3747a4b8cde731adba047617cc6caab71cc6c2d74aae88cb8d38ccab79d2e331a6d348995a5d8995ade976265d11 (by decide +kernel)

private theorem part563 : Excludes 0x101000000000001000000000000000 0x6fca99819240220080008000001010 :=
  splitAt 1 106 0x6fca99819240220080008000001010 part565 part564 (by decide +kernel)

private theorem part561 : Excludes 0x101000000000001000000000000000 0x2fca99819240220080008000001010 :=
  splitAt 1 118 0x2fca99819240220080008000001010 part563 part562 (by decide +kernel)

private theorem part559 : Excludes 0x101000000000001000000000000000 0x2f8a99819240220080008000001010 :=
  splitAt 1 110 0x2f8a99819240220080008000001010 part561 part560 (by decide +kernel)

private theorem part557 : Excludes 0x101000000000001000000000000000 0x2f8299819240220080008000001010 :=
  splitAt 1 107 0x2f8299819240220080008000001010 part559 part558 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part567 : Excludes 0x105000000000000008000000000000 0x2fa799aec041301100400440000000 :=
  finishCode 23 0x612a9949a0cede29816e8374c8da9afab09993c4ab2c6f3ad4e594615bceb530b7ac04935a985292a855cb6d6a630f36b92a8d0af091eb375cd991255995b53a44f061e5b64f725599141b6e3ad24c8d2fe41b6f3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part569 : Excludes 0x101800000000000008000000000000 0x6fe6d5a4f0c5201100400050000000 :=
  finishCode 39 0x5e231086c1a7be050e97d61132341bb37b516cf6dfa23f1736b5197db5325597d8cf664ecde993ad4dbcecded46e160c23dac4de16385b370cbe851b6fe16d32adc2f8f379b70b6fdc2914cb045ac8362fe14f94804cad85b3070faf32f9f6a73ccda2d13e12216f613b5ec45ccaaf5d6a6de683766f676da34b2d93441da654615eaeb2d2559950859b76d4d83c955f1eb53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part570 : Excludes 0x101000000000000008000000000000 0x2fca9184c041201100400040000000 :=
  finishCode 153 0x33184b85235089354615a59de46cec2e4dbd166d86df68b1b48abcca8d08afc97f30616b22cc628154b6227de3519437919d89942a685f7b588761382d6cde5e9b53265ad4ef1a0b1b0c399bcb6fe825f61e3361b537c74bf8d86d8fab1bc85a8b2d32785a172da34ca9b0a278cef62f18c8c4f22d689b7c736f6136e16f1d421dd67697e6de6f36875a1c6a26f24df2f4b689afdb10ee255b533511a19a551f1eb5325543b6dd4bf821478df1e60c59ea04b3288776019d6dd8265e7db8e986c2d17598309985d4955f16a3439cca8a9c4dc33b65336bda499c92ae2350f837935f4bf9b7c2065ddb37a852028e7cd183765a9cda332b6a24cb2e6da6b5fb79c48d652dc69db6a62e2ddf18361acb454ed4db7dafd0c6993c2558d24d868932b14368292aa5fda0b0f354995d054bf92a5ab5bce2ce60ea43693c6652d9a019dec4d278c231371acda1d1533271379249aca87cf268f4981b0c6d0dbcdf5619a889b6f7ad4f0c5ec6cd64b3c1b981c31967b066d4dec6804d24933c8a69a13a69d8630bf1acd54d0411a9e2efb5342780441bcf0b652761560783ff0b6d4e1ce6dd984d21812785b5a7c43da9842977d6a62f7213da9d9ec49284f6a73097d92ced4c21459ed3e5e51479e5b2d1e5cb2d724926fb53359249ad4f0b42169118c2da2a5b9c5cc2962496e7b2fb08c9262a6a964a05c26014b49f2138bdc39cd7af46de684ea6b258b01da1c3984ba94cbee14f4017ba1cdec626d84e7d59846184e4f71734b3b08e6454d65b68734cf78d (by decide +kernel)

private theorem part568 : Excludes 0x101000000000000008000000000000 0x2fc29184c041201100400040000000 :=
  splitAt 1 107 0x2fc29184c041201100400040000000 part570 part569 (by decide +kernel)

private theorem part566 : Excludes 0x101000000000000000000000000000 0x2f8291808040201000000000000000 :=
  splitAt 3051 110 0x2f829184c041201100400040000000 part568 part567 (by decide +kernel)

private theorem part556 : Excludes 0x101000000000000000000000000000 0x2f8291808040200000000000000000 :=
  splitAt 1 60 0x2f8291808040200000000000000000 part566 part557 (by decide +kernel)

private theorem part554 : Excludes 0x101000000000000000000000000000 0x2f8291808040000000000000000000 :=
  splitAt 1 69 0x2f8291808040000000000000000000 part556 part555 (by decide +kernel)

private theorem part552 : Excludes 0x101000000000000000000000000000 0x2f8291808000000000000000000000 :=
  splitAt 1 78 0x2f8291808000000000000000000000 part554 part553 (by decide +kernel)

private theorem part550 : Excludes 0x101000000000000000000000000000 0x2f8290808000000000000000000000 :=
  splitAt 1 96 0x2f8290808000000000000000000000 part552 part551 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part573 : Excludes 0x100041000000000000000000000000 0x26be2a0d0810a08208000000000000 :=
  finishCode 175 0x733b19cba5934034388a822bcbea9eb5a9af3a25c9289547cf89bc184cf6b87bb5a7c3cc51b0cc02cf6d0b3dd7cd3dd9eee5af5cb9e511d95842f9a38027e23db2906123bae44dc9eba174bead3830cb9624f6532d769e4575a7a7a91ed0ce9eb68f44de12ad7ae5b408f65cb12323b9e1e2bdae66f7619d0622692460361398d9106d4c9bdd8d3b1a4b5cb6c810c99ef330ce6932c764a248db26b32fac3ca209acc9eb8632d38eed9ada3b649acc47cdcebeaa1f2b7220d27a87afabb2b90c924f13d5865366b29699061151349b53b0b4f761e6236789eb2d7594cc09a4a41e6617d2aeb435cf4abad0ecbd72e4f59e341a6664c9bc186b495a7b0b48ade6619eb497994274f5a2d58664f56d9d0701b8c272c5f5427949f09c864d66f183b618a1cd27937bbfc47228ad8f36bdf258ec2193596c9a2b70b6439804410e5ef6787265787a1c698da6f2659621c9e1d1362a2dd2477455d24c38df343e85f50f7bd5277bb6e93596e9af934a4282b09d21c67aa6b48719ee42f108527924b1866cae6c96f7a69acadeaf0c6b436d7427b0b5dfd7d658dc239b0b5bdd09ecd6c2d6c99577916e77919e6658c33441c55b64b7b8fbcd8ebea9ef27ab0caecafad728964a00cee81866ca6951b53b4926585fad46d4e5ad09db65d932713499c91bcb462d24d3409630cd97d0beb436529eb6a6672db32ef36cd6a633b30ce2210c86c79b5ee978565a1d6a645766a4d24cb0f3142f033dad0e64484c8accf6780b5c4572dadef3224cb4a7b7be16c4cb68642694e43f34b2597c4ca67b6935a9b6cbb158797134d37bc8b6cb11f169f6168308a4d6a699f594e16895da9d97ae7d86247332365385b4430fb06f42cf745761e62d4cf62d6c84114d5f3e2134f5a5d195613505437865584d84e195 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part576 : Excludes 0x110040008000000000000000000000 0x2ebf9b130c85204462008001000000 :=
  finishCode 71 0x762a178ba6e115e2062b2d3c3daf2b07be6d16a67b2eb19ea17ce10e6b11017b7d5a2b61c60617a3d118b47095b65806946265d119c492212c4377b598070b616b899b62b253eb356f74d9a61c259f3c686591c413a5d5a9ecd6d3d04e6a7d113079e8ddd56be94cf561c6266c2d8ad6d9b0b7444686d92c864c5cb4e3432f6dcfa22dee67b2d7c56be78d0894d65a5ca2432f6d8fa230e3610a25c4ce88bd2591032b9ed499579580609348019ed37cf47492dce472def37bcc0e7aac0f37b919d42f1380ff9654b474257e5e8d01c5ee0185b688c51d37d85af86f072132c67b4a65973d1e0de88ad0b63beac7aba17a1385af4667ad8f688cb218c0f45ae8892eb73b7bc7097e615a4d968531f43628e17b6c7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part578 : Excludes 0x500040008000000000000000000000 0x2ffba3116c012005e0008001000000 :=
  finishCode 111 0x5d281347a591b75bce8924be19ec41726b432656c98fb743c9a617b3ed9651dcb92c032ab6888b9e3183eb53427d0b5c99a5d2ce511006188bc5cf109b337bb4bb4cda1e61e40ba169b3364e87a028aea13b0238dc764be4c8da1e84edee4ca986434bc99f4df30711dd0f38622f7477684a13d37b7bb63cdefa23a886303c4d284edcedee11f60c932da9c7109ed113338a1265d11a01506028220d86c03189a13d4d7146f0991b42ccce2d65f9b247250c0ec2b32345ae10cd9385b1348bdc33b7bcbbad924d3373e88ab1e46d112696c74056c9844a29aed119916c76f7d0f87bd80744509f0c6965b2960fd0b444a2a1647e42228d90986d7b29b42e5569bf42e879d0b8cf694e5561e3b53b495f37a43d99ed6936a6be74d751db0aad3e0dd94da9da9c243134e88da9d9168be7046bdd09ad4ed0ccf7426b43a974cf7426d4ed43d259e6c95f3a45a8ee9349a62d5bde00f44d9b0be64daf4946a1837203cbec5ae88da234be99ecb2c8f46a389970c5797445805bde615d1106faca5aa70c5b64996c31269d11177 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part580 : Excludes 0x100060008000000000000000000000 0x6fbf93514e033c047000c001000000 :=
  finishCode 29 0xba6231950441b240115ccced0f4f7c1b8b56a7b0bd80eb5389bf44694ed1142da8403446a4db538a326f333aa5930be601d0fa8ec9bd78bcb687905da9ce343e17378d8b5f43c896d0f4f7c2dd11b5326fb64a1aded116e76159b249be94617b4f7d115f3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part582 : Excludes 0x100044008000000000000000000000 0x67bfb3710d19222660408801000000 :=
  finishCode 31 0x4d2a9646dd6ed5c9a8ed804cf678f3f4beda2937d28da1e84ed334771c8029ad21d67b4b685ebcad6749b5a2e88ad3cbeae4904da1f84b4e7a16342a66bcb0094281b59d16a6670cf64b2bd0f9e5e19742d81f42e884f230eeb07fd28af98d0cb3cbea82c8d33595d1d8d0af2905cb4fa22076d336932d38d0c1e6c1f4776c26f900743ea3b2d9879205b53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part584 : Excludes 0x100040028000000000000000000000 0x6fbb27593c11204760088055000000 :=
  finishCode 29 0xb44d1e8c06c22b4a53ad4daf5b7718d73373a59da22dcf687b71d8beaccb4f91074444f6ca5ae5b665ce50f2459b9d43e50d8f373937d68f4060685c882d86dc7107a220e41bcde66b49c2f0f7c2d867977744600350fc1986726fa285106865 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part585 : Excludes 0x100040008000000000000000000000 0x67bb27130c01200460008001000000 :=
  finishCode 155 0x174ce632f13c8822bce26889704b2db44625d7954cd4a54ce1a1b51a23546bdad4c9bd79e1a12659af6d4e59e64d3b49be6ddb53d1144bd422aa94ca6ac23688b6e8d0d5180dbaa0884b06865f31a1ad4d0de516cb53868655ea6bb531a1ad1e646b534371a1975acb6646d4d7cc686d9a23441afa8d0ce09964375e5883775b446d1e49509c3d10b660d7af8613697980d4d70949be6ed5354b333d87993662854a4cf49be5f76e3a2529da236c6bdad3d80d84ed1e1135c96dd6bd90b7446f91c53593e499600dc7376bbaca66dbaf3ebb2c27016ae4b59d020134a8371b79afbcc2684aa535a3e88b0320d86dc6d99f3549ed115a7d0fb2b6c79b9f21cc7644cd306a4f68ed72db2f2f596bcbd86284b65b69ea4e84b373cd208bc089979ed4f445845b753b53e660c2329ab09d9acbeedbaa6b36eb09db2113c5e595d33d65b12fa22deef3366b115e1697bb7b8fbd863a22deebca51b0b4845e670be5f5c2d897a9aed17213498688c67ac22a6ba2335ee84a94c013ae7bd7ab9b25bddb9e5f7b64d2611335a9e88932b00a99b08b09df3217894294a13c9daf764ca99b00ae16cb3e88d9ec4cc56a13da23836bef363d2fa8732c886730be2631dd5f55e5d116018064280dc333c1bad3d09db668adc1b7999b9e1435f5b0b5bddb26d3e439c1b527b536c96e4017d5f3e7974cd2457ab89bd3665adb1ec2d17b4b3d118e4d321837282a948a2d4d29f2d4f6a64cb2c884017cd33e219d116a3d11a25d09e2cb871607b4f10bb532cbb446d4e5e5d11 (by decide +kernel)

private theorem part583 : Excludes 0x100040008000000000000000000000 0x67bb27110c01200460008001000000 :=
  splitAt 1 89 0x67bb27110c01200460008001000000 part585 part584 (by decide +kernel)

private theorem part581 : Excludes 0x100040008000000000000000000000 0x67bb23110c01200460008001000000 :=
  splitAt 1 98 0x67bb23110c01200460008001000000 part583 part582 (by decide +kernel)

private theorem part579 : Excludes 0x100040008000000000000000000000 0x67bb03110c01200460008001000000 :=
  splitAt 1 101 0x67bb03110c01200460008001000000 part581 part580 (by decide +kernel)

private theorem part577 : Excludes 0x100040008000000000000000000000 0x27bb03110c01200460008001000000 :=
  splitAt 1 118 0x27bb03110c01200460008001000000 part579 part578 (by decide +kernel)

private theorem part575 : Excludes 0x100040008000000000000000000000 0x26bb03110c01200460008001000000 :=
  splitAt 1 112 0x26bb03110c01200460008001000000 part577 part576 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part588 : Excludes 0x180040000040000000000000000000 0x67fa1387ac02a00040230c00200000 :=
  finishCode 25 0x3196cba512f1949a0cab71c2fa15abeedbaa6a15b27ad33a93e230be87b049b514574f5d115e70ab179b444296d4e9ce4d55f76ddb53195b53a696a72c61395da21e62d7de265873d1152797d6636d4e6029a98ad84a0dabb36c8b585d4c564f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part590 : Excludes 0x100060000040000000000000000000 0x6ebe9305ca023c00c0290800300000 :=
  finishCode 111 0x331218cd11965b1f93ca41a4d37d316bcadd2d734afda9b73c9eb3c6c9aa373d65a6b24dedcf60ccbcedcef0dc5a9bf1c8baf457a7a999d68e84e79e2cabe6be727ad30ef8b51ad1c465f1d76575e61f05e3cfa697b5b455e54f5e03e278bb36a7363d37a2bafbcd8e5c30fad29855e0ca2bcc3d4de8aec0a85d2614cb6ca53a62cc241dd80ccce06d4f78afa98694e2d62be7c3079219a790498da2852b6d1c5645d64adb2b079a57f118c963b12c6b2d98d14dc234f56b96c9be6e2e86b3833301b73a7ae18cd274c3855937d136bcfc09e2f3da9c8ae4dec2760bbd8cb5f4df84730ef3f596c4da56aec937b01e3226e4274f7b533494f51599f1cc441b78188d03e2d8be75a9999afaa2bb01b01118c5d94579e46586d4e23ebe440cbae84f2c3788afb0bd7ce1b694d15da4e975457a2d491c1ee586d88af10360bc4d855b09c40c9ef12af0be460d64406077017975d0fa6b2f55bf6e78af0aba5861b6d4f43e909ef37bd29af2d29c2dab7e63749a48f3739acd53714842706d97cc29708e4d9a533150a58cced4cd66d0f85fb53333aa4b1bde7c7457179c25915e9be7b5359 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part591 : Excludes 0x100040000040000000000000000000 0x2eba23058802200040210800200000 :=
  finishCode 107 0x178a0671866e97cec0ceea2593c98789bcd6741186dda4da2be205845eae96186dd0f6044dcc3da1f4d7a1f34ccc4da997ebc8d30ec2310f1a8d26da9b79c4dcd732c2de734aa401b76d464d95a742f6f3c4524c13f66eb97436d3299ee222065e5a6560386dad3df3d795a66b4f7cd5cbb5326f5f5e04d321a0ec42fca524036a710ebeec26c826597ce1cc7745a626c9a6ec213d21cb7f67b44d97acd478624cabef6a7618b519ac937f609964393594d99ae56545a49966915f439a8eda9b08b6ec017d6527503c2f97d6e98cbe6735033a4d3364937d2bd85ed133266726a364c83d5d6a2d934cea1ea6b30f00bb73d26854b64b09afac9eb31ac23a8ec2facdaef9e4df69f0f0b5e888d30aebda9934a2bcf56c26d7b5096189bd80d84daf626f33d4adc84b8d69e422beb30f4cea06c264d2be71acb64cc3f02e954b66711033ad7b308b6e99eda9cd34067b379ca8c9eab7ed1abaf4d13d66136dd765a9da8d2e2bead9330f3dea7a83ad68a0f2baf6a6dbba0b6537cbcba2368ebea3432c7758ccc8eecac996cf47bd7949965d9b53a65ad4deac687512c987d119ae5e8e2654f9c2dd11d118d4584e26e61e19d (by decide +kernel)

private theorem part589 : Excludes 0x100040000040000000000000000000 0x2eba03058802200040210800200000 :=
  splitAt 1 101 0x2eba03058802200040210800200000 part591 part590 (by decide +kernel)

private theorem part587 : Excludes 0x100040000040000000000000000000 0x26ba03058802200040210800200000 :=
  splitAt 1 115 0x26ba03058802200040210800200000 part589 part588 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part594 : Excludes 0x1000c0000000001000000000000000 0x67bb2f2daa41e20080000028060010 :=
  finishCode 27 0x150984d0cf60ad6116137c5c17d648d93108ae08bdcbbcc3d97cf23a2385e15201b618e88e17cc3a7ac38e86cf56153789e561d815315b04fe88a12e18cf9f85eb83693442b5ee88bd5cc3366e67b82e15af9abef27ab6ede24934619899a90f444cf626650388594742b690e6b916d6dd (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part595 : Excludes 0x100040000000001000000000000000 0x26ba8b218a40220080000008040010 :=
  finishCode 169 0x3b188d05e2a110455b4220b0230bb2beb20680bde88d85a2270cef8e3cb527da8e84ca0710268c2db4440cd30dacda9e19ed11b64f180f0c6d0d791b43d1135980287d316db34a230b4177b3d93d5f562e9881d11c2d4b7acada9e19da46c2db2b9e650d66d267917c7d116c37c7b445f89c78dacbd3d5e3698b6c3787a19ecf6813c6f36198b59b0c9be2d6787984df3f288976c0adb4446246870865a7601899533d11529743002ae5d9693d115e58838abd119794506123791b49d11331924418886f7cca3cfd2fad67a2365768a4ca67b3c64353d0db68ec1f156fab1573e3b0798ab07cd5385b82f10719eb00d85a67b6c33d5af8655bb6ca5b1ae6d096ad60f6dd6031a15e5a265b76916c9e4b0256a3f8855d7603d113598ab9f1df5584ec316e960394fb42de3705d75f4470b7426b3b2dd2efd0bc177c7aa442f8c1ec2a1570cab7bcc33348d9e8cab03f32f16c61924780fd79743c5edba5b9cd661b6d0f5e59e5b08ee8835e5359b2b9a9d08c91ed0f0f1d1107f6c77cd745e108e7815b103044c41923d85af9b045923da22663cc92591866a8342b5f30799ebd5cb969eabcb6531acae5937df2d9201a180595c2e6a1ed666b2d86cc7e595da22692d329eaa4d119a24d670b572e1b66ddd11c2d9810019f0f426d0e604d64d66b24d175ec2dd11533529c27b44575e40b97184f585cc7d686d3e5d115a76b3d099ed61b6c948025842664f4253d744569dbcc27d795bceb495cbb4f42f524b5c9eba12de6803a23686b96fc98193d6d261df8e0cac014a7446993b29c21527331a5f6d0e5af43e527b6490676694033db37983ed3f42dbcc5b58656ee6bd955d0b4055a116da043cd6a2db22f6c324bb134cb2e14060f6ed97adbcecee5d7aca6d0d3d6cde0995a16dd92126d85a2cade667ac332c5d785af4458545ced116c3 (by decide +kernel)

private theorem part593 : Excludes 0x100040000000001000000000000000 0x26ba0b218a40220080000008040010 :=
  splitAt 1 103 0x26ba0b218a40220080000008040010 part595 part594 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part597 : Excludes 0x100048000000000008000000000000 0x27fb0365dc68249100400000041009 :=
  finishCode 33 0x3b188b6462d46879a6f8b542d6190a75f761392552e0f57216b0cb01853bc6cc06c3285ac0730ca16c7029d80f0b6a5d991c2da97709729cc8c30ce4260f6b29abdacd9b132aecbdaaecc9f2b92a52bb300187ed34a59b66c4793284ba9a820d85abb29ee85b64aa199d8432da0e2a5214a0db038a94d33d66ad6767adbb0e713700619867b43621dbce8fe22f427 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part598 : Excludes 0x100040000000000008000000000000 0x26ba0b21d840201100400000040001 :=
  finishCode 175 0x673b188d0592208ab24aa21be5268c1f5a9e84b5eb018cab6ec41cc1f837349da9d29d35b07cc8d15a6676c600d0ba17d632bc2d80124da16656beb4c1cc1f706c616c4cabcac1f4bdc4ccc4d3073237ce00cacc8cdbb6a6c8a6b97e625699133dad456bdf3ed4e216c4419a3d18467949f366aeebe19acbe3838cd7b8633c69ace42d0666a1f687213c2f9e6c22b2ea04a20385ed66f231249acb4200f6b617d348b3aeca7ba13da1347785f4d349ef8ed4f213e84e17b79c57cd1866d4d7768b55db6f38659e5db0d7d69acd657779994bc0bdd6a30bebba3426b2c336ca40d0bd5cdeef9f6a7526c41a9e60fb53423b538cf4926cd6d3e796c615a20e8edbdc924d669164a67a265796d4d83c22eb534239a9eb536e7249885502ae60f6157e65108ecf6d0fa6b5e5b530add0fa8ecc6ed4e617853585ee016a760bbe6c56d1535a98cad6a794e6491786b2342c330f3527a13be7da9a09d0be016793a1ebbb0f36c800d0c80cce6c36cd8054d66d27425e3509e606b43427dc55109e60f867a99d794c3e42f529800cab59ca4e492bcaf9aa53552c968a451dd2ca12ec1e14b3c8e5a3d0db1524922ca6932068124d1dc85f84af8f85b0f2c36c4ad2be7bb6a6d48003fd4770f316a6672be417457da992098ad1dd65f12ab971c42f5eba60df0ea6bc2d60126fb4454c6b36a62e749b13684f3173c6837924d7cb252067620bf2c330b5b0ab53d6a6c3249b4b0e85da9b0caf5c9281a86198799f55775bce7e5a9beac4926732cf50200c0a3ba9acc4db8cce6c19c3185f17722fa8edf5509ed0f0b67d56d7c3184521866d4ed0b249b433176d772597d49b65f5a9cf1596a7594b79d2bd24da8c13f653361db26015b308b09d35cdc615abef786f38739a9df0db75f1d865b76 (by decide +kernel)

private theorem part596 : Excludes 0x100040000000000000000000000000 0x26ba03018840201000000000000000 :=
  splitAt 3051 99 0x26ba0321d840201100400000040001 part598 part597 (by decide +kernel)

private theorem part592 : Excludes 0x100040000000000000000000000000 0x26ba03018840200000000000000000 :=
  splitAt 1 60 0x26ba03018840200000000000000000 part596 part593 (by decide +kernel)

private theorem part586 : Excludes 0x100040000000000000000000000000 0x26ba03018800200000000000000000 :=
  splitAt 1 78 0x26ba03018800200000000000000000 part592 part587 (by decide +kernel)

private theorem part574 : Excludes 0x100040000000000000000000000000 0x26ba03010800200000000000000000 :=
  splitAt 1 87 0x26ba03010800200000000000000000 part586 part575 (by decide +kernel)

private theorem part572 : Excludes 0x100040000000000000000000000000 0x26ba02010800200000000000000000 :=
  splitAt 1 96 0x26ba02010800200000000000000000 part574 part573 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part602 : Excludes 0x180009000000000000000000000000 0x65ffe07a0c30c01248000000000000 :=
  finishCode 67 0x1c4c8582a0a6b8896ba19e91540d84584d78053597ae5c4a98482dc57ccaae2b8a0613f43cc39c4dcbed66b04fc01ef62637cf503219a605d8d45e288c5218b9732b4d3308c4ad33d84b0af848e8299f896c33d33bf2286865c235cd605d0d801f0c6cae59c995f1146bf8cf5846b0f77167d34b5fd34cc274be8baccad6270fc5cd9b85bc70c6d0db43125995b2b951265c31803f434cf61cc997090e7302b58da1b32b58b4f8cfe1e4184995bc5a916b612d33b02ae6a7ccc9cb9b4d39092613104c75025fa59c56d84699e7ab9516af0899f3659c236815025f08fa5ac285ea6a4f0896e19bbed15c23ba1ce2bc27ccfe25f858dac608d6f1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part603 : Excludes 0x100009000000000000000000000000 0x2dd760680430801248000000000000 :=
  finishCode 139 0x140ae49388c3314745926569984c819e850c1f23f72f70f69d64de192c27378c60285b7e9835cd35fa60e35fa4333d98dacbdbc432769908b5976c9bccf43269268b59776032578c9584f394c6a762286b0a6a99f3609009afa7ccc0a4cb451c33204df12ba1fc31d32685711f4b8b02900cabd30619348729aa2ce12e168977acd709d0adac572c2851652b669d0f925fa4942b26f8af9b85ac49bc7eec2d6df1e197bb4969d6e135fb462250a6b12f9ab9afe421b643b0c945989f9b05b86657880bf224c54864df1b46459435817f21180c9c2780b47ee93d0fdbbdb4686925f43f22f6d1b8914ec4cae22d1288c19ecc2268e6ae4cb1afc630847359eb08a22864c862a6b4c1864bf29840241a19343299ec67b357937864864c193673b1acc828dc19358a61afc33d4ae4cb142d5f031d4c8c20cbd4c3f62df0f64aed5f0f760d937c3bc3f6d5e1934b6cf9ea6a863688c02fc61694e3f6d2ebd288a6af247cf897c9bc8ee35fc25909be93e25fc276859ec99f116b3b434e16da28fccf7ab9a3f768e9be11f90ce49358dc35f26f0c92f99b05f3da7697b7bdc27a51c25309bdf3633d87b8a359d9dce5966469ce9656af42d6cfad3f09dbbcd7c326998453532d8d5df3d14cd5e357946e998492301988d13f0f716a6bf7110668b56d188fe68f6f134f (by decide +kernel)

private theorem part601 : Excludes 0x100009000000000000000000000000 0x25d760680430801248000000000000 :=
  splitAt 1 115 0x25d760680430801248000000000000 part603 part602 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part606 : Excludes 0x120008008000000000000000000000 0x65d75571243c003425001001000000 :=
  finishCode 43 0x168a853065e2918a6bb0c5b3492f445ef584584db969f35ee88bd5be7b5ec9c6dbba22f9f302e88e88d2cbccda6528004f35ee13e889afb6ee10cb626f3b9a29537daf4d7e431878e0fbc27a4f5e76bd6ddb650241246d36f3d11b0b5f3f084ccc9bf0b6d11c273332a611b3744409e4cfb4f05f933e49185c131a6fd68f4d32f70fcbe7da3d94d68e4bf2be99f59eae09bdea6a4f5a7853f06f4448370865eeb3d4cf6cdd116f3 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part608 : Excludes 0x100008088000000000000000000000 0x27df41f24c28043431101111000000 :=
  finishCode 51 0x1d8c86526160c2da1f5b754cf4454d6d1cc825034460254fb89f0c943133d8097434bad44627c326cfed11c2d87711b2fb0c982613cd5a9974d785ba22a229f760dd1dc67b0cea2219338511529d114458cf4b4c4de60ccf6d0d6ad0c9b4622715035f900cbd1dd0cb85b13e88b4d7a13688d30750a00cba67d0d3a1b2e688b4d727bd65b85a2b25a714ba22d89045a97dd4d767f51dcb9731688b20877b424bec0cd3de27e1ee96dd11b4733395435f2cb93e5a75af5a5ccf6d3e973acf4996cb633f265b09e19e6262d4326197 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part610 : Excludes 0x100008008100000000000000000000 0x6ff34578242a003421129001420408 :=
  finishCode 61 0xce6a321ac9c064ca1abeb29d1198935fb0452cf3e32e4dfa13452e88cbcf60c27865d0b49be89307688e16d3599ec32cc06c274c801afcbef11b16b38d119ab4d7e22e4f96bda498796134d9b4469bcd7daf6c138a85322885b68d1193edaf580dabe7cd7cd9abf44629206bd863acbe94e9be33da498945af6d11979d84e8b5a861298fc8a2fbd13446a5333dc80cbcf2e3cb4c5bcfb01cc5cf7b1496db4354d5844cf68ee22e3577a93ed96dd112e3b509f6f9f529d35e888cbc10b8e7cf7a9b446cfc8fe96e535a5d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part611 : Excludes 0x100008008000000000000000000000 0x27d341780528001421001001000000 :=
  finishCode 161 0x22988995b46a321841979846180ea8c2704d1188b4cf7394d760bcc0d35d82fa1b30351de88e88d68b68e1929f738944b6c6bf2af27da88da3d863317a221925f7097d35845a88cc8a7dc2231a2351fc3cd96afbb0999fd8270ddad9a11f34bd24a7da00cd2f49368ed2f186906b01b56d146c06d9b60aa382f8dc64cb529c3b8c1d476c23688b6eb76b59cb3a9f786343cd35e88b09ad24194a6b7a731ab5bb53660c98b3b49a2ce6e308fa8fe18e2cca964d110c99ab4cf45562456cda64a161a1b064c3dc51da4c4ca19267b064816931da3cfaba1e4df28d11265a1ec23e28528ddaa23595a6ca88c45ba8aa65230193477131a81bd262e1e640133d2cbad1c3bf4461e68ed3de98ba3b26f8b583253eea94774bed29b7199ec3dda22667086c512d1a2390545813ef5194197b2da57e5f432662e4f75bba5969ced3c10dabc60c906983c46a228e97333f35f1976af860e64e8a16af9739004994d7ccfdf110904c23185b123932b578b1f31b8da7276c3dc48c59932d4bb116b76da731759091e2650c9a22fb1648265311a8253c27aca5f56ca62455bbd0fad3ed2709dabed1e5964cf24706b7c7972546dabed1ecf66afb47251a5949169898a16af87b9e1696e1a4b6f0b49bc327109f7900c9865e62ed0f2dbb2d35f3370c9b11a236098b9b4c7a4cfc65e57e34f0c9b394c922b2083d311b142b4759ac48c59afbc88bd8b0302cd5ed66832a53908a3a625eec995f3e28e6054cf265ac988253860c995386a670c9acf5b4e3185b20e928c59d85ada71224df66b604459b4c99695f5e9 (by decide +kernel)

private theorem part609 : Excludes 0x100008008000000000000000000000 0x27d341780428001421001001000000 :=
  splitAt 1 80 0x27d341780428001421001001000000 part611 part610 (by decide +kernel)

private theorem part607 : Excludes 0x100008008000000000000000000000 0x27d341700428001421001001000000 :=
  splitAt 1 91 0x27d341700428001421001001000000 part609 part608 (by decide +kernel)

private theorem part605 : Excludes 0x100008008000000000000000000000 0x25d341700428001421001001000000 :=
  splitAt 1 113 0x25d341700428001421001001000000 part607 part606 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part614 : Excludes 0x180008000040000000000000000000 0x65ff5350ac32801200038c00040000 :=
  finishCode 65 0x3297ce2582d0a6b88605865e004c6d873e7caee87c2c2da73e7cae931da1f114822eccb9d2cf86330e67b4d3686b09c12d8e095d89965c5f35f3deee51195d265971971a1ee57687ba692e7d0589b97d984e9a4cf4cf6971b65a2a1888af85d465e2be1750a56c1898c4260196d317526398d810db4f44497c65f1150951984584c65ee865b2e4b6eae4d208c379a00d0f295784ba0ab932d70e71374d719eb6e9f6da22b972bb32a2da4c750b4581b063ff95d0a51978a5a3c2cba1b16abb2c06fc98da1b657e1ce2d61ce7e3631040f0b2e88c47cc3cc6931da22d830f716ab4f349d35e88b60e88d1840d4dfb095b066562bcc56c256c1 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part615 : Excludes 0x100008000040000000000000000000 0x2dd343408c22001200018800040000 :=
  finishCode 129 0x32940d630cdc1f18842bbe5611257de2655f7a5ae6110c90c99724416c1789b8950c9449da5823190ce618d317136ee69b312a1924dea53457b58cc0ba0b5a8b60cafcb9b69b76c622be0c95f76c1a62ef904a514c990ed6b6605972631d87e0cbd2a2d82c0ac27606115c9a654c8dbcc944cf697da3ba6baa618c32f2a2b929b331b4c6cb5ab7768d65c321a84530c99ead79c9bd84e7cd5e7b64aecc0614ec0a8033dad3e58663628e9879738a5e2642c819318b6299e16d667316c2620b4c5da6a9ad2e667abb3301e16db21e69735f5605c178cf580e26f8a4b3d4769b382ed7a4de65ac26c07907bb87b429e1a5f3c9449bd81688db66a34365c90f995b0c926f7e459d676d63a2316ba23532c232f47a2370905a10d6cde2e3995d115a1197449962d209d88918b326fb445b044d65c9c3189a7446936cce5db26998dd116c1a236d4618e997446d17c89bb43e1b465d14d3666975c9d116037a3a23c5d49be2d4c47446a174942123166f11b1430e7688898a7bcafd40965f208b043b40616c5ae86d2beef70db4b98bad4c2b3a9b2d632cec4acafc4d8b6d2ea9b3134c5ab60cbee0372e7a0b85b16b6c5a185d658584c9a5d10cb27bc32cf8f2c330605a6370b584c9bd3def827f3d8e87cc5d288a3da22bb7189759b053df0b66c126f (by decide +kernel)

private theorem part613 : Excludes 0x100008000040000000000000000000 0x25d343408c22001200018800040000 :=
  splitAt 1 115 0x25d343408c22001200018800040000 part615 part614 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part617 : Excludes 0x100008000000200000000000000000 0x25d341c09464011000008040420001 :=
  finishCode 171 0x1ccca50211ac619c85c2d03071329afa24a2cc32c887fa234b2d96cddf67a192193672301926bf21db77a7dcda6da38372e7a232d3a1dbdaa7dbead49f2be4a66beda269f0c1eb30990b8064c87e8939ce24b6d11ab928770e6193586f1a62eca49bdb46ca66b126fd05a1b54a65ccd5ed18474c6afb9afd62308574afbe1b78b68d65f2bed472edf12b1906a064a67c4cb85a6672e6b518c1cc6cd67142ddf84b450864b70c6bf58c804acda24a2da767630711b2cec318bbb59d0c6d62bb6667acc85c35032f3e6a88a7dbde9a7a29864c833887f11f3e7851bd4c5aa16b47cf9a14724453b2fa9cc94655eb2fd1194a65ccd5c325a86bebef45ae12d58b46a029e34f6bf197c2d9eed3ec28df94e7275e13be1a16bc6c5b6f0a4a285b6b2d1d84538c1af90dd136d7e876d2709acafe82a7dcb984cc66e87770864710fdf918b0378c34cb92f8e9b34aecda2dbf16de84cc6d37cb2e88e88dd8863891b445b4743612d77bb518c7634466f18a3ad45b4698b26989bc65eb188b46423032ee8ce19fc5acde331b3d4e16b47d28b02e725c6d0d9738a98a36bf98d899581738746d1b2fa576d26ca6d1188fb49b4353ee575b11ca0377c9097e57642d97398d95d90b68b598d33fa5ddb3d81695d0a78c4f238d82479b7f445bbdf9c46f15db943e93d0b657d3e497ea516d353582547a72081b2ee4c72d3acec46711a4cb4c3a99d925766d125f22fad3db4657424ea960b229acd7ef7711ada612a14ada34aeb78b49849c630b6b4512d40d8af6bf95da30d7f36fa7dcf9aa2304c808cd84a646a66da6f7af9ed8c23b4465dd76e605c264103498e87b5338a9605b09650fd11a4f8b587b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part619 : Excludes 0x10000c000000000008000000000000 0x65dbd3f4c568201f00400000001418 :=
  finishCode 11 0x1cc4499166c164a8612cb9732a9f6a6a14bc4895b095bbe2bdb854ce6561ce6dd263995b41424e1ce94e26ed1686d98b40d895995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part620 : Excludes 0x100008000000000008000000000000 0x25d34544c468201100400000001008 :=
  finishCode 181 0xe65032924e230caf3b132bac8c22cc45ec266af4c8b5a60d6ecd7c5b48d5bce98b35fa645ac45ec264df2f4ae48cb8cbc2c390b86a35832e8b3064e18cf9b2db307003c3be82bd48488c1b6ed0cac0667abd26bf44fb78eb116635f6c19bc465c2675954ec6a2508b33799ab9afe41ed6d0579f6f30c9459b6351cbd332adbb379b77a7db4ecdbabcec2732a8b32cb27d864a1da2ccbdc892dbf60c846060fb069f377acecde683b3231efd3584c9a7cc272db20eb01d42c1d81978c51dc9bf13612e6bec266bf04bc4dc1269f61336c86301848d32b2db18b2f91661cc57c7de211a4d995b2f0912f3a9ae5b5765bc4d7d166406bf1c449d0590b660db4708e79f97b91662575128ce420d7db069fc460481689f6d7b368ae4da8a168cbd26d35c33cb932f735ec48c43b2da32ed7b1ef937ad6b01c32f4cc24109be61133d26f984e606b3fa3b6bd7a98b59659af49bee06af906e229c3eda0a61af0af9ad7b6828cb971d2e614e8569f74c599ee43388a6dc0c979f980db470b642d79f7c38c5817de7b55295337c3c318cf66ad7627ccbb2d7b14af8ef3f185d9a5848cd3edb3ccf66d14fbc23e2a17c6038779bc62950ae95d14ed3e6bd69fb3b453829e45333d5a2a1af5f0de318fc59a7dcf0ada3452bc291fb47cd7e14790b071065e01185e7a9a498db7e654cfd40e219499542d6f3979e9165cd4d706e693d0d9739b46655af660642d5358c131d4a349e48edbede267e2eb2ecb68cb9be33878c235fb0078e4fb6d15d95e7ca105da1ac060db2e6a238374b9db25865117cd867b09c2465862d7415ab69617cd0916cf6037cd8cfd80ed940c24cac60996b2b22d61359b878d3eccf694e0919e3005b45d69967a9b5122da9470b4cf68227dc67b657616a7ddb230ddf19fb09cb0d0f332a2e311e85a14f406ef4fbacd425d3eeb4f (by decide +kernel)

private theorem part618 : Excludes 0x100008000000000000000000000000 0x25d341408460201000000000000000 :=
  splitAt 3051 98 0x25d34144c468201100400000001008 part620 part619 (by decide +kernel)

private theorem part616 : Excludes 0x100008000000000000000000000000 0x25d341408460001000000000000000 :=
  splitAt 1 69 0x25d341408460001000000000000000 part618 part617 (by decide +kernel)

private theorem part612 : Excludes 0x100008000000000000000000000000 0x25d341408420001000000000000000 :=
  splitAt 1 78 0x25d341408420001000000000000000 part616 part613 (by decide +kernel)

private theorem part604 : Excludes 0x100008000000000000000000000000 0x25d341400420001000000000000000 :=
  splitAt 1 87 0x25d341400420001000000000000000 part612 part605 (by decide +kernel)

private theorem part600 : Excludes 0x100008000000000000000000000000 0x25d340400420001000000000000000 :=
  splitAt 1 96 0x25d340400420001000000000000000 part604 part601 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part623 : Excludes 0x180101000000000000000000000000 0x67f6fa3bc038c80808000000000000 :=
  finishCode 51 0x1acbe532f032b65b36fcaa998a88a9accaca0b787e35fd85b67b2eef4ef72ddf046bf211888e61e5a6b538877e5101fe9717b97cbb4fa26633d1e7211977971b3da24f280945e4c9d10210a67b2d7152fca47a64d405f4540e99379b96b89b501827498e97621d96b33d7bf9932637d1940eb539959e522d3e16b9717b9b53185263be45061664e8855cf8abb539afe64e2b67bf993803a29168bc2f0cfdf36977b535cf828696d3aed3e16b7b9b537cfc27acf6656635f3e6365bfb5314f5cfb37888ed4c8ee61d73e6565bf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part624 : Excludes 0x180001000000000000000000000000 0x64f7e80a0030c00008000000000000 :=
  finishCode 161 0x35990e061031ccb695109f7ad7d11910c37c572f1486df6ef0a18046d26264cfc7eeb53b2b9717e45208287029d238b48b891bd15a6636a6f533509e48abda992fda9c2ae4bf085c19fb907fe1556af23f96797db009bd6a71329bf6570a1916c11e56b530757cbacaed4f42d7861b45592fd97cb391fda9c0188f4f61691691f97dd693043cb3cb1f95ca71821d735b85405792d62aa10e1ef44c80597cd27da9bd3d68f2a35a2c56c41843850d68b10af0b7c9e612a974ae443cdc2dbe4be32232b60926209760889649b0a8c5599699fd1561129c32d799e846c12cb6a6942f24125f5cf931ecb699f094cfe218808fb08ccfc97c9969a67a942fa51a28620dc25f6c19bc48d68af1699f3c976b15c2657c198bd4d847482de2f77523a80e13d67a98f84af9f32a67f15f5125183744cbd4c4b9298b5932845d81e9e99509db2b800db7d73cffe655e9c996c440099708ec279957d179733f7bb5af9f461e57832b32b527d34c0173e4c78a130fad3e1e67950e24005be0834254399222bd70214cf43ce02516db45b096b2d051b4f30f09f79b900f5c237136476f122ce106e88854c788eed3c26e2ae20679909b7bd897512df4645516fae53289c4191443a19573de0de9d15c2863316f12658cc5b86f0f896378a80c89abd2f9689b4bbcc9ae6c42cb3cb3ca03448a4cac67b10b2cea0281b350ae7bdfbe5af4bc4d846b9f10ad436a70cb450932a26de2c128a6226d9dcee70f6c236a6bb68aafc7b997a5eb6b4f33fb53501a56c98d15e78d3b5a9e16cc699eb08a21be6d30f32ac2314a64b30969f280cca8b8b08be8d32a2e20eb309a1bcc3ccada7d6a6a0332b2cc23f2996a33c3a1bb028c28b5d85b0df6a784ebd2f7230b5a7bf02367d1b2b853e975736 (by decide +kernel)

private theorem part622 : Excludes 0x180001000000000000000000000000 0x64f6e80a0030c00008000000000000 :=
  splitAt 1 104 0x64f6e80a0030c00008000000000000 part624 part623 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part627 : Excludes 0x120001400000000000000000000000 0x6cfe6c9a289999000aa00000000000 :=
  finishCode 17 0x1f95cc21b4e41bde6c95014596f7a245405406431b4412511673e792fb73b721f6b534451498b38ab9b250c5dc6957c276e7991899897e60c23ec1b25f0c3369 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part629 : Excludes 0x100001400100000000000000000000 0x2f966c9ba0198d000ab088800a0008 :=
  finishCode 27 0x1acce612e86931b48c48cecf2906d32fb215ae7a29864cd436a7123064a11d66f84229f6a715b48219348a64a1f2e87d6e76f7c1b97061f5b25510e3538ae0a80b5b840d4836a6a034bf11bd38be8da1f8f5b4df43bda98c2e82a80be58c2d836fc5cdad45406d3e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part630 : Excludes 0x100001400000000000000000000000 0x2e966c9a011188000aa00000000000 :=
  finishCode 167 0x3a22974995ae4b1f9c0501a43736914b1668b35a3c56d20cd4368e9843fa974d25bde645a76b536f7a5b97bce456c33b6a7346d20cbbd2fa279a4c33bb4dc6b03268ab36944f9a126c2e32e34c6cb8d4e715633a2e230b49359c0ce4a7d4bb2f619233b84a44d1165ec64f98ab33d42b7c108d15731ad8f687972da9b4ed2ee67aa0b4c8da99b4c33b289779872539ef5e16c1b4b55dbd0b5f58ab69d97a516467720f0706b260e64456e7ad7cb6f77bd881485f81acda616cd6e4736a6343167186a82e16cf9611f2ae11b4aba1b8d0c91e8e49618699eb73d16729f11ca70f03b1a1716784b59591caf4c31d29f29f36384792cd3253e5057cf94f9ade88369d87d5e90c99a530c948d62656b79e7f43e7cbb451a11458abe0642586d302791c829a18a27e10325166613c259b1c15e636c318ab5e9881b4bddcd8e4caf776e381acce6d309a01a1a62f4864b63d6a6db2d6f5a9cc6cdb36a73e7a82864d2ec9f24cadce6d34c96611ef626544544fb53a965ae50c5736505605775799459933d69d116b1488253258d088ba2ce7938b4fa1bdef423df3e98d17d8917bdad4e247212f70a5da9be7aedd0c731a4a65ff459da9ce2d4d902c784f4bdae7be5c472f5311c929d6a72c6e3522cd73e4235e99816185b3d97788b94f8bde18e5dd7a658342f7b1b4b6cbccdacc2521cdb24b3842312dce343604f986fa1f660e22c23e96e55e349b53239ad4c27769b8ec61380343900c991257a63697bb8994da7812e30a6a82864dd0da691ec2197b7bb4372659ea4676a59b426cb420f42e1f6644d246751666e9339349 (by decide +kernel)

private theorem part628 : Excludes 0x100001400000000000000000000000 0x2e966c9a001188000aa00000000000 :=
  splitAt 1 80 0x2e966c9a001188000aa00000000000 part630 part629 (by decide +kernel)

private theorem part626 : Excludes 0x100001400000000000000000000000 0x2c966c9a001188000aa00000000000 :=
  splitAt 1 113 0x2c966c9a001188000aa00000000000 part628 part627 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part633 : Excludes 0x100801008000000000000000000000 0x6fd76e783452894428140201000000 :=
  finishCode 31 0x583699c9e357cc270c6bb648a89a4def535a7b4ec51a20a2ac5299348719f2e5ede3580e6558453ae89fb2bb457bd995965a90e60e2ce18e656991173debe6a75d11718605a234d3d84628c4995603c21906696e22f09ed3d73e87ba04b6d84e11e4a720c279659e7da1ed4e27de369a4a180df364430758bee59618ed4f0b4cf50969538b589fb53957 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part635 : Excludes 0x120001008000000000000000000000 0x6cdf7c5824d090242c040201000000 :=
  finishCode 35 0x19cb4700d9e50187303613b7baf3cdb344bc56e13b6be120818724b298195eec97df3e92620fb45b43c1ba3f06b25fc2d857e5ee646c8c4945a2d2f64be823657613890d33da1c4cc12d4e596b497bd965acae99c1c6a697bd6af9646280863222ca179e24b35776364d167132497459da9ae6ca097e4c9b2f6d788b9b26d16795b495a7357 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part636 : Excludes 0x100001008000000000000000000000 0x2e9f68580450800428040201000000 :=
  finishCode 165 0xce6d381b8ac064f62c06ef4c44d6c031d67b4df0ceb9f16b4df431c59c3bd4deb9f0d0a21da21088995a64de46d4daddb1df0daf0d34c9c48c34d32710682b2cbed4e3f1879b539dc5e9e28c994996b535cf99569da8fe6561e69911b132c50c32cd64cf995a6f891973ed2458e2089b18441877976db5e8b36d7a2cd737b17cb064265626f50f51b441915ed4ec2db471216c79951a1b04ca99ed14285ea06896b97363d52104d2d6f446b6bb6cd6a667a48b348a1b2f85be9cecbe16f5e452d132b2c64491b9e09647619ea6acb43a1611ed332da476fa3594cf9ed334d2b42f36f5bd81a19ea62869a61ee12d21b88dd0988ee5ede6c68688d44b8486235b1e493073e7914c46bbdc34374b2550687104ba2df132cc8c48298f0f74c8da48b7c911067cf25db359bdc1ae19e93c8beb1083776f78cded2625d25d9b9def5f3ed1d8b21b3bb06856885e67b596cbdda7be8d65765e61e4bb43dc01e6e7a9b299abda66d256bdeb5e2610c880363c6086e78930f25d7e002c01eb425da2a3146f135a1920c3dad1e36879c1b97bb4f6999e361e6e8ac8043ccc8cf7edef16af7f202da7cf7f687322def19bc6099633d7d525d1fbb0b5366646c98370f4c50ae7cbdcc88d0932c911067a9c2d9ddda6458e19fb158a81b3c52cb64f96039956137d5981540e6565e74f9a8641816d3e6034195354f9ad3d80d065b2709e9955e74f9a05a9cd8e88a4cac887dad0ed4c95db5e189835a7c48c3492bad0d48a64b66b18c858258a36863222d95d85a6af32b6574ca9a7da9a18da3c03786284abd26af909a36bd0faa22a6b0876241b25bdd29e5f58777b9b359957cba2ced1e6e77978919b5e (by decide +kernel)

private theorem part634 : Excludes 0x100001008000000000000000000000 0x2c9f68580450800428040201000000 :=
  splitAt 1 113 0x2c9f68580450800428040201000000 part636 part635 (by decide +kernel)

private theorem part632 : Excludes 0x100001008000000000000000000000 0x2c9768580450800428040201000000 :=
  splitAt 1 107 0x2c9768580450800428040201000000 part634 part633 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part638 : Excludes 0x100001000100000000000000000000 0x2d966c49a018810008108800080008 :=
  finishCode 125 0xec6e3599cb4710de741500c9c259406d3d80d845f8747833675e7b371695a7b0969cd69ea5bc25b3790d6906cf374cc0d4c2a02b9ed73483374e12da7b08861cf030cdc5afe6ef0f7ad4dafc68721c4a4532f908527535a24c6cf96deef7f6a33c4cbbb73bb9d2c366af77087ad984ed3def5b5db9e69b45038cf6d46613435b4f501940cd5e51bba451eb5706a5d5a7b4950133d5a79705d969348b437c56b02d84b4e369fa0b48ab83849a53114ed3e7bf6116e77bf9e26d3daddd8daf3deb7bbe7d0fadce6af1335209abd3218d73364cc6cdaf69ec070e33f2894c8a4e14074006761390ec51da98c2b09a20bdfcb9e8464df301e8369387779155dde457b359a1c876d4d81628c615a7e5cf6efb4f4eb4235dbacd5afdbc5406717c6d19bc628e419777321915de26cd691b4b4f8b5f085a1ed4de149be29a0b3cfd9aae790ee10b01b08ce2d4e687185a5dc2734fb358616993c4558ad861416e33d98dc1bb5344d9afd73e99acda1a4be5c8828af6486598162454d584eb2522cc0630a8aef1326ed122f96f123424df74da5926833a8a719ebdf8bec21bde7cbb4f6d7b51969622d406d26112ef134c3be82b74bcd864cdb2f3736ca298bee42699c453b2f973c5a4325f569875c1a45b49337a2cc9a5ec66d9 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part640 : Excludes 0x100001000002000000000000000000 0x6c9e6a48815090000c000052000020 :=
  finishCode 97 0x339b8be533803426c26e2a03064ccaca02f3788c81bcd6030d2de1a16ef77788062cd4078889b442b78ae7d96d122de21932808d0e22b1b43678c061ad3cd730df2d6b7ef1315348b610da7b5cb01cdb35a7cc1cc8b01a80b09861d11f920501e03e891dda12b9f0cf84286b84b32a19213f4ca84fd2d7137c4e02f03250d686d995867a90c27de6ec92af04fbc4d0cf69332b0bf2d384fbd6bc34113732b08fae7c33d39d4bf4ca88be10d96da3bc4ed2c84774caa17a80a218d0cb228fc22fa656604d254078132ac030ba27d7d480eb4989f6035b39b9f06e114c6058d25b5e9c61f1b2f8b3b297ad6d99f558469955a7b258310a6af73521a80b09d23c13ea02dcf4c1b01ccacb5c82ea0332af5ac2390be462b08774c3576059705ed6655475ed6b49a2a546e6561089f4bf3e8d38da8d85b32b4c9a46169e357883611613766d1ae5b6580e8ad995a97eced80e7ad6d9ad45b1e2ad40e5e9a64d1bde7896033196136d7a25cb765e96b7899357897 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part641 : Excludes 0x100001000000000000000000000000 0x2c9668488112800008000000000000 :=
  finishCode 151 0x71186628e8ce4caeb3097ca65d37033b900c9916656e69d89f9773718c459d2b6efe48a4d316b26c937c45e40dc78019322c92ec4caf234c6893cbe99c9bcc8b2193c026f832427e3675a7806f4362d543db265dd15cde74184a6447cbb630ab9e8aac2332313799ec5acb9a887049e521c4df12f2ee2e3863050a0ecbb810d3028461437c7a7a5de56ccf513e691833d98457a61c67a7b4f33d7cda60cd5d096cded46e92c72761407597cdc064c3428b26f23130d09a4d4370c2613f451864c3cd6a7146b96477594e13d218b6864e134111b19eb09cc6cb9e30ab9b432e11c5aad9cf062619d6d93396d99676d4d0af59b8a6700dc6a01934b72f391ab099abc20384af078434862da8af36ce85d6a6d1a6f21924770b6a2bed278ddf5a984aa21b121e600d22923b5bf9778616b53a670369ac265a28e5dcdc43262d65cd4436139bc573ed4e28ccf645744d8326f9c0379c8227c192f870aaa6acf862c384b04d8b4864eb3394cec623686e364349915e61e4411898326361da4f2c99019de0227c19298f19ccad92eda4cee32d64ca67390b53808660656c9a65de77f33944f8325356a5d265459b53b08513c32631d8b5343b605acbe61d70546f0b6b495a788145998d8126d445f513f69046c6725df414c44d98797362d5afeb3b9915e9209a61e1be3e75db891253987a65a9cbb68aa2fa3d359aa6cc59e13d9da0ee82d4d15688d4575cf828493617db530a1ce530d863710c393649bcde5166 (by decide +kernel)

private theorem part639 : Excludes 0x100001000000000000000000000000 0x2c9668488110800008000000000000 :=
  splitAt 1 73 0x2c9668488110800008000000000000 part641 part640 (by decide +kernel)

private theorem part637 : Excludes 0x100001000000000000000000000000 0x2c9668488010800008000000000000 :=
  splitAt 1 80 0x2c9668488010800008000000000000 part639 part638 (by decide +kernel)

private theorem part631 : Excludes 0x100001000000000000000000000000 0x2c9668480010800008000000000000 :=
  splitAt 1 87 0x2c9668480010800008000000000000 part637 part632 (by decide +kernel)

private theorem part625 : Excludes 0x100001000000000000000000000000 0x2c9668080010800008000000000000 :=
  splitAt 1 94 0x2c9668080010800008000000000000 part631 part626 (by decide +kernel)

private theorem part621 : Excludes 0x100000000000000000000000000000 0x249248000000000000000000000000 :=
  splitAt 2382 115 0x249668080010800008000000000000 part625 part622 (by decide +kernel)

private theorem part599 : Excludes 0x100000000000000000000000000000 0x249240000000000000000000000000 :=
  splitAt 1 99 0x249240000000000000000000000000 part621 part600 (by decide +kernel)

private theorem part571 : Excludes 0x100000000000000000000000000000 0x249200000000000000000000000000 :=
  splitAt 1 102 0x249200000000000000000000000000 part599 part572 (by decide +kernel)

private theorem part549 : Excludes 0x100000000000000000000000000000 0x248200000000000000000000000000 :=
  splitAt 1 108 0x248200000000000000000000000000 part571 part550 (by decide +kernel)

private theorem part519 : Excludes 0x100000000000000000000000000000 0x248000000000000000000000000000 :=
  splitAt 1 105 0x248000000000000000000000000000 part549 part520 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part646 : Excludes 0x480220000000000000000000000000 0x35f5d6d99944440000000000000000 :=
  finishCode 45 0xb45629033754a204dc66e142f89819b8b7d2e36974ab15f31b6a7536d8522de4c76a6bc405ad4d8266561cec29337ba35208be2e856258c48f4db85365e7f76a7258923ccad97d85347af97439c46d36be5d0e6c1b8534bf2eac43c54cc248623457998931c4dd48348ef966a74ab457c51aeee88ccadd241308810fd30f32abda6a7acac3e0d82e4c6bbf32ac2f66f433e0bcb8ccac3cd32b2e24c6643123af6ccac0101eb49c1fc2933188f8b5b49a1e7446353995615 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part648 : Excludes 0x400220002000000000000000000000 0x3de5d2b8584466041c004400040000 :=
  finishCode 57 0x281c45e3e26569188b4380cde56ec3187918799194f5175d1ad3656c61e40e05df2ffa28f0c695e64653d45df56a61d0fd0bad4de8e489a72f8e87c51da9d20c61ef7e842337614bd1b04e21e8e609b5319bc29ad4f10f8705a145d518c6c363e85c5efa22d0e9de66f4df60bad0cc8cd2f2b7598ad0d3799b915c5ff82f29f4df685dfad345ff44656ccdd7b695bb0687b63a02cf6af135a6aefe03586a716b2f8af6b62d35f46867d11a595685efe4d308b8a3b042fc49e686bda33788a419adf44545db9e906b4d9036bcbbec130c6d76b9866e9beca6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part649 : Excludes 0x400220000000000000000000000000 0x3de5d2183844440000000000000000 :=
  finishCode 173 0xc4502b110bc291a97ec2903370c60f97ba26dbde9063bba59d11b49b09e657446912cd11a98e235b1c61db9c5fed11b338a3aceed2659483539bdd856206c214b979bb338d4e4980539d8522c0c819bd64b217e6077897ad6f785f97e5a1eb519955f995b92e5086cc744742eb3b7af6075ebb425e6e2d5f2c2ae9955e363d15f6a76a33dbde2d18c19ba2127cdeef7efa32af5a6d9b99bc4acfa6ecc176a9a986cde6567c9a6f723cae0b84eda16f9613b2f229ac995b44d1e1488af7c4910874468954ef5154efa55e895c31b44625545578e91a13206cc6ca7b74e88ca2b31b6889a9990ca2b6a3118be59a9e88b74c6a6b93a236896523da22c1e9dedd3249e51ecd27a232e24d2a2b10b51908692ed465f9b446cded44d4cce660f5157a432d0a2b58b0210d82f862336f7f60bd9d99cb7ba03cbd78629dfa2267359bb07e18d83016a3610e84b008cdf11f8fab614934c51c50cb8da1af8666fa13258e14934da9f103d67cb60f7d1b0c7446f12cd1119b6b98ce5ba578e4efc319ee53bd78f4457ff8980b252218bf2c0f85f210852cbdb49d85fa1332b6a614ac8962f5c32b915f19cbb8d69a0ff693345e889a9be5bd8c9df6666a72096581f2defed119955f124fb42ed115e335386446d6a7a229faf8f446a4278bba9df4db688e14e17a7ec5ad30883d0d4da0c87c78b5a26cbf6b53c2fa5589b9f0d3f5e26b537d193f453623f42e255086a3da71b53ba36158f6b4469348bcc5a8bcc4d3147481795a1a255efed4c285686b5390171d85b682bab65f15e46e41b5a9d38d97c54dd289609e601837426d110a52699826d4c5e4d0e0a18a0bcc49e9575a9c4ad82d4e16f0a5a41a9c6d061ce255086 (by decide +kernel)

private theorem part647 : Excludes 0x400220000000000000000000000000 0x3de5d2181844440000000000000000 :=
  splitAt 1 85 0x3de5d2181844440000000000000000 part649 part648 (by decide +kernel)

private theorem part645 : Excludes 0x400220000000000000000000000000 0x35e5d2181844440000000000000000 :=
  splitAt 1 115 0x35e5d2181844440000000000000000 part647 part646 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part652 : Excludes 0x480201000000000000000000000000 0x35fda69b8066601008000000000000 :=
  finishCode 81 0x2b14ca0472904be4d70c16f33789b9ebf09ea553e7b4ba4b181821731909e4317b6b5320199589560d745117b61ce0a195518110f901e23e1cd66e873c2916f5e3dfc80abe36a6be3520c39c5acf2d06981c2918188fad4e897818188050da9c2af6969b697318bda9bced98d98c80b69712b5a9d523974bc0c0e41d0bfeb86093374bba64d01e5a1a5c4c75d03db264da599bda99fda029d1a76783b535cfd07ad4de0f0c6b53d0b97db4b5ff98523da1a102bab3264c66635a9da0d32785230246f304e18da9d39c02d4e410c16faa122c4c69a7597bdcd68247b9086131cbff4e7520da4d68248ac498da2558270a66569b61896f3e4e87843e14c54e14cc12f4b31b32b44a64b098e5e38af181bc2b098e63697d31d4058a39e0e8f640d8af96b9937b7a59e656d0664c98e2be995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part654 : Excludes 0x401201000000000000000000000000 0x3fad6698924e209008000000000000 :=
  finishCode 47 0x501d0bca44cabe2b1b886048ca728422c75a9cadcb8a91b04d30f0adcc6a0bcabd12a47adee13758539945c1a6515ac6e2a93c09394e52e695b3e75f1987b4952395b945e5c70a6a5d9870a16097c4c3cdb331abab59bb7bb54ee238a7211336ccb8a10cc68b0cc3d136f87686c3cbcf92c8ba8c0d32199cba19cb0bcd531464630acc84304745a4cc3d14348ec132e35a991ec51d16b0c7a3b5342197fccdea5b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part655 : Excludes 0x400201000000000000000000000000 0x3d9d22988046201008000000000000 :=
  finishCode 169 0x2f1405e30cd62a96a79cdc5914e495e26b995a2a424e9955b5824665665695b97d9ae6d2571d78e657119cdc3e2c958b0291a9cc51d4e70bf11abe2f6f47188f6f4c3af1be9bdbcbc6b434c3af1cc3cbc6a46db32f1a8aa9c934cbc6c2f2f1d2dd65311a126bc74cac2f11168b53a43a258d8f0cba37bd5296e7b5d0db291815b581e6cbded74348dea738b6f436cbe28cf9c9a6b4b3378612bc4d2dd3a17446be19348c0e7178ea47405c29993a73b436d25826cbe8a35ff866d32198ce2ffd97ca4246f4b8cc3da48c0d652672a42a431e9b6cd523049712bda0cd33686db34e62fb8533ead39c8368b2f45acc3d97934b04d91e7e31d17da737c3965e12533796b269b49c8432e9545ff8c125c4ae2fb373d6878534e6ec96671ae5755ba6556b4f3d94a7a47993237ad3e5f6a459b1c92ccded12c7e3e8d4b2b6b36bcc3bcd98ecf864d3327693451c5a918cb1f46a716d93d39b1d015e7f3990a4210cd334e716ab9e80edb24d3045155d58a3b436556635a2e421acc62d7435b653f6691cba363c9aab8f2e284263a2fb4e75a1c1e2782d8e80e9c5c7aca69094f25acc6da8b53b7bda7d8536a2b83a1bc4b53983d191fca434b70c237985df46b2f2459487314074592656b1b89e135ed343eb5323152f61709d97c6b535ff8c742765c669d31d98da56dbdf6958dc135cbe36a6a73697272e18b6ccbb849e41a774265e397168bc318af421a5ac60659c6066c9b536e9da560516c293fb6c77b16e95ff9641178dba5f2ec2995594543f5e99cc1793674269cf0a5a7545529e2d59715c705dc2931d6c78f0664571e5c65548e6081c176e76e99e3b14846066c9b536e9b538605b9e6e9b53 (by decide +kernel)

private theorem part653 : Excludes 0x400201000000000000000000000000 0x3d8d22988046201008000000000000 :=
  splitAt 1 108 0x3d8d22988046201008000000000000 part655 part654 (by decide +kernel)

private theorem part651 : Excludes 0x400201000000000000000000000000 0x358d22988046201008000000000000 :=
  splitAt 1 115 0x358d22988046201008000000000000 part653 part652 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part658 : Excludes 0x400200004100000000000000000000 0x37ad6918aac40808e0070010208208 :=
  finishCode 145 0x210cc486734479968c44b2f8dd3243396b993bd7554542ce5ddc316b9b3b9ae649784efa635456285c931a9cb2d2e0bd99a8acd8f6932f5909859a77a10d29f2f74e6c2a80ebbac1f19caeed486840259249a4110865e323917108174617c8425ee472dd32e0a1097bd31a9dedd2b82dd32e0a10a06c0a366f26ab74cb6cdd386330ebc7832c098d8b353bcb76c31407b3d141e64b2d1884e37b99ccf96d7abab4bf4b39cc318604ce70c6a732d5b377cb1698ce697e96629a13618d99b00d9db5eb00d9c925e2c190b3b939655545664c9a53968a39455ab6724b2cbc6166d5b3272ab2f1b5ed4b76670f3450b56da39988a43a338d8edeea2b4bea5fc9df69a84384ce6e268a2b210d925aec17407b3f5f9967905eb3f339b29ad26d353bc06c2bcc75086cfebe612c0f0ba2ead92d464efc310b37b994565f63393f193965854570c69675eb5155d58ce53beb51ce684cbd6bf28433f3392c90303cf1621e302f06f97643b983c628f086cd5e6d78d7769cd78e96b82ce5f5015af67957cb9818016cd57ad81f05c6042bf719c8e3008c0c67201361380ad9dc10bdeb4d6bdb51a734d3b0866bd263ce442c165390be40178c2cea736018a126392a61e5f8ac879a285e568a3993b2f5dda1ed4570a696ecbd71eb2f9659dc2e2a2ac1e84328ad812a60b38a1a5ba735e3b3394557e43c578ea73b29 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part660 : Excludes 0x400200004000200000000000000000 0x37e5e158a140580870050200380050 :=
  finishCode 41 0x211ccd8401866c1305f98cee9cf4463395d561589b9ebed462bc54d7e4d4e68796da596f760f664f34450865159936b7ad0d7ae26f2016725fc43cb5c97f692d4720b2632912cc8300be9d4b61666a6fa7688be9d693326d861666a71a9d2a3523a06cbe931da4c4c748b247200167521e0cb69afcb0aeb183cd4e7d396da1e5b0e601961a59c98e17e0b3b29 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part661 : Excludes 0x400200004000000000000000000000 0x37a56118a140280860010000200000 :=
  finishCode 177 0x178e8ba4cac82c1ac6dd6edc6592209ab1f3b0c9a9b00da1e4ed093db0afc17b0c58653561081b2fed38cc3cd925af26a9a98b0b0cb00cc326a748c64b1ab686d60f3ef9085ab65b65157c9a205ab62560b36196ad6cdce592594e330c99cb00c913566c79615156193539ebd7ae64e2be6b99936194218d4ee9347a6b1b35bb5f11040dd098d4d83ed36d117b73db619a2bf0a56e64bd3ef353706c1b8e1190a8630d4c786d0d8676e961986dd115e324f619b43578f08b37520aeee17e86c57914d322bbacc24f3dbb435696906cc74458667a7a28e584d4cfaed0d6d9417d863399ac6195c1935578d7aece198cbf3a232e09a9c57c6a6c32d932e0c36e88ec2a12c3538418cda22c32f96eeeac9618ce663571e9675f99b0de571900b22b17e70be6c36d9d11978d71e5dd5c792e5e0ecfdba5b26646619922013365dda6d9616c37a3bfd84f327a229cba234b3af1cc9af1d50d83d0d4d864fae6b99675d5601c17ad2f0c74353be91347c364d30ea2a84385f4b5a03e88d2db00b00c1e74dba1fa22bbb0db2eaa8ae86d15ebd677ad32baac3360ba4820134a2371b76d43444d4e6196e924fd0da26c1fdba5ba65c15a1619705a1b0e1132736cbc4b7bb6cc15ebc76a2c035a8ab165e9877b75c1d11ad4571ed25e934e636eeb2d1086d9b4d978dbddf46ca69259bca2b6874aac32c03688a10e0bd9bb00cc326a76816179dad25efe91f0be1fdd11b37a84c3cfa2db2f4e6a6bc7688da8d4342e7a74efe61f8d832fa6bc6dee25f688af1d1359345e387bb4442cc605b35f4ed0b96e6555b36f01672eec5abd25866f7405a6d0239b1e26f0be53f60d47077c4db5cb7bcbeda89a9b0ce72d0d73688aeecc9d9bda2284352201785f9607515a92df4dab67d1983d3beb517af7a77c9 (by decide +kernel)

private theorem part659 : Excludes 0x400200004000000000000000000000 0x37a56118a140080860010000200000 :=
  splitAt 1 69 0x37a56118a140080860010000200000 part661 part660 (by decide +kernel)

private theorem part657 : Excludes 0x400200004000000000000000000000 0x37a56118a040080860010000200000 :=
  splitAt 1 80 0x37a56118a040080860010000200000 part659 part658 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part662 : Excludes 0x400200000000000000000000000000 0x358521184040000000000000000000 :=
  finishCode 171 0x19845bbc582d1b8ae0cdc91e0c32bc5ed8f2e2562bed4e3014b269c5a934c4db71cb42ddab830f7b4742e8cbda2032e0afcb76a109a5d29f832c2a843b4aa541b4f8814aba3539e0ce17d9ecba2842f3f539afcd20d4e2bdac8421b0a5e7d8567c7c29aa4f1b8d81e23eb53d0b7892690efacc6353920c5cc8d4c6b6615ed92c32de74c8857f12219cdc2f6cbca6a6c0350405a2d7086b3f5ed619405801a9b81bb6d462416d3699a9cecdc7f61ebb4d78d619b3b7d526baa4d201cc6ed6f35c1ad35866cee995b53d6332cde6a9a6fc295ed5a5a9da6c0434de4d6dbb69b135a54da0f69b32adbb84607898e23ec27995802f6cc1acc026b3d977a73c21a2d61e6b4f6192ed98daa40268a5f20bbbb97fb0caf6b69b79931ce8e62e8da6d2db6a6dba8421df683809e87bc997fb6e92fd99da0ef264bedbabdb42388c33887c5a0f6e96d4219950b33379959e0508545c9ac9ae52f9950b3963c4cbbf0cebcac0eb6b617e83a10881cb5a5c6bbe66e843c4aa40253e4210b36070b3983f58bbf43d935da6da170ce4a732b88407977e64742d45e9842ce2565df742f2c132bb4903d0d4ded6a63c31b42ed4e646256c9b894fb0bc9ad7e5b368af8faec99c3ebb0bd3565958558062a6c29b533eb34b8af92af43cd2c16ed4cfae53e24197b61526bb048368696bdb27fb7190fc2ae79b64b4197e653d2aeb4189b5dd5f9a60c9aea120e61a19a9b5cd6a6f8f83359d998e14935ee2c985f4a7afce83c7d729f623384d732329ccbdd67f3073071f5e17d9238f4607e6307c91e4e6e76c9d0f52d619b53d0ba5942b49ac2b626bb53ae454cb42a4615ab4360ba59e85ae1bc9da18042b617bc22e1d4def46de64c6d53530a69d422182f42fda99a59a9cf2d4d6866192690efa17d866 (by decide +kernel)

private theorem part656 : Excludes 0x400200000000000000000000000000 0x358521180040000000000000000000 :=
  splitAt 1 86 0x358521180040000000000000000000 part662 part657 (by decide +kernel)

private theorem part650 : Excludes 0x400200000000000000000000000000 0x358520180040000000000000000000 :=
  splitAt 1 96 0x358520180040000000000000000000 part656 part651 (by decide +kernel)

private theorem part644 : Excludes 0x400200000000000000000000000000 0x358500180040000000000000000000 :=
  splitAt 1 101 0x358500180040000000000000000000 part650 part645 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part665 : Excludes 0x401001000000000000000000000000 0x3eaa4680900e008008000000000000 :=
  finishCode 163 0x140dc7032168aa4d10ed13e7869b2ef0bccb1d16b32b32b4c2096095b971b2614d2a233b4e6e81675f1993934d45ed3d45e993c2988189ad45e6948d0224c42d92d70ceccaa8bb21f568734d3968688194f995887889e905bdf414e33daa8baffd6c6f7867545e65618c45ff967acf70b64d3951a91a044926ba555f1df5545cc06b536e924dd0135c9e63baa2ef6abff512b132a9d32df452da4b0ba8bcb1c7cf693142bc6e8ce4caaf6d0f6a4716a2c74bbcc7e14c80f31f0f233b9cb656220a732d7215cc98cea8bccac6732cf354d2acc3c5a8ced32c97826baa2c218c47c9a4b9a170c61a6d4e91d71c8b5ebf0a6c2787b8695c78b58a3a1a628622d869891a47a2d5e065c6966c31b534e95c7acd691e9c6d4e28e714b32e3d2fda7a7499bbd21a65c7c1f34d06742ba6069869b135e14d32a9d32e269b68a43a211546e76f7ac30bc4d6a739c9775d5a91e98f43467665545698e96d17d51789aee82fb2f1b6cb0b8ced6268fab36cccac4d848935a9cda0b1e4ccaaeab6c935cdb2dd3549e5d265617919d977acde6548dd4e53a699552319d9e35ae665545c676aa0cecd2f069b308b589a665688fc27a5de6557b68b596d269c29a6373964ba64067619045ff685b084bc65f696585db10ef5a8a69a24d2ccbed8434ca458bbe9658265de2362d4cde993a643cd16716b30f274cc999bd2268db33e3a15a24db21f66f7c27a22e64de2c8de169b51339993ac6a2d94c5619bcf8f48f4e316adb3327538d23b74e42d4d7feb291e996b60995b9f1d6aec298a3993b53453a2d70a6d2664d426d4e2d6269b8431bde15542b43f4538d35826 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part667 : Excludes 0x401000000040000000000000000000 0x3eaa0f2080a0000201006008000000 :=
  finishCode 157 0xca5b2c99caa0ced13512445bb81a6c31b9e89bc2f96b5f3515d0da1cf0be6061ceb51269a058140ddb0cf686c4db69dc22565f39812d5a5bf436995895a4590d74474344270665ae490c993b4465ad0acd35484d369816f3a5bd0ae5aee1a08954350f5a26f435b7619e2d54bf0be6d9b33963a63c9a50d645ba249116e65640796117d0af34534d7a1d1bb5af64072d1d1196fc2fa4521daccf0c65bd0aedc4322a643543fb3ba655165f569956ed0afa0562255b266d389b50952d45b269a60731a8ce22dcc9c82f2d64bb85f682b7bcb5ca2a16ab873bcda9b5ea2de63217ca43d8c4d61728928a754993913d3a61f50b9aa4322886b60d0da5e74469cdaf5bb705e32db33881895a90e34db519816d398190d5746a9207a5822982f1a6b5eb79a15d302f86da6be6be7274a159a6cda6856f272f99a6c83446d05c1f98142bb4da5c53a65aec8f93213af99a6b66da229d2dc76c5e5a21918aa440c4a8bcca2a9e2d733ead521b660da574f176203da236a74c34aed736a743dd30d2bb73ccad52f948b83d02ad1657ce979a63873b0666365918873a63658d0ec5e6269a536d46585825f1e179b516090ab58531d85f2c731f586604fda9cb7c20385366f134c427a23853285828bcc7d6a729a477614ccada1b29b2b760645625e663d4e6b53987a95665698e9634219e0577e196d4d4b6656a9a0ac4614e653660987b25d269be3cfc80f4af31a2f2d27617da8a84cc30c645988d979515d112696e99b5f446286e04d32df617da8a78a2cda8cdd383f0cd11945d0fe9be536c29449517ce5522d623491e89545950bb07eb51693c29a6394d459895 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part669 : Excludes 0x401000000000200000000000000000 0x3eaa4f448040500001000040180200 :=
  finishCode 169 0x35194b6512e88b77c8605c8ceb7177651533994701712c3686b61ae3cbee86d2c2857a1b2e3cb0d1ed2ab2c2a0d0d4af9774c4db0ddfe867a4bb859190c2b2df446cc78a7e88afca1ad686a2b65ee4862eed97cdb3a1b433cbecaad4dab47a1ada67e24d360502ebd693486d6f5a8e88cb7da4934bd2d4b3a230e76936a3c0be5209a696b4534597635cda22bbb3272a3227a8ad69286ac0344a92ea8ae72f9137284a09a1d85c8ced31d96a75a8cbc934b7bb6cb209165098679916e7ac4b1c2feba32af30aae8d6a630ef93b8323b416d4ed453cd126a015f323191b7bcb676a2db390be551a8eb515eb7af97d0b944f459a44aac66e49a172893a097d9ed49ad42e1ce04d887b539a39218da72e0a1ad53392c730ae17aeeb69c2ff0c3cd66da6bbb19bb61da8d52c82b7431be9a85b61e88afcb0ac81c0ac6c3723e3bbfc8572fb2ab3bfe86e88c2eefaa8574c9da7aeec51cfab48ef234da66f6a720b35942d0af4445df446b357c77b1e05f2094843b2699b1d166b170b53539b4466369b5ebeb3798db4469b6b5344f459b867298e26987318760f963a98e5e461d912cb5a8934b63934ca1358b836bc15630f449404cd38d853692826c12c2fa0b2fdd94cc7cc850432d142c2b0e710f4c7209d38cbb92ee0cd2ef12ba237cb6673286735a9a84af185a8cedc113ea634598a39ebd0eed2643b45350ba2d744513d16518b8b85a8d630be88f94f51752f1837c17bd16b0cef4a86b0e7520c33caac5abe0c5e7c9b2997468086b60d11a2062d460ecce94f89524bb0bd746cbe1970a021ad8221e52f3238959746c19521b2f644c2ca136932cb31f65f32219ed1152f873985a04c025e323b49b446d26 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part671 : Excludes 0x401000000000001000000000000000 0x3eaa0f029240202800008000001006 :=
  finishCode 165 0xd4652d97445b19d8d36919c40791665854558050d65eb945691548e4b340c0ec2b906c39ebf09c25df2516653e68f931a6b79e13cf93a1ef5f67b5d269246ad5f98cdf444d3618e6f3c173379e2e53d7e65de2362d451622d78b7afd115f99a433d10269b8369d2dda8a7986c431a2ce18d30f2b73bfe88da8e13c59a69d16b84f34904322d61ff50b4074d533742b435a5fb44659c5adb178a41b44501ed365accdc7d6d11a7197d93a740d85850101f446301c276b317f78150bc27a97c2e4c060013374e95e59870b988db0c461d3a6b4dd11a0562e84d7677446c5a85ce86d32747af5ebd6bd7688d22c50e18d9bcb0a27d502e558eff59b8a2af5c11e2ea7395bc1b4d597d165993a59e485b1d16899564342c9d3a228b2deed8e4d322ccd05e698f5179826cdeb168aa59dda22d0a6728762f21572c5652340d93a23686bbfc46845c7c7a1b11f28bd2fbcfa74bcfd84e89330b31b203e88cd05e698f791b05da4d45e926d4501f4462345e6977d11aa2c113d16692e78dd117a57afa6d8a19ebd7af4474111b4518c3a85da6c9d2d4f84f4be89348b45c223eb374e9a596e998f17f4499e58022e7d596f9850996f7a1b656ec1b86d9853299aa663c5e53a6a90c9e19cca12a5b6095982ae615f267c7aced609d3273c51cc2a74cf3ef4794ce5b24833b049e1a6dc2ca651553994fa1e5426d265239956c3a58e1ed4e680f8b84d148d0ae6f3689827c3e4b85eddb0e95eb43793b37a966566206656d0ec31924d1b069aa173dbe88c5aa74d2c64d711b14b434c5ac46d82816a3274b61b76d2cd2df82e857688a74dc2f812b4cad97a1a9a6a29a03c86b686de72df5a25929f342bdba84a1da27dc21e6b37a4b995a6d7af4597afacde179 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part673 : Excludes 0x401020000000000008000000000000 0x3eea5744f953241014000040010002 :=
  finishCode 29 0xb85f259a0b291caca9ccca92a8c3a27ccad4c6a738636a6a163073417fb539f4e2bed4ed054b37c99959646268a098fa586ca5ec61ce26e88827049c54da0a1068772de97f21dcf218d273e08baa84b49cd0a1336936a75a492acd2192df436ccacabbd7c4dbd263e78db51609ad24cdd2fe995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part674 : Excludes 0x401000000000000008000000000000 0x3eaa2704a041201014000040000000 :=
  finishCode 165 0xd45b2897c45bba59318f419d5c1914dbb4d17808574a6c59c319a6a298bec4aa15f1899534d9939dfd78cfd50ee5868b5c8502599c44f25582e62a69954133f1b0c5dfe17e8f69b5bce5842e5bde24b4530b9844b2504aae8109a59e655b1dbdf4369671615dd5a172d85f32a7c332752a99cb925e677f8b58636ed9675159b1e5867795c7d0f88b77f339967e052259e5c1453459a02f5d2a289fa0b2f5c63390bf59be86af5aea92ea8accad12b15edef203cacaeaaf5dd1c8dda69b31f5a4aee8f1c103682aee8b4a8aa15f02f9b8b3b9f56d45ade6546750ed16718f63452b71da98578cecd1c1167521ad1cbdb69b79bdacddb11f4b6934ba179b8995b519a5f415b1db762a5bb68c4c1b1e85fb37a4b4d36e724b6979b9cf7e31b97bb51539a59505ed4db76cdee1580b95239b9d4bd7e625d5151578b9617e58504c9746773190be5217e60b9453459a056113ed4eb3750b5e3a2369b6d46584d357aec0bba172d0b682da9bc5da883be16d99beae10d2cf6a79c72525d15f6a6bbabf334b519de4d35bcc9568b5b51187b53ad45a9cd35bcee934a0431b8dbb5de6d0f50b7d342b50bb397c5ddac445c66ef472c77fa22da9e1f618e7799596a74af9af44adde4d34d364072555c1722eec2ef2a2bf3083379de49562ce8b56c342b97e6c98c72457d8436a2fa6b9ec0f48d030acd2595ebe6d36f3c279f26cf6b3d9bced3e68f4b0a9a13935e13ca1785a84f4973c8b79a85d93397c539913c676097034da0291d32aa7311b59ba90c46d6772caa735f2d266bd6dd5e334d45334d9b8e81347a297c2eeddade70e7044b71a1dd32732b04925a1bd21848b28a85ad6776a72ce493863863459e18cf4c31a616d4e5e70be0b542b86394d (by decide +kernel)

private theorem part672 : Excludes 0x401000000000000000000000000000 0x3eaa07008040201000000000000000 :=
  splitAt 3051 101 0x3eaa0704a041201014000040000000 part674 part673 (by decide +kernel)

private theorem part670 : Excludes 0x401000000000000000000000000000 0x3eaa07008040200000000000000000 :=
  splitAt 1 60 0x3eaa07008040200000000000000000 part672 part671 (by decide +kernel)

private theorem part668 : Excludes 0x401000000000000000000000000000 0x3eaa07008040000000000000000000 :=
  splitAt 1 69 0x3eaa07008040000000000000000000 part670 part669 (by decide +kernel)

private theorem part666 : Excludes 0x401000000000000000000000000000 0x3eaa07008000000000000000000000 :=
  splitAt 1 78 0x3eaa07008000000000000000000000 part668 part667 (by decide +kernel)

private theorem part664 : Excludes 0x401000000000000000000000000000 0x3eaa06008000000000000000000000 :=
  splitAt 1 96 0x3eaa06008000000000000000000000 part666 part665 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part677 : Excludes 0x400440000000000000000000000000 0x37dba4606222200000000000000000 :=
  finishCode 63 0x6d3094035db857300a5ac33a1f0f9b61da1da9c43bebda9cde72918b3d6a6c32c4b53a8284bf198b4747703ee88e85c6726e66e75a0c253a234d7122cbed02b8d4363619a3ba9ac28e195bb424e7d788fad4db8dbcde088ae5a9ac1f5cc14bb34da59e85d1dc47cc8cf16d3647e80e7cb4992ccce492742d2bde2e9269bf42ea57b518a1339a628223e6166bd967d0996378b95581d6d2e58d70f426b4966535d832b87a22d7a9eafaec0b4526d3276a345099cbc5d35d26d37cd36ef2d7a673046831297457623f88f85b570e6bdd099af658f0940b230c850cdaa31380887ad4cd2e196955b53865a284946d4c6253d60a37d7619 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part679 : Excludes 0x400041000000000000000000000000 0x36deaa846006208208000000000000 :=
  finishCode 137 0x39940bc572e8c3364b65a9c31233bb49a135c66a6aaf088351bd47b600f3e16958a38b59938044c2da5573ed4e56e6d58a3b53c2788ce5dd6d65cf6f56d5a6621a96a729cc3ced2d4e539b538ce6b534f58b5879539ad4ec9908c37ada9cdb2d8b1370db5a9be2d4e40798d69550b523b4b901da554e548e539b53da682e188b659148d4e5f0626b98fad4db6669c026b641aee0bcf6330360b915b62e84cf1b6627a694ef8e80ed8b7478447a03c616d77863285a03985d44ba4f0d1573ed0bb4b879963269427b41e2d6d4e6ab6f5d0b887e88f088fad261e49a509ed4df06b49509365b53a893422b909cd56d8def3e4934cbec5d284ef93a1710fa13c61e16442779d9ad5bd663eb5378d981d0372cf8e2bad4af862bb4b1d6a64d7a0da5b2c8a46a72d6f4bdda99aeda5cd6f0bf6a744b24d1ed611334526b35d964c8d6a6082daadb784e9eadca4b113a5ec1748cc44e97b6a7b53d09ad3ecc62bc4c44f698ed4daee40526bb538251109dbd68afb530934f5b53ad4e149ac9749a4becdead4a3126ab1819d5cf80ee985b649a6ca6521b5398412989fadeb4df5a5b6cbcfda1b3c5a90cc9934da9912c46f6a74cb53bc36ca90c80b6824af2d75a0da0a24c0d7680dea2df4b5be4b6d935931d68246f6a64575a9935da5de2d4df266bb26b16f263b518546cc62062bcc067c9a5d8af083b53355 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part681 : Excludes 0x400040080000000000000000000000 0x36d6a1146100218400801000000000 :=
  finishCode 113 0x2b93878631f5dc9785f95dd7d3a9adb55866d3ea6b6d585fb536dbda61341643739a30acf82de66bb100178c4debd85743e7c97af093a19e285866d4d856b3d24d9a6f09d864d8f4178b5334b60b9a0e21c9ae23d09e991619acf741603638dcc9ae375c278d15badf05f4d86649789630cd21c8c0311f04bb6aa7ab03b61cf3a6aa2f784c218594dd5b17086165d0bda2f5cf3a6eb16a68abf336ab20cf4d557ae0f3d118817d57c7a20658d872300bcecde66ea9eac0f84f361bce9bdb799bacde72fc9bac939978c830ce12c0f473e0c50c47b6ada99a59b5da5c6eb6a6d8b0dabe72139359b1dd29966e335d1058c4ed04c168f5f06d4e90ea73427165b536ad12ba995b54d8ed4ec8f496213c4d6be6f5f4aa935eb34467c150b9aed01d3fe363e0642a1b498630d8e9167b303b0acc2c83b6a66ab4d70bdbe9a138a3cc2b66a6d74e75a9a13b0a9a5e8308744743e991427a736f3427a63cd55f4ee93450b9e74d75b8dbcef0d8766b613c33b03cb06a39ebd7cd3fed2e50b6a326b8e3209ae5cf5f92e1a9b5aecf5581c9ae60f0a45a5d85ac034774d62f710a53b425bd4d1622b6d5601b424d145ef446 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part682 : Excludes 0x400040000000000000000000000000 0x36d6a1086000200000000000000000 :=
  finishCode 105 0x2b88b738e63ebde368c33c0c26b0dd5bce42787319d77bb05e9bd01d074f364277c169b3634ff901c676c0f6b0bda09cb438cda618cd86fab0be6e633adc7b59aed09de466e77b5a6d94e509ee1a035b8dec29e195195b9978845f18675970b0135b6bc8266967ff439a13b71c84e80e4a7209b6ecf26dd2a5f4df7cc2592c1b40ade04c0dadb66a434275f37d3b41a21e25db414135f324dad4d7cf589e3213ae1a97c36a97d6a71b5f01b24d8e98d5f3b53b41970e6357cdb26b53a6136bda213cd5abe75a9e32e16a66f74a6a6d92caf9a03c14f1319b1f0369a080284c7966c6dc768373be35109f0bec317934b3968705e6dd4b3c17b42db771970883d109e31b4f15f360f985a9c4d22f6d77a1730ada9cf109eb532637c1b42d81f98d9359ebe0a138a3c7ff82e46b6a7cc5a134a13bc9da1278f4c296766af27684d24a59897b5dc4c62f7183f3904c59cd2d09f41e26b7a534b7a135c826c030026b904d855b9e6e9d0ba6f (by decide +kernel)

private theorem part680 : Excludes 0x400040000000000000000000000000 0x36d6a1006000200000000000000000 :=
  splitAt 1 91 0x36d6a1006000200000000000000000 part682 part681 (by decide +kernel)

private theorem part678 : Excludes 0x400040000000000000000000000000 0x36d6a0006000200000000000000000 :=
  splitAt 1 96 0x36d6a0006000200000000000000000 part680 part679 (by decide +kernel)

private theorem part676 : Excludes 0x400040000000000000000000000000 0x36d2a0006000200000000000000000 :=
  splitAt 1 106 0x36d2a0006000200000000000000000 part678 part677 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part685 : Excludes 0x400028000000000000000000000000 0x35f2d6001980055000000000000000 :=
  finishCode 95 0x73359c4d455033550877244fbb8278b62cdeab475329eb98abd2c606fa7a1a63786330a4d89a5b15bd69aed11c277d76c5943a2c0b0a42e88a3af6a63d69a7be86b1531efe14d29cc129f6fae66f853137688e0b8a5923beb91ec7befaf83f852893682c54bebae8d82b1a07d7945e95d4e57fcd6e20c2efaf454a1ab65b7ad26c86adeb1ade88913c95b0dba2286afaefa77cb85714be5ffc2919b44f45919b93fd4e511658bc75c43b6611ecf2622383f2eefaf4771fda59d35d9784c888c42ec13692407103e14da49ece88b04bd2d36c28ed2686a686fafa223369f760661add35da2332a4d2faf184fb7b19075a4e8a15b9a49a4da5865b665454e9853ed4bdf5f013866581f5ed068730f6888cdbd2d84f4db2eef9369330f0e72efbe9b7ae86c82c12819b7a598245ff09e9617d30a76eb864b0d4ca9f70dad96fa6f4b4cae8299bb6db7acfa633764b05a241240a735b31b9bd427e7a56cb31b95bb44466e5866a56eb7a5d1198735b823e9c39d696b93a0abbe48edeba1b688bd28cdd30e6b748aa430cde89b79d98d7d3263827125de6f54dbb09c56e5dc2860ff87b8a1b4115b15ba17e26e5c69564cd7c198d6f5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part687 : Excludes 0x420008000000000000000000000000 0x35fe74012184001000000000000000 :=
  finishCode 85 0xc05b2b1a045b902228cdc43da0a9b6dda7fe6864bf1ffa22d78e621fca2a89ec33149c4d1f5e18dc72d0be4c57c81b764fb6e38739e95b0e26324b898db362a618bc7131c8217cfee4fb96ba64f44668faedc736691ccd868b27ffa0ac48111466cd0e60d6cda21cffd7fe4089eddb1a19ffcbc7a222c2863512b10ce62ffb06934ca724bf5c339ccae29c9e7d496c120af4aaa16c322df525c31979b049fdc1259e60925fae19bd0e613b2d70abb04c11f084b049eca1db0cde211486195c1319e2cf4b2fb3267f7439cb5846cc0cef34b8c36a24a8ac57af1996d2d715289fcc4459166195c7c188cc98e2be9b64db2637432180783fb4a78ffd3248a57b61cdf0b432d1d31cc6d36d82e9b75318b7c39af6a69d82f6974aa7f7496bda66f1c87393248a497f07eb31 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part689 : Excludes 0x480008000000000000000000000000 0x37be74100990001000000000000000 :=
  finishCode 57 0x30158b65e116f715019b48126c2fe4c6d7732b38c29a56c29c5fdebe0a77a58f5cffdf5e7af2639953637d78decd8f41103638e365c51ebc9af06ed05b4ba6b5dfb415f4f4369514dba6b2fb69ba659ab4dd688cc6cb6d5b44577df5cd56c273377c17d31e39e0534e585726cf5f4c5fec0f43639959af5b74deed0dd118a97d79958a1bad32d32af4b34dcbbe86d1340deb1359b2cc6d8526aadeac2f5082571f116b35dcc3cc6b42d8d77853131ccac47d862f5e4d70f38530e745accac409362636bb74618c9a646785332b00879c1fb09d3370c623ed2f0a69959aee2be23c44e11f20d8af26b995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part690 : Excludes 0x400008000000000000000000000000 0x3fb274000180001000000000000000 :=
  finishCode 157 0xae5e249806198a4e2d8faf84b25d264e26999545b3553756f5b41665516e1b699552d44f617916e65770863066a279aad123166c2fa0b0613706d71530cda27cc9c95b14ade732ac2edbac2f59dccaa56b718669b1eb1ad60cdc2551bd61e6a6d977539977ad46891951995d0da915a35f4e545ebe64cd550c741603638dadb160cddc4a8cb92dea8b6862c2f051d82b1645ff617aa37aa2cd85332a6ab15f4cae14866d0f736a866ccaaf1866cd8a6cb6ca25f116e6565df7797af37543f60dd0457d3226ea6e694793b4462065adaaed0d97d7814178a4e2e0fafb8d6218d1168b313f4cab5dc82f32b48b3c9a18993ee341705a3801cfbd4be65466e96e687b4bb4d9950cdc24caa24cba312a863379c6d732b60b84c10c669b5d117f363459a254deef8c0431c299e4ded53edb4d7b6b3fd0da43867d0d80843353ee1ce4310cdb0683086f7306a2c9b5c3ecfae3366c75424d91645fe2cc93644917f32fb446995a6c3374151275984aa601b367b57d70cd36d3759a561164d957b69957d59959a770a64599950cd5eda655f55f5c335b8e0cd7d76cd8d8cdb665516f59a8dc5b033689303614a18afda2ddf250bda86266f52ecca926e14ad1c787389827dd530a62697c96bbb0c57469954d39ebe65419ec29b355ed431b6603088b73437390614c2ceba29f6dc6f273d1934c3174caba26132adcb610b55a69934bc8d1430f75498610c9caf864d383f6849efda5c3daffe0fcf8ef638089f97b5834dedace20bdb11f34db62bd8e14cc2f20981b9b06b65cdeaba34cae817ff4269656f59915176dba6574365096e399537345b (by decide +kernel)

private theorem part688 : Excludes 0x400008000000000000000000000000 0x37b274000180001000000000000000 :=
  splitAt 1 115 0x37b274000180001000000000000000 part690 part689 (by decide +kernel)

private theorem part686 : Excludes 0x400008000000000000000000000000 0x35b274000180001000000000000000 :=
  splitAt 1 113 0x35b274000180001000000000000000 part688 part687 (by decide +kernel)

private theorem part684 : Excludes 0x400008000000000000000000000000 0x35b254000180001000000000000000 :=
  splitAt 1 101 0x35b254000180001000000000000000 part686 part685 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part692 : Excludes 0x410001000000000000000000000000 0x3ebf4a800906080008000000000000 :=
  finishCode 129 0x32978ae5b1866e932b30b8cee22a99ca828aa9cccacd36deb49759bd6268db73dac43d9b84d935da1d32abab32b372d6864d732adeb2e384de42a0c46c59b55e1605d597fdbd64138b589b9a2e7c4d72ef2d9d508a4c6cb8e27a80ea02c8867a92e63709dec6e92ef450c51b4ad2e2ee2f8f3c1935980ee2e18888351b1542d45e98e1315d55a180fde545bdd108904f14e694f60d617b6616c66edeed8f29f2f899bda7cdee66ebe329cb0baf1cbfe4d744b25d208be268b372bd1d84e9faf6b531b72ccacd56be30f712ec46ae7bc4c9fabdac2f206d99ec5f0d7b585de8e995c2997bd0925daa5b2c9b819d99589ad4e4d16d0994569b5ba720f06d589ac84d8357c43fe7957bf26b345501841e6d55f1501795995c452259586e76e988fa98e58db6d78d835ee6515995ce5c2a8dcac28ade148ed2e963971a53e647426ceed2e1b6991995d095d5a4ba63548e5e6a61b4b6c7517995ad2de8e6365c66e598db85633932b4aca9ca8bcf265585e7d5b3ba56578e99598d9efe893c905d230f96c1b143536c4ac57cc8c59b32b189612ed32b15282694f4cac57e82cd320c747b32a67327eae3d31ebc73c25da5e4ce53f6d2e5cfa6d979 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part694 : Excludes 0x480001000000000000000000000000 0x35baca820026400008000000000000 :=
  finishCode 165 0xba6538990d06a28818f606eb365b438cc496585c966501993b53ac3a1e06405a43a5d995b535ed983c1f16a75c7b7263167987ad44066d0b01bb42ecde96c98daeda76a73789195263259ad4e5c6a5da5b981b2c41f4614f26b6db6eb72598d136daaf374bb5a9b06da5da1663e4d6f5b6a744aa3c0d55a8fa70cabdb8b7da9af1aff8a5d6a69a6f72d96dd73c1959edc98eb8e41959879f26206cde4b7c27987c1b6b5a96ccde78f0c299baed4d7fd83608e461779bad2c5565ac89e955a59331723bbd85a66ef7f2d6f73391eb67d19959ee4cded89a75a7e13a6a998a02bc493199bda9ccad2ecbdb6a66bb6406460c3a64706469b6b4b9673377b925f7959c92c16f9405efdf46606b53b0a4206d045be79608656289049630bc5305e1fd337b5324795b33117978131b7ad852bff6a74b34c3998da4d696dca482dd64c74860d4e050998cf5b32b5a0998d3095ba61e656d4c98db96a732b123998923d0f3266d2ac548bc931c81b8b0d05a1e6d4c26707d7b658e5e608fcac4b1826d4e7cb315b0c6d4dbd4c567958737b9b53a5ded062868730a1b539841059e7d160997798d2efa9c61cdf4456c5e6995609b53337c44c1b09b737acbb8bccc6dc1aeeb539953fb247995b0c45e6d4e179b8450d0f2deb69345388fc6f5a1e663422c5e62d5406d16834ca99bda5da8c2f2eef30f32aa032ef8488bcda218f0987a26e2bd8931ba1b3e5d3699bd0f6fa384f450c399ffcc6c3dd4ab4c730ebc78520d0f732b31f15f6a6e87c9a206655911032b3258cc3c3dcc2bd6d2b60ff4aaf2711f19bb72be8e510360c30c7782f1c866f4c7c54c57be9c1064c76a7385cfa26c26ccdc98e3ff9878877c52091c98e3373319ebe331 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part696 : Excludes 0x404001000000000000000000000000 0x3fbaeaa00486020008000000000000 :=
  finishCode 67 0x15cb2510676c1906f58d9582585e692ab598cbec47c5abca9aed01e0de9de76619967a6358665ed9f1d866b144c850182585df0e6197cbaf12c845b1865ee688d6e9791a23e236d4de9e7b18b5b536d9783b0a5e7de7e5017b19ba6d4d8657b6f1089630cc48c4d316add21fb4b8b4ecb3934b63cbbcdb2b4737bcb8cc3b4ebc11190b538637ac4d26cabfec2f646f5ad269cded4d95f2e167609d434ad47b85260ef72d8e63f51219106179a452582bb36ccb38408449aed662f6316b5a49aebd8bead42105c33bccaac5a8b7bc5cf06f4f83f3bcad9d32b8526bb16b355e188b5cb5b7ab04c417b45ae7c789fa1f697501ea5b2332697c735d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part698 : Excludes 0x400011000000000000000000000000 0x3dfb6e900606008888000000000000 :=
  finishCode 45 0xe2672b819b4033994e6d4c675866d9a1752b91398ca90da98ced41406d2e5c7a5988f407b537b9783a966a8a170c877a2ced4cc7cd75486cc6993968628742ee954a81aead280f72d0619995c298c2e636a4bd0b695b536b79a566370c6233b5369540798d6192d1a655f466192d9a6350ad866f140ac30cbe2d4c97d4e6606a4b5a1097977233a9b54070a5e546468667298a2b4df36cd37cb8f2c245a27dbdccb6c294b598d4076b7a5faca5b5c646d4d406 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part700 : Excludes 0x402001000000000000000000000000 0x3dda5a840826010008000000000000 :=
  finishCode 119 0x572e14896224a29c31b6e689a5d3396196e9ca592084d74bb59ab62a6ad39ad0d66b0e73eab72d682faa9cedaf1433c6b63b0cd0258f074caa80b0ca27f11865b9622926b6f525fb8904983c2d4e94db513c56ebc296f5724c9cdcb747c7a23ed3e77f4d5a47771339c29a64db1750ec0f19b6c3f4f14ce4625e7e594bf610da7ae7c312fa3450c478c4d408c30cda4d15f6a6f468774833c0a80bdfbc4bf2711ca59b2985f4c66ca66e77d5b499599a95f1ed4d404625a2591a8c410ecdd2dae43b4acda5b4cda9d2ec4976a643ad335a9b74d98cb2a940b821dbe097eca67a58696d72476e79ba658ed2f41e08f79f235b53e23b19043b434da9b74cbcbcfbe1dc218d8b83f5a9bc5e18b5cad0cd4b618ad0a6ad97b5cdc1c969735aca8b7ae14d66b2f3a136a6dd70cf614d9ae0bcc7c50bdada9d221984f35cc59b7492be13cf367b25fb65edaef076148aee10de240b0b84b1cbc8f4cd76dd6f6b5a9cf22867b5b2fa882b33eab62923da4ccad48603b6a648f6a7375b2388ec8c591ec4cde78d26b88f939d39e78d26b6eba28663dbd61120a44bc890d6872df6962df2ab3c5e14ca892fd22309cf5a59ec92bda5c4be7b241b17ee85e0b9ecbc097e951b53967897de56b4188f8a16e5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part701 : Excludes 0x400001000000000000000000000000 0x3dfa5a800006000008000000000000 :=
  finishCode 169 0x389a8d05d0336b144b4304d53288774caa279b2c57d6a731adca8770889bb0b5f44cdd8665c644943f9864d96656b5394d4495eda25032889f30ccca9b2b72d31f0c72ee87e8b332a4972f1b639b2b6acc7d12289f32b4888bacddb951651268154995a2065dd8665c5b95bd513c9ae9716b59b968154ae36cd32a87689e877222e52b985352ed388ceb0cd2311306f7905105ae9ce4d3c312275ff7b95ed934f0c743e6a72279638856d4e20dcb4a6af68b7d125367bfb3dacc658e9757c65f19ba6d948a62b1b564496996d99a55185d125bdec1b269a5db06dbde1f619d2696e9ae34bd4af30e8928a66ab684da999b934af1cbff749036183585e59e87701dc21337a593cfa5bdb56b4f955b4b3553cf5ff9a572d2e449453b35b06dad6d2ccdeb356f55d578bae50338c32c2f5a98cecd185c9ae43f44f97c6c99caa0cec80d55ee688f609869a9662d57fdbae5ffa5f6099126609617b539e48219a060d617863a59cd954861de97dd093cf689445aa500d9658e955539963a5e6556cc658eb536ebb8623415488d9484d95a9143686b62935affda9d54251a5f511695e96b9819519b14d95a26b435ffb862142e7c13655176ab9bd6d4d7c6d26b85a2b948ba229a2ce7328c1328a8618c8cb222e79bc275016f7687ad4c04d825485eb66d76f76096f79486d92c1916b99455ee45e540513f107b3290a9ca7ed4db6a64bf30cbc1a27e81f1a852150b90061da9da132df66384f2f3a135a4e0be13c82996633dccbcda9cc12b4307cda9c34da59ece0bc80f842a42a72186bff128a22e73101872908c8c9fa87f5621912b30c934da9affb0be52d4c30e5016193fb98254065dea596b943b619 (by decide +kernel)

private theorem part699 : Excludes 0x400001000000000000000000000000 0x3dda5a800006000008000000000000 :=
  splitAt 1 109 0x3dda5a800006000008000000000000 part701 part700 (by decide +kernel)

private theorem part697 : Excludes 0x400001000000000000000000000000 0x3dda4a800006000008000000000000 :=
  splitAt 1 100 0x3dda4a800006000008000000000000 part699 part698 (by decide +kernel)

private theorem part695 : Excludes 0x400001000000000000000000000000 0x3d9a4a800006000008000000000000 :=
  splitAt 1 110 0x3d9a4a800006000008000000000000 part697 part696 (by decide +kernel)

private theorem part693 : Excludes 0x400001000000000000000000000000 0x359a4a800006000008000000000000 :=
  splitAt 1 115 0x359a4a800006000008000000000000 part695 part694 (by decide +kernel)

private theorem part691 : Excludes 0x400000000000000000000000000000 0x349248000000000000000000000000 :=
  splitAt 2382 112 0x349a4a800006000008000000000000 part693 part692 (by decide +kernel)

private theorem part683 : Excludes 0x400000000000000000000000000000 0x349240000000000000000000000000 :=
  splitAt 1 99 0x349240000000000000000000000000 part691 part684 (by decide +kernel)

private theorem part675 : Excludes 0x400000000000000000000000000000 0x349200000000000000000000000000 :=
  splitAt 1 102 0x349200000000000000000000000000 part683 part676 (by decide +kernel)

private theorem part663 : Excludes 0x400000000000000000000000000000 0x348200000000000000000000000000 :=
  splitAt 1 108 0x348200000000000000000000000000 part675 part664 (by decide +kernel)

private theorem part643 : Excludes 0x400000000000000000000000000000 0x348000000000000000000000000000 :=
  splitAt 1 105 0x348000000000000000000000000000 part663 part644 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part705 : Excludes 0x80600000000000000000000000000 0x77d90e8503c0000000000000000000 :=
  finishCode 171 0x1b4ce5e2e964a855113515e38f8993a9b6d4df05f4f00d9b379854da9d10720a639bce98e899884a8cd634b348b0df1061666a7a17598b58da9e88859d33008975cca3a02cd78e79d995a739ede97ccc6b0c2f3e9c4ab5fb78d98c662fa7a22dc7688ccaaf1859938d136de3148e601e95f274469953176cdb419a7659e1c4c5db366f30abb4442ce99584418c471b0e6d36ef6f1609a57d85dbce617b5378379cd67482f9715ede7206e42d4ed069516d12f331b5fba47a625bcf315c8c3f1b864396f18a5b10e66932ba1f36fda9c40d98d94da2369315f1a9da22dbf306d1861a9d31dc633140d9dc6656d4e6a3d0d9337444cc6d4ec9509021c8aed69332ba226a76a69df10b5a4ba25d66af99594688be6d316d47598a77d6a780439b8688d47b6a66a6663688c3684bda991bd74885c10deb1348a9ad2c2749c620e09d9a551bce1819816cd353a2bcd4ec31993d11897964d34466cd1816c3ad4f446cf56f5e6e20e9a552c8de73cdb4e84b8c0b79d6633cdbcdd64b64d30c6b5399586d09b271980a2cd424730bf4daf9f82f6a66a74db5a9d15e4e348f5a59a9c43306a734ac46185e9ceb515d598b08508fa62c236d114edc31b436cd6edd0f9a3ed2585ed4575421ecc5c2f0ddb127cca8c1857be5d0e3687c36c4dbd6b0bb79c1176cbc5c2e9546c054bcacf4f32addf2888598c9b6de32fb2a22ef32b378caed97d32ade332b378b67859938cdc332a3074c98591b3e79d9957d309979bacc6ca744424e6566568956f1b5379da97db3df26d4ee964aa3f02746048e6b530699957bf5bdb0a6cf705e7cb99524fa6562be2beb53271884a0d2dee6167a41ad4f446d2e7b9d11 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part707 : Excludes 0x80220000000000000000000000000 0x75f486c18144440000000000000000 :=
  finishCode 123 0x1a0e2632e964a866113515700f5a2ef6888d1b45d6a332ad7f15f5a991e8bbd3330896d89e3a1b3e6567d3887a2bc68e5f16bf5e3868e656a93074688d132f171569eefa7807b7b8617cc2b683617aeb9128f8d69765e66315e97244b68881a2bd36e8ab5e5b44536e2af2198895ad0626d78c68e39137131da0b0ac55d6831374c714964cad25d682c2b10b370d25da0bdbd31cf6e81b4db4cac220da1afc68ea7133f95f9bc6ceea67d119951a397585de97dafc68f31687c031cf272eade267f4b3439ccaa1c8d1c56c9ef32a872de228f30aa1cda2b0346e86efa654cfea144b299abdb3e5dc8f428663616f9716bf263a98e26c7ed7c5afe2be4f7898e9a50b57b6e148c83e068e8867f0c0a197c625585de6eb418730a16bfa9045bdb7e610e7520be8b708b7931c330a6885887895315b0a5b8698df15033fb539bc429c5bdbc6a81fdc12e1422df3c7839a4e2b5e76d4db85e766bfb44468db85f9a1f614bcd8bcb77bdf99fb78b6fd6a667f98745a1f13c33f60da655bc57c6995c0541b8699517f0a978398242ae65665660d5eda655b8720f08611ec20330f152be2c2f700a782ac5fdeb60ab985c1fea240021d8567b7b4b07f16f89ba2045ed75e8954f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part710 : Excludes 0xa0201000000000000000000000000 0x75fde6c3e0e0701008000000000000 :=
  finishCode 45 0x7c36239306df6ef82131d2ef152f6f2e369744da06be9da9c4bf506cfc85a343e33f8995fb0a1a63a2b57ee98e8ad0979712158915a7698cc772120922fdcc9d6924c6c2f6a63034cc3182861ceb419518e439c30267e12ede38535a984b8c0cc0d15b12f6a6de2bc7e641b84496883b538a95ff78599385be2b625ed4f1948b53a55a92ddd61cc97df3da76c29a3d9a75f3d7fe546414c8244bc8224bec138c097860625e1ce0a160da6da25d8270a625f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part712 : Excludes 0x80a01000000000000000000000000 0x77f4bc93b562605008000000000000 :=
  finishCode 25 0x34174a63f11567886f32b34e84e8c0da9d66b61384b84eda9ca22089a67f5a9b4598ed69731b6a6d1752ada5da9cadde261e9955cfb536ef439137826e794c8adad4c25c60625eb536cf263742f08c65cf163969b5368b908de9ccfdee677568bb53987 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part713 : Excludes 0x80201000000000000000000000000 0x77fca4838060601008000000000000 :=
  finishCode 171 0x190bc52299745338a9973c9c5105156d2e8ab529802b146e49682bc9e5a9c7330f6f52ab77b70ca01f65cf16f23188f573e606c27a90c1fda2df15030d9a2d13661e63730b9f2f8d20bc2c9b6f6eb9ef0b21cc33311532a3367af8d42d46d07d0fa7368b44d2026dbdbae7a5cc3cb4b600325cae7d48384289ba08621ce83c4c798a73a1c5bc690e7856cf898d793c8661098e9956e18818a9aa523cc2ed3af6ef9348f377ccab70d83f4dad3b32a89b4db34ea06bd2ccacf2b1203ebb0a5b7d13585c7ee2ddd0b68dc1f89b44d44db07e26e6366bf781a641340a3b509e22ad6288bdb4bb450e86cb3b67cc0c33d11f85315f618cc6938d48731a4e34caa16d11c8be2a48952fda5df0c69cc1569933b9a17e9cd7b66bf92455da9c8468974b33e8b5fccad6278e85fba2af41009221cda4d302dc36a710f454da4da9cdc310a89b10b367d023932b345bd2d2ed0e74aa6176a6d1769f345d39c3e32b6f172d689b58d04a2084e348a23e7a82c09abe386352da82af8ca0b8c5cfad2d0ded4d7060f5a5af8da5cd4285b8c883f1c886f3c962e7c2d36a646eec885a5f6d2e09b5cf88ded4e91e985a99e7d49747b48b2ee287536ae7afdccad6970e2bf730f6a7047c4bbc81abf730f405fb68b88f6544276d2e2a62be916a0454d68246715f32b697613cf288d487186057fd4165110b3e7b0bcc6d8636a710a30384f276d39be7c4cda9bdcc462d1782ea0b6a6d4826114166062eda5d8afa7397132a85b34ebd4831cd3b0e315f5323885a86f5894378a7cc4e29f351ecc3c0eeb7a9f32ef4f250e844d897ad4e266216b53b53a2aed0660661eb53 (by decide +kernel)

private theorem part711 : Excludes 0x80201000000000000000000000000 0x77f4a4838060601008000000000000 :=
  splitAt 1 107 0x77f4a4838060601008000000000000 part713 part712 (by decide +kernel)

private theorem part709 : Excludes 0x80201000000000000000000000000 0x75f4a4838060601008000000000000 :=
  splitAt 1 113 0x75f4a4838060601008000000000000 part711 part710 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part715 : Excludes 0x80200004000000000000000000000 0x77f525a100c0080a04010000200000 :=
  finishCode 165 0xc6672c978a864113515dbce3531a3987a64e991c44bd11981e6554154d5b0e8add0d6f380451f265f96cd6f3a6382cd7e468e7b76cd885c10de81208819856cf62b6654d4e28bc8995f9a2066565c6d0f5f9d11b4fa26de6f44688c086f860578e60664e59ed115eb6157859805ead88303379b61e88c38c4cb79d32ba232c350aa4822910f457e88b79927b5eb62d3e6074ef181d117cb8af9eff44460541679bd116bd1816c688bcdd2e38430c0da22d7b6c437b430068c93e3e57d179b2398585f2ccc650d47379be7bd5c003d62636b3995a1943d70c63e57cb6a18af5dd79b1a3b25e1b190425a641330a3b10b594e888d1da8d15ba2310b863527c56a9a8d1d97d2e3a22346e8a2455cd343e995b4fa6d17dd11899087d11a2669b6c29a47a518999956a1d05443ce1ed871149b2fc31b43cbe452744707e3e1083c85226965300acb4e87c40e888d1b79a99e6200347a23442b61a939f5d8532d3a1fa23a23442c42c3471c960bec10a0ef18ec55c56da22d7ade72ca03e5ccac10710a6a766b455bd5e17b5ec42be6cdc785310b2e312f90b44b0cf138634e2f52f963461eb0aee859a9bd5be6d02013424fb435f2db8e655bcd66e99515b239d1187dd6f743e656956906b3d3e7a51c2f24fc85e3383471c42daa29acc6da22da64c604f432ca6681ba2249717ba93af19a9d4281843531759bcc90e2be6362434efb652268f569df1eda06b5eae1a867a942da56e787a732d56bda9cdf3e42d6bd745010b66932a5df25a8419ef8bab79d25c6231c8c5e01dc916d0da69c318014b348e5af6cf66bd4f93113e7063b05c43e58571c7ff4356f639348a402815c6ed6f34efb44661d32ed11d11a544b865f6d2d3e53bed1140da639ac5036b8e04efd1198d6a181ee9b45266a13e19714ef87963bd139a63 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part718 : Excludes 0x80240080000000000000000000000 0x77f4ad835569291404801000000000 :=
  finishCode 15 0x552e11c439981ed4d855e88ab379a2ad10a644cc56b79da1e12e2cf454a2bcde76a7a0883457a2acd4f43e423b53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part720 : Excludes 0x80200180000000000000000000000 0x75dceda570e02b501400f000000000 :=
  finishCode 45 0xbc461b15c7e367c81bbf44651b5fb795d0688cd7b0e33dbd487a2267ebff6a72874710cff68a07438be0da9c4ca2ba99d6a7a1f263be4b0bda9e18be0da9ca668af49f60bbe5a99b57c38a77da9ca17fe617b53a40d8844b13bde9e6e3b4b7d16e3b43de5425eb5386db4b617795b53985f42e6d15ff7e6d2892c6c4a1ee508e98ba599af6d4d08e98b617437a636437b539ee53bc8cea73887c174ef961b53 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part721 : Excludes 0x80200080000000000000000000000 0x75d4e5915060091004001000000000 :=
  finishCode 139 0x190d05a240346d8b2277eb2518c2717252dd8632bea0ac0f863688cafae4ca0b82f86331784330acf735a9eb10dec312715f160d6b3b445bcd0b6e910d621bd22d4963f2a0b84f6a6bfec2b610d6a6bff697138cc3da9aeee88eb389408e138e314a696e505615b532319035a2ed11c275fb45542dba5a9cbfe85b7895f94a7446c1b5ebba480f0e5ed6cf8976b36176e379db08709d7fe25eb536ef86fa20d8550b719548e39290bbad86076f193bed4df2cc6e8af17fb53b359f4d83759b49e2ffcc1afc6155f1c21b42d3be62ed4eb53a21dee45fdb463eb17fb3d615b442241ac6c3f34453bd83617f7b917fb0c583709e30c1b6a7688cb5a99d2eda1b0dabf6f7f84e49f5a9bd6e88b45a77eb2b8bfe23b52ee13cc3e13d4875a9cc3d2ed929110d6300affc12ea66d1718ecb8f4b76a6a670e3614b06da9caf824d6a7697313ac9e211d4babf72eb300da9cd16c0320d64a220c2f157277c378a7a9aceef8435a798dc41afdda9d2e3a226376468113d10ede34876a715b4ba20f5a9c38da7e10affe87c9d769e20e846bff649e28ea9998eda232d6c2f487688b0bca1f4ce26828085a86f2898b93bdbcc9c5af66f3d11d11ad2e61d3e65ddd18c4235dd85dc23ecd5856cd616bc64b8d6a6c2addf48251186e39bb45dd809df3d7bcab71cc5cf4e12ada35a9a779fdb7192fcd9b203139bcd8053bed4dee697ea4bb53971601 (by decide +kernel)

private theorem part719 : Excludes 0x80200080000000000000000000000 0x75d4e5815060091004001000000000 :=
  splitAt 1 92 0x75d4e5815060091004001000000000 part721 part720 (by decide +kernel)

private theorem part717 : Excludes 0x80200080000000000000000000000 0x75d4a5815060091004001000000000 :=
  splitAt 1 102 0x75d4a5815060091004001000000000 part719 part718 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part722 : Excludes 0x80200000000000000000000000000 0x75d425894040000000000000000000 :=
  finishCode 153 0x3308b770d05e2d1c41a3a6672a085a882c098793bdb4698d6cf0a795f80253e70a5abdb76c82ef347938853d00cfde932b47b536917b79da9c7ce45f2e6633686d20cc49f3ba25867f5cce617d23d20d2e6c1f30f520e14d4dba1732b6a6d7b5a0c37d42d4d13695b1779877b784070bda3e9573814f35f853d31a2ee67f24e26730a6b53b3b6af7ab7cf44144ba0614da0e9b731ad1ed664e2d1f299e42915c7ab7bd66370b47c0b76a783eeef1f3da9b47b47c45e2a3853359b70af6b47d6a67ce7f6d1f138d02c9202719840136ea4195d16b6c334bda44cd32a85b6a74da6a78c419ad4cc1e3eb6a14194db419ad4d0de656d4e419437da4c6d32a6a686e81f4cad23c57da9ed32104ce3d5be7c41cbca81aa0b6a686f48302de0fa82da9bf18085aa84a277bc4c7ce81a0670df538bc4d8320676a71572bf188cb9d9ac37cc02e8604c6a16830d6a69df69f5a990ec81a86f31abcb5a9de32164c65202c500eb3b9957775ed5355e5423a9754765d651d5338c131d4a267ea1ed5f009899776576906b5317f9876a687c23b85277ebba65f6a6c1e84718c29a5770be654cbdbbe61eb53c19a46d320ac7ab7cf5edad3e65508f0bf43e60fb4f99595ba65691ccc508d066b53b53908ef15c7e521bbf21b450f881b42e5d5b3d1369066cf257b5388f9758916d4d1061c6789a9cd4cccfed4d136c9b451bad4f0be5766266551354a6975533419b538799106d4f42c835abe655f9b498d90dd508336a6a0b617cc5841d38e83cd434832c35a9c4338f4b538cc5b0e21513575e2b5797409f3138a1ba2aa9ad6a740801a9938c2d74db0bb938c55d00b533ebb42e19dbb5bcd1566dd529 (by decide +kernel)

private theorem part716 : Excludes 0x80200000000000000000000000000 0x75d425814040000000000000000000 :=
  splitAt 1 91 0x75d425814040000000000000000000 part722 part717 (by decide +kernel)

private theorem part714 : Excludes 0x80200000000000000000000000000 0x75d425810040000000000000000000 :=
  splitAt 1 86 0x75d425810040000000000000000000 part716 part715 (by decide +kernel)

private theorem part708 : Excludes 0x80200000000000000000000000000 0x75d424810040000000000000000000 :=
  splitAt 1 96 0x75d424810040000000000000000000 part714 part709 (by decide +kernel)

private theorem part706 : Excludes 0x80200000000000000000000000000 0x75d404810040000000000000000000 :=
  splitAt 1 101 0x75d404810040000000000000000000 part708 part707 (by decide +kernel)

private theorem part704 : Excludes 0x80200000000000000000000000000 0x75d004810040000000000000000000 :=
  splitAt 1 106 0x75d004810040000000000000000000 part706 part705 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part726 : Excludes 0x80061000000000000000000000000 0x77b698ce85207ca308000000000000 :=
  finishCode 51 0x184a668310c49c2fbcb1689b74accc7a25a7ac1112dd8d6b1c2478cc6d1e06fb49acc626e92e3c9b31b47b4b813ed1c45e21e63d12f06e6b5b5389b4f580309cf2cc45a6c314f543989ba2a515e924b2a91c5e03c8b4c3cd30b0db15f6a784b5a1a7ab7ac4db21bd63ff89bb31a63e23d8af6f5ad0ed2c98e26ecb697923d4f589b8af9e5a9c2f24c6662f05e454d49f2f315e0fb44d923c9eb30f10284754b41c4131a7ac9ef12f1370b7d65689b137504f7915d10d3d644bb47 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part727 : Excludes 0x80060000000000000000000000000 0x77b291c285003c0000000000000000 :=
  finishCode 149 0x9c33340faf4ca84c110d155f985b594c32c5aa7ab09be30b6d11c176115e5b0b6d11c17b4b8b5b03d112db0e8d115d77a5ad4658e20c91ed1188d6881a4fd0d4f5615d11d4610cd6b68fa22c02f6f198d42c1693131a269add5110f09e3e3d11b4b601d11a39683536bd7e88b0a855cc03a2370aa5805e660f0ab98307cc6cf5e96f688e0dbc99238bcbf298e8d118cc508e616d0f247d113315018bd85ba222f7a1edcb2e262f616b72e87cc269a1f616816e10af2e88843b72d85b85b60bc40cf1f4d3d45e67b788598b9edee1a0906a0d6de1656fa7433b00d1db7ada4d836beac02c2782ec2743cc5a845d83115442d4571e3803f09e19df2580e0414f7d0b983c295bd5f26b49b2bb046250847610c41b078418bdb430b64236db423a1b6d0f6bb6db423c21b06e585855b95bd6cade76443455c468319509e5d1886b68ae886f5f348d31af9b729e7c9eb6576a72eebe69ef527da9a1cdc2996cba4c02af4467c95f36135d7a26f0b53d7446d2e35bc176cba93debed4cd6e89b9a974466157ded2d765f14c96611c89c502f3a7ad36d29b68f137103454da5cbce6638322f3a23a232dd855da8c2e3662662fa6d27611d9bda8e0ce88da9da22d2310f682f6efa73c0ab93d7446cad7ced1d7ceb530abd11a82ecd81f26d110a76f535b6f59f4f4367c1175d114adb8580fd69877c12630ab9a4105d5f4ed117936b5a69b4466367af6db5f3b5393d70970a840260d035b6f54dfa62db2c2965cb42f8c052da23153833217da5e88c14abc305c19b44572693e2becb6c252ddd11073b097445a45a950bc1b41b6 (by decide +kernel)

private theorem part725 : Excludes 0x80060000000000000000000000000 0x77b290c285003c0000000000000000 :=
  splitAt 1 96 0x77b290c285003c0000000000000000 part727 part726 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part729 : Excludes 0x80042000000000000000000000000 0x77bf20960481210840000000000000 :=
  finishCode 57 0x2f18cce622c150c821cd33008af12f294da9e889b1a2d998d4d27ff302a4f8045b946cd8dede155a7351b23da605f5d15f2130c029ad13446c2fa5b51b5f945b7d7a606b51b47a5ba7351b9c294ca6d2f289729b4bcbd4b48d683a0f0e368ebf29f203727acb3da3938a2da1ce17ca2285e3ff688896bebb76d26a2da12e42c0f7b3ebb5ea169b1a9aa93db1a6e8b5063d0d6ad7a97cf45ba6589c620de7216836b312ced1188f7d76a3e4d0cf1462cb4b0d32a2dc33e01f3e6a3b537d745ba64a2204e36a7282c55a7ad6a6947978bb5a76606d4e50509b783a2d4da6e691b4b1318abb47a90e5ad3d696b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part731 : Excludes 0x80040200000000000000000000000 0x77f332825400a11008040000000000 :=
  finishCode 39 0x602b9a87d7b65c116df16a66d6a6b2decc5cb8a93ca6b84b3e0afaa12da9eb0daf4465c92715c989c67bb61336bb53b04f116cdae216b43603899b49b05e425c45b261786139e36dcbd24c6872deb2f4da591bd6a6bd3ac5f7b4bc3194a49c50e6d6571b2e7c1b318955d92718afd4138da9c9d712f4a2bb3438da7b6dd66209a873ac167a916d4dbd546d4a5f3e42f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part732 : Excludes 0x80040000000000000000000000000 0x77b222a20400200000000000000000 :=
  finishCode 151 0x5528934ce1b29aae32d980a822db76da234774d6886c0f688d32d1e4432711958e441ebd73c89669db2f967d07800d136a13c981910c1be5e9b4b4f5ad0ec169722691ea7abeba2ae0110cf3e7d7d11b3189c44f477484d7667797c17d7271249a8edf5d76d16f415836d6622dd81f5e008aa95f447da7b41e13d29cf3b82f221d9acf928ab60a66728ee865d117d742d45778401f5ecaed0da63b47d118856c3871acbf43f4470be885c2fa21744743eb29425d11b2f443c622ddc2d4d83e6db7d79f4e7753ff7d76d5b4f6ebc0682a1909e1bdce1135f5e8adb539156c2f1959595356e3a65e2799cb622b938c14ec26beb4cf138c338bbbe0be4cd281847366c55bebb76a7c938af4da1684b2b2c26faf4db683879e18e85da2b61beba2ac4e2dc6faf212cfaefaf4e3195c60fb06503df05856d4c655f5e60f5f5a9a9aa8d9f8cbaef2785ec2b6a6a52f832e4b5dd34d95a599ffbeba93a9a853c7fea4ea6b6a778d0541766613b5344dc80cad2ed0e384715ea36e889781be2b5ede263a2ad4a6d4d08e195b53c0683506f74c45b924c209a1b3e7e87bddae5b7aa12c886db6beb04425b2b9f3f42deef43601f10da4dc31d0b7a94438679f5ecad79510e2062277854436e50194257d7ae36dcfaef772f3bc2890445bc21a2aed3d79743d08ed4f445bae2b6b35a3ba6bb3d883825a9c81efaea0aa5312f436c39a11da9beba9aa2dda0c4542794c44342d984c40e96b68b8836e5b0611c0ae62ea362df69686f10300ae11cc6a6db6d938a1bc4e34cb0598ca52a671c86288c40c11368f12b847009c39bcca7ad6930cf6572d6f32f08af88f6d06cbdaedbd5b96d0f9513e5b4942fbc532d4e993a51423529535987ad041fd46c536 (by decide +kernel)

private theorem part730 : Excludes 0x80040000000000000000000000000 0x77b222820400200000000000000000 :=
  splitAt 1 93 0x77b222820400200000000000000000 part732 part731 (by decide +kernel)

private theorem part728 : Excludes 0x80040000000000000000000000000 0x77b220820400200000000000000000 :=
  splitAt 1 97 0x77b220820400200000000000000000 part730 part729 (by decide +kernel)

private theorem part724 : Excludes 0x80040000000000000000000000000 0x77b200820400200000000000000000 :=
  splitAt 1 101 0x77b200820400200000000000000000 part728 part725 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part735 : Excludes 0x80028000000000000000000000000 0x759ed2508910055000000000000000 :=
  finishCode 131 0x1808a4e370fafa0e20d1af23132abff377b78cafcda3506d58d6d3de2d53de89b5f1a827dc13e687137682af8ca1bc678142395f33f48610c9ef4cefa6d9732b5440db41699debc98df4e2a61436f1013a9a5f05f2694dbd45fc62f4150b0482256995c31a697d35cb34b35bb46e178346d834ca8b0c072bff136b972ba14b8530eeae5b01e88852c93446c94cf4c3b6ab7ac47c4c6d822c32ef0cf360e88cd8330e34662b436cafccac4daea8d1d9289507e365b6ab50c6db05f4ed0da4d827df4e7a5d0dc313159eddf4e62e4df7c195dac110ac1a1e22d014f0c58d1d91a0d83433cc5d97b65b75c91b066df97798d867b445b05b0698db2457d0da20f2be136d82deb18a6d8f3707e9a4ffd3de8f62d71e55ffc1f6c11a3b446d1b89a0d1c4ac14b13785b688e829adaead34c9ee31748d1135b23fa19e9a53dcc46b446068f4466bf8af2cdb44447662ee9885df6f1b09c495e95f4e61c496b472479b2f445e765c6a1a0c45a2c0c0ac233c037b07e25427c2863ffa1ce63626e492b727bb6aafdcc3b7adf2390cf0fdaefccab60ccacbb70cebb7433da4b65f1209100679958905bd6496571ffb6ab04c50903d32ab00a1a1ce28c0d660d6c16f1c23aca44d454c1ac56e892495b985e635bd5a041f3e9ccac54a06c57d84f32ac2f32b282c11373c895898de76b31a63d055f1895acc5afdb3e311b415e340db31263895 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part738 : Excludes 0xa0009000000000000000000000000 0x75ffe03328b4501248000000000000 :=
  finishCode 79 0x512f990ac43290bfec1b7825f898e5f62396137cf175897e0920a830492fd2a2c26f5743999692fcf0ec0b5ca8620275b467a933fc276136bf9bc600d43598c39a56e828a7bd4844c7f719fcbeda128b8981898e2a664e298896b932584584e1ce23dc2796b17586595cc0afa7152c0b5a49ff914c0098dac6a69b4b14f7bd08da99deac98eac5e179e2455c7a4b32d0956cf6f1a041019e5e797da6d5c709525f239b09e92c2245ad7666a16138a196cbce81b2ede21f881b3ccbce931aedb02c3290e826369f8cfdf4d8467b7aca6cae2be545e2e1ce787951a4492804c647b253cbebd5c3984fcbec47b68f255cbea0687b91d8138ad82f8a7d2d73276c7c45180c264bf611b67af3da3cd42d3af53a0b78605207933498dde5f0529eb2bc25023b4f7a9b41584ecd68af7af25f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part739 : Excludes 0x80009000000000000000000000000 0x77bee0320830401248000000000000 :=
  finishCode 115 0x184a255248a6737a9a69aee42f86cb32b539c54af8a88a99d21b2df013f68f3cea06a81c612f32f0f2e8bcec54df2384e2f83378ccad84a81a0c358291787429ad4140e08ec6f5873a2bdb2e605b2ec1f30f7990579b6d8161ce089057a8614c78ad96f32deb0e735abe6bccd4208deb614cb8c5008e995c315d923dd05ad3f4169516a15e72715e3c29ab14cf35fd34a82938c3dd4d225f84adb6116dab6cd0451d0c26a6710fe82a16ccab02f84274069da96e2553e49c5ef6001d0dc29a5bd0569d4f98afb08da8640d1dd0018735354f9d05bc302c914cda8f4b27c938c5abe0c5d23cb11e99a4e3216d69f31b4879da655e654cd06698da4351d995a4642976c2125998d40d6bb535a0253c43f84e64e81a9f24e316b4c6a06c4acd7778c852178a67588e13882bd32afa70cb4c9b4ed98ca8ae34165de65743612d2cf5cd7d30577d3a196993b319677af271ac47177ed266e16ef5112719735f931b432a88ae6a16bc5d31b686c8622e6d4ce4e2fa60c7b842d98d825e28dbc6636327dc34ec85ad9ede32ef034be9d81d8fc50505b0619a8417e9957e4510b52b601f69dc2379723d821ffd48af9f4e784f412636b455fb1fba656caec25c2d4a9057153c2705f995 (by decide +kernel)

private theorem part737 : Excludes 0x80009000000000000000000000000 0x75bee0320830401248000000000000 :=
  splitAt 1 113 0x75bee0320830401248000000000000 part739 part738 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part741 : Excludes 0x80008080000000000000000000000 0x759ee5901810081010101000000000 :=
  finishCode 125 0xe26836990b0610d8d986e6d83618a9abc58d1cb8bebaecc9f63463473d7cf166ead963475c66491f5d4104604c6c8210de34b8be0a16e88a7dee25c5ac66f13e1a945edcf866f19716f1885c8a65c6cad5178603813eec8d8681b3c5c51899be0a06cef31462672bb206bbcbe0cf223e1e72cf40d8a36b1d0590b5e749c6d3ed0598b1ed42d40d4fbb3d90b5f047868a37c94fb35d7c19b45afe493442d6a35fd67af930cad7b189e611bc6cd608d23340d4fb88cde2e7c16bf78b9f05e2e88f6f18c19fc9f6de2f83471a92d7357900d35b619aea7dbdbbe4d637186351dc47878e88e0fbe08bbb57938c205de23d3eed11c21b0a63e102d88fa6986789c623e70347444fb5036de18da0a44368b69f618d9ac7ff65b69f454b5de4221644238cfdaedb2ec12017f97b585d066b3550f5ff6ef9aad9964a257278faf20b02efa99d0bfa0ac2f31b688cf83293e88cc6c81b56d11a535df6d5b444cfe5277797c151db35c29a5c62bdbc617df5ec9843535b6fbe0be99ffd31349e67f5c9e501bbe5c698d7d71777d79f5e7c17c18cfdf4f2178ae0d1cc6c083852687a22faf2002b985ddd6a4b6cdd115ff660b2d863a2281aeeb2b767afaf18904d0d0e26e5d960d8af617a58741617ed3e17e2333ffb4f8d0d755f067c97d7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part743 : Excludes 0x80008004000000000000000000000 0x759f61380892001204800400200000 :=
  finishCode 143 0x452b938e23ebd032132b84b26d13ee6f536d37b9a6214165e78af6136db822dbd62becb60716a107b5f56f55278af868d49e5351a3da301cde685b1c08d92a5ebe5448fdf4c8fec2553203471bae7180ec256bd42d6039e1e01d0f56ab1051a35cb37388f879e996585af50b468e6988a8526d846ddb47665a346bcec23905e76dda1ce2bf08ea676dda8595cb9715f4cb40d05972c225b8e2be5f67ab5cb5e3a6597d6c184b26d068e24b34326337bc44c0d862f922ea4ae3471534ca931c6e66a74c6b6eccad33d348d18d1dc4c84cab09c6e6347506ddb09584d7d4c96c256dd7cfb44498deac68f2184e259289608a99b6cdee086eadab454b7aa7dcd430bf0d19bda06cf563466e768bc40068e2bed056d33438646344685fd058af5e3903617ed0590454cd43a0a9f6686e04cda955f3deee95bc29823578d76db4df3deaec09f6346d43688cbb9a58a7c233689a461c1006056a2c1b916b847358c32cb9b2ef2ef2e6cd6311e44384ab9b302b90ce2206b4ac3cf2a384b2d6d4211a6baf6f350cc6d4d30f38466bb0cb688bd2e11846c6ba81ac06a712c0d2b686e12a7cb69a16ab1ac708e3c998dd11b08de96a3db2bc233fbc239a869716b1e26d2b885b0098d58361d31d147a1f51ecb8e88b58d47aa8c21acae1e743f07ecbf07ed11bc5a4c47ef82c0c29a64d03ecf57253ef0a65c9311b4f6a193ee1965db3fb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part744 : Excludes 0x80008000000000000000000000000 0x759e61184810001000000000000000 :=
  finishCode 105 0x3408b7b8bc57068e29187d742da654cfef99c271961829daf50b429e42daf8d89e472c8d82dde85b138a11da0f2e29f62ef4b099fb67c47853cef3614e82e8387ab02b68cae853c9181642d2cb9de65d4cfe29317309afaccab8201843169e87c46e14b61c42689b678f536a7cb02e14c42e2eec0b27da66c4e33866501f5f69c43e1936e6349c50b4d8dc09b7536b02cadc2d69b742fa7dc6f685bb4e24afc1f2bce4e29f66f6e095f8016576cd579d36df3da166b4ba90d983cae91cc2fcbcf66b260a0ca6d938e1229b45f5603a41bd9ffd66a622f538634aeccac7ff65bc485f8dede1e3ffb4f85f8af7ab8d8ea1b4c25e0dce81106a216cc4cbea2ef31711f12c8bbe83c9827c32babeaf8214ef4b2b7206beb853c46cc6cc0b31285ac06f4b683ccaa169b1bebc7eaa0a696a4f32b20ccc4bebd232100799a5d53ad43e8164be614cbda2fe7fea6a2ff3d7bcc931cf56f57570cfdbc695b0a77d77c1a93e62c0dc5de6562938995aa3ebbd2cdc2f5f2eadc3211cadcf4ad82f5f317546bb96fdf4e62c29ed3e78787351d (by decide +kernel)

private theorem part742 : Excludes 0x80008000000000000000000000000 0x759e61180810001000000000000000 :=
  splitAt 1 86 0x759e61180810001000000000000000 part744 part743 (by decide +kernel)

private theorem part740 : Excludes 0x80008000000000000000000000000 0x759e61100810001000000000000000 :=
  splitAt 1 91 0x759e61100810001000000000000000 part742 part741 (by decide +kernel)

private theorem part736 : Excludes 0x80008000000000000000000000000 0x759e60100810001000000000000000 :=
  splitAt 1 96 0x759e60100810001000000000000000 part740 part737 (by decide +kernel)

private theorem part734 : Excludes 0x80008000000000000000000000000 0x759e40100810001000000000000000 :=
  splitAt 1 101 0x759e40100810001000000000000000 part736 part735 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part747 : Excludes 0xa0005000000000000000000000000 0x74ffda4aaaa55002a8000000000000 :=
  finishCode 23 0x5d2597cac0c8c71826089b535016f1b0304d4832f2c1afa35a0c4ab58cfa2662a0368c29a54664c27deb5f4628f45013ef9e66cb4c5663ed16b2994d799ad3c9765be63ed15b860a196360d191985a4c2cf6a64bafcb2f88d5b062beb537cf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part749 : Excludes 0xb0001000000000000000000000000 0x74fffc0229a0580008000000000000 :=
  finishCode 91 0x174c25f2b944b00c8c8258bf6c1b133367a80c4dd15369612f280c4b996affa51b3d4069c6b3189b89532da92db8626de158823ccd10e4be443439d96c41b67c57bd5d15f157596b6fc40b7092fd62e0e88e52097ec067e4bb306916d4d211ed5f019a6dbc1e11c56c2342ea3da4b6af15f33fc2da92d04709c8b57fc97e60da90e825d8a046c65b12f15ab8a3d5b9ad3c8a693c8a679ba4b08d885b07ccb62168ad74451d867f04bc4bc56da2896573e8c5784fc40cba210710667ef334a6cb7bbba80c41d62012825db4f9e6458ccfe56609f595595b0a43d5e65eaed3d36ccfecaea3d79b77725d98490bb688108332d25da23702650465af799b43c2785bd04707e23b16f799c23789a90621ec0e8942fd91fd10611ec1b12f456e8584b84c850cf72c2ef4f5f271786c3a1f867f146f125f82262b68f6c1b25f6df897403c7bc22497ecc62b5bbe08925f6f181dc97497e96609125f89589757541dc97e9b6a4716925d33f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part750 : Excludes 0xa0001000000000000000000000000 0x75ffcc0220a0500008000000000000 :=
  finishCode 161 0x32990ba061d81d0f05fbbc43238c1b5c9c198d4b212ef5edc2ddebc96b8baed4df25b0699c28697d7af7a7a5f5ebed4e535f25b3e94d86f7834df94d8286d4ccfdee660db53a05e22b623f7d37e613d84a7f6d42f72473596e16842c41cd42dc2f08639185ea0c06efa54742da76d4e5adf4538d835a1cb3d2cf5a9da1d41896a7442ae6d02caeb53b2d6c1ad26554b8e94d98f00bb47b53b43923e2d4ed06c296cf5019dce2167ad6af1675cda21585dc92cae3d3d2cd2fad42f4aa032fb3c1ac1e0e5ae69d5df7a596b9bc709ec1b793783795bc4e118dbe1133c9cbeb57c4be67f70723dbd326fa712fcaada9aead6a728825a9da0a10330ef764bef03dbb09e555ea6d4c15ec257a9701988a1cd42b9b2ef350df3096ca2560645b12c6cfa82d2966b49a5fb536e17b97cba47ad2c785b86d4d7a69660f787b6d4db86d0e59e48dc36930b7e14c37da9e87d3262df4e35a1af4a80cbecc9c72f14c6f114f87de1be9a5ac572f08ccc488e86fc27793a477b75cbb08ed4ccc628e8163ad4e2ac5be613b53c233fbb08ed4ef09896367c81405ee6411091c17904743c97e59e5b969d411b53897b2b8b6743e26497de9d045406d3ea71b535018e4b1b85bc52bea710879670a18977a70a1a59e606b4b6cf7cbb537958a3ced68ec2712f15b68f4aac37da9bcecc099fbe9af4e12a0fc545617a661746054e687d0debf6f9267f6834bef7ed8b53a25ed2dee5abdf454064db6e116f263a9c706ccfdb0ddf538c4acf7f106de2136447682da0be8bcdb02afbd309256098df0f4b60fbc48b3b08da999f8b7d2e326fc4bc39bc4c37c67ec22e8c31a2b620e5bccfc91e959617b2d8878e3f2b14e3531da3b70b78c42d69699b4e266330b131931d68f4834c71c33f9bbde5633f (by decide +kernel)

private theorem part748 : Excludes 0xa0001000000000000000000000000 0x74ffcc0220a0500008000000000000 :=
  splitAt 1 112 0x74ffcc0220a0500008000000000000 part750 part749 (by decide +kernel)

private theorem part746 : Excludes 0xa0001000000000000000000000000 0x74ffc80220a0500008000000000000 :=
  splitAt 1 98 0x74ffc80220a0500008000000000000 part748 part747 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part752 : Excludes 0x80101000000000000000000000000 0x77b2da234028480808000000000000 :=
  finishCode 181 0xd66528954925f0d56d95c780cad41a13cb536dbc2da5c57fe636c2db4f9f256757fdbd6d4c98e5fb5f19e3dcd30f4b348681ac2e4c778743e4ca3608752e884d2cb5fcc3adfd4b6d6ac46db908de7546df075168f357caaafd99fa99b6dcf9304b53987856d85d7c5bd5b6e5f151b7c1a83c5cdb62def82dcb67752c931d32f93cb648065620c1b32abf731f365912d31e9774c9b57b65be4c4ba8ec81d0c1b0e359acc7afdc57cf9729a12ebff2f8cfa632aa6768b84f17012f3d7bcdbd6cbecc0d71f4679396b09f8ada655ebdf468ad9405efe4046b0b1a81caccc7da3cf3b5c4e1e29169955017d1a5fa715a1b1c94b368b025c57be0a80be5c42cd96a37852d9ebfef72ddf30bbdcbe5be4c5a6c1ad974b37c51b9ede91db2dee5b3e26e69f9817d1c44a29063f3e499faffcf92f732fdcbed7c9e352f0bff4c82299caaca5312f4b5ccacb8c67ede2d9ef9f282b0baf1836996a649b000bbbe14e8598ca94e85da0ede263f8534428efb65c4bcc3a99de2d188a619fa94cf9ea6730f2f8cfa32df4c3d696f9f3c5c362d15f156deb303326fc743dfc37d2d6dcb15b15f539adfa80cb5b72bcd99fd15af36f5af534b7be8d02d948995ae5e1035f0633f2399ef6966d4ed3c7a61f553333f959a2be9ced4ef14898fad4ccfd08eb53b35af978b318cfc656d4d4a546e9966b3e7a06cf0b66b1336a6d3f437bded20e10c56da9d11d13cbe043d68e67e4c6c1b32abf69c5e456c54d31f32af5f19fc4772f332b136fa2f8319fa80ccab91f93c5011559f4585de0fa34bc83ec4dc54be8cf6ed3fa1f6977c945a5c48f102c2f8634b1a06a5bd2f2f5b6a71374c61704da56481656e21c28663f09eb41d0f8879959e06aa54a45a9cf1f2e69f9672512638019fae7cf4e9d6b7f616d69fa0adb6846deb7c6db95985bdafdee661c61508ed055cf97d6f5ae4006166367a933fa6349464eb (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part754 : Excludes 0x90001000000000000000000000000 0x76b3c8020920480008000000000000 :=
  finishCode 143 0x5e31174b04e2508968ab90dc2f8a6dc4e246b15f4d327092c938d2dede2b9f610b6f8cad43288af441950a1a63df35b165366bb2530a19b165e57c689598f195944f35958aa138db1d04b232a5d3613c32e12a21d95d28806d84ed4b0f7a0e8876567eb129c33993a21b62da3c8864b3143457a21a21c68b138e1358fc1955a1fcd83679af4f84edded7ea02d97454c4db5f87ec04347ad9ed96b9e68b2e7d662f4f3ca86510e7592427125d9f35b2e09b33f097a1bdbd4974cc697925d33fbe57178ecb83709c693ea698ad24796f6c198fa4fa9a62b491e710e312eb6fc4ac46ad82d8319fcac938aeac4e30e30f18f7aeaa70cca938cc1e5e98f25da55a2b6f92b319fcbc938c90cfc1fea636bba5e6293c764b10be497c820bca70cdab0f34caaf1846da7da1732b0f2dca68b685ffb459f4427de6e5be027b47501b4f7776a5a9a46557fee92c92372c2da2f3a0b4cabcc80d87b8b7c4dbbbe0f8caa80c4dd2c6c1a32b48979a2562bc9766566d58a96c1822f24932b107719a7de55bd5eee8795f1973e2a6490f3450d9ad29afa2be30cb450af8ccac11e110ae37ada1f4609d0a18afb4f88eeca4254654186c25b2923b24192572e93c3ffa26e1e46146568790a13ffb09db54c3e2bdf3df366d5ae3e8cddf15e7b31879ff8c2c32adcaf9f3ca69983428497423441e3d997930f879ba4b309542719e6c25d0dd4046562150995437a599b6e61e9665e3b086cacfe54049c585e7b95014e186550dc9c6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part756 : Excludes 0x80005000000000000000000000000 0x77f3da4a02244002a8000000000000 :=
  finishCode 73 0x32924d65f031ea930365a85c1f3e6e56f59e594d32b4e6de285f653291894e7182da4c4a348aee7521cc9bddcc9d6a69db50983e7cdaaf5adead8b3ddb5acf772df0f89b2da9cc9b72bb0d960885edb75a9be7d2dd1ed69f3033269d767b4a6931be7863d14ba4b2a0a02d89e4029885eb08739b6e5e62d45e6a47b0a6256d2df461cea47179a47a9b5b6e1e628df4709eb316d5b536f599589597c6790c96f978e26d7fe7085e1434b1b78c39d85205f0f2db7536da9d98cc2b5fcb1c4acdc332b509244160deb0f33e5b6dd31c3cd65b136de33cb45ad4c98e1e68b5979b53b44b1787fee86b16cb8af3c59dc5bc70a47f70a61f11dfb07c7f53ddf4419e87324189b3c584bd75663dac62565d5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part758 : Excludes 0x80021000000000000000000000000 0x77b7cc4a8120442108000000000000 :=
  finishCode 131 0x114742f2a132b28439910ef9b87e36dd12b682c276a6d82dc30095bad4c26d15ed06c1107454afda2bcc6d68f15eeef0b8da1d15331e8af60c85f1f8bab31f5a5c4abe9b70e82c24385a47f68347b441d20c56c54c56cd8312b3e9b6fcf2a0873221d61f1747d333f85f9e0e98ed1e21eba687c106ee34b22f289768e99b4b7bd7be9ca0368f4c33fa8598d0e6d8aee32c6c274c73c9bb8cb1be9e82cfa2dead6b509e53110ed06a591794577e3917a6d2eb4995b4dd7bf9719ee69c709ed05eb6881b4bb47263a658184658e4557e520d16b6633f1eb6d2e5e9b51c275017d16e5ad2ec190a632270dc44bb419abe1c621dbc65be615c8bc617a1c62062a578e5f1b08621f43daff0a68a988798f1799ad6d4d7c512e48f6f525931c4dc81af6f682d634f343e771089691a591796dfb479c3c1c40e87d4b34c7687e12d1507e3617a5816709c7899f4697e9c5f46a476bf6ebad4dbd661ee8e4245898d135efde2709eb49b536c144d263936e56ee9609e226c4c68af386bf9eb51569b6b517ad963866e1d113768f19fcc6d68f3e9bdbda8d0e67eb31b6033f09b9eddf4e2a498e206b493ef9c561f889735fd2caf103686d6bf89533f9ac67b78817d3c29a21e255f4db0610d6df7c9987457a8431ee515de76987b473f5929f415a6c41df4eb47 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part760 : Excludes 0x80801000000000000000000000000 0x77b3fc123022404008000000000000 :=
  finishCode 57 0x30974455ad4d134d96d8c48a2f4d3220c2328a021cbc3d2a76834db327438d1572aa13721ca66da5da7cdeb68310bc372d31da0b69f0df3264a369f3dec13769e4c74c8a5710bd84570de297b4aada0e13b6fbcb84dd2c74aa931d2fac0b0df4bea6db57caaa1c931d1260dbf5a9b6db75de2606439b41a64ed4ccfeb53bc2f1b7d1350e696e5cdb539719dc70953ad73628fc724b26065cf3dba592370577d1982e6ccac86ef9f31af9f1eac2d24a732a4075a8b4e920cc6ccac4270fc16ba915dc655414c53d0df09ed079717cfa9169cecde5f709ea5d08d239 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part761 : Excludes 0x80001000000000000000000000000 0x77bbec020020400008000000000000 :=
  finishCode 175 0x6e351240c7c2440d76f086f5844d6f18cfe9668854e562216cb6a4b6a1c2540db53c238076965a866564cdc2595ba6db5344d9156c12844bae226c42cdc310b5a9be8d30350943c1bd3938d2ce8873274bec5e2f06d6350b04a11569c69955e933f44d6c185cbd27b3a16f72fa2e87c9ad26654c2eb496f1c25b44a279584437c19abcb45ee4cfdbc659ea717c16b15cd33f9e5742e1957957d16bf94046549c6393cac3dbd84f326f0765f69267e4e2de34c967a94664de965bde96223c237b7967783a964cfe656656aa5d2a06aa6cb3cb6221b09cf5ebd2fa33d7d32a8aaf2afa3687138ccadc2f94ca8138db1c13c5f7984521be8ab09b6119236fd6924a34c72c704dd697302d7f5a9a53d98e0bc9184dede6eba439f057669816cb955af1506a21cb6db7ad6a70def930df59dd0df326f0af93a0b4beb6dda9cf2614c7c4e1845816b3d97d6cb09b0159f4d8150e69556139559096656cd65f6606439613acd5dc57a6993c5e7b43a2162b50e70c6b53a20dbc6656a1789e5810e69889b084db2710f5808e557436d4e616d4e96b85bed4e1bdb6c9c67816f1a64c21ee6db6114559dc6d4f08e771b536dba63d6cdeb662a024e2db737ada9bd4cbe24e378a8582006ca89a8aef6f539a8dbe2cb6995971b2baa98435d8d96296633e5bdbb4ea21ca8cf72fa6d7737592ca21e428960365b49a20d85ecbe511995940d3b644bc2552d86bae8195a6d97b709ea4bc3189650ded4e9960a821bbe30a698db4594166570c69765e3a8045d6a6dab32b30ea0b5a9b5ab5dd6a6deb58745817b69955fb0579e570b6d1541577e65688e409dacb741d85deb5f4585eb2bb5390de9745ae5de (by decide +kernel)

private theorem part759 : Excludes 0x80001000000000000000000000000 0x77b3ec020020400008000000000000 :=
  splitAt 1 107 0x77b3ec020020400008000000000000 part761 part760 (by decide +kernel)

private theorem part757 : Excludes 0x80001000000000000000000000000 0x77b3cc020020400008000000000000 :=
  splitAt 1 101 0x77b3cc020020400008000000000000 part759 part758 (by decide +kernel)

private theorem part755 : Excludes 0x80001000000000000000000000000 0x77b3c8020020400008000000000000 :=
  splitAt 1 98 0x77b3c8020020400008000000000000 part757 part756 (by decide +kernel)

private theorem part753 : Excludes 0x80001000000000000000000000000 0x76b3c8020020400008000000000000 :=
  splitAt 1 112 0x76b3c8020020400008000000000000 part755 part754 (by decide +kernel)

private theorem part751 : Excludes 0x80001000000000000000000000000 0x76b2c8020020400008000000000000 :=
  splitAt 1 104 0x76b2c8020020400008000000000000 part753 part752 (by decide +kernel)

private theorem part745 : Excludes 0x80000000000000000000000000000 0x749248000000000000000000000000 :=
  splitAt 2382 113 0x74b2c8020020400008000000000000 part751 part746 (by decide +kernel)

private theorem part733 : Excludes 0x80000000000000000000000000000 0x749240000000000000000000000000 :=
  splitAt 1 99 0x749240000000000000000000000000 part745 part734 (by decide +kernel)

private theorem part723 : Excludes 0x80000000000000000000000000000 0x749200000000000000000000000000 :=
  splitAt 1 102 0x749200000000000000000000000000 part733 part724 (by decide +kernel)

private theorem part703 : Excludes 0x80000000000000000000000000000 0x749000000000000000000000000000 :=
  splitAt 1 105 0x749000000000000000000000000000 part723 part704 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part765 : Excludes 0x21400000000000000000000000000 0x7cc9ca91aa00000000000000000000 :=
  finishCode 73 0x381a4b4642906a35238c885aa29a2ce02818844f7af8f3de974442aed4ed115fb98f8d474442d6d4e0636e13516b144fba5b3286a23032fa8548c8c4fcf4b4be4aa2f338ac26eda234befaedc212edde9d33ebe88a71b367c94e97c5a6c0e2f9369ef5f361e87e0b8b2e0fe14a9ccbce6a2de374b63ebc6a2c2e323589a3e9b0bb6ed0faf5e4be46707dc3eae3a74e87bd7d2aceeaf5efa6de7a22b57525919a8aa15e22d9246e1ad4d4b54e6d014360bb6f9a8859b0bd48965a9da22a1612a79f36fb66b04e88c1130ed096cdd116e1609993b05db7d7fd046906a214b210b68d6a6c2f64b40c89a8c166a5f4f2495886440c5fb85a6a2a42c2ecc5396ef9f5d7ef4449566cf8625fc6a29faf2f52abdebeb85ab77cc2ed9ef00b5a17df5e206c252df0f9b4f3074e90b5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part767 : Excludes 0x21001000000000000000000000000 0x7cccc210b088108008000000000000 :=
  finishCode 81 0x3194cb6620d86196836794bdba6484eb3d5a90a7fd4ae86a823538afb9b3a08d686f9f30a4eba4c85f2c089ef0a4306d9ed3236a687e48334ee14d2ada9da3de13a585e53ec2d7d394fb0b6d4e11d43fc45a221ec2932db477af8af3679c285841d68e7e282334ebc5bd7d96d15f30b68e86b7c9c5e02566e16f1a252fcb8e12b66b5a7c9d368e4bf2f3285da3a08d22606ce10b5a9be484aa85d6a67e32e3b68d3192fb78db2d1583794218d9d4bda76c296b75154355e9ac501b068b35df421d0f52d52fc2194849d5f4e275b4521f2643550b36f44f942ed4e6f17817d350bbe693214844f7bd8d7d14d39206b13d9b0a708741d85c8f661ec214c99bbccb70a585c8f7086b178c279b454bdbc6cd63015d925f4ff5397d3929e2448f57672047ac13368e149afb069ecca729e2de3203cb974487c9d41857a48f692ec2197b4ad35f5f7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part769 : Excludes 0x21020000000000000000000000000 0x7d8cc3568142040000000000000000 :=
  finishCode 57 0x348f08a621f5e516035f16f89545fc956b53b538dbc95642bdc5f3206f36a7227a2ce88c8576a66c34c36764688b7bb49c5aa0cf4da7e3482dae4eb520a5fd6098054da9c7e213e30f65f536da9d23d389a4d4e33236a76cac1bcd302a5bde7d3349a71a1de609d3a22097459b6bcadb5bda1262b16790a4016da1ed62f02892d4e68e8b32c6c227cb8da2368fa234ade108f0c96331b68ba229d36889b7e23718432f8e889bca85b709afdf290157853688927b5bda9b73af8d6a664f37384fd527869337084dd234469575f1991b49173079a2bdafed11b5324f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part771 : Excludes 0x21000080000000000000000000000 0x7dc4e3108104600420001000000000 :=
  finishCode 161 0x3493878621f5ef1581779b7e2cdbc4d3cd7ef95415bacf69a5e95f4d1642e697d981323a1cd0d4956f9549822c84bd1662d7167285c97ec130bfa0abc689386312ab53e82a1ab76cc10ac24e1738a5b5948c45a2f190367aa6d1166c14975959e5b53d38996e88b76b910d6a7132d435b4450d60b9937ed3e5f5f0d62822d4f1f8d9e845da229d390aa591b35bb5165c812f353996d25d67ba234e33bab53e88d69a9d369f2fa11612f196a74845be268fa7043a15a1ad6177ec1b4e97d36f102182e53a5f4f44692ed114e97af0b908d6ed90ae5968bc227b602e4216b47085a63ed3e9514e9d1193a5ab42e6206d110b9a4622113c34f8b3a1df44424db3650b9e4c1bc68b3087097c31a1f5a368f64e950b8b3a1df44425d6007f531e18a74a85cc9d2ab56da23acc84d2917cb4f9dd532620497d1642e50fdf1544355e3e9d15e65ba1280f44dd95d9ee88bce8acc20783f2fb67b68eb462356cd4f15f656f5edba65ba0b34eda9e88bbab6ebbac65b68f88d11a20532585d3a497c2e6a910289f379ae5d2b2483a2313769f2f185cc82c134b479b35b8d0ae00d67361da3c9d3215de1ebeb4736fb339a9cc0542df0c8702e5d67adc6a177c6cda2953a65ad04db536ddb0081c65abb2d8767b6a744fb60996bd1f94450196a74913d2fb862b5ba2385b68f2fb618e88d25919af190467208e0bda9a0ebb0526b534116c196b6cae0f523315141d6ed6dd8cb5346d056c387db3f41da46b1f06bf108e285e0dcda22c767b4d2fa6c1b30bcdbef92de36a6842f5f370e10b71d80d3e6030f60b84b8bbda9d4ab496eea82382ede784f29f37098ee13cf1f1a06f1b4fa2bdb7d42d8266df5ff6e19bcf0b6d116f325f50b (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part772 : Excludes 0x21000000000000000000000000000 0x7c84e3188000000000000000000000 :=
  finishCode 135 0x562708b714bc3ebdf371ac6bf1739bbcde50ad0462757cf0a534f0a9984ed4c2dc1de6b7177b5334fbe551bb66f76f3b534596f7855f4145aed4d1256b64ab7cfb53dc5e2f9ac89b8d84de5aceb5396f0a50b76bf7c1a78b9d4e348f84686ad3e2e75a9df145e87344944f36142b8c1dbded4ef9907005cbf238bef32312c9a4b6cc1e6017496dee987536991b7bd14a82ed921532fb9a4d30fc65e96d76f716b905f717cbc5a310bd330285b9bceb2cce699b3f41344fb4f89b8af36198fa9b5b4c295f4e0b9361b53acd513cd86a940926217de6e7523539d6369b4cc4eaf7686b12a9fb369c4eb2f2856a474df290a0893ab74c85669305be33717ca6620d86a86f30bf0c8a27b7bcf7748a23dea24af1c3234d33ddb69cfaef0379c299f4c2e5f5ecb60b9d1142b7d3b4622990c6e990d5bdf21248c3e6806d0e74c64eaf7ac0ad473de93ab21f5ed2695596f275d11799873b49a55658c9d7445e67096a416d35f786215cfa686af0d116d3ad25adf4152fdf5e6066b78a21590fd4bfa0a9d32b2ddade6b5b34cbddcb7b69b79cf7a86ba0b45f29990aa05cc59cfae322d5ac232f3bebcd17d4d24cb6b4dc25411a584955f5c2e678611c4aafaed46f7a53dbb7444cb505eb4907f5e9d117d39045ab5f5c2e5983226932f1e88b54bebc60d265e34176f799331bb415b5d78c95720faf7c7bd914d1649d67cf4359a4305b60815157b7c2542b2d3a58584d79dbcecb65e7 (by decide +kernel)

private theorem part770 : Excludes 0x21000000000000000000000000000 0x7c84e3108000000000000000000000 :=
  splitAt 1 91 0x7c84e3108000000000000000000000 part772 part771 (by decide +kernel)

private theorem part768 : Excludes 0x21000000000000000000000000000 0x7c84c3108000000000000000000000 :=
  splitAt 1 101 0x7c84c3108000000000000000000000 part770 part769 (by decide +kernel)

private theorem part766 : Excludes 0x21000000000000000000000000000 0x7c84c2108000000000000000000000 :=
  splitAt 1 96 0x7c84c2108000000000000000000000 part768 part767 (by decide +kernel)

private theorem part764 : Excludes 0x21000000000000000000000000000 0x7c80c2108000000000000000000000 :=
  splitAt 1 106 0x7c80c2108000000000000000000000 part766 part765 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part775 : Excludes 0x20600000000000000000000000000 0x7cb94ac143c0000000000000000000 :=
  finishCode 77 0xca57249906199441218f9f368859da9affb0bb406067ab609b43dc5318267ab609860660988553982bf701535a98c0bc2a96b70850c30369352bae3da9b688c0da2e1805fb9f4425c60c2bed94c5fba2b625c2852ee4b99916097d18838975fba20cd467bf6d15ff5ff942db3d85ee970ce4a2189ff537859affb06859c686a176c6af9af5bce64de0ed4cd0c2ce40bf744cb6eb79ca8d15ad9a3075a9b6eb79b06a77d65f15b6a6bff20a85c13becbea3d509b5353934331fad4ee128a6f9dc744542e2166af96b771d11b4db53a498c7ed36d4d6b688596750bd11b53dc571f8dcc8370b7884bcf2ac122e75c31154177183883a9069c5bbd4e620e0979efe17d85c5cd7fe6178afa17d3bd7fc60ee14df688da9a9ca85aded65f1069df6a663ebff4824f860e25eb530ab609 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part777 : Excludes 0x20220000000000000000000000000 0x7dbcc2464044440000000000000000 :=
  finishCode 71 0x6e3117c35fae681b84de61a73799afc90ea834e6ef4c59bbc9debe36a770315a2ad4870a70854bc69ed262135d14ef8ad22b9e631f06c21335998b3b77b78e42d4d7b627516f982615f6ef6f17c36170bc6bf863210874465c7241895aca744571f446a4fb53157b445086910c9899086d4e4ef0a596594c43b2e76a7688e84d0321609a2f89a1c57c842d27688cabacb8afc483a2312ad27210e88da9e88c843687137598a6fe88da9e2281a09e0c5df2d95490055e0bd67f8533166865a7613a72da9cbada9d12f852c132e8cfa36a647668715b12ef93685da6bd2923cbe249e2ff44aa5202ae62e6d75f1a1c7084ee679b24f6d7d11b535f1d098d2662cc9d04493e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part779 : Excludes 0x20201000000000000000000000000 0x7cfc6240e0c0301008000000000000 :=
  finishCode 91 0x124a0671867114c941b8e4219605ff9835f0da2f831b7a85b78848d13782eb2f4964be21b439aefe149b7acbc5f64bf49612ba16a176a66de63b02bd25e13da99b7b68d25ca16a72bbec136a61433d4bc19b0da9da9d4961229726aebbebf78cce622d00133c58b6c37ae8da9a90c569b39bcdf220e8855ffb535092756e1509ad4e20f0864fdb4f361b53c85f092e7cfb536098839f3c516b538ad357a464260f9f125b0493ac313f67cf5d106d50912d9744b45f3cd7e61e06d13533f35f622d13c4186b4f60931dc279b05b848f70a582678761798d6c16e1c29ce461b17c951985c9d57b5b3db7ed0988ad8d9e9048f5a7e514823d9084d7dc9853457cc9e14c8232ab520e0bae89b3be8c81a7f10462d53441da7d32315b25ccc1e22d0ba344ce14caacc99bc9b3df2c0bdb456c41b0bcc1cf6e842de2ba325ccc8c419b0d2a2bfede38cb64b3106c34df4abc55b5ccabd0dad320b6822da311aaff9bca08b58cb2ebbefa6f3b15a6cea5f02d93ab06d1230c12d8163411b0c620f42c53f0c6883411a2b5a3e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part781 : Excludes 0x20200080000000000000000000000 0x7cb467404160210404001000000000 :=
  finishCode 147 0x124ae6b186739b89e5a2c06df70d03f069d85e89b8af8716f1822ffc4bebdabff439c32d3e7d395ba1c58261e99ab469e575b45798632fdc38e13b68f01b8e50b95f1a7a4ba2b620e57e63698bb53b351a736f9e432c8f07c1a5cc88709f0a61c57b655d835d90e344ce13d2bab2f36eb79af6b0b81ada1731b132bda316c13a07d396f5bb57c67a7e054069c5ee60d6e33435bda1c58357ee87160d357b870321201a7944f05fdb067a7c276f17a7893620e6d17a7b53893661e63425e4169f35fbd3cf17915b090913da9b70d36da16d1a7c212f67f82f086da9d9f8a8c7d7496dc2de231efc90378b68da5da16f4e12f1f5da5d2c312e9bf6a7b8b87029034f68d61a7c6df20b03605fde9e7cb8838c75efed3423ec3121bb3f7a70758ad8b6ed3d37ecfe3954883e0be983ad66a2be43f610b4fcc1b67b6a78434d36a73baaf6e84e13a6fe18d50c76063b4f98bc317d324db05f0c6d1ac821abaefda22c1263a4beb5f285e84ad7d85b67e4a645a31f49669ea174a2306be4371f48459a79efc11f12f6a76a74f2889df359b04b06c42d4e2594118835edad4e57462db75bcda9eb5318b259b86e381681a7d61abc6df28b04605fc25eb3568d4dfc2734f24da2b709db09df613b78926bd3b43d836f7fa1e49ad8783810709df2e2b6b35c279518e5509363016f1c275d15ed7c17d3c31b43f085b4620d7eec2760db4420d9c63f09e34f7890ffa55da7d65d42f09f08606fc2750b17f862f71ac6098d9ef9186eda265abdb7d046d0b6d18ad4ef93be609 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part782 : Excludes 0x20200000000000000000000000000 0x7cb463484040000000000000000000 :=
  finishCode 87 0x57116e4940dc30ce7359687e1bcaf1086b536e1c8369c14a9be4ea14b052c9bf6a64eb378a78a969b0854cd7e166d1f525cabb4ca108d3d538168a4057af6c82e317a132f6cb9acbcc6b69b5cd1ed312d52496bdada6dc74c71fd9a4857c37c15fb8c45a0d9e357ce5f220e5ed2755216e13fb8efc69ebe2e268dbf044217bb8206d4e68f0a530f965c295a3c2060a54216f17cf8f75746d4d086a964ce05792bc6934a34b9a0bba218bda7f3272a0b832d4a34ce4ea4eb1a4857cb7b3c9b71c558c5857b47ee340a432918d3e31f06ef28aa35171313107027aefa78b57ad6d106d5f2efbdecaeb57c4eb5a6d862d536a69df482d140e00c5c38cde66861e7614859b02216c27201d0b4efaa5a9b64d31600f44262e23925d32b275a6262b6d0bb4d6d77890b3 (by decide +kernel)

private theorem part780 : Excludes 0x20200000000000000000000000000 0x7cb463404040000000000000000000 :=
  splitAt 1 91 0x7cb463404040000000000000000000 part782 part781 (by decide +kernel)

private theorem part778 : Excludes 0x20200000000000000000000000000 0x7cb462404040000000000000000000 :=
  splitAt 1 96 0x7cb462404040000000000000000000 part780 part779 (by decide +kernel)

private theorem part776 : Excludes 0x20200000000000000000000000000 0x7cb442404040000000000000000000 :=
  splitAt 1 101 0x7cb442404040000000000000000000 part778 part777 (by decide +kernel)

private theorem part774 : Excludes 0x20200000000000000000000000000 0x7cb042404040000000000000000000 :=
  splitAt 1 106 0x7cb042404040000000000000000000 part776 part775 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part785 : Excludes 0x20028000000000000000000000000 0x7dded2072044055000000000000000 :=
  finishCode 71 0x622f148c01afe8229a2234f4d72ecbebb621b64fb43ba9a6d114fb27543b7d725789d741805f78fed3ed78df5c69eb17086297b09cc2f4af84ea43189a684c5b7843852ddec26de300b801e18e10d94e14a56d8427b37c5ed9b05bbc476793b495f78a532b8c26bea037436cc6e1291e9fdd84a0f74c3c5b74aaf4b6528775c43b6ef88f5f5e94e609d1114fc21be5c30089ebcf613c3bcc5a29bebc330865151ffa1dd80c4b579e29708709e28bc65b7086e18cc5d32afabeba61a5e17cb6ec1f6932293fbc29a5866118603d0990d53ef444265816e061721aa7de88a91901d2f62762229f78430ffe88a91e14c39a1aa7d82dbebdc2918045345906fa18c9d662f415f5f0a61dd21306706d275a04f113d7b66f16093439f5db4623d1357d7ba6017c6626b29609d116d19756d119897d7 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part787 : Excludes 0x20008080000000000000000000000 0x7dde60812904201410101000000000 :=
  finishCode 77 0xae5e24980619b44e320faf7035f916576635f8b39b35ac56b4d7ee190459869da8e6f38a542b895971df5eda642094ab4c9b4e9af9fdaffb04aeacdbe9be12a6bec1b045d988065dc97de76a4b3fb69d4ff7a535fb812fd85312a8b27cf1abc4ace301887d745993ee2cdbb5b8cd7d166877ce621836a674ff35f6cf98357b484e21f1635edb848308d8322cc4fa15b61d4d30c713f67b3c9af88d3be4ae3d68c8411f5d78d13c7deb4f6c398b04743b697a62e4170697b0850ad42d765f5e2cd71e7d7149976418e5d700a17614c59e88bebb5142e0575ff60dad1a0824310c57034f2f1af88d3cde7196dc3000a7169b61af1a228d38fdcc1a46623ebb26be7f7688bd2b4baf1a18d2002b98340ae5ff (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part789 : Excludes 0x20009000000000000000000000000 0x7dde60292084101248000000000000 :=
  finishCode 149 0xbc5728124da30ce430970a42ffc4ea87e8b3585ff94e513e8c2f1da0c6bf686dc2876d6313a9149afcbff588e29c968da0f4df2eef92fa6de2d3b2e3d24c3191fcbbd97cc0abcea2b2cb854113d0ae605613c2790adac495e87360543b25f98142871148b44e028635735fb82fbd15f4c240e85613f83f524b4b93aae3df3204eb297affb06e71e768b35cda577d352f06b976e2357b7a6f99152f8c5f1f8dcc296ef793897e95de4e25f2359825e95b7d7fee0bef2eda97bc9d4df0e6bb6c2f3c9a97df288bdb4b5a2cb67b06839cb970bebdad82de28b368b21a82fdf32144ac431bbec2720da495212755ff60d823a0fee20d6d1d07787c2161135f60969fa5470a584cd7c9d635fce3725ac9d4cb6d053bbc2923dc21b295155cb3a0bab4ec04247b30e65b0ef9dde1491e80dc3ecf9f30453357a1a5f3dea49d5f3eac522705a368381a836c48af39a79afe7308b8f52be14d30b01a90ae2cc64af1316c1c299938639b048fc1b698d980e925b05bc579ec4461f8bef2edcc30863d9c2927569db07e545a7ccb648d4275980cbf4cb709e2755d1b094f66d3c9d580c17eda6133940275d04614bd456c27a3dc295e94450f5acac3f69b4fef0a70870865e35ff7afc21ab06af304975cf9e6af2ffb08c27ebd286384ce4921887722ca9ca8ad0320a72d2f3e7e10a22a27d36cbcf48c8011c1fa47b66a78ad2e8a6f9f505e7b4f980da86c21ad3e42ba49a61c2752fac6417b68917cf45344560986279d1220e6bce8572ef34b8b1c3ec52c3ec8b2f9ebcf205ff157b0865ac8f5a5d8270960217a9c27697799 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part790 : Excludes 0x20008000000000000000000000000 0x7dd661092004001000000000000000 :=
  finishCode 125 0xa257116ef140b430ce42e04eb20e8d3a27ed261e4c95e37d741d27541d9ac6a1147d7a9956fc5d580f4118c258235815b4e7c14f196fdf056b68a57d75e75c789d5f5e71307d7ce6422ce5e38914531a72758227db09af3d9ec7bf2c2d7b1758bae12d1da15d4cabcf1232298d3e41f3e1a724b2759a2f3c856623688af3c52e0faee09a3e7a8ac86af528a6b972f3a2cbd4a29c00ebc6bce8b2f76bc734bd26bb9ae5e42f9044c2f1bdda0ebb9cd867f6da73b9cb0890af1c89f20b8369cb2d322c0a86a9f6f9ed2f454a7dbb9cf52a12e0509b095b0d4264fbc25b4683699ca45e35834e4eba2336eaf1b69d149a411b3709e5157cf515841d115eeed115e75e3844709f4474466c341d1a77a99b4c69cc0e60543b6e5210761f62757cf9e4beda232d784f618e8893ac877a224970d393ae82b978c86b069e917c7a98bdc9d5f3d14d1658664354fbb2d8d0d13db0d8649d63439c332b0fae14f682af4b4fa9ca91ae6ca2b846c32c272f3b0c9a7853cbeac32bd37ca4642708a68b3a0b43be13bebaf3cf529fb14a6d984ed3579df5e2ceb3f523a6dacfd48d13c16e5f7605911469eb9907ab829514df5d13eb085744f9ab853d2261e07b88b61942b78ba61c9d688b7ab445 (by decide +kernel)

private theorem part788 : Excludes 0x20008000000000000000000000000 0x7dd660092004001000000000000000 :=
  splitAt 1 96 0x7dd660092004001000000000000000 part790 part789 (by decide +kernel)

private theorem part786 : Excludes 0x20008000000000000000000000000 0x7dd660012004001000000000000000 :=
  splitAt 1 91 0x7dd660012004001000000000000000 part788 part787 (by decide +kernel)

private theorem part784 : Excludes 0x20008000000000000000000000000 0x7dd640012004001000000000000000 :=
  splitAt 1 101 0x7dd640012004001000000000000000 part786 part785 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part792 : Excludes 0x20081000000000000000000000000 0x7cda48322481120408000000000000 :=
  finishCode 105 0x38184be642d12ca05611151661f689125f5df6d7979eb958453c42f6b049abd13ef9edef4a3621bde8ab6999e25b90c87dad4e63d7ee5b492f695889f97a577e20d7ee2ae117965f05e99ed4e1f580db5e5ed5d9a5e56d514d77eb087eb0777a53da3d76e22e2cd77d7b5a1148b33cfaca6646d4da3741eb53a3d87d86fb0c57ec5768b38838ad962d28968501924a1865bde8ab357897a2442862662aec1789109d6f77b98b33c5a53705e244c662cd8645ae8996f78ab4f3891a6461bddefe5cb8ab357a41ad4d8667113ebd352cc559ab922c1f2d6ec33688c4e3286af6a7122c55b0cc56d247c30c96cd31a8574a32f48a2da9e14cbb329abef2f2f2b050b0ca79cc330c7c5310ad0d5046b2b5d9603619a2aed918b43f17a65f75d19b9ccb61f9b538ad6198ad9865866963f2b0f7f1072f484bc41cc0704bbd6ca180e4115b53570599e5658bf6bbf459b54a18aefd7cac5717ee38bbec32b2f525b64a8092fc2fc6af15e4bf571eae95b17d6196f79eadf3e26e97909f619 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part794 : Excludes 0x20401000000000000000000000000 0x7cdae8816280902008000000000000 :=
  finishCode 105 0x36990ba481d10c5fb785b18365978351d099abde2d3c48fdee6d4df06646221ad4debc8fd425f46899b65725567af6d123f6f1191351bc611f04916a495210519abe54742e9262648ff096d09899951a6fbc44cb0ccfa610b441bdcb021be7d1897ae208cf0ad436a6c328a766344cda9d721928351411a5e57fc64585d2a61916e179798f619a8229b77c13ab9a113346bc1b70dc2518498f980df3d4854bdc0d3b5a9cbcbe7a7fb06cc2f50704630968855cd61368da956565eded2d80e59eb535217cb98fb096b5360db65c064741285f5a9854bd816521623e0d15688b44baffda9cbff38625a22aed4e5ff4453fba20ed4ec318975ff95197feb970bc22cc59d2aabaac16de30ef523828c5982aaead6a6da370b66117a6955445b53509539944bcc0a24bf4c29ff786af9ede2cec2597d7c9849d7661be25d756b53b6533086a384b52ada9b70c4b8c8d38d696a0312f6a6de3386e19865bc5b06509c2989fb5387db416196c19ee542d405866d984b23f186462584eb537d36911e93516d13519164d464536e19865bbd866 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part796 : Excludes 0x20005000000000000000000000000 0x7cfeda40a8811002a8000000000000 :=
  finishCode 63 0x5b2f974361ca591f03230c94d6196f16cf275890565c3f743e26ecb4906619b80bbe86b531a2ccc2cda3486d1914c9d5b466e1e0096d30ac336a68a64eb186196c189770b686da0701866d10c3621ada2d2f368f2d7610c57d96cbccb1eb67d196fa6050d6b05a2896935a2ca6ae8be8cbc84fda2d2f365b13715f6935a2a55cc7cc8cabd1527f348d0b9e649d50d5f8d3f4c9caccc2e10e85ca8d31ef5b74845c1866690c7e21ada1bc6d16979b2d8af991b0a616369f9eb663d165166d0b5976f15fb5cb9b7d7eec1c05fbd0b96e6d4d0fd8362336dfc2d9b4577e2be5af6d1459619 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part797 : Excludes 0x20001000000000000000000000000 0x7cdecc002080100008000000000000 :=
  finishCode 171 0x17cb6573206f26d2c1b13a861d6186576eb49a576f1b2d976ef168e01bbd22504eb84f36cb74a22cbcf13ed934086222da2cf93843061e10d10b456b74a84e8308c1b297a84861ca281604ff902ffe13d85a47f2b2c2ef0f3bcbd7da9c066b9a8232e6affb129a697b7af5cd7c5a9ae29a64df06b1436af9659f2537e9596a91dd87a57fc9d709a08859ba54554bc30e4088b84f59aa78af6afde18c49b4de9e368e0411f086348943825565cd22324d7bd89fa9bdb9e53e0077b98695df9a7709497de1e0fd68d9555df943e2909fedcf610b6ccbed84384f8434a8e13b64d84b8434df047b6ca7fca1709fec2f3d4da3aff827da9d68ab9a263616c34ca7cc8ae6de2d15c36fda30cc82c0dbf456b06b04893ca16213a16da2f06bbf045ff897d13e6df44fad4de0f810c6a2c208f92793009bd7adaa64bcada3aef861cd3af0768a18760ba22a22cf5ef061876a73c192f861a08c09fa12a164bf5c84681866505cf534b67da3a7fa85da7cde2a02f83438e10c56bf258bc5018b3ad4db4430ed0b624a226660d8ad4110c3b42e265b3e5ff983741c05fb9f4ed4ed162b413c49c30d3fe50b7c1a2162b6c938c83b030eb3560d8998adae061cd14048ce25f09707ba20c5ae25fb3d5fb883b3594062662b640186857036a85c5989eca0322caf6da2d9c0a44e3686cf90435ad1e1cdee5e6e9c430c9d5c98473dfaa003e6f778b5e9a5f6f797662b5b266036e9da3e9cc06a121872c6b99ba50d695561979d603da4c298dc7a301bdccc272dea12f2b3dfca6b09861bcdd6a7846d7315ac26186fc6199f4e2ac30d7a430e5e997dc30d80e515a9c5b25ba4d9c30e79d367619ae061ca186664650b5d1b42ed26d143ff0866465be63e4ffa6f509 (by decide +kernel)

private theorem part795 : Excludes 0x20001000000000000000000000000 0x7cdec8002080100008000000000000 :=
  splitAt 1 98 0x7cdec8002080100008000000000000 part797 part796 (by decide +kernel)

private theorem part793 : Excludes 0x20001000000000000000000000000 0x7cdac8002080100008000000000000 :=
  splitAt 1 106 0x7cdac8002080100008000000000000 part795 part794 (by decide +kernel)

private theorem part791 : Excludes 0x20000000000000000000000000000 0x7c9248000000000000000000000000 :=
  splitAt 2382 103 0x7cda48002080100008000000000000 part793 part792 (by decide +kernel)

private theorem part783 : Excludes 0x20000000000000000000000000000 0x7c9240000000000000000000000000 :=
  splitAt 1 99 0x7c9240000000000000000000000000 part791 part784 (by decide +kernel)

private theorem part773 : Excludes 0x20000000000000000000000000000 0x7c9040000000000000000000000000 :=
  splitAt 1 105 0x7c9040000000000000000000000000 part783 part774 (by decide +kernel)

private theorem part763 : Excludes 0x20000000000000000000000000000 0x7c8040000000000000000000000000 :=
  splitAt 1 108 0x7c8040000000000000000000000000 part773 part764 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part800 : Excludes 0x11800000000000000000000000000 0x7ee548caf000000000000000000000 :=
  finishCode 77 0xca602288b6ccb83ebe1320f40b7a45317ce5e67b598f0a57c3acf619e323d07a6d79f867acae536655e36636313a6db357b1995a5e506de7e41b9c461f0bd7537ccaa0db67b0ac69f32a836837052cf7729b32a836f6309fd9e852b0a854e72e18888381913c99580a6d465ddb3dbbd3fd4b6514e34b8b5fc46c51a91c126565e695b9599e365e42869778a317152d8a194b661eb376cf5096f134f0a1ba4527841b5a7c32b78cca8c2c11e92df038cca9a2ca6c7ba48332b0f2f9b29b3c6ccac32c46cbcbcbcf52142de3360cda33cb0274d2c61421324a720dccacadcf9e14348b8532798009b187a5e4295b3d80630827523cb7d1eb5fb78d1eca5b32b2f3050e202a634f6bf9bbe5be09948377c2f2da332b3ca3da98de7d4e5b4548e78da6398f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part802 : Excludes 0x11400000000000000000000000000 0x7ee918a8aa00000000000000000000 :=
  finishCode 105 0x329a4ce6606a678cc862fdd93444d4585cfb62e530d8658f45a84fb4bf6c985f3cb85193bbdeda22ddf4e2f2efae2e7051b0bd00c8e213d112777d70a1995b4520cf764aad7e1476a33ebbcbcf766a24ef808a3c2b0faf70a850095428e2568af995d0597c706e63cfbed0f096d0d98fc2d9956090af99185f65bd8361868a4ab4c7925ccad70b2538c822f9ed1215a4ef404f3b0b620460e655e93ca71892f446c2f0efc2d79798f68fb445f3f06e63e3cbc2dc25161b51d11c2f99517db25c0166d0d799a476890af27799198345f60928d0d8c7f445ef577d82598bbf688e86afdb21656d0d98f8732f3ad0f435654f9ec0647686849925e86d48e63313bd633964b013b9a8c16613a6a34cacdbea42a7211f04993be7238a2ae0351c2f87962be9b4fc617e645ef62bed0d0b33239ef665744458699517d7cfac5c2a164c2da2bc955f5da166542ac28e912894da6554e62d45ce290c99552da2061ce96f6df98fa1ce9b43be6efa3d24fa5f8a1995351a2a69b58342adf92886db06e63db4583585e63e0998af96f6d1617a63f4362a426679a239c86531cfae9fb15e6a31431587ef0a6195f5e6562d65bb3237d7a2561eea63979995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part804 : Excludes 0x11020000000000000000000000000 0x7ecd08cd8122040000000000000000 :=
  finishCode 79 0x663115837994640d5e1931f60dc40af8b0bdc26560ab94da9969b4a6cb18bce17d4c628e7f332b140ab85e6656e0f6ba1b1f3afd855be1d2df83f4c68bcbebe88ccad325914361c02f23132b2f303fbebc4ac57caccc2afaf29b6497982957c6c2f8a387997c66565e4296c2f60fa6d89b8a4e278faf286efc23906cbb699578da2be1b708e28e656535793c9950a39b070b68b589594d985e3112b688b06c4d84cd84b68783338ac35fcddf137617bebe4178647617b58ccac4acf24184b12eae1b0baffd85ef62be361789fd85e0e31c9c1acbc221e5e50857d7c24a14b5ec6b457b5517b2b8b7e205f55796b456b76157861104dec6b457b58a9c25ad16584c8d796a49a44a1adea3f7b1b4741b6e795994b7445795f5695952d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part805 : Excludes 0x11000000000000000000000000000 0x7ecd28888000000000000000000000 :=
  finishCode 125 0xc0513488b79cb26d3303534c8a2f59ac9b4c36c9faefefaef7b4329130aa4709762569616078a9b0968818a9977515a2541de4fd41b7d7995b51a634de5f5df5e9e4b331883618a1bc91ccd23322826faf32b90413b41617e59489e20514381d6256506b315f3bfbebc5aa63cbca442eff0cb12b0c49bc9bcda0b2eecacbebc57c4aa7e9b48d4ce280faf987446265720c86c79b9e2562bf0967cf3f90af89507985a421e5be3f9345964305f5dce9854b5d058956858faf41663deede5e7cf0afaa59ac7c28368272c268a2fb30887889c21ed1e685a51b4fc8682d4a34cebc615ef76f9e2fb37bd92a990345a620dcdd312ba22f9f2c3684bc2857da3d32a2fb407644accad95c2872c683768b688a0dd286e79eef435f3e656ce5e261e371379481b4bdeda2332b486c79f3d7aeb3b24fa664258f9ebc737bbddb6c925d85f66f30e49f20db5cb7ba63c43648b2c331b88369975c6a5f5cde65964a44e1b7e3611a97d7615c2436c6c2bae3533c7a1b0c2175d06e5edd070755ed83ced055ed41b97997cde1e78dc275eb7d79591a9361173b41663e9b4c4e2bdf5c6a6c8faef0f4cac368d4c4dafcc4dd88bc560dc4c662776e79eedf3db66656d06d3489959bdd3a69876b952399552392e578d3a66553863f941396f1a9361 (by decide +kernel)

private theorem part803 : Excludes 0x11000000000000000000000000000 0x7ecd08888000000000000000000000 :=
  splitAt 1 101 0x7ecd08888000000000000000000000 part805 part804 (by decide +kernel)

private theorem part801 : Excludes 0x11000000000000000000000000000 0x7ec908888000000000000000000000 :=
  splitAt 1 106 0x7ec908888000000000000000000000 part803 part802 (by decide +kernel)

private theorem part799 : Excludes 0x11000000000000000000000000000 0x7ec108888000000000000000000000 :=
  splitAt 1 107 0x7ec108888000000000000000000000 part801 part800 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part808 : Excludes 0x10600000000000000000000000000 0x7eb91c30a3c0000000000000000000 :=
  finishCode 71 0x5e2c924ca6e1867099cb0290a9cccacb7615a8974974cadf2c04ef304856da1c9e729f3133164ef608ad85ee98e0918822bccaa21c4cd2f6b86b3f15b85b3c2e84b48da5856c8975844b44d539ad4621e2a5bbed46515087991d11ce542c0b77059ccaa77a26a2bc512e697bd116e1995443be370cbbedde4ef28d1194bf4465bb97bb66e2504ef378a97cbdd32ada2166bf74ca9a4859b06cde37ca8306857c9de4ef59de888578b7d15a30715f28aa20af1e88b6fb0cd82496c437c25618369951814e509d52d9958d274453954548f609d96661b120a5fa7195d8fadf2ecc6d11858585ecc49deb51978ed06d2e5120995a2b4cad8365968adb4466565ed4b697b995351 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part810 : Excludes 0x10220000000000000000000000000 0x7eb48e152064440000000000000000 :=
  finishCode 83 0x1a0dc662f1589e1bb9a7c4175650b6e1d117d595d90e5775dc5e360f39735dd5d5ba532d8bc68828966f33c1b749fcda233c88226afcd85fa22c1ec0f28ae13c6f2c1fa236cd11a6550e65ddd11be5b2586d34897390dd7c5ba5bdde0973538aeacb9cf064688cb9ebe31376774c8966e88af8dd19086f2c308ac40b6389caeed9dafce88c62b6a2d8f2f5dd238d85ddb3790dd3bdf2d0de5f96a7a5750df4453be04bd115dd9621bb07da22def323437de2a0def28aa97a1ca26c917ae44b885b445ed6646d912f21ba97a85d15afab64b622ac724069366759db7bbcdcb9be8bcdd29fa23374a1bbdc8b2cc2ef7ef9731b2f1b74be5a20c3290e808998366574445ddb9dbde78c1b6888469a49acee226e6076e93797ad96cf445f46b93cd118de69c6654d24de65c798ba1c578d08e9c66093eb97198d0ab37717f (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part812 : Excludes 0x10201000000000000000000000000 0x7eb52c10a940281008000000000000 :=
  finishCode 59 0x178924a186738b9f29ca1ca25d62f985b4b6c38c2fae0b0b93bd82d915a98f614cbd84bccabe6adad4c663b531b5cd0bf12b32a2cb4abe10ccaa25ee2f99c2774398d64de690d93373c42cbab68728b4661b66d0d6c7357367ce22bd106a5f15b0b7a79a1cd106a5ea166cf4aba2ae6115d6ce349b315df5fb5b38d26d9989e4b0da65c64e54375ff99534995b97fe655d110995437a56d48da9e6e77cfa459256e4e19912779444295695b4375233c597c5ea5f3f41e7970fda5543789de204ee6925f71f5e13ae1bc3c55d9dcf0e237b88af90dc9dd85e (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part814 : Excludes 0x10200080000000000000000000000 0x7e952d102060410204001000000000 :=
  finishCode 115 0x1b88e672c8bbb785f9a021ce84d84e4eec3360d0bb445e3400d15578f446cc21be10c63ba17316f4f0e35e2b0c32f131b3d33cf36b5e883a23b411bb0b7425dd662d78d0ddf2eac502f9648413bcc5cf6ac336088617c10f3166aefab2e73d198ecc5cc4cb82c331abae0c2ee6af66f082bbdcc4bd6b069abd02112c619a8042cc1c84ab833b8d307a2369a4533baa12ae0c57d42c8744254e1a55d707426b3bd1195724fa93e9a5eb57068415281a235cbc5a18661ce249c278af60118f455980621b4ba195c86ec03456a85918da134c6ad7bcd93bbeac4ef68bc670d7e36f455d098d5de6ed3689779bb4d9155066815c8830ced142e601a63437313b42698b1293f98af2774ff89df394cc1f8b4f42486ecfd064c366010696bfd098d5c16deff699cbc300c89a8af10c2188062bc9dd0decfe27776439e84d0e385b15ad172f1beacb6b9cb2542208aac1b2f1a1bb6211a23353ad9da6bcaa77be5bcacf4ef0b3f24fa64744694f1255b35b390de441cc614cf2ac12316c1b485b385ed0964e18ad (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part815 : Excludes 0x10200000000000000000000000000 0x7e942d182040000000000000000000 :=
  finishCode 169 0x2890845bbc50120c3398a84cada1b1744ef885978dee6c81f351eb07c42e88a1292ecdd2a2b9c7cf81de23497578d1561c6d1198397b9106019c5c1b24c1da22c2a047688c1fa78f322a2b307cbdb74e88e82a19cd114255ada8f621545515e1c608d97b9ba61c4897444216d053338f9f03b92ec46af1a2ad225930737bbe7d3233c964115810a2ba84b25ac38829e85b5ca12da13a174db25ae84b5cd36da12bc7614da1332284a89b13337bbe7b07a11da25948b2374b7be4112d7067bb4e19837839efc1fdf3e379441cc58339a05c79e6d155e6e6b979b8de60b379b6b9b0684c59a8af15a84b0828ffe88a21b5cd9290896e08ab9ea6645f3c2be5e3b427446a517a925d5e34414b9908d1059928a4411ba520d8e86ef7b2d34c1cade88cc1d2b769663b323684ccabd4da6a1be88cf2b886f520d38c38e889a4cb8cc69b4aead0e286f172d38aeae88da5cf2e6d332b30fa2374dc442b886ef97436bcd9b4be7c8473c5afa1c5f3e654d8545650bab3e7aeec303127a1bb00cee2f7a9e26d39cb0533410e31b4af1a1ba25d71806181a69a2162b578d08f0915b4c8b00a8ac56d31a89b48983b4257e5a44d66635455855456359b05f200bc710b0bea12c38d2da2fad7312f5a8ccac42a64cf9ed7284b24ae50370c334896436d32a832c2ac0315b4c8a2b8c7c56c6b26e215b225ee3314c40f8d9d104dc548636702db42dbde20d85512d80495e0ad441dc6d2c9488ad908db5d155806c1a17058c42a2ad36cbd7a06afb0a657c3ccdbc3edf0d10665668bb4f6d742387b89dc5ed804dde108830f74c5b6b92bc2f6167b8a44b358c2ac036823b9b65b9e5b6455455863e36798b8ddc9dc9667d50ad0b3 (by decide +kernel)

private theorem part813 : Excludes 0x10200000000000000000000000000 0x7e942d102040000000000000000000 :=
  splitAt 1 91 0x7e942d102040000000000000000000 part815 part814 (by decide +kernel)

private theorem part811 : Excludes 0x10200000000000000000000000000 0x7e942c102040000000000000000000 :=
  splitAt 1 96 0x7e942c102040000000000000000000 part813 part812 (by decide +kernel)

private theorem part809 : Excludes 0x10200000000000000000000000000 0x7e940c102040000000000000000000 :=
  splitAt 1 101 0x7e940c102040000000000000000000 part811 part810 (by decide +kernel)

private theorem part807 : Excludes 0x10200000000000000000000000000 0x7e900c102040000000000000000000 :=
  splitAt 1 106 0x7e900c102040000000000000000000 part809 part808 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part818 : Excludes 0x12040000000000000000000000000 0x7e9e09b60890200000000000000000 :=
  finishCode 103 0x5b32958c422dd73086b32d7856995c7e6c32faf409a6e1d84ef0024d5eb8fa53864139855065ed687b32b2592cf96d4c6cfa619cf1ed0bc258a35f36e74e19f544fd864cadf5cd66b99c66471f5e106924af30cb75c3124af286eba23e2d49160f787843f6934d06194f85b6c62586625696d17d6197d7a861289386eb6f5d0b823538655d7ce257879741f4cbe6d7749edb2dee83384b4acb5dbbfc51a63d49e7d24af688b74e2258ecae374b7b855c6b248f433be38b5c60fd64b39657d76e7d1117bae373c126faedcb32308889c363ad7c9cebf329e1573234c33cf914d62a0156dcb595b75bcfda2365b37ab6de88a73c832d8f58a861028e5366c56eb88f9ad6b4bd110ab257acb5bd5b6f446706921472fccc8e0cd84af8ed775c66651f5e08c332c6d509193d5855ec65f94195af93d61962d49ddad617bbc65208c32bf320cb0ab7ab6acd1b6e8818a9277883c8d0cb16adb769f2fc8128b9d69f37ad32b03924cd2b01136888bd93bd410666f5c2f906623e3d56e5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part820 : Excludes 0x100c0000000000000000000000000 0x7ebb28560281e00000000000000000 :=
  finishCode 101 0xd4602d95c45ba0411866202fb3ebbcb9a2b6db7aa09cf0af76fae84b10f1531032d7bd4cabb6dbebd4270ec7d782212c55c68b2af51dd49b106f532c31a2e0cbdda12d268becf9ed2afaf00a852109608f53303459b15baf426785413d0b8b8e8ee5b609a22027684bc3b758eeda1206af47cf24bacaf444d17446785823d5da1331e826d6b29b36dd7168faf2432ba9969ad866514cb4a785f023bdab53ad98b9c41c2e730cd1dd4201304258813bc116db6dea117019d35cc1da234774d788b3da20db149de8ee6c588688842d15a4ef5338fd912c38a70d7248c461988362cd1b970b67ab88189b425acf609b7ab7910a1c44bbc4eedeb2b6f9b3bf9a2ca3117cb613bbb086685f6b94f58716d9413a17db9e17e4a74f58835c184353cd8f66f42fcbdc38a12c4dd217068af09f5c3970609796509f4f5ac4d30b6d097a398f3452777637bc78284b68f362d21ad67cf6d59e180a03ebda7d4cb10615a2f6c3310883a2ad09624ba3b9914f585b5864d167cf17d (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part822 : Excludes 0x10060000000000000000000000000 0x7eba981700a03c0000000000000000 :=
  finishCode 87 0x6234178ba542708728aeccc23ebc41ca43a16bcaf6ba22f86bcb688c5692ec15710754d42f9d31a4bb837254e12916928af2cefed36d2338926a112c9765ddb416157d7a2b620e9598997b5517991923d29be351d1198f515ac3e34265c3d116b5c25539a6f7b1b4454e4d4504e351d110ab945cd66d88732b344cb73a8aa97cacd13315f38745d180987844bc55b65cdd6faebcb3eab00a1baf2cfab15afae86f1333659aca1bb6dd15715afaed97297a90e13512c7c73599bdd4bea6fd118555bd5486594c3519b27446c2513da9be637097715c8839855f5cd6691a2312eb73b7bcb9c962dd69e34c28462f361249449637ad334463493eb93d7445395f5df5e4fd7b56c5763ebd31e0032cab9e962f1a6b2f8685f5cb2b89762bc1e68c321d89eb217be1beaee183e4137b589b8af34985ce9ad3d5b2df5e0737b534909b9a450bf094d241b6 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part823 : Excludes 0x10040000000000000000000000000 0x7ebaa8120080200000000000000000 :=
  finishCode 119 0x5f2e9a01a9c4582f0f044d457843ebaf2da22c3358a4db0956eda6c8ff06d16d70e636c27970d86516f013845bb4b93d50ddf5e991c277a49970df3d3841662ddc257bb62167cb2b85a47349a61b4cb84b4a74709df41e9710f94ff5c3075977c2d9913596436ccf32d8eb87537c25a9ea8b68868272f9a2dafca17d50d64fa645b5f3d0bb43456d75e99def5bdf4178c44e09dd0e6b8db737ac40c54bebc4290db7100b62b00bbfd69e1e7a12046dd747b10b2df2f9c3dedd6a2b84ad8ba226b2ecae217db2488b66b2d2330c9f2c136d2315f534a70bebad7d2c6d96dab24a2461bd5e5e7cf4fd4137a3619a61407516de1ccae77f619b600fd69384a2268b6f0ef226b2f23600f566cb2777d745bb613be130866e752f5396c78f55b65b6e87104d5f3916cd674180ae33350faf7845bc430cae1c8728aeb872fc9a2c9eaf9f68584ea1b9a2a2bd321c6a5345b345437457aa5e17e634588351544d85f8d1653e20d45620eac300c89a8b750c4684c22f84ba22d8a872a2a89b001fb9eedb560139adecb70858574257e512ea188aa21ca2bcc7c136a5ea2b107492893409b9b15f3d3f4d15b566e55cf7bb9865d90089bad1c1b56bd73d0beb92f35a4c3684fc4de12d31eeeb1f2c57cbdcc2a25cc330045b88398568fe6e75c38ad7d7 (by decide +kernel)

private theorem part821 : Excludes 0x10040000000000000000000000000 0x7eba88120080200000000000000000 :=
  splitAt 1 101 0x7eba88120080200000000000000000 part823 part822 (by decide +kernel)

private theorem part819 : Excludes 0x10040000000000000000000000000 0x7eba08120080200000000000000000 :=
  splitAt 1 103 0x7eba08120080200000000000000000 part821 part820 (by decide +kernel)

private theorem part817 : Excludes 0x10040000000000000000000000000 0x7e9a08120080200000000000000000 :=
  splitAt 1 109 0x7e9a08120080200000000000000000 part819 part818 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part825 : Excludes 0x10001400000000000000000000000 0x7ebbcc900b1008800aa00000000000 :=
  finishCode 51 0x16cca6e3093c1a9aa1b4b7298652f51532297a71bd66db11999587addff08c0bdb6db6e6a96d92779b65e6665669905232776e9ad2f095eedba6b4bc256f79eedb1d48dd15c9955ff9f3e9bd3fcd44da6b168f3d5e85b63b0ba54cf7686ef5758ae13bb9250a034df1ece84a7fe83af897ec86ed43a127b32e321b9b4bd4c86ebe35c7b9b095dc4da5f46c236d91a9a794833e5b7bcca9a49b4c51d07f335bb7ba91ccac921b54070963f9991b4ba555f1a2bea55b5186d6e96a13b8d4b2171d7561c6233c274cf5cf00fa1be97c4e48cea5998d6d5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part827 : Excludes 0x10021000000000000000000000000 0x7eb7484d09200c2108000000000000 :=
  finishCode 81 0x371acc4672f974377379b459ba658d10512db1e9956c7a65512cd9e51589c4f2654d5e8f607788596f6178ad6c5aca742e58e56698e30d9955f1963979995ad0ed0d6cb8a97b5995ce57258c83615e4bc920cd331530f3120af8b6dd0daa02be2c812397c4b8418661626e7932352ad95af1d96a72affaf8d1473c8c27ec010be08325d94d98270a65e5b5578e98f643625e61e6061879b08db566467bfa559638795f1ac2f8d2f2bf732b62339584558ad94266554e5456687995ac4a27932a69f47b456bdfd47b2b21334cacadccad749e511b01430bcb6db7abe5be8c125961796c56f56d19bc53f588827378d31a7ec6104e6f196fa655b6e9639795cfa655bc504ec8bff050a2bd6321445edd05a956d1df2d85da667d5b47865441789a28cd265de4e5441995 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part829 : Excludes 0x10001008000000000000000000000 0x7eb77840094408400a040201000000 :=
  finishCode 109 0xce6b3097cac0d4e209de357377b63a24932b3c6e5aca6d3df3d3f529e6f55c7b4f7cf0619756493cb439b953f62169337abddcb5ef0f84b2eaa707a66af12d04b6d55d54139abdb55b96533e7b55b7aa7ea84d22590882374815cd6b67b01587de118fdd84384ad4a4babaa40f686b5292ec42d84b32b88ac22bca5e6cef476220a84d31cdb2dd2d4b4ace84cdd24bb68a897248012ecf531429faf9af46d5a6d939663ed16805912085ed05cf96d88ed31d3061f4c891dc41f612d94b4c8b791d987cbd891cb9ed3f0cf74841b0186d07d092ff97bb45b47061b0965bed3e699c25c1f6cb847eb16534a6b57da3bd4af893b9b7dd21ee6e95e3455c2597566571160b621ca2ad9ed496f9ea72d8b525c410e53cea4b6c55237cdae144823ddd2ae9faf9adcb74979a1ee2353f6a63564cac95769f84ed76b8311a85f255cb6bc4d9ed31a17d58d65c2e9886e79f3577cd5c9de48f9b36ab72af8cf7b4ca9ab93be0dd15a0bed4a6aec2f70883e6c11e69edcb85b1a7cbdbe7a12d349957cfa5e4d15a9624b96d7cf (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part831 : Excludes 0x10001000000040000000000000000 0x7eb368428b80080028001000300080 :=
  finishCode 93 0xb66b3099cbe450d64dc46a573e0158af5af6b109b995ac100cee2da24bb5a1d1ea7eb58d431174d422bd51aa53067bb6eb52d9959747435e5e515444352fa53d4e66469579a265eee06cf32b375a8ac43b6ac36d10f249836acdcaf4a55827d3f427e8797cd804a1a0b9e85f32304d9fccb6c12a13f2e7cc8c13732b12ec43c36b64a259b3d617974995b05c17ec14e797d0d99109f79958029c3f2d12272d92ba2d934c8c2fb15ef7b837026b6cbccdd2c0ba32e0b64cb684fafdcb6c68aba24eebab13b9abccac8af1a89b8c51d128995ce21cca72886deb60d848a2bc68b584394432359f554e45a6ce3e7cdd6a728aef9b279bc8bd584fe72e950c46b115db2e443c215cf367277345910e003530cf217b6aae7cc8cba32af136d8aba335aa258d4e23588731359b781fcf6aa16d9f15f370eb2f9745c1a17d04cd5d77d7ed75685f89b357c29909655db566457062bd74413e9876f5 (by decide +kernel)

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 30000 in
private theorem part832 : Excludes 0x10001000000000000000000000000 0x7eb3684089000c0008000000000000 :=
  finishCode 95 0x671867097cb60d4cd0de65984f02fbccaeac36cbca099b0c61f566bf8958af4e368c3f6bab30a4834bcbccccacb9f4579b7e235128367b2285c887322eef285b65da17a1b84332b3232df68b23811554be8877b997b9919579a2540617e5d18af98fa64669688c2f253605595709b8958afb2282891373c7d109f90be55e16fa55d73e55e09f5d18c3eca6d25e6e26ec8e0211826ed25aec1565ee5930b35d91bd2cc81aee09b94dc2598586da55e596874c2bcd903c23f692b899177792adaacf66cb66ab98f789a65573f504ef1b39b8cf1ee65fba477d160d277a65691de557c6f9889a3cfd2df10e23b0e332ad8ebf64ef74b664250bf76a3209bd6850af8a09ca0332a1433dcccaafdca03486a79b9d3ce219a712095d54139eb54057c57ef112cba6a23190357959a5edb267b9959a5eda9defd68f7304fccacbda80cc8bd6d0be2dedcf353cd8eb4b459095705f4427e644c1e8a996d16f (by decide +kernel)

private theorem part830 : Excludes 0x10001000000000000000000000000 0x7eb368408900080008000000000000 :=
  splitAt 1 66 0x7eb368408900080008000000000000 part832 part831 (by decide +kernel)

private theorem part828 : Excludes 0x10001000000000000000000000000 0x7eb368400900080008000000000000 :=
  splitAt 1 87 0x7eb368400900080008000000000000 part830 part829 (by decide +kernel)

private theorem part826 : Excludes 0x10001000000000000000000000000 0x7eb348400900080008000000000000 :=
  splitAt 1 101 0x7eb348400900080008000000000000 part828 part827 (by decide +kernel)

private theorem part824 : Excludes 0x10000000000000000000000000000 0x7e9248000000000000000000000000 :=
  splitAt 2382 94 0x7eb348000900080008000000000000 part826 part825 (by decide +kernel)

private theorem part816 : Excludes 0x10000000000000000000000000000 0x7e9208000000000000000000000000 :=
  splitAt 1 102 0x7e9208000000000000000000000000 part824 part817 (by decide +kernel)

private theorem part806 : Excludes 0x10000000000000000000000000000 0x7e9008000000000000000000000000 :=
  splitAt 1 105 0x7e9008000000000000000000000000 part816 part807 (by decide +kernel)

private theorem part798 : Excludes 0 0x7e8000000000000000000000000000 :=
  splitAt 2159 108 0x7e8008000000000000000000000000 part806 part799 (by decide +kernel)

private theorem part762 : Excludes 0 0x7c8000000000000000000000000000 :=
  splitAt 1 113 0x7c8000000000000000000000000000 part798 part763 (by decide +kernel)

private theorem part702 : Excludes 0 0x748000000000000000000000000000 :=
  splitAt 1 115 0x748000000000000000000000000000 part762 part703 (by decide +kernel)

private theorem part642 : Excludes 0 0x348000000000000000000000000000 :=
  splitAt 1 118 0x348000000000000000000000000000 part702 part643 (by decide +kernel)

private theorem part518 : Excludes 0 0x248000000000000000000000000000 :=
  splitAt 1 116 0x248000000000000000000000000000 part642 part519 (by decide +kernel)

private theorem part316 : Excludes 0 0x240000000000000000000000000000 :=
  splitAt 1 111 0x240000000000000000000000000000 part518 part317 (by decide +kernel)

private theorem part172 : Excludes 0 0x40000000000000000000000000000 :=
  splitAt 1 117 0x40000000000000000000000000000 part316 part173 (by decide +kernel)

private theorem part0 : Excludes 0 0 :=
  splitAt 1 114 0 part172 part1 (by decide +kernel)

private theorem noGood : ¬ Good 238 16 := by
  rintro ⟨c,hp,ha⟩
  exact part0 c hp ha (by simp [Red]) (blue_zero c)

end Case238
private theorem no238 : ¬ Good 238 16 := Case238.noGood

theorem spectrum (n : Nat) (p : n%2=0) : Good n 16 ↔ n ≤ 236 := by
  constructor
  · intro h
    by_contra! large
    exact no238 (restrictGood 238 ((n-238)/2) (by omega) h)
  · intro small
    exact restrictGood n ((236-n)/2) (by omega) yes236

end PalindromicSixteenEven

theorem OMA.solution : OMA.R_Green14_W_3_16_R2.H2 := PalindromicSixteenEven.spectrum
