import OMAReductions.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1

/-! A checked finite enumeration of transversals in Latin squares of order seven.
McKay, McLeod and Wanless computed the transversal counts through order nine.
Rows are masks on the 49 column-symbol pairs. Relabelling the two coordinates
identifies equivalent partial squares before their last four rows are filled. -/
-- Lean formalization by @KoaOkano.
namespace OMA.LatinSeven
open LatinSquare
private abbrev D := Fin 7
private def digits := List.finRange 7
private def pos (c s : D) : Nat := 7*c.val+s.val

private theorem pos_eq {c s j t : D} : pos c s = pos j t ↔ c=j ∧ s=t := by
  simp only [pos, Fin.ext_iff]
  omega

private def bits : List Nat → Nat
  | [] => 0
  | x::xs => 2^x ||| bits xs

private theorem test_bits (xs : List Nat) (a : Nat) :
    (bits xs).testBit a = true ↔ a∈xs := by
  induction xs with
  | nil => simp [bits]
  | cons h t ih =>
    simp only [bits,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,
      decide_eq_true_eq,ih,List.mem_cons]
    aesop

private def occupied : List Nat → Nat
  | [] => 0
  | r::rs => r ||| occupied rs

private theorem test_occupied (rs : List Nat) (a : Nat) :
    (occupied rs).testBit a = true ↔ ∃ r ∈ rs, r.testBit a=true := by
  induction rs with
  | nil => simp [occupied]
  | cons h t ih => simp [occupied,Nat.testBit_or,ih]

private def rowCode (cols : List D) (f : D → D) := bits (cols.map fun c => pos c (f c))
private def symbols (cols : List D) (f : D → D) := bits (cols.map fun c => (f c).val)
private def Agrees (r : Nat) (f : D → D) : Prop :=
  ∀ c s, r.testBit (pos c s) = true ↔ f c = s
private def Matches (L : LatinSquare 7) (rs : List Nat) : Prop :=
  ∀ r∈rs, ∃ i, Agrees r (L.mat i)
private def Good (rs : List Nat) : Prop :=
  ∀ L : LatinSquare 7, Matches L rs → ∃ σ, IsTransversal L σ

private theorem agrees_code (f : D → D) :
    Agrees (rowCode digits.reverse f) f := by
  intro c s
  simp only [rowCode,test_bits,List.mem_map,List.mem_reverse,digits,List.mem_finRange,
    true_and,pos_eq]
  aesop

-- Generate a new row with first symbol t. A branch is discarded precisely when
-- a column-symbol pair is occupied or a symbol has already been used in the row.
private def rowsOn (used : Nat) (t : D) : List D → List (Nat × Nat)
  | [] => [(0,0)]
  | c::cs => (rowsOn used t cs).flatMap fun a => digits.filterMap fun s =>
      if (c≠0 ∨ s=t) ∧ used.testBit (pos c s)=false ∧ a.2.testBit s.val=false then
        some (2^(pos c s) ||| a.1, 2^s.val ||| a.2)
      else none

private def nextRows (used : Nat) (t : D) :=
  (rowsOn used t digits.reverse).map Prod.fst

private theorem generates (used : Nat) (f : D → D) (hi : Function.Injective f)
    (hf : ∀ c, used.testBit (pos c (f c)) = false) (cols : List D) (hn : cols.Nodup) :
    (rowCode cols f,symbols cols f) ∈ rowsOn used (f 0) cols := by
  induction cols with
  | nil => simp [rowsOn,rowCode,symbols,bits]
  | cons c cs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp hn
    have missing : (symbols cs f).testBit (f c).val = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨d,hd,eq⟩ := List.mem_map.mp ((test_bits _ _).mp h)
      exact fresh (hi (Fin.ext eq) ▸ hd)
    apply List.mem_flatMap.mpr
    refine ⟨_, ih tail, List.mem_filterMap.mpr ⟨f c, List.mem_finRange _, ?_⟩⟩
    have first : c≠0 ∨ f c=f 0 := by by_cases h : c=0 <;> simp_all
    simp only [first,hf,missing,and_self,if_true,Option.some.injEq]
    rfl

private theorem extend (rs : List Nat) (t : D)
    (absent : (occupied rs).testBit (pos 0 t)=false)
    (children : ∀ r ∈ nextRows (occupied rs) t, Good (r::rs)) : Good rs := by
  intro L data
  obtain ⟨i,ht⟩ := (Finite.surjective_of_injective (L.col_injective 0)) t
  change L.mat i 0 = t at ht
  have space (c : D) : (occupied rs).testBit (pos c (L.mat i c)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨r,hr,hit⟩ := (test_occupied _ _).mp h
    obtain ⟨j,hj⟩ := data r hr
    have eq : j=i := L.col_injective c ((hj _ _).mp hit)
    have first := (hj 0 t).mpr (eq ▸ ht)
    have bad := (test_occupied rs (pos 0 t)).mpr ⟨r,hr,first⟩
    simp_all
  let r := rowCode digits.reverse (L.mat i)
  have hm : r∈nextRows (occupied rs) t := by
    apply List.mem_map.mpr
    refine ⟨(r,symbols digits.reverse (L.mat i)),?_,rfl⟩
    rw [← ht]
    exact generates _ _ (L.row_injective i) space _ (by decide)
  apply children r hm L
  intro a ha
  rcases List.mem_cons.mp ha with eq | old
  · exact ⟨i,eq ▸ agrees_code _⟩
  · exact data a old

private def firstGap (rs : List Nat) : Option D :=
  digits.find? fun t => !(occupied rs).testBit (pos 0 t)

private theorem absent_of_gap {rs t} (h : firstGap rs = some t) :
    (occupied rs).testBit (pos 0 t) = false := by
  simpa using List.find?_some h

-- Three bits encode each of the seven values of a column or symbol map.
private def decode (w : Nat) (x : D) : D :=
  Fin.ofNat 7 ((w >>> (3*x.val)) % 8)

private def permCheck (f : D → D) := symbols digits f == 127

private theorem injective_of_perm {f : D → D} (h : permCheck f = true) :
    Function.Injective f := by
  apply Finite.injective_iff_surjective.mpr
  intro y
  have all : ∀ i : D, (127 : Nat).testBit i.val = true := by decide
  have bit := all y
  rw [← (beq_iff_eq.mp h : symbols digits f = 127)] at bit
  obtain ⟨x,_,eq⟩ := List.mem_map.mp ((test_bits _ _).mp bit)
  exact ⟨x,Fin.ext eq⟩

private def witnessOK (rs : List Nat) (w : Nat) :=
  let col := decode w
  let sym := decode (w >>> 21)
  permCheck col && permCheck sym && digits.all fun x =>
    rs.any fun r => r.testBit (pos 0 x) && r.testBit (pos (col x) (sym x))

private theorem witness_sound {rs w} (pass : witnessOK rs w = true) : Good rs := by
  intro L data
  obtain ⟨both,all⟩ := Bool.and_eq_true_iff.mp pass
  obtain ⟨cols,syms⟩ := Bool.and_eq_true_iff.mp both
  let a (i : D) := L.mat i 0
  have inj : Function.Injective a := L.col_injective 0
  have vals (i : D) : L.mat i (decode w (a i)) = decode (w >>> 21) (a i) := by
    obtain ⟨r,hr,hit⟩ := List.any_eq_true.mp (List.all_eq_true.mp all (a i) (List.mem_finRange _))
    obtain ⟨j,agree⟩ := data r hr
    obtain ⟨h0,h1⟩ := Bool.and_eq_true_iff.mp hit
    have eq : j=i := inj ((agree _ _).mp h0)
    subst j
    exact (agree _ _).mp h1
  refine ⟨fun i => decode w (a i), (injective_of_perm cols).comp inj, ?_⟩
  intro i j h
  change L.mat i (decode w (a i)) = L.mat j (decode w (a j)) at h
  rw [vals i,vals j] at h
  exact inj (injective_of_perm syms h)


-- The witness array is traversed in the same order as the possible rows.
-- A successful traversal checks every completion of the prefix.
private def consume {α : Type} (f : α → Nat → Option Nat) : List α → Nat → Option Nat
  | [], i => some i
  | x::xs, i => (f x i).bind (consume f xs)

private theorem consume_all {α : Type} {f : α → Nat → Option Nat}
    (xs : List α) {i j : Nat} (h : consume f xs i = some j) :
    ∀ x ∈ xs, ∃ a b, f x a = some b := by
  induction xs generalizing i with
  | nil => simp
  | cons y ys ih =>
    cases e : f y i with
    | none => simp [consume,e] at h
    | some k =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | tail
      · exact ⟨i,k,e⟩
      · exact ih (by simpa [consume,e] using h) x tail

-- Eight 42-bit witnesses share one literal. Only the low 42 bits of the
-- selected word are inspected by the column and symbol decoders.
private def witnessWord (proofs : Array Nat) (i : Nat) :=
  (proofs[i/8]?.getD 0) >>> (42*(i%8))

private def completions (proofs : Array Nat) : Nat → List Nat → Nat → Option Nat
  | 0, rs, i => if witnessOK rs (witnessWord proofs i) then some (i+1) else none
  | depth+1, rs, i =>
    match firstGap rs with
    | none => none
    | some t => consume (fun r j => completions proofs depth (r::rs) j)
        (nextRows (occupied rs) t) i

private theorem completions_sound (proofs : Array Nat) (depth : Nat)
    (rs : List Nat) (i j : Nat) (pass : completions proofs depth rs i = some j) :
    Good rs := by
  induction depth generalizing rs i j with
  | zero =>
    simp only [completions] at pass
    split at pass
    · exact witness_sound (by assumption)
    · contradiction
  | succ depth ih =>
    cases e : firstGap rs with
    | none => simp [completions,e] at pass
    | some t =>
      apply extend rs t (absent_of_gap e)
      have h := consume_all (f := fun r j => completions proofs depth (r::rs) j)
        (nextRows (occupied rs) t) (by simpa only [completions,e] using pass)
      intro r hr
      obtain ⟨a,b,hb⟩ := h r hr
      exact ih _ _ _ hb

private def choices (rs : List Nat) (t : D) := nextRows (occupied rs) t

private def Span (rs : List Nat) (t : D) (a b : Nat) : Prop :=
  ∀ (i : Nat), (a ≤ i) → (i < b) → ∀ r, (choices rs t)[i]? = some r → Good (r::rs)

private theorem batch (rs : List Nat) (t : D) (a b : Nat) (ws : Array Nat) (last : Nat)
    (pass : consume (fun r i => completions ws 3 (r::rs) i)
      (((choices rs t).drop a).take (b-a)) 0 = some last) : Span rs t a b := by
  intro i lo hi r atIndex
  have inside : (((choices rs t).drop a).take (b-a))[i-a]? = some r := by
    rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,show a+(i-a)=i by omega]
    exact atIndex
  obtain ⟨u,v,h⟩ := consume_all _ pass r (List.mem_of_getElem? inside)
  exact completions_sound ws 3 (r::rs) u v h

private theorem joinSpan {rs t a b c} (lower : Span rs t a b) (upper : Span rs t b c) :
    Span rs t a c := by
  intro i lo hi
  by_cases side : i<b
  · exact lower i lo side
  · exact upper i (by omega) hi

private theorem fullSpan {rs t endAt} (gap : firstGap rs = some t)
    (bound : (choices rs t).length ≤ endAt) (ok : Span rs t 0 endAt) : Good rs := by
  apply extend rs t (absent_of_gap gap)
  intro r hr
  obtain ⟨i,eq⟩ := List.mem_iff_getElem?.mp (show r∈choices rs t from hr)
  have within : i < (choices rs t).length := by
    by_contra! h
    simp [List.getElem?_eq_none h] at eq
  exact ok i (Nat.zero_le _) (lt_of_lt_of_le within bound) r eq

-- A route relabels columns and symbols by independent permutations.
private def sameRow (c s : D → D) (old new : Nat) :=
  digits.all fun i => digits.all fun j =>
    new.testBit (pos (c i) (s j)) == old.testBit (pos i j)

private def routeOK (rs target : List Nat) (w : Nat) :=
  let c := decode w
  let s := decode (w >>> 21)
  permCheck c && permCheck s && target.all fun q => rs.any fun r => sameRow c s r q

private theorem route_sound {rs target : List Nat} {w : Nat}
    (h : routeOK rs target w=true) (next : Good target) : Good rs := by
  intro L rows
  obtain ⟨both,all⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨pc,ps⟩ := Bool.and_eq_true_iff.mp both
  let c : D ≃ D := Equiv.ofBijective (decode w)
    ⟨injective_of_perm pc, Finite.surjective_of_injective (injective_of_perm pc)⟩
  let s : D ≃ D := Equiv.ofBijective (decode (w >>> 21))
    ⟨injective_of_perm ps, Finite.surjective_of_injective (injective_of_perm ps)⟩
  let M : LatinSquare 7 := {
    mat := fun i j => s (L.mat i (c.symm j))
    row_injective := fun i => s.injective.comp ((L.row_injective i).comp c.symm.injective)
    col_injective := fun j => s.injective.comp (L.col_injective (c.symm j)) }
  have mt : Matches M target := by
    intro q hq
    obtain ⟨r,hr,eq⟩ := List.any_eq_true.mp (List.all_eq_true.mp all q hq)
    obtain ⟨i,agree⟩ := rows r hr
    refine ⟨i,?_⟩
    intro u v
    have bits := List.all_eq_true.mp (List.all_eq_true.mp eq (c.symm u) (List.mem_finRange _))
      (s.symm v) (List.mem_finRange _)
    have e : q.testBit (pos (c (c.symm u)) (s (s.symm v))) =
        r.testBit (pos (c.symm u) (s.symm v)) := beq_iff_eq.mp bits
    rw [c.apply_symm_apply,s.apply_symm_apply] at e
    rw [e,agree]
    change L.mat i (c.symm u) = s.symm v ↔ s (L.mat i (c.symm u)) = v
    exact s.eq_symm_apply
  obtain ⟨f,hc,hs⟩ := next M mt
  refine ⟨fun i => c.symm (f i), c.symm.injective.comp hc,?_⟩
  intro i j eq
  exact hs (congrArg s eq)

private def routes (rs : List Nat) (targets : List (List Nat)) (words : Array Nat) :
    List Nat → Nat → Bool
  | [], _ => true
  | r::rest, i =>
    let w := words[i]?.getD 0
    match targets[w >>> 42]? with
    | none => false
    | some target => routeOK (r::rs) target w && routes rs targets words rest (i+1)

private theorem routes_good {rs targets words} (known : ∀ p∈targets, Good p)
    (xs : List Nat) (i : Nat) (pass : routes rs targets words xs i = true) :
    ∀ r∈xs, Good (r::rs) := by
  induction xs generalizing i with
  | nil => simp
  | cons a tail ih =>
    simp only [routes] at pass
    split at pass
    · contradiction
    · rename_i t ht
      obtain ⟨one,rest⟩ := Bool.and_eq_true_iff.mp pass
      intro r hr
      rcases List.mem_cons.mp hr with rfl | mem
      · exact route_sound one (known t (List.mem_of_getElem? ht))
      · exact ih _ rest r mem

private theorem routeLevel (rs : List Nat) (targets : List (List Nat)) (words : Array Nat)
    (known : ∀ p∈targets, Good p) (t : D) (gap : firstGap rs = some t)
    (pass : routes rs targets words (nextRows (occupied rs) t) 0 = true) : Good rs :=
  extend rs t (absent_of_gap gap) (routes_good known _ 0 pass)

private abbrev p3_0 : List Nat := [282578800148737,72576365887618,141304428250116]
private abbrev p3_1 : List Nat := [282578800148737,72576365887618,140823421273092]
private abbrev p3_2 : List Nat := [282578800148737,72576365887618,141304426169348]
private abbrev p3_3 : List Nat := [282578800148737,72576365887618,140789061551108]
private abbrev p3_4 : List Nat := [282578800148737,72576365887618,8847700001796]
private abbrev p3_5 : List Nat := [282578800148737,72576365887618,4484013229060]
private abbrev p3_6 : List Nat := [282578800148737,72576365887618,35270338562052]
private abbrev p3_7 : List Nat := [282578800148737,72576365887618,9088217925636]
private abbrev p3_8 : List Nat := [282578800148737,72576365887618,35235978840068]
private abbrev p3_9 : List Nat := [282578800148737,72576365887618,4690171430916]
private abbrev p3_10 : List Nat := [282578800148737,72576365887618,141012768950276]
private abbrev p3_11 : List Nat := [282578800148737,72576365887618,140774129829892]
private abbrev p3_12 : List Nat := [282578800148737,72576365887618,35253494745092]
private abbrev p3_13 : List Nat := [282578800148737,72576365887618,9071374108676]
private abbrev p3_14 : List Nat := [282578800148737,72576365887618,35219403442180]
private abbrev p3_15 : List Nat := [282578800148737,72576365887618,4673596033028]
private abbrev p3_16 : List Nat := [282578800148737,72576365887618,35253428160516]
private abbrev p3_17 : List Nat := [282578800148737,72576365887618,9071307524100]
private abbrev p3_18 : List Nat := [282578800148737,72576365887618,35219336857604]
private abbrev p3_19 : List Nat := [282578800148737,72576365887618,4673529448452]
private abbrev p3_20 : List Nat := [282578800148737,19799832920194,141304426169348]
private abbrev p3_21 : List Nat := [282578800148737,19799832920194,70420350927876]
private abbrev p3_22 : List Nat := [282578800148737,19799832920194,140823390061572]
private abbrev p3_23 : List Nat := [282578800148737,19799832920194,140789032420356]
private abbrev p3_24 : List Nat := [282578800148737,19799832920194,8847700001796]
private abbrev p3_25 : List Nat := [282578800148737,19799832920194,4484013229060]
private abbrev p3_26 : List Nat := [282578800148737,19799832920194,140806610748420]
private abbrev p3_27 : List Nat := [282578800148737,19799832920194,140772519445508]
private abbrev p3_28 : List Nat := [282578800148737,19799832920194,70454646146052]
private abbrev p3_29 : List Nat := [282578800148737,19799832920194,9363031327748]
private abbrev p3_30 : List Nat := [282578800148737,19799832920194,70437866832900]
private abbrev p3_31 : List Nat := [282578800148737,19799832920194,35270338562052]
private abbrev p3_32 : List Nat := [282578800148737,19799832920194,140808489551876]
private abbrev p3_33 : List Nat := [282578800148737,19799832920194,35235978840068]
private abbrev p3_34 : List Nat := [282578800148737,19799832920194,141012768950276]
private abbrev p3_35 : List Nat := [282578800148737,19799832920194,140774129829892]
private abbrev p3_36 : List Nat := [282578800148737,19799832920194,35253494745092]
private abbrev p3_37 : List Nat := [282578800148737,19799832920194,35253428160516]
private abbrev p3_38 : List Nat := [282578800148737,37392018850306,141304428363908]
private abbrev p3_39 : List Nat := [282578800148737,37392018850306,8847700001796]
private abbrev p3_40 : List Nat := [282578800148737,37392018850306,4484013229060]
private abbrev p3_41 : List Nat := [282578800148737,37392018850306,9363031327748]
private abbrev p3_42 : List Nat := [282578800148737,37392018850306,141287784186884]
private abbrev p3_43 : List Nat := [282578800148737,37392018850306,9346185430020]
private abbrev p3_44 : List Nat := [282578800148737,37392018850306,17643730112520]
private abbrev p3_45 : List Nat := [282578800148737,6605693387266,141029550588036]
private abbrev p3_46 : List Nat := [282578800148737,6605693387266,35270338805892]
private abbrev p3_47 : List Nat := [282578800148737,6605693387266,35751312490628]
private abbrev p3_48 : List Nat := [282578800148737,6605693387266,140823390061572]
private abbrev p3_49 : List Nat := [282578800148737,6605693387266,8847700001796]
private abbrev p3_50 : List Nat := [282578800148737,6605693387266,70437866832900]
private abbrev p3_51 : List Nat := [282578800148737,6605693387266,70403708945412]
private abbrev p3_52 : List Nat := [282578800148737,6605693387266,141029548263428]
private abbrev p3_53 : List Nat := [282578800148737,6605693387266,35270274058244]
private abbrev p3_54 : List Nat := [282578800148737,6605693387266,35734401585156]

private abbrev p2_0 : List Nat := [282578800148737,72576365887618]
private abbrev p2_1 : List Nat := [282578800148737,19799832920194]
private abbrev p2_2 : List Nat := [282578800148737,37392018850306]
private abbrev p2_3 : List Nat := [282578800148737,6605693387266]

private abbrev p1_0 : List Nat := [282578800148737]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_0s0 : Span p3_0 3 0 5 :=
  batch _ _ _ _ #[
0xd1a22853337466841cb8ad18a8856667468521dca1c11ae066e53046b819b94c9d220b933014ee8d11ac,0xd19a1072e2b468521dca1d1a148772871702a2629dd19a1072e2b466841cb8ad1a14877287442b21d991,0xcc4350b8b8b210ba262d5d0aa1852e2f42a8614b8bcea1088eac7210ba262d5d0aa1852e2f405d41dc62,0xd017507718ab80e4708ead017507718b405d41dc62ce8310a63c9182e6509abd1a1487aa873302a3429d,0xd18a8852e670aa3223d51c8d8189952f466841d98ac9d220b933282f445d132c9d220b9333035a83545c,0xc2a8c88f5470aa3223d51d10ac872e46e0a1654d43d087507a98b442b21cb91d10ac872e47442b21cb91,0xca88c88f5471425611d63cea1088eac72a23223d51c509584758f1425611d63ca88c88f5471425611d63,0xc889582b58f222560ad63c889582b58f222560ad63d087507718b466841d98ad087507718b421d41dc62,0xd18a8852e67462a214b99cea108ae2c414ee8d11acce98108f52b3302a3429dd016a8531773a60423d4a,0xc456a0b91733a60423d4ace98108f52b1a1c423a72c427284e1d7109ca13875c427284e1d7109ca13875] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_0s1 : Span p3_0 3 5 10 :=
  batch _ _ _ _ #[
0xc11ae066e53046b819b94c509584758f1425611d63d086a8531771425611d63c11ae066e531425611d63,0xc889582b58f222560ad63c889582b58f222560ad63c427284e1d7109ca13875c427284e1d7109ca13875,0xd1a22853337466841cb8ad18a8856667468521dca1c11ae066e53046b819b94c296a0ca9733a8882accc,0xc81ae02ee53206b80bb94c81ae02ee53206b80bb94d1a228533374468614b8bd11a1852e2f4468614b8b,0xcc4350b8b8b2a60622d4bd0aa1852e2f42a8614b8bc296a0ab1732a60622d4bd0aa1852e2f405d41dc62,0x2a0b9a226af0a5a82ac5cc5c0a898a7742a8614b8bc54158b8a8f462a2159995033715439b1a84621ab3,0xd18a8852e67035c425672c9d10895ac7466841d98ac686a0ca9733a8882accca438b15057b3a8882accc,0xd18a8852e673302a2629db9a06177213035c425672d18a8852e67462a214b99d016a85a177446861598b,0xc686a0ab1731425611d63ce88888b56727442256b1c509584758f1425611d63a0bd11744cb1425611d63,0xc0d710959cb1a1a82ac5cce88888b567035c425672c5c0a8d0a77150562e2a35033715439b27442256b1] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_0s2 : Span p3_0 3 10 15 :=
  batch _ _ _ _ #[
0xd18a8852e67462a214b99c0d710959cb035c425672b19c81574633302a3429dd016a85317690e2c5415e,0xd18a8852e67150562e2a3c142e898b574688a168cdd18a8852e67405aa14c5dd016a853177405aa14c5d,0xc11ae066e53046b819b94c509584758f1425611d63d086a8531771425611d63c11ae066e531425611d63,0xc81ae02ee53206b80bb94c81ae02ee53206b80bb94c0a7286a1d7029ca1a875c0a7286a1d74688a168cd,0xd1a14877287468521dca1cc531094bca560e4468ead19a1072e2b468521dca1cc531094bcb2708a264cd,0xc81ae02ee53206b80bb94c81ae02ee53206b80bb9440bba1686b3466841cb8ac852e0b8b53111aa2645d,0xcea1088eac72a23233951d017507718b405d41dc62c8d11894acf3a84223ab1843ca958477405d41dc62,0x843b918c6ab0a5a82ac5cd1a1487aa873508a264cdd190a833277405d41dc62cea1088eac7111aa2645d,0xc852e0b8b53442b21cb91d022e833357174282e29cc2a8c88f547466841d98ab8285a3350f23446252b3,0xd087507a98b442b21cb91d10ac872e47442b21cb91548d190accf3a6043394ac2a8c88f5470aa3223d51] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_0s3 : Span p3_0 3 15 20 :=
  batch _ _ _ _ #[
0xd102e833357222560ad63d183503738b222560ad63c509584758f1425611d63c509584758f1425611d63,0xd087507718b466841d98ad087507718b421d41dc62ca88c88f5472a23223d51c889582b58f222560ad63,0xd111583728f444560dca3ce98108f52b1a1c423a72cea108ae2c7214b82e2d4c1d31094bcb3a60423d4a,0x843b918c6ab3508a264cdc1d31094bcb174282e29cd190a8332763a31473b02c0a7286a1d73a60423d4a,0xc889582b58f222560ad63c0a7286a1d7222560ad63c509584758f1425611d63c509584758f1425611d63,0xc81ae02ee53206b80bb94c81ae02ee53206b80bb94d111583aa8f222560ad63d183503738b460d40dce2,0xd1a228533374468614b8bd11a1852e2f4468614b8bd1a22853337462a215999c11ae066e53046b819b94,0xcea220ab333074c42c2f2c81ae02ee53206b80bb94c296a0ca973206b80bb94cea220ab333206b80bb94,0xcd4148b9a87462a215999cea1088eac65446644cab872ac18ee4342a8614b8bd0aa1852e2f42a8614b8b,0xd190a8332774642a0cc9dcd4148b9a870a5a82ac5cccca1095e2b031d435662d102e83a35742a8614b8b] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_0s4 : Span p3_0 3 20 25 :=
  batch _ _ _ _ #[
0xd18a8852e67462a214b99d016a85a177446861598bd18a8852e665642c4589eccca1095e2b23446252b3,0xcea220ab333462a214b995418f10e55b074c4252f2c55118b0acf074c4252f2d0a1583728f3a8882accc,0xc889582b58f222560ad63c889582b58f222560ad63c84ac895e473a22222d59c686a0ab17323446252b3,0xc8d11894acf350522e6a1d102e833357074c4252f2d102e833357440ba0ccd5ce88888b564a0ee88b1ac,0xd18a8852e67405aa14c5dd016a853177405aa14c5dd18a8852e67462a214b99c44750b998b405aa14c5d,0xd190a833277462a214b99c427284e1d7109ca13875283ba22c6b3074c4252f2d111583728f4688a168cd,0xc889582b58f222560ad63c889582b58f222560ad63c11ae066e53046b819b94d086a853177046b819b94,0xc427284e1d7206b80bb94d183503738b206b80bb94c427284e1d7109ca13875c81ae02ee53206b80bb94,0xd1a14877287468521dca1cc4a8895667115c425672c11ae066e53046b819b94c11ae066e53046b819b94,0xca911886acf2a44621ab3ccd81099d2b2a44621ab3ca911886acf466841cb8a40bba1686b3111aa2645d] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_0s5 : Span p3_0 3 25 30 :=
  batch _ _ _ _ #[
0xcc4a88956671a84621ab3d017507718b405d41dc62d190a833274c0f2a8e11dca98188b52f312a225599,0xd190a8332774642a0cc9d460b99426af440ba0e8d5d190a833277405d41dc62c54a18b162f1a84621ab3,0xce831086bcb442b21cb91d022e8333573a0c421af2d0a1583728f408ba0ccd5d022e833357408ba0ccd5,0x5418f10e55b3a0c421af2c1ca8895667428560dca3c858c899d472163226751c5d810d1d2aa0ce88e0ec,0xd102e833357222560ad63d183503738b222560ad63d0a1583aa8f460d40dce2d183503738b4642a0e89d,0xc8ca189562f440ba0ccd5d102e833357440ba0ccd5c5d810d1d2902ee85a1acc889582b58f222560ad63,0xd111583728f444560dca3ce831086bcb152862558bd190a8332774642a0cc9dd022e83a357460d40eae2,0xd190a833277109ca13875c427284e1d7444560dca3d190a8332771a846298b3c0a7286a1d73a0c421af2,0xc889582b58f222560ad63c0a7286a1d7222560ad63c11ae066e53046b819b94c11ae066e53460d40dce2,0xc427284e1d7460d40dce2c427284e1d7109ca13875d111583aa8f222560ad63d183503738b460d40dce2] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_0s6 : Span p3_0 3 30 35 :=
  batch _ _ _ _ #[
0xca911886acf3162226559c5ca1095e2b274882e4ccc84ac895e46e2a305cd50c9d220b9333212b225791,0xca911886acf2a44621ab3c81ae02ee53206b80bb94460b99426af206b80bb94ca911886acf206b80bb94,0xd190a8332773162226559421ce9634571a84621ab3d190a8332773a84223ab1aa1199832af212b225791,0xd190a8332774642a0cc9dc6a11886acf1a84621ab3ccca1095e2b1a84621ab3d102e83a35742a8614b8b,0x548d190accf172842c78ace831086bcb408ba0ccd5d0a1583728f408ba0ccd5d022e833357408ba0ccd5,0xc8d8189952f462a214b99ce831086bcb2a446298b3ce831086bca540bc44ad6d0a1583728f0762226559,0xc84ac895e47212b225791d102e833357460d40dce2d0a1583aa8f460d40dce2d183503738b4642a0e89d,0x5418f10e55b354882e4ccd102e8333565642c4589ed102e833357440ba0ccd5ccca1095e2b0762226559,0xd190a833277029ca1a875d111583728f444560dca3d190a8332774642a0cc9dd022e83a357460d40eae2,0xd190a833277462a214b99c427284e1d7109ca13875ce831086bcb1a846298b3d111583728f4688a168cd] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_0s7 : Span p3_0 3 35 36 :=
  batch _ _ _ _ #[
0xd111583aa8f460d40dce2d183503738b029ca1a875c509584758f1425611d63c509584758f460d40dce2,0xc427284e1d7206b80bb94d183503738b206b80bb94c427284e1d7109ca13875c81ae02ee53206b80bb94] 16 (by decide +kernel)

private theorem p3_0Good : Good p3_0 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan (joinSpan p3_0s0 p3_0s1) (joinSpan p3_0s2 p3_0s3)) (joinSpan (joinSpan p3_0s4 p3_0s5) (joinSpan p3_0s6 p3_0s7)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_1s0 : Span p3_1 3 0 5 :=
  batch _ _ _ _ #[
0xd0235858d8e2c2966a983d18a8856667052b21cb91d18a8856667462a2159998531717429b212b223b91,0xd190a8332774642a0cc9dd190a8332774642a0cc9dc447507a98b052b21cb91c42ae074e53052b21cb91,0xc456a0d5173052b21cb91cca1288cad7446861598bd11a185662f446861598bc0d6a0b917302a3a262d5,0xc5a12870ad72328622b8bd190a83a2774642a0e89dc8ca188ae2f10a3a342d5d190a83a2774642a0e89d,0xd0235858d8f408d616363c5a12870ad7115c425672d18a8856667462a215999c42ae074e53052b21cb91,0xd190a8332774642a0cc9dc54a1852e2f1528614b8bc0a8e8d0b57212b223b91d111583728f444560dca3,0xc5a12870ad72328622b8bc42ae074e53052b21cb91c8ca188ae2f2a446298b3d11a185662f446861598b,0xc2a31888dcf4642a0e89dc9d10895ac74642a0e89dc84ac88ee470a8c622373c54a1852e2f1528614b8b,0xc1c35078d8b42a8614b8bd0aa1852e2f42a8614b8bcea1088eac74445629ca3d0aa1852e2f070d41e362,0x8e858ace0a6e0ca85615ccea1088eac55c0c6429735703190a5cf070d41e362] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_1s1 : Span p3_1 3 5 10 :=
  batch _ _ _ _ #[
0xc5a82853337405aa1685dd11a185662f462a214b99ccc0a898a772a446298b3c50ae066e52666a08d998,0xcea1088eac65632285d19c818e83a3572063a0e8d5c818e83a357214c60c573c85318315cf462a214b99,0xd08750af18b070d41e362d08750af18b3302a2629dd103584758e505ac8585ed103584758f440d611d63,0xcc4350ccd8b3a42829c9cc50ae066e534445629ca3ca82e02f5532a0b80bd54ca82e02f5531702a3429d,0xc85318315cf214c60c573c85318315cf462a214b99d016a853177405aa14c5dc5a8285a3355223c44ad6,0xd0aa1852e2f42a8614b8bd11158a728f27442256b1d0aa1852e2f070d41e362d0aa18aa62f029ca1a875,0xca83182a5cf2a0c60a973ca83182a5cf2a0c60a973ca83182a5cf3a42829c9cd18a8856667070d41e362,0xcc4350ccd8b462a214b99d016a85a177405aa1685dd11a185662f446861598bc50ae066e5327442256b1,0xc88ae02ee53222b80bb94c88ae02ee53222b80bb94c5a828533373302a2629d] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_1s2 : Span p3_1 3 10 15 :=
  batch _ _ _ _ #[
0xcd5108b1ac727442256b1d103584758ebc81873a84d103584758f440d611d63ccc0a898a7727442256b1,0xc50ae066e534445629ca3c5c0a8d0a77421d42bc62cd5108b1ac6c0cac5415ecc4350ccd8b1702a3429d,0xc427284e1d7109ca13875c427284e1d7462a214b99d18a8852e67405aa14c5dd016a853177405aa14c5d,0xc8d118b0acf2660a264cdc8d118b0acf2660a264cdc88ae02ee53222b80bb94c88ae02ee53222b80bb94,0xc5ca1072e2b172841cb8acc53108cdcb205ca23475d086a85a177421aa1685dd18a8856667462a215999,0xd103584758f440d611d63d103584758f440d611d63c1d31070dcb045ca1c475c11728711d7045ca1c475,0xc5ca1072e2b234462c2b3cc53108cdcb214b833354d103584758f440d611d63d103584758f440d611d63,0xcea1088eac73a84223ab1d11158a728f3a84223ab1c1d31070dcb054b81e354c152e078d5315446252b3,0x5988695a3170a5a82ac5cca83182a5cf4642a0cc9dc1d31070dcb3a84223ab1c843583958d6621a568c5,0xca83182a5cf2a0c60a973] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_1s3 : Span p3_1 3 15 19 :=
  batch _ _ _ _ #[
0xcca8288b337210d60e563c843583958f4642a0e89dd190a83a27732a0a22ccdcca8288b3365642c4589e,0xc0c6a899177314c423372c1ca8895667314c423372c1ca8895667074c41c372c843583958f072a225599,0xcea1088eac65642c4589ec1d31070dcb1a1a832a5cc88ae02ee534642a0e89dc88ae02ee53334282e29c,0xc1ca8895667074c41c372ca82e02f5534642a0e89dca82e02f5530a5c42b872ca82e02f553074c41c372,0xc818e833357444560dca3c818e8333574445629ca3c1d31070dcb312a225599c152e078d53428560eaa3,0xcc53108cdcb4642a0cc9dd190a833277210d60e563c843583958d5234642b33c0a7286a1d72063a0ccd5,0xc152e078d53222b80bb94d111583728f314c423372c1ca8895667314c423372c1ca8895667444560dca3,0x9502f111d5b446861598bc5ca1072e2b172841cb8ac118e8c63565642c4589ed190a833277222b80bb94,0xc50728519d72063a0e8d5d1835039d8a540bc44756d1835039d8b446861598bc818e83a3572063a0e8d5,0xc5a828533372063a0e8d5] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_1s4 : Span p3_1 3 19 24 :=
  batch _ _ _ _ #[
0xc5511894acf3a8422b8b1c818e8333572063a0ccd5c447507a98b111d41ea62c8d118b0acf0463a21cd5,0xd190a83327715446252b3d190a833277031d433a62ccca108ee2b2063a0ccd5d111583728f2063a0ccd5,0xc9912831ad7462a215999d18a8856667206b80d794d086a85a177462a215999cd112885ad71423a318d5,0xc5a8285333716a0a14ccdca83182a5cf2a0c60a973c54a1852e2f2a0c60a973c84ac88ee472a0c60a973,0xca82e02f5532a0b80bd54ca82e02f5532a0b80bd54d103584758f440d611d63d103584758f440d611d63,0xc427284e1d72644a0c6b5c427284e1d72223a0ccd5c427284e1d7109ca13875c888e8333572223a0ccd5,0xc5ca1072e2b031d41ea62c447507a98b1423a318d5c152e0c5d532660a264cdc508e8c63572660a264cd,0xc852e039d53214b80e754c852e039d53115c425672c888e83a3572223a0e8d5c888e83a35735442256b1,0xc5ca1072e2b172841cb8ac0c7507a98b031d41ea62a43d11744cb1505631aa3a444f17285b031d41ea62,0x80bb918c6ab3328423b8a832a59aa60f3328423b8ac8c1583aa8f2223a0ccd5c888e8333572223a0ccd5] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_1s5 : Span p3_1 3 24 28 :=
  batch _ _ _ _ #[
0xc6a11886acd6665055ce0c843583958f1a84621ab3cc4a88956670a5a82ac5cc9d10895ac7050d631563,0xc2a2e067553142b819b94d190a8332755c0c642973cc4a889566727442256b1d01750af18b4642a0cc9d,0xc843583958f072a225599c2a2e067553210d60e563c843583958f4642a0e89dd190a83a27732a0a22ccd,0xc88ae02ee5316a0a14ccdc5a828533372a446298b3c1ca88956665642c4589ec1ca88956670a8b819d54,0xc446a8d1177428560eaa3d0a1583aa8f428560eaa3c88ae02ee53072a225599c88ae02ee534642a0e89d,0xc9d10895ac7428560eaa3c1ca88956655c0b843d549511991a2af4642a0e89dcc4a889566727442256b1,0xc0a7286a1d72063a0ccd5c818e833357444560dca3c818e833357142b819b94d08750af18b4642a0e89d,0xc427284e1d7444560dca3c427284e1d74642a0cc9dd190a833277210d60e563c843583958d5234642b33,0xd190a833277222b80bb9445dd0155cc3222b80bb94c88ae02ee53109ca13875c427284e1d7109ca13875] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_1s6 : Span p3_1 3 28 32 :=
  batch _ _ _ _ #[
0xc5ca1072e2b111d41ea62d1835039d8b460d40e762c5a8285333716a0a14ccdc118e8c63570a5c42b872,0xc5a828533372063a0e8d5c50728519d72063a0e8d5d1835039d8b115a83545cd1835039d8b214c60c573,0xd190a8332774642a0cc9dce831085dcb444560dca398266a7a117054c621573d1835039d8b460d40e762,0xd190a83327660cd45e162d190a8332773a42829c9cce831085dcb214c60c573d111583728f214c60c573,0xc2a2e0675530a8b819d54c2a2e0675530a8b819d54c5a82853337046b829794cd112885ad69732056b18,0xc5a8285333716a0a14ccdc9912831ad72644a0c6b5c54a1852e2f2223a0e8d5c84ac88ee47111d433a62,0xc0a7286a1d7029ca1a875c0a7286a1d7029ca1a875c15318855cf054c621573c5a8285a3373444a216b5,0xc427284e1d72644a0c6b5c427284e1d72223a0ccd5c427284e1d7109ca13875c888e8333572223a0ccd5] 64 (by decide +kernel)

private theorem p3_1Good : Good p3_1 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_1s0 (joinSpan p3_1s1 p3_1s2)) (joinSpan (joinSpan p3_1s3 p3_1s4) (joinSpan p3_1s5 p3_1s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_2s0 : Span p3_2 3 0 5 :=
  batch _ _ _ _ #[
0xd086a85a177466841cb8ad18a8856667405d41ea62b02c595740f3a8882bc8cc456a0d51733a8882bc8c,0xd19a1072e2b466841cb8ac0d6a0b9173442b21d991d19a1072e2b405d41ea62d017507a98b3a44421af2,0xcea220cea330465611d63d0aa1852e2f42a8614b8bc119584758f0465611d63d0aa1852e2f0465611d63,0xc819582b58f206560ad63c819582b58f206560ad63d017507718b310aa2629dd017507718b405d41dc62,0xd18a8852e674688a1cc8dd1a14857387466841d98ac50ae066e53142b819b94b0acc1774433a8882bc8c,0xd1a22873237442b21cb91d10ac872e47442b21cb91d1a228732374688a1cc8dd10ac872e472a0c621ab3,0xccc150b8b8b2a23223d51c29710ae1cb2a23223d51d02ac872e4740ab21cb91d1a1485ab8740ab21cb91,0xd087507718b466841d98ad087507718b421d41dc62ce9110a63c9086e6509abc5c150b8b8b40ab21cb91,0xd18a8852e67462a214b99c119584758f0465611d63c50ae066e530465611d63d016a8531770465611d63,0xc819582b58f206560ad63c819582b58f206560ad63c0a7284e1d7029ca13875c0a7284e1d7029ca13875] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_2s1 : Span p3_2 3 5 10 :=
  batch _ _ _ _ #[
0xc297108e9cb0a5c423a72d19a1072e2b466841cb8ad086a85317740ab21d991c0d6a0b9173310aa3429d,0xd19a1072e2b050d62e2a3d1a2287a2374688a1e88dc0a7284e1d7029ca13875c0a7284e1d7029ca13875,0xd086a85a177466841cb8ad18a8856667405d41ea62c9d220b9a330a5a832a5cc9d220b9a3282e2c5415e,0xc6a8188b52f4468614b8bd11a1852e2f4468614b8bd086a85a177421aa1685dd11a1852e2f050d6352a3,0xca98188b52f0465611d63d0aa1852e2f42a8614b8bc119584758f0465611d63d0aa1852e2f0465611d63,0xc45710959cb462a215999d1a1485ab874685216ae1cd5220b9a33050d62e2a3d1a1485ab8742a8614b8b,0xd18a8852e674688a1cc8dd1a14857387466841d98ac50ae066e53142b819b94c9d220b9a331a1a832a5c,0xc88ae02ee53222b80bb94c88ae02ee53222b80bb94d18a8852e674685215ce1d1a14857387274882e68c,0xccc150b8b8b2303a262d5cea1088abc72303a262d5d02ac872e4740ab21cb91d1a1485ab8740ab21cb91,0xc158c899d470563226751d1a1485ab873a84222af1c14358b8a8f336042674ad1a1485ab874685216ae1] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_2s2 : Span p3_2 3 10 15 :=
  batch _ _ _ _ #[
0xd18a8852e67462a214b99c119584758f0465611d63c50ae066e530465611d63d016a8531770465611d63,0xc88ae02ee53222b80bb94c88ae02ee53222b80bb94d18a8852e67109ca1a875c427286a1d7109ca1a875,0xcea108aa3c690f445d132d19a1072e2b466841cb8ad086a85317740ab21d991ce88888b567310aa3429d,0xc158c899d473a22222d59c540e898b573a22222d59c427286a1d7421aa14c5dd086a853177421aa14c5d,0xc8d0e0b8b5317444252f2d0a0e833357442b21d991d19a1072e2b405d41ea62cc4a8895667214c6252b3,0xd19a1072e2b405d41ea62d017507a98b1aa0622d4bcea220af233072a22c599d19a1072e2b466841cb8a,0xd110e833357206560ad63d191503738b206560ad63c119584758f0465611d63c119584758f0465611d63,0xd017507718b17444252f2d017507718b405d41dc62c8ca189562f232862558bc819582b58f206560ad63,0xd10ac872e47442b21cb91ccd11094bcb442b21cb91d1a22873237466841d98accd11094bcb232862558b,0xc88ae02ee53222b80bb94c88ae02ee53222b80bb94cea220af2334688a1cc8dc8d0e0b8b530aa3223d51] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_2s3 : Span p3_2 3 15 20 :=
  batch _ _ _ _ #[
0xccd11094bcb23438352d4d087507718b421d41dc62ca88c88f54740ab21cb91d02ac872e4740ab21cb91,0xcd4148b93871a1a82ac5c950399132af40ab21cb91d182a833277421d41dc62c29710ae1cb466841d98a,0xc819582b58f206560ad63c427286a1d7206560ad63c119584758f0465611d63c119584758f0465611d63,0xc88ae02ee53222b80bb94c88ae02ee53222b80bb94d103583aa8f206560ad63d191503738b464540dce2,0xd103583728f440d60dca3d1a2287a2374688a1e88dd19a1072e2b466841cb8ad02ac87664717444252f2,0xd19a1072e2b3a22222d59c5d11094bcb4688a1e88dd182a833277466841cb8ac427286a1d610f2a7211d,0xd086a85a177421aa1685dd11a1852e2f074a82e29cd086a85a177462a215999c296a0ca973214c6252b3,0xcc52a0b8a731aa0622d4b5488f10e55b1aa0622d4bd11a1852e2f4468614b8bd023583728f4468614b8b,0xc819582b58f206560ad63c819582b58f206560ad63ca98188b52f42a8614b8bd0aa1852e2f42a8614b8b,0xca98188b52e5646444cead110e833357462a215999d110e8333574443a0ccd5d1a1485ab874685216ae1] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_2s4 : Span p3_2 3 20 25 :=
  batch _ _ _ _ #[
0xd18a8852e674685215ce1d1a148573870aa3223d51d18a8852e674685215ce1c50ae066e53142b819b94,0xcc52a0b8a73174442c2f2c88ae02ee53222b80bb94c686a0ca973222b80bb94c9c22899a37222b80bb94,0x8e8c51af40b3a6043394ad1a1485ab874685216ae1ca9818ca52f3a84222af1c0c750b998b4685216ae1,0xd182a833277460aa0cc9dc44750d598b1a1a82ac5ccea1088abc74685216ae1d110e83a3573a84222af1,0xc819582b58f206560ad63c819582b58f206560ad63d18a8852e67462a214b99c50ae066e53405aa14c5d,0xc0a7284e1d7222b80bb94d191503738b222b80bb94c0a7284e1d7029ca13875c88ae02ee53222b80bb94,0xc0c750b998b421aa14c5dd086a853177421aa14c5dcea108aa3c7234382e2d4d086a8531773a22222d59,0xd182a8332773a8422a8f1c0a7284e1d7029ca13875ce88888b56717444252f2d103583728f3a22222d59,0xce911086bca5443c44ad6d0a0e833357442b21d991d023583728f4283a0ccd5d0a0e8333574283a0ccd5,0xc858c899d473a44421af2c446a899177408d60dca3541d190accf072a22c599d19a1072e2b466841cb8a] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_2s5 : Span p3_2 3 25 30 :=
  batch _ _ _ _ #[
0xd110e833357206560ad63d191503738b206560ad63d023583aa8f464540dce2d191503738b460aa0e89d,0x5488f10e55b4443a0ccd5d110e8333574443a0ccd5c8ca189562f232862558bc819582b58f206560ad63,0xd10ac872e47442b21cb91c9c148b9387442b21cb91c50ae066e53142b819b94c50ae066e53142b819b94,0xca831886acf2a0c621ab3421b99426af2a0c621ab3ca831886acf4688a1cc8dccd81099d2b072a225599,0x460ce9634570a8c621ab3d087507718b421d41dc62d182a8332773a84222af1aa0399832af3a84222af1,0xd182a833277460aa0cc9dcc4a88956674443a0e8d5d182a833277421d41dc62ccd81099d2b466841d98a,0xc819582b58f206560ad63c427286a1d7206560ad63c50ae066e53142b819b94d191503738b142b819b94,0xc0a7284e1d7464540dce2c0a7284e1d7029ca13875d103583aa8f206560ad63d191503738b464540dce2,0xd103583728f440d60dca3d1a2287a2374688a1e88dd182a833277460aa0cc9dd191503ab8b4283a0e8d5,0xd182a833277029ca13875c0a7284e1d7440d60dca3d182a833277466841cb8ac427286a1d73a44421af2] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_2s6 : Span p3_2 3 30 35 :=
  batch _ _ _ _ #[
0xc8d8189952f236062654bce911086bcb4283a0ccd5d023583728f4283a0ccd5d0a0e8333574283a0ccd5,0x5488f10e55a115666642bce911086bcb172842578ad11a1852e2f4468614b8bd023583728f4468614b8b,0xc1d888d156510ee85a1acd110e833357464540dce2d023583aa8f464540dce2d191503738b460aa0e89d,0xc84ac895e47156062654bd110e833357462a215999d110e8333574443a0ccd5d1a1485ab874685216ae1,0xca831886acd10ee85a1acce82a0c6a73332842578acea220af23327442254f1ccca1095e2b2708a2668d,0xca831886acf2a0c621ab3c88ae02ee53222b80bb94cc588899567222b80bb94ca831886acf222b80bb94,0xd182a833277052b22c791ccca1095e2b0a8c621ab3d182a8332769113c6c616ca88c88f5472a23223d51,0xd182a833277460aa0cc9dc2a31886acf0a8c621ab3421b99426af4685216ae1d110e83a3573508a2668d,0xd103583aa8f464540dce2d191503738b109ca1a875c119584758f0465611d63d191503738b0465611d63,0xc0a7284e1d7222b80bb94d191503738b222b80bb94c0a7284e1d7029ca13875c88ae02ee53222b80bb94] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_2s7 : Span p3_2 3 35 36 :=
  batch _ _ _ _ #[
0xd182a833277109ca1a875d103583728f440d60dca3d182a833277460aa0cc9dd191503ab8b4283a0e8d5,0xd182a8332773a0a829c9cc0a7284e1d7029ca13875ce911086bcb172842578ad103583728f3a44421af2] 16 (by decide +kernel)

private theorem p3_2Good : Good p3_2 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan (joinSpan p3_2s0 p3_2s1) (joinSpan p3_2s2 p3_2s3)) (joinSpan (joinSpan p3_2s4 p3_2s5) (joinSpan p3_2s6 p3_2s7)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_3s0 : Span p3_3 3 0 5 :=
  batch _ _ _ _ #[
0xc1a32870ad7068ca1c2b5d18a8856667462a215999c5ca1072e2b308ca232b5d18a8856667212b223b91,0xc5ca1072e2b068ca1c2b5d182a83a277460aa0e89dcc4a888ae671a1c42b872d182a83a277460aa0e89d,0xccca108ee2a1c1566ac23d11a185662f446861598bd11a185662f172841cb8ad0a15858d8f3a0a829c9c,0xd182a833277460aa0cc9dd182a833277460aa0cc9dc0a8e898b57052b21cb91ad6301b1ac3052b21cb91,0xc5ca1072e2b068ca1c2b5cc4a888ae67052b21cb91d18a8856667462a215999c0a8e8d0b57312a222b99,0xc1ca8852e67072a214b99ccca108ee2b1a84622373c1ca8852e67460aa0e89dc84ac88ee47460aa0e89d,0xd11a185662f446861598bc5ca1072e2b068ca1c2b5d0a15858d8f4285616363c0d710959cb052b21cb91,0xccca108ee2b1a1a82ac5cd103583728f440d60dca3d182a833277460aa0cc9dcc23288cad7308ca232b5,0xd11a1852e2f4468614b8bd086a85a1771a83819d54d11a1852e2f1a83819d54d18a885666706a5215ce1,0xc888e83a3572223a0e8d5c888e83a357234460c573c8d118315cd42c5c53166] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_3s1 : Span p3_3 3 5 10 :=
  batch _ _ _ _ #[
0xc1a9485ab87405d42bc62d111584758f3a88833a8cd111584758f4445611d63cc42a898a773a88833a8c,0xa0bd11744cb06a5216ae1ca90e02f5532a4380bd54ca90e02f553462a215999c1c2a8d0a77405d42bc62,0x5711190a5cd5c44642973c5c15078d8b06a5216ae1053972a439b3a88833a8cd10358a728f440d629ca3,0xd086a853177170541e362c11ae066e53440d629ca3cc2948cab8730a5232ae1a0bd11744cb3305433362,0xc8d118315cf234460c573c8d118315cd5063c44ad6ccc150ccd8b3a0a829c9cce82a0a7273421aa14c5d,0xd11a1852e2f4468614b8bc6a0e06755330a522ace1d18a885666706a5215ce1c427286a1d6e2c285615c,0xccc150ccd8b06a5215ce1c1a94857387206b80bb94c81ae02ee53206b80bb94c81ae02ee53421aa1685d,0x5710e10f55342a8614b8bd111584758e86a1c54ac6d111584758f4445611d63cc42a898a7614c5c99166,0xccc150ccd8b354882e68cd01750af18ab80ac6889ed0aa1852e2f354882e68c] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_3s2 : Span p3_3 3 10 14 :=
  batch _ _ _ _ #[
0xc9d220d5a33170541e362c686a0ab1731a1a82ac5cd10358a728f440d629ca3c550e0c5d5306a5216ae1,0xc11ae066e53440d629ca3ca91182a5cf2a4460a973ca91182a5cf2a4460a973ca91182a5cf3a0a829c9c,0xc81ae02ee53206b80bb94c81ae02ee53109ca1a875ce82a0a7273421aa14c5dd086a853177421aa14c5d,0xc85318b0acf3a8882bc8cc85318b0acf3a8882bc8cc0a7284e1d7029ca13875c0a7284e1d7206b80bb94,0xc5d11070dcb141ca1c475c50728711d7141ca1c475d016a85a177405aa1685dc85318b0acf031d41ea62,0xd111584758f4445611d63d111584758f4445611d63c887288d1d7221ca23475c14ac872e47221ca23475,0xc5d11070dcb154381e354c550e078d53054c6252b3d111584758f4445611d63d111584758f4445611d63,0xcc52a0b8a73214c62c2b3ccd1108cdcb2343833354] 60 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_3s3 : Span p3_3 3 14 18 :=
  batch _ _ _ _ #[
0x541d190accf230560e563c8c1583958f460aa0e89dd182a83a277031aa3445d990a595660f06a5215ce1,0xc5d11070dcb0a5a832a5cc81ae02ee53460aa0e89dc81ae02ee53174441c372c8c1583958f074a83529c,0x9582b11627b3a88833a8ccc52a0b8a73152862558bccd1108cdcb111aa2645dccd1108cdcb111aa2645d,0xc550e078d53174441c372ca90e02f553460aa0e89dca90e02f5531a1c42b872ca90e02f553174441c372,0x950399132af440d629ca3d10358a728f06a5216ae1d023583aa8f111aa2645dc5d11070dcb405d42bc62,0xca91182a5cf2a4460a973460ce963457460aa0cc9dc5d11070dcb152862c58bc8c1583958d1833a58d15,0xc8ca18b162f2223a0ccd5c888e833357440d60dca3c888e833357440d629ca3c686a0ab1732a4460a973,0xc550e078d53206b80bb94d103583728f460aa0cc9dd182a833277230560e563c8c1583958f109ca1a875,0xccd1108cdcb214c62c2b3ccd1108cdcb421d42bc62d103583728f3344423372d182a833277206b80bb94] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_3s4 : Span p3_3 3 18 23 :=
  batch _ _ _ _ #[
0xc9832831ad7312a222b9999a34177283222b80d794d016a85a177340ca216b5cd032885ad70463a318d5,0xc1ca8852e67072a214b99ca91182a5cf2a4460a973c1a948573872a4460a9735583a119ab32a4460a973,0xca90e02f5532a4380bd54ca90e02f5532a4380bd54d111584758f4445611d63d111584758f4445611d63,0xc0a7284e1d7260ca0c6b5c0a7284e1d72063a0ccd5c0a7284e1d7029ca13875c818e8333572063a0ccd5,0xc888e83a3572223a0e8d5cc2948ab387312a222b99cc52a0b8a721ac2c6215ed18a8856667462a215999,0xc1ca8852e672223a0e8d5c11728519d72223a0e8d5d1915039d8a5443c44756d1915039d88531ac84a5e,0xc1531894acf42a861598bc888e8333572223a0ccd5c0c7507a98b031d41ea62d0aa185662f42a861598b,0xd182a833277054c6252b3d182a83327742a861598bc44750ce98b2223a0ccd5d103583728f2223a0ccd5,0xc5ca1072e2b1543831754c118e8c6357031d41ea62c98948b93870463a318d5c98948b93871543831754,0xc818e83a3572063a0e8d5c818e83a357446861598bc8d0e039d53234380e754c8d0e039d53035c425672] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_3s5 : Span p3_3 3 23 27 :=
  batch _ _ _ _ #[
0xc5ca1072e2b172841cb8aa0bd11744ca82f445d132c447507a98b26252354e1c98948b938682f445d132,0xc843583aa8f2063a0ccd5c818e8333572063a0ccd5d0aa185662e354e0666a8855cc1b9c40d7304c6b0a,0xca8318a62cf230560e563c8c1583958f460aa0e89dd182a83a2771a83819d54990a595660f046b819b94,0xc81ae02ee5306a5215ce1c81ae02ee53460aa0e89dc81ae02ee531a83819d54c8c1583958f1a83819d54,0xd023583aa8f408d60eaa340bba14c6b3152862558bc1a9485738706a5215ce1c1a9485738706a5215ce1,0x4f5061c9d13232862558bcc2948cab87460aa0e89da32662ce91330a5232ae1c0c6a8d1177408d60eaa3,0x950399132af1a1a82ac5cc686a0ab173232862558bd023583aa8f111aa2645dd01750af18b460aa0e89d,0xd182a833277152862c58bc1a9485ab87460aa0cc9dc2a31886acf152862c58bc8c1583958f0a8c621ab3,0xc45710b19cb421d42bc62] 66 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_3s6 : Span p3_3 3 27 31 :=
  batch _ _ _ _ #[
0xc8c1583958f109ca1a875c8ca18b162f2223a0ccd5c888e833357440d60dca3c888e833357046b819b94,0xd182a833277206b80bb94c8ca18b162f206b80bb94c81ae02ee53460aa0cc9dd182a833277230560e563,0xcd032885ad73a8882bc8cc0a7284e1d7029ca13875c0a7284e1d7029ca13875d103583728f029ca13875,0x5711190a5cf446861598bc6a0e0675531a83819d54c6a0e0675531a83819d54c1ca8852e6706a5215ce1,0xcd032885ad71544621573c1ca8852e67072a214b99c9832831ad7260ca0c6b5c1a948573872063a0e8d5,0xc818e8333572063a0ccd5c427286a1d7109ca1a875c427286a1d7109ca1a875c1ca8852e67072a214b99,0xc1a9485738706a5215ce1c0a7284e1d7260ca0c6b5c0a7284e1d72063a0ccd5c0a7284e1d7029ca13875,0xd1915039d8b234460c573c0c7507a98b052b21cb91d1915039d8b464540e762c1ca8852e67072a214b99,0xc1ca8852e672223a0e8d5c11728519d72223a0e8d5d1915039d8b035a83545c] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_3s7 : Span p3_3 3 31 32 :=
  batch _ _ _ _ #[
0xd182a833277460aa0cc9dce911085dcb440d60dca3a1a8715631b1544621573d1915039d8b464540e762,0xd182a83327662c545e162d182a83327742a861598bce911085dcb234460c573d103583728f234460c573] 16 (by decide +kernel)

private theorem p3_3Good : Good p3_3 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan (joinSpan p3_3s0 p3_3s1) (joinSpan p3_3s2 p3_3s3)) (joinSpan (joinSpan p3_3s4 p3_3s5) (joinSpan p3_3s6 p3_3s7)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_4s0 : Span p3_4 3 0 6 :=
  batch _ _ _ _ #[
0xce82a0a5673454321cd51d022e870e57408ba1c395c8d8189722f052b226ad1d150c873547454321cd51,0xd182a831677156062cc8bcac2188ae2f440d60d5a3d182a831677460aa0c59dc50728711d7141ca1c475,0xca9118855cf1560625c8bd150c873547454321cd51c0d6a057173035a815c5cca9118855ce0356654c2b,0xcac2188ae2f1a84622373c11728711d7045ca1c475d111583958f266882e4ccd111583958f2b08622b8b,0xc6a0e078d531a8381e354b9c28152e62a131672b03d022e870e57408ba1c395d087507718b421d41dc62,0xc88728899d7454321cd51d022e870e57408ba1c395c8d8189722f052b226ad1c50728519d7141ca14675,0xa0c4f18e85b2b08622b8bd102e831e57440ba0c795d1835035e8b460d40d7a2cac2188ae2f212b234ad1,0xc84ac89ab471560625c8bc11728519d7045ca14675c81728899d7454321cd51ce911085dcb205ca22675,0xcac2188ae2f035a815c5cd1915039d8b464540e762cd182899a372b08622b8bd1915039d8b464540e762,0xc6a11888dcf1a84622373c8d818b322f0a5a832a5c815c595740e3d41463d42d02358a8e8f408d62a3a3] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_4s1 : Span p3_4 3 6 13 :=
  batch _ _ _ _ #[
0xca91182a5cf2a4460a973ca91182a5cf2a4460a973c2a2e066e531505616363c5415858d8f16a8816acc,0xc1d88897267170541e362c6a118465cf1a84611973c6a118465cf1a84611973c6a118465cf1a84611973,0xc0d6a057173035a815c5cca9118855cf2a44621573c8d0e02f553234380bd54c8d0e02f5534a8862a98b,0xc8d0e02f553310d42b3a2d150c873547170541e362ae10b18157b442b22e8d1d150c873547070aa1439d,0xce8888ba2673305433362c142e870e573305433362d017507a98b210ba23395c5aa20573330a5a816a5c,0xc1c35074e8b070d41d3a2c50958a728f1425629ca3d087507718b070aa1439dccaa20ab333454862c58b,0xccaa20cab33454862c58bccc150ccd8b1505616363ccc150ccd8b070aa1439dc5aa205ab33170541e362,0xc0a7284e1d71a84611973c6a118465cf050d6153a3c1c35074e8b029ca13875c427284e1d706ac2158f1,0xa0b8b19427b070aa1439dc5aa205ab33035a815c5ca620f16255b421d42bc62c0a7284e1d71a84611973,0xca91182a5cf2a4460a973d150c8735472305632363c88728899d7221ca22675c5415858d8f141ca14675] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_4s2 : Span p3_4 3 13 19 :=
  batch _ _ _ _ #[
0xc1ab08563c7050d6153a3c1435854e8f1a84611973c6a118465cf1a84611973d017507a98b06ac2158f1,0xd102e866657440ba19995c8d0e02f553234380bd54c8d0e02f553234380bd54c8d0e02f553070aa1439d,0xc5415858d8f1505616363c5aa205ab331505616363c8d8189722f070aa1439dc1c35074e8b070d41d3a2,0xc686a0b917316a8815ccccc2948af287214b82b394c1c2a850e7716a8816accc5415858d8f045ca14675,0xca91182a5cf2a4460a973c50728711d7428560ad63c686a0b9173428560ad63d0a1582b58f1a1a82e45c,0xc152e074e53210d60aba3c11728711d7210d60aba3c1435846e8f050d611ba3d182a8316772a4460a973,0xc1435846e8f050d611ba3c152e074e53045ca1c475c852e0ace531728426acacac2188ae2e02ee4740ea,0xd022e82e657052b226ad1d022e82e657054b81d394c843582ae8f050d611ba3c1435846e8f050d611ba3,0xc5d0a058d73050d611ba3cc52a0a8e732a6062e88bd111583958f054b81d394c152e074e53408ba0b995,0xcac2188ae2f440ba0c795c5d0a058d73314a82a39cd102e831e57440ba0c79595839111eab174281635c] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_4s3 : Span p3_4 3 19 25 :=
  batch _ _ _ _ #[
0xd1915039d8b464540e762d0a1582b58f428560ad63c1435846e8f050d611ba3d102e86665716a8815ccc,0xd022e82e657408ba0b995c1435846e8f050d611ba3c1435846e8f421d41dc62d087507718b4a8321e951,0xc5511850dcf16a8815cccc1d2a054e7316a8815cccd022e82e657408ba0b995d022e82e657408ba0b995,0xc819583aa8f174281635cc5d0a058d730a5a816a5cd0a1582b58f074a81539ccac0c899d471544614373,0xc5511850dcf174281635cd19a10ba32b074a81539cc1d2a054e732b03226751c819583aa8f074a81539c,0xcc52a0a8e73421d42bc62c1d2a054e72508e6429abc1d2a054e732a4460a973c5511850dcf074a81539c,0xc0a7284e1d7210ba0c795c0a7284e1d7408ba0b995c427284e1d7408ba0b995d022e82e6570a5a816a5c,0xd103583568f440d60d5a3ce911085dcb1560625c8bd182a831677460aa0c59da0c4f17285b464540e762,0xd022e82e657408ba0b995d022e82e657408ba0b995d182a8316760356662c2bc0a7286a1d73a44421772] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_4s4 : Span p3_4 3 25 30 :=
  batch _ _ _ _ #[
0xc5aa205ab3316a8816accc2a2e066e53141ca1c475c2a2e066e53210ba0c795d182a8316771543819d54,0xc842e831e57440d60d5a3c842e831e571543819d54c8d0e02f553234380bd54d182a83167730a5233aa1,0xc6a118465cf460aa0c59dd182a831677206560eaa3c819583aa8d670d0557a0c0a7286a1d7210ba0c795,0xc6a118465cf234380bd54c8d0e02f553408ba0b995d022e82e6571a84611973c6a118465cf408ba0b995,0xc427286a1d7210d60aba3c550e0675531543819d54d1835035e8b1543819d54d182a831677234380bd54,0xc0a7284e1d7029ca13875d111583958f210d60aba3d1835035e8b460d40d7a2c843582ae8f210d60aba3,0xcc2b088abc7408d60aba3cc2b088abc6e214655833c44750b998b111d42e662c0a7284e1d7460d40d7a2,0xc55818b322f234380bd54c1ab0852bc7035a815c5cd111583958f408d60aba3c2a2e066e53408d60aba3,0xd0a1582b58e60caa5419dd102e831e57460d40d7a2d1835035e8b428560ad63c5a8287323716a0a1cc8d,0xc84ac89ab47440ba0c795c0c750ce98b115a82e45cd0a1582b58f115a82e45c] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_4s5 : Span p3_4 3 30 35 :=
  batch _ _ _ _ #[
0xc843582ae8f210d60aba3cc2948af287050d611ba3c5aa2057333050d611ba3c55118855cf06a521dca1,0xc0a7286a1d71544621573c55118855cf1425629ca3d1915039d8b464540e762d0a1582b58f428560ad63,0xd1915039d8b408ba0b995d022e82e657408ba0b995d022e82e657408ba0b995d022e82e657029ca1a875,0xd022e82e657408ba0b995d022e82e657029ca1a875d1915039d8b464540e76240b9717429b210d60aba3,0xd0a1582b58f206560eaa3c6a0e067553234460c573c5aa20573330465631aa3d022e82e657408ba0b995,0xcac0c899d47408d60aba3c819583aa8d02f4a53135c819583aa8f30a522bca1c8d118315cf206560eaa3,0xc5aa205ab330a8b819b94c889583728f408d60aba3c50958a728f2b03226751c142e885e571425629ca3,0xc8d118315cf109ca1a875c0a7284e1d7408ba0b995c0a7286a1d7109ca1a8755711190a5cf222560dca3,0xc0a7284e1d7408ba0b995c8d118315cf408ba0b995c0a7286a1d7210ba0c795c0a7286a1d7109ca1a875,0xc0a7284e1d7210ba0c795] 74 (by decide +kernel)

private theorem p3_4Good : Good p3_4 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_4s0 (joinSpan p3_4s1 p3_4s2)) (joinSpan p3_4s3 (joinSpan p3_4s4 p3_4s5)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_5s0 : Span p3_5 3 0 6 :=
  batch _ _ _ _ #[
0xc456a057173115a815c5cca8318855cf342c2254f1d1d2107352b474841cd4accca109ab2b0762225c99,0xd103583958f3b02222b99d103583958f221ca23475c1d888b32670a8c622373c50728711d7141ca1c475,0xd1d2107352b474841cd4acc5888972671728426acad1d2107352a54466445abd0a0e870e574283a1c395,0xd190a8316774642a0c59dc11728711d7045ca1c475d190a8316773b02222b99c817288d1d7444560d5a3,0xaccc81cac62e501654b83c2a2e078d530a8b81e354d017507718b405d41dc62d0a0e870e574283a1c395,0xd1d2107352b3a0c421772ce831085dcb221ca22675d1d2107352b474841cd4ac50728519d7141ca14675,0xc456a057173342522e6a1d1835039d8b460d40e762b83311705cb3b02222b99d1835039d8b460d40e762,0xd1d2107352b474841cd4ac11728519d7045ca14675d1d2107352b3328426acad0a0e870e574283a1c395,0xc1d888b32671560625c8bd110e831e574443a0c795d1915035e8b464540d7a2cec0888ae672660a2668d,0xc686a0ca973316222cc99c2a31888dcf0a8c622373d0a158a8e8f428562a3a38b52c18f5421772055d18] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_5s1 : Span p3_5 3 6 12 :=
  batch _ _ _ _ #[
0xae02b18157b214b80bd54c5c0a850e77115a815c5cc456a0571732a0c621573ca8318855cd10f4a53135,0xc1ab0852bc73a4282959cc6a0e066e53050d616363d1d2107352b330542b3a2c1c35078d8ab80ac6055e,0xc2a318465cf0a8c611973c2a318465cf0a8c611973ca83182a5cf2a0c60a973ca83182a5cf2a0c60a973,0xc686a0ca97332a0a3388dc1c35078d8b214b80bd54c852e02f553214b80bd54c2a318465cf0a8c611973,0xcc4350ccd8b050d616363c5c0a850e7706ac214af1c11958a728f0465629ca3c5c15074e8b170541d3a2,0xc5aa20573334443a19995c6a8189aa2f1aa0626a8bc6a8189aa2f1702a1439dc5aa205ab33405d41dc62,0xccaa20ab33316a0a1cc8dc540e870e57330542b3a2c1a948772872303a23395c5a8287323716a8815ccc,0xc2a318465cf109ca13875c427284e1d70a8c611973c686a05a973029ca13875c427284e1d706ac2158f1,0xd01750af18b474222c599c2a318465cf15056153a3] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_5s2 : Span p3_5 3 12 18 :=
  batch _ _ _ _ #[
0xc1435858d8f141ca14675c5c0a850e7706ac214af1d110e8666574443a19995c5c15074e8b170541d3a2,0xc456a0571732660a2668dc5c0a850e773162225c99c1435858d8f06ac214af1c1ab0852bc71a83819b94,0xc1ab0852bc7045ca14675cc2b088abc730ac222af1c81728899d7205ca22675c5c0a850e7706ac214af1,0xc5c0a850e770762225c99c5415854e8f15056153a3c152e06755306ac2158f1ca83182a5cf2a0c60a973,0xc852e02f553214b80bd54c852e02f553214b80bd54c852e02f5530a8c611973c2a318465cf0a8c611973,0xc5a82873237141ca1c475c5a82873237230560aba3c50728711d7230560aba3c5415846e8f1505611ba3,0xc5415846e8f1505611ba3c5415846e8f1505611ba3cec0888ae67342c22c4f1c887288d1d73b02222b99,0xc296a0ab1734283a0b995d103583958f154381d394c550e074e53154381d394c8c1582ae8f1505611ba3,0xd023582b58f32a0a23c8dc296a0b91733a2222e899c8d0e0ace53314c423372d0a0e82e6574283a0b995,0xc11728711d74642a0c59dca83182a5cf2a0c60a973ca83182a5cf408d60ad63c296a0b9173408d60ad63] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_5s3 : Span p3_5 3 18 24 :=
  batch _ _ _ _ #[
0xd1835039d8b460d40e762d023582b58f408d60ad63c5415846e8f1505611ba3d110e8666574443a19995,0xd0a0e82e6574283a0b995c5415846e8f405d41dc62d017507718b06ac2158f1c5415846e8f1505611ba3,0xc1d2a058d73334282a39c95919111eab1505611ba3d0a0e82e6574283a0b995d0a0e82e6574283a0b995,0x5489991a2af4443a0c795c1d2a058d73334282a39cd110e831e574443a0c79595919111eab074a81635c,0xc5d0a054e73054c614373c5d0a054e7316a8816accc1d2a058d7306ac214af1c5d0a054e73174281539c,0xc686a05a973408d60ad63c5d0a054e73174281539cd02ac8b334740ab22ccd1ca83182a5cf054c614373,0xc1d2a058d73074a81635cc889583aa8f174281539cc889583aa8f334282a39cc1531850dcf054c614373,0xc8c0e831e57109ca13875ccd0a0a8e73405d42bc62d0a0e82e6571a1a816a5cc1ab08563c7174281539c,0xd0a0e82e657029ca13875d0a0e82e657109ca13875] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_5s4 : Span p3_5 3 24 29 :=
  batch _ _ _ _ #[
0xc8c1582ae8f230560aba3c0a7286a1d7230560aba3c152e067553054b819d54c152e067553464540d7a2,0xc427284e1d7464540d7a2c427284e1d7109ca13875d103583958f230560aba3d1915035e8b464540d7a2,0xc6a0e066e53428560aba3c1a9487aa87428560aba381dc517740ae054655833c0c750b998b262c2254f1,0xd1835039d8b3b02222b99c456a057173115a815c5cd103583958f031d42e662c852e02f553428560aba3,0xc427286a1d73a0c421772d111583568f444560d5a3ce831085dcb3a4282959cd190a8316774642a0c59d,0xd190a831677054b819d54d0a0e82e6574283a0b995d0a0e82e6574283a0b995d190a831677474841cd4a,0xce90a0a56733162225c99c852e02f553214b80bd54c6a0e066e53045ca1c475c6a0e066e532303a0c795,0xc8d818b322f2303a0c795c8c0e831e57444560d5a3c8c0e831e57054b819d54d190a83167706ac214af1,0xc2a318465cf214b80bd54c852e02f5534642a0c59dd190a831677222560eaa3c889583aa8f109ca1a875,0xd0a0e82e6574283a0b995c2a318465cf0a8c611973d0a0e82e6570a8c611973d190a831677214b80bd54] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_5s5 : Span p3_5 3 29 34 :=
  batch _ _ _ _ #[
0xd023582b58f408d60ad63c5415846e8f1728434acac5415846e8f32a0a23c8dc5a82873237221ca22675,0xc15318855cf0465629ca3c427286a1d7109ca1a875d1835039d8b460d40e762c8c1582ae8f230560aba3,0xd1835039d8b4283a0b995d0a0e82e6574283a0b995d0a0e82e6574283a0b995d0a0e82e657054c621573,0xd0a0e82e6574283a0b995d0a0e82e657052b226ad1c8c1582ae8f460d40e762c427286a1d7460d40e762,0x98b0a950677464540d7a2d1915035e8b32a882accca438b19427b408d60ad63d0a0e82e6574283a0b995,0xc0d6a0b91734443a0c795c9982899a374443a0c795c0d6a0b9173408d60ad63c0d6a0b9173408d60ad63,0xd0a1582ae8f1a83819b94c1ab0852bc73b0842674ac11958a728f428560aba3cc2b088abc70465629ca3,0xd023582b58f222560eaa3cca8288f23706a521dca1c819583728d5c0c642973cc2948cea87206560dca3,0x5442f111d5b214c60c573c889583aa8f16a8815cccc889583aa8f0a8b819d54c85318315cf222560eaa3] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_5s6 : Span p3_5 3 34 35 :=
  batch _ _ _ _ #[
0xc0a7286a1d7109ca1a875c8c0e831e57109ca1a875d0a0e82e657109ca13875c0a7286a1d7109ca1a875,0xd0a0e82e657214c60c573d0a0e82e657109ca13875c8c0e831e57109ca13875c0a7286a1d7214c60c573] 16 (by decide +kernel)

private theorem p3_5Good : Good p3_5 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_5s0 (joinSpan p3_5s1 p3_5s2)) (joinSpan (joinSpan p3_5s3 p3_5s4) (joinSpan p3_5s5 p3_5s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_6s0 : Span p3_6 3 0 5 :=
  batch _ _ _ _ #[
0xd0235858d8f408d616363cd1a20b93334548614d4bc5a12870ad74548614d4bd152185352f1423a1e855,0xd1d2107352b474841cd4ad1d2107352b4458a1c58dd1d2107352b4458a1c58dd1162871637046562e463,0xc5a12870ad71518a1c58dc686a046e731a1a811b9cc686a046e731a1a811b9cc686a046e731a1a811b9c,0xc5562075633155881d58ccec0889aa672063a23c55c14748756870a8c622373c118e87a1571684a1c2b5,0xa444f18e85b408d616363ce90a0a72733284a232b5c508e87a155d302c44a9ec118e8731573284a232b5,0xc508e8731573328426acac2a2e078d53460d419d62c2a2e078d531425615c63b11cc177443052b234ad1,0xccca109ab2b2223a26655c5ca10d2b2b222562ac63c118e87a1570463a1e855c5a12870ad71622a14c5d,0xd152185352f3a0c421772d152185352f4548614d4bccca109ab2b0a8c622373d1074855e87441d2157a1,0xd1074855e87306c40d8f2d152185352f1625435662d1074855e871684a1c2b5] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_6s1 : Span p3_6 3 5 11 :=
  batch _ _ _ _ #[
0xd1162851e373328426acad0235858d8e839466c433ca9620a9e332644a216b5ca9620a9e332644a216b5,0xc0aae0b8b533444a0c6b5cd112831ad6839466c433d0235858d8f408d616363c5ca10d2b2b4458a1478d,0xc5462851e37408d616363d0235858d8f4548614d4bca9118a62cf0463a1e855c1c350c5d8b428562e2a3,0xc1d31070dcb314c423372cc435039d8b310d40e762cc435039d8b1425616a63d1d088b32670a8c622373,0xd103584758f440d611d63c84ac89ab472a0c60a973ca83182a5cf4458a1c58dcec0889aa670465635463,0xc11958b918f3a0a80ad5cce82a02b573314c423372d0a6284e6374a8861694bd2a2185a52f440d611d63,0xca83182a5cf035a82a39cc5462871637115a81539cc456a054e73314c423372ce82a02b5730b1a222b99,0xd1a148772871518a1c58dc8c6288d63716a8815cccca83182a5cf2223a33855c118e8731571a9881ab8c,0xc1d31070dcb210d60e563d1a14877287210d60e5633706a206e73222b80ead4cac2189952f32a882accc] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_6s2 : Span p3_6 3 11 16 :=
  batch _ _ _ _ #[
0xce82a02b5731518a1c58dcc88a88b177115a81539cc456a054e731622a14c5d7702a10b571dc0a842d5c,0xc199507718b314c423372ce82a02b573322542bc62ce82a02b5733a0a80ad5cc5d0a0d4a73054b81e354,0xcca1282e2d73284a0b8b5cc53108cdcb466842cccad0a6286a637051d21d5a1cc1950af18b050d631563,0xcec0889aa67441d2157a1c888e899957115a81539cc428e87315716a8815cccccaa20ab33310a3a1cc55,0xd1074855e87441d2157a1c2c6888ae671423a34655ccca109ab2b115a81539cd1074855e872223a26655,0xc5a128662d7115a81539cd1074855e8710a3a1e855c11ae0a73534a8861694bd2a2185a52f4a8861694b,0xcca1282e2d73284a0b8b5c81ae0373533284a0b8b5d1074855e87441d2157a1c888e8d19570b1a222b99,0xcd112831ad74458a1478dc456a054e7302a3a1cc55d1162851e37115a81539cc0a8e873157074c41c372,0xca83182a5cf3444a0c6b5c0d6a0a8e732644a0c6b5] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_6s3 : Span p3_6 3 16 22 :=
  batch _ _ _ _ #[
0xc0a8e87a1571425615c63d2a2185a52f440d611d63c588a8531773444a216b5d103584758f440d611d63,0xc8c62889e37074c41c372ce82a02b5733a0a80ad5ccc53108cdcb4a8861694bc9912831ad7054b81e354,0xcc435039d8b2063a23c55ca83182a5cf409d213ba1c6a6206ae330463a1cc55c6a6206ae3310a5616a63,0xc428e87315710a3a1cc55c8c62889e3710a3a1cc55c428e8731573b0842674ac456a054e732a0c60a973,0xd103584758f440d611d63c0a8e88f157310d40e762443d294c4d7222b80ead4ccaa20ab333174283529c,0xd027484ee871a9881ab8cc5462851e371423a1cc55d103584758f440d611d63c9c148d5a87440d611d63,0xd02ac8ba3474a8861694bc199507718b4a8861694bcc8950af18b3a0a80ad5cc5d0a0d4a733a0a80ad5c,0xb1a0717621b212b234ad1cca1282e2d73284a0b8b5c509585a98f1425616a63d2a2185a52f1684a198b5,0xcca1282e2d74298a1398dcc18a8991770b1a222b99c2c6888ae67230560eaa3d1d2107352b0b1a222b99,0xcca1282e2d74298a1398dcca1282e2d73284a0b8b5d0a6284e6374298a1398d] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_6s4 : Span p3_6 3 22 28 :=
  batch _ _ _ _ #[
0xd027484ee87214b80bd54ca83182a5cf2a0c60a973ca83182a5cf1a9881ab8cc152e067553310d40e762,0xcc18a899177222b80ead4cc8b1032bcb054b819d54c6a11886acf310d40e762d152185352f409d213ba1,0xc6a6206ae33306c40d8f2cc1b10363cb1a9881ab8cd0a6284e6373284a0b8b5c852e02f553322c40caf2,0xcc1b10363cb474841cd4ac5462871637210d60e563c58950d598b02a5632a63ce831085dcb3a0c421772,0xca83182a5cf054b819d54c818e899957054b819d54cc1b10363cb10a5616a63c8c6288d6373a0c421772,0xc852e02f553474222cc99c9912831ad73444a0c6b5cd112831ad7210d60e563c843583958f2a0c60a973,0xc843583958f210d60e563c88ae03ab53322c40caf2ca9620a9e33054b819d54c852e02f553442b22e8d1,0xcc1b10363cb468521dca1c686a046e73214b80bd54c14748756872644a0c6b5d0a6286a635d10ac4455e,0xcc52a039573468521dca1ca82e039d53214c60c573ca82e039d53214c60c573cc1b10363cb1505631aa3,0xcc52a039573441d2157a1cc52a0395733a0c421772cc52a03957332a882accc] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_6s5 : Span p3_6 3 28 34 :=
  batch _ _ _ _ #[
0xc85318315cf214c60c573cca1282e2d73284a0b8b5cca1282e2d74298a1a98dd0a6286a6374298a1a98d,0xcca1282e2d73284a0b8b5c81ae0373533284a0b8b5cc52a0395734298a1a98dc81ae0373534298a1a98d,0xc9912831ad73444a0c6b5cc52a039573468521dca1cec0889aa6732a882acccc54158c6a8e9886660cab,0xc9912831ad7214c60c573d2a2185a52f4a8861694bc85318315cf440d611d63d0a6286a6374298a1a98d,0xd11158a728f2063a23c55c8c62889e374445629ca35033714c59b0463a26655c428e8ce1574298a1a98d,0xcc52a0395732063a23c55d10ac8ba3471423a1e855cc52a039573206b80dcd4c81ae037353206b80dcd4,0xc85318315cf214c60c573c85318315cf16a8815cccc428e8731572318a2278dd19a10b332b206b80dcd4,0xcc1b10363cb2318a2278dc0a8e88f157314a80e55cc686a046e73222b80ead4cc52a0395730a8b819d54,0xcc1b10363cb0463a1e855c85318315cf322542bc62cc88a88b177306c40d8f2d103584758f306c40d8f2,0xcc8950af18b2223a23c55c85318315cf1518a1478d] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_6s6 : Span p3_6 3 34 35 :=
  batch _ _ _ _ #[
0xc85318315cf214c60c573c85318315cf3b0842674ac85318315cf3284a0b8b5cc8b1032bcb066541dc62,0xcca1282e2d73284a0b8b5c85318315cf1a1a811b9ccc52a039573314a80e55c] 14 (by decide +kernel)

private theorem p3_6Good : Good p3_6 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_6s0 (joinSpan p3_6s1 p3_6s2)) (joinSpan (joinSpan p3_6s3 p3_6s4) (joinSpan p3_6s5 p3_6s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_7s0 : Span p3_7 3 0 5 :=
  batch _ _ _ _ #[
0xc84ac89ab47408d6153a3d0235854e8f408d6153a3c68710665cb1a1c419972c68710665cb1a1c419972,0xc888e8ce1572b08622b8bc198a8d11771728426acacc43502ee8b310d40bba2cc43502ee8b310d40bba2,0xc199507a98aa119c63546ca911886acf2a44621ab3c14748795871622a1685dc588a85a1771622a1685d,0xc29710665cb0a5c419972c509585a98f2a446298b3c888e8ce157474222cc99b832a154672e0ca85519c,0xc508e8731571423a1cc55d296107a52b4a5841e94ace82a02ae733a0a80ab9cce82a02ae733a0a80ab9c,0xc508e8731571a1a811d5cd0235854e8f4a5841e94ac1c35066e8b070d419ba2c509585718f1425615c63,0xc686a047573408d6153a3c29710665cb1a1a811d5cc5a12870ad71684a1c2b5c686a0475731a1a811d5c,0xc19b10a63cb3225435662d0568853567415a214d59d022e870e57408ba1c395cc43502ee8b408d6153a3,0xcc1b10363cb415a214d59c5a12870ad7408d6153a3d0235854e8f415a214d59c19b10a63cb3225435662,0xc42ae0b8b53306c40d8f2] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_7s1 : Span p3_7 3 5 11 :=
  batch _ _ _ _ #[
0xd182a8466772a5883274cd182a846677460aa1199dd0d6107352b435841cd4ad182a846677435841cd4a,0xcc43502ee8b310d40bba2cc43502ee8b310d40bba2c818e899957408d6153a3d0235854e8f408d6153a3,0xd0235854e8f408d6153a3d182a846677460aa1199da606b14257b35052356a1d182a846677442b22e8d1,0xd05688535671425616a63c888e8ce157310d40d7a2cc435035e8b310d40d7a2c588a85a1771a1c419972,0xce82a02ae733a0a80ab9cce82a02ae733a0a80ab9cc29710665cb415a214d59b015995a0ae82f445d132,0xd182a846677460aa1199dd182a8466774a1a216959d286885a567409d213d61ce82a02ae733a0a80ab9c,0x702a715631b214b82b394c5511894acf1728426acac55118b0acf310d40bba2cc43502ee8b174282e29c,0xcc1950ce98b10a5615c63c0d7108cdcb3284a0b8b5c88ae037353310d40bba2c1c35066e8b1684a198b5,0xc81ae03ab53206b80ead45462e115e531a9881ad4cc6a6206b5333a4280ea9cc457108cdcb10a5615c63] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_7s2 : Span p3_7 3 11 17 :=
  batch _ _ _ _ #[
0xd296107a52b035a83235cd296107a52b0b1a226559c152e074e53460d419ba2d1835066e8b4a5841e94a,0xd10ac8b33474a5841e94ac588a8531771622a14c5dc0d7108cdcb3a0a80ab9cc5d0a0b8a731a9881ad4c,0xc509585718f1425615c63c509585718f1622a14c5dc843583568f306c40d8f2c88ae0373531423a1cc55,0xc843583568f3284a0b8b5cca1282e2d74a8862a98bce90a03aa733a4280ea9cc457108cdcb0b1a226559,0xc4571070dcb1a9881ad4cc6a6206b533115a81635cc456a058d731a9881ad4c748d1115cc9d18a84559c,0xc0d7108cdcb154462c2b3ca870889dc7174282e29cc6a6206b533115a81635ccec0889aa651ac685e0ac,0xd182a846677115a81635cd182a846677334283529cc456a058d7310a5615c63d286885a5674a1a216959,0xcd112885ad7222562ac63cc43502ee8b310d40bba2d027484f587310d40bba2c9912831ad7460aa1199d,0xcc43502ee8b310d40bba2c9912831ad72644a0c6b5c118e899957070d419ba2c1c35066e8b0a9c21a971,0xc9912831ad7310d40bba2] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_7s3 : Span p3_7 3 17 23 :=
  batch _ _ _ _ #[
0xc588a85a177409d213d61d182a846677115a81635cd182a846677460aa1199dc6a6206b5334a1a216959,0xc152e074e53440d611ba3c456a058d73440d611ba3c81ae03ab53310d40d7a2c429585718f1622a1685d,0xce82a02ae733a0a80ab9cc842e831e57210ba0c795d19a10ba32b409d213d61d027484f5871a9881ad4c,0xc4571070dcb0463a1e855cc88a88b177115c41c372c5aa205ab33142b829cd4c0d7108cdcb115a81635c,0xc142e885e571b1842674ac0d7108cdcb1622a14c5dcc435035e8b310d40d7a2c88ae03735316a8816acc,0xc588a8531773284a0b8b5c509585718f3a4280ea9cc457108cdcb1684a198b5c5a128662d70a9c21a971,0xd0d6107352b435841cd4ad0d6107352b1423a26655ccd0a037273435841cd4accd0a037273334280dc9c,0xcca1282e2d73284a0b8b5c6871085dcb1a846298b3cca1282e2d7441d216761cca1282e2d7415a214d59,0xcc435035e8b0a5a83155cc6a11886acf322c40d8f2b88519560cf1423a1e855cc8b10363cb310d40d7a2] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_7s4 : Span p3_7 3 23 28 :=
  batch _ _ _ _ #[
0xcc8b1032bcb1a846298b3c5a128662d7210ba0c795c842e831e573a0a80ab9cce82a02ae733a0a80ab9c,0xc1c2a885677460d4297a2ccd0a037273310aa0c59dcca1282e2d71a846298b3c842e831e57334280dc9c,0xcc1b10363cb306c40d8f2c843583568f210d60d5a3cc1b10363cb306c40d8f2c843583568f210d60d5a3,0xc81ae03ab53210d60d5a3c843583568f4a8862a98bcc1b10363cb210d60d5a3cc1b10363cb210d60d5a3,0xc6871085dcb10a3a1e855c81ae03ab53206b80ead4c6871085dcb210d60d5a3cc42a831675c215c6a626,0xc843583568f322c40d8f2cc8b10363cb440ba19995cca1282e2d7206b80ead4c843583568f02a3a33855,0xcc8b10363cb1622a1685dc0a958ca98f2644a0c6b5cd112831ad7210d60d5a3b9170151dc2e45c054770,0xc9912831ad7310aa0c59dc6a118a62cf460d419ba2c2a7086a5c73a0a80ab9cce82a02ae733a0a80ab9c,0xc9912831ad7322c40caf27702a10ae730a5c421772d1d088b32672644a0c6b5] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_7s5 : Span p3_7 3 28 33 :=
  batch _ _ _ _ #[
0xcec0889aa6702a3a23c55cec0889aa674a5841e94ad296107a52b4a5841e94acc52a035673314a80d59c,0xc0a8e88f157162542e662c58950b998b162542e662791b01563c3162542e662c58950b998b162542e662,0xcd112831ad70463a34655d182a846677460aa1199dcec0889aa67310d40bba2cc52a035673314a80d59c,0xccca10d2b2b074a82959ccc43502ee8b314a80d59ccc43502ee8b310d40bba2d027484f5872644a0c6b5,0xc15708715c7314a80d59ccc52a035673314a80d59cc9912831ad7310d40bba2c9912831ad71728426aca,0xc429585718f1622a1685dc588a85a177206b80ead4c68710665cb10a5615c63a606b14257b454862c58b,0xc842e831e57210ba0c795d15218b162f454862c58bc842e831e57215c223571c81ae03ab53314a80d59c,0x519b815a3a340ab22ccd1c842e831e57210ba0c795d15218b162f35052356a1c428e873157210ba0c795,0xc0a8e88f15702a3a23c55] 66 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_7s6 : Span p3_7 3 33 35 :=
  batch _ _ _ _ #[
0xac4c51d5c0b454862c58bc88ae0373531423a1cc55cc52a035673314a80d59cc588a853177314a80d59c,0x711b815a3a31a1a811d5ccc52a035673314a80d59cc88ae0373531a1a811d5cc5562079533314a80d59c,0xce90a0c6a73306c40caf2c842e831e571425615c63c842e831e573284a0b8b5cc52a035673314a80d59c,0xc686a0475733284a0b8b5c686a047573155881e54c] 28 (by decide +kernel)

private theorem p3_7Good : Good p3_7 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_7s0 (joinSpan p3_7s1 p3_7s2)) (joinSpan (joinSpan p3_7s3 p3_7s4) (joinSpan p3_7s5 p3_7s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_8s0 : Span p3_8 3 0 5 :=
  batch _ _ _ _ #[
0xd1d088535658c54a5a835c686a0a56730463a1e855d1d088535674742214d59d1d088535674285616363,0xd1074875687454321cd51d150c873547262c2254f1d1074875687441d21d5a1c2c6888ae67454321cd51,0xd150c8735471423a1e855c296a046e730a5a811b9cc296a046e730a5a811b9cc296a046e730a5a811b9c,0xc6a0e078d534645419d62c55620756330465615c63c1a32870ad7068ca1c2b5c6a11888dcf4a1a22a999,0xcac2189aa2f206562ac63c1a32870ad70662a14c5dc118e87315710ab82e2d4c508e87a1571423a1e855,0xce82a0a7273308ca232b5c84ac8d2b472223a23c55c84ac8d2b472223a23c55c508e873157308ca232b5,0xa14c595ac0f260ca216b5a0c4f18e85b235882b58cb18c517740b0463a1e855c8d620ad6334285616363,0xd1d088535674285616363c2c6888ae67454321cd51d1074855e873328426acac0aae0d4b53260ca216b5,0xd1d08853567340ca0c6b5cd032831ad6e11945cb82d1d088535674742214d59] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_8s1 : Span p3_8 3 5 11 :=
  batch _ _ _ _ #[
0xd1162851e374458a1478dd150c873547454321cd51c58b10a63cb2063a26655c58b10a63cb2063a26655,0xd1d08853567322c40d8f2d1162851e370665435662d1d088535674742214d59d1162851e373a44421772,0xc119585a98f4742214d59d1d088535674285616363c508e87a1573508a2668dc5c150c5d8b051d2157a1,0xccd1108cdcb174441c372c1474855e87051d2157a1c6a11888dcf330540e762ccc15039d8b330540e762,0xd111584758f4445611d63ca91182a5cf0b1a222b99d1a228732372a4460a973cac2189aa2f052b234ad1,0xccd1108cdcb3a4280ad5ccc1950af18b142562e463d0a6284e6374298a1398dc1531894acf4445611d63,0xc14748756874688a1cc8dc1d2a0d4a7333444233725306696a6173b02226559ce90a02b5733a4280ad5c,0xcec088995673b02226559c1474875687206b80ead4c5d11070dcb230560e563c428e88f157230560e563,0xce90a02b573074a83529cc6a6206ae330463a1cc55d027486ae87035a81539cc0d6a054e7306ac214af1,0xce90a02b5733a4280ad5ccc1950af18b3a4280ad5c] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_8s2 : Span p3_8 3 11 17 :=
  batch _ _ _ _ #[
0xca91182a5cf2063a33855c6a6206ae33409d21aba1cc2b088abc7035a81539cccd1108cdcb06ac214af1,0xd2a0c87a5474a8321e951cec0889956706ac2158f1c1ab08563c706ac2158f1c118e87a1572a4460a973,0xc14ac8d2b47035a81539cc428e873157174441c372ccd1108cdcb308ca0b8b5cc23282e2d7051d21d5a1,0xca91182a5cf340ca0c6b5d1074855e87260ca0c6b5cd032831ad73344423372c0d6a054e73441d2157a1,0xc119585718f154381e354d1074855e874445611d63c198a85317706ac2158f1d111584758f4445611d63,0xcac2189aa2f02a3a1cc55ce90a02b5733a4280ad5cd0a6284e6374298a1398dc9832831ad7441d2157a1,0xc0a8e8731572063a26655d1162851e3702a3a1cc55c818e899957035a81539cc0a8e8731572a5882a78c,0x60e529710d7142b829cd4460af1a235b10a3a23c55d1162851e374458a1478dd1162851e37035a81539c,0xccca109ab2b2063a34655c1a328662d7035a81539cc1a328662d702a3a1e855c1ab08563c730ac22a8f1,0xcc23282e2d7308ca0b8b5c88ae037353308ca0b8b5c1a328662d7068ca198b5] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_8s3 : Span p3_8 3 17 23 :=
  batch _ _ _ _ #[
0x710a715631b211d22a7a1c0a8e8731572b03226751c0a8e87315702a3a1cc55c84748a9e8702a3a1cc55,0xc6a6206ae334445611d63d111584758f4445611d63c1474855e87206b80ead4c428e88f157330540e762,0xce90a02b573409d213ba1cc2b088abc70463a1cc55c0d6a054e730463a1cc55d111584758f4445611d63,0xc118e87a1571423a1cc55c50ae0a735302a5616a63c5d11070dcb2b03226751ce90a02b573409d213ba1,0xc1ab08563c7211d22a7a1c888e88f1572a4460a973c1ab0852bc72a4460a973ccc15039d8b115a82a39c,0xc1ab08563c7308ca0b8b5cc23282e2d706ac2158f1d0a6284e637068ca198b5c1474855e87066c421af2,0xc843583aa8f441d21d5a1d10748756869cc4463172c2c6888ae670b1a222b99c2c6888ae672a5882a78c,0xcc23282e2d74742214d59cc23282e2d7308ca0b8b5d1d088535674742214d59cc23282e2d73a44421772,0xccc15039d8b409d213ba1ca91182a5cf2a4460a973ca91182a5cf1543819d54c588a8d1177330540e762,0xc2a31886acf262c2254f1c8d0e02f553409d213ba1] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_8s4 : Span p3_8 3 23 29 :=
  batch _ _ _ _ #[
0xc8d0e02f553306c40caf2d1d08853567308ca0b8b5c81ae03ab53342c2254f1c550e067553306c40caf2,0xcd032831ad7230560e563c8c1583958f2a4460a973ca91182a5cf1543819d54c888e8999571543819d54,0xc550e067553306c40caf2c8d0e02f5532318a2358dc8d0e02f55110f4a5a135c9832831ad7340ca0c6b5,0xc81958ca98f260ca0c6b5c58950d5989d302c4455ec81ae03ab53230560e563c8c1583958f1505631563,0xd027486ae873a44421772d28688aa667322c40d8f2cc8b10363cb2063a26655c296a046e73234380bd54,0xd10ac8ba3473a44421772cc8b10363cb409d21aba1d15218b322f230560e563d027486ae87442b22e8d1,0xccd0a0395733328426acad1074855e87174283155ccac2189aa2f4688a1cc8dcc8b10363cb02a5616a63,0xd0a6284e6374298a1398dc8d118315cf4445611d63d2a0c87a5474a8321e951c9832831ad7340ca0c6b5,0xd0a6284e6374298a1398dd0a6284e6371423a26655c9832831ad7234460c573] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_8s5 : Span p3_8 3 29 34 :=
  batch _ _ _ _ #[
0xca90e039d53234460c573ca90e039d53234460c573cc8b10363cb2b08626a8bcc8b10363cb2b08626a8b,0xccd0a03957310a3a23c55ccd0a0395734458a1478dccd0a0395734688a1cc8dccd0a0395733a44421772,0xc8d118315cf234460c573cc23282e2d7308ca0b8b5cc23282e2d74a8321e951d2a0c87a5474a8321e951,0xcc23282e2d7308ca0b8b5c88ae037353308ca0b8b5ccd0a0395730463a26655c88ae0373530463a26655,0xccd0a0395731a83819d54c8d118315cf234460c573c8d118315cf2b03226751cac0c899d4702a3a1cc55,0xd111584758f322c40d8f2cc8b10363cb2b03226751c296a046e73206b80ead4c428e88f157334280e55c,0xd027484ee87234460c573cc8b10363cb1423a1e855c8d118315cf409d213ba1cc2b088abc7322c40d8f2,0xc88ae037353222b80dcd4c888e88f15706ac214af1d10358a728f2b03226751c888e8ce157409d213ba1,0xc888e88f1573508a2668dc1ab0852bc7222b80dcd4ccd0a0395730463a1e855ccd0a039573222b80dcd4] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_8s6 : Span p3_8 3 34 35 :=
  batch _ _ _ _ #[
0xc8d118315cf051d2157a1c8d118315cf234460c573c8d118315cf306c40caf2cc23282e2d7162541dc62,0xc296a046e73308ca0b8b5cc23282e2d7234460c573ccd0a039573334280e55c] 14 (by decide +kernel)

private theorem p3_8Good : Good p3_8 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_8s0 (joinSpan p3_8s1 p3_8s2)) (joinSpan (joinSpan p3_8s3 p3_8s4) (joinSpan p3_8s5 p3_8s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_9s0 : Span p3_9 3 0 5 :=
  batch _ _ _ _ #[
0xc29710665cb0a5c419972c29710665cb415a214d59c0aae0b8b5342856153a3d0a15854e8f42856153a3,0xccc1502ee8b330540bba2ccc1502ee8b330540bba2c818e8ce157441d21e561d1074879586e501654b83,0xce90a02ae733a4280ab9cce90a02ae733a4280ab9cc119585a98f2a0c6298b3c68710665cb1a1c419972,0xb8b0a154673162541ea62c198a85a1772a0c621ab3ca831886acf2a0c621ab3c198a85a1770662a1685d,0xd286885a5674a1a216959c119585718f0465615c63d19a10ba32b211d233561c84748cd586e2c285519c,0xc68710665cb0a5a811d5cd286885a5674a1a216959c5d0a0a5672605568dc23d0a15854e8ec213c5d816,0xc1a32870ad70a5a811d5cc296a047573055c21c571c296a04757342856153a3c296a04757342856153a3,0xd190a8466774642a1199dcec0888ae67260ca216b5d190a8466773b02222b99ccc1502ee8b068ca1c2b5,0xccc1502ee8b330540bba2c888e89995742856153a3d0a15854e8f42856153a3d190a8466773b02222b99,0xccc1502ee8b330540bba2] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_9s1 : Span p3_9 3 5 11 :=
  batch _ _ _ _ #[
0xcec0888ae673065435662cec0888ae673065435662cec0888ae67162c4298f2d0a0e870e574283a1c395,0xc0aae0b8b53322c40d8f2cc8b10363cb066542e662c1a32870ad742856153a3d0a15854e8dc429c558c6,0xce90a02ae733a4280ab9cc68710665cb1a1c419972cd4228d1a37454862cc8bcd422899a37051d216761,0xa216b14257a885ac5095ed190a846677051d216761ce90a02ae733a4280ab9cce90a02ae733a4280ab9c,0xccc15035e8b330540d7a2ccc15035e8b0a5c419972d0a15854e8f42856153a3d190a8466774642a1199d,0xd190a8466774642a1199dd190a846677214c6252b3d027484f587409d213d61c198a85a1772063a33855,0xc8d0e0ace53262c22c4f1ccc1502ee8b330540bba2cec0888ae674688a1cc8d548d19154cf3b02222b99,0xc550e074e534688a1cc8dc81ae037353330540bba2d1074879587308ca0b8b5c1a328662d71705419ba2,0xce90a02ae73074a82e29cd027486b587115a83235cd027486b585e214a53835d1915066e8b4645419ba2,0xc199507a98b4688a1cc8d] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_9s2 : Span p3_9 3 11 17 :=
  batch _ _ _ _ #[
0xc81ae0373530463a1cc55c8c1583568f322c40d8f2c58b10a63cb211d233561c1ab0852bc706ac214af1,0xc88ae03ab53222b80ead454e0e115e533a0a80ea9cd027486b5874a5841e94ac0a9585718f02a5615c63,0xc0d7108cdcb466842cccac119585718f0465615c63c119585718f0662a14c5dd02ac8b334740ab22ccd1,0xcac2189aa2f3062a3285dc2a7086a5c7230560d5a3cc23282e2d7308ca0b8b5ce82a03aa733a0a80ea9c,0xc9832831ad74642a1199dd190a846677035a81635cd190a8466771a9881ad4cc0d6a058d7302a5615c63,0xc5c15066e8b4688a1e88dc4571070dcb206562ac63ccc1502ee8b330540bba2cec0888ae67330540bba2,0xc9832831ad7330540bba2ccc1502ee8b330540bba2c9832831ad7260ca0c6b5d1074859d871423a26655,0xd286885a567214c6252b3cc52a0d4a73035a81635cc0d6a058d73035c41c372cec0888ae674a1a216959,0xd027484f587409d213d61d027484f587409d213d61cc52a0d4a73035a81635cd286885a5674a1a216959] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_9s3 : Span p3_9 3 17 23 :=
  batch _ _ _ _ #[
0xc8c0e831e574a1a216959d286885a5673508a3468dd286885a5674445611ba3c0d6a058d734445611ba3,0x74c19111eab4a1a2169597a115162e8b409d213d61c0d6a058d733a4280ab9cce90a02ae732303a0c795,0xc457108cdcb06ac214af1ccc15035e8b330540d7a2c0d71070dcb051d216761d286885a567035c41c372,0xd190a846677035a81635cd190a8466774642a1199dc85318b0acf3062a3285dc81ae0373532223a33855,0xc81958ab18f1503a21795c198a85a1770662a1685dc88ae03ab53330540d7a2c0a9585718f035c423372,0xc119585718f0662a14c5dcc23282e2d73a0a80ea9cc0d7108cdcb068ca198b5c1a328662d7115c41c372,0xd0d6107352b074a829c9cd1074879587441d21e561cc52a037273314a80dc9ccc52a0372734688a1e88d,0xcc23282e2d7308ca0b8b5c2a318a62cf0a5c421772cc23282e2d70a8c6298b3cc23282e2d7342c2254f1,0xc2a31886acf306c40d8f2ccc15035e8b1a1a83155cd15218b322f0463a1e855cc1b10363cb330540d7a2] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_9s4 : Span p3_9 3 23 28 :=
  batch _ _ _ _ #[
0xc2a318a62cf2303a0c795c8c0e831e572303a0c795c1a328662d73a4280ab9cce90a02ae733a4280ab9c,0xc8c1583568f306c40d8f2cc1b10363cb4443a19995cc52a037273306c40caf2d0568853567308ca0b8b5,0xcc1b10363cb0662a1685dc42958ca98f260ca0c6b5cd032831ad7230560d5a3b81519560cf454862cc8b,0xc9832831ad73302a0c59dd0d6107352b066c421af2d1915066e8b3a4280ab9cce90a02ae733a4280ab9c,0xcc52a0372733302a0c59dc9832831ad7306c40caf27710a10ae731a1c421772c81958ca98f260ca0c6b5,0xc8c1583568f230560d5a3cc8b10363cb322c40d8f2c8c1583568f230560d5a3c5c0a885677051d21e561,0xc8c1583568f0a9c21a971cc8b10363cb230560d5a3cc8b10363cb230560d5a3cc8b10363cb322c40d8f2,0xc88ae03ab53222b80ead4c2971085dcb230560d5a3ccc0a831675c055c6a626c88ae03ab53230560d5a3,0xcc23282e2d7222b80ead4c8c1583568f10a3a33855c2971085dcb02a3a1e855] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_9s5 : Span p3_9 3 28 33 :=
  batch _ _ _ _ #[
0xcd032831ad7409d21ad61d190a8466774642a1199dd027486b587330540bba2ccd0a035673334280d59c,0xb01599530af174282959cccc1502ee8b334280d59cccc1502ee8b330540bba27442b112a7b260ca0c6b5,0xd027486b587409d21ad61ccd0a035673334280d59cc9832831ad7330540bba2c9832831ad74688a1e88d,0xd027486b587409d21ad61d027486b587409d21ad61d027484f587409d213d61d027484f587409d21ad61,0xc8c0e831e572303a0c795c8c0e831e57474222c599d027484f587409d213d61d027484f587409d213d61,0xc857088d5c72303a0c795c8c0e831e57474222c599c0a8e8731572303a0c795a1467151d1b1b1842674a,0xc1ab0852bc7334280d59cccd0a035673334280d59c7710a10ae73409d213d61c428e88f157409d213d61,0xccd0a035673334280d59cd1d088b1667334280d59cc81ae0373534a1a216959c6c61099d2b055c21c571,0xc81ae0373530a5a811d5c672b018abc30a5a811d5c] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_9s6 : Span p3_9 3 33 35 :=
  batch _ _ _ _ #[
0xc29710665cb40ab22ccd1c0a9585718f3062a3285dc15708715c7334280d59cccd0a035673334280d59c,0xccd0a035673334280d59cc198a85a1770662a1685dc88ae03ab53334280d59cc0a9585718f222b80ead4,0xcc23282e2d7155881e54cd1d088b1667322c40caf2c119585718f2303a0c795c8c0e831e57308ca0b8b5,0xc296a0475730a5a811d5c] 26 (by decide +kernel)

private theorem p3_9Good : Good p3_9 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_9s0 (joinSpan p3_9s1 p3_9s2)) (joinSpan (joinSpan p3_9s3 p3_9s4) (joinSpan p3_9s5 p3_9s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_10s0 : Span p3_10 3 0 5 :=
  batch _ _ _ _ #[
0xc1a32870ad7068ca1c2b5c1a32870ad7052b21cb91c5ca1072e2b308ca232b5cc23288cad7308ca232b5,0xc0aae0ace53441d21e561d10748795871622a2645dcc8aa035673322a80d59ccc8aa035673212b223b91,0xc818e88f157162541ea62c296a0475730a5a811d5cc296a0475730a5a811d5cc296a0475730a5a811d5c,0xc119585a98f055c214771cc1950ce98b308ca232b5c1a32870ad7334440d732ccd11035ccb334440d732,0xc119585718f0465615c63d190a847477260ca216b5c1a32870ad7066541ea62ccc0a839476a80e660cab,0xc296a0475730a5a811d5cc296a0475730a5a811d5cd190a8474773225435662d190a8474774642a11d1d,0xb08599530af3065435662aa10f1a1c5b3065435662c508e899957340ca0c6b5cd032831ad7162542e662,0xc1ca8852e67072a214b99cc23288cad7308ca232b5c15708715c7055c21c571d0a0e878c574283a1e315,0xd0a0e878c56e501656b03c19950b998b066542e662] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_10s1 : Span p3_10 3 5 10 :=
  batch _ _ _ _ #[
0xc296a0475730a5a811d5cd190a847477332842578ad190a8474774642a11d1dc119585718f0465615c63,0xcd422899a37066a811b9cc5562079533055c21c571c589507a98b462a214b99c296a047573162541ea62,0xc1a32870ad74468614b8bc857088d5c7215c223571cc23288cad7308ca232b5d11a1852e2f066a811b9c,0xd11a185662f446861598bd0a0e878c574283a1e315c84ac88ee47308ca232b5cc1aa02ae73306a80ab9c,0xccd11035ccb334440d732ccd11035ccb446861598bc118e87a1570463a1e855ccca108ee2b2223a23c55,0xc1a32870ad7072a214b99c14ac872e47052b21cb91c1570851dc7055c214771d11a185662f072a214b99,0xc14ac872e47052b21cb91c14ac872e47035c41c37270ea81566632a1c223571c88958b918f035c41c372,0xd1a228732374688a1cc8dcc8aa035673054c62c2b3c84ac88ee47212b223b917423a10f2b3074a82e29c,0xc6a6206b5332a4460ab33d11a1852e2f4468614b8bca87088d5c7046b819b946ae301ae2c3046b819b94,0xd18a88b16672a4460ab33ca91182accf1a9881ad4c] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_10s2 : Span p3_10 3 10 16 :=
  batch _ _ _ _ #[
0xd18a88b16670463a1cc55cc8aa035673332842578ad190a8474774642a11d1dca87088d5c742a8614b8b,0xcc1aa02ae73409d21ad61d2a0c8af447066a811b9cc19aa046e73035a81635cc0d6a058d73340ca216b5,0xd110e867457340ca216b5d19a1072e2b2a4460ab33cd032831ad7306a80ab9cc9832831ad7306a80ab9c,0xc8ca189562f260ca0c6b5cd032831ad7222b80d794d10ac8b1e47260ca216b5c9832885ad70662a14c5d,0xd027486b587035c41c372c0a9585718f02a5615c63c818e89995702a5615c63ca870889dc7312a225599,0x45cd41b9381d08e843cacccc0a839477152862558bd027486b5874a8322bd11d027486b587035c41c372,0xc15318b0acf115a83235cc0d6a058d73214c6252b3c0d6a058d73312a225599ccc0a839477442b21cb91,0xc457108cdcb054c62c2b3c8ca189562f051d21e561c1ca88b1667051d21e561c15318b0acd5233845cd4,0xc9832831ad7340ca0c6b5c9832885ad7446861598bc198a85a177340ca216b5c8ca189562f115c423372,0xc9832831ad7340ca0c6b5] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_10s3 : Span p3_10 3 16 21 :=
  batch _ _ _ _ #[
0xc9832831ad7074a82e29cc119585718f40ab21d991d190a8474774443a19d15d0aa185662f42a861598b,0xd0aa185662f42a861598bd1a2287a23742a861598bc1ca8852e67260ca0c6b5c9832831ad742a861598b,0xc0a8e87a15702a3a1e855d0aa185662f035c41c372c0d6a058d7310a3a33855c457108cdcb068ca198b5,0xd11a185662f409d213d61c50ae066e53332842578acc23282e2d7072a214b99cc23282e2d7308ca0b8b5,0xc88ae02ee532303a0e715d027484f5872303a0e715c589507a98b115a83235cd11a185662f035a81635c,0xc118e87a1555384645533c1474859d873062a3285d741d11163cb332842578ac198a85a177332842578a,0xc118e87a1541cea8a919c6685a16b0b3051d216761c508e8731570662a1685dcc18a8ca1771423a1cc55,0xc0d71070dcb4642a11d1dd190a8474774642a11d1dd190a84747742a861598bc50ae066e5342a861598b,0xd18a8852e67222b80bb94cc23282e2d70662a14c5dcc23282e2d7462a214b99] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_10s4 : Span p3_10 3 21 28 :=
  batch _ _ _ _ #[
0xc8c0e839c57306a80ab9cc1a328662d7068ca198b54e9d018abc3066a811b9cc84748c9d87046b819b94,0xc2a7086a5c7308ca0b8b5cc23282e2d72a4460ab33ca91182accf308ca0b8b5cc23282e2d7306a80ab9c,0xc843583aa8f0a5c419972d027484f587322a80d59cc843583aa8f3222a2645dc14358c6a8f322a80d59c,0xd0aa185662f308ca0b8b5c843583aa8f40ab21d991d10748795874443a19d15cc23282e2d7308ca0b8b5,0xc88ae02ee531744429732c6a6206b533334440d73254c0f10ec5b210d60eaa3c50958b918f308ca0b8b5,0xc88ae02ee534688a1cc8dce82a0c6a73334440d732d027486b5870a5c419972c88ae02ee53222b80bb94,0x741d11163cb055c214771d150c8b9c47334440d732c14748795871702a3151dc888e88f157334440d732,0xc296a047573308ca0b8b5cc23282e2d7152862558bc88ae02ee53222b80bb94d02ac8ae647308ca0b8b5,0xd1a2287a237066541ea62ca91182accf2a4460ab33ca91182accf046b819b94c296a047573222b80bb94,0xc119585a98f308ca0b8b5c81ae02ee53308ca0b8b5cc1aa02ae73306a80ab9c] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_10s5 : Span p3_10 3 28 34 :=
  batch _ _ _ _ #[
0xd027486b587409d21ad61c8d118354ce885ac5095ed027486b587072a214b99c5ca1072e2b409d21ad61,0xc14358c6a8f0a9c213971d110e8674574443a19d15c9832831ad7340ca0c6b5d027486b587409d21ad61,0xc9832831ad74688a1e88dd1a2287a237210d60eaa3c843583aa8f0a9c213971c8d118354cf42a861598b,0xc2a7084e5c6c216654c2bc55118a54cf0a9c213971c2a7084e5c74688a1e88dc296a047573260ca0c6b5,0xcc23282e2d7308ca0b8b5c81ae035e53206b80d794b026716a51b234460d533c8d118354cf02a3a1e855,0xc88ae02ee53234460d533c8c0e839c57462a214b99c50ae066e532708a2668dcc23282e2d7072a214b99,0xc8d118354cf1544629533c0a9585a98f2708a2668dc88ae02ee532303a0e715d027484f5870a5c419972,0xc29710665cb0a5c419972c8d118354cf234460d533c508e8731570662a1685dc8c0e839c572303a0e715,0xcc23282e2d7474222e519d190a8474770a9c213971c8d118354cf234460d533c2a7084e5c7474222e519,0xd18a8852e67222b80bb94cc23282e2d7234460d533] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_10s6 : Span p3_10 3 34 35 :=
  batch _ _ _ _ #[
0xcc23282e2d7306a80ab9cc199507a98b066a811b9cc8c0e839c573a4440bb32ce91102eccb3a4440bb32,0x5711190accf308ca0b8b5cc23282e2d7206b80bb94c81ae02ee53308ca0b8b5] 14 (by decide +kernel)

private theorem p3_10Good : Good p3_10 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_10s0 (joinSpan p3_10s1 p3_10s2)) (joinSpan (joinSpan p3_10s3 p3_10s4) (joinSpan p3_10s5 p3_10s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_11s0 : Span p3_11 3 0 5 :=
  batch _ _ _ _ #[
0xc14ac872e47066541dc62c199507718b1622a2645dcc1950af18b3222a3445dc84ac88ee47306542bc62,0xce90a02b5733a4280ad5cce90a02b5733a4280ad5cce90a02b5733a4280ad5cce90a02b5733a4280ad5c,0xccd11031dcb334440c772c0a7284ccd7029ca13335c0a7284ccd73065433a62c119585a98f055c215731,0xc888e8d19570465615c63c9832885ad74645419d62c888e88f157066541ea62c199507a98b1423a1cc55,0xc0a7284ccd7029ca13335c0a7284ccd7029ca13335a0bd11943cb3225435662d191506758b4645419d62,0xd1162859c374458a1670dc5d0a0c55728394655833cd032831ad6919466a833c58950b998b162542e662,0xc85708ad4c73a0a829c9cc84ac88ee47212b223b91d0a15858d8f4285616363aa10f181d5b2063a34655,0xc119585a98f052b225791d0a15858d8f066a811b9cccd0a0395731a83833354c118e899956e45c055730,0xcc1aa02ae73306a80ab9ccc1aa02ae730a5c419b32c2971066ccb0a5c419b32d11a1852e2f162541dc62,0xcc1aa02ae73306a80ab9c] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_11s1 : Span p3_11 3 5 11 :=
  batch _ _ _ _ #[
0xd18a88566672223a33855cd5220d5a331744421772c0a7284ccd7029ca13335c508e87a1574645419d62,0xa60791634ab212b223b91ce90a02b5733a4280ad5cce90a02b5733a4280ad5cce90a02b573462a215999,0xd11a185662f029ca13335d19a107662b0662a1685dc118e87a157446861598bd11a185662f055c215731,0xc0a8e873157162a82959cc0a8e873155d10ac44a9eca8708ad4c7035c41d332c118e87a157029ca13335,0xcc8aa035673322a80d59cc428e88f155d08e843cacc84ac88ee47054c6252b3c14ac872e4702a3a1cc55,0xc81ae02ee532708a2668dc0a8e87315710a3a1cc55c50728654d7046b819b94c428e88f157115c42b332,0xcc52a0b8a730463a1cc55c550e078d534445611d63d111584758f4445611d63c887282d4d7066541ea62,0xc85318b0acf10a3a1cc55ce90a02b573221ca0b535c887282d4d73a4280ad5cce90a02b573154381e354,0xcc1aa02ae73230560e563cc1aa02ae73054c6252b3c19aa046e73066a811b9cc19aa046e71d302c4455e,0xcd032831ad7152862558b] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_11s2 : Span p3_11 3 11 16 :=
  batch _ _ _ _ #[
0xc550e078d532a4380bd54ca90e02f5530a9c213b31c2a7084ecc70a9c213b31c2a7084ecc70a9c213b31,0xc1172845cd7045ca11735ce90a02b573072a225599ce90a02b573340ca0c6b5ca90e02f553074a83529c,0xc8172829cd7205ca0a735c0d71074ccb205ca0a735c42958ca98f205ca0a735c2a7084ecc7045ca11735,0xcc18a8ca1773a8882bc8cc1ca8895667230560e563782a614ee13072a225599c1ca88956651833a60cd5,0xca91182a5cf3a4440b972ce91102e5cb222b80d794c9832885ad7260ca216b5d11a185662f466841d98a,0xc550e078d532a4380bd54c119585718f42a861598bca8708a9cc74445611d63cd032831ad72a4460a973,0xc1172845cd7045ca11735c1172845cd7462a215999d18a8856667035c41d3327442b112a7b3a4280ad5c,0xc0a9585718f442b21d991c8172829cd7052b21cb91c8172829cd7205ca0a735d10ac87664710a562ac63,0xc45710acccb02a5615c63] 66 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_11s3 : Span p3_11 3 16 21 :=
  batch _ _ _ _ #[
0x434a5952e0d5233845cd4c1a328662d742a861598bc1172845cd7045ca11735c0a8e87a15742a861598b,0xcc23282e2d7115c42b332cc23282e2d74688a1e88dd1162859c37205ca0a73554e119115cf205ca0a735,0xc0a8e8731574298a13d0d4c6a61ad613066a811b9ccea220af2334298a13d0dcc1950ce98b462a215999,0xd111584758f4445611d63d0a6284f437330540e762c81ae02ee53206b80bb94cc1aa02ae733a8882bc8c,0xc550e078d532a4380bd54ca90e02f553154381e354c550e078d53154381e354d111584758f4445611d63,0xc818e8ce1573062a3285d6ae061cd513035c41d332ce90a02b573462a215999ce90a02b573306542bc62,0xca91182a5cf0662a1685dce91102e5cb3062a3285dc0d71074ccb154381e354c0d71074ccb02a5616a63,0xc1531894acf054c6252b3c1a328662d7162541dc62c589507718b046b819b94ca91182a5cf330540e762,0xc85318b0acf066541ea62c81ae02ee53308ca0b8b5cc1aa02ae73066541ea62] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_11s4 : Span p3_11 3 21 28 :=
  batch _ _ _ _ #[
0xcc8aa0356731a83819d54ca91182a5cf2a4460a973ca91182a5cf466841d98ad19a107662b322a80d59c,0xc887282d4d74645419d62ce90a02b5733a4280ad5cd0a6284f437221ca0b535c887282d4d71a83819d54,0xc81ae02ee53046b819b94c428e88f157435842e70ac887282d4d542c5c53166cc23282e2d7306542bc62,0xce90a02b5733a4280ad5cca8318a62cf206b80bb94c81ae02ee53306a80ab9cd10ac8766471744421772,0xc54a18b162f152862c58b5833298c2d5dc42842d5cc54628794356845650d63c199507718b4645419d62,0xc198a85a1770463a1e855d19a107662b2a4460a973ca91182a5cf466841d98ac589507718b440d629ca3,0xc81ae02ee53308ca0b8b5d02ac872e4702a5616a63c0a9585a98f230560e563c8c1583958f0662a1685d,0xcc23282e2d7206b80bb94cc23282e2d7206b80bb94cc1aa02ae730a5c419b32cc1aa02ae734688a1e88d,0xc42958ab18f3a4440b972ce91102e5cb3a4440b972ce91102e5cb3a4440b972c119585a98f055c215731,0xcd032831ad7210d60eaa3c198a85a1771a1c429732c0a8e88f157222b80d794d11a185662e90f446c0f2] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_11s5 : Span p3_11 3 28 34 :=
  batch _ _ _ _ #[
0xd1a2287a2374688a1e88dca90e02f5532a4380bd54ca90e02f553142b829794d111584758f4688a1e88d,0xc1172845cd7334280e55cccd0a0395731544621573c68710a5ccb0465615c63c508e8999571a1c429732,0xc843583aa8f210d60eaa3c8d118315cf234460c573c8d118315cf234460c573c8172829cd7462a215999,0xd0aa185662f045ca11735ccd0a0395734688a1e88d7423a10f2b302a5615c63c0a9585718f234460c573,0xc1a328662d690f446c0f2d0aa185662f174283155cc8172829cd7205ca0a735ccd0a039573334280e55c,0xc8d118315cf055c21d531d18a8856667306a80ab9ccc23282e2d7234460c573cc23282e2d7234460c573,0xc9c22899a371544621573d0a6284f437334280e55cc81ae02ee53206b80bb94cc1aa02ae73234460c573,0x5833298c2d7306542bc62c8d118315cf066541dc62ca90e02f5532a4380bd54d111584758f0a9c213b31,0xce91102e5cb3a4440b972ce91102e5cb3a4440b972ce91102e5cb3a4440b972d18a8856667462a215999,0xc118e87a157334280e55cc0a9585a98f0662a1685dc118e87a1570463a1e855c2a7084ecc73062a3285d] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_11s6 : Span p3_11 3 34 35 :=
  batch _ _ _ _ #[
0xc2971066ccb306a80ab9cc19aa046e73052b225791c1a328662d7334280e55ccc1aa02ae73306a80ab9c,0xc2971066ccb0a5c419b32c81ae02ee53308ca0b8b5] 12 (by decide +kernel)

private theorem p3_11Good : Good p3_11 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_11s0 (joinSpan p3_11s1 p3_11s2)) (joinSpan (joinSpan p3_11s3 p3_11s4) (joinSpan p3_11s5 p3_11s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_12s0 : Span p3_12 3 0 5 :=
  batch _ _ _ _ #[
0xd1162851e374283a1e315d0235858d8f441d21d5a1a0c4f17285b346882e68cc2a2e0ccd53346882e68c,0xd1d2107352b474841cd4ad1d2107352b1b18423b8ad1d2107352b4283a1e315d0a0e878c570665435662,0x7463110e5c9d18c443972d190a8474769194655833d190a8474774642a11d1dc5562055e33155881578c,0xc1d2a047573074a811d5cce82a0395733a0a80e55cce82a039573408d616363ca8318855cf312a226a99,0xd1d2107352b4458a1c58dd152185352f074a811d5cd1074855e87074a811d5cca9620ad6330a8b833354,0xd0235858d8f074a811d5ccc52a02b573314a80ad5ccc52a02b573314a80ad5cd1d2107352b474841cd4a,0xcc52a02b573408d616363d0235858d8f4548614d4bc198a8d11774548614d4b7463110e5cb4742215d19,0xd183506758b460d419d62c0ab18b0acf460d419d62cc52a02b573314a80ad5ccc52a02b573314a80ad5c,0xd11628716372223a23c55c888e88f1574283a1e315c508e8731572a44629533c2a2e078d530a8b81e354,0xc888e88f156a84667052b] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_12s1 : Span p3_12 3 5 10 :=
  batch _ _ _ _ #[
0xcc52a02b5731a1a811b9cd1d2107352b1a1a811b9cc686a046e73211d22b5a1c1474875687074a811d5c,0xc5562055e330465615c63c1474875687051d21d5a1c88958ca98f314a80ad5ccc52a02b573314a80ad5c,0xc818e88f157235882a78cc1474875687206562ac63c118e8731570662a14c5dc686a046e731a1a811b9c,0xc2a2e0ccd530a8b833354c1d2a047573074a811d5cd1074855e87441d2157a1d150c877447454321dd11,0xcc52a02b573314a80ad5ccc52a02b573314a80ad5ccc52a02b5733a0c421772d1074855e87074a811d5c,0xc1c350c5d8b4a5842b98ad1074855e87262c22c6b1d1d2107352b4548614d4bc508e8d1957314a80ad5c,0xcc435039d8b314a80ad5ccc52a02b573314a80ad5cd1d088574674742215d19d0235858d8f074a811d5c,0xcc88a88b1770463a1e855cc88a88b177460d419d62c2a2e078d53155881578ccc435039d8b310d40e762,0xc818e8ce1571423a1cc55c8d620a9e331622a14c5dc2a2e078d523431a8ccc5] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_12s2 : Span p3_12 3 10 17 :=
  batch _ _ _ _ #[
0xce82a039573314c423372c456a054e7302a3a1cc55c5511854ccf115a81539cc0a8e873157314c423372,0xc5d11074ccb1a98813b8cc1d31070dcb409d213ba1d1074875687312a226a99ce82a039573441d21d5a1,0xcc18a899177334442b332cc1aa037273310d40e762c5d11074ccb4642a11d1dd190a8474771518a1478d,0xc8531888dcf2a0b80e754d11628716372a0b80e754ca9620ad63102f4a540f5c1531850dcf2223a26655,0xc1d31070dcb3b0842674ac0a8e873157070d431762c0a8e873157174441d332c6c6108ee2b4458a1c58d,0xccd110acccb440d611d63d103584758f440d611d63d103584758f174441d332cc8aa03aa732303a0e715,0x5463190a5cf054b81e354ca82e02f551518c642973cec21099d2b2065635463c1531850dcf054b81e354,0xc5d11074ccb409d21aba1c6a6204ee33054c614373c6a6204ee33174441d332c456a054e730662a14c5d,0xcac2189952dd234444af2cc53108cdcb314c423372cc1aa0372731423a26655c0d6a0a8e73174441d332,0xc1d31070dcb210d60e563c428e88f15710a3a23c55660ab182a7b3302a0e51dc818e8999571544615333] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_12s3 : Span p3_12 3 17 22 :=
  batch _ _ _ _ #[
0xc152e078d532a0b80bd54ca82e02f5531a98813b8cc1531850dcf460d419d62c0a9585a98f4a8321eb11,0x77031111dc9dc0c444772c1d31070dcb4a8321eb11d2a0c87ac473302a0e51dccc0a839477409d21aba1,0xca82e039d515303c43b165487a109eb3441d2157a1c5511854ccf1544615333cc4a889aa67174441d332,0xd110e8674574443a19d1574c0b10ac7b054c614373d1074855e871544615333c5d11074cc940cdc5a166,0xc81958ab18f1544615333ca82e039d534642a11d1dc119585718f4642a11d1dc5511854ccf174441d332,0xc0a8e87a1571544615333d0a6286a6372b03233b11d1074855e87306a80dc9cc1ca88d2a67174441d332,0xca82e02f5532a0b80bd54d0a6286a6371622a14c5dc1ab08762c7054b81e354d183506758b460d419d62,0xc8531888dcf214c622373c8d118a8ccf174441d332c5d11074ccb3b0842674ac1d31070dcb4298a1a98d,0x539727419b174441d332c8c0e839c57322a80ea9cc1d31070dcb211d22a7a1c8c62889e372318a2278d,0xc1d31070dcb310d40e762] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_12s4 : Span p3_12 3 22 28 :=
  batch _ _ _ _ #[
0xc6a6204ee331518a1478dc152e078d53440d611d63c5d11074ccb440d611d63c6a6204ee333b0842674a,0xc5d11074ccb4a8861694bc5d11074ccb06ac21d8b1ca82e02f553409d213ba1c1531850dcf1423a1cc55,0xd2a2185a52f174441d332c5511854ccf4642a11d1dc1474855e87051d2157a1d190a8474771544615333,0xd0a6286a6374298a1a98dd1d2107352b4742215d19cac0c8cec474298a1a98dcc435039d8b0662a14c5d,0xd1d2107352b214b80bd54c19950d598b4298a1a98dc852e02f553306542e662cd1a20b9a33346882e68c,0xd027484ee872a0c621573c852e02f553206c60d8b3c81b18362cf206c60d8b3c6a6204ee33310d40e762,0xc81b18362cf206c60d8b3d10748756873a0a80e55cce82a0395733a0a80e55cc81b18362cf310d40e762,0xce82a0395733a0a80e55cc852e039d530a8b819d54c1ca88d2a67155881578cc5aa2077233222562e463,0xd190a847477155881578cd0a6286a637306a80dc9cce82a0395733a0a80e55cce82a0395733a0a80e55c,0xc5562055e33306a80dc9cc0a8e8ce15540cdc5316694278a0e6a74298a1a98d] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_12s5 : Span p3_12 3 28 34 :=
  batch _ _ _ _ #[
0xb81519950cf074a811d5cd150c8774472a5882b58cd1d088574672a5882b58ccc52a02b573314a80ad5c,0xcc435039d8b314a80ad5cc2a318465cf0a8c611973c2a318465cf314a80ad5cce831085dcb074a811d5c,0xd0a6284e637322a80ea9cc852e02f5534742215d19c1ab08762c7222c60cab3c8c0e839c57310d40e762,0xc296a0a5673460d419d62d183506758b440d611d63b81519950cf440d611d63c428e8ce1568c5466c433,0xc98b0895ac7314a80ad5cd0a6284e6370a8c611973d0a6284e6370a8c611973c296a0a56730a8c611973,0xc81b18362cf206c60d8b3c6a11846ccf314a80ad5cd027486ae87206c60d8b3c81b18362cf3302a0e51d,0xc88b1832acf210d60e563d150c877447054b819d54b084f17285b054b819d54cc52a02b573314a80ad5c,0xb0b0b1a847b051d21d5a1c5aa20772332318a2358dc852e02f5531a1a811b9cc2a318465cf4298a1a98d,0xc843583958d17350754e0c686a046e733302a0e51d] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_12s6 : Span p3_12 3 34 36 :=
  batch _ _ _ _ #[
0xc118e87a157409d21aba1c118e87a157206c60d8b3c588a8531774a8321eb11d027486ae872318a2358d,0xd110e86745706ac21d8b1c81b18362cf3302a0e51dccc0a839475680d650d63cc88a88b177409d21aba1,0xc81958ab18f222c60cab3d0a6286a636c2c2c6a11ecec088b94674443a19d15d0d610b1e2b4443a19d15,0xc686a046e731a1a811b9cd0a6286a637454322e711] 28 (by decide +kernel)

private theorem p3_12Good : Good p3_12 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_12s0 (joinSpan p3_12s1 p3_12s2)) (joinSpan (joinSpan p3_12s3 p3_12s4) (joinSpan p3_12s5 p3_12s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_13s0 : Span p3_13 3 0 4 :=
  batch _ _ _ _ #[
0xc1c35066e8b3b08423b8ac1c35066e8b070d419ba2d0d6107352b435841cd4ad0235854e8f435841cd4a,0xd150c877447441d21e561d107487958710ac6252b3d1074879587266882e68cc19950b998b435841cd4a,0xc199507a98b02ac62c2b3c1c350a5e8b2a1c2235719590b206c7b2a1c223571d0235854e8f2a1c223571,0xd0235854e8f435841cd4ace91102eccb3a4440bb32ce91102ecc9c215c6b426d0235854e8d9115c55626,0xc6871085dcb162542e662cec2108ee2b206562e463cec2108ee2b0a8b82b394d0d6107352b435841cd4a,0xcc18a899176558868598bc508e8999563215c8d626c2a2e0ace53435841cd4ad150c877445898aa5099d,0xc1474859d87162541ea62c589507a98b162541ea62c81958b918f3062a2645dcc18a8991741715ca9626,0xd02358a8e8f408d62a3a3c589507a98b3225433a62] 60 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_13s1 : Span p3_13 3 4 8 :=
  batch _ _ _ _ #[
0xc1570851dc7055c214771c508e873157055c214771c0ab18b0acf02ac62c2b3c5d110a5ccb1744429732,0xc1570851dc7046562e463c54a189aa2f1423a1cc55c0ab18b0acf2328634a8bd0235854e8f408d6153a3,0xd0d6107352b0465616a63b9c28152e63408d6153a3d0235854e8f2223a23c55c42b1894acf408d6153a3,0xce91102eccb454321dd11c119585a98f2a0b829794d0d6107352b435841cd4acd0b0895ac7460d4297a2,0x119572a589b2063a26655d1835066e8b460d419ba2ce91102eccb3a4440bb32ce91102eccb3a4440bb32,0xc99a20b9a33408d62a3a3d0d61073529dc0a842b9cc99a20b9a33435841cd4aa146717151b460d419ba2,0xa46519560cf055c214771c509585718f1425615c63c84748cd5873065433a62c88958ca98ea843c68716,0xc8d620c9d332065632a63d02358a8e8f1a1a811d5cc119585a98f1a1a811d5cc686a047573211d233561] 64 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_13s2 : Span p3_13 3 8 13 :=
  batch _ _ _ _ #[
0xd150c877447454321dd11d0235854e8e885ac5095ed1074859d87441d216761cec2108ee2b0a8b82b394,0xc98b08b1ac6c419c54746c2a2e0ace52961685662cc2a2e0ace53454321dd11cec2108ee2b0a8b82b394,0xb0b0b15447b1425616a63c2a2e0ace53454321dd11d0235854e8f408d6153a3c198a85a177441d216761,0xd02358a8e8f0662a1685dc29710665cb0a5c419972c88958ca98ec05665682bc88958ca98e885ac5095e,0xc1c35066e8b070d419ba2c509585718f1425615c63c88958ca98f2225632a63b0b0b15447b162541ea62,0xcc88a88b1770662a1685dc29710665cb1a1a811d5ccc88a88b174189dc98366d296107a52b4a5841e94a,0x70ad41573831a98813d4cc6a6204f5319194a53835cc43502ee8b310d40bba23706a2075731622a14c5d,0xcec2108ee2b310d40bba2c457108cdcb070d419ba2c1c35066e8b1a98813d4cc852e0ace531544615333,0xc6a6204f5331b1842674ad027484f585ad0d06a7a0c6c61099d2b10a5615c63c0a958ab18f1622a2645d,0xc152e074e534a8322bd11c0d6a0c8d732a1c223571] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_13s3 : Span p3_13 3 13 19 :=
  batch _ _ _ _ #[
0x473129684d50ace8531ac54c0f10ec5b3225435662c1435846e8f3b08423b8ac1435846e8f050d611ba3,0xc0a9585718f02a5615c63d027486b587409d21ad61c843582ae8f409d21ad61c843582ae8f02a5615c63,0xca82e02ee53054b81d394c81958b918f035c41c372d2a0c8af447409d213d61d0aa18b322f440d611ba3,0xc508e873157035c41c372c5aa207aa3306ac21cab115ad0a12bc7462a22cc99ca82e02ee53162541ea62,0xc6a6204f533262c22c6b1c1ab0872ac7322a80dc9cc0d71070dcb051d216761c58aa0a72731423a1cc55,0xc843583568f3a4440bb32cd0b0895ac7409d21ad61c6a6204f533460d4297a2c429585718d5c44642b33,0xd1835066e8b02a5615c63d1835066e8b1a98813d4cc0a9585718f02a5615c63c0a958ab18f3a4440bb32,0xca82e02ee53035a83235cd027486b587409d21ad61ca82e02ee5302a5615c63c6a6204f533460d419ba2,0xcc8aa037273322a80dc9cc0d71070dcb162a829c9cd2a0c87ac47035c41c3726262a9426771622a14c5d,0xc843583568d6a19853d4474c0b11547b06ac21cab1] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_13s4 : Span p3_13 3 19 24 :=
  batch _ _ _ _ #[
0xc6a6204f533210d60aba3c0a958ab18d0ace8531acc5511854ccf3b08423b8acec2108ee2b1a98813d4c,0xc1c35066e8b3222a22c5dc1435846e8f3b08423b8ac0a958ab18dd302c42b1ec8d118a8ccd5384645533,0xcc43502ee8b346883568cc843582ae8f035c41c372c5511854ccf070d419ba2c2a7084e5c73222a22c5d,0xc152e074e534a8322bd1152e059b940f054b81d394c5511854ccf440d611ba3cc1950d598b0a9c213971,0xc5aa207aa33211d232761ca82e02ee532a0b80bb9470ad41ab383162541ea62c152e074e531544615333,0xcc8aa037273322a80dc9cc118e87a157051d216761c1c350a5e8b0463a1e855cc88a88b1770662a1685d,0xc5511854ccf0a9c213971c81b18362cf206c60d8b3cc435035e8b310d40d7a2cc18a8ca1771622a14c5d,0xd18a88b32673a4440bb32ce91102eccb1622a14c5dc588a853177234462a333cc88a88b1773222a22c5d,0xc2a7084e5c54631a54cc5d18a88b32673065433a62] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_13s5 : Span p3_13 3 24 30 :=
  batch _ _ _ _ #[
0xd0d6107352b070d419ba2d150c877447441d21e561cac0c8cec472b03233b11d0d6107352b1622a2645d,0xc429585a98f310d40d7a2cc43502ee8b441d21e561cc43502ee8b310d40bba2d150c877447070d419ba2,0xcc435035e8b310d40d7a2665191634ab16a881ea8cc1c350a5e8b10a5616a63c81b18362cf046c6298b3,0xa606b18157b066a831a9cb832a1546733a4440bb32ce91102eccb3a4440bb32c81b18362cf206c60d8b3,0xcc1aa03aa71e80aa6059d644571558995c44642b3379434155e8310a3a1e855cc88a8d11773222a3445d,0x74c0b10ac7b214b80d794d027484f5874a5841e94ad296107a52b10a5615c63cc43502ee8b310d40bba2,0xb026716a51b2a5883354cc29710665c9915685662cc429585718f310d40bba2cc43502ee8b310d40bba2,0xc843582ae8f10a3a1e855c2a7084e5c70a9c213971c843582ae8f10a3a1e855a727016a5c3050d611ba3,0xca82e02ee532a0b80bb94c2a7084e5c7142c621ab3d150c877447454321dd1160c5714e89b454321dd11,0x4217716159b3225433a62ca9118a54cf051d216761c589507a98b211d232761ca82e02ee532a0b80bb94] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_13s6 : Span p3_13 3 30 36 :=
  batch _ _ _ _ #[
0xcc43502ee895303c43b16b026714e51b1744429732c843582ae8f2065635463c1435846e8f310d40bba2,0xa216b14257b162542e662c5aa207aa3316a881ea8cc852e035e53214b80d794c11958b918f310d40bba2,0xc843583568f0662a1685dc429585a98f460d4297a2c843583568f210d60d5a3d18350a5e8b10a5616a63,0xd0d6107352b0a9c213971c843583568f454321dd11c843583568f3a4440bb32ce91102eccb3a4440bb32,0xca82e02ee50695a2a0d59c50b1886acf142c621ab3cc1aa03aa73454321dd11ca82e0a5e53454321dd11,0xd1835066e8b334440d732c509585a98f435841cd4ad150c8774472a0b80bb94ca82e02ee532a0b80bb94,0xc589507a989e054a53835c589507a98b409d21ad61d027486b587055c214771d1835066e8ae099853d44,0xc588a8531774a5841e94accd11035ccb334440d732c29710665cb3225433a62ccd11035cc9680d650ba3,0xc6a11846ccf474842c78accd11035ccb334440d732c843583568f210d60d5a3d296107a52b055c214771,0xc843583568f210d60d5a3c6a11846ccf055c214771] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_13s7 : Span p3_13 3 36 37 :=
  batch _ _ _ _ #[
0xc81958ca98f066541ea62c509585718f3065433a62cc1950ce98ae29c053970b8a7014e5c31622a14c5d,0xc843583568f1a1a811d5cc84748cd587235883274c] 12 (by decide +kernel)

private theorem p3_13Good : Good p3_13 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan (joinSpan p3_13s0 p3_13s1) (joinSpan p3_13s2 p3_13s3)) (joinSpan (joinSpan p3_13s4 p3_13s5) (joinSpan p3_13s6 p3_13s7)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_14s0 : Span p3_14 3 0 5 :=
  batch _ _ _ _ #[
0xd1162851e371742811d5cd152185742f1742811d5cc6a0e0ccd53346882e68cc5d0a0475731742811d5c,0xccd0a02b573334280ad5cccd0a02b573334280ad5cd1074875687441d21d5a1cd1a20b9a33454321cd51,0xca8318a54cf1518a1478dca8318a54cf4742214d59d1d088535674285616363d152185742f1742811d5c,0xd191506758b4645419d62ccd0a02b573334280ad5cccd0a02b573334280ad5cccd0a02b5734742214d59,0xc118e8731572a0c629533c818e88f1572063a23c55c42b18b0acf155881578cc6a0e078d531a8381e354,0xca9620ad632c39a055998ca9620ad6331a83833354d1074875687441d21d5a1aa0399c14af155881578c,0xd022e878c574458a1c58dd1162871637474841dd0ac0ab1894acf4458a1c58dd1074855e87342c2256b1,0xc58aa0a72732223a23c55d182a8474774458a1c58dc888e899956e419855784c0ab1894acf4458a1c58d,0xce90a039571d38444397274e1110e5cb4285616363ca9118855cf4458a1c58dd182a847477460aa11d1d,0xce90a0395733a4280e55c] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_14s1 : Span p3_14 3 5 10 :=
  batch _ _ _ _ #[
0xc5462871637408ba1e315c296a046e730a5a811b9cd1d2107742b0a5a811b9cc5d0a047573342c2256b1,0xc5562055e332318a2358dccd0a02b573334280ad5cccd0a02b573334280ad5cc888e8999572065632a63,0xc6a0e078d53235882a78cc5462871637051d21d5a1cac218b942f0a5a811b9cc588a8531770a5a811b9c,0xd022e878c57408ba1e315d152185742f1742811d5cc6a0e0ccd53346882e68cc5d0a0475731742811d5c,0xd1d088535674742214d59c1ca88d2a674458a1478dd150c873547474841dd0ad152185742f4548615d0b,0xd152185742f1742811d5cccd0a02b573334280ad5cccd0a02b573334280ad5cccd0a02b573334280ad5c,0xccd0a02b573330540e762ccc15039d8b330540e762c508e87a157211d22a7a1d152185742f051d2157a1,0xc508e87a1573062a22c5dc6a0e078d530465615c63cc18a88b177155881578cccd0a02b573334280ad5c,0xc198a8531771a8381e354b8c6818ae632223a33855c118e873157206562ac63] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_14s2 : Span p3_14 3 10 16 :=
  batch _ _ _ _ #[
0xc54a18d2a2f2a4380e754d1162851e37441d21d5a1c5511850dcf2063a26655cc88a899177314c42b332,0xc428e8731572b03226751c428e873157074c41d332d10748756871528634a8bd10748756872a4380e754,0xd111584758f074c41d332d111584758f4445611d63cc1aa03aa73210ba0e715c5d11070dcb16a881dc8c,0xca90e02f553446862cc8bcc2b088eac72225635463c6a6204ee33154381e354d027484ee874445611d63,0xc0d6a054e73441d2157a1c1531854ccf035a81539cc428e8731573344423372d11a18b322f154381e354,0xd2a2185ac2f409d213ba1c888e8999574458a1c58dce90a03957302a3a23c55ce90a0395734458a1c58d,0xcc8aa037273330540e762c1d31074ccb460aa11d1dd182a847477035a81539cc1d31074ccb02a5616a63,0xc0a8e88f15702a3a23c55c888e8999572318a2358dc1531854ccdd074444af2ccd1108cdcb3344423372,0x7aa0614f513310aa0e51dc5d11070dcb230560e563] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_14s3 : Span p3_14 3 16 21 :=
  batch _ _ _ _ #[
0xc5d11070dcb409d21aba1d027486ae871a98813b8cc0d6a054e731a98813b8cc6a6204ee333344423372,0xc588a853177035a81539ccc42a839477310aa0e51dc8d11888dcf154381e354ca90e02f5532a4380bd54,0xc99a20d5a33322a80dc9cd027486ae87409d21aba1c0d6a054e731544614373c6a6204ee3302a5616a63,0xc1531854ccf154381e354d191506758b4645419d62d0a6286a6374a8321e951c1d31074ccb074c41d332,0xc198a853177154381e354c5d11070dcb214c62a333ca90e02f5532a4380bd54d2a0c87a547441d2157a1,0xc8d11888dcf054c615333c1531854ccf2328626a8bc1d31074ccb312a226a9977111111dcb214c62a333,0xcc1950b998b054c615333d1162851e371528634a8bca90e039d531528634a8bc1ca88d2a671544614373,0xcd1a20b9a33054c615333d182a8474771425615c63d182a847477440ba19d15d102e867457074c41d332,0xc1d31074ccb4298a1a98dc1531854ccf2a4380e754c0a8e87a157322a80dc9c] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_14s4 : Span p3_14 3 21 27 :=
  batch _ _ _ _ #[
0xc8d11888dcf2344622373c19aa0c6a732b03226751c1d31074ccb16a881dc8cc5aa2077233074c41d332,0xc842e839c57306a80ea9cc5d11070dcb16a881dc8cc5d11070dcb330540e762ccaa20af233074c41d332,0xd2a2185ac2f1544614373c550e078d534445611d6374439119cab30ac223ab1d111584758f074c41d332,0xc589507718b074c41d332d0a6284e637074c41d332c118e873157446862cc8bd11a18b322f2a4380bd54,0xccc15039d8b1622a14c5dd0a6284e637460aa11d1dc1531854ccf460aa11d1dc509585718f1425615c63,0xd0a6286a6374742214d59c1ab08762c7474841dd0accd0a02b573334280ad5cc1d31074ccb054c615333,0xc6a118465cf1a84611973c6a118465cf334280ad5cd0a6286a6371742811d5ccd1a20b9a331742811d5c,0xd0a6284e6374742214d59670529710d7206c60cab3c842e839c57330540e762ccc15039d8b334280ad5c,0xd191506758b4445611d63d2a0c87a5474445611d63d2a0c87a5474298a1a98dcc1aa03aa73234380bd54,0xd0a6284e6371a84611973ca8318a54cf1a84611973cc2b08ae2c71a84611973d0a6286a637155881578c] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_14s5 : Span p3_14 3 27 33 :=
  batch _ _ _ _ #[
0xa620f16255a9cc287215ccd0b0895ac682f44650f2ca9620ad6331543819d54d1d2107742b474841dd0a,0xc550e067553330540e762425399434af234380bd54d1d2107742b474841dd0ac8d0e02f553441d2157a1,0xc888e8ce157222c60d8b3ccc15039d8b2a44621573c8d0e02f553222c60d8b3c88b18362cf222c60d8b3,0xc8d0e039d531a83819d54c88b18362cf222c60d8b3c42958ab18f3a4280e55cce90a0395733a4280e55c,0xce90a039573322a80dc9cce90a0395733a4280e55cccaa20af23332a882bc8cc81958b918f4458a1c58d,0xcc2b08ae2c55c44644573d182a8474774a8321e951d2a0c87a5473a4280e55cce90a0395733a4280e55c,0xc550e067553334280ad5cccd0a02b5731543819d54d0a6284e636354e08e7285417a10d6b3322a80dc9c,0xc8d0e02f5531a84611973c296a046e73474841dd0ac81b1832acf4298a1a98dc8c1583958f474841dd0a,0xc2a31846ccf334280ad5cd1d2107742b222c60d8b3c88b18362cf310aa0e51dccd0a02b573409d21aba1,0xc88b18362cf222c60d8b3] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_14s6 : Span p3_14 3 33 36 :=
  batch _ _ _ _ #[
0xc296a046e73310aa0e51dc8c1583958f211d22b5a1cec08899567051d21d5a1c5aa20772332318a2358d,0xc508e87a157409d21aba1d027486ae87222c60d8b3c198a8531772063a23c55c818e88f157409d21aba1,0xc589507718b440ba19d15cc42a839477310aa0e51dc88b18362cf2063a23c55c508e87a15730ac223ab1,0xc1ab08762c7206c60cab3d0a6286a6374a8321e951c147487568706ac21d8b1d102e867457440ba19d15,0xc296a046e730a5a811b9cd0a6286a635674c055730] 36 (by decide +kernel)

private theorem p3_14Good : Good p3_14 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_14s0 (joinSpan p3_14s1 p3_14s2)) (joinSpan (joinSpan p3_14s3 p3_14s4) (joinSpan p3_14s5 p3_14s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_15s0 : Span p3_15 3 0 4 :=
  batch _ _ _ _ #[
0xcc88a899177222562e463d0568853567415a214d59cc88a8991772a1c223571d0568853567441d21e561,0xd1074879587072a226a99c1ca889aa672a1c223571c8ca189aa2f441d21e561d1074879587066542e662,0xc199507a98b4548615d0bc88958b918f3222a2645dd0568853567415a214d59cc88a8991772a1c223571,0xc1d310a5ccb02ac6252b3ca87088d5c7428562a3a3c199507a989dc42842b9cc199507a98b066541ea62,0xc118e8731569194655833c42b18b0acf10ac62c2b3c1d310a5ccb074c429732d0a15854e8f42856153a3,0xc42b18b0acd9982a5099dd0a15854e8f42856153a3c5562059d33155881674cd0a15854e8f2225635463,0xcd0b0895ac72b03223b91d05688535668394655833c8d620c9d33142562e463c5562059d330463a1cc55,0x60e5294e0d71423a34655c58950b998b342c2256b1c5c15066e8b1a8382b394d0568853567415a214d59,0xc6a0e0ace532b03223b91c0ab1894acf02ac6252b3] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_15s1 : Span p3_15 3 4 9 :=
  batch _ _ _ _ #[
0xc1474859d87162541ea62d0568853567415a214d59ca9620cd5333062a3445dd0568853567051d216761,0xcd0b0895ac72223a26655ce83102eccb3a0c40bb32ce83102eccb415a214d59615c615731342856153a3,0xc81958ca98f262c22c6b1c508e8d1957342c2256b1d1915066e8aac19872744d1915066e8b4645419ba2,0xc6a0e0ace531a8382b394c509585a98f162a831a9cc98b08b1ac71423a34655d0a158a8e8ee054654a33,0xce83102eccb3a0c40bb32ce83102eccb346883568cc509585a98f2a43829794d19150a5e8b46454297a2,0xd58729591b3225433a62c119585718f0465615c63c0ab1894acf055c214771ce83102eccb3a0c40bb32,0xc2c688995670b1a226559c2c68899567474842e70ac296a047573155881674cc296a0475730a5a811d5c,0xae119181eab2b03223b91d152185742f4548615d0ba606b14257b2b03223b91d0a15854e8f2b03223b91,0xd152185742e981ac5095ed0a15854e8f42856153a3c588a85a1758c54a54635b032b15447b2b03223b91,0xb032b15447a3055c8d626c99a20b9a331a8382b394c99a20b9a331a8382b394] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_15s2 : Span p3_15 3 9 14 :=
  batch _ _ _ _ #[
0xc68710665cb1622a1685db032b15447b051d216761d152185742f4548615d0bc84748c9d86981ac5095e,0xcc18a88b177215c222771b032b15447b066541ea62d0a158a8e8f4548615d0bc84748c9d874548615d0b,0xcc18a88b1771622a1685dd286885a5674a1a216959c119585718f0465615c63d286885a5674a1a216959,0xc5415846e8f1505611ba3d286885a5670662a14c5dccc1502ee8b330540bba2c68710665cb0a5a811d5c,0xc8c1582ae8f1a98813d4cca87088d5c71a98813d4c5442f10ec5b2a1c223571c5415846e8f266882e68c,0x443d29503d74445611ba3c6a6204f53310a5615c63c1ca889aa672a1c223571c8c1582ae8f02a562ac63,0xca90e02ee53066541ea62ca90e02ee53154381d394c88958b918f115c41c372c6a6204f533234382b394,0xd2a2185ac2f0463a1cc55d2a2185ac2f115c41c372c88958d518f4a88616b0bc1ab0872ac74a88616b0b,0x7aa3014ecc3306a80dc9cc4571070dcb2a1c223571] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_15s3 : Span p3_15 3 14 20 :=
  batch _ _ _ _ #[
0xc5c15066e8b054c615333c8d0e0ace53054c615333c98b08b1ac7035a81635cc0a9585718d8394a53835,0xd027484f58702a5615c63d027486b587409d21ad61d027486b587330540bba2d027486b5871705419ba2,0xc550e074e53115a83235cc456a0c8d7317054297a2c1531854ccf17054297a2d027484f585ca8e053d28,0xc6a6204f533054c615333c429585718f4645419ba2d1915066e8b1a98813d4cc0d6a058d7310a5615c63,0xc4571070dcb0662a14c5dc508e8d195702a562ac63ca90e02ee532a4380bb94d027486b5871a98813d4c,0xcc1aa037273306a80dc9cc8c1583568f16a881ea8cc19aa0a7273115c41c372541ce1173519982a5099d,0xc6a6204f533054c615333c2c6889956702a5615c63c0a9585718f0b1a2265597442b115479d10ac4551e,0xcc18a88b1771505611ba3ce83102ecc9e054a54635c2c68899567409d21ad61ce83102eccb230560d5a3,0xcec210cec2b330540bba27442b10ac7b441d216761d1074859d87214c62a333cc18a88b1770a9c213971,0xc8c1582ae8f115c41c372c2a7084e5c7441d216761] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_15s4 : Span p3_15 3 20 26 :=
  batch _ _ _ _ #[
0xc6a6204f533214c62a333c1531854ccf2b03223b91c6a6204f533266882e68cc99a20b9a33214c62a333,0xc550e074e531a98813d4c42e661795134445611ba3c99a20b9a33266882e68cc8c1582ae8f10a562ac63,0xc199507a98b409d213d61c1531854ccf2a4380bb94ca90e02ee51cb8a06e518d027484f587054c615333,0xc5c150a5e8b051d216761c508e87a1551ac68531acc50b18a62cf16a881ea8cc5aa207aa331622a1685d,0xc1ab0872ac70662a14c5dcc1aa037273306a80dc9cc88b18362cf222c60d8b3ccc15035e8b330540d7a2,0xc84748c9d873225433a62cc8950ce98b054c615333c85318a8ccf3062a22c5dcc18a88b1773062a22c5d,0xc1ca889aa67072a226a99ce83102eccb3a0c40bb32c198a8531770662a14c5dc509585a98f211d232761,0xc8c1582ae8f415a214d59cec210cec2b441d21e561c8c1582ae8f02a3a1e855d05688535671505611ba3,0xca90e02ee532a4380bb94c0a8e87a157046c621ab35442f10ec5b346883568cd10748795870a5c421772,0xca8318a54cddc42842b9cc199507a98b4548615d0bd152185742d6845650ba3ca90e02ee532a4380bb94] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_15s5 : Span p3_15 3 26 32 :=
  batch _ _ _ _ #[
0xc8d0e035e53072a226a99cc4a88d2a67074c429732c8c1582ae8f330540bba2c88958d518f1505611ba3,0xc2a7084e5c7415a214d59c2a7084e5c70662a2645dc50958b918f330540bba2ccc1502ee8b234380d794,0xccc1502ee8b330540bba2cd0b0895ac7415a214d59c2a7084e5c7415a214d59cec210cec2b046562e463,0xc5c150a5e8b02a5616a63c88b18362cf06ac21cab1c0a9585a98f330540d7a2ccc1502ee898315c53a26,0xce83102eccb3a0c40bb32c1ab0872ac72223a33855c88b18362cf222c60d8b3ccc15035e8b330540d7a2,0x625391634ab415a214d59c2a7084e5c70a9c213971d2a0c8ae6474a8322b991d2a0c8ae6473a0c40bb32,0xd027486b587330540bba2ccc1502ee8b02a5615c63d0568853567322a80ea9cd0aa18ba22f051d216761,0xd027484f585835685662cc1570851dc7330540bba2d027486b5874a1a216959c1570851dc7234380d794,0xca90e02ee532a4380bb94ca90e02ee530a9c213971c11b1886acf046c621ab3ccc1502ee8b330540bba2,0xc119585a98d181dc50766cd0b0895ac72a4380bb94] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_15s6 : Span p3_15 3 32 37 :=
  batch _ _ _ _ #[
0xc1474879587230560d5a3c8c1583568f06ac21cab1c0a9585a98f462a22e899c19950b998b462a22e899,0xc8c1583568f3a0c40bb32ce83102eccb3a0c40bb32c8c1583568f1622a1685dd19150a5e8b02a5616a63,0xcc8aa03aa73346883568cca90e0a5e530a5c421772c0a8e87a1570a9c213971c8c1583568f346883568c,0xc199507a98b409d21ad61c199507a98b10a5615c63d1915066e8b4645419ba2b032b1a847b314c40d732,0xc84748cd5870662a14c5dcc531035ccb3065433a62c68710665cb02a562ac63c0a958ab18f409d21ad61,0xc588a85a1770a8c611b33c118e873157055c214771c8c1583568f230560d5a3cc531035ccb314c40d732,0xc2c688995670662a14c5dc5562059d330a8c611b33cc531035ccb314c40d732c8c1583568f230560d5a3,0xc8c1583568f235883274cc589507a989086e660cabcc8950ce98b0465615c63c2c688995670b1a226559,0xd1d210b9c2b0a5a811d5c] 66 (by decide +kernel)

private theorem p3_15Good : Good p3_15 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_15s0 (joinSpan p3_15s1 p3_15s2)) (joinSpan (joinSpan p3_15s3 p3_15s4) (joinSpan p3_15s5 p3_15s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_16s0 : Span p3_16 3 0 4 :=
  batch _ _ _ _ #[
0xd1162851e374283a1e315d0235858d8f441d21d5a1ca9620a9e3310ab8352d4ca9620a9e329194655833,0xc0aae0b8b534458a1478dd1162851e374742215d19d0235858d8f408d616363ca8318855cf4458a1478d,0xc118e87a1570463a1e855a7468152e629d1a054b98cd0b08953c4d702c81b1ed1074875687441d21d5a1,0xd1d2107352b4548614d4bd152185352f4283a1e315d0a0e878c574742215d19d0235858d8f441d21d5a1,0xc1d2a047573074a811d5cd1d2107352b306c40d8f2cc1b10363cb4548614d4b19d8539710b02ab82e2d4,0xd152185352f4742215d19d152185352f074a811d5cd1074855e87074a811d5c05e52a660d7346882e4cc,0xd0235858d8f074a811d5cd1074855e87441d2157a1c508e8999574548614d4bd1074855e874548614d4b,0xd152185352f26688354cccc8b1032bcb0662a3445d74c19119cab4548614d4bd1d088574674742215d19,0xcc435039d8b310d40e762cc435039d8b051d2157a1] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_16s1 : Span p3_16 3 4 10 :=
  batch _ _ _ _ #[
0xd1d21073529c215c5aa26c686a046e731a1a811b9cc686a046e731a1a811b9cc1474875687074a811d5c,0xd150c877447074a811d5cccc0a8394773302a0e51dccc0a839477322c40caf2cc8b1032bcb474841cd4a,0x3706a206e733302a0e51dccc0a8394773302a0e51dc84748ad6871a1a811b9cc1474875687074a811d5c,0xd190a847476c19945d982d190a8474774642a11d1dcc18a88b177074a83155cc1474875686885e4589aa,0xd1074855e87206562ac63a6079181eab0662a14c5d74c0b10ac7b408d616363ce831085dcb3a0c421772,0xd0a0e878c566213accc15d1162851e374458a1478dd183506758b460d419d62c2a2e078d531425615c63,0xd190a8474770a8b81e354c5ca10d2b2a9113c63a16d1162851e373a44429732ce9110a5ccb3a44429732,0xc198a8531772b0322e711c88958ca98f466842cccac84748a9e87408d616363c88958ca98f3062a22c5d,0xc2a2e078d5067542e5431cc88a88b1770463a1e855c5562075633460d419d62c2a2e078d531425615c63,0xc55620756331423a1cc55c88958ab18f1622a14c5d] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_16s2 : Span p3_16 3 10 16 :=
  batch _ _ _ _ #[
0xce82a0395734458a1478dc456a054e7302a3a1cc55d1162851e37115a81539cc0a8e873157074c41c372,0xc6a6206ae3310a5616a63c8c62889e37074c41c372c428e88f1574458a1478dce82a03957310a3a23c55,0xc456a054e73206b80dcd4cc435039d8b2063a23c55cc53108cdcb3a0a80e55cd190a8474774642a11d1d,0xc84ac89ab455c0c644573c5511854ccf32a882accc38455a3a88f174441d332c5aa2057333174441d332,0xc1d31070dc9521e8435ac626351c1d8b1544615333c5d11074ccb16a8815cccccaa20ab3333a0a80e55c,0xd2a2185a52f4642a11d1dc5511854ccf115a81539cd190a8474774443a19d15d2a2185a52f4a8861694b,0xcc18a899177174441d332c5511854ccf115a81539cc81ae037353174441d332519d41772833a0a80e55c,0xd1074855e872a0b80e754c14ac8d2b472a0b80e754ccca109ab2b212b226ad1d1074855e872223a26655,0xc0a8e873157214c622373c0a8e87315702a3a1cc55c5d11074ccb02a3a1cc55d1074855e873062a2645d,0xcc435039d8b054c614373c8c0e839c5710a3a23c55ccd110acccb211d22a7a1] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_16s3 : Span p3_16 3 16 22 :=
  batch _ _ _ _ #[
0xcc53108cdcb26688354cccc2b088abc72065635463c1531850dcf054b81e354d103584758f440d611d63,0xd103584758f440d611d63ce82a02b5733a0a80ad5cce82a02b5733a0a80ad5cce82a02b573409d213ba1,0xce82a02b5733a0a80ad5cd0a6284e6374298a1398dd183506758b314c423372d183506758b4298a1398d,0xc429585a98f1a9881ab8cc1ab0852bc74443a19d15ce82a02b5733a0a80ad5cd0a6284e637334442b332,0xca9620a9e3316a8815cccc456a054e73054c614373ca82e039d53115a81539cc1531850dcf054c614373,0xd027486ae8730ac222af1ccc0a839477222b80ead4cac2189952f054c614373c818e8999571544615333,0xc1531850dcf115a81539cc1531850dcf460d419d62c1531850dcf06ac214af1c1ab0852bc706ac214af1,0xc50ae0c6b5316a8815ccccc53108cdcb16a8815cccce82a02b5733a0a80ad5ccc53108cdcb054c614373,0xccaa20ab333054c614373c5511854ccf16a8815cccc8c6288d6371544615333cac2189952f1544615333,0xc843583958f054c614373c88ae03ab533302a0e51d] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_16s4 : Span p3_16 3 22 28 :=
  batch _ _ _ _ #[
0xd027486ae87442b22ccd1d183506758b314c423372c0a9585a98f174441d332d027486ae8730ac222af1,0xc199507718b06ac2158f1d110e867457066541dc62c1ab0852bc73a0a80ad5cce82a02b573054c614373,0xc198a8531771544615333c5511854ccf1544615333c119585718f0465615c63c119585718f1544615333,0xc852e02f553474841cd4ad1d0885746456b42c58b1d1d088574674742215d19c5511854ccf322c40caf2,0xce9110a5ccb262c22c4f1ce9110a5ccb4742215d19c852e02f553306542e662a222f16255a674a0a1d58,0xcc435039d8b409d213ba1c852e02f5532303a0e715c1c350c5d8b306c40d8f2cc435039d8b262c2254f1,0xd0a6284e6374298a1398dc198a8d11774742215d19c1ab08563c74298a1398dc0a958ca98f0463a1e855,0xcc52a02b573441d2157a1cc52a02b573314a80ad5cd0a6284e637074a811d5ccd1a20b9333074a811d5c,0xa222f16255b074a811d5cc852e02f553322c40caf2cc8b1032bcb310d40e762d1d0885746706ac2158f1,0xc8c0e839c57314a80ad5ccc52a02b573314a80ad5c] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_16s5 : Span p3_16 3 28 34 :=
  batch _ _ _ _ #[
0xcc52a02b573314a80ad5cc6a11846ccf322542e662acad018eac3074a811d5ccc1b10363cb2318a2358d,0xcc52a02b573210d60e563c852e02f553322c40caf2cc8b1032bcb3302a0e51dc1ab0852bc71518a1c58d,0xca82e039d53306c40d8f2cc1b10363cb1625435662c843583958f214b80bd54cc52a02b573222b80ead4,0xccaa20ab333314a80e55cd1074855e87322542e662c14ac8d2b4716a8815cccca82e039d532a0b80e754,0xca82e039d534a8861694bd2a2185a52f4a8861694bd110e8674574443a19d15d0a6284e6374298a1398d,0xcc52a039571521e8427acc81ae037353206562ac63c81958ab18f4298a1398dca82e039d532a0b80e754,0x5417a109eb34a8861694bd2a2185a52f440d611d63d0a6286a637440d611d63d103584758c56b42c58b1,0xc8c62889e3716a8815cccc88958ab18f0a8c611973ce9110a5ccb0a8c611973cc88a88b1771622a14c5d,0xc2a2e067553314a80e55cc8c0e839c57211d22a7a1c1474855e873b0842674a] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_16s6 : Span p3_16 3 34 36 :=
  batch _ _ _ _ #[
0xc6a11846ccf2223a23c55cc2b088abc6885e4589aacc1b10363cb440d611d63c8c62889e37440d611d63,0xcc8b1032bcb4298a1398dc118e87a157409d213ba1c8c62889e37409d213ba1cc88a88b1771423a1cc55,0xc686a046e734642a11d1dd190a8474774642a11d1dcc18a88b1774a8861694bc1ab08563c7322c40caf2,0xcc52a03957140cdc53166cc8b1032bcb4298a1398d] 28 (by decide +kernel)

private theorem p3_16Good : Good p3_16 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_16s0 (joinSpan p3_16s1 p3_16s2)) (joinSpan (joinSpan p3_16s3 p3_16s4) (joinSpan p3_16s5 p3_16s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_17s0 : Span p3_17 3 0 4 :=
  batch _ _ _ _ #[
0xc1c35066e8b2a5883274cc1c35066e8b070d419ba2d0d6107352b435841cd4ad0235854e8f435841cd4a,0xcc43502ee8b310d40bba2cc43502ee8b310d40bba2c818e899957408d6153a3d0235854e8f408d6153a3,0xd0235854e8f408d6153a3cd0b08953c7070d4297a2cd0b08953c73222a3445dd0235854e8f3222a3445d,0xd1074879587441d21e561b814e17a853310d40d7a2cc435035e8b310d40d7a2aa0399816addc44443b32,0xc1c35066e8b070d419ba2d150c877447454321dd11d0235854e8f441d21e561c0aae0d4b532b08622b8b,0xcc1b10363cb310d40bba2cc43502ee8b310d40bba2cc43502ee8b310d40bba2cc43502ee8b342c2254f1,0xd0d6107352b435841cd4ad0235854e8f435841cd4ac6a118a8ccf454321dd11cc1b10363cb306c40d8f2,0xd1074859d872a446295337085715589b2223a34655cc18a899177206562e463cc18a8991772a1c222771,0xaa1199c14af408d6153a3d0235854e8f408d6153a3] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_17s1 : Span p3_17 3 4 9 :=
  batch _ _ _ _ #[
0xc589507a98b211d232761c58b1086bcb3062a2645dcc18a8991771a8462a333cc18a89917734688354cc,0xd0d6107352b0465616a63ce82a02ae733a0a80ab9cce82a02ae733a0a80ab9cce82a02ae732a44629533,0xc119585a98f0465616a637711110eccb435841cd4ad0d6107352b435841cd4ad18350a5e8b2a1c222771,0xca9620c9d332063a26655d1835066e8b460d419ba2b814e17a8532a1c222771313a32b0339dc44443b32,0xce82a02ae73454321dd11c509585a98f0463a34655d02358a8e8f408d62a3a3ca9620c9d33460d419ba2,0xa70519528cf3225433a62d1835066e8b460d419ba2c509585a98e885ac5095ece82a02ae733a0a80ab9c,0xce82a02ae733a0a80ab9cce82a02ae733a0a80ab9cce82a02ae730662a1685dc198a85a1770a5c419972,0xcc88a88b177222562ac63c1c35066e8b074a82959cc1c35066e8b070d419ba2c509585718f1425615c63,0xcc88a88b175d232845c9cc686a0475731a1a811d5c6650b1a147b1a1a811d5cd0235854e8f408d6153a3,0xcc43502ee8b408d6153a3d0235854e8f3065435662c88958ab18f408d6153a3] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_17s2 : Span p3_17 3 9 14 :=
  batch _ _ _ _ #[
0xc84748c9d871a1a811d5cd0235854e8f1423a1cc55c1d2a0a5673074a82959cc509585718f1425615c63,0xc509585718f1425615c63c6c61099d2b1b1842674ac6c61099d2b408d6153a3c1474859d871423a1cc55,0xc29710665cb1a1a811d5ccc88a88b177215c223571d296107a52b4a5841e94ac1c35066e8b070d419ba2,0xcc1950d598b234462a333cc43502ee8b310d40bba2c8d620cd5331622a14c5dcc88a88b1770662a1685d,0xd027484f587070d419ba2c1c35066e8b1544615333c1c35066e8b262c22c4f1c456a058d7310a5615c63,0xc8d118a8ccf1b1842674ac6a6206b5331b1842674acc43502ee8b310d40bba2d027484f587310d40bba2,0xca91182accf310d40d7a2ca91182accf1544615333ca91182accf409d213d61c6a6206b5331544615333,0xcc43502ee8b409d213d61c1c35066e8b1544615333d027484f58710a5615c63d027484f587214b82b394,0xc152e074e531544615333cc1b10363cb310d40bba2] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_17s3 : Span p3_17 3 14 20 :=
  batch _ _ _ _ #[
0xc6a6206b5332a1c222771c14ac8d2b473328434acac6a6206b533050d611ba3c6a6206b5333225435662,0xc0a9585718f440d611ba3cec088cac671728426acac58950b998b10a562ac63c843582ae8f02a5615c63,0xc42958ab18f162c421af2c0d71070dcb1a9881ad4ccac0c8b9c47162c421af2c0d71070dcb440d611ba3,0xc508e873157035c41c372c81958d518dd232845c9ccc8950ce98b3a0a80ab9cce82a02ae73409d213d61,0xc1ab0852bc7310d40d7a2c88ae037353222b80dcd4c457108cdcb115c423372c0d71070dcb051d216761,0xc843582ae8f070d419ba2cec088cac67115c423372c1c35066e8b0a9c21a971c1435846e8dd384445732,0xc8d118a8ccddc44443b32c2a7086a5c73b02232b19c88ae037353310d40bba2cc43502ee8b054b81d394,0xca91182accf2a4460ab33c5511854ccf1544615333c6a6206b533234462a333c5511854ccf10a5615c63,0xc0a9585718f1544615333d1835066e8b460d419ba2c5511854ccf115a81635cc0a9585718dd302c4551e,0xc118e8d19573a0a80ab9cc5511854ccf115c423372] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_17s4 : Span p3_17 3 20 26 :=
  batch _ _ _ _ #[
0xd2a0c87ac474a8321eb11cc2b088abc716a8816accc50ae0a735306ac214af1c588a8531771622a14c5d,0xd1835066e890b99856744c5511854ccf214b82b394c88ae037353115c423372c0d71070dcb3065435662,0xc5511854ccf3225433a62ce82a02ae734a5841e94a72e051b9c0b1544615333c5511854ccf460d419ba2,0xc14748795872223a23c55c19b10a63c8d59888674cc5aa205ab330662a1685dc5aa205ab330662a1685d,0xc843583568f210d60d5a3cc1b10363cb306c40d8f2c88ae037353222b80dcd4c5aa205ab330662a1685d,0xc588a8531771622a14c5dc588a8531770465616a63cc88a88b1771544615333c5511854ccf0a9c21a971,0xcc43502ee8b310d40bba2ca91182accf1544615333d2a218aa62f211d233561cc1950ce98b1622a14c5d,0xcd0b08953c7070d419ba2d0d6107352b070d419ba2cec088cac672a5883274cc2a7086a5c7435841cd4a,0xc429585a98f310d40d7a2cc435035e8b16a8816accac15a2398b1d302c42b1ec50958b918f310d40bba2,0xc29710665cb310d40d7a2c1c350a5e8b10a5616a63c50958b918ee41985e544b8b111744cb2225635463] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_17s5 : Span p3_17 3 26 32 :=
  batch _ _ _ _ #[
0xca91182accf2a4460ab33ca91182accf2a4460ab33ca91182accf310d40d7a2cc435035e8b310d40d7a2,0xc428e87a157266882e4ccc1435846e8f1728426acac428e87a157206b80ead4cc435035e8b1622a2645d,0xc888e8d19571a1c421772c843582ae8f10a3a1e855d0d6107352b435841cd4acec088cac67441d216761,0xc428e87a157162c421af2c1474859d873a0a80ab9cce82a02ae733a0a80ab9cd1074859d87210d60aba3,0xc843583568f10a5616a63c1ab0852bc7306c40d8f2ca9118a54cf322c40caf2c296a0c55730a9c21a971,0xc843583568f210d60d5a3cc1b10363cb306c40d8f2c6a11846ccf1a84611b33c429585a98f460d4297a2,0xca91182accf2a4460ab33ca91182accf2a4460ab33ca91182accf435841cd4ad2a218aa62f4a8862a98b,0xce82a02ae733a0a80ab9cc428e87a157206b80ead4c843583568f435841cd4ac0a8e8ce1572a4460ab33,0xc88958ca98f1425616a63c509585a98f322c40caf2c2a7086a5c7460d419ba2c509585a98f162c421af2,0xd150c877447454321dd11] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_17s6 : Span p3_17 3 32 37 :=
  batch _ _ _ _ #[
0xc843582ae8f4a5841e94ac843582ae8f210d60aba3c843582ae8f314a80d59cb0b0b15447b409d21ad61,0xcc52a0356731622a14c5dc0a958ab18dd302c42b1ecc52a0356732a0b829794d027486b58710a562ac63,0xcc43502ee8b210d60aba340bd29702d71a1a811d5cc1d2a0a5673210d60aba3c843582ae8f314a80d59c,0xd1d088b9467409d213d61c8d118354cf10a562ac63a62199434af440d611ba3cc1950d598b3065435662,0xc29710665c98c54a53835d027484f587409d213d61c589507a98b10a562ac63d1d088b946710a562ac63,0xc15708715c71423a1cc55c8d118354cf234460d533cc52a035673314a80d59cc84748c9d871622a14c5d,0xc29710665cb06ac214af1cc52a035673314a80d59cc8d118354cf234460d533c508e8731571a84611b33,0xc686a047573211d232761c6c61099d2b1b1842674ac1d2a0a56731425615c63c6c61099d2b314a80d59c,0xc1474859d8562c4a5a135d1d088b9467211d232761] 68 (by decide +kernel)

private theorem p3_17Good : Good p3_17 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_17s0 (joinSpan p3_17s1 p3_17s2)) (joinSpan (joinSpan p3_17s3 p3_17s4) (joinSpan p3_17s5 p3_17s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_18s0 : Span p3_18 3 0 4 :=
  batch _ _ _ _ #[
0xd1162851e371742811d5cd152185742f1742811d5cca9620a9e32c39a055998c5d0a0475731742811d5c,0xd1d088535674742214d59d1d088535674458a1478dd1d088535674458a1478dd1162851e373a44421772,0xccc15039d8b4742214d59d1d088535672a0c629533ca8318a54cf2a0c629533d152185742f1742811d5c,0xa0e519560cf346882e4ccb9066175612e05385ea14c5462851e37306c40caf2ccc15039d8b330540e762,0xd1d088535674285616363c2c6888ae674458a1c58dd1074855e873328426acac0aae0d4b53346882e4cc,0xb084f17605b346882e4ccd1d088535670b1a222b99c2c6888ae66c581656943d1d088535674742214d59,0xd152185742f4548615d0bd022e878c57408ba1e315d152185742f3328426acac508e87a1571423a1e855,0xd11628716374458a1c58dcac218cac2f322c40d8f2cc8b10363cb4285616363d1162871635d10ac42b1e,0xd1d08853567408ba1e315c81958b918f10ab82e2d4] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_18s1 : Span p3_18 3 4 10 :=
  batch _ _ _ _ #[
0xc296a046e730a5a811b9cc296a046e732223a26655ce8310a5ccb454321cd51c5d0a047570c615ca9626,0xc5d0a0475734a1a22a999cc42a839477310aa0e51dcc42a839477306c40caf2cc1b1032bcb0a5a811b9c,0xcc42a8394774a1a22a999d150c8735471518a1c58dc296a046e73474841dd0ac5d0a047573408ba1e315,0xd1074855e870465615c63c6a0e078d531a8381e354d191506758b4645419d62cc42a839477310aa0e51d,0xd1074855e87441d2157a1a0c4f18e85b441d2157a1d022e878c55953505eaa0ce8310a5ccb3a0c429732,0xc5ca10d2b2b4458a1478dd182a847477460aa11d1dcc88a88b177174283155cd182a847476885e4607aa,0xd182a847477051d2157a1a2179181eab4458a1478dd1162851e373a44421772ce911085dcb1622a14c5d,0xc1474855e87222562ac63c588a853177211d22a7a1c5462851e373222a22c5dd0a15858d8f1518a1478d,0xc118e873157206562ac63c508e87a1573062a22c5dc55620756330465615c63cc18a88b1774645419d62,0xc198a8531771a8381e354b8c6818ae632223a33855] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_18s2 : Span p3_18 3 10 16 :=
  batch _ _ _ _ #[
0xd1162851e372a4380e754d1162851e37441d21d5a1c8d11888dcf2063a26655c5aa2057333074c41d332,0xc8d11888dcf10a3a1cc55c428e873157074c41d3325442f10ec5b4458a1478dc8d11888dcf2a4380e754,0xc842e839c5702a3a23c55ccc15039d8b1544614373ccaa20ab3315384642973c428e87315710a3a1cc55,0xce90a02b573409d213ba1d027484ee871a9881ab8cc5511850dcf1a9881ab8cd111584758f4445611d63,0xd111584758f4445611d63ce90a02b5733a4280ad5cce90a02b5733a4280ad5cccd1108cdcb3344423372,0xc5d11070dcb314c42b332c5d11070dcb4298a1398dd191506758b154381e354d191506758b314c42b332,0xc85318a8ccf035a81539cc428e873157174441c372ce90a02b5733a4280ad5cce90a02b5733a4280ad5c,0xd1074855e870b1a222b99ce90a039573441d2157a1ce90a0395733344423372c0d6a054e73441d2157a1,0xccc15039d8b3a4280e55cd182a847477460aa11d1dc1d31074ccb02a5616a63d2a2185ac2f4a88616b0b,0xc888e88f1573344423372c1ab0852bc7222b80dcd4] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_18s3 : Span p3_18 3 16 22 :=
  batch _ _ _ _ #[
0xc84ac89ab47054c615333cc5310accc95c44644573c1d31074ccb3344423372ccca109ab2b074c41d332,0xc5ca10d2b2b054c615333c1d31074ccb4458a1c58dc5d11070dcb052b234ad1c5ca10d2b2b3a4280e55c,0xd0a6284e637460aa11d1dc1531854ccf035a81539cd182a84747706ac2158f1d0a6284e6374298a1398d,0xc5aa20573333b02226559d0a6284e63706ac2158f1c1531854ccf035a81539cc88ae0373533a4280e55c,0xd027486ae87409d21aba1cc42a839477206b80ead4c8c6288d6371544614373c888e899957054c615333,0xc5511850dcf1544614373c0d6a054e734645419d62c5511850dcf10a5616a63cec088995673b02226559,0xc1d31074ccb02a5616a63d102e8674571622a14c5dce90a02b5733a4280ad5cccd1108cdcb1544614373,0xcec0889956716a8815cccc1ab0852bc71544614373ca90e039d53035a81539cc5511850dcf1544614373,0x7015716a89b1544614373c1531854ccf314c42b332c1531854ccf2318a2358dccd1108cdcb16a8815ccc,0xc81ae03ab53310aa0e51dc8c1583958f1544614373c1531854ccf211d22b5a1] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_18s4 : Span p3_18 3 22 28 :=
  batch _ _ _ _ #[
0xc54628716371544614373d191506758b10a5616a63ccd1108cdcb3b02226559cec08899567074c41d332,0xc1ab08563c706ac2158f1c1ab08563c7074c41d332ce90a02b5733a4280ad5ccc5310accc942c5c5a166,0xc1531854ccf054c615333c588a8531771425615c63c1531854ccf054c615333c509585718f1425615c63,0xd152185742f0b1a222b99d1d0885356702a3a1e855d1d2107742b0b1a222b99cc1b1032bcb054c615333,0xccd0a02b5734742214d59ccd0a02b573334280ad5cce911085dcb1742811d5cb88519950cf1742811d5c,0xd152185742f234380bd54c5d0a047573306c40caf2cc1b1032bcb4298a1398dd02ac8ba347330540e762,0xc550e06755306ac2158f1d0a6284e6374298a1398dc842e839c57334280ad5cccd0a02b573334280ad5c,0xd1d088535674298a1398dc8d0e02f553441d2157a1cd1a20b9333346882e4ccc8d0e02f553206562e463,0xc8d0e02f553210ba0e715d28688aa667322c40d8f2d28688aa667330540e762d1d088535674742214d59,0xd1d088535674742214d59ccc15039d8b2a44621573] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_18s5 : Span p3_18 3 28 34 :=
  batch _ _ _ _ #[
0xccd0a02b573230560e563c8d0e02f553230560e563c8d0e02f553306c40caf2cc1b1032bcb310aa0e51d,0xca90e0c5d53454321cd51c5d0a0475734a1a22a999cc8b10363cb4a1a22a999ccd0a02b573206b80ead4,0xc1ab08563c74445611d63d2a0c87a5474445611d63ccd0a02b573334280ad5cc2a31846ccf409d21aba1,0xc81958ab18f1a84611973ce8310a5ccb1a84611973d0a6284e637441d2157a1d0a6284e6374445611d63,0xca90e039d532a4380e754ca90e039d530665435662cc8b10363cb322c40d8f2c198a853175521e8427ac,0xc50ae0a73531728434acaccaa20ab33332a882acccd1162851e350ccca531357442b10ac7b334280e55c,0xca90e039d532a4380e754ca90e039d53222562ac63c50ae0a735306ac2158f1c1ab08563c7222562ac63,0xc8c62889e3716a8815cccc88958ab18f06ac2158f1c118e899957334280e55cc5ca10d2b2b222b80dcd4,0xc842e839c554c19a53985c6a0e067553334280e55cc1474855e86c0cac6a11e] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_18s6 : Span p3_18 3 34 36 :=
  batch _ _ _ _ #[
0xd15218b942f30ac222af1cc2b088abc74a88616b0bd111584758f322c40d8f2d111584758f2b03226751,0xd0a6284e6372065632a63c118e8731570a8c611b33d027484ee87409d213ba1c508e87a15542c5c53166,0xd0a6284e637460aa11d1dd182a847477051d2157a1d182a847477306c40caf2cc1b1032bcb222562ac63,0xcc1b1032bcb222562ac63c296a046e73334280e55c] 28 (by decide +kernel)

private theorem p3_18Good : Good p3_18 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_18s0 (joinSpan p3_18s1 p3_18s2)) (joinSpan (joinSpan p3_18s3 p3_18s4) (joinSpan p3_18s5 p3_18s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_19s0 : Span p3_19 3 0 4 :=
  batch _ _ _ _ #[
0xcec0888ae67222562e463d0568853567415a214d59cec0888ae670a8c62a333d0568853567441d21e561,0xd152185742f42856153a3d0a15854e8f42856153a3c50958b918f2a0c6295337015715589b415a214d59,0xc199507a98b415a214d59c19b1086bcb3222a2645dd0568853567415a214d59cd0b08953c60655c99a26,0xd05688535673b02222b99ce90a02ae733a4280ab9cce90a02ae733a4280ab9cce90a02ae732a0c629533,0xd0a15854e8f42856153a3c5c15066e8b3b02222b99d0568853567415a214d59cec0888ae672a1c222771,0xd0568853567051d216761ccc1502ee8b330540bba2ccc1502ee8b330540bba2d152185742f42856153a3,0xccc15035e8b4548615d0bd0a15854e8f42856153a3d0568853567415a214d599582b206c7b3062a3445d,0xaa1199816af4548615d0bccc15035e8b330540d7a2] 60 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_19s1 : Span p3_19 3 4 8 :=
  batch _ _ _ _ #[
0xcec0888ae67162c4298f2d152185742f4548615d0bcec0888ae67162c4298f2d0a15854e8f3b02222b99,0xd152185742f2b08632b0bcc8b10363cb322c40d8f2cc8b10363cb4548615d0bcec0888ae67162c4298f2,0x318572a589b2a1c222771ccc1502ee8b330540bba2ccc1502ee8b330540bba2ccc1502ee8b330540bba2,0xc508e8d1957428562a3a3d0a158a8e8f2223a26655d1915066e88c615ca9626d1915066e8b4645419ba2,0xca9620c9d30c615c99a26c509585a98e8394655833ce90a02ae733a4280ab9cce90a02ae730465616a63,0xca9620c9d332225632a637703110eccb1425616a63c509585a98ddc0c443b32d19150a5e8b46454297a2,0xc14748795870465616a63d1915066e8b4645419ba2c84748cd5873065433a62ca9620c9d328394655833,0xce90a02ae733a4280ab9cce90a02ae733a4280ab9cce90a02ae731a1c419972c588a85a1771622a1685d] 64 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_19s2 : Span p3_19 3 8 13 :=
  batch _ _ _ _ #[
0xc5c15066e8b1705419ba2c119585718f0465615c63d0a15854e8f42856153a3cc18a88b177206562ac63,0xd0a15854e8f42856153a3cc8950d598b052b226ad1d0a15854e8f3062a22c5dc5c15066e8b174282959c,0xd0a15854e8f055c21c571ccc1502ee8b441d216761c296a0475730a5a811d5cc84ac8d2b470a5a811d5c,0xc296a04757342856153a3c509585a98f055c21c571c5d0a0a5673174282959cc119585718f0465615c63,0xd286885a5674a1a216959cc18a88b176981ac5095ec88958ca98f211d232761d1d088b16672225632a63,0xc68710665cb0a5a811d5ccc18a88b1771622a1685dd286885a5674a1a216959c119585718f0465615c63,0xcc1950d598b1505611ba3cec0888ae673065435662d286885a5670662a14c5dccc1502ee8b330540bba2,0xd027484f587409d213d61c8c1582ae8f10a5615c633726220f5320655ca9626b9170231dc2a858ca074e,0xc19b1086bc95c43843b94c4571070dcb4445611ba3c429585718f4445611ba3d027484f587409d213d61,0xce90a02ae733a4280ab9ccd0b08953c74a8862ad0bd027484f5871a9881ad4cc6a6206b5334a8862ad0b] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_19s3 : Span p3_19 3 13 19 :=
  batch _ _ _ _ #[
0xd19a10b332b330540d7a2c4571070dc94b8166a983d2a2185ac2f115c41c372c5aa205ab334a88616b0b,0xc5c15066e8b0a9c21a971cec0888ae671505611ba3c81ae037353206b80dcd4c0d7108cdcb16a8816acc,0xccc1502ee89953505eaa0d1074879587154381d394c8c1582ae8f441d21e561c5c15066e8b441d21e561,0xc5c15066e8b1a9881ad4cc0d6a058d7302a5615c63cc8950d598b214c62a333c81ae037353330540bba2,0xccc1502ee8b330540bba2cec0888ae67330540bba2c0d7108cdcb1705419ba2c5c15066e8b054c615333,0xca83182accf035c423372c5c150a5e8b054c615333c85318a8ccf214c62a333c99a20b9333214c62a333,0xd286885a5673b02222b99cec0888ae6702a5615c63c1531854ccf2a0c60ab33ca83182accf330540d7a2,0xccc1502ee8b330540bba2d027484f587054c615333cc8b10363cb4a1a216959d027484f587054c615333,0xc429585718f4645419ba2c1531854ccf4645419ba2c1531854ccf10a5615c63c0d6a058d71d10ac4551e,0xd2a218ab42f3a4280ab9cc1531854ccf035c423372] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_19s4 : Span p3_19 3 19 25 :=
  batch _ _ _ _ #[
0x4333294c4d50ccca53135cc2b088abc716a8816accc4571070dcb06ac214af1c1ab0852bc7046b829cd4,0xd027486b58702a5615c63d027486b585dc0c443b32c81ae03735316a8816accca870889dc7115c41c372,0x52e2c1b9c43234382b394ca83182accf2a0c60ab33c1531854ccf46454297a2c1531854ccf054c615333,0xc1531854ccf054c615333d027486b585c2b506bca0d1915066e8b054c615333c1531854ccf4645419ba2,0xc818e88f1571423a1e855c588a85a17715056295a3c588a85a177211d233561ce90a02ae733065433a62,0xc588a85a1772223a33855c8c1583568f230560d5a3cc8b10363cb322c40d8f2c1474879587162c4298f2,0xd19a10b332b1425616a63c1531854ccf054c615333cc18a88b177162541ea62c81ae037353206b80dcd4,0xc2a7086a5c7054c615333ca83182accf0662a14c5dc198a8531770662a14c5dc198a853177466842ccca,0xa62199426af441d21e561d152185742f3b02222b99c2a7086a5c7415a214d59c5415846e8f10a3a33855,0xca8318a54cf230560aba3d05688535674548615d0bc8c1582ae8f415a214d59] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_19s5 : Span p3_19 3 25 31 :=
  batch _ _ _ _ #[
0xd152185742f415a214d59c2a7086a5c7066c421af2c19b1086bcb3a4280ab9cce90a02ae733a4280ab9c,0xd1074859d872b08632b0bd0568853567266882e4ccccc1502ee8b330540bba2ca8318a54cf306c40caf2,0xd152185742f4548615d0bd1074859d87330540bba2d152185742f415a214d59cc18a8d1177415a214d59,0xc1474859d87046562e463c1474859d872065635463c1ab0852bc744456295a3ccc15035e8b330540d7a2,0xca83182accf330540d7a2ccc15035e8b330540d7a2c68710665cb330540d7a2c5c150a5e8b02a5616a63,0xd152185742f222b80ead4ccc15035e8b4548615d0bca83182accf2a0c60ab33ca83182accf2a0c60ab33,0x7015716a89b2065632a63d1915066e8ae501665583c19b1086bcb0465616a63ce90a02ae733a4280ab9c,0xc8c1583568f2a5883274cc1ab0852bc7322c40d8f2c119585a98f0465616a63cc1b1032bcb2065632a63,0xc2a31846ccf0a8c611b33c8c1583568f230560d5a3cc8b10363cb322c40d8f2d19150a5e8b02a5616a63] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_19s6 : Span p3_19 3 31 36 :=
  batch _ _ _ _ #[
0xca83182accf2a0c60ab33ca83182accf2a0c60ab33ca83182accf0a9c21a971c50ae0c6b532a5883274c,0xccd0a035673334280d59cc88958ca98f10a3a33855c0a8e87a157222b80ead4c8c1583568f2a0c60ab33,0xc296a047573441d216761cc8950d598b330540bba2c8c1582ae8f230560aba3c5d0a0a56730662a14c5d,0xc8c1582ae8f230560aba3d027486b5874a1a216959c5ca10d2b2b334280d59cc8c1582ae8f212b234ad1,0xc15708715c72a43829794d027484f587230560aba3c42958ab18f409d21ad61ccd0a035673230560aba3,0xd1d088b166560cca5a135710a715631b214c60d533d027484f586888e650d2bd286885a5674445611ba3,0xccd0a035673334280d59cc15708715c7409d213d61c857088d5c7409d213d617a115162e8b1a1c419972,0xccd0a035673334280d59cc85318354cf214c60d533d286885a567055c21c571d286885a56706ac214af1,0xc85318354cf214c60d533c15708715c70a8c611b33c68710665cb474222c599] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_19s7 : Span p3_19 3 36 37 :=
  batch _ _ _ _ #[
0xc84748c9d87211d232761c5d0a0a56730465615c63c5d0a0a5673174282959ccc8950ce98b334280d59c,0xc88958ca98f0a5a811d5cc88958ca98f1425616a63] 12 (by decide +kernel)

private theorem p3_19Good : Good p3_19 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan (joinSpan p3_19s0 p3_19s1) (joinSpan p3_19s2 p3_19s3)) (joinSpan (joinSpan p3_19s4 p3_19s5) (joinSpan p3_19s6 p3_19s7)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_20s0 : Span p3_20 3 0 4 :=
  batch _ _ _ _ #[
0xc42ae074e52177205d530c42ae074e5310ab81d394d086a84e1d7421aa13875d086a84e1d7421aa13875,0xc9c228732372708a1cc8dc8d8189952f236062654ba445998b0aeb054c62a1ed191503ab8b464540eae2,0x89d071b131b3508a23c8dcd42288f23656464468ead11a185662f446861598b80bb918c6ab446861598b,0xc9c22873237236062654b88bc2a784373a6043394aaa10f1a235b3a6043394ac1a32898a76e2c28550f4,0xc9c228732372708a1cc8dc1a328d0a77354883568cd11a1852e2f4468614b8bcc588889dc65072642b33,0xc1d88851dc73508a23c8dd191503ab8b464540eae2c1d88851dc7308ca2629da21c9942ccf464540eae2,0xd11a185662f446861598bcc588889dc7115a82a674cc588889dc610f2a5a135c1a32898a773162222771,0xc1d88851dc702a5616363c0d6a0559d3035a815674c1d88851dc70762214771cc232898a768531655d03] 64 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_20s1 : Span p3_20 3 4 8 :=
  batch _ _ _ _ #[
0xc119584758f0465611d63d0aa1852e2f0465611d63d0aa1852e2f42a8614b8bc119584758f0465611d63,0xd086a84e1d7045ca14c5dd086a84e1d7421aa13875c1172853177045ca14c5dcd0328c6277340ca3189d,0xd1a1485ab872a23223d51c819582b58f33054352e2c1ab0852e6742a8614b8bd0aa1852e2f115a81d474,0xc8c0e898b570a62611973d1a1485ab870a62611973ce9810ce52b06ac214b99ca88c88f547340ca21c9d,0xd0aa185662f42a861598bc119584758f0465611d63cc2b088ae6730ac222b99b908595350f0a62611973,0xc5c150b8b8b421d433a62d0aa185662f0465611d63b1a0715631b142b819b94c119584758f0465611d63,0xca90e0a735306ac215999d0aa185662f2a43829cd455833112a7b421d433a62c5c150b8b8b050d6352a3,0xc456a0751d30a5a813a74b08599530af0a5a813a74b1a0715631b0a5a813a74c819582b58f42a861598b,0xc9832833276b054c62a1ecc2b08aa667115a81d474c456a0751d306ac215999c0d6a0ad1d102ee8531ac] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_20s2 : Span p3_20 3 8 12 :=
  batch _ _ _ _ #[
0xc119584758f0465611d63d0aa1852e2f0465611d63d0aa1852e2f42a8614b8bc119584758f0465611d63,0xc1172853177260ca0e89dc983283a277260ca0e89dc983283a2774685216ae1cd0328c62772a60622d4b,0xd1a1485ab87035a815674ccc150d4b8b0762214771ae1191833ab260ca0e89dc983283a277421aa13875,0xc5c150b8b8b115a82a674d1a1485ab874685216ae1b1a07152b1b0762214771c8c0e898b57340ca21c9d,0xd0aa185662f42a861598bc119584758f0465611d63c9832833277336042674ad1a1485ab874685216ae1,0xc88ae02ee533162222771d0aa185662f0465611d63ccd810d1d2b142b819b94c119584758f0465611d63,0xc1ab085666742a861598bc0d6a0559d3222b80bb94c88ae02ee53222b80bb94c88ae02ee53222b80bb94,0xa5e881715c30762214771c6a818ca52f340ca21c9db1a0715631b06ac215999c1d88851dc7336043474a,0xc98328332771aa063294bb1a0715631b1aa063294bc5d81099d2b354883568ccc588889dc730ac22a999] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_20s3 : Span p3_20 3 12 17 :=
  batch _ _ _ _ #[
0xc9c22873237050d629ca3c9c22873237111d41dc62ce88888d5c7262c225599d1a1485ab874685216ae1,0xd023583aa8f111d41dc62c98b0895665510e644cabd023583aa8f408d60eaa3c9894879587262521e561,0xc9c22873237111d41dc62ce88888d5c6508e6468abc9894879587111d41dc62c540e8873573a22223571,0xd0a0e83a3573425233561d191503ab8b4283a0e8d5c9c228732372708a1cc8dd191503ab8b464540eae2,0xd110e8333574443a0ccd5c819582b58f0465611d63c119584758f0465611d63c119584758f0465611d63,0xcd032887277111aa1c475d023583aa8f464540dce294a0f112b5b2a60622d4bd110e8333574443a0ccd5,0xc0c6a88d1d7152862c58bcc2b088ae6730ac222b994c6a61a9e1330ac222b99950399132af06ac214b99,0xc119584758f0465611d63c119584758f0465611d63c9832833277111aa1c475c446a8711d7111aa1c475,0xd191503738b1a1a81aa74c0c6a88d1d5332e0635a8c54a189562f3a60423d4ac819582b58f0465611d63,0xc686a06a9d31a1a81aa74] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_20s4 : Span p3_20 3 17 22 :=
  batch _ _ _ _ #[
0xc9832833277440d60dca3d103583728e5072642b33cc2b08aa6670a5a813a74c296a04e9d30a5a813a74,0xd0aa1852e2f42a8614b8bd0a0e83a357260ca0cc9d98b0a9503d7111aa1c475d103583728f440d60dca3,0xc0d89850dcf2303a0ccd5cc2b088ae671162622373c983283a277260ca0e89dc9c228732372708a1cc8d,0xd016a8519d7405aa14675d023583aa8f0a5a82a674c1ab0852e67206b80d794d023583aa8f2303a0ccd5,0xcd42288f237405aa14675c4589888dce662945cb82c8c0e8333572303a0ccd5d0aa185662e508e6468ab,0xc447507718b111d41dc6255833112a7b42a861598bc0d89850dcf2303a0ccd5d0a0e83a357405aa14675,0xd191503ab8b210d60dca3c4589888dcf1162622373d11a1852e2f2303a0ccd5c447507718b050d629ca3,0xc50ae066e53142b819b94c550e0d4b53421aa138755488f10e5595223c43956d086a84e1d7421aa13875,0xc1a94859d87222b80bb94d11a185662ea2c688e0eccc2948c9d8656464468eac50ae066e53142b819b94,0xc550e0d4b51560cc44a9ec88ae02ee53222b80bb94421b99426af222b80bb94] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_20s5 : Span p3_20 3 22 27 :=
  batch _ _ _ _ #[
0xd023583aa8f408d60eaa3c9c22873237111d41dc62ccd81099d2b262c225599c9894879586e2c28550f4,0xc6a0e0c6b53210d60dca3c889583958f4685216ae1c0c750af18a6053a5e815c843583728f210d60dca3,0xd0a0e83a3574283a0e8d5c14358a728f336043474ad191503ab8b464540eae2d0a0e83a3574283a0e8d5,0xc843583728f2303a0ccd5c8c0e833357222560e563c68898855cf176043474acd0b08956671a22621573,0xc983283a2774443a0ccd5c819582b58f408d60eaa3d023583aa8f464540dce2b9a0615ab132a60622d4b,0xc446a8711d7340ca21c9dc1d88851dc7464540dce294a0f112b5b260ca0e89dc1172853177260ca0e89d,0xc29898465cf115a82a674cc588889dc73162222771c6a0e0c6b533162222771950399132ae831666642b,0xd191503738b464540dce2c5d81099d2b142b819b94c29898465cf0a62611973c29898465cf0a62611973,0xc1ab0856667035a815674c88ae02ee53222b80bb94c88ae02ee533162222771c819582b58f142b819b94,0xc1d88851dc70762214771] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_20s6 : Span p3_20 3 27 32 :=
  batch _ _ _ _ #[
0xc9832833277440d60dca3d103583728f3162222771cc2b08aa6674283a0e8d5d191503ab8b4283a0e8d5,0xd023583aa8e8316654c2bd0a0e83a357260ca0cc9dd191503ab8b4283a0e8d5c54a189562f440d60dca3,0xc6a0e0c6b532303a0ccd5cc2b088ae65560cc4589ecc2b088ae656665056760d023583aa8f06ac214b99,0xd0a0e83a356865685662cd023583aa8e1cc2a620f5c1ab0852e67206b80d794d023583aa8f2303a0ccd5,0xcd42288f237405aa14675d0a0e83a3574283a0e8d559994159d8330ac22a999c540e88735706ac215999,0xd191503ab8b464540eae255833112a7b42a861598bc1ab08566672303a0ccd5d0a0e83a357405aa14675,0xd191503ab8b210d60dca3c8d8189952f236062654b5583311627b464540eae2c296a04e9d30a5a813a74,0xc1a94859d8706a52167615488f10e55b421aa13875c55818d152d5223c43956d086a84e1d7421aa13875,0xc29898465cf222b80bb94c8d8189952d666c055998cc2948c9d8510ee85a1aca1a87151d1b236062654b,0xc29898465cf0a62611973c88ae02ee53222b80bb94c29898465cf222b80bb94] 78 (by decide +kernel)

private theorem p3_20Good : Good p3_20 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_20s0 (joinSpan p3_20s1 p3_20s2)) (joinSpan (joinSpan p3_20s3 p3_20s4) (joinSpan p3_20s5 p3_20s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_21s0 : Span p3_21 3 0 3 :=
  batch _ _ _ _ #[
0xd29098465cf4a42611973d29098465cf4a42611973d29098465cf4a42611973d29098465cf4a42611973,0xd29098465cf4a42611973d29098465cf4a42611973d29098465cf4a42611973d29098465cf4a42611973,0xd29098465cf4a42611973d29098465cf4a42611973d29098465cf4a42611973d29098465cf4a42611973,0xd290982a5cf4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973,0xd290982a5cf4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973,0xd290982a5cf4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973,0xd28298a62cf1b02621573c9d22077233274881dc8cc6c098855cf4a0a6298b3c9d22077233270521e561,0xc296a06a9d30a5a81aa74c296a06a9d30a5a81aa74c428e88ce572a60622b8ba5cc81754c32a60622b8b,0xc0d6a0751d3462a2158f1d086a84e1d7421aa13875ca90e0675533a44421d5aca90e0675532744226559,0xc6a0e078d53035a81d474d0d098315cf434260c573c558189562f205ca22c5dcc4a888abc73544234559] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_21s1 : Span p3_21 3 3 8 :=
  batch _ _ _ _ #[
0xd29098465cf4a42611973d29098465cf4a42611973d29098465cf4a42611973d29098465cf4a42611973,0xc6a0e078d53035a81d474d103583728f440d60dca3d103583728f440d60dca3c0a8e88ce57312a222af1,0xd29098465cf4a42611973d29098465cf4a42611973d29098465cf4a42611973d29098465cf4a42611973,0xd290982a5cf4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973,0xd0a15858d8f4285616363d18a88563c7462a2158f1c5ca109ab2b312a222af1cc4a888abc702a3a1c395,0xc1ca8852bc7072a214af1cc232898a77212b226ad1c1ca8852bc710a3a23395d1915039d8b464540e762,0xd29098465cf4a42611973d29098465cf4a42611973d29098465cf4a42611973d29098465cf4a42611973,0xc889583568ee842650973c889583568f222560d5a3c8d0e02f5532063a0b995c818e82e6572063a0b995,0xc84358b8a8f210d62e2a354e0e119d51538384675450b1714c59b050d6352a3c14358d4a8d52266445ab,0xc81ae03ab53206b80ead4a620f16255b0a5a81aa74c8d0e02f553234380bd54d18a88b13c7170541e362] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_21s2 : Span p3_21 3 8 14 :=
  batch _ _ _ _ #[
0xc11728531772a43819d54d111584758f4445611d63d01750af18b1423a19995d111584758f1423a19995,0xd016a84e1d7236062558bc1c2a870ad6c47306bd10c888e82e657236062558bd18a88563c74a0a6298b3,0xd29098465cf3a4443195ad29098465cf4a42611973d29098465cf310aa232b5c118e866657340ca21c9d,0xcd0328872773305433362c1195846e8f0465611ba3c297109a96b0465611ba3c9832833277421d42bc62,0xc819582ae8f206560aba3c819582ae8d5383846754d08750af18b029ca1685d421af182b5b310aa232b5,0xd29098465cf4a42611973c0d7109716b1543819d54c9d220772331543819d54c550e067553466842e8ca,0xc550e0675530465611ba3c0d7109716b1a1a82a674d19a10ba32b234380bd54c8d0e02f5534a42611973,0xc8d0e02f553234380bd54c8d0e02f553234380bd54ce82a0a5ad3421aa14675d086a8519d70465611ba3,0xd18a88563c50873a70715c1c2a870ad71b02622373d18a88563c7274881dc8cc888e831e57029ca1685d,0xc6c09888dcf405d42e662d18a88563c71b02622373c983283a277260ca0e89d] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_21s3 : Span p3_21 3 14 19 :=
  batch _ _ _ _ #[
0xc983283a27730a522a7a1d18a88563c7462a2158f1d1a14859d874685216761d18a88563c70465611ba3,0xd111584758f4445611d63c888e82e6572223a0b995c888e82e6571b02622373c6c09888dcf06a52157a1,0xc5d11098d6b1aa062a98bd111584758f4445611d63d111584758f4445611d63d111584758f4445611d63,0xc508e8666571423a19995c447507a98b3a84232959c447507a9896845650d63c6a818aa62f1aa062a98b,0xc983283a277205ca22c5dd19a10b332b031aa1c475843ca9684d71a1c42e85ac888e82e657111aa23475,0xc0c6a88d1d7074a81d2b4cd032887277440d629ca3c6a8188ae2f408d60eaa3c888e82e657270521e561,0xd290982a5cf4a4260a973c88ae0373534a4260a973c818e82e6574a4260a973c550e0ccd53260ca0cc9d,0xc0c6a8711d7206560aba3c819582ae8f440d60dca3c819582ae8f0465611ba3c1195846e8f0465611ba3,0xc296a06a9d3230560e563c296a06a9d3260ca0cc9dd103583728f072a2254f1] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_21s4 : Span p3_21 3 19 24 :=
  batch _ _ _ _ #[
0xd111584758f4445611d63d111584758f4445611d63d111584758f4445611d63d111584758f4445611d63,0x8c2a71aa31b2223a0c795c888e831e57031d433a6294a0f10e55b4445611d63d111584758f4445611d63,0xd0d09850dcf4342614373d182a831ad72223a0c795c5d11098d6b210d60eaa3c686a0a99d3174442635a,0xc98328332774342614373c98328332772a4380e754d016a8519d7405aa14675c118e885e561c13a63c15,0xd111584758f4445611d63d111584758f4445611d63d111584758f4445611d63c0a7285a177464540e762,0x843ca9684d70463a19995c1ca8852bc7045ca14c5dc983283a277260ca0e89dc888e82e6572223a0b995,0xd290982a5cf2063a0b995c9832833277260ca0cc9d950399132af0463a19995d1a14859d874685216761,0xc9894875687031d41ea62d1915039d8b464540e762d290982a5cf4a4260a973c818e82e6572063a0b995,0x99d0517350b0b0a621ab38d0a719531b0b0a621ab3c118e885e573a84232959c989487568682e645c1aa,0xc889583568f210d60eaa3c818e831e572063a0c795] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_21s5 : Span p3_21 3 24 29 :=
  batch _ _ _ _ #[
0xd290982a5cf4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973,0xc8d0e02f553234380bd54c8d0e02f553234380bd54c818e82e6572063a0b995c818e82e6572063a0b995,0xc9d22077233230560e563c8c1583958f270521e561d15218b322f4a4260a973d290982a5cf4a4260a973,0xc550e0675531543819d54d182a831ad7115c42cc5ace82a0a5ad3466842e8cac8d0e02f553274881dc8c,0xc0a7285a177230560e563c8d0e02f553234380bd54d182a831ad7206560aba3c9c14879587206560aba3,0xc9d22077233230560e563d1915039d8b260ca0e89dd023583aa8f408d60eaa34f086989e172223a0c795,0xc819582ae8f0a5a81aa74d023583aa8f1b02621573d023583aa8f4a0a6298b3c8c1583958f260ca0e89d,0xc819582ae8d560cc4589ec6c098855cf206560aba3c819582ae8f30a522a7a1c0c6a8711d7206560aba3,0xc888e82e6572223a0b995c8c1583958f06a52157a1c8c1583958f1a83831754c983283a27730a522a7a1,0xc6a0e0c5d532223a0b995c1a94855e8706a52157a1] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_21s6 : Span p3_21 3 29 33 :=
  batch _ _ _ _ #[
0xd0d098315cf1423a21795d182a831ad7460aa0c6b5d0d098315cf434260c573d0d098315cf434260c573,0xd0d098315cf434260c573d182a831ad72223a0c795c5ca109ab2b210d60eaa3ce91108756b156062558b,0xc98328332770b0a621ab3d103583728f434260c573c1ca8852bc7434260c573c118e885e57035a81d474,0xc1ca8852bc7434260c573c508e866657035a81d474d0d098315cf434260c573c0a7285a177464540e762,0xba1099425cf0463a19995c1ca8852bc7045ca14c5dc983283a277260ca0e89dce91108756b434260c573,0xc6a0e0c5d532063a0b995d103583728f0b0a621ab3c0d6a0751d306a52157a1c1a94855e87072a214af1,0xd103583728f440d60dca3c818e82e6572063a0b995] 52 (by decide +kernel)

private theorem p3_21Good : Good p3_21 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_21s0 (joinSpan p3_21s1 p3_21s2)) (joinSpan (joinSpan p3_21s3 p3_21s4) (joinSpan p3_21s5 p3_21s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_22s0 : Span p3_22 3 0 7 :=
  batch _ _ _ _ #[
0xd110e833357205ca22c5dc447507a98b10ab81d394c42ae074e532660a1cc8dc54a1852e2f045ca14c5d,0x80bb918c6aa02f2a53135c9d22079533274881e54cc9982873237172841cb8ad110e8333574443a0ccd5,0xa9887172a1a8316662c2bd05298315cf0a8b833354ce88888eac6a843c688d6cd5220cd533474222c4f1,0xc9d22079533414a60c573c5ca1072e2aa843c688d6c5ca1072e2b3a0c421d5ac54a1852e2f2a0b819d54,0xd282982a5cf4a0a60a973c9982873237172841cb8ac1172853177045ca14c5dc1172853177408d632363,0xc998287a2365443c458d685dc8155cc307622256b1d282982a5cf4a0a60a973d282982a5cf4a0a60a973,0xa60c9942ccf2b08622d4bc1d88895ac684ccc5415ecac2188b52f2b08622d4b948c990acce5232642b33,0xc456a0559d302a562e2a3cec0888abc7316222c6b1c42ae074e532328622b8bca82e0675531528614b8b,0xc0d6a0ad1d3045ca14c5dc9d22079533045ca14c5dc11958a728ebc81872ac4c9d22079533115a81d474,0xccc0a888bd7206560dca3d10ac8ae647115a81d474] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_22s1 : Span p3_22 3 7 13 :=
  batch _ _ _ _ #[
0xc50728531772a0b819d54c5c0a850bd71702a142f5c1ab0852e6706ac214b99c98948772872303a262d5,0xc686a04e9d306ac215999ca82e02f5532a0b80bd54ca82e02f55306ac214b99c1ab0852e672303a262d5,0xc5a8287a23706ac215999c5c0a850bd71702a142f5c99828732372660a1cc8dc9d22079533274881e54c,0xc11958a728e8cca853174c456a0559d28cca853174d0aa18aa62d3c650e9ca0c5a8287a23716a0a1e88d,0xc852e039d53206560dca3c852e039d53214b80e754c819583728f206560dca3c1172853177045ca14c5d,0xc5072853177141ca14c5dc5c0a850bd71702a142f5c1ab0852e6706ac214b99c98948772872303a262d5,0xc427285a17706ac215999c5c0a850bd71702a142f5b99881762c3141ca14c5dcc588895ac72a0b819d54,0xc88ae02ee53222b80bb94c88ae02ee532660a1cc8dc9982873237262521eaa1c989487aa87262521eaa1,0xc998287a237111d41dc62832a598ae0f17428152f4c852e039d53222b80bb94c88ae02ee53222b80bb94,0xc447507718b111d41dc62cac2188b52f054b833354c852e078d532660a1e88dc852e078d521615c5d426] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_22s2 : Span p3_22 3 13 18 :=
  batch _ _ _ _ #[
0xc9982873237212b21cb91c9982873237172841cb8ac84ac872e4716a0a1e88dc5d0a054bd3074c42635a,0xc143584758f050d611d63c143584758f050d611d63d191503738b111d41ea62c5a8287a237206560dca3,0xd282982a5cf2303a0ccd5d282982a5cf4a0a60a973d282982a5cf266881d58cc843582b58f050d611d63,0xd190a8313d7210d60ad63c989487aa87210d60ad63c143584758f050d611d63d282982a5cf4a0a60a973,0xc5a8287a23706ac215999c686a06a9d32303a0ccd5d0a0e83a357222560eaa3d190a8313d7262521eaa1,0xc84ac872e474642a0c4f5ca82e02f5530a5a82b474c1d31098d6b2a0b80bd54ca82e02f553029ca1685d,0xc143584758f050d611d6394a0f112b5b050d611d63d190a8313d7172841cb8ac5a8287a2373b02222af1,0xd282982a5cf4a0a60a973c8c0e8333572303a0ccd5cec2108f52b405d42e662c81ae035e53210d60ad63,0xd282982a5cf206b80d794d282982a5cf2303a0ccd5] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_22s3 : Span p3_22 3 18 23 :=
  batch _ _ _ _ #[
0xd0aa18aa62f3a22223ab1c843582b58f210d60ad63c5d0a054bd3050d611d63c5d0a054bd3050d611d63,0xc5d0a054bd306ac215999c8c0e8333572303a0ccd5d0a0e83a3574283a0e8d5c889583aa8f222560eaa3,0xca82e02f5532a0b80bd54ca82e02f5532a0b80bd54d2a218ca52f029ca1685dc1d31098d6b17428152f4,0xd0a0e83a3574283a0e8d5c81ae035e53206b80d794cec0888abc7206b80d794d0a0e83a35717428152f4,0xccd0a0a8bd34443a0ccd5c819583728f205ca22c5dc0d898b0acf111d41ea62cec0888abc606b1a56705,0xc843582b58f050d611d63d282982a5cf30a522e6a1d282982a5cf1528614b8bd282982a5cf206560dca3,0xce88888eac7334282a2f4ce88888eac71a1a813a74c843582b58f1a1a813a74c686a04e9d3210d60ad63,0xc88ae02ee53222b80bb94cac2188b52f2b08622d4bc88ae02ee53222b80bb94ccd0a0a8bd33a22223ab1,0xc54a1852e2f2a0b80bd54c5ca1072e2b3b02222af1cac2188b52f222b80bb94c5d0a054bd3314c42635a,0xcec0888abc71528614b8bc550e0d4b533b02222af1421b99426af2328622b8b598869732172a0b80bd54] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_22s4 : Span p3_22 3 23 29 :=
  batch _ _ _ _ #[
0xc852e039d53115a815674c29898a62cf214b80e754c998287a237111d41dc62c447507718b2b08622d4b,0xc84ac872e4716a0a1e88dd191503738b16a0a1e88dc456a0559d3115a815674c98b08956661772055730,0xd191503738b214b80e754c456a0559d3206560dca3c852e039d533328423b8ac9982873237214b80e754,0xcc588895ac7266881d58cc843582b58f4a0a60a973d282982a5cf4a0a60a973d282982a5cf4a0a60a973,0xc50ae066e534283a0e8d5c1ab0852e672303a0ccd5ce90a0a53d32303a0ccd5c852e039d53214b80e754,0xd0a0e83a357222560eaa3c88ae02ee53222b80bb94d190a8313d7210d60ad63c989487aa87210d60ad63,0xca82e06755316a0a1e88dc5a8287a2374642a0c4f5b9a3015a5634283a0e8d5c1ab08566672303a0ccd5,0xd190a8313d7029ca1685dce83108756b4283a0e8d5ce90a0a53d34642a0c4f5c5ca1072e2b2a0b819d54,0xc6a0e0c6b533a0c43195ac9d220795333a0c43195ace8888ae2c7046b829794c9982899a37050d611d63,0x5489991a2af206b80d794ce8310c656b2303a0ccd5c9982899a372660a2668dc8c0e8333572303a0ccd5] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_22s5 : Span p3_22 3 29 34 :=
  batch _ _ _ _ #[
0x59c06953317414a60c573d0a0e83a357274881e54cc686a04e9d3050d611d63d05298315cf414a60c573,0xc427285a17706ac215999c8c0e8333572303a0ccd5d05298315cf414a60c573c889583aa8f222560eaa3,0xd05298315cf4283a0e8d5ca82e0675532a0b819d54d0a0e83a3574283a0e8d5a195a1598b3414a60c573,0xd0a0e83a3574283a0e8d5c81ae035e53206b80d794ce83108756b206b80d794d05298315cf3a0c421d5a,0xc5ca1072e2b111d41ea62d110e833357205ca22c5dc1a948b9a87464540dce2b814e1770533a2222b8b1,0xc843582b58f414a60c573c0d6a0ad1d330a522e6a1d110e8333571528614b8bd110e833357206560dca3,0x948c990accf414a60c573d02ac8b1e470a8b831754c843582b58f32a0a2668d599b0156663210d60ad63,0xc88ae02ee53222b80bb94d05298315cf414a60c573c88ae02ee53222b80bb94d1d088b13c550666468ab,0x5702e10f5533a0c421d5acc2948d5a87414a60c573cc2948b9a87222b80bb94c5aa2055e3150666468ab,0xce83108756b1528614b8bd05298315cf3a0c421d5ac456a0751d33a0c421d5ac5ca1072e2b172841cb8a] 80 (by decide +kernel)

private theorem p3_22Good : Good p3_22 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_22s0 (joinSpan p3_22s1 p3_22s2)) (joinSpan p3_22s3 (joinSpan p3_22s4 p3_22s5)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_23s0 : Span p3_23 3 0 7 :=
  batch _ _ _ _ #[
0xcd5108d1567434260c573d10ac8ae64735488354cc843ca94c4d735442345599502f11635a540bc458d6,0xc0aae074e533a44421d5ac11728531772a43819d54cac0c88f5471a83833354cd5108d15673a2222b8b1,0xc0aae074e525c42642973c98948772871528614b8bc8ca188ae2f052b21cb91ce8888ae2c7434260c573,0xc8ca188ae2f35488354ccc0c7507a98b440ba0ccd5d102e833357440ba0ccd5c0c7507a98b02ab81d394,0xac4c51af40a8872650b339502f11635a22c5c5a16688b1716859a5072642b33941c990acce5072642b33,0xca90e067553045ca14c5dc54a1852e2f205ca22c5da21c9942ccee66205cab0a531315057a8872650b33,0xc0c7507a98b1528614b8bc54a1852e2f1528614b8bc0d6a0559d310a562e2a3c54a1852e2f212b223b91,0xd290982a5cf4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973c84ac872e46560e444cea,0xca90e067553045ca14c5dc0d6a0751d3035a81d474c1c2a850bd7070aa142f5c842e898b57440ba318d5,0xca90e02f5532a4380bd54ca90e02f553035a81d474c0d6a0751d3210ba262d5] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_23s1 : Span p3_23 3 7 13 :=
  batch _ _ _ _ #[
0xc5072853177262521dca1c50728531772660a1e88d113372a439b262521dca1c0d6a0751d32660a1e88d,0xc2989886acf40ab22b991c11ae066e530a5a813a74cc42a888bd7222560dca3ce9110c656b035a81d474,0xcd5220d533330ac22a999cc42a888bd72a0b829cd4c2989886acf0a62621ab3c1c2a850bd7070aa142f5,0xc842e898b57210ba262d5c1c2a850bd7070aa142f5c842e898b57440ba318d5d0aa18aa62f4a83233951,0xc1c2a850bd7070aa142f5cd18288f237405d42bc62c1172853177045ca14c5dc11728531772a43819d54,0xc889583728f222560dca3c5072853177141ca14c5dcea220cab33262521dca1c1a9487aa87035a815674,0xc2989886acf0a62621ab3c11ae066e5306ac215999c8d0e039d53222560dca3c8d0e039d53234380e754,0xc81ae02ee53206b80bb94c81ae02ee53206b80bb94c81ae02ee5342a862a98bcc5888b1ac70a62621ab3,0xc8c1582b58f1505611d63c541584758f1505611d63c541584758f1505611d63c8d0e039d53206b80bb94,0xd290982a5cf4a4260a973d290982a5cf210ba0ccd5d290982a5cf4a4260a973d290982a5cf1a1a82b474] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_23s2 : Span p3_23 3 13 18 :=
  batch _ _ _ _ #[
0xd182a8313d5560e8464ecd182a8313d7230560ad63c5d11098d6b230560ad63c541584758f1505611d63,0xca90e02f553109ca1685dc427285a1774a83233951d022e83a357206560eaa3c296a06a9d3210ba0ccd5,0xcd18288f237174442635acd0b0895667460aa0c4f5ca90e02f553212b21cb91c84ac872e472a4380bd54,0xc99a2075633446862c58bc5d11098d6b031d41dc62c1ab0852e67074a8152f4d182a8313d65232645533,0xc1d2a054bd3212b21cb91c0c7507718b031d41dc62c8172899177442b22b991c99a2075633174442635a,0xc550e0ccd53222560dca3c8d0e078d53111d433a62c8d0e078d53031d41ea62cc52a0a8bd34a83233951,0xd10ac8b1e47222b80d794c541584758f1505611d63c541584758f2660a1e88dd183503738b031d41ea62,0xd290982a5cf210ba0ccd5d290982a5cf4a4260a973c842e833357210ba0ccd5c8c1582b58f30ac222b99,0xd290982a5cf222b80d794] 66 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_23s3 : Span p3_23 3 18 23 :=
  batch _ _ _ _ #[
0xc8c1582b58f230560ad63d08750b998b054b8352d4c541584758f074a8152f4c541584758f074a8152f4,0xd022e83a357408ba0e8d5c819583aa8f206560eaa3ccd11098d6b074a8152f4c842e833357210ba0ccd5,0xca90e02f5532a4380bd54ca90e02f5532a4380bd54c427285a1772660a1cc8dc1d2a054bd3212b21cb91,0xd022e83a357408ba0e8d5c88ae035e53222b80d794d022e83a357074a8152f4cd18288f237222b80d794,0xc8c1582b58f230560ad63cac0c88f54716a881578cc5aa2055e332b03223d51c152e0d4b531505611d63,0xc152e0d4b516621a5e885c81ae02ee53206b80bb94c296a04e9d3230560ad63c296a04e9d30a5a813a74,0xcc2948b9a8716a881578cc152e0d4b53206b80bb94c5aa2055e33074a8152f4c81ae02ee53206b80bb94,0xc84ac88ee465382644573c8ca188ae2f2a4380bd54c11728531772a4380bd54c54a1852e2f205ca22c5d,0xcc52a0a8bd3440ba0ccd5c889583728f16a881578c8ea07189d186654a8e81dc54a1852e2f045ca14c5d,0xd290982a5ce560e444cead290982a5cf074a8152f4d290982a5cf222560dca3c8ca188ae2f116262c2b3] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_23s4 : Span p3_23 3 23 29 :=
  batch _ _ _ _ #[
0xc2a2e0c6b5307622256b1c8c1582b58f4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973,0xd022e83a357046b819b94ce9110c656b210ba0ccd5ce82a0a53d3210ba0ccd5c8d0e039d53234380e754,0x598a6175613210ba0ccd5c81ae02ee53206b80bb94d182a8313d7230560ad63ce82a0a53d3230560ad63,0xca90e0675533a44421d5ace82a0a53d3460aa0c4f5d022e83a357212b21cb91d022e83a357206560eaa3,0xd182a8313d7109ca1685dd022e83a3573a44421d5ace82a0a53d3460aa0c4f5ce82a0a53d32a43819d54,0xc8d0e039d53035a815674c99a2075633234380e754c2a2e0c6b53031d41dc62c0c7507718b205ca2645d,0xcc2b08aa667115a82a674d183503738b1543831754c1ab0852e6706ac214b99c8172899177442b22b991,0xd183503738b234380e754c0d6a0559d3222560dca3c8d0e039d5204cdc550e6c456a0a99d3234380e754,0xce9110c656b30ac222b99ce9110c656b2660a1e88dc1ab0852e672b03223d51c541584758f2b03223d51,0xc1ab0852e67222b80d794ce9110c656b210ba0ccd5c9d108995672744226559c842e833357210ba0ccd5] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_23s5 : Span p3_23 3 29 34 :=
  batch _ _ _ _ #[
0xd022e83a357029ca3285dcc2b08aa667434260c573d0d098315cf434260c573c541584758f0a5a813a74,0xd0d098315cf434260c573c819583aa8f206560eaa34f1b018ae6306ac215999c842e833357210ba0ccd5,0xd022e83a3572a43819d54ca90e067553434260c573d022e83a357408ba0e8d5d0d098315cf274882e4cc,0xd022e83a357408ba0e8d5c88ae035e53222b80d794d0d098315cf06ac215999ce91108756b222b80d794,0xc8c1582b58f230560ad63cd5220d53333544234559cd5108d1567434260c573c6a0e0c5d53434260c573,0xd0d098315cf434260c573c81ae02ee53206b80bb94ccaa20a9e33230560ad63c6a0e0c5d533544234559,0xa620f181d5b434260c5735489991a2af206b80bb94c5aa2055e333544234559c81ae02ee53206b80bb94,0xd0d098315cf3a44421d5ac8ca188ae2f32a882a78cc14ac872e47052b21cb91c14ac872e473a44421d5a,0xc0c7507a98b052b21cb91d102e833357460d40dce2c9d220b93332744226559c54a1852e2f045ca14c5d,0xc84ac88ee465c42642973d102e83335732a0a2668dd102e833357222560dca3c8ca188ae2e60caa540f5] 80 (by decide +kernel)

private theorem p3_23Good : Good p3_23 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_23s0 (joinSpan p3_23s1 p3_23s2)) (joinSpan p3_23s3 (joinSpan p3_23s4 p3_23s5)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_24s0 : Span p3_24 3 0 6 :=
  batch _ _ _ _ #[
0xc8d8189722e5c42642973c8d8189722e5c42642973c84ac89ab4746684358ca9710990a5cf2660a1e88d,0xd290982a5cf4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973,0xc1a32850e77111d41ea62c1a32850e771a226298b3c5ca109ab2b266882e4ccc68898a62cf3a0c42999a,0xd102e82e657440ba0b995cac2188ae2ee2c2853174c5ca109ab2b266882e4cc10d59a330af2b08622b8b,0xb8b0a14c5d31728425cca8531714c59a177205d53011aa72b0b1b068ca1439dc9d2207563210f2a53135,0xc9d108995672660a1e88dc50728531765c42642973ac8531aa07b1a8381e354c6a0e078d53440ba0b995,0xc6a0e078d52e842650973ba1099425cf274881d58cc0d6a0751d3035a81d4749710990a5cf2744226559,0xc447507a98b2660a1e88dd0a158c8d8f2660a1e88dc887288b177115a82b474c9d220756331a8381e354,0xd290982a5cf4a4260a973d290982a5cf4a4260a973d290982a5cf4a4260a973c1a32850e77156062cc8b,0xd102e82e657440ba0b995d1915039d8b464540e762c1a32850e771a226298b3cc232888e772660a2668d] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_24s1 : Span p3_24 3 6 12 :=
  batch _ _ _ _ #[
0xc5c15078d8b170541e362c2a2e066e530a8b819b94c5aa205ab333a4443195ac5aa205ab3316a8816acc,0xc427285a177210ba1c395ae608a81dc70a62621ab3c9832831677260ca0c59dc5c15078d8b234380bd54,0xc819583aa8f234380bd54c8d0e02f553234380bd54c5c15078d8b170541e362c427285a177109ca1685d,0xc8d0e02f553170541e362c8d8189722f2360625c8bc81728991771a226298b3ccc150ccd8b3a0c42999a,0xcc2948cea87310d42b3a2c842e88ce57210ba23395c6c09888dcf1b02622373c1c35074e8b234380bd54,0xc889583728f222560dca3c142e870e5716a8816accc5c15078d8b141ca14c5dc1c35074e8b210ba1c395,0xc1435854e8f0a62621ab3c1c35074e8b210ba1c395c9d22075633405d433a62c1c35074e8b454862c58b,0xc5aa205ab331543819d54c1c35074e8b0a5c426a5ac297109a96b050ba23395d08750af18b4668434aca,0xc8d0e02f553156062cc8bc5aa205ab3316a8816accc0d7109716b035c425c5ac550e0675531543819d54,0xc142e88ce57050ba23395c5aa205ab33234380bd54] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_24s2 : Span p3_24 3 12 17 :=
  batch _ _ _ _ #[
0xc8d0e02f553050d6153a3c1435854e8f050d6153a3505c59ab40f0a62621ab3c427285a1771543819d54,0xc1c35074e8aa621c5d886c819583aa8f234380bd54c8d0e02f553234380bd54c8d0e02f553234380bd54,0xc6c09888dcf1a226298b3d01750b998b16a8816accc8d8189722f2360625c8bc6c09888dcf1b02622373,0xc296a06a9d30a5a81aa74c550e0675531543819d54c6c09888dcf1b02622373a133a14c6b316a8816acc,0xc8d0e02f553234380bd54c8d0e02f552b58c065598c1435854e8f050d6153a3a5cc8274cc33a0c42999a,0xc8c1582b58f111d42bc62c1d31094e6b230560ad63c8c1582b58f1505611d63c541584758f1505611d63,0xc541584758f1505611d63c98328316774a4260a973ccca109732b4a4260a973ccca109732b116262c2b3,0xc5a8287a237212b22ccd1c5ca109732b230560ad63c8c1582b58f408ba0b995c8c1582b58f1505611d63,0xc1d31094e6b206560eaa3c9832831677440d60d5a3] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_24s3 : Span p3_24 3 17 22 :=
  batch _ _ _ _ #[
0xc0c7507718b408d60aba3843ca9684d7408d60aba3c5ca109732b1aa0626a8bcc2948cea8730a5233aa1,0xc1435846e8f050d611ba3c0c7507718b440ba0b995c5ca109732b174442635accca109732b408d60aba3,0xc843582ae8f210d60aba3c1d31094e6b210d60aba3c6a818ba22f210d60aba3c1435846e8f050d611ba3,0xccaa20cab331505611d63c889583728f054b81d394c152e074e5316a0a1e88dc0d89894acd5644c4455e,0xd1835035e8b408d60aba3c0d89894ace1615c55626c1d31094e6b1505611d6395839111eab1505611d63,0xc541584758f1728425ccac541584758f1505611d63c0d89894acf4a4260a973c5aa205ab33074c42539a,0xd2a218aa62f460d40d7a2c8c1582b58f460d40d7a2d1835035e8a508e6429abc1d31094e6b052b225cd1,0xc541584758f1505611d63c541584758f1505611d63d1835035e8b206560eaa3c819583aa8f206560eaa3,0xd01750b998b440ba0b995c5aa205ab33230560ad63d023582ae8f2a4380e754c541584758f405d42e662] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_24s4 : Span p3_24 3 22 27 :=
  batch _ _ _ _ #[
0xc0d89894acf210d60aba3c1d31094e6a16ae0568e8c1435846e8f050d611ba3c0d89894acf312a222af1,0xccd110d0d6b1505611d63c889583728e538264457394e099115cd0b31656b03ca90e039d532a4380e754,0x94e099115cf230560ad63c5ca109732b230560ad63ca98189aa2f06a52356a1c1a948d5a871505611d63,0xc1435846e8f050d611ba3c1435846e8e2b81666543c819583aa8f1728425ccac819583aa8f3a8882a78c,0xc45898b0acf222560dca3c1ca8852bc746684358cac843582ae8f141ca14c5d8ea38189ea32b08622b8b,0xc9832831677440d60d5a3d103583568f115c42cc5ac558189722f3a84232959cea108ca567464540e762,0xd290982a5cf4a4260a973c427285a177260ca0c59dc427285a177464540e762843ca94c4d7440d60d5a3,0xc0d7109716b440d60d5a3c9832831677111d41ea62c55818b322f408ba0c795c45710b316b4a4260a973,0xc8d0e02f5533a4443195ad022e831e57052b234ad1] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_24s5 : Span p3_24 3 27 33 :=
  batch _ _ _ _ #[
0xc8d0e02f553312a222af1c843582ae8f1543819d54d1835035e8b460d40d7a2c5ca109ab2b1543819d54,0xa620f181d5b2b08622b8bc1ca8852bc7072a214af180d599530af1728426acac8d0e02f553234380bd54,0x5a02e962657234380bd54c5a82899a371a226298b3cc4a888abc7210d60aba3ce8310a666b210d60aba3,0xd102e831e57230560ad63ccca109732b460d40d7a2d1835035e8b408d60aba3c1ca8852bc7234380bd54,0xd1835035e8b460d40d7a2d0d098315cf434260c573ce9110c656b16a8816accc5aa205ab33454862c58b,0xc819583aa8f206560eaa394a0f10e55b230560ad63c0a728ca177230560ad63c5a8287a237460d40d7a2,0xd023582ae8f1505611d63d0d098315cf408d60aba3d023582ae8f408d60aba3d0d098315cf206560eaa3,0xd022e82e656e68c055998c0d6a0751d3434260c573d01750b998b440ba0b995c5aa205ab33230560ad63,0xc889583728e10f2a53135c456a0ad1d202f2a5a135c5ca109ab2b210d60aba3d022e82e657408ba0b995] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_24s6 : Span p3_24 3 33 35 :=
  batch _ _ _ _ #[
0x94a0f111d5b230560ad63c5ca109732b230560ad63d0d098315ce5072642b33d0d098315cf434260c573,0xd022e831e572a6062e88bd022e831e572a6062e88bc819583aa8f1728425ccac819583aa8f434260c573,0x9710990a5cf222560dca380bca9684d7210d60aba3] 20 (by decide +kernel)

private theorem p3_24Good : Good p3_24 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_24s0 (joinSpan p3_24s1 p3_24s2)) (joinSpan (joinSpan p3_24s3 p3_24s4) (joinSpan p3_24s5 p3_24s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_25s0 : Span p3_25 3 0 6 :=
  batch _ _ _ _ #[
0xc5a12850e77031d41ea62c998287a236237306bd10c998287a2373a4442999ac5a12850e773328426aca,0xd110e82e6574443a0b995c998287a237141ca3445dc998287a236873145eb02c8872899176e0ca853174,0xc1ca8852bc7236062cc8b9702990a5cf115c425c5ac1ca8852bc7072a214af1ccca109ab2b442b2358d1,0xd282982a5cf4a0a60a973d282982a5cf4a0a60a973d282982a5cf4a0a60a973d282982a5cf4a0a60a973,0xcd18288f2365c0a642973c456a0751d3115a81d474d15218d152f045ca14c5dc9d22079533442b2358d1,0xc2a2e078d532660a1cc8dba0299425cee80a650973c817288b1772660a1cc8dc0d6a0ad1d30a8b81e354,0xc2a2e078d530a8b81e354c9d108956672744225599c9d220795331684a1439d354c1a1742e10f2a53135,0xcca12888e773a4442999ac5a12850e77312a222af1d110e82e657052b225cd1ca9818ba22f052b225cd1,0xcc4a888abc7031d41ea62cc4a888abc72660a2668dd110e82e6574443a0b995d1835039d8b460d40e762,0xd282982a5cf4a0a60a973d282982a5cf4a0a60a973d282982a5cf4a0a60a973c457109716b1684a1439d] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_25s1 : Span p3_25 3 6 12 :=
  batch _ _ _ _ #[
0xc852e02f553214b80bd54c8872899177221ca2645dc887289917716a8816accc29898a62cf310d433362,0xc6a0e066e513d4c062d58c457109716b3a0c43195ac2c29888dcf0b0a622373c5c15074e8b070d41e362,0xc99128316772644a0c59dc1c35078d8b070d41e362c1c35078d8b214b80bd54c6a0e066e531a83819b94,0xc852e02f553214b80bd54c0a7285a177262521eaa1c989487aa87029ca1685dc0a7285a1772303a1c395,0xc99828732372660a1cc8dc8c0e870e57170541d3a2c889583aa8f070d41e362c1c35078d8b214b80bd54,0xc540e870e57170541d3a2c6a8189aa2f16a8816accc6a0e066e53045ca14c5dc8c0e88ce572303a23395,0xc9d2207953315056153a3d08750ce98b1a1c426a5ac8c0e870e57170541d3a2c819583728f206560dca3,0xcea1088ae67170541d3a2c540e88ce57405d42bc62b832a14c5d3170541d3a2c687109a96b1a1c426a5a,0xcea1088ae672660a1e88dc29898a62cf421d42e662c2c29888dcf0b0a622373d08750b998a8cca853174,0xc2c29888dcf0b0a622373cea1088ae6716a8816acc] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_25s2 : Span p3_25 3 12 17 :=
  batch _ _ _ _ #[
0xc457109716952266468abc152e067553054b819d54c457109716b115c425c5ac5aa205ab332303a1c395,0xc152e067553029ca1685dc540e88ce571503a23395cea1088ae67214b80bd54c852e02f552e80a688973,0xc852e02f553214b80bd54c852e02f553262521eaa1c989487aa8715056153a3c5415854e8f15056153a3,0xc152e067553054b819d54c686a06a9d31a1a81aa74c889583aa8f214b80bd54c852e02f553214b80bd54,0xd19a10ba32b214b80bd54c852e02f553214b80bd54ce9110a666b15056153a3c5415854e8f32a0a2668d,0xc447507718b428560aba3999a81563c3428560aba3ccaa20cab33462a22c4f1c84ac897347314c43435a,0xc5415846e8f1505611ba3c447507718b4443a0b995c998287a23706a521eaa1cc2948cea87428560aba3,0xc8c1582ae8f230560aba3c5d11094e6b230560aba3c9982873237230560aba3c5415846e8f1505611ba3,0xc819583728f1728426acac550e074e53154381d3945583311157b11626252b3] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_25s3 : Span p3_25 3 17 22 :=
  batch _ _ _ _ #[
0xc843582b58f031d42bc62c5d11094e6b210d60ad63c843582b58f050d611d63c143584758f050d611d63,0xc143584758f050d611d63c99128316774a0a60a973c1a9487aa8706a521eaa1d282982a5cf036262c2b3,0xd111583568f3425233aa1c42728ca177210d60ad63c843582b58f4283a0b995c843582b58f050d611d63,0xc143584758f050d611d63c143584758f050d611d63c5d11094e6b222560eaa38ee28189dc32644a0c59d,0xd08750b998b4443a0b995cea1088ae67428560aba3ca82e039d53210d60ad63d08750b998b050d611d63,0xccca10d2b2b2a0b80e754ca82e039d531505611ba3c5a8287a237072a214af194a1990a6af1505611ba3,0xc143584758e1a1665682bc819583728f4a8863294bc5ca109ab2b072a214af1c8c1582ae8f174442539a,0xd0a1582ae8f11626252b38195715589b174442539ad1915035e8b2b08622d4bc143584758f050d611d63,0xc4589894acf4a0a60a973cea1088ae67174442539a] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_25s4 : Span p3_25 3 22 27 :=
  batch _ _ _ _ #[
0xc5d11094e6b1a1c426a5ad1915035e8b210d60ad63c143584758f050d611d63c143584758e20cdc5a166,0xd1915035e8b222560eaa3c889583aa8f222560eaa39422f10e55b464540d7a2d1915035e8a52866429ab,0xc817288b177312a222af1c5415846e8f1505611ba381ac6959c17334442c39ac1ca8852bc71505611ba3,0xc843582b58f2b08622d4bc143584758f050d611d63c819583728f036262c2b3c8c1582ae8f045ca14c5d,0xc889583aa8f3a8883274cc889583aa8f16a0a3468dca9818ba22e5232642b33c843582b58f234382b394,0xc8c1582ae8f054b819d54cea108aa667054b819d54d1915035e8b464540d7a2cac2188b52f466842e8ca,0xca90e0a5e53405d435662d01750d598b3328426acac852e02f553214b80bd54c852e02f552a119c9ca46,0x45dd0157463214b80bd54c50728d1177230560aba3ce9110a666b230560aba3cea220c9d33221ca2645d,0xce9110a666b0a626298b3c8872899177214b80bd54] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_25s5 : Span p3_25 3 27 33 :=
  batch _ _ _ _ #[
0xc9912831677444560d5a3d111583568f16a0a1e88dc5a8287a236a621c6c686d1835039d8aa33305eb10,0xd282982a5cf4a0a60a973c1ca8852bc72644a0c59dd1835039d8b029ca1685dc558189722f444560d5a3,0xd0a0e831e57444560d5a3c9912831677031d41ea62cc4a888abc74283a0c795cc4a888abc74a0a60a973,0xd05298315cf428560aba3d0a1582ae8f428560aba3c99a20b9333115c425c5ac852e02f5533a0c43195a,0xd05298315cf3328434acad08750b998b4443a0b995d19a10ba32b428560aba3c843582b58f050d611d63,0xc5ca109ab2b230560aba3c5a8287a23716a0a1e88dd0a0e82e6574283a0b995d0a0e82e657115a81d474,0xc1a9487aa874443a0c795c843582b58f464540d7a2d0a1582ae8f464540d7a2c819583728f3544225599,0xd1915035e8b414a60c573d05298315cf464540d7a2ce8310c656b212b225cd19702990a5cf1728425cca,0xc889583aa8f222560eaa3cd5108956673544225599c843582b58f274881e54cc843582b58f464540d7a2,0xd05298315cf222560eaa3] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_25s6 : Span p3_25 3 33 35 :=
  batch _ _ _ _ #[
0xc819583728f3544225599c8c1582ae8f312a222af1c1ca8852bc74283a0c795c9d108b16674283a0c795,0xc889583aa8f414a60c573cd510895667210d60ad633706a20e9d3210d60ad63d05298315cf414a60c573,0xd05298315cf3544225599c889583aa8d6843a58995] 20 (by decide +kernel)

private theorem p3_25Good : Good p3_25 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_25s0 (joinSpan p3_25s1 p3_25s2)) (joinSpan (joinSpan p3_25s3 p3_25s4) (joinSpan p3_25s5 p3_25s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_26s0 : Span p3_26 3 0 5 :=
  batch _ _ _ _ #[
0xc6c09846ccf1b02611b33c6c09846ccf1b02611b33c6c09846ccf1b02611b33c6c09846ccf1b02611b33,0xd110e82f4574443a0bd15d110e82f4572660a1cc8dc0aae0ace53052b21cb91cd0b08b1667212b223b91,0xc81728991771a22621ab3c99a2075633266881d58cc6889886acf4a42629533c99a2075633262521eaa1,0xad08718ea1b2b08622d4ba86859ba20ea1a166e883b832a14c5d31a1a81aa74c686a06a9d31a1a81aa74,0xc5ca1072e2b10ab81d394c42ae074e532a0b819d54ca82e067553172841cb8ace83108756b212b223b91,0xc0c7507a98b31622256b1cd1a20ad633052b21cb91c1d888b1ac7172841cb8ac99a2075633111d433a62,0xd1835039d8b460d40e762c447507a98b10ab81d394c42ae074e532660a1cc8dc6c09846ccf045ca14c5d,0x89d0717541b1a22621ab3c5a12858c77274881e54cc9982873237172841cb8acca128c8c77460d40e762,0xb940595740f3a22223ab1cac0c8af4470a8b833354cac0c8af4472660a2668dd01750b998b1a22621ab3] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_26s1 : Span p3_26 3 5 12 :=
  batch _ _ _ _ #[
0xc9d220795332660a2668dc6c09846ccf1b02611b33c6c09846ccf2a0b819d54c6c09846ccf1b02611b33,0xcca128c8c772660a1e88dcd1828ce2371684a1631dc14ac872e4702a562e2a3c9894877287052b21cb91,0xc8ca188ae2f1b02611b33c6c09846ccf1b02611b33a9887172a1ae0cc46615aa585315287b1a1a81aa74,0xc456a0559d3172841cb8ac998287a237076222c6b1c54a1852e2e84ccc5415ec42ae074e5310ab81d394,0xc852e039d53206560dca3c852e039d53206560dca3c98b0895667115a81567445eb0156663115a815674,0xc9912839476e0ca853174c1ab0852e6706ac214b99cd1a20ad6332a0b819d54ca82e0675532a0b819d54,0xc11958a728e898a650973c9d22079533115a81d474cea108cac67346882b58cc99128394772644a0e51d,0xd2a0c8cec47206560dca3cd5220cd533115a81d474c0d6a0ad1d3045ca14c5dc9d22079533045ca14c5d,0xc50728531772a0b819d54d19a10b1e2b4443a31715c1ab0852e6706ac214b99c1c35078d8b274881e54c,0xca82e02f5532a0b80bd54ca82e02f553466842c78acd0948af287070d41e362] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_26s2 : Span p3_26 3 12 18 :=
  batch _ _ _ _ #[
0xcd5108d54673a44429d1ac5aa2055e333a44429d1ac686a04e9d31a1a813a74c50ae066e53142b819b94,0xc456a0559d32660a1e88dc98948772873a84232b19cd5108d546732a882a78cb11cc1b33433a22223ab1,0xc456a0559d3115a815674c1ab0852e6706ac214b99c50728531773a84232b19c887288b1773460a3388d,0xc88ae02ee53222b80bb94c686a06a9d306ac215999c989487aa87262521eaa1c427285a17706ac215999,0xd0d098a8ccf11626252b3c81ae035e53221ca2645dc98b08956673b08423d4ac852e039d53214b80e754,0xc81ae035e53314c42635ac1a9487aa87206b80d794c296a0a99d3214b81e354c852e078d533b08423d4a,0xccaa20a9e33052b21cb91c447507a9895073845cd4c819583728f16a881578cd10358c558f440d631563,0xc143584758f050d611d63cc2948b9a87052b21cb91c819583728f212b223b91cd0b0895667172841cb8a,0xc99a2075633266881d58cd1835039d8b266881d58cc843582b58f050d611d63c143584758f050d611d63,0xc447507718b2b08622d4bd1835039d8b2644a0e51d] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_26s3 : Span p3_26 3 18 23 :=
  batch _ _ _ _ #[
0xd0a0e839c57210d60ad63c843582b58d10ee85a1ac41e8697a217210d60ad63c843582b58f050d611d63,0xd0a0e839c574283a0e715c889583aa8f1a1a81aa74c99128394774283a0e715c843582b58f4283a0e715,0x80bca9503d602f2a540f5cac2188b52f222b80bb94cc531098d6b3a8883274cc88ae02ee53222b80bb94,0xc99128394774283a0e715ca82e02f5534283a0e715ca82e02f5515226644cabca82e02f553172841cb8a,0xc143584758f050d611d63c143584758f30ac222b99c14ac872e472644a0e51dd0a0e839c5732a0a2668d,0xd1835039d8b460d40e762d0d098a8ccf460d40e76245cd4157383050d611d63c998287a237050d611d63,0xd1835039d8b109ca1685dc4589894acf06ac215999c4589894acf16a0a1e88dc1ab0852e67214b81e354,0xc143584758f050d611d63c143584758f1a1a813a74d110e82f457206560dca3c427285a177172841cb8a,0xccd110b8c6b262521eaa1c989487aa87214b81e354c686a04e9d3210d60ad63c686a04e9d340ab22b991,0xc427285a177109ca1685d] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_26s4 : Span p3_26 3 23 28 :=
  batch _ _ _ _ #[
0xc44750ce9896129662b83ca82e02f5532a0b80bd54c989487728711626252b3c9894877287031d41ea62,0xc5aa2055e33050d611d63c143584758f1a1a813a74c0c7507a98b206b80d794c81ae035e530a5a82a674,0xd0a0e839c57222560eaa3d0d098a8ccf2b0322bd11d0d098a8ccf210d60ad63d0a0e839c57210d60ad63,0xcca82899a361c13a5cc15c8ca188ae2f16a881578cc88ae02ee5316a881578cc88ae02ee53222560eaa3,0xc54a1852e2f172841cb8ad0a0e839c572a0b80bd54ca82e02f5534283a0e715ccca108ee2a21a9665583,0xc852e039d53111d41dc62c1a9487aa87111d41dc62c1a9487aa87031d42bc62c1a9487aa871503a19d15,0xcca828ce237054b831754c456a0559d30a626298b3c8c0e82f457115a815674c29898a62cf262c225599,0xc6c09846ccf4443a0bd15c852e039d534443a0bd15c819583728f3a44429d1ac5a8287a2370465629ca3,0xd110e82f457206560dca3c6c09846ccf214b80e754] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_26s5 : Span p3_26 3 28 33 :=
  batch _ _ _ _ #[
0xc6889886acf210d60ad63c843582b58f262521eaa1c843582b58f1425631aa3cd1128c5477142b819b94,0xccca108ee2b266881d58cc1ab0856667214b80e75440bba14c6b3222560eaa3c989487aa855644c4551e,0xc9912839477029ca1685dca82e0675532644a0e51dc0c7507a98b3a0c421d5aca82e0675532644a0e51d,0xc843582b58e90f28550f4cec2108f52b1503a19d15d1835039d8b1503a19d15c0a7285a177029ca1685d,0xc1ab0852e670a626298b3d1835039d8b460d40e762c29898a62cf460d40e762c456a0751d30a626298b3,0xd110e82f457460d40e762c427285a17706ac215999d1835039d8b0465629ca3d1835039d8b460d40e762,0xc686a04e9d33a22223ab1cac0c8af4472b0322bd11d110e82f457206560dca3c6c09846ccf111d41ea62,0xc9d220795315306642d2bc6889886acf42a862a98bc6889886acf274881e54cc6889886acf210d60ad63,0xc427285a177109ca1685d548ce11ab53274881e54c] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_26s6 : Span p3_26 3 33 36 :=
  batch _ _ _ _ #[
0xc81ae035e532a0b819d54c0c7507a98b031d41ea62c9d22079533274422e519c9894877287031d41ea62,0xce88888eac74283a0e715c6c09846ccf206b80d794c81ae035e531b02611b33ca82e0675533a0c421d5a,0xc88ae02ee53222560eaa3d0a0e839c57222560eaa3ccaa20a9e330a8b831754465199c14af210d60ad63,0x54c0f10ec5b4283a0e715d0a0e839c57274422e519c8ca188ae2f4283a0e715c88ae02ee5316a881578c,0xc6c09846ccf172841cb8ad0a0e839c573a0c421d5a] 36 (by decide +kernel)

private theorem p3_26Good : Good p3_26 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_26s0 (joinSpan p3_26s1 p3_26s2)) (joinSpan (joinSpan p3_26s3 p3_26s4) (joinSpan p3_26s5 p3_26s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_27s0 : Span p3_27 3 0 5 :=
  batch _ _ _ _ #[
0xc98b08956670a62621ab3d28298a54cf0a62621ab3cd0b08956670a62621ab3d28298a54cf0a62621ab3,0xcac218ab42ee2c2853174c296a06a9d30a5a81aa74c296a06a9d3221ca2645dcac218ab42f07622256b1,0xc0aae074e5302ab81d394c0aae074e532a43819d548332a9684d71528614b8bcc5888b1ac71528614b8b,0xc5ca1072e2b3460a23c8dcc5888b1ac72660a1cc8dc42958b8a8f07622256b1c84ac872e4702a56352a3,0xc2c29846ccf0b0a611b33c2c29846ccf0b0a611b33c2c29846ccf0b0a611b33c2c29846ccf0b0a611b33,0xd102e82f457440ba0bd15d102e82f457316222c6b1c42ae0ace53266881d58cc1d88895ac7111d433a62,0xb940595350f308ca3231dd08750b998b0a62621ab3c2989886acf442b22c7919502f115c5b068ca1631d,0xc2c29846ccf2a43819d54c2c29846ccf0b0a611b33cec210af42b3544234559cac0c88f5472b03223d51,0xc998287323710a562e2a3c447507a98b212b21cb91c8ca188ae2f262522e6a1c2c29846ccf0b0a611b33] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_27s1 : Span p3_27 3 5 12 :=
  batch _ _ _ _ #[
0xd1915039d8b464540e762c0c7507a98b02ab81d394c0aae074e533a0c429d1ac2c29846ccf1528614b8b,0xd10ac8ae647068ca1631dd10ac8ae647474842e70ad1915039d8b308ca3231dc0c7507a98b262521dca1,0xc2c29846ccf02ab81d394c0aae074e53205ca22c5da195315287b0a5a81aa74b8b1119856b2b0862ad0b,0xc0aae074e53035a815674c99828732371528614b8bc11728531771528614b8bc2c29846ccf0b0a611b33,0xc9832839477260ca0e51dd28298a54cd02e5c5d0a6c1a9487aa872a43819d54ca90e0675532a43819d54,0x4f5061c9d13035a815674c99a2075633035a81567431d432b183b4a88632b0bc98328394774a88632b0b,0xc1ab0852e6706ac214b99a66099425cf170541e362c8d0e039d53222560dca3c8d0e039d53222560dca3,0xca90e02f55306ac214b99c1ab0852e67170541e362ca90e067553045ca14c5dc99828732372660a1cc8d,0xc50728531755233845cd4a66099425cf262521dca1c0d6a0751d282f28550f4ca90e02f5532a4380bd54,0xcc2b088ae67222560dca345eb0156663035a81d474c5072853177262521dca1] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_27s2 : Span p3_27 3 12 17 :=
  batch _ _ _ _ #[
0xc9d1089956531a1a73885ce8310a746b32a0a2668dc5aa2055e3316a881578cc296a04e9d30a5a813a74,0xccc150ccd8b210ba1e315d01750af18b035a815674d02ac8b1e46c63146ccc2d15218d542f3544234559,0xd10ac8ae6474a88632b0bc1ab0852e6706ac214b99ccc150ccd8b045ca14c5dd10ac8ae64706a521eaa1,0xc296a06a9d3206b80bb94c81ae02ee5342a862a98bd1d210d5c2b0a62621ab3c989487728706ac215999,0xc8c1582b58f1505611d63c541584758f1505611d63c541584758f1505611d63c8d0e039d53234380e754,0xc0c7507718b262c225599d1915039d8b260ca0e51dc8d0e078d53234381e354d1915039d8b1a1a82b474,0xd022e839c57230560ad63c8c1582b58f2b03223d51cac0c88f547230560ad63c8c1582b58f1505611d63,0xc81ae02ee53334442635acac218ab42f206b80bb94c81ae02ee53408ba0e715c8c1582b58f408ba0e715,0xd022e839c57408ba0e715c819583aa8f0a5a81aa74c9832839477221ca2645d] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_27s3 : Span p3_27 3 17 22 :=
  batch _ _ _ _ #[
0xca90e02f553408ba0e715ca90e02f5532328622b8bca90e02f553314c42e31a843ca9503d610f2a540f5,0xcac0c88f546560e44672ad022e839c57052b21cb91c9832839475510bc43b16c9832839477408ba0e715,0xc99a2075633266881d58cc99a207563330ac222b99d05298a8ccf03626252b3c88ae035e5306ac214b99,0xc889583728f334442635ad11158c558f4445631563c88ae035e53334442635acd1a20ad633222b80d794,0xc5ca1072e29510bc43b16c889583728f031d41ea62c5ca1072e2b3b08433b0ac14ac872e47052b21cb91,0xc8d0e078d531505611d63c1ab08566670a5a813a74c541584758f1505611d63584a5952e0f3328423b8a,0xc1ab085666706ac215999cc5310b8c696b01662d4340bba14c6b30a5a813a74c8c1582b58f0a5a813a74,0xc84ac872e472660a1cc8dca90e02f5532a4380bd54c1ab085666706ac215999c1ab085666703626252b3,0xc5ca1072e2b222b80d794c88ae035e532660a1cc8d] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_27s4 : Span p3_27 3 22 28 :=
  batch _ _ _ _ #[
0xd1915039d8b1505611d63c541584758e508bc43b16d01750b998b1505611d63c541584758f1505611d63,0xc0d89894acf4a83233951c0c7507718b234381e354d1915039d8b464540e762cd1828d1a37414a62a333,0xd102e82f457222560dca3c0a7285a177464540e762c0c7507a98b06ac215999c0d89894acf031d41ea62,0xc8c1582b58f414a62a333c5aa2055e3316a881578cc541584758e3a8e072728c296a04e9d31505611d63,0xc819583aa8f408ba0e715c819583aa8f206b80bb94cac218ab42f206b80bb94c8c1582b58f408ba0e715,0xd022e839c572a4380bd54c5aa2055e323a81c62746c84ac88ee47111d41ea628314e973057205ca22c5d,0xc8c1582b58f046b819b94cac218ab42f07622256b1cc5310b8c6b408ba0e715c11728531772a4380bd54,0xc819583aa8f316222c6b1443ba14c6b30a62621ab35583311547b230560ad63c8c1582b58f0a62621ab3,0xc447507a98b3a44421d5aca90e067553260ca0e51dc1d88895ac716a0a1e88d5583311547b234380e754,0xc427285a177109ca1685dc9832839477109ca1685dca90e067553260ca0e51d] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_27s5 : Span p3_27 3 28 33 :=
  batch _ _ _ _ #[
0xc8d0e039d53346882b58cc0c7507718b30ac222b99c0c7507718b050ba19d15c99a2075632e68c056b18,0xc1d88895ac71543831754c1ab0852e67266881d58cc99a2075633210ba0bd15c0d6a0559d31a226298b3,0xc8d0e039d53440ba0bd15c8d0e039d53440ba0bd15c889583728f3a0c429d1accca108ee2b266881d58c,0xc296a04e9d29883c58956c11958c6a8e9883c58956d102e82f457222560dca3c2c29846ccf0b0a611b33,0x40bba14c6b30a62621ab3c8c1582b58d510e642d2bc2989886acf421d42e662c2989886acf0a62621ab3,0xc84ac872e47142b829794c447507a98b16a0a1e88dc1ab085666706ac215999541ce11ab516621a66685,0xc88ae035e530b0a611b33ca90e067553111d41ea62c5a8287a237222b80d794ca90e067553172841cb8a,0xc0d6a0751d306ac214b99c142e86745730ac222b99c142e867457464540e762c2c29846ccf222b80d794,0xc0d6a0751d31a226298b3d1915039d8b464540e762c68898a62cf230560ad63c68898a62cf464540e762] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_27s6 : Span p3_27 3 33 36 :=
  batch _ _ _ _ #[
0xc0c7507a98b440ba0bd15c0c7507a98b06ac215999d1915039d8b262521dca1d1915039d8b464540e762,0xc9d108995671a83831754d022e839c5732a0a2668dd102e82f457222560dca3c2c29846ccf464540e762,0xc819583aa8f408ba0e715c819583aa8f206b80bb94cd5108d1567206b80bb94c9d10899567230560ad63,0xc2c29846ccf2328622b8bce91108756b408ba0e715d022e839c57408ba0e715b9a06159d13205ca22c5d,0xcc2948b9a87408ba0e715] 34 (by decide +kernel)

private theorem p3_27Good : Good p3_27 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_27s0 (joinSpan p3_27s1 p3_27s2)) (joinSpan (joinSpan p3_27s3 p3_27s4) (joinSpan p3_27s5 p3_27s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_28s0 : Span p3_28 3 0 6 :=
  batch _ _ _ _ #[
0xc88728991760393a66615c428e870e5710a3a1c395d0235858d8f4548614d4bd152185352e5443c458d6,0xce9810ae62b111d41ea62c9894875687111d41ea62d01a98362cf406a60d8b3c0a958a8e8f10a3a1c395,0xd28298465cf4a0a611973d28298465cf4a0a611973d28298465cf4a0a611973d28298465cf4a0a611973,0xd190a8313d74642a0c4f5d190a8313d74642a0c4f5c296a0ad1d32a2322b991c296a0ad1d30a8b833354,0xc2a2e0ccd53342c234a99c428e870e570b0a621573c2c298855cf454322ccd19510f11635a5443c458d6,0xd28298465cf4a0a611973d28298465cf4a0a611973ce9810ae62b342c234a99c428e870e572a23223b91,0xc8ca189aa2f2328626a8bca88c8ae6470a8b833354d28298465cf4a0a611973d28298465cf4a0a611973,0xd28298465cf4a0a611973d28298465cf4a0a611973ac8531aa07b2a2322b991ca88c8ae6472a2322b991,0xb814e177053464540dce2d191503738b205ca22c5dc817288b1774443a0ccd5d28298465cf4a0a611973,0xd01a98362cf216322c791cac0c89ab47141ca14c5dca82e0675532a0b819d54c8ca189aa2e10f2a5a135] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_28s1 : Span p3_28 3 6 11 :=
  batch _ _ _ _ #[
0xd152185352f262521d5a1d152185352f454322ccd1c8c0e898b571702a142f5c8c0e898b57262521d5a1,0xcc2b089aa671423a19995d1a1485ab86a80bc58956c2a8c88ee4716a881ea8cc8c0e898b572303a262d5,0xd28298465cf454322ccd1c99828716371423a19995c99828716371423a19995cc2b089aa671423a19995,0xc8c0e898b574a0a611973c81728991774a0a611973d28298465cf4a0a611973cc2b089aa67454322ccd1,0xce90a0a53d150666445abb1a0715631b17054352e2c1ab08d6267029ca1685dd150c8b33474a0a611973,0xd28298465cf454322ccd1d0aa18ba22ee68c0569585462e119d533460a2358dc99828716372660a1c58d,0xd152185352f454322ccd1d28298465cf4a0a611973ccc0a888bd7454322ccd1d28298465cf3302a222f5,0xc42728ca175417166ad03d152185352f4548614d4bccc0a888bd7454322ccd1d152185352f3302a222f5,0xc42728ca1771a1a813a74cc2b08ba267405d42e662d016a8519d73302a222f5ccc150b8b8b1702a142f5,0xc889582ae8f222560aba3c889582ae8f222560aba3ccc150b8b8b1a1a813a74] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_28s2 : Span p3_28 3 11 17 :=
  batch _ _ _ _ #[
0xc686a04e9d31a1a813a74443ba1782b34548614d4bc98b089aa672303a262d5d152185352f4548614d4b,0xc44a9894acf1423a19995c508e866657266881dc8cc889582ae8f222560aba3c889582ae8f1a1a813a74,0xa585315607b2223a0b995c888e82e6574a0a611973c11728531774a0a611973c44a9894acf1423a19995,0xd103584758f221ca22c5dd103584758f440d611d63ccc0a888bd7221ca22c5dc44a9894acf112a6252b3,0xb1a07152b1b3302a222f5ccc0a888bd7056322c791c50728531774685216ae1ca82e067553141ca14c5d,0xc0a728ca175098d670563d2a2185a52f266881dc8cd2a2185a52f4a8861694bc5095846e8f1425611ba3,0xd2a2185a52f414a614373c889582ae8f4a8322e8d1d2a0c8ba3474a8861694bc5c0a850bd542c5c6a0e6,0xd103584758f440d611d63c852e078d53334282a2f4cc2b08d6267464540dce2c447507a98a16ae05e8a8,0xc1d31098d695303c44ad6d190a8313d74642a0c4f5d103584758f440d611d63d103584758f440d611d63,0xd190a8313d7342c225c99] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_28s3 : Span p3_28 3 17 23 :=
  batch _ _ _ _ #[
0xc5aa207aa332b0862654bd191503738b054b833354d110e8333571423a19995c14358c558f32a8833a8c,0xc29710ba16b0aa3223b913466a2159d3111aa1c475c0c6a88d1d7421d42bc62d110e8333574443a0ccd5,0xc687109a96b1425611ba3c5095846e8f266881dc8cd01a98362ce1ab305eb10c446a8711d72a0b80bd54,0xc889582ae8f464540dce2c889582ae8e62c2a540f5d08a9832acf422a60cab3d2a0c8ba3474a8322e8d1,0xc5d0a054bd34a8861694bd103584758f440d611d63d103584758f440d611d63c889582ae8f334282a2f4,0xd2a2185a52d0b31656b03cc5310d0d6b2063a0c795c818e831e572a0b80bd54ca82e02f5532a0b80bd54,0xc888e82e6574443a0ccd5c888e82e6571423a19995c508e8666571423a19995ca82e02f553262c22cc99,0xcd0b08d62674443a0ccd59833517858b334282a2f4c817288b17716a0a1478dc5a82851e372223a0b995,0xc5a82851e37141ca14c5dc5a82851e3730a522a7a1c50728531770a5c42e85ad103584758f440d611d63,0xd01a98362cf2a0b80bd54c887288b1772a0b80bd54] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_28s4 : Span p3_28 3 23 28 :=
  batch _ _ _ _ #[
0xcd1a20d5a3330ac22e899c1ab08ba267029ca3285dd0a0e83a357109ca1685dc99a20b9a334283a0e8d5,0xd0a0e83a357115c425c5ac427285a177035c42cc5ac99a20b9a33342522b5a1d0a0e83a3572063a0c795,0xc447507a98b111d41ea62d01a98362cf0a8b831754d01a98362cf406a60d8b3aa10f1a235b221ca2645d,0xc5a82851e365443c458d645dd01574634548614d4bd01a98362cf4548614d4bc2a2e0c5d52508bc44756,0xc0d6a0a99d3029ca3285dc456a0559d3464540dce2c152e0c5d5330ac235899d191503738b464540dce2,0xd190a8313d706a52157a1ca88c8ae64690f447511ad191503738b115a815674c852e039d53031d433a62,0xc888e82e6572223a0b995c98b08ba2672223a0b995d190a8313d74642a0c4f5c2a2e0c5d533a428294f4,0xc858c8b1e47176042578ac11958a568e8654c6541ed190a8313d72223a0b995c1a94855e8706a52157a1,0xc819583568f4283a0e8d5c5d81095e2b3a0c421d5ad190a8313d72a0b819d54ca82e0675534642a0c4f5,0xd190a8313d73a0c421d5a] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_28s5 : Span p3_28 3 28 33 :=
  batch _ _ _ _ #[
0xcc2b089aa673a0c43195ac457109716b3a0c43195ac14358c558f035c42cc5ac14358c558e865685662c,0xc1ab08d2a67115c425c5ac0d710b316b210d60e56359c341795831a83831ad49702990a5cf1a83831ad4,0xc2c298855cf029ca3285dd0a0e83a357422a60cab3d08a9832acf422a60cab3d0a0e83a3574283a0e8d5,0xd08a9832acf422a60cab3c843583958f210d60e563d0a0e83a3574283a0e8d5c818e831e572063a0c795,0xc889582ae8f30a522a7a1c2c298855cf0a8b831754c2c298855cf454322ccd1c2c298855cf1425611ba3,0xc98b089aa67262c226a99c2a2e0c5d52508bc44756c889582ae8f0b0a621573c889582ae8f111aa1c475,0xc508e866657464540dce24f5061ab313210d60e563c2c298855cf06a52157a1c843583958f210d60e563,0xc456a0559d32223a0b995c888e82e6574443a0ccd5d110e83335716a881ea8cc456a0559d3050d631563,0xc2c298855cf406a60d8b3c98b0897267406a60d8b3c0d6a0a99d3111aa1c475d191503738b115a815674,0xc456a0559d3262c225c99ce83108756b406a60d8b3] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_28s6 : Span p3_28 3 33 34 :=
  batch _ _ _ _ #[
0xc0a728ca177222560aba398b0a9503d7464540dce2d191503738b464540dce2d08a9832acf422a60cab3,0xd08a9832acf210d60e563c843583958f210d60e5638531715439b222560aba3] 14 (by decide +kernel)

private theorem p3_28Good : Good p3_28 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_28s0 (joinSpan p3_28s1 p3_28s2)) (joinSpan (joinSpan p3_28s3 p3_28s4) (joinSpan p3_28s5 p3_28s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_29s0 : Span p3_29 3 0 6 :=
  batch _ _ _ _ #[
0xd191503ab8b464540eae2cd42288d6373508a2358dce8310a666b068ca1439dc68898465cf266881ea8c,0xc29898465cf10a5616363c29898465cf0a62611973c9c22871637176041cd4ac2a2e0ace53464540eae2,0xc9c228716373a6043394ace9810ce52b216321cd51c446a8711d7308ca2239dc29898465cf0a62611973,0xc0c750af18b308ca2239dc54a189722f2163226751c0d6a0a99d3408d6153a3d0235854e8f3a0c42999a,0xcd0b08d2a672a0b819b94c98b089aa673a0c421b9ad102e82e657440ba0b995d102e82e656a843c60ad6,0xc6a0e0b8b532328625c8ba60c9942cce9832650b33cc232888e77342c234a99ca82e066e532a0b819b94,0xccaa20cea331560614d4bd1a1485ab871560614d4bc5d8107352b1702a142f5d1a1485ab87210ba1c395,0xb1a0715631b109ca1685dcd032885677262521e561ccc0a888bd716a881ea8cc5d8107352b4685216ae1,0xc98328316773302a222f5c142e88ce55518b845794c68898855cf1702a142f5c842e870e57210ba1c395] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_29s1 : Span p3_29 3 6 10 :=
  batch _ _ _ _ #[
0xa620f182b5b176041cd4ac817289917730ac226a99d1a1485ab874685216ae1c550e0a735316a881ea8c,0xd086a84e1d73360423d4ad086a84e1d7421aa13875ccd8108f52b112a6252b3c296a0ad1d3176041cd4a,0xc842e870e5742a863588bc8d0e037353176041cd4ac5d8107352b205ca2645dd1a1485ab8716a881ea8c,0xd1035846e8f30ac22e899d1035846e8f440d611ba3c550e0a7352888e6509abd1035846e8f440d611ba3,0xce831086e6b3a0c421b9aca82e066e53050d6153a3ca82e066e532a0b819b94c1435854e8f050d6153a3,0xccc0a888bd7112a6252b3d1a1485ab871a22611973ca82e02ee53176041cd4ac29898855cf3a0c421b9a,0xccc0a888bd7112a6252b3c8d0e037353234380dcd44758c18f5433302a222f5d1a1485ab874685216ae1,0xc1435854e8f050d6153a3ca82e066e532a0b819b94b19c8155cc33302a222f5d1a1485ab874685216ae1,0xca82e02ee532a0b80bb94ca82e02ee532a0b80bb94ca82e066e53050d6153a3d016a8519d7405aa14675,0xca82e02ee532a0b80bb94ca82e02ee532a0b80bb94] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_29s2 : Span p3_29 3 10 17 :=
  batch _ _ _ _ #[
0xc296a04e9d3032a62c2b3d1a22851e37050d6153a3ccc0a888bd73302a222f5c1a94859d873a0c42999a,0xc29898465cf2360622d4bc29898465cf3a0c421b9ad1a22851e370a5a813a74b814e17a853112a6252b3,0xca82e02ee532a0b80bb94ca82e02ee532a0b80bb94ca82e02ee532a0b80bb94c29898465cf342c234a99,0xc5072853177141ca14c5db1a07152b1b0762214771c887288b177210ba1c395c152e0a5e531425611d63,0xc297109a96b1425611d63c889582b58f222560ad63c5c0a850bd7115a82a674c50728531770a62611973,0xca90e03ab53050d6153a3c99a207aa33266881ea8cc297109a96b0762214771c842e870e573302a222f5,0xc8ca189722f4685216ae1c852e074e53340ca2159dc889582b58f222560ad63ca90e03ab532a4380ead4,0xc1d31094e6b111d41dc62c852e074e531503a21cd5c0d89888dcf406a60d8b3d01a98362cf054b82b394,0xc81728991774685216ae1d1a1485ab87421aa13875d103583568f406a60cab3c447507718b406a60cab3,0xd023582ae8f408d60aba3d023582ae8f408d60aba3d023582ae8f408d60aba3c540e8873572328625c8b] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_29s3 : Span p3_29 3 17 22 :=
  batch _ _ _ _ #[
0xd190a8313d74642a0c4f5d1035846e8f440d611ba3d1035846e8f440d611ba3d1035846e8f440d611ba3,0xc446a8711d71425611d63c509584758f4443a318d5d08a9832acf4642a0c4f5d08a9832acf422a60cab3,0xc446a8711d7222560ad63c5aa207aa3316a881ea8cd023582ae8e6215655c23d023582ae8f1425611d63,0xc9c228716371425611d63c296a04e9d31425611d63c9c228716371425611d63c889582b58f222560ad63,0xc889582b58f0362622373c889582b58f222560ad63cd0b0897266508e6429abc1d31094e6b2a4380ead4,0xc4589888dcf1162622373d023582ae8f2303a0ccd5c852e074e532a2321e951ca88c87a5472a2321e951,0x8d6069d13174685216ae1d1a1485ab87440ba0b995ccd0a0a8bd34685216ae1d023582ae8f408d60aba3,0xd08a9832acf422a60cab3c8c0e8333572303a0ccd5d1035846e8f440d611ba3d1035846e8f440d611ba3,0xca82e02ee532a0b80bb94ca82e02ee531a1c426a5ad016a8519d72a0b80bb94c6a8185a52f1162622373] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_29s4 : Span p3_29 3 22 28 :=
  batch _ _ _ _ #[
0xc0c750af18b2a4380ead4ca90e03ab5317428152f4ca90e03ab534688a1478dc8ca18b322f30a5232761,0xd1035846e8f440d611ba3d1a22851e370a5a813a749510f112b5b334282a2f4d191503ab895223c43956,0xc686a04e9d11ac68560ecd1a22851e3717428152f4c5d0a054bd3152862cc8bc1d31094e6b440d611ba3,0xd01a98362cf406a60d8b3cd032885677054b829794ce9810ce52b2a0b80bb94ca82e02ee532a0b80bb94,0xc8ca189722f2328625c8bc54a18b322f214b80d794c54a18b322f406a60d8b3d01a98362cf054b829794,0xd103583568f406a60cab3c456a0559d3406a60cab3c540e887357111d41dc62d01a9832acf406a60cab3,0xd023582ae8f408d60aba3d023582ae8f408d60aba3c427285a177464540eae2c98328316771a22621573,0xc8c0e833357206560e563c852e035e53214b80d794d023582ae8f4642a0c4f5d023582ae8f408d60aba3,0xd190a8313d74642a0c4f5d08a9832acf422a60cab3d08a9832acf422a60cab3c819583958f440ba0b995,0xd190a8313d72303a0ccd5c5d81099d2b206560e563ce831086e6b1528625c8bd08a9832acf1503a21cd5] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_29s5 : Span p3_29 3 28 33 :=
  batch _ _ _ _ #[
0x59d061573116665056760c457109716b408d60aba3d08a98362cf050d6295a3c550e0a735296b4056b18,0xd102e82e657234380dcd4d102e82e657440ba0b995c68898465cf3508a2358dd102e82e657210d60d5a3,0xca82e066e532a0b819b94ca82e066e53422a60cab3c686a04e9d2888e6509abd08a9832acf1a1a813a74,0xc427285a1753c65072760c8d0e037353234380dcd4d08a9832acf3a0c421b9ace831086e6b234380dcd4,0xc5d8107352b0a8b829794d191503ab8b464540eae2c2a2e0a5e53050d6295a3d191503ab8b464540eae2,0xd022e831e57408ba0c795c68898465cf3a0c42999a5488f10e55b1a22611973d191503ab8b210d60d5a3,0xd022e831e570a62611973c5d8107352b342c234a99d022e831e573a0c421b9ac8d0e0373531a1a813a74,0xc98b0897267406a60d8b3c446a8711d7408d60aba3c29898465cf031aa23475c558185352f0a62611973,0xcd42288d637210d60d5a3c843583568f222560ad63c5aa207aa3316a881ea8cd01a98362cf1425611d63] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_29s6 : Span p3_29 3 33 34 :=
  batch _ _ _ _ #[
0xcc588889dc6508e6429abc509584758f0762214771d01a9832acf0a5c426a5ad01a9832acf0a5c426a5a,0xc843583568f342c225c99c5d81099d2b222560ad63] 12 (by decide +kernel)

private theorem p3_29Good : Good p3_29 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_29s0 (joinSpan p3_29s1 p3_29s2)) (joinSpan (joinSpan p3_29s3 p3_29s4) (joinSpan p3_29s5 p3_29s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_30s0 : Span p3_30 3 0 5 :=
  batch _ _ _ _ #[
0xc1ca8872ac7408d616363c0a8e870e5702a3a1c395c428e88ce5710a3a23395d152185352f312a223ab1,0xc0a958a8e8f072a21cab1c9894875687262521d5a1c50728d11773284a3231dc457109716b266882e68c,0xd1d08855cc61cc2a5a135c858c895e47408d616363d1d08855cc74742215731ce9110a746b3a44429d1a,0xd110e82f4574443a0bd15cac0c87ac472b0321eb11b832a14c5d302a562a3a3c9894875687312a223ab1,0xc8ca189aa2f421aa14675d086a8519d7421aa14675d0235858d8f4548614d4bd152185352f4548614d4b,0xc99828716372660a1c58dc8ca189aa2f2328626a8bc296a0ad1d30a8b833354d1835039d8b460d40e762,0xc1ca8872ac702a3a1c395c0a8e870e573a0c421d5aca82e0675532328626a8bd1d08855cc72a0b819d54,0xc98b089726702a3a1c395c9982871637072a21cab1cac0c87ac472b0321eb11c2a2e078d530a8b81e354,0xcd0b08d2a67422a60cab3c0a8e870e5710a3a23395b884e33a85310a3a23395c5a12858c765443c45716,0xca88c88ee46e421654b83cca128c8c773b0222b531] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_30s1 : Span p3_30 3 5 10 :=
  batch _ _ _ _ #[
0xc687109a96b0a8b81e354c0a8e870e5604cdc5316615a33210d7a2629c5ca86c11728531771684a1631d,0x8c8571a9898d684c8531ec8ca189aa2e20cdc5a166c428e88ce572b0862654bb832a14c5d34443a0bd15,0xce9810ae62b111d41ea62d01a98362cf3a6042b98aa5cc8152bc2e621465782d0235858d8e3171465cc2,0xc5072853177141ca14c5dce83108756b221ca22c5dd016a84e1d74742215731ca82e06755157888c654c,0xc9894875687054b819d54c152e06755290f28550f4d01a98362cf2b0321eb11cca128c8c772b0321eb11,0xc1c35078d8b221ca2645dd150c8af447070d41e362d152185352f262521d5a1c8c0e878c57054b819d54,0xc44a9894acf115a815674c44a9894acf115a815674d1d08855cc7262521d5a1cc2b089aa67405d42e662,0xc44a9894acf405d42bc62d1d08855cc552266445abc5aa207aa334742215731] 62 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_30s2 : Span p3_30 3 10 15 :=
  batch _ _ _ _ #[
0xc9982871637462a22c6b1d086a8519d7421aa14675cc2b089aa67205ca2645dd086a8519d6898a650973,0xd152185352f4548614d4bcc2b089aa674a42629533d152185352f4a42629533c998287163706ac234a99,0xc152e06755306a52157a1d08750b998b06ac234a99d29098a54cf421aa14675c8172899177421aa14675,0xc9912839477205ca2645dd152185352f4548614d4bccaa20b9a334a42629533d152185352f262c226a99,0xd103584758f440d611d63a26299425cf262c225c99b19c81b13c3045ca3445dcd0b08d2a672644a0e51d,0xc5d81095e2b2163225791c1c35078d8b2a0b819d54d1d08855cc72a0b819d54d103584758f2660a1c58d,0xcc2b089aa668ca1654b83c5aa207aa328ca1654b83b19c81563c32303a1e315cd18288d637421d42bc62,0xd152185352f4548614d4b45e94175683454322bd11c5aa207aa3150666429abcc2b089aa66c6720558f0,0xc152e067553054b819d54d01750b998b405d42e662c152e0675531425611ba3d152185352e84ccc5415e,0xc889582ae8f1a1a813a74c1c35078d8b1503a3331517429a10dcf029ca3285d4c68698d6155233846ad4] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_30s3 : Span p3_30 3 15 21 :=
  batch _ _ _ _ #[
0xc686a04e9d31a1a813a74d016a84e1d7070d41e362c118e86665706a52157a1b1a07155c1b1425611ba3,0xa3285952e0f221ca22c5dd103584758f0463a19995c889582ae8f222560aba3c889582ae8f30a522a7a1,0xc818e82e6572063a0b995c5072853177070d41e362d1d08855cc7262c225c99d103584758f440d611d63,0xce9110a7469098d670563d1d08855cc7266881dc8cd1d08855cc71425611ba3c540e8ccc569883c58b16,0xcc4a888eac61cc2a5a135c889582ae8f222560aba3a222f16255a9614c54a1ed1d08855cc73a44429d1a,0xcca82889e37074c43435a5583311157b32a0a2278dc447507a98a1cc2a5a1358730a9684d7072a21cab1,0xd103584758f440d611d63d103584758f440d611d63d103584758f440d611d63c447507a9893335072ae0,0xc14358c558f1423a21795d0a0e839c574283a0e715cc2948a9e87072a21cab1c54a18d2a2d5303c43b16,0xc99a2077233460d40e762c5aa207aa334443a0bd15d110e82f4572223a0c795c99a207723202f2a540f5] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_30s4 : Span p3_30 3 21 26 :=
  batch _ _ _ _ #[
0xc446a88d1d5530664652bca82e02f553031aa1c47581aa7172a18e614a8cc1d95919119cab174443531a,0xc687109a96b1425611ba3c1a94855e8706a52157a1ca82e02f553221ca22c5dd0d098a8ccf174443531a,0xc889582ae8f2b0862654bcca82889e37222560aba3d08a9832ace518a642973c687109a96b1a1c426a5a,0xcac0c87ac472b0321eb11c99a20772331423a21795c0a728ca1774a8861694bc889582ae8f342c234a99,0xd103584758f440d611d63c447507a98b4443a0bd15ca82e039d53460d40e762c888e831e572223a0c795,0xd2a2185a52f2b0321eb11c2a8c8ae6472a0b80bd5499066a8f117440d611d63d103584758f440d611d63,0xca82e02f553072a21cab1c5072853177440d611d63d103584758f440d611d63d103584758f440d611d63,0xca82e02f5532063a0b995c1a94855e872063a0b995ca82e02f5534283a0e715] 62 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_30s5 : Span p3_30 3 26 31 :=
  batch _ _ _ _ #[
0xc427285a17690f28550f4c9894875687262521d5a1c152e067553054b819d54c457109716b054b819d54,0x59994155e8166650557a0c99a20b9a33312a223ab1c0a728ca1769732054af0c152e067553109ca1685d,0xd01a98362cf406a60d8b3c6c09846ccf1b02611b33cd0948ad6871b02611b33c6c09846ccf1b02611b33,0xc818e82e6572063a0b995c2a2e0c5d53406a60d8b3c447507a98b0463a19995d01a98362cf406a60d8b3,0xc456a0559d3262521d5a1c9894875687312a223ab1c1ca8872ac71b02611b33d152185352f2063a0b995,0xce9110a746b1b02611b33c6c09846ccf3a44429d1ad110e82f4574443a0bd15ce9110a746b115a815674,0xd1835039d8b029ca1685dc447507a98b460d40e762c508e885e5706ac235899d110e82f457214b80e754,0xc0a7285a177206560d5a3c447507a98b2223a0c795c888e831e572660a1c58dcd18288d637460d40e762,0xc0c7507a98b2a0b819d54c99828716373444a3151dcac0c87ac472b0321eb11c42728ca177176042578a,0xc0a7285a177206560d5a39422f10e55b2a0b819d54] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_30s6 : Span p3_30 3 31 36 :=
  batch _ _ _ _ #[
0xc5aa207aa3150666429abd150c8af447406a60d8b3cc2b089aa669883c58b16d01a98362ce9883c58b16,0xc152e067553054b819d54d150c8af44732a8833a8cd01a98362cf406a60d8b3443ba1782b3406a60d8b3,0x59994155e83222560aba3c889582ae8f111aa2347554c199194af454322bd11d08a9832acf054b819d54,0xc118e8666574283a0e715d08a9832acf210d60e56354c199194af422a60cab3d08a9832acd66650557a0,0xc843583958f2063a0b995d0a0e839c572063a0b995c98b089aa67222560aba3c98b089aa6662c2a53135,0xce83108756b262c225c99d01a98362cf035a82a674c887288b1770a5c42e85ac843583958f342c234a99,0xc14358c558f176042578ac456a0559d204cdc53166d01a98362cf141ca14c5dc818e82e657406a60d8b3,0xc843583958f422a60cab3d110e82f457222560aba3c446a88d1d7222560aba3ce9110a746b422a60cab3,0xd110e82f4574443a0bd15c843583958f210d60e563] 68 (by decide +kernel)

private theorem p3_30Good : Good p3_30 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_30s0 (joinSpan p3_30s1 p3_30s2)) (joinSpan (joinSpan p3_30s3 p3_30s4) (joinSpan p3_30s5 p3_30s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_31s0 : Span p3_31 3 0 5 :=
  batch _ _ _ _ #[
0xd28298465cf4a0a611973d28298465cf4a0a611973d28298465cf4a0a611973d28298465cf4a0a611973,0xcc1aa0353d32744225c99d10ac8d6346e80a650973ca8708aa6672223a1e855c0aae0b8b532223a1e855,0xca87088ae671518a1c58dc4272850e772063a1e855c1474875687442b234ad1c2c298855cf3284a2629d,0xc45898951cf074a819574c5562075633036262c473cc53103356b2063a1e855c14748756872063a1e855,0xc199507718b212b226ad1c15708b16670463a1cc55a60791626ab2644a21c9dc1d2a0655d3074a819574,0xcca12898a77270521dca1c1d2a0655d3162a811af4ce83103a56b314a80b574cc52a02d5d3314a80b574,0xcc8aa02abd3322a80aaf4cc8aa02abd34458a1398dd18a8852bc7462a214af1d0235858d8f462a214af1,0xcc8950af18b074a819574b10c595740f074a819574c4272850e77109ca1439dcc8aa02abd3322a80aaf4,0xcc52a02d5d3314a80b574c8570895667109ca1439dc509585718f2a0b819d54cc8950af18b074a819574,0xc0a72888e77162541dc62] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_31s1 : Span p3_31 3 5 11 :=
  batch _ _ _ _ #[
0xce82a029dd33a0a80a774d1074855e874548614d4bd152185352f074c421d5ad1074855e87109ca1439d,0xd0235858d8f408d616363cd5108972672063a26655ce82a029dd33a0a80a774ce82a029dd33a0a80a774,0xc9d1089726702ab82e2d4d1162851e374a0a611973d28298465cf4a0a611973d1162851e373284a2629d,0xc84ac897347070d419d62c4571094e6b115c42539ac198a8711d7409d213ba1ca9620a9e33462a2158f1,0xd0a6284e6374a8861694bcc1aa0353d32b08622d4bcc531098d6b314c42635acc43502f58b1a9881ab8c,0xd103584758f440d611d63cc531098d6b205ca0c59dc852e078d53310d40bd62d0a6284e6374a8861694b,0xcca1283a277230560eaa3d2a2185a52f4298a1398dd2a2185a52f4a8861694bd103584758f440d611d63,0xc5072846677141ca1199dcc1aa0353d3306a80d4f4c8c1583aa8f230560eaa3cca1283a277205ca0c59d,0xc887282a6773444a0cc9dcd112833277221ca0a99dc887282a6772644a21c9dc8474875687141ca1199d,0xc6a6206ae33210d60e563cd1128332773a0c40e95a] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_31s2 : Span p3_31 3 11 16 :=
  batch _ _ _ _ #[
0xc5d0a074ad33a84226a99c1ca88953c71518a1c58dc8474875687211d21d5a1c8c6288d6373a84226a99,0xc6a6206ae331a9881ab8cc6a6206ae331a9881ab8ccac2189952d9885c58aa6c5d0a074ad32b0862654b,0xcc8aa02abd32644a0cc9dc58aa046bd3162a811af4c58aa046bd32063a1cc55c199507718b2318a1c58d,0xc9c1487728684ccca115ec84ac897347414a614373c5d0a074ad32644a0cc9dcc8aa02abd3174281d2b4,0xc152e0ccd53314c42635aca82e039d534458a1398dca82e039d513d01a63c85c508e8d19571a9881ab8c,0xc852e078d53214b81e354d0529850dcf214b81e354d2a2185a52f414a614373ce82a029dd33a0a80a774,0xc4571094e6b212b225cd1ce82a029dd3314c42635ac99128332774a8861694bc9912833277414a614373,0xc118e8d1957221ca0a99dc887282a6774458a1478dc888e87a1574458a1478dc888e87a157462a2158f1,0xcac2188b52f115c42539ad18a88563c7462a2158f1] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_31s3 : Span p3_31 3 16 22 :=
  batch _ _ _ _ #[
0xd18a8852bc7214b81e354d0529850dcf162a811af4d0529850dcf314c42635ac9c14877287414a614373,0xd103584758f440d611d63d107484ee873284a0e89dc88ae03ab53222b80ead4cc8aa02abd3462a214af1,0xd0529850dcf4a8861694bc509585718f414a614373d2a218ca52f3328426acac0a8e87a157440d611d63,0xc5072846677409d2157a1cca1283a277230560eaa3c8c1583aa8f230560eaa3d2a2185a52f4a8861694b,0xd0529850dcf414a614373c84ac89ab47314c42635ac887282a6773444a0cc9dc9912887277409d2157a1,0xcc43502f58b222b80ead4d18a8852bc7322a80aaf4d0529850dcf414a614373d0529850dcf414a614373,0xd0274855e87414a61437374a1a119ab33328426acad103584758f440d611d63d18a8852bc55644c4589e,0xc0a8e899957230560eaa3c5ca10d2b2b1728434acac88958ab18dd18a843574ccca109ab2b1425615c63,0xc428e87a15710a3a1e855c81728316773a0a80a774ce82a029dd33a0a80a774c509585718f230560eaa3,0xcc1aa0353d3230560eaa3c81958b918f1625435662cc53103356b4298a1398d] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_31s4 : Span p3_31 3 22 28 :=
  batch _ _ _ _ #[
0xd28298465cf4a0a611973c852e02f5534a0a611973c8c1583aa8f3544225c99cc1aa0353d32744225c99,0xc843583958f2063a1e855c843583958f1a9881ab8cc6a6206ae333a0a80a774ce82a029dd33a0a80a774,0xc8474875687054b819d54c588a8519d71622a14675cc53103356b314c40cd5ad29098a62cf0a5c42999a,0x531741a9e8310a5616a63c843583958f214b80bd54c852e02f5511946660cabc887282a677354422cc99,0xc852e02f553322a80aaf4c843583958f210d60e563c88ae03ab532318a1c58dcc53103356b314c40cd5a,0xcc8aa02abd3210d60e563cc8aa02abd3210d60e563c88ae03ab53314c40cd5ac2c298855cf222b80ead4,0xc857089566702a5632a63c843583958f0b0a621573d29098a62cf214b80bd54c2c298855cf214b80bd54,0xc9c148772872a0b80e754ca82e039d532a0b80e754c588a8519d71625435662a44599530ae8316662c2b,0xc588a8519d72223a26655d29098a62cf0a5c42999a] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_31s5 : Span p3_31 3 28 34 :=
  batch _ _ _ _ #[
0xca82e039d532a0b80e754ca82e039d534298a1398dc588a8519d74298a1398dd02ac8d63472063a1cc55,0xce83103a56b3a0c40e95ac118e88f157036262c473c99128332771b02621ab3c9912833277206b80dcd4,0xd28298465cf4a0a611973c118e8d1957221ca0a99dcea1089aa67221ca0a99dcc52a02d5d3314a80b574,0xcc8aa02abd34a8861694bc58aa046bd3074a819574cc52a02d5d3322a80aaf4c85708956674a0a611973,0xcc52a02d5d31162625473b322c1ce543222562ac63d107484ee873284a0e89dc88ae03ab53222b80ead4,0xd2a2185a52f3a8422e899d2a2185a52f4a8861694bc509585718f1425615c63c1d2a0655d3314a80b574,0xc887282a6773a0c40e95acc52a02d5d33a0c40e95acca1283a277230560eaa3c8c1583aa8f230560eaa3,0xc84ac89ab47055c22c599c5562075633221ca0a99dcd112833277221ca0a99dc81ae037353036262c473,0xcc8aa02abd34a426298b3c58aa046bd3155881d58cc1d2a0655d29832650b33cc8aa02abd3322a80aaf4,0xd18a8852bc7235882b58ccc52a02d5d3222b80ead4] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_31s6 : Span p3_31 3 34 35 :=
  batch _ _ _ _ #[
0xc508e873157155881d58cd103584758f235882b58cd103584758f2223a23c55c88958ab18f162541dc62,0xcc52a02d5d3230560eaa3cc52a02d5d3230560eaa3d0274855e87322542bc62c428e8d19571425615c63] 16 (by decide +kernel)

private theorem p3_31Good : Good p3_31 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_31s0 (joinSpan p3_31s1 p3_31s2)) (joinSpan (joinSpan p3_31s3 p3_31s4) (joinSpan p3_31s5 p3_31s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_32s0 : Span p3_32 3 0 6 :=
  batch _ _ _ _ #[
0xd0235858d8ea2f08ae0ccd0235858d8f1684a2629dc68710c6c699982a588b5c68710c6c6b162541ea62,0xcc8b1032e6b2b08622d4bc99a20756331a22622a73cac2188b52f310d40bd62cc43502f58b310d40bd62,0xd0568855cc7162541dc62c6c09886acf415a215731c888e88f1572a0b819d54c508e8731572a0b819d54,0xc42ae074e53162541dc62c2c6886acc70b1a21ab31c84ac872e47266881d58cc508e873157212b223b91,0xcc8b1032e6b3444a0cc9dc818e873157322c40cb9ac4272858c77109ca1631d656b01566630b0a621573,0xd116284f4374458a13d0dd0235858d8f274881e54cc54a1852e2f212b21cb91d0235858d8f109ca1631d,0xd286884ecc7074a819574cd1128332773444a0cc9dcd112833277212b21cb91c8ca188ae2f4458a13d0d,0xcd5220cd5331518a13d0dc9c14877287274881e54cd286884ecc74a1a213b31c4272858c77109ca1631d,0xc1d2a0655d31528614b8bc84ac872e471425615c63c8c6286b4372318a1ad0db014f1b185b1518a13d0d,0xc14ac872e47212b21cb91ce90a0a5ad33a428296b4c6c09886acf2a0b819d54ca82e0675531425615c63] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_32s1 : Span p3_32 3 6 12 :=
  batch _ _ _ _ #[
0xc9c1487aa874a0a611973d28298465cf4a0a611973d28298465cf4a0a611973d0235858d8f109ca1631d,0xd11a185662f428562e2a3c4272858c774458a13d0dc2c6886acc73444a0cc9dcd1128332773444a0cc9d,0xcc43502f58b408d616363d11a185662f446861598bd11a185662f446861598bc4272858c77109ca1631d,0xd0568855cc70b1a21ab31d11a185662f1425615c63c118e8ce157408d616363a44599530af310d40bd62,0xc2c6886acc7306c40d99acc1b103666b446861598bc509585718f1528614b8bd0568855cc7446861598b,0xce82a029dd33a0a80a774cc8950b998b42a8614b8bd0aa1852e2f42a8614b8bd0529850dcf414a614373,0xd286884ecc74a1a213b31d286884ecc74a1a213b31c81728394773a0a80a774ce82a029dd33a0a80a774,0xd0529850dcf440d611d63d103584758f440d611d63c88ae02ee532b08622d4bc5d0a074ad3310d40bd62,0xc2c6886acc70b1a21ab31c2c6886acc71423a1cc55c84ac88ee47074c42635ad0a62859c374298a1670d] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_32s2 : Span p3_32 3 12 18 :=
  batch _ _ _ _ #[
0xce82a029dd33a0a80a774cd112833277210d60e563cd112833277074c42635ac429585a98f074c42635a,0xc8c62879437141ca11d1dc5072847477141ca11d1dce82a029dd3210d60e563ce82a029dd30463a23c55,0xc991288727716a881578cd0d098b0acf1423a23c55c8c62879437074c42635ac887282b4772318a1e50d,0xc589507a98b3444a0cc9dcd112833277210d60e563c843583958f162541ea62c54a189562f2644a21c9d,0xc1d31098d6b174281d2b4c8c6286b43702a5632a63cd112833277222b80bb94c88ae02ee53322c40cb9a,0xd0529850dcf3a0a80a774ce82a029dd32318a1ad0dc5d0a074ad32644a0e89dcac2188b52f10a5616a63,0xc852e078d53214b81e354c852e078d53270521eaa1c9c1487aa87214b81e354c5d0a074ad3270521eaa1,0xc8c6286b437115c43531ad116284f4373a0a80a774d116284f4373a0a80a774d0529850dcf214b81e354,0xc546284f437206b80d794cc43502f58b2318a1ad0dc81ae035e531518a13d0dc9c148772872318a1ad0d] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_32s3 : Span p3_32 3 18 24 :=
  batch _ _ _ _ #[
0xc546284f437310d40bd62d286884ecc7162c421b9ad02ac8ae6474a1a213b31c9c148772874a1a213b31,0xc887282b4770b1a21ab31c0d710b8c6b1425615c63d103584758f440d611d63cc8b1032e6b1518a13d0d,0xc2c6886acc70b1a21ab31c81ae035e53206b80d794cca1283a2772223a1cc55c509585718f414a614373,0xccaa20a9e330b1a21ab31c99128872770b1a21ab31c2c6886acc7174281d2b4c199507718b2328622b8b,0xd0a62859c374a1a213b31cd1128332773444a0cc9dc54a1852e2f306542bc62c5d0a074ad33444a0cc9d,0xd286884ecc72644a0e89dc991283a277446861598bc1c3506758b446861598bd286884ecc716a881578c,0xc5072847477440d611d63d103584758f440d611d635591311627b222b80bb94c88ae02ee53310d40bd62,0xc991283a2772644a0e89dc8c1583aa8f306c40d99ac887282b477221ca0ad1dd11a185662f440d611d63,0xc11728c54772b08622d4bcc43502f58b310d40bd62cc1b103666b306c40d99ac991283a2772644a0e89d,0xc81728394774a0a611973d28298465cf4a0a611973d28298465cf4a0a611973c1c3506758b2b08622d4b] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_32s4 : Span p3_32 3 24 31 :=
  batch _ _ _ _ #[
0xcc8b1032e6b3284a0e89dc88ae02ee53162541ea62c88ae02ee5340ab22b991c99a2075633310d40bd62,0xcc8950af18b2a0b819d54c8c1583aa8f230560eaa3c8c1583aa8f0b1a21ab31cca1283a2773284a0e89d,0xd10ac8ae645d446843cacba0299425cf4445629ca3d0568855cc7415a215731c8c1583aa8f2a0b819d54,0xc843583958dd446843caccd112833277210d60e563cd1128332770463a1cc55c29710a746b210d60e563,0xca82e067553306c40d99ac887282b477435842e70ab8a7015ac63306c40d99acc1b103666b162541dc62,0xc843583958f152862558bc589507a98b222b80bb94c88ae02ee53066541dc62d29098a62cf2644a0e89d,0xcc8b1032e6b210d60e563c818e873157222b80bb94cc8b1032e6b10a3a1e855c199507718b210d60e563,0xcc1b103666b4a426298b3cc1b103666b322542e662c9c148772872318a1ad0dcc1b103666b306c40d99a,0xc428e87a157036262c473a746816acc282f286a0f4c428e87a156e68c056958cd5220cd533270521dca1,0xd116284f4374458a13d0dd116284f437212b21cb91c428e87a157052b223b91c14ac88ee4710a3a1e855] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_32s5 : Span p3_32 3 31 37 :=
  batch _ _ _ _ #[
0xd10ac8ae647442b22b991c81ae035e5342a8614b8bc9d220795332063a26655c8c6286b436e80a650973,0xc1d2a0655d3322c40cb9acca1283a2772318a1ad0dc546284f437206b80d794cc52a02d5d32063a26655,0xc546284f437314a80b574d0aa18aa62f314a80b574cc52a02d5d34a1a213b31c1d2a0655d3074a819574,0xca82e02f553440d611d63c50728474773284a0e89dcca1283a2771162625473cc8b1032e6b1518a13d0d,0xc81ae035e53206b80d794cca1283a277314a80b574cc52a02d5d31b02621ab3c887282b477314a80b574,0xc5aa2055e3302a3a34655a43ca1543d32328622b8bc199507718b11626254735591a119ab156468466ac,0xcd1128332773444a0cc9dc54a1852e2f4a0a611973cc52a02d5d3036262c473c1d2a0655d3074a819574,0xc88ae02ee53314a80b574cc52a02d5d34a1a213b31c1d2a0655d2888bc60756d286884ecc6509e286729,0xc887282b4772a0b80bd54ca82e02f5532a0b80bd54c5072847477306c40d99ac85708b9467222b80bb94,0xcc1b103666b306c40d99ac991283a2772644a0e89dc991283a2772644a0e89dc8c1583aa8f314a80b574] 80 (by decide +kernel)

private theorem p3_32Good : Good p3_32 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_32s0 (joinSpan p3_32s1 p3_32s2)) (joinSpan p3_32s3 (joinSpan p3_32s4 p3_32s5)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_33s0 : Span p3_33 3 0 5 :=
  batch _ _ _ _ #[
0xd29098465cf4a42611973d29098465cf4a42611973d29098465cf4a42611973d29098465cf4a42611973,0xcc8aa0353d346684358cac818e87a157212b226ad1c9d22077232e842650973c9d22077233222562e463,0xc1a328d0a772a5881ab8cc0a72850e771b02621573c9d220772332223a1e855d19a10d2b2b1518a1c58d,0xd0a15858d8f462a2158f1c5d0a0655d3066a811af4ccd1103356b051d21d5a1ca8708aa6672a5881ab8c,0xcc1aa02abd3306a80aaf4cc1aa02abd3462a2158f17503311627b462a2158f1cc232898a774285616363,0xc8d6207563317428195743508f31615b1742819574c0a72850e77029ca1439dcc1aa02abd3306a80aaf4,0xccd0a02d5d3334280b574c147484ee87051d213ba1c1ca8852bc72a43819d54c8d620756331742819574,0xc147484ee87051d213ba1c9832887277116262c473c8d620756331742819574c4272888e77066541dc62,0xccd0a02d5d3334280b574c147484ee87072a214af1ccca109ab2b1423a1cc55d116284e6374458a1398d,0xce91103a56b334280b574] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_33s1 : Span p3_33 3 5 11 :=
  batch _ _ _ _ #[
0xd29098465cf4a42611973c818e87a157308ca2629dd1074855e87441d2157a1ccca109ab2b2223a26655,0xc818e899957029ca1439dd116284e6374458a1398dc147484ee87072a214af1c508e8d19574a42611973,0xce90a029dd33a4280a774ce90a029dd33a4280a774d0a15858d8f4458a1478dd1162851e371744421d5a,0xd116284e6374458a1398dd027484ee873222a23475d027484ee87409d213ba1ce90a029dd33a4280a774,0xd0a6284e6374342614373cc8aa0353d31a9881ab8cc6a6206ae33330540bd62c1d2a074ad31a9881ab8c,0xd111584758f4445611d63c88728316773508a23c8dccc1502f58b2a5881ab8cd0a6284e6374342614373,0xcc23283a277210d60eaa3c1a328c62774298a1398dd0a6284e6374342614373d111584758f4445611d63,0xc818e88f1572318a1c58dcc8aa0353d3322a80d4f4c843583aa8f210d60eaa3cc23283a277221ca0c59d,0x5583311627b074a81d2b4614c69cd417074a81d2b45583311627b0463a1cc55cc52a0acad3314a82b2b4,0xc546288d637074a81d2b4c1d2a074ad30463a1cc55d19a10b332b1518a2358d] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_33s2 : Span p3_33 3 11 16 :=
  batch _ _ _ _ #[
0xcd032833277205ca0a99dc817282a677260ca21c9dd10ac8b3347045ca1199dc1172846677045ca1199d,0xc8c62871637162541dc62c1d2a074ad3230560e563cd0328332773a4440e95ac817282a677340ca0cc9d,0xcc1aa02abd3074a81d2b4cc1aa02abd3260ca0cc9dc19aa046bd3066a811af4c19aa046bd3340ca21c9d,0xc818e87a157035c42539ac9c22873237234381e354c9c22873235c215c55626c1d2a074ad3260ca0cc9d,0xc550e0ccd534458a1398dd116284e6374458a1398dc508e8d1957205ca0a99dc817282a6772063a1e855,0xd0a6284e6374342614373c19aa046bd3441d2157a1d0d09850dcf2a5881ab8cccd11098d6b4342614373,0xd111584758f4445611d63cc23283a277206b80ead4c5ca109732b206b80ead4cc1aa02abd34298a1398d,0xd0d09850dcf4298a1398dc119585718f4342614373c1ca8852bc65632285731c428e87a1574445611d63,0xcc23283a277210d60eaa3c843583aa8f210d60eaa3c81958ab18dc215c55626] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_33s3 : Span p3_33 3 16 22 :=
  batch _ _ _ _ #[
0xca90e039d533328425ccad1162851e372063a26655621ca941cd72708a1cc8dc42958ca98f4342614373,0xc847486ae874342614373ce90a029dd33a4280a774cd42288f237409d213ba1ca90e039d534342614373,0xc9832833277035c42539ac98328332774342614373c8d0e078d53234381e354d0d09850dcf234381e354,0xd0d09850dcf4342614373d0d09850dcf4342614373d0d09850dcf4342614373ce90a029dd3051d213ba1,0xd111584758f4445611d63ccc1502f58b206b80ead4cc52a0acad3462a2158f1cea220b9a33306a80aaf4,0xd18a88563c7462a2158f1ca8708aa6670465615c63cc4a888abc74342614373c1ca8852bc72a1c22a999,0xc11728466772b08626a8bc1ca8852bc7210d60eaa3c428e899957210d60eaa3cac2189aa2f3a8882e68c,0xce90a029dd33a4280a774c1ca8852bc7334442635ac817282a677340ca0cc9dc9832887277312a222af1,0xccd1103356b222562e463ccca109ab29dc42842774c887283167702a3a1e855c0a8e87a1573a4280a774,0xcc8aa0353d3210d60eaa3] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_33s4 : Span p3_33 3 22 29 :=
  batch _ _ _ _ #[
0xc8d0e02f5534a42611973d29098465cf4a42611973c843583aa8f3328426acacc8aa0353d31a9882a78c,0xc8c1583958f234380bd54c8d0e02f553274881dc8cc817282a6771a9881ab8cc818e87a1571543819d54,0xc8c1583958f206b80ead4c8c1583958f334440cd5accd1103356b2a5881ab8c58c7417568302a5616a63,0xc5d1108756b3a4280a774ce90a029dd33a4280a774c81ae03ab531b02621573c8d0e02f553306a80aaf4,0xccd1103356b334440cd5ad28298a62cf1a1c42999ac8c1583958f274881dc8cc8c1583958f454862cc8b,0xcc1aa02abd3230560e563cc1aa02abd3230560e563c81ae03ab53334440cd5ac198a8519d70662a14675,0xce91103a56b3a4440e95ac8c6288d637234380bd54c6c098855cf234380bd54c8c1583958f1b02621573,0xd29098465cf4a42611973c508e8d1957205ca0a99dcd42288f237205ca0a99dccd0a02d5d3334280b574,0xcc1aa02abd34298a1398dc19aa046bd31742819574ccd0a02d5d3306a80aaf4505c59b940f4a42611973,0xcc23283a277206b80ead4c5ca109732b206b80ead4] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_33s5 : Span p3_33 3 29 34 :=
  batch _ _ _ _ #[
0xc119585718f0465615c63c5d0a0655d3334280b574ccd0a02d5d30362625473c847486ae87206562ac63,0xcc23283a277210d60eaa3c843583aa8f210d60eaa3c1a328c6277051d213ba1d0a6284e6374298a1398d,0xca90e039d532a4380e754c198a8519d7409d213ba1a0c599530af2708a1cc8dc42958ca98f10a5632a63,0xb8a70156663211d21aba1c198a8519d72063a26655cd42288f237409d213ba1c888e87a1572a4380e754,0xc9832833277222b80dcd4ca90e039d532a4380e754ca90e039d530362625473c198a8519d710a3a33855,0xd02748a9e868872650b33cc1aa02abd3306a80aaf4c147484ee87051d213ba1c9832833277211d21aba1,0xccd0a02d5d3206b80ead47503311627b462a2158f1cc1aa02abd34a0a6298b3c19aa046bd31742819574,0xc118e873157312a222af1d111584758f072a214af1d111584758f2063a23c55c81958ab18f066541dc62,0xccd0a02d5d3210d60eaa3ccd0a02d5d3210d60eaa3cc1950af18b306542bc62d0a62851e370465615c63] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_33s6 : Span p3_33 3 34 35 :=
  batch _ _ _ _ #[
0xcd032833277205ca0a99dc45898b11cf222b80dcd4c817282a677334280b574ce91103a56b3a4440e95a,0xc1ca8852bc73328426acad1a228d1a37205ca0a99d] 12 (by decide +kernel)

private theorem p3_33Good : Good p3_33 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_33s0 (joinSpan p3_33s1 p3_33s2)) (joinSpan (joinSpan p3_33s3 p3_33s4) (joinSpan p3_33s5 p3_33s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_34s0 : Span p3_34 3 0 6 :=
  batch _ _ _ _ #[
0xd2909846ccf4a42611b33d2909846ccf4a42611b33d2909846ccf4a42611b33d2909846ccf4a42611b33,0xcc52a035ad3314a80d6b4cc52a035ad3408d62e2a3cc52a035ad32708a1cc8dc588a8711d6e842650b33,0xc686a0655d302ab81d394c686a0655d302ab82b394cd5220d5a333222a23475c686a0655d3342c225599,0xc588a8711d702ab81d394cc52a035ad32a5881ad4cd0a0e8ccc57314a80d6b4ca96206b533212b223b91,0xc0aae074e533302a0b535ca96206b533322c40cb9ac8ca189562f0465615c63c589507a98b0465615c63,0xca87088b5672a1c222d59c42ae074e5310ab81d394665191c1cab1a1c421d5ace9110c6c6b2223a1cc55,0xcc232898a77215c226559cc232898a77215c226559cc52a035ad3314a80d6b4ccc0a82d4d7152862558b,0xba109942ccf051d213d61d2909846ccf4a42611b33c9c22873237442b22c791d11a1852e2f235881e54c,0xccca108ee2b3328423b8acc8950d598b308ca2629dc85708995670465615c63c847486b5872223a26655,0xb9170153563036262c473c5ca1072e2b10ab81d394c42ae074e5302ab82b394] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_34s1 : Span p3_34 3 6 12 :=
  batch _ _ _ _ #[
0xc42ae0ace530a5a811774d190a845cd74642a11735cc232898a77162c421b9ad190a845cd7308ca2629d,0xd190a845cd7235881e54cce82a02ead33a0a80bab4ce82a02ead302ab81d394c296a045dd30a5a811774,0xa0c4f17285b441d213d61d107484f587441d213d61c8d62079533066542e662c888e8731570a5a811774,0xd11a185662f2063a1e855d11a185662f354883568cc8d62079532a80e660cabcd032833277340ca0cc9d,0xd11a185662f162541ea62a0bca1543d3162541ea62c0aae074e53446861598bc0aae074e53051d213d61,0xd107484f587446861598bd107484f58710ab81d394d11a185662f10ab82b394c0aae074e532708a1cc8d,0xcea220cea3342a8614b8bcc52a035ad3340ca0cc9dcd03283327710ab82b394cd032833277340ca0cc9d,0xc81ae035e51521cc4455ec81ae035e530463a34655d190a845cd74642a11735d190a845cd74342615333,0xd11a1852e2f4468614b8bd0274859d87046b819b94c540e867457046b819b94c818e899957115c42635a,0xc6a620c9d332303a0bd15c8c0e82f4571622a1c475c0d710d0d6b206b80bb94] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_34s2 : Span p3_34 3 12 18 :=
  batch _ _ _ _ #[
0xc84ac88ee47342c225599d0d09854ccf409d216761d0274859d874342615333d0d09854ccf050d631aa3,0xc847487958706ac214b99c1ab0852e67142b829794d1a228d1a37052b21cb91c14ac872e45d2328454f4,0xc8ca189562f051d233561c14748cd5873302a0b535d10ac8b1e474a83233b11c88ae035e53222b80d794,0xcd032833277340ca0cc9dcc18a8899d702a5616a63c0a9585a98f0662a14675c888e8731572223a1cc55,0xc119585718f142b819b94ca87088b567260ca0cc9dca87088b5672a1c222d59c81ae035e53206b80d794,0xc589507a98b3a0a80bab4c456a068dd33a0a80bab4ce82a02ead3115a81a374c5d110b8c6b1702a19535,0xc199507a98b1702a19535d10358a728f340ca21c9dccc0a82d4d7222b80bb94c589507a98b322c40cb9a,0xca87088b5672a1c222d59c81ae02ee53115a81a374c9832833277115a81a374c199507a98b115a81a374,0xd0d09854ccf051d213d61c147484f587142b829794c0d6a04cdd34342615333ccc0a82d4d7066541ea62,0xc88ae035e53222b80d794c843583728f306c40d99acc1b103666b4342615333] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_34s3 : Span p3_34 3 18 24 :=
  batch _ _ _ _ #[
0xc847486b5873508a23c8d541ce11ab53115c42635ac0d6a04cdd3035a813374c847486b587035a813374,0xc0d6a04cdd34342615333c2a708ca567210d60dca3c2a708ca567308ca0e89dcc23283a277115a81a374,0xc2a708ca5655073845cd4cc23283a277174442e31ac428e87a1572a5881ad4cc0d6a04cdd32a5881ad4c,0xd190a845cd74642a11735c58b1086e6b4642a11735d02ac8ae6474342615333cc23283a277222b80d794,0xcc23283a2772708a1cc8dcc8b1032e6b322c40cb9ace82a02ead302a3a1e855ce82a02ead34642a11735,0xc888e8731574642a11735d190a845cd5085dc50766d190a845cd74342615333d0d09854ccf4342615333,0xd0d09854ccf4342615333c9832833277441d213d61c198a8519d72223a1cc55c888e873157260ca0cc9d,0xd0d09854ccf446861598bce82a02ead33a0a80bab4d11a185662d5233846ad4d11a185662f4342615333,0xd11a185662f446861598bd11a185662f340ca21c9dcd0328872774342615333c88ae02ee518872a508f5,0xcd032833277260ca0cc9dcd032833277260ca0cc9dc9832833277340ca0cc9d] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_34s4 : Span p3_34 3 24 31 :=
  batch _ _ _ _ #[
0xc686a0655d3210d60dca3cc52a035ad11cc4a7211dcd42288f237210d60dca3cc52a035ad31503a19d15,0xc81ae02ee534a42611b33c843583728f210d60dca3c8c0e82f4572303a0bd15c81ae02ee53314a80d6b4,0xc843583aa8f210d60eaa3cc52a035ad32a5881ad4ccc52a035ad3314a80d6b4cc52a035ad3308ca0e89d,0xb906614f5133302a0b535ccc0a82d4d72a1c222d59c843583aa8f314a80d6b4c843583aa8d521cc4455e,0xc98328332773302a0b535ccc0a82d4d7340ca0cc9dc8ca189562f232862558bcc2b088ae6730ac222b99,0xc81958ab18f162541ea62ccc0a82d4d7222b80bb94c58b1086e6b222b80bb94c88ae02ee532a5881ad4c,0xc199507a98b02a3a1e855c81ae02ee533302a0b535cc23283a27710a3a1e855ccc0a82d4d7322c40cb9a,0xcc1b103666b1503a19d15cc52a035ad3260ca0cc9dcc52a035ad3206b80bb94c888e8731573302a0b535,0xcc1b103666b0a5c43195ac88ae035e53222b80d794c88ae035e53210d60dca3c9c2287323706ac214b99,0xc88ae035e53222b80d794c843583728f306c40d99a] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_34s5 : Span p3_34 3 31 37 :=
  batch _ _ _ _ #[
0xcc23283a277211d21ad61c428e87a15710a3a1e855c1a328c62771503a19d15c540e8674568316654c2b,0xc9d108b9467142b829794c9d108b9466cc19474742d2909846ccf210d60dca3d2909846ccf308ca0e89d,0xc9d108b9467274422e519cc23283a277222b80d79454c0f10ec5b210d60eaa3cc23283a277142b829794,0xcc18a8899d74642a11735c0a8e87a1573a0a80bab4ce82a02ead33a0a80bab4cc23283a277222b80d794,0xc9d108b94672223a1cc55c11ae0a5e53274422e519cc23283a2772708a1cc8dcc8b1032e6b322c40cb9a,0xc9832833277441d213d61c296a045dd32223a1cc55c296a045dd31a1c421d5ac0a8e87a1570662a14675,0xc589507a989505cc4295ec88ae02ee5282f28550f4b940595740f3a0a80bab4ce82a02ead33a0a80bab4,0xccca108ee2b052b21cb91c19b10a666b409d232761cc1b103666b409d232761c88ae02ee533544235519,0xcd032833277260ca0cc9dcd0328332772223a23c55] 68 (by decide +kernel)

private theorem p3_34Good : Good p3_34 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_34s0 (joinSpan p3_34s1 p3_34s2)) (joinSpan p3_34s3 (joinSpan p3_34s4 p3_34s5)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_35s0 : Span p3_35 3 0 6 :=
  batch _ _ _ _ #[
0xa5e882761c34285616363d11a1852e2f0a5c431b1ac199507a98b4468614b8bc1a32898a770a5c431b1a,0xc98b0895667306c40cb9accc1502f58b330540bd62ccc1502f58b435842e70ac298988a9ce961685e42c,0xd116284f4374458a13d0dd116284f4372a43819d54c14ac872e472a43819d54ca90e067553212b223b91,0xc14ac88ee470b1a21ab31c2c6886acc74543234751c2c6886acc70b1a21ab31c1a32898a77068ca2629d,0xcc1b1032e6b306c40cb9acd0328332772223a1cc55c0a72858c77270521e561c0a72858c75ac6c062b98,0xd10ac8b1e473a0a8296b4c19b1086e6b1742819574d0a15858d8f4285616363c0a72858c77029ca1631d,0xb1067155c1b0b1a213b31d10ac8b1e47068ca2629dcac0c88f547215c22e519d02358b8a8f029ca1631d,0xd116284f4374458a13d0dc9d108995672a43819d54ca90e0675530465615c63c5d0a0655d30b1a213b31,0xd0a15858d8f0b0a621ab37710a109dd32223a1cc55d0a15858d8f0b1a213b31c0d898951cf068ca2629d,0xcd032833277340ca0cc9dcd0328332772223a1cc55c9d108995674285616363d0a15858d8f02ab81d394] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_35s1 : Span p3_35 3 6 12 :=
  batch _ _ _ _ #[
0xc29710c6c6b066541ea62a73111d056b408d62e2a3d0a15858d8f4285616363c0a72858c77029ca1631d,0xc2c6886acc70465615c63c508e8ce157330540bd62ccc1502f58b4468614b8ba0c599530af4285616363,0xcc8b103666b322c40d99ac68898aa1cf0465615c63d116284f4372a43819d54d116284f437435843570a,0xd29098465cf4a42611973d29098465cf4a42611973d11a185662f029ca1631da146714ec1b1a2262a873,0xc0a72858c770b1a21ab31ca8708ab467212b21cb91cd032833277340ca0cc9dcd0328332774a42611973,0xce90a029dd33a4280a774cd0b08b16674342614373d0d09850dcf074a81d2b4c5d11098d6b2b03223d51,0xd0d09850dcf4298a1670dd0d09850dcf4298a1670dce90a029dd3221ca0e51dce90a029dd33a4280a774,0xd0d09850dcf4445611d63d111584758f4445611d63c1d2a074ad3330540bd62c81ae02ee5302a3a34655,0xc2c6886acc70b1a21ab31c2c6886acc5521cc4551ecc52a0acad3314a82b2b45487311547b052b21cb91] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_35s2 : Span p3_35 3 12 18 :=
  batch _ _ _ _ #[
0xc54a18b162f270521e561c817282b4774a5842bd0a4e0371a1a9b045ca11d1dc1172847477045ca11d1d,0xcd032833277230560e563cd032833277174442635ac0a9585a98f270521e561c118e88f157232862558b,0xc9832887277162541dc62ce90a029dd3230560e563ce90a029dd31423a23c55ce90a029dd33a4280a774,0xc81ae02ee53340ca0cc9dcd032833277230560e563c8c1583958f066541ea62d29610cec2b260ca21c9d,0xc818e87a157234381e354c42958ca98f2b03223d51cc1b1032e6b066541ea62cd032833277206b80bb94,0xc1ab0856665d072842af4c0a9585a98f222b80d794ccc1502f58b234381e354c88ae035e531705419d62,0xc1ab0856667306c40cb9ac1ab0856667330540bd62d0d09850dcf066c421b9ad28688a9cc7234381e354,0xc119585718f4342614373c817282b4774458a13d0dc45710b8c6b0465615c63d111584758f4445611d63,0xcc23283a2774458a13d0d5583a119ab3222b80d794c88ae035e53212b21cb91] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_35s3 : Span p3_35 3 18 23 :=
  batch _ _ _ _ #[
0xc1d2a074ad3260ca0e89dc818e89995702a5616a63c5d11098d6b074a81d2b4c5d11098d6b2b03223d51,0xc5d11098d6b234381e354c1d2a074ad342a861598bd0d09850dcf3a4280a774ce90a029dd3234381e354,0xd0aa185662f3a4280a774d0d09850dcf234381e354c8d0e078d53234381e354c8d0e078d5342a861598b,0xd0a62859c371705419d62d0a62859c37046b819b94cd0328c62774298a1670dc2c6886acc73a4280a774,0xccc1502f58b4468614b8bc81ae02ee53206b80bb94d11a1852e2f260ca0e89dc983283a2755073846ad4,0xc817282b477205ca0ad1dc2c6886acc74445611d63d111584758f4445611d63c11728474774445611d63,0xc843583aa8f322c40d99acc8b103666b260ca0e89dc983283a277260ca0e89dc983283a277322c40d99a,0xd1a14859d87260ca21c9dd11a185662f4298a1670dc84ac88ee474298a1670dd0a62859c374685216761,0xd11a185662f340ca0cc9dcd0328332771423a1cc55d0a62859c37340ca0cc9d] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_35s4 : Span p3_35 3 23 30 :=
  batch _ _ _ _ #[
0xd29098465cf4a42611973c5c1506758b330540bd62ccc1502f58b262c225599c50728c54770a9c232b19,0xcea108ca567206b80bb94ccc1502f58b40ab22b991c88728394774a42611973d29098465cf4a42611973,0xc843583aa8f308ca0e89dcc23283a277274882e68ccc23283a277306c40cb9ac199507a98b206b80bb94,0xc843583aa8f4458a13d0dd116284f4372a43819d54ca90e067553306542bc62c843583aa8f210d60eaa3,0xc983283a277322c40d99ac817282b477442b22b991d0d610d5c2b066541dc62cc8b103666b322c40d99a,0xc68710a746b230560e563c8ca189562f435843570ac8c62879437270521e561d28298a62cf2a43819d54,0xc81ae02ee53162541dc62c8c1583958f435843570acd032833277230560e563cd0328332771423a1cc55,0xc81ae02ee53162541dc62c0a8e87a157230560e563c8c1583958f270521e561c199507a98b206b80bb94,0xa0bca1543d32b03223d51c0d898951cf2b03223d51cc1b1032e6b230560e563cc1b1032e6b2223a1cc55,0xc0a9585a98f222b80d794ccd0a02d5d32223a26655ce9110c656b2744226559c88ae035e53142b829794] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_35s5 : Span p3_35 3 30 36 :=
  batch _ _ _ _ #[
0xccd0a02d5d31742819574c5d0a0655d31742819574c5d0a0655d3308ca0e89dcc1b1032e6a9116662c2b,0xc11728474770362625473c1ab0856667306c40cb9ac1ab0856667334280b574741ca10abd3334280b574,0xccd0a02d5d30b0a621ab3c817282b477334280b574ca90e02f553308ca0e89dcc23283a2774445611d63,0xcc8b103666b322c40d99acc23283a2774458a13d0d5583a119ab3222b80d794c88ae035e53334280b574,0xd0aa1852e2f2223a1e855cc8b103666b4a0a6298b3cc8b103666b306542e662a0c599530af2223a1e855,0xc508e88f15702a3a1e855c0a8e87a1570b1a213b31d0aa185662f4a83233951c0a8e87a1574a83233951,0xc11ae066e532b03223d51c0a8e87a15742a861598bd0aa185662f2223a1cc55c0a8e87a1571423a23c55,0xccd0a02d5d34468614b8bc81ae02ee53206b80bb94ccd0a02d5d05672881af4c5d0a0655d29883c60756,0xc983283a277334280b574c817282b4772a4380bd54ca90e02f5532a4380bd54c1172847477322c40d99a,0xc843583aa8f322c40d99acc8b103666b260ca0e89dc983283a277260ca0e89d] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_35s6 : Span p3_35 3 36 37 :=
  batch _ _ _ _ #[
0xc2c6884ecc71742819574c2c6884ecc74685216761c2c6884ecc7162541dc62ba1099425cf0362625473,0xd29098465cf340ca0cc9dcd0328332771423a1cc55ccd0a02d5d3446861598b] 14 (by decide +kernel)

private theorem p3_35Good : Good p3_35 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_35s0 (joinSpan p3_35s1 p3_35s2)) (joinSpan (joinSpan p3_35s3 p3_35s4) (joinSpan p3_35s5 p3_35s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_36s0 : Span p3_36 3 0 5 :=
  batch _ _ _ _ #[
0x6a03716159b1b02611b33d190a845cd7222562e463d190a845cd74642a11735c19aa0a5ad32063a26655,0xc818e88f157155881578cce82a02d5d33a0a80b574ce82a02d5d31b02611b33d0235858d8f1b02611b33,0xc6c09846ccf1b02611b3334689a161cf346882bc8cc2a2e078d530a8b81e354cac0c87ac470463a1cc55,0xd1074855e87029ca1439dc1ca8872ac72b0321eb11c588a8711d7266881dc8cc6c09846ccf1b02611b33,0xc147484ee87051d213ba1d0a0e8ccc574548614d4bd152185352f4548614d4bc6c6108ee2b2a5882b58c,0xc11958d518f4742215731c58aa066ad3074a811774c847486ae872223a26655c847486ae872223a26655,0xcc52a029dd3314a80a774cc52a029dd3441d213ba1d0235858d8f4742215731d29098a54cf1a1c421b9a,0xc1d2a045dd3074a811774c2a2e078d53074a811774c888e873157074a811774cc52a029dd3314a80a774,0xcc52a029dd3314a80a774c147484ee872a0b819d54c8ca189aa2f1423a1cc55c2a2e078d530a8b81e354,0xcc52a029dd3314a80a774] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_36s1 : Span p3_36 3 5 11 :=
  batch _ _ _ _ #[
0xc4272888e77109ca2239dc4272888e75d18c44695ac198a8519d70463a34655c1474875687029ca1439d,0xc0a72850e77155881578cc119585718f0463a1cc55c5562055e33074a811774c147487568697320654f0,0xb832a14c5d32063a23c55c99a2077233314a80a774cc52a029dd3314a80a774cc52a029dd3066541dc62,0xd152185352f211d21aba1c147484ee874458a1398dd1074855e87460d431762d1074855e87211d21aba1,0xc58aa066ad3074a811774c1c3506758b155881578cd1074855e874548614d4ba133315057b1622a14675,0xcc43502f58b310d40bd62cc43502f58b314a80a774cc52a029dd3314a80a774d116284e6374458a1398d,0xc1d2a045dd3074a811774cac0c87ac47074a811774c847486ae870a8b81e354c5562055e33155881578c,0xcc52a029dd3314a80a774cc52a029dd3314a80a774cc52a029dd31b02611b33d116284e6374458a1398d,0xd027484ee870665435662d116284e637051d213ba1cac0c87ac474742215731c508e873157314a80a774,0xcec2108f52b306a80d6b4cc43502f58b4642a11735c6a6204ee334642a11735c5072885677214b81e354] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_36s2 : Span p3_36 3 11 17 :=
  batch _ _ _ _ #[
0xc588a8711d7312a223ab152e2c1ce5430463a1cc55d0a62851e37066541dc62c1ca8872ac74298a1478d,0xc540e867457214b81e354c143584758f115c42539ace82a02d5d3072a21cab1ce82a02d5d3314c42635a,0xc152e0ccd53210d60ad635591311547b115c42539ac152e0ccd53115c42539ac508e8d1957115c42539a,0xcc8aa02ead3210d60ad63d0a62851e374298a1478dd0a62851e374298a1478d5591311547b210d60ad63,0xc508e873157409d2157a15417a10d6b32328626a8bd103584758f162541dc62d02748a9e87210d60ad63,0xc6a6204ee33211d21d5a1c8ca189aa2f2a0b80bd54c6c6108ee2b2a0b80bd54c198a8711d55303c43b16,0xcac2189952f2a0b80e754ca82e039d533302a0b535ccc0a82d4d71702a19535c8474875687211d21d5a1,0xc6a6204ee330662a14675c8c628716372318a1c58dc99a2077233210d60e563cac2189952f2b0862654b,0xcc1aa035ad31518a2358d5a03594358f4a83233b11c98b08972673062a22675c0a9585a98f2b0862654b] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_36s3 : Span p3_36 3 17 22 :=
  batch _ _ _ _ #[
0xc14748756873302a0b535c14748756870465615c63c119585718f066541dc62cc531098d6b211d22b5a1,0xc11728466771a98813b8cc42958ca98dd306443d2ac843583958f0463a1cc55c818e88f1571518a1c58d,0xc852e078d53214b81e354ca82e039d531a98813b8cc42958ca98d1735055ce0d116284e637214b81e354,0xc588a8519d70465615c63d2a2185a52f051d213ba1d0a6284e637211d21aba1c428e87a157211d21aba1,0xc143584758f3062a22675c119585718f4a8861694bc147484ee872a0b80e754ca82e039d534a8861694b,0xd107484ee87214b81e354d190a845cd7434262a333d190a845cd73062a22675cec2108f52b050d611d63,0xc509585718f440d611d63c847486ae8702a3a1e855c198a8519d7306542e662cc43502f58b42a862e88b,0xd2a2185a52f1425615c63ca82e02f5534a8861694b5417a109eb34642a11735d190a845cd72b0321eb11,0xcc1aa035ad34a8861694b] 66 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_36s4 : Span p3_36 3 22 27 :=
  batch _ _ _ _ #[
0xc1c3506758b162a819ab4c58aa066ad3070d419d62cec2108f52b1503a19d15c540e867457174443531a,0x748ca10abd32b0322bd11c1d310d0d6b310d40bd62c817282a6772b0322bd11c817282a677322a80bab4,0xd11a18d622f1425615c63c888e88f1571425615c63c1172846675dc0c444d5ad103584758ddc0c444d5a,0xd11a18d622f1423a1cc55c817282a67502ee85e0acc817282a677205ca0a99dc54a18d2a2d5303c43b16,0xc6c6108ee2b3a0a80b574ce82a02d5d33a0a80b574ce82a02d5d33a0a80b574ce82a02d5d33a0a80b574,0xcc1aa035ad31b02611b33584a599aa0f1b02611b33c6c09846cce30b1a8e8c5c8872831677221ca0c59d,0xc852e02f5534548614d4bd152185352f32a882e68cd11a18d622f3a0a80b574ce82a02d5d33a0a80b574,0xd10748ad687070d419d62c152e0c5d53310d40bd62c1ca8872ac71b02611b33d152185352f1b02611b33,0xd116284e6374742215731cc43502f58b441d22b5a1c852e039d532303a0bd15] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_36s5 : Span p3_36 3 27 33 :=
  batch _ _ _ _ #[
0xc8872831677221ca0c59dcd1a20af233312a223ab1c1ca8872ac74742215731c99a2077233266881dc8c,0xc428e87a157211d21aba1c6c09846ccf1b02611b33c852e039d53066541dc62c852e039d53221ca0c59d,0xc147484ee874298a1398d7423310a57b10a3a1e855d18350c5d8b2a5882b58cca9620ad6331625435662,0xc843582b58f310d40bd62cc43502f58b314a80a7744747416ae83051d213ba1cc8950b998b051d213ba1,0xcc52a029dd3314a80a774d107484ee87322a80bab4c8c0e82f4570465635463c843582b58f4a8861694b,0xc589507718b4a8861694bc1d2a045dd3074a811774cc8950af18b440d611d63d103584758f162541dc62,0xc6a6204ee334a83233b11c888e8999572223a26655c147484ee87051d213ba1d1d210d1d2b314a80a774,0xccc0a82d4d70a5c42999ac843583958f2223a26655c888e899957205ca0a99dc817282a67702a5616a63,0xc1474875687054b819d54c8c62871637054b819d54d0aa18ba22f054b819d54c0a9585a98f3302a0b535,0x465199434af42a862e88bc6871086e6b210d60e563c0a8e87a157210d60e563c843583958f210d60e563] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_36s6 : Span p3_36 3 33 36 :=
  batch _ _ _ _ #[
0xc843583958f3302a0b535c852e02f5531518a1c58dc843583958f205ca0a99dc152e067553409d22a7a1,0xca82e067553314a80a774c817282a677322542bc62a21791626ab3302a0b535c589507718b314a80a774,0xc14748756872318a1c58dc84748ad687266881dc8ccc52a029dd3314a80a774d1d210d1d2b02a5616a63,0xc199507718b10a3a1e855c843583958f066541dc62c1d2a045dd31702a19535] 30 (by decide +kernel)

private theorem p3_36Good : Good p3_36 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_36s0 (joinSpan p3_36s1 p3_36s2)) (joinSpan (joinSpan p3_36s3 p3_36s4) (joinSpan p3_36s5 p3_36s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_37s0 : Span p3_37 3 0 5 :=
  batch _ _ _ _ #[
0xd1162851e374458a1478dd190a845cd73328426acad190a845cd74642a11735a531315447b2063a26655,0xa33311d056b3328426acaca9620a9e33408d616363c818e89995702ab82e2d4d1162851e37408d616363,0xd116284e6374458a1398dccca109ab2a885e4589aad0235858d8f408d616363c818e87a157212b226ad1,0xd152185352f4548614d4bc818e87a1574283a33315c29898aa1cf4548614d4bc29898aa1cf4458a1398d,0xcc8950b998b3328426acad1074855e87029ca1439dd116284e637222562e463d0235858d8f2063a1e855,0xce82a029dd33a0a80a774ce82a029dd3441d2157a1d1074855e874548614d4bd152185352f4548614d4b,0x7463111a56b051d21d5a1cc18a8899d73062a22675c58aa046bd3029ca1439dce82a029dd33a0a80a774,0xc58aa046bd32063a1e855c58aa046bd31702a19535c0a72850e772a1c222b99c688988a9cf0662a14675,0xccc0a82d4d73302a0b535ccc0a82d4d69614c54a1ea9c0717541b1518a1c58dd19a10d632b408d632363] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_37s1 : Span p3_37 3 5 10 :=
  batch _ _ _ _ #[
0xc1ca8852bc73222a22675cac0c87ac473222a22675cac0c87ac473222a22675d1074855e87211d21aba1,0xd190a845cd7162a811af4c45898951cf051d213ba1c0d898b11cf1622a14675c4272888e77072a214af1,0xcc8aa02abd3322a80aaf4c19950d598b462a214af1d1162851e35d18c44695ad18a8852bc73062a22675,0xc6c09846ccf1b02611b33d190a845cd72b0321eb11d190a845cd74642a11735c509585718f1425615c63,0xc1d2a0655d3162a811af4c147484ee87314a80b574cc52a02d5d3036262c473c0d898b11cf1b02611b33,0xcc8aa02abd29614c54a1ec2a2e078d525782285731d116284e6374458a1398dc55620756328599855784,0xcac0c87ac47155881d58cc847486ae87074a819574c509585718f1425615c63cc8aa02abd3322a80aaf4,0xc2a2e078d53211d21aba1c2a2e078d531b02611b33d116284e6374458a1398dc147484ee87051d213ba1,0xd116284e637051d213ba1cc52a02d5d3314a80b574cc52a02d5d3211d21aba1c509585718f211d21aba1] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_37s2 : Span p3_37 3 10 16 :=
  batch _ _ _ _ #[
0xd027484ee874642a11735c118e8d19574642a11735c5072885677214b81e354c5072885677212b225cd1,0xc199507718b409d2157a1cac2188b52f115c42539acac2188b52f221ca0c59dc118e8d1957115c42539a,0x6660a941cd7409d213ba1c84ac89ab473222a23475cc1950af18b052b234ad1c84ac89ab47409d2157a1,0xcc43502f58b4458a1398dd116284e637310d40bd62d116284e6374458a1398dd116284e637214b81e354,0xc852e078d534a8861694bd2a2185a52f214b81e354c199507718b4a8861694bd116284e637214b81e354,0xc143584758f035c42c39ac199507718b214b81e354d2a218ca52f4a8861694bc81ae0373534a8861694b,0xc8c0e82f457035c42c39ac843582b58f210d60ad63c4571094e6b115c42539ac540e867457214b81e354,0xd0a62851e374298a1478dc4571094e6b3a0a80a774ce82a029dd3314c42635acc531098d6b2303a0bd15,0xc88ae03ab53310d40bd62c843582b58f1728425ccad0a62851e374298a1478dd0a62851e374298a1478d,0xca87088ae672303a0bd15] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_37s3 : Span p3_37 3 16 22 :=
  batch _ _ _ _ #[
0xc1ca8852bc5505e8435acc888e88f157312a222af1c508e8731574298a1478dc1ca8852bc7440d611d63,0xc843582b58f214b81e354c688988a9cf4298a1398dd0a6284e637050d611d63c540e8674574298a1398d,0xd103584758f440d611d63d107484ee87214b81e354c8c0e82f457222b80ead4d107484ee87441d213ba1,0xc1ca8852bc74a8861694bd0a6284e6374298a1398dc147484ee87334442e31ad0a6284e637162541dc62,0xc847487568710a5616a63c84748756872b0862654bc8c628716372318a1c58dcc1aa0353d3051d213ba1,0xc843583958f206b80dcd4cac2189952f2b0862654bca82e039d532a0b80e754ca82e039d532a0b80e754,0xc8474875687211d21d5a1ccd110b8c6b0662a14675c198a8519d72318a1c58dce82a029dd3210d60e563,0xc198a8519d5e80d458d62c198a8519d70662a14675d0d098a8ccf2b0862654bcc18a8899d702a5616a63,0xccc0a82d4d7409d22a7a1c58aa046bd30465615c63c58aa046bd3066541dc62cc531098d6b066541dc62,0xc843583958f3302a0b535c119585718f322a80aaf4] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_37s4 : Span p3_37 3 22 28 :=
  batch _ _ _ _ #[
0xd0d098a8ccf3302a0b535ccd110b8c6b02a5616a63c5c0a8654d70a6262a873c117284667746684358ca,0xc199507718b211d22b5a1c14358c558f066541dc62ccd110b8c6b02a5616a63c29898aa1cdd284c42b1e,0xc843583958f0465615c63c199507718b3302a0b535c14748756870465615c63c119585718f162a811af4,0xc152e0675530a9c22a999c152e0675530a9c22a999c152e067553141ca2159dc199507718b10a3a1e855,0xc5ca10d2b2b306542e662615c61af213221ca0c59dc88728316774642a11735c852e02f553214b80bd54,0xcc88a88d1d73222a23475c852e02f553409d2157a1c152e067553212b226ad1c84ac89ab470a6262a873,0xce82a029dd33a0a80a774ce82a029dd33a0a80a774c5ca10d2b2b4548614d4bd152185352e885e4589aa,0xd1074855e855644c4551ec428e87a157322542e662c147484ee874298a1398dd18350c5d8b3a0a80a774,0xc888e899957205ca0a99dc817282a67702a5616a63cc4a88953c73a0a80a774ce82a029dd33a0a80a774,0xc818e87a157454322bd11c843583958d530664652bc29710a666b2223a26655] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_37s5 : Span p3_37 3 28 35 :=
  batch _ _ _ _ #[
0xc88ae03ab53222b80ead4c843583958f214b80bd54c852e02f553054b819d54c8c628716371a22622a73,0xc843583958f214b80bd54ccc0a82d4d72a1c222b99cc8aa02abd3322a80aaf4c843583958d505e8427ac,0xca82e039d53045ca1199dc42958ca98e9c9c054b98c843583958f322a80aaf4c817282a677442b234ad1,0xd116284e6371625435662d116284e6373222a2267595078a11ea72223a26655c817282a6772a0b80e754,0xca82e039d534a8861694bc1ca8852bc74a8861694bc847486ae874298a1398dc818e87a1572063a1e855,0xd2a2185a52f0665435662c1ca8852bc7051d213ba1c81ae037353206b80dcd4ca82e039d532a0b80e754,0xd02ac8ba345505e8427acd107484ee87210d60ad63d190a845cd710a3a33855c843582b58f322a80aaf4,0xd103584758f314a80b574d103584758f440d611d63c847486ae874443a31715cc8aa02abd3462a214af1,0xc6c09846ccf1b02611b33c6c09846ccf051d213ba1d190a845cd69113c63a16d190a845cd71425615c63,0xd18a8852bc7322a80aaf4c817282a6770a8b831754d2a0c8b9c47205ca0a99dcc8aa02abd3409d22a7a1] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_37s6 : Span p3_37 3 35 36 :=
  batch _ _ _ _ #[
0xa21c99a22cf205ca0a99dc817282a677440d611d63c1172846677314a80b574d103584758f2223a23c55,0xc817282a6771b02611b33d0274855e871423a1cc55] 12 (by decide +kernel)

private theorem p3_37Good : Good p3_37 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_37s0 (joinSpan p3_37s1 p3_37s2)) (joinSpan (joinSpan p3_37s3 p3_37s4) (joinSpan p3_37s5 p3_37s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_38s0 : Span p3_38 3 0 6 :=
  batch _ _ _ _ #[
0xc6a8188754dc54e0744e8c99a2066e53056321c571c99a2066e53310d42e2e2c99a2066e53310d42e2e2,0xcd422898b571a83813a74c54a1894e4f116262654bc158c8715c71684a14c5dc8ca18b0e4f232862c393,0xd08a985662f2a60621d53c550e0ad1d3422a61598bcd422898b573508a262d5d08a985662f1a83813a74,0xd0a1585718f4285615c63c8d0e0751d3056321c571c858c8715c7460d431ae2d0a158ca98f116262654b,0xa62c19a344ea3a3062770c54a18b0e4f4443a13875c5a128531770a63419972c5a12853177152862c393,0xc8d0e0751d3405aa3388dd01a985662f1a83813a74c858c8715c72328625393c6a0e04e9d31a83813a74,0xc858c8715c70665419d62cc1b103666b306c40d99ac686a0af2330a63419972d110e84e1d7460aa14ccd,0xc458989952f422a614b8bc8ca18b0e4f234381d474c8d0e0751d3422a614b8bd08a9852e2f310d42e2e2,0xd111585a98f4445616a63c99a2066e533508a262d5d01a9852e2f2668819b94b828595a50ea870668d13,0xa21cd162ccb306c40cb9acc1b1032e6b460aa14ccd60d5a1790b3036262654bd111585a98f3508a262d5] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_38s1 : Span p3_38 3 6 12 :=
  batch _ _ _ _ #[
0xcca1288b1773284a22c5dc99a2066e528873458b32c99a2066e53310d42e2e2c550e0559d31543815674,0xca88c86a5c70665419d62cd1a202ee53346880bb94cd1a202ee531684a14c5dc1c350d4b8b3a88829cd4,0xa585315607b306540bd62cc19502f58b306540bd62741d111746b152862c393d08a985662f2a2321a971,0xd0a1585718f4285615c63cc4350b8b8b460d431ae2c29898ca52f1543815674cc8b103666b322c40d99a,0xd110e84e1d71684a14c5dd110e84e1d70a6263294bd016a8ce2373a88829cd4c298d0665cb0a63419972,0xd182a8533373508a262d5d01a985662f3a0a82accccd422898b572328625393cd422898b572328625393,0xc58b1086e6b0665419d62cc1b103666b035a82e68cd182a8533372328625393d0a1585a98f460aa14ccd,0xcc8b1032e6b306540bd62cc19502f58b306540bd62d111585718f3508a262d5d08a9852e2f1543815674,0xd111585a98f4445616a63c99a2066e530aa321a971d01a9852e2f1543815674c298988b52f322c40cb9a,0xcd1a202ee53346880bb94d182a8533374445616a63c8ca18b0e4f460aa14ccdd01a9852e2f406a614b8b] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_38s2 : Span p3_38 3 12 17 :=
  batch _ _ _ _ #[
0xd08a985662f422a61598bd0a1585a98f4285616a63d0a1585a98f4285616a63c8474877287036341c372,0xc68898ca52f2644a3445dc99128d117742a860cb93ca88c86a5c72a2321a971d0aa1832e4f42a860cb93,0xd08a9852e2f422a614b8b88bc2978457162c421b9ac1474877287051d21dca1c58b1086e6b3444a2645d,0xd0aa183664f0aa321a971c2a8c86a5c70aa321a971c458d08cdcb42a860d993d0aa183664f3444a2645d,0x990a595660f446860cb93d11a1832e4e668d055ce099a341573833aa0223d51c99a2066e53036341c372,0xc6a0e04e9d31a83813a74cd1a202ee53036341c372d1a228333572a2321a971ca88c86a5c74688a0ccd5,0xc0d8d070dcb2a2321a971cc19502f58b42a860cb93c44a989562f150562e463cc42a8993370a5a82bc8c,0x8a86718ea1b3284a22c5d990a5952e0f032a62558bcea8088f5472360626353c540e88d1d742a860cb93,0xd1a228333572360626353d016a8ce2370a6263294bd016a8ce2374688a0ccd5d1a228333560393a62635] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_38s3 : Span p3_38 3 17 22 :=
  batch _ _ _ _ #[
0xcd5220b8b53306c40d99acc1b103666b460d40dce2c686a0af2331a83813a74c6a0e04e9d31a83813a74,0xc8c0e8711d70665419d62cc1b103666b460d40dce2c8d81898d4f032a62558bd016a8ce237354882e2d4,0xc2a8c86a5c742a860d993c8c0e8711d7306540bd6268e941c9d825470645d13c44a98b162f1560626353,0xd183503738b306c40cb9acc1b1032e6b2668819b94c0d8d070dcb2668819b94d0aa183664f0aa321a971,0xc2a8c86a5c7346880bb94cd1a202ee532a4381aa74d183503738b354882e2d4c44a989562f460d40dce2,0xcc1b103666b3508a0ccd5a704e2a58d284f42ae119c19b10a666b1625431762d01a985662f066c42999a,0x7518310e55b4443a13875ca88c889dc5d460c43956cc1b103666b306c40d99ac58aa055e33322540e762,0x9826697a217310d40dce2cc43503738b306c40cb9ac99a2066e532668819b94d111585a98f406a614b8b,0x6295318a87b346880bb94c58aa055e33346880bb94c58aa055e33162a81578ccd1a202ee53346880bb94] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_38s4 : Span p3_38 3 22 27 :=
  batch _ _ _ _ #[
0x9884e96a0d66213a5a835cc43503738b3508a0ccd58f0a51ae60b4283a14675d0a0e8519d74283a14675,0xc541585718f1163423372d11a1832e4f446860cb93cd4228333573508a0ccd5c84748af2874283a14675,0x998a5172e0b3508a0ccd5cd4228333562a19c63a86c55818d0d4f051d21dca18f0a518ee0b2708a21cd5,0xd11a183664f446860d993c8d81898d4f0aa3222771cd5220b8b5332a880d794c84748af2873508a0ccd5,0xca88c86a5c604ee29c1a9ca88c86a5c72a2321a971c58b10a666a04ee29c1a9d0aa1832e4f42a860cb93,0xcc8b103666b322c40d99acc43503738b051d22bca1cc8b103666b3508a0ccd5998a517660a662945d982,0xb828595a50f0aa321a97194a19a1a1af162c421b9ac2a8c86a5c70aa321a971d0aa183664f42a860d993,0xc6a818c654f322c40cb9acc8b1032e6a5688c458d6c99128d1177111aa23c8dc84748af287322c40cb9a,0xc6a8188754f446860cb93d11a1832e4f1aa0621d53c6a8188754f446860cb93c99a2066e531a2263294b,0xd1a22833357346880bb94d1a228333571684a14c5dd11a1832e4f4688a0ccd5] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_38s5 : Span p3_38 3 27 32 :=
  batch _ _ _ _ #[
0xcc19502f58b306540bd62c44a989562f2a60621d53cc42a8993374285632a63c199506758b42a860cb93,0xc456a0b9a33032a62558bcc42a899337446860d993cc8b103666b42a860cb93ca98188754f2a60621d53,0xd1a22833357230562e463c8c158b918f4688a0ccd5d1a22833357115a82e68cc298d0665cb0a63419972,0xcc1b103666b460d40dce2c298d0665cae421654d43cd580899d473a0a82acccc5a12853177230562e463,0xca9818c654f460d40dce2c0d6a0b9a33405aa3388dd183503738b115a83568cc298d0665cb306c40d99a,0xcd580899d47306540bd62c9d808d1d47115a82e68ccd580899d47234382a674c199506758b42a860d993,0xcc1b1032e6b2668819b94c2a8c86a5c70aa321a971d0aa183664f032a62558bcc8b1032e6b306540bd62,0xd183503738b1543815674941cd10eccb1aa0631953c44a989562f460d40dce2d183503738b306c40cb9a,0xc9d808d1d47346880bb94] 66 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_38s6 : Span p3_38 3 32 36 :=
  batch _ _ _ _ #[
0xc8474877285e054a5681dc858c8715c7216321c571c6a0e04e9d31a83813a74c6a0e04e9d31a83813a74,0xc158c88d5c74443a138757518310e55b0563223571cc1b103666b306c40d99ac58aa055e33322540e762,0xcc8aa0a9e33211d21dca1c8474877287216321c571c541585718f1505615c63c296a0cea331505615c63,0xc158c88d5c7346880bb94c58aa055e33346880bb94c58aa055e33162a81578ccd1a202ee53346880bb94,0xc1474877287051d21dca1782a6155e13446860cb93d11a1832e4f1505615c63c296a0cea332708a21cd5,0xc541585718f111aa23c8dd11a1832e4f446860cb93cd4228333573508a0ccd5c84748af2874283a14675,0xd11a183664f0a63419972c298d0665cb0a63419972cc52a0b9333446860d993a44599530af2708a21cd5,0xd11a183664f446860d993c858c88d5c7036262654bc858c88d5c732a880d794c84748af2873508a0ccd5] 64 (by decide +kernel)

private theorem p3_38Good : Good p3_38 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_38s0 (joinSpan p3_38s1 p3_38s2)) (joinSpan (joinSpan p3_38s3 p3_38s4) (joinSpan p3_38s5 p3_38s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_39s0 : Span p3_39 3 0 6 :=
  batch _ _ _ _ #[
0xc447507a98b1423a232b5c447507a98b3342813d4cccd0a04f533035c425c5aca90e0655d3045ca2645d,0xc447507a98b1423a232b5c55620af153306a82e4ccd111583958f444560e563d111583958f444560e563,0xc6a6207a9531423a1c2b5c1d2a075633111d42bc62cd41484f587074a81d58ccd510899566346e0568e8,0xc447507a98b2b08621b938d634155e832b08621b93c50ae054bd3142b8152f4cd032850e77074a81d58c,0xa0bd11d446b260ca2239dc0c750ce98b1423a1c2b5d0a1582b58f428560ad63d0a1582b58f428560ad63,0xca96207a9530a5c426a5acd41484f587109ca1685dcc1aa05ab334a88629993cd5108995672223a1c2b5,0xc50ae054bd33528226ad188b1716859b222b82a2f4d01ad032bcb406b40caf2c297109a96b406b40caf2,0xc6a0e045dd32b08621b93cd032850e772b08621b93c427285a1770b0a622b8bc198a8d1a373528226ad1,0xd1a22831e574688a0c795ccd0a04f5333342813d4ccd4a089ab474688a0c795c6a0e045dd31a83811774] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_39s1 : Span p3_39 3 6 12 :=
  batch _ _ _ _ #[
0xcc4350ace8aa621c5d88609e869d1a17070d41d3a2ccd0a04f5332a438195740b332988677066a8354cc,0xca96207a953070d41d3a2ca96207a953070d41d3a2c81728991773508a23395a988717621b2708a1c395,0xc1c35074e8b3a0c42999acc1aa05ab33070d41d3a23a215a2358f070d41d3a2c9c22870e568873458b32,0xcc8aa05733310ab811af4c818e8662d710ab811af4cc4350ace8b2708a1c395cc4350ace8b405d433a62,0xc118e82e2d70463a0b8b5c6a6207a95302ab80aaf4c0aae02abd302ab80aaf4c1c35074e8b1505616363,0xc58aa057333405d433a62cc232846677308ca1199dc58aa057333162a815ccccc2328466772708a1c395,0xd01ad0a63cb10ab811af4c1a3282a677068ca0a99dcd42288ce573508a23395c9c22870e57070d41d3a2,0xc118e82e2d726252356a1ccd0a04f533235881dc54c5415858d8f3544214d59cd51085356454666468ab,0xc0a8e82e2d702a3a0b8b5c0a8e82e2d7109ca1685dcc1aa05ab334a88629993cc2328466771505616363,0xc427285a177109ca1685d] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_39s2 : Span p3_39 3 12 17 :=
  batch _ _ _ _ #[
0xc5415858d8ee2a305cab0cc18a899a373544214d59c9c22870e5710ab811af4c1c35074e8b10ab811af4,0xcd5108535673544214d59d28298aa62f1505616363d28298aa62f46a8234ad1c55620af1533508a23395,0xccd0a04f5333342813d4cd28298aa62f235882bc54c0a8e831ad71a83811774c6a0e045dd3306a816acc,0xc54628731573505213d61cd41484f5873505213d61c9d22074e53454862c393ccd0a04f53330a522e6a1,0xd08ad0363c8688d650ba3d28298aa62c688d650ba3d08ad0363cb422b40d8f2d111583958f422b40d8f2,0xc68710ba16b30a522bca1c0cad032bcb032b40caf2c44ad086bcb06a521dca1c42958a728f06a521dca1,0xc0a9583728f032b40caf2c11ae0353d3274881d394d08ad0363cb422b40d8f2c0a9583728f02a560dca3,0xc1a3282a677068ca0a99d05c5716a89b068ca0a99dcc232846677308ca1199dcc232846677308ca1199d,0xc0a8e82e2d662ab0558f0c0cad032bcb032b40caf2cd5220ace53068ca0a99dcc88a88f237314c42c39a] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_39s3 : Span p3_39 3 17 23 :=
  batch _ _ _ _ #[
0xd15218b0e4f460d40d7a2c550e04cdd30463a0b8b5d1835035e8b406b4298f2c42ae046bd31518a1cc55,0xd0a1582b58f0463a0b8b5c818e8662d72063a198b5c818e8662d7029ca22c5dc550e04cdd3460d40d7a2,0xce82a0a9e333a84222d59c550e04cdd31543813374c118e82e2d70463a0b8b5c4272853177109ca14c5d,0xd01ad032bcb3505213d61c8c62873157270521ad61cc232846677308ca1199dc118e82e2d74a4263294b,0xce90a059d333a4281674cc550e04cdd3109ca1685dc0a8e82e2d7406b40caf2d01ad032bcb068ca0a99d,0xd08ad0363cb2728225cd1c118e831ad702ab80aaf4c6c0988b52f10ab811af4c42ae046bd310ab811af4,0xd0a1582b58f0463a0c6b5ca9620b99532063a216b5ce90a059d333a4281674ccd41484f5871543813374,0xc0cad032bcb032b40caf2d08ad0363cb0463a0c6b5cc2948af287032b40caf2d0a1582b58f3a4281674c,0xcc2328466770b0a622b8bcc232846677162a815ccc898c696b417308ca1199dc0a9583728f02a560dca3,0xcc8aa057333032b40caf2c1a3282a676c21668cc2bce90a059d333a4281674c] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_39s4 : Span p3_39 3 23 28 :=
  batch _ _ _ _ #[
0xc88728ca17706a52356a1d15218b0e4f2728225cd1cd4a08973463429c558c6c428e885ad710a3a216b5,0xc887288b177074c42539acc1aa05ab33306a816accd28298aa62f141ca1685dc19aa0cab3302a3a0c6b5,0xc5072853177141ca14c5dd1a22831e57221ca22c5dc1d31094e6b322a815cccd29098ca52f141ca14c5d,0xc1a3282a677444560e563d1835035e8b460d40d7a2d29098ca52f162a815cccd29098ca52f314c42c39a,0xccd0a04f533460d40d7a2c0a8e82e2d7174281ad4cc1a3282a677444560e563d111583958f068ca0a99d,0xd08ad0363cb174281ad4c15a3a109eb302a3a0c6b5d1a22831e57444560e563d08750d598b460d40d7a2,0xc5462873157460d40d7a2c11ae0353d33342813d4cd1a22831e56674145cd42d111583958f02a3a0c6b5,0xc54628731571518a1cc55cd0948b9a8702ab80aaf4d1835035e8b10ab811af4c42ae046bd3460d40d7a2,0xc9d108d1567460d40d7a2c98948d5a87460d40d7a2] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_39s5 : Span p3_39 3 28 34 :=
  batch _ _ _ _ #[
0xa54cc14ecc310a5629ca3c0c750ce98b460d40d7a2b884e1558d3428560ad63d0a1582b58f428560ad63,0xc118e82e2d72b08621b93cac21886e4e1615c55626c0a9583728f111d41ea629710d10e5cb111d41ea62,0xc1a3282a6772744234559d01ad032bcb460d40d7a2c297109a96b10a3a198b5ca96207a95310a3a198b5,0xc68710ba16b074a81d58cc427285a177109ca1685dc0a8e82e2d7406b40caf2d01ad032bc814e5c5d0a6,0xd08ad0363cb2728225cd1d08ad0363cb074a81d58cd08ad0363cb3505213d61d08ad0363cb422b40d8f2,0xce90a059d332a5882e654d08ad0363cb10a5629ca3d0a1582b58f428560ad63cd41484f5873062a2668d,0xc0cad032bcb032b40caf2c118e831ad7032b40caf2ce8310a666b0463a0c6b5d08ad0363cb422b40d8f2,0xc1a3282a677262521dca1cd0948af287308ca1199dc58aa0ab333112b421af2c0a9583728f02a560dca3,0xc428e885ad706a52356a1c19aa0cab334688a0c795d1a22831e571518a1cc55cc8aa057333032b40caf2,0xcc1aa05ab33306a816accc6a0e045dd31a83811774c0a8e831ad74688a0c795c54628731574688a0c795] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_39s6 : Span p3_39 3 34 35 :=
  batch _ _ _ _ #[
0xcac21886e4f3544226559d1a22831e574688a0c795c6a620b9952961685ac2cd1a22831e57074a81d58c,0xcac21886e4f1a83811774c6a0e045dd33544226559] 12 (by decide +kernel)

private theorem p3_39Good : Good p3_39 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_39s0 (joinSpan p3_39s1 p3_39s2)) (joinSpan (joinSpan p3_39s3 p3_39s4) (joinSpan p3_39s5 p3_39s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_40s0 : Span p3_40 3 0 6 :=
  batch _ _ _ _ #[
0xcd41484ee873505213ba1cd41484ee87115c425c5ad2a218c654f235882bc54cc52a04f533314a813d4c,0xcea108aa667031d41ea62c81728d11772a0b81a374ca82e068dd33528226ad1d111583568f2a0b81a374,0xd0a1582ae8f428560aba3c447507718a518b4447728d634159d832b08621d53cac2188754f1423a1c2b5,0x8c2c694f417142b8152f4c508e870ad622f0a5e115d01ad0363cb428560aba3d0a1582ae8f428560aba3,0xd01ad0363cb06a521dca1c0a7288b1773a0c42635acd41484ee87031d41ea62cd41484ee87109ca14c5d,0xcd4a089ab473528226ad1c5d0a0756332223a1c2b5d01ad0363cb406b40d8f2c9c1486ae872223a232b5,0xd2a2183a54f4a8860e953d2a2183a54f4a8860e953cc1aa057333334282b58cd2a218c654f4a88631953,0xc50ae054bd3115c425c5ad2a218c654f222b82a2f4d2a2183a54f4a8860e953d2a2183a54f4a8860e953,0xce90a0a9e33464540d7a2d1915035e8b314a813d4cc50ae054bd3464540d7a2c9c1486ae87074a81ad4c,0xd01ad0363cb2223a232b5c50ae054bd3454860cd53c1d2a06b533142b8152f4c88ae0a8bd2346e0568e8] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_40s1 : Span p3_40 3 6 12 :=
  batch _ _ _ _ #[
0xc1d3103356b074c40cd5ac0a9583aa8f3a84222b99c44ad094bc83356853c2ccc52a04f533314a813d4c,0xa5e421d5853170541d3a2cc8aa05ab33322a816accc8d620af153314a813d4ccc52a04f533314a813d4c,0xc852e0655d0d5066843abc42ae046bd310ab811af4c5c15074e8b170541d3a2c0a8e82e2d7074c40cd5a,0xc44ad094bcb02ab80aaf4c0aae02abd3141ca1685dc5c15074e8b141ca1685dc5c15074e8b10ab811af4,0xc852e0655d32b08626353c5415854e8f15056153a3c852e0655d306a521dca1c152e02d5d3054b80b574,0xcd510895667054b80b574cac21898d4ea2c685a1acc5c15074e8b109ca14c5dc5415854e8f322a816acc,0xd2a218c654f170541d3a2c428e8662d710a3a198b5d0d098b162f2065629ca3c198a87323715056153a3,0xc5c15074e8b10ab811af4c0a8e82e2d7046560dca3c152e02d5d3054b80b574c119583728f4a88631953,0xc118e82e2d70463a0b8b5c1d3103356b074c40cd5ad29098aa62f3a4442999ac588a8d1a37170541d3a2] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_40s2 : Span p3_40 3 12 17 :=
  batch _ _ _ _ #[
0xc507285a1741794a7441dd28298ca52ebc81853b84c42ae046bd310ab811af4c818e885ad710ab811af4,0xac85315287b314c421d5ac1d3103356b074c40cd5ac118e831ad70463a0c6b5cc52a04f533074a81ad4c,0xa62199426af46a82358d1c1d3103356b46a82358d1c5415854e8f230562a3a3cc8aa05ab3315056153a3,0xcc8aa05ab3315056153a3cc8aa05ab33322a816acccc53108756b314c421d5acc8aa05ab33322a816acc,0xc2a2e029dd30a8b80a774c2a2e029dd30a8b80a774c2a2e029dd315056153a3c5415854e8c54666468ab,0xc8c628731572318a1cc55ccd110b0e6b111d41dc62cd4a08b334654466445abc9ca0897347174442539a,0xcd41484ee87112b421af2c44ad086bcb06a521dca1c546288f1572318a23c55c546287315702a560eaa3,0x14a999132af334442c39ac0cad032bcb032b40caf214ccd10eccb270521aba1d111583568f032b40caf2,0xd28298ca52f046b80d4f4c11ae0353d34a0a63294b] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_40s3 : Span p3_40 3 17 22 :=
  batch _ _ _ _ #[
0xc0a8e82e2d7422b40caf2d08ad032bcb046b80d4f4c11ae0353d310a3a198b5948cd10eccb1a1c426a5a,0xce82a059d333a0a81674cc81728d117435a1a66685c0a8e82e2d7444560d5a3c8c62873157444560d5a3,0xc8c6288f1572318a23c55d01ad0363ca2631a72705c0aae02abd3428560aba3c0aae02abd31518a1cc55,0xd15218d0d4f2063a198b5ce82a059d333a0a81674cd01ad0363cb3a84222b99c118e82e2d72318a23c55,0xc118e82e2d70463a0b8b5d15218d0d4f109ca14c5dd01ad0363cb3505213ba18f23414f5832063a198b5,0xcd41484ee874a8860e953cd41484ee8710a3a198b5cd4a089ab47270521aba1c9c1486ae873a0a81674c,0xc818e885ad7174442539ac0a8e82e2d702a3a0b8b5c0a8e82e2d74a8860e953c0cad032bcb4a8860e953,0xc9ca08973465073445732c0aae02abd302ab80aaf4d0a1582ae8f02ab80aaf4c5d11094e6b10ab811af4,0xc0a9583aa8f464540d7a2d1915035e8b0463a0c6b5c118e831ad7464540d7a2] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_40s4 : Span p3_40 3 22 27 :=
  batch _ _ _ _ #[
0xc1a948772874a0a63294bc1a94877287270521aba1c818e885ad7112b421af2c44ad086bcb06a521dca1,0xc0cad032bcb032b40caf2cd41484ee87111d433a62c118e831ad7112b421af2c0c7507a98b112b421af2,0x94a1990a6af1a1c426a5acd41484ee873a4282a78cce90a0a9e330463a0c6b5c118e831ad7032b40caf2,0xd08ad032bcb422b40caf2cd4a08973471518a23c55c687109a96b322a816accc8c628731573528225cd1,0xc507285a177334442c39a9702d10e5cb10a3a216b5cc8aa05ab326a8b05a970c2c2988b52f322a816acc,0xc2a2e029dd34548634353cc18a88f23702a3a0c6b5c88728ca177174442539ac5d11094e6b4a0a63294b,0xcc8aa05ab33322a816accd01ad0a63cb406b4298f2d01ad0a63cb1518a1cc55c2a2e029dd30a8b80a774,0xd111583568f314c421d5ac2a2e029dd30b0a622d4bc2a2e029dd33528225cd195a23111d58388dc50766,0xcd41484ee87045ca2645dc0a8e82e2d702a3a0b8b5c9c1486ae87032b40caf2d111583568f046b80d4f4,0xc1d3103356b3505213ba1] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_40s5 : Span p3_40 3 27 33 :=
  batch _ _ _ _ #[
0x9702d10e5cb074a81ad4cc1d2a06b53302a3a0c6b5c0a8e831ad7444560d5a3d152183354f314c421d5a,0xd0a1582ae8f428560aba3c1d3103356b444560d5a3d152183354f314a813d4ccc52a04f533454860cd53,0xcac2188754f2b08621d53d01ad0363cb02a560eaa3d0a1582ae8f428560aba3c0aae02abd310ab811af4,0xce82a059d333a0a81674cc852e0655d3214b819574d01ad0363cb3222a2668dc152e02d5d32b08621d53,0xd2a2183a54f4a8860e953d2a2183a54f4a8860e953c152e02d5d3054b80b574cc88a899a373a4442999a,0xc0a8e82e2d702a3a0b8b5c0a8e82e2d7032b40caf2cd0948b9a87174281d58cd2a2183a54f4a8860e953,0xcac2188754f354422c599cac2188754f2318a1cc55d0a1582ae8f464540d7a2d1915035e8b428560aba3,0xd1915035e8b464540d7a2c152e02d5d3464540d7a2d1915035e8b0463a0c6b5c118e831ad7464540d7a2,0xcc2948af2870463a0c6b5c118e831ad70463a0c6b5d1915035e8b214b819574c818e885ad72063a216b5,0xc152e02d5d3054b80b574] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_40s6 : Span p3_40 3 33 36 :=
  batch _ _ _ _ #[
0xd08ad032bc8568cc4295ed1915035e8a52866429abd08ad032bcb422b40caf2d2a2183a54f4a8860e953,0xa585315607b3544225599c198a873237174281d58cc152e02d5d3054b80b57414a9991a2af322a816acc,0xcc1aa057333141ca1685dc0a8e831ad702a3a0c6b5c0a8e831ad65c0b443972c428e885ad710a3a216b5,0x9952c1715c335442255991519991a2af334282b58ca1a87195a1a9833458b32a5a981d1aa2e681855784,0xcac2188754f3a4442999a] 34 (by decide +kernel)

private theorem p3_40Good : Good p3_40 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_40s0 (joinSpan p3_40s1 p3_40s2)) (joinSpan (joinSpan p3_40s3 p3_40s4) (joinSpan p3_40s5 p3_40s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_41s0 : Span p3_41 3 0 6 :=
  batch _ _ _ _ #[
0xcc2b089aa67115c42cc5accd0a057333276021cd51c6a0e046bd3340ca1439dc6a0e046bd31a83811af4,0xc427285a1771425616363d0a628ce1571162614d4bcc2b089aa67035c425c5ac9832888e77334282accc,0xc50ae074ad3142b81d2b4a0c599d10af4283a0a8f5d0a0e82a3d74283a0a8f588eac1b1ac3276021cd51,0xcc52a055e33142b82b2b4c54628731571518a1cc55c9832888e77111d41dc62c54628731573302a22ccd,0xc447507718b440d6153a3c44a989722f3302a22ccdc1d2a0a9e33260ca2239dad6301b1663314a81578c,0xc9c148ab3870a5c426a5ac1d2a0a9e334283a0a8f5d0a0e82a3d74283a0a8f5d1035854e8f440d6153a3,0xc9c22870e543356853c2cd0235846e8f408d611ba3ccd0a0573333342815cccd0235846e8f10ab819ab4,0xcc232846677308ca1199dc8d62077153046560e563c119583958f3342815cccc688d0665cb1a23419972,0xccd0a0573332a438294f4c9c22870e573a0c421b9ac9c22870e57308ca1199dcd0b089aa67342c226a99,0xc1a3282a677068ca0a99dc1a3282a677035c425c5a] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_41s1 : Span p3_41 3 6 12 :=
  batch _ _ _ _ #[
0xcc1aa0b9a33141ca1685dc8c0e888bd730ac226a99c6a0e046bd3174282acccc9c22870e574458a34655,0xc1a3282a677068ca0a99dc11ae035ad33a0a813b8cc427285a177235881dc54c9c22870e573a0c421b9a,0xc457109716b30a5216761c688d0665cb1a23419972c688d0665cb30a5216761c688d0665cb1a23419972,0xcea220a5e53155881dc54cc294859d873a0c421b9ad0a628d1957141ca1685dc507285a177334282accc,0xc298d02e5cb0a6340b972c298d02e5cb0a6340b972c298d02e5cb0a6340b972c0d7109716b3a0c421b9a,0x3507321617b10a5611d63c81ae066ad32303a222f5ce90a05ab333a42816accd1a148573873a42816acc,0xc11ae02ead3046b80bab4c540e850bd702a560ad63c1d2a0a9e332708a1c395c688d0665cb1aa0621d53,0xa60cd162ccb10a5611d63c8c0e888bd72708a1c395d1a148573874685215ce1c0a7288b177029ca22c5d,0xc4272853177109ca14c5dc427285317702a560ad63c540e850bd72708a1c395c0a7288b177029ca22c5d] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_41s2 : Span p3_41 3 12 17 :=
  batch _ _ _ _ #[
0xcc52a055e33162a81dc8cd0235846e8f408d611ba3c540e850bd71503a142f5d0235846e8e5642c858ce,0xc297109a96b308ca1199dd190a8ca33702ab80bab4cd09484f5873508a23395cd09484f5871a83811af4,0xc11ae02ead3262521ad61cc52a055e33406a634a8bcd0b08972670a5c426a5ac81ae066ad3206b819ab4,0xd0235846e8f408d611ba3d0235846e8f408d611ba3c1a3282a677068ca0a99dc11ae02ead3046b80bab4,0xd110e8313d72318a1cc55c447507718b111d41dc62d110e8313d74443a0c4f5d0235846e8f408d611ba3,0xc44a98b322f1702a22ccdc5581898d4f2318a1cc55cd0b089aa67032a625c8bc1ab08d62671a1c426a5a,0xce90a05ab333a42816accce90a05ab3310a5611d63cc2b08ba2671702a22ccdc458d070dcb116341c372,0xc11ae02ead32a5881ea54ca96207a95302a560ad63c0a9582b58f02a560ad63cd5220ace5302a560ad63,0xc143583568f314c42539acd5220ace53046b80bab4] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_41s3 : Span p3_41 3 17 22 :=
  batch _ _ _ _ #[
0xc0a9582b58f02a560ad63c458d070dcb02a560ad63c84358a568f0363423372c429584758f274881d394,0xc298d02e5cb116341c372c458d070dcb116341c372c458d070dc83ba1466742c143583568f02a560ad63,0xc6a6207a9531a9881ea54c458d070dcb10ab819ab4cd4148b93873425213d61c9d22074e53141ca14c5d,0xcc23284667715438152f4c298d02e5cb116341c372c458d070dcb02ab80bab4c298d02e5cb0a6340b972,0xc5581898d4f116341c372d0a0e82a3d74283a0a8f5c11ae02ead3308ca1199dc81ae066ad3308ca1199d,0xc68710ba16b1518a23c55d0235846e8f408d611ba3c1a3282a6770a5c426a5ac1a3282a677068ca0a99d,0xcc2b089aa671702a22ccdc507285a1771a2261694bcc531094e6b06ac234a99c88728ca1773302a22ccd,0xc1a3282a6774283a0a8f5c11ae035ad34283a0a8f5d0a0e82a3d73302a22ccdc8c628731571a1c426a5a,0xc550e054bd3068ca0a99dcd0b089aa67270522ace1] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_41s4 : Span p3_41 3 22 28 :=
  batch _ _ _ _ #[
0xc88728ca1774688a0c795cc294859d873aa0226751c1a948c9d862cc8a63195c54628731571518a1cc55,0xc98b08d2a671518a1cc55c550e054bd3141ca1685dc507285a1771a2261694bc5c0a88b3374688a0c795,0xcea80899d474688a0c795ce82a04ee330a6340b972ce82a04ee331518a1cc55c54628731562cc8a63195,0xccc0a8533374443a0c4f5d110e8313d74443a0c4f5c0ca989722f342c226a99cc5310b0e6b15438152f4,0xc0d8d031dcb314a81578cd110e8313d702ab80bab4d110e8313d72318a1cc55c688d0665cb1163421772,0xce831086e6b308ca1199dcc232846677308ca1199dc8c628731570a6262654bc546288f1571518a23c55,0xc546288f1573302a14ccdc0d8d031dcb3505215ce1cc2b08ba2672a438294f4cc2b08ba2671702a22ccd,0xc8d62077153174282acccc5d0a0ab333276021cd51c9d8087354730ac226a99c507285a177066a83568c,0xd0a0e82a3d73a0c421b9acc2328466771742815cccccd0a0573331a83811af4c6a0e046bd3155882bc54,0xc427285a1773342815cccc298d085dcb1742815cccc1a3282a677235881dc54c1a3282a677050d60d5a3] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_41s5 : Span p3_41 3 28 32 :=
  batch _ _ _ _ #[
0xc688d0665cb1a23419972c143583568f4688a0c795c688d0665cb1a23419972c688d0665cb1742815ccc,0xcc294859d871742815ccccc294859d871742815cccc688d0665cb050d60d5a3c688d0665cb1a23419972,0xce831086e6b4688a0c795d1a22831e57050d60d5a3d1a22831e574688a0c795c457109716b141ca1685d,0xce831086e6b3a88829794c0aae035ad302ab80d6b4d1a22831e57050d60d5a3ce831086e6b3a0c421b9a,0xcc294859d871742815cccc45710b316b1162614d4bc45710b316b1162614d4bc0d7109716b02ab80d6b4,0xa54cc1754c3206b819ab4a54cc1754c3210d6295a3d1a22831e574688a0c795c143583568f050d60d5a3,0xc0d8d031dcb02a560ad63c0a9582b58f02a560ad63c429584758f10a5611d63ce90a05ab3310a5611d63,0xc84358a568e9833458b32b9a06157313210d6295a3c11ae02ead3050d60d5a3c6a8188754e64c8a5c195,0xce831086e6b02a560ad63c0a9582b58f02a560ad63c429584758ee4c885d194c429584758f10a5611d63,0xd11628ce157050d60d5a3c143583568f3a0c421b9a] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_41s6 : Span p3_41 3 32 34 :=
  batch _ _ _ _ #[
0xc887288b1773560226751c9d808d1d4727052354e1c507285317710ab819ab4c42ae066ad310ab819ab4,0xc297109a96b342c225c99c297109a96b4283a0a8f5c0aae02ead302ab80bab4c0aae02ead3350522e4e1,0xcc52a055e334298a33855cd580899d47068ca0a99dcd4148b9387162a81dc8cc9c148d5387308ca1199d] 24 (by decide +kernel)

private theorem p3_41Good : Good p3_41 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_41s0 (joinSpan p3_41s1 p3_41s2)) (joinSpan (joinSpan p3_41s3 p3_41s4) (joinSpan p3_41s5 p3_41s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_42s0 : Span p3_42 3 0 6 :=
  batch _ _ _ _ #[
0xcc8b1094e6b06ac222b99c54628731571518a1cc55c11728d11771518a1cc55cc8b1094e6a53834458f2,0xc8172899177414b40d732d052d035ccb30ac214b99d052d035ccb4443a0c4f5cc2b0852e6730ac214b99,0xd052d035ccb109ca14c5dc5c0a8d1337446860cb93b1318ad03a7109ca14c5da32662af113029ca22c5d,0xd191503738b464540dce2c6a0e046bd31a83811af4c6a0e046bd3340ca1631dd2a218c6c4f30ac214b99,0xc298d085dcb3302a22ccdc858c8715c7216321c571c298988b52f414b40d732d052d035ccb464540dce2,0xcc1aa055e332225632363cc2b0852e6730ac214b99cc8b1094e6b0a6342177238455a3708f216321c571,0xc88958c8d8f111d41dc62c5462873157406a614b8bcc8b1094e6b06ac222b99c1ab088ae671425616363,0xcd414857387340ca1631dd11a1832e4f340ca1631dc54628731571518a1cc55d01a9852e2f406a614b8b,0xc1ab08aa6671aa0631953c6a818c654f440ba13335d11a1832e4f446860cb93c98328c8c77334282e4cc,0xc858c8715c74283a0a8f5d0a0e82a3d74283a0a8f5d0a0e82a3d74283a0a8f5d102e84ccd7440ba13335] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_42s1 : Span p3_42 3 6 13 :=
  batch _ _ _ _ #[
0x116a595660f162a81ab8cccc150b8b8b308ca11d1dd1a148573874685215ce1cc232847477308ca11d1d,0xc81958c558f152862c393c8ca1894e4f4a0a632b0bc8172899177322a813b8cd1a14857384175687262c,0xcd09484f587046560e563c119583958f046560e563c1ab088ae67262521ad61c11728991772328625393,0xc298d085dcb1503a142f5c858c8715c70a63421772c298d085dcb342c214b99cd09484f587205ca3445d,0xcc1aa055e33216321c571c1a3282b477068ca0ad1dc1a3282b47702a560ad63c0a9582b58f02a560ad63,0xc8ca1894e4f2303a222f5cc1aa055e3330ac214b99c6a0e046bd3262521ad61c6a0e046bd30a63421772,0xc58aa06ae33162a81ab8cc58aa06ae334642a14ccdcd0b0852e642875668ca3c54a18b0e4f2328625393,0xd05298d542f2303a222f5c540e850bd72a5882bc54c98b088ae6730a5216761c54a18b0e4f2303a222f5,0xccc150b8b8b10a5611d63c540e850bd7330542e2e2c19b1032e6b406a614b8bc0d8989952f406a614b8b,0xc1a3282b47702a560ad63c0a9582b58f1a23419972c688d0665c8d41cc8585e9884ea2e0d71a23419972] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_42s2 : Span p3_42 3 13 18 :=
  batch _ _ _ _ #[
0xd08a985662c568cc42b1ec688d0665cb1a23419972d08a985662f141ca1685dae1191833ab2303a222f5,0xc0a728ca1772a5882bc5481666a999172a5882bc54d08a985662f1503a142f5d05298d542f152862c393,0x9a84ca8e8c7216321c571ca9620af153162a81ab8cc427285a1770563223571c58aa06ae3294c68560ec,0xcc1b1086e6b036262654bc989486b587262521ad61cc1b1086e6acc50674a13c858c8715c74642a14ccd,0xd01a9852e2f262521ad61c19b1032e6b066c40cb9aac15315287b0563223571c989486b587262521ad61,0xc9c148ab387205ca3445dc119583958f046560e563d022e845cd7408ba11735d022e845cd7408ba11735,0xcc8aa04ee332318a23c55d110e8313d74443a0c4f5c55818d0d4e5688c45716cc8aa04ee33046560e563,0xd08a985662f422a61598bc54628731570b0a62ad0bca88c86a5c72a2321a971d08a985662f422a61598b,0xc2c298ab42f422a61598bc447507718b2a2321a971c119583958f4443a0c4f5] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_42s3 : Span p3_42 3 18 23 :=
  batch _ _ _ _ #[
0xc58aa06ae33046560e563c1d310d4c6b074c43531a8ce42999857162a81ab8cc1172899177162a81ab8c,0xd282d02eccb308ca11d1dc429584758f308ca11d1dcc5310b8c6b116341c372cc5310b8c6b322a813b8c,0xc8d81898d4f109ca14c5dc142e82d4d7050ba0b535c1a3282b4774a0b40bb32c1a3282b47702a560ad63,0xcc1aa055e3330ac214b99cc2b0852e67210ba19535c842e8654d7141ca14c5dc0ca989562f050ba0b535,0xcd09484f58414ee8531acc142e82d4d7050ba0b535ccc0a899337050ba0b535c5072853177350522e4e1,0xca9620af153262c222b99d282d02eccb30a5216761d282d02eccb4a0b40bb32c44a98b162f0aa3222771,0xd191503738b464540dce2cc8aa04ee334a0a632b0bd282d02eccb2a5882bc54d282d02eccb4a0b40bb32,0xc8d81898d4f0aa3222771cc8aa04ee3315438152f4cc8aa04ee3315438152f4d191503738b4a0a632b0b,0x14e8d10e5ca5688c45716d11a1832e4f141ca14c5dc550e054bd315438152f4c8d0e0a8bd3221ca22c5d,0xc2a8c889dc7066c40cb9a] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_42s4 : Span p3_42 3 23 29 :=
  batch _ _ _ _ #[
0xd11a1832e4f446860cb93c1a3282b477342c215999d11a1832e4f02a560ad63cc23284747710a5611d63,0x899d4177283141ca1685dc507285a176e42168e943151ce10ead3050ba0b535cd0b0856667066c40cb9a,0xc507285a1772a2321a971c507285a1772a2321a971cc5310b8c68550e64652b959191133ab464540dce2,0xc44a98b162f116341c372cc8aa04ee33210ba19535c842e8654d7234382a2f418bb119466b2a2321a971,0xc550e054bd3464540dce2cc8aa04ee334a0b40bb32cd4148b93874548635313d0a0e82a3d74283a0a8f5,0xc458d070dcb3425213d61c842e8654d715438152f4c550e054bd3234382a2f4c142e82d4d7322a813b8c,0xc142e82d4d73425213d61c142e82d4d7066c40cb9a154399194af15438152f4c19b1032e6b4283a0a8f5,0x8d1b818d6a3046560e563ca88c86a5c74443a0c4f5d110e8313d6b421c53946c8c6288f1572318a23c55,0xcd41485738742a860d993c81958c558f322a813b8cd08a985662f422a61598bc688d0665cb422a61598b,0xc58aa06ae33046560e563ca90e0a53d2274e072728] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_42s5 : Span p3_42 3 29 35 :=
  batch _ _ _ _ #[
0xc1a3282b477342c215999d11a1832e4f02a560ad63151ce10ead310a5611d63d11a1832e4f10a5611d63,0xc507285a177464540dce2d11a1832e4f068ca0ad1dd052d035ccb414b40d732c1a3282b477068ca0ad1d,0xc142e82d4d7414b40d732c6a0e046bd3414b40d732c55620b9953464540dce2d2a218c6c4f050ba0b535,0xc44a98b162e5c0b443b32d0a0e82a3d742a860d993d0aa183664f464540dce2c6a0e046bd31a83811af4,0xd0aa183664f350522e4e1d0aa183664f050ba0b535c427285a1765c0b443b32d0a0e82a3d74283a0a8f5,0xc142e82d4d73560226751c19b1032e6b4283a0a8f58d538159ca32760234751cc1b1086e6ab216853c2c,0xc5d0a0d533317428354ccccc0a88b337141ca1685da74419b304f1a98833a54c989486b587414b40d732,0xd08a985662f1a83811af4c6a0e046bd3422a61598bc6a0e046bd084ee88b1accc1aa055e323c2946b982,0xd0a0e82a3d74283a0a8f5d0a0e82a3d73302a22ccdccc0a88b3374a0b40bb32d282d02eccb4283a0a8f5,0xc858c8715c742a860d993c858c8715c742a860d993cac218a744f1aa0631953] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_42s6 : Span p3_42 3 35 36 :=
  batch _ _ _ _ #[
0xc8c6288f157342c215999c19b1032e6b1a23419972d11a1832e4f306c421b9accd0a0b933317428354cc,0xc688d0665cb031d42bc62c8c6288f157141ca1685dc507285a1772b08629d13] 14 (by decide +kernel)

private theorem p3_42Good : Good p3_42 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_42s0 (joinSpan p3_42s1 p3_42s2)) (joinSpan (joinSpan p3_42s3 p3_42s4) (joinSpan p3_42s5 p3_42s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_43s0 : Span p3_43 3 0 8 :=
  batch _ _ _ _ #[
0xac15a1598b33560223d51c5095858d8e831667442bc8d620771531425616363c1c2a871637340ca1439d,0xc14ac8b13c71425616363c50ae054bd31425616363c5095858d8f3544215d19c1c2a871637340ca1439d,0xc5095858d8f4458a33855c298d0665ca5c88644b93d1a22831e574688a0c795d1a22831e57340ca1439d,0xba221982e4f070aa1c58dd01ad0363cb406b40d8f2cd032850e771425616363c298d0665cb1425616363,0xcc1aa05ab33142b8152f4c5095858d8eb0a1c53946c50ae054bd31425616363cc1aa05ab33405d433a62,0xc9832888e76853166cc83cea1085ac67340ca1439dc158c8715c72318a1cc55cd5108b9467056321c571,0xd0a0e829cd74283a0a735d1035854e8f1702a1ad0dc5c0a86b437440d6153a3c447507718b1518a1cc55,0xc5c0a86b4372a60631953c298d0665cb111d42bc62cea80899d47142b8152f4c50ae054bd34283a0a735,0xd01ad0363cb406b40d8f2cc52a0ad633406b40d8f2cd032850e77340ca1439dc5c0a86b4365c88644b93,0xa464e1558d3142b8152f4c447507718b2225632363d1035854e8f40ab2158f1c88958c8d8f222b82a2f4] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_43s1 : Span p3_43 3 8 13 :=
  batch _ _ _ _ #[
0x10d599530ac4356654c2bd0235846e8f408d611ba3cd094859d873425216761d0235846e8f3425216761,0xc81ae0a53d3070d41d3a2d182a851e373508a23395ca88c889dc7046560e563b918c1715c34342615d0b,0xd10ac852bc730a5216761c119583958f046560e563d10ac852bc73a0c421b9ad0d0985742f206b8294f4,0xce831086e6b306a82e4ccd0d0985742f4342615d0bc19aa0d5333308ca1199dc11ae0353d3046b80d4f4,0xd0d0985742ee463063570d1aa08d6347046b80d4f4c119583958f046560e563c119583958f4342615d0b,0xd290985ac2f10a5611d63d182a851e37460aa1478dc8c0e868cd6b58c055998d290985ac2f2303a1a335,0xc540e84ccd71503a13335a62199434af02a560ad63c0cad0b0bcb306a816acccc1aa05ab33306a816acc,0xd10ac852bc710a5611d63c0d898d152f10a5611d63c8c0e868cd6b58c055998d10ac852bc7056321c571,0xca9620b99532163223571c0a9582b58f02a560ad63c1a9486b58706a521ad61151ce115ad3056321c571] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_43s2 : Span p3_43 3 13 18 :=
  batch _ _ _ _ #[
0xc0aae02abd302ab80aaf4cd5108b9467221ca22c5dd0235846e8f10ab811af4d0235846e8f3a84216b19,0xd290985ac2f221ca22c5dd290985ac2f056321c571cd42288ce571503a13335cc4350ace8b02ab80aaf4,0xc858c88d5c74a42616b0bd01750ce98b4298a34655cea220a5e53112b4252f2d290985ac2f4298a34655,0xc429584758f10a5611d63a660d1a1ccb10a5611d63cd42288ce57070d41d3a2d290985ac2f141ca14c5d,0xc0a9582b58f02a560ad63c540e84ccd71503a13335c298d0665cb0a63419972cd42288ce545662cc294e,0xd0235846e8f10ab811af4d0235846e8f408d611ba3cd09484f5873425213d61cc4350ace8b02a560ad63,0xc50728531771a9881ea54c507285317702ab80aaf4c0aae02abd30a63419972c989486b587221ca22c5d,0xcd09484f5874a42616b0bd0a628ce1572303a1a335d290985ac2f262521ad61d290985ac2f308ca1199d,0xc1a3282a677068ca0a99dc1a3282a67740ab2158f1] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_43s3 : Span p3_43 3 18 23 :=
  batch _ _ _ _ #[
0xcc531094e6b314c42539acd4a08b3347408d611ba3d0235846e8f408d611ba3d0235846e8f408d611ba3,0xc5c0a86b437036341c372d110e82d4d7460aa1478dc6c098ab42f3302a13d0dd1835035e8b1b0262ad0b,0xd1a22831e57422b40caf2d10ac852bc7046b80d4f4951199194af206b8294f4d10ac852bc7442b214af1,0xc5c0a86b437031d41dc62cd4a08973471a1c426a5acd4a08973471a1c426a5ac11ae0353d3442b214af1,0xcd5220ace534443a0b535ccc0a84f437272822ccd1d08ad032bcb422b40caf2c1a3282a677274881d394,0xcc531094e6b314c42539a151ce10ead302a560ad63c429584758f2a5881ea54c1d310b0e6b274881d394,0xd29098cac2f050d60d5a3cc1aa05ab334a42632b0bcc531094e6b212b2254f1cc531094e6b212b2254f1,0xcc29484f58702a560ad63cc29484f58702a560ad63c429584758f10a5611d63c1c2a8716371a1c426a5a,0x843b91983ab3a8422ad198cab81533a222e8c6c0d6cc42a88d637310aa2358dd08ad032bcb050d60d5a3] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_43s4 : Span p3_43 3 23 29 :=
  batch _ _ _ _ #[
0xc0aae02abd33a84216b19cc8aa05733310ab811af4c0d8d070dcb10ab811af4c42ae046bd33a84216b19,0xc58aa057333036341c372c887288b177210d6295a3d1aa08d2b4484ee88e0ecc84ac8953c7141ca14c5d,0xc58aa057333141ca14c5dcc42a88d637050d60d5a3d0a0e829cd74283a0a735c458d08cdcb4a42632b0b,0xc0a9582b58f02a560ad63c429584758f10a5611d63c429584758f1b0262e50bc688988b52f212b2254f1,0xc143583568f274881d394154399116ae5383445732cc29484f58702a560ad63cc29484f58730a5213d61,0xc0aae02abd25c88644b93c42ae046bd310ab811af4cd09484f5873425213d61d11628ce157050d60d5a3,0xd1aa08d2b4746a8234ad1d1aa08d2b47406b40d8f2c5072853177141ca14c5dd01ad0363cb3a84216b19,0xcd09484f587074c42c39acc232846677308ca1199dc58aa057333162a815cccc989486b587308ca1199d,0xc0aae02abd302ab80aaf4c42ae046bd3460d40d7a2d29098cac2f4a42632b0bc0d8d070dcb068ca0a99d,0xc8d620771533560223d51d11628ce157406b40d8f2c84ac8953c7406b40d8f2c0aae02abd3460d40d7a2] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_43s5 : Span p3_43 3 29 35 :=
  batch _ _ _ _ #[
0xcd5108574673425216761cd094859d87460d40d7a2cc1aa05ab33460d40d7a2d1835035e8b460d40d7a2,0xc9d80873547422b40caf2c1a3282a677066a832accc1a3282a677109ca1685dc9d108ab467068ca0a99d,0xc1a3282a6773a0c421b9ac1a3282a6773544215d19c143583568f46a82358d1c0a728ca17746a82358d1,0xcc294859d874283a0a7358d1b815a3a34688a0c795c29898ca52f210d6295a3d08ad032bcb068ca0a99d,0xc298d0665cb050d60d5a3ce831086e6b3a88829794ce831086e6b3a88829794d0a0e829cd74283a0a735,0xd1835035e8b02ab80aaf4c42ae046bd310ab811af4c42ae046bd3460d40d7a2d1835035e8b460d40d7a2,0xcd4a0897347308ca1199dd1835035e8b460d40d7a2c5c0a86b4372a60631953d01ad0363cb406b40d8f2,0xc427285a177068ca0a99dc19aa0cab33306a816accd182a851e373425216761d1835035e8b2318a1cc55,0xd08ad032bcb422b40caf2ca9620b9953308ca1199dcc232846677308ca1199dc1a3282a6772318a1cc55,0xd08ad032bcb068ca0a99dce831086e6854738456b4ce831086e6b029ca3285d] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_43s6 : Span p3_43 3 35 36 :=
  batch _ _ _ _ #[
0xcea220a5e534283a0a735d0a0e829cd7056321c571c8c6288f1574283a0a735d0a0e829cd74283a0a735,0xc298d0665cb442b214af1ce831086e6b3a0c421b9ac858c88d5c74283a0a735] 14 (by decide +kernel)

private theorem p3_43Good : Good p3_43 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_43s0 (joinSpan p3_43s1 p3_43s2)) (joinSpan (joinSpan p3_43s3 p3_43s4) (joinSpan p3_43s5 p3_43s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_44s0 : Span p3_44 2 0 4 :=
  batch _ _ _ _ #[
0xcc8b1032e6b322c40cb9ac5a1288b177308ca0cc9dcd0b0852e673284a14c5dcca12853177054b81d2b4,0xcc8b1032e6b308ca0cc9dcc2328332774645435662c0ca989562f306540e762c8c0e8711d706a521ad61,0xd282d02eccb346880d794cd1a2035e534a0b40bb32cc195039d8b032a62558bcea8088f5472360626353,0xd052d0acccb414b42b332cc5310b8c6b2360626353cd1a2035e53074c43531ad28298cac2f4a0b40bb32,0xce83103ac6b3460a0c795c8474879587428562ac63ce83103ac6b211d21e561c8d62078d533425213ba1,0xcca128531773284a14c5dcc18a851e373284a14c5dd282d02eccb3460a0c795d282d02eccb1558833354,0xc989486ae873a8880bd54c989486ae87262521aba1cea2202f553428562ac63cd182831e573460a0c795,0xc989486ae87306a82e68ccea2202f5533a8880bd54] 60 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_44s1 : Span p3_44 2 4 9 :=
  batch _ _ _ _ #[
0xce82a04ee332303a1c475c0d8d070dcb1503a23475cd5220ace521193a53835cc29484f5872303a1c475,0xcc195039d8b306540e762d19150d598b1503a23475c9d22074e533a0a813b8ccc1aa0b9a333a0a813b8c,0xc8d62078d533062a1478dcc195039d8b306540e762cc195039d8b06a521ad61c5a1288b1772303a1c475,0xd0175039d8b322a816accc5a12853177212b22c4f1ccaa2037351e888a58d157a222963457211d21e561,0xcd09484ee858394a7281dc2c2989952f3284a14c5dcca128531773062a1478dcc18a851e373062a1478d,0xc0d8d070dcb16a8829cd4d08ad032bcb3425213ba181ea51d630b322a816accd08ad032bca518b443972,0x7a035162e8b1503a23475cc29484f5872a4382a67494179119cab3284a14c5dcca128531772303a1c475,0xc1a9486b5873aa0223d51c152e074ad3342c214b99cc195039d8b354882b394ccaa2037353422b40caf2,0xcea108ab467036341c372c458d08cdcb068ca0cc9d0a62e9622d74458a34655c1a9486b5874642a3270d] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_44s2 : Span p3_44 2 9 14 :=
  batch _ _ _ _ #[
0xcc531098d6b066540d7a2c5581894e4f066540d7a2c5581894e4f066a83568cc19aa0d5a333425213ba1,0xc1c2a87163710a5611d63c0d8d070dcb10a5611d63cc1aa0b9a33046b80d6b4c11ae035ad3306a82e68c,0xcc42a88d637046b80d6b4c0a9582b58f02a560ad63c458d08cdcb02a560ad63c9d22074e5302a560ad63,0xc429584758f308ca11d1dc429584758f10a5611d63cc1aa0b9a33046b80d6b4c458d08cdcb1163423372,0xc1a9486b5871560634353d1915035e8b029ca22c5dc0a9582b58f308ca11d1dcc23284747710a5611d63,0xc1a3282b47702a560ad63d282d02eccb308ca11d1dc429584758f308ca11d1dc1a3282b47706a521ad61,0xc0ca989562f050ba0b535c8d81898d4f109ca14c5dc142e82d4d7050ba0b535c1a3282b4774a0b40bb32,0xc687109a96b322a816acccc8aa05ab322b8b05a970c989486ae871560625393d1aa08b33471a1c426a5a,0xc1995035e8b3a8422ad19cc8aa05ab302ba166a983d08ad032bcb46a822ccd1] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_44s3 : Span p3_44 2 14 19 :=
  batch _ _ _ _ #[
0xcc29484f58702a560ad63cc29484f58702a560ad63c429584758f10a5611d63c1c2a8716371a1c426a5a,0x843b91983ab3a8422ad198cab81533a222e8c6c0d6cc42a88d637310aa2358dd08ad032bcb050d60d5a3,0xc429584758f308ca11d1dc429584758f10a5611d63c429584758f308ca11d1dcc232847477308ca11d1d,0xc1a3282b477068ca0ad1dc0a9582b58f02a560ad63d1915035e8b308ca11d1dcc23284747710a5611d63,0xc8d62078d53054b81d2b4c142e82d4d7050ba0b535cc29484f5872360626353d28298cac2f068ca0ad1d,0xc8474879587322c40cb9acc8b1032e6b211d21e561c8474879587342c214b99c152e074ad3054b81d2b4,0xc5a12847477334442e31ac19950d598b2b0322b531c55620ccd53115c42635acd1a2035e531a23423a72,0xcc8b1032e6b346880d794cea108ab467409d22bca1cca1282b4771a23423a72cca1282b477314c42635a,0xcca1282b4773a0a813b8cc5a128474773a0a813b8cd15218b0e4f1684a11d1dc5a12847477070aa1c58d,0xc688d08e9cb4642a3270dc11ae035ad3454862c393c11ae035ad33284a0ad1d] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_44s4 : Span p3_44 2 19 25 :=
  batch _ _ _ _ #[
0xce83103ac6b4548635313d19150a5e8b334442539ad19150a5e8b308ca11d1dcc232847477308ca11d1d,0xc0c6a8794359835470ae2d15218d4c4f068ca0ad1dce83103ac6b3a0c40eb1ac1a3282b4773a0c40eb1a,0xc11ae035ad30b0a62654b1a23594358f174442539ac9c14875687031aa1e50dc2c2989952f0b0a62654b,0xc0ca989562f068ca0ad1dcd1a2035e531702a344cdd15218d4c4f342c214b99c550e054bd3308ca11d1d,0xc550e054bd3029ca0ad1dd0d0d0b0bcb15438152f4c58b1086e6b342c214b99c2a7088b567050ba0b535,0xd1aa08b3347070aa1c58dcc8b1032e6b434342c2f2c19950d59899a14c62a1ec550e054bd33a8880bd54,0xc0d710d0d6b050d60d5a3c4571098d6b1684a11d1dc5aa20a7353454862c393c84358a568f035c43435a,0xcc232847477334442539acc232847477308ca11d1dcc232847477308ca11d1dc4571098d6b310aa2358d,0xccaa2037353068ca0ad1dd052d0acccb174442c39acc8aa05ab3346454297a2c5aa20a7353308ca11d1d,0xcc8aa05ab33068ca0ad1d] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_44s5 : Span p3_44 2 25 31 :=
  batch _ _ _ _ #[
0xc0a7282b477031aa1e50dd19150a5e8b322a816accc4272847477109ca11d1dc9c14875687174442539a,0xcd0b0852e666429654b83cc8aa05ab334548634353cc8aa05ab33334442c39ac0a7282b477029ca0ad1d,0xc45710b8c6b2360626353c8d81898d4f068ca21c9dc58b1086e6b068ca21c9dc58b1086e6b162c421b9a,0xcd09484ee87235881e354cc2328872773460a0c795d08ad032bcb054b81d2b4cd0b0852e67342c214b99,0xc14ac8953c706a521ad61c852e0acad3422b40caf2c9982885e57405d40e762c8474879587211d21e561,0xce90a0a9e33422b40caf2c9c14875687031aa1e50dc58aa0cab3332a880dcd4d08ad032bcb422b40caf2,0xc429584758f346880d794c842e8654d7210ba19535c84ac8b13c730a5213d61cc29484f58730a5213d61,0xcea8088f5474a0b40bb32c550e054bd3032a62558bccc0a8993373302a264cdd282d02eccb4a0b40bb32,0xc42728872773460a0c795c42728872772a1c226a99cca1282b4773284a0ad1dc5d110d4c6b3284a0ad1d,0xd08ad032bcb422b40caf2c0a72833277422b40caf2ca87089aa67109ca21c9d] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_44s6 : Span p3_44 2 31 36 :=
  batch _ _ _ _ #[
0xcea108ab467029ca0cc9dc429584758f422b40caf2c42728872773284a0ad1dc9d22074e533284a0ad1d,0xce83103ac6b3a0c40eb1ad1915035e8b3a0c40eb1ac5a128474771684a11d1dd08ad032bcb029ca0cc9d,0xca87089aa6702a560ad63ccaa2037353210ba19535c8d81898d4f210ba19535c842e8654d72a1c226a99,0xcc2328474773a0c40eb1acd182831e573a0c40eb1ac142e82d4d7050ba0b535ccd11094e6b16a8829cd4,0xd282d02eccb4a0b40bb32c14748cd587050ba0b535073951ac68b046b80d6b4d282d02eccb15438152f4,0xc5581894e4f206b8296b4cd09484ee87109ca11d1dc989486ae87262521aba1cd182831e573460a0c795,0xc0a7282b477066a83568cc4272847477035c43531ad08a98d2a2f274881d394c11ae035ad315438152f4,0xce82a04ee33046b80d6b4c11ae035ad30665431762cd5220ace5253834458f2cd5220ace5330ac22cc99] 64 (by decide +kernel)

private theorem p3_44Good : Good p3_44 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_44s0 (joinSpan p3_44s1 p3_44s2)) (joinSpan (joinSpan p3_44s3 p3_44s4) (joinSpan p3_44s5 p3_44s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_45s0 : Span p3_45 3 0 8 :=
  batch _ _ _ _ #[
0xcd5220353d31684a14c5d0e95328687985a9855784c2a2e0a73531a1c43195ac0c75078d8b1b18423372,0xcc8b103666b06a521eaa1c1ab0852e673062a23c8dcc4350d4b8b0a5a813d4cc6c6108cdcb354880d4f4,0xc5a12853177262521eaa1c0c75078d8b2660a198b5c198a87323706a521eaa1cc8b103666b322c40d99a,0xc9d220a53d30a5a813d4ccd5220353d3354880d4f4cd5220353d3354880d4f4c989487aa870662a1e88d,0xcd5220353d30662a1cc8dcc8b1032e6b1684a1685dc5a1285a1770a5c421d5ad02ac8ae647262521eaa1,0xc5a12853177070d42e2e2c44750ccd8b3284a22c5dc5a1285317735602256b1c0c75078d8b035a81674c,0xd0a158ca98f0662a1cc8dcc2b088ae6706a521eaa1c296a06b533162c42999ac0d6a059d33442b22b991,0xc5a128531770662a1e88dc0c75078d8b035a81674ccea2202abd33a8880aaf4cea2202abd306ac214b99,0xc296a06b533162c421b9acd18282e2d7035a81674cc2a7088b567262521eaa1c989487aa871684a14c5d,0xc842e8d0b56c0ce4740eac142e898b57276022c6b1cc8b1032e6b262521eaa1c297108756b1684a1685d] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_45s1 : Span p3_45 3 8 13 :=
  batch _ _ _ _ #[
0xd296102e5cb306c40d99acc1b103666b4a5840b972cc1b103666b2660a198b5cea8088eac723606252b3,0xc14ac872e47112a614b8b621b91626ab3a8880aaf4cea2202abd1e0a9853b84cea2202abd34a5840b972,0xd022e8333570a9c222d59c2a7088b5658a54c6a81ed296102e5cb306c40d99ad296102e5cb0662a1e88d,0xc8c158ab18f310d40dce2c8d62068dd3306c40cb9ac8c0e8731571505615c63621b91626ab3460a0b8b5,0xc44a9852e2f112a614b8bc540e88f157310d40dce2c8d818b0acf15606252b3c8c0e8731572303a1cc55,0x94e61111dcb235881a374c198a873237235881a374c198a873237342c225599c8d62068dd31505616a63,0xc847486b587322c40d99acd1128d11772303a1cc55c296a06b5330a5a81ad4cd017502f58b054b82e2d4,0x7885295a0773a8880aaf4c1a9487aa873a8880aaf4d102e83a355e0a9853b84d102e83a357322c40d99a] 64 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_45s2 : Span p3_45 3 13 18 :=
  batch _ _ _ _ #[
0xc6a0e0af151d08e842cecc14ac872e47322c40d99acc8b1036669d08e842cecc9912899177162c42999a,0xc5581894acf15606252b36a1c29614d7322c40d99a6a1c29614d7112a622b8bc6a0e0af153112a622b8b,0xcd112899177162c421b9a7885295a075e214a5681d15c2b212b38570ac84acec8d818b0acf2644a2645d,0xcc8b1032e6b211d21ad61c5581894acde888a508f5c847486b587460d40eae2cc8b1032e6b162c421b9a,0xd296102e5cb406a62a98bc99828662d72660a198b5d183503ab8b1503a23c55c0d71098d6b40ab22b991,0xd0875039d8b3a8880aaf4c556204cdd33a8880aaf4d296102e5cb306c40d99ad296102e5cb4a5840b972,0xd296102e5cb1a8382bc54d296102e5cb1684a14c5dc98948b9a872660a198b5c44a9852e2f2660a198b5,0xc8c0e87315715606252b3d0875039d8b421d40e762cd18282e2d73460a0b8b5d022e8333573460a0b8b5,0xc147484f587310d40dce2c1c2a853337306c40cb9ac541585718f1505615c63c541585718f2303a1cc55,0xd0875039d8b421d40e762cc43503738b310d40dce2] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_45s3 : Span p3_45 3 18 23 :=
  batch _ _ _ _ #[
0xc296a04f5330a5a813d4cc296a04f5331505616a63c541585a98f1684a1685dc0ca9852e2f112a614b8b,0xc541585718f1505615c63ca8708ca56730a52356a1c0ca9852e2f1558813374c556204cdd31622a2668d,0xc541585718f070aa14ccdc541585718f32a0a0c6b5d102e83a357310d40dce2c8c158ab18f310d40dce2,0xc296a04f5330a5a813d4cd102e83a357322c40d99ac1a948b9a8706a522e6a1cca82831ad71505616a63,0xd017502f58b405d40bd62cca82831ad732a0a0c6b5d102e83a357440ba0e8d5c296a04f5330a5a813d4c,0xc541585718f23606252b3d017502f58b405d40bd62cc8b103666b322c40d99ad017502f58b322c40d99a,0xd183503ab8a540bc44ad6d296102e5cb40ab22c791c541585718f4a5840b972d01a98aa62f1505615c63,0xcc1b103666b2660a198b5ab0661cd5132660a198b5c1c2a8533371505615c63ce82a0cab33070aa14ccd,0xcc18a8ce2372343835654c8d0e0d5953154382e654c550e0b9953306c40d99acc1b103666b0662a1e88d,0xcd18282e2d72343835654] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_45s4 : Span p3_45 3 23 28 :=
  batch _ _ _ _ #[
0xc5a128531772a606298b3c14ac872e47306c40d99ad022e8333570662a1e88dc99828662d7408ba0ccd5,0xcd0b0895667306c40cb9ad0d61031dcb070d429ce2c5a128531773460a0b8b5cd18282e2d71684a14c5d,0xc98b08b1667310d40dce2cc43503738b1505615c63d0d61031dcb1505615c63c8c158ab18f310d40dce2,0xc198a8732370a5c421d5ac198a8732373b08421af2c84ac872e47435840c772c84ac872e470a5a81ad4c,0xc58b10a666b435840c772c5a1285a177112a614b8bd017502f58b1505616a63d017502f58b0a5c421d5a,0xd0d61031dcb310d40dce2cc8b103666b322c40d99ad102e83a357322c40d99aca9620655d3322c40d99a,0xc14ac872e47322c40d99acc8b103666b435840c772c9912899177052b21cb91c147484f587310d40dce2,0xcec21086bcb322c40d99ac0ca9852e2f2a588195747423a10b3b32a58819574d11158d518f2a58819574,0xc0d6a059d33035a81674cc0d6a059d33035a81674cd0d61031dcb032a614b8bc0d6a059d33035a81674c] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_45s5 : Span p3_45 3 28 34 :=
  batch _ _ _ _ #[
0xca82e0c6b53276022c6b1ca9620655d3435840c772cc8b1032e6b35602256b1cd112899177162c421b9a,0xd296102e5cb4a5840b972d183503ab8b051d213d61c1c2a853337070aa14ccdd0d61031dcb2a58819574,0xc1d2a0b93333460a0b8b5c1570899567306c40d99acc1b103666b211d21ad61c847486b587211d21ad61,0xd0875039d8b354880d4f4cec21086bcb4a5840b972d296102e5cb4a5840b972d0875039d8b3460a0b8b5,0xd0875039d8b421d40e762cd18282e2d73460a0b8b5d022e8333573460a0b8b5cc1b103666b408ba0ccd5,0xcc43503738b074a82e4ccd0875039d8b211d21ad61cd5220353d3066c421b9ac9d220a53d3421d40e762,0xc541585a98f0a5a813d4cd0875039d8b421d40e762cc43503738b310d40dce2c147484f587310d40dce2,0xc44a9852e2f1622a2668dc297108756b0a5c421d5acd5220353d3112a622b8bc44a988ae2f354880d4f4,0xc8c158ab18f310d40dce2cd5220353d332a0a0c6b5c5a82885ad7440ba0e8d5c0ca9852e2f1684a1685d,0xc6a62045dd3354880d4f4c6a62045dd332a0a0c6b5d102e83a357310d40dce2] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_45s6 : Span p3_45 3 34 36 :=
  batch _ _ _ _ #[
0xc14ac872e47052b21cb91d102e83a357322c40d99acc8b103666b3b08421af2cca82831ad7440ba0e8d5,0xd017502f58b405d40bd62cca82831ad732a0a0c6b5d102e83a357440ba0e8d5c198a8732370662a1cc8d,0xd296102e5cb4a5840b972d017502f58b405d40bd62cc8b103666b322c40d99ad017502f58b322c40d99a,0xd183503ab8b1a98811774d183503ab8b354880d4f4c0d6a079533406a62a98bd183503ab8b4a5840b972,0xc1c2a853337354880d4f4c6a62045dd3070aa14ccd] 36 (by decide +kernel)

private theorem p3_45Good : Good p3_45 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_45s0 (joinSpan p3_45s1 p3_45s2)) (joinSpan (joinSpan p3_45s3 p3_45s4) (joinSpan p3_45s5 p3_45s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_46s0 : Span p3_46 3 0 6 :=
  batch _ _ _ _ #[
0xcc53103356b0a9c222b99cc8aa0b9333441d22b5a16a037161599ad4c062d58c29710a666b0a5c42999a,0xc4475074e8b050d616363655981732a3050d616363cd18282e2d73460a0b8b5c2a7088ae672b08622373,0xc1435858d8f1a1c421b9ac1435858d8f050d616363c458989722f2b08622373c5ca1094bcb2b08622373,0xcc53103356b314c40cd5acca8282e2d7346880d4f4d11158b918f1a1a81ab8c748d111ac69d234446b1a,0xc1435858d8f3062a23c8dc5aa2046bd316a8811af4c4475074e8b111d41d3a2c5aa2046bd32748819574,0xce9110ba16b2748819574ccaa202abd332a880aaf4cd52202d5d33a0c40e95ace83103a56b0662a1cc8d,0xc1570895666e68c054d58b02c59ab40f0a8b819d54ca9818a62cf1684a14c5dcc2948af2872a606298b3,0xa222f16255b2748819574c9d220655d316a0a198b5cd52202d5d3055c225599d0a158ab18f442b234ad1,0xcd52202d5d3354880b574c1570895667354880b574cd52202d5d332a0a0b8b5c85708b1667066a815ccc] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_46s1 : Span p3_46 3 6 11 :=
  batch _ _ _ _ #[
0xc1435858d8f314c40cd5acc53103356b050d616363c1435858d8f3222a2668dc5aa2046bd3111d41d3a2,0xc84358c8d8f036262cc8bc5aa2046bd31162625c8bc5aa2046bd3050d616363cd18282e2d73460a0b8b5,0xa222f16255a959c065598c458989722f3460a0c6b5cac21888dcf050d616363c1435858d8f4443a34655,0xcc53103356b314c40cd5aa585315287ae21385ea14d19150d598b050d6163637423310a57b4645435662,0xc1435858d8dd234446b1ad02748a9e872a606298b3d19a10a63cb2b08622373c686a06ae331a1a81ab8c,0xd19a10363cb32a880aaf4ccaa202abd316a8811af4cea22029dd33a8880a774cea22029dd33a8880a774,0xcc43502f58b1a8381ea54c84ac89734732a880aaf4ccaa202abd3466840d8f2ccaa202abd3466840d8f2,0xd19a10363cb440d60e563d103583958f0a9c222b99c152e078d53466840d8f2c152e078d53466840d8f2,0xc2a7088ae673460a0b8b5] 66 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_46s2 : Span p3_46 3 11 16 :=
  batch _ _ _ _ #[
0xcc2948af2870a6262e88bd19a10363ca505e4439aac99828662d62a3166e503c99828662d73a4442e85a,0xcd18282e2d73460a0b8b59417910e6aa505e4439aace9110ba16b3460a0b8b5d19a10363cb3460a0b8b5,0xc8c158ca98e1a1666642bc8c158ca98f15606252b3c8d818b0acf4283a33855cc18a88f2365c88642973,0xcca8282e2d732a0a0b8b5cca8282e2d7332840caf2c8c158ca98f0662a1cc8dd02ac8d63470662a1cc8d,0xc540e8731572303a1cc55c5c1507718b3a0c40e95ac14ac8b33473a0c40e95ac6a0e07a952521e4439aa,0xc147484ee87051d213ba1c5ca1086bcb30a522bca1c540e88f1571503a23c55c152e078d53054b81e354,0xd023582b58f332840caf2d023582b58f346880d4f4d023582b58f408d60ad63ce83103a56b3a0c40e95a,0xcca8282e2d65c88642973c8c0e87315716a0a198b5c4571094e6b346880d4f4cd1a20353d34a0a63294b,0xd2a2182a5cf310d40bd62cc43502f58b236062c2b3c5c1507718b421d40bba2d087502ee8b32a0a0b8b5,0xc540e88f1574a8860a973] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_46s3 : Span p3_46 3 16 21 :=
  batch _ _ _ _ #[
0xc84ac89734732a880aaf4ccaa202abd3466840d8f2c98948d5a871503a1cc55c99828662d71503a1cc55,0xcca1288b1773a4442e85ac2a7088ae673460a0b8b5d19a10363cb2303a23c55c8c0e88f1572303a23c55,0xc147484ee87466840d8f2c5a128531765588644573c99828662d73222a2668dc99828662d7460d431762,0xcc1aa0ab3331505616a63c5a828662d71728421af2c847486ae87211d21aba1cd18282e2d73460a0b8b5,0xcca8282e2d732a0a0b8b5cca8282e2d7051d213ba1c147484ee87051d213ba1c0d710b0e6b332840caf2,0xd0175035e8b32a880aaf4ccaa202abd332a880aaf4c0d710b0e6b16a8811af4c8c0e87315652b0642b33,0xc847486ae872660a216b5d0175035e8b1503a23c55c296a0a9e33310d40bd62cc43502f58b405d40d7a2,0xce83103a56b30a522bca1cca1288b1773460a0c6b5ccca1032bcb2a1c22a999c5ca1086bcb1728421af2,0xc147484ee871684a14c5dcd182831ad7405d40d7a2] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_46s4 : Span p3_46 3 21 27 :=
  batch _ _ _ _ #[
0xc8c158ab18f1503a23c55c5581894acf310d40bd62959c1115ccb1505615c6394179111eab1505615c63,0x956219115cf306a82acccc540e88f1574a8860a973d2a2182a5cf310d40bd62cc43502f58b4a8860a973,0xc5581894acf3a0c40e95ace83103a569d330443b32c541585a98f1505616a63ca8708aa6674a0a63294b,0xd087502ee8b1505615c63d02748a9e871505615c63c686a06ae3346684298f2cea22029dd33a8880a774,0xd087502ee8b3a8880a774c541585718f3a8880a774cea22029dd33a4442e85acc43502f58b466840d8f2,0xc458989722f440d60e563d103583958f314c40cd5acc53103356b4a8860a973d2a2182a5cf4a8860a973,0xc1d3108756b154381dc54d0175035e8b40ab2358d1c84ac8d2b47322a82e4ccccca1032bcb405d40d7a2,0xcc8aa0b93330a5c42999ad19a10363cb2a606298b3d103583958f052b226ad1d19a10363cb314c40cd5a,0xc550e077153346880d4f4c847486ae87332840caf2d2a2182a5cf4a8860a973c541585a98f314c40cd5a,0xc147484ee87051d213ba1cc53103356b32a0a0b8b5cd11289917732a0a0b8b5] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_46s5 : Span p3_46 3 27 33 :=
  batch _ _ _ _ #[
0xcd1a20353d1e54c054d58c5d1109716b3444a2645dcca82831ad716a0a216b5cd112899177334442cc5a,0xd15218315cf454860c57377222109dd31162625c8bc99128d11771744425c5acd1128991772644a3445d,0xc8c0e88f1572303a23c55cd0948b9a8732a880aaf4d19a10363cb454860c573c540e873157454860c573,0xd15218315cf3a4442e85ad15218315cf2748819574ca82e0c5d53354880b574d19a10363cb2303a23c55,0xc5ca1086bcb16a0a198b5c5a828662d716a0a198b5cd52202d5d3354880b574c29710a666b2a606298b3,0xcca8282e2d732a0a0b8b5cca8282e2d7115a81d58cd05298d152f332840caf2b814e177053035a82b58c,0xcc43502f58b405d40d7a2ccaa202abd33460a0c6b5c8c0e873157442b22e8d1d0175035e8b454860c573,0xc9982885ad7454860c573d023582b58f408d60ad63d0175035e8b354880b574d15218315cf310d40bd62,0xcd52202d5d31684a14c5dcd182831ad7211d21aba1cd182831ad73460a0c6b5d0175035e8b405d40d7a2] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_46s6 : Span p3_46 3 33 36 :=
  batch _ _ _ _ #[
0xc8c158ab18f1a1c421b9ac6871086e69d08cc4295ec8c0e8731571505615c63c1c3506758b2748819574,0xd15218315cee310654a33cd52202d5d31505615c63c6871086e6b310d40bd62cc43502f589915687342c,0xd087502ee8b070d419d629487910e6ab32a0a0c6b5c198a87323732a0a0c6b5d15218315cf3062a23c8d,0xc541585718f310d40bd62cc43502f58b466840d8f29422f111d5b055c225599c15708956671503a1cc55,0xd087502ee8b2303a23c55] 34 (by decide +kernel)

private theorem p3_46Good : Good p3_46 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_46s0 (joinSpan p3_46s1 p3_46s2)) (joinSpan (joinSpan p3_46s3 p3_46s4) (joinSpan p3_46s5 p3_46s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_47s0 : Span p3_47 3 0 6 :=
  batch _ _ _ _ #[
0xc8d0e0771530a5c42999ad0a1585a98f406a63588bc858c873547031d41d3a2c458985352f1162614d4b,0xd1a228463d71162614d4bce98102e5cb3a6040b972ce98102e5cb4443a33855d0a1585a98f405aa1398d,0xc6a818465cf1aa0611973d111585a98f1aa0611973d1a228463d74688a118f5c99a2066ad3232862c2b3,0xc54a18b0ace9c9c062b98ccd110b316b0362614d4bd182a8d1337216321cd51c5d11097169a1a9875684,0xb8a70152e634285616a63c8d0e077153074a815cccd027484ee870362614d4bd0a1585a98f4285616a63,0xd1a228463d74688a118f5c858c873547216321cd51d1a228463d7216321cd51c8d0e0771531162622d4b,0xc5d110b316b031d41d3a2c142e898b57441d213ba1c6871086e6b234381dc54c8d0e0771530362614d4b,0xce98102e5cb3a6040b972c0d8988b52f216321cd51c1d2a057333234381dc54c8d0e0771530a5c42999a,0xd111585a98f1aa0611973d086a851e371aa0611973ce98102e5cb3a6040b972ce98102e5cb3a6040b972,0xd111585a98f0a5a813b8cc296a04ee33322540e762d086a851e37050ba262d5d111585a98e889e2d09a9] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_47s1 : Span p3_47 3 6 12 :=
  batch _ _ _ _ #[
0xd111585a98f4283a34655d0274855e871162622d4bcc52a0ab333056321cd51d111585a98f232862c2b3,0xc0c75074e8b031d41d3a2c158c873547056321cd51c296a04ee331162622d4ba0bd11b846b1162622d4b,0xce98102e5cb3a6040b972ce98102e5cb3a6040b972ce98102e5cb3a6040b972cd0b089aa67314a82accc,0xc2a2e0a7353234382e654cca1288b1772668819ab4c99a2066ad31543835654c688985a52f1a2261694b,0xc199506758b1a2261694bcd1a202ead3035a82a78caa02f1a235b346880bab4cd1a202ead31684a14c5d,0xccd81031dcb342c22e899c0c75074e8a560ac858cec199506758b0665419d62ca88c87a5472a2321e951,0xd0a1585718f4285615c63ce9110ba16b031d41d3a2d0a158ca98f306540bd62c8d0e0d59531a2261694b,0xd016a84e637441d213ba1c5a128531771684a14c5dc5a12853177234382e654cc2b08b32670a6261694b,0xd1a228463d74688a118f5d18350c6b8b1760421772d1a228463d7460d431ae2c298985a52f0a6261694b,0xb03391d03ab306540bd62a585315287b336040c772ccd81031dcb342c226a99c6a818465cf1aa0611973] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_47s2 : Span p3_47 3 12 18 :=
  batch _ _ _ _ #[
0xc45710b0e6a10f2ab310dd0a1585a98f070d429ce2c6a0e0ce9533a0a82e4ccd016a84e637405aa1398d,0xd1a228463d74688a118f5d1a228463d74688a118f5c6a0e0ce9532360622373c152e0b8b532360622373,0x7503a1193b3054b82e2d4c8c158ab18f0aa321e951c2a8c87a547405d40bba2d1a228463d74688a118f5,0xc540e88f15742a860cab3d0a1585a98f4285616a63cd0b08ba267214b8352d48b3229883d7409d213ba1,0xd1a228463d74688a118f5d1a228463d74688a118f5d102e83a357310aa22ccdd0aa1832acd8a5685e42c,0xc99128d117742a860d8b3cc42a88b33742a860d8b3c2a8c87a5470aa321e951d1a228463d74688a118f5,0xcd4228313d73508a0c4f5c0c6a8716371560614373c296a04ee331a2261694bc688985a52f1a2261694b,0xc5581850dcf2a2321e951c8d81888dcf346880bab4ca88c87a547405d40bba2cd4228313d706ac22cc99,0xc152e0b8b53031aa1c58dc8c158d518f42a860cab3c0c6a8716370665419d62c84748756871a2261694b,0xc8d81888dcf115c42539ac8d81888dcf306540bd62] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_47s3 : Span p3_47 3 18 23 :=
  batch _ _ _ _ #[
0xce98102e5cb3a6040b972ce9110ba16b1a1a813b8cc6a0e0af153460d431ae2c9c228853d71560614373,0xcc1aa0af233460d431ae2d022e8333572360622373d11a18362ce505e4439aacd4228313d73a6040b972,0xca90e0af153150562e463d0aa18362cf0aa321e951c0c6a8716371a1a813b8cd18350c6b8b0665419d62,0xca88c899d473a4442e85acc42a88b337035c42539ac19aa077233066a81dc8cc19aa077233306540bd62,0xc1c2a853337310d40dce2c298985a52f2360622373ce98102e5cb1560614373ce98102e5cb421d40d7a2,0xd086a851e37310aa22ccdcd1a202ead34688a118f5d1a228463d74688a118f5c1c2a8533373a6040b972,0xcc43503738b0a5a813b8cc1c2a853337346880bab4ce91109a96b346880bab4c541585718f322540e762,0xc98b08d62672a23233951d11a1832acf2a23233951d111585a98f409d2157a1d0274855e86540bc458d6,0xd102e83a357405d40bba2d017502ee8b23606223739502f11635b405d40bba2] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_47s4 : Span p3_47 3 23 28 :=
  batch _ _ _ _ #[
0xd016a84e637446860d8b3ce98102e5cb3a6040b972ce98102e5cb16a88296b4c8d81888dcf310aa22ccd,0xce82a0b9332885e4589aacd0b089aa67446860d8b3d016a84e6370a6261694bc298985a52f405aa1398d,0xc29710a666b405aa1398dc158c899d45dc60443972c29710a666b070d429ce2c1c350a738b032a625c8b,0xd017502ee8b405d40bba2c99a2066ad30aa321e951c456a055e33310d40dce2c29710a666b405aa1398d,0xcd1a202ead3405d40bba20a62ecc0b57336040c772c2971086e6b035a82a78cc8c158ab18f115a81578c,0xd0aa1832acf42a860cab3d0aa1832acf035a81578cca88c87a5471760421772c6a818465cf1aa0611973,0xc1c2a853337440ba0e8d5d027484ee871a1c42999ad027484ee87336040c772d102e83a357310aa22ccd,0xc6871086e6b42a860d8b3cc42a88b33742a860d8b3d0aa18362ce8316654c2bc8c0e8731570aa321e951,0xc44a98b322f070aa14ccdca82e0c6b53032a625c8bcd112899177336040c772] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_47s5 : Span p3_47 3 28 34 :=
  batch _ _ _ _ #[
0xc8474875687211d21d5a1c858c873547421d40d7a2cd4228313d7322a82e68ca84c59d540f421d40d7a2,0xc458985352f0a5a813b8cc158c88f547322540e762c458985352f074a815ccccc895039d8b322540e762,0xc6a818465cf346880bab4c8474875687216321cd51c858c873547322540e762c58aa0d5a330a5a813b8c,0xd102e83a357446860cab3d102e83a357440ba0e8d5c6a818465cf322a82e68ccd1a202ead3346880bab4,0xd017502ee8b3508a0c4f5d017502ee8b2163223d51d102e83a3545c5a883b8cc14748756873508a0c4f5,0xc1474875687314a82acccc158c873547446860d8b3ccd1109716b2708a214f5d017502ee8b2163223d51,0xd11a18362cf2163223d51c858c88f54732a880d6b4c1d2a0573333508a0c4f5cd0b089aa67150562e463,0xcd4228313d73508a0c4f5cc2b08972672708a214f5d017502ee8b446860cab3c99a2066ad3031aa1c58d,0xc0d6a055e330665419d62c199506758b0665419d62cd1a202ead31684a14c5dcd4228313d70a8b829cd4,0xcc19502f58b306540bd62cc19502f58b1a1c42999ad08a98d622f336040c772d0aa1832acf1a2261694b] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_47s6 : Span p3_47 3 34 36 :=
  batch _ _ _ _ #[
0xc14748756873508a0c4f5d022e833357408ba0ccd5c0d6a055e33408ba0ccd5ce9110ba16a885e4589aa,0xb8b811705cb0665419d62c199506758b0665419d62d110e8ce156505e4439aacd4228313d7115a82a78c,0xcc19502f58b306540bd62cc19502f58b066a81dc8cc6871086e6b336040c772d0aa18362cf306a82bc8c] 24 (by decide +kernel)

private theorem p3_47Good : Good p3_47 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_47s0 (joinSpan p3_47s1 p3_47s2)) (joinSpan (joinSpan p3_47s3 p3_47s4) (joinSpan p3_47s5 p3_47s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_48s0 : Span p3_48 3 0 7 :=
  batch _ _ _ _ #[
0xd110e83a357454860c573c1ab0852e6604cdc531668133714c59b1702a14ccdc6a0e0c6b53045ca1685d,0xccd0a0b93332a606298b39591911a3ab112a614b8bd110e83a357454860c573d15218315cf4443a0e8d5,0x9722190a5cf112a614b8bc44a9852e2f212b21cb91d15218315cf212b21cb91d023582b58f408d60ad63,0xc0ca988ae2f464540dce2c50ae074e53464540dce2c50ae074e53142b81d394c0ca9852e2e5c88642973,0xc2c2988b52f4443a0e8d5c1ab0852e67074a81674cc1d2a059d33045ca1685dc117285a177406a62a98b,0xc1d2a059d33074a81674cc55620559d25588644573d1d21031dca98b0650b33c9d80895ac7474840c772,0xc1d2a059d3220cdc5a166c55620559d31558815674d1d21031dcb112a614b8bc1d2a059d33074a81674c,0xd2a2182a5cf4a8860a973d2a2182a5cf4a8860a973d2a2182a5cf4a8860a973959191133ab06ac215999,0xc817288b1771622a1e88dc588a87a23706ac214b99c1ab0852e67045ca14c5dc6a6204e9d3050d616363,0xc540e898b571503a262d5d08a98aa62eb39086a634b9a0615ab131622a1e88d] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_48s1 : Span p3_48 3 7 12 :=
  batch _ _ _ _ #[
0xc8c0e898b57262521eaa1d29610ae1cb306c42999ac55620751d3155881d474d29610ae1cb3b08423372,0xc989487aa87155881d474c2a2e02f5530a8b80bd54c2a2e02f5530a8b80bd54c2a2e02f5532a606298b3,0xc119583728f046560dca3cec2108cdcb046560dca3c1ab0856667262521eaa1a5e421558d306ac215999,0xc1ab0852e67045ca14c5dc1172853177141ca1685dc507285a177050d616363c540e898b573b08423372,0xd10ac8ae6472b08622373c0aae02ee5302ab80bb94c0aae02ee5306ac214b99c1ab0852e6706ac214b99,0xc55620559d3406a62a98bc55620559d31558815674cac21888dcf2b08622373a5ad015746284ccc5415e,0xc55620559d3074a81674cc19b103666b066c40d99ac4272853177074a81674cc1d2a059d331558815674,0xc1ab085666706ac215999c1d2a059d33074a81674cd0d610b19cb1558815674d0d610b19cb06ac215999,0xc152e039d53046560dca3] 66 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_48s2 : Span p3_48 3 12 17 :=
  batch _ _ _ _ #[
0xc447507718b3302a22ccdc447507718b440d60e563d103583958f066c40d99ac19b103666b1a98813a74,0xd103583958f0b0a622d4bc0aae02ee53440d60e563c0aae02ee53440d60e563c447507718b074c42635a,0xcc1b10a666a3c81a62cc5c6a6206a9d302a560eaa3c6a6206a9d31a9881aa74c19b103666b066c40d99a,0xc58aa075633066c40d99ac1d31098d6b212b21cb91c0ca988ae2f0a8b80bd54c84ac872e470a8b80bd54,0xc58aa075633342c225599c119583728e5c88642973cd0b0895667074c42635ac14ac88ee47221ca2645d,0xd2a2182a5cf236062c2b3c50728991774a8860a973c119583728f440d60e563c6c6108e9cb464540dce2,0xcc2b088ae64558b846754cc2b088ae665283c44ad6a4459a870af10ab819b94cea8088eac710ab819b94,0xc0a9583aa8f1a9881aa74c0aae02ee5302ab80bb940e6351c1d8b30ac222b99c0a9583aa8f02a560eaa3,0xd023582b58f0a8b80bd54d023582b58f0a8b80bd54c6c6108e9cb4642a344cdca9620ad1d3032a614b8b,0xd28298ca52f1622a1e88dc588a87a2374a0a63294bd023582b58f408d60ad63c2a2e02f5530a8b80bd54] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_48s3 : Span p3_48 3 17 23 :=
  batch _ _ _ _ #[
0xc989487aa87074c42635ac989487aa865470645533c0a7285a17706ac215999c989487aa865c88642973,0xd01a98b162f406a62c58bd01a98b162f262521eaa1d0a0e83a35715606252b3c1172899177109ca3285d,0xc1ab0852e67221ca3285dc6a6204e9d302a560eaa3c6a6204e9d31a98813a74c19aa055e33066a81578c,0xc2a2e02f55315606252b3d28298ca52f4a0a63294bc1ab0852e6702a560eaa318c4e973057442b22b991,0xd0a0e8333574283a0ccd5ca9620a99d34a0a63294b0e1b9181eab408d60ad63c2a2e02f5530a8b80bd54,0xc11ae035e531702a14ccdc0a7285a1770b0a622d4bc19aa055e33262521eaa1ca9620a99d34a0a63294b,0xd2a2182a5ce5670445732c19aa055e33066a81578cc5581894acf4283a0e8d5c8d818b0acf074c42635a,0xc6c6108e9cb4443a0ccd5d191503738b141ca1685dc1a948b9a87046560dca3c0ca9852e2f032a614b8b,0xc8d0e0b8b53066c40d99a9510f11635a5588644573cc88a8ce237141ca1685dd110e8333574a0a63294b,0xd110e83a357066c40d99ac550e0d4b5340ab22c791d110e83a35715438352d4c5c0a8533371702a14ccd] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_48s4 : Span p3_48 3 23 28 :=
  batch _ _ _ _ #[
0xc447507718b3302a22ccdc447507718b440d60e563d103583958f066c40d99ac19b103666b10ab819b94,0xc0aae02ee53322a82b58cc0aae02ee53440d60e563c0aae02ee53474840c772c152e039d53342c22c599,0xd1d21031dcb162a81d58cd1d21031dcb02a560eaa3053ba14c6b3262c225599c19b103666b066c40d99a,0xc44a9852e2f066c40d99aca9818a62cf112a614b8bc0ca988ae2f2a606298b3c84ac872e465443c458d6,0xc152e039d53342c225599c119583728f4a8860a973d2a2182a5cf4a8860a973d1d21031dcb221ca2645d,0xc14ac88ee472a43829cd4d1d21031dcb054b80e754c44a9852e2f474840c772c152e039d53464540dce2,0xcc2b088ae6727602256b1c152e039d53054b80e754aa02f16255b10ab819b94c42958c6a8f10ab819b94,0xd1d21031dcb074a81674cd1d21031dcb074a81674cc6a81886acf30ac222b99c0a9583aa8f02a560eaa3,0xd023582b58e3c50a63435d023582b58f1622a1e88dd1d21031dcb474840c772b9a061573134283a0ccd5,0xd1d21031dcb4283a0ccd5d0a0e833357074a81674cd023582b58f408d60ad63c44a988ae2f4642a344cd] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_48s5 : Span p3_48 3 28 34 :=
  batch _ _ _ _ #[
0xc989487aa8730ac22a999c989487aa8735602256b1d2a2182a5cf4a8860a973d2a2182a5cf4a8860a973,0xd0a0e83a35706ac215999c1ab0856667074a81674cd1d21031dcb314a83274cc1172899177054b80e754,0xc6a81886acf3302a22ccdd15218315cf02a560eaa3cc2b088ae6730ac222b99d15218315cf1a98813a74,0xd023582b58e82f446e11ad15218315cf4283a0ccd5c1ab0852e6702a560eaa3c6a0e0c6b53442b22b991,0xd0a0e8333574283a0ccd5d01750d598b405d435662d01750d598b408d60ad63c11ae035e53408d60ad63,0xc11ae035e534283a0e8d5d0a0e83a357206b829794c19aa055e330662a2668dce8310c656b334282e4cc,0xd0a0e83a3565c88642973ccc0a88b3373062a3468dc11ae035e53046b80d794c42728ca177262521eaa1,0x959191133ab1622a1e88dd191503738b2a43829cd4c55620751d3046560dca3d191503738b06a522e6a1,0xd15218315cf066c40d99ac5c0a853337454860c573ca90e0a7353141ca1685dd15218315cf2a43829cd4,0xd110e83a357066c40d99a0f2a61a9e1340ab22c791c19b103666b155881d474c55620751d3155881d474] 80 (by decide +kernel)

private theorem p3_48Good : Good p3_48 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_48s0 (joinSpan p3_48s1 p3_48s2)) (joinSpan p3_48s3 (joinSpan p3_48s4 p3_48s5)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_49s0 : Span p3_49 3 0 6 :=
  batch _ _ _ _ #[
0xa585a2788b31aa06298b3c6a818a62ce5283c4395688dcc1774431aa06298b380d599530af1aa06298b3,0xc81728d1177444560e563c45710b316b205ca3445dd022e82e657408ba0b995d022e82e657408ba0b995,0xd023582ae8f408d60aba3c2a2e066e53174281e54cc2a2e066e53235881d474c117285a177174281e54c,0xc4272853174d598885674c8d620751d31a83819d54d19a10363cb466840d8f2d19a10363cb408d60aba3,0xa5a981732a3334283354cccd0a0cd533466840d8f2c4272853177109ca14c5dc6a0e0675531a83819d54,0xd05298b162f414a62c58b15e2a215e33066a816accd0a1582b58f428560ad63d0a1582b58f428560ad63,0x815c595740f035c425c5a9423990a6af0662a2668dc1d2a075633408ba0b995c297109a96b466840caf2,0xd1915039d8b408ba0b995d022e82e657408ba0b995d022e82e657408ba0b995c6a818a62cf1aa06298b3,0xd022e831e57408ba0c795c2c2988ae2f0b0a622b8bc117285a1760571655d03aa039a80eaf0662a1e88d] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_49s1 : Span p3_49 3 6 11 :=
  batch _ _ _ _ #[
0xc6a6206a9d31a9881aa74c2a2e066e530a8b819b94c5415858d8f1505616363c5415858d8f035c425c5a,0xc5415858d8c558b845794c5415858d8f310d42b3a2c6a6206a9d31a9881aa74c842e870e571a9881aa74,0xc6a81886acf170541e3620d686999a17210ba23395c119583aa8f2a5881aa74c119583aa8f170541e362,0xcc4350ace8b1a9881aa74a988717621b1a9881aa74c6a81886acf1aa0621ab3c842e88ce57210ba23395,0xc1435854e8f050d6153a3c142e870e5717284252f2d28298aa62f310d42b3a2c6a6206a9d31a9881aa74,0xc427288b177029ca14c5dc1c35074e8b070d41d3a2c0a72853177029ca14c5dccc150ccd8b442b2358d1,0xc55620751d3155881d474c5ca1094bcb405d433a62c84358a8e8f306a832accc427288b177109ca22c5d,0xc5415858d8f1505616363c117285a177045ca1685dc0d7109716b1a9881aa740a17726299b310d42b3a2,0xccca1094bcb3a0a82a78cc5415858d8f045ca1685dc117285a1771505616363c5415858d8f035c425c5a] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_49s2 : Span p3_49 3 11 16 :=
  batch _ _ _ _ #[
0xc1435854e8f050d6153a3c5415858d8f332842c2f2c5415858d8e888e6509abca96206a9d3050d6153a3,0xc142e870e56865685662cc5415858d8ea621c5d886c119583aa8e961685662cc842e870e572a0b829794,0xc5415858d8f1505616363c2a2e066e531505616363c5415858d8f1505616363d28298aa62eb870468732,0xd28298aa62f332842c2f2c1435854e8f050d6153a3c5415858d8f1505616363ccca1094bcb1505616363,0xc5415858d8f1505616363159d111ac6b2a60621ab3c5415858d8f1505616363a5e421750d34a0a62a98b,0x94ac190accf031d41dc62c1d31094e6b2343833354c119583aa8f046560eaa3d28298aa62f210ba23395,0xc6a6206a9d31a9881aa74c6a6206a9d3466840d8f2d19a10363ca52b0642b3394ac190accf466840d8f2,0xc55818b0acf214b82b394c8d81894ace1790a54635c152e074e5306a521dca1c6a6206a9d3466840d8f2,0xcea1088b56702a560dca3d0a1582b58e5443c43956d0a1582b58f30a522bca1d0a1582b58f428560ad63,0xc0a9583728f02a560dca3] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_49s3 : Span p3_49 3 16 22 :=
  batch _ _ _ _ #[
0xd022e82e657221ca3445dc84ac8b33466a81656943d022e82e65715606252b3c81958c6a8f052b225cd1,0xc8d81894ace0ab1656b03ccd110d0d6b3222a3388dc6c0988b52f046560eaa3d103583568f408ba0b995,0xd023582ae8f23606252b3d023582ae8f408d60aba386acc17ac43334443435ad023582ae8f3222a3388d,0xc8d81894acf029ca14c5dc5581894acf10a5629ca3c6c0988b52f1a9881aa74c6a6206a9d31a9881aa74,0xd102e82e65702a560dca3d102e82e657236062c2b3c152e074e53109ca22c5dc1a94877287156062c2b3,0x95839111eab045ca1685dc6a6206a9d326252356a1c0a9583728f02a560dca3cea1088b5671622a1e88d,0x9510f10e55b460d40d7a28585715589b460d40d7a2d1835035e8b408d60aba3c8d81894acf205ca3285d,0x95839111eab440ba0c7958585715589b0b0a622b8bcea1088b566560e4447aac42958a728e0a5665682b,0xc19aa05ab3315606252b3c0a9583728f02a560dca3c4272853177428560ad6319a8697321702a560dca3,0xd1835035e8b066a816accc8d0e0ccd53460d40d7a2d1835035e8b26252356a1d19a1032bcb2a5881aa74] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_49s4 : Span p3_49 3 22 28 :=
  batch _ _ _ _ #[
0xc8d81894ace5670445732ccd110d0d6b141ca1685dc6c0988b52f031d41dc62c507285a17652b0642b33,0xc5581894acf10a5629ca3c507285a177464540e762d28298aa62f111d42bc62c507285a177111d42bc62,0xd0a1582b58f428560ad63c0a9583728f236062c2b3cea1088b567174442635ac152e074e53029ca14c5d,0xc507285a177154381e354c152e074e53066a816acc85e429710d72065631aa3c0a9583728f30a522bca1,0xc2c2988ae2f440d60d5a3c119583aa8f4a0a62a98bd19a1032bcb214b82b394cc1aa0cab332343833354,0xd022e82e657141ca2645dc6a818a62cf440d60d5a3d103583568f1aa06298b388bc29684d7141ca2645d,0xd022e831e56157305dd10c2c2988ae2f0b0a622b8b853c294c4d7408ba0b995d022e82e6565670445732,0xca9818a62ce1156654c2bc0d7109716a674145cd42c0d7109716b2a606298b3d022e831e572a606298b3,0xc6a818a62cf2a0b8297940539717429b1aa06298b3d111583958f460d40d7a2d1835035e8b0b0a622b8b,0xc588a899a37460d40d7a2c6a818a62cf1622a2668dd111583958f342522e6a1d1835035e8b460d40d7a2] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_49s5 : Span p3_49 3 28 35 :=
  batch _ _ _ _ #[
0xd111583958e5283c447560754e1af0531622a1e88dd111583958ee681856744d111583958f1a9882a674,0xd111583958f3a0c42999ad111583958eb58c0a5398d111583958f3a0c42999ace8310a666b1622a1e88d,0xd05298b162f414a62c58bce9110c656b408d60aba3c5d0a0795332744234559d102e831e57440ba0c795,0xa98871b1a1b10a5629ca3d102e831e57428560ad63d0a1582b58f428560ad63d05298b162f460d40d7a2,0xd19a1032bcb466840caf2c0a9583728f02a560dca3c427285317622f0a5a135c6a0e06755302a560dca3,0xd05298b162f046560eaa3c55620751d3460d40d7a2c55620751d3155881d474d1835035e8b466840caf2,0xd023582ae8f408d60aba3d102e82e657440ba0b995d102e82e657074a81d58cd1835035e8b066a816acc,0xd0a1582b58f428560ad63c507285a177464540e762ca90e0c5d53111d42bc62c507285a177235881d474,0xd19a1032bcb074a81d58cc0a9583728f2744226559c0a9583728f434263454bd102e82e657440ba0b995,0xc119583aa8e5283c44756c119583aa8f155881d474d19a1032bcb235882b474] 78 (by decide +kernel)

private theorem p3_49Good : Good p3_49 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_49s0 (joinSpan p3_49s1 p3_49s2)) (joinSpan p3_49s3 (joinSpan p3_49s4 p3_49s5)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_50s0 : Span p3_50 3 0 6 :=
  batch _ _ _ _ #[
0xd1035858d8f440d6163638c2a7195a1b115c425c5a81aa71b1a1b1423a1c395d0a628519d74298a14675,0xd0a0e839c574283a0e715d0a0e839c574283a0e715c5895074e8b2a5882b474c0d710b316b30a522a7a1,0xc2a2e0675530a8b819d54c2a2e0675530a8b819d54c9ca0872ac706ac22cc99c158c8b1e472223a1c395,0xd023582b58f408d60ad63d023582b58f408d60ad63d023582b58f408d60ad63d023582b58f408d60ad63,0xd110e839c57115c425c5ab99421558d342a860cab3cac218855cf454322bd118195715589b2223a1c395,0xd110e82f4572a0b81e354d0d610b19cb074a81674ccac218855cf454322e71194a0f10ec5b162541d3a2,0xd2a218465cf4a88611973d2a218465cf4a88611973d110e82f4572a0b81e354c508e870e574443a0bd15,0xd110e839c5714256153a3c5095854e8f4443a0e715d110e839c5714256153a3d2a218465cf4a88611973,0xc117285a1771423a1c395d11a18362cf4283a0e715d1035858d8c545cc8585ed1035858d8f2223a23395] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_50s1 : Span p3_50 3 6 11 :=
  batch _ _ _ _ #[
0xd023582b58f408d60ad63d116284e1d74458a13875c44750ce98b4458a138758833716859b0a8b819d54,0xd2a218465cf4a88611973d2a218465cf4a88611973d1d21031dcb474840c772c508e870e57408d60ad63,0xd110e82f4574443a0bd15d1d21031dcb4443a0bd15d1d21031dcb474840c772d2a218465cf4a88611973,0xd190a859c37070d41e362d11628519d7262521d5a1d11628519d710a5611ba3c852e06755310a5611ba3,0xc4295846e8f10a5611ba3c989487568710a5611ba3c0a9582ae8f02a560aba3c457109716b221ca2645d,0xc0a9582ae8f070d41e362c858c895e47070d41e362c1c35078d8b1503a1e315c852e0c5d529883c58b16,0xc852e067553314c421d5ac852e0675531503a1e315c1435858d8f050d616363c0a9582ae8f02a560aba3,0xcec2108cdcb1503a1e315d150c8af447454322bd11c1435858d8c54666445abc852e067553314c421d5a,0xc8c0e878c573b08423372] 66 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_50s2 : Span p3_50 3 11 17 :=
  batch _ _ _ _ #[
0xc198a8716372a23223b91c428e885e5706a52157a1d0a628519d706a52157a1d0a628519d7162a81ea8c,0xc1d3103356b3b08423372c0a8e831e5702a3a0c795d1aa08b1ac706a52157a1c1a94855e87162a81ea8c,0xd023584758f029ca14c5dd023584758f15286252b3d023584758f408d611d63d29098b942f1a1c426a5a,0xd0d610b19cb046560d5a3d29098b942f109ca22c5dc8c0e878c57310d433362c8c0e878c57029ca14c5d,0xcc88a889e374458a13875d116284e1d7162a83568cc818e8666571503a1e315c1435858d8f050d616363,0xc1435858d8f050d616363d190a859c37214b819d54c0a9582ae8f02a560aba3c0a9582ae8f1a98813a74,0xd190a859c37050d616363c1435858d8f434262ad0bd2a218465cf3062a2278dcc53108756a888bc58956,0xc1c35078d8b070d41e362cc53108756b06a52157a1c1c35078d8b162a81ea8cc1d3103356b066540d7a2,0xd023584758e8654c5581ec1d3103356b342c234a99c1a94855e87162a81ea8ccd0b089aa67322a833a8c,0xae1c11a23cb235882a674ae1c11a23cb1558815674cc52a0c9d33074a81674cc2a2e0675530a8b819d54] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_50s3 : Span p3_50 3 17 23 :=
  batch _ _ _ _ #[
0xc0a8e82e657050d616363c1d2a059d334a88611973d2a218465cf1558815674c19aa07723310a3a19995,0xd023584758f408d611d63d023584758f408d611d63d023584758f408d611d63cc1aa0af233232862c2b3,0xc428e885e574548614373cc2b0897267342522b5a1cc1aa0d5a33272821cab1c9894875687262521d5a1,0xd023584758f408d611d63d103583958f1b18423a72c588a871637214b833354d0a628519d74298a14675,0xd023582b58f408d60ad63d023584758f408d611d63d023584758f408d611d63d023584758f408d611d63,0x8133714c59b045ca14c5dd023582b58f408d60ad63d023582b58f408d60ad63d023582b58f408d60ad63,0xd110e82f4574443a0bd159aa0595ac0f205ca22c5dccc0a8cd4373302a3350d898a7195a1b210d631563,0xc0a728531772063a21795c0a9582ae8f02a560aba3c0a9582ae8f02a560aba3d0aa1832acf050d60e563,0xd023582b58f0a8b80bd54d023582b58f0a8b80bd54d023582b58f2063a21795c198a851e374a8322bd11,0xc687109a96b0463a0c795c118e831e570a8b80bd54] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_50s4 : Span p3_50 3 23 28 :=
  batch _ _ _ _ #[
0xc687109a96b066a81dc8cc19aa07723306a52157a1c84358c558f1702a1e50dc8c6288d1d7066a81dc8c,0xc9ca0872ac7408d60ad63d023584758f408d611d63c2a2e039d530a8b80e754c0a8e831e5702a3a0c795,0xd1835039d8b0a8b80bd541ab3119856b0463a0b995d023582b58f408d60ad63c2a2e02f553408d60ad63,0xc2a8c8ae6466ac8463172cac0c8cec461ac645e12ac588a851e371b18423a72c428e86665710a3a19995,0xc852e0675531b18423a72cc2b08d626730ac235899d110e82f4574443a0bd1585e429710d730ac235899,0xc0c7507a98b440d60e563d103583958f30654297a2d103583958f440d60e563d103583958f440d60e563,0xd103583958f4a88611973cd4a088eac7115c425c5ad103583958f440d60e563c19aa0b9a33214b819d54,0xd103583958f440d60e563d11a18362cf446860d8b3c0c7507a98b031d41ea62cd0948ad687272821cab1,0xd103583958c286e6708abc1d3103356a56704458f2d103583958f446860d8b3d11a18362cf4283a0e715] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_50s5 : Span p3_50 3 28 33 :=
  batch _ _ _ _ #[
0xc2a2e0675530a8b819d54d11a18362cf4283a0bd15d0a0e82f4574283a0bd15c29710ba16b3528223ab1,0xd110e82f4574443a0bd15d1d21031dcb0463a0b995c50728d1177474840c772c989487568656704458f2,0xc152e039d534a88611973d110e82f457440d60e563c1ab08ba2674443a0bd15d1d21031dcb474840c772,0xc0a7285a17710a3a19995d1835039d8b460d40e762d110e82f4574a88611973d1d21031dcb440d60e563,0xd1835039d8b054b80bd54c9ca0872ac702a3a0b995cd4a088eac7109ca3285d0f1529d1077460d40e762,0xc143583958f10a5611ba3c818e8666569883c58b16c0a7285a177029ca1685dc152e02f553054b80bd54,0xc1d3103356b460d40e762c0a9582ae8f2a0b831754cac218855cf0463a0b995c118e82e657162a83568c,0xd110e839c5730654297a2c852e0675534443a0e715d110e839c5730654297a2cc8aa0b9a33045ca1685d,0xc1d3103356b066540d7a2c8c628711d7066540d7a2c1995035e8b434262ad0bc546288d1d730654297a2] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_50s6 : Span p3_50 3 33 36 :=
  batch _ _ _ _ #[
0xcd0b089aa67446860d8b3d11a18362cf446860d8b3d0a0e839c574283a0e715cc53108756b446860d8b3,0x8833716859b4283a0bd15d0a0e82f457235882a674d11a18362cf4283a0e715c143583958f1702a1e50d,0xd1d21031dcb4443a0bd15c55620559d31518a1c475cd0b08d2a665286642d2bc118e82e657408d60ad63,0xc1d2a059d33050d60e563c5c0a879437066a81dc8cc0a8e82e6573a44429d1ad110e82f4574443a0bd15,0x5c5717509b050d60e563] 34 (by decide +kernel)

private theorem p3_50Good : Good p3_50 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_50s0 (joinSpan p3_50s1 p3_50s2)) (joinSpan (joinSpan p3_50s3 p3_50s4) (joinSpan p3_50s5 p3_50s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_51s0 : Span p3_51 3 0 6 :=
  batch _ _ _ _ #[
0xcc2948a9e870662a1c58dc0d7109716b0662a1c58dc508e870e57031d41ea62d1a14859d874685216761,0xd111583958f444560e563c6a620a99d32223a23395c6a620a99d3444560e563c1a94855e873062a2358d,0xd1aa08563c746a82158f1c0d7109716b109ca3285dd0a6284e1d74298a13875d0a6284e1d74298a13875,0xc0a7285a177205ca3445dd111583958f322542b3a2c0a7285a177029ca1685dd111583958f444560e563,0xd2a2182accf4a8860ab338195715589b035c425c5ad05298ab42f414a62ad0bcc18a889e37070aa1e50d,0xc1a94855e87066a816accc5095854e8f414a62ad0bd2a2182accf4a8860ab33d2a2182accf4a8860ab33,0xc19aa05ab33414a62ad0bd05298ab42f14256153a3c1a94855e87066a816accd19a1032bcb0a62622b8b,0xc88ae0b8b53029ca1685dcea108ca56714256153a3c19aa05ab33466840caf295e21115ccb066a816acc,0xd0a1582b58f036262558bc9d10899566508e642d2bc0c7507a98b4458a14675d11628519d74458a14675,0xd0a1582b58f428560ad63d0a1582b58f428560ad63] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_51s1 : Span p3_51 3 6 11 :=
  batch _ _ _ _ #[
0xd15218354cf045ca14c5dd15218354cf235882b474c45898b162f4685216761c0d8989562f4685216761,0xa83331a847b454860d533d1aa08563c746a82158f1c55620751d3174281e54cd0a6284e1d74298a13875,0xc4295846e8f10a5611ba3d11628519d710a5611ba3c19aa057333454860d533d15218354cf306a82accc,0xc118e831e574a88611b33d1aa0852bc746a8214af1c4295846e8f10a5611ba3d11628519d74458a14675,0xc1995035e8b066540d7a2cd0948ad68733284252f2d1aa0852bc71505616363c118e831e570463a0c795,0xc142e878c574685216761c588a871637221ca2645dc298988ae2f206b831ad4c1995035e8b066540d7a2,0xd0a6284e1d73222a2358dc1d3103746b074c40dd1ad1a14859d873222a2358dc8872899177074c40dd1a,0xca96206a9d346a82158f114a9990a6af170541e362d1aa08563c7206b831ad4d0a6284e1d71505616363,0xc1d3103746b02a3a0b995c0a8e82e6571622a1c58d] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_51s2 : Span p3_51 3 11 17 :=
  batch _ _ _ _ #[
0xd1aa0852bc71a9881aa74a195319507b1a9881aa74d182a859c37460aa1670dccca1094bcb1a9881aa74,0xc1d3103746b074c40dd1ad182a859c37074c40dd1ad2a21846ccf4a88611b33d2a21846ccf4a88611b33,0xc68898aa62f1a2262a98bc6a6206a9d31a9881aa74cc5310a746b1a9881aa74c142e878c57442b22e8d1,0xd1aa0852bc7074c40dd1aa8bc21742d31a9881aa74d2a21846ccf4a88611b33d2a21846ccf4a88611b33,0xc19aa05ab331622a1478dc6a0e067553421d42e662c0a7288b177155881d474c0a7288b1773222a2278d,0xc588a851e374a88611b33cd5108d1567045ca14c5dcc88a889e36a870660ab3c588a851e37235882b474,0xb31419528ce888e650d2bc0a9582ae8f02a560aba3c588a851e36a631875684a531315057b066a815ccc,0xae6211a1ccb3544234559ae6211a1ccb306a832acccc1aa0cab33066a816acccc1aa0cab332744226559,0xc19aa0573333a44421d5ad2a21846ccf1505616363c55620ad1d3155882b474c19aa057333066a815ccc,0xc0a9582ae8f46a8214af1c68710ba16b3305433362] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_51s3 : Span p3_51 3 17 22 :=
  batch _ _ _ _ #[
0xd11628519d74458a14675d1521854ccf4548615333d1521854ccf4548615333d11628519d74458a14675,0xc1995035e8b066540d7a2d1521854ccf4548615333c118e831e574548615333d1521854ccf4458a14675,0xc81ae0a73520ace45e12ac1995035e8b02ab80dcd4c0aae0373534548615333d022e82f4570463a0c795,0xc14ac89ab441794a5681dc11ae037350bb320e6a88c588a8716374685216761d1521854ccf4548615333,0xc11ae03735310a3a19995d0a6284e1d74298a13875d1aa08563c746a82158f1c6a620a99d3046b80dcd4,0xcd0948ad687342522b5a1cea108ca56702a3a0b995c8d0e0ccd531622a1c58dd1aa08563c7046b80dcd4,0xc0aae037353046560d5a3c119583568e508e642d2bd1521854ccf234381e354c81958a568f460aa1670d,0x1542f10ec5a62c545e162cea1088b5671543833354c0aae03735302ab80dcd41a22e963457046560d5a3,0xc0aae037353046560d5a3c119583568f1a1c42e85ac0c7507a98b3a84222d59c550e0ccd534548615333,0xd022e82f457046560d5a3d022e82f457408ba0bd15c8d0e078d525788445732d022e82f45702ab80dcd4] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_51s4 : Span p3_51 3 22 28 :=
  batch _ _ _ _ #[
0xd0a1582b58f1622a1478dc297109a96b1622a1478dd08750b998b2a5881aa749502f115c5b3222a2278d,0xc588a851e372343833354c4295846e8f1a9881aa74c1172853177045ca14c5dc4272853177066a816acc,0xc19aa05ab3327282254f195839119cab4a8860ab33c8c6288d1d7066a815cccc19aa0573331622a1478d,0xca96206a9d3428560ad63d0a1582b58f306a832acccc1aa0cab33306a832accc9ca08953c727282254f1,0x95e21115ccb10a5611ba3c6a6206a9d310a5611ba3c19aa057333066a815cccca96206a9d3408ba0bd15,0xc0c7507a98b2a5882a674ca9620a99d3464540e762c507285a1774a8860ab33c1172853177306a82accc,0xc0a7285a17720656295a3d111583958e84ccc5511ec1995035e8a22c5c5a166c1995035e8b162a82e4cc,0xc1d3103746b460aa1670dc0a8e82e65702a3a0b995c0a7285a177029ca1685dd111583958f444560e563,0xc119583568f046560d5a3c42728ca17652b06458b3] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_51s5 : Span p3_51 3 28 33 :=
  batch _ _ _ _ #[
0xcc5310a746b444560e563c1a94855e87314c429d1ad111583958f444560e563c6a620a99d3314c429d1a,0xc119583568e62e84650f2c1d3103746b4685216761c1d3103746b074c40dd1ac119583568f046560d5a3,0xd102e839c543315c6b426c0a8e82e657466840caf2c298988ae2f440ba0e715d102e839c570a62622b8b,0xd2a2182accf4a8860ab33d102e839c57066a816accc19aa05ab331622a1478dcac218a54cf074c40dd1a,0xc1995035e8b066540d7a2cc18a889e374a8860ab33d2a2182accf4a8860ab33d2a2182accf4a8860ab33,0xa531315057b06a52157a1c1a94855e87066a816accc9ca08953c7141ca1685dc118e831e57464540e762,0xc1a94855e87066a816accd19a1032bcb2b08629533c1d3103746b35282254f1d19a1032bcb466840caf2,0x94ac19162cf036262558bd102e839c57454860d533c0a8e82e657454860d533d15218354cf066a815ccc,0xd102e839c57440ba0e715d1aa08563c746a82158f1d15218354cf046b80dcd4] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_51s6 : Span p3_51 3 33 35 :=
  batch _ _ _ _ #[
0xc1995035e8b02ab80dcd4c0aae037353428560ad63d0a1582b58f428560ad63d0a1582b58f428560ad63,0xd15218354cf045ca14c5dd0a1582b58f27442265599423990b4af031d41ea62c118e831e570463a0c795,0xd15218354cf046b80dcd4c507285a17662e84650f2cc2948a9e874685216761c817288b177046b80dcd4,0xc1a94855e861ce846c0f2] 26 (by decide +kernel)

private theorem p3_51Good : Good p3_51 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_51s0 (joinSpan p3_51s1 p3_51s2)) (joinSpan (joinSpan p3_51s3 p3_51s4) (joinSpan p3_51s5 p3_51s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_52s0 : Span p3_52 3 0 5 :=
  batch _ _ _ _ #[
0xd01a985662f1a83831ad4d01a985662f02a5616a63c88ae074e532360625473c88ae074e532360625473,0xc428e873157212b21cb91cea2202ead33a8880bab4cea2202ead3051d213d61d190a85a337051d213d61,0xc0a9585718f1a83829cd4d190a85a337212b21cb91d01a985662f406a61598bc55818b11cea843c688d6,0xd2a6084e5c74a98213971c55818951cf142b81d394ccc1503ab8b330540eae2a22399832af406a61598b,0xc50ae074e51d08cc4589ec147484f5870465616a63d01a9852e2f4a886298b3d2a6084e5c70465616a63,0xd2a6084e5c74a98213971c296a04f5330a5a813d4cd2a6084e5c70a5a813d4cc50ae074e53211d21ad61,0xc88ae074e53055c226559c5d0a0b9333032a614b8bcc8b1094e6b322c42539ad190a8533370465615c63,0xd1560851dc74558214771d1560851dc7035a81674cc88ae074e53066c42999ac88ae074e53440d62e2a3,0xcc1b103666b330540dce2ccc1503738b306c40d99acc1b1036669dc88843ab4] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_52s1 : Span p3_52 3 5 11 :=
  batch _ _ _ _ #[
0xc50ae074e534558214771d1560851dc74558214771c0d6a059d33035a81674cc428e873157035a81674c,0xc0d6a059d33035a81674ccc1b103666b308ca0cc9dcc1b103666b308ca0cc9dcc2328332771a83829cd4,0xcc1b1032e6b211d21ad61c847486b587142b81d394c19b1086e6b0465616a63d01a9852e2f406a614b8b,0xc0ca9852e2f032a614b8bc84ac872e47322c42539ac147484f586a78186e4c4c88ae0ace53306c40cb9a,0xa83331b027b222b82b394cd522035ad34642a14ccdd190a853337142b81d394c6a818aa1cf27488296b4,0xd01a985662f066c42999ac19b10a666b10ab819b94d190a85a3374642a168cdc14ac88ee47074a82e68c,0x75622115ad34642a168cdcc1b1036669a988a606b5c8d0e0d4b53306c40d99acc1b103666b02ab80bb94,0xc428e873157306c40d99a74cc110eccb212b21cb91d01a985662f406a61598bc428e873157035c42635a,0xd2a6084e5c74a98213971d2a6084e5c74a98213971d2a6084e5c74a98213971cc1b103666b308ca0cc9d,0xc0d71098d6b422a62c58bc11ae02ee5047a946c782c0c7502f58b031d40bd62] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_52s2 : Span p3_52 3 11 17 :=
  batch _ _ _ _ #[
0xc84ac872e47068ca0e89dd2a6084e5c74a98213971d2a6084e5c74a98213971d2a6084e5c74a98213971,0xce98108e9cb206b819b94cac6088d5c7206b819b94c14ac88ee47068ca0e89dc1a3283a2771aa062a873,0xd15218b0acf2223a1e855cac6088d5c7066c40cb9ac19b1032e6b2b18223571ce98108e9cb2223a1e855,0xcc2b088ae670a5a813d4cc296a04f5330a5a813d4cc296a04f5330a5a813d4cc11ae02ee53046b80bb94,0xd10ac8ae64702ab80bb94c0aae02ee533a8880bab4cea2202ead1c58d06e6a0c508e87a1573a8880bab4,0xc589507a98b406a62a98bc589507a98b3302a264cdc428e8731572b18223571c0a9585718f02a5615c63,0xc296a04f5330a5a813d4cc428e873157115c43435ac44a98b162f035c42635ac1a32833277032a62558b,0xce82a0cea33322c40cb9acc8b1032e6b068ca0e89dc1a3283a2770a5a813d4cc296a04f5330a5a813d4c,0xd08a985662f06ac214b99d08a985662f454862c2b3c1a3283a277068ca0e89dc1a3283a277032a62558b,0xc147484f5873065435662c147484f5874685216ae1cea2202ead33a8880bab4c0a9585a98c386e4607aa] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_52s3 : Span p3_52 3 17 23 :=
  batch _ _ _ _ #[
0xc1a32833277422a61598bc19950b998b2223a1e855c888e87a157422a61598bcc232887277032a614b8b,0xcc2328c627715438352d4ccc1503ab8b330540eae2c1a32833277068ca0cc9dc0ca9852e2f1423a33855,0xd2a6084e5c7322c40cb9ac11ae035e53162c421b9ac45710d0d6b162c421b9ac0d71098d6b308ca3189d,0xc447506758b111d419d62c447506758b111d419d62ccc1503738b068ca0e89dd2a6084e5c7330540dce2,0xcd03283a277031d40bd62d15218b0acf031d40bd62c81958ca98f15438352d4d15218b0acf0465616a63,0xc0aae035e53322c40d99a7503311627b032a614b8bd190a853337422a61598b660b91626ab210d631aa3,0xc447506758b111d419d62cd03283a277340ca0e89dc143583aa8f050d60eaa315a3a119ab32a1c232959,0xccc1503738b330540dce2c0aae035e5340ab22c791d02ac8b1e4740ab22c791c447506758b111d419d62,0xb917015a563330540dce2ccc1503738b330540dce2d02ac8b1e47031d40bd62c0d71098d6b050d60dca3,0xcc1b103666b406a61598bccc1503738b02ab80bb94cc1b103666b02ab80bb94ab0661cd5133360425672] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_52s4 : Span p3_52 3 23 29 :=
  batch _ _ _ _ #[
0xd1560851dc7308ca0cc9da8ccc17ac4327488296b4c84ac872e47354880d6b4cd522035ad30a9c222d59,0xc143583728f354880d6b4cd522035ad3354880d6b4c1a32833277308ca0cc9dd190a85a337306c40d99a,0xc11ae02ee505674446b1ac11ae02ee53262c22c599c0c7502f58b306c40cb9ad08a98b162f050d60dca3,0xcd522035ad3068ca0e89dc143583aa8f050d60eaa3c143583aa8e8c5386bc14c98b08b1667354880d6b4,0xccc0a899337354880d6b4cd522035ad3354880d6b4c297108756b068ca0e89dc1d2a0b9a33050d60eaa3,0xc44a989562f354880d6b4cd522035ad3066c40cb9ac19b1032e6b354880d6b4c68710c656b2223a1e855,0xcc2b088ae67162c42999ac508e87a157322c40d99acc8b103666b322c40d99ac0d6a059d33442b22b991,0x1a17516358b340ca0e89dc44a989562f322c40d99acc8b1036669dc88843ab4c508e87a157322c40d99a,0xc589507a98b3360425672c589507a98b3302a264cdc428e873157354880d6b4c2a7088b567162541ea62,0xcc232833277308ca0cc9dcc232833277354880d6b4c1a32833277032a62558b] 78 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_52s5 : Span p3_52 3 29 35 :=
  batch _ _ _ _ #[
0xcc8b1032e6b068ca0e89dc1a3283a2772063a1cc55ccd810959cb032a62558bcc8b1032e6b322c40cb9a,0xcea2202ead33a8880bab4c5c0a8993371702a264cdcd522035ad30a5c421d5ad2a218a62cf322c40cb9a,0xc147484f5874685216ae1c847486b587211d21ad61c58b10a666b162c42999acea2202ead33a8880bab4,0xc11ae035e533065435662ccc1503ab8b322c40d99ac19950b998b032a614b8bc147484f5873065435662,0xccc1503ab8b330540eae2c1a32833277068ca0cc9dc0ca9852e2f236062c473ccc1503ab8b322c40d99a,0xc11ae035e53046b80d794d2a6084e5c74a98213971d2a6084e5c71560625473ccc1503738b322c40cb9a,0xb93221742d28316654c2bccc1503738b068ca0e89dc11ae035e53330540dce2c847486b587322c40cb9a,0xca90e0c6b53031d40bd62c19b1032e6b050d60dca3b085995a0af3a60423a72c55818951cf1560625473,0xcac21886acf050d60eaa3cc8b103666b322c40d99acc8b103666b0a5a813d4ccd03283a277031d40bd62,0xcd03283a277340ca0e89dc143583aa8f050d60eaa3ca90e0a7353156062c473cc8b103666b02ab80d794] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_52s6 : Span p3_52 3 35 36 :=
  batch _ _ _ _ #[
0xc0aae035e53050d60dca3c143583728f02ab80d794c0a8e899957330540dce2ccc1503738b330540dce2,0xd02ac8b1e47031d40bd62c0a8e899957050d60dca3c0aae035e53330540dce2] 14 (by decide +kernel)

private theorem p3_52Good : Good p3_52 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_52s0 (joinSpan p3_52s1 p3_52s2)) (joinSpan (joinSpan p3_52s3 p3_52s4) (joinSpan p3_52s5 p3_52s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_53s0 : Span p3_53 3 0 7 :=
  batch _ _ _ _ #[
0xc147484ee874a88611973c99828711d74a88611973d1035858d8e8531656b03d052985352e8599855784,0xc5d0a057333421d42b3a2c5072850e7702a5616a63ccc1503ab8ae888650973d2a218465cf4a88611973,0xd2a218465cf1742815cccc8474875687314c40cd5ad150c8b334702a5616a63c0a9585a98f211d21d5a1,0xcc53103356b346880d6b4d1035858d8f1742815cccd2a218465cf272821cab1d2a218465cf211d21aba1,0xccc1503ab8b330540eae2c8872888e7732a0a22675c0a8e8999570a5c42999ad1035858d8e8531656b03,0xccc0a88b3370a5c42999aca82e078d5316a8819ab4ca82e078d5316a8819ab4d0274855e87314c40cd5a,0xca82e078d5310a3a1cc55c8872888e77221ca2239dc8872888e7732a880bab4d1035858d8f440d616363,0xcac0c89ab472b03226ad1d1a14857387141ca1439dc847486ae87141ca1439dca82e078d5330ac225c99,0xce831098d6b0465615c63ce831098d6b336042c672c847486ae87211d21aba1b117814e6a34685215ce1,0xc147484ee871760425672c147484ee870463a23c55d190a853337272821cab1ca90e0a7353211d21aba1] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_53s1 : Span p3_53 3 7 12 :=
  batch _ _ _ _ #[
0x1562e119d533302a22ccdd10748ad6873302a22ccdd1521850dcf4548614373d1521850dcf4548614373,0xc5c150c6b8a3541ca52c6c9ca0872ac5d40cc4455ed023584758f272821cab1d023584758dd330443b32,0xd01a98d622f2b03226ad1c428e87315710a3a1cc55c429585718c22ee85e0acd1521850dcf10a5615c63,0xc118e88f157029ca0a99d1562e119d530463a23c55c818e873157109ca1199dc4475066e8b109ca1199d,0xd282985a52f3460a23475d086a84e635a870a585351562e119d53029ca0a99dc818e873157029ca0a99d,0xc0a9585a98c558b846754c5aa2066ad2629d08bba0d1521850dcf02a5616a63c296a0ad631d306444cea,0xc4475066e8b051d213ba1c99828711d7408d611d63c117283167710a5632a63cd18288d1d7045ca0c59d,0xce83103a56b2223a1e855cc2b0897267051d213ba1c147484ee87115c42539ac99828711d7111d419ba2,0xc2a2e02f5530a8b80bd54ccc1503ab8b0a8b80bd54ce83103a56b3460a23475ce83103a56b031d40bba2,0xccc1503ab8b330540eae2] 74 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_53s2 : Span p3_53 3 12 17 :=
  batch _ _ _ _ #[
0xcd18288d1d72660a1c475948c9a1ac2f4a8322e8d1c98b08d2a67342c226a99cd18288d1d72660a1c475,0xc8474875687035c42c39ac84358c558d9885c50ae6c98b08d2a64558b846754cd0b089aa674a8322e8d1,0x741d111746b1423a1e855ce83103a56b27052354e1ccaa202ead316a8819ab4c5aa2066ad316a8819ab4,0xc550e0d4b531a1a813b8cce9810ae1cb3302a264cdc0c6a88d636c053ce9816c143583958f050d60e563,0xc446a8716370a8b80bd54c1ab08972670a8b80bd54c0c6a88d637031aa2358da21793226ab111aa1c58d,0xc81958ab18dd08cc4295ec119585718f342c226a99d2a0c8ba347422a634a8bc42728466770465615c63,0xc0a7282a677029ca0a99dc0a7282a677206562ac63c143583958f0463a23c55c118e88f1574a8322e8d1,0xd1521850dcf422a62e88bc0d710b0e6b3a0c40e95ac98b08d62673302a22ccdd1521850dcf3302a22ccd,0x5e529d1077342c22e899ce83103a56b3a0c40e95ad282985a52f4a0a61694b] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_53s3 : Span p3_53 3 17 22 :=
  batch _ _ _ _ #[
0xce83103a56b4685215ce1cd4a088eac7115c42539ad282985a52f211d21aba1c9ca0872ac7408d611d63,0xc550e0d4b5315438352d4ce83103a56b4a0a61694bcd1a2035ad30a8b80bd54c2a2e02f5533a0c40e95a,0xc98b08d2a670463a26655cd0b089aa67441d213ba1d2a0c8ba347441d213ba1d2a0c8ba3473302a22ccd,0xd282985a52f0465615c63d1521850dcf111d419ba2c0a7282a6774a8322e8d1c0a7282a677346880d6b4,0xc81958ab18f3a0c40e95ace83103a56b031d40bba2c0c7502ee8b3a0c40e95ac0c7502ee8b32a0a22675,0xd02748a9e870a8b80e754c2a2e039d5332a0a22675c88958ca98f32a0a22675c4571094e6b035c42c39a,0xc428e8d195732a0a22675c686a04ee331a1a813b8cc686a04ee3316a0a14675c2a2e039d534548614373,0xc0a7282a677314c40cd5ac99a20a5ad326688296b4d016a851e37346880d6b4c118e899957109ca1199d,0xccc1503ab8b054b80bd54cc53103356b054b80bd54] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_53s4 : Span p3_53 3 22 27 :=
  batch _ _ _ _ #[
0xd01a98d622f074c40cd5acc53103356b32a0a22675c88958b918f3a6042b872ccc1503ab8b330540eae2,0xd0274855e8716a0a14675c0c7502ee8b031d40bba2cc53103356b314c40cd5ac0c7502ee8b031d40bba2,0xc6a0e0c6b53054b80e754c456a055e333302a22ccdc5aa2066ad332a880bab4a0c5998b0af214b831754,0xd023584758f02a3a23c55c4475066e8b111d419ba2c5c0a853337441d22b5a1c152e039d5332a880bab4,0xc0c7502ee8b031d40bba2c0c7502ee8b031d40bba2cc2b089726710a3a1cc55d023584758f2b03226ad1,0xc0a7282a677109ca1199dd190a853337272821cab1ccc1503ab8b115a81578cccc1503ab8b3528223ab1,0xc456a055e33031d40bba2ca90e0a7353029ca0a99dc818e873157029ca0a99dc456a055e33031d40bba2,0xc508e87a157045ca0c59dd0274855e87409d2157a1ccc1503ab8b330540eae2ccc1503ab8b205ca2159d,0xd190a8d1337031d40bba2ccc1503ab8b074c40cd5ac11728316771423a1e855] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_53s5 : Span p3_53 3 27 33 :=
  batch _ _ _ _ #[
0xc1172831677054b80e754d282985a52f045ca0c59dce83103a56b3a0c40e95accaa202ead332a880bab4,0xcac0c89ab473a0c40e95ace83103a56b3a0c40e95ac0a9585a98f112a625c8bccaa202ead3054b80e754,0xccc1503ab8b211d21aba1d190a8d1337330540eae2c11728316774a0a61694bd282985a52f031d40bba2,0xc152e039d533a4282e4ccd2a0c8ba3474a8322e8d1d107484ee874a8322e8d1ccc1503ab8b330540eae2,0xc143583958f02a5616a63c5d0a057333405d4297a2c6871086e6b054b80e754c98b08d2a644353c6c616,0xcd1a2035ad3109ca1199dc0a9585a98f054b80bd54c1d3103356b2223a1e855c143583958f3302a264cd,0xc152e02f553054b80bd54c0a7282a677074c40cd5ac118e899957050d60e563c686a04ee33346880d6b4,0xccc0a8993371a1a813b8cc686a04ee331a1a813b8cc686a04ee331a1a813b8ccc53103356b314c40cd5a,0xcc53103356b050d60e563c143583958f02a3a26655c1d3103356b02a3a26655c0a8e8999573302a264cd] 72 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_53s6 : Span p3_53 3 33 36 :=
  batch _ _ _ _ #[
0xc456a055e33115a81578cc456a055e33211d21d5a1c5aa2066ad33a0c40e95accaa202ead33a0c40e95a,0xc0c6a88d6370b0a62654bc1ab089726706ac225c99c143583958f050d60e563c143583958f1423a1e855,0xccc0a8993372b08621573c1ab08972673302a264cdcc2b08b3266e45c055998c446a8716371702a344cd,0xc0a7282a677029ca0a99dd19150a738b109ca1199dc4272846677109ca1199dc119585718f0b0a62654b,0xc6871086e6b050d60e563c0a7282a6772a43829cd4c143583958f4645429ce2] 38 (by decide +kernel)

private theorem p3_53Good : Good p3_53 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_53s0 (joinSpan p3_53s1 p3_53s2)) (joinSpan (joinSpan p3_53s3 p3_53s4) (joinSpan p3_53s5 p3_53s6)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_54s0 : Span p3_54 3 0 5 :=
  batch _ _ _ _ #[
0x999429710d66650a5c435ccd81031dcb02ab81ea54c0aae07a95342a8614a73cc42a88b3371760421772,0xc5095858d8f1425616363c1c2a853337070aa14ccdcea2202abd31b0262ad0bcea2202abd33a8880aaf4,0xd017502ee8b16a8815674c296a04ee330a5a813b8cc0aae0b99534283a0e715c5aa20559d3141ca1439d,0xc8474875687211d21d5a1c5a128474771684a11d1dd017502ee8b2163223d51d017502ee8b3508a0c4f5,0xcd4228313d7221ca2239dcca1282b477405d40bba2d017502ee8b3284a0ad1dccd81031dcb1684a11d1d,0xccd81031dcb115a81578cc8474875687211d21d5a1c8474875687141ca1439dd29098cac2f4a42632b0b,0xcea2202abd33a8880aaf4cea2202abd34443a0bd15c8872888e77152862c473c8ca18951cf4443a0bd15,0xce98102e5cb3a6040b972ce98102e5cb02ab81ea54c5095858d8f211d21d5a1c5095858d8f1425616363,0xc0aae07a95310ab833a54cea2202abd33a8880aaf4cea2202abd3211d21d5a1] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_54s1 : Span p3_54 3 5 10 :=
  batch _ _ _ _ #[
0x86a7814e6a31425616363c5095858d8f0a5a81ab8cc2a708aa667111aa2358dc296a04ee321a9e0539a8,0xd11a18529cf4a42616b0bc296a06ae330a5a81ab8cc2a708aa6671425616363c296a04ee33051d21d5a1,0xcd5220353d3405d40bba2ce91103ac6b354880d4f4d0a0e839c574468614a7395e211163cb4468614a73,0xc8872888e77310aa22ccdc0d6a075633035a81d58cc296a04ee33405d40bba2d017502ee8b354880d4f4,0xc1c2a853337310d40dce2d016a84e6373a6040b972ce98102e5cb035a81d58cc8872888e773560223571,0x88bc29702d7046b81ea54ce91103ac6b4688a118f5d1a228463d74688a118f5d1a228463d74688a118f5,0xc296a06ae3316a8815674c296a04ee33310d40dce2cc43503738b405d40bba2cd5220353d1835685e42c,0xc296a06ae33409d2157a1d0274855e870a5a81ab8cc296a06ae330a5a81ab8cc296a06ae3316a8815674,0xd11a18529cf16a8815674c858c88f54716a8815674cea80889dc716a8815674d0274855e874468614a73,0xc0aae0b99532163223d51c152e037353054b80dcd4] 76 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_54s2 : Span p3_54 3 10 15 :=
  batch _ _ _ _ #[
0xc5a128474774468614a73c429584758f10a5611d63c429584758f4a42616b0bd11a18529cf4468614a73,0xc456a055e334a42632b0bcea108ab4674a42632b0bc0a9582b58f3284a0ad1dc0a9582b58f02a560ad63,0xcc19502f58b0a8b80ead4c456a055e330665419d62c199506758b031d41d3a27503a1193b1d284c42b1e,0xe5391833a818b5670aa3c0aae07a951d284c42b1ecea2202abd3460aa344cdcea2202abd30a8b80ead4,0xcea2202abd3405aa1398dd182a8d13373a8880aaf474a1310ac7b02ab81ea54c0aae07a953405aa1398d,0xc296a06ae332303a1e315d1a228463d7109ca1199d7503a1193b3046b81ea54cea2202abd33a8880aaf4,0xc296a06ae332303a1e315c152e0373530a9c22a999c2a708aa667046b81ea54c0a7282a6774688a118f5,0xcd1128394772303a1e315c8c0e878c570362614d4b62237142b9b074a815cccd086a851e370362614d4b,0xcea2202abd3346882b474ccd1103746b046560e563cc895039d8b045ca0c59d] 70 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_54s3 : Span p3_54 3 15 21 :=
  batch _ _ _ _ #[
0xc152e037353046560e563c1172831677046560e563c81958c558f4342615d0bc158c8735473aa0222771,0xca87088ae67054b80dcd4ccd1103746b046560e563c1d2a057333045ca0c59dcd112839477046560e563,0xca87088ae6462e545e162d107484ee87441d213ba1c0c75074e8844cdc550e6c8c0e878c57266881d474,0xcd1128394772303a1e315c8c0e878c57460d431ae2d1a228463d74688a118f5d1a228463d7441d213ba1,0xc9d808715c74468614a73c8c0e878c57046560e563cd11283947444cdc550e6ccd1103746b046560e563,0xc88ae0b99533a4440eb1ace91103ac6b421aa1478dcd58088d5c422e5c5a166d086a851e371684a11d1d,0xc81ae077153206b81dc54c15708b1665d284c42b1ecca1282b47702a560ad63cd5220353d1d08e842cec,0xcd5108b94674a83233b11c11ae0af1532a23226751c2a2e03ab530a8b80ead4ca88c899d470a8b80ead4,0xc199506758b0665419d62c11ae0771532744235519c8570895667215c225599c2a2e03ab53066c42cc5a,0xcc19502f58b32a882a674cc19502f58b111d42b3a2c686a04ee331a1a813b8cc199506758b0665419d62] 80 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_54s4 : Span p3_54 3 21 26 :=
  batch _ _ _ _ #[
0xc0c75074e8b0a6261694bc5a12847477441d213ba1d107484ee871684a11d1dc5a12847477441d213ba1,0xd022e8c6357441d213ba1cca1282b47702a560ad63cca1282b4771a1a813b8cce98102e5cb441d213ba1,0xc0c75074e8b441d213ba1c2a8c87a547111d42b3a2d18350c6b8b1a1a813b8cd1a228463d70665419d62,0x629531aa07b035a82a78c9aa2c19ab43210ba21cd5cc19502f58b1a1a813b8cc686a04ee331a1a813b8c,0xc456a055e331b0262ad0bd016a84e637050ba0ccd5c2a2e03ab530a8b80ead4cea2202abd33a8880aaf4,0xc0a7282a677109ca1199dccd81031dcb336040c772c42728466770a9c22a999ce91103ac6b3a4440eb1a,0xccd81031dcb322c426a5ad1a228463d74688a118f5d017502ee8b4688a118f5c0a7282a677029ca0a99d,0xc0d6a055e33046560e563d1a228463d74688a118f5d1a228463d71b0262ad0bc1c2a8533373444a0e51d,0xcc8b109a96b1760421772d1a228463d74688a118f5] 68 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_54s5 : Span p3_54 3 26 31 :=
  batch _ _ _ _ #[
0xcea2202abd33a8880aaf4cea2202abd3051d22b5a1c1d2a0573333a8880aaf4cea2202abd33a6040b972,0xc296a04ee330a5a813b8cc84748756871744429d1ac9c228853d72708a214f5c9c228853d7421d40d7a2,0x17171112e6b222b82e654c296a04ee305c5c444b9acc895039d8b109ca1199dc4272846677322540e762,0xc686a04ee334283a0e715ccd1103746b3508a0c4f5c1d2a0573333a6040b972c0d8985352f211d21d5a1,0xd0a0e839c57054b80dcd4cea80889dc72708a214f5cea80889dc72708a214f5c152e0373531a1a813b8c,0xcd4228313d73508a0c4f5ca87088ae670a6261694bcca1282b4773284a0ad1dc298985a52f3284a0ad1d,0xd110e82f457408ba318d5c5a128474770a6261694bc5a128474771684a11d1dc5a12847477222b81ea54,0xc5d81085dcb0665419d62d18350c6b8b460d431ae2c4272846677336040c772ccd81031dcb1b0262e50b,0xc84748ad6871b0262e50b] 66 (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p3_54s6 : Span p3_54 3 31 34 :=
  batch _ _ _ _ #[
0xc142e833357354422e519d0875035e8b0a8b80ead4c15708b16673a6040b972c298985a52f210ba21cd5,0xc298985a52f050ba0ccd5c8570895667215c225599c298985a52f0a6261694bc2a2e03ab530a8b80ead4,0xd1a228463d7310aa22ccdd1a228463d7070aa14ccdcd5220353d30a5a813b8ccd58088d5c73a4440eb1a,0xc9d108d54672b0322bd11c296a04ee33029ca0a99dcd58088d5c45c5c444b9ac0a7282a677029ca0a99d,0xd016a84e637405aa1398dc0d6a0756334468615873cc42a88b337354422e519cd5220353d2540bc44ad6,0xc298985a52f0a6261694b] 42 (by decide +kernel)

private theorem p3_54Good : Good p3_54 :=
  fullSpan (by decide) (by decide +kernel) (joinSpan (joinSpan p3_54s0 (joinSpan p3_54s1 p3_54s2)) (joinSpan (joinSpan p3_54s3 p3_54s4) (joinSpan p3_54s5 p3_54s6)))

private def level3 : List (List Nat) := [p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9, p3_10, p3_11, p3_12, p3_13, p3_14, p3_15, p3_16, p3_17, p3_18, p3_19, p3_20, p3_21, p3_22, p3_23, p3_24, p3_25, p3_26, p3_27, p3_28, p3_29, p3_30, p3_31, p3_32, p3_33, p3_34, p3_35, p3_36, p3_37, p3_38, p3_39, p3_40, p3_41, p3_42, p3_43, p3_44, p3_45, p3_46, p3_47, p3_48, p3_49, p3_50, p3_51, p3_52, p3_53, p3_54]
private theorem known3 (p : List Nat) (h : p∈level3) : Good p := by
  simp only [level3,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact p3_0Good
  · exact p3_1Good
  · exact p3_2Good
  · exact p3_3Good
  · exact p3_4Good
  · exact p3_5Good
  · exact p3_6Good
  · exact p3_7Good
  · exact p3_8Good
  · exact p3_9Good
  · exact p3_10Good
  · exact p3_11Good
  · exact p3_12Good
  · exact p3_13Good
  · exact p3_14Good
  · exact p3_15Good
  · exact p3_16Good
  · exact p3_17Good
  · exact p3_18Good
  · exact p3_19Good
  · exact p3_20Good
  · exact p3_21Good
  · exact p3_22Good
  · exact p3_23Good
  · exact p3_24Good
  · exact p3_25Good
  · exact p3_26Good
  · exact p3_27Good
  · exact p3_28Good
  · exact p3_29Good
  · exact p3_30Good
  · exact p3_31Good
  · exact p3_32Good
  · exact p3_33Good
  · exact p3_34Good
  · exact p3_35Good
  · exact p3_36Good
  · exact p3_37Good
  · exact p3_38Good
  · exact p3_39Good
  · exact p3_40Good
  · exact p3_41Good
  · exact p3_42Good
  · exact p3_43Good
  · exact p3_44Good
  · exact p3_45Good
  · exact p3_46Good
  · exact p3_47Good
  · exact p3_48Good
  · exact p3_49Good
  · exact p3_50Good
  · exact p3_51Good
  · exact p3_52Good
  · exact p3_53Good
  · exact p3_54Good

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p2_0Good : Good p2_0 :=
  routeLevel p2_0 level3 #[
0x358d11ac688,0x758d11ac688,0x6ccd1166688,0x66ad1135688,0xb58d11ac688,0xf58d11ac688,0xeccd1166688,0xe6ad1135688,0xf58983ac4c1,0x758983ac4c1,0x1358d11ac688,0x1758d11ac688,
0x166a983354c1,0x126a983354c1,0xecc983664c1,0x6cc983664c1,0x1758983ac4c1,0x1358983ac4c1,0x16ccd1166688,0x12ccd1166688,0xe6a983354c1,0x66a983354c1,0x126ad1135688,0x166ad1135688,
0x12cc983664c1,0x16cc983664c1,0x758435ac21a,0x1b58d11ac688,0x1f58d11ac688,0x1e6a4353521a,0x1a6a4353521a,0xf580b5ac05a,0x2358d11ac688,0x2758d11ac688,0x2b58d11ac688,0x2f58d11ac688,
0x2ecc0b56605a,0x2acc0b56605a,0x1b4a4277405a,0x1f4a4277405a,0x3358d11ac688,0x3758d11ac688,0x3b58d11ac688,0x3f58d11ac688,0x32e8d032e4c8,0x3ae8d032e4c8,0x266a0b53505a,0x226a0b53505a,
0x1ee8d032e4c8,0x1ae8d032e4c8,0x4358d11ac688,0x4758d11ac688,0x4b58d11ac688,0x4f58d11ac688,0x42e8d032e4c8,0x4ae8d032e4c8,0x6cc4356621a,0x1f58435ac21a,0x1b58435ac21a,0x1eccd1166688,
0x1accd1166688,0xecc0b56605a,0x2accd1166688,0x2eccd1166688,0x26ccd1166688,0x22ccd1166688,0x27580b5ac05a,0x23580b5ac05a,0x1f4ad03744c8,0x1b4ad03744c8,0x4eccd1166688,0x4b4ad03744c8,
0x46ccd1166688,0x434ad03744c8,0x42ccd1166688,0x4accd1166688,0x2a6a0b53505a,0x2e6a0b53505a,0x1e5c427a505a,0x1a5c427a505a,0x3eccd1166688,0x3b4ad03744c8,0x36ccd1166688,0x334ad03744c8,
0x32ccd1166688,0x3accd1166688,0x66a4353521a,0x1a6ad1135688,0x1e6ad1135688,0x1acc4356621a,0x1ecc4356621a,0xe6a0b53505a,0x226ad1135688,0x266ad1135688,0x2e6ad1135688,0x2a6ad1135688,
0x2f580b5ac05a,0x2b580b5ac05a,0x1ae84272e05a,0x1ee84272e05a,0x325cd03a54c8,0x3a6ad1135688,0x3a5cd03a54c8,0x326ad1135688,0x3e6ad1135688,0x366ad1135688,0x22cc0b56605a,0x26cc0b56605a,
0x1a5cd03a54c8,0x1e5cd03a54c8,0x425cd03a54c8,0x4a6ad1135688,0x4a5cd03a54c8,0x426ad1135688,0x4e6ad1135688,0x466ad1135688] known3 2 (by decide) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p2_1Good : Good p2_1 :=
  routeLevel p2_1 level3 #[
0x6e8ca174650,0x444395621cab,0x66a5a0e6a42,0x44c0b578c09d,0x5358d11ac688,0x5758d11ac688,0x525c990e5c81,0x565c990e5c81,0x5b58d11ac688,0x5f58d11ac688,0x6358d11ac688,0x6758d11ac688,
0x6b58d11ac688,0x6f58d11ac688,0x7358d11ac688,0x7758d11ac688,0x49e4298f214c,0x765c990e5c81,0x7b58d11ac688,0x496741816761,0x7a5c990e5c81,0x725c990e5c81,0x665c990e5c81,0x625c990e5c81,
0x6e5c990e5c81,0x5e5c990e5c81,0x6a5c990e5c81,0x5a5c990e5c81,0x5ee883374419,0x7f58d11ac688,0x3f3a8439d421,0x1b43585a1ac2,0x8358d11ac688,0x5f50a333508b,0x8758d11ac688,0x55942e8ca174,
0x8b58d11ac688,0x8f58d11ac688,0x82e4e112e4c1,0x1a6748466750,0x8ee4e112e4c1,0x8ae4e112e4c1,0x9358d11ac688,0x7e6748466750,0x30d423c6a11e,0x7f43585a1ac2,0x329813ca9833,0x92e4e112e4c1,
0x3de0ac35e08c,0x7ee4e112e4c1,0x54ba1688ba26,0x86e4e112e4c1,0x9758d11ac688,0x24cc13a8cc2b,0x76b131511746,0x261433b0a19d,0x75dd01454af0,0x96e4e112e4c1,0x304356621ab3,0x766ac22ec470,
0x7ebd0a15e850,0x2468556342ab,0x1abd0a15e850,0x3d57818157a1,0x91ad602d6b01,0x95ad602d6b01,0x7e999a0e9982,0x24233578231d,0x89ad602d6b01,0x5422ecd422f4,0x7dad602d6b01,0x81cb9029cb88,
0x85ad602d6b01,0x8dcb9029cb88,0x3d0ce988674c,0x1a999a0e9982,0x545654c2b2a6,0x89cb9029cb88,0x5d4d41614d59,0x5d0ba1685d0b,0x91cb9029cb88,0x95cb9029cb88,0x81ad602d6b01,0x7dcb9029cb88,
0x302a66702a5e,0x760772359506,0x8dad602d6b01,0x85cb9029cb88,0x61cb9029cb88,0x4abc8435e421,0x5d6b182b58c1,0x75cb9029cb88,0x4dd1846e8c2,0x65cb9029cb88,0x716b182b58c1,0x596b182b58c1,
0x756b182b58c1,0x516b182b58c1,0x69cb9029cb88,0x59cb9029cb88,0x6dcb9029cb88,0x5dcb9029cb88,0x656b182b58c1,0x450873a8439d,0x616b182b58c1,0x556b182b58c1,0x5cd4845cd50,0x51cb9029cb88,
0x79cb9029cb88,0x6d6b182b58c1,0x71cb9029cb88,0x471813ab182b,0x796b182b58c1,0x696b182b58c1,0x482cec342ccc,0x55cb9029cb88] known3 2 (by decide) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p2_2Good : Good p2_2 :=
  routeLevel p2_2 level3 #[
0x9942e8ca174,0x8b0acc8b1ac,0x9b58d11ac688,0x5032b4a195a5,0x9a5cc14e5c81,0x50b0acc8b1ac,0x9ae70152e681,0x519434aca1a5,0x9ac791163c88,0x51846cc585ac,0x50a0f4a507a5,0x9b3941573881,
0x9a3d5111ea88,0x5022eccc23ac,0x51162cc117ac,0x510674a833a5,0x99cb8159ca81,0x99eb110f5888,0x9b58c23ac611,0x5032ae819574,0x9a5cd02e5c50,0x50b0b588b135,0x5ae29c1a5053,0x5b545896608b,
0x9f58d11ac688,0xa358d11ac688,0x9ee71032e650,0xa2e71032e650,0x88a133a5099d,0xa758d11ac688,0x2842b3a2159d,0x973460b560cc,0x9714e50a8c5c,0x2823357022f5,0xa73950373850,0x88c0b568c0f5,
0xab58d11ac688,0x875811763382,0xa9cb9039ca50,0xaf58d11ac688,0x844b9334b832,0xadcb9039ca50,0x9ae71032e650,0x51942e8ca174,0x9ac782363c11,0x518475858535,0xae5cd02e5c50,0xaec791163c88,
0xaa5cd02e5c50,0x865c1325ca32,0xaac791163c88,0x86c191719b82,0xa2c791163c88,0x9ec791163c88,0x5b155c128c53,0x5aa398930a8b,0x9f3950373850,0xa33950373850,0x95a3a0ab0acc,0x8a04756604f5,
0xa6c791163c88,0x2918356118f5,0x890873a8439d,0x2a1433b0a19d,0x94a7a514645c,0xa5cb9039ca50,0x50a0ee850774,0x9b3950373850,0x9a3d4231ea11,0x5022f58c2335,0x28a133a5099d,0xa65cd02e5c50,
0x8842b3a2159d,0x953c65032a5c,0x951ce0b854cc,0x8823357022f5,0xa63d5111ea88,0x28c0b568c0f5,0x86e1132e5232,0xaae71032e650,0xaee71032e650,0xae3d5111ea88,0xaa3d5111ea88,0x860d516cd982,
0x9e3d5111ea88,0x591d5898588b,0xa1cb9039ca50,0xa23d5111ea88,0x58ab9c146853,0x9dcb9039ca50,0x511635811735,0x51066e883374,0x99cb9039ca50,0x99eb022f5811,0x9e5cd02e5c50,0xa25cd02e5c50,
0x9deb110f5888,0x58ea9882cc8b,0xa1eb110f5888,0x595c5c034a53,0x95e2a519505c,0x2a04756604f5,0xa6e71032e650,0x8918356118f5,0x290873a8439d,0x8a1433b0a19d,0x94e6a0a2accc,0xa5eb110f5888,
0xab3950373850,0xadeb110f5888,0x846b1166c782,0x870953329632,0xaf3950373850,0xa9eb110f5888] known3 2 (by decide) (by decide +kernel)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p2_3Good : Good p2_3 :=
  routeLevel p2_3 level3 #[
0xd942e8ca174,0x9a6ac22ecc88,0x5032ae8ca1a5,0xb758d11ac688,0xbb58d11ac688,0x511626b822ec,0xa50674a833a5,0xb5cb8149cb81,0x94435e421af2,0xbf58d11ac688,0xbabd1035e881,0x74b0acd8b0ac,
0x9698166e9816,0xc22e6b422e6,0xb9cb8149cb81,0x750674a833a5,0xb5dd102ee881,0xbda2358d11ac,0x998466b910ec,0xee8ca174650,0x34439d421cea,0x526a8b0ecc11,0x57588b163c11,0x982335688766,
0x50b135411766,0xd1735011735,0xc358d11ac688,0x53545896608b,0xc758d11ac688,0x65072e2314e5,0xb88d63446b1a,0x7d312e2322e5,0xb911ac688d63,0x35d421cea10e,0xcb58d11ac688,0x64a0e5d4629c,
0xa1312e20e4e5,0xc9a3a0a88af4,0x55952e050ce5,0xa985ac2585ac,0xc06b1a2358d1,0xcf58d11ac688,0x5ae883374419,0x7e5c5305ca32,0x373a8439d421,0x2ee70a173850,0x8ee70a173850,0xd358d11ac688,
0xc1a2358d11ac,0x598535258535,0xb4a72e00a72e,0xd758d11ac688,0xa0a625d41c9c,0xaac2c2dac2c2,0x78d42666a133,0xc86b1a2358d1,0x405473863156,0x67141cb28c53,0x91a3a0ab0acc,0xd51d588458b3,
0x2d18f50118f5,0xa65419d2a0ce,0xd5a2358d11ac,0x7ca625d4645c,0x8b4151759982,0xb9a2358d11ac,0x40435e421af2,0x774a833a5419,0x86bd0a15e850,0x1dea8c0ac631,0x22bd0a15e850,0x5432a5d4a19c,
0x5dc2ae0531a5,0xb502ee881774,0xc1066e883374,0x5cc63541a366,0xace42567212b,0x8917a0b82acc,0xcc6b1a2358d1,0xcd11ac688d63,0x411ce0ac558c,0xa8b0b590b0b5,0x88545e8660ab,0xc08d63446b1a,
0x11d0a625d0a6,0x9e2159d10ace,0x711d5898588b,0xcab47411115e,0x68aa1cd46853,0xdb58d11ac688,0xd540ee20bca5,0x6758c2363470,0x42bc8435e421,0x5d5c1c234a53,0x96bc8435e421,0xc5d1942e8ca,
0xc0a72e00a72e,0x59066e883374,0xd1a2358d11ac,0xb5a2358d11ac,0xd43b8a8f2941,0xad0959c84ace,0x8d18f50118f5,0xb48d63446b1a,0xa04b8a793941,0x350873a8439d,0xce3446b1a235,0x504d5165d982,
0x6d42f50142f5,0xd84a5e4252f2,0x2284666e8466,0x546b1166c782,0xd61a83d0d41e,0xb06a998ac383,0x8e8463da8463] known3 2 (by decide) (by decide +kernel)

private def level2 : List (List Nat) := [p2_0, p2_1, p2_2, p2_3]
private theorem known2 (p : List Nat) (h : p∈level2) : Good p := by
  simp only [level2,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact p2_0Good
  · exact p2_1Good
  · exact p2_2Good
  · exact p2_3Good

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private theorem p1_0Good : Good p1_0 :=
  routeLevel p1_0 level2 #[
0x358d11ac688,0x2e8d1174688,0x1ad610d6b08,0x758d11ac688,0x6e8d1174688,0x6ccd1166688,0x1e5610f2b08,0x74ad11a5688,0x65cd112e688,0x66ad1135688,0x3356119ab08,0x1aba10d5d08,
0x6c791163c88,0x6579112bc88,0x357111ab888,0x757111ab888,0x66751133a88,0x33aa119d508,0x2e711173888,0x6e711173888,0x1eaa10f5508,0x747511a3a88,0x63b9111dc88,0x1d5a10ead08,
0x6b99115cc88,0x63d5111ea88,0x356a11ab508,0x33b1119d888,0x73b1119d888,0x6bd1115e888,0x1dca10ee508,0x2bd1115e888,0x7395119ca88,0x5cb910e5c88,0x5d9910ecc88,0x2b5a115ad08,
0x5cd510e6a88,0x2e6a1173508,0x5eb110f5888,0x1eb110f5888,0x2bca115e508,0x5dd110ee888,0x5e9510f4a88,0x1dd110ee888,0x1a2358d11ac,0xb58d11ac688,0xae8d1174688,0xaccd1166688,
0x194358ca1ac,0xb4ad11a5688,0xa5cd112e688,0xa6ad1135688,0xb43585a1ac,0x911ac688d63,0x8a1ac650d63,0x48d63446b1a,0xf58d11ac688,0xee8d1174688,0xeccd1166688,0x4e163470b1a,
0xf4ad11a5688,0xe5cd112e688,0xe6ad1135688,0x71163588b1a,0x48ba3445d1a,0xec791163c88,0xe579112bc88,0x91c2c68e163,0xf57111ab888,0xe6751133a88,0x71a2358d11a,0x8ac2c656163,
0xee711173888,0x4ea2347511a,0xf47511a3a88,0xe3b9111dc88,0x4d1a3468d1a,0xeb99115cc88,0xe3d5111ea88,0x752235a911a,0x9622c6b1163,0xf3b1119d888,0xebd1115e888,0x4dc2346e11a,
0x8e42c672163,0xf395119ca88,0xdcb910e5c88,0xdd9910ecc88,0x691a3548d1a,0xdcd510e6a88,0x6e22357111a,0xdeb110f5888,0xb222c791163,0x69c2354e11a,0xddd110ee888,0xde9510f4a88,
0xb142c78a163,0x91174688ba3,0x8a174650ba3,0x48b3344599a,0xec6b1163588,0xe56b112b588,0xe3ab111d588,0x4d13346899a,0xeb8b115c588,0xdcab10e5588,0xdd8b10ec588,0x6913354899a,
0x1a3858d1c2c,0xb58991ac4c8,0xae8991744c8,0x48d2b44695a,0xf58991ac4c8,0xee8991744c8,0xe3ca911e548,0x753035a981a,0x963446b1a23,0xf3aa119d508,0xdcca90e6548,0x6e30357181a,
0xdeaa10f5508,0xb2344791a23,0xacc991664c8,0x195858cac2c,0xb4a991a54c8,0xecc991664c8,0x4e12b47095a,0xf4a991a54c8,0x91d4468ea23,0xf56a11ab508,0xe66a9133548,0x71b0358d81a,
0x69d0354e81a,0xddca10ee508,0xde8a90f4548,0xb154478aa23,0xa5c9912e4c8,0xa6a991354c8,0xb58585ac2c,0xe5c9912e4c8,0xe6a991354c8,0x7112b58895a,0x8ad44656a23,0xee6a1173508,
0x4eb0347581a,0xf46a91a3548,0xebca115e508,0x4dd0346e81a,0x8e544672a23,0xf38a919c548,0x48973444b9a,0xe357111ab88,0xdc5710e2b88,0x91a3468d1a3,0xec4f1162788,0xdd5310ea988,
0x6983354c19a,0x8aa346551a3,0xe54f112a788,0x4d83346c19a,0xeb53115a988,0x489ab444d5a,0xe35a911ad48,0xdc5a90e2d48,0x1ac458d622c,0x758435ac21a,0x6e84357421a,0xb55191aa8c8,
0xf55191aa8c8,0xde5610f2b08,0xb2a44795223,0xae5191728c8,0xee5191728c8,0x96a446b5223,0xf356119ab08,0xec599162cc8,0x91b8468dc23,0x6998354cc1a,0xdd5a10ead08,0xac599162cc8,
0xf54e11aa708,0xde5290f2948,0xb1a8478d423,0x19c858ce42c,0xb45591a2ac8,0x4e82b47415a,0xf45591a2ac8,0xe64e9132748,0x7194358ca1a,0xe559912acc8,0x8ab84655c23,0xeb5a115ad08,
0x4d98346cc1a,0xa559912acc8,0xee4e1172708,0x8ea84675423,0xf352919a948,0xa6559132ac8,0xbc8585e42c,0xe6559132ac8,0x7182b58c15a,0x4e943474a1a,0xf44e91a2748,0xda9710d4b88,
0x4c173460b9a,0xe2771113b88,0xdab310d5988,0x6c23356119a,0x952346a91a3,0xea8f1154788,0xe2af1115788,0x4ca3346519a,0x8d43466a1a3,0xea731153988,0xda9a90d4d48,0x4c1ab460d5a,
0xe27a9113d48,0x6cc4356621a,0x1e4458f222c,0x74a435a521a,0xdad610d6b08,0xb54447aa223,0xb2b191958c8,0xf2b191958c8,0xead191568c8,0x95c446ae223,0xaad191568c8,0xf2761193b08,
0x6c383561c1a,0xdaba10d5d08,0xea999154cc8,0x953846a9c23,0xdad290d6948,0xb52847a9423,0xaa999154cc8,0xf2ae1195708,0x4cc2b46615a,0xe2ce9116748,0x1e2858f142c,0x743435a1a1a,
0xb2959194ac8,0xf2959194ac8,0x8d58466ac23,0xea7a1153d08,0xe2b99115cc8,0x4cb83465c1a,0xeace1156708,0x8dc8466e423,0xa2b99115cc8,0xf2729193948,0xe2d59116ac8,0x4cd43466a1a,
0xa2d59116ac8,0xf28e9194748,0xe68587342c,0x7422b5a115a,0xd397109cb88,0xd47710a3b88,0x61173508b9a,0xd3b3109d988,0x6523352919a,0xd58f10ac788,0xaa2347511a3,0x61a3350d19a,
0xd4af10a5788,0xd57310ab988,0xa943474a1a3,0xd39a909cd48,0xd47a90a3d48,0x611ab508d5a,0x65c4352e21a,0x66a4353521a,0x3344599a22c,0xd3d6109eb08,0xae444772223,0xd6b190b58c8,
0x96b190b58c8,0xaac44756223,0xd5d190ae8c8,0xd67610b3b08,0x95d190ae8c8,0x65383529c1a,0xd3ba109dd08,0xaa384751c23,0xd59990accc8,0xd3d2909e948,0xae284771423,0xd6ae10b5708,
0x959990accc8,0xd4ce90a6748,0x61c2b50e15a,0x66343531a1a,0x3328599942c,0xd69590b4ac8,0x969590b4ac8,0xd57a10abd08,0xa958474ac23,0x61b8350dc1a,0xd4b990a5cc8,0xa9c8474e423,
0xd5ce10ae708,0xd67290b3948,0x94b990a5cc8,0x61d4350ea1a,0xd4d590a6ac8,0xd68e90b4748,0x94d590a6ac8,0x6622b53115a,0x3168598b42c] known2 1 (by decide) (by decide +kernel)

private theorem firstRow (L : LatinSquare 7) (h : ∀ x, L.mat 0 x=x) :
    ∃ σ, IsTransversal L σ := by
  apply p1_0Good L
  intro r hr
  have e : r = p1_0.head! := by simpa [p1_0] using hr
  subst r
  refine ⟨0,?_⟩
  have diag : ∀ c s : D, p1_0.head!.testBit (pos c s) = true ↔ c=s := by decide
  intro c s
  rw [h]
  exact diag c s

theorem orderSeven (L : LatinSquare 7) : ∃ σ, IsTransversal L σ := by
  let p : D ≃ D := Equiv.ofBijective (L.mat 0)
    ⟨L.row_injective 0,Finite.surjective_of_injective (L.row_injective 0)⟩
  let M : LatinSquare 7 := {
    mat := fun i j => L.mat i (p.symm j)
    row_injective := fun i => (L.row_injective i).comp p.symm.injective
    col_injective := fun j => L.col_injective (p.symm j) }
  obtain ⟨σ,hc,hs⟩ := firstRow M (fun j => p.apply_symm_apply j)
  exact ⟨fun i => p.symm (σ i),p.symm.injective.comp hc,hs⟩

end OMA.LatinSeven

theorem OMA.solution : OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1.H1 := OMA.LatinSeven.orderSeven
