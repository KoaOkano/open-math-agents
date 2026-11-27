import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H1_R1
import Mathlib

/-! A finite covering argument for the triangle-good graphs of orders four,
five and six tabulated by Brandt, Brinkmann and Harmuth. Extend a labelled
part of a triangle-free graph by one vertex with neighborhood S. All old
edges inside S must be absent. A checked instruction then exhibits the
desired complement embedding or embeds all remaining edges into the next
template. The instructions include both maps, so the covering argument
does not assume a classification of the hosts. -/
namespace OMA.SmallTriangleGood
open SimpleGraph

private def allI (k : Nat) (p : Fin k → Bool) := (List.finRange k).all p

private theorem takeI {k : Nat} {p : Fin k → Bool} (h : allI k p=true) (i : Fin k) :
    p i=true := List.all_eq_true.mp h i (List.mem_finRange i)

private def bit (graph i j : Nat) : Bool := graph.testBit (16*i+j)

private def expanded (k graph lo hi i j : Nat) : Bool :=
  if i=k then if j=k then false else hi.testBit j
  else if j=k then hi.testBit i
  else bit graph i j && !(lo.testBit i && lo.testBit j)

private def digit (k word i : Nat) : Fin (k+1) :=
  Fin.ofNat (k+1) ((word >>> (4*i)) % 16)

private def distinct {k h : Nat} (d : Fin k → Fin h) :=
  allI k fun i => allI k fun j => decide (i=j) || decide (d i ≠ d j)

private theorem inj {k h : Nat} {d : Fin k → Fin h} (ok : distinct d=true) :
    Function.Injective d := by
  intro i j eq
  have test := takeI (takeI ok i) j
  simpa [eq] using test

private def Found {N : Nat} (n pattern : Nat) (C : SimpleGraph (Fin N)) : Prop :=
  ∃ g : Fin n ↪ Fin N, ∀ i j, i<j → pattern.testBit (i.val*n+j.val)=false →
    ¬ C.Adj (g i) (g j)

private def Good (n pattern k host : Nat) : Prop :=
  ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
  ∀ l : Fin k ↪ Fin (2*n-1), (∀ i j, C.Adj (l i) (l j) → bit host i.val j.val=true) →
    Found n pattern C

private def instruction (n pattern k host lo hi w : Nat) (targets : List Nat) : Bool :=
  let word := w >>> 1
  let edge (i j : Fin (k+1)) := expanded k host lo hi i.val j.val
  if w.testBit 0 then
    let d (i : Fin n) := digit k word i.val
    distinct d && allI n fun i => allI n fun j =>
      !decide (i<j) || pattern.testBit (i.val*n+j.val) || !edge (d i) (d j)
  else
    let d (i : Fin (k+1)) := digit k word i.val
    match targets[word >>> (4*(k+1))]? with
    | none => false
    | some next => distinct d && allI (k+1) fun i => allI (k+1) fun j =>
        !edge i j || bit next (d i).val (d j).val

private theorem instruction_sound {n pattern k host lo hi w : Nat} {targets : List Nat}
    (rest : ∀ h∈targets, Good n pattern (k+1) h)
    (pass : instruction n pattern k host lo hi w targets=true)
    (C : SimpleGraph (Fin (2*n-1))) (ht : C.CliqueFree 3)
    (l : Fin (k+1) ↪ Fin (2*n-1))
    (cover : ∀ i j, C.Adj (l i) (l j) → expanded k host lo hi i.val j.val=true) :
    Found n pattern C := by
  unfold instruction at pass
  dsimp only at pass
  split at pass
  · obtain ⟨perm,check⟩ := Bool.and_eq_true_iff.mp pass
    let d : Fin n ↪ Fin (k+1) := ⟨fun i => digit k (w >>> 1) i.val, inj perm⟩
    refine ⟨d.trans l,?_⟩
    intro i j lt missing edge
    have xy := cover (d i) (d j) edge
    have tst := takeI (takeI check i) j
    change expanded k host lo hi (d i).val (d j).val = true at xy
    change ((!decide (i<j) || pattern.testBit (i.val*n+j.val)) ||
      !expanded k host lo hi (d i).val (d j).val)=true at tst
    simp [lt,missing,xy] at tst
  · split at pass
    · contradiction
    · rename_i h idx
      obtain ⟨perm,check⟩ := Bool.and_eq_true_iff.mp pass
      let d (i : Fin (k+1)) := digit k (w >>> 1) i.val
      let p : Fin (k+1) ≃ Fin (k+1) := Equiv.ofBijective d
        ⟨inj perm,Finite.surjective_of_injective (inj perm)⟩
      apply rest h (List.mem_of_getElem? idx) C ht (p.symm.toEmbedding.trans l)
      intro a b adj
      have xy := cover (p.symm a) (p.symm b) adj
      have tst := takeI (takeI check (p.symm a)) (p.symm b)
      change (!expanded k host lo hi (p.symm a).val (p.symm b).val ||
        bit h (p (p.symm a)).val (p (p.symm b)).val)=true at tst
      simpa [xy] using tst

private def Fits (k s lo hi : Nat) : Prop := ∀ i : Fin k,
  (lo.testBit i.val=true → s.testBit i.val=true) ∧
  (s.testBit i.val=true → hi.testBit i.val=true)

-- The s-th bit records whether the membership choices in s fit the box.
-- Doubling the truth table allows either value of the next membership bit.
private def cube (lo hi : Nat) : Nat → Nat
  | 0 => 1
  | k+1 =>
    let half := 2^k
    let inner := cube lo hi k % 2^half
    (if lo.testBit k then 0 else inner) ||| (if hi.testBit k then inner <<< half else 0)

private theorem cube_sound (lo hi k s : Nat) (hs : s < 2^k)
    (hit : (cube lo hi k).testBit s=true) : Fits k s lo hi := by
  induction k generalizing s with
  | zero => exact fun i => Fin.elim0 i
  | succ k ih =>
    by_cases low : s < 2^k
    · have ss := Nat.testBit_lt_two_pow low
      have good : lo.testBit k=false ∧ (cube lo hi k).testBit s=true := by
        cases l : lo.testBit k <;> cases h : hi.testBit k <;>
          simp_all [cube,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.not_le_of_gt low]
      intro i
      induction i using Fin.lastCases with
      | last => simp [ss,good.1]
      | cast i => exact ih s low good.2 i
    · let t := s - 2^k
      have tl : t<2^k := by dsimp [t]; rw [pow_succ] at hs; omega
      have sk := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (Nat.le_of_not_lt low) hs
      have good : hi.testBit k=true ∧ (cube lo hi k).testBit t=true := by
        cases l : lo.testBit k <;> cases h : hi.testBit k <;>
          simp_all [cube,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.le_of_not_lt low,show s-2^k<2^k from tl,t]
      have same (i : Fin k) : s.testBit i.val=t.testBit i.val := by
        conv_lhs => rw [show s=2^k*1+t by dsimp [t]; omega]
        rw [Nat.testBit_two_pow_mul_add _ tl,if_pos i.isLt]
      intro i
      induction i using Fin.lastCases with
      | last => simp [sk,good.1]
      | cast i => simpa only [Fin.val_castSucc,same] using ih t tl good.2 i

private def boxLo (k b : Nat) := b % (2^k)
private def boxHi (k b : Nat) := (b >>> k) % (2^k)
private def boxWord (k b : Nat) := b >>> (2*k)

private def maskOf (k : Nat) : List Nat → Nat
  | [] => 0
  | b::bs => cube (boxLo k b) (boxHi k b) k ||| maskOf k bs

private theorem findBox {k s : Nat} (boxes : List Nat) (hit : (maskOf k boxes).testBit s=true) :
    ∃ b∈boxes, (cube (boxLo k b) (boxHi k b) k).testBit s=true := by
  induction boxes with
  | nil => simp [maskOf] at hit
  | cons b bs ih =>
    rcases Bool.or_eq_true_iff.mp (by simpa only [maskOf,Nat.testBit_or] using hit) with h | h
    · exact ⟨b,by simp,h⟩
    · obtain ⟨c,hc,good⟩ := ih h
      exact ⟨c,by simp [hc],good⟩

private def Enough (n pattern k host : Nat) (targets : List Nat) (mask : Nat) : Prop :=
  ∀ s, s < 2^k → mask.testBit s=true → ∃ lo hi w, Fits k s lo hi ∧
    instruction n pattern k host lo hi w targets=true

private theorem group {n pattern k host targets} (boxes : List Nat)
    (pass : boxes.all (fun b => instruction n pattern k host
      (boxLo k b) (boxHi k b) (boxWord k b) targets)=true) : Enough n pattern k host targets (maskOf k boxes) := by
  intro s small hit
  obtain ⟨b,hb,ok⟩ := findBox boxes hit
  exact ⟨_,_,_,cube_sound _ _ _ _ small ok,List.all_eq_true.mp pass b hb⟩

private theorem merge {n pattern k host targets a b} (x : Enough n pattern k host targets a)
    (y : Enough n pattern k host targets b) : Enough n pattern k host targets (a ||| b) := by
  intro s small hit
  rcases Bool.or_eq_true_iff.mp (by simpa only [Nat.testBit_or] using hit) with h | h
  · exact x s small h
  · exact y s small h

private theorem grow {n pattern k host total : Nat} {targets : List Nat}
    (small : k<2*n-1) (rest : ∀ h∈targets, Good n pattern (k+1) h)
    (ready : Enough n pattern k host targets total) (full : total=2^(2^k)-1) :
    Good n pattern k host := by
  classical
  intro C ht l covered
  obtain ⟨v,hv⟩ : ∃ x, x ∉ Set.range l := by
    by_contra! sur
    have card := Fintype.card_le_of_surjective l (fun x => sur x)
    simp only [Fintype.card_fin] at card
    omega
  let hood (i : Fin k) := decide (C.Adj v (l i))
  let vbits := BitVec.ofBoolListLE (List.ofFn hood)
  let s : Fin (2^k) := ⟨vbits.toNat,by simpa [vbits] using vbits.isLt⟩
  have chosen (i : Fin k) : s.val.testBit i.val = decide (C.Adj v (l i)) := by
    change (BitVec.ofBoolListLE (List.ofFn hood)).getLsbD i.val = _
    rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD]
    simp [hood,i.isLt]
  obtain ⟨lo,hi,w,fit,pass⟩ := ready s.val s.isLt (by simp [full,s.isLt])
  have lower (i : Fin k) (mem : lo.testBit i.val=true) : C.Adj v (l i) :=
    of_decide_eq_true ((chosen i).symm ▸ (fit i).1 mem)
  have upper (i : Fin k) (adj : C.Adj v (l i)) : hi.testBit i.val=true :=
    (fit i).2 (by simp [chosen,adj])
  apply instruction_sound rest pass C ht (Fin.Embedding.snoc l hv)
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j =>
      simpa [Fin.Embedding.snoc_last,Fin.Embedding.snoc_castSucc,expanded,ne_of_lt j.isLt] using upper j
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simpa [Fin.Embedding.snoc_last,Fin.Embedding.snoc_castSucc,expanded,ne_of_lt i.isLt]
        using (fun h : C.Adj (l i) v => upper i h.symm)
    | cast j =>
      rw [Fin.Embedding.snoc_castSucc,Fin.Embedding.snoc_castSucc]
      intro adj
      have no : ¬(lo.testBit i.val=true ∧ lo.testBit j.val=true) := fun hh =>
        C.isIndepSet_neighborSet_of_triangleFree ht v (lower i hh.1) (lower j hh.2) adj.ne adj
      cases a : lo.testBit i.val <;> cases b : lo.testBit j.val <;>
        simp_all [expanded,ne_of_lt i.isLt,ne_of_lt j.isLt]

private theorem start {n pattern : Nat} (ok : Good n pattern 0 0)
    (C : SimpleGraph (Fin (2*n-1))) (ht : C.CliqueFree 3) : Found n pattern C := by
  apply ok C ht ⟨Fin.elim0,fun i => Fin.elim0 i⟩
  intro i
  exact Fin.elim0 i

namespace Order4
private def hosts7 : List Nat := []
private theorem level7 : ∀ h∈hosts7, Good 4 2048 7 h := by
  simp [hosts7]

private def b6_0_0 : List Nat := [
212343680,207896128,170401747,210376576,139075557,205929792,67518411,203840704,136732636,100941767,140787670,33972173,
138821594]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b6_0_0ok : Enough 4 2048 6 0xe000e003100310031000e hosts7 (maskOf 6 b6_0_0) :=
  group b6_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host6_0 : Good 4 2048 6 0xe000e003100310031000e :=
  grow (by decide) level7 b6_0_0ok (by decide +kernel)

private def hosts6 : List Nat := [0xe000e003100310031000e]
private theorem level6 : ∀ h∈hosts6, Good 4 2048 6 h := by
  intro h hh
  simp only [hosts6,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl
  · exact host6_0

private def b5_0_0 : List Nat := [
11300536768,43093664,25235431,43585312,42571360,34705402,8493037,16879595,35196918,34183164]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b5_0_0ok : Enough 4 2048 5 0xe001100110011000e hosts6 (maskOf 5 b5_0_0) :=
  group b5_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host5_0 : Good 4 2048 5 0xe001100110011000e :=
  grow (by decide) level6 b5_0_0ok (by decide +kernel)

private def b5_1_0 : List Nat := [
25823219,25855616,34247968,25757677,6722027749,6753485162,11157504908,7148176177,11174707922,33725632,16879598,16944896,
26387552,34146293,33656826]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b5_1_0ok : Enough 4 2048 5 0x30006000900180014 hosts6 (maskOf 5 b5_1_0) :=
  group b5_1_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host5_1 : Good 4 2048 5 0x30006000900180014 :=
  grow (by decide) level6 b5_1_0ok (by decide +kernel)

private def hosts5 : List Nat := [0xe001100110011000e,0x30006000900180014]
private theorem level5 : ∀ h∈hosts5, Good 4 2048 5 h := by
  intro h hh
  simp only [hosts5,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl
  · exact host5_0
  · exact host5_1

private def b4_0_0 : List Nat := [
140779744,8676176,6308855,8799120,8545584,4219899,2123261]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b4_0_0ok : Enough 4 2048 4 281479271743502 hosts5 (maskOf 4 b4_0_0) :=
  group b4_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host4_0 : Good 4 2048 4 281479271743502 :=
  grow (by decide) level5 b4_0_0ok (by decide +kernel)

private def b4_1_0 : List Nat := [
109322384,105382496,677527637,677650483,134627959,640172202,140526267,577257676,140772061,140779758,6562303]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b4_1_0ok : Enough 4 2048 4 0x6000900090006 hosts5 (maskOf 4 b4_1_0) :=
  group b4_1_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host4_1 : Good 4 2048 4 0x6000900090006 :=
  grow (by decide) level5 b4_1_0ok (by decide +kernel)

private def hosts4 : List Nat := [281479271743502,0x6000900090006]
private theorem level4 : ∀ h∈hosts4, Good 4 2048 4 h := by
  intro h hh
  simp only [hosts4,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl
  · exact host4_0
  · exact host4_1

private def b3_0_0 : List Nat := [
10029104,1640456,9537581,9476123,102591]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b3_0_0ok : Enough 4 2048 3 4295032838 hosts4 (maskOf 3 b3_0_0) :=
  group b3_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host3_0 : Good 4 2048 3 4295032838 :=
  grow (by decide) level4 b3_0_0ok (by decide +kernel)

private def hosts3 : List Nat := [4295032838]
private theorem level3 : ∀ h∈hosts3, Good 4 2048 3 h := by
  intro h hh
  simp only [hosts3,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl
  · exact host3_0

private def b2_0_0 : List Nat := [
16900,16424,1071]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b2_0_0ok : Enough 4 2048 2 65538 hosts3 (maskOf 2 b2_0_0) :=
  group b2_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host2_0 : Good 4 2048 2 65538 :=
  grow (by decide) level3 b2_0_0ok (by decide +kernel)

private def hosts2 : List Nat := [65538]
private theorem level2 : ∀ h∈hosts2, Good 4 2048 2 h := by
  intro h hh
  simp only [hosts2,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl
  · exact host2_0

private def b1_0_0 : List Nat := [
130]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b1_0_0ok : Enough 4 2048 1 0 hosts2 (maskOf 1 b1_0_0) :=
  group b1_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host1_0 : Good 4 2048 1 0 :=
  grow (by decide) level2 b1_0_0ok (by decide +kernel)

private def hosts1 : List Nat := [0]
private theorem level1 : ∀ h∈hosts1, Good 4 2048 1 h := by
  intro h hh
  simp only [hosts1,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl
  · exact host1_0

private def b0_0_0 : List Nat := [
0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b0_0_0ok : Enough 4 2048 0 0 hosts1 (maskOf 0 b0_0_0) :=
  group b0_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host0_0 : Good 4 2048 0 0 :=
  grow (by decide) level1 b0_0_0ok (by decide +kernel)

private def hosts0 : List Nat := [0]
private theorem level0 : ∀ h∈hosts0, Good 4 2048 0 h := by
  intro h hh
  simp only [hosts0,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl
  · exact host0_0

theorem embedding (C : SimpleGraph (Fin 7)) (ht : C.CliqueFree 3) :
    Found 4 2048 C := start host0_0 C ht

end Order4
namespace Order5
private def hosts9 : List Nat := []
private theorem level9 : ∀ h∈hosts9, Good 5 540672 9 h := by
  simp [hosts9]

private def b8_0_0 : List Nat := [
70972078336,72689507840,2252603143,70940620032,70907196160,45170818858,45137395500,45202276134,2221145867,10744102685,70405844224]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_0_0ok : Enough 5 540672 8 0x1e001e001e00e100e100e100e1001e hosts9 (maskOf 8 b8_0_0) :=
  group b8_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host8_0 : Good 5 540672 8 0x1e001e001e00e100e100e100e1001e :=
  grow (by decide) level9 b8_0_0ok (by decide +kernel)

private def b8_1_0 : List Nat := [
1692663684,38162005794,44608651017,38900162048,64498168064,21716235520,11423317904,47292972032,64569331200,63495601985,4507406080,62346362647,
30211943168,21118844904,13092893440]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_1_0ok : Enough 5 540672 8 0x540083000e008a003100a10070004c hosts9 (maskOf 8 b8_1_0) :=
  group b8_1_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host8_1 : Good 5 540672 8 0x540083000e008a003100a10070004c :=
  grow (by decide) level9 b8_1_0ok (by decide +kernel)

private def hosts8 : List Nat := [0x1e001e001e00e100e100e100e1001e,0x540083000e008a003100a10070004c]
private theorem level8 : ∀ h∈hosts8, Good 5 540672 8 h := by
  intro h hh
  simp only [hosts8,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl
  · exact host8_0
  · exact host8_1

private def b7_0_0 : List Nat := [
15453976192,15579314560,11300568998,555286411,65051994623744,15595535488,15587670656,13448052678,2686025629,11292704682,563150727,11284348844,
13440188362,13431832524]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_0_0ok : Enough 5 540672 7 0x1e001e0061006100610061001e hosts8 (maskOf 7 b7_0_0) :=
  group b7_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host7_0 : Good 5 540672 7 0x1e001e0061006100610061001e :=
  grow (by decide) level8 b7_0_0ok (by decide +kernel)

private def b7_1_0 : List Nat := [
2855305155,13827204864,7150337972,13834483840,13020790669,5002887096,3139000704,9012576210,992626560,2996404140,5002788805,7150272457,
2988015516,11160059874,0xbb2a19082a14,0xbb2a11882c18,0xbb2299083224,0xbb2291883428,11016372119,11150589851,0x93229b880a95,0xa32b91880b16,0xa32b99080d1a,0x9322b9880c99,
0x932a1b8812a5,8869412775,9003630507,0xa33a9908152a]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_1_0ok : Enough 5 540672 7 0x3000e000e003100310070004c hosts8 (maskOf 7 b7_1_0) :=
  group b7_1_0 (by decide +kernel)

private def b7_1_1 : List Nat := [
0xa33a91881326,0x932a398814a9]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_1_1ok : Enough 5 540672 7 0x3000e000e003100310070004c hosts8 (maskOf 7 b7_1_1) :=
  group b7_1_1 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host7_1 : Good 5 540672 7 0x3000e000e003100310070004c :=
  grow (by decide) level8 (merge b7_1_0ok b7_1_1ok) (by decide +kernel)

private def hosts7 : List Nat := [0x1e001e0061006100610061001e,0x3000e000e003100310070004c]
private theorem level7 : ∀ h∈hosts7, Good 5 540672 7 h := by
  intro h hh
  simp only [hosts7,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl
  · exact host7_0
  · exact host7_1

private def b6_0_0 : List Nat := [
3326622528,869835868032,3357957312,2825142246,138821579,3362012736,3360046400,140787655,671506397,2823176170,2821087212]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b6_0_0ok : Enough 5 540672 6 0x1e0021002100210021001e hosts7 (maskOf 6 b6_0_0) :=
  group b6_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host6_0 : Good 5 540672 6 0x1e0021002100210021001e :=
  grow (by decide) level7 b6_0_0ok (by decide +kernel)

private def b6_1_0 : List Nat := [
576811180928,604084767808,2754093015,2250907627,713449468,2787647451,3050139829394,3050131965204,2365464266134,3049974679064,2365621552794,2365629417244,
2789744605,3034033703074,2363316814279,2363474100939,2363481965389,3034025838884,2389780744874,3068859121859,869835868062,2217353191,2253004781,861782805422,
860776050037,3068857155909,3068794241609,867724174287]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b6_1_0ok : Enough 5 540672 6 0xe000e003100310031000e hosts7 (maskOf 6 b6_1_0) :=
  group b6_1_0 (by decide +kernel)

private def b6_1_1 : List Nat := [
2381665012914,860772117747,2381672877364,1787052022,2381767249464,2339252241619,2339260106069,2339354478169,2379517561059,2379525425509,2379619797609,2389788609324,
860681678457,1250312186,2389623458214,3033868552744]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b6_1_1ok : Enough 5 540672 6 0xe000e003100310031000e hosts7 (maskOf 6 b6_1_1) :=
  group b6_1_1 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host6_1 : Good 5 540672 6 0xe000e003100310031000e :=
  grow (by decide) level7 (merge b6_1_0ok b6_1_1ok) (by decide +kernel)

private def b6_2_0 : List Nat := [
2940010103680,105529315,2888195136,713449436,861782805410,2253012978,2894913637120,749098176,2718326733,2629269193157,2629237736137,2912730746132,
2912604917272,2364996584854,2365122414234,2665639707989,2665702622809,1745108951,713302005,2379525425509,2379619797609,713433081,1208369115]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b6_2_0ok : Enough 5 540672 6 0x3000e001100110030002c hosts7 (maskOf 6 b6_2_0) :=
  group b6_2_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host6_2 : Good 5 540672 6 0x3000e001100110030002c :=
  grow (by decide) level7 b6_2_0ok (by decide +kernel)

private def hosts6 : List Nat := [0x1e0021002100210021001e,0xe000e003100310031000e,0x3000e001100110030002c]
private theorem level6 : ∀ h∈hosts6, Good 5 540672 6 h := by
  intro h hh
  simp only [hosts6,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl | rfl
  · exact host6_0
  · exact host6_1
  · exact host6_2

private def b5_0_0 : List Nat := [
11300537280,705793696,35196903,696915296,26349555,706285344,697437600,167876605]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b5_0_0ok : Enough 5 540672 5 0x1000100010001001e hosts6 (maskOf 5 b5_0_0) :=
  group b5_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host5_0 : Good 5 540672 5 0x1000100010001001e :=
  grow (by decide) level6 b5_0_0ok (by decide +kernel)

private def b5_1_0 : List Nat := [
45660275136,9287270944,436277239,41490711155,80020013155,77335792045,71430210130,41492185781,41507914553,77470008220,11300537310,80019521701,
80003793193,77352995047,77337266539,10772613615,71431684756,77487211222,71447413528,77471482714,302092283,167876605]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b5_1_0ok : Enough 5 540672 5 0xe001100110011000e hosts6 (maskOf 5 b5_1_0) :=
  group b5_1_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host5_1 : Good 5 540672 5 0xe001100110011000e :=
  grow (by decide) level6 b5_1_0ok (by decide +kernel)

private def b5_2_0 : List Nat := [
75441504352,75740779136,41113223530,41081766117,45517243276,293736443,75867652384,41507914545,45534446290,75851892928,78006716845,77754536629,
420087799,78006747598,77754045043,77723140954,169412605,75701488384,34705406,545363951]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b5_2_0ok : Enough 5 540672 5 0x30006000900180014 hosts6 (maskOf 5 b5_2_0) :=
  group b5_2_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host5_2 : Good 5 540672 5 0x30006000900180014 :=
  grow (by decide) level6 b5_2_0ok (by decide +kernel)

private def hosts5 : List Nat := [0x1000100010001001e,0xe001100110011000e,0x30006000900180014]
private theorem level5 : ∀ h∈hosts5, Good 5 540672 5 h := by
  intro h hh
  simp only [hosts5,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl | rfl
  · exact host5_0
  · exact host5_1
  · exact host5_2

private def b4_0_0 : List Nat := [
677650656,140779536,671498871,641892403,642261077,646193305,677397179,677642973,8798975]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b4_0_0ok : Enough 5 540672 4 281479271743502 hosts5 (maskOf 4 b4_0_0) :=
  group b4_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host4_0 : Good 5 540672 4 281479271743502 :=
  grow (by decide) level5 b4_0_0ok (by decide +kernel)

private def b4_1_0 : List Nat := [
646193296,642253408,1214398549,1214521395,671498871,1177043114,677397179,1114128588,677642973,677650670,8798975]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b4_1_0ok : Enough 5 540672 4 0x6000900090006 hosts5 (maskOf 4 b4_1_0) :=
  group b4_1_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host4_1 : Good 5 540672 4 0x6000900090006 :=
  grow (by decide) level5 b4_1_0ok (by decide +kernel)

private def hosts4 : List Nat := [281479271743502,0x6000900090006]
private theorem level4 : ∀ h∈hosts4, Good 5 540672 4 h := by
  intro h hh
  simp only [hosts4,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl
  · exact host4_0
  · exact host4_1

private def b3_0_0 : List Nat := [
10029104,1640456,9537581,9476123,102591]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b3_0_0ok : Enough 5 540672 3 4295032838 hosts4 (maskOf 3 b3_0_0) :=
  group b3_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host3_0 : Good 5 540672 3 4295032838 :=
  grow (by decide) level4 b3_0_0ok (by decide +kernel)

private def hosts3 : List Nat := [4295032838]
private theorem level3 : ∀ h∈hosts3, Good 5 540672 3 h := by
  intro h hh
  simp only [hosts3,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl
  · exact host3_0

private def b2_0_0 : List Nat := [
16900,16424,1071]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b2_0_0ok : Enough 5 540672 2 65538 hosts3 (maskOf 2 b2_0_0) :=
  group b2_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host2_0 : Good 5 540672 2 65538 :=
  grow (by decide) level3 b2_0_0ok (by decide +kernel)

private def hosts2 : List Nat := [65538]
private theorem level2 : ∀ h∈hosts2, Good 5 540672 2 h := by
  intro h hh
  simp only [hosts2,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl
  · exact host2_0

private def b1_0_0 : List Nat := [
130]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b1_0_0ok : Enough 5 540672 1 0 hosts2 (maskOf 1 b1_0_0) :=
  group b1_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host1_0 : Good 5 540672 1 0 :=
  grow (by decide) level2 b1_0_0ok (by decide +kernel)

private def hosts1 : List Nat := [0]
private theorem level1 : ∀ h∈hosts1, Good 5 540672 1 h := by
  intro h hh
  simp only [hosts1,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl
  · exact host1_0

private def b0_0_0 : List Nat := [
0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b0_0_0ok : Enough 5 540672 0 0 hosts1 (maskOf 0 b0_0_0) :=
  group b0_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host0_0 : Good 5 540672 0 0 :=
  grow (by decide) level1 b0_0_0ok (by decide +kernel)

private def hosts0 : List Nat := [0]
private theorem level0 : ∀ h∈hosts0, Good 5 540672 0 h := by
  intro h hh
  simp only [hosts0,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl
  · exact host0_0

theorem embedding (C : SimpleGraph (Fin 9)) (ht : C.CliqueFree 3) :
    Found 5 540672 C := start host0_0 C ht

end Order5
namespace Order6
private def hosts11 : List Nat := []
private theorem level11 : ∀ h∈hosts11, Good 6 541065248 11 h := by
  simp [hosts11]

private def b10_0_0 : List Nat := [
23033923500032,22447686366208,21237556115456,0xb48427fc400,3242714988291,457485319221,22447717821440,0xea8625ffc9a,0xc8a643ffc6c,20412922592465,22712902722560,22713437492224,
0xe8a427ffca6,22310312418304,0xa08427ffc0f,22584053687296,22584588456960,22713468947456,0xc6a825ffc72,22584619912192,320079920185,0xea8643ffc9c,0xc8a625ffc6a,0xca8427ffc56,
723236420637,594387401773,23299140286464,23170291005440]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b10_0_0ok : Enough 6 541065248 10 0x3e003e003e003e03c103c103c103c103c1003e hosts11 (maskOf 10 b10_0_0) :=
  group b10_0_0 (by decide +kernel)

private def b10_0_1 : List Nat := [
457453861939,0xc6a843ffc74,0xc4a863ffc78,722670189591,593821170727,0xac8427ffc4e,723204963355,594355944491,0xc8a427ffc66,0xca8625ffc5a,0xca8643ffc5c,0xe6a825ffcb2,
0xe4a863ffcb8,0xea8427ffc96,0xe8a625ffcaa,0xae8427ffc8e,0xe8a643ffcac,0xe6a843ffcb4]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b10_0_1ok : Enough 6 541065248 10 0x3e003e003e003e03c103c103c103c103c1003e hosts11 (maskOf 10 b10_0_1) :=
  group b10_0_1 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host10_0 : Good 6 541065248 10 0x3e003e003e003e03c103c103c103c103c1003e :=
  grow (by decide) level11 (merge b10_0_0ok b10_0_1ok) (by decide +kernel)

private def b10_1_0 : List Nat := [
0xe4ca03ffc42,9510166985737,456384314416,0xc2ea05ffc84,0xe54a03d7000,20137059024130,9570296504320,0xa94427f4400,18369241217024,0xe2ca05ffc44,17817778490368,0xc34a05e6800,
7319733664785,20154238342144,20550361546497,593821170728,20953113296088,21185031017988,17946625703426,0xc953072dc00]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b10_1_0ok : Enough 6 541065248 10 0x270027001e001e031800e100e103c003c00318 hosts11 (maskOf 10 b10_1_0) :=
  group b10_1_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host10_1 : Good 6 541065248 10 0x270027001e001e031800e100e103c003c00318 :=
  grow (by decide) level11 b10_1_0ok (by decide +kernel)

private def b10_2_0 : List Nat := [
20109582138377,17782250929188,5687086152770,0xa52209ffc11,0xa52629ffe08,0xc34a1367800,0xa54629f1400,3103669615904,3110648668160,0xc34649e8c00,3102059003396,5721445851136,
0xa4e629ffc82,18370115399680,20706042832896,3103667518593,0xa52211ffd02,9574054080512,7922639654912,17782852812120,0xa52c11ffe40,20291612288000,20111226305584,9710497242112,
0xb14c05e6800]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b10_2_0ok : Enough 6 541065248 10 0x4c002a0007021201140061030102a001c00098 hosts11 (maskOf 10 b10_2_0) :=
  group b10_2_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host10_2 : Good 6 541065248 10 0x4c002a0007021201140061030102a001c00098 :=
  grow (by decide) level11 b10_2_0ok (by decide +kernel)

private def hosts10 : List Nat := [0x3e003e003e003e03c103c103c103c103c1003e,0x270027001e001e031800e100e103c003c00318,0x4c002a0007021201140061030102a001c00098]
private theorem level10 : ∀ h∈hosts10, Good 6 541065248 10 h := by
  intro h hh
  simp only [hosts10,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl | rfl
  · exact host10_0
  · exact host10_1
  · exact host10_2

private def b9_0_0 : List Nat := [
5128603552256,5096257597952,3412898348658,5128611415552,2757647924751,0x4c3b2a190807c00,4029099802268,4478066491192,3996745989798,5062165764608,5128469860864,3066885562880,
5096391289344,5062173627904,5027822276096,5096399152640,3447131733612,4578714058518,114371329589,180801240603,3996879683242,2963806355022,4546643361580,3962654162610,
180667547159,148455292455,3412906212980,180809104925]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b9_0_0ok : Enough 6 541065248 9 0x3e003e003e01c101c101c101c101c1003e hosts10 (maskOf 9 b9_0_0) :=
  group b9_0_0 (by decide +kernel)

private def b9_0_1 : List Nat := [
3928310677176,3479336123994,148588985899,3996887547564,3962662026932,80019979833,3479202430550,2998166093454,4029091937946,3479343988316,4512409976626,3446990175846,
3447123869290,3378554863224,148596850221,4512417840948,4028958244502,3032525831950,4578847751962,4578855616284,4546501803814,4546635497258,114363465267]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b9_0_1ok : Enough 6 541065248 9 0x3e003e003e01c101c101c101c101c1003e hosts10 (maskOf 9 b9_0_1) :=
  group b9_0_1 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host9_0 : Good 6 541065248 9 0x3e003e003e01c101c101c101c101c1003e :=
  grow (by decide) level10 (merge b9_0_0ok b9_0_1ok) (by decide +kernel)

private def b9_1_0 : List Nat := [
3900386049684,4716294562304,4999897536000,2800740728364,4723164265472,4402904563225,4712142195200,3350496542284,808128610083,2800882286136,3350630235732,4714281292288,
4999763846656,4999905398272,5231690630914,3350638100056,4407056924173,2800874421812,808262303555,4405043658261,4003188440966,2903810506538,2869584985906,774036782979,
2903676813094,3453566320458,3419340799826,154897743623]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b9_1_0ok : Enough 6 541065248 9 0x3001e001e001e00e100e100e101e0011c hosts10 (maskOf 9 b9_1_0) :=
  group b9_1_0 (by decide +kernel)

private def b9_1_1 : List Nat := [
3453432627014,155031437067,120805916435]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b9_1_1ok : Enough 6 541065248 9 0x3001e001e001e00e100e100e101e0011c hosts10 (maskOf 9 b9_1_1) :=
  group b9_1_1 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host9_1 : Good 6 541065248 9 0x3001e001e001e00e100e100e101e0011c :=
  grow (by decide) level10 (merge b9_1_0ok b9_1_1ok) (by decide +kernel)

private def b9_2_0 : List Nat := [
4723164265472,4965967117824,2826492182073,4719011855360,3453432627014,1892487265941,1858555346602,4486656281088,5238560276225,1907773931337,157045219328,2442536681074,
318106493457,1826351480524,1357884423973,5227538269954,4452297065984,4956671169033,122686001152,1894626360979,4712142195460,2410458644148,0x2cc3b219083c301,1894928350828,
4721150966784,2904389844696,4965974965760,2442108862093]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b9_2_0ok : Enough 6 541065248 9 0x7001e001e001e00e100e101e001e00118 hosts10 (maskOf 9 b9_2_0) :=
  group b9_2_0 (by decide +kernel)

private def b9_2_1 : List Nat := [
3382958882470,1892780867178,2444684164724,4965833457152,1824203996874,2373959810770,3930567212646,808128610083,2457529745233,1860702830252,2408311160498,4003758866040,
3454137269944,774036782979,2376107294420,2833337286342,3926003809945]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b9_2_1ok : Enough 6 541065248 9 0x7001e001e001e00e100e101e001e00118 hosts10 (maskOf 9 b9_2_1) :=
  group b9_2_1 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host9_2 : Good 6 541065248 9 0x7001e001e001e00e100e101e001e00118 :=
  grow (by decide) level10 (merge b9_2_0ok b9_2_1ok) (by decide +kernel)

private def b9_3_0 : List Nat := [
3930567212610,2377541746185,114096078384,3348599668356,3937009580032,3352894583808,2390426636288,1829933415953,4486656281088,148455292456,0xcc3b2a190804e00,2905824272896,
3382958882434,4712142195460,0x4ac3b2190823d06,0x2cc3b219083c321,4590162705408,5227538269954,0x4aa1c10bb03b0d8,1838523350791,2903676813094]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b9_3_0ok : Enough 6 541065248 9 0x27001e001e011800e100e101c001c00118 hosts10 (maskOf 9 b9_3_0) :=
  group b9_3_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host9_3 : Good 6 541065248 9 0x27001e001e011800e100e101c001c00118 :=
  grow (by decide) level10 b9_3_0ok (by decide +kernel)

private def b9_4_0 : List Nat := [
2375528480265,148455292452,2832944594562,1926847004177,3900393914120,2837239532032,157045219328,120538529538,4135164591104,4521007632896,3928310677040,4447994379908,
4452289201664,4574946524742,4575349026816,3855581445706,3855984011264,3936900532736,0x2cc3b219083c3a1,0x14c3b2a19080984c,0x1343caa19080a452,4445846896220,4579703688704,2410752070656]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b9_4_0ok : Enough 6 541065248 9 0x2a0007001e01140061014100e001c00098 hosts10 (maskOf 9 b9_4_0) :=
  group b9_4_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host9_4 : Good 6 541065248 9 0x2a0007001e01140061014100e001c00098 :=
  grow (by decide) level10 b9_4_0ok (by decide +kernel)

private def hosts9 : List Nat := [0x3e003e003e01c101c101c101c101c1003e,0x3001e001e001e00e100e100e101e0011c,0x7001e001e001e00e100e101e001e00118,0x27001e001e011800e100e101c001c00118,0x2a0007001e01140061014100e001c00098]
private theorem level9 : ∀ h∈hosts9, Good 6 541065248 9 h := by
  intro h hh
  simp only [hosts9,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl
  · exact host9_0
  · exact host9_1
  · exact host9_2
  · exact host9_3
  · exact host9_4

private def b8_0_0 : List Nat := [
4763807605865984,1144711931136,1136625441024,853224587122,689411981071,1144713896704,0xea8643ff9c,861782933356,1128102481152,1144678508800,758131454208,1136658863360,
1128104446720,1119516608256,20004994873,1136660828928,999186497446,45166886679,869834030938,999219920810,853226553204,990663540658,37113823015,740951588686,
999221886892,990665506740,45202276125,982077669304]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_0_0ok : Enough 6 541065248 8 0x3e003e00c100c100c100c100c1003e hosts9 (maskOf 8 b8_0_0) :=
  group b8_0_0 (by decide +kernel)

private def b8_0_1 : List Nat := [
869800607574,45200310043,37147246379,844638715768,37149212461,28592832309,749541523342,0xea8427ff96,0xea8625ff9a,869835997020,861747543910,861780967274,
28590866227]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_0_1ok : Enough 6 541065248 8 0x3e003e00c100c100c100c100c1003e hosts9 (maskOf 8 b8_0_1) :=
  group b8_0_1 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host8_0 : Good 6 541065248 8 0x3e003e00c100c100c100c100c1003e :=
  grow (by decide) level9 (merge b8_0_0ok b8_0_1ok) (by decide +kernel)

private def b8_1_0 : List Nat := [
0xa8650ec021e00,0xb0ec86420e100,991231868781,38329909234,199820967837,457483353911,328667889499,999723368398,854329655211,836013522812,708334321607,973452476348,
999821803381,999821934457,0x50864eca022323,0x30862eca042222,9718646796729404,0x30826eca044242,0x50846eca024343,9728954718248028,0x50842eca066262,0x70842eca066666,0x70842eac066a6a,0x70842aec067272,
9717822163787037,999821672307,0x30eca864200303,0x50eca864200707]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_1_0ok : Enough 6 541065248 8 0x1e001e001e00e100e100e100e1001e hosts9 (maskOf 8 b8_1_0) :=
  group b8_1_0 (by decide +kernel)

private def b8_1_1 : List Nat := [
0x50eca846200b0b,0x50eca486201313,0x70eca864202727,4763807605866046,0x70eac864204747,594385436463,0x50e0c8462a4a4a,0x50e0c4862a5252,0x50ec08642a2626,0x50ec08462a2a2a,0x50ec04862a3232,0x50e0c8642a4646,
861747543918,853157740406,0x500ec8642a8686,0x30eca862400505,0x30eca826400909,0x30eca286401111,4763129573678879,182641098557,191231033181,9586403248334181,9586405764917609,9586437977174385,
9817300690183589,9817303206767017,9817335419023793,9829670196004293]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_1_1ok : Enough 6 541065248 8 0x1e001e001e00e100e100e100e1001e hosts9 (maskOf 8 b8_1_1) :=
  group b8_1_1 (by decide +kernel)

private def b8_1_2 : List Nat := [
9829672712587721,9829704924844497,0x70428a0ec6d8d8,0x50486eca028383,0x50eca842600d0d,0x50eca428601919,0x50eca482601515,0x70eca842602d2d,0x70eca482603535,0x70eca428603939,0x70eac842604d4d,0x70eac482605555,
0x70eac428605959,982641803111,0x50ec08426a2c2c,0x50ec04826a3434,0x50ec04286a3838,0x50e0c8426a4c4c,0x50e0c4826a5454,0x50e0c4286a5858,0x500ec8426a8c8c,0x500ec4826a9494,0x500ec4286a9898,0x50482eca06a2a2,
0x70482eca06a6a6,0x50428eca06c2c2,0x70428eca06c6c6,4688793315763685]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_1_2ok : Enough 6 541065248 8 0x1e001e001e00e100e100e100e1001e hosts9 (maskOf 8 b8_1_2) :=
  group b8_1_2 (by decide +kernel)

private def b8_1_3 : List Nat := [
0x504860eca29191,21150040038,29739974634,0x308620eca43030,9860836564962958,0x302860eca49090,29740105708,38330040308,0x508640eca23131,0x50846e0ca24949,0x508460eca25151,9718643619542582,
0x30826e0ca44848,9728895169613390,0x308260eca45050,9728951541061206,0x30862ec0a42424,0x50864ec0a22525,0x30862e0ca42828,9718587248094766,0x50842ec0a66464,0x50842e0ca66868,9717762615152399,9717818986600215,
9717822006500123,9830357390124260,0x70842ea0c66c6c,466073288535]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_1_3ok : Enough 6 541065248 8 0x1e001e001e00e100e100e100e1001e hosts9 (maskOf 8 b8_1_3) :=
  group b8_1_3 (by decide +kernel)

private def b8_1_4 : List Nat := [
0x70842ae0c67474,0x70842a0ec67878,474663223191,0x70482ea0c6acac,0x70482ae0c6b4b4,0x70482a0ec6b8b8,0x70428ea0c6cccc,0x70428ae0c6d4d4,0x70eca846202b2b,0x70eca486203333,0x70eac846204b4b,0x70eac486205353,
0x70aec846208b8b,320077954875,0x70aec486209393,337257824155,991133564886,982577184730,9830357201380066,0x500ec8462a8a8a,0x500ec4862a9292,9586403059589987,9817300501439395,9829670007260099,
0x70aec428609999,982040313786,0x50846ec0a24545,0x50486ec0a28585]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_1_4ok : Enough 6 541065248 8 0x1e001e001e00e100e100e100e1001e hosts9 (maskOf 8 b8_1_4) :=
  group b8_1_4 (by decide +kernel)

private def b8_1_5 : List Nat := [
9718646639442490,0x30826ec0a44444,9728954560961114,0x30286ec0a48484,9860895956310682,0x50482ec0a6a4a4,0x50428ec0a6c4c4,4688793252848611,845739720615,862919589811,854329786285,862919720885,
4688751037182449,0x508420eca67070,0x504820eca6b0b0,862919851961,716924256203,0x504280eca6d0d0,725514190803,9830359906707688,9830392118964464,716924387277,725514321877,0x70482eac06aaaa,
0x70482aec06b2b2,0x70428eac06caca,0x70428aec06d2d2,725514452953]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_1_5ok : Enough 6 541065248 8 0x1e001e001e00e100e100e100e1001e hosts9 (maskOf 8 b8_1_5) :=
  group b8_1_5 (by decide +kernel)

private def b8_1_6 : List Nat := [
38330171384,0x50864e0ca22929,0x50486e0ca28989,991231737707,0x30286e0ca48888,9860892936410774,973989347292,0x50482e0ca6a8a8,0x50428e0ca6c8c8,4688791302498793,0x30286eca048282,9860896113597596,
4761746021572190,0x70aec864208787,4695775323922078,602975371087,611565305743,999186497454,990596693942,0x70aec842608d8d,0x70aec482609595,844601360250]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_1_6ok : Enough 6 541065248 8 0x1e001e001e00e100e100e100e1001e hosts9 (maskOf 8 b8_1_6) :=
  group b8_1_6 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host8_1 : Good 6 541065248 8 0x1e001e001e00e100e100e100e1001e :=
  grow (by decide) level9 (merge (merge b8_1_0ok (merge b8_1_1ok b8_1_2ok)) (merge (merge b8_1_3ok b8_1_4ok) (merge b8_1_5ok b8_1_6ok))) (by decide +kernel)

private def b8_2_0 : List Nat := [
0xf06843e900,964325277453,1111965135616,699681734452,837122654040,0xf04863e500,0x2f0ca864201e00,29664608147,1161893766018,0xf08643f100,699648311084,1111998556928,
1112000521984,699683700536,837120687956,4695775323922050,862821285830,0x45086eca029c00,38220988299,837087264588,963287187225,963821960981,38187564935,854298329042,
725415755690,725382332326,862854709194,716859375538]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_2_0ok : Enough 6 541065248 8 0x3001e001e00610061006100e0009c hosts9 (maskOf 8 b8_2_0) :=
  group b8_2_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host8_2 : Good 6 541065248 8 0x3001e001e00610061006100e0009c :=
  grow (by decide) level9 b8_2_0ok (by decide +kernel)

private def b8_3_0 : List Nat := [
706623045433,0x4f0ca864201e00,862821285830,38724431872,983688242432,37113823022,464531881813,473656590227,1101728835849,70936686865,1160855675778,0xf04863e584,
30134626304,975098438400,708236148650,610527215501,699681734580,982614540122,4763129573678873,964432232306,963895492460,602472054603,0xb0ec86420e181,4695775323922054,
0x45086eca029c84,0x486430eca00f09,0x48642f0ca01711,0x45086ec0a29a82]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_3_0ok : Enough 6 541065248 8 0x7001e001e0061006100e000e00098 hosts9 (maskOf 8 b8_3_0) :=
  group b8_3_0 (by decide +kernel)

private def b8_3_1 : List Nat := [
844061998937,0x6ed08a04262726,28524019510,0x68f0ca0426b838,0x6ec90a04264746,4761486748706662,837087264716,4688747861964920,0x68ed0a0426d858,38187564935,0x90eca864202a2a,0x8aed0684202c2c,
0x90eca684203232,0x8aed0864203434,37650693966,29060890454,981500952473,473121816469,593347346221,455941947189,601937280845,699648311212,837120688084,982077669178,
973487865660,974024736604,0x6a0ec428700700,963895361386]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_3_1ok : Enough 6 541065248 8 0x7001e001e0061006100e000e00098 hosts9 (maskOf 8 b8_3_1) :=
  group b8_3_1 (by decide +kernel)

private def b8_3_2 : List Nat := [
964432363380,0x8af0c684204c4c,0x90eac684205252,593882119979,611061989259,456476720947,465066655571,845675102154,708269572018,845708525522,0x90eac864204a4a,0x8af0c864205454,
0x6b0ec864209800,725382332326]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_3_2ok : Enough 6 541065248 8 0x7001e001e0061006100e000e00098 hosts9 (maskOf 8 b8_3_2) :=
  group b8_3_2 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host8_3 : Good 6 541065248 8 0x7001e001e0061006100e000e00098 :=
  grow (by decide) level9 (merge b8_3_0ok (merge b8_3_1ok b8_3_2ok)) (by decide +kernel)

private def b8_4_0 : List Nat := [
594385436425,28524019504,846276566016,457483353873,37113823016,975098438400,894594964548,1160855675778,0x6f0ca864201e00,0xeac421ffc6,1152293001794,0x6ed08a04262700,
0xf04863e584,459630833664,4761486748706630,4695775323922054,837686761984,983688242432,725919191296,597069785088,725382332326,0xb0e8c0642d858,0xb0ec86420e1a1,458557095758,
595996049238,459093966727]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_4_0ok : Enough 6 541065248 8 0x27001e00980061006100c000c00098 hosts9 (maskOf 8 b8_4_0) :=
  group b8_4_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host8_4 : Good 6 541065248 8 0x27001e00980061006100c000c00098 :=
  grow (by decide) level9 b8_4_0ok (by decide +kernel)

private def b8_5_0 : List Nat := [
320009142043,837153849316,200320614197,321620148163,0xea50035800,432418193322,973016137550,561842455808,561668423513,304683492096,0xea4603ff8d,0x4e90c6a4029511,
0x4f08462c0a7830,0x4ec8506a206a42,414634606390,0x4f0c4a08262724,304543039442,0x4ed08a60422b09,0x4e4d00a2868782,29704978353,0x4e48c702a0d444,0x4e490260cad888,707630071635,973951729509,
432451735552,562376566784,551538655036,0x868eb0c4021a12]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_5_0ok : Enough 6 541065248 8 0x2a0007009400230085006800d00058 hosts9 (maskOf 8 b8_5_0) :=
  group b8_5_0 (by decide +kernel)

private def b8_5_1 : List Nat := [
0x4870eca4023a32,0x49064e2c0a1713,0x4490e6c20a6949,0x82e9064a0ca1a0,4761462151084658,0x48ec506a20c545,0x490e4c0a265c4c,0x44f08c602ad151,4689308711834965,0x86ae8d00421c0c,4763773818777389,4761488258657099,
551605763982,0x48f06ca0429c8c,837155946409,0x44ed00a286e8a8,0x4428e70ca02e2c,826523489280,0x8650c8e2a06141,0x484ec702a06343,0x484f00c2a65a52,0x44e8306ca09692,4688747861964984,4689306543250636,
0xea90c70700,0x484702e0ca0f0d,0x44e90260caa3a2,827064658432]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_5_1ok : Enough 6 541065248 8 0x2a0007009400230085006800d00058 hosts9 (maskOf 8 b8_5_1) :=
  group b8_5_1 (by decide +kernel)

private def b8_5_2 : List Nat := [
0x450eca0826f0b0,4695773749090195,4695516051056550,0x4508e62c0aa5a4,0x908ec6a4021919,972877725469,0xea4803ff33,0x90e8264a0c3434,321720811377,0x8e29064a0c8a8a,0x8d0ea864201e1e,415708348262,
320179011414,304542908338,29698686946,973951467341,561672617836,562209488812,0x8c684f0a02e1e1,835545333561,596671463370,0x880cb0e462e0a0,973985284041,0xea4c03ff47,
843667603353,475340865396,562275942324,0x85082e6ca01612]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_5_2ok : Enough 6 541065248 8 0x2a0007009400230085006800d00058 hosts9 (maskOf 8 b8_5_2) :=
  group b8_5_2 (by decide +kernel)

private def b8_5_3 : List Nat := [
0x8f08246ca03131,0x9046c8e2a04646,0x842906eac00e0c,0x9046a8e2c06464,0x8e29064ac08989,0x86d04e8a20c141,0x90a64e8c20c2c2,414701715354,321619754891,553216376774]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b8_5_3ok : Enough 6 541065248 8 0x2a0007009400230085006800d00058 hosts9 (maskOf 8 b8_5_3) :=
  group b8_5_3 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host8_5 : Good 6 541065248 8 0x2a0007009400230085006800d00058 :=
  grow (by decide) level9 (merge (merge b8_5_0ok b8_5_1ok) (merge b8_5_2ok b8_5_3ok)) (by decide +kernel)

private def hosts8 : List Nat := [0x3e003e00c100c100c100c100c1003e,0x1e001e001e00e100e100e100e1001e,0x3001e001e00610061006100e0009c,0x7001e001e0061006100e000e00098,0x27001e00980061006100c000c00098,0x2a0007009400230085006800d00058]
private theorem level8 : ∀ h∈hosts8, Good 6 541065248 8 h := by
  intro h hh
  simp only [hosts8,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl
  · exact host8_0
  · exact host8_1
  · exact host8_2
  · exact host8_3
  · exact host8_4
  · exact host8_5

private def b7_0_0 : List Nat := [
65051994627840,251818242688,249796619392,215445733356,11291721623,247666369920,213306146802,5001248697,247665878656,251809887360,172352995215,187385378944,
249804974720,251818733952,249805465984,217458999260,245519410048,213306638324,11300077467,9278455719,9286811563,185237897166,217450151894,11300568989,
9287303085,7148208053,215436885990,211159678968]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_0_0ok : Enough 6 541065248 7 0x3e00410041004100410041003e hosts8 (maskOf 7 b7_0_0) :=
  group b7_0_0 (by decide +kernel)

private def b7_0_1 : List Nat := [
217458507738,215445241834,7147716531]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_0_1ok : Enough 6 541065248 7 0x3e00410041004100410041003e hosts8 (maskOf 7 b7_0_1) :=
  group b7_0_1 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host7_0 : Good 6 541065248 7 0x3e00410041004100410041003e :=
  grow (by decide) level8 (merge b7_0_0ok b7_0_1ok) (by decide +kernel)

private def b7_1_0 : List Nat := [
0xbb2a19080f00,48043924140160,116518322135,148596359087,209003380732,80019488699,64472173557485,64466133760757,64465630444793,64536598556510,346526971330947,487264459686791,
487264333858187,487260307327379,628001948046247,628001822217643,346355172806946,487092661162790,487092535334186,487088508803378,284954320408221,285023039823420,343262796357954,484000284713798,
484000158885194,627280393745254,627280267916650,346526963466885]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_1_0ok : Enough 6 541065248 7 0x1e001e0061006100610061001e hosts8 (maskOf 7 b7_1_0) :=
  group b7_1_0 (by decide +kernel)

private def b7_1_1 : List Nat := [
346526711809161,346520672012433,64882486579103,45660274621,47807758301,293750455677540,64471780340711,293750958994536,64472157828587,285023031958842,343262788493892,285538428038490,
285022780300086,343262536836168,346355164942884,290486280688293,346354913285160,290486784005289,284948021086095,284954060884887,284954312543643,627482006400217,487264318129805,487259914112153,
487260291598997,628001806489261,627997779958453,627997402471609]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_1_1ok : Enough 6 541065248 7 0x1e001e0061006100610061001e hosts8 (maskOf 7 b7_1_1) :=
  group b7_1_1 (by decide +kernel)

private def b7_1_2 : List Nat := [
627486410417869,627482383887061,487092519605804,487088493074996,487088115588152,484000143156812,483996116626004,483995739139160,627280252188268,627276225657460,627275848170616,0xa3b190a831e3,
285538176379734,293579160462537,114370838455,627997795686835,627486426146251,627482399615443,82166972379,293750416355682,293578657145541,290486241366435,293578617823683,0xa3b1928832e5,
483996132354386,627276241385842,64466118031859,293756998793328]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_1_2ok : Enough 6 541065248 7 0x1e001e0061006100610061001e hosts8 (maskOf 7 b7_1_2) :=
  group b7_1_2 (by decide +kernel)

private def b7_1_3 : List Nat := [
285016740501294,346348873488432,290492823804081,285532136580942,343256497039440,293585200261329,65051994627902,627486551974855,0xa3b1a90834e9,0xa3b2990838f1,150743842767,215436885998,
213289435126,285538435903068,211150340090]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_1_3ok : Enough 6 541065248 7 0x1e001e0061006100610061001e hosts8 (maskOf 7 b7_1_3) :=
  group b7_1_3 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host7_1 : Good 6 541065248 7 0x1e001e0061006100610061001e :=
  grow (by decide) level8 (merge (merge b7_1_0ok b7_1_1ok) (merge b7_1_2ok b7_1_3ok)) (by decide +kernel)

private def b7_2_0 : List Nat := [
338280634126080,206721580941,221753964672,174786215860,243505681792,64536598556482,206462058393,221494440576,334810303868416,181219721194,206595751829,253966217666,
221628134528,243497326976,174777860012,243506172800,174786707384,9412673479,7281934291,9421029323,181211365350,179080626162]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_2_0ok : Enough 6 541065248 7 0x3001e0021002100210060005c hosts8 (maskOf 7 b7_2_0) :=
  group b7_2_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host7_2 : Good 6 541065248 7 0x3001e0021002100210060005c :=
  grow (by decide) level8 b7_2_0ok (by decide +kernel)

private def b7_3_0 : List Nat := [
479018122481408,176655761337,9412673479,9546889216,9278455726,211428102784,241072469129,15586687121,64882486579097,64536598556486,334810343189826,176933175282,
221494440644,211015499737,7399437312,337015909418889,337009869622161,113985486773,174777860076,209280651648,253706695106,334810303868484,0xba190b283c38,0xa1b90b2813a6,
148470529963,48043924140225,116132970453,600028582445952]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_3_0ok : Enough 6 541065248 7 0x7001e00210021006000600058 hosts8 (maskOf 7 b7_3_0) :=
  group b7_3_0 (by decide +kernel)

private def b7_3_1 : List Nat := [
768739436401962,114119180211,751215969835572,7131004854,181211365350,176924819434,768739428537900,751215961970994,148336836525,174786215924,150618013643,211159678906,
209012228028,116266663891,610993877560320,150484320205]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_3_1ok : Enough 6 541065248 7 0x7001e00210021006000600058 hosts8 (maskOf 7 b7_3_1) :=
  group b7_3_1 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host7_3 : Good 6 541065248 7 0x7001e00210021006000600058 :=
  grow (by decide) level8 (merge b7_3_0ok b7_3_1ok) (by decide +kernel)

private def b7_4_0 : List Nat := [
206712733598,320724561599488,443797010391808,212779171763,206846951342,212913389493,0xa3990b2823c1,0xba190b283c48,320615200850816,443869872830464,440499278349964,476233364322868,
459300196060305,723080201120276,477435695475478,459267983807649,476233356458290,714895889805860,0xa190bb28078e,723080169662738,64466134252342,440499231163786,714895850484002,477306846458662,
0xa1bb29081cb1,477987329838749,477890693076653,78123237339]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_4_0ok : Enough 6 541065248 7 0x9000700070046003800380070 hosts8 (maskOf 7 b7_4_0) :=
  group b7_4_0 (by decide +kernel)

private def b7_4_1 : List Nat := [
80270721003,581236758348928,485028693976394,625766173976398,43771887581,45919371245,749468455015980,767672405462298,283895887637205,283928099893989,338243884162362,758768980724115,
767672397598236,338280240417687,477987314109851,758704556216739,338248028165031,477890677347755,64536204848087,485091492538577,283895871908307,484898219012321,283928084165091,64465630444793,
485028696433865,285467336063217,625766184789451,338243860569660]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_4_1ok : Enough 6 541065248 7 0x9000700070046003800380070 hosts8 (maskOf 7 b7_4_1) :=
  group b7_4_1 (by decide +kernel)

private def b7_4_2 : List Nat := [
283715123784921,283779548296425,625766176925389,64465591615100,485028646790732,283715132632668,283779557144172,758768941402773,758704516895397,283715124768090,283779549279594,64465630936442,
64471780340711,64528151783375,767575768700202]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b7_4_2ok : Enough 6 541065248 7 0x9000700070046003800380070 hosts8 (maskOf 7 b7_4_2) :=
  group b7_4_2 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host7_4 : Good 6 541065248 7 0x9000700070046003800380070 :=
  grow (by decide) level8 (merge b7_4_0ok (merge b7_4_1ok b7_4_2ok)) (by decide +kernel)

private def hosts7 : List Nat := [0x3e00410041004100410041003e,0x1e001e0061006100610061001e,0x3001e0021002100210060005c,0x7001e00210021006000600058,0x9000700070046003800380070]
private theorem level7 : ∀ h∈hosts7, Good 6 541065248 7 h := by
  intro h hh
  simp only [hosts7,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl
  · exact host7_0
  · exact host7_1
  · exact host7_2
  · exact host7_3
  · exact host7_4

private def b6_0_0 : List Nat := [
869835870080,54364625216,43088248783,53859219008,1787052021,2825019355,53326656192,53326533440,54362536512,46309473344,53861307712,2822930391,
2319613927,2825142237,54364747968,53861430464,2321825773,52789916096,1250312185,2321702891,1786929139]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b6_0_0ok : Enough 6 541065248 6 0x10001000100010001003e hosts7 (maskOf 6 b6_0_0) :=
  group b6_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host6_0 : Good 6 541065248 6 0x10001000100010001003e :=
  grow (by decide) level7 b6_0_0ok (by decide +kernel)

private def b6_1_0 : List Nat := [
3068859123584,740986849344,37149089775,3060805938029,3059799305589,3059704934009,5267882377411,7466905633223,7466874176203,7465867543763,2801999153379,2802007017829,
2802101389929,7423956003238,7423924546218,7422917913778,5267880411461,5267817497161,5088603284431,5266307548241,5087596651991,4580688267426,5087502280411,5087494416221,
827458856927,4580696131876,3060707633639,3060802005739]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b6_1_0ok : Enough 6 541065248 6 0x1e0021002100210021001e hosts7 (maskOf 6 b6_1_0) :=
  group b6_1_0 (by decide +kernel)

private def b6_1_1 : List Nat := [
28592709623,3059795373299,5096092208826,20004872187,7466870244173,7465769240153,7465863611733,2803108023409,869835870142,5096084344636,7423920614188,7422913981748,
7422819610168,4580790503976,5097193212846,4581797137456,5096186580406,11415068669]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b6_1_1ok : Enough 6 541065248 6 0x1e0021002100210021001e hosts7 (maskOf 6 b6_1_1) :=
  group b6_1_1 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host6_1 : Good 6 541065248 6 0x1e0021002100210021001e :=
  grow (by decide) level7 (merge b6_1_0ok b6_1_1ok) (by decide +kernel)

private def b6_2_0 : List Nat := [
2775669408192,2803009596928,9665928766090,9253712569165,9665425450130,9254719202645,7338056492893,9649319323810,9262772267365,7321950366573,7320440417653,3059704934009,
9209528239705,9225634368105,9226137685105,867724176367,9665928888905,9253712692110,9665425572945,9254719325590,7338056615838,9649319446625,9262772390310,9209530451740,
9225636580140,9226139897140,869835747197,45199941631]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b6_2_0ok : Enough 6 541065248 6 0x700070007003800380038 hosts7 (maskOf 6 b6_2_0) :=
  group b6_2_0 (by decide +kernel)

private def b6_2_1 : List Nat := [
3059697192764,9253708636875,9665924834060,3066747429839,9254715270355,9665421518100,9209528485530,7338052560603,3068760696279,827458856927,9225634613930,9262768335075,
9649315391780,7321946434283,9226137930930,7320436485363,869831814907,7321950489518,869835870142,3059705056954,869737442807,7320440540598,3060707633639]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b6_2_1ok : Enough 6 541065248 6 0x700070007003800380038 hosts7 (maskOf 6 b6_2_1) :=
  group b6_2_1 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host6_2 : Good 6 541065248 6 0x700070007003800380038 :=
  grow (by decide) level7 (merge b6_2_0ok b6_2_1ok) (by decide +kernel)

private def b6_3_0 : List Nat := [
9096917691136,43627323357,3060806060962,9123223962496,5002131276864,9519463793093,9519337964233,2777839961298,9115741064468,9115678150168,3059697192732,3066747429837,
2803108023393,9225770641765,9225802099305,3059799305589,3059704934009,7321914731373,7175885856960,9252580230550,5139033360286,9252643145370,7321849850343,7321912765163,
7439024041138,5120345771446,3068760696279,3068855068379]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b6_3_0ok : Enough 6 541065248 6 0x3000e001100110030002c hosts7 (maskOf 6 b6_3_0) :=
  group b6_3_0 (by decide +kernel)

private def b6_3_1 : List Nat := [
9225766709475,867724176367,3059795373299,28089393143,5120251399866,6926312279040,19501555707,9536037848405,9535943476825,869835870142]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b6_3_1ok : Enough 6 541065248 6 0x3000e001100110030002c hosts7 (maskOf 6 b6_3_1) :=
  group b6_3_1 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host6_3 : Good 6 541065248 6 0x3000e001100110030002c :=
  grow (by decide) level7 (merge b6_3_0ok b6_3_1ok) (by decide +kernel)

private def hosts6 : List Nat := [0x10001000100010001003e,0x1e0021002100210021001e,0x700070007003800380038,0x3000e001100110030002c]
private theorem level6 : ∀ h∈hosts6, Good 6 541065248 6 h := by
  intro h hh
  simp only [hosts6,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl
  · exact host6_0
  · exact host6_1
  · exact host6_2
  · exact host6_3

private def b5_0_0 : List Nat := [
45660275648,11300536352,80020013287,43371757733,43369791587,43395350825,80012149099,80011166125,45132351983,43647009329,45635668727,79735915321,
45660244925,45659261819,79760491123,79759508149,706284543]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b5_0_0ok : Enough 6 541065248 5 0x1000100010001001e hosts6 (maskOf 5 b5_0_0) :=
  group b5_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host5_0 : Good 6 541065248 5 0x1000100010001001e :=
  grow (by decide) level6 b5_0_0ok (by decide +kernel)

private def b5_1_0 : List Nat := [
73192800704,43647009312,45660244925,111831221082,114379751523,111695530413,105789948498,79760491123,111829746588,45660275678,114379260069,114363531561,
111712733415,111697004907,45132351983,45635668727,45659261819,105791423124,111846949590,105807151896,706284543,79735915321,79759508149]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b5_1_0ok : Enough 6 541065248 5 0xe001100110011000e hosts6 (maskOf 5 b5_1_0) :=
  group b5_1_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host5_1 : Good 6 541065248 5 0xe001100110011000e :=
  grow (by decide) level6 b5_1_0ok (by decide +kernel)

private def b5_2_0 : List Nat := [
109801242720,110100517504,110227390752,80020013285,80012149098,73720693644,79735915313,73696117458,110211631296,112366455213,112114274997,45660244925,
112366485966,112113783411,45660275678,112082879322,45132351983,45659261819,110061226752,45635668727,706284543]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b5_2_0ok : Enough 6 541065248 5 0x30006000900180014 hosts6 (maskOf 5 b5_2_0) :=
  group b5_2_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host5_2 : Good 6 541065248 5 0x30006000900180014 :=
  grow (by decide) level6 b5_2_0ok (by decide +kernel)

private def hosts5 : List Nat := [0x1000100010001001e,0xe001100110011000e,0x30006000900180014]
private theorem level5 : ∀ h∈hosts5, Good 6 541065248 5 h := by
  intro h hh
  simp only [hosts5,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl | rfl
  · exact host5_0
  · exact host5_1
  · exact host5_2

private def b4_0_0 : List Nat := [
677650656,140779536,671498871,641892403,642261077,646193305,677397179,677642973,8798975]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b4_0_0ok : Enough 6 541065248 4 281479271743502 hosts5 (maskOf 4 b4_0_0) :=
  group b4_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host4_0 : Good 6 541065248 4 281479271743502 :=
  grow (by decide) level5 b4_0_0ok (by decide +kernel)

private def b4_1_0 : List Nat := [
646193296,642253408,1214398549,1214521395,671498871,1177043114,677397179,1114128588,677642973,677650670,8798975]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b4_1_0ok : Enough 6 541065248 4 0x6000900090006 hosts5 (maskOf 4 b4_1_0) :=
  group b4_1_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host4_1 : Good 6 541065248 4 0x6000900090006 :=
  grow (by decide) level5 b4_1_0ok (by decide +kernel)

private def hosts4 : List Nat := [281479271743502,0x6000900090006]
private theorem level4 : ∀ h∈hosts4, Good 6 541065248 4 h := by
  intro h hh
  simp only [hosts4,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl
  · exact host4_0
  · exact host4_1

private def b3_0_0 : List Nat := [
10029104,1640456,9537581,9476123,102591]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b3_0_0ok : Enough 6 541065248 3 4295032838 hosts4 (maskOf 3 b3_0_0) :=
  group b3_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host3_0 : Good 6 541065248 3 4295032838 :=
  grow (by decide) level4 b3_0_0ok (by decide +kernel)

private def hosts3 : List Nat := [4295032838]
private theorem level3 : ∀ h∈hosts3, Good 6 541065248 3 h := by
  intro h hh
  simp only [hosts3,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl
  · exact host3_0

private def b2_0_0 : List Nat := [
16900,16424,1071]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b2_0_0ok : Enough 6 541065248 2 65538 hosts3 (maskOf 2 b2_0_0) :=
  group b2_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host2_0 : Good 6 541065248 2 65538 :=
  grow (by decide) level3 b2_0_0ok (by decide +kernel)

private def hosts2 : List Nat := [65538]
private theorem level2 : ∀ h∈hosts2, Good 6 541065248 2 h := by
  intro h hh
  simp only [hosts2,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl
  · exact host2_0

private def b1_0_0 : List Nat := [
130]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b1_0_0ok : Enough 6 541065248 1 0 hosts2 (maskOf 1 b1_0_0) :=
  group b1_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host1_0 : Good 6 541065248 1 0 :=
  grow (by decide) level2 b1_0_0ok (by decide +kernel)

private def hosts1 : List Nat := [0]
private theorem level1 : ∀ h∈hosts1, Good 6 541065248 1 h := by
  intro h hh
  simp only [hosts1,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl
  · exact host1_0

private def b0_0_0 : List Nat := [
0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem b0_0_0ok : Enough 6 541065248 0 0 hosts1 (maskOf 0 b0_0_0) :=
  group b0_0_0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
private theorem host0_0 : Good 6 541065248 0 0 :=
  grow (by decide) level1 b0_0_0ok (by decide +kernel)

private def hosts0 : List Nat := [0]
private theorem level0 : ∀ h∈hosts0, Good 6 541065248 0 h := by
  intro h hh
  simp only [hosts0,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl
  · exact host0_0

theorem embedding (C : SimpleGraph (Fin 11)) (ht : C.CliqueFree 3) :
    Found 6 541065248 C := start host0_0 C ht

end Order6
end OMA.SmallTriangleGood

-- Lean formalization by @KoaOkano.
theorem OMA.solution : OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H1_R1.H1 := by
  intro t
  fin_cases t
  · exact OMA.SmallTriangleGood.Order4.embedding
  · exact OMA.SmallTriangleGood.Order5.embedding
  · exact OMA.SmallTriangleGood.Order6.embedding
