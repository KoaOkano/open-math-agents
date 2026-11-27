import OMAReductions.R_Green14_W_3_13_R4

/-!
# The palindromic van der Waerden breakpoints for (3, 13)

Ahmed, Kullmann and Snevily, *On the van der Waerden numbers w(2; 3, t)*,
Discrete Applied Mathematics 174 (2014), §5.2, Table 6, report (142, 155).
Here true is red. A coloring must avoid red triples and blue progressions
of length thirteen. The two explicit colorings and two exhaustion trees
prove the exact spectrum for all lengths by removing symmetric endpoints.

In a reflected board, a position and its mirror share a bit. Each unit
instruction names an actual progression with just one live position. At a
leaf, a progression has no live positions. The soundness proof and all
four finite computations are checked by the Lean kernel.
-/

-- Formalization: @KoaOkano

namespace ReflectionCertificate


-- A rule requires one of the positions in its mask to have its specified color.
structure Rule where
  color : Bool
  mask : Nat
  deriving Inhabited

abbrev Board := Bool → Nat

def agrees (c : Nat → Bool) (s : Board) := ∀ b i, (s b).testBit i = true → c i = b

def marked (s : Board) (b : Bool) (i : Nat) : Board :=
  fun v => if v = b then s b ||| 2^i else s v

theorem agrees_marked {c s b i} (h : agrees c s) (hi : c i = b) :
    agrees c (marked s b i) := by
  intro v j hj
  by_cases he : v = b
  · subst v
    have upd : marked s b i b = s b ||| 2^i := by simp [marked]
    rw [upd, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hj
    rcases hj with hj | hj
    · exact h b j hj
    · simpa [of_decide_eq_true hj] using hi
  · exact h v j (by simpa [marked, he] using hj)

def live (r : Rule) (s : Board) := r.mask ^^^ (r.mask &&& s (!r.color))

def hits (c : Nat → Bool) (r : Rule) := ∃ i, r.mask.testBit i = true ∧ c i = r.color

theorem has_live {c s r} (hs : agrees c s) (hr : hits c r) :
    ∃ i, (live r s).testBit i = true ∧ c i = r.color := by
  obtain ⟨i, hm, hc⟩ := hr
  have hb : (s (!r.color)).testBit i = false := by
    cases e : (s (!r.color)).testBit i with
    | false => rfl
    | true =>
      have eq := (hs (!r.color) i e).symm.trans hc
      cases ec : r.color <;> simp [ec] at eq
  exact ⟨i, by simp [live, Nat.testBit_xor, hm, hb], hc⟩

-- Unit instructions in a chain are little-endian digits in base 16384.
def propagate (rule : Nat → Rule) : Nat → Nat → Board → Option Board
  | 0, _, s => some s
  | k+1, digits, s =>
    let r := rule (digits % 16384)
    let candidate := live r s
    let i := candidate.log2
    if candidate = 2^i then
      propagate rule k (digits / 16384) (marked s r.color i)
    else none

theorem propagate_sound {c : Nat → Bool} {rule : Nat → Rule} (hr : ∀ i, hits c (rule i))
    (k digits : Nat) (s t : Board) (hs : agrees c s)
    (pass : propagate rule k digits s = some t) : agrees c t := by
  induction k generalizing digits s with
  | zero =>
    simp only [propagate, Option.some.injEq] at pass
    simpa only [← pass] using hs
  | succ k ih =>
    simp only [propagate] at pass
    split at pass
    · rename_i eq
      obtain ⟨j, hj, hc⟩ := has_live hs (hr (digits % 16384))
      rw [eq, Nat.testBit_two_pow] at hj
      have ij := of_decide_eq_true hj
      exact ih _ _ (agrees_marked hs (ij ▸ hc)) pass
    · contradiction

inductive Tree where
  | stop (count digits conflict : Nat)
  | fork (count digits site : Nat) (red blue : Tree)

def check (rule : Nat → Rule) : Tree → Board → Bool
  | .stop k digits j, s =>
    match propagate rule k digits s with
    | none => false
    | some t => live (rule j) t == 0
  | .fork k digits i l r, s =>
    match propagate rule k digits s with
    | none => false
    | some t => check rule l (marked t true i) && check rule r (marked t false i)

theorem check_sound {c : Nat → Bool} {rule : Nat → Rule} (hr : ∀ i, hits c (rule i))
    (tree : Tree) (s : Board) (hs : agrees c s) (pass : check rule tree s = true) : False := by
  induction tree generalizing s with
  | stop k digits j =>
    cases e : propagate rule k digits s with
    | none => simp [check, e] at pass
    | some t =>
      have hz : live (rule j) t = 0 := by simpa [check, e] using pass
      obtain ⟨i, hi, _⟩ := has_live (propagate_sound hr k digits s t hs e) (hr j)
      simp [hz] at hi
  | fork k digits i l r il ir =>
    cases e : propagate rule k digits s with
    | none => simp [check, e] at pass
    | some t =>
      obtain ⟨hl, hb⟩ := Bool.and_eq_true_iff.mp (by simpa only [check, e] using pass)
      have ht := propagate_sound hr k digits s t hs e
      cases hc : c i with
      | false => exact ir _ (agrees_marked ht hc) hb
      | true => exact il _ (agrees_marked ht hc) hl

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

-- Each instruction names a progression by its color, common difference and start.
-- Invalid codes name the first three positions, so every code has a sound rule.
def apRule (n k code : Nat) : Rule :=
  let b := decide (13000 ≤ code)
  let a := (code % 13000) % n
  let d := (code % 13000) / n + 1
  if a + (terms k b - 1) * d < n then fromAP n k b a d else fromAP n k false 0 1

theorem fromAP_hits {n k c} (hp : Pal n c) (ha : Avoid n k c) (b a d)
    (hd : 0 < d) (he : a + (terms k b - 1) * d < n) : hits c (fromAP n k b a d) := by
  obtain ⟨t, ht, hc⟩ := ha b a d hd he
  have hx : a+t*d < n :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right d (show t ≤ terms k b - 1 by omega)) a) he
  refine ⟨min (a+t*d) (n-1-(a+t*d)), pointMask_bit _ _ _ _ _ ht, ?_⟩
  rcases le_total (a+t*d) (n-1-(a+t*d)) with h | h
  · simpa only [min_eq_left h, fromAP] using hc
  · simpa only [min_eq_right h, hp _ hx, fromAP] using hc

theorem apRule_hits {n k c} (hn : 3 ≤ n) (hp : Pal n c) (ha : Avoid n k c)
    (i : Nat) : hits c (apRule n k i) := by
  simp only [apRule]
  split
  · exact fromAP_hits hp ha _ _ _ (Nat.succ_pos _) (by assumption)
  · exact fromAP_hits hp ha _ _ _ (by decide) (by change 2 < n; omega)

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


set_option maxHeartbeats 150000000 in
set_option maxRecDepth 100000 in
private theorem yes141 : Good 141 13 := by
  apply ofMask 0x103400400868010012 (by decide)
  decide +kernel


set_option maxHeartbeats 150000000 in
set_option maxRecDepth 100000 in
private theorem yes154 : Good 154 13 := by
  apply ofMask 0x121002c680108008400 (by decide)
  decide +kernel

private def tree143_0 : Tree :=
(.fork 3 0x36972376b7 42
(.stop 4 0xdb05701e189a45 165)
(.stop 5 0x36c15c0786266db2ec 165))

private def tree143_1 : Tree :=
(.fork 8 0x34c30912c04b324489233198c77 55
(.fork 9 0x27317346de28c8a3f2f70be645a13a0 29
(.fork 5 0x5b337e93aa555da52 38
(.stop 2 0xdd45554 4185)
(.stop 18 0xdf55c8ddafe0fdd41d54764a75b52f4f59f00746c6243cc69cb9d2005e0b2e9 2439))
(.stop 3 0x37d8598763f 5161))
(.fork 0 0x0 31
(.fork 6 0x149890f31a50524a39936 52
(.fork 11 0x99c3141557694b63f00c88852f64be936414b9 38
(.stop 2 0xdd45554 4185)
tree143_0)
(.stop 25 0x36bf5e3981dd435bfcdd45044cbb4e93433d9bfdf6181cd0451fb59cf63610944a21dc4be143590df6fdf2fc 1157))
(.fork 0 0x0 47
(.stop 39 0x38633c696f0e17d152cb7d28ae188d77db05c8dd20cbe73ed9039415d15dd8e88853f210e645d54c959c363f076099c2d0cd05410505948019b6dd44b463a68eaf4111056 5313)
(.fork 11 0xd825551a556ff37512d0ce9d5bf98ab6fff6c8 36
(.stop 4 0xd8b08853f21670 1726)
(.stop 31 0x98ed2088f7d435fdecb2977e649774d0da850d4e75c8d7f86188e18cd833640df7551d9b7d05c91b2f40d04364d0ce49e14c2691363f 13572)))))

private def tree143_2 : Tree :=
(.fork 0 0x0 46
(.stop 13 0x19c5cfb5043d0685344579308dd241490530a29439128b 13887)
(.fork 6 0x23fc910286ccf9693f63b 52
(.fork 7 0x36c8053c5313cb4f375519660 48
(.stop 4 0xcb2d6f1625d898 5869)
(.stop 8 0xd8fd422df55554df5c0ab0dab59f 3152))
(.stop 7 0x33583134d69d8d53a052f341a 4456)))

private def tree143_3 : Tree :=
(.fork 19 0x1355bfb6c80e28a1828acbc24eab5211d94773243c9203edcfc8458577b5df9925 61
(.stop 17 0x1788cba18a8db154afcb2127b6269a41cff15478ccb3ed47f14c27219fda 14019)
(.stop 2 0x49ef635 13863))

private def tree143_4 : Tree :=
(.fork 0 0x0 32
(.fork 1 0x910 43
(.stop 5 0x3521694b7511030414 2305)
(.fork 0 0x0 57
(.stop 7 0x352b385b6c8415b7514a01286 2319)
(.stop 8 0xd4ac90fdb210565bfb751694b63f 3324)))
(.stop 37 0x2333e181d19db20fb67f7e06cd8982ed35dd3915e1b4895bff2e11b14c5e48052784a3b63f694a06d83eb75133f116445b18a2cbf076928d0be13c7cf3b531f5b3 13004))

private def tree143_5 : Tree :=
(.fork 8 0x1b80b432d60e09388cf253cfd9b6 61
(.fork 10 0x12b05c8174488e242cac64121052508d434 55
(.stop 23 0x34872cc750b81a386066eb743550f35e693b36883ea4e1e18d2934ebf63f2f98e14386939c4e81782 7295)
(.stop 15 0x13afd8bd66cdd34fb7df49278d1f87642670d7e411127c60236c8 13887))
(.fork 12 0x5385291704887268c9b331a528350a942d603f626 55
(.stop 20 0xd46cc4f76838635e4763f598785f5bd32d564ef7d5691f74c47d51f64e713a05ddd782 3036)
(.stop 20 0x690f63f5e4786364a362c695f74d691e337df5581fd46c75621d116470075a059976c8 13288)))

private def tree143_6 : Tree :=
(.fork 0 0x0 54
(.stop 25 0x351b45cb62c45b386362676c81feb48964ef7511fd4bd72face9d52ed662d6cc887225c9a326ccc694a0d42d 3761)
(.fork 0 0x0 59
(.fork 15 0x1e010505c63a6166a723ddabd8b45d11b886ed26a09ae33f116c 40
(.stop 6 0xd6cd1fadd460fae18d177 4173)
(.stop 18 0xd015c7dd411e34dd319bed8fda5278e60fadd45554cbb8e9ddb21559606b63b 6028))
(.fork 0 0x0 48
(.fork 6 0x243cbd52facd073f2177b 29
(.stop 11 0x386345df63c386954adb2105650f56fedd45a52 6033)
(.stop 14 0xd8fd04ee18d177d8f0e1a552b6c8415943d5bfb7512407521 3046))
(.stop 18 0xdd443fbd899c81d6cd177d8ed0e4d49851e3a754c2db201d81030be64a3b52b 2305))))

private def tree143_7 : Tree :=
(.fork 6 0x10909a826b8c6e33f116c 31
(.stop 13 0x351052e73eb2d0d200530553fdd451f147e96efd8fce16 2586)
(.stop 6 0xdd451f147eb63f4a1b6c8 2883))

private def tree143_8 : Tree :=
(.fork 0 0x0 54
(.fork 6 0x550c693cbcf3550a942d 50
(.stop 19 0x1fdecb4498e3a3181ad4459bfcfa189662676c83a7516345b54b752ed66159896ef 13006)
(.fork 6 0x1270991339567071ff63f 44
(.stop 10 0xd1dd80dcd65049414539d64a762c603d9b6 3583)
(.stop 3 0x36c85bfb751 4182)))
(.fork 0 0x0 49
(.stop 11 0x34933854e19d6cc1c9d8fc41a21f516dd480882 1323)
(.fork 11 0x415263915245cb52021f4b432d614b166db52b 31
(.fork 5 0x5261b186d34149bf7 36
(.stop 4 0xd8d90e4d0450e6 2601)
(.stop 5 0x37494393411244763f 2601))
(.stop 18 0x604b63f1487862598785f4a4363a4e974020dec6d61d58764411130a60336c8 13722))))

private def tree143_9 : Tree :=
(.fork 0 0x0 62
(.fork 7 0x15916f880120109ab3ee8fc5 54
(.fork 19 0x14e2f08d6c437d3aad8fc151105c41f17045cc1ba8c6931d0e13386d28350a942d 52
(.stop 16 0xcb395495bc38637d3751b5551da3df540c33140d834e7539f5519547 5444)
(.fork 2 0x6daf6b5 49
(.stop 8 0xdb0e06ce1881386b7349150a1549 3867)
(.stop 8 0xdf54f1b64cf6c555532ee457b744 3327)))
(.fork 0 0x0 49
(.fork 11 0x41a1b606e52248b5d3ca90d443856ee5bc180a 60
(.stop 2 0xd8fd0df 2331)
tree143_2)
(.fork 0 0x0 48
tree143_3
(.stop 30 0xd4114abe18dae1d2086c7671763536091eadd340ad286d8a8d8ed0e464cf526246cbd04a194c255456fe7d376c82f98d044a3b52b 444))))
(.fork 0 0x0 66
(.fork 8 0x10453f17305cd1fd88053608d91 44
(.fork 7 0x88d2d0cbd1457517348019b6 47
(.stop 24 0xdd4177fcb216625bbd899648da43e1889ae28a802d02eca29388d0434345895626b6263ed9044602180c 4728)
(.stop 29 0x32cf5987862553b2d383eb863220b5161da4b3633d54b9551d80ddd4002c28a4e23410d0d1626b62d1b1890f4a398a964db6c8 1723))
(.fork 0 0x0 50
(.stop 32 0x57572c869132e8075d895648d92766d363564db6c802f8882244177cd4851f14a01a5281b60fadd447f5220c893387ce9d3ab166159896ef 13052)
tree143_4))
(.fork 0 0x0 70
(.fork 5 0x27809f4a2e2d28b5d 44
tree143_5
tree143_6)
(.fork 8 0x9cc4a2246c9202f850d6437f391 59
tree143_7
tree143_8))))

private def tree143_10 : Tree :=
(.fork 18 0x243cc69361cf18007c0ac1b54d893c691526069a4e6da33784a399366da9c84 66
(.stop 17 0x32c986236b14a353ab6fe1d12e181434690f75147c51fa5bbf2f60e391e0 4445)
(.stop 19 0x38616ff32da6b838633164d776dbb358670f39112405aa2424a254c7155059ab40d 6308))

private def tree143_11 : Tree :=
(.fork 6 0xf06ea20109ab28e0a39 48
(.stop 2 0xd8fcfc8 2603)
(.fork 0 0x0 39
(.stop 27 0x336064cb2df578b74a04fce01555b63f319cf2d3cdcfbb3f132f33f2943a555352a28d4bcc3810f204eb14c659b56fa 4013)
(.stop 19 0x38637d373f745972f34391672d45d670629363f5321789605b37a31b4c70385f52b 3459)))

private def tree143_12 : Tree :=
(.fork 0 0x0 58
(.fork 5 0x92228d4c6d31c0e17 44
(.stop 6 0x532363f4a3b6c82d0d0e6 13178)
(.stop 5 0x337a605b75141375b3 5737))
(.fork 6 0x201891b2480b532f87391 44
(.stop 21 0x335864cb37a5321a52d8fc9113c69700d494c6940d19366fdf6c82d0cc5f433d0e647ad423 4436)
(.stop 8 0x605b75157936363aa0f2f4a0f52b 13178)))

private def tree143_13 : Tree :=
(.fork 5 0xcc079888e2248ac6 47
(.fork 12 0xe244a71d90772200491f26709ae411105649f128a 43
(.fork 14 0x7504a3246c2613f250e7d1f89982f40be649e128e52c14c2 70
(.stop 13 0x178ccb7d1fccbe02f10de076f4801434dd45554e18ce96 13021)
(.stop 18 0xcb7d318d27d0d5cd891ebd485399746385f23ccfa7431759647bd1fc66cf410 2443))
(.fork 12 0x2cfcc5d16bc5ba3f21670629363f43556fa64db6c4 68
(.stop 10 0xdd1178ccb7c4052d0d200dd44b4645554c9 4467)
(.stop 14 0xdac459ecb7d17352af4102f8529355535201014b43480352b 4183)))
(.fork 0 0x0 55
(.fork 9 0x15509cc53e17346eb2f70be63850e1a 64
(.fork 5 0x4a61ba07752470c6a 42
(.stop 11 0x36c4531b37460599c3dd45554d6cca382f94c5d 3042)
(.stop 25 0x33f66b7747e83eb863531955359b56facbacd8dd6cd04d555166cdaf5c89db0cfc8411505547f1543552b2f1 2293))
(.fork 0 0x0 70
(.stop 14 0xdaf1b6acdd1ad56d938633a875253f218a4d8fc5c81744916 6454)
(.stop 6 0xd040fc8d8fc80428e3391 3611)))
(.fork 0 0x0 59
(.fork 8 0xec15910904b31744be02f88cfc 31
tree143_10
(.stop 37 0x386069477d57f776c52427861694b75155518a2d6cc4192204fc8411505547f1316cbcc6d509c86e81dd491c28d90c4629f3913624dfe5e35a4ecde14c27f6b6c8 8016))
(.fork 5 0x41056c27d0e5f4a4 62
tree143_11
tree143_12))))

private def tree143_14 : Tree :=
(.fork 0 0x0 62
(.fork 5 0x309200480426ad551 39
(.stop 5 0x32f933ff86331694c6 1755)
(.stop 10 0xd471bfee18cfad74577d84a399366b776c8 6451))
(.stop 22 0xdd3d5e26b8f861145ce076b81bfee18d5546b8b75131d8d833641ad3cbf04b03a50eaf480f391 3049))

private def tree143_15 : Tree :=
(.fork 11 0x2902d80b81704ab42f40be649e128e4e513a8 56
(.stop 28 0xcb91d9dcb29ebfe185670607774a7f86188e18c9a535e8e9443390e747a1203d8d4c6b41346c335dd0d15e1735e5e0d89f 6451)
(.fork 0 0x0 58
(.stop 21 0x32d56ff32d9629b85f5bef51059b992fe18d27fcbd47f3454b74f1fb890828f0b51385d785 3445)
(.stop 15 0x375133b5a55e17dd18d895fe1ce4480435e38633ab0fc66b472f9 4611)))

private def tree143_16 : Tree :=
(.fork 0 0x0 50
(.fork 15 0x4981b646e61d4075e28a54c66db9c88db107f52010e9d3ee4fc6 58
(.stop 7 0x1bfcdd455dbd8b41df09d9287 13586)
(.stop 12 0xcd61307dd45436dd3d673ce3cc7250e153b554b40e 4869))
(.fork 8 0x96c2603a3cfab3f216705e2b63f 54
(.fork 7 0x4a517306d02644c743638e1b 55
(.stop 11 0x33587221f49cb64fbe5e1739128c916847d51f6 1872)
(.stop 13 0x3751008f74f59cdb6ee18dfe1ce3d92dd039a4b745b62c 6159))
(.fork 0 0x0 58
(.fork 7 0x27628d4b512d58bc92f7ce17 44
(.stop 2 0xd8d15db 465)
(.stop 9 0x1c88d44166e64bf5b331cb634629b512 13869))
(.fork 0 0x0 56
(.stop 17 0x33e847a363c34032f32474cf933fd53c55477512d3cb5831acc72413589f 3732)
(.stop 25 0x362d380b8627d3b2de6ff351264cf5b3074425ad8ed9c26b838630504aacdb1075e28c8bdc34011686fcb2f9 6167)))))

private def tree143_17 : Tree :=
(.fork 10 0x9cc38314d05cd1d78bdc2f98c7345a192c 54
(.fork 7 0x361b40c6931d11f547d9283 68
(.fork 11 0xd30c2476b28c8a3f2afc5a92649ae3db11203 32
(.stop 4 0xe17d782dd45701 6007)
(.stop 9 0x23c0df651f3d8fd4bb7f8786355532e1 14287))
(.fork 0 0x0 58
(.stop 10 0xcb659c4cb7504cd670a35385cfbe412d785 1449)
(.stop 26 0xdf5539ddb15200cb79b6b746385f86177d855278622b08c6c31c504c604b63f386f3912458eac5551ad66d8f51b 5875)))
(.fork 0 0x0 70
(.stop 14 0x607f63c23fd0d1576359c3cab525034c3941fe880924590e9 13600)
(.fork 5 0x41a2b0904c604b413 68
(.stop 14 0x49ff5b1171091828c85a959a38632884c5d47cd4bedb11203 13042)
(.fork 0 0x0 58
(.stop 26 0x59c3749315762d81b38621fd775159a2188e18ca212654be33641438d8f14bedf60a3528f0e173a90ea53ef9785 13022)
(.stop 4 0x31c77d82887525 13201)))))

private def tree143_18 : Tree :=
(.fork 0 0x0 54
(.stop 16 0x55277436b4f62c36550cc43a5c01ce455e359c363f3a7751b1b4075d 13730)
(.stop 8 0x33d751b3a7763f578f41931e752a 13052))

private def tree143_19 : Tree :=
(.fork 10 0x1f755546ff3751051c4a72004eaf415b4a4 43
(.fork 9 0x2902e81d4170491b2f40fcd49e128e 64
(.stop 8 0xcbed785d68841ae18d0d2438d437 3601)
(.fork 0 0x0 66
(.fork 9 0xa2a28f4ab73178fc947a92014c115e3 24
(.stop 8 0xe17d924d484e17d6cce0f5bfdd18 1167)
(.stop 5 0x1b6ed0045a93edf74a 14150))
(.stop 11 0x1926d45c37c3edf62c4a1f5b3385d16b509b391 13861)))
(.fork 0 0x0 27
(.fork 11 0x190068375148875028a4aa4360d4375319b6e 58
(.fork 11 0x394077c413106cc4e49fd2875bbf5b3385d426 48
(.stop 12 0x1d5b5b4649b6256fdf626120498852d32cd4e6580b 13734)
(.stop 9 0x351764db62c45cb74681b362614bf6b9 2178))
(.fork 0 0x0 49
(.stop 20 0xcb39f51cfc1544d8984983138e1f5bbf63f28f4e9c3ed93044c755e36dbf39131e51fb 5303)
(.stop 23 0x33fc78d32cd7d477d23a756ef66d763f578db6fd05d93b746374645cb5b231a4c743cbd0dc597b521 3615)))
(.fork 8 0xd985a91d58fb752f966b64db6c4 58
(.stop 4 0xd6894315535785 2613)
(.fork 0 0x0 64
(.stop 11 0x362c1fa8eadd689549cbece110758f2ae18d0d2 5444)
tree143_18))))

private def tree143_20 : Tree :=
(.fork 10 0x1fbc88d2d0cbd1457517347ad20054fd54e 31
(.fork 6 0x1b1890f385928e62a5936 50
(.stop 13 0x340b55578632400d89556762738173eb3ab11f147e96ef 2601)
(.stop 18 0xe18dae1cb59814d8b55e2dd294385e19813d8b8d89692f2f6415d5e359c363f 2877))
(.stop 18 0xd89d554e18cf25d4413a857716e8cdd96fc88536c852b385f530181a7b0b7da 5435))

private def tree143_21 : Tree :=
(.fork 0 0x0 46
(.stop 22 0xd89cab03a4b376578b7496b977da769b5166709ae0e18cd883858e1855315dad8fd0574391425 6022)
(.stop 2 0x576b2f6 13044))

private def tree143_22 : Tree :=
(.fork 0 0x0 50
(.stop 2 0xdd451fa 4593)
(.fork 0 0x0 26
(.fork 8 0x2adc138385ce8bd6cd554578db6f 43
(.stop 11 0x127adb2192ecbd9289e18c86c769b7da2f4128e 13044)
(.stop 12 0xdb21da6df694c0cdd94c655578633620e16386363f 7304))
(.fork 7 0xe17d6ccb3d6949ae183eb751 43
(.stop 12 0xd89d786e18d787db20ac8769b7da2f412014a395dc 3730)
(.fork 0 0x0 48
(.stop 17 0x3635410f86331bf37002936c82650a23df68e163861427576b63f3f210e2 4023)
tree143_21))))

private def tree143_23 : Tree :=
(.fork 5 0x15a0e646e61dd0890 57
(.fork 7 0x4a8173ca342b08aca2f78f32 44
(.stop 9 0x33764ea14c6e18dfdcdf686d347ad668 6170)
(.fork 0 0x0 32
(.fork 7 0xd6f385d28f606d8a86709d10 46
(.stop 18 0xdb11936df6966d64bb8627aff7d34a2da4fdd460fae18ca292add0d1439154c 4750)
(.stop 31 0x37da769b2d58a97861768f35778b33f86299bf4d4486ce745b62e6fe9f48dd3dc827f720fa8627863360cd903a7ceaa47cd1f852e72f4 7582))
(.stop 8 0xd4491f852e72f42478c6c31c75b3 4595)))
(.fork 0 0x0 52
(.fork 10 0x17286db1da4777340cd833640e9f3aa94b9 32
(.stop 23 0x32d174633fe00780ae1ae490f2cdb7da3808f1ecdf10e5db119c56db363f66ddfdc83ea189e18d9c2 6312)
(.fork 4 0x764bd147af5b3 46
(.stop 12 0xcff80b0cdf10e5db1128e64db7da7f73863410d1fe 1454)
(.stop 2 0x67136bf 13876)))
(.stop 11 0x37da4a3b6c426690e549e954dcbd49af28f32f9 3024)))

private def tree143_24 : Tree :=
(.fork 8 0x200499c28a8a3d3f25044415b4a4 58
(.stop 11 0x1554dd451ebdf6928ed8fc41b108c5ba385d431 13747)
(.fork 0 0x0 60
(.stop 5 0x3751578f63f224c91b 2189)
(.fork 6 0x1b6c769340cd8336432fc 43
(.stop 8 0xdd45b6fe18d663df68bd04a399b7 4587)
(.stop 16 0xcb9d6ffdd19d1bdf691eb4801929dd44b462fa75201d58fb764db6c4 5744))))

private def tree143_25 : Tree :=
(.fork 0 0x0 42
(.stop 2 0xd8f0c74 2759)
(.stop 9 0x363c361763f3eff6c45e272eb3f232ef 2336))

private def tree143_26 : Tree :=
(.fork 4 0x56480433e4cff 67
(.fork 8 0x33853e15005c317386e51ba8a3e 43
(.stop 3 0x37da457128e 3024)
(.stop 7 0x13acdf699386fe763f2f7f52a 13182))
(.fork 0 0x0 63
(.fork 6 0xfc774247491e31acc72 43
(.stop 20 0xcb7dae0e18e0fad20992ed8f05c11b4891b2898e026fe5da6df68bd04a393a850d5783 6451)
(.fork 0 0x0 39
(.stop 14 0xe18d78783eb3f75e2b63f64b9bf9df69936db114c6578166d 3162)
tree143_25))
(.fork 11 0x3600dc2730e285342f70be636190da45a34a4 64
(.stop 15 0x1791cfde0f7e1819bad8f14c66fef6c450bd4bccbc86e8223cbe5 13325)
(.stop 15 0x37da59b763c4a2f516605f63f5e476c450bd4b6d4a877b2227413 4321))))

private def tree143_27 : Tree :=
(.fork 5 0xeac47c54295bbf63f 48
(.stop 12 0x507f2eb4c7386064db3741460a29531b8635529925 14290)
(.stop 10 0x1d1b3743c7b7d83177407531b86349ff52a 14290))

private def tree143_28 : Tree :=
(.fork 0 0x0 39
(.fork 17 0x102ab55d95e1a188e18c52e169c6db28d4ab038114ac531978760519bb 64
(.stop 22 0xdb0d819d411172d8b91697461da5e181306d699ad764bb7da7d3f86135d953a554da51861e215 4869)
(.stop 24 0xd4114b2cb2d0c5766f2e23f09283d8b9811dd054b5d45981a6b977da64bb63f3a590ca47992057b1f414 4029))
(.stop 41 0x32cc5baf2f159ab361604f5043a191674a0f4133f2167066f9a4b6d9763f3efdb6ee18cb3c3628f313ccf39131bd5e259bd9306b5f3762f40f2a435d4c06069ae57b0b7da769b6c8 5299))

private def tree143_29 : Tree :=
(.fork 3 0x1a5283eb751 67
(.fork 7 0xce09f442414f8540170c5ce 43
(.stop 2 0xce45669 2331)
(.fork 0 0x0 39
(.stop 2 0xce45787 2613)
(.stop 3 0x36c8383b37e 2462)))
(.fork 0 0x0 63
(.fork 6 0xfc3991dd0c72434d934 60
(.stop 25 0x3479286b74450cb6284e856ef649f63f14ac76328a51ed4e955cf576740e031c1570784273246ce153865787 4461)
(.stop 20 0xdb10f34df691f5dd3d54d599d781cbb4d8e45a763c28d4a3c2d44b56385cf3159a7391 2458))
(.fork 0 0x0 55
(.fork 12 0xd803709cc534287cbdc2f990da436d1684c3d4bc 64
(.stop 19 0x386066eb63c5319bfbcb80f313ccf6bb52d54bd64972f212987752f74be531a99c3 4023)
tree143_27)
(.fork 4 0x2cf4ea647c74a4 31
(.stop 33 0x3516769b62d6713860360f8633ce92054c015e2dd3d05b4565438d8b955978e74131d88c6914acaad315cc6e3f2167066fb63f385928e64d99c3 6589)
tree143_28))))

private def tree143_30 : Tree :=
(.fork 11 0x1590c24417200480421fc88f24789ab49ed28b 67
(.fork 4 0x14f85401b94fca 48
(.stop 8 0xdb21da6df6928ed8fca2b3a6cfc8 3872)
(.stop 6 0xd485938df6915c4a3b52a 5741))
(.stop 27 0x375059c33617441fdb862386252f352b31c504c55319bcd0589162f855545bedad6d48038a14d0bdc2f98d8d599b4a4 4600))

private def tree143_31 : Tree :=
(.fork 0 0x0 67
(.stop 17 0x352045b763f267337e5533749439b52b26793ac6fdf63d1ffc8062d14b5a 2321)
(.stop 13 0x3596649b5ae1b6d77fd8f402d1d594be64db6c4415b4a4 3882))

private def tree143_32 : Tree :=
(.fork 7 0x27210906d526b8a3628eccfc 39
(.fork 3 0xab054e9553 44
(.stop 4 0xd41128d54fd54e 4729)
(.stop 5 0x362783eb75155535b3 3587))
(.fork 0 0x0 57
(.stop 7 0x33762f413a2df69da6db20e16 5743)
(.stop 12 0xd89e0fadd45554d6ccb43db2128e57735ae3cab5a2 3587)))

private def tree143_33 : Tree :=
(.fork 0 0x0 57
(.stop 5 0x14bedb1054016e4b57 13476)
(.stop 28 0xcb3206bdb10bd05e2dec27d3f7da47af6bd5bf5e347b077d164976285979665d290b5a31a4c7433dcd014a0d6eb5bcf2fb 4306))

private def tree143_34 : Tree :=
(.fork 0 0x0 68
(.fork 8 0x34c4b317107712f4cbe93c9cf3d 55
(.fork 8 0x12744a614f86de28c8a3f2f9965d 48
(.stop 8 0xdd45a52d8fceac4165554e18d54a 5463)
(.fork 0 0x0 54
(.stop 15 0x35105c07751555f63f52ef8633a451eb7d4f7da31a51f547d96f3 2886)
(.stop 2 0x47fb5a5 13334)))
(.fork 0 0x0 63
(.fork 2 0x1dd11fe 50
(.stop 10 0xdf687e2e18e0fadd447f533ccd053ab0fb9 8019)
(.stop 15 0x37d97235fe1e18dfdcdf69781d8f4acd31a4c7436392835bcf2fa 6594))
(.stop 7 0x36285979665d290b5a4a0f2fb 2765)))
(.fork 0 0x0 60
(.fork 9 0x27309e0763246c92026b4be14e5d3a5 59
(.fork 8 0x10906d526b8c6e31bccfc5095432 50
(.stop 7 0x351621f4a3a2d0f75147c51fa 4451)
(.stop 23 0x35a2457b2cd1f8b7da435d4b9603751023f1a52744f63f553166ad45887d28e8b4347ad4b154ff5b3 3588))
(.fork 0 0x0 63
(.stop 26 0xcfe1784cdf1663d8f527adf69936db10fb5411178764d37516ff37d7076c6d91fd4fb9458d16d5bbf5b328e91fe 6449)
tree143_31))
(.fork 0 0x0 70
(.fork 6 0x9f43991b88d07382ce23 55
(.stop 25 0x335a3811a48d670c53d6cc7f572036c464db7da3ca94b652f38636b8351b129853420249162f70be645a165d 883)
(.stop 18 0xd8a165e59977d34349dab86238632cc4c64555181f64edbfcdd45044415b4a4 5021))
(.fork 8 0xfc4a61ba0775266d15f45c7391 59
tree143_32
tree143_33))))

private def tree143_35 : Tree :=
(.fork 0 0x0 41
(.fork 4 0x26a0cea4e493aa 67
(.fork 11 0x41033827d14f85401b749193818e2049d9290 60
(.stop 28 0xd6cdb69d8b1670095b48364c77501b5880124390d24c5f2f7173877526a49ad3171437d4943961ffc806246c9202890be1 4729)
(.fork 0 0x0 64
(.stop 29 0x33e87f7618ae188f1edf6128e64d9adddb20c5a43491616b8206ee18ccff54f1551dd44b4f2d6104d627f2f91ba07755081437 3321)
tree143_14))
(.fork 0 0x0 63
(.fork 10 0xfc39916fc7742240a372f38be452b94c4 43
tree143_15
tree143_16)
(.fork 0 0x0 55
tree143_17
tree143_19)))
(.fork 0 0x0 66
(.fork 5 0x40010453f17305cd 59
(.fork 7 0x1590e384b3246892126b8cfc 44
tree143_20
tree143_22)
(.fork 0 0x0 63
tree143_23
tree143_24))
(.fork 0 0x0 56
(.fork 5 0x4a712c0b4f2d6104d 62
tree143_26
tree143_29)
(.fork 5 0xa2928f10d1439352d 62
tree143_30
tree143_34))))

private def tree143_36 : Tree :=
(.fork 0 0x0 46
(.fork 8 0x1710ab73129043415d42550c954c 62
(.stop 14 0xdd00c5ecdacd884e95433d89d789d8f887f31b127b4a2df4d 5461)
(.stop 6 0xe18ce8bd6cd1f16b87751 3464))
(.fork 0 0x0 50
(.stop 29 0x2217cb39e337d3f40b553de35d8dc36a2a9ce896dadd1278b363e31bd16345b6067d8f065731c50537d3775147c51fa4c356ef 13001)
(.stop 24 0xd88a066df5da4fd8f0fb4e18cc6f59bf6372431319605f751578dad8cde4c5564bb7da53015ce576b2f4 5298)))

private def tree143_37 : Tree :=
(.fork 3 0xd8245b1280 44
(.stop 3 0x386354fd668 2189)
(.stop 3 0x336252e3751 4458))

private def tree143_38 : Tree :=
(.fork 7 0x14a0be876428a8fb649f13a4 30
(.stop 8 0xdd295dcd8fd8a4e18cc59dd19d12 7160)
(.fork 0 0x0 36
(.stop 13 0x385f62a60f6d8a4e17df64b3f7d4774a3c7d8a2e18d8a4 5312)
(.stop 20 0xdd05034cda1669d8a58a2e18d786df45bf6e181f4acb694c0d0051ef6ff774f577363f 5158)))

private def tree143_39 : Tree :=
(.fork 0 0x0 30
(.fork 8 0x2674c683e94fc243813ab64ddbf8 47
(.stop 13 0xd86dd05b687d4785f247c4841b254c062a763728a93a4 13183)
(.stop 12 0xd2055e1cded6fd769f51a31a9a51cdfcd863cc32f6 5319))
(.fork 13 0x90c28ed0d0cde104a45a14c25e3763928a91fc531f63e 32
(.stop 10 0xdade0fbe18dae1dd451facbd8bdb3a2d81b 6022)
(.stop 4 0x6b8775147eb524 13599)))

private def tree143_40 : Tree :=
(.fork 10 0xd41e017089252d38b593cc0f344a09284 37
(.fork 8 0x12745bb2f28c6f3634fac64c1b64 50
(.stop 19 0x32cf913f6b1554f35e692359c3624e174a1d92fd8c14c7e18cd7864b37da5515548 5166)
(.stop 18 0xd671bf5cb35ec3df44e17436192f66f7630531d8a26fc386335e130464b32f0 6728))
(.stop 24 0xdd25a53cb715e1cfd14bf599b2f0552b7476fd7372363dd17d8fd545df68b552f7f515385cfbe4363639 7016))

private def tree143_41 : Tree :=
(.fork 5 0x2e416ecbca5555930 28
(.stop 16 0x83df6c13a2f86324035ae1fdb74937e5a43e18048b12505b2531da53 13297)
(.stop 7 0x1d0cd234e8b54ff35c4593629 13858))

private def tree143_42 : Tree :=
(.fork 0 0x0 31
(.fork 7 0x7622f10f183f0d31d62a5c84 70
(.fork 8 0x2f5ce0fd8fc30b1b889142905559 39
(.stop 3 0x374f4815814 2736)
(.stop 2 0x55575b4 13742))
(.fork 0 0x0 50
(.fork 8 0x106c775220ce0f47e954555216ef 37
tree143_41
(.stop 10 0xdf594bae18505704dd28b694f622648f40b 4460))
(.stop 17 0x3622722f86083df5130b90bca3eb1789d02d057d8fc0cd079d0c26b7752c 1021)))
(.fork 6 0xe0475c2ac0d8f507b6c8 37
(.stop 9 0x37da1fdb63f383f86002d08763eb1930 1727)
(.stop 2 0x52e35a6 13728)))

private def tree143_43 : Tree :=
(.fork 0 0x0 32
(.stop 17 0x36c8481740545df8635e4763f578db6fdd456f8df69781cbd8e173a2d4cb 2454)
(.stop 8 0xd6999c9db21439671763f4a4f5b3 1030))

private def tree143_44 : Tree :=
(.fork 0 0x0 51
(.fork 10 0x52c2f210507f631dcd82364516445b1928 50
(.fork 7 0x41b220c893387d1f159896ef 46
(.stop 14 0xcd755e7d2256fbdd44e233a63622531f863410d4326269923 4731)
(.stop 8 0xe181778d8d578ddb20fc964c3405 4034))
(.stop 17 0x901dd451fddb219c9d02d043e18c6cd47e75a010185b31fbc86e437f63f 13317))
(.fork 0 0x0 70
(.fork 9 0xd307ac30717186e235f0d953a60eb1 50
(.stop 23 0x336140f53abd0088fbdf68996db20ab0d69955562b78630bc476f2f44f25457517354ff75147c51fa 1735)
(.fork 0 0x0 44
(.stop 24 0xcb49d19db210e95be1785df699bddd28f1fe18d791d8fd5e3607f62e269cd8955372f62f9cf25457553f 3025)
tree143_43))
(.fork 0 0x0 58
(.fork 9 0x3a079c41b108c9a726bcd89385d54d 44
(.stop 9 0x165ad8fda4bdf647611fbcbd1457554e 14289)
(.stop 19 0x36272a8b5a61b14fc2df6543252ff74a66f77da5be3751578da4bd2354c764bf5b3 5016))
(.stop 29 0x1555e18d424cfa0373cb58bd154fd54edd455e3d8fc0b616c8ab0507943960536c82658d785be37da23ec90c28a94c7694f629 13604))))

private def tree143_45 : Tree :=
(.fork 5 0x38e0e5453f2468921 57
(.fork 10 0xe40c603204a81bb4a3428f4e163860f32 63
(.fork 7 0x15a0bf85cf1ba4ac42b20be4 45
(.stop 13 0x363c247b75159a17866709b6fe18dc88df694c057395da 6017)
(.stop 3 0x37da5bf3376 3586))
(.fork 0 0x0 23
(.fork 6 0x241c99641290d94a19d19 44
(.stop 15 0x337664bb7da7d3f40b550759a02981c021f1555e18c88d54fd668 5298)
tree143_36)
(.fork 7 0x9942ac0c713a4981464bb6c8 51
tree143_37
(.stop 21 0x374f694f2d3381488d2f4554ed8e53abd02d541d66887c50dd555cd8887a35e16f8604b7da 2295))))
(.fork 0 0x0 61
(.fork 8 0xec0ca17448002014ac62f80be2 44
(.fork 14 0x17087ef1ff890b24709ab2f44be74575173508d43454fd54e 47
tree143_38
(.stop 19 0x33fb62a76c874678604355a43d4b10d0dadc75321c578662920fbe18c2eb6fdb51f 6734))
(.fork 0 0x0 58
(.stop 12 0xcdcd04fcddcbdfd6cc41b108c9a726bcc703628e17 4034)
tree143_39))
(.fork 0 0x0 53
(.fork 9 0x2fa1b706e9201cc6831d504a414139e 55
tree143_40
tree143_42)
(.fork 8 0x1d88a3b2d10b5943414b253034a2 63
(.stop 38 0x3eb3506861b626767f2f626772dc5e3763c670b86305101d11ff8a272f44be74c6953fdd456f8df687f631b9057578d78a66fb63f1b98890247499a2b10ac849e928c 13288)
tree143_44))))

private def tree143_46 : Tree :=
(.fork 6 0x14b8b5d31e527e4a2180a 60
(.stop 10 0x21cb7d40bd8eb1553f63f14e4c6e31bd1fb 13730)
(.stop 13 0x36266fcb6c81b2f86138256f5dd4487237f9559743f63c 5302))

private def tree143_47 : Tree :=
(.fork 8 0xe1c5b81d88d953a60eb153034a2 55
(.stop 23 0x37da4c3b86354ff6b331535165c0f8602ac10ca43a763431b9271d8fc2692458f3043690db45a16f4 3014)
(.stop 5 0x363467276c84817405 5171))

private def tree143_48 : Tree :=
(.fork 9 0x144051c76f1fbce093c94f3f54fd54e 36
(.fork 9 0x1d1096c40d24509a3315cc6e49c53af 55
(.stop 17 0x335e1aeb2c952c94c05bab85f31a9bf6d8d128852db8633cc177764b1bf2 4734)
(.stop 12 0xd1f099a49e94b2d42527ecbd8a2e579f63453136c8 4166))
(.fork 9 0x27714cca3628ecab531cd28d50df63f 33
(.stop 13 0x35948a8f7d65bf1f4fdd314c1e18d05453136c855658a7 8021)
(.fork 0 0x0 51
(.stop 11 0x350b72136c828e8e11df554b153078632d74eab 2606)
(.stop 5 0x35ae31937d552c73fe 2618))))

private def tree143_49 : Tree :=
(.fork 0 0x0 26
(.fork 3 0xc64607d93b 64
(.fork 22 0x6dcf6bd2f858a2cde42720be85c02450a302905050d2882770c14a3b3170c73384542050dd4c5 33
(.stop 8 0xe184c51dd11930cffd4c4db21559 5294)
(.stop 6 0xcfedf4fe1854ae53135ae 3153))
(.fork 0 0x0 36
(.stop 6 0xce0cc6e2af4e17d6cd293 2467)
(.stop 15 0x34a2579b63b53136c812548872458be145df5b304e105059d763f 4748)))
(.fork 18 0xbe827209dc3051700a3628ecc5c3611437d8fc9142494a302905050691b751 60
(.stop 7 0x33ff50af7d438714c4db20fc3 4734)
(.stop 13 0x1f4edb21c84e185288e18d157744b7d550b14b96b4f6c3 13447)))

private def tree143_50 : Tree :=
(.fork 8 0x9dc4ab15085c91dc09a02f60bea 50
(.stop 29 0x32cf72137444a1da57e181930df50fbd52df63c4799929df55293628b8633c94fb33f3153f66d9a43dd451f147e966159896ef 3593)
(.stop 5 0x386354ff5b34a4f63f 3877))

private def tree143_51 : Tree :=
(.fork 9 0x2f20e1c76228ecd953a614c064a34a2 60
(.stop 24 0xd009bfadd0d786df55f4ee178d6847e736a64d375147e966266d763f31b8c6f12b891d28e928cdb21433 6733)
(.fork 0 0x0 54
(.stop 10 0xd68075adb2128cd8fd4bbe18c887268cfbd 2158)
(.stop 16 0xe18d66ee179beed8f1934dd451fa598b38347e491d289f6c8672762d 6022)))

private def tree143_52 : Tree :=
(.fork 11 0x5ca1b388852f64be937dce11435d0de45ad4b9 51
(.stop 6 0xd47578fdb218abd8fc414 1459)
(.fork 0 0x0 61
(.stop 16 0xe18d9b7e17837402d515b5543630125c76b5e1b51d5e3db6adb20fbb 2172)
(.stop 15 0x362b81bf7d645d9702d06476b5e1b51d5e3dc84db209965be352d 4734)))

private def tree143_53 : Tree :=
(.fork 10 0xdd076b288cf213cf52754a454c55e1b527 42
(.fork 8 0xa00b5222c909388517550d966a 61
(.stop 7 0x363f45bb2f6414b6c82894be2 3475)
(.stop 18 0xcfa436bdb21bffd20904049d17908cdb4927683863364d0e7691375045b352d 3733))
(.stop 14 0xdb218abd8fda4be1789952d459bdce045bb439d41c50ef529 4014))

private def tree143_54 : Tree :=
(.fork 0 0x0 45
(.fork 10 0xe1c7621dc0a3b3180c773ed0fcb52c94c0 61
(.stop 9 0x352445d763f530b6c81bac87e26b0be0 5171)
(.fork 0 0x0 41
(.fork 6 0x2e01d207587dd26596f8 42
(.stop 7 0x363f532762b3ef992cdb21436 1745)
(.stop 20 0xd65130bce05fd7e17876b3cf553bdf64c6e53259bed8fd28c5311d16db20f3059cf515 3022))
(.stop 16 0xd8dcfc1d8fd810d4905bb388748514847712f4cf3dd4b48fb49eb7da 5302)))
(.fork 0 0x0 55
(.stop 3 0x34a21de8a3f 1771)
(.fork 0 0x0 60
(.stop 18 0xd4b56f8df591fb49f9288cbd50df744f63f07a441d1dc490a31b8c6f3cbd289 4462)
(.fork 0 0x0 52
tree143_52
tree143_53))))

private def tree143_55 : Tree :=
(.fork 9 0x3b03200ca0e406e41bacbe24589816 47
(.fork 6 0x1d907e3247ce9a4a2954b 30
(.stop 15 0x385e412341055632e9381cfb45e19c8de18dda0d8fc6c55325bf8 4719)
(.fork 0 0x0 40
(.stop 12 0xcdb105264a363916e9175d8fd4b07681ebee18d786 4168)
(.fork 0 0x0 45
(.stop 13 0x37d9221517566f9a4bd8fd669d8ad92876838633ed1396 3168)
(.stop 7 0x1ebee18dc8ddafcbe952e7522 13597))))
(.stop 20 0xdf55175d041702e18dda0cfe966c5e1b51d2f64fc4cbd47621fc4d87414978f670f6c8 4725))

private def tree143_56 : Tree :=
(.fork 0 0x0 51
(.fork 7 0x1e0105091231dd16c4a0142d 69
(.stop 20 0xd22c90947e7518747386349d36c82d2cbe9d49d204532763f09f04ab14e05422f60bea 7309)
(.fork 6 0x2f852e21c8a2c4a234a2 40
(.stop 2 0xdb20c5b 1175)
(.stop 6 0xd8fd9c3cdb8c6f437f51d 3182)))
(.fork 0 0x0 56
(.fork 2 0x3a8d54b 31
(.fork 8 0xdac76235b8e163cd143b5e3d9c3 69
(.stop 5 0x351d48114c9d8fce08 3182)
(.stop 24 0x4a4747b692f4194a0f2da59cf74f2fa4eaa435d0de4a0528552e752931b9175532763f364d27e50bf4a2 13597))
(.fork 7 0x1be288d0d753019c7723b7da 57
(.stop 7 0x36c82b233742650aae38613a2 198)
(.stop 8 0xcdb96fc64d36c85e1f52752f34a2 5455)))
(.fork 8 0x17107712f4cbe93c9cf3d509752d 45
(.stop 2 0xdf694c0 1890)
(.fork 0 0x0 69
(.stop 13 0x37493f091fe5325558d460e9ad49cf345c0978fdf69c8e 3618)
(.stop 22 0xdd410ced2053a9d03448d1b259c7df699c369474133f094c9d48802f1f8c8903a6b52752f34a2 4744)))))

private def tree143_57 : Tree :=
(.fork 7 0x3c107865e28e0a392f80be2 47
(.stop 27 0x385e430b85f83df6b3437b63738318173a2cf1a8cdb863629363f47f528a4e60fa53f090e055617906dadbf8d8e53a4 8296)
(.fork 4 0x1b54f1a579b378 50
(.stop 8 0xdb2193ae18d786cbb51fcd8f90e0 5890)
(.stop 5 0x36c864eb863629363f 5890)))

private def tree143_58 : Tree :=
(.fork 17 0x41716ec8862f28c6f45593ae64c363e21fcc6131e0e993ac127b4a2f52d 21
(.stop 8 0xd44dd1ce18d702db20e0c59b5a56 6022)
(.fork 4 0x47b94b978e3630 31
(.stop 10 0x50d750c768f62748136bd64cdd1ce18d702 13587)
(.stop 9 0x38635e1b627768f50c416b6b8886b7da 2582)))

private def tree143_59 : Tree :=
(.fork 8 0xe803b12ac6e31bb0be131b8c6f 46
(.fork 18 0xe206d51fbc87d3650fb33f3154ed6cc7633184c783a64eb04e5d3a55095432 57
(.stop 15 0x1fd8e17cdff863350c604b7da265105a64bb6c838595415531668 13293)
(.stop 9 0x33f521bde38d8a5c84db2105a553f63f 5890))
(.fork 9 0x4a122289962890f22456966b5be352d 44
(.stop 32 0x2cdf2c97f673f26937493007801f6fdb51552e5e3881c36292424fbd7f637d65c09c84db2105a54f954f573363f1fbc87d3650fb352c553f 13046)
(.fork 7 0xe8b3c64f3559d1b696fdb5b3 42
(.stop 22 0xcbd8871d8add12cb25a4dd020a23435f358744f63f416b6c85c09ebcdf509093a550cd572d659 6584)
(.stop 9 0x337950b375121c5786df55790744b63e 5464))))

private def tree143_60 : Tree :=
(.fork 8 0xe45c51ff48083624d8a385f391 50
(.fork 10 0x104c4a128b4c6531e11f147e927f4a1d6ef 37
(.stop 31 0x3475767f59371f7750695b2d44e8592ddf55a4b8aa32cf2ac103c60536c841290d8dd442f114b4aaf31c10c9628992fe18d15664c19bd 4318)
(.stop 29 0x3364721b2d1700385e551775164a77d548136b171f786349d181462876c83eed0d5d4b40322490b5c435d16552e55d3575751f 3886))
(.fork 0 0x0 52
(.fork 8 0xbe49242d2cb5c437916545ad4b9 38
(.fork 8 0x1d6caaf2cf4c7043250e864bdc7d 51
(.stop 14 0xdac4bc3d425156df594bad8b9204692f63f2f6116445b11f9 5164)
(.stop 18 0xcd84bc3dac5204692f63f607b7d6437542ce17dbefdb2099645691765e1752d 4312))
(.stop 3 0x363f1fbf5b3 1037))
(.stop 23 0x3747721385f318542552ff52d2f811764e3b52943a192fd6cc7ef2f60ea3414181ed8fd2045e1b527 5890)))

private def tree143_61 : Tree :=
(.fork 0 0x0 70
(.fork 5 0xd317185d11b886ed 56
(.fork 11 0x1530558392108476d1dec889225cea33a9904d 69
(.fork 6 0x14e06df1bb077a245c924 47
(.stop 15 0x362647934055c098ade18d2934ebf63f0bdce093c9553fdd4554b 5016)
(.stop 13 0x3405556374d7b1b7513825c00d8d19c96b976c8556763c 5038))
(.fork 0 0x0 49
tree143_46
tree143_47))
(.fork 0 0x0 41
(.fork 8 0x12849962d54fb03f350cc43a56f8 44
tree143_48
tree143_49)
(.fork 10 0x78041428b8a412d28b5d459116c575352d 69
tree143_50
tree143_51)))
(.fork 0 0x0 68
(.fork 4 0xc244aa1ff8807 26
(.fork 4 0x2d1904d5c05a55 57
(.stop 39 0x1049d46181ddac53a3723785e7f5f63000687ed21f1437cd889942ac0fae3f2d814db200c610487dd21e89963a511e85be1812d4b40c817105cf24609233858e183cc90dc 13044)
tree143_54)
(.fork 5 0xb3d5be1bff7d4f751 61
tree143_55
tree143_56))
(.fork 6 0x9dc53815087701deb309 62
(.fork 6 0x5585c917409ab2d48b55 61
tree143_57
tree143_58)
(.fork 0 0x0 60
tree143_59
tree143_60))))

private def tree143_62 : Tree :=
(.fork 0 0x0 35
(.stop 6 0x2f9f4013a6f7da22115e4 13037)
(.stop 10 0xcdc8cdee18d4bbdd25a547d47860690f2eb 3151))

private def tree143_63 : Tree :=
(.fork 4 0x1fa4e0e74676c8 37
(.stop 19 0x3861694f629126cbeb4587401439b51c52ef863691b7da1d68876221903a5321555 3435)
(.fork 0 0x0 46
(.fork 6 0x2d68c78410d0575de5923 44
(.fork 5 0x49b26acc5f31d8e23 27
(.stop 6 0xe185a53d8a5276df68cf4 1602)
(.stop 8 0x2f0b622694f74959877da691b863 13168))
(.stop 9 0x362249db2e95791791e18ccde64e351c 27))
(.fork 0 0x0 28
(.fork 5 0xbd733d4d6b5559a53 41
(.stop 8 0xe18593ae18cd7836452765545a46 1602)
tree143_62)
(.stop 14 0xe18e336d421809df5dc00cfcdb72d4700c1319cc7650b3402 6458))))

private def tree143_64 : Tree :=
(.fork 9 0x7f6240c91440e5057431d0e655595e3 62
(.fork 7 0x3981b947731ddce01386cea9 37
(.stop 18 0xe18d933d4485a4d43a0f7e1814c3cbc15517231d19db20d8d3eb0fc95321555 7152)
(.stop 9 0x37da6fe751c2874e06e1894af530f63e 6456))
(.fork 0 0x0 38
(.fork 12 0x1698d786ffa06ed89002402c47691fa4f3b3eb5bf0 55
(.stop 15 0x32dc4a0f51c1b4528fd8f94b67f8b7da76a38602ab1bfde189bf2 4598)
(.stop 7 0x33ff59c786076a37da5bcb6c8 1880))
(.stop 15 0x363e579386335e37da64e351c02bc9102cdcbdb4a3d43c5e3b5b3 5461)))

private def tree143_65 : Tree :=
(.fork 5 0x8fc2d150435de5780 32
(.stop 18 0x885f2cd7f7f3f25e3735a5bb96f066d386333d14b852e9895626b7da2cdd78e 13001)
(.stop 10 0xcd696ee5bc386333d14b852eb7da6fe75b3 3598))

private def tree143_66 : Tree :=
(.fork 8 0x1908a2b319ccde5321938671763f 44
(.fork 10 0x126c5c21f809ab2f44be7433d15d45cd89c 46
(.fork 6 0x2e4b45388cfca410d780 15
(.stop 6 0xdb216f2df68cf4dd1e0fc 7308)
(.stop 9 0x32e75e376c85bcb7da2f0b3ed671b50e 2871))
(.fork 0 0x0 28
(.stop 10 0xdafd791e18dbfee180b2e383b6c828a94c7 6030)
(.stop 21 0x37406b8b862318b8608f0b2cb285335852e980c66db7da5bc9924649b6c838395d26b43402 3316)))
(.fork 0 0x0 38
(.stop 15 0x37cf47d9283cdfdbf9df680c21b44925db204951fa4f1f3f294ab 3035)
(.fork 0 0x0 42
(.stop 19 0x38624a2f8606ffa06ee18c0c02210a4133d0d8252e14ba6b4b7da6fe75b34a3d9b8 5295)
(.fork 0 0x0 46
tree143_65
(.stop 13 0x3862597b2eb2210a4136094badf69bf9d6ccbdb35b337b 3603)))))

private def tree143_67 : Tree :=
(.fork 10 0xd80c2031065019709252b010da4a09284 36
(.stop 24 0xe18143a6925bf0e18d0ddce45bf9d45ca322ab50c74398a1d02694b67f8b7da381942be1895566d95bf2 4042)
(.stop 8 0xce44d86d0115e6d0286d13f0763f 67))

private def tree143_68 : Tree :=
(.fork 0 0x0 63
(.fork 9 0x2710e2c39214c853c196089031ace12 41
(.stop 6 0xce45203d200bce381989f 3753)
(.fork 0 0x0 29
(.stop 9 0x36336ffb86326962a7ce45bf9df69938 5164)
(.stop 8 0xd8cdbfee18c9a5ce44ea96fcf372 5164)))
(.fork 10 0xbd049e14d8ab82d6cf2855096ec5bcb6c8 62
(.stop 4 0xcfacea947b91fd 3321)
(.fork 0 0x0 52
(.stop 12 0xcd694ba60337da50c739131e55d6649b86350b177f 4601)
(.fork 0 0x0 69
(.stop 30 0xe178499df65d1acb35a4bce44dfb8a9b86224510e6481143c5559b65743363f607b35a5bc38634c394b852e980860337da3830e22 5162)
(.stop 13 0x335a5bc38634c394b852e980860337da50c739128c363d 4601)))))

private def tree143_69 : Tree :=
(.fork 11 0x3303000c219608842904cf434114b852e95d4 62
(.fork 8 0x9d430916f85c91ba89ab3ee8fc5 36
(.stop 30 0xcb25895d0094c8d4351e952bd9b8d88965f59937d764ce06ee18c7e9db207f240d578e693f85e1f9c9032f7ce01431d556605dd0c 6009)
(.fork 0 0x0 50
(.stop 16 0x64e385e884f74964cdbfee18df4ddb2014d192c92236050535985662 13596)
(.stop 10 0xcba5933e18c7e95545f4ddb211fd532363f 1732)))
(.fork 0 0x0 68
(.fork 8 0x10c9122d3075a1fa5286db20b5b 48
(.stop 7 0x35065990e0772378635ded925 5727)
(.stop 5 0x362c7f87863691b63d 7166))
(.stop 14 0xcd694315bb180860336c81fa4fadd6cc3862488e1747e7391 3880)))

private def tree143_70 : Tree :=
(.fork 0 0x0 55
(.stop 13 0x1668d4355e5d8a4e075529bfee18c75e28c92824a1192c 13322)
(.fork 5 0x5c4246116645ab2fe 42
(.stop 2 0xe18ce07 2029)
(.stop 15 0x37d564a750d1205a54e18d42cd895b717d4b86135ad5565797629 6882)))

private def tree143_71 : Tree :=
(.fork 9 0x161194c9142494a3033bcd07382ce23 52
(.stop 21 0x33ed6d9b63f45d1321d42580ad449c0176a37da2cdd31e579d78ed6ccacf319d42b50b14b9 2888)
(.stop 16 0xe185548d6cd78ed470e0edb216f2df69166550554ccbf8e125e4763d 2311))

private def tree143_72 : Tree :=
(.fork 0 0x0 41
(.fork 9 0x2f419086dd2464e0638812764a41a46 70
(.fork 9 0xd3058427a245092528c0fb03f350cc 63
(.stop 14 0xd41966e6fc38636ffb3fe2aecacf2facd92d8fcbe43848e1c 6030)
(.stop 21 0x33f969538636ffb62c2b3cbeb648df48e17931455175b31b80907cbf848f1fa59c96b976c8 1740))
(.fork 0 0x0 68
(.fork 5 0x430c247f83a51203 63
(.stop 12 0xcd992824a1362550b1bfe7f878633848e1c52b94c4 4456)
tree143_70)
(.fork 7 0x27526acb403a80ea95547391 63
(.stop 24 0xd43943ae18d933d6bdad4e189ebfdd3d556d8fc53214f05bf2478b413a6cfb94a133662f38e1238714c4 3585)
(.stop 7 0x351c48094c3d8e4d8636376c8 1900))))
(.fork 6 0x2d14b5a3f297795e0352d 62
(.fork 11 0x27509e83091b9487f24789ab3a80ea949ed28b 42
(.fork 7 0xab33648eb048094af530d9b8 29
(.stop 2 0xdf69bf9 6456)
(.stop 22 0xdf69ec4cfa992ad8fd817cd650354c7b74e5999b64db216ec7d36218e18d0dd52cd4bf5bdf51c 4740))
(.fork 0 0x0 58
(.stop 26 0xcfb5ec4df68e9be188fa86705bf5cb99b64db216ec7d36218e18dbfe7aff36b191c9222f7cbe3385d0d843754bf 6160)
(.stop 20 0xd4386cfe18d933d4706bf55236223129c8c7d376c85bcb7da21d8886363503a532363e 878)))
(.fork 0 0x0 68
(.stop 15 0x340a2434a2bd8fca325515810df69284d894043034c5c42f4cbe9 1758)
(.fork 0 0x0 70
tree143_71
(.stop 27 0xfccd439c8cdb20bc6cfe1bfedd40271191c0b902ec49b1d8515c5bcb7da317cc7643995dbd6cc922385d0dd52ff391 13885)))))

private def tree143_73 : Tree :=
(.fork 12 0xe04388243491e33bcd07382ce2347b51fe5de5780 50
(.fork 7 0xacf2f5cfb95515548648d927 41
(.stop 17 0x1177e18d77dcf9da50cb48755430d9c2e17943ddb10bce2f90fb05311a46 14157)
(.stop 11 0x1157d8d86c7cb48a1a1d559c2e17955969437da 13864))
(.fork 0 0x0 64
(.stop 20 0xdd35a50cfa618de1792fe50f578bdb10bce2f90c5c3ec3628387515745dd5e1d6cd171 4039)
(.stop 21 0x37d36b538617f8f6bd607d93bdaec5b5df6927ad8bd1f3db10bde2f9116645a9541553363f 4471)))

private def tree143_74 : Tree :=
(.fork 10 0x16d45c01b78e07388515b45d542150d99b8 45
(.stop 25 0x32e21f9b4856feb2ca5df59b4e18c7712f4cf3d47b51fe649f7d526c4d053f1954555216ef66d763f4a3180e 4180)
(.stop 3 0x38633ef362c 3456))

private def tree143_75 : Tree :=
(.fork 4 0x3180e0d7237515 55
(.stop 19 0x352d47fb3fb3ef1adbe18e2a7df69203db100c21baca3228fccf834011f64a09284 3605)
(.stop 12 0x52eb7d435cb62552b94c459ada46d8ccfbc3f0f51f 14020))

private def tree143_76 : Tree :=
(.fork 10 0xcc4ab17249b22904bd82fa94b852e95d4 50
(.fork 10 0x54077528b4a403194c78552166159896ef 58
(.stop 17 0x32cf6dcb6c84a4b7d6479f6b95ded928e18d0e8d47ce1747c91f949fd287 3158)
(.stop 4 0xd020c75387f2ff 2179))
(.fork 0 0x0 42
(.fork 6 0x16d45c03ac10e866e1ad2 58
(.stop 9 0x3862313ca12db212745def86343756f7 2171)
(.fork 0 0x0 66
(.stop 16 0xe181292db211f7d6cc91245cd5585bff408481363f31d4d9149dd28f 2307)
(.stop 6 0x47df6c8416b63f45d7391 13055)))
(.fork 12 0x1b1ce1750f3524052c2f231dccee3cf980e64a3529 64
(.stop 17 0x38607b0774d83ef3ec0fe4ce96945f5488578631fa4c6164eb6c847fd935 4010)
(.stop 2 0x31d763f 13201))))

private def tree143_77 : Tree :=
(.fork 0 0x0 58
(.stop 15 0x32f0415f7497003515244cb3755156f2df694ca59c5ad9db110dd 5027)
(.stop 21 0x37d97235fe1d6cd4c7e18954a6dbdd1c7d520fbd8c891343192922cdd5457f8b7da532b639 3746))

private def tree143_78 : Tree :=
(.fork 9 0x7f828c8b4c2d6cbd32fa4f273cf7391 27
(.stop 18 0xcb587535e4374c3651782cba15e564e7629555d81ed8fd8107f8a21adf69702 3309)
(.stop 3 0x35107d53863 7309))

private def tree143_79 : Tree :=
(.fork 0 0x0 55
(.fork 8 0xd439112bc76c24951684a09284 56
(.fork 8 0x54053f1b7c6ec245c92443691f4 27
(.stop 18 0xd695c00df44bc755632e72694e88555f63f28cb3914374b373ebd0cddf69702 3597)
(.stop 12 0xe18dc8dce450d8d468b3743356f2df694ca6fcf6c4 2469))
(.fork 0 0x0 66
(.fork 6 0x17086dc2d38b5931a0c75 42
(.stop 4 0xdb11702df690cd 5322)
tree143_77)
(.fork 8 0xe0438831e0eb059756665e0352d 58
(.stop 29 0x3508576f35962b38622d7142cd44192f6b59bf0dd385ba28c9bf2d8c5fe2df694ca6b676c41ff4e173ef8fc143610dd52cd4bf 4896)
tree143_78)))
(.fork 20 0x16d4a2d2d2c90335ece994c476c45329702df682f417146e32d6ce0c38896ec5bcb4a4 56
(.stop 16 0xe179c00884f6bb721f6c564cf39159d763f434b863127853f41351f4 5748)
(.stop 7 0x3637531f863434b63f671752d 779)))

private def tree143_80 : Tree :=
(.fork 17 0x4ac245014d0e2491f2d6cc6231e4d7e49f128a5bb16f2d29092528c0a41 43
(.fork 10 0x750e0b47d362f099ca3931d4e963ec992a 38
(.stop 6 0xce0cf3fd01c90adf55157 3184)
(.stop 19 0x32cc7af77d552c75b33e9f596628f47640d16756fdf62c6fe1c85cfed54f5777863 4874))
(.fork 5 0x49547f5675721b63f 66
(.stop 5 0x35b304ec49bdb119c5 1343)
(.stop 22 0xcb3589ce179c01db11321cff0b5449f78631adcfa778b76252860d0747bd1fc597d66466cb63d 5297)))

private def tree143_81 : Tree :=
(.fork 0 0x0 66
(.fork 6 0x14fc6dc200080531a0c75 55
(.fork 23 0x5b51700a3833acd0349dd28f54f5550d8e42fc2d38e14242cea1437528a5555da2db10e1a45a1282 50
(.stop 7 0x14c7dafd543d8ad8a4e185548 13302)
(.stop 9 0x14c7dafdc8bdac5543d8ad8a4743363f 13302))
(.fork 10 0x534389247ca2a2d6cfb63f2527c4a2b4a4 35
(.fork 8 0x126c63c1b5cc6d3800ea94319932 38
(.stop 7 0x34011b11439d8fd8a4d891bf0 3041)
(.stop 20 0xcf9e0f6d659926cfe59c5744f63f64c77d31b58b533ef0fc36da737f3f1128f606f5b3 4592))
(.stop 3 0x363f67176c4 2307)))
(.stop 27 0x374d607762c5e032ed1d68a25530b6c819006cf242d0ddd8f43091b900330300912412105252e34a41bac7f82d6f309 22))

private def tree143_82 : Tree :=
(.fork 1 0x139e 67
(.fork 6 0xe3c5cb1da87782f68be8 66
(.fork 8 0x1084b112c853f1b706e931a0c75 50
(.fork 9 0x14d220c9113604d92383d54555216ef 55
(.stop 14 0xcd894c8555763938837da03085c22494ac045a12824a11429 3590)
tree143_63)
(.fork 0 0x0 36
tree143_64
tree143_66))
(.fork 0 0x0 56
(.fork 6 0x540a3328f904d47d11f7 55
tree143_67
tree143_68)
(.fork 0 0x0 51
tree143_69
tree143_72)))
(.fork 0 0x0 63
(.fork 7 0x27114c853c1ba48903848e1c 70
(.fork 8 0x34c39212b84b5245092528c0a41 46
tree143_73
(.stop 20 0xd449552e185dab7b1f86328dc1410ba049b1d98ea93c736c42f390e952b94c4691b52d 3305))
(.fork 6 0xc245ca173c7f82d33309 42
tree143_74
tree143_75))
(.fork 0 0x0 69
(.fork 5 0x41e22188962af8ace 51
tree143_76
tree143_79)
(.fork 6 0x7884162b18f2e3cdb392 70
tree143_80
tree143_81))))

private def tree143_83 : Tree :=
(.fork 9 0x27b172876622409aa26b0bde3ce1818 50
(.fork 11 0x5bd1b646e61dd47e626c4cf33414fb93f190e0 24
(.stop 11 0x32ed45d77d57235f4edd341c8d8bc5a32f4d552 5742)
(.fork 1 0x350d 27
(.stop 9 0x1bfad6a51ed66ff74d59bb63a07206c2 14156)
(.stop 2 0x35d7636 13871)))
(.stop 8 0xd4b0f3dcbcc91c2f9763f36332f7 2477))

private def tree143_84 : Tree :=
(.fork 6 0x267c9b131e0d05438363f 42
(.stop 7 0x385e7f877d549d774d5541b5f 4301)
(.stop 6 0xe17df54df552754a475b1 4020))

private def tree143_85 : Tree :=
(.fork 0 0x0 34
(.fork 6 0x886c91b589124a455e5 42
(.stop 9 0x37d56fd32f86fcf863073c37d102ce07 1476)
(.fork 0 0x0 57
(.stop 5 0x181ddd3c5c433f94be 13745)
(.stop 15 0x143bdd3581dd2150594eb786362672f802f05b83180fb43f2f410 13874)))
(.stop 21 0x348b4167632361d43bdd1115545d54c9d8fd0d552fb7d802e80bc097cc6031dcfb43f2f62f 2033))

private def tree143_86 : Tree :=
(.fork 0 0x0 47
(.fork 7 0x63c1d9091f2d18e9a49f128a 66
(.fork 11 0x42514fc8002014a2a28f4fb63f250c64395671 49
(.stop 12 0xdb1d320cb794cad6587582440a2c3600e9c3ab5926 4753)
(.fork 0 0x0 50
(.stop 25 0x32c9433b3fc073c769db1d28f54f774f38318a978d60f6cb69c8d7f860fbd8acd05383ce1f43550e05bbd899 1866)
(.stop 3 0x363f22172f8 1187)))
(.fork 0 0x0 69
(.fork 11 0x65619786e3244cbd42fa8e0c38892704a494ca 36
(.stop 15 0x33603a65309d6bd320e18dbf3cbe07595541939dd3520453258a4 5451)
tree143_84)
(.fork 0 0x0 52
(.stop 17 0x359f381f7d55df37d816f49b143555d5d8fc26b10744a322149022f64be9 3456)
tree143_85)))
(.fork 11 0x26f103080521d0912248cc77412105257534a4 39
(.fork 8 0x2c85bd1900b532f30fae4a4931f 52
(.stop 24 0xe18d6eecb3589adac40a31d2f85e33b566c861385f45d58a4d8fd5537afb3603eecfc452e5546551dbef 1741)
(.stop 8 0xe17953ad8fd17555435244eb763d 4185))
(.fork 5 0x75a2894fbb6fff6c8 60
(.stop 17 0x36c1267cf2bcbb94c1723774d095747e47ed673d8f44ab1dc4b542f859bf 23)
(.stop 21 0xcdd31beee178759d695788d8e85a3d1f80311dd40a659cd93ad47c99f34150e0598b529 13581))))

private def tree143_87 : Tree :=
(.fork 6 0x108c4251708b4e4319671 16
(.fork 7 0x10431af4c53550f85f7471f54 40
(.stop 5 0x351a38319c7df68faf 2328)
(.fork 3 0x900319737f 21
(.stop 4 0xcbb4a34d468e0c 901)
(.stop 6 0xcbb4a3452d34867d4f7da 6160)))
(.fork 7 0x99d35b53ab5e4181d64df632 46
(.stop 11 0x32d66b87863531d939d214c53d420e993c9d666 6599)
(.stop 5 0x3485531f863319737f 5037)))

private def tree143_88 : Tree :=
(.fork 8 0x10c27b09f091328c52704a494ca 51
(.fork 15 0x40c12ac912268075a318528664e9b726fff6c826c8bea3198c77 58
(.stop 12 0xcfce18bdd1d27fd8e1c00dd247e7d2191f94c55ad9 4583)
(.stop 5 0x352450f363f26c72fd 4469))
(.fork 0 0x0 55
(.fork 7 0x52a1b789a428c8a3f2ab1168 56
(.stop 31 0x1d10df64f33d6d4fb6dd24c553ebf7da38314b452fb2f255295d959a1c8d7471f547f87863413b63f1b7c6ec26949b12ce90da436dbf3 13576)
(.fork 0 0x0 66
tree143_87
(.stop 23 0x35a5556385f314ce17d469c8d7471f54e18c90538319c7df69810d8fc5c41dc4bd331e0f27597752d 5450)))
(.fork 15 0x5c51b8cb462f506303ebd0cd7d4dfe28a9f7da3830e223a6b4a4 56
(.fork 5 0x53f19449a526c5542 36
(.stop 9 0x386264e748b008802314ad1555325b65 3597)
(.stop 17 0x347937ef2db70037503418d8050a386357675b53154fbf3f0142752fb63f 1877))
(.stop 3 0x352d28f72fd 1476))))

private def tree143_89 : Tree :=
(.fork 0 0x0 57
(.stop 21 0x32ef3ed1668e18c9a526c4a3e6fcf52d171091812c453622109a626c117457933922f78d8b 3591)
(.fork 0 0x0 67
(.fork 6 0x1083962210ac045d15e4 49
(.stop 37 0x35af64b5a4bdd285a1cb70516552786245551755559b65d8fc9b128cf52d3f293add8cc02f02f0b463a6b6c83c816637b11f53df687581d9899e28b0d803838fc7 1583)
(.fork 20 0xb4b5a2f4cbe93c9cfb51f5caa2431e2a7e18cfcad4b45c32f48c603ed0fcb410b4a2 58
(.stop 3 0x1fdcdf69d11 14024)
(.stop 7 0x32d733cf63f47ff7da7f732fb 6168)))
(.fork 19 0x276172825f129452014a899a3180fb43f2d0e549eb4a21d988903c70f386063392 56
(.stop 25 0x335c670f59776872cc6fdf7443885811d22c77135c8e15386542450cd9bfe18c9a526c4b3a413565c599dbf3 6027)
(.stop 28 0xcb486becb68bc1d8a178ad6950e25c0751f50878630de475428691ff50eda50df68fb93f1b2fa1dc4bd33c9d1ed47fb52d 2445))))

private def tree143_90 : Tree :=
(.fork 0 0x0 30
(.stop 19 0x3359601d80ddf5592969172f8222c35fe18ce07554341021f916e671763f5325bf8 3879)
(.stop 6 0xcbe0885d8fc87e553751d 188))

private def tree143_91 : Tree :=
(.fork 12 0x1678bd9007001d125487e6715c86d8fd4c96075bf8 34
(.stop 6 0xe179550d8dde2dd659558 4719)
(.stop 8 0x5bdf5a940cf85e72376b93a6763d 13175))

private def tree143_92 : Tree :=
(.fork 0 0x0 60
(.stop 19 0x363f64c76b795b785e7f8762b6fdf74d5543639553763610744251b586e31dc4be1 2174)
(.stop 7 0x362b721b63f45d7639553751d 4020))

private def tree143_93 : Tree :=
(.fork 8 0xe406e41bac7641dc891f49f128a 44
(.fork 6 0x1944d054105059508d434 43
(.fork 11 0x2a02e81d407604a335e8d9338890ce439d4b0 66
(.stop 11 0x3746746f6291d8740162920fbe18c88d28a8a3d 4163)
(.stop 14 0xd8cc7f1dd19d1bd8a4ea4d665bf4d0298a4e18c6d65797636 1733))
(.fork 0 0x0 51
(.stop 16 0x16cf6c772377d52214bd92fa4fc464a763d2014912248cbea31dd052 13887)
(.fork 5 0xb3f35ed4be6b8f6c4 60
(.stop 7 0x37d553276b71dc488d52c54c1 1875)
tree143_90)))
(.fork 8 0x1f8cbcc458954b6059bff7d4f751 51
(.stop 27 0x37d531432e1266385e456d17555436226fbb7432254bd92fa54b9551b62f20149122fa8c6631dd0484149280602180c 3591)
(.fork 0 0x0 43
(.fork 16 0x285d39652d177fd8ace07456d17555436391b1499838890ce52c1669 34
(.stop 10 0xdf547f1dd116ff7d3347d40ef8631b59291 2437)
(.stop 12 0xcfa9f4cdac40b552af863109480049ddf5181b762f 882))
(.fork 7 0x9e0280b3f43554be6b8f6c4 30
tree143_91
tree143_92))))

private def tree143_94 : Tree :=
(.fork 0 0x0 69
(.fork 8 0x10c27c17146e32f50bea3830e22 56
(.stop 36 0xd6bd285cb586bfe18886d2f1dec5dd0cd063f2d781d474a322ab4ac145551e35325b65d8fcc653efc98a43377da5c0993adb10d7b3650fb33f316f5dd4554b 1323)
(.fork 0 0x0 66
(.fork 3 0xa2a28f4fc9 44
(.stop 10 0xcbf54b6d8a50cd886b7da5c0b6c435ed041 3047)
(.stop 22 0xcdfdc7fd890fb4d4894bcd8f917548114c9d8fca2d2d2ce996715b727d476c45c0b7da7d4f751 6437))
(.stop 25 0x37d964e762952d9782d4894c9d8fc5c42fa498a00b08fa3415041dd45f53886b7da5c0b6c43a64eb03cf752d 5748)))
(.fork 8 0x10839614d8ab82b30f283cf3392 49
(.fork 5 0x2f02f00be2678d80 56
(.stop 6 0xdf69663d8cd059dd4554b 3167)
(.stop 10 0x603f40a480b63d31d90e6dd44fb53f2b52d 13868))
(.stop 22 0xcb4d6f3cbedd11df68c5f31d9041dd44fb588622a7e18cfcad4b45c32f48c6031dcfb4410b4a2 3879)))

private def tree143_95 : Tree :=
(.fork 7 0x7dd33cd04d59c9a556b8b751 52
(.stop 10 0xd8c19c7e18d9bc7f8750e5325556e185ad3 4469)
(.stop 19 0x350d69537507f8785e4339c89df44e898f0f86155599397d236303884e9b64972f4 167))

private def tree143_96 : Tree :=
(.fork 9 0x42010c3961b749193818e2049d9290 57
(.fork 8 0x171087a24609232698be43cc9812 55
(.stop 26 0xcfbd0da0283751596f86152f77d559c9bf4dd1d5cee18d54ad6c45a928851f3df606501b78a3231cd04e45a192c 3015)
(.fork 0 0x0 31
(.stop 18 0x57977415ba37d80044d79670dfe0dd45ae26dc5f52e18425b1b4d43b6071d9e 13581)
(.fork 5 0x48f2610bd26fff6c8 44
(.stop 15 0x16eddac656ddf54fbfe18d0593171ae26dc5f52e1850e6596d668 13861)
tree143_95)))
(.fork 9 0xb8170cbd23180c773ed0fcb41634a2 63
(.stop 21 0x374f4c6b7516b89b71e1850c74c0d421e18c3791d50cf847ff4782668bce49e928c52b94c4 3879)
(.fork 0 0x0 55
(.stop 21 0x36bf5e3b59f6b8b48b59778634165782d8e401c579762964e363f09a43831b7875e28c8c73 4867)
(.stop 2 0x47ff6c8 13054))))

private def tree143_97 : Tree :=
(.fork 0 0x0 63
(.fork 8 0x9d827b1728a372f38be452b94c4 45
(.stop 3 0x36c42668c77 184)
(.fork 8 0xe2c80328b0a3f3600d93602b4a2 50
(.fork 17 0x24d16c4750313b6c400c46e6267c636316d0d37d4f75133ccd055df177d 54
(.stop 8 0x3c9f8613a3f2cc52dd4bb5511549 14293)
(.stop 3 0x38613c9f6c7 608))
(.stop 22 0x286f358671f7d650eda50e17d1755e2b63f16ccf2c57516ee5bc32fa1dacc5b3c8529154ef527 13604)))
(.fork 17 0x27c09944ab14989122680bd83198d916d834a41db088a3cf915a45db392 58
(.stop 19 0x32df53277d5886785f245ca22db21bffdd44cf3341527fd4a488b2254908385d1f9 3173)
(.stop 12 0x3f337516fff6c8416b63f45d752924909b141372ff 13607)))

private def tree143_98 : Tree :=
(.fork 7 0x5251dd4a2d3194d8136496ef 28
(.stop 12 0xdd2553ed4211ee47f76c8316b7d576875b555598ac 4451)
(.stop 10 0xcd811fddb212926297637553f50c458f5af 4444))

private def tree143_99 : Tree :=
(.fork 7 0x9192b18b40381929054f1551 69
(.fork 8 0xc28398172476c3c88f3e4569176 56
(.fork 11 0x2fd17386df1bb09172490a3e33e4cff413589f 36
(.stop 8 0xdb2154be18a3c4d431556605db65 603)
(.stop 13 0x385e7d4b749480b40400750c25c0b6c847f581e64e363f 7168))
(.fork 0 0x0 30
(.fork 7 0x5a916d087f45bd43a5561790 50
tree143_98
(.stop 18 0xcd811fd4c5f6c84a494ca57918a5d8dd54fd431556605f3792b14ac772172f9 4444))
(.fork 6 0x316916164cdbfe81bb62b 42
(.stop 10 0xd4210d2db20b4b319d4b9cbe4ac736494af 3880)
(.stop 23 0x385e4c7b4023f2b7d7605f3fb3830e220b3c6295de9fdb97f35083ca10d247b91fddb214ca5793639 4015))))
(.fork 9 0xb8170c7ff243091d41613084c674a2 64
(.fork 8 0x334775223c89128a0c5c31cd1ff 52
(.stop 6 0xdb210d2e18e218d444e1d 3162)
(.stop 20 0xcffdb70cfa11fddb2153a8cc785e286ce9376a350c81bb8631b688843ee95d464a32f9 6451))
(.fork 0 0x0 48
(.stop 8 0x47a76320bcb5211d94a2b458516f 13867)
(.stop 20 0x62ab85e414f63f605e213d446218e18c1410ba0ac0439763705142f23168f2059b752b 13874))))

private def tree143_100 : Tree :=
(.fork 0 0x0 58
(.stop 24 0x5deb48d3ced4abd4b4fc5cfa4aaf3eb543a5bed92fe18d933d45d2875bbd89966d763f2f7cbe350c5540 13429)
(.stop 17 0x32da59cb51c18f5817d8fc64b1b356fbe18d928d4b47733a6d16145bf52b 4026))

private def tree143_101 : Tree :=
(.fork 0 0x0 61
(.stop 21 0xfbbd8c8cff50eb52a02c85bd2d4cc5ad4ac03d056c3081b5c88431b4e1ad6d877228e0a39 13048)
(.fork 0 0x0 69
(.fork 5 0x30a0e4439817245d0 56
(.stop 19 0x38626d9763f2444fa867074862f50e0c47f554bce005c317386df245ca3328f904d 5462)
(.fork 8 0x21fc88f3184c783ac0fca4a2f52d 35
(.stop 14 0xdf5d9336ffa06ed8c8023605f63f38891ee47f76c84a494ca 4449)
(.stop 5 0x363047bb5b0532363e 3596)))
(.fork 10 0x170c7ff243091d2f4904241613084c674a2 47
(.fork 7 0x2d02e87f23ca0f3c47b91fd 64
(.stop 28 0xcda9b70e188f1b40df3615bf5817d204e93551dda8df60fad57856fbe18d928d4b40cd1dd48912438a2843490e347b11ff 6309)
tree143_100)
(.fork 14 0x97c5ae21fc88f2d14fca49ef52d22110e5455117462975b6 58
(.stop 24 0x626f35a62878627f6f36b6b8b59945856f764cf86374477da64e1bf9d8fc9222f7ce1752fd5405535ad9 13457)
(.stop 4 0x47a7632458752a 13867)))))

private def tree143_102 : Tree :=
(.fork 5 0x8f25be97896dcb6c4 70
(.stop 8 0xd1f977fdacd9c8e17938d4ebdd1d 3477)
(.stop 8 0xd8a589bcdb0b4bdacd5585e43639 2316))

private def tree143_103 : Tree :=
(.fork 9 0x52b1b60aad3804e1b478d204605db65 34
(.stop 17 0x351324338625e276c46fcf8635c0b7431d94bc74ebd5583155fe2d899c81 1021)
(.fork 0 0x0 37
(.stop 16 0xd421fdbcb586bf83df6b34335fe2df6970264e9d15e18d15645d9789 5885)
(.fork 0 0x0 31
(.stop 10 0xd8994afdacd271d02206bdb11bf3e18d702 4301)
(.stop 19 0x347a74578636fcf51378b3486431127123edfe2df6953c83df6b34ea73fc5bf7405 7163))))

private def tree143_104 : Tree :=
(.fork 0 0x0 64
(.fork 5 0x88f224490e2f74be5 28
(.stop 4 0xcdd4bcddaedc87 3603)
(.stop 5 0x36bb64b736f6b936c5 3021))
(.stop 18 0xdf5d0d4e18dd1cdb14c554335427df682ee28c54ca6fcf6c43efcfc052fb63f 6884))

private def tree143_105 : Tree :=
(.fork 9 0x2ee2228b403c88f3e456917654f1551 70
(.stop 24 0xe18d933e17d0cde1795c9dd34a2d2fac5a91d5a185db10c6562672f9107c42714ecc7935f8fb043310e9 4896)
(.fork 0 0x0 30
(.stop 28 0xcd61274d898b33df4c6433a550cd43a14af530f85f6491926d021204605f63f3195702db105a916d087f243916f5561b6b 1447)
(.fork 6 0x31690d245859337d53624 42
(.stop 15 0x385e721f491605f62652edb5fd44c02814c4ab33a54eb043354af 2304)
(.stop 3 0x385f6493639 4321))))

private def tree143_106 : Tree :=
(.fork 12 0xb402e105c87f223cc6131e0e993ac127b4a2f52d 70
(.stop 10 0xdf5dad8daf4c6c55332f914ecc6231e4e0b 4755)
(.fork 0 0x0 35
(.stop 17 0x36b383df85f31b14b4dd0c6d838051e3605f491244d2704a48fafdf694ca 1313)
(.stop 17 0x6bfd891d1ce17cc6cd8fc6d8435166364919b4d8a621adf6970274576c4 13733)))

private def tree143_107 : Tree :=
(.fork 7 0x2fd192ca2d3194fb93f19053 40
(.stop 19 0x385e745b2d86fe9f54e17ce9567077d64a4b62d2f34c5b3ebd1e754ed55257255df 4186)
(.fork 0 0x0 43
(.stop 23 0x1c00d676070d421809d6bdbfa284f8637d5385f433735e0ba076650f77d664d19c1d8ed05a4e51ad1 13876)
(.stop 6 0x435340850f763b4a4b6c4 13876)))

private def tree143_108 : Tree :=
(.fork 0 0x0 56
(.stop 14 0xd0153a85c0b86350a1f54d89d274d8f0c6b31c8cf933fd04d 3015)
(.stop 27 0x35b11d3f2ca16694365e41d16768f7d56709a4fd8b5fe2df58e083f3505a4e513a8508b63f1b607662ae90d4602b2f9 4322))

private def tree143_109 : Tree :=
(.fork 4 0xe4439817245d0 47
(.fork 8 0x1b8c7f22240bd43830e2247b91fd 61
(.fork 9 0x389195865e1d9091f28e0ac649f128a 50
(.stop 24 0x62b35af4c8386362935b135f9fdbdd34faf4c2736018f06d7244ce004a494ca6295932db110d54381899 13576)
(.fork 6 0x35ccd8c3805817629363f 35
(.stop 18 0x5e276327d378634c813af55636b36722068e1799b2cbe091338014ca6295932 13152)
tree143_102))
(.fork 0 0x0 56
(.fork 7 0x2fd245c92433fd04d550954b 36
tree143_103
tree143_104)
(.fork 0 0x0 41
tree143_105
tree143_106)))
(.fork 6 0xf403e0c1091d247b4a4 41
(.fork 11 0x5bf28dcb402f38f22456917652b94c454f1551 54
(.fork 18 0x55259c169437d628c402916d86df382105a4ea363f2900d853638e13386d9b9 34
(.stop 2 0xe18d933 4009)
(.stop 9 0x33e77d5385f54ef2e45e419c8745b6c5 1434))
(.fork 0 0x0 50
tree143_107
tree143_108))
(.stop 9 0x363c31acc7233e504dd4b4a314a4b5b6 1772)))

private def tree143_110 : Tree :=
(.fork 4 0xa0c5b4ead552 27
(.stop 4 0xd8fcd85d8b5c88 5032)
(.stop 8 0x78d762d55277d60bc02f64e536c4 13307))

private def tree143_111 : Tree :=
(.fork 0 0x0 63
(.fork 5 0x3d00f8890247491e 41
(.fork 12 0x16fca370e2c6d81d9904641510d443874a22f914c4 66
(.fork 8 0x7ac6e61dcc91035e0d913a70ead 40
tree143_110
(.stop 10 0x6db33f055576c428996ffd234e13551363b 13887))
(.stop 13 0x362d670b7d55df363f5e45c88db10b5d3190fcd43a7309 5307))
(.stop 3 0x34a22f7b5b6 1894))
(.fork 5 0x3c28e0a392b1b392 47
(.fork 6 0xe24764247d1fd49f128a 66
(.stop 19 0xc4bdd3ce1adb116fad4ac6d8d8fc64b3164f1fd4801e71dcc8002014a2a28f4fc9 14145)
(.fork 5 0x53b1720c793657309 36
(.stop 9 0x36b338052712cc78634a4d3af605d8a4 3039)
(.stop 12 0xdb118a5d1e99c96b95f4ddf60c7133f94b452fb63f 4742)))
(.stop 34 0x7d3348564cf6bd5bef51b0b8b63f31c752b1b5cc6d09bce0140f5c8783ff85e107c42714ec5c828b8b5d4bfb3092014fba3f1504857534a4386b5b6 14005)))

private def tree143_112 : Tree :=
(.fork 4 0xb88c6764e363f 38
(.stop 19 0x362f097b6c86feb7466045e36cf99434cbcc897455d2fe50f73912f84fca50e9788 4303)
(.stop 11 0x35ab3c972f33ed76336ffb8633864ea8480b63d 1875))

private def tree143_113 : Tree :=
(.fork 7 0x8842b00b3a45511745791bf3 69
(.stop 32 0xdd00bbbdf649932abd0e84c819bce18d668cbcc5b9241f3804c576c817149192488c56385cf336b6739105843080c286ec2490a314a494ca 4326)
(.fork 0 0x0 49
(.fork 10 0xe104a91d6076626789b03838e2050a142f 38
(.stop 20 0xe17916950d178e695f3e65e21932df68f20db20c79455d2934bf943dce44be13eb543a 1869)
(.fork 0 0x0 52
(.stop 17 0x36c831e739145b751b693b35e360577dd8fcd8c380116245b9932df69663 1469)
(.stop 15 0x1169d8cd54bdb20f20df6916ed8fcbd7555b51b50f7391386763d 13319)))
(.fork 0 0x0 57
(.stop 21 0x386167277d82884fad45dd293e18d668d4ac89750f739100e05362698bc82f78d8b3cc9b66 3593)
(.fork 8 0x1dc8ac631b4d873630e0064cb4a2 50
(.stop 27 0x347e1d2b3e76fbf7d8554b3f34e95bfe7d332de319cfbb3f11285574f62f386516d66ff391172091136050d543813a1 6023)
tree143_112))))

private def tree143_114 : Tree :=
(.fork 0 0x0 41
(.fork 7 0x6dd2464ac63818e2049d989f 69
(.stop 2 0xce446ec 353)
(.fork 7 0x87a2698be43efcfc0604b4a2 44
(.stop 23 0x32cc628359766f1a49d24cd793ed5fe0e1883851b4953edd1ce1952c54c1ce446e031d90e659a16f5 4867)
(.stop 4 0x38673913f3752b 13606)))
(.fork 19 0x49e14d87722240ab82b30f283cf15420bdcc5f31d90cf43996e95bd7751552f5b6 69
(.stop 20 0xd01180fd439d1ce18dd11ce446ec0075675df6898a2ae8bd8579981ed8fce223eccfcc 5879)
(.stop 22 0x11fb2cf57516f0603340a45a5bfed8b1426576f3913865202720763d2678c7950a180a649b4a2 13002)))

private def tree143_115 : Tree :=
(.fork 11 0x3712bc52a1db09a426c8aac38690da436dc80 70
(.fork 5 0x76d1dec889245943d 46
(.stop 23 0x1925df5dc00cfb60fe0dbf7da86362a9d4213af6fcb63f3195791e18d4285e0a0ff86336273a655d9 14003)
(.stop 15 0x1c01df694b6e18cc65db0cd9452f554ad01143c532d5e759d363c 13877))
(.fork 7 0xc56385cf313cccfc16b67391 36
(.stop 24 0x70037d95b9f2c80d9f2ca649786231978631d60905df68bc635c1bf5d8f052b287caad4811a4b6d95bf2 13876)
(.stop 9 0x335f64b763431e127f4e8542e5bbf63f 2453)))

private def tree143_116 : Tree :=
(.fork 23 0x25a097c87922248f63f3120464b5beed8d426f1d689a04a1930e4c4f4a418c0c6135fd93a6dcb6c8 42
(.stop 4 0xce45315e18d0e8 4039)
(.stop 9 0x385e700359964bf8634c575ab1dd7529 3607))

private def tree143_117 : Tree :=
(.fork 4 0x1b7c6ec245c924 47
(.fork 8 0x12785c52240bd42fa8e0c550954b 35
(.fork 5 0x2ee18f0a315329bf3 61
(.stop 23 0x34046fe385e04ec6c42628f32d1e8f25e18cc7935f8d954bf932150f7391247cd8c3800e1a49f128a 5301)
(.fork 5 0x98a3ebd0cd7f8b7da 64
(.stop 21 0x1c00dd3528ddad5b657f7786223ecd9547b165cd2185222d1cc653efdbfbe18cfc743490e3 13580)
(.stop 7 0x347a365532150f60718637391 3193)))
(.fork 20 0x26290cddf68147191452223e8aa43194fbf4a2970264eb6c435ecd943eccfcc5ba7751 64
(.stop 16 0x83e750c62b3860388f7d93ee1428dd356fdcb9cbdd43490e34a35bfb 13290)
(.stop 17 0x180ad425ae4e181558cfc05ac2f1b50c81c7391101448a124c52b2ab763f 14157)))
(.fork 0 0x0 35
(.fork 5 0xa312ce92705329bf3 63
(.fork 7 0x3921d98bde31acc723ce1818 61
(.stop 6 0xd4b07752f9739131b4e1a 2476)
(.stop 24 0xcd81ad9dd3566ee18d43753137da49e9667d4b04af200978bd8fc52b2434c6131e0eb047b51fe5767635 3878))
(.fork 0 0x0 55
tree143_115
tree143_116))
(.fork 6 0x1db088a2b18f3e45db5b6 63
(.stop 7 0x363531e35270e48bce31acc72 2624)
(.fork 11 0x48f2610c6135fd93adb20526268130e4c4f4a4 70
(.stop 16 0x4a374025c0f7435e177d650b59b9d8f11774c05320e18cb5d3ec19c9 14161)
(.stop 5 0x33914c5786343a351f 3045)))))

private def tree143_118 : Tree :=
(.fork 12 0x9bc4ac1720ac6361cd8cce48392108477b2227309 47
(.fork 10 0x12787643188c7935f8d9549f128a550954b 48
(.stop 21 0x359670072cf604363f38515435e0b625938786319546e03c954235bd77511b5d1ef52d54bd 5882)
(.stop 17 0x374d5beb362553f86352c1810d8fce141b80f25dd44e1a436d1685763633 3605))
(.stop 2 0x386b5b6 13476))

private def tree143_119 : Tree :=
(.fork 0 0x0 68
(.fork 2 0x34c309 35
(.fork 3 0x11e2480d557 61
(.fork 7 0x3900e5c6e431b4e003869932 63
tree143_83
tree143_86)
(.fork 0 0x0 69
tree143_88
tree143_89))
(.fork 0 0x0 47
(.fork 4 0x2240b463a68eaf 61
tree143_93
tree143_94)
(.fork 4 0x2b18e9447a35b6 67
tree143_96
tree143_97)))
(.fork 0 0x0 62
(.fork 1 0x9ab 67
(.fork 4 0x9d427a1b946ea 41
tree143_99
tree143_101)
(.fork 0 0x0 69
tree143_109
tree143_111))
(.fork 3 0x53f413741b 67
(.fork 4 0x170c5ce28cca3e 35
tree143_113
tree143_114)
(.fork 0 0x0 69
tree143_117
tree143_118))))

private def tree143_120 : Tree :=
(.fork 0 0x0 71
(.stop 13 0x32c8840218e88722aa8ce23c691524e295c25fe9a3271a 8306)
(.fork 0 0x0 65
(.fork 2 0x7b865a 51
(.fork 7 0x38d1b9c7681dd8e1038795d4 68
tree143_1
tree143_9)
(.fork 0 0x0 61
tree143_13
tree143_35))
(.fork 0 0x0 59
(.fork 2 0x1090cfc 66
tree143_45
tree143_61)
(.fork 0 0x0 53
tree143_82
tree143_119))))

set_option maxHeartbeats 150000000 in
set_option maxRecDepth 100000 in
private theorem no143 : ¬ Good 143 13 := by
  rintro ⟨c, hp, ha⟩
  apply check_sound (apRule_hits (by decide : 3 ≤ 143) hp ha) tree143_120 (fun _ => 0)
  · simp [agrees]
  · decide +kernel

private def tree156_0 : Tree :=
(.fork 11 0x16d05c0208279c9f83d697395cf57d45f5d9a5 37
(.stop 19 0x397e6b6771a44af5e955a173ccb54b0a2c74cf135d8fdea0fb8e636355796bb22be 4238)
(.fork 0 0x0 70
(.stop 26 0xce09e7dd28666dcb5590ad2c4d82423a22fd0457e4cbad74761fd91b7ca33753fd768022fcec33d74f6844ad139 5962)
(.fork 0 0x0 54
(.stop 27 0x205ed9e0f44d0410775f1dfb3861f3655cb5749e398940447d69283a77bd05b82a10cf0b1b2cb8c664239ad96b6dc0f 13632)
(.stop 6 0xe399692da0077e401b722 2368))))

private def tree156_1 : Tree :=
(.fork 9 0xa682c08ed04e3d3a950a9c1572bf2f4 43
(.stop 10 0xd75dc23e3ad7e5e3a6709d522195e399fb6 5931)
(.fork 0 0x0 34
(.stop 11 0x3548708b8ea41e37ac861f5d75f978e93aa5c23 1888)
(.stop 5 0x38e99c2754872fb8eb 6117)))

private def tree156_2 : Tree :=
(.fork 4 0x3d1113249a974a 62
(.stop 20 0x35e3672a35b84b5cbddf0da35a46e13173cdef047220389422ef92674e6d39d50e1c17 13475)
(.fork 0 0x0 57
(.stop 18 0xe39a83ecd9590d6905c0fdecdb89d7a173c07b8fdb44459b67ca768061c1f19 3928)
(.stop 10 0xce15df0d9fe403deccc6651158826e275fa 5494)))

private def tree156_3 : Tree :=
(.fork 11 0xd305b847d1dbc94d3b00ed03d6d73a5cf1870 34
(.stop 11 0x19b6da39aecd291c14cbc08a3dec4ea93d1174a 13036)
(.stop 2 0x228f68b 13190))

private def tree156_4 : Tree :=
(.fork 0 0x0 75
(.fork 8 0x11fc5b8231094f2f2cc6633add5a 49
(.stop 11 0x367f900f5d64956840e38801e6bb9f29dc69b7a 8132)
(.stop 15 0x37b102a9084debdf1bce1942a9e9771a6bbb6935ac74226e27686 495))
(.fork 16 0x1d8802a0cac93f5cb174ad9fc8a52500f68447d13c5a496af7c6f5fa 54
(.stop 11 0x36854e435d888ab855510f8e65f9353a642190d 3453)
(.stop 2 0x7ca7729 14113)))

private def tree156_5 : Tree :=
(.fork 13 0x20b083c5b11904b242cb8cdf33d51324c0139a4e79e84 40
(.stop 4 0xd2e97e5e3adf1f 4557)
(.stop 13 0x1390e601d4ed75a0f0dc89e8394deaaae3ad7e57edf37a 14270))

private def tree156_6 : Tree :=
(.fork 0 0x0 75
(.fork 8 0x11fc5b8231094f2ef0bcb319972a 49
(.stop 24 0xe3aa70acb5605fe39a195e5f9f29dc6990794df8eb11945a30f0c7f94e6f7b1366525a49d13906de9c14 7202)
(.stop 3 0x37be6e27686 3461))
(.fork 0 0x0 62
(.stop 28 0xd011d4dd291de8e6019a900440aa337b84c9c2384b703f7bc05ccd7650a986ee3a4bbe2f24c443164f654e6d39d50e1f1e 5962)
(.stop 29 0x32f6226b7ba75435d81618ba85f638e935db7217ca74ba64378e65d257e5d7d40c324fd1d75d2b67f22949403da111f44f35fa 5008)))

private def tree156_7 : Tree :=
(.fork 0 0x0 74
(.fork 11 0x4801243eb121465320688b4315cc6533c4d00 54
(.stop 16 0x7c736931b4b7bd50e1fc5e12c16e0a8433c2c6cb2e3fcd08e6435c0f 14256)
(.fork 0 0x0 62
(.fork 7 0xb232cbcbbe499d39b4e75438 49
(.stop 11 0x384c6b86708e39a83ed9fd73c66b38e36dbdb7a 6726)
(.stop 20 0x8b0398083ef548900b8e35cf1870778f68d44ca35bdef9422814a83ee399ae172bf2f4 13475))
(.fork 9 0x11114e7801c0074f597f137217ca7722 49
(.stop 15 0x38e6a0fb5d761c35481178ea95f99c23e3857e5e38db6f6de9c14 4853)
tree156_1)))
(.fork 0 0x0 46
(.fork 11 0x3d61dc477e2030c5e3fad0065579579752dde5 44
(.fork 10 0x3180c811c08a52500b243da111f5a49f1b 57
(.stop 25 0x36841d472c97c739802c3556992734a16deb8e955ee188888b8e66435a41decc47d1dbc94d5cf18707c6604f 5962)
(.stop 17 0x1267d0100ac2ea37bc64378e63109c1ae13093f253d1b95cb174a7c7367f 13813))
(.fork 0 0x0 34
tree156_2
(.stop 19 0x384c7c7368611f4b134993692499d747e13d8606db1ca4e3809cc6421c1492738eb 7194)))
(.fork 0 0x0 31
(.fork 5 0xc4f44492674c0d91b 57
tree156_3
tree156_4)
(.fork 6 0x25352ed620205283b3557 63
tree156_5
tree156_6))))

private def tree156_8 : Tree :=
(.fork 8 0x11c06392c911ba57dd6927a07423 49
(.stop 17 0x3714752384b708f5d87a3b8e9581ddf3d77dde7e3992f54c393904ea1e7c 7668)
(.fork 0 0x0 43
(.stop 21 0x1f29dca5085e399437e1325d3cb2d72be3a46c75a7d73b61cf84d27691b949516915cb1f1c 14113)
(.fork 0 0x0 57
(.stop 12 0xdc91df4e3a4b0f581ddf3d77dde7e39a195e129870 6427)
(.stop 21 0x37297ca75d74481738e12a0fbdc7e0fad502401d9e2708d795df3dc900c42538a745caf693 6259))))

private def tree156_9 : Tree :=
(.fork 15 0x33c0cc4eb83b452f54c39390ce4c7803adced03d4938f4ea542a 30
(.stop 7 0x32d683eb54900786c7d521f29 8288)
(.stop 7 0x762e3a5fc4d7956af7a07680 13486))

private def tree156_10 : Tree :=
(.fork 0 0x0 44
(.fork 9 0x2a250111f46e95f758556925abde81 57
(.stop 7 0x38e699bb5d81df09e85a89870 7810)
(.fork 0 0x0 49
(.stop 10 0xd761e8ee3a6537cb35e82e3992f54e413a8 1777)
(.stop 25 0x35e52ea767092432e007938e91b1f84d5a7b84c9c0f4b22f294371d4d113cb2c7fc3fa22cccb31de77a0b393 173)))
(.fork 0 0x0 41
(.stop 22 0xdc51df4e3a6060d525a52deadfc5e3992f54c393904ea1b6f6deb3932534b0e2ef52ed6202052 3930)
(.stop 21 0x2aabd762499e3a4a62e39a231d280ec05a89870ce4d437818368b057432b0cc4d766bb3692 14563)))

private def tree156_11 : Tree :=
(.fork 9 0x48012421d0fac485121881a315cc65 55
(.fork 12 0xa8878722fca812c70b2f3d64f6c3fd17d35f61ada 56
(.fork 8 0xd80370350ebf3d697395cf5a40 61
(.stop 2 0xe15569e 5175)
(.stop 11 0x34b2708f85599b78e930f974b708b7b45a4b8e6 1881))
(.fork 0 0x0 35
(.fork 5 0x59f2c6cd8b5abd74b 61
(.stop 5 0x32ec5f9b3863160c64 5962)
(.stop 2 0x7ca7729 14113))
(.fork 0 0x0 41
(.stop 11 0x1120dca462b61cf84d4bd6195e398bbd4bb6052 14410)
tree156_8)))
(.fork 0 0x0 63
(.fork 11 0x1710abc64c195ca892a50b242cb91324c01303 48
(.stop 19 0x39817a0e5d3e3823f4d79539d6b8771a1e00a68a5d78e122a4eb73d493a950a9c09 8742)
(.fork 0 0x0 49
(.stop 22 0xe60539d691a225da2d880dc520f0e12db87862f8e338d4eb84bd530e4e413a866799ac6dbdb7a 6738)
(.stop 23 0x35488b338e07cab4b13161881cbb574b8fd3717704f84c1dd4d83387925b49cd2f64c3590464472f5 6893)))
(.fork 0 0x0 43
(.fork 12 0x22cc9da2c8d1b9475d25449cd6915ac172c5d29f1c 48
tree156_9
tree156_10)
(.stop 36 0xd292190deb1091e15063a1fcb68b7c6a8dae39908557e16147ed32f35abdb88708b4bf0d2847827a0e363b00ed0471d69f5a89870ce4c78d2088b2940074c7 7668))))

private def tree156_12 : Tree :=
(.fork 7 0x2a00ad72c5d29e827c734c7 57
(.stop 12 0xcb609c7e3a1de3cd9cfeb55e5f19d7616a261c204f 5636)
(.stop 10 0xd795fc4cdd8ba4d761579d52462e75635e9 501))

private def tree156_13 : Tree :=
(.fork 11 0x3600dc2a222fca812f2cff440193a25f4d7d8 48
(.fork 7 0x3d111b06d81b9080e50a9f17 29
(.stop 7 0x1e8ee38dc0ee398773cbac76d 14114)
(.stop 8 0x5f978e37039de2e39973e7a3b678 13489))
(.fork 0 0x0 27
(.stop 12 0x249f8e8708b7b48feb729703a052e39908f4e6d437 14251)
(.fork 0 0x0 68
(.stop 16 0xcbc093cd055f1ddc8939dd9e2703d4ee66dd774ff940052fb4c2143e 7023)
(.stop 9 0x37ab6dbf2f22ed53a15f975dd99b7855 6726))))

private def tree156_14 : Tree :=
(.fork 0 0x0 67
(.fork 8 0x5ec3dd2570c5e3fe90944bf1307 41
(.stop 20 0xe3a5f239c2b4ab88ab8ea2f10eb73b4142a5f7f2f31db08085d1205fe39930d7072052 4845)
(.fork 0 0x0 49
(.stop 19 0x340075035e36b9f40f1d9ceb73d4f5e525589e1360d2f65aa5adfe3997446dbdde2 7341)
(.stop 16 0xcb3dad9dc682a935ccb0a46cf8e83b412625a7d6a261c190a642f38d 6718)))
(.fork 0 0x0 75
(.fork 5 0x3ea2c74b303629b89 53
(.stop 8 0x7caf8e64c36052da38b1a2f25008 13959)
(.stop 16 0xd9c972ae6043cbd2cd2674e6da39da00d993d4cf6d4969390778b393 4845))
(.fork 0 0x0 72
(.stop 31 0x32cd22372d683eb36b6b65adb703f2f34c36052e3a0ec37089cbcd2ecf5b3da969f5a89870642990bce4c6551b90b1a3634d993fd5d57 6718)
(.stop 11 0x34a15d15e7dda383442ca4ff9400526d50fb4c7 5937))))

private def tree156_15 : Tree :=
(.fork 13 0x3605b833c0d088222c6cb2e42390a161cdad96b6dc0f 75
(.stop 16 0xdebe194e398d8344af85538e590e72ab3931e18b1d2cc0bbc3d60f6d 4411)
(.fork 0 0x0 62
(.stop 5 0x336b4e6d39d5cdd73f 4711)
(.fork 11 0x3dd1dacd833cf512b50df5e92ed5ca972ab7bd 72
(.stop 8 0xcd96973e5f9f16debd13b470e194 5163)
(.stop 3 0x36926bb38e6 1900))))

private def tree156_16 : Tree :=
(.fork 0 0x0 48
(.stop 14 0xcde99b8694dd5ad31c32b29ede8ee148768e399aecda00eb7 5497)
(.stop 4 0x360f8e66bb3692 13963))

private def tree156_17 : Tree :=
(.fork 7 0x46c1b60b153adced050a9745 61
(.fork 8 0xaa06f11dcc94127f0b3050d9437 63
(.fork 5 0x5b122a49dd49a1303 42
(.stop 4 0xda00775e5f9f1d 1888)
(.stop 4 0x1dd72e64bb78e9 13498))
(.stop 11 0x35497a3b8e37ecf4ba274368007c4bb55f975e9 2356))
(.stop 13 0x34c75d0384875138e344bc7531d80eb04bd368044d755a 3475))

private def tree156_18 : Tree :=
(.fork 0 0x0 41
(.fork 11 0x3291b448a22534b0e40051394bb530d6202052 66
(.stop 9 0x371275738e6250797e7c8b6874e5d3a1 5497)
(.stop 13 0x38e6250797e8d9b6875ac57e5d2e89ebe3894457a437bd 7979))
(.stop 4 0x50df55a44d7692 13963))

private def tree156_19 : Tree :=
(.fork 0 0x0 49
(.fork 9 0x3d20f646e52ca4d994e413a86de9de2 41
(.fork 12 0x7f4465228894d2c392ed1d7cc37313205fe39930d 62
(.stop 5 0x35e351174a66919f1e 5019)
(.stop 18 0xd9e0ebce3a41ebcb584502730e10cb3cb00333955ed2aa0fad7a572aaaab97e 355))
(.fork 0 0x0 55
(.stop 10 0xd761e8ee115d41e398ff44019a3f6b69e7c 2239)
(.fork 0 0x0 62
(.stop 27 0x3845b6d767292678e46bb38e64295140e604ffb708a2c0d2ccf53d31cb1044a12fc8b2f852499d39b4e7560368e5a46 10922)
tree156_16)))
(.fork 0 0x0 29
(.fork 4 0x3f68ff54e75fc4 55
(.stop 29 0x32d84bf354994c35d83d299a6cb4c58588a666dd9e56a35ce173ee39a3fad2e82a21db48bf2a04d033fd10065f4da3f6901ada 5174)
(.fork 0 0x0 48
tree156_17
tree156_18))
(.stop 16 0xe39a052e115a3fce4d1284bf2701d5401740aa0348255895d44bf555 4084)))

private def tree156_20 : Tree :=
(.fork 10 0x25349e92c38ba94bb530d511572a5d31880 63
(.stop 21 0x35d87a0b4a788cb3767f1384d55ed6af72cdde7cde9d588d7397e5f49873d2e91324999303 5788)
(.stop 15 0x12e135b89cde9d58e5f942a510f2f7643b7b12c6d6af6bbb685 14268))

private def tree156_21 : Tree :=
(.fork 13 0x1571da0d7655e6224e154d8a3898f443f7d1325d29b89 35
(.stop 4 0xe601873e605aee 2824)
(.stop 7 0x802cda25d2e602368927367e 14410))

private def tree156_22 : Tree :=
(.fork 0 0x0 44
(.fork 10 0x2c9111f44f1255557157b5a496af779de81 57
(.stop 3 0x36763b41604 3466)
(.fork 0 0x0 43
(.stop 30 0xcb7c76288cb4a20ebc757223f2c98afe359e15157966e22bee3a173b7ed72f75f65f298da249cda151c07f136764c3d72c5d29e82 330)
(.stop 13 0x36766e279815f65f29d9f8d76ce1d1c04bd9a456b5768c 4077)))
(.fork 0 0x0 53
(.stop 29 0x384d8aff2ca3aa8f45d9f97d25f6586d61cdca972ab7aa8afb84c3628f443f7d1326209b89da2cd01402186c61d19076439d44 5497)
(.fork 8 0x18fd1c04bd9a3a6915ad56b7f429 48
(.stop 20 0xda0088f55ab2d87a435553f7dc0fe60130368e1a47d9f87733adced03fb52f44c3d42a 4710)
(.fork 0 0x0 34
tree156_21
(.stop 19 0x27a5d9f9aeee391078d524c4061c32d87a437bc08189fa33c156a58156075cef68b 14257)))))

private def tree156_23 : Tree :=
(.fork 5 0x2af2088f5f3d99001 43
(.fork 10 0x22cccf7364ceb246e572c5d29a4c7a09f1c 48
(.stop 24 0xd2e9ad5e605f29d9de7a3cda1e8ee3a6366d7950855851d4cdea8e1844f1692779f555510d7315d15b6e 6245)
(.fork 0 0x0 55
(.stop 10 0xe3a1579d2e9f29da14a7c3b037145ce17d3 4075)
(.stop 13 0x2366d9f9f29e605a456b572f758118747f136765a4b68b 13797)))
(.fork 0 0x0 48
(.stop 14 0x68eb6935a7f85431777bc0a9d0064c217385f634bf510d745 14410)
(.stop 3 0x368c3b03727 2684)))

private def tree156_24 : Tree :=
(.fork 0 0x0 63
(.stop 39 0x173ed760febcdbdd58dc51d50d069fc494df5e218fccdd384f7b47ef384c11f48b32eacce146e572c7069d4e7a09f1cdc9c9f0473f43505d05b12c90b2e44c926649a1303 13047)
(.fork 0 0x0 65
(.stop 36 0xcb2e0eed7bc941cda5ad56b7f2f75801738dc50a742c3cd7b494d7e572d5fb7d9f8d7641f5fbce13047d190c8b333851b95cb1c1a7a09f1cdc9c9f044c11cf 1875)
(.stop 7 0x35e8191143c5f634c7364f438 2390)))

private def tree156_25 : Tree :=
(.fork 0 0x0 55
(.fork 9 0x2a7191064f22fcff4401943150f17d8 62
(.stop 18 0xdc3dc1b7a0f8e38d6f85272c9f1adef11b2703a052e398fff4e6d39d5a756a4 4091)
(.stop 18 0xe13e701d4e5907cbc960d5d163fada35c227c936931de8b2931750014c235f4 5182))
(.fork 6 0x3782b411e0b2940074c7 53
(.stop 15 0x36936e1f70f7c937b89c0f7be5815c1de13d12844f142f50f9907 3916)
(.stop 15 0x38527efe2cbe3912fe581573bcbdd44366d9e8686234bf473f393 4383)))

private def tree156_26 : Tree :=
(.fork 0 0x0 77
(.stop 5 0x35f550f74c73679447 4251)
(.stop 22 0x2a078e475437af581797e5f9769349bde86862384d2c4db87972b71f190cd943b211ca55c7438 13511))

private def tree156_27 : Tree :=
(.fork 10 0x5b833c2088b1b2cb908e428586d61cdc0f 75
(.fork 20 0x16e00340f58bc933acd0138e512844f19076439d44ce4c7862310bbc2f2cc513d60f6d 43
(.fork 4 0x18e113b5d29f1c 41
(.stop 16 0xce019b6e151fc4d292368927397e8d9b8e02c392ed4c3572a5d31860 41)
(.stop 7 0x1b87cdf1f29d9f8d765ac7692 13963))
(.stop 16 0x8d9b36f6e2768b2a0355c4c35adfda316b1e155fc68b377ac8da3980 13950))
(.fork 0 0x0 62
(.fork 11 0x20a11c847a16e8bbe2f252674e6d39d5cdd73f 43
(.fork 7 0x638190c9eb2c411d75d29f1c 41
(.stop 14 0xe130a6ee3a5b7ace4d69de3980c31db0c443d952ed4c36052 817)
(.stop 10 0xdc513a8ce4d43dcb7daece3a07615a775e5 5008))
(.fork 0 0x0 67
(.stop 9 0x384d691b5403fd1b746dd74ab426d43d 3936)
(.stop 16 0x335f54029bb8e935db84b3678ff45a757d86dd33933b213a87ee771f 14103)))
(.fork 0 0x0 50
(.stop 10 0xd7bd43ddc7c3cc2a0355c08085a4360d30d 4251)
(.fork 7 0x29c11c059e447d13c7a075fa 72
(.stop 5 0x3393428109bd7d5749 2706)
tree156_26))))

private def tree156_28 : Tree :=
(.fork 0 0x0 72
(.stop 17 0x368c5d1f98079ff2f74e9e188d78cb1333e8ec869273933664f6a4211749 2847)
(.stop 2 0x61ef717 13511))

private def tree156_29 : Tree :=
(.fork 0 0x0 46
(.fork 8 0xf5880c3178feb401955e55e5d4b 44
(.fork 10 0xb00c603204702500b24447d6925abde81 43
(.fork 9 0x160058c8b327691b9511d72c5d29f1c 57
(.stop 17 0x38e655ef7142c4199fd011267dc45f29e3a077c202494d3da96a261c1f19 4385)
(.stop 22 0xd011fc6e3a4764e5fa8d9cb2572f5d1d86363f62c8da14d834e6db87e130cfa68d9a49706b393 4072))
(.fork 0 0x0 75
(.stop 31 0x3366af8b6777305f29e3a2195cb40896decdb8783eb676495447d1d91d58ce0c76f1df0a953628f6a5a89870ce2d27450a1445557157b 1876)
tree156_28))
(.fork 10 0x58c1662ca4d9938d53904ea1b6f6deb564 75
(.stop 29 0x1c15e155caddec41530559c24e3ade8ee149b897a435e542951c06b7f4236bb9f29da0078122d48c427b8f53448525a50a1445 13013)
(.stop 23 0x38e64c3785261e1a49d0d4baad01e974e601fb7e38db87dc3c80f20751324c0130366799ac6df74c7 8584)))
(.fork 17 0x1fd119494d2c392ed4c358606202052d584b293664e354e413a86deb566 75
(.fork 10 0x3945b81e048c42f2cf5349692745ca974c 30
(.stop 8 0xe399744e3801ee224e195e5f9f29 6582)
(.stop 19 0x36713cf77ba66b2403d2725d49c238e66209b89d2e96b16bb36874021128751371a 5962))
(.fork 0 0x0 62
(.stop 5 0x38e92ef8bc93111267 1908)
(.fork 0 0x0 63
(.stop 17 0x38e122f0f565f6de79d761fba86238e686575e22c90cf544c930066b1e84 5642)
(.stop 29 0x37276e1f7b3730736c9c338ea16535d8a35b97e4225124450138b509944757d2405d0e0e158656708e39829711c09405abf5fa 8281)))))

private def tree156_30 : Tree :=
(.fork 0 0x0 56
(.fork 8 0x350208279c9f83d697395cf59a5 44
(.fork 10 0xce06d41b809402c9111f44f16925abde81 72
(.stop 28 0x511f85538732da7ca3373927b97e5cab5e950dd69e5a8dfb8ce4c95c228894d2c38c59d284d8d3664ff540150a05cb5749 13632)
(.fork 13 0x3c0aa03491bc49fc2cc0c5850d94375a796a3779f8e6 55
(.stop 17 0x353f3f7f5d82e6340358535d77c5f85500dc6392a050065ce173e6901ada 2676)
tree156_12))
(.fork 0 0x0 34
(.fork 6 0x18e8cd833b8f4444c974a 55
tree156_13
tree156_14)
(.fork 0 0x0 54
tree156_15
tree156_19)))
(.fork 0 0x0 61
(.fork 11 0x3c0d246551b946f127f0c58319139c50d9437 75
(.fork 6 0xfb082922d48c42c88bcb 41
tree156_20
tree156_22)
(.fork 0 0x0 68
tree156_23
tree156_24))
(.fork 0 0x0 66
(.fork 9 0x1740d083480fa89562574d9344bd135 67
(.stop 27 0x38e6640b5df3addae1cbb0ba894df8e36dbdb7ada4cbbe3d80f653fed39dd7ec04205ec3dd19688c23178cf833e509b 5956)
tree156_25)
(.fork 0 0x0 54
tree156_27
tree156_29))))

private def tree156_31 : Tree :=
(.fork 10 0x1e209e727e0b1d2cc0e2438dcf5a3dad9a5 67
(.fork 10 0x11fc6451e1878e22f08c22570c5e4bf1307 53
(.fork 9 0x16a16c4bb533ad00844f14ca6dcdb76 42
(.stop 18 0xdca09d3cb3d8706429ad86b738ea5d2b55a778a83ee3988083ac52534e25b81 7182)
(.stop 3 0x37b77c8f5ec 5964))
(.fork 0 0x0 29
(.stop 24 0xd569de2e399f2bdc4d423da10ed0533b8e25f19b81d2e96a90edd3966b99e8e7f1a2cddc89a516e25fc4 6731)
(.stop 5 0x174cd7f4fed6e07719 13816)))
(.fork 0 0x0 53
(.stop 43 0x353d70377233fd349c94df49f52ed6166baf4ba5116220e12190a642dad86b734213198d8c3668e275f5d9a8cc0c94c2c69005470d1d6cc105b12ed4bc933acd01402112844f1b736dd9d44 2365)
(.fork 6 0x16809ee40191215117690 59
(.stop 13 0x1875e114ea641e9692a5dac7de399438cc1077e3198d9a 14120)
(.stop 23 0x1d47deb5f2bdca1875e14942ad7f4ff56e25e90e604f6d49d1a396919de2ce4ca952ef9267705f303 14099))))

private def tree156_32 : Tree :=
(.fork 5 0x17d19491384be9309 31
(.stop 20 0x55738eb4bbd616debceb947038e6229cd7f401912150a17ca5f85f19d762704d9de0f6 13317)
(.fork 0 0x0 43
(.stop 24 0x88cb5eb3d47677558b8e63b113a4dc4111f8b2f8e877d60fc92634043fad00644854285f297e1d76172c 13166)
(.stop 14 0xce057e1da413a4d2e111fe3a1df59263407927b6775f677b5 7190)))

private def tree156_33 : Tree :=
(.fork 6 0x3d44fed5f65f298da249c 65
(.stop 2 0xda30ce1 2234)
(.fork 0 0x0 62
(.fork 9 0x20a16e864b2a20bc9499d7375cfd875 55
(.stop 14 0xd9caaaae5f174c61837ae22bf8e657db68c3b4969d5a91b75 2689)
(.stop 2 0x22bf71b 13203))
(.stop 2 0x194b303 13056)))

private def tree156_34 : Tree :=
(.fork 0 0x0 30
(.stop 21 0x3410643372361ff2ee20609e938d4ecfce48d8566d5b89dc859b877cf69066d9df57ca5fc3 4084)
(.stop 19 0x37185a8339249c755761ff693168ca834e3986e6b7b7124e1957bda419b86bb3722 4536))

private def tree156_35 : Tree :=
(.fork 11 0x7772ed0c4f361508c47091d749752715a696a7 51
(.stop 9 0x35d661a355f44f1e7ada4113e4971742 5186)
(.stop 17 0x1614dc4489f7c878555ac5cb5da312745cb7852755df2b88cb4b3584f561 13958))

private def tree156_36 : Tree :=
(.fork 8 0x5cc819253cc563630d9a50e1606 63
(.stop 26 0x61bb8eb29cde84e606c7dd9c5e908b2f5e63378d7952f5f1fcdf94437eea054da409ee27e913247311cd4e6939e 13478)
(.stop 9 0x33786e25e907f1368d5f9daee708b693 341))

private def tree156_37 : Tree :=
(.fork 0 0x0 69
(.fork 6 0x85434b0f7c65227d0e31 47
(.fork 16 0x360d1c04bd930d55d72f9206c8a83394f51421d38e53117305d19b7c 24
(.stop 6 0xe3a2195d2b47687a422cb 6881)
(.stop 18 0xcb4a2c7dc42aacd025c17da41443d7ca22599a6a11e60618ad2b5b897c97852 473))
(.fork 0 0x0 48
(.stop 7 0x37287caf71b6def38f4c3d443 3780)
(.stop 2 0x5d335fd 13816)))
(.fork 8 0xf481b3160c644c053024e73564 36
(.stop 19 0x367266e36904019738dc6e23299b798141eb555510dae16db9b7bd7f51345d32225 3622)
(.fork 0 0x0 48
(.stop 34 0xd025fbcd295cb2cb54cd7cd95a4972c769044c14cc644e18de6052f64c3599f66ada3a778768d5d29cbd8fd75505a917385cfb728510dad36b85b7b 3459)
(.stop 2 0x44c35f8 13496))))

private def tree156_38 : Tree :=
(.fork 8 0x5bc81b2c88c58319139c55a956d 44
(.fork 11 0x3d420289db447d255557157b5a496af779dfb5 57
(.stop 12 0xcd9e7a5d9dda4979ff6904e836763b416045f5604f 9062)
(.stop 26 0xcdc1fc4e6057cecb251ade601e7fda419b888933875a860618da249cd9f942a6db9d49d0911d94bd9a45702f693 7824))
(.fork 0 0x0 39
(.stop 21 0x36779e977a85f5b2f52c1341350a1b7875328dbdc616a05a875fd44c19b872ff4b8510e2bc 3909)
(.stop 14 0xd9f942ad091b7892738e1007c7703b01df3da408a746b7728 3444)))

private def tree156_39 : Tree :=
(.fork 7 0x3db11f45b322e89f04bfb304 46
(.fork 2 0xce9428 42
(.stop 5 0x37185a8356403193aa 4708)
(.stop 8 0xdc42494da196065a835645abf693 4708))
(.stop 8 0xcbd4a7936176867a3b54d5a87566 2073))

private def tree156_40 : Tree :=
(.fork 0 0x0 54
(.fork 10 0x1e18b1b2cb8c513198f583db508e4285c0f 42
(.fork 11 0x3361b48b222ef925349c93894ea96905ac57c6 65
(.fork 10 0x85447d16cc64322e8a9235ecec855c5cb5 39
(.stop 8 0xe5fa368e601e8eda1815c1ddde86 2362)
(.stop 15 0x368624eb97e692769077ce366d2cd6a7e601d50ce2dcaa8d7b8e6 5964))
(.stop 30 0xd28649ccb35f19da4113c55734b877bf8e44c35562e398f4d44ed5f6debcd8a3b0113861c1a3e690730019488af27d0fe76937303 8748))
(.fork 0 0x0 57
(.fork 12 0x5ac47d2534a832a54d8a3670ec03b4187068f9a41 69
tree156_32
(.stop 3 0x36775f67303 6098))
(.fork 0 0x0 21
tree156_33
(.stop 28 0x7c974b166e36906209b89e3854c46db738f0f30802d53464b2a20bc9499f3005f4a366d9f820208188ba3ae4ed24c37685 13485))))
(.fork 0 0x0 72
(.fork 5 0x17d121c5ba16ec655 59
(.fork 9 0x77e206494f3158d8c3668e2738d1606 53
(.stop 22 0x7f1349c66e1aeccbb05a34ea1c147ec369336710a349c5a3c690f392340512844f11d666a1d44 13951)
tree156_34)
(.fork 7 0x3e211f45b322e89f02a2f303 52
tree156_35
(.stop 18 0xdeddcbfe13125a50ad44261a1878da151d658332fb44f944555e56136927392 2997)))
(.fork 0 0x0 62
(.fork 8 0x192c7811e38a882a54bbe2f25267 59
tree156_36
tree156_37)
(.fork 11 0x65222cc8c227a49fa33c0d013898e355cef39a 61
tree156_38
tree156_39))))

private def tree156_41 : Tree :=
(.fork 11 0x33192cb1833a4f6f497127250b5ad66b79f14 38
(.stop 10 0x6ddf4398d938e353117345f42a0fe385c1f 14560)
(.stop 20 0xcd92222e39a22dcb4973a61c1c0cd0e4e1b3d454c4752b7b35d0925f5f6f8e08d8f5e2 7044))

private def tree156_42 : Tree :=
(.fork 0 0x0 62
(.stop 24 0xcb91df07f138e98d9b8e061803342509de5da41880e11447a12086562ef8bc9363cd9750d543861ad875 7199)
(.fork 0 0x0 41
(.stop 9 0x173cd7e9c1fe384a8533d511c6201a4e 13800)
(.stop 34 0xd4e1fc4d2a49d977a72e877cf8e0813338572a9d45e116363e5f92ea889b8e66df75fb11f47771e101665579a366925de5d55cb2c3b212645a6b692 5022)))

private def tree156_43 : Tree :=
(.fork 7 0xb0d2c80ec84ea191b6ba6187 71
(.stop 15 0x1dddda2d11b46df8eb77cf69049bd908ce40cf43b08ece49c1a4f 14561)
(.fork 9 0x5b12cb8cf535e4d9044c939e7c7f4c8 51
(.stop 16 0xda41df3e3825c8d2c54d46bb38e66e135e66b8b8e349712726b59ade 2525)
(.stop 10 0xda49aece3989c6e381b6ccbd0d806e1384f 5176)))

private def tree156_44 : Tree :=
(.fork 16 0x2c98eb53fad6945ab5b6cda406db2c60b2b33a525c4e493a650b5876 47
(.stop 16 0xcb55ae9dc31c18e3ae363d78a22ed9f622de39999ed52cd80386d4c4 8595)
(.stop 7 0x35e288bb67d88b78e6889b420 7202))

private def tree156_45 : Tree :=
(.fork 0 0x0 69
(.stop 2 0xd310d90 2548)
(.fork 0 0x0 65
(.stop 27 0x371f83cb4078b0f70c6b438e12514c4c3875390558586861e355f1ddcc4f47091d74e4d3a55a9d7d05f6de79d310ec8 6250)
(.stop 15 0x35f1277755c755784579e74c44ea356449c9e83d7f4d97499f435 2063)))

private def tree156_46 : Tree :=
(.fork 0 0x0 72
(.stop 16 0xdc8d74766bf6904be5ae57555e8dd7a53a1cc040e003885ba1e25005 4701)
(.stop 17 0x174ada10e18da3973fd7ad3a3d7f495d31a0ed0424739327d4b2949b74cb 13503))

private def tree156_47 : Tree :=
(.fork 6 0x11c0e003882b816e8789 65
(.fork 7 0x21527c0a8b2a48bc12f18ec8 51
(.fork 12 0x2044b182cacc4e33a525c49c92f750b54405cd1742 44
(.stop 17 0x2707e155a50cb9c76972f78e3313d1d749c569a5a9f2fc44f16af5d25863 14411)
(.stop 23 0x32d4a36349c88a38e172f6230cb70c4f470925d79e5f14dc61a506e11e86d57d4426badc1f7c875ee 7974))
(.fork 0 0x0 52
(.stop 3 0x1749d7ec777 13813)
(.stop 13 0x37ae38b4e2ed5982970f3d3866e135f55d275fa4c2b2fc 4383)))
(.stop 37 0x34aa88bf7ae8feb54b817f720510d611ce30c4f5d1d91be13cc3b62035f43120eb43fa90a158516ae692b5fa44f11d64be530a55cb39305e895627c4b272caf300 8594))

private def tree156_48 : Tree :=
(.fork 0 0x0 71
(.fork 4 0x3843ee1958825 65
(.fork 8 0x5e448527c0b262cb0bc12f18ec8 51
(.stop 15 0x35da66d9b84da4113c5a4b5ee2c60b2b49c93924e994405cd1742 4719)
(.fork 0 0x0 54
(.stop 27 0x38e97a334a972f5df1863741f339d9b36e1e22edc7d91866d1aec88b78e67f0769044f16925abd7e36dff5fb49bd571 5804)
(.stop 4 0x44f338c38bb42d 13052)))
(.stop 23 0x35ef5d2d7e5e3a5df0d2bcce738754c653717cdce450a1497d26f532d4d7cbf4a912c9cb2b364f2ff 5027))
(.fork 0 0x0 68
(.fork 7 0x4403782b420889f327d4b29 74
(.stop 24 0x6e138e6532738e18ed6afdc9d74ada10fec5f81e7ed7f494d27a0e363b00ed042791c761c32ff0d28485 14108)
(.stop 30 0x4c375f16df340175372fc475d72c5d29918dc3d6af618d99966c755f510d5fb5d174301918cfa3868feb55795795cbd74761ef566 13049))
(.fork 19 0x3200cc64b2c60b2b3dbd25c49c942d5101f14d33c9f429f8c4f47091d74e974d0 65
(.fork 12 0x11f4299557b690121477727c0bc13b2169a5cd1742 38
(.stop 3 0x38e352ed4de 1897)
(.stop 12 0xd4e1d45d7807fc88c370c7561f2688a32e75abf5ee 4383))
(.stop 18 0xd7e1443e3992ea537b3786205cbe75638e06ddf30133a8d84449d13d476343b 4719))))

private def tree156_49 : Tree :=
(.fork 4 0x5ec6ee1bc48bf 59
(.fork 11 0x3e319206531e2c819209cd8c3668f5d3da1606 56
(.fork 13 0x16d05c03e01e2081620909e727e0f5a3dad12b44e59a5 51
(.stop 21 0x158d4f590b704b4396e2f6905d1d91be38dcbdd9f525c3130d6d64638e650b5ad66b79ca7 13038)
(.stop 10 0xdca1b72d7a666ae399fc1da415796bb368e 3750))
(.fork 0 0x0 52
(.fork 9 0x9f429f8c4f475d3934e95a3c690de79 51
tree156_41
tree156_42)
(.fork 0 0x0 40
tree156_43
(.stop 16 0xda40e39e385dddd7ec95a2cb925f49bd908ce406562094ec23b3b4c4 2840))))
(.fork 0 0x0 63
(.fork 11 0x2af0f803e716c45bb195cb242cb8cf533f1132 71
(.fork 4 0x3846562094c62 51
tree156_44
(.stop 3 0x36924e972fa 2860))
(.fork 0 0x0 66
(.stop 42 0xe3a459cd75aaaacb3222de1315f85851c18ce25b8492678485a6880f274907b46c524c7089df083ca226dc7d6a7da48212255895d2c9cb2b20489f4313d1d74e4d3a557fd7d0d310f64 2989)
tree156_45))
(.fork 0 0x0 56
(.fork 10 0x1e2081620909e727e0f5a3dad12b44e59a5 51
(.stop 14 0xdc811d8d0eca7ed9f478931a0ed0cc0464b27ccb2b4971440 3460)
tree156_46)
(.fork 0 0x0 72
tree156_47
tree156_48))))

private def tree156_50 : Tree :=
(.fork 0 0x0 51
(.fork 5 0x2993138ce949c9742 44
(.stop 14 0xdc45f21cb9dcbde3a44682ed0c4f475d69acbf113c5cb5749 2989)
(.fork 0 0x0 49
(.stop 11 0x37bd5aa38554bd9391d7b8bb4e3a142b5109868 5644)
(.stop 10 0x5a6b8e45081e87e1552f64e476855aa355f 13950)))
(.fork 0 0x0 45
(.fork 2 0xb1614 52
(.stop 2 0xd2ed1d7 3151)
(.stop 2 0x5833720 13052))
(.stop 27 0x3720815f3698b0f97f88bf2d9470f711a36767e51094bb6945f21e154ce84bd93915f775fb5d257e57561df288a35ef 5786)))

private def tree156_51 : Tree :=
(.fork 7 0x3e325589f127dcd9338b4e2e 52
(.stop 17 0x37ad755f84807cd1b14931cbcda31a50d7ec46822b0948585368d583569a 2996)
(.stop 6 0x58332fb22b36935abf38c 13964))

private def tree156_52 : Tree :=
(.fork 0 0x0 51
(.fork 9 0x811255cc4e33a525c49c92f75cd1742 50
(.stop 24 0xe151614dc66365cb69e8ecdd6366d9f9e8dda4113c5d2755f00c48ab33a0d8336692f64c353914e9d7dd 4228)
(.fork 0 0x0 38
(.fork 6 0x1da49e63f8d4426badf21 52
(.stop 10 0xd57ce275abf68c5833719585368d475d25d 1911)
(.stop 13 0x336b755e18dd07de8ed4fd1177a2768d33dd56355d3392 2205))
(.stop 19 0x368c29b784b9c1f84c88a397e497569a5a9f39250f960c79eb7295ab974a86374ba 2373)))
(.fork 0 0x0 59
(.stop 6 0xd55d271ce488273630d9a 3151)
(.stop 14 0xdc4969acbf10a044f1692d7d130d620191ad584b29510b566 4546)))

private def tree156_53 : Tree :=
(.fork 6 0x1089563174c5f38b4e2e 51
(.stop 11 0x38e644d11b27a2768d583738c49ad6afda316a8 1911)
(.fork 0 0x0 35
(.stop 4 0xda3560dcbc16af 2376)
(.stop 9 0x1b7fce3077744df4bf50f37276e1f693 14111)))

private def tree156_54 : Tree :=
(.fork 11 0x3db20449e233a525c49c956355d17345d0b430 50
(.fork 7 0x3222acd834bd930d583d7dd 39
(.stop 13 0x1d58cb89d53e391d44e38c89d297cf51d9f863466d9e86 13792)
(.stop 13 0x35e066c337d3d4737788a38e85839a4bda4113c6dff555 5652))
(.stop 25 0x111ae3997e0619b53a9e7b7191b75b8275438e4754df21d2e960ed088948445d1344ba13085851b877a2768d 13784))

private def tree156_55 : Tree :=
(.fork 11 0x7771e108bc2cb0c4f31911c2475d69a5a9de79 51
(.stop 28 0xcba5d58d541ad6889b8e69c2367127835e22c90b2e3ff9132d9fc8ac2558e2d57fd6a8ce703db192c81133a525c49c9742 5624)
(.fork 0 0x0 63
(.fork 7 0x5b11904b242cb8ffc44c97db 66
(.stop 14 0xce25914d5409e050f37b668f2228d9c495638b8f6157fd60d 5624)
(.stop 14 0x61af7bd889b8e636692644e6939ed591878e149a496df7557 14405))
(.fork 0 0x0 59
(.stop 27 0x38557c6b8e11dc47fe273100655e75576201df3e5fd692e39990d750f4335835a517f1367f3630d9a499126a68f1a43 2681)
(.fork 8 0x5a45a93fd100653314d672af4cf 66
(.stop 11 0x2228e5fdddfda257ddd7ecffb5abf72750f15ff 13807)
(.stop 17 0x37b92ed75ef61d7670777368c35edb7fdc5e057d571880dc9cb1b423b566 2825)))))

private def tree156_56 : Tree :=
(.fork 0 0x0 71
(.fork 13 0x410ab43e32558a91364ce2d38bb39c0d346561e28b26 32
(.fork 6 0x278143c5d21f2788a62c3 51
(.stop 21 0x2708e15622ee3a59aedeb2230e601de0dc85df1d08881122b0bb333a525c4e493a65a656a8 14412)
(.stop 33 0x3539a0fb8e88176708d286495e601decd7ecce2deb1f21e5f9e8ce3a561272f5df183cf4220a2db8788ba530972b71f2c6cb2e42394d755c72fa 2809))
(.fork 8 0x252d2eb50859b66ba9dec7a1b690 51
(.stop 12 0x5cbb71a61db2fc77839805f8db7fd78925c4e996a8 14098)
(.stop 15 0x2228dedd878d089132e391aec864f9805f217e36dff4bc72ef7ad 14100)))
(.fork 0 0x0 44
(.fork 13 0x1730f8c8a53630d9a499126a581b4cc2c90d94447d692 77
(.stop 9 0xf49e3989ec0a84d8764373982cc9447 14261)
(.stop 2 0x22cf67f 13212))
(.fork 31 0xd8c190c779361cd9e388908e50c143d5599571ce606e9621191fce70f60445d24d5851b877c8e057d300041036c3492308c5e364b4c4 39
(.fork 4 0x3d257285d39e86 50
(.stop 10 0x2f340b3d474a99c2354018d0fef42957dd 13340)
(.stop 5 0x3538974b8e477835fa 3925))
(.stop 24 0xcb2dde0e5fde7bd4e1cbd816618dd07205f974b8e89c2353a77ce3669c0b71b3d45089866649ca0e37bd 2190))))

private def tree156_57 : Tree :=
(.fork 12 0xd80371e209e72a08a943afcf5a3dad9a568fda40 61
(.fork 10 0x5bc2a316e4bbd3160c645a796a35ce173e 42
(.stop 5 0x35f744f16afd9e5f1d 2228)
(.stop 24 0xcb3df1bce0862dcb4e8d9e605fb6d9e1e80d085cbe83ef4b26dc35fd75135d8708e060e1562318b2f5e6 5469))
(.stop 27 0x398188c7372818384c7a037294235d59d005b707505d4777874b23b096065f517d761b9872cc0878a22c512a44eb304 5934))

private def tree156_58 : Tree :=
(.fork 0 0x0 52
(.stop 6 0x1e2b30419309f43190d00 13058)
(.fork 0 0x0 71
(.stop 35 0x32eb02ef54066df7be4e4367938298807565df3d2f14225a4972e72a9d467eda8dae39990d6dd1b75ce50d9a3b0960661cb302038447b16e478a252d13a 4103)
(.fork 0 0x0 44
(.stop 2 0xd330b24 2228)
(.stop 17 0x37297ca77193160d90d2f1880d7dd74b77a75f8082c47316c4a892cbb4c8 2517))))

private def tree156_59 : Tree :=
(.fork 9 0x9d52be8b0d35f54316e05f299272838 62
(.stop 10 0x86534017775de0ce053a7d05de8dd7ad73f 13181)
(.stop 19 0x1dddcb268d8e5f2366e3a605b863f2e27c8e2cba0fb8e8510f37d360dde179ef42c 13660))

private def tree156_60 : Tree :=
(.fork 0 0x0 57
(.stop 25 0x38e87c8f2e294c340177b339c4e9f5e85cfda4b6e0ddf3d501dedd285421510d9b6754b38149ca185d9dd9a6 7024)
(.stop 12 0xcb6d7dfd501d52ce05272da30b2a498126e6e0f4b1 6582))

private def tree156_61 : Tree :=
(.fork 0 0x0 69
(.stop 14 0xe39a496cb65c1cd2b5fc0d00524c5075c227a2b8ea4981b83 7660)
(.stop 6 0xd4f22c0e3a96a47ee7719 4095))

private def tree156_62 : Tree :=
(.fork 13 0x3711b06451e2095c279cd033d68f6b4bf130768fda40 71
(.stop 21 0x1de1e605d46d0b635ccdf60ecd0057d461ca2bdd52cd7ddc65a5177b772233d113a49c1a4f 14566)
(.fork 0 0x0 59
(.stop 23 0x349fa0fb36a8d8337d8d734019247722536188077cf36e55a156f582b43642711365f5186e61ca187 7494)
(.stop 6 0xd0d9308e5f1a34692f55a 2852)))

private def tree156_63 : Tree :=
(.fork 0 0x0 62
(.stop 5 0x3557192ccf43d80f65 991)
(.fork 0 0x0 68
(.stop 27 0x337072f35fd4bb78e9204dcb8754b55f5abdc227c9367757f960ed5980430abc5bf1de895b2f0cbc4420109c4c21c1d 5492)
(.stop 20 0xd005f15dca59b0e12130d6dc339238d112e61bb566011c2b8208c9e6428130c66d7398 6568)))

private def tree156_64 : Tree :=
(.fork 0 0x0 29
(.stop 13 0x338277b78e6777397c4bed745e3a943150f23fad56a0f8 3916)
(.stop 8 0x9c1b8e677b72eb22c513a50b3550 13643))

private def tree156_65 : Tree :=
(.fork 13 0x351de482227d8b1b367908e428543050f569c6dd1b75 50
(.fork 14 0x9ecd7d3d454316e074b12ca8d8336696985aa5ddc7785e7b 72
(.stop 10 0xd766702cb21d467775de0d7bd267cdf53a7 5009)
(.stop 15 0x32c8778397f078f84d116c889e3a4b09d4e973f77ce3669c0b5eb 7494))
(.stop 4 0xd2b4eb16e0768c 1901))

private def tree156_66 : Tree :=
(.fork 0 0x0 66
(.fork 11 0x420f8c65a25589f733e0cf93ac143150f1dec 48
(.stop 19 0x35d679eb5fb5d037216b85ded86578e646cb6718b2e701d540a8c2c54b2850a97cc 4700)
(.stop 19 0x342f5d1b5dd8b178e83b2913a49c97e5706f38c5a761959c238e646c9b877c8f4bc 5490))
(.fork 0 0x0 62
(.stop 34 0xd4ee05ed7f48a53cfdcc18d834a194c754d7ca62c5d061917692dd4dce20b282ca8e3149b9fc0d55c64b1958bbe2f24d783d80f65499d69d5a91b7c 5642)
(.fork 0 0x0 68
(.stop 33 0x397c75632e1865753a53635fd4e9f55f35f767e57f960e750b5662ca8d834c3560f5a616a977736930abc5bf209c95b2f0cbc43d312fb4c21f24 4223)
(.stop 10 0xdc8912e66a3566011c2b8208c957279b398 2073))))

private def tree156_67 : Tree :=
(.fork 0 0x0 56
(.stop 20 0xe605fc2d568d7d50c5b81dc656a96dc1de1e399deddc886451e2095c279cd033a98f5a 4877)
(.fork 0 0x0 68
(.stop 33 0x38e6901753b6946360d2c5c0cd599260756397c4e2d3ac57d2c7fd7e0cf835f4e3042816925abda34ce3077a256cbc32f110934c2160f8642668 7506)
(.fork 0 0x0 66
(.stop 16 0x8feb8e666db72219689560ee43c049838ea25749f733e524c50c543c 14113)
(.stop 30 0x55b5402c577214216708cb61fc3d2b87f077cde8dd7b9c2272f368c6dc3566011c2b816ec823255cf5b423d0a0508187f7ca3398 13192))))

private def tree156_68 : Tree :=
(.fork 0 0x0 66
(.stop 25 0x1a51dc89defd2f144366db8e69c1a83cd0bd6a464538ea01083e3196895625749f733e0cf9493143150f14cb 14105)
(.fork 0 0x0 54
(.fork 11 0x77920889f62c6cb2e3678ea442390a150f5de0 36
(.stop 10 0x4e9f5ef66adb70da31b81d2c526c6e1ddef 13371)
(.stop 2 0x9c13557 13645))
(.fork 0 0x0 62
(.stop 33 0x38e65a4b85272cb7b199b353b754e668e3a8d88448de928daac7fda4d56e582987a8ff754d9c13557192c6562ef8f603d951145a756a466ae2c0 8276)
(.fork 0 0x0 68
(.stop 35 0x36778d734a17ed353a863f5d9708a3fd925f54d9c1283ad599d46925b9814bd930d4e456985aa5de1d2e9fc3d7e05bf1de8827256cbc32f11308754e668 8282)
(.stop 11 0x20ecd598f4f58537220ae08234bdd4207f0f398 13655)))))

private def tree156_69 : Tree :=
(.fork 6 0xd246df22f08c24e593a2 40
(.fork 6 0x2284fe54e1d3a8646dcb7 54
(.fork 15 0x3500d83d01de482227d8b1b2cb8d9e42390a150c143d6dd1b75 29
(.stop 17 0x38e9973b49e9c0b54061cb42f55a5f29d9dd9a6da3076d2c556a966d5a51 4716)
(.fork 0 0x0 21
tree156_59
tree156_60))
(.fork 0 0x0 66
(.fork 14 0x1083e31968778255895d27dccf833e4f4a3d9143150f1d51 29
(.stop 17 0x35405f974aa708b8ea498126e6e0f432252c9e73ffd44366d9d52e39a3fa 9056)
tree156_61)
(.fork 0 0x0 56
tree156_62
tree156_63)))
(.fork 0 0x0 16
(.fork 4 0x4e4187088c27a3 56
(.fork 15 0x36191478825709e72e90d033d68f6b4bf13075f519a568fda40 44
(.stop 22 0xcb263f6d285de1e39969ddc660f8a35f97c24d0d713831880e3a86e035f513c5a49a34692e0e9 6088)
tree156_64)
(.fork 0 0x0 54
tree156_65
tree156_66))
(.fork 5 0x1d4479f25cca5d35d8 31
(.fork 1 0x1267 54
(.stop 25 0x20f6d9f9e8de5fd3a779ef68c3d6d08f428187fa36339c00d882227d8b1b2cb8d9e428543050f54d76dd1de0 13807)
tree156_67)
(.fork 1 0x3410 56
(.stop 26 0xcdf60fae60530d77878e69c1b55a35f54316e077196945deddc88036191478825709e7340cf5a4c1d6035f5df18 2529)
tree156_68))))

private def tree156_70 : Tree :=
(.fork 5 0x4791e208152a39394 48
(.stop 20 0xdef0f51da15e8a83eb36a24d337a646e190e121a42d2e99b6707b8e63d359b2da35745 3609)
(.stop 11 0x33687089e8a7c9367e83da190e13df2988af5ec 7822))

private def tree156_71 : Tree :=
(.fork 9 0x3e31de095627dcd9350c543c5595572 56
(.stop 15 0x3364af836795ce173e61d235ae3989e74e5cc3e49af8ea6695a40 9837)
(.stop 5 0x371c77b38e6426b5f4 5187))

private def tree156_72 : Tree :=
(.fork 0 0x0 72
(.stop 31 0x2222e5f9f29d28a22fcb3d87168f784c3dad7d76695a3f6901b73d7e88193668e34581986e61c99a8cc0c0470ae06552798b1a423d1d6 13801)
(.fork 0 0x0 71
(.fork 3 0x78a44a925e 56
(.stop 15 0x384c50aa22ecdaa66dd9e56a35ce1874cc0816d340cf5a3dada40 3470)
(.stop 2 0x3b5339c 13208))
(.stop 5 0x2a0d320d033b53439 13208)))

private def tree156_73 : Tree :=
(.fork 8 0xf7c64b2ef8d78499d69d5a92054 54
(.stop 16 0xdc31860defd1ae8fdb6725abf68c033816905b02a4475f4cc2cb9b75 39)
(.stop 24 0x729b4a6669b85555b72de44c80c005641f86e1f5e6580960ad330c644c0573ed5993a87ee771462035fd 13938))

private def tree156_74 : Tree :=
(.fork 0 0x0 59
(.fork 13 0xd3081c20b0f8c5a32064ba73630d9a581986e61ca222 77
(.fork 8 0x864a852cc8ced3620d9e5acd74e 44
(.stop 12 0xdee876dd2d875d30f754068f3398499f55727b1447 3771)
(.stop 9 0x34a61d74c3dd5011d7d2d16a481535fa 3006))
(.fork 0 0x0 69
(.stop 9 0x349e7edb6932c6d08ed799002498126e 5962)
(.stop 23 0x1875d9c22bcd9c9d4dcb3e537cda9fb6da4cb1b42397376421b75703f5e62ef8d785a756a48153439 13512)))
(.fork 0 0x0 77
(.fork 6 0x86464f2c7cd8836796b3 52
(.stop 12 0x4bb76795a9371c4e4356631916afdc9cebb3dbd1d7 13665)
(.stop 2 0x2c934cc 13508))
(.fork 0 0x0 66
(.stop 2 0xd0bcfff 2390)
(.fork 0 0x0 62
tree156_73
(.stop 5 0x34c436434cc27d3435 2852)))))

private def tree156_75 : Tree :=
(.fork 18 0x11ec0361b508c03830f5a3dad9a568fda40ce70656256cf5c44a913a5d21f27 51
(.stop 19 0x397e77c74ba69172d08b2f36a88bb84c36617385cfb72933a525c4e493a67509d46 7512)
(.stop 3 0x33025f53679 5944))

private def tree156_76 : Tree :=
(.fork 0 0x0 68
(.fork 8 0xabc77a208882729f0b294c21574 69
(.fork 4 0xf7c788498126e 35
(.stop 15 0x353c83db84f7ca622bd2e8f42e398f4d5cb174ada341553d7d6af 1878)
(.stop 5 0x1f29d2e88b35d2b693 13957))
(.fork 5 0x3d816b09345d17430 56
(.stop 4 0xd9e56afd7c4f6b 3930)
(.stop 11 0x35e58657854754f4ba7ca76855abf5555d2b68d 5342)))
(.fork 0 0x0 69
(.fork 28 0x11935fd081846e2c5cd834bd9562702dc13778742f191c77022cce263d090925ced90cce703df1e209f43fe126049b9610 35
(.stop 6 0x92634101d9889c35d1c22 13162)
(.stop 10 0xdef1876cdaa1959c2398133a525c6de370f 2825))
(.fork 0 0x0 63
(.stop 38 0xd7f4c45dc65085cb38ba3d7c5a51dc4a8d9cb25cabd76187672b1d42d9e4f5a6695a3f690339c38d53904ea199e79f355a082c4732c90b2e44c91cc4925268580a3f7 7805)
(.fork 18 0xf6003608286382c6d0a15cddb74703f433192c8a82ef91ae499d69d9247439 36
(.stop 17 0x38e64c0b6724e4368c66af49f750f4c818e4cd7cded435d7ada51e12db87 3594)
(.stop 17 0x32c87771e7bd9fd60670535eb7f12537e3a4e1d68e5e7cd9f97d25f67557 6714)))))

private def tree156_77 : Tree :=
(.fork 0 0x0 53
(.fork 11 0x35033c0d116c4bb52f2512844f1c0e7041d44 68
(.fork 9 0x2b41de882722b88bd256cb294c2143e 66
(.fork 6 0x1de0956364d43c5595572 48
(.stop 8 0xcb91e8ed9e1b7be3989e7da35745 3935)
(.stop 14 0xd9e2401cb25a3f6901c0d704768d5835cab7779ddf79e7382 5631))
(.fork 0 0x0 69
tree156_70
(.stop 3 0x35555d17430 5187)))
(.fork 0 0x0 69
(.stop 16 0xce70956e399f25e12142a510d6abd3200e108644791e20815208c9f4 3622)
(.fork 0 0x0 66
tree156_71
tree156_72)))
(.fork 0 0x0 39
(.fork 7 0x46b24ec94b279d421510d9b6 72
(.fork 11 0x2b816e85bb208c9e627dccf3423d0a04e193a7 68
(.stop 26 0x817b2d8645b722470925d53274ac72f1f24da4d74a72f74ba49c92f74c31574d598822209c8c12ca51374c21cb8 13965)
(.stop 36 0xce01e8dd9de0ebdeb1077750e187cb2a8d8cb3e537cda987069075fa081cba70a848a02a00b1b42390a144ed9086435b746dd5c0fdc4960661b9872888b42c 3622))
(.fork 0 0x0 68
(.stop 20 0x18d738c583768d5abf693255895d3174d933fff5f80ad077a20888272ca4e2b44dd308 13042)
tree156_74))
(.fork 7 0xd713620ec050f188077cf690 72
(.fork 8 0x11c5ba16ec655208c9e64281e8d 59
(.stop 9 0x37b469035fb081c819209cd9a389ce34 3930)
(.stop 7 0x37213fd5005d57130855d3303 2082))
(.fork 0 0x0 71
tree156_75
tree156_76))))

private def tree156_78 : Tree :=
(.fork 9 0x4701202b816e85bb1954ce84e453a7 67
(.stop 6 0x2a03561255c95c2ca8c5e 13660)
(.fork 0 0x0 69
(.stop 13 0x37104e513a46b71d44da40ec03dab3001e2082627d0a8e 4412)
(.fork 13 0xca07f820255e5613619769022f48c129f0b2957f7303 44
(.stop 7 0x1f29e604ff540172ff2061692 14097)
(.stop 7 0xb9ae605f29dc44ff5401755f 14265))))

private def tree156_79 : Tree :=
(.fork 0 0x0 51
(.stop 8 0x5a4b55544df67d192c9e233a525c 13942)
(.fork 5 0x3d319191d261c3430 56
(.stop 12 0x4c1f69050fb55544b768e0d106e0279cf5a3dad26d 13815)
(.stop 27 0x1cb2d9d9fbfd2ae8d4e5f1c168d9b677925f84a66d9f2988af5ec49b16985aa77273160f5f3d9939c581160868eb566 14268)))

private def tree156_80 : Tree :=
(.fork 0 0x0 35
(.stop 12 0xaf8353c88c798129a2975e3adf1fd088d8b5d2e226 14560)
(.stop 16 0xdc3ea0fe3ae2c7e602230d2b623194cf53c75274223643721537b5f1 7032))

private def tree156_81 : Tree :=
(.fork 0 0x0 48
(.fork 10 0xc00ca03308a93adced050a944368e1a47 74
(.fork 7 0x3eb1b987802a24a943d49273 29
(.stop 4 0xd089f1fe3825c8 7187)
(.fork 0 0x0 31
(.stop 6 0xd089f1fe382be0d4f1df4 7497)
tree156_80))
(.fork 0 0x0 69
(.stop 13 0x38eb61d9b78e115c13ce70788473124949a36902ca96ab 1904)
(.stop 4 0x5aa769049a355a 13653)))
(.fork 0 0x0 47
(.fork 3 0x9433dad4c4 74
(.stop 8 0xd9d9866d31064c1b98fec50a5444 2858)
(.fork 0 0x0 62
(.stop 14 0x5d135645d1b5f23d834c461adf1fe11403d192cbbe4731b6d 13496)
(.stop 33 0x340358237ab8fdf6907eeb40741ef71f643da3a7c77845494d27277a75f2585187c70638e147091d75f6de79d310b2a3394d9036595755d1b435 8283)))
(.stop 17 0x1268e114a94474dd41d3109f42c5cd90365b69211b8bbe3b2925349cb5fd 13968)))

private def tree156_82 : Tree :=
(.fork 8 0xd243eb22f08c22784b2a31796a9 77
(.stop 29 0x35d8817e5d2e3925ccd2c4f51496338d511f68e510d6b3d7bcf6049b18847c8f557361ce2238e508e4287566194100a42290a5 7357)
(.stop 9 0x173fd7c4f6b4c1f55c192cbc93d8343b 13803))

private def tree156_83 : Tree :=
(.fork 0 0x0 56
(.stop 5 0x33040a8c64bd32cf6b 1928)
(.stop 5 0x64bcc109f431934d0 13519))

private def tree156_84 : Tree :=
(.fork 0 0x0 71
(.fork 8 0x3846561e289f23134c6250b1441 61
(.fork 7 0x5af16e4c583190d984e71a45 44
(.stop 15 0x38e4925f9807c9f7275d2b684386339c0ce09ec447d6af5f217e3 186)
(.stop 11 0x3549755b72702e8f5a3fdb68e11996125d2b692 6586))
(.fork 9 0x17c0ad08222560a7c2ca55fd583f302 56
(.stop 28 0xd00141cd52e3ffcdb5731e3a1563da01ae7e605085585172e645b7113ad4feb5a516ad6195fb3da4016a1b809e73d69261 5472)
(.stop 35 0x35daa83f53b816a366e3a5e899c2398150876903fae05f9c1b8e4645b7aa35cd43e584974a72f767d4971272558dc0cda38ed03fd90044749ca672b72ff 3123)))
(.fork 0 0x0 68
(.fork 8 0xabc2b42088a7c2a38b2957f560f 74
(.fork 7 0x3eb1b9878d3878e36496d273 58
(.stop 35 0x32e529c36762ec32e17a3f37792732cb57e16147c6b37f75625cdd50513c68f5a426dd9d44d7c4f6b498526d61bdd47dc3cd8b366ce2644b5137702dc13 4224)
(.stop 20 0xdc4488ee605e89e38c89c30fb5f15d15e7dd7f5272729f39305a8f5a3dad26149b72ff 5652))
(.fork 0 0x0 48
(.stop 7 0x355550fb6900328bc4510d745 4412)
tree156_79))
(.fork 0 0x0 63
(.fork 6 0x16c47752c90b2e44c9911 77
(.stop 9 0x355550e7692086421d22e08c640290a5 2847)
tree156_81)
(.fork 0 0x0 67
tree156_82
tree156_83))))

private def tree156_85 : Tree :=
(.fork 8 0x11c0480ae05ba16ec65540156ae 57
(.stop 7 0x957d5846e1230494d2574f6a 13059)
(.fork 0 0x0 58
(.fork 6 0x1dc081820988b338d4ecf 39
(.stop 7 0x1a51d7b9c22da4d1d6d0b1137 13965)
(.stop 9 0x16a8dc8112d5835a517f13686692b55f 13812))
(.stop 23 0x35ee5f874226bb37105abdc2281636934759d44cbf160d66d5a517f1368627c4c5d33e4d93692b2fe 341)))

private def tree156_86 : Tree :=
(.fork 5 0x2af0ad09582ca5916 61
(.stop 15 0x35da754b854317b7145821870cbe047116bc9413160d983d99d4c 6582)
(.stop 19 0x353e646f4ac6bb1c20da3833329c5cb8e151919ce386462534ed03fd900461c32fe 4691))

private def tree156_87 : Tree :=
(.fork 0 0x0 74
(.stop 43 0x222acdbe537e5fd7df94c730270627a3da0187ee38a2c9e13530e5f19919defcbb53a8cebc42350a244a113c75132fa3611aec7f178e63660eb73b4138f4ea542a510d56055df39444f555d 13003)
(.stop 35 0x32cd926b369446742061ea531e1518706ddf8e25d299ba72f5df1d52d74466699b08fef6903af19b47571df7864f8e64c2f39825452f14c4538c4eb339c 9062))

private def tree156_88 : Tree :=
(.fork 0 0x0 61
(.stop 12 0xe129f1ada10ffadc50c584c099b6d7b0f665811608 4397)
(.stop 13 0x37ac7c6a8dae398a717f1754877d37140fac9e844f7566 6732))

private def tree156_89 : Tree :=
(.fork 10 0xd1063a19146e01e209e73d68f6b498526d 48
(.stop 18 0xda01df3d524c36e60574b7c935f10a6c8b33ac91d7d9e138f4ea75555d15e7d 5492)
(.fork 0 0x0 53
(.stop 9 0x354168f5a42da1d2726b9f5ec44a142f 4397)
(.stop 18 0xd9e11d7d526060e3a4fe64bb5880d7f574b3a99f1aa0fb8e66e2355a3d7f7b9 8132)))

private def tree156_90 : Tree :=
(.fork 0 0x0 43
(.stop 41 0x33729e8f2c8702354962039815a49999779f53c3fad579619587bd2e82960a6c7802f1142a510d7315d175ec7ca679eda14f5f3d9939c7531e82cbf88b33ac8ecb475d72c5d29a4c 3608)
(.stop 10 0xcbe513dd0c0e31cbf894133a512d5d17686 3017))

private def tree156_91 : Tree :=
(.fork 5 0x3d91914788279cf5a 66
(.stop 10 0xe399301da00ce950e63fad540c483d85397 2524)
(.stop 4 0x277769049a355a 13653))

private def tree156_92 : Tree :=
(.fork 0 0x0 62
(.fork 9 0x3d192c8c62770bbe38c51cc4735cb2 66
(.stop 16 0x475f67125377b666bf69066c35506679f1a8fea83ee398fff68d5a4a 13049)
(.stop 5 0x35f266db8e6667b564 5187))
(.fork 0 0x0 77
(.fork 6 0x86481d22e09514bc5311 66
(.stop 11 0x384594df6767c6b68b1904c4f3dbf4c03d91a35 8756)
(.stop 4 0x5acf4c03dbf566 13663))
(.stop 22 0xcbe9272d2e9a4ad7606475379746d0a5880da40b283b414435a5b4c027d0d90365986461f3432 4712)))

private def tree156_93 : Tree :=
(.fork 0 0x0 56
(.stop 18 0xd9e11d7dc81692a0fb8e65aa1a4acc107880a8c3330ce464b33a525cd32cf6b 3951)
(.stop 16 0xe399b72d9fd5ff5aa343b192cce93dbf4cf27d0c6444f51c2475f4d0 819))

private def tree156_94 : Tree :=
(.fork 0 0x0 71
(.fork 6 0x3846561e28f4f5cb9748 56
(.stop 21 0x368444c956855bf53b5ab5fb3da4034911c45af16e4d8e366169e5a8f8e6279d090427d9a5 2225)
(.fork 0 0x0 66
(.stop 19 0x39805f217e3d2f130be3996a8dc70f6470632fd0ab495d2a30a913120c5d33e4d93 4843)
(.fork 0 0x0 68
tree156_86
tree156_87)))
(.fork 0 0x0 68
(.fork 7 0x2af0ad0b293174d7e63fd916 57
(.fork 9 0x33919186e12534ec03b411c761c1fb4 56
(.stop 22 0xcb39adc6dcdb76d7dcd8b55775557f12537d9d9f1ada4834418e86e0279cf6b49b590a642d9a5 6102)
tree156_88)
(.fork 0 0x0 56
tree156_89
tree156_90))
(.fork 0 0x0 63
(.fork 6 0x16c4a772a24b2444c9c18 56
tree156_91
tree156_92)
(.fork 0 0x0 67
(.stop 17 0xed0d7c89614c0b561192cbbe2f24e313d973980fac64522f08c23178cf9 13366)
tree156_93))))

private def tree156_95 : Tree :=
(.fork 0 0x0 65
(.fork 6 0x85447d12149f027e0ec8 72
(.fork 8 0x11c2b80f885ba16ec6552a2ca92 46
(.fork 13 0x77e2c4cc5e33e8f503fad006557957957e561368d9a49 39
(.stop 26 0xcb32057dc61734d7e9749e5f9085865784b9c1f84c5109868da151d65801d44cbf07773d253864e9d4216941e86 5163)
tree156_50)
(.fork 0 0x0 66
tree156_51
tree156_52))
(.fork 0 0x0 68
(.fork 9 0x17605e42af0ad0822209cb2933dccfa 66
tree156_53
tree156_54)
(.fork 0 0x0 52
tree156_55
tree156_56)))
(.fork 0 0x0 55
(.fork 4 0x2a04ff44019ada 74
(.fork 9 0x4808743eb12187872c70b2f3d64f6c 56
tree156_57
tree156_58)
(.fork 0 0x0 67
tree156_69
tree156_77))
(.fork 0 0x0 50
(.fork 5 0x956360cd9a4bd930d 72
tree156_78
tree156_84)
(.fork 6 0x206508542855f85853565 72
tree156_85
tree156_94))))

private def tree156_96 : Tree :=
(.fork 9 0x4a03902b50adc7872c70b2f3d64f6c 63
(.fork 9 0x20b1e0878f254c9602a24a94580960a 54
(.fork 11 0x3516c864e2f28cec3408ed33fcd69c6dd1c0f 37
(.stop 8 0xd7acbabdc9d883e39ceb8dc5174d 5810)
(.stop 16 0x813767188cf7177c7f7272eaf5eb5385cb3def46d231156175d2f553 13635))
(.fork 7 0x3f14388c53ff509755c3394 53
(.stop 19 0x354361db36a94eb8e6585f5ec7a3e1988b3397c3d2168c5ac9fbbda217407039c10 3141)
(.stop 6 0x5acb68883f771977a75f8 13815)))
(.fork 0 0x0 57
(.stop 38 0xd2822318da78e67c772cc79f9f18d7dc02900a88085091617d7c85181db990b6695a3fce50d93556d691d5640d1034c9e827e4b1e2cc4cef3408e2538d987066919a6 3441)
(.fork 0 0x0 53
(.stop 27 0x38e68da797f585d72b18e72e15d2f55d27bcffd55c169b5a9b39400d40cf1e14c503194d863674f573db908d7039c10 6260)
(.stop 23 0x2be3e399cb5ce098836951b88ded0ce1535b3052a1cd9349513abd58c46b27bd00744fd3105113567 14251))))

private def tree156_97 : Tree :=
(.fork 0 0x0 72
(.stop 15 0x384f8b3b70e8fdb7261e04ff2d9ce973e12065522f49e62cb4c59 9995)
(.fork 6 0x1dd09d34c217e866e75ec 63
(.stop 6 0x8aff6815ac974cdc9960a 13939)
(.stop 18 0xd9f9c16e154d77e399e91cdd59b86951c25defdfc7818771e927f7ae5d33436 5798)))

private def tree156_98 : Tree :=
(.fork 8 0xf3c3d6141450e22d91bc47693ab 72
(.stop 11 0x38525cd9740da30b265831a49d3388234281613 1757)
(.stop 27 0x34a88d932dd8b3b70e7ecb54e5d2341e49678e666d372644a925e49c16adda34d9649813945f874ce33e92fb4c23396 6577))

private def tree156_99 : Tree :=
(.fork 12 0xac851014646441e3cbae2f092fd50c543c666d9af 33
(.fork 7 0x6d51d90cd7383538066e5b8a 24
(.stop 12 0xcb42228dec5cb6e390a6b7033717706f8e96451f2c 7349)
(.stop 18 0xdc9cb00cd9a233cb45cb6e1496a8e398fff445169dd7a113f4bcde7e7ecb97c 969))
(.stop 17 0x3412706f717a37397f201cc4472db8525aa355425089ed3ffd6a4705f559 660))

private def tree156_100 : Tree :=
(.fork 0 0x0 62
(.stop 4 0xda04a955a756a4 2541)
(.stop 27 0x32d272cf85252f9d46cda1ae4d0d4c6253394d4580960a6411b7dd5646d51b85275509dfb4da20ed23d5112544ff396 7039))

private def tree156_101 : Tree :=
(.fork 12 0xa9c3e916cc64e207c82a2c4cb2633e8ec85331a49 63
(.stop 13 0x367166bb55357d5de1aab78e58b0f8e72774ffc3ff9602 4851)
(.stop 31 0x370f88cf54499c397f7a1b8e344ff5ee77db8e75acb84518e47712268cd74e859b988a384738b943c619d879d0ccc6049659137c5f563 2979))

private def tree156_102 : Tree :=
(.fork 4 0x1d90cd766e7847 68
(.stop 30 0xcb29d427519de0e39e49fcdadb75def11d9da35745619f4ac5f9d883816367e70922cde38e06288cf54e317cce43fe586561ee05a 7028)
(.stop 8 0xd54d743d7b94455acb4c149d7563 4415))

private def tree156_103 : Tree :=
(.fork 0 0x0 69
(.fork 10 0xf985b720548232f08d96498126e5f297e1 68
(.stop 7 0x3725498768d1de895b2a39308 3465)
(.stop 12 0xd2b5e91e3991d3cc00bcb3b48fedd9e925949d7563 7204))
(.fork 0 0x0 66
(.fork 10 0xac85b4191078f27dcbae50c543c666d9af 62
(.stop 18 0xda4dc1bdc5ccd766e75dd7ee77270a643d1201d445d3049ed27ecffb3ffdc17 6571)
(.fork 0 0x0 42
(.stop 4 0xd58c3d1d305446 1914)
tree156_102))
(.stop 48 0xd774cd7cb29fb2e3a5e91d9f9602cb51080556371f66af6713af53954e8db746dd5c0fd7c89420a643d131102180d1077a256cfe640052fb4c2186561edb82d9e944552f968f5acb4c527b49fb5a756a4705f4cd 1588)))

private def tree156_104 : Tree :=
(.fork 8 0xf00d80f9881c27b49fb4e6d69d 49
(.stop 14 0xe399d46d78cfff6e2b8e444d54315f7b30733f4d9946fde7c 5800)
(.stop 2 0x44d74c5 13505))

private def tree156_105 : Tree :=
(.fork 0 0x0 66
(.stop 10 0xd589617d7ec5b416f90a449d756327dcd93 1131)
(.fork 0 0x0 69
(.stop 43 0x397f006b40177bf67f8b0b3646dd1c0fd2e9b8a7f038515841c14e5f46323340eba44a91c65349df6dc39fb2d58900255ad60661b9872729367349652757025c157c5f563208cf67498126e 6120)
(.fork 0 0x0 61
(.stop 5 0xd98d58c6552314a87 13063)
(.stop 21 0x1fbbcb4186e643743838cd12272c35672798cdcd7d00360cf0cec3b4d86d61cdb746dd74d1 13063))))

private def tree156_106 : Tree :=
(.fork 10 0xd88a022bccec3408ebd3b4db746dd5c0f 68
(.stop 33 0x397c224f3726e2b53b691b67e5a978e93b495fd77736715ca5c1dd2b0d785cdf54e03040c30f4476c201cd913f994e15a3d6b26e0b5eb4e8dcb8 4224)
(.fork 0 0x0 62
(.fork 4 0x20709ed35e169d 41
(.stop 10 0xe12d74dce00ebe3b48f5855ef6735a3d6b2 2055)
(.stop 9 0x1e7bdc38806337b7142edd133620f5eb 13939))
(.stop 5 0xed2dc39602582b562 13365)))

private def tree156_107 : Tree :=
(.fork 10 0xf444fe141c81c42210a449652757c5f5f8 69
(.stop 22 0xe149917def1de2d2b524e83ba22694cb9817a2b5f15d176733b48f54449556255d5de1d2f926e 4374)
(.stop 15 0x156fd54c025d9cced23d5370e580b5625d15c2577db5f11dcf4d1 13365))

private def tree156_108 : Tree :=
(.fork 7 0x46b24ec94b2eed5f2585d7e8 72
(.fork 10 0x86021c0fa482327989f733cd08f42813a7 62
(.stop 3 0x367a5a756a4 2541)
(.stop 25 0x397e94eb36b6695adbd7e9b7ed9e16028b3b70e3608fee46fd42bd334d023af4ed344a513b6dd1b75703f4ca 3465))
(.fork 0 0x0 66
(.fork 11 0x5b416f86441e3cd933b1cfe43ffd43150f1dec 68
(.fork 5 0x6511964b293175cb8 22
(.stop 25 0x336b6dd77b3335f84794e78e75d15867cbc17e7620f6933b491267f1a2cde38df22d30573e6e0a06288ce703 9375)
(.stop 28 0xcdade87e39dde0dea2aace38d8797c5f97c4932b48cd90f5457f768d07c4a6f446124e5d35deed538327335d380816b850 4697))
(.stop 15 0x397c5ccf43253338e93835380d5645102a0cb1e33bd2fd669b562 3924))
(.fork 0 0x0 65
(.fork 10 0x16a45b31938659207c82a3b20f6353314d6 38
(.stop 2 0xd588ffe 2846)
(.stop 26 0x11d767192534a0779e8dce5f1e8a927e8d5d781a40dc71f17b6d367349834c218fca8733751304e717385cfb68f 13042))
(.fork 0 0x0 54
tree156_106
tree156_107))))

private def tree156_109 : Tree :=
(.fork 0 0x0 61
(.stop 4 0xd0ecb2244c1268 1621)
(.stop 5 0x37197c87729535b4ca 2517))

private def tree156_110 : Tree :=
(.fork 6 0x33b0d7150f1a547097690 62
(.fork 9 0x3e6207082a22a09ed27ed1cc5a756a4 72
(.stop 7 0x34c52ca768808706552798c59 2241)
(.fork 0 0x0 71
(.fork 7 0x51e256ccf433f512a44e9f27 61
(.stop 27 0x398109e34a144538e4e3a1083d04028bcb6d433d51900455a5604669b42d4e996b26e16189d9cd1134c0939c5ce173e 160)
(.stop 19 0x38e651078e41fc249fe6062c28d778e966e5b8a7a3367c66919a6d3156b26e1768f 5488))
(.fork 8 0x13dc500201cc4452f968f5acb5f7 75
(.stop 19 0x249fd9e1424d0915746e0a0f5d552490e3990744b92184888397c68fda40def174c 13627)
(.stop 3 0x343055d3673 1617))))
(.fork 0 0x0 50
(.fork 10 0xa745001e08a6a29f0ed23d5112544fdde1 72
(.stop 28 0xd27dde3d3457ddcdbdcaf7c5f54a9002670d9d5b8a7f0f71a58198726de768f5d35b86dc84655208c9e633a108f4e457e4 4260)
(.fork 0 0x0 57
(.stop 23 0x1b8ae3a09cf35add48d4f1558cbb113a5105f27d7ddf17813e2bfd9cda45da200d30f4c3da2c793a0 13657)
(.stop 14 0xd295b79d9cd26e55d5a4dd0cd13ad58803042912597c5f567 1597)))
(.fork 0 0x0 42
(.fork 8 0xa405921de89ea44e942451195f5 69
(.stop 34 0xe130583cb2a83ad4f2d19e5f56a3973b97c226525994ea970d9ce3f7d9e00371b5077b2020bb838919a568fda40ce5882333d926049b9610693605b 10453)
tree156_109)
(.stop 30 0x42438e694eb2ca6409e7d7c5f4242ee0e0c69035fb4c4199c7ecb5620fa45a916cc659207cfe33ff91304e81f218b0f4c649bb4be 13363))))

private def tree156_111 : Tree :=
(.fork 0 0x0 53
(.fork 11 0x35033c0d11e14d863674f573db9c0e7041d44 62
(.fork 11 0x3e61430515207082a27b49fb5a756a45f457da 42
(.fork 6 0x190876d1de91d6585de83 75
(.stop 18 0xd9c6670e5f1fb0e5f54455d338481fe8fd97a45f2be398b222edcbcb4ea96b1 7656)
(.stop 10 0xda456b2e114fd9e39803d254cc454737307 40))
(.fork 0 0x0 60
(.stop 28 0xd290d78694397f5f1f68d8d66491aaa797d50d9b86dc3a3f6dc94d99cc1c0d80f584802580b212f2d39d53457d35f6190e 5929)
tree156_97))
(.fork 0 0x0 42
(.stop 48 0x695371f0f25fc0dc54d6be3a1f17cb20fd92c05cb07ecb7bc58338e694eb84824e4c30e13d73e88cf67f3d9d26e4e935fb254096029d0b212f2d4d15f4d7d8641dfb7ce586421db477a27a913a475944657d5617 14108)
(.fork 0 0x0 46
tree156_98
(.stop 38 0xda2a665e1160fde120cddcb3d55bdc3ca6f41f5fbcd57446b252cbbb7a1b5fb25417d3643a223ce583e916a45b31964ec83d88fe33ff96007c874c649b96b2620f4be 4837))))
(.fork 0 0x0 46
(.fork 8 0x141450e22d91bc476938d4eae04d 57
(.fork 10 0xdc0d31944b1e2cc4cef3408f6a66919a6 66
tree156_99
tree156_100)
(.fork 0 0x0 65
tree156_101
tree156_103))
(.fork 0 0x0 60
(.fork 11 0x2a20a9c48025409602c84b312f2d4d15f4d7d8 62
tree156_104
tree156_105)
(.fork 0 0x0 39
tree156_108
tree156_110))))

private def tree156_112 : Tree :=
(.fork 6 0x3154cdb33c4f4783c32e7 44
(.stop 6 0x79e76713d3973ae39df1b 13206)
(.stop 2 0x4e6384f 14269))

private def tree156_113 : Tree :=
(.fork 16 0xce864c2e699026dca2268d7aa12e3987773880ff15a697d05f6de79 33
(.stop 9 0x2233d9c5f26927f8e78b0f7273626228 14111)
(.stop 6 0xe5f1740e3a54466b9397e 5159))

private def tree156_114 : Tree :=
(.fork 0 0x0 45
(.fork 6 0x2eb4bc149592755119ae4 32
(.stop 2 0xe39e2c3 2046)
(.fork 0 0x0 56
(.stop 15 0x36834b96665d9c60f0d54d7d6927f8e779ff8e3367543250edfb3 5947)
(.stop 7 0x32fa5d0371483c355333bf727 5172)))
(.stop 10 0x46c77278b0f8e77c9b39422a4d894c17691 14565))

private def tree156_115 : Tree :=
(.fork 4 0x318d7b50916b1 31
(.stop 2 0xe39a35e 7360)
(.stop 16 0xcdd2062d755de3e3a0932d7594d5753f84fa5db8e67cae19888cb4b3 1574))

private def tree156_116 : Tree :=
(.fork 7 0x9cc29e507542457e177da494 59
(.stop 28 0xe3997d5d565913e3ad4c2d9d5ae3d9de977cda169a68f1b726ddf8460d0477122949ea2eecbcc472526449a96065ce973c 6263)
(.fork 0 0x0 75
(.fork 7 0x4a22e8a8336711215115b89 33
(.stop 7 0x384f50cf4b38d7a976e399c24 3143)
(.fork 0 0x0 42
tree156_115
(.stop 7 0x384f50ce35ea5db8e67caf7bf 3143)))
(.fork 0 0x0 66
(.stop 23 0x1733e5f1de3d755ae3e3a5e86d2dc0b907c476438353054e019b9e11c78538b4e2e4bf560d666d9af 14253)
(.fork 0 0x0 33
(.stop 4 0x1ddf68f02e46d5 13495)
(.stop 16 0xe118f6ee39a53ad9ddde3dc9d43b730235ed2dc58f35edae388cf67c 5786)))))

private def tree156_117 : Tree :=
(.fork 6 0x42191225ce97d6927f8e5 75
(.stop 7 0x38e6730235ed2cca834486232 2234)
(.fork 0 0x0 48
(.stop 17 0x38e95f75caddeb5cb6da3c7773d8d6175fa1e86d2dc9df318108849d5913 3950)
(.fork 0 0x0 64
(.stop 28 0xe5fc757d9c2970e39957588a36912f08cf683db7115a9b8e41ba0d7a1dbd43b5d1dcc08d7a3f8d2dcf633ff543a6b8db7e 2187)
(.stop 15 0x38e36b9368f4e875590f3c777474d6175fa34b750ed90a7ecf727 2989))))

private def tree156_118 : Tree :=
(.fork 11 0x3410f3c3d61b747853618d9d3db90a25831d44 75
(.fork 15 0xd853fc508c428d69ace582b61934d015f2a35ea84ac7de399121 42
(.stop 10 0xd2ce232e39492ada199b9d27544657d56b1 2514)
(.stop 8 0xe39e232defda54d9dd11766e768d 6275))
(.stop 14 0xe39169b5a99ae3da4c95927d13a429b525972d78e65f2b433 4093))

private def tree156_119 : Tree :=
(.fork 0 0x0 58
(.fork 7 0x33a1b88c554bf93055cede7f 47
(.stop 13 0x38e753475d54e7dad1d9e063c29e512244fd2f366b9de4 3938)
(.fork 0 0x0 42
(.stop 6 0x511768a27a8e2e5119617 13195)
(.stop 9 0x33851dc16b2e39c7fe2031a547097558 968)))
(.fork 0 0x0 48
(.fork 9 0x2e03200ca277cc6049652756409913 39
(.stop 2 0xd589617 1911)
(.stop 20 0x927f8e577db97e3625c11d7ed445deb569ad5883c446c51cf620da546e234b349938e6 13795))
(.fork 18 0x7e83ce11888042048fe35a316b2620f55e1ba077727d0e203fc569a79e7563 75
(.stop 12 0xe381e8b88cf5d54e95c1fd9f8bb8445da53d05591d 7039)
(.stop 24 0xcda6705cb55606dc7de8be1497477c9b67e3625cbed75dadfe398b9a77d9fc7def495066859a9888f42a 5935))))

private def tree156_120 : Tree :=
(.fork 7 0x3cf25649e43618d9d3d5d0a2 63
(.stop 8 0xdc3dddfda2127557eda47d7b1740 4260)
(.stop 4 0x64437bc0ce74b7 13371))

private def tree156_121 : Tree :=
(.fork 9 0x34c1b8877c2094e1a424509e5cbd747 59
(.fork 9 0x5b7192065327ecbbb2f30f5d5ce973c 63
(.fork 12 0x6b5a66ae3987821e3c95333d51324e694d46db1b7d 40
(.stop 6 0xe381256d78845ce13df1f 2519)
(.stop 7 0x384f9c2f5e21d5b6758b238e7 7980))
(.stop 21 0x35e8693b8457a2f5d55ca5ae9e39c33911a5427def0d80d7987852790d863d5cf6e4be7559 1891))
(.fork 0 0x0 66
(.stop 16 0xdece70be3a476438359b9d564212085851016d07851e3cb272f092fd 4694)
(.fork 0 0x0 47
(.fork 18 0x50b636994ea8d6da0402d00b829f16849533600d97448913f4bcd6955ab1e7e 40
(.stop 20 0xd7b1defd7a1fc7e385b76cd92220e1490a24be5ad86b735591ffde8b9e835d55ca5ae9 5958)
(.stop 14 0x8d8f36c7a4753d6ddb7146b61d44e1199b9d7b1d5b8b238e7 13004))
(.fork 0 0x0 53
tree156_120
(.stop 30 0x7ee736561d5c17d0edd54d755e79da21f2cdc3de8be3ae1988da77b349d53a957ed611d7e02940a6493d33d511c44e568f693b5f1 13948)))))

private def tree156_122 : Tree :=
(.fork 0 0x0 53
(.stop 21 0x37bf07d09d7e39db7ece59b72e3997e8862f5ec3618d9d0a949dd29dd4d45d01b7dd0ed0a2 5310)
(.stop 2 0xa535fd 13816))

private def tree156_123 : Tree :=
(.fork 0 0x0 50
(.fork 10 0x3281fe0f6878238d8f543db912544fdcad 66
(.fork 9 0x2b211d85b42f092fd5ccd743666d9af 33
(.stop 19 0x3677334f5df75474b400c87fe72db7b10ce56a8d2dcb043f912f0e5f07714e019b9 3914)
(.stop 13 0x17e8e3a573cdc5d6a8730367794eb367667d9ab705f559 13475))
(.fork 0 0x0 71
(.stop 14 0x8d935d579e768333d126755b999f66af5591e28ece51056ad 13948)
(.stop 9 0x35fd2f3367779ff55444b156255d7307 4253)))
(.fork 12 0xb002d0ce46d51b849ed4959275509d4467ed3565 59
(.fork 7 0x390f5480b2eecbcc3b3973c 63
(.stop 13 0x2701e1160fde121304d788a8944c8b9a52fb8e65351b7d 13206)
(.stop 6 0xd7a16a6ce58785428b559 4868))
(.fork 0 0x0 71
(.stop 14 0xded99afd9f16a6dc9cd9d3d5d2706b73559120c78a3d3d748 3785)
(.fork 0 0x0 66
(.stop 23 0x37173b277ae99c397c5fa22bce399cc0d754c55498d73b5f55e7f7c6b5591e1478f31212fd66bda35 1460)
tree156_122))))

private def tree156_124 : Tree :=
(.fork 13 0x21b08702b619349ee33acd013fc9008448513e50a1445 62
(.fork 7 0x3e611c89ed27eca885f69c17 42
(.stop 14 0xe399e91dc559b9da19b89e122197927b8e8169938950916b1 4218)
(.stop 6 0x7a478e641eb72666e7424 14109))
(.stop 27 0x368c620f7aa495938ecb4142e690dddece5a532a5db8e67a460fc926371566e5defda197e1d338c6658199a277972ff 6733))

private def tree156_125 : Tree :=
(.fork 5 0x333ae908b79eb852 59
(.stop 11 0x1e91e3991b8e3ade83e5f9446dc98f5d6b59de5 14101)
(.stop 4 0x7c9b726511b688 14110))

private def tree156_126 : Tree :=
(.fork 0 0x0 59
(.stop 10 0xe399f1ad3385047a2768d709754e0f545b7 496)
(.stop 19 0x38e4816f546777771f695354e79e6221d755cc07a478e67a2768d44b5e7f7c6b2ff 4253))

private def tree156_127 : Tree :=
(.fork 0 0x0 71
(.stop 14 0xd755e7f1ff78e67c6b3020f546e827d0e203fc5e79d561748 5947)
(.stop 15 0x35e683f767079ff55d1ba16016dfb68c29b6970e3997ca61f3439 5028))

private def tree156_128 : Tree :=
(.fork 0 0x0 70
(.fork 10 0xd306e225649e427d4e1a4be530a5cbd747 63
(.fork 9 0x483254c9dd33d4cfc44c97365d01b7d 54
(.stop 25 0x32ca509371e0eef5d55ca5f1fe39d1cd7c9b715779767a14344fc2998e203a8cf3ee3985163b4d6a572a5caa 6408)
(.fork 0 0x0 44
(.stop 11 0x38554e97688511b5ec5d277152c44f4e3da14c1 3616)
tree156_125))
(.fork 0 0x0 62
(.stop 17 0x35d57a4784b4e95e79da3d30c50b74b7584f43611e851520709ed27ecd97 5011)
(.stop 3 0x34393b3b301 1931)))
(.fork 9 0x2c00b446927b525649d5427511b565 72
(.fork 10 0xfb477e22f4b2d3fa91c357e56135a4d6ae 63
(.stop 5 0x173bd5185162775740 13518)
(.stop 23 0x32e730eb2cb777f53f8d9371d83e6193e1313a6ded91d572a74ce1e2925e49c16945ab572e5d23303 7201))
(.fork 0 0x0 68
(.fork 9 0x48822b8ce435f8d9550bd43e6195916 63
(.stop 24 0x862f67133373737a478e652fb8528b3a49fe395574695354e0f54771424d09c7a0354614349dd3659b7d 13781)
tree156_126)
(.fork 0 0x0 63
(.stop 17 0x35d5862f5e61ff92495d235533881cc07a478e67c6b4ce1434d965d01b7d 5947)
tree156_127))))

private def tree156_129 : Tree :=
(.fork 10 0xad43e60fb45b727d0bc235fcd965f297e1 58
(.fork 9 0x64719486e21e28a843155092427573b 45
(.stop 12 0x9c0f8513fe75fd669f8e4645b5581dc12755119864 14407)
(.stop 18 0xd56205be392188deadfb3d0b0950581756555d768a2a3ceba3b4d0a46de338f 5655))
(.fork 0 0x0 68
(.fork 6 0x1104801220a8e2a3d87b 56
(.stop 28 0xd9e2233d7560e9def539558075f25d197cbd2dda54816f84751187fd49678e661f35651bb0bb836251c6474d26149b5fb3 5936)
(.stop 5 0x338d511756536572ff 3323))
(.stop 4 0xce3d0a449d7563 46)))

private def tree156_130 : Tree :=
(.fork 0 0x0 54
(.stop 15 0x3435645b3893aeb71e7c9b7250f104fce39a226d7ad25f49bd6a5 4557)
(.stop 20 0xd7891cde381f1fda3c9f32c60eba422f2f938838e6889b5f703181fa4209446585f5fd 7664))

private def tree156_131 : Tree :=
(.fork 0 0x0 45
(.fork 10 0xb002d0f54c5d365525649d54276459e80 32
(.stop 12 0xe39508655eb71d7c6a532e3981f00a51e89da35c25 6870)
(.stop 21 0x32ce669f7168b1b8e7620f7b07caf8e66435c0fe120cf14939deed53862f29cd08b99a3851 6408))
(.stop 15 0x249fe39d745619f41b6bbb69347434c90d4095f3158c6644fb565 13951))

private def tree156_132 : Tree :=
(.fork 9 0x3a0ce86e22a10c555a816a15cede7f 45
(.stop 7 0x35d56b4730566bf8511dc080b 5017)
(.fork 0 0x0 41
(.stop 21 0x367e7a4736964359a7dc45b71e39d74366bdcb6cc153046951c25d56113f704f56551156b2 6878)
(.stop 13 0x32d24e39428d59513f4bcdd4ace14d8b366d086530f4c1 4385)))

private def tree156_133 : Tree :=
(.fork 0 0x0 48
(.stop 11 0x34c152fb8e6388356200b80ca18f46484965275 3328)
(.stop 9 0x370d2048c415acb5543880ff179e7563 3328))

private def tree156_134 : Tree :=
(.fork 7 0x472207094227b4cf4499dc17 41
(.stop 33 0x35e37cb336a8b2b5d57ede052e1116ac7c9f2e40a54baa585d8fc64677167f1e198900354a448913f55e16126db769149c5613d5516b266d1f1e 4235)
(.stop 26 0x2d784b862b2cd9e872d28d8f67c4bde2cad551e918d923fedc35e79da453a650b59056443391365ce1a5cbf4c5 13497))

private def tree156_135 : Tree :=
(.fork 0 0x0 63
(.fork 10 0x120c7821e3c95325809dd27b91326db1b7d 70
(.fork 8 0xd303e0195c6e233d4cfc3869747 59
(.stop 22 0xdef6226e399861e1160fde12108213f108b497f8e03d1d384d2f5446585f7263d74f684e6939e 8586)
(.fork 0 0x0 72
(.stop 15 0x37b9585f71e7c9b68327ccc4e318ceba4bdd30ccbe45162f21613 5961)
tree156_130))
(.stop 25 0x35d5708767199c2aa9d4fd6067a0342c2060b2540175530aa833a1dc0c555cede7fd3349ed29dca89511b565 2059))
(.fork 0 0x0 59
(.fork 9 0x7711df89ea27ecbbb2f30ece5819de5 68
(.fork 7 0x4801448ce4424d09c619587b 70
(.stop 21 0x38e694cb71d693b7b07a035dd83df7b44e553a3642190dd0c00de0ad8648194c6e227ccf68 7825)
tree156_131)
(.fork 0 0x0 58
tree156_132
tree156_133))
(.fork 0 0x0 71
(.fork 8 0x86c2b20adc4881e28eb55a516ad 62
tree156_134
(.stop 30 0x926b2d3864f85566cf8e9a836aa9d754d8d3d412f757e755e42913924e9942d510339138ccecd5345d4bcc0434c386972f5d1f4cd 13010))
(.stop 2 0x44fb399 13205))))

private def tree156_136 : Tree :=
(.fork 6 0x22d8c5e46f11da4e353ab 65
(.fork 10 0xfa464e207c82a2c4cb2633e8ec868d9a49 63
(.fork 13 0x3f1e0878f254c96027749ee3658ffc3ff91326db1b7d 59
(.fork 15 0x3411dc49ea52f9902889a35ee398bbb2f312644e6939e5819de5 32
(.stop 17 0x397e5f273965f6f4a33d1d615e12dfb5d9d52f06dff7bd5cea49fe39e2c3 1262)
tree156_112)
(.fork 0 0x0 52
tree156_113
tree156_114))
(.fork 0 0x0 57
(.fork 6 0x2c78b3133bd3984e81f19 29
tree156_116
tree156_117)
(.fork 0 0x0 53
tree156_118
tree156_119)))
(.fork 0 0x0 57
(.fork 7 0x6512c78b3133bcd023da9f19 75
(.fork 11 0x4a086c2b614649ee2a0ca95448513e50a1445 64
(.stop 7 0x38e679fb5f71934954257ca78 4415)
(.stop 32 0xcb4990bdeaa8dccd92358d285a4de605d5b7cb1fc68d8b8e55ce9b70d7c4f6e449513f47011d955895757299cade39912c44e17ca5f87306 6103))
(.fork 0 0x0 70
tree156_121
tree156_123))
(.fork 0 0x0 53
(.fork 9 0x3cf0f587853618d9d3d5cf6e4289d44 75
tree156_124
tree156_128)
(.fork 0 0x0 69
tree156_129
tree156_135))))

private def tree156_137 : Tree :=
(.fork 0 0x0 45
(.fork 4 0x49592756b91b7e 32
(.stop 8 0xd57573bda0d269e39d74870962c3 5791)
(.stop 11 0x283ad3097d5e39abe3e5fdb7fe3a09f96b63558 13782))
(.stop 12 0x6bbf4a2311938a706b2f04965c1994eb8e68b0b691 13967))

private def tree156_138 : Tree :=
(.fork 12 0x36048025409602c84b31319526549a54d1641d90e 58
(.stop 27 0x35dc77936756dc75435fa1f20cddca6d310590dcb5c8a4cb6d56c58196a066a38e40a8078a2a1139f58156075ceda42 4868)
(.stop 4 0x58074ce3d7b726 14109))

private def tree156_139 : Tree :=
(.fork 7 0x9ed365525649d54276dfb565 74
(.stop 30 0xd50c6d1e39d5faa5df2d088c75da5fa1f20e5fcd9b4e7d73b7791f1ace290074c414295111a37692355827e4a893141120557557a 8445)
(.fork 0 0x0 58
(.fork 8 0xa947701e28a844e7d73b68f5f1a 69
(.stop 22 0xd279c1ee399c19d771883d9c1c0fd7997dc79e1e7ad50d6a166899a87a038e442753944e9187c 5338)
(.stop 27 0x2220cb20f43492b6757ed797f5f735e635d5a41cb48ea397278e65f55adcd56033b2eed6065a816a166899a87a0343b 13635))
(.fork 0 0x0 54
(.stop 19 0x354366e771d5a95c18d0e56126bbf71e5acb5e233ed310692355333b0d023b4d601 1893)
(.stop 8 0x5d235e65d0355d1b84cfb4e934ca 13651))))

private def tree156_140 : Tree :=
(.fork 0 0x0 59
(.stop 5 0x354e27ed2ff4c11606 2538)
(.stop 4 0xd5949602a27399 1922))

private def tree156_141 : Tree :=
(.fork 9 0xd8083048025409602c84b314995269 69
(.stop 28 0xd9c187cdecc6ce2041c13d0be36994eb5e54bfb68333b12e469535581e28a8458156075cef5620fb45b716f865833d8cfb 2815)
(.fork 0 0x0 65
(.fork 15 0x402c48b2549592756b93729193881f2310ec83d88f6347291cf 58
(.stop 13 0x397f6b7dc0bd7d1748def56a17a0368366ba233dc49f1a 4863)
(.stop 8 0x22675f444977bd5cbb71266bb567 14265))
(.fork 10 0x22988b52c48b2549592755119b7e779b4c1 58
(.stop 13 0x336c72d385072c35584c1156c58196a07a033991e29607 2212)
(.stop 22 0xdeae222cd991b0dc98b14cdb1cb47edb8504c1156b55b16067a0343238cd13f68dda4872c3567 1893))))

private def tree156_142 : Tree :=
(.fork 13 0x3e2070027030cc5935e8d915ac9f1ed2f5131499f4c9 54
(.stop 9 0x1126d04d3995cef5543d61882ce651d5 13205)
(.fork 0 0x0 75
(.stop 8 0x3aeb71644ff5f866d355427a5882 13205)
(.stop 2 0x44ff691 13669)))

private def tree156_143 : Tree :=
(.fork 0 0x0 57
(.stop 17 0x34be7c978e644fde7eda0d13861f343b5d338e830fd07c42619b9d7c943a 5810)
(.stop 13 0x107ce132362dc59f25e39850052f96b2d7f4cfb61f34d1 13816))

private def tree156_144 : Tree :=
(.fork 0 0x0 57
(.stop 15 0x337d3b252fd5d0f68829f0f5444ff5652a55131499f7292c7943a 3475)
(.stop 16 0xda20e37dea97cf5f7339122a0c4431651ae4731267d324ec95acb4c1 5492))

private def tree156_145 : Tree :=
(.fork 0 0x0 39
(.fork 8 0x2eeceae3b1cf6357c96175fa1f20 69
(.fork 7 0x3e60fb465822bccfb474dc1e 71
(.stop 9 0x1575da446e12c79138d588483122078a 13669)
(.stop 23 0x3553645f8eb536b5433851138da29df6d7c56b2620dfbbda20a8e3d5157561df56549d56ab66b75f8 7205))
(.fork 0 0x0 57
(.stop 8 0xd5953a7d7c83e1141ca83340943a 2853)
(.fork 0 0x0 45
(.stop 39 0x9c5cb225c9d28235cdedd6b281578e7703f5f2277913f4c41a37779355329dce1350d14397061fbace543331dc078a2a10b0c7c6a2bcd3349ed2c48b253655275509db7e 13158)
tree156_142)))
(.fork 6 0x2510cec4c11a547097690 45
(.fork 10 0x1d8c77027b4b122c94d9549594465d21b7e 66
(.stop 12 0x8b0b7127a1e05be39143a7ed35631e3cd933b25a4a 13657)
(.fork 0 0x0 65
(.stop 27 0x14cddef55f6d5662c2e399f25d29a362e39dd50e39174661f34c244fd2f34c4199c66bb56700fc81f3b20f624e822c3 13194)
tree156_143))
(.fork 0 0x0 65
(.fork 10 0xfc0400fa4659207c82a3b20f624e822c3 69
(.stop 13 0x38e77069cb4d2bd877cbd4e2472ff68f4e7d73bd59ccfb 3932)
(.stop 14 0xdc665d5e39c6c6d090cf03d732fb38936912779b8a756f729 9064))
(.fork 0 0x0 69
(.stop 20 0xda299b2cdfdd5bd078776da205be0f685001e088102a38b173d51575d59465833d8cfb 5500)
tree156_144))))

private def tree156_146 : Tree :=
(.fork 8 0x1282b50adc3eb315cc6533c5a52 61
(.stop 8 0x620f7b966a756300f07802a1d436 13662)
(.fork 10 0xab0518193881f255507d42651cf7ef3399 48
(.stop 19 0x38e6496f54183f75433370fe366df71a07c59b972fb8e13d4925949d5902644dc09 8133)
(.stop 18 0x72d77b97f1f8eb55eb55966e6057da1a233d505c25dc90ce14495fc583f77b4 13964)))

private def tree156_147 : Tree :=
(.fork 6 0xd1cb2c3638e335105c20 48
(.stop 24 0xe5fe362cd9089a88a38eb77b78e613cdf2788cf53c751338b66c9df6d4f96ab72e5d54d7ed2756409913 1575)
(.stop 14 0xe39a706d51a360dc9df1cd2917486b935fb2524f5758332f7 7661))

private def tree156_148 : Tree :=
(.fork 0 0x0 21
(.stop 5 0x3693511b5fb4495cb9 3297)
(.fork 0 0x0 48
(.stop 15 0x33657edf8e9277cf6e44fdad56b7f5fb31810884965275644dc09 3451)
(.stop 25 0x33657c578e68d7b8527a0b71f8d8b2cf816f546709771427a8a7435ecd9250915f572d5fb7d9f960c643b7b4 2207)))

private def tree156_149 : Tree :=
(.fork 8 0x22b49e1425109b46cd6985aa7306 61
(.fork 7 0x3b1b64a87384539c68e9a45 23
(.stop 9 0x39818b1770d9e778465ac6232d0e16a3 1926)
(.stop 10 0x79ef54688cf8517c7770d702754f620f5e5 14407))
(.stop 20 0xcd95d41e5fdf1ce11cce3509d446d7a5d5b8b177ab0cf07863b4d43061b587379ef4d1 5945))

private def tree156_150 : Tree :=
(.fork 0 0x0 62
(.fork 11 0x3c0f985a62070baa3ab12674e6d39d7a0e18a 54
(.stop 17 0x32dc276b68666e78eb3ac78e63a8f4c511e86d26dbf97f27509e55cdd73f 2361)
(.stop 16 0xdc55e8ce5fe193e121d44ce34e17d519744e399deddc50cdc888f68f 4377))
(.stop 10 0xce35437e5fd41fd0bc9493d9cfe775535fb 3303))

private def tree156_151 : Tree :=
(.fork 8 0xcc463e19246d93fb900946fdb6f 62
(.fork 9 0x3e61dd078127b49fb499d39b4e75a46 54
(.stop 10 0xcdad73d6b65adbd9fc47a5cdd73f61b5c0f 5945)
(.stop 15 0x28dce114ebadc39b76ce652fcda057395cf767f365d2f36db768f 13944))
(.fork 0 0x0 70
(.fork 4 0x16e0a8d3130ecd 53
(.stop 9 0x38e672ab386429142dd7e89592790d9d 4719)
(.stop 12 0xe1162cedc396965aaf3991920ce642915fb7027563 4873))
(.stop 17 0xe10e38d122dc39fc7e1443dd1e18a7b425143050f5732cc1930961b74be 14406)))

private def tree156_152 : Tree :=
(.fork 7 0xbd07c4d893f799b96e2b725 70
(.stop 17 0x1c24d7e9309ce1930ad58cd975ab187acbc0ecd4e949da3398ebadc79f26 13184)
(.fork 0 0x0 71
(.fork 7 0x21b2794b1938cd41f7081e8c 38
(.stop 19 0x353c8ff74ce4e6f97f0c983bb13a0627dc7990ecbd9259a0f38e6009428c36393a6 3137)
(.stop 5 0x33845d237bc4e6f4be 4725))
(.stop 12 0x27b74cd532b30770936858b3b71e2768a873d9f693 13509)))

private def tree156_153 : Tree :=
(.fork 0 0x0 65
(.fork 9 0x2ac193881f231107d42651ca473dfbc 38
(.fork 8 0x9002518f8cdc3f8d68c7c86223 56
(.fork 10 0x82050f29c0bcc3624d9d50c943b5ce573d 48
(.stop 13 0x38e6864f8456def36535edfb7e3a4c6064099137025e7d 6879)
(.stop 11 0x353c889338b5119919e119094d58d09f70837b4 3451))
(.fork 0 0x0 71
tree156_147
tree156_148))
(.fork 0 0x0 50
(.fork 8 0x3d50f6e449513f51057ce6b55adf 48
(.stop 27 0x35463fba233cda9c1ad2ddcafcb349d02786228d7a56177edf8e944d139c50d9437e1489df318108849652756409c15 497)
(.stop 12 0xcdf1436e14943bd9f8e204027567426d6175fa37b4 4400))
(.fork 11 0x2900a549ea29d0d7b3649424511961772d74be 56
(.stop 21 0x36735a5b7bd83e3374755397e77db53c889369108203d22020b0a2ee0d89367543250ed73d 1875)
(.stop 15 0x1b6fd4f2224da3d6a78d8b4af5aaf72466c9df67f1f5dc75535fb 13939))))
(.fork 0 0x0 50
(.fork 8 0x16b8f543db912544fd4416b55adf 69
(.stop 14 0x7c7770d702756700f06d96917852144c9f42c5cb2a4c25575 13666)
(.fork 0 0x0 62
(.stop 37 0x32cc8b1736a276b5408152188d78d9b9e38ceb18da767a5cc97447a233973b4d73f61b768f1e04fee4025a466dbf4c500f06da20709ed27eceac499d39b667e18a 4223)
tree156_149))
(.fork 0 0x0 42
(.fork 9 0x2900a5450a27a8a745091446585d6b1 56
(.stop 7 0x38e6a84b7150f488083625739 7965)
tree156_150)
(.fork 0 0x0 49
tree156_151
tree156_152))))

private def tree156_154 : Tree :=
(.fork 0 0x0 61
(.fork 7 0x63f19546d920a4e11426939c 36
(.stop 6 0xdeaa702d53d0a4d7bd26c 8600)
(.stop 12 0x5cf354688cf8516953677385b8e7429354f86637bc 13807))
(.fork 0 0x0 59
(.stop 3 0x371a44d9606 4398)
(.fork 6 0x1440b1e2e94cef49b32fd 72
(.stop 5 0x1c1bd9dc9f133a13a7 13638)
(.stop 4 0x888397c86637bc 13791))))

private def tree156_155 : Tree :=
(.fork 0 0x0 57
(.fork 10 0xf4c6512c78ba533bcd02498926c7299cad 59
(.stop 22 0xd032496e60493de3a4a6a3f759b8d2c1a4bd528ce83d6f5e618f49ea2eecbcc336d12e5ce973c 3299)
(.fork 0 0x0 72
(.stop 19 0x3712818b8e929ab4b0538591a7073543509f691121c65522c89572570ce83d6d4dd 5310)
(.stop 20 0xe39d08b88cb84766977b39c2f54688cf8465ac743b03041f911b4500538568f70735f1 8134)))
(.fork 0 0x0 61
(.fork 8 0x18fc6551b64a87384539c68e9a45 75
(.fork 8 0x11fc7862cc0eb947011d95ac59b8 36
(.stop 4 0xe11a702e11e2bf 2050)
(.stop 10 0xdc367a5d9f9883def1fc69e778466dbb5f8 5810))
(.stop 24 0xe119b82e6062c5d774ce3d28dd5386278e75f7db6e6def43057f97d29c2f67e3d7cf6649b560f77bb439 2684))
(.stop 31 0x270be3a49ead9e876213a75ef3fab54a692f4b02570a8044a513b4e453a751094dd6e1b4392ca57325d134cd1de478633b0ed350c34d1 13635)))

private def tree156_156 : Tree :=
(.fork 0 0x0 66
(.fork 9 0x5b416f8d933f90fff5ccd74377b1f22 57
(.stop 10 0xe3a6198e5f1380d5645101944a834bf5cad 1115)
(.stop 17 0x142de39ddf67f1e497cde9b8ae119cbad9f8b2977bb562208157b66e3399 13791))
(.fork 0 0x0 54
(.stop 16 0xd9de70bd50d870cbfd26d583f3065cfdfc7d7acebd3b4d26f4c25c0f 5783)
(.stop 22 0xdc351bfd9f12f055ef85255895755aaf4d14e95c11d58926d75072ff141c63220710a449675fd 4081)))

private def tree156_157 : Tree :=
(.fork 8 0xfa43ed1954ce84e454dd5f91b86 59
(.fork 7 0x78b27ecbcc336cfdd5819b79 57
(.stop 21 0x38e946cb7122e7b2d25ccf6755d27852422f2d446fd44270536773a9cf5b5ce973c61c1cad 4861)
(.stop 7 0x37bd6e2b67527c51bf705367e 5961))
(.stop 18 0xd528feadc68fee510b5465cb75d95ccf3032c60c4e318d08b4bdf4b73d6f399 1749))

private def tree156_158 : Tree :=
(.fork 4 0x2c1126773034b7 57
(.stop 18 0xcb291b27ef77bc1d8e7a0dc3e83be39dc1f86635df7f076773a9cf4161c1ca6 1882)
(.stop 11 0x1393dc3e83be39d867d579c1fd77dfc1817367e 13666))

private def tree156_159 : Tree :=
(.fork 0 0x0 65
(.stop 32 0x8da73681d5a404d4f0f40def5733e5f108b42917427c538521b50b0a2ee0bcc383143250edc11d9f8e2040253a5d58909944c13a05f39fbc 14256)
(.fork 0 0x0 66
(.fork 7 0x5b416f89e0364d1185cce229 59
(.stop 11 0x38e9202f7a85ce973cd59c3dc18f49fb4742358 4861)
(.fork 0 0x0 51
(.stop 6 0x3a9f67e7f075df422d6a8 13943)
tree156_158))
(.stop 27 0x38e7862b98179f77aa49d5cafd551cc0e148b182ec8f5d3da330703543d32c78ba53a9d73a5cf1870729b4363fe35f1 7650)))

private def tree156_160 : Tree :=
(.fork 6 0x1e08f543db912544fd441 67
(.fork 9 0x3eb148c8ad2784b2a46cd6985aa5e88 62
(.fork 14 0xaa42ae0cf86da1e3881c27b49fb3b14f603d95099499d9ab 66
(.fork 5 0xffb3ffd7335d0df22 51
(.stop 9 0x35d957d78e33a8397c5cfde7bdef1910 3761)
(.stop 10 0xe38e369d77cea0e5f173f79ef7ba927f5e3 3761))
(.stop 23 0x32d59e7770d7c778e37a4754f7a0b4c55cca7a6d9cc58dd78d73702fc89c251dfbed7ad73f79ef436 2497))
(.fork 0 0x0 66
(.fork 9 0x4101085b433e0cf9364d7335d0df22 54
(.stop 16 0xd2c1a50e11a062999b8e3585d7e8d7bc78633b0d023b4d430535de7b 6265)
tree156_154)
(.fork 0 0x0 65
(.stop 26 0xe39d7dfd2d190ad51863f4e73683581a233e1183d311d4b1e498926c4e81ca6d0cc3e91938659207c8ba3648d94 482)
tree156_155)))
(.fork 0 0x0 74
(.fork 12 0x1280e40ad46e633c4e1e38d925b49cd5f05855a52 61
(.stop 10 0xdc9191cdef509a620f55e00cb5671e0078d 2690)
(.stop 30 0xe3a59b7dc68623d0025d3dc3e52fd9f96175fa1e86ce2d2754e3d3a9640b71f5a9f2fc146064e207c8ab2554bc641f57dd7ef3399 4232))
(.fork 0 0x0 39
(.fork 10 0x940bf030463418fcbbb4e9d5f2585d7e8 65
(.stop 24 0xda3d3a1e11e198e3a4c5c813f85250ef7240f4c50734093a0d5886591ddc81f22e8f4941f50995f75e86 6884)
tree156_156)
(.fork 10 0xa2c2901400a6a29f0cec66e1a547097690 72
tree156_157
tree156_159))))

private def tree156_161 : Tree :=
(.fork 0 0x0 48
(.stop 23 0x37b76e1397f927e83bd2b909ecc0591394d38e057c35e85ab3691192081c3398cfc42210a457ed611 5033)
(.stop 4 0xda3cd97499f390 2555))

private def tree156_162 : Tree :=
(.fork 8 0x940c12eecd8f49bd5f2585db84 56
(.fork 7 0x3e016d08242c28d89474d26d 72
(.stop 7 0x37b75ab36837f0e0f7d2b9b86 3150)
(.stop 12 0xe12142dd9e938ae1196acda44bc150ede867ef343b 4880))
(.fork 0 0x0 48
(.stop 17 0x38e7471ddeed0c89df5aaf84f1df082529c509161c1de3cbe90a453755fb 2857)
(.stop 4 0x1b6f2fc1df338c 13050)))

private def tree156_163 : Tree :=
(.fork 9 0x28b0a40b1833b16ac6951c257f07690 56
(.fork 9 0x3e016d06d42090b0a2f30d8944e526d 65
(.stop 12 0xd589398e14a70be11666ae3997e463f5918d2dd43b 8586)
(.stop 16 0xe148f5bdef55fb9c2f5d9707f4ae862b9815f257e2da29b867a375f1 1883))
(.fork 0 0x0 48
(.stop 12 0x507b7bc2c793a0cbf06482070cfc422127553755fb 14250)
(.fork 0 0x0 57
(.stop 10 0xd2dd4d46461cc0e39a18ace3077c1e24825 5176)
(.fork 6 0xcc49e02ca4c4c46ff2f6 62
(.stop 8 0xce219b9da0c78b5109b86e39a18a 5961)
(.stop 8 0xd2b9b8a7c9b6836e1b71f3da3390 5186)))))

private def tree156_164 : Tree :=
(.fork 0 0x0 52
(.stop 21 0x22bfe399b88d2dddf488c75f5312108c64520fddeb91b247417e866e768d40255ff58356a7 13783)
(.stop 6 0xded9130cbf063d644f563 4245))

private def tree156_165 : Tree :=
(.fork 11 0x50f1460b0a2c74bb82f30d89367543250ed9a5 42
(.stop 20 0x66cb678816f43342438e6640b5673ffb69116711304e81c25da40d925091446585dcb5 13962)
(.fork 9 0x2529c0b1e3f8cffe5a316b2620f4be 69
(.stop 16 0xd76a496d2adf27816f851427f97c5a8f68a19152fcd59c9f431811c6 7515)
(.stop 19 0x1de2e399b7bd2adf27e145913d0b43b633875e919175625a6a22e94eb8e96e17433 13195)))

private def tree156_166 : Tree :=
(.fork 0 0x0 52
(.fork 11 0x77722788ad27d0b2c3880ff1402569a5a9de79 74
(.stop 18 0xe398a62d504d7b72d768533876861930d0002f41f138959b9e38512744f5615 2695)
(.fork 0 0x0 42
(.fork 15 0x93936196007511dde777f69016709ea35ed42451195f55ac5cb5 63
(.stop 16 0x92438e1779f70f2749c1acb558746419b7be399902dc517405f6dde9 13624)
(.stop 9 0x32ca778f7145821906e399b726ddf433 3601))
(.stop 6 0x585b68c2c78ffe620f4c2 13363)))
(.fork 19 0x4a0adc3eb255463218f4780277cc603d4925949d53a96409913ce41615694b396 38
(.stop 14 0x5a477ad585d91c7a1b8e658332fc38959b9e3acfe33ff9883 13971)
(.stop 20 0x7cb370f753b2fc61c2404d50d9b9e3ae70bdc6960c7f178e6585d72b5d2f4ae448b68f 13953)))

private def tree156_167 : Tree :=
(.fork 9 0x51916f87852080829364cf614461f22 49
(.stop 28 0xe39a3fad9fdfbdcb3de87dc69b8a709218ee141c1472bf2fb429125949d52f4619f38c1e04f533db4fee46fd25a49d17cd 3003)
(.fork 0 0x0 67
(.stop 14 0xd9fde87dc69aeeda4d1d0581b2fb429338c1e1878e33e0cf9 4553)
(.stop 3 0x36935fa3690 191)))

private def tree156_168 : Tree :=
(.fork 0 0x0 62
(.fork 10 0xf987811e3881c27b49fb2a20a953ab0ec5 53
(.fork 5 0x9393618f573fc97da 36
(.stop 14 0x116368c27078e10eccf474bbf8eb88ca49fdc59f1edc999b9 13634)
(.fork 0 0x0 54
(.stop 10 0xda357407a434b461af8eb647737e3d6173f 5654)
(.stop 14 0x274b68570938eb86637bc428d86bce21616da357407a435ec 14266)))
(.stop 14 0x751738064777b63b4d73f5f4b5f24c0939cd3140c15fa3690 14253))
(.fork 0 0x0 54
(.fork 6 0x1e18c513408f583db5309 63
(.stop 10 0xd2d10085d036900304641538574cdc956a5 1779)
(.stop 7 0x2061dc5938ada313a377bb306 13957))
(.stop 8 0x315b2fe0f946511bcf39627d34c6 13502)))

private def tree156_169 : Tree :=
(.fork 9 0x2b216d05be3120c5d33e4d933d85a4a 57
(.stop 14 0xce31009e39cc4e756f4aa3fa96936e1b5591b54b1e3409870 966)
(.fork 0 0x0 36
(.stop 17 0xbcacbe15ffdedda54da30767422f54a3fab55e426939cce651d05fa19b9 13968)
(.stop 4 0x50af563402768d 13951)))

private def tree156_170 : Tree :=
(.fork 0 0x0 74
(.fork 11 0xe40ad42b70faca8933c512044f557a5855a52 54
(.stop 22 0x7f1f49e7a0b72764720eeded0f5f5f65d4ccbfced13fb9f16e39ddeed59cd023b4cff3401dc0f 13803)
(.stop 7 0x34b2645b5632a1f39916875fd 3454))
(.fork 0 0x0 54
(.fork 8 0x141050d27509e533b0d023b4d309 68
(.stop 7 0x36905ccb70e7c5b71e6459dee 4378)
(.stop 24 0xd5167a6dc3a49fd9fd606ce64cf3da40a7b73038e94c414c15d275f4510b68d401512944ed4ba6e1b439 1115))
(.fork 9 0x2400974be0fb45b727d187c75534c6 71
(.stop 9 0x38e63b334ac1915ded7a236905d21c20 5934)
(.stop 2 0x5d1b5fd 13810))))

private def tree156_171 : Tree :=
(.fork 0 0x0 70
(.fork 6 0xad852338a53844e95cba 53
(.fork 10 0x11a478525649e427d4d863674f574be530a 54
(.fork 8 0x11e864e2794cec3408ed349bdcaa 63
(.stop 12 0xd50dcc0e39990ddc70516169ccf533f0f475a71740 5018)
(.stop 3 0x35fb3da3301 3313))
(.fork 0 0x0 44
(.stop 29 0x38e78b0f7275d0b4aa94eb8e68d7b7ba5d01b84d780637499d7e3730205cda3c0bd16756115d25f26da44f684bc1310585587d 6264)
tree156_161))
(.fork 0 0x0 74
(.fork 8 0x3902160ad42b7195ccf15855a52 57
(.stop 26 0xdc91f2cd2dcd8473038e6862b5595ac17e8ce08763da0da4ed7f4bc149d769116846512c78ba533bcd02389509e 5635)
(.stop 17 0x1cb5dedcd804bcd6acda44a82362513950ef2fc1938659207cbc14267399 13953))
(.fork 0 0x0 39
tree156_162
tree156_163)))
(.fork 0 0x0 65
(.fork 7 0x3e91938659207d07d4265fbc 66
(.fork 11 0x410ac85b416f8785364ce2d38b8f614461f22 57
(.stop 33 0x32c8779df1bd272224dc4a35ee3a57e8888b69072fa5cb99974aa6e2a18ed551264581973a5cf2358dc9051014645a12c78cef4bf53984e81870 4217)
tree156_164)
(.fork 0 0x0 56
tree156_165
tree156_166))
(.fork 0 0x0 75
(.fork 6 0x12821b0870b1d5ac59b8 66
tree156_167
tree156_168)
(.fork 8 0x7e446111a49ed4959275511b565 66
tree156_169
tree156_170))))

private def tree156_172 : Tree :=
(.fork 7 0x21b11fc4871e38f587091f2b 66
(.stop 28 0x7057847585f4ab865e667e14a0f3863e70bd77d6b2620de87dc84b152ca0bc43fb52595f7f2f31e1478f2c50cf8364d6a8 14262)
(.fork 5 0x430d2cb2844b34ca 56
(.stop 14 0x5d1b5f83d7b4be5acb71d8b378511dec8082ee0d9d38919a5 13810)
(.stop 6 0xdc55389dc94b213d7b396 3761)))

private def tree156_173 : Tree :=
(.fork 5 0x3eb148d1c85d123fb 65
(.fork 12 0x1040db03743e91938659207c82a3648d94583252f 50
(.fork 8 0x18d08ab22e89f2449513f5a616a9 45
(.stop 7 0x11caded126ce38d25649d5ae4 13363)
(.stop 2 0x7c87721 14105))
(.fork 9 0x28c16385982c79119620dded7c874c2 56
(.stop 14 0xdc65df6dec1f1cd09de86e3a5616cbcc50f1914a702ee1090 5949)
(.stop 18 0xded2670cb54ce1385dae6e11cce349599b06b935fb2310cdc425109b472b396 8595)))
(.fork 0 0x0 50
(.fork 13 0x6341e089e127c8b2a3348ce83d50f6e449513f5a616a9 45
(.stop 36 0x6b5798169072ce8ff34063acb85088cf8e4558d60e704b543645b4384c1da54d79573c7072369e3a526c61c1cad7ed34cd27b4ce333e51d94959275509d446 13821)
(.fork 0 0x0 57
(.stop 10 0xcdf5743d7c4f6550e37212c78b3133bcd02 3475)
(.stop 4 0xdc84f655acb4c1 1913)))
(.fork 0 0x0 45
(.stop 18 0x64377bf50fb7251de43dd53634cd3408ed350f74ca27b4ce333e544661f19b0 14109)
(.fork 0 0x0 75
tree156_172
(.stop 32 0xda05119dc55739d4f9b81dc987ff61cddef90138e84bcd7305d1986661eb38d144c5b716f8b283d78f678b1f4c10f744802c84b314c03565 4860)))))

private def tree156_174 : Tree :=
(.fork 11 0x5151e14c653618d9d3db97d15f699076439d44 70
(.stop 13 0x130cdef0ed35101910d2ddc24cdf4d8f365cec34c29918 13967)
(.fork 0 0x0 43
(.fork 7 0x59d276938a556d57c77a1f1c 34
(.stop 17 0x37aa8da771d4e272cc88977ba421e404927b8e82c1cf58585b3072c6907a 2498)
(.stop 7 0x38e861cf68a7caf8eb6db797d 5943))
(.stop 7 0xbbccc1cb1ae5f4f468d67686 13349)))

private def tree156_175 : Tree :=
(.fork 10 0x2c68d863674ea33d5d1c347599076439d44 58
(.fork 9 0x3a2290a843b04ecf581573b68f5a42 51
(.stop 8 0xd51a365cd9e22fda0ced368edb71 7670)
(.stop 11 0x1df6e3919a7e116359da4d883d7d07703b375fb 13175))
(.stop 10 0xd7ecebadc591b6da359b5d07c59d66e7725 3789))

private def tree156_176 : Tree :=
(.fork 8 0x1dc8b012c50e33448913f4bcdcb0 65
(.fork 13 0x2ac143c64e207c8c429e4ec847291cf499160c66719ae 43
(.stop 19 0x38e890135438d6797d61e384f3f8d57ad2c9446dc6489522909da3384f674e29f1c 7177)
(.stop 16 0xdc7e0fbe121256e3adfc7dee4899dc920fdded06d85fa19b9815f67f 1275))
(.fork 0 0x0 69
(.fork 8 0xad451316dc6473d9d73061f22c7 49
(.stop 31 0x35dc3341f18cb2e5cecd955f5e119f16e1160fdd9e8cdc4bd32cf496569670575634e919b98d676782ec4c373130fee46fd6106dbdb7a 8600)
(.stop 9 0x371594eb84883f78450f415585ca741f 969))
(.fork 7 0x5b83600ecd5ab191888b7305 53
(.stop 15 0x34006b5b6813b4d42d5101e78d7e8c653618d9d3a8cf574be530a 3933)
(.stop 5 0x38513d7556b581b399 2538))))

private def tree156_177 : Tree :=
(.fork 4 0x6801b756f4b7 50
(.stop 8 0x5f3b67a1b7b729312d259e3a1adf 13368)
(.stop 8 0xd59d263d9ea369d7716108d8b5fb 4232))

private def tree156_178 : Tree :=
(.fork 0 0x0 42
(.fork 9 0x3c414287fa20209ea29d14245119617 53
(.fork 9 0x7853194d863a8cf573db960c641d90e 75
(.stop 8 0x5a337b14e934ce16e0d013d61389 14248)
(.stop 18 0xe3a1918dc3e404d4fa3fda84b7a85a31cb9def0cec709797f3f9d3944e935fb 2356))
(.fork 0 0x0 43
(.stop 21 0x1571da299b9d4f8ce13f8d902ce4463e337367a496530f705756722909da364cf674e2957c 13481)
(.fork 6 0x18f864931311bf4c3b38b 75
(.stop 14 0xdca62c7d02d08849678e86b7f41a006801b72fdd5bd2cdf2b 3949)
tree156_177)))
(.fork 17 0xb807b01f01dc0cec41e1a54709755800e80d41e288a458156075cef55d 51
(.stop 11 0x1f21dca560ccc1a05be390b18366ceba42916a8 14105)
(.fork 0 0x0 53
(.stop 7 0x37a88af34b33d5d60c6439a3d 6428)
(.fork 0 0x0 49
(.stop 3 0x37293131610 1598)
(.stop 10 0x7f077193d24f5ee14991c7a1b3854c1738f 13481)))))

private def tree156_179 : Tree :=
(.fork 11 0x33b19206531e2c9ea2eecf5d3da143866899a8 57
(.stop 25 0x1e8be116221e39e193cb30affd4f89d892675da7c6b3900ce5256509d7c9def0d0242454d45ce973c6b61adc 13781)
(.stop 21 0x36757a13543509f418422dfc7cdce49fd799740d0e4f5c5cef39033b0fdd6951c257f07553 2692))

private def tree156_180 : Tree :=
(.fork 0 0x0 72
(.stop 2 0xd2ddcbc 4876)
(.stop 4 0x337b5e861f77bc 14257))

private def tree156_181 : Tree :=
(.fork 0 0x0 54
(.fork 10 0x11e876c33b0d023af4ed3497d26f703dca9 63
(.stop 16 0xd9e892ed50e404dc5df1fdc9d611cde43c431691d6511b7ad5cd9740 3449)
(.stop 16 0xd756221dc9d611d78e193d2dc5034c435fb25391d6511b7ad690b301 5947))
(.fork 0 0x0 45
(.fork 7 0x9ed3ad125649d542751197c9 58
(.fork 6 0xa947701e28a845ceda3d 72
(.stop 6 0xcb9d4e15d273845ab9a50 1283)
(.stop 14 0x47633842c1f2d1704b8e542457d55f598706b7355836035ec 13371))
(.stop 19 0x353f88cf5d557df7255d260f9d7b12705ca741f44c9740cc0477c4bc13105387390 3152))
(.fork 0 0x0 47
(.stop 29 0x35e07a138524baf5d5a5c770c8af354644c9439d7e9b88dc9ca845ced7d57793390496542d83e653ada04d80365d1224c416ac 5655)
(.fork 10 0x2d01e811717406e12499da20a8449c368f 74
(.stop 5 0x339042911d8d2ddb88 1600)
tree156_180))))

private def tree156_182 : Tree :=
(.fork 9 0x4a086c21c3404f583fc90087091f2b 62
(.fork 7 0x78127b4a882a554385f457da 34
(.fork 12 0x2c412ef4e2955b5859de8d0943282c1d07a44c9b89 36
(.stop 2 0xe39174c 2515)
(.stop 9 0x32cb927b8e831137bc4ea942457d75ec 5001))
(.fork 0 0x0 41
(.stop 11 0x3542270649fdc59e83e3adde8d095729e5f5f1e 3140)
(.stop 5 0x3715a1078eb7a0f726 9684)))
(.stop 25 0x28d4e5f1e84d50e404d29d38a61ab54236403c43114fe74ea9617d7b1740cbfc5b744b13944e9187c8b1f4ca 13206))

private def tree156_183 : Tree :=
(.fork 8 0x8049ed4959275509d44661f3565 58
(.fork 7 0x2a51dc078a2290a845cedf1a 72
(.stop 12 0xaaa75d535d769300e4e27581b30322f4ecf5a4e0f9 13631)
(.stop 14 0xe39e977d288d0247497d661c354e35f912d50f97e0645b305 7186))
(.fork 0 0x0 54
(.stop 26 0x8af797d3aa72ce2e8771d401d1224bcd3105f8353f581990864359a266a1e80cbfc50d1db0cec3408ed3703dcaa 13812)
(.stop 17 0x37175ac35436e0a233d2c943e645b39403902b7361112055e9b887f174ca 5638)))

private def tree156_184 : Tree :=
(.fork 8 0x146064e196482a255495e3b21264 57
(.fork 6 0x2c78e2538d93984e81870 48
(.stop 12 0xdc89f2adc85918d07d306da0544672d77bf4ea5913 2682)
(.stop 10 0x9e9370c9e737bf538738c38bb3946463724 14263))
(.stop 4 0x49cf41f44cb2fc 13050))

private def tree156_185 : Tree :=
(.fork 0 0x0 70
(.fork 16 0x85865127a0b1e3408e2538d90914279870ce64653195cc4c646222d 47
(.stop 18 0xd756233973f8468b238e55f276815f56186d07d7e6dedcd80365d1224bcd6ac 6085)
(.stop 7 0x341f7a2f683693b5fd49d7691 5947))
(.fork 0 0x0 45
(.fork 7 0x9ed2a251204959275511957a 59
(.stop 22 0x7a276933acb8e53f75c25d539d5bdef48b414486512ca509c5f81916cc148c32eecbcc5819e80 14256)
(.stop 19 0x33847ef785102e080a7a3f7127c6b559364d306692b30519449e83408e2538db399 6565))
(.stop 14 0xd538ff3d0a8bb0cc148c327a9438581b3991e08e3644ff565 3308)))

private def tree156_186 : Tree :=
(.fork 7 0x200a1c28c3624f5d5845f26 57
(.stop 13 0x38489c2f5d99256530d7822c8dee8789209509e4e814d4 1916)
(.stop 20 0xd0c8e30e12270bd766495d7f52ebd7552498d7338f4c1573bcbe8634363d6176943389 8903))

private def tree156_187 : Tree :=
(.fork 8 0x18d0bbb363d25057c96176943383 57
(.stop 20 0x86637b357ef559498f7ba642e49fdeba361a84b4a192575f12094a712c7912c4e814d4 13791)
(.fork 6 0xed8622297e2ce99ab4a9 48
(.stop 18 0x925767c99c37ae44de665b4675d55cedd49e38cc603b222c3ce3ccfc42215fb 13002)
(.stop 18 0xd7822c8e39dd53deb986fd07de8b7c9e404d7560e9cbc0ec88b0f4bd474f2f5 6885)))

private def tree156_188 : Tree :=
(.fork 5 0x8a43d712fe4c1573b 75
(.stop 24 0xe385274729768666bb4b3585f5e07a1e670e3909c43fb62cedc65f21dca465222e89e927e8e2472fdf2b 1893)
(.fork 0 0x0 66
(.stop 23 0x38e7927f538383b84883a769318d0af94926d19d754f4977b1e868af33892780b1438b4e2e498e495 7815)
(.stop 7 0x1249d9e113f4bcd9ae779368a 13937)))

private def tree156_189 : Tree :=
(.fork 0 0x0 56
(.stop 36 0x33432c9863797d13ab5d51d465cad2dcce1d2a49cf99c37ae29a9e869c2f8e33181088496590279f75673ff96b2da4450f16d08083624e0c389109050c99a5 13962)
(.stop 31 0x25d5e5f5c1ecdd5b7fe149e84e5f0c6244fd911ce5130f7091cbf7caf681364cf4d4e299987069d4ed0956108b1f7293ff913249272fc 14567))

private def tree156_190 : Tree :=
(.fork 6 0x86c21c3891c2472fdf2b 69
(.stop 25 0x38e78b3a368cdc62338b3797d77a75f24c3d38a556d616d094d9044c9249cbfc3e616f86523fe112c584205b 6262)
(.fork 0 0x0 62
(.stop 9 0x1910def16b2d30478122a0a954731438 13205)
(.stop 13 0xeaddc64fedd7c93aad7c49e02ca74c12c78c565acb729 13062)))

private def tree156_191 : Tree :=
(.fork 10 0x14006341e08a6a29f0cd233a112544ff565 69
(.stop 35 0x35da400b8e87c9f7bd64163fdcb31b716de397d6695cac75078e00a1858335b19178d8b37b422d4c85aa33853d352597c96970d2b512c55d5610816e2c7 5010)
(.fork 0 0x0 66
(.stop 17 0x35398b2785275375d566ae491dca4b1e3a9d30661c34c12780d935aa1733 6565)
(.fork 6 0x3d7109050b1f27864f307 62
(.stop 4 0xd314b1eda21438 3325)
(.stop 12 0xe3a5088e3a1b7902968dcd4fa2c9dc453854e9b729 4381))))

private def tree156_192 : Tree :=
(.fork 6 0x2e01ec07c0cec6951c25 45
(.fork 9 0x7631dc09ed4959275509d4465d2187c 66
(.fork 10 0x16d078f2780b143174d9368d5a4a88a6495 57
(.stop 17 0x3712447397c694354653856b288835d95cf2198e3a54e0754741f4c193a0 5310)
(.stop 12 0xa5df97d6de76931e2f3996b938e9538341f5abb567 13781))
(.fork 0 0x0 65
(.fork 7 0x3e9196481f2f052646b9252f 56
(.stop 13 0x35e0115b8e444cb8485acb4c244fd2f34c41f18e38ce24 3288)
(.stop 3 0x38e34767396 4415))
(.fork 0 0x0 72
(.stop 9 0x1729d754c4c88b74ca33a16935ab97e4 13343)
(.stop 19 0x22c8cdce198e38d1d9ce38f685ab1f267f0683bd34573a8b3a49fd798bbb2f335f2 14260))))
(.fork 0 0x0 70
(.fork 7 0x2b62c60c4c5ab19187f0622d 41
(.stop 29 0x34aa88cf5d55ca741f4c1b2fd498d9b3d2dda50decce2d619dcb6da206482070bb042215fbcbd050033d513953856b266d1a4e 3914)
(.fork 0 0x0 33
tree156_186
tree156_187))
(.fork 0 0x0 65
(.fork 9 0x3e9196481f20a8ec849913a08b0e52f 58
tree156_188
tree156_189)
(.fork 0 0x0 75
tree156_190
tree156_191))))

private def tree156_193 : Tree :=
(.fork 0 0x0 69
(.stop 17 0x370c7f03851707f68149bdb8488b75651948a848af3300474d73061f1c1e 5649)
(.stop 8 0x88b7847555dc247caf43b1e2b301 13062))

private def tree156_194 : Tree :=
(.fork 9 0x4881964b292ec0e2b446913772e2361 54
(.stop 5 0x38e961f35653d6126f 4694)
(.stop 24 0xe3a249ed2aa8d5e5f59a5decd616620b565646338f61f001a006c6c3756e3fcd539c1e8b1f3955aa35f8 4070))

private def tree156_195 : Tree :=
(.fork 15 0x1a006c32729dd56f756df2cd54c4831b6c78f384d1327eeb558 75
(.stop 15 0x372957ef2f572978e17a137bf8b1f8e08af32fa3d6157b7cadfc6 5810)
(.stop 10 0xd594c4cd2a65d5d50dcb98b1f7b75acb67a 4094))

private def tree156_196 : Tree :=
(.fork 8 0x18a46342eed5f2585d7e86943690 62
(.stop 40 0xd9e0a67cb41910ded9092dc95423a36e977d7559a5da4daeed7c81fb254cb01421d1224bcd38e5f81b6dd7e081c14787812a54f586209c247caf56520a89ed35e0d8f3ffe054 4390)
(.fork 0 0x0 57
(.fork 9 0x5071944a832c78cef340912c5351870 66
(.stop 7 0x37244e634320ac85b4364d6a8 3784)
(.fork 0 0x0 70
(.stop 17 0x37b77c9b98161f75e8424172e66d1aea864f5f22f04eb45f257e2da05b84 5010)
(.stop 30 0xd755075e395d5bce08cd811b4a6153877b799c384666bb6837f1f84766977240ce46d5da0539894bf43b1e288a42a1173b5f5b4c2 2347)))
(.fork 0 0x0 47
(.fork 6 0x7ec9532c512f34c417e0 65
(.stop 15 0x367f707f5d67f1e198e14530577932fc143c64e29e4f4966b9e86 3611)
tree156_193)
(.fork 0 0x0 68
tree156_194
tree156_195))))

private def tree156_197 : Tree :=
(.fork 0 0x0 60
(.fork 5 0x4802540b212cc5300 62
(.fork 8 0x3583e6207082a27b539b4e75438 49
(.stop 18 0xdee92f35cdde87e3917decc1cc653618d9d75133991e04c4c33f4d9946fda46 1908)
(.fork 0 0x0 53
tree156_174
(.stop 35 0x32ce42091b8e605fc399b2706cdae0fd8fff68183e77bc510222dd31588183b768f3b4d08b4e493a65aa190568eda44ce44e334241e8c864f39970934b9 4534)))
(.fork 0 0x0 72
(.fork 11 0xe408703480fa43ed1b906f033a0d9969420f9 53
tree156_175
(.stop 22 0xd7d17e4da4ce106de37b4756f37577db7b07a034bd3b056a15cef4cd1e2c9ea2f30e2755af399 6891))
(.fork 0 0x0 47
tree156_176
tree156_178)))
(.fork 0 0x0 53
(.fork 8 0x1e14d863674ea33d5cf6e5831d44 70
(.fork 9 0x2b625649e427d4c4c4be530a646222d 59
tree156_179
tree156_181)
(.fork 0 0x0 75
tree156_182
tree156_183))
(.fork 0 0x0 74
(.fork 7 0x4a03902b50adcd846e21fc5 65
tree156_184
tree156_185)
(.fork 0 0x0 32
tree156_192
tree156_196))))

private def tree156_198 : Tree :=
(.fork 8 0x140076329a8cec4251130695218f 66
(.stop 11 0x1fbdd285e7dd9dc6bbd059879cbb4cf8426a229 13035)
(.stop 12 0xd9c0ea0d286189dea973c7299cadd9f97d76de75f1 3751))

private def tree156_199 : Tree :=
(.fork 0 0x0 48
(.stop 11 0x34165aaf3072c5767866e77151e00d984965b7b 3934)
(.stop 27 0x33877c632c99c2f36a9c1b7ab888f3745a799a5d2919b96e2a0f4dc543eb3ac462c44491ad88ab4163fe90946e07563 8126))

private def tree156_200 : Tree :=
(.fork 9 0x463444912fd0587722034e334489cb0 74
(.stop 11 0x32ea49d7545669768c69538503619e8fd2c99b7 3000)
(.stop 7 0x34ba361b846695368c50ef726 6275))

private def tree156_201 : Tree :=
(.fork 11 0xd908342111938659207c82a35ed13044d1b7f 48
(.stop 16 0xd9e1fb8deb5901705b55d3fe926ad059879d0cc780277cd98644db7b 2681)
(.stop 17 0x36784bcf56766c35e03d3dd4cd0a93a16e2a228e144d9d5a796a3669738c 2681))

private def tree156_202 : Tree :=
(.fork 11 0x4711d8c94127b4f4f4959275509d4467533565 56
(.stop 35 0x204fd281cacdeb4f41e3a51d35fa20eeda41262645b36e582190b68f9fb4dc956a56b65c0fd7f478f254ca94337d1324999568e144d895a796a35f5d9a5 13003)
(.fork 0 0x0 63
(.stop 11 0x1d53d2d94d2d7f450d1e3c9532a24cdf44c9266 13206)
(.fork 0 0x0 57
(.stop 20 0x9e7b67757df6905fa38e966c7559692f8501b54b1e33bc76f3b31310530738c3409604 14406)
(.stop 6 0x3d7f563338f85066e768d 13964))))

private def tree156_203 : Tree :=
(.fork 5 0x51d1954a87310d90f 50
(.fork 10 0x18fc7823d50f6e449513f496d9ab68e9a45 67
(.fork 6 0x27849f22ca8ffa5a616a9 42
(.stop 25 0x336a57f960e66ab5e95f7f54f5ac9c1cdc351ad88ab416534569fd0ec9ea2c3cb223648f665091446706df1d 5174)
(.fork 0 0x0 32
tree156_198
(.stop 2 0x9c0b850 14406)))
(.fork 0 0x0 68
(.stop 5 0x354e5a7f69029f0f66 5175)
(.fork 0 0x0 57
(.stop 26 0x66e74a161e5e7dcbb5de7d77d6a36697677706f5f10354b1e140076329a8cec3a9d3a06951c257c9f6905a7dcad 13035)
(.stop 16 0xce1cff8da40f5ed0596ab693730635edc1bd58877336610a449d7567 1280))))
(.fork 0 0x0 60
(.fork 11 0x3b00f048025409602c8543650dd4d15a7d873 42
(.fork 11 0x50a29d0b2235ed42451195f5585dc1b7c75fb7 53
(.stop 14 0xda19f27cdc20f6d058f5e77bf5fb3194d86367586c61d190e 7205)
tree156_199)
(.fork 0 0x0 47
tree156_200
(.stop 19 0x32f7558368c473d43b5cd372683d353a77b74be0fac6bb444912fd058ffa425355d 6252)))
(.fork 0 0x0 75
(.fork 9 0x4a086c3e520a4b222cc1087865e49e 62
(.stop 23 0x336a41eb7263fc986cd7f4ed364419a066ab2f05d319b9da3403d207082a27b49fb2a20a954c05302 3910)
(.stop 19 0x36717ee37266dfdcb3d2d1a53756b41644c96a5691f55d1e18c5133b0d023af7396 4525))
(.fork 0 0x0 65
tree156_201
tree156_202))))

private def tree156_204 : Tree :=
(.fork 0 0x0 56
(.stop 10 0x5d0b8e7706b5f21db8bb8367512b580d7d7 13486)
(.stop 21 0x1ad8dc51fc1e3994bee149440d7b1c1ad2997e272cb68f27ecb102c8cd8f365d56955bb390 13968))

private def tree156_205 : Tree :=
(.fork 11 0x46f19206531e2c93f27a89fb2eecf685f5dfb6 50
(.stop 17 0x37b0a37384583f7848753b5674c296b2e12ca7c33b1f277f0754e44fd4db 9059)
(.stop 18 0xb6d397f7a274a472c1f1cda4033b254cd8044892f3d539fc18da653aa35b8e6 13156))

private def tree156_206 : Tree :=
(.fork 0 0x0 68
(.stop 28 0xdeacc3c6e2b715a84b8e67f063f7da256a5e1206571e08cf538ace30691dd4ece64044086048012209f333dcecb50bda4c 9834)
(.fork 0 0x0 47
(.fork 13 0xc707ec1ff1ffc9533600d97448913f4bcd3105a556ac 56
(.stop 16 0x888f68149674a03fb35e95cf587372c1f1cdedc77b2058bb844ad139 13783)
(.fork 0 0x0 60
(.stop 11 0x33747a3f5dc94eb67a707dfc786638e172c1f1c 5808)
(.stop 9 0x36814c2b69094e38e1644f390193b300 4697)))
(.fork 0 0x0 45
(.fork 10 0xac0c51d8c9ed3b34f4f4959275509d446 72
(.stop 7 0x20fde121273ce4100544ed2f7 14405)
(.stop 2 0x29df55d 13651))
(.fork 0 0x0 54
(.stop 19 0x353d02ac76129b6369e399caada406571e096a5cc0447a193895a33b113b49bd873 7337)
(.stop 27 0x353f94eb84883f78454bdd7e4d59c3e0205909f44ad603e381b7fd2f59b283ee363da282910a5930a5a316b2707f68f 948)))))

private def tree156_207 : Tree :=
(.fork 0 0x0 60
(.stop 21 0x336472c38555847725585db84e399ad66b7b4384c3142d79e1e7ad7e89502c84ba83b3590e 4688)
(.stop 2 0x1e2f439 13057))

private def tree156_208 : Tree :=
(.fork 10 0x1e149592790d863674f573db92704c2942f 57
(.fork 9 0x77c1e249d727a0d02424509e5a7dadc 48
(.stop 2 0xe385611 4725)
(.stop 8 0x72cb7ba5d035e63378d9755bb390 13478))
(.fork 0 0x0 74
(.stop 20 0xcdc9910d2dd74bd27a53aa35b8552070cde363d267cc04653195cc50319542251120fb 8753)
(.fork 0 0x0 62
(.stop 11 0xfe0d2dcd7950b785520709fb3378d8f365d267 14412)
(.fork 0 0x0 63
(.stop 11 0x2a12e3991d6585f7257c9b855254ccf535e5a47 14101)
tree156_207))))

private def tree156_209 : Tree :=
(.fork 0 0x0 69
(.stop 31 0x3673af8f8e6474f8eb88b32de66cf716693b7154964d80448913f5a556ac5d1b38f49d56115aaf56301102b50f983ed16f8eb3446db83 5810)
(.stop 16 0xd2f53a1cbe54cbdc596176bab69038cd12244fd444ce44f4f7c9f399 4409))

private def tree156_210 : Tree :=
(.fork 0 0x0 57
(.fork 13 0x6511df078920949d727a0b1e33bcd02424509e44e169f 48
(.stop 18 0xe398500e145fbddecd13952fb5df2c9f43b192081c422125949d55fb5845a47 6120)
(.fork 0 0x0 33
(.stop 30 0xe3a62c4cb20ea7da41b84e5f111c52f968fd77d4275f277ba5d0dca672b74320848b273d28f644e013a175475f23d759b96e29f26 3764)
(.stop 21 0x39813d0784f51035e63d51911d2b91ccda40bbb4e6939e5ceb5fd254ccf535e4f647c7f554 1878)))
(.fork 0 0x0 63
(.fork 10 0x120c6571e089532580cf535e4d903d91a47 33
(.stop 17 0x1ae7e1552eae399749dee5a547097690585d9b3dc783c23d751cd6e29f26 13803)
(.stop 5 0x34b97097690585f725 5190))
(.fork 0 0x0 59
(.stop 4 0xd58c78b27ed09c 1608)
(.fork 0 0x0 51
(.stop 34 0xd29a192decd8816e29f26e3ae2c8e12e533da20e2a38c4eb3446f3999c1b8e6363cd97499d60364419abd58c9f32caceba3b4d08b429130c50b5440 6579)
tree156_209))))

private def tree156_211 : Tree :=
(.fork 10 0x18dc78525649e43618d9d3d5cf6e4c2942f 44
(.stop 16 0xd7b0d02e155a47d0ed1d84bdd42de39c9503d38f684c417e361f5b7f 5952)
(.fork 0 0x0 48
(.fork 8 0x1920ce642210a449d55fb5845a47 57
(.stop 7 0x1df4d7a16acda4525fe3adadc 13178)
(.stop 7 0x337a5ab3691497f8eb94e35fa 7668))
(.stop 2 0x33b3386 13184)))

private def tree156_212 : Tree :=
(.fork 0 0x0 57
(.fork 9 0x6511df08252c78d023d6d091427969f 48
(.stop 22 0xe1459a5d7a13a9deddb84e39913f4bcd6ac79fb69114406483399088429125949d56115aada47 1115)
(.fork 0 0x0 50
(.stop 12 0xcdf0ebae39d743d7999b97c9b5591e08bb22f18f54 2840)
(.stop 17 0x37ae6e138e600478e72caf5fd254f5593624ea644ad13950ed7d7642f38c 4563)))
(.fork 0 0x0 63
(.fork 9 0x3e0120c6571e0878f254ccf54c0da47 54
(.stop 2 0xda4126f 3308)
(.stop 22 0xd2728d4d2c1ae4e3adb7fdc99f26d781d5b8b2354e585db84da40b182e7ceba422d2f751032f6 9212))
(.fork 0 0x0 72
(.stop 41 0x34b19e7b2c9a5cea0dcb322c9cde9883d4f5e7de3ad6115d174a086433012c9cd80386ce3344fd2f3557d57857e9695ce44f4f5f8df279c1b3990fa43ed1e2d2f761fdf287f0e66c 6734)
(.fork 0 0x0 68
(.stop 4 0xce644881965093 68)
(.stop 36 0x585f8e62ecb36e77d370d44e78eb94d32ce4bcd5fa5a5768a61cdc0970573012a315605f8df277f0a706ce6464827389df3399088496527557ed6115aaf563 14417)))))

private def tree156_213 : Tree :=
(.fork 11 0x19a57c8797d140877727d0b2c3fc569a5a9de79 74
(.stop 26 0xe38daeee5f1ad07a038eb6e29e8fd7813a95a3f543a37336892538e766a6231e39927350a56b083ee49d94e28da 3462)
(.stop 9 0x1c25e39d1cadc494bee148f543dbb4c2 13968))

private def tree156_214 : Tree :=
(.fork 0 0x0 50
(.stop 23 0x36817c9771918eb97d75074b4141c58f2eecf495fa36904e8169fd58878222e8f543db913f49cd7dd 2846)
(.fork 0 0x0 56
(.stop 18 0xded1cb0d0c1275dc64a79d588b1e3ff9616620f4c2146076e1decd9d427d9a5 507)
(.fork 0 0x0 60
(.stop 23 0x38e68da73708fff53e8d66a0de5f5f21d2c961272c35587c9e706da149602768b2147291cf534569f 2809)
(.stop 15 0x37ad69536779c2f5434ea5913691f3940ad42b75a456b083ef396 7343))))

private def tree156_215 : Tree :=
(.fork 10 0x120095025809da2c84f67534569f61cdf1c 74
(.stop 33 0x13aae6062cedc656ae6e2797d8af7712927b7b98da649dd290d00389ce3455b17d77edb3954bdd7e47f0f3050adcb23315cc6549cd6915ac2538 13046)
(.fork 0 0x0 62
(.fork 16 0xa6c51516749d336197d1641d90ed3149ed2c4139b4e7560366adde8 34
(.stop 7 0x38e68da736a927b3072c6907a 6274)
(.stop 7 0x34a486638e08fd32e1924797d 7801))
(.stop 2 0x3dbb4d1 13518)))

private def tree156_216 : Tree :=
(.fork 0 0x0 50
(.stop 15 0x36905f93562400b3001dec9f42a3b4cd0f4c7823db913f49cd9ab 5031)
(.fork 0 0x0 75
(.fork 10 0x12821b087094f421d2ef4c3d5f6585a197 62
(.fork 7 0x3e627b4a882a54ecb580dde8 53
(.stop 17 0x35ec5d33726509384c88cb8eb11544f9d5080ab1d84a6d8da784b3d5cff2 5951)
(.stop 15 0x22c0e5f1f14d292054da41c25decced3422d910ce54cdf5d334c5 13468))
(.fork 0 0x0 69
(.stop 17 0x355872ff84b49872ff5a9797d94e68d5dc58d02d2f9617620b8e63d359b2 5166)
(.stop 5 0x330650bf4cd340b4ca 1447)))
(.fork 11 0x2b03140c71d8c9ed3d3d25649d5427511b565 74
(.stop 19 0x336a94cb8e981823fcd5386513ac942f693330503902b52a2513d55756b083ee538 7515)
(.fork 0 0x0 69
(.stop 19 0xbbbda41740d9dccefd54df2cd2d1d53d2f8ed34bdd4dad50c77b27d0e1966c9def 13821)
(.stop 25 0x38e664377ad7f1f37e3ab797d79e74b436259b96e2b72544c96a55d0343950bdca972ab4cd3408ed344ef4ca 3003)))))

private def tree156_217 : Tree :=
(.fork 12 0xfa464e1964777207c82a2cb0d7b3b2169a5a9db7f 38
(.fork 9 0x3ce20108122c78ffe5a316b2620df21 56
(.stop 24 0xd4e07f2e5f666edec1902deb99b9d9e0e0cdeb512783ef4335cf771929e50a344fd2f3ce2cd9d5f5dc0d 3306)
(.stop 6 0xce2d13f49ab97d5f3b68c 3950))
(.fork 0 0x0 53
(.stop 18 0x46c769338977b63140c65449d13249a97e6d2ca0fbd308785274cd863674f6e 14253)
(.fork 0 0x0 45
(.fork 4 0xf5476344f5275 67
(.stop 5 0x354f1e089e1d308cf9 3299)
(.stop 19 0x1fbdd9c6840dc9e226e39913f4bcf84b0c4c931669797d44cb55e5a7d9a9779b690 13506))
(.fork 4 0x18d8cea472b722 47
(.stop 6 0x8b3b8e7583635fd30913f 14113)
(.stop 8 0xda41c25dc85125e399259640b2ed 5801)))))

private def tree156_218 : Tree :=
(.fork 7 0x6362c84cdf49c54be5acb4c1 62
(.stop 15 0x35545325ae1e399882e5f59a5da1851e1e38d855d3356566adf1e 3465)
(.stop 2 0x532f722 13517))

private def tree156_219 : Tree :=
(.fork 0 0x0 53
(.fork 9 0x3300d0785274cd863674f573db942f 74
(.stop 7 0x3686086cd853673565319513d 1612)
(.fork 13 0x2a4143051516985b020709ed27ed2675f4586b61d74ca 63
(.stop 4 0xe13cb21d7b1740 4402)
(.stop 15 0x3855426f8e6814b5656e2797d7c7b54377db68d2748a6d620f693 1906)))
(.fork 0 0x0 57
(.fork 10 0xa7c2a41944b1e33bcd02367169f6dc9b77 45
(.stop 40 0xdeddcadcb20f41e38e1989e735df7547727669797d7eeb5590cccfe457c97e8da40cf94c1960d8d7f5fd0f5476318d88973350cea3f6cff66e29d5b7f0f71249592755119fb4 3144)
(.stop 8 0xda416a97097721449756533ab722 1423))
(.fork 0 0x0 74
(.stop 19 0x1d53dc885a6706f68c24dce373b4d2f7ce4d0a3ce642b70fac64c33a8d0044f525b 13061)
(.fork 0 0x0 45
(.stop 23 0x2707e15513f5d0f67846ca7a2dc49fc399b355e1e3c8123174cf9532d5ff58374cd27b4f4f4959275 14411)
tree156_218))))

private def tree156_220 : Tree :=
(.fork 8 0x1280e40add25b50894446206538 63
(.stop 4 0xd594c57e398d79 2697)
(.stop 21 0x34b95f9b8eb422d1d8cbd9873d5954467a0f68c620f5546b8730575478e62eed09c5f5f399 5021))

private def tree156_221 : Tree :=
(.fork 0 0x0 62
(.stop 32 0xe3ad9b9da19df67f1f36897538e64c31910ce4d3aa5091617706de83da317e7865e49ece64cdf52f94e17c7b4c127b49fb3378cf4580d9ab 2513)
(.fork 8 0xac85b43d28f64532dc1b75474cd 59
(.stop 14 0x620f84b5a4f5673175275dc6512544fd7436de768d47251d0 13950)
(.stop 9 0x36778d7f7225acb4c1476768c5f9f399 4389)))

private def tree156_222 : Tree :=
(.fork 4 0x3b215585ca5cb7 57
(.fork 8 0x19449d727a0b1e33bcd0244e169f 62
(.stop 3 0x35652a559ab 2541)
(.fork 0 0x0 66
(.fork 10 0xac851014645b41e14f4a3d912fd4c19c1b 33
(.stop 14 0x79fb7127f0f4322eef6901d8f5654495ae5d9dc313e5f618e 13356)
(.stop 6 0x8b3b6775a4f7227f0f559 13642))
(.stop 15 0x36775119693dc89fc3cc19f27da40bbb5f5f3021e08f6e44974ca 4694)))
(.fork 0 0x0 53
(.fork 8 0x1e149d33618d9d3d5cf6e49c142f 63
(.fork 9 0x9532580cdf35e4d9044c97365d01a47 62
(.stop 19 0x337099c367166d666cd7b16a5e5f586a64437bf27ec0c2227f85533791cc47357d1 8751)
(.stop 12 0xd4fe670d9c59b599b38e600980c2e12dc0f72ab392 3308))
(.fork 11 0x283161458f18a86351b44ebd66d5c2577db686 62
(.stop 26 0x866397c9753715647784c4c4155ce1212eee5f41e930c0fedd50de83da4d7e76e2649ed5949ed27ed2674e757d1 13168)
(.stop 16 0xe3ad446dc79422e39a53acdc0f5ecc005b73acd11b4e51b8388b3305 4062)))
(.fork 0 0x0 69
(.fork 7 0x2b50f983ed16dc5be3641def 68
(.stop 19 0x34b75aaf5f851194e0ce3d7308ff3678709605bda411d3cbfc48012208142a38a8f 6740)
(.stop 21 0x3715814aa12e39858fd9e1612e5f54d17057565421d13f4bcd730ce3d0a449652755a5b563 4062))
(.fork 0 0x0 74
tree156_220
tree156_221))))

private def tree156_223 : Tree :=
(.fork 10 0x191476327b4ce333e4f4f49d54465ab99b0 57
(.stop 7 0x1d53d2d0eb3d328d0249b169f 13194)
(.stop 15 0x14e1d2d143ee145b8ad798f5e7a29f25d338ebdda34022165768c 14109))

private def tree156_224 : Tree :=
(.fork 0 0x0 75
(.fork 9 0x21b11fc4871e1878e36290876209b89 53
(.stop 12 0xcbb94bee398a6d620f68c706f4ce77bf6863675008 3320)
(.fork 0 0x0 69
(.stop 11 0x37ba4c1d8837a2b5df52fa496973a976e399f25 7663)
(.stop 17 0x10a4ce32052e399deddea9c1cd2f59b9da345b44b99ae583cf4c66e07719 13051)))
(.stop 20 0xdef1ded8da78e69c1b6864e774ce1e149d32c68d9d3d5f4c12c84f5e426d69f61cf565 5650))

private def tree156_225 : Tree :=
(.fork 0 0x0 65
(.stop 12 0xded1d5bd7bd5fe7a1b67e22ac8ba277cd9250edb7f 5955)
(.stop 5 0x34ad77b7721535f4cd 5810))

private def tree156_226 : Tree :=
(.fork 0 0x0 54
(.stop 19 0x38e7532b4cd77bf678337cf4b5acb725511b5651e189f63408d703af4ed350f5873 3927)
(.fork 10 0x10c0df0fb45b73acd6ab77be0f6a0eb4ca 60
(.fork 6 0xf745132c85094426d69f 47
(.stop 17 0x397d86477ab865e667d281f18d7594246e074be77b6369e39986661e9cb0 3433)
(.stop 20 0xd282360d795fc7dee6c7de399dedd2e9b8a83d372551199b0ce1d41db46797d6697429 2672))
(.stop 24 0x816f542756f8e772b2360cda25d4d595446d2f9ded8da78e63a991c6474d2fc50768d5b46797d6697396 13172)))

private def tree156_227 : Tree :=
(.fork 2 0xfaf425 34
(.fork 3 0x11326bbe059 50
(.fork 9 0x46625189e12ca8f6e44956985aa59ab 45
(.stop 3 0x38465ab999a 1891)
(.stop 3 0x34cd340b719 1614))
(.fork 0 0x0 65
(.fork 17 0xbe2c78fe35ac988377b74c201040dd0fa464e196481f364909649aa18d 56
(.stop 14 0x77db7195cf74336e178e96209e86ce2c50f1914a703624d9d 13962)
(.stop 5 0x353e6bab8e69c1b693 7665))
(.fork 0 0x0 45
tree156_223
tree156_224)))
(.fork 5 0x31f1aed26788ab41c 50
(.fork 10 0x1e089e127c8b2a3db912544fd60f5a616a9 45
(.stop 10 0xd529883d9dd005e140763338d25649d5446 4074)
(.fork 0 0x0 57
(.stop 20 0xd9dd397d77e18fe119c1bd7c5b797c874a15ac988377b77213408f413d6d69f7299cad 2666)
tree156_225))
(.fork 0 0x0 65
(.stop 35 0x353a57cb97f13bf4a47a320f488a368a8af6359999797d7c86223d2f8a9133acf57cbd8e333d3df27da311cf4c0d69fce3064e196481f277cd9250edb7f 7661)
(.fork 0 0x0 66
(.stop 37 0x3729a0eb2ca79f753b729f8e7927e670d9e1c2572fe18f88a78514e5d3a157c6c7db46797d66972fd1e3c47f121c5191488ceb694e49ed594cf944bd4d7706e2c4 5646)
tree156_226))))

private def tree156_228 : Tree :=
(.fork 0 0x0 70
(.fork 5 0x2b6148d3937a2e7a0 43
(.fork 6 0x1b1cd934e2955b55f18fd 57
(.fork 10 0xf4c6511df07892094b1e3409091427969f 48
(.stop 8 0x6e138e679fb691192125949d5611 13953)
tree156_204)
(.fork 0 0x0 59
tree156_205
tree156_206))
(.fork 0 0x0 40
(.fork 4 0x3b211b65ca5ae9 53
tree156_208
tree156_210)
(.fork 4 0xc7c6bb499f41f 53
tree156_211
tree156_212)))
(.fork 0 0x0 43
(.fork 6 0x1b1cd93385d38a556d57c 65
(.fork 9 0x3e9193881f20a8ce133dcd7b6dfdc1a 52
tree156_213
tree156_214)
(.fork 0 0x0 60
tree156_215
tree156_216))
(.fork 0 0x0 52
(.fork 3 0x9f43fc5e79 65
tree156_217
tree156_219)
(.fork 0 0x0 40
tree156_222
tree156_227))))

private def tree156_229 : Tree :=
(.fork 0 0x0 64
(.fork 6 0xd306e81bd08b92314ffd 53
(.fork 11 0x64219347852cb4d863674f573db969b5a99d44 65
(.fork 12 0xfc34119386591b7481f20a8ec83d88f63580160c 47
(.stop 25 0x336a83f767094eb8e67c6b4be1dc9cb0779b8e75d21ad0d7ed3a069522c3d7a09ef29e4cfb448931066b9a48 7652)
tree156_137)
(.fork 0 0x0 60
tree156_138
tree156_139))
(.fork 0 0x0 74
(.fork 7 0x4a03902b516c85bc27bc9f9 65
(.stop 32 0xd50dcc0e3992735ac1cb4ce1574b72d75584c11cafda45b8adc89f2adc852754ea590266b756700fc0401460659207c82a2578ec83d88f63 7670)
tree156_140)
(.fork 0 0x0 60
tree156_141
tree156_145)))
(.fork 0 0x0 37
(.fork 3 0xc555d3591e 60
(.fork 10 0x12009502580b212cc4d76363513553462be 74
tree156_146
tree156_153)
(.fork 0 0x0 50
tree156_160
tree156_171))
(.fork 0 0x0 28
(.fork 4 0x388139c7301e91 67
tree156_173
tree156_197)
(.fork 5 0x11bf5cee23390137bb 61
tree156_203
tree156_228))))

private def tree156_230 : Tree :=
(.fork 8 0x118c933444974761fdf2881720f6 44
(.stop 5 0x37164949a4edc95749 3918)
(.stop 20 0xa5c3981693b7169c1f2cc66978eb1ffdcb7d4f19b56e0e0edce09cb994da66a9c137b4 13156))

private def tree156_231 : Tree :=
(.fork 0 0x0 28
(.stop 19 0x35d5618770e63fb8eb317b8ea4949a4edc5428c141858e493dc1f72e768183e622d 3763)
(.fork 0 0x0 46
(.fork 7 0xc5e35fcd963d4172f5f297e1 33
(.stop 6 0xd2919a5d76c7ff5d25fc0 969)
(.fork 0 0x0 27
(.stop 4 0xe3ad739da05aeb 6423)
(.stop 21 0x398046db2c8862340372e754a3d390845cb5863e3ad739a35a970dc35861dc95a4e88bf2e1 3763)))
(.stop 12 0xda05cb9e3899a5e3adb8372df41c1ffceb3a0eb7bb 5945)))

private def tree156_232 : Tree :=
(.fork 0 0x0 63
(.fork 6 0x2efccf533f0d903659132 50
(.stop 29 0x34a7645f7b488b35d98d8f54d708770d61a58778d7741f1dd4b172c6124958416acda40b2a2ec8bc64e453a7531d4db55d5911 3763)
(.stop 4 0xda409572c632fa 1755))
(.stop 17 0x370d3a85a4e8ff767c3d20f62da44a7d4bdd30c50b72fb2c94c6133ef2fc 1897))

private def tree156_233 : Tree :=
(.fork 12 0xa949e42cb51c347592f94c2956555c97365d01d44 44
(.stop 28 0xcb422c4d76d693d27622ddeecbaecb587562bfb7ae0a186c830ed2495362229defd7438b238e53d390845cb574961f5cb3 2506)
(.stop 32 0xcd9a3fecd9c7635a4da4ad06001f054a2298fdf8e2583222d92578555aa605e8feb5504e9d4c7536d7335d0f38c5d1df2881722c4924b852 2820))

private def tree156_234 : Tree :=
(.fork 0 0x0 50
(.stop 28 0x7ef78e21d8f7bb5d1e492e14987d864b5d9707f85511d8ce84e44b252f04c4833e4eb43fa97c9ce253a7536d7335d0d911 13488)
(.stop 18 0xd2a6a0ee5f9e86ce247707a35fc188a741a3ff92fed0b08183b0526b50e72fa 9830))

private def tree156_235 : Tree :=
(.fork 13 0x11cd49a57497c9b4bd00fc1780d18b252cb4c613ff5097 50
(.stop 15 0x36815d1f6905ab38558b237b42ec8ce81b3b7b04e453a76411911 3456)
(.stop 6 0xda0542dcbe8943360342c 1910))

private def tree156_236 : Tree :=
(.fork 0 0x0 51
(.fork 11 0x6db255cb183138c634bdd30c50b544061a9876 44
(.fork 9 0x3cd2060b113d390845cb574961f5cb3 46
(.stop 25 0x368329932d042091b8e604201272f53d4c0340755859acdc55911692666acdddaeb707e055cb956135cbd747 203)
(.stop 17 0x336494d32d577c2226e3a92f958317365d01d4479e1e7ada4130088b77bb 9216))
(.stop 8 0xdee5cbcd2c0c4c3608d9966b355f 5952))
(.fork 9 0x6e22774e1a3d415f9584d7476df7561 44
(.fork 6 0xb00c62c44f4e5cb5749 38
(.stop 6 0x94b79813ff92ea4c29442 14093)
(.stop 15 0x370e360b70d94b79812718c32d764ec846d9f1fda44d805d03681 2994))
(.fork 5 0xc4c3609442667b564 24
(.fork 4 0x360174061e1b84 62
(.stop 7 0x38456185e83e60494268e5a46 3141)
(.stop 8 0xd081e8de115f1fda3d7e294b77b9 6417))
(.stop 13 0x336e94db85242091b8e6042012f04fea5f257e27063681 7821))))

private def tree156_237 : Tree :=
(.fork 6 0x1043482c9ccf833e4d93 50
(.stop 35 0x354b72df8e5925772046cb364a83b8ea999e973e5fdf2881722c4dc6d1c34be530a5361d44cbf4ec14e0143d77c9f26863b5ef4e9d4c7536d6985aa5743 8281)
(.stop 2 0x204f5fb 13356))

private def tree156_238 : Tree :=
(.fork 11 0x5012044a6b2c60c4e318d2f750b54405cd1742 38
(.stop 22 0xcb4218dd5694cdcb50c3e72f20f2dee5b73e15205cdc8da50dc60757334d72fd4fdaeb707df21 4067)
(.stop 7 0x1613dee560c69437187ca368f 13968))

private def tree156_239 : Tree :=
(.fork 0 0x0 56
(.stop 16 0xe38d1b8dc601596941e86d2ed6137ecf2f30a44a703d8930ada3d43b 1884)
(.stop 3 0x35fb44c7564 3939))

private def tree156_240 : Tree :=
(.fork 7 0x2ac0f88a8b2a48bc12f18ec8 52
(.fork 11 0x5b01ddc78429f8bb449752714e4d3a55a696a7 51
(.stop 15 0x37ab94bf8553d8b55a25156115d25f26d9f0b2b313942d5cd1742 5644)
(.stop 24 0xdead600e394c61e149cbcd2ed91894bf84c644dc1f90037ad2058ff54e8543b70375fb5d25f2688a35e9 952))
(.fork 0 0x0 66
(.fork 8 0x1002121bd49f12cacd9338b4e2e 53
(.fork 10 0x2790b1a470d2f94c2956555c96005831d44 44
(.stop 30 0xcb22700cd9636592677ae88be36399974aa72eb7bb5d1e2c48d7b9808b0f7b67a1b5f544ae2c8972b8e53d3972d5d2586361f5b7f 9214)
(.stop 13 0x397e57e5a36cbc15fb8d8f8459c078527a1b72850ef5fa 5025))
(.stop 17 0x38487a2f9808b0f7bf4e5e8d8deb93a150ef2fc4e19a506e11dec7a1b38b 7039))
(.fork 0 0x0 33
(.fork 6 0x25156115d25df27c9a228 51
tree156_238
tree156_239)
(.stop 25 0x20efd7a5d55e38d863dc6d74e7cb77b60c986c22058a7050ef2f95d09a4e88bf68a3d8930a5109aeb707f691 14099))))

private def tree156_241 : Tree :=
(.fork 3 0x34e120b39d 51
(.fork 10 0x1e0cb183138f553dbcff04bdd30c50b5440 60
(.fork 8 0x1b909eb3634d993b0cecd68eda44 31
(.stop 11 0x355a69574b5693b7b92500ebc6941d5cdeed747 3463)
(.stop 5 0x3681778398088b75db 5152))
(.stop 14 0xdc6d9a7da45311da40ebcdca08182c7cbba3b04ecf3fdf301 4703))
(.fork 11 0x9e42c68b2d38e4ebc3b511d64be530a7513397 56
(.fork 8 0x5a894c401512b44e59a56dcdb76 31
(.stop 25 0x1cb0cb39b7a778b7255d25e81ce0912399b37bb6e1a22fdc391125345739641d90ecc04ff75d1db8b709a05c 13969)
(.stop 15 0xd99dc422cfe6018fdaaa78455d275e96e1368146f5258557f68f 13658))
(.fork 0 0x0 44
(.stop 12 0xd78dadfd7d56b3da45276d598d99cc048184eb1749 1899)
(.stop 6 0xdc4138cd7e90a54493564 3789))))

private def tree156_242 : Tree :=
(.fork 6 0x1180e003886551e2478b 69
(.fork 6 0x5e8489209895925689f4 60
(.fork 11 0x2ac144c5ae1b90d8d3664ec33b34f5e3d9d4d1 47
(.fork 11 0xcfb3600d973ad955f55e16955ab17305d19cb0 31
tree156_230
tree156_231)
(.stop 3 0x3389474f2f7 4409))
(.fork 0 0x0 56
(.fork 13 0x3e011f077b205894c2570ff5401512b44e51c6474d9a5 47
(.stop 25 0x368172e736b5825c17dee60f98b1f9801ffd7497f0341e00b829e1680d7f57e56135cbd747da416ac5d19f18 3456)
(.stop 12 0xd2bddefdc8dc1fda3d747da41610ce2ca7d5d2768a 5651))
(.fork 0 0x0 62
(.stop 20 0xd534d7ddc8df23da41c17816e22fdc4db8494cf688364130c6e0f68f365ce2a38c5267 6888)
tree156_232)))
(.fork 0 0x0 63
(.fork 8 0xf803e71458bbf2f20cf533f1132 66
(.fork 7 0x2120d209f12c9cb2b3d84f64 53
tree156_233
tree156_234)
(.fork 0 0x0 64
tree156_235
tree156_236))
(.fork 0 0x0 67
(.fork 8 0x5e02ae0acc9572570a8d2a40c5e 66
tree156_237
(.stop 3 0x355c2a03566 1913))
(.fork 0 0x0 65
tree156_240
tree156_241))))

private def tree156_243 : Tree :=
(.fork 12 0x11dc80327ccb182cacbb34e493a650b54406b59ade 42
(.stop 16 0xcdb5e837ee75ee6bab69049c1ae9d2f0ecd3d3f7ba316911d64659b3 2829)
(.stop 15 0x398166d38e66bab4ae5f8b8e07c7f5676442705e38d2706ba7386 1589))

private def tree156_244 : Tree :=
(.fork 0 0x0 49
(.stop 27 0x32d49c1b8e67f073707071e888b178eb5f377a877bb5fb03041fd29cccf546dd9b4693b68b339ccfd53194dc5585c14 9834)
(.stop 26 0xe5fdaeacb817e2dee990e7c734b864638ea0a406372764c5a447591966cf38627909f529fd2704be530a668b2f6 3764))

private def tree156_245 : Tree :=
(.fork 10 0xab064935d8e2838ccec33b3513553462be 68
(.stop 29 0x336c9c172ca99bb7ba77b5fc181778e6646338b426d1b35f317df7a2339133f156057ed7315d15c15cbdc9f327d50014939dee 9521)
(.fork 0 0x0 38
(.stop 22 0xe5fcf4edea2838d78e193e39a052dc543eb425109b44657cc5f7ddedce44cfc58472f74c293a6 7196)
(.stop 31 0x38ea77c6059d2b8eb1e39a193e5fe2c8cd9a360e129a4e7072052d081094426e22ace44c65694b5fa2ecd2674c0d7475f8dfc28173688 4692)))

private def tree156_246 : Tree :=
(.fork 0 0x0 53
(.fork 9 0x46914549e427d4a7f2a452704be530a 63
(.fork 7 0x213169c6573168cfc44ca0f0 44
(.stop 14 0x6df78ea8b2770e61a9600dc31e78dc916ac6b49ae2da3d7e3 13953)
(.stop 4 0x5d1f6817f074bc 13200))
(.fork 4 0x1b7481158332fe 48
(.stop 9 0x463e399cb5defd6acda456116409913 13953)
(.stop 7 0x38e68d7b6817f074bc585742d 6428)))
(.fork 0 0x0 62
(.stop 26 0xdea222ee3a45014735f26dc55b85da209dc36116a866d38e650b54406415910cbe4cfd363cd973b15099499e18a 2028)
(.stop 34 0xe39a22dd9f59acdc787f8dc325c8e605fbc8b235da5cb97c95f89c18da049f32c60bb34e493a650b5440cbe8213195cc5a33d4cfc3d8513283c32fc 1755)))

private def tree156_247 : Tree :=
(.fork 11 0x3e036021211e851533d0d8f365d13144cd267 45
(.stop 11 0x35db5d076832c48d9538c8ece5cbdae3da41748 5941)
(.stop 17 0x34bd644f4af77975dd61ef6756b8dc17da409443398d98558199d66b742d 3473))

private def tree156_248 : Tree :=
(.fork 5 0x598252930a707f5f4 45
(.stop 24 0x5cbf8ea6e1397f41f32e166cdd4fdc595fa5849a48d9f13935cd72fb3370e1481720f8a35f6805f89b7e 13787)
(.stop 21 0x368a5a57369817768081735db7a2f8eb2c3b4b964659b3753dfb7e11dc15888f2fb4c2f5fb 4689))

private def tree156_249 : Tree :=
(.fork 0 0x0 65
(.stop 13 0x32ea33d50974261132d7ec1792c98bc12f18ec83d88f63 3162)
(.fork 0 0x0 48
(.fork 13 0x6482510a8c3398cfc3604d98558157757ed61166759ad 68
(.stop 26 0x61ef84d6e133785f837b30525601817770d7c577266b9dcbbe3ad25e49c130a50bd43e5a6f4bd3644d955cc5745 13789)
(.fork 0 0x0 50
(.stop 3 0x368050b1877 2994)
tree156_248))
(.fork 0 0x0 41
(.fork 10 0x33d4d7a3644ec944711b747559b46939dea 38
(.stop 28 0xd59d2f8cb59b84e151747d76de85d9f0ec24739df17a2e227e3acb0e3370e2838cd26549a54d1d0b57e281760f7da1dc1f 4874)
(.stop 30 0xcb49a45dc591ce641b5db5cbd747e134a654bff84c94d36875f8b7b34be130b4e4d7355d0755d0cd46421b449e449792f95a6f55e 5164))
(.stop 36 0xcb5e535cda5385707f7aa444a05cd76d4d1641d90ed0b46d2338111d64659b3d57543e55c96a6ce457e281760f7da38a7e3b09132473961277c5e8b889f692 9369))))

private def tree156_250 : Tree :=
(.fork 0 0x0 52
(.fork 3 0x3ce29f913d 24
(.stop 4 0xe399b7dd550b10 3170)
(.stop 4 0x7c5371483e354b 14092))
(.stop 2 0x165b683 13500))

private def tree156_251 : Tree :=
(.fork 10 0x2c98c5e3868e323ad4ece5a516ad5cbd747 62
(.fork 8 0x84847a145494233d0cfd363cd97 45
(.fork 8 0xb09dc3ad0ecd3d3d72e5d21cb2 48
(.stop 2 0xe399ae1 202)
(.fork 0 0x0 68
(.stop 16 0xcdb23648ffb5db57f78e653279807c922c0dc9c9f33390ecb61ed916 2514)
tree156_250))
(.fork 0 0x0 41
(.stop 8 0x4e4f69127cd3a6ce44cf54471a4e 13948)
(.stop 21 0x35db8b2767c5583855708f8e0449d3937c5369127ccd8447613a650b73892c8d086530f4bd 3457)))
(.fork 0 0x0 63
(.fork 7 0x6573168c6233d4cfc44c9b7d 49
(.stop 3 0x367d55859ac 3303)
(.fork 0 0x0 66
(.stop 4 0xd2f402cda48b2b 2705)
(.stop 24 0xa35f2cd8d937158d8767a4c2973675134bd3ad12f89c1767d00680b4299a193e398b9a6baa2c98d8f726 13003)))
(.fork 0 0x0 60
(.stop 23 0x37bc07e9919d54da4fda28a8cd59d30bd7d429940051d5693b4bd0f585ae192480c2068e2838ccecd 2984)
(.stop 34 0xe141fc1e39a3facb6e22dd76d9b1da397e2ce45576da11df081634af61ef55e2a302021b7894a47111d549bd4cbcbf4a912c9cb2b2eb8d9366bf2ff 5645))))

private def tree156_252 : Tree :=
(.fork 0 0x0 63
(.fork 6 0x195cc5a3188cfc44c9740 51
(.stop 17 0x35535a5740672ab8ea5d2340c8d937257a3367d00680b66bab71e4e4986a 4856)
(.stop 6 0x7c9b726006b71f7c9f724 14110))
(.stop 19 0x37ba64659b3cbadaead7b9f27d76cbb368ef5fa16b89403194e333b354d1643b301 6259))

private def tree156_253 : Tree :=
(.fork 0 0x0 48
(.stop 36 0xcb4a49ad02d919e3a4d80d00d39250b5440e5fda4f861f41f44f555d55e9fc5a0ff6904baf5db202cec23da1606cc04a8c2e70bb03398cfc360556055dd611 8908)
(.fork 0 0x0 51
(.stop 5 0x35631b6d30bda40d84 2547)
(.fork 6 0x24c0f4e3da0fe95f8f68e 63
(.stop 15 0x35db973f2d3926b2d17f176906e12499dc71a4f88bb68444c9c18 9214)
(.stop 10 0x4713724693f7176e236904c2f56331772ff 13053))))

private def tree156_254 : Tree :=
(.fork 7 0x1790ab0b2c2f18ec8499252f 51
(.fork 10 0x2c60bb335b4d844e9942d51016a85cd1742 54
(.stop 20 0x8fff67a926a534d05cb086df384a9c1b84d64175e2365143057fb69049bd571703dde0 13003)
(.stop 22 0x6e132ea646740864435ee61aa0f2cb2d5fb5f31913d2f0d9457f98668fef41f5849695667368f 13953))
(.stop 9 0x37b7364943dda410075ab338949bf2f9 4548))

private def tree156_255 : Tree :=
(.fork 0 0x0 33
(.fork 6 0xa30b193d756117a31f26 51
(.fork 8 0x14049f32c60bb3361142d51016a8 67
(.stop 7 0x1ae9e3a4d80926768150f55fe 13967)
(.fork 0 0x0 62
(.stop 14 0xdec5a4fd07de8bd756a0de3a54d168ef690363cd974735905 6259)
(.stop 13 0x38e988bb67d7a2f5db5345a3bda41b84926767a61ab563 3635)))
(.fork 0 0x0 47
(.stop 16 0x693f6769c1b5db5a9756350f5c0fcbe81645f8f692365ce3358497e0 13343)
(.stop 11 0x38e388bb6841180b115f8f69244c91af473738d 6579)))
(.stop 12 0xe3a900757e96ac5f8338d194c6573611b887f174bd 3456))

private def tree156_256 : Tree :=
(.fork 0 0x0 48
(.stop 22 0xd9e6535e141c1fd7a1c1cd2f4a91706f2fe2e9d09bd7ecbc433989df5f8e05cd070d985581611 2682)
(.fork 0 0x0 44
(.stop 9 0x32f74979606d0594d1d0b42add0717e3 3635)
(.fork 0 0x0 53
(.stop 4 0xd7b9aead7ed42f 4874)
(.stop 4 0x706f42d38cf2f6 13196))))

private def tree156_257 : Tree :=
(.fork 6 0x37817905f09f32ca542f 48
(.stop 30 0xdc5942ccdba22ecb7d87ed07c1fc3d397e366c78eb386f3912e9d11a6e11cb8da410016939b82d2f4d98558157757ed6115d15a47 6579)
(.fork 0 0x0 41
(.stop 4 0x38af69040051d5 13357)
(.stop 14 0xdc91f24dc51b84da40ff9d2f49db693e3fcda10e183da3692 4072)))

private def tree156_258 : Tree :=
(.fork 0 0x0 51
(.stop 9 0x1c0fda44f68d2f190e66a9f26e15542d 14411)
(.fork 0 0x0 44
(.stop 12 0x703f8e2888b72761fb2e26ba9b84d7bdf26e154fe9 14411)
(.stop 13 0x156bdc51b84d7bdf26e132534da1cbb250b35ee693b692 13500)))

private def tree156_259 : Tree :=
(.fork 0 0x0 63
(.fork 5 0x6573168c6233d5a47 27
(.fork 3 0x457339da4f 44
(.stop 17 0x370caaa38ea364d4cb6b95decdc79aea6e11fbae3989db3d38f683fa5b7f 4688)
(.fork 0 0x0 36
(.stop 2 0xda49440 4092)
(.stop 5 0x36924e9b38661cf4bc 4094)))
(.stop 23 0x1863e382363d2792667021c16d9e93a650b5876defc6e31ffc9432c9cd80386ce3357e9ad26b8b553 13939))
(.fork 0 0x0 47
(.fork 8 0x1b8c7ff2c9cd80386ce3357e9695 61
(.stop 29 0x37bf66cf6847ee32c8a35b6735f8d8636dfdde7e3858fddc90a7f497986c61d1ca9da4126f703f42d16bc5b9310cd8e3661c08 6725)
(.fork 6 0x2f18d7b3b219ae6dff301 48
(.stop 14 0x49bf682706b8514c29f21d7b9a4edefd7348d92538e3ad5fb 13052)
(.stop 18 0x81332fc4c2b97e6ba9e86d7a4ce1618b71c75437bf5cd22c894e38eb815f4bc 14560)))
(.fork 6 0x35ed11d64659b3706f55d 48
(.stop 14 0xd2e53a9d7b80c207f05a449c368a61cf3011920ce63661611 4878)
(.fork 8 0x18dc9e429fd25e49c12f94c2b567 74
(.stop 12 0x4e236923fa542de155f26cb8987ed05908d4c3a0fb 14412)
tree156_258))))

private def tree156_260 : Tree :=
(.fork 0 0x0 28
(.fork 6 0x313139c64619b4864e22d 53
(.fork 11 0x51527909f529fca9149792704be530a5831d44 67
(.stop 28 0xd0b57cccb32705decd87dcbad9b388ba2c8925b7b136019b08ffe499e3a99a266a32fe084c3dd204c82127d94ca53623fb 1143)
(.fork 0 0x0 59
(.stop 30 0xcb997e2cbb49d9dc36499cd922c8d9f52f84c2da3c79e741f2ecd39250b5ad66b79e7879eb69219206531b8cec23d74f6866899a8 5960)
tree156_252))
(.fork 0 0x0 45
(.fork 9 0x9cb2770bc13ad0ecd3d3d72e5d217e2 67
(.stop 24 0xd2f1440da39577e38a361dc549d93ac5b81e144f5d3da1606cbf82130fac9f227d8a90338ccf966699b0 4689)
tree156_253)
(.fork 0 0x0 65
tree156_254
tree156_255)))
(.fork 7 0xf4f4e4de8b7c9e7069e837bb 62
(.fork 6 0x11e851533f4d8f365d9ab 48
(.stop 2 0xe399ae1 3480)
(.stop 3 0x38e650b72f6 1455))
(.fork 0 0x0 67
(.fork 7 0x2130fac9f227d8a8d385dcb7 51
(.stop 2 0xd070bb3 1455)
tree156_256)
(.fork 0 0x0 68
tree156_257
tree156_259))))

private def tree156_261 : Tree :=
(.fork 7 0x64227909f53af0ed45a9b397 33
(.stop 7 0x1426d7d1139dc79a556bc1f26 14102)
(.stop 9 0x3718779b7167a2e2cfd9d57c96dfb691 5158))

private def tree156_262 : Tree :=
(.fork 0 0x0 47
(.fork 10 0x2778b2736011bd476d25849d96955ab1a48 44
(.stop 32 0xd4f6b49d752664e39d112507968ee5fa6719c338ea66e9a55889f71618df68127d4e393b512f94c2969b5a9b3971df09ec3d393ac509987d 2814)
(.stop 6 0x707f5e83645139693b68e 13959))
(.fork 0 0x0 39
(.fork 6 0x3ab8ec749bd6b35d39f20 61
(.fork 9 0x51425449ec27f0cdd38c91cb473939c 48
(.stop 9 0x3716a37797e141cce646f961166b5b6e 7965)
(.stop 20 0xcdae5cfd05a3fea10a8dddc5969e13d462b50e9cc183df6875a8d9a5ce2957d693b692 4395))
(.fork 0 0x0 57
(.stop 4 0xda0143350e9870 1916)
tree156_261))
(.stop 25 0x34a1584574566759adda11df788b6361e399c19da0143350eb3973d7d11666e9df07c934bf27d4d9136574c3 6577)))

private def tree156_263 : Tree :=
(.fork 7 0x5b516fc6501968a8d2a40c5e 51
(.fork 10 0x11dc9472c60f553fc100a50b544057f960e 44
(.fork 14 0xf343d427b0d7d3650f4e4e2d3ac5099447618d87d68d1a4b 54
(.stop 14 0x7a2f854817367a24eb8509c3384755f5a4ed2d4e3949bd43d 14102)
(.stop 22 0x7a0797c5847725556b8e65d3b7bc61e9e92cdc04ed166e05cd071cb77a2e2cfdeee22d9c338ea 14248))
(.fork 0 0x0 26
(.fork 7 0xce65d0987a6939e928d8e531 60
(.stop 27 0x384750972ca3d1367699ab7b44e3199a779b4b575737bb5fa6223d098e39497d43050f586d61cdde0d57d09b50d9a3b 7041)
(.stop 12 0xd9d955adc751c888b772050c143dd57d0005acf4c0 1118))
(.stop 13 0x3723817385475737bb448d1dbdee530a5d397e9707f5ee 6724)))
(.fork 0 0x0 61
(.stop 17 0x35555aa73901de4a85da49134d3009ec27f11235cef7bb38a4ffa400139c 1599)
(.fork 0 0x0 59
(.stop 23 0x35453fbdb79d7d1b8bd070e178dab7bb499126ada39884d3006482a14a972c80b323d74f6844b9136 2532)
(.stop 25 0x1df7deed873dc4d1bdd9e9fc88ffb4b52f196a9d7d45046211f23d5707792528d8738e525f49bd43d703f566 13807))))

private def tree156_264 : Tree :=
(.fork 7 0x5a349bd7285d39b847a1a222 46
(.stop 5 0x38525d0b97e6925de5 5330)
(.stop 14 0x73078e55a7a0eee149742e5f907d88d2705dc618847ef37bb 13780))

private def tree156_265 : Tree :=
(.fork 7 0x2ac1e10bc12f18cf733e8ec8 56
(.stop 25 0x33717555e89e3a59b1cbcd26f72e1e86d2fd9ba69548082ec17e07571df7deede8b7efe18dd07d26d50ed9a5 3143)
(.stop 12 0x7a2f7bb493b8e65f834bb6e2dfc1da4126f4e8f566 13343))

private def tree156_266 : Tree :=
(.fork 0 0x0 47
(.stop 12 0xe399e7ed7b9e92d9f5124558755f5acf3861dc91db 7671)
(.stop 20 0x584770c5acf85444935e235db7bb7a2f4ae5a89ad8d7b9e92dee8e213af190e79e3426 13969))

private def tree156_267 : Tree :=
(.fork 8 0x2c60b2b3dbcff050b544068eda44 38
(.stop 8 0xe11e22de3992ea4c2974e707e223 652)
(.fork 0 0x0 54
(.stop 29 0x367699ab36b189da4edee5611695785172eb5db3131d5c77df98046d9426704a842a37767a361ce2238e525f49bd86d61cdde0 8756)
(.fork 6 0x166cff74449747709b681 44
(.stop 17 0x37251fff7bc669767d3399e92dc39e8b8b3f7bb0f3477c2500f4e509987d 5473)
(.fork 0 0x0 56
(.stop 3 0x38e25cf59a5 3176)
tree156_266))))

private def tree156_268 : Tree :=
(.fork 8 0x1dc8b2736011bd476d2765ab34c7 56
(.stop 13 0x37bb27522cfd9d9caae3a9b76ce5cc6844ad1395cf59a5 3772)
(.stop 18 0xe11e04fda2d9a36ddf71777df8e679fb39738e525f61b5873d5856185acf724 969))

private def tree156_269 : Tree :=
(.fork 7 0x816314cc6833b912b44e59a5 51
(.fork 10 0xa782a32c60b2b3dbcff0402942d5101cac 39
(.stop 19 0x3710925340857ed913ce093ac5f89ae4da0543b5cd17427a1b3012c7d26f5acd74e 7516)
(.stop 13 0x36818d7b8ea511f55a72a9de2e398ebc4be530a6ddb690 5036))
(.fork 11 0x506143cb2736011bd476d25849d96955ab34cb 58
(.stop 29 0x35db6ba78e775738e6704f2cf30f1f26d75dddfd9e8eb44491874d9d9caae3a92f96909b736ddb6902c7cff7400d73b61bdde4 5029)
(.stop 17 0x370d6ba78e7449367672ab8ea4be5b73ce5c9ec3d39426511d87d83a768b 969)))

private def tree156_270 : Tree :=
(.fork 0 0x0 59
(.fork 9 0x51b1920a852a5cb202cc8f5d3da1606 52
(.stop 4 0xda48a7e3dbd3a5 1924)
(.fork 10 0x5b4816314cc6833b912b5f517d766974c8 65
(.fork 6 0x143c6f52f04bc6499143b 39
tree156_264
(.stop 27 0x3368706b980703dde0d9d5fbcdeedde5a37797ea35b8e65a8dc1f818f71b83de3f9def57426b59ade72b35e97557728 2516))
(.stop 26 0xcdbc6278d8f97e888b8e638a74a588a7851364d1c94e5d6a8dc94f55402942d29c0eb44492234d9d9ad66b7b68b 7051)))
(.fork 0 0x0 68
(.fork 5 0xde16d89f327d4b29 61
(.fork 12 0xf789ec27f0c43448d90f7a2f7bb38a4e323d9939c 50
(.stop 4 0x18af6922f18fef 13959)
(.stop 7 0x341650c943bda49139498738e 3319))
(.fork 0 0x0 65
tree156_265
(.stop 8 0xda0125fd59077c2ee4c6861c3397 3618)))
(.fork 0 0x0 60
(.fork 8 0xab05ae27ac9fc2a18ec33b354d1 51
tree156_267
tree156_268)
(.fork 0 0x0 56
tree156_269
(.stop 2 0x3dbf4d0 13519)))))

private def tree156_271 : Tree :=
(.fork 8 0xab05182578bc12f18cf733e8ec8 52
(.fork 9 0x7772520a7e33a93934e954c953656a7 35
(.stop 8 0x973f5db8d7a532a36b8e66e21f24 13325)
(.stop 22 0xcba9d4fd75d8709c275483644f6268df7b28b1b2e18b0e497d76e35e94ca66aa36b8e65f834bf 6269))
(.fork 0 0x0 54
(.stop 3 0x34bf49bd3a3 4103)
(.stop 21 0x385094e37bb88b7847644ddeea0ef8e7778f71c27e4e25424509e471d1d24e613a061c32fb 3922)))

private def tree156_272 : Tree :=
(.fork 0 0x0 35
(.stop 7 0x32f34e977bb5a7f5fd4e8db88 3789)
(.stop 17 0x1e8fd795e89e3a6361deede8bda480383afd26149b590adc9d91c72e34bf 13966))

private def tree156_273 : Tree :=
(.fork 12 0x191877c27a09f93894e36424509e471d1d261c339b 48
(.fork 9 0x50716b0bb03398f524e3d3a95cc5de3 37
(.stop 21 0x38e977d340933634ae497de8fd795e7ee3997395cf78541b60d763b0cecd534569fe39ddee 2048)
(.stop 19 0xf41d284763e1189d24e0b4bf79fa66aa36b8e60044eb2865b8e75a7de8b94e37bb 13343))
(.fork 0 0x0 41
(.fork 8 0x400511c44e53885f157e66939b82 54
(.stop 14 0xda1c01ed07d393e15191cdc9d3a329b8eb25f59deee39dc0f 4703)
(.fork 0 0x0 52
(.stop 9 0x38546473714693371f6e237bb4e4d3a5 5808)
(.stop 16 0x29878e17c6b8e66e234bf64738465ac1e89d7e17cbe39d7d6861b38e 14565)))
(.fork 0 0x0 47
(.stop 31 0x349c861384670372cc8d8f3687c6371488c666ee398c5735d8f445a89cb08afb8e777bb7bb7a2dfbfd9d8fec50a56955ab17cb5f81e7e 7817)
(.fork 0 0x0 43
(.stop 20 0xd795e8fd03d73de1509da315cec33b378e577bb7bb7a2dfbfda2d0035a456b06461a4c 5945)
tree156_272))))

private def tree156_274 : Tree :=
(.fork 8 0xac034616c89ef27e4c5b3184ffd 53
(.fork 9 0x6422790c5031950a24be530a5a6d6a6 52
(.stop 13 0x384c7c9a228d9f1734d30cf6358316a7ce6c5141b71393 5649)
(.stop 29 0x34a6889f713644f5e05f89b7e72cb6736dd9ca7e13587d6dfdc19dca160c5cd38e25f7190579eb4c3363d133499d7d15f6b55d 7495))
(.fork 0 0x0 65
(.fork 12 0xab05182f04bc636111d850b54405cd17cfd30cf63 52
(.stop 11 0x38eb973f5db8d7b8e61450a7e449d3935cd5741 8898)
(.stop 7 0x38e6640b56764437108fe3728 4555))
(.stop 21 0x32df88c75e5707f55449a543650dd4d1d7dd1334c05302d59c5141e00bbd472d1ce4e7339b 8129)))

private def tree156_275 : Tree :=
(.fork 0 0x0 61
(.stop 12 0x72e78e23d9e83ada107802ef573bdeece294e71437 13662)
(.stop 30 0xe5fe83bcdc1fc0cb81defd4f0459165c6325855cbad07d2f55ce78e67f1640299aa704e3a96965aaf563191c9f43d9d7305d1b39b 5007))

private def tree156_276 : Tree :=
(.fork 0 0x0 61
(.stop 7 0x367d5cede8bdeece2938c939c 1920)
(.stop 23 0x349c79e35f2694b7bb7a2f67d141d4dfe398d84366d1d850b544072b37b73894e3661c190b79fb39b 6876))

private def tree156_277 : Tree :=
(.fork 0 0x0 60
(.fork 8 0xab05ae2068c573194ec33b354d1 51
(.fork 11 0x50a144cb183610d9b47051d850b544068eda44 61
(.stop 30 0xd2968dae606189ce09e8fd796192e3a4d803ae1df492674a064437b01e00bbd310d69f61cd90f7a2e5389e837bb38a543666819aa 4062)
(.stop 24 0xcd9d691e600ebf44ad90b6b65adb729f423862b7bb61cf6916dc9c0c79fb39b3f792ea508a052a36b8e6 4703))
(.fork 0 0x0 47
(.fork 10 0x1dc8d80365cfec401d42951116955ab1cb0 57
(.stop 29 0x336961bf5594ea74a170378eb449d9a96ddf84644499b7d76e83fd504c4c4e719187f177bb16846ed1df0e25424509e5a7d6a2 4395)
tree156_275)
(.fork 6 0x2c8cf67400d6b064634c7 57
(.stop 19 0x38e929d367a68f9ad9da3cebfd08d2ea508a052e398ba535d8e294e95615deed69f 2516)
(.stop 5 0x3567643f7bb38a739b 1920))))
(.fork 0 0x0 56
(.fork 7 0x5182058a823afd12b44e59a5 47
(.fork 7 0xd80365cfec401d4445ab1f18 69
(.stop 28 0xe11a83ae601d47d4e2970da04e197f178ea1b2cd7f5a8e2cce144f524e3d6115a59e7dd58c6471bb477b25649f43395746 9528)
tree156_276)
(.fork 10 0xa782a32c60d84366d1c1476142d51034cb 52
(.stop 2 0xdeed3a5 5011)
(.stop 25 0x353f6dcf5622c8f8ea77c371888b32de6ba5b83cde94da5a5b39b141cce63d49611d7b17e2da2126f6e13728 7508)))
(.stop 39 0x35e05d2f7bd365d007e1552eae398bc65a9d734ce6ce255845cbee380e1a42190a2530d4dfdeecd84366d1c1476142d5101f14d33c51427d0a7e33a912744f53934e974d0 3456)))

private def tree156_278 : Tree :=
(.fork 0 0x0 71
(.fork 5 0x450fb878a2090825 37
(.fork 9 0x9e538a4ffd4e113a5507d4417081cba 59
(.fork 10 0xd1c6481b8ccdb33c4ec23b38f5d3da2358 51
tree156_243
tree156_244)
(.fork 0 0x0 60
tree156_245
tree156_246))
(.fork 0 0x0 64
(.fork 6 0x5e05bc2f00bc7316cc61 62
tree156_247
tree156_249)
(.fork 0 0x0 46
tree156_251
tree156_260)))
(.fork 0 0x0 77
(.fork 4 0x8683e71208489 64
(.fork 8 0x5e03461e0c7902078c5b3184ffd 59
(.stop 21 0x37aa88af5fa5d3a222cdfc9de388943a5f89c26730768e33b99bada486482a14f5d3da12ff 7352)
tree156_262)
(.fork 0 0x0 67
tree156_263
tree156_270))
(.fork 5 0x2160fac653195f30f 68
(.fork 6 0x11034a1e349f327d4b29 65
tree156_271
tree156_273)
(.fork 0 0x0 64
tree156_274
tree156_277))))

private def tree156_279 : Tree :=
(.fork 12 0x11ac93b2a0cb1f3ab955755ed6b35ca174e6209f20 42
(.stop 16 0xe3a1735cb2e225e5f16a47a0e054d09877a4e254bf556957d5a41d4f 1885)
(.fork 0 0x0 26
(.stop 15 0x397c5d3371550977b81e0478e2584d785a756a4ce28f567569f2d 4847)
(.stop 8 0x94bb70e691b7265d3337c5a934b6 13335)))

private def tree156_280 : Tree :=
(.fork 9 0x34316d45bf1e38e2c38bd3964e8b690 42
(.stop 20 0xd759de4d516063e3a9735e39187a6921fb2d099c1977b6405e39955a55f56906e05d4f 5006)
(.fork 0 0x0 36
(.fork 12 0x2239866925a976aabb8e62c24cf041f174c694df23 25
(.stop 4 0xe3a1735e3a9fc8 7981)
(.stop 9 0x2667e3a9735e140f533d2342649d3725 13471))
(.stop 24 0xd271de4d099dead289dede399f1adc39d5ad02a368e3a97355d05ca8e11938c4eb199a66c1b7e83a3424 8756)))

private def tree156_281 : Tree :=
(.fork 9 0x62b18d89de388943a6bb9c2677d6493 56
(.stop 22 0xe38a063cd965c9e399739814b4245d3b97e35c94c29c2a842a37770e2288b3033b8e2453359a5 5654)
(.stop 6 0xdc8d74ece188aa3d4f2f7 1598))

private def tree156_282 : Tree :=
(.fork 7 0x4f73d4d4337cae06383fb687 34
(.stop 27 0x28ddd50a052e399deddef0ebb5d072f7421f85453360618da2838e388786338ce2f3d2dc1c8167395473988266e9b89 14248)
(.fork 0 0x0 26
(.stop 22 0xd0122cfdc41f20d03c7fb25078e750d9e82ce5478631473825859cb4d058f567569e927cb6061 1885)
(.stop 17 0x33708da340f925b8e677b7395641b8463d216165d3991dcdf94c29c2b716 8756)))

private def tree156_283 : Tree :=
(.fork 0 0x0 58
(.fork 11 0x1720d005b627a4b1f2ee8bcd33c13994e7d73b 49
(.fork 8 0x14208aa3d4cf6d422512449d1912 47
(.stop 17 0x625d054b12d548c5349af37575738e63d09af072ff38227791bd49d93aa 13942)
(.stop 13 0x1cbfe1459a5778b7b3752f2ec22d49eb2a1926549a7723 13942))
(.stop 19 0x34157305e90d2d5f1a8b0b8e6706742661e9e928187552194065a1e18c5e4723395 5466))
(.fork 0 0x0 44
(.fork 12 0x16a09ec2eb125549d138b4eb1426511d55c55edc19 57
(.fork 8 0x14645b51dbcc5431a0d8a3671870 25
(.stop 7 0x37b5586368477df8e62bfa0fc 334)
(.stop 7 0x35527a4b6848b3f5e158637b8 6883))
(.fork 6 0x16fc6503178cf835f7395 41
(.stop 22 0xdef1cb0cb2a35de3a9aee8b16493d055c247571df78fef8e6814b42455f55f45ca974c7071dea 3912)
(.stop 11 0x32fb5d074b56955b89da11df7e399866692338d 5329)))
(.fork 0 0x0 41
(.fork 12 0x35e8d913b25423511555955f55f4586172a5d31dea 30
tree156_281
tree156_282)
(.stop 39 0x1df7e39d9a9e146702d75938e02f032a41f384a619987a692342677b62cd90164a0dc55df58b1768e16fc65a3178e2c38be059ce548aa33b8d8a47398826955b89889f692 13637))))

private def tree156_284 : Tree :=
(.fork 9 0xa782c4cb263178cfa448513e5115ae3 58
(.stop 21 0x35e149d3728277b8e45a41d4fcb9cf4244595f6e3981720d006d62578cf04bf93054e6539f 4693)
(.fork 0 0x0 57
(.stop 13 0x38e45a41d4fdefe2c2e39820d27e4d9c4e613a050cd43a 2970)
(.fork 0 0x0 47
(.stop 4 0xd5522c2e39881b 5622)
(.stop 6 0xd2cd267d579c1a88cb855 4403))))

private def tree156_285 : Tree :=
(.fork 11 0x176147878122a0a88425913144cd1ae499e491 43
(.fork 9 0x6432c40c4633852ef57d9c1a72d1de8 36
(.stop 10 0xdc6ce08cd914c26b91cb2e3adf2be13107c 4539)
(.stop 15 0xcd4d03270ae5f57355d07720644342472cb67072d78e67caf97c 14412))
(.stop 7 0x397c5cd17cf5f734b37caf554 496))

private def tree156_286 : Tree :=
(.fork 0 0x0 54
(.stop 20 0xe39dd50cbb876335ed0876dfe706d7860f594cb55e57da35ee398f583db556655c5601 5492)
(.stop 5 0x1574d59c59c4eab4c2 13051))

private def tree156_287 : Tree :=
(.fork 0 0x0 74
(.fork 9 0x3500fac51816c85bc255495e27bc9f9 52
(.fork 10 0x33a8d85423112744f569a5a9d7355d05e79 43
(.stop 22 0xe5f5f1ed2a5f1d863740394bf85572d5d4fd781de8e39574272fa061e1295f65a456b07069cb4 3142)
(.stop 25 0x3670889f97d8d9f53899bb8e666ab84c70922288b0b37d5d32225e5f17346441f14d2cd133499d86b61d755e 7503))
(.stop 22 0xe3ae367dc4e2c3d05d74c6bb772347617345d097cfcbe539c7caf5542c8d09644c5133499f567 4539))
(.fork 0 0x0 67
(.stop 35 0x384788cb8e58da37118fe6493dca512ddca1e7ed091f1a925b8e661c59a5d5481720d003db144478a27a4cf047212fe4c1539fd3087861e38d923650e2f 5024)
(.fork 7 0xe2444c12e44e81cbf8b0f690 58
(.stop 6 0xd5489e933c0f5c4bf939f 987)
(.fork 0 0x0 62
tree156_285
tree156_286))))

private def tree156_288 : Tree :=
(.fork 5 0x8072cbcebe559d6a4 42
(.fork 10 0x58277be03081f6169876d2c88baa4e253aa 32
(.stop 6 0xe134b12dea173fe5f12e4 2363)
(.stop 3 0x367235e3690 2363))
(.stop 8 0xda412e4e5f1b7cd9c973f6dd75f2 3448))

private def tree156_289 : Tree :=
(.fork 11 0x3e03600da14787811e38a882a5513144cd267 41
(.fork 10 0x27a4c4435e8d91508d4455ca974c77a9f1e 28
(.stop 13 0x35f24eab7b12770f581dd8d84387ce3764173954e71570 2526)
(.fork 0 0x0 43
(.stop 36 0x641740377d797da102b47cd91690753f67061d77285a778e64c05b89def173f61df97c22a0e244b91cbf9247690030c0c52c40b2331192ef57d961672d1de8 13205)
(.fork 5 0x6da1dd8f487eef554 55
tree156_288
(.stop 12 0x70237181dab6900c9b7162c88b302ea4bbd473b395 13936))))
(.fork 0 0x0 47
(.stop 18 0x5a937b744fb69081538e82c48d9546ed1d9d31481b22a09de27bd087428d3aa 13205)
(.stop 25 0x397c8af38e67c6b8551dd97cfd5484721410b1236551d96dfb4c516c8f58580560b4c054d57a435eb5cff5f7 7968)))

private def tree156_290 : Tree :=
(.fork 0 0x0 39
(.stop 22 0x7caf7108143846644b3953af9076e3a1de4d7f48a0dedc15f0cb43332a0cb0c3ab8ec755edf20 14262)
(.stop 17 0x3850058d912ce5543ae3a1de4dc4d5707091f2be39912144f942879ff690 5034))

private def tree156_291 : Tree :=
(.fork 11 0x50814448aa2ca4f533db525a49d19036449cae 60
(.stop 28 0xd9d8b0ce399ad5dc459a5778b8eb5f7b8e86bba18cd77d3aa753f850058c80c29e112150a1d4bdc8463e2f2d26549a5605 3281)
(.fork 0 0x0 47
(.stop 25 0x341b27438e616672db8da336a3d09cbfcde0a78448513e50a37227a1f8e85f79914d7c89de4e393aa6921de4 6256)
(.fork 0 0x0 66
(.stop 6 0xd0119096431e7cdc8cec7 5488)
(.stop 6 0x6bbb8e424f9690753f5fd 13815))))

private def tree156_292 : Tree :=
(.fork 11 0x380f685192a0cd8a50cd43a5f557d661c34c1 46
(.stop 22 0xe11dd4fd27cf3f64274b3999397c4995e90d79511657d9e7e8b0a976e398a78317913e50a1e7f 4836)
(.fork 0 0x0 54
(.stop 20 0x83af40f8187552751b71344b52657a435e544595f679fa2c2e398f58582d9a3669dc0f 13471)
(.fork 0 0x0 29
(.stop 15 0x372349560f5d7848a455c38e63d0b690498b8e45a41d4fd7c9265 5034)
(.stop 18 0xcde5fc6e3ad1c8e399e7ed0a525564277193d211d2585991d7eef7218187854 3289))))

private def tree156_293 : Tree :=
(.fork 7 0xbcb3af8ed23d655705829ada 38
(.stop 12 0xd7e0b0fd9e4bace3a92685ce37192754ead585a055 4250)
(.stop 8 0x276f2e242575f72ef51cb49a3729 13347))

private def tree156_294 : Tree :=
(.fork 0 0x0 41
(.fork 9 0xbbd337cd7a3b25388508d72a5f15e84 49
(.stop 19 0x1911e399c19e385e8fcb91cbfe13063e2ef0c5749952694c01303d7e130e644999e 14113)
(.fork 8 0x1400e1e3ae527361a587764472f7 22
(.stop 14 0xcdae66fdebc59ada1d57be135e90e389de9d54dfc68b36367 7668)
(.fork 0 0x0 40
(.stop 11 0x33656b7f97c7a425c8dc46a11aaaf97d7a15f1f 9838)
(.stop 5 0x35f877a78e277d37be 4867))))
(.stop 17 0x3553338367d94e785550df8e64c032f849cd5f6585b38749d157b7067692 4712))

private def tree156_295 : Tree :=
(.fork 0 0x0 41
(.stop 18 0xcb85fc58187711b46397c3d2191d66ddfbbd5780291670b225d2f5f85d317e6 9828)
(.stop 2 0x5d2f5fd 13815))

private def tree156_296 : Tree :=
(.fork 15 0xc5e22a89e029ecf533db52745cc97445f79903644b4c133e4e2c 38
(.stop 27 0x760d281fbda1038ea6451a48d27e496e398ed2da4960e6bb9df5924f8e45a41b81706f8503b18f486475ded7a1dfbb 13177)
(.stop 23 0x38e627434a8692397c335d2694e013a183d354f77a72ea7ef78ea7a423fadc85431da4960e6bbb722 3761))

private def tree156_297 : Tree :=
(.fork 8 0x5d43e5206cb222cc11cb473939c 57
(.fork 6 0xf683e150cd43a5811870 54
(.stop 5 0x1b75da1c5a5d0a45a8 13945)
(.stop 6 0xd9f5437d7f544572c74c6 3019))
(.fork 0 0x0 63
(.fork 6 0x1b9c9ee425d0984999268 50
(.stop 20 0xd056197d29d616647784b508f68450df69055edcb3779f6873b491c047658776445a45 6259)
(.stop 34 0xa5cb2cd6dd36847a322c2dc95912d0117c8d77dde7d9e6055e12d9a9deb46411b70d855cd57d05f6d906643dd437517553582d69c5a957d2703f4c6 13002))
(.fork 18 0xf3877635dcd8e6475fbb862755e142c6dc361508c5cd5741641990f79e7567 41
(.fork 9 0x15b18d8ba935e9423511572a5d31dea 60
(.stop 6 0xdc39877cd959a166a6223 5174)
(.stop 11 0x340a6b836703cf370e61df371337740f582f5f8 6418))
(.fork 0 0x0 49
(.stop 5 0x3692143b40a6449ae0 4724)
(.stop 9 0x338755ef6926dd75fd668770d6917725 3909)))))

private def tree156_298 : Tree :=
(.fork 0 0x0 57
(.fork 6 0xf683e12a0d43350e9870 54
(.stop 4 0x6dd768705ac5a8 13945)
(.stop 9 0x1265d7dd11679fb8e629e112151174ca 13797))
(.stop 2 0x3db74d1 13517))

private def tree156_299 : Tree :=
(.fork 0 0x0 58
(.fork 9 0x1720d0078a27a49fa33c13994e7d73b 74
(.stop 23 0x384d647341a645b423476555d55eb4b94bd587170675e54995269581f5fd11f85b225389ef27e4d8b 4385)
(.fork 0 0x0 45
(.fork 7 0x77022d4b1236551bb4765f1a 67
(.stop 9 0x35f786338e8583b55219147863178cf9 7652)
tree156_290)
(.fork 0 0x0 49
tree156_291
tree156_292)))
(.fork 0 0x0 74
(.fork 6 0xd403eb16c85bc27bc9f9 63
(.fork 8 0x19306e727b8a892a510974261132 55
tree156_293
tree156_294)
(.fork 9 0x82033a8d85423112744f57355d07567 60
(.stop 20 0xcb6a403cda6189e15539c50d9437643d9aadc651c15f3da3bda1c4702068bcb66859a9 9063)
tree156_295))
(.fork 0 0x0 66
(.fork 8 0x370519148882020a4d933b1cec9 67
tree156_296
(.stop 20 0x83f397d66972fa14351d95309a35692b4c149d369250f1cbfda401741b9c9ee44cb563 13956))
(.fork 0 0x0 61
tree156_297
tree156_298))))

private def tree156_300 : Tree :=
(.fork 7 0x8072c3938858617c55f9a052 52
(.stop 2 0xe3999a9 4721)
(.stop 11 0x285d9f270ce5f508958175d77a0797f888f691 14270))

private def tree156_301 : Tree :=
(.fork 8 0x193c7831e4081e20acced340cd88 39
(.fork 9 0x93b2c7cc573ab94bc5acd7285d39f20 52
(.stop 25 0x35455a472cc863397c779f67961fdd4f7c774b27099df4d0111ce5ce173e83bb67c3400ed43d597355d05cab 2514)
(.fork 0 0x0 44
(.stop 14 0xd5156a6d9d6051d5112ff5819872da449ec42813ac511dc19 1885)
(.stop 15 0x38e75ce36751d7754561ca051d08c6424c394bf538957d5d2f38a 4863)))
(.fork 0 0x0 42
(.fork 11 0x6422a18ce04c394bf538955a55f572b5d2dd4f 45
(.stop 16 0xcdca402def5e8fd05028188c64a0dec1e92e5fde80d08d3ac55e9b7e 7203)
(.stop 14 0x2c375d7a5e397f4bff423706640592838e6472d87f66df381 14567))
(.fork 0 0x0 45
(.fork 9 0x59f2544b122c9512044f52f14e313ac 40
(.stop 4 0xe1512f5e399422 2848)
(.stop 10 0x5a478ea88d34a488c75444bfd6067a03683 13941))
(.fork 8 0x27ac9fc2a5cc6553457d35f63421 41
tree156_300
(.stop 8 0xe3aa8dae398d993ae10894bd74b5 4374)))))

private def tree156_302 : Tree :=
(.fork 0 0x0 59
(.stop 8 0xd781254e3a9434d5613045a85872 5022)
(.stop 25 0x36887eef2cc7a137ad64478ea311b40144c8d6f3a95e8f94b75ec5d03558314169b68f5a427039c1075135f8 2697))

private def tree156_303 : Tree :=
(.fork 8 0xfc20b2a24a94425d132580960a 66
(.fork 8 0x19108bb364cec73b24f6450c543c 38
(.stop 4 0x5d038ea3ab509a 14105)
(.stop 13 0x367949997387c778e6703b4235d0f85588c78ea77a72ec 2831))
(.fork 0 0x0 53
(.stop 24 0xe3a9911e3992f5e134cd5da3cf484951f20e5f0cd7da2876b99935534999e8fd7b06423140c655d01c0e 2977)
(.fork 0 0x0 38
(.stop 27 0x336c7c738ea88c74a5620740486238544c39fb7d54d43753457d8d7dcbbd49992685ce173edc649d53ab4f4866de055 7502)
(.fork 0 0x0 61
(.stop 20 0xaf8740186232e36205e85814f37488c785550dd4d15f635f72ef51cb49992685ce173e 14412)
(.stop 14 0x201f55364738e635e5422da3d303d7e0c4564477217a3f729 13797)))))

private def tree156_304 : Tree :=
(.fork 0 0x0 72
(.fork 21 0x51f13b04f55335e8ddc84c4e33a8ea5535991a7a3e493dca465527989f72c94b2d423d0a0 40
(.stop 6 0xd4fd30e640d912d2e5881 4853)
(.fork 0 0x0 33
(.fork 4 0x335cec149a5df2 42
(.stop 16 0xdefa227d27e18ce5fe49ddeb075472d38e54bd785561cb68f61fdd4f 2521)
(.stop 4 0x9c1f8554e4738a 14411))
(.stop 5 0x12f5e1556a161cb691 13497)))
(.fork 0 0x0 52
(.fork 12 0x5a434019306dc33a8d00449d13d5cd574172a1cab 53
(.stop 20 0xdefddf4d0357385cfb8e65d0dc23e12c812364cec73b25565d0a80cf1908c503195c0e 4245)
(.fork 0 0x0 38
(.stop 6 0xd0117385cfb71927559b7 4558)
(.stop 5 0x340447397385cfb729 4555)))
(.fork 0 0x0 58
(.fork 10 0x5c847e253895e362cd9b4e6539f642590c 60
(.stop 15 0x37bd70678e616936834c1191cd560a892c49f1adc64c6549a5605 2214)
tree156_302)
(.fork 0 0x0 63
tree156_303
(.stop 3 0x35583143567 1602)))))

private def tree156_305 : Tree :=
(.fork 10 0xfc04014605211e409552578ec83d88f63 68
(.fork 7 0x2100d2878d33dccfa3644d95 51
(.fork 7 0x9e236111c147617345d097cf 42
(.stop 14 0xe5f5e79def960f5f778e68b0b8eb7cab72119092ee6b9dcb5 5941)
(.stop 17 0x397d5cd77b8583d7ce7c578e67a278540d0508d50bd600dc85745640b2ed 3922))
(.fork 0 0x0 53
(.stop 14 0xe39a66ee5f573579e77be277cf52640b42a190908d50f960c 6094)
(.stop 39 0x336450737af66c77b05d1740592772cd8d878e6583e1908fe34a335ecf4c4bb84f83d0d24a72fa05a88a22c2ce1574b72d5d4fd5392ff4c10cea7a3e22b8fe7722581b38b 1890)))
(.fork 0 0x0 52
(.fork 8 0x33a8d00449d13d5a697355d05e79 43
(.fork 11 0x502142cb233118ce149512735a456b07069cb4 53
(.stop 10 0xe151b7fe3862c2e39a66ee5f50a258316a6 3438)
(.stop 21 0x336c88a367c5d0b7ad8b0f404277d3a9d781cb588c666ee398d6e92537112068a786b8f722 1892))
(.fork 10 0xc803336111c147617345d097dc7c534c3 48
(.stop 19 0x1aedcde0021d4e076449a767c6b8f7226b85cb599bb8e61e009443d4938f640999d 14097)
(.stop 2 0x44c755e 13652)))
(.fork 0 0x0 62
(.stop 23 0x371b8d9f7b5a36b8e66b8755442377b8448369144d37280360d8447634c305cc6e62c8d09644c5267 6419)
(.stop 15 0x37b56de78e6499126ada3c1621e009df3d49902d59c64272d755d 4723))))

private def tree156_306 : Tree :=
(.fork 7 0x174147c64c2a251324c01303 38
(.stop 27 0x340a276b36a7a3e2cce3acb0e337cd7a4e23692706623199bb8e666799accbd91c1581591166b6402dc64ead3d21fbb 3449)
(.stop 13 0x2231e39999ecbdd1c1581591166b77197a176914e7b729 13960))

private def tree156_307 : Tree :=
(.fork 10 0xe88b4230cd004bfd30455ad56c581b39b 72
(.stop 8 0xe3acf487eef729646b4b92c94d99 6118)
(.stop 18 0xe11d077cb75b88e3a9fb6dc49adeda008a62c4912055e9de6dc659ad7057567 5963))

private def tree156_308 : Tree :=
(.fork 8 0x202c8c32a14b202cc92ff4c11606 62
(.fork 6 0x5c0b2344c513350d5438 49
(.stop 10 0xe3aa063d0509d33d19aeddc622cfd9d5a39 4233)
(.stop 12 0x66b78ea818f414274cf466bb77188b3f5db889f7be 13046))
(.fork 0 0x0 34
(.stop 8 0xd5219adda39cc1e39c8aa33ba227 6893)
(.stop 18 0xd9d62cfdc414bcdca16b0e388323818f6807305d5c94bb8e5450199d66b7692 1427)))

private def tree156_309 : Tree :=
(.fork 6 0x8046423140ebc4237397 39
(.stop 6 0xdc622cfda0c32d3b1d6b3 2515)
(.stop 16 0x818353faabb8e699bb97d18bcccd83fb680499d39f709b7285ac34c3 14112))

private def tree156_310 : Tree :=
(.fork 8 0x3686e62770b2344c5133499dcb2 59
(.fork 7 0x17022d12ff4c114355819e80 58
(.fork 7 0x17225394cf5a816a15cedf1a 24
(.stop 8 0xd785e85d9d6225dc61f20e39a231 3768)
(.stop 10 0xd04e227d9c22bcdca0d757a175e14bd72d8 7807))
(.fork 11 0x1620594780203938f4ea599d66b5ad36b8784c 39
(.stop 11 0x397d3ae38ea927740e7a3f4a63d19aedd5214df 4369)
(.stop 11 0x38ea3d1b5486b8f67570537be508b8e6927797f 3768)))
(.stop 16 0x7c6b4a63d1b718143064242897da61d35f12ef51ce4c05302753339b 13474))

private def tree156_311 : Tree :=
(.fork 0 0x0 58
(.stop 32 0xe396053dc4de8fd2890a25a6da42d7c4941276cbbd4739e82e399c19dca08a43118d9349cd6b0d30d304647235dd56094e362cd9b4e7df1a 6403)
(.stop 23 0xa78dc61f20e5fc1650cc0474202c8b4230d2ff7a0339b1e009444ea59add59c642338172b753f55d 13640))

private def tree156_312 : Tree :=
(.fork 6 0x35c64c425d26649a1911 27
(.stop 11 0x38ea4bb9de9d79a5d3e5f174061b35f75d0e664 5315)
(.stop 13 0x1cb3da497dce3889dd94bb5df5ccf5f761d367d77a7553 13479))

private def tree156_313 : Tree :=
(.fork 0 0x0 51
(.stop 24 0x273340a27438e05355f2ae60574bdee509a862755e00cc6dc33a97355d059067c5372847617cf5f719aa 13792)
(.stop 10 0xd9f5735dc4dd4fd0a909ae12c9db57df692 3296))

private def tree156_314 : Tree :=
(.fork 7 0x51f1930a94425d1326411911 53
(.fork 6 0xa94642314108d4289740 27
(.fork 3 0x76b4bfd743 49
(.stop 6 0xda3ceade38924ada28b29 2665)
(.fork 0 0x0 31
(.stop 5 0xba1e38960f66de492 13969)
(.stop 11 0x629d9cd1afda44eade3a8e2b7eeb84d7cab7be 13337)))
(.stop 5 0x1912d7855fd583f553 13646))
(.fork 0 0x0 29
(.fork 4 0x27754397caa5c8 30
(.fork 3 0x1d166939e 49
(.stop 13 0x368f5d0f4a772cf6927a1397c00c00311664b032ca4eb8 3912)
(.stop 5 0x1de9d5380b575677be 14261))
(.stop 18 0xe5f6701e3ad881ded4eb8e3a89442c09745da1c3321dd8ead3d219b77eef722 6265))
(.fork 0 0x0 41
(.stop 24 0xda4462ecb5062c22636887eef97c2eb1cb3dec14df6db1b7ddc65de9d7e050935e8d913b253a977a9e84 7967)
(.fork 0 0x0 59
(.stop 22 0xd9d4e14cb511ba72cf8eb5d0f67600c0b293ae191266799ac70534b91dc5086530db7ddc65b79 3281)
(.stop 6 0x3ab77216df75df5ccf5f1 14105)))))

private def tree156_315 : Tree :=
(.fork 10 0x14488b4230cd004bfd3045819b706de739b 72
(.stop 4 0xdc81f28dc8d3a7 3304)
(.stop 27 0x38eb889f2cb6b59adee5fcc38dc450a2530d4dfe3a9fc5dc60b043afddf4d7849d933812ee4c3972b5d2dd4f8147558 3907))

private def tree156_316 : Tree :=
(.fork 0 0x0 60
(.fork 9 0xd808302102068c57319526549a54d1 61
(.fork 11 0x3b05c86551e009fc2ef51cb473939c50d9437 63
(.stop 22 0x68ef6926b9736d974f85542695ffe1359acd9f57355f6d90f66859a9d54d74bcb850984999268 14411)
(.stop 25 0x340a69136926b9736d7a1f9812749116d77dfbb862755e142ccea449cba8338367d5cd5906643d9a166a7567 20))
(.fork 0 0x0 77
(.stop 3 0x339720aca97 1923)
(.fork 0 0x0 63
tree156_306
tree156_307)))
(.fork 0 0x0 45
(.fork 8 0x2a24b122c94d95448113d55e9b7e 77
(.fork 7 0x78320789514bc53114e313ac 59
tree156_308
tree156_309)
(.fork 0 0x0 62
tree156_310
tree156_311))
(.fork 9 0x6e6204081e387925b49cd86961df565 61
(.fork 11 0x17218fc6551e0078d2ef51cb473939c68e9a45 63
tree156_312
tree156_313)
(.fork 0 0x0 63
tree156_314
tree156_315))))

private def tree156_317 : Tree :=
(.fork 11 0xd8083021014709eb27f0a862a5d26549a54d1 57
(.fork 9 0x16e16d4bcd315143350e969f5a89870 72
(.fork 7 0x34e1b90b252cb4d993d6cf6a 52
(.stop 27 0x32cb813f4265d3b37f7a4b55235eb2d05f4d7d866919a61dc8f4466eb97d6b69ca872af5e15cd59a166a5b726ddde79 5933)
(.fork 0 0x0 40
(.stop 10 0xda04d69e5f477246f72f24281adad785e85 2534)
(.stop 9 0x34b76baf6911dc8c3ddeb11b066eb7be 5966)))
(.fork 0 0x0 44
(.fork 6 0x11c076f2500bac4eb1c19 66
(.stop 7 0x38506691c0ed30de7ee398ec7 5180)
(.stop 8 0xe1419a4703b4c379fb8e65d3b681 3464))
(.stop 12 0xd7a174ee3999a96dcb8500344d8855c17d86693680 3926)))
(.fork 0 0x0 45
(.fork 9 0x8a62c48b254bc53114e313ac6df9de6 32
(.stop 14 0x83fb7ac586368e448d73bd7842013b5339736210784251b8b 13959)
(.fork 7 0x3ce18f8bba337174e888f5f4 66
(.stop 16 0x818f8ea66b768e7039caa814b8e63af1565e1192e666eb97d68d5a4a 13952)
(.stop 16 0x299797f8b3f8542c278e6703b4c30f74ebc5a6f84718bc7723d13716 13945)))
(.stop 41 0x32c841f3400866784642817d37ecb3975a99e92dc58d7a5566052dc9539f6e2dc26d9cda37da44ec7426d68d5acd7280a4829711c05a82eb138b5099c197a075fa5d39f2086235f5 3595)))

private def tree156_318 : Tree :=
(.fork 0 0x0 61
(.stop 12 0x55bb725030c337511d4e2d0291cb47394d25ce173e 13350)
(.stop 12 0xe39d870d2d42ab0a36227e5f45a32a1560661cb691 5486))

private def tree156_319 : Tree :=
(.fork 9 0x214146c5241de8b293644d954c21cb8 34
(.stop 19 0x3679224797c6ddf71d5325741e391745d074292499dc268fe3552473943e66e9fbf 6256)
(.stop 14 0xdeaa35ae5f1de7cdf91bed29973ed5492675a934b650eb726 4865))

private def tree156_320 : Tree :=
(.fork 0 0x0 61
(.stop 6 0x58135fa120495125849ec 13800)
(.stop 12 0xd54a225d7d0292dc9a051d9d40d30aac5a32a1767c 4711))

private def tree156_321 : Tree :=
(.fork 0 0x0 45
(.stop 25 0x367c7a03368973340a709b4a272cb5f477b64a0e399f1adc39b8188d38ea167cb124bc538c4eb199a66c1b7e 7652)
(.stop 25 0x37a8691b7252ee9119cbaca767cb76759c338ea2e8cf4b7c8f5e366b74275569866925ab49e39969d5a935f5 1872))

private def tree156_322 : Tree :=
(.fork 0 0x0 45
(.stop 28 0xe5fc75ecb30ea5924f67983c785422aa227dc3968eda0d1bd227cbba3105fbbd7d169d92838e62544d954bc538c4eb1b7e 1424)
(.stop 23 0x32d27eef97e690b71647397385cf986c61d1b6ee399e89e1352ffd775731d7d43d845011be66b7427 6409))

private def tree156_323 : Tree :=
(.fork 8 0x20388b72770d7838c507a499e054 36
(.stop 18 0xcb30897d9c9ddedeb0b10cda17dace5cba78b3f6751410c543d18f6083c6225 6251)
(.stop 12 0xe5f1a43cb31425d514ed461af71831115597c7b552 2832))

private def tree156_324 : Tree :=
(.fork 0 0x0 69
(.stop 9 0x37188b3f675667738a22bc9f433ed87c 7663)
(.fork 0 0x0 32
(.stop 12 0xd515df7e39d564ce5ced4ce28e2250eb6872511304 3631)
(.stop 14 0xd9e60f1dc622cfda0d1dbce28ebb4bfd60b77df8e761c35f4 5178)))

private def tree156_325 : Tree :=
(.fork 6 0x22dc9dc38c5133499e054 49
(.stop 17 0x367c580f5527c7b70e9c0b97c66c33970a903d53b5186bdc607744491140 5951)
(.fork 0 0x0 57
(.stop 18 0x30cf97c448f5e131196065f6b97d5d05b77dc60c443d95f1ed548c5431a1433 13627)
(.stop 2 0x7c7b726 14102)))

private def tree156_326 : Tree :=
(.fork 0 0x0 30
(.fork 6 0x13d44fe2778e2250e9cc1 56
(.stop 13 0x38e238bd30766c33975f5f6755567692474db76dc3a04e 1891)
(.stop 15 0x38e55ccb70e666b3974c135e88b3f675556769227d0ebb3b5338a 5476))
(.fork 6 0xa9850422bcd8738e74b6 41
(.stop 4 0xda01870ce5c779 5171)
(.stop 10 0x5ccb49e6449de2dc98c68813b54d66b7692 13207)))

private def tree156_327 : Tree :=
(.fork 0 0x0 69
(.fork 5 0x9f433d8cfb386587c 36
(.stop 13 0x38ea4beb53a925b8e67c96227dc3939f6e2e22adc6df23 6586)
(.stop 12 0xe3a92fad4ea496e399f25889f70e4e7db8b88ab728 6586))
(.fork 0 0x0 32
(.stop 20 0x5d138e777b77b066ea227da486363350ebb55932fb3889cc1da1c77025113045361af0 13637)
(.fork 7 0x3c70f38bba446513677b75f4 30
(.stop 19 0x384d18af71e1d950896e078e2863397f77df8e66199a48dc6d69bcbece227306493 4220)
(.stop 4 0x7c8f723476f687 14107))))

private def tree156_328 : Tree :=
(.fork 8 0x8046423884e393af0ed45a6dd44 47
(.stop 10 0xdc751b28b0b8e646f463118f0c54dc41a48 821)
(.fork 0 0x0 31
(.stop 23 0x354413ef85433bb72650cf6805aaf8e8586368316746c73118d935301cb4d30c80b499d39f6e2dc26 2045)
(.fork 11 0x62f1d6889f83fb71b13ec9d3315107c4e93728 43
(.stop 15 0x38e82c838e58d775f472c9dead28876161c78e67c6b716364dcb4 2372)
(.stop 7 0x38e6754770e5a3b7b54e675e1 4530))))

private def tree156_329 : Tree :=
(.fork 8 0x1d8c77025112e44c11af06e2f690 47
(.stop 29 0x38e7752336683fb6723cf9a3e703f5d455f561877ab68e02e01ec07c09dc2c04b147571df7e399e7e7ed339733ed1bd4961a48 2192)
(.stop 12 0xda48ceed54987cdca01f41b71618d9f0638364f4c3 2524))

private def tree156_330 : Tree :=
(.fork 0 0x0 55
(.fork 9 0x50e193cced340cd88367956755c1ada 39
(.fork 9 0x46b24ecb1f3ab968d5acd7285d39f20 26
(.fork 6 0x1d74b123d596a67a49f2d 68
(.stop 14 0xe11d56e813f71d70673885d177bc085077a2ca4d914c21cb8 5191)
tree156_318)
(.fork 0 0x0 68
tree156_319
tree156_320))
(.fork 0 0x0 67
(.fork 8 0xacc34316d45bf38b0e2f4e593a2 69
(.stop 20 0x7cb740a4e7d909ce20b0992838e6703b4264eb36910aac3df20549f42ca0cf633ed26e 13955)
tree156_321)
(.fork 11 0xd11908b2d3884ed45a6d6a67039c107513690 69
(.stop 18 0xdc3968ece119add5360f6d77169d7065f2590178e61204524205526e4e513a4 6722)
tree156_322)))
(.fork 10 0x2544b122c94d954bc53114e313ac6dfb565 39
(.fork 9 0x15f0cb4b1f3ab8ec75a356b35ca174e 34
(.fork 7 0x28d18bc8aa33b91b066ea227 62
tree156_323
tree156_324)
(.fork 0 0x0 62
tree156_325
tree156_326))
(.fork 0 0x0 67
(.fork 8 0x16d4650338ccf938b0e2f66699b0 62
(.stop 4 0xd548f603d95267 3633)
tree156_327)
(.fork 0 0x0 53
tree156_328
tree156_329))))

private def tree156_331 : Tree :=
(.fork 8 0x59850e29e0c5e3d40f6a584dae3 51
(.stop 25 0x3378445e227d9c187fd785cb4cda205e925371166777b04e457ced7b974977ca2288b0b67c5cd17425f71f14 3150)
(.stop 7 0x2707e1540cc4e475fb5d275ef 14411))

private def tree156_332 : Tree :=
(.fork 9 0x3321b3877638a8f48493d4426badfbb 43
(.stop 10 0xe5fdadf888f2fb36412ecda292fad4fd7e4 2984)
(.stop 5 0x368a4beb8eb44cb38f 3472))

private def tree156_333 : Tree :=
(.fork 0 0x0 54
(.stop 5 0x367a5a5b84b582dc0f 3612)
(.stop 17 0x367a7c7b5d9667784b645f72833d1133667f2fb1690d90446d30c66d7691 6888))

private def tree156_334 : Tree :=
(.fork 10 0x34c9e627dd0a0559d57066919a66b6b565 62
(.stop 3 0x367a5a756a4 1456)
(.stop 24 0xd9e88a0da4235dcb291b04e8b40a3ad83d044a513b5805a416dd1b75703f4ca3b3d55f68dde7e7ecb42c 7493))

private def tree156_335 : Tree :=
(.fork 8 0x22a89f13608d9950ad442640d912 62
(.stop 27 0x367a6b6b56507fb981582f2e22774bc8473199e6df739d1df894229e0c5ed5487743164c6333f513144cd26768e5a46 5796)
(.fork 0 0x0 50
(.fork 8 0xc00312040ce84e453a761a5877 54
(.stop 28 0xcb62365cd95e79e3923f8d4f9e8d8d776905ab739d0a9846527407ff277955f692384b3b0543d8b0b5ef1459129582de7b 8130)
(.stop 12 0x646b722584f7b0641342111b878a2060ec14e7f4d1 13650))
(.fork 5 0x16914390a06b6b565 54
(.stop 16 0xe5f9e8dd7a0ce0d2798726b7b39d255cbc73139d46d7e85166dd5f16 1281)
(.stop 20 0xce10e2cda40eaed789e8ddc85439dc3987f924b55211ed09858099acd7e8c4e646b722 6573))))

private def tree156_336 : Tree :=
(.fork 5 0x21411f06552c94b2d 65
(.fork 8 0xfc0400f88a8b2a48ec83d88f63 59
(.stop 26 0xd4e9903702b2ed338525d6e077215aa75fb5d260f4d7bd60eda411ca50e991adc881730aac77e38d12ff4c11606 5009)
(.fork 0 0x0 52
(.fork 9 0x5b027d0b2c2ed125d5a696a75cd5741 46
tree156_331
(.stop 5 0x34c25aa76904997721 3474))
(.fork 19 0x1f02e40bb277cf5b61fdf288fe368f251513149292694b9574977ca2288b0b691 50
(.stop 28 0x5d0b38b447b36486538559c1f2c85552057dc814d6646a365dc463f9924f7b45ab5a49da409e12c10ce84e455755f39869 14256)
(.stop 17 0x2970d9c2973e5fd74288bf41a385784b9c1f84c29e0b1331796ad692738a 13819))))
(.fork 0 0x0 69
(.fork 7 0x17a0aac82320989f433d8cfb 50
(.fork 9 0x3da2040b172ca8ce84e453a755d5877 38
tree156_332
tree156_333)
(.stop 19 0x1262debd24fda45138cbdc5a8421342c03605131b906f03664f5e3d9d2695347565 13962))
(.fork 0 0x0 57
(.fork 8 0xf683e122c8f5b3da943350e9870 60
(.stop 38 0xd04e227d9c1deae60538669422bccdce22fd9d5fb5cbd0ecf3365add7a1771958157d55f5b4ca1dd89e63d21aebdca40d805b81710d206e4366526549a54d15a7d6a2 2522)
tree156_334)
(.fork 0 0x0 49
tree156_335
(.stop 3 0x34c93b274c1 3161)))))

private def tree156_337 : Tree :=
(.fork 0 0x0 47
(.stop 6 0xcb94f65da408a82778a79 3936)
(.fork 0 0x0 41
(.stop 7 0x32e444d13014c0b69147559b4 4400)
(.stop 6 0x4c0767a5a756a46b6b387 13185)))

private def tree156_338 : Tree :=
(.fork 8 0x143c9de29e4cfb38cd5fa58499ae 45
(.stop 4 0xd7b96a6da41748 359)
(.stop 15 0x22c9e5f49454b975ef582f72944c1f27da40167204142c5f775fb 14420))

private def tree156_339 : Tree :=
(.fork 14 0x3638ead3d2124f6e174be05dc47b3188d90365909844cb55d 60
(.stop 6 0xd54d610d064f674c01303 3303)
(.stop 22 0xe399c1ed0116abd2a1e8c8b0b683337dae8dc799b2debcce78d8b5535d2186461f1b7e7063565 3917))

private def tree156_340 : Tree :=
(.fork 0 0x0 43
(.stop 16 0xcb8560bd9d4d8e4e1737a83c767261df72603141fb2c40c46618987e 3149)
(.stop 3 0x355436637b8 3470))

private def tree156_341 : Tree :=
(.fork 8 0x2770b123654f4f5cb97486df9cb2 67
(.fork 8 0x27c89f63178ce338bcf6566699b0 42
(.stop 2 0xe389b81 4381)
(.stop 5 0x38e2816772550d77bf 7665))
(.fork 0 0x0 25
(.stop 26 0xdc59f1ee3a1694cdf0ce0d2a20f1d9c973fda0c0c713e4a752c41083618987e72d3554360543558257416e16364 6249)
(.fork 0 0x0 46
(.fork 8 0xb447214389423ad4ece5a51c17 61
(.stop 20 0x72d32d169172f822c4c4446ddf1ee3a130bcb904fb299784c3638d98473930172c5d4c 13652)
(.stop 4 0x77a35e15cd7683 13948))
(.fork 7 0x15f252cd784c2df208153690 34
(.stop 20 0xd4f9fbbd5519a5d78587ee3a1fb1dc35869ded91d558057375cff6833b091ce5849df1 5305)
tree156_340))))

private def tree156_342 : Tree :=
(.fork 0 0x0 41
(.stop 20 0x5cd77b8311b8e16db739114249f250b187766af5650f604742038d813661560d0b51d5 13793)
(.stop 32 0x6db784b7eef8eb6b66535d9ca222e3a19abd59494b35e130b6ba9f2081535e30f789f6580560b5cdd73f5f65c0fd0b4d9847393024e734c5 14561))

private def tree156_343 : Tree :=
(.fork 7 0xdc0ab4a8c2a44d933b1cec9 55
(.fork 8 0x11ec50e44a913a50c543c559d570 67
(.stop 31 0x32d9645349f86322c4e5fe493e3917356de73696e15ded7a1f7215aa573361ddde1d7ed3a150f5e8cd7a4ce75f3590379f34c133e5396 632)
(.stop 34 0xd276701d281b74dc663fae39a05de39156b72ef84766975fb5d0da4f94c35e9692a535e119fb2d59c8123370f484e16223d56526953457d35f63690 7650))
(.stop 30 0xd7d1c11cd9619392578e68176493da1d9afda4112fd7857355d0756733e4f4f5cb974868d74c122a894644c961277c60f3889f692 2066))

private def tree156_344 : Tree :=
(.fork 0 0x0 61
(.fork 5 0x1753638d98473939c 55
(.fork 10 0xcf447b252c95b44a913a559d7385cf9ada 50
(.stop 24 0x5cd72d08fff368643b42d582e22ee12c16711c4d6f5a6d86c61d1c10751355e61fb67961a587768e9a45 13661)
(.stop 3 0x35fb6dfb716 5790))
(.fork 8 0x22c4d7a36451b74755dea7ee3692 63
(.stop 27 0x32f881472cca0f32cf753dde97c7771666b266bd788b123d3d72e706356550df84c386d7db61de49ada1d26649a1e84 6260)
(.fork 0 0x0 50
(.stop 9 0x1269e3ac471497986cd57987eda1d877 13357)
(.stop 2 0x5d235fa 13812))))
(.fork 0 0x0 53
(.fork 7 0x64229fd25e49c169b5a99d44 50
(.fork 15 0x16a27c8c4d31889de2e78d6f61fa05d924f67950b186961ddf15 52
(.stop 11 0x1748e5fcce7dc346362560b1933512f84c2d741 13807)
(.stop 23 0x36768b0b8eb24d8d7a6dfb2d0974336b201494b72e1f20d27df27d538ce7531b7ac57f560f88af55d 6573))
(.fork 7 0x3400d49f64755601582f4ce 60
(.stop 12 0xe381de6926b70e22a9f167ec371d49a54d1641d90e 7030)
(.stop 8 0xdc39f16dc79612d5397486dfb565 5626)))
(.fork 13 0x64922a8b295319f16d3342a627d91d5580560b703f4d1 55
(.stop 24 0xcd9dfbbd53d877e399de2d7bcb195cd5741750f56311ec63825109cf5d2235dda4050e252d56755c1b75 5325)
(.stop 17 0x1b7edc39aeada4046ad7d17dbd54ce1b926b7ad00c033611d09446677692 13669))))

private def tree156_345 : Tree :=
(.fork 5 0x3e11e28bc02f1f30f 65
(.fork 9 0x3f01001790d1cb262cb0ec83d88f63 62
(.fork 7 0xd81454cfd425913144cd267 45
(.stop 6 0xcba0e2f3d80f65da41748 3474)
(.fork 0 0x0 43
(.stop 26 0xd9e80b4e3a25d0d78d2fae38557066d3855580560b5cff69122a094444c1f27924769038bd083427d87e7069de8 3286)
tree156_337))
(.fork 0 0x0 67
(.stop 21 0x354f5a9b6839c1b8e661f36914739f25d2e91ca49a738a2300c6033ef4c227c89f63648e2f 9678)
(.fork 0 0x0 47
tree156_338
(.stop 21 0xb12dc8560bcdcd269da40944277cd813661577644d9add59c64233d8d7b6465cb5753f55d 13955))))
(.fork 0 0x0 69
(.fork 7 0xdf0aac8be23009f433d8cfb 62
(.stop 32 0xdece79fd9cdae8e39108366cb55435b2362e12cd983b113024e71a45da44a8e3134c62667d9abd5940d803683df1454cf438a8e3144c5267 4535)
(.fork 0 0x0 68
(.stop 35 0x37aa8b1f4167075cb9d295e89dea126883d6229d539d567a2a35a8fd337f50df3892a44bc23b1d12fdc94f5e3d9d26549a54d1d59495b2a38b293644d95 1112)
tree156_339))
(.fork 0 0x0 62
(.fork 9 0x3e03600da1454cf433f513144cd267 45
tree156_341
tree156_342)
(.fork 0 0x0 66
tree156_343
tree156_344))))

private def tree156_346 : Tree :=
(.fork 1 0xffd 75
(.fork 5 0x4841934658255095f 77
(.fork 6 0x6083e81e0c790207882b 55
(.fork 12 0x143864f2edcbcb33b4d033620d9e3af956755c1ada 39
tree156_279
tree156_280)
(.fork 0 0x0 62
(.stop 4 0xce5478e2584a95 1921)
tree156_283))
(.fork 0 0x0 65
(.fork 8 0xfc04016cc8ba2310ec83d88f63 46
tree156_284
tree156_287)
(.fork 0 0x0 62
tree156_289
tree156_299)))
(.fork 0 0x0 74
(.fork 6 0xac03eb16c85bc27bc9f9 55
(.fork 9 0x50e1e1cb1c2cbcf593db156755c1ada 77
tree156_301
tree156_304)
(.fork 0 0x0 65
tree156_305
tree156_316))
(.fork 0 0x0 77
(.fork 5 0x3e81e0c790207882b 60
tree156_317
tree156_330)
(.fork 0 0x0 72
tree156_336
tree156_345))))

private def tree156_347 : Tree :=
(.fork 12 0xf74778204cceb3404ff240214ca536156555c9d44 28
(.fork 7 0xb143a8d6a85d11c247cae3fb 42
(.fork 8 0xf107fa2020eca4e256b16e05c1b 15
(.stop 15 0x35d65cab84f029f8ea7a436863b493964e89c10dc8df23900e70a 7815)
(.stop 13 0x349f99bf67942078ea7a436863b493966b6b7235d338e4 2055))
(.fork 0 0x0 50
(.stop 21 0x34002be336d81675505d01911815771b7a1f8e77a236872ca8cd23ae4ed25a616a95ccd743 2515)
(.stop 19 0x156fe39e22ce5f174ccbb9cb98b1f68724e54318da2838e3a92fc4c1d9a56ddb38c 14115)))
(.fork 0 0x0 36
(.stop 9 0x367d3b491c05d0f8e646c93a45d31fbd 2374)
(.stop 28 0xd9c587672b37bf72e5e87cbb1e84e5f2976b1f78e66447728421f7bb24e54316e06838e3a92fc4c1d3974e859a56ddb4b8 9210)))

private def tree156_348 : Tree :=
(.fork 6 0xca46c52c556a97a423fa 28
(.stop 9 0x1119dc88ebe4e5b2f32c516a85d11f2b 13945)
(.stop 10 0xd2e19a5e3a943150f1adadeec58f426f8e6 4069))

private def tree156_349 : Tree :=
(.fork 0 0x0 38
(.fork 7 0x15b3b1907e44655f16475ded 55
(.stop 11 0x38464eab7a8777367f4e587f9669771950c543c 5784)
(.fork 0 0x0 28
(.stop 18 0xcbf512fd2ad914d5406345d0f678a10397d07c845a18addf5da016a85d11f2b 6565)
(.fork 5 0x62b2be108772df7bb 60
(.stop 7 0x371966977a85d0f8e6426e052 5949)
(.stop 14 0xda1c769d509698dc409c43fb771966977a87f1b5de620b720 5015))))
(.stop 32 0x64477bc3d032c85f138e744be2c4d27e6679c0755018d09462e78cd25a617335d0f2f32c517447cae495deec62b29e8ebe5839aee8b17729 14113))

private def tree156_350 : Tree :=
(.fork 12 0x2edcec66475ded7a1f7223af8ed24e593a250c5e7c 29
(.stop 14 0xd0a493cd029879e391c1be11e667e3a9699d9e5dece39a3fa 6420)
(.stop 3 0x3678a103719 8125))

private def tree156_351 : Tree :=
(.fork 7 0x89b421dc1b72de197927b7bb 51
(.stop 15 0x34294c1f8ea8da35d894c367d66b1a47e14591ddc891265839699 5955)
(.stop 4 0x29eb6808da3852 13970))

private def tree156_352 : Tree :=
(.fork 0 0x0 37
(.fork 16 0x2edcebe3b493964e894316b6b2fd2c74f6144d51d15ac59b87a21f22 28
(.stop 12 0xce30b15d9fde87d2a97deda4dfbd94e78517091f2b 4069)
(.stop 12 0xd9fde87dc69ae8d0a59147a438ea3f975d879f368c 5964))
(.fork 0 0x0 69
(.fork 5 0x34b1948b282ca8bc5 56
(.fork 8 0x3890e37474d2fc4c1d3974e859a5 47
(.stop 5 0x38e68b378514ea9866 2836)
(.stop 7 0x3851202354f72e78ea6b6b2f3 5014))
(.fork 0 0x0 55
(.stop 10 0xd0a53aada4dfbde3a8bb7498143150f1ada 4225)
(.stop 26 0xda4df23e3a249ee122704e13cb0ee1413aa5cc174661e991472c32f75aa1c247cae2c7d070bbc3d7909444bf2fd 8126)))
(.fork 0 0x0 41
(.fork 8 0x27a4eb03d2d4235ca974c7071cb6 29
tree156_348
tree156_349)
(.fork 9 0x5112780a7b3d4d7325d117cd5f7b4c1 55
tree156_350
tree156_351))))

private def tree156_353 : Tree :=
(.fork 7 0x43037434b19489f42ca0b2a 60
(.fork 10 0xf7451314708b52f2cf5e3d9d094426d4d1 42
(.fork 7 0xa742c88eb14e253aa5ac5b81 49
(.stop 5 0x3429778a052e399744 4724)
(.stop 15 0x37a85d3370d5075e8ae38912c70937bb3acd25563f991768d32f3 4871))
(.fork 7 0x63e446591d72e5ded888f4be 41
(.stop 18 0xe119cb0dea2220e389aeed0494375a8f8e67cae232e11d0815ca974c6ba2052 5794)
(.stop 11 0x3851692f2f372c38468afb7bb44b169f5a8b725 4693)))
(.fork 11 0x6501decb1d2cc0e2447191d34bf13076697398 42
(.fork 12 0x3a9a496973a976e3988083ac4fe74e253aa6935b81 55
(.stop 12 0xd53cb0bcdae22ca36f97c88838e25ca974cd7ddc0e 8436)
(.stop 8 0xa36f97c68d372849b38e2a0eb7bb 14099))
(.fork 0 0x0 36
(.stop 7 0x38e47c635fd4e9174c77bdf23 5958)
(.fork 6 0x3af8ceb6ddb5f85d1b5ec 28
(.stop 9 0x34be72e78ea6b7397c68d37237cae2c7 3288)
(.stop 2 0x3acf7bb 14120)))))

private def tree156_354 : Tree :=
(.fork 8 0xcc847035f5255692dde77a07555 19
(.fork 3 0xe175a7e197 35
(.stop 8 0xd055a44e12974cd9f5a47deaa35a 6894)
(.stop 10 0x4bd384a5d3370d9e77851499b2df88ab8ea 13647))
(.stop 5 0x37aaaf8b3678aff84d 8587))

private def tree156_355 : Tree :=
(.fork 3 0xd8a6209b89 53
(.stop 11 0x37b75d31f23d091902e399dedd30973bdeed60c 6429)
(.stop 14 0xce2dde2e399dedd30973bdeedc24dedd74c7c8f4243fb7719 5654))

private def tree156_356 : Tree :=
(.fork 0 0x0 38
(.fork 5 0xa703f8d6166475ded 41
(.fork 5 0x6dd22889e95d31d50 52
(.stop 5 0x34243fb77193614d9c 1911)
(.stop 15 0x35d8271371916678e6778b4191d7337018ae49edeedf2b88cb851 5938))
(.stop 6 0x7caf7bb927b848271384f 14271))
(.stop 6 0xdefdc247caf7bb5cef4c2 2537))

private def tree156_357 : Tree :=
(.fork 0 0x0 57
(.stop 9 0x35f85cf5b81dc656a9d32803816ad26c 4077)
(.stop 18 0xd7c974cdedd73d6e078ea585991ddc88ebe3b493966b6b7bb472173b61bf4d1 4077))

private def tree156_358 : Tree :=
(.fork 5 0x5b516fcf6f3fc100a 58
(.stop 19 0x38e6901736e8186234e3a85b31b7cd884e899096431ada751b7bb47211d15cedb78 7506)
(.fork 9 0x3dd23109eb2a18bbc425109b6913398 34
(.stop 7 0x355f42278e29c0b8516956059 6731)
(.fork 0 0x0 49
(.stop 2 0xd779744 5938)
(.stop 7 0x270ce145c24d779426692f55f 14416))))

private def tree156_359 : Tree :=
(.fork 0 0x0 58
(.stop 15 0x342944dd57be399deddc480cf080c5b33b49d46deed1c8474573b 2537)
(.fork 0 0x0 65
(.stop 19 0x2702e14591ddc691d9ce38777204cf49d57cb292f10cf755d339a2310d923651734 14406)
(.fork 10 0xc40322784eb93b491c047656985aa74ca 53
(.stop 28 0xd275e81dc4d43ed9d8cd235b63fbcb76197e3a174c7c8f7bc05903320f34d7d495555c692f55f204cceb3fc90085361f15 2513)
(.stop 17 0x37196e078465cab70d474957457f739a426f55f0cc911957c561677b771a 5809))))

private def tree156_360 : Tree :=
(.fork 0 0x0 61
(.fork 8 0xd0c3e5206cb222cc0ffa400139c 58
(.stop 2 0xdeed73b 4561)
(.fork 0 0x0 77
(.stop 4 0xdeed90fce609fc 2221)
(.fork 18 0xf749e147011d95a616a968e9a456b55adfd3188c4425109b50d9437534739a 49
(.stop 24 0xdea2838e3a9c15d29174c7ee35e56bba2c5da011265a89ae6d77990f865f7bb1b64f5349692745cc9ae0 6727)
tree156_354)))
(.fork 0 0x0 56
(.fork 9 0x64519406ec2c74e2438dd2fc4c1d9a5 65
(.fork 10 0x36c50f16cc8ba2310d923650ec850c943b 34
tree156_355
tree156_356)
(.fork 0 0x0 53
(.stop 2 0xd328d01 362)
tree156_357))
(.fork 0 0x0 51
(.fork 6 0x1b9c947387d12657f960e 77
tree156_358
tree156_359)
(.fork 15 0x1fd119446d5ca974c70735611444b293d4d25a49d17325d13566 60
(.stop 24 0xdef1e92d759f1ce1451326e26059d7799a992838e6429557dd3443dd18f88c42c38bbc425109b6dea052 6266)
(.stop 31 0x397e927b7bb3afb679a5e349c863f97c2701dede39999e7a1342462099badc3878422b4f5642310a35593396429514055f55f4586339a 4233)))))

private def tree156_361 : Tree :=
(.fork 3 0xd9057cdb83 53
(.stop 9 0x341e6de35d42c24eb19016970e399c0e 5004)
(.stop 10 0xdee93ac645f7ab35d191f7a2b8ea6e07851 1901))

private def tree156_362 : Tree :=
(.fork 6 0x2074a7b42257446dbdb7a 45
(.stop 7 0x38e3647f8ea9c3384666699b0 7344)
(.stop 13 0x38e3647f8ea818f8519c338465a3b5de92838e6751b5f5 7344))

private def tree156_363 : Tree :=
(.fork 3 0x1618814b725 44
(.stop 3 0x24a0e398940 13790)
(.stop 4 0x92838e666d355f 13790))

private def tree156_364 : Tree :=
(.fork 8 0xd0c6df33b4d8836793964e89ada 52
(.fork 12 0x5a416c1e108ad27d0ebb3d58f6f559157372ade79 71
(.stop 19 0x397d9c3367c619a706e39a405dc3999ad7d46412a14f6558619b4dc989f244e930b 9060)
(.stop 29 0x36758b3f36e9c338ea224797e888b5f54eb35f43b29b81dc996a975738e73d8124d647f5572a14a972c8112e44d986e61cb566 1131))
(.fork 0 0x0 58
(.fork 7 0x5111e28b1f2cc8bba4721909 69
(.fork 8 0x3743df14706472ca0b2a4249260 40
tree156_361
(.stop 8 0xd750b093ac6405e399f1a83a3691 5004))
(.stop 21 0x37ba4eb3555388784658297427a4b4a23ac51bd5a76405e39900a57f960e6de1d42751b566 2825))
(.fork 0 0x0 62
(.fork 8 0xf603df22dcf603d952675a756a4 51
(.stop 18 0x5d135de69134c075378ea364913a6e078e9033c640251cf5540295fe6415910 14101)
(.stop 22 0xe5f6a0de38d60c94bf2e1473d39b4e754d1d2f0d9442654cc535b72627c8cf433f512a44eb557 9841))
(.fork 10 0xa882a70f7451c2a18a97426d4d15f63398 49
tree156_362
tree156_363))))

private def tree156_365 : Tree :=
(.fork 0 0x0 54
(.fork 7 0x33c1de4d8750c143d61b5873 62
(.stop 21 0x32cd113b8545d138e69017406862b37758159a36dc5b78e3a48b73d8139b4e757375cfd905 1412)
(.fork 0 0x0 38
(.stop 15 0x38519c0b53a86677b46de371d5d137bb5fa574261e9e92dee5ded 4864)
(.stop 3 0x342661eb5e2 5954)))
(.stop 17 0x37b44e3368f72df7bb62138e3032c51118f8a7b422512445017446dbf55f 3936))

private def tree156_366 : Tree :=
(.fork 7 0x20f2a14b202cc912e44d9b79 36
(.fork 5 0x3cc3d8124d6211f23 65
(.stop 16 0xdc4c88949638e777df5455599c0f7ec739879e5f15e5f526a5f397dd 5773)
(.fork 0 0x0 44
(.stop 18 0x2c077bb8dab8e72ebd258dc4c3c16e2f85127674b538e739811a0d7d4eb1f1b 13789)
(.stop 11 0x37bb2e9f71b361f39855938e546f91db5f7f68e 1588)))
(.stop 4 0xce6126755cf557 3463))

private def tree156_367 : Tree :=
(.fork 19 0xce08183cc1410a6e3d8124d621191f7c8f55c1de4d873888e3950c1c0f79ef566 39
(.stop 20 0x2c4768e7a1b36a6411e92925b8e7928367a7eeb545816741c448f7bb18d08a05acd74e 13493)
(.stop 27 0x385127232c94e075de77df5ef0c649c272df8e43b19119d9e9fc897334b5365138b509b7b946f51db496186661eb389 812))

private def tree156_368 : Tree :=
(.fork 0 0x0 54
(.fork 9 0x6431de4d87388943050f556655c5c0f 36
(.fork 5 0x50444d1884647df23 51
(.stop 23 0x354583fb5de18a49d1928367a335b5dca5e397e5d3b7bd270b8e405a03db11dc89d3fc15fe5d09de0 3913)
(.stop 2 0x5d3b5fb 13818))
(.stop 31 0x3400a37749e49a96066422222d571130d7b9f2de38e52fdeede8894ef8e705a112345008a02c7d7285d39e86dc8d1db5f7d902644f4c0 1570))
(.stop 11 0x34c0476f683499139cdeed1d14bf93055cef398 1596))

private def tree156_369 : Tree :=
(.fork 8 0x141050d1de49f6361ce3950c143d 52
(.stop 12 0xd535cb9d514e17448d73bdeed30950b987cd55cf6f 3926)
(.fork 0 0x0 28
(.stop 10 0xe129258619987adc8c33311df55761f1d5c 5956)
(.stop 8 0x77835574c277bb72df4c0476f718 14096)))

private def tree156_370 : Tree :=
(.fork 0 0x0 58
(.stop 3 0x37bb474573b 4552)
(.fork 0 0x0 62
(.fork 7 0x8b723189dc38c4f603d95267 71
(.stop 23 0x3374755b41488d353e0ccc4fe41fdaea754b8e66b874bc33d046111a48ad5fa5e88deecf4f5cb9748 7665)
(.stop 3 0x37186443557 3951))
(.stop 15 0x356666d37bb337f69222e1132cbf912eda008ad27d0f6f5593398 5956)))

private def tree156_371 : Tree :=
(.fork 0 0x0 60
(.fork 9 0x3dd14709eb27f0a862a5d094426d4d1 71
(.fork 8 0x84c34d192478a27c89f638a0e33 45
(.fork 6 0x3d3d2f14eb172e66c1de6 34
(.stop 2 0xe3a9df1 6586)
(.stop 21 0x38e972c9fb9d0817e9e5f4925dc95618d77a19988d38ea13c4f56dc5a405e399d5c83e354b 4711))
(.fork 0 0x0 51
(.stop 28 0xd77a535dea23f4e3a8459deee2cfd2920f4da446352c55d5c8d837ba7a4a2c9d7b92675f8e22ada20f6f3fc13924e99a44 6741)
(.stop 15 0x38e988bb7b17a075fb6b872f766a5ded90178e666d1c1c814b38d 6115)))
(.fork 0 0x0 51
(.fork 8 0x251cf6f3fc100a57f960e68eda44 44
(.stop 23 0x9c2dc3987ada4463e29ef72518b8b0ed77a059e3a987372de36adeec3cd0f5094035f4d944eb1426 13031)
tree156_365)
(.fork 0 0x0 54
(.stop 32 0xe5f6199def57cce5fe52fda0125861eb4ab338dde6d7bcf6025011c84c0174477df7bb621191f7c8e359d570779361ce2250c143d61b5873 3908)
(.stop 35 0x370e81678ea61a397f4e6f5f44eb199a66c368f72df7bb621191f7c8f8e346f59a990178e6814b561144463e2074a7b42250a544917325d11b6f6deb566 1256))))
(.fork 0 0x0 50
(.fork 9 0x9e127c8b2a3fbd00a42290a55a616a9 61
(.fork 8 0x18fc95125849ec3fe90004e71a45 63
(.stop 14 0xd7799a266a355538e77ab8aff4c0643f7bb1dd48b84999911 5947)
(.stop 23 0x1fb8da497ddd059e82d779258dc6dc26def4e395f673985cef7bb621191f7c8f4c03aed7df7a4b5ef 14256))
(.fork 0 0x0 59
tree156_366
tree156_367))
(.fork 0 0x0 65
(.fork 8 0x36c0dd0d346e91e10d923650ec8 62
(.stop 18 0xe38d910d57139c50e37bb448cb1f7a1b723476d9136b4f4c03d80f654265267 3925)
tree156_368)
(.fork 7 0x951338d2f14e313ac66c3565 54
tree156_369
tree156_370))))

private def tree156_372 : Tree :=
(.fork 4 0xf309d3493526c 21
(.stop 3 0x35de49756a1 2829)
(.stop 7 0x36756e1b7bb423f5ef66c38ea 1899))

private def tree156_373 : Tree :=
(.fork 13 0xa6a447986edc6876822b4cdb36351b34745b867a23729 57
(.stop 5 0x3710692f54a5ce973c 4716)
(.stop 12 0xd085b81e3a8ec8d779d4adc4c76224db54a692f7b9 5496))

private def tree156_374 : Tree :=
(.fork 0 0x0 59
(.fork 6 0x83ce2738d112e44d9606 50
(.fork 10 0x14245122784ce84e453a75a616a96dc1b79 53
(.fork 8 0xcec3410f74b1a47594d866899a8 36
tree156_372
(.stop 3 0x34213d6f557 2059))
(.fork 0 0x0 45
(.stop 8 0xdc49f1ad5283ccd55c80b338cfea 3290)
tree156_373))
(.fork 0 0x0 58
(.stop 12 0x7c6b722475b68c14440d31b7d86edeed1c8474573b 14098)
(.stop 3 0x34be49ab4ca 3474)))
(.fork 11 0x1fd119446d49c75611444a7b2ca4d99510b566 50
(.stop 8 0x423f5ef5d034d161e36814e453a7 13054)
(.stop 3 0x368861e34ce 2699)))

private def tree156_375 : Tree :=
(.fork 4 0xab8655255c95c 69
(.fork 9 0x4303740df05e882320989f42ca0b2a 60
(.fork 8 0xf74d8d3664f5e3d9d094426d4d1 28
(.fork 5 0x94044b20f98b1e3fb 47
(.stop 9 0x371694db7ab4b9de8adee574661e9cb0 7041)
(.stop 20 0xd28d112d4e801a88bf716a35797d494b72550f586d61cd908d2f900244d956b581b42c 5149))
(.stop 13 0x32f661eb7167a2b6933d6d30361fe22ad071cb777bf7bb 6259))
(.stop 43 0xfd8d019caadeadc1e9e775de70623f7dc603b461ea3fd94c771661fe22ad0716105f9205b863f4b03acdcb777bdfc399b37bb4c2543050f73921b84e193fa96935ab986461f199a66c3565 13000))
(.fork 0 0x0 66
(.fork 18 0x11d894627849f233a13a75aa57335d0f56501040420d209f127dccf833e4d93 37
(.stop 12 0xd4e52716dc9e79dca05ab3d6d26cd7bcf616e19e88 4701)
(.fork 5 0x14cb706dcb77f0f7bb 57
(.stop 15 0x3729751384872f1fbecb85e8de11527179e741c3d6d26249b12fd 5152)
(.stop 12 0x708797d58199a26de75505d01f15dca4ec6691f5ef 13336)))
(.fork 0 0x0 71
(.stop 24 0xdc65df1d070e173d3f7bb16609df2c554ddce486f005e4b2c27994427c874c23648ec8d32878a27c89f6 2842)
(.fork 0 0x0 54
(.stop 47 0x32da66c35ef1d78762692f71035db67e2c35cb7d779e88e5f4ea96dd770d7c574cd0818ce84e9d6a96dc1b79da4cf5b424d57361fe22ad55c20f0a84e2744b9606642190dd5707792a00a9244a513b50c143d 7046)
tree156_374))))

private def tree156_376 : Tree :=
(.fork 0 0x0 57
(.stop 21 0x2702e14218ae3a1c1ce3a5fc2dea1de2925b8e65d11d4075232f216acb0b3fd926c66919a6 14406)
(.stop 14 0x66978ea81638464e6e2bededdc20d30574466d38e6925b5e3 13819))

private def tree156_377 : Tree :=
(.fork 0 0x0 56
(.stop 20 0xded99b4e39a496d78e972e5f8ff644b960e817771a7c8b7215835c11e1453974e859a5 8894)
(.stop 3 0x371a669b5ee 4086))

private def tree156_378 : Tree :=
(.fork 9 0x3d82c54d8136615775f7d9026b4dae1 28
(.stop 14 0xd29960ecbe509b7549e86e12987a66b9b7cda3c5982771090 5626)
(.stop 13 0x397d66b9b6de38de8ccb85f27deec4fe3d25aea7a1b8e6 5626))

private def tree156_379 : Tree :=
(.fork 0 0x0 45
(.stop 18 0xd779b7ce38e223deb53854e9b3825359adadeec9dc2eb4ce33d3d7486b91cb2 6574)
(.fork 0 0x0 51
(.stop 15 0x19aae5f55fa66b9b6de3a560966973864e995fe58397426415910 13478)
(.stop 25 0x1ae6e5f5adacbdd73dd276665da29e8ce3a4e333638e12446538577b5f21ce09094426d1ca473d39d534742d 13185)))

private def tree156_380 : Tree :=
(.fork 9 0x6452770ce33d3d72e5d2199a66c1cb2 34
(.stop 25 0x38e2755b2d429af68329db4a481538e6274539264432f72038ec23fe88ad3ab0ec57a237bb4e8961277c6059 6886)
(.fork 0 0x0 42
(.stop 26 0xcb71e8cdc54595e389e827c7753e0f349cad2f016224b9de6d778baa3ac511d22b4ec57a237bb44e99196e05e83 4866)
(.fork 0 0x0 26
(.stop 34 0x755b8e21b24a6bd53de82cb2a2c5d76943666819aa779f8e63fa73866e165cce38d910cbd863222b4eac46cd41f7a237bb44a987a6459aea8b26531 13012)
(.fork 11 0x88b22693929e8771e0cb4b194451e8c83d3726 44
(.stop 18 0xdeedadacb28f45d015e807c6f7ad53459b1e38c80d3639301779f8e63fa5d4d 189)
(.stop 9 0x37bb7a234a47a0354b4c078e677b7386 6258)))))

private def tree156_381 : Tree :=
(.fork 0 0x0 43
(.stop 6 0x2c57854498969fd7ed09f 13044)
(.stop 29 0x3364925354b708397d88ab8e988ba5cae5fd73d77c6838cd9569f5a8b38b66d21938fef8e63f79e8c83d2228e11d91370272f3 8130))

private def tree156_382 : Tree :=
(.fork 6 0x37c2131e289f227db30f 66
(.fork 8 0x1040420ab4a8c2a44cf833e4d93 55
(.fork 8 0x252d12a44e93964e8943150f1ada 38
(.fork 7 0x81244651364e99b8577b5e87 33
(.stop 28 0xe3a9d48e5fe8d7d0060efdc64fe5d2f1b7a7c89fbea8378e97f0b7a85371e7ccbc98668fea4969c1b8e60a313804e85e8c 5796)
tree156_376)
(.fork 0 0x0 62
(.stop 24 0x27378ea5a7f54b4e774bc61af53942414385aa38e66199b6d6df32ee33d0cfd3d80f653fed2675a756a4 13186)
tree156_377))
(.fork 7 0x64938a0e33426d12f44d7565 51
(.stop 13 0x37293d974c14c1b41c66a5d5177b605de39a706deed6a8 1733)
(.stop 12 0x6ddf4c166d38e6925b7bc08208124be160d66a72f3 14259)))
(.fork 0 0x0 62
(.fork 7 0x2a91454cf433f4f603d95267 65
(.fork 7 0x1790d1cb2c3648d944259099 48
tree156_378
tree156_379)
(.fork 0 0x0 45
tree156_380
(.stop 4 0xd0b45af36634c5 60)))
(.fork 0 0x0 65
(.fork 26 0xa9c3dd1924cdc38a0e33425109b472a223ce781792cb0d8e3f8d11944d93854e99b8577b5f21d308d923650ec8 45
(.stop 23 0x1fc2e3a622ee5fe228d9f1fbce3912625a7d6a27ed32f7166109066d2193e39972e66699b06b91de6 13158)
tree156_381)
(.fork 28 0x2c3ceb100ec3dd142864929d0e2838cd094426d43650dd4d1ce78f66447513a6465b817c774c23638d983fe90004e734ca 56
(.stop 14 0x8afb41688ab8ea5a7d90fcb64b0eda11e8cd53d09f4c1d69e 14562)
(.stop 6 0x11c35f461c384a9c1b84d 13047)))))

private def tree156_383 : Tree :=
(.fork 10 0x8802318c07732edcf453f817e78b0235a 74
(.stop 16 0xe60283fcdb9cbf8183855315a2328b3371b3401606d7f50a2537d6b0 9374)
(.fork 0 0x0 50
(.stop 6 0x1d4784b384b2cb667da3a 13001)
(.stop 11 0x37ad88cb85513edcb2dea9874d7f47716477726 2046)))

private def tree156_384 : Tree :=
(.fork 0 0x0 59
(.stop 18 0xe606232e3ae3f5dc363f6dea86e63b491c04765a3ada3094f31594355819de5 7957)
(.stop 24 0xdc367a5d9c0d68dc6ced2da14939e391dde8fdb7aa02f8fdf8fd75550f3c471274d008428987475135f1 3769))

private def tree156_385 : Tree :=
(.fork 0 0x0 50
(.stop 29 0x3684276f68e88932c99e933655f65c0f79ef981862755e1dccf456bba35ad794d0042190a2449d4c3cc188ba3ae4ed24701a3a 2998)
(.stop 29 0x38eb708f2dd66e34a553475fd223892a2e6b98111a991d862755e1dccbb73d15aeed794d0042190a2449d13d530f30644d368d 5653))

private def tree156_386 : Tree :=
(.fork 8 0x354209083463b2a0d6045821870 71
(.stop 19 0x19a7d0494e0693f4a472ef8513d7156a5f5b559205cd8e3660eb53fd90045a516ad 13327)
(.fork 0 0x0 60
(.stop 4 0xd7957e1cc1881a 3455)
(.fork 0 0x0 54
(.stop 4 0xd9dd7d25f65c0f 3949)
(.stop 4 0x194b39a1e035fd 13062))))

private def tree156_387 : Tree :=
(.fork 0 0x0 58
(.fork 10 0x5bc6521b5878a33c0d0155a956d5cede7f 32
(.stop 26 0xe605a3ada4de82cb3de8fdc4db7b75275fd5a86368d9f91ba49d155c7ed77282068bca362d086530d91ccc19130 2818)
(.fork 4 0x1b64c408893558 60
(.stop 22 0xe3ad55dd0a5e81cd9c88d270d1c0900f676473c94f4c3d5f6e6017e7d9f8d7650dd605581dd4b 1892)
(.fork 0 0x0 44
(.stop 19 0x38e77a435e06bbb67e7a1b42400ac160190d30f5859c1ae11930568d9a49cc19615 2835)
(.stop 9 0x130fe6017e7d9f9a497a1b306537f728 13496))))
(.stop 23 0x37b7a5cb6858d6b97e1fd77b666e355d080846a3144c663db57d25f6739a0f5847111e4ff2428b562 7200))

private def tree156_388 : Tree :=
(.fork 7 0x8a727b912144f94285115cb1 77
(.fork 7 0x182120496127b09fc4bc9311 65
(.stop 25 0x38e5af93980703f3984c17847555d74edca05b3402112345011be4bd130f644f4b81e10b132c98ec844c1134 9364)
(.fork 8 0x1e28d8e3660eb53b396945ab7306 52
(.fork 12 0x59850b3614d9c3aeced43d5908c4be130b641990f 35
(.stop 10 0xcb6e232cda9738d9d9a3adc999ba6bb9d56 3769)
(.stop 3 0x342066e3381 5185))
(.stop 12 0xd0819bada2da4fd2e188466e368e3678e2238e7398 5185)))
(.fork 0 0x0 62
(.fork 9 0x3c11c851e1e04a882a553014c09c17 36
(.fork 8 0x1658cf03aacec43d1913488962bf 35
tree156_383
tree156_384)
(.fork 0 0x0 50
(.stop 22 0xe5f1435dc3591ddecd69a9e9767e274908688cb5e0033033a423186b61d5e79dc60ed247011d9 3744)
(.stop 6 0xd7b1c1ad780b104c3f68d 2383)))
(.fork 0 0x0 52
(.fork 11 0x1660cd033a142c9f43614d9c4231906643de79 71
(.stop 24 0xd02dcbbd27142cd7589db3f61cbfe12c9e55f49c0fce683d629fcff24289d44777b55e3638d984be1694 3755)
tree156_385)
(.fork 0 0x0 57
tree156_386
tree156_387))))

private def tree156_389 : Tree :=
(.fork 9 0x1710d2c6e71dd49fa3d1d132499a0f0 74
(.stop 11 0x191de3817dbd790f524bd368b2ef4bca57c1615 13490)
(.stop 22 0xcb225c8d9c4d77585b97e6685d437515e79d790b0e475574c7a12052dc98c515a717d9703f4c6 6406))

private def tree156_390 : Tree :=
(.fork 0 0x0 71
(.stop 10 0x6e277bc75534c616e478a2794d8e38a1441 13502)
(.fork 0 0x0 74
(.fork 8 0xd447802ef4bca315cc655855a52 50
(.stop 28 0xcb35906e6007f3cb7160861c355e02f880233c0e10694f84d3d175e588ca5d3e605b89d9d91c0496d27368e9a456b55adf 3908)
(.fork 0 0x0 43
(.stop 13 0x384a61c3567643f84d6e2768b119cd8b3d1742358596b0 5622)
(.stop 23 0xbed9f6403cdb6976e604d85449d9a9e6019b7862755902f4937362cf45d9dd1c166a9a3b69132ef 14420)))
(.stop 8 0xd791870d58865225249f43d7b306 5794)))

private def tree156_391 : Tree :=
(.fork 10 0x60835116e47802ef4bca33c55f05855a52 36
(.fork 15 0x230090eab082447124e49d3340508d61d35fd44d16b0694e2bf 50
(.stop 17 0x367d056876be6011278b333659c2aa11e3a87689e9683fd9f87756915f15 3910)
(.stop 9 0x1e7adedd881cbb9fba9c2b8ea5d0368c 14562))
(.fork 0 0x0 65
(.stop 8 0xe5f25d3d78108c449f4b83b21fbc 2514)
(.stop 6 0xdc61740d7b186c61d35fd 4236)))

private def tree156_392 : Tree :=
(.fork 0 0x0 53
(.fork 10 0x82447124e494933acd013fc900861b1874 52
(.stop 24 0xdeaa18bcb26225d7989d229fcf453f838ea426530261ae18ace68034142cd853b5108c6419dde777de79 8431)
(.fork 0 0x0 62
(.stop 21 0x370d8fdb7aa5f4a7a5d9dd99f6915f15da140230090eab5d3371800f451e2584a884265301 3769)
(.fork 7 0x9e53144c6638e57d2703f398 63
(.stop 18 0xe151fbadc5a232e5f17c45f9f980337d74cdc980d9169c7753d1d1325a71740 1745)
(.stop 4 0x44d3718140f67e 13062))))
(.fork 10 0x940bf030463f2a0ccdd55ed88283bb690 58
(.stop 13 0x17d9d7f5fbcdc6050b253d30fda4c78a27e8b0c2c7ccf0 13957)
(.fork 0 0x0 62
(.stop 20 0x61d72f66443414534b5eb88cb9813145079dc94a754c3f68c00f451e25850994c05302 13957)
(.fork 0 0x0 54
(.stop 23 0x1079deda232e39dfc6d79169cda15884d2e06321da88065d09aead069571d080c664c257d25f65c0f 14253)
(.stop 10 0xcc1939ed069cc1d2d8f564c2f39812074be 1924)))))

private def tree156_393 : Tree :=
(.fork 5 0x9c2274d1345d31def 35
(.stop 8 0xdc6cd78d9c973fcbd877324dcf45 5943)
(.stop 6 0xd9ddc0fd7f494f4c3f68c 6105))

private def tree156_394 : Tree :=
(.fork 17 0xc513198d873888e393db57d9703f398060848125449ec27f11238b3e36a 32
(.stop 21 0x20fed515425d295d50e39d734dc603c13374f495d39882dca11344e81571cc1926872fdf27 13334)
(.stop 14 0xe39d7426ba9e92d069571d08174c647f38018fd74e620b690 1420))

private def tree156_395 : Tree :=
(.fork 0 0x0 57
(.fork 14 0x82420d2a0cb0b44994ce5819fc68b375e436296045a7d870 74
(.stop 27 0x355957db2cd3d077133d1797c88cb8e749d1de7dc811d55d31fb888836844be9a3e6905c0fce50f52496df2a8d9e538 3621)
(.stop 5 0x372077bf3067c9f690 3788))
(.stop 38 0xcda1e82cbb6055dc35a45dedcb073fc986c61d1caa75136906208a6e3144c663db569c5a9739a708e3f5da491345d31defd2e09db29dce1f50ddfc6d54d268691f55d 6404))

private def tree156_396 : Tree :=
(.fork 0 0x0 55
(.fork 10 0x5bc33d16ccbb72f2cebe3b497385cf9ada 62
(.stop 27 0x2232e605874dea86c98fdb71d5d32225d7b17d9da1494f29d52ef57d9616da3003d0f6051e2584a952cbd3015a756a4 13803)
(.fork 0 0x0 54
(.fork 10 0xd4bca3144c6636797d25f65b746dd5c0f 71
(.stop 30 0xcd9e23294e785597532c8666397e3671ca8750dd4579e78e8420d2ef57d9862d5652685d21cbf7c9f690252c9e53638d9844a91d5 9060)
(.stop 10 0xcdb96086693716620b69049a1602582b677 5636))
(.fork 0 0x0 74
(.stop 27 0x38e75f135d494e670ce3aa061d2c974e620991c83bb4243dbf69316e4b1c142c64c27d0d85367108c44f5cabce50f6c 7826)
(.stop 8 0xd2d9882da40ed43d5b398362339a 5966))))
(.fork 0 0x0 37
(.fork 4 0x1b64e1166e2224 60
(.fork 11 0x3b00f08b523109fc2ef0d7650d943753462be 63
tree156_389
tree156_390)
(.fork 0 0x0 74
tree156_391
tree156_392))
(.fork 6 0x310d73b643e197927b7bb 62
(.fork 11 0x3c00f451e1e049612a20a95499d3014c099ab 36
tree156_393
(.stop 17 0x3388314591ddeb8c44900f71877a368d4499606707b5e435e188283bb728 4879))
(.fork 0 0x0 77
tree156_394
tree156_395))))

private def tree156_397 : Tree :=
(.fork 9 0x2302f477535d8e113d1d61583c2224 40
(.stop 9 0x38e07cab84a691368b5f638e93641444 2051)
(.stop 16 0xe606231d4f222ce3a57d8e601a44cbc925472c2538cb2a189888f386 7818))

private def tree156_398 : Tree :=
(.fork 7 0xecc46e91d85855cb3779de81 43
(.stop 19 0x173eda1173bcb42231dc50cdccb9880d3fb14295111ae2d54c02a49516b07a09f1c 13796)
(.stop 5 0x370f5caf5535113727 3139))

private def tree156_399 : Tree :=
(.fork 8 0x142cd933d9d25449cd6b07a09f1c 57
(.fork 10 0x202477235cf5e427a1604582169f5a89870 56
(.stop 6 0xcb497395cf590a642d9a5 5790)
(.stop 9 0x37bb1b4f8e34c39b7a444f70c7503854 1753))
(.fork 5 0x1ff1dc8fec5113567 55
(.stop 2 0xd79173e 5944)
(.stop 11 0x37bb6dff7b972d74b247291cf33735e466bb684 5653)))

private def tree156_400 : Tree :=
(.fork 0 0x0 38
(.fork 9 0x63e2a08cdc35dd09a55e99b78626223 57
(.fork 8 0x8346ed27a0e2558116085a7d6a2 51
(.fork 7 0x50a47059a066a9a3b7031c12 34
(.stop 11 0x38e372c340c6bb7981751b980449de8fcb609d1 6566)
(.stop 8 0xcda1d46d9f4b052e8370c7c535e4 6566))
(.stop 2 0x56371f 14108))
(.fork 15 0x15827491cf5d2f7b911c080427d0cea449d906643d9a166a7563 29
(.stop 13 0x336768ef71c2ea38e972c37ab1164d7638477bb3d65aed 1259)
(.stop 15 0x34c7511371c66832cf3f7f541900b7ab3840eabda35a3aa36b981 2844)))
(.stop 2 0x389755e 13657))

private def tree156_401 : Tree :=
(.fork 12 0x5b572b5d2df1dd0a847111e50a26dcdc0e7041d44 27
(.stop 6 0xcb25dded79076b3cf5c23 7181)
(.stop 5 0x397c57c384c51138e7 2364))

private def tree156_402 : Tree :=
(.fork 5 0x80d3fb14447059f18 45
(.stop 34 0xdead608d50591ce11e225e6052ee752b2d03aacec48aff7105855a52deede7fe60173b61bd8717791f1ad5500c711c463a2504951448113d5575d4c 2345)
(.stop 33 0x39809c2753c18c06d6deec9295a877aba5d7981647daed8aff41e5d1b4275d2f7b0779354505a833818fc6e63878e36496d27368e9a45751f565 7185))

private def tree156_403 : Tree :=
(.fork 8 0x5bc33d2c70b2f3d657385cf9cab 77
(.fork 7 0x64f1e109ec3620ebb3d58f6f 39
(.stop 13 0x337822734b214176793d1574b66eb717974f8e75acd74e 1896)
(.stop 7 0x371c58234275d2f717530f854 2536))
(.fork 0 0x0 57
(.stop 23 0x1c23d505615ce0591cdc91f14e5f174b7c775fd42699b7d564209083429f27a0e2558219a46699b77 14111)
(.fork 4 0xc863f387b686 66
(.stop 5 0x341b5d2f7175ccd743 4245)
(.stop 13 0x371c620741b5a9f5f25d2f7bd0cc8804275755e428b854 4400))))

private def tree156_404 : Tree :=
(.fork 27 0x20d229d4c3537dcb1deec8112554ec844c11345a696a75cd1742d59403200cc8bb366cf6f47051d866819aa7c534cf 42
(.stop 10 0x201397c6df32d16441c17def574b72d5f1d 14421)
(.stop 14 0xdead910e3a4769e13080de3adf2ad504a6cdc306303d17693 1875))

private def tree156_405 : Tree :=
(.fork 7 0x3d035c0d92a251324999268 40
(.fork 10 0x27a0c4335e4d903d9142251118817c7e053 77
(.fork 3 0x9ec57cd6b3 58
(.stop 15 0x1884deec6d3229f6737a0b7177a4b7b90a9494e2ee8d8b366d434 13336)
(.stop 26 0xd02e671d005df47f2397c61b18747511f15def4f453f86055d9e57386b69ddcda487753878fef402908a6447394 3929))
(.fork 0 0x0 42
(.stop 27 0x397c7ec38541fece13cb356915ac371766ab36e58297385cf9ada70436761dad0a25cd974061b1874d7dd74b77a5f1d 2987)
(.stop 28 0xcdb8755cb26492d9cc75a227e2cce3ac9dbd9d9cb1deec7752008e1e6411f15d594b1c3f862bfd7b174061b187475135fd 5942)))
(.fork 11 0x9db27b0b113b311ba47615f75855cb3779f4c4 55
(.stop 35 0x22bccb21f15ded893be129cb1cb39adc813f54988c77147041d44d7f574b889a35acb859b78156189e39c33d11cc6391910b1c3d6560258297385cf9ada 13796)
(.stop 8 0xd54d604da10d8b5d2f72749cf565 4076)))

private def tree156_406 : Tree :=
(.fork 5 0x5b91e0078d2ef4bca 60
(.fork 9 0x3b00f081a27f0c57319543650dd4d1 63
(.fork 10 0x36417105d064c2a24a9444c926649a1303 35
(.fork 9 0x80f362ceaa3d1507b5d2e2268d6a3f4 37
tree156_397
(.stop 19 0x3386337371c88c79817caa669d058f6777bf68424dd25bdeec4733fb14446b8b553 3788))
(.fork 0 0x0 44
tree156_398
(.stop 21 0x34ae974f8eb7caa22ccb7dfc0da2d7388b337147c7372735e6231dee4c45470560564477bd 7353)))
(.fork 0 0x0 58
(.stop 16 0xcb616085f557d661c37bd5855a52deec16f11f8d8b55a9605581d73b 5636)
(.fork 0 0x0 43
tree156_399
tree156_400)))
(.fork 0 0x0 56
(.fork 10 0xa8c2a81460a822a50ebf3b4569e5a8d9a5 55
(.fork 11 0x3705bcb1c2cbcd033d657385cf9a3f6901ada 53
tree156_401
(.stop 32 0xc6f2ce298b67322672e5115c7ff5f5f40457df6797c7742a00b45052c014df7ecf5e4708f8e55111c167c63567142c76e1deca755a4755e 13477))
(.fork 0 0x0 47
tree156_402
(.stop 17 0x1447d59d86f642dc17dc4df1bdca05a01dc50a2537f7bb33c4d005f5f4cb 13637)))
(.fork 0 0x0 52
(.fork 9 0x50b19309f433a8d00449d13d641990f 55
tree156_403
tree156_404)
(.fork 0 0x0 63
tree156_405
(.stop 2 0x22d34cc 13512)))))

private def tree156_407 : Tree :=
(.fork 8 0x277d12345011be476d9136def4c8 55
(.stop 17 0x336579fe04dda4063f6915c1377875ee2ee92fe55b590975273983679f17 6729)
(.stop 19 0x38e72c4f7bb275371830f384779ef5fa05a0336190d571703f3982c7cf495d3b728 2512))

private def tree156_408 : Tree :=
(.fork 6 0x146c95b3d7cf664bed308 39
(.fork 8 0x11ac63f3374e2b5acd74e72e20ee 48
(.stop 18 0xcda1a4ce1427a7d008fe655655f4d07543ed790ebb61ede928ff37bc5d15b6e 4542)
(.fork 0 0x0 52
(.stop 10 0x530372433934b60a35cc1def0ebb3d58f6f 14100)
(.stop 12 0x86438e33884f3fdef08073f9b71d5821a4c7f234ac 14416)))
(.fork 0 0x0 46
(.fork 8 0x1414646229cce449d92f261edcb1 51
(.stop 4 0xdc949e23d5500a 1445)
(.fork 0 0x0 48
(.stop 17 0x336ca5e367988ae7a7dc3d90fe144a757cb78e3200113250fb5555d15f17 4542)
(.stop 10 0xe5f1f1fdc51c10dee52665829b6c6df7427 6252)))
(.stop 3 0x355550fb690 3617)))

private def tree156_409 : Tree :=
(.fork 0 0x0 68
(.fork 8 0xf7851b16d8a7c3d7cf6657f560f 34
(.stop 33 0x32cb27137aa1db9cc188af68e62122bfe3a5f2d925f7b0364cba988d279ed7754255301e82d2fd132032864649d92f2619587bda4143e6955fbf 1260)
(.fork 0 0x0 48
(.stop 28 0xcdb5c11d511870e39d6187a1338349b569edc3d99bda41740d52da47d2fcc5f364d09542697335d0d86761e75555d15b7b 6417)
(.fork 0 0x0 37
(.stop 20 0xdea2490d06dcc1dee9258dc51a4cdc9d6187ee368b5d0f4271dd4bb949b57e96211dee 5157)
(.stop 6 0x339369055cb5557307687 13648))))
(.fork 8 0xaa04761ba8946425509a5d0f308 63
(.stop 5 0x37bb691f6873d85266 202)
(.stop 15 0x369258638e78dab7bb49db7bc730635fda00bb9315160461c35ef 4571)))

private def tree156_410 : Tree :=
(.fork 7 0x3c1690ff940054375345ad5 34
(.stop 8 0x9c0f8515a8f72761fb98124d943e 14407)
(.stop 17 0x266bcb25d4c7799fb4d274eb55a535e45a89ca6813f70d6665de77a07692 13956))

private def tree156_411 : Tree :=
(.fork 0 0x0 57
(.stop 23 0x1b82e118cde3acb5da75337bc584b2e35ab769049c34ac5a8dcbbd9c8ff640111c758116087299cad 13966)
(.stop 21 0x336c7c7b9814c09cb2d5386ca24d943ed52c02c00b4ce45a5186561ef7bb3d3d916753342d 3140))

private def tree156_412 : Tree :=
(.fork 9 0x646229cce43ad4ece5a516ad61edcb1 45
(.stop 23 0x35da40078e844cb2df81773715825c17d53926d5a796a3cbdc02d11c494135f8f4f5cb97486459d4c 7817)
(.stop 9 0x1739cbdd43e584b72640054365347565 14109))

private def tree156_413 : Tree :=
(.fork 0 0x0 62
(.stop 8 0xcbd969fd594f4f50bd603deecec5 3635)
(.stop 12 0xd7916a261c37263d78ff94005436ce388c03b334c6 4408))

private def tree156_414 : Tree :=
(.fork 2 0x2c656ad 32
(.fork 4 0x811305d21f27 55
(.stop 2 0xd79173e 5944)
(.stop 2 0x51077bb 13669))
(.stop 10 0xd2f1b7fdeed09944d35650cb463f252f690 5635))

private def tree156_415 : Tree :=
(.fork 10 0x142c81729d4b10420d09f6189de87a0b554 32
(.stop 24 0xd01266bdea9e83dc587fe72c75e45ce173ed595a457c9683cd9ccff866cb42d18e08a8444d1305d21f27 7508)
(.fork 0 0x0 36
(.fork 5 0x3cc3b1113472ee2bf 45
(.fork 3 0xc513ec504 59
(.stop 4 0x77c72de5349606 13021)
(.stop 4 0x5a777157c777bf 13048))
(.stop 15 0x1f1ddc74c44cdb2054da40ece534986e61cb6735a757385cfb565 14101))
(.stop 13 0x32dd581b71435e2054d78d7d9d0b402b276ca763b334bc 5951)))

private def tree156_416 : Tree :=
(.fork 17 0x16e1b54b1938356add564171082420d205cff64011604582169f5a89870 56
(.stop 11 0x34be55d78e964672db7f0b2d85a8d7395cf590a 3934)
(.stop 9 0x1fc2e3a59a6deed44155d72f264677bc 14257))

private def tree156_417 : Tree :=
(.fork 0 0x0 63
(.fork 8 0x36447b3168c6244c926649a1303 37
(.stop 16 0xdc520f8cb7a49adc5990ecbdc64122c4b0edc996add2f89e570820f0 4720)
(.stop 13 0x32e35ab74c6475768499af84b2748c4250bb85566a7553 2525))
(.fork 0 0x0 53
(.fork 9 0x3d611c447929fd27061b19076439d44 56
(.stop 21 0x38ea7c72228cb28fde41e797e7c774c22794d76507d44170822bee1557395cf59a56dcdb76 3596)
(.fork 0 0x0 50
(.stop 2 0xe155a45 5185)
(.stop 22 0xcb3e2c3dc520f8e13530bd9cde827c7371f6dff7b12794d76384541f70838553fa57e37a075fa 4227)))
(.stop 26 0xe5fcb97cdb48a772c784d2505748d7bcf67420f55922c4ba946ddfb8dc34b192cb12f84c2d90f66859a979e7567 1136)))

private def tree156_418 : Tree :=
(.fork 0 0x0 77
(.fork 5 0x481254496127b09fc 65
(.fork 9 0xd9083434d1ba46f51e10ec844c1134 68
(.fork 16 0xf7851b2ca4cf718fccdd3d251375ca174e72e1e86da40cfa3d7cf66 48
(.stop 12 0x69578516e09d50d045f2de3a49df476d7315d15913 13796)
(.stop 21 0x58fdeedfbce5f222bd2d9f2d7f238e3729f2f3496173875435e4695785150c943b5a8f38e 13329))
(.fork 0 0x0 56
(.stop 19 0x397e1dc5a4977975e45f52222d32c2a318fcb1f5d39e86dca050f33b8d0350c943b 5330)
tree156_407))
(.fork 0 0x0 55
(.fork 10 0x5bc33d193cced340cd8836797385cf9ada 68
tree156_408
(.stop 20 0x7f2340766eb727366033414148a73b39cb1da4130bcc2050b3aeced43dbd90f72af398 14108))
(.fork 8 0x18fcfef402908a4295a3a6917565 71
(.stop 48 0x3aaf402777b6737ecf7241ffb7bb8daa7a1cda222ed7a543e751338758482840a249c82765f2d7f22364dc35a5577c63f5da4957d63f1f1dd09c2ad1668b9e3888ff661f9c26da1c78a3134c623638d9850b1441 13468)
tree156_409)))
(.fork 6 0xab45af1e28d8e366330f 68
(.fork 7 0x1790f78958256cb293d7cf66 50
(.fork 12 0x144863f29f0a8e3134c6250b144157f560f68e9a45 60
tree156_410
tree156_411)
(.fork 0 0x0 46
tree156_412
tree156_413))
(.fork 0 0x0 62
(.fork 8 0xf003d1454cf433f52674c05302 33
tree156_414
tree156_415)
(.fork 8 0xec64938a0e3350d9437534739e 57
tree156_416
tree156_417))))

private def tree156_419 : Tree :=
(.fork 6 0x22609df3f7126750ee35e 49
(.fork 4 0x29a525a61a1878 42
(.stop 15 0x397cb4637110edd1bb495f2d13f8f5d6164b36618b07fa4e253aa 4529)
(.stop 3 0x37ae6e2f847 2511))
(.stop 8 0x13b78504e836931bd4e2e49af564 14407))

private def tree156_420 : Tree :=
(.fork 0 0x0 39
(.stop 23 0x32cb4e277b6924771179f78e461bd9a5d592701b1f78451fdcbad30d1df57f235e761e1e90e149e86 8276)
(.stop 20 0xd9e1c17e5f9d49d09063bcba49cb3f8f845729755a6451e90e14938e4ea99ae7793723 4726))

private def tree156_421 : Tree :=
(.fork 0 0x0 38
(.stop 2 0xd0a4c56 3002)
(.stop 23 0x367f7a432d899bf2c88af38e61fe89d95a42051d561f22d7596a05a85c0a7a034294c45a4a7c6b7b1 4539))

private def tree156_422 : Tree :=
(.fork 11 0x3a1dc477e253cb323158c6658196a05a85de5 45
(.stop 15 0x3852537d57be39943872cb30544b51c97a4367846ed1d97a01f1a 4711)
(.fork 0 0x0 37
(.stop 22 0x7ed78527a4336d6de5c0b704f8e63ffd26750d5438534dc17862b85066bdf22d314cf15ac59b8 13159)
(.stop 17 0x32d249572e95111d4ace14f6c4bd138fd0908c32538d8b42194c3537f4c1 5006)))

private def tree156_423 : Tree :=
(.fork 9 0x5052edcbcb3af8ed26425ada8137395 77
(.stop 13 0x341a7cb74b544b7303193c9522ee8ced340cd8849d9311 6577)
(.fork 0 0x0 74
(.stop 13 0x1005e11d3a1da4cd9350f199b66bf3031e1c94e2cbcf59 13497)
(.fork 7 0x2c00b477046edf1a83a34c1 68
(.stop 15 0x249be398bb0e391690da4d616d05da3fd76512d44dd2fb6195916 13958)
(.fork 0 0x0 62
(.stop 14 0x5a437ad79f797c4015a3fd591431e148472499d4cf5a91cb2 14408)
(.stop 16 0xd77c93be398b9ccb25e7de39093e4e25690d56100568fdfb3813b429 1901)))))

private def tree156_424 : Tree :=
(.fork 6 0xce86d6448513e50a1e7f 65
(.fork 12 0xf885b322e88c42578b1333e8ec84bf930568d9a49 44
(.fork 10 0xb00c6032080a2a20c474955274557157b 57
(.stop 10 0x669f4127a438e7585b8474e817d661c204f 13327)
(.stop 21 0x19b8e3a17d4e601616e5f9ad9da152764e399aedc4e35ee398f5818c0b98d03d566669f41b 14417))
(.fork 0 0x0 28
(.fork 7 0x4fc2290a663d612647cae52f 31
tree156_419
tree156_420)
(.fork 0 0x0 39
(.stop 3 0x199cdc60b0c 14096)
(.stop 22 0xdc820fcd786840e3a0c404bd38e711a8472190cc663828f6d5599571669f8458d7a976b1f78e6 7652))))
(.fork 0 0x0 49
(.fork 10 0x58c5081e04b293d4cf6d49692747295cae 72
(.stop 3 0x330327c4d99 1918)
(.fork 10 0x11d847e14645aa27812635f357de666f305 47
(.stop 7 0x385258174b800bcb144e39914 4399)
tree156_421))
(.fork 0 0x0 57
(.stop 4 0xcc146462a54f6a 1305)
(.fork 0 0x0 59
tree156_422
tree156_423))))

private def tree156_425 : Tree :=
(.fork 0 0x0 51
(.stop 4 0xda419b8deed6a8 4405)
(.stop 17 0x34117a438ea5cf76906e2f4b37caf8e661c59a5778b42649d17de72bb395 4388))

private def tree156_426 : Tree :=
(.fork 10 0x27809f12ca4f533db525a49d17cd5f79cae 60
(.stop 16 0xd7596a0702b4296696840e3a8a7438bb5582c537bb2f2d1355815b7a 3158)
(.fork 9 0x599168cb0c3f915576209dec8af3690 47
(.stop 24 0xdc691bbd9fe2cdd022976d9d8fede3a8811deedfb2d7593a164778475a656a8deb538e4ea99016451de4 4214)
(.fork 0 0x0 56
(.stop 16 0xe390feddc649cbdeeda3fd77ce2e5a416b1e11d91d7a1f41161c59a5 2819)
(.stop 18 0xcb3cc37dc61431d00045a24ab67f7a1f41172d78473d2530561a18787a1b429 4067))))

private def tree156_427 : Tree :=
(.fork 0 0x0 56
(.fork 14 0x3489d63f922bcda400d41bb0b1d3890e374e5d3a161c59a5 42
(.stop 13 0x35d979f797c68ff3955a878ea3121005530b4c138b93aa 1901)
(.stop 3 0x37bb6943851 2551))
(.stop 30 0xe3a8b02e3a1e87dc494d7756b4b35aa1f2bdeec6442028896495555c55edae5d0a512d4725e90da19a4a7c6b4c138b93aa5ac7693 1904))

private def tree156_428 : Tree :=
(.fork 0 0x0 62
(.stop 14 0x814341061d78525a937bb27714e072cb4c51e04d78499d609 14408)
(.stop 9 0x186edc49f1adc889e63afb7bb6943306 13059))

private def tree156_429 : Tree :=
(.fork 5 0x3d40f6ce1f4499b78 62
(.fork 4 0x35820a1e04a95 77
(.stop 2 0xd57cb32 2847)
(.stop 3 0x36901dc34c5 819))
(.fork 0 0x0 68
(.stop 28 0x70572ed474b53f83e77bb6e1b8502768c4a756b8542ca512d00e847814288b52ef0bcb3fe54d1581da3b691369044dd574 13793)
(.fork 5 0x1803138ec13b3f306 59
(.stop 4 0xdc48c666b59ade 3158)
(.stop 18 0xdc694426deb8546e278eb581da44da419b86e1b7bb33a0ed247653a7704f429 3949))))

private def tree156_430 : Tree :=
(.fork 12 0x202d267756b55700e403a2cc8c5631996065a8755c 65
(.stop 10 0xe5f9e86888b69066e37bb16cc8ba4991305 4221)
(.stop 14 0x6e278e170937bb3afb72266e3690168cf5349d1c1472974c9 14113))

private def tree156_431 : Tree :=
(.fork 0 0x0 74
(.fork 7 0x1820d4047e253895e362cd9b 62
(.stop 6 0xdeed438ce547812a54b2f 3313)
(.fork 4 0x2060ec13b3f305 59
(.fork 11 0x3900e894f3158c6633c4d0038d16065a816a1 45
(.stop 34 0xa0f72c83f71077d28c9cbdeecebed019cbf75672e8168cd823d4d2f57029c1472976933fd51107a4205ed9e11bb47654c2538155d5a4d6ae7a01f1a 13015)
(.stop 15 0x17c4e381c13da4dc14e3841543aff72369437bb3af91117a3f722 13037))
(.stop 33 0x190ae389cbfcb5d2f4cbcccea41db7227caa05edc8500561bd9a5d08d9b77569df47ca35e72290ce83d620f9deecbcb3634d995345605581f303 13014)))
(.fork 0 0x0 66
(.fork 7 0x20e11d85192080d93498d26b 77
(.fork 8 0xd385b6193c6ea1bd4b1f2cc8bba 47
(.stop 6 0x44d76903d0b8e62c511bd 14267)
tree156_425)
(.fork 0 0x0 49
tree156_426
tree156_427))
(.fork 0 0x0 56
(.fork 12 0x3489d62a0cb1f55ed882da400d41bb0b1d3890e37 65
(.stop 8 0xded92647caf7bb16cc8ba4c15e86 2056)
tree156_428)
(.fork 0 0x0 51
tree156_429
tree156_430))))

private def tree156_432 : Tree :=
(.fork 0 0x0 45
(.stop 22 0xd27a186d52222fcdc6400d4fe0f9d006050da4c5082286221ce1029d1dc080b40156935ab9f1a 6426)
(.stop 26 0xd9d5de1d28991ad52222fcdc4e0bd4fe231cd91c14d9f9a50888a2bcd08416d2c68c5042351c37039c107513721 1288))

private def tree156_433 : Tree :=
(.fork 9 0x29d1dc080b40156935ab9e807c6a0e8 26
(.stop 14 0xe3a9de8cd920ec861b55770872d5533d69d5a935f4645a22f 6408)
(.fork 0 0x0 41
(.stop 15 0xeacd005c21cdc96a4d7d113769436904759861d27991a83b2186 13166)
(.stop 11 0x2400cb5d90d668d9a7e1496a4d7d13087087557 13010)))

private def tree156_434 : Tree :=
(.fork 0 0x0 39
(.fork 4 0x168c93b4e9da50 56
(.stop 4 0xcb4d87168fda40 6255)
(.stop 11 0x336f88bf2d850d569d5a91e83d3251d661ff685 1901))
(.fork 0 0x0 53
(.stop 10 0x4c235ef50e367e475942b61bd9a7d775a3d 13345)
(.stop 21 0x38527eff6754bb336846e187fd9f94385a934c950ad86f669e22fa3635dd35c4f423f77690 3161)))

private def tree156_435 : Tree :=
(.fork 0 0x0 40
(.stop 24 0xda4d254ded191ad08ce1ee15081a315cc655817303147c94e27a0b1c2cbcd8b3db3564142094c4c319b5 5656)
(.fork 12 0x360960a88bf6830a7459f1dc0fea40156935abb691 74
(.stop 13 0x2973e5fcc572761388d08cc655f638e72cbcd9b3d6555d 13633)
(.stop 9 0x38ea4c4739d0ce49da5817303318f564 4080)))

private def tree156_436 : Tree :=
(.fork 19 0x3914245121da07753100cdb33c54ba6e1b7bb1df8b32389ce3458196a05a85b79 51
(.stop 3 0x36756dc5b78 4876)
(.fork 0 0x0 45
(.stop 5 0x37b0499f84f5ab9e80 1129)
(.stop 19 0x367e72bb2d168f77b04bb367590032d613c8cda70877202ed0fdde38893f534f5e3 7030)))

private def tree156_437 : Tree :=
(.fork 0 0x0 74
(.stop 7 0x160fd2ec51f1b98d8b366d273 13059)
(.fork 0 0x0 49
(.stop 8 0xa9339d2f236831420b2936090a5 13059)
(.stop 23 0x1f28dca1c0d889736555a5609cc0d26ddeecf6a72b739d33b9132755f5553fd586f6695d41751f55f 14112)))

private def tree156_438 : Tree :=
(.fork 11 0x390f5477e202cb32389ce3458196a05a85e80 28
(.fork 5 0x8a4272d43869420f9 53
(.stop 26 0xd039aedd7ba22fcd96a0ecb20cd16baf53f7051ca57ec35e770877230a9446922f4ea3470d1d66689a3d6909d44 8582)
(.stop 9 0x37b4900371b645a22fdec08c32a27690 7823))
(.stop 21 0x32e08b2b4a23ab78ea1458a772efd39e50d14397eeb685057c5a344df69011a4cf16e1b7bb 3445))

private def tree156_439 : Tree :=
(.fork 0 0x0 66
(.stop 9 0x342c533f7b67c8b7bb69434bb364d26b 4547)
(.stop 8 0x5cff7b6690b69022837b7669f561 13059))

private def tree156_440 : Tree :=
(.fork 0 0x0 63
(.fork 7 0x2a50aa85162a24bc850d1439 39
(.stop 7 0x3683360b564318cfffd0b0b1f 1288)
(.stop 8 0xda0c9f1360b54672cb42c4c47690 1288))
(.fork 0 0x0 77
(.stop 22 0xe5fd42bd59913b53016b05f1f4bb647f7233b53397318d267533d4d3cc0c34e16d8b1f2f35311 4388)
(.fork 9 0x33922c88c13d6cf6a5f558707ed339b 41
(.stop 10 0xd0b09e8e601a50d2ecd9349af3033165271 1912)
(.fork 0 0x0 74
(.stop 17 0x39816bb6225ce10e1cdede22fda0d73f7a3f7b672cb30311f89e844f557a 4547)
tree156_439))))

private def tree156_441 : Tree :=
(.fork 5 0x3e220608263b04ecf 55
(.fork 7 0x16c27989f7423d9096431ada 59
(.fork 13 0x3a034c207082c77e2cc8e2738d16065a816a161b9872 74
(.fork 6 0x1e1c94e2c70b2f33c4f59 54
(.stop 9 0x33699002975cb4990d668d9a76dd5c0f 4393)
tree156_432)
(.fork 0 0x0 45
tree156_433
tree156_434))
(.fork 0 0x0 68
(.stop 8 0xd569132ce745b61e1c8c12ca5137 1302)
(.fork 0 0x0 54
(.stop 29 0x191cd27d87f83af69340174b93194d8b366cb0ed9e0f59ce7416e0a88d8d3665607cc0c20a1458a80367913b668d9a76dd1c0f 13344)
tree156_435)))
(.fork 0 0x0 60
(.fork 6 0xe80d40d20d8d36654d1 74
(.stop 17 0x367c66d7854276913b49516b0d79cf5b61c33974c037bb2068c573194d9b 4397)
(.fork 0 0x0 54
(.stop 5 0x339d3d6d303d79d13b 3463)
(.stop 21 0x36915d3b68c4c0f980276b68344dd3a70ce8f6a584f7bb6942188d57c50a4c31a3b6913564 4881)))
(.fork 0 0x0 50
(.fork 8 0x81846e11d8ce84e453a7702dc13 59
tree156_436
tree156_437)
(.fork 7 0x7703fa90055a4d6ae7c6b565 59
tree156_438
tree156_440))))

private def tree156_442 : Tree :=
(.fork 0 0x0 40
(.fork 6 0x14209e829c94225111881 77
(.stop 9 0x38509e9f71777df8e688c78ea3620d9e 7967)
(.stop 8 0xe151917cbc8a773fcf7177c7f693 5642))
(.fork 4 0x201cff3708f71f 32
(.stop 8 0xd5219b7cba9917dc6428b1dc0d88 806)
(.stop 8 0xcc14647d795e92d521df488c7724 5642)))

private def tree156_443 : Tree :=
(.fork 8 0x82c2a511cca892a51434580960a 40
(.fork 9 0x50822849e829c8d7936414226205f1f 77
(.stop 17 0x38e67f172d28183717511f7b97a3f97c7a134b514152574bc9b6ce1516b3 6417)
(.stop 17 0x3548537f40f694b4b164477ae7a132cf753b7173fcd9a76dd1b75703f5f8 2820))
(.stop 7 0x371f18e37146dd368a18e74c4 4083))

private def tree156_444 : Tree :=
(.fork 6 0x191c6ed424926049bb305 77
(.stop 2 0xd330d03 2866)
(.fork 0 0x0 54
(.stop 25 0x340499a72cc1fc32cf13b862f6e0e5cee5f20e8d9e8ebf61c5a40d330ff875675584c259a3669db746dd5c0f 6268)
(.stop 2 0x61cb5ec 13798)))

private def tree156_445 : Tree :=
(.fork 15 0x1711930a8944c87753100f4757c1615694b7bb4c0130350d1439 48
(.stop 10 0xe6016b0862f54872fb8e022e0f524ea5a38 6273)
(.stop 17 0x3980703f2f54bd75e572c37ab8fdf72429c8b0ee381e92dc5c9da72fb7bd 4216))

private def tree156_446 : Tree :=
(.fork 0 0x0 43
(.stop 15 0x37bb694b98179fb5e5400730505b88092f357d55f5b3973d9d691 6112)
(.stop 8 0x5f838e638d97d579fb397191f4bf 13061))

private def tree156_447 : Tree :=
(.fork 19 0x2a50aa864c08186e61dd4e1e38d92736411911702dc13d594a892a5113250d1439 59
(.fork 8 0x14248b42cc939e58196a06dc1b79 48
(.stop 26 0x2267981a5d7366924b5e775678ea8d8b8e71d9ccda862f2ea6e0f7290a08634334b7bb03285a28b338e022a5ca4 13189)
(.stop 4 0xe3a991c7eeb7bd 5343))
(.fork 2 0x818370f 48
(.stop 6 0xdc65429d7c48b8312d3a9 202)
(.fork 0 0x0 40
(.fork 6 0x142059a1d78d793641444 77
(.stop 11 0x340266ddb8b924b5e72c45fb5def54dfdeeddf7 4079)
(.stop 6 0x7ed77bd537f7191fe75fd 14097))
(.stop 14 0xe605b7ddca5af0da441640cc880a645dfb5d3105003d0b724 4230))))

private def tree156_448 : Tree :=
(.fork 0 0x0 59
(.fork 7 0x3922d0b3233c4d0058196a0 50
(.stop 5 0x35583fe330514486e6 1607)
(.fork 7 0x770202d12055e9e807c6b565 68
(.fork 7 0x34a16b0b29427112d44dd916 43
(.stop 21 0x1e8fd00a5d3cd99a426ddb7b061c604ece10ff361edc23d5397e0d2812545a456b06932050 13186)
(.stop 7 0x354e5f838e67a2769349875e7 1275))
(.fork 0 0x0 62
(.stop 6 0xd321ae1e3994dfdeed438 6257)
(.stop 2 0x191f558 13061))))
(.fork 0 0x0 68
(.fork 6 0xd285ac16d8b2944b5137 57
(.stop 13 0x38e55a474bf5f838e67c6b56538d91c747497d55f59870 2536)
(.stop 12 0xda15395d7b1e8988c78e661f1f1ad594a8e424b39b 6257))
(.stop 6 0x22df39b191f4cb00e34cf 13061)))

private def tree156_449 : Tree :=
(.fork 7 0x3d43d54f6f3fc16995aa1b71 60
(.stop 25 0x7f2d00a186e3a1c26d79d7cd75273698feb8e661c5cacd7b880c2eb8bc2495d2f2752f7bb44d5605581da3b 13648)
(.stop 4 0x61c78e67c6b565 13520))

private def tree156_450 : Tree :=
(.fork 0 0x0 55
(.stop 9 0x36904c476885aaf4cc340cd883679260 672)
(.stop 9 0x38e67c6b5650f6d00ad31c77b61c74d0 6268))

private def tree156_451 : Tree :=
(.fork 7 0xd2081820a190cd873889571 63
(.stop 15 0x37ab7a1354d42278546df767a1dc0cd68fdf71c22e0ffc50d169c 668)
(.stop 3 0x35f44eb35f5 1904))

private def tree156_452 : Tree :=
(.fork 0 0x0 74
(.fork 5 0x47e253895e362cd9b 55
(.fork 9 0x16c1e1cb1c2cbcf593db19096431ada 60
(.fork 10 0xe80d40a8881a315cc655345605581d7d3 43
(.stop 20 0xdc6538b668f36557dd6157a077b053538e64bd599e6dbdca5e15160acc14f675a45f1c 2697)
tree156_442)
(.fork 0 0x0 63
tree156_443
tree156_444))
(.fork 0 0x0 60
(.fork 8 0xe80d4035881a315cc655815607 63
tree156_445
tree156_446)
(.fork 0 0x0 63
tree156_447
tree156_448)))
(.fork 6 0x16d8b1f2cc8bba2f3730f 66
(.fork 8 0x838476193c6ea1bd4d93498d26b 63
(.stop 11 0x35e753475654eb355005dc81d3d8513250d1439 4867)
(.fork 0 0x0 51
tree156_449
(.stop 8 0x44d75657c6b8e62c511bd49db4c7 14267)))
(.fork 0 0x0 69
(.fork 3 0x51c191c9f4 63
(.stop 14 0x22937bb4c256a5da447703621af06e2f6900a9481d3640d96 13799)
tree156_450)
(.fork 7 0x3db1ba47843b212fe4c17308 54
tree156_451
(.stop 19 0x34cc473f7b04eb36816e2f71461e3854143c63c22dca7946f51db49612767793683 2077)))))

private def tree156_453 : Tree :=
(.fork 0 0x0 67
(.fork 2 0xfacc5e 75
(.fork 5 0x21711fc4871e1878e 66
(.fork 9 0x410108519196882020a4cf833e4d93 53
tree156_347
tree156_352)
(.fork 0 0x0 69
tree156_353
tree156_360))
(.fork 0 0x0 77
(.fork 5 0x2b316d45bf194065a 55
tree156_364
tree156_371)
(.fork 0 0x0 72
tree156_375
tree156_382)))
(.fork 0 0x0 61
(.fork 2 0x195539c 75
(.fork 5 0x3e5206c8292c88b30 46
tree156_388
tree156_396)
(.fork 0 0x0 74
tree156_406
tree156_418))
(.fork 3 0x78a5cef43a 75
(.fork 5 0x65227a49fa33c0d01 46
tree156_424
tree156_431)
(.fork 0 0x0 72
tree156_441
tree156_452))))

private def tree156_454 : Tree :=
(.fork 0 0x0 73
(.fork 2 0x604520 60
(.fork 6 0x195077f1e30cf233fd4d1 59
(.fork 11 0x3a00ec3e320648272a5cd8c366956b55b1606 56
tree156_0
tree156_7)
(.fork 0 0x0 74
tree156_11
tree156_30))
(.fork 0 0x0 75
(.fork 6 0x1240e303942b60fa83ec 56
tree156_31
tree156_40)
(.fork 0 0x0 70
tree156_49
tree156_95)))
(.fork 0 0x0 76
(.fork 1 0x4c 55
(.fork 7 0x6eb22fcc52319ce2338e1ada 74
tree156_96
tree156_111)
(.fork 0 0x0 46
tree156_136
tree156_229))
(.fork 0 0x0 70
(.fork 2 0xad88bf 72
tree156_242
tree156_278)
(.fork 0 0x0 64
tree156_346
tree156_453))))

set_option maxHeartbeats 150000000 in
set_option maxRecDepth 100000 in
private theorem no156 : ¬ Good 156 13 := by
  rintro ⟨c, hp, ha⟩
  apply check_sound (apRule_hits (by decide : 3 ≤ 156) hp ha) tree156_454 (fun _ => 0)
  · simp [agrees]
  · decide +kernel

/-- Table 6 of Ahmed, Kullmann and Snevily. With odd length the last
avoiding palindrome has 141 positions, and with even length it has 154. -/
theorem palindromic_3_13 (n : Nat) :
    Good n 13 ↔ (n % 2 = 0 ∧ n ≤ 154) ∨ (n % 2 = 1 ∧ n ≤ 141) := by
  constructor
  · intro h
    by_cases even : n % 2 = 0
    · left
      refine ⟨even, ?_⟩
      by_contra! large
      exact no156 (restrictGood 156 ((n-156)/2) (by omega) h)
    · right
      refine ⟨by omega, ?_⟩
      by_contra! large
      exact no143 (restrictGood 143 ((n-143)/2) (by omega) h)
  · rintro (⟨even, small⟩ | ⟨odd, small⟩)
    · exact restrictGood n ((154-n)/2) (by omega) yes154
    · exact restrictGood n ((141-n)/2) (by omega) yes141

private lemma mono_of_noGood {n : Nat} (h : ¬ Good n 13) (c : Nat → Bool) (hp : Pal n c) :
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 12)*d < n ∧
      ∀ t ≤ (if b then 2 else 12), c (a+t*d) = b := by
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
    exact Bool.eq_false_iff.mpr (absent t (by change t < 13; change t ≤ 12 at ht; omega))

end ReflectionCertificate

theorem OMA.solution : OMA.R_Green14_W_3_13_R4.H1 := by
  intro n hn c hp
  apply ReflectionCertificate.mono_of_noGood _ c hp
  intro h
  have := (ReflectionCertificate.palindromic_3_13 n).mp h
  rcases hn with rfl | rfl <;> omega
