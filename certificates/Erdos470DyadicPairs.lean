import OMAReductions.R_Erdos470_erdos_470_parts_ii_R1_H2_R1

/-!
# Certified dyadic pairs for primitive weird numbers

At each listed dyadic scale the following Lucas certificates verify a prime
in each interval used in the prime-gap reduction of Erdős 470(ii).
The construction of primitive weird numbers is due to G. Melfi.
The imported proof of his divisor criterion is by @biondadave. The interval
selection, certificates and finite-range verification are by @KoaOkano.
-/

namespace OMA.Erdos470Examples

private theorem divisorInList (fs : List (ℕ × ℕ)) {r : ℕ} (hr : r.Prime)
    (h : r ∣ (fs.map (fun z => z.1 ^ z.2)).prod) : ∃ z ∈ fs, r ∣ z.1 := by
  induction fs with
  | nil => simp [hr.not_dvd_one] at h
  | cons z zs ih =>
    simp only [List.map_cons, List.prod_cons, hr.dvd_mul] at h
    rcases h with h | h
    · exact ⟨z, List.mem_cons_self, hr.dvd_of_dvd_pow h⟩
    · obtain ⟨u, hu, hd⟩ := ih h
      exact ⟨u, List.mem_cons_of_mem _ hu, hd⟩

private theorem lucasList {n g : ℕ} (fs : List (ℕ × ℕ))
    (product : n - 1 = (fs.map (fun z => z.1 ^ z.2)).prod)
    (one : (g : ZMod n) ^ (n - 1) = 1)
    (tests : ∀ z ∈ fs, z.1.Prime ∧ (g : ZMod n) ^ ((n - 1) / z.1) ≠ 1) :
    n.Prime := by
  apply lucas_primality n (g : ZMod n) one
  intro r hr hd
  rw [product] at hd
  obtain ⟨z, hz, hdiv⟩ := divisorInList fs hr hd
  obtain ⟨hp, test⟩ := tests z hz
  have eq := (Nat.prime_dvd_prime_iff_eq hr hp).mp hdiv
  rwa [eq]


private theorem prime_2 : Nat.Prime 2 := by norm_num

private theorem prime_5 : Nat.Prime 5 := by norm_num

private theorem prime_409 : Nat.Prime 409 := by norm_num

private theorem prime_261761 : Nat.Prime 261761 := by
  apply lucasList (g := 3) [(2, 7), (5, 1), (409, 1)]
  · decide
  · change (3 : ZMod 261761) ^ 261760 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 261761) ^ 130880 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (3 : ZMod 261761) ^ 52352 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_409, ?_⟩
      change (3 : ZMod 261761) ^ 640 ≠ 1
      reduce_mod_char
      decide

private theorem prime_4099 : Nat.Prime 4099 := by norm_num

private theorem prime_262337 : Nat.Prime 262337 := by
  apply lucasList (g := 3) [(2, 6), (4099, 1)]
  · decide
  · change (3 : ZMod 262337) ^ 262336 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 262337) ^ 131168 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_4099, ?_⟩
      change (3 : ZMod 262337) ^ 64 ≠ 1
      reduce_mod_char
      decide

private theorem prime_227 : Nat.Prime 227 := by norm_num

private theorem prime_577 : Nat.Prime 577 := by norm_num

private theorem prime_1047833 : Nat.Prime 1047833 := by
  apply lucasList (g := 3) [(2, 3), (227, 1), (577, 1)]
  · decide
  · change (3 : ZMod 1047833) ^ 1047832 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 1047833) ^ 523916 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_227, ?_⟩
      change (3 : ZMod 1047833) ^ 4616 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_577, ?_⟩
      change (3 : ZMod 1047833) ^ 1816 ≠ 1
      reduce_mod_char
      decide

private theorem prime_11 : Nat.Prime 11 := by norm_num

private theorem prime_197 : Nat.Prime 197 := by norm_num

private theorem prime_1048829 : Nat.Prime 1048829 := by
  apply lucasList (g := 2) [(2, 2), (11, 3), (197, 1)]
  · decide
  · change (2 : ZMod 1048829) ^ 1048828 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 1048829) ^ 524414 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11, ?_⟩
      change (2 : ZMod 1048829) ^ 95348 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_197, ?_⟩
      change (2 : ZMod 1048829) ^ 5324 ≠ 1
      reduce_mod_char
      decide

private theorem prime_3 : Nat.Prime 3 := by norm_num

private theorem prime_719 : Nat.Prime 719 := by norm_num

private theorem prime_4193209 : Nat.Prime 4193209 := by
  apply lucasList (g := 14) [(2, 3), (3, 6), (719, 1)]
  · decide
  · change (14 : ZMod 4193209) ^ 4193208 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (14 : ZMod 4193209) ^ 2096604 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (14 : ZMod 4193209) ^ 1397736 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_719, ?_⟩
      change (14 : ZMod 4193209) ^ 5832 ≠ 1
      reduce_mod_char
      decide

private theorem prime_839 : Nat.Prime 839 := by norm_num

private theorem prime_4195001 : Nat.Prime 4195001 := by
  apply lucasList (g := 3) [(2, 3), (5, 4), (839, 1)]
  · decide
  · change (3 : ZMod 4195001) ^ 4195000 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 4195001) ^ 2097500 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (3 : ZMod 4195001) ^ 839000 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_839, ?_⟩
      change (3 : ZMod 4195001) ^ 5000 ≠ 1
      reduce_mod_char
      decide

private theorem prime_61 : Nat.Prime 61 := by norm_num

private theorem prime_4297 : Nat.Prime 4297 := by norm_num

private theorem prime_16775489 : Nat.Prime 16775489 := by
  apply lucasList (g := 3) [(2, 6), (61, 1), (4297, 1)]
  · decide
  · change (3 : ZMod 16775489) ^ 16775488 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 16775489) ^ 8387744 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_61, ?_⟩
      change (3 : ZMod 16775489) ^ 275008 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_4297, ?_⟩
      change (3 : ZMod 16775489) ^ 3904 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_3413 : Nat.Prime 3413 := by norm_num

private theorem prime_16778309 : Nat.Prime 16778309 := by
  apply lucasList (g := 2) [(2, 2), (1229, 1), (3413, 1)]
  · decide
  · change (2 : ZMod 16778309) ^ 16778308 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 16778309) ^ 8389154 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1229, ?_⟩
      change (2 : ZMod 16778309) ^ 13652 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3413, ?_⟩
      change (2 : ZMod 16778309) ^ 4916 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_2939 : Nat.Prime 2939 := by norm_num

private theorem prime_67103249 : Nat.Prime 67103249 := by
  apply lucasList (g := 3) [(2, 4), (1427, 1), (2939, 1)]
  · decide
  · change (3 : ZMod 67103249) ^ 67103248 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 67103249) ^ 33551624 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1427, ?_⟩
      change (3 : ZMod 67103249) ^ 47024 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2939, ?_⟩
      change (3 : ZMod 67103249) ^ 22832 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_1627 : Nat.Prime 1627 := by norm_num

private theorem prime_67110497 : Nat.Prime 67110497 := by
  apply lucasList (g := 3) [(2, 5), (1289, 1), (1627, 1)]
  · decide
  · change (3 : ZMod 67110497) ^ 67110496 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 67110497) ^ 33555248 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1289, ?_⟩
      change (3 : ZMod 67110497) ^ 52064 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1627, ?_⟩
      change (3 : ZMod 67110497) ^ 41248 ≠ 1
      reduce_mod_char
      decide

private theorem prime_89 : Nat.Prime 89 := by norm_num

private theorem prime_353 : Nat.Prime 353 := by norm_num

private theorem prime_268426849 : Nat.Prime 268426849 := by
  apply lucasList (g := 17) [(2, 5), (3, 1), (89, 2), (353, 1)]
  · decide
  · change (17 : ZMod 268426849) ^ 268426848 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (17 : ZMod 268426849) ^ 134213424 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (17 : ZMod 268426849) ^ 89475616 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_89, ?_⟩
      change (17 : ZMod 268426849) ^ 3016032 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_353, ?_⟩
      change (17 : ZMod 268426849) ^ 760416 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_7213 : Nat.Prime 7213 := by norm_num

private theorem prime_268439009 : Nat.Prime 268439009 := by
  apply lucasList (g := 3) [(2, 5), (1163, 1), (7213, 1)]
  · decide
  · change (3 : ZMod 268439009) ^ 268439008 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 268439009) ^ 134219504 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1163, ?_⟩
      change (3 : ZMod 268439009) ^ 230816 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7213, ?_⟩
      change (3 : ZMod 268439009) ^ 37216 ≠ 1
      reduce_mod_char
      decide

private theorem prime_127 : Nat.Prime 127 := by norm_num

private theorem prime_431 : Nat.Prime 431 := by norm_num

private theorem prime_613 : Nat.Prime 613 := by norm_num

private theorem prime_1073720993 : Nat.Prime 1073720993 := by
  apply lucasList (g := 3) [(2, 5), (127, 1), (431, 1), (613, 1)]
  · decide
  · change (3 : ZMod 1073720993) ^ 1073720992 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 1073720993) ^ 536860496 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_127, ?_⟩
      change (3 : ZMod 1073720993) ^ 8454496 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_431, ?_⟩
      change (3 : ZMod 1073720993) ^ 2491232 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_613, ?_⟩
      change (3 : ZMod 1073720993) ^ 1751584 ≠ 1
      reduce_mod_char
      decide

private theorem prime_19 : Nat.Prime 19 := by norm_num

private theorem prime_251 : Nat.Prime 251 := by norm_num

private theorem prime_1759 : Nat.Prime 1759 := by norm_num

private theorem prime_1073749889 : Nat.Prime 1073749889 := by
  apply lucasList (g := 3) [(2, 7), (19, 1), (251, 1), (1759, 1)]
  · decide
  · change (3 : ZMod 1073749889) ^ 1073749888 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 1073749889) ^ 536874944 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_19, ?_⟩
      change (3 : ZMod 1073749889) ^ 56513152 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_251, ?_⟩
      change (3 : ZMod 1073749889) ^ 4277888 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1759, ?_⟩
      change (3 : ZMod 1073749889) ^ 610432 ≠ 1
      reduce_mod_char
      decide

private theorem prime_31 : Nat.Prime 31 := by norm_num

private theorem prime_509 : Nat.Prime 509 := by norm_num

private theorem prime_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_4294917569 : Nat.Prime 4294917569 := by
  apply lucasList (g := 6) [(2, 6), (31, 1), (509, 1), (4253, 1)]
  · decide
  · change (6 : ZMod 4294917569) ^ 4294917568 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (6 : ZMod 4294917569) ^ 2147458784 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_31, ?_⟩
      change (6 : ZMod 4294917569) ^ 138545728 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_509, ?_⟩
      change (6 : ZMod 4294917569) ^ 8437952 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_4253, ?_⟩
      change (6 : ZMod 4294917569) ^ 1009856 ≠ 1
      reduce_mod_char
      decide

private theorem prime_29 : Nat.Prime 29 := by norm_num

private theorem prime_101 : Nat.Prime 101 := by norm_num

private theorem prime_179 : Nat.Prime 179 := by norm_num

private theorem prime_4294991873 : Nat.Prime 4294991873 := by
  apply lucasList (g := 3) [(2, 13), (29, 1), (101, 1), (179, 1)]
  · decide
  · change (3 : ZMod 4294991873) ^ 4294991872 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 4294991873) ^ 2147495936 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_29, ?_⟩
      change (3 : ZMod 4294991873) ^ 148103168 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_101, ?_⟩
      change (3 : ZMod 4294991873) ^ 42524672 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_179, ?_⟩
      change (3 : ZMod 4294991873) ^ 23994368 ≠ 1
      reduce_mod_char
      decide

private theorem prime_103 : Nat.Prime 103 := by norm_num

private theorem prime_997 : Nat.Prime 997 := by norm_num

private theorem prime_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_17179793537 : Nat.Prime 17179793537 := by
  apply lucasList (g := 3) [(2, 7), (103, 1), (997, 1), (1307, 1)]
  · decide
  · change (3 : ZMod 17179793537) ^ 17179793536 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 17179793537) ^ 8589896768 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_103, ?_⟩
      change (3 : ZMod 17179793537) ^ 166794112 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_997, ?_⟩
      change (3 : ZMod 17179793537) ^ 17231488 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1307, ?_⟩
      change (3 : ZMod 17179793537) ^ 13144448 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_17179897601 : Nat.Prime 17179897601 := by
  apply lucasList (g := 3) [(2, 8), (5, 2), (1097, 1), (2447, 1)]
  · decide
  · change (3 : ZMod 17179897601) ^ 17179897600 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 17179897601) ^ 8589948800 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (3 : ZMod 17179897601) ^ 3435979520 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1097, ?_⟩
      change (3 : ZMod 17179897601) ^ 15660800 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2447, ?_⟩
      change (3 : ZMod 17179897601) ^ 7020800 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_2609 : Nat.Prime 2609 := by norm_num

private theorem prime_68719306753 : Nat.Prime 68719306753 := by
  apply lucasList (g := 5) [(2, 11), (3, 2), (1429, 1), (2609, 1)]
  · decide
  · change (5 : ZMod 68719306753) ^ 68719306752 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (5 : ZMod 68719306753) ^ 34359653376 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (5 : ZMod 68719306753) ^ 22906435584 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1429, ?_⟩
      change (5 : ZMod 68719306753) ^ 48089088 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2609, ?_⟩
      change (5 : ZMod 68719306753) ^ 26339328 ≠ 1
      reduce_mod_char
      decide

private theorem prime_2971 : Nat.Prime 2971 := by norm_num

private theorem prime_5647 : Nat.Prime 5647 := by norm_num

private theorem prime_68719562753 : Nat.Prime 68719562753 := by
  apply lucasList (g := 3) [(2, 12), (2971, 1), (5647, 1)]
  · decide
  · change (3 : ZMod 68719562753) ^ 68719562752 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 68719562753) ^ 34359781376 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2971, ?_⟩
      change (3 : ZMod 68719562753) ^ 23130112 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5647, ?_⟩
      change (3 : ZMod 68719562753) ^ 12169216 ≠ 1
      reduce_mod_char
      decide

private theorem prime_137 : Nat.Prime 137 := by norm_num

private theorem prime_313 : Nat.Prime 313 := by norm_num

private theorem prime_274877501441 : Nat.Prime 274877501441 := by
  apply lucasList (g := 3) [(2, 12), (5, 1), (137, 1), (313, 2)]
  · decide
  · change (3 : ZMod 274877501441) ^ 274877501440 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 274877501441) ^ 137438750720 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (3 : ZMod 274877501441) ^ 54975500288 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_137, ?_⟩
      change (3 : ZMod 274877501441) ^ 2006405120 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_313, ?_⟩
      change (3 : ZMod 274877501441) ^ 878202880 ≠ 1
      reduce_mod_char
      decide

private theorem prime_41 : Nat.Prime 41 := by norm_num

private theorem prime_67 : Nat.Prime 67 := by norm_num

private theorem prime_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_274877917697 : Nat.Prime 274877917697 := by
  apply lucasList (g := 3) [(2, 9), (41, 1), (67, 2), (2917, 1)]
  · decide
  · change (3 : ZMod 274877917697) ^ 274877917696 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 274877917697) ^ 137438958848 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_41, ?_⟩
      change (3 : ZMod 274877917697) ^ 6704339456 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_67, ?_⟩
      change (3 : ZMod 274877917697) ^ 4102655488 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2917, ?_⟩
      change (3 : ZMod 274877917697) ^ 94233088 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_6143 : Nat.Prime 6143 := by norm_num

private theorem prime_1099510899713 : Nat.Prime 1099510899713 := by
  apply lucasList (g := 3) [(2, 10), (103, 1), (1697, 1), (6143, 1)]
  · decide
  · change (3 : ZMod 1099510899713) ^ 1099510899712 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 1099510899713) ^ 549755449856 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_103, ?_⟩
      change (3 : ZMod 1099510899713) ^ 10674863104 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1697, ?_⟩
      change (3 : ZMod 1099510899713) ^ 647914496 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_6143, ?_⟩
      change (3 : ZMod 1099510899713) ^ 178985984 ≠ 1
      reduce_mod_char
      decide

private theorem prime_43 : Nat.Prime 43 := by norm_num

private theorem prime_743 : Nat.Prime 743 := by norm_num

private theorem prime_4201 : Nat.Prime 4201 := by norm_num

private theorem prime_1099511799809 : Nat.Prime 1099511799809 := by
  apply lucasList (g := 3) [(2, 13), (43, 1), (743, 1), (4201, 1)]
  · decide
  · change (3 : ZMod 1099511799809) ^ 1099511799808 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 1099511799809) ^ 549755899904 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_43, ?_⟩
      change (3 : ZMod 1099511799809) ^ 25570041856 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_743, ?_⟩
      change (3 : ZMod 1099511799809) ^ 1479827456 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_4201, ?_⟩
      change (3 : ZMod 1099511799809) ^ 261726208 ≠ 1
      reduce_mod_char
      decide

private theorem prime_4451 : Nat.Prime 4451 := by norm_num

private theorem prime_6701 : Nat.Prime 6701 := by norm_num

private theorem prime_4398044921857 : Nat.Prime 4398044921857 := by
  apply lucasList (g := 5) [(2, 14), (3, 2), (4451, 1), (6701, 1)]
  · decide
  · change (5 : ZMod 4398044921857) ^ 4398044921856 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (5 : ZMod 4398044921857) ^ 2199022460928 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (5 : ZMod 4398044921857) ^ 1466014973952 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_4451, ?_⟩
      change (5 : ZMod 4398044921857) ^ 988102656 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_6701, ?_⟩
      change (5 : ZMod 4398044921857) ^ 656326656 ≠ 1
      reduce_mod_char
      decide

private theorem prime_2459 : Nat.Prime 2459 := by norm_num

private theorem prime_11491 : Nat.Prime 11491 := by norm_num

private theorem prime_4398047322113 : Nat.Prime 4398047322113 := by
  apply lucasList (g := 3) [(2, 13), (19, 1), (2459, 1), (11491, 1)]
  · decide
  · change (3 : ZMod 4398047322113) ^ 4398047322112 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 4398047322113) ^ 2199023661056 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_19, ?_⟩
      change (3 : ZMod 4398047322113) ^ 231476174848 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2459, ?_⟩
      change (3 : ZMod 4398047322113) ^ 1788551168 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11491, ?_⟩
      change (3 : ZMod 4398047322113) ^ 382738432 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_2999 : Nat.Prime 2999 := by norm_num

private theorem prime_17592184287233 : Nat.Prime 17592184287233 := by
  apply lucasList (g := 3) [(2, 12), (1171, 1), (1223, 1), (2999, 1)]
  · decide
  · change (3 : ZMod 17592184287233) ^ 17592184287232 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 17592184287233) ^ 8796092143616 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1171, ?_⟩
      change (3 : ZMod 17592184287233) ^ 15023214592 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1223, ?_⟩
      change (3 : ZMod 17592184287233) ^ 14384451584 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2999, ?_⟩
      change (3 : ZMod 17592184287233) ^ 5866016768 ≠ 1
      reduce_mod_char
      decide

private theorem prime_5689 : Nat.Prime 5689 := by norm_num

private theorem prime_9437 : Nat.Prime 9437 := by norm_num

private theorem prime_17592186634241 : Nat.Prime 17592186634241 := by
  apply lucasList (g := 6) [(2, 16), (5, 1), (5689, 1), (9437, 1)]
  · decide
  · change (6 : ZMod 17592186634241) ^ 17592186634240 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (6 : ZMod 17592186634241) ^ 8796093317120 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (6 : ZMod 17592186634241) ^ 3518437326848 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5689, ?_⟩
      change (6 : ZMod 17592186634241) ^ 3092316160 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_9437, ?_⟩
      change (6 : ZMod 17592186634241) ^ 1864171520 ≠ 1
      reduce_mod_char
      decide

private theorem prime_4889 : Nat.Prime 4889 := by norm_num

private theorem prime_9151 : Nat.Prime 9151 := by norm_num

private theorem prime_70368738410497 : Nat.Prime 70368738410497 := by
  apply lucasList (g := 11) [(2, 19), (3, 1), (4889, 1), (9151, 1)]
  · decide
  · change (11 : ZMod 70368738410497) ^ 70368738410496 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (11 : ZMod 70368738410497) ^ 35184369205248 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (11 : ZMod 70368738410497) ^ 23456246136832 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_4889, ?_⟩
      change (11 : ZMod 70368738410497) ^ 14393278464 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_9151, ?_⟩
      change (11 : ZMod 70368738410497) ^ 7689732096 ≠ 1
      reduce_mod_char
      decide

private theorem prime_7 : Nat.Prime 7 := by norm_num

private theorem prime_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_8069 : Nat.Prime 8069 := by norm_num

private theorem prime_70368744570881 : Nat.Prime 70368744570881 := by
  apply lucasList (g := 3) [(2, 17), (5, 1), (7, 1), (1901, 1), (8069, 1)]
  · decide
  · change (3 : ZMod 70368744570881) ^ 70368744570880 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 70368744570881) ^ 35184372285440 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (3 : ZMod 70368744570881) ^ 14073748914176 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7, ?_⟩
      change (3 : ZMod 70368744570881) ^ 10052677795840 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1901, ?_⟩
      change (3 : ZMod 70368744570881) ^ 37016698880 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_8069, ?_⟩
      change (3 : ZMod 70368744570881) ^ 8720875520 ≠ 1
      reduce_mod_char
      decide

private theorem prime_8887 : Nat.Prime 8887 := by norm_num

private theorem prime_11933 : Nat.Prime 11933 := by norm_num

private theorem prime_281474965536769 : Nat.Prime 281474965536769 := by
  apply lucasList (g := 17) [(2, 15), (3, 4), (8887, 1), (11933, 1)]
  · decide
  · change (17 : ZMod 281474965536769) ^ 281474965536768 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (17 : ZMod 281474965536769) ^ 140737482768384 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (17 : ZMod 281474965536769) ^ 93824988512256 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_8887, ?_⟩
      change (17 : ZMod 281474965536769) ^ 31672664064 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11933, ?_⟩
      change (17 : ZMod 281474965536769) ^ 23587946496 ≠ 1
      reduce_mod_char
      decide

private theorem prime_13 : Nat.Prime 13 := by norm_num

private theorem prime_461 : Nat.Prime 461 := by norm_num

private theorem prime_2297 : Nat.Prime 2297 := by norm_num

private theorem prime_281474980380673 : Nat.Prime 281474980380673 := by
  apply lucasList (g := 11) [(2, 19), (3, 1), (13, 2), (461, 1), (2297, 1)]
  · decide
  · change (11 : ZMod 281474980380673) ^ 281474980380672 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (11 : ZMod 281474980380673) ^ 140737490190336 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (11 : ZMod 281474980380673) ^ 93824993460224 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_13, ?_⟩
      change (11 : ZMod 281474980380673) ^ 21651921567744 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_461, ?_⟩
      change (11 : ZMod 281474980380673) ^ 610574794752 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2297, ?_⟩
      change (11 : ZMod 281474980380673) ^ 122540261376 ≠ 1
      reduce_mod_char
      decide

private theorem prime_293 : Nat.Prime 293 := by norm_num

private theorem prime_9857 : Nat.Prime 9857 := by norm_num

private theorem prime_11897 : Nat.Prime 11897 := by norm_num

private theorem prime_1125899881578497 : Nat.Prime 1125899881578497 := by
  apply lucasList (g := 3) [(2, 15), (293, 1), (9857, 1), (11897, 1)]
  · decide
  · change (3 : ZMod 1125899881578497) ^ 1125899881578496 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 1125899881578497) ^ 562949940789248 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_293, ?_⟩
      change (3 : ZMod 1125899881578497) ^ 3842661711872 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_9857, ?_⟩
      change (3 : ZMod 1125899881578497) ^ 114223382528 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11897, ?_⟩
      change (3 : ZMod 1125899881578497) ^ 94637293568 ≠ 1
      reduce_mod_char
      decide

private theorem prime_521 : Nat.Prime 521 := by norm_num

private theorem prime_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_8929 : Nat.Prime 8929 := by norm_num

private theorem prime_1125899910316033 : Nat.Prime 1125899910316033 := by
  apply lucasList (g := 10) [(2, 16), (3, 1), (521, 1), (1231, 1), (8929, 1)]
  · decide
  · change (10 : ZMod 1125899910316033) ^ 1125899910316032 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (10 : ZMod 1125899910316033) ^ 562949955158016 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (10 : ZMod 1125899910316033) ^ 375299970105344 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_521, ?_⟩
      change (10 : ZMod 1125899910316033) ^ 2161036296192 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1231, ?_⟩
      change (10 : ZMod 1125899910316033) ^ 914622185472 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_8929, ?_⟩
      change (10 : ZMod 1125899910316033) ^ 126094737408 ≠ 1
      reduce_mod_char
      decide

private theorem prime_23 : Nat.Prime 23 := by norm_num

private theorem prime_683 : Nat.Prime 683 := by norm_num

private theorem prime_3347 : Nat.Prime 3347 := by norm_num

private theorem prime_4503599583133697 : Nat.Prime 4503599583133697 := by
  apply lucasList (g := 3) [(2, 16), (23, 1), (683, 1), (1307, 1), (3347, 1)]
  · decide
  · change (3 : ZMod 4503599583133697) ^ 4503599583133696 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 4503599583133697) ^ 2251799791566848 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_23, ?_⟩
      change (3 : ZMod 4503599583133697) ^ 195808677527552 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_683, ?_⟩
      change (3 : ZMod 4503599583133697) ^ 6593850048512 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1307, ?_⟩
      change (3 : ZMod 4503599583133697) ^ 3445753315328 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3347, ?_⟩
      change (3 : ZMod 4503599583133697) ^ 1345563066368 ≠ 1
      reduce_mod_char
      decide

private theorem prime_2237 : Nat.Prime 2237 := by norm_num

private theorem prime_4503599628943361 : Nat.Prime 4503599628943361 := by
  apply lucasList (g := 6) [(2, 19), (5, 1), (11, 3), (577, 1), (2237, 1)]
  · decide
  · change (6 : ZMod 4503599628943361) ^ 4503599628943360 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (6 : ZMod 4503599628943361) ^ 2251799814471680 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (6 : ZMod 4503599628943361) ^ 900719925788672 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11, ?_⟩
      change (6 : ZMod 4503599628943361) ^ 409418148085760 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_577, ?_⟩
      change (6 : ZMod 4503599628943361) ^ 7805198663680 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2237, ?_⟩
      change (6 : ZMod 4503599628943361) ^ 2013231841280 ≠ 1
      reduce_mod_char
      decide

private theorem prime_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_7393 : Nat.Prime 7393 := by norm_num

private theorem prime_18014398432018433 : Nat.Prime 18014398432018433 := by
  apply lucasList (g := 5) [(2, 17), (19, 2), (23, 1), (2239, 1), (7393, 1)]
  · decide
  · change (5 : ZMod 18014398432018433) ^ 18014398432018432 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (5 : ZMod 18014398432018433) ^ 9007199216009216 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_19, ?_⟩
      change (5 : ZMod 18014398432018433) ^ 948126233264128 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_23, ?_⟩
      change (5 : ZMod 18014398432018433) ^ 783234714435584 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2239, ?_⟩
      change (5 : ZMod 18014398432018433) ^ 8045734002688 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7393, ?_⟩
      change (5 : ZMod 18014398432018433) ^ 2436683137024 ≠ 1
      reduce_mod_char
      decide

private theorem prime_3907 : Nat.Prime 3907 := by norm_num

private theorem prime_18014398516559873 : Nat.Prime 18014398516559873 := by
  apply lucasList (g := 3) [(2, 18), (7, 1), (613, 1), (3907, 1), (4099, 1)]
  · decide
  · change (3 : ZMod 18014398516559873) ^ 18014398516559872 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 18014398516559873) ^ 9007199258279936 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7, ?_⟩
      change (3 : ZMod 18014398516559873) ^ 2573485502365696 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_613, ?_⟩
      change (3 : ZMod 18014398516559873) ^ 29387273273344 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3907, ?_⟩
      change (3 : ZMod 18014398516559873) ^ 4610800746496 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_4099, ?_⟩
      change (3 : ZMod 18014398516559873) ^ 4394827644928 ≠ 1
      reduce_mod_char
      decide

private theorem prime_3557 : Nat.Prime 3557 := by norm_num

private theorem prime_3851 : Nat.Prime 3851 := by norm_num

private theorem prime_6689 : Nat.Prime 6689 := by norm_num

private theorem prime_72057593913409537 : Nat.Prime 72057593913409537 := by
  apply lucasList (g := 5) [(2, 18), (3, 1), (3557, 1), (3851, 1), (6689, 1)]
  · decide
  · change (5 : ZMod 72057593913409537) ^ 72057593913409536 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (5 : ZMod 72057593913409537) ^ 36028796956704768 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (5 : ZMod 72057593913409537) ^ 24019197971136512 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3557, ?_⟩
      change (5 : ZMod 72057593913409537) ^ 20257968488448 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3851, ?_⟩
      change (5 : ZMod 72057593913409537) ^ 18711398055936 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_6689, ?_⟩
      change (5 : ZMod 72057593913409537) ^ 10772551041024 ≠ 1
      reduce_mod_char
      decide

private theorem prime_72057594063093761 : Nat.Prime 72057594063093761 := by
  apply lucasList (g := 6) [(2, 23), (5, 1), (11, 3), (577, 1), (2237, 1)]
  · decide
  · change (6 : ZMod 72057594063093761) ^ 72057594063093760 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (6 : ZMod 72057594063093761) ^ 36028797031546880 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (6 : ZMod 72057594063093761) ^ 14411518812618752 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11, ?_⟩
      change (6 : ZMod 72057594063093761) ^ 6550690369372160 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_577, ?_⟩
      change (6 : ZMod 72057594063093761) ^ 124883178618880 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2237, ?_⟩
      change (6 : ZMod 72057594063093761) ^ 32211709460480 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_2633 : Nat.Prime 2633 := by norm_num

private theorem prime_288230375780515841 : Nat.Prime 288230375780515841 := by
  apply lucasList (g := 3) [(2, 21), (5, 1), (7, 1), (23, 1), (61, 1), (1063, 1), (2633, 1)]
  · decide
  · change (3 : ZMod 288230375780515841) ^ 288230375780515840 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 288230375780515841) ^ 144115187890257920 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (3 : ZMod 288230375780515841) ^ 57646075156103168 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7, ?_⟩
      change (3 : ZMod 288230375780515841) ^ 41175767968645120 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_23, ?_⟩
      change (3 : ZMod 288230375780515841) ^ 12531755468718080 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_61, ?_⟩
      change (3 : ZMod 288230375780515841) ^ 4725088127549440 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1063, ?_⟩
      change (3 : ZMod 288230375780515841) ^ 271148048711680 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2633, ?_⟩
      change (3 : ZMod 288230375780515841) ^ 109468429844480 ≠ 1
      reduce_mod_char
      decide

private theorem prime_17 : Nat.Prime 17 := by norm_num

private theorem prime_53 : Nat.Prime 53 := by norm_num

private theorem prime_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_3313 : Nat.Prime 3313 := by norm_num

private theorem prime_288230376334163969 : Nat.Prime 288230376334163969 := by
  apply lucasList (g := 3) [(2, 21), (17, 1), (41, 1), (53, 1), (1123, 1), (3313, 1)]
  · decide
  · change (3 : ZMod 288230376334163969) ^ 288230376334163968 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 288230376334163969) ^ 144115188167081984 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_17, ?_⟩
      change (3 : ZMod 288230376334163969) ^ 16954728019656704 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_41, ?_⟩
      change (3 : ZMod 288230376334163969) ^ 7030009178882048 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_53, ?_⟩
      change (3 : ZMod 288230376334163969) ^ 5438308987437056 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1123, ?_⟩
      change (3 : ZMod 288230376334163969) ^ 256661065302016 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3313, ?_⟩
      change (3 : ZMod 288230376334163969) ^ 86999811751936 ≠ 1
      reduce_mod_char
      decide

private theorem prime_107 : Nat.Prime 107 := by norm_num

private theorem prime_167 : Nat.Prime 167 := by norm_num

private theorem prime_47 : Nat.Prime 47 := by norm_num

private theorem prime_117877 : Nat.Prime 117877 := by
  apply lucasList (g := 2) [(2, 2), (3, 1), (11, 1), (19, 1), (47, 1)]
  · decide
  · change (2 : ZMod 117877) ^ 117876 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 117877) ^ 58938 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (2 : ZMod 117877) ^ 39292 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11, ?_⟩
      change (2 : ZMod 117877) ^ 10716 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_19, ?_⟩
      change (2 : ZMod 117877) ^ 6204 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_47, ?_⟩
      change (2 : ZMod 117877) ^ 2508 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1099511626987 : Nat.Prime 1099511626987 := by
  apply lucasList (g := 5) [(2, 1), (3, 2), (29, 1), (107, 1), (167, 1), (117877, 1)]
  · decide
  · change (5 : ZMod 1099511626987) ^ 1099511626986 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (5 : ZMod 1099511626987) ^ 549755813493 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (5 : ZMod 1099511626987) ^ 366503875662 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_29, ?_⟩
      change (5 : ZMod 1099511626987) ^ 37914194034 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_107, ?_⟩
      change (5 : ZMod 1099511626987) ^ 10275809598 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_167, ?_⟩
      change (5 : ZMod 1099511626987) ^ 6583901958 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_117877, ?_⟩
      change (5 : ZMod 1099511626987) ^ 9327618 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1152921503779520513 : Nat.Prime 1152921503779520513 := by
  apply lucasList (g := 3) [(2, 20), (1099511626987, 1)]
  · decide
  · change (3 : ZMod 1152921503779520513) ^ 1152921503779520512 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 1152921503779520513) ^ 576460751889760256 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1099511626987, ?_⟩
      change (3 : ZMod 1152921503779520513) ^ 1048576 ≠ 1
      reduce_mod_char
      decide

private theorem prime_37 : Nat.Prime 37 := by norm_num

private theorem prime_73 : Nat.Prime 73 := by norm_num

private theorem prime_109 : Nat.Prime 109 := by norm_num

private theorem prime_36650387593 : Nat.Prime 36650387593 := by
  apply lucasList (g := 5) [(2, 3), (3, 2), (7, 1), (13, 1), (19, 1), (37, 1), (73, 1), (109, 1)]
  · decide
  · change (5 : ZMod 36650387593) ^ 36650387592 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (5 : ZMod 36650387593) ^ 18325193796 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (5 : ZMod 36650387593) ^ 12216795864 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7, ?_⟩
      change (5 : ZMod 36650387593) ^ 5235769656 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_13, ?_⟩
      change (5 : ZMod 36650387593) ^ 2819260584 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_19, ?_⟩
      change (5 : ZMod 36650387593) ^ 1928967768 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_37, ?_⟩
      change (5 : ZMod 36650387593) ^ 990551016 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_73, ?_⟩
      change (5 : ZMod 36650387593) ^ 502060104 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_109, ?_⟩
      change (5 : ZMod 36650387593) ^ 336242088 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1099511627791 : Nat.Prime 1099511627791 := by
  apply lucasList (g := 3) [(2, 1), (3, 1), (5, 1), (36650387593, 1)]
  · decide
  · change (3 : ZMod 1099511627791) ^ 1099511627790 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 1099511627791) ^ 549755813895 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (3 : ZMod 1099511627791) ^ 366503875930 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (3 : ZMod 1099511627791) ^ 219902325558 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_36650387593, ?_⟩
      change (3 : ZMod 1099511627791) ^ 30 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1152921504622575617 : Nat.Prime 1152921504622575617 := by
  apply lucasList (g := 3) [(2, 20), (1099511627791, 1)]
  · decide
  · change (3 : ZMod 1152921504622575617) ^ 1152921504622575616 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 1152921504622575617) ^ 576460752311287808 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1099511627791, ?_⟩
      change (3 : ZMod 1152921504622575617) ^ 1048576 ≠ 1
      reduce_mod_char
      decide

private theorem prime_211 : Nat.Prime 211 := by norm_num

private theorem prime_4391 : Nat.Prime 4391 := by norm_num

private theorem prime_6133 : Nat.Prime 6133 := by norm_num

private theorem prime_4611686017208942593 : Nat.Prime 4611686017208942593 := by
  apply lucasList (g := 5) [(2, 21), (3, 2), (43, 1), (211, 1), (4391, 1), (6133, 1)]
  · decide
  · change (5 : ZMod 4611686017208942593) ^ 4611686017208942592 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (5 : ZMod 4611686017208942593) ^ 2305843008604471296 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (5 : ZMod 4611686017208942593) ^ 1537228672402980864 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_43, ?_⟩
      change (5 : ZMod 4611686017208942593) ^ 107248512028114944 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_211, ?_⟩
      change (5 : ZMod 4611686017208942593) ^ 21856331835113472 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_4391, ?_⟩
      change (5 : ZMod 4611686017208942593) ^ 1050258714918912 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_6133, ?_⟩
      change (5 : ZMod 4611686017208942593) ^ 751946195533824 ≠ 1
      reduce_mod_char
      decide

private theorem prime_173 : Nat.Prime 173 := by norm_num

private theorem prime_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_4611686018748252161 : Nat.Prime 4611686018748252161 := by
  apply lucasList (g := 3) [(2, 21), (5, 1), (31, 1), (37, 3), (173, 1), (1619, 1)]
  · decide
  · change (3 : ZMod 4611686018748252161) ^ 4611686018748252160 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 4611686018748252161) ^ 2305843009374126080 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (3 : ZMod 4611686018748252161) ^ 922337203749650432 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_31, ?_⟩
      change (3 : ZMod 4611686018748252161) ^ 148764065120911360 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_37, ?_⟩
      change (3 : ZMod 4611686018748252161) ^ 124640162668871680 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_173, ?_⟩
      change (3 : ZMod 4611686018748252161) ^ 26657144617041920 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1619, ?_⟩
      change (3 : ZMod 4611686018748252161) ^ 2848478084464640 ≠ 1
      reduce_mod_char
      decide

private theorem prime_4973 : Nat.Prime 4973 := by norm_num

private theorem prime_44219249 : Nat.Prime 44219249 := by
  apply lucasList (g := 3) [(2, 4), (23, 1), (107, 1), (1123, 1)]
  · decide
  · change (3 : ZMod 44219249) ^ 44219248 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 44219249) ^ 22109624 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_23, ?_⟩
      change (3 : ZMod 44219249) ^ 1922576 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_107, ?_⟩
      change (3 : ZMod 44219249) ^ 413264 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1123, ?_⟩
      change (3 : ZMod 44219249) ^ 39376 ≠ 1
      reduce_mod_char
      decide

private theorem prime_884384981 : Nat.Prime 884384981 := by
  apply lucasList (g := 2) [(2, 2), (5, 1), (44219249, 1)]
  · decide
  · change (2 : ZMod 884384981) ^ 884384980 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 884384981) ^ 442192490 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (2 : ZMod 884384981) ^ 176876996 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_44219249, ?_⟩
      change (2 : ZMod 884384981) ^ 20 ≠ 1
      reduce_mod_char
      decide

private theorem prime_18446744071230717953 : Nat.Prime 18446744071230717953 := by
  apply lucasList (g := 3) [(2, 22), (4973, 1), (884384981, 1)]
  · decide
  · change (3 : ZMod 18446744071230717953) ^ 18446744071230717952 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 18446744071230717953) ^ 9223372035615358976 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_4973, ?_⟩
      change (3 : ZMod 18446744071230717953) ^ 3709379463348224 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_884384981, ?_⟩
      change (3 : ZMod 18446744071230717953) ^ 20858273792 ≠ 1
      reduce_mod_char
      decide

private theorem prime_83 : Nat.Prime 83 := by norm_num

private theorem prime_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_8597 : Nat.Prime 8597 := by norm_num

private theorem prime_18446744074762321921 : Nat.Prime 18446744074762321921 := by
  apply lucasList (g := 26) [(2, 22), (3, 2), (5, 1), (7, 1), (17, 1), (83, 1), (1151, 1), (8597, 1)]
  · decide
  · change (26 : ZMod 18446744074762321921) ^ 18446744074762321920 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (26 : ZMod 18446744074762321921) ^ 9223372037381160960 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (26 : ZMod 18446744074762321921) ^ 6148914691587440640 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (26 : ZMod 18446744074762321921) ^ 3689348814952464384 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7, ?_⟩
      change (26 : ZMod 18446744074762321921) ^ 2635249153537474560 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_17, ?_⟩
      change (26 : ZMod 18446744074762321921) ^ 1085102592633077760 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_83, ?_⟩
      change (26 : ZMod 18446744074762321921) ^ 222249928611594240 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1151, ?_⟩
      change (26 : ZMod 18446744074762321921) ^ 16026710751313920 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_8597, ?_⟩
      change (26 : ZMod 18446744074762321921) ^ 2145718747791360 ≠ 1
      reduce_mod_char
      decide

private theorem prime_2143 : Nat.Prime 2143 := by norm_num

private theorem prime_2207 : Nat.Prime 2207 := by norm_num

private theorem prime_2719 : Nat.Prime 2719 := by norm_num

private theorem prime_73786976288026656769 : Nat.Prime 73786976288026656769 := by
  apply lucasList (g := 17) [(2, 25), (3, 2), (19, 1), (2143, 1), (2207, 1), (2719, 1)]
  · decide
  · change (17 : ZMod 73786976288026656769) ^ 73786976288026656768 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (17 : ZMod 73786976288026656769) ^ 36893488144013328384 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (17 : ZMod 73786976288026656769) ^ 24595658762675552256 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_19, ?_⟩
      change (17 : ZMod 73786976288026656769) ^ 3883525067790876672 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2143, ?_⟩
      change (17 : ZMod 73786976288026656769) ^ 34431626825957376 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2207, ?_⟩
      change (17 : ZMod 73786976288026656769) ^ 33433156451303424 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2719, ?_⟩
      change (17 : ZMod 73786976288026656769) ^ 27137541849219072 ≠ 1
      reduce_mod_char
      decide

private theorem prime_167441 : Nat.Prime 167441 := by
  apply lucasList (g := 3) [(2, 4), (5, 1), (7, 1), (13, 1), (23, 1)]
  · decide
  · change (3 : ZMod 167441) ^ 167440 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 167441) ^ 83720 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (3 : ZMod 167441) ^ 33488 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7, ?_⟩
      change (3 : ZMod 167441) ^ 23920 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_13, ?_⟩
      change (3 : ZMod 167441) ^ 12880 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_23, ?_⟩
      change (3 : ZMod 167441) ^ 7280 ≠ 1
      reduce_mod_char
      decide

private theorem prime_4353467 : Nat.Prime 4353467 := by
  apply lucasList (g := 2) [(2, 1), (13, 1), (167441, 1)]
  · decide
  · change (2 : ZMod 4353467) ^ 4353466 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 4353467) ^ 2176733 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_13, ?_⟩
      change (2 : ZMod 4353467) ^ 334882 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_167441, ?_⟩
      change (2 : ZMod 4353467) ^ 26 ≠ 1
      reduce_mod_char
      decide

private theorem prime_478881371 : Nat.Prime 478881371 := by
  apply lucasList (g := 11) [(2, 1), (5, 1), (11, 1), (4353467, 1)]
  · decide
  · change (11 : ZMod 478881371) ^ 478881370 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (11 : ZMod 478881371) ^ 239440685 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (11 : ZMod 478881371) ^ 95776274 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11, ?_⟩
      change (11 : ZMod 478881371) ^ 43534670 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_4353467, ?_⟩
      change (11 : ZMod 478881371) ^ 110 ≠ 1
      reduce_mod_char
      decide

private theorem prime_2199023255633 : Nat.Prime 2199023255633 := by
  apply lucasList (g := 6) [(2, 4), (7, 1), (41, 1), (478881371, 1)]
  · decide
  · change (6 : ZMod 2199023255633) ^ 2199023255632 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (6 : ZMod 2199023255633) ^ 1099511627816 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7, ?_⟩
      change (6 : ZMod 2199023255633) ^ 314146179376 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_41, ?_⟩
      change (6 : ZMod 2199023255633) ^ 53634713552 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_478881371, ?_⟩
      change (6 : ZMod 2199023255633) ^ 4592 ≠ 1
      reduce_mod_char
      decide

private theorem prime_73786976297556115457 : Nat.Prime 73786976297556115457 := by
  apply lucasList (g := 3) [(2, 25), (2199023255633, 1)]
  · decide
  · change (3 : ZMod 73786976297556115457) ^ 73786976297556115456 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 73786976297556115457) ^ 36893488148778057728 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2199023255633, ?_⟩
      change (3 : ZMod 73786976297556115457) ^ 33554432 ≠ 1
      reduce_mod_char
      decide

private theorem prime_271 : Nat.Prime 271 := by norm_num

private theorem prime_2741 : Nat.Prime 2741 := by norm_num

private theorem prime_2467 : Nat.Prime 2467 := by norm_num

private theorem prime_394721 : Nat.Prime 394721 := by
  apply lucasList (g := 3) [(2, 5), (5, 1), (2467, 1)]
  · decide
  · change (3 : ZMod 394721) ^ 394720 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 394721) ^ 197360 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (3 : ZMod 394721) ^ 78944 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2467, ?_⟩
      change (3 : ZMod 394721) ^ 160 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1759218604387 : Nat.Prime 1759218604387 := by
  apply lucasList (g := 3) [(2, 1), (3, 1), (271, 1), (2741, 1), (394721, 1)]
  · decide
  · change (3 : ZMod 1759218604387) ^ 1759218604386 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 1759218604387) ^ 879609302193 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (3 : ZMod 1759218604387) ^ 586406201462 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_271, ?_⟩
      change (3 : ZMod 1759218604387) ^ 6491581566 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2741, ?_⟩
      change (3 : ZMod 1759218604387) ^ 641816346 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_394721, ?_⟩
      change (3 : ZMod 1759218604387) ^ 4456866 ≠ 1
      reduce_mod_char
      decide

private theorem prime_295147905170192465921 : Nat.Prime 295147905170192465921 := by
  apply lucasList (g := 3) [(2, 25), (5, 1), (1759218604387, 1)]
  · decide
  · change (3 : ZMod 295147905170192465921) ^ 295147905170192465920 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 295147905170192465921) ^ 147573952585096232960 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (3 : ZMod 295147905170192465921) ^ 59029581034038493184 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1759218604387, ?_⟩
      change (3 : ZMod 295147905170192465921) ^ 167772160 ≠ 1
      reduce_mod_char
      decide

private theorem prime_277 : Nat.Prime 277 := by norm_num

private theorem prime_6761 : Nat.Prime 6761 := by norm_num

private theorem prime_151 : Nat.Prime 151 := by norm_num

private theorem prime_73387 : Nat.Prime 73387 := by
  apply lucasList (g := 2) [(2, 1), (3, 5), (151, 1)]
  · decide
  · change (2 : ZMod 73387) ^ 73386 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 73387) ^ 36693 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (2 : ZMod 73387) ^ 24462 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_151, ?_⟩
      change (2 : ZMod 73387) ^ 486 ≠ 1
      reduce_mod_char
      decide

private theorem prime_3969356057 : Nat.Prime 3969356057 := by
  apply lucasList (g := 3) [(2, 3), (6761, 1), (73387, 1)]
  · decide
  · change (3 : ZMod 3969356057) ^ 3969356056 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 3969356057) ^ 1984678028 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_6761, ?_⟩
      change (3 : ZMod 3969356057) ^ 587096 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_73387, ?_⟩
      change (3 : ZMod 3969356057) ^ 54088 ≠ 1
      reduce_mod_char
      decide

private theorem prime_2199023255579 : Nat.Prime 2199023255579 := by
  apply lucasList (g := 2) [(2, 1), (277, 1), (3969356057, 1)]
  · decide
  · change (2 : ZMod 2199023255579) ^ 2199023255578 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 2199023255579) ^ 1099511627789 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_277, ?_⟩
      change (2 : ZMod 2199023255579) ^ 7938712114 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3969356057, ?_⟩
      change (2 : ZMod 2199023255579) ^ 554 ≠ 1
      reduce_mod_char
      decide

private theorem prime_295147905182976704513 : Nat.Prime 295147905182976704513 := by
  apply lucasList (g := 3) [(2, 27), (2199023255579, 1)]
  · decide
  · change (3 : ZMod 295147905182976704513) ^ 295147905182976704512 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 295147905182976704513) ^ 147573952591488352256 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2199023255579, ?_⟩
      change (3 : ZMod 295147905182976704513) ^ 134217728 ≠ 1
      reduce_mod_char
      decide

private theorem prime_4157 : Nat.Prime 4157 := by norm_num

private theorem prime_3017983 : Nat.Prime 3017983 := by
  apply lucasList (g := 3) [(2, 1), (3, 1), (11, 2), (4157, 1)]
  · decide
  · change (3 : ZMod 3017983) ^ 3017982 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 3017983) ^ 1508991 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (3 : ZMod 3017983) ^ 1005994 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11, ?_⟩
      change (3 : ZMod 3017983) ^ 274362 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_4157, ?_⟩
      change (3 : ZMod 3017983) ^ 726 ≠ 1
      reduce_mod_char
      decide

private theorem prime_18107899 : Nat.Prime 18107899 := by
  apply lucasList (g := 10) [(2, 1), (3, 1), (3017983, 1)]
  · decide
  · change (10 : ZMod 18107899) ^ 18107898 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (10 : ZMod 18107899) ^ 9053949 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (10 : ZMod 18107899) ^ 6035966 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3017983, ?_⟩
      change (10 : ZMod 18107899) ^ 6 ≠ 1
      reduce_mod_char
      decide

private theorem prime_2498890063 : Nat.Prime 2498890063 := by
  apply lucasList (g := 3) [(2, 1), (3, 1), (23, 1), (18107899, 1)]
  · decide
  · change (3 : ZMod 2498890063) ^ 2498890062 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 2498890063) ^ 1249445031 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (3 : ZMod 2498890063) ^ 832963354 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_23, ?_⟩
      change (3 : ZMod 2498890063) ^ 108647394 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_18107899, ?_⟩
      change (3 : ZMod 2498890063) ^ 138 ≠ 1
      reduce_mod_char
      decide

private theorem prime_39982241009 : Nat.Prime 39982241009 := by
  apply lucasList (g := 3) [(2, 4), (2498890063, 1)]
  · decide
  · change (3 : ZMod 39982241009) ^ 39982241008 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 39982241009) ^ 19991120504 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2498890063, ?_⟩
      change (3 : ZMod 39982241009) ^ 16 ≠ 1
      reduce_mod_char
      decide

private theorem prime_79964482019 : Nat.Prime 79964482019 := by
  apply lucasList (g := 2) [(2, 1), (39982241009, 1)]
  · decide
  · change (2 : ZMod 79964482019) ^ 79964482018 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 79964482019) ^ 39982241009 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_39982241009, ?_⟩
      change (2 : ZMod 79964482019) ^ 2 ≠ 1
      reduce_mod_char
      decide

private theorem prime_8796093022091 : Nat.Prime 8796093022091 := by
  apply lucasList (g := 2) [(2, 1), (5, 1), (11, 1), (79964482019, 1)]
  · decide
  · change (2 : ZMod 8796093022091) ^ 8796093022090 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 8796093022091) ^ 4398046511045 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (2 : ZMod 8796093022091) ^ 1759218604418 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11, ?_⟩
      change (2 : ZMod 8796093022091) ^ 799644820190 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_79964482019, ?_⟩
      change (2 : ZMod 8796093022091) ^ 110 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1180591620701707829249 : Nat.Prime 1180591620701707829249 := by
  apply lucasList (g := 3) [(2, 27), (8796093022091, 1)]
  · decide
  · change (3 : ZMod 1180591620701707829249) ^ 1180591620701707829248 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 1180591620701707829249) ^ 590295810350853914624 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_8796093022091, ?_⟩
      change (3 : ZMod 1180591620701707829249) ^ 134217728 ≠ 1
      reduce_mod_char
      decide

private theorem prime_607 : Nat.Prime 607 := by norm_num

private theorem prime_2039 : Nat.Prime 2039 := by norm_num

private theorem prime_17327423 : Nat.Prime 17327423 := by
  apply lucasList (g := 5) [(2, 1), (7, 1), (607, 1), (2039, 1)]
  · decide
  · change (5 : ZMod 17327423) ^ 17327422 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (5 : ZMod 17327423) ^ 8663711 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7, ?_⟩
      change (5 : ZMod 17327423) ^ 2475346 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_607, ?_⟩
      change (5 : ZMod 17327423) ^ 28546 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2039, ?_⟩
      change (5 : ZMod 17327423) ^ 8498 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1282229303 : Nat.Prime 1282229303 := by
  apply lucasList (g := 5) [(2, 1), (37, 1), (17327423, 1)]
  · decide
  · change (5 : ZMod 1282229303) ^ 1282229302 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (5 : ZMod 1282229303) ^ 641114651 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_37, ?_⟩
      change (5 : ZMod 1282229303) ^ 34654846 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_17327423, ?_⟩
      change (5 : ZMod 1282229303) ^ 74 ≠ 1
      reduce_mod_char
      decide

private theorem prime_2564458607 : Nat.Prime 2564458607 := by
  apply lucasList (g := 5) [(2, 1), (1282229303, 1)]
  · decide
  · change (5 : ZMod 2564458607) ^ 2564458606 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (5 : ZMod 2564458607) ^ 1282229303 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1282229303, ?_⟩
      change (5 : ZMod 2564458607) ^ 2 ≠ 1
      reduce_mod_char
      decide

private theorem prime_51289172141 : Nat.Prime 51289172141 := by
  apply lucasList (g := 2) [(2, 2), (5, 1), (2564458607, 1)]
  · decide
  · change (2 : ZMod 51289172141) ^ 51289172140 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 51289172141) ^ 25644586070 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (2 : ZMod 51289172141) ^ 10257834428 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2564458607, ?_⟩
      change (2 : ZMod 51289172141) ^ 20 ≠ 1
      reduce_mod_char
      decide

private theorem prime_102578344283 : Nat.Prime 102578344283 := by
  apply lucasList (g := 2) [(2, 1), (51289172141, 1)]
  · decide
  · change (2 : ZMod 102578344283) ^ 102578344282 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 102578344283) ^ 51289172141 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_51289172141, ?_⟩
      change (2 : ZMod 102578344283) ^ 2 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1180591620725363703809 : Nat.Prime 1180591620725363703809 := by
  apply lucasList (g := 3) [(2, 25), (7, 3), (102578344283, 1)]
  · decide
  · change (3 : ZMod 1180591620725363703809) ^ 1180591620725363703808 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 1180591620725363703809) ^ 590295810362681851904 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7, ?_⟩
      change (3 : ZMod 1180591620725363703809) ^ 168655945817909100544 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_102578344283, ?_⟩
      change (3 : ZMod 1180591620725363703809) ^ 11509170176 ≠ 1
      reduce_mod_char
      decide

private theorem prime_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_311 : Nat.Prime 311 := by norm_num

private theorem prime_10300321 : Nat.Prime 10300321 := by
  apply lucasList (g := 7) [(2, 5), (3, 2), (5, 1), (23, 1), (311, 1)]
  · decide
  · change (7 : ZMod 10300321) ^ 10300320 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (7 : ZMod 10300321) ^ 5150160 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (7 : ZMod 10300321) ^ 3433440 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (7 : ZMod 10300321) ^ 2060064 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_23, ?_⟩
      change (7 : ZMod 10300321) ^ 447840 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_311, ?_⟩
      change (7 : ZMod 10300321) ^ 33120 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1599289640387 : Nat.Prime 1599289640387 := by
  apply lucasList (g := 2) [(2, 1), (29, 1), (2677, 1), (10300321, 1)]
  · decide
  · change (2 : ZMod 1599289640387) ^ 1599289640386 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 1599289640387) ^ 799644820193 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_29, ?_⟩
      change (2 : ZMod 1599289640387) ^ 55147918634 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2677, ?_⟩
      change (2 : ZMod 1599289640387) ^ 597418618 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_10300321, ?_⟩
      change (2 : ZMod 1599289640387) ^ 155266 ≠ 1
      reduce_mod_char
      decide

private theorem prime_4722366482826963976193 : Nat.Prime 4722366482826963976193 := by
  apply lucasList (g := 3) [(2, 28), (11, 1), (1599289640387, 1)]
  · decide
  · change (3 : ZMod 4722366482826963976193) ^ 4722366482826963976192 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 4722366482826963976193) ^ 2361183241413481988096 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11, ?_⟩
      change (3 : ZMod 4722366482826963976193) ^ 429306043893360361472 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1599289640387, ?_⟩
      change (3 : ZMod 4722366482826963976193) ^ 2952790016 ≠ 1
      reduce_mod_char
      decide

private theorem prime_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_1704173791 : Nat.Prime 1704173791 := by
  apply lucasList (g := 11) [(2, 1), (3, 1), (5, 1), (11, 1), (683, 1), (7561, 1)]
  · decide
  · change (11 : ZMod 1704173791) ^ 1704173790 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (11 : ZMod 1704173791) ^ 852086895 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (11 : ZMod 1704173791) ^ 568057930 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (11 : ZMod 1704173791) ^ 340834758 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11, ?_⟩
      change (11 : ZMod 1704173791) ^ 154924890 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_683, ?_⟩
      change (11 : ZMod 1704173791) ^ 2495130 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7561, ?_⟩
      change (11 : ZMod 1704173791) ^ 225390 ≠ 1
      reduce_mod_char
      decide

private theorem prime_1901857950757 : Nat.Prime 1901857950757 := by
  apply lucasList (g := 2) [(2, 2), (3, 2), (31, 1), (1704173791, 1)]
  · decide
  · change (2 : ZMod 1901857950757) ^ 1901857950756 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 1901857950757) ^ 950928975378 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (2 : ZMod 1901857950757) ^ 633952650252 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_31, ?_⟩
      change (2 : ZMod 1901857950757) ^ 61350256476 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1704173791, ?_⟩
      change (2 : ZMod 1901857950757) ^ 1116 ≠ 1
      reduce_mod_char
      decide

private theorem prime_4722366482892797771777 : Nat.Prime 4722366482892797771777 := by
  apply lucasList (g := 3) [(2, 26), (37, 1), (1901857950757, 1)]
  · decide
  · change (3 : ZMod 4722366482892797771777) ^ 4722366482892797771776 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 4722366482892797771777) ^ 2361183241446398885888 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_37, ?_⟩
      change (3 : ZMod 4722366482892797771777) ^ 127631526564670210048 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_1901857950757, ?_⟩
      change (3 : ZMod 4722366482892797771777) ^ 2483027968 ≠ 1
      reduce_mod_char
      decide

private theorem prime_97 : Nat.Prime 97 := by norm_num

private theorem prime_157 : Nat.Prime 157 := by norm_num

private theorem prime_10627 : Nat.Prime 10627 := by norm_num

private theorem prime_2104147 : Nat.Prime 2104147 := by
  apply lucasList (g := 2) [(2, 1), (3, 2), (11, 1), (10627, 1)]
  · decide
  · change (2 : ZMod 2104147) ^ 2104146 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 2104147) ^ 1052073 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (2 : ZMod 2104147) ^ 701382 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11, ?_⟩
      change (2 : ZMod 2104147) ^ 191286 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_10627, ?_⟩
      change (2 : ZMod 2104147) ^ 198 ≠ 1
      reduce_mod_char
      decide

private theorem prime_513411869 : Nat.Prime 513411869 := by
  apply lucasList (g := 2) [(2, 2), (61, 1), (2104147, 1)]
  · decide
  · change (2 : ZMod 513411869) ^ 513411868 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 513411869) ^ 256705934 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_61, ?_⟩
      change (2 : ZMod 513411869) ^ 8416588 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_2104147, ?_⟩
      change (2 : ZMod 513411869) ^ 244 ≠ 1
      reduce_mod_char
      decide

private theorem prime_161211326867 : Nat.Prime 161211326867 := by
  apply lucasList (g := 2) [(2, 1), (157, 1), (513411869, 1)]
  · decide
  · change (2 : ZMod 161211326867) ^ 161211326866 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (2 : ZMod 161211326867) ^ 80605663433 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_157, ?_⟩
      change (2 : ZMod 161211326867) ^ 1026823738 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_513411869, ?_⟩
      change (2 : ZMod 161211326867) ^ 314 ≠ 1
      reduce_mod_char
      decide

private theorem prime_18889465931419927707649 : Nat.Prime 18889465931419927707649 := by
  apply lucasList (g := 13) [(2, 27), (3, 2), (97, 1), (161211326867, 1)]
  · decide
  · change (13 : ZMod 18889465931419927707649) ^ 18889465931419927707648 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (13 : ZMod 18889465931419927707649) ^ 9444732965709963853824 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (13 : ZMod 18889465931419927707649) ^ 6296488643806642569216 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_97, ?_⟩
      change (13 : ZMod 18889465931419927707649) ^ 194736762179586883584 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_161211326867, ?_⟩
      change (13 : ZMod 18889465931419927707649) ^ 117172076544 ≠ 1
      reduce_mod_char
      decide

private theorem prime_467 : Nat.Prime 467 := by norm_num

private theorem prime_7949 : Nat.Prime 7949 := by norm_num

private theorem prime_18889465931498310860801 : Nat.Prime 18889465931498310860801 := by
  apply lucasList (g := 3) [(2, 27), (5, 2), (11, 2), (83, 1), (151, 1), (467, 1), (7949, 1)]
  · decide
  · change (3 : ZMod 18889465931498310860801) ^ 18889465931498310860800 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 18889465931498310860801) ^ 9444732965749155430400 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (3 : ZMod 18889465931498310860801) ^ 3777893186299662172160 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11, ?_⟩
      change (3 : ZMod 18889465931498310860801) ^ 1717224175590755532800 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_83, ?_⟩
      change (3 : ZMod 18889465931498310860801) ^ 227583926885521817600 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_151, ?_⟩
      change (3 : ZMod 18889465931498310860801) ^ 125095800870849740800 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_467, ?_⟩
      change (3 : ZMod 18889465931498310860801) ^ 40448535185221222400 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7949, ?_⟩
      change (3 : ZMod 18889465931498310860801) ^ 2376332360233779200 ≠ 1
      reduce_mod_char
      decide

private theorem prime_307 : Nat.Prime 307 := by norm_num

private theorem prime_5101 : Nat.Prime 5101 := by norm_num

private theorem prime_75557863725718633971713 : Nat.Prime 75557863725718633971713 := by
  apply lucasList (g := 3) [(2, 28), (7, 1), (11, 1), (13, 1), (23, 1), (37, 1), (211, 1), (307, 1), (5101, 1)]
  · decide
  · change (3 : ZMod 75557863725718633971713) ^ 75557863725718633971712 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 75557863725718633971713) ^ 37778931862859316985856 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7, ?_⟩
      change (3 : ZMod 75557863725718633971713) ^ 10793980532245519138816 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11, ?_⟩
      change (3 : ZMod 75557863725718633971713) ^ 6868896702338057633792 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_13, ?_⟩
      change (3 : ZMod 75557863725718633971713) ^ 5812143363516817997824 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_23, ?_⟩
      change (3 : ZMod 75557863725718633971713) ^ 3285124509813853650944 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_37, ?_⟩
      change (3 : ZMod 75557863725718633971713) ^ 2042104425019422539776 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_211, ?_⟩
      change (3 : ZMod 75557863725718633971713) ^ 358094140880183099392 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_307, ?_⟩
      change (3 : ZMod 75557863725718633971713) ^ 246116819953480892416 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5101, ?_⟩
      change (3 : ZMod 75557863725718633971713) ^ 14812363012295360512 ≠ 1
      reduce_mod_char
      decide

private theorem prime_59 : Nat.Prime 59 := by norm_num

private theorem prime_149 : Nat.Prime 149 := by norm_num

private theorem prime_202343 : Nat.Prime 202343 := by
  apply lucasList (g := 5) [(2, 1), (7, 1), (97, 1), (149, 1)]
  · decide
  · change (5 : ZMod 202343) ^ 202342 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (5 : ZMod 202343) ^ 101171 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7, ?_⟩
      change (5 : ZMod 202343) ^ 28906 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_97, ?_⟩
      change (5 : ZMod 202343) ^ 2086 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_149, ?_⟩
      change (5 : ZMod 202343) ^ 1358 ≠ 1
      reduce_mod_char
      decide

private theorem prime_14325884401 : Nat.Prime 14325884401 := by
  apply lucasList (g := 7) [(2, 4), (3, 1), (5, 2), (59, 1), (202343, 1)]
  · decide
  · change (7 : ZMod 14325884401) ^ 14325884400 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (7 : ZMod 14325884401) ^ 7162942200 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (7 : ZMod 14325884401) ^ 4775294800 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (7 : ZMod 14325884401) ^ 2865176880 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_59, ?_⟩
      change (7 : ZMod 14325884401) ^ 242811600 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_202343, ?_⟩
      change (7 : ZMod 14325884401) ^ 70800 ≠ 1
      reduce_mod_char
      decide

private theorem prime_75557863725965863026689 : Nat.Prime 75557863725965863026689 := by
  apply lucasList (g := 3) [(2, 34), (307, 1), (14325884401, 1)]
  · decide
  · change (3 : ZMod 75557863725965863026689) ^ 75557863725965863026688 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 75557863725965863026689) ^ 37778931862982931513344 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_307, ?_⟩
      change (3 : ZMod 75557863725965863026689) ^ 246116819954286198784 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_14325884401, ?_⟩
      change (3 : ZMod 75557863725965863026689) ^ 5274219839488 ≠ 1
      reduce_mod_char
      decide

private theorem prime_3041 : Nat.Prime 3041 := by norm_num

private theorem prime_6343 : Nat.Prime 6343 := by norm_num

private theorem prime_302231454903269672878081 : Nat.Prime 302231454903269672878081 := by
  apply lucasList (g := 11) [(2, 30), (3, 2), (5, 1), (23, 2), (613, 1), (3041, 1), (6343, 1)]
  · decide
  · change (11 : ZMod 302231454903269672878081) ^ 302231454903269672878080 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (11 : ZMod 302231454903269672878081) ^ 151115727451634836439040 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (11 : ZMod 302231454903269672878081) ^ 100743818301089890959360 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (11 : ZMod 302231454903269672878081) ^ 60446290980653934575616 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_23, ?_⟩
      change (11 : ZMod 302231454903269672878081) ^ 13140498039272594472960 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_613, ?_⟩
      change (11 : ZMod 302231454903269672878081) ^ 493036631163572060160 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3041, ?_⟩
      change (11 : ZMod 302231454903269672878081) ^ 99385549129651322880 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_6343, ?_⟩
      change (11 : ZMod 302231454903269672878081) ^ 47648030096684482560 ≠ 1
      reduce_mod_char
      decide

private theorem prime_331 : Nat.Prime 331 := by norm_num

private theorem prime_18837001 : Nat.Prime 18837001 := by
  apply lucasList (g := 19) [(2, 3), (3, 2), (5, 3), (7, 1), (13, 1), (23, 1)]
  · decide
  · change (19 : ZMod 18837001) ^ 18837000 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (19 : ZMod 18837001) ^ 9418500 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (19 : ZMod 18837001) ^ 6279000 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_5, ?_⟩
      change (19 : ZMod 18837001) ^ 3767400 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_7, ?_⟩
      change (19 : ZMod 18837001) ^ 2691000 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_13, ?_⟩
      change (19 : ZMod 18837001) ^ 1449000 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_23, ?_⟩
      change (19 : ZMod 18837001) ^ 819000 ≠ 1
      reduce_mod_char
      decide

private theorem prime_51177268492849 : Nat.Prime 51177268492849 := by
  apply lucasList (g := 13) [(2, 4), (3, 3), (19, 1), (331, 1), (18837001, 1)]
  · decide
  · change (13 : ZMod 51177268492849) ^ 51177268492848 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (13 : ZMod 51177268492849) ^ 25588634246424 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_3, ?_⟩
      change (13 : ZMod 51177268492849) ^ 17059089497616 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_19, ?_⟩
      change (13 : ZMod 51177268492849) ^ 2693540446992 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_331, ?_⟩
      change (13 : ZMod 51177268492849) ^ 154614104208 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_18837001, ?_⟩
      change (13 : ZMod 51177268492849) ^ 2716848 ≠ 1
      reduce_mod_char
      decide

private theorem prime_302231454903671789191169 : Nat.Prime 302231454903671789191169 := by
  apply lucasList (g := 3) [(2, 29), (11, 1), (51177268492849, 1)]
  · decide
  · change (3 : ZMod 302231454903671789191169) ^ 302231454903671789191168 = 1
    reduce_mod_char
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨prime_2, ?_⟩
      change (3 : ZMod 302231454903671789191169) ^ 151115727451835894595584 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_11, ?_⟩
      change (3 : ZMod 302231454903671789191169) ^ 27475586809424708108288 ≠ 1
      reduce_mod_char
      decide
    · refine ⟨prime_51177268492849, ?_⟩
      change (3 : ZMod 302231454903671789191169) ^ 5905580032 ≠ 1
      reduce_mod_char
      decide

/-- Both prime intervals hit at every exponent in this finite range. -/
theorem certifiedPairs (s : ℕ) (hs : 2 ≤ s) (ht : s ≤ 32) :
    let t := (2:ℕ)^s
    let X := (128*t)^2
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ X-104*t < p ∧
      5*(p-(X-104*t)) ≤ 256*t ∧ X < q ∧ 5*(q-X) ≤ 256*t := by
  interval_cases s
  · exact ⟨261761, 262337, prime_261761, prime_262337, by decide⟩
  · exact ⟨1047833, 1048829, prime_1047833, prime_1048829, by decide⟩
  · exact ⟨4193209, 4195001, prime_4193209, prime_4195001, by decide⟩
  · exact ⟨16775489, 16778309, prime_16775489, prime_16778309, by decide⟩
  · exact ⟨67103249, 67110497, prime_67103249, prime_67110497, by decide⟩
  · exact ⟨268426849, 268439009, prime_268426849, prime_268439009, by decide⟩
  · exact ⟨1073720993, 1073749889, prime_1073720993, prime_1073749889, by decide⟩
  · exact ⟨4294917569, 4294991873, prime_4294917569, prime_4294991873, by decide⟩
  · exact ⟨17179793537, 17179897601, prime_17179793537, prime_17179897601, by decide⟩
  · exact ⟨68719306753, 68719562753, prime_68719306753, prime_68719562753, by decide⟩
  · exact ⟨274877501441, 274877917697, prime_274877501441, prime_274877917697, by decide⟩
  · exact ⟨1099510899713, 1099511799809, prime_1099510899713, prime_1099511799809, by decide⟩
  · exact ⟨4398044921857, 4398047322113, prime_4398044921857, prime_4398047322113, by decide⟩
  · exact ⟨17592184287233, 17592186634241, prime_17592184287233, prime_17592186634241, by decide⟩
  · exact ⟨70368738410497, 70368744570881, prime_70368738410497, prime_70368744570881, by decide⟩
  · exact ⟨281474965536769, 281474980380673, prime_281474965536769, prime_281474980380673, by decide⟩
  · exact ⟨1125899881578497, 1125899910316033, prime_1125899881578497, prime_1125899910316033, by decide⟩
  · exact ⟨4503599583133697, 4503599628943361, prime_4503599583133697, prime_4503599628943361, by decide⟩
  · exact ⟨18014398432018433, 18014398516559873, prime_18014398432018433, prime_18014398516559873, by decide⟩
  · exact ⟨72057593913409537, 72057594063093761, prime_72057593913409537, prime_72057594063093761, by decide⟩
  · exact ⟨288230375780515841, 288230376334163969, prime_288230375780515841, prime_288230376334163969, by decide⟩
  · exact ⟨1152921503779520513, 1152921504622575617, prime_1152921503779520513, prime_1152921504622575617, by decide⟩
  · exact ⟨4611686017208942593, 4611686018748252161, prime_4611686017208942593, prime_4611686018748252161, by decide⟩
  · exact ⟨18446744071230717953, 18446744074762321921, prime_18446744071230717953, prime_18446744074762321921, by decide⟩
  · exact ⟨73786976288026656769, 73786976297556115457, prime_73786976288026656769, prime_73786976297556115457, by decide⟩
  · exact ⟨295147905170192465921, 295147905182976704513, prime_295147905170192465921, prime_295147905182976704513, by decide⟩
  · exact ⟨1180591620701707829249, 1180591620725363703809, prime_1180591620701707829249, prime_1180591620725363703809, by decide⟩
  · exact ⟨4722366482826963976193, 4722366482892797771777, prime_4722366482826963976193, prime_4722366482892797771777, by decide⟩
  · exact ⟨18889465931419927707649, 18889465931498310860801, prime_18889465931419927707649, prime_18889465931498310860801, by decide⟩
  · exact ⟨75557863725718633971713, 75557863725965863026689, prime_75557863725718633971713, prime_75557863725965863026689, by decide⟩
  · exact ⟨302231454903269672878081, 302231454903671789191169, prime_302231454903269672878081, prime_302231454903671789191169, by decide⟩

/-- Each dyadic exponent in the certified range gives a primitive weird number
with the indicated exact 2-adic valuation. -/
theorem weirdAtEachScale (s : ℕ) (hs : 2 ≤ s) (ht : s ≤ 32) :
    ∃ n : ℕ, Erdos470.PrimitiveWeird n ∧ padicValNat 2 n = 2*s+12 := by
  let t := (2:ℕ)^s
  let k := 2*s+12
  have large : 4 ≤ t := (by decide : 4 ≤ (2:ℕ)^2).trans
    (Nat.pow_le_pow_right (by decide) (by omega : 2 ≤ s))
  have hx : 2^(k+2) = (128*t)^2 := by
    dsimp [k,t]
    rw [show 2*s+12+2 = (s+7)*2 by omega, pow_mul, pow_add]
    norm_num
    ring
  obtain ⟨p, q, hp, hq, hl, hl', hu, hu'⟩ := certifiedPairs s hs ht
  obtain ⟨a, b, hsep, hab, hpa, hqb⟩ :=
    OMA.R_Erdos470_erdos_470_parts_ii_R1_H2_R1.offsets large hp hq hl hl' hu hu'
  rw [← hx] at hab hpa hqb
  let P := 2^(k+2) - a
  let Q := 2^(k+2) + b
  change Nat.Prime P at hpa
  change Nat.Prime Q at hqb
  have plenty : 8 ≤ 2^(k+2) := by rw [hx]; nlinarith
  have ha2 : 2*a ≤ a*(a+b) := by
    have bound := Nat.mul_le_mul_left a (show 2 ≤ a+b by omega)
    omega
  have p2 : P ≠ 2 := by dsimp [P]; omega
  have q2 : Q ≠ 2 := by dsimp [Q]; omega
  have vP := padicValNat.eq_zero_of_not_dvd (p := 2)
    (fun h => p2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpa).mp h).symm)
  have vQ := padicValNat.eq_zero_of_not_dvd (p := 2)
    (fun h => q2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hqb).mp h).symm)
  refine ⟨2^k*P*Q, OMAMelfi.melfi k a b hsep hab hpa hqb, ?_⟩
  rw [padicValNat.mul (Nat.mul_ne_zero (by positivity) hpa.ne_zero) hqb.ne_zero,
    padicValNat.mul (by positivity) hpa.ne_zero, padicValNat.pow, padicValNat.self (by decide),
    vP, vQ]
  simp [k]

/-- The witnesses are pairwise distinct, as their exact valuations differ. -/
theorem distinctPrimitiveWeird :
    ∃ f : Fin (32-2+1) ↪ ℕ, ∀ i, Erdos470.PrimitiveWeird (f i) ∧
      padicValNat 2 (f i) = 2*(i.val+2)+12 := by
  classical
  have h (i : Fin (32-2+1)) :=
    weirdAtEachScale (i.val+2) (by omega) (by have := i.isLt; omega)
  choose n hn using h
  let f : Fin (32-2+1) ↪ ℕ :=
    ⟨n, fun i j eq => Fin.ext (by
      have eqv := congrArg (padicValNat 2) eq
      rw [(hn i).2, (hn j).2] at eqv
      omega)⟩
  exact ⟨f, hn⟩


end OMA.Erdos470Examples
