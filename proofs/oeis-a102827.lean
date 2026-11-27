import OMAStatements.S_oeis_a102827

open OMA.S_oeis_a102827

namespace DecimalDigitCount

def advance (b : ℕ) (s : ℕ × List ℕ) : ℕ × List ℕ :=
  let v := nextValue b s.2
  (v, addDigits b v s.2)

def steps (b : ℕ) (s : ℕ × List ℕ) : ℕ → ℕ × List ℕ
  | 0 => s
  | k+1 => advance b (steps b s k)

lemma shift (b n k : ℕ) : state b (n+k) = steps b (state b n) k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (advance b) ih

-- Each equality is checked from the previous digit counts.

lemma at0 : state 10 0 = (1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  decide

lemma at16 : state 10 16 = (18, [0, 10, 2, 2, 2, 2, 2, 2, 2, 1]) := by
  rw [show 16 = 0+16 by decide, shift, at0]
  decide

lemma at32 : state 10 32 = (39, [0, 11, 11, 11, 4, 4, 4, 4, 4, 4]) := by
  rw [show 32 = 16+16 by decide, shift, at16]
  decide

lemma at48 : state 10 48 = (77, [0, 11, 11, 11, 11, 11, 11, 9, 7, 7]) := by
  rw [show 48 = 32+16 by decide, shift, at32]
  decide

lemma at64 : state 10 64 = (123, [0, 32, 15, 13, 12, 12, 12, 12, 12, 12]) := by
  rw [show 64 = 48+16 by decide, shift, at48]
  decide

lemma at80 : state 10 80 = (146, [0, 48, 21, 21, 18, 15, 15, 14, 14, 14]) := by
  rw [show 80 = 64+16 by decide, shift, at64]
  decide

lemma at96 : state 10 96 = (188, [0, 64, 21, 21, 21, 21, 21, 21, 20, 18]) := by
  rw [show 96 = 80+16 by decide, shift, at80]
  decide

lemma at112 : state 10 112 = (228, [0, 74, 42, 23, 23, 23, 23, 23, 23, 22]) := by
  rw [show 112 = 96+16 by decide, shift, at96]
  decide

lemma at128 : state 10 128 = (256, [0, 74, 59, 31, 31, 28, 26, 25, 25, 25]) := by
  rw [show 128 = 112+16 by decide, shift, at112]
  decide

lemma at144 : state 10 144 = (315, [0, 77, 72, 35, 32, 32, 31, 31, 31, 31]) := by
  rw [show 144 = 128+16 by decide, shift, at128]
  decide

lemma at160 : state 10 160 = (339, [0, 81, 78, 57, 34, 34, 34, 34, 34, 34]) := by
  rw [show 160 = 144+16 by decide, shift, at144]
  decide

lemma at176 : state 10 176 = (377, [0, 81, 78, 73, 41, 41, 41, 39, 37, 37]) := by
  rw [show 176 = 160+16 by decide, shift, at160]
  decide

lemma at192 : state 10 192 = (429, [0, 87, 83, 78, 53, 43, 43, 43, 43, 43]) := by
  rw [show 192 = 176+16 by decide, shift, at176]
  decide

lemma at208 : state 10 208 = (466, [0, 87, 83, 83, 74, 51, 48, 46, 46, 46]) := by
  rw [show 208 = 192+16 by decide, shift, at192]
  decide

lemma at224 : state 10 224 = (527, [0, 92, 85, 83, 83, 59, 53, 53, 52, 52]) := by
  rw [show 224 = 208+16 by decide, shift, at208]
  decide

lemma at240 : state 10 240 = (567, [0, 92, 87, 87, 87, 79, 59, 57, 56, 56]) := by
  rw [show 240 = 224+16 by decide, shift, at224]
  decide

lemma at256 : state 10 256 = (637, [0, 96, 90, 88, 87, 87, 70, 64, 63, 63]) := by
  rw [show 256 = 240+16 by decide, shift, at240]
  decide

lemma at272 : state 10 272 = (689, [0, 96, 90, 90, 90, 90, 89, 71, 71, 69]) := by
  rw [show 272 = 256+16 by decide, shift, at256]
  decide

lemma at288 : state 10 288 = (779, [0, 99, 92, 92, 92, 92, 92, 89, 78, 78]) := by
  rw [show 288 = 272+16 by decide, shift, at272]
  decide

lemma at304 : state 10 304 = (934, [0, 102, 94, 95, 94, 93, 93, 93, 93, 95]) := by
  rw [show 304 = 288+16 by decide, shift, at288]
  decide

lemma at320 : state 10 320 = (968, [0, 102, 97, 99, 99, 99, 99, 97, 97, 111]) := by
  rw [show 320 = 304+16 by decide, shift, at304]
  decide

lemma at331 : state 10 331 = (1002, [2, 103, 101, 100, 100, 100, 100, 100, 100, 128]) := by
  rw [show 331 = 320+11 by decide, shift, at320]
  decide

lemma at332 : state 10 332 = (20, [3, 103, 102, 100, 100, 100, 100, 100, 100, 128]) := by
  rw [show 332 = 331+1 by decide, shift, at331]
  decide

end DecimalDigitCount

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a102827.main) := by
  intro h
  have witness := h 10 (by decide) 332
  rw [DecimalDigitCount.at332] at witness
  exact witness (by decide)
