import OMAStatements.S_oeis_a072031

/-!
Peter Bala's coefficient identity for the square of the divisor Lambert series.
Both sides count factorizations in a decomposition of `n` as a sum of two
positive products. Extracting a common divisor from opposite factors turns
one count into the other. This is the factor-pair bijection underlying the
Busche–Ramanujan identity for the divisor function.
-/

namespace OEISA072031

open Finset OMA.S_oeis_a072031

private abbrev LeftKey := Σ _ : ℕ, (ℕ × ℕ) × (ℕ × ℕ)
private abbrev RightKey := Σ _ : ℕ × ℕ, Σ _ : ℕ, ℕ × ℕ

private def leftSet (n : ℕ) : Finset LeftKey :=
  (Icc 1 n).sigma fun k => k.divisorsAntidiagonal ×ˢ (n - k).divisorsAntidiagonal

private def rightSet (n : ℕ) : Finset RightKey :=
  n.divisorsAntidiagonal.sigma fun gd =>
    (Icc 1 gd.2).sigma fun u => (u * (gd.2 - u)).divisorsAntidiagonal

private def leftKey (g a b c d : ℕ) : LeftKey :=
  ⟨g * (a * b), (g * a, b), (c, g * d)⟩

private def rightKey (g a b c d : ℕ) : RightKey :=
  ⟨(g, a * b + c * d), a * b, (a * c, b * d)⟩

private def forward (l : LeftKey) : RightKey :=
  let g := l.2.1.1.gcd l.2.2.2
  rightKey g (l.2.1.1 / g) l.2.1.2 l.2.2.1 (l.2.2.2 / g)

private def backward (r : RightKey) : LeftKey :=
  let v := r.1.2 - r.2.1
  let c := r.2.2.1.gcd v
  let a := r.2.2.1 / c
  leftKey r.1.1 a (r.2.1 / a) c (v / c)

private theorem forward_key {g a b c d : ℕ} (hg : 0 < g) (h : a.Coprime d) :
    forward (leftKey g a b c d) = rightKey g a b c d := by
  simp [forward, leftKey, Nat.gcd_mul_left, h.gcd_eq_one, hg]

private theorem backward_key {g a b c d : ℕ} (ha : 0 < a) (hc : 0 < c) (h : a.Coprime d) :
    backward (rightKey g a b c d) = leftKey g a b c d := by
  simp [backward, rightKey, Nat.mul_comm a c, Nat.gcd_mul_left, h.gcd_eq_one, hc, ha]

private theorem factor_gcd {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    ∃ g a d : ℕ, 0 < g ∧ 0 < a ∧ 0 < d ∧ a.Coprime d ∧ x = g * a ∧ y = g * d := by
  let g := x.gcd y
  have hg : 0 < g := Nat.gcd_pos_of_pos_left y hx
  have h₁ : g ∣ x := Nat.gcd_dvd_left x y
  have h₂ : g ∣ y := Nat.gcd_dvd_right x y
  have ex : g * (x / g) = x := Nat.mul_div_cancel' h₁
  have ey : g * (y / g) = y := Nat.mul_div_cancel' h₂
  refine ⟨g, x / g, y / g, hg, ?_, ?_, Nat.coprime_div_gcd_div_gcd hg, ex.symm, ey.symm⟩
  · exact Nat.pos_of_mul_pos_left (ex ▸ hx)
  · exact Nat.pos_of_mul_pos_left (ey ▸ hy)

private theorem left_key_mem {g a b c d : ℕ}
    (hg : 0 < g) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    leftKey g a b c d ∈ leftSet (g * (a * b + c * d)) := by
  have h₁ : 0 < g * (a * b) := by positivity
  have h₂ : 0 < g * (c * d) := by positivity
  simp only [leftKey, leftSet, mem_sigma, mem_Icc, mem_product, Nat.mem_divisorsAntidiagonal,
    Nat.mul_add, Nat.add_sub_cancel_left]
  exact ⟨⟨h₁, by omega⟩, ⟨by ring, h₁.ne'⟩, by ring, h₂.ne'⟩

private theorem right_key_mem {g a b c d : ℕ}
    (hg : 0 < g) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    rightKey g a b c d ∈ rightSet (g * (a * b + c * d)) := by
  simp only [rightKey, rightSet, mem_sigma, Nat.mem_divisorsAntidiagonal, mem_Icc,
    Nat.add_sub_cancel_left]
  exact ⟨⟨trivial, by positivity⟩, ⟨Nat.mul_pos ha hb, by omega⟩, by ring, by positivity⟩

private theorem left_decompose {n : ℕ} {l : LeftKey} (hl : l ∈ leftSet n) :
    ∃ g a b c d : ℕ, 0 < g ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a.Coprime d ∧
      n = g * (a * b + c * d) ∧ l = leftKey g a b c d := by
  rcases l with ⟨k, ⟨x, b⟩, ⟨c, y⟩⟩
  simp only [leftSet, mem_sigma, mem_Icc, mem_product, Nat.mem_divisorsAntidiagonal] at hl
  obtain ⟨⟨_, hkn⟩, ⟨hx, hk⟩, hy, hnk⟩ := hl
  have hp : 0 < x * b := by omega
  have hq : 0 < c * y := by omega
  obtain ⟨g, a, d, hg, ha, hd, cop, rfl, rfl⟩ :=
    factor_gcd (Nat.pos_of_mul_pos_right hp) (Nat.pos_of_mul_pos_left hq)
  refine ⟨g, a, b, c, d, hg, ha, Nat.pos_of_mul_pos_left hp, Nat.pos_of_mul_pos_right hq,
    hd, cop, ?_, ?_⟩
  · calc
      n = (g * a) * b + c * (g * d) := by omega
      _ = _ := by ring
  · simp [leftKey, ← hx, Nat.mul_assoc]

private theorem right_decompose {n : ℕ} {r : RightKey} (hr : r ∈ rightSet n) :
    ∃ g a b c d : ℕ, 0 < g ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a.Coprime d ∧
      n = g * (a * b + c * d) ∧ r = rightKey g a b c d := by
  rcases r with ⟨⟨g, t⟩, u, s, z⟩
  simp only [rightSet, mem_sigma, Nat.mem_divisorsAntidiagonal, mem_Icc] at hr
  obtain ⟨⟨hn, hn₀⟩, ⟨hu, hut⟩, hsz, hnz⟩ := hr
  let v := t - u
  have huv : t = u + v := by dsimp [v]; omega
  change s * z = u * v at hsz
  change u * v ≠ 0 at hnz
  have hs : 0 < s * z := by omega
  have hv : 0 < u * v := by omega
  obtain ⟨c, a, d, hc, ha, hd, cop, hsc, hvc⟩ :=
    factor_gcd (Nat.pos_of_mul_pos_right hs) (Nat.pos_of_mul_pos_left hv)
  have hz : a * z = u * d := by
    apply Nat.eq_of_mul_eq_mul_left hc
    calc
      c * (a * z) = s * z := by rw [hsc]; ring
      _ = u * v := hsz
      _ = c * (u * d) := by rw [hvc]; ring
  obtain ⟨b, hub⟩ := cop.dvd_mul_right.mp (show a ∣ u * d by rw [← hz]; exact dvd_mul_right ..)
  have hzd : z = b * d := by
    apply Nat.eq_of_mul_eq_mul_left ha
    simpa [hub, Nat.mul_assoc] using hz
  have hg : 0 < g := Nat.pos_of_mul_pos_right (show 0 < g * t by omega)
  have ht : t = a * b + c * d := by rw [huv, hub, hvc]
  exact ⟨g, a, b, c, d, hg, ha, Nat.pos_of_mul_pos_left (show 0 < a * b by omega),
    hc, hd, cop, by rw [← ht, hn], by simp [rightKey, ht, hub, hsc, hzd, Nat.mul_comm a c]⟩

private theorem counts (n : ℕ) : (leftSet n).card = (rightSet n).card := by
  apply Finset.card_bij' (fun l _ => forward l) (fun r _ => backward r)
  · intro l hl
    obtain ⟨g,a,b,c,d,hg,ha,hb,hc,hd,cop,rfl,rfl⟩ := left_decompose hl
    rw [forward_key hg cop]
    exact right_key_mem hg ha hb hc hd
  · intro r hr
    obtain ⟨g,a,b,c,d,hg,ha,hb,hc,hd,cop,rfl,rfl⟩ := right_decompose hr
    rw [backward_key ha hc cop]
    exact left_key_mem hg ha hb hc hd
  · intro l hl
    obtain ⟨g,a,b,c,d,hg,ha,hb,hc,hd,cop,rfl,rfl⟩ := left_decompose hl
    rw [forward_key hg cop, backward_key ha hc cop]
  · intro r hr
    obtain ⟨g,a,b,c,d,hg,ha,hb,hc,hd,cop,rfl,rfl⟩ := right_decompose hr
    rw [backward_key ha hc cop, forward_key hg cop]

private theorem card_pairs (m : ℕ) : m.divisorsAntidiagonal.card = tau m := by
  rw [← Nat.map_div_right_divisors, Finset.card_map, tau]

end OEISA072031

open Finset OMA.S_oeis_a072031 OEISA072031 in
theorem OMA.solution : type_of% @OMA.S_oeis_a072031.main := by
  intro n _
  have h := counts n
  simp only [leftSet, rightSet, card_sigma, card_product, card_pairs] at h
  exact h.trans (Nat.sum_divisorsAntidiagonal' (n := n)
    (fun _ d => ∑ k ∈ Icc 1 d, tau (k * (d - k))))
