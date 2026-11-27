import OMAStatements.S_oeis_a006531

/-!
For every modulus m and n ≥ m, the functions x ↦ x^n and x ↦ x^(n+φ(m))
agree modulo m. At a prime power dividing m the base is either a unit, when
Euler's theorem applies, or its nth power is already zero.

The kth forward difference of x^n at zero is k! S(n,k). Taking differences
preserves the modular identity, as does multiplication by the Catalan number
and the sign in Bala's formula. Terms with k ≥ m vanish modulo m. Thus n=m
is an explicit starting index for the common period φ(m).

This specializes the Omega Institute's earlier theorem on factorial-weighted
Stirling transforms. Here the weights are the signed Catalan numbers together
with the outer factor (-1)^n. The proof below checks the OEIS statement directly.
https://the-omega-institute.github.io/trureturing-mdbook/Blueprint/D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.html
-/

namespace SemiorderPeriods

open Finset OMA.S_oeis_a006531

private theorem power_nat (q : ℕ) : ∀ k, q ∣ k → 0 < k → ∀ n, k ≤ n → ∀ x : ℕ,
    x^(n+k.totient) ≡ x^n [MOD q] := by
  induction q using Nat.recOnPrimeCoprime with
  | zero =>
    intro k h hk
    simp_all
  | prime_pow p e hp =>
    intro k hd hk n hn x
    by_cases hx : p ∣ x
    · have he : e ≤ n := calc
        e ≤ 2^e := (Nat.lt_two_pow_self).le
        _ ≤ p^e := Nat.pow_le_pow_left hp.two_le _
        _ ≤ k := Nat.le_of_dvd hk hd
        _ ≤ n := hn
      have hz (j : ℕ) (hj : e ≤ j) : x^j ≡ 0 [MOD p^e] :=
        Nat.modEq_zero_iff_dvd.mpr ((pow_dvd_pow_of_dvd hx e).trans (pow_dvd_pow x hj))
      exact (hz _ (by omega)).trans (hz _ he).symm
    · have hc : x.Coprime (p^e) := (hp.coprime_iff_not_dvd.mpr hx).symm.pow_right _
      obtain ⟨c,he⟩ := Nat.totient_dvd_of_dvd hd
      have h := (Nat.ModEq.pow_totient hc).pow c
      rw [one_pow,←pow_mul,←he] at h
      simpa [pow_add] using h.mul_left (x^n)
  | coprime a b _ _ h ia ib =>
    intro k hd hk n hn x
    apply (Nat.modEq_and_modEq_iff_modEq_mul h).mp
    exact ⟨ia k ((dvd_mul_right a b).trans hd) hk n hn x,
      ib k ((dvd_mul_left b a).trans hd) hk n hn x⟩

private theorem power_period (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) (x : ZMod m) :
    x^(n+m.totient) = x^n := by
  let _ : NeZero m := ⟨hm.ne'⟩
  have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (power_nat m m dvd_rfl hm n hn x.val)
  simpa using h

private def diff {R : Type} [Sub R] (f : ℕ → R) : ℕ → ℕ → R
  | 0,x => f x
  | k+1,x => diff f k (x+1) - diff f k x

private theorem diff_one {R : Type} [Ring R] (k x : ℕ) :
    diff (fun _ => (1 : R)) (k+1) x = 0 := by
  induction k generalizing x with
  | zero => simp [diff]
  | succ k ih => rw [diff,ih,ih,sub_self]

private theorem diff_times_x {R : Type} [CommRing R] (f : ℕ → R) (k x : ℕ) :
    diff (fun y => (y : R) * f y) (k+1) x =
    (x+k+1 : R) * diff f (k+1) x + (k+1 : R) * diff f k x := by
  induction k generalizing x with
  | zero => simp [diff]; ring
  | succ k ih =>
    rw [diff,ih,ih]
    rw [show diff f (k+1+1) x = diff f (k+1) (x+1) - diff f (k+1) x from rfl]
    rw [show diff f (k+1) x = diff f k (x+1) - diff f k x from rfl]
    push_cast
    ring

private theorem diff_powers (m n k : ℕ) :
    diff (fun x : ℕ => (x : ZMod m)^n) k 0 =
      (k.factorial : ZMod m) * stirling2 n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [diff,stirling2]
    | succ k => simp [diff_one,stirling2]
  | succ n ih =>
    cases k with
    | zero => simp [diff,stirling2]
    | succ k =>
      have h : (fun x : ℕ => (x : ZMod m)^(n+1)) = fun x : ℕ => (x : ZMod m)*(x : ZMod m)^n := by
        funext x; rw [pow_succ,mul_comm]
      rw [h,diff_times_x,ih,ih,stirling2,Nat.factorial_succ]
      push_cast
      ring

private noncomputable def term (m n k : ℕ) : ZMod m :=
  (-1)^(n+k) * (catalan k : ZMod m) * ((k.factorial : ZMod m) * stirling2 n k)

private theorem cast_a (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (a n : ZMod m) = ∑ k ∈ range m, term m n k := by
  have c : (a n : ZMod m) = ∑ k ∈ range (n+1), term m n k := by
    unfold a term
    push_cast
    apply sum_congr rfl
    intro k _
    ring
  rw [c]
  symm
  apply sum_subset (range_mono (by omega))
  intro k _ hk
  have hd : m ∣ k.factorial := Nat.dvd_factorial hm (by simpa using hk)
  have hz : (k.factorial : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  simp [term,hz]

private theorem term_period (m n k : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    term m (n+m.totient) k = term m n k := by
  have f : (fun x : ℕ => (x : ZMod m)^(n+m.totient)) = fun x : ℕ => (x : ZMod m)^n :=
    funext (fun x => power_period m n hm hn x)
  unfold term
  rw [← diff_powers,← diff_powers,f,show n+m.totient+k = n+k+m.totient by omega,
    power_period m (n+k) hm (by omega)]

end SemiorderPeriods

open SemiorderPeriods OMA.S_oeis_a006531

theorem OMA.solution : type_of% @OMA.S_oeis_a006531.main := by
  intro m hm
  refine ⟨m.totient,m,Nat.totient_pos.mpr hm,dvd_rfl,?_⟩
  intro n hn
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  rw [cast_a m (n+m.totient) hm (by omega),cast_a m n hm hn]
  exact Finset.sum_congr rfl (fun k _ => term_period m n k hm hn)
