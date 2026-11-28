import OMAReductions.R_erdos_132_R1_H1_R1
import Mathlib

/-!
# The five-point case of the Erdős–Pach problem

A planar set of at least five points with at most two positive distances has
exactly five points, and both distances are rare. Consequently every five-point
planar set has at least two distances of unordered multiplicity at most five.

Erdős and Fishburn record the stronger classification of extremal two-distance
sets as regular pentagons in *Maximum planar sets that determine k distances*,
Discrete Mathematics 160 (1996), 115–125, doi:10.1016/0012-365X(95)00153-N.

This proof uses rank two of the planar Gram matrix. A point with three neighbors
at distance r leaves seven unspecified pairs among five points. For each of the
128 assignments of the two possible distances, a displayed polynomial identity
contradicts the positivity of the squared distance ratio. Lean checks every
identity by ring normalization. Counting degrees finishes the proof.

Lean formalization by Koa Okano (@KoaOkano) with OpenAI Codex.
-/

open Finset
open scoped Classical
namespace PrizeFormalizations.Erdos132.TwoDistances

abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def d3 (a b c d e f g h i : ℝ) : ℝ :=
  a*e*i + b*f*g + c*d*h - a*f*h - b*d*i - c*e*g

private noncomputable def entry (o : Plane) (s : ℝ) (p q : Plane) : ℝ :=
  dist o p ^ 2 / s + dist o q ^ 2 / s - dist p q ^ 2 / s

private lemma entry_eq (o : Plane) (s : ℝ) (p q : Plane) :
    entry o s p q = (2/s)*((p 0-o 0)*(q 0-o 0)+(p 1-o 1)*(q 1-o 1)) := by
  simp only [entry, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  ring

private lemma dotDet (s a b c d e f u v w z h k : ℝ) :
    d3 (s*(a*u+b*v)) (s*(a*w+b*z)) (s*(a*h+b*k))
       (s*(c*u+d*v)) (s*(c*w+d*z)) (s*(c*h+d*k))
       (s*(e*u+f*v)) (s*(e*w+f*z)) (s*(e*h+f*k)) = 0 := by
  unfold d3
  ring

private lemma geoMinor (o : Plane) (s : ℝ) (a b c i j k : Plane) :
    d3 (entry o s a i) (entry o s a j) (entry o s a k)
       (entry o s b i) (entry o s b j) (entry o s b k)
       (entry o s c i) (entry o s c j) (entry o s c k) = 0 := by
  simp only [entry_eq]
  apply dotDet

/-! The ten distinct 3-by-3 minors of the symmetric Gram matrix of four planar vectors. -/
private def rankTwo (v01 v02 v03 v04 v12 v13 v14 v23 v24 v34 : ℝ) : Prop :=
  d3 (v01+v01) (v01+v02-v12) (v01+v03-v13) (v02+v01-v12) (v02+v02) (v02+v03-v23) (v03+v01-v13) (v03+v02-v23) (v03+v03) = 0 ∧
  d3 (v01+v01) (v01+v02-v12) (v01+v04-v14) (v02+v01-v12) (v02+v02) (v02+v04-v24) (v03+v01-v13) (v03+v02-v23) (v03+v04-v34) = 0 ∧
  d3 (v01+v01) (v01+v03-v13) (v01+v04-v14) (v02+v01-v12) (v02+v03-v23) (v02+v04-v24) (v03+v01-v13) (v03+v03) (v03+v04-v34) = 0 ∧
  d3 (v01+v02-v12) (v01+v03-v13) (v01+v04-v14) (v02+v02) (v02+v03-v23) (v02+v04-v24) (v03+v02-v23) (v03+v03) (v03+v04-v34) = 0 ∧
  d3 (v01+v01) (v01+v02-v12) (v01+v04-v14) (v02+v01-v12) (v02+v02) (v02+v04-v24) (v04+v01-v14) (v04+v02-v24) (v04+v04) = 0 ∧
  d3 (v01+v01) (v01+v03-v13) (v01+v04-v14) (v02+v01-v12) (v02+v03-v23) (v02+v04-v24) (v04+v01-v14) (v04+v03-v34) (v04+v04) = 0 ∧
  d3 (v01+v02-v12) (v01+v03-v13) (v01+v04-v14) (v02+v02) (v02+v03-v23) (v02+v04-v24) (v04+v02-v24) (v04+v03-v34) (v04+v04) = 0 ∧
  d3 (v01+v01) (v01+v03-v13) (v01+v04-v14) (v03+v01-v13) (v03+v03) (v03+v04-v34) (v04+v01-v14) (v04+v03-v34) (v04+v04) = 0 ∧
  d3 (v01+v02-v12) (v01+v03-v13) (v01+v04-v14) (v03+v02-v23) (v03+v03) (v03+v04-v34) (v04+v02-v24) (v04+v03-v34) (v04+v04) = 0 ∧
  d3 (v02+v02) (v02+v03-v23) (v02+v04-v24) (v03+v02-v23) (v03+v03) (v03+v04-v34) (v04+v02-v24) (v04+v03-v34) (v04+v04) = 0

private lemma planarRank (p0 p1 p2 p3 p4 : Plane) (s : ℝ) :
    rankTwo (dist p0 p1 ^ 2 / s) (dist p0 p2 ^ 2 / s) (dist p0 p3 ^ 2 / s) (dist p0 p4 ^ 2 / s) (dist p1 p2 ^ 2 / s) (dist p1 p3 ^ 2 / s) (dist p1 p4 ^ 2 / s) (dist p2 p3 ^ 2 / s) (dist p2 p4 ^ 2 / s) (dist p3 p4 ^ 2 / s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [entry, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, dist_comm p2 p1, dist_comm p3 p1, dist_comm p3 p2] using
      geoMinor p0 s p1 p2 p3 p1 p2 p3
  · simpa only [entry, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, dist_comm p2 p1, dist_comm p3 p1, dist_comm p3 p2] using
      geoMinor p0 s p1 p2 p3 p1 p2 p4
  · simpa only [entry, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, dist_comm p2 p1, dist_comm p3 p1] using
      geoMinor p0 s p1 p2 p3 p1 p3 p4
  · simpa only [entry, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, dist_comm p3 p2] using
      geoMinor p0 s p1 p2 p3 p2 p3 p4
  · simpa only [entry, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, dist_comm p2 p1, dist_comm p4 p1, dist_comm p4 p2] using
      geoMinor p0 s p1 p2 p4 p1 p2 p4
  · simpa only [entry, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, dist_comm p2 p1, dist_comm p4 p1, dist_comm p4 p3] using
      geoMinor p0 s p1 p2 p4 p1 p3 p4
  · simpa only [entry, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, dist_comm p4 p2, dist_comm p4 p3] using
      geoMinor p0 s p1 p2 p4 p2 p3 p4
  · simpa only [entry, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, dist_comm p3 p1, dist_comm p4 p1, dist_comm p4 p3] using
      geoMinor p0 s p1 p3 p4 p1 p3 p4
  · simpa only [entry, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, dist_comm p3 p2, dist_comm p4 p2, dist_comm p4 p3] using
      geoMinor p0 s p1 p3 p4 p2 p3 p4
  · simpa only [entry, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, dist_comm p3 p2, dist_comm p4 p2, dist_comm p4 p3] using
      geoMinor p0 s p2 p3 p4 p2 p3 p4

/-! Exact polynomial certificates for the remaining seven pair lengths. Each branch combines
vanishing Gram minors to obtain a positive multiple of 1, x, or x² equal to zero. -/
set_option maxHeartbeats 0 in
private lemma impossibleStar (x : ℝ) (hx : 0 < x) (v04 v12 v13 v14 v23 v24 v34 : ℝ)
    (hv04 : v04 = 1 ∨ v04 = x)
    (hv12 : v12 = 1 ∨ v12 = x)
    (hv13 : v13 = 1 ∨ v13 = x)
    (hv14 : v14 = 1 ∨ v14 = x)
    (hv23 : v23 = 1 ∨ v23 = x)
    (hv24 : v24 = 1 ∨ v24 = x)
    (hv34 : v34 = 1 ∨ v34 = x)
    (rank : rankTwo 1 1 1 v04 v12 v13 v14 v23 v24 v34) : False := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := rank
  simp only [d3] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  rcases hv04 with h | h <;> subst v04 <;>
    rcases hv12 with h | h <;> subst v12 <;>
    rcases hv13 with h | h <;> subst v13 <;>
    rcases hv14 with h | h <;> subst v14 <;>
    rcases hv23 with h | h <;> subst v23 <;>
    rcases hv24 with h | h <;> subst v24 <;>
    rcases hv34 with h | h <;> subst v34
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h9
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h7
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h0
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h7
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h7
    exact (ne_of_gt (by positivity)) z
  · have z : (3*x : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((-1)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h9
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h0
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h0
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h0
    exact (ne_of_gt (by positivity)) z
  · have z : (6*x : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (18 : ℝ) = 0 := by linear_combination ((7)*1+(-2)*x) * h0 + ((-6)*1+(4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((4)*1+(-1)*x) * h0 + ((-8)*1+(2)*x) * h1 + ((-1)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h9
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (6*x : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((3)*1+(-1)*x) * h0 + ((-4)*1+(2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((-3)*1+(2)*x) * h0 + ((14)*1+(-4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h9
    exact (ne_of_gt (by positivity)) z
  · have z : (3*x : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((-1)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (18 : ℝ) = 0 := by linear_combination ((7)*1+(-2)*x) * h0 + ((-6)*1+(4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((4)*1+(-1)*x) * h0 + ((-8)*1+(2)*x) * h1 + ((-1)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((3)*1+(-1)*x) * h0 + ((-4)*1+(2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((-3)*1+(2)*x) * h0 + ((14)*1+(-4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (3 : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((-1)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((5)*1+(-2)*x) * h0 + ((-8)*1+(2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h9
    exact (ne_of_gt (by positivity)) z
  · have z : (6*x : ℝ) = 0 := by linear_combination ((3)*1+(-1)*x) * h0 + ((-2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h7
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((6)*1+(-5)*x+(1)*x^2) * h0 + ((-6)*1+(2)*x) * h1 + ((-2)*1) * h2
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h7
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((-1)*1+(1)*x) * h0 + ((2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h7
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((7)*1+(-6)*x+(1)*x^2) * h0 + ((-8)*1+(2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h9
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((10)*1+(-7)*x+(1)*x^2) * h0 + ((-10)*1+(2)*x) * h1 + ((2)*1) * h2
    exact (ne_of_gt (by positivity)) z
  · have z : (6*x : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((-4)*1+(5)*x+(-1)*x^2) * h0 + ((8)*1+(-2)*x) * h1 + ((-1)*1) * h7
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((1)*1+(-1)*x) * h0 + ((2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((4)*1+(-2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((-1)*1+(4)*x+(-1)*x^2) * h0 + ((-8)*1+(2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((-3)*1+(2)*x) * h0 + ((14)*1+(-4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h9
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((-1)*1+(1)*x) * h0 + ((2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((1)*1+(-1)*x) * h0 + ((2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((4)*1+(-2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6*x : ℝ) = 0 := by linear_combination ((2)*1) * h3 + ((1)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (8 : ℝ) = 0 := by linear_combination ((4)*x+(-1)*x^2) * h0 + ((8)*1+(6)*x+(-2)*x^2) * h1 + ((-4)*1) * h7
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((8)*1+(-6)*x+(1)*x^2) * h0 + ((-8)*1+(10)*x+(-2)*x^2) * h1 + ((-2)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((4)*1+(-1)*x) * h0 + ((8)*1+(-10)*x+(2)*x^2) * h1 + ((-2)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h9
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((7)*1+(-6)*x+(1)*x^2) * h0 + ((-8)*1+(2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((-1)*1+(4)*x+(-1)*x^2) * h0 + ((-8)*1+(2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((-3)*1+(2)*x) * h0 + ((14)*1+(-4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((8)*1+(-6)*x+(1)*x^2) * h0 + ((-8)*1+(10)*x+(-2)*x^2) * h1 + ((-2)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((4)*1+(-1)*x) * h0 + ((8)*1+(-10)*x+(2)*x^2) * h1 + ((-2)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (8 : ℝ) = 0 := by linear_combination ((4)*1+(7)*x+(-2)*x^2) * h0 + ((-8)*1+(-6)*x+(2)*x^2) * h1 + ((-4)*1) * h7
    exact (ne_of_gt (by positivity)) z
  · have z : (2*x^2 : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((-2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h0
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h0
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h0
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h0
    exact (ne_of_gt (by positivity)) z
  · have z : (6*x : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (18 : ℝ) = 0 := by linear_combination ((7)*1+(-2)*x) * h0 + ((-6)*1+(4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((4)*1+(-1)*x) * h0 + ((-8)*1+(2)*x) * h1 + ((-1)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h0
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h0
    exact (ne_of_gt (by positivity)) z
  · have z : (4 : ℝ) = 0 := by linear_combination ((1)*1) * h0
    exact (ne_of_gt (by positivity)) z
  · have z : (1 : ℝ) = 0 := by linear_combination ((1)*1) * h3
    exact (ne_of_gt (by positivity)) z
  · have z : (10 : ℝ) = 0 := by linear_combination ((8)*1+(-2)*x) * h0 + ((8)*1+(-2)*x) * h1 + ((-5)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (27 : ℝ) = 0 := by linear_combination ((7)*1+(-2)*x) * h0 + ((9)*1+(-2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (27 : ℝ) = 0 := by linear_combination ((8)*1) * h0 + ((-9)*1+(4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((-6)*1) * h2 + ((-1)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (6*x : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (10 : ℝ) = 0 := by linear_combination ((8)*1+(-2)*x) * h0 + ((8)*1+(-2)*x) * h1 + ((-5)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (27 : ℝ) = 0 := by linear_combination ((7)*1+(-2)*x) * h0 + ((9)*1+(-2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((-3)*1+(14)*x) * h0 + ((-52)*1+(14)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (33 : ℝ) = 0 := by linear_combination ((9)*1+(-4)*x) * h0 + ((17)*1+(-4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (18 : ℝ) = 0 := by linear_combination ((5)*1+(2)*x) * h0 + ((-14)*1+(4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((1)*1+(-1)*x) * h0 + ((8)*1+(-2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (18 : ℝ) = 0 := by linear_combination ((7)*1+(-2)*x) * h0 + ((-6)*1+(4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((4)*1+(-1)*x) * h0 + ((-8)*1+(2)*x) * h1 + ((-1)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (27 : ℝ) = 0 := by linear_combination ((8)*1) * h0 + ((-9)*1+(4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((6)*1) * h3 + ((-1)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (18 : ℝ) = 0 := by linear_combination ((5)*1+(2)*x) * h0 + ((-14)*1+(4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((1)*1+(-1)*x) * h0 + ((8)*1+(-2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (78 : ℝ) = 0 := by linear_combination ((25)*1) * h0 + ((-32)*1+(10)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (3 : ℝ) = 0 := by linear_combination ((2)*1) * h0 + ((-7)*1+(2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6*x : ℝ) = 0 := by linear_combination ((1)*1+(1)*x) * h0 + ((-2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (10 : ℝ) = 0 := by linear_combination ((12)*1+(-3)*x) * h0 + ((-8)*1+(2)*x) * h1 + ((-5)*1) * h7
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((3)*x+(-1)*x^2) * h0 + ((-6)*1+(2)*x) * h1 + ((-2)*1) * h2
    exact (ne_of_gt (by positivity)) z
  · have z : (9 : ℝ) = 0 := by linear_combination ((4)*1+(-2)*x) * h0 + ((-4)*1+(2)*x) * h1 + ((-3)*1) * h2
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((-1)*1+(-4)*x) * h0 + ((30)*1+(-8)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((-3)*1+(4)*x+(-1)*x^2) * h0 + ((8)*1+(-2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (22 : ℝ) = 0 := by linear_combination ((9)*1) * h0 + ((-20)*1+(6)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((11)*1+(-9)*x+(2)*x^2) * h0 + ((-14)*1+(4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((5)*x+(-1)*x^2) * h0 + ((-10)*1+(2)*x) * h1 + ((2)*1) * h2
    exact (ne_of_gt (by positivity)) z
  · have z : (9 : ℝ) = 0 := by linear_combination ((4)*1) * h0 + ((-4)*1) * h1 + ((3)*1) * h2
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((4)*1+(-5)*x+(1)*x^2) * h0 + ((8)*1+(-2)*x) * h1 + ((-1)*1) * h7
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((6)*1) * h3 + ((-1)*1) * h7
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((5)*1+(-6)*x+(1)*x^2) * h0 + ((8)*1+(-2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (26 : ℝ) = 0 := by linear_combination ((5)*1+(-2)*x) * h0 + ((18)*1+(-4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((-3)*1+(9)*x+(-2)*x^2) * h0 + ((-14)*1+(4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((-1)*1) * h0 + ((8)*1+(-2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((-1)*1+(-4)*x) * h0 + ((30)*1+(-8)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((-3)*1+(4)*x+(-1)*x^2) * h0 + ((8)*1+(-2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((5)*1+(-6)*x+(1)*x^2) * h0 + ((8)*1+(-2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (26 : ℝ) = 0 := by linear_combination ((5)*1+(-2)*x) * h0 + ((18)*1+(-4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6*x^2 : ℝ) = 0 := by linear_combination ((1)*1) * h0 + ((2)*1) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (56 : ℝ) = 0 := by linear_combination ((26)*1+(22)*x+(-17)*x^2+(2)*x^3) * h0 + ((28)*1+(24)*x+(-18)*x^2+(2)*x^3) * h1 + ((-28)*1) * h7
    exact (ne_of_gt (by positivity)) z
  · have z : (28 : ℝ) = 0 := by linear_combination ((18)*1+(18)*x+(-9)*x^2) * h0 + ((-28)*1+(-16)*x+(26)*x^2+(-6)*x^3) * h1 + ((-14)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (20 : ℝ) = 0 := by linear_combination ((8)*1+(6)*x+(-6)*x^2+(1)*x^3) * h0 + ((20)*1+(16)*x+(-14)*x^2+(2)*x^3) * h1 + ((-10)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (22 : ℝ) = 0 := by linear_combination ((9)*1) * h0 + ((-20)*1+(6)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((11)*1+(-9)*x+(2)*x^2) * h0 + ((-14)*1+(4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (6 : ℝ) = 0 := by linear_combination ((-3)*1+(9)*x+(-2)*x^2) * h0 + ((-14)*1+(4)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (2 : ℝ) = 0 := by linear_combination ((-1)*1) * h0 + ((8)*1+(-2)*x) * h1
    exact (ne_of_gt (by positivity)) z
  · have z : (28 : ℝ) = 0 := by linear_combination ((18)*1+(18)*x+(-9)*x^2) * h0 + ((-28)*1+(-16)*x+(26)*x^2+(-6)*x^3) * h1 + ((-14)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (20 : ℝ) = 0 := by linear_combination ((8)*1+(6)*x+(-6)*x^2+(1)*x^3) * h0 + ((20)*1+(16)*x+(-14)*x^2+(2)*x^3) * h1 + ((-10)*1) * h4
    exact (ne_of_gt (by positivity)) z
  · have z : (40 : ℝ) = 0 := by linear_combination ((28)*1+(22)*x+(-20)*x^2+(3)*x^3) * h0 + ((-20)*1+(-8)*x+(22)*x^2+(-6)*x^3) * h1 + ((-20)*1) * h7
    exact (ne_of_gt (by positivity)) z
  · have z : (2*x : ℝ) = 0 := by linear_combination ((8)*1+(-2)*x) * h3 + ((-1)*1) * h4
    exact (ne_of_gt (by positivity)) z

private lemma noFiveStar (p0 p1 p2 p3 p4 : Plane) (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (h01 : dist p0 p1 = r) (h02 : dist p0 p2 = r) (h03 : dist p0 p3 = r)
    (hv04 : dist p0 p4 = r ∨ dist p0 p4 = t)
    (hv12 : dist p1 p2 = r ∨ dist p1 p2 = t)
    (hv13 : dist p1 p3 = r ∨ dist p1 p3 = t)
    (hv14 : dist p1 p4 = r ∨ dist p1 p4 = t)
    (hv23 : dist p2 p3 = r ∨ dist p2 p3 = t)
    (hv24 : dist p2 p4 = r ∨ dist p2 p4 = t)
    (hv34 : dist p3 p4 = r ∨ dist p3 p4 = t)
    : False := by
  let x := t^2/r^2
  have pos : 0 < x := div_pos (sq_pos_of_pos ht) (sq_pos_of_pos hr)
  have ne : r^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hr)
  have normalize {p q : Plane} (h : dist p q = r ∨ dist p q = t) :
      dist p q ^ 2 / r^2 = 1 ∨ dist p q ^ 2 / r^2 = x := by
    rcases h with eq | eq
    · exact Or.inl (by rw [eq,div_self ne])
    · exact Or.inr (by rw [eq])
  have rank := planarRank p0 p1 p2 p3 p4 (r^2)
  rw [h01,h02,h03,div_self ne] at rank
  exact impossibleStar x pos _ _ _ _ _ _ _
    (normalize hv04) (normalize hv12) (normalize hv13) (normalize hv14) (normalize hv23) (normalize hv24) (normalize hv34) rank


/-- No point has three neighbors at the same distance in a two-distance set with at least five points. -/
theorem degreeTwo (A : Finset Plane) (five : 5 ≤ A.card) (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (two : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → dist a b = r ∨ dist a b = t)
    (o : Plane) (ho : o ∈ A) : (A.filter (fun y => dist o y = r)).card ≤ 2 := by
  classical
  by_contra! many
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := two_lt_card_iff.mp many
  obtain ⟨aA,ar⟩ := mem_filter.mp ha
  obtain ⟨bA,br⟩ := mem_filter.mp hb
  obtain ⟨cA,cr⟩ := mem_filter.mp hc
  let used : Finset Plane := {o,a,b,c}
  have small : used.card ≤ 4 := by
    calc
      used.card ≤ ({a,b,c} : Finset Plane).card + 1 := card_insert_le _ _
      _ ≤ (({b,c} : Finset Plane).card + 1) + 1 :=
        Nat.add_le_add_right (card_insert_le _ _) _
      _ ≤ 4 := by have h := Finset.card_le_two (a := b) (b := c); omega
  obtain ⟨v,hv,free⟩ := exists_mem_notMem_of_card_lt_card (small.trans_lt (by omega : 4 < A.card))
  have diff : v ≠ o ∧ v ≠ a ∧ v ≠ b ∧ v ≠ c := by simpa [used] using free
  exact noFiveStar o a b c v r t hr ht ar br cr
    (two o ho v hv diff.1.symm) (two a aA b bA ab) (two a aA c cA ac)
    (two a aA v hv diff.2.1.symm) (two b bA c cA bc)
    (two b bA v hv diff.2.2.1.symm) (two c cA v hv diff.2.2.2.symm)

open OMA.S_erdos_132 (pairMultiplicity rareDistances)

private lemma lengthPos {A : Finset Plane} {r : ℝ}
    (hit : r ∈ A.offDiag.image (fun p => dist p.1 p.2)) : 0 < r := by
  obtain ⟨⟨a,b⟩,h,rfl⟩ := mem_image.mp hit
  exact dist_pos.mpr (mem_offDiag.mp h).2.2

private lemma multiplicity_of_degree (A : Finset Plane) (r : ℝ)
    (deg : ∀ a ∈ A, (A.filter (fun b => dist a b = r)).card ≤ 2) :
    pairMultiplicity A r ≤ A.card := by
  classical
  let G := (A ×ˢ A).filter (fun p => dist p.1 p.2 = r)
  have incl : A.offDiag.filter (fun p => dist p.1 p.2 = r) ⊆ G := by
    intro p hp
    obtain ⟨edge,eq⟩ := mem_filter.mp hp
    obtain ⟨a,b,_⟩ := mem_offDiag.mp edge
    exact mem_filter.mpr ⟨mem_product.mpr ⟨a,b⟩,eq⟩
  have bound : G.card ≤ 2*A.card := by
    calc
      G.card = ∑ a ∈ A, (A.filter (fun b => dist a b = r)).card := by
        simp only [G,card_filter,sum_product]
      _ ≤ ∑ _a ∈ A, 2 := sum_le_sum deg
      _ = _ := by simp [mul_comm]
  have ord := (card_le_card incl).trans bound
  change (A.offDiag.filter (fun p => dist p.1 p.2 = r)).card / 2 ≤ A.card
  omega

/-- A planar set of at least five points realizing at most two positive distances
has exactly five points, and each realized distance is rare. -/
theorem twoDistanceSet (A : Finset Plane) (five : 5 ≤ A.card)
    (few : (A.offDiag.image (fun p => dist p.1 p.2)).card ≤ 2) :
    A.card = 5 ∧ (rareDistances A).card = 2 := by
  classical
  let D := A.offDiag.image (fun p => dist p.1 p.2)
  obtain ⟨o,ho,p,hp,ne⟩ := one_lt_card.mp (by omega : 1 < A.card)
  have posD : dist o p ∈ D := mem_image.mpr ⟨(o,p),mem_offDiag.mpr ⟨ho,hp,ne⟩,rfl⟩
  have twoRadii : ∃ r ∈ D, ∃ t ∈ D, D ⊆ {r,t} := by
    rcases (show D.Nonempty from ⟨_,posD⟩).exists_eq_singleton_or_nontrivial with ⟨r,eq⟩ | wider
    · exact ⟨r,by simp [eq],r,by simp [eq],by simp [eq]⟩
    · have size : D.card = 2 := Nat.le_antisymm few (one_lt_card_iff_nontrivial.mpr wider)
      obtain ⟨r,t,_,eq⟩ := card_eq_two.mp size
      exact ⟨r,by simp [eq],t,by simp [eq],by simp [eq]⟩
  obtain ⟨r,hr,t,ht,cover⟩ := twoRadii
  have two (a : Plane) (ha : a ∈ A) (b : Plane) (hb : b ∈ A) (ab : a ≠ b) :
      dist a b = r ∨ dist a b = t := by
    have h := cover (mem_image.mpr ⟨(a,b),mem_offDiag.mpr ⟨ha,hb,ab⟩,rfl⟩)
    simpa only [mem_insert,mem_singleton] using h
  have degR := degreeTwo A five r t (lengthPos hr) (lengthPos ht) two
  have degT := degreeTwo A five t r (lengthPos ht) (lengthPos hr)
    (fun a ha b hb ab => (two a ha b hb ab).symm)
  let R := A.filter (fun b => dist o b = r)
  let T := A.filter (fun b => dist o b = t)
  have others : A.erase o ⊆ R ∪ T := by
    intro b hb
    obtain ⟨bo,inside⟩ := mem_erase.mp hb
    apply mem_union.mpr
    exact (two o ho b inside bo.symm).imp (fun h => mem_filter.mpr ⟨inside,h⟩)
      (fun h => mem_filter.mpr ⟨inside,h⟩)
  have total := (card_le_card others).trans (card_union_le R T)
  have nr : R.card ≤ 2 := degR o ho
  have nt : T.card ≤ 2 := degT o ho
  rw [card_erase_of_mem ho] at total
  have size : A.card = 5 := by omega
  have diff : r ≠ t := by
    intro eq
    have same : R = T := by simp [R,T,eq]
    rw [same,union_self] at others
    have short := card_le_card others
    rw [card_erase_of_mem ho] at short
    omega
  have rare {u : ℝ} (hu : u ∈ D) (degu : ∀ a ∈ A, (A.filter (fun b => dist a b = u)).card ≤ 2) :
      u ∈ rareDistances A := mem_filter.mpr
    ⟨hu,OMA.R_erdos_132_R1.multiplicity_pos hu,multiplicity_of_degree A u degu⟩
  have lower : 1 < (rareDistances A).card := one_lt_card.mpr ⟨r,rare hr degR,t,rare ht degT,diff⟩
  have upper : (rareDistances A).card ≤ D.card := card_le_card (filter_subset _ _)
  exact ⟨size,le_antisymm (upper.trans few) lower⟩

/-- Every five-point planar configuration has two rare distances. -/
theorem fivePoints (A : Finset Plane) (size : A.card = 5) : 2 ≤ (rareDistances A).card := by
  by_cases few : (A.offDiag.image (fun p => dist p.1 p.2)).card ≤ 2
  · exact (twoDistanceSet A size.ge few).2.ge
  have tally := OMA.R_erdos_132_R1.distinct_lt_half_add_rare A (by omega)
  have three : 3 ≤ (A.offDiag.image (fun p => dist p.1 p.2)).card := by omega
  have h := lt_of_le_of_lt three tally
  rw [size] at h
  omega

end PrizeFormalizations.Erdos132.TwoDistances

theorem OMA.solution : OMA.R_erdos_132_R1_H1_R1.H1 :=
  PrizeFormalizations.Erdos132.TwoDistances.twoDistanceSet
