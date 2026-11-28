import OMAStatements.S_oeis_a078008
import Mathlib.Tactic

open OMA.S_oeis_a078008

namespace FareyParity

private def adjacent (g : Gap) : Prop := g.1.2*g.2.1=g.1.1*g.2.2+1
private def E (g : Gap) := evenDen (mediant g)

private lemma neighbors (g : Gap) (hg : adjacent g) : ∀ s ∈ children g, adjacent s := by
  rcases g with ⟨⟨p,q⟩,r,s⟩
  simp [children,mediant,adjacent] at *
  constructor <;> nlinarith only [hg]

private lemma invariant (n : ℕ) : ∀ g ∈ gaps n, adjacent g := by
  induction n with
  | zero => simp [gaps,adjacent]
  | succ n ih =>
    intro g hg
    obtain ⟨p,hp,h⟩ := List.mem_flatMap.mp hg
    exact neighbors p (ih p hp) g h

-- A common divisor of the mediant's numerator and denominator divides
-- q(p+r)-p(q+s)=1, so reduction really does preserve its denominator.
private lemma reduced (g : Gap) (hg : adjacent g) :
    (mediant g).1.gcd (mediant g).2 = 1 := by
  rcases g with ⟨⟨p,q⟩,r,s⟩
  change q*r=p*s+1 at hg
  change (p+r).gcd (q+s)=1
  let d := (p+r).gcd (q+s)
  have a : d ∣ q*(p+r) := dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _
  have b : d ∣ p*(q+s) := dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
  rw [show q*(p+r)=p*(q+s)+1 by nlinarith only [hg]] at a
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right b).mpr a)

private lemma test (g : Gap) (hg : adjacent g) :
    E g = ((g.1.2+g.2.2)%2 == 0) := by
  unfold E evenDen
  rw [reduced g hg,Nat.div_one]
  rfl

private lemma parity (q v : ℕ) (h : ¬ (q%2=0 ∧ v%2=0)) :
    (if (q+v+v)%2=0 then 1 else 0) + (if (q+(q+v))%2=0 then 1 else 0) +
      (if (q+v)%2=0 then 1 else 0) = 1 := by
  have x : (q+(q+v))%2=v%2 := by omega
  have y : (q+v+v)%2=q%2 := by omega
  simp only [x,y,Nat.add_mod q v 2]
  rcases (show q%2=0 ∨ q%2=1 by omega) with hq | hq <;>
    rcases (show v%2=0 ∨ v%2=1 by omega) with hv | hv <;> simp_all

-- Of a gap and its two children, exactly one mediant has even denominator.
private lemma splitCount (g : Gap) (hg : adjacent g) :
    (children g).countP E + (if E g then 1 else 0) = 1 := by
  let l : Gap := (g.1,mediant g)
  let r : Gap := (mediant g,g.2)
  have hl := test l (neighbors g hg l (by simp [children,l]))
  have hr := test r (neighbors g hg r (by simp [children,r]))
  rw [show children g=[l,r] from rfl]
  simp only [List.countP_cons,List.countP_nil,Nat.zero_add,hl,hr,test g hg,beq_iff_eq]
  rcases g with ⟨⟨p,q⟩,u,v⟩
  change q*u=p*v+1 at hg
  have h : ¬ (q%2=0 ∧ v%2=0) := by
    rintro ⟨hq,hv⟩
    have x : 2 ∣ q*u := dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero hq) _
    have y : 2 ∣ p*v := dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero hv) _
    rw [hg] at x
    omega
  exact parity q v h

private lemma counts (gs : List Gap) (ok : ∀ g ∈ gs, adjacent g) :
    (gs.flatMap children).countP E + gs.countP E = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have x := splitCount g (ok g (by simp))
    have y := ih (fun s hs => ok s (List.mem_cons_of_mem g hs))
    simp only [List.flatMap_cons,List.countP_append,List.countP_cons,List.length_cons]
    omega

private lemma sizes (gs : List Gap) : (gs.flatMap children).length = 2*gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [children,ih,Nat.mul_succ]

private lemma recurrence (n : ℕ) : fareyCount (n+2)=fareyCount (n+1)+2*fareyCount n := by
  have h : fareyCount (n+1)+fareyCount n=(gaps n).length := counts _ (invariant n)
  have h' : fareyCount (n+2)+fareyCount (n+1)=(gaps (n+1)).length := counts _ (invariant (n+1))
  have hs : (gaps (n+1)).length=2*(gaps n).length := sizes _
  omega

end FareyParity

theorem OMA.solution : type_of% @OMA.S_oeis_a078008.main := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih₀ ih₁ => rw [a, ih₀, ih₁, FareyParity.recurrence]
