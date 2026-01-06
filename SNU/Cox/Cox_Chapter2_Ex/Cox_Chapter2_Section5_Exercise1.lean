import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

open MvPolynomial MonomialOrder
open scoped MonomialOrder

namespace MonomialOrder

variable {σ R : Type*} [CommSemiring R]
variable {k : Type*} [Field k]
variable {m : MonomialOrder σ}

variable (m) in
/-- the leading coefficient of a multivariate polynomial with respect
to a monomial ordering -/
noncomputable def leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)

variable (m) in
/-- The set of leading terms of nonzero polynomials in an ideal I. -/
def LT_set (I : Ideal (MvPolynomial σ R)) : Set (MvPolynomial σ R) :=
  { f | ∃ g ∈ I, g ≠ 0 ∧ leadingTerm m g = f }

variable (m) in
def leadingTermIdeal (I : Ideal (MvPolynomial σ R)) : Ideal (MvPolynomial σ R) :=
  Ideal.span (LT_set m I)

theorem isUnit_leadingCoeff_iff_nonzero
  (m : MonomialOrder σ) (b : MvPolynomial σ k) :
  IsUnit (m.leadingCoeff b) ↔ b ≠ 0 := by
  constructor
  · intro h
    contrapose! h
    rw [h, m.leadingCoeff_zero]
    exact not_isUnit_zero
  · intro hb
    have h₁ : m.leadingCoeff b ≠ 0 := by exact MonomialOrder.leadingCoeff_ne_zero_iff.mpr hb
    exact isUnit_iff_ne_zero.mpr h₁

end MonomialOrder

noncomputable section
abbrev σ : Type := Fin 3
abbrev R : Type := ℝ

abbrev x : MvPolynomial σ ℝ := X 0
abbrev y : MvPolynomial σ ℝ := X 1
abbrev z : MvPolynomial σ ℝ := X 2

def g1 : MvPolynomial σ ℝ := x * (y ^ 2) - x * z + y
def g2 : MvPolynomial σ ℝ := x * y - (z ^ 2)
def g3 : MvPolynomial σ ℝ := x - y * (z ^ 4)

def I : Ideal (MvPolynomial σ ℝ) :=
  Ideal.span ({g1, g2, g3} : Set (MvPolynomial σ ℝ))

-- g := g2 - y*g3 = y^2*z^4 - z^2
def g : MvPolynomial σ ℝ := g2 - y * g3

/--
Cox–Little–O'Shea, Ch.2 §5, Exercise 1.

Let `I = ⟨g₁, g₂, g₃⟩ ⊆ ℝ[x,y,z]` where
`g₁ = x*y^2 - x*z + y`, `g₂ = x*y - z^2`, `g₃ = x - y*z^4`.
Using the lex order, let `g := g₂ - y*g₃` (so `g = y^2*z^4 - z^2`).
Show that `LT(g) ∉ ⟨LT(g₁), LT(g₂), LT(g₃)⟩`.
-/
example :
    g ∈ I ∧
      (MonomialOrder.lex (σ := σ)).leadingTerm g ∉
        Ideal.span
          ({ (MonomialOrder.lex (σ := σ)).leadingTerm g1
           , (MonomialOrder.lex (σ := σ)).leadingTerm g2
           , (MonomialOrder.lex (σ := σ)).leadingTerm g3
           } : Set (MvPolynomial σ ℝ)) := by
  sorry

end
