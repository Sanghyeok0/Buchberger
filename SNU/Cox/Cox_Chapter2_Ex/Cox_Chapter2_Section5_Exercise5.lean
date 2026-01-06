import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

open MvPolynomial MonomialOrder
open scoped MonomialOrder

variable {σ R : Type*} [CommSemiring R]
variable {k : Type*} [Field k]
variable {m : MonomialOrder σ}

namespace MonomialOrder

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

end MonomialOrder

namespace MvPolynomial

variable (m) in
def IsGroebnerBasis (I : Ideal (MvPolynomial σ k)) (G : Finset (MvPolynomial σ k)) : Prop :=
  (G : Set (MvPolynomial σ k)) ⊆ I ∧
  Ideal.span ((fun g => leadingTerm m g) '' (G : Set (MvPolynomial σ k))) = leadingTermIdeal m I

/--
Cox–Little–O'Shea, Ch.2 §5, Exercise 5.

`G ⊆ I` is a Gröbner basis of `I` iff the leading term of any element of `I`
is divisible by one of the `LT(g)` for `g ∈ G`.
-/
example (I : Ideal (MvPolynomial σ k)) (G : Finset (MvPolynomial σ k))
    (hGI : ∀ g ∈ G, g ∈ I) :
    IsGroebnerBasis (m := m) I G ↔
    ∀ f : MvPolynomial σ k, f ∈ I → f ≠ 0 →
    ∃ g : MvPolynomial σ k, g ∈ G ∧ g ≠ 0 ∧ (m.leadingTerm g ∣ m.leadingTerm f) := by
    sorry

end MvPolynomial
