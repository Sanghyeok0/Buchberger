import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPolynomial.Groebner

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

namespace MvPolynomial

variable {σ k : Type*} [Field k]
variable {m : MonomialOrder σ}

theorem division_algorithm_existence (m : MonomialOrder σ)
  {B : Set (MvPolynomial σ k)} (hB : ∀ b ∈ B, b ≠ 0) (f : MvPolynomial σ k) :
  ∃ (g : B →₀ (MvPolynomial σ k)) (r : MvPolynomial σ k),
    f = Finsupp.linearCombination _ (fun (p : B) ↦ (p : MvPolynomial σ k)) g + r ∧
    (∀ (p : B), m.degree ((p : MvPolynomial σ k) * (g p)) ≼[m] m.degree f) ∧
    (∀ c ∈ r.support, ∀ b ∈ B, ¬ m.degree b ≤ c) :=
  MonomialOrder.div_set
      (fun b hb => (isUnit_leadingCoeff_iff_nonzero m b).mpr (hB b hb))
      f

noncomputable def quotients (m : MonomialOrder σ)
  {B : Set (MvPolynomial σ k)} (hB : ∀ b ∈ B, b ≠ 0) (f : MvPolynomial σ k) :
  B →₀ MvPolynomial σ k :=
  (division_algorithm_existence m hB f).choose

noncomputable def normalForm (m : MonomialOrder σ)
  {B : Set (MvPolynomial σ k)} (hB : ∀ b ∈ B, b ≠ 0) (f : MvPolynomial σ k) :
  MvPolynomial σ k :=
  (Exists.choose_spec (division_algorithm_existence m hB f)).choose

/--
Ch.2 §5, Exercise 3(a).

Suppose `I = ⟨f₁,…,fₛ⟩` (modeled as `Ideal.span B`) and
`⟨LT(f₁),…,LT(fₛ)⟩` is strictly smaller than `⟨LT(I)⟩`.
Prove that there exists `f ∈ I` whose remainder (normal form) on division by `B`
is nonzero.
-/
example
    (B : Set (MvPolynomial σ k))
    (hB : ∀ b ∈ B, b ≠ (0 : MvPolynomial σ k))
    (hproper : Ideal.span ((fun f : MvPolynomial σ k => m.leadingTerm f) '' B) < MonomialOrder.leadingTermIdeal m (Ideal.span B)) :
    ∃ f : MvPolynomial σ k,
      f ∈ (Ideal.span B : Ideal (MvPolynomial σ k)) ∧
      MvPolynomial.normalForm m hB f ≠ 0 := by
  sorry

end MvPolynomial
