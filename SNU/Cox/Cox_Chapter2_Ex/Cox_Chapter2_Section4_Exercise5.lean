import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finsupp.MonomialOrder

open MvPolynomial

variable {σ R : Type*} [Fintype σ] [CommSemiring R]
variable {k : Type*} [Field k]
variable {m : MonomialOrder σ}

open scoped MonomialOrder

namespace MvPolynomial

variable (R) in
def monomialIdeal (A : Set (σ →₀ ℕ)) : Ideal (MvPolynomial σ R) :=
  Ideal.span ((fun a => monomial a (1 : R)) '' A)

end MvPolynomial

/-- Exponents whose monomials occur in an ideal `I`. -/
def expSet (I : Ideal (MvPolynomial σ k)) : Set (σ →₀ ℕ) :=
  {β | monomial β (1 : k) ∈ I}

-- Cox, Ch 2 §4, Exercise 5
example
    (A : Set (σ →₀ ℕ))
    (I : MvPolynomial.monomialIdeal (σ := σ) (R := k) A)
    (β : σ →₀ ℕ)
    (hβ :
      β ∈ expSet (σ := σ) (k := k)
        (MvPolynomial.monomialIdeal (σ := σ) (R := k) A))
    (hmin :
      ∀ γ,
        γ ∈ expSet (σ := σ) (k := k)
          (MvPolynomial.monomialIdeal (σ := σ) (R := k) A) →
          β ≺[m] γ) :
    β ∈ A := by
  sorry
