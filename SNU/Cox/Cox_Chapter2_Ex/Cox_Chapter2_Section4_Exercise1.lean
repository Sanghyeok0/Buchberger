import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Span

open MvPolynomial

variable {σ R : Type*} [Fintype σ] [CommSemiring R]
variable {k : Type*} [Field k]

namespace MvPolynomial

variable (R) in
def monomialIdeal (A : Set (σ →₀ ℕ)) : Ideal (MvPolynomial σ R) :=
  Ideal.span ((fun a => monomial a (1 : R)) '' A)

end MvPolynomial

-- Cox, Ch 2 §4, Exercise 1
example
    (I : Ideal (MvPolynomial σ k))
    (h :
      ∀ f : MvPolynomial σ k, f ∈ I →
        ∀ a : σ →₀ ℕ, a ∈ f.support → monomial a (1 : k) ∈ I) :
    ∃ S : Set (σ →₀ ℕ), I = MvPolynomial.monomialIdeal (σ := σ) (R := k) S := by
  sorry
