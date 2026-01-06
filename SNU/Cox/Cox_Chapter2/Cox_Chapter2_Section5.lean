import Mathlib.RingTheory.Nullstellensatz

namespace MvPolynomial

variable {σ k : Type*} [Fintype σ] [Field k]

/-!
  ### Chapter 2. Gröbner Bases
  #### §5. The Hilbert Basis Theorem and Gröbner Bases
-/

/--
Cox–Little–O'Shea, Ch.2 §5, Definition 8.

Let I ⊆ k[x₁,...,xₙ] be an ideal. We will denote by 𝐕(I) the set
𝐕(I) = { (a₁,...,aₙ) ∈ kⁿ | f(a₁,...,aₙ) = 0 for all f ∈ I }.
-/
def IsAffineAlgebraicSet (W : Set (σ → k)) : Prop :=
  ∃ I : Ideal (MvPolynomial σ k), W = zeroLocus k I

end MvPolynomial
