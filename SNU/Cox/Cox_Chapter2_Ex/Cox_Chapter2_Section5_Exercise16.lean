import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Nullstellensatz

open MvPolynomial

variable {σ : Type*} [Fintype σ]
variable {k : Type*} [Field k]

/--
Cox–Little–O'Shea, Ch.2 §5, Definition 8.

Let I ⊆ k[x₁,...,xₙ] be an ideal. We will denote by 𝐕(I) the set
𝐕(I) = { (a₁,...,aₙ) ∈ kⁿ | f(a₁,...,aₙ) = 0 for all f ∈ I }.
-/
def IsAffineAlgebraicSet (W : Set (σ → k)) : Prop :=
  ∃ I : Ideal (MvPolynomial σ k), W = zeroLocus k I

/--
Cox–Little–O'Shea, Ch.2 §5, Exercise 16.

We defined the ideal `𝐈(V)` of an **affine algebraic set** `V ⊆ kⁿ`. In this section, we defined
the **affine algebraic set** `𝐕(I)` of any ideal. In particular, `𝐕(𝐈(V))` is an **affine algebraic set**.
Prove that `𝐕(𝐈(V)) = V`.
-/
example (V : Set (σ → k)) (hV : IsAffineAlgebraicSet V) :
    MvPolynomial.zeroLocus (K := k)
        (MvPolynomial.vanishingIdeal (k := k) (K := k) V)
      = V := by
  sorry
