import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Nullstellensatz

open MvPolynomial

variable {σ : Type*} [Fintype σ]
variable {k : Type*} [Field k]


/--
Cox–Little–O'Shea, Ch.2 §5, Exercise 15.

Given polynomials `f₁, f₂, … ∈ k[x₁, …, xₙ]`, let `𝐕(f₁, f₂, …) ⊆ kⁿ` be the
affine algebraic set consisting of the solutions of the infinite system of equations
`f₁ = f₂ = ⋯ = 0`.
Show that there exists `N` such that `𝐕(f₁, f₂, …) = 𝐕(f₁, …, f_N)`.
-/
example (f : ℕ → MvPolynomial σ k) :
    ∃ N : ℕ,
      MvPolynomial.zeroLocus (K := k) (Ideal.span (Set.range f))
        =
      MvPolynomial.zeroLocus (K := k) (Ideal.span (f '' Set.Icc 0 N)) := by
  sorry
