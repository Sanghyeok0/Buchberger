import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.MvPolynomial.Basic

open MvPolynomial

variable {σ : Type*} [Fintype σ]
variable {k : Type*} [Field k]

/--
Cox–Little–O'Shea, Ch.2 §5, Exercise 14.

For an infinite sequence `f₀, f₁, f₂, ...` in `k[x₁,...,xₙ]`,
there exists `N` such that all later terms lie in the ideal generated
by the first `N` terms.
-/
example (f : ℕ → MvPolynomial σ k) :
    ∃ N : ℕ, ∀ i : ℕ, N + 1 ≤ i → f i ∈ Ideal.span (f '' (Set.Icc 0 N)) := by
  sorry
