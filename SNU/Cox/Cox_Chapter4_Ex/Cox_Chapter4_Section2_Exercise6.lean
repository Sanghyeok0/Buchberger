import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open MvPolynomial

variable {σ k : Type*} [Fintype σ] [Field k]

/--
Ch.4 §2, Exercise 6(a).

Let `I` be an ideal in `k[x₁,...,xₙ]`. In the special case when `√I = ⟨f₁,f₂⟩`,
with `fᵢ^{mᵢ} ∈ I`, prove that `f^(m₁+m₂-1) ∈ I` for all `f ∈ √I`.
-/
example
    {I : Ideal (MvPolynomial σ k)}
    {f₁ f₂ : MvPolynomial σ k} {m₁ m₂ : ℕ}
    (hRad : I.radical = Ideal.span ({f₁, f₂} : Set (MvPolynomial σ k)))
    (hf₁ : f₁ ^ m₁ ∈ I)
    (hf₂ : f₂ ^ m₂ ∈ I) :
    ∀ f ∈ I.radical, f ^ (m₁ + m₂ - 1) ∈ I := by
  sorry

/--
Ch.4 §2, Exercise 6(b).

Let `I` be an ideal in `k[x₁,...,xₙ]`. Prove that there exists a single integer `m`
such that `f^m ∈ I` for all `f ∈ √I`.
-/
example (I : Ideal (MvPolynomial σ k)) :
    ∃ m : ℕ, ∀ f, f ∈ I.radical → f ^ m ∈ I := by
  sorry
