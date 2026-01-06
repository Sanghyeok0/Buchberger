import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
-- import Mathlib.Algebra.GCDMonoid.Basic

open scoped BigOperators
open MvPolynomial

noncomputable section

variable {σ : Type*} [Fintype σ]
variable {k : Type*} [Field k]

local instance : GCDMonoid (MvPolynomial σ k) := UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial σ k)

/--
Cox–Little–O'Shea, Ch.4 §2, Exercise 10.

Prove the following ideal-theoretic characterization of `gcd(f,g)`:
given polynomials `f, g, h` in `k[x₁, …, xₙ]`, then `h = gcd f g` if and only if
`h` is a generator of the smallest principal ideal containing `⟨f, g⟩`
(i.e., `⟨f, g⟩ ⊆ ⟨h⟩` and, whenever `J` is a principal ideal such that
`J ⊇ ⟨f, g⟩`, we have `⟨h⟩ ⊆ J`).
-/
example (f g h : MvPolynomial σ k) :
    h = gcd f g ↔
      (Ideal.span ({f, g} : Set (MvPolynomial σ k)) ≤ Ideal.span ({h} : Set (MvPolynomial σ k)) ∧
        ∀ a : MvPolynomial σ k,
          Ideal.span ({f, g} : Set (MvPolynomial σ k)) ≤ Ideal.span ({a} : Set (MvPolynomial σ k)) →
            Ideal.span ({h} : Set (MvPolynomial σ k)) ≤ Ideal.span ({a} : Set (MvPolynomial σ k))) := by
  sorry
