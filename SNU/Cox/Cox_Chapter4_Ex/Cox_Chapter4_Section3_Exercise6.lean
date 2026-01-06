import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open MvPolynomial

variable {σ k : Type*} [Fintype σ] [Field k]

/--
Ch.4 §3, Exercise 6(a).

Let `I₁`, `I₂`, `J` be ideals in `k[x₁,...,xₙ]`.
Show that `(I₁ + I₂) * J = I₁ * J + I₂ * J`.
-/
example (I₁ I₂ J : Ideal (MvPolynomial σ k)) :
    (I₁ + I₂) * J = I₁ * J + I₂ * J := by
  simpa only [Submodule.add_eq_sup] using add_mul I₁ I₂ J

/--
Ch.4 §3, Exercise 6(b).

Let `I₁,...,Iᵣ` be ideals in `k[x₁,...,xₙ]`.
Show that `(I₁ * ... * Iᵣ)^m = I₁^m * ... * Iᵣ^m`.
-/
example {r : ℕ} (I : Fin r → Ideal (MvPolynomial σ k)) (m : ℕ) :
    (∏ i, I i) ^ m = ∏ i, (I i) ^ m := by
  exact Eq.symm (Finset.prod_pow Finset.univ m I)
