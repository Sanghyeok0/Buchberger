import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Nullstellensatz

open MvPolynomial

variable {σ : Type*} [Fintype σ]
variable {k : Type*} [Field k] [IsAlgClosed k]

/--
Cox–Little–O'Shea, Ch.4 §1, Theorem 1 (The Weak Nullstellensatz).

Let `k` be an algebraically closed field and let `I ⊆ k[x₁,...,xₙ]` be an ideal
satisfying `𝐕(I) = ∅`. Then `I = k[x₁,...,xₙ]`.
-/
theorem weak_nullstellensatz (I : Ideal (MvPolynomial σ k))
    (h : zeroLocus k I = ∅) : I = ⊤ := by
  sorry
