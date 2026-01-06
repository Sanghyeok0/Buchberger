import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Span

variable {σ k : Type*} [Fintype σ]
variable [Field k]

/-
Ch.4 §1, Exercise 9.

Let `k` be a field and let `S` be the set of all polynomials in `k[x₁, …, xₙ]`
that have no zeros in `kⁿ`. If `I` is an ideal such that `I ∩ S = ∅`,
show that `𝐕(I) ≠ ∅`.
-/

def S : Set (MvPolynomial σ k) :=
  {p | ∀ x : σ → k, MvPolynomial.aeval x p ≠ (0 : k)}

example (I : Ideal (MvPolynomial σ k))
    (hdisj : (I : Set (MvPolynomial σ k)) ∩ S (σ := σ) (k := k) = ∅) :
    (MvPolynomial.zeroLocus (K := k) I).Nonempty := by
  sorry
