import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Nullstellensatz

open MvPolynomial

variable {σ : Type*} [Fintype σ]

/--
Ch.4 §1, Exercise 1(b).

Any affine variety 𝐕(I) ⊆ ℝ^n can be defined by a single equation,
i.e. there exists `f` such that 𝐕(I) = 𝐕(⟨f⟩).
-/
example (I : Ideal (MvPolynomial σ ℝ)) :
    ∃ f : MvPolynomial σ ℝ,
      MvPolynomial.zeroLocus (K := ℝ) I
        =
      MvPolynomial.zeroLocus (K := ℝ) (Ideal.span ({f} : Set (MvPolynomial σ ℝ))) := by
  sorry
