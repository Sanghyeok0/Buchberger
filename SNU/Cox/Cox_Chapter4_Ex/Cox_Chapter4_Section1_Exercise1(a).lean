import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Nullstellensatz

open MvPolynomial

noncomputable section

abbrev σ : Type := Fin 3

abbrev x : MvPolynomial σ ℝ := X 0
abbrev y : MvPolynomial σ ℝ := X 1
abbrev z : MvPolynomial σ ℝ := X 2

def f₁ : MvPolynomial σ ℝ := y - x ^ 2
def f₂ : MvPolynomial σ ℝ := z - x ^ 3
def g₁ : MvPolynomial σ ℝ := (f₁ ^ 2) + (f₂ ^ 2)

/--
Ch.4 §1, Exercise 1(a).
Recall that 𝐕(y - x^2, z - x^3) is the twisted cubic in ℝ^3.
𝐕(y - x^2, z - x^3) = 𝐕((y - x^2)^2 + (z - x^3)^2) in ℝ^3.
-/
example :
    MvPolynomial.zeroLocus (K := ℝ) (Ideal.span ({f₁, f₂} : Set (MvPolynomial σ ℝ)))
      =
    MvPolynomial.zeroLocus (K := ℝ) (Ideal.span ({g₁} : Set (MvPolynomial σ ℝ))) := by
  sorry

end
