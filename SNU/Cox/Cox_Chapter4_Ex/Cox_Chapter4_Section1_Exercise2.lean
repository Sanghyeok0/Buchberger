import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Nullstellensatz

open MvPolynomial

noncomputable section

abbrev σ : Type := Fin 2

abbrev x : MvPolynomial σ ℝ := X 0
abbrev y : MvPolynomial σ ℝ := X 1

def J : Ideal (MvPolynomial σ ℝ) :=
  Ideal.span ({x ^ 2 + y ^ 2 - 1, y - 1} : Set (MvPolynomial σ ℝ))

/--
Ch.4 §1, Exercise 2.
Let `J = ⟨x^2 + y^2 - 1, y - 1⟩`.
Find `f ∈ 𝐈(𝐕(J))` with `f ∉ J`.
-/
example :
    ∃ f : MvPolynomial σ ℝ,
      f ∈
        MvPolynomial.vanishingIdeal (k := ℝ) (K := ℝ)
          (MvPolynomial.zeroLocus (K := ℝ) J)
        ∧
      f ∉ J := by sorry

end
