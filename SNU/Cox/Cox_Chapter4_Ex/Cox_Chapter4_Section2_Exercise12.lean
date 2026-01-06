import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.MvPolynomial.CommRing

open MvPolynomial

noncomputable section

abbrev σ : Type := Fin 2
abbrev x : MvPolynomial σ ℚ := X 0
abbrev y : MvPolynomial σ ℚ := X 1

def f : MvPolynomial σ ℚ :=
  x ^ 5
    + 3 * x ^ 4 * y
    + 3 * x ^ 3 * y ^ 2
    - 2 * x ^ 4 * y ^ 2
    + x ^ 2 * y ^ 3
    - 6 * x ^ 3 * y ^ 3
    - 6 * x ^ 2 * y ^ 4
    + x ^ 3 * y ^ 4
    - 2 * x * y ^ 5
    + 3 * x ^ 2 * y ^ 5
    + 3 * x * y ^ 6
    + y ^ 7

/--
Ch. 4 §2, Exercise 12.

Show that
  √⟨ f ⟩ = ⟨ (x + y) * (x - y^2) ⟩,
where
  f = x^5 + 3x^4y + 3x^3y^2 - 2x^4y^2 + x^2y^3 - 6x^3y^3 - 6x^2y^4
      + x^3y^4 - 2xy^5 + 3x^2y^5 + 3xy^6 + y^7 ∈ ℚ[x,y].
-/
example :
    (Ideal.span ({f} : Set (MvPolynomial σ ℚ))).radical
      =
    Ideal.span ({(x + y) * (x - y ^ 2)} : Set (MvPolynomial σ ℚ)) := by
  sorry
