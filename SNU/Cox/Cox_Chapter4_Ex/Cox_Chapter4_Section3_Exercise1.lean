import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.MvPolynomial.CommRing

open MvPolynomial

/--
Ch.4 §3, Exercise 1.

Show that in `ℚ[x,y]`, we have
⟨(x+y)^4 (x^2+y)^2 (x-5y)⟩ ∩ ⟨(x+y) (x^2+y)^3 (x+3y)⟩
  = ⟨(x+y)^4 (x^2+y)^3 (x-5y) (x+3y)⟩.
-/
example :
    let σ : Type := Fin 2
    let x : MvPolynomial σ ℚ := X (0 : σ)
    let y : MvPolynomial σ ℚ := X (1 : σ)
    Ideal.span ({((x + y) ^ 4) * ((x ^ 2 + y) ^ 2) * (x - 5 * y)} : Set (MvPolynomial σ ℚ)) ⊓
      Ideal.span ({((x + y)) * ((x ^ 2 + y) ^ 3) * (x + 3 * y)} : Set (MvPolynomial σ ℚ))
    =
    Ideal.span ({((x + y) ^ 4) * ((x ^ 2 + y) ^ 3) * (x - 5 * y) * (x + 3 * y)} : Set (MvPolynomial σ ℚ)) := by
  sorry
