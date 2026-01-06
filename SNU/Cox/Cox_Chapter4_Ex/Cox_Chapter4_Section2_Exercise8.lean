import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.AdjoinRoot

open scoped BigOperators
open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]

abbrev σ : Type := Fin 2
abbrev x : MvPolynomial σ k := X 0
abbrev y : MvPolynomial σ k := X 1

def f₁ : MvPolynomial σ k := y ^ 2 + (2 : MvPolynomial σ k) * x * y - 1
def f₂ : MvPolynomial σ k := x ^ 2 + 1

/--
Cox–Little–O'Shea, Ch.4 §2, Exercise 8.

Let `f₁ = y^2 + 2xy - 1` and `f₂ = x^2 + 1`.
Prove that `⟨f₁, f₂⟩` is not a radical ideal.
Hint: What is `f₁ + f₂`?
-/
example : ¬ (Ideal.span ({f₁, f₂} : Set (MvPolynomial σ k))).IsRadical := by sorry
