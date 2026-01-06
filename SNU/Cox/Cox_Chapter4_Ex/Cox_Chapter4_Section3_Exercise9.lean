import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.AdjoinRoot

open scoped BigOperators
open MvPolynomial

noncomputable section

variable {σ k : Type*} [Fintype σ] [Field k]

/--
Cox–Little–O'Shea, Ch.4 §3, Exercise 9(1).

Let `I` and `J` be ideals in `k[x₁,...,xₙ]` (modeled using `MvPolynomial`).
Show that `√(I * J) = √(I ⊓ J)`.
-/
example (I₁ J₁ : Ideal (MvPolynomial σ k)) :
    (I₁ * J₁).radical = (I₁ ⊓ J₁).radical := by
  sorry

abbrev σ' := Fin 2
abbrev x : MvPolynomial σ' k := X 0
abbrev y : MvPolynomial σ' k := X 1

def I : Ideal (MvPolynomial σ' k) := Ideal.span ({x} : Set (MvPolynomial σ' k))
def J : Ideal (MvPolynomial σ' k) := Ideal.span ({x, y} : Set (MvPolynomial σ' k))

/--
Cox–Little–O'Shea, Ch.4 §3, Exercise 9(2).

In `k[x,y]`, let `I = ⟨x⟩` and `J = ⟨x,y⟩`.
Show that `I` and `J` are radical ideals, but `I * J` is not radical.
-/
example :
    (I : Ideal (MvPolynomial σ' k)).IsRadical ∧ (J : Ideal (MvPolynomial σ' k)).IsRadical ∧ ¬ (I * J : Ideal (MvPolynomial σ' k)).IsRadical := by
  sorry

/--
Cox–Little–O'Shea, Ch.4 §3, Exercise 9(3).

With the same `I = ⟨x⟩` and `J = ⟨x,y⟩` in `k[x,y]`,
show that `√(I * J) ≠ √I * √J`.
-/
example :
    (I * J : Ideal (MvPolynomial σ' k)).radical ≠ I.radical * J.radical := by
  sorry
