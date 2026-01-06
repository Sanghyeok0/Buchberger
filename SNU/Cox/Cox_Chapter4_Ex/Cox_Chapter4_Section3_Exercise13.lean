import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.MvPolynomial.Eval

open scoped BigOperators
open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]
variable {m n : ℕ}

/-
Cox–Little–O'Shea, Ch.4 §3, Exercise 13.

Let `A` be an `m × n` matrix over a field `k`.
Thinking of `x = A y`, define the substitution map
`α_A : k[x₁,...,xₘ] → k[y₁,...,yₙ]` by sending `x_i` to `∑ j, a_{i,j} * y_j`
and fixing coefficients in `k`.

Show that `α_A` is a ring homomorphism (hence additive and multiplicative, and `k`-linear).
-/

def alphaA (A : Matrix (Fin m) (Fin n) k) :
    MvPolynomial (Fin m) k → MvPolynomial (Fin n) k :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : k →+* MvPolynomial (Fin n) k)
    (fun i : Fin m =>
      ∑ j : Fin n, MvPolynomial.C (A i j) * MvPolynomial.X j)

/--
Exercise 13 (ring-hom properties, packaged as the usual identities).
-/
example (A : Matrix (Fin m) (Fin n) k) :
    (alphaA (k := k) (m := m) (n := n) A) 1 = 1
    ∧ (∀ f g, alphaA (k := k) (m := m) (n := n) A (f + g)
        = alphaA (k := k) (m := m) (n := n) A f
        + alphaA (k := k) (m := m) (n := n) A g)
    ∧ (∀ f g, alphaA (k := k) (m := m) (n := n) A (f * g)
        = alphaA (k := k) (m := m) (n := n) A f
        * alphaA (k := k) (m := m) (n := n) A g) := by
  constructor
  · simp [alphaA]
  constructor
  · intro f g
    simp [alphaA]
  · intro f g
    simp [alphaA]

/--
A convenient `k`-linearity form: `α_A (C r * f + C s * g) = ...`.
-/
example (A : Matrix (Fin m) (Fin n) k) (r s : k)
    (f g : MvPolynomial (Fin m) k) :
    alphaA (k := k) (m := m) (n := n) A (MvPolynomial.C r * f + MvPolynomial.C s * g)
      =
    MvPolynomial.C r * alphaA (k := k) (m := m) (n := n) A f
      +
    MvPolynomial.C s * alphaA (k := k) (m := m) (n := n) A g := by
  simp [alphaA, map_add, map_mul, add_mul, mul_add]
