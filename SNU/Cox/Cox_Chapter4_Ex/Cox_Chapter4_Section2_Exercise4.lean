import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open MvPolynomial

variable {σ k : Type*} [Field k]

/-
Cox–Little–O'Shea, Ch.4 §2, Exercise 4.

Let `I` be an ideal in `k[x₁, ..., xₙ]`.

(a) Show that `√I` is a radical ideal.
(b) Show that `I` is radical iff `I = √I`.
(c) Show that `√(√I) = √I`.
-/

variable (I : Ideal (MvPolynomial σ k))

/-- (a) `√I` is a radical ideal. -/
example : (I.radical).IsRadical := by
  sorry

/-- (b) `I` is radical iff `I = √I`. -/
example : I.IsRadical ↔ I = I.radical := by
  sorry

/-- (c) `√(√I) = √I`. -/
example : (I.radical).radical = I.radical := by
  sorry
