import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations

open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]

abbrev σ : Type := Fin 2
abbrev x : MvPolynomial σ k := X 0
abbrev y : MvPolynomial σ k := X 1

/--
Cox–Little–O'Shea, Ch.4 §2, Exercise 1 (general form).

For a field `k` (not necessarily algebraically closed),
`√⟨x^n, y^m⟩ = ⟨x, y⟩` in `k[x,y]` for all positive integers `n, m`.
-/
example {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
  (Ideal.span ({(x : MvPolynomial σ k) ^ n, (y : MvPolynomial σ k) ^ m} : Set (MvPolynomial σ k))).radical
    =
  Ideal.span ({(x : MvPolynomial σ k), (y : MvPolynomial σ k)} : Set (MvPolynomial σ k)) := by sorry
