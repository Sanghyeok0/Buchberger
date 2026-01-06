import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations

open MvPolynomial

variable {σ k : Type*} [Fintype σ] [Field k]

/--
Ch.4 §3, Exercise 7(a).

Let `I` and `J` be ideals in `k[x₁,...,xₙ]`.
If `I^ℓ ≤ J` for some `ℓ > 0`, then `√I ≤ √J`.
-/
example (I J : Ideal (MvPolynomial σ k)) {ℓ : ℕ} (hℓ : 0 < ℓ) (hIJ : I ^ ℓ ≤ J) :
    I.radical ≤ J.radical := by
  sorry

/--
Ch.4 §3, Exercise 7(b).

Let `I` and `J` be ideals in `k[x₁,...,xₙ]`.
Show that `√(I + J) = √(√I + √J)`.
-/
example (I J : Ideal (MvPolynomial σ k)) :
    (I + J).radical = (I.radical + J.radical).radical := by
  sorry
