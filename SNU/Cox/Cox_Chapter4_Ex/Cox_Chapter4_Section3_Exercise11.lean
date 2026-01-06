import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Data.Complex.Basic
import SNU.Cox.Cox_Chapter4.Cox_Chapter4_Section3

open MvPolynomial

variable {σ : Type*} [Fintype σ]

/--
Cox–Little–O'Shea, Ch.4 §3, Exercise 11(a).

Let `I` and `J` be ideals in `ℂ[x₁,...,xₙ]`.
Show that `I` and `J` are coprime (`IsCoprime I J`) if and only if
`𝐕(I) ∩ 𝐕(J) = ∅`, where `𝐕(I)` is the **affine algebraic set** of `I`.
-/
example (I J : Ideal (MvPolynomial σ ℂ)) :
    IsCoprime I J ↔
      (MvPolynomial.zeroLocus (k := ℂ) (K := ℂ) I) ∩
        (MvPolynomial.zeroLocus (k := ℂ) (K := ℂ) J)
        = (∅ : Set (σ → ℂ)) := by sorry

/--
Cox–Little–O'Shea, Ch.4 §3, Exercise 11(b).

Let `I` and `J` be ideals in `k[x₁,...,xₙ]`.
If `I` and `J` are coprime, then `IJ = I ∩ J`.
-/
example {k : Type*} [Field k] (I J : Ideal (MvPolynomial σ k)) (h : IsCoprime I J) :
    I * J = I ⊓ J := by
  simpa only using Ideal.mul_eq_inf_of_coprime (I := I) (J := J) h.sup_eq
