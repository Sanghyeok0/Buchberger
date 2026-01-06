import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Polynomial.UniqueFactorization

open MvPolynomial

variable {k : Type*} [Field k]

/-- “`n` is the smallest power such that `p^n ∈ I`”. -/
def IsMinPowInIdeal {R : Type*} [CommSemiring R] (p : R) (I : Ideal R) (n : ℕ) : Prop :=
  p ^ n ∈ I ∧ ∀ m : ℕ, m < n → p ^ m ∉ I

/--
Ch.4 §2, Exercise 7(a).

Show that `x+y ∈ √⟨x^3, y^3, x*y*(x+y)⟩` and that the smallest power of `x+y` in the ideal is `3`.
-/
example :
    let σ : Type := Fin 2
    let x : MvPolynomial σ k := X 0
    let y : MvPolynomial σ k := X 1
    let J : Ideal (MvPolynomial σ k) :=
      Ideal.span ({x ^ 3, y ^ 3, x * y * (x + y)} : Set (MvPolynomial σ k))
    (x + y ∈ J.radical) ∧ IsMinPowInIdeal (x + y) J 3 := by
  sorry

/--
Ch.4 §2, Exercise 7(b).

Is `x^2+3*x*z ∈ √⟨x+z, x^2*y, x - z^2⟩`?
We assume the characteristic of `k` is not `2`.)
-/
example (h_char : ringChar k ≠ 2) :
    let σ : Type := Fin 3
    let x : MvPolynomial σ k := X 0
    let y : MvPolynomial σ k := X 1
    let z : MvPolynomial σ k := X 2
    let K : Ideal (MvPolynomial σ k) :=
      Ideal.span ({x + z, x ^ 2 * y, x - z ^ 2} : Set (MvPolynomial σ k))
    (x ^ 2 + (3 : k) • (x * z)) ∉ K.radical := by
  sorry
