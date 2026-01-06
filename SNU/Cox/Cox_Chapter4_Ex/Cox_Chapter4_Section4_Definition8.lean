import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Algebra.MvPolynomial.Basic

namespace MvPolynomial

variable {σ k : Type*} [Fintype σ] [Field k]

open Ideal

/--
Cox–Little–O'Shea, Ch. 4 §4, Definition 8.
The saturation of I with respect to J, denoted I : J^∞,
defined as `⨆ n, I.colon (J ^ n)`.
-/
noncomputable def saturation (I J : Ideal (MvPolynomial σ k)) : Ideal (MvPolynomial σ k) :=
  ⨆ n : ℕ, I.colon (J ^ n)

end MvPolynomial
