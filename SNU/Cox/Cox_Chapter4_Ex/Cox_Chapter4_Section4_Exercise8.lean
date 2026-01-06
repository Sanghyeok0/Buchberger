import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Operations
import SNU.Cox.Cox_Chapter2.Cox_Chapter2_Section5

namespace MvPolynomial

variable {σ k : Type*} [Fintype σ] [Field k]

omit [Fintype σ] in
/--
Cox–Little–O'Shea, Ch. 4 §4, Exercise 8.
Let V, W ⊆ k^n be affine algebraic sets. Prove that I(V) : I(W) = I(V \ W).
-/
theorem vanishingIdeal_diff_eq_colon (V W : Set (σ → k))
    (hV : IsAffineAlgebraicSet V) (hW : IsAffineAlgebraicSet W) :
    (vanishingIdeal k V).colon (vanishingIdeal k W) = vanishingIdeal k (V \ W) := by sorry

end MvPolynomial
