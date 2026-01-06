import Mathlib.RingTheory.Nullstellensatz

namespace MvPolynomial

variable {σ k : Type*} [Fintype σ] [Field k]

def IsAffineAlgebraicSet (W : Set (σ → k)) : Prop :=
  ∃ I : Ideal (MvPolynomial σ k), W = zeroLocus k I

def zariskiClosure (S : Set (σ → k)) : Set (σ → k) :=
  zeroLocus k (vanishingIdeal k S)

omit [Fintype σ] in
/--
Cox–Little–O'Shea, Ch. 4 §4, Proposition 1.

If S ⊆ k^n, the affine algebraic set V(I(S)) is the smallest algebraic set that contains S.
(i.e., if W is any affine algebraic set containing S, then V(I(S)) ⊆ W).
-/
theorem zariskiClosure_is_smallest_algebraic_set (S : Set (σ → k)) (W : Set (σ → k))
    (h_W : IsAffineAlgebraicSet W)
    (h_subset : S ⊆ W) :
    zariskiClosure S ⊆ W := by
  rcases h_W with ⟨J, rfl⟩
  apply zeroLocus_anti_mono
  apply le_zeroLocus_iff_le_vanishingIdeal.1
  exact h_subset
