import Mathlib.RingTheory.Nullstellensatz

namespace MvPolynomial

open Ideal

variable {σ k : Type*} [Fintype σ] [Field k]

def IsAffineAlgebraicSet (W : Set (σ → k)) : Prop :=
  ∃ I : Ideal (MvPolynomial σ k), W = zeroLocus k I

-- Zariski Closure 정의 (이전 코드와 동일하다고 가정)
def zariskiClosure (S : Set (σ → k)) : Set (σ → k) :=
  zeroLocus k (vanishingIdeal k S)


omit [Fintype σ] in
/--
Cox–Little–O'Shea, Ch. 4 §4, Proposition 7 (i).
If I and J are ideals in k[x₁,...,xₙ], then
  V(I) = V(I + J) ∪ V(I : J).
-/
theorem zeroLocus_eq_union_colon (I J : Ideal (MvPolynomial σ k)) :
    zeroLocus k I = zeroLocus k (I ⊔ J) ∪ zeroLocus k (I.colon J) := by sorry

omit [Fintype σ] in
/--
Cox–Little–O'Shea, Ch. 4 §4, Proposition 7 (ii).
If V and W are affine algebraic sets in k^n, then
  V = (V ∩ W) ∪ (closure(V \ W)).
-/
theorem algebraic_set_eq_union_closure_diff (V W : Set (σ → k))
    (hV : IsAffineAlgebraicSet V) (hW : IsAffineAlgebraicSet W) :
    V = (V ∩ W) ∪ zariskiClosure (V \ W) := by sorry

omit [Fintype σ] in
/--
Cox–Little–O'Shea, Ch. 4 §4, Proposition 7 (iii).
In the situation of (i), we have
  closure(V(I) \ V(J)) ⊆ V(I : J).
-/
theorem closure_diff_subset_colon (I J : Ideal (MvPolynomial σ k)) :
    zariskiClosure (zeroLocus k I \ zeroLocus k J) ⊆ zeroLocus k (I.colon J) := by sorry

end MvPolynomial
