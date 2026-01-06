import Mathlib.RingTheory.Nullstellensatz
import SNU.Cox.Cox_Chapter4.Cox_Chapter4_Section3

namespace MvPolynomial

variable {σ k : Type*} [Fintype σ] [Field k]

/--
Cox–Little–O'Shea, Ch.4 §4, Definition 2

Zariski closure of a subset `S ⊆ k^σ` (affine space),
defined as `𝐕(𝐈(S))`
-/
def zariskiClosure (S : Set (σ → k)) : Set (σ → k) :=
  zeroLocus k (vanishingIdeal k S)

omit [Fintype σ] in
/--
Cox–Little–O'Shea, Ch. 4 §4, Proposition 1.

If S ⊆ k^n, the affine variety V(I(S)) is the smallest variety that contains S.
(i.e., if W is any affine variety containing S, then V(I(S)) ⊆ W).
-/
theorem zariskiClosure_is_smallest_variety (S : Set (σ → k)) (W : Set (σ → k))
    (h_variety : ∃ I : Ideal (MvPolynomial σ k), W = zeroLocus k I)
    (h_subset : S ⊆ W) :
    zariskiClosure S ⊆ W := by
  rcases h_variety with ⟨J, rfl⟩
  apply zeroLocus_anti_mono
  apply le_zeroLocus_iff_le_vanishingIdeal.1
  exact h_subset

omit [Fintype σ] in
/--
Ch. 4 §4 (basic property of vanishing ideals).

For subsets `S T ⊆ k^n`, the vanishing ideal of a union is the intersection of vanishing ideals.
In Lean, intersection of ideals is `⊓`.
-/
theorem vanishingIdeal_union (S T : Set (σ → k)) :
    vanishingIdeal k (S ∪ T) = vanishingIdeal k S ⊓ vanishingIdeal k T := by
  classical
  ext p
  constructor
  · intro hp
    refine Ideal.mem_inf.2 ?_
    constructor
    · have hp' : ∀ x ∈ (S ∪ T), aeval x p = 0 := by
        simpa only [Set.mem_union, aeval_eq_eval, vanishingIdeal, Submodule.mem_mk,
          AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] using hp
      change ∀ x ∈ S, aeval x p = 0
      intro x hx
      exact hp' x (Or.inl hx)
    · have hp' : ∀ x ∈ (S ∪ T), aeval x p = 0 := by
        simpa only [Set.mem_union, aeval_eq_eval, vanishingIdeal, Submodule.mem_mk,
          AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] using hp
      change ∀ x ∈ T, aeval x p = 0
      intro x hx
      exact hp' x (Or.inr hx)
  · intro hp
    have hS : p ∈ vanishingIdeal k S := (Ideal.mem_inf.1 hp).1
    have hT : p ∈ vanishingIdeal k T := (Ideal.mem_inf.1 hp).2
    have hS' : ∀ x ∈ S, aeval x p = 0 := by
      simpa only [aeval_eq_eval, vanishingIdeal, Submodule.mem_mk, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_setOf_eq] using hS
    have hT' : ∀ x ∈ T, aeval x p = 0 := by
      simpa only [aeval_eq_eval, vanishingIdeal, Submodule.mem_mk, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_setOf_eq] using hT
    change ∀ x ∈ (S ∪ T), aeval x p = 0
    intro x hx
    rcases hx with hx | hx
    · exact hS' x hx
    · exact hT' x hx

omit [Fintype σ] in
/--
Lemma 3 (i). I(S̄) = I(S).
-/
lemma vanishingIdeal_zariskiClosure (S : Set (σ → k)) :
    vanishingIdeal k (zariskiClosure S) = vanishingIdeal k S := by
  rw [zariskiClosure]
  rw [le_antisymm_iff]
  constructor
  · apply vanishingIdeal_anti_mono
    exact zeroLocus_vanishingIdeal_le S
  · exact le_vanishingIdeal_zeroLocus (vanishingIdeal k S)

omit [Fintype σ] in
/--
Lemma 3 (ii). If S ⊆ T, then S̄ ⊆ T̄.
-/
theorem zariskiClosure_mono {S T : Set (σ → k)} (h : S ⊆ T) :
    zariskiClosure S ⊆ zariskiClosure T := by
  unfold zariskiClosure
  apply zeroLocus_anti_mono
  apply vanishingIdeal_anti_mono
  exact h

omit [Fintype σ] in
/--
Lemma 3 (iii). `S̄ ∪ T̄ = (S ∪ T)̄ `.
Note: Zariski closure distributes over finite unions.
-/
theorem zariskiClosure_union (S T : Set (σ → k)) :
    zariskiClosure (S ∪ T) = zariskiClosure S ∪ zariskiClosure T := by
  classical
  unfold zariskiClosure
  simpa only [vanishingIdeal_union] using
    (zeroLocus_inf (k := k) (I := vanishingIdeal k S) (J := vanishingIdeal k T))

end MvPolynomial
