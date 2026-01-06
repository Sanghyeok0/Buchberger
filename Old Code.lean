import Mathlib.RingTheory.Nullstellensatz

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

theorem zariskiClosure_union (S T : Set (σ → k)) :
    zariskiClosure (S ∪ T) = zariskiClosure S ∪ zariskiClosure T := by
  classical
  unfold zariskiClosure
  -- 1) I(S ∪ T) = I(S) ⊓ I(T)
  have hI :
      vanishingIdeal k (S ∪ T) = (vanishingIdeal k S) ⊓ (vanishingIdeal k T) :=
    vanishingIdeal_union (k := k) S T
  -- reduce to a statement about zeroLocus of inf
  ext x
  rw [hI]
  constructor
  · intro hx
    -- hx : x ∈ V(I ⊓ J)
    by_cases hxS : x ∈ zeroLocus k (vanishingIdeal k S)
    · exact Or.inl hxS
    · -- show x ∈ V(J)
      refine Or.inr ?_
      have hx' : ∀ p ∈ (vanishingIdeal k S ⊓ vanishingIdeal k T), aeval x p = 0 := by
        simpa [MvPolynomial.zeroLocus] using hx
      -- from ¬ x ∈ V(I), get p ∈ I with p(x) ≠ 0
      have hxS' : ∃ p, p ∈ vanishingIdeal k S ∧ aeval x p ≠ 0 := by
        have : ¬ (∀ p ∈ vanishingIdeal k S, aeval x p = 0) := by
          simpa [MvPolynomial.zeroLocus] using hxS
        push_neg at this
        exact this
      rcases hxS' with ⟨p, hpI, hpne⟩
      -- now prove x ∈ V(J)
      change ∀ q ∈ vanishingIdeal k T, aeval x q = 0
      intro q hqJ
      have hpq_mem : p * q ∈ (vanishingIdeal k S ⊓ vanishingIdeal k T) := by
        refine Ideal.mem_inf.mpr ?_
        constructor
        · exact Ideal.mul_mem_right _ _ hpI
        · exact Ideal.mul_mem_left _ _ hqJ
      have hprod : aeval x p * aeval x q = 0 := by
        simpa [map_mul] using hx' (p * q) hpq_mem
      exact (mul_eq_zero.mp hprod).resolve_left hpne
  · rintro (hxS | hxT)
    · -- if x ∈ V(I), then x ∈ V(I ⊓ J)
      have hxS' : ∀ p ∈ vanishingIdeal k S, aeval x p = 0 := by
        simpa [MvPolynomial.zeroLocus] using hxS
      change ∀ p ∈ (vanishingIdeal k S ⊓ vanishingIdeal k T), aeval x p = 0
      intro p hp
      have hpS : p ∈ vanishingIdeal k S := (Ideal.mem_inf.mp hp).1
      exact hxS' p hpS
    · -- if x ∈ V(J), then x ∈ V(I ⊓ J)
      have hxT' : ∀ p ∈ vanishingIdeal k T, aeval x p = 0 := by
        simpa [MvPolynomial.zeroLocus] using hxT
      change ∀ p ∈ (vanishingIdeal k S ⊓ vanishingIdeal k T), aeval x p = 0
      intro p hp
      have hpT : p ∈ vanishingIdeal k T := (Ideal.mem_inf.mp hp).2
      exact hxT' p hpT

end MvPolynomial
