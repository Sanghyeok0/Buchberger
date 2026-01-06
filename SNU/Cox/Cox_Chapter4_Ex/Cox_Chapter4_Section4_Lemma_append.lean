import Mathlib.RingTheory.Nullstellensatz

namespace MvPolynomial

variable {σ k : Type*} [Field k]

/--
Ch. 4 §4 (basic property of vanishing ideals).

For subsets `S T ⊆ k^n`, the vanishing ideal of a union is the intersection of vanishing ideals.
`𝐈(S ∪ T) = 𝐈(S) ⊓ 𝐈(T)`
-/
theorem vanishingIdeal_union (S T : Set (σ → k)) :
    vanishingIdeal k (S ∪ T) = vanishingIdeal k S ⊓ vanishingIdeal k T := by
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

end MvPolynomial
