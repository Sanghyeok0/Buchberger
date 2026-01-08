import SNU.Buchberger.MonomialIdeal
import Mathlib.RingTheory.MvPolynomial.Groebner

variable {σ : Type*}
variable {m : MonomialOrder σ}
variable {k : Type*} [Field k] [DecidableEq k]

open MonomialOrder

namespace MvPolynomial

variable (m) in
/--
**Gröbner basis property.**
For an ideal `I` and a finite set `G`, this means:

- `G ⊆ I`, and
- `⟨ LT(G) ⟩ = ⟨ LT(I) ⟩`,

where `LT(G) = { LT(g) | g ∈ G }` and `LT(I) = { LT(f) | f ∈ I \ {0} }`.
-/
def GroebnerBasis_prop (I : Ideal (MvPolynomial σ k)) (G : Finset (MvPolynomial σ k)) : Prop :=
  (G : Set (MvPolynomial σ k)) ⊆ I ∧
  Ideal.span ((fun g => leadingTerm m g) '' (G : Set (MvPolynomial σ k))) = leadingTermIdeal m I

variable (m) [DecidableEq σ] in
/--
Removing `0` from `G` does not change the Gröbner basis property:

`G` satisfies `G ⊆ I` and `⟨ LT(G) ⟩ = ⟨ LT(I) ⟩`
if and only if `G \ {0}` satisfies the same conditions.
-/
lemma GroebnerBasis_prop_remove_zero (I : Ideal (MvPolynomial σ k)) (G : Finset (MvPolynomial σ k)) :
  GroebnerBasis_prop m I G ↔ GroebnerBasis_prop m I (G \ {0}) := by
  -- shorthand
  let LT : MvPolynomial σ k → MvPolynomial σ k := fun g => leadingTerm m g

  -- Key fact: adding/removing `0` does not change the span of leading terms.
  have hspan_sdiff :
      Ideal.span (LT '' ((G \ ({0} : Finset (MvPolynomial σ k))) : Set (MvPolynomial σ k)))
        =
      Ideal.span (LT '' (G : Set (MvPolynomial σ k))) := by
    apply le_antisymm
    · -- (⊆) monotonicity: (G \ {0}) ⊆ G
      refine Ideal.span_mono ?_
      rintro x ⟨g, hg, rfl⟩
      have hg0 : g ∈ (G \ ({0} : Finset (MvPolynomial σ k))) := by
        simpa using hg
      have hgG : g ∈ G := (Finset.mem_sdiff.mp hg0).1
      exact ⟨g, (by simpa using hgG), rfl⟩
    · -- (⊇) each generator from G is either from (G\{0}) or is 0
      refine Ideal.span_le.2 ?_
      rintro x ⟨g, hgG, rfl⟩
      have hgG' : g ∈ G := by simpa using hgG
      by_cases h0 : g = 0
      · subst h0
        have hLT0 : LT (0 : MvPolynomial σ k) = 0 := by simp [LT]
        -- 0 is always in the span
        simpa only [LT, hLT0] using
          (Ideal.zero_mem
            (Ideal.span (LT '' ((G \ ({0} : Finset (MvPolynomial σ k))) : Set (MvPolynomial σ k)))))
      · have hg0 : g ∈ (G \ ({0} : Finset (MvPolynomial σ k))) := by
          refine Finset.mem_sdiff.2 ?_
          refine ⟨hgG', ?_⟩
          simp only [Finset.mem_singleton, h0, not_false_eq_true]
        have hx :
            LT g ∈ LT '' ((G \ ({0} : Finset (MvPolynomial σ k))) : Set (MvPolynomial σ k)) :=
          ⟨g, (by simpa using hg0), rfl⟩
        exact Ideal.subset_span hx

  -- Now unfold the definition and use `hspan_sdiff` (and `0 ∈ I`) to move between the two versions.
  unfold GroebnerBasis_prop
  constructor
  · rintro ⟨hGI, hspan⟩
    constructor
    · -- (G\{0}) ⊆ I
      simp only [Finset.coe_sdiff, Finset.coe_singleton, Set.diff_singleton_subset_iff,
        SetLike.mem_coe, zero_mem, Set.insert_eq_of_mem]
      exact hGI
    · -- ⟨ LT(G) ⟩ = ⟨ LT(I) ⟩ => ⟨ LT(G\{0}) ⟩ = ⟨ LT(I) ⟩
      unfold LT at hspan_sdiff
      rw [←hspan, ←hspan_sdiff]
      simp only [Finset.coe_sdiff, Finset.coe_singleton]

  · rintro ⟨hGI0, hspan0⟩
    constructor
    · -- G ⊆ I (use 0 ∈ I for the missing element)
      intro g hg
      have hgG : g ∈ G := by simpa using hg
      by_cases h0 : g = 0
      · subst h0
        simpa only using (Ideal.zero_mem I)
      · have hg0 : g ∈ (G \ ({0} : Finset (MvPolynomial σ k))) := by
          refine Finset.mem_sdiff.2 ⟨hgG, ?_⟩
          simp [h0]
        exact hGI0 (by simpa using hg0)
    · -- ⟨ LT(G\{0}) ⟩ = ⟨ LT(I) ⟩ => ⟨ LT(G) ⟩ = ⟨ LT(I) ⟩
      unfold LT at hspan_sdiff
      rw [←hspan0, ←hspan_sdiff]
      simp only [Finset.coe_singleton, Finset.coe_sdiff]

end MvPolynomial
