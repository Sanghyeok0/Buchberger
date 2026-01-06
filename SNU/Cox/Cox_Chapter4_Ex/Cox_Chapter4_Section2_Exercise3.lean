import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Nilpotent.Lemmas

open scoped BigOperators
open Polynomial

noncomputable section

def f : ℝ[X] := (X : ℝ[X]) ^ 2 + 1
def I : Ideal ℝ[X] := Ideal.span ({f} : Set ℝ[X])

/-- “Zero locus” of an ideal in the univariate case. -/
def zeroLocus (J : Ideal ℝ[X]) : Set ℝ :=
  { r | ∀ g ∈ J, g.eval r = 0 }

/--
Ch.4 §2, Exercise 3.
Show that `⟨x^2 + 1⟩ ⊆ ℝ[x]` is a radical ideal, but that `𝐕(x^2 + 1)` is the empty set.
-/
example :
    I.IsRadical ∧ zeroLocus I = (∅ : Set ℝ) := by
  constructor
  · -- radicality of the principal ideal
    have hf_irreducible : Irreducible f := by
      have hf_deg : f.natDegree = 2 := by
        have : f = C 1 * X  ^ 2 + C 0 * X + C 1 := by unfold f; simp only [map_one, one_mul, map_zero,
          zero_mul, add_zero]
        rw [this]
        apply Polynomial.natDegree_quadratic
        simp only [ne_eq, one_ne_zero, not_false_eq_true]
      have hp2 : 2 ≤ f.natDegree := by exact Nat.le_of_eq (id (Eq.symm hf_deg))
      have hp3 : f.natDegree ≤ 3 := by rw [hf_deg]; exact Nat.AtLeastTwo.prop
      refine
        (Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three
            (p := f) hp2 hp3).2 ?_
      have hf_roots : (f.roots = 0) := by
        classical
        have hf0 : f ≠ 0 := by
          refine Monic.ne_zero ?_
          refine Monic.def.mpr ?_
          unfold f
          simp only [Nat.ofNat_pos, leadingCoeff_X_pow_add_one]
        -- roots = 0  ↔  no roots
        refine (Polynomial.roots_eq_zero_iff_isRoot_eq_bot hf0).2 ?_
        ext r
        -- `IsRoot f r` ↔ `f.eval r = 0`
        -- but `r^2 + 1 ≠ 0` over ℝ
        simp [Polynomial.IsRoot, f, pow_two]
        nlinarith
      exact hf_roots
        -- use: IsRadical f ↔ (Ideal.span {f}).IsRadical
    have hf_rad : IsRadical f := (hf_irreducible.prime).isRadical
    -- unfold I to match the statement
    simpa [I] using (isRadical_iff_span_singleton (y := f)).mp hf_rad
  · -- zero locus is empty
    ext r
    constructor
    · intro hr
      -- since f ∈ I, it must vanish at r
      have hf_mem : f ∈ I := by
        -- generator is in the span
        simpa [I] using (Ideal.subset_span (by simp : f ∈ ({f} : Set ℝ[X])))
      have h0 : f.eval r = 0 := hr f hf_mem

      have hne : f.eval r ≠ 0 := by
        -- f.eval r = r^2 + 1
        have : f.eval r = r^2 + (1 : ℝ) := by simp [f, pow_two]
        -- r^2 + 1 ≠ 0
        nlinarith [this]
      exact (hne h0).elim
    · intro hr
      cases hr
