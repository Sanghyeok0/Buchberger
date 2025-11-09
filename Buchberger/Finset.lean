import Mathlib.Algebra.BigOperators.Group.Finset.Basic

variable {ι κ M β γ : Type*} {s : Finset ι}

namespace Finset

section CommMonoid

variable [CommMonoid M]

@[to_additive (attr := simp)]
theorem prod_ite_not_mem (s t : Finset ι)
  [DecidableEq ι] (f : ι → M) :
  (∏ x ∈ s, if x ∈ t then 1 else f x) = ∏ x ∈ s \ t, f x := by
  -- decompose s into (s \ t) ∪ (s ∩ t)
  have s_eq : s = (s \ t) ∪ (s ∩ t) := by
    exact Eq.symm (sdiff_union_inter s t)

  nth_rw 1 [s_eq]

  -- the two pieces are disjoint, so product over union splits
  have h_disj : Disjoint (s \ t) (s ∩ t) := by
    rw [disjoint_iff_inter_eq_empty]
    ext x
    simp only [mem_inter, mem_sdiff, notMem_empty, iff_false, not_and, and_imp]
    exact fun a a a_1 ↦ a

  rw [prod_union h_disj]

  -- on s \ t the `if` simplifies to `f`, on s ∩ t it simplifies to `1`
  have h1 : (∏ x ∈ s \ t, if x ∈ t then 1 else f x) = ∏ x ∈ s \ t, f x := by
    apply Finset.prod_congr rfl
    intro x hx
    simp only [ite_eq_right_iff]
    simp only [mem_sdiff] at hx
    exact fun h => False.elim (hx.2 h)
  rw [h1]

  have h2 : (∏ x ∈ s ∩ t, if x ∈ t then 1 else f x) = ∏ x ∈ s ∩ t, (1 : M) := by
    apply Finset.prod_congr rfl
    intro x hx
    simp only [ite_eq_left_iff]
    simp only [mem_inter] at hx
    exact fun h => False.elim (h hx.2)
  rw [h2]

  -- product of 1's is 1 and multiplying by 1 is neutral
  simp only [Finset.prod_const_one, mul_one]
