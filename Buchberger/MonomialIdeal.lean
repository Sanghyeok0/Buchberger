import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

variable {σ R : Type*} [CommSemiring R] --[EmptyCollection σ]
variable {m : MonomialOrder σ}

namespace MvPolynomial

def monomialIdeal (s : Set (σ →₀ ℕ)) : Ideal (MvPolynomial σ R) :=
  Ideal.span ((fun s => monomial s (1 : R)) '' s)

/--
Lemma 2. Let I = ⟨x^α | α ∈ A⟩ be a monomial ideal. Then a monomial x^β lies in I if and only if
x^β is divisible by some x^α for α in A, i.e. there exists α ∈ A such that α ≤ β.
-/

lemma mem_monomialIdeal_iff_divisible {A : Set (σ →₀ ℕ)} {β : σ →₀ ℕ} [DecidableEq R] [Nontrivial R] :
  (monomial β (1 : R)) ∈ monomialIdeal A ↔ ∃ α ∈ A, α ≤ β := by
  constructor
  · intro h
    unfold monomialIdeal at h
    rw [mem_ideal_span_monomial_image] at h
    have supp_eq : (monomial β (1 : R)).support = {β} := by
      rw [MvPolynomial.support_monomial]
      have : 0 ≠ (1 : R) := by exact zero_ne_one' R
      exact if_neg (id (Ne.symm this))
    specialize h β (by simp [supp_eq])
    exact h
  · intro h
    unfold monomialIdeal
    rw [mem_ideal_span_monomial_image]
    have supp_eq : (monomial β (1 : R)).support = {β} := by
      rw [MvPolynomial.support_monomial]
      have : 0 ≠ (1 : R) := by exact zero_ne_one' R
      exact if_neg (id (Ne.symm this))
    intros xi hxi
    rw [supp_eq, Finset.mem_singleton] at hxi
    subst hxi
    exact h

/-
Theorem 5 (Dickson’s Lemma). Let
 I = ⟨ x^α | α ∈ A ⟩ ⊆ k[x₁, …, xₙ]
be a monomial ideal. Then there exists a finite subset s ⊆ A such that
 I = ⟨ x^α | α ∈ s ⟩.
In other words, every monomial ideal has a finite basis.
-/

variable [Fintype σ] in
theorem Dickson_lemma (A : Set (σ →₀ ℕ)) :
  ∃ (s : Finset (σ →₀ ℕ)), s.toSet ⊆ A ∧ (@monomialIdeal σ R _ A = monomialIdeal ↑s ) := by sorry
--   by_cases h : Fintype.card σ = 0
--   · have dom_empty : IsEmpty σ := Fintype.card_eq_zero_iff.mp h
--     have this : A = ∅ := by apply?

--     use ∅
--     simp
--     ext p
--     rw [monomialIdeal, monomialIdeal]
--     simp
--     by_cases p_eq_zero : p = 0
--     · sorry
--     · simp
--     sorry
--   · -- Inductive step (Fintype.card σ > 0)
--     sorry

variable [Fintype σ] [EmptyCollection σ] in
theorem Dickson_lemma₀ (A : Set (σ →₀ ℕ)) :
  ∃ (s : Finset (σ →₀ ℕ)), s.toSet ⊆ A ∧ (@monomialIdeal σ R _ A = monomialIdeal ↑s ) := by
  induction (Fintype.card σ) using Nat.strongRecOn with
  | ind n IH =>
    obtain _ | n := n
    · refine ⟨∅, by simp, ?_⟩
      ext p
      simp only [Finset.coe_empty]
      constructor
      · intro h
        sorry
      · intro h
        rw [monomialIdeal] at h
        simp only [Set.image_empty, Ideal.span_empty, Ideal.mem_bot] at h
        rw [h, monomialIdeal]
        exact Submodule.zero_mem (Ideal.span ((fun s => (monomial s) 1) '' A))
    · sorry

-- variable [Fintype σ] in
-- theorem Dickson_lemma₉ (A : Set (σ →₀ ℕ)) :
--   ∃ (s : Finset (σ →₀ ℕ)), s.toSet ⊆ A ∧ (@monomialIdeal σ R _ A = monomialIdeal ↑s ) := by
--   induction (Fintype.card σ) using Nat.strongRecOn with
--   | ind n IH =>
--     obtain _ | n := n
--     · refine ⟨∅, by simp, ?_⟩
--       ext p
--       simp only [Finset.coe_empty]
--       constructor
--       · intro h
--         have : IsEmpty σ := by
--           have h : Fintype.card (PLift σ) = 0 := by rfl -- simp_all does not finish the proof
--           exact instIsEmpty (PLift σ)
--         have : A = ∅ ∨ A = {0} := by
--           apply Set.eq_empty_or_singleton_of_isEmpty
--           intro x
--           apply Finsupp.ext
--           intro a
--           exact IsEmpty.elim this a
--         cases this with
--         | inl h => simp [h]
--         | inr h =>
--           simp only [h, monomialIdeal, Set.image_singleton, Ideal.span_singleton_one, eq_true_iff,
--             Submodule.top_eq_top, and_true]
--           exact trivial
--       · intro h
--         rw [monomialIdeal] at h
--         simp only [Set.image_empty, Ideal.span_empty, Ideal.mem_bot] at h
--         rw [h, monomialIdeal]
--         exact Submodule.zero_mem (Ideal.span ((fun s => (monomial s) 1) '' A))
--     · sorry

-- variable [Fintype σ] in
-- theorem Dickson_lemma₀ (A : Set (σ →₀ ℕ)) :
--   ∃ (s : Finset (σ →₀ ℕ)), s.toSet ⊆ A ∧ (@monomialIdeal σ R _ A = monomialIdeal ↑s ) := by
--   let n := Fintype.card σ
--   induction' n with n ih
--   · have : n = 0 := by apply?
--   · done
--   | zero =>
--     have : n = 0 := by apply?
--     refine ⟨∅, by simp, ?_⟩
--     have : Fintype.card σ = 0 := by apply?
--     have : IsEmpty σ := by assumption
--     have : A = ∅ := by sorry
--     simp_all
--   | succ n IH => sorry

-- variable [Fintype σ] in
-- theorem Dickson_lemma₁ (A : Set (σ →₀ ℕ)) :
--   ∃ (s : Finset (σ →₀ ℕ)), s.toSet ⊆ A ∧ (@monomialIdeal σ R _ A = monomialIdeal ↑s ) := by
--   let n := Fintype.card σ
--   induction n with
--   | zero =>
--     have : Fintype.card σ = 0 := by sorry
--     refine ⟨∅, by simp, ?_⟩
--     have : Fintype.card σ = 0 := by sorry
--     have : IsEmpty σ := by assumption
--     have : A = ∅ := by sorry
--     simp_all
--   | succ n IH => sorry

variable [Fintype σ] in
theorem Dickson_lemma₂ (A : Set (σ →₀ ℕ)) :
  ∃ (s : Finset (σ →₀ ℕ)), s.toSet ⊆ A ∧ (@monomialIdeal σ R _ A = monomialIdeal ↑s ) := by
  let n := Fintype.card σ
  let S : Finset σ := Finset.univ
  -- induction' n using Nat.strong_induction_on with n ih
  induction S using Finset.induction with
  | empty => sorry
  | insert _ _ => sorry
  sorry

-- variable [Fintype σ] in
-- theorem Dickson_lemma₃ (A : Set (σ →₀ ℕ)) :
--   ∃ (s : Finset (σ →₀ ℕ)), s.toSet ⊆ A ∧ (@monomialIdeal σ R _ A = monomialIdeal ↑s ) := by
--   induction (Fintype.card σ) using Nat.strongRecOn with
--   | ind n IH =>
--     obtain hn | hn := Nat.eq_zero_or_pos n
--     · -- Base case: n = 0 (card σ = 0)
--       refine ⟨∅, by simp, ?_⟩
--       have : IsEmpty σ := by
--         have h : Fintype.card (PLift σ) = 0 := by simp_all;
--       have : A = ∅ ∨ A = {0} := by
--         apply Set.eq_empty_or_singleton_of_isEmpty
--         intro x
--         apply Finsupp.ext
--         intro a
--         exact IsEmpty.elim this a
--       cases this with
--       | inl h => simp [h]
--       | inr h =>
--         simp only [h, monomialIdeal, Set.image_singleton, Ideal.span_singleton_one,
--           eq_true_iff, Submodule.top_eq_top, and_true]
