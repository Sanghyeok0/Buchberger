import Mathlib.Data.Finsupp.WellFounded

/-!
## The max-lex order on finite subsets

This section defines the max-lexicographic order on `P_fin(M)`, represented
in Lean by `Finset M`.

Instead of using the recursive definition from Becker--Weispfenning--Kredel
as the definitional equation, we define the strict order by transporting
finite subsets to their characteristic finitely supported functions and
using `Finsupp.Lex`.

The recursive definition from the book can later be recovered as a theorem.
-/

noncomputable section

namespace Finset

variable {M : Type*} [DecidableEq M] [LinearOrder M]

/--
The characteristic finitely supported function of a finite subset.

It sends elements of `A` to `1` and all other elements to `0`.
-/
def maxLexChar (A : Finset M) : M →₀ ℕ :=
  Finsupp.onFinset A
    (fun x => if x ∈ A then 1 else 0)
    (by
      intro x hx
      by_contra hxA
      simp [hxA] at hx)

/--
The strict max-lexicographic order on finite subsets.

The order compares characteristic finitely supported functions
lexicographically from larger elements of `M` to smaller elements.
-/
def maxLexLt (A B : Finset M) : Prop :=
  Finsupp.Lex
    (fun x y : M => x > y)
    ((· < ·) : ℕ → ℕ → Prop)
    (maxLexChar A)
    (maxLexChar B)

/--
The non-strict max-lexicographic order on finite subsets.
-/
def maxLexLe (A B : Finset M) : Prop :=
  A = B ∨ maxLexLt A B

scoped[MaxLex] notation:50 A:51 " ≤ₘₗ " B:51 =>
  Finset.maxLexLe A B

scoped[MaxLex] notation:50 A:51 " <ₘₗ " B:51 =>
  Finset.maxLexLt A B

open scoped MaxLex

omit [LinearOrder M] in
@[simp]
theorem maxLexChar_apply (A : Finset M) (x : M) :
    maxLexChar A x = if x ∈ A then 1 else 0 := by
  by_cases hx : x ∈ A <;> simp only [maxLexChar, Finsupp.onFinset_apply, hx, ↓reduceIte]

omit [LinearOrder M] in
theorem mem_iff_of_not_mem_symmDiff {A B : Finset M} {x : M}
    (hx : x ∉ symmDiff A B) :
    x ∈ A ↔ x ∈ B := by
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B
  · exact ⟨fun _ => hB, fun _ => hA⟩
  · exfalso
    exact hx (by simp [Finset.mem_symmDiff, hA, hB])
  · exfalso
    exact hx (by simp [Finset.mem_symmDiff, hA, hB])
  · exact ⟨fun h => False.elim (hA h), fun h => False.elim (hB h)⟩

theorem maxLexLt_of_max_symmDiff_mem_right {A B : Finset M}
    (hD : (symmDiff A B).Nonempty)
    (hxB : (symmDiff A B).max' hD ∈ B) :
    A <ₘₗ B := by
  classical
  let x := (symmDiff A B).max' hD
  have hxD : x ∈ symmDiff A B := by
    exact Finset.max'_mem (symmDiff A B) hD
  have hxA : x ∉ A := by
    intro hxA
    have hx_notD : x ∉ symmDiff A B := by
      simp? [Finset.mem_symmDiff, hxA] says
        simp only [mem_symmDiff, hxA, true_and, not_true_eq_false, and_false, or_false, Decidable.not_not]
      exact mem_def.mpr hxB
    exact hx_notD hxD
  unfold maxLexLt Finsupp.Lex
  change
    Pi.Lex
      (fun x y : M => x > y)
      (fun {_ : M} => ((· < ·) : ℕ → ℕ → Prop))
      (maxLexChar A)
      (maxLexChar B)
  refine ⟨x, ?_, ?_⟩
  · intro y hy
    have hy_notD : y ∉ symmDiff A B := by
      intro hyD
      have hy_le_x : y ≤ x := by
        exact Finset.le_max' (symmDiff A B) y hyD
      exact (not_lt_of_ge hy_le_x) hy
    have hyiff : y ∈ A ↔ y ∈ B :=
      mem_iff_of_not_mem_symmDiff hy_notD
    by_cases hyA : y ∈ A
    · have hyB : y ∈ B := hyiff.mp hyA
      simp [hyA, hyB]
    · have hyB : y ∉ B := by
        intro hyB
        exact hyA (hyiff.mpr hyB)
      simp [hyA, hyB]
  · have hxB' : x ∈ B := hxB
    simp only [maxLexChar_apply, hxA, ↓reduceIte, hxB', zero_lt_one]

theorem maxLexLt_of_max_symmDiff_mem_left {A B : Finset M}
    (hD : (symmDiff A B).Nonempty)
    (hxA : (symmDiff A B).max' hD ∈ A) :
    B <ₘₗ A := by
  have hD' : (symmDiff B A).Nonempty := by
    simpa only [symmDiff_comm, symmDiff_nonempty] using hD
  exact maxLexLt_of_max_symmDiff_mem_right
    (A := B) (B := A) hD' (by
      simpa only [symmDiff_comm] using hxA)

/--
The empty finite set is strictly below every nonempty finite set in the
max-lexicographic order.
-/
theorem maxLexLt_empty_left_of_ne_empty {A : Finset M}
    (hA : A ≠ ∅) :
    (∅ : Finset M) <ₘₗ A := by
  classical
  have ha : A.Nonempty := Finset.nonempty_of_ne_empty hA
  unfold maxLexLt
  change
    Pi.Lex
      (fun x y : M => x > y)
      (fun {_ : M} => ((· < ·) : ℕ → ℕ → Prop))
      (maxLexChar (∅ : Finset M))
      (maxLexChar A)
  refine ⟨A.max' ha, ?_, ?_⟩
  · intro y hy
    have hy_not_mem : y ∉ A := by
      intro hyA
      have hy_le : y ≤ A.max' ha :=
        Finset.le_max' A y hyA
      exact (not_lt_of_ge hy_le) hy
    simp [maxLexChar, hy_not_mem]
  · simp [maxLexChar, Finset.max'_mem A ha]

/--
No finite set is strictly below the empty finite set in the max-lexicographic
order.
-/
theorem not_maxLexLt_empty_right (A : Finset M) :
    ¬ A <ₘₗ (∅ : Finset M) := by
  classical
  intro h
  unfold maxLexLt at h
  change
    Pi.Lex
      (fun x y : M => x > y)
      (fun {_ : M} => ((· < ·) : ℕ → ℕ → Prop))
      (maxLexChar A)
      (maxLexChar (∅ : Finset M)) at h
  rcases h with ⟨x, _hx_eq, hx_lt⟩
  simp [maxLexChar] at hx_lt

/-- The empty finite set is below every finite set. -/
theorem maxLexLe_empty_left (A : Finset M) :
    (∅ : Finset M) ≤ₘₗ A := by
  by_cases hA : A = ∅
  · exact Or.inl hA.symm
  · exact Or.inr (maxLexLt_empty_left_of_ne_empty hA)

/-- A nonempty finite set is not below the empty finite set. -/
theorem not_maxLexLe_empty_right_of_ne_empty {A : Finset M}
    (hA : A ≠ ∅) :
    ¬ A ≤ₘₗ (∅ : Finset M) := by
  intro h
  rcases h with h_eq | h_lt
  · exact hA h_eq
  · exact not_maxLexLt_empty_right A h_lt

/-- If a nonempty finite set is below another finite set, then the latter is nonempty. -/
theorem maxLexLe_ne_empty_right {A B : Finset M}
    (hA : A ≠ ∅) (hAB : A ≤ₘₗ B) :
    B ≠ ∅ := by
  intro hB
  exact not_maxLexLe_empty_right_of_ne_empty hA (by simpa [hB] using hAB)

theorem maxLexLt_asymm {A B : Finset M}
    (hAB : A <ₘₗ B) :
    ¬ B <ₘₗ A := by
  intro hBA
  unfold maxLexLt Finsupp.Lex at hAB hBA
  change
    Pi.Lex
      (fun x y : M => x > y)
      (fun {_ : M} => ((· < ·) : ℕ → ℕ → Prop))
      (maxLexChar A)
      (maxLexChar B) at hAB
  change
    Pi.Lex
      (fun x y : M => x > y)
      (fun {_ : M} => ((· < ·) : ℕ → ℕ → Prop))
      (maxLexChar B)
      (maxLexChar A) at hBA

  rcases hAB with ⟨i, hAB_eq, hAB_lt⟩
  rcases hBA with ⟨j, hBA_eq, hBA_lt⟩

  rcases lt_trichotomy i j with hij | hij | hji
  · have hij_eq : maxLexChar A j = maxLexChar B j :=
      hAB_eq j hij
    have : maxLexChar B j < maxLexChar B j := by
      simp only [maxLexChar_apply, lt_self_iff_false, hij_eq] at hBA_lt
    exact (lt_irrefl _ this)
  · subst j
    exact lt_asymm hAB_lt hBA_lt
  · have hji_eq : maxLexChar B i = maxLexChar A i :=
      hBA_eq i hji
    have : maxLexChar A i < maxLexChar A i := by
      simp only [maxLexChar_apply, lt_self_iff_false, hji_eq] at hAB_lt
    exact (lt_irrefl _ this)

/--
Lemma 4.67, reflexivity part.

The induced max-lexicographic order `Finset.maxLexLe` on finite subsets is
reflexive: every finite subset is below itself.
-/
theorem maxLexLe_refl :
    ∀ A : Finset M, A ≤ₘₗ A := by
  intro A
  exact Or.inl rfl

/--
Transitivity of the strict max-lexicographic order.

This is proved directly from the definition of `Finsupp.Lex`.
-/
theorem maxLexLt_trans {A B C : Finset M}
    (hAB : A <ₘₗ B) (hBC : B <ₘₗ C) :
    A <ₘₗ C := by
  unfold maxLexLt Finsupp.Lex at *
  change
    Pi.Lex
      (fun x y : M => x > y)
      (fun {_ : M} => ((· < ·) : ℕ → ℕ → Prop))
      (maxLexChar A)
      (maxLexChar B) at hAB
  change
    Pi.Lex
      (fun x y : M => x > y)
      (fun {_ : M} => ((· < ·) : ℕ → ℕ → Prop))
      (maxLexChar B)
      (maxLexChar C) at hBC
  change
    Pi.Lex
      (fun x y : M => x > y)
      (fun {_ : M} => ((· < ·) : ℕ → ℕ → Prop))
      (maxLexChar A)
      (maxLexChar C)

  rcases hAB with ⟨i, hAB_eq, hAB_lt⟩
  rcases hBC with ⟨j, hBC_eq, hBC_lt⟩

  rcases lt_trichotomy i j with hij | hij | hji
  · -- Case `i < j`: compare at `j`.
    refine ⟨j, ?_, ?_⟩
    · intro k hk
      have hABk : maxLexChar A k = maxLexChar B k :=
        hAB_eq k (lt_trans hij hk)
      have hBCk : maxLexChar B k = maxLexChar C k :=
        hBC_eq k hk
      exact hABk.trans hBCk
    · have hABj : maxLexChar A j = maxLexChar B j :=
        hAB_eq j hij
      exact lt_of_eq_of_lt hABj hBC_lt

  · -- Case `i = j`: compare at the common index.
    subst hij
    refine ⟨i, ?_, ?_⟩
    · intro k hk
      have hABk : maxLexChar A k = maxLexChar B k :=
        hAB_eq k hk
      have hBCk : maxLexChar B k = maxLexChar C k :=
        hBC_eq k hk
      exact hABk.trans hBCk
    · exact lt_trans hAB_lt hBC_lt

  · -- Case `j < i`: compare at `i`.
    refine ⟨i, ?_, ?_⟩
    · intro k hk
      have hABk : maxLexChar A k = maxLexChar B k :=
        hAB_eq k hk
      have hBCk : maxLexChar B k = maxLexChar C k :=
        hBC_eq k (lt_trans hji hk)
      exact hABk.trans hBCk
    · have hBCi : maxLexChar B i = maxLexChar C i :=
        hBC_eq i hji
      exact lt_of_lt_of_eq hAB_lt hBCi

/--
Lemma 4.67, transitivity part.

The induced max-lexicographic order `Finset.maxLexLe` on finite subsets is
transitive: if `A ≤ₘₗ B` and `B ≤ₘₗ C`, then `A ≤ₘₗ C`.
-/
theorem maxLexLe_trans :
    ∀ {A B C : Finset M}, A ≤ₘₗ B → B ≤ₘₗ C → A ≤ₘₗ C := by
  intro A B C hAB hBC
  rcases hAB with hAB_eq | hAB_lt
  · subst hAB_eq
    exact hBC
  rcases hBC with hBC_eq | hBC_lt
  · subst hBC_eq
    exact Or.inr hAB_lt
  · exact Or.inr (maxLexLt_trans hAB_lt hBC_lt)

/--
Lemma 4.67, antisymmetry part.

The induced max-lexicographic order `Finset.maxLexLe` on finite subsets is
antisymmetric: if `A ≤ₘₗ B` and `B ≤ₘₗ A`, then `A = B`.
-/
theorem maxLexLe_antisymm :
    ∀ {A B : Finset M}, A ≤ₘₗ B → B ≤ₘₗ A → A = B := by
  intro A B hAB hBA
  rcases hAB with hAB_eq | hAB_lt
  · exact hAB_eq
  rcases hBA with hBA_eq | hBA_lt
  · exact hBA_eq.symm
  · exact False.elim ((maxLexLt_asymm hAB_lt) hBA_lt)

omit [LinearOrder M] in
theorem symmDiff_nonempty_of_ne {A B : Finset M}
    (hAB : A ≠ B) :
    (symmDiff A B).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hD
  apply hAB
  ext x
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B
  · simp only [hxA, hxB]
  · have hxD : x ∈ symmDiff A B := by
      simp [Finset.mem_symmDiff, hxA, hxB]
    have : False := by
      simp only [hD, notMem_empty] at hxD
    exact False.elim this
  · have hxD : x ∈ symmDiff A B := by
      simp [Finset.mem_symmDiff, hxA, hxB]
    have : False := by
      simp only [hD, notMem_empty] at hxD
    exact False.elim this
  · simp only [hxA, hxB]

/--
Lemma 4.67, connexity part.

The induced max-lexicographic order `Finset.maxLexLe` on finite subsets is
connex: any two finite subsets are comparable, i.e. for any `A` and `B`,
either `A ≤ₘₗ B` or `B ≤ₘₗ A`.
-/
theorem maxLexLe_total :
    ∀ A B : Finset M, A ≤ₘₗ B ∨ B ≤ₘₗ A := by
  intro A B
  by_cases hAB : A = B
  · left
    exact Or.inl hAB
  · have hD : (symmDiff A B).Nonempty :=
      symmDiff_nonempty_of_ne hAB
    let x := (symmDiff A B).max' hD
    have hxD : x ∈ symmDiff A B := by
      exact Finset.max'_mem (symmDiff A B) hD
    by_cases hxB : x ∈ B
    · left
      exact Or.inr (maxLexLt_of_max_symmDiff_mem_right hD hxB)
    · right
      have hxA : x ∈ A := by
        by_contra hxA
        have hx_notD : x ∉ symmDiff A B := by
          simp [Finset.mem_symmDiff, hxA, hxB]
        exact hx_notD hxD
      exact Or.inr (maxLexLt_of_max_symmDiff_mem_left hD hxA)

/--
Lemma 4.67.

The relation `Finset.maxLexLe` makes `P_fin(M)` into an ordered set
in the terminology of the book. In Lean's relation-level terminology,
this means that `Finset.maxLexLe` is an `IsLinearOrder`.
-/
theorem maxLexLe_isLinearOrder :
    IsLinearOrder (Finset M)
      (Finset.maxLexLe : Finset M → Finset M → Prop) where
  refl := maxLexLe_refl
  trans := by
    intro A B C hAB hBC
    exact maxLexLe_trans hAB hBC
  antisymm := by
    intro A B hAB hBA
    exact maxLexLe_antisymm hAB hBA
  total := maxLexLe_total

/--
Theorem 4.69.

If `M` is well-ordered, then the finite subsets of `M`, equipped with the
max-lexicographic strict order associated to `Finset.maxLexLe`, are also
well-founded.

In the terminology of Becker--Weispfenning--Kredel, if `(M, ≤)` is a
well-ordered set, then so is `(P_fin(M), ≤')`.
-/
theorem maxLexLt_wellFounded [WellFoundedLT M] :
    WellFounded (Finset.maxLexLt : Finset M → Finset M → Prop) := by
  classical

  haveI : Std.Trichotomous (fun x y : M => x > y) :=
    { trichotomous := by
        intro a b hab hba
        exact le_antisymm (le_of_not_gt hab) (le_of_not_gt hba)
    }

  have hlex :
      WellFounded
        (Finsupp.Lex
          (fun x y : M => x > y)
          ((· < ·) : ℕ → ℕ → Prop) :
            (M →₀ ℕ) → (M →₀ ℕ) → Prop) := by
    refine Finsupp.Lex.wellFounded'
      (r := fun x y : M => x > y)
      (s := ((· < ·) : ℕ → ℕ → Prop))
      ?hbot
      ?hs
      ?hr
    · intro n
      simp only [not_lt_zero, not_false_eq_true]
    · exact (inferInstance : WellFoundedLT ℕ).wf
    · change WellFounded ((· < ·) : M → M → Prop)
      exact (inferInstance : WellFoundedLT M).wf

  unfold Finset.maxLexLt
  exact InvImage.wf Finset.maxLexChar hlex

end Finset

end noncomputable section


-- /-!
-- ## The max-lex order on finite subsets

-- This is the recursive order on `P_fin(M)` used in Becker--Weispfenning--Kredel,
-- Chapter 4, Section 4.4.

-- -/

-- /--
-- The max-lexicographic order on finite subsets.

-- This is the relation `≤'` on `P_fin(M)` defined recursively by:
-- * `∅ ≤' B` for every `B`;
-- * if `A ≠ ∅`, then `A ≤' B` iff `B ≠ ∅` and either
--   `max A < max B`, or `max A = max B` and
--   `A \ {max A} ≤' B \ {max B}`.
-- -/
-- def maxLexLe_old : Finset M → Finset M → Prop
--   | A, B =>
--       if hA : A = ∅ then
--         True
--       else if hB : B = ∅ then
--         False
--       else
--         have ha : A.Nonempty := Finset.nonempty_of_ne_empty hA
--         have hb : B.Nonempty := Finset.nonempty_of_ne_empty hB
--         A.max' ha < B.max' hb ∨
--           (A.max' ha = B.max' hb ∧
--             maxLexLe_old (A.erase (A.max' ha)) (B.erase (B.max' hb)))
-- termination_by A _B => A.card
-- decreasing_by
--   have ha : A.Nonempty := Finset.nonempty_of_ne_empty hA
--   exact Finset.card_erase_lt_of_mem (Finset.max'_mem A ha)

-- /--
-- The strict order associated to `Finset.maxLexLe`.
-- -/
-- def maxLexLt_old (A B : Finset M) : Prop :=
--   maxLexLe_old A B ∧ ¬ maxLexLe_old B A
