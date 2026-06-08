import Mathlib.Data.Finsupp.WellFounded

variable {M : Type*} [DecidableEq M] [LinearOrder M]

namespace Finset

/--
The colexicographic order on finite subsets.

This is the recursive definition of the order on `P_fin(M)`:
`∅ ≤ B` for all `B`; if `A` and `B` are nonempty, compare their maxima;
if the maxima are equal, erase the common maximum and compare recursively.
-/
def colexLe : Finset M → Finset M → Prop
  | A, B =>
      if hA : A = ∅ then
        True
      else if hB : B = ∅ then
        False
      else
        have ha : A.Nonempty := Finset.nonempty_of_ne_empty hA
        have hb : B.Nonempty := Finset.nonempty_of_ne_empty hB
        A.max' ha < B.max' hb ∨
          (A.max' ha = B.max' hb ∧
            colexLe (A.erase (A.max' ha)) (B.erase (B.max' hb)))
termination_by A _B => A.card
decreasing_by
  have ha : A.Nonempty := Finset.nonempty_of_ne_empty hA
  exact Finset.card_erase_lt_of_mem (Finset.max'_mem A ha)

/-- The strict colexicographic order associated to `Finset.colexLe`. -/
def colexLt (A B : Finset M) : Prop :=
  colexLe A B ∧ ¬ colexLe B A

scoped[Colex] notation:50 A:51 " ≤꜀ " B:51 =>
  Finset.colexLe A B

scoped[Colex] notation:50 A:51 " <꜀ " B:51 =>
  Finset.colexLt A B

open scoped Colex

/-- The empty finite set is below every finite set in colex order. -/
theorem colexLe_empty_left (A : Finset M) :
    (∅ : Finset M) ≤꜀ A := by
  simp [colexLe]

/-- A nonempty finite set is not below the empty finite set in colex order. -/
theorem not_colexLe_empty_right_of_ne_empty {A : Finset M}
    (hA : A ≠ ∅) :
    ¬ A ≤꜀ (∅ : Finset M) := by
  simp [colexLe, hA]

/-- Recursive characterization of `Finset.colexLe` for nonempty finite sets. -/
theorem colexLe_iff_of_ne_empty {A B : Finset M}
    (hA : A ≠ ∅) (hB : B ≠ ∅) :
    A ≤꜀ B ↔
      let ha : A.Nonempty := Finset.nonempty_of_ne_empty hA
      let hb : B.Nonempty := Finset.nonempty_of_ne_empty hB
      A.max' ha < B.max' hb ∨
        (A.max' ha = B.max' hb ∧
          A.erase (A.max' ha) ≤꜀ B.erase (B.max' hb)) := by
  rw [colexLe]
  simp only [hA, hB, ↓reduceDIte]

/-- If a nonempty finite set is below another finite set, then the latter is nonempty. -/
theorem colexLe_ne_empty_right {A B : Finset M}
    (hA : A ≠ ∅) (hAB : A ≤꜀ B) :
    B ≠ ∅ := by
  intro hB
  exact not_colexLe_empty_right_of_ne_empty hA (by simpa [hB] using hAB)

@[simp]
theorem colexLe_refl (A : Finset M) : A ≤꜀ A := by
  have hmain : ∀ n : ℕ, ∀ A : Finset M, A.card = n → A ≤꜀ A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro A hcard
        by_cases hA : A = ∅
        · simp [colexLe, hA]
        · have ha : A.Nonempty := Finset.nonempty_of_ne_empty hA
          rw [colexLe_iff_of_ne_empty hA hA]
          right
          constructor
          · rfl
          · have hlt : (A.erase (A.max' ha)).card < n := by
              simpa [hcard] using
                Finset.card_erase_lt_of_mem (Finset.max'_mem A ha)
            exact ih
              (A.erase (A.max' ha)).card
              hlt
              (A.erase (A.max' ha))
              rfl
  exact hmain A.card A rfl

theorem colexLe_trans (A B C : Finset M) :
    A ≤꜀ B → B ≤꜀ C → A ≤꜀ C := by
  have hmain :
      ∀ n : ℕ, ∀ {A B C : Finset M},
        A.card = n → A ≤꜀ B → B ≤꜀ C → A ≤꜀ C := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro A B C hcard hAB hBC
        by_cases hA : A = ∅
        · simpa [hA] using colexLe_empty_left C
        · have hB : B ≠ ∅ := colexLe_ne_empty_right hA hAB
          have hC : C ≠ ∅ := colexLe_ne_empty_right hB hBC
          have ha : A.Nonempty := Finset.nonempty_of_ne_empty hA
          have hb : B.Nonempty := Finset.nonempty_of_ne_empty hB
          have hc : C.Nonempty := Finset.nonempty_of_ne_empty hC
          have hAB' := (colexLe_iff_of_ne_empty hA hB).1 hAB
          have hBC' := (colexLe_iff_of_ne_empty hB hC).1 hBC
          rw [colexLe_iff_of_ne_empty hA hC]
          rcases hAB' with hABlt | ⟨hABeq, hABerase⟩
          · rcases hBC' with hBClt | ⟨hBCeq, _hBCerase⟩
            · left
              exact lt_trans hABlt hBClt
            · left
              simpa [hBCeq] using hABlt
          · rcases hBC' with hBClt | ⟨hBCeq, hBCerase⟩
            · left
              simpa [hABeq] using hBClt
            · right
              constructor
              · exact hABeq.trans hBCeq
              · have hlt : (A.erase (A.max' ha)).card < n := by
                  simpa [hcard] using
                    Finset.card_erase_lt_of_mem (Finset.max'_mem A ha)
                exact ih
                  (A.erase (A.max' ha)).card
                  hlt
                  rfl
                  hABerase
                  hBCerase
  intro hAB hBC
  exact hmain A.card rfl hAB hBC

theorem colexLe_antisymm (A B : Finset M) :
    A ≤꜀ B → B ≤꜀ A → A = B := by
  have hmain :
      ∀ n : ℕ, ∀ {A B : Finset M},
        A.card = n → A ≤꜀ B → B ≤꜀ A → A = B := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro A B hcard hAB hBA
        by_cases hA : A = ∅
        · by_cases hB : B = ∅
          · simp [hA, hB]
          · exfalso
            exact not_colexLe_empty_right_of_ne_empty hB (by simpa [hA] using hBA)
        · have hB : B ≠ ∅ := colexLe_ne_empty_right hA hAB
          have ha : A.Nonempty := Finset.nonempty_of_ne_empty hA
          have hb : B.Nonempty := Finset.nonempty_of_ne_empty hB
          have hAB' := (colexLe_iff_of_ne_empty hA hB).1 hAB
          have hBA' := (colexLe_iff_of_ne_empty hB hA).1 hBA
          rcases hAB' with hABlt | ⟨hABeq, hABerase⟩
          · rcases hBA' with hBAlt | ⟨hBAeq, _hBAerase⟩
            · exact False.elim (lt_asymm hABlt hBAlt)
            · have : A.max' ha < A.max' ha := by
                simpa [hBAeq] using hABlt
              exact False.elim (lt_irrefl _ this)
          · rcases hBA' with hBAlt | ⟨hBAeq, hBAerase⟩
            · have : B.max' hb < B.max' hb := by
                simpa [hABeq] using hBAlt
              exact False.elim (lt_irrefl _ this)
            · have hlt : (A.erase (A.max' ha)).card < n := by
                simpa [hcard] using
                  Finset.card_erase_lt_of_mem (Finset.max'_mem A ha)
              have hErase :
                  A.erase (A.max' ha) = B.erase (B.max' hb) :=
                ih
                  (A.erase (A.max' ha)).card
                  hlt
                  rfl
                  hABerase
                  hBAerase
              have hErase' :
                  A.erase (A.max' ha) = B.erase (A.max' ha) := by
                simpa [hABeq] using hErase
              ext x
              by_cases hx : x = A.max' ha
              · subst hx
                constructor
                · intro _hxA
                  simpa [hABeq] using Finset.max'_mem B hb
                · intro _hxB
                  exact Finset.max'_mem A ha
              · have hxiff :
                    x ∈ A.erase (A.max' ha) ↔
                      x ∈ B.erase (A.max' ha) := by
                  rw [hErase']
                simpa [Finset.mem_erase, hx] using hxiff
  intro hAB hBA
  exact hmain A.card rfl hAB hBA

theorem colexLe_total (A B : Finset M) :
    A ≤꜀ B ∨ B ≤꜀ A := by
  have hmain :
      ∀ n : ℕ, ∀ A B : Finset M,
        A.card = n → A ≤꜀ B ∨ B ≤꜀ A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro A B hcard
        by_cases hA : A = ∅
        · left
          simpa [hA] using colexLe_empty_left B
        · by_cases hB : B = ∅
          · right
            simpa [hB] using colexLe_empty_left A
          · have ha : A.Nonempty := Finset.nonempty_of_ne_empty hA
            have hb : B.Nonempty := Finset.nonempty_of_ne_empty hB
            rcases lt_trichotomy (A.max' ha) (B.max' hb) with hlt | heq | hgt
            · left
              rw [colexLe_iff_of_ne_empty hA hB]
              left
              exact hlt
            · have hltcard : (A.erase (A.max' ha)).card < n := by
                simpa [hcard] using
                  Finset.card_erase_lt_of_mem (Finset.max'_mem A ha)
              have hrec :=
                ih
                  (A.erase (A.max' ha)).card
                  hltcard
                  (A.erase (A.max' ha))
                  (B.erase (B.max' hb))
                  rfl
              rcases hrec with hABerase | hBAerase
              · left
                rw [colexLe_iff_of_ne_empty hA hB]
                right
                exact ⟨heq, hABerase⟩
              · right
                rw [colexLe_iff_of_ne_empty hB hA]
                right
                exact ⟨heq.symm, hBAerase⟩
            · right
              rw [colexLe_iff_of_ne_empty hB hA]
              left
              exact hgt
  exact hmain A.card A B rfl

/--
The characteristic finitely supported function of a finite subset.

It sends elements of `A` to `1` and all other elements to `0`.
-/
noncomputable def maxLexChar (A : Finset M) : M →₀ ℕ :=
  Finsupp.onFinset A
    (fun x => if x ∈ A then 1 else 0)
    (by
      intro x hx
      by_contra hxA
      simp [hxA] at hx)

noncomputable def maxLexLtFinsupp (A B : Finset M) : Prop :=
  Finsupp.Lex
    (fun x y : M => x > y)
    ((· < ·) : ℕ → ℕ → Prop)
    (maxLexChar A)
    (maxLexChar B)

end Finset

-- theorem maxLexLt_iff_maxLexLtFinsupp {A B : Finset M} :
--     maxLexLt A B ↔ maxLexLtFinsupp A B := by
--   constructor
--   · intro h
--     simp [maxLexLt, maxLexLtFinsupp, maxLexChar]
--     by_cases hA : A = ∅
--     · rcases h with ⟨hAB, hnBA⟩
--       have hB : B ≠ ∅ := by
--         intro hB
--         apply hnBA
--         simpa [hA, hB] using maxLexLe_empty_left (∅ : Finset M)

--       have hb : B.Nonempty := Finset.nonempty_of_ne_empty hB
--       simp [hA, Finsupp.lex_def]
--       let x := B.max' hb
--       use x
--       constructor
--       · intro y hxy
--         apply Finset.notMem_of_max_lt_coe
--         rw [Eq.symm (coe_max' hb)]
--         exact WithBot.coe_lt_coe.mpr hxy
--       · have : x ∈ B := by exact max'_mem B hb
--         rw [ite_cond_eq_true]
--         · exact Nat.one_pos
--         · exact eq_true this
--     · simp [Finsupp.lex_def]
--       rcases h with ⟨hAB, hnBA⟩
--       have hB : B ≠ ∅ := by
--         intro hB
--         rw [hB] at hnBA
--         apply hnBA
--         exact maxLexLe_empty_left A

--       let x := B.max' hb
--       use x



/-- Finite subsets equipped with the colexicographic order. -/
def FinsetColex (M : Type*) :=
  Finset M

/-- Identity equivalence from `Finset M` to `FinsetColex M`. -/
@[match_pattern]
def toFinsetColex : Finset M ≃ FinsetColex M :=
  Equiv.refl _

/-- Identity equivalence from `FinsetColex M` to `Finset M`. -/
@[match_pattern]
def ofFinsetColex : FinsetColex M ≃ Finset M :=
  Equiv.refl _

@[simp]
theorem ofFinsetColex_toFinsetColex (A : Finset M) :
    ofFinsetColex (toFinsetColex A) = A :=
  rfl

@[simp]
theorem toFinsetColex_ofFinsetColex (A : FinsetColex M) :
    toFinsetColex (ofFinsetColex A) = A :=
  rfl

namespace FinsetColex

variable {M : Type*} [DecidableEq M] [LinearOrder M]

instance : LE (FinsetColex M) where
  le A B := Finset.colexLe (ofFinsetColex A) (ofFinsetColex B)

instance : LT (FinsetColex M) where
  lt A B := Finset.colexLt (ofFinsetColex A) (ofFinsetColex B)

end FinsetColex
