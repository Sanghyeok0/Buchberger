import Mathlib

variable {σ : Type*}
variable {m : MonomialOrder σ}
variable {k : Type*} [Field k]

/--
Lemma 1 (Cox–Little–O'Shea, Ch.~3 §5).

Assume that `f = ∑ A_j * g_j` is a standard representation for
the lex order with `x₁ > ⋯ > xₙ`. Then:

(i) `degX1 f ≥ degX1 (A j * g j)` whenever `A j * g j ≠ 0`.

(ii) If `N = degX1 f`, then
`cOf f = ∑_{degX1 (A j * g j) = N} cOf (A j) * cOf (g j)`.
-/
noncomputable
lemma lex_standardRep_deg
    (f : MvPolynomial σ k) (A g : Fin t → Poly)
    (hstd : IsStandardRepLex f A g) :
    (∀ j : Fin t, A j * g j ≠ 0 → degX1 f ≥ degX1 (A j * g j))
    ∧
    let N := degX1 f
    f.leadingCoeff =
      ∑ j in Finset.univ.filter
        (fun j : Fin t => degX1 (A j * g j) = N),
        (A j).leadingCoeff  * (g j).leadingCoeff  := by
  -- Proof omitted (left as an exercise, as in the book).
  sorry
