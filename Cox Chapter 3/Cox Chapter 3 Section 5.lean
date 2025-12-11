import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.Finset.Basic

variable {k : Type*} [Field k]
variable {n : ℕ}

/-- Coefficient ring `k[x₂, …, xₙ]` (abstractly). -/
abbrev CoeffRing : Type _ := MvPolynomial (Fin n) k

/-- The polynomial ring `k[x₁, …, xₙ]` viewed as
polynomials in `x₁` with coefficients in `k[x₂, …, xₙ]`. -/
abbrev Poly : Type _ := Polynomial (CoeffRing)

/-- `deg(f, x₁)` from the book: the degree of `f` in the variable `x₁`. -/
noncomputable
def degX1 (f : Poly) : ℕ :=
  f.natDegree

/-- `c_f` from the book: the coefficient of the highest power of `x₁`. -/
noncomputable
def cOf (f : Poly) : CoeffRing :=
  f.leadingCoeff

variable {t : ℕ}

/-- `IsStandardRepLex f A g` means that
`f = ∑₍j₎ A j * g j` is a standard representation for the
lexicographic order with `x₁ > ⋯ > xₙ`.

Here we keep this as an abstract predicate; its concrete
definition (in terms of leading terms, etc.) can be filled
in elsewhere. -/
def IsStandardRepLex
    (f : Poly) (A g : Fin t → Poly) : Prop :=
  True

/--
Lemma 1 (Cox–Little–O'Shea, Ch.~3 §5).

Assume that `f = ∑ A_j * g_j` is a standard representation for
the lex order with `x₁ > ⋯ > xₙ`. Then:

(i) `degX1 f ≥ degX1 (A j * g j)` whenever `A j * g j ≠ 0`.

(ii) If `N = degX1 f`, then
`cOf f = ∑_{degX1 (A j * g j) = N} cOf (A j) * cOf (g j)`.
-/
noncomputable
lemma lex_standardRep_deg_and_cOf
    (f : Poly) (A g : Fin t → Poly)
    (hstd : IsStandardRepLex f A g) :
    (∀ j : Fin t, A j * g j ≠ 0 → degX1 f ≥ degX1 (A j * g j))
    ∧
    let N := degX1 f
    in
    cOf f =
      ∑ j in Finset.univ.filter
        (fun j : Fin t => degX1 (A j * g j) = N),
        cOf (A j) * cOf (g j) := by
  -- Proof omitted (left as an exercise, as in the book).
  sorry
