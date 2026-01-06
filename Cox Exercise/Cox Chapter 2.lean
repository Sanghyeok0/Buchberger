import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Div

open MvPolynomial Polynomial

variable {k : Type*} [Field k]

noncomputable section

/-
Definition 1.

Let m be a positive integer. Suppose that we have a point (a,b) ∈ V(f)
and let L be the line through (a,b). Then L meets V(f) with multiplicity m
at (a,b) if L can be parametrized as

  x = a + c t,   y = b + d t

so that t = 0 is a root of multiplicity m of g(t) = f(a + c t, b + d t).
-/

/-- Evaluate the bivariate polynomial `f` at the point `(a, b)`. -/
def evalAtPoint
    (f : MvPolynomial (Fin 2) k) (a b : k) : k :=
  MvPolynomial.eval₂ (RingHom.id k)
    (fun i : Fin 2 =>
      match i with
      | 0 => a
      | 1 => b) f

/-- The point `(a, b)` lies on the affine plane curve `V(f)`. -/
def OnCurve
    (f : MvPolynomial (Fin 2) k) (a b : k) : Prop :=
  evalAtPoint f a b = 0

/-- Restrict the bivariate polynomial `f` to the line

`x = a + c t,  y = b + d t`

through `(a, b)` in direction `(c, d)`, obtaining a univariate polynomial
`g(t) = f(a + c t, b + d t)`. -/
def restrictToLine
    (f : MvPolynomial (Fin 2) k)
    (a b c d : k) : Polynomial k :=
  MvPolynomial.aeval
    (fun i : Fin 2 =>
      match i with
      | 0 =>
        Polynomial.C a + Polynomial.C c * Polynomial.X
      | 1 =>
        Polynomial.C b + Polynomial.C d * Polynomial.X) f

/-- The multiplicity of the root `t = 0` of
`g(t) = f(a + c t, b + d t)`. -/
def lineMultiplicity
    (f : MvPolynomial (Fin 2) k)
    (a b c d : k) : ℕ :=
  Polynomial.rootMultiplicity 0 (restrictToLine f a b c d)

/-- Definition 1: the line through `(a, b)` with direction `(c, d)` meets `V(f)`
with multiplicity `m` at `(a, b)` iff `t = 0` is a root of multiplicity `m`
of `g(t) = f(a + c t, b + d t)`. -/
def MeetsWithMultiplicity
    (f : MvPolynomial (Fin 2) k)
    (a b c d : k) (m : ℕ) : Prop :=
  0 < m ∧ lineMultiplicity f a b c d = m

/-- Variant using “multiplicity ≥ m”. This will be used for Proposition 2
and the definition of tangent line. -/
def MeetsWithMultiplicityAtLeast
    (f : MvPolynomial (Fin 2) k)
    (a b c d : k) (m : ℕ) : Prop :=
  m ≤ lineMultiplicity f a b c d

/-
Gradient of f at (a, b):  ∇f(a, b) = (∂f/∂x(a, b), ∂f/∂y(a, b)).
-/

/-- The gradient `∇ f(a, b)` of `f` at `(a, b)`.

Here `0` and `1` index the variables `x` and `y` respectively. -/
def gradAt
    (f : MvPolynomial (Fin 2) k)
    (a b : k) : k × k :=
  ( evalAtPoint (MvPolynomial.pderiv 0 f) a b
  , evalAtPoint (MvPolynomial.pderiv 1 f) a b )

/-- Proposition 2 (i).

If `∇ f (a,b) ≠ (0,0)` and `(a,b) ∈ V(f)`, then there is a unique line
through `(a,b)` that meets `V(f)` with multiplicity ≥ 2.
-/
theorem existsUnique_line_meetsWithMult_two_of_gradAt_ne_zero
    (f : MvPolynomial (Fin 2) k) (a b : k)
    (hV : OnCurve f a b)
    (hgrad : gradAt f a b ≠ (0, 0)) :
    ∃! cd : k × k,
      cd ≠ (0, 0) ∧
      MeetsWithMultiplicityAtLeast f a b cd.1 cd.2 2 := by
  sorry

/-- Proposition 2 (ii).

If `∇ f (a,b) = (0,0)` and `(a,b) ∈ V(f)`, then **every** line through `(a,b)`
meets `V(f)` with multiplicity ≥ 2.
-/
theorem all_lines_meetWithMult_two_of_gradAt_eq_zero
    (f : MvPolynomial (Fin 2) k) (a b : k)
    (hV : OnCurve f a b)
    (hgrad : gradAt f a b = (0, 0)) :
    ∀ cd : k × k,
      cd ≠ (0, 0) →
      MeetsWithMultiplicityAtLeast f a b cd.1 cd.2 2 := by
  sorry


/-
Definition 3.

Let f ∈ k[x,y] and let (a,b) ∈ V(f).

(i) If ∇f(a,b) ≠ (0,0), then the tangent line of V(f) at (a,b) is the
    unique line through (a,b) which meets V(f) with multiplicity ≥ 2.
    We say that (a,b) is a nonsingular point of V(f).

(ii) If ∇f(a,b) = (0,0), then we say that (a,b) is a singular point of V(f).
-/

/-- The line through `(a, b)` in direction `(c, d)` is the tangent line
of `V(f)` at `(a, b)`. -/
def IsTangentLine
    (f : MvPolynomial (Fin 2) k)
    (a b c d : k) : Prop :=
  OnCurve f a b ∧
  gradAt f a b ≠ (0, 0) ∧
  (c, d) ≠ (0, 0) ∧
  MeetsWithMultiplicityAtLeast f a b c d 2 ∧
  ∀ cd' : k × k,
    cd' ≠ (0, 0) →
    MeetsWithMultiplicityAtLeast f a b cd'.1 cd'.2 2 →
    cd' = (c, d)

/-- `(a, b)` is a nonsingular point of the plane curve `V(f)`. -/
def IsNonsingularPoint
    (f : MvPolynomial (Fin 2) k)
    (a b : k) : Prop :=
  OnCurve f a b ∧ gradAt f a b ≠ (0, 0)

/-- `(a, b)` is a singular point of the plane curve `V(f)`. -/
def IsSingularPoint
    (f : MvPolynomial (Fin 2) k)
    (a b : k) : Prop :=
  OnCurve f a b ∧ gradAt f a b = (0, 0)

/-
Definition 4.

Given a polynomial F ∈ k[x,y,t], fix a scalar t ∈ k. Then the variety
in k² defined by F(x,y,t) = 0 is denoted V(Fₜ), and the family of curves
determined by F consists of the varieties V(Fₜ) as t varies over k.
-/

/-- For a polynomial `F(x,y,t)` describing a family of plane curves,
`paramCurve F t` is the specialized polynomial in `x,y` obtained by fixing
the parameter `t`. This corresponds to `F_t` in the book. -/
def paramCurve
    (F : MvPolynomial (Fin 3) k) (t : k) : MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval
    (fun i : Fin 3 =>
      match i with
      | ⟨0, _⟩ => MvPolynomial.X (0 : Fin 2)  -- x
      | ⟨1, _⟩ => MvPolynomial.X (1 : Fin 2)  -- y
      | ⟨2, _⟩ => MvPolynomial.C t)           -- parameter t
    F

/-- The variety `V(F_t)` as a subset of `k × k`. -/
def paramVariety (F : MvPolynomial (Fin 3) k) (t : k) : Set (k × k) :=
  {p : k × k | OnCurve (paramCurve F t) p.1 p.2}

/-- The family of curves determined by `F`. -/
def curveFamily (F : MvPolynomial (Fin 3) k) : k → Set (k × k) :=
  fun t => paramVariety F t

/-
Definition 5.

Given a family V(Fₜ) of curves in k², its envelope consists of all points
(x,y) ∈ k² with the property that

    F(x,y,t) = 0,
    ∂F/∂t (x,y,t) = 0

for some t ∈ k.
-/

/-- Evaluate the trivariate polynomial `F(x,y,t)` at `(x, y, t)`. -/
def evalAtTriple
    (F : MvPolynomial (Fin 3) k) (x y t : k) : k :=
  MvPolynomial.eval₂ (RingHom.id k)
    (fun i : Fin 3 =>
      match i with
      | ⟨0, _⟩ => x
      | ⟨1, _⟩ => y
      | ⟨2, _⟩ => t) F

/-- `(x, y)` is a point of the envelope of the family V(Fₜ) determined by `F`. -/
def IsEnvelopePoint
    (F : MvPolynomial (Fin 3) k)
    (x y : k) : Prop :=
  ∃ t : k,
    evalAtTriple F x y t = 0 ∧
    evalAtTriple (MvPolynomial.pderiv (2 : Fin 3) F) x y t = 0

/-- The envelope of the family V(Fₜ) as a subset of `k × k`. -/
def Envelope (F : MvPolynomial (Fin 3) k) : Set (k × k) :=
  {p : k × k | IsEnvelopePoint F p.1 p.2}

end
