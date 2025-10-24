import Buchberger.GroebnerBases
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Let `ι` be the type indexing the dimensions of our space (e.g., `Fin n` for ℝⁿ).
variable {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n]

open Matrix Set

namespace PolyhedralGeometry

/-!
# Formalizing Polyhedra using Mathlib

This section formalizes the definitions from Chapter 2 of "Gröbner Bases and Convex Polytopes"
by leveraging the existing cone and halfspace theories in Mathlib.
-/








/--
A **Polyhedron** is defined by the data of its H-representation (A, b).
-/
@[ext]
structure Polyhedron (m ι : Type*) where
  m_fin :Fintype m
  ι_fin : Fintype ι
  A : Matrix m ι ℝ
  b : m → ℝ
  /-- The set of points in ℝⁿ satisfying the inequalities A • x ≤ b. -/
  toSet : Set (ι → ℝ) := { x | A *ᵥ x ≤ b }

lemma mem_polyhedron_iff (P : Polyhedron m ι) (x : ι → ℝ) :
  x ∈ P.toSet ↔ P.A *ᵥ x ≤ P.b := by sorry

/--
A Polyhedron is a convex set.
-/
theorem Polyhedron.convex (P : Polyhedron m ι) : Convex ℝ P.toSet := by
  have h_def : P.toSet = ⋂ i : m, { x | P.A i ⬝ᵥ x ≤ P.b i } := by
    ext x
    simp only [mem_iInter, mem_setOf_eq]
    -- The inequality `A *ᵥ x ≤ b` is defined element-wise.
    show x ∈ P.toSet ↔ ∀ (i : m), P.A i ⬝ᵥ x ≤ P.b i
    unfold Polyhedron.toSet
    show x ∈ P.5 ↔ ∀ (i : m), P.A i ⬝ᵥ x ≤ P.b i
    sorry
  rw [h_def]
  -- The intersection of a family of convex sets is convex.
  apply convex_iInter
  -- Now we just need to prove that each set in the intersection is convex.
  intro i
  -- The map `x ↦ P.A i ⬝ᵥ x` is a linear map.
  -- let f : (ι → ℝ) →ₗ[ℝ] ℝ := {
  --   toFun := fun x => P.A i ⬝ᵥ x
  --   map_add' := by
  --     intro x y
  --     -- Prove f(x + y) = f(x) + f(y)
  --     simp [dotProduct_add]
  --   map_smul' := by
  --     intro r x
  --     -- Prove f(r • x) = r • f(x)
  --     simp [dotProduct_smul, smul_eq_mul]
  -- }
  let f := fun x : (ι → ℝ) => P.A i ⬝ᵥ x
  have hf : IsLinearMap ℝ f := {
    map_add := by intro x y; exact dotProduct_add (P.A i) x y
    map_smul := by intro r x; exact dotProduct_smul r (P.A i) x
  }
  -- The set `{x | f x ≤ P.b i}` is a closed half-space.
  -- `convex_halfspace_le` proves that such a set is convex.
  exact convex_halfSpace_le hf (P.b i)

lemma Polyhedron.toSet_convex (P : Polyhedron m ι) : Convex ℝ P.toSet := by
  -- P.toSet := { x | P.A *ᵥ x ≤ P.b }
  -- express as intersection of halfspaces: P.toSet = ⋂ i, { x | (P.A i) ⬝ᵥ x ≤ P.b i }
  have : P.toSet = ⋂ (i : m), { x | (P.A i) ⬝ᵥ x ≤ P.b i } := by
    funext x
    dsimp [Set.mem_setOf_eq, Matrix.mulVec]
    -- the above line depends on how Matrix.* is defined; if needed, use `simp`:
    sorry
  rw [this]
  -- apply convex_iInter with explicit 𝕜, E to help inference
  apply convex_iInter (𝕜 := ℝ) (E := ι → ℝ)
  intro i
  -- each halfspace { x | a x ≤ b } is convex
  sorry

/--
A **Polyhedral Cone** is a special case of a polyhedron where b = 0.
-/
@[ext]
structure PolyhedralCone (m ι : Type*) extends (Polyhedron m ι) where
  b := 0
  /-- The set of points in ℝⁿ satisfying the inequalities A • x ≤ 0. -/
  -- toSet : Set (ι → ℝ) := { x | A *ᵥ x ≤ 0 }

-- We still need a Polytope definition for Proposition 2.1
@[ext]
structure Polytope (ι : Type*) where
  vertices : Finset (ι → ℝ)
  toSet : Set (ι → ℝ) := convexHull ℝ vertices

lemma Polytope.toSet_convex (P : Polytope ι) : Convex ℝ P.toSet := by
  -- P.toSet = convexHull ℝ P.vertices by definition
  sorry

-- instance : Coe (Polytope ι) (Set (ι → ℝ)) where
--   coe P := convexHull ℝ (P.vertices : Set (ι → ℝ))

/-!
### Section: Faces and Minkowski Addition (Adapted for new structures)
-/

/--
**Sturmfels, Chapter 2:** `faceω(P) := {u ∈ P : ω • u ≥ ω • v for all v ∈ P}`

The face of a Polyhedron P. The input is a `Polyhedron` structure, not just a `Set`.
-/
def face (ω : ι → ℝ) (P : Set (ι → ℝ)) : Set (ι → ℝ) :=
  { u ∈ P | ∀ v ∈ P, ω ⬝ᵥ v ≤ ω ⬝ᵥ u }

/--
**Sturmfels, Chapter 2:** "a face of P"

A subset `F` is a face of a Polyhedron `P`.
-/
def IsFace (F : Set (ι → ℝ)) (P : Polyhedron m ι) : Prop :=
  F ⊆ P.toSet ∧ ∃ (ω : ι → ℝ), F = face ω P.toSet

/--
**Sturmfels, Chapter 2:** `faceω'(faceω(P)) = face(ω+ε·ω')(P)`
-/
lemma face_of_face_is_face {m ι : Type*} [Fintype m] [Fintype ι]
  (ω ω' : ι → ℝ) (P : Polyhedron m ι) :
  ∃ ε₀ > 0, ∀ ε, 0 < ε ∧ ε < ε₀ →
    face ω' (face ω P.toSet) = face (ω + ε • ω') P.toSet :=
-- The inner `face ω P` is a `Set`, so the outer `face ω'` takes a `Set`.
-- The RHS `face (ω + ε • ω')` also needs a `Set`, so we use `P.toSet`.
sorry

-- /--
-- **Sturmfels, Chapter 2:** "Proposition 2.1. Every polyhedron P can be written as the sum P = Q + C"
-- -/
-- theorem exists_polytope_cone_sum_decomposition (P : Polyhedron m ι) :
--   ∃ (Q : Polytope ι) (C : PolyhedralCone n ι),
--     -- **Corrected Line**: Using explicit coercions `(Q : Set ...)` for robustness.

--     (P.toSet : Set (ι → ℝ)) = (Q.toSet) + (C.toSet) :=
-- sorry

-- /--
-- **Sturmfels, Chapter 2:** `P₁ + P₂ := {p₁ + p₂ : p₁ ∈ P₁, p₂ ∈ P₂}`
-- -/
-- -- The `+` operator works on the coerced sets.
-- example (P₁ : Polyhedron m ι) (P₂ : Polyhedron n ι) : Set (ι → ℝ) :=
--   (P₁ : Set (ι → ℝ)) + (P₂ : Set (ι → ℝ))

-- /--
-- **Sturmfels, Chapter 2:** `faceω(P₁ + P₂) = faceω(P₁) + faceω(P₂)`
-- -/
-- lemma face_add (ω : ι → ℝ) (P₁ : Polyhedron m ι) (P₂ : Polyhedron n ι)
--   (hP₁ : (P₁ : Set (ι → ℝ)).Nonempty) (hP₂ : (P₂ : Set (ι → ℝ)).Nonempty) :
--   face ω ((P₁ : Set (ι → ℝ)) + (P₂ : Set (ι → ℝ))) = face ω P₁ + face ω P₂ :=
-- -- `face` is defined on `Set`, so we must coerce the `Polyhedron` arguments.
-- sorry

-- /--
-- **Sturmfels, Chapter 2:** "if v is a vertex of P₁ + P₂ then there exist unique vertices p₁ of P₁ and p₂ of P₂"
-- -/
-- theorem unique_vertex_decomposition_of_minkowski_sum
--   (P₁ P₂ : Polytope ι) (v : ι → ℝ) (hv : IsVertex ((P₁ : Set (ι → ℝ)) + (P₂ : Set (ι → ℝ))) v) :
--   ∃! p₁ ∈ (P₁.vertices : Set (ι → ℝ)), ∃! p₂ ∈ (P₂.vertices : Set (ι → ℝ)), v = p₁ + p₂ :=
-- sorry

end PolyhedralGeometry


























































/--
A **Polyhedron** (H-representation) is a finite intersection of closed half-spaces.
This definition directly translates the text: `P = {x ∈ ℝⁿ : A • x ≤ b}`.

Each row `i` of the matrix `A` and the corresponding entry `b i` defines a
closed half-space `{x | (A i) • x ≤ b i}`. The polyhedron is the intersection of these.
-/
@[ext]
structure Polyhedron (m ι : Type*) [Fintype m] [Fintype ι] where
  A : Matrix m ι ℝ
  b : m → ℝ
  /-- The set of points in ℝⁿ satisfying the inequalities A • x ≤ b. -/
  toSet : Set (ι → ℝ) := { x | A *ᵥ x ≤ b }

/--
A **Polyhedral Cone** is a finite intersection of closed linear half-spaces.
It is a special case of a polyhedron where b = 0.
P = {x ∈ ℝⁿ : A • x ≤ 0}.
-/
@[ext]
structure PolyhedralCone (m ι : Type*) [Fintype m] [Fintype ι] where
  A : Matrix m ι ℝ
  /-- The set of points in ℝⁿ satisfying the inequalities A • x ≤ 0. -/
  toSet : Set (ι → ℝ) := { x | A *ᵥ x ≤ 0 }

@[ext]
structure PolyhedralCone₂ (m ι : Type*) [Fintype m] [Fintype ι] where
  /-- The underlying polyhedron. -/
  toPolyhedron : Polyhedron m ι
  /-- The proof that the vector b is zero. -/
  b_is_zero : toPolyhedron.b = 0












-- -- toSet과 같은 유용한 필드들을 PolyhedralCone에서 바로 접근할 수 있도록 도우미 정의 추가
-- def PolyhedralCone₂.toSet (C : PolyhedralCone m ι) : Set (ι → ℝ) :=
--   C.toPolyhedron.toSet

-- /--
-- **Sturmfels, Chapter 2:**
-- "A polyhedron of the form (2.1) is called a (polyhedral) cone."
-- (2.1) `P = pos({u₁,...,uₘ}) := {λ₁u₁ + ... + λₘuₘ : λ₁,...,λₘ ∈ ℝ₊}.`
-- -/
-- def IsCone (P : Polyhedron) : Prop :=
--   ∃ (s : Finset (ι → ℝ)), (P : Set (ι → ℝ)) = ⋂ a ∈ s, { x | a ⬝ᵥ x ≤ 0 }

-- instance : Coe (PolyhedralCone ι) (Set (ι → ℝ)) where
--   coe C := C.asPointedCone

-- omit [Fintype ι] in
-- @[simp]
-- lemma mem_polyhedralCone_iff (C : PolyhedralCone ι) (x : ι → ℝ) :
--     x ∈ (C : Set (ι → ℝ)) ↔ x ∈ Submodule.span {r : ℝ // 0 ≤ r} (C.generators : Set (ι → ℝ)) := by
--   cases C
--   simp only [PolyhedralCone.asPointedCone, SetLike.mem_coe]

-- /--
-- **Lemma (Characterization of membership in a polyhedral cone):**
-- A point `x` is in the cone if and only if it is a non-negative linear combination
-- of its generators. This matches the formula (2.1) in the text.
-- -/
-- @[simp]
-- lemma mem_polyhedralCone_iff_exists_nonneg_coeffs
--     (C : PolyhedralCone ι) (x : ι → ℝ) :
--     x ∈ (C : Set (ι → ℝ)) ↔
--       ∃ (coeffs : (ι → ℝ) →₀ ℝ),
--         (∀ g ∈ coeffs.support, 0 ≤ coeffs g) ∧
--         coeffs.support ⊆ C.generators ∧
--         x = coeffs.sum (fun g c => c • g) := by
--   -- Unfold the membership
--   rw [mem_polyhedralCone_iff, Submodule.mem_span_finset]
--   sorry













-- /-!
-- # Formalizing Polyhedra using Mathlib

-- This section formalizes the definitions from Chapter 2 of "Gröbner Bases and Convex Polytopes"
-- by leveraging the existing cone and halfspace theories in Mathlib.
-- -/

-- @[ext]
-- structure Polytope (ι : Type*) where
--   vertices : Finset (ι → ℝ)

-- def Polytope.asSet {ι : Type*} (P : Polytope ι) : Set (ι → ℝ) :=
--   convexHull ℝ (P.vertices : Set (ι → ℝ))

-- /--
-- A **Polyhedron** is a set that can be described as a finite intersection of closed half-spaces.
-- -/
-- def IsPolyhedron (P : Set (ι → ℝ)) : Prop :=
--   ∃ (s : Finset ((ι → ℝ) × ℝ)), P = ⋂ i ∈ s, { x | i.1 ⬝ᵥ x ≤ i.2 }


-- instance : Coe (PolyhedralCone ι) (Set (ι → ℝ)) where
--   coe C := C.asPointedCone

-- /--
-- A point `v` is a **vertex** of a set `P` if it is an extreme point of `P`.
-- Mathlib uses `IsExtreme ℝ P v`.
-- -/
-- def IsVertex (P : Set (ι → ℝ)) (v : ι → ℝ) : Prop :=
--   IsExtreme ℝ P {v}













-- /-!
-- ### Section: Faces and Minkowski Addition
-- -/

-- /--
-- **Sturmfels, Chapter 2:** `faceω(P) := {u ∈ P : ω • u ≥ ω • v for all v ∈ P}`
-- -/
-- def face (ω : ι → ℝ) (P : Set (ι → ℝ)) : Set (ι → ℝ) :=
--   { u ∈ P | ∀ v ∈ P, ω ⬝ᵥ v ≤ ω ⬝ᵥ u }

-- /--
-- **Sturmfels, Chapter 2:** "a face of P"
-- -/
-- def IsFace (F P : Set (ι → ℝ)) : Prop :=
--   F ⊆ P ∧ ∃ (ω : ι → ℝ), F = face ω P

-- /--
-- **Sturmfels, Chapter 2:** `faceω'(faceω(P)) = face(ω+ε·ω')(P)`
-- -/
-- lemma face_of_face_is_face (ω ω' : ι → ℝ) (P : Set (ι → ℝ)) (hP : IsPolyhedron P) :
--   ∃ ε₀ > 0, ∀ ε, 0 < ε ∧ ε < ε₀ → face ω' (face ω P) = face (ω + ε • ω') P :=
-- sorry -- This proof is non-trivial and relies on the properties of polyhedra.

-- /--
-- **Sturmfels, Chapter 2:** "Proposition 2.1. Every polyhedron P can be written as the sum P = Q + C"
-- -/
-- theorem exists_polytope_cone_sum_decomposition (P : Set (ι → ℝ)) (hP : IsPolyhedron P) :
--   ∃ (Q : Polytope ι) (C : PolyhedralCone ι),
--     -- **Corrected Line**: `Q` must be coerced to a set inside the `∀` quantifier as well.
--     (∀ (C' : PolyhedralCone ι), P = (Q : Set (ι → ℝ)) + (C' : Set (ι → ℝ)) → C' = C) ∧
--     P = (Q : Set (ι → ℝ)) + (C : Set (ι → ℝ)) :=
-- sorry

-- /--
-- **Sturmfels, Chapter 2:** `P₁ + P₂ := {p₁ + p₂ : p₁ ∈ P₁, p₂ ∈ P₂}`
-- -/
-- example (P₁ P₂ : Set (ι → ℝ)) : Set (ι → ℝ) := P₁ + P₂

-- /--
-- **Sturmfels, Chapter 2:** `faceω(P₁ + P₂) = faceω(P₁) + faceω(P₂)`
-- -/
-- lemma face_add (ω : ι → ℝ) (P₁ P₂ : Set (ι → ℝ)) (hP₁ : P₁.Nonempty) (hP₂ : P₂.Nonempty) :
--   face ω (P₁ + P₂) = face ω P₁ + face ω P₂ :=
-- -- This is a standard result in convex analysis.
-- sorry

-- /--
-- **Sturmfels, Chapter 2:** "if v is a vertex of P₁ + P₂ then there exist unique vertices p₁ of P₁ and p₂ of P₂"
-- -/
-- theorem unique_vertex_decomposition_of_minkowski_sum
--   (P₁ P₂ : Polytope ι) (v : ι → ℝ) (hv : IsVertex (P₁ + P₂ : Set (ι → ℝ)) v) :
--   ∃! p₁ ∈ (P₁.vertices : Set (ι → ℝ)), ∃! p₂ ∈ (P₂.vertices : Set (ι → ℝ)), v = p₁ + p₂ :=
-- -- The original statement was slightly off. The vertices `p₁` and `p₂` themselves are unique.
-- -- The `IsVertex` property is a given.
-- sorry



-- old version

-- def HPolyhedron {m : Type*} [Fintype m] (A : Matrix m ι ℝ) (b : m → ℝ) : Set (ι → ℝ) :=
--   ⋂ i : m, { x | A i ⬝ᵥ x ≤ b i }

-- @[ext]
-- structure PolyhedralCone' (ι : Type*) where
--   /-- The finite set of vectors that generate the cone. -/
--   generators : Finset (ι → ℝ)
--   /-- The cone is the `PointedCone` spanned by these vectors. -/
--   asPointedCone : PointedCone ℝ (ι → ℝ) := Submodule.span {r : ℝ // 0 ≤ r} (generators : Set (ι → ℝ))
