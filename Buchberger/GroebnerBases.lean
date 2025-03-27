import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Noetherian.Defs

variable {σ R : Type*} [CommSemiring R]
variable {k : Type*} [Field k]
variable {m : MonomialOrder σ}

namespace MvPolynomial

open scoped MonomialOrder

set_option maxHeartbeats 400000

/-
## Reference : [Becker-Weispfenning1993]

## TODO

* Authors: Antoine Chambert-Loir

* Prove that under `Field F`, `IsUnit (m.leadingCoeff (b i))` is equivalent to `b i ≠ 0`.
-/

theorem isUnit_leadingCoeff_iff_nonzero
  (m : MonomialOrder σ) (b : MvPolynomial σ k) :
  IsUnit (m.leadingCoeff b) ↔ b ≠ 0 := by
  constructor
  · intro h
    contrapose! h
    rw [h, m.leadingCoeff_zero]
    exact not_isUnit_zero
  · intro hb
    have h₁ : m.leadingCoeff b ≠ 0 := by exact MonomialOrder.leadingCoeff_ne_zero_iff.mpr hb
    exact isUnit_iff_ne_zero.mpr h₁

variable (m) in
/-- the leading coefficient of a multivariate polynomial with respect to a monomial ordering -/
noncomputable def leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)

variable (m) in
/-- The S-polynomial. -/
noncomputable def S_polynomial (f g : MvPolynomial σ k) : MvPolynomial σ k :=
  let γ := monomial (m.degree f ⊔ m.degree g) (1 : k)
  (γ - leadingTerm m f) * f - (γ - leadingTerm m g) * g

variable (m) in
/-- The set of leading terms of nonzero polynomials in an ideal I. -/
def leadingTermSet (I : Ideal (MvPolynomial σ R)) : Set (MvPolynomial σ R) :=
  { f | ∃ g ∈ I, g ≠ 0 ∧ leadingTerm m g = f }

variable (m) in
/-- The ideal generated by the leading terms of the nonzero elements of I. -/
def initialIDeal (I : Ideal (MvPolynomial σ R)) : Ideal (MvPolynomial σ R) :=
  Ideal.span (leadingTermSet m I) -- initialIDeal = Ideal.span { f | ∃ g ∈ I, g ≠ 0 ∧ leadingTerm m g = f }

-- Proposition 3.
theorem initialIDeal_is_monomial_ideal {I : Ideal (MvPolynomial σ R)} (hI : I ≠ ⊥) :
  ∃ (A : Finset (σ →₀ ℕ)), (A.toSet ⊆ { s : (σ →₀ ℕ) | ∃ (g : MvPolynomial σ R), g ∈ I ∧ g ≠ 0 ∧ m.degree g = s } ∧
    initialIDeal m I = Ideal.span { f | ∃ s ∈ A, f = monomial s (1 : R) }) := by sorry

/- Definition 5. Groebner_basis
A finite subset G of an ideal I is called a Gröbner basis (or standard basis)
if the ideal generated by the leading terms of the elements of G equals the leading term ideal of I.
We adopt the convention that ⟨∅⟩ = {0}, so that the empty set is the Gröbner basis of the zero ideal.
-/

variable (m) [DecidableEq (MvPolynomial σ R)] in
def is_GrobnerBasis (I : Ideal (MvPolynomial σ R)) (G : List (MvPolynomial σ R)): Prop :=
  (G.toFinset.toSet ⊆ I) ∧
    Ideal.span (G.toFinset.image (fun g ↦ leadingTerm m g)) = initialIDeal m I
  -- (I = ⊥ ∧ G = []) ∨
  -- (I ≠ ⊥ ∧ (G.toFinset.toSet ⊆ I) ∧
  --   Ideal.span (G.toFinset.image (fun g ↦ leadingTerm m g)) = initialIDeal m I)

variable (m) [DecidableEq (MvPolynomial σ R)] in
def is_GrobnerBasis_domain {ι : Type*} (I : Ideal (MvPolynomial σ R)) (G : ι →₀ MvPolynomial σ R): Prop :=
  (I = ⊥ ∧ G = 0) ∨
  (I ≠ ⊥ ∧ (∀ i ∈ G.support, G i ∈ I) ∧
    Ideal.span (G.support.image (fun i ↦ leadingTerm m (G i))) = initialIDeal m I)

/-
Corollary 6.
Fix a monomial order on \(k[x_1,\dots,x_n]\). Then every ideal \(I\) has a Gröbner basis.
Furthermore, any Gröbner basis for \(I\) is a generating set of \(I\).
-/

variable [Fintype σ] [IsNoetherianRing R] in
theorem Hilbert_basis_initial (I : Ideal (MvPolynomial σ R)) : Ideal.FG (initialIDeal m I)
  := sorry --(inferInstance : IsNoetherian _ _).noetherian (initialIDeal m I)

variable [Fintype σ] [DecidableEq (MvPolynomial σ R)] in
theorem grobner_basis_exists (I : Ideal (MvPolynomial σ R)) :
  ∃ (ι : Type*) (G : ι →₀ MvPolynomial σ R), is_GrobnerBasis_domain m I G := by
  -- have h_fin : Ideal.FG (initialIDeal m I) := Hilbert_basis_initial I
  sorry

/-
Recursive step for the division algorithm, calculating the remainder.
It takes the current polynomial `f`, the list of divisors `B`, the proof `hb`
that leading coefficients are units, and the accumulated remainder `r`.
-/

/-
B : ι →₀ MvPolynomial σ R로 하려했으나 일단은 List로 정의
Field가 아니면 Heartbeats 에러로 일단 Field k인 경우 정의
[DecidableEq (σ →₀ ℕ)] [DecidableEq (MvPolynomial σ k)] <- 제거 가능한 방법?
-/


/-
Use same technique as mathlib4/Mathlib/RingTheory/MvPolynomial/Groebner.lean
-/

variable [DecidableEq (σ →₀ ℕ)] [DecidableEq (MvPolynomial σ k)] in
noncomputable def remainderRec (f : MvPolynomial σ k) (B : List (MvPolynomial σ k))
    (hb_all : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) (r : MvPolynomial σ k) : MvPolynomial σ k :=
  if hf : f = 0 then
    r
  else
    if hb' : ∃ b ∈ B , m.degree b = 0 then
      0
    else
      -- Predicate to find a divisor
      match h_find : B.find? (m.degree · ≤ m.degree f) with
      | some b =>
          -- Divisor b found
          have hb_unit : IsUnit (m.leadingCoeff b) :=
            have hb_mem : b ∈ B := by exact List.mem_of_find?_eq_some h_find
            hb_all b hb_mem
          remainderRec (m.reduce hb_unit f) B hb_all r
      | none =>
          -- No divisor's leading term divides LT(f).
          if hl0 : (m.degree f) = 0
          then
            r + f
          else
          -- Add LT(f) to the remainder and continue with f - LT(f).
            let LT_f := leadingTerm m f
            remainderRec (f - LT_f) B hb_all (r + LT_f)
  termination_by WellFounded.wrap
  ((isWellFounded_iff m.syn fun x x_1 ↦ x < x_1).mp m.wf) (m.toSyn (m.degree f))
  decreasing_by
  · have deg_le : m.degree b ≤ m.degree f := by apply of_decide_eq_true (by apply List.find?_some h_find)
    push_neg at hb'
    have deg_reduce : m.degree (m.reduce hb_unit f) ≺[m] m.degree f := by
      apply MonomialOrder.degree_reduce_lt hb_unit deg_le
      intro hf0'
      apply hb' b
      · exact List.mem_of_find?_eq_some h_find
      · simpa [hf0'] using deg_le
    simp
    exact deg_reduce
  · apply MonomialOrder.degree_sub_LTerm_lt
    exact hl0

variable [DecidableEq (σ →₀ ℕ)] [DecidableEq (MvPolynomial σ k)] in
noncomputable def remainder (f : MvPolynomial σ k) (B : List (MvPolynomial σ k)) (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) : MvPolynomial σ k :=
  remainderRec f B hB 0

/-MonomialOrder.div를 이용해 remainder를 정의할 방법 찾기-/
def remainder' (f : MvPolynomial σ R) {ι : Type*} (b : ι → MvPolynomial σ R)
    (hb : ∀ i : ι, IsUnit (m.leadingCoeff (b i))) : MvPolynomial σ R := sorry -- (Classical.choose (m.div hb f)).2.1 -- wrong

variable [DecidableEq (σ →₀ ℕ)] [DecidableEq (MvPolynomial σ k)] in
theorem mem_ideal_iff_remainder_GB_eq_zero
    {I : Ideal (MvPolynomial σ k)} {G : List (MvPolynomial σ k)} (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
    (hGB : is_GrobnerBasis m I G) :
    ∀ (f : MvPolynomial σ k), f ∈ I ↔ remainder f G hG = 0 := by sorry

/-
Buchberger’s Criterion (Theorem 6) says:
Let `I` be a polynomial ideal and let `G` be a basis of `I` (i.e. `I = ideal.span G`).
Then `G` is a Gröbner basis if and only if for all pairs of distinct polynomials
`g₁, g₂ ∈ G`, the remainder on division of `S_polynomial g₁ g₂` by `G` is zero.
-/

variable (m) [Fintype σ] [DecidableEq (σ →₀ ℕ)] [DecidableEq (MvPolynomial σ k)] in
theorem Buchberger_criterion
  {I : Ideal (MvPolynomial σ k)}
  {G : List (MvPolynomial σ k)}
  (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
  (hGI : I = Ideal.span G.toFinset) :
  is_GrobnerBasis m I G ↔
    (∀ (g₁ g₂ : MvPolynomial σ k),
      g₁ ∈ G →
      g₂ ∈ G →
      g₁ ≠ g₂ →
      remainder (S_polynomial m g₁ g₂) G hG = 0) := by
        constructor
        · intro h_isGB g₁ g₂ hg₁ hg₂ hneq
          have : G.toFinset.toSet ⊆ I := by apply h_isGB.1
          have : S_polynomial m g₁ g₂ ∈ I := by sorry
          exact (mem_ideal_iff_remainder_GB_eq_zero hG h_isGB (S_polynomial m g₁ g₂)).mp this
        · sorry


-- variable (m) [Fintype σ]  [DecidableEq (MvPolynomial σ k)] in
-- theorem Buchberger_criterion_domain
--   {ι : Type*} {I : Ideal (MvPolynomial σ k)}
--   (G : ι →₀ MvPolynomial σ k)
--   (hG : I = Ideal.span (Set.range G)) :
--   is_GrobnerBasis_domain m I G ↔
--     (∀ (g₁ g₂ : MvPolynomial σ k),
--       g₁ ∈ (Set.range G) →
--       g₂ ∈ (Set.range G) →
--       g₁ ≠ g₂ →
--       remainder (S_polynomial m g₁ g₂) (G.toFinset.image (fun i ↦ G i)) = 0) := by sorry

/-
A polynomial `f` in `MvPolynomial σ R` is said to reduce to zero modulo a
finite set of polynomials `G ⊆ MvPolynomial σ R` (written `f ⟶[G] 0`) if there
exists a standard representation
  f = ∑ (g ∈ G), A(g) * g,
where `A : G → MvPolynomial σ R`, such that for every `g ∈ G`, if
  A(g) * g ≠ 0,
then
  m.degree (A(g) * g) ≤ m.degree f.
-/

variable [Fintype σ] in
def reduces_to_zero (G : Finset (MvPolynomial σ k)) (f : MvPolynomial σ k) : Prop :=
∃ (A : MvPolynomial σ k → MvPolynomial σ k),
  (f = ∑ g ∈ G, (A g) * g) ∧ ∀ g ∈ G, (A g) * g ≠ 0 → m.degree ((A g) * g) ≼[m] m.degree f

-- variable [DecidableEq (σ →₀ ℕ)] [DecidableEq (MvPolynomial σ k)] in
-- partial def BuchbergerAux (G : List (MvPolynomial σ k)) (B : List (Nat × Nat)) :
--     List (MvPolynomial σ k) :=
--   -- Use pattern matching directly on B for the loop condition
--   match hB : B with
--   | [] => G -- Base case: No more pairs, return current G
--   | (i, j) :: B_tl => -- Get head and tail
--       -- Get polynomials safely (ensure indices are valid for THIS G)
--       if hi : i < G.length then
--         if hj : j < G.length then
--           let gi := G.get ⟨i, hi⟩ -- Use Fin index for guaranteed validity
--           let gj := G.get ⟨j, hj⟩ -- Use Fin index

--           -- Compute S-polynomial and remainder
--           let S_ij := S_polynomial m gi gj
--           let r := remainder S_ij G -- Divide by the current ordered list G
--           if hr : r ≠ 0 then
--             -- Add non-zero remainder to basis G
--             let G' := G ++ [r]
--             let t' := G.length -- Current length BEFORE adding r
--             -- Add new pairs involving the new element (index t')
--             let new_pairs := (List.range t').map fun k ↦ (k, t')
--             -- Recursive call with updated G and B
--             BuchbergerAux G' (new_pairs ++ B_tl)
--           else
--             -- Remainder is zero, just continue with the remaining pairs
--              BuchbergerAux G B_tl
--         else -- Index j out of bounds (should ideally not happen if B is managed correctly)
--           BuchbergerAux G B_tl -- Skip pair if index j is invalid
--       else -- Index i out of bounds (should ideally not happen)
--         BuchbergerAux G B_tl -- Skip pair if index i is invalid

partial def Buchberger_Algorithm (F : List (MvPolynomial σ R)) : List (MvPolynomial σ R) := by sorry
  -- Id.run do
  --   let mut G : List (MvPolynomial σ R) := F -- Explicit type
  --   let mut t : Nat := G.length           -- Explicit type
  --   -- Generate initial pairs (i, j) with 0 <= i < j < t
  --   let mut B : List (Nat × Nat) := List.flatten <| (List.range t).map fun i ↦
  --      (List.range (t - (i + 1))).map fun k ↦ (i, i + 1 + k)

  --   -- Use `B ≠ []` which is Decidable
  --   while hB : B ≠ [] do
  --     -- Use pattern matching on the list B
  --     match B with
  --     | [] => panic! "while condition ¬(B = []) failed" -- Should be unreachable
  --     | (i, j) :: B_tl => -- Get head and tail
  --         let gi := G.getD i 0 -- Default to 0 if index is somehow invalid
  --         let gj := G.getD j 0 -- Default to 0 if index is somehow invalid

  --         -- Compute S-polynomial and remainder
  --         let S_ij := sPolynomial m gi gj
  --         let r := remainder m S_ij G -- Divide by the current ordered list G

  --         if hr : r ≠ 0 then
  --           -- Add non-zero remainder to basis G
  --           let t' := G.length -- Get current length *before* adding
  --           let G' := G ++ [r]
  --           -- Add new pairs involving the new element (index t')
  --           let new_pairs := (List.range t').map fun k ↦ (k, t')
  --           -- Update state
  --           G := G'
  --           t := t' + 1 -- Update count *after* using old length for pairs
  --           B := new_pairs ++ B_tl -- Add new pairs (e.g., at the front)
  --         else
  --           -- Remainder is zero, just continue with the remaining pairs
  --            B := B_tl -- Update B to the tail
  --   return G
