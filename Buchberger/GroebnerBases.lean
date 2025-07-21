import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Span.Defs
-- import Mathlib.RingTheory.Polynomial.Basic
-- import Mathlib.Algebra.Ring.Defs
import Buchberger.MonomialIdeal
-- import Buchberger.Order2

variable {σ : Type*} -- [DecidableEq σ]
variable {m : MonomialOrder σ}

set_option maxHeartbeats 0

open MonomialOrder MvPolynomial

namespace MonomialOrder

/-- Given a monomial order, notation for the corresponding equality relation on `σ →₀ ℕ` -/
scoped
notation:50 c " ≈[" m:25 "] " d:50 => (MonomialOrder.toSyn m c = MonomialOrder.toSyn m d)

/-
## Reference : [Cox, Little, and O'Shea 1997] [Becker-Weispfenning1993]
-/

section Semiring

variable {R : Type*} [CommSemiring R]

variable {ι : Type*} [DecidableEq ι] [LinearOrder ι] [OrderBot ι] in
lemma degree_sum_le_max (s : Finset ι) (hs : s.Nonempty) (f : ι → MvPolynomial σ R) :
    ∑ i ∈ s, (f i).support.sup m.toSyn ≤ (s.image (fun i => (f i).support.sup m.toSyn)).max' (by apply Finset.image_nonempty.mpr hs) := by
  -- We proceed by induction on the finset `s`.
  induction s using  Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.image_empty, zero_le]
  | insert i s hi_not_in_s ih =>
    by_cases h_s_empty : s = ∅
    · -- If s is empty, then `insert i s` is just `{i}`.
      subst h_s_empty
      simp
    -- Inductive step: s' = insert i s, where s is not empty.
    have h_s_nonempty : s.Nonempty := Finset.nonempty_of_ne_empty h_s_empty
    have h_insert_nonempty : (insert i s).Nonempty := by exact Finset.insert_nonempty i s
    -- `∑_{j∈s'} f j = f i + ∑_{j∈s} f j`
    rw [Finset.sum_insert hi_not_in_s]
    have h1 : m.toSyn (m.degree ((f i) + (∑ j ∈ s, f j))) ≤ max (m.toSyn (m.degree (f i))) (m.toSyn (m.degree (∑ j ∈ s, f j))) := m.degree_add_le
    have : ((f i) + (∑ j ∈ s, f j)).support.sup m.toSyn ≤ max ((f i).support.sup m.toSyn) ((∑ j ∈ s, f j).support.sup m.toSyn) := by sorry
    sorry
    -- apply le_trans this
    -- rw [max_le_iff]
    -- constructor
    -- · -- m.toSyn (m.degree (f i)) ≤ m.toSyn ((insert i s).sup fun i ↦ m.degree (f i))
    --   apply toSyn_monotone
    --   have : i ∈ (insert i s) := by exact Finset.mem_insert_self i s
    --   apply Finset.le_sup this
    -- · -- m.toSyn (s.sup fun i ↦ m.degree (f i)) ≤ m.toSyn ((insert i s).sup fun i ↦ m.degree (f i))
    --   apply le_trans ih
    --   apply toSyn_monotone
    --   refine Finset.sup_mono ?_
    --   exact Finset.subset_insert i s

-- -- We immediately prove lemmas that rewrite the notation into a more usable form.
-- -- These are the fundamental definitions of the monomial order relations.
-- theorem le_def (c d : σ →₀ ℕ) : (c ≼[m] d) = (m.toSyn c ≤ m.toSyn d) := rfl
-- theorem lt_def (c d : σ →₀ ℕ) : (c ≺[m] d) = (m.toSyn c < m.toSyn d) := rfl

-- -- For convenience, we provide `iff` lemmas.
-- @[simp]
-- theorem le_iff_toSyn_le {c d : σ →₀ ℕ} : c ≼[m] d ↔ m.toSyn c ≤ m.toSyn d := .rfl

-- @[simp]
-- theorem lt_iff_toSyn_lt {c d : σ →₀ ℕ} : c ≺[m] d ↔ m.toSyn c < m.toSyn d := .rfl

/--
A monomial order endows `σ →₀ ℕ` with the structure of a linearly ordered
cancellative additive commutative monoid.
We can formalize this by showing that `toSyn` is an order isomorphism.

This theorem states that `toSyn` is an isomorphism between `(σ →₀ ℕ, ≼[m])`
and `(m.syn, ≤)`.
-/
def relIso : RelIso (· ≼[m] ·) ((· : m.syn) ≤ ·) where
  toEquiv := m.toSyn.toEquiv
  map_rel_iff' {c d} := by
    -- The goal is `m.toSyn c ≤ m.toSyn d ↔ c ≼[m] d`.
    -- This is the reverse of `le_iff_toSyn_le`, so we can use `iff_comm`.
    exact ge_iff_le

theorem toSyn_degree_eq_sup_support (f : MvPolynomial σ R) :
    m.toSyn (m.degree f) = f.support.sup m.toSyn := by
  -- Unfold the definition of degree
  rw [MonomialOrder.degree]
  exact AddEquiv.apply_symm_apply m.toSyn (f.support.sup ⇑m.toSyn)

variable (m) in
lemma degree_add_lt_of_le_lt {f g : MvPolynomial σ R} {δ : m.syn}
  (hf : m.toSyn (m.degree f) < δ) (hg : m.toSyn (m.degree g) < δ) :
  m.toSyn (m.degree (f + g)) < δ := by
  apply lt_of_le_of_lt (m.degree_add_le)
  rw [max_lt_iff]
  exact ⟨hf, hg⟩

variable (m) in
lemma degree_sum_le_syn {ι : Type*} (s : Finset ι) (h : ι → MvPolynomial σ R) :
    m.toSyn (m.degree (∑ i ∈ s, h i)) ≤ s.sup (fun i => m.toSyn (m.degree (h i))) := by
  have : s.sup (fun i => m.toSyn (m.degree (h i))) = m.toSyn (m.toSyn.symm (s.sup fun i ↦ m.toSyn (m.degree (h i)))) := by
    exact Eq.symm (AddEquiv.apply_symm_apply m.toSyn (s.sup fun i ↦ m.toSyn (m.degree (h i))))
  rw [this]
  apply (@degree_le_iff σ m R _ (∑ i ∈ s, h i) (m.toSyn.symm (s.sup (fun i => m.toSyn (m.degree (h i)))))).mpr
  intro b hb
  obtain ⟨i, hi_s, hi_mem_support⟩ := Finsupp.mem_support_finset_sum b hb
  rw [AddEquiv.apply_symm_apply]
  have h_syn_le : m.toSyn b ≤ m.toSyn (m.degree (h i)) := m.le_degree hi_mem_support
  apply le_trans h_syn_le
  apply @Finset.le_sup _ _ _ _ s fun i ↦ m.toSyn (m.degree (h i))
  exact hi_s

variable {ι : Type*} [DecidableEq ι] in
lemma degree_sum_le (s : Finset ι) (f : ι → MvPolynomial σ R) :
    m.degree (∑ i ∈ s, f i) ≼[m] s.sup (fun i => m.degree (f i)) := by
  -- We proceed by induction on the finset `s`.
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, m.degree_zero, map_zero, Finset.sup_empty, zero_le]
    --exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a ↦ a) rfl (m.toSyn ⊥)
  | insert i s hi_not_in_s ih =>
    by_cases h_s_empty : s = ∅
    · -- If s is empty, then `insert i s` is just `{i}`.
      subst h_s_empty
      simp only [insert_empty_eq, Finset.sum_singleton, Finset.sup_singleton, le_refl]
    -- Inductive step: s' = insert i s, where s is not empty.
    have h_s_nonempty : s.Nonempty := Finset.nonempty_of_ne_empty h_s_empty
    have h_insert_nonempty : (insert i s).Nonempty := by exact Finset.insert_nonempty i s
    -- `∑_{j∈s'} f j = f i + ∑_{j∈s} f j`
    rw [Finset.sum_insert hi_not_in_s]
    have : m.toSyn (m.degree ((f i) + (∑ j ∈ s, f j))) ≤ max (m.toSyn (m.degree (f i))) (m.toSyn (m.degree (∑ j ∈ s, f j))) := m.degree_add_le
    apply le_trans this
    rw [max_le_iff]
    constructor
    · -- m.toSyn (m.degree (f i)) ≤ m.toSyn ((insert i s).sup fun i ↦ m.degree (f i))
      apply toSyn_monotone
      have : i ∈ (insert i s) := by exact Finset.mem_insert_self i s
      apply Finset.le_sup this
    · -- m.toSyn (s.sup fun i ↦ m.degree (f i)) ≤ m.toSyn ((insert i s).sup fun i ↦ m.degree (f i))
      apply le_trans ih
      apply toSyn_monotone
      refine Finset.sup_mono ?_
      exact Finset.subset_insert i s

end Semiring

section CommRing

variable {R : Type*} [CommRing R]

noncomputable def normalForm_general
  (B : Set (MvPolynomial σ R))
  (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
  (f : MvPolynomial σ R) : MvPolynomial σ R := by
  choose gcomb r hr using MonomialOrder.div_set hB f
  exact r

variable [CommRing R] [Finite σ] [IsNoetherianRing R] in
theorem Hilbert_basis_initial (I : Ideal (MvPolynomial σ R)) :
  Ideal.FG (initialIdeal m I) := by sorry --(inferInstance : IsNoetherianRing _).noetherian (initialIdeal m I) -- @isNoetherianRing R σ _ _

end CommRing
end MonomialOrder

namespace MvPolynomial
section Field

variable {k : Type*} [Field k] [DecidableEq k]

/-
## TODO
normalForm과 remainder를 하나로 합치기
-/

-- variable (m) in
-- noncomputable def normalForm
--   (B : Set (MvPolynomial σ k))
--   (hB : ∀ b ∈ B, b ≠ 0)
--   (f : MvPolynomial σ k) : MvPolynomial σ k := by
--   choose gcomb r hr using
--     MonomialOrder.div_set
--       (fun b hb => (isUnit_leadingCoeff_iff_nonzero m b).mpr (hB b hb))
--       f
--   -- (*)
--   exact r

omit [DecidableEq k] in
theorem division_algorithm_existence (m : MonomialOrder σ)
  {B : Set (MvPolynomial σ k)} (hB : ∀ b ∈ B, b ≠ 0) (f : MvPolynomial σ k) :
  ∃ (g : B →₀ (MvPolynomial σ k)) (r : MvPolynomial σ k),
    f = Finsupp.linearCombination _ (fun (p : B) ↦ (p : MvPolynomial σ k)) g + r ∧
    (∀ (p : B), m.degree ((p : MvPolynomial σ k) * (g p)) ≼[m] m.degree f) ∧
    (∀ c ∈ r.support, ∀ b ∈ B, ¬ m.degree b ≤ c) :=
  MonomialOrder.div_set
      (fun b hb => (isUnit_leadingCoeff_iff_nonzero m b).mpr (hB b hb))
      f

noncomputable def quotients (m : MonomialOrder σ)
  {B : Set (MvPolynomial σ k)} (hB : ∀ b ∈ B, b ≠ 0) (f : MvPolynomial σ k) :
  B →₀ MvPolynomial σ k :=
  (division_algorithm_existence m hB f).choose

noncomputable def normalForm (m : MonomialOrder σ)
  {B : Set (MvPolynomial σ k)} (hB : ∀ b ∈ B, b ≠ 0) (f : MvPolynomial σ k) :
  MvPolynomial σ k :=
  (Exists.choose_spec (division_algorithm_existence m hB f)).choose

omit [DecidableEq k] in
/--
This lemma states that the `quotients` and `normalForm` functions satisfy the properties
guaranteed by the division algorithm.
-/
lemma normalForm_spec (m : MonomialOrder σ)
  {B : Set (MvPolynomial σ k)} (hB : ∀ b ∈ B, b ≠ 0) (f : MvPolynomial σ k) :
  let q := quotients m hB f
  let r := normalForm m hB f
  -- Property 1: The division equation
  f = (Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ k)) q) + r ∧
  -- Property 2: The degree condition
  (∀ (p : B), m.degree ((p : MvPolynomial σ k) * q p) ≼[m] m.degree f) ∧
  -- Property 3: The remainder condition (irreducibility)
  (∀ c ∈ r.support, ∀ b ∈ B, ¬ m.degree b ≤ c) := by
  -- The proof is by applying `Exists.choose_spec` twice.
  let H_exists := division_algorithm_existence m hB f
  let spec_q := Exists.choose_spec H_exists
  let spec_r := Exists.choose_spec spec_q
  -- `spec_r` is exactly the goal of the lemma.
  exact spec_r

omit [DecidableEq k] in
/--
This lemma states that the `quotients` and `normalForm` functions satisfy the properties
guaranteed by the division algorithm.
-/
lemma normalForm_spec' (m : MonomialOrder σ)
  {B : Set (MvPolynomial σ k)} (hB : ∀ b ∈ B, b ≠ 0) (f : MvPolynomial σ k) :
  -- Property 1: The division equation
  f = (Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ k)) (quotients m hB f)) + (normalForm m hB f) ∧
  -- Property 2: The degree condition
  (∀ (p : B), m.degree ((p : MvPolynomial σ k) * (quotients m hB f) p) ≼[m] m.degree f) ∧
  -- Property 3: The remainder condition (irreducibility)
  (∀ c ∈ (normalForm m hB f).support, ∀ b ∈ B, ¬ m.degree b ≤ c) := by
  -- The proof is by applying `Exists.choose_spec` twice.
  let H_exists := division_algorithm_existence m hB f
  let spec_q := Exists.choose_spec H_exists
  let spec_r := Exists.choose_spec spec_q
  -- `spec_r` is exactly the goal of the lemma.
  exact spec_r

omit [DecidableEq k] in
/--  If `normalForm m B hB f = 0`, then in fact
    `f = ∑ (quotients m B hB f) • b`. -/
theorem representation_of_f_of_normalForm_zero
  {B : Set (MvPolynomial σ k)} (hB : ∀ b ∈ B, b ≠ 0) (f : MvPolynomial σ k)
  (h0 : normalForm m hB f = 0) :
  f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ k)) (quotients m hB f) := by
  have : f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ k)) (quotients m hB f) + (normalForm m hB f) := by
    apply (normalForm_spec m hB f).1
  rw [h0, add_zero] at this
  exact this



variable (m) [DecidableEq σ] in
/-- Definition 5. Groebner_basis
A finite subset G of an ideal I is called a Gröbner basis (or standard basis)
if the ideal generated by the leading terms of the elements of G
equals the leading term ideal of I.
We adopt the convention that ⟨∅⟩ = {0}, so that the empty set is the
Gröbner basis of the zero ideal.
-/
def IsGroebnerBasis (I : Ideal (MvPolynomial σ k)) (G : Finset (MvPolynomial σ k)) : Prop :=
  (∀ g ∈ G, g ≠ 0) ∧ G.toSet ⊆ I ∧ Ideal.span (G.image fun g => leadingTerm m g) = initialIdeal m I

variable [DecidableEq σ] in
lemma IsGroebnerBasis.initialIdeal_eq_monomialIdeal
  {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
  (hGB : IsGroebnerBasis m I G) :
  initialIdeal m I = monomialIdeal k (G.image fun g => m.degree g) := by
  -- by hypothesis the leading‐term span equals the initial ideal
  have h_span : initialIdeal m I = Ideal.span (G.image fun g => leadingTerm m g) := by
    simpa [initialIdeal] using (hGB.2.2).symm
  -- rewrite both sides into span …  and monomialIdeal
  rw [h_span, monomialIdeal]; clear h_span
  apply le_antisymm
  · -- (⊆) : every leadingTerm m g lies in the span of monomial α 1
    apply Ideal.span_le.mpr
    intro f hf
    simp at hf
    obtain ⟨g, hg_in_G, hgf, rfl⟩ := hf
    rw [leadingTerm]
    -- g ∈ G ⇒ m.degree g ∈ G.image (fun h => m.degree h)
    have hdeg : m.degree g ∈ G.image (fun h => m.degree h) :=
      Finset.mem_image.2 ⟨g, hg_in_G, rfl⟩
    -- so monomial (m.degree g) 1 is a generator
    have hmono : monomial (m.degree g) 1 ∈
      ((fun s => monomial s (1 : k)) '' (G.image fun h => m.degree h)) :=
      Set.mem_image_of_mem _ hdeg
    -- and the leading coefficient is a unit
    have hunit : IsUnit (m.leadingCoeff g) :=
      (isUnit_leadingCoeff_iff_nonzero m g).mpr (hGB.1 g hg_in_G)
    -- conclude
    have :
      monomial (m.degree g) (m.leadingCoeff g)
          = (C (m.leadingCoeff g)) * monomial (m.degree g) 1 := by
          rw [C_mul_monomial]
          rw [MulOneClass.mul_one (m.leadingCoeff g)]
    rw [this]
    apply Ideal.mul_mem_left
    exact (Ideal.mem_span ((monomial (m.degree g)) 1)).mpr fun p a ↦ a hmono
  · -- (⊇) : each `monomial α 1` comes from some g ∈ G
    apply Ideal.span_le.mpr
    intro f hf
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, exists_exists_and_eq_and] at hf
    obtain ⟨g, hg_in_G, rfl⟩ := hf
    obtain ⟨gnzero, hGI, hspan⟩ := hGB
    have hlt : monomial (m.degree g) (1 : k) = C (m.leadingCoeff g)⁻¹ * leadingTerm m g := by
      simp [leadingTerm]
      rw [C_mul_monomial]
      have : (m.leadingCoeff g)⁻¹ * m.leadingCoeff g = 1 := by
        exact IsUnit.inv_mul_cancel ((isUnit_leadingCoeff_iff_nonzero m g).mpr (gnzero g hg_in_G))
      rw [this]
    rw [hlt]
    apply Ideal.mul_mem_left
    --show leadingTerm m g ∈ Ideal.span ↑(Finset.image (fun g ↦ leadingTerm m g) G)
    have hgen : leadingTerm m g ∈ (G.image fun g => leadingTerm m g) :=
      Finset.mem_image_of_mem (fun g ↦ leadingTerm m g) hg_in_G
    exact (Ideal.mem_span (leadingTerm m g)).mpr fun p a ↦ a hgen

variable [Fintype σ] [DecidableEq σ] in
/--
§5 Corollary 6.
Fix a monomial order on \(k[x_1,\dots,x_n]\). Then every ideal \(I\)
has a Gröbner basis.
Furthermore, any Gröbner basis for \(I\) is a generating set of \(I\).
-/
theorem grobner_basis_exists (I : Ideal (MvPolynomial σ k)) :
  ∃ G : Finset (MvPolynomial σ k), IsGroebnerBasis m I G := by
  -- have h_fin : Ideal.FG (initialIDeal m I) := Hilbert_basis_initial I
  sorry

variable [DecidableEq σ] in
/--
Proposition.  If `G` is a Gröbner basis for `I`, then every `f` admits
a unique decomposition `f = g + r` with
1. `g ∈ I`, and
2. no term of `r` is divisible by any `LT gᵢ`.
-/
theorem normalForm_exists_unique
  {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
  (hGB : IsGroebnerBasis m I G)
  (f  : MvPolynomial σ k) :
  -- restated with ExistsUnique
  ExistsUnique (λ r : MvPolynomial σ k ↦
    (∃ g, g ∈ I ∧ f = g + r)
    ∧ ∀ c ∈ r.support, ∀ gi ∈ G, ¬ m.degree gi ≤ c) := by
  -- 1) **Existence** via the division algorithm
  have hGset : ∀ gi ∈ G, IsUnit (m.leadingCoeff gi) := by
    intro gi
    intro gi_in_G
    exact (isUnit_leadingCoeff_iff_nonzero m gi).mpr (hGB.1 gi gi_in_G)
  obtain ⟨gcomb, r, ⟨hre, hdeg, hnil⟩⟩ := m.div_set hGset f

  -- 2) set `g := ∑ b in gcomb.support, gcomb b • (b : MvPolynomial)`
  let g : MvPolynomial σ k := gcomb.sum (fun b coeff => coeff • (b : MvPolynomial σ k))
  have hgI : g ∈ I := by
    simp [g, Finsupp.sum]
    have h_support_mem : ∀ b ∈ gcomb.support, (b : MvPolynomial σ k) ∈ I :=
      fun b hb => hGB.2.1 b.2
    exact Submodule.sum_smul_mem I gcomb h_support_mem
  use r
  constructor
  · simp
    constructor
    · show ∃ g ∈ I, f = g + r -- g ∈ I because each `b ∈ G` lies in `I` and `I` is an ideal
      use g
      constructor
      · show g ∈ I
        exact hgI
      · show f = g + r
        simpa only [g] using hre
    · -- no term of `r` is divisible by any `LT gᵢ`
      show ∀ (c : σ →₀ ℕ), ¬coeff c r = 0 → ∀ gi ∈ G, ¬m.degree gi ≤ c
      intro c hc gi hgi
      have : c ∈ r.support := (mem_support_iff.mpr hc)
      have : ∀ b ∈ ↑G, ¬m.degree b ≤ c := by exact fun b a ↦ hnil c this b a
      have : ¬m.degree gi ≤ c := by (expose_names; exact hnil c this_1 gi hgi)
      have : m.degree gi = m.degree (leadingTerm m gi) := by exact Eq.symm (degree_leadingTerm gi)
      (expose_names; exact hnil c this_1 gi hgi)

  · -- **uniqueness**
    -- Suppose `r'` also works; then `f = g' + r'` and `r'` has no divisible LT–terms.
    clear hdeg
    rintro r' ⟨⟨g', hg'I, hre'⟩, hnil'⟩
    by_contra hdiff
    have hne: ¬(r - r' = 0) := by exact sub_ne_zero_of_ne fun a ↦ hdiff (id (Eq.symm a))
    have hrg : r - r' = g' - g := by
      rw [eq_sub_of_add_eq' (id (Eq.symm hre)), eq_sub_of_add_eq' (id (Eq.symm hre'))]
      exact sub_sub_sub_cancel_left g g' f
    have dI : r - r' ∈ I := by
      rw [hrg]
      exact (Submodule.sub_mem_iff_left I hgI).mpr hg'I
    have hlt_in : leadingTerm m (r - r') ∈ initialIdeal m I := by
      dsimp [initialIdeal]
      apply Ideal.subset_span
      exact ⟨r - r', dI, hne, rfl⟩
    have hlm_in : monomial (m.degree (r - r')) 1 ∈ initialIdeal m I := by
      -- have hC : IsUnit (m.leadingCoeff (r - r')) := by
      --   exact (isUnit_leadingCoeff_iff_nonzero m (r - r')).mpr hne
      have h₁ : (monomial (m.degree (r - r')) (1 : k)) = C (m.leadingCoeff (r - r'))⁻¹ * (leadingTerm m (r - r')):= by
        simp only [leadingTerm, C_mul_monomial, inv_mul_cancel₀ (MonomialOrder.leadingCoeff_ne_zero_iff.mpr hne)]
      -- have h₁: leadingTerm m (r - r') = (MvPolynomial.C (m.leadingCoeff (r - r'))) * (monomial (m.degree (r - r')) (1 : k)) := by
      --   simp [leadingTerm, C_mul_monomial]
      rw [initialIdeal]

      have : leadingTerm m (r - r') ∈ initialIdeal m I
        → C (m.leadingCoeff (r - r'))⁻¹ * (leadingTerm m (r - r')) ∈ initialIdeal m I := by exact fun a ↦ Ideal.mul_mem_left (initialIdeal m I) (C (m.leadingCoeff (r - r'))⁻¹) hlt_in
      rw [initialIdeal] at *
      have : C (m.leadingCoeff (r - r'))⁻¹ * leadingTerm m (r - r') ∈ Ideal.span {f | ∃ g ∈ I, g ≠ 0 ∧ leadingTerm m g = f} := by exact this hlt_in
      rw [h₁]
      exact this
    -- extract an exponent α dividing `m.degree d`
    have hmono : monomial (m.degree (r - r')) 1 ∈ monomialIdeal k ↑(Finset.image (fun g ↦ m.degree g) G) := by
      simp only [IsGroebnerBasis.initialIdeal_eq_monomialIdeal hGB, Finset.coe_image, g] at hlm_in
      simp only [Finset.coe_image, hlm_in, g]
    have : ∃ α ∈ (Finset.image (fun g ↦ m.degree g) G), α ≤ m.degree (r - r') := by
      apply mem_monomialIdeal_iff_divisible.mp hmono
    obtain ⟨α, hα⟩ := this
    rw [Finset.mem_image] at hα
    obtain ⟨gα, ⟨hgα_in_G, hgαlm, rfl⟩⟩ := hα.1
    have hin : m.degree (r - r') ∈ r.support ∪ r'.support := by
      apply Finsupp.support_sub
      exact MonomialOrder.degree_mem_support hne
    simp only [Finset.mem_union] at hin
    cases hin with
    | inl h => exact hnil (m.degree (r - r')) h gα hgα_in_G hα.2
    | inr h => exact hnil' (m.degree (r - r')) h gα hgα_in_G hα.2

-- variable [DecidableEq σ] in
-- /--
-- **§6 Corollary 2**
-- Let $G = \{g_1,\dots,g_t\}$ be a Gröbner basis for an ideal $I \subseteq k[x_1,\dots,x_n]$ and let $f \in k[x_1,\dots,x_n]$.
-- Then $f \in I$ if and only if the remainder on division of $f$ by $G$ is zero.
-- -/
-- theorem mem_I_iff_normalForm_eq_zero'
--   {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
--   (hGB : IsGroebnerBasis m I G)
--   (f : MvPolynomial σ k) :
--   f ∈ I ↔ normalForm m G hGB.1 f = 0 := by
--   -- prepare the two hypotheses for `div_set` and for uniqueness
--   --let B := G.toSet
--   --have hB : ∀ b ∈ B, b ≠ 0 := fun _ hb => hGB.1 _ hb
--   let hU : ∀ g ∈ G, IsUnit (m.leadingCoeff g) := fun g hg =>
--     (isUnit_leadingCoeff_iff_nonzero m g).mpr (hGB.1 g hg)
--   have unique_rem := normalForm_exists_unique hGB f

--   constructor
--   · -- (→) if `f ∈ I` then the chosen remainder must be `0`
--     intro hf
--     -- build the “r = 0” witness of the unique‐remainder property
--     have P₀ :
--       (∃ g, g ∈ I ∧ f = g + 0) ∧
--       ∀ c ∈ (0 : MvPolynomial σ k).support, ∀ gi ∈ G, ¬ m.degree gi ≤ c := by
--       constructor
--       · use f; constructor; exact hf; simp
--       · simp
--     -- build the “r = normalForm …” witness
--     have Pn :
--       (∃ g, g ∈ I ∧ f = g + normalForm m G hGB.1 f) ∧
--       ∀ c ∈ (normalForm m G hGB.1 f).support, ∀ gi ∈ G, ¬ m.degree gi ≤ c := by
--       obtain ⟨q, r, ⟨hre, _, hnil⟩⟩ :=
--         MonomialOrder.div_set hU f
--       dsimp [normalForm]
--       constructor
--       · -- `g := ∑ q i • (i : MvPolynomial)`
--         use q.sum fun i coeff => coeff • (i : MvPolynomial σ k)
--         -- this `g` lies in `I` because `G ⊆ I`
--         have : ∀ i ∈ q.support, (i : MvPolynomial σ k) ∈ I := fun i hi =>
--           hGB.2.1 i.2
--         sorry
--         --refine ⟨Submodule.sum_smul_mem I _ this, _⟩
--         --simpa [Finsupp.sum, *] using hre
--       · sorry
--     -- now uniqueness forces `normalForm … = 0`
--     sorry
--     --simpa [normalForm] using unique_rem.2 _ _ Pn P₀

--   · -- (←) if the remainder is `0` then `f = g + 0 ∈ I`
--     intro h0
--     obtain ⟨q, r, ⟨hre, _, _⟩⟩ := MonomialOrder.div_set hU f
--     -- since `r = normalForm … = 0`, we get `f = ∑ q i • i`
--     sorry

variable [DecidableEq σ] in
/--
**§6 Corollary 2**
Let $G = \{g_1,\dots,g_t\}$ be a Gröbner basis for an ideal $I \subseteq k[x_1,\dots,x_n]$
and let $f \in k[x_1,\dots,x_n]$.
Then $f \in I$ if and only if the remainder on division of $f$ by $G$ is zero.
-/
theorem mem_Ideal_iff_GB_normalForm_eq_zero
  {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
  (hGB : IsGroebnerBasis m I G)
  (f : MvPolynomial σ k) :
  f ∈ I ↔ normalForm m hGB.1 f = 0 := by
  -- The hypothesis that all elements of G are non-zero
  have hG_nonzero : ∀ g ∈ G.toSet, g ≠ 0 := fun g hg => hGB.1 g hg
  -- The hypothesis that all elements of G have unit leading coefficients
  have hG_unit_lc : ∀ g ∈ G.toSet, IsUnit (m.leadingCoeff g) := fun g hg =>
    (isUnit_leadingCoeff_iff_nonzero m g).mpr (hG_nonzero g hg)

  -- The uniqueness of the remainder is key.
  have unique_rem := normalForm_exists_unique hGB f

  constructor
  · -- Direction (→): Assume `f ∈ I`. We must show its normal form is 0.
    intro hf_in_I
    -- We will show that `r = 0` is a valid remainder for `f`.
    -- According to `normalForm_exists_unique`, there can be only one such remainder.
    -- Since `normalForm ... f` is also a valid remainder, they must be equal.

    -- 1: The trivial decomposition `f = f + 0`.
    have P_zero : (∃ g, g ∈ I ∧ f = g + 0) ∧
        (∀ c ∈ (0 : MvPolynomial σ k).support, ∀ gi ∈ G, ¬ m.degree gi ≤ c) := by
      constructor
      · -- `f = g + 0` with `g ∈ I`. We can choose `g = f`.
        use f, hf_in_I
        simp
      · -- The remainder `0` has an empty support.
        simp

    -- 2: The decomposition given by the `normalForm` function.
    let r_n := normalForm m hG_nonzero f
    have P_normal : (∃ g, g ∈ I ∧ f = g + r_n) ∧
        (∀ c ∈ r_n.support, ∀ gi ∈ G, ¬ m.degree gi ≤ c) := by
      have spec := normalForm_spec m hG_nonzero f
      constructor
      · -- `f = g + r_n` with `g ∈ I`.
        let q_n := quotients m hG_nonzero f
        let g_n := q_n.sum fun i coeff => coeff • (i : MvPolynomial σ k)
        use g_n
        constructor
        · -- `g_n` ∈ `I`.
          apply Submodule.sum_smul_mem I
          intro i _
          exact hGB.2.1 i.2 -- i.2 is the proof that i.val ∈ G
        · -- `f = g_n + r_n` .
          exact spec.1
      · -- The remainder condition for `r_n`.
        exact spec.2.2
    -- unique_rem : ∃! r, P r
    obtain ⟨r₀, hr₀, hr_unique⟩ := unique_rem
    -- hr_unique : ∀ y, P y → y = r₀

    -- P_normal : P r_n
    have eq_rn_r0 : r_n = r₀ := hr_unique _ P_normal
    -- P_zero : P 0
    have eq_0_r0  : 0   = r₀ := hr_unique _ P_zero

    -- conclude r_n = 0
    exact eq_rn_r0.trans eq_0_r0.symm

  · -- Direction (←): Assume `normalForm m G hGB.1 f = 0`. We must show `f ∈ I`.
    intro h_norm_is_zero

    have spec := normalForm_spec m hG_nonzero f
    let q := quotients m hG_nonzero f
    let r := normalForm m hG_nonzero f
    let g := q.sum fun i coeff => coeff • (i : MvPolynomial σ k)

    -- The division equation is `f = g + r`.
    have h_div_eq := spec.1

    rw [h_norm_is_zero] at h_div_eq
    simp at h_div_eq
    rw [h_div_eq]
    apply Submodule.sum_smul_mem I
    intro i _
    exact hGB.2.1 i.2

variable (m) in
/-- The S-polynomial. -/
noncomputable def S_polynomial (f g : MvPolynomial σ k) : MvPolynomial σ k :=
  monomial (m.degree f ⊔ m.degree g - m.degree f) ((m.leadingCoeff f)⁻¹ : k) * f
  - monomial (m.degree f ⊔ m.degree g - m.degree g) (( m.leadingCoeff g)⁻¹ : k) * g

omit [DecidableEq k] in
/--
**Lemma 5 (Cox, Little, O'Shea, Ch 2, §6, Lemma 5): Cancellation Lemma**
Suppose we have a sum P = ∑ pᵢ where all pᵢ have the same multidegree δ.
If m.degree P < δ, then P is a linear combination of the S-polynomials S(pⱼ, pₗ),
and each S(pⱼ, pₗ) has multidegree less than δ.
-/
lemma Spolynomial_syzygy_of_degree_cancellation
    {ι : Type*} [DecidableEq ι]
    (m : MonomialOrder σ)
    (δ : σ →₀ ℕ)
    -- (hδ : 0 ≺[m] δ)
    (p : ι →₀ MvPolynomial σ k) -- An indexed family with finite support
    (hp_ne_zero : ∀ i ∈ p.support, p i ≠ 0)
    (hp_deg : ∀ i ∈ p.support, m.degree (p i) = δ)
    (hsum   : m.degree (∑ i ∈ p.support, p i) ≺[m] δ)
    : (∃ (c : ι × ι → k),
      (∑ i ∈ p.support, p i = ∑ ij ∈ p.support.offDiag, c ij • S_polynomial m (p ij.1) (p ij.2))) ∧
      (∀ i ∈ p.support, ∀ j ∈ p.support, i ≠ j → m.degree (S_polynomial m (p i) (p j)) ≺[m] δ) := by
  constructor
  · -- ∃ (c : ι × ι → k)
    -- The case where the support is empty is trivial, as the sum is zero.
    by_cases h_supp_empty : p.support = ∅
    · rw [h_supp_empty]
      simp only [Finset.sum_empty, Finset.offDiag_empty, exists_const]

    -- Since the support is not empty, we can pick an element `s` to be our pivot,
    -- just like `pₛ` in the textbook's proof.
    let s := (Finset.nonempty_of_ne_empty h_supp_empty).choose
    have hs : s ∈ p.support := (Finset.nonempty_of_ne_empty h_supp_empty).choose_spec

    -- Let d i := LC(p i) be the leading coefficient of p i.
    let d : ι → k := fun i => m.leadingCoeff (p i)

    -- As in the textbook, the sum of these leading coefficients must be zero
    -- because the degree of the sum dropped.
    have h_sum_lc_zero : ∑ i ∈ p.support, d i = 0 := by
      have h_coeff_sum_zero : MvPolynomial.coeff δ (∑ i ∈ p.support, p i) = 0 :=
        m.coeff_eq_zero_of_lt hsum

      rw [MvPolynomial.coeff_sum] at h_coeff_sum_zero

      have h_coeff_eq_lc : ∀ i ∈ p.support, MvPolynomial.coeff δ (p i) = d i := by
        intro i hi
        dsimp [d]
        rw [leadingCoeff, hp_deg i hi]

      rwa [Finset.sum_congr rfl h_coeff_eq_lc] at h_coeff_sum_zero

    -- Since all `p i` have the same degree `δ`, their S-polynomial simplifies.
    have h_S_poly_simple : ∀ i ∈ p.support, ∀ j ∈ p.support, S_polynomial m (p i) (p j) = (d i)⁻¹ • p i - (d j)⁻¹ • p j := by
      intro i hi j hj
      unfold S_polynomial
      -- The sup of the degrees is δ.
      have h_deg_sup : m.degree (p i) ⊔ m.degree (p j) = δ := by
        simp [hp_deg i hi, hp_deg j hj]
      simp_rw [h_deg_sup, hp_deg i hi, hp_deg j hj, tsub_self, monomial_zero']
      dsimp [d]
      rw [MvPolynomial.C_mul', MvPolynomial.C_mul']

    -- The textbook shows that `∑ pᵢ` can be rewritten using S-polynomials involving `pₛ`.
    have h_sum_reduces : ∑ i ∈ p.support, p i = ∑ i ∈ (p.support.erase s), d i • S_polynomial m (p i) (p s) := by
      -- We expand the RHS and show it equals the LHS.
      have h_d_ne_zero : ∀ i ∈ p.support, d i ≠ 0 := fun i hi => leadingCoeff_ne_zero_iff.mpr (hp_ne_zero i hi)
      -- Expand S-polynomials: `∑ dᵢ • ((1/dᵢ)pᵢ - (1/dₛ)pₛ)`

      have expand_sum1 : ∑ i ∈ p.support.erase s, d i • S_polynomial m (p i) (p s)
        = ∑ i ∈ p.support.erase s, (p i - ((d i) * (d s)⁻¹) • p s) := by
          apply Finset.sum_congr rfl
          intro x hx
          have : x ∈ p.support := by exact Finset.mem_of_mem_erase hx
          rw [h_S_poly_simple x (Finset.mem_of_mem_erase hx) s hs]
          rw [MvPolynomial.smul_eq_C_mul]
          rw [mul_sub_left_distrib]
          rw [MvPolynomial.smul_eq_C_mul, ←mul_assoc]
          rw [←MvPolynomial.C_mul]
          have : d x * (d x)⁻¹ = 1 := by exact
            CommGroupWithZero.mul_inv_cancel (d x) (h_d_ne_zero x this)
          rw [this]
          simp only [C_1, one_mul, sub_right_inj]
          rw [MvPolynomial.smul_eq_C_mul, ←mul_assoc]
          rw [←MvPolynomial.C_mul]
          exact C_mul'

      have expand_sum2 : ∑ i ∈ p.support.erase s, (p i - ((d i) * (d s)⁻¹) • p s)
          = ∑ i ∈ p.support.erase s, p i + ( - ∑ i ∈ p.support.erase s, (d i * ((d s)⁻¹))) • p s := by
            rw [Finset.sum_sub_distrib, neg_smul, Finset.sum_smul, sub_eq_add_neg]

      rw [expand_sum1, expand_sum2]
      have h_coeff_ps : - ∑ i ∈ p.support.erase s, d i * (d s)⁻¹ = 1 := by
        -- Factor out the constant `(d s)⁻¹`.
        rw [← Finset.sum_mul]
        have h_sum_erase : ∑ i ∈ p.support.erase s, d i = - (d s) := by
          rw [← add_right_inj (d s), add_comm, Finset.sum_erase_add p.support d hs, h_sum_lc_zero, add_neg_cancel]

        rw [h_sum_erase]
        rw [neg_mul, neg_neg]
        apply mul_inv_cancel₀
        -- We need to prove `d s ≠ 0`.
        exact leadingCoeff_ne_zero_iff.mpr (hp_ne_zero s hs)
      rw [h_coeff_ps, one_smul]
      exact Eq.symm (Finset.sum_erase_add p.support (⇑p) hs)

    -- Now, we construct the coefficient function `c` for the existential goal.
    -- The sum we proved is over `i` paired with a fixed `s`. The goal is a sum over all pairs `ij`.
    -- We define `c ij` to be `d i` if `j=s` and `i≠s`, and 0 otherwise.
    let c (ij : ι × ι) : k := if ij.2 = s ∧ ij.1 ∈ p.support.erase s then d ij.1 else 0
    use c
    dsimp [c]
    simp only [Finset.mem_erase, ne_eq, Finsupp.mem_support_iff, ite_smul, zero_smul]
    show ∑ i ∈ p.support, p i =
    ∑ x ∈ p.support.offDiag, if x.2 = s ∧ x.1 ∈ p.support.erase s then d x.1 • S_polynomial m (p x.1) (p x.2) else 0
    rw [h_sum_reduces]
    rw [← Finset.sum_filter]
    have h_filter_eq : (p.support.offDiag).filter (fun x => x.2 = s ∧ x.1 ∈ p.support.erase s) =
      (p.support.erase s).image (fun i => (i, s)) := by
      ext ij
      -- We need to prove `ij ∈ filter ↔ ij ∈ image`.
      -- simp only [Finset.mem_erase, Finsupp.mem_support_iff, Finset.mem_filter,
      --   Finset.mem_offDiag, Finset.mem_image]
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_offDiag]
      constructor
      · intro h
        use ij.1
        refine ⟨h.2.2, ?_⟩
        apply Prod.ext
        · rfl
        · rw [h.2.1]
      · intro h
        obtain ⟨i, hi_in_erase, h_ij_eq⟩ := h
        rw [←h_ij_eq]
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · -- `i ∈ p.support`
          exact Finset.mem_of_mem_erase hi_in_erase
        · -- `s ∈ p.support`
          exact hs
        · -- `i ≠ s`
          exact (Finset.mem_erase.mp hi_in_erase).1
        · -- Second, `ij.2 = s ∧ ij.1 ∈ p.support.erase s`.
          exact ⟨rfl, hi_in_erase⟩
    rw [h_filter_eq]
    have h_inj : (p.support.erase s).toSet.InjOn (fun i => (i, s))  := by
      intro x _ y _ h_eq
      -- `(x, s) = (y, s)` implies `x = y`.
      exact (Prod.ext_iff.mp h_eq).1
    rw [Finset.sum_image h_inj]
  · intro i hi j hj hij
    let f := p i; let g := p j
    -- S(f,g) is designed to cancel the leading terms of f and g.
    -- Since deg(f) = deg(g) = δ, the two parts of the S-poly subtraction
    -- also have degree δ and identical leading terms.
    let d_f := m.leadingCoeff f; let d_g := m.leadingCoeff g
    let term1 := (d_f)⁻¹ • f
    let term2 := (d_g)⁻¹ • g
    dsimp [S_polynomial]
    sorry


variable (m) [DecidableEq σ] in
/--
**Lemma 5 (Cox, Little, O'Shea, Ch 2, §6, Lemma 5): Cancellation Lemma**
Suppose we have a sum P = ∑ pᵢ where all pᵢ have the same multidegree δ.
If m.degree P < δ, then P is a linear combination of the S-polynomials S(pⱼ, pₗ),
and each S(pⱼ, pₗ) has multidegree less than δ.
-/
lemma exists_S_polynomial_syzygies
    (p : Finset (MvPolynomial σ k)) -- The list of polynomials p₁, ..., pₛ
    (hp : ∀ pi ∈ p, pi ≠ 0) -- Finset.nonempty_of_sum_ne_zero
    (δ : σ →₀ ℕ) -- The common multidegree
    (hδ : 0 ≺[m] δ)
    (hp_deg : ∀ pi ∈ p, m.degree pi = δ) -- All polynomials have multidegree δ
    (hsum   : m.degree (∑ pi ∈ p, pi) ≺[m] δ)
    : ∀ ps ∈ p,
      (∑ pi ∈ p, pi = ∑ pi ∈ p.erase ps, m.leadingCoeff pi • S_polynomial m pi ps
      ∧ ∀ pi ∈ p, ∀ pj ∈ p, m.degree (S_polynomial m pj pi) ≺[m] δ)
      := by
      intro ps hps
      let p' : Finset (MvPolynomial σ k) := p.erase ps
      have coeff_sum_zero : (∑ pi ∈ p, pi).coeff δ = 0 := by
        apply coeff_eq_zero_of_lt
        simpa using hsum
      -- But (∑ pi in p, pi).coeff δ = ∑ pi in p, pi.coeff δ by coeff_sum.
      have sum_of_coeffs : ∑ pi ∈ p, pi.coeff δ = 0 := by
        simp [coeff_sum] at coeff_sum_zero
        exact coeff_sum_zero
      -- 3)  Because m.degree pi = δ for each pi ∈ p, we have pi.coeff δ = m.leadingCoeff pi.
      have sum_lead_coeffs : ∑ pi ∈ p, m.leadingCoeff pi = 0 := by
        have eq_coeff_lead : ∀ pi ∈ p, pi.coeff δ = m.leadingCoeff pi := by
          intro pi hpi
          rw [leadingCoeff, hp_deg pi hpi]
        calc
          ∑ pi ∈ p, m.leadingCoeff pi = ∑ pi ∈ p, coeff δ pi := by exact Eq.symm (Finset.sum_congr rfl eq_coeff_lead)
          _ = 0 := by exact sum_of_coeffs

      have sum_split : ps + (∑ pi ∈ p', pi) = (∑ pi ∈ p, pi) := by
        -- p = p' ∪ {s}, disjointly.
        apply Finset.add_sum_erase
        exact hps

      have S_poly_simp : ∀ pi ∈ p, ∀ pj ∈ p, S_polynomial m pi pj = ((m.leadingCoeff pi)⁻¹) • pi - ((m.leadingCoeff pj)⁻¹) • pj := by
        intro pi hpi pj hpj
        unfold S_polynomial
        have deg_sup : m.degree pi ⊔ m.degree pj = δ := by
          simp only [hp_deg pi hpi, hp_deg pj hpj, le_refl, sup_of_le_left]
        simp only [hp_deg pi hpi, hp_deg pj hpj, le_refl, sup_of_le_left, tsub_self,
          monomial_zero'] -- , one_div
        rw [MvPolynomial.C_mul', MvPolynomial.C_mul']

      have expand_sum1 : ∑ pi ∈ p', (m.leadingCoeff pi) • S_polynomial m pi ps
        = ∑ pi ∈ p', m.leadingCoeff pi • (((m.leadingCoeff pi)⁻¹) • pi - ((m.leadingCoeff ps)⁻¹) • ps) := by
          apply Finset.sum_congr rfl
          intro x hxp'; congr
          apply S_poly_simp
          · exact Finset.mem_of_mem_erase hxp'
          · exact hps
          -- apply S_poly_simp (by exact Finset.mem_of_mem_erase hxp') hps
      have expand_sum2 : ∑ pi ∈ p', m.leadingCoeff pi • (((m.leadingCoeff pi)⁻¹) • pi - ((m.leadingCoeff ps)⁻¹) • ps)
        = ∑ pi ∈ p', (pi - (m.leadingCoeff pi * ((m.leadingCoeff ps)⁻¹)) • ps) := by
          apply Finset.sum_congr rfl
          intro x hxp'
          rw [smul_sub, ←smul_assoc, ←smul_assoc]
          simp
          have : (m.leadingCoeff x * (m.leadingCoeff x)⁻¹) = 1 := by
            refine IsUnit.mul_inv_cancel ?_
            refine isUnit_leadingCoeff.mpr ?_
            exact hp _ (by exact Finset.mem_of_mem_erase hxp')
          rw [this]
          simp only [one_smul]
      have expand_sum3 : ∑ pi ∈ p', (pi - (m.leadingCoeff pi * ((m.leadingCoeff ps)⁻¹)) • ps)
        = ∑ pi ∈ p', pi + ( - ∑ pi ∈ p', (m.leadingCoeff pi * ((m.leadingCoeff ps)⁻¹))) • ps := by
          rw [Finset.sum_sub_distrib, neg_smul, Finset.sum_smul, sub_eq_add_neg]
      have sum_lemma : - ∑ pi ∈ p', (m.leadingCoeff pi * ((m.leadingCoeff ps)⁻¹)) = 1 := by
        rw [←add_zero (- ∑ pi ∈ p', (m.leadingCoeff pi * ((m.leadingCoeff ps)⁻¹)))]
        have : (m.leadingCoeff ps) * (m.leadingCoeff ps)⁻¹ - (m.leadingCoeff ps) * (m.leadingCoeff ps)⁻¹ = 0 := by
          exact sub_eq_zero.mpr rfl
        rw [←this, sub_eq_neg_add, ←add_assoc]
        dsimp [p']
        rw [←neg_add]
        rw [Finset.sum_erase_add p _ hps, ←Finset.sum_mul]
        rw [sum_lead_coeffs]
        simp only [zero_mul, neg_zero, zero_add] -- , p'
        refine IsUnit.mul_inv_cancel ?_
        refine isUnit_leadingCoeff.mpr ?_
        exact hp ps hps
      simp only [sum_lemma, one_smul, p'] at expand_sum3 -- Finset.sum_sub_distrib
      rw [Finset.sum_erase_add] at expand_sum3
      clear sum_lemma
      constructor
      · rw [expand_sum1, expand_sum2, expand_sum3]
      · intro pi hpi pj hpj
        rw [S_poly_simp pj hpj pi hpi]
        have hi_unit : IsUnit (m.leadingCoeff pi) := (isUnit_leadingCoeff_iff_nonzero m pi).mpr (hp pi hpi)
        have hj_unit : IsUnit (m.leadingCoeff pj) := (isUnit_leadingCoeff_iff_nonzero m pj).mpr (hp pj hpj)
        have hji : m.degree pi ≤ m.degree pj := by
          have h₁ : m.degree pj = δ := by exact hp_deg pj hpj
          have h₂ : m.degree pi = δ := by exact hp_deg pi hpi
          rw [h₂, h₁]
        have : (m.toSyn 0 < m.toSyn δ) → δ ≠ 0 := by
          contrapose
          simp only [ne_eq, Decidable.not_not, map_zero, not_lt]
          intro hδ_zero
          rw [hδ_zero, ←m.eq_zero_iff]
          exact AddEquiv.map_zero m.toSyn
        have hj_deg_nz : m.degree pj ≠ 0 := by
          rw [hp_deg pj hpj]
          exact this hδ
        clear this
        have : IsRegular (m.leadingCoeff pj)⁻¹ := by
          refine isRegular_iff_ne_zero.mpr ?_
          exact inv_ne_zero (by exact leadingCoeff_ne_zero_iff.mpr (hp pj hpj))
        have h1' : m.degree (pj - ((m.leadingCoeff pj) * (m.leadingCoeff pi)⁻¹) • pi)
          = m.degree ((m.leadingCoeff pj)⁻¹ • (pj - ((m.leadingCoeff pj) * (m.leadingCoeff pi)⁻¹) • pi)) := by
            rw [MonomialOrder.degree_smul this]
        have h2' : (m.leadingCoeff pj)⁻¹ • (pj - ((m.leadingCoeff pj) * (m.leadingCoeff pi)⁻¹) • pi)
          = (m.leadingCoeff pj)⁻¹ • pj - (m.leadingCoeff pi)⁻¹ • pi := by
            rw [smul_sub]
            simp only [sub_right_inj]
            rw [←smul_assoc]
            simp only [smul_eq_mul, ←mul_assoc]
            have : (m.leadingCoeff pj)⁻¹ * (m.leadingCoeff pj) = 1 := by
              exact IsUnit.inv_mul_cancel hj_unit
            simp only [this, one_mul]
        rw [←h2', ←h1']
        have hi_deg_δ : m.degree pj = δ := by exact hp_deg pj hpj
        have hj_deg_δ : m.degree pi = δ := by exact hp_deg pi hpi
        have h3' : pj - ((m.leadingCoeff pj) * (m.leadingCoeff pi)⁻¹) • pi
          = m.reduce hi_unit pj := by
          rw [reduce, hi_deg_δ, hj_deg_δ]
          simp
          rw [←MvPolynomial.C_mul, MvPolynomial.C_mul', mul_comm]
        rw [h3']
        have : m.degree pj = δ := by exact hp_deg pj hpj
        rw [←hi_deg_δ]
        apply MonomialOrder.degree_reduce_lt hi_unit hji hj_deg_nz
      exact hps

variable (m) [Fintype σ] [DecidableEq σ] in
lemma leadingTerm_sum_of_max_degree'
  {f : MvPolynomial σ k}
  (H : MvPolynomial σ k → MvPolynomial σ k) (G : Finset (MvPolynomial σ k))
  (h_repr : f = ∑ g ∈ G, H g * g)
  (h_deg_eq_max : m.degree f = G.sup (fun g => m.degree (H g * g))) :
  leadingTerm m f = ∑ g ∈ G.filter (fun g => m.degree (H g * g) = m.degree f), leadingTerm m (H g * g) := by
    calc
    m.leadingTerm f = monomial (m.degree f) (m.leadingCoeff f) := by rw [leadingTerm]
    _ = monomial (G.sup (fun g => m.degree (H g * g))) (m.leadingCoeff (∑ g ∈ G, H g * g)) := by rw [h_deg_eq_max, h_repr]
    _ = ∑ g ∈ G.filter (fun g => m.degree (H g * g) = m.degree f), leadingTerm m (H g * g) := by sorry

  -- rw [leadingTerm, Finset.sum_filter]


  -- | empty => contradiction
  -- | insert a s ha ih =>
  --   rw [Finset.sup_insert]
  --   -- The sup is max (a, s.sup id).
  --   -- If s is empty, sup is just a.
  --   by_cases hs_empty : s = ∅
  --   · subst hs_empty
  --     simp
  --   · -- If s is not empty, we can use induction.
  --     have s_nonempty : s.Nonempty := Finset.nonempty_of_ne_empty hs_empty
  --     specialize ih s_nonempty
  --     -- The sup is max(a, s.sup id).
  --     -- `ih` tells us `s.sup id ∈ s`.
  --     -- We need to show `max(a, s.sup id)` is in `insert a s`.
  --     cases le_total a (s.sup id) with
  --     | inl h_le => -- max is s.sup id
  --       rw [max_eq_right h_le]
  --       apply Finset.mem_insert_of_mem
  --       exact ih
  --     | inr h_ge => -- max is a
  --       rw [max_eq_left h_ge]
  --       apply Finset.mem_insert_self

variable (m) [Fintype σ] [DecidableEq σ] in
/--
**(Cox, Little, O'Shea, Ch 2, §6, Theorem 6): Buchberger’s Criterion** :
Let `I` be a polynomial ideal and let `G` be a basis of `I` (i.e. `I =
ideal.span G`).
Then `G` is a Gröbner basis if and only if for  all pairs of distinct polynomials
`g₁, g₂ ∈ G`, the remainder on division of `S_polynomial g₁ g₂` by `G` is zero.
-/
theorem Buchberger_criterion'
  {I : Ideal (MvPolynomial σ k)}
  {G : Finset (MvPolynomial σ k)}
  (hG : ∀ g ∈ G, g ≠ 0)
  (hGI : I = Ideal.span G) :
  IsGroebnerBasis m I G ↔
    (∀ (g₁ g₂ : MvPolynomial σ k),
      g₁ ∈ G →
      g₂ ∈ G →
      g₁ ≠ g₂ → normalForm m hG (S_polynomial m g₁ g₂) = 0) := by
      constructor
      · -- (⇒)
        intro hGB g₁ g₂ hg₁ hg₂ hneq
        apply (mem_Ideal_iff_GB_normalForm_eq_zero hGB _).mp
        rw [S_polynomial]
        have hG_sub_I : G.toSet ⊆ I := by rw [hGI]; exact Ideal.subset_span
        exact sub_mem (Ideal.mul_mem_left _ _ (hG_sub_I hg₁)) (Ideal.mul_mem_left _ _ (hG_sub_I hg₂))
      · -- (⇐) If all S-polynomials reduce to 0, then G is a Gröbner basis.
        intro hS_poly
        rw [IsGroebnerBasis]
        have hG_sub_I : (↑G : Set (MvPolynomial σ k)) ⊆ I := by rw [hGI]; exact Ideal.subset_span
        refine ⟨hG, hG_sub_I, ?_⟩
        by_cases hG_empty : G = ∅
        · simp [hG_empty] at hGI
          rw [initialIdeal, hGI, hG_empty]
          simp
        -- We need to show `initialIdeal m I = Ideal.span (LT(G))`.
        -- The inclusion `Ideal.span(LT(G)) ⊆ initialIdeal m I` is straightforward.
        apply le_antisymm
        · apply Ideal.span_mono
          intro lt_g h_lt_g_mem
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at h_lt_g_mem
          obtain ⟨g, hg_in_G, rfl⟩ := h_lt_g_mem
          refine Set.mem_setOf.mpr ?_
          use g
          exact ⟨by exact hG_sub_I hg_in_G, by exact hG g hg_in_G, rfl⟩
        -- The difficult inclusion: `initialIdeal m I ⊆ Ideal.span (LT(G))`.
        -- This means for any non-zero `f ∈ I`, we must show `LT(f) ∈ ⟨LT(G)⟩`.
        rw [initialIdeal, Ideal.span_le]
        rw [Set.subset_def]
        intro LTf h_LTf_in_initI
        obtain ⟨f, hfI, hf_ne, hLTf⟩ := h_LTf_in_initI
        rw [←hLTf]; clear hLTf; clear LTf
        have hf_in_I := hfI
        rw [hGI, Ideal.span, Submodule.mem_span_finset] at hfI
        have h_image_nonempty_of_repr (H' : MvPolynomial σ k → MvPolynomial σ k) :
            (Finset.image (fun g ↦ m.degree (H' g * g)) G).Nonempty := by
          rw [Finset.image_nonempty]
          exact Finset.nonempty_of_ne_empty hG_empty

        obtain ⟨H, h_H_supp, h_f_eq⟩ := hfI

        let RepMaxSynDegrees : Set m.syn :=
          { δ_syn | ∃ (h : MvPolynomial σ k → MvPolynomial σ k),
              Function.support h ⊆ G ∧ f = (∑ g ∈ G, h g * g) ∧
              -- δ_syn is the sup of the degrees *in the synonym type*.
              δ_syn = (G.image (m.toSyn ∘ (fun g => m.degree (h g * g)))).sup id }

        have h_RepMaxSynDegrees_nonempty : RepMaxSynDegrees.Nonempty := by
          use (G.image (m.toSyn ∘ (fun g => m.degree (H g * g)))).sup id
          use H
          exact ⟨h_H_supp, h_f_eq.symm, rfl⟩

        let δ_syn_min := WellFounded.min (by exact wellFounded_lt) RepMaxSynDegrees h_RepMaxSynDegrees_nonempty

        -- obtain ⟨h_min, h_min_supp, h_f_eq_min, h_δ_syn_min_eq⟩ :=
        --   WellFounded.min_mem (by exact wellFounded_lt) RepMaxSynDegrees h_RepMaxSynDegrees_nonempty
        let δ_min := m.toSyn.symm δ_syn_min

        have h_δ_min_in_RepDegrees : δ_syn_min ∈ RepMaxSynDegrees := by
          exact WellFounded.min_mem wellFounded_lt RepMaxSynDegrees h_RepMaxSynDegrees_nonempty

        obtain ⟨h_min, h_supp_min, h_f_eq_min, h_δ_syn_min_eq⟩ := h_δ_min_in_RepDegrees
        have f_deg_le : m.toSyn (m.degree f) ≤ δ_syn_min := by
          -- The goal is `m.toSyn (m.degree f) ≤ δ_syn_min`.

          -- From `h_δ_min_in_RepDegrees`, we know there is a minimal representation.

          -- We use this specific representation of f.
          rw [h_f_eq_min]
          -- simp only [AddEquiv.apply_symm_apply, δ_min]
          apply le_trans (@degree_sum_le_syn σ m k _ (MvPolynomial σ k) G (fun g => h_min g * g))

          -- The goal after applying the lemma is:
          -- `(G.sup (fun i => m.toSyn (m.degree (h_min i * i)))) ≤ δ_syn_min`.

          -- From `h_δ_syn_min_eq`, we know the LHS is exactly `δ_syn_min`.
          rw [h_δ_syn_min_eq]
          refine le_of_eq ?_
          rw [eq_comm]
          apply Finset.sup_image

        -- have f_deg_le' : m.degree f ≼[m] δ_min := by
        --   rw [h_f_eq_min]

        --   apply le_trans (@degree_sum_le_syn σ m k _ (MvPolynomial σ k) G (fun g => h_min g * g))
        --   simp only [δ_min, AddEquiv.apply_symm_apply]
        --   rw [h_δ_syn_min_eq]
        --   refine le_of_eq ?_
        --   rw [eq_comm]
        --   apply Finset.sup_image

        have h_le : ∀ g ∈ G, m.toSyn (m.degree (h_min g * g)) ≤ δ_syn_min := by
          intro h hg
          rw [h_δ_syn_min_eq]
          rw [Finset.sup_image]
          simp only [CompTriple.comp_eq]
          exact @Finset.le_sup _ _ _ _ _ (m.toSyn ∘ fun g ↦ m.degree (h_min g * g)) _ (hg)

        -- have h_le' : ∀ g ∈ G, m.degree (h_min g * g) ≼[m] δ_min := by
        --   intro h hg
        --   simp only [δ_min, AddEquiv.apply_symm_apply]
        --   rw [h_δ_syn_min_eq]
        --   rw [Finset.sup_image]
        --   simp only [CompTriple.comp_eq]
        --   exact @Finset.le_sup _ _ _ _ _ (m.toSyn ∘ fun g ↦ m.degree (h_min g * g)) _ (hg)

        by_cases h_min_le_bot : δ_syn_min ≤ ⊥
        · have h_syn_min_eq_bot : δ_syn_min = ⊥ := by exact le_bot_iff.mp h_min_le_bot
          have h_min_eq_bot : δ_min = 0 := by exact (AddEquiv.map_eq_zero_iff m.toSyn.symm).mpr h_syn_min_eq_bot

          have f_deg_0 : (m.degree f) = 0 := by
            rw [h_syn_min_eq_bot] at f_deg_le
            rw [le_bot_iff] at f_deg_le
            exact (AddEquiv.map_eq_zero_iff m.toSyn).mp f_deg_le
          --rw [h_f_eq_min]
          rw [leadingTerm, f_deg_0]
          have h_f_is_const : f = C (m.leadingCoeff f) := eq_C_of_degree_eq_zero f_deg_0
          simp

          have g_deg_0 : ∀g ∈ G, m.toSyn (m.degree (h_min g * g)) = 0 := by
            intro g hg
            rw [h_syn_min_eq_bot] at h_le
            exact (MonomialOrder.eq_zero_iff m).mpr (h_le g hg)

          have h_exists_nonzero_term : ∃ g ∈ G, h_min g * g ≠ 0 := by
            -- We prove this by contradiction.
            by_contra h_all_terms_zero
            push_neg at h_all_terms_zero

            -- `h_all_terms_zero` is now `∀ g ∈ G, h_min g * g = 0`.
            -- Let's see what this implies for `f`.
            have h_f_is_zero : f = 0 := by
              -- We start with the representation of `f`.
              rw [h_f_eq_min]
              -- We use `Finset.sum_eq_zero` which requires proving each term is zero.
              apply Finset.sum_eq_zero
              intro g hg
              exact h_all_terms_zero g hg

            -- This contradicts our main hypothesis `hf_ne : f ≠ 0`.
            exact hf_ne h_f_is_zero

          -- Now we have a `g` for which the term is non-zero.
          obtain ⟨g₀, hg₀_in_G, h_term_ne_zero⟩ := h_exists_nonzero_term
          --have : g₀

          rw [h_f_eq_min]
          rw [MvPolynomial.C_eq_smul_one]

          have h_deg_g₀ : m.degree g₀ = 0 := by
            -- We know the degree of the product is 0.
            have h_term_deg_zero : m.degree (h_min g₀ * g₀) = 0 := by
              exact (AddEquiv.map_eq_zero_iff m.toSyn).mp (g_deg_0 g₀ hg₀_in_G)

            -- The degree of a product is the sum of degrees (for non-zero polynomials).
            -- We need to show `h_min g₀` and `g₀` are non-zero.
            have h_g₀_ne_zero : g₀ ≠ 0 := hG g₀ hg₀_in_G
            have h_h_min_g₀_ne_zero : h_min g₀ ≠ 0 := by
              -- If h_min g₀ = 0, then h_min g₀ * g₀ = 0, which contradicts `h_term_ne_zero`.
              contrapose! h_term_ne_zero
              rw [h_term_ne_zero, zero_mul]

            -- Now apply the degree of product rule.
            have h_deg_add := m.degree_mul h_h_min_g₀_ne_zero h_g₀_ne_zero
            rw [h_term_deg_zero] at h_deg_add
            have : m.degree (h_min g₀) = 0 ∧ m.degree g₀ = 0 := by exact add_eq_zero.mp (by exact id (Eq.symm h_deg_add))
            exact this.2

          have h_unit_g₀ : IsUnit (m.leadingTerm g₀) := by

            -- The leading term is `monomial 0 (leadingCoeff g₀)`.
            -- This is the same as `C (leadingCoeff g₀)`.
            rw [leadingTerm, h_deg_g₀]
            simp only [monomial_zero', isUnit_map_iff, isUnit_iff_ne_zero, ne_eq,
              leadingCoeff_eq_zero_iff]
            exact hG g₀ hg₀_in_G
          have : Ideal.span ((fun g ↦ m.leadingTerm g) '' G.toSet) = ⊤ := by
            apply Ideal.eq_top_of_isUnit_mem _ _ h_unit_g₀
            apply Ideal.subset_span
            rw [Set.mem_image]
            use g₀
            constructor
            · -- `g₀ ∈ G.toSet` is the same as `g₀ ∈ G`, which is `hg₀_in_G`.
              exact hg₀_in_G
            · rfl
          rw [this]
          exact Submodule.mem_top

        push_neg at h_min_le_bot
        by_cases h_deg_eq_δ_syn : m.toSyn (m.degree f) = δ_syn_min
        · have h_sup_is_achieved : ∃ g ∈ G, (m.toSyn (m.degree (h_min g * g))) = δ_syn_min := by
            by_contra h_not_achieved
            push_neg at h_not_achieved
            have h_g_lt_δ : ∀ g ∈ G, m.toSyn (m.degree (h_min g * g)) < δ_syn_min  := by
              intro g hg
              apply lt_of_le_of_ne ?_ (h_not_achieved g hg)
              exact h_le g hg

            clear h_not_achieved
            rw [h_f_eq_min] at h_deg_eq_δ_syn
            have h_deg_lt_δ : m.toSyn (m.degree (∑ g ∈ G, h_min g * g)) < δ_syn_min := by
              apply LE.le.trans_lt (m.degree_sum_le_syn G (fun i ↦ (h_min i) * i))
              rw [@Finset.sup_lt_iff _ _ _ _ G (fun i ↦ m.toSyn (m.degree (h_min i * i))) (δ_syn_min ) h_min_le_bot]
              exact h_g_lt_δ
            exact (Eq.not_lt h_deg_eq_δ_syn) h_deg_lt_δ
          obtain ⟨gᵢ,⟨hgᵢG, hgᵢ_δ_min_syn⟩⟩ := h_sup_is_achieved
          · -- have hgᵢ_δ_min : (m.degree (h_min gᵢ * gᵢ)) =  δ_min := by apply m.toSyn.injective; exact hgᵢ_δ_min_syn
            -- have h_deg_eq_δ : (m.degree f) = δ_min := by apply m.toSyn.injective; exact h_deg_eq_δ_syn
            have h_nzero_h_min_gᵢ : h_min gᵢ ≠ 0 := by
              by_contra h_zero_h_min_gᵢ
              rw [h_zero_h_min_gᵢ] at hgᵢ_δ_min_syn
              simp only [zero_mul, degree_zero, map_zero] at hgᵢ_δ_min_syn
              rw [←hgᵢ_δ_min_syn] at h_min_le_bot
              simp only [MonomialOrder.bot_eq_zero, lt_self_iff_false] at h_min_le_bot
            have : m.leadingTerm f = m.leadingTerm (h_min gᵢ * gᵢ) * C ((m.leadingCoeff f) * (m.leadingCoeff (h_min gᵢ * gᵢ))⁻¹):= by
              rw [leadingTerm, leadingTerm, mul_comm]
              rw [MvPolynomial.C_mul_monomial, mul_assoc]
              --nth_rw 2 [mul_comm]
              rw [leadingCoeff_mul h_nzero_h_min_gᵢ (hG gᵢ hgᵢG), mul_inv_rev, mul_assoc]
              nth_rw 3 [←mul_assoc]

              rw [inv_mul_cancel₀ (by exact leadingCoeff_ne_zero_iff.mpr h_nzero_h_min_gᵢ), one_mul]
              rw [inv_mul_cancel₀ (by exact leadingCoeff_ne_zero_iff.mpr (hG gᵢ hgᵢG)), mul_one]
              have hgᵢ_δ_min : (m.degree (h_min gᵢ * gᵢ)) =  δ_min := by
                apply m.toSyn.injective; rw [AddEquiv.apply_symm_apply]; exact hgᵢ_δ_min_syn
              have h_deg_eq_δ : (m.degree f) = δ_min := by
                apply m.toSyn.injective; rw [AddEquiv.apply_symm_apply]; exact h_deg_eq_δ_syn
              rw [hgᵢ_δ_min, h_deg_eq_δ]
            rw [this]
            apply Ideal.mul_mem_right
            rw [leadingTerm_mul (h_nzero_h_min_gᵢ) (hG gᵢ hgᵢG)]
            apply Ideal.mul_mem_left
            apply Submodule.mem_span_of_mem
            apply Finset.mem_image_of_mem _ hgᵢG

        · have f_deg_lt : m.toSyn (m.degree f) < δ_syn_min := by
            apply (LE.le.lt_iff_ne' f_deg_le).mpr (by exact fun a ↦ h_deg_eq_δ_syn (id (Eq.symm a)))
          clear f_deg_le; clear h_deg_eq_δ_syn
          let G_δ := G.filter (fun g => m.toSyn (m.degree (h_min g * g)) = δ_syn_min)
          have h_f_split : f = (∑ g ∈ G_δ, h_min g * g) + (∑ g ∈ G \ G_δ, h_min g * g) := by
            rw [h_f_eq_min]
            have : G = G_δ ∪ (G \ G_δ) := by
              refine Eq.symm (Finset.union_sdiff_of_subset ?_)
              exact Finset.filter_subset (fun g ↦ m.toSyn (m.degree (h_min g * g)) = δ_syn_min) G
            nth_rw 1 [this]
            rw [Finset.sum_union (by exact Finset.disjoint_sdiff)]
          have h_sdiff : G \ G_δ = G.filter (fun g => m.toSyn (m.degree (h_min g * g)) < δ_syn_min) := by
            dsimp [G_δ]
            -- We also know `m.degree (h_min g * g) ≼[m] δ_min` because δ_min is the maximum.
            have h_le : ∀ g ∈ G, m.toSyn (m.degree (h_min g * g)) ≤ δ_syn_min := by
              intro h hg
              rw [h_δ_syn_min_eq]
              rw [Finset.sup_image]
              simp only [CompTriple.comp_eq]
              exact @Finset.le_sup _ _ _ _ _ (m.toSyn ∘ fun g ↦ m.degree (h_min g * g)) _ (hg)
            ext g
            -- We use `Finset.mem_filter` and `Finset.mem_sdiff` to simplify the goal.
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            constructor
            · -- Direction (→): Assume `g ∈ G \ G_δ`.
              intro h_left
              -- `h_left` is `⟨g ∈ G, g ∉ G_δ⟩`.
              -- We need to prove `g ∈ G` (which is `h_left.1`) and `m.toSyn (d g) < δ_syn_min`.
              refine ⟨h_left.1, ?_⟩

              -- We know `g ∉ G_δ`, which means `¬(m.toSyn (d g) = δ_syn_min)`.
              have h_ne : ¬ (m.toSyn (m.degree (h_min g * g)) = δ_syn_min) := by
                simp only [not_and] at h_left
                apply h_left.2 h_left.1

              -- `a ≤ b` and `a ≠ b` implies `a < b` for a linear order.
              exact lt_of_le_of_ne (h_le g h_left.1) h_ne

            · -- Direction (←): Assume `g ∈ G.filter (...)`.
              intro h_right
              -- `h_right` is `⟨g ∈ G, m.toSyn (d g) < δ_syn_min⟩`.
              -- We need to prove `g ∈ G \ G_δ`, which is `g ∈ G` and `g ∉ G_δ`.
              refine ⟨h_right.1, ?_⟩

              -- To show `g ∉ G_δ`, we need to show `¬(m.toSyn (d g) = δ_syn_min)`.
              -- This follows directly from `m.toSyn (d g) < δ_syn_min`.
              simp only [not_and]
              intro hg
              exact ne_of_lt h_right.2

          have h_h_min_decomp : ∀ g, h_min g = leadingTerm m (h_min g) + (h_min g - leadingTerm m (h_min g)) := by
            intro g
            exact (add_sub_cancel _ _).symm

          let P₁ := ∑ g ∈ G_δ, leadingTerm m (h_min g) * g
          let P₂ := ∑ g ∈ G_δ, (h_min g - leadingTerm m (h_min g)) * g
          let P₃ := ∑ g ∈ G \ G_δ, h_min g * g

          have h_f_is_P123 : f = P₁ + P₂ + P₃ := by
            -- Start with the split sum for f.
            rw [h_f_split]
            -- Unfold S_δ.
            -- Rewrite the first sum using its decomposition.
            -- Unfold the definitions of P₁, P₂, P₃.
            dsimp [P₁, P₂, P₃]
            -- The goal is now `(a + b) + c = a + b + c`, which is true by associativity.
            rw [add_left_inj]
            rw [←Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro x
            rw [sub_mul]
            exact fun a ↦ Eq.symm (add_sub_cancel (m.leadingTerm (h_min x) * x) (h_min x * x))

          have hG_δ_deg : ∀ g ∈ G_δ, m.toSyn (m.degree (h_min g * g)) = δ_syn_min := by
            intro g hg
            simp only [G_δ, Finset.mem_filter] at hg
            exact hg.2

          have hP₃_deg_lt : m.toSyn (m.degree P₃) < δ_syn_min := by
            dsimp [P₃]
            apply lt_of_le_of_lt (m.degree_sum_le_syn (G \ G_δ) (fun g ↦ h_min g * g))
            rw [Finset.sup_lt_iff h_min_le_bot]
            intro g hg_sdiff
            rw [h_sdiff] at hg_sdiff
            simp only [Finset.mem_filter] at hg_sdiff
            exact hg_sdiff.2

          have hP₂_deg_lt : m.toSyn (m.degree P₂) < δ_syn_min := by
            have h_term_deg_lt : ∀ g ∈ G_δ, m.toSyn (m.degree ((h_min g - leadingTerm m (h_min g)) * g)) < δ_syn_min := by
              intro g hg_in_G_δ

              -- We need `h_min g` to be non-zero to use `degree_sub_LTerm_lt`.
              have h_h_min_g_ne_zero : h_min g ≠ 0 := by
                -- If `h_min g` were zero, deg(0*g)=0, so `δ_syn_min` would be 0, contradicting `h_min_le_bot`.
                intro h_h_zero
                have hg_prop := (Finset.mem_filter.mp hg_in_G_δ).2
                rw [h_h_zero, zero_mul, degree_zero, map_zero] at hg_prop
                exact not_le_of_gt h_min_le_bot (le_of_eq hg_prop.symm)
              -- We consider two cases for the degree of `h_min g`.
              by_cases h_deg_h_min_g_zero : m.degree (h_min g) = 0
              · -- Case 1: `deg(h_min g) = 0`.
                -- Then `h_min g` is a constant, so `h_min g = LT(h_min g)`.
                have : h_min g = leadingTerm m (h_min g) := by
                  apply m.eq_leadingTerm_of_degree_zero h_deg_h_min_g_zero
                rw [this]
                rw [sub_eq_zero_of_eq (congrArg m.leadingTerm this)]
                simp only [zero_mul, degree_zero, map_zero, gt_iff_lt]
                exact h_min_le_bot

              · -- Case 2: `deg(h_min g) ≠ 0`.
                -- Now we can use `degree_sub_LTerm_lt`.
                have h_sub_lt : m.degree (h_min g - leadingTerm m (h_min g)) ≺[m] m.degree (h_min g) :=
                  degree_sub_LTerm_lt h_deg_h_min_g_zero
                by_cases h_sub_zero : (h_min g - leadingTerm m (h_min g)) = 0
                · rw [h_sub_zero, zero_mul, degree_zero, map_zero]
                  exact h_min_le_bot

                · rw [←(hG_δ_deg g hg_in_G_δ)]
                  rw [degree_mul h_sub_zero (hG g (h_supp_min h_h_min_g_ne_zero))]
                  rw [degree_mul h_h_min_g_ne_zero (hG g (h_supp_min h_h_min_g_ne_zero))]
                  simp only [map_add, add_lt_add_iff_right, gt_iff_lt]
                  exact h_sub_lt
            dsimp [P₂]
            apply lt_of_le_of_lt (m.degree_sum_le_syn G_δ fun g ↦ (h_min g - m.leadingTerm (h_min g)) * g)
            rw [Finset.sup_lt_iff h_min_le_bot]
            exact h_term_deg_lt

          have hP₁_deg_lt : m.toSyn (m.degree P₁) < δ_syn_min := by
            have h_P1_eq_sub : P₁ = f - (P₂ + P₃) := by
              rw [h_f_is_P123, add_sub_add_right_eq_sub, add_sub_cancel_right]

            rw [h_P1_eq_sub]

            have h_deg_P2_plus_P3_lt : m.toSyn (m.degree (P₂ + P₃)) < δ_syn_min := by
              exact m.degree_add_lt_of_le_lt hP₂_deg_lt hP₃_deg_lt

            apply lt_of_le_of_lt (m.degree_sub_le)
            rw [max_lt_iff]
            exact ⟨f_deg_lt, h_deg_P2_plus_P3_lt⟩

          -- let p : MvPolynomial σ k → MvPolynomial σ k := fun g ↦ m.leadingTerm ((h_min g) * g)
          let p_set := (G_δ).image (fun g => m.leadingTerm ((h_min g) * g))
          have hp_set : ∀ h_min_gi ∈ p_set, h_min_gi ≠ 0 := by
            intro h_min_gi h_min_gi_mem
            dsimp [p_set] at h_min_gi_mem
            simp only [Finset.mem_image] at h_min_gi_mem
            obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := h_min_gi_mem
            rw [←ha₂]
            rw [Finset.mem_filter] at ha₁
            intro h_lt_is_zero
            have h_eq_zero : h_min a * a = 0 := by exact m.leadingTerm_eq_zero_imp_eq_zero h_lt_is_zero
            simp only [h_eq_zero, degree_zero, map_zero] at ha₁
            apply Eq.not_lt ha₁.2
            exact h_min_le_bot

          have P₁_rw : P₁ = ∑ h_g ∈ p_set, h_g := by
            dsimp [P₁, p_set]
            sorry

          have S_polynomial_syzygies :
            ∀ ps ∈ p_set,
            (∑ pi ∈ p_set, pi = ∑ pi ∈ p_set.erase ps, m.leadingCoeff pi • S_polynomial m pi ps
            ∧ ∀ pi ∈ p_set, ∀ pj ∈ p_set, m.degree (S_polynomial m pj pi) ≺[m] δ_min) := by
            have h_min_le_bot' : 0 ≺[m] δ_min := by simp [δ_min]; exact h_min_le_bot
            have hG_δ_deg' : ∀ pi ∈ p_set, m.degree pi = δ_min := by
              intro pi hpi
              dsimp [p_set] at hpi
              simp only [Finset.mem_image] at hpi
              obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := hpi
              rw [←ha₂]
              rw [Finset.mem_filter] at ha₁
              simp only [degree_leadingTerm]
              dsimp [δ_min]
              apply (AddEquiv.eq_symm_apply m.toSyn).mpr ha₁.2

            have : m.toSyn (m.degree (∑ pi ∈ p_set, pi)) < m.toSyn δ_min := by
              apply lt_of_le_of_lt (m.degree_sum_le_syn p_set _)
              dsimp [p_set]
              simp only [Finset.sup_image]
              have : ((fun (i : MvPolynomial σ k) ↦ m.toSyn (m.degree i)) ∘ fun g ↦ m.leadingTerm (h_min g * g))
                = fun g ↦ m.toSyn (m.degree (h_min g * g)) := by sorry
              rw [this]
              sorry

            exact exists_S_polynomial_syzygies m p_set hp_set δ_min h_min_le_bot' hG_δ_deg' this
          /-lemma exists_S_polynomial_syzygies
    (p : Finset (MvPolynomial σ k)) -- The list of polynomials p₁, ..., pₛ
    (hp : ∀ pi ∈ p, pi ≠ 0) -- Finset.nonempty_of_sum_ne_zero
    (δ : σ →₀ ℕ) -- The common multidegree
    (hδ : 0 ≺[m] δ)
    (hp_deg : ∀ pi ∈ p, m.degree pi = δ) -- All polynomials have multidegree δ
    (hsum   : m.degree (∑ pi ∈ p, pi) ≺[m] δ)
    : ∀ ps ∈ p,
      (∑ pi ∈ p, pi = ∑ pi ∈ p.erase ps, m.leadingCoeff pi • S_polynomial m pi ps
      ∧ ∀ pi ∈ p, ∀ pj ∈ p, m.degree (S_polynomial m pj pi) ≺[m] δ)-/

          sorry

variable (m) [Fintype σ] [DecidableEq σ] in
/--
**(Cox, Little, O'Shea, Ch 2, §6, Theorem 6): Buchberger’s Criterion** :
Let `I` be a polynomial ideal and let `G` be a basis of `I` (i.e. `I =
ideal.span G`).
Then `G` is a Gröbner basis if and only if for  all pairs of distinct polynomials
`g₁, g₂ ∈ G`, the remainder on division of `S_polynomial g₁ g₂` by `G` is zero.
-/
theorem Buchberger_criterion
  {I : Ideal (MvPolynomial σ k)}
  {G : Finset (MvPolynomial σ k)}
  (hG : ∀ g ∈ G, g ≠ 0)
  (hGI : I = Ideal.span G) :
  IsGroebnerBasis m I G ↔
    (∀ (g₁ g₂ : MvPolynomial σ k),
      g₁ ∈ G →
      g₂ ∈ G →
      g₁ ≠ g₂ → normalForm m hG (S_polynomial m g₁ g₂) = 0) := by
      constructor
      · -- (⇒)
        intro hGB g₁ g₂ hg₁ hg₂ hneq
        apply (mem_Ideal_iff_GB_normalForm_eq_zero hGB _).mp
        rw [S_polynomial]
        have hG_sub_I : G.toSet ⊆ I := by rw [hGI]; exact Ideal.subset_span
        exact sub_mem (Ideal.mul_mem_left _ _ (hG_sub_I hg₁)) (Ideal.mul_mem_left _ _ (hG_sub_I hg₂))
      · -- (⇐) If all S-polynomials reduce to 0, then G is a Gröbner basis.
        intro hS_poly
        rw [IsGroebnerBasis]
        have hG_sub_I : (↑G : Set (MvPolynomial σ k)) ⊆ I := by rw [hGI]; exact Ideal.subset_span
        refine ⟨hG, hG_sub_I, ?_⟩

        -- We need to show `initialIdeal m I = Ideal.span (LT(G))`.
        -- The inclusion `Ideal.span(LT(G)) ⊆ initialIdeal m I` is straightforward.
        apply le_antisymm
        · apply Ideal.span_mono
          intro lt_g h_lt_g_mem
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at h_lt_g_mem
          obtain ⟨g, hg_in_G, rfl⟩ := h_lt_g_mem
          refine Set.mem_setOf.mpr ?_
          use g
          exact ⟨by exact hG_sub_I hg_in_G, by exact hG g hg_in_G, rfl⟩

        -- The difficult inclusion: `initialIdeal m I ⊆ Ideal.span (LT(G))`.
        -- This means for any non-zero `f ∈ I`, we must show `LT(f) ∈ ⟨LT(G)⟩`.
        rw [initialIdeal, Ideal.span_le]
        rw [Set.subset_def]
        intro LTf h_LTf_in_initI
        obtain ⟨f, hfI, hf_ne, hLTf⟩ := h_LTf_in_initI
        rw [←hLTf]; clear hLTf; clear LTf
        by_cases hG_empty : G = ∅
        · simp [hG_empty] at hGI
          simp [hGI] at hfI
          exact False.elim (hf_ne hfI)
        rw [hGI] at hfI
        rw [Ideal.span, Submodule.mem_span_finset] at hfI
        have h_image_ne_empty :
          ∀ (H' : MvPolynomial σ k → MvPolynomial σ k),
            (Function.support H' ⊆ G ∧ f = (∑ g ∈ G, H' g * g)) →
          Finset.image (fun g ↦ m.degree (H' g * g)) G ≠ ∅ := by
          intro H' f_repr
          apply Finset.nonempty_iff_ne_empty.mp
          rw [Finset.image_nonempty]
          exact Finset.nonempty_iff_ne_empty.mpr hG_empty
        have h_deg_ineq :
          ∀ (H' : MvPolynomial σ k → MvPolynomial σ k),
            (Function.support H' ⊆ G ∧ f = (∑ g ∈ G, H' g * g)) →
            m.degree f ≼[m] (G.image (fun g => m.degree (H' g * g))).sup' (Finset.nonempty_of_ne_empty ?_) id := by
            intro H' f_repr
            rw [f_repr.2]
            apply le_trans (m.degree_sum_le G (fun g => H' g * g))
            apply m.toSyn_monotone
            apply le_of_eq
            let s' := Finset.image (fun g ↦ m.degree (H' g * g)) G
            have h_s'_nonempty : s'.Nonempty := by
              rw [Finset.image_nonempty]
              exact Finset.nonempty_iff_ne_empty.mpr hG_empty
            rw [Finset.sup'_eq_sup h_s'_nonempty id]
            rw [Finset.sup_image]
            simp only [CompTriple.comp_eq]
            show Finset.image (fun g ↦ m.degree (H' g * g)) G ≠ ∅
            sorry
        have h_image_nonempty_of_repr (H' : MvPolynomial σ k → MvPolynomial σ k) :
            (Finset.image (fun g ↦ m.degree (H' g * g)) G).Nonempty := by
          rw [Finset.image_nonempty]
          exact Finset.nonempty_of_ne_empty hG_empty

        -- Now, let's prove the inequality holds for any representation.
        have h_deg_ineq_for_any_repr :
          ∀ (H' : MvPolynomial σ k → MvPolynomial σ k),
            (f = (∑ g ∈ G, H' g * g)) →
            m.degree f ≼[m] (G.image (fun g => m.degree (H' g * g))).sup' (h_image_nonempty_of_repr H') id := by
            intro H' h_f_repr
            rw [h_f_repr]
            apply le_trans (m.degree_sum_le G (fun g => H' g * g))
            apply m.toSyn_monotone
            apply le_of_eq
            let s' := Finset.image (fun g ↦ m.degree (H' g * g)) G
            rw [Finset.sup'_eq_sup (h_image_nonempty_of_repr H') id]
            rw [Finset.sup_image]
            simp only [CompTriple.comp_eq]


        -- have h_deg_ineq' : (∃ (H' : MvPolynomial σ k → MvPolynomial σ k),
        --   Function.support H ⊆ G ∧ f = (∑ g ∈ G, H g * g)) →
        --   m.degree f ≼[m] (G.image (fun g => m.degree (H' g * g))).sup' (Finset.nonempty_of_ne_empty ?_) id := by
        --   intro f_repr
        --   obtain ⟨H', f_reps'⟩ := f_repr
        --   rw [f_reps'.2]
        --   apply le_trans (m.degree_sum_le G (fun g => H' g * g))
        --   apply m.toSyn_monotone
        --   apply le_of_eq
        --   let s' := Finset.image (fun g ↦ m.degree (H' g * g)) G
        --   have h_s'_nonempty : s'.Nonempty := by
        --     rw [Finset.image_nonempty]
        --     exact Finset.nonempty_iff_ne_empty.mpr hG_empty
        --   · rw [Finset.sup'_eq_sup h_s'_nonempty id]
        --   rw [Finset.sup_image]
        --   --simp only [CompTriple.comp_eq]
        --   have : (∃ H, Function.support H ⊆ ↑G ∧ f = ∑ g ∈ G, H g * g) := by
        --     use H'
        --   sorry


        let RepDegrees (f : MvPolynomial σ k) : Set (σ →₀ ℕ) :=
          { δ | ∃ (H : MvPolynomial σ k → MvPolynomial σ k),
              Function.support H ⊆ G ∧
              f = (∑ g ∈ G, H g * g) ∧
              δ = G.sup (fun g => m.degree (H g * g)) }

        obtain ⟨H, f_reps⟩ := hfI
        -- need one representation H and f_reps here so that makes RepDegrees nonempty.

        have h_RepDegrees_nonempty : (RepDegrees f).Nonempty := by
          use G.sup (fun g => m.degree (H g * g))
          use H
          exact ⟨f_reps.1, f_reps.2.symm, rfl⟩
        clear f_reps; clear H


        let RepDegreesSyn : Set m.syn := m.toSyn '' (RepDegrees f)

        have h_RepDegreesSyn_nonempty : RepDegreesSyn.Nonempty := by
          exact Set.image_nonempty.mpr h_RepDegrees_nonempty

        let δ_syn_min := WellFounded.min (by exact wellFounded_lt) RepDegreesSyn h_RepDegreesSyn_nonempty
        let δ_min := m.toSyn.symm δ_syn_min
        have h_δ_min_in_RepDegrees : δ_min ∈ RepDegrees f := by
          dsimp [δ_min]
          have : δ_syn_min ∈ RepDegreesSyn := by
            exact WellFounded.min_mem wellFounded_lt RepDegreesSyn h_RepDegreesSyn_nonempty
          rw [Set.mem_image m.toSyn (RepDegrees f)] at this
          obtain ⟨x, hx_in_Rep, hx_maps_to_min⟩ := this
          rw [← hx_maps_to_min]
          rw [m.toSyn.symm_apply_apply]
          exact hx_in_Rep


        have f_deg_le : m.degree f ≼[m] δ_min := by
          obtain ⟨h_min, h_supp_min, h_f_eq_min, h_δ_min_eq_repr⟩ := h_δ_min_in_RepDegrees
          rw [h_f_eq_min]
          apply le_trans (m.degree_sum_le G (fun g => h_min g * g))
          rw [h_δ_min_eq_repr]

        by_cases h_deg_eq_δ : m.degree f = δ_min
        obtain ⟨H_min, H_supp_min, h_f_eq_min, h_δ_min_eq_repr⟩ := h_δ_min_in_RepDegrees

        have h_sup_is_achieved : ∃ g ∈ G, m.degree (H_min g * g) = δ_min := by
          by_contra h_not_achieved
          push_neg at h_not_achieved
          let d := fun g => m.degree (H_min g * g)
          let d_syn := fun (g : MvPolynomial σ k) => (g.support.sup m.toSyn)
          have h_δ_is_sup : δ_min = G.sup d := h_δ_min_eq_repr

          have h_lt_δ_min : ∀ g ∈ G, (d g) ≺[m] δ_min := by
            intro g hg
            rw [h_δ_is_sup] -- Replace δ_min with the sup expression
            apply lt_of_le_of_ne
            · -- Prove `d g ≤ G.sup d`
              apply m.toSyn_monotone
              exact Finset.le_sup hg
            · -- Prove `d g ≠ G.sup d`
              intro h_eq_contra
              have h1 : m.degree (H_min g * g) ≠ G.sup d := by rw [←h_δ_is_sup]; exact h_not_achieved g hg
              exact h1 (m.toSyn.injective h_eq_contra)

          have h_sup_lt_δ_min : (G.sup d) ≺[m] δ_min := by
            --rw [@Finset.sup_lt_iff m.syn (MvPolynomial σ k) m.lo _ G (m.toSyn ∘ d) (m.toSyn δ_min) _]
            sorry



          -- We will prove `m.toSyn (s.sup d) < m.toSyn δ_min` for all non-empty `s ⊆ G`.
          have h_sup_lt_δ_min : (G.sup d) ≺[m] δ_min := by
            -- Let's define the property we want to prove by induction.
            let P (s : Finset (MvPolynomial σ k)) (hs : s.Nonempty) : Prop :=
              s ⊆ G → m.toSyn (s.sup d) < m.toSyn δ_min

            -- We prove `P s hs` for all non-empty `s` by `cons_induction`.
            suffices ∀ s (hs : s.Nonempty), P s hs by
              apply this G (Finset.nonempty_of_ne_empty hG_empty)
              exact Finset.Subset.refl G

            apply Finset.Nonempty.cons_induction
            · -- Base case: singleton {a}.
              intro a ha_sub_G
              -- Goal: `P {a} (singleton_nonempty a)`.
              -- This means `m.toSyn (d a) < m.toSyn δ_min`.
              rw [Finset.sup_singleton]
              -- We need `a ∈ G` to use `h_lt_δ_min`.
              have ha_in_G : a ∈ G := by
                rw [Finset.singleton_subset_iff] at ha_sub_G
                exact ha_sub_G
              exact h_lt_δ_min a ha_in_G
            · -- Inductive step: `cons a s h hs ih`.
              intro a s ha_not_in_s hs_nonempty ih ha_cons_sub_G
              -- `ih` is `P s hs`, which is `s ⊆ G → m.toSyn (s.sup d) < m.toSyn δ_min`.
              sorry

          -- The final contradiction.
          rw [h_δ_is_sup] at h_sup_lt_δ_min
          exact lt_irrefl _ h_sup_lt_δ_min


        have h_sup_is_achieved : ∃ g ∈ G, m.degree (H_min g * g) = δ_min := by
          by_contra h_not_achieved

          -- Our assumption is that for all `g`, the degree is not equal to the sup.
          push_neg at h_not_achieved

          -- Let `d g := m.degree (h_min g * g)`.
          let d := fun g => m.degree (H_min g * g)
          -- We know `δ_min = G.sup d`.
          have h_δ_is_sup : δ_min = G.sup d := h_δ_min_eq_repr
          --rw [h_δ_min_eq_repr] at h_not_achieved

          have h_lt_sup : ∀ g ∈ G, (d g) ≺[m] δ_min := by
            intro g hg
            rw [h_δ_is_sup] -- Replace δ_min with the sup expression
            apply lt_of_le_of_ne
            · -- Prove `d g ≤ G.sup d`
              apply m.toSyn_monotone
              exact Finset.le_sup hg
            · -- Prove `d g ≠ G.sup d`
              intro h_eq_contra
              have h1 : m.degree (H_min g * g) ≠ G.sup d := by rw [←h_δ_is_sup]; exact h_not_achieved g hg
              exact h1 (m.toSyn.injective h_eq_contra)
          have h_sup_lt_δ_min : G.sup d ≺[m] δ_min := by
            -- We will prove `m.toSyn (s.sup d) < m.toSyn δ_min` by induction on s.
            let P (s : Finset (MvPolynomial σ k)) : Prop := m.toSyn (s.sup d) < m.toSyn δ_min
            suffices P G by exact this
            induction G using Finset.induction_on with
            | empty => sorry
            | insert a s _ _ => sorry



          have h2 : ¬(G.sup d ≺[m] δ_min) := by
            apply Eq.not_lt
            exact congrArg (⇑m.toSyn) (id (Eq.symm h_δ_min_eq_repr))
          exact h2 h_sup_lt_δ_min

        sorry
        sorry


        -- -- By span_induction, we only need to prove it for the generators of `initialIdeal m I`.
        -- -- That is, for any non-zero `f ∈ I`, `leadingTerm m f` must be in the target ideal.
        -- apply Submodule.span_induction h_ltf_in_initI
        -- · -- **Step 1: Setup for the minimal representation argument.**
        --   -- Let `f ∈ I` be nonzero. We will show that `LT(f) ∈ <LT(G)>`.
        --   intro p hp
        --   obtain ⟨f, hf_in_I, hf_ne_zero, rfl⟩ := hp

        --   -- A "representation" of `f` is a map `h` such that `f = ∑ h_g * g`.
        --   -- Let `RepDegrees` be the set of all possible maximal degrees `δ` for representations of `f`.
        --   let RepDegrees (f : MvPolynomial σ k) : Set (σ →₀ ℕ) :=
        --     { δ | ∃ (h : MvPolynomial σ k →₀ MvPolynomial σ k),
        --         h.support ⊆ G ∧
        --         f = h.sum (fun g coeff => coeff * g) ∧
        --         δ = (h.support.image (fun g => m.degree (h g * g))).max' (by
        --           -- The set of degrees is non-empty if f is non-zero
        --           refine Finset.nonempty_image_iff.mpr ?_
        --           contrapose! hf_ne_zero
        --           rw [h.sum_eq_zero_iff_support_empty.mpr hf_ne_zero] at ‹_›
        --           exact hf_ne_zero) }

        --   -- Since `f ∈ I = span G`, at least one representation exists.
        --   have h_rep_exists : ∃ h, h.support ⊆ G ∧ f = h.sum (fun g c => c * g) := by
        --     rw [hGI, Ideal.mem_span_iff_exists_sum] at hf_in_I
        --     exact hf_in_I
        --   have h_RepDegrees_nonempty : (RepDegrees f).Nonempty := by
        --     obtain ⟨h, h_supp, h_f_eq⟩ := h_rep_exists
        --     use (h.support.image (fun g => m.degree (h g * g))).max' _
        --     exact ⟨h, h_supp, h_f_eq, rfl⟩

        --   -- **Step 2: Pick the most efficient representation.**
        --   -- The minimal `δ` exists by the well-ordering property of our monomial ordering.
        --   let δ_min := m.syn.wf.min (RepDegrees f) h_RepDegrees_nonempty

        --   -- We pick one representation for which `δ` is minimal.
        --   obtain ⟨h_min, h_supp_min, h_f_eq_min, h_δ_eq_min⟩ :=
        --     m.syn.wf.min_mem (RepDegrees f) h_RepDegrees_nonempty

        --   -- **Step 3: Analyze the minimal representation.**
        --   -- By definition, `multideg(f) ≤ δ_min`.
        --   have h_deg_f_le_δ : m.degree f ≼[m] δ_min := by
        --     rw [h_f_eq_min]
        --     apply le_trans (m.degree_sum_le _)
        --     rw [h_δ_eq_min]
        --     apply Finset.sup_le_iff.mpr
        --     intro g hg
        --     exact Finset.le_max' (Finset.mem_image_of_mem _ hg)

        --   -- We will show the case `multideg(f) < δ_min` leads to a contradiction.
        --   -- This implies `multideg(f) = δ_min` must hold for a minimal representation.
        --   by_cases h_deg_eq_δ : m.degree f = δ_min

        --   · -- **Case 1: `multideg(f) = δ_min` (No cancellation).**
        --     -- This easily implies that `LT(f)` is in `<LT(G)>`.
        --     -- `LT(f) = LT(∑ h_g * g) = ∑_{deg(h_g*g)=δ_min} LT(h_g * g)`.
        --     have h_lt_sum : leadingTerm m f =
        --       ∑ g in h_min.support.filter (fun g => m.degree (h_min g * g) = δ_min),
        --         leadingTerm m (h_min g * g) := by
        --       -- This relies on a helper lemma about leading terms of sums where
        --       -- the max degree is achieved.
        --       sorry -- `leadingTerm_sum_of_max_degree`

        --     rw [h_lt_sum]
        --     -- Each term `LT(h_g * g)` is in the ideal `<LT(G)>`.
        --     apply Ideal.sum_mem
        --     intro g hg_in_filter
        --     have : leadingTerm m (h_min g * g) ∈ Ideal.span (G.image (fun g => leadingTerm m g)) := by
        --       have hg_in_G : g ∈ G := h_supp_min (Finset.mem_of_mem_filter hg_in_filter)
        --       have h_lt_prod : leadingTerm m (h_min g * g) = leadingTerm m (h_min g) * leadingTerm m g := by
        --         -- This requires `leadingCoeff(h) * leadingCoeff(g) ≠ 0`.
        --         sorry -- `leadingTerm_mul`
        --       rw [h_lt_prod]
        --       apply Ideal.mul_mem_left
        --       apply Ideal.subset_span
        --       exact Finset.mem_image_of_mem _ hg_in_G
        --     exact this

        --   · -- **Case 2: `multideg(f) < δ_min` (Cancellation).**
        --     -- This will contradict the minimality of `δ_min`.
        --     have h_deg_lt_δ : m.toSyn (m.degree f) < m.toSyn δ_min :=
        --       lt_of_le_of_ne (m.toSyn.monotone h_deg_f_le_δ) (by rwa [Ne, EmbeddingLike.apply_eq_iff_eq])

        --     -- We will use `S(gᵢ,gⱼ) mod G = 0` to find a new expression for `f`
        --     -- that decreases `δ_min`.

        --     -- This part of the proof requires a very detailed construction of the new representation
        --     -- using the cancellation lemma and the S-polynomial reduction property. It's famously
        --     -- complex to formalize.
        --     sorry

        -- · -- The other cases for `span_induction` are trivial.
        --   intro p q hp hq
        --   exact Ideal.add_mem _ hp hq
        -- · intro c p hp
        --   exact Ideal.smul_mem _ c hp


      -- · -- (⇐)
      --   intro hS_poly
      --   rw [IsGroebnerBasis]
      --   have hG_sub_I : G.toSet ⊆ I := by rw [hGI]; exact Ideal.subset_span
      --   constructor
      --   · exact hG
      --   · constructor
      --     · exact hG_sub_I
      --     · rw [initialIdeal, hGI]
      --       --nth_rw 3 [Ideal.span]
      --       --apply subset_antisymm
      --       ext LTf
      --       constructor
      --       · apply Ideal.span_mono
      --         clear LTf
      --         refine Set.subset_setOf.mpr ?_
      --         intro LTg LTG_in
      --         simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at LTG_in
      --         obtain ⟨g, hg⟩ := LTG_in
      --         use g
      --         constructor
      --         · rw [←hGI]; exact hG_sub_I hg.1
      --         · exact And.imp_left (hG g) hg
      --       · intro hmem              -- We need to show that `LTf` is in `Ideal.span (G.image (leadingTerm m))`.
      --         nth_rw 2 [Ideal.span] at hmem

      --         -- Can we use Submodule.mem_span_finset
      --         -- at hmem : LTf ∈ Ideal.span {f | ∃ g ∈ Submodule.span (MvPolynomial σ k) ↑G, g ≠ 0 ∧ m.leadingTerm g = f} ?
      --         sorry


            -- · intro h_LTf_G
            --   have : (Finset.image (fun g ↦ m.leadingTerm g) G).toSet ⊆ {f | ∃ g ∈ Submodule.span (MvPolynomial σ k) ↑G, g ≠ 0 ∧ m.leadingTerm g = f} := by sorry
            --   have : Ideal.span (Finset.image (fun g ↦ m.leadingTerm g) G)
            --     ≤ Ideal.span {f | ∃ g ∈ Submodule.span (MvPolynomial σ k) G.toSet, g ≠ 0 ∧ m.leadingTerm g = f} := by
            --       exact Ideal.span_mono this
            --   exact this h_LTf_G
            --rw [Submodule.mem_span_finset]

            -- · sorry
            -- · intro h_LTf_inI
            --   rw [initialIdeal, hGI] at h_LTf_inI
            --   simp only [ne_eq] at h_LTf_inI

            --   have : ∃ f ∈ I, m.leadingTerm f = LTf := by
            --     rw [Ideal.mem_span_singleton_self] at h_LTf_inI
            --   obtain  ⟨f, hfI, h_LTf⟩ := this
            --   obtain ⟨c, hc, hsum⟩ := Submodule.mem_span_set.mp (by rw [hGI] at hfI; apply hfI)
            --   sorry

-- and now `f = ∑ q b • b` is exactly the representation you need.
-- /-forward 증명이 지저분-/
-- variable (m) [Fintype σ] [DecidableEq σ] in
-- theorem Buchberger_criterion_old
--   {I : Ideal (MvPolynomial σ k)}
--   {G : List (MvPolynomial σ k)}
--   (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
--   (hGI : I = Ideal.span G.toFinset) :
--   is_GroebnerBasis m I G ↔
--     (∀ (g₁ g₂ : MvPolynomial σ k),
--       g₁ ∈ G →
--       g₂ ∈ G →
--       g₁ ≠ g₂ →
--       remainder_old (S_polynomial m g₁ g₂) G hG = 0) := by
--         constructor
--         · intro h_isGB g₁ g₂ hg₁ hg₂ hneq
--           have : G.toFinset.toSet ⊆ I := by apply h_isGB.1
--           have hGsubI: ∀g ∈ G, g ∈ I := by
--             simp [SetLike.coe_subset_coe, ←SetLike.setOf_mem_eq] at this
--             exact fun g a ↦ this g a
--           have h_Sp: S_polynomial m g₁ g₂ ∈ I := by
--             rw [S_polynomial]
--             have hg₁I : g₁ ∈ I := by exact hGsubI g₁ hg₁
--             have hg₂I : g₂ ∈ I := by exact hGsubI g₂ hg₂
--             apply Ideal.sub_mem
--             · exact
--               Ideal.mul_mem_left I ((monomial (m.degree g₁ ⊔ m.degree g₂)) 1 - leadingTerm m g₁)
--                 (hGsubI g₁ hg₁)
--             · exact
--               Ideal.mul_mem_left I ((monomial (m.degree g₁ ⊔ m.degree g₂)) 1 - leadingTerm m g₂)
--                 (hGsubI g₂ hg₂)
--           exact (mem_ideal_iff_remainder_GB_eq_zero_old hG h_isGB (S_polynomial m g₁ g₂)).mp h_Sp
--         · intro hSpols
--           -- (1) every g ∈ G lies in I because I = span G
--           have hGsubI : G.toFinset.toSet ⊆ I := by
--             simpa [hGI] using Ideal.subset_span

--           -- (2) we must show
--           --     span (leadingTerm m '' G) = initialIdeal m I
--           have : initialIdeal m I = initialIdeal m (Ideal.span G.toFinset) := by
--             simp [hGI]
--           -- reduce to
--           --   span (LT G) = initialIdeal m (span G)
--           rw [is_GroebnerBasis]
--           constructor
--           · exact hGsubI
--           · sorry



-- variable (m) [Fintype σ]  [DecidableEq (MvPolynomial σ k)] in
-- theorem Buchberger_criterion_domain
--   {ι : Type*} {I : Ideal (MvPolynomial σ k)}
--   (G : ι →₀ MvPolynomial σ k)
--   (hG : I = Ideal.span (Set.range G)) :
--   is_GroebnerBasis_domain m I G ↔
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

/-
Implementation of Buchberger's Algorithm based on the provided pseudocode.
Input: F = a list of polynomials (generators of the ideal I)
Output: G = a Gröbner basis for I such that F ⊆ G
-/

/- Buchberger's Algorithm to compute a Gröbner basis. -/
/-Id.run do 사용 안함, List 없이 쓰려면?-/
-- variable [DecidableEq (σ →₀ ℕ)] [DecidableEq (MvPolynomial σ k)] in
-- noncomputable def Buchberger (F : List (MvPolynomial σ k)) : List (MvPolynomial σ k) :=
--   let G₀ := F
--   let rec loop (G : List (MvPolynomial σ k)) : List (MvPolynomial σ k) :=
--     let G' := G
--     -- Generate pairs {p, q}, p ≠ q in G'
--     let pairs := G'.tails.flatMap (fun tail =>
--       match tail with
--       | [] => []
--       | p :: ps => ps.map (fun q => (p, q)) -- Pair p with every q after it
--     )
--     -- Process pairs iteratively (simulating the FOR loop)
--     let rec processPairs (currentG : List (MvPolynomial σ k)) (pairsToProcess : List (MvPolynomial σ k × MvPolynomial σ k)) : List (MvPolynomial σ k) :=
--       match pairsToProcess with
--       | [] => currentG -- No more pairs for this iteration, return the potentially updated G
--       | (p, q) :: restOfPairs =>
--           -- Assume polynomials in G are non-zero for remainder calculation (or handle zero case in remainder)
--           -- have hG_nonzero : ∀ g ∈ currentG, g ≠ 0 := sorry -- Requires proof or assumption management
--           have hG_nonzero : ∀ b ∈ currentG, IsUnit (m.leadingCoeff b) := by sorry
--           -- r := remainder(S(p, q), G') -- Use currentG for division
--           let r := remainder (S_polynomial m p q) currentG hG_nonzero
--           -- IF r ≠ 0 THEN G := G ∪ {r}
--           if hr : r ≠ 0 then
--             -- Need to re-run the whole process with the new G
--             -- The pseudocode implies a REPEAT-UNTIL structure which means we restart the pair checking
--             let G_new := currentG ++ [r] -- Add r to G
--             loop G_new -- Restart the outer loop with the new G
--           else
--             -- Remainder is 0, continue processing the rest of the pairs for *this* iteration
--             processPairs currentG restOfPairs

--     -- Start processing pairs for the current G
--     let G_next := processPairs G pairs
--     -- UNTIL G = G' (Check if G changed in this iteration)
--     if G_next == G' then
--       G' -- G did not change, terminate and return G'
--     else
--       -- G changed (implicitly handled by restarting loop in processPairs when r ≠ 0)
--       -- If processPairs finishes *without* finding a non-zero remainder, G_next will equal G'
--       G_next -- Should be G' if no change occurred

--   -- Initial call to the loop
--   loop G₀
-- termination_by sorry

partial def Buchberger_Algorithm (F : List (MvPolynomial σ k)) : List (MvPolynomial σ k) := by sorry
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

variable [DecidableEq σ] in
lemma grobner_basis_remove_redundant
  {I : Ideal _} {G : Finset _} {p : MvPolynomial σ k}
  (hG : IsGroebnerBasis m I G)
  (hpG : p ∈ G)
  (hLT : leadingTerm m p ∈ Ideal.span ((G.erase p).image (fun g ↦ leadingTerm m g))) :
  IsGroebnerBasis m I (G.erase p) := by sorry

-- variable [DecidableEq σ] in
-- lemma grobner_basis_remove_redundant_old
--   {I : Ideal (MvPolynomial σ k)} {G : List (MvPolynomial σ k)} {p : MvPolynomial σ k}
--   (hG : is_GroebnerBasis m I G)
--   (hpG : p ∈ G)
--   (hLT : leadingTerm m p ∈ Ideal.span ((G.erase p).toFinset.image (fun g ↦ leadingTerm m g))) :
--   is_GroebnerBasis m I (G.erase p) := by sorry

end Field
end MvPolynomial
