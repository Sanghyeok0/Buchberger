import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Noetherian.Defs
-- import Mathlib.RingTheory.Polynomial.Basic
-- import Mathlib.Algebra.Ring.Defs
import Buchberger.MonomialIdeal
-- import Buchberger.Order2

variable {σ : Type*} -- [DecidableEq σ]
variable {m : MonomialOrder σ}

open MonomialOrder MvPolynomial

namespace MonomialOrder

set_option maxHeartbeats 0

/-
## Reference : [Cox, Little, and O'Shea 1997] [Becker-Weispfenning1993]
-/

section Semiring

variable {R : Type*} [CommSemiring R]

/-- The multidegree of the leading term `LT(f)` is equal to the degree of `f`. -/
lemma degree_leadingTerm (f : MvPolynomial σ R) :
    m.degree (leadingTerm m f) = m.degree f := by
  have : Decidable (m.leadingCoeff f = 0) := by exact Classical.propDecidable (m.leadingCoeff f = 0)
  rw [leadingTerm, m.degree_monomial]
  split_ifs with h_coeff_zero
  · rw [m.leadingCoeff_eq_zero_iff] at h_coeff_zero
    rw [h_coeff_zero, m.degree_zero]
  · rfl

variable {ι : Type*} [DecidableEq ι] in
lemma degree_sum_le (s : Finset ι) (f : ι → MvPolynomial σ R) :
    m.degree (∑ i ∈ s, f i) ≼[m] s.sup (fun i => m.degree (f i)) := by
  -- We proceed by induction on the finset `s`.
  induction s using Finset.induction_on with
  | empty =>
    simp [m.degree_zero]
    exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a ↦ a) rfl (m.toSyn ⊥)
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
          monomial_zero', one_div]
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
        simp only [zero_mul, neg_zero, zero_add, p']
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
/--
**Lemma 5 (Cox, Little, O'Shea, Ch 2, §6, Theorem 6): Buchberger’s Criterion** :
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
        -- This means for any non-zero `f ∈ I`, we must show `LT(f) ∈ <LT(G)>`.
        rw [initialIdeal, Ideal.span_le]
        rw [Set.subset_def]
        intro LTf h_LTf_in_initI
        obtain ⟨f, hfI, hf_ne, hLTf⟩ := h_LTf_in_initI
        by_cases hG_empty : G = ∅
        · simp [hG_empty] at hGI
          simp [hGI] at hfI
          exact False.elim (hf_ne hfI)
        rw [hGI] at hfI
        rw [Ideal.span, Submodule.mem_span_finset] at hfI
        obtain ⟨H, f_reps⟩ := hfI
        have : Finset.image (fun g ↦ m.degree (H g * g)) G ≠ ∅ := by
          apply Finset.nonempty_iff_ne_empty.mp
          rw [Finset.image_nonempty]
          exact Finset.nonempty_iff_ne_empty.mpr hG_empty
        have h_deg_ineq : m.degree f ≼[m] (G.image (fun g => m.degree (H g * g))).sup' (Finset.nonempty_of_ne_empty this) id := by
          rw [←f_reps.2]
          apply le_trans (m.degree_sum_le G (fun g => H g * g))
          apply m.toSyn_monotone
          apply le_of_eq
          let s' := Finset.image (fun g ↦ m.degree (H g * g)) G
          have h_s'_nonempty : s'.Nonempty := by
            rw [Finset.image_nonempty]
            exact Finset.nonempty_iff_ne_empty.mpr hG_empty
          rw [Finset.sup'_eq_sup h_s'_nonempty]
          rw [Finset.sup_image]
          simp only [CompTriple.comp_eq]

        -- Let δ be the maximal degree in our given representation.
        let δ := G.sup (fun g => m.degree (H g * g))
        let P (δ' : σ →₀ ℕ) : Prop :=
          ∀ (f' : MvPolynomial σ k) (h' : MvPolynomial σ k → MvPolynomial σ k),
            -- Given f' and a representation h'
            (f' ∈ I ∧ f' ≠ 0 ∧ Function.support h' ⊆ G ∧ f' = ∑ g ∈ G, h' g * g) →
            -- such that the maximal degree of the representation is δ'
            (G.sup (fun g => m.degree (h' g * g)) = δ') →
              leadingTerm m f' ∈ Ideal.span (G.image (fun g => leadingTerm m g))
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
