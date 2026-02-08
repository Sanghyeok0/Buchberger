module

public import Buchberger.Finset
public import Buchberger.MonomialIdeal
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.MvPolynomial.Groebner

@[expose] public section

/-!
# The Division Algorithm and Buchberger's Criterion

This file defines the multivariate division algorithm (`normalForm`) and proves
the main theorem of Gröbner basis theory: Buchberger's Criterion.

## Main Definitions
- `MvPolynomial.normalForm`: Computes the remainder of a polynomial `f` upon division
  by a set of polynomials `B`. This is often called the "normal form" of `f`.
- `MvPolynomial.IsGroebnerBasis`: Defines a Gröbner basis `G` for an ideal `I` as a
  basis whose leading terms generate the initial ideal of `I`.
- `MonomialOrder.S_polynomial`: The S-polynomial of two polynomials `f` and `g`.

## Main Results
- `MvPolynomial.normalForm_spec`: Guarantees that the `normalForm` function satisfies
  the properties of the division algorithm (the division equation, the degree condition,
  and the remainder condition).
- `MvPolynomial.normalForm_exists_unique`: Shows that for a Gröbner basis, the remainder
  is unique.
- `MvPolynomial.mem_Ideal_iff_GB_normalForm_eq_zero`: A polynomial `f` is in an ideal `I`
  if and only if its normal form with respect to a Gröbner basis of `I` is zero.
- `MonomialOrder.Spolynomial_syzygy_of_degree_cancellation`: The crucial "Cancellation Lemma"
  used in the proof of Buchberger's Criterion.
- `MvPolynomial.Buchberger_criterion`: The main theorem. A basis `G` of an ideal `I` is a
  Gröbner basis if and only if the S-polynomial of every pair of elements in `G`
  reduces to zero.
-/

variable {σ : Type*}
variable {m : MonomialOrder σ}

open MonomialOrder MvPolynomial Finset

namespace MonomialOrder

/-
## Reference : [Cox, Little, and O'Shea 1997] [Becker-Weispfenning1993]
-/

section Semiring

variable {R : Type*} [CommSemiring R]

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

end Semiring

end MonomialOrder
namespace MvPolynomial
section Field

variable {k : Type*} [Field k] [DecidableEq k]

omit [DecidableEq k] in
noncomputable def quotients (m : MonomialOrder σ)
  {B : Set (MvPolynomial σ k)} (hB : ∀ b ∈ B, b ≠ 0) (f : MvPolynomial σ k) :
  B →₀ MvPolynomial σ k :=
  (MonomialOrder.div_set (m := m) (B := B)
      (hB := fun b hb => isUnit_leadingCoeff.2 (hB b hb))
      f).choose

omit [DecidableEq k] in
noncomputable def normalForm (m : MonomialOrder σ)
  {B : Set (MvPolynomial σ k)} (hB : ∀ b ∈ B, b ≠ 0) (f : MvPolynomial σ k) :
  MvPolynomial σ k :=
  (MonomialOrder.div_set (m := m) (B := B)
      (hB := fun b hb => isUnit_leadingCoeff.2 (hB b hb))
      f).choose_spec.choose

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
  simpa only [quotients, Subtype.forall, mem_support_iff, ne_eq, normalForm] using
    (MonomialOrder.div_set (m := m) (B := B) (hB := fun b hb =>
        isUnit_leadingCoeff.2 (hB b hb)) f).choose_spec.choose_spec

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

variable (m) in
/--
**Gröbner basis property.**
For an ideal `I` and a finite set `G`, this means:

- `G ⊆ I`, and
- `⟨ LT(G) ⟩ = ⟨ LT(I) ⟩`,

where `LT(G) = { LT(g) | g ∈ G }` and `LT(I) = { LT(f) | f ∈ I \ {0} }`.
-/
def GroebnerBasis_prop (I : Ideal (MvPolynomial σ k)) (G : Finset (MvPolynomial σ k)) : Prop :=
  (G : Set (MvPolynomial σ k)) ⊆ I ∧
  Ideal.span ((fun g => leadingTerm m g) '' G) = leadingTermIdeal m I

variable (m) [DecidableEq σ] in
/--
Removing `0` from `G` does not change the Gröbner basis property:

`G` satisfies `G ⊆ I` and `⟨ LT(G) ⟩ = ⟨ LT(I) ⟩`
if and only if `G \ {0}` satisfies the same conditions.
-/
lemma GroebnerBasis_prop_remove_zero (I : Ideal (MvPolynomial σ k)) (G : Finset (MvPolynomial σ k)) :
    GroebnerBasis_prop m I G ↔ GroebnerBasis_prop m I (G \ {0}) := by
  -- Auxiliary lemma: removing 0 does not change the span of leading terms
  have h_span : Ideal.span ((leadingTerm m) '' G) = Ideal.span ((leadingTerm m) '' (G \ {0} : Set (MvPolynomial σ k))) := by
    apply le_antisymm
    · -- (⊆) Case split: g = 0 (trivial) or g ≠ 0 (in G \ {0})
      rw [Ideal.span_le]
      rintro y ⟨g, hg, rfl⟩
      by_cases h0 : g = 0
      · rw [h0, leadingTerm_zero]; exact Ideal.zero_mem _
      · apply Ideal.subset_span
        exact ⟨g, by simpa only [Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff] using ⟨hg, h0⟩, rfl⟩
    · -- (⊇) Monotonicity: G \ {0} ⊆ G
      apply Ideal.span_mono
      apply Set.image_mono
      simp only [Set.diff_singleton_subset_iff, Set.subset_insert]

  unfold GroebnerBasis_prop
  constructor
  · -- (→) If G is a GB, so is G \ {0}
    rintro ⟨hGI, hLT⟩
    constructor
    · -- G \ {0} ⊆ G ⊆ I
      simp only [coe_sdiff, coe_singleton, Set.diff_singleton_subset_iff,
        SetLike.mem_coe, zero_mem, Set.insert_eq_of_mem]
      exact hGI
    · -- The spans are equal via h_span
      simp only [coe_sdiff, coe_singleton]
      rw [←h_span, ←hLT]

  · -- (←) If G \ {0} is a GB, so is G
    rintro ⟨hGI, hLT⟩
    constructor
    · -- G ⊆ I (handle 0 case explicitly)
      intro g hg
      by_cases h0 : g = 0
      · rw [h0]; exact Ideal.zero_mem _
      · apply hGI
        simpa using ⟨hg, h0⟩
    · -- The spans are equal via h_span
      rw [h_span]
      simp only [coe_sdiff, coe_singleton] at hLT
      exact hLT

variable (m) [DecidableEq σ] in
/-- **Cox, Little, O'Shea, Ch 2, §5 Definition 5. Groebner_basis**
A finite subset `G` of an ideal `I` is called a Gröbner basis (or standard basis) if

1. `0 ∉ G`, and
2. `G ⊆ I`, and
3. `⟨ LT(G) ⟩ = ⟨ LT(I) ⟩` (the ideal generated by the leading terms of the elements of `G`
equals the leading term ideal of `I`).

We adopt the convention `⟨∅⟩ = {0}`, so `∅` is a Gröbner basis of the zero ideal.
-/
def IsGroebnerBasis (I : Ideal (MvPolynomial σ k)) (G : Finset (MvPolynomial σ k)) : Prop :=
  (∀ g ∈ G, g ≠ 0) ∧ GroebnerBasis_prop m I G


variable [DecidableEq σ] in
omit [DecidableEq k] in
lemma IsGroebnerBasis.initialIdeal_eq_monomialIdeal
    {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
    (hGB : IsGroebnerBasis m I G) :
    leadingTermIdeal m I = monomialIdeal k (G.image fun g => m.degree g) := by
  rw [hGB.2.2.symm, monomialIdeal, Finset.coe_image, Set.image_image]
  apply le_antisymm <;> rw [Ideal.span_le] <;> rintro _ ⟨g, hg, rfl⟩
  · -- (⊆) leadingTerm g ∈ span { monomial (deg g) 1 }
    unfold leadingTerm
    -- Explicitly construct the equality to assist rewriting
    have h_decomp : monomial (m.degree g) (m.leadingCoeff g) =
                    C (m.leadingCoeff g) * monomial (m.degree g) 1 := by
      rw [C_mul_monomial, mul_one]
    simp only [SetLike.mem_coe]
    rw [h_decomp]
    apply Ideal.mul_mem_left
    exact Ideal.subset_span ⟨g, hg, rfl⟩
  · -- (⊇) monomial (deg g) 1 ∈ span { leadingTerm g }
    dsimp only
    have h_lc_ne0 : m.leadingCoeff g ≠ 0 := by exact leadingCoeff_ne_zero_iff.mpr (hGB.1 g hg)
    -- Construct equality: monomial n 1 = C (lc⁻¹) * leadingTerm g
    have h_decomp : monomial (m.degree g) 1 = C (m.leadingCoeff g)⁻¹ * leadingTerm m g := by
      rw [leadingTerm, C_mul_monomial, inv_mul_cancel₀ h_lc_ne0]
    rw [h_decomp]
    apply Ideal.mul_mem_left
    -- Since g ∈ G, LT(g) is in the span of LT(G)
    apply Ideal.subset_span
    exact ⟨g, hg, rfl⟩

variable [DecidableEq σ] in
/--
Proposition. If `G` is a Gröbner basis for `I`, then every `f` admits
a unique decomposition `f = g + r` with
1. `g ∈ I`, and
2. no term of `r` is divisible by any `LT gᵢ`.
-/
theorem normalForm_exists_unique
  {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
  (hGB : IsGroebnerBasis m I G)
  (f  : MvPolynomial σ k) :
  ExistsUnique (λ r : MvPolynomial σ k ↦
    (∃ g, g ∈ I ∧ f = g + r)
    ∧ ∀ c ∈ r.support, ∀ gi ∈ G, ¬ m.degree gi ≤ c) := by
  -- 1) **Existence**
  have h_unit : ∀ g ∈ G, IsUnit (m.leadingCoeff g) :=
    fun g hg => isUnit_leadingCoeff.mpr (hGB.1 g hg)
  obtain ⟨q, r, h_eq, -, h_rem⟩ := m.div_set h_unit f

  -- Define g as the quotient part and show g ∈ I
  let g := q.sum (fun b (coeff : MvPolynomial σ k) => coeff * b)
  have hgI : g ∈ I := by
    simp only [Finsupp.sum, Set.elem_mem, mem_val, g]
    have h_support_mem : ∀ b ∈ q.support, (b : MvPolynomial σ k) ∈ I :=
      fun b hb => hGB.2.1 b.2
    exact Submodule.sum_smul_mem I q h_support_mem

  refine ⟨r, ⟨⟨g, hgI, h_eq⟩, h_rem⟩, ?_⟩

  · -- **uniqueness**
    -- Suppose `r'` also works; then `f = g' + r'` and `r'` has no divisible LT–terms.
    rintro r' ⟨⟨g', hg'I, h_eq'⟩, h_rem'⟩
    by_contra hdiff
    have hne: ¬(r - r' = 0) := by exact sub_ne_zero_of_ne fun a ↦ hdiff (id (Eq.symm a))
    have hrg : r - r' = g' - g := by
      rw [eq_sub_of_add_eq' (id (Eq.symm h_eq)), eq_sub_of_add_eq' (id (Eq.symm h_eq'))]
      exact sub_sub_sub_cancel_left g g' f
    have dI : r - r' ∈ I := by
      rw [hrg]
      exact (Submodule.sub_mem_iff_left I hgI).mpr hg'I
    have hlt_in : leadingTerm m (r - r') ∈ leadingTermIdeal m I := by
      unfold leadingTermIdeal
      apply Ideal.subset_span
      rw [LT_set]
      simp only [Set.mem_setOf_eq]
      exact ⟨r - r', dI, hne, rfl⟩
    have hlm_in : monomial (m.degree (r - r')) 1 ∈ leadingTermIdeal m I := by
      rw [leadingTermIdeal_is_initialIdeal, initialIdeal]
      apply Ideal.subset_span
      simp only [Set.mem_image]
      refine ⟨m.degree (r - r'), ?_, rfl⟩
      rw [LM_set]
      exact ⟨r - r', dI, hne, rfl⟩
    -- extract an exponent α dividing `m.degree d`
    have hmono : monomial (m.degree (r - r')) 1 ∈ monomialIdeal k ↑(Finset.image (fun g ↦ m.degree g) G) := by
      rw [IsGroebnerBasis.initialIdeal_eq_monomialIdeal hGB] at hlm_in
      exact hlm_in
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
    | inl h => exact h_rem (m.degree (r - r')) h gα hgα_in_G hα.2
    | inr h => exact h_rem' (m.degree (r - r')) h gα hgα_in_G hα.2

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
  have hG_nonzero : ∀ g ∈ SetLike.coe G, g ≠ 0 := fun g hg => hGB.1 g hg
  -- The hypothesis that all elements of G have unit leading coefficients
  have hG_unit_lc : ∀ g ∈ SetLike.coe G, IsUnit (m.leadingCoeff g) := fun g hg =>
    isUnit_leadingCoeff.mpr (hG_nonzero g hg)

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
noncomputable def S_polynomial
  (f g : MvPolynomial σ k)
  : MvPolynomial σ k :=
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
      (∀ i ∈ p.support, ∀ j ∈ p.support, m.degree (S_polynomial m (p i) (p j)) ≺[m] δ) := by
  -- Let lc i := LC(p i) be the leading coefficient of p i.
  let lc : ι → k := fun i => m.leadingCoeff (p i)
  -- Since all `p i` have the same degree `δ`, their S-polynomial simplifies.
  have h_S_poly_simple : ∀ i ∈ p.support, ∀ j ∈ p.support, S_polynomial m (p i) (p j) = (lc i)⁻¹ • p i - (lc j)⁻¹ • p j := by
    intro i hi j hj
    unfold S_polynomial
    -- The sup of the degrees is δ.
    have h_deg_sup : m.degree (p i) ⊔ m.degree (p j) = δ := by
      simp only [hp_deg i hi, hp_deg j hj, le_refl, sup_of_le_left]
    simp_rw [h_deg_sup, hp_deg i hi, hp_deg j hj, tsub_self, monomial_zero']
    unfold lc
    rw [MvPolynomial.C_mul', MvPolynomial.C_mul']

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

    -- As in the textbook, the sum of these leading coefficients must be zero
    -- because the degree of the sum dropped.
    have h_sum_lc_zero : ∑ i ∈ p.support, lc i = 0 := by
      have h_coeff_sum_zero : MvPolynomial.coeff δ (∑ i ∈ p.support, p i) = 0 :=
        m.coeff_eq_zero_of_lt hsum

      rw [MvPolynomial.coeff_sum] at h_coeff_sum_zero

      have h_coeff_eq_lc : ∀ i ∈ p.support, MvPolynomial.coeff δ (p i) = lc i := by
        intro i hi
        unfold lc
        rw [leadingCoeff, hp_deg i hi]

      rwa [Finset.sum_congr rfl h_coeff_eq_lc] at h_coeff_sum_zero

    have S_polynomial_of_equal_degree {p q : MvPolynomial σ k} (h_deg_p : m.degree p = δ) (h_deg_q : m.degree q = δ) :
      S_polynomial m p q = C (m.leadingCoeff p)⁻¹ * p - C (m.leadingCoeff q)⁻¹ * q := by
      unfold S_polynomial
      simp only [h_deg_p, h_deg_q, le_refl, sup_of_le_left, tsub_self, monomial_zero']

    have h_sum_reduces : ∑ i ∈ (p.support.erase s), lc i • S_polynomial m (p i) (p s) = ∑ i ∈ p.support, p i := by
      have h_lc_ne_zero : ∀ i ∈ p.support, lc i ≠ 0 :=
        fun i hi => leadingCoeff_ne_zero_iff.mpr (hp_ne_zero i hi)

      calc
        -- Start with the LHS of the goal.
        ∑ i ∈ (p.support.erase s), lc i • S_polynomial m (p i) (p s)

        -- Step 1: Expand the definition of S_polynomial
        _ = ∑ i ∈ (p.support.erase s), lc i • (C (lc i)⁻¹ * p i - C (lc s)⁻¹ * p s) := by
            apply Finset.sum_congr rfl; intro i hi
            have hi_supp : i ∈ p.support := Finset.mem_of_mem_erase hi
            rw [S_polynomial_of_equal_degree (hp_deg i hi_supp) (hp_deg s hs)]

        -- Step 2: Distribute the `lc i` scalar into the parenthesis.
        _ = ∑ i ∈ (p.support.erase s), (lc i • (C (lc i)⁻¹ * p i) - lc i • (C (lc s)⁻¹ * p s)) := by
            apply Finset.sum_congr rfl; intro i _; rw [smul_sub]

        -- Step 3: Simplify each term inside the sum.
        _ = ∑ i ∈ (p.support.erase s), (p i - (lc i * (lc s)⁻¹) • p s) := by
            apply Finset.sum_congr rfl; intro i hi
            have hi_supp : i ∈ p.support := Finset.mem_of_mem_erase hi
            rw [C_mul', ←smul_assoc, smul_eq_mul, mul_inv_cancel₀ (h_lc_ne_zero i hi_supp), one_smul]
            rw [sub_right_inj]
            rw [C_mul', ←smul_assoc]
            rfl

        -- Step 4: Distribute the summation over the subtraction.
        _ = (∑ i ∈ p.support.erase s, p i) - (∑ i ∈ p.support.erase s, (lc i * (lc s)⁻¹) • p s) := by
            rw [Finset.sum_sub_distrib]

        -- Step 5: Factor the constant polynomial `p s` and its scalar multiple out of the second sum.
        _ = (∑ i ∈ p.support.erase s, p i) - ((∑ i ∈ p.support.erase s, lc i) * (lc s)⁻¹) • p s := by
            rw [←Finset.sum_smul, Finset.sum_mul]

        -- Step 6: Use the `h_sum_lc_zero` identity to simplify the coefficient sum.
        -- We know `∑_{i≠s} lc i = -lc s`.
        _ = (∑ i ∈ p.support.erase s, p i) + p s := by
            have h_sum_erase : ∑ i ∈ p.support.erase s, lc i = -lc s := by
              rw [←add_eq_zero_iff_eq_neg, Finset.sum_erase_add p.support lc hs]
              exact h_sum_lc_zero
            rw [h_sum_erase, neg_mul, sub_eq_add_neg, neg_smul, neg_neg]
            simp only [add_right_inj]
            rw [CommGroupWithZero.mul_inv_cancel (lc s) (h_lc_ne_zero s hs), one_smul]

        -- Step 7: Combine the terms back into a single sum over the full support.
        _ = ∑ i ∈ p.support, p i := by
            exact sum_erase_add p.support (⇑p) hs

    -- Now, we construct the coefficient function `c` for the existential goal.
    -- The sum we proved is over `i` paired with a fixed `s`. The goal is a sum over all pairs `ij`.
    -- We define `c ij` to be `lc i` if `j=s` and `i≠s`, and 0 otherwise.
    let c (ij : ι × ι) : k := if ij.2 = s ∧ ij.1 ∈ p.support.erase s then lc ij.1 else 0
    use c
    dsimp only [mem_erase, Finsupp.mem_support_iff, c]
    simp only [Finset.mem_erase, Finsupp.mem_support_iff, ite_smul, zero_smul]
    show ∑ i ∈ p.support, p i =
    ∑ x ∈ p.support.offDiag, if x.2 = s ∧ x.1 ∈ p.support.erase s then lc x.1 • S_polynomial m (p x.1) (p x.2) else 0
    rw [← h_sum_reduces]
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
    have h_inj : (SetLike.coe (p.support.erase s)).InjOn (fun i => (i, s))  := by
      intro x _ y _ h_eq
      -- `(x, s) = (y, s)` implies `x = y`.
      exact (Prod.ext_iff.mp h_eq).1
    rw [Finset.sum_image h_inj]
  · intro i hi j hj
    let f := p i; let g := p j
    -- S(f,g) is designed to cancel the leading terms of f and g.
    -- Since deg(f) = deg(g) = δ, the two parts of the S-poly subtraction
    -- also have degree δ and identical leading terms.
    rw [h_S_poly_simple i hi j hj]
    have hi_unit : IsUnit (lc i) := isUnit_leadingCoeff.mpr (hp_ne_zero i hi)
    have hj_unit : IsUnit (lc j) := isUnit_leadingCoeff.mpr (hp_ne_zero j hj)
    have : IsRegular (lc i)⁻¹ := by
      refine IsUnit.isRegular (IsUnit.inv hi_unit)
    have h1 : (lc i)⁻¹ • (p i - ((lc i) * (lc j)⁻¹) • p j)
          = (lc i)⁻¹ • p i - (lc j)⁻¹ • p j := by
            rw [smul_sub]
            simp only [sub_right_inj]
            rw [←smul_assoc]
            simp only [smul_eq_mul, ←mul_assoc]
            have : (lc i)⁻¹ * (lc i) = 1 := by
              exact IsUnit.inv_mul_cancel hi_unit
            simp only [this, one_mul]
    have h2 : m.degree (p i - (lc i * (lc j)⁻¹) • p j)
          = m.degree ((lc i)⁻¹ • (p i - (lc i * (lc j)⁻¹) • p j)) := by
            rw [MonomialOrder.degree_smul_of_isRegular this]

    rw [←h1, ←h2]
    have hi_deg_δ : m.degree (p i) = δ := by exact hp_deg i hi
    have hj_deg_δ : m.degree (p j) = δ := by exact hp_deg j hj
    have h3 : p i - (lc i * (lc j)⁻¹) • p j
      = m.reduce hj_unit (p i) := by
      rw [reduce, hi_deg_δ, hj_deg_δ]
      simp
      rw [←MvPolynomial.C_mul, MvPolynomial.C_mul', mul_comm]
    rw [h3, ←hi_deg_δ]
    apply MonomialOrder.degree_reduce_lt
    · rw [hi_deg_δ, hj_deg_δ]
    · -- hδ not used
      rw [hi_deg_δ]
      -- We now need to prove `δ ≠ 0`.

      -- Assume `δ = 0` for contradiction.
      intro h_δ_is_zero

      -- `hsum` is `m.degree (∑ ...) ≺[m] δ`.
      -- If `δ = 0`, then `hsum` becomes `m.degree (∑ ...) ≺[m] 0`.
      have h_deg_sum_lt_zero : m.degree (∑ i ∈ p.support, p i) ≺[m] 0 := by
        rwa [h_δ_is_zero] at hsum

      -- However, the degree of any polynomial is always `≽[m] 0`.
      have h_deg_ge_zero : 0 ≼[m] m.degree (∑ i ∈ p.support, p i) := by simp

      -- We have `0 ≤ deg < 0`, which is impossible.
      -- We use `not_lt_of_le` to formalize this contradiction.
      exact not_lt_of_ge h_deg_ge_zero h_deg_sum_lt_zero

variable (m) in
/--
**(Cox, Little, O'Shea, Ch 2, §6, Exercise 7)
-/
lemma degree_S_polynomial_lt_lcm (f g : MvPolynomial σ k) (hf : f ≠ 0) (hg : g ≠ 0)
  (hγ : m.degree f ⊔ m.degree g > 0) :
  let γ := m.degree f ⊔ m.degree g
  m.degree (S_polynomial m f g) ≺[m] γ := by

  -- Define the abbreviations from the strategy.
  let γ := m.degree f ⊔ m.degree g
  let lc_f := m.leadingCoeff f
  let lc_g := m.leadingCoeff g
  let mono_f := monomial (γ - m.degree f) (lc_f⁻¹)
  let mono_g := monomial (γ - m.degree g) (lc_g⁻¹)
  let term₁ := mono_f * f
  let term₂ := mono_g * g

  -- The S-polynomial is the difference of these two terms.
  unfold S_polynomial
  have h_mono_f_ne_zero : mono_f ≠ 0 := by
      rw [Ne, monomial_eq_zero]; exact inv_ne_zero (m.leadingCoeff_ne_zero_iff.mpr hf)
  have h_mono_g_ne_zero : mono_g ≠ 0 := by
      rw [Ne, monomial_eq_zero]; exact inv_ne_zero (m.leadingCoeff_ne_zero_iff.mpr hg)

  -- We need to show `m.degree (term₁ - term₂) ≺[m] γ`.
  -- First, let's establish the degrees of term₁ and term₂.
  have h_deg_t1 : m.degree term₁ = γ := by
    rw [degree_mul h_mono_f_ne_zero hf, degree_monomial]
    rw [ite_cond_eq_false]
    · refine tsub_add_cancel_of_le ?_
      exact le_sup_left
    · unfold lc_f
      exact eq_false (inv_ne_zero (m.leadingCoeff_ne_zero_iff.mpr hf))

  have h_deg_t2 : m.degree term₂ = γ := by
    rw [degree_mul h_mono_g_ne_zero hg, degree_monomial]
    rw [ite_cond_eq_false]
    · refine tsub_add_cancel_of_le ?_
      exact le_sup_right
    · unfold lc_g
      exact eq_false (inv_ne_zero (m.leadingCoeff_ne_zero_iff.mpr hg))

  -- Next, show that their leading coefficients are identical.
  have h_lc_t1 : m.leadingCoeff term₁ = 1 := by
    rw [leadingCoeff_mul h_mono_f_ne_zero hf, leadingCoeff_monomial]
    unfold lc_f
    rw [inv_mul_cancel₀ (m.leadingCoeff_ne_zero_iff.mpr hf)]

  have h_lc_t2 : m.leadingCoeff term₂ = 1 := by
    rw [leadingCoeff_mul h_mono_g_ne_zero hg, leadingCoeff_monomial]
    unfold lc_g
    rw [inv_mul_cancel₀ (m.leadingCoeff_ne_zero_iff.mpr hg)]

  have h_lt_eq : m.leadingTerm term₁ = m.leadingTerm term₂ := by
    rw [leadingTerm, leadingTerm, h_deg_t1, h_deg_t2, h_lc_t1, h_lc_t2]

  have : term₁ - term₂ = m.subLTerm term₁ - m.subLTerm term₂ := by
    unfold subLTerm
    rw [h_deg_t1, h_deg_t2, h_lc_t1, h_lc_t2]
    exact Eq.symm (sub_sub_sub_cancel_right term₁ term₂ ((monomial γ) 1))
  rw [this, sub_eq_add_neg]
  apply lt_of_le_of_lt degree_add_le
  have h_deg_lt1 : m.degree (m.subLTerm term₁) ≺[m] γ := by
    rw [←h_deg_t1]
    apply degree_sub_LTerm_lt
    rw [h_deg_t1]
    exact pos_iff_ne_zero.mp hγ

  have h_deg_lt2 : m.degree (-m.subLTerm term₂) ≺[m] γ := by
    have : m.degree (-m.subLTerm term₂) = m.degree (m.subLTerm term₂) := by exact degree_neg
    rw [this, ←h_deg_t2]
    apply degree_sub_LTerm_lt
    rw [h_deg_t2]
    exact pos_iff_ne_zero.mp hγ
  exact max_lt h_deg_lt1 h_deg_lt2


variable (m) in
/--
**(Cox, Little, O'Shea, Ch 2, §6, Exercise 8)
-/
lemma Spolynomial_of_monomial_mul_eq_monomial_mul_Spolynomial
  (gᵢ gⱼ : MvPolynomial σ k) (hgᵢ_ne_zero : gᵢ ≠ 0) (hgⱼ_ne_zero : gⱼ ≠ 0)
  (aᵢ aⱼ : σ →₀ ℕ) (cᵢ cⱼ : k) (hcᵢ_ne_zero : cᵢ ≠ 0) (hcⱼ_ne_zero : cⱼ ≠ 0)
  (h_deg_eq : aᵢ + m.degree gᵢ = aⱼ + m.degree gⱼ) :
  let pᵢ := monomial aᵢ cᵢ * gᵢ
  let pⱼ := monomial aⱼ cⱼ * gⱼ
  S_polynomial m pᵢ pⱼ = monomial (aᵢ + m.degree gᵢ - (m.degree gᵢ ⊔ m.degree gⱼ)) 1 * S_polynomial m gᵢ gⱼ := by
    let δ := aᵢ + m.degree gᵢ
    let γ := m.degree gᵢ ⊔ m.degree gⱼ
    let lc_gᵢ := m.leadingCoeff gᵢ
    let lc_gⱼ := m.leadingCoeff gⱼ
    have hᵢ_ne_zero : monomial aᵢ cᵢ ≠ 0 := by
      contrapose hcᵢ_ne_zero
      simp only [ne_eq, monomial_eq_zero] at *
      exact hcᵢ_ne_zero
    have hᵢ_degree : m.degree ((monomial aᵢ) cᵢ) = aᵢ := by
      rw [m.degree_monomial cᵢ]
      exact if_neg hcᵢ_ne_zero
    have h_δ_eq_pᵢ : m.degree (monomial aᵢ cᵢ * gᵢ) = δ := by
      rw [m.degree_mul hᵢ_ne_zero hgᵢ_ne_zero, hᵢ_degree]
    have hⱼ_ne_zero : monomial aⱼ cⱼ ≠ 0 := by
      contrapose hcⱼ_ne_zero
      simp only [ne_eq, monomial_eq_zero] at *
      exact hcⱼ_ne_zero
    have hⱼ_degree : m.degree ((monomial aⱼ) cⱼ) = aⱼ := by
      rw [m.degree_monomial cⱼ]
      exact if_neg hcⱼ_ne_zero
    have h_δ_eq_pⱼ : m.degree (monomial aⱼ cⱼ * gⱼ) = δ := by
      rw [m.degree_mul hⱼ_ne_zero hgⱼ_ne_zero, hⱼ_degree, ←h_deg_eq]


    have lhs_simplified : S_polynomial m (monomial aᵢ cᵢ * gᵢ) (monomial aⱼ cⱼ * gⱼ) =
      (m.leadingCoeff (monomial aᵢ cᵢ * gᵢ))⁻¹ • (monomial aᵢ cᵢ * gᵢ) -
      (m.leadingCoeff (monomial aⱼ cⱼ * gⱼ))⁻¹ • (monomial aⱼ cⱼ * gⱼ) := by
      unfold S_polynomial
      rw [h_δ_eq_pᵢ, h_δ_eq_pⱼ, sup_idem, tsub_self, monomial_zero']
      simp only [C_eq_smul_one, Algebra.smul_mul_assoc, one_mul]
    simp only
    rw [lhs_simplified]
    rw [m.leadingCoeff_mul hᵢ_ne_zero hgᵢ_ne_zero,
      m.leadingCoeff_mul hⱼ_ne_zero hgⱼ_ne_zero,
      m.leadingCoeff_monomial cᵢ, m.leadingCoeff_monomial cⱼ]
    rw [←C_mul', ←mul_assoc, C_mul_monomial, ←C_mul', ←mul_assoc, C_mul_monomial]
    simp only [mul_inv_rev, mul_assoc]
    rw [inv_mul_cancel₀ hcᵢ_ne_zero, inv_mul_cancel₀ hcⱼ_ne_zero, mul_one, mul_one]
    -- The fully simplified LHS is: `lc_gᵢ⁻¹ • (monomial aᵢ 1 * gᵢ) - lc_gⱼ⁻¹ • (monomial aⱼ 1 * gⱼ)`

    -- Part 2: Simplify the RHS `monomial (δ - γ) 1 * S(gᵢ, gⱼ)`.
    unfold S_polynomial
    rw [mul_sub_left_distrib]
    -- We now have two terms on the RHS. Let's simplify them one by one.
    congr 1
    · -- First term of the subtraction.
      -- `(monomial (δ - γ) 1) * (monomial (γ - m.degree gᵢ) (lc_gᵢ⁻¹) * gᵢ)`
      rw [← mul_assoc] -- Group the monomials together
      -- We need to prove `(monomial aᵢ lc_gᵢ⁻¹) = (monomial (δ - γ) 1) * (monomial (γ - m.degree gᵢ) lc_gᵢ⁻¹)`.
      rw [monomial_mul, one_mul]
      congr 1
      · rw [tsub_add_tsub_cancel]
        · simp only [add_tsub_cancel_right]
        · exact sup_le (le_add_self) (by rw [h_deg_eq]; exact le_add_self)
        · exact le_sup_left

    · rw [← mul_assoc] -- Group the monomials together
      -- We need to prove `(monomial aᵢ lc_gᵢ⁻¹) = (monomial (δ - γ) 1) * (monomial (γ - m.degree gᵢ) lc_gᵢ⁻¹)`.
      rw [monomial_mul, one_mul]
      congr 1
      · -- Exponents: `aᵢ = (δ - γ) + (γ - m.degree gᵢ)`.
        -- `γ = m.degree gᵢ ⊔ m.degree gⱼ`.
        rw [tsub_add_tsub_cancel]
        · simp only [h_deg_eq, add_tsub_cancel_right]
        · exact sup_le (le_add_self) (by rw [h_deg_eq]; exact le_add_self)
        · exact le_sup_right

variable (m) [DecidableEq σ] in
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
        have hG_sub_I : SetLike.coe G ⊆ I := by rw [hGI]; exact Ideal.subset_span
        exact sub_mem (Ideal.mul_mem_left _ _ (hG_sub_I hg₁)) (Ideal.mul_mem_left _ _ (hG_sub_I hg₂))
      · -- (⇐) If all S-polynomials reduce to 0, then G is a Gröbner basis.
        intro hS_poly
        rw [IsGroebnerBasis]
        have hG_sub_I : (↑G : Set (MvPolynomial σ k)) ⊆ I := by rw [hGI]; exact Ideal.subset_span
        refine ⟨hG, hG_sub_I, ?_⟩
        by_cases hG_empty : G = ∅
        · simp only [hG_empty, coe_empty, Ideal.span_empty] at hGI
          rw [leadingTermIdeal, hGI, hG_empty, LT_set]
          simp only [coe_empty, Submodule.mem_bot, ne_eq, exists_eq_left, not_true_eq_false,
            leadingTerm_zero, false_and, Set.setOf_false, Ideal.span_empty]
          simp only [Set.image_empty, Ideal.span_empty]
        -- We need to show `initialIdeal m I = Ideal.span (LT(G))`.
        -- The inclusion `Ideal.span(LT(G)) ⊆ initialIdeal m I` is straightforward.
        apply le_antisymm
        · apply Ideal.span_mono
          intro lt_g h_lt_g_mem
          simp only [Set.mem_image, mem_coe] at h_lt_g_mem
          obtain ⟨g, hg_in_G, rfl⟩ := h_lt_g_mem
          refine Set.mem_setOf.mpr ?_
          use g
          exact ⟨by exact hG_sub_I hg_in_G, by exact hG g hg_in_G, rfl⟩
        -- The difficult inclusion: `initialIdeal m I ⊆ Ideal.span (LT(G))`.
        -- This means for any non-zero `f ∈ I`, we must show `LT(f) ∈ ⟨LT(G)⟩`.
        rw [leadingTermIdeal, Ideal.span_le]
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

        let ℍ : ↥G →₀ MvPolynomial σ k :=
          Finsupp.onFinset G.attach
            (fun g => H g.val)
            (by
              intro g hg
              simp only [Finset.mem_attach])

        have h_f_eq : ∑ g ∈ G.attach, ℍ g * g.val = f := by
          simp only [ℍ, Finsupp.onFinset_apply]
          rw [Finset.sum_attach G (fun a => H a * a)]
          exact h_f_eq

        let RepMaxSynDegrees : Set m.syn :=
          { δ_syn | ∃ (h : ↥G →₀ MvPolynomial σ k),
              f = (∑ g ∈ G.attach, h g * g.val) ∧
              -- δ_syn is the sup of the degrees *in the synonym type*.
              δ_syn = (G.attach.image (m.toSyn ∘ (fun g => m.degree (h g * g.val)))).sup id }

        have h_RepMaxSynDegrees_nonempty : RepMaxSynDegrees.Nonempty := by
          use (G.attach.image (m.toSyn ∘ (fun g => m.degree (ℍ g * g.val)))).sup id
          use ℍ
          exact ⟨h_f_eq.symm, rfl⟩

        let δ_syn_min := WellFounded.min (by exact wellFounded_lt) RepMaxSynDegrees h_RepMaxSynDegrees_nonempty

        let δ_min := m.toSyn.symm δ_syn_min
        have hδ_syn : δ_syn_min = m.toSyn δ_min := by unfold δ_min; simp only [AddEquiv.apply_symm_apply]

        have h_δ_min_in_RepDegrees : δ_syn_min ∈ RepMaxSynDegrees := by
          exact WellFounded.min_mem wellFounded_lt RepMaxSynDegrees h_RepMaxSynDegrees_nonempty

        obtain ⟨h_min, h_f_eq_min, h_δ_syn_min_eq⟩ := h_δ_min_in_RepDegrees

        have f_deg_le : m.toSyn (m.degree f) ≤ δ_syn_min := by

          rw [h_f_eq_min]
          -- simp only [AddEquiv.apply_symm_apply, δ_min]
          apply le_trans (@degree_sum_le_syn σ m k _ (↥G) G.attach _) -- (fun g => h_min' g * g.val)

          -- The goal after applying the lemma is:
          -- `(G.sup (fun i => m.toSyn (m.degree (h_min i * i)))) ≤ δ_syn_min`.

          -- From `h_δ_syn_min_eq`, we know the LHS is exactly `δ_syn_min`.
          rw [h_δ_syn_min_eq]
          refine le_of_eq ?_
          rw [eq_comm]
          apply Finset.sup_image

        have h_le : ∀ g ∈ G.attach, m.toSyn (m.degree (h_min g * g.val)) ≤ δ_syn_min := by
          intro g hg
          -- rewrite δ_syn_min to the `image ... .sup id` form
          rw [h_δ_syn_min_eq]
          -- convert (image ...).sup id into G.attach.sup (the function on ↥G)
          rw [Finset.sup_image]
          -- now apply the lemma that f x ≤ s.sup f for x ∈ s
          exact @Finset.le_sup _ _ _ _ (G.attach) (m.toSyn ∘ fun g => m.degree (h_min g * g.val)) g hg

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

          have g_deg_0 : ∀g ∈ G.attach, m.toSyn (m.degree (h_min g * g.val)) = 0 := by
            intro g hg
            rw [h_syn_min_eq_bot] at h_le
            exact (MonomialOrder.eq_zero_iff m).mpr (h_le g hg)

          have h_exists_nonzero_term : ∃ g ∈ G.attach, h_min g * g ≠ 0 := by
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

          have h_deg_g₀ : m.degree g₀.val = 0 := by
            -- We know the degree of the product is 0.
            have h_term_deg_zero : m.degree (h_min g₀ * g₀.val) = 0 := by
              exact (AddEquiv.map_eq_zero_iff m.toSyn).mp (g_deg_0 g₀ hg₀_in_G)

            -- The degree of a product is the sum of degrees (for non-zero polynomials).
            -- We need to show `h_min g₀` and `g₀` are non-zero.
            have h_g₀_ne_zero : g₀.val ≠ 0 := hG g₀.val g₀.property
            have h_h_min_g₀_ne_zero : h_min g₀ ≠ 0 := by
              -- If h_min g₀ = 0, then h_min g₀ * g₀ = 0, which contradicts `h_term_ne_zero`.
              contrapose! h_term_ne_zero
              rw [h_term_ne_zero, zero_mul]

            -- Now apply the degree of product rule.
            have h_deg_add := m.degree_mul h_h_min_g₀_ne_zero h_g₀_ne_zero
            rw [h_term_deg_zero] at h_deg_add
            have : m.degree (h_min g₀) = 0 ∧ m.degree g₀.val = 0 := by exact add_eq_zero.mp (by exact id (Eq.symm h_deg_add))
            exact this.2

          have hg₀_val_in_G : g₀.val ∈ G := by exact Finset.coe_mem g₀

          have h_unit_g₀ : IsUnit (m.leadingTerm g₀.val) := by

            -- The leading term is `monomial 0 (leadingCoeff g₀)`.
            -- This is the same as `C (leadingCoeff g₀)`.
            rw [leadingTerm, h_deg_g₀]
            simp only [monomial_zero', isUnit_map_iff, isUnit_iff_ne_zero, ne_eq,
              leadingCoeff_eq_zero_iff]
            exact hG g₀.val hg₀_val_in_G
          have : Ideal.span ((fun g ↦ m.leadingTerm g) '' SetLike.coe G) = ⊤ := by
            apply Ideal.eq_top_of_isUnit_mem _ _ h_unit_g₀
            apply Ideal.subset_span
            exact Set.mem_image_of_mem (fun g ↦ m.leadingTerm g) hg₀_val_in_G
          rw [this]
          exact Submodule.mem_top

        push_neg at h_min_le_bot
        by_cases h_const_ex : ∃ g ∈ G, m.degree g = 0
        · obtain ⟨g, ⟨hgG, hg_deg_zero⟩⟩ := h_const_ex
          have inI_top : Ideal.span (Finset.image (fun g ↦ m.leadingTerm g) G) = (⊤ : Ideal (MvPolynomial σ k)) := by
            have LTg_unit : IsUnit (m.leadingTerm g) := by
              rw [leadingTerm, hg_deg_zero, monomial_zero',isUnit_map_iff, isUnit_iff_ne_zero, ne_eq, leadingCoeff_eq_zero_iff]
              exact hG g hgG
            apply Ideal.eq_top_of_isUnit_mem _ _  LTg_unit
            apply Submodule.mem_span_of_mem
            simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
            use g
          simp only [coe_image] at inI_top
          rw [inI_top]
          exact trivial

        have h_const_non_ex:= h_const_ex; clear h_const_ex
        push_neg at h_const_non_ex

        by_cases h_deg_eq_δ_syn : m.toSyn (m.degree f) = δ_syn_min
        · have h_sup_is_achieved : ∃ g ∈ G.attach, (m.toSyn (m.degree (h_min g * g.val))) = δ_syn_min := by
            by_contra h_not_achieved
            push_neg at h_not_achieved
            have h_g_lt_δ : ∀ g ∈ G.attach, m.toSyn (m.degree (h_min g * g.val)) < δ_syn_min  := by
              intro g hg
              apply lt_of_le_of_ne ?_ (h_not_achieved g hg)
              exact h_le g hg

            clear h_not_achieved
            rw [h_f_eq_min] at h_deg_eq_δ_syn
            have h_deg_lt_δ : m.toSyn (m.degree (∑ g ∈ G.attach, h_min g * g.val)) < δ_syn_min := by
              apply LE.le.trans_lt (m.degree_sum_le_syn G.attach (fun i ↦ (h_min i) * i.val))
              rw [@Finset.sup_lt_iff _ _ _ _ G.attach (fun i ↦ m.toSyn (m.degree (h_min i * i.val))) (δ_syn_min ) h_min_le_bot]
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
            have : m.leadingTerm f = m.leadingTerm (h_min gᵢ * gᵢ.val) * C ((m.leadingCoeff f) * (m.leadingCoeff (h_min gᵢ * gᵢ.val))⁻¹):= by
              rw [leadingTerm, leadingTerm, mul_comm]
              rw [MvPolynomial.C_mul_monomial, mul_assoc]
              --nth_rw 2 [mul_comm]
              rw [leadingCoeff_mul h_nzero_h_min_gᵢ (hG gᵢ (Finset.coe_mem gᵢ)), mul_inv_rev, mul_assoc]
              nth_rw 3 [←mul_assoc]

              rw [inv_mul_cancel₀ (by exact leadingCoeff_ne_zero_iff.mpr h_nzero_h_min_gᵢ), one_mul]
              rw [inv_mul_cancel₀ (by exact leadingCoeff_ne_zero_iff.mpr (hG gᵢ (Finset.coe_mem gᵢ))), mul_one]
              have hgᵢ_δ_min : (m.degree (h_min gᵢ * gᵢ.val)) =  δ_min := by
                apply m.toSyn.injective; rw [AddEquiv.apply_symm_apply]; exact hgᵢ_δ_min_syn
              have h_deg_eq_δ : (m.degree f) = δ_min := by
                apply m.toSyn.injective; rw [AddEquiv.apply_symm_apply]; exact h_deg_eq_δ_syn
              rw [hgᵢ_δ_min, h_deg_eq_δ]
            rw [this]
            apply Ideal.mul_mem_right
            rw [leadingTerm_mul (h_nzero_h_min_gᵢ) (hG gᵢ (Finset.coe_mem gᵢ))]
            apply Ideal.mul_mem_left
            apply Submodule.mem_span_of_mem
            simp only [Set.mem_image, SetLike.mem_coe]
            exact ⟨gᵢ, ⟨coe_mem gᵢ, rfl⟩⟩

        · have f_deg_lt : m.toSyn (m.degree f) < δ_syn_min := by
            apply (LE.le.lt_iff_ne' f_deg_le).mpr (by exact fun a ↦ h_deg_eq_δ_syn (id (Eq.symm a)))
          clear f_deg_le; clear h_deg_eq_δ_syn

          -- STEP 1: Decompose f into P₁, P₂, P₃
          let G_δ := G.attach.filter (fun g => m.toSyn (m.degree (h_min g * g.val)) = δ_syn_min)
          have h_f_split : f = (∑ g ∈ G_δ, h_min g * g) + (∑ g ∈ G.attach \ G_δ, h_min g * g) := by
            rw [h_f_eq_min]
            have G_sep : G.attach = G_δ ∪ (G.attach \ G_δ) := by
              refine Eq.symm (Finset.union_sdiff_of_subset ?_)
              exact Finset.filter_subset (fun g ↦ m.toSyn (m.degree (h_min g * g.val)) = δ_syn_min) G.attach
            nth_rw 1 [G_sep]
            rw [Finset.sum_union (by exact Finset.disjoint_sdiff)]
          have h_sdiff : G.attach \ G_δ = G.attach.filter (fun g => m.toSyn (m.degree (h_min g * g.val)) < δ_syn_min) := by
            dsimp only [G_δ]
            -- We also know `m.degree (h_min g * g) ≼[m] δ_min` because δ_min is the maximum.
            have h_le : ∀ g ∈ G.attach, m.toSyn (m.degree (h_min g * g.val)) ≤ δ_syn_min := by
              intro h hg
              rw [h_δ_syn_min_eq]
              rw [Finset.sup_image]
              simp only [CompTriple.comp_eq]
              exact @Finset.le_sup _ _ _ _ _ (m.toSyn ∘ fun g ↦ m.degree (h_min g * g.val)) _ (by simp only [Finset.mem_attach])
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
              have h_ne : ¬ (m.toSyn (m.degree (h_min g * g.val)) = δ_syn_min) := by
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
          let P₃ := ∑ g ∈ G.attach \ G_δ, h_min g * g

          have h_f_is_P123 : f = P₁ + P₂ + P₃ := by
            -- Start with the split sum for f.
            rw [h_f_split]
            -- Unfold S_δ.
            -- Rewrite the first sum using its decomposition.
            -- Unfold the definitions of P₁, P₂, P₃.
            unfold P₁ P₂ P₃
            -- The goal is now `(a + b) + c = a + b + c`, which is true by associativity.
            rw [add_left_inj]
            rw [←Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro x
            rw [sub_mul]
            exact fun a ↦ Eq.symm (add_sub_cancel (m.leadingTerm (h_min x) * x) (h_min x * x))

          have hG_δ_deg : ∀ g ∈ G_δ, m.toSyn (m.degree (h_min g * g.val)) = δ_syn_min := by
            intro g hg
            simp only [G_δ, Finset.mem_filter] at hg
            exact hg.2

          have h_P₃term_deg_lt : ∀ g ∈ G.attach \ G_δ, m.toSyn (m.degree (h_min g * g.val)) < δ_syn_min := by
            intro g hg_sdiff
            rw [h_sdiff] at hg_sdiff
            simp only [Finset.mem_filter] at hg_sdiff
            exact hg_sdiff.2

          have hP₃_deg_lt : m.toSyn (m.degree P₃) < δ_syn_min := by
            unfold P₃
            apply lt_of_le_of_lt (m.degree_sum_le_syn (G.attach \ G_δ) (fun g ↦ h_min g * g.val))
            rw [Finset.sup_lt_iff h_min_le_bot]
            exact h_P₃term_deg_lt

          have h_P₂term_deg_lt : ∀ g ∈ G_δ, m.toSyn (m.degree ((h_min g - leadingTerm m (h_min g)) * g.val)) < δ_syn_min := by
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
                rw [degree_mul h_sub_zero (hG g (by simp only [Finset.coe_mem]))]
                rw [degree_mul h_h_min_g_ne_zero (hG g (by simp only [Finset.coe_mem]))]
                simp only [map_add, add_lt_add_iff_right, gt_iff_lt]
                exact h_sub_lt

          have hP₂_deg_lt : m.toSyn (m.degree P₂) < δ_syn_min := by
            unfold P₂
            apply lt_of_le_of_lt (m.degree_sum_le_syn G_δ fun g ↦ (h_min g - m.leadingTerm (h_min g)) * g.val)
            rw [Finset.sup_lt_iff h_min_le_bot]
            exact h_P₂term_deg_lt

          have hP₁_deg_lt : m.toSyn (m.degree P₁) < δ_syn_min := by
            have h_P1_eq_sub : P₁ = f - (P₂ + P₃) := by
              rw [h_f_is_P123, add_sub_add_right_eq_sub, add_sub_cancel_right]

            rw [h_P1_eq_sub]

            have h_deg_P₂_plus_P₃_lt : m.toSyn (m.degree (P₂ + P₃)) < δ_syn_min := by
              exact m.degree_add_lt_of_le_lt hP₂_deg_lt hP₃_deg_lt

            apply lt_of_le_of_lt (m.degree_sub_le)
            rw [max_lt_iff]
            exact ⟨f_deg_lt, h_deg_P₂_plus_P₃_lt⟩

          -- STEP 2: Rewrite P₁ using the Cancellation Lemma.
          let ι := ↥G_δ
          let p_fun (g : ι) : MvPolynomial σ k := leadingTerm m (h_min g.val) * g.val
          let p : ι →₀ MvPolynomial σ k := (Finsupp.equivFunOnFinite).symm p_fun
          have LT_hᵢi_ne_zero : ∀ i : ι, m.leadingTerm (h_min i.1) * i.1 ≠ 0 := by
            intro i
            apply mul_ne_zero
            · -- First goal: `leadingTerm m (h_min i.val) ≠ 0`.
              -- This is equivalent to `h_min i.val ≠ 0`.
              intro LT_h_min_i_ne_zero
              have : (h_min ↑i) = 0 := by exact leadingTerm_eq_zero_imp_eq_zero m LT_h_min_i_ne_zero
              unfold Subtype.val at this
              have hi_in_G_δ : i.1 ∈ G_δ := by exact Finset.coe_mem i

              -- By definition of `G_δ`, `m.toSyn (m.degree (h_min i.val * i.val)) = δ_syn_min`.
              have h_deg_is_δ := (Finset.mem_filter.mp hi_in_G_δ).2

              -- Substitute `h_min i.val = 0` into this.
              rw [this, zero_mul, degree_zero, map_zero] at h_deg_is_δ

              -- Now we have `δ_syn_min = 0`.
              -- This contradicts `h_min_le_bot : ⊥ < δ_syn_min`.
              exact not_le_of_gt h_min_le_bot (le_of_eq h_deg_is_δ.symm)

            · -- Second goal: `i.val ≠ 0`.
              -- This is true because `i.val ∈ G_δ ⊆ G`.
              have hi_in_G : i.val ∈ G.attach := (Finset.mem_filter.mp i.property).1
              exact hG i.val (by simp only [Finset.coe_mem])

          have h_p_support : p.support = (Finset.univ : Finset ι) := by
            -- To show two finsets are equal, we show they have the same elements.
            ext i
            -- We need to prove `i ∈ p.support ↔ i ∈ Finset.univ`.
            -- `i ∈ Finset.univ` is always true.
            simp only [Finset.mem_univ, Finsupp.mem_support_iff, iff_true]
            dsimp only [Finsupp.equivFunOnFinite_symm_apply_apply, p]

            -- The goal is now `p_fun i ≠ 0`.
            unfold p_fun
            exact LT_hᵢi_ne_zero i

          have h_P₁_eq_sum_p : P₁ = ∑ i ∈ p.support, p_fun i := by
            -- First, use the fact that the support is the whole set of indices.
            rw [h_p_support]
            -- The goal is now `∑ g in G_δ, ... = ∑ i in Finset.univ, p i`.

            rw [← Finset.attach_eq_univ]

            unfold P₁ p_fun
            rw [Finset.sum_attach G_δ (fun i ↦ m.leadingTerm (h_min ↑i) * ↑i)]

          -- Hypothesis 1: All polynomials in the family are non-zero.
          have hp_ne_zero : ∀ i ∈ p.support, p i ≠ 0 := by
            -- Since `p.support` is `Finset.univ`, this is `∀ i, p i ≠ 0`.
            rw [h_p_support]
            intro i _ -- i is `Finset.mem_univ`
            dsimp only [Finsupp.equivFunOnFinite_symm_apply_apply, p, p_fun]
            exact LT_hᵢi_ne_zero i

          -- Hypothesis 2: All polynomials in the family have degree `δ_min`.
          have hp_deg : ∀ i ∈ p.support, m.degree (p i) = δ_min := by
            rw [h_p_support]
            intro i _
            dsimp only [Finsupp.equivFunOnFinite_symm_apply_apply, p]
            -- Goal: `m.degree (LT(h_min i.val) * i.val) = δ_min`.
            -- We prove this by showing it's equal to `m.degree(h_min i.val * i.val)`,
            -- which is `δ_min` by definition of `G_δ`.
            have h_deg_eq : m.degree (m.leadingTerm (h_min i.val) * i.val.val) = m.degree (h_min i.val * i.val.val) := by
              --have hi_in_G : i.val ∈ G.attach := (Finset.mem_filter.mp i.property).1
              have h_h_min_i_ne_zero : h_min i.val ≠ 0 := by
                intro h_h_min_i_zero
                have h_deg_is_δ := (Finset.mem_filter.mp i.property).2
                rw [h_h_min_i_zero, zero_mul, degree_zero, map_zero] at h_deg_is_δ
                exact not_le_of_gt h_min_le_bot (le_of_eq h_deg_is_δ.symm)
              rw [m.degree_mul _ (hG i.val (by simp only [Finset.coe_mem])), degree_leadingTerm, m.degree_mul h_h_min_i_ne_zero (hG i.val (by simp only [Finset.coe_mem]))]
              contrapose! LT_hᵢi_ne_zero
              use i; apply mul_eq_zero_of_left LT_hᵢi_ne_zero
            rw [h_deg_eq]
            apply m.toSyn.injective
            rw [AddEquiv.apply_symm_apply]
            have hi_in_G_δ : i.val ∈ G_δ := i.property
            exact (Finset.mem_filter.mp hi_in_G_δ).2

          -- Hypothesis 3: The degree of the sum has dropped.
          have hsum : m.degree (∑ i ∈ p.support, p i) ≺[m] δ_min := by
            -- We know `∑ i in p.support, p i` is `P₁`.
            have h_sum_p_eq_P₁ : (∑ i ∈ p.support, p i) = P₁ := by
              rw [h_p_support, ← Finset.attach_eq_univ]
              dsimp only [Finsupp.equivFunOnFinite_symm_apply_apply, p, p_fun, P₁]
              exact Finset.sum_attach G_δ (fun i ↦ m.leadingTerm (h_min i) * i)
            rw [h_sum_p_eq_P₁]
            rw [AddEquiv.apply_symm_apply]
            exact hP₁_deg_lt

          have h_syzygy_result :=
            by exact Spolynomial_syzygy_of_degree_cancellation m δ_min p hp_ne_zero hp_deg hsum

          rcases h_syzygy_result.1 with ⟨c, hP₁_rw_S_poly_pᵢ_pⱼ⟩

          have h_S_relation : ∀ (ij : ι × ι), ij ∈ p.support.offDiag →
              S_polynomial m (p ij.1) (p ij.2) =
              monomial (δ_min - (m.degree ij.1.val.val ⊔ m.degree ij.2.val.val)) 1 * S_polynomial m ij.1.val ij.2.val := by
            intro ij hij
            unfold p p_fun at hij
            simp only [Finsupp.equivFunOnFinite_symm_apply_support, Set.Finite.toFinset_setOf,
              ne_eq, mul_eq_zero, not_or, leadingTerm_ne_zero_iff, Finset.mem_offDiag,
              Finset.mem_filter, Finset.mem_univ, true_and] at hij

            let gᵢ := ij.1.val; let gⱼ := ij.2.val
            let hᵢ := h_min gᵢ; let hⱼ := h_min gⱼ
            dsimp only [leadingTerm, Finsupp.equivFunOnFinite_symm_apply_apply, p, p_fun]
            rw [@Spolynomial_of_monomial_mul_eq_monomial_mul_Spolynomial σ m k _ _ (↑ij.1) (↑ij.2) ?_ ?_ (m.degree (h_min ↑ij.1))]
            · --show (monomial (m.degree (h_min ↑ij.1) + m.degree ↑ij.1 - m.degree ↑ij.1 ⊔ m.degree ↑ij.2)) 1 * S_polynomial m ↑ij.1 ↑ij.2 = (monomial (δ_min - m.degree ↑ij.1 ⊔ m.degree ↑ij.2)) 1 * S_polynomial m ↑ij.1 ↑ij.2
              congr 4
              rw [←MonomialOrder.degree_mul hij.1.1 hij.1.2]
              have h_ij1_in_G_δ : ij.1.val ∈ G_δ := ij.1.property
              apply m.toSyn.injective
              rw [AddEquiv.apply_symm_apply]
              exact (Finset.mem_filter.mp h_ij1_in_G_δ).2

            · -- m.leadingCoeff (h_min ↑ij.1) ≠ 0
              rw [MonomialOrder.leadingCoeff_ne_zero_iff]
              exact hij.1.1
            · -- m.leadingCoeff (h_min ↑ij.2) ≠ 0
              rw [MonomialOrder.leadingCoeff_ne_zero_iff]
              exact hij.2.1.1
            · -- m.degree (h_min ↑ij.1) + m.degree ↑ij.1 = m.degree (h_min ↑ij.2) + m.degree ↑ij.2
              rw [←MonomialOrder.degree_mul hij.1.1 hij.1.2, ←MonomialOrder.degree_mul hij.2.1.1 hij.2.1.2]
              apply m.toSyn.injective
              have h_ij1_in_G_δ : ij.1.val ∈ G_δ := ij.1.property
              have h_deg1_eq_δ : m.toSyn (m.degree (h_min ij.1.val * ij.1.val.val)) = δ_syn_min := by
                exact (Finset.mem_filter.mp h_ij1_in_G_δ).2
              have h_ij2_in_G_δ : ij.2.val ∈ G_δ := ij.2.property
              have h_deg2_eq_δ : m.toSyn (m.degree (h_min ij.2.val * ij.2.val.val)) = δ_syn_min := by
                exact (Finset.mem_filter.mp h_ij2_in_G_δ).2
              rw [h_deg1_eq_δ, h_deg2_eq_δ]
            · -- ↑ij.1 ≠ 0
              exact hij.1.2
            · -- ↑ij.2 ≠ 0
              exact hij.2.1.2

          -- Step 2: Formalize (6) and (7) from the textbook.
          -- For any S-polynomial S(gᵢ,gⱼ), since its normal form is 0, the division algorithm
          -- gives us a representation with a good degree property.
          have h_S_poly_gᵢ_gⱼ_repr
            (ij : ι × ι) (hi : ij.1.val ∈ G_δ) (hj : ij.2.val ∈ G_δ) (h_ne : ij.1.val ≠ ij.2.val) :
            --(gᵢ gⱼ : MvPolynomial σ k) (hgᵢ : gᵢ ∈ G) (hgⱼ : gⱼ ∈ G) (h_ne : gᵢ ≠ gⱼ)
            let gᵢ := ij.1.val; let gⱼ := ij.2.val
            let S_poly := S_polynomial m gᵢ gⱼ
            let A := quotients m hG S_poly
            -- Equation (6): A is an element of `↥G →₀ MvPolynomial σ k`
            S_poly = A.sum (fun (g : ↥G) (q : MvPolynomial σ k) => q * g.val) ∧
            -- Equation (7): The degree condition holds.
            (∀ (gₗ : ↥G), m.degree (gₗ.val * A gₗ) ≼[m] m.degree S_poly) := by
            intro gᵢ gⱼ S_poly A
            have hgᵢ : ↑gᵢ ∈ G := by simp only [Finset.coe_mem]
            have hgⱼ : ↑gⱼ ∈ G := by simp only [Finset.coe_mem]
            specialize hS_poly (gᵢ : MvPolynomial σ k) (gⱼ : MvPolynomial σ k) hgᵢ hgⱼ (by exact Subtype.coe_ne_coe.mpr h_ne)

            -- This is the representation from the division algorithm.
            have h_spec := normalForm_spec m hG S_poly

            -- Use the fact that the normal form is zero.
            rw [hS_poly] at h_spec
            simp only [add_zero] at h_spec

            -- Now h_spec.1 is `S_poly = Finsupp.linearCombination ...`.
            -- We need to show this `linearCombination` is the same as our `Finsupp.sum`.
            have h_repr_eq : S_poly = A.sum (fun (g : ↥G) (h : MvPolynomial σ k) => h * g.val) := by
              -- Unfold the definition of `linearCombination` from the division algorithm's spec.
              rw [h_spec.1]
              -- `Finsupp.linearCombination B v f` is defined as `v.sum (fun i a => a • f i)`.
              -- Here, B is `G.toSet`, v is `A`, f is `(fun b => b.val)`.
              -- So it's `A.sum (fun (g : ↥G) (h : MvPolynomial σ k) => h • g.val)`.
              -- Since `h • g.val` is the same as `h * g.val`, the equality holds.
              rfl

            exact ⟨h_repr_eq, h_spec.2.1⟩

          have γ_le_δ (ij : ι × ι) (hi : ij.1.val ∈ G_δ) (hj : ij.2.val ∈ G_δ)
            :
            let i := ij.1; let j := ij.2
            let gᵢ := i.val; let gⱼ := j.val
            m.degree gᵢ.val ⊔ m.degree gⱼ.val ≤ δ_min:= by
            intro i j gᵢ gⱼ
            simp only [sup_le_iff]
            have h_deg_prod_i : m.degree (h_min i.val * i.val.val) = δ_min := by
              apply m.toSyn.injective
              rw [AddEquiv.apply_symm_apply]
              exact (Finset.mem_filter.mp i.property).2
            have h_deg_prod_j : m.degree (h_min j.val * j.val.val) = δ_min := by
              apply m.toSyn.injective
              rw [AddEquiv.apply_symm_apply]
              exact (Finset.mem_filter.mp j.property).2
            constructor
            · rw [←h_deg_prod_i, degree_mul]
              · exact le_add_self
              · intro h_h_min_i_zero
                have h_deg_is_δ := (Finset.mem_filter.mp i.property).2
                rw [h_h_min_i_zero, zero_mul, degree_zero, map_zero] at h_deg_is_δ
                exact not_le_of_gt h_min_le_bot (le_of_eq h_deg_is_δ.symm)
              · exact hG i.val (by simp only [Finset.coe_mem])
            · rw [←h_deg_prod_j, degree_mul]
              · exact le_add_self
              · intro h_h_min_j_zero
                have h_deg_is_δ := (Finset.mem_filter.mp j.property).2
                rw [h_h_min_j_zero, zero_mul, degree_zero, map_zero] at h_deg_is_δ
                exact not_le_of_gt h_min_le_bot (le_of_eq h_deg_is_δ.symm)
              · exact hG j.val ((by simp only [Finset.coe_mem]))

          -- We don't need (h_ne : ij.1.val ≠ ij.2.val) here
          have h_γ_S_poly_gᵢ_gⱼ_deg_lt (ij : ι × ι) (hi : ij.1.val ∈ G_δ) (hj : ij.2.val ∈ G_δ) :
            let i := ij.1; let j := ij.2
            let gᵢ := i.val; let gⱼ := j.val
            let mono_factor := monomial (δ_min - (m.degree gᵢ.val ⊔ m.degree gⱼ.val)) 1
            let S_gij := S_polynomial m gᵢ gⱼ
            let A_ij := quotients m hG S_gij
            m.toSyn (m.degree (mono_factor * S_gij)) < δ_syn_min := by
              let i := ij.1; let j := ij.2
              let gᵢ := i.val; let gⱼ := j.val
              let mono_factor := monomial (δ_min - (m.degree gᵢ.val ⊔ m.degree gⱼ.val)) (1 : k)
              let S_gij := S_polynomial m gᵢ.val gⱼ.val
              let A_ij := quotients m hG S_gij
              by_cases S_poly_zero : S_gij = 0
              · dsimp only [Set.elem_mem, mem_val, Lean.Elab.WF.paramLet, S_gij] at *
                rw [S_poly_zero]
                simp only [mul_zero, degree_zero, map_zero, gt_iff_lt]
                exact h_min_le_bot
              have S_poly_nezero : S_gij ≠ 0 := S_poly_zero
              clear S_poly_zero
              have h_mono_ne_zero : mono_factor ≠ 0 := by rw [Ne, MvPolynomial.monomial_eq_zero]; exact one_ne_zero
              apply lt_of_le_of_lt degree_mul_le
              have mon_deg_δ_min : m.degree ((monomial δ_min) (1:k) ) = δ_min := by
                rw [degree_monomial]
                simp only [one_ne_zero, ↓reduceIte]
              have h1 : m.degree ((monomial (δ_min - m.degree (i : MvPolynomial σ k) ⊔ m.degree (j : MvPolynomial σ k))) (1 : k))
                = m.degree ((monomial (δ_min)) (1 : k)) - m.degree (i : MvPolynomial σ k) ⊔ m.degree (j : MvPolynomial σ k) := by
                rw [mon_deg_δ_min]
                repeat rw [degree_monomial]
                repeat simp only [one_ne_zero, ↓reduceIte]
              rw [h1]
              rw [mon_deg_δ_min]

              rw [hδ_syn]
              have rw_δ_min : (δ_min - m.degree i.val.val ⊔ m.degree j.val.val) + m.degree i.val.val ⊔ m.degree j.val.val = δ_min := by
                rw [tsub_add_cancel_iff_le]
                exact γ_le_δ ij hi hj
              nth_rw 2 [←rw_δ_min]
              rw [map_add, map_add]
              simp only [add_lt_add_iff_left, gt_iff_lt]
              apply degree_S_polynomial_lt_lcm
              · -- show ↑↑ij.1 ≠ 0
                intro h_zero
                -- For example, if degree is defined and zero polynomial has degree -∞, contradict bounds
                have h_deg := (Finset.mem_filter.mp hi).2
                rw [h_zero] at h_deg
                have : δ_syn_min ≤ ⊥ := by
                  simp only [MonomialOrder.bot_eq_zero]
                  rw [←h_deg]; simp only [mul_zero, degree_zero, map_zero, le_refl]
                exact not_le_of_gt h_min_le_bot this

              · -- show ↑↑ij.2 ≠ 0
                intro h_zero
                -- For example, if degree is defined and zero polynomial has degree -∞, contradict bounds
                have h_deg := (Finset.mem_filter.mp hj).2
                rw [h_zero] at h_deg
                have : δ_syn_min ≤ ⊥ := by
                  simp only [MonomialOrder.bot_eq_zero]
                  rw [←h_deg]; simp only [mul_zero, degree_zero, map_zero, le_refl]
                exact not_le_of_gt h_min_le_bot this
              · -- show `γ > 0`
                apply lt_sup_of_lt_left
                apply lt_of_le_of_ne
                · simp only [_root_.zero_le]
                · symm
                  apply h_const_non_ex
                  simp only [Finset.coe_mem]

          by_cases h_γ_zero : ∃ ij : ι × ι, m.toSyn (m.degree ij.1.val.val ⊔ m.degree ij.2.val.val) = 0
          · obtain ⟨ij, hij_γ_is_zero⟩ := h_γ_zero

            have h_sup_is_zero : m.degree ij.1.val.val ⊔ m.degree ij.2.val.val = 0 := by
              exact m.toSyn.injective (by rwa [map_zero])

            -- The sup of two multidegrees is 0 iff both are 0.
            have h_degs_are_zero : m.degree ij.1.val.val = 0 ∧ m.degree ij.2.val.val = 0 := by
              -- We prove each part of the `and`.
              constructor
              · -- Prove `m.degree ij.1.val = 0`.
                -- We know `a ≤ a ⊔ b`.
                have h_le_sup := @le_sup_left _ _ (m.degree ij.1.val.val) (m.degree ij.2.val.val)
                -- Substitute the hypothesis that the sup is 0.
                rw [h_sup_is_zero] at h_le_sup
                -- Now we have `... ≤ 0`. Since 0 is the minimum, it must be an equality.
                exact le_bot_iff.mp h_le_sup
              · -- Prove `m.degree ij.2.val = 0`.
                -- The argument is symmetric.
                have h_le_sup := @le_sup_right _ _ (m.degree ij.1.val.val) (m.degree ij.2.val.val)
                rw [h_sup_is_zero] at h_le_sup
                exact le_bot_iff.mp h_le_sup

            -- Now we have `m.degree ij.1.val = 0`.
            have h_deg_i_is_zero : m.degree ij.1.val.val = 0 := h_degs_are_zero.1

            -- We know `ij.1.val ∈ G`.
            have h_i_in_G : ij.1.val.val ∈ G := by simp only [Finset.coe_mem]

            -- This contradicts our hypothesis `h_const_non_ex`.
            exact False.elim (h_const_non_ex ij.1.val h_i_in_G h_deg_i_is_zero)

          have h_γ_S_poly_gᵢ_gⱼ_repr
            (ij : ι × ι) (hi : ij.1.val ∈ G_δ) (hj : ij.2.val ∈ G_δ) (h_ne : ij.1.val ≠ ij.2.val) :
            let i := ij.1; let j := ij.2
            let gᵢ := i.val; let gⱼ := j.val
            let mono_factor := monomial (δ_min - (m.degree gᵢ.val ⊔ m.degree gⱼ.val)) (1 : k)
            let S_gij := S_polynomial m gᵢ gⱼ
            let A_ij : ↑G →₀ MvPolynomial σ k := quotients m hG S_gij
            let B_ij : ↥G →₀ MvPolynomial σ k :=
              A_ij.mapRange (fun p => mono_factor * p) (by exact CommMonoidWithZero.mul_zero mono_factor)
            mono_factor * S_gij = B_ij.sum (fun (g : ↥G) (h : MvPolynomial σ k) => h * g.val) := by
            intro i j gᵢ gⱼ mono_factor S_gij A_ij B_ij
            -- nth_rw 1 [(h_S_poly_gᵢ_gⱼ_repr gᵢ gⱼ hi hj h_ne).1]
            -- simp only [Set.elem_mem, Finset.mem_val]
            unfold S_gij B_ij A_ij
            rw [Finsupp.sum_mapRange_index (by simp)]
            specialize h_S_poly_gᵢ_gⱼ_repr ij hi hj h_ne
            rw [h_S_poly_gᵢ_gⱼ_repr.1]
            rw [Finsupp.mul_sum]
            congr
            ext
            rw [mul_assoc]

          have h_Bₗgₗ_lt_δ
            (ij : ι × ι) (hi : ij.1.val ∈ G_δ) (hj : ij.2.val ∈ G_δ) (h_ne : ij.1.val ≠ ij.2.val) :
            -- (gᵢ gⱼ : MvPolynomial σ k) (hgᵢ : gᵢ ∈ G) (hgⱼ : gⱼ ∈ G) (h_ne : gᵢ ≠ gⱼ)
            let i := ij.1; let j := ij.2
            let gᵢ := i.val; let gⱼ := j.val
            let mono_factor := monomial (δ_min - (m.degree gᵢ.val ⊔ m.degree gⱼ.val)) (1 : k)
            let S_gij := S_polynomial m gᵢ gⱼ
            let A_ij : ↑G →₀ MvPolynomial σ k := quotients m hG S_gij
            let B_ij : ↥G →₀ MvPolynomial σ k :=
              A_ij.mapRange (fun p => mono_factor * p) (by exact CommMonoidWithZero.mul_zero mono_factor)
            (∀ (gₗ : ↥G), m.degree (gₗ.val * B_ij gₗ) ≺[m] δ_min) := by
            -- simp only
            intro i j gᵢ gⱼ mono_factor S_gij A_ij B_ij gₗ
            have h_mono_ne_zero : mono_factor ≠ 0 := by rw [Ne, monomial_eq_zero]; exact one_ne_zero
            unfold B_ij
            rw [Finsupp.mapRange_apply]
            by_cases h_Aₗ_zero : A_ij gₗ = 0
            · -- unfold B_ij
              -- rw [Finsupp.mapRange_apply]
              rw [h_Aₗ_zero]
              simp only [mul_zero, degree_zero, map_zero, ←hδ_syn]
              exact h_min_le_bot

            have h_gₗAₗ_ne_zero : gₗ.val * A_ij gₗ ≠ 0 := by rw [mul_ne_zero_iff]; exact ⟨hG gₗ gₗ.2, h_Aₗ_zero⟩
            by_cases hS_poly_zero : S_polynomial m gᵢ.val gⱼ.val = 0
            · specialize h_γ_S_poly_gᵢ_gⱼ_repr ij hi hj h_ne
              have h_gₗAₗ_deg_zero : m.toSyn (m.degree (gₗ.val * A_ij gₗ)) = m.toSyn 0 := by
                have h_spec := normalForm_spec m hG S_gij
                have := h_spec.2.1 gₗ
                unfold S_gij at this
                nth_rw 2 [hS_poly_zero] at this
                simp only [Set.elem_mem, Finset.mem_val, degree_zero, map_zero] at this
                rw [←m.bot_eq_zero, le_bot_iff, m.bot_eq_zero] at this
                unfold A_ij S_gij
                rw [map_zero]
                exact this

              rw [←mul_assoc, mul_comm gₗ.val, mul_assoc, degree_mul h_mono_ne_zero h_gₗAₗ_ne_zero]
              rw [map_add, h_gₗAₗ_deg_zero, map_zero, add_zero]
              unfold mono_factor

              have rw_δ_min : (δ_min - m.degree i.val.val ⊔ m.degree j.val.val) + m.degree i.val.val ⊔ m.degree j.val.val = δ_min := by
                rw [tsub_add_cancel_iff_le]
                exact γ_le_δ ij hi hj
              nth_rw 2 [←rw_δ_min]
              rw [map_add, degree_monomial]
              simp only [one_ne_zero, ↓reduceIte]
              have : m.toSyn (δ_min - m.degree gᵢ.val ⊔ m.degree gⱼ.val) = m.toSyn (δ_min - m.degree gᵢ.val ⊔ m.degree gⱼ.val) + 0 := by simp only [add_zero]
              nth_rw 1 [←add_zero (m.toSyn (δ_min - m.degree gᵢ.val ⊔ m.degree gⱼ.val))]
              rw [add_lt_add_iff_left]
              push_neg at h_γ_zero
              rw [←MonomialOrder.bot_eq_zero, bot_lt_iff_ne_bot]
              exact h_γ_zero ij
            have := h_γ_S_poly_gᵢ_gⱼ_deg_lt ij hi hj
            rw [←hδ_syn]
            apply lt_of_le_of_lt _ (h_γ_S_poly_gᵢ_gⱼ_deg_lt ij hi hj)
            rw [←mul_assoc, mul_comm gₗ.val, mul_assoc, degree_mul h_mono_ne_zero h_gₗAₗ_ne_zero, map_add]
            nth_rw 2 [degree_mul, degree_monomial]
            simp only [one_ne_zero, ↓reduceIte, map_add]
            unfold mono_factor gᵢ gⱼ
            rw [degree_monomial]
            simp only [one_ne_zero, ↓reduceIte]
            rw [add_le_add_iff_left]
            specialize h_S_poly_gᵢ_gⱼ_repr ij hi hj h_ne
            apply h_S_poly_gᵢ_gⱼ_repr.2 gₗ
            · unfold mono_factor at h_mono_ne_zero
              exact h_mono_ne_zero
            · exact hS_poly_zero

          have h_P₁_rw1 : P₁ = ∑ ij ∈ p.support.offDiag, c ij • S_polynomial m (p ij.1) (p ij.2) := by
            convert hP₁_rw_S_poly_pᵢ_pⱼ

          have h_P₁_rw2 : P₁ = ∑ ij ∈ p.support.offDiag, c ij • ((monomial (δ_min - m.degree ij.1.val.val ⊔ m.degree ij.2.val.val) 1) * S_polynomial m ij.1.val ij.2.val) := by
            rw [h_P₁_rw1]
            apply Finset.sum_congr rfl
            intro ij hij
            congr 1
            exact h_S_relation ij hij

          have h_P₁_rw3 : P₁ = ∑ ij ∈ p.support.offDiag, c ij • (
              let gᵢ := ij.1.val; let gⱼ := ij.2.val
              let mono_factor := monomial (δ_min - (m.degree gᵢ.val ⊔ m.degree gⱼ.val)) 1
              let S_gij := S_polynomial m gᵢ gⱼ
              let A_ij := quotients m hG S_gij
              let B_ij : ↥G →₀ MvPolynomial σ k :=
                A_ij.mapRange (fun p => mono_factor * p) (by exact CommMonoidWithZero.mul_zero mono_factor)
              B_ij.sum (fun (g : ↥G) (h : MvPolynomial σ k) => h * g.val)
            ) := by

            rw [h_P₁_rw2]
            apply Finset.sum_congr rfl
            intro ij hij
            congr 1
            -- This is exactly `h_γ_S_poly_gᵢ_gⱼ_repr`.
            apply h_γ_S_poly_gᵢ_gⱼ_repr ij ij.1.property ij.2.property ?_
            simp only [Finset.mem_offDiag, Finsupp.mem_support_iff] at hij
            apply Subtype.val_injective.ne
            exact hij.2.2

          let B_tilde : ↥G →₀ MvPolynomial σ k :=
              ∑ ij ∈ (p.support).offDiag,
                let gᵢ := ij.1.val; let gⱼ := ij.2.val
                let mono_factor := monomial (δ_min - (m.degree gᵢ.val ⊔ m.degree gⱼ.val)) 1
                let A_ij := quotients m hG (S_polynomial m gᵢ gⱼ)
                let B_ij : ↥G →₀ MvPolynomial σ k := A_ij.mapRange
                  (fun p => mono_factor * p) (by exact CommMonoidWithZero.mul_zero mono_factor)
                c ij • B_ij

          have h_P₁_rw4 : P₁ = B_tilde.sum (fun (g : ↥G) (h : MvPolynomial σ k) => h * g.val) := by
            -- Start with the representation of P₁ from h_P₁_rw3.
            rw [h_P₁_rw3]

            unfold B_tilde
            rw [←Finsupp.sum_finset_sum_index (by simp) (by ring_nf; simp)]
            congr 1
            funext ij
            ring_nf

            rw [←MvPolynomial.C_mul']
            rw [Finsupp.mul_sum]
            rw [Finsupp.sum_smul_index']
            · simp only [Algebra.smul_mul_assoc]
              congr
              funext g h
              rw [MvPolynomial.C_mul']
            · simp only [zero_mul, implies_true]

          let h_P₂_fun (g : ↥G) : MvPolynomial σ k :=
            if g ∈ G_δ then (h_min g - leadingTerm m (h_min g)) else 0
          let h_P₂_finsupp : ↥G →₀ MvPolynomial σ k :=
            (Finsupp.equivFunOnFinite).symm h_P₂_fun

          let h_P₃_fun (g : ↥G) : MvPolynomial σ k :=
            if g ∈ G.attach \ G_δ then h_min g else 0
          let h_P₃_finsupp : ↥G →₀ MvPolynomial σ k :=
            (Finsupp.equivFunOnFinite).symm h_P₃_fun

          -- Now, all three Finsupps have the same type `↥G →₀ MvPolynomial σ k`.
          -- The definition of `h_new` is now well-defined.
          let h_new : ↥G →₀ MvPolynomial σ k := B_tilde + h_P₂_finsupp + h_P₃_finsupp

          have h_f_eq_new : f = h_new.sum (fun g h => h * g.val) := by
            rw [h_f_is_P123, h_P₁_rw4]
            unfold h_new
            rw [Finsupp.sum_add_index, Finsupp.sum_add_index]
            · rw [add_assoc, add_assoc, add_left_cancel_iff]
              have G_sep : G.attach = G_δ ∪ (G.attach \ G_δ) := by
                refine Eq.symm (Finset.union_sdiff_of_subset ?_)
                apply Finset.filter_subset
              -- show P₂ + P₃ = (h_P₂_finsupp.sum fun g h ↦ h * ↑g) + h_P₃_finsupp.sum fun g h ↦ h * ↑g
              congr
              · -- P₂ = h_P₂_finsupp.sum fun g h ↦ h * ↑g
                unfold P₂
                -- Unfold the sum of the finsupp.
                -- `h_P₂_finsupp` was defined via `equivFunOnFinite`. Its sum can be rewritten.
                have h_rhs_eq_sum_univ :
                    h_P₂_finsupp.sum (fun g h => h * g.val)
                    = ∑ i ∈ (Finset.univ : Finset ↥G), h_P₂_fun i * i.val := by
                  dsimp only [univ_eq_attach, h_P₂_finsupp]
                  rw [Finsupp.equivFunOnFinite_symm_eq_sum]
                  simp only [Finset.univ_eq_attach]
                  have h_sum_of_sum_single :
                    ((∑ a ∈ G.attach, Finsupp.single a (h_P₂_fun a))).sum (fun g h => h * g.val)
                    = ∑ a ∈ G.attach, (h_P₂_fun a) * a.val := by
                    -- Let `F g h := h * g.val` be the function inside the `Finsupp.sum`.

                    -- `Finsupp.sum` distributes over `Finset.sum`.
                    -- The lemma is `Finsupp.sum_sum_index`.
                    rw [←Finsupp.sum_finset_sum_index]
                    · congr
                      funext g
                      simp only [zero_mul, Finsupp.sum_single_index]
                    · simp only [zero_mul, implies_true]
                    · ring_nf; simp only [implies_true]
                  exact h_sum_of_sum_single
                rw [h_rhs_eq_sum_univ]
                unfold h_P₂_fun
                simp only [Finset.univ_eq_attach, ite_mul, zero_mul]
                rw [G_sep]
                rw [Finset.sum_union]
                simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sdiff_inter_self,
                  Finset.sum_empty, add_zero]
                exact Finset.disjoint_sdiff

              · -- show P₃ = h_P₃_finsupp.sum fun g h ↦ h * ↑g
                dsimp only [P₃, h_P₃_finsupp]
                rw [Finsupp.equivFunOnFinite_symm_eq_sum]
                simp only [Finset.univ_eq_attach]
                -- Step 1: Prove the helper lemma to simplify the `Finsupp.sum`.
                have h_sum_of_sum_single :
                    ((∑ a ∈ G.attach, Finsupp.single a (h_P₃_fun a))).sum (fun g h => h * g.val)
                    = ∑ a ∈ G.attach, (h_P₃_fun a) * a.val := by
                  rw [←Finsupp.sum_finset_sum_index]
                  · congr
                    funext g
                    rw [Finsupp.sum_single_index]
                    exact zero_mul g.val
                  · -- Side condition 1 for `sum_sum_index'`: `F 0 = 0`.
                    simp only [zero_mul, implies_true]
                  · -- Side condition 2 for `sum_sum_index'`: `F` is additive.
                    ring_nf; simp only [implies_true]

                rw [h_sum_of_sum_single]
                unfold h_P₃_fun

                simp only [Finset.mem_sdiff, Finset.mem_attach, true_and, ite_not, ite_mul,
                  zero_mul]

                rw [Finset.sum_ite_not_mem]

            · -- show ∀ a ∈ B_tilde.support ∪ h_P₂_finsupp.support, 0 * ↑a = 0
              intro a ha_in_union; exact zero_mul a.val
            · -- show ∀ a ∈ B_tilde.support ∪ h_P₂_finsupp.support, ∀ (b₁ b₂ : MvPolynomial σ k), (b₁ + b₂) * ↑a = b₁ * ↑a + b₂ * ↑a
              intro a ha_in_union b₁ b₂; exact add_mul b₁ b₂ a.val
            · -- show ∀ a ∈ (B_tilde + h_P₂_finsupp).support ∪ h_P₃_finsupp.support, 0 * ↑a = 0
              intro a ha_in_union; exact zero_mul a.val
            · -- show ∀ a ∈ (B_tilde + h_P₂_finsupp).support ∪ h_P₃_finsupp.support, ∀ (b₁ b₂ : MvPolynomial σ k), (b₁ + b₂) * ↑a = b₁ * ↑a + b₂ * ↑a
              intro a ha_in_union b₁ b₂; exact add_mul b₁ b₂ a.val

          let δ_new_min := (Finset.image (⇑m.toSyn ∘ fun g ↦ m.degree (h_new g * g.val)) G.attach).sup id

          have δ_new_min_lt_δ_syn_min : δ_new_min < δ_syn_min := by
            rw [Finset.sup_lt_iff h_min_le_bot]
            intro Hg Hg_mem
            simp only [id_eq]
            simp only [Finset.mem_image, Function.comp_apply] at Hg_mem
            obtain ⟨g, ⟨hg_mem_G, h_eq_Hg⟩⟩ := Hg_mem
            rw [←h_eq_Hg]; clear Hg h_eq_Hg
            unfold h_new
            simp only [Finsupp.coe_add, Pi.add_apply]
            rw [right_distrib, right_distrib]
            apply lt_of_le_of_lt MonomialOrder.degree_add_le
            apply max_lt
            · apply lt_of_le_of_lt MonomialOrder.degree_add_le
              apply max_lt
              · -- show m.toSyn (m.degree (B_tilde g * ↑g)) < δ_syn_min
                unfold B_tilde

                simp only [Finsupp.coe_finset_sum, Finsupp.coe_smul,
                    sum_apply, Pi.smul_apply, Finsupp.mapRange_apply]
                ring_nf
                rw [Finset.sum_mul]
                apply lt_of_le_of_lt
                  (m.degree_sum_le_syn (p.support.offDiag)
                  (fun ij ↦ c ij • ((monomial (δ_min - m.degree ij.1.val.val ⊔ m.degree ij.2.val.val)) (1 : k) * (quotients m hG (S_polynomial m ↑↑ij.1 ↑↑ij.2)) g) * g.val))
                rw [Finset.sup_lt_iff h_min_le_bot]
                intro ij hij_mem_p_supp_offdiag
                have := h_Bₗgₗ_lt_δ ij (coe_mem ij.1) (coe_mem ij.2) (Subtype.coe_ne_coe.mpr ((Finset.mem_offDiag.mp hij_mem_p_supp_offdiag).2.2))
                have kk := this g
                rw [←MvPolynomial.C_mul']
                rw [mul_assoc _ _ g.val]
                apply lt_of_le_of_lt MonomialOrder.degree_mul_le
                rw [map_add]
                simp only [degree_C, map_zero, Set.elem_mem, mem_val, zero_add]
                rw [hδ_syn]
                simp only [Finsupp.mapRange_apply, mul_comm g.val _] at kk
                exact kk

              · -- show m.toSyn (m.degree (h_P₂_finsupp g * ↑g)) < δ_syn_min
                unfold h_P₂_finsupp
                simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
                unfold h_P₂_fun
                simp only [ite_mul, zero_mul]
                by_cases h : g ∈ G_δ
                · rw [ite_cond_eq_true ((h_min g - m.leadingTerm (h_min g)) * g.val) 0 (eq_true h)]
                  exact h_P₂term_deg_lt g h
                · rw [ite_cond_eq_false ((h_min g - m.leadingTerm (h_min g)) * g.val) 0 (eq_false h)]
                  simp only [degree_zero, map_zero]
                  exact h_min_le_bot


            · -- show m.toSyn (m.degree (h_P₃_finsupp g * ↑g)) < δ_syn_min
              unfold h_P₃_finsupp
              simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
              unfold h_P₃_fun
              simp only [ite_mul, zero_mul]
              by_cases h : g ∈ G.attach \ G_δ
              · rw [ite_cond_eq_true ((h_min g) * g.val) 0 (eq_true h)]
                exact h_P₃term_deg_lt g h
              · rw [ite_cond_eq_false ((h_min g) * g.val) 0 (eq_false h)]
                simp only [degree_zero, map_zero]
                exact h_min_le_bot

          have h_new_in : δ_new_min ∈ RepMaxSynDegrees := by
            use h_new
            -- δ_new_min was defined to be the sup for h_new, so the equality is `rfl` by definition
            refine ⟨?_, rfl⟩
            have : h_new.sum (fun g h ↦ h * ↑g) = ∑ g ∈ G.attach, h_new g * ↑g := by
              rw [Finsupp.sum]
              have support_subset : h_new.support ⊆ G.attach := by
                unfold h_new

                apply Finset.Subset.trans Finsupp.support_add
                · apply Finset.union_subset
                  · exact Finset.subset_univ _
                  · exact Finset.subset_univ _

              rw [Finset.sum_subset support_subset]
              intro g hg_in_G hg_not_in_h_new
              simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hg_not_in_h_new
              rw [hg_not_in_h_new, zero_mul]

            rw [←this]; exact h_f_eq_new

          have h_min_property := WellFounded.not_lt_min (by exact wellFounded_lt) RepMaxSynDegrees h_RepMaxSynDegrees_nonempty h_new_in
          exact False.elim (h_min_property δ_new_min_lt_δ_syn_min)

variable [DecidableEq σ] in
lemma grobner_basis_remove_redundant
  {I : Ideal _} {G : Finset _} {p : MvPolynomial σ k}
  (hG : IsGroebnerBasis m I G)
  (hpG : p ∈ G)
  (hLT : leadingTerm m p ∈ Ideal.span ((G.erase p).image (fun g ↦ leadingTerm m g))) :
  IsGroebnerBasis m I (G.erase p) := by

  -- Let G' be the smaller basis for clarity.
  let G' := G.erase p

  -- We need to prove the three properties of a Gröbner basis for G'.
  -- 1. `G'` is zero-free.
  have hG'_zero_free : ∀ g ∈ G', g ≠ 0 := by
    intro g hg_in_G'
    -- An element of `G.erase p` is also an element of `G`.
    have hg_in_G : g ∈ G := Finset.mem_of_mem_erase hg_in_G'
    -- Now use the property from the original basis `hG`.
    exact hG.1 g hg_in_G

  -- 2. `G'` is a subset of the ideal `I`.
  have hG'_subset_I : (G' : Set (MvPolynomial σ k)) ⊆ I := by
    -- We will show `G' ⊆ G` and `G ⊆ I`.
    apply Set.Subset.trans
    · -- First goal: `↑G' ⊆ ↑G`.
      apply Finset.coe_subset.mpr
      exact Finset.erase_subset p G
    · -- Second goal: `↑G ⊆ I`.
      exact hG.2.1

  -- 3. The ideal of leading terms of `G'` is the initial ideal of `I`.
  have h_lt_ideal_eq : Ideal.span (G'.image (leadingTerm m)) = leadingTermIdeal m I := by
    -- From `hG`, we know `<LT(G)> = initialIdeal I`.
    -- So we just need to prove `<LT(G')> = <LT(G)>`.
    rw [← hG.2.2]

    -- We prove equality by proving inclusion in both directions.
    apply le_antisymm

    · -- First direction: `<LT(G')> ⊆ <LT(G)>`.
      -- This is true because `G' ⊆ G`.
      apply Ideal.span_mono
      simp only [coe_image]
      refine Set.image_mono ?_
      exact Finset.erase_subset p G

    · -- Second direction: `<LT(G)> ⊆ <LT(G')>`.
      -- We need to show every generator `LT(g)` for `g ∈ G` is in `<LT(G')>`.
      rw [Ideal.span_le, Finset.coe_image, Set.subset_def]
      intro lt_g h_lt_g_mem

      -- Unpack the image to get `g`.
      rcases h_lt_g_mem with ⟨g, hg_in_G, rfl⟩

      -- We now have a `g ∈ G`. We need to show `LT(g) ∈ <LT(G')>`.
      -- We split by cases: either `g = p` or `g ≠ p`.
      by_cases h_g_is_p : g = p

      · -- Case 1: `g = p`.
        -- We need to show `LT(p) ∈ <LT(G')>`.
        subst h_g_is_p
        simp only [coe_image] at hLT
        exact hLT

      · -- Case 2: `g ≠ p`.
        -- Since `g ∈ G` and `g ≠ p`, we have `g ∈ G.erase p`, which is `g ∈ G'`.
        have hg_in_G' : g ∈ G' := Finset.mem_erase.mpr ⟨h_g_is_p, hg_in_G⟩

        -- Since `g ∈ G'`, its leading term `LT(g)` is a generator of `<LT(G')>`.
        apply Ideal.subset_span
        exact Set.mem_image_of_mem m.leadingTerm hg_in_G'

  -- Now we have all three properties, so we can construct the final proof.
  simp only [coe_image] at h_lt_ideal_eq
  exact ⟨hG'_zero_free, ⟨hG'_subset_I, h_lt_ideal_eq⟩⟩

end Field
end MvPolynomial
