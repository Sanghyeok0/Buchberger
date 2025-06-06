import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Ring.Defs
import Buchberger.MonomialIdeal
import Buchberger.Order2

variable {σ : Type*} -- [DecidableEq σ]
variable {m : MonomialOrder σ}

open MonomialOrder MvPolynomial

-- Mathlib4 최신버전에 있는 코드들----------------------------

namespace MonomialOrder

variable {R : Type*} [CommSemiring R]

lemma degree_mem_support {p : MvPolynomial σ R} (hp : p ≠ 0) :
    m.degree p ∈ p.support := by
  rwa [MvPolynomial.mem_support_iff, coeff_degree_ne_zero_iff]

end MonomialOrder
---------------------------------------------------------------

namespace MonomialOrder

set_option maxHeartbeats 3000000

/-
## Reference : [Becker-Weispfenning1993]

-/

section Semiring

variable {R : Type*} [CommSemiring R]

/-- The multidegree of the leading term `LT(f)` is equal to the degree of `f`. -/
lemma degree_leadingTerm (f : MvPolynomial σ R) :
    m.degree (leadingTerm m f) = m.degree f := by
  rw [leadingTerm]
  let d := m.degree f
  let c := m.leadingCoeff f -- which is coeff d f
  -- Use the degree_monomial lemma, which depends on whether the coefficient is zero
  have : Decidable (c = 0) := by exact Classical.propDecidable (c = 0)
  rw [m.degree_monomial c]
  split_ifs with hc -- hc : c = 0
  · show 0 = m.degree f
    rw [m.leadingCoeff_eq_zero_iff] at hc
    rw [hc, m.degree_zero]
  · -- Case 2: c ≠ 0.
    rfl

end Semiring

section CommRing

variable {R : Type*} [CommRing R]

variable (m) in
/-- f reduces to g modulo a single nonzero p by eliminating term t -/
def red_poly_step_by_term (p f g : MvPolynomial σ R) (hp : IsUnit (m.leadingCoeff p)) (t : σ →₀ ℕ) : Prop :=
  g = f - (MvPolynomial.monomial (t - (m.degree p)) (hp.unit⁻¹ * f.coeff t)) * p

variable (m) in
/-- f reduces to g modulo a single nonzero p by eliminating one term -/
def red_poly_step (p f g : MvPolynomial σ R) (hp : IsUnit (m.leadingCoeff p)) : Prop :=
  ∃ t, red_poly_step_by_term m p f g hp t

variable (m) in
/-- One‐step reduction modulo a set `P`.  (Definition 5.18 (iii)). -/
def Red_Poly_step (P : Set (MvPolynomial σ R))
  (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) :
  MvPolynomial σ R → MvPolynomial σ R → Prop
| f, g => ∃ (p : MvPolynomial σ R) (hp : p ∈ P),
    red_poly_step m p f g (hP p hp)

/-- (iii)  In a single step `f →[p] g` eliminating `t`,
  * `t ∉ g.support`, and
  * for every `u > t`, `u ∈ f.support ↔ u ∈ g.support`. -/
theorem support_after_step
  {p f g : MvPolynomial σ R}
  (hp : IsUnit (m.leadingCoeff p))
  {t : σ →₀ ℕ}
  (h : red_poly_step_by_term m p f g hp t)
  : (t ∉ g.support) ∧ ∀ u, t < u → (u ∈ f.support ↔ u ∈ g.support) := by
  rw [red_poly_step_by_term] at h
  have : m.degree ((monomial (t - m.degree p)) (↑hp.unit⁻¹ * coeff t f) * p) = t := by sorry
  constructor
  · sorry
  · sorry


/-- Single‐step "top" reduction by any `p ∈ P`. -/
def Reduce (m : MonomialOrder σ)
  (P : Set (MvPolynomial σ R)) (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) :
  MvPolynomial σ R → MvPolynomial σ R → Prop
| g, f => ∃ (p : MvPolynomial σ R) (hp : p ∈ P) (hpf : m.degree p ≤ m.degree f) (hf : m.degree f ≠ 0) , g = m.reduce (hP p hp) f

/-- **Theorem 5.21.**  For any `P ⊆ K[X]`, the relation `→[P]` is a noetherian reduction. (top‐reduction case).-/
theorem Reduce.noetherian
  (P : Set (MvPolynomial σ R))
  (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) :
  IsAsymm _ (m.Reduce P hP) ∧ WellFounded (m.Reduce P hP) := by
  constructor
  · -- asymmetry:
    refine { asymm := ?_ }
    intro f g hfg hgf
    simp only [Reduce] at hfg
    rcases hfg with ⟨p, hpP, hpg, hg_ne, hf_red_g⟩
    simp only [Reduce] at hgf
    rcases hgf with ⟨q, hqP, hqf, hf_ne, hg_red_f⟩

    have d1 : (m.degree g) ≺[m] (m.degree f) := by
      rw [hg_red_f]
      exact degree_reduce_lt (hP q hqP) hqf hf_ne
    have d2 : (m.degree f) ≺[m] (m.degree g) := by
      rw [hf_red_g]
      exact degree_reduce_lt (hP p hpP) hpg hg_ne
    let cyc : m.degree f ≺[m] m.degree f := by
      simpa using d2.trans d1
    exact (lt_self_iff_false (m.toSyn (m.degree f))).mp cyc

  · -- Well‐foundedness
    apply WellFounded.wellFounded_iff_no_descending_seq.mpr
    by_contra h
    simp at h
    obtain ⟨f_seq, h_step⟩ := h
    let u_seq : ℕ → (σ →₀ ℕ) := fun n => m.degree (f_seq n)
    have h_dec : ∀ n, u_seq (n+1) ≺[m] u_seq n := by
      intro n
      simp only [Reduce] at h_step
      obtain ⟨p, ⟨hp_mem, ⟨hpf, ⟨hf, f_red⟩⟩⟩⟩ := h_step n
      have : m.degree (m.reduce (hP p hp_mem) (f_seq n)) ≺[m] m.degree (f_seq n) := by
        apply degree_reduce_lt (hP p hp_mem) hpf hf
      simp only [f_red, gt_iff_lt, u_seq]
      exact this
    have m_wf : WellFounded (· ≺[m] ·) := by
      have : WellFounded (· < ·) := (m.wf.wf)
      exact WellFounded.onFun this
    -- convert to the subtype of strictly‐descending sequences
    let desc_sub : {u : ℕ → _ // ∀ n, (· ≺[m] ·) (u (n+1)) (u n)} :=
      ⟨u_seq, h_dec⟩
    have no_seq : IsEmpty { f : ℕ → (σ →₀ ℕ)// ∀ (n : ℕ), (· ≺[m] ·) (f (n + 1)) (f n) } := by
      rw [WellFounded.wellFounded_iff_no_descending_seq] at m_wf
      exact m_wf
    exact no_seq.elim desc_sub

variable (m) in
def normalform_rel (P : Set (MvPolynomial σ R))
  (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) (f g : MvPolynomial σ R) :=
  @Relation.NormalFormof _ (Reduce m P hP) (Reduce.noetherian P hP).1 g f

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

* Authors: Antoine Chambert-Loir

* Prove that under `Field F`, `IsUnit (m.leadingCoeff (b i))` is
equivalent to `b i ≠ 0`.
-/
omit [DecidableEq k] in
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
/-
## TODO
normalForm과 remainder를 하나로 합치기
-/

variable (m) in
noncomputable def normalForm
  (B : Set (MvPolynomial σ k))
  (hB : ∀ b ∈ B, b ≠ 0)
  (f : MvPolynomial σ k) : MvPolynomial σ k := by
  choose gcomb r hr using
    MonomialOrder.div_set
      (fun b hb => (isUnit_leadingCoeff_iff_nonzero m b).mpr (hB b hb))
      f
  exact r

-- Proposition 3. -- (hI : I ≠ ⊥) -- 증명 수정 필요
variable [Fintype σ] [DecidableEq σ] in
theorem initialIdeal_is_FG (I : Ideal (MvPolynomial σ k)) : (initialIdeal m I).FG := by
  -- 1. Show initialIdeal m I is spanned by monomials with coefficient 1
  rw [initialIdeal_is_monomial_ideal' I]
  rw [Ideal.FG]
  rw [Mvpoly_to_mono]
  have h_fg : (monomialIdeal k (LM_set m I)).FG := Dickson_lemma_MV k (LM_set m I)
  obtain ⟨b, h_span⟩ := h_fg
  use b
  exact h_span

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
Proposition 1.  If `G` is a Gröbner basis for `I`, then every `f` admits
a unique decomposition `f = g + r` with
1. `g ∈ I`, and
2. no term of `r` is divisible by any `LT gᵢ`.
-/
theorem remainder_exists_unique
  {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
  (hGB     : IsGroebnerBasis m I G)
  --(hG_unit : ∀ gi ∈ G, IsUnit (m.leadingCoeff gi))
  (f : MvPolynomial σ k) :
  ∃! r : MvPolynomial σ k,
    (∃ g, g ∈ I ∧ f = g + r) ∧
    ∀ c ∈ r.support, ∀ gi ∈ G, ¬ m.degree gi ≤ c := by
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


variable [DecidableEq σ] in
/-- The unique remainder of `f` upon division by a Gröbner basis `G`. -/
noncomputable def remainder
  {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
  (hGB : IsGroebnerBasis m I G)
  (f : MvPolynomial σ k) : MvPolynomial σ k :=
  Classical.choose (ExistsUnique.exists (remainder_exists_unique hGB f))

variable [DecidableEq σ] in
/--
**§6 Corollary 2**
Let $G = \{g_1,\dots,g_t\}$ be a Gröbner basis for an ideal $I \subseteq k[x_1,\dots,x_n]$ and let $f \in k[x_1,\dots,x_n]$.
Then $f \in I$ if and only if the remainder on division of $f$ by $G$ is zero.
-/
theorem mem_I_iff_normalForm_eq_zero
  {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
  (hGB : IsGroebnerBasis m I G)
  (f : MvPolynomial σ k) :
  f ∈ I ↔ normalForm m G hGB.1 f = 0 := by
  -- prepare the two hypotheses for `div_set` and for uniqueness
  --let B := G.toSet
  --have hB : ∀ b ∈ B, b ≠ 0 := fun _ hb => hGB.1 _ hb
  let hU : ∀ g ∈ G, IsUnit (m.leadingCoeff g) := fun g hg =>
    (isUnit_leadingCoeff_iff_nonzero m g).mpr (hGB.1 g hg)
  have unique_rem := remainder_exists_unique hGB f

  constructor
  · -- (→) if `f ∈ I` then the chosen remainder must be `0`
    intro hf
    -- build the “r = 0” witness of the unique‐remainder property
    have P₀ :
      (∃ g, g ∈ I ∧ f = g + 0) ∧
      ∀ c ∈ (0 : MvPolynomial σ k).support, ∀ gi ∈ G, ¬ m.degree gi ≤ c := by
      constructor
      · use f; constructor; exact hf; simp
      · simp
    -- build the “r = normalForm …” witness
    have Pn :
      (∃ g, g ∈ I ∧ f = g + normalForm m G hGB.1 f) ∧
      ∀ c ∈ (normalForm m G hGB.1 f).support, ∀ gi ∈ G, ¬ m.degree gi ≤ c := by
      obtain ⟨q, r, ⟨hre, _, hnil⟩⟩ :=
        MonomialOrder.div_set hU f
      dsimp [normalForm]
      constructor
      · -- `g := ∑ q i • (i : MvPolynomial)`
        use q.sum fun i coeff => coeff • (i : MvPolynomial σ k)
        -- this `g` lies in `I` because `G ⊆ I`
        have : ∀ i ∈ q.support, (i : MvPolynomial σ k) ∈ I := fun i hi =>
          hGB.2.1 i.2
        sorry
        --refine ⟨Submodule.sum_smul_mem I _ this, _⟩
        --simpa [Finsupp.sum, *] using hre
      · sorry
    -- now uniqueness forces `normalForm … = 0`
    sorry
    --simpa [normalForm] using unique_rem.2 _ _ Pn P₀

  · -- (←) if the remainder is `0` then `f = g + 0 ∈ I`
    intro h0
    obtain ⟨q, r, ⟨hre, _, _⟩⟩ := MonomialOrder.div_set hU f
    -- since `r = normalForm … = 0`, we get `f = ∑ q i • i`
    sorry

variable [DecidableEq σ] in
/--
**§6 Corollary 2**
Let $G = \{g_1,\dots,g_t\}$ be a Gröbner basis for an ideal $I \subseteq k[x_1,\dots,x_n]$ and let $f \in k[x_1,\dots,x_n]$.
Then $f \in I$ if and only if the remainder on division of $f$ by $G$ is zero.
-/
theorem mem_ideal_iff_remainder_GB_eq_zero
  {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
  (hGB : IsGroebnerBasis m I G)
  (f   : MvPolynomial σ k) :
  f ∈ I ↔ remainder hGB f = 0 := by
  constructor
  · rw [remainder]
    rw [IsGroebnerBasis] at hGB
    sorry
  · sorry

variable (m) in
/-- The S-polynomial. -/
noncomputable def S_polynomial (f g : MvPolynomial σ k) : MvPolynomial σ k :=
  let γ := monomial (m.degree f ⊔ m.degree g) (1 : k)
  (γ - leadingTerm m f) * f - (γ - leadingTerm m g) * g

/--
**Lemma 5 (Cox, Little, O'Shea, Ch 2, §6, Lemma 5): Cancellation Lemma**
Suppose we have a sum `P = ∑ pᵢ` where all `pᵢ` have the same multidegree `δ`.
If `m.degree P < δ`, then `P` is a linear combination of the S-polynomials `S(pⱼ, pₗ)`,
and each `S(pⱼ, pₗ)` has multidegree less than `δ`.
-/
lemma exists_S_polynomial_syzygies
    (p : Finset (MvPolynomial σ k)) -- The list of polynomials p₁, ..., pₛ
    (δ : σ →₀ ℕ) -- The common multidegree
    (hp_deg : ∀ pi ∈ p, m.degree pi = δ) -- All polynomials have multidegree δ
    (hsum   : m.degree (∑ pi ∈ p, pi) ≺[m] δ)
    : ∃ coeff : MvPolynomial σ k → MvPolynomial σ k → k,
      (∑ pi ∈ p, pi = ∑ pi ∈ p, ∑ pj ∈ p, coeff pj pi • S_polynomial m pj pi
      ∧ ∀ pi ∈ p, ∀ pj ∈ p, m.degree (S_polynomial m pj pi) ≺[m] δ)
      := by sorry

/-
Buchberger’s Criterion (Theorem 6) says:
Let `I` be a polynomial ideal and let `G` be a basis of `I` (i.e. `I =
ideal.span G`).
Then `G` is a Gröbner basis if and only if for all pairs of distinct polynomials
`g₁, g₂ ∈ G`, the remainder on division of `S_polynomial g₁ g₂` by `G` is zero.
-/

variable (m) [Fintype σ] [DecidableEq σ] in
theorem Buchberger_criterion
  {I : Ideal (MvPolynomial σ k)}
  {G : Finset (MvPolynomial σ k)}
  (hG : ∀ g ∈ G, g ≠ 0)
  (hGI : I = Ideal.span G) :
  IsGroebnerBasis m I G ↔
    (∀ (g₁ g₂ : MvPolynomial σ k),
      g₁ ∈ G →
      g₂ ∈ G →
      g₁ ≠ g₂ → normalForm m G hG (S_polynomial m g₁ g₂) = 0) := by sorry

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

/-Old version-/
-- variable [DecidableEq (σ →₀ ℕ)] [DecidableEq (MvPolynomial σ k)] [DecidableEq k] in
-- /--
-- Proposition 1.  If `G` is a Gröbner basis for `I`, then every `f` admits
-- a unique decomposition `f = g + r` with
-- 1. `g ∈ I`, and
-- 2. no term of `r` is divisible by any `LT gᵢ`.
-- -/
-- theorem remainder_exists_unique'
--   {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
--   (hGB     : IsGroebnerBasis m I G)
--   (hG_unit : ∀ gi ∈ G, IsUnit (m.leadingCoeff gi))
--   (f : MvPolynomial σ k) :
--   ∃! r : MvPolynomial σ k,
--     (∃ g, g ∈ I ∧ f = g + r) ∧
--     ∀ c ∈ r.support, ∀ gi ∈ G, ¬ m.degree (leadingTerm m gi) ≤ c := by
--   -- 1) **Existence** via the division algorithm
--   have hGset : ∀ gi ∈ (G : Set _), IsUnit (m.leadingCoeff gi) := fun _ hgi => hG_unit _ hgi
--   obtain ⟨gcomb, r, ⟨hre, hdeg, hnil⟩⟩ := m.div_set hGset f

--   -- 2) set `g := ∑ b in gcomb.support, gcomb b • (b : MvPolynomial)`
--   let g : MvPolynomial σ k := gcomb.sum (fun b coeff => coeff • (b : MvPolynomial σ k))
--   have hgI : g ∈ I := by
--     simp [g, Finsupp.sum]
--     have h_support_mem : ∀ b ∈ gcomb.support, (b : MvPolynomial σ k) ∈ I :=
--       fun b hb => hGB.2.1 b.2
--     exact Submodule.sum_smul_mem I gcomb h_support_mem
--   use r
--   constructor
--   · simp
--     constructor
--     · show ∃ g ∈ I, f = g + r -- g ∈ I because each `b ∈ G` lies in `I` and `I` is an ideal
--       use g
--       constructor
--       · show g ∈ I
--         exact hgI
--       · show f = g + r
--         simpa only [g] using hre
--     · -- no term of `r` is divisible by any `LT gᵢ`
--       show ∀ (c : σ →₀ ℕ), ¬coeff c r = 0 → ∀ gi ∈ G, ¬m.degree (leadingTerm m gi) ≤ c
--       intro c hc gi hgi
--       have : c ∈ r.support := (mem_support_iff.mpr hc)
--       have : ∀ b ∈ ↑G, ¬m.degree b ≤ c := by exact fun b a ↦ hnil c this b a
--       have : ¬m.degree gi ≤ c := by (expose_names; exact hnil c this_1 gi hgi)
--       have : m.degree gi = m.degree (leadingTerm m gi) := by exact Eq.symm (degree_leadingTerm gi)
--       (expose_names;
--         exact Eq.mpr_not (congrFun (congrArg LE.le (id (Eq.symm this))) c) (this_2 gi hgi))


--   · -- **uniqueness**
--     -- Suppose `r'` also works; then `f = g' + r'` and `r'` has no divisible LT–terms.
--     clear hdeg
--     rintro r' ⟨⟨g', hg'I, hre'⟩, hnil'⟩
--     by_contra hdiff
--     have hne: ¬(r - r' = 0) := by exact sub_ne_zero_of_ne fun a ↦ hdiff (id (Eq.symm a))
--     have hrg : r - r' = g' - g := by
--       rw [eq_sub_of_add_eq' (id (Eq.symm hre)), eq_sub_of_add_eq' (id (Eq.symm hre'))]
--       exact sub_sub_sub_cancel_left g g' f
--     have dI : r - r' ∈ I := by
--       rw [hrg]
--       exact (Submodule.sub_mem_iff_left I hgI).mpr hg'I
--     have hlt_in : leadingTerm m (r - r') ∈ initialIdeal m I := by
--       dsimp [initialIdeal]
--       apply Ideal.subset_span
--       exact ⟨r - r', dI, hne, rfl⟩
--     have hlm_in : monomial (m.degree (r - r')) 1 ∈ initialIdeal m I := by
--       -- have hC : IsUnit (m.leadingCoeff (r - r')) := by
--       --   exact (isUnit_leadingCoeff_iff_nonzero m (r - r')).mpr hne
--       have h₁ : (monomial (m.degree (r - r')) (1 : k)) = C (m.leadingCoeff (r - r'))⁻¹ * (leadingTerm m (r - r')):= by
--         simp only [leadingTerm, C_mul_monomial, inv_mul_cancel₀ (MonomialOrder.leadingCoeff_ne_zero_iff.mpr hne)]
--       -- have h₁: leadingTerm m (r - r') = (MvPolynomial.C (m.leadingCoeff (r - r'))) * (monomial (m.degree (r - r')) (1 : k)) := by
--       --   simp [leadingTerm, C_mul_monomial]
--       rw [initialIdeal]

--       have : leadingTerm m (r - r') ∈ initialIdeal m I
--         → C (m.leadingCoeff (r - r'))⁻¹ * (leadingTerm m (r - r')) ∈ initialIdeal m I := by exact fun a ↦ Ideal.mul_mem_left (initialIdeal m I) (C (m.leadingCoeff (r - r'))⁻¹) hlt_in
--       rw [initialIdeal] at *
--       have : C (m.leadingCoeff (r - r'))⁻¹ * leadingTerm m (r - r') ∈ Ideal.span {f | ∃ g ∈ I, g ≠ 0 ∧ leadingTerm m g = f} := by exact this hlt_in
--       rw [h₁]
--       exact this
--     -- extract an exponent α dividing `m.degree d`
--     have hmono : monomial (m.degree (r - r')) 1 ∈ monomialIdeal k ↑(Finset.image (fun g ↦ m.degree g) G) := by
--       simp only [IsGroebnerBasis.initialIdeal_eq_monomialIdeal hGB, Finset.coe_image, g] at hlm_in
--       simp only [Finset.coe_image, hlm_in, g]
--     have : ∃ α ∈ (Finset.image (fun g ↦ m.degree g) G), α ≤ m.degree (r - r') := by
--       apply mem_monomialIdeal_iff_divisible.mp hmono
--     obtain ⟨α, hα⟩ := this
--     rw [Finset.mem_image] at hα
--     obtain ⟨gα, ⟨hgα_in_G, hgαlm, rfl⟩⟩ := hα.1
--     have hin : m.degree (r - r') ∈ r.support ∪ r'.support := by
--       apply Finsupp.support_sub
--       exact MonomialOrder.degree_mem_support hne
--     simp only [Finset.mem_union] at hin
--     cases hin with
--     | inl h => sorry
--     | inr h =>
--       have : ¬m.degree (leadingTerm m gα) ≤ m.degree (r - r') := by apply hnil' _ h _ hgα_in_G
--       sorry


-- variable [DecidableEq (MvPolynomial σ k)] in
-- /--
-- **Proposition 1.**  If `G` is a Gröbner basis for `I`, then every `f` admits
-- a unique decomposition `f = g + r` with
--   1. `g ∈ I` and
--   2. no term of `r` is divisible by any `LT gₖ`.
-- -/
-- theorem remainder_exists_unique {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
--   (hGB : IsGroebnerBasis m I G)
--   (hG_unit : ∀ gi ∈ G, IsUnit (m.leadingCoeff gi)) (f : MvPolynomial σ k) :
--   ∃! r : MvPolynomial σ k,
--     (∃ g, g ∈ I ∧ f = g + r) ∧
--     ∀ c ∈ r.support, ∀ gi ∈ G, ¬ m.degree (leadingTerm m gi) ≤ c := by
--       -- 1) Existence via the division algorithm `MonomialOrder.div_set`
--     have hGset : ∀ gi ∈ (G.toSet), IsUnit (m.leadingCoeff gi) := by exact fun gi a ↦ hG_unit gi a
--     obtain ⟨gcomb, r, div_props⟩ := @MonomialOrder.div_set σ m k _ (G.toSet) (by simpa using hG_unit) f
--     use r
--     constructor
--     · simp
--       constructor
--       · use (Finsupp.linearCombination (MvPolynomial σ k) fun b ↦ ↑b) gcomb
--         constructor
--         · show (Finsupp.linearCombination (MvPolynomial σ k) fun b ↦ ↑b) gcomb ∈ I
--           sorry
--         · show f = (Finsupp.linearCombination (MvPolynomial σ k) fun b ↦ ↑b) gcomb + r
--           sorry
--       · show ∀ (c : σ →₀ ℕ), ¬coeff c r = 0 → ∀ gi ∈ G, ¬m.degree (leadingTerm m gi) ≤ c
--         sorry
--     · show ∀ (y : MvPolynomial σ k), (fun r ↦ (∃ g ∈ I, f = g + r) ∧ ∀ c ∈ r.support, ∀ gi ∈ G, ¬m.degree (leadingTerm m gi) ≤ c) y → y = r
--       sorry
