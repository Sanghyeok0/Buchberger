import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Noetherian.Defs
-- import Mathlib.RingTheory.Polynomial.Basic
-- import Mathlib.Algebra.Ring.Defs
import Buchberger.MonomialIdeal
import Buchberger.Order2

variable {σ : Type*} -- [DecidableEq σ]
variable {m : MonomialOrder σ}

open MonomialOrder MvPolynomial

namespace MonomialOrder

set_option maxHeartbeats 0

/-
## Reference : [Becker-Weispfenning1993] [Cox, Little, and O'Shea 1997]
Following [Becker–Weispfenning 1993], we intend to define a more general normal form.
To this end, we imported the Order2 file.

Trying to define normalform
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
  ∃ t, m.red_poly_step_by_term p f g hp t

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

variable (m) in
/--  The induced quasi‐order on multivariate polynomials: `f ≼ g` iff `T(f) ≤' T(g)`. -/
def MvPolynomial.maxOrder  :
  MvPolynomial σ R → MvPolynomial σ R → Prop
| f, g =>
  (f.support.map m.toSyn : Finset m.syn)
  ≤'
  (g.support.map m.toSyn : Finset m.syn)

notation:50 " ≼'[" m "] " => MvPolynomial.maxOrder m

/-- Single‐step "top" reduction by any `p ∈ P`. -/
def TopReduce (m : MonomialOrder σ)
  (P : Set (MvPolynomial σ R)) (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) :
  MvPolynomial σ R → MvPolynomial σ R → Prop
| f₁, f₀ => ∃ (p : MvPolynomial σ R) (hp : p ∈ P) (hpf₀ : m.degree p ≤ m.degree f₀) (hf₀_ne : f₀ ≠ 0) , f₁ = m.reduce (hP p hp) f₀

/-- If `f` is reduced to `g`, and `m.degree f = 0`, then `g` must be `0`. -/
lemma TopReduce.target_is_zero_if_source_deg_is_zero
  {f g : MvPolynomial σ R}
  {P : Set (MvPolynomial σ R)} {hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)}
  (hgf : m.TopReduce P hP g f) (hf_deg_eq_0 : m.degree f = 0) :
    g = 0 := by
    simp only [TopReduce] at hgf
    obtain ⟨p, hp_mem, hpf_le_df, hf_ne, hg_eq_reduce_f⟩ := hgf
    -- If `f ≠ 0` and `m.degree f = 0`, then `f = C (m.leadingCoeff f)`.
    have hf_eq_C_lc : f = C (m.leadingCoeff f) := m.eq_C_of_degree_eq_zero hf_deg_eq_0
    -- `m.leadingCoeff f ≠ 0` since `f ≠ 0`.
    have hf_lc_ne_0 : m.leadingCoeff f ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hf_ne
    -- `hpf_le_df : m.degree p ≤ m.degree f` becomes `m.degree p ≤ 0`, so `m.degree p = 0`.
    have hp_deg_eq_0 : m.degree p = 0 := by rw [hf_deg_eq_0] at hpf_le_df; exact nonpos_iff_eq_zero.mp hpf_le_df
    -- Since `m.degree p = 0`, `p` is a constant `C (m.leadingCoeff p)`.
    have hp_eq_C_lc : p = C (m.leadingCoeff p) := m.eq_C_of_degree_eq_zero hp_deg_eq_0
    -- Substitute into `hg_eq_reduce` and simplify
    rw [reduce, hf_eq_C_lc, hp_deg_eq_0, degree_C, tsub_self, monomial_zero'] at hg_eq_reduce_f
    nth_rw 2 [mul_comm] at hg_eq_reduce_f
    rw [C_mul, congrArg m.leadingCoeff (id (Eq.symm hf_eq_C_lc))] at hg_eq_reduce_f
    nth_rw 3 [hp_eq_C_lc] at hg_eq_reduce_f
    rw [←C_mul, ←C_mul, mul_assoc] at hg_eq_reduce_f
    rw [IsUnit.val_inv_mul, mul_one, sub_self] at hg_eq_reduce_f
    exact hg_eq_reduce_f

/-- **Theorem 5.21.**  For any `P ⊆ K[X]`, the relation `→[P]` is a noetherian reduction. (top‐reduction case).-/
theorem TopReduce.noetherian
  (P : Set (MvPolynomial σ R))
  (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) :
  IsAsymm _ (m.TopReduce P hP) ∧ WellFounded (m.TopReduce P hP) := by
  constructor
  · -- asymmetry:
    refine { asymm := ?_ }
    intro f g hfg hgf
    by_cases h_lmf_eq_zero : m.degree f = 0
    · -- m.degree f = 0
      have hg_zero : g = 0 := by exact TopReduce.target_is_zero_if_source_deg_is_zero hgf h_lmf_eq_zero
      simp only [TopReduce] at hfg
      rcases hfg with ⟨p, hpP, hpg, hg_ne, hf_eq_reduce_g⟩
      exact hg_ne hg_zero
    · -- m.degree f ≠ 0
      by_cases h_lmg_eq_zero : m.degree g = 0
      · -- m.degree f ≠ 0 ∧ m.degree g = 0
        have hg_zero : f = 0 := by exact TopReduce.target_is_zero_if_source_deg_is_zero hfg h_lmg_eq_zero
        have : m.degree f = 0 := by rw [hg_zero, degree_zero]
        exact h_lmf_eq_zero this
      · -- m.degree f ≠ 0 ∧ m.degree g ≠ 0
        simp only [TopReduce] at hfg
        rcases hfg with ⟨p, hpP, hpg, hg_ne, hf_eq_reduce_g⟩
        simp only [TopReduce] at hgf
        rcases hgf with ⟨q, hqP, hqf, hf_ne, hg_eq_reduce_f⟩
        have d1 : (m.degree g) ≺[m] (m.degree f) := by
          rw [hg_eq_reduce_f]
          exact degree_reduce_lt (hP q hqP) hqf h_lmf_eq_zero
        have d2 : (m.degree f) ≺[m] (m.degree g) := by
          rw [hf_eq_reduce_g]
          exact degree_reduce_lt (hP p hpP) hpg h_lmg_eq_zero
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
      simp only [TopReduce] at h_step
      obtain ⟨p, ⟨hp_mem, ⟨hpf, ⟨hf, f_red⟩⟩⟩⟩ := h_step n
      have : m.degree (m.reduce (hP p hp_mem) (f_seq n)) ≺[m] m.degree (f_seq n) := by
        by_cases h_lmf_n_eq_zero : m.degree (f_seq n) = 0
        · have : f_seq (n + 1) = 0 := by exact
            TopReduce.target_is_zero_if_source_deg_is_zero (h_step n) h_lmf_n_eq_zero
          obtain ⟨q, ⟨hq_mem, ⟨hqf, ⟨hf', f_red'⟩⟩⟩⟩ := h_step (n + 1)
          exact absurd this hf'
        · exact degree_reduce_lt (hP p hp_mem) hpf h_lmf_n_eq_zero
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
def Isnormalform {P : Set (MvPolynomial σ R)}
  (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) (f : MvPolynomial σ R) :=
  ¬(∃ g, (TopReduce m P hP) g f)

variable (m) in
def normalform_mod {P : Set (MvPolynomial σ R)}
  (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) (f₁ f₀ : MvPolynomial σ R) :=
  Isnormalform m hP f₁ ∧ Relation.ReflTransGen (TopReduce m P hP) f₁ f₀

/--
A polynomial `r` is a normal form with respect to a set `P`
if and only if it cannot be top-reduced by any polynomial in `P`. This is
equivalent to saying that for every `p ∈ P`, either `r` is zero or the degree
of `p` is not less than or equal to the degree of `r`.
-/
lemma Isnormalform_iff {P : Set (MvPolynomial σ R)}
    (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) (r : MvPolynomial σ R) :
    Isnormalform m hP r ↔ (∀ p ∈ P, ¬ m.degree p ≤ m.degree r ∨ r = 0) := by
  constructor
  · -- `Isnormalform → degree condition`
    unfold Isnormalform
    -- `h : ¬∃ g, TopReduce m P hP g r`
    intro h p hp
    by_contra h_contra
    push_neg at h_contra
    -- `h_contra` is `m.degree p ≤ m.degree r ∧ r ≠ 0`
    -- This is the condition for `r` to be reducible by `p`.
    -- So we can construct a `g` and a reduction proof.
    let g := m.reduce (hP p hp) r
    have h_reduc : ∃ g, TopReduce m P hP g r :=
      ⟨g, p, hp, h_contra.1, h_contra.2, rfl⟩
    -- This contradicts the assumption `h`.
    exact h h_reduc
  · -- `degree condition → Isnormalform`
    -- `h : ∀ p ∈ P, ¬ m.degree p ≤ m.degree r ∨ r = 0`
    intro h
    unfold Isnormalform
    -- Assume for contradiction that `r` is reducible
    rintro ⟨g, p, hp, hpr, hr0, rfl⟩
    -- `hpr` is `m.degree p ≤ m.degree r`
    -- `hr0` is `r ≠ 0`
    -- We can specialize our assumption `h` to this `p`.
    specialize h p hp
    -- `h` is now `¬ m.degree p ≤ m.degree r ∨ r = 0`
    -- This creates a contradiction with `hpr` and `hr0`.
    tauto

/--
A polynomial `r` is a normal form of `f` with respect to a set of polynomials `P`
if and only if `f` reduces to `r` in zero or more steps, and `r` is irreducible.
This lemma expresses this equivalence using the degree-based condition for irreducibility.
-/
lemma normalform_mod_iff {P : Set (MvPolynomial σ R)}
    (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) (r f : MvPolynomial σ R) :
    normalform_mod m hP r f ↔
      ((∀ p ∈ P, ¬ m.degree p ≤ m.degree r ∨ r = 0) ∧
       Relation.ReflTransGen (m.TopReduce P hP) r f) := by
  unfold normalform_mod
  rw [Isnormalform_iff]


-- variable (m) in
-- def normalform_rel (P : Set (MvPolynomial σ R)) -- Relation.reflTransGen_iff_eq
--   (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) (f g : MvPolynomial σ R) :=
--   @Relation.NormalFormof _ (TopReduce m P hP) (TopReduce.noetherian P hP).1 f g


/--
**Proposition 5.22 (Becker-Weispfenning).**
Let `P` be a subset of `k[X]` and `f ∈ k[X]`. Then there exists a normal form `g` of `f`
modulo `P` and a family `q` of polynomials such that:
1. `f = (∑ p ∈ P, q_p * p) + g`
2. The degree of each term in the sum is at most the degree of `f`.
-/
theorem div_set'
  {B : Set (MvPolynomial σ R)} (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
  (f : MvPolynomial σ R) :
  ∃ (g : B →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
    f = Finsupp.linearCombination _ (fun (p : B) ↦ (p : MvPolynomial σ R)) g
      + r
    ∧ (∀ (p : B), m.degree ((p : MvPolynomial σ R) * (g p)) ≼[m] m.degree f)
    ∧ Isnormalform m hB r := by
    -- --- Case 1: The polynomial `f` is zero. ---
      by_cases hf0 : f = 0
      -- If f is 0, the quotients and remainder are all 0.
      refine ⟨0, 0, by simp [hf0], ?_⟩
      simp only [Finsupp.coe_zero, Pi.ofNat_apply, mul_zero, degree_zero, map_zero, hf0, le_refl,
        implies_true, normalform_mod, true_and]
      simp only [Isnormalform, not_exists]
      intro x
      simp only [TopReduce, ne_eq, not_true_eq_false, IsEmpty.exists_iff, degree_zero, nonpos_iff_eq_zero,
        exists_false, exists_const, not_false_eq_true]
    -- --- Case 2: At least one divisor `bi` is a constant (degree 0). ---
    -- This is a special, non-recursive case that terminates the algorithm.
      by_cases hb' : ∃ bi ∈ B, m.degree (bi) = 0
      obtain ⟨bi, hbi, hbi_deg0⟩ := hb'
      use Finsupp.single (⟨bi, hbi⟩ : B) ((hB bi hbi).unit⁻¹ • f), 0
      constructor
      · -- Prove the division equation: f = q_bi * bi + 0
        simp only [Finsupp.linearCombination_single, smul_eq_mul, add_zero]
        simp only [smul_mul_assoc, ← smul_eq_iff_eq_inv_smul, Units.smul_isUnit]
        nth_rewrite 2 [eq_C_of_degree_eq_zero hbi_deg0]
        rw [mul_comm, smul_eq_C_mul]
      · constructor
        · -- Prove the degree condition.
          intro bj
          by_cases hj : bj = (⟨bi, hbi⟩ : B)
          · apply le_trans degree_mul_le
            simp only [hj, hbi_deg0, Finsupp.single_eq_same, zero_add]
            apply le_of_eq
            simp only [EmbeddingLike.apply_eq_iff_eq]
            apply degree_smul (Units.isRegular _)
          · simp only [Finsupp.single_eq_of_ne (Ne.symm hj), mul_zero, degree_zero, map_zero]
            apply bot_le
        · -- Prove the `normalform_mod` property.
          show m.Isnormalform hB 0
          refine (Isnormalform_iff hB 0).mpr ?_
          intro p hp; right; rfl
    -- --- Case 3: `f` is top-reducible by some `bi` in `B`. ---
      by_cases hf : ∃ bi ∈ B, m.degree bi ≤ m.degree f
      push_neg at hb'
      · obtain ⟨bi, hbi ,hbif⟩ := hf
        -- First, we prove that the reduction step strictly decreases the degree of `f`.
        have deg_reduce : m.degree (m.reduce (hB bi hbi) f) ≺[m] m.degree f := by
          apply degree_reduce_lt (hB bi hbi) hbif
          intro hf0'
          apply hb' bi hbi
          simpa [hf0'] using hbif
        -- Then, we apply the induction hypothesis (recursive call) to the reduced polynomial.
        obtain ⟨g', r', H'⟩ := div_set' hB ((m.reduce (hB bi hbi) f))
        use g' +
          Finsupp.single (⟨bi, hbi⟩ : B) (monomial (m.degree f - m.degree (bi)) ((hB bi hbi).unit⁻¹ * m.leadingCoeff f))
        use r'
        constructor
        · rw [map_add, add_assoc, add_comm _ r', ← add_assoc, ← H'.1]
          simp [reduce]
        constructor
        · -- Prove the degree condition holds for the new quotients.
          rintro j
          simp only [Finsupp.coe_add, Pi.add_apply]
          rw [mul_add]
          apply le_trans degree_add_le
          simp only [sup_le_iff]
          constructor
          · exact le_trans (H'.2.1 _) (le_of_lt deg_reduce)
          · classical
            rw [Finsupp.single_apply]
            split_ifs with hc
            · apply le_trans degree_mul_le
              simp only [map_add]
              apply le_of_le_of_eq (add_le_add_left (degree_monomial_le _) _)
              simp only [← hc]
              rw [← map_add, m.toSyn.injective.eq_iff]
              rw [add_tsub_cancel_of_le]
              exact hbif
            · simp only [mul_zero, degree_zero, map_zero]
              exact bot_le
        · -- Prove the `normalform_mod` property.
          show m.Isnormalform hB r'
          rw [Isnormalform_iff]
          exact ((m.Isnormalform_iff hB r')).mp H'.2.2
    -- --- Case 4: The leading term of `f` is not reducible by any `bi` in `B`. ---
    -- Here, we can't perform a top-reduction. We "peel off" the leading term,
    -- treat it as part of the remainder, and recurse on the rest (`f - LT(f)`).
      · push_neg at hf
        -- -- Case 4: leading term not reducible by any `bi ∈ B`.
        -- -- Decompose `f` into its sub‐leading‐term plus leading term.
        -- have : f = m.subLTerm f + leadingTerm m f := by
        --   rw [subLTerm, add_comm, ←leadingTerm, add_sub_cancel]
        -- -- Apply induction to `m.subLTerm f`.
        -- obtain ⟨g', r', ⟨h_div, h_deg_bound, h_norm⟩⟩ := div_set' hB (m.subLTerm f)
        -- -- Build the new quotient‐map and remainder.
        -- let g := g'
        -- let r := r' + leadingTerm m f
        -- use g, r
        -- constructor
        -- · -- f = (∑ g p • p) + r
        --   calc
        --     f
        --       = m.subLTerm f + leadingTerm m f       := by rw [subLTerm, add_comm, ←leadingTerm, add_sub_cancel]
        --     _ = Finsupp.linearCombination (MvPolynomial σ R) (fun (p : B) ↦ (p : MvPolynomial σ R)) g' + r' + m.leadingTerm f := by rw [h_div]
        --     _ = Finsupp.linearCombination (MvPolynomial σ R) (fun (p : B) ↦ (p : MvPolynomial σ R)) g' + r := by rw [add_assoc]


        -- constructor
        -- · -- ∀ p, degree (p * g p) ≤ degree f
        --   intro p hp
        --   calc
        --     m.degree (p * g p)
        --         = m.degree (p * g' p)              := rfl
        --     _ ≤ m.degree (m.subLTerm f)            := h_deg_bound p
        --     _ ≤ m.degree f                         := degree_sub_LTerm_le (m := m) f

        -- · -- Isnormalform r
        --   apply (Isnormalform_iff hB r).mpr
        --   intro p hp
        --   -- show ¬ m.degree p ≤ m.degree r
        --   have : m.degree r = m.degree f := by
        --     -- `r = r' + leadingTerm f` and `degree_sub_LTerm_lt` give the max is `m.degree f`
        --     rw [degree_add_of_lt (degree_sub_LTerm_lt (m := m) f) (degree_leadingTerm f).symm]
        --   -- but `hf` says `m.degree p ≤ m.degree f` is false
        --   exact (hf p hp).resolve_left (by rw [←this])
        ------------------------------------------------------
        suffices ∃ (g' : B →₀ MvPolynomial σ R), ∃ r',
            (m.subLTerm f = Finsupp.linearCombination (MvPolynomial σ R) (fun (p : B) ↦ (p : MvPolynomial σ R)) g' + r') ∧
            (∀ bi : B, m.degree ((bi : MvPolynomial σ R) * (g' bi)) ≼[m] m.degree (m.subLTerm f)) ∧
            (m.Isnormalform hB r') by
          obtain ⟨g', r', H'⟩ := this
          use g', r' +  monomial (m.degree f) (m.leadingCoeff f)
          constructor
          · simp [← add_assoc, ← H'.1, subLTerm]
          constructor
          · exact fun b ↦ le_trans (H'.2.1 b) (degree_sub_LTerm_le f)
          · show m.Isnormalform hB (r' + (monomial (m.degree f)) (m.leadingCoeff f))
            rw [Isnormalform_iff]
            intro p hpB
            left
            have : ∀ p ∈ B, ¬m.degree p ≤ m.degree r' ∨ r' = 0 := by exact (Isnormalform_iff hB r').mp H'.2.2
            -- Step 1: Establish the degree of the sum `r' + LTf`.
            by_cases hf'0 : m.subLTerm f = 0
            sorry
            have h_deg_sum : m.degree (r' + monomial (m.degree f) (m.leadingCoeff f)) = m.degree f := by
              calc
                m.degree (r' + (monomial (m.degree f)) (m.leadingCoeff f))
                = m.degree (monomial (m.degree f) (m.leadingCoeff f)) := by
                  rw [add_comm]; apply degree_add_of_lt
                  have : Decidable (m.leadingCoeff f = 0) := by exact Classical.propDecidable (m.leadingCoeff f = 0)
                  rw [degree_monomial]
                  by_cases h0 : m.leadingCoeff f = 0
                  · simp [h0]; sorry
                  · simp [h0]; sorry
                _ = m.degree f := by rw [←leadingTerm]; exact degree_leadingTerm f
            have h_deg_lt : m.degree r' ≺[m] m.degree f := by
              sorry

            have h_deg_sum1 : m.degree (monomial (m.degree f) (m.leadingCoeff f) + r') = m.degree (monomial (m.degree f) (m.leadingCoeff f)) := by
              apply degree_add_of_lt
              sorry
            have h_deg_sum2 : m.degree (r' + monomial (m.degree f) (m.leadingCoeff f)) = m.degree f := by sorry
            exact Eq.mpr_not (congrArg (LE.le (m.degree p)) h_deg_sum2) (hf p hpB)

        by_cases hf'0 : m.subLTerm f = 0
        · refine ⟨0, 0, by simp [hf'0], ?_⟩
          constructor
          · intro bi
            simp only [Finsupp.coe_zero, Pi.zero_apply, mul_zero, degree_zero, map_zero]
            exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a ↦ a) rfl (m.toSyn (m.degree (m.subLTerm f)))
          · show m.Isnormalform hB 0
            refine (Isnormalform_iff hB 0).mpr ?_
            exact fun p a ↦ Decidable.not_or_of_imp (congrFun rfl)
        · exact (div_set' hB) (m.subLTerm f)
termination_by WellFounded.wrap
((isWellFounded_iff m.syn fun x x_1 ↦ x < x_1).mp m.wf) (m.toSyn (m.degree f))
decreasing_by
· exact deg_reduce
· apply degree_sub_LTerm_lt
  intro hf0
  apply hf'0
  simp only [subLTerm, sub_eq_zero]
  nth_rewrite 1 [eq_C_of_degree_eq_zero hf0, hf0]
  simp
-- normalform_mod m hB r f is WROMG!
      -- by_cases hb' : ∃ bi ∈ B, m.degree (bi) = 0
      -- obtain ⟨bi, hbi, hbi_deg0⟩ := hb'
      -- use Finsupp.single (⟨bi, hbi⟩ : B) ((hB bi hbi).unit⁻¹ • f), 0
      -- constructor
      -- · simp only [Finsupp.linearCombination_single, smul_eq_mul, add_zero]
      --   simp only [smul_mul_assoc, ← smul_eq_iff_eq_inv_smul, Units.smul_isUnit]
      --   nth_rewrite 2 [eq_C_of_degree_eq_zero hbi_deg0]
      --   rw [mul_comm, smul_eq_C_mul]
      -- constructor
      -- · intro bj
      --   by_cases hj : bj = (⟨bi, hbi⟩ : B)
      --   · apply le_trans degree_mul_le
      --     simp only [hj, hbi_deg0, Finsupp.single_eq_same, zero_add]
      --     apply le_of_eq
      --     simp only [EmbeddingLike.apply_eq_iff_eq]
      --     apply degree_smul (Units.isRegular _)
      --   · simp only [Finsupp.single_eq_of_ne (Ne.symm hj), mul_zero, degree_zero, map_zero]
      --     apply bot_le
      -- · rw [normalform_mod, Isnormalform]
      --   simp only [TopReduce, ne_eq, not_true_eq_false, IsEmpty.exists_iff, degree_zero,
      --     nonpos_iff_eq_zero, exists_false, exists_const, not_false_eq_true, true_and]
      --   refine (Relation.ReflTransGen.cases_tail_iff (m.TopReduce B hB) 0 f).mpr ?_
      --   simp only [hf0, false_or]
      --   show ∃ b, b →*[m.TopReduce B hB] 0 ∧ m.TopReduce B hB b f
      --   use f - monomial (m.degree f - m.degree bi) ((hB bi hbi).unit⁻¹ * m.leadingCoeff f) * bi
      --   constructor
      --   · sorry
      --   · simp [TopReduce, hf0]
      --     use bi
      --     simp only [hbi_deg0, zero_le, tsub_zero, true_and]
      --     use hbi
      --     apply degree_reduce_lt (hB bi hbi) f
      --     refine ⟨bi, hbi, degree_reduce_lt (hB bi hbi) f, rfl⟩

end CommRing
end MonomialOrder

namespace MvPolynomial
section Field

variable {k : Type*} [Field k] [DecidableEq k]

variable (m) [DecidableEq σ] in
/-- Definition 5. Groebner_basis
A finite subset G of an ideal I is called a Gröbner basis (or standard basis)
if the ideal generated by the leading terms of the elements of G
equals the leading term ideal of I.
We adopt the convention that ⟨∅⟩ = {0}, so that the empty set is the
Gröbner basis of the zero ideal.
-/
def IsGroebnerBasis' (I : Ideal (MvPolynomial σ k)) (G : Finset (MvPolynomial σ k)) : Prop :=
  (∀ g ∈ G, g ≠ 0) ∧ G.toSet ⊆ I ∧ Ideal.span (G.image fun g => leadingTerm m g) = initialIdeal m I

variable [DecidableEq σ] in
lemma IsGroebnerBasis.initialIdeal_eq_monomialIdeal'
  {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
  (hGB : IsGroebnerBasis' m I G) :
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

variable [DecidableEq σ] in
/--
**§6 Corollary 2**
Let $G = \{g_1,\dots,g_t\}$ be a Gröbner basis for an ideal $I \subseteq k[x_1,\dots,x_n]$ and let $f \in k[x_1,\dots,x_n]$.
Then $f \in I$ if and only if the remainder on division of $f$ by $G$ is zero.
-/
theorem mem_Ideal_iff_GB_normalForm_eq_zero'
  {I : Ideal (MvPolynomial σ k)} {G : Finset (MvPolynomial σ k)}
  (hGB : IsGroebnerBasis' m I G)
  (f : MvPolynomial σ k) :
  f ∈ I ↔ normalform_mod m (fun g hg =>
    (isUnit_leadingCoeff_iff_nonzero m g).mpr (hGB.1 g hg)) 0 f := by sorry
