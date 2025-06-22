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
## Reference : [Becker-Weispfenning1993]

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
def Reduce (m : MonomialOrder σ)
  (P : Set (MvPolynomial σ R)) (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) :
  MvPolynomial σ R → MvPolynomial σ R → Prop
| f₁, f₀ => ∃ (p : MvPolynomial σ R) (hp : p ∈ P) (hpf₀ : m.degree p ≤ m.degree f₀) (hf₀_ne : f₀ ≠ 0) , f₁ = m.reduce (hP p hp) f₀

/-- If `f` is reduced to `g`, and `m.degree f = 0`, then `g` must be `0`. -/
lemma Reduce.target_is_zero_if_source_deg_is_zero
  {f g : MvPolynomial σ R}
  {P : Set (MvPolynomial σ R)} {hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)}
  (hgf : m.Reduce P hP g f) (hf_deg_eq_0 : m.degree f = 0) :
    g = 0 := by
    simp only [Reduce] at hgf
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
theorem Reduce.noetherian
  (P : Set (MvPolynomial σ R))
  (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) :
  IsAsymm _ (m.Reduce P hP) ∧ WellFounded (m.Reduce P hP) := by
  constructor
  · -- asymmetry:
    refine { asymm := ?_ }
    intro f g hfg hgf
    by_cases h_lmf_eq_zero : m.degree f = 0
    · -- m.degree f = 0
      have hg_zero : g = 0 := by exact Reduce.target_is_zero_if_source_deg_is_zero hgf h_lmf_eq_zero
      simp only [Reduce] at hfg
      rcases hfg with ⟨p, hpP, hpg, hg_ne, hf_eq_reduce_g⟩
      exact hg_ne hg_zero
    · -- m.degree f ≠ 0
      by_cases h_lmg_eq_zero : m.degree g = 0
      · -- m.degree f ≠ 0 ∧ m.degree g = 0
        have hg_zero : f = 0 := by exact Reduce.target_is_zero_if_source_deg_is_zero hfg h_lmg_eq_zero
        have : m.degree f = 0 := by rw [hg_zero, degree_zero]
        exact h_lmf_eq_zero this
      · -- m.degree f ≠ 0 ∧ m.degree g ≠ 0
        simp only [Reduce] at hfg
        rcases hfg with ⟨p, hpP, hpg, hg_ne, hf_eq_reduce_g⟩
        simp only [Reduce] at hgf
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
      simp only [Reduce] at h_step
      obtain ⟨p, ⟨hp_mem, ⟨hpf, ⟨hf, f_red⟩⟩⟩⟩ := h_step n
      have : m.degree (m.reduce (hP p hp_mem) (f_seq n)) ≺[m] m.degree (f_seq n) := by
        by_cases h_lmf_n_eq_zero : m.degree (f_seq n) = 0
        · have : f_seq (n + 1) = 0 := by exact
            Reduce.target_is_zero_if_source_deg_is_zero (h_step n) h_lmf_n_eq_zero
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
  ¬(∃ g, (Reduce m P hP) g f)

variable (m) in
def normalform_mod {P : Set (MvPolynomial σ R)}
  (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) (f₁ f₀ : MvPolynomial σ R) :=
  Isnormalform m hP f₁ ∧ Relation.ReflTransGen (Reduce m P hP) f₁ f₀

lemma normalform_mod_iff' {P : Set (MvPolynomial σ R)}
  (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p))
  (r f : MvPolynomial σ R)
  (hnorm : normalform_mod m hP r f) :
    ¬(∃ g, (Reduce m P hP) g r)
      ∧ Relation.ReflTransGen (Reduce m P hP) r f := by
    dsimp [Reduce, reduce]
    push_neg -- hP p hp
    simp only [ne_eq, imp_iff_not_or, not_not]

    sorry

lemma normalform_mod_iff'' {P : Set (MvPolynomial σ R)}
  (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p))
  (r f : MvPolynomial σ R)
  (hnorm : normalform_mod m hP r f) :
  (∀ (g p : MvPolynomial σ R) (hp : p ∈ P),
    ¬ m.degree p ≤ m.degree r ∨ r = 0 ∨ g ≠ r - (monomial (m.degree r - m.degree p)) ((hP p hp).unit⁻¹ * m.leadingCoeff r) * p)
      ∧ Relation.ReflTransGen (Reduce m P hP) r f := by
    dsimp [Reduce, reduce]
    push_neg -- hP p hp
    sorry

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
    -- `h : ¬∃ g, Reduce m P hP g r`
    intro h p hp
    by_contra h_contra
    push_neg at h_contra
    -- `h_contra` is `m.degree p ≤ m.degree r ∧ r ≠ 0`
    -- This is the condition for `r` to be reducible by `p`.
    -- So we can construct a `g` and a reduction proof.
    let g := m.reduce (hP p hp) r
    have h_reduc : ∃ g, Reduce m P hP g r :=
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
       Relation.ReflTransGen (m.Reduce P hP) r f) := by
  unfold normalform_mod
  rw [Isnormalform_iff]


-- variable (m) in
-- def normalform_rel (P : Set (MvPolynomial σ R)) -- Relation.reflTransGen_iff_eq
--   (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) (f g : MvPolynomial σ R) :=
--   @Relation.NormalFormof _ (Reduce m P hP) (Reduce.noetherian P hP).1 f g


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
      simp only [Reduce, ne_eq, not_true_eq_false, IsEmpty.exists_iff, degree_zero, nonpos_iff_eq_zero,
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
      --   simp only [Reduce, ne_eq, not_true_eq_false, IsEmpty.exists_iff, degree_zero,
      --     nonpos_iff_eq_zero, exists_false, exists_const, not_false_eq_true, true_and]
      --   refine (Relation.ReflTransGen.cases_tail_iff (m.Reduce B hB) 0 f).mpr ?_
      --   simp only [hf0, false_or]
      --   show ∃ b, b →*[m.Reduce B hB] 0 ∧ m.Reduce B hB b f
      --   use f - monomial (m.degree f - m.degree bi) ((hB bi hbi).unit⁻¹ * m.leadingCoeff f) * bi
      --   constructor
      --   · sorry
      --   · simp [Reduce, hf0]
      --     use bi
      --     simp only [hbi_deg0, zero_le, tsub_zero, true_and]
      --     use hbi
      --     apply degree_reduce_lt (hB bi hbi) f
      --     refine ⟨bi, hbi, degree_reduce_lt (hB bi hbi) f, rfl⟩


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

-- /-- Single‐step "top" reduction by any `p ∈ P`. -/
-- def Reduce_old (m : MonomialOrder σ)
--   (P : Set (MvPolynomial σ R)) (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) :
--   MvPolynomial σ R → MvPolynomial σ R → Prop
-- | g, f => ∃ (p : MvPolynomial σ R) (hp : p ∈ P) (hpf : m.degree p ≤ m.degree f) (hf : m.degree f ≠ 0) , g = m.reduce (hP p hp) f

-- /-- **Theorem 5.21.**  For any `P ⊆ K[X]`, the relation `→[P]` is a noetherian reduction. (top‐reduction case).-/
-- theorem Reduce_old.noetherian
--   (P : Set (MvPolynomial σ R))
--   (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) :
--   IsAsymm _ (m.Reduce_old P hP) ∧ WellFounded (m.Reduce_old P hP) := by
--   constructor
--   · -- asymmetry:
--     refine { asymm := ?_ }
--     intro f g hfg hgf
--     simp only [Reduce_old] at hfg
--     rcases hfg with ⟨p, hpP, hpg, hg_ne, hf_red_g⟩
--     simp only [Reduce_old] at hgf
--     rcases hgf with ⟨q, hqP, hqf, hf_ne, hg_red_f⟩

--     have d1 : (m.degree g) ≺[m] (m.degree f) := by
--       rw [hg_red_f]
--       exact degree_reduce_lt (hP q hqP) hqf hf_ne
--     have d2 : (m.degree f) ≺[m] (m.degree g) := by
--       rw [hf_red_g]
--       exact degree_reduce_lt (hP p hpP) hpg hg_ne
--     let cyc : m.degree f ≺[m] m.degree f := by
--       simpa using d2.trans d1
--     exact (lt_self_iff_false (m.toSyn (m.degree f))).mp cyc

--   · -- Well‐foundedness
--     apply WellFounded.wellFounded_iff_no_descending_seq.mpr
--     by_contra h
--     simp at h
--     obtain ⟨f_seq, h_step⟩ := h
--     let u_seq : ℕ → (σ →₀ ℕ) := fun n => m.degree (f_seq n)
--     have h_dec : ∀ n, u_seq (n+1) ≺[m] u_seq n := by
--       intro n
--       simp only [Reduce_old] at h_step
--       obtain ⟨p, ⟨hp_mem, ⟨hpf, ⟨hf, f_red⟩⟩⟩⟩ := h_step n
--       have : m.degree (m.reduce (hP p hp_mem) (f_seq n)) ≺[m] m.degree (f_seq n) := by
--         apply degree_reduce_lt (hP p hp_mem) hpf hf
--       simp only [f_red, gt_iff_lt, u_seq]
--       exact this
--     have m_wf : WellFounded (· ≺[m] ·) := by
--       have : WellFounded (· < ·) := (m.wf.wf)
--       exact WellFounded.onFun this
--     -- convert to the subtype of strictly‐descending sequences
--     let desc_sub : {u : ℕ → _ // ∀ n, (· ≺[m] ·) (u (n+1)) (u n)} :=
--       ⟨u_seq, h_dec⟩
--     have no_seq : IsEmpty { f : ℕ → (σ →₀ ℕ)// ∀ (n : ℕ), (· ≺[m] ·) (f (n + 1)) (f n) } := by
--       rw [WellFounded.wellFounded_iff_no_descending_seq] at m_wf
--       exact m_wf
--     exact no_seq.elim desc_sub

-- /--
-- A polynomial `r` is a normal form of `f` with respect to a set of polynomials `P`
-- if and only if `f` reduces to `r` in zero or more steps, and `r` is irreducible.
-- A polynomial `r` is irreducible if no polynomial `p` in `P` can top-reduce it.
-- This is equivalent to saying that for all `p` in `P`, either `r` is zero or the
-- degree of `p` is not less than or equal to the degree of `r`.
-- -/
-- lemma normalform_mod_iff_old {P : Set (MvPolynomial σ R)}
--     (hP : ∀ p ∈ P, IsUnit (m.leadingCoeff p)) (r f : MvPolynomial σ R) :
--     normalform_mod m hP r f ↔
--       ((∀ p ∈ P, ¬ m.degree p ≤ m.degree r ∨ r = 0) ∧
--        Relation.ReflTransGen (m.Reduce P hP) r f) := by
--   constructor
--   -- `normalform_mod → ...`
--   · intro h
--     unfold normalform_mod at h
--     constructor
--     · -- Prove the irreducibility condition
--       unfold Isnormalform at h
--       intro p hp
--       -- Proof by contradiction: assume `r` is reducible by `p`
--       by_contra h_contra
--       push_neg at h_contra
--       -- `h_contra` is `m.degree p ≤ m.degree r ∧ r ≠ 0`
--       -- This is exactly the condition for `r` to be reducible.
--       -- So we can find a `g` that `r` reduces to.
--       have h_reduc : ∃ g, Reduce m P hP g r :=
--         ⟨m.reduce (hP p hp) r, p, hp, h_contra.1, h_contra.2, rfl⟩
--       -- This contradicts that `r` is a normal form.
--       exact h.1 h_reduc
--     · -- The reduction path is part of the definition
--       exact h.2
--   -- `... → normalform_mod`
--   · intro h
--     constructor
--     · -- Prove `r` is a normal form
--       unfold Isnormalform
--       -- Assume for contradiction that `r` is reducible
--       rintro ⟨g, p, hp, hpr, hr0, rfl⟩
--       -- `h.1` gives `∀ p ∈ P, ¬ m.degree p ≤ m.degree r ∨ r = 0`
--       -- But we have `m.degree p ≤ m.degree r` and `r ≠ 0`
--       have := h.1 p hp
--       tauto
--     · -- The reduction path is given
--       exact h.2
