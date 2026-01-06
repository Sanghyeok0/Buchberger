import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import SNU.Cox.Cox_Chapter4_Ex.Cox_Chapter4_Section4_Exercise5

namespace MvPolynomial

variable {σ k : Type*} [Fintype σ] [Field k]

open Ideal

-- Saturation 정의 (이전과 동일)
noncomputable def saturation (I J : Ideal (MvPolynomial σ k)) : Ideal (MvPolynomial σ k) :=
  ⨆ n : ℕ, I.colon (J ^ n)


omit [Fintype σ] in
/-- Proposition 9(i), first half: `I ≤ I : J`. -/
theorem le_colon (I J : Ideal (MvPolynomial σ k)) :
    I ≤ I.colon J := by
  intro f hf
  rw [Submodule.mem_colon]
  intro g _
  exact I.mul_mem_right g hf

omit [Fintype σ] in
/-- Proposition 9(i), second half: `I : J ≤ I : J^∞`. -/
theorem colon_le_saturation (I J : Ideal (MvPolynomial σ k)) :
    I.colon J ≤ saturation I J := by
  -- n=1 일 때가 I : J 이므로 Supremum 성질에 의해 성립
  rw [saturation]
  convert le_iSup (fun n ↦ I.colon (J ^ n)) 1
  simp only [pow_one]

omit [Fintype σ] in
/-- Often convenient: `I ≤ I : J^∞`. -/
theorem le_saturation (I J : Ideal (MvPolynomial σ k)) :
    I ≤ saturation I J :=
  (le_colon I J).trans (colon_le_saturation I J)

/--
Proposition 9(ii) (stabilization of the chain):
`∃ N, ∀ n ≥ N, I : J^n = I : J^N`.
-/
theorem colonPow_stabilizes (I J : Ideal (MvPolynomial σ k)) :
    ∃ N : ℕ, ∀ n ≥ N, I.colon (J ^ n) = I.colon (J ^ N) := by
  let chain : ℕ →o Ideal (MvPolynomial σ k) := {
    toFun := fun n ↦ I.colon (J ^ n)
    monotone' := by
      intro n m hnm
      -- n ≤ m ⇒ J^m ⊆ J^n
      have h_pow_le : J ^ m ≤ J ^ n := Ideal.pow_le_pow_right hnm
      apply Submodule.colon_mono le_rfl h_pow_le
  }
  obtain ⟨N, h_stab⟩ := (monotone_stabilizes_iff_noetherian.mpr isNoetherianRing) chain

  use N
  intro n hn
  exact (h_stab n hn).symm

/--
Proposition 9(ii) (as an equality of ideals):
`I : J^∞ = I : J^N` for some `N`.
-/
theorem saturation_eq_colon_pow (I J : Ideal (MvPolynomial σ k)) :
    ∃ N : ℕ, saturation I J = I.colon (J ^ N) := by
  obtain ⟨N, h_stab⟩ := colonPow_stabilizes I J
  use N
  apply le_antisymm
  · -- (⊆) ⨆ (I:J^n) ⊆ I:J^N
    apply iSup_le
    intro n
    by_cases h : n ≤ N
    · -- If n ≤ N then I:J^n ⊆ I:J^N
      intro f hf
      have h_pow : J ^ N ≤ J ^ n := Ideal.pow_le_pow_right h
      exact Submodule.colon_mono le_rfl h_pow hf
    · -- If n > N then I:J^n = I:J^N
      rw [h_stab n (le_of_not_ge h)]
  · -- (⊇) I:J^N ⊆ ⨆ (I:J^n)
    exact le_iSup (fun n ↦ I.colon (J ^ n)) N

/--
Proposition 9(iii): `√(I : J^∞) = (√I : J)`.
Here `saturation I J := ⨆ n, I.colon (J^n)`.
-/
theorem radical_saturation_eq_radical_colon_WIP
  (I J : Ideal (MvPolynomial σ k)) :
  (saturation I J).radical = I.radical.colon J := by
  apply le_antisymm
  · -- (⊆) √(I:J^∞) ⊆ √I:J
    intro f hf
    obtain ⟨m, hfm⟩ := Ideal.mem_radical_iff.mp hf
    obtain ⟨N, h_sat_eq⟩ := saturation_eq_colon_pow I J
    rw [h_sat_eq] at hfm

    -- 모든 g ∈ J에 대해 fg ∈ √I 임을 보임
    have h_fg_in_radical : ∀ g ∈ J, f * g ∈ I.radical := by
      intro g hg
      apply Ideal.mem_radical_iff.mpr
      use m + N
      rw [mul_pow]
      have h_split : f ^ (m + N) * g ^ (m + N) = (f ^ N * g ^ m) * (f ^ m * g ^ N) := by ring
      rw [h_split]
      apply Ideal.mul_mem_left
      exact (Submodule.mem_colon.mp hfm) (g ^ N) (Ideal.pow_mem_pow hg N)
    exact Submodule.mem_colon'.mpr h_fg_in_radical

  · -- (⊇) √I : J ⊆ √(saturation I J)
    intro f hf
    -- 목표: ∃ M, f^M ∈ saturation I J
    -- 1) J의 finite generator를 잡는다
    by_cases hJ_bot : J = ⊥
    · rw [hJ_bot]
      have : saturation I ⊥ = ⊤ := by
        apply eq_top_iff.mpr
        refine le_trans ?_ (le_iSup (fun n ↦ I.colon (⊥ ^ n)) 1)
        rw [pow_one]
        simp only [top_le_iff]
        rw [eq_top_iff]
        intro x _
        rw [Submodule.mem_colon]
        intro y hy
        have hy0 : y = 0 := by rw [Submodule.mem_bot] at hy; exact hy
        rw [hy0]
        simp only [smul_eq_mul, mul_zero, zero_mem]
      rw [this, Ideal.radical_top]
      exact Submodule.mem_top
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian J
    have hs_nonempty : s.Nonempty := by
      contrapose! hJ_bot
      simp only [Finset.not_nonempty_iff_eq_empty] at hJ_bot
      simp only [hJ_bot, Finset.coe_empty, submodule_span_eq, span_empty] at hs
      exact hs.symm
    -- 2) colon membership을 generator에 적용: f*g ∈ √I
    have hmul_radical : ∀ g ∈ s, f * g ∈ I.radical := by
      intro g hg
      -- hf : f ∈ I.radical.colon J  ↔  ∀ g∈J, f*g ∈ I.radical
      have hf' : ∀ g ∈ J, f * g ∈ I.radical := by
        -- colon의 mem lemma는 Submodule.mem_colon 형태
        -- (Ideal은 Submodule)
        exact (Submodule.mem_colon.mp hf)
      have hgJ : g ∈ J := by
        -- g ∈ span(s) = J
        -- Ideal.subset_span : (g ∈ s) → g ∈ Ideal.span (s:Set R)
        -- hg : g ∈ s 이므로
        have : g ∈ Ideal.span (s : Set (MvPolynomial σ k)) := by
          exact Ideal.subset_span (by simpa using hg)
        simpa only [← hs, submodule_span_eq]
      simpa [mul_assoc] using hf' g hgJ

    -- 3) 각 generator에 대해 (f*g)^m ∈ I 인 m을 택하고, 최대값 M을 잡는다
    classical
    let mOf : s → ℕ := fun g =>
      Classical.choose (Ideal.mem_radical_iff.mp (hmul_radical g g.property))
    let M : ℕ := s.attach.sup mOf

    have hpowI : ∀ g ∈ s, (f * g) ^ M ∈ I := by
      intro g hg
      have hle : mOf ⟨g, hg⟩ ≤ M := by
        -- Finset.sup의 upper bound
        apply Finset.le_sup
        exact Finset.mem_attach s ⟨g, hg⟩
      have hbase : (f * g) ^ (mOf ⟨g, hg⟩) ∈ I := by
        exact (Classical.choose_spec (Ideal.mem_radical_iff.mp (hmul_radical g hg)))
      have : (f * g) ^ M = (f * g) ^ (mOf ⟨g, hg⟩) * (f * g) ^ (M - mOf ⟨g, hg⟩) := by
        -- M = m + (M-m) 형태
        have : M = mOf ⟨g, hg⟩ + (M - mOf ⟨g, hg⟩) := (Nat.add_sub_of_le hle).symm
        exact Eq.symm (pow_mul_pow_sub (f * g) hle)
      -- (f*g)^M = (f*g)^m * (f*g)^(...) 이므로 ∈ I
      simpa [this, mul_assoc] using I.mul_mem_right _ hbase

    -- 4) 이제 generator마다 f^M * g^M ∈ I 를 얻는다
    have hfgM : ∀ g ∈ s, f ^ M * g ^ M ∈ I := by
      intro g hg
      -- (f*g)^M = f^M * g^M
      have : (f * g) ^ M = f ^ M * g ^ M := by
        rw [mul_pow]
      simpa [this] using hpowI g hg

    -- 5) J^(s.card*M) ≤ span{g^M | g∈s}
    have hJpow_le :
        J ^ (s.card * M) ≤ Ideal.span ((fun g : MvPolynomial σ k => g ^ M) '' (s : Set (MvPolynomial σ k))) := by
      rw [←hs]
      apply span_pow_card_mul_le_span_image_pow _ hs_nonempty

-- 6) f^M ∈ I : J^(s.card*M) 을 보이고, 따라서 f ∈ radical(saturation I J)
    have hfM_in_colon : f ^ M ∈ I.colon (J ^ (s.card * M)) := by
      refine Submodule.mem_colon.mpr ?_
      intro h hh
      -- h ∈ J^(s.card*M) implies h ∈ span {g^M}
      have hh_in_span : h ∈ Ideal.span ((fun g => g ^ M) '' s) := hJpow_le hh

      let gen_set := (fun g : MvPolynomial σ k => g ^ M) '' s
      change h ∈ Ideal.span gen_set at hh_in_span
      apply Submodule.span_induction (p := fun x _ => f ^ M * x ∈ I) (hx := hh_in_span)

      · -- 1. Base case: x ∈ gen_set (생성원)
        intro x hx_gen
        obtain ⟨g, hg_s, rfl⟩ := (Set.mem_image _ _ _).mp hx_gen
        exact hfgM g hg_s

      · -- 2. Zero case
        rw [mul_zero]
        exact I.zero_mem

      · -- 3. Add case
        intro x y hx_span hy_span hx_mem hy_mem
        rw [mul_add]
        exact I.add_mem hx_mem hy_mem

      · -- 4. Smul case
        intro r x hx_span hx_mem
        rw [mul_smul_comm]
        exact I.mul_mem_left r hx_mem

    have hfM_in_saturation : f ^ M ∈ saturation I J := by
      -- le_iSup (fun n => I.colon (J^n)) (s.card*M)
      exact (le_iSup (fun n : ℕ => I.colon (J ^ n)) (s.card * M)) hfM_in_colon

    -- 마지막: f ∈ radical(saturation I J)
    exact Ideal.mem_radical_iff.mpr ⟨M, hfM_in_saturation⟩

end MvPolynomial
