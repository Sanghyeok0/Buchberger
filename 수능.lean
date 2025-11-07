import Mathlib

set_option maxHeartbeats 0

open Set Real Filter Topology Polynomial BigOperators Finset

namespace Polynomial

variable {R : Type*} [Ring R]

variable [Nontrivial R] in
/-- `(-X)`의 차수는 1. -/
@[simp] lemma natDegree_neg_X : ((-X : R[X]).natDegree) = 1 := by
  -- `natDegree_neg`와 `natDegree_X`로 한 줄
  simp only [natDegree_neg]
  exact natDegree_X

variable [Nontrivial R] in
/-- 합성 `p ∘ (-X)`는 natDegree를 보존한다. -/
@[simp] lemma natDegree_comp_neg_X [NoZeroDivisors R] (p : R[X]) :
  (p.comp (-X)).natDegree = p.natDegree := by
  -- `natDegree_comp` + `natDegree_neg_X`
  simpa [natDegree_neg_X, Nat.mul_one] using
    (Polynomial.natDegree_comp (p := p) (q := (-X : R[X])))

variable [Nontrivial R] in
/-- `0 < natDegree p` 이면 `0 < degree (p ∘ (-X))`. -/
lemma degree_pos_comp_neg_X_of_natDegree_pos [NoZeroDivisors R] {p : R[X]}
  (hp : 0 < p.natDegree) : 0 < (p.comp (-X)).degree := by
  have : 0 < (p.comp (-X)).natDegree := by
    simpa [natDegree_comp_neg_X (p := p)] using hp
  exact (natDegree_pos_iff_degree_pos).1 this

/-- `p.comp (-X)`의 최고차항: `(-1)^n * lc(p)`. (mathlib: `comp_neg_X_leadingCoeff_eq`) -/
@[simp] lemma leadingCoeff_comp_neg_X (p : R[X]) :
  (p.comp (-X)).leadingCoeff = (-1 : R) ^ p.natDegree * p.leadingCoeff := by
  simp only [comp_neg_X_leadingCoeff_eq]

/-- `natDegree p`가 홀수이면 `p.comp (-X)`의 lc는 `- lc(p)`. -/
@[simp] lemma leadingCoeff_comp_neg_X_of_odd {p : R[X]} (hodd : Odd p.natDegree) :
  (p.comp (-X)).leadingCoeff = - p.leadingCoeff := by
  simp only [comp_neg_X_leadingCoeff_eq, hodd.neg_one_pow, neg_mul, one_mul]

end Polynomial


namespace Polynomial
variable {R : Type*} [Ring R] [LinearOrder R] [AddLeftMono R]

lemma leadingCoeff_comp_neg_X_nonpos_of_pos {p : R[X]}
    (hodd : Odd p.natDegree) (hpos : 0 < p.leadingCoeff) :
    (p.comp (-X)).leadingCoeff ≤ 0 := by
  -- lc(q) = - lc(p)
  have h := leadingCoeff_comp_neg_X_of_odd (p := p) hodd
  -- -a ≤ 0  ↔  0 ≤ a
  simpa [h] using (neg_nonpos.mpr (le_of_lt hpos))

lemma leadingCoeff_comp_neg_X_nonneg_of_neg {p : R[X]}
    (hodd : Odd p.natDegree) (hneg : p.leadingCoeff < 0) :
    0 ≤ (p.comp (-X)).leadingCoeff := by
  have h := leadingCoeff_comp_neg_X_of_odd (p := p) hodd
  -- 0 ≤ -a  ↔  a ≤ 0
  simpa [h] using (neg_nonneg.mpr (le_of_lt hneg))

lemma leadingCoeff_comp_neg_X_neg_of_pos {p : R[X]}
    (hodd : Odd p.natDegree) (hpos : 0 < p.leadingCoeff) :
    (p.comp (-X)).leadingCoeff < 0 := by
  have h := leadingCoeff_comp_neg_X_of_odd (p := p) hodd
  -- -a < 0  ↔  0 < a
  simpa [h, neg_lt_zero] using hpos

lemma leadingCoeff_comp_neg_X_pos_of_neg {p : R[X]}
    (hodd : Odd p.natDegree) (hneg : p.leadingCoeff < 0) :
    0 < (p.comp (-X)).leadingCoeff := by
  have h := leadingCoeff_comp_neg_X_of_odd (p := p) hodd
  -- 0 < -a  ↔  a < 0
  simpa [h, neg_pos] using hneg
end Polynomial


/-- `atBot`에서의 수렴은 `x ↦ -x`를 합성하면 `atTop`에서의 수렴과 동치이다. -/
@[simp]
lemma tendsto_atBot_iff_tendsto_atTop_comp_neg
  {α : Type*} [TopologicalSpace α]
  {f : ℝ → α} {l : Filter α} :
  Tendsto f atBot l ↔ Tendsto (fun x => f (-x)) atTop l := by
  constructor
  · -- Forward direction: (f(x) → l as x → -∞) ⇒ (f(-x) → l as x → +∞)
    intro h
    -- We know `Tendsto (fun y ↦ -y) atTop atBot`.
    -- By composing `h: Tendsto f atBot l` with this, we get the desired result.
    exact h.comp tendsto_neg_atTop_atBot
  · -- Backward direction: (f(-x) → l as x → +∞) ⇒ (f(x) → l as x → -∞)
    intro h
    -- We know `Tendsto (fun y ↦ -y) atBot atTop`.
    -- Composing `h: Tendsto (fun x ↦ f (-x)) atTop l` with this gives us:
    -- `Tendsto (fun y ↦ (fun x ↦ f (-x)) (-y)) atBot l`, which is `Tendsto (fun y ↦ f (-(-y))) atBot l`.
    have h' : Tendsto (fun x : ℝ => f (-(-x))) atBot l :=
      h.comp tendsto_neg_atBot_atTop
    -- The `simpa` tactic simplifies the hypothesis `h''` using `neg_neg`
    -- and then uses it to prove the goal.
    exact (by simpa [neg_neg] using h')

/-- 반대 방향 버전: `atTop`에서의 수렴과 `x ↦ -x` 합성 후 `atBot`에서의 수렴의 동치. -/
@[simp]
lemma tendsto_atTop_iff_tendsto_atBot_comp_neg
  {α : Type*} [TopologicalSpace α]
  {f : ℝ → α} {l : Filter α} :
  Tendsto f atTop l ↔ Tendsto (fun x => f (-x)) atBot l := by
  constructor
  · -- Forward: (f(x) → l as x → +∞) ⇒ (f(-x) → l as x → -∞)
    intro h
    -- atBot --(x↦-x)--> atTop --f--> l
    exact h.comp tendsto_neg_atBot_atTop
  · -- Backward: (f(-x) → l as x → -∞) ⇒ (f(x) → l as x → +∞)
    intro h
    -- atTop --(x↦-x)--> atBot --(y↦f(-y))--> l
    have h' : Tendsto (fun x : ℝ => f (-(-x))) atTop l :=
      h.comp tendsto_neg_atTop_atBot
    -- f(-(-x)) = f x
    simpa [neg_neg] using h'


/-- 특수화: `atBot → atBot` 수렴 ↔ `x ↦ -x` 합성 후 `atTop → atBot` 수렴 -/
@[simp]
lemma tendsto_atBot_atBot_iff {α : Type*} [TopologicalSpace α] [Preorder α]
  {f : ℝ → α} :
  Tendsto f atBot atBot ↔ Tendsto (fun x => f (-x)) atTop atBot := by exact
    tendsto_atBot_iff_tendsto_atTop_comp_neg


/-- 특수화: `atBot → atTop` 수렴 ↔ `x ↦ -x` 합성 후 `atTop → atTop` 수렴 -/
@[simp]
lemma tendsto_atBot_atTop_iff {α : Type*} [TopologicalSpace α] [Preorder α]
  {f : ℝ → α} :
  Tendsto f atBot atTop ↔ Tendsto (fun x => f (-x)) atTop atTop := by exact
    tendsto_atBot_iff_tendsto_atTop_comp_neg

/-- 특수화: `atTop → atBot` 수렴 ↔ `x ↦ -x` 합성 후 `atBot → atBot` 수렴 -/
@[simp]
lemma tendsto_atTop_atBot_iff {α : Type*} [TopologicalSpace α] [Preorder α]
  {f : ℝ → α} :
  Tendsto f atTop atBot ↔ Tendsto (fun x => f (-x)) atBot atBot := by exact
    tendsto_atTop_iff_tendsto_atBot_comp_neg

/-- 특수화: `atTop → atTop` 수렴 ↔ `x ↦ -x` 합성 후 `atBot → atTop` 수렴 -/
@[simp]
lemma tendsto_atTop_atTop_iff {α : Type*} [TopologicalSpace α] [Preorder α]
  {f : ℝ → α} :
  Tendsto f atTop atTop ↔ Tendsto (fun x => f (-x)) atBot atTop := by exact
    tendsto_atTop_iff_tendsto_atBot_comp_neg



-- Helper lemma: A (positive-leading) cubic with one real root has predictable sign.
-- 보조정리: 최고차항계수가 양수인 삼차다항식이 단일 실근 α만 가지면, α를 기준으로 좌<0, 우>0.
lemma sign_of_cubic_with_one_root
    (f : Cubic ℝ) (h_pos : f.a > 0)
    {α : ℝ} (h_one_root : f.toPoly.roots.toFinset = {α}) :
    (∀ x, x < α → f.toPoly.eval x < 0) ∧ (∀ x, x > α → f.toPoly.eval x > 0) := by
  classical
  set p := f.toPoly

  -- natDegree = 3
  have h_deg3 : p.natDegree = 3 :=
    Cubic.natDegree_of_a_ne_zero (by exact ne_of_gt h_pos)
  have p_LC : p.leadingCoeff = f.a := Cubic.leadingCoeff_of_a_ne_zero (Ne.symm (ne_of_lt h_pos))
  -- leadingCoeff p = f.a, so positive
  have hLC_pos : 0 < p.leadingCoeff := by rw [p_LC]; exact h_pos
  have hLC_ne  : p.leadingCoeff ≠ 0 := ne_of_gt hLC_pos

  -- Limits at ±∞ for odd degree with positive leadingCoeff
  -- x→+∞ : p(x)→+∞,  x→-∞ : p(x)→-∞
  have h_lim_right : Tendsto (fun x : ℝ => p.eval x) atTop atTop := by
    rw [Polynomial.tendsto_atTop_iff_leadingCoeff_nonneg p]
    constructor
    · show 0 < p.degree
      refine natDegree_pos_iff_degree_pos.mp ?_
      exact Nat.lt_of_sub_eq_succ h_deg3
    · show 0 ≤ p.leadingCoeff
      exact Std.le_of_lt hLC_pos


  -- x→-∞ : p(x)→-∞  을 `q(x)=p(-x)`로부터 얻는다.
  have h_lim_left : Tendsto (fun x : ℝ => p.eval x) atBot atBot := by
    -- q의 정의 및 성질
    set q : ℝ[X] := p.comp (-X)
    have hq_deg_pos : 0 < q.degree := by
      -- natDegree p = 3 > 0 ⇒ degree(q) > 0
      have : 0 < p.natDegree := by simp only [h_deg3, Nat.ofNat_pos]
      -- mathlib: `degree_pos_comp_neg_X_of_natDegree_pos`
      simpa [q] using Polynomial.degree_pos_comp_neg_X_of_natDegree_pos (p := p) this
    have hodd : Odd p.natDegree := by simp only [h_deg3]; exact Nat.odd_iff.mpr rfl
    have hq_lc : q.leadingCoeff = - p.leadingCoeff :=
      Polynomial.leadingCoeff_comp_neg_X_of_odd (p := p) hodd
    have hq_lc_nonpos : q.leadingCoeff ≤ 0 := by
      have : 0 ≤ p.leadingCoeff := le_of_lt hLC_pos
      simpa [hq_lc] using (neg_nonpos.mpr this)
    -- q atTop → atBot
    have hq_top_atBot :
        Tendsto (fun x : ℝ => q.eval x) atTop atBot :=
      (Polynomial.tendsto_atBot_of_leadingCoeff_nonpos (P := q) hq_deg_pos hq_lc_nonpos)
    -- q.eval x = p.eval (-x)
    have hq_eval_rewrite : (fun x : ℝ => p.eval (-x)) = (fun x : ℝ => q.eval x) := by
      funext x
      -- eval (p.comp (-X)) x = p.eval (eval x (-X)) = p.eval (-x)
      simp [q]
    have hneg : Tendsto (fun x : ℝ => p.eval (-x)) atTop atBot := by
      rw [hq_eval_rewrite]
      exact hq_top_atBot
    -- 변환: atBot ↔ (∘(-·)) atTop
    exact (tendsto_atBot_iff_tendsto_atTop_comp_neg
      (f := fun x : ℝ => p.eval x) (l := atBot)).mpr hneg

  -- Uniqueness of the root: eval z = 0 ⇒ z = α
  have root_unique : ∀ z, p.eval z = 0 → z = α := by
    intro z hz
    have hz_mem : z ∈ p.roots.toFinset := by
      refine Multiset.mem_toFinset.mpr ?_
      refine (mem_roots ?_).mpr hz
      exact leadingCoeff_ne_zero.mp hLC_ne
    have : z ∈ ({α} : Finset ℝ) := by simpa [h_one_root] using hz_mem
    exact Finset.mem_singleton.mp this

  -- Continuity
  have h_cont : Continuous fun x => p.eval x := Polynomial.continuous p

  -- 좌측 부호: x < α ⇒ p(x) < 0
  have h_left : ∀ x, x < α → p.eval x < 0 := by
    intro x hx
    by_contra hxpos
    have hx_nonneg : 0 ≤ p.eval x := le_of_not_gt hxpos
    -- atBot→atBot 이므로 결국 p(t) ≤ -1 인 구간이 존재
    have hAev : ∀ᶠ t in atBot, p.eval t ≤ -1 :=
      h_lim_left.eventually (eventually_le_atBot (-1))
    obtain ⟨A, hA⟩ := Filter.eventually_atBot.1 hAev
    -- x 보다 작은 L 을 하나 고른다
    let L : ℝ := min A (x - 1)
    have hL_le_A : L ≤ A := min_le_left _ _
    have hL_lt_x : L < x := by
      have : L ≤ x - 1 := min_le_right _ _
      have : L + 1 ≤ x := by linarith
      linarith
    have hL_val_le : p.eval L ≤ -1 := hA _ hL_le_A
    have hL_neg : p.eval L < 0 := by linarith
    -- [L, x]에서 IVT로 근이 생김 (c ≤ x < α ⇒ c ≠ α) → 유일근과 모순
    have hcontOn : ContinuousOn (fun t : ℝ => p.eval t) (Set.Icc L x) := h_cont.continuousOn
    have hIVT :
        Set.Icc (p.eval L) (p.eval x) ⊆ (fun t => p.eval t) '' Set.Icc L x :=
      intermediate_value_Icc (f := fun t : ℝ => p.eval t) (by linarith [le_of_lt hL_lt_x]) hcontOn
    have h0mem : (0 : ℝ) ∈ Set.Icc (p.eval L) (p.eval x) :=
      ⟨le_of_lt hL_neg, hx_nonneg⟩
    rcases hIVT h0mem with ⟨c, hc_Icc, hc0⟩
    have hc_le_x : c ≤ x := (Set.mem_Icc.mp hc_Icc).2
    have hc_ne_alpha : c ≠ α := by
      have hc_lt_alpha : c < α := lt_of_le_of_lt hc_le_x hx
      exact ne_of_lt hc_lt_alpha
    have : c = α := root_unique c hc0
    exact hc_ne_alpha this

  -- 우측 부호: x > α ⇒ p(x) > 0
  have h_right : ∀ x, x > α → p.eval x > 0 := by
    intro x hx
    by_contra hxnonpos
    have hx_le : p.eval x ≤ 0 := le_of_not_gt hxnonpos
    -- atTop→atTop 이므로 결국 p(t) ≥ 1 인 구간이 존재
    have hBev : ∀ᶠ t in atTop, 1 ≤ p.eval t :=
      h_lim_right.eventually (eventually_ge_atTop (1 : ℝ))
    obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 hBev
    -- x 보다 큰 U 를 하나 고른다
    let U : ℝ := max B (x + 1)
    have hU_ge_B : B ≤ U := le_max_left _ _
    have hU_gt_x : x < U := by
      have : x + 1 ≤ U := le_max_right _ _
      have : x ≤ U - 1 := by linarith
      linarith
    have hU_val_ge : 1 ≤ p.eval U := hB _ hU_ge_B
    have hU_pos : 0 < p.eval U := by linarith
    -- [x, U]에서 IVT로 근이 생김 (α < x ≤ c ⇒ c ≠ α) → 유일근과 모순
    have hcontOn : ContinuousOn (fun t : ℝ => p.eval t) (Set.Icc x U) := h_cont.continuousOn
    have hIVT :
        Set.Icc (p.eval x) (p.eval U) ⊆ (fun t => p.eval t) '' Set.Icc x U :=
      intermediate_value_Icc (f := fun t : ℝ => p.eval t) (by linarith [le_of_lt hU_gt_x]) hcontOn
    have h0mem : (0 : ℝ) ∈ Set.Icc (p.eval x) (p.eval U) :=
      ⟨hx_le, le_of_lt hU_pos⟩
    rcases hIVT h0mem with ⟨c, hc_Icc, hc0⟩
    have hx_le_c : x ≤ c := (Set.mem_Icc.mp hc_Icc).1
    have hc_ne_alpha : c ≠ α := by
      have halpha_lt_c : α < c := lt_of_lt_of_le hx hx_le_c
      exact ne_of_gt halpha_lt_c
    have : c = α := root_unique c hc0
    exact hc_ne_alpha this

  exact ⟨h_left, h_right⟩

























-- #1.
example : (24:ℝ) ^ (1 / 3 : ℝ) * 3 ^ (2 / 3 : ℝ) = 6 := by
  calc
    (24:ℝ) ^ (1 / 3 : ℝ) * 3 ^ (2 / 3 : ℝ)
    = (2 ^ (3 : ℝ) * (3 : ℝ)) ^ (1 / 3 : ℝ) * 3 ^ (2 / 3 : ℝ) := by norm_num
    _ = (2 ^ (3 : ℝ)) ^ (1 / 3 : ℝ) * (3 : ℝ) ^ (1 / 3 : ℝ) * 3 ^ (2 / 3 : ℝ) := by rw [Real.mul_rpow]; all_goals norm_num
    _ = 2 * (3 : ℝ) ^ (1 / 3 : ℝ) * 3 ^ (2 / 3 : ℝ) := by rw [← Real.rpow_mul]; all_goals norm_num
    _ = 2 * ((3 : ℝ) ^ (1 / 3 : ℝ) * 3 ^ (2 / 3 : ℝ)) := by rw [mul_assoc]
    _ = 2 * (3 : ℝ) ^ ((1 / 3 : ℝ) + (2 / 3 : ℝ)) := by rw [Real.rpow_add]; all_goals norm_num
    _ = 6 := by norm_num

-- #2.
example : deriv (fun x : ℝ => 2*x^3 - 5*x^2 + 3) 2 = 4 := by norm_num

-- #3.
example {θ : ℝ}
  (hθ : (3 / 2 : ℝ) * π < θ ∧ θ < 2 * π)
  (hsin : sin (-θ) = 1 / 3) :
  tan θ = -√2 / 4 := by
  -- sin (−θ) = 1/3 ⟹ sin θ = −1/3
  have hsin' : sin θ = -1 / 3 := by rw [Real.sin_neg] at hsin; linarith
  clear hsin
  -- θ ∈ (3π/2, 2π) ⟹ cos θ > 0
  have hcos_abs : |cos θ| = (2 * √2) / 3 := by
    calc
      |cos θ| = √(1 - sin θ ^ 2) := Real.abs_cos_eq_sqrt_one_sub_sin_sq θ
      _ = √8 / 3 := by rw [hsin']; norm_num
      _ = √(2 ^ 2 * 2) / 3 := by norm_num
      _ = (2 * √2) / 3 := by simp only [Nat.ofNat_nonneg, pow_nonneg, sqrt_mul, sqrt_sq]
  have hcos_pos : cos θ > 0 := by
    have h2 : cos (2 * π - θ) > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      simp only [Set.mem_Ioo, neg_lt_sub_iff_lt_add]
      constructor
      · linarith
      · linarith
    rw [Real.cos_two_pi_sub] at h2
    exact h2
  have hcos : cos θ = (2 * √2) / 3 := by rw [abs_of_pos hcos_pos] at hcos_abs; exact hcos_abs
  calc
    tan θ
        = sin θ / cos θ := Real.tan_eq_sin_div_cos θ
    _   = (-1 / 3) / ((2 * √2) / 3)   := by rw [hsin', hcos];
    _   = -(1 / (2 * √2))             := by field_simp
    _   = -√2 / 4                     := by field_simp; rw [mul_comm]; simp only [Nat.ofNat_nonneg, sq_sqrt, neg_inj]; ring

-- #4.
example {a}
  (h : Continuous (fun x : ℝ ↦ if x < 2 then 3 * x - a else x^2 + a)) :
  a = 1 := by
  let f := fun x : ℝ ↦ if x < 2 then 3 * x - a else x^2 + a
  have h_cont_at_2 : ContinuousAt f 2 := h.continuousAt

  -- x가 2로 갈 때의 좌극한
  have h_limit_calc : Tendsto f (𝓝[<] 2) (𝓝 (6 - a)) := by
    have hf_eq : ∀ x ∈ Set.Iio 2, (fun x' ↦ 3 * x' - a) x = f x := by
      intro x hx
      unfold f
      rw [ite_cond_eq_true]
      exact eq_true hx

    apply tendsto_nhdsWithin_congr hf_eq
    have h_lin_cont : Continuous (fun x' : ℝ => 3 * x' - a) := by fun_prop
    have h_within := Continuous.continuousWithinAt h_lin_cont (s := Iio 2) (x := 2)
    simp only [ContinuousWithinAt, nhdsWithin] at h_within
    convert h_within using 1
    · ring_nf

  -- 연속성에 의해 좌극한 = f(2)
  have h_limit_eq_val : 6 - a = f 2 :=
    tendsto_nhds_unique h_limit_calc (h_cont_at_2.continuousWithinAt)

  simp [f] at h_limit_eq_val
  linarith


-- #5.
example (f : Polynomial ℝ)
    (h_deriv : ∀ x, (derivative f).eval x = (3 : ℝ) * x * (x - 2))
    (h_val : f.eval 1 = 6) :
    f.eval 2 = 4 := by
    -- g(x) = x³ - 3x² + 8
    let g := X^3 - 3*X^2 + C (8 : ℝ)
    have deriv_eq : derivative f = derivative g := by
      apply Polynomial.funext
      intro x
      have dg_eval : (derivative g).eval x = 3 * x * (x - 2) := by
        simp [g]; ring
      rw [h_deriv, dg_eval]

    -- derivative (f - g) = derivative f - derivative g = 0
    have deriv_zero : derivative (f - g) = 0 := by
      rw [Polynomial.derivative_sub, deriv_eq]; simp

    have eq_const : f - g = C ((f - g).coeff 0) := Polynomial.eq_C_of_derivative_eq_zero deriv_zero
    -- use the value at 1 to show that constant is 0, hence f = g
    have hf_eq_g : f = g := by
      apply eq_of_sub_eq_zero
      rw [eq_const]
      apply C_eq_zero.mpr
      have hg1 : g.eval 1 = 6 := by simp [g]; norm_num
      have hfg1 : (f - g).eval 1 = 0 := by simp [h_val, hg1]
      -- since (f - g) = C c, evaluation at 1 gives c = 0
      rwa [eq_const, eval_C] at hfg1

    -- now evaluate at 2
    rw [hf_eq_g]
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_ofNat, eval_C, g]
    norm_num

/-
6. 등비수열 {aₙ}의 첫째항부터 제n항까지의 합을 Sₙ이라 하자.
   S₄ - S₂ = 3a₄, a₅ = 3/4
   일 때, a₁ + a₂의 값은? [3점]

   ① 27      ② 24      ③ 21      ④ 18      ⑤ 15
-/

example
    -- a₁: 첫째항 (the first term)
    -- r: 공비 (the common ratio)
    {a₁ r : ℝ}
    -- h1, h2: 문제의 조건 (the given conditions)
    (h1 : let a := fun n : ℕ ↦ a₁ * r ^ (n - 1)
          let S := fun n : ℕ ↦ ∑ i ∈ range n, a (i + 1)
          S 4 - S 2 = 3 * a 4)
    (h2 : a₁ * r ^ (5 - 1) = 3/4) :
    -- 결론 (the value to find)
    a₁ + a₁ * r = 18 := by
  -- Define 'a' as the geometric sequence and 'S' as its partial sum for the proof.
  let a := fun n : ℕ ↦ a₁ * r ^ (n - 1)
  let S := fun n : ℕ ↦ ∑ i ∈ range n, a (i + 1)

  -- 조건 h2 (a₅ = 3/4)는 a₁과 r이 0이 아님을 암시합니다.
  -- Condition h2 (a₅ = 3/4) implies that a₁ and r are non-zero.
  have ha₁_ne_zero : a₁ ≠ 0 := by
    intro ha₁_zero
    rw [ha₁_zero] at h2
    simp only [Nat.add_one_sub_one, zero_mul] at h2
    norm_num at h2

  have hr_ne_zero : r ≠ 0 := by
    intro hr_zero
    rw [hr_zero] at h2
    simp only [Nat.add_one_sub_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero] at h2
    norm_num at h2

  -- 조건 h1 (S₄ - S₂ = 3a₄)을 간단히 합니다.
  -- S₄ - S₂ = (a₁ + a₂ + a₃ + a₄) - (a₁ + a₂) = a₃ + a₄.
  have h1_simplified : a 3 + a 4 = 3 * a 4 := by
    have h_S_diff : S 4 - S 2 = a 3 + a 4 := by
      unfold S
      -- S 4 = (S 3) + a 4 = (S 2 + a 3) + a 4
      simp_rw [sum_range_succ]
      simp only [Finset.range_zero, sum_empty, zero_add, Nat.reduceAdd]
      rw [add_assoc]
      simp only [add_sub_cancel_left]
    rw [←h_S_diff]
    exact h1

  -- 위 식으로부터 a₃ = 2a₄를 유도합니다.
  have h_a3_eq_2a4 : a 3 = 2 * a 4 := by
    linarith [h1_simplified]

  -- 등비수열의 정의를 이용하여 공비 r을 구합니다.
  -- a₁ * r² = 2 * (a₁ * r³)
  have hr_is_half : r = 1/2 := by
    unfold a at h_a3_eq_2a4
    simp only [Nat.add_one_sub_one] at h_a3_eq_2a4
    field_simp at h_a3_eq_2a4
    linarith

  -- 구한 공비 r의 값을 h2에 대입하여 첫째항 a₁을 구합니다.
  -- a₁ * (1/2)⁴ = 3/4  =>  a₁ * (1/16) = 3/4  =>  a₁ = 12
  have ha₁_is_12 : a₁ = 12 := by
    rw [hr_is_half] at h2
    field_simp at h2
    linarith

  -- 마지막으로, a₁과 a₂의 합을 계산합니다.
  -- a₁ + a₂ = a₁ + a₁ * r
  rw [ha₁_is_12, hr_is_half]
  norm_num


/-
7. 함수 f(x) = (1/3)x³ - 2x² - 12x + 4가 x = α에서 극대이고
   x = β에서 극소일 때, β - α의 값은? (단, α와 β는 상수이다.) [3점]

   ① -4      ② -1      ③ 2      ④ 5      ⑤ 8
-/
example
  {α β : ℝ}
  (h_max : IsLocalMax (fun x : ℝ => (1/3) * x^3 - 2 * x^2 - 12 * x + 4) α)
  (h_min : IsLocalMin (fun x : ℝ => (1/3) * x^3 - 2 * x^2 - 12 * x + 4) β) :
  β - α = 8 := by
  -- 본문에서 f를 '정의'로 도입
  let f : ℝ → ℝ := fun x => (1/3) * x^3 - 2 * x^2 - 12 * x + 4

  have h_deriv : deriv f = fun x => x^2 - 4*x - 12 := by
    funext x
    change deriv (fun x : ℝ => (1/3) * x^3 - 2 * x^2 - 12 * x + 4) x = _
    simp only [mul_comm, sub_eq_add_neg]
    norm_num
    rw [mul_comm, ←mul_assoc, one_div, inv_mul_cancel₀ (by norm_num), one_mul, add_right_inj, neg_inj]
    show 2 * x * 2 = x * 4
    rw [mul_comm 2 x, mul_assoc]
    norm_num

  -- 인수분해 (x+2)(x-6)
  have h_fac (x : ℝ) : x^2 - 4*x - 12 = (x + 2) * (x - 6) := by ring

  ------------------------------------------------------------------
  -- 2) 극값이면 도함수=0 → α,β는 임계점
  ------------------------------------------------------------------
  have hα0 : deriv f α = 0 := h_max.deriv_eq_zero
  have hβ0 : deriv f β = 0 := h_min.deriv_eq_zero

  -- α 후보는 -2 또는 6
  have hα_root : α = -2 ∨ α = 6 := by
    have hmul_zero : (α + 2) * (α - 6) = 0 := by
      simpa [h_deriv, h_fac α] using hα0
    rcases mul_eq_zero.mp hmul_zero with hα1 | hα2
    show α = -2 ∨ α = 6
    · left;  linarith [hα1]
    · right; linarith [hα2]

  -- β 후보는 -2 또는 6
  have hβ_root : β = -2 ∨ β = 6 := by
    have hmul_zero : (β + 2) * (β - 6) = 0 := by
      simpa [h_deriv, h_fac β] using hβ0
    rcases mul_eq_zero.mp hmul_zero with hβ1 | hβ2
    · left;  linarith [hβ1]
    · right; linarith [hβ2]

  ------------------------------------------------------------------
  -- 3) 2계 도함수: f''(x) = 2x - 4
  ------------------------------------------------------------------
  have h_deriv2 : deriv (deriv f) = fun x => 2*x - 4 := by
    funext x
    rw [h_deriv]
    simp only [mul_comm, sub_eq_add_neg, deriv_add_const', differentiableAt_fun_id,
      DifferentiableAt.fun_pow, differentiableAt_fun_neg_iff, differentiableAt_const,
      DifferentiableAt.fun_mul, deriv_fun_add, deriv_fun_pow, Nat.cast_ofNat, Nat.add_one_sub_one,
      pow_one, deriv_id'', mul_left_comm, one_mul, deriv.fun_neg', deriv_fun_mul, deriv_const',
      mul_zero, add_zero]


  have h2α : deriv (deriv f) α = 2*α - 4 := by
    rw [h_deriv2]
  have h2β : deriv (deriv f) β = 2*β - 4 := by
    rw [h_deriv2]

  ------------------------------------------------------------------
  -- 4) 부호 판정으로 α, β 확정
  --
  -- 계산:
  --   f''(-2) = 2*(-2) - 4 = -8 < 0  → 그 점은 극대 후보
  --   f''(6)  = 2*6 - 4    =  8 > 0  → 그 점은 극소 후보
  --
  -- 따라서 α는 -2, β는 6이어야 한다.
  ------------------------------------------------------------------

  ------------------------------------------------------------------
  -- 차이식 인수분해로 극대/극소 분류
  -- f(x) - f(6)  = ((x-6)^2 * (x+6)) / 3
  -- f(x) - f(-2) = ((x-10) * (x+2)^2) / 3
  ------------------------------------------------------------------
  have diff_at6 :
      ∀ x, f x - f 6 = ((x - 6)^2 * (x + 6)) / 3 := by
    sorry

  have diff_atm2 :
      ∀ x, f x - f (-2) = ((x - 10) * (x + 2)^2) / 3 := by
    intro x
    have : 3 * (f x - f (-2)) = (x - 10) * (x + 2)^2 := by
      ring_nf
      sorry
    field_simp [this]
    sorry

  sorry



example
  {α β : ℝ}
  (h_max : IsLocalMax (fun x : ℝ => (1/3) * x^3 - 2 * x^2 - 12 * x + 4) α)
  (h_min : IsLocalMin (fun x : ℝ => (1/3) * x^3 - 2 * x^2 - 12 * x + 4) β) :
  β - α = 8 := by
  -- 이름 붙이기
  let f : ℝ → ℝ := fun x => (1/3) * x^3 - 2 * x^2 - 12 * x + 4
  have hmax' : IsLocalMax f α := by simpa [f] using h_max
  have hmin' : IsLocalMin f β := by simpa [f] using h_min

  -- f'(x) = x^2 - 4x - 12 = (x+2)(x-6)
  have h_deriv : deriv f = fun x => x^2 - 4*x - 12 := by
    funext x
    unfold f
    simp only [mul_comm, sub_eq_add_neg]
    norm_num
    rw [mul_comm, ←mul_assoc, one_div, inv_mul_cancel₀ (by norm_num), one_mul, add_right_inj, neg_inj]
    show 2 * x * 2 = x * 4
    rw [mul_comm 2 x, mul_assoc]
    norm_num
  have h_fac (x : ℝ) : x^2 - 4*x - 12 = (x + 2) * (x - 6) := by ring

  -- 극값 ⇒ 도함수 0 → 임계점은 −2 또는 6
  have hα0 : deriv f α = 0 := by simpa using hmax'.deriv_eq_zero
  have hβ0 : deriv f β = 0 := by simpa using hmin'.deriv_eq_zero
  have hα_root : α = -2 ∨ α = 6 := by
    have : (α + 2) * (α - 6) = 0 := by simpa [h_deriv, h_fac α] using hα0
    exact (mul_eq_zero.mp this).elim (fun h => Or.inl (by linarith)) (fun h => Or.inr (by linarith))
  have hβ_root : β = -2 ∨ β = 6 := by
    have : (β + 2) * (β - 6) = 0 := by simpa [h_deriv, h_fac β] using hβ0
    exact (mul_eq_zero.mp this).elim (fun h => Or.inl (by linarith)) (fun h => Or.inr (by linarith))

  -- f''(x) = 2x - 4
  have h_deriv2 : deriv (deriv f) = fun x => 2*x - 4 := by
    funext x
    have : deriv (fun y : ℝ => y^2 - 4*y - 12) x = 2*x - 4 := by
      simp only [mul_comm, sub_eq_add_neg, deriv_add_const', differentiableAt_fun_id,
        DifferentiableAt.fun_pow, differentiableAt_fun_neg_iff, differentiableAt_const,
        DifferentiableAt.fun_mul, deriv_fun_add, deriv_fun_pow, Nat.cast_ofNat, Nat.add_one_sub_one,
        pow_one, deriv_id'', mul_left_comm, one_mul, deriv.fun_neg', deriv_fun_mul, deriv_const',
        mul_zero, add_zero]
    simpa [h_deriv] using this
  have hCts : ContinuousAt f (-2) := by unfold f; sorry
  have hCts6 : ContinuousAt f 6 := by sorry

  -- 이차 미분 판정으로 분류 고정:
  --   -2 에서는 f''<0 이고 f'(-2)=0 이므로 국소 최대
  have hMaxAtNeg2 : IsLocalMax f (-2) := by
    have : deriv (deriv f) (-2) < 0 := by simpa [h_deriv2] using (by norm_num : (2*(-2:ℝ) - 4) < 0)
    have : deriv f (-2) = 0 := by
      simp only [h_deriv, even_two, Even.neg_pow, mul_neg, sub_neg_eq_add]
      norm_num
    exact isLocalMax_of_deriv_deriv_neg (x₀ := -2) (f := f) (by simpa using ‹_›) (by simpa using ‹_›) hCts
  --   6 에서는 f''>0 이고 f'(6)=0 이므로 국소 최소
  have hMinAt6 : IsLocalMin f 6 := by
    have : deriv (deriv f) 6 > 0 := by simpa [h_deriv2] using (by norm_num : (2*(6:ℝ) - 4) > 0)
    have : deriv f 6 = 0 := by
      have : (6 + 2) * (6 - 6) = 0 := by norm_num
      simpa [h_deriv, h_fac 6]
    exact isLocalMin_of_deriv_deriv_pos (x₀ := 6) (f := f) (by simpa using ‹_›) (by simpa using ‹_›) hCts6

  -- 이제 α, β를 결정
  have hα : α = -2 := by
    rcases hα_root with rfl | hα6
    · rfl
    ·
      -- IsLocalMax at 6 → 근방에서 f y ≤ f 6
      have hev : ∀ᶠ y in 𝓝 (6 : ℝ), f y ≤ f 6 := by simpa [hα6] using hmax'
      rcases Metric.eventually_nhds_iff.mp hev with ⟨ε, hε, hεall⟩
      -- 작은 δ>0를 골라 y=6+δ 가 그 근방에 들어가게 한다
      let δ : ℝ := min (ε/2) (1/2)
      have hδpos : 0 < δ := by
        have : 0 < min (ε/2) (1/2) := by
          exact lt_min_iff.mpr ⟨half_pos hε, by norm_num⟩
        simpa [δ] using this
      let y : ℝ := 6 + δ
      have hy_in : dist y 6 < ε := by
        -- |y-6| = δ < ε/2 < ε
        have : δ < ε := (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))
        simpa [Real.dist_eq, y, abs_of_nonneg (le_of_lt hδpos)] using this
      -- 차이식 인수분해로 f y - f 6 > 0
      have hy_pos : 0 < f y - f 6 := by
        -- 3*(f y - f 6) = (y-6)^2*(y+6) = δ^2*(12+δ) > 0
        have : 0 < ((y - 6)^2 * (y + 6)) := by
          have A : 0 < (y - 6)^2 := by
            have : y - 6 ≠ 0 := by simpa [y] using (ne_of_gt hδpos : δ ≠ 0)
            simp only [gt_iff_lt]
            exact pow_two_pos_of_ne_zero this
          have B : 0 < y + 6 := by
            -- y=6+δ ⇒ y+6=12+δ>0
            linarith [hδpos]
          exact Left.mul_pos A B
        -- 3>0 → 좌변도 양수
        have : 0 < 3 * (f y - f 6) := by
          simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, sub_pos, y]
          unfold f
          ring_nf
          linarith
        -- ⇒ f y - f 6 > 0
        have : 0 < (f y - f 6) := by
          have h3 : (0 : ℝ) < 3 := by norm_num
          exact (mul_pos_iff_of_pos_left h3).1 this
        exact this
      have hy_gt : f 6 < f y := sub_pos.mp hy_pos
      -- 그런데 근방에서는 f y ≤ f 6 이어야 함 → 모순
      have : f y ≤ f 6 := hεall hy_in
      exact (lt_of_le_of_lt this hy_gt).false.elim

  have hβ : β = 6 := by
    rcases hβ_root with hβm2 | rfl
    ·
      -- IsLocalMin at -2 → 근방에서 f (-2) ≤ f y
      have hev : ∀ᶠ y in 𝓝 (-2 : ℝ), f (-2) ≤ f y := by simpa [hβm2] using hmin'
      rcases Metric.eventually_nhds_iff.mp hev with ⟨ε, hε, hεall⟩
      let δ : ℝ := min (ε/2) (1/2)
      have hδpos : 0 < δ := by
        have : 0 < min (ε/2) (1/2) := by
          exact lt_min_iff.mpr ⟨half_pos hε, by norm_num⟩
        simpa [δ] using this
      let y : ℝ := (-2) + δ
      have hy_in : dist y (-2) < ε := by
        have : δ < ε := (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))
        simpa [Real.dist_eq, y, abs_of_nonneg (le_of_lt hδpos), add_comm, add_left_comm, add_assoc] using this
      -- 차이식 인수분해로 f y - f (-2) < 0
      have hy_neg : f y - f (-2) < 0 := by
        -- 3*(f y - f (-2)) = (y-10)*(y+2)^2, 여기서 y=-2+δ → (y-10) < 0, (y+2)^2 = δ^2 > 0
        have A : y - 10 < 0 := by
          have : δ ≤ 1/2 := min_le_right _ _
          linarith [this]
        have B : 0 < (y + 2)^2 := by
          have : y + 2 ≠ 0 := by simp only [add_comm, add_neg_cancel_comm_assoc, ne_eq, hδpos.ne',
            not_false_eq_true, y]
          exact pow_two_pos_of_ne_zero this
        have : (y - 10) * (y + 2)^2 < 0 := mul_neg_of_neg_of_pos A B
        -- 3>0 이므로 좌변 <0 → f y - f (-2) < 0
        have h3 : (0 : ℝ) < 3 := by norm_num
        have : 3 * (f y - f (-2)) < 0 := by unfold f; ring_nf; linarith
        exact (pos_iff_neg_of_mul_neg this).mp h3
      have hy_lt : f y < f (-2) := by exact sub_neg.mp hy_neg
      -- 근방에서는 f (-2) ≤ f y 이어야 함 → 모순
      have : f (-2) ≤ f y := hεall hy_in
      exact (lt_of_le_of_lt this hy_lt).false.elim
    · rfl

  -- 결론
  rw [hα, hβ]
  norm_num











private lemma eval_split (p : ℝ[X]) (x : ℝ) :
    p.eval x
      = p.leadingCoeff * x ^ p.natDegree
        + ∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ i := by
  simp only [Polynomial.eval_eq_sum_range (p := p) x, mul_comm, Finset.sum_range_succ]
  rw [add_comm, mul_comm, leadingCoeff]

-- /-- (핵심) 하위항의 비가 0으로 감: `x → +∞`에서 `∑_{i<n} a_i x^i / (a_n x^n) → 0`. -/
-- private lemma tendsto_tail_over_leading
--     (p : ℝ[X]) (hdeg : 0 < p.natDegree) :
--     Tendsto
--       (fun x : ℝ =>
--         (∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ i) /
--           (p.leadingCoeff * x ^ p.natDegree))
--       atTop (𝓝 0) := by
--   classical

--   have hlc : p.leadingCoeff ≠ 0 :=
--     Polynomial.leadingCoeff_ne_zero.mpr
--       (Polynomial.ne_zero_of_natDegree_gt (by simpa using hdeg))
--   -- 합-나눗셈 분배
--   simp_rw [Finset.sum_div]

--   -- 유한합의 극한 = 합의 극한
--   have hsum :
--       Tendsto
--         (fun x : ℝ =>
--           ∑ i ∈ Finset.range p.natDegree,
--             (p.coeff i * x ^ i) / (p.leadingCoeff * x ^ p.natDegree))
--         atTop
--         (𝓝 (∑ _i ∈ Finset.range p.natDegree, (0 : ℝ))) := by
--     refine
--       @tendsto_finset_sum
--         (ι := ℕ) (α := ℝ) (M := ℝ) _ _ _
--         (f := fun i (x : ℝ) =>
--           (p.coeff i * x ^ i) / (p.leadingCoeff * x ^ p.natDegree))
--         (x := atTop)
--         (a := fun _ => (0 : ℝ))
--         (s := Finset.range p.natDegree)
--         ?all
--     -- 각 항이 0으로 감을 보이면 됨
--     intro i hi
--     have hi_lt : i < p.natDegree := Finset.mem_range.mp hi

--     -- (x^i / x^n) =ᶠ (x^(n-i))⁻¹  (atTop에서 결국 x>0)
--     have heq :
--         (fun x : ℝ => x ^ i / x ^ p.natDegree)
--           =ᶠ[atTop]
--         (fun x : ℝ => (x ^ (p.natDegree - i))⁻¹) := by
--       filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
--       have hx0 : x ≠ 0 := ne_of_gt hx
--       field_simp [pow_ne_zero _ hx0, div_eq_mul_inv, pow_sub, hi_lt.le]
--       refine pow_mul_pow_sub x ?_
--       exact Nat.le_of_succ_le hi_lt

--     have heq' :
--         (fun x : ℝ =>
--           (p.coeff i / p.leadingCoeff) * ((x ^ i) / (x ^ p.natDegree)))
--           =ᶠ[atTop]
--         (fun x : ℝ =>
--           (p.coeff i / p.leadingCoeff) * (x ^ (p.natDegree - i))⁻¹) :=
--       heq.mono (by
--         intro x hx
--         simp only [hx])

--     -- 역거듭제곱은 0으로 감
--     have h_inv :
--         Tendsto (fun x : ℝ => (x ^ (p.natDegree - i))⁻¹) atTop (𝓝 0) :=
--       tendsto_inv_atTop_zero.comp
--         (tendsto_pow_atTop (Nat.ne_of_gt (Nat.sub_pos_of_lt hi_lt)))

--     have :
--         Tendsto
--           (fun x : ℝ =>
--             (p.coeff i / p.leadingCoeff) * ((x ^ i) / (x ^ p.natDegree)))
--           atTop (𝓝 0) := by
--       -- heq로 치환 후 const_mul
--       refine (Tendsto.congr' heq'.symm ?_)
--       simpa [mul_zero] using h_inv.const_mul (p.coeff i / p.leadingCoeff)

--     -- 우리가 원하는 항과 동일
--     -- (분자 분모를 상수배 형태로 만든 뒤 위 극한을 재해석)
--     refine this.congr' ?_
--     filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx0
--     field_simp [hlc, pow_ne_zero _ hx0, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

--   -- 여기서 결론은 𝓝 (∑ … 0) 이므로 𝓝 0 으로 정리
--   simpa [Finset.sum_const_zero] using hsum



/--
[보조정리] 홀수 차수의 실수 다항식은 적어도 하나의 실근을 가진다.
[Lemma] A real polynomial of odd degree has at least one real root.
-/
lemma exists_root_of_odd_degree {p : ℝ[X]} (hodd : Odd p.natDegree) :
  ∃ x, p.eval x = 0 := by
  classical
  -- deg > 0
  have hdeg_pos : 0 < p.degree := by
    have : 0 < p.natDegree := hodd.pos
    exact (Polynomial.natDegree_pos_iff_degree_pos).1 this

  -- atTop에서의 발산 부호: lc 부호에 따라 결정
  have h_top :
      Tendsto (fun x : ℝ => p.eval x) atTop atTop ∨
      Tendsto (fun x : ℝ => p.eval x) atTop atBot := by
    rcases le_total (0 : ℝ) p.leadingCoeff with hnonneg | hnonpos
    · -- lc ≥ 0 ⇒ atTop → +∞
      left
      exact (Polynomial.tendsto_atTop_iff_leadingCoeff_nonneg (P := p)).2 ⟨hdeg_pos, hnonneg⟩
    · -- lc ≤ 0 ⇒ atTop → -∞
      right
      exact (Polynomial.tendsto_atBot_iff_leadingCoeff_nonpos (P := p)).2 ⟨hdeg_pos, hnonpos⟩

  -- q(x) := p(-x)
  set q : ℝ[X] := p.comp (-X)

  -- q의 natDegree = p의 natDegree
  have hq_nat : q.natDegree = p.natDegree := by
    simp only [natDegree_comp_neg_X, q]

  -- q의 degree > 0
  have hq_deg : 0 < q.degree := by
    have hp_nat_pos : 0 < p.natDegree := hodd.pos
    simp only [gt_iff_lt, q]
    exact degree_pos_comp_neg_X_of_natDegree_pos hp_nat_pos

  -- q의 lc = (-1)^n * lc(p) = - lc(p) (n = p.natDegree가 홀수)
  have hq_lc : q.leadingCoeff = (-1 : ℝ) ^ p.natDegree * p.leadingCoeff := by
    -- mathlib: `comp_neg_X_leadingCoeff_eq`
    simp only [comp_neg_X_leadingCoeff_eq, q]
  have neg_one_pow_odd : (-1 : ℝ) ^ p.natDegree = -1 := by
    simpa using hodd.neg_one_pow

  -- q의 atTop 거동
  have hq_top :
      Tendsto (fun x : ℝ => q.eval x) atTop atTop ∨
      Tendsto (fun x : ℝ => q.eval x) atTop atBot := by
    -- q.leadingCoeff = - p.leadingCoeff
    have : q.leadingCoeff = - p.leadingCoeff := by
      simp only [hq_lc, neg_one_pow_odd, neg_mul, one_mul]
    rcases le_total (0 : ℝ) p.leadingCoeff with hnonneg | hnonpos
    · -- lc(p) ≥ 0 ⇒ lc(q) ≤ 0 ⇒ q atTop → -∞
      right
      have hnonpos' : q.leadingCoeff ≤ 0 := by simpa [this]
      exact (Polynomial.tendsto_atBot_of_leadingCoeff_nonpos (P := q) hq_deg hnonpos')
    · -- lc(p) ≤ 0 ⇒ lc(q) ≥ 0 ⇒ q atTop → +∞
      left
      have hnonneg' : 0 ≤ q.leadingCoeff := by simpa [this]
      exact (Polynomial.tendsto_atTop_of_leadingCoeff_nonneg (P := q) hq_deg hnonneg')

  -- q.eval x = p.eval (-x)
  have hcomp : (fun x : ℝ => q.eval x) = fun x => p.eval (-x) := by
    funext x; simp [q]

  -- q의 atTop 거동을 p의 atBot 거동으로 옮긴다.
  have h_bot' :
      Tendsto (fun x : ℝ => p.eval x) atBot atTop ∨
      Tendsto (fun x : ℝ => p.eval x) atBot atBot := by
    rcases hq_top with hq_pos | hq_neg
    · -- q atTop→+∞ ⇒ p atBot→+∞
      left
      have : Tendsto (fun x : ℝ => p.eval (-x)) atTop atTop := by
        rw [← hcomp]; exact hq_pos
      exact (tendsto_atBot_iff_tendsto_atTop_comp_neg
        (f := fun x : ℝ => p.eval x) (l := atTop)).mpr this
    · -- q atTop→-∞ ⇒ p atBot→-∞
      right
      have : Tendsto (fun x : ℝ => p.eval (-x)) atTop atBot := by
        rw [← hcomp]; exact hq_neg
      exact (tendsto_atBot_iff_tendsto_atTop_comp_neg
        (f := fun x : ℝ => p.eval x) (l := atBot)).mpr this

  -- 연속성
  have hcont : Continuous fun x : ℝ => p.eval x := (Polynomial.continuous (p := p))

  -- 이제 +∞/−∞에서 서로 반대 부호의 eventually 를 뽑아 IVT 적용
  cases h_top with
  | inl h_plus =>
    -- lc ≥ 0 를 추출
    have h_lc_nonneg : 0 ≤ p.leadingCoeff :=
      ((Polynomial.tendsto_atTop_iff_leadingCoeff_nonneg (P := p)).1 h_plus).2
    -- q.leadingCoeff = - lc ≤ 0 ⇒ q atTop → -∞
    have h_q_atTop_atBot : Tendsto (fun x : ℝ => q.eval x) atTop atBot := by
      have : q.leadingCoeff ≤ 0 := by
        -- q.lc = (-1)^n * lc = - lc  (n odd)
        simpa [hq_lc, neg_one_pow_odd, neg_mul, one_mul] using (neg_nonpos.mpr h_lc_nonneg)
      exact (Polynomial.tendsto_atBot_of_leadingCoeff_nonpos (P := q) hq_deg this)
    -- p atBot → -∞  (합성 레마 사용)
    have h_bot_neg : Tendsto (fun x : ℝ => p.eval x) atBot atBot := by
      -- q.eval x = p.eval (-x)
      have : Tendsto (fun x : ℝ => p.eval (-x)) atTop atBot := by
        have hcomp : (fun x : ℝ => q.eval x) = fun x => p.eval (-x) := by
          funext x; simp [q]
        rw [← hcomp]
        exact h_q_atTop_atBot
      exact (tendsto_atBot_iff_tendsto_atTop_comp_neg
        (f := fun x : ℝ => p.eval x) (l := atBot)).mpr this

    -- 오른쪽 끝: 충분히 크면 양수
    obtain ⟨R, hRpos⟩ :
        ∃ R, ∀ x ≥ R, 0 < p.eval x :=
      Filter.eventually_atTop.1 (h_plus.eventually (eventually_gt_atTop (0 : ℝ)))
    -- 왼쪽 끝: 충분히 작으면 음수
    obtain ⟨L, hLneg⟩ :
        ∃ L, ∀ x ≤ L, p.eval x < 0 :=
      Filter.eventually_atBot.1 (h_bot_neg.eventually (eventually_lt_atBot (0 : ℝ)))

    -- 구간 [a,b]에서 부호 변화
    set a : ℝ := min L R
    set b : ℝ := max L R
    have hab : a ≤ b := min_le_max
    have ha_neg : p.eval a < 0 := by
      have : a ≤ L := min_le_left _ _
      exact hLneg _ this
    have hb_pos : 0 < p.eval b := by
      have : R ≤ b := le_max_right _ _
      exact hRpos _ this

    -- IVT: 0 ∈ [p a, p b] ⊆ p '' [a,b]
    have hcontOn : ContinuousOn (fun x : ℝ => p.eval x) (Set.Icc a b) := hcont.continuousOn
    have hIVT :
        Set.Icc (p.eval a) (p.eval b) ⊆ (fun x => p.eval x) '' Set.Icc a b :=
      intermediate_value_Icc (f := fun x : ℝ => p.eval x) hab hcontOn
    have h0mem : (0 : ℝ) ∈ Set.Icc (p.eval a) (p.eval b) :=
      ⟨le_of_lt ha_neg, le_of_lt hb_pos⟩
    rcases hIVT h0mem with ⟨c, _hcab, hc0⟩
    exact ⟨c, hc0⟩

  | inr h_minus => -- atTop → -∞
    -- 오른쪽 끝: 충분히 크면 음수
    have h_lc_nonpos : p.leadingCoeff ≤ 0 :=
      ((Polynomial.tendsto_atBot_iff_leadingCoeff_nonpos (P := p)).1 h_minus).2
    have h_q_atTop_atTop : Tendsto (fun x : ℝ => q.eval x) atTop atTop := by
      have : 0 ≤ q.leadingCoeff := by
        -- q.lc = - lc ≥ 0
        simpa [hq_lc, neg_one_pow_odd, neg_mul, one_mul] using (neg_nonneg.mpr h_lc_nonpos)
      exact (Polynomial.tendsto_atTop_of_leadingCoeff_nonneg (P := q) hq_deg this)
    have h_bot_pos : Tendsto (fun x : ℝ => p.eval x) atBot atTop := by
      have : Tendsto (fun x : ℝ => p.eval (-x)) atTop atTop := by
        have hcomp : (fun x : ℝ => q.eval x) = fun x => p.eval (-x) := by
          funext x; simp [q]
        rw [← hcomp]
        exact h_q_atTop_atTop
      exact (tendsto_atBot_iff_tendsto_atTop_comp_neg
        (f := fun x : ℝ => p.eval x) (l := atTop)).mpr this

    obtain ⟨R, hRneg⟩ :
        ∃ R, ∀ x ≥ R, p.eval x < 0 :=
      Filter.eventually_atTop.1 (h_minus.eventually (eventually_lt_atBot (0 : ℝ)))

    obtain ⟨L, hLpos⟩ :
        ∃ L, ∀ x ≤ L, 0 < p.eval x :=
      Filter.eventually_atBot.1 (h_bot_pos.eventually (eventually_gt_atTop (0 : ℝ)))


    -- 구간 [a,b]에서 부호 변화 (a에서 양수, b에서 음수)
    set a : ℝ := min L R
    set b : ℝ := max L R
    have hab : a ≤ b := min_le_max
    have ha_pos : 0 < p.eval a := by
      have : a ≤ L := min_le_left _ _
      exact hLpos _ this
    have hb_neg : p.eval b < 0 := by
      have : R ≤ b := le_max_right _ _
      exact hRneg _ this

    -- 이번엔 -p로 IVT를 적용해 0을 집어넣는다.
    have hcontOn' : ContinuousOn (fun x : ℝ => (-p).eval x) (Set.Icc a b) :=
      (Polynomial.continuous (p := -p)).continuousOn
    have hIVT' :
        Set.Icc ((-p).eval a) ((-p).eval b) ⊆ (fun x => (-p).eval x) '' Set.Icc a b :=
      intermediate_value_Icc (f := fun x : ℝ => (-p).eval x) hab hcontOn'
    have h0mem' : (0 : ℝ) ∈ Set.Icc ((-p).eval a) ((-p).eval b) := by
      -- (-p).eval a = - p.eval a, (-p).eval b = - p.eval b
      -- ha_pos : 0 < p.eval a, hb_neg : p.eval b < 0
      -- ⇒ -p.eval a < 0 < -p.eval b ⇒ 0 ∈ [-(p a), -(p b)]
      simp only [eval_neg, Set.mem_Icc, Left.neg_nonpos_iff, Left.nonneg_neg_iff]
      exact ⟨ Std.le_of_lt ha_pos, Std.le_of_lt hb_neg ⟩
    rcases hIVT' h0mem' with ⟨c, _hcab, hc0⟩
    -- (-p).eval c = 0 ⇒ p.eval c = 0
    exact ⟨c, by simpa [eval_neg] using hc0⟩






/-
문제 22. 최고차항의 계수가 1인 삼차함수 f(x)가 다음 조건을 만족시킨다.
  (가) 함수 f(x)에 대하여 f(k-1)f(k+1) < 0 을 만족시키는 정수 k는 존재하지 않는다.
  (나) f'(-1/4) = -1/4, f'(1/4) < 0
일 때, f(8)의 값을 구하시오.

Problem 22. A cubic function f(x) with a leading coefficient of 1 satisfies the following conditions.
  (a) For the function f(x), there are no integers k such that f(k-1)f(k+1) < 0.
  (b) f'(-1/4) = -1/4 and f'(1/4) < 0.
Find the value of f(8).
-/

example
    -- Let f be a real polynomial.
    -- f(x)는 최고차항의 계수가 1인 3차 함수이다.
    (f : Cubic ℝ)
    -- (g : Polynomial ℝ)
    -- (hg : g.degree = 3)
    (h_monic : f.a = 1)

    -- For any integer k, f(k-1)f(k+1) is not negative.
    -- f(k-1)f(k+1) < 0 을 만족시키는 정수 k는 존재하지 않는다.
    (h_sign_cond : ∀ k : ℤ, (f.toPoly.eval ((k :ℝ) - 1)) * (f.toPoly.eval ((k :ℝ) + 1)) ≥ 0)

    -- Derivative conditions.
    -- f'(-1/4) = -1/4, f'(1/4) < 0
    (h_deriv1 : (derivative f.toPoly).eval (-1/4) = -1/4)
    (h_deriv2 : (derivative f.toPoly).eval (1/4) < 0) :

    -- Find the value of f(8).
    -- f(8)의 값을 구하시오.
    f.toPoly.eval 8 = 483 := by
  -- [Step 1: Core Insight - Deduce roots from conditions via Case Analysis]
  have h_roots_are_0_and_1 : f.toPoly.eval 0 = 0 ∧ f.toPoly.eval 1 = 0 := by
    let num_roots := f.toPoly.roots.toFinset.card
    have h_le : num_roots ≤ 3 := Cubic.card_roots_le
    have deg_f_eq_3 : f.toPoly.natDegree = 3 := by
      apply Cubic.natDegree_of_a_ne_zero
      exact ne_zero_of_eq_one h_monic
    cases h_card_val : num_roots with
    | zero =>
      -- Case 0: 실근이 0개인 경우 — 모순
      -- Cubic은 홀수차이므로 반드시 실근이 하나 이상 존재.
      have deg_f_odd : Odd (f.toPoly.natDegree) := by
        rw [deg_f_eq_3]
        exact (by decide : Odd 3)
      obtain ⟨x, hx⟩ := exists_root_of_odd_degree deg_f_odd
      exfalso
      have : x ∈ f.toPoly.roots.toFinset := by
        refine Multiset.mem_toFinset.mpr ?_;
        refine (mem_roots_iff_aeval_eq_zero ?_).mpr hx
        refine Cubic.ne_zero_of_a_ne_zero ?_
        exact ne_zero_of_eq_one h_monic
      have h_empty : f.toPoly.roots.toFinset = ∅ := by
        apply Finset.card_eq_zero.mp
        simp only [h_card_val, num_roots]
      simpa [h_empty]
    | succ n => -- 실근이 1개 이상인 경우 (n+1)
      cases n with
      | zero =>
        exfalso
        have h_one_root : f.toPoly.roots.toFinset.card = 1 := by exact h_card_val
        obtain ⟨α, hα_singleton⟩ := Finset.card_eq_one.mp h_one_root
        have h_pos : f.a > 0 := by rw [h_monic]; exact Real.zero_lt_one
        have h_sign := sign_of_cubic_with_one_root f h_pos hα_singleton
        by_cases h_α_int : ∃ k : ℤ, α = k
        · obtain ⟨k, hk⟩ := h_α_int
          specialize h_sign_cond k
          have h_km1_neg : f.toPoly.eval (k - 1 : ℝ) < 0 := by
            apply h_sign.1; rw [hk]; simp only [sub_lt_self_iff, zero_lt_one]
          have h_kp1_pos : 0 < f.toPoly.eval (k + 1 : ℝ) := by
            apply h_sign.2; rw [hk]; simp only [gt_iff_lt, lt_add_iff_pos_right, zero_lt_one]
          have : (f.toPoly.eval (k - 1 : ℝ)) * (f.toPoly.eval (k + 1 : ℝ)) < 0 := mul_neg_of_neg_of_pos h_km1_neg h_kp1_pos
          linarith

        -- α가 정수가 아닌 경우.
        -- m = ⌊α⌋ 이라 정의하면, m < α < m+1.
        let m : ℤ := ⌊α⌋
        have hm : (m : ℝ) < α ∧ α < (m : ℝ) + 1 := by
          constructor
          · apply lt_of_le_of_ne (Int.floor_le α)
            simp only [not_exists] at h_α_int
            exact fun a ↦ h_α_int ⌊α⌋ (id (Eq.symm a))
          · exact Int.lt_floor_add_one α
        -- 조건 (가)에 k = m+1 을 대입한다: f(m)f(m+2) ≥ 0
        specialize h_sign_cond (m + 1)
        -- f(m)의 부호는 음수이다.
        have h_fm_neg : f.toPoly.eval ↑m < 0 := h_sign.1 ↑m hm.1
        -- f(m+2)의 부호는 양수이다.
        have h_fm2_pos : 0 < f.toPoly.eval (m + 2 : ℝ) := by
          apply h_sign.2; linarith [hm.2]

        -- 따라서 f(m)f(m+2) < 0 이므로 모순이다.
        have : (f.toPoly.eval ↑m) * (f.toPoly.eval (m + 2 : ℝ)) < 0 := mul_neg_of_neg_of_pos h_fm_neg h_fm2_pos
        simp only [Int.cast_add] at h_sign_cond
        nth_rw 2 3 [←Int.cast_one] at h_sign_cond
        rw [add_sub_cancel_right, add_assoc, ←Int.cast_add] at h_sign_cond
        simp only [Int.reduceAdd, Int.cast_ofNat] at h_sign_cond
        linarith
      | succ n => sorry



    -- 위의 모든 경우를 종합하면, 3차 함수는 반드시 3개의 실근을 가져야 하며, 그 중 두 개는 0과 1이다.
    -- (This part would formally combine the results of the case analysis)
  have h_root0 : f.toPoly.eval 0 = 0 := h_roots_are_0_and_1.left
  have h_root1 : f.toPoly.eval 1 = 0 := h_roots_are_0_and_1.right

  -- [Step 2: Determine Coefficients from Roots]
  -- f(0) = 0 조건으로부터 상수항 d가 0임을 알 수 있다.
  have hd_zero : f.d = 0 := by
    simp [Cubic.toPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X] at h_root0
    exact h_root0

  -- f(1) = 0 조건과 f.a=1, f.d=0을 이용하여 계수 b와 c의 관계식을 찾는다.
  -- f(1) = a + b + c + d = 0  =>  1 + b + c + 0 = 0  =>  c = -1 - b
  have hc_rel : f.c = -1 - f.b := by
    simp [Cubic.toPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X] at h_root1
    rw [h_monic, hd_zero] at h_root1
    linarith

  -- [Step 3: Determine Coefficients from Derivative Condition]
  -- f'(x)를 계산하고 f'(-1/4)=-1/4 조건을 이용해 b의 값을 찾는다.
  have h_deriv_form : derivative f.toPoly = 3 * C f.a * X^2 + 2 * C f.b * X + C f.c := by
    simp only [Cubic.toPoly, derivative_add, derivative_mul, derivative_C, zero_mul, derivative_pow,
      Nat.cast_ofNat, Nat.add_one_sub_one, derivative_X, mul_one, zero_add, pow_one, add_zero,
      add_left_inj]
    rw [h_monic, map_one, one_mul, mul_one]
    rw [←mul_assoc, mul_comm (C f.b)]
    congr

  have hb : f.b = -3/8 := by
    -- Substitute f.a=1 and c=-1-b into the derivative expression and evaluate at -1/4.
    -- 3*(-1/4)² + 2*b*(-1/4) + c = -1/4
    -- 3/16 - b/2 + (-1 - b) = -1/4
    -- -13/16 - (3/2)b = -4/16  =>  (3/2)b = -9/16  =>  b = -3/8
    rw [h_deriv_form, h_monic, hc_rel] at h_deriv1
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at h_deriv1
    field_simp at h_deriv1
    simp only [one_div, eval_ofNat] at h_deriv1
    linarith

  -- 위에서 구한 b의 값을 이용해 c의 값을 찾는다.
  have hc : f.c = -5/8 := by
    rw [hc_rel, hb]
    norm_num

  -- [Step 4: Final Calculation]
  -- 모든 계수가 결정되었으므로 f(8)의 값을 계산한다.
  -- f(x) = x³ - (3/8)x² - (5/8)x
  simp only [Cubic.toPoly, h_monic, hb, hc, hd_zero, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  norm_num -- Automates the final calculation: 8^3 - (3/8)*8^2 - (5/8)*8 = 512 - 24 - 5 = 483
