import Mathlib
set_option maxHeartbeats 0

open Set Real Filter Topology Polynomial BigOperators Finset

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
    -- α와 β를 실수로 정의합니다.
    {α β : ℝ}
    -- Define the function f. / 함수 f를 정의합니다.
    (f : ℝ → ℝ := fun x ↦ (1/3) * x^3 - 2 * x^2 - 12 * x + 4)
    -- h_max: f는 α에서 극댓값을 가집니다.
    (h_max : IsLocalMax f α)
    -- h_min: f는 β에서 극솟값을 가집니다.
    (h_min : IsLocalMin f β) :
    -- 우리가 찾고자 하는 값입니다.
    β - α = 8 := by sorry
