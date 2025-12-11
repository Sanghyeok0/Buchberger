import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Real

/-
9. 수직선 위의 두 점 P(log_5 3), Q(log_5 12)에 대하여
   선분 PQ를 m : (1-m)으로 내분하는 점의 좌표가 1일 때,
   4^m 의 값은? (단, m은 0 < m < 1인 상수이다.) [4점]
   ① 7/6  ② 4/3  ③ 3/2  ④ 5/3  ⑤ 11/6
-/

example (m : ℝ) (h_range : 0 < m ∧ m < 1)
  -- 조건: 분모가 1이므로 분자만 남김
  (h_cond : (m * logb 5 12 + (1 - m) * logb 5 3) / (m + (1 - m)) = 1) :
  Real.rpow 4 m = 5 / 3 := by
  have h_simple_cond : m * logb 5 12 + (1 - m) * logb 5 3 = 1 := by
    have h_denom : m + (1 - m) = 1 := by ring
    rw [h_denom, div_one] at h_cond
    exact h_cond

  have h_key : m * logb 5 4 = logb 5 (5 / 3) := calc
    m * logb 5 4
    = m * logb 5 (12 / 3) := by norm_num
    _ = m * (logb 5 12 - logb 5 3) := by rw [logb_div]; all_goals norm_num
    _ = (m * logb 5 12 + (1 - m) * logb 5 3) - logb 5 3 := by ring
    _ = 1 - logb 5 3 := by rw [h_simple_cond]
    _ = logb 5 5 - logb 5 3 := by rw [logb_self_eq_one]; all_goals norm_num
    _ = logb 5 (5 / 3) := by rw [logb_div]; all_goals norm_num

  -- [최종 답] 4^m 계산
  calc
    Real.rpow 4 m
    -- 1. 지수 m을 로그로 표현: m = log_5 (5/3) / log_5 4
    = Real.rpow 4 (logb 5 (5 / 3) / logb 5 4) := by
      rw [←h_key]
      field_simp
      norm_num
    -- 2. 밑 변환 공식: log_5 (5/3) / log_5 4 = log_4 (5/3)
    _ = Real.rpow 4 (logb 4 (5 / 3)) := by
      unfold logb; field_simp
    -- 3. 로그의 정의: 4^(log_4 x) = x
    _ = 5 / 3 := by
      apply rpow_logb <;> norm_num
