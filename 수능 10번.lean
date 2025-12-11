import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Real MeasureTheory Set

/-
10. 시각 t=0일 때 동시에 원점을 출발하여 수직선 위를
    움직이는 두 점 P, Q의 시각 t(t≥0)에서의 속도가 각각
    v_1(t) = t^2 - 6t + 5, v_2(t) = 2t - 7
    이다. 시각 t에서의 두 점 P, Q 사이의 거리를 f(t)라 할 때,
    함수 f(t)는 구간 [0, a]에서 증가하고, 구간 [a, b]에서
    감소하고, 구간 [b, ∞)에서 증가한다. 시각 t=a에서
    t=b까지 점 Q가 움직인 거리는? (단, 0 < a < b) [4점]
    ① 15/2 ② 17/2 ③ 19/2 ④ 21/2 ⑤ 23/2
-/

noncomputable def v₁ (t : ℝ) : ℝ := t^2 - 6 * t + 5
noncomputable def v₂ (t : ℝ) : ℝ := 2 * t - 7

noncomputable def f (t : ℝ) : ℝ := |(∫ x in 0..t, v₁ x) - (∫ x in 0..t, v₂ x)|

example (a b : ℝ) (h_ord : 0 < a ∧ a < b)
  (h_inc1 : StrictMonoOn f (Icc 0 a))
  (h_dec  : StrictAntiOn f (Icc a b))
  (h_inc2 : StrictMonoOn f (Ici b)) :
  ∫ t in a..b, |v₂ t| = 17 / 2 := by
  sorry
