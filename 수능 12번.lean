import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Real MeasureTheory Set

/-
12. 함수 f(x) = 1/9 x(x-6)(x-9)와 실수 t(0 < t < 6)에 대하여
    함수 g(x)는
    g(x) = f(x)       (x < t)
           -(x-t)+f(t) (x ≥ t)
    이다. 함수 y=g(x)의 그래프와 x축으로 둘러싸인 영역의
    넓이의 최댓값은? [4점]
    ① 125/4 ② 127/4 ③ 129/4 ④ 131/4 ⑤ 133/4
-/

noncomputable def f (x : ℝ) : ℝ := (1/9) * x * (x - 6) * (x - 9)

-- g(x)와 x축으로 둘러싸인 넓이 함수 S(t)
-- S(t) = ∫_0^t f(x) dx + 1/2 * f(t)^2
noncomputable def S (t : ℝ) : ℝ := (∫ x in 0..t, f x) + (1/2) * (f t)^2

example :
  IsLocalMaxOn S (Set.Ioo (0 : ℝ) 6) 3 ∧ S 3 = 129 / 4 := by
  sorry
