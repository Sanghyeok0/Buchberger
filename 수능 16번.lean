import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-
16. 방정식 3^(x-8) = (1/27)^x 을 만족시키는 실수 x의 값을 구하시오. [3점]
-/

example {x : ℝ}
  (h : Real.rpow 3 (x - 8) = Real.rpow (1 / 27) x) :
  x = 2 := by sorry
