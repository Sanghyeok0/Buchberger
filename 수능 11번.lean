import Mathlib.Data.Finset.Range
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic

open BigOperators

/-
11. 공차가 0이 아닌 등차수열 {a_n}에 대하여
    |a_6| = a_8 , ∑_{k=1}^5 1 / (a_k a_{k+1}) = 5 / 96
    일 때, ∑_{k=1}^{15} a_k의 값은? [4점]
    ① 60 ② 65 ③ 70 ④ 75 ⑤ 80
-/

example (a : ℕ → ℝ) (d : ℝ)
  -- 등차수열 정의: a_n = a_1 + (n-1)d
  (h_arith : ∀ n ≥ 1, a n = a 1 + (n - 1) * d)
  (h_d_ne_zero : d ≠ 0)
  (h_cond1 : |a 6| = a 8)
  (h_cond2 : ∑ k ∈ Finset.range 5, 1 / (a (k + 1) * a (k + 2)) = 5 / 96) :
  ∑ k ∈ Finset.range 15, a (k + 1) = 60 := by
  sorry
