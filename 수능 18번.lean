import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

open BigOperators

/-
18. 두 수열 {aₙ}, {bₙ}에 대하여

      10          10
     ∑ aₖ =      ∑ (2bₖ - 1),
     k=1         k=1

      10
     ∑ (3aₖ + bₖ) = 33
     k=1

일 때,  10
       ∑ bₖ 의 값을 구하여라. [3점]
       k=1
-/
example (a b : ℕ → ℝ)
  (h1 :
    ∑ k ∈ Finset.range 10, a (k + 1)
      = ∑ k ∈ Finset.range 10, (2 * b (k + 1) - 1))
  (h2 :
    ∑ k ∈ Finset.range 10, (3 * a (k + 1) + b (k + 1)) = 33) :
  ∑ k ∈ Finset.range 10, b (k + 1) = 9 := by
  sorry
