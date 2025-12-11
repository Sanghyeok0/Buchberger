import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
open Nat

/-
15. 첫째항이 자연수인 수열 {aₙ}이 모든 자연수 n에 대하여

          { 2^(aₙ)     (aₙ이 홀수인 경우)
aₙ₊₁  =  {
          { (1/2) aₙ   (aₙ이 짝수인 경우)

를 만족시킬 때, a₆ + a₇ = 3이 되도록 하는 모든
a₁의 값의 합은? [4점]

    ① 139   ② 146   ③ 153   ④ 160   ⑤ 167
-/

/- 점화식 정의: a_{n+1} = 2^{a_n} (홀수), a_{n+1} = a_n / 2 (짝수) -/
def satisfiesRecurrence (a : ℕ → ℕ) : Prop :=
  ∀ n ≥ 1,
    (Odd (a n)  → a (n + 1) = 2 ^ (a n)) ∧
    (Even (a n) → a (n + 1) = a n / 2)

/- `goodFirst m` : `m` 이 어떤 수열의 첫째항 `a₁` 이고,
  그 수열이 조건을 만족하며 `a₆ + a₇ = 3` 이 되는 경우가 존재한다. -/
def goodFirst (m : ℕ) : Prop :=
  ∃ a : ℕ → ℕ,
    a 1 = m ∧
    0 < a 1 ∧                  -- a₁이 자연수
    satisfiesRecurrence a ∧
    a 6 + a 7 = 3

/- 조건을 만족하는 모든 a₁ 값들의 합은 153이다 -/
example (hfin : (Set.Finite ({m : ℕ | goodFirst m} : Set ℕ))) :
    (hfin.toFinset).sum (fun m => m) = 153 := by
  sorry
