import Mathlib.Data.Set.Card
import Mathlib.Topology.MetricSpace.Pseudo.Defs

open Filter Set
open scoped Topology

/-
14. 두 자연수 a, b에 대하여 함수 f(x)는

        { 2x^3 - 6x + 1        (x ≤ 2)
f(x) =  {
        { a(x - 2)(x - b) + 9  (x > 2)

이다. 실수 t에 대하여 함수 y = f(x)의 그래프와
직선 y = t가 만나는 점의 개수를 g(t)라 하자.

    g(k) + lim_{t → k^-} g(t) + lim_{t → k^+} g(t) = 9

를 만족시키는 실수 k의 개수가 1이 되도록 하는
두 자연수 a, b의 순서쌍 (a, b)에 대하여
a + b의 최댓값은? [4점]

    ① 51   ② 52   ③ 53   ④ 54   ⑤ 55
-/

/- 두 자연수 a, b 에 대한 함수 f(x) 정의 -/
noncomputable def f (a b : ℕ) (x : ℝ) : ℝ :=
  if h : x ≤ 2 then
    2 * x^3 - 6 * x + 1
  else
    (a : ℝ) * (x - 2) * (x - (b : ℝ)) + 9

/- g(t) : y = f(x) 와 y = t 의 교점 개수 -/
noncomputable def g (a b : ℕ) (t : ℝ) : ℝ :=
  (Set.ncard {x : ℝ | f a b x = t} : ℝ)

/- goodAt a b k : 주어진 a,b 에 대해 g(k) + (좌극한) + (우극한) = 9 를 만족하는 k -/
def goodAt (a b : ℕ) (k : ℝ) : Prop :=
  ∃ L_left L_right : ℝ,
    Tendsto (g a b) (nhdsWithin k (Iio k)) (𝓝 L_left) ∧
    Tendsto (g a b) (nhdsWithin k (Ioi k)) (𝓝 L_right) ∧
    g a b k + L_left + L_right = 9

/- 문제에서 말하는 “실수 k 의 개수가 1개가 되도록 하는 (a,b)” 를
   ∃! k, goodAt a b k 로 표현 -/
def goodPair (a b : ℕ) : Prop :=
  ∃! k : ℝ, goodAt a b k

example (a b : ℕ)
  (h_nat_pos_a : 0 < a) (h_nat_pos_b : 0 < b)
  (h_good : goodPair a b)
  (h_max : ∀ a' b', goodPair a' b' → a' + b' ≤ a + b) :
  a + b = 54 := by
  sorry
