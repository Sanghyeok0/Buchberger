import Mathlib
set_option maxHeartbeats 0

open Set Real Filter Topology Polynomial BigOperators Finset

namespace Polynomial

variable {R : Type*} [Ring R] [Nontrivial R]

/-- `(-X)`의 차수는 1. -/
@[simp] lemma natDegree_neg_X : ((-X : R[X]).natDegree) = 1 := by
  -- `natDegree_neg`와 `natDegree_X`로 한 줄
  simp only [natDegree_neg, natDegree_X]

/-- 합성 `p ∘ (-X)`는 natDegree를 보존한다. -/
@[simp] lemma natDegree_comp_neg_X [NoZeroDivisors R] (p : R[X]) :
  (p.comp (-X)).natDegree = p.natDegree := by
  -- `natDegree_comp` + `natDegree_neg_X`
  simpa [natDegree_neg_X, Nat.mul_one] using
    (Polynomial.natDegree_comp (p := p) (q := (-X : R[X])))

/-- `0 < natDegree p` 이면 `0 < degree (p ∘ (-X))`. -/
lemma degree_pos_comp_neg_X_of_natDegree_pos [NoZeroDivisors R] {p : R[X]}
  (hp : 0 < p.natDegree) : 0 < (p.comp (-X)).degree := by
  have : 0 < (p.comp (-X)).natDegree := by
    simpa [natDegree_comp_neg_X (p := p)] using hp
  exact (natDegree_pos_iff_degree_pos).1 this

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
