import SNU.Buchberger.Order
import Mathlib.Data.Finsupp.PWO

variable {σ : Type*}

namespace MonomialOrder
open Set

theorem Dickson_lemma {σ : Type*} [Fintype σ] :
  HasDicksonProperty (σ →₀ ℕ) := by
  apply HasDicksonProperty_iff_WellQuasiOrderedLE.mpr
  refine (wellQuasiOrderedLE_def (σ →₀ ℕ)).mpr ?_
  -- Given any sequence f : ℕ → σ →₀ ℕ, PWO gives a monotone subsequence
  intro f
  have hPWO : (Set.univ : Set (σ →₀ ℕ)).IsPWO := Finsupp.isPWO (S := Set.univ)
  obtain ⟨g, hg_mono⟩ := @hPWO.exists_monotone_subseq _ _ _ f (fun _ => mem_univ _)
  -- Take the first two indices i := g 0, j := g 1
  let i := g 0
  let j := g 1
  -- Strict‐mono of g turns 0 < 1 into i < j
  have hij : i < j := g.strictMono (Nat.zero_lt_succ 0)
  -- Monotonicity of f ∘ g at 0 ≤ 1 gives f i ≤ f j
  have hle : f i ≤ f j := by
    rw [Monotone] at hg_mono
    refine hg_mono ?_
    exact Nat.zero_le 1
  exact ⟨i, j, hij, hle⟩
