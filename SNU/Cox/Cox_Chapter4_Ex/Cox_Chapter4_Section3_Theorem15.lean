import Mathlib.RingTheory.Nullstellensatz
import SNU.Cox.Cox_Chapter4_Ex.Cox_Chapter4_Section3_Theorem7

namespace MvPolynomial

variable {σ k : Type*} [Fintype σ] [Field k]

omit [Fintype σ] in
/--
Cox–Little–O'Shea, Ch.4 §3, Theorem 15.
𝐕(I ∩ J) = 𝐕(I) ∪ 𝐕(J).
The affine algebraic set defined by the intersection of two ideals is the union of their affine algebraic set.
-/
theorem zeroLocus_inf (I J : Ideal (MvPolynomial σ k)) :
    zeroLocus k (I ⊓ J) = zeroLocus k I ∪ zeroLocus k J := by
  -- 교재의 증명 흐름에 따라 양방향 포함 관계(⊆, ⊇)로 나누어 증명합니다.
  apply le_antisymm

  · -- (⊆ 방향)
    -- "since IJ ⊆ I ∩ J, we have 𝐕(I ∩ J) ⊆ 𝐕(IJ)."
    -- "But 𝐕(IJ) = 𝐕(I) ∪ 𝐕(J) by Theorem 7"
    rw [← zeroLocus_mul]
    apply zeroLocus_anti_mono
    exact Ideal.mul_le_inf

  · -- (⊇ 방향)
    -- "Let a ∈ 𝐕(I) ∪ 𝐕(J) ... Hence a ∈ 𝐕(I ∩ J)."
    rintro x (hI | hJ)
    -- Case 1: x ∈ 𝐕(I). I ∩ J ⊆ I 이므로 x ∈ 𝐕(I ∩ J)
    · exact zeroLocus_anti_mono (inf_le_left) hI
    -- Case 2: x ∈ 𝐕(J). I ∩ J ⊆ J 이므로 x ∈ 𝐕(I ∩ J)
    · exact zeroLocus_anti_mono (inf_le_right) hJ

end MvPolynomial
