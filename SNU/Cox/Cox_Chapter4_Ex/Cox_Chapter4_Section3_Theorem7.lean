import Mathlib.RingTheory.Nullstellensatz

namespace MvPolynomial

variable {σ k : Type*} [Fintype σ] [Field k]

omit [Fintype σ] in
/--
Cox–Little–O'Shea, Ch.4 §3, Theorem 7.
`V(I · J) = V(I) ∪ V(J)`.
The affine algebraic set defined by the product of two ideals is the union of their affine algebraic sets.
-/
theorem zeroLocus_mul (I J : Ideal (MvPolynomial σ k)) :
    zeroLocus k (I * J) = zeroLocus k I ∪ zeroLocus k J := by
  ext x
  simp only [mem_zeroLocus_iff, Set.mem_union]
  constructor

  -- (⊆ 방향): Let a ∈ V(I·J). ... In either event, a ∈ V(I) ∪ V(J).
  · intro h
    -- "If g(a) = 0 for all g ∈ I, then a ∈ V(I)."
    by_cases h_in_I : ∀ g ∈ I, aeval x g = 0
    · -- Case 1: 모든 g에 대해 0인 경우 -> x ∈ V(I)
      left
      exact h_in_I

    · -- Case 2: "If g(a) ≠ 0 for some g ∈ I..."
      right
      push_neg at h_in_I
      obtain ⟨g, hg_I, hg_ne_0⟩ := h_in_I

      -- "... then we must have h(a) = 0 for all h ∈ J."
      intro h_poly hh_J

      -- "Then g(a)h(a) = 0" (왜냐하면 gh ∈ I*J 이고 가정 h에 의해)
      have h_mul_zero : aeval x (g * h_poly) = 0 := by
        apply h
        apply Ideal.mul_mem_mul hg_I hh_J

      -- Field 성질에 의해 g(a)h(a) = 0 이면 g(a)=0 또는 h(a)=0
      rw [map_mul, mul_eq_zero] at h_mul_zero
      cases h_mul_zero with
      | inl h_g_zero => contradiction -- g(a) ≠ 0 이므로 모순
      | inr h_h_zero => exact h_h_zero -- 따라서 h(a) = 0 이어야 함

  · -- (⊇ 방향): If x ∈ V(I) or x ∈ V(J), then x ∈ V(I·J).
    rintro (hI | hJ) p hp
    · exact hI p (Ideal.mul_le_right hp) -- I*J ⊆ I
    · exact hJ p (Ideal.mul_le_left hp)  -- I*J ⊆ J
