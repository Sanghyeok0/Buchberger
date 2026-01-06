import Mathlib.RingTheory.Nullstellensatz

namespace MvPolynomial

variable {σ k : Type*} [Field k]

/--
Cox–Little–O'Shea, Ch.4 §3, Theorem 4.
`𝐕(I + J) = 𝐕(I) ∩ 𝐕(J)`.
The affine algebraic set defined by the sum of two ideals is the intersection of their affine algebraic sets.
-/
theorem zeroLocus_sup (I J : Ideal (MvPolynomial σ k)) :
    zeroLocus k (I ⊔ J) = zeroLocus k I ∩ zeroLocus k J := by
  ext a
  simp only [mem_zeroLocus_iff, Set.mem_inter_iff]
  constructor
  · -- (⊆ 방향): If a ∈ 𝐕(I+J), then a ∈ 𝐕(I) and a ∈ 𝐕(J).
    intro h
    constructor
    · -- a ∈ 𝐕(I)
      intro p hp
      apply h
      exact Submodule.mem_sup_left hp
    · -- a ∈ 𝐕(J)
      intro p hp
      apply h
      exact Submodule.mem_sup_right hp
  · -- (⊇ 방향): If a ∈ 𝐕(I) and a ∈ 𝐕(J), then a ∈ 𝐕(I+J).
    rintro ⟨hI, hJ⟩ p hp_mem_I_plus_J
    rw [Submodule.mem_sup] at hp_mem_I_plus_J
    rcases hp_mem_I_plus_J with ⟨f, hf, g, hg, rfl⟩
    rw [map_add]
    -- f(a) = 0 (because f ∈ I)
    rw [hI f hf]
    -- g(a) = 0 (because g ∈ J)
    rw [hJ g hg]
    -- 0 + 0 = 0
    rw [add_zero]

  -- or you can just use zeroLocus_vanishingIdeal_galoisConnection.l_sup
