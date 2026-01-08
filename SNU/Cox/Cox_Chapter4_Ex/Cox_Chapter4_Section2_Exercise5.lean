import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nullstellensatz

open scoped BigOperators
open MvPolynomial

/-
Ch.4 §2, Exercise 5.

“Inclusion-reversing” means order-reversing (antitone):
  I₁ ≤ I₂  ⇒  𝐕(I₁) ⊇ 𝐕(I₂),
  V₁ ⊆ V₂ ⇒  𝐈(V₁) ⊇ 𝐈(V₂).
-/

variable {σ k : Type*} [Fintype σ] [Field k]
variable {K : Type*} [Field K] [Algebra k K]

-- Ideals ↦ affine algebraic sets is inclusion-reversing.
example {I₁ I₂ : Ideal (MvPolynomial σ k)} (h : I₁ ≤ I₂) :
    MvPolynomial.zeroLocus (K := K) I₂ ⊆ MvPolynomial.zeroLocus (K := K) I₁ := by
  simpa only [ge_iff_le, Set.le_eq_subset] using (MvPolynomial.zeroLocus_anti_mono (K := K) h)

-- Affine algebraic sets ↦ ideals is inclusion-reversing.
example {V₁ V₂ : Set (σ → K)} (h : V₁ ⊆ V₂) :
    MvPolynomial.vanishingIdeal (k := k) (K := K) V₂ ≤
      MvPolynomial.vanishingIdeal (k := k) (K := K) V₁ := by
  simpa only [ge_iff_le] using (MvPolynomial.vanishingIdeal_anti_mono (k := k) (K := K) h)

-- 𝐕(√I) = 𝐕(I).
example (I : Ideal (MvPolynomial σ k)) :
    MvPolynomial.zeroLocus (K := K) I.radical = MvPolynomial.zeroLocus (K := K) I := by
    ext x
    constructor
    · -- 𝐕(√I) ⊆ 𝐕(I) since I ≤ √I
      intro hx
      simp [MvPolynomial.zeroLocus] at hx ⊢
      intro f hf
      have : f ∈ I.radical := (Ideal.le_radical : I ≤ I.radical) hf
      exact hx f this
    · -- 𝐕(I) ⊆ 𝐕(√I)
      intro hx
      simp only [zeroLocus, Set.mem_setOf_eq] at hx ⊢
      intro f hf
      rcases (Ideal.mem_radical_iff.mp hf) with ⟨n, hn⟩

      have h0 : (aeval x) (f ^ n) = 0 := hx (f ^ n) hn
      have hpow0 : (aeval x) f = 0 ∧ ¬n = 0 := by simpa only [map_pow, pow_eq_zero_iff', ne_eq] using h0
      exact hpow0.1
