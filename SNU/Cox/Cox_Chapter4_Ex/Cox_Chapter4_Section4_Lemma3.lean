import Mathlib.RingTheory.Nullstellensatz
import SNU.Cox.Cox_Chapter4.Cox_Chapter4_Section3
import SNU.Cox.Cox_Chapter4_Ex.Cox_Chapter4_Section4_Lemma_append

namespace MvPolynomial

variable {σ k : Type*} [Field k]

-- zariskiClosure
def zariskiClosure (S : Set (σ → k)) : Set (σ → k) :=
  zeroLocus k (vanishingIdeal k S)

/--
Lemma 3 (i). I(S̄) = I(S).
-/
lemma vanishingIdeal_zariskiClosure (S : Set (σ → k)) :
    vanishingIdeal k (zariskiClosure S) = vanishingIdeal k S := by
  rw [zariskiClosure]
  rw [le_antisymm_iff]
  constructor
  · apply vanishingIdeal_anti_mono
    exact zeroLocus_vanishingIdeal_le S
  · exact le_vanishingIdeal_zeroLocus (vanishingIdeal k S)

/--
Lemma 3 (ii). If S ⊆ T, then S̄ ⊆ T̄.
-/
theorem zariskiClosure_mono {S T : Set (σ → k)} (h : S ⊆ T) :
    zariskiClosure S ⊆ zariskiClosure T := by
  unfold zariskiClosure
  apply zeroLocus_anti_mono
  apply vanishingIdeal_anti_mono
  exact h

/--
Lemma 3 (iii). `S̄ ∪ T̄ = (S ∪ T)̄ `.
Note: Zariski closure distributes over finite unions.
-/
theorem zariskiClosure_union (S T : Set (σ → k)) :
    zariskiClosure (S ∪ T) = zariskiClosure S ∪ zariskiClosure T := by
  classical
  unfold zariskiClosure
  simpa only [vanishingIdeal_union] using
    (zeroLocus_inf (k := k) (I := vanishingIdeal k S) (J := vanishingIdeal k T))
