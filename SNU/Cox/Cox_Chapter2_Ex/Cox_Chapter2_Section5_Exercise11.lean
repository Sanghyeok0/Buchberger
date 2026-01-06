import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

open MvPolynomial

variable {σ : Type*} [Fintype σ]
variable {k : Type*} [Field k]
variable {m : MonomialOrder σ}

/--
Ch.2 §5, Exercise 11.

If `f ∉ ⟨X i | i : σ⟩`, then `⟨X i | i : σ⟩ + ⟨f⟩ = ⊤`,
equivalently `Ideal.span (vars ∪ {f}) = ⊤`.
-/
example
  {f : MvPolynomial σ k}
  (hf : f ∉ Ideal.span (Set.range (fun i : σ => (X i : MvPolynomial σ k)))) :
    Ideal.span ((Set.range (fun i : σ => (X i : MvPolynomial σ k))) ∪ ({f} : Set (MvPolynomial σ k)))
      = (⊤ : Ideal (MvPolynomial σ k)) := by
  sorry
