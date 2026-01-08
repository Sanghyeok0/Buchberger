import Mathlib.RingTheory.MvPolynomial.Groebner

variable {σ : Type*}
variable {m : MonomialOrder σ}
variable {k : Type*} [Field k]

open MonomialOrder

namespace MvPolynomial

noncomputable def quotients (m : MonomialOrder σ)
  {B : Set (MvPolynomial σ k)} (hB : ∀ b ∈ B, b ≠ 0) (f : MvPolynomial σ k) :
  B →₀ MvPolynomial σ k :=
  (MonomialOrder.div_set (m := m) (B := B)
      (hB := fun b hb => isUnit_leadingCoeff.2 (hB b hb))
      f).choose

noncomputable def normalForm (m : MonomialOrder σ)
  {B : Set (MvPolynomial σ k)} (hB : ∀ b ∈ B, b ≠ 0) (f : MvPolynomial σ k) :
  MvPolynomial σ k :=
  (MonomialOrder.div_set (m := m) (B := B)
      (hB := fun b hb => isUnit_leadingCoeff.2 (hB b hb))
      f).choose_spec.choose

end MvPolynomial
