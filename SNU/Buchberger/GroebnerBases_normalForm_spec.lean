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

/--
This lemma states that the `quotients` and `normalForm` functions satisfy the properties
guaranteed by the division algorithm.
-/
lemma normalForm_spec (m : MonomialOrder σ)
  {B : Set (MvPolynomial σ k)} (hB : ∀ b ∈ B, b ≠ 0) (f : MvPolynomial σ k) :
  let q := quotients m hB f
  let r := normalForm m hB f
  -- Property 1: The division equation
  f = (Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ k)) q) + r ∧
  -- Property 2: The degree condition
  (∀ (p : B), m.degree ((p : MvPolynomial σ k) * q p) ≼[m] m.degree f) ∧
  -- Property 3: The remainder condition (irreducibility)
  (∀ c ∈ r.support, ∀ b ∈ B, ¬ m.degree b ≤ c) := by
  simpa only [quotients, Subtype.forall, mem_support_iff, ne_eq, normalForm] using
    (MonomialOrder.div_set (m := m) (B := B) (hB := fun b hb =>
        isUnit_leadingCoeff.2 (hB b hb)) f).choose_spec.choose_spec

end MvPolynomial
