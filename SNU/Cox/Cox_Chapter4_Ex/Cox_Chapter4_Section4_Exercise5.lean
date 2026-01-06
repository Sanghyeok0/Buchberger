import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

namespace MvPolynomial

variable {σ k : Type*} [Field k]

/--
Cox Ch.4 §5, Exercise 5 (finite generating set form).

If `s` is a finite set of generators (nonempty), then
`(Ideal.span s)^(s.card*M) ≤ Ideal.span (s^M)`.
Here `s^M` means the image `{ g^M | g ∈ s }`.
-/
theorem span_pow_card_mul_le_span_image_pow
  {s : Finset (MvPolynomial σ k)} (M : ℕ) (hs : s.Nonempty):
    (Ideal.span (s : Set (MvPolynomial σ k))) ^ (s.card * M)
      ≤ Ideal.span ((fun g : MvPolynomial σ k => g ^ M) '' (s : Set (MvPolynomial σ k))) := by sorry

/--
Textbook phrasing: if `J = ⟨g₁,…,g_s⟩` via a finite generating finset `s`,
then `J^(s*M) ≤ ⟨g₁^M,…,g_s^M⟩`.
-/
theorem pow_card_mul_le_span_powers_of_eq_span
  {J : Ideal (MvPolynomial σ k)}
  {s : Finset (MvPolynomial σ k)} (M : ℕ)
  (hs : s.Nonempty)
  (hJ : Ideal.span (s : Set (MvPolynomial σ k)) = J) :
    J ^ (s.card * M)
      ≤ Ideal.span ((fun g : MvPolynomial σ k => g ^ M) '' (s : Set (MvPolynomial σ k))) := by
  -- just rewrite using `hJ` and apply the lemma above
  simpa [hJ] using (span_pow_card_mul_le_span_image_pow (σ := σ) (k := k) M hs)

end MvPolynomial
