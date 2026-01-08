import SNU.Buchberger.MonomialIdeal
import Mathlib.RingTheory.MvPolynomial.Groebner

variable {σ : Type*}
variable {m : MonomialOrder σ}
variable {k : Type*} [Field k] [DecidableEq k]

open MonomialOrder

namespace MvPolynomial

variable (m) in
/--
**Gröbner basis property.**
For an ideal `I` and a finite set `G`, this means:

- `G ⊆ I`, and
- `⟨ LT(G) ⟩ = ⟨ LT(I) ⟩`,

where `LT(G) = { LT(g) | g ∈ G }` and `LT(I) = { LT(f) | f ∈ I \ {0} }`.
-/
def GroebnerBasis_prop (I : Ideal (MvPolynomial σ k)) (G : Finset (MvPolynomial σ k)) : Prop :=
  (G : Set (MvPolynomial σ k)) ⊆ I ∧
  Ideal.span ((fun g => leadingTerm m g) '' (G : Set (MvPolynomial σ k))) = leadingTermIdeal m I

end MvPolynomial
