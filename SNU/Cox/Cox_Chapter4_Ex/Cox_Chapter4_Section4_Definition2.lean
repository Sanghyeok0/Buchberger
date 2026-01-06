import Mathlib.RingTheory.Nullstellensatz

namespace MvPolynomial

variable {σ k : Type*} [Fintype σ] [Field k]

/--
Cox–Little–O'Shea, Ch.4 §4, Definition 2

Zariski closure of a subset `S ⊆ k^σ` (affine space),
defined as `𝐕(𝐈(S))`
-/
def zariskiClosure (S : Set (σ → k)) : Set (σ → k) :=
  zeroLocus k (vanishingIdeal k S)
