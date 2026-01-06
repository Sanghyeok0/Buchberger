import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

open scoped BigOperators
open MvPolynomial

variable {σ k : Type*} [Fintype σ] [Field k]

/--
Cox–Little–O'Shea, Ch.4 §3, Exercise 12.

Let `I, J` be ideals in `k[x₁,...,xₙ]` and suppose `I ≤ √J` (i.e. `I ≤ J.radical`).
Show that `I^m ≤ J` for some integer `m > 0`.
-/
example (I J : Ideal (MvPolynomial σ k)) (hIJ : I ≤ J.radical) :
    ∃ m : ℕ, 0 < m ∧ I ^ m ≤ J := by
  have hfg : I.FG := by
    exact ((isNoetherianRing_iff_ideal_fg (MvPolynomial σ k)).1 isNoetherianRing) I

  -- This lemma is exactly the “power goes into J” statement under finite generation.
  rcases Ideal.exists_pow_le_of_le_radical_of_fg (I := I) (J := J) hIJ hfg with ⟨n, hn⟩

  -- Make the exponent positive by taking `n+1` (since powers decrease as exponent increases).
  refine ⟨n.succ, Nat.succ_pos n, ?_⟩
  exact (Ideal.pow_le_pow_right (I := I) (m := n) (n := n.succ) (Nat.le_succ n)).trans hn
