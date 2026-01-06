import Mathlib.RingTheory.Ideal.Basic

/--
Ch.4 §1, Exercise 3.
Prove that `{0}` and `k` are the only ideals of a field `k`.
-/
example (k : Type*) [Field k] (I : Ideal k) :
    I = ⊥ ∨ I = ⊤ := Ideal.eq_bot_or_top I
