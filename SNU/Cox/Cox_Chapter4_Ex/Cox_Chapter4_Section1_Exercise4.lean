import Mathlib.FieldTheory.IsAlgClosed.Basic

/--
Ch.4 §1, Exercise 4.

An algebraically closed field is infinite.
-/
example (k : Type*) [Field k] [IsAlgClosed k] :
    Infinite k := IsAlgClosed.instInfinite
