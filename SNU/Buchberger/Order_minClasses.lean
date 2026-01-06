import Mathlib.Order.WellQuasiOrder

variable {M : Type*} [Preorder M]

/--
#### Minimal elements (`MinimalElements`)

Let `N ⊆ M`. An element `a ∈ N` is **minimal in `N`** if there is no `b ∈ N`
with `b < a`, where `<` is the strict part of the preorder.
-/
def MinimalElements (N : Set M) : Set M :=
  { a ∈ N | ∀ b ∈ N, ¬ (b < a) }

/--
#### Min–classes (`minClasses`)

Fix `N ⊆ M`. We use the equivalence relation `≈` induced by antisymmetry:
`a ≈ b` means `a ≤ b ∧ b ≤ a`.

A **min–class** of `N` is obtained by taking a minimal element `a ∈ MinimalElements N`
and intersecting `N` with its `≈`-equivalence class.
-/
def minClasses (N : Set M) : Set (Set M) :=
  letI : Setoid M := AntisymmRel.setoid M (· ≤ ·)
  -- Here `x ≈ a` abbreviates `x ≤ a ∧ a ≤ x`.
  { C | ∃ a ∈ MinimalElements N, C = { x ∈ N | x ≈ a } }
