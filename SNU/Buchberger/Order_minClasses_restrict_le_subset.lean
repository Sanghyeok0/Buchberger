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

/--
#### Lemma `minClasses_restrict_le_subset`

Let `N ⊆ M` and let `a ∈ N`. Consider the restricted subset

`Nₐ := { d ∈ N | d ≤ a }`.

Then every **min–class** of `Nₐ` is also a **min–class** of `N`, i.e.

`minClasses Nₐ ⊆ minClasses N`.
-/
lemma minClasses_restrict_le_subset {N : Set M} {a : M} {_ : a ∈ N} :
  minClasses { d | d ∈ N ∧ d ≤ a } ⊆ minClasses N := by
  intro c h
  rcases h with ⟨d, hd_min, rfl⟩
  rcases hd_min with ⟨⟨hdN, hda⟩, hmin'⟩
  simp only [Set.mem_setOf_eq, and_imp] at hmin'
  simp only [Set.mem_setOf_eq]
  use d
  constructor
  · show d ∈ N ∧ ∀ x ∈ N, ¬x < d
    constructor
    · exact hdN
    · show ∀ x ∈ N, ¬x < d
      intro x hxN hlt
      by_cases hxa : x ≤ a
      · exact hmin' x hxN hxa hlt
      · exact hmin' x hxN (by apply le_trans (by exact le_of_lt hlt) hda) hlt
  · ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · -- (⊆)
      rintro ⟨⟨hxN, _⟩, hequiv⟩
      exact ⟨hxN, hequiv⟩
    · -- (⊇)
      rintro ⟨hxN, hequiv⟩
      have hxd : x ≤ d := hequiv.1
      have hxa : x ≤ a := le_trans hxd hda
      exact ⟨⟨hxN, hxa⟩, hequiv⟩
