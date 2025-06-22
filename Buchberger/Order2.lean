import Mathlib.Order.Antisymmetrization
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Max
import Mathlib.SetTheory.Ordinal.Basic

namespace Relation

variable {M : Type*}
variable (r : M → M → Prop)

/-- Diagonal (identity) relation Δ(M). -/
def diag : M → M → Prop := fun x y => x = y

/-- Inverse of a relation: `r⁻¹ a b` ↔ `r b a`. -/
def inv (a b : M) : Prop := r b a

/-- The strict part of `r`, i.e. `r \ r⁻¹`. -/
def strict (r : M → M → Prop) : M → M → Prop :=
  fun x y => r x y ∧ ¬ r y x

section IsAsymm
variable [IsAsymm M r]

/--
`a` is `r`-maximal in `N` if there is no `b ∈ N` with `a rₛ b`.
-/
def IsRelMaximalIn (N : Set M) (a : M) : Prop :=
  a ∈ N ∧ ∀ b, b ∈ N → ¬ strict r a b
-- a ∈ N ∧ ∀ b, b ∈ N → (¬ r a b ∨ r b a)

def IsRelMaximal (a : M) : Prop :=
  IsRelMaximalIn r Set.univ a

/-- one‐step reduction: `x →[r] y` means `r x y`. -/
notation:50 a " →[" r:0 "] " b:50 => r b a

/-- strict step: `x ↝[r] y` means `r x y ∧ ¬ r y x`. -/
notation:50 a " ↝[" r:0 "] " b:50 => r b a ∧ ¬ r a b

/-- reflexive‐transitive closure: `x →*[r] y`. -/
notation:50 a " →*[" r:0 "] " b:50 => ReflTransGen r b a

/-- converse reflexive‐transitive closure: `x ←*[r] y`. -/
notation:50 a " ←*[" r:0 "] " b:50 => ReflTransGen (Function.swap r) b a

/-- symmetric‐closure: `x ↔[r] y`. -/
notation:50 a " ↔[" r:0 "] " b:50 => r b a ∨ r a b

/-- equivalence‐closure: `x ↔*[r] y`. -/
notation:50 a " ↔*[" r:0 "] " b:50 =>
  ReflTransGen (fun x y => r y x ∨ r x y) b a

/-- joinability: `x ↓[r] y`. -/
notation:70 a " ↓[" r:0 "] " b:70 => Relation.Join ReflTransGen r b a

/--
A “normal form” for a relation `r` is simply an `r`-maximal element.
-/
def IsNormalForm (a : M) : Prop :=
  IsRelMaximal r a

def NormalFormof [IsAsymm M r] (a₁ a₀ : M) : Prop :=
  IsNormalForm r a₁ ∧ a₀ →*[r] a₁

end IsAsymm


/-- **Lemma 4.73.** If `r` is well‐founded then
1. `strict r` is asymmetric, and
2. `strict r` is well‐founded. -/
theorem strict_is_asymm (r : M → M → Prop) : IsAsymm M (strict r) :=
  ⟨fun a b h1 h2 => h1.2 h2.1⟩

namespace WellFounded
variable {r} in
theorem strict_is_wf (hwf : WellFounded r) : WellFounded (Relation.strict r) :=
  hwf.mono fun _ _ h' => h'.1
end WellFounded

section LinearOrder
variable [LinearOrder M]
variable [IsLinearOrder M r]
/--
“Max‐first” order on finite subsets of `M`.
1.  If `A.max = none` (i.e. `A = ∅`), then `A ≤ᴹ B`.
2.  Else if `B.max = none` (i.e. `B = ∅`), then `A ≤ᴹ B` is false.
3.  Otherwise compare `mA = max A` and `mB = max B`.
   - If `mA < mB` then `A ≤ᴹ B`.
   - If `mB < mA` then false.
   - If `mA = mB` then recurse on `A.erase mA ≤ᴹ B.erase mB`.
-/
partial def Finset.maxSetOrder : Finset M → Finset M → Prop
| A, B =>
  match A.max with
  | none    => True
  | some mA =>
    match B.max with
    | none    => False
    | some mB =>
      if mA < mB then True
      else if mB < mA then False
      else maxSetOrder (A.erase mA) (B.erase mB)
-- termination_by _ A B => A.card
notation:50 A " ≤' " B => Finset.maxSetOrder A B

lemma maxSetOrder_LinearOrder : IsLinearOrder (Finset M) Finset.maxSetOrder := by sorry

variable [IsWellOrder M r] in
theorem maxSetOrder_wellOrder : IsWellOrder (Finset M) Finset.maxSetOrder := by sorry

end LinearOrder
end Relation
