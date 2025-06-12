import Mathlib.Order.Antisymmetrization
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Basic

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
notation:50 a " →[" r:0 "] " b:50 => r a b

/-- strict step: `x ↝[r] y` means `r x y ∧ ¬ r y x`. -/
notation:50 a " ↝[" r:0 "] " b:50 => r a b ∧ ¬ r b a

/-- reflexive‐transitive closure: `x →*[r] y`. -/
notation:50 a " →*[" r:0 "] " b:50 => ReflTransGen r a b

/-- converse reflexive‐transitive closure: `x ←*[r] y`. -/
notation:50 a " ←*[" r:0 "] " b:50 => ReflTransGen (Function.swap r) a b

/-- symmetric‐closure: `x ↔[r] y`. -/
notation:50 a " ↔[" r:0 "] " b:50 => r a b ∨ r b a

/-- equivalence‐closure: `x ↔*[r] y`. -/
notation:50 a " ↔*[" r:0 "] " b:50 =>
  ReflTransGen (fun x y => r x y ∨ r y x) a b

/-- joinability: `x ↓[r] y`. -/
notation:70 a " ↓[" r:0 "] " b:70 => Relation.Join ReflTransGen r a b

/--
A “normal form” for a relation `r` is simply an `r`-maximal element.
-/
def IsNormalForm (a : M) : Prop :=
  IsRelMaximal r a

def NormalFormof [IsAsymm M r] (a b : M) : Prop :=
  IsNormalForm r b ∧ a →*[r] b

end IsAsymm


/-- **Lemma 4.73.** If `r` is well‐founded then
1. `strict r` is asymmetric, and
2. `strict r` is well‐founded. -/
theorem strict_of_wf_is_asymm (hwf : WellFounded r) :
  IsAsymm M (strict r) ∧ WellFounded (strict r):= by
  constructor
  · refine { asymm := ?_ }
    unfold strict
    simp
    exact fun a b a_1 a_2 a ↦ a_1
  · apply hwf.mono
    intros x y hxy; exact hxy.1

end Relation
