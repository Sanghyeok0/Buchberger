module

public import Mathlib.Order.WellQuasiOrder

@[expose] public section

variable {M : Type*} [Preorder M]

/-!
## Reference : [Becker-Weispfenning1993]

# Formalization of Proposition 4.42

This section formalizes Proposition 4.42, which states the equivalence
of three conditions for a preorder `≤` on a set `M`:

1.  **(i)** The preorder `≤` has the Dickson property (every subset has a finite basis).
2.  **(ii)** `≤` is a Well Quasi-Order (every infinite sequence `aₙ` has `i < j` with `aᵢ ≤ aⱼ`).
3.  **(iii)** For every nonempty `N : Set M`, the set of min-classes
     `minClasses N` is finite and nonempty.
-/

variable (M) in
/--
**Definition 4.39**
The relation `≤` on `M` has the Dickson property (finite basis property).
Every subset `N` of `M` has a finite subset `B ⊆ N` such that every element
of `N` is greater than or equal to some element of `B`.
-/
def HasDicksonProperty : Prop :=
  ∀ N : Set M, ∃ B : Set M, B.Finite ∧ (B ⊆ N ∧ ∀ a ∈ N, ∃ b ∈ B, b ≤ a)

/--
#### Min–classes (`minClasses`)

Fix `N ⊆ M`. We use the equivalence relation `≈` induced by antisymmetry:
`a ≈ b` means `a ≤ b ∧ b ≤ a`.

A **min–class** of `N` is obtained by taking a minimal element
`a` satisfying `x ∈ N` and intersecting `N` with its `≈`-equivalence class.
-/
def minClasses (N : Set M) : Set (Set M) :=
  letI : Setoid M := AntisymmRel.setoid M (· ≤ ·)
  { C | ∃ a, Minimal (fun x => x ∈ N) a ∧ C = { x ∈ N | x ≈ a } }

/--
#### Lemma `minClasses_restrict_le_subset`

Let `N ⊆ M` and let `a : M`. Consider the restricted subset
`Nₐ := { d ∈ N | d ≤ a }`.
Then every **min–class** of `Nₐ` is also a **min–class** of `N`, i.e.
`minClasses Nₐ ⊆ minClasses N`.
-/
lemma minClasses_restrict_le_subset {N : Set M} {a : M} :
  minClasses { d | d ∈ N ∧ d ≤ a } ⊆ minClasses N := by
  intro c hc
  rcases hc with ⟨d, hdMin, rfl⟩
  letI : Setoid M := AntisymmRel.setoid M (· ≤ ·)
  have hdN : d ∈ N := hdMin.1.1
  have hda : d ≤ a := hdMin.1.2
  refine ⟨d, ?_, ?_⟩
  · refine ⟨hdN, ?_⟩
    intro x hxN hxd
    exact hdMin.2 ⟨hxN, le_trans hxd hda⟩ hxd
  · ext x
    constructor
    · intro hx
      rcases hx with ⟨⟨hxN, hxa⟩, hxd⟩
      exact ⟨hxN, hxd⟩
    · intro hx
      rcases hx with ⟨hxN, hxd⟩
      exact ⟨⟨hxN, le_trans hxd.1 hda⟩, hxd⟩

/--
**Lemma (iii) ⇒ (i): finiteness and nonemptiness of min-classes implies Dickson Property.**
Shows that if for every nonempty `N : Set M` the set `minClasses N` is finite and nonempty,
then every subset `N` has a finite basis.
-/
lemma finite_minClasses_implies_hasDicksonProperty
  (h : ∀ N : Set M, N.Nonempty → (minClasses N).Finite ∧ (minClasses N).Nonempty) :
  HasDicksonProperty M := by
  letI : Setoid M := AntisymmRel.setoid M (· ≤ ·)
  intro N
  by_cases hN : N.Nonempty
  · obtain ⟨hfin, hnonempty⟩ := h N hN
    haveI : Fintype (minClasses N) := hfin.fintype
    let S : Finset (Set M) := (minClasses N).toFinset
    have pick :
        ∀ C, C ∈ S → ∃ a, Minimal (fun x => x ∈ N) a ∧ C = { x ∈ N | x ≈ a } := by
      intro C hCS
      have hC : C ∈ minClasses N := (Set.mem_toFinset).1 hCS
      rcases hC with ⟨a, haMin, rfl⟩
      exact ⟨a, haMin, rfl⟩
    choose rep rep_spec using pick
    let rep' : ↥S → M := fun x => rep x.1 x.2
    let B : Set M := Set.range rep'
    refine ⟨B, Set.finite_range rep', ?_⟩
    constructor
    · -- B ⊆ N
      intro b hb
      rcases hb with ⟨x, rfl⟩
      exact (rep_spec x.1 x.2).1.1
    · -- ∀ a ∈ N, ∃ b ∈ B, b ≤ a
      intro a ha
      let N' : Set M := { x | x ∈ N ∧ x ≤ a }
      have hN' : N'.Nonempty := ⟨a, ⟨ha, le_rfl⟩⟩
      obtain ⟨_, hnonempty'⟩ := h N' hN'
      rcases hnonempty' with ⟨C0, hC0⟩
      have hsub :
          minClasses { d | d ∈ N ∧ d ≤ a } ⊆ minClasses N := by
        exact minClasses_restrict_le_subset (M := M) (N := N) (a := a)
      have hC0N : C0 ∈ minClasses N := by
        exact hsub hC0
      have hC0S : C0 ∈ S := by
        have : C0 ∈ (minClasses N).toFinset := (Set.mem_toFinset).2 hC0N
        simpa only [Set.mem_toFinset, S] using this
      let b : M := rep C0 hC0S
      refine ⟨b, ?_, ?_⟩
      · exact ⟨⟨C0, hC0S⟩, rfl⟩
      · have hbMin : Minimal (fun x => x ∈ N) b := (rep_spec C0 hC0S).1
        have hbC0 : b ∈ C0 := by
          have hEq : C0 = { x ∈ N | x ≈ b } := (rep_spec C0 hC0S).2
          rw [hEq]
          exact ⟨hbMin.1, ⟨le_rfl, le_rfl⟩⟩
        have hC0subset : C0 ⊆ N' := by
          rcases hC0 with ⟨d, hdMin, rfl⟩
          intro x hx
          exact hx.1
        have hbN' : b ∈ N' := hC0subset hbC0
        exact hbN'.2
  · -- N = ∅
    refine ⟨(∅ : Set M), ?_, ?_⟩
    · exact Set.finite_empty
    · constructor
      · simp only [Set.empty_subset]
      · intro a ha
        exact (hN ⟨a, ha⟩).elim

/--
**Lemma (i) ⇒ (ii): A preorder with the Dickson property is well‐quasi‐ordered.**
-/
theorem HasDicksonProperty.to_wellQuasiOrderedLE
  (h : HasDicksonProperty M) :
    WellQuasiOrderedLE M := by
  refine { wqo := ?_ }
  dsimp [WellQuasiOrdered]
  intro f
  let N : Set M := Set.range f
  obtain ⟨B, hBfin, ⟨hBsub, hbasis⟩⟩ := h N
  haveI : Fintype B := Set.Finite.fintype hBfin
  have hBfin_inx : ∀ b ∈ B.toFinset, ∃ i : ℕ, f i = b := by
    have : ∀ b ∈ B.toFinset, b ∈ B := by
      intro b hb
      exact Set.mem_toFinset.mp hb
    intro b hb
    exact hBsub (this b hb)
  choose index h_index using hBfin_inx
  let Bfinat := B.toFinset.attach
  let Bfin_inx : Finset ℕ := Bfinat.image fun x => index x.1 x.2
  let j : ℕ := Bfin_inx.sup id + 1
  have hj : ∀ i ∈ Bfin_inx, i < j := by
    intro i hi
    exact Nat.lt_succ_of_le (Bfin_inx.le_sup (f := id) hi)
  have fjN : f j ∈ N := Set.mem_range_self j
  obtain ⟨b₀, hb₀B, hle⟩ := hbasis (f j) fjN
  have hb₀fin : b₀ ∈ B.toFinset := Set.mem_toFinset.mpr hb₀B
  let i₀ : ℕ := index b₀ hb₀fin
  let x₀ : Subtype _ := ⟨b₀, hb₀fin⟩
  have hx₀ : x₀ ∈ Bfinat := Finset.mem_attach _ _
  have hi₀j : i₀ ∈ Bfin_inx := by
    exact Finset.mem_image_of_mem _ hx₀
  have hi₀_lt_j : i₀ < j := hj _ hi₀j
  have fi : f i₀ = b₀ := h_index b₀ hb₀fin
  exact ⟨i₀, j, hi₀_lt_j, fi.symm ▸ hle⟩

/--
**(ii) ⇒ (iii): A Well Quasi-Ordered preorder has only finitely many, but at least one, min-classes in any nonempty subset.**
-/
theorem WellQuasiOrderedLE.minClasses_finite_and_nonempty
  (h_wqo : WellQuasiOrderedLE M) :
  ∀ N : Set M, N.Nonempty → (minClasses (M := M) N).Finite ∧ (minClasses (M := M) N).Nonempty := by
  letI : Setoid M := AntisymmRel.setoid M (· ≤ ·)
  letI : WellQuasiOrderedLE M := h_wqo
  intro N hN
  let QN : Set (Set M) := minClasses (M := M) N
  constructor
  · by_contra h_not_fin
    have QN_inf : QN.Infinite := h_not_fin
    let emb : ℕ ↪ Subtype QN := Set.Infinite.natEmbedding _ QN_inf
    let g_sets : ℕ → Set M := fun n => (emb n).1
    have inj_sets : Function.Injective g_sets := by
      intro i j hij
      have : emb i = emb j := Subtype.ext hij
      exact emb.injective this
    have mem_sets : ∀ n, g_sets n ∈ QN := fun n => (emb n).2
    have rep_exists :
        ∀ n, ∃ a, Minimal (fun x => x ∈ N) a ∧ g_sets n = { x ∈ N | x ≈ a } := by
      intro n
      have : g_sets n ∈ minClasses (M := M) N := mem_sets n
      simpa only [minClasses, Set.mem_setOf_eq] using this
    choose g hg_min hg_set using rep_exists
    have g_in_N : ∀ n, g n ∈ N := by
      intro n
      exact (hg_min n).1
    let gQ : ℕ → Antisymmetrization M (fun x y : M => x ≤ y) :=
      fun n => toAntisymmetrization (r := fun x y : M => x ≤ y) (g n)
    have g_minimal :
        ∀ n b, b ∈ N →
          toAntisymmetrization (r := fun x y : M => x ≤ y) b < gQ n → False := by
      intro n b hbN hlt
      rcases (lt_iff_le_and_ne).1 hlt with ⟨hb_le, hne⟩
      have hbg : b ≤ g n := by
        simpa only [toAntisymmetrization_le_toAntisymmetrization_iff] using hb_le
      have hgb : g n ≤ b := (hg_min n).2 hbN hbg
      have hq : gQ n ≤ toAntisymmetrization (r := fun x y : M => x ≤ y) b := hgb
      exact hne (le_antisymm hb_le hq)
    have set_eq_of_equiv {a b : M} (hab : a ≈ b) :
        { x ∈ N | x ≈ a } = { x ∈ N | x ≈ b } := by
      ext x
      constructor
      · rintro ⟨hxN, hxa⟩
        exact ⟨hxN, Setoid.trans hxa hab⟩
      · rintro ⟨hxN, hxb⟩
        exact ⟨hxN, Setoid.trans hxb (Setoid.symm hab)⟩
    have inj_gQ : Function.Injective gQ := by
      intro i j hijQ
      have hab : g i ≈ g j := Quotient.exact hijQ
      have hset : g_sets i = g_sets j := by
        calc
          g_sets i = { x ∈ N | x ≈ g i } := hg_set i
          _ = { x ∈ N | x ≈ g j } := set_eq_of_equiv hab
          _ = g_sets j := (hg_set j).symm
      exact inj_sets hset
    have ⟨i, j, hij, hle⟩ := h_wqo.wqo g
    have hle' : g i ≤ g j := hle
    have hQle : gQ i ≤ gQ j := by
      simpa only [toAntisymmetrization_le_toAntisymmetrization_iff] using hle'
    have hQne : gQ i ≠ gQ j := by
      intro hEq
      exact (Nat.ne_of_lt hij) (inj_gQ hEq)
    have hQlt : gQ i < gQ j := lt_of_le_of_ne hQle hQne
    exact (g_minimal j (g i) (g_in_N i)) hQlt
  · have hmin :
        ∃ a ∈ N, ∀ x ∈ N, ¬ x < a := by
      exact @WellFounded.has_min M (· < ·) (wellFounded_lt) N hN
    rcases hmin with ⟨a, haN, hamin⟩
    refine ⟨{ x ∈ N | x ≈ a }, ?_⟩
    refine ⟨a, ?_, rfl⟩
    have haMin : Minimal (fun x => x ∈ N) a := by
      refine ⟨haN, ?_⟩
      intro x hxN hxa
      by_contra hax
      exact hamin x hxN (lt_of_le_not_ge hxa hax)
    exact haMin

/--
**Theorem (Proposition 4.42, conditions (i) and (ii)).**

For a preorder `≤` on `M`, the following are equivalent:

- **(i)** `≤` has the **Dickson property** (finite basis property):
  for every subset `N ⊆ M` there exists a finite subset `B ⊆ N` such that
  for every `a ∈ N` there exists `b ∈ B` with `b ≤ a`.

- **(ii)** `≤` is a **well quasi-order** (wqo):
  for every sequence `a : ℕ → M` there exist indices `i < j` with `a i ≤ a j`.

This theorem formalises the equivalence **(i) ↔ (ii)** from Proposition 4.42.
-/
theorem HasDicksonProperty_iff_WellQuasiOrderedLE :
    HasDicksonProperty M ↔ WellQuasiOrderedLE M := by
  constructor
  · exact HasDicksonProperty.to_wellQuasiOrderedLE
  · intro h_wqo
    apply finite_minClasses_implies_hasDicksonProperty
    exact h_wqo.minClasses_finite_and_nonempty
