import Mathlib.Order.WellQuasiOrder

variable {M : Type*} [Preorder M]

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

/--
**Lemma (iii) ⇒ (i): finiteness and nonemptiness of min‑classes implies Dickson Property.**
Shows that if for every nonempty (N : Set M) the set minClasses N is finite and nonempty
(Condition iii), then every subset N has a finite basis (Condition i).
-/
lemma finite_minClasses_implies_hasDicksonProperty
  (h : ∀ N : Set M, N.Nonempty → (minClasses N).Finite ∧ (minClasses N).Nonempty) :
  HasDicksonProperty M := by
  classical
  letI : Setoid M := AntisymmRel.setoid M (· ≤ ·)

  intro N
  by_cases hN : N.Nonempty
  · obtain ⟨hfin, hnonempty⟩ := h N hN
    haveI : Fintype (minClasses N) := hfin.fintype
    let S : Finset (Set M) := (minClasses N).toFinset

    have pick :
        ∀ C, C ∈ S → ∃ a, a ∈ MinimalElements N ∧ C = { x ∈ N | x ≈ a } := by
      intro C hCS
      have hC_toFinset : C ∈ (minClasses N).toFinset := by
        simpa only using hCS
      have hC : C ∈ minClasses N := (Set.mem_toFinset).1 hC_toFinset
      rcases hC with ⟨a, haMin, rfl⟩
      exact ⟨a, haMin, rfl⟩

    choose rep rep_spec using pick

    let rep' : ↥S → M := fun x => rep x.1 x.2
    let B : Set M := Set.range rep'

    refine ⟨B, ?_, ?_⟩
    · -- B.Finite
      have : B.Finite := by
        simpa only using (Set.finite_range rep')
      exact this
    · constructor
      · -- B ⊆ N
        intro b hb
        rcases hb with ⟨x, rfl⟩
        have hxMin : rep x.1 x.2 ∈ MinimalElements N := (rep_spec x.1 x.2).1
        have hxMin' :
            rep x.1 x.2 ∈ N ∧ ∀ y ∈ N, ¬ y < rep x.1 x.2 := by
          simpa only [MinimalElements, Set.mem_setOf_eq] using hxMin
        exact hxMin'.1
      · -- ∀ a ∈ N, ∃ b ∈ B, b ≤ a
        intro a ha
        let N' : Set M := { x | x ∈ N ∧ x ≤ a }
        have hN' : N'.Nonempty := ⟨a, ⟨ha, le_rfl⟩⟩
        obtain ⟨hfin', hnonempty'⟩ := h N' hN'
        rcases hnonempty' with ⟨C0, hC0⟩

        have hsub :
            minClasses { d | d ∈ N ∧ d ≤ a } ⊆ minClasses N := by
            apply minClasses_restrict_le_subset (M := M) (N := N) (a := a)
            exact ha

        have hC0N : C0 ∈ minClasses N := by
          have : C0 ∈ minClasses { d | d ∈ N ∧ d ≤ a } := by
            simpa only using hC0
          exact hsub this

        have hC0S : C0 ∈ S := by
          have : C0 ∈ (minClasses N).toFinset := (Set.mem_toFinset).2 hC0N
          simpa only using this

        let b : M := rep C0 hC0S
        refine ⟨b, ?_, ?_⟩
        · -- b ∈ B
          refine ⟨⟨C0, hC0S⟩, rfl⟩
        · -- b ≤ a
          have hbMin : b ∈ MinimalElements N := by
            simpa only using (rep_spec C0 hC0S).1
          have hbMin' : b ∈ N ∧ ∀ y ∈ N, ¬ y < b := by
            simpa only [MinimalElements, Set.mem_setOf_eq] using hbMin

          have hbC0 : b ∈ C0 := by
            have hEq : C0 = { x ∈ N | x ≈ b } := by
              simpa only using (rep_spec C0 hC0S).2
            rw [hEq]
            refine ⟨hbMin'.1, ?_⟩
            show b ≤ b ∧ b ≤ b
            exact ⟨le_rfl, le_rfl⟩

          have hC0subset : C0 ⊆ N' := by
            rcases hC0 with ⟨d, hdMin, rfl⟩
            intro x hx
            exact hx.1

          have hbN' : b ∈ N' := hC0subset hbC0
          exact hbN'.2
  · -- N = ∅
    refine ⟨(∅ : Set M), ?_, ?_⟩
    · simpa only using (Set.finite_empty : (∅ : Set M).Finite)
    · constructor
      · simp only [Set.empty_subset]
      · intro a ha
        exfalso
        exact hN ⟨a, ha⟩

/--
**Lemma (i) ⇒ (ii): A poset with the Dickson property is well‐quasi‐ordered.**
-/
theorem HasDicksonProperty.to_wellQuasiOrderedLE
  (h : HasDicksonProperty M) :
    WellQuasiOrderedLE M := by
  refine { wqo := ?_ }
  dsimp only [WellQuasiOrdered]; intro f
  -- 1) Let N = range f, apply Dickson
  let N : Set M := Set.range f
  obtain ⟨B, hBfin, ⟨hBsub, hbasis⟩⟩ := h N
  -- 2) Turn B into a Finset: we need a concrete `Fintype B`.
  haveI : Fintype B := Set.Finite.fintype hBfin
  --let Bfin := @Set.toFinset M B (by exact hBfin.fintype)
  -- 3) From B ⊆ range f get an index‐function
  have hBfin_inx: ∀ b ∈ B.toFinset, ∃ i : ℕ, f i = b:= by
    have : ∀ b ∈ B.toFinset, b ∈ B := by
      intro b
      intro hb_in_Bfin
      exact Set.mem_toFinset.mp hb_in_Bfin
    exact fun b a ↦ hBsub (this b a)
  choose index h_index using hBfin_inx
  -- 4) Collect all these indices into a finite set and pick one larger
  let Bfinat := B.toFinset.attach
  let Bfin_inx  : Finset ℕ := Bfinat.image fun x => index x.1 x.2
  let j : ℕ := Bfin_inx.sup id + 1
  have hj : ∀ i ∈ Bfin_inx, i < j := by
    intro i hi
    simp only [j]
    apply Nat.lt_succ_of_le
    apply Finset.le_sup hi
  -- 5) Now `f j ∈ N`, cover it by some `b ∈ B`
  have fjN : f j ∈ N := by exact Set.mem_range_self j
  obtain ⟨b₀, hb₀B, hle⟩ := hbasis (f j) fjN
  -- `b₀ ∈ B`, hence in `Bfin`
  have hb₀fin : b₀ ∈ B.toFinset := by exact Set.mem_toFinset.mpr hb₀B
  let i₀ : ℕ := index b₀ hb₀fin
  let x₀ : Subtype _ := ⟨b₀, hb₀fin⟩
  have hx₀ : x₀ ∈ Bfinat := by exact Finset.mem_attach B.toFinset x₀
  have hi₀j : i₀ ∈ Bfin_inx := by
     exact Finset.mem_image_of_mem _ hx₀
  have hi₀_lt_j : i₀ < j := hj _ hi₀j
  have fi : f i₀ = b₀ := h_index b₀ hb₀fin
  exact ⟨i₀, j, hi₀_lt_j, fi.symm ▸ hle⟩

/--
**(ii) ⇒ (iii): A Well Quasi-Ordered preorder has only finitely many, but at least one, min‑classes in any nonempty subset.**
-/
theorem WellQuasiOrderedLE.minClasses_finite_and_nonempty
  (h_wqo : WellQuasiOrderedLE M) :
  ∀ N : Set M, N.Nonempty → (minClasses (M := M) N).Finite ∧ (minClasses (M := M) N).Nonempty := by
  -- Fix the setoid `≈` (the antisymmetry equivalence) so that later `simp` steps behave robustly.
  letI : Setoid M := AntisymmRel.setoid M (· ≤ ·)
  -- Also register the WQO assumption as an instance, so we can use instance-based lemmas if needed.
  letI : WellQuasiOrderedLE M := h_wqo

  intro N hN
  let QN : Set (Set M) := minClasses (M := M) N
  constructor

  · -- (finite): assume `QN` is infinite and derive a contradiction.
    by_contra h_not_fin
    have QN_inf : QN.Infinite := h_not_fin

    -- 1) Obtain an embedding ℕ ↪ QN.
    let emb : ℕ ↪ Subtype QN := Set.Infinite.natEmbedding _ QN_inf

    -- 2) Turn that into a genuine sequence ℕ → Set M (a sequence of pairwise distinct min-class sets).
    let g_sets : ℕ → Set M := fun n => (emb n).1

    have inj_sets : Function.Injective g_sets := by
      intro i j hij
      have : emb i = emb j := Subtype.ext hij
      exact emb.injective this

    have mem_sets : ∀ n, g_sets n ∈ QN := fun n => (emb n).2

    -- 3) Each set in `QN` is, by definition, of the form {x ∈ N | x ≈ a}; choose such a representative `a`.
    have rep_exists :
        ∀ n, ∃ a, a ∈ MinimalElements N ∧ g_sets n = { x ∈ N | x ≈ a } := by
      intro n
      have : g_sets n ∈ minClasses (M := M) N := by
        simpa only using mem_sets n
      simpa only [minClasses, Set.mem_setOf_eq] using this

    choose g hg_min hg_set using rep_exists
    -- hg_min : ∀ (n : ℕ), g n ∈ MinimalElements N
    -- hg_set : ∀ (n : ℕ), g_sets n = {x | x ∈ N ∧ x ≈ g n}

    have g_in_N : ∀ n, g n ∈ N := by
      intro n
      have hn : g n ∈ N ∧ ∀ b ∈ N, ¬ b < g n := by
        simpa only [MinimalElements, Set.mem_setOf_eq] using hg_min n
      exact hn.1

    have g_minimal : ∀ n x, x ∈ N → ¬ x < g n := by
      intro n x hxN
      have hn : g n ∈ N ∧ ∀ b ∈ N, ¬ b < g n := by
        simpa only [MinimalElements, Set.mem_setOf_eq] using hg_min n
      exact hn.2 x hxN

    -- 4) Auxiliary lemma: if a ≈ b, then the corresponding equivalence-class subsets of N coincide.
    have set_eq_of_equiv {a b : M} (hab : a ≈ b) :
        { x ∈ N | x ≈ a } = { x ∈ N | x ≈ b } := by
      ext x
      constructor
      · rintro ⟨hxN, hxa⟩
        exact ⟨hxN, Setoid.trans hxa hab⟩
      · rintro ⟨hxN, hxb⟩
        exact ⟨hxN, Setoid.trans hxb (Setoid.symm hab)⟩

    -- 5) To relate distinct min-class *sets* to distinct quotient classes,
    --    pass to gQ : ℕ → Antisymmetrization.
    let gQ : ℕ → Antisymmetrization M (· ≤ ·) :=
      fun n => toAntisymmetrization (· ≤ ·) (g n)

    have inj_gQ : Function.Injective gQ := by
      intro i j hijQ
      -- If the quotient classes are equal, then the chosen representatives are equivalent (≈).
      have hab : g i ≈ g j := by
        exact Quotient.exact hijQ
      -- Then the corresponding class subsets are equal, hence i = j by injectivity of `g_sets`.
      have hset : g_sets i = g_sets j := by
        calc
          g_sets i = { x ∈ N | x ≈ g i } := hg_set i
          _ = { x ∈ N | x ≈ g j } := set_eq_of_equiv hab
          _ = g_sets j := (hg_set j).symm
      exact inj_sets hset

    -- 6) Apply the WQO property to the actual sequence g : ℕ → M.
    have ⟨i, j, hij, hle⟩ := h_wqo.wqo g
    have hle' : g i ≤ g j := by simpa using hle

    -- 7) Produce a strict inequality in the quotient, contradicting minimality of g j.
    have hQle : gQ i ≤ gQ j := hle'

    have hQne : gQ i ≠ gQ j := by
      intro hEq
      exact (Nat.ne_of_lt hij) (inj_gQ hEq)

    have hQlt : gQ i < gQ j := lt_of_le_of_ne hQle hQne

    -- Contradiction with the minimality of g j.
    exact (g_minimal j (g i) (g_in_N i)) hQlt

  · -- (nonempty): WQO ⇒ well-foundedness of (<) ⇒ existence of a minimal element in N.
    have hmin :
        ∃ a ∈ N, ∀ x ∈ N, ¬ x < a :=
      @WellFounded.has_min M (· < ·) (wellFounded_lt) N hN
    rcases hmin with ⟨a, haN, hamin⟩
    refine ⟨{ x ∈ N | x ≈ a }, ?_⟩
    -- This follows directly from the definition of `minClasses`.
    refine ⟨a, ?_, rfl⟩
    -- Show a ∈ MinimalElements N.
    have : a ∈ N ∧ ∀ x ∈ N, ¬ x < a := ⟨haN, hamin⟩
    simpa only [MinimalElements, Set.mem_setOf_eq] using this
