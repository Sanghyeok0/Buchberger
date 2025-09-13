import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.Defs.Unbundled -- For def Minimal
import Mathlib.Data.Set.Card

variable {M : Type*} [Preorder M] -- M equipped with a quasi-order (preorder) ≤

/-!
## Reference : [Becker-Weispfenning1993]

# Formalization of Proposition 4.42

This section formalizes Proposition 4.42, which states the equivalence
of three conditions for a preorder `≤` on a set `M`:

1.  **(i)** `≤` has the Dickson property (every subset has a finite basis).
2.  **(ii)** `≤` is a Well Quasi‑Order (every infinite sequence `aₙ` has `i < j` with `aᵢ ≤ aⱼ`).
3.  **(iii)** For every nonempty `N : Set M`, the set of min‑classes
     `minClasses N` is finite and nonempty.

We define a predicate for (i) and show its equivalence to (ii), which is
represented by the typeclass `WellQuasiOrderedLE M`.  The equivalence is
proven by relating both to condition (iii) using Mathlib’s
`wellQuasiOrderedLE_iff`.
-/

/--
**Condition (i) of Proposition 4.42:**
The relation `≤` on `M` has the Dickson property (finite basis property).
Every subset `N` of `M` has a finite subset `B ⊆ N` such that every element
of `N` is greater than or equal to some element of `B`.
-/
def HasDicksonProperty (M : Type*) [Preorder M] : Prop :=
  ∀ N : Set M, ∃ B : Set M, B.Finite ∧ (B ⊆ N ∧ ∀ a ∈ N, ∃ b ∈ B, b ≤ a)

-- Condition (ii) is directly represented by the typeclass `WellQuasiOrderedLE M`.

/--
toAntisymmetrization (· ≤ ·) '' { a | a ∈ N ∧ ∀ x ∈ N, ¬ (x < a) }
-/
def minClasses (N : Set M) : Set (Antisymmetrization M (· ≤ ·)) :=
  toAntisymmetrization (· ≤ ·) '' { a | a ∈ N ∧ ∀ x ∈ N, ¬ (x < a) }
-- WRONG DEFINITION! : toAntisymmetrization (· ≤ ·) '' { b | Minimal (· ∈ N) b }

lemma minClasses_restrict_le_subset {N : Set M} {a : M} {_ : a ∈ N} :
  minClasses { d | d ∈ N ∧ d ≤ a } ⊆ minClasses N := by
  intro c h
  rcases h with ⟨d, hd_min, rfl⟩
  rcases hd_min with ⟨⟨hdN, hda⟩, hmin'⟩
  simp only [Set.mem_setOf_eq, and_imp] at hmin'
  simp only [minClasses, Set.mem_image, Set.mem_setOf_eq]
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
  · rfl

/--
**Lemma (iii) ⇒ (i): finiteness and nonemptiness of min‑classes implies Dickson Property.**
Shows that if for every nonempty N : Set M the set minClasses N is finite and nonempty
(Condition iii), then every subset N has a finite basis (Condition i).
-/
lemma finite_min_classes_implies_hasDicksonProperty
  (h : ∀ N : Set M, N.Nonempty → (minClasses N).Finite ∧ (minClasses N).Nonempty) :
  HasDicksonProperty M := by
  intro N
  by_cases hN : N.Nonempty
  · -- build the finite basis
    obtain ⟨hfin, hnonempty⟩ := h N hN
    haveI : Fintype (minClasses N) := hfin.fintype
    let S := (minClasses N).toFinset
    -- pick a representative from each class in S
    have pick : ∀ c ∈ S, ∃ b, b ∈ N ∧ (∀ x ∈ N, ¬(x < b)) ∧ toAntisymmetrization ((· : M) ≤ ·) b = c := by
      -- if c ∈ S then c ∈ minClasses N, so c = Quotient.mk b for some minimal b
      intro c hc
      --simp only [Set.mem_setOf_eq]
      simp [S, minClasses] at hc
      obtain ⟨x, hx⟩ := hc
      use x
      exact and_assoc.mp hx
    choose rep rep_spec using pick

    -- Turn `S` into a `Finset M` of actual reps
    let rep' (x : Subtype fun c => c ∈ S) : M := rep x.1 x.2
    let B : Set M := (fun x => rep x.1 x.2) '' S.attach.toSet
    -- S.attach : Finset { c // c ∈ S } and S.attach.toSet : Set { c // c ∈ S }

    use B
    constructor
    · show B.Finite
      exact (Set.toFinite _)
    · constructor
      · -- B ⊆ N
        show B ⊆ N
        rintro b ⟨x, _, rfl⟩
        exact (rep_spec x.1 x.2).1
      · -- every a ∈ N is ≥ some b ∈ B
        intro a ha
        let N' := { x | x ∈ N ∧ x ≤ a }
        have hN' : N'.Nonempty := ⟨a, ⟨ha, le_rfl⟩⟩
        obtain ⟨hfin', hnonempty'⟩ := h N' hN'
        let S' : Finset (Antisymmetrization M (· ≤ ·)) := @(minClasses N').toFinset (Antisymmetrization M (· ≤ ·)) (Set.Finite.fintype hfin')
        -- similarly pick one minimal class in S'
        have ⟨γ, hγ_in_S'⟩ : S'.Nonempty := by
            exact @Set.Aesop.toFinset_nonempty_of_nonempty (Antisymmetrization M (· ≤ ·)) (minClasses N') (by exact hfin'.fintype) hnonempty'
        have pick' : ∀ c ∈ S', ∃ d, d ∈ N' ∧ (∀ x ∈ N', ¬(x < d)) ∧ toAntisymmetrization ((· : M) ≤ ·) d = c := by
          intro c hc'
          simp only [minClasses, Set.mem_toFinset, Set.mem_image, Set.mem_setOf_eq, S'] at hc'
          obtain ⟨x, hx⟩ := hc'
          use x
          exact and_assoc.mp hx
        let repS' (c : Antisymmetrization M (· ≤ ·)) (hc' : c ∈ S') : M :=
          Classical.choose (pick' c hc')
        have repS'_spec (c : Antisymmetrization M (· ≤ ·)) (hc' : c ∈ S')
          : repS' c hc' ∈ N' ∧ (∀ x ∈ N', ¬x < (repS' c hc')) ∧ ⟦repS' c hc'⟧ = c
          := Classical.choose_spec (pick' c hc')
        -- pick one class from S'
        have ⟨γ, hγ_in_S'⟩ : S'.Nonempty := by
          exact @Set.Aesop.toFinset_nonempty_of_nonempty (Antisymmetrization M (· ≤ ·)) (minClasses N') (by exact hfin'.fintype) hnonempty'
        let c : M := repS' γ hγ_in_S'
        have ⟨hc_in_N', hc_min_N', hc_rep_γ⟩ := (repS'_spec γ hγ_in_S')
        have hc'_le_a : c ≤ a := by exact hc_in_N'.2
        have hγS : γ ∈ S := by
          have h_min_sub: minClasses N' ⊆ minClasses N := by
            exact @minClasses_restrict_le_subset M _ N a ha
          --have h_minclass_fin: Fintype ↑(minClasses N) := by exact hfin.fintype --를 적으면 오히려 증명 안됨
          exact Set.mem_toFinset.mpr (h_min_sub (by exact (Set.Finite.mem_toFinset hfin').mp hγ_in_S'))

        have hbc' : ∃ b ∈ B, toAntisymmetrization ((· : M) ≤ ·) b = toAntisymmetrization ((· : M) ≤ ·) c := by
          use rep γ hγS
          constructor
          · -- rep γ hc'S is one of your basis elements
            simp only [Finset.coe_attach, Set.image_univ, Set.mem_range, Subtype.exists, B]
            exact BEx.intro γ hγS rfl
          · calc
              toAntisymmetrization ((· : M) ≤ ·) (rep γ hγS) = γ := (rep_spec γ hγS).2.2
              _ = toAntisymmetrization ((· : M) ≤ ·) c := (repS'_spec γ hγ_in_S').2.2.symm
        obtain ⟨b, hbB, hb_eq⟩ := hbc'
        use b
        constructor
        · exact hbB
        · have : toAntisymmetrization ((· : M) ≤ ·) b = toAntisymmetrization ((· : M) ≤ ·) c → ((· : M) ≤ ·) b c := by
            rw [toAntisymmetrization, Quotient.eq]
            -- simp only [AntisymmRel]
            intro h
            exact h.1

          exact Preorder.le_trans b c a (this hb_eq) hc'_le_a
  · -- N = ∅ : take the empty basis
    use ∅
    simp only [Set.finite_empty, Set.empty_subset, Set.mem_empty_iff_false, false_and, exists_false,
      imp_false, true_and]
    exact fun a ↦ forall_not_of_not_exists hN a

/-- (i) ⇒ (ii): A poset with the Dickson property is well‐quasi‐ordered. -/
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
**(ii) ⇒ (iii): A Well Quasi-Ordered preorder has only finitely many, but at least one,
min‑classes in any nonempty subset.**
-/
theorem WellQuasiOrderedLE.minClasses_finite_and_nonempty
  (h_wqo : WellQuasiOrderedLE M) :
  ∀ N : Set M, N.Nonempty → (minClasses N).Finite ∧ (minClasses N).Nonempty := by
  intro N hN
  let QN : Set (Antisymmetrization M (· ≤ ·)) := minClasses N
  constructor

  · -- assume `QN` infinite and derive a contradiction
    by_contra h_inf
    have QN_inf : QN.Infinite := h_inf
    clear h_inf
    -- 1) get an embedding of ℕ into QN = minClasses N
    let emb : ℕ ↪ Subtype QN := Set.Infinite.natEmbedding _ QN_inf

    -- 2) turn that into an honest ℕ → Antisymmetrization M
    let g_classes : ℕ → Antisymmetrization M (· ≤ ·) := fun n => (emb n).1

    -- 3) injective followed by "embedding"
    have inj : Function.Injective g_classes := by
      intro i j h
      have : emb i = emb j := Subtype.ext h
      exact emb.injective this
    -- 4) each `g_classes n` lands in `QN`
    have mem : ∀ n, g_classes n ∈ QN := fun n => (emb n).2

    -- pick actual representatives in S = {a ∈ N | minimal in N}
    let S : Set M := { a | a ∈ N ∧ ∀ x ∈ N, ¬ x < a }

    -- 5) from `mem` we know `g_classes n ∈ toAntisymmetrization '' S`,
    --    so `∃ m ∈ S, toAntisymmetrization m = g_classes n`
    choose g hg_spec using fun n =>
      show ∃ m ∈ S, toAntisymmetrization ((· : M) ≤ ·) m = g_classes n
        from by simpa [minClasses, QN] using mem n

    -- unpack -- (range of g : ℕ → M) ⊆ N
    have g_in_N    : ∀ n,      (g n) ∈ N       := fun n => (hg_spec n).1.1
    have g_minimal : ∀ n x, x ∈ N → ¬ x < g n := fun n x hNx hlt =>
      (hg_spec n).1.2 x hNx hlt
    have g_eq      : ∀ n, toAntisymmetrization ((· : M) ≤ ·) (g n) = g_classes n := fun n => (hg_spec n).2

    -- 6) now apply WQO to the real sequence `g : ℕ → M`
    have ⟨i, j, hij, hle⟩ := h_wqo.wqo g

    -- 7) rule out `g i < g j` because `g j` is minimal
    by_cases heq : g i = g j
    · -- if they were equal then `g_classes i = g_classes j`, contradicting injectivity
      have hgceq : g_classes i = g_classes j := by
        have : toAntisymmetrization ((· : M) ≤ ·) (g i) = toAntisymmetrization _ (g j) := by
          exact congrArg (toAntisymmetrization fun x1 x2 ↦ x1 ≤ x2) heq
        rw [(hg_spec i).2, (hg_spec j).2] at this
        exact this
      exact (fun a ↦ Nat.ne_of_lt hij) hij (inj hgceq)
    · -- otherwise `g i < g j`, contradict minimality of `g j`
      simp only at hle
      have hclass_le : g_classes i ≤ g_classes j := by
        rw [←(hg_spec i).2, ←(hg_spec j).2]
        exact hle
      have hclass_neq : ¬g_classes i = g_classes j := by exact fun a ↦ heq (congrArg g (inj a))
      have hclass_lt : g_classes i < g_classes j := by exact lt_of_le_of_ne hclass_le hclass_neq
      have hlt : g i < g j := by
        simp only [← g_eq i, ← g_eq j,
          toAntisymmetrization_lt_toAntisymmetrization_iff] at hclass_lt
        exact hclass_lt
      exact (g_minimal j (g i) (g_in_N i)) hlt
  · -- (minClasses N) is nonempty
    -- from WQO we get well-foundedness of `<`
    --haveI _ : WellFoundedLT M := WellQuasiOrderedLE.to_wellFoundedLT
    have : ∃ a ∈ N, ∀ x ∈ N, ¬ x < a := @WellFounded.has_min M (· < ·) (wellFounded_lt) N hN
    obtain ⟨a, ha⟩ := this
    dsimp only [minClasses, Set.Nonempty]
    use toAntisymmetrization ((· : M) ≤ ·) a
    exact Set.mem_image_of_mem (toAntisymmetrization fun x1 x2 ↦ x1 ≤ x2) ha

/--
**Theorem (Proposition 4.42 formalised): Dickson Property ↔ Well Quasi-Ordered.**
Equivalence of Condition (i) and Condition (ii).
-/
theorem HasDicksonProperty_iff_WellQuasiOrderedLE :
    HasDicksonProperty M ↔ WellQuasiOrderedLE M := by
  constructor
  · exact HasDicksonProperty.to_wellQuasiOrderedLE
  · intro h_wqo
    apply finite_min_classes_implies_hasDicksonProperty
    exact h_wqo.minClasses_finite_and_nonempty
