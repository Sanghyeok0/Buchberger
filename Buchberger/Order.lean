import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.Defs.Unbundled -- For def Minimal
import Mathlib.Data.Set.Card

variable {M : Type*} [Preorder M] -- M equipped with a quasi-order (preorder) ≤

/-!
# Formalization of Proposition 4.42

This section formalizes Proposition 4.42, which states the equivalence
of four conditions for a preorder `≤` on a set `M`:

1.  **(i)** `≤` has the Dickson property (every subset has a finite basis).
2.  **(ii)** `≤` is a Well Quasi‑Order (every infinite sequence `aₙ` has `i < j` with `aᵢ ≤ aⱼ`).
3.  **(iii)** For every nonempty `N : Set M`, the set of min‑classes
     `minClasses N` is finite and nonempty.
4.  **(iv)** `≤` is well-founded and has no infinite antichains.

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

/-- The `~`‐equivalence on `M` associated to `≤`. -/
instance leSetoid : Setoid M where
  r := fun a b => a ≤ b ∧ b ≤ a
  iseqv := { refl := fun a => ⟨le_refl _, le_refl _⟩
             symm := by exact fun {x y} a ↦ id (And.symm a)
             trans := fun a b => ⟨le_trans a.1 b.1, le_trans b.2 a.2⟩ }

namespace Quotient

/-- The induced `≤` on `Quotient leSetoid`. -/
instance quotientPreorder : Preorder (Quotient (@leSetoid M _)) where
  le := fun a b =>
    Quotient.liftOn₂ a b
      (fun x y => x ≤ y)
      (fun a₁ a₂ b₁ b₂ (⟨h₁, h₁'⟩ : a₁ ≤ b₁ ∧ b₁ ≤ a₁)
                      (⟨h₂, h₂'⟩ : a₂ ≤ b₂ ∧ b₂ ≤ a₂) => by
        -- we must show `(a₁ ≤ b₁) = (a₂ ≤ b₂)` as Prop‐equality
        have : (a₁ ≤ a₂) ↔ (b₁ ≤ b₂) := by
          constructor
          · intro hab; exact h₁'.trans (hab.trans h₂)
          · intro hba; exact h₁.trans (hba.trans h₂')
        simp
        exact this )
  le_refl := by
    intro a; refine Quotient.inductionOn a fun x => ?_
    exact le_refl _
  le_trans := by
    intros q₁ q₂ q₃
    refine Quotient.inductionOn₃ q₁ q₂ q₃ fun a b c => (le_trans : a ≤ b → b ≤ c → a ≤ c)

/-- In the quotient, antisymmetry holds, so we get a `PartialOrder`. -/
instance partialOrder : PartialOrder (Quotient (@leSetoid M _)) where
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩
    intro hab hba
    apply Quotient.sound
    exact ⟨hab, hba⟩

end Quotient

/-- A **min‑class** of `N` is the `~`‑equivalence class of a minimal element of `N`. -/
def minClasses (N : Set M) : Set (Quotient (@leSetoid M _)) :=
  Quotient.mk leSetoid '' { a | a ∈ N ∧ ∀ x ∈ N, ¬ (x < a) }
  -- WRONG DEFINITION! : Quotient.mk leSetoid '' { b | Minimal (· ∈ N) b }

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
**Lemma 4.37:** Let `≤` be a quasi-order on `M`. The following are equivalent:
(i) Each non-empty subset `N` of `M` has exactly one min-class in `N`.
(ii) `≤` is linear and well-founded.
-/
lemma minclass_iff_linear_and_wf :
    -- Condition (i): Unique min-class for non-empty subsets
    (∀ (N : Set M), N.Nonempty → (minClasses N).ncard =1 )
    ↔
    -- Condition (ii): Linear and Well-founded
    (IsLinearOrder M (· ≤ ·) ∧ IsWellFounded M (· ≤ ·)):= by sorry

/--
**Lemma (i) ⇒ (iv): Dickson Property implies Well-Foundedness + Finite Antichains.**
Shows that if every subset has a finite basis (Condition i), then the order must
be well-founded and contain no infinite antichains (Condition iv).
-/
lemma hasDicksonProperty_implies_wf_and_finite_antichains :
    HasDicksonProperty M → (WellFoundedLT M ∧ ∀ s : Set M, IsAntichain (· ≤ ·) s → s.Finite) := by
  intro h_dickson
  sorry

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
    have pick : ∀ c ∈ S, ∃ b, b ∈ N ∧ (∀ x ∈ N, ¬(x < b)) ∧ Quotient.mk leSetoid b = c := by
      -- if c ∈ S then c ∈ minClasses N, so c = Quotient.mk b for some minimal b
      intro c hc
      --simp only [Set.mem_setOf_eq]
      simp [S, minClasses] at hc
      obtain ⟨x, hx⟩ := hc
      use x
      exact and_assoc.mp hx
    --choose rep rep_spec using pick
    let rep (c : Quotient leSetoid) (hc : c ∈ S) : M :=
      Classical.choose (pick c hc)
    let rep_spec (c : Quotient leSetoid) (hc : c ∈ S)
      : rep c hc ∈ N ∧ (∀ x ∈ N, ¬x < rep c hc) ∧ ⟦rep c hc⟧ = c
      := (Classical.choose_spec (pick c hc))

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
        let S' : Finset (Quotient leSetoid) := @(minClasses N').toFinset (Quotient leSetoid) (Set.Finite.fintype hfin')
        -- similarly pick one minimal class in S'
        have ⟨γ, hγ_in_S'⟩ : S'.Nonempty := by
            exact @Set.Aesop.toFinset_nonempty_of_nonempty (Quotient leSetoid) (minClasses N') (by exact hfin'.fintype) hnonempty'
        have pick' : ∀ c ∈ S', ∃ d, d ∈ N' ∧ (∀ x ∈ N', ¬(x < d)) ∧ Quotient.mk leSetoid d = c := by
          intro c hc'
          simp [S', minClasses] at hc'
          obtain ⟨x, hx⟩ := hc'
          use x
          exact and_assoc.mp hx
        let repS' (c : Quotient leSetoid) (hc' : c ∈ S') : M :=
          Classical.choose (pick' c hc')
        have repS'_spec (c : Quotient leSetoid) (hc' : c ∈ S')
          : repS' c hc' ∈ N' ∧ (∀ x ∈ N', ¬x < (repS' c hc')) ∧ ⟦repS' c hc'⟧ = c
          := Classical.choose_spec (pick' c hc')
        -- pick one class from S'
        have ⟨γ, hγ_in_S'⟩ : S'.Nonempty := by
          exact @Set.Aesop.toFinset_nonempty_of_nonempty (Quotient leSetoid) (minClasses N') (by exact hfin'.fintype) hnonempty'
        let c : M := repS' γ hγ_in_S'
        have ⟨hc_in_N', hc_min_N', hc_rep_γ⟩ := (repS'_spec γ hγ_in_S')
        have hc'_le_a : c ≤ a := by exact hc_in_N'.2
        have hγS : γ ∈ S := by
          have h_min_sub: minClasses N' ⊆ minClasses N := by
            exact @minClasses_restrict_le_subset M _ N a ha
          --have h_minclass_fin: Fintype ↑(minClasses N) := by exact hfin.fintype --를 적으면 오히려 증명 안됨
          exact Set.mem_toFinset.mpr (h_min_sub (by exact (Set.Finite.mem_toFinset hfin').mp hγ_in_S'))

        have hbc' : ∃ b ∈ B, Quotient.mk leSetoid b = Quotient.mk leSetoid c := by
          use rep γ hγS
          constructor
          · -- rep γ hc'S is one of your basis elements
            simp [B, hγS]
            exact BEx.intro γ hγS rfl
          · calc
              Quot.mk leSetoid (rep γ hγS) = γ := (rep_spec γ hγS).2.2
              _ = Quot.mk leSetoid (repS' γ hγ_in_S') := (repS'_spec γ hγ_in_S').2.2.symm
        obtain ⟨b, hbB, hb_eq⟩ := hbc'
        use b
        constructor
        · exact hbB
        · have : Quotient.mk leSetoid b = Quotient.mk leSetoid c → b ≤ c := by
            simp only [leSetoid, Quotient.eq, and_imp, S, rep, B]
            exact fun a a_1 ↦ a
          exact Preorder.le_trans b c a (this hb_eq) hc'_le_a
  · -- N = ∅ : take the empty basis
    use ∅
    simp only [Set.finite_empty, Set.empty_subset, Set.mem_empty_iff_false, false_and, exists_false,
      imp_false, true_and]
    exact fun a ↦ forall_not_of_not_exists hN a

/-- (iv) ⇒ (iii): Well‐Foundedness + Finite Antichains implies finiteness and non-emptiness
of `minClasses N` for any nonempty `N`. -/
lemma wf_and_finite_antichains_implies_minClasses_finite_and_nonempty
  (h : WellFoundedLT M ∧ ∀ s : Set M, IsAntichain (· ≤ ·) s → s.Finite) :
  ∀ N : Set M, N.Nonempty → (minClasses N).Finite ∧ (minClasses N).Nonempty := by
  intro N hN
  -- Extract well-foundedness of `<`
  have wf_lt : WellFounded (· < ·) := h.1.wf
  -- 1. Choose a `<`-minimal element b ∈ N
  obtain ⟨b, hbN, hb_min⟩ := wf_lt.has_min N hN
  -- 2. Collect all minimal elements of N for `<`
  let A : Set M := { a | a ∈ N ∧ ∀ x ∈ N, ¬ (x < a) }
  -- A is nonempty (contains b)
  have hA_nonempty : A.Nonempty := ⟨b, hbN, fun x hx => hb_min x hx⟩
  -- A is an antichain under `≤`
  have hA_antichain : IsAntichain (· ≤ ·) A := by
    intro x hx y hy hxy
    sorry
  -- 3. A is finite by hypothesis
  have hA_fin : A.Finite := h.2 A hA_antichain
  -- 4. `minClasses N` is the image of A under `Quotient.mk leSetoid`
  have : minClasses N = Quotient.mk leSetoid '' A := rfl
  -- 5. Conclude finiteness and nonemptiness
  sorry


/--
**Lemma (iv) ⇒ (i): Well-Foundedness + Finite Antichains implies Dickson Property.**
Shows that if the order is well-founded and has no infinite antichains (Condition iv),
then every subset `N` must have a finite basis (Condition i).
-/
lemma wf_and_finite_antichains_implies_hasDicksonProperty :
  (WellFoundedLT M ∧ ∀ s : Set M, IsAntichain (· ≤ ·) s → s.Finite) → HasDicksonProperty M := by
  intro wf_and_finite_antichains
  have : ∀ N : Set M, (N.Nonempty → (minClasses N).Finite ∧ (minClasses N).Nonempty) := by
    exact fun N a ↦ wf_and_finite_antichains_implies_minClasses_finite_and_nonempty wf_and_finite_antichains N a
  exact finite_min_classes_implies_hasDicksonProperty this

/-- (i) ⇒ (ii): A poset with the Dickson property is well‐quasi‐ordered. -/
theorem HasDicksonProperty.to_wellQuasiOrderedLE
  (h : HasDicksonProperty M) :
    WellQuasiOrderedLE M := by
  refine { wqo := ?_ }
  dsimp [WellQuasiOrdered]; intro f
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

-- /--
-- **(ii) ⇒ (iii): A Well Quasi-Ordered preorder has only finitely many, but at least one,
-- min‑classes in any nonempty subset.**
-- -/
-- theorem WellQuasiOrderedLE.minClasses_finite_and_nonempty
--     (h_wqo : WellQuasiOrderedLE M) : -- Assume Condition (ii)
--     ∀ N : Set M, N.Nonempty → (minClasses N).Finite ∧ (minClasses N).Nonempty := by
--   intro N hN_nonempty
--   haveI h_wf : WellFoundedLT M := WellQuasiOrderedLE.to_wellFoundedLT

--   constructor
--   · -- Part 1: Prove (minClasses N).Finite
--     by_contra h_mc_infinite
--     let QN := minClasses N
--     have QN_inf : QN.Infinite := h_mc_infinite

--     -- Construct infinite sequence of distinct min-classes and their representatives
--     -- recursively using classical choice.
--     let rec build_seq (n : ℕ) (picked_classes : Finset (Quotient leSetoid)) :
--         Σ' (q : Quotient leSetoid) (m : M),
--            q ∈ QN ∧ q ∉ picked_classes ∧ m ∈ { a | a ∈ N ∧ ∀ x ∈ N, ¬ (x < a) } ∧ Quotient.mk leSetoid m = q := by
--       -- Since QN is infinite, QN \ picked_classes is non-empty
--       have : (QN \ (↑picked_classes : Set (Quotient leSetoid))).Nonempty :=
--         Set.Infinite.nonempty_diff_finite QN_inf picked_classes.finite_toSet
--       -- Choose a class q from this difference
--       let q := Classical.choose this
--       have q_spec : q ∈ QN ∧ q ∉ picked_classes := Classical.choose_spec this
--       -- Choose a representative m for q
--       choose m hm_spec using (show ∃ m ∈ { a | a ∈ N ∧ ∀ x ∈ N, ¬ (x < a) }, Quotient.mk leSetoid m = q by
--           rw [minClasses, Set.mem_image] at q_spec; exact q_spec.1)
--       -- Return the pair (class, representative) and the proofs
--       exact ⟨q, m, q_spec.1, q_spec.2, hm_spec⟩

--     -- Define the sequence of classes and elements using dependent recursion / choice
--     let seq : ℕ → Σ' (q : Quotient leSetoid) (m : M),
--                    q ∈ QN ∧ q ∉ (Finset.image (fun k => (build_seq k default).1) (Finset.range n))
--                    ∧ m ∈ minimals_le N ∧ Quotient.mk Setoid.r m = q :=
--        fun n => build_seq n (Finset.image (fun k => (seq k).1) (Finset.range n)) -- This definition is circular!

--     -- Let's use exists_sequence_of_infinite instead.
--     obtain ⟨g, hg_inj⟩ : ∃ g : ℕ → Quotient leSetoid, Function.Injective g ∧ Set.range g ⊆ QN :=
--         Set.Infinite.exists_sequence_of_infinite QN_inf

--     -- For each distinct class g n, choose a representative minimal element f n
--     choose f hf_spec using (fun n => show ∃ m ∈ minimals_le N, Quotient.mk Setoid.r m = g n by
--       have : g n ∈ QN := Set.mem_range_of_mem g (Set.mem_range_self n) ▸ (hg_inj.2)
--       rw [minClasses, Set.mem_image] at this; exact this)
--     -- hf_spec n : f n ∈ minimals_le N ∧ Quotient.mk Setoid.r (f n) = g n

--     -- Now we have f : ℕ → M such that f n ∈ minimals_le N and ⟦f i⟧ ≠ ⟦f j⟧ for i ≠ j
--     have h_f_pairwise_neq : ∀ i j, i ≠ j → ¬ (f i ≈ f j) := by
--       intro i j hij_ne
--       contrapose! hij_ne -- Assume f i ≈ f j, prove i = j
--       apply hg_inj -- Use injectivity of g
--       rw [← (hf_spec i).2, ← (hf_spec j).2] -- Rewrite g i = ⟦f i⟧ and g j = ⟦f j⟧
--       exact Quotient.sound hij_ne -- f i ≈ f j → ⟦f i⟧ = ⟦f j⟧

--     -- Apply WQO to the sequence f
--     obtain ⟨i, j, hij_lt, hij_le⟩ := h_wqo.wqo f -- f i ≤ f j
--     have f_i_min : f i ∈ minimals_le N := (hf_spec i).1
--     have f_j_min : f j ∈ minimals_le N := (hf_spec j).1
--     have hji_le : f j ≤ f i := f_j_min.2 (f i) f_i_min.1 hij_le -- Use minimality of f j
--     have fi_equiv_fj : f i ≈ f j := ⟨hij_le, hji_le⟩
--     -- Contradiction
--     exact h_f_pairwise_neq i j hij_lt.ne fi_equiv_fj

--   · -- Part 2: Prove (minClasses N).Nonempty
--     rw [Set.nonempty_image_iff]
--     exact WellFounded.has_min N hN_nonempty

/--
**(ii) ⇒ (iii): A Well Quasi-Ordered preorder has only finitely many, but at least one,
min‑classes in any nonempty subset.**
-/
theorem WellQuasiOrderedLE.minClasses_finite_and_nonempty
    (h_wqo : WellQuasiOrderedLE M) : -- Assume Condition (ii)
    ∀ N : Set M, N.Nonempty → (minClasses N).Finite ∧ (minClasses N).Nonempty := by
  intro N hN_nonempty
  -- From WQO, we get WellFoundedLT
  haveI h_wf : WellFoundedLT M := WellQuasiOrderedLE.to_wellFoundedLT

  constructor
  · -- Part 1: Prove (minClasses N).Finite
    -- Proof by contradiction: Assume minClasses N is infinite.
    by_contra h_mc_infinite
    let QN := minClasses N
    have mc_inf : (minClasses N).Infinite := h_mc_infinite
    have bad_seq :
        ∃ f : ℕ → M, (∀ n, f n ∈ { a | a ∈ N ∧ ∀ x ∈ N, ¬ (x < a) }) ∧
                      (∀ i j, i ≠ j → ¬ (f i ≈ f j)) := by

      -- For each q ∈ minClasses N, choose a representative m_q ∈ minimal N such that ⟦m_q⟧ = q
      choose m_rep h_m_rep_spec using (fun q (hq : q ∈ minClasses N) =>
        show ∃ m ∈ { a | a ∈ N ∧ ∀ x ∈ N, ¬ (x < a) }, Quotient.mk leSetoid m = q by
          exact hq
      )
      sorry
    sorry
  · sorry


-- /-- (ii) ⇒ (iii): A well‐quasi‐ordered preorder has only finitely many, but at least one,
-- min‐classes in any nonempty subset. -/
-- theorem WellQuasiOrderedLE.minClasses_finite_and_nonempty
--   {M : Type*} [Preorder M]
--   (h : WellQuasiOrderedLE M) :
--   ∀ N : Set M, N.Nonempty → (minClasses N).Finite ∧ (minClasses N).Nonempty := by
--   intro N hN
--   have hfin : (minClasses N).Finite := by
--     by_contra h_inf
--     have : (minClasses N).Infinite := by exact h_inf
--     -- build the bad sequence using classical.choice; leave the details to `sorry`
--     have bad_seq : ∃ a : ℕ → M, ∀ i, a i ∈ N ∧ ∀ j, j < i → ¬ (Quotient.mk leSetoid (a j) = Quotient.mk leSetoid (a i)) := by
--       have : ∀ a, ∃ b ∈ (minClasses N), b < a := sorry --Set.infinite_iff_exists_lt this
--     sorry


/--
**Theorem (Proposition 4.42 formalised): Dickson Property ↔ Well Quasi-Ordered.**
Equivalence of Condition (i) and Condition (ii).
-/
theorem HasDicksonProperty_iff_WellQuasiOrderedLE :
    HasDicksonProperty M ↔ WellQuasiOrderedLE M := by
  -- We use the equivalence of both (i) and (ii) to (iv)
  rw [wellQuasiOrderedLE_iff] -- Replace (ii) with (iv)
  -- Goal is now HasDicksonProperty M ↔ (WellFoundedLT M ∧ FiniteAntichains M)
  exact ⟨hasDicksonProperty_implies_wf_and_finite_antichains,
         wf_and_finite_antichains_implies_hasDicksonProperty⟩

-- 틀린 코드

-- def minClasses_old (N : Set M) : Set (Quotient (@leSetoid M _)) :=
--   Quotient.mk leSetoid '' { b | Minimal (· ∈ N) b }

-- /--
-- **Lemma (iii) ⇒ (i): finiteness and nonemptiness of min‑classes implies Dickson Property.**
-- Shows that if for every nonempty N : Set M the set minClasses N is finite and nonempty
-- (Condition iii), then every subset N has a finite basis (Condition i).
-- -/
-- lemma finite_min_classes_implies_hasDicksonProperty_wrong_Minimal
--   (h : ∀ N : Set M, N.Nonempty → (minClasses_old N).Finite ∧ (minClasses_old N).Nonempty) :
--   HasDicksonProperty M := by
--   intro N
--   by_cases hN : N.Nonempty
--   · -- Build a finite basis B ⊆ N
--     obtain ⟨hfin, hnonempty⟩ := h N hN
--     haveI : Fintype (minClasses_old N) := hfin.fintype
--     let S := (minClasses_old N).toFinset
--     --let S := @(minClasses N).toFinset (Quotient leSetoid) (Set.Finite.fintype hfin)

--     -- pick a representative from each class
--     have pick : ∀ c ∈ S, ∃ b, b ∈ { b | Minimal (· ∈ N) b } ∧ Quotient.mk leSetoid b = c := by
--         -- if c ∈ s then c ∈ minClasses N, so c = mk b for some minimal b
--         intro c hc
--         simp only [Set.mem_setOf_eq]
--         simp [S, minClasses_old] at hc
--         obtain ⟨x, hx⟩ := hc
--         use x
--     --choose rep rep_spec using pick
--     let rep (c : Quotient leSetoid) (hc : c ∈ S) : M :=
--       Classical.choose (pick c hc)
--     have rep_spec (c : Quotient leSetoid) (hc : c ∈ S) :
--       Minimal (· ∈ N) (rep c hc) ∧ Quotient.mk leSetoid (rep c hc) = c :=
--       Classical.choose_spec (pick c hc)

--     -- Turn S into a Finset M of actual reps
--     let rep' (x : Subtype fun c => c ∈ S) : M := rep x.1 x.2
--     let B : Set M := (fun x => rep x.1 x.2) '' S.attach.toSet
--     -- S.attach : Finset { c // c ∈ S } and S.attach.toSet : Set { c // c ∈ S }

--     use B
--     constructor
--     · show B.Finite
--       exact (Set.toFinite B)
--     · constructor
--       · show B ⊆ N
--         rintro b ⟨x, _, rfl⟩
--         exact (rep_spec x.1 x.2).1.1
--       · show ∀ a ∈ N, ∃ b ∈ B, b ≤ a
--         intro a ha
--         let N' := { d | d ∈ N ∧ d ≤ a }
--         have N'_ne : N'.Nonempty := ⟨a, ha, le_rfl⟩
--         obtain ⟨hfin', hnonempty'⟩ := h N' N'_ne
--         let S' : Finset (Quotient leSetoid) := @(minClasses_old N').toFinset (Quotient leSetoid) (Set.Finite.fintype hfin')
--         have pick' : ∀ c ∈ S', ∃ d, Minimal (· ∈ N') d ∧ Quotient.mk leSetoid d = c := by
--           intro c hc'
--           simp [S', minClasses_old] at hc'
--           obtain ⟨x, hx⟩ := hc'
--           use x
--         let repS' (c : Quotient leSetoid) (hc' : c ∈ S') : M :=
--           Classical.choose (pick' c hc')
--         have repS'_spec (c : Quotient leSetoid) (hc' : c ∈ S') :
--           Minimal (· ∈ N') (repS' c hc') ∧ Quotient.mk leSetoid (repS' c hc') = c :=
--             Classical.choose_spec (pick' c hc')
--         -- pick one class from S'
--         have ⟨γ, hγ_in_S'⟩ : S'.Nonempty := by
--           exact @Set.Aesop.toFinset_nonempty_of_nonempty (Quotient leSetoid) (minClasses_old N') (by exact hfin'.fintype) hnonempty'
--         let c : M := repS' γ hγ_in_S'
--         have ⟨hc_mem_N', hc_min_N'⟩ := (repS'_spec γ hγ_in_S').1
--         simp only at hc_mem_N'
--         simp only at hc_min_N'
--         -- We want to show c' is minimal in N i.e., ⟦c'⟧ = c'_class ∈ S
--         have hc'_le_a : c ≤ a := by exact hc_mem_N'.2
--         have hγS : γ ∈ S := by
--           have test : γ ∈ (minClasses_old N') := by exact pick' γ hγ_in_S'
--           have h_min_sub: minClasses_old N' ⊆ minClasses_old N := by
--             sorry --exact @minClasses_restrict_le_subset M _ N a ha
--           --have h_minclass_fin: Fintype ↑(minClasses N) := by exact hfin.fintype 를 적으면 오히려 증명 안됨
--           have sq : γ ∈ (minClasses_old N).toFinset := by exact Set.mem_toFinset.mpr (h_min_sub (pick' γ hγ_in_S'))
--           exact Set.mem_toFinset.mpr (h_min_sub (pick' γ hγ_in_S'))
--           --exact Set.mem_toFinset.mpr (h_min_sub (pick' γ hγ_in_S'))

--         have hbc' : ∃ b ∈ B, Quotient.mk leSetoid b = Quotient.mk leSetoid c := by
--           use rep γ hγS
--           constructor
--           · -- rep γ hc'S is one of your basis elements
--             simp [B, hγS]
--             exact BEx.intro γ hγS rfl
--           · calc
--               Quot.mk leSetoid (rep γ hγS) = γ := (rep_spec γ hγS).2
--               _ = Quot.mk leSetoid (repS' γ hγ_in_S') := (repS'_spec γ hγ_in_S').2.symm
--         obtain ⟨b, hbB, hb_eq⟩ := hbc'
--         use b
--         constructor
--         · exact hbB
--         · have : Quotient.mk leSetoid b = Quotient.mk leSetoid c → b ≤ c := by
--             simp only [leSetoid, Quotient.eq, and_imp, S, rep, B]
--             exact fun a a_1 ↦ a
--           exact Preorder.le_trans b c a (this hb_eq) hc'_le_a

--   · -- N = ∅: take the empty basis
--     use ∅
--     simp only [Set.finite_empty, Set.empty_subset, Set.mem_empty_iff_false, false_and, exists_false,
--       imp_false, true_and]
--     exact fun a ↦ forall_not_of_not_exists hN a
