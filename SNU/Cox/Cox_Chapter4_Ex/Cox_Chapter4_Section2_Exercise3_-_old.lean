import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Nullstellensatz

open MvPolynomial

noncomputable section

abbrev σ : Type := Fin 1
abbrev x : MvPolynomial σ ℝ := X 0
def f : MvPolynomial σ ℝ := x ^ 2 + 1
def I : Ideal (MvPolynomial σ ℝ) := Ideal.span ({f} : Set (MvPolynomial σ ℝ))

theorem span_singleton_isRadical_of_irreducible
    (hf : Irreducible f) :
    (Ideal.span ({f} : Set (MvPolynomial σ k))).IsRadical := by
  classical
  have hrad :
      (Ideal.span ({f} : Set (MvPolynomial σ k))).radical
        =
      Ideal.span ({f} : Set (MvPolynomial σ k)) := by
    let a : Unit →₀ ℕ := Finsupp.single () 1
    let fi : Unit → MvPolynomial σ k := fun _ => f

    have h_irred : ∀ i ∈ a.support, Irreducible (fi i) := by
      intro i hi
      simpa [fi] using hf

    have h_ne_assoc :
        (a.support : Set Unit).Pairwise
          (fun i j => ¬ Associated (fi i) (fi j)) := by
      intro i hi j hj hij
      exact (hij (Subsingleton.elim i j)).elim

    have h_fact :
        f = C (1 : k) * a.prod (fun i n => (fi i) ^ n) := by
      simp [a, fi]

    -- Prop 9 적용
    simpa [a, fi] using
      (radical_span_singleton_eq_span_prod_irreducibles
        (f := f) (fi := fi)
        (hc := (one_ne_zero : (1 : k) ≠ 0))
        (h_irred := h_irred) (h_ne_assoc := h_ne_assoc) (h_fact := h_fact))

  exact (Ideal.radical_eq_iff
    (I := Ideal.span ({f} : Set (MvPolynomial σ k)))).1 hrad

/--
Ch.4 §2, Exercise 3.
Show that `⟨x^2 + 1⟩ ⊆ ℝ[x]` is a radical ideal, but that `V(x^2 + 1)` is the empty variety.
-/
example :
    I.IsRadical ∧ MvPolynomial.zeroLocus (K := ℝ) I = (∅ : Set (σ → ℝ)) := by
  constructor
  · -- `⟨x^2 + 1⟩` is radical
    -- (e.g. show it is prime, hence radical)
    sorry
  · -- `V(x^2 + 1)` is empty
    ext v
    constructor
    · intro hv
      -- unfold the definition of `zeroLocus`
      have hf_mem : f ∈ I := by
        exact Ideal.subset_span (by simp [I, f])
      have h_eval_zero : MvPolynomial.eval v f = 0 := by
        simpa [MvPolynomial.zeroLocus, I] using hv f hf_mem
      have h_ne_zero : MvPolynomial.eval v f ≠ 0 := by
        -- `eval v (x^2 + 1) = (v 0)^2 + 1 > 0`
        have h_eval : (MvPolynomial.eval v f) = (v 0) ^ 2 + (1 : ℝ) := by
          simp only [f, x, Fin.isValue, map_add, map_pow, eval_X, map_one]
        -- positivity gives nonzero
        have h_pos : (v 0) ^ 2 + (1 : ℝ) ≠ 0 := by
          nlinarith
        exact Ne.symm (ne_of_ne_of_eq (id (Ne.symm h_pos)) (id (Eq.symm h_eval)))
      exact (h_ne_zero h_eval_zero).elim
    · intro hv
      cases hv
