import Mathlib.RingTheory.Polynomial.UniqueFactorization

namespace MvPolynomial

open scoped BigOperators

variable {σ : Type*} [Fintype σ]
variable {k : Type*} [Field k]

omit [Fintype σ] in
/--
Cox–Little–O'Shea, Ch.4 §2, Proposition 9.

Let `f ∈ k[x₁,...,xₙ]` and let I = ⟨f⟩.
Assume a factorization `f = C c * ∏ i, (fi i) ^ (a i)` into powers of
pairwise non-associated irreducibles `fi i`.
Then `√I = ⟨∏ i, fi i⟩`.
-/
theorem radical_span_singleton_eq_span_prod_irreducibles
  {f : MvPolynomial σ k}
  {ι : Type*} [DecidableEq ι]
  {c : k}
  {a : ι →₀ ℕ}
  (fi : ι → MvPolynomial σ k)
  (hc : c ≠ 0)
  (h_irred : ∀ i ∈ a.support, Irreducible (fi i))
  (h_ne_assoc : (a.support : Set ι).Pairwise fun i j => ¬ Associated (fi i) (fi j))
  (h_fact : f = C c * a.prod (fun i n => (fi i) ^ n)) :
  (Ideal.span ({f} : Set (MvPolynomial σ k))).radical
    =
  Ideal.span ({∏ i ∈ a.support, fi i} : Set (MvPolynomial σ k)) := by
  -- abbreviations
  set s : Finset ι := a.support
  set p : MvPolynomial σ k := ∏ i ∈ s, fi i

  -- rewrite the `Finsupp.prod` appearing in `h_fact` as a `Finset.prod`
  have h_aProd :
      a.prod (fun i n => (fi i) ^ n) = ∏ i ∈ s, (fi i) ^ (a i) := by
    simp [s, Finsupp.prod]

  have h_fact' : f = C c * ∏ i ∈ s, (fi i) ^ (a i) := by
    simpa [h_aProd] using h_fact

  -- coprimality on support (distinct irreducibles)
  have hcop : (s : Set ι).Pairwise (fun i j => IsRelPrime (fi i) (fi j)) := by
    intro i hi j hj hij
    have hirri : Irreducible (fi i) := h_irred i (by simpa [s] using hi)
    have hirrj : Irreducible (fi j) := h_irred j (by simpa [s] using hj)
    have hna : ¬ Associated (fi i) (fi j) := by
      exact h_ne_assoc (by simpa [s] using hi) (by simpa [s] using hj) hij
    have hnot : ¬ fi i ∣ fi j := by
      intro hdiv
      have hassoc : Associated (fi i) (fi j) := by
        exact (Irreducible.dvd_irreducible_iff_associated (h_irred i hi) (h_irred j hj)).mp hdiv
      exact hna hassoc
    exact (hirri.isRelPrime_iff_not_dvd).2 hnot

  -- each `fi i` divides `f` (for i in support)
  have hfi_dvd_f : ∀ i ∈ s, fi i ∣ f := by
    intro i hi
    have hai_ne : a i ≠ 0 := by
      simpa only [s] using (Finsupp.mem_support_iff.mp hi)
    have h1 : fi i ∣ (fi i) ^ (a i) := by
      simpa using (dvd_pow_self (fi i) hai_ne)

    have h2 : (fi i) ^ (a i) ∣ ∏ j ∈ s, (fi j) ^ (a j) := by
      exact Finset.dvd_prod_of_mem (f := fun j => (fi j) ^ (a j)) hi

    have h3 : fi i ∣ ∏ j ∈ s, (fi j) ^ (a j) := dvd_trans h1 h2

    -- f = C c * (∏ ...)
    rcases h3 with ⟨t, ht⟩
    refine ⟨C c * t, ?_⟩
    calc
      f = C c * (∏ j ∈ s, (fi j) ^ (a j)) := h_fact'
      _ = C c * (fi i * t) := by simp only [ht, mul_comm, mul_assoc]
      _ = fi i * (C c * t) := by simp only [mul_comm, mul_assoc, mul_left_comm]

  -- Now prove ideal equality by ext.
  apply Ideal.ext
  intro x
  constructor

  · -- (⊆)  x ∈ √⟨f⟩  →  x ∈ ⟨p⟩
    intro hx
    rcases (Ideal.mem_radical_iff.mp hx) with ⟨n, hn⟩

    -- force a positive exponent: x^(n+1) ∈ ⟨f⟩
    have hn' : x ^ (n + 1) ∈ Ideal.span ({f} : Set (MvPolynomial σ k)) := by
      simpa [pow_succ'] using (Ideal.mul_mem_left (Ideal.span ({f} : Set (MvPolynomial σ k))) x hn)

    rcases (Ideal.mem_span_singleton'.1 hn') with ⟨r, hr⟩
    -- hr : r * f = x^(n+1)

    -- show every fi i divides x
    have hfi_dvd_x : ∀ i ∈ s, fi i ∣ x := by
      intro i hi
      have hirr : Irreducible (fi i) := by exact h_irred i hi
      have hprime : Prime (fi i) := hirr.prime

      -- fi i ∣ x^(n+1)
      have h_dvd_pow : fi i ∣ x ^ (n + 1) := by
        have : fi i ∣ r * f := dvd_mul_of_dvd_right (hfi_dvd_f i hi) r
        simpa only [hr.symm] using this

      exact hprime.dvd_of_dvd_pow h_dvd_pow

    -- product divides x (pairwise coprime + each divides)
    have hp_dvd_x : (∏ i ∈ s, fi i) ∣ x := by
      exact Finset.prod_dvd_of_isRelPrime hcop hfi_dvd_x

    -- convert divisibility to membership in ⟨p⟩
    rcases hp_dvd_x with ⟨t, ht⟩
    -- ht : x = (∏ ...) * t
    refine Ideal.mem_span_singleton'.2 ?_
    refine ⟨t, ?_⟩
    -- need t * p = x
    simpa [p, s, mul_assoc, mul_left_comm, mul_comm] using ht.symm

  · -- (⊇)  x ∈ ⟨p⟩  →  x ∈ √⟨f⟩
    intro hx
    rcases (Ideal.mem_span_singleton'.1 hx) with ⟨r, hr⟩
    -- hr : r * p = x

    -- show p ∈ √⟨f⟩ by exhibiting an exponent
    have hp_mem_rad : p ∈ (Ideal.span ({f} : Set (MvPolynomial σ k))).radical := by
      -- choose N = sum of exponents (works even if support is empty)
      let N : ℕ := ∑ i ∈ s, a i
      let q : MvPolynomial σ k := C (c⁻¹) * ∏ i ∈ s, (fi i) ^ (N - a i)

      have ha_le : ∀ i ∈ s, a i ≤ N := by
        intro i hi
        have : a i ≤ ∑ j ∈ s, a j :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        simpa [N] using this

      have hp_pow :
          (∏ i ∈ s, fi i) ^ N = ∏ i ∈ s, (fi i) ^ N := by
        refine Finset.induction_on s ?_ ?_
        · simp only [Finset.prod_empty, one_pow]
        · intro i s hi ih
          simp only [hi, not_false_eq_true, Finset.prod_insert, mul_pow, ih]

      have hsplit :
          (∏ i ∈ s, (fi i) ^ (N - a i)) * (∏ i ∈ s, (fi i) ^ (a i))
            =
          ∏ i ∈ s, (fi i) ^ N := by
        calc
          (∏ i ∈ s, (fi i) ^ (N - a i)) * (∏ i ∈ s, (fi i) ^ (a i))
              =
            ∏ i ∈ s, ((fi i) ^ (N - a i) * (fi i) ^ (a i)) := by
              simpa using (Finset.prod_mul_distrib : _).symm
          _ =
            ∏ i ∈ s, (fi i) ^ N := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              have hle : a i ≤ N := ha_le i hi
              -- (N - a i) + a i = N
              have : (N - a i) + a i = N := Nat.sub_add_cancel hle
              -- rewrite using pow_add
              calc
                (fi i) ^ (N - a i) * (fi i) ^ (a i)
                    =
                  (fi i) ^ ((N - a i) + a i) := by
                    simpa only using (pow_add (fi i) (N - a i) (a i)).symm
                _ = (fi i) ^ N := by simp only [this]

      have hmul : q * f = p ^ N := by
        -- expand f using h_fact'
        calc
          q * f
              =
            (C (c⁻¹) * ∏ i ∈ s, (fi i) ^ (N - a i)) * (C c * ∏ i ∈ s, (fi i) ^ (a i)) := by
              simp only [h_fact', q]
          _ =
            (C (c⁻¹) * C c) * ((∏ i ∈ s, (fi i) ^ (N - a i)) * (∏ i ∈ s, (fi i) ^ (a i))) := by
              simp only [mul_comm, mul_left_comm, mul_assoc]
          _ =
            (1 : MvPolynomial σ k) * (∏ i ∈ s, (fi i) ^ N) := by
              rw [←MvPolynomial.C_mul]
              rw [inv_mul_cancel₀ hc]
              simp only [MvPolynomial.C_1, one_mul]
              exact hsplit
          _ =
            ∏ i ∈ s, (fi i) ^ N := by simp
          _ =
            (∏ i ∈ s, fi i) ^ N := by
              simpa only using hp_pow.symm
          _ = p ^ N := by simp [p]

      -- p^N ∈ ⟨f⟩ hence p ∈ √⟨f⟩
      refine Ideal.mem_radical_iff.mpr ?_
      refine ⟨N, ?_⟩
      refine Ideal.mem_span_singleton'.2 ?_
      refine ⟨q, hmul⟩

    -- now x = r * p belongs to the radical ideal
    have : r * p ∈ (Ideal.span ({f} : Set (MvPolynomial σ k))).radical :=
      Ideal.mul_mem_left _ r hp_mem_rad
    simpa only [hr] using this
