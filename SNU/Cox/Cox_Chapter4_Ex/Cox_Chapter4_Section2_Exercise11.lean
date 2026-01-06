import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Polynomial.UniqueFactorization

open scoped Polynomial
open Polynomial

noncomputable section

/--
Ch. 4 §2, Exercise 11.

Show that
  √⟨ x^5 - 2x^4 + 2x^2 - x ,  x^5 - x^4 - 2x^3 + 2x^2 + x - 1 ⟩ = ⟨ x^2 - 1 ⟩.
-/
def f₁ : ℝ[X] := X^5 - 2 * X^4 + 2 * X^2 - X
def f₂ : ℝ[X] := X^5 - X^4 - 2 * X^3 + 2 * X^2 + X - 1

def J : Ideal ℝ[X] := Ideal.span ({f₁, f₂} : Set ℝ[X])

example :
    J.radical = Ideal.span ({X^2 - 1} : Set ℝ[X]) := by sorry







-- -- common factor
-- def g : ℝ[X] := (X - 1)^3 * (X + 1)
-- -- squarefree part
-- def h : ℝ[X] := (X - 1) * (X + 1)

  -- -- 1) explicit factorisations
  -- have hf₁ : f₁ = X * g := by
  --   -- purely algebraic identity in ℝ[X]
  --   simp [f₁, g]
  --   ring

  -- have hf₂ : f₂ = (X + 1) * g := by
  --   simp [f₂, g]
  --   ring

  -- -- 2) show ⟨f₁,f₂⟩ = ⟨g⟩ using g = f₂ - f₁ and divisibility
  -- have hJ : J = Ideal.span ({g} : Set ℝ[X]) := by
  --   unfold J
  --   apply le_antisymm
  --   · -- ⟨f₁,f₂⟩ ⊆ ⟨g⟩
  --     refine Ideal.span_le.2 ?_
  --     intro x hx
  --     rcases (by
  --       simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with rfl | rfl
  --     · -- f₁ ∈ ⟨g⟩
  --       refine Ideal.mem_span_singleton'.2 ?_
  --       refine ⟨X, ?_⟩
  --       simpa [hf₁]
  --     · -- f₂ ∈ ⟨g⟩
  --       refine Ideal.mem_span_singleton'.2 ?_
  --       refine ⟨X + 1, ?_⟩
  --       simpa [hf₂]
  --   · -- ⟨g⟩ ⊆ ⟨f₁,f₂⟩ since g = f₂ - f₁
  --     refine Ideal.span_le.2 ?_
  --     intro x hx
  --     have hf₁_mem : f₁ ∈ Ideal.span ({f₁, f₂} : Set ℝ[X]) :=
  --       Ideal.subset_span (by simp)
  --     have hf₂_mem : f₂ ∈ Ideal.span ({f₁, f₂} : Set ℝ[X]) :=
  --       Ideal.subset_span (by simp)
  --     have hg_mem : g ∈ Ideal.span ({f₁, f₂} : Set ℝ[X]) := by
  --       have : f₂ - f₁ ∈ Ideal.span ({f₁, f₂} : Set ℝ[X]) :=
  --         Ideal.sub_mem _ hf₂_mem hf₁_mem
  --       -- f₂ - f₁ = g
  --       have : f₂ - f₁ = g := by
  --         -- (X+1)g - Xg = g
  --         simp [hf₁, hf₂, g, sub_eq_add_neg]
  --         ring
  --       simpa [this] using this
  --     -- singleton case
  --     simpa [Set.mem_singleton_iff] using (by
  --       rcases (by simpa [Set.mem_singleton_iff] using hx) with rfl
  --       exact hg_mem)

  -- -- 3) compute √⟨g⟩ = ⟨h⟩
  -- have hrad :
  --     (Ideal.span ({g} : Set ℝ[X])).radical = Ideal.span ({h} : Set ℝ[X]) := by
  --   apply Ideal.ext
  --   intro x
  --   constructor
  --   · -- (⊆) x ∈ √⟨g⟩ → x ∈ ⟨h⟩
  --     intro hx
  --     rcases Ideal.mem_radical_iff.mp hx with ⟨n, hn⟩
  --     rcases Ideal.mem_span_singleton'.1 hn with ⟨r, hr⟩
  --     -- g ∣ x^n
  --     have hg_dvd : g ∣ x ^ n := ⟨r, by simpa [mul_assoc] using hr.symm⟩

  --     let p₁ : ℝ[X] := X - 1
  --     let p₂ : ℝ[X] := X + 1

  --     -- p₁ and p₂ are prime (linear polynomials over a field are irreducible hence prime)
  --     have hp₁_prime : Prime p₁ := by
  --       simpa [p₁] using (Polynomial.irreducible_X_sub_C (R := ℝ) (a := (1 : ℝ))).prime
  --     have hp₂_prime : Prime p₂ := by
  --       -- p₂ = X - (-1)
  --       simpa [p₂, sub_eq_add_neg] using
  --         (Polynomial.irreducible_X_sub_C (R := ℝ) (a := (-1 : ℝ))).prime

  --     -- p₁ ∣ g and p₂ ∣ g
  --     have hp₁_dvd_g : p₁ ∣ g := by
  --       -- g = p₁^3 * p₂
  --       simpa [g, p₁, p₂] using
  --         dvd_mul_of_dvd_left (dvd_pow_self p₁ (by decide : (3 : ℕ) ≠ 0)) p₂
  --     have hp₂_dvd_g : p₂ ∣ g := by
  --       -- g = p₁^3 * p₂
  --       simpa [g, p₁, p₂, mul_comm, mul_left_comm, mul_assoc] using
  --         dvd_mul_of_dvd_right (dvd_rfl : p₂ ∣ p₂) (p₁ ^ 3)

  --     -- hence p₁ ∣ x and p₂ ∣ x (prime divides a power ⇒ divides the base)
  --     have hp₁_dvd_x : p₁ ∣ x :=
  --       hp₁_prime.dvd_of_dvd_pow (dvd_trans hp₁_dvd_g hg_dvd)
  --     have hp₂_dvd_x : p₂ ∣ x :=
  --       hp₂_prime.dvd_of_dvd_pow (dvd_trans hp₂_dvd_g hg_dvd)

  --     -- p₁ and p₂ are coprime, so (p₁*p₂) ∣ x
  --     have hcop : IsCoprime p₁ p₂ := by
  --       refine ⟨(-((1 : ℝ) / 2) : ℝ[X]), ((1 : ℝ) / 2 : ℝ[X]), ?_⟩
  --       -- a*p₁ + b*p₂ = 1
  --       simp [p₁, p₂]
  --       ring

  --     have hp12_dvd_x : (p₁ * p₂) ∣ x :=
  --       IsCoprime.mul_dvd hcop hp₁_dvd_x hp₂_dvd_x

  --     -- convert divisibility to membership in ⟨h⟩
  --     rcases hp12_dvd_x with ⟨t, ht⟩
  --     refine Ideal.mem_span_singleton'.2 ?_
  --     refine ⟨t, ?_⟩
  --     -- t * h = x
  --     -- ht : x = p₁*p₂*t
  --     simpa [h, p₁, p₂, mul_assoc, mul_left_comm, mul_comm] using ht.symm

  --   · -- (⊇) x ∈ ⟨h⟩ → x ∈ √⟨g⟩
  --     intro hx
  --     rcases Ideal.mem_span_singleton'.1 hx with ⟨r, hr⟩

  --     have hh_mem : h ∈ (Ideal.span ({g} : Set ℝ[X])).radical := by
  --       refine Ideal.mem_radical_iff.mpr ?_
  --       refine ⟨3, ?_⟩
  --       refine Ideal.mem_span_singleton'.2 ?_
  --       refine ⟨(X + 1) ^ 2, ?_⟩
  --       -- (X+1)^2 * g = h^3
  --       have : (X + 1) ^ 2 * g = h ^ 3 := by
  --         -- both sides are (X-1)^3 * (X+1)^3
  --         simp [g, h]
  --         -- rearrange/multiply powers
  --         ring
  --       simpa [this]

  --     -- x = r*h belongs to the radical ideal
  --     have : r * h ∈ (Ideal.span ({g} : Set ℝ[X])).radical :=
  --       Ideal.mul_mem_left _ r hh_mem
  --     simpa [hr] using this

  -- -- 4) finish: rewrite J using hJ and expand h = X^2 - 1
  -- have hh : h = X^2 - 1 := by
  --   simp [h]
  --   ring

  -- calc
  --   J.radical
  --       = (Ideal.span ({g} : Set ℝ[X])).radical := by simpa [hJ]
  --   _ = Ideal.span ({h} : Set ℝ[X]) := hrad
  --   _ = Ideal.span ({X^2 - 1} : Set ℝ[X]) := by simpa [hh]
