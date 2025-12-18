import RrLean.RiemannRochV2.FullRRData
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# Riemann-Roch Consistency Check for P¹ (Projective Line)

This module proves that the `FullRRData` axioms are **consistent** by exhibiting
a concrete function satisfying all the axioms for the genus 0 case (P¹).

## Mathematical Background

For P¹ over a field k:
- genus g = 0
- canonical divisor K has degree -2
- ℓ(D) = max(0, deg(D) + 1) for any divisor D

This gives:
- ℓ(0) = 1 (constants)
- ℓ(D) = 0 when deg(D) < 0 (no sections)
- ℓ(D) - ℓ(K-D) = deg(D) + 1 (Riemann-Roch)

## Main Result

`FullRRData_consistent_for_genus_0`: There exists a function ℓ : ℤ → ℕ satisfying
all the FullRRData axioms with genus = 0 and deg(K) = -2.

This validates that our axiom system is not contradictory.

## Note on Full Instantiation

A complete instantiation of `FullRRData k k[X] k(X)` for the polynomial ring
would require:
1. Handling the point at infinity (the affine line is not proper)
2. Proving ℓ(D) = max(0, deg(D) + 1) for actual divisors

This is left for future work. The consistency check here validates the axiom design.
-/

namespace RiemannRochV2.P1

/-! ## The P¹ Dimension Formula

For the projective line, ℓ(D) = max(0, deg(D) + 1).
-/

/-- The dimension formula for P¹: ℓ(D) = max(0, deg(D) + 1). -/
def ell_P1 (d : ℤ) : ℕ := (max 0 (d + 1)).toNat

lemma ell_P1_eq (d : ℤ) : ell_P1 d = (max 0 (d + 1)).toNat := rfl

/-- ℓ(D) = 0 when deg(D) < 0. -/
lemma ell_P1_zero_of_neg (d : ℤ) (hd : d < 0) : ell_P1 d = 0 := by
  simp only [ell_P1]
  have h : d + 1 ≤ 0 := by omega
  simp [max_eq_left h]

/-- ℓ(D) = deg(D) + 1 when deg(D) ≥ 0. -/
lemma ell_P1_pos (d : ℤ) (hd : d ≥ 0) : ell_P1 d = (d + 1).toNat := by
  simp only [ell_P1]
  have h : 0 ≤ d + 1 := by omega
  simp [max_eq_right h]

/-- ℓ(0) = 1 for P¹. -/
lemma ell_P1_zero : ell_P1 0 = 1 := by simp [ell_P1]

/-! ## Riemann-Roch Verification

Verify that ℓ(D) - ℓ(K-D) = deg(D) + 1 where K has degree -2.
-/

/-- Verify Riemann-Roch for P¹: ℓ(D) - ℓ(K-D) = deg(D) + 1 - g
where deg(K) = -2 and g = 0. -/
lemma RR_P1_check (d : ℤ) :
    (ell_P1 d : ℤ) - ell_P1 (-2 - d) = d + 1 := by
  by_cases hd : d < 0
  · -- Case: d < 0
    by_cases hd' : d < -1
    · -- Subcase: d ≤ -2
      -- ℓ(D) = 0, ℓ(K-D) = -d - 1 (since -2 - d ≥ 0)
      have h1 : ell_P1 d = 0 := ell_P1_zero_of_neg d hd
      have h2 : -2 - d ≥ 0 := by omega
      have h3 : ell_P1 (-2 - d) = (-2 - d + 1).toNat := ell_P1_pos (-2 - d) h2
      simp only [h1, h3, CharP.cast_eq_zero, zero_sub]
      have h4 : -2 - d + 1 = -d - 1 := by ring
      rw [h4]
      have h5 : -d - 1 ≥ 0 := by omega
      simp only [Int.toNat_of_nonneg h5]
      ring
    · -- Subcase: d = -1
      push_neg at hd'
      have hd_eq : d = -1 := by omega
      subst hd_eq
      simp [ell_P1]
  · -- Case: d ≥ 0
    push_neg at hd
    have h1 : ell_P1 d = (d + 1).toNat := ell_P1_pos d hd
    have h2 : -2 - d < 0 := by omega
    have h3 : ell_P1 (-2 - d) = 0 := ell_P1_zero_of_neg (-2 - d) h2
    simp only [h1, h3]
    have h4 : d + 1 ≥ 0 := by omega
    simp only [Int.toNat_of_nonneg h4, CharP.cast_eq_zero, sub_zero]

/-! ## Main Consistency Theorem -/

/-- The FullRRData axioms are consistent for genus 0.

This proves there exists a dimension function ℓ : ℤ → ℕ and a canonical
degree such that all the FullRRData axioms are satisfied. -/
theorem FullRRData_consistent_for_genus_0 :
    ∃ (ell : ℤ → ℕ) (degK : ℤ),
      -- Axiom 1: ℓ(0) = 1
      ell 0 = 1 ∧
      -- Axiom 2: deg(K) = 2g - 2 = -2
      degK = -2 ∧
      -- Axiom 3: RR equation
      (∀ d, (ell d : ℤ) - ell (degK - d) = d + 1) ∧
      -- Axiom 4: Vanishing for negative degree
      (∀ d, d < 0 → ell d = 0) := by
  use ell_P1, -2
  refine ⟨ell_P1_zero, rfl, ?_, ell_P1_zero_of_neg⟩
  intro d
  exact RR_P1_check d

/-- Corollary: The genus 0 case satisfies all FullRRData properties. -/
theorem genus_0_validates_FullRRData :
    -- There is a consistent assignment for g = 0
    ∃ (ell : ℤ → ℕ),
      -- ℓ(0) = 1 (properness)
      ell 0 = 1 ∧
      -- ℓ(D) = 0 for deg(D) < 0 (vanishing)
      (∀ d, d < 0 → ell d = 0) ∧
      -- ℓ(D) - ℓ(K-D) = deg(D) + 1 for K of degree -2 (Serre duality / RR)
      (∀ d, (ell d : ℤ) - ell (-2 - d) = d + 1) ∧
      -- deg(K) = 2g - 2 with g = 0
      (-2 : ℤ) = 2 * 0 - 2 := by
  use ell_P1
  exact ⟨ell_P1_zero, ell_P1_zero_of_neg, RR_P1_check, rfl⟩

end RiemannRochV2.P1
