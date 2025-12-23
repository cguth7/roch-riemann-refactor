/-
# Canonical Divisor for P¹

This file defines the canonical divisor K = -2[∞] for P¹ = RatFunc Fq.

## Main Definitions

* `p1Canonical Fq` - The canonical divisor K = -2[∞] on P¹

## Mathematical Background

For P¹ over any field k:
- The canonical bundle is ω_{P¹} = O(-2)
- This corresponds to the divisor K = -2[∞] (or any divisor of degree -2)
- deg(K) = -2, which gives genus g = 0 via g = (deg K + 2)/2

For function fields, the canonical divisor can also be defined via:
- The different ideal: K = -div(differentIdeal)
- For k(t), differentIdeal = (1), so K = 0 at finite places
- The "missing" -2 comes from the place at infinity

## References

- Stacks Project 0BXE (Serre duality for curves)
- Algebraic Geometry, Hartshorne, Chapter IV
-/

import RrLean.RiemannRochV2.P1Instance.P1Place
import RrLean.RiemannRochV2.Core.DivisorV3

noncomputable section

open IsDedekindDomain
open scoped Polynomial

namespace RiemannRochV2

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

-- DecidableEq instances needed for DivisorV3 operations
noncomputable instance : DecidableEq (HeightOneSpectrum Fq[X]) := Classical.decEq _

/-! ## The Canonical Divisor on P¹ -/

/-- The canonical divisor on P¹ = RatFunc Fq.

For P¹, the canonical divisor is K = -2[∞], where ∞ is the unique infinite place.
This is the divisor of any differential form, e.g., div(dt) = -2[∞].

Note: dt has a pole of order 2 at infinity because:
- t has a pole of order 1 at ∞ (v_∞(t) = -1)
- dt = d(1/s) = -ds/s² when s = 1/t is the local parameter at ∞
- So div(dt) = -2[∞]
-/
def p1Canonical : DivisorV3 Fq[X] (RatFunc Fq) :=
  DivisorV3.singleInfinite (p1InftyPlace Fq) (-2)

/-- The canonical divisor has degree -2. -/
@[simp]
lemma deg_p1Canonical : (p1Canonical Fq).deg = -2 := DivisorV3.deg_singleInfinite _ _

/-- The canonical divisor has coefficient -2 at the infinite place. -/
@[simp]
lemma p1Canonical_at_infty :
    p1Canonical Fq (Place.infinite (p1InftyPlace Fq)) = -2 := by
  simp only [p1Canonical, DivisorV3.singleInfinite, DivisorV3.single, Finsupp.single_eq_same]

/-- The canonical divisor has coefficient 0 at any finite place. -/
@[simp]
lemma p1Canonical_at_finite (v : HeightOneSpectrum Fq[X]) :
    p1Canonical Fq (Place.finite v) = 0 := by
  simp only [p1Canonical, DivisorV3.singleInfinite, DivisorV3.single, Finsupp.single_apply]
  have h : Place.finite v ≠ Place.infinite (p1InftyPlace Fq) := by
    intro heq
    cases heq
  simp [h]

/-- The canonical divisor is supported only at infinity. -/
lemma p1Canonical_support :
    (p1Canonical Fq).support = {Place.infinite (p1InftyPlace Fq)} := by
  simp only [p1Canonical, DivisorV3.singleInfinite, DivisorV3.single]
  rw [Finsupp.support_single_ne_zero]
  omega

/-- The finite part of the canonical divisor is zero. -/
lemma p1Canonical_finiteFilter : (p1Canonical Fq).finiteFilter = 0 := by
  ext p
  simp only [DivisorV3.finiteFilter, Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs with h
  · -- p.isFinite = true means p = Place.finite v for some v
    cases p with
    | finite v => exact p1Canonical_at_finite Fq v
    | infinite _ => simp [Place.isFinite] at h
  · rfl

/-- The infinite part of the canonical divisor equals the canonical divisor. -/
lemma p1Canonical_infiniteFilter : (p1Canonical Fq).infiniteFilter = p1Canonical Fq := by
  ext p
  simp only [DivisorV3.infiniteFilter, Finsupp.filter_apply]
  cases p with
  | finite v =>
    simp only [Place.isInfinite, p1Canonical_at_finite]
    rfl
  | infinite v =>
    simp only [Place.isInfinite, ite_true]

/-- The degree at finite places is 0 for the canonical divisor. -/
@[simp]
lemma degFinite_p1Canonical : (p1Canonical Fq).degFinite = 0 := by
  unfold DivisorV3.degFinite
  rw [p1Canonical_finiteFilter]
  simp only [DivisorV3.deg, Finsupp.sum_zero_index]

/-- The degree at infinite places is -2 for the canonical divisor. -/
@[simp]
lemma degInfinite_p1Canonical : (p1Canonical Fq).degInfinite = -2 := by
  unfold DivisorV3.degInfinite
  rw [p1Canonical_infiniteFilter, deg_p1Canonical]

/-! ## Relationship to Genus

For a smooth projective curve, the genus g satisfies:
  deg(K) = 2g - 2

For P¹: deg(K) = -2, so g = 0.
-/

/-- The genus of P¹ is 0. -/
def p1Genus : ℕ := 0

/-- The genus formula: deg(K) = 2g - 2 holds for P¹. -/
lemma p1_genus_formula : (p1Canonical Fq).deg = 2 * (p1Genus : ℤ) - 2 := by
  simp only [deg_p1Canonical, p1Genus, Int.ofNat_zero, mul_zero, zero_sub]

/-! ## Connection to Different Ideal

For general curves, the canonical divisor can be defined via the different ideal:
  K = -div(differentIdeal)

However, for P¹ = Frac(Fq[X]), the different ideal for the extension Fq[X] → RatFunc Fq
is trivial (= (1)), because there is no finite ramification. The canonical divisor
K = -2[∞] arises entirely from the place at infinity, which is NOT captured by
Mathlib's `differentIdeal` machinery (which only sees finite places).

This is the "Affine Trap" identified in Cycle 248: the different ideal infrastructure
only captures the affine part of the curve. For P¹, we define K = -2[∞] directly.
-/

/-! ## K - D for Serre Duality

Serre duality relates L(D) to L(K - D). For effective D on P¹:
- If deg(D) ≥ -1, then K - D has degree ≤ -1, so L(K - D) = 0
- This gives h¹(D) = 0 for such divisors
-/

/-- The degree of K - D. -/
lemma deg_p1Canonical_sub (D : DivisorV3 Fq[X] (RatFunc Fq)) :
    (p1Canonical Fq - D).deg = -2 - D.deg := by
  rw [DivisorV3.deg_sub, deg_p1Canonical]

/-- If deg(D) ≥ -1, then deg(K - D) ≤ -1. -/
lemma deg_p1Canonical_sub_neg {D : DivisorV3 Fq[X] (RatFunc Fq)}
    (hD : D.deg ≥ -1) : (p1Canonical Fq - D).deg ≤ -1 := by
  rw [deg_p1Canonical_sub]
  omega

/-- If deg(D) ≥ 0, then deg(K - D) ≤ -2 < 0. -/
lemma deg_p1Canonical_sub_neg' {D : DivisorV3 Fq[X] (RatFunc Fq)}
    (hD : D.deg ≥ 0) : (p1Canonical Fq - D).deg < 0 := by
  rw [deg_p1Canonical_sub]
  omega

end RiemannRochV2

end
