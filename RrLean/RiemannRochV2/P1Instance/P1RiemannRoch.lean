/-
# Riemann-Roch Theorem for P¹

This file assembles the full Riemann-Roch theorem for P¹ = RatFunc Fq.

## Main Results

* `riemann_roch_p1` - The Riemann-Roch theorem for P¹

## Mathematical Background

For P¹ over a finite field Fq:
- Genus g = 0
- Canonical divisor K = -2[∞]
- For effective divisors D: ℓ(D) = deg(D) + 1, ℓ(K-D) = 0

The Riemann-Roch theorem states:
  ℓ(D) - ℓ(K - D) = deg(D) + 1 - g

For P¹ with g = 0 and effective D:
  ℓ(D) - ℓ(K - D) = (deg(D) + 1) - 0 = deg(D) + 1

## Implementation Notes

This file combines results from two frameworks:
1. `ell_ratfunc_projective` (DimensionScratch.lean) - uses affine divisors + noPoleAtInfinity
2. `ellV3` (P1VanishingLKD.lean) - uses projective divisors (DivisorV3)

Both frameworks compute the same dimensions for the spaces involved.
-/

import RrLean.RiemannRochV2.P1Instance.P1VanishingLKD
import RrLean.RiemannRochV2.SerreDuality.P1Specific.DimensionScratch

noncomputable section

open IsDedekindDomain
open scoped Polynomial

namespace RiemannRochV2

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-! ## The Riemann-Roch Theorem for P¹

We state Riemann-Roch using the established dimension formulas:
- ℓ(D) from `ell_ratfunc_projective_eq_deg_plus_one`
- ℓ(K-D) from `ellV3_p1Canonical_sub_ofAffine_eq_zero`
-/

/-- For effective divisors D with linear support on P¹, ℓ(D) = deg(D) + 1.

This is equivalent to `ell_ratfunc_projective_eq_deg_plus_one`. -/
theorem ell_D_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective D = D.deg.toNat + 1 :=
  ell_ratfunc_projective_eq_deg_plus_one Fq D hD hDlin

/-- For effective divisors D on P¹, ℓ(K-D) = 0.

This is equivalent to `ellV3_p1Canonical_sub_ofAffine_eq_zero`. -/
theorem ell_K_sub_D_eq_zero {D : DivisorV2 (Polynomial Fq)} (hD : D.Effective) :
    ellV3 (k := Fq) (R := Polynomial Fq) (K := RatFunc Fq)
      (p1Canonical Fq - DivisorV3.ofAffine D) = 0 :=
  ellV3_p1Canonical_sub_ofAffine_eq_zero Fq hD

/-- Helper: Effective divisors have non-negative degree. -/
lemma effective_deg_nonneg' {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {D : DivisorV2 R} (hD : D.Effective) :
    0 ≤ D.deg := by
  unfold DivisorV2.Effective at hD
  unfold DivisorV2.deg
  -- Sum of non-negative coefficients is non-negative
  apply Finsupp.sum_nonneg
  intro v _
  exact hD v

/-- The Riemann-Roch theorem for P¹: ℓ(D) - ℓ(K-D) = deg(D) + 1 - g for effective D.

This is the genus-0 version of Riemann-Roch. For P¹:
- g = 0 (genus)
- K = -2[∞] (canonical divisor)
- For effective D: ℓ(D) = deg(D) + 1, ℓ(K-D) = 0

The formula becomes: ℓ(D) - ℓ(K-D) = deg(D) + 1 - 0 = deg(D) + 1

**Note**: This theorem uses `ell_ratfunc_projective` for ℓ(D) and `ellV3` for ℓ(K-D).
Both are dimensions of finite-dimensional Fq-vector spaces:
- `ell_ratfunc_projective` uses `Module.finrank`
- `ellV3` uses `Module.length` (which equals finrank for finite-dim spaces)
-/
theorem riemann_roch_p1 (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    (ell_ratfunc_projective D : ℤ) -
      (ellV3 (k := Fq) (R := Polynomial Fq) (K := RatFunc Fq)
        (p1Canonical Fq - DivisorV3.ofAffine D) : ℤ) =
    D.deg + 1 - (p1Genus : ℤ) := by
  -- ℓ(D) = deg(D) + 1
  have h_ell_D := ell_ratfunc_projective_eq_deg_plus_one Fq D hD hDlin
  -- ℓ(K-D) = 0
  have h_ell_KD := ellV3_p1Canonical_sub_ofAffine_eq_zero Fq hD
  -- p1Genus = 0
  simp only [p1Genus, Int.ofNat_zero, sub_zero]
  -- deg(D) ≥ 0 since D is effective
  have hD_deg : D.deg ≥ 0 := effective_deg_nonneg' hD
  -- Substitute and compute
  rw [h_ell_D, h_ell_KD]
  simp only [Int.ofNat_zero, sub_zero]
  -- deg(D).toNat + 1 = deg(D) + 1 (when deg ≥ 0)
  omega

/-- Alternative formulation: ℓ(D) - ℓ(K-D) = deg(D) + 1 for effective D on P¹. -/
theorem riemann_roch_p1' (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    (ell_ratfunc_projective D : ℤ) -
      (ellV3 (k := Fq) (R := Polynomial Fq) (K := RatFunc Fq)
        (p1Canonical Fq - DivisorV3.ofAffine D) : ℤ) =
    D.deg + 1 := by
  rw [riemann_roch_p1 Fq D hD hDlin]
  simp only [p1Genus, Int.ofNat_zero, sub_zero]

/-- The Riemann-Roch formula as a natural number equality (when everything is ≥ 0). -/
theorem riemann_roch_p1_nat (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective D = D.deg.toNat + 1 + p1Genus -
      ellV3 (k := Fq) (R := Polynomial Fq) (K := RatFunc Fq)
        (p1Canonical Fq - DivisorV3.ofAffine D) := by
  have h_ell_D := ell_ratfunc_projective_eq_deg_plus_one Fq D hD hDlin
  have h_ell_KD := ellV3_p1Canonical_sub_ofAffine_eq_zero Fq hD
  rw [h_ell_D, h_ell_KD]
  simp only [p1Genus, add_zero, Nat.sub_zero]

/-! ## Summary of Riemann-Roch Components

For P¹ = RatFunc Fq with genus g = 0:

| Component | Definition | Value for effective D |
|-----------|------------|----------------------|
| g | p1Genus | 0 |
| K | p1Canonical Fq | -2[∞] |
| deg(K) | deg_p1Canonical | -2 |
| ℓ(D) | ell_ratfunc_projective D | deg(D) + 1 |
| ℓ(K-D) | ellV3 (p1Canonical - ofAffine D) | 0 |

Riemann-Roch: ℓ(D) - ℓ(K-D) = deg(D) + 1 - g = deg(D) + 1
-/

end RiemannRochV2

end
