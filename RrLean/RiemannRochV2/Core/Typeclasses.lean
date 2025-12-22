import RrLean.RiemannRochV2.Core.RRSpace

/-!
# Typeclasses for Riemann-Roch

This module defines the typeclass hierarchy for Riemann-Roch:

* `LocalGapBound` - Affine version: gap ≤ 1 via evaluation map
* `SinglePointBound` - Projective version: adds ℓ(0) = 1
* `BaseDim` - Explicit base dimension constant

## Affine vs Projective Model Distinction (Cycle 23)

**Problem (discovered Cycle 22)**:
- `ell_zero_eq_one : ellV2_real R K 0 = 1` is IMPOSSIBLE for affine models
- HeightOneSpectrum R captures only FINITE places
- L(0) = R (integral elements) → Module.length R R = ⊤

**Solution: Two-tier typeclass hierarchy**:
- `LocalGapBound`: PROVABLE (gap ≤ 1 via evaluation map to residue field)
- `SinglePointBound extends LocalGapBound`: PROJECTIVE (adds ℓ(0) = 1)
- `BaseDim`: SEPARATE (explicit base dimension constant)
-/

namespace RiemannRochV2

open IsDedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: typeclass_local_gap_bound] [status: OK] [cycle: 23]
/-- Typeclass capturing the local gap bound for Riemann-Roch (AFFINE VERSION).

This encodes ONE key geometric fact that's PROVABLE from affine model:
1. Adding a single point increases ℓ(D) by at most 1 (gap_le_one)

The bound comes from the evaluation map L(D + v) → κ(v) with kernel ⊇ L(D).

This is the PROVABLE subset that works for affine models (HeightOneSpectrum R).
Does NOT assume ℓ(0) = 1, which requires compactification. -/
class LocalGapBound (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] where
  /-- Adding a single point increases dimension by at most 1 -/
  gap_le_one : ∀ (D : DivisorV2 R) (v : HeightOneSpectrum R),
    ellV2_real R K (D + DivisorV2.single v 1) ≤ ellV2_real R K D + 1

-- Candidate 2 [tag: typeclass_single_point_bound] [status: OK] [cycle: 23]
/-- Typeclass capturing the single-point dimension bound for Riemann-Roch (PROJECTIVE VERSION).

This extends LocalGapBound with the additional axiom:
2. The only functions with no poles are constants, so ℓ(0) = 1 (ell_zero_eq_one)

This REQUIRES compactification (including infinite places).
For affine models using HeightOneSpectrum R alone, ell_zero_eq_one is FALSE.

Geometric meaning:
- LocalGapBound: Local evaluation gives dimension jump ≤ 1
- ell_zero_eq_one: Global holomorphic sections = constants (proper curve)

These axioms enable the degree induction proof of Riemann inequality. -/
class SinglePointBound (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    extends LocalGapBound R K where
  /-- L(0) has dimension 1 (only constants have no poles) -/
  ell_zero_eq_one : ellV2_real R K 0 = 1

-- Candidate 3 [tag: typeclass_base_dim] [status: OK] [cycle: 23]
/-- Typeclass providing the base dimension constant for Riemann-Roch.

For affine models: basedim = ℓ_affine(0) (dimension of integral functions)
For projective models: basedim = ℓ(0) = 1 (only constants)

This separates the DIMENSION CONSTANT from the PROVABILITY ASSUMPTION.

Example values:
- Function field k(t) affine: basedim = ∞ (k[t] has infinite length)
- Function field k(t) projective: basedim = 1 (only constants k)
- Elliptic curve: basedim = 1 -/
class BaseDim (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] where
  /-- The base dimension ℓ(0) -/
  basedim : ℕ
  /-- The base dimension equals ℓ(0) -/
  ell_zero_eq : ellV2_real R K 0 = basedim

-- Candidate 6 [tag: instance_single_to_base] [status: OK] [cycle: 23]
/-- Derive BaseDim instance from SinglePointBound.

For projective models with SinglePointBound, we get basedim = 1.
This instance allows reusing affine results in projective contexts. -/
instance SinglePointBound.toBaseDim [spb : SinglePointBound R K] : BaseDim R K where
  basedim := 1
  ell_zero_eq := spb.ell_zero_eq_one

-- Candidate 4 [tag: typeclass_application] [status: OK] [cycle: 23]
/-- Application of LocalGapBound: ℓ(D + v) ≤ ℓ(D) + 1.

Updated in Cycle 23 to use LocalGapBound instead of SinglePointBound.
This makes the helper lemma usable in affine contexts. -/
lemma ellV2_real_add_single_le_succ [LocalGapBound R K]
    (D : DivisorV2 R) (v : HeightOneSpectrum R) :
    ellV2_real R K (D + DivisorV2.single v 1) ≤ ellV2_real R K D + 1 :=
  LocalGapBound.gap_le_one D v

end RiemannRochV2
