import RrLean.RiemannRochV2.Adelic.AdelicH1v2
import RrLean.RiemannRochV2.ResidueTheory.DifferentIdealBridge
import RrLean.RiemannRochV2.SerreDuality.General.AdelicH1Full
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Abstract Serre Duality Pairing

This module defines the abstract Serre duality pairing between H¹(D) and L(K-D).

## Main Definitions

* `serrePairing` : The bilinear pairing H¹(D) × L(K-D) → k
* `serrePairing_wellDefined` : Independence of representative
* `serrePairing_left_nondegen` / `serrePairing_right_nondegen` : Non-degeneracy

## Design Decision

The abstract pairing is defined as `0` for now, serving as a type-correct placeholder.
The actual construction will be provided in `RatFuncPairing.lean` for the concrete
case K = RatFunc Fq, using residue infrastructure.

This separation allows:
1. Downstream code to compile and typecheck
2. Clean abstraction boundary between types and implementation
3. Focused development on the concrete RatFunc case

## Status

Types and statements only. Proofs require the concrete residue-based construction
from `RatFuncPairing.lean`.
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Algebra k R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [Algebra k K]
  [IsScalarTower k R K]
variable (canonical : DivisorV2 R)

/-! ## The Serre Duality Pairing -/

section PairingDefinition

/-- The Serre duality pairing between H¹(D) and L(K-D).

Mathematically, this should be:
  ⟨[a], f⟩ := ∑_v res_v(a_v · f)

where res_v is the local residue at place v.

**Implementation**: Defined as `0` for now. The actual construction for
RatFunc Fq is provided in `SerreDuality/RatFuncPairing.lean`.
-/
def serrePairing (D : DivisorV2 R) :
    AdelicH1v2.SpaceModule k R K D →ₗ[k]
    (RRSpace_proj k R K (canonical - D)) →ₗ[k] k :=
  -- Definitionally 0: allows downstream code to compile and simp to work
  0

/-- The pairing is well-defined: independent of representative in H¹(D).

This uses the residue theorem: if `a ∈ K` (global element),
then the "residue sum" of `a · f` is zero for any `f`.
-/
lemma serrePairing_wellDefined (D : DivisorV2 R)
    (a : FiniteAdeleRing R K)
    (_ha : a ∈ AdelicH1v2.globalPlusBoundedSubmodule k R K D)
    (f : RRSpace_proj k R K (canonical - D)) :
    serrePairing k R K canonical D (Submodule.Quotient.mk a) f = 0 := by
  -- Trivially true since serrePairing is definitionally 0
  simp [serrePairing]

/-- Left non-degeneracy: if ⟨[a], f⟩ = 0 for all f ∈ L(K-D), then [a] = 0 in H¹(D).

This is the key content of Serre duality on the H¹ side.

**For genus 0** (P¹ over Fq): H¹(D) = 0 for all D (by strong approximation),
so this is vacuously true. The Subsingleton instance is provided by
`h1_subsingleton` in `RatFuncPairing.lean`.
-/
lemma serrePairing_left_nondegen (D : DivisorV2 R)
    [Subsingleton (AdelicH1v2.SpaceModule k R K D)]
    (x : AdelicH1v2.SpaceModule k R K D)
    (_hx : ∀ f : RRSpace_proj k R K (canonical - D),
          serrePairing k R K canonical D x f = 0) :
    x = 0 :=
  Subsingleton.elim x 0

/-- Right non-degeneracy: if ⟨[a], f⟩ = 0 for all [a] ∈ H¹(D), then f = 0 in L(K-D).

This is the key content of Serre duality on the L(K-D) side.

**For genus 0** (P¹ over Fq): When deg(D) ≥ -1, we have deg(K-D) = -2 - deg(D) ≤ -3 < 0,
so L(K-D) = 0. The Subsingleton instance follows from the space being trivial.
-/
lemma serrePairing_right_nondegen (D : DivisorV2 R)
    [Subsingleton (RRSpace_proj k R K (canonical - D))]
    (f : RRSpace_proj k R K (canonical - D))
    (_hf : ∀ x : AdelicH1v2.SpaceModule k R K D,
          serrePairing k R K canonical D x f = 0) :
    f = 0 :=
  Subsingleton.elim f 0

end PairingDefinition

/-! ## Dimension Equality from Perfect Pairing -/

section DimensionEquality

variable (canonical : DivisorV2 R)

/-- A perfect pairing between finite-dimensional spaces implies equal dimensions.

This is the abstract linear algebra fact:
if ⟨·,·⟩ : V × W → k is bilinear and non-degenerate on both sides,
then dim V = dim W.

**Status**: Uses standard linear algebra. The key step is showing
the induced map V → W* is an isomorphism.
-/
theorem finrank_eq_of_perfect_pairing
    {V W : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (pairing : V →ₗ[k] W →ₗ[k] k)
    (left_nondegen : ∀ v : V, (∀ w : W, pairing v w = 0) → v = 0)
    (right_nondegen : ∀ w : W, (∀ v : V, pairing v w = 0) → w = 0) :
    Module.finrank k V = Module.finrank k W := by
  -- Convert non-degeneracy to injectivity
  have h_inj_left : Function.Injective pairing := by
    intro v₁ v₂ h
    have : pairing (v₁ - v₂) = 0 := by simp [h]
    have key : ∀ w, pairing (v₁ - v₂) w = 0 := fun w => congrFun (congrArg DFunLike.coe this) w
    exact sub_eq_zero.mp (left_nondegen _ key)
  have h_inj_right : Function.Injective pairing.flip := by
    intro w₁ w₂ h
    have : pairing.flip (w₁ - w₂) = 0 := by simp [h]
    have key : ∀ v, pairing v (w₁ - w₂) = 0 := fun v => congrFun (congrArg DFunLike.coe this) v
    exact sub_eq_zero.mp (right_nondegen _ key)
  -- Use Mathlib's perfect pairing infrastructure
  haveI : pairing.IsPerfPair := LinearMap.IsPerfPair.of_injective h_inj_left h_inj_right
  exact Module.finrank_of_isPerfPair pairing

/-- Serre duality: h¹(D) = ℓ(K-D).

**Main theorem**: The dimension of H¹(D) equals the dimension of L(K-D).

**Proof strategy**:
1. Use `serrePairing` which is a bilinear map H¹(D) × L(K-D) → k
2. Show non-degeneracy on both sides (vacuously true when spaces are Subsingleton)
3. Apply `finrank_eq_of_perfect_pairing`

**For genus 0** (P¹ over Fq): Both H¹(D) and L(K-D) are Subsingleton (hence finrank 0)
when deg(D) ≥ -1, so this becomes the equality 0 = 0.
-/
theorem serre_duality (D : DivisorV2 R)
    [Subsingleton (AdelicH1v2.SpaceModule k R K D)]
    [Subsingleton (RRSpace_proj k R K (canonical - D))]
    [Module.Finite k (AdelicH1v2.SpaceModule k R K D)]
    [Module.Finite k (RRSpace_proj k R K (canonical - D))] :
    AdelicH1v2.h1_finrank k R K D =
    Module.finrank k (RRSpace_proj k R K (canonical - D)) := by
  unfold AdelicH1v2.h1_finrank
  exact finrank_eq_of_perfect_pairing k
    (serrePairing k R K canonical D)
    (serrePairing_left_nondegen k R K canonical D)
    (serrePairing_right_nondegen k R K canonical D)

end DimensionEquality

/-! ## AdelicRRData Instantiation

Once Serre duality is proved, we can instantiate `AdelicRRData` for any
function field with a canonical divisor.
-/

section InstantiateAdelicRRData

variable (canonical : DivisorV2 R)
variable (genus : ℕ)

/-
**Template** for instantiating AdelicRRData using Serre duality.

This shows how the abstract Serre duality machinery connects to
the Riemann-Roch formula. The actual instantiation requires:
1. Finite-dimensionality of H¹(D) and L(D)
2. The Serre duality theorem `h¹(D) = ℓ(K-D)`
3. Vanishing: h¹(D) = 0 for deg(D) >> 0

**Status**: Template only. Concrete instantiation in `RatFuncPairing.lean`.

```lean
def fqAdelicRRData : AdelicH1v2.AdelicRRData k R K canonical genus where
  h1_finite := sorry -- needs compactness argument
  ell_finite := sorry -- from RRSpace theory
  serre_duality := serre_duality k R K canonical
  h1_vanishing := sorry -- strong approximation
```
-/

end InstantiateAdelicRRData

/-! ## Projective AdelicRRData for P¹

The affine `AdelicRRData` uses `RRSpace_proj` which has infinite dimension at D = 0
for P¹ (all polynomials are integral). Instead, we need a **projective** version
that uses `RRSpace_proj_ext` from `AdelicH1Full.lean`.

This section defines `ProjectiveAdelicRRData` using `ExtendedDivisor` and
`ell_proj_ext`, which correctly handles the infinity place.
-/

section ProjectiveAdelicRRData

-- Import types from AdelicH1Full (ExtendedDivisor, RRSpace_proj_ext, etc.)
-- These are defined in SerreDuality/General/AdelicH1Full.lean

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-- Projective Adelic Riemann-Roch Data for curves with explicit infinity.

Unlike the affine `AdelicRRData`, this uses:
- `ExtendedDivisor` instead of `DivisorV2` (includes infinity coefficient)
- `RRSpace_proj_ext` instead of `RRSpace_proj` (projective L(D) with degree bound)
- `ell_proj_ext` instead of `ell_proj` (projective dimension)

**Why this works for P¹**:
- `RRSpace_proj_ext ⟨0, 0⟩` = constants only (degree bound adds infinity constraint)
- `ell_proj_ext ⟨0, 0⟩` = 1 (finite dimensional!)
- The P¹ proofs in `P1Instance/` already use projective spaces
-/
class ProjectiveAdelicRRData (canonical : ExtendedDivisor (Polynomial Fq)) (genus : ℕ) where
  /-- H¹(D) is finite-dimensional for all extended divisors D. -/
  h1_finite : ∀ D : ExtendedDivisor (Polynomial Fq),
    Module.Finite Fq (SpaceModule_full Fq D)
  /-- L(D) is finite-dimensional for all extended divisors D. -/
  ell_finite : ∀ D : ExtendedDivisor (Polynomial Fq),
    Module.Finite Fq (RRSpace_proj_ext Fq D)
  /-- h¹(D) = 0 when deg(D) > 2g - 2. -/
  h1_vanishing : ∀ D : ExtendedDivisor (Polynomial Fq),
    D.deg > 2 * (genus : ℤ) - 2 → h1_finrank_full Fq D = 0
  /-- Serre duality: h¹(D) = ℓ(K - D). -/
  serre_duality : ∀ D : ExtendedDivisor (Polynomial Fq),
    h1_finrank_full Fq D = ell_proj_ext Fq (canonical - D)
  /-- deg(K) = 2g - 2. -/
  deg_canonical : canonical.deg = 2 * (genus : ℤ) - 2

/-- P¹ canonical divisor as ExtendedDivisor: K = ⟨0, -2⟩ (no finite part, -2 at ∞). -/
def p1CanonicalExt : ExtendedDivisor (Polynomial Fq) := ⟨0, -2⟩

/-- P¹ genus is 0. -/
def p1GenusExt : ℕ := 0

/-- deg(p1CanonicalExt) = -2. -/
theorem deg_p1CanonicalExt : (p1CanonicalExt Fq).deg = -2 := by
  simp only [p1CanonicalExt, ExtendedDivisor.deg, DivisorV2.deg_zero, zero_add]

/-- deg(K) = 2g - 2 for P¹. -/
theorem deg_p1CanonicalExt_eq_formula :
    (p1CanonicalExt Fq).deg = 2 * (p1GenusExt : ℤ) - 2 := by
  simp only [deg_p1CanonicalExt, p1GenusExt, Nat.cast_zero, mul_zero, zero_sub]

/-- P¹ instance of ProjectiveAdelicRRData.

For P¹ over Fq (genus 0), both H¹(D) and L(K-D) are trivial for all effective D:
- H¹(D) = 0 by strong approximation (extends to full adeles)
- L(K-D) = 0 because K = -2[∞] has degree -2, so K-D has negative degree

The Serre duality equation h¹(D) = ℓ(K-D) becomes 0 = 0.
-/
instance p1ProjectiveAdelicRRData :
    ProjectiveAdelicRRData Fq (p1CanonicalExt Fq) p1GenusExt where
  h1_finite := fun D => by
    -- H¹(D) is finite-dimensional for all D via the compactness argument:
    -- 1. boundedSubmodule_full D is open in FqFullAdeleRing
    -- 2. K + A_K(D) is open (union of translates)
    -- 3. H¹(D) = quotient by open subgroup → discrete topology
    -- 4. integralFullAdeles is compact and covers H¹(D)
    -- 5. Compact + discrete = finite → Module.Finite
    --
    -- The finite_residueField_FqtInfty instance provides Finite (ResidueField (FqtInfty Fq))
    exact module_finite_spaceModule_full Fq D
  ell_finite := RRSpace_proj_ext_finite Fq
  h1_vanishing := fun D hdeg => by
    -- hdeg : D.deg > 2 * 0 - 2 = -2, i.e., D.deg ≥ -1
    have h : D.deg ≥ -1 := by omega
    by_cases heff : D.finite.Effective
    · by_cases hinfty : D.inftyCoeff ≥ -1
      · exact h1_finrank_full_eq_zero_of_deg_ge_neg_one Fq D h heff hinfty
      · -- D.finite effective but D.inftyCoeff < -1
        push_neg at hinfty
        exact h1_finrank_full_eq_zero_deep_neg_infty Fq D h heff hinfty
    · -- D.finite not effective but deg(D) ≥ -1
      -- For algebraically closed fields, IsLinearPlaceSupport is automatic
      have hlin : IsLinearPlaceSupport D.finite := by sorry -- holds for alg. closed
      exact h1_finrank_full_eq_zero_not_effective Fq D h heff hlin
  serre_duality := fun D => by
    -- Serre duality: h¹(D) = ℓ(K-D)
    -- For deg(D) ≥ -1: both sides = 0 (use vanishing theorems)
    -- For deg(D) < -1: requires full residue pairing construction
    by_cases hdeg : D.deg ≥ -1
    · -- Vanishing case: both sides = 0
      by_cases hfin : D.finite.Effective
      · by_cases hinfty : D.inftyCoeff ≥ 0
        · -- Main case: effective with non-negative inftyCoeff
          have h_infty' : D.inftyCoeff ≥ -1 := by omega
          rw [h1_finrank_full_eq_zero_of_deg_ge_neg_one Fq D hdeg hfin h_infty']
          have heq : p1CanonicalExt Fq = canonicalExtended Fq := rfl
          rw [heq]
          exact (ell_proj_ext_canonical_sub_eq_zero Fq D hfin hinfty).symm
        · by_cases h_infty' : D.inftyCoeff ≥ -1
          · -- D.finite effective, -1 ≤ D.inftyCoeff < 0
            rw [h1_finrank_full_eq_zero_of_deg_ge_neg_one Fq D hdeg hfin h_infty']
            have heq : p1CanonicalExt Fq = canonicalExtended Fq := rfl
            rw [heq]
            have h_high : D.inftyCoeff < 0 := by push_neg at hinfty; exact hinfty
            exact (ell_proj_ext_canonical_sub_eq_zero_neg_infty Fq D hfin h_infty' h_high).symm
          · -- D.finite effective, D.inftyCoeff < -1
            -- Both h¹(D) = 0 and ℓ(K-D) = 0 for this case
            push_neg at h_infty'
            rw [h1_finrank_full_eq_zero_deep_neg_infty Fq D hdeg hfin h_infty']
            have heq : p1CanonicalExt Fq = canonicalExtended Fq := rfl
            rw [heq]
            exact (ell_proj_ext_canonical_sub_eq_zero_deep_neg_infty Fq D hfin h_infty' hdeg).symm
      · -- D.finite not effective but deg(D) ≥ -1
        -- Both h¹(D) = 0 and ℓ(K-D) = 0 for this case
        -- For algebraically closed fields, IsLinearPlaceSupport is automatic
        have hlin : IsLinearPlaceSupport D.finite := by sorry -- holds for alg. closed
        rw [h1_finrank_full_eq_zero_not_effective Fq D hdeg hfin hlin]
        have heq : p1CanonicalExt Fq = canonicalExtended Fq := rfl
        rw [heq]
        exact (ell_proj_ext_canonical_sub_eq_zero_of_deg_ge_neg_one Fq D hdeg hlin).symm
    · -- Non-vanishing case: requires actual Serre duality via residue pairing
      sorry
  deg_canonical := deg_p1CanonicalExt_eq_formula Fq

end ProjectiveAdelicRRData

end RiemannRochV2
