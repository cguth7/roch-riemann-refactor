import RrLean.RiemannRochV2.ResidueTheory.DifferentIdealBridge

/-!
# Trace Duality and Serre Duality (Track B)

This module connects the dimension of Riemann-Roch spaces to trace duals,
working toward discharging the `serre_duality_eq` axiom in `FullRRData`.

## Strategy

The key mathematical insight is:
- For a fractional ideal I, the trace dual `dual A K_A I` satisfies:
  `x ∈ dual(I) ⟺ ∀ y ∈ I, Tr(xy) ∈ A`
- The trace pairing is nondegenerate for separable extensions
- This gives a duality: `dim_k(I) = dim_k(dual(I))` (in appropriate sense)
- Combined with `div(dual I) = K - div(I)`, we get Serre duality

## Main Results

* `RRSpaceToFractionalIdeal` — L(D) corresponds to divisorToFractionalIdeal(-D)
* `dim_eq_dual_dim` (TODO) — Trace pairing preserves dimensions
* `serre_duality_via_trace` (TODO) — ℓ(D) = ℓ(K-D) relation

## References

* `Mathlib.RingTheory.DedekindDomain.Different` — traceDual, dual_dual, dual_le_dual
* Liu "Algebraic Geometry and Arithmetic Curves" Chapter 7
-/

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable [Algebra k R] [Algebra k K] [IsScalarTower k R K]

/-! ## RRSpace and Fractional Ideal Correspondence

The Riemann-Roch space L(D) = {f ∈ K : div(f) ≥ -D} corresponds to the
fractional ideal I_{-D} = ∏ P_v^{-D(v)}.

More precisely:
- f ∈ L(D) ⟺ v(f) ≥ -D(v) for all v
- This is exactly the condition f ∈ divisorToFractionalIdeal(-D)
-/

section RRSpaceFractionalIdeal

open FractionalIdeal

/-- The fractional ideal corresponding to L(D).

L(D) consists of elements f with v(f) ≥ -D(v) for all v.
This corresponds to the fractional ideal I_{-D} = ∏ P_v^{-D(v)}. -/
noncomputable def RRSpaceFractionalIdeal (D : DivisorV2 R) : FractionalIdeal R⁰ K :=
  divisorToFractionalIdeal R K (-D)

/-- The RRSpace as an R-submodule equals the fractional ideal viewed as a submodule.

This uses `mem_divisorToFractionalIdeal_iff` which characterizes membership in
`divisorToFractionalIdeal R K D` via valuation bounds:
  x ∈ I_D ↔ x = 0 ∨ ∀ v, v.valuation K x ≤ exp(-D v)

For RRSpaceFractionalIdeal R K D = divisorToFractionalIdeal R K (-D):
  x ∈ L(D) ↔ x = 0 ∨ ∀ v, v.valuation K x ≤ exp(D v)

Which matches exactly with `satisfiesValuationCondition R K D f`. -/
lemma RRModuleV2_eq_fractionalIdeal_toSubmodule (D : DivisorV2 R) :
    (RRModuleV2_real R K D).toAddSubmonoid =
      ((RRSpaceFractionalIdeal R K D) : Submodule R K).toAddSubmonoid := by
  -- The proof follows from mem_divisorToFractionalIdeal_iff
  -- which characterizes membership via valuation bounds.
  ext f
  simp only [Submodule.mem_toAddSubmonoid, RRModuleV2_real,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  unfold satisfiesValuationCondition RRSpaceFractionalIdeal
  -- Now we need: (f = 0 ∨ ∀ v, v(f) ≤ exp(D v)) ↔ f ∈ ↑(divisorToFractionalIdeal R K (-D))
  -- By mem_divisorToFractionalIdeal_iff: f ∈ I_E ↔ f = 0 ∨ ∀ v, v(f) ≤ exp(-E v)
  -- For E = -D: f ∈ I_{-D} ↔ f = 0 ∨ ∀ v, v(f) ≤ exp(-(-D v)) = exp(D v)
  -- The coercion from FractionalIdeal to Submodule preserves membership
  rw [FractionalIdeal.mem_coe, mem_divisorToFractionalIdeal_iff]
  -- After rewrite: (f = 0 ∨ ∀ v, v(f) ≤ exp(D v)) ↔ (f = 0 ∨ ∀ v, v(f) ≤ exp(-(-D v)))
  -- Since (-D) v = -(D v) for Finsupp, -(-D v) = D v
  -- Need to show: -(-D v) = D v for DivisorV2 = Finsupp
  have h_neg : ∀ v : HeightOneSpectrum R, -(-D) v = D v := fun v => by
    simp only [Finsupp.coe_neg, Pi.neg_apply, neg_neg]
  simp_rw [h_neg]

end RRSpaceFractionalIdeal

/-! ## Trace Duality for Dimensions

The trace pairing `Tr : K × K → A` is nondegenerate for separable extensions.
This means that for finite-dimensional k-vector spaces, the trace dual
has the same dimension.

Key properties from Mathlib:
- `dual_dual` : dual(dual(I)) = I (involution)
- `dual_le_dual` : dual(I) ≤ dual(J) ↔ J ≤ I (anti-monotone)
- `traceDual_span_of_basis` : trace dual preserves span structure
-/

section TraceDualDimension

variable {R K}
variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
variable (K_A : Type*) [Field K_A] [Algebra A K_A] [IsFractionRing A K_A]
variable [Algebra A R] [Algebra A K] [Algebra K_A K] [NoZeroSMulDivisors A R]
variable [IsScalarTower A K_A K] [IsScalarTower A R K]
variable [FiniteDimensional K_A K] [Algebra.IsSeparable K_A K]
variable [IsIntegralClosure R A K] [IsFractionRing R K]

open FractionalIdeal

-- finrank_dual_eq moved to Archive/SorriedLemmas.lean (wrong approach for Serre duality)
-- See docstring in archive for why this approach doesn't work

/-- The trace dual operation is involutive on fractional ideals. -/
lemma dual_dual_eq (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    dual A K_A (dual A K_A I) = I :=
  FractionalIdeal.dual_dual A K_A I

end TraceDualDimension

/-! ## Serre Duality via Trace

The main goal: prove that ℓ(D) - ℓ(K-D) = deg(D) + 1 - g.

Using the trace dual machinery:
1. L(D) corresponds to fractional ideal I_D
2. dual(I_D) corresponds to L(K - div(I_D)) = L(K - (-D)) = L(K+D)
3. Wait... this doesn't give L(K-D) directly.

Actually, we need to be more careful about conventions.
Let me reconsider...

The correct correspondence for Serre duality is:
- H^0(D)* ≅ H^1(K-D) via residue pairing
- And h^1(D) = h^0(K-D)

In the arithmetic setting:
- L(D)^dual ≅ "H^1(D)" via trace residues
- "H^1(D)" ≅ L(K-D) by definition of K

So the key is to identify "H^1(D)" appropriately.
-/

section SerreDuality

variable {R K}
variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
variable (K_A : Type*) [Field K_A] [Algebra A K_A] [IsFractionRing A K_A]
variable [Algebra A R] [Algebra A K] [Algebra K_A K] [NoZeroSMulDivisors A R]
variable [IsScalarTower A K_A K] [IsScalarTower A R K]
variable [FiniteDimensional K_A K] [Algebra.IsSeparable K_A K]
variable [IsIntegralClosure R A K] [IsFractionRing R K]

-- The key insight connecting L(D) and L(K-D) via trace duality:
--
-- Mathematically: The trace pairing gives
--   L(K-D) ≅ Hom_k(L(D), k)
-- when both are finite-dimensional.
--
-- More precisely, for I = I_{-D} (so L(D) ≅ I as k-spaces):
--   dual(I) corresponds to divisor K - (-D) = K + D
--   But we want L(K-D), not L(K+D).
--
-- The resolution: The trace dual of L(D) is not L(K-D) directly.
-- Instead, we use the RR exact sequence:
--   0 → L(D) → ⊕_v K_v → "H^1(D)" → 0
-- where the "residues at all places" give the cohomology.

-- For now, we state the target theorem assuming the axiom approach works.
-- The full discharge of `serre_duality_eq` requires:
-- 1. Adelic/idelic interpretation of H^1
-- 2. Trace duality at each local factor
-- 3. Global sum formula

/-- Serre duality relates L(D) and L(K-D) dimensions.

This is equivalent to the RR equation:
  ℓ(D) - ℓ(K-D) = deg(D) + 1 - g

The proof uses:
1. L(D) ↔ fractional ideal I with div(I) = -D
2. dual(I) has div = K - div(I) = K + D (by fractionalIdealToDivisor_dual)
3. Connect to L(K-D) via the canonical pairing

This lemma captures the relationship; full proof requires adelic methods.
-/
theorem serre_duality_dimension
    (frr : FullRRData k R K) (D : DivisorV2 R)
    [Module.Finite k (RRSpace_proj k R K D)]
    [Module.Finite k (RRSpace_proj k R K (frr.canonical - D))] :
    (ell_proj k R K D : ℤ) - ell_proj k R K (frr.canonical - D) =
      D.deg + 1 - frr.genus :=
  -- This follows from the FullRRData axiom
  frr.serre_duality_eq D

end SerreDuality

/-! ## Next Steps for Track B (Updated Cycle 90)

**Status**: The trace dual approach in this file provides infrastructure but is
not the correct path to Serre duality. The adelic approach in `Adeles.lean` is
the right direction.

**What this file establishes**:
- ✅ `RRModuleV2_eq_fractionalIdeal_toSubmodule`: L(D) ↔ fractional ideal correspondence
- ✅ `fractionalIdealToDivisor_dual`: div(dual I) = K - div(I)
- ❌ `finrank_dual_eq`: Not the right lemma (dual gives L(K+D), not L(K-D))

**Correct path via Adeles.lean**:

1. **H¹(D) structure** (✅ Cycle 85): `AdelicH1.Space k R K D = A_K ⧸ (K + A_K(D))`

2. **Finiteness** (TODO): Prove `Module.Finite k (AdelicH1.Space k R K D)`
   - Key insight: For large deg(D), H¹(D) = 0 (strong approximation)
   - Use compactness of adele class group A_K/K

3. **Serre duality** (TODO): `AdelicH1.h1_finrank k R K D = ell_proj k R K (K - D)`
   - Local duality: At each place v, residue pairing gives local duality
   - Global piecing: Product formula assembles local dualities

4. **Discharge axiom** (TODO): Instantiate `FullRRData` with proved duality
   - Set `canonical := canonicalDivisorFrom A` from DifferentIdealBridge.lean
   - Set `genus := ell_proj k R K canonical` (ℓ(K) = g)
   - Prove `serre_duality_eq` from h¹(D) = ℓ(K-D)

**Estimated remaining work**: 3-4 cycles for finiteness + Serre duality
-/

end RiemannRochV2
