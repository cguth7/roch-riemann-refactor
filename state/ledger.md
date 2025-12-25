# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (with expected sorries)
**Result**: Proof structure for full strong approximation complete, 1 sorry remaining
**Cycle**: 280 (In Progress)

---

## What's Proved

```lean
-- General dimension formula for ALL effective divisors
theorem ell_ratfunc_projective_eq_degWeighted_plus_one (D : DivisorV2 (Polynomial k))
    (hD : D.Effective) :
    ell_ratfunc_projective D = (degWeighted k D).toNat + 1

-- Full Riemann-Roch for P¹
theorem riemann_roch_p1 (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    (ell_ratfunc_projective D : ℤ) - (ellV3 (p1Canonical Fq - DivisorV3.ofAffine D) : ℤ) =
    D.deg + 1 - (p1Genus : ℤ)

-- Traced residue = classical residue (for linear places)
theorem tracedResidueAtPlace_eq_residueAt_linear (α : Fq) (f : RatFunc Fq)
    (hf : hasSimplePoleAt Fq (linearPlace Fq α) f ∨ ¬hasPoleAt Fq (linearPlace Fq α) f) :
    tracedResidueAtPlace Fq (linearPlace Fq α) f = residueAt α f

-- L(K-D) = 0 for effective D on P¹ (Cycle 272 - now with proper hypothesis)
theorem RRSpace_proj_ext_canonical_sub_eq_bot
    (D : ExtendedDivisor (Polynomial Fq)) (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    RRSpace_proj_ext Fq (canonicalExtended Fq - D) = ⊥
```

---

## Sorries

| Location | Count | Status |
|----------|-------|--------|
| P1Instance/ | 0 | ✅ Complete |
| ResidueTrace.lean | 0 | ✅ Complete |
| AdelicH1Full.lean | 1 | Line 677: `|k₂|_∞ ≤ exp(D.inftyCoeff)` for strong approx k₂ |
| Abstract.lean | 5 | General abstract infrastructure (h1_finite low-deg case, serre_duality cases) |

---

## Next Steps

### Cycle 280 (In Progress): Complete infinity valuation bound for k₂

**Goal**: Fill the remaining sorry at line 677 in `globalPlusBoundedSubmodule_full_eq_top_of_deg_ge_neg_one`

**What's been done**:
- ✅ Proof structure complete using two-step approach
- ✅ Step 1: k₁ from `exists_local_approximant_with_bound_infty` approximates a.2 at infinity
- ✅ Step 2: k₂ from `strong_approximation_ratfunc` handles finite places for (a.1 - diag(k₁))
- ✅ Ultrametric inequality reduces to: |k₂|_∞ ≤ exp(D.inftyCoeff)

**Remaining sorry**: Prove `Valued.v (inftyRingHom Fq k₂) ≤ WithZero.exp D.inftyCoeff`

**Mathematical Analysis**:

The key insight: k₂ = k_pole + p where:
- k_pole = Σ principal parts at linear places → intDegree ≤ -1 → |k_pole|_∞ ≤ exp(-1)
- p = CRT polynomial (if D.finite has negative coefficients)

**For effective D.finite** (all coefficients ≥ 0):
- No CRT polynomial needed, k₂ = k_pole
- |k₂|_∞ ≤ exp(-1) ≤ exp(D.inftyCoeff) since D.inftyCoeff ≥ -1 (from deg(D) ≥ -1)
- This case should be straightforward to prove

**For non-effective D.finite** (some D.finite(v) < 0):
- CRT polynomial has degree bounded by Σ_{D.finite(v) < 0} |D.finite(v)|
- Need more careful analysis to show compatibility with D.inftyCoeff
- The constraint deg(D) ≥ -1 should provide the necessary slack

**Recommended approach for completion**:
1. First prove the effective case (should be direct from principal part properties)
2. Then handle non-effective case using CRT degree bounds

**After**: Complete remaining Abstract.lean sorries for full Serre duality

---

## Cycle 280 Summary (In Progress)

**Task**: Complete `globalPlusBoundedSubmodule_full_eq_top_of_deg_ge_neg_one`

**Progress**:

1. **Implemented two-step proof structure**:
   - Step 1: Use `exists_local_approximant_with_bound_infty` for k₁ with |a.2 - k₁|_∞ ≤ exp(D.inftyCoeff)
   - Step 2: Use `strong_approximation_ratfunc` for k₂ on shifted finite adele (a.1 - diag(k₁))
   - Set k = k₁ + k₂ as the global approximant

2. **Proved finite places condition**:
   - (a - diag(k)).1 = (a.1 - diag(k₁)) - diag(k₂) which is D.finite-bounded by construction

3. **Reduced infinity condition to key lemma**:
   - By ultrametric: |a.2 - k|_∞ ≤ max(|a.2 - k₁|_∞, |k₂|_∞)
   - First term bounded by hk₁
   - Reduces to proving: |k₂|_∞ ≤ exp(D.inftyCoeff)

4. **Identified mathematical structure**:
   - For effective D.finite: k₂ = sum of principal parts, has intDegree ≤ -1
   - For non-effective D.finite: k₂ = principal parts + CRT polynomial
   - The deg(D) ≥ -1 constraint ensures compatibility

**Blocking issue**: Need to prove |k₂|_∞ ≤ exp(D.inftyCoeff) using properties of strong_approximation_ratfunc

**Build status**: ✅ Compiles with 1 sorry in AdelicH1Full.lean

---

## Cycle 279 Summary ✅

**Task**: Fix compile error and correct mathematical error in H¹(D) vanishing

**Achievement**:

1. **Fixed compile error** at line 568:
   - Issue: `Valued.isClopen_closedBall` API mismatch
   - Fix: Pass `(R := FqtInfty Fq)` explicitly and use nonzero proof `h_exp_ne`

2. **Corrected critical mathematical error**:
   - Old theorem `globalPlusBoundedSubmodule_full_eq_top` claimed H¹(D) = 0 for ALL D
   - This was **FALSE** - contradicts Riemann-Roch for low-degree divisors
   - Example: D = ⟨0, -3⟩ gives H¹(D) ≅ L(K-D)ᵛ = L(1[∞])ᵛ which has dimension 2

3. **Refactored to mathematically correct version**:
   - Renamed to `globalPlusBoundedSubmodule_full_eq_top_of_deg_ge_neg_one`
   - Added hypothesis: `(hdeg : D.deg ≥ -1)`
   - Threshold deg ≥ -1 comes from Serre vanishing: H¹(D) = 0 iff deg(D) > 2g-2 = -2

4. **Updated downstream theorems**:
   - `SpaceModule_full_subsingleton_of_deg_ge_neg_one`
   - `SpaceModule_full_finite_of_deg_ge_neg_one`
   - `h1_finrank_full_eq_zero_of_deg_ge_neg_one`
   - `serre_duality_p1` (now derives degree bound from effectivity hypotheses)

5. **Updated Abstract.lean**:
   - `p1ProjectiveAdelicRRData` now correctly uses conditional theorems
   - Added case analysis for degree bounds
   - Documented remaining sorries for non-vanishing cases

**Key lesson**: The universal vanishing H¹(D) = 0 only holds for deg(D) ≥ -1 on P¹.
Below this threshold, Serre duality requires the actual residue pairing construction.

---

## Cycle 278 Summary (Partial)

**Task**: Fill `globalPlusBoundedSubmodule_full_eq_top`

**Progress**:
- Added `FullStrongApproximation` section to AdelicH1Full.lean
- Added `exists_local_approximant_with_bound_infty`: approximation at infinity with arbitrary bounds
  - Uses density of K in FqtInfty plus clopen balls in valued rings
- Analyzed proof strategy for full strong approximation
- Removed broken `exists_fractional_part_small_infty` lemma (API issues)

**Blocking issue**:
- `Valued.isClopen_closedBall` API mismatch at line 568
- Need to find correct Mathlib signature for clopen balls

**Key insight from analysis**:
The proof requires a two-step process:
1. First approximate at infinity: find k₁ with |a.2 - k₁|_∞ ≤ exp(D.inftyCoeff)
2. Then handle finite places on (a.1 - diag(k₁)) using strong_approximation_ratfunc
3. Set k = k₁ + k₂ and verify both bounds hold

The challenge is that k₂ might have large infinity valuation that disrupts step 1.
Need to either bound |k₂|_∞ or use a clever construction.

---

## Cycle 277 Summary ✅

**Task**: Fix Module.Finite instance synthesis for Polynomial.degreeLT

**Achievement**:
- Fixed `Module.Finite Fq (Polynomial.degreeLT Fq n)` by using `Module.Finite.equiv`
- Key insight: Use the linear equivalence `degreeLTEquiv : degreeLT Fq n ≃ₗ[Fq] Fin n → Fq`
- Since `Fin n → Fq` has `Module.Finite` (via pi instance), transport via equivalence

**Solution**:
```lean
haveI hdegreeLT_fin : Module.Finite Fq (Polynomial.degreeLT Fq n) :=
  Module.Finite.equiv (Polynomial.degreeLTEquiv Fq n).symm
```

**Key lesson**: When instance resolution fails for a computed type like `degreeLT Fq (bound.toNat + 1)`,
explicitly construct the instance using linear equivalences rather than trying `inferInstance`.

**Sorry count**: 2 → 1 (RRSpace_proj_ext_finite now proved!)

---

## Cycle 275 Summary ✅

**Task**: Complete RRSpace_proj_ext_finite using pole-clearing infrastructure

**Achievement**:
- Proved `clearingPoly_intValuation_at_pos`: At v with D(v) > 0, valuation = exp(-D(v))
- Proved `clearingPoly_intValuation_at_nonpos`: At v with D(v) ≤ 0, valuation = 1
- Proved `mul_clearingPoly_valuation_le_one`: f·clearingPoly is integral at all finite places
- Defined embedding ψ : L(D) →ₗ Polynomial.degreeLT using f ↦ (f·q).num
- Proved ψ is injective (key for finiteness)
- Completed finiteness proof structure using `Module.Finite.of_injective`

---

## Cycle 274 Summary ✅

**Task**: Implement pole-clearing infrastructure for RRSpace_proj_ext_finite

**Achievement**:
- Added PlaceDegree import to AdelicH1Full.lean
- Defined `DivisorV2.positiveSupport`: the set of places where D(v) > 0
- Defined `clearingPoly`: ∏_{D(v) > 0} generator(v)^{D(v).toNat}
- Proved `clearingPoly_ne_zero`: clearing polynomial is nonzero
- Proved `clearingPoly_monic`: clearing polynomial is monic
- Proved `clearingPoly_natDegree`: degree = Σ D(v) · deg(v) over positive places

---

## Cycle 273 Summary ✅

**Task**: Analyze remaining sorries and attempt to fill one

**Achievement**: Architecture analysis revealed fundamental issues:

1. **Serre duality approach flaw discovered**:
   - Current code assumes h¹(D) = 0 for ALL D (via `globalPlusBoundedSubmodule_full_eq_top`)
   - This is FALSE for non-effective D (e.g., D = ⟨0, -3⟩ gives h¹(D) = 2)
   - The "both sides = 0" proof strategy only works for effective divisors
   - Full Serre duality requires actual residue pairing, not triviality argument

2. **RRSpace_proj_ext_finite complexity**:
   - When D.finite(v) > 0, POLES are allowed at place v (exp(D.finite(v)) > 1)
   - Elements are NOT necessarily polynomials when D.finite has positive coefficients
   - Correct approach: pole-clearing multiplication by ∏ generator^{max(0, D.finite(v))}

---

## Cycle 272 Summary ✅

**Task**: Fill projective infrastructure sorries

**Achievement**:
- Filled `RRSpace_proj_ext_canonical_sub_eq_bot` helper sorry
- Used `eq_algebraMap_of_valuation_le_one_forall` from P1VanishingLKD.lean
- Added `D.finite.Effective` hypothesis (necessary for proof)

---

*For cycles 1-271, see previous ledger entries or `ledger_archive.md`*
