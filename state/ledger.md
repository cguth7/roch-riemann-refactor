# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ❌ Compile error (needs small fix in AdelicH1Full.lean line 568)
**Result**: Added `exists_local_approximant_with_bound_infty` helper lemma (partial)
**Cycle**: 279 (Next)

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
| AdelicH1Full.lean | 1 | `globalPlusBoundedSubmodule_full_eq_top` (line 582) |
| Abstract.lean | 5 | General abstract infrastructure (h1_finite, ell_finite, etc.) |

---

## Next Steps

### Cycle 279: Fix compile error and complete `globalPlusBoundedSubmodule_full_eq_top`

**Immediate**: Fix `Valued.isClopen_closedBall` call in AdelicH1Full.lean:568
- Current error: wrong argument type to `Valued.isClopen_closedBall`
- Fix: Check the correct Mathlib API for clopen balls in valued rings

**Then complete**: `globalPlusBoundedSubmodule_full_eq_top` (line ~605 after fix)

**Strategy** (from Cycle 278 analysis):
1. Use `exists_local_approximant_with_bound_infty` to approximate at infinity first
2. Apply `strong_approximation_ratfunc` to the adjusted finite adele
3. The key challenge: ensuring k₂ from finite approx doesn't mess up infinity bound

**Key infrastructure available**:
- `exists_local_approximant_with_bound_infty` (lines 561-580): approximation at ∞ with any bound
- `strong_approximation_ratfunc` (RatFuncPairing.lean): approximation at finite places
- `denseRange_inftyRingHom` (FullAdelesCompact.lean): K is dense in K_∞

**After**: Abstract.lean sorries become provable, completing P¹ Riemann-Roch infrastructure

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
