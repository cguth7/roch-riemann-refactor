# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles with 1 sorry (in AdelicH1Full.lean line 582)
**Result**: RRSpace_proj_ext_finite proved - L(D) is finite-dimensional for all extended divisors
**Cycle**: 278 (Next)

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

### Cycle 278: Fill `globalPlusBoundedSubmodule_full_eq_top`

**Target**: Prove that K + A_K(D) = FullAdeleRing for P¹ (strong approximation for full adeles)

**Context**: This is the key lemma showing H¹(D) = 0 for P¹. The proof requires:
1. Strong approximation for finite adeles (already proved)
2. Density of K in K_∞ (completion at infinity)
3. Show the same global k works for both finite and infinity bounds

**After**: Abstract.lean sorries become provable, completing P¹ Riemann-Roch infrastructure

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
