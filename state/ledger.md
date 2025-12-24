# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (0 sorries in P1Instance, 0 sorries in ResidueTrace.lean, 4 new sorries in projective infrastructure)
**Result**: ProjectiveAdelicRRData class + P¹ instance created (sorries for full adele strong approx)
**Cycle**: 272 (Next)

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
```

---

## Sorries

| Location | Count | Status |
|----------|-------|--------|
| P1Instance/ | 0 | ✅ Complete |
| ResidueTrace.lean | 0 | ✅ Complete |
| Abstract.lean | 0 | ✅ (template sorries were in comments) |

**Cycle 271 Discovery**: The "3 sorries" were in a **comment block** template.
That template (`fqAdelicRRData`) can't work for P¹ anyway - affine trap!
Created `ProjectiveAdelicRRData` class instead.

---

## Next Steps

### Cycle 272: Fill projective infrastructure sorries

**Status**: 4 sorries to fill

**Sorries remaining**:
1. `globalPlusBoundedSubmodule_full_eq_top` (AdelicH1Full.lean:580)
   - Extends strong approximation to full adeles
   - Key: show k from strong_approx has bounded infinity valuation

2. `RRSpace_proj_ext_canonical_sub_eq_bot` helper (AdelicH1Full.lean:641)
   - Show f with valuation bounds at finite places is polynomial
   - Uses: f integral at all finite places → f ∈ Polynomial Fq

3. `RRSpace_proj_ext_finite` (AdelicH1Full.lean:704)
   - Show RRSpace_proj_ext is finite-dimensional
   - Bridge to existing RRSpace_ratfunc_projective finiteness

4. `serre_duality` D.inftyCoeff < 0 case (Abstract.lean:305)
   - Handle negative infinity coefficients
   - May need to analyze L(K-D) for these cases

**After Cycle 272**:

**Option A**: Start new curve instance (elliptic or hyperelliptic)
**Option B**: Extend residues to higher-order poles

---

## Cycle 271 Summary ✅

**Task**: Create ProjectiveAdelicRRData class and P¹ instance

**Achievement**:
- Created `ProjectiveAdelicRRData` class in Abstract.lean using:
  - `ExtendedDivisor` (includes infinity coefficient)
  - `RRSpace_proj_ext` (projective L(D) with degree bound)
  - `SpaceModule_full` (H¹ using full adeles)
- Created P¹ instance `p1ProjectiveAdelicRRData`
- Added infrastructure lemmas in AdelicH1Full.lean:
  - `SpaceModule_full_subsingleton` (H¹ = 0 for P¹)
  - `ell_proj_ext_canonical_sub_eq_zero` (L(K-D) = 0 for effective D)
  - `serre_duality_p1` (0 = 0 for P¹)

**4 sorries introduced** (structural, for future cycles):
1. `globalPlusBoundedSubmodule_full_eq_top` - strong approx for full adeles
2. `RRSpace_proj_ext_canonical_sub_eq_bot` helper - f is polynomial
3. `RRSpace_proj_ext_finite` - finiteness
4. `serre_duality` negative inftyCoeff case

---

## Cycle 270 Summary ✅

**Task**: Fill `tracedResidueAtPlace_eq_residueAt_linear` sorry (stuck for 2 cycles)

**Fix**: The blocking `hq'_inv_eq` lemma was proved using `PowerSeries.mul_inv_cancel`
+ `IsUnit.mul_right_inj` instead of failed approaches with `map_inv₀` or `Units.val_inv_eq_inv_val`.

---

## Cycle 265-269 Summary

- **265**: Filled `ell_ratfunc_projective_gap_eq` → 0 sorries in P1Instance
- **266**: Refactored Residue.lean (1,385 lines → 5 focused files)
- **267**: Filled `trace_degree_one_eq`, created ResidueTrace.lean
- **268**: Defined `localResidueAtPlace`, `tracedResidueAtPlace` for arbitrary places
- **269-270**: Filled `tracedResidueAtPlace_eq_residueAt_linear`

---

*For cycles 1-264, see `ledger_archive.md`*
