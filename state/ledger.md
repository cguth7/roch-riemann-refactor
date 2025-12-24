# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (3 sorries in projective infrastructure, down from 4)
**Result**: Filled `RRSpace_proj_ext_canonical_sub_eq_bot` helper sorry
**Cycle**: 273 (Next)

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
| AdelicH1Full.lean | 2 | Strong approx + finiteness |
| Abstract.lean | 2 | serre_duality non-effective cases |

---

## Next Steps

### Cycle 273: Continue projective infrastructure

**Sorries remaining** (3 distinct, 4 total instances):

1. `globalPlusBoundedSubmodule_full_eq_top` (AdelicH1Full.lean:566)
   - Extends strong approximation to full adeles
   - Deep: requires showing K dense in K_∞ with controlled degree

2. `RRSpace_proj_ext_finite` (AdelicH1Full.lean:704)
   - Show RRSpace_proj_ext is finite-dimensional
   - Should follow RRSpace_ratfunc_projective_effective_finite pattern

3. `serre_duality` non-effective cases (Abstract.lean:277, inside p1ProjectiveAdelicRRData)
   - Case D.finite effective but D.inftyCoeff < 0
   - Case D.finite not effective
   - May be vacuous for P¹ if we only care about effective divisors

**After Cycle 273**:

**Option A**: Prove remaining sorries are vacuous for P¹ RR
**Option B**: Start new curve instance (elliptic or hyperelliptic)
**Option C**: Extend residues to higher-order poles

---

## Cycle 272 Summary ✅

**Task**: Fill projective infrastructure sorries

**Achievement**:
- Filled `RRSpace_proj_ext_canonical_sub_eq_bot` helper sorry
- Used `eq_algebraMap_of_valuation_le_one_forall` from P1VanishingLKD.lean
- Added `D.finite.Effective` hypothesis (necessary for proof)
- Updated downstream theorems:
  - `ell_proj_ext_canonical_sub_eq_zero`
  - `serre_duality_p1`
- Restructured Abstract.lean serre_duality proof to handle effective/non-effective cases separately

**Technical fix**: The original proof assumed D.finite was effective without stating it.
Now `RRSpace_proj_ext_canonical_sub_eq_bot` requires `hDfin : D.finite.Effective`.

**Sorry count**: 4 → 3 (distinct sorries)

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
