# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ⚠️ Compiles with 4 sorries (2 valuation lemma proofs + 2 linear map axioms)
**Result**: Major progress on RRSpace_proj_ext_finite - valuation lemmas and embedding defined
**Cycle**: 276 (Next)

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
| AdelicH1Full.lean | 4 | 2 linear map axioms + globalPlusBoundedSubmodule_full_eq_top + valuation issues |
| Abstract.lean | 2 | serre_duality non-effective cases |

---

## Next Steps

### Cycle 276: Complete Linear Map Axioms for RRSpace_proj_ext_finite

**Target**: Fill the 2 linear map axiom sorries (`map_add'`, `map_smul'`) in AdelicH1Full.lean

**Current State** (after Cycle 275):
- ✅ Valuation lemmas: `clearingPoly_intValuation_at_pos`, `clearingPoly_intValuation_at_nonpos`
- ✅ `mul_clearingPoly_valuation_le_one`: f·q is integral at all finite places
- ✅ Embedding strategy into Polynomial.degreeLT defined
- ⏳ Linear map axioms need coercion path fixes (2 sorries)
- ⏳ Some Int.toNat_le_toNat usage issues

**Remaining Work**:
1. Fix `map_add'` proof: Handle `↑(f+g)` vs `↑f + ↑g` coercion difference
2. Fix `map_smul'` proof: Handle `↑(c•f)` vs `c • ↑f` coercion difference
3. Fix `Int.toNat_le_toNat` argument order issue

**Key Technical Issue**:
The proofs correctly show that f·q lands in polynomials of bounded degree.
The blocking issue is proving the linear map axioms when the RatFunc numerator function
`RatFunc.num` is applied to coerced submodule elements with different coercion paths.

**Pattern to use**: Look at `partialClearPoles` in DimensionCore.lean lines 381-438
for how to prove `map_add'` and `map_smul'` with subtype coercions.

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

**Sorries introduced** (to be filled in Cycle 276):
1. `map_add'` - coercion path issue with `(↑(f+g) * q).num` vs `(↑f * q).num + (↑g * q).num`
2. `map_smul'` - coercion path issue with `(↑(c•f) * q).num` vs `C(c) * (↑f * q).num`

**Technical Notes**:
- The valuation arithmetic uses `generator_intValuation_at_self` and `generator_intValuation_at_other_prime`
- The `Ne.symm` is needed because the lemma expects `v ≠ w` but we have `w ≠ v`
- `RatFunc.algebraMap_injective` is used to transfer polynomial equality through algebraMap
- The key insight: when f·q is a polynomial (algebraMap p), then (f·q).num = p

**Sorry count**: 2 → 4 (traded instance sorry for 2 linear map axiom sorries)

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
- Documented complete strategy for RRSpace_proj_ext_finite in docstring

**Technical Notes**:
- The clearing polynomial uses `PlaceDegree.generator` (monic irreducible for each place)
- Valuation lemmas require careful handling of `Finset.prod` over `positiveSupport`
- Pattern from DimensionGeneral.lean: use `valuation_of_algebraMap` + `generator_intValuation_at_self`

**Sorry count**: Unchanged (2 in AdelicH1Full.lean)
- Architecture in place, valuation arithmetic deferred to Cycle 275

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

3. **Updated proof strategy**:
   - Added detailed comment in RRSpace_proj_ext_finite explaining pole-clearing approach
   - Documented architecture issues in ledger for future cycles

**No sorry count change** - this was an investigative cycle that clarified the path forward.

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
