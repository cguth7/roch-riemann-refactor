# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (2 sorries in AdelicH1Full.lean)
**Result**: Pole-clearing infrastructure added for RRSpace_proj_ext_finite
**Cycle**: 275 (Next)

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
| AdelicH1Full.lean | 2 | globalPlusBoundedSubmodule_full_eq_top + RRSpace_proj_ext_finite |
| Abstract.lean | 2 | serre_duality non-effective cases |

---

## Next Steps

### Cycle 275: Complete RRSpace_proj_ext_finite

**Target**: Fill `RRSpace_proj_ext_finite` sorry using pole-clearing infrastructure

**Current State** (after Cycle 274):
- ✅ `DivisorV2.positiveSupport` - support of positive D coefficients
- ✅ `clearingPoly` - product of generator^{D(v)} over positive places
- ✅ Basic lemmas: `clearingPoly_ne_zero`, `clearingPoly_monic`, `clearingPoly_natDegree`
- ⏳ Valuation lemmas need filling

**Remaining Work**:
1. Prove valuation lemmas for clearing polynomial:
   - At v with D(v) > 0: v.valuation(clearingPoly) = exp(-D(v))
   - At v with D(v) ≤ 0: v.valuation(clearingPoly) = 1
2. Prove `mul_clearingPoly_integral`: f·clearingPoly is integral at all finite places
3. Complete embedding into Polynomial.degreeLT

**Sorries remaining** (2 in AdelicH1Full.lean):

1. `globalPlusBoundedSubmodule_full_eq_top` (line 567)
   - ⚠️ ARCHITECTURE ISSUE: Claims h¹(D) = 0 for all D (only true for deg(D) > -2)
   - Lower priority - affects non-effective divisors only

2. `RRSpace_proj_ext_finite` (line 765)
   - Strategy documented, infrastructure in place
   - Needs valuation arithmetic to complete

**Strategic Direction (Gemini Review)**:

⚠️ **Option A REJECTED**: Restricting to effective divisors is a retreat that breaks the
roadmap for general curves (elliptic, hyperelliptic). The duality between positive and
negative degree divisors IS the point of the theorem.

**Cycle 274: Execute Option C (Finiteness via Pole-Clearing)**

Target: `RRSpace_proj_ext_finite` in AdelicH1Full.lean

Rationale: Cannot count dimensions (ℓ(D)) until the space is proven finite-dimensional.

Implementation plan:
1. **Pole-Clearing Lemma**: Construct polynomial `q = ∏ generator^{max(0, D.finite(v))}`
   that clears all allowed poles of any f ∈ L(D)
2. **Embedding**: Define L(D) ↪ L(0) (or into polynomial ring mod ideal) via f ↦ f·q
3. **Conclude**: Target is finite-dimensional (already proved), so L(D) is too

**After Cycle 274: Execute Option B (Residue Pairing)**

Target: `serre_duality` in Abstract.lean

Once finiteness is secure:
1. Abandon "both sides = 0" strategy for non-effective divisors
2. Implement actual Residue Pairing: ⟨f, α⟩ = ∑ Res(f·α)
3. Use finiteness to show pairing is perfect → H¹(D) ≅ L(K-D)ᵛ

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
