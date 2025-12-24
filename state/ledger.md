# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (3 sorries in projective infrastructure)
**Result**: Architecture analysis - discovered issues with serre_duality approach
**Cycle**: 274 (Next)

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

### Cycle 274: Address architecture issues

**Key Discovery (Cycle 273)**: The current serre_duality proof strategy has a flaw:
- It assumes h¹(D) = 0 for ALL D via `globalPlusBoundedSubmodule_full_eq_top`
- This is only true when deg(D) > -2 (for P¹)
- For D = ⟨0, -3⟩: K-D = ⟨0, 1⟩, so L(K-D) = polynomials deg ≤ 1 = dim 2
- Serre duality h¹(D) = ℓ(K-D) gives h¹(⟨0, -3⟩) = 2, NOT 0!

**Sorries remaining** (3 distinct):

1. `globalPlusBoundedSubmodule_full_eq_top` (AdelicH1Full.lean:566)
   - ⚠️ ARCHITECTURE ISSUE: Claims K + A_K(D) = full adeles for ALL D
   - Only true for D with deg(D) > 2g-2 = -2 (for P¹)
   - Needs hypothesis restriction OR different approach

2. `RRSpace_proj_ext_finite` (AdelicH1Full.lean:724)
   - Strategy: pole-clearing multiplication then polynomial embedding
   - When D.finite has positive coefficients, POLES are allowed (not just polynomials)
   - Requires constructing clearing polynomial q = ∏ (generator)^{-D.finite(v)}

3. `serre_duality` non-effective cases (Abstract.lean:300, 304)
   - ⚠️ CANNOT prove as both = 0 for non-effective D
   - Needs actual Serre duality via residue pairing, not both-sides-zero argument

**Recommended approach for Cycle 274**:

**Option A**: Restrict `ProjectiveAdelicRRData` to effective divisors only
- Simpler, covers main P¹ RR use case
- Leave full Serre duality for future work

**Option B**: Implement proper residue pairing for non-effective cases
- More general, but requires significant infrastructure

**Option C**: Focus on `RRSpace_proj_ext_finite` with pole-clearing approach
- Independent of serre_duality issues
- Mechanical proof once clearing polynomial is constructed

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
