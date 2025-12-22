# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (0 sorries in main path)
**Result**: Restricted P¹ Riemann-Roch (linear places only)
**Cycle**: 250

---

## What's Proved

```lean
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective D = D.deg.toNat + 1
```

For effective divisors D with **linear support only**, dim L(D) = deg(D) + 1.

---

## Limitations

**This is NOT full P¹ Riemann-Roch.**

The `IsLinearPlaceSupport` hypothesis restricts to divisors supported at Fq-rational points:

```lean
def IsLinearPlaceSupport (D : DivisorV2 (Polynomial Fq)) : Prop :=
  ∀ v ∈ D.support, ∃ α : Fq, v = linearPlace α
```

Not covered:
- Places of degree > 1 (e.g., (X² + X + 1) over F₂)
- Divisors mixing linear and non-linear places

Full P¹ RR is mathematically trivial - the "vibe coding" methodology is more interesting than the result.

---

## Cycle 250 Summary

**Task**: Create `DivisorV3.lean` - projective divisors using unified Place type

**New File**: `RrLean/RiemannRochV2/Core/DivisorV3.lean`

Created projective divisors that include both finite and infinite places:

```lean
/-- A projective divisor on a curve is a finitely supported function from all places to ℤ. -/
abbrev DivisorV3 := Place R K →₀ ℤ
```

**Key definitions**:
- `DivisorV3.deg`: Degree (sum of all coefficients)
- `DivisorV3.degFinite`: Degree contribution from finite places
- `DivisorV3.degInfinite`: Degree contribution from infinite places
- `DivisorV3.Effective`: Non-negative divisors
- `DivisorV3.ofAffine`: Embedding from DivisorV2 (affine) to DivisorV3 (projective)
- `DivisorV3.singleFinite`, `DivisorV3.singleInfinite`: Single-place divisors

**Key lemmas**:
- `deg_eq_degFinite_add_degInfinite`: Total degree = finite + infinite contributions
- `finiteFilter_add_infiniteFilter`: Divisor = finiteFilter + infiniteFilter
- `deg_ofAffine`: Embedding preserves degree
- `ofAffine_effective`: Embedding preserves effectivity

**Verification**:
```bash
lake build RrLean.RiemannRochV2.Core.DivisorV3  # ✅
lake build RrLean.RiemannRochV2.SerreDuality.Smoke  # ✅ Still passes
```

---

## Cycle 249 Summary (Previous)

**Task**: Create `Place.lean` - unified Place type for Phase 3

**New File**: `RrLean/RiemannRochV2/Core/Place.lean`

Created the foundational type for projective Riemann-Roch:

```lean
/-- An infinite place on a function field K. -/
structure InfinitePlace (K : Type*) [Field K] where
  val : Valuation K (WithZero (Multiplicative ℤ))
  deg : ℕ
  deg_pos : 0 < deg

/-- A place on a curve is either finite or infinite. -/
inductive Place (R : Type*) (K : Type*) ...
  | finite : HeightOneSpectrum R → Place R K
  | infinite : InfinitePlace K → Place R K
```

**Key definitions**:
- `Place.valuation`: Dispatches to finite or infinite valuation
- `Place.isFinite`, `Place.isInfinite`: Classification predicates
- `HasInfinitePlaces`: Typeclass for curves with infinite places
- `HasInfinitePlaces.allPlaces`: Combined finite + infinite places

---

## Cycle 248 Summary (Previous)

**Task**: Investigate Abstract.lean sorries and plan next steps

**Key Discovery**: The Abstract.lean "sorries" are in a **docstring template**, not actual code.

**CRITICAL CORRECTION** (from Gemini review):

The current `AdelicRRData` framework is **broken for ALL projective curves**, not just P¹:

| Curve Type | Coordinate Ring R | Missing Place(s) |
|------------|-------------------|------------------|
| P¹ | k[t] | ∞ |
| Elliptic | k[x,y]/(y²-x³-ax-b) | Point O at infinity |
| Hyperelliptic | k[x,y]/(y²-f(x)) | 1-2 points at infinity |

**The Affine Trap**: Any Dedekind domain R models the AFFINE part of a curve.
`HeightOneSpectrum R` = finite places only. The framework currently computes
**Affine Riemann-Roch**, not Projective Riemann-Roch.

**Implication**: Abstract.lean sorries CANNOT be filled for any projective curve
until Phase 3 (Place type) is complete. Phase 3 is not optional cleanup - it's
required infrastructure for the general framework to work.

**Changes**:
- Corrected understanding of Affine vs Projective framework
- Phase 3 is now immediate priority
- Build remains clean (0 sorryAx)

---

## Cycle 247 Summary (Previous)

**Task**: Fill `RRSpace_proj_ext` degree sorries in AdelicH1Full.lean

**Changes**:
1. Fixed `add_mem'` degree bound proof:
   - Used `by_cases` on `a = 0` and `b = 0` to handle zero cases explicitly
   - Applied `RatFunc.intDegree_add_le` for the non-zero case
   - Converted between `num.natDegree ≤ denom.natDegree + n` and `intDegree ≤ n`

2. Fixed `smul_mem'` degree bound proof:
   - Used `by_cases hf_zero : f = 0` to handle zero case
   - Applied `RatFunc.intDegree_mul` and `RatFunc.intDegree_C` (which equals 0)
   - Used `map_eq_zero` instead of non-existent `RatFunc.C_eq_zero`

**Sorries remaining in RRSpace_proj_ext**: 0

**Verification**:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "error\|sorryAx"
# No output = main path still sorry-free
grep -n "sorry" RrLean/RiemannRochV2/SerreDuality/General/AdelicH1Full.lean
# No output = AdelicH1Full.lean is sorry-free
```

---

## Cycle 246 Summary (Previous)

**Task**: Fix `RRSpace_proj_ext` definition in AdelicH1Full.lean

**Problem Found**: The carrier definition had two bugs:
1. **Wrong inequality direction**: `exp(D(v)) ≤ v(f)` instead of `v(f) ≤ exp(D(v))`
   - The original was NOT closed under addition (pole cancellation breaks it)
   - Fixed to match `RRModuleV2_real` pattern
2. **Missing zero handling**: Needed `f = 0 ∨ ...` pattern since v(0) = 0 is bottom element

**Changes**:
1. Fixed carrier to: `f = 0 ∨ ((∀ v, v(f) ≤ exp(D(v))) ∧ degree bound)`
2. Proved `zero_mem'`: Now trivial via `Or.inl rfl`
3. Proved `add_mem'` valuation: Uses ultrametric `Valuation.map_add_le_max'`
4. Proved `smul_mem'` valuation: Uses `IsScalarTower.algebraMap_apply` + `valuation_le_one`
5. Degree proofs left as sorry (2 sorries) - need careful intDegree ↔ natDegree conversion

**Verification**:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "error\|sorryAx"
# No output = main path still sorry-free
```

---

## Cycle 245 Summary (Previous)

**Task**: Complete SerreDuality reorganization - General/ subfolder + archive

**Changes**:
1. Created `SerreDuality/General/` subfolder for curve-agnostic infrastructure
2. Moved `Abstract.lean` → `General/` (abstract Serre pairing)
3. Moved `AdelicH1Full.lean` → `General/` (full adele H¹)
4. Moved `DimensionCore.lean` → `P1Specific/` (P¹ finiteness proofs)
5. Archived `IntDegreeTest.lean` → `Archive/`
6. Updated imports in `SerreDuality.lean`, `Smoke.lean`, `DimensionScratch.lean`

**Final SerreDuality structure**:
```
SerreDuality/
├── General/
│   ├── Abstract.lean        # Abstract Serre pairing
│   └── AdelicH1Full.lean    # Full adele H¹(D)
├── P1Specific/
│   ├── DimensionCore.lean   # Finiteness for L(n·[α])
│   ├── DimensionScratch.lean
│   ├── RatFuncFullRR.lean
│   └── RatFuncPairing.lean
├── RatFuncResidues.lean
└── Smoke.lean
```

**Verification**:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "error\|sorryAx"
# No output = success
```

---

## Cycle 244 Summary (Previous)

**Task**: Major reorganization - group files into subfolders

**New structure**:
```
RrLean/RiemannRochV2/
├── Core/           # Basic, Divisor, RRSpace, Typeclasses
├── Adelic/         # Adeles, AdelicH1v2, AdelicTopology, FullAdeles*
├── Definitions/    # RRDefinitions, Infrastructure, Projective, FullRRData
├── Dimension/      # DimensionCounting, KernelProof, RiemannInequality
├── ResidueTheory/  # Residue, ResidueFieldIso, DifferentIdealBridge
├── Support/        # DedekindDVR, AllIntegersCompactProof, TraceDualityProof
├── P1Instance/     # P1Instance, ProductFormula, FqPolynomialInstance
└── SerreDuality/   # (already organized with P1Specific/)
```

**Files moved**: 28 files → 7 subfolders
**Imports updated**: All references across codebase

---

## Cycle 243 Summary (Previous)

**Task**: Fill scalar mult sorries in `AdelicH1Full.lean`

**File**: `RrLean/RiemannRochV2/SerreDuality/General/AdelicH1Full.lean`

**Sorries fixed**:
1. `smul_mem_boundedSubset_full` (lines 230, 234) - Scalar mult preserves bounded adeles
   - Finite part: Used scalar tower to show `(c • a).1 = c • a.1`, then applied existing lemma
   - Infinity part: Used `diag_infty_valuation` + `FunctionField.inftyValuation.C` for constants
2. `smul_mem_globalSubset_full` (line 276) - Scalar mult preserves diagonal embedding
   - Used `map_mul` for ring homomorphism `fqFullDiagonalEmbedding`

**Sorries remaining** (in `RRSpace_proj_ext` - lower priority):
- 5 sorries for Riemann-Roch space with infinity constraint

**Verification**:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
# No output = main path still sorry-free
```

---

## Cycle 242 Summary (Previous)

**Task**: Reorganize SerreDuality folder - create P1Specific subfolder

**Changes**:
1. Created `RrLean/RiemannRochV2/SerreDuality/P1Specific/` directory
2. Moved `RatFuncPairing.lean` → `P1Specific/`
3. Moved `DimensionScratch.lean` → `P1Specific/`
4. Moved `RatFuncFullRR.lean` → `P1Specific/`
5. Updated imports in all affected files (5 files total)

---

## Cycle 241 Summary (Previous)

**Fixes applied**:
1. `add_le_add_left` → `linarith` with explicit sum non-negativity
2. Added `simp only [Finsupp.sum]` to unfold Finsupp.sum
3. Replaced circular proof with direct calc-based proof
4. Moved 6 dead-code sorried lemmas to Archive
5. Eliminated last sorry by adding `1 ≤ bound` hypothesis

---

## Sorries

**3 sorries total** in non-archived code:
- `Abstract.lean`: 3 (placeholder `AdelicRRData` instance fields)

**Sorry-free files** (confirmed Cycle 250):
- DimensionCore.lean ✅
- AdelicH1Full.lean ✅
- DimensionScratch.lean ✅
- Place.lean ✅ (new)
- DivisorV3.lean ✅ (new)
- All other SerreDuality files ✅

6 dead-code lemmas in `RrLean/Archive/SorriedLemmas.lean`.

---

## Build Commands

```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "depends on axioms"
```

**See also**: `state/PROOF_CHAIN.md` for the full import chain and verification details.

---

## Next Steps

### Immediate: Continue Phase 3 - RRSpaceV3

**Cycle 250 complete**: `DivisorV3.lean` created with projective divisors over unified Place type.

**Cycle 251**: Create `RRSpaceV3.lean` (or extend RRSpace)
- Define `L(D)` using `DivisorV3` and `Place.valuation`
- Port existing RRSpace lemmas (membership conditions, module structure)
- Handle both finite and infinite valuation constraints

**Cycle 252**: Connect to P¹ Instance
- Define `inftyPlace` for P¹ (using `FunctionField.inftyValuation`)
- Create `HasInfinitePlaces` instance for `Polynomial Fq / RatFunc Fq`
- Prove `inftyPlace.deg = 1` (degree 1 place)

**After Phase 3**: Abstract.lean sorries become fillable for all projective curves.

---

## Refactor Status

**Phase**: 0 (Cleanup) - mostly complete
**Docs created**: `INVENTORY_REPORT.md`, `REFACTOR_PLAN.md`
**Next phase**: 1 (Complete incomplete infrastructure)

See `REFACTOR_PLAN.md` for full roadmap.

---

*For historical cycles 1-240, see `ledger_archive.md`*
