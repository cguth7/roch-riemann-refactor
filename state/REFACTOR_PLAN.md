# Refactor Plan: P¹ → Arbitrary Curves

**Status**: Ready for execution (post-Cycle 241)
**Goal**: Transform restricted P¹ Riemann-Roch into a framework for arbitrary algebraic curves
**Reference**: See `INVENTORY_REPORT.md` for detailed file analysis

---

## Cycle Sizing Guidance

Each cycle has ~50k tokens of context. Scope work accordingly:

| Task Type | Scope per Cycle |
|-----------|-----------------|
| File reorganization | Move 3-5 files, update 1-2 imports |
| Sorry filling | 1 sorry (or 2-3 trivial ones) |
| New definitions | 1 definition + 3-5 basic lemmas |
| Architectural changes | 1 file refactor |

**Rule**: If you're not sure a task fits in one cycle, it doesn't. Split it.

**See**: `state/playbook.md` → "Cycle Discipline" for full methodology.

---

## Executive Summary

The codebase has **~3,700 lines of curve-agnostic infrastructure** that needs no changes. The pivot requires:
- Burning 4 P¹-specific files
- Refactoring 8 files (mostly extracting P¹ instances)
- Completing 2 incomplete files
- Archiving 8 reference files

**Critical Path**: AdelicH1Full.lean → RRDefinitions.lean → FullAdelesCompact.lean → RatFuncResidues.lean

---

## Phase 0: Cleanup (This Session)

### 0.1 Archive Deprecated Items
- [x] Add `agents/README.md` marking folder as deprecated
- [x] Move `BUILD_PATH_SORRIES.md` → `archive/random/`
- [x] Move `state/handoff_cycle68.md` → `archive/random/`

### 0.2 Reorganize SerreDuality Folder
Create clear separation between general and P¹-specific:

```
RrLean/RiemannRochV2/SerreDuality/
├── General/           # NEW - curve-agnostic
│   ├── Abstract.lean  # (move from root)
│   └── AdelicH1Full.lean  # (move from root)
├── P1Specific/        # NEW - reference only
│   ├── RatFuncResidues.lean
│   ├── RatFuncPairing.lean
│   ├── RatFuncFullRR.lean
│   ├── DimensionCore.lean
│   └── DimensionScratch.lean
├── IntDegreeTest.lean  # (archive)
└── Smoke.lean          # (keep for build hygiene)
```

---

## Phase 1: Complete Incomplete Infrastructure

**Status**: ✅ COMPLETE (Cycles 243-247)

### 1.1 Finish AdelicH1Full.lean Sorries - DONE

All sorries in AdelicH1Full.lean filled. `SpaceModule_full` compiles.

### 1.2 Residue.lean Status

- Phase A (X-adic): ✅ Complete
- Phase B (infinity): ✅ Complete (`residueAtInfty`)
- Phase C (residue sum): ✅ Complete for linear places (`residueSumTotal_splits`)
- Higher-degree places: Deferred to Phase 4 (needs trace maps)

---

## ⚠️ CRITICAL DISCOVERY (Cycle 248): The Affine Trap

**Problem**: The current `AdelicRRData` framework models **Affine Riemann-Roch**, not Projective.

| Curve Type | Coordinate Ring R | Missing Place(s) |
|------------|-------------------|------------------|
| P¹ | k[t] | ∞ |
| Elliptic | k[x,y]/(y²-x³-ax-b) | Point O at infinity |
| Hyperelliptic | k[x,y]/(y²-f(x)) | 1-2 points at infinity |

**Root cause**: `HeightOneSpectrum R` only contains finite places. Any Dedekind domain R
represents the AFFINE part of a curve. The infinite place(s) are missing.

**Impact**: Abstract.lean sorries CANNOT be filled for any projective curve until
`DivisorV2` is extended to include infinite places.

**Resolution**: Phase 3 (Place Type) is now CRITICAL PATH, not optional cleanup.

---

## Phase 2: Extract P¹-Specific Instances

**Priority**: MEDIUM - Enables parallel work on new curve instances

### 2.1 Split FullAdelesBase.lean

**Current**: General definitions + Fq[X] instance mixed together

**Refactor**:
```
FullAdelesBase.lean (lines 1-236)     → KEEP as general framework
FullAdelesFqInstance.lean (lines 237-461) → EXTRACT to new file
```

**Changes**:
- Move `FqInstance` section to new file
- Keep: `FullAdeleRing`, `fullDiagonalEmbedding`, `FullDiscreteCocompactEmbedding` typeclass
- Extract: `inftyValuationDef`, `polynomial_inftyVal_ge_one`, `finite_integral_implies_polynomial`

### 2.2 Split FullAdelesCompact.lean

**Current**: General compactness + Fq[X] weak approximation mixed

**Refactor**:
```
AdelicCompactness.lean (lines 1-435)              → KEEP as general theorems
FullAdelesFqWeakApproximation.lean (lines 436+)   → EXTRACT to new file
```

**Changes**:
- Move all polynomial division proofs to new file
- Keep: `rankOne_FqtInfty`, `isCompact_integralFullAdeles`, `isDiscreteValuationRing_integer_FqtInfty`
- Extract: `exists_finite_integral_translate*`, `fq_discrete_in_fullAdeles`, `fq_closed_in_fullAdeles`

### 2.3 Create FqPolynomialFullInstance.lean

**Purpose**: Single file that provides complete P¹ instantiation

**Contents** (aggregated from extractions):
- `FullAdelesFqInstance` (from FullAdelesBase)
- `FullAdelesFqWeakApproximation` (from FullAdelesCompact)
- `instAdelicRRData_ratfunc` instance
- Re-export `RatFuncFullRR` theorems

---

## Phase 3: Generalize Place Type

**Priority**: 🔴 CRITICAL - Blocks all projective curve work (see Affine Trap above)
**Status**: IN PROGRESS (Cycles 249-251 complete, ~3 cycles remaining)

### 3.1 Define Unified Place Type - ✅ DONE (Cycle 249)

**File**: `RrLean/RiemannRochV2/Core/Place.lean`

```lean
/-- A place on a curve is either finite or infinite. -/
inductive Place (R : Type*) (K : Type*) ...
  | finite : HeightOneSpectrum R → Place R K
  | infinite : InfinitePlace K → Place R K

/-- An infinite place with valuation and degree. -/
structure InfinitePlace (K : Type*) [Field K] where
  val : Valuation K (WithZero (Multiplicative ℤ))
  deg : ℕ
  deg_pos : 0 < deg
```

Key definitions: `Place.valuation`, `Place.isFinite`, `HasInfinitePlaces` typeclass.

### 3.2 Define Projective Divisors - ✅ DONE (Cycle 250)

**File**: `RrLean/RiemannRochV2/Core/DivisorV3.lean`

```lean
/-- Projective divisor = finitely supported map from ALL places to ℤ. -/
abbrev DivisorV3 := Place R K →₀ ℤ
```

Key definitions: `DivisorV3.deg`, `DivisorV3.degFinite`, `DivisorV3.degInfinite`,
`DivisorV3.ofAffine` (embed affine divisor into projective).

### 3.3 Define Projective L(D) - ✅ DONE (Cycle 251)

**File**: `RrLean/RiemannRochV2/Core/RRSpaceV3.lean`

```lean
/-- Projective L(D) must use base field k as scalars (not R). -/
class ConstantsValuationBound (k R K) where
  valuation_le_one : ∀ c p, p.valuation (algebraMap k K c) ≤ 1

def RRModuleV3 [ConstantsValuationBound k R K] (D : DivisorV3 R K) : Submodule k K
```

**Key insight**: Elements of R have valuation > 1 at infinity, so projective L(D)
is a k-module, not an R-module.

### 3.4 Connect to P¹ Instance - ✅ DONE (Cycle 252)

**File**: `RrLean/RiemannRochV2/P1Instance/P1Place.lean`

- `p1InftyPlace : InfinitePlace (RatFunc Fq)` using `FunctionField.inftyValuation`
- `instHasInfinitePlacesP1` instance for P¹
- `instConstantsValuationBoundP1` for Fq constants

### 3.5 Define Canonical Divisor - ✅ DONE (Cycle 253)

**File**: `RrLean/RiemannRochV2/P1Instance/P1Canonical.lean`

- `p1Canonical : DivisorV3 Fq[X] (RatFunc Fq)` = -2[∞]
- Key lemmas: `deg_p1Canonical = -2`, `p1_genus_formula`

### 3.6 L(K-D) Vanishing - ✅ DONE (Cycles 254-255)

**File**: `RrLean/RiemannRochV2/P1Instance/P1VanishingLKD.lean`

- `RRSpaceV3_p1Canonical_sub_ofAffine_eq_zero`: L(K-D) = {0} for effective D
- `ellV3_p1Canonical_sub_ofAffine_eq_zero`: ℓ(K-D) = 0 for effective D
- Key helper: `eq_algebraMap_of_valuation_le_one_forall` - characterizes polynomials via valuations

---

## Phase 4: Generalize Residue Theorem

**Priority**: HIGH for Serre duality - Can start after Phase 1.1

### 4.1 Trace-Compatible Residues

**Problem**: Current `RatFuncResidues.lean` only handles degree-1 places.

**Solution**:
```lean
/-- Residue at a place v, traced to base field k. -/
def residueAt (k : Type*) [Field k] (v : Place R K) : K → k :=
  match v with
  | .finite v => traceToBase k (localResidue v)
  | .infinite v => infinityResidue v
```

**Key Lemma**: `residue_sum_eq_zero : ∑ v, residueAt k v f = 0`

### 4.2 Update SerreDuality/Abstract.lean

**Current**: `serrePairing := 0` (placeholder)

**Change**: Wire in actual residue pairing once Phase 4.1 complete.

---

## Phase 5: Burn P¹-Specific Files

**Priority**: LOW - Can defer until Phases 1-4 complete

### Files to Remove from Main Build

| File | Reason | Action |
|------|--------|--------|
| `P1Instance.lean` | Pure P¹ validation | Move to `archive/P1Reference/` |
| `ProductFormula.lean` | Admits formula is false | Move to `archive/P1Reference/` |
| `SerreDuality/RatFuncPairing.lean` | P¹ geometry hack | Move to `SerreDuality/P1Specific/` |
| `SerreDuality/DimensionScratch.lean` | ℓ(D)=deg+1 is P¹-only | Move to `SerreDuality/P1Specific/` |

### Update Imports

After moving:
1. Update `RiemannRochV2.lean` to not import burned files
2. Update `SerreDuality.lean` exports
3. Ensure `lake build` still succeeds on core modules

---

## Phase 6: New Curve Instances (Future)

**Priority**: After Phases 1-4 complete

### 6.1 Template: Hyperelliptic Curves

```lean
/-- Instance for hyperelliptic curve y² = f(x) over Fq. -/
instance hyperellipticRRData (f : Polynomial Fq) [hf : IsHyperelliptic f] :
    AdelicRRData Fq (CoordinateRing f) (FunctionField f) where
  h1_finite := sorry  -- Use genus formula g = (deg f - 1) / 2
  h1_vanishing := sorry
  serre_duality := sorry
```

### 6.2 Template: Elliptic Curves

```lean
/-- Instance for elliptic curve E: y² = x³ + ax + b over Fq. -/
instance ellipticRRData (E : EllipticCurve Fq) :
    AdelicRRData Fq E.CoordinateRing E.FunctionField where
  h1_finite := sorry  -- Genus 1
  h1_vanishing := sorry
  serre_duality := sorry
```

---

## Dependency Graph

```
Phase 0 (Cleanup)
    ↓
Phase 1.1 (AdelicH1Full sorries)  ←── Critical Path Start
    ↓
Phase 2 (Extract P¹ instances)   ←── Can parallelize
    ↓
Phase 3 (Place type)             ←── Architectural core
    ↓
Phase 4 (Residue theorem)        ←── Needs Phases 1 + 3
    ↓
Phase 5 (Burn P¹ files)          ←── Cleanup
    ↓
Phase 6 (New instances)          ←── Payoff
```

---

## Verification Checkpoints

### After Phase 1
```bash
lake build RrLean.RiemannRochV2.SerreDuality.AdelicH1Full 2>&1 | grep "sorry"
# Expected: No output (sorries filled)
```

### After Phase 2
```bash
lake build RrLean.RiemannRochV2.FullAdelesBase 2>&1 | grep "Polynomial\|RatFunc"
# Expected: No matches in general module (all moved to FqInstance)
```

### After Phase 3
```bash
lake build RrLean.RiemannRochV2.Place 2>&1
# Expected: Clean build of new Place type
```

### After Phase 4
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Abstract 2>&1 | grep "sorryAx"
# Expected: No output (real pairing, not placeholder)
```

---

## Estimated Effort (Cycle-by-Cycle Breakdown)

### Phase 0: Cleanup - ✅ COMPLETE
| Cycle | Task | Status |
|-------|------|--------|
| 242 | Move 3 files to `SerreDuality/P1Specific/`, update imports | ✅ Done |

### Phase 1: Complete Infrastructure - ✅ COMPLETE
| Cycle | Task | Status |
|-------|------|--------|
| 243-247 | AdelicH1Full.lean sorries + RRSpace_proj_ext | ✅ Done |
| — | Residue.lean Phases A/B/C (linear places) | ✅ Done |

### Phase 2: Extract P¹ Instances - DEFERRED
Skipping for now - Phase 3 is more urgent due to Affine Trap discovery.

### Phase 3: Place Type - ✅ COMPLETE (Cycles 249-255)
| Cycle | Task | Status |
|-------|------|--------|
| 249 | Define `Place` inductive type + basic API | ✅ Done |
| 250 | Create `DivisorV3` with Place-based divisors | ✅ Done |
| 251 | Create `RRSpaceV3` with projective L(D) | ✅ Done |
| 252 | Connect to P¹: `inftyPlace`, `ConstantsValuationBound` instance | ✅ Done |
| 253 | Define canonical divisor K = -2[∞] for P¹ | ✅ Done |
| 254-255 | Prove L(K-D) = 0 for effective D (sorry-free!) | ✅ Done |

### Phase 3.5: Surjectivity for Dimension Formula (Current)
| Cycle | Task | Status |
|-------|------|--------|
| 256-261 | PlaceDegree + GapBoundGeneral + finiteness | ✅ Done |
| 262 | PlaceDegree cleanup + evaluationMapAt_surj skeleton | ✅ Done |
| 263+ | Fill surjectivity sorries (hf_affine, hf_infty, eval=c) | Pending |

### Phase 4: Residue Theorem
| Cycle | Task |
|-------|------|
| TBD | Trace-compatible residues at higher-degree places |
| TBD | Prove `residue_sum_eq_zero` for all places |
| TBD | Wire residue pairing into Abstract.lean |

### Phase 5: Cleanup
| Cycle | Task |
|-------|------|
| TBD | Move remaining P¹ files to archive, update all imports |

**Current focus**: Fill `evaluationMapAt_surj` sorries to complete dimension formula

---

## Success Criteria

The refactor is complete when:

1. **Core compiles without P¹**: `lake build RrLean.RiemannRochV2` succeeds with no Polynomial/RatFunc in general modules
2. **P¹ instance separate**: `lake build RrLean.RiemannRochV2.Instances.P1` provides full P¹ Riemann-Roch
3. **New instance template works**: Can instantiate `AdelicRRData` for at least one non-P¹ curve
4. **Residue theorem general**: `residue_sum_eq_zero` proved for all places (not just linear)
5. **Zero sorries in core**: All infrastructure files sorry-free

---

*Plan created Cycle 241+. Updated Cycle 262: Phase 3 COMPLETE, Phase 3.5 (surjectivity) in progress.*
