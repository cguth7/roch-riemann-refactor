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

**Priority**: HIGH - Blocks all generalization work

### 1.1 Finish AdelicH1Full.lean Sorries

**File**: `RrLean/RiemannRochV2/SerreDuality/AdelicH1Full.lean`

**Sorries to fill**:
| Line | Lemma | Description |
|------|-------|-------------|
| 230 | `smul_mem_boundedSubset_full` | Scalar mult preserves bounded adeles |
| 234 | `smul_mem_boundedSubset_full` | Second sorry in same lemma |
| 276 | `smul_mem_globalSubset_full` | Scalar mult on diagonal |

**Strategy**: These are straightforward - show that k-scalars don't change valuations (k ⊆ integers at all places).

**Outcome**: Unlocks `SpaceModule_full` as the correct H¹(D) definition for arbitrary curves.

### 1.2 Complete Residue.lean Phase B/C

**File**: `RrLean/RiemannRochV2/Residue.lean`

**Current State**: Phase A (X-adic residue) complete. Phases B (infinity) and C (sum) incomplete.

**Work Needed**:
1. Define `residueAt v` for arbitrary HeightOneSpectrum v (not just X)
2. Generalize LaurentSeries expansion to arbitrary uniformizers
3. Prove `residue_sum_eq_zero` for finite places

**Dependency**: Needs trace maps for higher-degree places (see Phase 3).

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

**Priority**: MEDIUM - Core architectural change

### 3.1 Define Unified Place Type

**New File**: `RrLean/RiemannRochV2/Place.lean`

```lean
/-- A place on a function field K/k is either finite (HeightOneSpectrum R)
    or infinite (archimedean valuation). -/
inductive Place (R : Type*) (K : Type*) [CommRing R] [Field K] [Algebra R K]
  | finite : HeightOneSpectrum R → Place R K
  | infinite : InfinitePlace K → Place R K

/-- Infinite places for function fields. For now, just the degree valuation. -/
structure InfinitePlace (K : Type*) [Field K] where
  valuation : K → ℤ∞
  is_valuation : Valuation.IsValuation valuation
```

### 3.2 Refactor RRDefinitions.lean

**Current**: All definitions use `HeightOneSpectrum R`

**Changes**:
1. Keep existing code as `valuationRingAt_finite`, `evaluationMapAt_finite`, etc.
2. Add parallel definitions for infinite places
3. Create unified wrappers that dispatch on `Place R K`

**Outcome**: `DivisorV2` becomes `Place R K →₀ ℤ` (not just `HeightOneSpectrum R →₀ ℤ`)

### 3.3 Update Divisor.lean

**Minimal Changes**:
- Extend `DivisorV2` to include infinite places
- Add `deg_finite`, `deg_infinite` for separate degree contributions
- Prove `deg = deg_finite + deg_infinite`

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

### Phase 0: Cleanup
| Cycle | Task |
|-------|------|
| 242 | Move 3 files to `SerreDuality/P1Specific/`, update imports |

### Phase 1: Complete Infrastructure
| Cycle | Task |
|-------|------|
| 243 | Fill `smul_mem_boundedSubset_full` sorry (line 230) |
| 244 | Fill `smul_mem_boundedSubset_full` sorry (line 234) + `smul_mem_globalSubset_full` (276) |
| 245-247 | Residue.lean Phase B: define `residueAt` for arbitrary places |
| 248-249 | Residue.lean Phase C: prove finite residue sum |

### Phase 2: Extract P¹ Instances
| Cycle | Task |
|-------|------|
| 250 | Extract FqInstance from FullAdelesBase.lean |
| 251 | Extract weak approximation from FullAdelesCompact.lean |
| 252 | Create FqPolynomialFullInstance.lean aggregator |

### Phase 3: Place Type
| Cycle | Task |
|-------|------|
| 253 | Define `Place` inductive type + basic API |
| 254 | Add `InfinitePlace` structure |
| 255-256 | Extend `DivisorV2` to include infinite places |
| 257-259 | Update `RRDefinitions.lean` to dispatch on Place |

### Phase 4: Residue Theorem
| Cycle | Task |
|-------|------|
| 260-262 | Trace-compatible residues at higher-degree places |
| 263-265 | Prove `residue_sum_eq_zero` for all places |
| 266-267 | Wire residue pairing into Abstract.lean |

### Phase 5: Cleanup
| Cycle | Task |
|-------|------|
| 268 | Move remaining P¹ files to archive, update all imports |

**Total**: ~27 cycles (rough estimate, will vary based on proof difficulty)

---

## Success Criteria

The refactor is complete when:

1. **Core compiles without P¹**: `lake build RrLean.RiemannRochV2` succeeds with no Polynomial/RatFunc in general modules
2. **P¹ instance separate**: `lake build RrLean.RiemannRochV2.Instances.P1` provides full P¹ Riemann-Roch
3. **New instance template works**: Can instantiate `AdelicRRData` for at least one non-P¹ curve
4. **Residue theorem general**: `residue_sum_eq_zero` proved for all places (not just linear)
5. **Zero sorries in core**: All infrastructure files sorry-free

---

*Plan created Cycle 241+. Update as work progresses.*
