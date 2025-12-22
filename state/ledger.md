# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (0 sorries in main path)
**Result**: Restricted P¹ Riemann-Roch (linear places only)
**Cycle**: 243

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

## Cycle 243 Summary

**Task**: Fill scalar mult sorries in `AdelicH1Full.lean`

**File**: `RrLean/RiemannRochV2/SerreDuality/AdelicH1Full.lean`

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

**0 sorries in main codebase.**

6 dead-code lemmas in `RrLean/Archive/SorriedLemmas.lean`.

---

## Build Commands

```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "depends on axioms"
```

---

## Next Steps

### Immediate (Cycle 244): Continue Phase 0 reorganization

Per `REFACTOR_PLAN.md`:
1. Create `SerreDuality/General/` subfolder
2. Move `Abstract.lean` → `General/`
3. Move `AdelicH1Full.lean` → `General/`
4. Move `DimensionCore.lean` → `P1Specific/`
5. Archive `IntDegreeTest.lean`

**Success criteria**:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke  # Still compiles
ls RrLean/RiemannRochV2/SerreDuality/General/       # Shows 2 files
```

### Alternative (Cycle 244): Fill RRSpace_proj_ext sorries

**File**: `RrLean/RiemannRochV2/SerreDuality/AdelicH1Full.lean` (lines 374-390)

5 sorries for the Riemann-Roch space with infinity constraint:
- `zero_mem'` - Fix valuation ordering for zero
- `add_mem'` - Ultrametric inequality + degree bound
- `smul_mem'` - Scalar preserves valuation + degree

---

## Refactor Status

**Phase**: 0 (Cleanup) - mostly complete
**Docs created**: `INVENTORY_REPORT.md`, `REFACTOR_PLAN.md`
**Next phase**: 1 (Complete incomplete infrastructure)

See `REFACTOR_PLAN.md` for full roadmap.

---

*For historical cycles 1-240, see `ledger_archive.md`*
