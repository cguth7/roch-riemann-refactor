# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (0 sorries in main path)
**Result**: Restricted P¹ Riemann-Roch (linear places only)
**Cycle**: 245

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

## Cycle 245 Summary

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

### Immediate (Cycle 246): Fill RRSpace_proj_ext sorries

**File**: `RrLean/RiemannRochV2/SerreDuality/General/AdelicH1Full.lean`

5 sorries for the Riemann-Roch space with infinity constraint (RRSpace_proj_ext)

### Alternative: Clean up remaining linter warnings

Several files have `unusedSectionVars` warnings that could be cleaned up with `omit` annotations

---

## Refactor Status

**Phase**: 0 (Cleanup) - mostly complete
**Docs created**: `INVENTORY_REPORT.md`, `REFACTOR_PLAN.md`
**Next phase**: 1 (Complete incomplete infrastructure)

See `REFACTOR_PLAN.md` for full roadmap.

---

*For historical cycles 1-240, see `ledger_archive.md`*
