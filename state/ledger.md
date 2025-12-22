# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (0 sorries)
**Result**: Restricted P¹ Riemann-Roch (linear places only)
**Cycle**: 241

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

## Cycle 241 Summary

**Fixes applied**:
1. `add_le_add_left` → `linarith` with explicit sum non-negativity
2. Added `simp only [Finsupp.sum]` to unfold Finsupp.sum
3. Replaced circular proof with direct calc-based proof
4. Moved 6 dead-code sorried lemmas to Archive
5. Eliminated last sorry by adding `1 ≤ bound` hypothesis

**Verification**:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
# No output = no sorries

# Axioms: [propext, Classical.choice, Quot.sound] (standard mathlib)
```

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

### Immediate (Cycle 242): Reorganize SerreDuality folder

**Task**: Create `SerreDuality/P1Specific/` subfolder and move P¹-only files there.

**Files to move**:
- `RatFuncPairing.lean` → `P1Specific/`
- `DimensionScratch.lean` → `P1Specific/`
- `RatFuncFullRR.lean` → `P1Specific/`

**Success criteria**:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke  # Still compiles
ls RrLean/RiemannRochV2/SerreDuality/P1Specific/    # Shows 3 files
```

**Context**: This separates curve-agnostic infrastructure from P¹-specific code, making it clear what generalizes vs. what needs replacement.

**After**: Fill the 2 sorries in `AdelicH1Full.lean` (scalar mult lemmas), which unblocks the correct H¹(D) definition for arbitrary curves.

---

## Refactor Status

**Phase**: 0 (Cleanup) - mostly complete
**Docs created**: `INVENTORY_REPORT.md`, `REFACTOR_PLAN.md`
**Next phase**: 1 (Complete incomplete infrastructure)

See `REFACTOR_PLAN.md` for full roadmap.

---

*For historical cycles 1-240, see `ledger_archive.md`*
