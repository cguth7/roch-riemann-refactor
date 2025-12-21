# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Compiles (with sorries)
**Phase**: 3 - Serre Duality → Dimension Formula
**Cycle**: 233

### CRITICAL CORRECTION (Cycle 233)

**Previous ledger entries (Cycles 231-232) were INCORRECT.**

The SerreDuality folder files were **never on the build path**. When we added them:
1. Multiple syntax errors from Mathlib API drift
2. **6 sorries in DimensionScratch.lean** that were never proved
3. The "Riemann-Roch PROVED" claims were based on files that didn't compile

### Active Sorries

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **DimensionScratch.lean** | 3 | **HIGH** | Gap bound, dimension formulas - BLOCKING |
| **RatFuncFullRR.lean** | 0 | ✅ DONE | L_proj(0) = constants, ℓ(0) = 1 |
| **RatFuncPairing.lean** | 1 | LOW | Early incomplete attempt |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma |
| **Residue.lean** | 2 | LOW | Higher-degree places |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach |

---

## Cycle 233 Progress (IN PROGRESS)

**Goal**: Fix DimensionScratch.lean sorries to complete Riemann-Roch

### Build Path Fixed

Added to build path via `SerreDuality.lean`:
- ✅ DimensionScratch.lean - compiles with sorries
- ✅ RatFuncFullRR.lean - compiles clean
- ✅ IntDegreeTest.lean - compiles clean

### Sorries Fixed This Cycle

1. ✅ **`linearPlace_residue_equiv`** (lines 76-91)
   - `residueFieldAtPrime (Polynomial Fq) (linearPlace α) ≃+* Fq`
   - Uses `Polynomial.quotientSpanXSubCAlgEquiv` composed with quotient bijection

2. ✅ **`IsLinearPlaceSupport_sub_single`** (lines 588-604)
   - Linear support preserved when subtracting a linear place
   - Changed signature to take `α : Fq` instead of arbitrary `v`

### Sorries Still Blocking (3 remaining)

| Lemma | Line | Status | Blocker |
|-------|------|--------|---------|
| `linearPlace_residue_finrank` | ~95 | **STUCK** | Type mismatch in LinearEquiv.ofBijective |
| `ell_ratfunc_projective_gap_le` | ~137 | sorry | Depends on residue finrank |
| `ell_ratfunc_projective_single_linear` | ~483 | sorry | Depends on gap bound |
| `ell_ratfunc_projective_eq_deg_plus_one` | ~656 | sorry | MAIN THEOREM - depends on above |

### Technical Blocker: `linearPlace_residue_finrank`

**Goal**: Prove `Module.finrank Fq (residueFieldAtPrime (Polynomial Fq) (linearPlace α)) = 1`

**Issue**: Building an Fq-linear equivalence from the bijective algebraMap fails with type mismatch:
```
LinearEquiv.ofBijective expects Function.Bijective ⇑?m.119
but hbij has type Function.Bijective ⇑(algebraMap (R ⧸ I) I.ResidueField)
```

**Attempted approaches**:
1. Direct composition of ring equivs - `▸` notation failed
2. Building LinearMap then using ofBijective - type mismatch
3. Using AlgEquiv.toLinearEquiv - needs scalar tower compatibility

**Suggested fix for next session**:
- Use `RationalPoint` typeclass from `Projective.lean`
- Instantiate `RationalPoint Fq (Polynomial Fq) (linearPlace α)`
- Then `residue_finrank_eq_one` gives the result directly

### Key Mathlib Lemmas Used

```lean
-- From Mathlib.RingTheory.Polynomial.Quotient
Polynomial.quotientSpanXSubCAlgEquiv : (R[X] ⧸ span{X - C x}) ≃ₐ[R] R

-- From Mathlib.RingTheory.Ideal.Quotient.Operations
Ideal.bijective_algebraMap_quotient_residueField :
  Function.Bijective (algebraMap (R ⧸ I) I.ResidueField)
```

---

## Dependency Graph (Corrected)

```
riemann_roch_ratfunc (NOT PROVED)
    ├─→ ell_ratfunc_projective_eq_deg_plus_one (sorry)
    │       ├─→ ell_ratfunc_projective_gap_le (sorry)
    │       │       └─→ linearPlace_residue_finrank (BLOCKED)
    │       │               └─→ linearPlace_residue_equiv ✅ DONE
    │       ├─→ inv_X_sub_C_pow_mem_projective_general ✅
    │       └─→ inv_X_sub_C_pow_not_mem_projective_general ✅
    └─→ ell_canonical_sub_zero ✅ DONE (Cycle 224)
            └─→ ell_ratfunc_projective_zero_of_neg_deg ✅ DONE (Cycle 222)
```

---

## Files to Read for Next Session

1. **DimensionScratch.lean** - Main file with sorries
2. **Projective.lean** - Has `RationalPoint` typeclass that may solve the blocker
3. **Infrastructure.lean** - Has `residueFieldAtPrime.linearEquiv`

---

## Build Command

```bash
lake build RrLean.RiemannRochV2.SerreDuality.DimensionScratch 2>&1 | grep -E "(error|sorry)"
```

---

## Cycle 230-232 (SUPERSEDED)

**Note**: These cycles claimed proofs that were never on the build path.
The mathematical work was real but had Mathlib API drift issues.
See Cycle 233 for the corrected state.

---

## Quick Commands

```bash
# Build
lake build 2>&1 | tail -5

# Find sorries in DimensionScratch
grep -n "sorry" RrLean/RiemannRochV2/SerreDuality/DimensionScratch.lean

# Count all sorries
grep -rn "sorry" RrLean/RiemannRochV2/*.lean RrLean/RiemannRochV2/SerreDuality/*.lean | wc -l
```

---

*For strategy, see `playbook.md`*
*For historical cycles 1-229, see `ledger_archive.md`*
