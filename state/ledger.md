# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles with sorries
**Phase**: 3 - Serre Duality
**Cycle**: 212

### Active Sorries (4 in RatFuncPairing.lean)

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **RatFuncPairing.lean** | 4 | HIGH | `add_mem'`, `constant_mem_projective_zero`, `projective_LRatFunc_eq_zero_of_neg_deg`, + 1 other |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma - documented |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

---

## Cycle 212 Progress

**Completed**:
1. ✅ Added `import RrLean.RiemannRochV2.ProductFormula` to RatFuncPairing.lean
2. ✅ Deleted duplicate `ProductFormulaLite` section (removed ~75 lines, 3 sorries)
3. ✅ **Proved `smul_mem'`** for `RRSpace_ratfunc_projective`

**Key implementation details for `smul_mem'`**:
- Used `open Classical` at section level for GCDMonoid instance
- Finite valuation: `← RatFunc.algebraMap_C` + `valuation_of_algebraMap` + `IsUnit.val_inv_mul`
- Infinity: Pattern from `Residue.lean:residueAtInfty_smul` with `natDegree_smul_of_smul_regular`

---

## Next Steps (Cycle 213)

### 1. Implement `add_mem'` (line ~2070)

Shows addition preserves `noPoleAtInfinity`. Key lemma: `RatFunc.num_denom_add`

**Proof structure**:
```lean
-- For a, b with noPoleAtInfinity:
-- Define raw_num := a.num * b.denom + b.num * a.denom
-- Define raw_denom := a.denom * b.denom
-- Show: raw_num.natDegree ≤ raw_denom.natDegree (from degree bounds)
-- Use num_denom_add: (a+b).num * raw_denom = raw_num * (a+b).denom
-- Derive: (a+b).num.natDegree ≤ (a+b).denom.natDegree
```

Key Mathlib lemmas:
- `Polynomial.natDegree_add_le`
- `Polynomial.natDegree_mul` (for nonzero polynomials)
- `RatFunc.num_denom_add`

### 2. Prove `constant_mem_projective_zero` (line ~2149)

Show `algebraMap Fq (RatFunc Fq) c ∈ RRSpace_ratfunc_projective 0`
- Finite: `v.valuation (RatFunc.C c) = 1` (same pattern as smul_mem')
- Infinity: `(RatFunc.C c).num = Polynomial.C c`, `(RatFunc.C c).denom = 1`, both degree 0

### 3. Tackle `projective_LRatFunc_eq_zero_of_neg_deg` (line ~2171)

Main vanishing theorem - needs product formula argument.

---

## Critical Path

```
RatFuncPairing.lean: projective_LRatFunc_eq_zero_of_neg_deg
    ├─→ smul_mem' ✅ DONE
    ├─→ add_mem' (next priority)
    ├─→ constant_mem_projective_zero (straightforward)
    └─→ L_proj(D) = {0} when deg(D) < 0
        └─→ Serre duality RHS verified
```

---

## Quick Commands

```bash
# Build
lake build 2>&1 | tail -5

# Find sorries
grep -rn "sorry" RrLean/RiemannRochV2/*.lean RrLean/RiemannRochV2/SerreDuality/*.lean

# Count sorries
grep -rn "sorry" RrLean/RiemannRochV2/*.lean RrLean/RiemannRochV2/SerreDuality/*.lean | wc -l
```

---

*For strategy, see `playbook.md`*
*For historical cycles 1-211, see `ledger_archive.md`*
