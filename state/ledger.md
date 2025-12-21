# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles with sorries (2762 jobs)
**Phase**: 3 - Serre Duality
**Cycle**: 210

### Active Sorries (15 total)

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **ProductFormula.lean** | 3 | HIGH | Product formula - blocks L(D) vanishing |
| **RatFuncPairing.lean** | 7 | HIGH | Projective L(D) infrastructure |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

### Critical Path

```
ProductFormula.lean (3 sorries - Mathlib one-liners)
    └─→ RatFuncPairing.lean: projective_LRatFunc_eq_zero_of_neg_deg
        └─→ L_proj(D) = {0} when deg(D) < 0
            └─→ Serre duality RHS verified
```

**Estimated effort**: 5-10 cycles to clear critical path.

---

## Architecture Summary

### Key Insight: Affine vs Projective L(D)

**Problem**: `DivisorV2 R` only tracks finite places. The "affine" L(D) has no infinity constraint:
- `L(0)` for RatFunc = all polynomials = infinite dimensional
- But we need `ℓ(0) = 1` for Riemann-Roch

**Solution** (Cycle 208): Projective L(D) with degree constraint:
```
L_proj(D) := { f ∈ L(D) | deg(f.num) ≤ deg(f.denom) + D(∞) }
```
- `L_proj(0)` = constants only (dim 1) ✓
- Product formula bridges finite valuations to degree

### Key Proven Results

- ✅ Riemann inequality (Phase 1 complete)
- ✅ Adelic infrastructure: compactness, discreteness (Phase 2 complete)
- ✅ Strong approximation for RatFunc Fq
- ✅ H¹(D) = 0 for finite adeles (via h1_subsingleton)
- ✅ Non-degeneracy lemmas (vacuously true via Subsingleton)
- ✅ Abstract Serre duality theorem structure

---

## Next Steps (Cycle 210+)

### Immediate: Fill Product Formula (3 sorries)

All are near-trivial Mathlib lookups:
1. `sum_rootMultiplicity_eq_card_roots` - Use `Polynomial.card_roots`
2. `sum_rootMultiplicity_le_natDegree` - Use `Polynomial.card_roots_le_degree`
3. `principal_divisor_degree_le_zero` - Careful inequality analysis

### Then: RatFuncPairing Submodule Proofs (5 sorries)

- `add_mem'`, `smul_mem'` for RRSpace_ratfunc_projective
- `constant_mem_projective_zero`
- `projective_LRatFunc_eq_zero_of_neg_deg` (main vanishing)

### Lower Priority (not blocking)

- `residueAtIrreducible` - Higher-degree places (deferred)
- `residue_sum_eq_zero` - General residue theorem (deferred)
- `TraceDualityProof` - Alternative approach, skip

---

## Quick Commands

```bash
# Build
lake build 2>&1 | tail -5

# Find sorries
grep -rn "sorry$" RrLean/RiemannRochV2/*.lean RrLean/RiemannRochV2/SerreDuality/*.lean

# Count sorries
grep -rn "sorry$" RrLean/RiemannRochV2/*.lean RrLean/RiemannRochV2/SerreDuality/*.lean | wc -l
```

---

## File Status

### Core (sorry-free)
- `RiemannInequality.lean` ✅ - Main inequality theorem
- `Abstract.lean` ✅ - Serre duality structure
- `RatFuncResidues.lean` ✅ - Residue infrastructure
- `AdelicH1v2.lean` ✅ - H¹ via finite adeles
- `FullAdelesBase.lean` ✅ - Full adele definitions
- `FqPolynomialInstance.lean` ✅ - AllIntegersCompact instance

### Active (has sorries)
- `ProductFormula.lean` ⚠️ (3) - Product formula
- `RatFuncPairing.lean` ⚠️ (7) - Projective L(D)
- `Residue.lean` ⚠️ (2) - Deferred infrastructure

### Not on critical path
- `TraceDualityProof.lean` (1) - Alternative approach
- `FullAdelesCompact.lean` (1) - Edge case

---

*For strategy, see `playbook.md`*
*For historical cycles 1-209, see `ledger_archive.md`*
