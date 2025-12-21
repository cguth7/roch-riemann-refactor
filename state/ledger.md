# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles with sorries (2138 jobs)
**Phase**: 3 - Serre Duality
**Cycle**: 210

### Active Sorries (12 total)

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **RatFuncPairing.lean** | 7 | HIGH | Projective L(D) infrastructure |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma - see below |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

### Cycle 210 Progress

**ProductFormula.lean**: 2 sorries ✅ PROVED, 1 marked INCORRECT
- ✅ `sum_rootMultiplicity_eq_card_roots` - proved via `Multiset.toFinset_sum_count_eq`
- ✅ `sum_rootMultiplicity_le_natDegree` - proved via above + `card_roots'`
- ⚠️ `principal_divisor_degree_eq_zero` - **FALSE as stated** (see docstring)
  - Counterexample: f = 1/(X²+X+1) over F₂ gives 0 + 2 = 2 ≠ 0
  - Fq-rational product formula only works when polynomials split completely
  - The proof of `projective_LRatFunc_eq_zero_of_neg_deg` doesn't need this lemma

### Critical Path

```
RatFuncPairing.lean: projective_LRatFunc_eq_zero_of_neg_deg
    ├─→ Needs: degree-weighted product formula (UFD, not root counting)
    ├─→ Needs: smul_mem' and add_mem' for RRSpace_ratfunc_projective
    └─→ L_proj(D) = {0} when deg(D) < 0
        └─→ Serre duality RHS verified
```

**Key Insight (Cycle 210)**: The proof doesn't need Fq-rational product formula.
It uses: `Σ_P deg(P) * mult(P, f) = deg(f)` from unique factorization.

**Estimated effort**: 5-8 cycles to clear critical path.

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

## Next Steps (Cycle 211+)

### Immediate: RatFuncPairing Submodule Proofs

1. `smul_mem'` for RRSpace_ratfunc_projective
   - Need: scalar mult preserves valuation bounds and degree bounds
   - Key lemma: for c : Fq×, `(c • f).num.natDegree = f.num.natDegree`

2. `add_mem'` for RRSpace_ratfunc_projective
   - Need: addition preserves noPoleAtInfinity
   - Key: degree of sum ≤ max of degrees

3. `constant_mem_projective_zero`
   - Need: `algebraMap Fq (RatFunc Fq) c` has valuation 1 everywhere
   - Key: `RatFunc.algebraMap_eq_C` + `num_C`, `denom_C`

4. `projective_LRatFunc_eq_zero_of_neg_deg` (main vanishing)
   - Need: degree-weighted product formula argument
   - Key: Σ_P deg(P) * ord_P(f) = deg(num) - deg(denom) from UFD

### RatFuncPairing Cleanup (Optional)

- Lines 2063, 2072, 2108: Duplicate lemmas from ProductFormula.lean
- Consider importing ProductFormula.lean and reusing proved lemmas

### Lower Priority (not blocking)

- `residueAtIrreducible` - Higher-degree places (deferred)
- `residue_sum_eq_zero` - General residue theorem (deferred)
- `TraceDualityProof` - Alternative approach, skip
- `FullAdelesCompact` edge case - not needed for main theorem

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
- `ProductFormula.lean` ⚠️ (1) - Intentionally incorrect lemma (documented)
- `RatFuncPairing.lean` ⚠️ (7) - Projective L(D)
- `Residue.lean` ⚠️ (2) - Deferred infrastructure

### Not on critical path
- `TraceDualityProof.lean` (1) - Alternative approach
- `FullAdelesCompact.lean` (1) - Edge case

---

*For strategy, see `playbook.md`*
*For historical cycles 1-209, see `ledger_archive.md`*
