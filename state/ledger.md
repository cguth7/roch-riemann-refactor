# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles with sorries
**Phase**: 3 - Serre Duality
**Cycle**: 214

### Active Sorries (2 in RatFuncPairing.lean)

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **RatFuncPairing.lean** | 2 | HIGH | `LRatFunc_eq_zero_of_neg_deg`, `projective_LRatFunc_eq_zero_of_neg_deg` |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma - documented |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

---

## Cycle 214 Progress

**Completed**:
1. ✅ **Proved `IsLinearPlaceSupport`** - Predicate for divisors supported on linear places
2. ✅ **Proved `constant_valuation_eq_one`** - Constants have valuation 1 at all finite places
3. ✅ **Proved `exists_neg_of_deg_neg`** - Negative degree implies negative coefficient exists
4. ✅ **Proved `constant_not_in_LRatFunc_of_neg_coeff`** - Constants excluded from L(D) when D has negative coeff
5. ⏳ **Partial progress on `projective_LRatFunc_eq_zero_of_neg_deg`** - Constant case proved, non-constant case needs product formula

**Key implementation details**:

**`constant_valuation_eq_one`**:
- Uses `intValuation_eq_one_iff` to show constants (units) have valuation 1
- Key: `Polynomial.C c` is a unit, so not in any prime ideal v.asIdeal

**`exists_neg_of_deg_neg`**:
- Contrapositive: if all D(v) ≥ 0 in support, then deg(D) ≥ 0
- Uses `DivisorV2.deg_nonneg_of_effective`

**`constant_not_in_LRatFunc_of_neg_coeff`**:
- If D(v) < 0, then exp(D v) < 1
- Constant has valuation 1, so 1 ≤ exp(D v) < 1 is contradiction

**Main theorem structure for `projective_LRatFunc_eq_zero_of_neg_deg`**:
- Case 1 (constants): ✅ PROVED via `constant_not_in_LRatFunc_of_neg_coeff`
- Case 2 (non-constants): Needs product formula infrastructure

**Key insight on weighted vs unweighted degree**:
- Current `deg(D) = Σ_v D(v)` is unweighted
- Product formula: `Σ_v deg(v) * ord_v(f) + ord_∞(f) = 0` is weighted
- For LINEAR places (deg = 1), these coincide
- Non-linear places would need weighted degree definition
- Workaround: If D is linear-supported, poles must be at linear places (else D((π)) = 0 < 1 required)

---

## Next Steps (Cycle 215)

### Complete `projective_LRatFunc_eq_zero_of_neg_deg`

The non-constant case requires:
1. **Order function**: `ord_v : RatFunc Fq → ℤ` for each v
2. **Product formula**: `Σ_v ord_v(f) = deg(num) - deg(denom)` for linear places
3. **Membership characterization**: `f ∈ L(D) ↔ ∀ v, ord_v(f) ≥ -D(v)`

**Mathematical argument**:
- For f = num/denom with noPoleAtInfinity: deg(num) ≤ deg(denom)
- Poles at places v require D(v) ≥ 1
- Places with D(v) < 0 require zeros
- Sum: deg(D) + Σ ord_v(f) ≥ 0
- But Σ ord_v(f) ≤ deg(num) - deg(denom) ≤ 0
- So deg(D) ≥ 0, contradicting deg(D) < 0

---

## Critical Path

```
RatFuncPairing.lean: projective_LRatFunc_eq_zero_of_neg_deg
    ├─→ smul_mem' ✅ DONE (Cycle 212)
    ├─→ add_mem' ✅ DONE (Cycle 213)
    ├─→ constant_mem_projective_zero ✅ DONE (Cycle 213)
    ├─→ constant case ✅ DONE (Cycle 214)
    └─→ non-constant case ← NEXT (needs product formula)
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
