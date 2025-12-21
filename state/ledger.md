# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles with sorries
**Phase**: 3 - Serre Duality
**Cycle**: 217

### Active Sorries (2 in RatFuncPairing.lean)

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **RatFuncPairing.lean** | 2 | HIGH | `LRatFunc_eq_zero_of_neg_deg`, `projective_LRatFunc_eq_zero_of_neg_deg` |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma - documented |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

---

## Cycle 217 Progress

**Completed**:
1. ✅ **Proved Step 2 completely**: Irreducible factors of denom give poles at linear places
   - For any irreducible factor π | denom, constructed place v_π with asIdeal = span{π}
   - Proved v_π.intValuation(denom) < 1 (π ∈ v_π.asIdeal)
   - Proved v_π.intValuation(num) = 1 (coprimality: π ∤ num)
   - Therefore valuation(f) = val(num)/val(denom) > 1 (f has pole at v_π)
   - From L(D) membership: valuation(f) ≤ exp(D(v_π)), so exp(D(v_π)) > 1
   - Therefore D(v_π) > 0, so v_π ∈ D.support
   - By IsLinearPlaceSupport: v_π is a linear place
   - Conclusion: all irreducible factors of denom are linear (X - α)

**Remaining for `projective_LRatFunc_eq_zero_of_neg_deg`** (Step 3 - counting argument):
The formal counting argument requires tracking multiplicities:
- Σ_{D(v)>0} D(v) ≥ deg(denom) (from pole multiplicities)
- Σ_{D(v)<0} |D(v)| > Σ_{D(v)>0} D(v) (from deg(D) < 0)
- Σ_{D(v)<0} |D(v)| ≤ deg(num) (from zero multiplicities)
- deg(num) ≤ deg(denom) (from noPoleAtInfinity)
- Contradiction: deg(denom) < deg(denom)

---

## Cycle 216 Progress

**Completed**:
1. ✅ **Added `IsLinearPlaceSupport D` assumption** to `projective_LRatFunc_eq_zero_of_neg_deg` and downstream theorems
2. ✅ **Proved Step 1 completely**: For non-constant f with noPoleAtInfinity, denom has positive degree
   - If denom.natDegree = 0, then denom is a constant (C c)
   - From noPoleAtInfinity: deg(num) ≤ deg(denom) = 0, so num is also constant (C n)
   - Then f = C n / C c = C (n/c), a constant - contradiction

**Key insight on IsLinearPlaceSupport**:
The theorem as originally stated (without IsLinearPlaceSupport) is actually FALSE for general divisors. Counterexample:
- D = [(X), -2] + [(π), 1] where π is irreducible of degree 2
- deg(D) = -1 < 0
- But f = X²/π satisfies L(D) with noPoleAtInfinity (both have degree 2)

For divisors supported only on linear places, the unweighted degree equals the weighted degree, making the theorem true.

---

## Cycle 215 Progress

**Research completed**: Full proof strategy for `projective_LRatFunc_eq_zero_of_neg_deg`

**Key discovery**: The proof does NOT require weighted degrees or product formula infrastructure. A simpler counting argument works:

**Proof strategy (non-constant case)**:
1. For non-constant f with noPoleAtInfinity, show `denom.natDegree > 0` (else f = constant)
2. denom has at least one irreducible factor π; at (π), f has a pole
3. At poles: `val(f) > 1`, so `D((π)) ≥ 1` (from L(D) membership)
4. Let `P = {poles of f}`, then `Σ_{v ∈ P} D(v) ≥ Σ multiplicities ≥ 1`
5. Since `deg(D) < 0`, we have `Σ_{v ∉ P} D(v) < -1`
6. Places with `D(v) < 0` require `val(f) < 1`, i.e., f has zeros there
7. **Counting**: `|{v : D(v) < 0}| > total pole multiplicities`
8. But each such v is a factor of num, so `|{v : D(v) < 0}| ≤ deg(num) ≤ deg(denom)`
9. And `deg(denom) ≥ total pole multiplicities`, giving contradiction

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
    ├─→ IsLinearPlaceSupport assumption ✅ ADDED (Cycle 216)
    ├─→ non-constant Step 1 (denom positive degree) ✅ DONE (Cycle 216)
    └─→ non-constant Steps 2-5 (counting argument) ← NEXT
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
