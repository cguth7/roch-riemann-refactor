# Riemann-Roch Formalization Ledger

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 307
**Total Sorries**: 11 (2 new infrastructure + 3 high-level + 6 axioms)
**Elliptic Axioms**: 8

---

## Sorry Classification

### Content Sorries - New Infrastructure (2)
| Location | Line | Description | Difficulty |
|----------|------|-------------|------------|
| PlaceDegree | 802 | `natDegree_eq_sum_ord_mul_degree` | Medium (UFD) ← NEXT |
| PlaceDegree | 832 | `intDegree_ge_deg_of_valuation_bounds_and_linear_support` | Blocked on above |

### Content Sorries - High Level (3)
| Location | Line | Description | Difficulty |
|----------|------|-------------|------------|
| AdelicH1Full | 757 | `globalPlusBoundedSubmodule_full_eq_top_deep_neg_infty` | High |
| AdelicH1Full | 1328 | `intDegree_ge_deg_of_valuation_bounds_and_linear_support_ratfunc` | Medium (blocked on PlaceDegree) |
| AdelicH1Full | 1460 | `globalPlusBoundedSubmodule_full_eq_top_not_effective` | High |

### Axiom Sorries (6) - Intentional
| Location | Line | Description |
|----------|------|-------------|
| Abstract | 277 | `h1_zero_finite` - H¹ finite-dimensionality |
| StrongApproximation | 115 | Strong approximation instance (1) |
| StrongApproximation | 164 | Strong approximation instance (2) |
| EllipticH1 | 206 | Elliptic H¹ axiom (1) |
| EllipticH1 | 219 | Elliptic H¹ axiom (2) |
| EllipticSetup | 105 | `IsDedekindDomain` for elliptic coordinate ring |

---

## What's Proved

### P¹ over Finite Field (98% complete)
- Full adelic infrastructure
- Divisor/RR-space definitions
- Genus = 0 computation
- ℓ(D) = max(0, deg(D)+1) for deg(D) ≥ -1
- Serre duality (partial)

### Elliptic Curves (axiomatized)
- Full RR theorem (uses 8 axioms)
- Genus = 1 verification
- ℓ(D) formulas

---

## Next Steps

| Cycle | Task | Status |
|-------|------|--------|
| 303 | Fill `linear_of_degree_eq_one` + add ord infrastructure | ✅ DONE |
| 304 | Fill `ord_generator_self` and `ord_generator_other` | ✅ DONE |
| 305 | Add UFD infrastructure + ord lemmas | ✅ DONE |
| 306 | Fill `pow_generator_dvd_iff_le_ord` (Nat arithmetic) | ✅ DONE |
| 307 | Fill `intValuation_eq_exp_neg_ord` | ✅ DONE |
| 308 | Fill `natDegree_eq_sum_ord_mul_degree` | **NEXT** (Medium - UFD) |
| 309+ | High-level AdelicH1Full sorries | Blocked |

### Cycle 307 Summary
**Completed**:
- Filled `intValuation_eq_exp_neg_ord` - key bridge between valuation and divisibility
- Proof uses `Ideal.count_associates_eq'` from Mathlib to connect:
  - `v.intValuation p = exp(-(Associates.count on ideal factorization))`
  - `ord k v p = count in polynomial factorization`
- Key insight: `v.asIdeal = span{generator(v)}` via `asIdeal_eq_span_generator`
- Used `pow_generator_dvd_iff_le_ord` to establish divisibility bounds

**Unblocked**: Path to `natDegree_eq_sum_ord_mul_degree` is clearer

### Cycle 308 Target
**File**: PlaceDegree.lean:802
**Lemma**: `natDegree_eq_sum_ord_mul_degree`
**Goal**: `(p.natDegree : ℤ) = ∑ v ∈ S, (ord k v p : ℤ) * (degree k v : ℤ)`
**Approach**:
- Unique factorization: `p = c * ∏ gen(v)^{ord_v(p)}`
- `natDegree(p) = natDegree(∏ gen(v)^{ord_v(p)})` (leading coeff is unit)
- Use `natDegree_multiset_prod_of_monic` for product
- `natDegree(gen(v)^n) = n * natDegree(gen(v)) = n * degree(v)`

---

## Architecture Summary

```
RrLean/RiemannRochV2/
├── Core/           - Divisor types, basic defs
├── P1Instance/     - P¹-specific: PlaceDegree, RRSpace
├── Adelic/         - Full adeles, compactness
├── SerreDuality/   - H¹ computations, pairing
├── Elliptic/       - Elliptic curve instance
└── Definitions/    - Infrastructure
```

**Total**: ~16K LOC

---

*Updated Cycle 307. See ledger_archive.md for historical cycles.*
