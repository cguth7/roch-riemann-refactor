# Riemann-Roch Formalization Ledger

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 306
**Total Sorries**: 12 (3 new infrastructure + 3 high-level + 6 axioms)
**Elliptic Axioms**: 8

---

## Sorry Classification

### Content Sorries - New Infrastructure (3)
| Location | Line | Description | Difficulty |
|----------|------|-------------|------------|
| PlaceDegree | 770 | `intValuation_eq_exp_neg_ord` | Medium (valuation API) ← NEXT |
| PlaceDegree | 789 | `natDegree_eq_sum_ord_mul_degree` | Medium (UFD) |
| PlaceDegree | 819 | `intDegree_ge_deg_of_valuation_bounds_and_linear_support` | Blocked on above |

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
| 307 | Fill `intValuation_eq_exp_neg_ord` | **NEXT** (Medium - valuation API) |
| 308 | Fill `natDegree_eq_sum_ord_mul_degree` | Medium (UFD) |
| 309+ | High-level AdelicH1Full sorries | Blocked |

### Cycle 306 Summary
**Completed**:
- Filled `pow_generator_dvd_iff_le_ord` - key divisibility characterization of ord
- Proof uses `generalize` to capture Nat.find from goal and work with unified decidability instance
- Used `Nat.find_spec` and `Nat.find_min` with the generalized Nat.find
- Key insight: `n ≤ ord ↔ n < Nat.find ↔ gen^n | p`
- Nat arithmetic: `Nat.sub_lt_iff_lt_add`, `Nat.lt_of_le_pred`

**Unblocked**: `ord_eq_count_normalizedFactors` now uses `pow_generator_dvd_iff_le_ord`

### Cycle 307 Target
**File**: PlaceDegree.lean:770
**Lemma**: `intValuation_eq_exp_neg_ord`
**Goal**: `v.intValuation p = WithZero.exp (-(ord k v p : ℤ))`
**Approach**:
- Both definitions count the same thing (multiplicity of generator)
- `intValuation` uses Associates.count on ideals
- `ord` uses divisibility of generator
- Bridge: `v.asIdeal = span{generator(v)}`

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

*Updated Cycle 306. See ledger_archive.md for historical cycles.*
