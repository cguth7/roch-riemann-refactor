# Riemann-Roch Formalization Ledger

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 310
**Total Sorries**: 8 (0 new infrastructure + 2 high-level + 6 axioms)
**Elliptic Axioms**: 8

---

## Sorry Classification

### Content Sorries - New Infrastructure (0)
*All new infrastructure filled!*

### Content Sorries - High Level (2)
| Location | Line | Description | Difficulty |
|----------|------|-------------|------------|
| AdelicH1Full | 757 | `globalPlusBoundedSubmodule_full_eq_top_deep_neg_infty` | High |
| AdelicH1Full | 1458 | `globalPlusBoundedSubmodule_full_eq_top_not_effective` | High |

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
| 308 | Fill `natDegree_eq_sum_ord_mul_degree` | ✅ DONE |
| 309 | Fill `intDegree_ge_deg_of_valuation_bounds_and_linear_support` | ✅ DONE |
| 310 | Fill `intDegree_ge_deg_of_valuation_and_denom_constraint` (AdelicH1Full) | ✅ DONE |
| 311+ | High-level AdelicH1Full sorries | **NEXT** |

### Cycle 310 Summary
**Completed**:
- Filled `intDegree_ge_deg_of_valuation_and_denom_constraint` at AdelicH1Full.lean:1328
- Simple wrapper: converts `IsLinearPlaceSupport D` to `∀ v ∈ D.support, degree Fq v = 1`
- Then applies `PlaceDegree.intDegree_ge_deg_of_valuation_bounds_and_linear_support`
- Uses `linearPlace_degree_eq_one` to prove degree = 1 for linear places

**Remaining**: 2 high-level sorries in AdelicH1Full (deep negative infty + non-effective cases)

### Cycle 311 Target
**File**: AdelicH1Full.lean:757 or 1458
**Lemma**: One of the remaining high-level sorries
**Challenge**: These handle edge cases (deep negative inftyCoeff, non-effective divisors)
**Approach**: May require new infrastructure or can be deferred as low-priority edge cases

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

*Updated Cycle 310. See ledger_archive.md for historical cycles.*
