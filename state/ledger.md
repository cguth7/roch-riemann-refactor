# Riemann-Roch Formalization Ledger

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 308
**Total Sorries**: 10 (1 new infrastructure + 3 high-level + 6 axioms)
**Elliptic Axioms**: 8

---

## Sorry Classification

### Content Sorries - New Infrastructure (1)
| Location | Line | Description | Difficulty |
|----------|------|-------------|------------|
| PlaceDegree | 936 | `intDegree_ge_deg_of_valuation_bounds_and_linear_support` | Medium ← NEXT |

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
| 308 | Fill `natDegree_eq_sum_ord_mul_degree` | ✅ DONE |
| 309 | Fill `intDegree_ge_deg_of_valuation_bounds_and_linear_support` | **NEXT** |
| 310+ | High-level AdelicH1Full sorries | Blocked |

### Cycle 308 Summary
**Completed**:
- Filled `natDegree_eq_sum_ord_mul_degree` - key theorem relating natDegree to sum over places
- Proof uses `Finset.sum_bij'` to establish bijection between:
  - `T = (normalizedFactors p).toFinset` (monic irreducible factors)
  - `{v : ord k v p ≠ 0}` (places with nonzero multiplicity)
- Key lemmas used:
  - `Finset.sum_multiset_map_count` to convert multiset sum to finset sum
  - `exists_place_with_generator` for the bijection
  - `ord_eq_count_normalizedFactors` to connect ord with count

**Unblocked**: `intDegree_ge_deg_of_valuation_bounds_and_linear_support` can now proceed

### Cycle 309 Target
**File**: PlaceDegree.lean:936
**Lemma**: `intDegree_ge_deg_of_valuation_bounds_and_linear_support`
**Goal**: For f = num/denom with valuation bounds, `f.intDegree ≥ D.deg`
**Approach**:
- Use `natDegree_eq_sum_ord_mul_degree` for both num and denom
- intDegree(f) = natDegree(num) - natDegree(denom)
- With IsLinearPlaceSupport (deg(v) = 1), simplifies to sum of ord differences
- Valuation constraints give: ord(num) - ord(denom) ≥ D(v) at each place

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

*Updated Cycle 308. See ledger_archive.md for historical cycles.*
