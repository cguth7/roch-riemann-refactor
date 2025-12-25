# Riemann-Roch Formalization Ledger

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 303
**Total Sorries**: 14 (5 new infrastructure + 3 high-level + 6 axioms)
**Elliptic Axioms**: 8

---

## Sorry Classification

### Content Sorries - New Infrastructure (5)
| Location | Line | Description | Difficulty |
|----------|------|-------------|------------|
| PlaceDegree | 550 | `ord_generator_self` | Low ← NEXT |
| PlaceDegree | 555 | `ord_generator_other` | Low |
| PlaceDegree | 562 | `intValuation_eq_exp_neg_ord` | Medium |
| PlaceDegree | 581 | `natDegree_eq_sum_ord_mul_degree` | Medium |
| PlaceDegree | 611 | `intDegree_ge_deg_of_valuation_bounds_and_linear_support` | Blocked on above |

### Content Sorries - High Level (3)
| Location | Line | Description | Difficulty |
|----------|------|-------------|------------|
| AdelicH1Full | 757 | Deep negative inftyCoeff | High |
| AdelicH1Full | 1328 | Degree gap lemma | Medium (blocked) |
| AdelicH1Full | 1460 | Non-effective strong approx | High |

### Axiom Sorries (6) - Intentional
| Location | Description |
|----------|-------------|
| Abstract | `h1_zero_finite` - H¹ finite-dimensionality |
| StrongApproximation (2) | Strong approximation for function fields |
| EllipticH1 (2) | Elliptic-specific H¹ computations |
| EllipticSetup | Elliptic setup axiom |

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
| 304 | Fill `ord_generator_self` and `ord_generator_other` | **NEXT** (Low) |
| 305 | Fill `intValuation_eq_exp_neg_ord` | Medium |
| 306 | Fill `natDegree_eq_sum_ord_mul_degree` | Medium (UFD) |
| 307 | Fill `intDegree_ge_deg...` using above | Blocked |
| 308+ | High-level AdelicH1Full sorries | Blocked |

### Cycle 304 Target
**File**: PlaceDegree.lean:550, 555
**Lemmas**: `ord_generator_self`, `ord_generator_other`
**Proof sketch**:
- `ord_generator_self`: gen^1 | gen trivially; gen^2 ∤ gen because irreducible
- `ord_generator_other`: gen(w)^1 ∤ gen(v) by coprimality (use `generator_not_mem_other_prime`)

### New Infrastructure (Cycle 303)
Added foundational ord/degree framework in PlaceDegree.lean:
- `exists_pow_generator_not_dvd` - Well-foundedness for ord ✅
- `ord` - Multiplicity of p at place v (via Nat.find) ✅ (defn)
- `natDegree_eq_sum_ord_mul_degree` - Key UFD theorem (sorry)

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

*Updated Cycle 303. See ledger_archive.md for historical cycles.*
