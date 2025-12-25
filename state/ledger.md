# Riemann-Roch Formalization Ledger

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 305
**Total Sorries**: 13 (4 new infrastructure + 3 high-level + 6 axioms)
**Elliptic Axioms**: 8

---

## Sorry Classification

### Content Sorries - New Infrastructure (4)
| Location | Line | Description | Difficulty |
|----------|------|-------------|------------|
| PlaceDegree | 643 | `pow_generator_dvd_iff_le_ord` | Easy (Nat arithmetic) ← NEXT |
| PlaceDegree | 733 | `intValuation_eq_exp_neg_ord` | Medium (valuation API) |
| PlaceDegree | 752 | `natDegree_eq_sum_ord_mul_degree` | Medium (UFD, blocked) |
| PlaceDegree | 782 | `intDegree_ge_deg_of_valuation_bounds_and_linear_support` | Blocked on above |

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
| 304 | Fill `ord_generator_self` and `ord_generator_other` | ✅ DONE |
| 305 | Add UFD infrastructure + ord lemmas | ✅ DONE |
| 306 | Fill `pow_generator_dvd_iff_le_ord` (Nat arithmetic) | **NEXT** (Easy) |
| 307 | Fill `natDegree_eq_sum_ord_mul_degree` using above | Blocked on 306 |
| 308 | Fill `intValuation_eq_exp_neg_ord` | Medium (valuation API) |
| 309+ | High-level AdelicH1Full sorries | Blocked |

### Cycle 305 Summary
**Completed**:
- Added UFD/normalization imports
- Proved `generator_normalize`: generators are monic hence normalized
- Added `pow_generator_dvd_iff_le_ord` (sorry - blocked on Nat arithmetic)
- Proved `ord_eq_count_normalizedFactors`: ord = count in normalized factors
- Proved `exists_place_with_generator`: bijection monic irreducibles ↔ places
- Proved `natDegree_normalizedFactors_prod`: product of factors has same natDegree
- Proved `monic_of_mem_normalizedFactors`: normalized factors are monic
- Proved `natDegree_normalizedFactors_prod_eq_sum`: natDegree = sum over multiset

**Blocked on**: `pow_generator_dvd_iff_le_ord` - Nat.find subtraction arithmetic
The proof requires showing `gen^n | p ↔ n ≤ (Nat.find ... - 1)` which needs
careful handling of Nat subtraction. The logic is clear but Lean's Nat omega
struggles with `m - 1` patterns.

### Cycle 306 Target
**File**: PlaceDegree.lean:643
**Lemma**: `pow_generator_dvd_iff_le_ord`
**Goal**: `generator k v ^ n ∣ p ↔ n ≤ ord k v p`
**Approach**:
- `ord k v p = Nat.find(...) - 1` where Nat.find gives first m with gen^m ∤ p
- If gen^n | p, then n < Nat.find, so n ≤ Nat.find - 1 = ord
- If n ≤ ord, then n < Nat.find, so by Nat.find_min, gen^n | p
- Needs: `Nat.sub_add_cancel`, `Nat.succ_le_of_lt`, `Nat.lt_succ_self`

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

*Updated Cycle 304. See ledger_archive.md for historical cycles.*
