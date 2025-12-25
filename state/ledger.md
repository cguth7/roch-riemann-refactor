# Riemann-Roch Formalization Ledger

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 304
**Total Sorries**: 12 (3 new infrastructure + 3 high-level + 6 axioms)
**Elliptic Axioms**: 8

---

## Sorry Classification

### Content Sorries - New Infrastructure (3)
| Location | Line | Description | Difficulty |
|----------|------|-------------|------------|
| PlaceDegree | 633 | `intValuation_eq_exp_neg_ord` | Medium ← NEXT |
| PlaceDegree | 652 | `natDegree_eq_sum_ord_mul_degree` | Medium (UFD) |
| PlaceDegree | 682 | `intDegree_ge_deg_of_valuation_bounds_and_linear_support` | Blocked on above |

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
| 305 | Fill `natDegree_eq_sum_ord_mul_degree` (UFD) | **NEXT** (Medium) |
| 306 | Fill `intValuation_eq_exp_neg_ord` | Deferred (valuation API) |
| 307 | Fill `intDegree_ge_deg...` using above | Blocked |
| 308+ | High-level AdelicH1Full sorries | Blocked |

### Cycle 304 Summary
**Completed**:
- Fixed `ord` definition (was off-by-one: added `- 1` to Nat.find result)
- Proved `ord_generator_self`: gen² ∤ gen for irreducible gen, so ord = 1
- Proved `ord_generator_other`: gen(w) ∤ gen(v) for v ≠ w by coprimality, so ord = 0

**Proof Techniques**:
- Used `Nat.find_min'` for upper bounds
- Used `Nat.le_find_iff` for lower bounds
- Handled DecidablePred instance mismatch with `convert ... using 2`

### Cycle 305 Target
**File**: PlaceDegree.lean:652
**Lemma**: `natDegree_eq_sum_ord_mul_degree` (UFD approach)
**Goal**: Express polynomial degree as sum of multiplicities:
```lean
p.natDegree = ∑ v ∈ S, ord k v p * degree k v
```
**Proof sketch** (direct UFD, bypasses valuation bridge):
1. Use unique factorization: `p = c * ∏ gen(v)^{ord_v(p)}`
2. `natDegree` is multiplicative: `natDegree(a*b) = natDegree(a) + natDegree(b)`
3. `natDegree(gen(v)) = degree(v)` by definition
4. `natDegree(c) = 0` for constants
5. Use `ord_generator_self` and `ord_generator_other` to identify multiplicities

**Alternative** (deferred): `intValuation_eq_exp_neg_ord` bridges valuation to `ord` via Mathlib's `Associates.count`. More complex, requires diving into valuation internals.

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
