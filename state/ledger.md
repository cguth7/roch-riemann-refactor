# Riemann-Roch Formalization Ledger

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 302
**Total Sorries**: 11
**Elliptic Axioms**: 8

---

## Sorry Classification

### Content Sorries (5)
| Location | Line | Description | Difficulty |
|----------|------|-------------|------------|
| PlaceDegree | 155 | `linear_of_degree_eq_one` | **Low** ← NEXT |
| PlaceDegree | 524 | `intDegree_ge_deg_of_valuation_bounds_and_linear_support` | Medium |
| AdelicH1Full | 757 | Deep negative inftyCoeff | High |
| AdelicH1Full | 1328 | Degree gap lemma | Medium |
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
| 303 | Fill `linear_of_degree_eq_one` | **NEXT** (Low) |
| 304 | Fill main degree-valuation lemma | Blocked on 303 |
| 305 | Fill AdelicH1Full:1328 | Blocked on 304 |
| 306+ | Infinity bound sorries | Needs new approach |

### Cycle 303 Target
**File**: PlaceDegree.lean:155
**Lemma**: `linear_of_degree_eq_one`
**Proof sketch**:
1. degree(v) = 1 means generator(v).natDegree = 1
2. Monic degree-1 polynomial = X - C α (use `Polynomial.natDegree_eq_one`)
3. So generator(v) = X - C α, hence v = linearPlace α

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

*Updated Cycle 302. See ledger_archive.md for historical cycles.*
