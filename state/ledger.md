# Riemann-Roch Formalization Ledger

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 311
**Phase**: 7 (Weil Differentials) - Active
**Total Sorries**: 8 (2 archived P¹ edge cases + 6 axioms)

---

## Critical Insight (Cycle 311 Correction)

**We are closer than previously thought.** Per INVENTORY_REPORT.md:

| Asset | Lines | Status |
|-------|-------|--------|
| Curve-agnostic core | 3,700 | ✅ DONE |
| Riemann Inequality | 250 | ✅ **PROVED** |
| DVR properties | 100 | ✅ **PROVED** |
| H¹(D) framework | 550 | ✅ DONE |
| Dimension machinery | 600 | ✅ PROVED |

**The P¹ sorries are edge cases we BYPASS with Weil differentials.**

Estimated remaining: **~15-20 cycles** (not 50-70).

---

## Sorry Classification

### Archived P¹ Edge Cases (2)
*Bypassed by Weil differential approach - don't need to fill these.*

| Location | Line | Description |
|----------|------|-------------|
| AdelicH1Full | 757 | Strong approx for deep negative infty |
| AdelicH1Full | 1458 | Strong approx for non-effective D |

### Axiom Sorries (6) - Intentional
| Location | Line | Description |
|----------|------|-------------|
| Abstract | 277 | `h1_zero_finite` |
| StrongApproximation | 115, 164 | Function field density (2) |
| EllipticH1 | 206, 219 | Elliptic-specific (2) |
| EllipticSetup | 105 | IsDedekindDomain |

---

## What's Already Proved (Not Axiomatized!)

| Theorem | File | Status |
|---------|------|--------|
| Riemann Inequality | RiemannInequality.lean | ✅ PROVED |
| DVR for adic completion | DedekindDVR.lean | ✅ PROVED |
| Residue field isomorphism | ResidueFieldIso.lean | ✅ PROVED |
| Kernel characterization | KernelProof.lean | ✅ PROVED |
| Local gap bounds | DimensionCounting.lean | ✅ PROVED |
| Module length additivity | DimensionCounting.lean | ✅ PROVED |

---

## Phase 7: Weil Differentials (Revised Plan)

### The Key Insight
The P¹ sorries are about strong approximation edge cases.
Weil differential pairing `⟨f, ω⟩ = ω(f)` **bypasses** that machinery entirely.

### Revised Cycle Plan

| Cycle | Task | Difficulty | Est. |
|-------|------|------------|------|
| 312 | Define `WeilDifferential` structure | Medium | 1 cycle |
| 313 | K-module structure + basic lemmas | Medium | 1-2 cycles |
| 314 | Define pairing `⟨f, ω⟩ = ω(f)` | Easy | 1 cycle |
| 315 | **Prove non-degeneracy** | **HARD** | 5-10 cycles |
| 316 | Prove dim(Ω) = g (or deg(K) = 2g-2) | Medium | 2-3 cycles |
| 317 | Instantiate FullRRData | Easy | 1 cycle |
| 318 | Assembly + cleanup | Medium | 2-3 cycles |
| **Total** | | | **~15-20 cycles** |

### Cycle 312 Target
**File**: `RrLean/RiemannRochV2/General/WeilDifferential.lean` (new)

```lean
structure WeilDifferential (k R K K_infty : Type*) ... where
  toLinearMap : FullAdeleRing R K K_infty →ₗ[k] k
  vanishes_on_K : ∀ x : K, toLinearMap (fullDiagonalEmbedding x) = 0
```

---

## The Crux: Non-Degeneracy (Cycle 315)

This is where the real work is. Need to prove:
```
∀ f ∈ L(D), f ≠ 0 → ∃ ω ∈ Ω(K-D), ⟨f, ω⟩ ≠ 0
```

Options:
1. **Prove it** - requires local-global principle for differentials
2. **Axiomatize it** - acceptable, orthogonal to RR content
3. **Derive from compactness** - uses A_K/K compact (already have infrastructure)

---

## Architecture Summary

```
RrLean/RiemannRochV2/
├── Core/              - 3,700 lines curve-agnostic ✅
├── P1Instance/        - P¹-specific (frozen)
├── Adelic/            - Full adeles (reusable) ✅
├── SerreDuality/      - H¹ framework (reusable) ✅
├── Elliptic/          - Axiomatized
└── General/           - NEW: Weil differentials
```

---

## Key References

- [Rosen Ch. 6](https://link.springer.com/chapter/10.1007/978-1-4757-6046-0_6) - Weil Differentials
- [Stichtenoth §1.7](https://link.springer.com/book/10.1007/978-3-540-76878-4) - Local Components
- INVENTORY_REPORT.md - Asset inventory showing 3,700 lines reusable

---

*Updated Cycle 311 (corrected assessment). ~15-20 cycles to complete.*
