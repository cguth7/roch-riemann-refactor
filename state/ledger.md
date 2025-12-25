# Riemann-Roch Formalization Ledger

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 311
**Phase**: 7 (Weil Differentials) - Active
**Total Sorries**: 8 (2 archived P¹ edge cases + 6 axioms)

---

## Sorry Classification

### Content Sorries - Archived P¹ Edge Cases (2)
*These are PID-specific and not needed for general curves.*

| Location | Line | Description | Status |
|----------|------|-------------|--------|
| AdelicH1Full | 757 | `globalPlusBoundedSubmodule_full_eq_top_deep_neg_infty` | Archived |
| AdelicH1Full | 1458 | `globalPlusBoundedSubmodule_full_eq_top_not_effective` | Archived |

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

### P¹ over Finite Field (Frozen - Architecture Validator)
- Full adelic infrastructure ✅
- Divisor/RR-space definitions ✅
- Genus = 0 computation ✅
- ℓ(D) = max(0, deg(D)+1) for deg(D) ≥ -1 ✅
- Serre duality (effective D, non-negative inftyCoeff) ✅

### Elliptic Curves (genus 1, axiomatized)
- Full RR theorem ✅ (uses 5 axioms)
- Genus = 1 verification ✅
- ℓ(D) - ℓ(-D) = deg(D) ✅

---

## Phase 7: Weil Differentials

### Overview
Transition from P¹-specific residue pairing to general Weil differential pairing.

### Cycle Plan

| Cycle | Task | Status |
|-------|------|--------|
| 311 | Archive P¹ edge cases, activate Phase 7 | ✅ DONE |
| 312 | Define `WeilDifferential` structure | **NEXT** |
| 313 | Define `localComponent` extraction | Planned |
| 314 | Define `div(ω)` and `valuation_differential` | Planned |
| 315 | Define Serre pairing `⟨f, ω⟩ = ω(f)` | Planned |
| 316 | Canonical divisor properties | Planned |
| 317+ | Complete general RR | Future |

### Cycle 311 Summary
**Completed**:
- Archived P¹ edge case sorries (PID-specific, not generalizable)
- Updated REFACTOR_PLAN.md with Phase 7 roadmap
- Researched Weil differential definitions and references

**Key Decision**: The remaining AdelicH1Full sorries are artifacts of the PID-based strong approximation proof. They're not needed for general curves, which will use Weil differentials.

### Cycle 312 Target
**File**: `RrLean/RiemannRochV2/General/WeilDifferential.lean` (new)
**Goal**: Define `WeilDifferential` as linear functional on adeles vanishing on K

```lean
structure WeilDifferential (k R K K_infty : Type*) ... where
  toLinearMap : FullAdeleRing R K K_infty →ₗ[k] k
  vanishes_on_K : ∀ x : K, toLinearMap (fullDiagonalEmbedding x) = 0
```

**Deliverables**:
- [ ] Define `WeilDifferential` structure
- [ ] Prove K-module structure
- [ ] Basic lemmas (zero, add, smul)

---

## Architecture Summary

```
RrLean/RiemannRochV2/
├── Core/           - Divisor types, basic defs
├── P1Instance/     - P¹-specific (frozen)
├── Adelic/         - Full adeles (reusable)
├── SerreDuality/   - H¹ computations
├── Elliptic/       - Elliptic curves (axiomatized)
├── General/        - NEW: Weil differentials
└── Definitions/    - Infrastructure
```

**Total**: ~16K LOC

---

## Key References

- [Rosen Ch. 6](https://link.springer.com/chapter/10.1007/978-1-4757-6046-0_6) - Weil Differentials and Canonical Class
- [Stichtenoth §1.7](https://link.springer.com/book/10.1007/978-3-540-76878-4) - Local Components
- [Charles U. Thesis](https://dspace.cuni.cz/bitstream/handle/20.500.11956/62611/DPTX_2012_2_11320_0_392289_0_137152.pdf) - Computational Algorithms

---

*Updated Cycle 311. Phase 7 active. See REFACTOR_PLAN.md for detailed roadmap.*
