# Riemann-Roch Formalization Ledger

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 313
**Phase**: 7 (Weil Differentials) - Active
**Total Sorries**: 8 (2 archived P¹ edge cases + 6 axioms)

---

## Cycle 313 In Progress

**Extended**: `RrLean/RiemannRochV2/General/WeilDifferential.lean`

### Completed
- [x] `finiteAdeleSingle` - construct finite adele with single component
- [x] `embedFinitePlace` - embed local element into full adeles
- [x] `hasOrderGe` - predicate for order ≥ n at a place
- [x] `hasOrderGe_of_le` - monotonicity lemma
- [x] `satisfiesDivisorConstraint` - divisor constraint predicate
- [x] `DivisorDifferentials D` - Ω(D) as k-submodule

### Deferred (typeclass issues)
- [ ] `divisorDifferentials_antitone` - D ≤ E ⟹ Ω(E) ≤ Ω(D)
- [ ] `divisorDifferentials_zero_iff` - characterization of Ω(0)

### Technical Note
The antitone lemma has typeclass resolution issues with `Algebra ? K_infty`.
Fix: Either add explicit section variables or restructure the proof to
provide explicit type annotations. The `open Classical in` pattern works
for the definition but the lemmas need careful handling.

---

## Cycle 314 Target

**Continue Ω(D) properties**:
1. Fix typeclass issues in `divisorDifferentials_antitone`
2. Add `divisorDifferentials_zero_iff`
3. Start Serre pairing: `⟨f, ω⟩ = ω(diag(f))`

---

## Cycle 312 Completed

**Created**: `RrLean/RiemannRochV2/General/WeilDifferential.lean`

### Deliverables
- [x] `WeilDifferential` structure (linear functional on adeles vanishing on K)
- [x] `AddCommGroup` instance
- [x] `Module k` instance (k-vector space structure)
- [x] `Module K` instance with action `(c · ω)(a) = ω(c · a)`
- [x] `IsScalarTower k K WeilDifferential` (compatibility)
- [x] `CommRing` instance on `FullAdeleRing` (added to FullAdelesBase.lean)

### Key Definitions
```lean
structure WeilDifferential where
  toLinearMap : FullAdeleRing R K K_infty →ₗ[k] k
  vanishes_on_K : ∀ x : K, toLinearMap (fullDiagonalEmbedding R K K_infty x) = 0
```

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
| WeilDifferential | ~350 | ✅ **NEW** |

**The P¹ sorries are edge cases we BYPASS with Weil differentials.**

Estimated remaining: **~12-18 cycles** (down from 15-20).

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
| WeilDifferential k-module | WeilDifferential.lean | ✅ **NEW** |
| WeilDifferential K-module | WeilDifferential.lean | ✅ **NEW** |

---

## Phase 7: Weil Differentials (Updated Plan)

### Completed
| Cycle | Task | Status |
|-------|------|--------|
| 312 | WeilDifferential structure + K-module | ✅ DONE |

### Remaining
| Cycle | Task | Difficulty | Est. |
|-------|------|------------|------|
| 313 | Divisor-constrained differentials Ω(D) | Medium | 1-2 cycles |
| 314 | Define pairing `⟨f, ω⟩ = ω(embed f)` | Easy | 1 cycle |
| 315-320 | **Prove non-degeneracy** | **HARD** | 5-8 cycles |
| 321-323 | Prove dim(Ω) = g (or deg(K) = 2g-2) | Medium | 2-3 cycles |
| 324 | Instantiate FullRRData | Easy | 1 cycle |
| 325-327 | Assembly + cleanup | Medium | 2-3 cycles |
| **Total** | | | **~12-18 cycles** |

---

## Cycle 313 Target

**File**: `RrLean/RiemannRochV2/General/WeilDifferential.lean` (extend)

Add divisor-constrained differentials:
```lean
/-- Ω(D) = Weil differentials with poles bounded by D -/
def DivisorDifferentials (D : DivisorV2 R) : Submodule K (WeilDifferential k R K K_infty) := ...
```

This requires defining "local order" of a differential at each place.

---

## The Crux: Non-Degeneracy (Cycle 315-320)

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
└── General/           - WeilDifferential.lean ✅ NEW
```

---

## Key References

- [Rosen Ch. 6](https://link.springer.com/chapter/10.1007/978-1-4757-6046-0_6) - Weil Differentials
- [Stichtenoth §1.7](https://link.springer.com/book/10.1007/978-3-540-76878-4) - Local Components
- INVENTORY_REPORT.md - Asset inventory showing 3,700+ lines reusable

---

*Updated Cycle 312. WeilDifferential structure complete. ~12-18 cycles to complete.*
