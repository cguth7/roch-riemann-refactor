# Riemann-Roch Formalization Ledger

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 315
**Phase**: 7 (Weil Differentials) - Active
**Total Sorries**: 8 (2 archived P¹ edge cases + 6 axioms)

---

## Cycle 315 Completed

**Extended**: `RrLean/RiemannRochV2/General/WeilDifferential.lean`

### Restricted Pairing Infrastructure
- [x] `serrePairingRestricted` - bilinear map L(D) × Ω(-D) → k
- [x] `serrePairingRestricted_apply` - evaluation simp lemma
- [x] `serrePairingGeneral` - general pairing L(D) × Ω(E) → k for any D, E
- [x] `serrePairingGeneral_apply` - evaluation simp lemma

### Non-Degeneracy Strategy Documented
Outlined three approaches for proving non-degeneracy (Cycle 316+):
1. From A_K/K compactness → perfect pairing
2. Local non-degeneracy at each place → global
3. Axiomatize if needed

### Technical Notes
Import added: `RrLean.RiemannRochV2.Definitions.Projective` for `RRSpace_proj`.
Non-degeneracy definitions deferred to Cycle 316 due to typeclass complexity.

---

## Cycle 316 Target

**Non-degeneracy formalization**:
1. Define `PairingNondegenerateLeft`, `PairingNondegenerateRight`, `PairingPerfect`
2. Prove `dim_eq_of_perfect_pairing`
3. Begin proving non-degeneracy (or axiomatize)

---

## Cycle 314 Completed

**Extended**: `RrLean/RiemannRochV2/General/WeilDifferential.lean`

### Ω(D) Properties
- [x] `divisorDifferentials_antitone` - D ≤ E ⟹ Ω(E) ≤ Ω(D) (with explicit types)
- [x] `mem_divisorDifferentials_zero_iff` - characterization of Ω(0)

### Serre Pairing Infrastructure
- [x] `serrePairingF` - ⟨f, ω⟩ = ω(diag(f)) evaluation
- [x] `serrePairingF_zero_left/right` - zero lemmas
- [x] `serrePairingF_add_left/right` - additivity lemmas
- [x] `serrePairingF_smul_left/right` - k-linearity lemmas
- [x] `serrePairingLinearω` - linear map in ω for fixed f
- [x] `serrePairingBilinear` - full k-bilinear pairing K →ₗ[k] Ω →ₗ[k] k

### Technical Resolution
Typeclass issues with `Algebra ? K_infty` fixed by adding explicit
type annotations `(k := k) (R := R) (K := K) (K_infty := K_infty)` and
explicit return type annotations on antitone/zero_iff lemmas.

---

## Cycle 313 Completed

**Extended**: `RrLean/RiemannRochV2/General/WeilDifferential.lean`

### Local Components
- [x] `finiteAdeleSingle` - construct finite adele with single component
- [x] `embedFinitePlace` - embed local element into full adeles
- [x] `hasOrderGe` - predicate for order ≥ n at a place
- [x] `hasOrderGe_of_le` - monotonicity lemma
- [x] `satisfiesDivisorConstraint` - divisor constraint predicate
- [x] `DivisorDifferentials D` - Ω(D) as k-submodule

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
| WeilDifferential | ~690 | ✅ **EXPANDED** |

**The P¹ sorries are edge cases we BYPASS with Weil differentials.**

Estimated remaining: **~10-15 cycles** (3 more cycles completed).

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
| 313 | Local components + Ω(D) definition | ✅ DONE |
| 314 | Serre pairing `⟨f, ω⟩ = ω(diag f)` | ✅ DONE |
| 315 | Restricted pairing L(D) × Ω(E) → k | ✅ DONE |

### Remaining
| Cycle | Task | Difficulty | Est. |
|-------|------|------------|------|
| 316-320 | **Prove non-degeneracy** | **HARD** | 4-6 cycles |
| 321-323 | Prove dim(Ω) = g (or deg(K) = 2g-2) | Medium | 2-3 cycles |
| 324 | Instantiate FullRRData | Easy | 1 cycle |
| 325-327 | Assembly + cleanup | Medium | 2-3 cycles |
| **Total** | | | **~9-14 cycles** |

---

## The Crux: Non-Degeneracy (Cycle 316-320)

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
