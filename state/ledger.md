# Riemann-Roch Formalization Ledger

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 322
**Phase**: 7 (Weil Differentials) - Active
**Total Sorries**: 8 (2 archived P¹ edge cases + 6 axioms)

---

## Cycle 322 Completed

**Goal**: Analyze `ell_zero_of_neg_deg` (vanishing for negative degree).

### Analysis Results

**The axiom `ell_zero_of_neg_deg`**: if deg(D) < 0, then ℓ(D) = 0.

**Classical proof requires:**
1. If f ∈ L(D) is nonzero, then div(f) + D ≥ 0 (effective)
2. Principal divisors have degree 0: deg(div(f)) = 0 (**product formula**)
3. Therefore deg(D) = deg(div(f) + D) ≥ 0
4. Contrapositive: deg(D) < 0 ⟹ L(D) = 0

**Why we axiomatize it:**
The product formula (step 2) requires degree-weighted sums over ALL irreducible
polynomials, not just rational points. The "naive" formula over Fq-rational points
is FALSE in general (see `ProductFormula.lean` counterexample).

### Where ell_zero_of_neg_deg IS Proved

1. **P¹ with linear places**: `projective_LRatFunc_eq_zero_of_neg_deg` in RatFuncPairing.lean
2. **Adelic approach**: In `AdelicH1v2.lean`, derived from Serre duality + h1_vanishing

### Alternative Derivation (AdelicRRData)

```
If deg(D) < 0:
  deg(K - D) = (2g-2) - deg(D) > 2g - 2
  So h¹(K - D) = 0 by h1_vanishing
  By Serre duality: h¹(K - D) = ℓ(K - (K - D)) = ℓ(D)
  Therefore ℓ(D) = 0
```

This swaps `ell_zero_of_neg_deg` for `h1_vanishing` as the axiom.

### Deliverables

1. **Documentation**: Added comprehensive analysis to WeilDifferential.lean
   (new section "About ell_zero_of_neg_deg (Cycle 322 Analysis)")
2. **Architecture confirmed**: `FullRRBridge` correctly axiomatizes this property
3. **Path forward identified**: Can discharge for specific curves or via adelic approach

### Key Insight

The axiom is **correctly placed** in `FullRRBridge`. It can be discharged by:
- Proving the full product formula (hard in general)
- Using the adelic approach with h1_vanishing
- Specializing to curve types where product formula is simpler (P¹, elliptic)

---

## Cycle 323 Target

**Priority**: Focus on completing the bridge for specific curve instances.

**Options**:
1. **Instantiate P¹**: Use existing `ell_ratfunc_projective_zero_of_neg_deg`
2. **Adelic bridge**: Connect `AdelicRRData` to `FullRRBridge`
3. **Alternative**: Prove RR directly for high-degree divisors where ℓ(K-D) = 0

---

## Cycle 321 Summary (Archived)

**Goal**: Bridge WeilRRData' to FullRRData.

---

## Cycle 320 Summary (Archived)

**Goal**: Prove dimension theorem, clean up unused lemmas.

### Deliverables
- `finrank_eq_of_perfect_pairing` - PROVED
- Cleanup of unused lemmas
- Sorry count reduced 10 → 8

---

## Cycle 319 Summary (Archived)

**Goal**: Bridge WeilDifferential to FullRRData for final assembly.

### Deliverables
- HasPerfectPairing' structure
- WeilRRData' structure
- serre_duality_dim' theorem
- Dimension theorem (with sorry)

---

## Cycle 318 Summary (Archived)

**Goal**: Hook WeilDifferential.lean into build, add non-degeneracy infrastructure.

### Deliverables
- Build integration (RrLean/RiemannRochV2/General.lean)
- Non-degeneracy definitions (PairingNondegenerateLeft/Right/Perfect)
- CanonicalData structure with P¹ and elliptic instances

---

## Cycle 317 Summary (Archived)

---

## Cycle 316 (Archived - Contains Bugs)

**Note**: Cycle 316 code did not compile. Reverted in Cycle 317.

The *intended* additions were:
- Non-degeneracy definitions (PairingNondegenerateLeft/Right/Perfect)
- HasCanonicalDivisor typeclass
- Dimension theorems from perfect pairing

These need to be properly re-implemented with correct type parameters.

---

## Cycle 315 Completed

**Extended**: `RrLean/RiemannRochV2/General/WeilDifferential.lean`

### Restricted Pairing Infrastructure
- [x] `serrePairingRestricted` - bilinear map L(D) × Ω(-D) → k
- [x] `serrePairingRestricted_apply` - evaluation simp lemma
- [x] `serrePairingGeneral` - general pairing L(D) × Ω(E) → k for any D, E
- [x] `serrePairingGeneral_apply` - evaluation simp lemma

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
| 316 | Non-degeneracy defs + HasCanonicalDivisor | ✅ DONE |

### Remaining
| Cycle | Task | Difficulty | Est. |
|-------|------|------------|------|
| 317-318 | Instantiate for P¹ or elliptic | Medium | 2 cycles |
| 319-320 | Bridge to FullRRData | Easy-Medium | 2 cycles |
| 321-323 | Assembly + final RR theorem | Medium | 2-3 cycles |
| **Total** | | | **~6-8 cycles** |

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
