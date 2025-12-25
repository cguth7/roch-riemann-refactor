# Refactor Plan: P¹ → General Curves

**Status**: Phase 7 Active. **~15-20 cycles to completion.**
**Goal**: Sorry-free Riemann-Roch for smooth projective curves.

---

## Critical Insight (Cycle 311)

Per INVENTORY_REPORT.md, we have **3,700 lines of curve-agnostic infrastructure**:

| Asset | Status |
|-------|--------|
| Riemann Inequality | ✅ **PROVED** |
| DVR for completions | ✅ **PROVED** |
| H¹(D) framework | ✅ DONE |
| Dimension machinery | ✅ PROVED |
| FullRRData axiom package | ✅ DONE |

**The P¹ sorries are edge cases we BYPASS with Weil differentials.**

---

## Phase Summary

| Phase | Status | Achievement |
|-------|--------|-------------|
| 0-4 | ✅ Complete | P¹ infrastructure |
| 5 | ⏸️ Archived | P¹ edge cases (bypassed) |
| 6 | ✅ Complete | Elliptic (axiomatized) |
| 7 | ⏳ **Active** | Weil differentials → RR |

---

## Phase 7: Weil Differentials (Revised)

### Why This Approach

The P¹ sorries are about strong approximation for edge cases.
Weil differential pairing `⟨f, ω⟩ = ω(f)` **bypasses** that entirely.

We already have:
- H¹(D) as quotient of adeles ✅
- Riemann Inequality ✅
- Gap bounds ✅
- FullRRData framework ✅

We need:
- WeilDifferential definition
- Pairing is perfect (non-degeneracy)
- deg(K) = 2g-2

### Implementation Plan

#### Cycle 312: WeilDifferential Structure
**File**: `RrLean/RiemannRochV2/General/WeilDifferential.lean`

```lean
/-- A Weil differential is a linear functional on adeles vanishing on K -/
structure WeilDifferential (k R K K_infty : Type*)
    [Field k] [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field K_infty] [Algebra K K_infty] where
  toLinearMap : FullAdeleRing R K K_infty →ₗ[k] k
  vanishes_on_K : ∀ x : K, toLinearMap (fullDiagonalEmbedding R K K_infty x) = 0
```

**Deliverables**:
- [x] Define structure
- [ ] Prove AddCommGroup instance
- [ ] Prove Module K instance

#### Cycle 313: K-Module Structure
- Prove `WeilDifferential` is a K-vector space
- Scalar multiplication: `(c • ω)(a) = ω(c⁻¹ • a)`
- Basic lemmas

#### Cycle 314: Serre Pairing
**File**: `RrLean/RiemannRochV2/General/SerrePairing.lean`

```lean
/-- The Serre pairing is just evaluation -/
def serrePairing (D : DivisorV2 R) :
    RRSpace_proj k R K D →ₗ[k] WeilDifferential k R K K_infty →ₗ[k] k :=
  fun f => fun ω => ω.toLinearMap (embed_to_adele f)
```

This is straightforward once WeilDifferential exists.

#### Cycle 315-320: Non-Degeneracy (THE CRUX)

Need to prove:
```lean
theorem serrePairing_nondegenerate :
    ∀ f ∈ L(D), f ≠ 0 → ∃ ω ∈ Ω(K-D), serrePairing D f ω ≠ 0
```

**Strategy options**:
1. **From compactness**: A_K/K is compact → quotient is finite-dim → pairing is perfect
2. **Local-to-global**: Non-degenerate at each place → global non-degeneracy
3. **Axiomatize**: If proofs are too hard, acceptable to axiomatize

We have compactness infrastructure in `AdelicTopology.lean`, so option 1 is viable.

#### Cycle 321-325: Canonical Class

```lean
/-- Canonical divisor as divisor of any nonzero differential -/
def canonicalDivisor (ω : WeilDifferential k R K K_infty) (hω : ω ≠ 0) : DivisorV2 R := ...

theorem deg_canonical : (canonicalDivisor ω hω).deg = 2 * genus - 2 := ...
```

#### Cycle 326-330: Assembly

Instantiate `FullRRData` with:
- `canonical := canonicalDivisor ω hω`
- `genus := g`
- `serre_duality_eq` from non-degeneracy

Then `riemann_roch_full` gives us RR!

---

## What We Keep (3,700 lines)

From INVENTORY_REPORT.md "Core Kernel":

| File | Lines | Status |
|------|-------|--------|
| Basic.lean | 100 | KEEP |
| Typeclasses.lean | 150 | KEEP |
| Infrastructure.lean | 300 | KEEP |
| Divisor.lean | 200 | KEEP |
| RRSpace.lean | 200 | KEEP |
| KernelProof.lean | 400 | KEEP |
| DimensionCounting.lean | 200 | KEEP |
| RiemannInequality.lean | 250 | KEEP (**PROVED**) |
| DedekindDVR.lean | 100 | KEEP (**PROVED**) |
| AdelicTopology.lean | 300 | KEEP |
| AdelicH1v2.lean | 550 | KEEP |
| Projective.lean | 350 | KEEP |
| ResidueFieldIso.lean | 250 | KEEP (**PROVED**) |
| DifferentIdealBridge.lean | 200 | KEEP |
| FullRRData.lean | 150 | KEEP |

**Total: ~3,700 lines curve-agnostic, mostly sorry-free**

---

## What We Archive (P¹-Specific)

| File | Reason |
|------|--------|
| RatFuncPairing.lean | Linear places only |
| DimensionScratch.lean | ℓ(D)=deg+1 is P¹-only |
| P1Instance.lean | P¹ validation |
| ProductFormula.lean | Naive formula is false |
| AdelicH1Full sorries | Strong approx edge cases |

These don't block general RR.

---

## Estimated Timeline

| Phase | Cycles | Confidence |
|-------|--------|------------|
| WeilDifferential basics | 3 | High |
| Pairing definition | 1 | High |
| Non-degeneracy | 5-10 | Medium |
| Canonical class | 3-5 | Medium |
| Assembly | 2-3 | High |
| **Total** | **~15-20** | **Medium-High** |

---

## Success Criteria

Sorry-free proof of:
```lean
theorem riemann_roch (D : DivisorV2 R) :
    ell_proj D - ell_proj (canonical - D) = D.deg + 1 - genus
```

With:
- `canonical` defined via WeilDifferential
- `genus` defined as dim(Ω) or from deg(K) = 2g-2
- Non-degeneracy proved (not axiomatized) if possible

---

*Updated Cycle 311 (corrected). ~15-20 cycles remaining.*
