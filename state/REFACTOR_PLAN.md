# Refactor Plan: P¹ → General Curves

**Status**: Phase 7 Active. **~8-10 cycles to completion.**
**Goal**: Sorry-free Riemann-Roch for smooth projective curves.

---

## Critical Insight (Cycle 323)

We have **3,700 lines of curve-agnostic infrastructure** + key bridges:

| Asset | Status |
|-------|--------|
| Riemann Inequality | ✅ **PROVED** |
| DVR for completions | ✅ **PROVED** |
| H¹(D) framework | ✅ DONE |
| Dimension machinery | ✅ PROVED |
| FullRRData axiom package | ✅ DONE |
| AdelicRRData → FullRRData bridge | ✅ **DONE** |
| Elliptic FullRRData instance | ✅ **DONE** (Cycle 323) |

**The key remaining work**: Prove the Euler characteristic formula χ(D) = deg(D) + 1 - g.

---

## Phase Summary

| Phase | Status | Achievement |
|-------|--------|-------------|
| 0-4 | ✅ Complete | P¹ infrastructure |
| 5 | ⏸️ Archived | P¹ edge cases (bypassed) |
| 6 | ✅ Complete | Elliptic (axiomatized) |
| 7 | ⏳ **Active** | Weil differentials → RR |

---

## Phase 7: Euler Characteristic (Revised Cycle 323)

### The Core Strategy

The key to Riemann-Roch is the **Euler characteristic formula**:
```
χ(D) = ℓ(D) - h¹(D) = deg(D) + 1 - g
```

We prove this via the **6-term exact sequence**:
```
0 → L(D) → L(D+v) → κ(v) → H¹(D) → H¹(D+v) → 0
```

### What We Already Have

| Component | Status | File |
|-----------|--------|------|
| L(D) → L(D+v) inclusion | ✅ PROVED | RRSpace.lean |
| L(D+v) → κ(v) evaluation | ✅ PROVED | KernelProof.lean |
| Exactness at L(D+v) | ✅ PROVED | KernelProof.lean |
| H¹(D) → H¹(D+v) surjection | ✅ PROVED | AdelicH1v2.lean |
| ℓ(D+v) ≤ ℓ(D) + 1 | ✅ PROVED | DimensionCounting.lean |
| h¹(D+v) ≤ h¹(D) | ✅ PROVED | AdelicH1v2.lean |
| AdelicRRData → FullRRData | ✅ DONE | AdelicH1v2.lean |
| Elliptic FullRRData | ✅ DONE | EllipticRRData.lean |

### Implementation Plan

#### Cycle 324: Connecting Homomorphism
**File**: `RrLean/RiemannRochV2/Adelic/EulerCharacteristic.lean`

```lean
/-- The connecting homomorphism δ: κ(v) → H¹(D).
Takes a residue class, lifts to an adele supported at v,
maps to the quotient A_K / (K + A_K(D)). -/
def connectingHom (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    residueFieldAtPrime R v →ₗ[k] SpaceModule k R K D := ...
```

**Construction**:
1. Take α ∈ κ(v) = R/v.asIdeal
2. Choose uniformizer π at v
3. Construct adele a with: a_v = π⁻¹ · (lift of α), a_w = 0 for w ≠ v
4. Map to H¹(D) = A_K / (K + A_K(D))

#### Cycle 325-326: Exactness Proofs

Need to verify:
1. **At κ(v)**: image(eval) = ker(δ)
2. **At H¹(D)**: image(δ) = ker(H¹(D) → H¹(D+v))

These follow from adelic manipulations.

#### Cycle 327: Dimension Formula

Using Rank-Nullity on the exact sequence:
```lean
theorem chi_additive (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    (ell_proj k R K (D + single v 1) : ℤ) - h1_finrank k R K (D + single v 1)
    = (ell_proj k R K D : ℤ) - h1_finrank k R K D + 1
```

This says: χ(D+v) = χ(D) + 1

#### Cycle 328: Full Euler Characteristic

By induction from χ(0) = 1 - g:
```lean
theorem euler_characteristic (D : DivisorV2 R) :
    (ell_proj k R K D : ℤ) - h1_finrank k R K D = D.deg + 1 - genus
```

#### Cycle 329-330: Serre Duality + Assembly

With Euler characteristic proved, Serre duality h¹(D) = ℓ(K-D) gives:
```lean
theorem riemann_roch (D : DivisorV2 R) :
    (ell_proj k R K D : ℤ) - ell_proj k R K (canonical - D) = D.deg + 1 - genus
```

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
| Connecting homomorphism δ | 1 | High |
| Exactness proofs | 2 | Medium-High |
| Dimension formula (χ additive) | 1 | High |
| Full Euler characteristic | 1 | High |
| Serre duality + Assembly | 2-3 | Medium |
| **Total** | **~8-10** | **High** |

---

## Success Criteria

Sorry-free proof of:
```lean
theorem riemann_roch (D : DivisorV2 R) :
    (ell_proj k R K D : ℤ) - ell_proj k R K (canonical - D) = D.deg + 1 - genus
```

With:
- Euler characteristic χ(D) = deg(D) + 1 - g **proved** via exact sequence
- Serre duality h¹(D) = ℓ(K-D) from residue pairing
- No new axioms beyond existing AdelicRRData structure

---

*Updated Cycle 323. ~8-10 cycles remaining via Euler characteristic approach.*
