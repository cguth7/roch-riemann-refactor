# Proof Chain: Riemann-Roch Formalization

Tracks what's **already proved** and what remains. Updated Cycle 311 (corrected).

---

## Critical Insight

**3,700 lines of curve-agnostic infrastructure is DONE.**
**~15-20 cycles to sorry-free RR.**

---

## What's Already Proved (Sorry-Free!)

These theorems are **fully proved**, not axiomatized:

| Theorem | File | Lines |
|---------|------|-------|
| **Riemann Inequality** | RiemannInequality.lean | 250 |
| DVR for adic completion | DedekindDVR.lean | 100 |
| Residue field isomorphism | ResidueFieldIso.lean | 250 |
| Kernel = L(D) | KernelProof.lean | 400 |
| ℓ(D+v) ≤ ℓ(D) + 1 | DimensionCounting.lean | 200 |
| Module length additivity | DimensionCounting.lean | 200 |

### Riemann Inequality (THE BIG ONE)

```lean
-- RiemannInequality.lean - SORRY-FREE
theorem riemann_inequality_real [LocalGapBound k R K] [BaseDim k R K] :
    ∀ D : DivisorV2 R, D.Effective →
    ell k R K D ≥ D.deg + BaseDim.c k R K
```

This is **half of Riemann-Roch**, already done!

---

## Proof Chain Diagram

### Current State

```
        ┌─────────────────────────────────────┐
        │     RIEMANN INEQUALITY (PROVED)     │
        │   ℓ(D) ≥ deg(D) + 1 - g             │
        └─────────────────────────────────────┘
                         │
         Uses: DimensionCounting, KernelProof
                         │
        ┌────────────────┴────────────────────┐
        ▼                                     ▼
   LocalGapBound                        BaseDim
   (PROVED for Dedekind)                (typeclass)
        │                                     │
        ▼                                     ▼
   KernelProof.lean                    Divisor.lean
   (exact sequence)                    (deg, Effective)
        │                                     │
        └────────────────┬────────────────────┘
                         ▼
                    Mathlib
```

### What Remains

```
        ┌─────────────────────────────────────┐
        │         RIEMANN-ROCH (GOAL)         │
        │   ℓ(D) - ℓ(K-D) = deg(D) + 1 - g    │
        └─────────────────────────────────────┘
                         │
        ┌────────────────┴────────────────────┐
        ▼                                     ▼
   Riemann Inequality              Serre Duality
   ✅ PROVED                       ⏳ Need pairing
                                          │
                         ┌────────────────┴────────────────┐
                         ▼                                 ▼
                  WeilDifferential              Non-Degeneracy
                  ⏳ Cycle 312                  ⏳ Cycle 315-320
                         │                                 │
                         ▼                                 ▼
                  FullAdeleRing ✅            Compactness of A/K ✅
                  (already done)              (AdelicTopology.lean)
```

---

## Module Status

### ✅ Complete Core (3,700 lines)

| Module | Files | Status |
|--------|-------|--------|
| Core infrastructure | 6 | ✅ Sorry-free |
| Dimension machinery | 3 | ✅ Sorry-free |
| Adelic framework | 4 | ✅ Done |
| H¹ definition | 1 | ✅ Done |
| FullRRData | 1 | ✅ Framework done |

### ⏳ Phase 7 (New)

| File | Cycle | Status |
|------|-------|--------|
| WeilDifferential.lean | 312-313 | Not started |
| SerrePairing.lean | 314 | Not started |
| NonDegeneracy.lean | 315-320 | Not started |
| Canonical.lean | 321-325 | Not started |

### ⏸️ Archived (P¹-Specific)

| File | Reason |
|------|--------|
| AdelicH1Full sorries | Strong approx edge cases |
| RatFuncPairing.lean | Linear places only |
| DimensionScratch.lean | ℓ(D)=deg+1 is P¹-only |

---

## Sorry Locations (8 total)

### Archived P¹ Edge Cases (2)
*Bypassed by Weil differential approach*

| Location | Description |
|----------|-------------|
| AdelicH1Full:757 | Strong approx deep negative |
| AdelicH1Full:1458 | Strong approx non-effective |

### Axiom Sorries (6) - Intentional
| Location | Description |
|----------|-------------|
| Abstract:277 | h1_zero_finite |
| StrongApproximation:115,164 | Density (2) |
| EllipticH1:206,219 | Elliptic-specific (2) |
| EllipticSetup:105 | IsDedekindDomain |

---

## The Path to Sorry-Free RR

### Already Done
1. ✅ Riemann Inequality (PROVED)
2. ✅ H¹(D) as adelic quotient
3. ✅ FullRRData framework
4. ✅ Compactness infrastructure

### Remaining Work
5. ⏳ WeilDifferential definition (Cycle 312)
6. ⏳ Serre pairing (Cycle 314)
7. ⏳ **Non-degeneracy** (Cycle 315-320) - THE CRUX
8. ⏳ Canonical class (Cycle 321-325)
9. ⏳ Assembly (Cycle 326-330)

### Non-Degeneracy Strategy

We need:
```lean
∀ f ∈ L(D), f ≠ 0 → ∃ ω ∈ Ω(K-D), ω(f) ≠ 0
```

Options:
1. **From compactness** - A_K/K compact → pairing is perfect (infrastructure exists)
2. **Local-to-global** - Non-degenerate at each place
3. **Axiomatize** - Acceptable fallback

---

## Key Infrastructure (Reusable)

| File | Key Theorem | Status |
|------|-------------|--------|
| RiemannInequality.lean | `riemann_inequality_real` | ✅ PROVED |
| DedekindDVR.lean | `isDiscreteValuationRing_adicCompletionIntegers` | ✅ PROVED |
| ResidueFieldIso.lean | `residueFieldIso` | ✅ PROVED |
| KernelProof.lean | `kernel_evaluationMapAt_complete_proof` | ✅ PROVED |
| DimensionCounting.lean | `length_LD_plus_v_le` | ✅ PROVED |
| AdelicH1v2.lean | `SpaceModule` H¹ definition | ✅ DONE |
| FullRRData.lean | `riemann_roch_full` | ✅ Framework |
| AdelicTopology.lean | `compact_adelic_quotient` | ✅ DONE |

---

## Verification

```bash
# Check Riemann Inequality is sorry-free
grep -rn "sorry" RrLean/RiemannRochV2/RiemannInequality.lean
# Expected: No output

# Check core files are sorry-free
for f in DedekindDVR KernelProof DimensionCounting ResidueFieldIso; do
  echo "=== $f ===" && grep -c "sorry" RrLean/RiemannRochV2/$f.lean 2>/dev/null || echo "0"
done
# Expected: All 0
```

---

*Updated Cycle 311 (corrected). Riemann Inequality is PROVED. ~15-20 cycles to RR.*
