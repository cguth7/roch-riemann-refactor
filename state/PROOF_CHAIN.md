# Proof Chain: P¹ Riemann-Roch

Tracks the critical path from main theorems down to Mathlib. Updated Cycle 271.

---

## Main Theorem (Proved, Sorry-Free)

```lean
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective D = D.deg.toNat + 1
```

**Location**: `RrLean/RiemannRochV2/SerreDuality/P1Specific/DimensionScratch.lean`

---

## Axioms Used (Standard Mathlib Only)

```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "depends on axioms"
```
- `propext`, `Classical.choice`, `Quot.sound` - No `sorryAx`

---

## P¹ Proof Chain (Complete)

```
Smoke.lean                          # Build hygiene
  └── DimensionScratch.lean         # Main theorem: ℓ = deg + 1
        └── DimensionCore.lean      # Module.Finite for L(D)
              └── RatFuncPairing.lean  # H¹ = Subsingleton
                    ├── FullAdelesCompact.lean  # Strong approximation
                    └── ResidueTheory/          # Residue infrastructure
```

### Key Files (All Sorry-Free)

| Folder | Purpose |
|--------|---------|
| `P1Instance/` | P¹-specific proofs (canonical, L(K-D)=0, RR formula) |
| `SerreDuality/P1Specific/` | Dimension formulas, Serre pairing |
| `ResidueTheory/` | Residue at linear places, traced residue |
| `Core/` | Place, DivisorV3, RRSpaceV3 |

---

## General Curve Chain (Target)

For curves beyond P¹, must use Riemann Inequality + Serre Duality:

```
Abstract.lean                       # ProjectiveAdelicRRData class
  ├── AdelicH1Full.lean             # ExtendedDivisor, RRSpace_proj_ext
  └── [CurveInstance.lean]          # Instance for specific curve
```

### Key Types (Cycle 271 Discovery)

| Type | Uses | Dimension at D=0 |
|------|------|------------------|
| `RRSpace_proj` | Affine (HeightOneSpectrum) | ∞ for P¹ |
| `RRSpace_proj_ext` | Projective (ExtendedDivisor) | 1 for P¹ ✓ |

**Rule**: For projective curves, use `ProjectiveAdelicRRData` not `AdelicRRData`.

---

## Files NOT in P¹ Chain

| File | Status | Purpose |
|------|--------|---------|
| `Abstract.lean` | 0 sorries (template only) | `ProjectiveAdelicRRData` class |
| `AdelicH1Full.lean` | 0 sorries | Full adele H¹, `ExtendedDivisor` |
| `RiemannInequality.lean` | 0 sorries | General ℓ(D) ≥ deg + 1 - g |

---

## Verification

```bash
# Check for sorryAx
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
# No output = complete

# Full build
lake build RrLean.RiemannRochV2.SerreDuality.Smoke
```

---

*Updated Cycle 271: Added ProjectiveAdelicRRData, simplified chain documentation.*
