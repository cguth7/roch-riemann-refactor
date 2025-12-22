# Proof Chain: P¹ Riemann-Roch

Tracks the critical path from main theorems down to Mathlib. Updated Cycle 247.

---

## Main Theorem

```lean
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective D = D.deg.toNat + 1
```

**Location**: `RrLean/RiemannRochV2/SerreDuality/P1Specific/DimensionScratch.lean`

**Meaning**: For effective divisors D on P¹ with linear place support, dim L(D) = deg(D) + 1.

---

## Axioms Used

```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "depends on axioms"
```

**Result** (Cycle 247):
- `propext` - Propositional extensionality
- `Classical.choice` - Classical logic
- `Quot.sound` - Quotient soundness

These are **standard Mathlib axioms**. No `sorryAx`.

---

## Full Import Chain

```
Smoke.lean                                    # Build hygiene test
  │
  ├── DimensionScratch.lean                   # Main theorem: ell = deg + 1
  │     ├── DimensionCore.lean                # Finiteness: Module.Finite for L(D)
  │     └── RatFuncFullRR.lean                # Full RR statement
  │           └── FullRRData.lean             # RR data structure
  │                 └── Projective.lean       # Projective L(D) definition
  │                       └── KernelProof.lean    # Kernel dimension lemmas
  │
  ├── RatFuncPairing.lean                     # Serre pairing construction
  │     ├── AdelicH1v2.lean                   # H¹(D) via finite adeles
  │     │     └── Adeles.lean                 # Adele ring basics
  │     │           └── Core/RRSpace.lean     # L(D) as submodule
  │     │
  │     ├── FullAdelesCompact.lean            # Compactness, weak approximation
  │     │     └── FullAdelesBase.lean         # Full adele ring definition
  │     │           └── AdelicTopology.lean   # Topology on adeles
  │     │
  │     ├── RatFuncResidues.lean              # Residue at linear places
  │     │     └── Residue.lean                # General residue theory
  │     │
  │     └── ProductFormula.lean               # Product formula
  │
  └── DimensionCore.lean                      # (also imported directly)
        └── RatFuncPairing.lean               # (see above)
```

### Core Infrastructure (transitively included)

```
Core/
  ├── Basic.lean          # Shared imports
  ├── Divisor.lean        # DivisorV2, deg, Effective
  ├── RRSpace.lean        # L(D) as Fq-submodule
  └── Typeclasses.lean    # LocalGapBound, SinglePointBound

Definitions/
  ├── Infrastructure.lean # Residue field, uniformizer
  ├── RRDefinitions.lean  # DVR-valuation bridge
  ├── Projective.lean     # Projective L(D)
  └── FullRRData.lean     # Full RR data structure

Adelic/
  ├── Adeles.lean         # Basic adele definitions
  ├── AdelicH1v2.lean     # H¹(D) quotient module
  ├── AdelicTopology.lean # Topology on adeles
  ├── FullAdelesBase.lean # Full adele ring
  └── FullAdelesCompact.lean # Compactness proofs
```

---

## NOT in Main Chain

These files exist but are NOT imported by Smoke.lean:

| File | Purpose | Why not in chain |
|------|---------|------------------|
| `Dimension/RiemannInequality.lean` | ℓ(D) ≥ deg(D) + 1 - g | Separate theorem, P¹ uses direct approach |
| `Dimension/DimensionCounting.lean` | General dimension counting | Not needed for P¹ |
| `SerreDuality/General/Abstract.lean` | Curve-agnostic Serre duality | Has 3 sorries, not wired in yet |
| `SerreDuality/General/AdelicH1Full.lean` | Full adele H¹ | Alternative approach, now sorry-free |

---

## Verification Commands

### Check for sorryAx
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
# No output = proof complete
```

### Check axioms used
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "depends on axioms"
# Should show only: propext, Classical.choice, Quot.sound
```

### Full build
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke
```

---

## File Status Summary

### On Main Chain (connected to Smoke.lean) - All Sorry-Free

| Folder | Files | Status |
|--------|-------|--------|
| SerreDuality/P1Specific/ | DimensionScratch, DimensionCore, RatFuncPairing, RatFuncFullRR | ✅ |
| SerreDuality/ | RatFuncResidues, Smoke | ✅ |
| Core/ | Basic, Divisor, RRSpace, Typeclasses | ✅ |
| Definitions/ | Infrastructure, RRDefinitions, Projective, FullRRData | ✅ |
| Adelic/ | Adeles, AdelicH1v2, AdelicTopology, FullAdelesBase, FullAdelesCompact | ✅ |
| Dimension/ | KernelProof | ✅ |
| ResidueTheory/ | Residue | ✅ |
| P1Instance/ | ProductFormula, FqPolynomialInstance | ✅ |

### Not on Main Chain

| File | Sorries | Connection Plan |
|------|---------|-----------------|
| Dimension/RiemannInequality.lean | 0 | Standalone theorem (Phase 1 milestone) |
| Dimension/DimensionCounting.lean | 0 | General infrastructure |
| SerreDuality/General/Abstract.lean | 3 | Wire into curve-agnostic framework |
| SerreDuality/General/AdelicH1Full.lean | 0 | Alternative H¹ approach |

---

## Adding New Files

**IMPORTANT**: When adding a new file to the repo:

1. **If it's on the critical path**: Import it in Smoke.lean (directly or transitively)
2. **If it's infrastructure**: Document in "Not on Main Chain" table above with:
   - What it does
   - Where you plan to connect it
   - Current sorry count

3. **After connecting**: Run verification commands above to confirm no sorryAx introduced

**Why this matters**: Cycle 236-240 taught us that files can appear "done" while containing sorries that don't show up in builds. The Smoke.lean test catches this by forcing `#check` on critical theorems and printing their axioms.

---

## Future Chain: General Curves

The P¹ proof uses a "brute force" approach - explicit construction of 1/(x-α)^n functions
and strong induction on degree. This **bypasses** the Riemann Inequality + Serre Duality strategy.

For **general curves** (elliptic, hyperelliptic, etc.), we cannot do brute force because we
don't have explicit function formulas. We must use the standard approach:

```
General Curve Proof Chain (Target)
==================================

Smoke.lean (or new GeneralSmoke.lean)
  │
  ├── Abstract.lean                      # Curve-agnostic Serre duality (3 sorries to fill)
  │     ├── AdelicH1Full.lean            # H¹(D) via full adeles (now sorry-free!)
  │     └── [New: SerrePairing.lean]     # Residue pairing construction
  │
  ├── RiemannInequality.lean             # ℓ(D) ≥ deg(D) + 1 - g  ← NOT USED BY P¹
  │     └── DimensionCounting.lean       # General dimension machinery
  │           └── KernelProof.lean       # Kernel dimension lemmas
  │
  └── [New: CurveInstance.lean]          # Instance for specific curve
        └── FullRRData.lean              # RR data structure

The Logic:
1. Riemann Inequality:  ℓ(D) ≥ deg(D) + 1 - g
2. Serre Duality:       h¹(D) = ℓ(K - D)
3. Combine:             ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

### Why P¹ Didn't Need This

| Component | P¹ Approach | General Approach |
|-----------|-------------|------------------|
| Dimension formula | Direct induction on deg(D) | Riemann Inequality + Duality |
| Function construction | Explicit 1/(x-α)^n | Abstract existence via Serre |
| Finiteness | Embedding into polynomial space | Compactness of adeles |
| h¹ computation | Not needed (g=0, so h¹=0 for deg≥-1) | Full Serre duality pairing |

### Files to Connect for General Curves

| File | Current Status | Action Needed |
|------|---------------|---------------|
| `RiemannInequality.lean` | Sorry-free, disconnected | Import into general chain |
| `DimensionCounting.lean` | Sorry-free, disconnected | Import via RiemannInequality |
| `Abstract.lean` | 3 sorries | Fill h1_finite, ell_finite, h1_vanishing |
| `AdelicH1Full.lean` | Sorry-free | Wire into Abstract.lean |

---

## History

| Cycle | Change |
|-------|--------|
| 236 | Created Smoke.lean for build hygiene |
| 237-240 | Filled DimensionCore sorries |
| 247 | Filled AdelicH1Full sorries, created this doc, mapped full chain |
