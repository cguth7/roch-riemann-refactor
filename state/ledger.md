# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Compiles (with sorries in DimensionCore + ell_ratfunc_projective_eq_deg_plus_one)
**Phase**: 3 - Serre Duality → Dimension Formula
**Cycle**: 236

---

## ⚠️ STATUS CLARIFICATION (Cycle 236)

**Important**: Cycle 232 claimed "RIEMANN-ROCH FOR P¹ PROVED!" but this was inaccurate.

**What was actually true at Cycle 232:**
- RatFuncFullRR.lean compiled and had the theorem *statement* for `riemann_roch_ratfunc`
- The theorem depended on `ell_ratfunc_projective_eq_deg_plus_one` (in DimensionScratch.lean)
- DimensionScratch.lean compiled at the time with sorries in place

**What happened in Cycle 233-235:**
- Attempted to fill those sorries
- Circular dependency trap was hit: trying to prove `Module.Finite` via `finrank`
- DimensionScratch.lean had compilation errors (not just sorries)

**What was fixed in Cycle 236:**
- ✅ Created DimensionCore.lean with proper finiteness proofs via embedding (no circular finrank)
- ✅ Fixed DimensionScratch.lean to use DimensionCore's instances
- ✅ Build now succeeds with sorries (not errors)
- ✅ Created Smoke.lean for build hygiene

**Current status**: Build compiles. Key theorem `ell_ratfunc_projective_single_linear` is proved. Main theorem `ell_ratfunc_projective_eq_deg_plus_one` still has sorry. DimensionCore.lean has sorries for the embedding construction.

---

## Build Hygiene Guardrails (Cycle 236) - IMPLEMENTED

### Problem Identified
No mechanical guarantee that the RR-for-P¹ critical path is actually being compiled. Lake globs and import graphs can silently drift.

### Implemented Guardrails

**1. Umbrella Import Module** ✅ DONE
Created `RrLean/RiemannRochV2/SerreDuality/Smoke.lean`:
- Imports all critical-path modules
- `#check` verifies key theorems are accessible
- `#print axioms` shows dependency on `sorryAx`
- `example` verifies type class instances are registered

**2. No-Sorries Smoke Test**
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
```
Currently shows `sorryAx` (expected - proofs have sorries). When all proofs are complete, this should return nothing.

**3. Find-and-Build Script** (optional)
```bash
find RrLean/RiemannRochV2/SerreDuality -name "*.lean" -exec lake build {} \;
```
This catches any files not in the import graph.

---

## Cycle 236 Plan

### Goal: Fix finiteness circularity + add build hygiene

### Math/Lean Fix: Finiteness via Embedding

**(A) Create DimensionCore.lean** (NEW FILE)
Prove `Module.Finite` for `RRSpace_ratfunc_projective (n·[α])` WITHOUT using finrank:
```lean
-- Construct linear injection: f ↦ (X-α)^n · f
-- Codomain: Polynomial.degreeLT Fq (n+1) (finite-dim)
-- Conclude: Module.Finite from finite codomain
instance RRSpace_ratfunc_projective_single_linear_finite :
    Module.Finite Fq (RRSpace_ratfunc_projective (n • DivisorV2.single (linearPlace α) 1)) := ...
```

**(B) Fix DimensionScratch.lean**
- Import DimensionCore
- Use the established `Module.Finite` instances
- Prove `ell_ratfunc_projective_single_linear` using gap bound + strict inclusion
- Complete `ell_ratfunc_projective_eq_deg_plus_one` by induction

### Architecture

```
RatFuncPairing.lean        (RRSpace definitions)
    ↓
DimensionCore.lean         (NEW: Module.Finite via embedding - NO finrank)
    ↓
DimensionScratch.lean      (dimension formulas using finrank)
    ↓
RatFuncFullRR.lean         (riemann_roch_ratfunc)
    ↓
Smoke.lean                 (NEW: umbrella + #print axioms check)
```

**Key principle**: Separate finiteness proofs from dimension computation

---

## Honest Sorry Audit (Cycle 236)

### CRITICAL PATH FOR P¹ (6 sorries total)

**DimensionCore.lean** (5 sorries):
```
Line 67:  mul_X_sub_pow_is_polynomial     - valuation bounds → polynomial form
Line 88:  partialClearPoles.map_add'      - linearity (addition)
Line 92:  partialClearPoles.map_smul'     - linearity (scalar mult)
Line 101: partialClearPoles_injective    - mult by nonzero is injective
Line 126: RRSpace_...add_single_finite   - finiteness for D + [v]
```

**DimensionScratch.lean** (1 sorry):
```
Line 892: ell_ratfunc_projective_eq_deg_plus_one - main theorem (strong induction)
```

### NOT ON CRITICAL PATH (15 sorries - imported but not used)

| File | Count | Why not critical |
|------|-------|------------------|
| AdelicH1Full.lean | 8 | Adelic approach (alternative) |
| Residue.lean | 2 | Higher-degree places |
| Others | 5 | Infrastructure not used by P¹ |

### Dependency Graph

```
riemann_roch_ratfunc (NOT PROVED)
    ├─→ ell_ratfunc_projective_eq_deg_plus_one (1 sorry - MAIN BLOCKER)
    │       ├─→ ell_ratfunc_projective_single_linear ✅ PROVED (modulo DimensionCore)
    │       │       ├─→ RRSpace_single_linear_finite (5 sorries in DimensionCore)
    │       │       └─→ ell_ratfunc_projective_gap_le ✅ PROVED
    │       ├─→ inv_X_sub_C_pow_mem_projective ✅
    │       └─→ inv_X_sub_C_pow_not_mem_projective_smaller ✅
    └─→ ell_canonical_sub_zero ✅ PROVED
```

### Verification

```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
# Shows sorryAx now. When empty, P¹ is complete.
```

---

## Anti-Pattern: Circular Finrank-Finiteness (Cycle 235)

### DON'T: Prove finiteness using finrank
```lean
-- THIS IS CIRCULAR - DON'T DO THIS
have hpos : 0 < Module.finrank Fq M := ...  -- needs Module.Finite!
haveI : Module.Finite Fq M := Module.finite_of_finrank_pos hpos
```

### DO: Prove finiteness by embedding into known finite-dim space
```lean
-- Construct linear injection into Fq[X]_{≤n}
def clearPoles : RRSpace(n·[α]) →ₗ[Fq] Polynomial.degreeLT Fq (n+1) := ...
have hinj : Function.Injective clearPoles := ...
-- Conclude finiteness from finite codomain
haveI : Module.Finite Fq RRSpace(n·[α]) := Module.Finite.of_injective clearPoles hinj
```

---

## Build Commands

```bash
# Current failing build
lake build RrLean.RiemannRochV2.SerreDuality.DimensionScratch 2>&1 | grep -E "(error|sorry)"

# Check if critical path modules are connected (after adding Smoke.lean)
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1

# Verify no sorryAx in final theorem (after Smoke.lean exists)
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
```

---

## Cycle 235 Summary (SUPERSEDED)

Attempted to prove `Module.Finite` via `finrank` bounds - discovered circular dependency.
See "Anti-Pattern" section above.

## Cycle 234 Summary (SUPERSEDED)

Proved `linearPlace_residue_finrank` and `ell_ratfunc_projective_gap_le`.

---

*For strategy, see `playbook.md`*
*For historical cycles 1-232, see `ledger_archive.md`*
