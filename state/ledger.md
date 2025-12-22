# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Compiles (with sorries in DimensionCore + ell_ratfunc_projective_eq_deg_plus_one)
**Phase**: 3 - Serre Duality → Dimension Formula
**Cycle**: 237

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

## Honest Sorry Audit (Cycle 237)

### CRITICAL PATH FOR P¹ (6 sorries total)

**DimensionCore.lean** (5 sorries):
```
Line 54:  denom_is_power_of_X_sub        - denom = (X-α)^m with m ≤ n (KEY LEMMA)
Line 119: partialClearPoles.map_add'      - linearity (addition)
Line 123: partialClearPoles.map_smul'     - linearity (scalar mult)
Line 135: partialClearPoles_injective    - mult by nonzero is injective
Line 155: RRSpace_...add_single_finite   - finiteness for D + [v]
```

Note: `mul_X_sub_pow_is_polynomial` is now fully proved modulo `denom_is_power_of_X_sub`.

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

## Cycle 237 Summary

**Goal**: Fill DimensionCore sorries

**What happened**: Attempted to prove `denom_is_power_of_X_sub` with a ~150 line proof. Hit many API mismatches and wasted time debugging non-existent lemmas.

**Outcome**:
- Simplified `denom_is_power_of_X_sub` to a sorry with clear math sketch
- `mul_X_sub_pow_is_polynomial` proof structure is correct (modulo `denom_is_power_of_X_sub`)
- Build compiles with 5 sorries in DimensionCore

**Lesson learned**: Don't write 150 lines at once. Build incrementally, test each step.

---

## ⚠️ API Lessons (Cycle 237)

### APIs that DON'T EXIST (don't use these):
```lean
-- WRONG - these don't exist:
Irreducible.not_unit           -- use Irreducible.not_isUnit
Associated.normalize_eq        -- not a method
Polynomial.normalize_monic     -- not in this form
Associated.eq_of_monic_of_associated  -- doesn't exist
RatFunc.mk_eq_div              -- doesn't exist
Polynomial.rootMultiplicity_pow_self  -- may not exist
WithZero.inv_exp               -- may not exist
```

### APIs that DO work:
```lean
-- CORRECT patterns:
Irreducible.not_isUnit hπ_irr (isUnit_of_dvd_one hdvd_one)
Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd  -- factors p = (X-α)^m * R
intValuation_linearPlace_eq_exp_neg_rootMultiplicity       -- valuation ↔ rootMultiplicity
WfDvdMonoid.exists_irreducible_factor hR_not_unit hR_ne    -- get irreducible factor
Valuation.map_div, v.valuation_of_algebraMap              -- valuation computation
one_lt_inv_iff₀                                           -- for inverse comparisons
RatFunc.num_div_denom f                                   -- NOT mk_eq_div
Polynomial.isUnit_iff                                     -- returns ∃ c ≠ 0, p = C c
```

### Proof Strategy for `denom_is_power_of_X_sub`:
The math is clear:
1. Factor `denom = (X-α)^m * R` using `exists_eq_pow_rootMultiplicity_mul_and_not_dvd`
2. Show `R = 1` by contradiction: any irreducible factor π of R creates place v_π where val(f) > 1
3. Show `m ≤ n` from valuation bound at `linearPlace α`

The implementation is tricky due to:
- Constructing `HeightOneSpectrum` from an irreducible
- Showing π ≠ (X-α) when π | R and (X-α) ∤ R (associated elements and normalization)
- Computing valuations in RatFunc correctly

**Recommendation for next Claude**: Prove this in small pieces. First prove a helper that any irreducible factor of denom creates a pole. Then use that to show R = 1.

---

## Incremental Proof Strategy (Cycle 237)

**DO**:
- Write 10-20 lines, build, fix errors
- Use `sorry` to validate proof structure first
- Extract helper lemmas when a sub-proof is complex
- Check if APIs exist before using them (grep codebase)

**DON'T**:
- Write 100+ line proofs hoping they compile
- Assume lemma names from memory (they're often wrong)
- Try to prove everything at once when stuck on one piece

---

## Cycle 235 Summary (SUPERSEDED)

Attempted to prove `Module.Finite` via `finrank` bounds - discovered circular dependency.
See "Anti-Pattern" section above.

## Cycle 234 Summary (SUPERSEDED)

Proved `linearPlace_residue_finrank` and `ell_ratfunc_projective_gap_le`.

---

*For strategy, see `playbook.md`*
*For historical cycles 1-232, see `ledger_archive.md`*
