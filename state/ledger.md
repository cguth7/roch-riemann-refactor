# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ❌ Does not compile (errors in DimensionScratch.lean)
**Phase**: 3 - Serre Duality → Dimension Formula
**Cycle**: 235

---

## Cycle 235 Summary

**Goal**: Fix DimensionScratch.lean sorries
**Result**: BLOCKED by architectural issue - circular dependency

### The Problem

Attempted to prove `Module.Finite` for `RRSpace_ratfunc_projective (n·[v])` using `finrank` bounds,
but `finrank` only behaves well when `Module.Finite` is already in scope. This is circular:

```
Need Module.Finite → to use Module.finrank_pos_iff → to get positive finrank → to prove Module.Finite
```

### What Doesn't Work

1. **Using `Module.finrank_pos_iff`** - requires `[Module.Finite]` instance
2. **Using gap bound for finiteness** - `ell_ratfunc_projective_gap_le` requires `[Module.Finite]` for the larger space
3. **`linarith`/`omega` on finrank** - doesn't work without proper coercion/instance setup
4. **`interval_cases` on `Module.finrank`** - finrank isn't computable without finite-dim

### Correct Decomposition (for next session)

**(A) Prove `Module.Finite` WITHOUT using finrank:**
- Construct explicit linear map `φ : RRSpace(n·[α]) →ₗ[Fq] (Fq[X]_{≤n})`
  - Send `f ↦ (X-α)^n · f` (clears poles, produces polynomial of degree ≤ n)
- Prove `Injective φ`
- Conclude `FiniteDimensional` because codomain is finite-dimensional
- **No finrank needed at this stage**

**(B) Prove dimension = n+1 AFTER finiteness:**
- `≥ n+1`: Exhibit n+1 linearly independent elements `{1, (X-α)⁻¹, ..., (X-α)⁻ⁿ}`
- `≤ n+1`: Use gap bound / injection into polynomials of degree ≤ n

### Files Modified This Cycle

- `DimensionScratch.lean` - Multiple failed attempts, left in broken state

### Recommended Architecture Refactor

```
RatFuncPairing.lean        (foundational: RRSpace definitions)
    ↓
DimensionCore.lean         (NEW: Module.Finite proofs, no finrank)
    ↓
DimensionScratch.lean      (dimension formulas using finrank)
    ↓
SerreDuality.lean          (top-level Riemann-Roch)
```

Key principle: **Separate finiteness proofs from dimension computation**

---

## Dependency Graph (Updated)

```
riemann_roch_ratfunc (NOT PROVED)
    ├─→ ell_ratfunc_projective_eq_deg_plus_one (sorry)
    │       ├─→ ell_ratfunc_projective_single_linear (BLOCKED - needs finiteness refactor)
    │       │       ├─→ RRSpace_single_linear_finite (NEEDED - construct directly)
    │       │       └─→ ell_ratfunc_projective_gap_le ✅ DONE (Cycle 234)
    │       │               └─→ linearPlace_residue_finrank ✅ DONE (Cycle 234)
    │       ├─→ inv_X_sub_C_pow_mem_projective_general ✅
    │       └─→ inv_X_sub_C_pow_not_mem_projective_general ✅
    └─→ ell_canonical_sub_zero ✅ DONE (Cycle 224)
```

---

## Key Anti-Pattern Discovered (Cycle 235)

### DON'T: Prove finiteness using finrank
```lean
-- THIS IS CIRCULAR - DON'T DO THIS
have hpos : 0 < Module.finrank Fq M := ...  -- needs Module.Finite!
haveI : Module.Finite Fq M := Module.finite_of_finrank_pos hpos
```

### DO: Prove finiteness by embedding into known finite-dim space
```lean
-- Construct linear injection into Fq[X]_{≤n}
def φ : RRSpace(n·[α]) →ₗ[Fq] Polynomial.degreeLT Fq (n+1) := ...
have hinj : Function.Injective φ := ...
-- Conclude finiteness from finite codomain
haveI : Module.Finite Fq RRSpace(n·[α]) := Module.Finite.of_injective φ hinj
```

---

## Files Modified This Cycle

- `DimensionScratch.lean` - Left in broken state, needs refactor

---

## Build Command

```bash
lake build RrLean.RiemannRochV2.SerreDuality.DimensionScratch 2>&1 | grep -E "(error|sorry)"
```

---

## Next Session Action Items

1. **Revert DimensionScratch.lean** to last working state (before this cycle)
2. **Create DimensionCore.lean** with:
   - `instance RRSpace_ratfunc_projective_single_linear_finite` via embedding approach
   - NO finrank, NO ell_ratfunc_projective
3. **Then in DimensionScratch.lean**:
   - Import DimensionCore
   - Prove `ell_ratfunc_projective_single_linear` using existing gap bound + strict inclusion
   - Prove `ell_ratfunc_projective_eq_deg_plus_one` by induction

---

## Cycle 234 (SUPERSEDED)

Proved `linearPlace_residue_finrank` and `ell_ratfunc_projective_gap_le`.
See Cycle 235 for current blocker.

---

*For strategy, see `playbook.md`*
*For historical cycles 1-232, see `ledger_archive.md`*
