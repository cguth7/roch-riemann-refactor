# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Compiles (with 2 sorries in DimensionCore + 1 in DimensionScratch)
**Phase**: 3 - Serre Duality → Dimension Formula
**Cycle**: 238

---

## Cycle 238 Summary - MAJOR PROGRESS

**Goal**: Fill "low-hanging fruit" sorries (linearity + injectivity)

**What was accomplished**:
- ✅ `partialClearPoles.map_add'` - PROVED
- ✅ `partialClearPoles.map_smul'` - PROVED
- ✅ `partialClearPoles_injective` - PROVED

**Sorries reduced**: 5 → 2 in DimensionCore.lean

**Key insight**: Refactored using "Extract and Conquer" pattern (see below).

---

## ✅ PATTERN: Extract and Conquer (Cycle 238)

When defining a `LinearMap` with non-trivial properties, DON'T try to prove everything inside the `where` block. This creates "context soup" that confuses Lean's `rw` tactic ("motive is not type correct" errors).

### The Mathlib Way (3 steps):

**Step 1: Define the raw function**
```lean
def partialClearPolesFun (α : Fq) (n : ℕ) (f : RRSpace...) : Polynomial.degreeLT Fq (n+1) := by
  have hpoly := mul_X_sub_pow_is_polynomial ...
  exact ⟨hpoly.choose, ...⟩
```

**Step 2: Prove the specification lemma**
```lean
lemma partialClearPolesFun_spec ... :
    algebraMap _ _ (partialClearPolesFun ...).val = (X-α)^n * f.val := by
  -- Full algebraic proof here
```

**Step 3: Bundle as LinearMap**
```lean
def partialClearPoles ... : ... →ₗ[Fq] ... where
  toFun := partialClearPolesFun α n
  map_add' := by ... rw [partialClearPolesFun_spec, ...]; ring  -- ONE-LINER!
  map_smul' := by ... rw [partialClearPolesFun_spec, ...]; ring  -- ONE-LINER!
```

This eliminates circular dependencies and makes linearity proofs trivial.

---

## Honest Sorry Audit (Cycle 238)

### CRITICAL PATH FOR P¹ (3 sorries total - down from 6!)

**DimensionCore.lean** (2 sorries):
```
Line 61:  denom_is_power_of_X_sub           - KEY LEMMA: denom = (X-α)^m with m ≤ n
Line 225: RRSpace_...add_single_finite      - finiteness for D + [v]
```

**DimensionScratch.lean** (1 sorry):
```
Line 892: ell_ratfunc_projective_eq_deg_plus_one - main theorem (strong induction)
```

### What's NOW PROVED (Cycle 238):
- ✅ `partialClearPolesFun_spec` - the key algebraic equation
- ✅ `partialClearPoles` (full LinearMap) - linearity via spec
- ✅ `partialClearPoles_injective` - injectivity via spec
- ✅ `RRSpace_ratfunc_projective_single_linear_finite` - finiteness (uses injective embedding)

### Dependency Graph (updated)

```
riemann_roch_ratfunc (NOT PROVED)
    ├─→ ell_ratfunc_projective_eq_deg_plus_one (1 sorry - MAIN BLOCKER)
    │       ├─→ ell_ratfunc_projective_single_linear ✅ PROVED (modulo DimensionCore)
    │       │       ├─→ RRSpace_single_linear_finite ✅ (needs denom_is_power_of_X_sub)
    │       │       │       ├─→ partialClearPoles ✅ PROVED (LinearMap)
    │       │       │       └─→ partialClearPoles_injective ✅ PROVED
    │       │       └─→ ell_ratfunc_projective_gap_le ✅ PROVED
    │       ├─→ inv_X_sub_C_pow_mem_projective ✅
    │       └─→ inv_X_sub_C_pow_not_mem_projective_smaller ✅
    └─→ ell_canonical_sub_zero ✅ PROVED
```

---

## Next Steps for Future Claude (Cycle 239)

### Priority 1: `denom_is_power_of_X_sub` (Line 61)

**What to prove**:
```lean
lemma denom_is_power_of_X_sub (α : Fq) (n : ℕ) (f : RatFunc Fq) (hf_ne : f ≠ 0)
    (hf : f ∈ RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) :
    ∃ m : ℕ, m ≤ n ∧ f.denom = (Polynomial.X - Polynomial.C α) ^ m
```

**Math strategy**:
1. Factor `denom = (X-α)^m * R` using `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`
2. Show `R = 1` by contradiction:
   - If R has irreducible factor π ≠ (X-α), then π defines a place v_π
   - At v_π: f has a pole (val < 0) but RRSpace membership says val ≥ 0 at all places ≠ α
   - Contradiction!
3. Show `m ≤ n` from valuation bound at `linearPlace α`

**Implementation tips**:
- Use `HeightOneSpectrum.mk` to construct place from irreducible
- Key lemma: `intValuation_linearPlace_eq_exp_neg_rootMultiplicity`
- Build in small pieces (10-20 lines), test each step
- See "API Lessons" section below for correct lemma names

### Priority 2: `RRSpace_ratfunc_projective_add_single_finite` (Line 225) - LIKELY EASY

**What to prove**: Finiteness for `D + [v]` given finiteness for `D`.

**Key insight** (thanks Gemini): This should be simpler than it looks!
- We're given `[hD : Module.Finite Fq (RRSpace_ratfunc_projective D)]`
- `L(D) ⊆ L(D+[α])` as submodules
- Gap bound: `dim L(D+[α]) ≤ dim L(D) + 1`

**Approach**: Finite submodule + finite quotient → finite module. Look for:
```lean
-- Something like:
Module.Finite.of_quotient_finite  -- if quotient is finite-dim
-- Or use the fact that L(D+[α])/L(D) has dim ≤ 1
```

**Note**: `RRSpace_ratfunc_projective_single_linear_finite` (n•[α] case) is ALREADY PROVED using the one-liner:
```lean
exact Module.Finite.of_injective (partialClearPoles Fq α n) (partialClearPoles_injective Fq α n)
```
The `add_single_finite` case just needs the "finite extension" version of this argument.

### Priority 3: `ell_ratfunc_projective_eq_deg_plus_one` (DimensionScratch.lean)

Strong induction on `deg(D)`. Once DimensionCore sorries are filled, this may "just work" or need minor fixes.

---

## API Lessons (Cycle 237-238)

### APIs that DON'T EXIST (don't use these):
```lean
Irreducible.not_unit           -- use Irreducible.not_isUnit
Associated.normalize_eq        -- not a method
RatFunc.mk_eq_div              -- doesn't exist
```

### APIs that DO work:
```lean
IsFractionRing.injective (Polynomial Fq) (RatFunc Fq)  -- algebraMap injective
RatFunc.num_div_denom f                                -- f = num/denom in RatFunc
Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd  -- factor out (X-α)^m
intValuation_linearPlace_eq_exp_neg_rootMultiplicity   -- valuation ↔ rootMultiplicity
IsScalarTower.algebraMap_apply                         -- normalize algebraMap paths
```

### Useful patterns from this session:
```lean
-- Prove polynomial equality via algebraMap injectivity
apply IsFractionRing.injective (Polynomial Fq) (RatFunc Fq)

-- Lift polynomial equation to RatFunc
have hspec_lifted := congrArg (algebraMap (Polynomial Fq) (RatFunc Fq)) hspec

-- Normalize algebraMap paths
simp only [← IsScalarTower.algebraMap_apply Fq (Polynomial Fq) (RatFunc Fq)]
```

---

## Build Commands

```bash
# Build DimensionCore and check sorries
lake build RrLean.RiemannRochV2.SerreDuality.DimensionCore 2>&1 | grep -E "(error|sorry)"

# Full smoke test
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"

# Count sorries in DimensionCore
grep -n "sorry" RrLean/RiemannRochV2/SerreDuality/DimensionCore.lean | grep -v "^[0-9]*:.*--"
```

---

## Historical Notes

### Cycle 237
- Attempted `denom_is_power_of_X_sub` with 150-line proof, hit API mismatches
- Lesson: Build incrementally, 10-20 lines at a time

### Cycle 236
- Created DimensionCore.lean architecture
- Fixed circular finrank-finiteness anti-pattern
- Added Smoke.lean for build hygiene

### Cycles 233-235
- Circular dependency trap (finrank needs Module.Finite needs finrank)
- See "Anti-Pattern" section in playbook.md

---

*For strategy, see `playbook.md`*
*For historical cycles 1-232, see `ledger_archive.md`*
