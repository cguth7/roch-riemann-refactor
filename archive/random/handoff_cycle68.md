# Handoff: Cycle 68 Refactoring In Progress

## Context
Cycle 68 completed successfully (5/8 candidates PROVED). Started refactoring to move proven lemmas but ran into build issues.

## Current Problem
**LocalGapInstance.lean is too large** (~3750 lines) - builds are taking 5+ minutes, making iteration painful.

## What Was Done
1. Added `withzero_lt_exp_succ_imp_le_exp` to Infrastructure.lean (line ~393)
2. Removed duplicate from LocalGapInstance.lean (replaced with comment at line 3566)
3. Added `classical` to `valuation_bound_at_other_prime_proof` (line 3646)

## Current State
- Infrastructure.lean builds successfully
- LocalGapInstance.lean build started but taking too long
- There may be cascading errors due to the refactoring

## What Needs To Be Done

### Option A: Revert and Split Differently
```bash
git checkout HEAD -- RrLean/RiemannRochV2/LocalGapInstance.lean
git checkout HEAD -- RrLean/RiemannRochV2/Infrastructure.lean
```
Then create a new file (e.g., `KernelHelpers.lean`) to hold Cycles 66-68 candidates.

### Option B: Fix Current Refactoring
The errors were:
1. `Valuation.ne_zero_iff.mpr` not found (line 3584)
2. `ring` failing on WithZero types (lines 3594, 3596, 3599)
3. `omega` failing (line 3632)

These suggest the lemma `withzero_lt_exp_succ_imp_le_exp` in Infrastructure has a different signature or isn't being imported correctly.

## Recommended Approach for Next Session

**Split LocalGapInstance.lean into smaller files:**

1. **Keep in LocalGapInstance.lean** (~lines 1-2000):
   - Core definitions: `valuationRingAt`, `uniformizerAt`, `shiftedElement`
   - Evaluation map infrastructure: `evaluationMapAt_complete`
   - Residue field bridges

2. **New file: KernelProof.lean** (~lines 2000-3750):
   - Cycle 66-68 candidates
   - Kernel characterization lemmas
   - `withzero_lt_exp_succ_imp_le_exp` and extraction lemmas

3. **Infrastructure.lean**:
   - Keep pure, reusable lemmas only
   - The WithZero discrete step-down can stay here

## Victory Path Status
```
extract_valuation_bound (PROVED in Cycle 68) ✅
    ↓
LD_element_maps_to_zero (SORRY - 3 sub-lemmas needed)
    ↓
kernel_evaluationMapAt_complete (SORRY)
    ↓
LocalGapBound instance → VICTORY
```

## Files Modified (uncommitted)
- `RrLean/RiemannRochV2/Infrastructure.lean` - added WithZero lemma
- `RrLean/RiemannRochV2/LocalGapInstance.lean` - removed duplicate, added classical

## Key Insight
The build time problem is the real blocker now. Splitting the file is necessary before continuing with Cycle 69.
