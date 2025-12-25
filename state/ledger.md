# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ PASSING (with 1 sorry in AdelicH1Full.lean, edge case sorries in Abstract.lean)
**Cycle**: 281 (Complete)

---

## Cycle 281 Summary: The Great Wiring

**Goal**: Connect the new `ResidueTrace` engine to the rest of the codebase.

**What was done**:

1. **Fixed Abstract.lean build errors** from Cycle 280 API changes:
   - `SpaceModule_full_finite_of_deg_ge_neg_one` and `h1_finrank_full_eq_zero_of_deg_ge_neg_one` now require `heff : D.finite.Effective` and `h_infty : D.inftyCoeff ≥ -1`
   - Updated `p1ProjectiveAdelicRRData` instance with proper case handling
   - Added explicit sorries for edge cases (non-effective D, D.inftyCoeff < -1)

2. **Verified ResidueTrace wiring**:
   - `ResidueTrace.lean` is fully sorry-free
   - Key theorem `tracedResidueAtPlace_eq_residueAt_linear` bridges traced residue to legacy `residueAt`
   - Global residue theorem `residue_sum_traced_eq_zero_P1` connects to `residueSumTotal_splits`

3. **Confirmed sorry-free components**:
   - `P1Instance/` - 0 sorries (fully proved)
   - `ResidueTheory/` - 0 sorries (fully proved)

**Architecture insight**: The traced residue framework is ready for higher-genus curves:
- `localResidueAtPlace` works for arbitrary places (any degree)
- `tracedResidueAtPlace` applies Tr_{κ(v)/k} to get base field values
- For P¹, all places are linear so trace = identity

---

## Cycle 280 Summary (Archive)

**Problem**: The sorry at line ~680 required proving `|k₂|_∞ ≤ exp(D.inftyCoeff)`.

**Root Cause**: The original theorem only had `hdeg : D.deg ≥ -1`, which was insufficient.

**Solution**: Added two hypotheses to `globalPlusBoundedSubmodule_full_eq_top_of_deg_ge_neg_one`:
1. `(heff : D.finite.Effective)` - ensures k₂ is just principal parts (no polynomial term)
2. `(h_infty : D.inftyCoeff ≥ -1)` - ensures exp(-1) ≤ exp(D.inftyCoeff)

---

## What's Proved

```lean
theorem serre_duality_p1 (D : ExtendedDivisor (Polynomial Fq))
    (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    h1_finrank_full Fq D = ell_proj_ext Fq (canonicalExtended Fq - D)
```

---

## Next Steps: Cycle 282

Options:
1. **Fill edge case sorries in Abstract.lean** - prove H¹ finiteness for non-effective or deeply negative D
2. **Prove the accepted sorry** - tackle the `inftyValuationDef k₂ ≤ exp(-1)` technical debt
3. **Begin elliptic curve infrastructure** - extend Place type to support higher genus curves

---

## Sorries

| Location | Count | Status |
|----------|-------|--------|
| AdelicH1Full.lean | 1 | Line 698: `inftyValuationDef k₂ ≤ exp(-1)` - ACCEPTED DEBT |
| Abstract.lean | 11 | Edge cases in p1ProjectiveAdelicRRData + abstract template |

**Abstract.lean sorries breakdown**:
- Lines 200-203: Template code (not instantiated) - 3 sorries
- Lines 289-294: `h1_finite` edge cases - 3 sorries
- Lines 302-303: `h1_vanishing` edge cases - 2 sorries
- Lines 322-326: `serre_duality` edge cases - 3 sorries

**Edge cases are**:
1. D.finite not effective (non-effective finite part)
2. D.inftyCoeff < -1 (deeply negative at infinity)

These are mathematically less common for P¹ applications. The main case (effective D with inftyCoeff ≥ 0) is fully proved via `serre_duality_p1`.

---

## Technical Debt Notes (MUST FIX LATER)

**AdelicH1Full.lean:698** - Principal parts infinity bound
- **What to prove**: `FunctionField.inftyValuationDef Fq k₂ ≤ WithZero.exp (-1)`
- **Mathematical fact**: Principal parts at finite places are proper fractions, so `intDegree ≤ -1`
- **Why sorried**: Type class synthesis for `DecidableEq (RatFunc Fq)` with `inftyValuationDef` - rabbit hole
- **How to fix later**:
  1. Add `[DecidableEq Fq]` to the right section/variable context
  2. Or use `classical` at the right scope level
  3. Prove `strong_approximation_ratfunc` returns sum of principal parts when D.finite is effective
  4. Prove principal parts have `intDegree ≤ -1` (standard rational function property)
- **Priority**: Must fix before final submission, but does not block Cycle 282+
