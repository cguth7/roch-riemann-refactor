# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ PASSING (with 1 sorry in AdelicH1Full.lean)
**Cycle**: 280 (In Progress)

---

## Recent Fix (Cycle 280)

**Problem**: Lines 654-656 and 663-664 had `simp` proofs that didn't close goals because:
1. `FullAdeleRing` is a `def` not an `abbrev`, so `Prod.fst_sub` etc. didn't apply
2. Needed to unfold `AdelicH1v2.diagonalK` and apply `sub_sub`

**Solution**:
1. Added simp lemmas in `FullAdelesBase.lean`:
   - `FullAdeleRing.fst_sub`, `FullAdeleRing.snd_sub`
   - `FullAdeleRing.fst_add`, `FullAdeleRing.snd_add`
2. Updated simp calls to include `AdelicH1v2.diagonalK` and `sub_sub`

---

## What's Proved (when build works)

```lean
theorem serre_duality_p1 (D : ExtendedDivisor (Polynomial Fq))
    (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    h1_finrank_full Fq D = ell_proj_ext Fq (canonicalExtended Fq - D)
```

---

## Mathematical Analysis (Cycle 280 - Complete)

**The remaining sorry** at line ~680: Prove `|k₂|_∞ ≤ exp(D.inftyCoeff)`

**Key insight**:
- k₂ from strong_approximation is sum of principal parts at finite places
- Principal parts have `|pp_v|_∞ ≤ exp(-1)` (poles at finite places = zeros at infinity)
- So `|k₂|_∞ ≤ exp(-1)`
- Need `exp(-1) ≤ exp(D.inftyCoeff)`, i.e., `D.inftyCoeff ≥ -1`

**Gap**: Hypothesis `D.deg ≥ -1` only gives `D.inftyCoeff ≥ -1 - D.finite.deg`

**For serre_duality_p1**: Hypothesis `D.inftyCoeff ≥ 0` makes the bound work.

---

## Next Steps

1. **Prove the sorry at line ~680**: Need to show `|k₂|_∞ ≤ exp(D.inftyCoeff)`
   - This requires proving that k₂ from strong approximation has bounded infinity valuation
   - Use the fact that k₂ is a sum of principal parts at finite places

---

## Sorries

| Location | Count | Status |
|----------|-------|--------|
| AdelicH1Full.lean | 1 | Line ~680: `|k₂|_∞ ≤ exp(D.inftyCoeff)` |
| Abstract.lean | 5 | General infrastructure |
