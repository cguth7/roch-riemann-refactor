# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ PASSING (2 sorries in AdelicH1Full.lean, 8 edge case sorries in Abstract.lean)
**Cycle**: 282 (Complete)

---

## Cycle 282 Summary: Edge Case Analysis

**Goal**: Fill edge case sorries in Abstract.lean.

**What was done**:

1. **Added new theorems to AdelicH1Full.lean**:
   - `RRSpace_proj_ext_canonical_sub_eq_bot_neg_infty`: L(K-D) = {0} when D.finite effective and -1 ≤ D.inftyCoeff < 0
   - `ell_proj_ext_canonical_sub_eq_zero_neg_infty`: ℓ(K-D) = 0 for the above case
   - `RRSpace_proj_ext_canonical_sub_eq_bot_deep_neg_infty`: L(K-D) = {0} when D.finite effective, D.inftyCoeff < -1, deg(D) ≥ -1 (has 1 sorry for degree-valuation relationship)
   - `ell_proj_ext_canonical_sub_eq_zero_deep_neg_infty`: ℓ(K-D) = 0 for the above case

2. **Fixed one serre_duality edge case**:
   - For D.finite effective, -1 ≤ D.inftyCoeff < 0: NOW PROVED via the new theorems
   - Both h¹(D) = 0 and ℓ(K-D) = 0, so Serre duality holds as 0 = 0

3. **Analyzed remaining edge cases**:
   - D.finite not effective: Requires more complex analysis (elements of L(K-D) can have poles)
   - D.inftyCoeff < -1: Strong approximation proof fails at infinity (k₂ has |k₂|_∞ ≤ exp(-1) but we need ≤ exp(D.inftyCoeff) < exp(-1))
   - deg(D) < -1: Non-vanishing case requiring full residue pairing construction

**Key insight**: For P¹, the main applications use effective divisors with inftyCoeff ≥ 0. The edge cases (non-effective or deeply negative inftyCoeff) are mathematically valid but less common in practice.

---

## Cycle 281 Summary (Archive)

**Goal**: Connect the new `ResidueTrace` engine to the rest of the codebase.

**What was done**:
1. Fixed Abstract.lean build errors from Cycle 280 API changes
2. Verified ResidueTrace wiring
3. Confirmed sorry-free components: P1Instance/, ResidueTheory/

---

## What's Proved

```lean
-- Main Serre duality for P¹ (effective divisors with non-negative inftyCoeff)
theorem serre_duality_p1 (D : ExtendedDivisor (Polynomial Fq))
    (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    h1_finrank_full Fq D = ell_proj_ext Fq (canonicalExtended Fq - D)

-- Extended case: D.finite effective, -1 ≤ D.inftyCoeff < 0
-- Proved via: h¹(D) = 0 (SpaceModule_full_subsingleton) and ℓ(K-D) = 0 (new theorem)
```

---

## Sorries

| Location | Count | Status |
|----------|-------|--------|
| AdelicH1Full.lean:619 | 1 | `inftyValuationDef k₂ ≤ exp(-1)` - ACCEPTED DEBT |
| AdelicH1Full.lean:893 | 1 | Polynomial degree-valuation relationship - NEW |
| Abstract.lean | 8 | Edge cases in p1ProjectiveAdelicRRData |

**Abstract.lean sorries breakdown** (in p1ProjectiveAdelicRRData instance):
- `h1_finite` (3 sorries):
  - D.finite effective, D.inftyCoeff < -1
  - D.finite not effective
  - deg(D) < -1 (requires Serre duality isomorphism)
- `h1_vanishing` (2 sorries):
  - D.finite effective, D.inftyCoeff < -1
  - D.finite not effective
- `serre_duality` (3 sorries):
  - D.finite effective, D.inftyCoeff < -1 (ℓ(K-D)=0 proved, h¹(D)=0 needs extended strong approx)
  - D.finite not effective
  - deg(D) < -1 (requires full residue pairing)

**Note**: Template code at lines 200-203 has 3 sorries but is commented out (not active code).

---

## Next Steps: Cycle 283

Options:
1. **Prove AdelicH1Full.lean:893** - the polynomial degree-valuation relationship
   - Need: Σ ord_v(p)·deg(v) ≤ p.natDegree for polynomial p
   - This would complete ℓ(K-D)=0 for deeply negative inftyCoeff case

2. **Extend strong approximation** - prove H¹(D)=0 for D.inftyCoeff < -1
   - Requires modifying the k₂ construction to have smaller infinity valuation
   - Mathematically: use polynomial adjustment at infinity

3. **Prove the accepted sorry** - tackle `inftyValuationDef k₂ ≤ exp(-1)`

4. **Begin elliptic curve infrastructure** - extend Place type to support higher genus

---

## Technical Debt Notes

**AdelicH1Full.lean:619** - Principal parts infinity bound
- **What to prove**: `FunctionField.inftyValuationDef Fq k₂ ≤ WithZero.exp (-1)`
- **Mathematical fact**: Principal parts at finite places are proper fractions
- **Status**: ACCEPTED DEBT from Cycle 280

**AdelicH1Full.lean:893** - Polynomial degree-valuation (NEW)
- **What to prove**: For polynomial p with val_v(p) ≤ exp(-n), the total zeros (weighted by place degree) is at least n
- **Mathematical fact**: Σ_{v|p} ord_v(p)·deg(v) = p.natDegree (fundamental theorem of algebra)
- **Status**: Documented, blocks deep-negative-infty case
