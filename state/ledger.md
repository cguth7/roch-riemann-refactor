# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ PASSING (1 sorry in AdelicH1Full.lean, 8 edge case sorries in Abstract.lean)
**Cycle**: 284 (Complete)

---

## Cycle 284 Summary: Coprimality and Degree-Valuation

**Goal**: Fill the coprimality sorry in PlaceDegree.lean, then use it to complete AdelicH1Full.lean:999.

**What was done**:

1. **Completed `natDegree_ge_degWeighted_of_valuation_bounds` in PlaceDegree.lean**:
   - Proved generators at different places are coprime via `generator_not_mem_other_prime`
   - Used `Irreducible.coprime_iff_not_dvd` and `isCoprime_comm` for coprimality
   - Applied `IsCoprime.pow` for powers of coprime elements
   - Used `Finset.prod_dvd_of_coprime` to show product divides p
   - Used `monic_prod_of_monic` and `natDegree_prod_of_monic` for degree calculation
   - Final chain: p.natDegree ≥ product.natDegree = degWeighted ≥ D.deg

2. **Filled AdelicH1Full.lean:999** (formerly line 999, now uses new lemma):
   - Applied `valuation_of_algebraMap` to convert RatFunc valuation to polynomial valuation
   - Used `natDegree_ge_degWeighted_of_valuation_bounds` to get p.natDegree ≥ degWeighted
   - Used `degWeighted_ge_deg` to get degWeighted ≥ D.finite.deg
   - Contradiction with p.natDegree < D.finite.deg via omega

**Sorries eliminated**: 2 (PlaceDegree.lean:403, AdelicH1Full.lean:999)

---

## Cycle 283 Summary (Archive)

**Goal**: Fill the degree-valuation relationship sorry in AdelicH1Full.lean.

**What was done**:

1. **Added new lemmas to PlaceDegree.lean**:
   - `asIdeal_pow_eq_span_generator_pow`: v.asIdeal^n = span{gen_v^n}
   - `mem_asIdeal_pow_iff_generator_pow_dvd`: Membership ↔ generator power divides
   - `natDegree_ge_of_pow_dvd`: If g^n | p (g monic), then p.natDegree ≥ n * g.natDegree
   - `natDegree_ge_of_intValuation_le`: If val_v(p) ≤ exp(-n), then p.natDegree ≥ n * deg(v)
   - `degWeighted_ge_deg`: For effective D, degWeighted ≥ D.deg (proved!)
   - `natDegree_ge_degWeighted_of_valuation_bounds`: Sum version (had 1 sorry, now filled in Cycle 284)

---

## Cycle 282 Summary (Archive)

**Goal**: Fill edge case sorries in Abstract.lean.

**What was done**:

1. **Added new theorems to AdelicH1Full.lean**:
   - `RRSpace_proj_ext_canonical_sub_eq_bot_neg_infty`: L(K-D) = {0} when D.finite effective and -1 ≤ D.inftyCoeff < 0
   - `ell_proj_ext_canonical_sub_eq_zero_neg_infty`: ℓ(K-D) = 0 for the above case
   - `RRSpace_proj_ext_canonical_sub_eq_bot_deep_neg_infty`: L(K-D) = {0} when D.finite effective, D.inftyCoeff < -1, deg(D) ≥ -1 (now fully proved!)
   - `ell_proj_ext_canonical_sub_eq_zero_deep_neg_infty`: ℓ(K-D) = 0 for the above case

---

## What's Proved

```lean
-- Main Serre duality for P¹ (effective divisors with non-negative inftyCoeff)
theorem serre_duality_p1 (D : ExtendedDivisor (Polynomial Fq))
    (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    h1_finrank_full Fq D = ell_proj_ext Fq (canonicalExtended Fq - D)

-- Extended case: D.finite effective, -1 ≤ D.inftyCoeff < 0
-- Proved via: h¹(D) = 0 (SpaceModule_full_subsingleton) and ℓ(K-D) = 0

-- Deep negative case: D.finite effective, D.inftyCoeff < -1, deg(D) ≥ -1
-- L(K-D) = {0} now fully proved via valuation-degree relationship
```

---

## Sorries

| Location | Count | Status |
|----------|-------|--------|
| AdelicH1Full.lean:619 | 1 | `inftyValuationDef k₂ ≤ exp(-1)` - ACCEPTED DEBT |
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

**Note**: Template code at lines 200-203 has 3 sorries but is inside a docstring (not active code).

---

## Next Steps: Cycle 285

Options:
1. **Prove the accepted sorry** - tackle `inftyValuationDef k₂ ≤ exp(-1)` at AdelicH1Full.lean:619
2. **Extend strong approximation** - prove H¹(D)=0 for D.inftyCoeff < -1 (unblocks 3 Abstract.lean sorries)
3. **Handle non-effective divisors** - characterize L(D) and H¹(D) when D.finite not effective
4. **Begin elliptic curve infrastructure** - extend Place type to support higher genus

---

## Technical Debt Notes

**AdelicH1Full.lean:619** - Principal parts infinity bound
- **What to prove**: `FunctionField.inftyValuationDef Fq k₂ ≤ WithZero.exp (-1)`
- **Mathematical fact**: Principal parts at finite places are proper fractions
- **Status**: ACCEPTED DEBT from Cycle 280

**Abstract.lean edge cases** - Non-effective and deep negative
- **What to prove**: Various H¹ and Serre duality results for edge cases
- **Mathematical fact**: For P¹, most edge cases are vacuous (no such divisors arise naturally)
- **Status**: Low priority, mainly needed for full generality
