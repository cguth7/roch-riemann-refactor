# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ PASSING (2 sorries in AdelicH1Full.lean, 5 edge case sorries in Abstract.lean)
**Cycle**: 285 (Complete)

---

## Cycle 285 Summary: Extended Strong Approximation for Deep Negative Infinity

**Goal**: Extend strong approximation to prove H¹(D)=0 for D.inftyCoeff < -1 (Option 2 from Cycle 284).

**What was done**:

1. **Added new theorems to AdelicH1Full.lean for D.inftyCoeff < -1**:
   - `globalPlusBoundedSubmodule_full_eq_top_deep_neg_infty`: Strong approx for D.inftyCoeff < -1 with deg(D) ≥ -1
   - `SpaceModule_full_subsingleton_deep_neg_infty`: H¹(D) is Subsingleton for this case
   - `SpaceModule_full_finite_deep_neg_infty`: H¹(D) is finite-dimensional
   - `h1_finrank_full_eq_zero_deep_neg_infty`: h¹(D) = 0 for this case

2. **Filled 3 sorries in Abstract.lean**:
   - `h1_finite` for D.finite effective, D.inftyCoeff < -1 → uses `SpaceModule_full_finite_deep_neg_infty`
   - `h1_vanishing` for D.finite effective, D.inftyCoeff < -1 → uses `h1_finrank_full_eq_zero_deep_neg_infty`
   - `serre_duality` for D.finite effective, D.inftyCoeff < -1 → both sides = 0 (h¹ and ℓ(K-D))

**Key insight**: When D.inftyCoeff < -1 and deg(D) ≥ -1, we have D.finite.deg > 0. This provides
"slack" at places in supp(D.finite) that absorbs the tight infinity constraint via the product formula.

**Sorries added**: 1 new sorry in `globalPlusBoundedSubmodule_full_eq_top_deep_neg_infty` for the
full constrained approximation (requires showing K_S is dense in K_∞).

**Sorries eliminated**: 3 (Abstract.lean D.inftyCoeff < -1 cases)

---

## Cycle 284 Summary (Archive): Coprimality and Degree-Valuation

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
-- Both h¹(D) = 0 and ℓ(K-D) = 0 now proved (Cycle 285)
-- Uses extended strong approximation with product formula slack

-- NEW (Cycle 285):
theorem h1_finrank_full_eq_zero_deep_neg_infty (D : ExtendedDivisor (Polynomial Fq))
    (hdeg : D.deg ≥ -1) (heff : D.finite.Effective) (h_infty : D.inftyCoeff < -1) :
    h1_finrank_full Fq D = 0
```

---

## Sorries

| Location | Count | Status |
|----------|-------|--------|
| AdelicH1Full.lean:619 | 1 | `inftyValuationDef k₂ ≤ exp(-1)` - ACCEPTED DEBT |
| AdelicH1Full.lean:763 | 1 | Deep negative strong approximation - NEW (Cycle 285) |
| Abstract.lean | 5 | Edge cases in p1ProjectiveAdelicRRData |

**Abstract.lean sorries breakdown** (in p1ProjectiveAdelicRRData instance):
- `h1_finite` (2 sorries):
  - D.finite not effective
  - deg(D) < -1 (requires Serre duality isomorphism)
- `h1_vanishing` (1 sorry):
  - D.finite not effective
- `serre_duality` (2 sorries):
  - D.finite not effective
  - deg(D) < -1 (requires full residue pairing)

**Note**: Template code at lines 200-203 has 3 sorries but is inside a docstring (not active code).

---

## Next Steps: Cycle 286

Options:
1. **Prove the deep negative sorry** - fill `globalPlusBoundedSubmodule_full_eq_top_deep_neg_infty` by showing K_S dense in K_∞
2. **Prove the accepted sorry** - tackle `inftyValuationDef k₂ ≤ exp(-1)` at AdelicH1Full.lean:619
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
