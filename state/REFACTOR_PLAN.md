# Refactor Plan: P¹ → Arbitrary Curves

**Status**: P¹ Serre duality proved, valuation-degree infrastructure complete (Cycle 284)
**Goal**: Transform P¹ Riemann-Roch into a framework for arbitrary algebraic curves

---

## Quick Reference

| Phase | Status | Key Achievement |
|-------|--------|-----------------|
| 0-1 | ✅ Complete | Infrastructure, AdelicH1Full |
| 3 | ✅ Complete | Place.lean, DivisorV3, P1Instance/ |
| 4 | ✅ Complete | serre_duality_p1 proved |
| 4.5 | ✅ Complete | Valuation-degree infrastructure (Cycle 284) |
| 5 | ⏳ Optional | Clean up edge cases in Abstract.lean |
| 6 | ⏳ Future | New curve instances (elliptic, hyperelliptic) |

---

## Current State (Cycle 284)

**Proved**:
```lean
theorem serre_duality_p1 (D : ExtendedDivisor (Polynomial Fq))
    (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    h1_finrank_full Fq D = ell_proj_ext Fq (canonicalExtended Fq - D)

lemma natDegree_ge_degWeighted_of_valuation_bounds (D : DivisorV2 (Polynomial k))
    (hD_eff : D.Effective) (p : Polynomial k) (hp_ne : p ≠ 0)
    (hval : ∀ v ∈ D.support, v.intValuation p ≤ exp(-(D v))) :
    (p.natDegree : ℤ) ≥ degWeighted k D
```

**Remaining sorries**:
- AdelicH1Full.lean:619 - 1 (accepted technical debt)
- Abstract.lean - 8 (edge cases, low priority)

---

## Completed Phases

### Phase 0-1: Cleanup + Infrastructure ✅
- AdelicH1Full sorries filled
- Residue infrastructure established

### Phase 3: Place Type ✅ (Cycles 249-265)
- `Place.lean` - Unified place type
- `DivisorV3.lean` - Projective divisors
- `P1Instance/` - Full P¹ (sorry-free)

### Phase 4: Serre Duality ✅ (Cycles 274-280)
- `serre_duality_p1` proved for effective D

### Phase 4.5: Valuation-Degree ✅ (Cycles 283-284)
- `natDegree_ge_degWeighted_of_valuation_bounds` - coprimality proof
- `RRSpace_proj_ext_canonical_sub_eq_bot_deep_neg_infty` - now fully proved
- Key insight: generators at different places are coprime irreducibles

---

## Remaining Phases

### Phase 5: Edge Case Cleanup (Optional)
Fill Abstract.lean sorries for:
- `h1_finite` with D.inftyCoeff < -1 or D.finite not effective
- `h1_vanishing` for same edge cases
- `serre_duality` for deg(D) < -1

**Priority**: Low. These edge cases rarely arise in practice.

### Phase 6: New Curve Instances (Future)
```lean
instance ellipticRRData (E : EllipticCurve Fq) :
    ProjectiveAdelicRRData Fq (canonicalExt E) 1 where
  h1_finite := ...
  ell_finite := ...
  serre_duality := ...
```

**Requirements**:
- Coordinate ring for elliptic curves
- Canonical divisor computation
- Strong approximation for genus 1

---

## Key Infrastructure Now Available

| Lemma | Location | Use |
|-------|----------|-----|
| `generator_not_mem_other_prime` | PlaceDegree.lean | Coprimality of generators |
| `natDegree_ge_degWeighted_of_valuation_bounds` | PlaceDegree.lean | Degree bounds from valuations |
| `valuation_of_algebraMap` | Mathlib | Convert RatFunc to polynomial valuation |
| `degWeighted_ge_deg` | PlaceDegree.lean | Weighted ≥ unweighted for effective |

---

*Updated Cycle 284: Valuation-degree infrastructure complete, 2 sorries eliminated.*
