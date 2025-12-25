# Refactor Plan: P¹ → Arbitrary Curves

**Status**: P¹ Serre duality proved with 1 accepted sorry (Cycle 280 complete)
**Goal**: Transform P¹ Riemann-Roch into a framework for arbitrary algebraic curves

---

## Quick Reference

| Phase | Status | Key Files |
|-------|--------|-----------|
| 0-1 | ✅ Complete | Infrastructure, AdelicH1Full |
| 3 | ✅ Complete | Place.lean, DivisorV3, RRSpaceV3, P1Instance/ |
| 4 | ✅ Complete | Abstract.lean, AdelicH1Full, serre_duality_p1 |
| 5 | 🔄 Next | The Great Wiring (Residue Refactor) |
| 6 | ⏳ Future | New curve instances |

---

## Current State (Post-Cycle 280)

**Proved**:
```lean
theorem serre_duality_p1 (D : ExtendedDivisor (Polynomial Fq))
    (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    h1_finrank_full Fq D = ell_proj_ext Fq (canonicalExtended Fq - D)
```

**Technical debt**: 1 sorry in AdelicH1Full.lean:698
- What: Principal parts infinity bound (`inftyValuationDef k₂ ≤ exp(-1)`)
- Why sorried: Type class synthesis issues with Mathlib API
- Priority: Must fix before final submission, does not block Cycle 281+

---

## Completed Phases

### Phase 0-1: Cleanup + Infrastructure ✅
- AdelicH1Full sorries filled
- Residue.lean split into 5 focused files

### Phase 3: Place Type ✅ (Cycles 249-265)
- `Place.lean` - Unified place type (finite + infinite)
- `DivisorV3.lean` - Projective divisors over all places
- `RRSpaceV3.lean` - Projective L(D) as k-module
- `P1Instance/` - Full P¹ Riemann-Roch (sorry-free)

### Phase 4: Serre Duality ✅ (Cycles 274-280)
- Pole-clearing infrastructure
- `RRSpace_proj_ext_finite` - L(D) finite-dimensional
- `globalPlusBoundedSubmodule_full_eq_top_of_deg_ge_neg_one` - H¹(D) = 0 (1 accepted sorry)
- `serre_duality_p1` - h¹(D) = ℓ(K-D) for effective D

---

## Remaining Phases

### Phase 5: The Great Wiring (Cycle 281 - Next)
Refactor legacy residue code to use new `ResidueTrace` engine:
- Connect pairing infrastructure to traced residues
- Clean up redundant residue implementations
- Validates the framework end-to-end

### Phase 6: New Curve Instances (Future)
```lean
instance ellipticRRData (E : EllipticCurve Fq) :
    ProjectiveAdelicRRData Fq (canonicalExt E) 1 where
  h1_finite := sorry
  ell_finite := sorry
  ...
```

---

## Key Insights

1. **Affine Trap**: `HeightOneSpectrum R` misses infinite places. Use `Place` type.
2. **Two dimension functions**: `ell_proj` (affine, infinite for P¹) vs `ell_proj_ext` (projective, finite)
3. **Hypothesis lesson** (Cycle 280): `globalPlusBoundedSubmodule_full_eq_top` needed both `D.finite.Effective` and `D.inftyCoeff ≥ -1`, not just `D.deg ≥ -1`

---

*Updated Cycle 280: serre_duality_p1 proved, 1 accepted sorry (technical debt).*
