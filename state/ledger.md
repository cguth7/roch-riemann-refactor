# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (0 sorries in P1Instance)
**Result**: Riemann-Roch for P¹ (all effective divisors) + General dimension formula ℓ(D) = degWeighted(D) + 1
**Cycle**: 266 (Ready to start)

---

## What's Proved

```lean
-- General dimension formula for ALL effective divisors
theorem ell_ratfunc_projective_eq_degWeighted_plus_one (D : DivisorV2 (Polynomial k))
    (hD : D.Effective) :
    ell_ratfunc_projective D = (degWeighted k D).toNat + 1

-- Full Riemann-Roch for P¹ (linear places version)
theorem riemann_roch_p1 (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    (ell_ratfunc_projective D : ℤ) - (ellV3 (p1Canonical Fq - DivisorV3.ofAffine D) : ℤ) =
    D.deg + 1 - (p1Genus : ℤ)
```

Key results:
- **ℓ(D) = degWeighted(D) + 1** for ALL effective D (any places, any degrees)
- **ℓ(K-D) = 0** for effective D on P¹
- **g = 0** (genus of P¹)

---

## Cycle 265 Summary

**Task**: Fill remaining sorry in `ell_ratfunc_projective_gap_eq`

**Status**: ✅ Complete (1 → 0 sorries in P1Instance)

**Key Achievement**: Proved tight gap bound `ℓ(D+[v]) = ℓ(D) + deg(v)` for effective D

**Strategy**:
1. Added `evaluationMapAt_surj_projective` - strengthens `evaluationMapAt_surj` to return projective elements
2. Proved `ψ` surjective by case split: c=0 uses 0, c≠0 uses construction with `noPoleAtInfinity`
3. Used first isomorphism theorem: quotient `L(D+v)/L(D) ≅ κ(v)` via bijective descended map
4. `LinearEquiv.ofBijective` + `finrank_eq` gives `finrank(quotient) = deg(v)`
5. Combined with `finrank_quotient_add_finrank` to get equality

**Key lemmas**:
- `evaluationMapAt_surj_projective` - surjectivity from projective space (new)
- `LinearEquiv.ofBijective` - constructs equivalence from bijection
- `LinearEquiv.finrank_eq` - dimension preserved under equivalence
- `Submodule.finrank_quotient_add_finrank` - quotient dimension formula

---

## Sorries

**0 sorries in P1Instance/** - All P¹ Riemann-Roch proofs complete!

**Abstract.lean**: 3 sorries (placeholder `AdelicRRData` instance fields - not blocking)

**Sorry-free files**:
- DimensionGeneral.lean ✅ (includes `evaluationMapAt_surj_projective`, `ell_ratfunc_projective_gap_eq`)
- PlaceDegree.lean ✅ (includes uniformizer-generator relationship lemmas)
- GapBoundGeneral.lean ✅
- P1RiemannRoch.lean ✅
- P1VanishingLKD.lean ✅
- DimensionCore.lean ✅
- All other SerreDuality files ✅

---

## Build Commands

```bash
lake build RrLean.RiemannRochV2.P1Instance.DimensionGeneral 2>&1 | tail -5
grep -n "sorry" RrLean/RiemannRochV2/P1Instance/DimensionGeneral.lean
```

---

## Next Steps

### P¹ Riemann-Roch: COMPLETE ✅

The full P¹ Riemann-Roch theorem is now proved for all effective divisors:
- `ell_ratfunc_projective_eq_degWeighted_plus_one` - ℓ(D) = degWeighted(D) + 1

Key components:
- `evaluationMapAt_surj_projective` - evaluation is surjective from projective space
- `ell_ratfunc_projective_gap_eq` - tight gap bound ℓ(D+[v]) = ℓ(D) + deg(v)
- `RRSpace_ratfunc_projective_effective_finite` - L(D) is finite-dimensional for effective D

### Future Work

The main remaining work is in Abstract.lean (general Dedekind domain case):
- `AdelicRRData` instance for general R, K
- Strong approximation arguments
- Compactness-based finiteness proofs

See `REFACTOR_PLAN.md` for full roadmap.

---

## Refactor Status

**Completed Phases**:
- Phase 0: Cleanup ✅
- Phase 1: Complete Infrastructure ✅
- Phase 3: Place Type ✅
- Phase 3.5: Surjectivity for Dimension Formula ✅

**Next**: Phase 4 (Residue Theorem) or Phase 6 (New Curve Instances)

See `REFACTOR_PLAN.md` for full roadmap.

---

*For historical cycles 1-264, see `ledger_archive.md`*
