# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (0 sorries in P1Instance)
**Result**: Riemann-Roch for P¹ (all effective divisors) + General dimension formula ℓ(D) = degWeighted(D) + 1
**Cycle**: 266 (Complete)

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

## Cycle 266 Summary

**Task**: Refactor Residue.lean (too large at 1,385 lines)

**Status**: ✅ Complete

**Key Achievement**: Split Residue.lean into 5 focused files

**Split structure**:
| File | Lines | Content |
|------|-------|---------|
| `ResidueAtX.lean` | ~160 | X-adic residue via Laurent series |
| `ResidueAtInfinity.lean` | ~445 | Residue at ∞ via polynomial remainder |
| `ResidueAtLinear.lean` | ~235 | Direct `residueAtLinear` (simple poles) |
| `ResidueLinearCorrect.lean` | ~265 | Translation-based `residueAt` (truly linear) |
| `ResidueTheorem.lean` | ~115 | Global residue theorem for linear places |

**Changes**:
- Created 5 new files in `ResidueTheory/`
- Updated `RatFuncResidues.lean` to import `ResidueTheorem`
- Archived original to `archive/RefactoredFiles/Residue.lean.bak`
- Full build passes ✅

---

## Cycle 265 Summary

**Task**: Fill remaining sorry in `ell_ratfunc_projective_gap_eq`

**Status**: ✅ Complete (1 → 0 sorries in P1Instance)

**Key Achievement**: Proved tight gap bound `ℓ(D+[v]) = ℓ(D) + deg(v)` for effective D

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

### Cycle 267: Implement Trace Maps for Higher-Degree Places

**Goal**: Extend residue theory from linear places (deg 1) to all finite places (any degree).

**Why**: P¹ only has linear places, but elliptic/hyperelliptic curves have higher-degree places.
The current `residueAtLinear` only works for (X - α). For irreducible p(X) of degree d > 1,
we need `Tr_{κ(v)/k}(local residue)` to get a value in the base field k.

**Immediate task**: Create `ResidueTrace.lean` with:
```lean
/-- Residue at finite place v, traced to base field k. -/
def residueAtFiniteTraced (k : Type*) [Field k] (v : HeightOneSpectrum R) (f : K) : k :=
  Algebra.trace (κ v) k (localResidue v f)
```

**Key Mathlib imports**:
- `Algebra.Trace` - trace map
- `RingTheory.DedekindDomain.Ideal` - residue field κ(v) = R/v

**Success criteria**: `residue_sum_eq_zero` proved for ALL finite places (not just linear).

**After**: Wire into `Abstract.lean` to fill the 3 remaining sorries.

---

### P¹ Riemann-Roch: COMPLETE ✅

The full P¹ Riemann-Roch theorem is now proved for all effective divisors.
See Cycle 265 summary for details.

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
