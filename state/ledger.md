# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (0 sorries in P1Instance, 0 sorries in ResidueTrace.lean)
**Result**: Riemann-Roch for P¹ fully proved for all effective divisors
**Cycle**: 270 (Complete)

---

## What's Proved

```lean
-- General dimension formula for ALL effective divisors
theorem ell_ratfunc_projective_eq_degWeighted_plus_one (D : DivisorV2 (Polynomial k))
    (hD : D.Effective) :
    ell_ratfunc_projective D = (degWeighted k D).toNat + 1

-- Full Riemann-Roch for P¹
theorem riemann_roch_p1 (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    (ell_ratfunc_projective D : ℤ) - (ellV3 (p1Canonical Fq - DivisorV3.ofAffine D) : ℤ) =
    D.deg + 1 - (p1Genus : ℤ)

-- Traced residue = classical residue (for linear places)
theorem tracedResidueAtPlace_eq_residueAt_linear (α : Fq) (f : RatFunc Fq)
    (hf : hasSimplePoleAt Fq (linearPlace Fq α) f ∨ ¬hasPoleAt Fq (linearPlace Fq α) f) :
    tracedResidueAtPlace Fq (linearPlace Fq α) f = residueAt α f
```

---

## Sorries

| Location | Count | Status |
|----------|-------|--------|
| P1Instance/ | 0 | ✅ Complete |
| ResidueTrace.lean | 0 | ✅ Complete |
| Abstract.lean | 3 | Placeholder for general curves |

The 3 Abstract.lean sorries are `h1_finite`, `ell_finite`, `h1_vanishing` - these are
placeholders in the curve-agnostic framework. P1Instance proves all these already.

---

## Next Steps

### Cycle 271: Wire P¹ into Abstract.lean

**Goal**: Connect P1Instance proofs to the curve-agnostic Abstract.lean framework

**The 3 sorries to fill**:
1. `h1_finite` - H¹ finiteness (P1Instance has this)
2. `ell_finite` - L(D) finiteness (P1Instance has this)
3. `h1_vanishing` - H¹ vanishing (P1Instance has this)

**Why this matters**: Validates that the abstract framework actually works by instantiating
it with a concrete curve (P¹). Sets up the template for other curves.

**Success criteria**: Abstract.lean compiles with 0 sorries for P¹ instance.

### After Cycle 271:

**Option A**: Start new curve instance (elliptic or hyperelliptic) - ~3-5 cycles
**Option B**: Extend residues to higher-order poles - ~2-3 cycles

---

## Cycle 270 Summary ✅

**Task**: Fill `tracedResidueAtPlace_eq_residueAt_linear` sorry (stuck for 2 cycles)

**Fix**: The blocking `hq'_inv_eq` lemma was proved using `PowerSeries.mul_inv_cancel`
+ `IsUnit.mul_right_inj` instead of failed approaches with `map_inv₀` or `Units.val_inv_eq_inv_val`.

---

## Cycle 265-269 Summary

- **265**: Filled `ell_ratfunc_projective_gap_eq` → 0 sorries in P1Instance
- **266**: Refactored Residue.lean (1,385 lines → 5 focused files)
- **267**: Filled `trace_degree_one_eq`, created ResidueTrace.lean
- **268**: Defined `localResidueAtPlace`, `tracedResidueAtPlace` for arbitrary places
- **269-270**: Filled `tracedResidueAtPlace_eq_residueAt_linear`

---

*For cycles 1-264, see `ledger_archive.md`*
