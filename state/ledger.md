# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (0 sorries in P1Instance, 0 sorries in ResidueTrace.lean)
**Result**: Riemann-Roch for P¹ fully proved for all effective divisors
**Cycle**: 271 (In Progress)

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
| Abstract.lean | 0 | ✅ (template sorries were in comments) |

**Cycle 271 Discovery**: The "3 sorries" were in a **comment block** template.
That template (`fqAdelicRRData`) can't work for P¹ anyway - affine trap!
Created `ProjectiveAdelicRRData` class instead.

---

## Next Steps

### Cycle 271: Wire P¹ into Abstract.lean (IN PROGRESS)

**Discovery**: The affine `AdelicRRData` **cannot** be instantiated for P¹!
- `AdelicRRData` requires `ell_finite : ∀ D, Module.Finite k (RRSpace_proj k R K D)`
- For P¹: `RRSpace_proj(0)` = all polynomials = **infinite dimensional** (affine trap)
- P1Instance proofs use `ell_ratfunc_projective` (projective) not `ell_proj` (affine)

**Solution**: Created `ProjectiveAdelicRRData` class in Abstract.lean that uses:
- `ExtendedDivisor` (includes infinity coefficient) instead of `DivisorV2`
- `RRSpace_proj_ext` (projective L(D) with degree bound) instead of `RRSpace_proj`
- `ell_proj_ext` (projective dimension) instead of `ell_proj`

**Progress**:
- [x] Analyzed affine vs projective mismatch
- [x] Found projective infrastructure in `AdelicH1Full.lean`
- [x] Created `ProjectiveAdelicRRData` class in Abstract.lean
- [ ] Instantiate `ProjectiveAdelicRRData` for P¹

**Remaining**:
- Create P¹ instance of `ProjectiveAdelicRRData` using:
  - `h1_finite`: From `h1_subsingleton` (H¹ is Subsingleton → finite)
  - `ell_finite`: From `RRSpace_ratfunc_projective_effective_finite`
  - `h1_vanishing`: From `h1_finrank_zero_of_large_deg`
  - `serre_duality`: Both H¹(D) and L(K-D) are 0 for P¹
  - `deg_canonical`: -2 = 2*0 - 2

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
