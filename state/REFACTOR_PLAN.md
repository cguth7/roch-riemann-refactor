# Refactor Plan: P¹ → Arbitrary Curves

**Status**: P¹ nearly complete, 1 sorry + 1 compile error remaining (Cycle 278)
**Goal**: Transform P¹ Riemann-Roch into a framework for arbitrary algebraic curves

---

## Quick Reference

| Phase | Status | Key Files |
|-------|--------|-----------|
| 0-1 | ✅ Complete | Infrastructure, AdelicH1Full |
| 3 | ✅ Complete | Place.lean, DivisorV3, RRSpaceV3, P1Instance/ |
| 4 | 🔄 In Progress | Abstract.lean, AdelicH1Full (1 sorry) |
| 5-6 | ⏳ Future | Cleanup, new curve instances |

---

## Critical Discovery (Cycle 271): Affine vs Projective

**Problem**: The `AdelicRRData` class uses **affine** dimensions:
- `ell_finite` requires `Module.Finite k (RRSpace_proj k R K D)`
- For P¹: `RRSpace_proj(0)` = all polynomials = **infinite dimensional**

**Root Cause**: `RRSpace_proj` uses `HeightOneSpectrum R` (finite places only).
Elements are "integral at all finite places" but can have ANY pole at infinity.

**Solution** (Cycle 271): Created `ProjectiveAdelicRRData` in Abstract.lean:
- Uses `ExtendedDivisor` (includes infinity coefficient)
- Uses `RRSpace_proj_ext` (projective L(D) with degree bound)
- Uses `ell_proj_ext` (projective dimension - finite for P¹!)

**Files involved**:
- `AdelicH1Full.lean` - Has `ExtendedDivisor`, `RRSpace_proj_ext`, `ell_proj_ext`
- `Abstract.lean` - Now has `ProjectiveAdelicRRData` class

---

## Current Work: Cycle 279

**Task**: Complete `globalPlusBoundedSubmodule_full_eq_top` (full strong approximation)

**Recent Progress**:
- ✅ Cycle 274-276: Pole-clearing infrastructure built
- ✅ Cycle 277: `RRSpace_proj_ext_finite` PROVED via pole-clearing
- 🔄 Cycle 278: Added `exists_local_approximant_with_bound_infty` helper (compile error)

**Sorries remaining**:
| Sorry | Location | Description |
|-------|----------|-------------|
| `globalPlusBoundedSubmodule_full_eq_top` | AdelicH1Full:~605 | Proves h¹(D)=0 for P¹ |
| Abstract.lean sorries | Various | Blocked by above |

**Blocking issue**: Compile error at AdelicH1Full:568
- `Valued.isClopen_closedBall` API mismatch
- Need to check correct Mathlib signature for clopen balls

**Proof strategy for globalPlusBoundedSubmodule_full_eq_top**:
1. Use `exists_local_approximant_with_bound_infty` to approximate at infinity first
2. Apply `strong_approximation_ratfunc` to adjusted finite adele
3. Combine: k = k₁ + k₂ satisfies both bounds
4. Challenge: ensure k₂ from finite approx doesn't mess up infinity bound

---

## Phase Summary (Completed)

### Phase 0-1: Cleanup + Infrastructure ✅
- AdelicH1Full sorries filled
- Residue.lean split into 5 focused files

### Phase 3: Place Type ✅ (Cycles 249-265)
- `Place.lean` - Unified place type (finite + infinite)
- `DivisorV3.lean` - Projective divisors over all places
- `RRSpaceV3.lean` - Projective L(D) as k-module
- `P1Instance/` - Full P¹ Riemann-Roch (sorry-free)

### Phase 4.1: Finiteness ✅ (Cycles 274-277)
- Built pole-clearing infrastructure
- `clearingPoly` - product of generators at places with D(v) > 0
- `RRSpace_proj_ext_finite` - L(D) finite-dimensional for all extended divisors
- Key technique: embed L(D) ↪ Polynomial.degreeLT via f ↦ f·clearingPoly

---

## Remaining Phases

### Phase 4.2: Complete H¹ Vanishing (Current - Cycle 279)
**Immediate**: Fix compile error, then fill `globalPlusBoundedSubmodule_full_eq_top`
- This proves h¹(D) = 0 for P¹ (strong approximation at all places)
- Once complete: Abstract.lean sorries become fillable

### Phase 4.3: Wire P¹ into Abstract.lean (Next)
- Create P¹ instance of `ProjectiveAdelicRRData`
- Bridge between `RRSpace_proj_ext` and `RRSpace_ratfunc_projective`
- Fill remaining Abstract.lean sorries

### Phase 5: Cleanup (Low Priority)
Move P¹-specific files to archive once general framework works.

### Phase 6: New Curve Instances (Future)
```lean
instance ellipticRRData (E : EllipticCurve Fq) :
    ProjectiveAdelicRRData Fq (canonicalExt E) 1 where
  h1_finite := sorry
  ell_finite := sorry
  ...
```

---

## Key Insights for Future Agents

1. **Affine Trap**: `HeightOneSpectrum R` misses infinite places. Use `Place` type.
2. **Two dimension functions**:
   - `ell_proj` (affine) - infinite for P¹ at D=0
   - `ell_proj_ext` / `ell_ratfunc_projective` (projective) - finite for P¹
3. **P¹ proofs bypass Riemann Inequality**: Use direct induction, not RR framework
4. **For general curves**: Must use Riemann Inequality + Serre Duality approach

---

*Updated Cycle 278: RRSpace_proj_ext_finite proved, 1 sorry remaining (globalPlusBoundedSubmodule_full_eq_top).*
