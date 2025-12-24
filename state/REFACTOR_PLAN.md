# Refactor Plan: P¹ → Arbitrary Curves

**Status**: P¹ COMPLETE, Abstract.lean integration in progress (Cycle 271)
**Goal**: Transform P¹ Riemann-Roch into a framework for arbitrary algebraic curves

---

## Quick Reference

| Phase | Status | Key Files |
|-------|--------|-----------|
| 0-1 | ✅ Complete | Infrastructure, AdelicH1Full |
| 3 | ✅ Complete | Place.lean, DivisorV3, RRSpaceV3, P1Instance/ |
| 4 | 🔄 In Progress | Abstract.lean (ProjectiveAdelicRRData) |
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

## Current Work: Cycle 272

**Task**: Fill 4 sorries in projective infrastructure

**Sorries remaining**:
| Sorry | Location | Description |
|-------|----------|-------------|
| `globalPlusBoundedSubmodule_full_eq_top` | AdelicH1Full:580 | Extend strong approx to full adeles |
| `RRSpace_proj_ext_canonical_sub_eq_bot` helper | AdelicH1Full:641 | Show f is polynomial |
| `RRSpace_proj_ext_finite` | AdelicH1Full:704 | Finiteness of RRSpace_proj_ext |
| `serre_duality` case | Abstract:305 | D.inftyCoeff < 0 case |

**Cycle 271 completed**: Created `p1ProjectiveAdelicRRData` instance

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

---

## Remaining Phases

### Phase 4.2: Wire P¹ into Abstract.lean (Current)
- Create P¹ instance of `ProjectiveAdelicRRData`
- Bridge between `RRSpace_proj_ext` and `RRSpace_ratfunc_projective`

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

*Updated Cycle 271: Added ProjectiveAdelicRRData, documented affine/projective mismatch.*
