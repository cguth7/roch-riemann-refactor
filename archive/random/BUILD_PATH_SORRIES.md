# Build Path & Sorry Analysis

**Updated: Cycle 233**

## Summary

Build path now includes SerreDuality files. Current state:
- **DimensionScratch.lean**: 3 sorries (down from 6) - **BLOCKING**
- **RatFuncFullRR.lean**: 0 sorries - compiles clean
- **IntDegreeTest.lean**: 0 sorries - compiles clean

---

## Current Blocker: `linearPlace_residue_finrank`

**Goal**: Prove `Module.finrank Fq (residueFieldAtPrime (Polynomial Fq) (linearPlace α)) = 1`

**What's done**:
- `linearPlace_residue_equiv` : `κ(v) ≃+* Fq` - PROVED
- This ring equivalence should give finrank = 1

**What's failing**:
Converting the RingEquiv to a LinearEquiv over Fq fails with type mismatch:
```
LinearEquiv.ofBijective expects Function.Bijective ⇑?m.119
but hbij has type Function.Bijective ⇑(algebraMap (R ⧸ I) I.ResidueField)
```

**Suggested approaches**:
1. Use `RationalPoint` typeclass from `Projective.lean`
   - Instantiate `RationalPoint Fq (Polynomial Fq) (linearPlace α)`
   - Use `linearPlace_residue_equiv.symm` as the `residue_equiv` field
   - Then `residue_finrank_eq_one` gives the result

2. Build the linear equiv manually:
   - The issue is scalar compatibility: need `e (c • x) = c • e x`
   - For ring equiv between Fq-algebras, this should be automatic
   - May need to use `AlgEquiv` instead of `RingEquiv`

---

## Dependency Chain

```
riemann_roch_ratfunc (NOT PROVED)
    ├─→ ell_ratfunc_projective_eq_deg_plus_one (sorry, line ~656)
    │       ├─→ ell_ratfunc_projective_gap_le (sorry, line ~137)
    │       │       └─→ linearPlace_residue_finrank (BLOCKED, line ~95)
    │       │               └─→ linearPlace_residue_equiv ✅
    │       ├─→ inv_X_sub_C_pow_mem_projective_general ✅
    │       └─→ inv_X_sub_C_pow_not_mem_projective_general ✅
    └─→ ell_canonical_sub_zero ✅
```

---

## Key Mathlib Lemmas

```lean
-- From Mathlib.RingTheory.Polynomial.Quotient
Polynomial.quotientSpanXSubCAlgEquiv (x : R) :
    (R[X] ⧸ Ideal.span ({X - C x})) ≃ₐ[R] R

-- From Mathlib.RingTheory.Ideal.Quotient.Operations
Ideal.bijective_algebraMap_quotient_residueField (I : Ideal R) [I.IsMaximal] :
    Function.Bijective (algebraMap (R ⧸ I) I.ResidueField)
```

---

## Files to Read

1. `RrLean/RiemannRochV2/SerreDuality/DimensionScratch.lean` - Main file, lines 76-124
2. `RrLean/RiemannRochV2/Projective.lean` - `RationalPoint` typeclass, lines 78-92
3. `RrLean/RiemannRochV2/Infrastructure.lean` - `residueFieldAtPrime.linearEquiv`

---

## Build Command

```bash
lake build RrLean.RiemannRochV2.SerreDuality.DimensionScratch 2>&1 | grep -E "(error|sorry)"
```

---

## Other Sorries (Low Priority)

These are not on the critical path:

| File | Line | Notes |
|------|------|-------|
| RatFuncPairing.lean | 1896 | Dead code - superseded |
| ProductFormula.lean | 111 | Intentionally wrong lemma |
| TraceDualityProof.lean | 144 | Alternative approach |
| FullAdelesCompact.lean | 984 | Edge case not needed |
| Residue.lean | 1282, 1397 | Higher-degree places |
