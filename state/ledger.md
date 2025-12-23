# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (1 sorry in DimensionGeneral.lean)
**Result**: Riemann-Roch for P¹ (linear places) + Generalized gap bound + Finiteness for all effective D
**Cycle**: 265 (Ready to start)

---

## What's Proved

```lean
theorem riemann_roch_p1 (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    (ell_ratfunc_projective D : ℤ) -
      (ellV3 (k := Fq) (R := Polynomial Fq) (K := RatFunc Fq)
        (p1Canonical Fq - DivisorV3.ofAffine D) : ℤ) =
    D.deg + 1 - (p1Genus : ℤ)
```

The full Riemann-Roch formula for P¹ with:
- ℓ(D) = deg(D) + 1 for effective D with linear support
- ℓ(K-D) = 0 for effective D
- g = 0 (genus)

---

## Limitations

**This is NOT full P¹ Riemann-Roch.**

The `IsLinearPlaceSupport` hypothesis restricts to divisors supported at Fq-rational points:

```lean
def IsLinearPlaceSupport (D : DivisorV2 (Polynomial Fq)) : Prop :=
  ∀ v ∈ D.support, ∃ α : Fq, v = linearPlace α
```

Not covered:
- Places of degree > 1 (e.g., (X² + X + 1) over F₂)
- Divisors mixing linear and non-linear places

Full P¹ RR is mathematically trivial - the "vibe coding" methodology is more interesting than the result.

---

## Cycle 265 Progress

**Task**: Fill remaining sorry in `ell_ratfunc_projective_gap_eq`

**Status**: Ready to start

**Remaining Sorry** (1):
- Line 451: `gap_eq` - Dimension equality from surjectivity
  - Have: upper bound `gap ≤ deg(v)` and surjectivity of evaluation
  - Need: first isomorphism theorem argument to get `gap = deg(v)`

---

## Cycle 264 Summary

**Task**: Fill `evaluation = c` sorry in evaluationMapAt_surj

**Status**: ✅ Complete (2 → 1 sorries)

**Key Breakthrough**: Uniformizer-generator relationship lemmas

Added to PlaceDegree.lean:
- `uniformizerAt_mem_asIdeal` - uniformizer is in v.asIdeal (valuation < 1)
- `uniformizerAt_not_mem_asIdeal_sq` - not in v.asIdeal² (valuation exactly exp(-1))
- `generator_dvd_uniformizerAt` - generator divides uniformizer in k[X]
- `uniformizerQuotient` - defines w = uniformizerAt /ₘ generator
- `uniformizerAt_eq_generator_mul_quotient` - uniformizerAt = generator * w
- `uniformizerQuotient_not_mem_asIdeal` - w is coprime to generator
- `uniformizerQuotient_residue_ne_zero` - [w] ≠ 0 in κ(v)

**Core Fix**: Modified preimage construction in `evaluationMapAt_surj`:
- Original: lift c directly to q', use f = q'/gen^n
- Problem: eval(f) = [q'] * [w]^n ≠ c (wrong by factor [w]^n)
- Solution: lift c_adj = c * [w]^{-n} instead, then eval(f) = c_adj * [w]^n = c ✓

**Key Proof Steps**:
1. Use field structure: `letI : Field (k[X] ⧸ v.asIdeal) := Ideal.Quotient.field`
2. Compute w^{-n} in quotient field
3. Show shiftedElement(f) = algebraMap (q' * w^n) using `uniformizerAt_eq_generator_mul_quotient`
4. Apply `bridge_residue_algebraMap_clean` to get evaluation = [q' * w^n mod gen]
5. Simplify [q'] * [w]^n = c_adj * w_pow_n = c_quot via `mul_inv_cancel`
6. Finish with `LinearEquiv.apply_symm_apply`

---

## Cycle 263 Summary

**Task**: Prove `generator_intValuation_at_self` + `hf_affine`
**Status**: ✅ Complete (4 → 3 sorries)
**Key Discovery**: `HeightOneSpectrum.intValuation_singleton` directly gives valuation = exp(-1).

---

## Cycle 262 Summary

**Task**: Fix PlaceDegree.lean + skeleton for evaluationMapAt_surj
**Status**: ✅ Complete (5 → 4 sorries)
**Key discovery**: Abstract `uniformizerAt` can have extra prime factors in k[X].

---

## Sorries

**1 sorry total** in DimensionGeneral.lean:
- Line 451: `ell_ratfunc_projective_gap_eq` - dimension argument from surjectivity

**Abstract.lean**: 3 sorries (placeholder `AdelicRRData` instance fields - not blocking)

**Sorry-free files**:
- PlaceDegree.lean ✅ (includes new uniformizer-generator relationship lemmas)
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

### Immediate: Fill `ell_ratfunc_projective_gap_eq` (Line 451)

**Have**:
- `h_le := ell_ratfunc_projective_gap_le_general k D v` (upper bound: gap ≤ deg(v))
- `h_surj := evaluationMapAt_surj k v D hD` (evaluation map is surjective)

**Need**: Prove gap = deg(v) using first isomorphism theorem

**Strategy**:
1. Evaluation map φ : L(D+[v]) → κ(v) is surjective (h_surj)
2. ker(φ) = L(D) (from kernel_evaluationMapAt_complete_proof)
3. By first isomorphism: L(D+[v])/L(D) ≅ κ(v)
4. dim(κ(v)) = deg(v) (from finrank_residueField_eq_degree)
5. Therefore: ℓ(D+[v]) - ℓ(D) = deg(v)

**Key lemmas to use**:
- `kernel_evaluationMapAt_complete_proof` - ker = range(inclusion)
- `finrank_residueField_eq_degree` - dim(κ(v)) = deg(v)
- `LinearMap.quotKerEquivOfSurjective` or similar for iso

### Technical Context

The evaluation map machinery is now fully functional:
- `evaluationMapAt_complete` is an R-linear map L(D+[v]) → κ(v)
- Kernel = L(D) (via inclusion)
- Surjectivity proved via preimage construction with uniformizer adjustment

---

## Refactor Status

**Phase**: 0 (Cleanup) - mostly complete
**Next phase**: 1 (Complete incomplete infrastructure)

See `REFACTOR_PLAN.md` for full roadmap.

---

*For historical cycles 1-260, see `ledger_archive.md`*
