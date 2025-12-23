# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (2 sorries in DimensionGeneral.lean)
**Result**: Riemann-Roch for P¹ (linear places) + Generalized gap bound + Finiteness for all effective D
**Cycle**: 262 (In Progress)

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

## Cycle 262 Summary

**Task**: Fix PlaceDegree.lean + skeleton for evaluationMapAt_surj

**Status**: 🔄 In Progress

**Done**:
- PlaceDegree.lean ✅ sorry-free (removed unprovable uniformizer lemmas)
- evaluationMapAt_surj skeleton with 4 documented sorries

**Key discovery**: Abstract `uniformizerAt` can have extra prime factors in k[X], making
`uniformizerAt_not_mem_other_prime` unprovable. Use `generator` instead.

---

## Cycle 261 Summary

**Task**: Add coprimality lemmas for distinct primes

**Status**: ✅ Complete (generator lemmas), ❌ Uniformizer lemmas unprovable

**Proved**: `generator_not_mem_other_prime`, `generator_intValuation_at_other_prime`

---

## Cycle 260 Summary

**Task**: Fill finiteness instance in DimensionGeneral.lean
**Status**: ✅ Complete - `RRSpace_ratfunc_projective_effective_finite` proved
**Key technique**: Strong induction on degWeighted + `Module.Finite.of_submodule_quotient`

---

## Cycle 259 Summary

**Task**: Create DimensionGeneral.lean skeleton
**Status**: ✅ Complete - Main theorem structure with helper lemmas proved
**File**: `DimensionGeneral.lean` - proves `ℓ(D) = degWeighted(D) + 1` for effective D

---

## Cycle 258 Summary

**Task**: Generalize gap bound to arbitrary places
**Status**: ✅ Complete - `GapBoundGeneral.lean` sorry-free
**Result**: `ell_ratfunc_projective_gap_le_general`: gap ≤ deg(v) for any place v

**Key technique**: `Polynomial.Monic.finite_adjoinRoot` for quotient finiteness

---

## Cycle 257 Summary

**Task**: Create PlaceDegree.lean infrastructure
**Status**: ✅ Complete
**Key definitions**: `generator`, `degree`, `degWeighted`, `finrank_residueField_eq_degree`

---

## Cycle 256 Summary

**Task**: Assemble P1RiemannRoch.lean
**Status**: ✅ Complete - `riemann_roch_p1` sorry-free
**Result**: ℓ(D) - ℓ(K-D) = deg(D) + 1 - g for effective D with linear support

---

## Cycle 255 Summary

**Task**: Complete L(K-D) vanishing in P1VanishingLKD.lean
**Status**: ✅ Complete
**Key insight**: "v(f) ≤ 1 at all finite places ⟹ f is polynomial" via UFD factorization

---

## Cycle 254 Summary

**Task**: P1VanishingLKD.lean setup
**Key insight**: Mathlib infinity valuation: v_∞(p) = exp(deg(p)) (larger for higher degree!)

---

## Cycle 253 Summary

**Task**: P1Canonical.lean - define K = -2[∞] for P¹
**Key insight**: Canonical divisor for P¹ is entirely at infinity ("Affine Trap" bypass)

*For cycles 241-252, see `ledger_archive.md`.*

---

## Sorries

**8 sorries total** in non-archived code:
- `Abstract.lean`: 3 (placeholder `AdelicRRData` instance fields)
- `DimensionGeneral.lean`: 5 (see breakdown below)

**Files with sorries** (Cycle 262):
- DimensionGeneral.lean: ⚠️ 5 sorries
  - Line 132: zero case (q = 0 ⟹ c = 0)
  - Line 145: hf_affine (valuation conditions for f = q/gen^n)
  - Line 149: hf_infty (no pole at infinity)
  - Line 159: evaluation equals c
  - Line 182: ell_ratfunc_projective_gap_eq (follows from surjectivity)

**Sorry-free files** (confirmed Cycle 262):
- PlaceDegree.lean ✅ (Cycle 262 - removed unprovable uniformizer lemmas)
- GapBoundGeneral.lean ✅ (Generalized gap bound)
- P1RiemannRoch.lean ✅ (Full Riemann-Roch theorem)
- P1VanishingLKD.lean ✅
- DimensionCore.lean ✅
- AdelicH1Full.lean ✅
- DimensionScratch.lean ✅
- Place.lean ✅
- DivisorV3.lean ✅
- RRSpaceV3.lean ✅
- P1Place.lean ✅
- P1Canonical.lean ✅
- All other SerreDuality files ✅

6 dead-code lemmas in `RrLean/Archive/SorriedLemmas.lean`.

---

## Build Commands

```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "depends on axioms"
```

**See also**: `state/PROOF_CHAIN.md` for the full import chain and verification details.

---

## Next Steps

### Immediate: Fill `evaluationMapAt_surj` Sorries

**Skeleton complete** - 4 sorries remain in the main proof:

1. **hf_affine** (line 145) - Valuation conditions for f = q/gen^n
   ```
   At v: v(f) = v(q) - n*v(gen) = 1 - n*exp(-1) = exp(n) ≤ exp(D(v)+1) ✓
   At w ≠ v: w(f) = w(q)/w(gen)^n ≤ 1/1 = 1 ≤ exp(D(w)) ✓
   ```
   Key lemmas: `generator_intValuation_at_other_prime`, `intValuation_le_one`

2. **hf_infty** (line 149) - No pole at infinity
   - f = q/gen^n where deg(q) can be arbitrary, deg(gen^n) = n*deg(gen)
   - Need: deg(numerator) ≤ deg(denominator) for effective D
   - This may require choosing q with deg(q) < deg(gen) (modular reduction)

3. **evaluation = c** (line 159) - Trace through shiftedElement
   - f * π^n = (q/gen^n) * π^n = q * (π/gen)^n
   - π and gen are associates: π = u*gen for some unit u in localization
   - Residue of q*u^n should give [q] = c

4. **zero case** (line 132) - Trivial: q=0 ⟹ c=0, eval(0)=0

### Key Technical Insight

**Abstract uniformizer vs generator**: The abstract `uniformizerAt v` is defined as ANY element
with v.intValuation = exp(-1). In k[X], this could be `gen * other_irreducible`, which belongs
to multiple prime ideals. Therefore:
- ❌ `uniformizerAt_not_mem_other_prime` is FALSE in general
- ✅ `generator_not_mem_other_prime` is TRUE (generator is monic irreducible)
- **Always use generator for coprimality arguments in k[X]**

### After Surjectivity

1. `ell_ratfunc_projective_gap_eq` follows from surjectivity + kernel characterization
2. Update `riemann_roch_p1` to use `degWeighted` instead of `deg`
3. Remove `IsLinearPlaceSupport` restriction from main theorem

---

## Refactor Status

**Phase**: 0 (Cleanup) - mostly complete
**Docs created**: `INVENTORY_REPORT.md`, `REFACTOR_PLAN.md`
**Next phase**: 1 (Complete incomplete infrastructure)

See `REFACTOR_PLAN.md` for full roadmap.

---

*For historical cycles 1-240, see `ledger_archive.md`*
