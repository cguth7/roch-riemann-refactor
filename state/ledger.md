# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (2 sorries in DimensionGeneral.lean)
**Result**: Riemann-Roch for P¹ (linear places) + Generalized gap bound + Finiteness for all effective D
**Cycle**: 264 (In Progress)

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

## Cycle 264 Progress

**Task**: Fill `hf_infty` sorry in evaluationMapAt_surj

**Status**: ✅ Complete (3 → 2 sorries)

**Completed**:
1. ✅ `hf_infty` - PROVED! (noPoleAtInfinity for f = q'/gen^n)
   - Key insight: Use `q' = q %ₘ gen` (modByMonic) instead of original `q`
   - Then `deg(q') < deg(gen) ≤ deg(gen^n)` for n ≥ 1
   - This gives `intDegree(f) = deg(q') - deg(gen^n) < 0`, hence `noPoleAtInfinity f`
   - Added proof that `q'` and `q` give same element in κ(v) (since `q - q' ∈ ⟨gen⟩`)

**Remaining Sorries** (2):
- Line 307: `evaluation = c` - Trace evaluation through residue field bridge
- Line 330: `gap_eq` - Dimension equality from surjectivity

**Technical details**:
- `Polynomial.natDegree_modByMonic_lt` gives `q'.natDegree < gen.natDegree`
- `RatFunc.intDegree_polynomial`, `RatFunc.intDegree_mul`, `RatFunc.intDegree_inv` for intDegree computation
- `noPoleAtInfinity_iff_intDegree_le_zero` to convert condition

---

## Cycle 263 Summary

**Task**: Prove `generator_intValuation_at_self` + `hf_affine`

**Status**: ✅ Complete (4 → 3 sorries)

**Completed**:
1. ✅ `generator_intValuation_at_self` - PROVED using Mathlib's `intValuation_singleton`
2. ✅ `hf_affine` - PROVED (valuation bounds for f = q/gen^n at all finite places)

**Key Discovery**: `HeightOneSpectrum.intValuation_singleton` directly gives valuation = exp(-1).

---

## Cycle 262 Summary

**Task**: Fix PlaceDegree.lean + skeleton for evaluationMapAt_surj

**Status**: ✅ Complete (5 → 4 sorries)

**Done**:
- PlaceDegree.lean ✅ sorry-free (removed unprovable uniformizer lemmas)
- evaluationMapAt_surj skeleton with documented sorries
- **Zero case filled** (line 132): q=0 ⟹ c=0, eval(0)=0 ✅

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

**5 sorries total** in non-archived code:
- `Abstract.lean`: 3 (placeholder `AdelicRRData` instance fields)
- `DimensionGeneral.lean`: 2 (see breakdown below)

**Files with sorries** (Cycle 264):
- DimensionGeneral.lean: ⚠️ 2 sorries
  - ~~Line 132: zero case~~ ✅ DONE (Cycle 262)
  - ~~Line 153: hf_affine~~ ✅ DONE (Cycle 263)
  - ~~Line 226: hf_infty~~ ✅ DONE (Cycle 264) - used modByMonic
  - Line 307: evaluation equals c (residue field bridge)
  - Line 330: ell_ratfunc_projective_gap_eq (follows from surjectivity)

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

### Immediate: Fill remaining 2 sorries in DimensionGeneral.lean

**Remaining sorries**:

1. ~~**hf_infty** (Line 226)~~ ✅ DONE (Cycle 264) - Used modByMonic approach

2. **evaluation = c** (Line 307) - Complex residue field mechanics
   - Need to trace: `f ↦ shiftedElement(f) → residue → bridge → c`
   - f = q'_K / gen_K^n where q' = q %ₘ gen
   - shiftedElement multiplies by uniformizer^{D(v)+1}
   - Key insight: uniformizer and generator both have v-valuation exp(-1)
   - May need lemma showing `uniformizerAt v` and `generator k v` differ by unit in valuation ring

3. **gap_eq** (Line 330) - Standard dimension argument
   - Surjectivity of ψ implies quotient ≅ κ(v)
   - Use first isomorphism theorem: L(D+v)/ker(ψ) ≅ im(ψ) = κ(v)
   - Combined with kernel = L(D) gives dim(quotient) = deg(v)

### Key Technical Insight (Confirmed)

**Abstract uniformizer vs generator**: The abstract `uniformizerAt v` is defined as ANY element
with v.intValuation = exp(-1). In k[X], this could be `gen * other_irreducible`, which belongs
to multiple prime ideals. Therefore:
- ❌ `uniformizerAt_not_mem_other_prime` is FALSE in general
- ✅ `generator_not_mem_other_prime` is TRUE (generator is monic irreducible)
- **Always use generator for coprimality arguments in k[X]**

### Mathlib Lemma Discovery

`HeightOneSpectrum.intValuation_singleton` provides a direct path to proving generator valuations:
```lean
theorem intValuation_singleton {r : R} (hr : r ≠ 0) (hv : v.asIdeal = Ideal.span {r}) :
    v.intValuation r = exp (-1 : ℤ)
```
No type-peeling through `WithZero (Multiplicative ℤ)` needed!

---

## Refactor Status

**Phase**: 0 (Cleanup) - mostly complete
**Docs created**: `INVENTORY_REPORT.md`, `REFACTOR_PLAN.md`
**Next phase**: 1 (Complete incomplete infrastructure)

See `REFACTOR_PLAN.md` for full roadmap.

---

*For historical cycles 1-240, see `ledger_archive.md`*
