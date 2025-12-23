# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (4 sorries in DimensionGeneral.lean)
**Result**: Riemann-Roch for P¹ (linear places) + Generalized gap bound + Finiteness for all effective D
**Cycle**: 263 (Ready to Start)

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

## Cycle 263 Task

**Task**: Prove `generator_intValuation_at_self` + fill remaining evaluationMapAt_surj sorries

**Blocking Lemma**: Need to add to PlaceDegree.lean:
```lean
lemma generator_intValuation_at_self (v : HeightOneSpectrum (Polynomial k)) :
    v.intValuation (generator k v) = WithZero.exp (-1 : ℤ)
```

**Proof Strategy** (attempted but hit type issues):
1. Show `gen ∈ v.asIdeal` (trivial: gen generates the ideal)
2. Show `gen ∉ v.asIdeal²` (gen is irreducible, so gen² ∤ gen)
3. Use `intValuation_le_pow_iff_mem` to get bounds: `exp(-2) < val ≤ exp(-1)`
4. Use `intValuation_if_neg` to express val as `exp(-count)` for some ℕ
5. **Peel the type wrappers** to reduce to integer arithmetic:
   - `WithZero.exp` = `↑(Multiplicative.ofAdd _)`
   - Use `WithZero.coe_le_coe` / `coe_lt_coe` to strip WithZero
   - Use `Multiplicative.ofAdd_le` / `ofAdd_lt` to strip Multiplicative
   - Now have `-2 < -count ≤ -1` in ℤ, so `count = 1` by `omega`

**Type Hell Warning**: The `WithZero (Multiplicative ℤ)` type requires careful peeling.
Do NOT guess lemma names - search for actual usage in codebase (e.g., P1VanishingLKD.lean:181).

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

**7 sorries total** in non-archived code:
- `Abstract.lean`: 3 (placeholder `AdelicRRData` instance fields)
- `DimensionGeneral.lean`: 4 (see breakdown below)

**Files with sorries** (Cycle 263):
- DimensionGeneral.lean: ⚠️ 4 sorries
  - ~~Line 132: zero case~~ ✅ DONE (Cycle 262)
  - Line 153: hf_affine (valuation conditions for f = q/gen^n)
  - Line 157: hf_infty (no pole at infinity)
  - Line 167: evaluation equals c
  - Line 190: ell_ratfunc_projective_gap_eq (follows from surjectivity)

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

### Immediate: Prove `generator_intValuation_at_self` (Blocking)

**Add to PlaceDegree.lean** - This lemma is required for the remaining sorries.

**Proof outline** (90% done, needs type-peeling fixes):
```lean
lemma generator_intValuation_at_self (v : HeightOneSpectrum (Polynomial k)) :
    v.intValuation (generator k v) = WithZero.exp (-1 : ℤ) := by
  -- 1. gen ∈ v.asIdeal (trivial)
  have hgen_mem : generator k v ∈ v.asIdeal := ...
  -- 2. gen ∉ v.asIdeal² (irreducible ⟹ gen² ∤ gen)
  have hgen_not_mem_sq : generator k v ∉ v.asIdeal ^ 2 := ...
  -- 3. Get bounds via intValuation_le_pow_iff_mem
  have hle : v.intValuation (generator k v) ≤ WithZero.exp (-1) := ...
  have hgt : v.intValuation (generator k v) > WithZero.exp (-2) := ...
  -- 4. Express as exp(-count) via intValuation_if_neg
  have hval_form := v.intValuation_if_neg hgen_ne
  rw [hval_form] at hle hgt ⊢
  -- 5. Peel types: WithZero → Multiplicative → ℤ
  rw [WithZero.exp, WithZero.exp] at hle hgt
  simp only [WithZero.coe_le_coe, WithZero.coe_lt_coe] at hle hgt
  rw [Multiplicative.ofAdd_le] at hle
  rw [Multiplicative.ofAdd_lt] at hgt
  -- 6. Now -2 < -count ≤ -1, so count = 1
  have hcount_eq : count = 1 := by omega
  simp [hcount_eq]
```

**Key issue encountered**: The `mul_left_cancel₀` step for proving `gen ∉ v.asIdeal²` had
argument order problems. Need to carefully match `hc : gen² * c = gen` to the cancellation form.

### After generator_intValuation_at_self

Fill remaining 4 sorries in DimensionGeneral.lean:

1. **hf_affine** (line 153) - Now straightforward with generator valuation lemma
2. **hf_infty** (line 157) - Need deg(q) ≤ deg(gen^n) for no pole at infinity
3. **evaluation = c** (line 167) - Trace through residue field bridge
4. **gap_eq** (line 190) - Follows from surjectivity

### Key Technical Insight

**Abstract uniformizer vs generator**: The abstract `uniformizerAt v` is defined as ANY element
with v.intValuation = exp(-1). In k[X], this could be `gen * other_irreducible`, which belongs
to multiple prime ideals. Therefore:
- ❌ `uniformizerAt_not_mem_other_prime` is FALSE in general
- ✅ `generator_not_mem_other_prime` is TRUE (generator is monic irreducible)
- **Always use generator for coprimality arguments in k[X]**

---

## Refactor Status

**Phase**: 0 (Cleanup) - mostly complete
**Docs created**: `INVENTORY_REPORT.md`, `REFACTOR_PLAN.md`
**Next phase**: 1 (Complete incomplete infrastructure)

See `REFACTOR_PLAN.md` for full roadmap.

---

*For historical cycles 1-240, see `ledger_archive.md`*
