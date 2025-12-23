# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (0 sorries in main path)
**Result**: Restricted P¹ Riemann-Roch (linear places only)
**Cycle**: 254

---

## What's Proved

```lean
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective D = D.deg.toNat + 1
```

For effective divisors D with **linear support only**, dim L(D) = deg(D) + 1.

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

## Cycle 254 Summary

**Task**: Prove L(K-D) vanishing for effective D on P¹

**New File**: `RrLean/RiemannRochV2/P1Instance/P1VanishingLKD.lean`

**Key insight**: For P¹, the Mathlib convention for infinity valuation is:
```lean
v_∞(p) = exp(deg(p)) for nonzero polynomial p
```
This means higher degree polynomials have LARGER valuations at infinity, not smaller.

**Key lemmas**:
```lean
lemma p1InftyValuation_polynomial (p : Polynomial Fq) (hp : p ≠ 0) :
    (p1InftyPlace Fq).valuation (algebraMap (Polynomial Fq) (RatFunc Fq) p) =
    WithZero.exp (p.natDegree : ℤ)

lemma p1InftyValuation_polynomial_not_le_exp_neg2 (p : Polynomial Fq) (hp : p ≠ 0) :
    ¬ (p1InftyPlace Fq).valuation (algebraMap (Polynomial Fq) (RatFunc Fq) p) ≤
      WithZero.exp (-2 : ℤ)
```

**Main theorem structure** (1 sorry remaining):
```lean
theorem RRSpaceV3_p1Canonical_sub_ofAffine_eq_zero
    {D : DivisorV2 (Polynomial Fq)} (hD : D.Effective) :
    RRSpaceV3 (Polynomial Fq) (RatFunc Fq) (p1Canonical Fq - DivisorV3.ofAffine D) = {0}
```

The remaining sorry needs to show that elements with no finite poles are polynomials,
which then contradicts the infinity condition v_∞(f) ≤ exp(-2).

**Verification**:
```bash
lake build RrLean.RiemannRochV2.P1Instance.P1VanishingLKD  # ✅
lake build RrLean.RiemannRochV2.SerreDuality.Smoke  # ✅ Still passes
```

---

## Cycle 253 Summary (Previous)

**Task**: Define the canonical divisor K = -2[∞] for P¹

**New File**: `RrLean/RiemannRochV2/P1Instance/P1Canonical.lean`

**Key definitions**:
```lean
/-- The canonical divisor on P¹ = RatFunc Fq. K = -2[∞]. -/
def p1Canonical : DivisorV3 Fq[X] (RatFunc Fq) :=
  DivisorV3.singleInfinite (p1InftyPlace Fq) (-2)

/-- The genus of P¹ is 0. -/
def p1Genus : ℕ := 0
```

**Key lemmas**:
- `deg_p1Canonical` : degree is -2
- `p1Canonical_at_infty` : coefficient at ∞ is -2
- `p1Canonical_at_finite` : coefficient at finite places is 0
- `p1_genus_formula` : deg(K) = 2g - 2 holds for P¹
- `deg_p1Canonical_sub` : deg(K - D) = -2 - deg(D)
- `deg_p1Canonical_sub_neg` : if deg(D) ≥ -1, then deg(K - D) ≤ -1

**Insight**: The canonical divisor for P¹ arises entirely from the place at infinity.
Mathlib's `differentIdeal` machinery only captures finite places (the "Affine Trap"),
so there's no useful connection for P¹. For P¹, we define K = -2[∞] directly.

**Verification**:
```bash
lake build RrLean.RiemannRochV2.P1Instance.P1Canonical  # ✅
lake build RrLean.RiemannRochV2.SerreDuality.Smoke  # ✅ Still passes
```

---

## Cycle 252 Summary (Previous)

**Task**: Connect P¹ to Place infrastructure with inftyPlace and ConstantsValuationBound

**New File**: `RrLean/RiemannRochV2/P1Instance/P1Place.lean`

**Changes**:

1. **RRSpaceV3.lean refactored**: Changed `satisfiesValuationConditionV3` and `ConstantsValuationBound`
   to only check registered infinite places (from `HasInfinitePlaces.infinitePlaces`).
   This is more mathematically correct - arbitrary `InfinitePlace K` values don't correspond
   to real places on the curve.

2. **P1Place.lean created**: Connects P¹ = RatFunc Fq to the Place infrastructure:
   - `p1InftyPlace Fq` - The unique infinite place using `FunctionField.inftyValuationDef`
   - `instHasInfinitePlacesP1` - P¹ has exactly one infinite place (degree 1)
   - `instConstantsValuationBoundP1` - Constants from Fq have valuation ≤ 1 at all places

**Key definitions**:
```lean
def p1InftyPlace : InfinitePlace (RatFunc Fq) where
  val := (FunctionField.inftyValuedFqt Fq).v
  deg := 1
  deg_pos := Nat.one_pos

instance instHasInfinitePlacesP1 : HasInfinitePlaces Fq[X] (RatFunc Fq)
instance instConstantsValuationBoundP1 : ConstantsValuationBound Fq Fq[X] (RatFunc Fq)
```

**Architectural improvement**: The original `ConstantsValuationBound` required valuation bounds
for ALL `InfinitePlace K` values, which is unprovable since `InfinitePlace` can contain
arbitrary valuations. The refactored version only requires bounds for places in
`HasInfinitePlaces.infinitePlaces`, making it provable and mathematically correct.

**Verification**:
```bash
lake build RrLean.RiemannRochV2.P1Instance.P1Place  # ✅
lake build RrLean.RiemannRochV2.SerreDuality.Smoke  # ✅ Still passes
```

---

## Cycle 251 Summary (Previous)

**Task**: Create `RRSpaceV3.lean` - projective Riemann-Roch space using DivisorV3

**New File**: `RrLean/RiemannRochV2/Core/RRSpaceV3.lean`

Created the projective L(D) for divisors that include both finite and infinite places:

```lean
/-- Membership condition for L(D) using all places. -/
def satisfiesValuationConditionV3 (D : DivisorV3 R K) (f : K) : Prop :=
  f = 0 ∨ ∀ p : Place R K, p.valuation f ≤ WithZero.exp (D p)

/-- L(D) as a submodule over base field k. -/
def RRModuleV3 [ConstantsValuationBound k R K] (D : DivisorV3 R K) : Submodule k K
```

**Key definitions**:
- `satisfiesValuationConditionV3`: Membership condition for projective L(D)
- `RRSpaceV3`: The carrier set {f ∈ K : f ∈ L(D)}
- `ConstantsValuationBound`: Typeclass for base fields where constants have valuation ≤ 1
- `RRModuleV3`: L(D) as Submodule k K (over base field, not coordinate ring)
- `ellV3_extended`, `ellV3`: Dimension ℓ(D) as ℕ∞ and ℕ
- `satisfiesValuationConditionV3_of_affine`: Connection to affine L(D)

**Key insight**: The projective L(D) must be a `Submodule k K` (over base field k),
not `Submodule R K` (over coordinate ring R), because elements of R may have
valuation > 1 at infinite places.

**Verification**:
```bash
lake build RrLean.RiemannRochV2.Core.RRSpaceV3  # ✅
lake build RrLean.RiemannRochV2.SerreDuality.Smoke  # ✅ Still passes
```

---

## Cycle 250 Summary (Previous)

**Task**: Create `DivisorV3.lean` - projective divisors using unified Place type

**New File**: `RrLean/RiemannRochV2/Core/DivisorV3.lean`

Created projective divisors that include both finite and infinite places:

```lean
/-- A projective divisor on a curve is a finitely supported function from all places to ℤ. -/
abbrev DivisorV3 := Place R K →₀ ℤ
```

**Key definitions**:
- `DivisorV3.deg`: Degree (sum of all coefficients)
- `DivisorV3.degFinite`: Degree contribution from finite places
- `DivisorV3.degInfinite`: Degree contribution from infinite places
- `DivisorV3.Effective`: Non-negative divisors
- `DivisorV3.ofAffine`: Embedding from DivisorV2 (affine) to DivisorV3 (projective)
- `DivisorV3.singleFinite`, `DivisorV3.singleInfinite`: Single-place divisors

**Key lemmas**:
- `deg_eq_degFinite_add_degInfinite`: Total degree = finite + infinite contributions
- `finiteFilter_add_infiniteFilter`: Divisor = finiteFilter + infiniteFilter
- `deg_ofAffine`: Embedding preserves degree
- `ofAffine_effective`: Embedding preserves effectivity

**Verification**:
```bash
lake build RrLean.RiemannRochV2.Core.DivisorV3  # ✅
lake build RrLean.RiemannRochV2.SerreDuality.Smoke  # ✅ Still passes
```

---

## Cycle 249 Summary (Previous)

**Task**: Create `Place.lean` - unified Place type for Phase 3

**New File**: `RrLean/RiemannRochV2/Core/Place.lean`

Created the foundational type for projective Riemann-Roch:

```lean
/-- An infinite place on a function field K. -/
structure InfinitePlace (K : Type*) [Field K] where
  val : Valuation K (WithZero (Multiplicative ℤ))
  deg : ℕ
  deg_pos : 0 < deg

/-- A place on a curve is either finite or infinite. -/
inductive Place (R : Type*) (K : Type*) ...
  | finite : HeightOneSpectrum R → Place R K
  | infinite : InfinitePlace K → Place R K
```

**Key definitions**:
- `Place.valuation`: Dispatches to finite or infinite valuation
- `Place.isFinite`, `Place.isInfinite`: Classification predicates
- `HasInfinitePlaces`: Typeclass for curves with infinite places
- `HasInfinitePlaces.allPlaces`: Combined finite + infinite places

---

## Cycle 248 Summary (Previous)

**Task**: Investigate Abstract.lean sorries and plan next steps

**Key Discovery**: The Abstract.lean "sorries" are in a **docstring template**, not actual code.

**CRITICAL CORRECTION** (from Gemini review):

The current `AdelicRRData` framework is **broken for ALL projective curves**, not just P¹:

| Curve Type | Coordinate Ring R | Missing Place(s) |
|------------|-------------------|------------------|
| P¹ | k[t] | ∞ |
| Elliptic | k[x,y]/(y²-x³-ax-b) | Point O at infinity |
| Hyperelliptic | k[x,y]/(y²-f(x)) | 1-2 points at infinity |

**The Affine Trap**: Any Dedekind domain R models the AFFINE part of a curve.
`HeightOneSpectrum R` = finite places only. The framework currently computes
**Affine Riemann-Roch**, not Projective Riemann-Roch.

**Implication**: Abstract.lean sorries CANNOT be filled for any projective curve
until Phase 3 (Place type) is complete. Phase 3 is not optional cleanup - it's
required infrastructure for the general framework to work.

**Changes**:
- Corrected understanding of Affine vs Projective framework
- Phase 3 is now immediate priority
- Build remains clean (0 sorryAx)

---

## Cycle 247 Summary (Previous)

**Task**: Fill `RRSpace_proj_ext` degree sorries in AdelicH1Full.lean

**Changes**:
1. Fixed `add_mem'` degree bound proof:
   - Used `by_cases` on `a = 0` and `b = 0` to handle zero cases explicitly
   - Applied `RatFunc.intDegree_add_le` for the non-zero case
   - Converted between `num.natDegree ≤ denom.natDegree + n` and `intDegree ≤ n`

2. Fixed `smul_mem'` degree bound proof:
   - Used `by_cases hf_zero : f = 0` to handle zero case
   - Applied `RatFunc.intDegree_mul` and `RatFunc.intDegree_C` (which equals 0)
   - Used `map_eq_zero` instead of non-existent `RatFunc.C_eq_zero`

**Sorries remaining in RRSpace_proj_ext**: 0

**Verification**:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "error\|sorryAx"
# No output = main path still sorry-free
grep -n "sorry" RrLean/RiemannRochV2/SerreDuality/General/AdelicH1Full.lean
# No output = AdelicH1Full.lean is sorry-free
```

---

## Cycle 246 Summary (Previous)

**Task**: Fix `RRSpace_proj_ext` definition in AdelicH1Full.lean

**Problem Found**: The carrier definition had two bugs:
1. **Wrong inequality direction**: `exp(D(v)) ≤ v(f)` instead of `v(f) ≤ exp(D(v))`
   - The original was NOT closed under addition (pole cancellation breaks it)
   - Fixed to match `RRModuleV2_real` pattern
2. **Missing zero handling**: Needed `f = 0 ∨ ...` pattern since v(0) = 0 is bottom element

**Changes**:
1. Fixed carrier to: `f = 0 ∨ ((∀ v, v(f) ≤ exp(D(v))) ∧ degree bound)`
2. Proved `zero_mem'`: Now trivial via `Or.inl rfl`
3. Proved `add_mem'` valuation: Uses ultrametric `Valuation.map_add_le_max'`
4. Proved `smul_mem'` valuation: Uses `IsScalarTower.algebraMap_apply` + `valuation_le_one`
5. Degree proofs left as sorry (2 sorries) - need careful intDegree ↔ natDegree conversion

**Verification**:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "error\|sorryAx"
# No output = main path still sorry-free
```

---

## Cycle 245 Summary (Previous)

**Task**: Complete SerreDuality reorganization - General/ subfolder + archive

**Changes**:
1. Created `SerreDuality/General/` subfolder for curve-agnostic infrastructure
2. Moved `Abstract.lean` → `General/` (abstract Serre pairing)
3. Moved `AdelicH1Full.lean` → `General/` (full adele H¹)
4. Moved `DimensionCore.lean` → `P1Specific/` (P¹ finiteness proofs)
5. Archived `IntDegreeTest.lean` → `Archive/`
6. Updated imports in `SerreDuality.lean`, `Smoke.lean`, `DimensionScratch.lean`

**Final SerreDuality structure**:
```
SerreDuality/
├── General/
│   ├── Abstract.lean        # Abstract Serre pairing
│   └── AdelicH1Full.lean    # Full adele H¹(D)
├── P1Specific/
│   ├── DimensionCore.lean   # Finiteness for L(n·[α])
│   ├── DimensionScratch.lean
│   ├── RatFuncFullRR.lean
│   └── RatFuncPairing.lean
├── RatFuncResidues.lean
└── Smoke.lean
```

**Verification**:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "error\|sorryAx"
# No output = success
```

---

## Cycle 244 Summary (Previous)

**Task**: Major reorganization - group files into subfolders

**New structure**:
```
RrLean/RiemannRochV2/
├── Core/           # Basic, Divisor, RRSpace, Typeclasses
├── Adelic/         # Adeles, AdelicH1v2, AdelicTopology, FullAdeles*
├── Definitions/    # RRDefinitions, Infrastructure, Projective, FullRRData
├── Dimension/      # DimensionCounting, KernelProof, RiemannInequality
├── ResidueTheory/  # Residue, ResidueFieldIso, DifferentIdealBridge
├── Support/        # DedekindDVR, AllIntegersCompactProof, TraceDualityProof
├── P1Instance/     # P1Instance, ProductFormula, FqPolynomialInstance
└── SerreDuality/   # (already organized with P1Specific/)
```

**Files moved**: 28 files → 7 subfolders
**Imports updated**: All references across codebase

---

## Cycle 243 Summary (Previous)

**Task**: Fill scalar mult sorries in `AdelicH1Full.lean`

**File**: `RrLean/RiemannRochV2/SerreDuality/General/AdelicH1Full.lean`

**Sorries fixed**:
1. `smul_mem_boundedSubset_full` (lines 230, 234) - Scalar mult preserves bounded adeles
   - Finite part: Used scalar tower to show `(c • a).1 = c • a.1`, then applied existing lemma
   - Infinity part: Used `diag_infty_valuation` + `FunctionField.inftyValuation.C` for constants
2. `smul_mem_globalSubset_full` (line 276) - Scalar mult preserves diagonal embedding
   - Used `map_mul` for ring homomorphism `fqFullDiagonalEmbedding`

**Sorries remaining** (in `RRSpace_proj_ext` - lower priority):
- 5 sorries for Riemann-Roch space with infinity constraint

**Verification**:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
# No output = main path still sorry-free
```

---

## Cycle 242 Summary (Previous)

**Task**: Reorganize SerreDuality folder - create P1Specific subfolder

**Changes**:
1. Created `RrLean/RiemannRochV2/SerreDuality/P1Specific/` directory
2. Moved `RatFuncPairing.lean` → `P1Specific/`
3. Moved `DimensionScratch.lean` → `P1Specific/`
4. Moved `RatFuncFullRR.lean` → `P1Specific/`
5. Updated imports in all affected files (5 files total)

---

## Cycle 241 Summary (Previous)

**Fixes applied**:
1. `add_le_add_left` → `linarith` with explicit sum non-negativity
2. Added `simp only [Finsupp.sum]` to unfold Finsupp.sum
3. Replaced circular proof with direct calc-based proof
4. Moved 6 dead-code sorried lemmas to Archive
5. Eliminated last sorry by adding `1 ≤ bound` hypothesis

---

## Sorries

**4 sorries total** in non-archived code:
- `Abstract.lean`: 3 (placeholder `AdelicRRData` instance fields)
- `P1VanishingLKD.lean`: 1 (polynomial characterization for vanishing proof)

**Sorry-free files** (confirmed Cycle 254):
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

### Immediate: Complete L(K-D) Vanishing Proof

**Cycle 254 complete**: Infrastructure for L(K-D) vanishing created.

**Cycle 255**: Fill the remaining sorry in `P1VanishingLKD.lean`
- Need to prove: "elements with v(f) ≤ 1 at all finite places are polynomials"
- This is a characterization of the image of Polynomial Fq → RatFunc Fq
- Once proven, the contradiction v_∞(polynomial) ≥ 1 > exp(-2) completes the proof

**Key Mathlib API to investigate**:
- `RatFunc.num_div_denom` - representation as num/denom
- `HeightOneSpectrum.valuation_le_one` - elements in valuation ring
- Localization properties for Dedekind domains

**Context**: Completing this proof gives ℓ(K-D) = 0 for effective D on P¹,
which is the last ingredient for Riemann-Roch via Serre duality.

**After Phase 3**: Abstract.lean sorries become fillable for all projective curves.

---

## Refactor Status

**Phase**: 0 (Cleanup) - mostly complete
**Docs created**: `INVENTORY_REPORT.md`, `REFACTOR_PLAN.md`
**Next phase**: 1 (Complete incomplete infrastructure)

See `REFACTOR_PLAN.md` for full roadmap.

---

*For historical cycles 1-240, see `ledger_archive.md`*
