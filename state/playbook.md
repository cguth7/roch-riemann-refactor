# Playbook (Curator maintained)

## Ultimate Goal: Riemann-Roch Theorem

**IMPORTANT CONTEXT FOR ALL LOOPS**: The current target (`LocalGapBound R K`) is a milestone, NOT the final goal.

The **ultimate objective** is a complete formalization of the **Riemann-Roch theorem** for algebraic curves/function fields in Lean 4:
```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

Where:
- `ℓ(D)` = dimension of the Riemann-Roch space L(D)
- `K` = canonical divisor
- `g` = genus of the curve/function field
- `deg(D)` = degree of divisor D

**Current Phase**: We're proving the **Riemann inequality** (`ℓ(D) ≤ deg(D) + 1 - g` or affine variant) as a stepping stone. This requires:
1. ✅ `riemann_inequality_affine` theorem (PROVED, but needs `LocalGapBound` instance)
2. ⚠️ `LocalGapBound R K` instance (CURRENT TARGET)
3. 🔮 Full Riemann-Roch with canonical divisor and genus (FUTURE)

**Why this matters for decision-making**:
- When choosing between approaches, prefer ones that generalize to the full RR theorem
- The residue field / evaluation map machinery will be reused for the canonical divisor construction
- Keep an eye on how genus `g` will eventually be defined (likely via differentials or Serre duality)

---

## Heuristics

### General
- Prefer line-bundle / invertible-sheaf RR statements; divisor RR is a wrapper.
- Use `finrank k` for dimensions; avoid `Nat`-based dims until the end.
- Keep lemma statements small: fewer binders, fewer coercions, fewer implicit arguments.
- When stuck on coercions, introduce explicit `let` bindings for objects (e.g. `L : LineBundle X`).

### Lean Formalization Discipline (Added Cycle 33)

**Archaeology-First Rule**: Before writing a new proof, spend 15+ min searching mathlib for existing lemmas. The "obvious math" often already exists under a different name. Search patterns:
- `*_iff_*` for characterizations
- `exists_*` for existence lemmas
- Check the specific module's API (e.g., `ValuationSubring`, `IsLocalization`, `IsFractionRing`)

**Frontier Freeze Rule**: Don't add new sorry candidates while a key blocker is stuck. Sorry count creeping up (19→25) without the hard lemma moving is a warning sign. Keep pressure on the actual blocker.

**DVR/Valuation Anti-Pattern**: Avoid constructing uniformizers manually. The moment you say "find π with v(π)=...", you're signing up for `Associates`, `Irreducible`, `UniqueFactorizationMonoid` instance juggling. Instead:
- Use localization universal properties
- Work inside the DVR/localization where API is cleanest, then transport
- Look for `exists_lift_of_le_one` patterns in mathlib

**Reframing Rule**: If a "converse" lemma is hard, check if there's a higher-level equivalence that gives both directions for free (e.g., ring isomorphism instead of set equality).

---

## Current Status (Cycle 71 - Kernel Proofs Complete!)

**Codebase Structure**:
```
RrLean/RiemannRochV2/
├── Basic.lean              # Imports ✅
├── Divisor.lean            # DivisorV2 ✅
├── RRSpace.lean            # L(D), ℓ(D) ✅ (1 sorry placeholder)
├── Typeclasses.lean        # LocalGapBound ✅
├── RiemannInequality.lean  # Main theorems ✅ (1 sorry placeholder)
├── Infrastructure.lean     # Residue, uniformizer ✅ **CLEAN** (0 sorries!)
├── LocalGapInstance.lean   # Cycles 25-65 (3344 lines, 90s build) ✅
├── KernelProof.lean        # Cycles 66-71 (590 lines) ✅ **KEY PROOFS COMPLETE!**
└── TestBlockerProofs.lean  # Cycle 58-60: Test proofs
```

**Active Development**: `KernelProof.lean` - KEY LEMMAS NOW PROVED!

### Key Achievement (Cycle 71)

**ALL THREE KERNEL LEMMAS PROVED!** The kernel characterization is now complete:

1. **`LD_element_maps_to_zero`** ✅ - Forward direction: L(D) ⊆ ker
2. **`kernel_element_satisfies_all_bounds`** ✅ - Backward direction: ker ⊆ L(D)
3. **`kernel_evaluationMapAt_complete_proof`** ✅ - Full characterization: ker = L(D)

**Technical highlights**:
- Used `erw [IsLocalRing.residue_eq_zero_iff]` to handle definitional mismatch between `valuationRingAt` and `(v.valuation K).valuationSubring`
- Used `unfold valuationRingAt` before `Valuation.mem_maximalIdeal_iff` rewrites
- Bridge injectivity via `RingEquiv.injective` for backward direction

### Typeclass Hierarchy
```
LocalGapBound R K          -- PROVABLE (gap ≤ 1 via evaluation map)
    ↑ extends
SinglePointBound R K       -- PROJECTIVE (adds ell_zero = 1)

BaseDim R K                -- SEPARATE (explicit base dimension)
```

### Key Blockers (Updated Cycle 71 - ALL RESOLVED!)

| Name | Status | Notes |
|------|--------|-------|
| `evaluationMapAt_complete` | ✅ **PROVED** | Cycle 56: LinearMap bundle complete |
| `bridge_residue_algebraMap_clean` | ✅ **PROVED** | Cycle 65: CLEAN BRIDGE PROVED |
| `uniformizerAt_zpow_valuation` | ✅ **PROVED** | Cycle 70: zpow version |
| `extract_valuation_bound_zpow` | ✅ **PROVED** | Cycle 70: Unified extraction |
| `LD_element_maps_to_zero` | ✅ **PROVED** | Cycle 71: Forward direction complete! |
| `kernel_element_satisfies_all_bounds` | ✅ **PROVED** | Cycle 71: Backward direction complete! |
| `kernel_evaluationMapAt_complete_proof` | ✅ **PROVED** | Cycle 71: ker(eval) = L(D) PROVED! |

### Next Cycle (72) Instructions - LocalGapBound Instance

**Goal**: Prove `instance : LocalGapBound R K` using rank-nullity theorem.

**Setup**:
1. Create new file `RrLean/RiemannRochV2/DimensionCounting.lean` to avoid 90s compile time of LocalGapInstance
2. Import `RrLean.RiemannRochV2.KernelProof` and `Mathlib.LinearAlgebra.Dimension`

**Proof Strategy**:
1. Define φ : L(D+v) → κ(v) as `evaluationMapAt_complete v D` (already exists!)
2. Apply **Rank-Nullity**: `LinearMap.finrank_range_add_finrank_ker φ`
   - This gives: `dim(L(D+v)) = dim(ker φ) + dim(image φ)`
3. Use `kernel_evaluationMapAt_complete_proof` to show: `ker φ = range(inclusion from L(D))`
   - Since inclusion is injective: `dim(ker φ) = dim(L(D))`
4. Use that κ(v) is 1-dimensional: `dim(image φ) ≤ 1`
5. Conclude: `dim(L(D+v)) ≤ dim(L(D)) + 1` ✓

**Key Mathlib lemmas to use**:
- `LinearMap.finrank_range_add_finrank_ker` - Rank-Nullity
- `LinearMap.finrank_range_of_inj` - dim(range) = dim(domain) for injective map
- `Submodule.inclusion_injective` - inclusion is injective

**LocalGapBound typeclass** (check `Typeclasses.lean` for exact field name):
```lean
instance : LocalGapBound R K where
  gap_le_one := fun v D => <the dimension inequality proof>
```

**Victory**: Once this instance is proved, `riemann_inequality_affine` becomes unconditional!

### Cycle 71 Technical Notes (Kernel Proofs)
- **`erw` for definitional mismatches**: `erw [IsLocalRing.residue_eq_zero_iff]` sees through `valuationRingAt v` = `(v.valuation K).valuationSubring`
- **`unfold valuationRingAt`**: Required before `Valuation.mem_maximalIdeal_iff` rewrites
- **Bridge injectivity**: `RingEquiv.injective` + `map_zero` for backward direction
- **Strict bound for forward**: f ∈ L(D) gives v(f) ≤ exp(D v), so v(shiftedElement) ≤ exp(-1) < 1

---

## Victory Path (Updated Cycle 71 - KERNEL COMPLETE!)

```
evaluationMapAt_complete (Cycle 56 - PROVED ✅)  ← LINEARMAP COMPLETE!
    ↓
bridge_residue_algebraMap_clean (Cycle 65 - PROVED ✅)  ← CLEAN BRIDGE PROVED!
    ↓
uniformizerAt_zpow_valuation (Cycle 70 - PROVED ✅)  ← ZPOW INFRASTRUCTURE!
    ↓
extract_valuation_bound_zpow (Cycle 70 - PROVED ✅)  ← UNIFIED EXTRACTION!
    ↓
LD_element_maps_to_zero (Cycle 71 - PROVED ✅)  ← FORWARD DIRECTION!
    ↓
kernel_element_satisfies_all_bounds (Cycle 71 - PROVED ✅)  ← BACKWARD DIRECTION!
    ↓
kernel_evaluationMapAt_complete (Cycle 71 - PROVED ✅)  ← KERNEL = L(D)!
    ↓
LocalGapBound instance → **NEXT TARGET**
```

**Cycle 71 Status**: ALL KERNEL LEMMAS PROVED! Only LocalGapBound instance remains!

- [x] `uniformizerAt_zpow_valuation` - Cycle 70 (PROVED) - v(π^n) = exp(-n) for all n ∈ ℤ
- [x] `extract_valuation_bound_zpow` - Cycle 70 (PROVED) - unified for all integers
- [x] `withzero_lt_exp_succ_imp_le_exp` - Cycle 68 (PROVED) - discrete step-down
- [x] `extract_valuation_bound_from_maxIdeal_nonneg_proof` - Cycle 68 (PROVED)
- [x] `valuation_bound_at_other_prime_proof` - Cycle 68 (PROVED)
- [x] `valuation_lt_one_imp_mem_maxIdeal` - Cycle 68 (PROVED)
- [x] `LD_element_maps_to_zero` - Cycle 71 (PROVED) - LD ⊆ ker direction
- [x] `kernel_element_satisfies_all_bounds` - Cycle 71 (PROVED) - ker ⊆ LD direction
- [x] `kernel_evaluationMapAt_complete_proof` - Cycle 71 (PROVED) - ker(eval) = L(D)
- [ ] `instance : LocalGapBound R K` (makes riemann_inequality_affine unconditional)

---

## Infrastructure Summary

**Core Infrastructure (PROVED)**:
- `residueFieldAtPrime v` = v.asIdeal.ResidueField (Cycle 24)
- `uniformizerAt v` + 7 lemmas (Cycle 24.2)
- `valuationRingAt v` : ValuationSubring K + 5 lemmas (Cycle 26)
- `partialResidueMap` + linearity proofs (Cycles 27-28)
- `localizationAtPrime_isDVR`: Localization.AtPrime is DVR (Cycle 31)
- `localization_isFractionRing`: IsFractionRing (Loc.AtPrime) K (Cycle 35)
- `range_algebraMap_subset_valuationRingAt`: Forward set inclusion (Cycle 36)

**Recent Achievements (Cycles 41-46)**:
- `mem_of_algebraMap_mem_map`: Reverse direction via comap_map_of_isPrime_disjoint
- `algebraMap_isUnit_iff_not_mem`: IsUnit ↔ not in ideal
- `dvr_intValuation_of_isUnit`: Units have intVal = 1
- `mem_asIdeal_iff_mem_maxIdeal`: r ∈ v.asIdeal ↔ algebraMap r ∈ maxIdeal
- `dvr_intValuation_unit`: r ∉ v.asIdeal ⟹ DVR.intVal = 1
- `dvr_intValuation_of_algebraMap'` (easy case): DVR intVal = v.intVal for r ∉ v.asIdeal
- **Cycle 45**: ROOT BLOCKER `mem_pow_of_mul_mem_pow_of_not_mem` via Ideal.IsPrime.mul_mem_pow
- **Cycle 45**: `mem_asIdeal_pow_of_algebraMap_mem_maxIdeal_pow` (backward direction)
- **Cycle 45**: `mem_asIdeal_pow_iff_mem_maxIdeal_pow'` (complete iff characterization)
- **Cycle 46**: `dvr_intValuation_eq_via_pow_membership` PROVED via intValuation_le_pow_iff_mem bridge

---

## Historical Cycles

| Cycle | Achievement |
|-------|-------------|
| 1-3 | RRData structure, statement elaborates |
| 4-6 | Divisor, FunctionFieldData, RRSpace as k-Submodule |
| 7-9 | ell = finrank, quotient infrastructure |
| 10-11 | SinglePointBound axiom, **Riemann inequality PROVED** (v1) |
| 12-16 | Full RR structure, Clifford's theorem (v1) |
| 17 | **PIVOT**: Created RR_v2.lean with Dedekind domains |
| 18-20 | Valuation-based L(D), RRModuleV2_real, ellV2_real_mono |
| 21-23 | SinglePointBound typeclass, LocalGapBound hierarchy, riemann_inequality_affine |
| 24 | Linear Algebra Bridge + Uniformizer infrastructure |
| 25-28 | Valuation ring + partial residue map + linearity proofs |
| 29-30 | shifted_element_valuation PROVED, ker(residueMapFromR) = v.asIdeal |
| 31-33 | DVR instance, localization machinery, forward direction |
| 34-37 | Arithmetic lemmas, IsFractionRing instance, complete proof structure |
| 38-40 | intValuation bridge candidates, **modularization** |
| 41 | Foundation lemmas COMPLETE (8/8 PROVED) |
| 42 | Section ordering blocker identified |
| 43 | Section reordering, 3 lemmas PROVED |
| 44 | Ideal power membership bridge (3 PROVED, identified ROOT BLOCKER) |
| 45 | ROOT BLOCKER PROVED (3 lemmas via Ideal.IsPrime.mul_mem_pow) |
| 46 | **dvr_intValuation_eq_via_pow_membership PROVED** (intVal bridge, unblocks hard case) |
| 47 | **dvr_intValuation_of_algebraMap' PROVED** (section reordering, unblocks valuation bridge) |
| 48 | **dvr_valuation_eq_height_one' PROOF VERIFIED** (section ordering blocks deployment) |
| 49 | **dvr_valuation_eq_height_one' DEPLOYED** (Cycle49Prerequisites section, cascade unblocked) |
| 50 | **valuationRingAt_equiv_localization' PROVED** (Ring equiv via ValuationSubring equality) |
| 51 | **residueFieldBridge candidates** (8 stubs, proof chain identified: 1→6→2→3→7) |
| 52 | **residueFieldBridge PROVED** (7/8 candidates via IsLocalRing.ResidueField.mapEquiv) |
| 53 | **Consolidation & Cull** (dead code marked OBSOLETE, corrected victory path) |
| 54 | **shifted_element_valuation_le_one PROVED** (7 helpers + main lemma, Infrastructure.lean CLEAN) |
| 55 | **evaluationFun_via_bridge DEFINED** (core function + 3/8 candidates PROVED, linearity pending) |
| 56 | **evaluationMapAt_complete PROVED** (LinearMap complete! 5/6 PROVED, diagram commutativity pending) |
| 57 | **bridge_residue_algebraMap decomposition** (2/8 PROVED, 2 key blockers identified) |
| 58 | **Deep analysis of key blockers** (proof strategies identified, test file created) |
| 59 | **BLOCKER 2 helpers PROVED** (2/8 PROVED: localization_residue_equiv_symm_algebraMap, ofBijective_quotient_mk_eq_algebraMap) |
| 60 | **BLOCKER 2 PROVED in TestBlockerProofs** (1/8 in main file, type unification blocks transplant) |
| 61-65 | Bridge completion, evaluationMapAt linear map finalization |
| 66-68 | KernelProof extraction, discrete step-down lemmas |
| 69 | Refactoring: Split LocalGapInstance (3.3K lines, 86s) into separate KernelProof.lean |
| 70 | **zpow fix**: shiftedElement now uses zpow (not toNat), uniformizerAt_zpow_valuation + extract_valuation_bound_zpow PROVED |
| 71 | **🎉 KERNEL COMPLETE**: LD_element_maps_to_zero + kernel_element_satisfies_all_bounds + kernel_evaluationMapAt_complete_proof ALL PROVED |

---

## Key References
- mathlib: `RingTheory.DedekindDomain.*`
- mathlib: `RingTheory.Length` (Module.length_eq_add_of_exact)
- mathlib: `Ideal.ResidueField` for κ(v)
- mathlib: `ValuationSubring` for valuation ring
