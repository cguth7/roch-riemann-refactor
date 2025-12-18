# Playbook (Curator maintained)

## Ultimate Goal: Riemann-Roch Theorem

**IMPORTANT CONTEXT FOR ALL LOOPS**: The Riemann inequality milestones are complete. Next target is full Riemann-Roch.

The **ultimate objective** is a complete formalization of the **Riemann-Roch theorem** for algebraic curves/function fields in Lean 4:
```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

Where:
- `ℓ(D)` = dimension of the Riemann-Roch space L(D)
- `K` = canonical divisor
- `g` = genus of the curve/function field
- `deg(D)` = degree of divisor D

**Current Phase**: Both affine and projective Riemann inequalities are **COMPLETE**!
1. ✅ `riemann_inequality_affine` — UNCONDITIONALLY PROVED (Cycle 73)
2. ✅ `riemann_inequality_proj` — SORRY-FREE (Cycle 79)
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

## Current Status (Cycle 79 - Projective Complete! 🎉)

**Codebase Structure**:
```
RrLean/RiemannRochV2/
├── Basic.lean              # Imports ✅
├── Divisor.lean            # DivisorV2 ✅
├── RRSpace.lean            # L(D), ℓ(D) via Module.length ✅ **CLEAN** (0 sorries!)
├── Typeclasses.lean        # LocalGapBound, SinglePointBound, BaseDim ✅
├── RiemannInequality.lean  # Affine theorem ✅ **UNCONDITIONAL!**
├── Infrastructure.lean     # Residue, uniformizer ✅ **CLEAN** (0 sorries!)
├── RRDefinitions.lean      # Essential definitions ✅ **CLEAN** (0 sorries!)
├── KernelProof.lean        # Kernel proofs ✅ **CLEAN** (0 sorries!)
├── DimensionCounting.lean  # Cycle 73 ✅ **CLEAN** (0 sorries!)
├── Projective.lean         # Cycle 79 ✅ **CLEAN** (0 sorries!)
├── TestBlockerProofs.lean  # Cycle 58-60: Test proofs
└── archive/
    └── LocalGapInstance.lean  # ARCHIVED: exploration history
```

**Affine codebase**: 0 sorries (complete!)
**Projective layer**: 0 sorries (complete!)

### 🎉 MILESTONE ACHIEVED (Cycle 73)

**RIEMANN INEQUALITY IS NOW UNCONDITIONALLY PROVED!**

```lean
lemma riemann_inequality_affine [bd : BaseDim R K] {D : DivisorV2 R} (hD : D.Effective) :
    (ellV2_real R K D : ℤ) ≤ D.deg + bd.basedim
```

The `[LocalGapBound R K]` hypothesis has been removed - it's now a global instance!

### Typeclass Hierarchy
```
LocalGapBound R K          -- ✅ PROVED (Cycle 73 - global instance!)
    ↑ extends
SinglePointBound R K       -- PROJECTIVE (adds ell_zero = 1)

BaseDim R K                -- SEPARATE (explicit base dimension)
```

### All Blockers RESOLVED!

| Name | Status | Cycle |
|------|--------|-------|
| `evaluationMapAt_complete` | ✅ **PROVED** | 56 |
| `kernel_evaluationMapAt_complete_proof` | ✅ **PROVED** | 71 |
| `localGapBound_of_dedekind` | ✅ **PROVED** | 73 |
| `riemann_inequality_affine` | ✅ **UNCONDITIONAL** | 73 |

### Cycle 73 Technical Notes (LocalGapBound Instance)
- **Exact sequence**: `LinearMap.ker_rangeRestrict` + `Submodule.range_subtype` give exactness
- **`gcongr` tactic**: Handles universe-polymorphic ENat addition
- **Instance disambiguation**: `haveI : LocalGapBound R K := ...` to specify which instance
- **ENat arithmetic**: `ENat.toNat_add`, `WithTop.add_eq_top` for finite case

### Cycle 71 Technical Notes (Kernel Proofs)
- **`erw` for definitional mismatches**: `erw [IsLocalRing.residue_eq_zero_iff]` sees through `valuationRingAt v` = `(v.valuation K).valuationSubring`
- **`unfold valuationRingAt`**: Required before `Valuation.mem_maximalIdeal_iff` rewrites
- **Bridge injectivity**: `RingEquiv.injective` + `map_zero` for backward direction
- **Strict bound for forward**: f ∈ L(D) gives v(f) ≤ exp(D v), so v(shiftedElement) ≤ exp(-1) < 1

---

## Victory Path (COMPLETE! 🎉)

```
evaluationMapAt_complete (Cycle 56 - PROVED ✅)
    ↓
kernel_evaluationMapAt_complete_proof (Cycle 71 - PROVED ✅)
    ↓
localGapBound_of_dedekind (Cycle 73 - PROVED ✅)
    ↓
riemann_inequality_affine (Cycle 73 - UNCONDITIONAL ✅)  ← 🎉 VICTORY!
```

**All checkboxes complete!**

- [x] `evaluationMapAt_complete` - Cycle 56 (PROVED)
- [x] `kernel_evaluationMapAt_complete_proof` - Cycle 71 (PROVED)
- [x] `localGapBound_of_dedekind` - Cycle 73 (PROVED)
- [x] `riemann_inequality_affine` - Cycle 73 (UNCONDITIONAL)

---

## Cleanup Status (Cycle 75 - COMPLETE ✅)

All technical debt has been addressed:

- ✅ **RRSpace.lean**: Deleted unused placeholder definitions (`RRModuleV2`, `ellV2`, etc.)
- ✅ **KernelProof.lean**: Deleted 12 obsolete stubs, kept proved versions
- ✅ **RiemannInequality.lean**: Deleted deprecated `riemann_inequality` lemma
- ✅ **RRDefinitions.lean**: Added ~130 lines to complete DVR-valuation bridge proof
- ✅ **LocalGapInstance.lean**: Archived to `archive/` folder

**Result**: 0 sorries in main codebase!

---

## Future Work

### ✅ Projective Layer (Cycle 79 - COMPLETE)

**Status**: Projective RR is now **SORRY-FREE**!

```lean
theorem riemann_inequality_proj [ProperCurve k R K] [AllRational k R]
    {D : DivisorV2 R} (hD : D.Effective)
    [∀ E, Module.Finite k (RRSpace_proj k R K E)] :
    (ell_proj k R K D : ℤ) ≤ D.deg + 1
```

**Solution Used** (Cycle 79):
1. Derived `Module.Finite k κ(v)` from `RationalPoint` via `κ(v) ≃ₐ[k] k`
2. Constructed k-linear map `ψ` using scalar tower `IsScalarTower.algebraMap_smul`
3. Proved `LD = ker(ψ)` using `LD_element_maps_to_zero` and `kernel_evaluationMapAt_complete_proof`
4. Applied `Submodule.liftQ` + `LinearMap.finrank_le_finrank_of_injective`

**Key Typeclasses**:
- `RationalPoint k R v` — κ(v) ≅ₐ[k] k
- `ProperCurve k R K` — axiom `ell_proj 0 = 1`
- `AllRational k R` — all points are rational

### Long-term: Full Riemann-Roch

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

Requires:
1. Canonical divisor K
2. Genus g (via differentials or Serre duality)
3. Duality between L(D) and L(K-D)

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
| 72 | DimensionCounting extraction, gap bound formalization |
| 73 | **🎉 VICTORY**: LocalGapBound PROVED, riemann_inequality_affine UNCONDITIONAL |
| 74 | Victory lap refactor: RRDefinitions.lean extracted, LocalGapInstance.lean archived |
| 75 | **🎉 SORRY-FREE**: All sorries eliminated, DVR-valuation bridge completed |

---

## Key References
- mathlib: `RingTheory.DedekindDomain.*`
- mathlib: `RingTheory.Length` (Module.length_eq_add_of_exact)
- mathlib: `Ideal.ResidueField` for κ(v)
- mathlib: `ValuationSubring` for valuation ring
