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

## Current Status (Cycle 54)

**Codebase Structure**:
```
RrLean/RiemannRochV2/
├── Basic.lean              # Imports ✅
├── Divisor.lean            # DivisorV2 ✅
├── RRSpace.lean            # L(D), ℓ(D) ✅ (1 sorry placeholder)
├── Typeclasses.lean        # LocalGapBound ✅
├── RiemannInequality.lean  # Main theorems ✅ (1 sorry placeholder)
├── Infrastructure.lean     # Residue, uniformizer ✅ **CLEAN** (0 sorries!)
└── LocalGapInstance.lean   # Cycles 25-54 WIP ✅ BUILDS (dead code marked OBSOLETE)
```

**Active Development**: `LocalGapInstance.lean` (evaluationMapAt_via_bridge - uses shifted_element!)

### Typeclass Hierarchy
```
LocalGapBound R K          -- PROVABLE (gap ≤ 1 via evaluation map)
    ↑ extends
SinglePointBound R K       -- PROJECTIVE (adds ell_zero = 1)

BaseDim R K                -- SEPARATE (explicit base dimension)
```

### Key Active Blockers

| Name | Status | Notes |
|------|--------|-------|
| `mem_pow_of_mul_mem_pow_of_not_mem` | ✅ **PROVED** | Cycle 45: via Ideal.IsPrime.mul_mem_pow |
| `dvr_intValuation_eq_via_pow_membership` | ✅ **PROVED** | Cycle 46: via intValuation_le_pow_iff_mem bridge |
| `dvr_intValuation_of_algebraMap'` | ✅ **PROVED** | Cycle 47: section reordering |
| `dvr_valuation_eq_height_one'` | ✅ **DEPLOYED** | Cycle 49: key valuation bridge |
| `dvr_valuationSubring_eq_valuationRingAt'` | ✅ **PROVED** | Cycle 50: ValuationSubring equality |
| `valuationRingAt_equiv_localization'` | ✅ **PROVED** | Cycle 50: Ring equivalence |
| `residueField_transport_direct` | ✅ **PROVED** | Cycle 52: via IsLocalRing.ResidueField.mapEquiv |
| `residueFieldBridge_explicit` | ✅ **PROVED** | Cycle 52: composition with localization_residueField_equiv |
| `residueMapFromR_surjective` | ❌ **OBSOLETE** | Bypassed by Cycle 52's mapEquiv approach |
| `shifted_element_valuation_le_one` | ✅ **PROVED** | Cycle 54: case analysis (nonneg/neg) + WithZero.exp arithmetic |

### Next Cycle (55) Priorities
1. **Build `evaluationMapAt_via_bridge`** (LocalGapInstance.lean:379) - Uses residueFieldBridge_explicit + shifted_element (PROVED!)
2. **Prove kernel characterization** - Key for gap bound: ker(eval) = L(D)
3. **Instance `LocalGapBound R K`** - Final target

---

## Victory Path (Updated Cycle 54)

```
dvr_intValuation_eq_via_pow_membership (Cycle 46 - PROVED ✅)
    ↓
dvr_intValuation_of_algebraMap' (Cycle 47 - PROVED ✅)
    ↓
dvr_valuation_eq_height_one' (Cycle 49 - DEPLOYED ✅)
    ↓
dvr_valuationSubring_eq_valuationRingAt' (Cycle 50 - PROVED ✅)
    ↓
valuationRingAt_equiv_localization' (Cycle 50 - PROVED ✅)
    ↓
residueField_transport_direct (Cycle 52 - PROVED ✅)
    ↓
residueFieldBridge_explicit (Cycle 52 - PROVED ✅)
    ↓
shifted_element_valuation_le_one (Cycle 54 - PROVED ✅)  ← INFRASTRUCTURE COMPLETE!
    ↓ (proves f·π^{D(v)+1} ∈ valuationRingAt v)
evaluationMapAt_via_bridge (LocalGapInstance.lean:379)  ← NEXT TARGET
    ↓
kernel_evaluationMapAt = L(D)
    ↓
LocalGapBound instance → VICTORY
```

**NOTE**: `residueMapFromR_surjective` is OBSOLETE - the mapEquiv approach bypasses it entirely.

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

---

## Key References
- mathlib: `RingTheory.DedekindDomain.*`
- mathlib: `RingTheory.Length` (Module.length_eq_add_of_exact)
- mathlib: `Ideal.ResidueField` for κ(v)
- mathlib: `ValuationSubring` for valuation ring
