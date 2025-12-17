# Ledger Vol. 2 (Cycles 35+)

*For Cycles 1-34, see `state/ledger_archive.md`*

## Summary: Where We Are (End of Cycle 42)

**Project Goal**: Prove Riemann-Roch inequality for Dedekind domains in Lean 4.

**Current Target**: `instance : LocalGapBound R K` (makes riemann_inequality_affine unconditional)

**Codebase Structure** (after Cycle 40 modularization):
```
RrLean/
├── RiemannRochV2.lean          # Re-export (imports all modules)
├── RiemannRochV2/
│   ├── Basic.lean              # Imports (~50 lines) ✅
│   ├── Divisor.lean            # DivisorV2 (~130 lines) ✅
│   ├── RRSpace.lean            # L(D), ℓ(D) (~245 lines) ✅
│   ├── Typeclasses.lean        # LocalGapBound etc (~100 lines) ✅
│   ├── RiemannInequality.lean  # Main theorems (~220 lines) ✅
│   ├── Infrastructure.lean     # Residue, uniformizer (~280 lines) ✅
│   └── LocalGapInstance.lean   # Cycles 25-41 WIP (~1620 lines) ✅ BUILDS
└── archive/
    ├── RR_v1_axiom_based.lean  # Cycles 1-16 (archived)
    └── RR_v2_monolithic.lean   # Cycles 17-39 (archived)
```

**Blocking Chain** (UPDATED after Cycle 41):
```
mem_of_algebraMap_mem_map (Cycle 41 - PROVED) ✅
algebraMap_isUnit_iff_not_mem (Cycle 41 - PROVED) ✅
dvr_intValuation_of_isUnit (Cycle 41 - PROVED) ✅
    ↓
mem_asIdeal_iff_mem_maxIdeal (Cycle 39 - UNBLOCKED)
dvr_intValuation_unit (Cycle 39 - UNBLOCKED)
    ↓
dvr_intValuation_of_algebraMap' (Cycle 39 - TARGET)
    ↓
dvr_valuation_eq_height_one' (Cycle 37 - KEY BLOCKER)
    ↓
valuationRingAt_subset_range_algebraMap' (PROVED*, depends on above)
    ↓
valuationSubring_eq_localization_image_complete (PROVED*, set equality)
    ↓
valuationRingAt_equiv_localization
    ↓
residueMapFromR_surjective
    ↓
evaluationMapAt → kernel → LocalGapBound → VICTORY
```

**Cycle 42 Achievement**: Identified section ordering blocker. Cycle 39 candidates are PROVABLE once Cycle 41 section is moved before them.

---

## 2025-12-16

### Cycle 40 - CLEANING CYCLE: Modularization - COMPLETE

**Goal**: Split monolithic RR_v2.lean (2,531 lines) into focused modules for maintainability.

#### Changes Made

| Action | Details |
|--------|---------|
| **Created** | `RrLean/RiemannRochV2/` directory with 7 modules |
| **Archived** | `RR_v2.lean` → `archive/RR_v2_monolithic.lean` |
| **Archived** | `RR.lean` (v1) → `archive/RR_v1_axiom_based.lean` |
| **Updated** | `RrLean.lean` root to import only modular v2 |

#### New Module Structure

| Module | Lines | Content | Build Status |
|--------|-------|---------|--------------|
| `Basic.lean` | ~50 | Shared mathlib imports | ✅ Builds |
| `Divisor.lean` | ~130 | DivisorV2, deg, Effective, helpers | ✅ Builds |
| `RRSpace.lean` | ~245 | L(D), ℓ(D), monotonicity | ⚠️ 1 sorry (placeholder) |
| `Typeclasses.lean` | ~100 | LocalGapBound, SinglePointBound, BaseDim | ✅ Builds |
| `RiemannInequality.lean` | ~220 | riemann_inequality_real, _affine | ⚠️ 1 sorry (placeholder) |
| `Infrastructure.lean` | ~280 | Residue field, uniformizer (Cycles 22-24) | ⚠️ 1 sorry (WIP) |
| `LocalGapInstance.lean` | ~1530 | Cycles 25-39 evaluation map work | ❌ Pre-existing errors |

#### Key Findings

1. **Original RR_v2.lean had build errors** - Cycle 37 proofs were broken (rewrite failures in `dvr_valuationSubring_eq_range` proof). Modularization exposed pre-existing issues.

2. **Core theorems isolated and working** - `riemann_inequality_real` and `riemann_inequality_affine` are in clean, building modules.

3. **WIP code contained** - All sorries and broken proofs from Cycles 25-39 are now isolated in `LocalGapInstance.lean`.

#### Dependency Graph

```
Basic
  ↓
Divisor
  ↓
RRSpace
  ↓
Typeclasses ←── Infrastructure
  ↓                ↓
RiemannInequality  LocalGapInstance
```

#### Benefits

- **Faster iteration**: Changing `LocalGapInstance` doesn't rebuild `Divisor`
- **Parallel builds**: Lake can build independent modules concurrently
- **Clear separation**: Proven theorems vs WIP clearly demarcated
- **Matches mathlib style**: Each file ~100-300 lines, focused on one concept

**Cycle rating**: 8/10 - Major architectural improvement, technical debt addressed

---

### Cycle 41 - Foundation Lemmas COMPLETE - MAJOR PROGRESS

**Goal**: Prove foundation lemmas for intValuation bridge (unblock Cycle 39 blockers)

#### Results

| Definition/Lemma | Status | Notes |
|-----------------|--------|-------|
| `mem_of_algebraMap_mem_map` | ✅ **PROVED** | Reverse direction via `comap_map_of_isPrime_disjoint` |
| `algebraMap_isUnit_iff_not_mem` | ✅ **PROVED** | Uses `IsLocalization.AtPrime.isUnit_to_map_iff` |
| `dvr_intValuation_of_isUnit` | ✅ **PROVED** | Units have intVal = 1 (chains C4 + C7) |
| `localRing_not_mem_maxIdeal_iff_isUnit` | ✅ **PROVED** | Uses `IsLocalRing.notMem_maximalIdeal` |
| `algebraMap_mem_map_of_mem` | ✅ **PROVED** | Forward direction (trivial) |
| `algebraMap_not_mem_maxIdeal_of_not_mem` | ✅ **PROVED** | Contrapositive of C1 |
| `dvr_intValuation_eq_one_iff_not_mem_maxIdeal` | ✅ **PROVED** | Uses `HeightOneSpectrum.intValuation_eq_one_iff` |
| `dvr_maximalIdeal_asIdeal_eq_localRing_maximalIdeal` | ✅ **PROVED** | Definitional equality (rfl) |

**All 8/8 candidates PROVED!**

#### Key Achievements

1. **Fixed build error from Cycle 40**: `dvr_valuationSubring_eq_range` proof was using incorrect `ValuationSubring.mem_toSubring` rewrite. Fixed to use `Subring.coe_map` + `Set.image_univ`.

2. **Ideal membership bridge**: `mem_of_algebraMap_mem_map` proves the hard direction using `IsLocalization.comap_map_of_isPrime_disjoint` - for localization at a prime, `comap(map(I)) = I`.

3. **Unit characterization bridge**: `algebraMap_isUnit_iff_not_mem` + `dvr_intValuation_of_isUnit` together prove that elements outside v.asIdeal have DVR intValuation = 1.

#### Blockers Unblocked

| Cycle 39 Blocker | Status | How to Complete |
|------------------|--------|-----------------|
| `mem_asIdeal_iff_mem_maxIdeal` | **UNBLOCKED** | Use C1 (reverse) + C5 (forward) |
| `dvr_intValuation_unit` | **UNBLOCKED** | Use C2 + C3 |

#### Next Steps

Cycle 42 should:
1. Complete `mem_asIdeal_iff_mem_maxIdeal` (now trivial)
2. Complete `dvr_intValuation_unit` (now trivial)
3. Then tackle `dvr_intValuation_of_algebraMap'` → `dvr_valuation_eq_height_one'`

**Cycle rating**: 10/10 - All 8 candidates proved, major blockers unblocked

---

### Cycle 42 - Section Ordering Blocker Identified - PROGRESS

**Goal**: Complete `mem_asIdeal_iff_mem_maxIdeal` and `dvr_intValuation_unit` using Cycle 41 foundation

#### Results

| Definition/Lemma | Status | Notes |
|-----------------|--------|-------|
| `dvr_intValuation_zero` | ✅ **PROVED** | Base case via `map_zero` |
| `dvr_intValuation_mem_lt_one` | ⚠️ SORRY | intVal < 1 for r ∈ v.asIdeal (depends on ideal membership) |
| `intValuation_mem_lt_one_both` | ✅ **BUILDS** | Shows both intValuations < 1 (depends on #2) |

#### Key Finding: Section Ordering Blocker

The Cycle 39 candidates (`mem_asIdeal_iff_mem_maxIdeal`, `dvr_intValuation_unit`) are mathematically PROVABLE using Cycle 41 lemmas, but **cannot compile** because:

- Cycle 39 section (lines 1415-1527) appears BEFORE Cycle 41 section (lines 1538-1631)
- Lean requires declarations to appear before their uses

**Solution for Cycle 43**: Reorder sections - move Cycle 41 before Cycle 39.

#### Proof Sketches Ready

```lean
-- mem_asIdeal_iff_mem_maxIdeal (once reordered)
rw [localization_maximalIdeal_eq_map v]
exact ⟨algebraMap_mem_map_of_mem v r, mem_of_algebraMap_mem_map v r⟩

-- dvr_intValuation_unit (once reordered)
have hunit := (algebraMap_isUnit_iff_not_mem v r).mpr hr
exact dvr_intValuation_of_isUnit v _ hunit
```

#### Reflector Ranking (Top 2)

1. **Section Reordering** (10/10) - Single file change unlocks 3 lemmas
2. **dvr_intValuation_of_algebraMap' easy case** (9/10) - Follows immediately from unit case

**Cycle rating**: 6/10 - Identified critical structural issue, added helper lemmas, clear path forward

---

### Cycle 39 - intValuation Foundation Candidates - PROGRESS
- **Active edge**: Prove dvr_intValuation_of_algebraMap (DVR intVal = v.intVal on R)
- **Strategy**: Foundation approach via ideal membership preservation + unit case

#### Results
| Definition/Lemma | Status | Notes |
|-----------------|--------|-------|
| `ideal_span_map_singleton` | ✅ **PROVED** | Ideal.map(span {r}) = span {algebraMap r} |
| `algebraMap_uniformizer_dvr_uniformizer` | ⚠️ SORRY | Uniformizer maps to uniformizer |
| `dvr_intValuation_unfold` | ✅ **PROVED** | DVR intValuation = intValuationDef (rfl) |
| `mem_asIdeal_iff_mem_maxIdeal` | ⚠️ **SORRY** | **CRITICAL**: r ∈ v.asIdeal ↔ algebraMap r ∈ maxIdeal |
| `dvr_intValuation_of_algebraMap'` | ⚠️ **SORRY** | **TARGET**: DVR intVal = v.intVal on R |
| `mem_asIdeal_pow_iff_mem_maxIdeal_pow` | ⚠️ SORRY | Generalizes membership to powers |
| `dvr_intValuation_uniformizer_pow` | ⚠️ SORRY | Special case for uniformizer powers |
| `dvr_intValuation_unit` | ⚠️ **SORRY** | **CRITICAL**: r ∉ v.asIdeal ⟹ DVR.intVal = 1 |

#### Key Discovery: Foundation Approach
Instead of directly attacking the valuation equality, decompose into:
1. **Ideal membership equivalence** (`mem_asIdeal_iff_mem_maxIdeal`): r ∈ v.asIdeal ↔ algebraMap r ∈ maxIdeal
2. **Unit case** (`dvr_intValuation_unit`): r ∉ v.asIdeal ⟹ intValuation = 1

These two together characterize intValuation behavior completely.

#### Reflector Analysis (Top 2)
1. **mem_asIdeal_iff_mem_maxIdeal** (Score 9.5/10) - Foundation for all membership-based proofs
2. **dvr_intValuation_unit** (Score 8.5/10) - Establishes unit base case

#### Recommended Proving Order
1. `mem_asIdeal_iff_mem_maxIdeal` → 2. `dvr_intValuation_unit` → 3. `dvr_intValuation_of_algebraMap'`

#### Sorry Count
- Total in RR_v2.lean: ~40 sorries (includes Cycle 39 candidates)
- Cycle 39 section: 8 candidates (2 PROVED, 6 SORRY)

**Cycle rating**: 6/10 - Good exploration, identified foundation lemmas, 2 PROVED

---

### Cycle 38 - intValuation Bridge Candidates - PROGRESS
- **Active edge**: Prove dvr_valuation_eq_height_one' (DVR valuation = HeightOneSpectrum valuation)
- **Strategy**: Decompose into intValuation comparison, then use scalar tower

#### Results
| Definition/Lemma | Status | Notes |
|-----------------|--------|-------|
| `dvr_maximalIdeal_asIdeal_eq'` | ✅ **PROVED** | rfl: asIdeal = IsLocalRing.maximalIdeal |
| `dvr_valuation_eq_on_R` | ⚠️ SORRY | Valuations agree on algebraMap R K r |
| `dvr_intValuation_of_algebraMap` | ⚠️ SORRY | **KEY HELPER**: DVR intVal = v.intVal on R |
| `dvr_valuation_via_scalar_tower` | ⚠️ SORRY | Alternative via scalar tower |
| `dvr_valuation_isEquiv_height_one` | ⚠️ SORRY | Show valuations equivalent |
| `dvr_valuationSubring_eq` | ⚠️ SORRY | ValueationSubrings equal |
| `dvr_valuation_eq_height_one'_via_mk` | ⚠️ SORRY | Via fraction decomposition |
| `dvr_intValuation_of_mk'` | ⚠️ SORRY | Partial progress (s ∉ v.asIdeal → intVal s = 1) |

#### Key Discovery: intValuation Bridge
**`dvr_intValuation_of_algebraMap`** is the key helper needed to prove the blocker:
```lean
lemma dvr_intValuation_of_algebraMap (v : HeightOneSpectrum R) (r : R) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation
      (algebraMap R (Localization.AtPrime v.asIdeal) r) = v.intValuation r
```

**Why this should work**:
1. DVR's maximalIdeal = IsLocalRing.maximalIdeal = Ideal.map v.asIdeal
2. Both intValuations measure divisibility by v.asIdeal
3. For r ∈ R: algebraMap R Loc r has the same v.asIdeal-divisibility as r

#### Reflector Analysis (Top 2)
1. **dvr_intValuation_of_algebraMap** (Score 9.0/10) - Key bridge lemma
2. **dvr_intValuation_of_mk'** (Score 8.0/10) - Partial progress, good backup

#### Sorry Count
- Total in RR_v2.lean: 34 sorries (+1 from new sorry in blocker chain)
- Cycle 38 section: 8 candidates (1 PROVED, 7 SORRY)

**Cycle rating**: 6/10 - Good exploration, identified key helper, no concrete proofs beyond rfl

---

### Cycle 37 - Complete Proof Structure (7/8 candidates compile) - PROGRESS
- **Active edge**: Prove DVR valuation = HeightOneSpectrum valuation
- **Strategy**: Use DVR structure + mathlib's `exists_lift_of_le_one` and `map_algebraMap_eq_valuationSubring`

#### Results
| Definition/Lemma | Status | Notes |
|-----------------|--------|-------|
| `dvr_maximalIdeal_asIdeal_eq` | ✅ **PROVED** | Simple rfl |
| `dvr_valuation_eq_height_one'` | ⚠️ **SORRY** | **KEY BLOCKER**: DVR val = HeightOneSpectrum val |
| `exists_lift_from_dvr_valuation` | ✅ **PROVED*** | Uses exists_lift_of_le_one (depends on #2) |
| `dvr_valuationSubring_eq_range` | ✅ **PROVED** | Uses map_algebraMap_eq_valuationSubring |
| `dvr_valuationSubring_eq_valuationRingAt` | ✅ **PROVED*** | Sets equal via val equality (depends on #2) |
| `valuationRingAt_subset_range_algebraMap'` | ✅ **PROVED*** | **TARGET**: 2-line proof via rewrites |
| `valuationRingAt_mem_implies_range` | ✅ **PROVED*** | Alt path via exists_lift |
| `valuationSubring_eq_localization_image_complete` | ✅ **PROVED*** | Full set equality |

#### Key Achievement: Complete Proof Structure
The entire proof chain is now structurally complete! Only one sorry remains:
- `dvr_valuation_eq_height_one'` blocks all 7 dependent lemmas
- Once proved, the full set equality `valuationRingAt = range(algebraMap)` is complete

#### New Blocker: Valuation Equality
**`dvr_valuation_eq_height_one'`**: Need to show:
```lean
(IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K g =
  v.valuation K g
```

**Mathematical insight**:
- DVR's maximalIdeal = IsLocalRing.maximalIdeal = Ideal.map v.asIdeal
- Both valuations extend intValuation from the same prime
- They should agree by construction

#### Sorry Count
- Total in RR_v2.lean: 33 sorries (+1 from key blocker)
- Cycle 37 section: 8 candidates (7 compile, 1 SORRY)

**Cycle rating**: 7/10 - Excellent architecture (single blocker, clean cascade)

---

### Cycle 36 - Forward Set Inclusion PROVED - PROGRESS
- **Active edge**: Prove valuationRingAt = range(algebraMap from Localization.AtPrime)
- **Strategy**: Set equality via subset in both directions

#### Results
| Definition/Lemma | Status | Notes |
|-----------------|--------|-------|
| `localRing_maximalIdeal_eq_map'` | ✅ **PROVED** | Wrapper for Cycle 33 lemma |
| `valuationRingAt_eq_localization_valuationRing` | ✅ **PROVED** | Definitional equality (rfl) |
| `algebraMap_localization_mk'_eq_div'` | ✅ **PROVED** | **KEY**: mk' → r/s in K |
| `valuation_eq_intValuation_extendToLocalization` | ✅ **PROVED** | Definition unwrapping |
| `range_algebraMap_subset_valuationRingAt` | ✅ **PROVED** | **KEY**: Forward direction! |
| `valuationRingAt_subset_range_algebraMap` | ⚠️ **SORRY** | **KEY BLOCKER**: Converse |
| `valuationSubring_eq_localization_image'` | ⚠️ SORRY | Depends on converse |
| `exists_coprime_rep_via_set_eq` | ⚠️ SORRY | Depends on set equality |

#### Key Achievement: Forward Direction PROVED
**`range_algebraMap_subset_valuationRingAt` PROVED**:
```lean
Set.range (algebraMap (Localization.AtPrime v.asIdeal) K) ⊆ (valuationRingAt v : Set K)
```

This required:
1. Use `IsLocalization.surj` to write localization elements as mk'
2. Show mk' → r/s in K via calc block (`algebraMap_localization_mk'_eq_div'`)
3. Apply `mk_mem_valuationRingAt` (Cycle 33) for v(r/s) ≤ 1 when s ∉ v.asIdeal

#### New Blocker: Converse Direction
**`valuationRingAt_subset_range_algebraMap`**: Need to show:
```lean
(valuationRingAt v : Set K) ⊆ Set.range (algebraMap (Localization.AtPrime v.asIdeal) K)
```

**Why this is hard**: Must show that any g ∈ K with v(g) ≤ 1 comes from the localization. This requires either:
1. DVR uniformizer factorization (Cycle 34 approach)
2. Direct use of IsFractionRing surjectivity + valuation analysis

#### Sorry Count
- Total in RR_v2.lean: 32 sorries
- Cycle 36 section: 8 candidates (5 PROVED, 3 SORRY)

**Cycle rating**: 7/10 - Major progress (forward direction complete), clear single blocker

---

### Cycle 35 - IsFractionRing Instance Infrastructure PROVED - PROGRESS
- **Active edge**: Complete `exists_coprime_rep` using DVR theory
- **Strategy**: Path A - Use `IsDiscreteValuationRing.exists_lift_of_le_one`

#### Results
| Definition/Lemma | Status | Notes |
|-----------------|--------|-------|
| `primeCompl_isUnit_in_K` | ✅ **PROVED** | Elements of primeCompl become units in K |
| `localizationToK` | ✅ **PROVED** | Ring hom Loc.AtPrime → K via lift |
| `algebraLocalizationK` | ✅ **PROVED** | Algebra instance K over Loc.AtPrime |
| `scalarTowerLocalizationK` | ✅ **PROVED** | Scalar tower R → Loc.AtPrime → K |
| `localization_isFractionRing` | ✅ **PROVED** | **KEY**: IsFractionRing Loc.AtPrime K |
| `dvr_valuation_eq_height_one` | ⚠️ SORRY | **BLOCKER**: Valuation comparison |
| `exists_localization_lift` | ⚠️ SORRY | Depends on valuation comparison |
| `localization_surj_representation` | ✅ **PROVED** | IsLocalization.surj wrapper |
| `exists_coprime_rep_via_lift` | ⚠️ SORRY | Main target |
| `primeCompl_iff_not_mem` | ✅ **PROVED** | Trivial helper |
| `algebraMap_localization_mk'_eq_div` | ⚠️ SORRY | Division formula (technical) |
| `valuationSubring_eq_localization_image` | ⚠️ SORRY | Alternative approach |

#### Key Achievement: IsFractionRing Instance
**`localization_isFractionRing` PROVED**:
```lean
instance : IsFractionRing (Localization.AtPrime v.asIdeal) K
```

This required:
1. Proving primeCompl elements become units in K
2. Defining the lift ring hom via `IsLocalization.lift`
3. Setting up Algebra and ScalarTower instances
4. Applying `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`

#### Instance Chain (All PROVED)
```
primeCompl_isUnit_in_K → localizationToK → algebraLocalizationK
                                              ↓
                             scalarTowerLocalizationK
                                              ↓
                             localization_isFractionRing ✅
```

#### New Blocker: Valuation Comparison
**`dvr_valuation_eq_height_one`**: Need to show:
```lean
(IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K g =
  v.valuation K g
```

**Why this matters**: To apply `exists_lift_of_le_one`, we need the DVR's maximal ideal valuation to equal our HeightOneSpectrum valuation.

#### Sorry Count
- Total in RR_v2.lean: 31 sorries
- Cycle 35 section: 12 candidates (7 PROVED, 5 SORRY)

**Cycle rating**: 7/10 - Major infrastructure progress (IsFractionRing instance), clear blocker identified

---

## Cycle 36 Plan

**Priority 1**: Prove `dvr_valuation_eq_height_one`
- Both valuations arise from the same prime ideal v.asIdeal
- DVR's maximalIdeal = map of v.asIdeal (proved in Cycle 33)
- Should be able to show valuations agree

**Priority 2 (Backup)**: Prove `valuationSubring_eq_localization_image` directly
- Show the sets are equal without going through valuation comparison

**Once blocker resolved**:
1. `exists_localization_lift` follows from `exists_lift_of_le_one`
2. `exists_coprime_rep_via_lift` follows from lift + surj representation
3. Cascade to DVR equivalence → bridges → evaluation map → LocalGapBound

---

## Key Infrastructure (Proved in Earlier Cycles)

### From Cycle 31-34
- `localizationAtPrime_isDVR`: Localization.AtPrime is DVR
- `localization_maximalIdeal_eq_map`: maxIdeal = map v.asIdeal
- `mk_mem_valuationRingAt`: Forward direction (fractions have valuation ≤ 1)
- `valuation_of_fraction`: v(a/b) = intVal(a)/intVal(b)
- `intValuation_le_of_div_le_one`: v(a/b) ≤ 1 implies intVal(a) ≤ intVal(b)

### From Cycle 24-30
- `local_gap_bound_of_exists_map`: Linear Algebra Bridge
- `uniformizerAt` infrastructure (7 lemmas)
- `valuationRingAt` infrastructure (5 lemmas)
- `residueMapFromR_ker`: ker = v.asIdeal
- `shifted_element_valuation_le_one_v2`: KEY lemma for evaluation

### Victory Path
```
dvr_valuation_eq_height_one (BLOCKER)
    ↓
exists_lift_of_le_one (mathlib)
    ↓
exists_coprime_rep
    ↓
valuationRingAt_equiv_localization
    ↓
residueMapFromR_surjective
    ↓
evaluationMapAt
    ↓
kernel_evaluationMapAt
    ↓
instLocalGapBound → VICTORY
```
