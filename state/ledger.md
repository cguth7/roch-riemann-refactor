# Ledger Vol. 2 (Cycles 35+)

*For Cycles 1-34, see `state/ledger_archive.md`*

## Summary: Where We Are (End of Cycle 38)

**Project Goal**: Prove Riemann-Roch inequality for Dedekind domains in Lean 4.

**Current Target**: `instance : LocalGapBound R K` (makes riemann_inequality_affine unconditional)

**Blocking Chain**:
```
dvr_intValuation_of_algebraMap (Cycle 38 - NEW KEY HELPER)
    ↓
dvr_valuation_eq_on_R (Cycle 38)
    ↓
dvr_valuation_eq_height_one' (Cycle 37 - KEY BLOCKER)
    ↓
valuationRingAt_subset_range_algebraMap' (PROVED*, depends on above)
    ↓
valuationSubring_eq_localization_image_complete (PROVED*, set equality)
    ↓
exists_coprime_rep_via_set_eq
    ↓
valuationRingAt_equiv_localization
    ↓
residueMapFromR_surjective
    ↓
evaluationMapAt → kernel → LocalGapBound → VICTORY
```

**Cycle 38 Progress**: 8 candidates generated, 1 PROVED (rfl), 7 SORRY. Identified key helper: `dvr_intValuation_of_algebraMap`.

---

## 2025-12-16

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
