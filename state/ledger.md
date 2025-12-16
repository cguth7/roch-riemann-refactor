# Ledger Vol. 2 (Cycles 35+)

*For Cycles 1-34, see `state/ledger_archive.md`*

## Summary: Where We Are (End of Cycle 36)

**Project Goal**: Prove Riemann-Roch inequality for Dedekind domains in Lean 4.

**Current Target**: `instance : LocalGapBound R K` (makes riemann_inequality_affine unconditional)

**Blocking Chain**:
```
valuationRingAt_subset_range_algebraMap (Cycle 36 - KEY BLOCKER)
    ↓
valuationSubring_eq_localization_image' (set equality)
    ↓
exists_coprime_rep_via_set_eq
    ↓
valuationRingAt_equiv_localization
    ↓
residueMapFromR_surjective
    ↓
evaluationMapAt → kernel → LocalGapBound → VICTORY
```

**Cycle 36 Progress**: Forward direction `range(algebraMap) ⊆ valuationRingAt` PROVED!

---

## 2025-12-16

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
