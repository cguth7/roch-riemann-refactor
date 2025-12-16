# Ledger Vol. 2 (Cycles 35+)

*For Cycles 1-34, see `state/ledger_archive.md`*

## Summary: Where We Are (End of Cycle 35)

**Project Goal**: Prove Riemann-Roch inequality for Dedekind domains in Lean 4.

**Current Target**: `instance : LocalGapBound R K` (makes riemann_inequality_affine unconditional)

**Blocking Chain**:
```
exists_coprime_rep (Cycle 34-35)
    ↓
valuationRingAt_equiv_localization
    ↓
residueMapFromR_surjective
    ↓
evaluationMapAt → kernel → LocalGapBound → VICTORY
```

---

## 2025-12-16

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
