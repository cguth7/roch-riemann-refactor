# Ledger Vol. 2 (Cycles 35+)

*For Cycles 1-34, see `state/ledger_archive.md`*

## Summary: Where We Are (End of Cycle 47)

**Project Goal**: Prove Riemann-Roch inequality for Dedekind domains in Lean 4.

**Current Target**: `instance : LocalGapBound R K` (makes riemann_inequality_affine unconditional)

**Blocking Chain**:
```
dvr_intValuation_eq_via_pow_membership (Cycle 46 - PROVED ✅)
    ↓
dvr_intValuation_of_algebraMap' (Cycle 47 - PROVED ✅)
    ↓
dvr_valuation_eq_height_one' (KEY BLOCKER)
    ↓
valuationRingAt_subset_range_algebraMap' (PROVED*, depends on above)
    ↓
valuationRingAt_equiv_localization → residueMapFromR_surjective
    ↓
evaluationMapAt → kernel → LocalGapBound → VICTORY
```

---

## 2025-12-17

### Cycle 47 - dvr_intValuation_of_algebraMap' PROVED

**Goal**: Complete dvr_intValuation_of_algebraMap' via section reordering

#### Key Change

**Section Reordering**: Moved `Cycle44Candidates` section (containing `dvr_intValuation_eq_via_pow_membership`) to before `Cycle39Candidates` (renamed to `Cycle44Candidates_Moved`).

This resolved a dependency ordering issue where `dvr_intValuation_of_algebraMap'` (in Cycle39) needed `dvr_intValuation_eq_via_pow_membership` (in Cycle44), but Cycle44 was defined after Cycle39 in the file.

#### Proof Strategy

The hard case of `dvr_intValuation_of_algebraMap'` (when `r ∈ v.asIdeal`) now uses:
```lean
exact dvr_intValuation_eq_via_pow_membership_moved v r hr0
```

#### Results

| Lemma | Status | Notes |
|-------|--------|-------|
| `dvr_intValuation_of_algebraMap'` | ✅ **PROVED** | Hard case completed via section reordering |

**Cascade Unblocked**: `dvr_valuation_eq_height_one'` is now the sole KEY BLOCKER.

**Discovery**: Found `Valuation.extendToLocalization_apply_map_apply` in mathlib - may help prove `dvr_valuation_eq_height_one'`.

**Next Steps (Cycle 48)**:
1. Prove `dvr_valuation_eq_height_one'` using `dvr_intValuation_of_algebraMap'` + extension properties
2. Complete `valuationRingAt_subset_range_algebraMap'`
3. Build towards `valuationRingAt_equiv_localization`

**Cycle rating**: 9/10 (key lemma proved, clear path to final blocker)

---

### Cycle 46 - dvr_intValuation_eq_via_pow_membership PROVED

**Goal**: Prove dvr_intValuation_eq_via_pow_membership (key bridge lemma)

#### Key Discovery

Used **`HeightOneSpectrum.intValuation_le_pow_iff_mem`** from `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean:249`:
```lean
theorem intValuation_le_pow_iff_mem (r : R) (n : ℕ) :
    v.intValuation r ≤ exp (-(n : ℤ)) ↔ r ∈ v.asIdeal ^ n
```

Combined with `mem_asIdeal_pow_iff_mem_maxIdeal_pow'` (proved in Cycle 45), this bridges both intValuations.

#### Proof Strategy

1. Both intValuations are characterized by `intValuation_le_pow_iff_mem`
2. Use `mem_asIdeal_pow_iff_mem_maxIdeal_pow'` to connect: `r ∈ v.asIdeal^n ↔ algebraMap r ∈ maxIdeal^n`
3. Apply `le_antisymm` with calc blocks showing each direction

#### Results

| Lemma | Status | Notes |
|-------|--------|-------|
| `dvr_intValuation_eq_via_pow_membership` | ✅ **PROVED** | Key bridge via threshold characterization |

**Cascade Unblocked**: `dvr_intValuation_of_algebraMap'` hard case is now unblocked (needs section reordering to access the lemma)

**Next Steps (Cycle 47)**:
1. Reorder sections: Move Cycle44/45 lemmas before Cycle39Candidates
2. Complete `dvr_intValuation_of_algebraMap'` hard case
3. Attack `dvr_valuation_eq_height_one'` (final KEY BLOCKER)

**Cycle rating**: 9/10 (key lemma proved, cascade unblocked)

---

### Cycle 45 - ROOT BLOCKER PROVED - 3 LEMMAS COMPLETE

**Goal**: Prove ROOT BLOCKER `mem_pow_of_mul_mem_pow_of_not_mem`

#### Key Discovery

Found **`Ideal.IsPrime.mul_mem_pow`** in `Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean:668`:
```lean
theorem Ideal.IsPrime.mul_mem_pow (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : ℕ}
    (h : a * b ∈ I ^ n) : a ∈ I ∨ b ∈ I ^ n
```

This directly proves the ROOT BLOCKER!

#### Results

| Lemma | Status | Notes |
|-------|--------|-------|
| `mem_pow_of_mul_mem_pow_of_not_mem` | ✅ **PROVED** | ROOT BLOCKER via Ideal.IsPrime.mul_mem_pow |
| `mem_asIdeal_pow_of_algebraMap_mem_maxIdeal_pow` | ✅ **PROVED** | Backward direction |
| `mem_asIdeal_pow_iff_mem_maxIdeal_pow'` | ✅ **PROVED** | Complete iff characterization |

**Proof Strategy (worked perfectly)**:
1. `Ideal.IsPrime.mul_mem_pow` gives: `a * b ∈ I^n → a ∈ I ∨ b ∈ I^n`
2. Our lemma: `m ∉ v.asIdeal, m * r ∈ v.asIdeal^n → r ∈ v.asIdeal^n`
3. Apply, then `resolve_left` with hypothesis `hm : m ∉ v.asIdeal`

**Section Reordering**: Moved `mem_pow_of_mul_mem_pow_of_not_mem` before `mem_asIdeal_pow_of_algebraMap_mem_maxIdeal_pow` to fix dependency ordering.

**Cycle rating**: 10/10 (ROOT BLOCKER eliminated, cascade unblocked)

---

### Cycle 44 - Ideal Power Membership Bridge - 3 PROVED + ROOT BLOCKER IDENTIFIED

**Goal**: Complete dvr_intValuation_of_algebraMap' hard case (r ∈ v.asIdeal)

#### Results

| Lemma | Status | Notes |
|-------|--------|-------|
| `ideal_map_pow_eq_pow_map'` | ✅ **PROVED** | Trivial: Ideal.map_pow application |
| `maxIdeal_pow_eq_map_asIdeal_pow` | ✅ **PROVED** | maxIdeal^n = map(v.asIdeal^n) |
| `algebraMap_mem_maxIdeal_pow_of_mem_asIdeal_pow` | ✅ **PROVED** | Forward direction |
| `mem_asIdeal_pow_of_algebraMap_mem_maxIdeal_pow` | ⚠️ SORRY | Backward, needs coprimality |
| `mem_pow_of_mul_mem_pow_of_not_mem` | ⚠️ **ROOT BLOCKER** | m∉p, m*r∈p^n → r∈p^n |

**Key Discovery**: The coprimality lemma `mem_pow_of_mul_mem_pow_of_not_mem` is the ROOT BLOCKER.

**Proof Strategy for Cycle 45**:
- Use `Associates.count_mul`: count(p, a*b) = count(p, a) + count(p, b)
- Since m ∉ v.asIdeal: count(v.asIdeal, span{m}) = 0
- Therefore: count(v.asIdeal, span{m*r}) = count(v.asIdeal, span{r})
- Conclude: if v.asIdeal^n | span{m*r}, then v.asIdeal^n | span{r}

**Cycle rating**: 7/10 (good progress, identified clear path forward)

---

### Cycle 43 - Section Reordering COMPLETE - 3 LEMMAS PROVED

**Goal**: Reorder sections and complete Cycle 39 blockers using Cycle 41 foundation

#### Results

| Lemma | Status | Notes |
|-------|--------|-------|
| `mem_asIdeal_iff_mem_maxIdeal` | ✅ **PROVED** | r ∈ v.asIdeal ↔ algebraMap r ∈ maxIdeal |
| `dvr_intValuation_unit` | ✅ **PROVED** | r ∉ v.asIdeal ⟹ DVR.intVal = 1 |
| `dvr_intValuation_of_algebraMap'` (easy) | ✅ **PROVED** | r ∉ v.asIdeal case |
| `dvr_intValuation_of_algebraMap'` (hard) | ⚠️ SORRY | r ∈ v.asIdeal case remains |

**Key Change**: Moved Cycle41Candidates section before Cycle39Candidates in LocalGapInstance.lean

**Sorry Count**: ~43 (down from ~47)

**Cycle rating**: 9/10

---

## 2025-12-16

### Cycle 42 - Section Ordering Blocker Identified

**Goal**: Complete `mem_asIdeal_iff_mem_maxIdeal` and `dvr_intValuation_unit`

**Key Finding**: Cycle 39 candidates are mathematically PROVABLE using Cycle 41 lemmas, but cannot compile because Cycle 39 section appears BEFORE Cycle 41 in the file.

**Solution identified for Cycle 43**: Reorder sections.

**Cycle rating**: 6/10

---

### Cycle 41 - Foundation Lemmas COMPLETE - MAJOR PROGRESS

**Goal**: Prove foundation lemmas for intValuation bridge

#### Results (8/8 PROVED)

| Lemma | Status |
|-------|--------|
| `mem_of_algebraMap_mem_map` | ✅ PROVED |
| `algebraMap_isUnit_iff_not_mem` | ✅ PROVED |
| `dvr_intValuation_of_isUnit` | ✅ PROVED |
| `localRing_not_mem_maxIdeal_iff_isUnit` | ✅ PROVED |
| `algebraMap_mem_map_of_mem` | ✅ PROVED |
| `algebraMap_not_mem_maxIdeal_of_not_mem` | ✅ PROVED |
| `dvr_intValuation_eq_one_iff_not_mem_maxIdeal` | ✅ PROVED |
| `dvr_maximalIdeal_asIdeal_eq_localRing_maximalIdeal` | ✅ PROVED |

**Key Achievement**: All 8/8 candidates PROVED! Major blockers unblocked.

**Cycle rating**: 10/10

---

### Cycle 40 - CLEANING CYCLE: Modularization

**Goal**: Split monolithic RR_v2.lean (2,531 lines) into focused modules

#### New Module Structure

| Module | Lines | Status |
|--------|-------|--------|
| `Basic.lean` | ~50 | ✅ |
| `Divisor.lean` | ~130 | ✅ |
| `RRSpace.lean` | ~245 | ✅ (1 sorry) |
| `Typeclasses.lean` | ~100 | ✅ |
| `RiemannInequality.lean` | ~220 | ✅ (1 sorry) |
| `Infrastructure.lean` | ~280 | ✅ (1 sorry) |
| `LocalGapInstance.lean` | ~1530 | ✅ |

**Cycle rating**: 8/10

---

### Cycle 39 - intValuation Foundation Candidates

**Goal**: Prove dvr_intValuation_of_algebraMap

| Lemma | Status |
|-------|--------|
| `ideal_span_map_singleton` | ✅ PROVED |
| `dvr_intValuation_unfold` | ✅ PROVED |
| `mem_asIdeal_iff_mem_maxIdeal` | ⚠️ SORRY (blocked by section order) |
| `dvr_intValuation_of_algebraMap'` | ⚠️ SORRY |
| `dvr_intValuation_unit` | ⚠️ SORRY (blocked by section order) |

**Key Discovery**: Foundation approach - decompose into ideal membership + unit case.

**Cycle rating**: 6/10

---

### Cycle 38 - intValuation Bridge Candidates

**Goal**: Prove dvr_valuation_eq_height_one'

| Lemma | Status |
|-------|--------|
| `dvr_maximalIdeal_asIdeal_eq'` | ✅ PROVED (rfl) |
| `dvr_intValuation_of_algebraMap` | ⚠️ SORRY (KEY HELPER) |

**Key Discovery**: `dvr_intValuation_of_algebraMap` is the key helper.

**Cycle rating**: 6/10

---

### Cycle 37 - Complete Proof Structure

**Goal**: Prove DVR valuation = HeightOneSpectrum valuation

| Lemma | Status |
|-------|--------|
| `dvr_maximalIdeal_asIdeal_eq` | ✅ PROVED |
| `dvr_valuation_eq_height_one'` | ⚠️ **KEY BLOCKER** |
| `dvr_valuationSubring_eq_range` | ✅ PROVED |
| `valuationRingAt_subset_range_algebraMap'` | ✅ PROVED* (depends on blocker) |
| `valuationSubring_eq_localization_image_complete` | ✅ PROVED* (depends on blocker) |

**Key Achievement**: Complete proof structure! Only one sorry remains.

**Cycle rating**: 7/10

---

### Cycle 36 - Forward Set Inclusion PROVED

**Goal**: Prove valuationRingAt = range(algebraMap)

| Lemma | Status |
|-------|--------|
| `algebraMap_localization_mk'_eq_div'` | ✅ PROVED |
| `range_algebraMap_subset_valuationRingAt` | ✅ PROVED |
| `valuationRingAt_subset_range_algebraMap` | ⚠️ SORRY (converse) |

**Key Achievement**: Forward direction `range(algebraMap) ⊆ valuationRingAt` complete!

**Cycle rating**: 7/10

---

### Cycle 35 - IsFractionRing Instance PROVED

**Goal**: Complete exists_coprime_rep using DVR theory

| Lemma | Status |
|-------|--------|
| `primeCompl_isUnit_in_K` | ✅ PROVED |
| `localizationToK` | ✅ PROVED |
| `algebraLocalizationK` | ✅ PROVED |
| `scalarTowerLocalizationK` | ✅ PROVED |
| `localization_isFractionRing` | ✅ PROVED |
| `dvr_valuation_eq_height_one` | ⚠️ SORRY (blocker) |

**Key Achievement**: IsFractionRing (Loc.AtPrime v.asIdeal) K proved!

**Cycle rating**: 7/10
