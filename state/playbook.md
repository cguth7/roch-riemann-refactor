# Playbook (Curator maintained)

## Heuristics
- Prefer line-bundle / invertible-sheaf RR statements; divisor RR is a wrapper.
- Use `finrank k` for dimensions; avoid `Nat`-based dims until the end.
- Keep lemma statements small: fewer binders, fewer coercions, fewer implicit arguments.
- When stuck on coercions, introduce explicit `let` bindings for objects (e.g. `L : LineBundle X`).

## Current Status Summary (Cycle 32)

**RR.lean (v1)**: Axiom-based approach with `FunctionFieldDataWithRR`. Complete but circular - ARCHIVED.

**RR_v2.lean (v2)**: Constructive Dedekind domain approach. Active development.

### Key Results PROVED
- `RRModuleV2_real`: Valuation-based L(D) definition (Cycle 19)
- `ellV2_real_mono`: Monotonicity via Module.length (Cycle 20)
- `riemann_inequality_real`: Conditional on `[SinglePointBound R K]` (Cycle 21)
- `riemann_inequality_affine`: Conditional on `[LocalGapBound R K] [BaseDim R K]` (Cycle 23)
- `local_gap_bound_of_exists_map`: Linear Algebra Bridge (Cycle 24)
- Uniformizer infrastructure: 7 lemmas (Cycle 24.2)
- Valuation ring infrastructure: 5 lemmas (Cycle 26)
- Partial residue map infrastructure: 8 lemmas (Cycle 27-28)
- `shifted_element_valuation_le_one_v2`: KEY BLOCKER RESOLVED (Cycle 29)
- `maximalIdeal_valuationRingAt_comap`: Kernel proof (Cycle 30)
- `residueMapFromR_ker`: ker = v.asIdeal (Cycle 30)
- **`localizationAtPrime_isDVR`: DVR instance (Cycle 31)**
- **`valuation_eq_one_of_not_mem`: v(s)=1 when s∉v.asIdeal (Cycle 31)**
- **`valuation_div_eq_of_unit`: v(r/s)=v(r) when v(s)=1 (Cycle 31)**
- **`residueFieldBridge_v2_of_surj`: First Isom Thm bridge (conditional, Cycle 31)**
- **`residueFieldBridge_v3_of_surj`: Full bridge (conditional, Cycle 31)**
- **`localization_residue_equiv`: R/v.asIdeal ≃ Loc.AtPrime/maxIdeal (Cycle 32)**
- **`localization_residueField_equiv`: Loc.AtPrime.ResidueField ≃ residueFieldAtPrime (Cycle 32)**
- **`localization_residue_surjective`: Helper lemma (Cycle 32)**

### Typeclass Hierarchy
```
LocalGapBound R K          -- PROVABLE (gap ≤ 1 via evaluation map)
    ↑ extends
SinglePointBound R K       -- PROJECTIVE (adds ell_zero = 1)

BaseDim R K                -- SEPARATE (explicit base dimension)
```

---

## Current Sorry Count (RR_v2.lean after Cycle 32)

| Line | Name | Status | Notes |
|------|------|--------|-------|
| 335 | `ellV2_mono` | DEPRECATED | Superseded by `ellV2_real_mono` |
| 713 | `riemann_inequality` | DEPRECATED | Superseded by `riemann_inequality_real` |
| 989 | `shifted_element_valuation_le_one` | SUPERSEDED | By `_v2` version in Cycle 29 section |
| 1029 | `evaluationMapAt` | BLOCKER | Can use `evaluationMapAt_via_bridge` once bridge ready |
| 1040 | `kernel_evaluationMapAt` | BLOCKED | Depends on evaluationMapAt |
| 1049 | `instLocalGapBound` | BLOCKED | Depends on kernel proof |
| 1315 | `residueFieldBridge` | SUPERSEDED | Use residueFieldBridge_v3 instead |
| 1322 | `residueFieldBridge_algebraMap_comm` | SUPERSEDED | Not needed with bypass strategy |
| 1331 | `evaluationMapAt_via_bridge` | BLOCKED | Depends on bridge |
| 1414 | `residueMapFromR_surjective` | BLOCKED | On exists_same_residue_class |
| 1436 | `residueFieldBridge_v2` | BLOCKED | Depends on surjectivity |
| 1449 | `residueFieldBridge_v3` | BLOCKED | Depends on v2 |
| 1496 | `exists_same_residue_class` | ACTIVE | density lemma |
| 1541 | `valuationRingAt_eq_fractions` | ACTIVE | Alternative approach |
| 1603 | `valuationRingAt_equiv_localization` | **ACTIVE** | **KEY BLOCKER** - DVR equivalence |
| 1610 | `residueField_equiv_of_valuationRingAt_equiv` | BLOCKED | Depends on 1603 |
| 1621 | `residueFieldBridge_via_localization` | BLOCKED | Depends on 1603 |
| 1631 | `residueMapFromR_surjective_via_localization` | BLOCKED | Depends on 1603 |
| 1642 | `exists_same_residue_class_via_fractions` | BACKUP | Alternative direct approach |

**Total**: 19 sorries (2 deprecated, 4 superseded, 5 new Cycle 32, 8 active path)

---

## Cycle 32 Accomplishments

**Goal**: Bypass `exists_same_residue_class` via localization machinery

**Key Discovery**: `IsLocalization.AtPrime.equivQuotMaximalIdeal` provides R ⧸ p ≃+* Rₚ ⧸ maxIdeal with built-in surjectivity!

**Results**: 3/8 candidates PROVED
- **`localization_residue_equiv`**: R/v.asIdeal ≃ Loc.AtPrime/maxIdeal (PROVED via equivQuotMaximalIdeal)
- **`localization_residue_surjective`**: Helper lemma (PROVED, trivial)
- **`localization_residueField_equiv`**: Loc.AtPrime.ResidueField ≃ residueFieldAtPrime (PROVED)
- `valuationRingAt_equiv_localization`: SORRY - **NEW KEY BLOCKER** (DVR equivalence)
- `residueField_equiv_of_valuationRingAt_equiv`: SORRY - depends on DVR equiv
- `residueFieldBridge_via_localization`: SORRY - depends on DVR equiv
- `residueMapFromR_surjective_via_localization`: SORRY - depends on DVR equiv
- `exists_same_residue_class_via_fractions`: SORRY - backup direct approach

**Key Insight**: The localization path is cleaner than direct proof:
1. R/v.asIdeal ≃ Loc.AtPrime/maxIdeal (PROVED via equivQuotMaximalIdeal)
2. **MISSING**: valuationRingAt ≃ Loc.AtPrime (both are DVRs in K)
3. Once #2 proved, bridges compose trivially

**New Blocker**: `valuationRingAt_equiv_localization` - need to show valuationRingAt (valuation approach)
equals Localization.AtPrime (algebraic approach). Both are DVRs with same maximal ideal.

---

## Cycle 31 Accomplishments

**Goal**: Prove `residueMapFromR_surjective` (key blocker from Cycle 30)

**Results**: 5/8 candidates PROVED
- **`localizationAtPrime_isDVR`**: Localization.AtPrime is DVR (PROVED)
- `exists_same_residue_class`: SORRY - **NEW KEY BLOCKER** (density of R in valuationRingAt)
- `residueMapFromR_surjective'`: SORRY - depends on density lemma
- **`residueFieldBridge_v2_of_surj`**: First Isomorphism Theorem (PROVED, conditional)
- **`residueFieldBridge_v3_of_surj`**: Full bridge composition (PROVED, conditional)
- `valuationRingAt_eq_fractions`: SORRY - alternative approach
- **`valuation_eq_one_of_not_mem`**: v(s)=1 for s∉v.asIdeal (PROVED)
- **`valuation_div_eq_of_unit`**: v(r/s)=v(r) when v(s)=1 (PROVED)

**Key Insight**: The conditional bridges are complete. Once `exists_same_residue_class` is proved:
1. `residueMapFromR_surjective'` follows immediately
2. `residueFieldBridge_v2_of_surj` gives R/v.asIdeal ≃ valuationRingAt.residueField
3. `residueFieldBridge_v3_of_surj` completes to residueFieldAtPrime

**New Blocker**: `exists_same_residue_class` - needs to show that for any g ∈ valuationRingAt v,
there exists r ∈ R such that embedding(r) - g ∈ maximalIdeal. This is the "density" of R in the
valuation ring modulo maximalIdeal.

---

## Cycle 30 Accomplishments

**Goal**: Construct residueFieldBridge via bypass strategy

**Results**: 3/7 candidates PROVED
- `embeddingToValuationRingAt`: Ring hom R →+* valuationRingAt v (DEF)
- **`maximalIdeal_valuationRingAt_comap`**: maximalIdeal ∩ R = v.asIdeal (PROVED 4/5)
- `residueMapFromR`: Composition R → valuationRingAt → residue field (DEF)
- **`residueMapFromR_ker`**: ker = v.asIdeal (PROVED 4/5)
- `residueMapFromR_surjective`: SORRY - **NEW KEY BLOCKER** (5/5)
- `residueFieldBridge_v2`: SORRY - depends on surjectivity (5/5)
- `residueFieldBridge_v3`: SORRY - depends on v2 (5/5)

**Key Insight**: The bypass strategy is architecturally correct:
1. ker(residueMapFromR) = v.asIdeal (PROVED)
2. IF residueMapFromR is surjective, THEN by First Isomorphism Theorem:
   - valuationRingAt.residueField v ≃ R/v.asIdeal ≃ residueFieldAtPrime R v

**New Blocker**: `residueMapFromR_surjective` - needs to show R is "dense" in valuationRingAt v
modulo the maximal ideal. This is a real mathematical property of Dedekind domains.

---

## Cycle 29 Accomplishments

**Goal**: Complete `shifted_element_valuation_le_one` and residue field bridge infrastructure

**Results**: 5/8 candidates PROVED
- `toNat_nonneg_case`: Int.toNat_of_nonneg wrapper (3/5)
- `toNat_neg_case`: Int.toNat_eq_zero wrapper (3/5)
- **`shifted_element_valuation_le_one_v2`**: KEY BLOCKER RESOLVED via case analysis (5/5 ⭐⭐)
- `valuationRingAt_embedding_compatible`: Simple wrapper (3/5)
- `valuation_algebraMap_mul`: map_mul wrapper (3/5)

**New Sorries** (infrastructure for next cycle):
- `residueFieldBridge`: RingEquiv between residue fields (5/5 - next target)
- `residueFieldBridge_algebraMap_comm`: Depends on bridge (4/5)
- `evaluationMapAt_via_bridge`: Depends on bridge (5/5)

**Key Insight**: Case analysis on `D(v) + 1 ≥ 0` vs `< 0` cleanly handles Int.toNat behavior. Proof uses `WithZero.exp_add`, `WithZero.exp_lt_exp`, and `uniformizerAt_pow_valuation`.

---

## Cycle 28 Accomplishments

**Goal**: Fix partialResidueMap linearity proofs

**Results**: All 3 sorries PROVED
- `partialResidueMap_zero`: Uses `map_zero` (5/5)
- `partialResidueMap_add`: Definitional via `rfl` in SubringClass (5/5)
- `partialResidueMap_smul`: Definitional via `rfl` in SubringClass (5/5)

**Key Insight**: In SubringClass, subtype operations (addition, multiplication) are definitional equalities. The proofs simplify to `rfl` after unfolding definitions.

---

## Active Edge: DVR Equivalence (Cycle 32→33)

**Goal**: Prove `valuationRingAt_equiv_localization` to complete the localization path

**Current State** (after Cycle 32):
```
Localization Path (NEW - Cycle 32):
R/v.asIdeal ≃ Loc.AtPrime/maxIdeal ≃ valuationRingAt.residueField
    ✅ PROVED       ❌ MISSING           ▲
                         │
               valuationRingAt ≃ Loc.AtPrime
                    ❌ KEY BLOCKER
```

**What We Have**:
- ✅ `localization_residue_equiv`: R/v.asIdeal ≃ Loc.AtPrime/maxIdeal (Cycle 32)
- ✅ `localization_residueField_equiv`: Loc.AtPrime.ResidueField ≃ residueFieldAtPrime (Cycle 32)
- ✅ `localizationAtPrime_isDVR`: Localization.AtPrime is DVR (Cycle 31)

**What We Need**:
- ❌ `valuationRingAt_equiv_localization`: valuationRingAt v ≃+* Localization.AtPrime v.asIdeal

**Why This Unlocks Everything**:
1. DVR equivalence → residue field equivalence follows trivially
2. residue field equivalence → residueFieldBridge composition completes
3. bridges → evaluationMapAt → kernel → LocalGapBound → victory

**Alternative Path** (if DVR equiv too hard):
- Prove `exists_same_residue_class_via_fractions` directly using IsFractionRing + CRT

---

## Infrastructure Summary

### Cycle 24-28 Infrastructure (All PROVED unless noted)

**Residue Field (Cycle 24.1)**:
- `residueFieldAtPrime v` = v.asIdeal.ResidueField
- `residueFieldAtPrime.linearEquiv` : R ⧸ v.asIdeal ≃ₗ[R] κ(v)
- `residueFieldAtPrime.isSimpleModule` : κ(v) is simple R-module
- `residueFieldAtPrime.length_eq_one` : Module.length R κ(v) = 1

**Uniformizer (Cycle 24.2)**:
- `uniformizerAt v` : R - uniformizer at v
- `uniformizerAt_val` : v.intValuation π = exp(-1)
- `uniformizerAt_pow_valuation` : v.valuation K (π^n) = exp(-n)

**Linear Algebra Bridge (Cycle 24.1)**:
- `local_gap_bound_of_exists_map` : IF φ exists with right kernel THEN bound holds

**Valuation Ring (Cycle 26)**:
- `valuationRingAt v` : ValuationSubring K
- `mem_valuationRingAt_iff` : g ∈ valRing ↔ v(g) ≤ 1
- `valuationRingAt.isLocalRing` : valuation ring is local
- `valuationRingAt.residueField` : residue field of valuation ring
- `valuationRingAt.residue` : residue map

**Helpers (Cycle 26-27)**:
- `withzero_exp_mul` : exp(a) * exp(b) = exp(a+b)
- `withzero_exp_neg` : exp(-a) = (exp a)⁻¹
- `withzero_exp_le_exp` : exp(a) ≤ exp(b) ↔ a ≤ b
- `withzero_exp_mul_le_one` : exp(a) * exp(b) ≤ 1 → a + b ≤ 0

**Partial Residue Map (Cycle 27-28)**:
- `partialResidueMap v g h` : maps K-element with v(g) ≤ 1 to valuationRingAt.residueField v
- `algebraMap_valuationRingAt_comm` : R embeds compatibly
- `mem_range_iff_valuation_le_one_everywhere` : global integrality criterion
- `partialResidueMap_zero` : PROVED (Cycle 28)
- `partialResidueMap_add` : PROVED (Cycle 28)
- `partialResidueMap_smul` : PROVED (Cycle 28)

---

## Victory Condition

- [ ] `instance : LocalGapBound R K` (makes riemann_inequality_affine unconditional)

**Current Path** (after Cycle 32):
1. ~~Fix `shifted_element_valuation_le_one`~~ ✅ DONE (Cycle 29)
2. ~~ker(residueMapFromR) = v.asIdeal~~ ✅ DONE (Cycle 30)
3. ~~Conditional bridges ready~~ ✅ DONE (Cycle 31)
4. ~~Localization path discovered~~ ✅ DONE (Cycle 32)
5. **BLOCKER**: Prove `valuationRingAt_equiv_localization` (DVR equivalence)
6. Then residue field bridges compose → evaluationMapAt → kernel → LocalGapBound

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
| 18-19 | Valuation-based L(D), RRModuleV2_real complete |
| 20 | ellV2_real_mono PROVED |
| 21 | SinglePointBound typeclass, riemann_inequality_real PROVED |
| 22 | **DISCOVERY**: Affine model limitation (ℓ(0) ≠ 1) |
| 23 | **LocalGapBound hierarchy, riemann_inequality_affine PROVED** |
| 24.1 | Linear Algebra Bridge PROVED (local_gap_bound_of_exists_map) |
| 24.2 | Uniformizer infrastructure PROVED (7 lemmas) |
| 25 | Integration, blocker identified (residue field bridge) |
| 26 | **Valuation ring infrastructure** (5 lemmas, gap narrowed) |
| 27 | **Partial residue map** (5 OK, 3 SORRY), linearity proofs pending |
| 28 | **Linearity proofs COMPLETE** (3 PROVED via rfl) |
| 29 | **shifted_element_valuation_le_one_v2 PROVED** (key blocker resolved) |
| 30 | **Bypass strategy**: ker(residueMapFromR) = v.asIdeal PROVED |
| 31 | **Conditional bridges**: First Isom Thm approach ready, density lemma blocking |
| 32 | **Localization path**: equivQuotMaximalIdeal discovered, DVR equiv blocking |

---

## Key References
- mathlib: `RingTheory.DedekindDomain.*`
- mathlib: `RingTheory.Length` (Module.length_eq_add_of_exact)
- mathlib: `Ideal.ResidueField` for κ(v)
- mathlib: `ValuationSubring` for valuation ring

---

## Cycle 33 Tactical Guide

### Task 1: Prove `valuationRingAt_equiv_localization` (Priority: CRITICAL)

**Location**: Line 1603 in RR_v2.lean

**Goal**: Show valuationRingAt v ≃+* Localization.AtPrime v.asIdeal

**Proof Strategy**:
```lean
noncomputable def valuationRingAt_equiv_localization (v : HeightOneSpectrum R) :
    valuationRingAt (R := R) (K := K) v ≃+* Localization.AtPrime v.asIdeal
```

**Mathematical Content**:
- Both sides are DVRs with fraction field K
- Both have maximal ideal corresponding to v.asIdeal
- `valuationRingAt v` = {g ∈ K : v(g) ≤ 1} (valuation approach)
- `Localization.AtPrime v.asIdeal` = {r/s : r, s ∈ R, s ∉ v.asIdeal} (algebraic approach)
- These are the same subset of K for Dedekind domains

**Approach A: Use existing mathlib DVR machinery**
1. Search for `IsDiscreteValuationRing.equivValuationSubring` or similar
2. Apply to `Localization.AtPrime v.asIdeal` (which we proved is DVR)
3. Check if result connects to `valuationRingAt v`

**Approach B: Show subset equality directly**
1. Prove: `(valuationRingAt v : Set K) = range(algebraMap (Loc.AtPrime) K)`
2. Use `IsFractionRing` properties
3. Both directions:
   - (⊇) r/s with s ∉ v.asIdeal has v(r/s) = v(r) ≤ 1
   - (⊆) g with v(g) ≤ 1 can be written as r/s with s ∉ v.asIdeal

**Approach C: Use uniqueness of DVR with given valuation**
1. Both have same valuation restricted from K
2. DVR with given valuation is unique
3. Use universal property

**Decision Point**: Start with Approach A (search for existing lemmas).

### Task 2: Complete bridge (depends on Task 1)

Once `valuationRingAt_equiv_localization` is proved:

```lean
-- This should become trivial composition:
noncomputable def residueFieldBridge_via_localization (v : HeightOneSpectrum R)
    (e : valuationRingAt v ≃+* Localization.AtPrime v.asIdeal) :
    (R ⧸ v.asIdeal) ≃+* valuationRingAt.residueField v := by
  have h1 := localization_residue_equiv v       -- R/v.asIdeal ≃ Loc/max
  have h2 := residueField_equiv_of_... e        -- Loc.ResField ≃ valRing.ResField
  exact h1.symm.trans h2
```

### Fallback: Direct proof

If DVR equiv proves too hard, fall back to direct proof:
1. Prove `exists_same_residue_class_via_fractions` (line 1642)
2. Use IsFractionRing + CRT approximation
