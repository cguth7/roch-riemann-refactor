# Playbook (Curator maintained)

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

## Current Status Summary (Cycle 33)

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
- **`localization_maximalIdeal_eq_map`: maxIdeal = map v.asIdeal (Cycle 33)**
- **`mk_mem_valuationRingAt`: Forward direction - fractions have valuation ≤ 1 (Cycle 33)**

### Typeclass Hierarchy
```
LocalGapBound R K          -- PROVABLE (gap ≤ 1 via evaluation map)
    ↑ extends
SinglePointBound R K       -- PROJECTIVE (adds ell_zero = 1)

BaseDim R K                -- SEPARATE (explicit base dimension)
```

---

## Current Sorry Count (RR_v2.lean after Cycle 33)

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
| 1603 | `valuationRingAt_equiv_localization` | **ACTIVE** | **KEY BLOCKER** - DVR equivalence (Cycle 32) |
| 1610 | `residueField_equiv_of_valuationRingAt_equiv` | BLOCKED | Depends on 1603 |
| 1621 | `residueFieldBridge_via_localization` | BLOCKED | Depends on 1603 |
| 1631 | `residueMapFromR_surjective_via_localization` | BLOCKED | Depends on 1603 |
| 1642 | `exists_same_residue_class_via_fractions` | BACKUP | Alternative direct approach |
| 1714 | `valuationRingAt_iff_fraction` | HELPER | Bidirectional (Cycle 33) |
| 1733 | `valuationRingAt_exists_fraction` | **ACTIVE** | **KEY BLOCKER** - converse direction (Cycle 33) |
| 1744 | `valuationRingAt_equiv_localization_v3` | BLOCKED | Depends on 1733 |
| 1753 | `valuationRingAt_equiv_localization_v2` | REDUNDANT | Same as v3 |
| 1759 | `residueField_equiv_of_valuationRingAt_equiv_v2` | BLOCKED | Depends on equiv |
| 1769 | `residueMapFromR_surjective_via_localization_v2` | BLOCKED | Final target |

**Total**: 25 sorries (2 deprecated, 4 superseded, 6 new Cycle 33, 13 active path)

**Note**: Sorry count increased 19→25 in Cycle 33. Per Frontier Freeze Rule, Cycle 34 should focus exclusively on the key blocker without adding new candidates.

---

## Cycle 33 Accomplishments

**Goal**: Prove DVR equivalence via fraction characterization

**Results**: 2/8 candidates PROVED
- **`localization_maximalIdeal_eq_map`**: maxIdeal (Loc.AtPrime) = map v.asIdeal (PROVED via mathlib)
- **`mk_mem_valuationRingAt`**: Forward direction - r/s ∈ valuationRingAt when s ∉ v.asIdeal (PROVED)
- `valuationRingAt_iff_fraction`: SORRY - bidirectional characterization
- `valuationRingAt_exists_fraction`: SORRY - **NEW KEY BLOCKER** (converse direction)
- `valuationRingAt_equiv_localization_v3`: SORRY - depends on converse
- `valuationRingAt_equiv_localization_v2`: SORRY - redundant
- `residueField_equiv_of_valuationRingAt_equiv_v2`: SORRY - depends on equiv
- `residueMapFromR_surjective_via_localization_v2`: SORRY - final target

**Key Discovery**: `mk_mem_valuationRingAt` proves the forward direction:
```lean
lemma mk_mem_valuationRingAt (v : HeightOneSpectrum R) (r : R) {s : R} (hs : s ∉ v.asIdeal) :
    (algebraMap R K r / algebraMap R K s) ∈ valuationRingAt v
```
Proof uses `valuation_eq_one_of_not_mem` (Cycle 31) and `Valuation.map_div`.

**New Blocker**: `valuationRingAt_exists_fraction` - need to show every g ∈ K with v(g) ≤ 1 can be written as r/s with s ∉ v.asIdeal.

**Mathlib Archaeology Results**:
- `IsDiscreteValuationRing.exists_lift_of_le_one`: If DVR valuation ≤ 1, element is in DVR image ✓
- `IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring`: DVR image = valuationSubring ✓
- `IsDiscreteValuationRing.equivValuationSubring`: DVR ≃+* valuationSubring ✓

**Gap Identified**: The DVR valuation `(maximalIdeal (Loc.AtPrime v.asIdeal)).valuation K` and `v.valuation K` are defined on different HeightOneSpectrum elements. Need to show they're equal/equivalent.

**Reframing for Cycle 34**: Instead of proving the converse directly, show the valuations are equal. Then `exists_lift_of_le_one` gives the converse for free!

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

## Active Edge: Valuation Equality (Cycle 33→34)

**Goal**: Show DVR valuation = HeightOneSpectrum valuation, then DVR equiv follows

**Current State** (after Cycle 33):
```
Valuation Equality Path (NEW - Cycle 34):
(maxIdeal (Loc.AtPrime)).valuation K  =?=  v.valuation K
              │                                   │
              ▼                                   ▼
    Loc.AtPrime ⊆ valuationSubring     valuationRingAt v
              │                                   │
              └───── Should be equal! ────────────┘

If equal → exists_lift_of_le_one gives converse → equivValuationSubring gives equiv
```

**What We Have**:
- ✅ `mk_mem_valuationRingAt`: Forward direction (fractions have valuation ≤ 1) (Cycle 33)
- ✅ `localization_maximalIdeal_eq_map`: maxIdeal = map v.asIdeal (Cycle 33)
- ✅ `localizationAtPrime_isDVR`: Localization.AtPrime is DVR (Cycle 31)
- ✅ Mathlib: `exists_lift_of_le_one`, `equivValuationSubring` (discovered Cycle 33)

**What We Need**:
- ❌ Valuation equality: `(IsDiscreteValuationRing.maximalIdeal (Loc.AtPrime)).valuation K = v.valuation K`
- OR: Show valuationSubrings are equal

**Why This Unlocks Everything**:
1. Valuation equality → valuationSubring equality
2. valuationSubring equality + equivValuationSubring → DVR equivalence
3. DVR equivalence → residue field bridge → evaluationMapAt → LocalGapBound → victory

**Cycle 34 Constraint**: NO new sorry candidates. Focus exclusively on valuation equality.

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

**Current Path** (after Cycle 33):
1. ~~Fix `shifted_element_valuation_le_one`~~ ✅ DONE (Cycle 29)
2. ~~ker(residueMapFromR) = v.asIdeal~~ ✅ DONE (Cycle 30)
3. ~~Conditional bridges ready~~ ✅ DONE (Cycle 31)
4. ~~Localization path discovered~~ ✅ DONE (Cycle 32)
5. ~~Forward direction (mk_mem_valuationRingAt)~~ ✅ DONE (Cycle 33)
6. **BLOCKER**: Show valuation equality → get converse for free (Cycle 34)
7. Then DVR equiv → residue field bridges → evaluationMapAt → kernel → LocalGapBound

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
| 33 | **Forward direction PROVED** (mk_mem_valuationRingAt), mathlib archaeology, reframing |

---

## Key References
- mathlib: `RingTheory.DedekindDomain.*`
- mathlib: `RingTheory.Length` (Module.length_eq_add_of_exact)
- mathlib: `Ideal.ResidueField` for κ(v)
- mathlib: `ValuationSubring` for valuation ring

---

## Cycle 34 Tactical Guide

### Strategic Reframing (Based on Cycle 33 Archaeology)

**OLD approach** (Cycle 33): Prove converse direction directly
- Write g = a/b via IsFractionRing
- If b ∈ v.asIdeal, factor out uniformizer...
- **Problem**: Uniformizer math leads to instance hell

**NEW approach** (Cycle 34): Show valuations are equal, get converse for free
- Show `(maximalIdeal (Loc.AtPrime v.asIdeal)).valuation K = v.valuation K` (or equivalent)
- Then `exists_lift_of_le_one` from mathlib gives converse automatically
- Then `equivValuationSubring` gives the ring equivalence

### Task 1: Prove Valuation Equality (Priority: CRITICAL)

**Goal**: Show the two valuations on K are equal/equivalent:
```lean
lemma localization_valuation_eq (v : HeightOneSpectrum R) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K =
    v.valuation K
-- OR show their valuationSubrings are equal
```

**Search Strategy**:
1. Search mathlib for lemmas connecting `HeightOneSpectrum.valuation` to DVR valuations
2. Look for `valuation.*eq` or `IsEquiv.*valuation` lemmas
3. Check if there's a universal property: "valuation on K centered at p is unique"

**Key Files to Check**:
- `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` (HeightOneSpectrum.valuation)
- `Mathlib/RingTheory/Valuation/Discrete/Basic.lean` (DVR valuation)
- `Mathlib/RingTheory/Localization/AtPrime/*.lean` (localization properties)

**Mathematical Argument**:
Both valuations:
1. Have value group ℤᵐ⁰
2. Are centered at the same prime ideal v.asIdeal (one directly, one via localization)
3. Give the same valuation on elements of R
4. Extend uniquely to K as fraction field

By uniqueness of extensions, they should be equal.

### Task 2: Apply DVR Machinery (Depends on Task 1)

Once valuation equality is proved:
```lean
noncomputable def valuationRingAt_equiv_localization (v : HeightOneSpectrum R) :
    valuationRingAt v ≃+* Localization.AtPrime v.asIdeal := by
  -- valuation equality gives valuationSubring equality
  have heq : ((maxIdeal (Loc.AtPrime)).valuation K).valuationSubring = valuationRingAt v := ...
  -- equivValuationSubring gives: Loc.AtPrime ≃+* (maxIdeal).valuationSubring
  have hequiv := IsDiscreteValuationRing.equivValuationSubring (Loc.AtPrime) K
  -- Compose: valuationRingAt = valuationSubring ≃ Loc.AtPrime
  exact heq ▸ hequiv.symm
```

### Success Criteria for Cycle 34

**Pass**: One of:
- Find existing mathlib lemma showing valuation equality
- Prove valuation equality via universal property
- Prove a "baby lemma" that demonstrably shortens the path

**Fail**: Adding more sorry scaffolding without moving the blocker

### Fallback (Only if Task 1 proves impossible)

If valuation equality is blocked by fundamental API gaps:
1. Document the gap clearly
2. Consider axiomatizing `valuationRingAt v ≃ Localization.AtPrime v.asIdeal` as a structure field
3. Or pivot to direct `exists_same_residue_class_via_fractions` proof
