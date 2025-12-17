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

## Current Status Summary (Cycle 41)

**Codebase Structure** (after Cycle 40 modularization):
```
RrLean/
├── RiemannRochV2.lean          # Re-export
├── RiemannRochV2/
│   ├── Basic.lean              # Imports ✅
│   ├── Divisor.lean            # DivisorV2 ✅
│   ├── RRSpace.lean            # L(D), ℓ(D) ✅
│   ├── Typeclasses.lean        # LocalGapBound ✅
│   ├── RiemannInequality.lean  # Main theorems ✅
│   ├── Infrastructure.lean     # Residue, uniformizer ✅
│   └── LocalGapInstance.lean   # Cycles 25-41 WIP ✅ BUILDS
└── archive/
    ├── RR_v1_axiom_based.lean  # ARCHIVED (Cycles 1-16)
    └── RR_v2_monolithic.lean   # ARCHIVED (Cycles 17-39)
```

**Active Development**: `RrLean/RiemannRochV2/LocalGapInstance.lean` (Cycles 25-41 work)

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
- `localizationAtPrime_isDVR`: DVR instance (Cycle 31)
- `valuation_eq_one_of_not_mem`: v(s)=1 when s∉v.asIdeal (Cycle 31)
- `localization_maximalIdeal_eq_map`: maxIdeal = map v.asIdeal (Cycle 33)
- `mk_mem_valuationRingAt`: Forward direction - fractions have valuation ≤ 1 (Cycle 33)
- `localization_isFractionRing`: IsFractionRing (Loc.AtPrime v.asIdeal) K (Cycle 35)
- Instance chain: primeCompl_isUnit_in_K → localizationToK → algebraLocalizationK → scalarTowerLocalizationK (Cycle 35)
- **`algebraMap_localization_mk'_eq_div'`: mk' maps to r/s division in K (Cycle 36) ⭐**
- **`range_algebraMap_subset_valuationRingAt`: Forward set inclusion PROVED (Cycle 36) ⭐**
- **`dvr_valuationSubring_eq_range`: DVR range = valuationSubring (Cycle 37) ⭐**
- **`valuationRingAt_subset_range_algebraMap'`: Converse (conditional on valuation eq) (Cycle 37) ⭐**
- **`dvr_maximalIdeal_asIdeal_eq'`: DVR HeightOneSpectrum asIdeal = IsLocalRing.maximalIdeal (Cycle 38) ⭐**
- **`ideal_span_map_singleton`: Ideal.map(span {r}) = span {algebraMap r} (Cycle 39) ⭐**
- **`dvr_intValuation_unfold`: DVR intValuation = intValuationDef by rfl (Cycle 39) ⭐**
- **`mem_of_algebraMap_mem_map`: Reverse direction via comap_map_of_isPrime_disjoint (Cycle 41) ⭐⭐**
- **`algebraMap_isUnit_iff_not_mem`: IsUnit ↔ not in ideal (Cycle 41) ⭐⭐**
- **`dvr_intValuation_of_isUnit`: Units have intVal = 1 (Cycle 41) ⭐⭐**
- **`dvr_intValuation_eq_one_iff_not_mem_maxIdeal`: intVal = 1 characterization (Cycle 41) ⭐⭐**

### Typeclass Hierarchy
```
LocalGapBound R K          -- PROVABLE (gap ≤ 1 via evaluation map)
    ↑ extends
SinglePointBound R K       -- PROJECTIVE (adds ell_zero = 1)

BaseDim R K                -- SEPARATE (explicit base dimension)
```

---

## Current Sorry Count (after Cycle 41)

**By Module**:
| Module | Sorries | Build Status |
|--------|---------|--------------|
| Basic.lean | 0 | ✅ |
| Divisor.lean | 0 | ✅ |
| RRSpace.lean | 1 | ✅ (placeholder) |
| Typeclasses.lean | 0 | ✅ |
| RiemannInequality.lean | 1 | ✅ (placeholder) |
| Infrastructure.lean | 1 | ✅ (WIP) |
| LocalGapInstance.lean | ~45 | ✅ BUILDS (Cycle 41 fixed errors) |

**Key Active Blockers** (in `LocalGapInstance.lean`):
| Name | Status | Notes |
|------|--------|-------|
| `mem_asIdeal_iff_mem_maxIdeal` | **UNBLOCKED** | Foundation - now completable via Cycle 41 lemmas |
| `dvr_intValuation_unit` | **UNBLOCKED** | Unit case - now completable via Cycle 41 lemmas |
| `dvr_intValuation_of_algebraMap'` | **CYCLE 42 TARGET** | DVR intVal = v.intVal on R |
| `dvr_intValuation_of_algebraMap` | **KEY HELPER** | Same target (Cycle 38) |
| `dvr_valuation_eq_height_one'` | **ORIGINAL BLOCKER** | DVR valuation = HeightOneSpectrum valuation (Cycle 37) |

**Cycle 39 Candidates** (8 total, 2 PROVED):
- `ideal_span_map_singleton` - **PROVED** (Ideal.map_span + Set.image_singleton)
- `algebraMap_uniformizer_dvr_uniformizer` - SORRY (uniformizer maps to uniformizer)
- `dvr_intValuation_unfold` - **PROVED** (rfl)
- `mem_asIdeal_iff_mem_maxIdeal` - SORRY (**CRITICAL** - foundation)
- `dvr_intValuation_of_algebraMap'` - SORRY (**TARGET**)
- `mem_asIdeal_pow_iff_mem_maxIdeal_pow` - SORRY (generalizes to powers)
- `dvr_intValuation_uniformizer_pow` - SORRY (uniformizer power case)
- `dvr_intValuation_unit` - SORRY (**CRITICAL** - unit case)

**Reflector Ranking (Top 2)**:
1. `mem_asIdeal_iff_mem_maxIdeal` (9.5/10) - foundation for all
2. `dvr_intValuation_unit` (8.5/10) - unit base case

**Note**: 2/8 candidates PROVED (Cycle 39). Next priority: prove Candidates 4 and 8.

---

## Cycle 37 Accomplishments

**Goal**: Complete the converse direction `valuationRingAt_subset_range_algebraMap`

**Results**: 7/8 candidates compile, 1 sorry (KEY BLOCKER)

**Key Achievement**: Complete proof structure!
- **`dvr_valuationSubring_eq_range`**: Uses `IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring` (PROVED)
- **`dvr_valuationSubring_eq_valuationRingAt`**: Shows DVR's valuationSubring = our valuationRingAt (PROVED*)
- **`valuationRingAt_subset_range_algebraMap'`**: TARGET LEMMA - 2-line proof via rewrites (PROVED*)
- **`valuationSubring_eq_localization_image_complete`**: Full set equality (PROVED*)

**New Blocker**: `dvr_valuation_eq_height_one'` - need to show:
```lean
(IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K g =
  v.valuation K g
```

**Why this should work**:
1. DVR's maximalIdeal = `IsLocalRing.maximalIdeal (Loc.AtPrime v.asIdeal)` = `Ideal.map v.asIdeal`
2. Both valuations measure divisibility by the same prime ideal
3. Need to show the extendToLocalization definitions agree

**Once blocker resolved**: All 7 conditional lemmas automatically complete, and set equality is PROVED.

---

## Cycle 36 Accomplishments

**Goal**: Prove valuationRingAt = range(algebraMap from Localization.AtPrime)

**Results**: 5/8 candidates PROVED
- **`algebraMap_localization_mk'_eq_div'`**: mk' → r/s division in K (PROVED via mk'_spec + scalar tower)
- **`range_algebraMap_subset_valuationRingAt`**: Forward direction (PROVED via mk_mem_valuationRingAt)
- **`localRing_maximalIdeal_eq_map'`**: Wrapper for Cycle 33 lemma (PROVED)
- **`valuationRingAt_eq_localization_valuationRing`**: Definitional equality (PROVED via rfl)
- **`valuation_eq_intValuation_extendToLocalization`**: Definition unwrapping (PROVED via rfl)

**Key Insight**: Forward direction `range(algebraMap) ⊆ valuationRingAt` is now complete!
The proof uses:
1. `IsLocalization.surj` to write localization elements as mk'
2. Show mk' → r/s in K via calc block
3. Apply `mk_mem_valuationRingAt` (Cycle 33)

**Remaining Blocker**: `valuationRingAt_subset_range_algebraMap` - need to show v(g) ≤ 1 implies g comes from localization

---

## Cycle 34 Accomplishments

**Goal**: Prove valuation equality → get converse for free (per Frontier Freeze Rule, no new scaffolding)

**Results**: 4/6 candidates PROVED
- **`valuation_of_fraction`**: v(a/b) = intVal(a)/intVal(b) (PROVED via valuation_of_mk')
- **`intValuation_le_of_div_le_one`**: v(a/b) ≤ 1 ⟹ intVal(a) ≤ intVal(b) (PROVED)
- **`intValuation_eq_one_of_not_mem'`**: b ∉ v.asIdeal ⟹ intVal(b) = 1 (PROVED, trivial wrapper)
- **`intValuation_lt_one_of_mem`**: b ∈ v.asIdeal ⟹ intVal(b) < 1 (PROVED, trivial wrapper)
- `exists_coprime_rep`: SORRY - **KEY BLOCKER** (partial proof: easy case done, hard case needs uniformizer)
- `valuationRingAt_exists_fraction_v2`: SORRY (wrapper for exists_coprime_rep)

**Candidates 7-8 REMOVED**: localizationToFractionRing infrastructure required type class juggling not essential for this cycle.

**Key Progress on `exists_coprime_rep`**:
```lean
lemma exists_coprime_rep (v : HeightOneSpectrum R) (g : K)
    (hg : g ∈ valuationRingAt v) :
    ∃ (r s : R), s ∉ v.asIdeal ∧ algebraMap R K s ≠ 0 ∧ g = algebraMap R K r / algebraMap R K s
```
- **Easy case PROVED**: If b ∉ v.asIdeal, done with r=a, s=b
- **Hard case partial**: If b ∈ v.asIdeal, then v(g) ≤ 1 implies intVal(a) ≤ intVal(b), hence a ∈ v.asIdeal too
- **Remaining**: Factor out uniformizers to reduce to coprime form

**Mathematical Insight for Cycle 35**:
When both a, b ∈ v.asIdeal with v(a/b) ≤ 1:
- a = π^n · a' and b = π^m · b' where π is uniformizer
- intVal(a) ≤ intVal(b) means n ≥ m (since intVal(π^k) = exp(-k))
- So g = (π^(n-m) · a') / b' where b' ∉ v.asIdeal

This needs either:
1. Uniformizer factorization lemma (leads to instance hell - avoid)
2. OR induction on v.intValuation (cleaner approach)
3. OR direct use of DVR structure on Localization.AtPrime

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
| 34 | **Arithmetic lemmas PROVED** (4/6), partial proof of exists_coprime_rep (easy case done) |

---

## Key References
- mathlib: `RingTheory.DedekindDomain.*`
- mathlib: `RingTheory.Length` (Module.length_eq_add_of_exact)
- mathlib: `Ideal.ResidueField` for κ(v)
- mathlib: `ValuationSubring` for valuation ring

---

## Cycle 36 Tactical Guide

### Context (After Cycle 35)

**Cycle 35 Achievement**: IsFractionRing instance chain PROVED!
- `primeCompl_isUnit_in_K`: primeCompl elements become units in K ✅
- `localizationToK`: Ring hom via IsLocalization.lift ✅
- `algebraLocalizationK`: Algebra instance ✅
- `scalarTowerLocalizationK`: Scalar tower R → Loc.AtPrime → K ✅
- `localization_isFractionRing`: IsFractionRing (Loc.AtPrime v.asIdeal) K ✅

**Path A Status**: PARTIALLY COMPLETE
- Step 1: IsFractionRing ✅ DONE (Cycle 35)
- Step 2: Valuation comparison ❌ NEW BLOCKER
- Step 3: exists_lift_of_le_one (ready once Step 2 done)
- Step 4: Unpack result ✅ localization_surj_representation ready

### CURRENT BLOCKER: dvr_valuation_eq_height_one

```lean
lemma dvr_valuation_eq_height_one (v : HeightOneSpectrum R) (g : K) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K g =
      v.valuation K g
```

**Why This Should Work**:
1. `IsDiscreteValuationRing.maximalIdeal` on Loc.AtPrime is defined from `IsLocalRing.maximalIdeal`
2. `IsLocalRing.maximalIdeal (Loc.AtPrime v.asIdeal) = map v.asIdeal` (PROVED: `localization_maximalIdeal_eq_map`)
3. Both valuations are defined from the same underlying prime ideal v.asIdeal
4. They should be extensionally equal on K

**Search for Cycle 36**:
```bash
# Find valuation comparison lemmas
./scripts/rg_mathlib.sh "HeightOneSpectrum.*valuation.*eq|valuation.*HeightOneSpectrum.*eq"
./scripts/rg_mathlib.sh "intValuation.*IsLocalization|IsLocalization.*intValuation"

# Check how DVR maximalIdeal valuation is defined
rg -n "def valuation.*maximalIdeal|maximalIdeal.*valuation" .lake/packages/mathlib/Mathlib/RingTheory/Valuation/Discrete/
```

---

### Alternative: valuationSubring_eq_localization_image

If valuation comparison is too complex, prove set equality directly:
```lean
lemma valuationSubring_eq_localization_image (v : HeightOneSpectrum R) :
    (valuationRingAt (R := R) (K := K) v : Set K) =
      Set.range (algebraMap (Localization.AtPrime v.asIdeal) K)
```

**Approach**:
- (⊇) PROVED: `mk_mem_valuationRingAt` shows fractions are in valuationRingAt
- (⊆) Need: If v(g) ≤ 1, then g ∈ range(algebraMap)

---

### Success Criteria for Cycle 36

**Option 1 (Preferred)**: Prove `dvr_valuation_eq_height_one`
- Then `exists_lift_of_le_one` applies directly
- `exists_localization_lift` follows
- `exists_coprime_rep_via_lift` follows

**Option 2 (Backup)**: Prove `valuationSubring_eq_localization_image`
- Direct set equality bypasses valuation comparison
- Still gives exists_coprime_rep

### Victory Path (Once Blocker Resolved)
```
dvr_valuation_eq_height_one OR valuationSubring_eq_localization_image
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
