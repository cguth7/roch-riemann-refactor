# Playbook (Curator maintained)

## Heuristics
- Prefer line-bundle / invertible-sheaf RR statements; divisor RR is a wrapper.
- Use `finrank k` for dimensions; avoid `Nat`-based dims until the end.
- Keep lemma statements small: fewer binders, fewer coercions, fewer implicit arguments.
- When stuck on coercions, introduce explicit `let` bindings for objects (e.g. `L : LineBundle X`).

## Current Status Summary (Cycle 31)

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

### Typeclass Hierarchy
```
LocalGapBound R K          -- PROVABLE (gap ≤ 1 via evaluation map)
    ↑ extends
SinglePointBound R K       -- PROJECTIVE (adds ell_zero = 1)

BaseDim R K                -- SEPARATE (explicit base dimension)
```

---

## Current Sorry Count (RR_v2.lean after Cycle 31)

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
| 1496 | `exists_same_residue_class` | **ACTIVE** | **KEY BLOCKER** - density lemma |
| 1541 | `valuationRingAt_eq_fractions` | ACTIVE | Alternative approach |

**Total**: 14 sorries (2 deprecated, 3 superseded, 9 active path)

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

## Active Edge: Density Lemma (Cycle 31→32)

**Goal**: Prove `exists_same_residue_class` to unlock the residue field bridge

**Current State** (after Cycle 31):
```
R ──residueMapFromR──▶ valuationRingAt.residueField v
        │                          ≃ (once surjective)
        ▼                          ▼
   R/v.asIdeal ◀────────────── residueFieldAtPrime R v
```

**What We Have**:
- ✅ `residueMapFromR_ker = v.asIdeal` (Cycle 30)
- ✅ Conditional bridges: `residueFieldBridge_v2_of_surj`, `residueFieldBridge_v3_of_surj` (Cycle 31)
- ✅ Helper lemmas: `valuation_eq_one_of_not_mem`, `valuation_div_eq_of_unit` (Cycle 31)

**What We Need**:
- ❌ `exists_same_residue_class`: ∀ g ∈ valuationRingAt, ∃ r ∈ R, embedding(r) ≡ g (mod maxIdeal)

**Why This Unlocks Everything**:
1. `exists_same_residue_class` → `residueMapFromR_surjective`
2. surjective + ker = v.asIdeal → First Isomorphism Theorem applies
3. bridges become unconditional → `evaluationMapAt` can be constructed
4. kernel proof → `LocalGapBound` instance → victory

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

**Current Path** (after Cycle 31):
1. ~~Fix `shifted_element_valuation_le_one`~~ ✅ DONE (Cycle 29)
2. ~~ker(residueMapFromR) = v.asIdeal~~ ✅ DONE (Cycle 30)
3. ~~Conditional bridges ready~~ ✅ DONE (Cycle 31)
4. **BLOCKER**: Prove `exists_same_residue_class` (density lemma)
5. Then `residueMapFromR_surjective` follows
6. Then bridges become unconditional → evaluationMapAt → kernel → LocalGapBound

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

---

## Key References
- mathlib: `RingTheory.DedekindDomain.*`
- mathlib: `RingTheory.Length` (Module.length_eq_add_of_exact)
- mathlib: `Ideal.ResidueField` for κ(v)
- mathlib: `ValuationSubring` for valuation ring

---

## Cycle 32 Tactical Guide

### Task 1: Prove `exists_same_residue_class` (Priority: CRITICAL)

**Location**: Line 1496 in RR_v2.lean

**Goal**: Show R is "dense" in valuationRingAt v modulo maximalIdeal

**Proof Strategy**:
```lean
lemma exists_same_residue_class (v : HeightOneSpectrum R)
    (g : valuationRingAt v) :
    ∃ r : R, (embeddingToValuationRingAt v r) - g ∈ maximalIdeal (valuationRingAt v)
```

**Approach A: Use IsFractionRing.div_surjective**
1. Write g.val = a/b for a, b ∈ R (via `IsFractionRing.div_surjective`)
2. Since v(g) ≤ 1, we have v(a)/v(b) ≤ 1
3. **Case b ∉ v.asIdeal**: v(b) = 1, so v(a) ≤ 1 (always true for a ∈ R)
   - Take r = a
   - Need: v(a - g·b) < 1, i.e., v(a - a) = 0 ... this doesn't work directly
4. **Case b ∈ v.asIdeal**: v(b) < 1, so need different approach

**Approach B: Use Localization.AtPrime structure**
- Localization.AtPrime v.asIdeal consists of r/s for r ∈ R, s ∉ v.asIdeal
- For such elements, v(r/s) = v(r) (since v(s) = 1)
- If v(g) ≤ 1, can we express g as r/s with s ∉ v.asIdeal?
- This is essentially `valuationRingAt_eq_fractions`

**Approach C: Use DVR equivalence**
- `Localization.AtPrime v.asIdeal ≃+* valuationRingAt v` (via IsDiscreteValuationRing.equivValuationSubring)
- The residue field of Localization.AtPrime is R/v.asIdeal
- Bijective_algebraMap_quotient_residueField gives surjectivity for the localization
- Transport via the equivalence

**Decision Point**: Try Approach C first (uses existing mathlib results).

### Fallback: Alternative formulation

If `exists_same_residue_class` proves too hard, consider:
1. Prove `valuationRingAt_eq_fractions` first (every element is r/s with s ∉ v.asIdeal)
2. Then for g = r/s, take r as the approximation
3. Show algebraMap(r) - g = algebraMap(r) - r/s = r(s-1)/s lies in maximalIdeal
