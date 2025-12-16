# Playbook (Curator maintained)

## Heuristics
- Prefer line-bundle / invertible-sheaf RR statements; divisor RR is a wrapper.
- Use `finrank k` for dimensions; avoid `Nat`-based dims until the end.
- Keep lemma statements small: fewer binders, fewer coercions, fewer implicit arguments.
- When stuck on coercions, introduce explicit `let` bindings for objects (e.g. `L : LineBundle X`).

## Current Status Summary (Cycle 29)

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
- **`shifted_element_valuation_le_one_v2`: KEY BLOCKER RESOLVED (Cycle 29)**

### Typeclass Hierarchy
```
LocalGapBound R K          -- PROVABLE (gap ≤ 1 via evaluation map)
    ↑ extends
SinglePointBound R K       -- PROJECTIVE (adds ell_zero = 1)

BaseDim R K                -- SEPARATE (explicit base dimension)
```

---

## Current Sorry Count (RR_v2.lean after Cycle 29)

| Line | Name | Status | Notes |
|------|------|--------|-------|
| 335 | `ellV2_mono` | DEPRECATED | Superseded by `ellV2_real_mono` |
| 713 | `riemann_inequality` | DEPRECATED | Superseded by `riemann_inequality_real` |
| 989 | `shifted_element_valuation_le_one` | SUPERSEDED | By `_v2` version in Cycle 29 section |
| 1029 | `evaluationMapAt` | BLOCKER | Can use `evaluationMapAt_via_bridge` once bridge ready |
| 1040 | `kernel_evaluationMapAt` | BLOCKED | Depends on evaluationMapAt |
| 1049 | `instLocalGapBound` | BLOCKED | Depends on kernel proof |
| 1315 | `residueFieldBridge` | **ACTIVE** | Next cycle focus |
| 1322 | `residueFieldBridge_algebraMap_comm` | BLOCKED | Depends on bridge |
| 1331 | `evaluationMapAt_via_bridge` | BLOCKED | Depends on bridge |

**Total**: 9 sorries (2 deprecated, 1 superseded, 6 active path)

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

## Active Edge: Residue Field Bridge

**Goal**: Construct `evaluationMapAt : L(D+v) →ₗ[R] κ(v)`

**Current Strategy** (Cycle 26):
1. For f ∈ L(D+v), compute g = f · π^{D(v)+1}
2. Show v(g) ≤ 1 → g ∈ `valuationRingAt v` (LOCAL condition)
3. Apply `valuationRingAt.residue` to get element in `valuationRingAt.residueField v`
4. **GAP**: Bridge to `residueFieldAtPrime R v` (our target κ(v))

**Why Valuation Ring Approach Works**:
- Shifted element may have poles at OTHER primes (so g ∉ R in general)
- But g has valuation ≤ 1 at v specifically (local condition)
- Valuation ring is LOCAL - only cares about single prime v
- Can apply residue map locally without global integrality

**Gap to Close**:
- `valuationRingAt.residueField v` ≠ `residueFieldAtPrime R v` definitionally
- Need isomorphism or proof they're equivalent for Dedekind domains
- Both are "residue field at v" but constructed differently

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

This requires:
1. Fix `shifted_element_valuation_le_one` (use WithZero.exp helpers)
2. Construct `evaluationMapAt` (bridge residue fields)
3. Prove `kernel_evaluationMapAt`
4. Apply `local_gap_bound_of_exists_map`

---

## Cycle 30 Tactical Guide

### Task 1: Construct `residueFieldBridge` (Priority: HIGH, Risk: MEDIUM)

**Location**: Line 1315 in RR_v2.lean

**Goal**: Prove `valuationRingAt.residueField v ≃+* residueFieldAtPrime R v`

**Path A: Use DVR isomorphism (RECOMMENDED)**
```
For Dedekind domains at height-1 prime v:
1. Localization.AtPrime v.asIdeal is a DVR (already known)
2. DVRs have unique valuation → valuation ring = ring itself
3. IsDiscreteValuationRing.equivValuationSubring gives: DVR A ≃+* valuationSubring
4. Compose: Localization.AtPrime ≃ valuationRingAt v
5. Residue fields are functorial → residueFieldAtPrime ≃ valuationRingAt.residueField
```

**Key Mathlib Lemma** (discovered Cycle 29):
```
IsDiscreteValuationRing.equivValuationSubring :
    A ≃+* ((maximalIdeal A).valuation K).valuationSubring
```
Located in: `Mathlib/RingTheory/Valuation/Discrete/Basic.lean:503`

**Path B: Direct construction via quotient isomorphism**
Both residue fields are quotients of local rings by their maximal ideals:
- `residueFieldAtPrime R v` = R / v.asIdeal
- `valuationRingAt.residueField v` = valuationRingAt / maxIdeal

Show the maximal ideals correspond under the embedding.

**Path C (Fallback): Bypass bridge entirely**
If bridge is too hard, redefine target to use `valuationRingAt.residueField` directly:
1. Define `evaluationMapAt' : L(D+v) →ₗ[R] valuationRingAt.residueField v`
2. Prove `Module.length R (valuationRingAt.residueField v) = 1` (DVR residue field is simple)
3. Use `local_gap_bound_of_exists_map` variant targeting `valuationRingAt.residueField`

**Decision Point**: If Path A takes >45 min, switch to Path C.

---

### Task 2: Residue Field Bridge (COMPLETED in Cycle 29)

**The Problem**:
- We have `valuationRingAt.residueField v` (from ValuationSubring)
- We need `residueFieldAtPrime R v` (= `v.asIdeal.ResidueField`)
- `local_gap_bound_of_exists_map` expects the latter

**Investigation Paths** (try in order):

**Path A: Find existing isomorphism in mathlib**
```
Search queries:
- "ValuationSubring.*residue.*Localization"
- "equivValuationSubring" (in RingTheory/Valuation/Discrete/Basic.lean)
- "IsDiscreteValuationRing.*residue"
```

For Dedekind domains at height-1 primes:
- `Localization.AtPrime v.asIdeal` is a DVR
- DVRs have unique valuation → their valuation ring = themselves
- So `valuationRingAt v ≃ Localization.AtPrime v.asIdeal`?

**Path B: Reformulate target to use valuationRingAt.residueField**
If the bridge is hard, consider:
1. Redefine `residueFieldAtPrime` as `valuationRingAt.residueField`
2. OR prove `residueFieldAtPrime.isSimpleModule` for `valuationRingAt.residueField` directly
3. This avoids the bridge entirely

**Path C: Direct construction**
Build `evaluationMapAt` targeting `valuationRingAt.residueField v`:
```lean
def evaluationMapAt' (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    RRModuleV2_real R K (D + DivisorV2.single v 1) →ₗ[R]
    valuationRingAt.residueField (R := R) (K := K) v := ...
```
Then prove `valuationRingAt.residueField` has length 1 (it should, as residue field of a DVR).

**Decision Point**: If Path A takes >30 min of searching, switch to Path B or C.

---

### Task 3: evaluationMapAt Construction (after Task 2 resolved)

**Once residue field target is decided**, the construction is:
```lean
def evaluationMapAt v D : L(D+v) →ₗ[R] target_residue_field := {
  toFun := fun ⟨f, hf⟩ =>
    let g := f * algebraMap R K (uniformizerAt v ^ (D v + 1).toNat)
    let hg : v.valuation K g ≤ 1 := shifted_element_valuation_le_one v D f hf
    partialResidueMap v g hg  -- or composed with bridge
  map_add' := ... -- use partialResidueMap_add
  map_smul' := ... -- use partialResidueMap_smul
}
```

**Key Challenge**: The linearity proofs need to show that shifting by π^n is compatible with addition/scalar multiplication. This should follow from:
- `algebraMap` is a ring homomorphism
- Multiplication distributes

---

### Fallback Strategy

If both residue field approaches prove difficult:

**Option: Axiomatize the evaluation map temporarily**
Add to a new typeclass `HasEvaluationMap R K`:
```lean
class HasEvaluationMap ... where
  evaluationMapAt : ∀ v D, L(D+v) →ₗ[R] residueFieldAtPrime R v
  kernel_condition : ∀ v D, ker (evaluationMapAt v D) = range (inclusion ...)
```

This would let us:
1. Complete `instLocalGapBound` conditionally
2. Make `riemann_inequality_affine` work with `[HasEvaluationMap R K]`
3. Defer the construction to a future cycle

**Risk**: Adds another assumption layer. Use only if stuck >2 cycles.

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

---

## Key References
- mathlib: `RingTheory.DedekindDomain.*`
- mathlib: `RingTheory.Length` (Module.length_eq_add_of_exact)
- mathlib: `Ideal.ResidueField` for κ(v)
- mathlib: `ValuationSubring` for valuation ring
