# Playbook (Curator maintained)

## Heuristics
- Prefer line-bundle / invertible-sheaf RR statements; divisor RR is a wrapper.
- Use `finrank k` for dimensions; avoid `Nat`-based dims until the end.
- Keep lemma statements small: fewer binders, fewer coercions, fewer implicit arguments.
- When stuck on coercions, introduce explicit `let` bindings for objects (e.g. `L : LineBundle X`).

## Current Status Summary (Cycle 26)

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

### Typeclass Hierarchy
```
LocalGapBound R K          -- PROVABLE (gap ≤ 1 via evaluation map)
    ↑ extends
SinglePointBound R K       -- PROJECTIVE (adds ell_zero = 1)

BaseDim R K                -- SEPARATE (explicit base dimension)
```

---

## Current Sorry Count (RR_v2.lean)

| Line | Name | Status | Notes |
|------|------|--------|-------|
| 337 | `ellV2_mono` | DEPRECATED | Superseded by `ellV2_real_mono` |
| 715 | `riemann_inequality` | DEPRECATED | Superseded by `riemann_inequality_real` |
| 1001 | `shifted_element_valuation_le_one` | ACTIVE | WithZero.exp arithmetic (proof path clear) |
| 1030 | `evaluationMapAt` | **BLOCKER** | Needs residue field bridge |
| 1042 | `kernel_evaluationMapAt` | BLOCKED | Depends on evaluationMapAt |
| 1061 | `instLocalGapBound` | BLOCKED | Depends on kernel proof |

**Total**: 6 sorries (2 deprecated, 4 active)

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

### Cycle 24-26 Infrastructure (All PROVED unless noted)

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

**Helpers (Cycle 26)**:
- `withzero_exp_mul` : exp(a) * exp(b) = exp(a+b)
- `withzero_exp_neg` : exp(-a) = (exp a)⁻¹

---

## Victory Condition

- [ ] `instance : LocalGapBound R K` (makes riemann_inequality_affine unconditional)

This requires:
1. Fix `shifted_element_valuation_le_one` (use WithZero.exp helpers)
2. Construct `evaluationMapAt` (bridge residue fields)
3. Prove `kernel_evaluationMapAt`
4. Apply `local_gap_bound_of_exists_map`

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

---

## Key References
- mathlib: `RingTheory.DedekindDomain.*`
- mathlib: `RingTheory.Length` (Module.length_eq_add_of_exact)
- mathlib: `Ideal.ResidueField` for κ(v)
- mathlib: `ValuationSubring` for valuation ring
