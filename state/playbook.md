# Playbook (Curator maintained)

## Heuristics
- Prefer line-bundle / invertible-sheaf RR statements; divisor RR is a wrapper.
- Use `finrank k` for dimensions; avoid `Nat`-based dims until the end.
- Keep lemma statements small: fewer binders, fewer coercions, fewer implicit arguments.
- When stuck on coercions, introduce explicit `let` bindings for objects (e.g. `L : LineBundle X`).

## Current Status Summary

**RR.lean (v1)**: Axiom-based approach with `FunctionFieldDataWithRR`. Complete but circular.

**RR_v2.lean (v2)**: Constructive Dedekind domain approach. Key results:
- `RRModuleV2_real`: Valuation-based L(D) definition (PROVED)
- `ellV2_real_mono`: Monotonicity via Module.length (PROVED)
- `riemann_inequality_real`: Conditional on `[SinglePointBound R K]` (PROVED)
- `riemann_inequality_affine`: Conditional on `[LocalGapBound R K] [BaseDim R K]` (PROVED) ✅ NEW

**Typeclass Hierarchy (Cycle 23)**:
```
LocalGapBound R K          -- PROVABLE (gap ≤ 1 via evaluation map)
    ↑ extends
SinglePointBound R K       -- PROJECTIVE (adds ell_zero = 1)

BaseDim R K                -- SEPARATE (explicit base dimension)
```

---

## CYCLE 24 PLAN: Prove LocalGapBound Instance

### Goal
Prove `instance : LocalGapBound R K` via evaluation map, making `riemann_inequality_affine` unconditional.

### Implementation Tasks

#### 1. Extract uniformizer at height-1 prime
```lean
-- Use DVR structure from localization_at_prime_is_dvr
-- Need to extract uniformizer π_v from mathlib DVR API
noncomputable def uniformizerAt (v : HeightOneSpectrum R) : K := ...
```

#### 2. Define evaluation map
```lean
-- ev_v : L(D + v) → κ(v) by extracting coefficient of π_v^{-1}
noncomputable def evaluationMapAt (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    RRModuleV2_real R K (D + DivisorV2.single v 1) →ₗ[R] residueFieldAtPrime R v := ...
```

#### 3. Prove kernel containment
```lean
-- The kernel of ev_v contains L(D)
lemma evaluationMapAt_ker_contains (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    RRModuleV2_real R K D ≤ LinearMap.ker (evaluationMapAt v D) := ...
```

#### 4. Prove dimension bound
```lean
-- dim(L(D+v) / L(D)) ≤ 1
lemma dim_quotient_le_one (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    Module.finrank R (RRModuleV2_real R K (D + DivisorV2.single v 1) ⧸
                      (RRModuleV2_real R K D).comap ...) ≤ 1 := ...
```

#### 5. Instantiate LocalGapBound
```lean
instance : LocalGapBound R K where
  gap_le_one D v := ...  -- from dim_quotient_le_one
```

### Victory Condition for Cycle 24
- [ ] evaluationMapAt defined
- [ ] Kernel containment proved
- [ ] instance : LocalGapBound R K (making riemann_inequality_affine unconditional)

### Blockers
- mathlib DVR API may be limited
- May need `HeightOneSpectrum.valuation` lemmas
- Uniformizer extraction may require additional work

---

## Historical Cycles (Summary)

| Cycle | Achievement |
|-------|-------------|
| 1-3 | RRData structure, statement elaborates |
| 4-6 | Divisor, FunctionFieldData, RRSpace as k-Submodule |
| 7-9 | ell = finrank, quotient infrastructure |
| 10-11 | SinglePointBound axiom, **Riemann inequality PROVED** |
| 12-16 | Full RR structure, Clifford's theorem |
| 17 | **PIVOT**: Created RR_v2.lean with Dedekind domains |
| 18-19 | Valuation-based L(D), RRModuleV2_real complete |
| 20 | ellV2_real_mono PROVED |
| 21 | SinglePointBound typeclass, riemann_inequality_real PROVED |
| 22 | **DISCOVERY**: Affine model limitation, residue field infrastructure |
| 23 | **LocalGapBound hierarchy, riemann_inequality_affine PROVED** |
| 24 | (PLANNED) LocalGapBound instance via evaluation map |

---

## Key References
- mathlib: `RingTheory.DedekindDomain.*`
- mathlib: `RingTheory.Length` (Module.length_eq_add_of_exact)
- mathlib: `Ideal.ResidueField` for κ(v)
