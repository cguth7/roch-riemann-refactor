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

## CYCLE 24 RESULTS: Phase 1 - Linear Algebra Bridge PROVED

### Summary
Cycle 24 was split into two phases per strategic override. Phase 1 implemented the **Linear Algebra Bridge** - a conditional lemma that establishes the bound assuming an evaluation map exists.

### Phase 1 Results (COMPLETED)
| Definition/Lemma | Status | Notes |
|-----------------|--------|-------|
| `divisor_le_add_single` | ✅ **PROVED** | D ≤ D + single v 1 |
| `HeightOneSpectrum.isMaximal` | ✅ **PROVED** | Height-1 primes are maximal in Dedekind domains |
| `residueFieldAtPrime.linearEquiv` | ✅ **PROVED** | R ⧸ v.asIdeal ≃ₗ[R] κ(v) via bijective algebraMap |
| `residueFieldAtPrime.isSimpleModule` | ✅ **PROVED** | κ(v) is simple R-module (uses linearEquiv) |
| `residueFieldAtPrime.length_eq_one` | ✅ **PROVED** | Module.length R (κ(v)) = 1 |
| `local_gap_bound_of_exists_map` | ✅ **PROVED** | **LINEAR ALGEBRA BRIDGE** |

### Key Lemma (PROVED)
```lean
lemma local_gap_bound_of_exists_map
    (D : DivisorV2 R) (v : HeightOneSpectrum R)
    (φ : ↥(RRModuleV2_real R K (D + DivisorV2.single v 1)) →ₗ[R] residueFieldAtPrime R v)
    (h_ker : LinearMap.ker φ = LinearMap.range (Submodule.inclusion ...)) :
    ellV2_real_extended R K (D + DivisorV2.single v 1) ≤ ellV2_real_extended R K D + 1
```

**Mathematical Content**: IF there exists φ : L(D+v) → κ(v) with ker φ = L(D), THEN ℓ(D+v) ≤ ℓ(D) + 1.

**Proof Strategy**:
1. Exact sequence: length(L(D+v)) = length(L(D)) + length(range φ)
2. Since range φ ⊆ κ(v) and κ(v) is simple, length(range φ) ≤ 1
3. Therefore: ℓ(D+v) ≤ ℓ(D) + 1

### Phase 2 Results (Cycle 24 Session 3) - PARTIAL COMPLETE
- ✅ `residueFieldAtPrime.linearEquiv` PROVED via bijective algebraMap
- ✅ `residueFieldAtPrime.isSimpleModule` PROVED using the linearEquiv

**Key Discovery**: `Ideal.bijective_algebraMap_quotient_residueField` in mathlib
- When I is maximal, `algebraMap (R ⧸ I) I.ResidueField` is bijective
- This gives us `R ⧸ v.asIdeal ≃ₗ[R] κ(v)` directly
- No need for IsFractionRing plumbing

**Proof Strategy for linearEquiv**:
```lean
-- Use bijective algebraMap to construct LinearEquiv
have hbij := Ideal.bijective_algebraMap_quotient_residueField v.asIdeal
exact LinearEquiv.ofBijective { toFun := algebraMap ..., map_add', map_smul' } hbij
```

### Phase 2 Tasks (REMAINING)
- [ ] Construct `evaluationMapAt v D : L(D+v) →ₗ[R] κ(v)`
- [ ] Prove kernel condition: ker(evaluationMapAt) = range(inclusion)
- [ ] Instantiate `LocalGapBound R K`

### Victory Condition for Phase 2
- [ ] instance : LocalGapBound R K (making riemann_inequality_affine unconditional)

### Current Sorry Count (RR_v2.lean)
1. Line 335: `ellV2_mono` (deprecated, superseded by `ellV2_real_mono`)
2. Line 713: `riemann_inequality` (deprecated, superseded by `riemann_inequality_real`)

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
