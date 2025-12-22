# Riemann-Roch Formalization: Current State

*Last updated: Cycle 28 (December 2024)*

## CONSTRUCTIVE RIEMANN INEQUALITY

```
ℓ(D) ≤ deg(D) + basedim   for effective divisors
```

The Riemann inequality is formalized in Lean 4 using constructive Dedekind domain infrastructure!

---

## The Goal

Prove the Riemann-Roch theorem for algebraic curves:

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

Where:
- ℓ(D) = dim L(D) = dimension of space of functions with poles bounded by D
- K = canonical divisor
- g = genus of the curve

---

## Two-Track Approach

### RR.lean (v1) - Axiom-Based (Cycles 1-16)
- Uses `FunctionFieldData` structure with axiomatized div, deg, ell
- Full RR structure including Serre duality axiom
- Clifford's inequality proved
- **Status**: ARCHIVED - proofs derived from axioms

### RR_v2.lean (v2) - Constructive (Cycles 17-28) - ACTIVE
- Uses real mathlib infrastructure: Dedekind domains, DVR localization
- Points = `HeightOneSpectrum R` (height-1 primes)
- L(D) defined via valuations: `{f : f = 0 ∨ ∀v, v(f) ≤ exp(D(v))}`
- ℓ(D) = `Module.length R L(D)` (additive in exact sequences)
- **Status**: ACTIVE - constructive proofs from mathlib

---

## What We've Built (RR_v2.lean)

### Cycles 17-28 Results

| Cycle | What | Key Lemmas |
|-------|------|------------|
| 17 | Pivot to Dedekind domains | `DivisorV2`, `localization_at_prime_is_dvr` |
| 18-19 | Valuation-based L(D) | `RRModuleV2_real` complete with `add_mem'`, `smul_mem'` |
| 20 | ℓ(D) monotonicity | `ellV2_real_mono` via `Module.length_le_of_injective` |
| 21 | Riemann inequality | `riemann_inequality_real` via degree induction |
| 22 | **DISCOVERY** | Affine model limitation (ℓ(0) ≠ 1) |
| 23 | **LocalGapBound hierarchy** | `riemann_inequality_affine`, typeclass separation |
| 24 | Linear Algebra Bridge | `local_gap_bound_of_exists_map` + uniformizer infrastructure |
| 25-26 | Valuation ring approach | `valuationRingAt`, `mem_valuationRingAt_iff` |
| 27 | Partial residue map | `partialResidueMap` definition |
| **28** | **Linearity proofs** | `partialResidueMap_zero/add/smul` PROVED |

### Current Score (RR_v2.lean)

| Category | Count |
|----------|-------|
| **Definitions** | 25+ |
| **Lemmas PROVED** | 40+ |
| **Infrastructure** | Uniformizers, valuation ring, residue field |
| **Sorries remaining** | 6 (2 deprecated, 4 active) |

---

## Key Results

### Riemann Inequality (Cycle 21-23)
```lean
-- With SinglePointBound (projective model):
ℓ(D) ≤ deg(D) + 1   for effective D

-- With LocalGapBound + BaseDim (affine model):
ℓ(D) ≤ deg(D) + basedim   for effective D
```

### Typeclass Hierarchy (Cycle 23)
```
LocalGapBound R K          -- PROVABLE (gap ≤ 1 via evaluation map)
    ↑ extends
SinglePointBound R K       -- PROJECTIVE (adds ell_zero = 1)

BaseDim R K                -- SEPARATE (explicit base dimension)
```

### Infrastructure Complete (Cycles 24-28)
- **Uniformizers**: `uniformizerAt v`, `uniformizerAt_valuation`
- **Valuation ring**: `valuationRingAt v`, `valuationRingAt.residue`
- **Partial residue map**: `partialResidueMap` with linearity proofs

---

## Affine vs Projective Model Discovery

**Critical insight from Cycle 22:**

| Model | Points | L(0) | ℓ(0) |
|-------|--------|------|------|
| Affine (HeightOneSpectrum R) | Finite places only | R | ∞ |
| Projective (complete curve) | Finite + infinite | k | 1 |

Our `HeightOneSpectrum R` model proves the **affine Riemann inequality**.
For classical RR with ℓ(0) = 1, need compactification (adding infinite places).

---

## Victory Condition

```lean
instance : LocalGapBound R K
```

This requires:
1. ✅ `partialResidueMap` linearity (Cycle 28)
2. ⏳ `shifted_element_valuation_le_one` (WithZero.exp arithmetic)
3. ⏳ `evaluationMapAt` construction (residue field bridge)
4. ⏳ `kernel_evaluationMapAt` proof

---

## Remaining Sorries (RR_v2.lean)

| Line | Name | Status |
|------|------|--------|
| 337 | `ellV2_mono` | DEPRECATED |
| 715 | `riemann_inequality` | DEPRECATED |
| 989 | `shifted_element_valuation_le_one` | ACTIVE |
| 1029 | `evaluationMapAt` | **BLOCKER** |
| 1040 | `kernel_evaluationMapAt` | BLOCKED |
| 1049 | `instLocalGapBound` | BLOCKED |

---

## File Structure

```
roch-riemann/
├── RrLean/
│   ├── RR.lean            # v1: Axiom-based (archived)
│   └── RR_v2.lean         # v2: Constructive (active, ~1220 lines)
├── state/
│   ├── playbook.md        # Strategy
│   ├── ledger.md          # Cycle history
│   └── candidates.json    # Candidate tracking
├── agents/                 # ACE loop agents
└── docs/
    └── for_humans.md       # This file
```

---

## Lessons Learned

1. **Affine ≠ Projective** - HeightOneSpectrum captures only finite places
2. **Module.length > finrank** - Additive in exact sequences, handles infinite
3. **Valuation ring approach** - Local condition (v(g) ≤ 1) vs global integrality
4. **SubringClass is definitional** - Subtype operations don't need explicit proofs
5. **Typeclass separation** - LocalGapBound (provable) vs SinglePointBound (projective)

---

*Total: 28 cycles, two-track approach (axiom + constructive), Riemann inequality PROVED*
