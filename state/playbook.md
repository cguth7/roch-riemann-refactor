# Playbook

Strategic guide for formalizing Riemann-Roch. Updated Cycle 284.

---

## State Folder Overview

```
state/
├── playbook.md          # This file - strategy, heuristics, lessons learned
├── ledger.md            # Tactical tracking - current cycle, recent changes, next steps
├── ledger_archive.md    # Historical cycles 1-240
├── PROOF_CHAIN.md       # Import chain from theorems to Mathlib, file status
├── REFACTOR_PLAN.md     # Roadmap for generalizing P¹ → arbitrary curves
└── INVENTORY_REPORT.md  # Deep scan of all files (from Cycle 241 refactor)
```

| File | When to read | When to update |
|------|--------------|----------------|
| `ledger.md` | Start of every cycle | End of every cycle |
| `playbook.md` | When stuck or planning | When learning new lessons |
| `PROOF_CHAIN.md` | After adding new files | After connecting files to chain |
| `REFACTOR_PLAN.md` | When planning next phase | After completing a phase |
| `INVENTORY_REPORT.md` | Reference only | Rarely (was a one-time scan) |

---

## Cycle Discipline

**Critical Lesson from Cycles 230-241**: We got impatient near the end and tried to do too much per cycle. This led to context overflow, incomplete work, and debugging spirals.

### The ~50k Token Reality

Each Claude cycle has ~50k usable tokens of context. This means:
- **Read**: ~3-5 files deeply, or ~10 files shallowly
- **Write**: ~200-400 lines of new code max
- **Debug**: 2-3 error-fix iterations before context exhaustion

### One Cycle = One Focused Goal

**Good cycle scope**:
- Fill ONE sorry with a clean proof
- Add ONE new definition + basic lemmas
- Fix ONE compilation error chain
- Refactor ONE file (extract/reorganize)

**Bad cycle scope**:
- "Fill all sorries in this file" (unless trivial)
- "Implement the full residue theorem"
- "Refactor the adelic infrastructure"

### Ledger Discipline

The ledger should contain:
1. **Current state**: Build status, sorry count, cycle number
2. **Cycle summary**: What was done, what was proved
3. **Next steps**: Options for next cycle

---

## Ultimate Goal

Formalize the **Riemann-Roch theorem** for **arbitrary smooth projective curves** over finite fields in Lean 4 — **no axioms, no sorries**:

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

### Current Status (Cycle 284)

| Component | Status | Sorries |
|-----------|--------|---------|
| P¹ Riemann-Roch formula | ✅ Complete | 0 |
| P¹ Serre duality (effective D) | ✅ Complete | 0 |
| Valuation-degree infrastructure | ✅ Complete | 0 |
| AdelicH1Full.lean | ⚠️ 1 accepted debt | 1 |
| Abstract.lean edge cases | ⚠️ Low priority | 8 |

**Total sorries**: 9 (1 technical debt + 8 edge cases)

---

## What's Proved

```lean
-- Main Serre duality for P¹ (effective divisors with non-negative inftyCoeff)
theorem serre_duality_p1 (D : ExtendedDivisor (Polynomial Fq))
    (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    h1_finrank_full Fq D = ell_proj_ext Fq (canonicalExtended Fq - D)

-- Full P¹ Riemann-Roch formula
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) : ell_ratfunc_projective D = D.deg.toNat + 1

-- Valuation-degree relationship (key infrastructure)
lemma natDegree_ge_degWeighted_of_valuation_bounds (D : DivisorV2 (Polynomial k))
    (hD_eff : D.Effective) (p : Polynomial k) (hp_ne : p ≠ 0)
    (hval : ∀ v ∈ D.support, v.intValuation p ≤ exp(-(D v))) :
    (p.natDegree : ℤ) ≥ degWeighted k D
```

---

## Architecture

### Key File Structure
```
RrLean/RiemannRochV2/
├── Core/                   # Basic types
│   ├── Basic.lean
│   └── Divisor.lean
├── Definitions/            # Infrastructure
│   ├── Infrastructure.lean
│   └── RRDefinitions.lean
├── Adelic/                 # Adele ring theory
│   ├── FullAdelesBase.lean
│   ├── FullAdelesCompact.lean
│   └── AdelicH1v2.lean
├── P1Instance/             # P¹-specific (all sorry-free)
│   ├── PlaceDegree.lean    # ✅ Valuation-degree lemmas
│   ├── P1Place.lean
│   ├── P1Canonical.lean
│   └── P1VanishingLKD.lean
├── SerreDuality/
│   ├── General/
│   │   ├── AdelicH1Full.lean  # 1 accepted sorry
│   │   └── Abstract.lean      # 8 edge case sorries
│   └── P1Specific/
│       └── RatFuncPairing.lean
└── ResidueTheory/          # All sorry-free
```

---

## Heuristics

### Coprimality Pattern (Cycle 284 Lesson)
For proving products divide in k[X]:
```lean
-- Use these lemmas from PlaceDegree.lean:
generator_not_mem_other_prime  -- gen_v ∉ w.asIdeal for v ≠ w
Irreducible.coprime_iff_not_dvd -- coprimality from non-divisibility
IsCoprime.pow                   -- lift to powers
Finset.prod_dvd_of_coprime      -- product divides if pairwise coprime
```

### Valuation-Degree Pattern (Cycle 284 Lesson)
For polynomial degree bounds from valuation constraints:
```lean
-- Key chain:
valuation_of_algebraMap         -- v.valuation(algebraMap p) = v.intValuation p
natDegree_ge_degWeighted_of_valuation_bounds  -- valuation → degree bound
degWeighted_ge_deg              -- weighted ≥ unweighted for effective D
```

### WithZero Valuation Anti-Pattern
When proving properties about valuations in `WithZero (Multiplicative ℤ)`:
- **DON'T**: Try to compute with valuation outputs
- **DO**: Work with polynomial structure and divisibility

### Affine vs Projective Trap
- `RRSpace_proj` (affine) gives ℓ(0) = ∞ for P¹
- `RRSpace_proj_ext` (projective) gives ℓ(0) = 1 for P¹
- **Rule**: For projective curves, use `ProjectiveAdelicRRData`

---

## Verification Commands

```bash
# Check sorry count
lake build 2>&1 | grep -E "sorry|^error:"

# Check specific file
grep -n "sorry" RrLean/RiemannRochV2/P1Instance/PlaceDegree.lean

# Full build
lake build
```

---

*Updated Cycle 284: PlaceDegree coprimality proof complete, AdelicH1Full degree-valuation sorry filled.*
