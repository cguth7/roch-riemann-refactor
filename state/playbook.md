# Playbook

Strategic guide for formalizing Riemann-Roch. Updated Cycle 287.

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

---

## Ultimate Goal

Formalize **Riemann-Roch** for **algebraically closed curves** in Lean 4:

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

### Current Status (Cycle 287)

| Component | Status |
|-----------|--------|
| P¹ Riemann-Roch formula | ✅ Complete |
| P¹ Serre duality (effective D) | ✅ Complete |
| P¹ edge cases (non-effective) | ✅ Works for alg. closed fields |
| Elliptic curves (genus 1) | ⏳ Next phase |

**Key insight (Cycle 287)**: For algebraically closed fields, all places have degree 1,
so `IsLinearPlaceSupport` is automatic and all theorems apply.

---

## What's Proved

```lean
-- Main Serre duality for P¹
theorem serre_duality_p1 (D : ExtendedDivisor (Polynomial Fq))
    (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    h1_finrank_full Fq D = ell_proj_ext Fq (canonicalExtended Fq - D)

-- Full P¹ Riemann-Roch formula
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) : ell_ratfunc_projective D = D.deg.toNat + 1
```

---

## Heuristics

### Weighted vs Unweighted Degree (Cycle 287 Lesson)
- `DivisorV2.deg` = Σ D(v) (unweighted, sum of coefficients)
- `degWeighted` = Σ D(v) · deg(v) (weighted by place degree)
- For algebraically closed fields: these are equal (all deg(v) = 1)
- For general Fq: use `IsLinearPlaceSupport` hypothesis when needed

### Coprimality Pattern (Cycle 284)
```lean
generator_not_mem_other_prime  -- gen_v ∉ w.asIdeal for v ≠ w
Irreducible.coprime_iff_not_dvd -- coprimality from non-divisibility
Finset.prod_dvd_of_coprime      -- product divides if pairwise coprime
```

### Affine vs Projective
- `RRSpace_proj` (affine) gives ℓ(0) = ∞
- `RRSpace_proj_ext` (projective) gives ℓ(0) = 1
- **Rule**: Use `ProjectiveAdelicRRData` for projective curves

---

## Cycle Discipline

### One Cycle = One Focused Goal

**Good scope**:
- Fill ONE sorry with a clean proof
- Add ONE new definition + basic lemmas
- Explore ONE new curve type (check Mathlib support)

**Bad scope**:
- "Fill all sorries in this file"
- "Implement elliptic curves completely"

---

## Verification Commands

```bash
# Check sorry count
lake build 2>&1 | grep -E "sorry|^error:"

# Full build
lake build
```

---

*Updated Cycle 287: Discovered weighted/unweighted degree issue, added IsLinearPlaceSupport fix,
prepared for elliptic curve phase.*
