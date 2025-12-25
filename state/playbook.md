# Playbook

Strategic guide for formalizing Riemann-Roch. Updated Cycle 311 (corrected).

---

## Critical Status Update

**We are ~15-20 cycles from completion**, not 50-70.

Per INVENTORY_REPORT.md, we have **3,700 lines of curve-agnostic infrastructure** already done:
- Riemann Inequality: **PROVED**
- DVR properties: **PROVED**
- H¹(D) framework: **DONE**
- Dimension machinery: **PROVED**

The P¹ sorries are edge cases we **bypass** with Weil differentials.

---

## State Folder Overview

```
state/
├── playbook.md          # This file - strategy
├── ledger.md            # Current cycle, next steps
├── PROOF_CHAIN.md       # Dependency graph
├── REFACTOR_PLAN.md     # Phase 7 roadmap
├── INVENTORY_REPORT.md  # KEY: Shows 3,700 lines reusable
└── ledger_archive.md    # Historical cycles
```

---

## Ultimate Goal

Formalize **Riemann-Roch** for smooth projective curves:

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

### Current Status (Cycle 311)

| Component | Status |
|-----------|--------|
| Riemann Inequality | ✅ **PROVED** |
| H¹(D) as adelic quotient | ✅ DONE |
| Serre pairing (abstract) | ✅ Framework done |
| WeilDifferential definition | ⏳ Cycle 312 |
| Non-degeneracy proof | ⏳ Cycle 315 (crux) |

---

## What's Already Proved (Key Assets)

These are **sorry-free**, not axiomatized:

| Theorem | File | Why It Matters |
|---------|------|----------------|
| Riemann Inequality | RiemannInequality.lean | Half of RR |
| ℓ(D+v) ≤ ℓ(D) + 1 | DimensionCounting.lean | Gap bound |
| DVR for completions | DedekindDVR.lean | Local structure |
| Residue field iso | ResidueFieldIso.lean | Connects R/v to completion |
| Kernel = L(D) | KernelProof.lean | Exact sequence |

---

## Phase 7: The Final Push

### Why Weil Differentials Work

**Old approach (P¹)**: Residue sum pairing
- Tied to polynomial factorization
- Only works for linear places
- The sorries are about edge cases here

**New approach (general)**: Weil differential pairing
- `⟨f, ω⟩ = ω(f)` is just evaluation
- Residue theorem is built into definition (ω vanishes on K)
- **Bypasses** the P¹ sorries entirely

### Revised Timeline

| Cycle | Task | Notes |
|-------|------|-------|
| 312 | WeilDifferential structure | Define + K-module |
| 313 | Local components | May be simpler than feared |
| 314 | Pairing definition | Straightforward |
| 315 | **Non-degeneracy** | THE crux - 5-10 cycles |
| 316 | Canonical class | deg(K) = 2g-2 |
| 317-318 | Assembly | Instantiate FullRRData |

**Total: ~15-20 cycles**

### The Crux: Non-Degeneracy

To prove h¹(D) = ℓ(K-D), need the pairing to be perfect:
```
∀ f ≠ 0 in L(D), ∃ ω in Ω(K-D) with ω(f) ≠ 0
```

Options:
1. **Prove from compactness** - A_K/K compact → perfect pairing
2. **Prove locally** - Non-degeneracy at each place → global
3. **Axiomatize** - Acceptable if needed

We have compactness infrastructure (AdelicTopology.lean), so option 1 is viable.

---

## Architectural Lessons

### What Gets Reused (3,700 lines)

| File | Lines | Purpose |
|------|-------|---------|
| Infrastructure.lean | 300 | Uniformizers, valuations |
| Divisor.lean | 200 | DivisorV2, degree |
| RRSpace.lean | 200 | L(D) definition |
| KernelProof.lean | 400 | Exact sequence |
| DimensionCounting.lean | 200 | Gap bounds |
| RiemannInequality.lean | 250 | **PROVED** |
| AdelicH1v2.lean | 550 | H¹ framework |
| FullRRData.lean | 150 | Axiom package |
| + 10 more files | ~1,450 | Supporting infra |

### What's P¹-Specific (Archived)

| File | Status |
|------|--------|
| RatFuncPairing.lean | BURN |
| DimensionScratch.lean | BURN |
| P1Instance.lean | BURN |
| ProductFormula.lean | BURN |

These don't affect the general proof.

---

## Verification Commands

```bash
# Build check
lake build

# Sorry count
lake build 2>&1 | grep "sorry" | wc -l
# Expected: 8 (2 archived + 6 axioms)

# Check Riemann Inequality is sorry-free
grep -n "sorry" RrLean/RiemannRochV2/RiemannInequality.lean
# Expected: No output
```

---

## Key Files for Phase 7

| Goal | File |
|------|------|
| See what's proved | INVENTORY_REPORT.md |
| H¹ definition | Adelic/AdelicH1v2.lean |
| Full adeles | Adelic/FullAdelesBase.lean |
| Abstract RR axioms | FullRRData.lean |
| **Start here** | General/WeilDifferential.lean (new) |

---

*Updated Cycle 311 (corrected). ~15-20 cycles to sorry-free RR.*
