# Playbook

Strategic guide for formalizing Riemann-Roch. Updated Cycle 339.

---

## Mission

**Goal**: Fully formalized Riemann-Roch for curves over algebraically closed fields, using only the standard 3 foundational axioms (propext, Classical.choice, Quot.sound).

**Motivation**: Daniel Litt's Twitter challenge (Dec 15, 2025).

---

## Current Status: Core Proof COMPLETE

| Milestone | Status |
|-----------|--------|
| Euler characteristic χ(D) = deg(D) + 1 - g | ✅ **PROVED** |
| chi_additive χ(D+v) = χ(D) + 1 | ✅ **PROVED** |
| 6-term exact sequence | ✅ **PROVED** |
| Riemann-Roch from Euler | ✅ **PROVED** |
| Riemann Inequality | ✅ **PROVED** |

### What Remains: Axiom Elimination

The core proof is done, but we have `axiom` declarations that need to become theorems:

| Axiom | Location | Difficulty |
|-------|----------|------------|
| `h1_finite_all` | EllipticRRData.lean | Medium |
| `ell_finite_all` | EllipticRRData.lean | Medium |
| `isDedekindDomain_coordRing` | EllipticSetup.lean | Medium-Hard |
| Strong approximation (2) | StrongApproximation.lean | Hard |

Plus ~7 sorry placeholders in abstraction layers.

---

## State Folder Overview

```
state/
├── playbook.md          # This file - strategy
├── ledger.md            # Current state, next steps
├── PROOF_CHAIN.md       # What's proved, what remains
├── REFACTOR_PLAN.md     # Phase 8 roadmap
├── INVENTORY_REPORT.md  # Asset inventory
└── ledger_archive.md    # Historical cycles
```

---

## Phase 8: Axiom Elimination

**Estimated**: 12-21 cycles

### Priority Order

1. **Remove `euler_char_axiom`** - We proved this!
2. **Prove finiteness axioms** - Standard AG facts
3. **Prove `isDedekindDomain_coordRing`** - Smooth → Dedekind
4. **Strong approximation** - The hard ones
5. **Clear remaining sorries** - Instance wiring

---

## Architecture

```
RrLean/RiemannRochV2/
├── Core/              - Curve-agnostic infrastructure ✅
├── Adelic/            - Full adeles, Euler characteristic ✅
├── SerreDuality/      - H¹ framework ✅
├── Elliptic/          - Instances (has axioms to eliminate)
├── ResidueTheory/     - Residue fields ✅
└── General/           - Weil differentials ✅
```

---

## Key Theorems (Sorry-Free!)

| Theorem | File |
|---------|------|
| `euler_characteristic` | EulerCharacteristic.lean |
| `chi_additive` | EulerCharacteristic.lean |
| `riemann_inequality_real` | RiemannInequality.lean |
| `residueFieldIso` | ResidueFieldIso.lean |
| `kernel_evaluationMapAt_complete_proof` | KernelProof.lean |

---

## Verification

```bash
# Build check
lake build

# Check EulerCharacteristic is sorry-free
grep -n "sorry" RrLean/RiemannRochV2/Adelic/EulerCharacteristic.lean
# Expected: No output

# Find remaining sorries
grep -rn "sorry" RrLean/RiemannRochV2 --include="*.lean" | grep -v Archive
```

---

*Updated Cycle 339. Core RR proof complete. Phase 8: Eliminate axioms.*
