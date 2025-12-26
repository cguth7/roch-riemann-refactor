# Playbook

Strategic guide for formalizing Riemann-Roch. Updated Cycle 326.

---

## Critical Status Update

**We are ~10-15 cycles from full RR for arbitrary curves.**

### Completed Infrastructure
- Riemann Inequality: **PROVED**
- DVR properties: **PROVED**
- H¹(D) framework: **DONE**
- Dimension machinery: **PROVED**
- Elliptic FullRRData: **INSTANTIATED** (Cycle 323)
- AdelicRRData → FullRRData bridge: **DONE**

### The Key Remaining Piece
**Euler characteristic formula**: χ(D) = deg(D) + 1 - g

This is the ONE theorem we need to prove. Once we have it, full RR follows.

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

### Current Status (Cycle 326)

| Component | Status |
|-----------|--------|
| Riemann Inequality | ✅ **PROVED** |
| H¹(D) as adelic quotient | ✅ DONE |
| AdelicRRData → FullRRData bridge | ✅ **DONE** |
| Elliptic FullRRData instance | ✅ **DONE** (Cycle 323) |
| Connecting homomorphism δ | ✅ **CONSTRUCTED** (Cycle 325) |
| Technical lemmas for δ | ✅ **PROVED** (Cycle 326) |
| Euler characteristic formula | ⏳ **NEXT** (needs exactness proofs) |
| Serre duality | ⏳ After χ formula |

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

## Phase 7: The Final Push - Euler Characteristic

### The Key Insight

The core of Riemann-Roch is the **Euler characteristic formula**:
```
χ(D) = ℓ(D) - h¹(D) = deg(D) + 1 - g
```

Once we prove this, combined with Serre duality h¹(D) = ℓ(K-D), we get full RR.

### Strategy: 6-Term Exact Sequence

For each place v, there's an exact sequence:
```
0 → L(D) → L(D+v) → κ(v) → H¹(D) → H¹(D+v) → 0
```

Taking alternating sum of dimensions gives: χ(D+v) = χ(D) + 1

**What we already have**:
| Piece | Status | Location |
|-------|--------|----------|
| L(D) → L(D+v) inclusion | ✅ PROVED | RRSpace.lean |
| L(D+v) → κ(v) evaluation | ✅ PROVED | KernelProof.lean |
| Exactness at L(D+v) | ✅ PROVED | KernelProof.lean |
| H¹(D) → H¹(D+v) surjection | ✅ PROVED | AdelicH1v2.lean (h1_anti_mono) |
| ℓ(D+v) ≤ ℓ(D) + 1 | ✅ PROVED | DimensionCounting.lean |

**What we need to build**:
| Piece | Cycle | Notes |
|-------|-------|-------|
| Connecting map δ: κ(v) → H¹(D) | 324 | Lift residue class to adele |
| Exactness at κ(v) | 324-325 | image(eval) = ker(δ) |
| Exactness at H¹(D) | 325-326 | image(δ) = ker(surj) |
| Dimension formula | 326 | Rank-Nullity |

### Implementation (No Category Theory)

We don't need formal exact sequence objects. Just:
1. Define δ: κ(v) → H¹(D) explicitly
2. Prove the isomorphisms that give dimension counting
3. Conclude χ(D+v) = χ(D) + 1

### Revised Timeline

| Cycle | Task | Notes |
|-------|------|-------|
| 324 | Connecting homomorphism δ | The key construction |
| 325-326 | Exactness proofs | Verify kernel/image relations |
| 327 | Dimension formula | χ(D+v) = χ(D) + 1 |
| 328 | Induction to full χ | χ(D) = deg(D) + 1 - g |
| 329-330 | Serre duality cleanup | h¹(D) = ℓ(K-D) |
| 331 | Assembly | Prove full RR |

**Total: ~8-10 cycles**

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
| Dimension counting | Dimension/DimensionCounting.lean |
| Kernel proof | Dimension/KernelProof.lean |
| H¹ definition | Adelic/AdelicH1v2.lean |
| FullRRData bridge | Adelic/AdelicH1v2.lean (adelicRRData_to_FullRRData) |
| Elliptic instance | Elliptic/EllipticRRData.lean |
| **Next work** | Adelic/EulerCharacteristic.lean (new) |

---

*Updated Cycle 323. ~8-10 cycles to sorry-free RR via Euler characteristic.*
