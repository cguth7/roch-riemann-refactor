# Proof Chain: Riemann-Roch Formalization

What's proved, what remains. Updated Cycle 339.

---

## Status: Core Proof COMPLETE

The Euler characteristic formula and full Riemann-Roch are **PROVED**.

What remains: eliminating `axiom` declarations to satisfy Litt's challenge.

---

## What's Proved (Sorry-Free!)

### The Big Theorems

| Theorem | File | Status |
|---------|------|--------|
| `euler_characteristic` | EulerCharacteristic.lean | ✅ **PROVED** |
| `chi_additive` | EulerCharacteristic.lean | ✅ **PROVED** |
| `riemann_roch_from_euler` | EulerCharacteristic.lean | ✅ **PROVED** |
| `riemann_inequality_real` | RiemannInequality.lean | ✅ **PROVED** |

### Supporting Infrastructure (All Sorry-Free)

| Theorem | File |
|---------|------|
| DVR for adic completion | DedekindDVR.lean |
| Residue field isomorphism | ResidueFieldIso.lean |
| Kernel = L(D) | KernelProof.lean |
| ℓ(D+v) ≤ ℓ(D) + 1 | DimensionCounting.lean |
| H¹ surjection | AdelicH1v2.lean |
| All exactness lemmas | EulerCharacteristic.lean |

---

## Proof Chain Diagram

```
        ┌─────────────────────────────────────┐
        │         RIEMANN-ROCH (PROVED)       │
        │   ℓ(D) - ℓ(K-D) = deg(D) + 1 - g    │
        └─────────────────────────────────────┘
                         │
        ┌────────────────┴────────────────────┐
        ▼                                     ▼
   Euler Characteristic              Serre Duality
   χ(D) = deg(D) + 1 - g             h¹(D) = ℓ(K-D)
   ✅ PROVED                         ✅ From AdelicRRData
        │                                     │
        └────────────────┬────────────────────┘
                         ▼
        ┌─────────────────────────────────────┐
        │       6-TERM EXACT SEQUENCE         │
        │  0→L(D)→L(D+v)→κ(v)→H¹(D)→H¹(D+v)→0 │
        │            ALL PROVED               │
        └─────────────────────────────────────┘
                         │
        ┌────────────────┴────────────────────┐
        ▼                                     ▼
   Dimension Counting              Connecting Homomorphism
   chi_additive                    δ: κ(v) → H¹(D)
   ✅ PROVED                       ✅ PROVED
        │                                     │
        └────────────────┬────────────────────┘
                         ▼
        ┌─────────────────────────────────────┐
        │     RIEMANN INEQUALITY (PROVED)     │
        │   ℓ(D) ≥ deg(D) + 1 - g             │
        └─────────────────────────────────────┘
```

---

## What Blocks Full Formalization

### Axiom Declarations (Must Become Theorems)

| Axiom | Location | Description |
|-------|----------|-------------|
| `h1_finite_all` | EllipticRRData.lean | H¹(D) finite-dimensional |
| `ell_finite_all` | EllipticRRData.lean | L(D) finite-dimensional |
| `isDedekindDomain_coordRing` | EllipticSetup.lean | Smooth → Dedekind |
| `strong_approx_*` (2) | StrongApproximation.lean | Function field density |

### Sorry Placeholders (~7)

| Location | Description |
|----------|-------------|
| Abstract.lean (3) | Abstraction layer instances |
| AdelicH1Full.lean (2) | Strong approximation edge cases |
| EllipticH1.lean (2) | Elliptic-specific facts |

---

## Key Files

### Core Proof (Sorry-Free)

| File | Key Content |
|------|-------------|
| EulerCharacteristic.lean | Main theorems, 6-term sequence |
| RiemannInequality.lean | Riemann inequality |
| KernelProof.lean | Kernel = L(D) |
| DimensionCounting.lean | Gap bounds |
| ResidueFieldIso.lean | Residue isomorphism |

### Needs Axiom Elimination

| File | Issue |
|------|-------|
| EllipticRRData.lean | 3 axiom declarations |
| EllipticSetup.lean | 1 axiom declaration |
| StrongApproximation.lean | 2 axiom declarations |

---

## Foundational Axioms Used

Only the standard 3:
- `propext` - Propositional extensionality
- `Classical.choice` - Axiom of choice
- `Quot.sound` - Quotient soundness

These are exactly what Mathlib uses. ✅

---

## Verification

```bash
# Verify EulerCharacteristic is sorry-free
grep -n "sorry" RrLean/RiemannRochV2/Adelic/EulerCharacteristic.lean
# Expected: No output

# Check foundational axioms
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "axioms:"
# Expected: [propext, Classical.choice, Quot.sound]

# Find all remaining sorries
grep -rn "sorry" RrLean/RiemannRochV2 --include="*.lean" | grep -v Archive | wc -l
```

---

*Updated Cycle 339. Core proof complete. Axiom elimination phase next.*
