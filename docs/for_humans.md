# Riemann-Roch Formalization: Current State

## The Goal

Prove the Riemann-Roch theorem for smooth projective curves:

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

Where:
- `ℓ(D)` = dim H⁰(X, O_X(D))
- `K` = canonical divisor
- `g` = genus = dim H¹(X, O_X)

---

## Current Status: Axiomatized Interface (NOT a Proof)

**We do NOT have a proof of Riemann-Roch.**

What we have is an **axiomatized theory interface** - a Lean file that captures the *shape* of RR but assumes the key mathematical content as structure fields.

| What we claimed | What it actually is |
|-----------------|---------------------|
| "PROVED" | **DERIVED FROM ASSUMPTIONS** |
| Riemann-Roch theorem | Algebraic consequence of assumed fields |
| `eulerChar_formula` | This IS Riemann-Roch in disguise |

The derivation is **circular**: we assumed RR (as `eulerChar_formula`) and derived RR.

---

## The Problem: mathlib Gaps

mathlib (as of Dec 2024) **lacks**:
- Divisors on schemes (Weil or Cartier)
- Line bundles / invertible sheaves
- Genus of a curve
- Degree of a divisor
- Sheaf cohomology H⁰, H¹
- Serre duality
- Canonical sheaf

mathlib **has**:
- `Scheme` type
- `IsSmooth`, `IsProper` morphism properties
- General homological algebra

**Without the foundational objects, we cannot state or prove RR from first principles.**

---

## Structure Hierarchy

```
┌─────────────────────────────────────────────────────────────┐
│                        RRData                               │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  X : Scheme           (the curve)                     │  │
│  │  Div : Type           (abstract, NOT connected to X)  │  │
│  │  deg : Div → ℤ        (abstract degree function)      │  │
│  │  ell : Div → ℕ        (abstract ℓ(D) = dim H⁰)        │  │
│  │  genus : ℕ            (abstract genus)                │  │
│  │  K : Div              (abstract canonical divisor)    │  │
│  └───────────────────────────────────────────────────────┘  │
│                     STATUS: Abstract interface              │
└─────────────────────────────────────────────────────────────┘
                              │
                              │ extends (adds ASSUMPTIONS)
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                  RRDataWithCohomology                       │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  h1 : Div → ℕ                   (dim H¹(O_X(D)))      │  │
│  │  serreDuality : ℓ(K-D) = h1(D)  ⚠️ ASSUMPTION        │  │
│  └───────────────────────────────────────────────────────┘  │
│         STATUS: serreDuality is a deep theorem we assume    │
└─────────────────────────────────────────────────────────────┘
                              │
                              │ extends (adds MORE ASSUMPTIONS)
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                    RRDataWithEuler                          │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  eulerChar : Div → ℤ             (χ(D))               │  │
│  │  eulerChar_def : χ(D) = ℓ(D) - h1(D)   (definition)   │  │
│  │  eulerChar_formula : χ(D) = deg(D)+1-g ⚠️ = RR!!!    │  │
│  └───────────────────────────────────────────────────────┘  │
│         STATUS: eulerChar_formula IS Riemann-Roch          │
└─────────────────────────────────────────────────────────────┘
```

---

## The "Derivation" (Circular)

```
                    ASSUMED STRUCTURE FIELDS
                    ════════════════════════
                              │
        ┌─────────────────────┼─────────────────────┐
        │                     │                     │
        ▼                     ▼                     ▼
  serreDuality         eulerChar_def        eulerChar_formula
  ℓ(K-D) = h1(D)      χ(D) = ℓ(D) - h1(D)   χ(D) = deg(D)+1-g
  ⚠️ ASSUMED          (definition)          ⚠️ THIS IS RR!
        │                     │                     │
        │                     └──────────┬──────────┘
        │                                │
        │                                ▼
        │                      ell_sub_h1_eq_deg
        │                   ℓ(D) - h1(D) = deg(D)+1-g
        │                     (algebra from assumptions)
        │                                │
        └────────────────┬───────────────┘
                         │
                         ▼
               ell_sub_ell_K_sub_D
            ℓ(D) - ℓ(K-D) = deg(D)+1-g
              (substitution, algebra)
                         │
                         ▼
              ┌─────────────────────────┐
              │                         │
              │  riemannRoch            │
              │  DERIVED FROM           │
              │  ASSUMPTIONS            │
              │  (not proved!)          │
              │                         │
              └─────────────────────────┘
```

**The "proof" is valid algebra, but we assumed the answer (`eulerChar_formula`).**

---

## Semantic Status Table

| Component | Status | Notes |
|-----------|--------|-------|
| `RRData` | Abstract interface | No assumptions, just structure |
| `RRDataWithCohomology.serreDuality` | **ASSUMPTION** | Serre duality is a deep theorem |
| `RRDataWithEuler.eulerChar_def` | Definition | Harmless |
| `RRDataWithEuler.eulerChar_formula` | **ASSUMPTION = RR** | This IS the target theorem! |
| `RRDataWithEuler.riemannRoch` | **DERIVED** | Circular - derived from above |
| `RRData.riemannRoch` | `sorry` | No proof path |

---

## What Would a Real Proof Require?

To **actually prove** Riemann-Roch, someone needs to build in Lean:

1. **Divisors** (Weil or Cartier) on schemes/varieties
2. **Line bundles** / invertible sheaves with `O_X(D)`
3. **Sheaf cohomology** H⁰, H¹ for coherent sheaves
4. **Degree** of a divisor
5. **Genus** as dim H¹(O_X)
6. **Serre duality theorem** (a major result itself)
7. **Riemann-Roch** (the goal)

This represents **thousands of lines** of foundational Lean code and **months of expert work**.

---

## Next Steps: Option 3

We've chosen to **build the foundations ourselves**.

This means:
- Start defining Weil divisors on curves
- Build toward sheaf cohomology
- Eventually instantiate `RRData` with real objects
- Then actually prove the assumed fields

This is a long-term project.

---

## File Structure

```
roch-riemann/
├── RrLean/
│   └── RR.lean              # Axiomatized interface (NOT a proof)
├── problem/
│   └── problem.md           # Mathematical target (READ-ONLY)
├── state/
│   ├── playbook.md          # Heuristics and status
│   ├── candidates.json      # Candidates with honest status labels
│   └── ledger.md            # Cycle history with Assumption Accounting
├── agents/
│   ├── orchestrator.md      # Main loop controller
│   ├── generator.md         # Proposes candidates
│   ├── reflector.md         # Scores candidates
│   └── curator.md           # Updates state files
└── docs/
    └── for_humans.md        # This file
```

---

## Lessons Learned

1. **"No sorry" ≠ "proved"** - A theorem with no sorry can still be derived from assumed axioms
2. **Structure fields are assumptions** - Prop fields in structures are mathematically axioms
3. **Semantic honesty matters** - Label things correctly: DERIVED_FROM_ASSUMPTIONS, not PROVED
4. **mathlib gaps are real** - Algebraic geometry in Lean 4 is still being built
