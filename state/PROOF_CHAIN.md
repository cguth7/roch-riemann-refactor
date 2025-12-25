# Proof Chain: Riemann-Roch Formalization

Tracks the dependency chain from main theorems down to Mathlib. Updated Cycle 311.

---

## Main Theorems (Proved)

```lean
-- P¹ Riemann-Roch formula
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) : ell_ratfunc_projective D = D.deg.toNat + 1

-- Serre duality for P¹ (effective divisors with non-negative inftyCoeff)
theorem serre_duality_p1 (D : ExtendedDivisor (Polynomial Fq))
    (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    h1_finrank_full Fq D = ell_proj_ext Fq (canonicalExtended Fq - D)

-- Elliptic RR (axiomatized)
theorem ell_minus_ell_neg_eq_deg (D : DivisorV2 (EllipticCoordRing W))
    : ell_proj D - ell_proj (-D) = D.deg
```

---

## Module Status

### ✅ Complete (Frozen)

| Module | Files | LOC | Key Contribution |
|--------|-------|-----|------------------|
| **P1Instance/** | 10 | 3,300 | P¹ places, canonical divisor, L(K-D)=0 |
| **ResidueTheory/** | 7 | 2,000 | Trace pairing, residue calculus |
| **Core/** | 6 | 2,000 | Place, Divisor, RRSpace definitions |
| **Support/** | 3 | 600 | DVR properties |
| **Dimension/** | 3 | 650 | Gap bounds, Riemann inequality |

### ⏸️ Archived (P¹ Edge Cases)

| File | Sorries | Status |
|------|---------|--------|
| `SerreDuality/General/AdelicH1Full.lean` | 2 | PID-specific, archived |

### ⏳ Phase 7 (New)

| File | Status |
|------|--------|
| `General/WeilDifferential.lean` | Cycle 312 |
| `General/LocalComponent.lean` | Cycle 313 |
| `General/DifferentialDivisor.lean` | Cycle 314 |
| `General/SerrePairingGeneral.lean` | Cycle 315 |

---

## Proof Chain Diagram

### Current (P¹ + Elliptic)

```
                    Main Theorems
                         │
        ┌────────────────┼────────────────┐
        ▼                ▼                ▼
  serre_duality_p1   ell_proj_eq   elliptic_RR
        │                │                │
        └────────────────┼────────────────┘
                         │
              ┌──────────┴──────────┐
              ▼                     ▼
      AdelicH1Full.lean       EllipticRRData.lean
      (P¹-specific)           (Axiomatized)
              │                     │
              ▼                     ▼
      FullAdelesBase.lean     StrongApproximation
      (FullAdeleRing)         (Axiom)
              │
              ▼
         Mathlib
```

### Future (Phase 7: Weil Differentials)

```
                 General Riemann-Roch
                         │
                         ▼
              h¹(D) = ℓ(K - D)
                         │
        ┌────────────────┼────────────────┐
        ▼                ▼                ▼
  WeilDifferential  SerrePairing    Canonical
  (functionals)     (evaluation)    (div(ω))
        │                │                │
        └────────────────┼────────────────┘
                         │
                         ▼
              LocalComponent.lean
              (ω_P extraction)
                         │
              ┌──────────┴──────────┐
              ▼                     ▼
      FullAdeleRing ✅        HeightOneSpectrum ✅
      (reuse)                 (reuse)
              │                     │
              └──────────┬──────────┘
                         ▼
                    Mathlib
```

---

## Sorry Locations (8 total, Cycle 311)

### Archived P¹ Edge Cases (2)
*PID-specific, not needed for general curves*

| Location | Description |
|----------|-------------|
| AdelicH1Full:757 | Deep negative inftyCoeff |
| AdelicH1Full:1458 | Non-effective strong approx |

### Axiom Sorries (6) - Intentional
| Location | Description |
|----------|-------------|
| Abstract | `h1_zero_finite` |
| StrongApproximation (2) | Function field density |
| EllipticH1 (2) | Elliptic-specific H¹ |
| EllipticSetup | IsDedekindDomain |

---

## Phase 7: Weil Differential Chain (Planned)

```
GeneralRRData.lean (Cycle 317+)
├── h¹(D) = ℓ(K - D) via WeilDifferential pairing
└── Full RR for any genus
        │
        ▼
SerrePairingGeneral.lean (Cycle 315)
├── serrePairing_general : L(D) →ₗ WeilDiff →ₗ k
├── Pairing is just evaluation: ⟨f, ω⟩ = ω(f)
└── Non-degeneracy (axiom or prove)
        │
        ▼
Canonical.lean (Cycle 316)
├── canonical_class_unique (div ω₁ ≈ div ω₂)
└── deg_canonical = 2g - 2
        │
        ▼
DifferentialDivisor.lean (Cycle 314)
├── valuation_differential ω v : ℤ
└── div ω : DivisorV2 R
        │
        ▼
LocalComponent.lean (Cycle 313) ← THE HARD PART
├── localComponent ω v : K_v →ₗ k
└── ext_localComponent (local determines global)
        │
        ▼
WeilDifferential.lean (Cycle 312) ← NEXT
├── structure WeilDifferential
├── toLinearMap : FullAdeleRing →ₗ k
├── vanishes_on_K : ∀ x : K, ω(diag x) = 0
└── Module K WeilDifferential instance
        │
        ▼
FullAdelesBase.lean ✅ (REUSE)
├── FullAdeleRing = FiniteAdeleRing × K_infty
└── fullDiagonalEmbedding : K → FullAdeleRing
```

---

## Key Infrastructure (Reusable for Phase 7)

| File | Key Components | Reusable? |
|------|----------------|-----------|
| `FullAdelesBase.lean` | FullAdeleRing, fullDiagonalEmbedding | ✅ Yes |
| `AdelicH1v2.lean` | SpaceModule, globalPlusBoundedSubmodule | ✅ Yes |
| `Core/Divisor.lean` | DivisorV2, deg, support | ✅ Yes |
| `PlaceDegree.lean` | degree, generator | ⚠️ P¹-specific |
| `ResidueTheory/*` | residueAt*, residueSumTotal | ❌ Replace |

---

## Axiom Stack (Current + Planned)

### Existing Axioms
| Axiom | File | Justification |
|-------|------|---------------|
| `IsDedekindDomain CoordRing` | EllipticSetup | Hartshorne II.6 |
| `StrongApprox K` | StrongApproximation | K dense in A_S |
| `h1_zero_eq_one` | EllipticH1 | Genus = 1 |
| `h1_vanishing_positive` | EllipticH1 | Serre vanishing |
| `serre_duality` | EllipticH1 | Residue pairing |

### Planned Axioms (Phase 7)
| Axiom | File | Justification |
|-------|------|---------------|
| `dim_K(WeilDiff) = 1` | WeilDifferential | Standard theory |
| `serrePairing_nondegenerate` | SerrePairingGeneral | Or derive from RR |

---

## Verification Commands

```bash
# Check for sorries in P1Instance (should be empty)
grep -rn "sorry" RrLean/RiemannRochV2/P1Instance/
# Expected: No output

# Check total sorries
lake build 2>&1 | grep "sorry" | wc -l
# Expected: 8

# Full build
lake build
```

---

*Updated Cycle 311. Phase 7 active. See REFACTOR_PLAN.md for detailed roadmap.*
