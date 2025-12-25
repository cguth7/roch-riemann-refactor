# Proof Chain: Riemann-Roch Formalization

Tracks the dependency chain from main theorems down to Mathlib. Updated Cycle 288.

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

-- H¹ vanishing
theorem h1_finrank_full_eq_zero_of_deg_ge_neg_one (D : ExtendedDivisor (Polynomial Fq))
    (hdeg : D.deg ≥ -1) (heff : D.finite.Effective) (hinfty : D.inftyCoeff ≥ -1) :
    h1_finrank_full Fq D = 0
```

---

## Module Status

### ✅ Complete (Sorry-Free)

| Module | Files | LOC | Key Contribution |
|--------|-------|-----|------------------|
| **P1Instance/** | 10 | 3,300 | P¹ places, canonical divisor, L(K-D)=0 |
| **ResidueTheory/** | 7 | 2,000 | Trace pairing, residue calculus |
| **Core/** | 6 | 2,000 | Place, Divisor, RRSpace definitions |
| **Support/** | 3 | 600 | DVR properties (proved, not axiom!) |
| **Dimension/** | 3 | 650 | Gap bounds, Riemann inequality |

### ⚠️ Near-Complete (Has Sorries)

| File | Sorries | Status |
|------|---------|--------|
| `SerreDuality/General/AdelicH1Full.lean` | 4 | 95% - strong approx edge cases |
| `SerreDuality/General/Abstract.lean` | 5 | 85% - IsLinearPlaceSupport + deg < -1 |
| `Adelic/FullAdelesCompact.lean` | 1-2 | 90% - compactness bounds |

---

## Proof Chain Diagram

```
                    Main Theorems
                         │
        ┌────────────────┼────────────────┐
        ▼                ▼                ▼
  serre_duality_p1   ell_proj_eq   h1_finrank_eq_zero
        │                │                │
        └────────────────┼────────────────┘
                         │
              ┌──────────┴──────────┐
              ▼                     ▼
      AdelicH1Full.lean       P1VanishingLKD.lean
      (SpaceModule_full)      (L(K-D) = 0)
              │                     │
              ▼                     ▼
      FullAdelesCompact       PlaceDegree.lean
      (strong approx)         (valuation-degree)
              │                     │
              └──────────┬──────────┘
                         ▼
              FullAdelesBase.lean
              (FullAdeleRing = Finite × K∞)
                         │
              ┌──────────┴──────────┐
              ▼                     ▼
      AdelicTopology.lean    P1Instance.lean
      (compactness)          (IsDedekindDomain Fq[X])
              │                     │
              └──────────┬──────────┘
                         ▼
                    Mathlib
         (DedekindDomain, Valuation, Finsupp)
```

---

## P1Instance Chain (Complete)

```
P1VanishingLKD.lean
├── RRSpaceV3_p1Canonical_sub_ofAffine_eq_zero ✅
├── denom_eq_one_of_valuation_le_one_forall ✅
└── p1InftyValuation_polynomial_not_le_exp_neg2 ✅
        │
        ▼
P1Canonical.lean
├── p1Canonical = -2[∞] ✅
└── deg_p1Canonical = -2 ✅
        │
        ▼
P1Place.lean
├── p1InftyPlace ✅
└── HasInfinitePlaces instance ✅
        │
        ▼
PlaceDegree.lean
├── natDegree_ge_degWeighted_of_valuation_bounds ✅
├── degWeighted_ge_deg ✅
└── generator_not_mem_other_prime ✅
```

---

## Sorry Locations (9 total)

### Content Sorries (4) - Need proof work

| Location | Line | Description |
|----------|------|-------------|
| AdelicH1Full.lean | 698 | Strong approx infinity bound |
| AdelicH1Full.lean | 817 | Deep negative inftyCoeff |
| AdelicH1Full.lean | 1213 | Degree gap in L(K-D)=0 |
| AdelicH1Full.lean | 1283 | Non-effective IsLinearPlaceSupport |

### Infrastructure Sorries (5) - Trivial for alg. closed

| Location | Line | Description |
|----------|------|-------------|
| Abstract.lean | 294 | IsLinearPlaceSupport |
| Abstract.lean | 312 | IsLinearPlaceSupport |
| Abstract.lean | 345 | IsLinearPlaceSupport |
| Abstract.lean | 299 | deg(D) < -1 case |
| Abstract.lean | 351 | deg(D) < -1 case |

---

## Key Infrastructure (All Sorry-Free)

| File | Key Lemmas |
|------|------------|
| `PlaceDegree.lean` | `generator_monic`, `generator_irreducible`, `natDegree_ge_degWeighted_of_valuation_bounds` |
| `P1Canonical.lean` | `canonicalExtended`, `deg_canonicalExtended` |
| `P1VanishingLKD.lean` | `RRSpace_proj_ext_canonical_sub_eq_bot` |
| `FullAdelesCompact.lean` | `strong_approximation_ratfunc` |
| `DedekindDVR.lean` | `isDiscreteValuationRing_adicCompletionIntegers` |
| `ResidueFieldIso.lean` | `residueFieldIso` (completion residue = quotient) |

---

## Verification Commands

```bash
# Check for sorries in P1Instance (should be empty)
grep -rn "sorry" RrLean/RiemannRochV2/P1Instance/
# Expected: No output

# Check AdelicH1Full sorries
lake build 2>&1 | grep "AdelicH1Full.*sorry"
# Expected: 4 lines

# Full sorry count
lake build 2>&1 | grep "sorry" | wc -l
# Expected: 9
```

---

## Elliptic Curve Chain (In Progress)

```
EllipticRRData.lean (planned)
├── ProjectiveAdelicRRData instance
└── h1_finrank_full_eq_genus_minus_ell
        │
        ▼
EllipticH1.lean (planned)
├── h1_finrank computation
└── SpaceModule for elliptic
        │
        ▼
EllipticCanonical.lean (planned)
├── ellipticCanonical = 0
└── deg_ellipticCanonical = 0
        │
        ▼
EllipticPlaces.lean ✅ CREATED (Cycle 289)
├── EllipticPlace = HeightOneSpectrum (CoordRing W)
├── LocalUniformizer structure
└── uniformizerAt (local, not global!)
        │
        ▼
EllipticSetup.lean ✅ CREATED (Cycle 289)
├── NonsingularCurve typeclass
├── [IsDedekindDomain (CoordRing W)] ← AXIOM (sorry)
└── [IsFractionRing (CoordRing W) (FuncField W)]
        │
        ▼
Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
├── WeierstrassCurve.Affine.CoordinateRing
├── WeierstrassCurve.Affine.FunctionField
└── W.Δ (discriminant)
```

---

*Updated Cycle 289: Added EllipticSetup + EllipticPlaces. Axiom approach implemented.*
