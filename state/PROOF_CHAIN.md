# Proof Chain: P¹ Riemann-Roch

Tracks the critical path from main theorems down to Mathlib. Updated Cycle 284.

---

## Main Theorems (Proved)

```lean
-- Serre duality for P¹
theorem serre_duality_p1 (D : ExtendedDivisor (Polynomial Fq))
    (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    h1_finrank_full Fq D = ell_proj_ext Fq (canonicalExtended Fq - D)

-- P¹ dimension formula
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) : ell_ratfunc_projective D = D.deg.toNat + 1
```

---

## Sorry Status

| File | Sorries | Notes |
|------|---------|-------|
| P1Instance/*.lean | 0 | All sorry-free |
| PlaceDegree.lean | 0 | Coprimality proof complete (Cycle 284) |
| ResidueTheory/*.lean | 0 | All sorry-free |
| AdelicH1Full.lean | 1 | Line 619 - accepted technical debt |
| Abstract.lean | 8 | Edge cases in ProjectiveAdelicRRData |

---

## P¹ Proof Chain (Complete)

```
Main theorems
  └── serre_duality_p1, ell_ratfunc_projective_eq_deg_plus_one
        └── PlaceDegree.lean (valuation-degree infrastructure)
              ├── natDegree_ge_degWeighted_of_valuation_bounds ✅
              ├── degWeighted_ge_deg ✅
              └── generator_not_mem_other_prime (coprimality) ✅
        └── AdelicH1Full.lean
              ├── RRSpace_proj_ext_canonical_sub_eq_bot_deep_neg_infty ✅
              └── SpaceModule_full_finite_of_deg_ge_neg_one ✅
        └── FullAdelesCompact.lean (strong approximation) ✅
```

---

## Key Infrastructure (All Sorry-Free)

| File | Key Lemmas |
|------|------------|
| `PlaceDegree.lean` | `generator_monic`, `generator_irreducible`, `natDegree_ge_degWeighted_of_valuation_bounds` |
| `P1Canonical.lean` | `canonicalExtended`, `deg_canonicalExtended` |
| `P1VanishingLKD.lean` | `RRSpace_proj_ext_canonical_sub_eq_bot` |
| `FullAdelesCompact.lean` | `strong_approximation_ratfunc` |

---

## Verification

```bash
# Check for sorries in key files
grep -rn "sorry" RrLean/RiemannRochV2/P1Instance/
# Expected: No output

lake build 2>&1 | grep -E "sorry|^error:"
# Expected: Only AdelicH1Full.lean:619 and Abstract.lean sorries
```

---

*Updated Cycle 284: PlaceDegree sorries eliminated, valuation-degree chain complete.*
