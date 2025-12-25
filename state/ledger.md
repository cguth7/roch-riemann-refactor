# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ PASSING (1 sorry in PlaceDegree.lean, 2 sorries in AdelicH1Full.lean, 8 edge case sorries in Abstract.lean)
**Cycle**: 283 (In Progress)

---

## Cycle 283 Summary: Valuation-Degree Infrastructure

**Goal**: Fill the degree-valuation relationship sorry in AdelicH1Full.lean.

**What was done**:

1. **Added new lemmas to PlaceDegree.lean**:
   - `asIdeal_pow_eq_span_generator_pow`: v.asIdeal^n = span{gen_v^n}
   - `mem_asIdeal_pow_iff_generator_pow_dvd`: Membership ↔ generator power divides
   - `natDegree_ge_of_pow_dvd`: If g^n | p (g monic), then p.natDegree ≥ n * g.natDegree
   - `natDegree_ge_of_intValuation_le`: If val_v(p) ≤ exp(-n), then p.natDegree ≥ n * deg(v)
   - `degWeighted_ge_deg`: For effective D, degWeighted ≥ D.deg (proved!)
   - `natDegree_ge_degWeighted_of_valuation_bounds`: Sum version (has 1 sorry for coprimality)

2. **Proof structure established**:
   - Key: generators at different places are coprime (irreducible, distinct primes)
   - Product of gen_v^{D(v)} over support divides p
   - Degree of product = degWeighted k D ≥ D.deg
   - This gives p.natDegree ≥ D.finite.deg, yielding the contradiction

3. **Remaining work**:
   - The sorry in `natDegree_ge_degWeighted_of_valuation_bounds` needs:
     - `IsCoprime` proof for generator powers at different places
     - `Finset.prod_dvd_of_coprime` application
   - Once this is filled, AdelicH1Full.lean:999 can be completed

**Key insight**: The valuation-degree relationship reduces to polynomial factorization. When gen_v^n | p for coprime generators, their product divides p, and degree(product) = sum of contributions.

---

## Cycle 282 Summary (Archive)

**Goal**: Fill edge case sorries in Abstract.lean.

**What was done**:

1. **Added new theorems to AdelicH1Full.lean**:
   - `RRSpace_proj_ext_canonical_sub_eq_bot_neg_infty`: L(K-D) = {0} when D.finite effective and -1 ≤ D.inftyCoeff < 0
   - `ell_proj_ext_canonical_sub_eq_zero_neg_infty`: ℓ(K-D) = 0 for the above case
   - `RRSpace_proj_ext_canonical_sub_eq_bot_deep_neg_infty`: L(K-D) = {0} when D.finite effective, D.inftyCoeff < -1, deg(D) ≥ -1 (has 1 sorry for degree-valuation relationship)
   - `ell_proj_ext_canonical_sub_eq_zero_deep_neg_infty`: ℓ(K-D) = 0 for the above case

2. **Fixed one serre_duality edge case**:
   - For D.finite effective, -1 ≤ D.inftyCoeff < 0: NOW PROVED via the new theorems
   - Both h¹(D) = 0 and ℓ(K-D) = 0, so Serre duality holds as 0 = 0

**Key insight**: For P¹, the main applications use effective divisors with inftyCoeff ≥ 0.

---

## Cycle 281 Summary (Archive)

**Goal**: Connect the new `ResidueTrace` engine to the rest of the codebase.

**What was done**:
1. Fixed Abstract.lean build errors from Cycle 280 API changes
2. Verified ResidueTrace wiring
3. Confirmed sorry-free components: P1Instance/, ResidueTheory/

---

## What's Proved

```lean
-- Main Serre duality for P¹ (effective divisors with non-negative inftyCoeff)
theorem serre_duality_p1 (D : ExtendedDivisor (Polynomial Fq))
    (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    h1_finrank_full Fq D = ell_proj_ext Fq (canonicalExtended Fq - D)

-- Extended case: D.finite effective, -1 ≤ D.inftyCoeff < 0
-- Proved via: h¹(D) = 0 (SpaceModule_full_subsingleton) and ℓ(K-D) = 0 (new theorem)
```

---

## Sorries

| Location | Count | Status |
|----------|-------|--------|
| PlaceDegree.lean:403 | 1 | `natDegree_ge_degWeighted_of_valuation_bounds` - coprimality proof needed |
| AdelicH1Full.lean:619 | 1 | `inftyValuationDef k₂ ≤ exp(-1)` - ACCEPTED DEBT |
| AdelicH1Full.lean:999 | 1 | Polynomial degree-valuation relationship - blocked by PlaceDegree sorry |
| Abstract.lean | 8 | Edge cases in p1ProjectiveAdelicRRData |

**PlaceDegree.lean sorry** (new in Cycle 283):
- `natDegree_ge_degWeighted_of_valuation_bounds`: Sum version of valuation-degree bound
- Requires: IsCoprime proof for generators at different places
- Once filled: AdelicH1Full.lean:999 can be completed using the lemma

**Abstract.lean sorries breakdown** (in p1ProjectiveAdelicRRData instance):
- `h1_finite` (3 sorries):
  - D.finite effective, D.inftyCoeff < -1
  - D.finite not effective
  - deg(D) < -1 (requires Serre duality isomorphism)
- `h1_vanishing` (2 sorries):
  - D.finite effective, D.inftyCoeff < -1
  - D.finite not effective
- `serre_duality` (3 sorries):
  - D.finite effective, D.inftyCoeff < -1 (ℓ(K-D)=0 proved, h¹(D)=0 needs extended strong approx)
  - D.finite not effective
  - deg(D) < -1 (requires full residue pairing)

**Note**: Template code at lines 200-203 has 3 sorries but is commented out (not active code).

---

## Next Steps: Cycle 284

Priority:
1. **Complete PlaceDegree.lean:403** - the coprimality proof
   - Need: `IsCoprime (generator v) (generator w)` for v ≠ w (different irreducibles are coprime)
   - Use: `Finset.prod_dvd_of_coprime` to get product divisibility
   - This unblocks AdelicH1Full.lean:999

Other options:
2. **Prove the accepted sorry** - tackle `inftyValuationDef k₂ ≤ exp(-1)` at AdelicH1Full.lean:619
3. **Extend strong approximation** - prove H¹(D)=0 for D.inftyCoeff < -1
4. **Begin elliptic curve infrastructure** - extend Place type to support higher genus

---

## Technical Debt Notes

**PlaceDegree.lean:403** - Coprimality of generators (NEW in Cycle 283)
- **What to prove**: Product of gen_v^{D(v)} divides p when each gen_v^{D(v)} divides p
- **Mathematical fact**: Generators at different places are coprime (distinct irreducibles)
- **Status**: Documented, proof structure established, needs IsCoprime lemma

**AdelicH1Full.lean:619** - Principal parts infinity bound
- **What to prove**: `FunctionField.inftyValuationDef Fq k₂ ≤ WithZero.exp (-1)`
- **Mathematical fact**: Principal parts at finite places are proper fractions
- **Status**: ACCEPTED DEBT from Cycle 280

**AdelicH1Full.lean:999** - Polynomial degree-valuation
- **What to prove**: For polynomial p satisfying valuation bounds from D.finite, p.natDegree ≥ D.finite.deg
- **Mathematical fact**: Σ_{v|p} ord_v(p)·deg(v) ≤ p.natDegree, with equality for zeros
- **Status**: Blocked by PlaceDegree.lean:403 sorry
