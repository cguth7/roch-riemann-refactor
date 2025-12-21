# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles
**Phase**: 3 - Serre Duality → FullRRData Instance
**Cycle**: 226 (IN PROGRESS)

### Active Sorries

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **DimensionScratch.lean** | 6 | HIGH | Dimension formula structure - key sorries for ℓ(D) = deg(D)+1 |
| **RatFuncFullRR.lean** | 0 | ✅ DONE | L_proj(0) = constants PROVED, ℓ(0) = 1 PROVED |
| **RatFuncPairing.lean** | 1 | LOW | Early incomplete attempt (line 1956), not on critical path |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma - documented |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

---

## Cycle 226 Progress (IN PROGRESS)

**Goal**: Dimension formula ℓ(D) = deg(D) + 1 for effective D with linear support

### Created: DimensionScratch.lean

New file `RrLean/RiemannRochV2/SerreDuality/DimensionScratch.lean` with structure:

1. ✅ **`RRSpace_ratfunc_projective_mono`**: L_proj(D) ⊆ L_proj(D + [v])
2. 🔲 **`ell_ratfunc_projective_gap_le`**: Gap bound ℓ(D+[v]) ≤ ℓ(D) + 1 (sorry)
3. 🔲 **`inv_X_sub_C_pow_satisfies_valuation`**: 1/(X-α)^k satisfies valuations (sorry)
4. 🔲 **`inv_X_sub_C_pow_noPoleAtInfinity`**: No pole at infinity (sorry)
5. ✅ **`inv_X_sub_C_pow_mem_projective`**: 1/(X-α)^k ∈ L_proj(k·[linearPlace α])
6. 🔲 **`inv_X_sub_C_pow_not_mem_projective_smaller`**: Not in L_proj((k-1)·[v]) (sorry)
7. 🔲 **`ell_ratfunc_projective_single_linear`**: ℓ(n·[v]) = n+1 (sorry)
8. 🔲 **`ell_ratfunc_projective_eq_deg_plus_one`**: General dimension formula (sorry)

### Strategy

For P¹ with g = 0:
- K has degree -2
- When deg(D) ≥ 0, deg(K-D) = -2 - deg(D) < 0
- So ℓ(K-D) = 0 (already proved: `ell_canonical_sub_zero`)
- Riemann-Roch becomes: ℓ(D) = deg(D) + 1

Proof approach:
1. Base case: ℓ(0) = 1 ✅ (proved in Cycle 225)
2. Inductive step: ℓ(D + [v]) = ℓ(D) + 1
   - Upper bound: Gap ≤ 1 via evaluation map (need to prove)
   - Lower bound: Explicit element 1/(X-α)^k in L(D+[v]) \ L(D)

### Key Insight (from Gemini)

The dimension formula ℓ(D) = deg(D) + 1 IS the Riemann-Roch formula for P¹!
Since ℓ(K-D) = 0 for deg(D) ≥ 0, we just need to prove the dimension directly.

---

## Cycle 225 Progress (COMPLETED) 🎉

**Goal**: Complete RatFuncFullRR.lean sorries - ACHIEVED!

### Proved Theorems

1. ✅ **`projective_L0_eq_constants`**: L_proj(0) = image of Fq under algebraMap
   - Proof strategy: If f ∈ L_proj(0) has denom with positive degree,
     there's an irreducible factor π giving a pole at v_π,
     but hval says valuation ≤ 1, contradiction
   - So denom has degree 0, meaning denom = 1 (monic), and num has degree 0 (from noPoleAtInfinity)
   - Therefore f = constant

2. ✅ **`ell_ratfunc_projective_zero_eq_one`**: finrank(L_proj(0)) = 1
   - Uses `projective_L0_eq_constants` to rewrite L_proj(0) as image of Fq
   - Shows Algebra.linearMap is injective (via RatFunc.C_injective)
   - Applies LinearEquiv.ofInjective to get finrank = finrank Fq Fq = 1

### Significance

These complete the "ProperCurve" axioms for P¹:
- L_proj(0) = constants (no global meromorphic functions without poles)
- ℓ(0) = 1 (dimension of constants is 1)

Combined with `ell_ratfunc_projective_zero_of_neg_deg` (Cycle 222), we now have:
- ℓ(D) = 0 when deg(D) < 0 (for linear place support)
- ℓ(0) = 1

**RatFuncFullRR.lean is now sorry-free!**

---

## Cycle 224 Progress (COMPLETED)

**Goal**: Begin FullRRData instantiation for RatFunc Fq - ACHIEVED

### Created: RatFuncFullRR.lean

New file `RrLean/RiemannRochV2/SerreDuality/RatFuncFullRR.lean` with:

1. ✅ **`canonical_ratfunc`**: K = -2·[linearPlace 0]
   - Represents canonical divisor K = -2[∞] using finite places
   - Any degree -2 divisor works (linearly equivalent on P¹)

2. ✅ **`deg_canonical_ratfunc`**: deg(K) = -2

3. ✅ **`canonical_ratfunc_linear_support`**: K is supported on linear places

4. ✅ **`sub_linear_support`**: K - D has linear support when D does

5. ✅ **`deg_canonical_sub_neg`**: deg(K - D) < 0 when deg(D) ≥ -1

6. ✅ **`ell_canonical_sub_zero`**: ℓ(K - D) = 0 when deg(D) ≥ -1
   - Uses proved `ell_ratfunc_projective_zero_of_neg_deg`

### Key Insight

For RR formula ℓ(D) - ℓ(K-D) = deg(D) + 1 with g = 0:
- When deg(D) ≥ -1: ℓ(K-D) = 0 (by `ell_canonical_sub_zero`)
- Formula reduces to: ℓ(D) = deg(D) + 1
- Need to prove dimension formula for positive degree divisors

---

## Cycle 223 Progress (COMPLETED)

**Goal**: Verify Serre duality integration and identify path to FullRRData - ACHIEVED

Analysis documented above led to Cycle 224 implementation.

---

## Cycle 222 Progress (COMPLETED) 🎉

**Goal**: Complete Step 3 counting argument - ACHIEVED!

**Completed this session**:
1. ✅ **PROVED `hneg_le_num`**: `neg_abs_sum ≤ num.natDegree`
   - Location: RatFuncPairing.lean:3147-3281
   - Final piece of the counting argument
   - Strategy: Map neg_places → Fq via linearPlace inverse, show image ⊆ num.roots
   - Key lemmas used:
     - `Finset.sum_image` with linearPlace injectivity
     - `Multiset.toFinset_sum_count_eq` for root counting
     - `Polynomial.card_roots'` for degree bound

**Major milestone**: `projective_LRatFunc_eq_zero_of_neg_deg` is now COMPLETE!
- L_proj(D) = {0} when deg(D) < 0 and D is supported on linear places
- This is the key step for Serre duality RHS

---

## Cycle 221 Progress (COMPLETED)

**Goal**: Complete Step 3 counting argument structure

**Completed**:
1. ✅ **PROVED `irreducible_factor_of_denom_is_linear`** (new helper lemma)
2. ✅ **PROVED `denom_splits_of_LRatFunc`** (new helper lemma)
3. ✅ **PROVED `hdeg_split`**: `D.deg = pos_sum - neg_abs_sum`
4. ✅ **PROVED `hsum_ineq`**: `pos_sum < neg_abs_sum`
5. ✅ **PROVED `hpos_ge_denom`**: `pos_sum ≥ denom.natDegree`

---

## Next Steps (Cycle 227+)

Fill sorries in `DimensionScratch.lean` (in order of dependency):

1. **`inv_X_sub_C_pow_satisfies_valuation`** - Valuation of 1/(X-α)^k
   - At linearPlace α: val = exp(k) (pole of order k)
   - At other places: val ≤ 1 (no pole)
   - Use `intValuation_linearPlace_eq_exp_neg_rootMultiplicity`

2. **`inv_X_sub_C_pow_noPoleAtInfinity`** - deg(num) ≤ deg(denom)
   - For 1/(X-α)^k: num = 1 (deg 0), denom = (X-α)^k (deg k)
   - Need to compute num/denom of RatFunc.mk

3. **`ell_ratfunc_projective_gap_le`** - Gap bound for projective case
   - Adapt `gap_le_one_proj_of_rational` from Projective.lean
   - Use evaluation map with kernel = L(D)

4. **`inv_X_sub_C_pow_not_mem_projective_smaller`** - Exclusion lemma
   - val at linearPlace α is exp(k) > exp(k-1)

5. **`ell_ratfunc_projective_single_linear`** - ℓ(n·[v]) = n+1
   - Induction using gap = 1 exactly

6. **`ell_ratfunc_projective_eq_deg_plus_one`** - General formula
   - Reduce to single-point case or use induction on support

7. **Instantiate FullRRData** combining all pieces

---

## Critical Path ✅ COMPLETE

```
RatFuncPairing.lean: projective_LRatFunc_eq_zero_of_neg_deg ✅ DONE!
    ├─→ smul_mem' ✅ DONE (Cycle 212)
    ├─→ add_mem' ✅ DONE (Cycle 213)
    ├─→ constant_mem_projective_zero ✅ DONE (Cycle 213)
    ├─→ constant case ✅ DONE (Cycle 214)
    ├─→ IsLinearPlaceSupport assumption ✅ ADDED (Cycle 216)
    ├─→ non-constant Step 1 (denom positive degree) ✅ DONE (Cycle 216)
    ├─→ non-constant Step 2 (poles at linear places) ✅ DONE (Cycle 217)
    ├─→ intValuation_linearPlace_eq_exp_neg_rootMultiplicity ✅ DONE (Cycle 218)
    ├─→ not_isRoot_of_coprime_isRoot ✅ DONE (Cycle 219)
    ├─→ pole_multiplicity_le_D ✅ DONE (Cycle 219)
    ├─→ zero_multiplicity_ge_neg_D ✅ DONE (Cycle 219)
    ├─→ irreducible_factor_of_denom_is_linear ✅ DONE (Cycle 221)
    ├─→ denom_splits_of_LRatFunc ✅ DONE (Cycle 221)
    ├─→ hdeg_split ✅ DONE (Cycle 221)
    ├─→ hsum_ineq ✅ DONE (Cycle 221)
    ├─→ hpos_ge_denom ✅ DONE (Cycle 221)
    └─→ hneg_le_num ✅ DONE (Cycle 222)
        └─→ L_proj(D) = {0} when deg(D) < 0 ✅
            └─→ Serre duality RHS verified ✅
```

---

## Quick Commands

```bash
# Build
lake build 2>&1 | tail -5

# Find sorries
grep -rn "sorry" RrLean/RiemannRochV2/*.lean RrLean/RiemannRochV2/SerreDuality/*.lean

# Count sorries
grep -rn "sorry" RrLean/RiemannRochV2/*.lean RrLean/RiemannRochV2/SerreDuality/*.lean | wc -l
```

---

*For strategy, see `playbook.md`*
*For historical cycles 1-221, see `ledger_archive.md`*
