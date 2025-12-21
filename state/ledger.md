# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles - ProperCurve axioms PROVED for P¹!
**Phase**: 3 - Serre Duality → FullRRData Instance
**Cycle**: 225 (COMPLETED)

### Active Sorries

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **RatFuncFullRR.lean** | 0 | ✅ DONE | L_proj(0) = constants PROVED, ℓ(0) = 1 PROVED |
| **RatFuncPairing.lean** | 1 | LOW | Early incomplete attempt (line 1956), not on critical path |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma - documented |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

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

## Next Steps (Cycle 226+)

To complete FullRRData instance for RatFunc Fq:

1. **Prove dimension formula**: `ℓ(D) = deg(D) + 1` for `deg(D) ≥ 0` with linear support
   - Strategy: Construct explicit basis `{1, 1/(X-α₁), ..., 1/(X-αₖ)^nₖ}`

2. **Instantiate FullRRData** combining:
   - `ell_ratfunc_projective_zero_of_neg_deg` (ℓ(D) = 0 when deg < 0)
   - `ell_ratfunc_projective_zero_eq_one` (ℓ(0) = 1)
   - `ell_canonical_sub_zero` (ℓ(K-D) = 0 when deg(D) ≥ -1)
   - Dimension formula (TODO)

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
