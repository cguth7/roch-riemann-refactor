# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ⚠️ Errors in DimensionScratch.lean (work in progress)
**Phase**: 3 - Serre Duality → FullRRData Instance
**Cycle**: 231 (IN PROGRESS)

### Active Sorries

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **DimensionScratch.lean** | 1 | HIGH | General formula only - GAP BOUND PROVED! |
| **RatFuncFullRR.lean** | 0 | ✅ DONE | L_proj(0) = constants PROVED, ℓ(0) = 1 PROVED |
| **RatFuncPairing.lean** | 1 | LOW | Early incomplete attempt (line 1956), not on critical path |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma - documented |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

---

## Cycle 231 Progress (IN PROGRESS)

**Goal**: Complete dimension formula for projective L(D)

### 🎉 MAJOR MILESTONE: Gap Bound PROVED!

**`ell_ratfunc_projective_gap_le`** - Gap bound ℓ(D+[v]) ≤ ℓ(D) + 1 is now PROVED!

**Proof structure** (lines 63-290 in DimensionScratch.lean):
1. **Residue field isomorphism**: `linearPlace_residue_equiv` shows κ(linearPlace α) ≅ Fq
2. **Dimension bound**: `linearPlace_residue_finrank` proves dim_Fq(κ(v)) = 1
3. **Evaluation map**: Constructed Fq-linear map ψ: L_proj(D+v) → κ(v)
4. **Kernel characterization**:
   - ker(ψ) ⊇ L_proj(D) via `LD_element_maps_to_zero`
   - ker(ψ) ⊆ L_proj(D) via `kernel_evaluationMapAt_complete_proof` + noPoleAtInfinity preservation
5. **Dimension counting**: Quotient embeds into 1-dim κ(v), so gap ≤ 1

### Single-Point Formula (IN PROGRESS)

**`ell_ratfunc_projective_single_linear`** - proving ℓ(n·[v]) = n + 1

Current issue at line 527: Need to establish `0 < finrank` for Module.Finite instance.

**Remaining step**: Show `0 < ell_ratfunc_projective (...)` using the nonzero element
`1/(X-α)^(m+1) ∈ L((m+1)·[v])`. The element existence is proved (`h_in`), just need
to connect to `Module.finrank_pos_iff`.

### Remaining Sorry (1)

**`ell_ratfunc_projective_eq_deg_plus_one`** (line 557) - General formula
- Depends on single-point case for induction
- Structure is clear: decompose D into sum of single points

### Key Technical Insights

1. **Kernel preservation**: If f ∈ L_proj(D+v) and eval(f) = 0, then:
   - f ∈ L_affine(D) by affine kernel theorem
   - f has noPoleAtInfinity (from f ∈ L_proj(D+v))
   - Therefore f ∈ L_proj(D) ✓

2. **Strict inclusion for lower bound**: L(m·[v]) ⊊ L((m+1)·[v]) because
   1/(X-α)^(m+1) ∈ L((m+1)·[v]) \ L(m·[v]). With equal finrank + inclusion → equality,
   contraposition gives finrank strictly increases.

---

## Cycle 230 Progress (COMPLETED)

**Goal**: Port intDegree approach and fix DimensionScratch.lean sorries - ACHIEVED

### Major Progress: DimensionScratch.lean 6 → 2 sorries

**Proved**:
1. ✅ `inv_X_sub_C_pow_noPoleAtInfinity` - via intDegree approach
2. ✅ `valuation_X_sub_at_other` - fixed via PrincipalIdealRing.isMaximal_of_irreducible
3. ✅ `inv_X_sub_C_pow_satisfies_valuation` - fixed simp issue
4. ✅ `inv_X_sub_C_pow_not_mem_projective_smaller` - exclusion lemma
5. ✅ Lower bound structure in `ell_ratfunc_projective_single_linear`

---

## Cycle 229 Progress (COMPLETED)

**Goal**: Fix typeclass issue blocking `inv_X_sub_C_pow_noPoleAtInfinity`

### Solution Found: Use `intDegree` Instead of `num_div`/`denom_div`

The typeclass mismatch with `gcd` can be completely avoided by using `RatFunc.intDegree`:

**Key insight**: `noPoleAtInfinity f ↔ f.intDegree ≤ 0`

**Mathlib lemmas used** (from `Mathlib.FieldTheory.RatFunc.Degree`):
- `RatFunc.intDegree_inv`: `intDegree(x⁻¹) = -intDegree(x)`
- `RatFunc.intDegree_mul`: `intDegree(x * y) = intDegree(x) + intDegree(y)` (for nonzero x, y)
- `RatFunc.intDegree_polynomial`: `intDegree(algebraMap p) = p.natDegree`
- `RatFunc.intDegree_X`: `intDegree(X) = 1`
- `RatFunc.intDegree_C`: `intDegree(C k) = 0`

**Proof sketch**:
```
intDegree((X - C α)⁻¹ ^ k) = k * intDegree((X - C α)⁻¹)
                           = k * (-intDegree(X - C α))
                           = k * (-1)
                           = -k ≤ 0 ✓
```

### Created: IntDegreeTest.lean

New test file `RrLean/RiemannRochV2/SerreDuality/IntDegreeTest.lean` with:
1. ✅ `RatFunc_X_sub_C_ne_zero`: X - C α ≠ 0 (via intDegree)
2. ✅ `intDegree_inv_X_sub_C_pow`: intDegree((X - C α)⁻¹ ^ k) = -k
3. ✅ `inv_X_sub_C_pow_noPoleAtInfinity`: 1/(X-α)^k has no pole at infinity

**All lemmas compile without sorry!** This approach completely sidesteps the typeclass issue.

### Next Steps

1. Port `IntDegreeTest.lean` lemmas into `DimensionScratch.lean`
2. Fix existing errors in `DimensionScratch.lean` (some lemmas have broken proofs)
3. Complete remaining dimension formula sorries

### Note on DimensionScratch.lean

This file currently has some broken proofs that need fixing. The `IntDegreeTest.lean` approach
provides working versions of the key lemmas that can be ported over.

---

## Cycle 228 Progress (COMPLETED)

**Goal**: Investigate typeclass mismatch blocking `inv_X_sub_C_pow_noPoleAtInfinity`

### Findings

1. ✅ Documented the `gcd` typeclass mismatch issue
2. ✅ Identified solution: use `RatFunc.intDegree` instead of `num_div`/`denom_div`

### Technical Lesson: Typeclass Instance Mismatch

The `gcd` function on polynomials uses `DecidableEq` instances. When `RatFunc.num_div` is applied,
it can elaborate `gcd` with a different instance than what appears in the goal after simplification.
This causes `simp only [gcd_one_left, ...]` to make no progress even though the math is identical.

**Solution**: Avoid `num_div`/`denom_div` entirely. Use `RatFunc.intDegree` which provides
clean lemmas (`intDegree_inv`, `intDegree_mul`) that work without typeclass issues.

---

## Cycle 226 Progress (COMPLETED)

**Goal**: Create DimensionScratch.lean structure - ACHIEVED

### Created: DimensionScratch.lean

1. ✅ **`RRSpace_ratfunc_projective_mono`**: L_proj(D) ⊆ L_proj(D + [v])
2. 🔲 **`ell_ratfunc_projective_gap_le`**: Gap bound (adapt from Projective.lean)
3. 🔲 **`inv_X_sub_C_pow_satisfies_valuation`**: Valuation condition
4. 🔲 **`inv_X_sub_C_pow_noPoleAtInfinity`**: No pole at infinity
5. ✅ **`inv_X_sub_C_pow_mem_projective`**: 1/(X-α)^k ∈ L_proj(k·[linearPlace α])
6. 🔲 **`inv_X_sub_C_pow_not_mem_projective_smaller`**: Exclusion lemma
7. 🔲 **`ell_ratfunc_projective_single_linear`**: ℓ(n·[v]) = n+1
8. 🔲 **`ell_ratfunc_projective_eq_deg_plus_one`**: General formula

### Strategy

For P¹ with g = 0:
- K has degree -2
- When deg(D) ≥ 0, deg(K-D) = -2 - deg(D) < 0
- So ℓ(K-D) = 0 (already proved: `ell_canonical_sub_zero`)
- Riemann-Roch becomes: ℓ(D) = deg(D) + 1

### Key Insight

The dimension formula ℓ(D) = deg(D) + 1 IS the Riemann-Roch formula for P¹!

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

## Next Steps (Cycle 229+)

### Priority 1: Fix `inv_X_sub_C_pow_noPoleAtInfinity` typeclass issue

Options to try:
1. Add `attribute [instance] Classical.decEq` at file top
2. Prove degree bound via valuation instead of `RatFunc.num_div`/`denom_div`
3. Use `convert` with explicit instance arguments

### Priority 2: Complete remaining DimensionScratch lemmas

1. **`inv_X_sub_C_pow_not_mem_projective_smaller`** - Exclusion lemma
   - Use `WithZero.exp_lt_exp` or similar for exp(k) > exp(k-1)

2. **`ell_ratfunc_projective_gap_le`** - Gap bound
   - Adapt from Projective.lean using evaluation map

3. **`ell_ratfunc_projective_single_linear`** - ℓ(n·[v]) = n+1
   - Induction using gap = 1 exactly

4. **`ell_ratfunc_projective_eq_deg_plus_one`** - General formula
   - Induction on deg(D)

### Priority 3: Instantiate FullRRData combining all pieces

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
