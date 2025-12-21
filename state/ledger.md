# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles - Step 3 COMPLETE!
**Phase**: 3 - Serre Duality
**Cycle**: 223 (IN PROGRESS)

### Active Sorries

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **RatFuncPairing.lean** | 1 | LOW | Early incomplete attempt (line 1956), not on critical path |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma - documented |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

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

## Cycle 223 Progress (IN PROGRESS)

**Goal**: Verify Serre duality integration and identify path to FullRRData

**Analysis completed**:

### 1. ✅ Integration Architecture Verified

The proved theorem connects as follows:
```
ell_ratfunc_projective_zero_of_neg_deg (D.deg < 0, IsLinearPlaceSupport D)
    └─→ This IS the `ell_zero_of_neg_deg` axiom for FullRRData
    └─→ For K-D where K=-2[∞]: deg(K-D) = -2 - deg(D)
        └─→ When deg(D) ≥ -1: deg(K-D) < 0, so ℓ(K-D) = 0
```

### 2. ✅ IsLinearPlaceSupport Analysis

**Finding**: The assumption is mathematically appropriate for genus 0 / P¹:
- Linear places = (X - α) for α ∈ Fq = "rational points"
- Standard RR on P¹ is stated for rational divisors
- If D has linear support, then K - D also has linear support (K = -2[∞])
- The limitation is the **unweighted degree** definition

**For full generality** (non-linear places):
- Would need weighted degree: deg(D) = Σ_v [k(v):k] · D(v)
- Deferred to future work (not needed for genus 0 case)

### 3. ✅ Remaining Work Identified

**To instantiate FullRRData for RatFunc Fq (genus 0)**:

| Axiom | Status | Notes |
|-------|--------|-------|
| `ell_zero_of_neg_deg` | ✅ DONE | `ell_ratfunc_projective_zero_of_neg_deg` |
| `deg_canonical` | ❓ Need | Define K = -2[∞], show deg = -2 |
| `serre_duality_eq` | ❓ Need | ℓ(D) - ℓ(K-D) = deg(D) + 1 |

**For `serre_duality_eq`**, need:
1. ℓ(D) = deg(D) + 1 when deg(D) ≥ 0 (with linear support)
2. Construct explicit basis: {1, 1/(X-α₁), ..., 1/(X-αₙ)^k, ...}

---

## Next Steps (Cycle 223+)

### Option A: Complete FullRRData Instance (RECOMMENDED)
1. **Define canonical divisor** for RatFunc: K = -2·linearPlace(0) or similar
2. **Prove ℓ(D) = deg(D) + 1** for deg(D) ≥ 0 with linear support
3. **Instantiate FullRRData** for Fq, Polynomial Fq, RatFunc Fq

### Option B: P¹ Consistency Check Only
- Already have `P1Instance.lean` proving axiom consistency
- No need for concrete instantiation if goal is just to validate axioms

### Option C: Clean Up (Low Priority)
- Remove RatFuncPairing.lean:1956 old incomplete attempt
- Address AdelicH1Full.lean sorries (needed only for full adeles approach)

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

## Cycle 220 Progress (COMPLETED)

**Goal**: Complete Step 3 counting argument

**Completed**:
1. ✅ Built proof structure from line 2670 to ~2970
2. ✅ Proved key intermediate facts:
   - `hv_neg_linear`: v_neg = linearPlace β (using IsLinearPlaceSupport)
   - `hzero_mult`: num.rootMultiplicity β ≥ |D(linearPlace β)|
   - `hα_root`: α is a root of denom (from Step 2's v_π = linearPlace α)
   - `hαβ_ne`: α ≠ β (D(α) > 0 but D(β) < 0)
   - `hβ_mult_le_deg`: num.rootMultiplicity β ≤ num.natDegree
   - `hneg_D_le_num`: -D(linearPlace β) ≤ num.natDegree
3. ✅ Set up final contradiction structure with calc chain

---

## Cycle 219 Progress (COMPLETED)

**Goal**: Complete Step 3 of `projective_LRatFunc_eq_zero_of_neg_deg`

**Completed**:
1. ✅ **PROVED `not_isRoot_of_coprime_isRoot`** (helper lemma)
2. ✅ **PROVED `pole_multiplicity_le_D`** (Lemma 1 from plan)
3. ✅ **PROVED `zero_multiplicity_ge_neg_D`** (Lemma 3 from plan)

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
*For historical cycles 1-211, see `ledger_archive.md`*
