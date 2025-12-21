# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles with 1 sorry in Step 3
**Phase**: 3 - Serre Duality
**Cycle**: 221 (IN PROGRESS)

### Active Sorries

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **RatFuncPairing.lean** | 2 | HIGH | Step 3 has 1 sorry (hneg_le_num) - almost done! |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma - documented |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

---

## Cycle 221 Progress (IN PROGRESS)

**Goal**: Complete Step 3 counting argument

**Completed this session**:
1. ✅ **PROVED `irreducible_factor_of_denom_is_linear`** (new helper lemma)
   - Location: RatFuncPairing.lean:2495-2575
   - For any irreducible factor π of f.denom (with f ∈ L(D)), π is associated to (X - C α)
   - Generalizes the Step 2 argument to ALL irreducible factors

2. ✅ **PROVED `denom_splits_of_LRatFunc`** (new helper lemma)
   - Location: RatFuncPairing.lean:2577-2596
   - Uses `irreducible_factor_of_denom_is_linear` + `splits_iff_splits`
   - Shows f.denom.Splits when f ∈ L(D) with IsLinearPlaceSupport D

3. ✅ **PROVED `hdeg_split`**: `D.deg = pos_sum - neg_abs_sum`
   - Location: RatFuncPairing.lean:3046-3067
   - Sum decomposition using `Finset.sum_filter_add_sum_filter_not`

4. ✅ **PROVED `hsum_ineq`**: `pos_sum < neg_abs_sum`
   - Location: RatFuncPairing.lean:3070
   - Follows from hdeg_split + hD by omega

5. ✅ **PROVED `hpos_ge_denom`**: `pos_sum ≥ denom.natDegree`
   - Location: RatFuncPairing.lean:3074-3143
   - Uses denom_splits + sum over roots with `Multiset.toFinset_sum_count_eq`
   - Key: linearPlace injective + pole_multiplicity_le_D for each root

**Remaining sorry** (line ~3194):
- **`hneg_le_num`**: `neg_abs_sum ≤ num.natDegree`

---

## Next Steps (Cycle 222)

### Complete `hneg_le_num`

The proof structure is set up (lines 3147-3194). Key facts already proved:
- `hneg_lin`: Every v in neg_places equals linearPlace β for some β
- `hbound_per_v`: For each such v, `-D v ≤ rootMult(β, num)`
- `hneg_is_num_root`: Each β is a root of num

**Strategy documented in code**:
```
Σ_{v} (-D v) ≤ Σ_{v} rootMult(β_v, num)
             = Σ_{β ∈ image} rootMult(β, num)  [β_v distinct by linearPlace injective]
             = Σ_{β ∈ image} num.roots.count(β)  [count_roots]
             ≤ num.roots.card  [sum over subset ≤ total]
             ≤ num.natDegree  [card_roots']
```

**Key insight**: The image of neg_places under linearPlace⁻¹ is a subset of num.roots.toFinset.
Need to use Finset.sum over this image and bound by Multiset.card.

**Suggested approach**:
1. Use `Finset.sum_image` to rewrite sum over neg_places as sum over image
2. Show image ⊆ num.roots.toFinset (each β_v is a root of num)
3. Use `Finset.sum_le_sum_of_subset_of_nonneg` or sum bound for count

---

## Critical Path

```
RatFuncPairing.lean: projective_LRatFunc_eq_zero_of_neg_deg
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
    └─→ hneg_le_num ← NEXT (1 sorry remaining!)
        └─→ L_proj(D) = {0} when deg(D) < 0
            └─→ Serre duality RHS verified
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
