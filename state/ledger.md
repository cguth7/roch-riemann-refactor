# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles with sorries
**Phase**: 3 - Serre Duality
**Cycle**: 211 (research cycle - no code changes committed)

### Active Sorries (12 total)

| File | Count | Priority | Notes |
|------|-------|----------|-------|
| **RatFuncPairing.lean** | 7 | HIGH | Projective L(D) infrastructure |
| **ProductFormula.lean** | 1 | DONE* | *Intentionally incorrect lemma - documented |
| **Residue.lean** | 2 | LOW | Higher-degree places, general residue theorem (deferred) |
| **FullAdelesCompact.lean** | 1 | LOW | Edge case bound < 1 (not needed) |
| **TraceDualityProof.lean** | 1 | LOW | Alternative approach (not on critical path) |

---

## Cycle 211 Research Notes

**Goal**: Prove `smul_mem'` and `add_mem'` for `RRSpace_ratfunc_projective`

### Key Discoveries

#### 1. Import ProductFormula.lean to Remove Duplicates
- RatFuncPairing.lean has duplicate lemmas from ProductFormula.lean (lines ~2051-2110)
- Add `import RrLean.RiemannRochV2.ProductFormula` and delete the `ProductFormulaLite` section
- This removes 3 sorries immediately

#### 2. smul_mem' Proof Strategy (COMPLETE)

For showing scalar multiplication preserves `RRSpace_ratfunc_projective`:

**Finite valuation bound**: Use `v.valuation_of_algebraMap` and show `Polynomial.C c` has valuation 1:
```lean
have hCc_not_mem : Polynomial.C c ∉ v.asIdeal := by
  intro hmem
  have h1_mem := v.asIdeal.mul_mem_left (↑hCc_unit.unit⁻¹ : Polynomial Fq) hmem
  simp only [IsUnit.unit_spec, Units.inv_mul_cancel] at h1_mem
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1_mem)
exact_mod_cast intValuation_eq_one_iff.mpr hCc_not_mem
```

**Infinity bound**: Use from Residue.lean:
- `(c • f).num = Polynomial.C c * f.num`
- `(c • f).denom = f.denom`
- `Polynomial.natDegree_smul_of_smul_regular` preserves degree

Need `open Classical in` before the definition for GCDMonoid instance.

#### 3. add_mem' Proof Strategy (95% COMPLETE)

For showing addition preserves `noPoleAtInfinity`:

**Key lemma**: `RatFunc.num_denom_add a b` gives:
```
(a + b).num * (a.denom * b.denom) = (a.num * b.denom + a.denom * b.num) * (a + b).denom
```

**Proof structure**:
1. Define `hraw_num := a.num * b.denom + b.num * a.denom`
2. Define `hraw_denom := a.denom * b.denom`
3. Show `hraw_num.natDegree ≤ hraw_denom.natDegree` using degree bounds from `noPoleAtInfinity`
4. Use `num_denom_add` to get: `(a+b).num * hraw_denom = hraw_num * (a+b).denom`
5. Expand via `Polynomial.natDegree_mul` to get degree equation
6. Derive `(a+b).num.natDegree ≤ (a+b).denom.natDegree`

**Remaining issue**: `omega` can't solve the final Nat arithmetic. Need explicit proof:
```lean
-- From: a + x = y + z and y ≤ x, derive: a ≤ z
have hle : y + z ≤ x + z := Nat.add_le_add_right hdeg_raw_num _
-- Then: a + x = y + z ≤ x + z, so a ≤ z
```

---

## Critical Path

```
RatFuncPairing.lean: projective_LRatFunc_eq_zero_of_neg_deg
    ├─→ smul_mem' (proof strategy ready)
    ├─→ add_mem' (proof strategy ready, omega issue)
    ├─→ constant_mem_projective_zero (straightforward)
    └─→ L_proj(D) = {0} when deg(D) < 0
        └─→ Serre duality RHS verified
```

**Estimated effort**: 2-3 cycles to implement and debug.

---

## Next Steps (Cycle 212)

1. **Add ProductFormula import** and delete duplicate section
2. **Implement smul_mem'** using the pattern above
3. **Implement add_mem'** with explicit Nat proof instead of omega
4. **Prove constant_mem_projective_zero**
5. **Tackle main vanishing theorem**

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
*For historical cycles 1-210, see `ledger_archive.md`*
