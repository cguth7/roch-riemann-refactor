# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles (2804 jobs)
**Phase**: 3 - Serre Duality
**Cycle**: 182

### Active Sorries (8 total)

| File | Lemma | Priority | Notes |
|------|-------|----------|-------|
| Residue.lean | `residueAtInfty_smul` | HIGH | Scalar mult for res_∞ - proof documented |
| Residue.lean | `residueAtIrreducible` | LOW | Placeholder for higher-degree places |
| Residue.lean | `residue_sum_eq_zero` | MED | General residue theorem |
| SerreDuality.lean | `serrePairing` | HIGH | Main pairing construction |
| SerreDuality.lean | `serrePairing_wellDefined` | MED | Uses residue theorem |
| SerreDuality.lean | `serrePairing_left_nondegen` | MED | Left non-degeneracy |
| SerreDuality.lean | `serrePairing_right_nondegen` | MED | Right non-degeneracy |
| FullAdelesCompact.lean | (1 sorry) | LOW | Edge case |

### Key Infrastructure ✅

| Component | Status | Location |
|-----------|--------|----------|
| Residue at X (X-adic) | ✅ | Residue.lean |
| Residue at infinity | ✅ | Residue.lean |
| Residue at linear places | ✅ | Residue.lean |
| residueSumTotal (finite + ∞) | ✅ | SerreDuality.lean |
| Residue theorem (split denom) | ✅ | SerreDuality.lean |
| Bilinear pairing | ✅ | SerreDuality.lean |
| Perfect pairing dimension | ✅ | SerreDuality.lean |

---

## Next Steps (Cycle 183)

1. **Fill `residueAtInfty_smul`** - Prove scalar multiplication for residue at infinity
   - Needs: lemma about num/denom of scalar multiplication
   - Uses: leadingCoeff_C_mul_of_isUnit, natDegree_C_mul_of_isUnit

2. **Wire serrePairing** - Replace sorry with actual construction
   - Use `residuePairing_bilinear` for diagonal elements
   - Need to extend to full adele ring

3. **Fill non-degeneracy lemmas** - For serrePairing
   - Left: if ⟨[a], f⟩ = 0 for all f, then [a] = 0
   - Right: if ⟨[a], f⟩ = 0 for all [a], then f = 0

---

## Recent Progress

### Cycle 182 - Bilinear pairing infrastructure
- `residueSumTotal_smul` ✅ - Scalar multiplication for total residue sum
- `residueSumTotal_linearMap` ✅ - Total residue as linear map
- `residuePairing` ✅ - Bilinear pairing via product
- `residuePairing_bilinear` ✅ - Full bilinear map structure
- `residuePairing_eq_zero_of_splits` ✅ - Residue theorem for pairing
- NEW sorry: `residueAtInfty_smul` (proof documented)

### Cycle 181 - Extended residue theorem to n poles
- `pairwise_coprime_X_sub_of_injective` ✅
- `residueSumTotal_n_poles_finset` ✅ - General residue theorem for n distinct linear poles
- `residueSumTotal_splits` ✅ - Corollary for split denominators

### Cycle 180 - Two poles residue theorem
- `residueSumTotal_two_poles` ✅ - Uses partial fractions

### Cycle 179 - Partial fractions infrastructure
- Added `Mathlib.Algebra.Polynomial.PartialFractions` import
- `isCoprime_X_sub_of_ne` ✅

### Cycle 178 - Perfect pairing dimension
- `finrank_eq_of_perfect_pairing` ✅ - Key lemma for Serre duality

### Earlier cycles (166-177)
- See `ledger_archive.md` for detailed history

---

## Quick Commands

```bash
# Build
lake build 2>&1 | tail -5

# Find sorries
grep -rn "sorry$" RrLean/RiemannRochV2/*.lean | grep -v "FqPolynomialInstance\|TraceDualityProof"

# Build specific file
lake build RrLean.RiemannRochV2.SerreDuality
```

---

## File Status

### In Build (2804 jobs)
- `RiemannRochV2.lean` (root)
- `Basic`, `Divisor`, `RRSpace`, `Typeclasses`
- `RiemannInequality` ✅
- `Infrastructure`, `RRDefinitions`
- `FullAdelesBase`, `FullAdelesCompact` ✅
- `AdelicH1v2` ✅
- `Residue.lean` ✅
- `SerreDuality.lean` (in progress)

### Disconnected (not blocking)
- `DifferentIdealBridge.lean` ✅
- `TraceDualityProof.lean` (1 sorry, alternative approach)
- `FqPolynomialInstance.lean` (4 sorries, instantiation)
- `FullRRData.lean`, `Projective.lean`, `P1Instance.lean`

---

*For strategy and architecture, see `playbook.md`*
*For historical cycles 1-181, see `ledger_archive.md`*
