# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles with sorries (warnings only)
**Phase**: 3 - Serre Duality
**Cycle**: 188

### Active Sorries (7 total)

| File | Lemma | Priority | Notes |
|------|-------|----------|-------|
| Residue.lean | `residueAtIrreducible` | LOW | Placeholder for higher-degree places |
| Residue.lean | `residue_sum_eq_zero` | MED | General residue theorem |
| SerreDuality.lean | `serrePairing` | HIGH | Main pairing construction |
| SerreDuality.lean | `serrePairing_wellDefined` | MED | Uses residue theorem |
| SerreDuality.lean | `serrePairing_left_nondegen` | MED | Left non-degeneracy |
| SerreDuality.lean | `serrePairing_right_nondegen` | MED | Right non-degeneracy |
| SerreDuality.lean | `serrePairing_ratfunc` | HIGH | Concrete pairing for RatFunc Fq |
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
| Diagonal embedding (RatFunc) | ✅ | SerreDuality.lean |
| K-part well-definedness | ✅ | SerreDuality.lean |
| Pole cancellation (valuation) | ✅ | SerreDuality.lean |
| linearPlace definition | ✅ | SerreDuality.lean |
| translatePolyEquiv (RingEquiv) | ✅ | SerreDuality.lean |
| translateRatFuncHom (lifted) | ✅ | SerreDuality.lean |
| intValuation_translatePolyEquiv | ✅ | SerreDuality.lean |
| linearPlace_valuation_eq_comap | ✅ | SerreDuality.lean |
| residueAt_of_valuation_le_one | ✅ | SerreDuality.lean |
| bounded_diagonal_finite_residue_zero | ✅ | SerreDuality.lean |
| rawDiagonalPairing | ✅ | SerreDuality.lean |
| rawDiagonalPairing_bilinear | ✅ | SerreDuality.lean |
| rawDiagonalPairing_eq_zero_of_splits | ✅ | SerreDuality.lean |
| rawDiagonalPairing_finite_zero_of_bounded | ✅ | SerreDuality.lean |

---

## Next Steps (Cycle 189)

1. **Handle FiniteAdele vs FullAdele issue** - The current H¹(D) uses FiniteAdeleRing (no infinity),
   but residue theorem needs all places. Either:
   - Switch to FullAdeleRing-based H¹, or
   - Handle infinity component separately in pairing

2. **Complete serrePairing_ratfunc construction** - Use liftQ with:
   - rawDiagonalPairing for diagonal K elements
   - Show it vanishes on globalPlusBoundedSubmodule

3. **Prove non-degeneracy** - The hard part of Serre duality

---

## Recent Progress

### Cycle 188 - **Raw pairing infrastructure for RatFunc Fq**
- `bounded_diagonal_finite_residue_zero` ✅ - Now fully proved (was pending verification)
  - Uses chain: bounded × L(K-D) → valuation ≤ 1 → residue = 0 → sum = 0
  - Key lemmas: `bounded_times_LKD_no_pole` + `residueAt_of_valuation_le_one`
- Added RawPairing section with diagonal pairing infrastructure:
  - `rawDiagonalPairing` ✅ - residueSumTotal(g * f) for g, f ∈ K
  - `rawDiagonalPairing_add_left/right` ✅ - Additivity in both arguments
  - `rawDiagonalPairing_smul_left/right` ✅ - Scalar linearity
  - `rawDiagonalPairing_bilinear` ✅ - Full bilinear map structure
  - `rawDiagonalPairing_eq_zero_of_splits` ✅ - Residue theorem for pairing
  - `rawDiagonalPairing_finite_zero_of_bounded` ✅ - Pole cancellation for bounded
- Added `serrePairing_ratfunc` (sorry) - Concrete pairing for RatFunc Fq
- Identified key architectural issue: FiniteAdeleRing vs FullAdeleRing
  - Current H¹(D) uses FiniteAdeleRing (no infinity component)
  - Residue theorem needs ALL places including infinity
  - Pairing vanishing on diagonal K requires full residue sum = 0
- Documented strategy in SerrePairingConstruction section comments
- Sorries: 6 → 7 (added serrePairing_ratfunc placeholder)

### Cycle 187 - **Valuation transport proof complete** 🎉
- **KEY MILESTONE**: `linearPlace_valuation_eq_comap` ✅ - The main blocker is SOLVED!
- Core proof strategy:
  - `intValuation_translatePolyEquiv` ✅ - Proves intValuation preserved under translation
  - Key insight: divisibility by (X-α)^n ↔ divisibility by X^n after translation
  - Used `Associates.prime_pow_dvd_iff_le` for count characterization
  - Bidirectional implication via `hdvd_iff` using ideal map properties
- `linearPlace_valuation_eq_comap` ✅ - Uses Valuation.map_div and valuation_of_algebraMap
  - Extends intValuation result to full RatFunc via fraction decomposition
- `translatePolyEquiv_ideal_pow_map` ✅ - Helper for ideal^n mapping
- Fixed translatePolyEquiv proofs (left_inv/right_inv/map_add')
- `residueAt_of_valuation_le_one` now unblocked and complete
- Sorries: 7 → 6

### Cycle 186 - Valuation transport infrastructure for residue vanishing
- Added translation RingEquiv infrastructure:
  - `translatePolyEquiv` ✅ - RingEquiv on Polynomial Fq: p ↦ p.comp(X + C α)
  - `translatePolyEquiv_X_sub_C` ✅ - Sends X - C α to X
  - `translatePolyEquiv_ideal_map` ✅ - Maps ideal span{X-α} to span{X}
  - `translatePolyEquiv_mem_nonZeroDivisors` ✅ - Preserves non-zero-divisors
  - `translateRatFuncHom` ✅ - Lifted RingHom on RatFunc via mapRingHom
  - `translateRatFuncHom_eq_translateBy` ✅ - Agrees with existing translateBy
- Proof structure for residueAt_of_valuation_le_one:
  - Uses Valuation.comap to transport valuations
  - Connects to LaurentSeries.coeff_zero_of_lt_valuation
  - Only blocked by `linearPlace_valuation_eq_comap` (1 sorry)
- `bounded_diagonal_finite_residue_zero` now wired to use residueAt_of_valuation_le_one
- Key insight: Use high-level Valuation API, not manual polynomial decomposition
- Sorries: 9 → 7 (resolved 2 structural, added infrastructure)

### Cycle 185 - Pole cancellation infrastructure for bounded adeles
- Added PoleCancellation section:
  - `canonicalZeroAtFinite` ✅ - Predicate: K(v) = 0 for all finite v
  - `linearPlace` ✅ - HeightOneSpectrum for place (X - α)
  - `bounded_times_LKD_valuation_bound` ✅ - Product valuation: v(g·f) ≤ exp(K(v))
  - `bounded_times_LKD_no_pole` ✅ - When K(v)=0: v(g·f) ≤ 1 (no pole)
  - `residueAt_of_valuation_le_one` (sorry) - Valuation ≤ 1 implies residue = 0
  - `bounded_diagonal_finite_residue_zero` (sorry) - Bounded diagonal has zero finite residue
- Added detailed strategy documentation:
  - liftQ construction approach
  - rawPairing definition via local residues
  - Key properties needed for well-definedness
  - Current infrastructure vs missing pieces
- Sorries: 7 → 9 (2 new intermediate lemmas added)
- Key insight: pole cancellation argument for A_K(D) × L(K-D) formalized

### Cycle 184 - Diagonal pairing infrastructure for RatFunc Fq
- Added DiagonalPairing section:
  - `diagonalEmbedding` ✅ - K →+* FiniteAdeleRing for RatFunc case
  - `diagonalResiduePairing` ✅ - residuePairing on RatFunc Fq
  - `diagonalResiduePairing_bilinear` ✅ - bilinear map structure
  - `diagonalResiduePairing_eq_zero_of_splits` ✅ - vanishing for split denominators
  - `diagonal_pairing_eq_residue` ✅ - equality with residuePairing
- Added RatFuncSpecialization section:
  - `H1_ratfunc` ✅ - specialized H¹(D) type alias
  - `LKD_ratfunc` ✅ - specialized L(K-D) type alias
  - `diagonal_maps_to_zero` ✅ - K-part vanishes under residue sum
  - `polynomial_diagonal_pairing_zero` ✅ - polynomial case of vanishing
  - `diagonalEmbedding_mem_globalSubmodule` ✅ - diagonal K lands in globalSubmodule
  - `diagonal_globalSubmodule_pairing_zero` ✅ - well-definedness for K-part
- Sorries unchanged: 7 total
- Infrastructure for K-part of serrePairing well-definedness now complete

### Cycle 183 - Scalar multiplication for residue at infinity
- `residueAtInfty_smul` ✅ - Proved res_∞(c • f) = c * res_∞(f)
  - Key steps: (c • f).num = C c * f.num, (c • f).denom = f.denom
  - Used: isCoprime_mul_unit_left_left, smul_modByMonic, natDegree_smul_of_smul_regular
- Sorries reduced: 8 → 7

### Cycle 182 - Bilinear pairing infrastructure
- `residueSumTotal_smul` ✅ - Scalar multiplication for total residue sum
- `residueSumTotal_linearMap` ✅ - Total residue as linear map
- `residuePairing` ✅ - Bilinear pairing via product
- `residuePairing_bilinear` ✅ - Full bilinear map structure
- `residuePairing_eq_zero_of_splits` ✅ - Residue theorem for pairing

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
