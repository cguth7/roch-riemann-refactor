import RrLean.RiemannRochV2.SerreDuality.Abstract
import RrLean.RiemannRochV2.SerreDuality.RatFuncResidues
import RrLean.RiemannRochV2.SerreDuality.RatFuncPairing
import RrLean.RiemannRochV2.SerreDuality.DimensionScratch

/-!
# Serre Duality

This module re-exports the Serre duality infrastructure split across:

* `SerreDuality/Abstract.lean` - Abstract pairing types and statements
* `SerreDuality/RatFuncResidues.lean` - Residue infrastructure for RatFunc Fq
* `SerreDuality/RatFuncPairing.lean` - Concrete pairing construction

## Architecture

The split follows the reviewer's recommendation (Cycle 189):

1. **Abstract layer**: Type-correct placeholder pairing (definitionally 0),
   non-degeneracy statements, dimension equality.

2. **Residue layer**: `residueSumTotal`, `residuePairing`, residue theorem
   for split denominators. No adeles, no quotients.

3. **Pairing layer**: Pole cancellation, valuation transport, raw pairing,
   the `serrePairing_ratfunc` construction (currently sorry).

## Key Sorries

* `serrePairing_left_nondegen` / `serrePairing_right_nondegen` in Abstract.lean
* `finrank_eq_of_perfect_pairing` in Abstract.lean
* `serrePairing_ratfunc` in RatFuncPairing.lean

## Outstanding Issue

The current H¹(D) uses `FiniteAdeleRing` (no infinity component), but the
residue theorem requires all places including infinity. Resolution options:

* **Option A**: Refactor to use `FullAdeleRing` for H¹
* **Option B**: Define pairing via `-residueAtInfty(k·f)` with approximation

See `RatFuncPairing.lean` strategy notes for details.
-/
