import RrLean.RiemannRochV2.Basic
import RrLean.RiemannRochV2.Divisor
import RrLean.RiemannRochV2.RRSpace
import RrLean.RiemannRochV2.Typeclasses
import RrLean.RiemannRochV2.RiemannInequality
import RrLean.RiemannRochV2.Infrastructure
import RrLean.RiemannRochV2.LocalGapInstance

/-!
# Riemann-Roch V2: Constructive Dedekind Domain Approach

This module re-exports all components of the Riemann-Roch V2 formalization.

## Module Structure

* `Basic` - Shared imports from mathlib
* `Divisor` - Divisor theory (DivisorV2, deg, Effective)
* `RRSpace` - Riemann-Roch space L(D) and dimension ℓ(D)
* `Typeclasses` - LocalGapBound, SinglePointBound, BaseDim
* `RiemannInequality` - Main theorems (riemann_inequality_real, _affine)
* `Infrastructure` - Residue field, uniformizer infrastructure
* `LocalGapInstance` - Work toward LocalGapBound instance (Cycles 25-39)

## Affine vs Projective Models

**Affine Model** (current implementation):
- Points = finite places only (HeightOneSpectrum R)
- Proves: ℓ(D) ≤ deg(D) + basedim

**Projective Model** (requires compactification):
- Points = finite + infinite places
- Proves: ℓ(D) ≤ deg(D) + 1
-/
