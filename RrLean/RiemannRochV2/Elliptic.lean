import RrLean.RiemannRochV2.Elliptic.EllipticSetup
import RrLean.RiemannRochV2.Elliptic.EllipticPlaces
import RrLean.RiemannRochV2.Elliptic.EllipticCanonical
import RrLean.RiemannRochV2.Elliptic.EllipticH1
-- StrongApproximation typeclass (in Adelic/) with elliptic instance
import RrLean.RiemannRochV2.Adelic.StrongApproximation

/-!
# Elliptic Curve Infrastructure for Riemann-Roch

This module re-exports the elliptic curve infrastructure needed for
instantiating Riemann-Roch on genus 1 curves.

## Module Structure

* `EllipticSetup` - IsDedekindDomain axiom, basic definitions
* `EllipticPlaces` - HeightOneSpectrum, local uniformizers
* `EllipticCanonical` - K = 0 (trivial canonical divisor for g=1)
* `EllipticH1` - H¹ calculations (dim H¹(O) = 1)

## Status (Cycle 292)

Setup, canonical divisor, Strong Approximation, and H¹ complete. Future cycles will add:
- `EllipticRRData.lean` - ProjectiveAdelicRRData instance

## StrongApproximation (CRITICAL)

The `StrongApprox` typeclass is defined as TOPOLOGICAL DENSITY:
```lean
class StrongApprox (R K) : Prop where
  dense_in_finite_adeles : DenseRange (FiniteAdeleRing.algebraMap R K)
```

This is NOT "A = K + O" which would force H¹(O) = 0 and collapse genus!

## Mathematical Background

For an elliptic curve E over a field F:
- genus g = 1
- canonical divisor K ≡ 0 (the invariant differential has no zeros/poles)
- ℓ(D) = deg(D) for deg(D) > 0 (Riemann-Roch with g=1, K=0)
- ℓ(0) = 1 (only constants)
- h¹(O) = dim H¹(E, O) = 1 (key difference from P¹)

## The Axiom Approach

We axiomatize `IsDedekindDomain (CoordinateRing W)` because:
1. It's textbook mathematics (smooth ⟹ Dedekind)
2. Orthogonal to Riemann-Roch content
3. The proof requires significant commutative algebra infrastructure

This is standard practice in formalization for "trivial but tedious" facts.
-/
