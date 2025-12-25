import RrLean.RiemannRochV2.Elliptic.EllipticSetup
import RrLean.RiemannRochV2.Elliptic.EllipticPlaces
import RrLean.RiemannRochV2.Elliptic.EllipticCanonical

/-!
# Elliptic Curve Infrastructure for Riemann-Roch

This module re-exports the elliptic curve infrastructure needed for
instantiating Riemann-Roch on genus 1 curves.

## Module Structure

* `EllipticSetup` - IsDedekindDomain axiom, basic definitions
* `EllipticPlaces` - HeightOneSpectrum, local uniformizers
* `EllipticCanonical` - K = 0 (trivial canonical divisor for g=1)

## Status (Cycle 290)

Setup and canonical divisor complete. Future cycles will add:
- `EllipticH1.lean` - H¹ calculations (dim = 1 for O)
- `EllipticRRData.lean` - ProjectiveAdelicRRData instance

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
