import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Order

/-!
# Riemann-Roch V2: Basic Imports and Setup

This module provides the shared imports for the constructive Dedekind domain
approach to Riemann-Roch.

## Strategy (Jiedong Jiang approach)

1. **Points**: HeightOneSpectrum R (height-1 primes of Dedekind domain R)
2. **Divisors**: HeightOneSpectrum R →₀ ℤ (finitely supported formal sums)
3. **L(D)**: Defined via valuations at each prime
4. **ℓ(D)**: Module.length (additive in exact sequences)
5. **Proofs**: Use DVR localization and exact sequence additivity

## Affine vs Projective Models (Cycle 23 Discovery)

**Affine Model** (current HeightOneSpectrum R implementation):
- Points = finite places only (height-1 primes of R)
- L(0) = R (all integral functions) → ℓ(0) = ∞ for Dedekind domains
- Proves: ℓ(D) ≤ deg(D) + ℓ(0) (affine Riemann inequality)
- Typeclass: `LocalGapBound R K` (gap ≤ 1 via evaluation map)

**Projective Model** (requires compactification):
- Points = finite + infinite places (complete curve)
- L(0) = k (only constants) → ℓ(0) = 1
- Proves: ℓ(D) ≤ deg(D) + 1 (classical Riemann inequality)
- Typeclass: `SinglePointBound R K extends LocalGapBound R K`

## References
- mathlib: RingTheory.DedekindDomain.*
- mathlib: RingTheory.Length (Module.length_eq_add_of_exact)
-/

namespace RiemannRochV2

open IsDedekindDomain

end RiemannRochV2
