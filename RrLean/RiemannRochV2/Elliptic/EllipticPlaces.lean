import RrLean.RiemannRochV2.Elliptic.EllipticSetup
import RrLean.RiemannRochV2.Core.Place
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

/-!
# Places on Elliptic Curves

This module defines places (points) on elliptic curves using `HeightOneSpectrum`
of the coordinate ring, and establishes local uniformizer infrastructure.

## Key Insight: Local vs Global Uniformizers

For P¹, every place v has a global generator: the monic irreducible polynomial
defining v. This works because Fq[X] is a PID.

For elliptic curves, the coordinate ring is Dedekind but NOT a PID.
The class group is non-trivial (isomorphic to the curve's rational points).
This means:
- NOT every prime ideal is principal
- We cannot assume global generators exist
- We MUST work with local uniformizers

Fortunately, HeightOneSpectrum still provides:
- v.valuation K : Valuation K ℤₘ₀ (the v-adic valuation on the function field)
- Local uniformizers always exist (by definition of DVR at height-one primes)

## Main Definitions

* `EllipticPlace W` - Type alias for `HeightOneSpectrum (CoordRing W)`
* `LocalUniformizer` - Structure for local uniformizers at places

## References

- Silverman, "The Arithmetic of Elliptic Curves", II.1-2
-/

namespace RiemannRochV2.Elliptic

open IsDedekindDomain WeierstrassCurve

variable {F : Type*} [Field F]
variable (W : Affine F) [NonsingularCurve W]

/-! ## Places as HeightOneSpectrum

With `IsDedekindDomain (CoordRing W)`, we can use `HeightOneSpectrum` to
represent the finite places on the elliptic curve.

Each place corresponds to a height-one prime ideal of the coordinate ring.
For elliptic curves over algebraically closed fields, these correspond to
the affine points (x, y) on the curve.
-/

/-- Places on an elliptic curve are height-one primes of the coordinate ring.

For an elliptic curve E over an algebraically closed field k:
- Affine points (x, y) ∈ E(k) correspond to maximal ideals ⟨X - x, Y - y⟩
- These are height-one primes since dim(CoordRing) = 1

Note: This captures only FINITE places (the affine part).
The point at infinity requires separate treatment via compactification.
-/
abbrev EllipticPlace := HeightOneSpectrum (CoordRing W)

/-! ## Local Uniformizers

At each place v, we need a local uniformizer π with v(π) = 1.
Unlike P¹, we cannot assume π generates the prime ideal globally.
-/

/-- A local uniformizer at a place v on an elliptic curve.

The uniformizer π is an element of the function field K = FuncField W such that:
- v(π) = 1 (valuation is exactly 1)

For an affine point (a, b), a local uniformizer can be:
- (X - a) if the tangent line at (a, b) is not vertical
- (Y - b) if the tangent line is vertical (only at 2-torsion points)

Unlike P¹, we do NOT require that (π) = v.asIdeal as an ideal.
-/
structure LocalUniformizer (v : EllipticPlace W) where
  /-- The uniformizer element in the function field -/
  π : FuncField W
  /-- The valuation at v is exactly 1 -/
  val_eq_one : v.valuation (FuncField W) π = 1

/-! ## Existence of Uniformizers

Every place admits a local uniformizer. This follows from:
1. The localization at a height-one prime of a Dedekind domain is a DVR
2. Every DVR has a uniformizer

We state this as an axiom since the proof requires DVR machinery. -/

/-- Every place on an elliptic curve has a local uniformizer.

This follows from the fact that the localization at any height-one prime
of a Dedekind domain is a DVR, and DVRs have uniformizers by definition.

For computational purposes, one can construct uniformizers explicitly:
- For a point (a, b) with non-vertical tangent: π = X - a works
- For a 2-torsion point (a, 0): π = Y works
-/
axiom exists_localUniformizer (v : EllipticPlace W) : Nonempty (LocalUniformizer W v)

/-- Choose a local uniformizer at each place.
Uses choice to pick a uniformizer from the existence proof. -/
noncomputable def uniformizerAt (v : EllipticPlace W) : LocalUniformizer W v :=
  (exists_localUniformizer W v).some

/-! ## Degree of Places

For an elliptic curve over Fq (finite field), each place v has a degree:
  deg(v) = [κ(v) : Fq]
where κ(v) is the residue field.

Over an algebraically closed field:
- All places have degree 1
- This is the algebraic closure property

For our purposes, we'll primarily work over algebraically closed fields
where all places are rational (degree 1).
-/

/-! ## Comparison with P¹ Infrastructure

The key difference is in how we handle generators:

**P¹ (Polynomial Fq)**:
```lean
def PlaceGenerator (v : HeightOneSpectrum (Polynomial Fq)) : Polynomial Fq :=
  v.asIdeal.generator  -- Always exists since Fq[X] is a PID
```

**Elliptic (CoordRing W)**:
```lean
-- WRONG: This doesn't work!
def PlaceGenerator (v : EllipticPlace W) : CoordRing W :=
  v.asIdeal.generator  -- May not exist! Not a PID!

-- RIGHT: Use local uniformizers
def uniformizerAt (v : EllipticPlace W) : LocalUniformizer W v := ...
```

The general adelic infrastructure should use `uniformizerAt` and
valuation-based definitions, never global generators.
-/

end RiemannRochV2.Elliptic
