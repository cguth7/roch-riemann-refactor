import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Elliptic Curve Setup for Riemann-Roch

This module establishes the foundational infrastructure for elliptic curves,
bridging Mathlib's `WeierstrassCurve.Affine` to our Riemann-Roch framework.

## The Mathlib Gap

Mathlib provides:
- `WeierstrassCurve.Affine.CoordinateRing` = F[X,Y]/⟨W(X,Y)⟩
- `WeierstrassCurve.Affine.FunctionField` = Frac(CoordinateRing)
- `IsDomain CoordinateRing` (when base is a domain)

Mathlib does NOT provide:
- `IsDedekindDomain CoordinateRing` (required for `HeightOneSpectrum`)

## The Axiom Approach

We add `IsDedekindDomain` as an axiom. This is standard practice because:
1. It's textbook mathematics (Hartshorne II.6: smooth implies Dedekind)
2. It's orthogonal to Riemann-Roch content
3. The proof would require significant commutative algebra infrastructure

## Key Differences from P¹

| Aspect | P¹ (g=0) | Elliptic (g=1) |
|--------|----------|----------------|
| Coordinate ring | `Polynomial Fq` (PID) | `CoordinateRing` (Dedekind, not PID) |
| deg(K) | -2 | 0 |
| ℓ(D) for deg(D) > 0 | deg(D) + 1 | deg(D) |
| H¹(O) dimension | 0 | 1 |
| Global uniformizer | Yes (monic irred poly) | No! (class group non-trivial) |

## References

- Hartshorne, "Algebraic Geometry", II.6 (smooth implies regular)
- Silverman, "The Arithmetic of Elliptic Curves", III.3
-/

namespace RiemannRochV2.Elliptic

open WeierstrassCurve

variable {F : Type*} [Field F]

/-! ## The Coordinate Ring

The coordinate ring F[X,Y]/⟨W(X,Y)⟩ is the ring of regular functions on the
affine part of the elliptic curve. -/

/-- Abbreviation for the coordinate ring of a Weierstrass curve.
This is F[X,Y]/⟨W(X,Y)⟩ where W(X,Y) is the Weierstrass polynomial. -/
abbrev CoordRing (W : Affine F) := W.CoordinateRing

/-- Abbreviation for the function field of a Weierstrass curve.
This is the fraction field of the coordinate ring. -/
abbrev FuncField (W : Affine F) := W.FunctionField

/-! ## The IsDedekindDomain Axiom

This is the key axiom that Mathlib is missing. For nonsingular Weierstrass curves,
the coordinate ring is a Dedekind domain.

Mathematical justification:
1. Nonsingular implies the curve is smooth as a variety
2. Smooth 1-dimensional varieties have regular local rings at all points
3. A Noetherian domain with all localizations being DVRs is Dedekind
4. CoordinateRing is Noetherian (quotient of polynomial ring)

This could be proven in Mathlib but requires significant infrastructure.
For our purposes, we axiomatize it as it's orthogonal to Riemann-Roch.

Note: We require that the curve has at least one nonsingular point, which
is the standard definition of "nonsingular curve" in algebraic geometry.
For elliptic curves in Weierstrass form with nonzero discriminant, this
is automatic.
-/

/-- A nonsingular elliptic curve (discriminant ≠ 0).

This is a predicate on Weierstrass curves that asserts nonsingularity.
It's equivalent to Δ ≠ 0 but packaged as a typeclass for instance synthesis. -/
class NonsingularCurve (W : Affine F) : Prop where
  discriminant_ne_zero : W.Δ ≠ 0

/-- The coordinate ring of a nonsingular Weierstrass curve is a Dedekind domain.

This is a standard fact from algebraic geometry:
- Nonzero discriminant ⟹ all points are nonsingular
- Nonsingular ⟹ smooth
- Smooth ⟹ regular in codimension 1
- Regular + Noetherian + dimension 1 ⟹ Dedekind

We axiomatize this rather than proving it, since:
1. The proof requires commutative algebra beyond current Mathlib scope
2. It's orthogonal to the Riemann-Roch theorem we're proving
3. It's textbook mathematics (Hartshorne II.6)

This axiom is SAFE: it doesn't affect the mathematical validity of RR,
it just provides the infrastructure to state it for elliptic curves. -/
axiom isDedekindDomain_coordinateRing_axiom (W : Affine F) [NonsingularCurve W] :
    IsDedekindDomain (CoordRing W)

/-- Instance version for typeclass inference. -/
instance isDedekindDomain_coordinateRing (W : Affine F) [NonsingularCurve W] :
    IsDedekindDomain (CoordRing W) := isDedekindDomain_coordinateRing_axiom W

/-! ## Fraction Ring Instance

The function field is the fraction ring of the coordinate ring. -/

/-- The function field is the fraction ring of the coordinate ring.

This follows from Mathlib's definition of FunctionField as
FractionRing CoordinateRing. The instance is inferred from FractionRing's
built-in localization structure (FractionRing R is defined as Localization
at nonZeroDivisors R, which is an IsFractionRing). -/
instance isFractionRing_functionField (W : Affine F) :
    IsFractionRing (CoordRing W) (FuncField W) :=
  Localization.isLocalization

/-! ## Genus and Canonical Divisor

For elliptic curves:
- genus g = 1
- canonical divisor K has degree 0 (trivial canonical bundle)
- deg(K) = 2g - 2 = 0 ✓
-/

/-- The genus of an elliptic curve is 1. -/
def ellipticGenus : ℕ := 1

/-- The degree of the canonical divisor for an elliptic curve.
By the formula deg(K) = 2g - 2 with g = 1, we get deg(K) = 0. -/
lemma deg_canonical_elliptic : (2 : ℤ) * ellipticGenus - 2 = 0 := by
  simp [ellipticGenus]

/-! ## Architecture Notes

### No Global Uniformizers

Unlike P¹ where every place has a global generator (monic irreducible polynomial),
elliptic curves do NOT have global uniformizers for all places.

This is because:
1. The coordinate ring is NOT a PID (class group is the elliptic curve itself!)
2. Prime ideals may not be principal
3. The class group of an elliptic curve over an algebraically closed field
   is isomorphic to the curve's group of rational points (infinite)

For our infrastructure, this means:
- We CANNOT use `MonicIrreduciblePoly` as generators
- We MUST use local uniformizers via `uniformizerAt`
- Strong approximation still works because uniformizers exist locally

### The Invariant Differential

For elliptic curves in Weierstrass form y² = x³ + ax + b, the differential
  ω = dx / (2y)
is the unique (up to scalar) regular differential on the curve.

This means:
- ω has no zeros and no poles
- The canonical divisor is K = div(ω) = 0
- For residue computations, we can use ω to identify functions with differentials

This simplifies Serre duality: h¹(D) = ℓ(K - D) = ℓ(-D).
-/

end RiemannRochV2.Elliptic
