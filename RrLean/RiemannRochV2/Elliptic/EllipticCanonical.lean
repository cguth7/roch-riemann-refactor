import RrLean.RiemannRochV2.Elliptic.EllipticPlaces
import RrLean.RiemannRochV2.Core.Divisor

/-!
# Canonical Divisor for Elliptic Curves

This file defines the canonical divisor K = 0 for elliptic curves.

## Main Definitions

* `ellipticCanonical` - The canonical divisor K = 0 on an elliptic curve

## Mathematical Background

For an elliptic curve E over a field F:
- The invariant differential ω = dx/(2y) has no zeros and no poles
- Therefore K = div(ω) = 0 (the zero divisor)
- deg(K) = 0, which gives genus g = 1 via g = (deg K + 2)/2

This is a key difference from P¹:
- P¹ has K = -2[∞] with deg(K) = -2 (genus 0)
- Elliptic curves have K = 0 with deg(K) = 0 (genus 1)

## The Invariant Differential

For a Weierstrass curve y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆, the
invariant differential is:
  ω = dx / (2y + a₁x + a₃)

In the simplified form y² = x³ + ax + b (char ≠ 2, 3), this becomes:
  ω = dx / (2y)

The key properties:
1. ω is regular everywhere on E (no poles at finite points)
2. ω has no zeros at finite points
3. At the point at infinity O, ω also has no zero or pole
4. Therefore div(ω) = 0

This is equivalent to saying the canonical bundle Ω¹_E is trivial.

## References

- Silverman, "The Arithmetic of Elliptic Curves", III.5 (Invariant Differentials)
- Hartshorne, "Algebraic Geometry", IV.1 (Canonical Divisor)
-/

noncomputable section

open IsDedekindDomain WeierstrassCurve

namespace RiemannRochV2.Elliptic

variable {F : Type*} [Field F]
variable (W : Affine F) [NonsingularCurve W]

/-! ## The Canonical Divisor on an Elliptic Curve -/

/-- The canonical divisor on an elliptic curve is the zero divisor.

For elliptic curves, the invariant differential ω = dx/(2y) is regular
and nonvanishing everywhere on the curve (including at infinity).
Therefore div(ω) = 0.

This contrasts with P¹ where K = -2[∞]. -/
def ellipticCanonical : DivisorV2 (CoordRing W) := 0

/-- The canonical divisor is zero. -/
@[simp]
lemma ellipticCanonical_eq_zero : ellipticCanonical W = 0 := rfl

/-- The canonical divisor has degree 0. -/
@[simp]
lemma deg_ellipticCanonical : (ellipticCanonical W).deg = 0 := by
  simp [ellipticCanonical, DivisorV2.deg]

/-- The canonical divisor has coefficient 0 at every place. -/
@[simp]
lemma ellipticCanonical_at_place (v : EllipticPlace W) :
    ellipticCanonical W v = 0 := by
  simp [ellipticCanonical]

/-- The canonical divisor is effective (trivially, since it's zero). -/
lemma ellipticCanonical_effective : (ellipticCanonical W).Effective := by
  simp [ellipticCanonical, DivisorV2.Effective]

/-- The support of the canonical divisor is empty. -/
lemma ellipticCanonical_support : (ellipticCanonical W).support = ∅ := by
  simp [ellipticCanonical]

/-! ## Relationship to Genus

For a smooth projective curve, the genus g satisfies:
  deg(K) = 2g - 2

For elliptic curves: deg(K) = 0, so g = 1.
-/

/-- The genus of an elliptic curve is 1.
(Re-exported from EllipticSetup for convenience.) -/
abbrev genus : ℕ := ellipticGenus

/-- The genus formula: deg(K) = 2g - 2 holds for elliptic curves. -/
lemma genus_formula : (ellipticCanonical W).deg = 2 * (genus : ℤ) - 2 := by
  simp only [deg_ellipticCanonical, genus, ellipticGenus]
  ring

/-! ## K - D for Serre Duality

For elliptic curves, Serre duality simplifies because K = 0:
  h¹(D) = ℓ(K - D) = ℓ(-D)

This is much simpler than the P¹ case where K = -2[∞].
-/

/-- K - D = -D for elliptic curves (since K = 0). -/
lemma ellipticCanonical_sub (D : DivisorV2 (CoordRing W)) :
    ellipticCanonical W - D = -D := by
  simp [ellipticCanonical]

/-- The degree of K - D equals -deg(D). -/
lemma deg_ellipticCanonical_sub (D : DivisorV2 (CoordRing W)) :
    (ellipticCanonical W - D).deg = -D.deg := by
  simp [DivisorV2.deg_neg]

/-- If deg(D) > 0, then deg(K - D) = deg(-D) < 0. -/
lemma deg_ellipticCanonical_sub_neg {D : DivisorV2 (CoordRing W)}
    (hD : D.deg > 0) : (ellipticCanonical W - D).deg < 0 := by
  rw [deg_ellipticCanonical_sub]
  omega

/-- If deg(D) ≥ 1, then deg(K - D) ≤ -1. -/
lemma deg_ellipticCanonical_sub_le_neg_one {D : DivisorV2 (CoordRing W)}
    (hD : D.deg ≥ 1) : (ellipticCanonical W - D).deg ≤ -1 := by
  rw [deg_ellipticCanonical_sub]
  omega

/-! ## Comparison with P¹

| Property | P¹ (g=0) | Elliptic (g=1) |
|----------|----------|----------------|
| K | -2[∞] | 0 |
| deg(K) | -2 | 0 |
| K - D for deg(D)=0 | -2[∞] | 0 |
| L(K) | {0} (empty) | {constants} = F |
| h⁰(K) | 0 | 1 |

For P¹: L(K) = L(-2[∞]) = {f : div(f) + K ≥ 0} = {f : div(f) ≥ 2[∞]} = {0}
  (no function can have a zero of order ≥ 2 at infinity without poles elsewhere)

For elliptic: L(K) = L(0) = {f : div(f) ≥ 0} = {constants} = F
  (constants are the only functions without poles)

This gives:
- P¹: h⁰(K) = 0, confirming g = 0 via Riemann-Roch
- Elliptic: h⁰(K) = 1, confirming g = 1 via Riemann-Roch
-/

/-! ## The Riemann-Roch Dimension Formula

For effective divisors D on an elliptic curve with deg(D) > 0:
  ℓ(D) = deg(D)

This is Riemann-Roch with g = 1:
  ℓ(D) - ℓ(K - D) = deg(D) + 1 - g = deg(D)

Since deg(K - D) = -deg(D) < 0, we have ℓ(K - D) = 0 (for deg D > 0).
Therefore ℓ(D) = deg(D).

Contrast with P¹ (g = 0):
  ℓ(D) = deg(D) + 1

The "+1" disappears for elliptic curves!
-/

end RiemannRochV2.Elliptic

end
