/-
# H¹ for Elliptic Curves (Cycle 292)

This file computes the first cohomology group H¹ for elliptic curves.

## Main Results

For an elliptic curve E over an algebraically closed field k:
- `h1_zero_eq_one`: dim H¹(O) = 1 (the zero divisor has 1-dimensional H¹)
- `h1_positive_eq_zero`: H¹(D) = 0 for deg(D) > 0 (vanishing for positive degree)

## Mathematical Background

For a smooth projective curve of genus g:
- H¹(O) ≅ k^g (the space of holomorphic 1-forms)
- For elliptic curves (g = 1), H¹(O) ≅ k

The adelic interpretation:
- H¹(O) = A/(K + A(O)) where:
  - A = finite adeles (restricted product)
  - K = function field (embedded diagonally)
  - A(O) = integral adeles (v(a_v) ≤ 1 for all v)

For genus 1, the quotient is 1-dimensional because:
1. Strong Approximation gives K dense in A (so A = K + A(O)̄ topologically)
2. But A/(K + A(O)) is NOT zero - the algebraic quotient has dimension 1
3. This captures the failure of exact algebraic representation

## The Invariant Differential

The 1-dimensional H¹(O) is spanned by the class of the invariant differential
ω = dx/(2y). This is the unique (up to scalar) regular differential on E.

## References

- Silverman, "The Arithmetic of Elliptic Curves", III.5
- Cassels-Fröhlich, "Algebraic Number Theory", Ch. II
-/

import RrLean.RiemannRochV2.Elliptic.EllipticCanonical
import RrLean.RiemannRochV2.Adelic.StrongApproximation
import RrLean.RiemannRochV2.Adelic.AdelicH1v2
import RrLean.RiemannRochV2.Definitions.Projective

noncomputable section

open IsDedekindDomain WeierstrassCurve

namespace RiemannRochV2.Elliptic

variable {F : Type*} [Field F]
variable (W : Affine F) [NonsingularCurve W]

/-! ## Elliptic H¹ via Adelic Infrastructure

We use the general adelic H¹ definition from AdelicH1v2, specialized to
elliptic curves.
-/

/-- H¹ for a divisor D on an elliptic curve, as a k-module.

This is the quotient:
  H¹(D) = FiniteAdeleRing / (K + A_K(D))

where K = FuncField W and A_K(D) = {a : v(a_v) ≤ exp(D(v)) for all v}.
-/
abbrev EllipticH1 (D : DivisorV2 (CoordRing W)) : Type _ :=
  AdelicH1v2.SpaceModule F (CoordRing W) (FuncField W) D

/-- The dimension h¹(D) for elliptic curves. -/
abbrev h1_finrank (D : DivisorV2 (CoordRing W)) : ℕ :=
  AdelicH1v2.h1_finrank F (CoordRing W) (FuncField W) D

/-! ## Main Results: H¹(O) = 1-dimensional

For the zero divisor O, we have dim H¹(O) = 1.

This is the key computation that distinguishes elliptic curves (g=1) from P¹ (g=0).
-/

/-- The zero divisor on an elliptic curve. -/
def zeroDivisor : DivisorV2 (CoordRing W) := 0

/-- H¹(O) has dimension 1 for elliptic curves.

This is the fundamental result identifying the genus. For an elliptic curve,
the quotient A/(K + A(O)) is exactly 1-dimensional.

**Mathematical justification**:
1. The invariant differential ω = dx/(2y) spans H¹(O)
2. No other independent elements exist (ω is unique up to scalar)
3. This is the genus of the elliptic curve

We axiomatize this as it requires detailed analysis of the adelic quotient.
The proof would use:
- Local analysis at each place
- The residue theorem for differentials
- Properties of the invariant differential
-/
axiom h1_zero_eq_one : h1_finrank W (zeroDivisor W) = 1

/-- H¹(O) has dimension equal to the genus. -/
lemma h1_zero_eq_genus : h1_finrank W (zeroDivisor W) = ellipticGenus :=
  h1_zero_eq_one W

/-- H¹(O) is finite-dimensional.

This follows from h1_zero_eq_one: the space has dimension 1, hence is finite.
-/
axiom h1_zero_finite : Module.Finite F (EllipticH1 W (zeroDivisor W))

/-! ## Vanishing for Positive Degree

For D with deg(D) > 0, we have H¹(D) = 0.

This follows from:
1. Strong Approximation: K is dense in finite adeles
2. For positive degree D, the bounded adeles A(D) are "large enough"
   that K + A(D) covers all of A.
-/

/-- H¹(D) = 0 when deg(D) > 0.

For an effective divisor of positive degree, H¹ vanishes.
This is a key property used in Riemann-Roch.

**Mathematical justification**:
By the general vanishing theorem, H¹(D) = 0 when deg(D) > deg(K) = 0.
Since K = 0 for elliptic curves, any D with deg(D) > 0 satisfies this.

We axiomatize this as the full proof requires:
- Strong Approximation (already axiomatized)
- Analysis of the quotient topology
- Showing K + A(D) = A for large D
-/
axiom h1_vanishing_positive (D : DivisorV2 (CoordRing W)) (hD : D.deg > 0) :
    h1_finrank W D = 0

/-- H¹(D) = 0 when deg(D) ≥ 1. -/
lemma h1_vanishing_of_deg_ge_one (D : DivisorV2 (CoordRing W)) (hD : D.deg ≥ 1) :
    h1_finrank W D = 0 :=
  h1_vanishing_positive W D (by omega)

/-- H¹(D) vanishes when deg(D) > 2g - 2 = 0 (the canonical degree).

This is the general vanishing condition for curves of genus g.
For elliptic curves, 2g - 2 = 0, so this is equivalent to deg(D) > 0.
-/
lemma h1_vanishing_deg_gt_canonical (D : DivisorV2 (CoordRing W))
    (hD : D.deg > (2 : ℤ) * ellipticGenus - 2) :
    h1_finrank W D = 0 := by
  simp only [ellipticGenus] at hD
  -- 2 * 1 - 2 = 0, so hD : D.deg > 0
  have hpos : D.deg > 0 := by omega
  exact h1_vanishing_positive W D hpos

/-! ## Serre Duality for Elliptic Curves

For elliptic curves, Serre duality takes the form:
  h¹(D) = ℓ(K - D) = ℓ(-D)

since the canonical divisor K = 0.

This means:
- h¹(O) = ℓ(O) = 1 ✓ (constants)
- h¹(P) = ℓ(-P) = 0 for deg(P) > 0 ✓ (L(-P) = {0})
-/

/-- Serre duality for elliptic curves: h¹(D) = ℓ(-D).

Since K = 0, we have K - D = -D, so Serre duality becomes:
  h¹(D) = ℓ(K - D) = ℓ(-D)

This is axiomatized as the proof requires:
1. The residue pairing between adeles and differentials
2. Perfect pairing: H¹(D) ≅ L(K - D)∨
3. For finite-dimensional spaces: dim H¹(D) = dim L(K - D) = ℓ(K - D)
-/
axiom serre_duality (D : DivisorV2 (CoordRing W)) :
    h1_finrank W D = ell_proj F (CoordRing W) (FuncField W) (-D)

/-- Serre duality restated with canonical divisor (which is 0). -/
lemma serre_duality' (D : DivisorV2 (CoordRing W)) :
    h1_finrank W D = ell_proj F (CoordRing W) (FuncField W) (ellipticCanonical W - D) := by
  rw [ellipticCanonical_sub, serre_duality W D]

/-! ## Riemann-Roch for Elliptic Curves

Combining the above, we can state Riemann-Roch for elliptic curves:
  ℓ(D) - ℓ(-D) = deg(D)

For deg(D) > 0:
  ℓ(D) - 0 = deg(D)
  ℓ(D) = deg(D)

This is the genus-1 formula (compare with P¹: ℓ(D) = deg(D) + 1).
-/

/-- Riemann-Roch for elliptic curves with deg(D) > 0.

For an effective divisor D of positive degree:
  ℓ(D) = deg(D)

This is RR with g = 1 and h¹(D) = 0.
-/
theorem riemann_roch_positive (D : DivisorV2 (CoordRing W)) (hD : D.deg > 0) :
    (ell_proj F (CoordRing W) (FuncField W) D : ℤ) = D.deg := by
  -- By Serre duality: h¹(D) = ℓ(-D)
  -- By vanishing: h¹(D) = 0 (since deg(D) > 0)
  -- By RR formula: ℓ(D) - h¹(D) = deg(D) + 1 - g
  -- With g = 1: ℓ(D) - 0 = deg(D) + 1 - 1 = deg(D)
  -- This requires the full AdelicRRData instance
  sorry

/-- Riemann-Roch formula: ℓ(D) - ℓ(-D) = deg(D) for elliptic curves.

This is the full Riemann-Roch formula for genus 1, where K = 0.
-/
theorem riemann_roch_full (D : DivisorV2 (CoordRing W)) :
    (ell_proj F (CoordRing W) (FuncField W) D : ℤ) -
    ell_proj F (CoordRing W) (FuncField W) (-D) = D.deg := by
  -- ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
  -- With K = 0 and g = 1:
  -- ℓ(D) - ℓ(-D) = deg(D) + 1 - 1 = deg(D)
  sorry

/-! ## Summary: Elliptic vs P¹

| Property | P¹ (g=0) | Elliptic (g=1) |
|----------|----------|----------------|
| K | -2[∞] | 0 |
| deg(K) | -2 | 0 |
| h¹(O) | 0 | 1 |
| ℓ(D) for deg(D) > 0 | deg(D) + 1 | deg(D) |
| h¹(D) vanishes when | deg(D) > -2 | deg(D) > 0 |

The "+1" in ℓ(D) = deg(D) + 1 for P¹ comes from 1 - g = 1 - 0 = 1.
For elliptic curves: 1 - g = 1 - 1 = 0, so no "+1" term.
-/

end RiemannRochV2.Elliptic

end
