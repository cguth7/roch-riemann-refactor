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
import RrLean.RiemannRochV2.Adelic.AdelicH1v2
import RrLean.RiemannRochV2.Definitions.Projective
import RrLean.RiemannRochV2.SerreDuality.General.PairingNondegenerate

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
Proof: h¹(O) = 1 > 0, so Module.finite_of_finrank_pos applies.
-/
theorem h1_zero_finite : Module.Finite F (EllipticH1 W (zeroDivisor W)) := by
  have h := h1_zero_eq_one W
  have heq : h1_finrank W (zeroDivisor W) =
      Module.finrank F (EllipticH1 W (zeroDivisor W)) := rfl
  rw [heq] at h
  have hpos : 0 < Module.finrank F (EllipticH1 W (zeroDivisor W)) := by
    rw [h]; exact Nat.one_pos
  exact Module.finite_of_finrank_pos hpos

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

The full Riemann-Roch theorems are proved in `EllipticRRData.lean`:
- `riemann_roch_positive'`: ℓ(D) = deg(D) for deg(D) > 0
- `riemann_roch_full'`: ℓ(D) - ℓ(-D) = deg(D)
- `riemann_roch_fullRRData`: ℓ(D) - ℓ(K-D) = deg(D) + 1 - g

These require the full AdelicRRData instance, which is constructed in that file
using the Euler characteristic theorem.
-/

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

/-! ## Connection to General Serre Duality (Cycle 367)

The general Serre duality theorem from `PairingNondegenerate.lean` states:
  h¹(D) = ℓ(KDiv - D)

For elliptic curves with KDiv = ellipticCanonical = 0, this specializes to:
  h¹(D) = ℓ(0 - D) = ℓ(-D)

This matches the `serre_duality` axiom above. We show this connection explicitly.
-/

open RiemannRochV2.PairingNondegenerate

/-- Helper: The finrank of an R-submodule viewed as a k-module equals
the finrank of its restrictScalars version.

This is because restrictScalars preserves the carrier and the k-module action
comes from the same algebra k → K in both cases. -/
theorem finrank_eq_ell_proj (D : DivisorV2 (CoordRing W))
    [Module.Finite F (RRModuleV2_real (CoordRing W) (FuncField W) D)] :
    Module.finrank F (RRModuleV2_real (CoordRing W) (FuncField W) D) =
    ell_proj F (CoordRing W) (FuncField W) D := by
  -- ell_proj F R K D = Module.finrank F (RRSpace_proj F R K D)
  -- RRSpace_proj F R K D = (RRModuleV2_real R K D).restrictScalars F
  -- The carriers are the same and the F-module structure is the same
  -- So finrank should be equal
  unfold ell_proj RRSpace_proj
  -- Both compute Module.finrank F of essentially the same k-module
  -- The restrictScalars doesn't change the finrank since it preserves
  -- the underlying module structure over the scalar field F
  rfl

/-- The general Serre duality theorem instantiated for elliptic curves.

Uses `serre_duality_finrank` from PairingNondegenerate.lean with:
- k = F (base field)
- R = CoordRing W (coordinate ring)
- K = FuncField W (function field)
- KDiv = ellipticCanonical W = 0 (canonical divisor)

This gives: h¹(D) = ℓ(0 - D) = ℓ(-D).

**Note** (Cycle 372): Now requires `FiniteDimensional` and `Algebra.IsSeparable`
assumptions for the trace-based non-degeneracy proof.
-/
theorem serre_duality_from_general (D : DivisorV2 (CoordRing W))
    [FiniteDimensional F (FuncField W)]
    [Algebra.IsSeparable F (FuncField W)]
    [Module.Finite F (AdelicH1v2.SpaceModule F (CoordRing W) (FuncField W) D)]
    [hfin : Module.Finite F (RRModuleV2_real (CoordRing W) (FuncField W) (-D))] :
    h1_finrank W D = ell_proj F (CoordRing W) (FuncField W) (-D) := by
  -- Need to provide the Module.Finite instance for (ellipticCanonical W - D)
  -- Since ellipticCanonical W - D = -D, we can use the provided instance
  have heq : ellipticCanonical W - D = -D := ellipticCanonical_sub W D
  -- Transport the Module.Finite instance along this equality
  haveI : Module.Finite F (RRModuleV2_real (CoordRing W) (FuncField W) (ellipticCanonical W - D)) := by
    rw [heq]; exact hfin
  -- Apply the general theorem with KDiv = ellipticCanonical W
  have h_general := serre_duality_finrank (R := CoordRing W) (K := FuncField W) F D (ellipticCanonical W)
  -- h_general : Module.finrank F (SpaceModule F R K D) = Module.finrank F (RRModuleV2_real R K (K - D))
  -- Since ellipticCanonical W - D = -D
  rw [heq] at h_general
  -- h_general : Module.finrank F (SpaceModule F R K D) = Module.finrank F (RRModuleV2_real R K (-D))
  calc h1_finrank W D
      = Module.finrank F (AdelicH1v2.SpaceModule F (CoordRing W) (FuncField W) D) := rfl
    _ = Module.finrank F (RRModuleV2_real (CoordRing W) (FuncField W) (-D)) := h_general
    _ = ell_proj F (CoordRing W) (FuncField W) (-D) := finrank_eq_ell_proj W (-D)

/-! ## Status (Cycle 367)

The `serre_duality_from_general` theorem shows that the `serre_duality` axiom
(h¹(D) = ℓ(-D)) is derivable from the general Serre duality theorem in
`PairingNondegenerate.lean`, given the finite-dimensionality assumptions.

The `serre_duality` axiom can now be understood as an instance of the general
Serre duality theorem for the special case of elliptic curves where:
- The canonical divisor is 0
- The base field is F

**Note**: The `serre_duality` axiom is kept for now because the general theorem
has its own axioms (non-degeneracy of the pairing). Once those are proved,
the elliptic-specific axiom becomes redundant.
-/

end RiemannRochV2.Elliptic

end
