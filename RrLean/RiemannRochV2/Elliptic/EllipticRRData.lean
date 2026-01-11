/-
# Elliptic Curve AdelicRRData Instance (Cycle 293)

This file creates the `AdelicRRData` instance for elliptic curves,
completing the abstract Riemann-Roch infrastructure for genus 1.

## Main Definitions

* `EllipticAdelicRRData` - The `AdelicRRData` instance for elliptic curves

## Axioms

We add the remaining axioms needed for the full `AdelicRRData` instance:
* `h1_finite_all` - H¹(D) is finite-dimensional for all D
* `ell_finite_all` - L(D) is finite-dimensional for all D
* `adelic_euler_char` - The adelic Euler characteristic: ℓ(D) - h¹(D) = deg(D)

## Mathematical Background

For an elliptic curve E of genus g = 1:
- The Euler characteristic: χ(D) = ℓ(D) - h¹(D) = deg(D) + 1 - g = deg(D)
- Serre duality: h¹(D) = ℓ(K - D) = ℓ(-D) (since K = 0)
- Full RR: ℓ(D) - ℓ(-D) = deg(D)

The key insight is that the Euler characteristic formula, combined with
Serre duality, gives the full Riemann-Roch theorem.

## References

- Silverman, "The Arithmetic of Elliptic Curves", III.5
- Hartshorne, "Algebraic Geometry", IV.1
-/

import RrLean.RiemannRochV2.Elliptic.EllipticH1
import RrLean.RiemannRochV2.Adelic.AdelicH1v2
import RrLean.RiemannRochV2.Adelic.EulerCharacteristic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring

noncomputable section

open IsDedekindDomain WeierstrassCurve

namespace RiemannRochV2.Elliptic

variable {F : Type*} [Field F] [IsAlgClosed F]
variable (W : Affine F) [NonsingularCurve W]

/-! ## Additional Axioms for Full AdelicRRData

The axioms in EllipticH1 cover:
- h1_zero_eq_one: dim H¹(O) = 1
- h1_vanishing_positive: H¹(D) = 0 for deg(D) > 0
- serre_duality: h¹(D) = ℓ(-D)

We need additional axioms for:
1. Finiteness of H¹(D) for all D
2. Finiteness of L(D) for all D
3. The Euler characteristic formula
-/

/-! ### Degree One Places

For an elliptic curve over an algebraically closed field F, all places have
degree 1, i.e., all residue fields are isomorphic to F.

This is because the residue field κ(v) = R/v.asIdeal is a finite extension of F,
and algebraically closed fields have no proper finite extensions.
-/

/-- All places of an elliptic curve over an algebraically closed field have degree 1.

This means dim_F(κ(v)) = 1 for all places v.

For algebraically closed F:
- κ(v) is a finite extension of F (by Jacobson ring theory)
- But F has no proper finite extensions (IsAlgClosed)
- Therefore κ(v) ≃ F, so dim = 1

PROOF SKETCH (Cycle 344):
1. Fields are Jacobson rings (IsArtinianRing → IsJacobsonRing)
2. Residue field is a finite type F-algebra (quotient of finitely generated algebra)
3. finite_of_finite_type_of_isJacobsonRing gives Module.Finite
4. Algebra.IsIntegral.of_finite gives integrality
5. IsAlgClosed.algebraMap_bijective_of_isIntegral gives bijective algebraMap F → κ(v)
6. Bijective algebraMap implies κ(v) = F, so finrank = 1

The proof is mathematically complete but requires careful handling of scalar tower
instances between F, CoordRing W, quotient, and residue field.
-/
axiom degreeOnePlaces_elliptic (v : HeightOneSpectrum (CoordRing W)) :
    Module.finrank F (residueFieldAtPrime (CoordRing W) v) = 1

/-- DegreeOnePlaces instance for elliptic curves. -/
instance ellipticDegreeOnePlaces : EulerCharacteristic.DegreeOnePlaces F (CoordRing W) where
  residue_finrank_one := degreeOnePlaces_elliptic W

/-! ### Finiteness Axioms -/

/-- H¹(D) is finite-dimensional for all divisors D.

This follows from:
1. For deg(D) > 0: H¹(D) = 0, trivially finite
2. For deg(D) = 0: Requires analysis of A/(K + A(O))
3. For deg(D) < 0: Follows from Serre duality + finiteness of L(-D)

The proof would use compactness of adelic quotients (analytic argument).
We axiomatize this as it's standard and orthogonal to RR content.
-/
axiom h1_finite_all (D : DivisorV2 (CoordRing W)) :
    Module.Finite F (EllipticH1 W D)

/-- Instance version of h1_finite_all for use with euler_characteristic. -/
instance ellipticH1Finite (E : DivisorV2 (CoordRing W)) :
    Module.Finite F (AdelicH1v2.SpaceModule F (CoordRing W) (FuncField W) E) :=
  h1_finite_all W E

/-! ### ℓ(0) = 1 (moved here to break circular dependency)

This lemma is needed for the Euler characteristic theorem proof below.
-/

/-- ℓ(O) = 1 for elliptic curves.

The Riemann-Roch space L(0) consists only of constants.

Proof via Serre duality (breaks circular dependency with Euler char):
- serre_duality W 0 : h¹(0) = ℓ(-0) = ℓ(0)
- h1_zero_eq_one W : h¹(0) = 1
- Therefore: ℓ(0) = 1
-/
lemma ell_zero_eq_one : ell_proj F (CoordRing W) (FuncField W) (zeroDivisor W) = 1 := by
  -- zeroDivisor W = 0 by definition
  unfold zeroDivisor
  -- By Serre duality: h¹(0) = ℓ(-0) = ℓ(0)
  have h_serre := serre_duality W 0
  simp only [neg_zero] at h_serre
  -- h_serre : h1_finrank W 0 = ell_proj ... 0
  -- h1_zero_eq_one W : h1_finrank W (zeroDivisor W) = 1
  have h_h1 : h1_finrank W 0 = 1 := by
    have := h1_zero_eq_one W
    unfold zeroDivisor at this
    exact this
  -- Combine: ell_proj ... 0 = 1
  omega

/-! ### ProperCurve Instance (needed for finiteness proof)

Elliptic curves are proper, so L(0) = constants = 1-dimensional.
-/

/-- Elliptic curves are proper curves (L(0) = k). -/
instance ellipticProperCurve : ProperCurve F (CoordRing W) (FuncField W) where
  ell_zero_eq_one := by
    have h := ell_zero_eq_one W
    unfold zeroDivisor at h
    exact h

/-! ### ℓ(D) ≥ 1 for effective D with positive degree (Cycle 343)

For effective D, we have L(0) ⊆ L(D), so ℓ(D) ≥ ℓ(0) = 1.
-/

/-- For effective D, ℓ(D) ≥ 1.

Since 0 ≤ D (effective), we have L(0) ⊆ L(D) by monotonicity.
Combined with ℓ(0) = 1, this gives ℓ(D) ≥ 1.
-/
lemma ell_proj_ge_one_of_effective (D : DivisorV2 (CoordRing W)) (hD : D.Effective) :
    1 ≤ ell_proj F (CoordRing W) (FuncField W) D := by
  have h_mono := ell_proj_mono F (CoordRing W) (FuncField W) hD
    (EulerCharacteristic.ell_finite_of_effective F (CoordRing W) (FuncField W) D hD)
  have h_zero := ell_zero_eq_one W
  unfold zeroDivisor at h_zero
  omega

/-- For effective D with positive degree, ℓ(D) > 0. -/
lemma ell_proj_pos_of_effective (D : DivisorV2 (CoordRing W)) (hD : D.Effective) :
    0 < ell_proj F (CoordRing W) (FuncField W) D := by
  have h := ell_proj_ge_one_of_effective W D hD
  omega

/-! ### H¹ Finiteness for -D effective (Cycle 343)

When -D is effective, we can prove H¹(D) is finite via Serre duality.
-/

/-- H¹(D) is finite when -D is effective.

Proof:
1. By Serre duality: h1_finrank W D = ell_proj ... (-D)
2. Since -D is effective: ell_proj(-D) ≥ 1 by ell_proj_ge_one_of_effective
3. So h1_finrank W D ≥ 1 > 0
4. Use Module.finite_of_finrank_pos
-/
lemma h1_finite_of_neg_effective (D : DivisorV2 (CoordRing W)) (hD : (-D).Effective) :
    Module.Finite F (EllipticH1 W D) := by
  -- By Serre duality: h1_finrank W D = ell_proj ... (-D)
  have h_serre := serre_duality W D
  -- Since -D is effective, ell_proj(-D) ≥ 1
  have h_ell_pos := ell_proj_pos_of_effective W (-D) hD
  -- So h1_finrank W D ≥ 1 > 0
  have h_h1_pos : 0 < h1_finrank W D := by
    rw [h_serre]
    exact h_ell_pos
  -- Use Module.finite_of_finrank_pos
  exact Module.finite_of_finrank_pos h_h1_pos

/-! ### Finiteness of L(D) (Cycle 342)

L(D) is finite-dimensional for all divisors D.

For effective D: Use `ell_finite_of_effective` from EulerCharacteristic.lean
For general D: L(D) ⊆ L(D⁺) where D⁺ is the positive part
-/

/-- The positive part of a divisor: D⁺(v) = max(D(v), 0). -/
def DivisorV2.posPart (D : DivisorV2 (CoordRing W)) : DivisorV2 (CoordRing W) :=
  D.mapRange (max · 0) (by simp)

/-- The positive part is effective. -/
lemma DivisorV2.posPart_effective (D : DivisorV2 (CoordRing W)) :
    (DivisorV2.posPart W D).Effective := by
  intro v
  simp only [DivisorV2.posPart, Finsupp.mapRange_apply]
  exact le_max_right _ _

/-- D ≤ D.posPart pointwise. -/
lemma DivisorV2.le_posPart (D : DivisorV2 (CoordRing W)) : D ≤ DivisorV2.posPart W D := by
  intro v
  simp only [DivisorV2.posPart, Finsupp.mapRange_apply]
  exact le_max_left _ _

/-- L(D) ⊆ L(D.posPart) via monotonicity. -/
lemma RRSpace_proj_le_posPart (D : DivisorV2 (CoordRing W)) :
    RRSpace_proj F (CoordRing W) (FuncField W) D ≤
    RRSpace_proj F (CoordRing W) (FuncField W) (DivisorV2.posPart W D) :=
  RRSpace_proj_mono F (CoordRing W) (FuncField W) (DivisorV2.le_posPart W D)

/-- L(D) is finite-dimensional for all divisors D.

This is now a THEOREM using `ell_finite_of_effective` from EulerCharacteristic.lean.

Proof:
- D.posPart is effective
- L(D.posPart) is finite by `ell_finite_of_effective`
- L(D) ⊆ L(D.posPart), so L(D) is finite via the inclusion map
-/
theorem ell_finite_all (D : DivisorV2 (CoordRing W)) :
    Module.Finite F (RRSpace_proj F (CoordRing W) (FuncField W) D) := by
  -- D.posPart is effective
  have heff : (DivisorV2.posPart W D).Effective := DivisorV2.posPart_effective W D
  -- L(D.posPart) is finite by ell_finite_of_effective
  haveI hfin : Module.Finite F (RRSpace_proj F (CoordRing W) (FuncField W) (DivisorV2.posPart W D)) :=
    EulerCharacteristic.ell_finite_of_effective F (CoordRing W) (FuncField W) (DivisorV2.posPart W D) heff
  -- L(D) is a submodule of L(D.posPart)
  have hsub : RRSpace_proj F (CoordRing W) (FuncField W) D ≤
      RRSpace_proj F (CoordRing W) (FuncField W) (DivisorV2.posPart W D) :=
    RRSpace_proj_le_posPart W D
  -- The inclusion map from L(D) to L(D.posPart)
  let incl : ↥(RRSpace_proj F (CoordRing W) (FuncField W) D) →ₗ[F]
      ↥(RRSpace_proj F (CoordRing W) (FuncField W) (DivisorV2.posPart W D)) :=
    { toFun := fun f => ⟨f.val, hsub f.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- The inclusion is injective (obvious from construction)
  have h_inj : Function.Injective incl := by
    intro x y h
    simp only [incl, LinearMap.coe_mk, AddHom.coe_mk, Subtype.mk.injEq] at h
    exact Subtype.ext h
  -- Use Module.Finite.of_injective: injective linear map into finite module means domain is finite
  exact Module.Finite.of_injective incl h_inj

/-- Instance version of ell_finite_all for use with euler_characteristic. -/
instance ellipticEllFinite (E : DivisorV2 (CoordRing W)) :
    Module.Finite F (RRSpace_proj F (CoordRing W) (FuncField W) E) :=
  ell_finite_all W E

/-! ### The Euler Characteristic Theorem

The adelic Euler characteristic is the fundamental relation:
  χ(D) = ℓ(D) - h¹(D) = deg(D) + 1 - g

For genus 1: χ(D) = deg(D).

This is now a theorem using our proved euler_characteristic!
-/

/-- The adelic Euler characteristic for elliptic curves.

ℓ(D) - h¹(D) = deg(D) + 1 - g = deg(D) (for g = 1)

This is the fundamental relation in adelic Riemann-Roch.
Combined with Serre duality, it gives the full RR formula.

PROVED using the general euler_characteristic theorem from EulerCharacteristic.lean!
-/
theorem adelic_euler_char (D : DivisorV2 (CoordRing W)) :
    (ell_proj F (CoordRing W) (FuncField W) D : ℤ) - h1_finrank W D =
    D.deg + 1 - ellipticGenus := by
  -- Use the general euler_characteristic theorem
  -- We need: h_genus = h1(0) = ellipticGenus, h_ell_zero = ell(0) = 1
  have h_genus : h1_finrank W (0 : DivisorV2 (CoordRing W)) = ellipticGenus := by
    have := h1_zero_eq_one W
    unfold zeroDivisor at this
    simp only [ellipticGenus]
    exact this
  have h_ell_zero : ell_proj F (CoordRing W) (FuncField W) 0 = 1 := by
    have := ell_zero_eq_one W
    unfold zeroDivisor at this
    exact this
  -- Apply euler_characteristic
  have h := EulerCharacteristic.euler_characteristic F (CoordRing W) (FuncField W) D ellipticGenus h_genus h_ell_zero
  -- h : eulerChar F (CoordRing W) (FuncField W) D = D.deg + 1 - ellipticGenus
  -- eulerChar is defined as (ell_proj ... D : ℤ) - h1_finrank ... D
  unfold EulerCharacteristic.eulerChar at h
  exact h

/-- Simplified form: ℓ(D) - h¹(D) = deg(D) for elliptic curves. -/
lemma euler_char_simplified (D : DivisorV2 (CoordRing W)) :
    (ell_proj F (CoordRing W) (FuncField W) D : ℤ) - h1_finrank W D = D.deg := by
  have h := adelic_euler_char W D
  simp only [ellipticGenus] at h
  omega

/-! ## The AdelicRRData Instance

Now we can instantiate `AdelicRRData` for elliptic curves.
-/

/-- The AdelicRRData instance for elliptic curves.

This packages all the axioms into the typeclass structure expected by
the general Riemann-Roch infrastructure.

Parameters:
- canonical = ellipticCanonical W = 0 (the zero divisor)
- genus = 1
-/
instance ellipticAdelicRRData :
    AdelicH1v2.AdelicRRData F (CoordRing W) (FuncField W) (ellipticCanonical W) ellipticGenus where
  h1_finite := h1_finite_all W
  ell_finite := ell_finite_all W
  h1_vanishing := fun D hdeg => by
    -- hdeg : D.deg > 2 * 1 - 2 = 0
    have hpos : D.deg > 0 := by simp [ellipticGenus] at hdeg; omega
    exact h1_vanishing_positive W D hpos
  adelic_rr := adelic_euler_char W
  serre_duality := fun D => by
    -- h¹(D) = ℓ(K - D) = ℓ(0 - D) = ℓ(-D)
    rw [ellipticCanonical_sub]
    exact serre_duality W D
  deg_canonical := by
    -- deg(K) = 2g - 2 = 2 * 1 - 2 = 0
    -- ellipticCanonical W = 0, and deg(0) = 0
    simp only [ellipticCanonical, ellipticGenus]
    rfl

/-! ## Proving the Riemann-Roch Theorems

With the AdelicRRData instance, we can now prove the RR theorems
that were left as sorry in EllipticH1.lean.
-/

/-- Riemann-Roch for positive degree divisors on elliptic curves.

For deg(D) > 0: ℓ(D) = deg(D)

Proof:
1. By vanishing: h¹(D) = 0 (since deg > 0)
2. By Euler characteristic: ℓ(D) - h¹(D) = deg(D)
3. Therefore: ℓ(D) = deg(D)
-/
theorem riemann_roch_positive' (D : DivisorV2 (CoordRing W)) (hD : D.deg > 0) :
    (ell_proj F (CoordRing W) (FuncField W) D : ℤ) = D.deg := by
  -- h¹(D) = 0 by vanishing
  have h_vanish : h1_finrank W D = 0 := h1_vanishing_positive W D hD
  -- ℓ(D) - h¹(D) = deg(D) by Euler characteristic
  have h_euler := euler_char_simplified W D
  -- Substitute h¹(D) = 0
  simp only [h_vanish, CharP.cast_eq_zero, sub_zero] at h_euler
  exact h_euler

/-- Full Riemann-Roch for elliptic curves.

ℓ(D) - ℓ(-D) = deg(D)

This is the genus-1 Riemann-Roch formula.

Proof:
1. By Serre duality: h¹(D) = ℓ(-D)
2. By Euler characteristic: ℓ(D) - h¹(D) = deg(D)
3. Substituting: ℓ(D) - ℓ(-D) = deg(D)
-/
theorem riemann_roch_full' (D : DivisorV2 (CoordRing W)) :
    (ell_proj F (CoordRing W) (FuncField W) D : ℤ) -
    ell_proj F (CoordRing W) (FuncField W) (-D) = D.deg := by
  -- By Serre duality: h¹(D) = ℓ(-D)
  have h_serre := serre_duality W D
  -- By Euler characteristic: ℓ(D) - h¹(D) = deg(D)
  have h_euler := euler_char_simplified W D
  -- Substitute
  rw [h_serre] at h_euler
  exact h_euler

/-! ## Corollaries

Additional consequences of Riemann-Roch for elliptic curves.

Note: `ell_zero_eq_one` was moved earlier in the file to break
the circular dependency with the Euler characteristic theorem.
-/

/-- ℓ(-D) = 0 for deg(D) > 0.

If deg(D) > 0, then deg(-D) < 0, so L(-D) = {0}.
-/
lemma ell_neg_eq_zero (D : DivisorV2 (CoordRing W)) (hD : D.deg > 0) :
    ell_proj F (CoordRing W) (FuncField W) (-D) = 0 := by
  -- By RR: ℓ(D) - ℓ(-D) = deg(D)
  have h_rr := riemann_roch_full' W D
  -- By positive RR: ℓ(D) = deg(D)
  have h_pos := riemann_roch_positive' W D hD
  -- Substitute: deg(D) - ℓ(-D) = deg(D)
  omega

/-! ### Comparison: elliptic vs P¹

For deg(D) > 0:
- P¹: ℓ(D) = deg(D) + 1
- Elliptic: ℓ(D) = deg(D)

The "+1" difference is the genus: 1 - g where g = 0 for P¹ and g = 1 for elliptic.
-/

/-! ## FullRRData Instance (Cycle 323)

With AdelicRRData and ProperCurve, we get FullRRData via the bridge.
This completes the abstract Riemann-Roch infrastructure for elliptic curves.
-/

/-- The FullRRData instance for elliptic curves.

This is the capstone result: combining AdelicRRData + ProperCurve via the
bridge from AdelicH1v2.lean to get all FullRRData axioms.

The full Riemann-Roch theorem is now available for elliptic curves:
  ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
where K = 0 (the zero divisor) and g = 1.
-/
instance ellipticFullRRData : FullRRData F (CoordRing W) (FuncField W) :=
  AdelicH1v2.adelicRRData_to_FullRRData F (CoordRing W) (FuncField W)
    (canonical := ellipticCanonical W) (genus := ellipticGenus)

/-- The full Riemann-Roch theorem for elliptic curves via FullRRData.

For any divisor D on an elliptic curve:
  ℓ(D) - ℓ(-D) = deg(D)

This is the genus-1 specialization of the general formula ℓ(D) - ℓ(K-D) = deg(D) + 1 - g.
Since K = 0 and g = 1, this becomes ℓ(D) - ℓ(-D) = deg(D).
-/
theorem riemann_roch_fullRRData (D : DivisorV2 (CoordRing W)) :
    (ell_proj F (CoordRing W) (FuncField W) D : ℤ) -
    ell_proj F (CoordRing W) (FuncField W) (ellipticCanonical W - D) =
    D.deg + 1 - ellipticGenus := by
  exact (ellipticFullRRData W).serre_duality_eq D

/-! ## Summary of Axiom Stack

| Axiom | File | Purpose |
|-------|------|---------|
| IsDedekindDomain CoordRing | EllipticSetup | HeightOneSpectrum exists |
| exists_localUniformizer | EllipticPlaces | Local uniformizers exist |
| h1_zero_eq_one | EllipticH1 | dim H¹(O) = 1 (genus) |
| h1_zero_finite | EllipticH1 | H¹(O) is finite-dimensional |
| h1_vanishing_positive | EllipticH1 | H¹(D) = 0 for deg > 0 |
| serre_duality | EllipticH1 | h¹(D) = ℓ(-D) |
| h1_finite_all | EllipticRRData | H¹(D) finite for all D |
| ell_finite_all | EllipticRRData | L(D) finite for all D |
| adelic_euler_char | EllipticRRData | ℓ(D) - h¹(D) = deg(D) |

Total: 9 axioms for elliptic curve infrastructure (plus StrongApprox).

These are all standard facts in algebraic geometry:
- Finiteness follows from function field structure
- Euler characteristic from residue theorem / Riemann inequality
- Serre duality from residue pairing perfectness
-/

end RiemannRochV2.Elliptic

end
