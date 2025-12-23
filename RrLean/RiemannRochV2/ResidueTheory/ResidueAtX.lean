import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import RrLean.RiemannRochV2.Core.Basic

/-!
# X-adic Residue for RatFunc Fq

The X-adic residue is the coefficient of X^{-1} in the Laurent series expansion.
This is the residue at the place corresponding to the prime ideal (X).

## Mathematical Background

For F = RatFunc Fq (the rational function field over a finite field):
- The X-adic place corresponds to the prime ideal (X) in Fq[X].
- The completion is Fq((X)) ≅ LaurentSeries Fq.
- Mathlib provides a direct coercion `RatFunc Fq → LaurentSeries Fq`.

## Key Mathlib Tools

- `LaurentSeries K` = `HahnSeries ℤ K` - formal Laurent series
- `HahnSeries.coeff : HahnSeries Γ R → Γ → R` - coefficient extraction
- Coercion `RatFunc F → LaurentSeries F` - X-adic expansion (via algebraMap)

## References

- Rosen "Number Theory in Function Fields" Chapter 4
- Stichtenoth "Algebraic Function Fields and Codes" Section 1.4
-/

noncomputable section

open scoped LaurentSeries
open HahnSeries Polynomial

namespace RiemannRochV2.Residue

variable {Fq : Type*} [Field Fq]

/-- The X-adic residue of a rational function.

This is the residue at the place v = (X), which corresponds to evaluating
at X = 0. The residue is the coefficient of X^{-1} in the Laurent expansion.

For example:
- res_X(1/X) = 1
- res_X(1/X²) = 0
- res_X(X) = 0
- res_X(1/(X-1)) = 0 (no pole at X = 0)
-/
def residueAtX (f : RatFunc Fq) : Fq :=
  (f : LaurentSeries Fq).coeff (-1)

/-- The X-adic residue is additive. -/
theorem residueAtX_add (f g : RatFunc Fq) :
    residueAtX (f + g) = residueAtX f + residueAtX g := by
  simp only [residueAtX, map_add, HahnSeries.coeff_add]

/-- The X-adic residue respects scalar multiplication. -/
theorem residueAtX_smul (c : Fq) (f : RatFunc Fq) :
    residueAtX (c • f) = c • residueAtX f := by
  simp only [residueAtX]
  -- c • f = RatFunc.C c * f
  rw [RatFunc.smul_eq_C_mul]
  rw [map_mul]
  -- Show that (RatFunc.C c : LaurentSeries) = HahnSeries.C c
  have h : ((RatFunc.C c : RatFunc Fq) : LaurentSeries Fq) = HahnSeries.C c := by
    -- RatFunc.C c = (Polynomial.C c : RatFunc)
    rw [← RatFunc.algebraMap_C c]
    -- (Polynomial.C c : RatFunc : LaurentSeries) = (Polynomial.C c : PowerSeries : LaurentSeries)
    rw [show ((algebraMap Fq[X] (RatFunc Fq) (Polynomial.C c) : RatFunc Fq) : LaurentSeries Fq) =
            ((Polynomial.C c : PowerSeries Fq) : LaurentSeries Fq) from (RatFunc.coe_coe _).symm]
    rw [Polynomial.coe_C, HahnSeries.ofPowerSeries_C]
  rw [h, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]

/-- The X-adic residue as a linear map. -/
def residueAtX_linearMap : RatFunc Fq →ₗ[Fq] Fq where
  toFun := residueAtX
  map_add' := residueAtX_add
  map_smul' := residueAtX_smul

@[simp]
theorem residueAtX_zero : residueAtX (0 : RatFunc Fq) = 0 := by
  simp [residueAtX]

/-- The residue of 1/X is 1.

In Laurent series, X maps to `single 1 1`, so X⁻¹ maps to `single (-1) 1`.
The coefficient at -1 of `single (-1) 1` is 1.
-/
theorem residueAtX_inv_X : residueAtX (RatFunc.X⁻¹ : RatFunc Fq) = 1 := by
  simp only [residueAtX]
  -- X in RatFunc maps to single 1 1 in LaurentSeries
  have hX : ((RatFunc.X : RatFunc Fq) : LaurentSeries Fq) = single 1 1 := RatFunc.coe_X
  -- X⁻¹ maps to (single 1 1)⁻¹ = single (-1) 1
  have hXinv : ((RatFunc.X⁻¹ : RatFunc Fq) : LaurentSeries Fq) = (single 1 (1 : Fq))⁻¹ := by
    rw [map_inv₀, hX]
  rw [hXinv, HahnSeries.inv_single, HahnSeries.coeff_single_same]
  simp

/-- The residue of 1/X² is 0. -/
theorem residueAtX_inv_X_sq : residueAtX ((RatFunc.X⁻¹)^2 : RatFunc Fq) = 0 := by
  simp only [residueAtX]
  have hX : ((RatFunc.X : RatFunc Fq) : LaurentSeries Fq) = single 1 1 := RatFunc.coe_X
  have h : (((RatFunc.X⁻¹)^2 : RatFunc Fq) : LaurentSeries Fq) = (single 1 (1 : Fq))⁻¹ ^ 2 := by
    rw [map_pow, map_inv₀, hX]
  rw [h, HahnSeries.inv_single]
  -- (single (-1) 1⁻¹)^2 = single (-2) 1 (since 1⁻¹ = 1 in a field)
  simp only [inv_one]
  have hpow : (single (-1) (1 : Fq))^2 = single (-2) (1 : Fq) := by
    rw [sq, HahnSeries.single_mul_single]
    simp
  rw [hpow, HahnSeries.coeff_single_of_ne]
  omega

/-- The residue of a polynomial is 0 (no pole at X = 0).

Polynomials embed into power series (non-negative powers only),
so the coefficient of X^{-1} is always 0.
-/
theorem residueAtX_polynomial (p : Polynomial Fq) :
    residueAtX (p : RatFunc Fq) = 0 := by
  simp only [residueAtX]
  -- (p : RatFunc : LaurentSeries) = (p : PowerSeries : LaurentSeries) by coe_coe
  rw [show ((p : RatFunc Fq) : LaurentSeries Fq) =
          ((p : PowerSeries Fq) : LaurentSeries Fq) from (RatFunc.coe_coe _).symm]
  -- PowerSeries embeds via ofPowerSeries which uses embDomain with Nat.cast : ℕ → ℤ
  -- The support is in ℕ ⊆ ℤ≥0, so -1 is not in the range
  rw [ofPowerSeries_apply]
  apply embDomain_notin_range
  simp only [Set.mem_range, not_exists]
  intro n hn
  simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at hn
  have h : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  omega

/-- The X-adic residue of 1/(X - c) is 0 when c ≠ 0.

When c ≠ 0, the function 1/(X - c) has no pole at the origin.
The key insight: (X - c) has nonzero constant term (-c ≠ 0), so it is a unit
in PowerSeries. Its inverse is also a PowerSeries (no negative powers),
hence coeff(-1) = 0.
-/
theorem residueAtX_inv_X_sub_ne (c : Fq) (hc : c ≠ 0) :
    residueAtX ((RatFunc.X - RatFunc.C c)⁻¹ : RatFunc Fq) = 0 := by
  simp only [residueAtX]
  set p : Polynomial Fq := Polynomial.X - Polynomial.C c with hp_def
  -- 1. Align RatFunc.X - RatFunc.C c with the polynomial p
  have hp_eq : RatFunc.X - RatFunc.C c = (p : RatFunc Fq) := by
    rw [hp_def, RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub]; rfl
  rw [hp_eq]
  -- 2. Pull the inverse OUTSIDE the coercion
  rw [map_inv₀]
  -- 3. Switch the map: RatFunc -> LS becomes PowerSeries -> LS
  rw [← RatFunc.coe_coe]
  -- 4. Show p is a unit in PowerSeries (constant coeff -c ≠ 0)
  have h_const : PowerSeries.constantCoeff (p : PowerSeries Fq) = -c := by
    simp only [hp_def, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C,
               map_sub, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C]
    ring
  have hp_unit : IsUnit (p : PowerSeries Fq) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, h_const]
    exact (neg_ne_zero.mpr hc).isUnit
  -- 5. Use the unit property: (p : PS)⁻¹ in LS equals ((p⁻¹ : PS) : LS)
  rw [← hp_unit.unit_spec]
  rw [← map_units_inv]
  -- 6. Finish: PowerSeries have no -1 coeff
  rw [HahnSeries.ofPowerSeries_apply]
  apply embDomain_notin_range
  simp only [Set.mem_range, not_exists, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
  intro n hn
  have h : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  omega

end RiemannRochV2.Residue
