import RrLean.RiemannRochV2.ResidueTheory.ResidueAtX
import RrLean.RiemannRochV2.ResidueTheory.ResidueAtLinear

/-!
# General Residue via Translation

The `residueAtLinear` definition using "multiply by (X-α) and evaluate" only works
correctly for simple poles. For higher-order poles it returns 0, which breaks additivity.

The correct approach: define residue at α by translating to the origin and using
the robust `residueAtX` definition (HahnSeries.coeff (-1)).

  res_α(f(X)) := res_0(f(X + α))

This inherits linearity from `residueAtX` automatically!

## Main Definitions

- `translateBy α f`: translate f by α, i.e., f(X) ↦ f(X + α)
- `residueAt α f`: the residue of f at α, defined via translation
- `residueAt_linearMap α`: the residue at α as a linear map

## References

- Rosen "Number Theory in Function Fields" Chapter 4
- Stichtenoth "Algebraic Function Fields and Codes" Section 1.4
-/

noncomputable section

open scoped LaurentSeries
open HahnSeries Polynomial

namespace RiemannRochV2.Residue

variable {Fq : Type*} [Field Fq]

/-- Helper: translate a rational function by α, i.e., f(X) ↦ f(X + α).

For f = p/q, this computes (p.comp (X + C α)) / (q.comp (X + C α)).
Composition preserves coprimality and non-zero denominators.
-/
def translateBy (α : Fq) (f : RatFunc Fq) : RatFunc Fq :=
  let p' := f.num.comp (Polynomial.X + Polynomial.C α)
  let q' := f.denom.comp (Polynomial.X + Polynomial.C α)
  algebraMap (Polynomial Fq) (RatFunc Fq) p' / algebraMap (Polynomial Fq) (RatFunc Fq) q'

/-- Helper: composition with X + C α preserves non-zero monic polynomials. -/
private lemma comp_shift_ne_zero (α : Fq) (p : Polynomial Fq) (hp : p.Monic) :
    p.comp (Polynomial.X + Polynomial.C α) ≠ 0 := by
  intro h
  -- p is monic, so p ≠ 0
  have hp_ne : p ≠ 0 := hp.ne_zero
  -- (X + C α) has degree 1
  have hshift_deg : (Polynomial.X + Polynomial.C α).natDegree = 1 := Polynomial.natDegree_X_add_C α
  -- (p.comp (X + C α)).natDegree = p.natDegree * 1 = p.natDegree
  have hdeg : (p.comp (Polynomial.X + Polynomial.C α)).natDegree = p.natDegree := by
    rw [Polynomial.natDegree_comp, hshift_deg, mul_one]
  rw [h, Polynomial.natDegree_zero] at hdeg
  -- If p.natDegree = 0 and p is monic, then p = 1
  -- And 1.comp q = 1 ≠ 0 for any q, so h would be false
  have h1 : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hp hdeg.symm
  rw [h1, Polynomial.one_comp] at h
  exact one_ne_zero h

/-- Translation by α is additive. -/
theorem translateBy_add (α : Fq) (f g : RatFunc Fq) :
    translateBy α (f + g) = translateBy α f + translateBy α g := by
  simp only [translateBy]
  -- Let shift = X + C α for readability
  set shift := Polynomial.X + Polynomial.C α with hshift_def
  -- Use num_denom_add: (f + g).num * (f.denom * g.denom) = (f.num * g.denom + f.denom * g.num) * (f + g).denom
  have hrel := RatFunc.num_denom_add f g
  -- Compose both sides with shift
  have hrel_comp := congr_arg (fun p => p.comp shift) hrel
  simp only [Polynomial.mul_comp, Polynomial.add_comp] at hrel_comp
  -- Show both LHS and RHS denominators are nonzero
  have hf_denom_comp_ne : f.denom.comp shift ≠ 0 := comp_shift_ne_zero α f.denom (RatFunc.monic_denom f)
  have hg_denom_comp_ne : g.denom.comp shift ≠ 0 := comp_shift_ne_zero α g.denom (RatFunc.monic_denom g)
  have hfg_denom_comp_ne : (f + g).denom.comp shift ≠ 0 :=
    comp_shift_ne_zero α (f + g).denom (RatFunc.monic_denom (f + g))
  have hf_denom_ne : (algebraMap (Polynomial Fq) (RatFunc Fq) (f.denom.comp shift)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hf_denom_comp_ne
  have hg_denom_ne : (algebraMap (Polynomial Fq) (RatFunc Fq) (g.denom.comp shift)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hg_denom_comp_ne
  have hfg_denom_ne : (algebraMap (Polynomial Fq) (RatFunc Fq) ((f + g).denom.comp shift)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hfg_denom_comp_ne
  -- Goal: algebraMap _ _ ((f+g).num.comp shift) / algebraMap _ _ ((f+g).denom.comp shift) =
  --       algebraMap _ _ (f.num.comp shift) / algebraMap _ _ (f.denom.comp shift) +
  --       algebraMap _ _ (g.num.comp shift) / algebraMap _ _ (g.denom.comp shift)
  rw [div_add_div _ _ hf_denom_ne hg_denom_ne]
  rw [div_eq_div_iff hfg_denom_ne (mul_ne_zero hf_denom_ne hg_denom_ne)]
  simp only [← map_mul, ← map_add]
  -- Goal closes with congr because hrel_comp provides the polynomial equality
  congr 1

/-- Translation by α respects scalar multiplication. -/
theorem translateBy_smul (α : Fq) (c : Fq) (f : RatFunc Fq) :
    translateBy α (c • f) = c • translateBy α f := by
  simp only [translateBy]
  set shift := Polynomial.X + Polynomial.C α with hshift_def
  -- c • f = RatFunc.C c * f = algebraMap _ _ (Polynomial.C c) * f
  rw [Algebra.smul_def, Algebra.smul_def]
  simp only [RatFunc.algebraMap_eq_C]
  -- RatFunc.C c = algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c)
  simp only [← RatFunc.algebraMap_C c]
  -- h := algebraMap _ _ (Polynomial.C c)
  set h := algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c) with hh_def
  -- h.num = Polynomial.C c, h.denom = 1
  have hC_num : h.num = Polynomial.C c := RatFunc.num_algebraMap _
  have hC_denom : h.denom = 1 := RatFunc.denom_algebraMap _
  -- (Polynomial.C c).comp shift = Polynomial.C c
  have hC_comp : (Polynomial.C c).comp shift = Polynomial.C c := Polynomial.C_comp
  -- num_denom_mul: (h * f).num * (h.denom * f.denom) = h.num * f.num * (h * f).denom
  have hmul := RatFunc.num_denom_mul h f
  rw [hC_num, hC_denom, one_mul] at hmul
  -- Compose both sides with shift
  have hmul_comp := congr_arg (fun p => p.comp shift) hmul
  simp only [Polynomial.mul_comp] at hmul_comp
  rw [hC_comp] at hmul_comp
  -- hmul_comp : (h * f).num.comp shift * f.denom.comp shift =
  --             Polynomial.C c * f.num.comp shift * (h * f).denom.comp shift
  -- Show denominators are nonzero
  have hf_denom_comp_ne : f.denom.comp shift ≠ 0 := comp_shift_ne_zero α f.denom (RatFunc.monic_denom f)
  have hhf_denom_comp_ne : (h * f).denom.comp shift ≠ 0 :=
    comp_shift_ne_zero α (h * f).denom (RatFunc.monic_denom (h * f))
  have hf_denom_ne : (algebraMap (Polynomial Fq) (RatFunc Fq) (f.denom.comp shift)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hf_denom_comp_ne
  have hhf_denom_ne : (algebraMap (Polynomial Fq) (RatFunc Fq) ((h * f).denom.comp shift)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hhf_denom_comp_ne
  -- Goal: algebraMap _ _ ((h * f).num.comp shift) / algebraMap _ _ ((h * f).denom.comp shift) =
  --       h * (algebraMap _ _ (f.num.comp shift) / algebraMap _ _ (f.denom.comp shift))
  -- Expand h on RHS using num_div_denom
  conv_rhs => rw [← RatFunc.num_div_denom h, hC_num, hC_denom]
  -- Now: ... = (algebraMap _ _ (Polynomial.C c) / algebraMap _ _ 1) * (...)
  simp only [map_one, div_one]
  -- Now: ... = algebraMap _ _ (Polynomial.C c) * (...)
  rw [← hC_comp]
  -- ... = algebraMap _ _ ((Polynomial.C c).comp shift) * (...)
  rw [mul_div_assoc']
  rw [div_eq_div_iff hhf_denom_ne hf_denom_ne]
  simp only [← map_mul]
  congr 1
  -- Goal: (h * f).num.comp shift * f.denom.comp shift =
  --       (Polynomial.C c).comp shift * f.num.comp shift * (h * f).denom.comp shift
  rw [hC_comp]
  exact hmul_comp

/-- Translation of zero is zero. -/
@[simp]
theorem translateBy_zero (α : Fq) : translateBy α (0 : RatFunc Fq) = 0 := by
  simp only [translateBy, RatFunc.num_zero, RatFunc.denom_zero, Polynomial.zero_comp,
             Polynomial.one_comp, map_zero, zero_div]

/-- Translation of a polynomial gives a polynomial: the composition with X + C α.

For a polynomial p viewed as p/1 in RatFunc:
- num = p, denom = 1
- translateBy α p = (p.comp (X + C α)) / (1.comp (X + C α)) = (p.comp (X + C α)) / 1 = p.comp (X + C α)
-/
theorem translateBy_polynomial (α : Fq) (p : Polynomial Fq) :
    translateBy α (algebraMap (Polynomial Fq) (RatFunc Fq) p) =
    algebraMap (Polynomial Fq) (RatFunc Fq) (p.comp (Polynomial.X + Polynomial.C α)) := by
  simp only [translateBy]
  -- p as RatFunc has num = p, denom = 1
  have hnum : (algebraMap (Polynomial Fq) (RatFunc Fq) p).num = p := RatFunc.num_algebraMap p
  have hdenom : (algebraMap (Polynomial Fq) (RatFunc Fq) p).denom = 1 := RatFunc.denom_algebraMap p
  rw [hnum, hdenom]
  simp only [Polynomial.one_comp, map_one, div_one]

/-- Residue at a finite place α ∈ Fq, defined via translation to the origin.

This is the coefficient of (X - α)^{-1} in the Laurent expansion of f at α.
Unlike `residueAtLinear`, this handles all pole orders correctly and is
genuinely additive/linear.

Mathematical idea: shift coordinates so the pole at α becomes a pole at 0,
then extract the (-1) coefficient using HahnSeries.
-/
def residueAt (α : Fq) (f : RatFunc Fq) : Fq :=
  residueAtX (translateBy α f)

/-- Residue at α is additive. Follows from translation being additive
    and residueAtX being additive. -/
theorem residueAt_add (α : Fq) (f g : RatFunc Fq) :
    residueAt α (f + g) = residueAt α f + residueAt α g := by
  simp only [residueAt, translateBy_add, residueAtX_add]

/-- Residue at α respects scalar multiplication. -/
theorem residueAt_smul (α : Fq) (c : Fq) (f : RatFunc Fq) :
    residueAt α (c • f) = c * residueAt α f := by
  simp only [residueAt, translateBy_smul]
  rw [residueAtX_smul, smul_eq_mul]

/-- Residue at α of zero is zero. -/
@[simp]
theorem residueAt_zero' (α : Fq) : residueAt α (0 : RatFunc Fq) = 0 := by
  simp only [residueAt, translateBy_zero, residueAtX_zero]

/-- Polynomials have zero residue at all finite places.

A polynomial has no poles anywhere in Fq, so all residues are zero.
Proof: translateBy α (polynomial) = polynomial.comp (X + C α) is still a polynomial,
and residueAtX of a polynomial is 0.
-/
theorem residueAt_polynomial (α : Fq) (p : Polynomial Fq) :
    residueAt α (algebraMap (Polynomial Fq) (RatFunc Fq) p) = 0 := by
  simp only [residueAt]
  rw [translateBy_polynomial]
  exact residueAtX_polynomial (p.comp (Polynomial.X + Polynomial.C α))

/-- The residue at a finite place as a linear map.

This is the proper linear map for residues, handling all pole orders correctly.
-/
def residueAt_linearMap (α : Fq) : RatFunc Fq →ₗ[Fq] Fq where
  toFun := residueAt α
  map_add' := residueAt_add α
  map_smul' := residueAt_smul α

/-- Residue at 0 equals residueAtX (translation by 0 is identity). -/
theorem residueAt_zero_eq_residueAtX (f : RatFunc Fq) :
    residueAt (0 : Fq) f = residueAtX f := by
  simp only [residueAt, translateBy]
  simp only [Polynomial.C_0, add_zero, Polynomial.comp_X]
  rw [RatFunc.num_div_denom f]

/-- Link residueAt to residueAtLinear for simple poles.

For f = c • (X - α)⁻¹ with a simple pole at α, both definitions give c.
This bridges the computational formula with the abstract definition.
-/
theorem residueAt_eq_residueAtLinear_simple (α c : Fq) :
    residueAt α (c • (RatFunc.X - RatFunc.C α)⁻¹) = c := by
  simp only [residueAt]
  -- Use translateBy_smul to pull out the scalar
  rw [translateBy_smul]
  -- Now: residueAtX (c • translateBy α (X - C α)⁻¹) = c
  rw [residueAtX_smul, smul_eq_mul]
  -- Need: c * residueAtX (translateBy α (X - C α)⁻¹) = c
  -- Suffices to show: residueAtX (translateBy α (X - C α)⁻¹) = 1
  suffices h : residueAtX (translateBy α (RatFunc.X - RatFunc.C α)⁻¹) = 1 by
    rw [h, mul_one]
  -- Show translateBy α (X - C α)⁻¹ = X⁻¹
  -- translateBy α (X - C α)⁻¹ = ((X - C α)⁻¹.num.comp shift) / ((X - C α)⁻¹.denom.comp shift)
  simp only [translateBy]
  set shift := Polynomial.X + Polynomial.C α with hshift_def
  set f := (RatFunc.X - RatFunc.C α)⁻¹ with hf_def
  -- (X - C α)⁻¹ = 1 / (X - C α) = algebraMap 1 / algebraMap (X - C α)
  have hXa_ne : (Polynomial.X - Polynomial.C α) ≠ (0 : Polynomial Fq) := by
    intro h; have hdeg := congr_arg Polynomial.natDegree h; simp at hdeg
  have hf_eq : f = algebraMap (Polynomial Fq) (RatFunc Fq) 1 /
                   algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C α) := by
    simp only [hf_def, RatFunc.X, ← RatFunc.algebraMap_C α, ← map_sub]
    rw [map_one, one_div]
  -- num and denom of 1/(X - C α)
  -- leadingCoeff (X - C α) = 1, so the normalization factor is C 1⁻¹ = C 1 = 1
  have hlc : (Polynomial.X - Polynomial.C α).leadingCoeff = 1 := Polynomial.leadingCoeff_X_sub_C α
  have hf_num : f.num = 1 := by
    rw [hf_eq, RatFunc.num_div]
    simp only [gcd_one_left, EuclideanDomain.div_one, hlc, inv_one, Polynomial.C_1, mul_one]
  have hf_denom : f.denom = Polynomial.X - Polynomial.C α := by
    rw [hf_eq, RatFunc.denom_div (1 : Polynomial Fq) hXa_ne]
    simp only [gcd_one_left, EuclideanDomain.div_one, hlc, inv_one, Polynomial.C_1, one_mul]
  -- After composition:
  -- 1.comp shift = 1
  -- (X - C α).comp shift = X + C α - C α = X
  have h1_comp : (1 : Polynomial Fq).comp shift = 1 := Polynomial.one_comp
  have hXa_comp : (Polynomial.X - Polynomial.C α).comp shift = Polynomial.X := by
    simp only [hshift_def, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    ring
  -- So translateBy α f = 1 / X = X⁻¹
  rw [hf_num, hf_denom, h1_comp, hXa_comp]
  -- algebraMap 1 / algebraMap X = 1 / X = X⁻¹
  simp only [map_one, RatFunc.algebraMap_X, one_div]
  -- residueAtX X⁻¹ = 1
  exact residueAtX_inv_X

/-- The residue at β of c/(X - α) is 0 when β ≠ α.

This shows that simple poles at α don't contribute to residues at other places.
The proof uses translation: translateBy β moves the pole from α to α - β.
Since α ≠ β, we have α - β ≠ 0, so the translated function has no pole at origin.
-/
theorem residueAt_inv_X_sub_ne (α β c : Fq) (hne : α ≠ β) :
    residueAt β (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) = 0 := by
  simp only [residueAt]
  rw [translateBy_smul, residueAtX_smul, smul_eq_mul]
  suffices h : residueAtX (translateBy β ((RatFunc.X - RatFunc.C α)⁻¹)) = 0 by rw [h, mul_zero]
  -- translateBy β ((X - C α)⁻¹) = (X - C(α - β))⁻¹
  simp only [translateBy]
  set shift := Polynomial.X + Polynomial.C β with hshift_def
  set f := (RatFunc.X - RatFunc.C α)⁻¹ with hf_def
  have hXa_ne : (Polynomial.X - Polynomial.C α) ≠ (0 : Polynomial Fq) := by
    intro h; have hdeg := congr_arg Polynomial.natDegree h; simp at hdeg
  have hlc : (Polynomial.X - Polynomial.C α).leadingCoeff = 1 := Polynomial.leadingCoeff_X_sub_C α
  have hf_num : f.num = 1 := by
    rw [hf_def, RatFunc.X, ← RatFunc.algebraMap_C α, ← map_sub]
    rw [show (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C α))⁻¹ =
        algebraMap (Polynomial Fq) (RatFunc Fq) 1 /
        algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C α) by
      rw [map_one, one_div]]
    rw [RatFunc.num_div]
    simp only [gcd_one_left, EuclideanDomain.div_one, hlc, inv_one, Polynomial.C_1, mul_one]
  have hf_denom : f.denom = Polynomial.X - Polynomial.C α := by
    rw [hf_def, RatFunc.X, ← RatFunc.algebraMap_C α, ← map_sub]
    rw [show (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C α))⁻¹ =
        algebraMap (Polynomial Fq) (RatFunc Fq) 1 /
        algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C α) by
      rw [map_one, one_div]]
    rw [RatFunc.denom_div (1 : Polynomial Fq) hXa_ne]
    simp only [gcd_one_left, EuclideanDomain.div_one, hlc, inv_one, Polynomial.C_1, one_mul]
  -- After composition:
  -- 1.comp shift = 1
  -- (X - C α).comp shift = X + C β - C α = X - C(α - β)
  have h1_comp : (1 : Polynomial Fq).comp shift = 1 := Polynomial.one_comp
  have hXa_comp : (Polynomial.X - Polynomial.C α).comp shift = Polynomial.X - Polynomial.C (α - β) := by
    simp only [hshift_def, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, Polynomial.C_sub]
    ring
  rw [hf_num, hf_denom, h1_comp, hXa_comp]
  -- translateBy β f = 1 / (X - C(α - β)) = (X - C(α - β))⁻¹
  simp only [map_one, one_div]
  rw [show algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C (α - β)) =
          RatFunc.X - RatFunc.C (α - β) by
    rw [RatFunc.X, ← RatFunc.algebraMap_C, map_sub]]
  -- α ≠ β implies α - β ≠ 0
  have hab_ne : α - β ≠ 0 := sub_ne_zero.mpr hne
  -- residueAtX of (X - C(α - β))⁻¹ = 0 since pole is at α - β ≠ 0
  exact residueAtX_inv_X_sub_ne (α - β) hab_ne

end RiemannRochV2.Residue
