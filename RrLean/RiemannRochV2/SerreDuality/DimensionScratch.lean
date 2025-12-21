import RrLean.RiemannRochV2.SerreDuality.RatFuncFullRR
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Scratch file for dimension formula development

Goal: Prove ℓ(D) = deg(D) + 1 for effective D with linear place support on P¹.

For P¹ with g = 0:
- K has degree -2
- When deg(D) ≥ 0, deg(K-D) = -2 - deg(D) < 0
- So ℓ(K-D) = 0 (already proved: `ell_canonical_sub_zero`)
- Riemann-Roch becomes: ℓ(D) = deg(D) + 1
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Polynomial RatFunc
open scoped Classical

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-! ## Dimension Formula via Gap Bound

Strategy: Prove by induction on deg(D) using the gap bound.
- Base: ℓ(0) = 1 (proved in RatFuncFullRR)
- Step: ℓ(D + [v]) = ℓ(D) + 1 for linear v

For the step, we need:
1. ℓ(D + [v]) ≤ ℓ(D) + 1 (gap bound, need to prove for projective case)
2. ℓ(D + [v]) ≥ ℓ(D) + 1 (construct explicit element in L(D+[v]) \ L(D))
-/

/-! ## Upper bound: Gap ≤ 1 for projective space -/

/-- L_proj(D) ⊆ L_proj(D + [v]) for any linear place v. -/
lemma RRSpace_ratfunc_projective_mono (D : DivisorV2 (Polynomial Fq)) (α : Fq) :
    RRSpace_ratfunc_projective D ≤
    RRSpace_ratfunc_projective (D + DivisorV2.single (linearPlace α) 1) := by
  intro f hf
  rcases hf with ⟨hval, hinfty⟩
  constructor
  · -- Valuation condition for D + [v]
    rcases hval with hzero | hval'
    · left; exact hzero
    right
    intro w
    by_cases hw : w = linearPlace α
    · subst hw
      simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_apply, if_pos rfl]
      calc (linearPlace α).valuation (RatFunc Fq) f
          ≤ WithZero.exp (D (linearPlace α)) := hval' (linearPlace α)
        _ ≤ WithZero.exp (D (linearPlace α) + 1) := by
            apply WithZero.exp_le_exp.mpr; omega
    · simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_apply, hw,
                 if_neg (Ne.symm hw), add_zero]
      exact hval' w
  · exact hinfty

/-! ## Residue field isomorphism for linear places

For linearPlace α, the residue field κ(v) = Fq[X]/(X-α) ≅ Fq via evaluation at α.
This gives dim_Fq(κ(v)) = 1, which is key for the gap bound. -/

/-- The residue field at a linear place is isomorphic to Fq.
This uses the fact that Fq[X]/(X-α) ≅ Fq via evaluation at α. -/
noncomputable def linearPlace_residue_equiv (α : Fq) :
    residueFieldAtPrime (Polynomial Fq) (linearPlace α) ≃+* Fq := by
  -- κ(linearPlace α) = Polynomial Fq / (linearPlace α).asIdeal
  -- (linearPlace α).asIdeal = Ideal.span {X - C α}
  -- So κ(v) = Fq[X]/(X - C α) ≅ Fq via evaluation at α
  have h1 : (linearPlace (Fq := Fq) α).asIdeal = Ideal.span {Polynomial.X - Polynomial.C α} := rfl
  -- The residue field at prime is the localization quotient, but for a polynomial ring
  -- over a field, this is just the polynomial quotient
  have hprime : (linearPlace (Fq := Fq) α).asIdeal.IsPrime := (linearPlace α).isPrime
  -- Use the evaluation isomorphism
  exact (Ideal.quotientEquivAlgOfEq (Polynomial Fq) (Polynomial Fq) h1.symm).symm.toRingEquiv.trans
    ((Ideal.quotientSpanEquivPolynomialDenomIso (Polynomial.X_sub_C_ne_zero α)
      (Polynomial.monic_X_sub_C α)).symm.trans (Polynomial.aeval α).toRingEquiv)

/-- The residue field at a linear place has dimension 1 over Fq. -/
lemma linearPlace_residue_finrank (α : Fq) :
    Module.finrank Fq (residueFieldAtPrime (Polynomial Fq) (linearPlace α)) = 1 := by
  -- Use the isomorphism to Fq
  have e := linearPlace_residue_equiv Fq α
  have h : Module.finrank Fq Fq = 1 := Module.finrank_self Fq
  rw [← h]
  -- Need a linear equiv, not just ring equiv
  -- The residue field has an Fq-algebra structure via Polynomial Fq → κ(v)
  -- and Fq → Polynomial Fq (constants)
  haveI : Algebra Fq (residueFieldAtPrime (Polynomial Fq) (linearPlace α)) := by
    exact Ideal.Quotient.algebra Fq
  -- The ring equiv e : κ(v) ≃+* Fq respects the Fq-action
  have hcompat : ∀ (c : Fq) (x : residueFieldAtPrime (Polynomial Fq) (linearPlace α)),
      e (c • x) = c • e x := by
    intro c x
    -- c • x = algebraMap Fq κ(v) c * x
    simp only [Algebra.smul_def]
    rw [map_mul]
    -- Need to show e(algebraMap Fq κ(v) c) = c
    congr 1
    -- algebraMap Fq κ(v) c = image of C c under quotient map
    simp only [algebraMap_def, Ideal.Quotient.algebraMap_eq]
    -- e sends [C c] to aeval α (C c) = c
    simp only [linearPlace_residue_equiv, RingEquiv.trans_apply, AlgEquiv.toRingEquiv_eq_coe,
               RingEquiv.coe_toRingEquiv, AlgEquiv.symm_apply_apply]
    rfl
  let e_lin : residueFieldAtPrime (Polynomial Fq) (linearPlace α) ≃ₗ[Fq] Fq := {
    e with
    map_smul' := hcompat
  }
  exact LinearEquiv.finrank_eq e_lin

/-- Gap bound for projective RRSpace: ℓ(D + [v]) ≤ ℓ(D) + 1.

This uses the evaluation map which sends f to its "residue" at v.
The kernel equals L(D), so the quotient has dimension at most 1 (dim κ(v) = 1). -/
theorem ell_ratfunc_projective_gap_le (D : DivisorV2 (Polynomial Fq)) (α : Fq) :
    ell_ratfunc_projective (D + DivisorV2.single (linearPlace α) 1) ≤
    ell_ratfunc_projective D + 1 := by
  -- The inclusion L_proj(D) → L_proj(D+v)
  let v := linearPlace (Fq := Fq) α
  have hle := divisor_le_add_single D v
  have hincl : RRSpace_ratfunc_projective D ≤
      RRSpace_ratfunc_projective (D + DivisorV2.single v 1) :=
    RRSpace_ratfunc_projective_mono Fq D α

  -- LD = comap of L_proj(D) in L_proj(D+v)
  let LD := (RRSpace_ratfunc_projective D).comap
      (RRSpace_ratfunc_projective (D + DivisorV2.single v 1)).subtype

  -- The affine evaluation map φ : L_affine(D+v) → κ(v)
  let φ := evaluationMapAt_complete (R := Polynomial Fq) (K := RatFunc Fq) v D

  -- Construct the Fq-linear evaluation map on projective space
  -- First, embed L_proj(D+v) → L_affine(D+v)
  have h_proj_le_affine : RRSpace_ratfunc_projective (D + DivisorV2.single v 1) ≤
      RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1) := by
    intro f hf
    exact hf.1

  -- Define ψ : L_proj(D+v) →ₗ[Fq] κ(v)
  let ψ : ↥(RRSpace_ratfunc_projective (D + DivisorV2.single v 1)) →ₗ[Fq]
      residueFieldAtPrime (Polynomial Fq) v where
    toFun := fun x => φ ⟨x.val, h_proj_le_affine x.property⟩
    map_add' := fun x y => by
      show φ ⟨(x + y).val, _⟩ = φ ⟨x.val, _⟩ + φ ⟨y.val, _⟩
      have := φ.map_add ⟨x.val, h_proj_le_affine x.property⟩ ⟨y.val, h_proj_le_affine y.property⟩
      convert this using 1
      · congr 1; rfl
      · rfl
    map_smul' := fun c x => by
      -- c is in Fq, need to use scalar tower Fq → Polynomial Fq → RatFunc Fq
      show φ ⟨(c • x).val, _⟩ = c • φ ⟨x.val, _⟩
      -- c • x in Fq-module = algebraMap Fq (Polynomial Fq) c • x in Polynomial Fq-module
      have h1 : (c • x).val = (algebraMap Fq (Polynomial Fq) c) • x.val :=
        (IsScalarTower.algebraMap_smul (Polynomial Fq) c x.val).symm
      have hmem : (algebraMap Fq (Polynomial Fq) c) • x.val ∈
          RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1) :=
        Submodule.smul_mem _ _ (h_proj_le_affine x.property)
      -- φ is (Polynomial Fq)-linear
      have h2 : φ ⟨(algebraMap Fq (Polynomial Fq) c) • x.val, hmem⟩ =
          (algebraMap Fq (Polynomial Fq) c) • φ ⟨x.val, h_proj_le_affine x.property⟩ := by
        convert φ.map_smul (algebraMap Fq (Polynomial Fq) c) ⟨x.val, h_proj_le_affine x.property⟩
      -- algebraMap c • y = c • y in κ(v) via scalar tower
      have h3 : (algebraMap Fq (Polynomial Fq) c) • φ ⟨x.val, h_proj_le_affine x.property⟩ =
          c • φ ⟨x.val, h_proj_le_affine x.property⟩ :=
        IsScalarTower.algebraMap_smul (Polynomial Fq) c _
      calc φ ⟨(c • x).val, (c • x).property.1⟩
          = φ ⟨(algebraMap Fq (Polynomial Fq) c) • x.val, hmem⟩ := by simp only [h1]
        _ = (algebraMap Fq (Polynomial Fq) c) • φ ⟨x.val, h_proj_le_affine x.property⟩ := h2
        _ = c • φ ⟨x.val, h_proj_le_affine x.property⟩ := h3

  -- Show LD ⊆ ker(ψ)
  have h_LD_le_ker : LD ≤ LinearMap.ker ψ := by
    intro x hx
    rw [LinearMap.mem_ker]
    rw [Submodule.mem_comap] at hx
    -- hx : x.val ∈ L_proj(D)
    let y : RRModuleV2_real (Polynomial Fq) (RatFunc Fq) D := ⟨x.val, hx.1⟩
    -- φ(inclusion(y)) = 0 by LD_element_maps_to_zero from KernelProof
    have h_affine_mem : x.val ∈ RRModuleV2_real (Polynomial Fq) (RatFunc Fq) D := hx.1
    have h_in_affine_Dv : x.val ∈ RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1) :=
      RRModuleV2_mono_inclusion (Polynomial Fq) (RatFunc Fq) hle h_affine_mem
    let y_affine : RRModuleV2_real (Polynomial Fq) (RatFunc Fq) D := ⟨x.val, h_affine_mem⟩
    have hinc : (⟨x.val, h_in_affine_Dv⟩ : RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1)) =
        Submodule.inclusion (RRModuleV2_mono_inclusion (Polynomial Fq) (RatFunc Fq) hle) y_affine := rfl
    show ψ x = 0
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
    -- Need to match with the affine evaluation
    have hx_eq : (⟨x.val, h_proj_le_affine x.property⟩ :
        RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1)) =
        ⟨x.val, h_in_affine_Dv⟩ := rfl
    rw [hx_eq, hinc]
    exact LD_element_maps_to_zero v D y_affine

  -- Show ker(ψ) ⊆ LD
  have h_ker_le_LD : LinearMap.ker ψ ≤ LD := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    show x ∈ LD
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk] at hx
    -- hx : φ ⟨x.val, _⟩ = 0
    have h_in_ker : (⟨x.val, h_proj_le_affine x.property⟩ :
        RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1)) ∈
        LinearMap.ker φ := hx
    rw [kernel_evaluationMapAt_complete_proof, LinearMap.mem_range] at h_in_ker
    obtain ⟨y, hy⟩ := h_in_ker
    -- y ∈ L_affine(D), and inclusion(y) = ⟨x.val, _⟩, so y.val = x.val
    rw [Submodule.mem_comap, Submodule.coe_subtype]
    -- Goal: x.val ∈ L_proj(D)
    have hval : y.val = x.val := congrArg Subtype.val hy
    -- x.val = y.val ∈ L_affine(D)
    have h_affine : x.val ∈ RRModuleV2_real (Polynomial Fq) (RatFunc Fq) D := by
      rw [← hval]; exact y.property
    -- x has noPoleAtInfinity (since x ∈ L_proj(D+v))
    have h_infty : x.val = 0 ∨ noPoleAtInfinity x.val := x.property.2
    -- Combine to get x.val ∈ L_proj(D)
    exact ⟨h_affine, h_infty⟩

  -- LD = ker(ψ)
  have h_eq_ker : LD = LinearMap.ker ψ := le_antisymm h_LD_le_ker h_ker_le_LD

  -- The quotient L_proj(D+v)/LD embeds into κ(v) which has dim 1
  have h_quot_le : Module.finrank Fq
      (↥(RRSpace_ratfunc_projective (D + DivisorV2.single v 1)) ⧸ LD) ≤ 1 := by
    -- κ(v) is finite-dimensional over Fq
    haveI : Module.Finite Fq (residueFieldAtPrime (Polynomial Fq) v) := by
      rw [Module.finite_def]
      have e := linearPlace_residue_equiv Fq α
      have hcompat : ∀ (c : Fq) (x : residueFieldAtPrime (Polynomial Fq) (linearPlace α)),
          e (c • x) = c • e x := by
        intro c x
        simp only [Algebra.smul_def, map_mul]
        congr 1
        simp only [algebraMap_def, Ideal.Quotient.algebraMap_eq]
        simp only [linearPlace_residue_equiv, RingEquiv.trans_apply, AlgEquiv.toRingEquiv_eq_coe,
                   RingEquiv.coe_toRingEquiv, AlgEquiv.symm_apply_apply]
        rfl
      let e_lin : residueFieldAtPrime (Polynomial Fq) v ≃ₗ[Fq] Fq := {
        e with
        map_smul' := hcompat
      }
      have hfin : (⊤ : Submodule Fq Fq).FG := ⟨{1}, by simp⟩
      exact e_lin.symm.fg_iff.mpr hfin

    -- The descended map: quotient → κ(v) is injective
    let desc := Submodule.liftQ LD ψ h_LD_le_ker
    have h_desc_inj : Function.Injective desc := by
      rw [← LinearMap.ker_eq_bot]
      have hker := Submodule.ker_liftQ LD ψ h_LD_le_ker
      rw [hker, h_eq_ker, Submodule.mkQ_map_self]

    -- finrank of domain ≤ finrank of codomain when injection exists
    calc Module.finrank Fq (↥(RRSpace_ratfunc_projective (D + DivisorV2.single v 1)) ⧸ LD)
        ≤ Module.finrank Fq (residueFieldAtPrime (Polynomial Fq) v) :=
          LinearMap.finrank_le_finrank_of_injective h_desc_inj
      _ = 1 := linearPlace_residue_finrank Fq α

  -- LD equals range(inclusion) since L_proj(D) ⊆ L_proj(D+v)
  have h_LD_eq : Module.finrank Fq LD = ell_ratfunc_projective D := by
    unfold ell_ratfunc_projective LD
    have h_eq : (RRSpace_ratfunc_projective D).comap
        (RRSpace_ratfunc_projective (D + DivisorV2.single v 1)).subtype =
        LinearMap.range (Submodule.inclusion hincl) := by
      apply le_antisymm
      · intro x hx
        rw [Submodule.mem_comap] at hx
        rw [LinearMap.mem_range]
        exact ⟨⟨x.val, hx⟩, rfl⟩
      · intro x hx
        rw [LinearMap.mem_range] at hx
        obtain ⟨y, hy⟩ := hx
        rw [Submodule.mem_comap]
        rw [← hy]; exact y.2
    rw [h_eq]
    exact LinearMap.finrank_range_of_inj (Submodule.inclusion_injective hincl)

  -- Use finrank(quotient) + finrank(LD) = finrank(L_proj(D+v))
  have h_add := Submodule.finrank_quotient_add_finrank LD
  unfold ell_ratfunc_projective
  have h_eq : Module.finrank Fq ↥(RRSpace_ratfunc_projective (D + DivisorV2.single v 1)) =
      Module.finrank Fq LD +
      Module.finrank Fq (↥(RRSpace_ratfunc_projective (D + DivisorV2.single v 1)) ⧸ LD) := by
    rw [← h_add, add_comm]
  rw [h_eq, h_LD_eq]
  omega

/-! ## Lower bound: Explicit elements -/

/-- The valuation of (X-α) at linearPlace α is exp(-1).
Uses intValuation_linearPlace_eq_exp_neg_rootMultiplicity and Polynomial.rootMultiplicity_X_sub_C. -/
lemma valuation_X_sub_at_self (α : Fq) :
    (linearPlace α).valuation (RatFunc Fq) (RatFunc.X - RatFunc.C α) = WithZero.exp (-1 : ℤ) := by
  have heq : RatFunc.X - RatFunc.C α = algebraMap (Polynomial Fq) (RatFunc Fq)
      (Polynomial.X - Polynomial.C α) := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [heq, HeightOneSpectrum.valuation_of_algebraMap]
  rw [intValuation_linearPlace_eq_exp_neg_rootMultiplicity α _ (Polynomial.X_sub_C_ne_zero α)]
  -- rootMultiplicity_X_sub_C : (X - C a).rootMultiplicity a = 1
  simp only [Polynomial.rootMultiplicity_X_sub_C]
  rfl

/-- The valuation of (X-α)⁻¹^k at linearPlace α is exp(k).
Uses valuation_X_sub_at_self, WithZero.exp_inv_eq_neg_int, and WithZero.exp_nsmul. -/
lemma valuation_inv_X_sub_pow_at_self (α : Fq) (k : ℕ) :
    (linearPlace α).valuation (RatFunc Fq) ((RatFunc.X - RatFunc.C α)⁻¹ ^ k) =
    WithZero.exp (k : ℤ) := by
  rw [Valuation.map_pow, Valuation.map_inv, valuation_X_sub_at_self]
  rw [WithZero.exp_inv_eq_neg_int, neg_neg]
  rw [← WithZero.exp_nsmul]
  simp only [nsmul_eq_mul, mul_one]

/-- At a place v ≠ linearPlace α, (X-α) has valuation 1.
Key: if (X-α) ∈ v.asIdeal then v = linearPlace α by maximality.
Proof: span{X-α} is maximal (irreducible in PID), contained in v.asIdeal, so they're equal. -/
lemma valuation_X_sub_at_other (α : Fq) (v : HeightOneSpectrum (Polynomial Fq))
    (hv : v ≠ linearPlace α) :
    v.valuation (RatFunc Fq) (RatFunc.X - RatFunc.C α) = 1 := by
  have heq : RatFunc.X - RatFunc.C α = algebraMap (Polynomial Fq) (RatFunc Fq)
      (Polynomial.X - Polynomial.C α) := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [heq, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem; apply hv
  -- span{X-α} is maximal (X-α is irreducible in PID Fq[X])
  have hirr : Irreducible (Polynomial.X - Polynomial.C α) := Polynomial.irreducible_X_sub_C α
  have hmax_span : (Ideal.span {Polynomial.X - Polynomial.C α}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hirr
  -- span{X-α} ≤ v.asIdeal
  have hle : Ideal.span {Polynomial.X - Polynomial.C α} ≤ v.asIdeal := by
    rw [Ideal.span_le]; intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact hmem
  -- v.asIdeal ≠ ⊤ (since v is a HeightOneSpectrum element)
  have hv_ne_top : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
  -- By maximality of span{X-α}, we have span{X-α} = v.asIdeal
  have heq' : Ideal.span {Polynomial.X - Polynomial.C α} = v.asIdeal :=
    hmax_span.eq_of_le hv_ne_top hle
  exact HeightOneSpectrum.ext heq'.symm

/-- 1/(X-α)^k satisfies the valuation condition for k·[linearPlace α]. -/
lemma inv_X_sub_C_pow_satisfies_valuation (α : Fq) (k : ℕ) (hk : k ≠ 0) :
    satisfiesValuationCondition (Polynomial Fq) (RatFunc Fq)
      ((k : ℤ) • DivisorV2.single (linearPlace α) 1)
      ((RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ k) := by
  right
  intro v
  by_cases hv : v = linearPlace α
  · -- At linearPlace α: val = exp(k) ≤ exp(k)
    subst hv
    simp only [Finsupp.smul_apply, smul_eq_mul, DivisorV2.single, Finsupp.single_apply,
               ↓reduceIte, mul_one]
    rw [valuation_inv_X_sub_pow_at_self]
  · -- At other places: val = 1 ≤ 1 = exp(0)
    simp only [Finsupp.smul_apply, smul_eq_mul, DivisorV2.single, Finsupp.single_apply]
    have hne : linearPlace (Fq := Fq) α ≠ v := fun h => hv h.symm
    simp only [hne, ↓reduceIte, mul_zero, WithZero.exp_zero]
    rw [Valuation.map_pow, Valuation.map_inv, valuation_X_sub_at_other Fq α v hv]
    simp only [inv_one, one_pow, le_refl]

/-! ## intDegree-based lemmas for noPoleAtInfinity

The direct approach using num/denom is blocked by typeclass issues with gcd.
Instead, we use intDegree which provides clean lemmas without typeclass mismatches. -/

/-- X - C α is nonzero in RatFunc. -/
lemma RatFunc_X_sub_C_ne_zero (α : Fq) : (RatFunc.X : RatFunc Fq) - RatFunc.C α ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have h1 : (RatFunc.X : RatFunc Fq).intDegree = 1 := RatFunc.intDegree_X
  have h2 : (RatFunc.C α : RatFunc Fq).intDegree = 0 := RatFunc.intDegree_C α
  rw [h, h2] at h1
  exact zero_ne_one h1

/-- The intDegree of (X - C α)⁻¹ ^ k is -k. -/
lemma intDegree_inv_X_sub_C_pow (α : Fq) (k : ℕ) :
    ((RatFunc.X - RatFunc.C α : RatFunc Fq)⁻¹ ^ k).intDegree = -(k : ℤ) := by
  -- intDegree(X - C α) = 1
  have hXα_deg : (RatFunc.X - RatFunc.C α : RatFunc Fq).intDegree = 1 := by
    have heq : RatFunc.X - RatFunc.C α = algebraMap (Polynomial Fq) (RatFunc Fq)
        (Polynomial.X - Polynomial.C α) := by
      simp [RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    rw [heq, RatFunc.intDegree_polynomial, Polynomial.natDegree_X_sub_C]
    rfl
  -- intDegree((X - C α)⁻¹) = -1
  have hinv_deg : (RatFunc.X - RatFunc.C α : RatFunc Fq)⁻¹.intDegree = -1 := by
    rw [RatFunc.intDegree_inv, hXα_deg]
  -- Helper: (X - C α)⁻¹ ≠ 0
  have hinv_ne : (RatFunc.X - RatFunc.C α : RatFunc Fq)⁻¹ ≠ 0 :=
    inv_ne_zero (RatFunc_X_sub_C_ne_zero Fq α)
  -- Induction on k
  induction k with
  | zero => simp [RatFunc.intDegree_one]
  | succ m ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero m hinv_ne) hinv_ne, ih, hinv_deg]
    omega

/-- noPoleAtInfinity is equivalent to intDegree ≤ 0. -/
lemma noPoleAtInfinity_iff_intDegree_le_zero (f : RatFunc Fq) :
    noPoleAtInfinity f ↔ f.intDegree ≤ 0 := by
  unfold noPoleAtInfinity
  simp only [RatFunc.intDegree, sub_nonpos, Int.ofNat_le]

/-- 1/(X-α)^k has no pole at infinity for any k ≥ 0.
Note: The proof uses intDegree and works for k = 0 too (when the function is 1). -/
lemma inv_X_sub_C_pow_noPoleAtInfinity (α : Fq) (k : ℕ) :
    noPoleAtInfinity ((RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ k) := by
  rw [noPoleAtInfinity_iff_intDegree_le_zero, intDegree_inv_X_sub_C_pow]
  omega

/-- 1/(X-α)^k is in L_proj(k·[linearPlace α]). -/
lemma inv_X_sub_C_pow_mem_projective (α : Fq) (k : ℕ) :
    (RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ k ∈
    RRSpace_ratfunc_projective ((k : ℤ) • DivisorV2.single (linearPlace α) 1) := by
  by_cases hk : k = 0
  · -- k = 0: 1 ∈ L(0)
    subst hk
    simp only [pow_zero, Nat.cast_zero, zero_smul]
    have h1 : (1 : RatFunc Fq) = algebraMap Fq (RatFunc Fq) 1 := by simp
    rw [h1]
    exact constant_mem_projective_zero (1 : Fq)
  · constructor
    · exact inv_X_sub_C_pow_satisfies_valuation Fq α k hk
    · right; exact inv_X_sub_C_pow_noPoleAtInfinity Fq α k

/-- 1/(X-α)^k is NOT in L_proj((k-1)·[linearPlace α]) for k ≥ 1.

This shows the gap is exactly 1, not just ≤ 1. -/
lemma inv_X_sub_C_pow_not_mem_projective_smaller (α : Fq) (k : ℕ) (hk : 0 < k) :
    (RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ k ∉
    RRSpace_ratfunc_projective (((k : ℤ) - 1) • DivisorV2.single (linearPlace α) 1) := by
  intro ⟨hval, _⟩
  -- f = (X-α)⁻¹^k is nonzero
  have hf_ne : (RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ k ≠ 0 :=
    pow_ne_zero k (inv_ne_zero (RatFunc_X_sub_C_ne_zero Fq α))
  -- The valuation condition must hold for all v
  rcases hval with hzero | hval_all
  · exact hf_ne hzero
  -- At linearPlace α, the valuation is exp(k)
  have hval_at_α := hval_all (linearPlace α)
  rw [valuation_inv_X_sub_pow_at_self] at hval_at_α
  -- But D(linearPlace α) = k - 1
  simp only [Finsupp.smul_apply, smul_eq_mul, DivisorV2.single, Finsupp.single_apply,
             ↓reduceIte, mul_one] at hval_at_α
  -- So we need exp(k) ≤ exp(k-1), which is false for k ≥ 1
  have hcontra : ¬(WithZero.exp (k : ℤ) ≤ WithZero.exp ((k : ℤ) - 1)) := by
    rw [not_le]
    apply WithZero.exp_lt_exp.mpr
    omega
  exact hcontra hval_at_α

/-! ## Dimension formula for single-point divisors -/

/-- For D = n·[linearPlace α] with n ≥ 0, ℓ(D) = n + 1.

The proof uses the gap bound for the upper bound and constructs explicit
elements for the lower bound, avoiding circular FiniteDimensional issues. -/
theorem ell_ratfunc_projective_single_linear (α : Fq) (n : ℕ) :
    ell_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1) = n + 1 := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_smul, zero_add]
    exact ell_ratfunc_projective_zero_eq_one Fq
  | succ m ih =>
    -- Divisor decomposition
    have h_eq : ((m + 1 : ℕ) : ℤ) • DivisorV2.single (linearPlace (Fq := Fq) α) 1 =
        (m : ℤ) • DivisorV2.single (linearPlace α) 1 + DivisorV2.single (linearPlace α) 1 := by
      simp only [Nat.cast_succ, add_smul, one_smul]
    rw [h_eq]

    -- Upper bound from gap lemma: ℓ(m·[v] + [v]) ≤ ℓ(m·[v]) + 1 = m + 2
    have h_le := ell_ratfunc_projective_gap_le Fq ((m : ℤ) • DivisorV2.single (linearPlace α) 1) α
    rw [ih] at h_le

    -- Lower bound: ℓ((m+1)·[v]) ≥ m + 2
    -- Key: L(m·[v]) is a proper subspace of L((m+1)·[v]) because
    -- 1/(X-α)^(m+1) ∈ L((m+1)·[v]) \ L(m·[v])
    -- Since ℓ(m·[v]) = m + 1 (by IH) and L(m·[v]) ⊊ L((m+1)·[v]),
    -- we have ℓ((m+1)·[v]) ≥ m + 2
    have h_ge : ell_ratfunc_projective
        ((m : ℤ) • DivisorV2.single (linearPlace α) 1 + DivisorV2.single (linearPlace α) 1) ≥ m + 2 := by
      -- Rewrite divisor as (m+1)·[v]
      have hdiv_eq : (m : ℤ) • DivisorV2.single (linearPlace (Fq := Fq) α) 1 +
          DivisorV2.single (linearPlace α) 1 =
          ((m + 1 : ℕ) : ℤ) • DivisorV2.single (linearPlace α) 1 := by
        simp only [Nat.cast_succ, add_smul, one_smul]
      rw [hdiv_eq]

      -- 1/(X-α)^(m+1) witnesses strict inclusion
      have h_in := inv_X_sub_C_pow_mem_projective Fq α (m + 1)
      have h_not_in := inv_X_sub_C_pow_not_mem_projective_smaller Fq α (m + 1) (Nat.succ_pos m)
      simp only [Nat.cast_succ, add_sub_cancel_right] at h_not_in

      -- L(m·[v]) ⊆ L((m+1)·[v])
      have h_mono' : RRSpace_ratfunc_projective ((m : ℤ) • DivisorV2.single (linearPlace α) 1) ≤
          RRSpace_ratfunc_projective (((m + 1 : ℕ) : ℤ) • DivisorV2.single (linearPlace α) 1) := by
        have h_mono := RRSpace_ratfunc_projective_mono Fq
            ((m : ℤ) • DivisorV2.single (linearPlace α) 1) α
        convert h_mono using 1
        simp only [Nat.cast_succ, add_smul, one_smul]

      -- The inclusion is strict
      have h_ne : RRSpace_ratfunc_projective ((m : ℤ) • DivisorV2.single (linearPlace α) 1) ≠
          RRSpace_ratfunc_projective (((m + 1 : ℕ) : ℤ) • DivisorV2.single (linearPlace α) 1) := by
        intro heq
        apply h_not_in
        rw [heq]
        exact h_in

      -- Upper bound gives finite dimensionality
      have h_upper : ell_ratfunc_projective (((m + 1 : ℕ) : ℤ) • DivisorV2.single (linearPlace α) 1) ≤ m + 2 := by
        have h := ell_ratfunc_projective_gap_le Fq ((m : ℤ) • DivisorV2.single (linearPlace α) 1) α
        calc ell_ratfunc_projective (((m + 1 : ℕ) : ℤ) • DivisorV2.single (linearPlace α) 1)
            = ell_ratfunc_projective ((m : ℤ) • DivisorV2.single (linearPlace α) 1 +
                DivisorV2.single (linearPlace α) 1) := by rw [hdiv_eq]
          _ ≤ _ := h
          _ = m + 2 := by rw [ih]; ring

      -- Establish Module.Finite (= FiniteDimensional for fields) from bounded finrank
      haveI hfin : Module.Finite Fq
          ↥(RRSpace_ratfunc_projective (((m + 1 : ℕ) : ℤ) • DivisorV2.single (linearPlace α) 1)) := by
        -- L((m+1)·[v]) contains the nonzero element 1/(X-α)^(m+1), so finrank > 0
        have hne : (RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ (m + 1) ≠ 0 :=
          pow_ne_zero (m + 1) (inv_ne_zero (RatFunc_X_sub_C_ne_zero Fq α))
        have hpos : 0 < ell_ratfunc_projective (((m + 1 : ℕ) : ℤ) • DivisorV2.single (linearPlace α) 1) := by
          rw [Module.finrank_pos_iff]
          exact ⟨⟨_, h_in⟩, fun heq => hne (congrArg Subtype.val heq)⟩
        exact Module.finite_of_finrank_pos hpos

      -- Strict inclusion of submodules with finite upper bound implies finrank increases
      unfold ell_ratfunc_projective

      -- We need to show finrank ≥ m + 2
      -- Proof by contradiction: if finrank(L(m+1)) < m + 2, then finrank(L(m+1)) ≤ m + 1 = finrank(L(m))
      -- Combined with L(m) ≤ L(m+1) and equal finrank, we get L(m) = L(m+1), contradiction
      by_contra h_lt
      push_neg at h_lt
      have h_le' : Module.finrank Fq ↥(RRSpace_ratfunc_projective
          (((m + 1 : ℕ) : ℤ) • DivisorV2.single (linearPlace α) 1)) ≤ m + 1 := Nat.lt_succ_iff.mp h_lt
      have h_eq_m : Module.finrank Fq ↥(RRSpace_ratfunc_projective
          ((m : ℤ) • DivisorV2.single (linearPlace α) 1)) = m + 1 := ih
      have h_finrank_eq : Module.finrank Fq ↥(RRSpace_ratfunc_projective
          ((m : ℤ) • DivisorV2.single (linearPlace α) 1)) =
          Module.finrank Fq ↥(RRSpace_ratfunc_projective
          (((m + 1 : ℕ) : ℤ) • DivisorV2.single (linearPlace α) 1)) := by
        have h1 := Submodule.finrank_mono h_mono'
        omega
      have h_eq_submodule := Submodule.eq_of_le_of_finrank_eq h_mono' h_finrank_eq
      exact h_ne h_eq_submodule

    omega

/-! ## General dimension formula -/

/-- For effective D with linear support and deg(D) ≥ 0, ℓ(D) = deg(D) + 1. -/
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective D = D.deg.toNat + 1 := by
  -- Proof by induction on deg(D)
  -- Base case: deg(D) = 0 means D = 0 (since D is effective)
  -- Inductive case: D = D' + [v] for some linear v
  sorry

end RiemannRochV2
