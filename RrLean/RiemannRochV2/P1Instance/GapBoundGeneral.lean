import RrLean.RiemannRochV2.P1Instance.PlaceDegree
import RrLean.RiemannRochV2.SerreDuality.P1Specific.DimensionCore
import RrLean.RiemannRochV2.Dimension.KernelProof

/-!
# Generalized Gap Bound for Arbitrary Places

This module extends the gap bound from linear places to arbitrary places.

## Main Results

* `RRSpace_ratfunc_projective_mono_general` - L(D) ⊆ L(D + [v]) for any place v
* `ell_ratfunc_projective_gap_le_general` - ℓ(D+[v]) ≤ ℓ(D) + deg(v) for any place v

## Strategy

The gap bound for linear places gives ℓ(D+[v]) ≤ ℓ(D) + 1.
For arbitrary places, the gap is at most deg(v) = [κ(v) : k].

The proof:
1. L(D+[v])/L(D) embeds into κ(v) via the evaluation map
2. dim(κ(v)) = deg(v) (from PlaceDegree.finrank_residueField_eq_degree)
3. Therefore ℓ(D+[v]) - ℓ(D) ≤ deg(v)
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Polynomial RatFunc PlaceDegree
open scoped Classical

variable (k : Type*) [Field k] [Fintype k] [DecidableEq k]

/-! ## Monotonicity for arbitrary places -/

/-- Divisor ordering for adding a single place. -/
lemma divisor_le_add_single_general (D : DivisorV2 (Polynomial k))
    (v : HeightOneSpectrum (Polynomial k)) :
    D ≤ D + DivisorV2.single v 1 := by
  intro w
  simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_apply]
  by_cases hw : w = v
  · subst hw
    simp only [↓reduceIte, le_add_iff_nonneg_right, zero_le_one]
  · simp only [if_neg (Ne.symm hw), add_zero, le_refl]

/-- L(D) ⊆ L(D + [v]) for any place v. -/
lemma RRSpace_ratfunc_projective_mono_general (D : DivisorV2 (Polynomial k))
    (v : HeightOneSpectrum (Polynomial k)) :
    RRSpace_ratfunc_projective D ≤
    RRSpace_ratfunc_projective (D + DivisorV2.single v 1) := by
  intro f hf
  rcases hf with ⟨hval, hinfty⟩
  constructor
  · -- Valuation condition for D + [v]
    rcases hval with hzero | hval'
    · left; exact hzero
    right
    intro w
    by_cases hw : w = v
    · subst hw
      simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_apply, ↓reduceIte]
      calc w.valuation (RatFunc k) f
          ≤ WithZero.exp (D w) := hval' w
        _ ≤ WithZero.exp (D w + 1) := by
            apply WithZero.exp_le_exp.mpr; omega
    · simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_apply,
                 if_neg (Ne.symm hw), add_zero]
      exact hval' w
  · exact hinfty

/-! ## Residue field finiteness for arbitrary places -/

/-- The residue field at any place is finite-dimensional over k.
Uses `Polynomial.Monic.finite_adjoinRoot` for monic polynomials. -/
instance residueField_finite (v : HeightOneSpectrum (Polynomial k)) :
    Module.Finite k (Polynomial k ⧸ v.asIdeal) := by
  -- Rewrite using the generator
  rw [asIdeal_eq_span_generator k v]
  -- The generator is monic, so we can use Polynomial.Monic.finite_adjoinRoot
  -- Note: AdjoinRoot g = k[X] ⧸ Ideal.span {g}
  exact (generator_monic k v).finite_adjoinRoot

/-- The residue field at any place is finite-dimensional (alternative phrasing). -/
instance residueFieldAtPrime_finite (v : HeightOneSpectrum (Polynomial k)) :
    Module.Finite k (residueFieldAtPrime (Polynomial k) v) := by
  -- residueFieldAtPrime is isomorphic to k[X]/v.asIdeal for maximal ideals
  haveI hmax : v.asIdeal.IsMaximal := v.isMaximal
  have hbij := Ideal.bijective_algebraMap_quotient_residueField v.asIdeal
  let e := RingEquiv.ofBijective _ hbij
  -- Build a linear equivalence
  have hcompat : ∀ (c : k) (x : Polynomial k ⧸ v.asIdeal), e (c • x) = c • e x := by
    intro c x
    simp only [Algebra.smul_def, map_mul]
    -- Need to show: e (algebraMap k (k[X] ⧸ v.asIdeal) c) = algebraMap k (residueFieldAtPrime) c
    -- This follows from the fact that e is an algebra map
    have halg : e ((algebraMap k (Polynomial k ⧸ v.asIdeal)) c) =
        (algebraMap k (residueFieldAtPrime (Polynomial k) v)) c := by
      -- e is the canonical map from quotient to residue field, which is an algebra map
      simp only [e, RingEquiv.ofBijective_apply]
      rfl
    rw [halg]
  let e_lin : (Polynomial k ⧸ v.asIdeal) ≃ₗ[k] residueFieldAtPrime (Polynomial k) v := {
    e with
    map_smul' := hcompat
  }
  -- Transfer Module.Finite through the equivalence
  exact Module.Finite.equiv e_lin

/-- The dimension of the residue field at place v equals deg(v). -/
lemma finrank_residueFieldAtPrime_eq_degree (v : HeightOneSpectrum (Polynomial k)) :
    Module.finrank k (residueFieldAtPrime (Polynomial k) v) = degree k v := by
  haveI hmax : v.asIdeal.IsMaximal := v.isMaximal
  have hbij := Ideal.bijective_algebraMap_quotient_residueField v.asIdeal
  let e := RingEquiv.ofBijective _ hbij
  have hcompat : ∀ (c : k) (x : Polynomial k ⧸ v.asIdeal), e (c • x) = c • e x := by
    intro c x
    simp only [Algebra.smul_def, map_mul]
    have halg : e ((algebraMap k (Polynomial k ⧸ v.asIdeal)) c) =
        (algebraMap k (residueFieldAtPrime (Polynomial k) v)) c := by
      simp only [e, RingEquiv.ofBijective_apply]
      rfl
    rw [halg]
  let e_lin : (Polynomial k ⧸ v.asIdeal) ≃ₗ[k] residueFieldAtPrime (Polynomial k) v := {
    e with
    map_smul' := hcompat
  }
  rw [← LinearEquiv.finrank_eq e_lin, finrank_residueField_eq_degree k v]

/-! ## Generalized Gap Bound -/

/-- Gap bound for arbitrary places: ℓ(D + [v]) ≤ ℓ(D) + deg(v).

This generalizes `ell_ratfunc_projective_gap_le` from linear places (where deg(v) = 1)
to arbitrary places.

The proof:
1. Build k-linear map ψ : L(D+v) → κ(v) via evaluation at v
2. Show ker(ψ) = L(D) (elements with higher vanishing at v)
3. By first isomorphism theorem: L(D+v)/L(D) ≅ im(ψ) ⊆ κ(v)
4. Since dim(κ(v)) = deg(v), we get ℓ(D+v) - ℓ(D) ≤ deg(v)
-/
theorem ell_ratfunc_projective_gap_le_general (D : DivisorV2 (Polynomial k))
    (v : HeightOneSpectrum (Polynomial k))
    [hfin : Module.Finite k (RRSpace_ratfunc_projective (D + DivisorV2.single v 1))] :
    ell_ratfunc_projective (D + DivisorV2.single v 1) ≤
    ell_ratfunc_projective D + degree k v := by
  have hle := divisor_le_add_single_general k D v
  have hincl : RRSpace_ratfunc_projective D ≤
      RRSpace_ratfunc_projective (D + DivisorV2.single v 1) :=
    RRSpace_ratfunc_projective_mono_general k D v

  -- LD = comap of L(D) in L(D+v)
  let LD := (RRSpace_ratfunc_projective D).comap
      (RRSpace_ratfunc_projective (D + DivisorV2.single v 1)).subtype

  -- The affine evaluation map φ : L_affine(D+v) → κ(v)
  let φ := evaluationMapAt_complete (R := Polynomial k) (K := RatFunc k) v D

  -- L(D+v) elements satisfy the affine condition
  have h_proj_to_affine : ∀ f, f ∈ RRSpace_ratfunc_projective (D + DivisorV2.single v 1) →
      f ∈ RRModuleV2_real (Polynomial k) (RatFunc k) (D + DivisorV2.single v 1) :=
    fun f hf => hf.1

  -- Define ψ : L(D+v) →ₗ[k] κ(v)
  let ψ : ↥(RRSpace_ratfunc_projective (D + DivisorV2.single v 1)) →ₗ[k]
      residueFieldAtPrime (Polynomial k) v := {
    toFun := fun x => φ ⟨x.val, h_proj_to_affine x.val x.property⟩
    map_add' := fun x y => by
      have := φ.map_add ⟨x.val, h_proj_to_affine x.val x.property⟩
          ⟨y.val, h_proj_to_affine y.val y.property⟩
      convert this using 1 <;> rfl
    map_smul' := fun c x => by
      have h1 : (c • x).val = (algebraMap k (Polynomial k) c) • x.val :=
        (IsScalarTower.algebraMap_smul (Polynomial k) c x.val).symm
      have hmem : (algebraMap k (Polynomial k) c) • x.val ∈
          RRModuleV2_real (Polynomial k) (RatFunc k) (D + DivisorV2.single v 1) :=
        Submodule.smul_mem _ _ (h_proj_to_affine x.val x.property)
      have h2 : φ ⟨(algebraMap k (Polynomial k) c) • x.val, hmem⟩ =
          (algebraMap k (Polynomial k) c) • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ := by
        convert φ.map_smul (algebraMap k (Polynomial k) c) ⟨x.val, h_proj_to_affine x.val x.property⟩
      have h3 : (algebraMap k (Polynomial k) c) • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ =
          c • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ :=
        IsScalarTower.algebraMap_smul (Polynomial k) c _
      simp only [RingHom.id_apply]
      calc φ ⟨(c • x).val, h_proj_to_affine (c • x).val (c • x).property⟩
          = φ ⟨(algebraMap k (Polynomial k) c) • x.val, hmem⟩ := by simp only [h1]
        _ = (algebraMap k (Polynomial k) c) • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ := h2
        _ = c • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ := h3
  }

  -- Show LD ≤ ker(ψ)
  have h_LD_le_ker : LD ≤ LinearMap.ker ψ := by
    intro x hx
    rw [LinearMap.mem_ker]
    rw [Submodule.mem_comap] at hx
    have h_affine_mem : x.val ∈ RRModuleV2_real (Polynomial k) (RatFunc k) D := hx.1
    have h_in_affine_Dv : x.val ∈ RRModuleV2_real (Polynomial k) (RatFunc k) (D + DivisorV2.single v 1) :=
      RRModuleV2_mono_inclusion (Polynomial k) (RatFunc k) hle h_affine_mem
    let y_affine : RRModuleV2_real (Polynomial k) (RatFunc k) D := ⟨x.val, h_affine_mem⟩
    have hinc : (⟨x.val, h_in_affine_Dv⟩ : RRModuleV2_real (Polynomial k) (RatFunc k) (D + DivisorV2.single v 1)) =
        Submodule.inclusion (RRModuleV2_mono_inclusion (Polynomial k) (RatFunc k) hle) y_affine := rfl
    show ψ x = 0
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
    have hx_eq : (⟨x.val, h_proj_to_affine x.val x.property⟩ :
        RRModuleV2_real (Polynomial k) (RatFunc k) (D + DivisorV2.single v 1)) =
        ⟨x.val, h_in_affine_Dv⟩ := rfl
    rw [hx_eq, hinc]
    exact LD_element_maps_to_zero v D y_affine

  -- Show ker(ψ) ≤ LD
  have h_ker_le_LD : LinearMap.ker ψ ≤ LD := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk] at hx
    have h_in_ker : (⟨x.val, h_proj_to_affine x.val x.property⟩ :
        RRModuleV2_real (Polynomial k) (RatFunc k) (D + DivisorV2.single v 1)) ∈
        LinearMap.ker φ := hx
    rw [kernel_evaluationMapAt_complete_proof, LinearMap.mem_range] at h_in_ker
    obtain ⟨y, hy⟩ := h_in_ker
    rw [Submodule.mem_comap, Submodule.coe_subtype]
    have hval : y.val = x.val := congrArg Subtype.val hy
    have h_affine : x.val ∈ RRModuleV2_real (Polynomial k) (RatFunc k) D := by
      rw [← hval]; exact y.property
    have h_infty : x.val = 0 ∨ noPoleAtInfinity x.val := x.property.2
    exact ⟨h_affine, h_infty⟩

  -- LD = ker(ψ)
  have h_eq_ker : LD = LinearMap.ker ψ := le_antisymm h_LD_le_ker h_ker_le_LD

  -- The quotient L(D+v)/LD embeds into κ(v) which has dimension deg(v)
  have h_quot_le : Module.finrank k
      (↥(RRSpace_ratfunc_projective (D + DivisorV2.single v 1)) ⧸ LD) ≤ degree k v := by
    -- The descended map: quotient → κ(v) is injective
    let desc := Submodule.liftQ LD ψ h_LD_le_ker
    have h_desc_inj : Function.Injective desc := by
      rw [← LinearMap.ker_eq_bot]
      have hker := Submodule.ker_liftQ LD ψ h_LD_le_ker
      rw [hker, h_eq_ker, Submodule.mkQ_map_self]
    -- finrank of domain ≤ finrank of codomain when injection exists
    calc Module.finrank k (↥(RRSpace_ratfunc_projective (D + DivisorV2.single v 1)) ⧸ LD)
        ≤ Module.finrank k (residueFieldAtPrime (Polynomial k) v) :=
          LinearMap.finrank_le_finrank_of_injective h_desc_inj
      _ = degree k v := finrank_residueFieldAtPrime_eq_degree k v

  -- LD equals range(inclusion) since L(D) ⊆ L(D+v)
  have h_LD_eq : Module.finrank k LD = ell_ratfunc_projective D := by
    unfold ell_ratfunc_projective LD
    have h_eq : (RRSpace_ratfunc_projective D).comap
        (RRSpace_ratfunc_projective (D + DivisorV2.single v 1)).subtype =
        LinearMap.range (Submodule.inclusion hincl) := by
      ext x
      constructor
      · intro hx
        rw [Submodule.mem_comap] at hx
        rw [LinearMap.mem_range]
        exact ⟨⟨x.val, hx⟩, rfl⟩
      · intro hx
        rw [LinearMap.mem_range] at hx
        obtain ⟨y, hy⟩ := hx
        rw [Submodule.mem_comap]
        rw [← hy]; exact y.2
    rw [h_eq]
    exact LinearMap.finrank_range_of_inj (Submodule.inclusion_injective hincl)

  -- Use finrank(quotient) + finrank(LD) = finrank(L(D+v))
  have h_add := Submodule.finrank_quotient_add_finrank LD
  unfold ell_ratfunc_projective
  have h_eq' : Module.finrank k ↥(RRSpace_ratfunc_projective (D + DivisorV2.single v 1)) =
      Module.finrank k LD +
      Module.finrank k (↥(RRSpace_ratfunc_projective (D + DivisorV2.single v 1)) ⧸ LD) := by
    rw [← h_add, add_comm]
  -- Goal: finrank(L(D+v)) ≤ ell(D) + deg(v)
  -- We have: finrank(L(D+v)) = finrank(LD) + finrank(quotient) = ell(D) + finrank(quotient)
  -- And: finrank(quotient) ≤ deg(v)
  calc Module.finrank k ↥(RRSpace_ratfunc_projective (D + DivisorV2.single v 1))
      = Module.finrank k LD +
          Module.finrank k (↥(RRSpace_ratfunc_projective (D + DivisorV2.single v 1)) ⧸ LD) := h_eq'
    _ = ell_ratfunc_projective D +
          Module.finrank k (↥(RRSpace_ratfunc_projective (D + DivisorV2.single v 1)) ⧸ LD) := by
        rw [h_LD_eq]
    _ ≤ ell_ratfunc_projective D + degree k v := by linarith

end RiemannRochV2
