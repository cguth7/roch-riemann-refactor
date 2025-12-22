import RrLean.RiemannRochV2.Definitions.Infrastructure
import RrLean.RiemannRochV2.Dimension.KernelProof
import RrLean.RiemannRochV2.Definitions.RRDefinitions
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Projective Riemann-Roch

This module provides a projective version of Riemann-Roch using `finrank` over a base field `k`
instead of `Module.length` over `R`.

## Key Differences from Affine Version

* **Affine (RRSpace.lean)**: ℓ(D) = Module.length R L(D)
* **Projective (this file)**: ℓ(D) = finrank k L(D)

The projective version requires:
1. A base field `k` with `[Field k] [Algebra k K]`
2. A "properness" axiom: ℓ(0) = 1 (global regular functions are constants)

## Main Definitions

* `ell_proj k R K D` - Dimension of L(D) as a k-vector space
* `RationalPoint k R K v` - Typeclass asserting κ(v) ≅ k
* `ProperCurve k R K` - Typeclass with properness axiom ℓ(0) = 1

## Main Results

* `gap_le_one_proj` - Adding a rational point increases dimension by at most 1
* `riemann_inequality_proj` - ℓ(D) ≤ deg(D) + 1 for effective divisors
-/

namespace RiemannRochV2

open IsDedekindDomain

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable [Algebra k R] [Algebra k K] [IsScalarTower k R K]

/-! ## L(D) as a k-vector space

The Riemann-Roch space L(D) is defined as an R-submodule of K in RRSpace.lean.
Via the scalar tower k → R → K, it's automatically a k-subspace of K.
-/

/-- L(D) viewed as a k-subspace of K.
This is just the R-submodule with its induced k-module structure. -/
def RRSpace_proj (D : DivisorV2 R) : Submodule k K :=
  (RRModuleV2_real R K D).restrictScalars k

/-- The dimension ℓ(D) as a k-vector space dimension.
Returns a natural number (0 if infinite-dimensional). -/
noncomputable def ell_proj (D : DivisorV2 R) : ℕ :=
  Module.finrank k (RRSpace_proj k R K D)

/-! ## Monotonicity -/

/-- When D ≤ E, we have L(D) ⊆ L(E) as k-subspaces. -/
lemma RRSpace_proj_mono {D E : DivisorV2 R} (hDE : D ≤ E) :
    RRSpace_proj k R K D ≤ RRSpace_proj k R K E := by
  intro f hf
  exact RRModuleV2_mono_inclusion R K hDE hf

/-- Monotonicity of ell_proj for finite-dimensional spaces. -/
lemma ell_proj_mono {D E : DivisorV2 R} (hDE : D ≤ E)
    (hfin : Module.Finite k (RRSpace_proj k R K E)) :
    ell_proj k R K D ≤ ell_proj k R K E := by
  unfold ell_proj
  exact Submodule.finrank_mono (RRSpace_proj_mono k R K hDE)

/-! ## Rational Points

A point v is "rational" over k if its residue field κ(v) is isomorphic to k.
This is the generic situation for algebraically closed k. -/

/-- A height-one prime v is a rational point if κ(v) ≅ k as k-algebras.
For algebraically closed k, all closed points are rational. -/
class RationalPoint (v : HeightOneSpectrum R) where
  /-- The residue field is isomorphic to the base field -/
  residue_equiv : residueFieldAtPrime R v ≃ₐ[k] k

/-- For a rational point, the residue field has dimension 1 over k. -/
lemma residue_finrank_eq_one (v : HeightOneSpectrum R) [RationalPoint k R v] :
    Module.finrank k (residueFieldAtPrime R v) = 1 := by
  have e := RationalPoint.residue_equiv (k := k) (R := R) (v := v)
  -- κ(v) ≃ₐ[k] k means κ(v) ≅ k as k-vector spaces
  -- k has finrank 1 over itself
  have h1 : Module.finrank k k = 1 := Module.finrank_self k
  rw [← h1]
  exact LinearEquiv.finrank_eq e.toLinearEquiv

/-! ## Proper Curve Typeclass -/

/-- A proper curve over k has the property that global regular functions are constants.
This is the key axiom that makes ℓ(0) = 1 hold. -/
class ProperCurve where
  /-- L(0) = k, i.e., functions with no poles are constants -/
  ell_zero_eq_one : ell_proj k R K 0 = 1

/-- Alternative: AllRational says every point is rational. -/
class AllRational where
  rational : ∀ v : HeightOneSpectrum R, RationalPoint k R v

/-! ## Gap Bound for Projective Case

The key insight is that the existing evaluation map infrastructure from the affine
case transfers: we have a k-linear map L(D+v) → κ(v) with kernel containing L(D).
When κ(v) ≅ k (rational point), dim κ(v) = 1 over k, so the gap is at most 1.
-/

section GapBound

variable {k R K}

/-- The gap bound: adding a single rational point increases dimension by at most 1.

PROOF IDEA:
1. The evaluation map φ : L(D+v) → κ(v) has ker φ ⊇ L(D)
2. For rational v: dim κ(v) = 1 over k
3. By rank-nullity: dim L(D+v) ≤ dim(ker φ) + 1 ≤ dim L(D) + 1
-/
lemma gap_le_one_proj_of_rational (D : DivisorV2 R) (v : HeightOneSpectrum R)
    [RationalPoint k R v]
    [hfin : Module.Finite k (RRSpace_proj k R K (D + DivisorV2.single v 1))] :
    ell_proj k R K (D + DivisorV2.single v 1) ≤ ell_proj k R K D + 1 := by
  -- The inclusion L(D) → L(D+v) is injective
  have hle := divisor_le_add_single D v
  have hincl : RRSpace_proj k R K D ≤ RRSpace_proj k R K (D + DivisorV2.single v 1) :=
    RRSpace_proj_mono k R K hle

  -- The comap gives us L(D) as a submodule of L(D+v)
  let LD := (RRSpace_proj k R K D).comap (RRSpace_proj k R K (D + DivisorV2.single v 1)).subtype

  -- The quotient L(D+v)/L(D) embeds into κ(v), which has dim 1
  -- So finrank(quotient) ≤ 1
  have h_quot_le : Module.finrank k (↥(RRSpace_proj k R K (D + DivisorV2.single v 1)) ⧸ LD) ≤ 1 := by
    -- For a rational point, κ(v) ≅ k as k-vector space, so has dimension 1
    have h_residue_dim : Module.finrank k (residueFieldAtPrime R v) = 1 :=
      residue_finrank_eq_one k R v

    -- The R-linear evaluation map φ : L(D+v) → κ(v) has kernel = range(inclusion : L(D) → L(D+v))
    -- This is proved in kernel_evaluationMapAt_complete_proof
    -- We've shown LD = range(inclusion), so LD = ker(φ)

    -- The quotient L(D+v)/ker(φ) is isomorphic to range(φ) ⊆ κ(v)
    -- So finrank_k(quotient) = finrank_k(range(φ)) ≤ finrank_k(κ(v)) = 1

    -- Key: the R-module structure on κ(v) comes from scalar tower k → R → κ(v)
    -- So any R-submodule is also a k-submodule, and finrank is preserved

    -- The quotient (as k-module) has dimension at most that of κ(v) = 1
    -- because quotient ≅ image ⊆ κ(v), and any k-subspace of a 1-dim space has dim ≤ 1

    -- Technical: need to show LD = ker(φ) where φ is the R-linear eval map
    -- Then use LinearMap.quotKerEquivRange to get quotient ≅ range
    -- And range ⊆ κ(v) implies finrank(range) ≤ finrank(κ(v)) = 1

    -- The issue is converting between k-finrank and the R-module structure
    -- For k ⊆ R, any R-module is a k-module, and submodule finrank is monotonic

    -- Direct argument: quotient is a k-vector space of dim ≤ 1
    -- because it maps injectively into κ(v) ≅ k (a 1-dimensional k-space)

    -- Using: if f : V → W is k-linear injective and dim W = 1, then dim V ≤ 1
    -- The key missing piece: construct a k-linear injection from quotient to κ(v)

    -- The R-linear evaluation map φ : L(D+v)_R → κ(v) becomes k-linear via restrict_scalars
    -- We have: ker(φ) = range(incl) = LD (this is kernel_evaluationMapAt_complete_proof + h_eq)
    -- So quotient L(D+v)/LD ≅ₗ[R] range(φ) via quotKerEquivRange
    -- And range(φ) is a k-submodule of κ(v)

    -- For the finrank bound: any k-subspace of κ(v) ≅ k has dimension ≤ 1
    -- This is because κ(v) is 1-dimensional over k, so has only {0} and κ(v) as subspaces

    -- The cleanest approach: use that finrank of a submodule ≤ finrank of the ambient module
    -- range(φ) ⊆ κ(v) implies finrank_k(range(φ)) ≤ finrank_k(κ(v)) = 1
    -- And quotient ≅ range(φ) implies finrank_k(quotient) = finrank_k(range(φ))

    -- Technical issue: the quotient is over LD (defined via comap), but the kernel
    -- characterization is for the R-module version. Need to bridge this.

    -- Actually, the quotient we're computing finrank for is over the k-module structure
    -- And LD (as k-submodule) should equal ker(φ) (as k-submodule) when φ is k-linear

    -- Strategy: Show LD = ker(φ) as sets, then use that quotient by ker ≅ range ⊆ κ(v)

    -- Get the R-linear evaluation map
    let φ := evaluationMapAt_complete (R := R) (K := K) v D
    have h_ker_R := kernel_evaluationMapAt_complete_proof (R := R) (K := K) v D

    -- Key observation: LD and ker(φ) have the same underlying set
    -- LD = {x ∈ L(D+v) : x.val ∈ L(D)}
    -- ker(φ) = range(incl) = {x ∈ L(D+v) : ∃ y ∈ L(D), y = x} = {x ∈ L(D+v) : x.val ∈ L(D)}

    -- The quotient L(D+v)/LD as k-vector space embeds into κ(v) which has dim 1
    -- This uses that ker(φ) = LD, so the first iso theorem gives quotient ≅ range(φ) ⊆ κ(v)

    -- For a subspace of a 1-dim space, dim ≤ 1
    -- Since quotient embeds into κ(v), finrank(quotient) ≤ finrank(κ(v)) = 1

    -- The quotient L(D+v)/LD injects into κ(v), which has dim 1 over k
    -- So finrank(quotient) ≤ finrank(κ(v)) = 1

    -- PROOF STRATEGY (to be completed):
    -- 1. Use φ_R.restrictScalars k to get k-linear eval map φ_k
    -- 2. Show ker(φ_k) = LD.comap LD_v.subtype via kernel_evaluationMapAt_complete_proof
    -- 3. Apply LinearMap.finrank_range_add_finrank_ker for dimension counting
    -- 4. Bound dim(range φ_k) ≤ dim(κ(v)) = 1 via Submodule.finrank_le
    -- 5. Conclude dim(LD_v) = dim(ker) + dim(range) ≤ dim(LD) + 1
    -- The key insight: the quotient L(D+v)/LD injects into κ(v) via the evaluation map
    -- Since κ(v) is 1-dimensional over k, the quotient has dimension ≤ 1

    -- LD = comap(subtype)(L(D)) equals range(inclusion) as k-submodules
    -- And range(inclusion) = ker(φ) by kernel_evaluationMapAt_complete_proof
    -- So LD = ker(φ) as sets, meaning the quotient L(D+v)/LD ≅ range(φ) ⊆ κ(v)

    -- The bound follows: finrank(quotient) = finrank(range(φ)) ≤ finrank(κ(v)) = 1

    calc Module.finrank k (↥(RRSpace_proj k R K (D + DivisorV2.single v 1)) ⧸ LD)
        ≤ Module.finrank k (residueFieldAtPrime R v) := by
          -- κ(v) is finite-dimensional over k since κ(v) ≅ₐ[k] k for a rational point
          haveI : Module.Finite k (residueFieldAtPrime R v) := by
            have e := RationalPoint.residue_equiv (k := k) (R := R) (v := v)
            exact Module.Finite.equiv e.symm.toLinearEquiv

          -- Construct a k-linear map ψ : RRSpace_proj → κ(v) with same function as φ
          -- Using the scalar tower k → R → K and k → R → κ(v)
          let ψ : ↥(RRSpace_proj k R K (D + DivisorV2.single v 1)) →ₗ[k]
              residueFieldAtPrime R v :=
            { toFun := fun x => φ ⟨x.val, x.property⟩
              map_add' := fun x y => φ.map_add _ _
              map_smul' := fun c x => by
                -- Goal: φ ⟨(c • x).val, _⟩ = c • φ ⟨x.val, _⟩
                -- c • x in k-module = (algebraMap k R c) • x in R-module via IsScalarTower
                have h1 : (c • x).val = (algebraMap k R c) • x.val :=
                  (IsScalarTower.algebraMap_smul R c x.val).symm
                -- The smul is in the R-submodule
                have hmem : (algebraMap k R c) • x.val ∈ RRModuleV2_real R K (D + DivisorV2.single v 1) :=
                  Submodule.smul_mem _ _ x.property
                -- φ is R-linear
                have h2 : φ ⟨(algebraMap k R c) • x.val, hmem⟩ = (algebraMap k R c) • φ ⟨x.val, x.property⟩ := by
                  convert φ.map_smul (algebraMap k R c) ⟨x.val, x.property⟩ using 1
                -- (algebraMap k R c) • y = c • y in κ(v) via IsScalarTower
                have h3 : (algebraMap k R c) • φ ⟨x.val, x.property⟩ = c • φ ⟨x.val, x.property⟩ :=
                  IsScalarTower.algebraMap_smul R c _
                calc φ ⟨(c • x).val, (c • x).property⟩
                    = φ ⟨(algebraMap k R c) • x.val, hmem⟩ := by simp only [h1]
                  _ = (algebraMap k R c) • φ ⟨x.val, x.property⟩ := h2
                  _ = c • φ ⟨x.val, x.property⟩ := h3 }

          -- Show LD ≤ ker(ψ): elements of L(D) map to 0
          have h_le_ker : LD ≤ LinearMap.ker ψ := by
            intro x hx
            rw [LinearMap.mem_ker]
            rw [Submodule.mem_comap] at hx
            -- hx : x.val ∈ L(D)
            let y : RRModuleV2_real R K D := ⟨x.val, hx⟩
            -- φ(inclusion(y)) = 0 by LD_element_maps_to_zero
            have hinc : (⟨x.val, x.property⟩ : RRModuleV2_real R K (D + DivisorV2.single v 1)) =
                Submodule.inclusion (RRModuleV2_mono_inclusion R K
                    (divisor_le_add_single D v)) y := rfl
            show ψ x = 0
            simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
            rw [hinc]
            exact LD_element_maps_to_zero v D y

          -- Show ker(ψ) ≤ LD: if ψ(x) = 0, then x.val ∈ L(D)
          have h_ker_le : LinearMap.ker ψ ≤ LD := by
            intro x hx
            rw [LinearMap.mem_ker] at hx
            show x ∈ LD
            simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk] at hx
            -- hx : φ ⟨x.val, x.property⟩ = 0, so ⟨x.val, x.property⟩ ∈ ker(φ) = range(incl)
            have h_in_ker : (⟨x.val, x.property⟩ : RRModuleV2_real R K (D + DivisorV2.single v 1)) ∈
                LinearMap.ker φ := hx
            rw [h_ker_R, LinearMap.mem_range] at h_in_ker
            obtain ⟨y, hy⟩ := h_in_ker
            -- y ∈ L(D), and inclusion(y) = ⟨x.val, _⟩, so y.val = x.val
            rw [Submodule.mem_comap, Submodule.coe_subtype]
            -- Goal: x.val ∈ RRSpace_proj k R K D = RRModuleV2_real R K D
            -- hy : inclusion y = ⟨x.val, x.property⟩
            have hval : y.val = x.val := congrArg Subtype.val hy
            rw [← hval]
            exact y.property

          -- LD = ker(ψ)
          have h_eq_ker : LD = LinearMap.ker ψ := le_antisymm h_le_ker h_ker_le

          -- The descended map: quotient → κ(v) is injective
          let desc := Submodule.liftQ LD ψ h_le_ker
          -- desc : quotient →ₗ[k] κ(v)

          -- Kernel of descended map = 0 since LD = ker(ψ)
          have h_desc_inj : Function.Injective desc := by
            rw [← LinearMap.ker_eq_bot]
            -- Submodule.ker_liftQ gives: ker(liftQ p f h) = map (mkQ p) (ker f)
            -- When ker f = p, this becomes map (mkQ p) p = ⊥
            have hker := Submodule.ker_liftQ LD ψ h_le_ker
            rw [hker, h_eq_ker, Submodule.mkQ_map_self]

          -- finrank of domain ≤ finrank of codomain when injection exists
          exact LinearMap.finrank_le_finrank_of_injective h_desc_inj
      _ = 1 := h_residue_dim

  -- LD is the comap of L(D) via subtype, which equals range(inclusion) since L(D) ⊆ L(D+v)
  -- The inclusion is injective, so finrank(LD) = finrank(range) = finrank(L(D))
  have h_LD_eq : Module.finrank k LD = ell_proj k R K D := by
    unfold ell_proj LD
    -- LD = comap subtype L(D) = range(inclusion) since L(D) ⊆ L(D+v)
    -- The proof: comap S.subtype T = {x ∈ S : x.val ∈ T}
    --           range(inclusion hincl) = {x ∈ L(D+v) : ∃ y ∈ L(D), inclusion y = x}
    -- These are equal when T ⊆ S (both equal T viewed inside S)
    have h_eq : (RRSpace_proj k R K D).comap
        (RRSpace_proj k R K (D + DivisorV2.single v 1)).subtype =
        LinearMap.range (Submodule.inclusion hincl) := by
      apply le_antisymm
      · -- comap ≤ range: if x ∈ comap then x ∈ range
        intro x hx
        rw [Submodule.mem_comap] at hx
        rw [LinearMap.mem_range]
        exact ⟨⟨x.val, hx⟩, rfl⟩
      · -- range ≤ comap: if x ∈ range then x ∈ comap
        intro x hx
        rw [LinearMap.mem_range] at hx
        obtain ⟨y, hy⟩ := hx
        rw [Submodule.mem_comap]
        rw [← hy]
        exact y.2
    rw [h_eq]
    exact LinearMap.finrank_range_of_inj (Submodule.inclusion_injective hincl)

  have h_LD_le : Module.finrank k LD ≤ ell_proj k R K D := le_of_eq h_LD_eq

  -- Use: finrank(quotient) + finrank(LD) = finrank(L(D+v))
  -- So: finrank(L(D+v)) = finrank(LD) + finrank(quotient)
  --                     ≤ finrank(L(D)) + 1
  have h_add := Submodule.finrank_quotient_add_finrank LD
  -- h_add : finrank(quotient) + finrank(LD) = finrank(L(D+v))
  unfold ell_proj
  -- Rewrite using h_add (rearranged)
  have h_eq : Module.finrank k ↥(RRSpace_proj k R K (D + DivisorV2.single v 1)) =
      Module.finrank k LD +
      Module.finrank k (↥(RRSpace_proj k R K (D + DivisorV2.single v 1)) ⧸ LD) := by
    rw [← h_add, add_comm]
  rw [h_eq]
  calc Module.finrank k LD +
        Module.finrank k (↥(RRSpace_proj k R K (D + DivisorV2.single v 1)) ⧸ LD)
      ≤ Module.finrank k (RRSpace_proj k R K D) + 1 := Nat.add_le_add h_LD_le h_quot_le

end GapBound

/-! ## Main Theorem: Projective Riemann Inequality -/

/-- Riemann inequality for projective curves: ℓ(D) ≤ deg(D) + 1.

Proof by induction on degree, using:
- Base case: ℓ(0) = 1 from ProperCurve
- Inductive step: gap ≤ 1 from gap_le_one_proj_of_rational
-/
theorem riemann_inequality_proj [ProperCurve k R K] [AllRational k R]
    {D : DivisorV2 R} (hD : D.Effective)
    [∀ E : DivisorV2 R, Module.Finite k (RRSpace_proj k R K E)] :
    (ell_proj k R K D : ℤ) ≤ D.deg + 1 := by
  -- Induction on degree
  have h_deg_nonneg : 0 ≤ D.deg := by
    unfold DivisorV2.deg
    apply Finsupp.sum_nonneg
    intro v _
    exact hD v
  generalize hn : D.deg.toNat = n
  induction n generalizing D with
  | zero =>
    -- deg(D) = 0 and D effective implies D = 0
    have hdeg_zero : D.deg = 0 := by
      have : D.deg.toNat = 0 := hn
      have := Int.toNat_of_nonneg h_deg_nonneg
      omega
    have h_zero : D = 0 := by
      ext v
      by_contra h_neq
      have h_pos : 0 < D v := lt_of_le_of_ne (hD v) (Ne.symm h_neq)
      have h_in_supp : v ∈ D.support := Finsupp.mem_support_iff.mpr (ne_of_gt h_pos)
      have h_sum_pos : 0 < D.deg := by
        unfold DivisorV2.deg
        apply Finsupp.sum_pos'
        · intro x _; exact hD x
        · exact ⟨v, h_in_supp, h_pos⟩
      omega
    subst h_zero
    simp only [DivisorV2.deg_zero, zero_add]
    have h1 : ell_proj k R K 0 = 1 := ProperCurve.ell_zero_eq_one
    omega
  | succ n ih =>
    -- deg(D) = n + 1 > 0, so exists v with D(v) > 0
    have hdeg_pos : D.deg = n + 1 := by
      have h1 := Int.toNat_of_nonneg h_deg_nonneg
      omega
    have h_exists_pos : ∃ v, 0 < D v := DivisorV2.exists_pos_of_deg_pos (R := R) hD (by omega)
    obtain ⟨v, hv⟩ := h_exists_pos
    -- D' = D - single v 1
    let D' := D - DivisorV2.single v 1
    have h_decomp : D = D' + DivisorV2.single v 1 := by
      simp only [D', DivisorV2.sub_add_single_cancel]
    -- D' is effective
    have hD' : D'.Effective := DivisorV2.effective_sub_single (R := R) hD v hv
    -- deg(D') = n
    have hdeg' : D'.deg.toNat = n := by
      have h1 : D'.deg = D.deg - 1 := DivisorV2.deg_sub_single (R := R) D v
      have h2 : 0 ≤ D'.deg := by
        unfold DivisorV2.deg
        apply Finsupp.sum_nonneg
        intro w _; exact hD' w
      omega
    -- Apply IH to D'
    have h_le := ih hD' (by
      unfold DivisorV2.deg
      apply Finsupp.sum_nonneg
      intro w _; exact hD' w) hdeg'
    -- Apply gap bound
    rw [h_decomp]
    haveI : RationalPoint k R v := AllRational.rational v
    have h_step : ell_proj k R K (D' + DivisorV2.single v 1) ≤ ell_proj k R K D' + 1 :=
      gap_le_one_proj_of_rational D' v
    -- Combine
    have hdeg_D' : D'.deg = n := by
      have h1 : D'.deg = D.deg - 1 := DivisorV2.deg_sub_single (R := R) D v
      rw [h1, hdeg_pos]
      ring
    have hdeg_total : (D' + DivisorV2.single v 1).deg = D'.deg + 1 :=
      DivisorV2.deg_add_single' (R := R) D' v
    calc (ell_proj k R K (D' + DivisorV2.single v 1) : ℤ)
        ≤ ell_proj k R K D' + 1 := by exact_mod_cast h_step
      _ ≤ (D'.deg + 1) + 1 := by linarith
      _ = D'.deg + 2 := by ring
      _ = n + 2 := by rw [hdeg_D']
      _ = (n + 1) + 1 := by ring
      _ = (D' + DivisorV2.single v 1).deg + 1 := by rw [hdeg_total, hdeg_D']

end RiemannRochV2
