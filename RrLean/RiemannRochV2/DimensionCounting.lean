import RrLean.RiemannRochV2.KernelProof
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Dimension Counting for LocalGapBound

This file proves the `LocalGapBound` instance using the kernel characterization
from `KernelProof.lean` and Module.length additivity.

## Main Result

* `instance : LocalGapBound R K` - Adding a point increases dimension by at most 1

## Strategy (Cycle 72)

Using Module.length additivity on exact sequences:
1. We have evaluationMapAt_complete : L(D+v) → κ(v)
2. By kernel_evaluationMapAt_complete_proof: ker(φ) = range(inclusion : L(D) → L(D+v))
3. The sequence 0 → ker → L(D+v) → image → 0 is exact
4. ker ≅ L(D), and image ⊆ κ(v) which has length 1
5. Therefore: length(L(D+v)) ≤ length(L(D)) + 1
-/

namespace RiemannRochV2

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## Residue Field Has Length 1

The residue field κ(v) = v.asIdeal.ResidueField is isomorphic to R/v as R-modules.
Since v.asIdeal is maximal, R/v is a field, hence a simple R-module with length 1.
-/

section ResidueFieldLength

-- The quotient R/v.asIdeal is a simple R-module since v.asIdeal is maximal
instance quotient_isSimple (v : HeightOneSpectrum R) :
    IsSimpleModule R (R ⧸ v.asIdeal) := by
  haveI hmax : v.asIdeal.IsMaximal := v.isMaximal
  -- Use isSimpleModule_iff_quot_maximal (backwards)
  -- R/v is isomorphic to R/v via identity, so it's simple
  rw [isSimpleModule_iff_quot_maximal]
  exact ⟨v.asIdeal, hmax, ⟨LinearEquiv.refl R _⟩⟩

-- The residue field κ(v) is a simple R-module
instance residueField_isSimple (v : HeightOneSpectrum R) :
    IsSimpleModule R (residueFieldAtPrime R v) := by
  haveI hmax : v.asIdeal.IsMaximal := v.isMaximal
  -- κ(v) ≅ R/v.asIdeal as R-modules
  have hbij := Ideal.bijective_algebraMap_quotient_residueField v.asIdeal
  let e : (R ⧸ v.asIdeal) ≃ₗ[R] residueFieldAtPrime R v := LinearEquiv.ofBijective
    { toFun := algebraMap (R ⧸ v.asIdeal) (residueFieldAtPrime R v)
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
        rw [IsScalarTower.algebraMap_apply R (R ⧸ v.asIdeal) (residueFieldAtPrime R v) r] }
    hbij
  -- Transport simplicity through the equivalence
  rw [isSimpleModule_iff_quot_maximal]
  exact ⟨v.asIdeal, hmax, ⟨e.symm⟩⟩

-- κ(v) has Module.length = 1 as an R-module
lemma residueField_length (v : HeightOneSpectrum R) :
    Module.length R (residueFieldAtPrime R v) = 1 :=
  Module.length_eq_one_iff.mpr (residueField_isSimple v)

-- Any submodule of κ(v) has length ≤ 1
lemma submodule_of_residueField_length_le (v : HeightOneSpectrum R)
    (M : Submodule R (residueFieldAtPrime R v)) :
    Module.length R M ≤ 1 := by
  calc Module.length R M
      ≤ Module.length R (residueFieldAtPrime R v) :=
        Module.length_le_of_injective (Submodule.subtype M) Subtype.val_injective
    _ = 1 := residueField_length v

end ResidueFieldLength

/-! ## Dimension Bound via Exact Sequence -/

section DimensionBound

-- Key dimension inequality using Module.length
lemma length_LD_plus_v_le (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    Module.length R (RRModuleV2_real R K (D + DivisorV2.single v 1)) ≤
    Module.length R (RRModuleV2_real R K D) + 1 := by
  -- Use the kernel characterization: ker(eval) = range(inclusion)
  have hker := kernel_evaluationMapAt_complete_proof (R := R) (K := K) v D
  -- The inclusion map L(D) → L(D+v)
  let incl := Submodule.inclusion (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v))
  have hincl_inj : Function.Injective incl :=
    Submodule.inclusion_injective (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v))
  -- Key: length is additive via the exact sequence
  -- 0 → ker(eval) → L(D+v) → range(eval) → 0
  let φ := evaluationMapAt_complete (R := R) (K := K) v D
  -- length(L(D+v)) = length(ker φ) + length(range φ) by exact sequence
  have hexact : Module.length R (RRModuleV2_real R K (D + DivisorV2.single v 1)) =
      Module.length R (LinearMap.ker φ) + Module.length R (LinearMap.range φ) := by
    -- Use Module.length_eq_add_of_exact with ker.subtype and rangeRestrict
    have hinj : Function.Injective (LinearMap.ker φ).subtype := Submodule.subtype_injective _
    have hsurj : Function.Surjective (φ.rangeRestrict) := LinearMap.surjective_rangeRestrict φ
    -- The exactness: ker(rangeRestrict) = ker(φ) = range(subtype)
    have hexact_seq : Function.Exact (LinearMap.ker φ).subtype φ.rangeRestrict := by
      rw [LinearMap.exact_iff]
      -- range(subtype) = ker φ as a submodule, and ker(rangeRestrict) = ker φ
      rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]
    exact Module.length_eq_add_of_exact _ _ hinj hsurj hexact_seq
  -- length(ker φ) = length(L(D)) since ker = range(incl) ≅ L(D)
  have hlen_ker : Module.length R (LinearMap.ker φ) =
      Module.length R (RRModuleV2_real R K D) := by
    rw [hker]
    -- range(incl) ≃ L(D) since incl is injective
    exact (LinearEquiv.ofInjective incl hincl_inj).symm.length_eq
  -- length(range φ) ≤ 1 since range ⊆ κ(v) which has length 1
  have hlen_range : Module.length R (LinearMap.range φ) ≤ 1 :=
    submodule_of_residueField_length_le v _
  -- Combine: length(L(D+v)) = length(ker) + length(range) ≤ length(L(D)) + 1
  rw [hexact, hlen_ker]
  -- Goal: length(L(D)) + length(range φ) ≤ length(L(D)) + 1
  -- From hlen_range: length(range φ) ≤ 1
  gcongr

-- Main dimension inequality at ℕ∞ level
lemma ellV2_real_extended_gap_le_one (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    ellV2_real_extended R K (D + DivisorV2.single v 1) ≤
    ellV2_real_extended R K D + 1 := by
  unfold ellV2_real_extended
  exact length_LD_plus_v_le v D

-- Convert to ℕ level
lemma ellV2_real_gap_le_one (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    ellV2_real R K (D + DivisorV2.single v 1) ≤ ellV2_real R K D + 1 := by
  unfold ellV2_real
  by_cases hfin : ellV2_real_extended R K D = ⊤
  · -- If L(D) has infinite length, L(D+v) ⊇ L(D) also has infinite length
    have hfin' : ellV2_real_extended R K (D + DivisorV2.single v 1) = ⊤ := by
      have hmono := ellV2_real_mono_extended R K (divisor_le_add_single D v)
      rw [hfin] at hmono
      exact eq_top_iff.mpr hmono
    simp only [hfin, hfin', ENat.toNat_top]
    exact Nat.zero_le _
  · -- Finite case: both L(D) and L(D+v) have finite length
    -- First, L(D+v) must also be finite
    have hfin' : ellV2_real_extended R K (D + DivisorV2.single v 1) ≠ ⊤ := by
      intro h
      have hle := ellV2_real_extended_gap_le_one (R := R) (K := K) v D
      rw [h] at hle
      -- ⊤ ≤ x + 1 with x ≠ ⊤ is impossible
      simp only [top_le_iff] at hle
      -- hle : ellV2_real_extended R K D + 1 = ⊤
      rw [WithTop.add_eq_top] at hle
      cases hle with
      | inl hle => exact hfin hle
      | inr hle => exact WithTop.one_ne_top hle
    -- Also, D + 1 ≠ ⊤
    have h1_ne_top : (1 : ℕ∞) ≠ ⊤ := WithTop.one_ne_top
    have hsum_ne_top : ellV2_real_extended R K D + 1 ≠ ⊤ := by
      intro h
      rw [WithTop.add_eq_top] at h
      cases h with
      | inl h => exact hfin h
      | inr h => exact h1_ne_top h
    -- Use toNat monotonicity and additivity
    have h := ellV2_real_extended_gap_le_one (R := R) (K := K) v D
    have htoNat := ENat.toNat_le_toNat h hsum_ne_top
    calc (ellV2_real_extended R K (D + DivisorV2.single v 1)).toNat
        ≤ (ellV2_real_extended R K D + 1).toNat := htoNat
      _ = (ellV2_real_extended R K D).toNat + (1 : ℕ∞).toNat :=
          ENat.toNat_add hfin h1_ne_top
      _ = (ellV2_real_extended R K D).toNat + 1 := by rfl

end DimensionBound

/-! ## LocalGapBound Instance -/

-- Lower priority so it doesn't conflict with SinglePointBound inheritance
instance localGapBound_of_dedekind (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (priority := 100) :
    LocalGapBound R K where
  gap_le_one := fun D v => ellV2_real_gap_le_one v D

end RiemannRochV2
