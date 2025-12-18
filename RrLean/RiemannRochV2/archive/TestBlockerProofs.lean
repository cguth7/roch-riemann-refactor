import RrLean.RiemannRochV2.LocalGapInstance

/-!
# Test Proofs for Key Blockers (Cycle 58)

Using Gemini's suggestions:
1. Use `subst` to eliminate casts from `▸`
2. Look for specific _apply lemmas
-/

namespace RiemannRochV2

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- ============================================================================
-- KEY BLOCKER 2: localization_residueField_equiv_algebraMap
-- ============================================================================

/-- Direct proof of blocker 2 using congrArg.

Key insight: Both sides factor through R ⧸ v.asIdeal, and the equivalences
are designed to make the diagrams commute.
-/
lemma localization_residueField_equiv_algebraMap_v4 (v : HeightOneSpectrum R) (r : R) :
    (localization_residueField_equiv v)
      (IsLocalRing.residue (Localization.AtPrime v.asIdeal)
        (algebraMap R (Localization.AtPrime v.asIdeal) r)) =
    algebraMap R (residueFieldAtPrime R v) r := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  -- Unfold the layers
  unfold localization_residueField_equiv
  simp only [RingEquiv.trans_apply]
  -- Handle the residue map: residue = Quotient.mk maxIdeal
  rw [IsLocalRing.residue_def, Ideal.Quotient.mk_algebraMap]
  -- Now LHS = h2 ((localization_residue_equiv v).symm (algebraMap R (Loc ⧸ maxIdeal) r))
  -- First show the key step about equivQuotMaximalIdeal
  have key : (localization_residue_equiv v).symm
      (algebraMap R (Localization.AtPrime v.asIdeal ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) r) =
      Ideal.Quotient.mk v.asIdeal r := by
    unfold localization_residue_equiv
    rw [RingEquiv.symm_apply_eq]
    -- Goal: algebraMap R (Loc ⧸ maxIdeal) r = equivQuotMaximalIdeal (Quotient.mk v.asIdeal r)
    unfold IsLocalization.AtPrime.equivQuotMaximalIdeal
    simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    rfl
  -- Use congrArg to apply key
  have step : (RingEquiv.ofBijective (algebraMap (R ⧸ v.asIdeal) (residueFieldAtPrime R v))
        (Ideal.bijective_algebraMap_quotient_residueField v.asIdeal))
      ((localization_residue_equiv v).symm
        (algebraMap R (Localization.AtPrime v.asIdeal ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) r)) =
      (RingEquiv.ofBijective (algebraMap (R ⧸ v.asIdeal) (residueFieldAtPrime R v))
        (Ideal.bijective_algebraMap_quotient_residueField v.asIdeal))
      (Ideal.Quotient.mk v.asIdeal r) := by
    exact congrArg _ key
  rw [step]
  -- Goal: RingEquiv.ofBijective _ _ (Quotient.mk v.asIdeal r) = algebraMap R (ResidueField) r
  simp only [RingEquiv.ofBijective_apply]
  -- Goal: algebraMap (R ⧸ v.asIdeal) (ResidueField) (Quotient.mk r) = algebraMap R (ResidueField) r
  rw [← Ideal.Quotient.algebraMap_eq]
  rfl

-- ============================================================================
-- KEY BLOCKER 1: valuationRingAt_equiv_algebraMap
-- ============================================================================

/-- The key step: valuationRingAt_equiv_localization' maps algebraMap R K r
to algebraMap R (Localization.AtPrime) r.

Strategy: Use injectivity to K, avoiding rw on dependent types.
-/
lemma valuationRingAt_equiv_algebraMap_v5 (v : HeightOneSpectrum R) (r : R) :
    (valuationRingAt_equiv_localization' (R := R) (K := K) v)
      ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩ =
    algebraMap R (Localization.AtPrime v.asIdeal) r := by
  haveI inst_dvr : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI inst_frac : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- Use injectivity to reduce to equality in K
  apply IsFractionRing.injective (Localization.AtPrime v.asIdeal) K
  -- Goal: algebraMap (Loc) K (LHS) = algebraMap (Loc) K (RHS)
  -- RHS: use scalar tower
  have rhs_eq : algebraMap (Localization.AtPrime v.asIdeal) K
      (algebraMap R (Localization.AtPrime v.asIdeal) r) = algebraMap R K r :=
    IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal) K r
  rw [rhs_eq]
  -- LHS: Need to show algebraMap (Loc) K (equiv ⟨algebraMap R K r, _⟩) = algebraMap R K r
  -- The key property we need: for any x ∈ valuationRingAt v,
  --   algebraMap (Loc) K (valuationRingAt_equiv_localization' v x) = x.val
  -- This is because equivValuationSubring.symm preserves the embedding to K
  -- Let's try to prove this as a separate lemma
  -- For now, use the definition directly
  unfold valuationRingAt_equiv_localization'
  -- The definition is: h ▸ equivValuationSubring.symm
  -- where h : valuationRingAt v = DVR.valuationSubring
  -- After unfolding, we have: (h ▸ equivValuationSubring.symm) ⟨algebraMap R K r, _⟩
  -- The key insight: the result's algebraMap to K equals the original val
  -- This is because equivValuationSubring.symm has this property
  -- equivValuationSubring : Loc.AtPrime ≃+* valuationSubring
  -- equivValuationSubring a = ⟨algebraMap (Loc) K a, _⟩
  -- So equivValuationSubring.symm ⟨x, _⟩ = the unique a with algebraMap (Loc) K a = x
  -- Therefore algebraMap (Loc) K (equivValuationSubring.symm ⟨x, _⟩) = x
  -- The cast h ▸ just changes the type but preserves the val
  -- So for ⟨algebraMap R K r, _⟩ ∈ valuationRingAt v, after cast it has same val
  -- Then equivValuationSubring.symm gives the unique element embedding to that val
  -- Which is algebraMap R K r
  -- Try to finish with simp or native_decide
  simp only [IsDiscreteValuationRing.equivValuationSubring, RingEquiv.symm_trans_apply]
  -- After unfolding, we have:
  -- topEquiv.symm.symm (equivMapOfInjective.symm (subringCongr.symm (h ▸ ⟨algebraMap R K r, _⟩)))
  -- Let's trace through:
  -- 1. h ▸ ⟨algebraMap R K r, _⟩ : DVR.valuationSubring (same val)
  -- 2. subringCongr.symm _ : map ⊤ (same val)
  -- 3. equivMapOfInjective.symm _ : ⊤ (preimage under algebraMap)
  -- 4. topEquiv _ : Loc.AtPrime (the actual element)
  -- algebraMap of step 4 = val of step 1 = algebraMap R K r
  -- The key is step 3: equivMapOfInjective.symm ⟨x, _⟩ gives the element whose algebraMap is x
  sorry

-- Try using show to make the goal explicit
lemma valuationRingAt_equiv_algebraMap_show (v : HeightOneSpectrum R) (r : R) :
    (valuationRingAt_equiv_localization' (R := R) (K := K) v)
      ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩ =
    algebraMap R (Localization.AtPrime v.asIdeal) r := by
  haveI inst_dvr : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI inst_frac : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  apply IsFractionRing.injective (Localization.AtPrime v.asIdeal) K
  show algebraMap (Localization.AtPrime v.asIdeal) K
      ((valuationRingAt_equiv_localization' (R := R) (K := K) v)
        ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩) =
    algebraMap (Localization.AtPrime v.asIdeal) K
      (algebraMap R (Localization.AtPrime v.asIdeal) r)
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal) K r]
  -- Now need to show LHS = algebraMap R K r
  -- The LHS is: algebraMap (Loc) K (equiv ⟨algebraMap R K r, _⟩)
  -- By the property of equivValuationSubring, this should equal (algebraMap R K r)
  -- because equivValuationSubring.symm preserves the embedding to K
  sorry

end RiemannRochV2
