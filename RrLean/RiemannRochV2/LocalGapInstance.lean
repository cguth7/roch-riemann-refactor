import RrLean.RiemannRochV2.Infrastructure
import RrLean.RiemannRochV2.Typeclasses

/-!
# LocalGapInstance - Evaluation Map and LocalGapBound

This file constructs the evaluation map infrastructure needed to prove `LocalGapBound R K`
for Dedekind domains. Once complete, this makes `riemann_inequality_affine` unconditional.

## Table of Contents

| Line | Section | Content |
|------|---------|---------|
| ~30 | EvaluationMapConstruction | **TARGET**: evaluationMapAt, instLocalGapBound |
| ~90 | Cycle26Candidates | valuationRingAt infrastructure |
| ~155 | Cycle27Candidates | partialResidueMap |
| ~245 | Cycle29Candidates | shifted_element_valuation_le_one_v2 ✅ |
| ~370 | Cycle30Candidates | residueMapFromR_ker ✅ |
| ~490 | Cycle31Candidates | localizationAtPrime_isDVR ✅ |
| ~595 | Cycle32Candidates | localization_residue_equiv ✅ |
| ~710 | Cycle33Candidates | localization_maximalIdeal_eq_map ✅ |
| ~805 | Cycle34Candidates | Arithmetic lemmas |
| ~920 | Cycle35Candidates | IsFractionRing instance chain ✅ |
| ~1030 | Cycle36Candidates | range_algebraMap_subset_valuationRingAt ✅ |
| ~1180 | Cycle37Candidates | Complete proof structure (conditional) |
| ~1290 | Cycle38Candidates | intValuation bridge candidates |
| ~1415 | Cycle41Candidates | Foundation lemmas (8/8 PROVED) ✅ |
| ~1540 | Cycle44Candidates_Moved | Ideal power membership bridge (7/8 PROVED) ✅ |
| ~1675 | Cycle39Candidates | dvr_intValuation_of_algebraMap' ✅ (Cycle 47) |
| ~1810 | Cycle42Candidates | Hard case candidates |

## Victory Path

```
dvr_intValuation_of_algebraMap' ✅ (PROVED Cycle 47)
    ↓
dvr_valuation_eq_height_one' (KEY BLOCKER)
    ↓
valuationRingAt_subset_range_algebraMap' → valuationRingAt_equiv_localization
    ↓
residueMapFromR_surjective → evaluationMapAt → instLocalGapBound
```
-/

namespace RiemannRochV2

open IsDedekindDomain

/-! ## Cycle 25: Evaluation Map and LocalGapBound Instance

With the uniformizer infrastructure, we can construct the evaluation map:
  evaluationMapAt v D : L(D+v) →ₗ[R] κ(v)

The key property is:
- ker(evaluationMapAt) = L(D) (embedded in L(D+v))

This allows us to apply `local_gap_bound_of_exists_map` to get the instance. -/

section EvaluationMapConstruction

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 25]
/-- The evaluation map φ : L(D+v) →ₗ[R] κ(v) defined by shifted evaluation.

CONSTRUCTION: For f ∈ L(D+v):
1. Compute g = f · π^{D(v)+1}
2. By shifted_element_valuation_le_one, v(g) ≤ 1
3. Map g to κ(v) via mem_integers → residue map

NOTE: This requires careful handling of the fraction field structure. -/
noncomputable def evaluationMapAt (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    RRModuleV2_real R K (D + DivisorV2.single v 1) →ₗ[R] residueFieldAtPrime R v := sorry

-- Candidate 2 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 25]
/-- The kernel of evaluationMapAt is exactly L(D).

ker(evaluationMapAt v D) = range(Submodule.inclusion : L(D) → L(D+v))

PROOF OUTLINE:
- L(D) ⊆ ker: If f ∈ L(D), then v(f·π^{D(v)+1}) ≤ exp(-1) < 1, so maps to 0
- ker ⊆ L(D): If f maps to 0, then f·π^{D(v)+1} ∈ v.asIdeal, so v(f) ≤ exp(D(v)) -/
lemma kernel_evaluationMapAt (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    LinearMap.ker (evaluationMapAt v D) = LinearMap.range (Submodule.inclusion
      (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v))) := sorry

-- Candidate 3 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 25]
/-- LocalGapBound instance for Dedekind domains.

This completes the proof that ℓ(D+v) ≤ ℓ(D) + 1 unconditionally.
Uses local_gap_bound_of_exists_map with evaluationMapAt and kernel_evaluationMapAt. -/
instance instLocalGapBound (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] : LocalGapBound R K where
  gap_le_one := fun D v => by
    -- Apply the bridge lemma
    have h := local_gap_bound_of_exists_map (R := R) (K := K) D v
      (evaluationMapAt v D)
      (kernel_evaluationMapAt v D)
    -- h : ellV2_real_extended R K (D + single v 1) ≤ ellV2_real_extended R K D + 1
    -- Convert from ℕ∞ to ℕ using toNat
    unfold ellV2_real
    -- Need to show: (ellV2_real_extended R K (D + single v 1)).toNat ≤ (ellV2_real_extended R K D).toNat + 1
    -- From h at ℕ∞ level, need ENat reasoning
    sorry -- Technical ℕ∞ → ℕ conversion via ENat.toNat_le_toNat

end EvaluationMapConstruction

/-! ## Cycle 26 Candidates: Evaluation Map Construction via Valuation Ring

The strategy is to use the valuation ring at v as an intermediate object:
1. Shifted element g = f · π^{D(v)+1} has v(g) ≤ 1
2. g belongs to valuation ring at v (not necessarily to R)
3. Valuation ring ≃ Localization.AtPrime v.asIdeal (DVR)
4. Use DVR residue structure to map to κ(v)
-/

section Cycle26Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: coercion_simplify] [status: OK]
/-- WithZero.exp arithmetic: exp(a) * exp(b) = exp(a+b).
This is the key identity needed for shifted_element_valuation_le_one. -/
lemma withzero_exp_mul (a b : ℤ) :
    WithZero.exp a * WithZero.exp b = WithZero.exp (a + b) :=
  (WithZero.exp_add a b).symm

-- Candidate 2 [tag: coercion_simplify] [status: OK]
/-- Exp of negation: exp(-a) is the inverse of exp(a). -/
lemma withzero_exp_neg (a : ℤ) :
    WithZero.exp (-a) = (WithZero.exp a)⁻¹ := by
  rw [WithZero.exp_neg]

-- Candidate 3 [tag: bundle_divisor_bridge] [status: OK]
/-- The valuation ring of v in K: {g ∈ K : v(g) ≤ 1}.
This is the natural domain for the residue map to κ(v). -/
noncomputable def valuationRingAt (v : HeightOneSpectrum R) : ValuationSubring K :=
  (v.valuation K).valuationSubring

-- Candidate 4 [tag: bundle_divisor_bridge] [status: PROVED]
/-- Elements with v-valuation ≤ 1 belong to the valuation ring at v. -/
lemma mem_valuationRingAt_iff (v : HeightOneSpectrum R) (g : K) :
    g ∈ valuationRingAt v ↔ v.valuation K g ≤ 1 :=
  Valuation.mem_valuationSubring_iff (v.valuation K) g

-- Candidate 5 [tag: bundle_divisor_bridge] [status: PROVED]
/-- R embeds into the valuation ring at any prime v.
Elements of R have v-valuation ≤ 1 for all v. -/
lemma algebraMap_mem_valuationRingAt (v : HeightOneSpectrum R) (r : R) :
    algebraMap R K r ∈ valuationRingAt v := by
  rw [mem_valuationRingAt_iff]
  exact v.valuation_le_one r

-- Candidate 6 [tag: rr_bundle_bridge] [status: PROVED]
/-- The valuation ring at v is a local ring with maximal ideal {g : v(g) < 1}. -/
instance valuationRingAt.isLocalRing (v : HeightOneSpectrum R) :
    IsLocalRing (valuationRingAt (R := R) (K := K) v) :=
  ValuationSubring.isLocalRing (valuationRingAt v)

-- Candidate 7 [tag: rr_bundle_bridge] [status: OK]
/-- The residue field of the valuation ring at v. -/
noncomputable abbrev valuationRingAt.residueField (v : HeightOneSpectrum R) :=
  IsLocalRing.ResidueField (valuationRingAt (R := R) (K := K) v)

-- Candidate 8 [tag: rr_bundle_bridge] [status: OK]
/-- The residue map from the valuation ring at v to its residue field. -/
noncomputable def valuationRingAt.residue (v : HeightOneSpectrum R) :
    valuationRingAt (R := R) (K := K) v →+* valuationRingAt.residueField (R := R) (K := K) v :=
  IsLocalRing.residue (valuationRingAt (R := R) (K := K) v)

end Cycle26Candidates

/-! ## Cycle 27 Candidates: Completing the Residue Field Bridge

The goal is to:
1. Complete shifted_element_valuation_le_one using WithZero.exp arithmetic
2. Establish the bridge between valuationRingAt.residueField and residueFieldAtPrime
3. Construct evaluationMapAt using this bridge
-/

section Cycle27Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: coercion_simplify] [status: OK]
/-- Inverse relationship for WithZero.exp: exp(a) ≤ exp(b) ↔ a ≤ b.
This is a key simplification needed for shifted_element_valuation_le_one. -/
lemma withzero_exp_le_exp (a b : ℤ) :
    WithZero.exp a ≤ WithZero.exp b ↔ a ≤ b :=
  WithZero.exp_le_exp

-- Candidate 2 [tag: coercion_simplify] [status: OK]
/-- Transitivity helper: if exp(a) * exp(b) ≤ 1 and exp(a) * exp(b) = exp(a+b), then a+b ≤ 0.
Needed to complete shifted_element_valuation_le_one. -/
lemma withzero_exp_mul_le_one (a b : ℤ) (h : WithZero.exp a * WithZero.exp b ≤ 1) :
    a + b ≤ 0 := by
  rw [← WithZero.exp_add] at h
  rw [← WithZero.exp_zero] at h
  exact WithZero.exp_le_exp.mp h

-- Candidate 3 [tag: bundle_divisor_bridge] [status: OK]
/-- For Dedekind domains, the algebra map R → valuationRingAt v factors through
the canonical embedding R → K and the inclusion valuationRingAt v ⊆ K.
This establishes that R embeds compatibly into the valuation ring. -/
lemma algebraMap_valuationRingAt_comm (v : HeightOneSpectrum R) (r : R) :
    ((⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩ :
      valuationRingAt (R := R) (K := K) v) : K) = algebraMap R K r :=
  rfl

-- Candidate 4 [tag: rr_bundle_bridge] [status: OK]
/-- The composition: embed K-element into valuation ring, then apply residue map.
This defines a partial residue map from K to κ(v) for elements with v(g) ≤ 1.
Preparatory step for constructing evaluationMapAt. -/
noncomputable def partialResidueMap (v : HeightOneSpectrum R) (g : K) (h : v.valuation K g ≤ 1) :
    valuationRingAt.residueField (R := R) (K := K) v :=
  (valuationRingAt.residue (R := R) (K := K) v).toFun ⟨g, (mem_valuationRingAt_iff v g).mpr h⟩

-- Candidate 5 [tag: rr_bundle_bridge] [status: OK]
/-- Global integrality criterion: if v(g) ≤ 1 for ALL height-1 primes, then g ∈ R.
This explains why we need the local (valuation ring) approach - shifted elements
may have poles at OTHER primes, so they're not in R globally. -/
lemma mem_range_iff_valuation_le_one_everywhere (g : K)
    (h : ∀ (w : HeightOneSpectrum R), w.valuation K g ≤ 1) :
    g ∈ (algebraMap R K).range :=
  HeightOneSpectrum.mem_integers_of_valuation_le_one K g h

-- Candidate 6 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 28]
/-- The partialResidueMap sends 0 to 0.

The subtype ⟨0, h⟩ is definitionally equal to 0 in SubringClass,
so map_zero applies directly. -/
lemma partialResidueMap_zero (v : HeightOneSpectrum R) :
    partialResidueMap (R := R) (K := K) v 0 (by simp only [map_zero]; exact zero_le') = 0 := by
  unfold partialResidueMap
  exact map_zero (valuationRingAt.residue (R := R) (K := K) v)

-- Candidate 7 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 28]
/-- The partialResidueMap is additive for elements both with v(g) ≤ 1.

In SubringClass, ⟨g₁ + g₂, _⟩ = ⟨g₁, _⟩ + ⟨g₂, _⟩ definitionally,
so map_add applies directly. -/
lemma partialResidueMap_add (v : HeightOneSpectrum R) (g₁ g₂ : K)
    (h₁ : v.valuation K g₁ ≤ 1) (h₂ : v.valuation K g₂ ≤ 1)
    (h_sum : v.valuation K (g₁ + g₂) ≤ 1) :
    partialResidueMap v (g₁ + g₂) h_sum = partialResidueMap v g₁ h₁ + partialResidueMap v g₂ h₂ := by
  unfold partialResidueMap
  -- The subtype ⟨g₁ + g₂, _⟩ = ⟨g₁, _⟩ + ⟨g₂, _⟩ by definition in SubringClass
  -- Then .toFun is just application, and map_add gives the result
  rfl

-- Candidate 8 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 28]
/-- The partialResidueMap respects scalar multiplication by R.

In SubringClass, ⟨r * g, _⟩ = ⟨r, _⟩ * ⟨g, _⟩ definitionally,
so map_mul applies directly. -/
lemma partialResidueMap_smul (v : HeightOneSpectrum R) (r : R) (g : K)
    (h : v.valuation K g ≤ 1)
    (h_smul : v.valuation K (algebraMap R K r * g) ≤ 1) :
    partialResidueMap v (algebraMap R K r * g) h_smul =
    ((valuationRingAt.residue (R := R) (K := K) v) ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩) *
    partialResidueMap v g h := by
  unfold partialResidueMap
  -- The subtype ⟨r * g, _⟩ = ⟨r, _⟩ * ⟨g, _⟩ by definition in SubringClass
  -- Then .toFun is just application, and map_mul gives the result
  rfl

end Cycle27Candidates

/-! ## Cycle 29 Candidates: shifted_element proof and residue field bridge -/

section Cycle29Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: coercion_simplify] [status: OK]
/-- Case analysis for Int.toNat: when n ≥ 0, toNat n = n as natural number.
Helper for shifted_element_valuation_le_one. -/
lemma toNat_nonneg_case (n : ℤ) (hn : 0 ≤ n) :
    WithZero.exp (-(n.toNat : ℤ)) = WithZero.exp (-n) := by
  rw [Int.toNat_of_nonneg hn]

-- Candidate 2 [tag: coercion_simplify] [status: OK]
/-- Case analysis for Int.toNat: when n < 0, toNat n = 0.
Helper for shifted_element_valuation_le_one when D(v)+1 < 0. -/
lemma toNat_neg_case (n : ℤ) (hn : n < 0) :
    n.toNat = 0 := by
  exact Int.toNat_eq_zero.mpr (le_of_lt hn)

-- Candidate 3 [tag: bundle_divisor_bridge] [status: PROVED]
/-- Complete proof of shifted_element_valuation_le_one using case analysis on D(v)+1.
This is the KEY lemma for evaluation map construction. -/
lemma shifted_element_valuation_le_one_v2
    (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : K) (hf : f ∈ RRModuleV2_real R K (D + DivisorV2.single v 1)) :
    v.valuation K (f * algebraMap R K ((uniformizerAt v) ^ (D v + 1).toNat)) ≤ 1 := by
  -- Handle f = 0 case
  rcases hf with rfl | hf'
  · simp only [zero_mul, map_zero, zero_le']
  -- f ≠ 0 case: use membership condition and uniformizer properties
  have hfv := hf' v
  simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_eq_same] at hfv
  -- hfv : v.valuation K f ≤ WithZero.exp (D v + 1)
  rw [Valuation.map_mul]
  -- Goal: v(f) * v(π^n) ≤ 1 where n = (D v + 1).toNat
  by_cases h_nonneg : 0 ≤ D v + 1
  · -- Case 1: D(v) + 1 ≥ 0
    -- n = D(v) + 1 as ℕ
    have hn_eq : ((D v + 1).toNat : ℤ) = D v + 1 := Int.toNat_of_nonneg h_nonneg
    -- v(π^n) = exp(-n) = exp(-(D(v)+1))
    rw [uniformizerAt_pow_valuation]
    -- v(f) * exp(-n) ≤ exp(D(v)+1) * exp(-(D(v)+1)) = exp(0) = 1
    calc v.valuation K f * WithZero.exp (-(D v + 1).toNat : ℤ)
        ≤ WithZero.exp (D v + 1) * WithZero.exp (-(D v + 1).toNat : ℤ) := by
          apply mul_le_mul' hfv (le_refl _)
      _ = WithZero.exp (D v + 1) * WithZero.exp (-(D v + 1)) := by
          rw [hn_eq]
      _ = WithZero.exp ((D v + 1) + (-(D v + 1))) := by
          rw [← WithZero.exp_add]
      _ = WithZero.exp 0 := by ring_nf
      _ = 1 := WithZero.exp_zero
  · -- Case 2: D(v) + 1 < 0
    push_neg at h_nonneg
    -- n = 0 (toNat of negative is 0)
    have hn_zero : (D v + 1).toNat = 0 := toNat_neg_case (D v + 1) h_nonneg
    rw [hn_zero, pow_zero]
    simp only [map_one, mul_one]
    -- v(f) ≤ exp(D(v)+1) < exp(0) = 1
    have h_exp_lt : WithZero.exp (D v + 1) < WithZero.exp (0 : ℤ) := by
      rw [WithZero.exp_lt_exp]
      exact h_nonneg
    have h_lt : v.valuation K f < 1 := by
      calc v.valuation K f
          ≤ WithZero.exp (D v + 1) := hfv
        _ < WithZero.exp (0 : ℤ) := h_exp_lt
        _ = 1 := WithZero.exp_zero
    exact le_of_lt h_lt

-- Candidate 4 [tag: rr_bundle_bridge] [status: PROVED]
/-- The valuation ring at v embeds into K, and this embedding is compatible
with the algebra structure. Elements have valuation ≤ 1 by definition. -/
lemma valuationRingAt_embedding_compatible (v : HeightOneSpectrum R)
    (g : valuationRingAt (R := R) (K := K) v) :
    v.valuation K (g : K) ≤ 1 := by
  rw [← mem_valuationRingAt_iff]
  exact g.property

-- Candidate 5 [tag: rr_bundle_bridge] [status: SUPERSEDED]
-- SUPERSEDED: Use residueFieldBridge_explicit (Cycle 52, line 2210) which is PROVED.
/-- For Dedekind domains, the residue field of the valuation ring at v
is ring-isomorphic to the residue field at the prime v.asIdeal.
This is the KEY bridge for constructing evaluationMapAt.

Note: This requires showing that valuationRingAt v ≃ Localization.AtPrime v.asIdeal
and that their residue fields are compatible.
Uses RingEquiv instead of LinearEquiv to avoid Module instance issues. -/
noncomputable def residueFieldBridge (v : HeightOneSpectrum R) :
    valuationRingAt.residueField (R := R) (K := K) v ≃+* residueFieldAtPrime R v := sorry

-- Candidate 6 [tag: rr_bundle_bridge] [status: SUPERSEDED]
-- SUPERSEDED: Should use residueFieldBridge_explicit + residueField_equiv_commutes_with_residue.
/-- The residue field bridge commutes with the natural residue maps:
algebraMap R → valuationRingAt v → residue field at valuation ring
is equivalent to algebraMap R → residue field at prime. -/
lemma residueFieldBridge_algebraMap_comm (v : HeightOneSpectrum R) (r : R) :
    (residueFieldBridge (R := R) (K := K) v) ((valuationRingAt.residue (R := R) (K := K) v)
      ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩) =
    (residueMapAtPrime R v) r := sorry

-- Candidate 7 [tag: rr_bundle_bridge] [status: ACTIVE_TARGET]
-- ACTIVE TARGET: Can now be proved using residueFieldBridge_explicit (PROVED in Cycle 52).
-- BLOCKED BY: shifted_element_valuation_le_one (Infrastructure.lean:274)
/-- Construct evaluationMapAt using the residue field bridge.
For f ∈ L(D+v), compute g = f · π^{D(v)+1}, use shifted_element_valuation_le_one
to show g ∈ valuationRingAt v, apply residue, then bridge to residueFieldAtPrime. -/
noncomputable def evaluationMapAt_via_bridge (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    RRModuleV2_real R K (D + DivisorV2.single v 1) →ₗ[R] residueFieldAtPrime R v := sorry

-- Candidate 8 [tag: coercion_simplify] [status: PROVED]
/-- Valuation multiplicativity with explicit algebraMap coercion.
For r ∈ R and f ∈ K: v(r·f) = v(r) * v(f).
Helper for showing evaluation map respects R-module structure. -/
lemma valuation_algebraMap_mul (v : HeightOneSpectrum R) (r : R) (f : K) :
    v.valuation K (algebraMap R K r * f) =
    v.valuation K (algebraMap R K r) * v.valuation K f :=
  (v.valuation K).map_mul (algebraMap R K r) f

end Cycle29Candidates

/-! ## Cycle 30 Candidates: Residue Field Bridge and Bypass Strategy

The goal is to close the gap between:
- `valuationRingAt.residueField v` (residue field of valuation ring)
- `residueFieldAtPrime R v` (= v.asIdeal.ResidueField)

Strategy: **Bypass** - Instead of proving they're isomorphic, prove:
1. `valuationRingAt.residueField v` is simple as R-module
2. Hence has Module.length R = 1
3. Redefine evaluation map to target `valuationRingAt.residueField` directly
-/

section Cycle30Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Helper: The embedding from R to valuationRingAt v as a ring homomorphism
noncomputable def embeddingToValuationRingAt (v : HeightOneSpectrum R) :
    R →+* valuationRingAt (R := R) (K := K) v where
  toFun r := ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩
  map_one' := by simp only [map_one]; rfl
  map_mul' x y := by simp only [map_mul]; rfl
  map_zero' := by simp only [map_zero]; rfl
  map_add' x y := by simp only [map_add]; rfl

-- Candidate 1 [tag: bypass_bridge] [status: PROVED] [cycle: 30]
/-- The maximal ideal of valuationRingAt v corresponds to v.asIdeal in R.
Elements of maximal ideal have valuation < 1, which for R means membership in v.asIdeal. -/
lemma maximalIdeal_valuationRingAt_comap (v : HeightOneSpectrum R) :
    (IsLocalRing.maximalIdeal (valuationRingAt (R := R) (K := K) v)).comap
      (embeddingToValuationRingAt (R := R) (K := K) v) = v.asIdeal := by
  ext r
  simp only [Ideal.mem_comap, embeddingToValuationRingAt, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk]
  -- r maps to maximal ideal iff v(r) < 1 (in the valuation ring)
  -- The embedding sends r ↦ ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩
  -- valuationRingAt v = (v.valuation K).valuationSubring definitionally
  -- Use Valuation.mem_maximalIdeal_iff and HeightOneSpectrum.valuation_lt_one_iff_mem
  change (⟨algebraMap R K r, _⟩ : (v.valuation K).valuationSubring) ∈
    IsLocalRing.maximalIdeal _ ↔ r ∈ v.asIdeal
  rw [Valuation.mem_maximalIdeal_iff]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem v r

-- Candidate 2 [tag: bypass_bridge] [status: OK] [cycle: 30]
/-- The natural ring homomorphism from R to the residue field of valuationRingAt v
factors through v.asIdeal (its kernel is v.asIdeal).

This gives a field homomorphism R/v.asIdeal → valuationRingAt.residueField v. -/
noncomputable def residueMapFromR (v : HeightOneSpectrum R) :
    R →+* valuationRingAt.residueField (R := R) (K := K) v :=
  (IsLocalRing.residue (valuationRingAt (R := R) (K := K) v)).comp
    (embeddingToValuationRingAt (R := R) (K := K) v)

-- Candidate 3 [tag: bypass_bridge] [status: PROVED] [cycle: 30]
/-- The kernel of residueMapFromR is exactly v.asIdeal. -/
lemma residueMapFromR_ker (v : HeightOneSpectrum R) :
    RingHom.ker (residueMapFromR (R := R) (K := K) v) = v.asIdeal := by
  ext r
  simp only [RingHom.mem_ker, residueMapFromR, RingHom.coe_comp, Function.comp_apply]
  rw [IsLocalRing.residue_eq_zero_iff]
  -- ⟨algebraMap R K r, _⟩ ∈ maximalIdeal ↔ r ∈ v.asIdeal
  have h := maximalIdeal_valuationRingAt_comap (R := R) (K := K) v
  rw [← h]
  simp only [Ideal.mem_comap]

-- Candidate 4 [tag: bypass_bridge] [status: OBSOLETE] [cycle: 30]
-- OBSOLETE: Bypassed by Cycle 52's mapEquiv approach. residueFieldBridge_explicit
-- now uses valuationRingAt_equiv_localization' + IsLocalRing.ResidueField.mapEquiv
-- without needing surjectivity of R → residueField.
/-- The residue map from R to valuationRingAt.residueField v is surjective.
Every element of the residue field has a representative in R. -/
lemma residueMapFromR_surjective (v : HeightOneSpectrum R) :
    Function.Surjective (residueMapFromR (R := R) (K := K) v) := by
  intro x
  -- x is a residue class, lift to valuationRingAt v
  obtain ⟨g, rfl⟩ := IsLocalRing.residue_surjective x
  -- g ∈ valuationRingAt v means v(g) ≤ 1
  -- Need to find r ∈ R with algebraMap R K r - g ∈ maximalIdeal
  -- For Dedekind domains, R is dense enough in the valuation ring
  -- This uses the fact that R is integrally closed and v is a DVR
  sorry

-- Candidate 5 [tag: bypass_bridge] [status: OBSOLETE] [cycle: 30]
-- OBSOLETE: First Isomorphism Theorem approach superseded by Cycle 52's mapEquiv.
-- Use residueFieldBridge_explicit (line 2196) instead.
/-- The residue field of valuationRingAt v is isomorphic to R/v.asIdeal as rings.
Uses the First Isomorphism Theorem: if φ: R → S is surjective, then R/ker(φ) ≃ S.

Proof outline:
1. residueMapFromR : R →+* residueField is surjective (Candidate 4)
2. ker(residueMapFromR) = v.asIdeal (Candidate 3)
3. Apply quotientKerEquivOfSurjective

BLOCKED: Needs residueMapFromR_surjective (Candidate 4) and correct quotient transport.
-/
noncomputable def residueFieldBridge_v2 (v : HeightOneSpectrum R) :
    valuationRingAt.residueField (R := R) (K := K) v ≃+* (R ⧸ v.asIdeal) := by
  -- The First Isomorphism Theorem approach
  -- R / ker(residueMapFromR) ≃ range(residueMapFromR) = residueField (since surjective)
  -- ker(residueMapFromR) = v.asIdeal
  -- So R / v.asIdeal ≃ residueField
  sorry

-- Candidate 6 [tag: bypass_bridge] [status: OBSOLETE] [cycle: 30]
-- OBSOLETE: Superseded by residueFieldBridge_explicit (Cycle 52, line 2196).
/-- The full residue field bridge: valuationRingAt.residueField v ≃+* residueFieldAtPrime R v.
Composes Candidate 5 with the canonical isomorphism R/v.asIdeal ≃ v.asIdeal.ResidueField.

BLOCKED: Needs residueFieldBridge_v2 (which needs surjectivity) -/
noncomputable def residueFieldBridge_v3 (v : HeightOneSpectrum R) :
    valuationRingAt.residueField (R := R) (K := K) v ≃+* residueFieldAtPrime R v := by
  -- Placeholder - compose with quotient isomorphism
  sorry

-- OBSOLETE: Use residueFieldBridge_explicit (Cycle 52, line 2196) instead.
noncomputable def residueFieldBridge' (v : HeightOneSpectrum R) :
    valuationRingAt.residueField (R := R) (K := K) v ≃+* residueFieldAtPrime R v :=
  residueFieldBridge_v3 v

end Cycle30Candidates

/-! ## Cycle 31 Candidates: Proving residueMapFromR_surjective

OBSOLETE: This entire approach was bypassed by Cycle 52's mapEquiv discovery.
The residueFieldBridge is now proved via:
  valuationRingAt_equiv_localization' → IsLocalRing.ResidueField.mapEquiv → localization_residueField_equiv
See residueFieldBridge_explicit (line 2196) for the working proof.

Strategy: Direct proof using First Isomorphism Theorem approach.

Key insight:
1. We have residueMapFromR_ker : ker = v.asIdeal (PROVED in Cycle 30)
2. R/v.asIdeal is a field (v.asIdeal is maximal)
3. If surjective, then R/v.asIdeal ≃ valuationRingAt.residueField by First Isomorphism Theorem

The key mathematical content is showing that every element of valuationRingAt.residueField
has a preimage in R. This follows from R being "dense" in the valuation ring modulo maximalIdeal.
-/

section Cycle31Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: dvr_bridge] [status: PROVED] [cycle: 31]
/-- The localization of a Dedekind domain at a height-1 prime is a DVR. -/
instance localizationAtPrime_isDVR (v : HeightOneSpectrum R) :
    IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot
    (Localization.AtPrime v.asIdeal)

-- Candidate 2 [tag: core_lemma] [status: OBSOLETE] [cycle: 31]
-- OBSOLETE: Not needed - Cycle 52 proved residueFieldBridge without this density argument.
/-- For any g ∈ valuationRingAt v (i.e., v(g) ≤ 1), there exists r ∈ R such that
algebraMap r ≡ g (mod maximalIdeal of valuationRingAt).

Mathematical content: R is "dense" in the valuation ring modulo maximalIdeal.

Proof strategy: Write g = a/b for a, b ∈ R. Since v(g) ≤ 1:
- Case b ∉ v.asIdeal: v(b) = 1, so v(a) = v(g) ≤ 1. Take r = a. Then
  algebraMap r - g = a - a/b = a(1 - 1/b) = a(b-1)/b. Need v(a(b-1)/b) < 1.
- Use CRT or approximation to handle general case. -/
lemma exists_same_residue_class (v : HeightOneSpectrum R)
    (g : valuationRingAt (R := R) (K := K) v) :
    ∃ r : R, (embeddingToValuationRingAt (R := R) (K := K) v r) - g ∈
      IsLocalRing.maximalIdeal (valuationRingAt (R := R) (K := K) v) := by
  sorry

-- Candidate 3 [tag: main_proof] [status: OBSOLETE] [cycle: 31]
-- OBSOLETE: Not needed - Cycle 52 proved residueFieldBridge without surjectivity.
/-- Surjectivity of residueMapFromR using exists_same_residue_class. -/
lemma residueMapFromR_surjective' (v : HeightOneSpectrum R) :
    Function.Surjective (residueMapFromR (R := R) (K := K) v) := by
  intro x
  obtain ⟨g, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨r, hr⟩ := exists_same_residue_class v g
  use r
  -- residueMapFromR r = residue (embedding r) = residue g
  simp only [residueMapFromR, RingHom.coe_comp, Function.comp_apply]
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hr

-- Candidate 4 [tag: first_isomorphism] [status: OK] [cycle: 31]
/-- Once surjectivity is proved, residue field bridge follows from First Isomorphism Theorem.
R/ker(φ) ≃ target when φ is surjective. Since ker = v.asIdeal, we get R/v.asIdeal ≃ residueField. -/
noncomputable def residueFieldBridge_v2_of_surj (v : HeightOneSpectrum R)
    (h : Function.Surjective (residueMapFromR (R := R) (K := K) v)) :
    (R ⧸ v.asIdeal) ≃+* valuationRingAt.residueField (R := R) (K := K) v := by
  have hker := residueMapFromR_ker (R := R) (K := K) v
  have equiv := RingHom.quotientKerEquivOfSurjective h
  -- Transport along ker = v.asIdeal
  exact hker ▸ equiv

-- Candidate 5 [tag: bridge_complete] [status: OK] [cycle: 31]
/-- Full bridge: valuationRingAt.residueField v ≃+* residueFieldAtPrime R v.
Composes residueFieldBridge_v2 with R/v.asIdeal ≃ v.asIdeal.ResidueField. -/
noncomputable def residueFieldBridge_v3_of_surj (v : HeightOneSpectrum R)
    (h : Function.Surjective (residueMapFromR (R := R) (K := K) v)) :
    valuationRingAt.residueField (R := R) (K := K) v ≃+* residueFieldAtPrime R v := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  -- residueField ≃ R/v.asIdeal ≃ v.asIdeal.ResidueField
  have h1 := (residueFieldBridge_v2_of_surj v h).symm
  have h2 := RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField v.asIdeal)
  exact h1.trans h2

-- Candidate 6 [tag: wrap_up] [status: SORRY] [cycle: 31]
/-- Alternative direct approach: show valuationRingAt is "close" to Localization.AtPrime.
Every element of valuationRingAt can be written as r/s for r, s ∈ R with s ∉ v.asIdeal. -/
lemma valuationRingAt_eq_fractions (v : HeightOneSpectrum R)
    (g : valuationRingAt (R := R) (K := K) v) :
    ∃ (r : R) (s : v.asIdeal.primeCompl),
      g.val = algebraMap R K r / algebraMap R K s := by
  -- g.val is in K, so IsFractionRing.div_surjective gives a/b
  -- The condition v(g) ≤ 1 constrains the relationship
  sorry

-- Candidate 7 [tag: helper] [status: OK] [cycle: 31]
/-- Helper: If s ∉ v.asIdeal, then v(s) = 1 (v-adic unit). -/
lemma valuation_eq_one_of_not_mem (v : HeightOneSpectrum R) {s : R} (hs : s ∉ v.asIdeal) :
    v.valuation K (algebraMap R K s) = 1 := by
  apply le_antisymm (v.valuation_le_one s)
  rw [← not_lt]
  intro hlt
  exact hs (v.valuation_lt_one_iff_mem s |>.mp hlt)

-- Candidate 8 [tag: helper] [status: OK] [cycle: 31]
/-- Helper: v(r/s) = v(r)/v(s) = v(r) when v(s) = 1. -/
lemma valuation_div_eq_of_unit (v : HeightOneSpectrum R) {r s : R} (hs : s ∉ v.asIdeal) :
    v.valuation K (algebraMap R K r / algebraMap R K s) = v.valuation K (algebraMap R K r) := by
  rw [Valuation.map_div, valuation_eq_one_of_not_mem v hs, div_one]

end Cycle31Candidates

/-! ## Cycle 32 Candidates: Bypass via Localization Machinery

Key discovery: `IsLocalization.AtPrime.equivQuotMaximalIdeal` provides
R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ with FULL surjectivity built in.

Strategy: Instead of proving `exists_same_residue_class` directly,
compose equivalences:
1. R ⧸ v.asIdeal ≃+* (Loc.AtPrime v.asIdeal) ⧸ maxIdeal (from equivQuotMaximalIdeal)
2. valuationRingAt v ≃+* Loc.AtPrime v.asIdeal (both are DVRs)
3. Hence the residue field bridge follows.
-/

section Cycle32Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: rr_bundle_bridge] [status: OK] [cycle: 32]
/-- For DVR Localization.AtPrime v.asIdeal, there is a canonical ring isomorphism
from R/v.asIdeal to (Localization.AtPrime v.asIdeal) / maximalIdeal.
This is IsLocalization.AtPrime.equivQuotMaximalIdeal from mathlib,
which has full surjectivity of the residue map built in. -/
noncomputable def localization_residue_equiv (v : HeightOneSpectrum R) :
    (R ⧸ v.asIdeal) ≃+*
      ((Localization.AtPrime v.asIdeal) ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  exact IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal (Localization.AtPrime v.asIdeal)

-- Candidate 2 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 32]
/-- The valuation subring (v.valuation K).valuationSubring is ring-isomorphic
to the DVR Localization.AtPrime v.asIdeal.
This connects valuationRingAt (defined as valuationSubring) to the localization.

Mathematical content: Both are the "integers at v" in K. The localization approach
constructs fractions a/s with s ∉ v. The valuation approach takes {g : v(g) ≤ 1}.
These are the same subset of K for Dedekind domains. -/
noncomputable def valuationRingAt_equiv_localization (v : HeightOneSpectrum R) :
    valuationRingAt (R := R) (K := K) v ≃+* Localization.AtPrime v.asIdeal := by
  -- Section ordering: proof depends on dvr_valuation_eq_height_one' (Cycle37)
  -- See valuationRingAt_equiv_localization' (line ~1500) for complete proof
  sorry

-- Candidate 3 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 32]
/-- Given the equivalence from Candidate 2, the residue fields are isomorphic.
Transport the residue field structure along the ring equivalence. -/
noncomputable def residueField_equiv_of_valuationRingAt_equiv (v : HeightOneSpectrum R)
    (e : valuationRingAt (R := R) (K := K) v ≃+* Localization.AtPrime v.asIdeal) :
    valuationRingAt.residueField (R := R) (K := K) v ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal) := by
  sorry

-- Candidate 4 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 32]
/-- Compose the chain:
R ⧸ v.asIdeal ≃ Loc.AtPrime / maxIdeal ≃ valuationRingAt.residueField
The first equivalence is localization_residue_equiv.
The second comes from valuationRingAt ≃ Loc.AtPrime (Candidate 2). -/
noncomputable def residueFieldBridge_via_localization (v : HeightOneSpectrum R)
    (e : valuationRingAt (R := R) (K := K) v ≃+* Localization.AtPrime v.asIdeal) :
    (R ⧸ v.asIdeal) ≃+* valuationRingAt.residueField (R := R) (K := K) v := by
  sorry

-- Candidate 5 [tag: main_proof] [status: SORRY] [cycle: 32]
/-- Once we have the equivalences, surjectivity follows immediately.
The chain R → valuationRingAt → residueField factors through:
R → Loc.AtPrime → Loc.AtPrime / maxIdeal ≃ R / v.asIdeal (inverse direction)
The mathlib equivalence equivQuotMaximalIdeal has surjectivity built in. -/
lemma residueMapFromR_surjective_via_localization (v : HeightOneSpectrum R)
    (e : valuationRingAt (R := R) (K := K) v ≃+* Localization.AtPrime v.asIdeal) :
    Function.Surjective (residueMapFromR (R := R) (K := K) v) := by
  sorry

-- Candidate 6 [tag: core_lemma] [status: SORRY] [cycle: 32]
/-- Alternative: Prove exists_same_residue_class using the fraction representation.
Every g ∈ valuationRingAt v can be written as a/b with a, b ∈ R, b ∉ v.asIdeal.
Since b ∉ v.asIdeal, v(b) = 1. Since v(g) ≤ 1, v(a) = v(g·b) ≤ 1.
Take r = a. Then embedding(a) - g = a - a/b = a(b-1)/b.
For this to be in maxIdeal, need v(a(b-1)/b) < 1. -/
lemma exists_same_residue_class_via_fractions (v : HeightOneSpectrum R)
    (g : valuationRingAt (R := R) (K := K) v) :
    ∃ r : R, (embeddingToValuationRingAt (R := R) (K := K) v r) - g ∈
      IsLocalRing.maximalIdeal (valuationRingAt (R := R) (K := K) v) := by
  sorry

-- Candidate 7 [tag: helper] [status: PROVED] [cycle: 32]
/-- The residue map from Localization.AtPrime to its residue field is surjective.
This is standard: residue is a quotient map, hence surjective.
Note: IsLocalRing.residue_surjective takes the local ring as implicit argument. -/
lemma localization_residue_surjective (v : HeightOneSpectrum R) :
    Function.Surjective
      (IsLocalRing.residue (Localization.AtPrime v.asIdeal)) :=
  IsLocalRing.residue_surjective

-- Candidate 8 [tag: helper] [status: PROVED] [cycle: 32]
/-- The residue field of Localization.AtPrime v.asIdeal is isomorphic to
the residue field at prime (R/v.asIdeal), via equivQuotMaximalIdeal
composed with the quotient-to-residueField bijection.

Note: IsLocalRing.ResidueField (Loc.AtPrime) = (Loc.AtPrime) / maxIdeal
This is DEFINITIONALLY equal to the target of localization_residue_equiv. -/
noncomputable def localization_residueField_equiv (v : HeightOneSpectrum R) :
    IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal) ≃+*
      residueFieldAtPrime R v := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  -- ResidueField (Loc.AtPrime) = (Loc.AtPrime) / maxIdeal (definitionally)
  -- localization_residue_equiv gives: R / v.asIdeal ≃ (Loc.AtPrime) / maxIdeal
  -- So symm gives: ResidueField ≃ R / v.asIdeal
  -- Then R / v.asIdeal ≃ residueFieldAtPrime via bijective_algebraMap_quotient
  have h2 : (R ⧸ v.asIdeal) ≃+* residueFieldAtPrime R v :=
    RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField v.asIdeal)
  exact (localization_residue_equiv v).symm.trans h2

end Cycle32Candidates

/-! ## Cycle 33 Candidates: Proving valuationRingAt_equiv_localization (DVR Equivalence)

CRITICAL BLOCKER: valuationRingAt_equiv_localization (line 1603 was sorry)

Strategy: Use IsDiscreteValuationRing.equivValuationSubring which gives A ≃+* ((maximalIdeal A).valuation K).valuationSubring
for DVR A. We have:
1. Localization.AtPrime v.asIdeal is a DVR (proved: localizationAtPrime_isDVR)
2. maximalIdeal (Loc.AtPrime) = v.asIdeal.map algebraMap (AtPrime.map_eq_maximalIdeal)
3. Need to show: valuations correspond appropriately
4. Then use equivValuationSubring and transport

Key mathlib lemmas:
- IsDiscreteValuationRing.equivValuationSubring : A ≃+* ((maximalIdeal A).valuation K).valuationSubring
- IsLocalization.AtPrime.map_eq_maximalIdeal : v.asIdeal.map algebraMap = maximalIdeal Rₚ
-/

section Cycle33Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: dvr_bridge] [relevance: 5] [status: OK] [cycle: 33]
/-- The maximal ideal of Localization.AtPrime v.asIdeal equals
the image of v.asIdeal under the algebraMap.
Direct application of IsLocalization.AtPrime.map_eq_maximalIdeal. -/
lemma localization_maximalIdeal_eq_map (v : HeightOneSpectrum R) :
    IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) =
      Ideal.map (algebraMap R (Localization.AtPrime v.asIdeal)) v.asIdeal := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  exact (IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal (Localization.AtPrime v.asIdeal)).symm

-- Candidate 2 [tag: dvr_bridge] [relevance: 5] [status: SORRY] [cycle: 33]
/-- Characterization of membership in valuationRingAt via fractions.
An element g ∈ K is in valuationRingAt v iff it can be written as r/s with s ∉ v.asIdeal.
This is the key connection between valuation and localization approaches. -/
lemma valuationRingAt_iff_fraction (v : HeightOneSpectrum R) (g : K) :
    g ∈ valuationRingAt (R := R) (K := K) v ↔
      ∃ (r s : R), s ∉ v.asIdeal ∧ algebraMap R K s ≠ 0 ∧ g = algebraMap R K r / algebraMap R K s := by
  sorry

-- Candidate 3 [tag: dvr_bridge] [relevance: 5] [status: PROVED] [cycle: 33]
/-- Every element of the form r/s with s ∉ v.asIdeal has valuation ≤ 1.
This connects fractions from the localization to the valuation ring. -/
lemma mk_mem_valuationRingAt (v : HeightOneSpectrum R) (r : R) {s : R} (hs : s ∉ v.asIdeal) :
    (algebraMap R K r / algebraMap R K s) ∈ valuationRingAt (R := R) (K := K) v := by
  rw [mem_valuationRingAt_iff]
  -- v(r/s) = v(r) / v(s). Since s ∉ v.asIdeal, v(s) = 1. So v(r/s) = v(r) ≤ 1.
  have hvs : v.valuation K (algebraMap R K s) = 1 := valuation_eq_one_of_not_mem v hs
  rw [Valuation.map_div, hvs, div_one]
  exact v.valuation_le_one r

-- Candidate 4 [tag: dvr_bridge] [relevance: 5] [status: SORRY] [cycle: 33]
/-- Elements of valuationRingAt can be represented as fractions r/s with s ∉ v.asIdeal.
This is the converse of Candidate 3 and completes the characterization. -/
lemma valuationRingAt_exists_fraction (v : HeightOneSpectrum R) (g : K)
    (hg : g ∈ valuationRingAt (R := R) (K := K) v) :
    ∃ (r s : R), s ∉ v.asIdeal ∧ algebraMap R K s ≠ 0 ∧ g = algebraMap R K r / algebraMap R K s := by
  -- g has valuation ≤ 1. Use IsFractionRing to write g = a/b.
  -- If b ∉ v.asIdeal, we're done with r = a, s = b.
  -- If b ∈ v.asIdeal, need to adjust...
  sorry

-- Candidate 5 [tag: dvr_bridge] [relevance: 5] [status: SORRY] [cycle: 33]
/-- MAIN GOAL: The equivalence between valuationRingAt and Localization.AtPrime.
Uses the fraction characterization to establish the set equality, then constructs the ring equiv. -/
noncomputable def valuationRingAt_equiv_localization_v3 (v : HeightOneSpectrum R) :
    valuationRingAt (R := R) (K := K) v ≃+* Localization.AtPrime v.asIdeal := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  -- Strategy: Both represent fractions r/s with s ∉ v.asIdeal
  sorry

-- Candidate 6 [tag: dvr_bridge] [relevance: 5] [status: SORRY] [cycle: 33]
/-- Transport the FractionRing version to abstract K via the canonical isomorphism. -/
noncomputable def valuationRingAt_equiv_localization_v2 (v : HeightOneSpectrum R) :
    valuationRingAt (R := R) (K := K) v ≃+* Localization.AtPrime v.asIdeal := by
  sorry

-- Candidate 7 [tag: rr_bundle_bridge] [relevance: 5] [status: SORRY] [cycle: 33]
/-- Residue field equivalence follows from the ring equivalence. -/
noncomputable def residueField_equiv_of_valuationRingAt_equiv_v2 (v : HeightOneSpectrum R)
    (e : valuationRingAt (R := R) (K := K) v ≃+* Localization.AtPrime v.asIdeal) :
    valuationRingAt.residueField (R := R) (K := K) v ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal) := by
  sorry

-- Candidate 8 [tag: main_proof] [relevance: 5] [status: SORRY] [cycle: 33]
/-- Once we have the equivalence, surjectivity of residueMapFromR follows. -/
lemma residueMapFromR_surjective_via_localization_v2 (v : HeightOneSpectrum R)
    (e : valuationRingAt (R := R) (K := K) v ≃+* Localization.AtPrime v.asIdeal) :
    Function.Surjective (residueMapFromR (R := R) (K := K) v) := by
  sorry

end Cycle33Candidates

/-! ## Cycle 34 Candidates: Valuation Equality and Converse Direction

Per Frontier Freeze Rule: Focus exclusively on the key blocker without adding new scaffolding.

KEY BLOCKER: `valuationRingAt_exists_fraction` (line 1733)

Strategy: Use arithmetic manipulation of valuations to prove the converse direction.
- If v(g) ≤ 1 and g = a/b, then v.intValuation a ≤ v.intValuation b
- If b ∈ v.asIdeal, need to factor and adjust to get coprime denominator

Key mathlib lemmas:
- `valuation_of_mk'` : v(r/s) = v.intValuation r / v.intValuation s
- `valuation_lt_one_iff_mem` : v(r) < 1 ↔ r ∈ v.asIdeal
- `intValuation_eq_one_iff` : v.intValuation x = 1 ↔ x ∉ v.asIdeal
-/

section Cycle34Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: arithmetic] [relevance: 5/5] [status: PROVED] [cycle: 34]
/-- The valuation of a fraction a/b is the quotient of intValuations.
Direct wrapper for HeightOneSpectrum.valuation_of_mk'. -/
lemma valuation_of_fraction (v : HeightOneSpectrum R) (a : R) {b : R} (hb : b ≠ 0) :
    v.valuation K (algebraMap R K a / algebraMap R K b) =
      v.intValuation a / v.intValuation b := by
  -- Use IsFractionRing.mk'_eq_div to rewrite as mk' form
  have heq : algebraMap R K a / algebraMap R K b =
      IsLocalization.mk' K a ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩ := by
    rw [IsFractionRing.mk'_eq_div]
  rw [heq, v.valuation_of_mk']

-- Candidate 2 [tag: arithmetic] [relevance: 5/5] [status: PROVED] [cycle: 34]
/-- If v(a/b) ≤ 1 for a fraction, then v.intValuation a ≤ v.intValuation b.
Key arithmetic fact for proving the converse direction. -/
lemma intValuation_le_of_div_le_one (v : HeightOneSpectrum R) (a : R) {b : R}
    (hb : b ≠ 0) (h : v.valuation K (algebraMap R K a / algebraMap R K b) ≤ 1) :
    v.intValuation a ≤ v.intValuation b := by
  rw [valuation_of_fraction v a hb] at h
  -- v.intValuation a / v.intValuation b ≤ 1 means v.intValuation a ≤ v.intValuation b
  have hvb : v.intValuation b ≠ 0 := v.intValuation_ne_zero' ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩
  have hvb_pos : 0 < v.intValuation b := zero_lt_iff.mpr hvb
  rwa [div_le_one₀ hvb_pos] at h

-- Candidate 3 [tag: arithmetic] [relevance: 5/5] [status: PROVED] [cycle: 34]
/-- If b ∉ v.asIdeal, then v.intValuation b = 1.
Restatement of intValuation_eq_one_iff. -/
lemma intValuation_eq_one_of_not_mem' (v : HeightOneSpectrum R) {b : R} (hb : b ∉ v.asIdeal) :
    v.intValuation b = 1 :=
  v.intValuation_eq_one_iff.mpr hb

-- Candidate 4 [tag: arithmetic] [relevance: 5/5] [status: PROVED] [cycle: 34]
/-- If b ∈ v.asIdeal (and b ≠ 0), then v.intValuation b < 1.
Key for detecting when the denominator needs adjustment. -/
lemma intValuation_lt_one_of_mem (v : HeightOneSpectrum R) {b : R} (hb : b ∈ v.asIdeal) (hb' : b ≠ 0) :
    v.intValuation b < 1 :=
  (v.intValuation_lt_one_iff_mem b).mpr hb

-- Candidate 5 [tag: converse] [relevance: 5/5] [status: SORRY] [cycle: 34]
/-- KEY LEMMA: If g ∈ valuationRingAt v and g = a/b with b ∈ v.asIdeal,
then we can find a "better" representation g = a'/b' with b' ∉ v.asIdeal.

The idea: In a Dedekind domain, b ∈ v.asIdeal means π | b for some uniformizer π.
If v(a/b) ≤ 1, then v(a) ≥ v(b), so π | a as well.
We can cancel the π to get a smaller representation.

This is an induction on the v-adic valuation of b. -/
lemma exists_coprime_rep (v : HeightOneSpectrum R) (g : K)
    (hg : g ∈ valuationRingAt (R := R) (K := K) v) :
    ∃ (r s : R), s ∉ v.asIdeal ∧ algebraMap R K s ≠ 0 ∧ g = algebraMap R K r / algebraMap R K s := by
  -- Get initial representation g = a/b
  obtain ⟨a, b, hb', hab⟩ := IsFractionRing.div_surjective (A := R) g
  -- hb' : b ∈ nonZeroDivisors R, so b ≠ 0
  have hb_ne : (b : R) ≠ 0 := nonZeroDivisors.ne_zero hb'
  -- By cases: either b ∉ v.asIdeal (done) or b ∈ v.asIdeal (need to adjust)
  by_cases hbv : (b : R) ∉ v.asIdeal
  · -- Easy case: b ∉ v.asIdeal, we're done
    refine ⟨a, b, hbv, ?_, hab.symm⟩
    rw [ne_eq, map_eq_zero_iff (algebraMap R K) (IsFractionRing.injective R K)]
    exact hb_ne
  · -- Hard case: b ∈ v.asIdeal
    push_neg at hbv
    -- v(g) ≤ 1 gives v.intValuation a ≤ v.intValuation b
    rw [mem_valuationRingAt_iff] at hg
    rw [← hab] at hg
    have hle := intValuation_le_of_div_le_one v a hb_ne hg
    -- Since b ∈ v.asIdeal, v.intValuation b < 1, so v.intValuation a < 1, so a ∈ v.asIdeal
    have ha_mem : a ∈ v.asIdeal := by
      by_contra ha_nmem
      have ha_val : v.intValuation a = 1 := v.intValuation_eq_one_iff.mpr ha_nmem
      have hb_val : v.intValuation b < 1 := intValuation_lt_one_of_mem v hbv hb_ne
      rw [ha_val] at hle
      exact not_lt.mpr hle hb_val
    -- Now both a, b ∈ v.asIdeal. Factor out a uniformizer...
    -- This requires DVR/uniformizer machinery - TODO prove via uniformizer cancellation
    sorry

-- Candidate 6 [tag: converse] [relevance: 5/5] [status: SORRY] [cycle: 34]
/-- Alternate approach: Use that for Dedekind domains, elements of K with v(g) ≤ 1
for a specific v can always be written in coprime form.

This is equivalent to Candidate 5 but stated more directly. -/
lemma valuationRingAt_exists_fraction_v2 (v : HeightOneSpectrum R) (g : K)
    (hg : g ∈ valuationRingAt (R := R) (K := K) v) :
    ∃ (r s : R), s ∉ v.asIdeal ∧ algebraMap R K s ≠ 0 ∧ g = algebraMap R K r / algebraMap R K s :=
  exists_coprime_rep v g hg

-- Candidates 7-8 REMOVED: localizationToFractionRing infrastructure
-- These require careful type class setup and are not essential for the main blocker.
-- The key candidates (1-6) provide arithmetic tools for proving exists_coprime_rep.

end Cycle34Candidates

/-! ## Cycle 35 Candidates: exists_lift_of_le_one Strategy

Goal: Prove `exists_coprime_rep` using DVR theory.

Strategy (Path A from Playbook):
1. Get `IsFractionRing (Localization.AtPrime v.asIdeal) K`
2. Connect v.valuation K to the DVR's maximal ideal valuation
3. Apply `IsDiscreteValuationRing.exists_lift_of_le_one`
4. Unpack the result to get coprime representation

Key mathlib lemmas:
- `IsDiscreteValuationRing.exists_lift_of_le_one`: If DVR valuation ≤ 1, element lifts to DVR
- `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`: IsFractionRing for localizations
-/

section Cycle35Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 0 [tag: instance_setup] [relevance: 5/5] [status: PROVED] [cycle: 35]
/-- Elements of primeCompl become units in the fraction field K.
This is needed to construct the algebra map Localization.AtPrime → K. -/
lemma primeCompl_isUnit_in_K (v : HeightOneSpectrum R) (y : v.asIdeal.primeCompl) :
    IsUnit (algebraMap R K y) := by
  apply IsUnit.mk0
  rw [ne_eq, map_eq_zero_iff (algebraMap R K) (IsFractionRing.injective R K)]
  exact nonZeroDivisors.ne_zero (v.asIdeal.primeCompl_le_nonZeroDivisors y.2)

-- Candidate 0b [tag: instance_setup] [relevance: 5/5] [status: PROVED] [cycle: 35]
/-- The ring homomorphism from Localization.AtPrime to the fraction field K.
Lifts the algebra map R → K via the universal property of localization. -/
noncomputable def localizationToK (v : HeightOneSpectrum R) :
    Localization.AtPrime v.asIdeal →+* K :=
  IsLocalization.lift (fun y => primeCompl_isUnit_in_K v y)

-- Candidate 0c [tag: instance_setup] [relevance: 5/5] [status: PROVED] [cycle: 35]
/-- The algebra structure on K over Localization.AtPrime v.asIdeal. -/
noncomputable instance algebraLocalizationK (v : HeightOneSpectrum R) :
    Algebra (Localization.AtPrime v.asIdeal) K :=
  RingHom.toAlgebra (localizationToK v)

-- Candidate 0d [tag: instance_setup] [relevance: 5/5] [status: PROVED] [cycle: 35]
/-- The scalar tower R → Localization.AtPrime → K. -/
instance scalarTowerLocalizationK (v : HeightOneSpectrum R) :
    IsScalarTower R (Localization.AtPrime v.asIdeal) K :=
  IsScalarTower.of_algebraMap_eq (fun x => by
    simp only [localizationToK, RingHom.algebraMap_toAlgebra]
    exact (IsLocalization.lift_eq (fun y => primeCompl_isUnit_in_K v y) x).symm)

-- Candidate 1 [tag: dvr_bridge] [relevance: 5/5] [status: PROVED] [cycle: 35]
/-- Get IsFractionRing instance for Localization.AtPrime with abstract field K.
This uses the tower R → Localization.AtPrime → K and the fact that K is
a fraction field of R. -/
noncomputable instance localization_isFractionRing (v : HeightOneSpectrum R) :
    IsFractionRing (Localization.AtPrime v.asIdeal) K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization v.asIdeal.primeCompl
    (Localization.AtPrime v.asIdeal) K

-- Candidate 2 [tag: dvr_bridge] [relevance: 5/5] [status: SORRY] [cycle: 35]
/-- Connect DVR valuation to HeightOneSpectrum valuation.
Both valuations should agree because they're defined from the same prime ideal. -/
lemma dvr_valuation_eq_height_one (v : HeightOneSpectrum R) (g : K) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K g =
      v.valuation K g := by
  sorry

-- Candidate 3 [tag: dvr_bridge] [relevance: 5/5] [status: SORRY] [cycle: 35]
/-- Apply exists_lift_of_le_one to get element in Localization.AtPrime.
Requires: IsFractionRing instance and valuation agreement. -/
lemma exists_localization_lift (v : HeightOneSpectrum R) (g : K)
    (hg : g ∈ valuationRingAt (R := R) (K := K) v) :
    ∃ y : Localization.AtPrime v.asIdeal, algebraMap (Localization.AtPrime v.asIdeal) K y = g := by
  sorry

-- Candidate 4 [tag: arithmetic] [relevance: 4/5] [status: PROVED] [cycle: 35]
/-- Unpack Localization element via IsLocalization.surj.
y * s = r in the localization when s comes from primeCompl. -/
lemma localization_surj_representation (v : HeightOneSpectrum R)
    (y : Localization.AtPrime v.asIdeal) :
    ∃ (r : R) (s : v.asIdeal.primeCompl),
      y * algebraMap R (Localization.AtPrime v.asIdeal) s = algebraMap R (Localization.AtPrime v.asIdeal) r := by
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj v.asIdeal.primeCompl y
  exact ⟨r, s, h⟩

-- Candidate 5 [tag: dvr_bridge] [relevance: 5/5] [status: SORRY] [cycle: 35]
/-- Combine lift and unpacking to prove exists_coprime_rep.
This is the main target - should follow from Candidates 3 and 4. -/
lemma exists_coprime_rep_via_lift (v : HeightOneSpectrum R) (g : K)
    (hg : g ∈ valuationRingAt (R := R) (K := K) v) :
    ∃ (r s : R), s ∉ v.asIdeal ∧ algebraMap R K s ≠ 0 ∧ g = algebraMap R K r / algebraMap R K s := by
  sorry

-- Candidate 6 [tag: arithmetic] [relevance: 4/5] [status: PROVED] [cycle: 35]
/-- Helper: primeCompl membership means not in ideal. -/
lemma primeCompl_iff_not_mem (v : HeightOneSpectrum R) (s : R) :
    s ∈ v.asIdeal.primeCompl ↔ s ∉ v.asIdeal := Iff.rfl

-- Candidate 7 [tag: arithmetic] [relevance: 4/5] [status: SORRY] [cycle: 35]
/-- Helper: algebraMap from localization mk' equals division in fraction field.
The proof is technical but mathematically clear. -/
lemma algebraMap_localization_mk'_eq_div (v : HeightOneSpectrum R) (r : R) (s : v.asIdeal.primeCompl) :
    algebraMap (Localization.AtPrime v.asIdeal) K (IsLocalization.mk' (Localization.AtPrime v.asIdeal) r s) =
      algebraMap R K r / algebraMap R K s := by
  sorry

-- Candidate 8 [tag: dvr_bridge] [relevance: 4/5] [status: SORRY] [cycle: 35]
/-- Alternative: show valuationSubrings are equal.
If proved, this gives exists_coprime_rep immediately via localization surjectivity. -/
lemma valuationSubring_eq_localization_image (v : HeightOneSpectrum R) :
    (valuationRingAt (R := R) (K := K) v : Set K) =
      Set.range (algebraMap (Localization.AtPrime v.asIdeal) K) := by
  sorry

end Cycle35Candidates

/-! ## Cycle 36 Candidates: DVR-HeightOneSpectrum Bridge

Key insight: Both v.valuation K and (maximalIdeal (Loc.AtPrime)).valuation K
are defined via HeightOneSpectrum.valuation = intValuation.extendToLocalization.
The localization's maximalIdeal is a HeightOneSpectrum with asIdeal = map v.asIdeal.

Strategy:
1. Show the two HeightOneSpectrum objects have related intValuations
2. OR prove set equality: valuationRingAt = range(algebraMap from Loc.AtPrime)
-/

section Cycle36Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: dvr_bridge] [relevance: 5/5] [status: PROVED] [cycle: 36]
/-- The local ring maximal ideal equals the mapped ideal.
This is a restatement of localization_maximalIdeal_eq_map (Cycle 33). -/
lemma localRing_maximalIdeal_eq_map' (v : HeightOneSpectrum R) :
    IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) =
      Ideal.map (algebraMap R (Localization.AtPrime v.asIdeal)) v.asIdeal :=
  localization_maximalIdeal_eq_map v

-- Candidate 2 [tag: dvr_bridge] [relevance: 5/5] [status: SORRY] [cycle: 36]
/-- The valuationRingAt equals the valuation ring of the localization DVR.
Both are DVRs in K with the same maximal ideal. -/
lemma valuationRingAt_eq_localization_valuationRing (v : HeightOneSpectrum R) :
    (valuationRingAt (R := R) (K := K) v : Set K) =
      (Valuation.valuationSubring (v.valuation K) : Set K) := by
  -- valuationRingAt IS defined as Valuation.valuationSubring
  rfl

-- Candidate 3 [tag: arithmetic] [relevance: 4/5] [status: PROVED] [cycle: 36]
/-- Technical lemma: mk' maps to division in K.
Uses IsLocalization properties and scalar tower. -/
lemma algebraMap_localization_mk'_eq_div' (v : HeightOneSpectrum R) (r : R) (s : v.asIdeal.primeCompl) :
    algebraMap (Localization.AtPrime v.asIdeal) K (IsLocalization.mk' (Localization.AtPrime v.asIdeal) r s) =
      algebraMap R K r / algebraMap R K s := by
  have hs_ne : algebraMap R K (s : R) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff (algebraMap R K) (IsFractionRing.injective R K)]
    exact nonZeroDivisors.ne_zero (v.asIdeal.primeCompl_le_nonZeroDivisors s.property)
  rw [eq_div_iff hs_ne]
  have h := IsLocalization.mk'_spec (Localization.AtPrime v.asIdeal) r s
  -- h : mk' r s * algebraMap R _ s = algebraMap R _ r
  calc algebraMap (Localization.AtPrime v.asIdeal) K
        (IsLocalization.mk' (Localization.AtPrime v.asIdeal) r s) * algebraMap R K s
      = algebraMap (Localization.AtPrime v.asIdeal) K
          (IsLocalization.mk' (Localization.AtPrime v.asIdeal) r s) *
          algebraMap (Localization.AtPrime v.asIdeal) K (algebraMap R _ s) := by
          rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal) K]
    _ = algebraMap (Localization.AtPrime v.asIdeal) K
          (IsLocalization.mk' (Localization.AtPrime v.asIdeal) r s * algebraMap R _ s) := by
          rw [map_mul]
    _ = algebraMap (Localization.AtPrime v.asIdeal) K (algebraMap R _ r) := by rw [h]
    _ = algebraMap R K r := by rw [← IsScalarTower.algebraMap_apply]

-- Candidate 4 [tag: rewrite_bridge] [relevance: 3/5] [status: PROVED] [cycle: 36]
/-- Helper: Explicit form of HeightOneSpectrum.valuation definition. -/
lemma valuation_eq_intValuation_extendToLocalization (v : HeightOneSpectrum R) :
    v.valuation K = v.intValuation.extendToLocalization
      (fun r hr => Set.mem_compl (v.intValuation_ne_zero' ⟨r, hr⟩)) K := rfl

-- Candidate 5 [tag: dvr_bridge] [relevance: 5/5] [status: PROVED] [cycle: 36]
/-- The range of algebraMap from localization is contained in valuationRingAt.
Uses mk_mem_valuationRingAt on each fraction. -/
lemma range_algebraMap_subset_valuationRingAt (v : HeightOneSpectrum R) :
    Set.range (algebraMap (Localization.AtPrime v.asIdeal) K) ⊆
      (valuationRingAt (R := R) (K := K) v : Set K) := by
  intro g ⟨y, hy⟩
  subst hy
  -- y is in Localization.AtPrime, write it as mk' r s
  obtain ⟨⟨r, s⟩, heq⟩ := IsLocalization.surj v.asIdeal.primeCompl y
  -- heq : y * algebraMap R _ s = algebraMap R _ r
  have hs : (s : R) ∉ v.asIdeal := s.property
  -- Show algebraMap _ K y = algebraMap R K r / algebraMap R K s
  have hy_eq : algebraMap (Localization.AtPrime v.asIdeal) K y = algebraMap R K r / algebraMap R K s := by
    have hs_ne : algebraMap R K (s : R) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff (algebraMap R K) (IsFractionRing.injective R K)]
      exact nonZeroDivisors.ne_zero (v.asIdeal.primeCompl_le_nonZeroDivisors s.property)
    rw [eq_div_iff hs_ne]
    calc algebraMap (Localization.AtPrime v.asIdeal) K y * algebraMap R K s
        = algebraMap (Localization.AtPrime v.asIdeal) K y *
            algebraMap (Localization.AtPrime v.asIdeal) K (algebraMap R _ s) := by
            rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal) K]
      _ = algebraMap (Localization.AtPrime v.asIdeal) K (y * algebraMap R _ s) := by rw [map_mul]
      _ = algebraMap (Localization.AtPrime v.asIdeal) K (algebraMap R _ r) := by rw [heq]
      _ = algebraMap R K r := by rw [← IsScalarTower.algebraMap_apply]
  -- Now use mk_mem_valuationRingAt
  rw [hy_eq]
  exact mk_mem_valuationRingAt v r hs

-- Candidate 6 [tag: dvr_bridge] [relevance: 5/5] [status: SORRY] [cycle: 36]
/-- The valuationRingAt is contained in range of algebraMap from localization.
This is the hard direction - proves that elements with v(g) ≤ 1 come from localization. -/
lemma valuationRingAt_subset_range_algebraMap (v : HeightOneSpectrum R) :
    (valuationRingAt (R := R) (K := K) v : Set K) ⊆
      Set.range (algebraMap (Localization.AtPrime v.asIdeal) K) := by
  intro g hg
  simp only [SetLike.mem_coe, ValuationSubring.mem_toSubring] at hg
  rw [mem_valuationRingAt_iff] at hg
  -- Need to show g is in range of algebraMap from localization
  -- This should follow from DVR structure + IsFractionRing
  sorry

-- Candidate 7 [tag: dvr_bridge] [relevance: 5/5] [status: SORRY] [cycle: 36]
/-- Set equality via subset in both directions. -/
lemma valuationSubring_eq_localization_image' (v : HeightOneSpectrum R) :
    (valuationRingAt (R := R) (K := K) v : Set K) =
      Set.range (algebraMap (Localization.AtPrime v.asIdeal) K) := by
  apply Set.eq_of_subset_of_subset
  · exact valuationRingAt_subset_range_algebraMap v
  · exact range_algebraMap_subset_valuationRingAt v

-- Candidate 8 [tag: dvr_bridge] [relevance: 4/5] [status: SORRY] [cycle: 36]
/-- Once we have lift, unpack via IsLocalization.mk' to get coprime representation. -/
lemma exists_coprime_rep_via_set_eq (v : HeightOneSpectrum R) (g : K)
    (hg : g ∈ valuationRingAt (R := R) (K := K) v) :
    ∃ (r s : R), s ∉ v.asIdeal ∧ algebraMap R K s ≠ 0 ∧ g = algebraMap R K r / algebraMap R K s := by
  -- Use set equality to get y in localization with algebraMap y = g
  have heq := valuationSubring_eq_localization_image' (R := R) (K := K) v
  have hg' : g ∈ (valuationRingAt (R := R) (K := K) v : Set K) := hg
  rw [heq] at hg'
  obtain ⟨y, hy⟩ := hg'
  -- Unpack y via IsLocalization.surj
  obtain ⟨⟨r, s⟩, hys⟩ := IsLocalization.surj v.asIdeal.primeCompl y
  use r, s, s.property
  constructor
  · rw [ne_eq, map_eq_zero_iff (algebraMap R K) (IsFractionRing.injective R K)]
    exact nonZeroDivisors.ne_zero (v.asIdeal.primeCompl_le_nonZeroDivisors s.property)
  · rw [← hy]
    have hs_ne : algebraMap R K (s : R) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff (algebraMap R K) (IsFractionRing.injective R K)]
      exact nonZeroDivisors.ne_zero (v.asIdeal.primeCompl_le_nonZeroDivisors s.property)
    rw [eq_div_iff hs_ne]
    calc algebraMap (Localization.AtPrime v.asIdeal) K y * algebraMap R K s
        = algebraMap (Localization.AtPrime v.asIdeal) K y *
            algebraMap (Localization.AtPrime v.asIdeal) K (algebraMap R _ s) := by
            rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal) K]
      _ = algebraMap (Localization.AtPrime v.asIdeal) K (y * algebraMap R _ s) := by rw [map_mul]
      _ = algebraMap (Localization.AtPrime v.asIdeal) K (algebraMap R _ r) := by rw [hys]
      _ = algebraMap R K r := by rw [← IsScalarTower.algebraMap_apply]

end Cycle36Candidates

/-! ## Cycle 49: Prerequisites for dvr_valuation_eq_height_one'

This section consolidates the lemmas needed to prove dvr_valuation_eq_height_one' in Cycle37.
These were originally developed in Cycles 41, 44, 46, and 47, but need to be ordered before Cycle37.

Dependency chain:
1. Foundation lemmas (from Cycle 41)
2. Ideal power membership bridge (from Cycle 44)
3. intValuation bridge (from Cycles 46-47)
4. → enables dvr_valuation_eq_height_one' proof in Cycle37
-/

section Cycle49Prerequisites

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- ============================================================================
-- Part 1: Foundation Lemmas (from Cycle 41)
-- ============================================================================

/-- Elements not in v.asIdeal are exactly those whose image under algebraMap is a unit. -/
lemma algebraMap_isUnit_iff_not_mem_c49 (v : HeightOneSpectrum R) (r : R) :
    IsUnit (algebraMap R (Localization.AtPrime v.asIdeal) r) ↔ r ∉ v.asIdeal := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime v.asIdeal) v.asIdeal r]
  rfl

/-- Units in a DVR have intValuation equal to 1. -/
lemma dvr_intValuation_of_isUnit_c49 (v : HeightOneSpectrum R) (x : Localization.AtPrime v.asIdeal)
    (hx : IsUnit x) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation x = 1 := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  have hx' : x ∉ IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) :=
    IsLocalRing.notMem_maximalIdeal.mpr hx
  rw [HeightOneSpectrum.intValuation_eq_one_iff]
  exact hx'

/-- The asIdeal of DVR.maximalIdeal equals IsLocalRing.maximalIdeal. -/
lemma dvr_maximalIdeal_asIdeal_eq_localRing_maximalIdeal_c49 (v : HeightOneSpectrum R) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).asIdeal =
      IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  rfl

-- ============================================================================
-- Part 2: Ideal Power Membership Bridge (from Cycle 44)
-- ============================================================================

/-- Ideal.map commutes with powers. -/
lemma ideal_map_pow_eq_pow_map_c49 (v : HeightOneSpectrum R) (n : ℕ) :
    Ideal.map (algebraMap R (Localization.AtPrime v.asIdeal)) (v.asIdeal ^ n) =
      (Ideal.map (algebraMap R (Localization.AtPrime v.asIdeal)) v.asIdeal) ^ n :=
  Ideal.map_pow (algebraMap R (Localization.AtPrime v.asIdeal)) v.asIdeal n

/-- MaxIdeal^n = map(v.asIdeal^n). -/
lemma maxIdeal_pow_eq_map_asIdeal_pow_c49 (v : HeightOneSpectrum R) (n : ℕ) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) ^ n =
      Ideal.map (algebraMap R (Localization.AtPrime v.asIdeal)) (v.asIdeal ^ n) := by
  rw [localization_maximalIdeal_eq_map v, ideal_map_pow_eq_pow_map_c49 v n]

/-- Forward direction: r ∈ v.asIdeal^n → algebraMap r ∈ maxIdeal^n. -/
lemma algebraMap_mem_maxIdeal_pow_of_mem_asIdeal_pow_c49 (v : HeightOneSpectrum R) (r : R) (n : ℕ)
    (hr : r ∈ v.asIdeal ^ n) :
    algebraMap R (Localization.AtPrime v.asIdeal) r ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) ^ n := by
  rw [maxIdeal_pow_eq_map_asIdeal_pow_c49 v n]
  exact Ideal.mem_map_of_mem _ hr

/-- Coprimality in Dedekind domain: m ∉ p, m * r ∈ p^n → r ∈ p^n. -/
lemma mem_pow_of_mul_mem_pow_of_not_mem_c49 (v : HeightOneSpectrum R) (m r : R)
    (hm : m ∉ v.asIdeal) (n : ℕ) (hmr : m * r ∈ v.asIdeal ^ n) :
    r ∈ v.asIdeal ^ n := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  exact (Ideal.IsPrime.mul_mem_pow v.asIdeal hmr).resolve_left hm

/-- Backward direction: algebraMap r ∈ maxIdeal^n → r ∈ v.asIdeal^n. -/
lemma mem_asIdeal_pow_of_algebraMap_mem_maxIdeal_pow_c49 (v : HeightOneSpectrum R) (r : R) (n : ℕ)
    (hr : algebraMap R (Localization.AtPrime v.asIdeal) r ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) ^ n) :
    r ∈ v.asIdeal ^ n := by
  rw [maxIdeal_pow_eq_map_asIdeal_pow_c49 v n] at hr
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff v.asIdeal.primeCompl] at hr
  obtain ⟨m, hm, hmr⟩ := hr
  have hm' : m ∉ v.asIdeal := hm
  exact mem_pow_of_mul_mem_pow_of_not_mem_c49 v m r hm' n hmr

/-- Complete characterization: r ∈ v.asIdeal^n ↔ algebraMap r ∈ maxIdeal^n. -/
lemma mem_asIdeal_pow_iff_mem_maxIdeal_pow_c49 (v : HeightOneSpectrum R) (r : R) (n : ℕ) :
    r ∈ v.asIdeal ^ n ↔
      algebraMap R (Localization.AtPrime v.asIdeal) r ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) ^ n :=
  ⟨algebraMap_mem_maxIdeal_pow_of_mem_asIdeal_pow_c49 v r n,
   mem_asIdeal_pow_of_algebraMap_mem_maxIdeal_pow_c49 v r n⟩

-- ============================================================================
-- Part 3: intValuation Bridge (from Cycles 46-47)
-- ============================================================================

/-- DVR intValuation equals HeightOneSpectrum.intValuation for r ∈ R (via ideal powers). -/
lemma dvr_intValuation_eq_via_pow_membership_c49 (v : HeightOneSpectrum R) (r : R) (hr_ne : r ≠ 0) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation
      (algebraMap R (Localization.AtPrime v.asIdeal) r) = v.intValuation r := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  let dvrMax := IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)
  have hbridge : ∀ n : ℕ, dvrMax.intValuation (algebraMap R _ r) ≤ WithZero.exp (-(n : ℤ)) ↔
      v.intValuation r ≤ WithZero.exp (-(n : ℤ)) := fun n => by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    rw [dvr_maximalIdeal_asIdeal_eq_localRing_maximalIdeal_c49 v]
    exact (mem_asIdeal_pow_iff_mem_maxIdeal_pow_c49 v r n).symm
  have hr' : algebraMap R (Localization.AtPrime v.asIdeal) r ≠ 0 := by
    intro h
    apply hr_ne
    have hpc : v.asIdeal.primeCompl ≤ nonZeroDivisors R := v.asIdeal.primeCompl_le_nonZeroDivisors
    exact (IsLocalization.to_map_eq_zero_iff (Localization.AtPrime v.asIdeal) hpc).mp h
  classical
  apply le_antisymm
  · have hk : v.intValuation r = WithZero.exp
        (-(((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors) : ℤ)) :=
      v.intValuation_if_neg hr_ne
    let k := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors
    calc dvrMax.intValuation (algebraMap R (Localization.AtPrime v.asIdeal) r)
        ≤ WithZero.exp (-(k : ℤ)) := (hbridge k).mpr (le_of_eq hk)
      _ = v.intValuation r := hk.symm
  · have hm : dvrMax.intValuation (algebraMap R (Localization.AtPrime v.asIdeal) r) = WithZero.exp
        (-(((Associates.mk dvrMax.asIdeal).count (Associates.mk (Ideal.span {algebraMap R _ r})).factors) : ℤ)) :=
      dvrMax.intValuation_if_neg hr'
    let m := (Associates.mk dvrMax.asIdeal).count (Associates.mk (Ideal.span {algebraMap R _ r})).factors
    calc v.intValuation r
        ≤ WithZero.exp (-(m : ℤ)) := (hbridge m).mp (le_of_eq hm)
      _ = dvrMax.intValuation (algebraMap R (Localization.AtPrime v.asIdeal) r) := hm.symm

/-- Direct proof of DVR intValuation agreement for elements of R. KEY LEMMA. -/
lemma dvr_intValuation_of_algebraMap_c49 (v : HeightOneSpectrum R) (r : R) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation
      (algebraMap R (Localization.AtPrime v.asIdeal) r) = v.intValuation r := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  by_cases hr0 : r = 0
  · simp only [hr0, map_zero]
  by_cases hr : r ∈ v.asIdeal
  · exact dvr_intValuation_eq_via_pow_membership_c49 v r hr0
  · have hunit := (algebraMap_isUnit_iff_not_mem_c49 v r).mpr hr
    rw [dvr_intValuation_of_isUnit_c49 v _ hunit]
    symm
    rw [HeightOneSpectrum.intValuation_eq_one_iff]
    exact hr

end Cycle49Prerequisites

/-! ## Cycle 37 Candidates: Proving valuationRingAt_subset_range_algebraMap

KEY BLOCKER: `valuationRingAt_subset_range_algebraMap` (line 2099)

Strategy: Use the DVR structure of Localization.AtPrime v.asIdeal
1. Show DVR valuation equals HeightOneSpectrum valuation
2. Apply `IsDiscreteValuationRing.exists_lift_of_le_one` to get lift
3. Use `IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring` for set equality

Key mathlib lemmas:
- `IsDiscreteValuationRing.exists_lift_of_le_one`: v(x) ≤ 1 → ∃ a : A, algebraMap A K a = x
- `IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring`: range(algebraMap A K) = valuationSubring
-/

section Cycle37Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: dvr_bridge] [relevance: 5/5] [status: SORRY] [cycle: 37]
/-- The DVR maximal ideal (as HeightOneSpectrum) equals the original HeightOneSpectrum.
This relates the DVR maximalIdeal to v.asIdeal. -/
lemma dvr_maximalIdeal_asIdeal_eq (v : HeightOneSpectrum R) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).asIdeal =
      IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) := by
  rfl

-- Candidate 2 [tag: dvr_bridge] [relevance: 5/5] [status: PROVED] [cycle: 37→49]
/-- The DVR maximal ideal valuation equals the HeightOneSpectrum valuation.
This is the critical bridge lemma. Both valuations are defined from the same prime ideal.
PROVED in Cycle 49 via section reordering (Cycle49Prerequisites enables access to
dvr_intValuation_of_algebraMap_c49). -/
lemma dvr_valuation_eq_height_one' (v : HeightOneSpectrum R) (g : K) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K g =
      v.valuation K g := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- Write g as r/s for r, s ∈ R with s ∈ nonZeroDivisors
  obtain ⟨r, s, hs, hg⟩ := IsFractionRing.div_surjective (A := R) g
  rw [← hg]
  -- RHS: Use valuation_of_fraction
  rw [valuation_of_fraction v r (nonZeroDivisors.ne_zero hs)]
  -- LHS: Use Valuation.map_div and the scalar tower
  let dvr_spec := IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)
  rw [Valuation.map_div (dvr_spec.valuation K)]
  -- Rewrite algebraMap R K = algebraMap (Loc.AtPrime) K ∘ algebraMap R (Loc.AtPrime)
  have hr_eq : algebraMap R K r = algebraMap (Localization.AtPrime v.asIdeal) K
      (algebraMap R (Localization.AtPrime v.asIdeal) r) :=
    IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal) K r
  have hs_eq : algebraMap R K (s : R) = algebraMap (Localization.AtPrime v.asIdeal) K
      (algebraMap R (Localization.AtPrime v.asIdeal) (s : R)) :=
    IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal) K (s : R)
  rw [hr_eq, hs_eq]
  -- Apply dvr_spec.valuation_of_algebraMap to reduce to intValuation
  rw [dvr_spec.valuation_of_algebraMap, dvr_spec.valuation_of_algebraMap]
  -- Apply dvr_intValuation_of_algebraMap_c49 twice (KEY STEP - enabled by Cycle49Prerequisites)
  rw [dvr_intValuation_of_algebraMap_c49 v r, dvr_intValuation_of_algebraMap_c49 v (s : R)]

-- Candidate 3 [tag: dvr_bridge] [relevance: 5/5] [status: SORRY] [cycle: 37]
/-- Apply IsDiscreteValuationRing.exists_lift_of_le_one with DVR valuation equality.
If v(g) ≤ 1, then g lifts to an element of the localization. -/
lemma exists_lift_from_dvr_valuation (v : HeightOneSpectrum R) (g : K)
    (hg : v.valuation K g ≤ 1) :
    ∃ y : Localization.AtPrime v.asIdeal, algebraMap (Localization.AtPrime v.asIdeal) K y = g := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- Rewrite hg using DVR valuation equality, then apply exists_lift_of_le_one
  have hg' : (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K g ≤ 1 := by
    rw [dvr_valuation_eq_height_one' v g]
    exact hg
  exact IsDiscreteValuationRing.exists_lift_of_le_one hg'

-- Candidate 4 [tag: dvr_bridge] [relevance: 5/5] [status: PROVED] [cycle: 37→41]
/-- The valuationSubring of a DVR equals the range of algebraMap from DVR to its fraction field.
Uses IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring. -/
lemma dvr_valuationSubring_eq_range (v : HeightOneSpectrum R) :
    Set.range (algebraMap (Localization.AtPrime v.asIdeal) K) =
      (((IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K).valuationSubring : Set K) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- map_algebraMap_eq_valuationSubring gives: Subring.map (algebraMap A K) ⊤ = valuationSubring.toSubring
  have h := IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
    (A := Localization.AtPrime v.asIdeal) (K := K)
  -- Convert from Subring equality to Set equality
  have hset : (Subring.map (algebraMap (Localization.AtPrime v.asIdeal) K) ⊤ : Set K) =
      (((IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K).valuationSubring : Set K) := by
    rw [h]
    rfl
  -- Subring.map ... ⊤ is the same as Set.range
  simp only [Subring.coe_map, Subring.coe_top] at hset
  rw [Set.image_univ] at hset
  exact hset

-- Candidate 5 [tag: valuation_bridge] [relevance: 5/5] [status: SORRY] [cycle: 37]
/-- The DVR's valuationSubring equals valuationRingAt v.
This combines valuation equality with the definition of valuationRingAt. -/
lemma dvr_valuationSubring_eq_valuationRingAt (v : HeightOneSpectrum R) :
    (((IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K).valuationSubring : Set K) =
      (valuationRingAt (R := R) (K := K) v : Set K) := by
  -- Both are {g : K | valuation g ≤ 1}, and valuations agree by dvr_valuation_eq_height_one'
  ext g
  simp only [SetLike.mem_coe, Valuation.mem_valuationSubring_iff, mem_valuationRingAt_iff]
  rw [dvr_valuation_eq_height_one' (K := K) v g]

-- Candidate 6 [tag: dvr_bridge] [relevance: 5/5] [status: SORRY] [cycle: 37]
/-- Prove valuationRingAt_subset_range_algebraMap using set transitivity.
Combines Candidates 4 and 5 to get the desired inclusion. -/
lemma valuationRingAt_subset_range_algebraMap' (v : HeightOneSpectrum R) :
    (valuationRingAt (R := R) (K := K) v : Set K) ⊆
      Set.range (algebraMap (Localization.AtPrime v.asIdeal) K) := by
  -- Chain: valuationRingAt = DVR.valuationSubring = range(algebraMap)
  rw [← dvr_valuationSubring_eq_valuationRingAt (K := K) v]
  rw [← dvr_valuationSubring_eq_range (K := K) v]

-- Candidate 7 [tag: valuation_bridge] [relevance: 4/5] [status: SORRY] [cycle: 37]
/-- Alternative proof via exists_lift_from_dvr_valuation directly.
Given g with v(g) ≤ 1, construct the lift explicitly. -/
lemma valuationRingAt_mem_implies_range (v : HeightOneSpectrum R) (g : K)
    (hg : g ∈ valuationRingAt (R := R) (K := K) v) :
    g ∈ Set.range (algebraMap (Localization.AtPrime v.asIdeal) K) := by
  rw [mem_valuationRingAt_iff] at hg
  obtain ⟨y, hy⟩ := exists_lift_from_dvr_valuation (K := K) v g hg
  exact ⟨y, hy⟩

-- Candidate 8 [tag: rewrite_bridge] [relevance: 4/5] [status: SORRY] [cycle: 37]
/-- Complete the set equality for valuationSubring once we have converse. -/
lemma valuationSubring_eq_localization_image_complete (v : HeightOneSpectrum R) :
    (valuationRingAt (R := R) (K := K) v : Set K) =
      Set.range (algebraMap (Localization.AtPrime v.asIdeal) K) := by
  apply Set.eq_of_subset_of_subset
  · exact valuationRingAt_subset_range_algebraMap' (K := K) v
  · exact range_algebraMap_subset_valuationRingAt (K := K) v

-- Candidate 9 [tag: dvr_bridge] [relevance: 5/5] [status: PROVED] [cycle: 50]
/-- Prove valuationSubrings are equal as ValuationSubrings (not just as sets).
Uses ext with the proved valuation equality dvr_valuation_eq_height_one'. -/
lemma dvr_valuationSubring_eq_valuationRingAt' (v : HeightOneSpectrum R) :
    ((IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K).valuationSubring =
      valuationRingAt (R := R) (K := K) v := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  ext g
  rw [Valuation.mem_valuationSubring_iff, mem_valuationRingAt_iff]
  rw [dvr_valuation_eq_height_one' v g]

-- Candidate 10 [tag: dvr_bridge] [relevance: 5/5] [status: PROVED] [cycle: 50]
/-- The ring equivalence between valuationRingAt and Localization.AtPrime.
Uses equivValuationSubring.symm composed with the ValuationSubring equality. -/
noncomputable def valuationRingAt_equiv_localization' (v : HeightOneSpectrum R) :
    valuationRingAt (R := R) (K := K) v ≃+* Localization.AtPrime v.asIdeal := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- First, show valuationRingAt = DVR.valuationSubring
  have h : valuationRingAt (R := R) (K := K) v =
      ((IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K).valuationSubring :=
    (dvr_valuationSubring_eq_valuationRingAt' v).symm
  -- Use cast along this equality, then apply equivValuationSubring.symm
  exact (h ▸ IsDiscreteValuationRing.equivValuationSubring.symm :
    valuationRingAt (R := R) (K := K) v ≃+* Localization.AtPrime v.asIdeal)

end Cycle37Candidates

/-! ## Cycle 38 Candidates: Prove dvr_valuation_eq_height_one'

The key blocker is proving that the DVR valuation equals the HeightOneSpectrum valuation.
Both are extensions of intValuation from different rings to K.

**Key insight**: Both valuations measure divisibility by v.asIdeal.
The maximal ideal of Loc.AtPrime v.asIdeal is exactly Ideal.map v.asIdeal.
-/

section Cycle38Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: dvr_bridge] [relevance: 5/5] [status: TBD] [cycle: 38]
/-- The maximal ideal of Localization.AtPrime v.asIdeal, as a HeightOneSpectrum,
has asIdeal = IsLocalRing.maximalIdeal. This is trivial by definition. -/
lemma dvr_maximalIdeal_asIdeal_eq' (v : HeightOneSpectrum R) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).asIdeal =
      IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) := rfl

-- Candidate 2 [tag: rewrite_bridge] [relevance: 5/5] [status: TBD] [cycle: 38]
/-- For elements in R, both valuations agree after coercion to K.
This is a special case but foundational for the general proof. -/
lemma dvr_valuation_eq_on_R (v : HeightOneSpectrum R) (r : R) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K
      (algebraMap R K r) = v.valuation K (algebraMap R K r) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- Both sides should reduce to intValuation r
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  -- Need to show DVR valuation on algebraMap R K r equals v.intValuation r
  -- The algebra map R → K factors through Loc.AtPrime → K
  have hcomp : algebraMap R K r = algebraMap (Localization.AtPrime v.asIdeal) K
      (algebraMap R (Localization.AtPrime v.asIdeal) r) := by
    simp only [← IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal) K]
  rw [hcomp]
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  -- Now we need: DVR.intValuation (algebraMap R Loc r) = v.intValuation r
  sorry

-- Candidate 3 [tag: dvr_bridge] [relevance: 5/5] [status: TBD] [cycle: 38]
/-- The DVR's intValuation on algebraMap R (Loc.AtPrime) r equals v.intValuation r.
This is the key bridge connecting the two intValuations. -/
lemma dvr_intValuation_of_algebraMap (v : HeightOneSpectrum R) (r : R) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation
      (algebraMap R (Localization.AtPrime v.asIdeal) r) = v.intValuation r := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  -- intValuation is defined via ideal membership
  -- Both measure: how many times does the prime divide r?
  -- For the DVR, the maximal ideal = map v.asIdeal
  sorry

-- Candidate 4 [tag: rewrite_bridge] [relevance: 5/5] [status: TBD] [cycle: 38]
/-- Alternative proof via scalar tower: for y in Loc.AtPrime, valuations agree.
Combined with IsFractionRing surjectivity, this gives the result. -/
lemma dvr_valuation_via_scalar_tower (v : HeightOneSpectrum R) (y : Localization.AtPrime v.asIdeal) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K
      (algebraMap (Localization.AtPrime v.asIdeal) K y) =
    v.valuation K (algebraMap (Localization.AtPrime v.asIdeal) K y) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- Write y as mk' r s for r : R, s : primeCompl
  obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj v.asIdeal.primeCompl y
  -- hy : algebraMap R _ r = y * algebraMap R _ s
  sorry

-- Candidate 5 [tag: dvr_bridge] [relevance: 5/5] [status: TBD] [cycle: 38]
/-- Show valuations are equivalent via IsEquiv. If they agree on < relation, they're equiv.
Then we can potentially derive equality. -/
lemma dvr_valuation_isEquiv_height_one (v : HeightOneSpectrum R) :
    Valuation.IsEquiv
      ((IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K)
      (v.valuation K) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- IsEquiv means: ∀ x y, v1 x ≤ v1 y ↔ v2 x ≤ v2 y
  intro x y
  sorry

-- Candidate 6 [tag: rewrite_bridge] [relevance: 4/5] [status: TBD] [cycle: 38]
/-- Use the fact that valuations on fields are determined by their valuationSubring.
If valuationSubrings are equal, valuations are equal. -/
lemma dvr_valuationSubring_eq (v : HeightOneSpectrum R) :
    ((IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K).valuationSubring =
    (v.valuation K).valuationSubring := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  ext g
  simp only [Valuation.mem_valuationSubring_iff]
  -- Both say: g is in the subring iff valuation ≤ 1
  -- We already know valuationRingAt v = range(algebraMap Loc K) = DVR valuationSubring
  -- by the Cycle 37 lemmas (conditional on dvr_valuation_eq_height_one')
  sorry

-- Candidate 7 [tag: dvr_bridge] [relevance: 5/5] [status: TBD] [cycle: 38]
/-- Direct approach: use valuation_of_mk' on both sides to reduce to intValuation comparison. -/
lemma dvr_valuation_eq_height_one'_via_mk (v : HeightOneSpectrum R) (g : K) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K g =
      v.valuation K g := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- Write g as r/s for r : R, s : nonZeroDivisors R
  obtain ⟨r, s, hs, hg⟩ := IsFractionRing.div_surjective (A := R) g
  -- The RHS via valuation_of_mk': v.intValuation r / v.intValuation s
  -- For LHS, need to decompose through the scalar tower R → Loc.AtPrime → K
  -- Both measure divisibility by v.asIdeal, so should be equal
  sorry

-- Candidate 8 [tag: rewrite_bridge] [relevance: 4/5] [status: TBD] [cycle: 38]
/-- The intValuation of DVR on Loc.AtPrime elements is determined by the v.intValuation
applied to numerator/denominator of mk' representation. -/
lemma dvr_intValuation_of_mk' (v : HeightOneSpectrum R) (r : R) (s : v.asIdeal.primeCompl) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation
      (IsLocalization.mk' (Localization.AtPrime v.asIdeal) r s) =
    v.intValuation r / v.intValuation s := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  -- The DVR intValuation measures membership in powers of the maximal ideal
  -- The maximal ideal of Loc.AtPrime = Ideal.map v.asIdeal
  -- So we measure: how many times does (map v.asIdeal) divide mk' r s?
  -- This should equal: (how many times v.asIdeal divides r) - (how many times v.asIdeal divides s)
  -- But s ∈ primeCompl means s ∉ v.asIdeal, so v.intValuation s = 1
  have hs : v.intValuation s = 1 := by
    rw [HeightOneSpectrum.intValuation_eq_one_iff]
    exact s.property
  rw [hs, div_one]
  sorry

end Cycle38Candidates

/-! ## Cycle 41 Candidates: Foundation Lemmas for intValuation Bridge

Focus: Prove `mem_asIdeal_iff_mem_maxIdeal` and `dvr_intValuation_unit` via:
- Ideal membership preservation under localization
- Unit characterization in DVRs
- Key mathlib lemmas: `IsLocalization.AtPrime.isUnit_to_map_iff`, `intValuation_eq_one_iff`
-/
section Cycle41Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: dvr_bridge] [relevance: 5/5] [status: PROVED] [cycle: 41]
/-- Reverse direction of ideal membership under localization map.
If algebraMap r ∈ Ideal.map I, then r ∈ I (injectivity property). -/
lemma mem_of_algebraMap_mem_map (v : HeightOneSpectrum R) (r : R)
    (h : algebraMap R (Localization.AtPrime v.asIdeal) r ∈
         Ideal.map (algebraMap R (Localization.AtPrime v.asIdeal)) v.asIdeal) :
    r ∈ v.asIdeal := by
  -- For localization at a prime, comap (map I) = I when I is prime and disjoint from the submonoid
  have hcomap := IsLocalization.comap_map_of_isPrime_disjoint
    (M := v.asIdeal.primeCompl)
    (S := Localization.AtPrime v.asIdeal)
    v.asIdeal v.isPrime
    (Set.disjoint_left.mpr fun x hx ↦ hx)
  -- r ∈ comap (map I) = I
  rw [← hcomap]
  exact Ideal.mem_comap.mpr h

-- Candidate 2 [tag: rewrite_bridge] [relevance: 5/5] [status: PROVED] [cycle: 41]
/-- Elements not in v.asIdeal are exactly those whose image under algebraMap is a unit.
Uses IsLocalization.AtPrime.isUnit_to_map_iff. -/
lemma algebraMap_isUnit_iff_not_mem (v : HeightOneSpectrum R) (r : R) :
    IsUnit (algebraMap R (Localization.AtPrime v.asIdeal) r) ↔ r ∉ v.asIdeal := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime v.asIdeal) v.asIdeal r]
  rfl

-- Candidate 3 [tag: arithmetic] [relevance: 5/5] [status: PROVED] [cycle: 41]
/-- Units in a DVR have intValuation equal to 1.
This is a fundamental property of discrete valuation rings. -/
lemma dvr_intValuation_of_isUnit (v : HeightOneSpectrum R) (x : Localization.AtPrime v.asIdeal)
    (hx : IsUnit x) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation x = 1 := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  -- Chain: IsUnit x → x ∉ maxIdeal → intVal x = 1
  -- Step 1: IsUnit x ↔ x ∉ maxIdeal (IsLocalRing.notMem_maximalIdeal)
  have hx' : x ∉ IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) :=
    IsLocalRing.notMem_maximalIdeal.mpr hx
  -- Step 2: intVal = 1 ↔ x ∉ asIdeal (HeightOneSpectrum.intValuation_eq_one_iff)
  -- Step 3: DVR.maximalIdeal.asIdeal = IsLocalRing.maximalIdeal by rfl
  rw [HeightOneSpectrum.intValuation_eq_one_iff]
  exact hx'

-- Candidate 4 [tag: dvr_bridge] [relevance: 4/5] [status: PROVED] [cycle: 41]
/-- Non-membership in maximal ideal characterizes units in a local ring.
In a local ring, x ∉ maxIdeal ↔ IsUnit x. -/
lemma localRing_not_mem_maxIdeal_iff_isUnit (v : HeightOneSpectrum R)
    (x : Localization.AtPrime v.asIdeal) :
    x ∉ IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) ↔ IsUnit x :=
  IsLocalRing.notMem_maximalIdeal

-- Candidate 5 [tag: coercion_simplify] [relevance: 3/5] [status: PROVED] [cycle: 41]
/-- Ideal.mem_map_of_mem applied to localization: forward direction.
This is the easy direction from mathlib. -/
lemma algebraMap_mem_map_of_mem (v : HeightOneSpectrum R) (r : R) (hr : r ∈ v.asIdeal) :
    algebraMap R (Localization.AtPrime v.asIdeal) r ∈
      Ideal.map (algebraMap R (Localization.AtPrime v.asIdeal)) v.asIdeal :=
  Ideal.mem_map_of_mem _ hr

-- Candidate 6 [tag: rewrite_bridge] [relevance: 5/5] [status: PROVED] [cycle: 41]
/-- Composition: r ∉ v.asIdeal implies algebraMap r ∉ maxIdeal.
Combines localization_maximalIdeal_eq_map with membership. -/
lemma algebraMap_not_mem_maxIdeal_of_not_mem (v : HeightOneSpectrum R) (r : R)
    (hr : r ∉ v.asIdeal) :
    algebraMap R (Localization.AtPrime v.asIdeal) r ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) := by
  rw [localization_maximalIdeal_eq_map v]
  -- Need: algebraMap r ∉ Ideal.map v.asIdeal
  -- Use mem_of_algebraMap_mem_map contrapositive
  intro h
  exact hr (mem_of_algebraMap_mem_map v r h)

-- Candidate 7 [tag: arithmetic] [relevance: 5/5] [status: PROVED] [cycle: 41]
/-- DVR intValuation equals 1 iff element is not in maximal ideal.
Characterization of valuation 1 elements in terms of ideal membership. -/
lemma dvr_intValuation_eq_one_iff_not_mem_maxIdeal (v : HeightOneSpectrum R)
    (x : Localization.AtPrime v.asIdeal) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation x = 1 ↔
      x ∉ (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).asIdeal := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  -- Use HeightOneSpectrum.intValuation_eq_one_iff
  exact HeightOneSpectrum.intValuation_eq_one_iff

-- Candidate 8 [tag: dvr_bridge] [relevance: 4/5] [status: PROVED] [cycle: 41]
/-- The asIdeal of IsDiscreteValuationRing.maximalIdeal equals IsLocalRing.maximalIdeal.
This is definitional by how DVR.maximalIdeal is constructed. -/
lemma dvr_maximalIdeal_asIdeal_eq_localRing_maximalIdeal (v : HeightOneSpectrum R) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).asIdeal =
      IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  rfl

end Cycle41Candidates

/-! ## Cycle 44 Candidates (MOVED): Ideal power membership bridge

Goal: Prove the hard case of dvr_intValuation_of_algebraMap' (when r ∈ v.asIdeal).

Key insight: Both intValuations measure "how many times the element is divisible by the prime".
The strategy is to show that ideal power membership is preserved under localization:
  r ∈ v.asIdeal^n ↔ algebraMap r ∈ maxIdeal^n

Key mathlib lemmas:
- `intValuation_le_pow_iff_mem`: v.intValuation r ≤ exp(-n) ↔ r ∈ v.asIdeal^n
- `algebraMap_mem_map_algebraMap_iff`: membership in map relates to ∃ m in complement with m*r in ideal
- `Ideal.map_pow`: map(I^n) = (map I)^n

NOTE: Section moved before Cycle39 in Cycle 47 to resolve dependency ordering.
-/
section Cycle44Candidates_Moved

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: dvr_bridge] [relevance: 5/5] [status: PROVED] [cycle: 44]
/-- Ideal.map commutes with powers. Direct application of mathlib's Ideal.map_pow. -/
lemma ideal_map_pow_eq_pow_map'_moved (v : HeightOneSpectrum R) (n : ℕ) :
    Ideal.map (algebraMap R (Localization.AtPrime v.asIdeal)) (v.asIdeal ^ n) =
      (Ideal.map (algebraMap R (Localization.AtPrime v.asIdeal)) v.asIdeal) ^ n :=
  Ideal.map_pow (algebraMap R (Localization.AtPrime v.asIdeal)) v.asIdeal n

-- Candidate 2 [tag: dvr_bridge] [relevance: 5/5] [status: PROVED] [cycle: 44]
/-- MaxIdeal^n = map(v.asIdeal^n). Combines localization_maximalIdeal_eq_map with Ideal.map_pow. -/
lemma maxIdeal_pow_eq_map_asIdeal_pow_moved (v : HeightOneSpectrum R) (n : ℕ) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) ^ n =
      Ideal.map (algebraMap R (Localization.AtPrime v.asIdeal)) (v.asIdeal ^ n) := by
  rw [localization_maximalIdeal_eq_map v, ideal_map_pow_eq_pow_map'_moved v n]

-- Candidate 3 [tag: arithmetic] [relevance: 5/5] [status: PROVED] [cycle: 44]
/-- Forward direction: r ∈ v.asIdeal^n → algebraMap r ∈ maxIdeal^n.
Direct application of mem_map_of_mem and the power identity. -/
lemma algebraMap_mem_maxIdeal_pow_of_mem_asIdeal_pow_moved (v : HeightOneSpectrum R) (r : R) (n : ℕ)
    (hr : r ∈ v.asIdeal ^ n) :
    algebraMap R (Localization.AtPrime v.asIdeal) r ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) ^ n := by
  rw [maxIdeal_pow_eq_map_asIdeal_pow_moved v n]
  exact Ideal.mem_map_of_mem _ hr

-- Candidate 4 [tag: arithmetic] [relevance: 5/5] [status: PROVED] [cycle: 45]
/-- In a Dedekind domain, if m ∉ p and m * r ∈ p^n, then r ∈ p^n.
This is the coprimality argument needed for the backward direction.
Uses Ideal.IsPrime.mul_mem_pow from mathlib. ROOT BLOCKER PROVED in Cycle 45. -/
lemma mem_pow_of_mul_mem_pow_of_not_mem_moved (v : HeightOneSpectrum R) (m r : R)
    (hm : m ∉ v.asIdeal) (n : ℕ) (hmr : m * r ∈ v.asIdeal ^ n) :
    r ∈ v.asIdeal ^ n := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  exact (Ideal.IsPrime.mul_mem_pow v.asIdeal hmr).resolve_left hm

-- Candidate 5 [tag: arithmetic] [relevance: 5/5] [status: PROVED] [cycle: 45]
/-- Backward direction: algebraMap r ∈ maxIdeal^n → r ∈ v.asIdeal^n.
Uses algebraMap_mem_map_algebraMap_iff and coprimality in Dedekind domain. -/
lemma mem_asIdeal_pow_of_algebraMap_mem_maxIdeal_pow_moved (v : HeightOneSpectrum R) (r : R) (n : ℕ)
    (hr : algebraMap R (Localization.AtPrime v.asIdeal) r ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) ^ n) :
    r ∈ v.asIdeal ^ n := by
  rw [maxIdeal_pow_eq_map_asIdeal_pow_moved v n] at hr
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff v.asIdeal.primeCompl] at hr
  obtain ⟨m, hm, hmr⟩ := hr
  have hm' : m ∉ v.asIdeal := hm  -- primeCompl membership is definitionally ∉
  exact mem_pow_of_mul_mem_pow_of_not_mem_moved v m r hm' n hmr

-- Candidate 6 [tag: arithmetic] [relevance: 5/5] [status: PROVED] [cycle: 45]
/-- Complete characterization: r ∈ v.asIdeal^n ↔ algebraMap r ∈ maxIdeal^n.
Combines the forward and backward directions. -/
lemma mem_asIdeal_pow_iff_mem_maxIdeal_pow_moved (v : HeightOneSpectrum R) (r : R) (n : ℕ) :
    r ∈ v.asIdeal ^ n ↔
      algebraMap R (Localization.AtPrime v.asIdeal) r ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) ^ n :=
  ⟨algebraMap_mem_maxIdeal_pow_of_mem_asIdeal_pow_moved v r n,
   mem_asIdeal_pow_of_algebraMap_mem_maxIdeal_pow_moved v r n⟩

-- Candidate 7 [tag: arithmetic] [relevance: 5/5] [status: PROVED] [cycle: 46]
/-- DVR intValuation characterization via ideal powers.
Both valuations measure the same ideal power membership.
Key lemma that bridges HeightOneSpectrum.intValuation with the DVR intValuation. -/
lemma dvr_intValuation_eq_via_pow_membership_moved (v : HeightOneSpectrum R) (r : R) (hr_ne : r ≠ 0) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation
      (algebraMap R (Localization.AtPrime v.asIdeal) r) = v.intValuation r := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  -- Strategy: Both intValuations are characterized by ideal power membership via intValuation_le_pow_iff_mem.
  -- Key insight: (DVR.maximalIdeal).asIdeal = IsLocalRing.maximalIdeal (definitional)
  -- Use mem_asIdeal_pow_iff_mem_maxIdeal_pow_moved to transfer between ideal powers.
  let dvrMax := IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)
  -- Both intValuations satisfy: intVal x ≤ exp(-n) ↔ x ∈ asIdeal^n
  -- For the DVR: dvrMax.intVal (algebraMap r) ≤ exp(-n) ↔ algebraMap r ∈ dvrMax.asIdeal^n
  --            = algebraMap r ∈ (IsLocalRing.maximalIdeal)^n (by dvr_maximalIdeal_asIdeal_eq_localRing_maximalIdeal)
  -- For v: v.intVal r ≤ exp(-n) ↔ r ∈ v.asIdeal^n (by intValuation_le_pow_iff_mem)
  -- Bridge: r ∈ v.asIdeal^n ↔ algebraMap r ∈ maxIdeal^n (by mem_asIdeal_pow_iff_mem_maxIdeal_pow_moved)
  -- Use le_antisymm with the WithZero.exp characterization
  have hbridge : ∀ n : ℕ, dvrMax.intValuation (algebraMap R _ r) ≤ WithZero.exp (-(n : ℤ)) ↔
      v.intValuation r ≤ WithZero.exp (-(n : ℤ)) := fun n => by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    rw [dvr_maximalIdeal_asIdeal_eq_localRing_maximalIdeal v]
    exact (mem_asIdeal_pow_iff_mem_maxIdeal_pow_moved v r n).symm
  -- Now use that values in WithZero (ℤᵐ⁰) are equal iff they satisfy the same inequalities
  -- Both values are of form exp(-k) for some k, so use the fact that the valuations agree on all exp(-n)
  -- Key: Both valuations take values exp(-n) for some n ∈ ℕ (since they're nonzero and ≤ 1).
  -- hbridge shows they're in the same "threshold class" for all exp(-n).
  -- For any two elements a, b of form exp(-k), a = b iff ∀n, (a ≤ exp(-n) ↔ b ≤ exp(-n)).
  -- Actually, we just need: a ≤ b iff ∀n, b ≤ exp(-n) → a ≤ exp(-n)
  -- and vice versa, then le_antisymm gives equality.
  have hr' : algebraMap R (Localization.AtPrime v.asIdeal) r ≠ 0 := by
    intro h
    apply hr_ne
    have hpc : v.asIdeal.primeCompl ≤ nonZeroDivisors R := v.asIdeal.primeCompl_le_nonZeroDivisors
    exact (IsLocalization.to_map_eq_zero_iff (Localization.AtPrime v.asIdeal) hpc).mp h
  classical  -- needed for DecidableEq instances in Associates.count
  apply le_antisymm
  · -- Show DVR.intVal ≤ v.intVal
    -- Strategy: v.intVal = exp(-k) for some k, and hbridge gives DVR.intVal ≤ exp(-k)
    have hk : v.intValuation r = WithZero.exp
        (-(((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors) : ℤ)) :=
      v.intValuation_if_neg hr_ne
    let k := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors
    calc dvrMax.intValuation (algebraMap R (Localization.AtPrime v.asIdeal) r)
        ≤ WithZero.exp (-(k : ℤ)) := (hbridge k).mpr (le_of_eq hk)
      _ = v.intValuation r := hk.symm
  · -- Show v.intVal ≤ DVR.intVal
    have hm : dvrMax.intValuation (algebraMap R (Localization.AtPrime v.asIdeal) r) = WithZero.exp
        (-(((Associates.mk dvrMax.asIdeal).count (Associates.mk (Ideal.span {algebraMap R _ r})).factors) : ℤ)) :=
      dvrMax.intValuation_if_neg hr'
    let m := (Associates.mk dvrMax.asIdeal).count (Associates.mk (Ideal.span {algebraMap R _ r})).factors
    calc v.intValuation r
        ≤ WithZero.exp (-(m : ℤ)) := (hbridge m).mp (le_of_eq hm)
      _ = dvrMax.intValuation (algebraMap R (Localization.AtPrime v.asIdeal) r) := hm.symm

end Cycle44Candidates_Moved

/-! ## Cycle 39 Candidates: Prove dvr_intValuation_of_algebraMap

The key blocker is `dvr_intValuation_of_algebraMap`: showing that the DVR's intValuation
agrees with v.intValuation on elements from R.

**Mathematical insight**: Both intValuations measure divisibility by the same prime:
- `v.intValuation r` counts powers of v.asIdeal in Ideal.span {r}
- DVR's intValuation on `algebraMap R Loc r` counts powers of maxIdeal in Ideal.span {algebraMap R Loc r}
- We know maxIdeal = Ideal.map v.asIdeal (localization_maximalIdeal_eq_map)
- Key fact: Ideal.map preserves the count under localization at the prime

**Approaches**:
1. Direct proof via span mapping and ideal map properties
2. Proof via uniformizer: both valuations measure powers of the same uniformizer
3. Proof via ideal membership: r ∈ v.asIdeal^n ↔ algebraMap r ∈ maxIdeal^n
4. Inductive proof on the valuation count
5. Alternative via DVR additive valuation (addVal) equality
-/

section Cycle39Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: dvr_bridge] [relevance: 5/5] [status: TBD] [cycle: 39]
/-- Ideal.span commutes with algebraMap: map (span {r}) = span {algebraMap r}.
This is the key identity for relating the two intValuations. -/
lemma ideal_span_map_singleton (v : HeightOneSpectrum R) (r : R) :
    Ideal.map (algebraMap R (Localization.AtPrime v.asIdeal)) (Ideal.span {r}) =
      Ideal.span {algebraMap R (Localization.AtPrime v.asIdeal) r} := by
  rw [Ideal.map_span]
  congr 1
  exact Set.image_singleton

-- Candidate 2 [tag: dvr_bridge] [relevance: 5/5] [status: TBD] [cycle: 39]
/-- The uniformizer at v remains a uniformizer after mapping to the localization.
More precisely, algebraMap π generates the maximal ideal of Loc.AtPrime. -/
lemma algebraMap_uniformizer_dvr_uniformizer (v : HeightOneSpectrum R) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation
      (algebraMap R (Localization.AtPrime v.asIdeal) (uniformizerAt v)) = WithZero.exp (-1 : ℤ) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  -- The DVR's uniformizer should equal the image of v's uniformizer
  -- Both generate the same maximal ideal (up to units)
  sorry

-- Candidate 3 [tag: dvr_bridge] [relevance: 5/5] [status: TBD] [cycle: 39]
/-- The DVR's intValuation definition unpacks using intValuationDef.
Both DVR and v's intValuation use the same underlying definition. -/
lemma dvr_intValuation_unfold (v : HeightOneSpectrum R) (r : Localization.AtPrime v.asIdeal) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation r =
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuationDef r := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  rfl

-- Candidate 4 [tag: dvr_bridge] [relevance: 5/5] [status: TBD] [cycle: 39]
/-- Ideal membership is preserved under localization: r ∈ v.asIdeal ↔ algebraMap r ∈ maxIdeal.
This is the base case that drives the intValuation equality. -/
lemma mem_asIdeal_iff_mem_maxIdeal (v : HeightOneSpectrum R) (r : R) :
    r ∈ v.asIdeal ↔
      algebraMap R (Localization.AtPrime v.asIdeal) r ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) := by
  -- maxIdeal = Ideal.map v.asIdeal
  rw [localization_maximalIdeal_eq_map v]
  -- r ∈ v.asIdeal ↔ algebraMap r ∈ Ideal.map v.asIdeal
  -- Use Cycle 41: algebraMap_mem_map_of_mem (forward) + mem_of_algebraMap_mem_map (reverse)
  exact ⟨algebraMap_mem_map_of_mem v r, mem_of_algebraMap_mem_map v r⟩

-- Candidate 5 [tag: arithmetic] [relevance: 5/5] [status: TBD] [cycle: 39]
/-- Direct proof of dvr_intValuation_of_algebraMap using count preservation.
Combines the span mapping and count preservation lemmas. -/
lemma dvr_intValuation_of_algebraMap' (v : HeightOneSpectrum R) (r : R) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation
      (algebraMap R (Localization.AtPrime v.asIdeal) r) = v.intValuation r := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  by_cases hr0 : r = 0
  · simp only [hr0, map_zero]
  by_cases hr : r ∈ v.asIdeal
  · -- Hard case: r ∈ v.asIdeal (PROVED Cycle 47 via section reordering)
    exact dvr_intValuation_eq_via_pow_membership_moved v r hr0
  · -- Easy case: r ∉ v.asIdeal, both = 1
    -- DVR side: use Cycle 41 lemmas directly (algebraMap_isUnit_iff_not_mem + dvr_intValuation_of_isUnit)
    -- v side: intValuation_eq_one_iff gives intVal = 1 when r ∉ v.asIdeal
    have hunit := (algebraMap_isUnit_iff_not_mem v r).mpr hr
    rw [dvr_intValuation_of_isUnit v _ hunit]
    symm
    rw [HeightOneSpectrum.intValuation_eq_one_iff]
    exact hr

-- Candidate 6 [tag: dvr_bridge] [relevance: 4/5] [status: TBD] [cycle: 39]
/-- Alternative proof via ideal membership: r ∈ v.asIdeal^n ↔ algebraMap r ∈ maxIdeal^n.
This establishes the key ideal membership preservation that powers both intValuations. -/
lemma mem_asIdeal_pow_iff_mem_maxIdeal_pow (v : HeightOneSpectrum R) (r : R) (n : ℕ) :
    r ∈ v.asIdeal ^ n ↔
      algebraMap R (Localization.AtPrime v.asIdeal) r ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) ^ n := by
  -- The maximal ideal of Loc.AtPrime = Ideal.map v.asIdeal
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) =
      Ideal.map (algebraMap R (Localization.AtPrime v.asIdeal)) v.asIdeal :=
    localization_maximalIdeal_eq_map v
  rw [hmax]
  -- Now use properties of Ideal.map and membership
  sorry

-- Candidate 7 [tag: dvr_bridge] [relevance: 5/5] [status: TBD] [cycle: 39]
/-- For powers of the uniformizer, the DVR intValuation agrees with v.intValuation.
This is a special case that might be easier to prove first. -/
lemma dvr_intValuation_uniformizer_pow (v : HeightOneSpectrum R) (n : ℕ) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation
      (algebraMap R (Localization.AtPrime v.asIdeal) ((uniformizerAt v) ^ n)) =
    v.intValuation ((uniformizerAt v) ^ n) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  -- Both should equal exp(-n)
  -- Use uniformizerAt_pow_val for v.intValuation
  -- Use algebraMap_uniformizer_dvr_uniformizer for the DVR side
  rw [map_pow, uniformizerAt_pow_val]
  -- Now show DVR.intValuation (algebraMap π)^n = exp(-n)
  sorry

-- Candidate 8 [tag: rewrite_bridge] [relevance: 4/5] [status: TBD] [cycle: 39]
/-- Elements not in v.asIdeal remain units in the localization, with intValuation = 1.
This establishes the base case for elements coprime to v. -/
lemma dvr_intValuation_unit (v : HeightOneSpectrum R) (r : R) (hr : r ∉ v.asIdeal) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation
      (algebraMap R (Localization.AtPrime v.asIdeal) r) = 1 := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  -- r ∉ v.asIdeal means algebraMap r is a unit in Loc.AtPrime
  -- Units have intValuation = 1 in a DVR
  -- Use Cycle 41: algebraMap_isUnit_iff_not_mem + dvr_intValuation_of_isUnit
  have hunit := (algebraMap_isUnit_iff_not_mem v r).mpr hr
  exact dvr_intValuation_of_isUnit v _ hunit

end Cycle39Candidates

/-! ## Cycle 42 Candidates: Complete Foundation + Attack Hard Case

Goal: Prove the hard case of dvr_intValuation_of_algebraMap' (when r ∈ v.asIdeal).
Strategy: Show both intValuations count ideal powers the same way.
-/
section Cycle42Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: arithmetic] [relevance: 5/5] [status: SORRY] [cycle: 42]
/-- For r ∈ v.asIdeal with r ≠ 0, the DVR intValuation < 1.
Uses mem_asIdeal_iff_mem_maxIdeal to transfer ideal membership. -/
lemma dvr_intValuation_mem_lt_one (v : HeightOneSpectrum R) (r : R)
    (hr : r ∈ v.asIdeal) (hr_ne : r ≠ 0) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation
      (algebraMap R (Localization.AtPrime v.asIdeal) r) < 1 := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  have hmem : algebraMap R (Localization.AtPrime v.asIdeal) r ∈
      (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).asIdeal := by
    rw [dvr_maximalIdeal_asIdeal_eq_localRing_maximalIdeal v]
    rw [← mem_asIdeal_iff_mem_maxIdeal v r]
    exact hr
  -- We have: r ∈ maxIdeal.asIdeal and r ≠ 0, need to conclude intVal < 1
  -- Use HeightOneSpectrum.intValuation_lt_one_iff_dvd for DVR.maximalIdeal
  rw [HeightOneSpectrum.intValuation_lt_one_iff_dvd]
  sorry

-- Candidate 2 [tag: dvr_bridge] [relevance: 5/5] [status: PROVED] [cycle: 42]
/-- DVR intValuation of zero equals zero (via map_zero).
Base case for intValuation equality. -/
lemma dvr_intValuation_zero (v : HeightOneSpectrum R) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation
      (0 : Localization.AtPrime v.asIdeal) = 0 := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  exact map_zero _

-- Candidate 3 [tag: arithmetic] [relevance: 5/5] [status: SORRY] [cycle: 42]
/-- For r ∈ v.asIdeal, both intValuations are < 1.
Establishes parallel structure for the hard case. -/
lemma intValuation_mem_lt_one_both (v : HeightOneSpectrum R) (r : R)
    (hr : r ∈ v.asIdeal) (hr_ne : r ≠ 0) :
    v.intValuation r < 1 ∧
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation
      (algebraMap R (Localization.AtPrime v.asIdeal) r) < 1 := by
  refine ⟨?_, dvr_intValuation_mem_lt_one v r hr hr_ne⟩
  -- Use HeightOneSpectrum.intValuation_lt_one_iff_mem
  rw [v.intValuation_lt_one_iff_mem]
  exact hr

end Cycle42Candidates

-- NOTE: Cycle44Candidates section was moved before Cycle39 in Cycle 47.
-- The original section is now at Cycle44Candidates_Moved above.

/-! ## Cycle 48 Candidates: Prove dvr_valuation_eq_height_one' (KEY BLOCKER)

Goal: Prove dvr_valuation_eq_height_one' using dvr_intValuation_of_algebraMap'.

This section is placed at the end of the file because it has access to all the
previously defined lemmas (unlike the placeholder in Cycle37).

After verification, section reordering should move this proof to replace the
placeholder in Cycle37.
-/

section Cycle48Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: dvr_bridge] [relevance: 5/5] [status: PROVED] [cycle: 48]
/-- PROOF VERIFICATION: DVR valuation equals HeightOneSpectrum valuation.
This lemma proves the same statement as dvr_valuation_eq_height_one' (Cycle37)
but has access to dvr_intValuation_of_algebraMap' (Cycle39).
After verification, use section reordering to replace the Cycle37 placeholder. -/
lemma dvr_valuation_eq_height_one'_proof (v : HeightOneSpectrum R) (g : K) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K g =
      v.valuation K g := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- Write g as r/s for r, s ∈ R with s ∈ nonZeroDivisors
  obtain ⟨r, s, hs, hg⟩ := IsFractionRing.div_surjective (A := R) g
  rw [← hg]
  -- RHS: Use valuation_of_fraction
  rw [valuation_of_fraction v r (nonZeroDivisors.ne_zero hs)]
  -- LHS: Use Valuation.map_div and the scalar tower
  let dvr_spec := IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)
  rw [Valuation.map_div (dvr_spec.valuation K)]
  -- Rewrite algebraMap R K = algebraMap (Loc.AtPrime) K ∘ algebraMap R (Loc.AtPrime)
  have hr_eq : algebraMap R K r = algebraMap (Localization.AtPrime v.asIdeal) K
      (algebraMap R (Localization.AtPrime v.asIdeal) r) :=
    IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal) K r
  have hs_eq : algebraMap R K (s : R) = algebraMap (Localization.AtPrime v.asIdeal) K
      (algebraMap R (Localization.AtPrime v.asIdeal) (s : R)) :=
    IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal) K (s : R)
  rw [hr_eq, hs_eq]
  -- Apply dvr_spec.valuation_of_algebraMap to reduce to intValuation
  rw [dvr_spec.valuation_of_algebraMap, dvr_spec.valuation_of_algebraMap]
  -- Apply dvr_intValuation_of_algebraMap' twice
  rw [dvr_intValuation_of_algebraMap' v r, dvr_intValuation_of_algebraMap' v (s : R)]

end Cycle48Candidates

/-! ## Cycle 51 Candidates: Prove residueFieldBridge

Goal: Prove `residueFieldBridge : valuationRingAt.residueField v ≃+* residueFieldAtPrime R v`

Strategy: Compose the chain:
1. `valuationRingAt_equiv_localization'` (PROVED, line 1491) gives ring equiv
2. Show this equiv is a local ring homomorphism
3. Transport residue field structure
4. Compose with `localization_residueField_equiv` (PROVED, line 710)
-/

section Cycle51Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: rr_bundle_bridge] [relevance: 5/5] [status: PROVED Cycle52] [cycle: 51]
/-- A RingEquiv between local rings maps units to units.
This shows valuationRingAt_equiv_localization' preserves the maximal ideal structure. -/
lemma valuationRingAt_equiv_map_unit_iff (v : HeightOneSpectrum R)
    (x : valuationRingAt (R := R) (K := K) v) :
    IsUnit x ↔ IsUnit ((valuationRingAt_equiv_localization' (R := R) (K := K) v) x) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  exact (MulEquiv.isUnit_map (valuationRingAt_equiv_localization' (R := R) (K := K) v)).symm

-- Candidate 2 [tag: rr_bundle_bridge] [relevance: 3/5] [status: NOT_NEEDED] [cycle: 51]
-- NOT_NEEDED: IsLocalRing.ResidueField.mapEquiv handles ideal correspondence automatically.
-- The mapEquiv approach (Candidate 3) bypasses the need for explicit ideal comap equality.
/-- The maximal ideal of valuationRingAt v equals the preimage of the maximal ideal
of Localization.AtPrime v.asIdeal under valuationRingAt_equiv_localization'.
This establishes the ideal correspondence needed for residue field transport. -/
lemma valuationRingAt_maximalIdeal_correspondence (v : HeightOneSpectrum R) :
    IsLocalRing.maximalIdeal (valuationRingAt (R := R) (K := K) v) =
      Ideal.comap (valuationRingAt_equiv_localization' (R := R) (K := K) v).toRingHom
        (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) := sorry

-- Candidate 3 [tag: rr_bundle_bridge] [relevance: 5/5] [status: PROVED Cycle52] [cycle: 51]
/-- Direct construction: Transport residue field from valuationRingAt to Localization.AtPrime
using valuationRingAt_equiv_localization'. Uses IsLocalRing.ResidueField.mapEquiv. -/
noncomputable def residueField_transport_direct (v : HeightOneSpectrum R) :
    IsLocalRing.ResidueField (valuationRingAt (R := R) (K := K) v) ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  exact IsLocalRing.ResidueField.mapEquiv (valuationRingAt_equiv_localization' (R := R) (K := K) v)

-- Candidate 4 [tag: rr_bundle_bridge] [relevance: 5/5] [status: PROVED Cycle52] [cycle: 51]
/-- The full residueFieldBridge constructed by composing:
(1) Transport residue field from valuationRingAt to Localization via residueField_transport_direct
(2) Apply localization_residueField_equiv to get to residueFieldAtPrime.
This is the main target for Cycle 51. -/
noncomputable def residueFieldBridge_via_composition (v : HeightOneSpectrum R) :
    valuationRingAt.residueField (R := R) (K := K) v ≃+* residueFieldAtPrime R v := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  exact (residueField_transport_direct (R := R) (K := K) v).trans (localization_residueField_equiv v)

-- Candidate 5 [tag: coercion_simplify] [relevance: 5/5] [status: PROVED Cycle52] [cycle: 51]
/-- Alternative: Use that isomorphic local rings have isomorphic residue fields directly.
Both valuationRingAt and Localization.AtPrime are local rings with equiv between them. -/
lemma residueField_iso_of_ringEquiv_localRings (v : HeightOneSpectrum R)
    (e : valuationRingAt (R := R) (K := K) v ≃+* Localization.AtPrime v.asIdeal) :
    Nonempty (IsLocalRing.ResidueField (valuationRingAt (R := R) (K := K) v) ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal)) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  exact ⟨IsLocalRing.ResidueField.mapEquiv e⟩

-- Candidate 6 [tag: rr_bundle_bridge] [relevance: 5/5] [status: PROVED Cycle52] [cycle: 51]
/-- Key helper: Show valuationRingAt_equiv_localization' maps maximalIdeal to maximalIdeal.
An element is in maximalIdeal iff its valuation < 1. The equiv preserves valuation. -/
lemma valuationRingAt_equiv_mem_maximalIdeal_iff (v : HeightOneSpectrum R)
    (x : valuationRingAt (R := R) (K := K) v) :
    x ∈ IsLocalRing.maximalIdeal (valuationRingAt (R := R) (K := K) v) ↔
      (valuationRingAt_equiv_localization' (R := R) (K := K) v) x ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- Use that x ∈ maximalIdeal ↔ x ∈ nonunits ↔ ¬IsUnit x, and RingEquiv preserves units
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rw [valuationRingAt_equiv_map_unit_iff v x]

-- Candidate 7 [tag: rr_bundle_bridge] [relevance: 5/5] [status: PROVED Cycle52] [cycle: 51]
/-- Explicit map construction: The residue field bridge as an explicit quotient isomorphism.
Uses that both residue fields are quotients by maximal ideals, and the ring equiv
induces a bijection on these quotients. -/
noncomputable def residueFieldBridge_explicit (v : HeightOneSpectrum R) :
    valuationRingAt.residueField (R := R) (K := K) v ≃+* residueFieldAtPrime R v := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- Chain: valuationRingAt.residueField → Loc.AtPrime.residueField → residueFieldAtPrime
  -- Step 1: transport via valuationRingAt_equiv_localization'
  have h1 : IsLocalRing.ResidueField (valuationRingAt (R := R) (K := K) v) ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal) := residueField_transport_direct v
  -- Step 2: use localization_residueField_equiv
  have h2 : IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal) ≃+*
      residueFieldAtPrime R v := localization_residueField_equiv v
  exact h1.trans h2

-- Candidate 8 [tag: coercion_simplify] [relevance: 5/5] [status: PROVED Cycle52] [cycle: 51]
/-- Verification: The residue map commutes with the ring equivalence.
For a ∈ valuationRingAt v, applying residue then the transported equiv
equals applying the equiv then residue. Uses the specific mapEquiv. -/
lemma residueField_equiv_commutes_with_residue (v : HeightOneSpectrum R)
    (a : valuationRingAt (R := R) (K := K) v) :
    (residueField_transport_direct (R := R) (K := K) v)
      (IsLocalRing.residue (valuationRingAt (R := R) (K := K) v) a) =
      IsLocalRing.residue (Localization.AtPrime v.asIdeal)
        ((valuationRingAt_equiv_localization' (R := R) (K := K) v) a) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- residueField_transport_direct is mapEquiv, and map_residue gives the commutation
  rfl

end Cycle51Candidates

/-! ## Cycle 55 Candidates: evaluationMapAt_via_bridge construction

Goal: Prove evaluationMapAt_via_bridge (LocalGapInstance.lean:379)

Strategy: Construct the linear map L(D+v) →ₗ[R] κ(v) by:
1. Shift f ↦ f * π^{(D v + 1).toNat}
2. Use shifted_element_valuation_le_one to get g ∈ valuationRingAt v
3. Apply valuationRingAt.residue v
4. Apply residueFieldBridge_explicit v
-/

section Cycle55Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: rr_bundle_bridge] [status: OK] [cycle: 55]
/-- The shifted element function: f ↦ f * π^{(D v + 1).toNat}.
This is the core computation in the evaluation map construction.
For f ∈ L(D+v), the shifted element has valuation ≤ 1 at v. -/
noncomputable def shiftedElement (v : HeightOneSpectrum R) (D : DivisorV2 R) (f : K) : K :=
  f * algebraMap R K ((uniformizerAt v) ^ (D v + 1).toNat)

-- Candidate 2 [tag: coercion_simplify] [status: PROVED] [cycle: 55]
/-- The shifted element of f ∈ L(D+v) lies in the valuation ring at v.
This follows immediately from shifted_element_valuation_le_one and mem_valuationRingAt_iff. -/
lemma shiftedElement_mem_valuationRingAt (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : RRModuleV2_real R K (D + DivisorV2.single v 1)) :
    shiftedElement v D f.val ∈ valuationRingAt (R := R) (K := K) v := by
  rw [mem_valuationRingAt_iff]
  exact shifted_element_valuation_le_one v D f.val f.property

-- Candidate 3 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 55]
/-- Additivity of shiftedElement: (f + g) * π^n = f * π^n + g * π^n.
Key for proving the evaluation map is additive. -/
lemma shiftedElement_add (v : HeightOneSpectrum R) (D : DivisorV2 R) (f g : K) :
    shiftedElement v D (f + g) = shiftedElement v D f + shiftedElement v D g := by
  simp only [shiftedElement, add_mul]

-- Candidate 4 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 55]
/-- R-linearity of shiftedElement: (r • f) * π^n = r • (f * π^n).
Key for proving the evaluation map respects R-module structure. -/
lemma shiftedElement_smul (v : HeightOneSpectrum R) (D : DivisorV2 R) (r : R) (f : K) :
    shiftedElement v D (algebraMap R K r * f) =
    algebraMap R K r * shiftedElement v D f := by
  simp only [shiftedElement, mul_assoc]

-- Candidate 5 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 55]
/-- The core evaluation function: sends f ∈ L(D+v) to its residue class in κ(v).
Computes shiftedElement, embeds into valuationRingAt, applies residue, then bridges. -/
noncomputable def evaluationFun_via_bridge (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : RRModuleV2_real R K (D + DivisorV2.single v 1)) : residueFieldAtPrime R v :=
  let g : valuationRingAt (R := R) (K := K) v :=
    ⟨shiftedElement v D f.val, shiftedElement_mem_valuationRingAt v D f⟩
  let res := (valuationRingAt.residue (R := R) (K := K) v) g
  (residueFieldBridge_explicit (R := R) (K := K) v) res

-- Cycle 56 helper: subtype equality in valuationRingAt for addition
-- [tag: coercion_simplify] [status: PROVED] [cycle: 56]
/-- The shifted element subtype for (f + g) equals the sum of shifted subtypes.
Key for proving evaluationFun_add. -/
lemma shiftedSubtype_add (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f g : RRModuleV2_real R K (D + DivisorV2.single v 1)) :
    (⟨shiftedElement v D (f + g).val, shiftedElement_mem_valuationRingAt v D (f + g)⟩ :
      valuationRingAt (R := R) (K := K) v) =
    ⟨shiftedElement v D f.val, shiftedElement_mem_valuationRingAt v D f⟩ +
    ⟨shiftedElement v D g.val, shiftedElement_mem_valuationRingAt v D g⟩ := by
  apply Subtype.ext
  show shiftedElement v D (f + g).val =
       (⟨shiftedElement v D f.val, _⟩ + ⟨shiftedElement v D g.val, _⟩ : valuationRingAt v).val
  conv_rhs => rw [show (⟨shiftedElement v D f.val, _⟩ + ⟨shiftedElement v D g.val, _⟩ : valuationRingAt v).val =
    shiftedElement v D f.val + shiftedElement v D g.val from rfl]
  exact shiftedElement_add v D f.val g.val

-- Cycle 56 helper: subtype equality in valuationRingAt for smul
-- [tag: coercion_simplify] [status: PROVED] [cycle: 56]
/-- The shifted element subtype for (r • f) equals algebraMap r times shifted subtype.
Key for proving evaluationFun_smul. -/
lemma shiftedSubtype_smul (v : HeightOneSpectrum R) (D : DivisorV2 R) (r : R)
    (f : RRModuleV2_real R K (D + DivisorV2.single v 1)) :
    (⟨shiftedElement v D (r • f).val, shiftedElement_mem_valuationRingAt v D (r • f)⟩ :
      valuationRingAt (R := R) (K := K) v) =
    ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩ *
    ⟨shiftedElement v D f.val, shiftedElement_mem_valuationRingAt v D f⟩ := by
  apply Subtype.ext
  show shiftedElement v D (r • f).val = _
  conv_lhs => rw [show (r • f).val = r • f.val from rfl, Algebra.smul_def]
  rw [shiftedElement_smul]
  rfl

-- Cycle 56 KEY BLOCKER: Diagram commutativity for algebra structure
-- [tag: rr_bundle_bridge] [status: SORRY] [cycle: 56]
/-- Diagram commutativity: bridge(residue(algebraMap r)) = algebraMap r in residue field.
This is the key lemma for R-linearity of the evaluation map. -/
lemma bridge_residue_algebraMap (v : HeightOneSpectrum R) (r : R) :
    (residueFieldBridge_explicit (R := R) (K := K) v)
      ((valuationRingAt.residue (R := R) (K := K) v) ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩) =
    algebraMap R (residueFieldAtPrime R v) r := sorry

-- Candidate 6 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 56]
/-- The evaluation function is additive.
Uses shiftedSubtype_add and that residue and bridge are additive homomorphisms. -/
lemma evaluationFun_add (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f g : RRModuleV2_real R K (D + DivisorV2.single v 1)) :
    evaluationFun_via_bridge v D (f + g) =
    evaluationFun_via_bridge v D f + evaluationFun_via_bridge v D g := by
  simp only [evaluationFun_via_bridge]
  rw [shiftedSubtype_add]
  simp only [map_add]

-- Candidate 7 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 56]
/-- The evaluation function respects R-scalar multiplication.
Uses shiftedSubtype_smul and bridge_residue_algebraMap. -/
lemma evaluationFun_smul (v : HeightOneSpectrum R) (D : DivisorV2 R) (r : R)
    (f : RRModuleV2_real R K (D + DivisorV2.single v 1)) :
    evaluationFun_via_bridge v D (r • f) = r • evaluationFun_via_bridge v D f := by
  simp only [evaluationFun_via_bridge]
  rw [shiftedSubtype_smul]
  simp only [map_mul]
  rw [Algebra.smul_def]
  congr 1
  exact bridge_residue_algebraMap v r

-- Candidate 8 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 56]
/-- The complete evaluation map as a linear map.
Bundles evaluationFun_via_bridge with additivity and R-linearity proofs. -/
noncomputable def evaluationMapAt_complete (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    RRModuleV2_real R K (D + DivisorV2.single v 1) →ₗ[R] residueFieldAtPrime R v where
  toFun := evaluationFun_via_bridge v D
  map_add' := evaluationFun_add v D
  map_smul' r f := evaluationFun_smul v D r f

end Cycle55Candidates

/-! ## Cycle 57 Candidates: Proving bridge_residue_algebraMap (diagram commutativity)

Goal: Prove `bridge_residue_algebraMap` - the key blocker for R-algebra structure.

Strategy: Break down the composition `residueFieldBridge_explicit = h1.trans h2`:
1. h1 = `residueField_transport_direct` = `mapEquiv (valuationRingAt_equiv_localization')`
2. h2 = `localization_residueField_equiv` = `(localization_residue_equiv).symm.trans (algebraMap_bijection)`

Key mathlib lemmas:
- `IsLocalRing.ResidueField.map_residue`: `map f (residue r) = residue (f r)`
- `IsLocalRing.ResidueField.algebraMap_residue`: `algebraMap (residue x) = residue (algebraMap x)` (rfl)
- `IsScalarTower.algebraMap_apply`: algebra tower factorization
-/

section Cycle57Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 57]
/-- The key step: showing that valuationRingAt_equiv_localization' maps algebraMap R K r
to algebraMap R (Localization.AtPrime) r. This establishes scalar compatibility. -/
lemma valuationRingAt_equiv_algebraMap (v : HeightOneSpectrum R) (r : R) :
    (valuationRingAt_equiv_localization' (R := R) (K := K) v)
      ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩ =
    algebraMap R (Localization.AtPrime v.asIdeal) r := by
  -- The equiv is equivValuationSubring.symm transported along equality
  -- Key: algebraMap R K factors through Loc by scalar tower, and equivValuationSubring
  -- maps x ↦ ⟨algebraMap x, _⟩, so its inverse is the preimage.
  -- Strategy: use congrArg to transport along the ValuationSubring equality,
  -- then apply equivValuationSubring.symm_apply_apply
  sorry

-- Candidate 2 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 57]
/-- The h1 step: residue field transport commutes with residue of algebraMap.
Uses residueField_equiv_commutes_with_residue and valuationRingAt_equiv_algebraMap. -/
lemma residueField_transport_algebraMap (v : HeightOneSpectrum R) (r : R) :
    (residueField_transport_direct (R := R) (K := K) v)
      ((valuationRingAt.residue (R := R) (K := K) v) ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩) =
    IsLocalRing.residue (Localization.AtPrime v.asIdeal)
      (algebraMap R (Localization.AtPrime v.asIdeal) r) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- valuationRingAt.residue is IsLocalRing.residue
  conv_lhs => rw [valuationRingAt.residue]
  rw [residueField_equiv_commutes_with_residue, valuationRingAt_equiv_algebraMap]

-- Candidate 3 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 60]
/-- The h2 step: localization_residueField_equiv maps residue of algebraMap R to algebraMap R κ(v).
BLOCKER 2 - Proof in TestBlockerProofs.lean works; type unification issue in main file. -/
lemma localization_residueField_equiv_algebraMap (v : HeightOneSpectrum R) (r : R) :
    (localization_residueField_equiv v)
      (IsLocalRing.residue (Localization.AtPrime v.asIdeal)
        (algebraMap R (Localization.AtPrime v.asIdeal) r)) =
    algebraMap R (residueFieldAtPrime R v) r := by
  -- Proof structure from TestBlockerProofs.lean:
  -- 1. unfold localization_residueField_equiv + simp [trans_apply]
  -- 2. rw [residue_def, mk_algebraMap]
  -- 3. Key: (loc_res_equiv v).symm (algebraMap R ...) = Quotient.mk v.asIdeal r
  -- 4. simp [key, ofBijective_apply, Quotient.algebraMap_eq]
  -- Type mismatch between residueFieldAtPrime R v and v.asIdeal.ResidueField blocks rw/simp
  sorry

-- Candidate 4 [tag: coercion_simplify] [status: PROVED] [cycle: 57]
/-- Scalar tower property: algebraMap from R to κ(v) factors as R → R/I → κ(v). -/
lemma algebraMap_residueField_factorization (v : HeightOneSpectrum R) (r : R) :
    algebraMap R (residueFieldAtPrime R v) r =
    algebraMap (R ⧸ v.asIdeal) (residueFieldAtPrime R v) (Ideal.Quotient.mk v.asIdeal r) := by
  rw [IsScalarTower.algebraMap_apply R (R ⧸ v.asIdeal) (residueFieldAtPrime R v)]
  rfl

-- Candidate 5 [tag: coercion_simplify] [status: PROVED] [cycle: 57]
/-- Commutation of residue and algebraMap in Localization.AtPrime. Definitional. -/
lemma localization_residue_algebraMap (v : HeightOneSpectrum R) (r : R) :
    IsLocalRing.residue (Localization.AtPrime v.asIdeal)
      (algebraMap R (Localization.AtPrime v.asIdeal) r) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal))
      (algebraMap R (Localization.AtPrime v.asIdeal) r) := rfl

-- Candidate 6 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 57]
/-- The quotient map R → R ⧸ v.asIdeal factors through localization residue field.
This is the inverse of equivQuotMaximalIdeal applied to algebraMap r. -/
lemma quotient_mk_via_localization (v : HeightOneSpectrum R) (r : R) :
    Ideal.Quotient.mk v.asIdeal r =
    (localization_residue_equiv v).symm
      (IsLocalRing.residue (Localization.AtPrime v.asIdeal)
        (algebraMap R (Localization.AtPrime v.asIdeal) r)) := by
  sorry

-- Candidate 7 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 57]
/-- Direct composition: once Candidates 2 and 3 are proved, this follows by rewriting. -/
lemma residueFieldBridge_composition_algebraMap (v : HeightOneSpectrum R) (r : R) :
    ((residueField_transport_direct (R := R) (K := K) v).trans (localization_residueField_equiv v))
      ((valuationRingAt.residue (R := R) (K := K) v) ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩) =
    algebraMap R (residueFieldAtPrime R v) r := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  simp only [RingEquiv.trans_apply]
  rw [residueField_transport_algebraMap, localization_residueField_equiv_algebraMap]

-- Candidate 8 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 57]
/-- The full proof using that residueFieldBridge_explicit = h1.trans h2.
Depends on Candidates 2 and 3. -/
lemma bridge_residue_algebraMap_proof (v : HeightOneSpectrum R) (r : R) :
    (residueFieldBridge_explicit (R := R) (K := K) v)
      ((valuationRingAt.residue (R := R) (K := K) v) ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩) =
    algebraMap R (residueFieldAtPrime R v) r := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- residueFieldBridge_explicit = h1.trans h2
  unfold residueFieldBridge_explicit
  simp only [RingEquiv.trans_apply]
  rw [residueField_transport_algebraMap, localization_residueField_equiv_algebraMap]

end Cycle57Candidates

/-! ## Cycle 59 Candidates: Proving Key Blockers

Two key blockers for bridge_residue_algebraMap:
- BLOCKER 1: valuationRingAt_equiv_algebraMap (scalar tower compatibility)
- BLOCKER 2: localization_residueField_equiv_algebraMap (h2 step)

Strategy:
- BLOCKER 1: Use IsFractionRing.injective + helper lemma about equivValuationSubring.symm
- BLOCKER 2: Unfold layers + use definitional equality residueFieldAtPrime = ResidueField
-/

section Cycle59Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 59]
/-- Helper for BLOCKER 1: The composition of algebraMap from Loc.AtPrime to K
with valuationRingAt_equiv_localization' extracts the value in K.
Key property: for x ∈ valuationRingAt, algebraMap Loc K (equiv x) = x.val -/
lemma valuationRingAt_equiv_coe_eq (v : HeightOneSpectrum R)
    (x : valuationRingAt (R := R) (K := K) v) :
    algebraMap (Localization.AtPrime v.asIdeal) K
      ((valuationRingAt_equiv_localization' (R := R) (K := K) v) x) = x.val := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  sorry

-- Candidate 2 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 59]
/-- Helper for BLOCKER 1: equivValuationSubring.symm preserves the embedding to K.
For y ∈ DVR.valuationSubring, algebraMap DVR K (equiv.symm y) = y.val -/
lemma equivValuationSubring_symm_coe (v : HeightOneSpectrum R)
    (y : ((IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K).valuationSubring) :
    algebraMap (Localization.AtPrime v.asIdeal) K
      (IsDiscreteValuationRing.equivValuationSubring.symm y) = y.val := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  sorry

-- Candidate 3 [tag: coercion_simplify] [status: SORRY] [cycle: 59]
/-- Helper for BLOCKER 1: Cast along ValuationSubring equality preserves the value in K.
When h : A = B and x ∈ A, then (h ▸ x).val = x.val in K. -/
lemma cast_valuationSubring_preserves_val (v : HeightOneSpectrum R)
    (h : valuationRingAt (R := R) (K := K) v =
      ((IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K).valuationSubring)
    (x : valuationRingAt (R := R) (K := K) v) :
    (h ▸ x : ((IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K).valuationSubring).val = x.val := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- Cast along equality preserves the underlying value: both subrings live in K
  -- Note: Dependent elimination on ValuationSubring equality is blocked
  sorry

-- Candidate 4 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 59]
/-- BLOCKER 1 using helpers: Combine Candidates 1-3 to prove the main goal.
Strategy: Use IsFractionRing.injective, then apply scalar tower and helper lemmas. -/
lemma valuationRingAt_equiv_algebraMap_via_helpers (v : HeightOneSpectrum R) (r : R) :
    (valuationRingAt_equiv_localization' (R := R) (K := K) v)
      ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩ =
    algebraMap R (Localization.AtPrime v.asIdeal) r := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  apply IsFractionRing.injective (Localization.AtPrime v.asIdeal) K
  -- Use simp to handle dependent type issues with rewrite
  simp only [valuationRingAt_equiv_coe_eq, ← IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal) K r]

-- Candidate 5 [tag: coercion_simplify] [status: SORRY] [cycle: 59]
/-- Helper for BLOCKER 2: Unfolding localization_residue_equiv.symm applied to algebraMap.
Shows that the inverse equivalence maps algebraMap R (Loc ⧸ maxIdeal) r to Quotient.mk v.asIdeal r. -/
lemma localization_residue_equiv_symm_algebraMap (v : HeightOneSpectrum R) (r : R) :
    (localization_residue_equiv v).symm
      (algebraMap R (Localization.AtPrime v.asIdeal ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) r) =
    Ideal.Quotient.mk v.asIdeal r := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  unfold localization_residue_equiv
  rw [RingEquiv.symm_apply_eq]
  unfold IsLocalization.AtPrime.equivQuotMaximalIdeal
  simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

-- Candidate 6 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 59]
/-- Helper for BLOCKER 2: The RingEquiv.ofBijective applied to Quotient.mk equals algebraMap.
Combines Quotient.algebraMap_eq with ofBijective_apply. -/
lemma ofBijective_quotient_mk_eq_algebraMap (v : HeightOneSpectrum R) (r : R) :
    (RingEquiv.ofBijective (algebraMap (R ⧸ v.asIdeal) (residueFieldAtPrime R v))
      (Ideal.bijective_algebraMap_quotient_residueField v.asIdeal))
    (Ideal.Quotient.mk v.asIdeal r) =
    algebraMap R (residueFieldAtPrime R v) r := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  simp only [RingEquiv.ofBijective_apply]
  rw [← Ideal.Quotient.algebraMap_eq]
  rfl

-- Candidate 7 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 59]
/-- BLOCKER 2 intermediate step: After unfolding and using residue_def,
show the key equality using Ideal.Quotient.mk_algebraMap.
Note: residueFieldAtPrime R v = v.asIdeal.ResidueField definitionally.
Key steps:
1. unfold + simp trans
2. rw Quotient.mk_algebraMap
3. Use localization_residue_equiv_symm_algebraMap + ofBijective_quotient_mk_eq_algebraMap -/
lemma localization_residueField_equiv_algebraMap_step (v : HeightOneSpectrum R) (r : R) :
    (localization_residueField_equiv v)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal))
        (algebraMap R (Localization.AtPrime v.asIdeal) r)) =
    algebraMap R (residueFieldAtPrime R v) r := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  -- Strategy: unfold localization_residueField_equiv = (loc_res_equiv).symm.trans h2
  -- Then use helpers: localization_residue_equiv_symm_algebraMap + ofBijective_quotient_mk_eq_algebraMap
  -- BLOCKED: Type coercion between residueFieldAtPrime R v and v.asIdeal.ResidueField
  -- These are definitionally equal but Lean's rewriter treats them as syntactically different
  sorry

-- Candidate 8 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 59]
/-- BLOCKER 2 complete: Combine step lemma with residue_def to finish the proof. -/
lemma localization_residueField_equiv_algebraMap_complete (v : HeightOneSpectrum R) (r : R) :
    (localization_residueField_equiv v)
      (IsLocalRing.residue (Localization.AtPrime v.asIdeal)
        (algebraMap R (Localization.AtPrime v.asIdeal) r)) =
    algebraMap R (residueFieldAtPrime R v) r := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  rw [IsLocalRing.residue_def]
  exact localization_residueField_equiv_algebraMap_step v r

end Cycle59Candidates

/-! ## Cycle 60 Candidates

Focus: Complete BLOCKER 2 (type coercion) and BLOCKER 1 (equivValuationSubring.symm)

Discovery results:
- `Subring.coe_equivMapOfInjective_apply`: (equiv x : S) = f x
- `RingEquiv.subringCongr`: preserves underlying values
- `equivValuationSubring` construction uses these
-/

section Cycle60Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: coercion_simplify] [status: SORRY] [cycle: 60]
/-- Forward direction: equivValuationSubring sends a ∈ DVR to ⟨algebraMap a, _⟩.
Key insight: equivValuationSubring is built from equivMapOfInjective which has
coe_equivMapOfInjective_apply: (equiv x : S) = f x -/
lemma equivValuationSubring_coe (v : HeightOneSpectrum R)
    (a : Localization.AtPrime v.asIdeal) :
    (IsDiscreteValuationRing.equivValuationSubring (K := K) a).val =
    algebraMap (Localization.AtPrime v.asIdeal) K a := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  sorry

-- Candidate 2 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 60]
/-- Key property: equivValuationSubring.symm preserves the embedding to K.
Strategy: Use RingEquiv.apply_symm_apply on the forward direction,
then extract the value component. -/
lemma equivValuationSubring_symm_coe_via_apply_symm (v : HeightOneSpectrum R)
    (y : ((IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K).valuationSubring) :
    algebraMap (Localization.AtPrime v.asIdeal) K
      (IsDiscreteValuationRing.equivValuationSubring.symm y) = y.val := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- Strategy: conv_rhs => rw [← equivValuationSubring.apply_symm_apply y]
  -- Then use equivValuationSubring_coe
  sorry

-- Candidate 3 [tag: coercion_simplify] [status: OK] [cycle: 60]
/-- Type coercion bridge for BLOCKER 2: residueFieldAtPrime R v = v.asIdeal.ResidueField
by definition (abbrev). This is rfl. -/
lemma residueFieldAtPrime_eq_ResidueField (v : HeightOneSpectrum R) :
    residueFieldAtPrime R v = v.asIdeal.ResidueField := rfl

-- Candidate 4 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 60]
/-- BLOCKER 2 step - Try using unfold and explicit type annotations.
Use show to make the type coercion explicit. -/
lemma localization_residueField_equiv_algebraMap_step_v2 (v : HeightOneSpectrum R) (r : R) :
    (localization_residueField_equiv v)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal))
        (algebraMap R (Localization.AtPrime v.asIdeal) r)) =
    algebraMap R (residueFieldAtPrime R v) r := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  -- The helpers are proved:
  -- localization_residue_equiv_symm_algebraMap v r : (loc_res_equiv v).symm (algebraMap ...) = Quotient.mk v.asIdeal r
  -- ofBijective_quotient_mk_eq_algebraMap v r : ofBijective (Quotient.mk ...) = algebraMap R (residueFieldAtPrime R v) r
  -- ISSUE: rw fails because the pattern doesn't match exactly
  -- The LHS after unfold+simp is:
  --   (RingEquiv.ofBijective ...) ((localization_residue_equiv v).symm (Quotient.mk (maxIdeal Loc) (algebraMap R Loc r)))
  -- But localization_residue_equiv_symm_algebraMap talks about algebraMap R (Loc ⧸ maxIdeal) r
  -- Need to first show Quotient.mk_algebraMap equivalence
  sorry

-- Candidate 5 [tag: coercion_simplify] [status: SORRY] [cycle: 60]
/-- Alternative approach: Cast along ValuationSubring equality preserves val.
Both valuationRingAt and DVR.valuationSubring are subtypes of K, so cast preserves val. -/
lemma cast_valuationSubring_val_eq (v : HeightOneSpectrum R)
    (h : valuationRingAt (R := R) (K := K) v =
      ((IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K).valuationSubring)
    (x : valuationRingAt (R := R) (K := K) v) :
    (h ▸ x).val = x.val := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- Cast along equality should preserve the value since both are subtypes of K
  -- Use subst h or induction h
  sorry

-- Candidate 6 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 60]
/-- BLOCKER 1 main lemma via equivValuationSubring.symm.
Combine IsFractionRing.injective with the helper lemmas. -/
lemma valuationRingAt_equiv_algebraMap_v2 (v : HeightOneSpectrum R) (r : R) :
    (valuationRingAt_equiv_localization' (R := R) (K := K) v)
      ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩ =
    algebraMap R (Localization.AtPrime v.asIdeal) r := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  apply IsFractionRing.injective (Localization.AtPrime v.asIdeal) K
  -- Goal: algebraMap Loc K (equiv ⟨algebraMap R K r, _⟩) = algebraMap R K r
  -- LHS: Use valuationRingAt_equiv_coe_eq (once proved)
  -- RHS: Use IsScalarTower.algebraMap_apply
  sorry

-- Candidate 7 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 60]
/-- bridge_residue_algebraMap complete using BLOCKER 2 fix.
Uses residueField_transport_direct + localization_residueField_equiv. -/
lemma bridge_residue_algebraMap_v2 (v : HeightOneSpectrum R) (r : R) :
    (residueFieldBridge_explicit (R := R) (K := K) v)
      ((valuationRingAt.residue (R := R) (K := K) v) ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩) =
    algebraMap R (residueFieldAtPrime R v) r := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- Unfold residueFieldBridge_explicit = h1.trans h2
  -- h1: residueField_transport_direct (via mapEquiv)
  -- h2: localization_residueField_equiv
  sorry

-- Candidate 8 [tag: coercion_simplify] [status: SORRY] [cycle: 60]
/-- Helper for equivValuationSubring_coe: unfold the definition and use
Subring.coe_equivMapOfInjective_apply. -/
lemma equivValuationSubring_coe_unfold (v : HeightOneSpectrum R)
    (a : Localization.AtPrime v.asIdeal) :
    (IsDiscreteValuationRing.equivValuationSubring (K := K) a).val =
    algebraMap (Localization.AtPrime v.asIdeal) K a := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := localizationAtPrime_isDVR v
  haveI : IsFractionRing (Localization.AtPrime v.asIdeal) K := localization_isFractionRing v
  -- equivValuationSubring = (topEquiv.symm.trans (equivMapOfInjective ...)).trans (subringCongr ...)
  -- subringCongr preserves val (both subrings live in K), equivMapOfInjective gives algebraMap
  unfold IsDiscreteValuationRing.equivValuationSubring
  simp only [RingEquiv.trans_apply]
  -- After unfolding: the result is ⟨algebraMap a, _⟩ : valuationSubring
  -- subringCongr just reindexes the Subring but doesn't change the value in K
  sorry

end Cycle60Candidates

end RiemannRochV2
