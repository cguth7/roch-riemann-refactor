import RrLean.RiemannRochV2.Core.DivisorV3
import RrLean.RiemannRochV2.Core.RRSpace

/-!
# Projective Riemann-Roch Space L(D)

This module defines the Riemann-Roch space L(D) for projective divisors `DivisorV3`,
which include both finite and infinite places.

## Main Definitions

* `satisfiesValuationConditionV3 R K D f` - Membership condition for L(D) at all places
* `RRSpaceV3 R K D` - The carrier set {f ∈ K : f ∈ L(D)}
* `RRModuleV3 k R K D` - The space L(D) as a submodule over base field k

## Key Differences from RRSpace.lean (affine version)

The affine version `RRModuleV2_real` is a `Submodule R K` where:
- Only finite places (HeightOneSpectrum R) are considered
- R-scalars preserve membership because elements of R have valuation ≤ 1 at all finite places

The projective version `RRModuleV3` must be a `Submodule k K` where k is the base field:
- ALL places (finite + registered infinite) are considered
- Elements of R may have valuation > 1 at infinite places (e.g., X ∈ Fq[X] has v_∞(X) = -1)
- Only BASE FIELD elements have valuation ≤ 1 at all places

## Mathematical Background

For f ∈ K and divisor D, we define:
  f ∈ L(D) ⟺ f = 0 ∨ (∀ p : Place R K, ord_p(f) ≥ -D(p))

In multiplicative notation (Mathlib convention):
  f ∈ L(D) ⟺ f = 0 ∨ (∀ p, p.valuation f ≤ WithZero.exp (D p))

## Design Note

We require `HasInfinitePlaces R K` to specify which infinite places to consider.
This avoids issues with arbitrary `InfinitePlace K` values that don't correspond
to actual places on the curve.

For P¹ = RatFunc Fq, k = Fq and constants have valuation = 1 everywhere.
-/

namespace RiemannRochV2

open IsDedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable [hip : HasInfinitePlaces R K]

/-! ## Membership Condition for Projective L(D) -/

/-- The membership condition for L(D) using all registered places (finite + registered infinite).

f ∈ L(D) iff:
  f = 0, OR
  for all finite places v, v(f) ≤ exp(D(finite v)), AND
  for all registered infinite places v, v(f) ≤ exp(D(infinite v))

In additive notation: ord_p(f) ≥ -D(p) (poles bounded by D). -/
def satisfiesValuationConditionV3 (D : DivisorV3 R K) (f : K) : Prop :=
  f = 0 ∨ ((∀ v : HeightOneSpectrum R, (Place.finite v : Place R K).valuation f ≤
              WithZero.exp (D (Place.finite v))) ∧
           (∀ v ∈ hip.infinitePlaces, (Place.infinite v : Place R K).valuation f ≤
              WithZero.exp (D (Place.infinite v))))

/-- Alternative formulation when we want to check a specific infinite place. -/
lemma satisfiesValuationConditionV3_iff_forall_registered (D : DivisorV3 R K) (f : K) :
    satisfiesValuationConditionV3 R K D f ↔
    f = 0 ∨ ((∀ v : HeightOneSpectrum R, (Place.finite v : Place R K).valuation f ≤
                WithZero.exp (D (Place.finite v))) ∧
             (∀ v ∈ hip.infinitePlaces, (Place.infinite v : Place R K).valuation f ≤
                WithZero.exp (D (Place.infinite v)))) := Iff.rfl

/-! ## Carrier Set -/

/-- The carrier set for L(D) - elements satisfying the valuation condition. -/
def RRSpaceV3 (D : DivisorV3 R K) : Set K :=
  { f | satisfiesValuationConditionV3 R K D f }

/-- Zero is in L(D) for any divisor D. -/
lemma zero_mem_RRSpaceV3 (D : DivisorV3 R K) : (0 : K) ∈ RRSpaceV3 R K D :=
  Or.inl rfl

/-- L(D) is closed under addition (uses ultrametric inequality). -/
lemma add_mem_RRSpaceV3 {D : DivisorV3 R K} {a b : K}
    (ha : a ∈ RRSpaceV3 R K D) (hb : b ∈ RRSpaceV3 R K D) :
    a + b ∈ RRSpaceV3 R K D := by
  by_cases h : a + b = 0
  · exact Or.inl h
  · right
    rcases ha with rfl | ⟨ha_fin, ha_inf⟩
    · simp only [zero_add] at h ⊢
      rcases hb with rfl | ⟨hb_fin, hb_inf⟩
      · exact absurd rfl h
      · exact ⟨hb_fin, hb_inf⟩
    rcases hb with rfl | ⟨hb_fin, hb_inf⟩
    · simp only [add_zero] at h ⊢
      exact ⟨ha_fin, ha_inf⟩
    -- Both a and b are nonzero with valuation bounds
    constructor
    · intro v
      have hav := ha_fin v
      have hbv := hb_fin v
      calc (Place.finite v : Place R K).valuation (a + b)
          ≤ max ((Place.finite v).valuation a) ((Place.finite v).valuation b) :=
            Place.valuation_add_le _ a b
        _ ≤ WithZero.exp (D (Place.finite v)) := max_le hav hbv
    · intro v hv
      have hav := ha_inf v hv
      have hbv := hb_inf v hv
      calc (Place.infinite v : Place R K).valuation (a + b)
          ≤ max ((Place.infinite v).valuation a) ((Place.infinite v).valuation b) :=
            Place.valuation_add_le _ a b
        _ ≤ WithZero.exp (D (Place.infinite v)) := max_le hav hbv

/-- L(D) is closed under negation. -/
lemma neg_mem_RRSpaceV3 {D : DivisorV3 R K} {a : K}
    (ha : a ∈ RRSpaceV3 R K D) : -a ∈ RRSpaceV3 R K D := by
  rcases ha with rfl | ⟨ha_fin, ha_inf⟩
  · simp only [neg_zero]; exact Or.inl rfl
  · right
    constructor
    · intro v
      have hav := ha_fin v
      have h_neg : (Place.finite v : Place R K).valuation (-a) = (Place.finite v).valuation a := by
        simp only [Place.valuation_finite]; exact Valuation.map_neg _ a
      rw [h_neg]; exact hav
    · intro v hv
      have hav := ha_inf v hv
      have h_neg : (Place.infinite v : Place R K).valuation (-a) =
          (Place.infinite v : Place R K).valuation a := by
        simp only [Place.valuation_infinite, InfinitePlace.valuation]; exact Valuation.map_neg _ a
      rw [h_neg]; exact hav

/-! ## Monotonicity -/

/-- When D ≤ E pointwise, L(D) ⊆ L(E). -/
lemma RRSpaceV3_mono {D E : DivisorV3 R K} (hDE : D ≤ E) :
    RRSpaceV3 R K D ⊆ RRSpaceV3 R K E := by
  intro f hf
  rcases hf with rfl | ⟨hf_fin, hf_inf⟩
  · exact Or.inl rfl
  · right
    constructor
    · intro v
      have hDv := hDE (Place.finite v)
      have hfv := hf_fin v
      calc (Place.finite v : Place R K).valuation f
          ≤ WithZero.exp (D (Place.finite v)) := hfv
        _ ≤ WithZero.exp (E (Place.finite v)) := WithZero.exp_le_exp.mpr hDv
    · intro v hv
      have hDv := hDE (Place.infinite v)
      have hfv := hf_inf v hv
      calc (Place.infinite v : Place R K).valuation f
          ≤ WithZero.exp (D (Place.infinite v)) := hfv
        _ ≤ WithZero.exp (E (Place.infinite v)) := WithZero.exp_le_exp.mpr hDv

/-! ## Submodule Structure over Base Field -/

/-- Typeclass asserting that constants from k have valuation ≤ 1 at all places.

For P¹ = RatFunc Fq with k = Fq, constants embed as degree-0 rational functions
which have valuation = 1 at all places.

Parameters:
- k: the base field (e.g., Fq)
- R: the Dedekind domain (e.g., Fq[X])
- K: the function field (e.g., RatFunc Fq)

We only require the bound for registered infinite places (those in HasInfinitePlaces.infinitePlaces). -/
class ConstantsValuationBound (k : Type*) (R : Type*) (K : Type*)
    [Field k] [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Algebra k K] [hip : HasInfinitePlaces R K] where
  /-- Elements of k have valuation ≤ 1 at all finite places. -/
  valuation_le_one_finite : ∀ (c : k) (v : HeightOneSpectrum R),
    (Place.finite v : Place R K).valuation (algebraMap k K c) ≤ 1
  /-- Elements of k have valuation ≤ 1 at all registered infinite places. -/
  valuation_le_one_infinite : ∀ (c : k) (v : InfinitePlace K),
    v ∈ hip.infinitePlaces →
    (Place.infinite v : Place R K).valuation (algebraMap k K c) ≤ 1

variable (k : Type*) [Field k] [Algebra k K]

/-- L(D) is closed under scalar multiplication by k, given ConstantsValuationBound. -/
lemma smul_mem_RRSpaceV3 [ConstantsValuationBound k R K] {D : DivisorV3 R K} {c : k} {f : K}
    (hf : f ∈ RRSpaceV3 R K D) : c • f ∈ RRSpaceV3 R K D := by
  by_cases h : c • f = 0
  · exact Or.inl h
  · right
    rcases hf with rfl | ⟨hf_fin, hf_inf⟩
    · exfalso; apply h; simp only [smul_zero]
    constructor
    · intro v
      simp only [Algebra.smul_def]
      rw [Place.valuation_mul]
      have hfv := hf_fin v
      have hc : (Place.finite v : Place R K).valuation (algebraMap k K c) ≤ 1 :=
        ConstantsValuationBound.valuation_le_one_finite c v
      calc (Place.finite v : Place R K).valuation (algebraMap k K c) *
              (Place.finite v).valuation f
          ≤ 1 * WithZero.exp (D (Place.finite v)) := mul_le_mul' hc hfv
        _ = WithZero.exp (D (Place.finite v)) := one_mul _
    · intro v hv
      simp only [Algebra.smul_def]
      rw [Place.valuation_mul]
      have hfv := hf_inf v hv
      have hc : (Place.infinite v : Place R K).valuation (algebraMap k K c) ≤ 1 :=
        ConstantsValuationBound.valuation_le_one_infinite c v hv
      calc (Place.infinite v : Place R K).valuation (algebraMap k K c) *
              (Place.infinite v).valuation f
          ≤ 1 * WithZero.exp (D (Place.infinite v)) := mul_le_mul' hc hfv
        _ = WithZero.exp (D (Place.infinite v)) := one_mul _

/-- L(D) as a submodule over the base field k.

This requires ConstantsValuationBound to ensure scalar multiplication preserves membership. -/
def RRModuleV3 [ConstantsValuationBound k R K] (D : DivisorV3 R K) : Submodule k K where
  carrier := RRSpaceV3 R K D
  zero_mem' := zero_mem_RRSpaceV3 R K D
  add_mem' := add_mem_RRSpaceV3 R K
  smul_mem' := fun _ _ hf => smul_mem_RRSpaceV3 (k := k) (R := R) (K := K) hf

/-- Monotonicity as submodule inclusion. -/
lemma RRModuleV3_mono [ConstantsValuationBound k R K] {D E : DivisorV3 R K} (hDE : D ≤ E) :
    RRModuleV3 (k := k) (R := R) (K := K) D ≤ RRModuleV3 (k := k) (R := R) (K := K) E :=
  RRSpaceV3_mono R K hDE

/-! ## Dimension -/

/-- The dimension ℓ(D) of L(D) as ℕ∞ (may be infinite). -/
noncomputable def ellV3_extended [ConstantsValuationBound k R K] (D : DivisorV3 R K) : ℕ∞ :=
  Module.length k (RRModuleV3 (k := k) (R := R) (K := K) D)

/-- The dimension ℓ(D) as a natural number (assuming finiteness). -/
noncomputable def ellV3 [ConstantsValuationBound k R K] (D : DivisorV3 R K) : ℕ :=
  (ellV3_extended (k := k) (R := R) (K := K) D).toNat

/-- Monotonicity: D ≤ E implies ℓ(D) ≤ ℓ(E) at the ℕ∞ level. -/
lemma ellV3_mono_extended [ConstantsValuationBound k R K] {D E : DivisorV3 R K} (hDE : D ≤ E) :
    ellV3_extended (k := k) (R := R) (K := K) D ≤ ellV3_extended (k := k) (R := R) (K := K) E := by
  unfold ellV3_extended
  have hle : RRModuleV3 (k := k) (R := R) (K := K) D ≤ RRModuleV3 (k := k) (R := R) (K := K) E :=
    RRModuleV3_mono (k := k) (R := R) (K := K) hDE
  exact Module.length_le_of_injective
    (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

/-- Monotonicity at the ℕ level. -/
lemma ellV3_mono [ConstantsValuationBound k R K] {D E : DivisorV3 R K} (hDE : D ≤ E)
    (hfin : ellV3_extended (k := k) (R := R) (K := K) E ≠ ⊤) :
    ellV3 (k := k) (R := R) (K := K) D ≤ ellV3 (k := k) (R := R) (K := K) E := by
  unfold ellV3
  have hmono : ellV3_extended (k := k) (R := R) (K := K) D ≤ ellV3_extended (k := k) (R := R) (K := K) E :=
    ellV3_mono_extended (k := k) (R := R) (K := K) hDE
  exact ENat.toNat_le_toNat hmono hfin

/-! ## Connection to Affine RR Space -/

/-- For divisors supported only at finite places, the projective and affine
conditions agree on finite places. The infinite places need separate handling. -/
lemma satisfiesValuationConditionV3_of_affine {D : DivisorV2 R} {f : K}
    (hf : satisfiesValuationCondition R K D f)
    (hinf : ∀ v ∈ hip.infinitePlaces,
      (Place.infinite v : Place R K).valuation f ≤ WithZero.exp ((DivisorV3.ofAffine (K := K) D) (Place.infinite v))) :
    satisfiesValuationConditionV3 R K (DivisorV3.ofAffine D) f := by
  rcases hf with rfl | hf'
  · left; rfl
  · right
    constructor
    · intro v
      have hfv := hf' v
      simp only [Place.valuation_finite]
      have h_coeff : (DivisorV3.ofAffine (K := K) D) (Place.finite v) = D v := by
        unfold DivisorV3.ofAffine
        rw [Finsupp.mapDomain_apply Place.finite_injective]
      rw [h_coeff]
      exact hfv
    · exact hinf

end RiemannRochV2
