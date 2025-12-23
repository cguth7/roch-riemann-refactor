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
- ALL places (finite + infinite) are considered
- Elements of R may have valuation > 1 at infinite places (e.g., X ∈ Fq[X] has v_∞(X) = -1)
- Only BASE FIELD elements have valuation ≤ 1 at all places

## Mathematical Background

For f ∈ K and divisor D, we define:
  f ∈ L(D) ⟺ f = 0 ∨ (∀ p : Place R K, ord_p(f) ≥ -D(p))

In multiplicative notation (Mathlib convention):
  f ∈ L(D) ⟺ f = 0 ∨ (∀ p, p.valuation f ≤ WithZero.exp (D p))

## Design Note

We parameterize over a base field k with:
- An algebra map k → K (embedding constants)
- A proof that constants have valuation ≤ 1 at all places

For P¹ = RatFunc Fq, k = Fq and constants have valuation = 1 everywhere.
-/

namespace RiemannRochV2

open IsDedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## Membership Condition for Projective L(D) -/

/-- The membership condition for L(D) using all places (finite + infinite).

f ∈ L(D) iff:
  f = 0, OR
  for all places p, the valuation satisfies v_p(f) ≤ exp(D(p))

In additive notation: ord_p(f) ≥ -D(p) (poles bounded by D). -/
def satisfiesValuationConditionV3 (D : DivisorV3 R K) (f : K) : Prop :=
  f = 0 ∨ ∀ p : Place R K, p.valuation f ≤ WithZero.exp (D p)

/-- Alternative formulation: explicit disjunction for each place type. -/
lemma satisfiesValuationConditionV3_iff (D : DivisorV3 R K) (f : K) :
    satisfiesValuationConditionV3 R K D f ↔
    f = 0 ∨ ((∀ v : HeightOneSpectrum R, (Place.finite v : Place R K).valuation f ≤
                WithZero.exp (D (Place.finite v))) ∧
             (∀ v : InfinitePlace K, (Place.infinite v : Place R K).valuation f ≤
                WithZero.exp (D (Place.infinite v)))) := by
  constructor
  · intro h
    rcases h with rfl | h
    · left; rfl
    · right
      constructor
      · intro v; exact h (Place.finite v)
      · intro v; exact h (Place.infinite v)
  · intro h
    rcases h with rfl | ⟨hfin, hinf⟩
    · left; rfl
    · right
      intro p
      cases p with
      | finite v => exact hfin v
      | infinite v => exact hinf v

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
    intro p
    rcases ha with rfl | ha'
    · simp only [zero_add] at h ⊢
      rcases hb with rfl | hb'
      · exact absurd rfl h
      · exact hb' p
    rcases hb with rfl | hb'
    · simp only [add_zero] at h ⊢
      exact ha' p
    -- Both a and b are nonzero with valuation bounds
    have hap := ha' p
    have hbp := hb' p
    -- The ultrametric inequality: v(a+b) ≤ max(v(a), v(b))
    calc p.valuation (a + b)
        ≤ max (p.valuation a) (p.valuation b) := Place.valuation_add_le p a b
      _ ≤ WithZero.exp (D p) := max_le hap hbp

/-- L(D) is closed under negation. -/
lemma neg_mem_RRSpaceV3 {D : DivisorV3 R K} {a : K}
    (ha : a ∈ RRSpaceV3 R K D) : -a ∈ RRSpaceV3 R K D := by
  rcases ha with rfl | ha'
  · simp only [neg_zero]; exact Or.inl rfl
  · right
    intro p
    have hap := ha' p
    -- v(-a) = v(a) for valuations
    have h_neg : p.valuation (-a) = p.valuation a := by
      cases p with
      | finite v => simp only [Place.valuation_finite]; exact Valuation.map_neg _ a
      | infinite v => simp only [Place.valuation_infinite, InfinitePlace.valuation]; exact Valuation.map_neg _ a
    rw [h_neg]
    exact hap

/-! ## Monotonicity -/

/-- When D ≤ E pointwise, L(D) ⊆ L(E). -/
lemma RRSpaceV3_mono {D E : DivisorV3 R K} (hDE : D ≤ E) :
    RRSpaceV3 R K D ⊆ RRSpaceV3 R K E := by
  intro f hf
  rcases hf with rfl | hf'
  · exact Or.inl rfl
  · right
    intro p
    have hDp := hDE p  -- D p ≤ E p
    have hfp := hf' p  -- p.valuation f ≤ WithZero.exp (D p)
    calc p.valuation f
        ≤ WithZero.exp (D p) := hfp
      _ ≤ WithZero.exp (E p) := WithZero.exp_le_exp.mpr hDp

/-! ## Submodule Structure over Base Field -/

/-- Typeclass asserting that constants from k have valuation ≤ 1 at all places.

For P¹ = RatFunc Fq with k = Fq, constants embed as degree-0 rational functions
which have valuation = 1 at all places.

Parameters:
- k: the base field (e.g., Fq)
- R: the Dedekind domain (e.g., Fq[X])
- K: the function field (e.g., RatFunc Fq) -/
class ConstantsValuationBound (k : Type*) (R : Type*) (K : Type*)
    [Field k] [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Algebra k K] where
  /-- Elements of k have valuation ≤ 1 at all places. -/
  valuation_le_one : ∀ (c : k) (p : Place R K), p.valuation (algebraMap k K c) ≤ 1

variable (k : Type*) [Field k] [Algebra k K]

/-- L(D) is closed under scalar multiplication by k, given ConstantsValuationBound. -/
lemma smul_mem_RRSpaceV3 [ConstantsValuationBound k R K] {D : DivisorV3 R K} {c : k} {f : K}
    (hf : f ∈ RRSpaceV3 R K D) : c • f ∈ RRSpaceV3 R K D := by
  by_cases h : c • f = 0
  · exact Or.inl h
  · right
    intro p
    -- c • f = algebraMap k K c * f for an algebra
    simp only [Algebra.smul_def]
    -- p.valuation (c * f) = p.valuation c * p.valuation f
    rw [Place.valuation_mul]
    rcases hf with rfl | hf'
    · exfalso; apply h; simp only [smul_zero]
    have hfp := hf' p
    -- Key: p.valuation (algebraMap k K c) ≤ 1 for all c ∈ k
    have hc : p.valuation (algebraMap k K c) ≤ 1 := ConstantsValuationBound.valuation_le_one c p
    calc p.valuation (algebraMap k K c) * p.valuation f
        ≤ 1 * WithZero.exp (D p) := mul_le_mul' hc hfp
      _ = WithZero.exp (D p) := one_mul _

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
conditions agree on those places. -/
lemma satisfiesValuationConditionV3_of_affine {D : DivisorV2 R} {f : K}
    (hf : satisfiesValuationCondition R K D f)
    (hinf : ∀ v : InfinitePlace K, (Place.infinite v : Place R K).valuation f ≤ 1) :
    satisfiesValuationConditionV3 R K (DivisorV3.ofAffine D) f := by
  rcases hf with rfl | hf'
  · left; rfl
  · right
    intro p
    cases p with
    | finite v =>
      have hfv := hf' v
      simp only [Place.valuation_finite]
      -- Need: D.ofAffine (Place.finite v) = D v
      have h_coeff : (DivisorV3.ofAffine (K := K) D) (Place.finite v) = D v := by
        unfold DivisorV3.ofAffine
        rw [Finsupp.mapDomain_apply Place.finite_injective]
      rw [h_coeff]
      exact hfv
    | infinite v =>
      have hiv := hinf v
      -- D.ofAffine has 0 coefficient at infinite places
      have h_coeff : (DivisorV3.ofAffine (K := K) D) (Place.infinite v) = 0 := by
        -- Place.infinite v is not in the range of Place.finite
        have h_not_finite : ∀ w : HeightOneSpectrum R, Place.finite w ≠ Place.infinite v := by
          intro w h
          cases h
        unfold DivisorV3.ofAffine
        rw [Finsupp.mapDomain_notin_range]
        intro ⟨w, hw⟩
        exact h_not_finite w hw
      rw [h_coeff]
      simp only [WithZero.exp_zero]
      exact hiv

end RiemannRochV2
