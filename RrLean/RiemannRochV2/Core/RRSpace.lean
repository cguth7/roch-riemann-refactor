import RrLean.RiemannRochV2.Core.Divisor

/-!
# Riemann-Roch Space L(D) and Dimension ℓ(D)

This module defines the Riemann-Roch space L(D) as a submodule of the fraction field K,
and defines the dimension function ℓ(D) using module length.

## Main Definitions

* `satisfiesValuationCondition R K D f` - Membership condition for L(D)
* `RRModuleV2_real R K D` - The space L(D) as a submodule of K
* `ellV2_real_extended R K D` - Dimension ℓ(D) as ℕ∞
* `ellV2_real R K D` - Dimension ℓ(D) as ℕ (assuming finiteness)

## Main Results

* `RRModuleV2_mono_inclusion` - D ≤ E implies L(D) ⊆ L(E)
* `ellV2_real_mono_extended` - D ≤ E implies ℓ(D) ≤ ℓ(E)
-/

namespace RiemannRochV2

open IsDedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## Riemann-Roch Space L(D)

The key insight is that L(D) = {f ∈ K : ord_v(f) + D(v) ≥ 0 for all v}
where K is the fraction field and ord_v is the valuation at prime v.
-/

-- Candidate 8 [tag: bundle_divisor_bridge] [status: PROVED]
/-- At each height-1 prime v, the localization is a discrete valuation ring.
This is the foundational fact that enables us to define valuations ord_v. -/
instance localization_at_prime_is_dvr (v : HeightOneSpectrum R) :
    IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot _

/-! ## Cycle 18: Valuation-based membership condition

The key insight is that the v-adic valuation from `HeightOneSpectrum.valuation` allows
us to define the membership condition for L(D):

  f ∈ L(D) ⟺ f = 0 ∨ (∀ v, v.valuation K f ≥ WithZero.exp (-D v))

This uses the multiplicative notation where:
- `v.valuation K f : ℤᵐ⁰ = WithZero (Multiplicative ℤ)`
- `WithZero.exp n` embeds n : ℤ into ℤᵐ⁰
- The condition `ord_v(f) + D(v) ≥ 0` becomes `v.valuation K f ≥ WithZero.exp (-D v)`
-/

-- Candidate 2 [tag: membership_condition] [status: PROVED]
/-- The membership condition for L(D): f = 0 or all valuations satisfy ord_v(f) + D(v) ≥ 0.
In multiplicative notation: v.valuation K f ≤ WithZero.exp (D v).

Mathematical explanation:
- Standard convention: ord_v(f) ≥ -D(v) (poles bounded by D)
- Mathlib's multiplicative valuation: v(f) = exp(-ord_v(f))
- So ord_v(f) ≥ -D(v) becomes -ord_v(f) ≤ D(v), i.e., v(f) ≤ exp(D(v))
-/
def satisfiesValuationCondition (D : DivisorV2 R) (f : K) : Prop :=
  f = 0 ∨ ∀ v : HeightOneSpectrum R, v.valuation K f ≤ WithZero.exp (D v)

-- Candidate 3 [tag: rrmodule_real] [status: PROVED]
/-- The Riemann-Roch space L(D) as a submodule of K (REAL VERSION).

L(D) = {f ∈ K : f = 0 ∨ (∀ v, v.valuation K f ≤ WithZero.exp (D v))}

This is the space of functions whose poles are bounded by D. -/
def RRModuleV2_real (D : DivisorV2 R) : Submodule R K where
  carrier := { f | satisfiesValuationCondition R K D f }
  zero_mem' := Or.inl rfl
  add_mem' := fun {a b} ha hb => by
    by_cases h : a + b = 0
    · exact Or.inl h
    · right
      intro v
      rcases ha with rfl | ha'
      · simp only [zero_add] at h ⊢
        rcases hb with rfl | hb'
        · exact absurd rfl h
        · exact hb' v
      rcases hb with rfl | hb'
      · simp only [add_zero] at h ⊢
        exact ha' v
      -- Both a and b are nonzero with valuation bounds
      have hav := ha' v
      have hbv := hb' v
      -- The ultrametric inequality: v(a+b) ≤ max(v(a), v(b))
      calc v.valuation K (a + b)
          ≤ max (v.valuation K a) (v.valuation K b) := by
            exact Valuation.map_add_le_max' (v.valuation K) a b
        _ ≤ WithZero.exp (D v) := by
            exact max_le hav hbv
  smul_mem' := fun r {f} hf => by
    by_cases h : r • f = 0
    · exact Or.inl h
    · right
      intro v
      -- r • f = algebraMap R K r * f for an algebra
      simp only [Algebra.smul_def]
      -- v.valuation K (r * f) = v.valuation K r * v.valuation K f
      rw [(v.valuation K).map_mul]
      rcases hf with rfl | hf'
      · exfalso; apply h; simp only [smul_zero]
      have hfv := hf' v
      -- Key: v.valuation K (algebraMap R K r) ≤ 1 for all r ∈ R
      have hr : v.valuation K (algebraMap R K r) ≤ 1 := by
        exact HeightOneSpectrum.valuation_le_one v r
      -- For ordered monoids: if a ≤ b and c ≤ d then a*c ≤ b*d
      calc v.valuation K (algebraMap R K r) * v.valuation K f
          ≤ 1 * WithZero.exp (D v) := by
            exact mul_le_mul' hr hfv
        _ = WithZero.exp (D v) := by
            exact one_mul _

set_option linter.unusedSectionVars false in
-- Candidate 4 [tag: zero_mem_real] [status: PROVED]
/-- Zero is in L(D) for any divisor D. -/
lemma RRModuleV2_real_zero_mem (D : DivisorV2 R) :
    (0 : K) ∈ (RRModuleV2_real R K D).carrier := Or.inl rfl

set_option linter.unusedSectionVars false in
-- Candidate 7 [tag: inclusion_submodule] [status: PROVED]
/-- When D ≤ E, we have L(D) ⊆ L(E), giving a submodule inclusion. -/
lemma RRModuleV2_mono_inclusion {D E : DivisorV2 R} (hDE : D ≤ E) :
    RRModuleV2_real R K D ≤ RRModuleV2_real R K E := by
  intro f hf
  cases hf with
  | inl h => exact Or.inl h
  | inr h =>
    apply Or.inr
    intro v
    have hDv := hDE v  -- D v ≤ E v
    have hfv := h v    -- v.valuation K f ≤ WithZero.exp (D v)
    -- Since D v ≤ E v, we have WithZero.exp (D v) ≤ WithZero.exp (E v)
    -- So v.valuation K f ≤ WithZero.exp (D v) ≤ WithZero.exp (E v)
    calc v.valuation K f ≤ WithZero.exp (D v) := hfv
       _ ≤ WithZero.exp (E v) := by
           apply WithZero.exp_le_exp.mpr
           exact hDv

/-! ## Cycle 20: ℓ(D) using RRModuleV2_real -/

-- Candidate 1 [tag: rr_bundle_bridge] [status: OK]
/-- The dimension ℓ(D) of L(D) using module length (REAL VERSION).

Uses RRModuleV2_real which has the correct valuation-based membership condition.
Module.length is additive in exact sequences, which is key for proving Riemann-Roch.

Returns ℕ∞ because length can be infinite; we extract ℕ when finite. -/
noncomputable def ellV2_real_extended (D : DivisorV2 R) : ℕ∞ :=
  Module.length R (RRModuleV2_real R K D)

-- Candidate 2 [tag: rr_bundle_bridge] [status: OK]
/-- The dimension ℓ(D) as a natural number (REAL VERSION, assuming finiteness). -/
noncomputable def ellV2_real (D : DivisorV2 R) : ℕ :=
  (ellV2_real_extended R K D).toNat

-- Candidate 3 [tag: rr_bundle_bridge] [status: PROVED]
/-- Monotonicity: D ≤ E implies ℓ(D) ≤ ℓ(E) at the ℕ∞ level.

PROOF STRATEGY:
1. Use RRModuleV2_mono_inclusion (already PROVED) to get L(D) ≤ L(E)
2. Apply Submodule.inclusion to get an injective linear map L(D) →ₗ[R] L(E)
3. Use Submodule.inclusion_injective to verify injectivity
4. Apply Module.length_le_of_injective to get length(L(D)) ≤ length(L(E)) -/
lemma ellV2_real_mono_extended {D E : DivisorV2 R} (hDE : D ≤ E) :
    ellV2_real_extended R K D ≤ ellV2_real_extended R K E := by
  unfold ellV2_real_extended
  -- Get the submodule inclusion L(D) ≤ L(E)
  have hle := RRModuleV2_mono_inclusion R K hDE
  -- Apply Module.length_le_of_injective with the inclusion map
  exact Module.length_le_of_injective
    (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

-- Candidate 4 [tag: rr_bundle_bridge] [status: PROVED]
/-- Monotonicity at the ℕ level: D ≤ E implies ℓ(D) ≤ ℓ(E).

Uses ellV2_real_mono_extended and ENat.toNat_le_toNat.
Note: This requires finiteness of ellV2_real_extended E. Without that hypothesis,
we use the fact that toNat maps ⊤ to 0, so the inequality holds trivially. -/
lemma ellV2_real_mono {D E : DivisorV2 R} (hDE : D ≤ E)
    (hfin : ellV2_real_extended R K E ≠ ⊤) :
    ellV2_real R K D ≤ ellV2_real R K E := by
  unfold ellV2_real
  exact ENat.toNat_le_toNat (ellV2_real_mono_extended R K hDE) hfin

-- Candidate 5 [tag: rr_bundle_bridge] [status: PROVED]
/-- Alternative monotonicity: always holds, but may give 0 for infinite length. -/
lemma ellV2_real_mono' {D E : DivisorV2 R} (hDE : D ≤ E) :
    ellV2_real R K D ≤ ellV2_real R K E ∨ ellV2_real_extended R K E = ⊤ := by
  by_cases h : ellV2_real_extended R K E = ⊤
  · exact Or.inr h
  · exact Or.inl (ellV2_real_mono R K hDE h)

end RiemannRochV2
