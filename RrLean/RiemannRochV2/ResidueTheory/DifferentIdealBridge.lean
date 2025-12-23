import RrLean.RiemannRochV2.Definitions.FullRRData
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Bridge between Different Ideal and DivisorV2

This module provides the bridge between Mathlib's `differentIdeal` and `FractionalIdeal`
machinery and our `DivisorV2` representation.

## Main Definitions

* `fractionalIdealToDivisor` : Convert a fractional ideal to a divisor using `count`
* `divisorToFractionalIdeal` : Convert a divisor to a fractional ideal

## References

* `Mathlib.RingTheory.DedekindDomain.Factorization` for `FractionalIdeal.count`
* `Mathlib.RingTheory.DedekindDomain.Different` for `differentIdeal`, `traceDual`
-/

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## Fractional Ideal to Divisor Bridge -/

section FractionalIdealBridge

open FractionalIdeal

open Classical in
/-- Convert a fractional ideal to a divisor using the count function. -/
noncomputable def fractionalIdealToDivisor (I : FractionalIdeal R⁰ K) : DivisorV2 R :=
  if _hI : I = 0 then 0 else
    (finite_factors I).toFinset.sum fun v => Finsupp.single v (count K v I)

/-- Convert a divisor to a fractional ideal. -/
noncomputable def divisorToFractionalIdeal (D : DivisorV2 R) : FractionalIdeal R⁰ K :=
  D.prod fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n

/-- The count of a fractional ideal at v equals the coefficient in the divisor. -/
lemma fractionalIdealToDivisor_apply {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (v : HeightOneSpectrum R) :
    fractionalIdealToDivisor R K I v = count K v I := by
  classical
  simp only [fractionalIdealToDivisor, dif_neg hI]
  rw [Finset.sum_apply']
  by_cases hv : v ∈ (finite_factors I).toFinset
  · simp only [Finsupp.single_apply]
    rw [Finset.sum_eq_single v]
    · simp only [ite_true]
    · intro w _ hw
      simp only [hw, ite_false]
    · intro hv'
      exact absurd hv hv'
  · simp only [Finsupp.single_apply]
    have h_zero : count K v I = 0 := by
      have : v ∉ {w | count K w I ≠ 0} := by
        simp only [Set.mem_setOf_eq, ne_eq, not_not]
        by_contra h_ne
        exact hv ((finite_factors I).mem_toFinset.mpr h_ne)
      simpa using this
    rw [Finset.sum_eq_zero]
    · exact h_zero.symm
    intro w hw
    by_cases hvw : w = v
    · subst hvw
      exact absurd hw hv
    · simp [hvw]

/-- Negation of divisor corresponds to inverse of fractional ideal. -/
lemma fractionalIdealToDivisor_inv {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    fractionalIdealToDivisor R K I⁻¹ = -fractionalIdealToDivisor R K I := by
  ext v
  simp only [Finsupp.coe_neg, Pi.neg_apply]
  by_cases hI_inv : I⁻¹ = 0
  · simp only [inv_eq_zero] at hI_inv
    exact absurd hI_inv hI
  rw [fractionalIdealToDivisor_apply R K hI_inv, fractionalIdealToDivisor_apply R K hI]
  exact count_inv K v I

/-- Multiplication corresponds to addition of divisors. -/
lemma fractionalIdealToDivisor_mul {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    fractionalIdealToDivisor R K (I * J) =
      fractionalIdealToDivisor R K I + fractionalIdealToDivisor R K J := by
  ext v
  simp only [Finsupp.coe_add, Pi.add_apply]
  have hIJ : I * J ≠ 0 := mul_ne_zero hI hJ
  rw [fractionalIdealToDivisor_apply R K hIJ, fractionalIdealToDivisor_apply R K hI,
      fractionalIdealToDivisor_apply R K hJ]
  exact count_mul K v hI hJ

/-! ## Valuation-Membership Bridge

The key connection between fractional ideal membership and valuations.
For `x ∈ K`, we have:
- `x ∈ divisorToFractionalIdeal R K D` iff `∀ v, v.valuation K x ≤ exp(-D v)`

This connects our valuation-based L(D) definition to fractional ideals.
-/

section ValuationMembership

open FractionalIdeal

/-- The count of divisorToFractionalIdeal at v equals D v.
This is the key property: div(I_D) = D. -/
lemma count_divisorToFractionalIdeal (D : DivisorV2 R) (v : HeightOneSpectrum R) :
    count K v (divisorToFractionalIdeal R K D) = D v := by
  -- divisorToFractionalIdeal D = D.prod (fun v n => P_v^n)
  -- By count_finsuppProd: count v (D.prod ...) = D v
  unfold divisorToFractionalIdeal
  exact count_finsuppProd K v D

/-- For nonzero x, the valuation equals exp(-count(spanSingleton x)).
This connects FractionalIdeal.count to HeightOneSpectrum.valuation. -/
lemma valuation_eq_exp_neg_count (v : HeightOneSpectrum R) (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-count K v (spanSingleton R⁰ x)) := by
  classical
  -- Write x = n/d for n : R, d : R⁰
  obtain ⟨⟨n, d, hd⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ x
  simp only [IsFractionRing.mk'_eq_div] at hx ⊢
  have hn : n ≠ 0 := by
    intro h
    simp [h] at hx
  have hd' : (d : R) ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨d, hd⟩
  -- v.valuation K (n/d) = v.intValuation n / v.intValuation d
  rw [map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
  -- v.intValuation r = exp(-count v (span {r}))
  rw [v.intValuation_if_neg hn, v.intValuation_if_neg hd']
  -- count (spanSingleton (n/d)) = count(span{n}) - count(span{d})
  have h_count : count K v (spanSingleton R⁰ (algebraMap R K n / algebraMap R K d)) =
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n})).factors -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d})).factors := by
    have h_ne : spanSingleton R⁰ (algebraMap R K n / algebraMap R K d) ≠ 0 := by
      rw [spanSingleton_ne_zero_iff]
      exact hx
    exact count_well_defined K v h_ne (by
      rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, mul_comm,
          ← div_eq_mul_inv])
  rw [h_count]
  -- Now simplify: exp(-a) / exp(-b) = exp(-a) * exp(b) = exp(b - a)
  rw [div_eq_mul_inv, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_add]
  congr 1
  ring

/-- Fractional ideal ordering is characterized by count at all primes. -/
lemma le_iff_forall_count_ge {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J ↔ ∀ v : HeightOneSpectrum R, count K v J ≤ count K v I := by
  constructor
  · intro h v
    exact count_mono K v hI h
  · intro h
    -- Strategy: show I * J⁻¹ ≤ 1, then I ≤ J
    -- Step 1: I * J⁻¹ has non-negative counts at all primes
    have hK : I * J⁻¹ ≠ 0 := mul_ne_zero hI (inv_ne_zero hJ)
    have h_counts_nonneg : ∀ v, 0 ≤ count K v (I * J⁻¹) := by
      intro v
      rw [count_mul K v hI (inv_ne_zero hJ), count_inv]
      linarith [h v]
    -- Step 2: A fractional ideal with all nonneg counts is ≤ 1
    -- Key: use factorization I * J⁻¹ = ∏ v^{count v (I*J⁻¹)} where all exponents ≥ 0
    have h_le_one : I * J⁻¹ ≤ 1 := by
      -- Use the factorization: I * J⁻¹ = ∏ᶠ v, v^{count K v (I * J⁻¹)}
      rw [← @FractionalIdeal.finprod_heightOneSpectrum_factorization' R _ K _ _ _ _ (I * J⁻¹) hK]
      -- Each factor v^n with n ≥ 0 is ≤ 1 (it's an ideal)
      -- The product of things ≤ 1 is ≤ 1
      -- For fractional ideals: if A ≤ 1 and B ≤ 1, then A * B ≤ 1 * B = B ≤ 1
      refine finprod_induction (p := (· ≤ 1)) le_rfl ?_ ?_
      · intro A B hA hB
        calc A * B ≤ 1 * B := by gcongr
          _ = B := one_mul B
          _ ≤ 1 := hB
      · intro v
        -- Show v^{count K v (I * J⁻¹)} ≤ 1 when the count is ≥ 0
        have h_nonneg := h_counts_nonneg v
        obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h_nonneg
        rw [hn, zpow_natCast]
        -- (v.asIdeal)^n as an ideal, coerced to FractionalIdeal, is ≤ 1
        have : ((v.asIdeal ^ n : Ideal R) : FractionalIdeal R⁰ K) ≤ 1 := coeIdeal_le_one
        rwa [coeIdeal_pow] at this
    -- Step 3: Conclude I ≤ J
    calc I = I * 1 := (mul_one I).symm
      _ = I * (J⁻¹ * J) := by rw [inv_mul_cancel₀ hJ]
      _ = (I * J⁻¹) * J := by ring
      _ ≤ 1 * J := by gcongr
      _ = J := one_mul J

/-- Membership in divisorToFractionalIdeal is characterized by valuation bounds.

This is the key bridge between our valuation-based L(D) and fractional ideal membership.
For nonzero x ∈ K:
  x ∈ I_D  ⟺  (x) ≤ I_D  ⟺  count v (x) ≥ D v for all v  ⟺  v(x) ≤ exp(-D v) for all v

Note: The condition `v.valuation K x ≤ exp(-D v)` means:
- If D v > 0: x must vanish to order ≥ D v at v (zero of order D v)
- If D v < 0: x may have a pole of order ≤ |D v| at v
- If D v = 0: x has no pole at v
-/
lemma mem_divisorToFractionalIdeal_iff (D : DivisorV2 R) (x : K) :
    x ∈ divisorToFractionalIdeal R K D ↔
      x = 0 ∨ ∀ v : HeightOneSpectrum R, v.valuation K x ≤ WithZero.exp (-D v) := by
  by_cases hx : x = 0
  · -- Case x = 0: 0 is in every fractional ideal
    simp only [hx, true_or, iff_true]
    exact zero_mem _
  · -- Case x ≠ 0
    simp only [hx, false_or]
    -- x ∈ I ↔ spanSingleton x ≤ I
    rw [← spanSingleton_le_iff_mem]
    -- divisorToFractionalIdeal is nonzero (product of nonzero terms)
    have h_ne : divisorToFractionalIdeal R K D ≠ 0 := by
      unfold divisorToFractionalIdeal
      rw [Finsupp.prod, Finset.prod_ne_zero_iff]
      intro v _
      exact zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)
    have hx_ne : spanSingleton R⁰ x ≠ 0 := spanSingleton_ne_zero_iff.mpr hx
    -- Use le_iff_forall_count_ge
    rw [le_iff_forall_count_ge R K hx_ne h_ne]
    -- Rewrite count of divisorToFractionalIdeal
    simp only [count_divisorToFractionalIdeal]
    -- Now need: D v ≤ count K v (spanSingleton x) ↔ v.valuation K x ≤ exp(-D v)
    -- Key: exp is monotone, so exp(-a) ≤ exp(-b) ↔ -a ≤ -b ↔ b ≤ a
    constructor
    · intro h v
      -- h : ∀ v, D v ≤ count K v (spanSingleton x)
      rw [valuation_eq_exp_neg_count R K v x hx]
      rw [WithZero.exp_le_exp]
      -- Need: -count K v (spanSingleton x) ≤ -D v
      -- From h v: D v ≤ count K v (spanSingleton x)
      linarith [h v]
    · intro h v
      -- h: ∀ v, v.valuation K x ≤ exp(-D v)
      specialize h v
      rw [valuation_eq_exp_neg_count R K v x hx] at h
      rw [WithZero.exp_le_exp] at h
      -- h : -count K v (spanSingleton x) ≤ -D v
      -- Need: D v ≤ count K v (spanSingleton x)
      linarith

end ValuationMembership

end FractionalIdealBridge

/-! ## Canonical Divisor from Different Ideal

The canonical divisor K corresponds to the inverse of the different ideal,
viewed as a fractional ideal.

In the AKLB setting:
- A is the base ring (e.g., integers of k(t))
- K_A is the fraction field of A (e.g., k(t))
- R = B is the extension ring
- K = L is the fraction field of B

The different ideal `differentIdeal A R` is an ideal of R, and by
`coeIdeal_differentIdeal`: `↑(differentIdeal A R) = (dual A K_A 1)⁻¹`

So the canonical divisor is div((dual 1)) = -div(differentIdeal).
-/

section CanonicalDivisor

variable {R K}
variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
variable (K_A : Type*) [Field K_A] [Algebra A K_A] [IsFractionRing A K_A]
variable [Algebra A R] [Algebra A K] [Algebra K_A K] [NoZeroSMulDivisors A R]
variable [IsScalarTower A K_A K] [IsScalarTower A R K]
variable [FiniteDimensional K_A K] [Algebra.IsSeparable K_A K]
variable [IsIntegralClosure R A K] [IsFractionRing R K]

open FractionalIdeal

/-- The canonical divisor as a DivisorV2.

The canonical divisor corresponds to `(differentIdeal A R)⁻¹` viewed as a divisor.
So canonicalDivisor = -div(differentIdeal). -/
noncomputable def canonicalDivisorFrom : DivisorV2 R :=
  -fractionalIdealToDivisor R K (↑(differentIdeal A R) : FractionalIdeal R⁰ K)

/-- The dual of a fractional ideal corresponds to K - div(I) as a divisor.

By `dual_eq_mul_inv`: `dual A K_A I = dual A K_A 1 * I⁻¹`
And `coeIdeal_differentIdeal`: `↑(differentIdeal A R) = (dual A K_A 1)⁻¹`
So `dual 1 = (↑differentIdeal)⁻¹`

In terms of divisors:
  `div(dual I) = div(dual 1) - div(I) = K - div(I)` -/
lemma fractionalIdealToDivisor_dual {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    fractionalIdealToDivisor R K (dual A K_A I) =
      canonicalDivisorFrom (R := R) (K := K) A - fractionalIdealToDivisor R K I := by
  have h_dual_ne : dual A K_A I ≠ 0 := dual_ne_zero A K_A hI
  have h_dual_one_ne : dual A K_A (1 : FractionalIdeal R⁰ K) ≠ 0 := dual_ne_zero A K_A one_ne_zero
  rw [dual_eq_mul_inv A K_A I]
  rw [fractionalIdealToDivisor_mul R K h_dual_one_ne (inv_ne_zero hI)]
  rw [fractionalIdealToDivisor_inv R K hI]
  simp only [sub_eq_add_neg]
  congr 1
  -- Now show: div(dual 1) = canonicalDivisorFrom
  unfold canonicalDivisorFrom
  -- By coeIdeal_differentIdeal: ↑(differentIdeal A R) = (dual A K_A 1)⁻¹
  -- So dual A K_A 1 = (↑(differentIdeal A R))⁻¹
  have h_diff := coeIdeal_differentIdeal A K_A K R
  -- h_diff : ↑(differentIdeal A R) = (dual A K_A 1)⁻¹
  have h_dual_eq : dual A K_A (1 : FractionalIdeal R⁰ K) =
      (↑(differentIdeal A R) : FractionalIdeal R⁰ K)⁻¹ := by
    simp only [h_diff, inv_inv]
  rw [h_dual_eq]
  -- Need to show: (differentIdeal A R : FractionalIdeal R⁰ K) ≠ 0 for the inverse
  have h_diff_ne : (↑(differentIdeal A R) : FractionalIdeal R⁰ K) ≠ 0 := by
    -- The differentIdeal A R is nonzero (non-bot) under our assumptions.
    -- We need to show: differentIdeal A R ≠ ⊥, then convert via coeIdeal_ne_zero.
    --
    -- Mathlib's differentIdeal_ne_bot requires:
    --   [Module.Finite A R] and [Algebra.IsSeparable (FractionRing A) (FractionRing R)]
    --
    -- We have:
    --   - IsIntegralClosure R A K gives Module.Finite A R (via IsIntegralClosure.finite)
    --   - Algebra.IsSeparable K_A K where K_A ≃ FractionRing A, K ≃ FractionRing R
    --
    -- For now, we state this as a hypothesis that can be discharged later.
    -- Track B TODO: Construct the Algebra (FractionRing A) (FractionRing R) instance
    -- and transfer separability to apply differentIdeal_ne_bot directly.
    haveI : IsNoetherianRing A := inferInstance
    haveI : Module.Finite A R := IsIntegralClosure.finite A K_A K R
    -- The different ideal is nonzero in any finite separable extension
    -- For now we use the fact that it equals (dual 1)⁻¹ and dual 1 ≠ 0
    have h1 : dual A K_A (1 : FractionalIdeal R⁰ K) ≠ 0 := dual_ne_zero A K_A one_ne_zero
    rw [h_diff]
    exact inv_ne_zero h1
  rw [fractionalIdealToDivisor_inv R K h_diff_ne]

end CanonicalDivisor

end RiemannRochV2
