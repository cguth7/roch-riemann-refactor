import RrLean.RiemannRochV2.FullRRData
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
  if hI : I = 0 then 0 else
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
