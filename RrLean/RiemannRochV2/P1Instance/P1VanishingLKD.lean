/-
# L(K-D) Vanishing for P¹

This file proves that L(K-D) = 0 for effective divisors D on P¹.

## Main Results

* `RRModuleV3_p1Canonical_sub_eq_bot` - L(K-D) = ⊥ for effective D
* `ellV3_p1Canonical_sub_eq_zero` - ℓ(K-D) = 0 for effective D

## Mathematical Background

For P¹ = RatFunc Fq, the canonical divisor is K = -2[∞].

The key observation is that for any effective divisor D:
- L(K-D) requires ord_∞(f) ≥ 2 (since K(∞) = -2)
- L(K-D) requires ord_v(f) ≥ D(v) ≥ 0 at all finite v

The second condition means f has no finite poles, so f is in the image
of Polynomial Fq → RatFunc Fq. But polynomials have ord_∞(p) = -deg(p) ≤ 0 < 2.

This contradiction shows L(K-D) = {0}.

## Key Insight: Additive vs Multiplicative Convention

In Mathlib:
- v(f) = exp(-ord_v(f)) for the multiplicative valuation
- v(π) = exp(-1) < 1 for uniformizer π (ord(π) = 1)

The L(D) condition v(f) ≤ exp(D(v)) translates to:
- exp(-ord_v(f)) ≤ exp(D(v))
- -ord_v(f) ≤ D(v)
- ord_v(f) ≥ -D(v)

So for K-D with K = -2[∞]:
- At ∞: ord_∞(f) ≥ -K(∞) = -(-2) = 2
- This is impossible for polynomials (which have ord_∞ ≤ 0)

## References

- P1Canonical.lean (canonical divisor K = -2[∞])
- RRSpaceV3.lean (projective L(D))
-/

import RrLean.RiemannRochV2.P1Instance.P1Canonical
import RrLean.RiemannRochV2.Core.RRSpaceV3
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

noncomputable section

open IsDedekindDomain
open scoped Polynomial

namespace RiemannRochV2

/-! ## Polynomial Characterization via Valuations

Key lemma: if f ∈ RatFunc K has v(f) ≤ 1 at all finite places, then f is a polynomial.

The proof uses:
1. f = num/denom with coprime monic denom
2. If denom ≠ 1, some irreducible q divides denom
3. At the HeightOneSpectrum for q: v(denom) < 1 but v(num) = 1 (coprimality)
4. So v(f) = v(num)/v(denom) > 1, contradiction
-/

variable {K : Type*} [Field K]

/-- Construct a HeightOneSpectrum from a prime polynomial. -/
def heightOneSpectrum_of_prime (q : Polynomial K) (hprime : Prime q) :
    HeightOneSpectrum (Polynomial K) :=
  { asIdeal := Ideal.span {q}
    isPrime := (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
    ne_bot := by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hprime.ne_zero }

/-- v(f) ≤ 1 iff v(num) ≤ v(denom) for f = num/denom. -/
lemma valuation_le_one_iff_intValuation_le (f : RatFunc K)
    (v : HeightOneSpectrum (Polynomial K)) :
    v.valuation (RatFunc K) f ≤ 1 ↔ v.intValuation f.num ≤ v.intValuation f.denom := by
  conv_lhs => rw [(RatFunc.num_div_denom f).symm]
  rw [Valuation.map_div]
  simp only [HeightOneSpectrum.valuation_of_algebraMap]
  have hpos : 0 < v.intValuation f.denom := by
    rw [WithZero.pos_iff_ne_zero]
    exact HeightOneSpectrum.intValuation_ne_zero v f.denom (RatFunc.denom_ne_zero f)
  exact div_le_one₀ hpos

/-- If denom ≠ 1, there exists a finite place where v(f) > 1. -/
theorem exists_valuation_not_le_one_of_denom_ne_one (f : RatFunc K) (hdenom : f.denom ≠ 1) :
    ∃ v : HeightOneSpectrum (Polynomial K), ¬(v.valuation (RatFunc K) f ≤ 1) := by
  have hmonic : f.denom.Monic := RatFunc.monic_denom f
  have hne_zero : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have h_not_unit : ¬IsUnit f.denom := fun hu => hdenom (hmonic.eq_one_of_isUnit hu)
  obtain ⟨q, hq_irr, hq_dvd⟩ := WfDvdMonoid.exists_irreducible_factor h_not_unit hne_zero
  have hq_prime : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq_irr
  let v := heightOneSpectrum_of_prime q hq_prime
  use v
  rw [valuation_le_one_iff_intValuation_le]
  have hdenom_lt : v.intValuation f.denom < 1 := by
    rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]
    show f.denom ∈ (heightOneSpectrum_of_prime q hq_prime).asIdeal
    simp only [heightOneSpectrum_of_prime, Ideal.mem_span_singleton]
    exact hq_dvd
  have hcop : IsCoprime f.num f.denom := RatFunc.isCoprime_num_denom f
  have hnum_not_mem : f.num ∉ v.asIdeal := by
    show f.num ∉ (heightOneSpectrum_of_prime q hq_prime).asIdeal
    simp only [heightOneSpectrum_of_prime, Ideal.mem_span_singleton]
    intro hq_dvd_num
    exact hq_prime.not_unit (hcop.isUnit_of_dvd' hq_dvd_num hq_dvd)
  have hnum_eq : v.intValuation f.num = 1 := by
    have hle := HeightOneSpectrum.intValuation_le_one v f.num
    have hlt_iff := HeightOneSpectrum.intValuation_lt_one_iff_mem v f.num
    exact le_antisymm hle (le_of_not_lt (fun hlt => hnum_not_mem (hlt_iff.mp hlt)))
  rw [hnum_eq]
  exact not_le_of_gt hdenom_lt

/-- If v(f) ≤ 1 at all finite places, then f.denom = 1. -/
theorem denom_eq_one_of_valuation_le_one_forall (f : RatFunc K)
    (hf : ∀ v : HeightOneSpectrum (Polynomial K), v.valuation (RatFunc K) f ≤ 1) :
    f.denom = 1 := by
  by_contra hdenom
  obtain ⟨v, hv⟩ := exists_valuation_not_le_one_of_denom_ne_one f hdenom
  exact hv (hf v)

/-- If v(f) ≤ 1 at all finite places, then f = algebraMap(f.num). -/
theorem eq_algebraMap_of_valuation_le_one_forall (f : RatFunc K)
    (hf : ∀ v : HeightOneSpectrum (Polynomial K), v.valuation (RatFunc K) f ≤ 1) :
    f = algebraMap (Polynomial K) (RatFunc K) f.num := by
  have hdenom : f.denom = 1 := denom_eq_one_of_valuation_le_one_forall f hf
  have := RatFunc.num_div_denom f
  rw [hdenom] at this
  simp only [map_one, div_one] at this
  exact this.symm

/-! ## P¹-Specific Lemmas -/

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-! ## Key Lemmas about Infinity Valuation

The infinity valuation on P¹ = RatFunc Fq is given by Mathlib's `inftyValuationDef`:
  v_∞(p) = exp(deg(p)) for nonzero polynomial p

This means:
- v_∞(1) = exp(0) = 1 (constants)
- v_∞(X) = exp(1) > 1 (linear)
- v_∞(X^n) = exp(n) (degree n)

Higher degree polynomials have LARGER valuations at infinity.

For L(K-D) with K = -2[∞]:
- Need v_∞(f) ≤ exp(-2) at infinity
- But polynomials have v_∞(p) = exp(deg(p)) ≥ exp(0) = 1 > exp(-2)

So no nonzero polynomial can satisfy the L(K-D) condition at infinity.
-/

/-- The P¹ infinity valuation of a nonzero polynomial p is exp(deg(p)).

This uses Mathlib's `FunctionField.inftyValuation.polynomial`.
-/
lemma p1InftyValuation_polynomial (p : Polynomial Fq) (hp : p ≠ 0) :
    (p1InftyPlace Fq).valuation (algebraMap (Polynomial Fq) (RatFunc Fq) p) =
    WithZero.exp (p.natDegree : ℤ) := by
  simp only [p1InftyPlace, InfinitePlace.valuation]
  -- The valuation is FunctionField.inftyValuationDef
  exact FunctionField.inftyValuation.polynomial (Fq := Fq) hp

/-- For any nonzero polynomial p, v_∞(p) = exp(deg(p)) ≥ exp(0) = 1.

Since deg(p) ≥ 0 for any polynomial, we have v_∞(p) ≥ 1.
-/
lemma p1InftyValuation_polynomial_ge_one (p : Polynomial Fq) (hp : p ≠ 0) :
    1 ≤ (p1InftyPlace Fq).valuation (algebraMap (Polynomial Fq) (RatFunc Fq) p) := by
  rw [p1InftyValuation_polynomial Fq p hp]
  -- 1 = exp(0) in WithZero (Multiplicative ℤ)
  have h1 : (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 := by
    simp only [WithZero.exp, ofAdd_zero]
    rfl
  rw [h1, WithZero.exp, WithZero.exp, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
  exact Int.natCast_nonneg _

/-- A polynomial cannot satisfy v_∞(p) ≤ exp(-2).

This is the key lemma: for nonzero polynomial p,
  v_∞(p) = exp(deg(p)) with deg(p) ≥ 0
So v_∞(p) ≥ exp(0) = 1 > exp(-2).

Hence v_∞(p) ≤ exp(-2) is impossible for nonzero polynomials.
-/
lemma p1InftyValuation_polynomial_not_le_exp_neg2
    (p : Polynomial Fq) (hp : p ≠ 0) :
    ¬ (p1InftyPlace Fq).valuation (algebraMap (Polynomial Fq) (RatFunc Fq) p) ≤
      WithZero.exp (-2 : ℤ) := by
  rw [p1InftyValuation_polynomial Fq p hp]
  simp only [WithZero.exp, not_le]
  rw [WithZero.coe_lt_coe, Multiplicative.ofAdd_lt]
  have h : 0 ≤ (p.natDegree : ℤ) := Int.natCast_nonneg _
  omega

/-! ## Main Vanishing Theorem -/

/-- The coefficient of K-D at infinity is -2 when D is affine.

For K = -2[∞] and D a DivisorV2 (affine divisor):
- (K - ofAffine D)(∞) = K(∞) - 0 = -2
-/
lemma p1Canonical_sub_ofAffine_at_infty (D : DivisorV2 (Polynomial Fq)) :
    (p1Canonical Fq - DivisorV3.ofAffine (K := RatFunc Fq) D)
      (Place.infinite (p1InftyPlace Fq)) = -2 := by
  simp only [Finsupp.coe_sub, Pi.sub_apply]
  rw [p1Canonical_at_infty]
  -- ofAffine D has 0 at infinite places because it only maps finite places
  have h_ofAffine : (DivisorV3.ofAffine (K := RatFunc Fq) D)
      (Place.infinite (p1InftyPlace Fq)) = 0 := by
    unfold DivisorV3.ofAffine
    -- mapDomain Place.finite maps only to finite places, so infinite places get 0
    rw [Finsupp.mapDomain_notin_range]
    simp only [Set.mem_range, not_exists]
    intro v
    exact fun h => by cases h
  rw [h_ofAffine]
  ring

/-- L(K-D) = {0} for effective divisors D on P¹.

Key argument:
1. L(K-D) requires v_∞(f) ≤ exp(-2) at infinity
2. L(K-D) requires v(f) ≤ exp(-D(v)) ≤ 1 at finite places (since D effective)
3. Condition 2 means f has no finite poles, so f = algebraMap(p) for polynomial p
4. But for polynomial p: v_∞(p) = exp(-deg(p)) ≥ 1 > exp(-2) when deg(p) ≤ 1
5. And for deg(p) ≥ 2, v_∞(p) = exp(-deg(p)) ≤ exp(-2) is possible, but then
   the finite conditions force additional zeros that conflict with the structure

Actually, the clean argument is:
- f ∈ L(K-D) with no finite poles means ord_∞(f) = -deg(f_poly) ≤ 0
- But L(K-D) requires ord_∞(f) ≥ 2
- So 0 ≥ ord_∞(f) ≥ 2 is impossible

This uses that v(f) ≤ exp(D(v)) means ord_v(f) ≥ -D(v), and for K-D:
- At ∞: ord_∞(f) ≥ -(K-D)(∞) = -(-2) = 2
-/
theorem RRSpaceV3_p1Canonical_sub_ofAffine_eq_zero
    {D : DivisorV2 (Polynomial Fq)} (hD : D.Effective) :
    RRSpaceV3 (Polynomial Fq) (RatFunc Fq) (p1Canonical Fq - DivisorV3.ofAffine D) = {0} := by
  ext f
  simp only [Set.mem_singleton_iff]
  constructor
  · -- If f ∈ L(K-D), then f = 0
    intro hf
    by_contra hf_ne
    -- f ∈ L(K-D) and f ≠ 0, so we get the valuation bounds
    rcases hf with rfl | ⟨hf_fin, hf_inf⟩
    · exact hf_ne rfl

    -- Get the infinity condition
    have h_inf_mem : p1InftyPlace Fq ∈ (instHasInfinitePlacesP1 Fq).infinitePlaces := by
      simp [instHasInfinitePlacesP1, p1InfinitePlaces]
    specialize hf_inf (p1InftyPlace Fq) h_inf_mem

    -- The infinity condition says v_∞(f) ≤ exp((K-D)(∞)) = exp(-2)
    have h_coeff : (p1Canonical Fq - DivisorV3.ofAffine (K := RatFunc Fq) D)
        (Place.infinite (p1InftyPlace Fq)) = -2 := p1Canonical_sub_ofAffine_at_infty Fq D
    rw [h_coeff] at hf_inf
    -- So (p1InftyPlace Fq).valuation f ≤ exp(-2)

    -- Step 1: Show v(f) ≤ 1 at all finite places
    -- At finite v: v(f) ≤ exp((K-D)(v)) = exp(-D(v)) ≤ exp(0) = 1 since D effective
    have hf_fin_le_one : ∀ v : HeightOneSpectrum (Polynomial Fq),
        v.valuation (RatFunc Fq) f ≤ 1 := by
      intro v
      have hfv := hf_fin v
      -- (K-D)(finite v) = 0 - D(v) = -D(v)
      have h_coeff_fin : (p1Canonical Fq - DivisorV3.ofAffine (K := RatFunc Fq) D)
          (Place.finite v) = -D v := by
        simp only [Finsupp.coe_sub, Pi.sub_apply]
        rw [p1Canonical_at_finite]
        simp only [DivisorV3.ofAffine, Finsupp.mapDomain_apply Place.finite_injective, zero_sub]
      rw [h_coeff_fin] at hfv
      -- D(v) ≥ 0 since D effective
      have hDv_nonneg : 0 ≤ D v := hD v
      -- exp(-D(v)) ≤ exp(0) = 1
      have h_exp_le : WithZero.exp (-D v) ≤ 1 := by
        have h1 : (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 := by
          simp only [WithZero.exp, ofAdd_zero]; rfl
        rw [h1, WithZero.exp_le_exp]
        omega
      exact le_trans hfv h_exp_le

    -- Step 2: f is a polynomial (f = algebraMap(f.num))
    have hf_poly : f = algebraMap (Polynomial Fq) (RatFunc Fq) f.num :=
      eq_algebraMap_of_valuation_le_one_forall f hf_fin_le_one

    -- Step 3: Polynomials cannot satisfy v_∞(f) ≤ exp(-2)
    have hf_num_ne : f.num ≠ 0 := by
      intro h
      apply hf_ne
      rw [hf_poly, h, map_zero]
    rw [hf_poly] at hf_inf
    exact p1InftyValuation_polynomial_not_le_exp_neg2 Fq f.num hf_num_ne hf_inf

  · -- If f = 0, then f ∈ L(K-D)
    intro hf
    rw [hf]
    exact zero_mem_RRSpaceV3 _ _ _

/-- L(K-D) = ⊥ as a submodule for effective D on P¹. -/
theorem RRModuleV3_p1Canonical_sub_ofAffine_eq_bot
    {D : DivisorV2 (Polynomial Fq)} (hD : D.Effective) :
    RRModuleV3 (k := Fq) (R := Polynomial Fq) (K := RatFunc Fq)
      (p1Canonical Fq - DivisorV3.ofAffine D) = ⊥ := by
  ext f
  simp only [Submodule.mem_bot]
  constructor
  · intro hf
    have h := RRSpaceV3_p1Canonical_sub_ofAffine_eq_zero Fq hD
    simp only [Set.eq_singleton_iff_unique_mem] at h
    exact h.2 f hf
  · intro hf
    rw [hf]
    exact (RRModuleV3 (k := Fq) (R := Polynomial Fq) (K := RatFunc Fq) _).zero_mem

/-- ℓ(K-D) = 0 for effective D on P¹. -/
theorem ellV3_p1Canonical_sub_ofAffine_eq_zero
    {D : DivisorV2 (Polynomial Fq)} (hD : D.Effective) :
    ellV3 (k := Fq) (R := Polynomial Fq) (K := RatFunc Fq)
      (p1Canonical Fq - DivisorV3.ofAffine D) = 0 := by
  unfold ellV3 ellV3_extended
  rw [RRModuleV3_p1Canonical_sub_ofAffine_eq_bot Fq hD]
  simp only [Module.length_bot, ENat.toNat_zero]

end RiemannRochV2

end
