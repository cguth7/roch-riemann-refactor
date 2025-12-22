import RrLean.RiemannRochV2.SerreDuality.P1Specific.RatFuncPairing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Core Finiteness Results for RRSpace

This module proves `Module.Finite` for `RRSpace_ratfunc_projective (n·[α])` using the
correct mathematical approach: embedding into a known finite-dimensional space.

## Key Principle

**DO NOT** prove `Module.Finite` using `finrank`. This is circular:
- `Module.finite_of_finrank_pos` requires `Module.finrank` to be positive
- `Module.finrank` only gives meaningful values when `Module.Finite` holds

**DO** prove `Module.Finite` by constructing a linear injection into a known finite-dim space:
1. Define `clearPoles : RRSpace(n·[α]) →ₗ[Fq] Polynomial.degreeLT Fq (n+1)`
   by `f ↦ (X-α)^n · f`
2. Show this is well-defined: if f ∈ RRSpace(n·[α]), then (X-α)^n · f is a polynomial
   of degree ≤ n (clears poles at α, and noPoleAtInfinity ⟹ degree ≤ 0 + n = n)
3. Show it's injective: multiplication by nonzero is injective in a domain
4. Conclude: codomain `Polynomial.degreeLT Fq (n+1)` is finite-dim ⟹ domain is finite-dim

## Main Results

* `RRSpace_ratfunc_projective_single_linear_finite` - Module.Finite for L(n·[α])

## References

This is the standard approach in algebraic geometry: L(D) ↪ k^{deg(D)+1} via pole clearing.
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Polynomial RatFunc
open scoped Classical

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-! ## Pole Clearing Map

For f ∈ RRSpace(n·[α]), the function (X-α)^n · f is a polynomial of degree ≤ n.
This gives a linear injection into the finite-dimensional space Fq[X]_{≤n}.
-/

/-! ### Helper lemmas for denom_is_power_of_X_sub -/

/-- At places v ≠ linearPlace α, an element of RRSpace(n·[α]) has valuation ≤ 1. -/
lemma RRSpace_valuation_le_one_at_other_places (α : Fq) (n : ℕ) (f : RatFunc Fq)
    (hf : f ∈ RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1))
    (hf_ne : f ≠ 0) (v : HeightOneSpectrum (Polynomial Fq)) (hv : v ≠ linearPlace α) :
    v.valuation (RatFunc Fq) f ≤ 1 := by
  rcases hf with ⟨hval, _⟩
  rcases hval with rfl | hval'
  · exact (hf_ne rfl).elim
  specialize hval' v
  -- D(v) = 0 for v ≠ linearPlace α
  have hDv : ((n : ℤ) • DivisorV2.single (linearPlace α) 1) v = 0 := by
    simp only [Finsupp.smul_apply, DivisorV2.single, Finsupp.single_apply]
    rw [if_neg (Ne.symm hv), smul_zero]
  rw [hDv, WithZero.exp_zero] at hval'
  exact hval'

/-- If an irreducible π divides f.denom and π ≠ (X-α), then v_π.valuation f > 1. -/
lemma valuation_gt_one_at_other_irreducible (α : Fq) (f : RatFunc Fq) (hf_ne : f ≠ 0)
    (π : Polynomial Fq) (hπ_irr : Irreducible π) (hπ_dvd : π ∣ f.denom)
    (hπ_ne : π ≠ Polynomial.X - Polynomial.C α) :
    let v_π : HeightOneSpectrum (Polynomial Fq) :=
      ⟨Ideal.span {π}, Ideal.span_singleton_prime hπ_irr.ne_zero |>.mpr hπ_irr.prime,
       by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hπ_irr.ne_zero⟩
    v_π.valuation (RatFunc Fq) f > 1 := by
  intro v_π
  have hdenom_ne : f.denom ≠ 0 := f.denom_ne_zero
  -- π | denom implies denom ∈ v_π.asIdeal
  have hdenom_in_v : f.denom ∈ v_π.asIdeal := by
    simp only [v_π, Ideal.mem_span_singleton]; exact hπ_dvd
  have hdenom_val_lt : v_π.intValuation f.denom < 1 :=
    (intValuation_lt_one_iff_mem v_π f.denom).mpr hdenom_in_v
  -- Coprimality: π ∤ num
  have hcop : IsCoprime f.num f.denom := f.isCoprime_num_denom
  have hπ_not_dvd_num : ¬(π ∣ f.num) := by
    intro hπ_dvd_num
    have hdvd_one : π ∣ (1 : Polynomial Fq) := by
      obtain ⟨a, b, hab⟩ := hcop
      calc π ∣ a * f.num + b * f.denom := dvd_add (dvd_mul_of_dvd_right hπ_dvd_num a)
                                                   (dvd_mul_of_dvd_right hπ_dvd b)
         _ = 1 := hab
    exact Irreducible.not_isUnit hπ_irr (isUnit_of_dvd_one hdvd_one)
  have hnum_not_in_v : f.num ∉ v_π.asIdeal := by
    simp only [v_π, Ideal.mem_span_singleton]; exact hπ_not_dvd_num
  have hnum_val_one : v_π.intValuation f.num = 1 :=
    intValuation_eq_one_iff.mpr hnum_not_in_v
  -- Compute valuation(f) = valuation(num) / valuation(denom) = 1 / (< 1) > 1
  rw [← RatFunc.num_div_denom f]
  have hnum_ne : f.num ≠ 0 := by
    intro heq
    have hf_eq_zero : f = 0 := by
      rw [← RatFunc.num_div_denom f, heq, map_zero, zero_div]
    exact hf_ne hf_eq_zero
  have hdenom_alg_ne : algebraMap (Polynomial Fq) (RatFunc Fq) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero hdenom_ne
  rw [Valuation.map_div, v_π.valuation_of_algebraMap, v_π.valuation_of_algebraMap,
      hnum_val_one, one_div]
  have hdenom_mem : f.denom ∈ nonZeroDivisors (Polynomial Fq) :=
    mem_nonZeroDivisors_of_ne_zero hdenom_ne
  have hval_ne : v_π.intValuation f.denom ≠ 0 :=
    v_π.intValuation_ne_zero' ⟨f.denom, hdenom_mem⟩
  have hcoe_val_lt : (v_π.intValuation f.denom : WithZero (Multiplicative ℤ)) < 1 :=
    hdenom_val_lt
  exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr (by exact_mod_cast hval_ne), hcoe_val_lt⟩

/-- The place defined by an irreducible π not associate to (X-α) is not linearPlace α. -/
lemma irreducible_place_ne_linearPlace (α : Fq) (π : Polynomial Fq) (hπ_irr : Irreducible π)
    (hπ_not_assoc : ¬ Associated π (Polynomial.X - Polynomial.C α)) :
    let v_π : HeightOneSpectrum (Polynomial Fq) :=
      ⟨Ideal.span {π}, Ideal.span_singleton_prime hπ_irr.ne_zero |>.mpr hπ_irr.prime,
       by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hπ_irr.ne_zero⟩
    v_π ≠ linearPlace α := by
  intro v_π hcontra
  apply hπ_not_assoc
  -- If v_π = linearPlace α, then span{π} = span{X - α}
  have hspan_eq : Ideal.span {π} = Ideal.span {Polynomial.X - Polynomial.C α} := by
    have h1 : v_π.asIdeal = Ideal.span {π} := rfl
    have h2 : (linearPlace α).asIdeal = Ideal.span {Polynomial.X - Polynomial.C α} := rfl
    rw [← h1, ← h2, hcontra]
  -- In a PID, span{π} = span{X-α} implies π and (X-α) are associates
  rw [Ideal.span_singleton_eq_span_singleton] at hspan_eq
  exact hspan_eq

/-- If (X-α) ∤ R and π | R with π irreducible, then π is not associate to (X-α). -/
lemma irreducible_factor_not_assoc_of_not_dvd (α : Fq) (R π : Polynomial Fq)
    (hπ_irr : Irreducible π) (hπ_dvd : π ∣ R) (hX_not_dvd : ¬ (Polynomial.X - Polynomial.C α) ∣ R) :
    ¬ Associated π (Polynomial.X - Polynomial.C α) := by
  intro hassoc
  apply hX_not_dvd
  -- If π ~ (X-α), then π | R implies (X-α) | R
  -- Associated.dvd_iff_dvd_left : a ~ b → (∀ c, a ∣ c ↔ b ∣ c)
  exact hassoc.dvd_iff_dvd_left.mp hπ_dvd

/-- Helper: If f ∈ RRSpace_ratfunc_projective (n·[α]), then f.denom = (X-α)^m for some m ≤ n.
This is because:
1. At any place v ≠ linearPlace α, val_v(f) ≤ 1, so denom has no other irreducible factors
2. At linearPlace α, val_α(f) ≤ exp(n), so m ≤ n -/
lemma denom_is_power_of_X_sub (α : Fq) (n : ℕ) (f : RatFunc Fq) (hf_ne : f ≠ 0)
    (hf : f ∈ RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) :
    ∃ m : ℕ, m ≤ n ∧ f.denom = (Polynomial.X - Polynomial.C α) ^ m := by
  -- Step 1: Factor denom = (X-α)^m * R where (X-α) ∤ R
  let denom := f.denom
  have hdenom_ne : denom ≠ 0 := f.denom_ne_zero
  have hdenom_monic : denom.Monic := RatFunc.monic_denom f
  let m := denom.rootMultiplicity α
  obtain ⟨R, hdenom_factor, hR_not_dvd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd denom hdenom_ne α

  -- Step 2: Show R has degree 0 by contradiction
  -- If R has positive degree, it has an irreducible factor π with π ∤ (X-α)
  have hR_deg_zero : R.natDegree = 0 := by
    by_contra hR_pos'
    push_neg at hR_pos'
    have hR_pos : 0 < R.natDegree := Nat.pos_of_ne_zero hR_pos'
    -- Get an irreducible factor π of R
    have hR_ne : R ≠ 0 := by
      intro hR_zero
      rw [hR_zero, mul_zero] at hdenom_factor
      exact hdenom_ne hdenom_factor
    obtain ⟨π, hπ_irr, hπ_dvd_R⟩ := Polynomial.exists_irreducible_of_natDegree_pos hR_pos
    -- π is not associate to (X-α) since (X-α) ∤ R
    have hπ_not_assoc := irreducible_factor_not_assoc_of_not_dvd Fq α R π hπ_irr hπ_dvd_R hR_not_dvd
    -- π | denom since π | R and R | denom
    have hπ_dvd_denom : π ∣ denom := by
      calc π ∣ R := hπ_dvd_R
         _ ∣ (Polynomial.X - Polynomial.C α) ^ m * R := dvd_mul_left R _
         _ = denom := hdenom_factor.symm
    -- Define the place v_π
    let v_π : HeightOneSpectrum (Polynomial Fq) :=
      ⟨Ideal.span {π}, Ideal.span_singleton_prime hπ_irr.ne_zero |>.mpr hπ_irr.prime,
       by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hπ_irr.ne_zero⟩
    -- v_π ≠ linearPlace α
    have hv_ne : v_π ≠ linearPlace α := irreducible_place_ne_linearPlace Fq α π hπ_irr hπ_not_assoc
    -- At v_π: valuation(f) > 1
    have hπ_ne : π ≠ Polynomial.X - Polynomial.C α := fun heq =>
      hπ_not_assoc (heq ▸ Associated.refl _)
    have hval_gt : v_π.valuation (RatFunc Fq) f > 1 :=
      valuation_gt_one_at_other_irreducible Fq α f hf_ne π hπ_irr hπ_dvd_denom hπ_ne
    -- But RRSpace membership says valuation ≤ 1 at v_π ≠ linearPlace α
    have hval_le : v_π.valuation (RatFunc Fq) f ≤ 1 :=
      RRSpace_valuation_le_one_at_other_places Fq α n f hf hf_ne v_π hv_ne
    -- Contradiction
    exact not_lt.mpr hval_le hval_gt

  -- Step 3: R is a nonzero constant. Since denom is monic, R must be 1.
  have hR_ne : R ≠ 0 := by
    intro hR_zero
    rw [hR_zero, mul_zero] at hdenom_factor
    exact hdenom_ne hdenom_factor
  rw [Polynomial.natDegree_eq_zero] at hR_deg_zero
  obtain ⟨c, hR_eq⟩ := hR_deg_zero
  have hc_ne : c ≠ 0 := by
    intro hc_zero
    rw [hc_zero, Polynomial.C_0] at hR_eq
    exact hR_ne hR_eq.symm
  -- leadingCoeff(denom) = leadingCoeff((X-α)^m) * leadingCoeff(C c) = 1 * c = c
  have hpow_monic : (Polynomial.X - Polynomial.C α) ^ m |>.Monic :=
    Polynomial.Monic.pow (Polynomial.monic_X_sub_C α) m
  have hprod_ne : ((Polynomial.X - Polynomial.C α) ^ m).leadingCoeff *
      (Polynomial.C c).leadingCoeff ≠ 0 := by
    rw [hpow_monic.leadingCoeff, Polynomial.leadingCoeff_C]
    simp [hc_ne]
  have hlc : denom.leadingCoeff =
      ((Polynomial.X - Polynomial.C α) ^ m).leadingCoeff * (Polynomial.C c).leadingCoeff := by
    rw [hdenom_factor, ← hR_eq]
    exact Polynomial.leadingCoeff_mul' hprod_ne
  rw [hdenom_monic.leadingCoeff, hpow_monic.leadingCoeff, Polynomial.leadingCoeff_C, one_mul] at hlc
  have hc_eq_one : c = 1 := hlc.symm
  have hR_eq_one : R = 1 := by rw [← hR_eq, hc_eq_one, Polynomial.C_1]

  -- Step 4: Show m ≤ n from the valuation bound at linearPlace α
  -- First establish denom = (X-α)^m using hdenom_factor and hR_eq_one
  have hdenom_eq' : denom = (Polynomial.X - Polynomial.C α) ^ m := by
    rw [hdenom_factor, hR_eq_one, mul_one]
  -- Since denom := f.denom by let-binding, we have f.denom = (X-α)^m
  have hfdenom_eq : f.denom = (Polynomial.X - Polynomial.C α) ^ m := hdenom_eq'

  -- Handle m = 0 case
  by_cases hm_zero : m = 0
  · -- Case m = 0
    use 0
    constructor
    · omega
    · simp only [hm_zero, pow_zero] at hfdenom_eq; exact hfdenom_eq
  · -- Case m ≠ 0
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_zero

    -- Get the valuation bound
    rcases hf with ⟨hval, _⟩
    rcases hval with rfl | hval'
    · exact (hf_ne rfl).elim
    specialize hval' (linearPlace α)
    have hD_α : ((n : ℤ) • DivisorV2.single (linearPlace (Fq := Fq) α) 1) (linearPlace α) = n := by
      simp only [Finsupp.smul_apply, DivisorV2.single, Finsupp.single_apply]
      simp only [if_true, smul_eq_mul, mul_one]
    rw [hD_α] at hval'

    -- Compute v(f) = v(num) / v(denom) where v = linearPlace α
    let v := linearPlace (Fq := Fq) α
    have hnum_ne : f.num ≠ 0 := by
      intro heq
      have hf_zero : f = 0 := by rw [← RatFunc.num_div_denom f, heq, map_zero, zero_div]
      exact hf_ne hf_zero
    have hv_val : v.valuation (RatFunc Fq) f =
        (v.intValuation f.num : WithZero (Multiplicative ℤ)) / v.intValuation f.denom := by
      conv_lhs => rw [← RatFunc.num_div_denom f]
      have hdenom_alg_ne : algebraMap (Polynomial Fq) (RatFunc Fq) f.denom ≠ 0 :=
        RatFunc.algebraMap_ne_zero hdenom_ne
      rw [Valuation.map_div, v.valuation_of_algebraMap, v.valuation_of_algebraMap]

    -- v(denom) = exp(-m) via bridge lemma
    have hdenom_bridge : v.intValuation f.denom = WithZero.exp (-(m : ℤ)) := by
      rw [hfdenom_eq]
      have hpow_ne : (Polynomial.X - Polynomial.C α) ^ m ≠ 0 :=
        pow_ne_zero m (Polynomial.X_sub_C_ne_zero α)
      rw [intValuation_linearPlace_eq_exp_neg_rootMultiplicity α _ hpow_ne]
      congr 1
      simp only [neg_inj, Nat.cast_inj]
      exact Polynomial.rootMultiplicity_X_sub_C_pow α m

    -- v(num) = 1 since num coprime to denom = (X-α)^m, so (X-α) ∤ num
    have hX_not_dvd_num : ¬(Polynomial.X - Polynomial.C α) ∣ f.num := by
      intro hdvd
      have hcop : IsCoprime f.num f.denom := f.isCoprime_num_denom
      have hdvd_denom : (Polynomial.X - Polynomial.C α) ∣ f.denom := by
        rw [hfdenom_eq]
        exact dvd_pow_self _ (Nat.pos_iff_ne_zero.mp hm_pos)
      have hdvd_one : (Polynomial.X - Polynomial.C α) ∣ 1 := by
        obtain ⟨a, b, hab⟩ := hcop
        calc (Polynomial.X - Polynomial.C α) ∣ a * f.num + b * f.denom :=
               dvd_add (dvd_mul_of_dvd_right hdvd a) (dvd_mul_of_dvd_right hdvd_denom b)
           _ = 1 := hab
      have hunit : IsUnit (Polynomial.X - Polynomial.C α) := isUnit_of_dvd_one hdvd_one
      have hdeg_pos : 0 < (Polynomial.X - Polynomial.C α).natDegree := by
        rw [Polynomial.natDegree_X_sub_C]; omega
      exact Polynomial.not_isUnit_of_natDegree_pos _ hdeg_pos hunit
    have hnum_not_in : f.num ∉ v.asIdeal := by
      simp only [v, linearPlace, Ideal.mem_span_singleton]
      exact hX_not_dvd_num
    have hnum_val_one : v.intValuation f.num = 1 := intValuation_eq_one_iff.mpr hnum_not_in

    -- v(f) = 1 / exp(-m) = exp(m)
    rw [hnum_val_one, hdenom_bridge] at hv_val
    simp only [one_div, WithZero.exp_neg, inv_inv] at hv_val
    rw [hv_val] at hval'
    -- exp(m) ≤ exp(n) implies m ≤ n
    have hm_le_n : m ≤ n := Int.ofNat_le.mp (WithZero.exp_le_exp.mp hval')

    exact ⟨m, hm_le_n, hfdenom_eq⟩

lemma mul_X_sub_pow_is_polynomial (α : Fq) (n : ℕ) (f : RatFunc Fq)
    (hf : f ∈ RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) :
    ∃ p : Polynomial Fq, (Polynomial.X - Polynomial.C α)^n * RatFunc.num f =
        p * RatFunc.denom f ∧ p.natDegree ≤ n := by
  by_cases hf0 : f = 0
  · use 0
    simp [hf0]
  -- Get denom = (X-α)^m with m ≤ n
  obtain ⟨m, hm_le, hdenom_eq⟩ := denom_is_power_of_X_sub Fq α n f hf0 hf
  -- Define p = (X-α)^(n-m) * num
  use (Polynomial.X - Polynomial.C α) ^ (n - m) * f.num
  constructor
  · -- (X-α)^n * num = p * denom = (X-α)^(n-m) * num * (X-α)^m
    rw [hdenom_eq]
    have hpow : (Polynomial.X - Polynomial.C α) ^ n =
        (Polynomial.X - Polynomial.C α) ^ (n - m) * (Polynomial.X - Polynomial.C α) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hm_le]
    rw [hpow]
    ring
  · -- natDegree(p) ≤ n
    rcases hf with ⟨_, hinfty⟩
    rcases hinfty with rfl | hnopole
    · exact (hf0 rfl).elim
    -- noPoleAtInfinity: num.natDegree ≤ denom.natDegree = m
    have hnum_deg : f.num.natDegree ≤ m := by
      unfold noPoleAtInfinity at hnopole
      rw [hdenom_eq] at hnopole
      simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at hnopole
      exact hnopole
    calc ((Polynomial.X - Polynomial.C α) ^ (n - m) * f.num).natDegree
        ≤ ((Polynomial.X - Polynomial.C α) ^ (n - m)).natDegree + f.num.natDegree := Polynomial.natDegree_mul_le
      _ = (n - m) * (Polynomial.X - Polynomial.C α).natDegree + f.num.natDegree := by
          rw [Polynomial.natDegree_pow]
      _ = (n - m) + f.num.natDegree := by simp [Polynomial.natDegree_X_sub_C]
      _ ≤ (n - m) + m := Nat.add_le_add_left hnum_deg _
      _ = n := Nat.sub_add_cancel hm_le

/-! ## Step 1: Raw function -/

/-- Raw function: extracts the polynomial part of (X-α)^n · f.
This is the underlying function before we prove it's linear. -/
def partialClearPolesFun (α : Fq) (n : ℕ)
    (f : RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) :
    Polynomial.degreeLT Fq (n + 1) := by
  have hpoly := mul_X_sub_pow_is_polynomial Fq α n f.val f.property
  refine ⟨hpoly.choose, ?_⟩
  have hdeg := hpoly.choose_spec.2
  simp only [Polynomial.mem_degreeLT]
  calc hpoly.choose.degree
      ≤ hpoly.choose.natDegree := Polynomial.degree_le_natDegree
    _ ≤ n := Nat.cast_le.mpr hdeg
    _ < n + 1 := by exact_mod_cast Nat.lt_succ_self n

/-! ## Step 2: Specification lemma -/

/-- The polynomial extracted by partialClearPolesFun satisfies the key equation.
In RatFunc: algebraMap p = algebraMap (X-α)^n * f -/
lemma partialClearPolesFun_spec (α : Fq) (n : ℕ)
    (f : RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) :
    algebraMap (Polynomial Fq) (RatFunc Fq) (partialClearPolesFun Fq α n f).val =
    algebraMap (Polynomial Fq) (RatFunc Fq) ((Polynomial.X - Polynomial.C α) ^ n) * f.val := by
  have hpoly := mul_X_sub_pow_is_polynomial Fq α n f.val f.property
  have hspec := hpoly.choose_spec.1
  have hdenom_ne : f.val.denom ≠ 0 := RatFunc.denom_ne_zero f.val
  have hdenom_alg_ne : algebraMap (Polynomial Fq) (RatFunc Fq) f.val.denom ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (Polynomial Fq) (RatFunc Fq))]
    exact hdenom_ne
  have hf_eq : f.val = algebraMap (Polynomial Fq) (RatFunc Fq) f.val.num /
                       algebraMap (Polynomial Fq) (RatFunc Fq) f.val.denom :=
    (RatFunc.num_div_denom f.val).symm
  rw [hf_eq, mul_div_assoc']
  have hspec_lifted := congrArg (algebraMap (Polynomial Fq) (RatFunc Fq)) hspec
  rw [map_mul, map_mul] at hspec_lifted
  rw [eq_div_iff hdenom_alg_ne]
  exact hspec_lifted.symm

/-! ## Step 3: Bundle as LinearMap -/

/-- Partial pole clearing: maps f to the polynomial part of (X-α)^n · f.
This is the linear map version bundled with linearity proofs. -/
def partialClearPoles (α : Fq) (n : ℕ) :
    RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1) →ₗ[Fq]
    Polynomial.degreeLT Fq (n + 1) where
  toFun := partialClearPolesFun Fq α n
  map_add' := fun f g => by
    apply Subtype.ext
    apply IsFractionRing.injective (Polynomial Fq) (RatFunc Fq)
    rw [Submodule.coe_add, map_add]
    rw [partialClearPolesFun_spec, partialClearPolesFun_spec, partialClearPolesFun_spec]
    -- Goal: (X-α)^n * ↑(f + g) = (X-α)^n * ↑f + (X-α)^n * ↑g
    -- Need to unfold ↑(f + g) = ↑f + ↑g first
    simp only [Submodule.coe_add]
    ring
  map_smul' := fun c f => by
    apply Subtype.ext
    apply IsFractionRing.injective (Polynomial Fq) (RatFunc Fq)
    rw [SetLike.val_smul, RingHom.id_apply]
    rw [Algebra.smul_def, map_mul]
    rw [partialClearPolesFun_spec, partialClearPolesFun_spec]
    -- Goal: (X-α)^n * ↑(c • f) = algebraMap c * ((X-α)^n * ↑f)
    simp only [SetLike.val_smul, Algebra.smul_def]
    -- Normalize algebraMap paths: algebraMap Fq (RatFunc Fq) = algebraMap Fq[X] (RatFunc Fq) ∘ algebraMap Fq Fq[X]
    simp only [← IsScalarTower.algebraMap_apply Fq (Polynomial Fq) (RatFunc Fq)]
    ring

/-- Alias: partialClearPoles uses partialClearPolesFun -/
lemma partialClearPoles_spec (α : Fq) (n : ℕ)
    (f : RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) :
    algebraMap (Polynomial Fq) (RatFunc Fq) (partialClearPoles Fq α n f).val =
    algebraMap (Polynomial Fq) (RatFunc Fq) ((Polynomial.X - Polynomial.C α) ^ n) * f.val :=
  partialClearPolesFun_spec Fq α n f

/-- The pole clearing map is injective: if the cleared polynomials are equal, f = g.

The proof uses the fact that if p_f = p_g where (X-α)^n * num = p * denom,
then (X-α)^n * f = (X-α)^n * g (as RatFunc), hence f = g by cancellativity. -/
lemma partialClearPoles_injective (α : Fq) (n : ℕ) :
    Function.Injective (partialClearPoles Fq α n) := by
  intro f g heq
  -- From heq: the polynomials are equal
  have hp_eq : (partialClearPoles Fq α n f).val = (partialClearPoles Fq α n g).val :=
    congrArg Subtype.val heq
  -- Use the spec: algebraMap p_f = algebraMap (X-α)^n * f, same for g
  have hf_spec := partialClearPoles_spec Fq α n f
  have hg_spec := partialClearPoles_spec Fq α n g
  -- From hp_eq: algebraMap p_f = algebraMap p_g
  have halg_eq : algebraMap (Polynomial Fq) (RatFunc Fq) (partialClearPoles Fq α n f).val =
                 algebraMap (Polynomial Fq) (RatFunc Fq) (partialClearPoles Fq α n g).val := by
    rw [hp_eq]
  -- So algebraMap (X-α)^n * f = algebraMap (X-α)^n * g
  rw [hf_spec, hg_spec] at halg_eq
  -- Cancel (X-α)^n (nonzero) from both sides
  have hpow_ne : algebraMap (Polynomial Fq) (RatFunc Fq) ((Polynomial.X - Polynomial.C α) ^ n) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (Polynomial Fq) (RatFunc Fq))]
    exact pow_ne_zero n (Polynomial.X_sub_C_ne_zero α)
  have hval_eq : f.val = g.val := mul_left_cancel₀ hpow_ne halg_eq
  ext
  exact hval_eq

/-! ## Module.Finite Instance

The key instance: RRSpace_ratfunc_projective (n·[α]) is finite-dimensional.
-/

/-- For D = n·[linearPlace α] with n ≥ 0, RRSpace_ratfunc_projective D is finite-dimensional.

The proof constructs a linear injection into Fq[X]_{≤n}, which is finite-dimensional.
-/
instance RRSpace_ratfunc_projective_single_linear_finite (α : Fq) (n : ℕ) :
    Module.Finite Fq (RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) := by
  -- Strategy: embed into Polynomial.degreeLT Fq (n+1) which is finite-dim
  have hinj := partialClearPoles_injective Fq α n
  -- Module.Finite instance for degreeLT comes from Mathlib.RingTheory.Polynomial.DegreeLT
  haveI : Module.Finite Fq (Polynomial.degreeLT Fq (n + 1)) := inferInstance
  exact Module.Finite.of_injective (partialClearPoles Fq α n) hinj

/-! ## Helper lemmas for add_single_finite

These are used in the proof of RRSpace_ratfunc_projective_add_single_finite below.
-/

/-- L_proj(D) ⊆ L_proj(D + [v]) for any linear place v. -/
lemma RRSpace_ratfunc_projective_mono (D : DivisorV2 (Polynomial Fq)) (α : Fq) :
    RRSpace_ratfunc_projective D ≤
    RRSpace_ratfunc_projective (D + DivisorV2.single (linearPlace α) 1) := by
  intro f hf
  rcases hf with ⟨hval, hinfty⟩
  constructor
  · -- Valuation condition for D + [v]
    rcases hval with hzero | hval'
    · left; exact hzero
    right
    intro w
    by_cases hw : w = linearPlace α
    · subst hw
      simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_apply, if_pos rfl]
      calc (linearPlace α).valuation (RatFunc Fq) f
          ≤ WithZero.exp (D (linearPlace α)) := hval' (linearPlace α)
        _ ≤ WithZero.exp (D (linearPlace α) + 1) := by
            apply WithZero.exp_le_exp.mpr; omega
    · simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_apply, hw,
                 if_neg (Ne.symm hw), add_zero]
      exact hval' w
  · exact hinfty

/-- The residue field at a linear place has dimension 1 over Fq.
Uses that κ(v) = Fq[X]/(X-α) ≅ Fq via evaluation at α. -/
lemma linearPlace_residue_finrank (α : Fq) :
    Module.finrank Fq (residueFieldAtPrime (Polynomial Fq) (linearPlace α)) = 1 := by
  -- Fq[X]/span{X-Cα} ≃ₐ[Fq] Fq via quotientSpanXSubCAlgEquiv
  let e_alg : (Polynomial Fq ⧸ (linearPlace (Fq := Fq) α).asIdeal) ≃ₐ[Fq] Fq :=
    Polynomial.quotientSpanXSubCAlgEquiv α
  -- This gives finrank(Fq[X]/I) = finrank(Fq) = 1
  have h1 : Module.finrank Fq (Polynomial Fq ⧸ (linearPlace (Fq := Fq) α).asIdeal) = 1 := by
    rw [← Module.finrank_self Fq]
    exact LinearEquiv.finrank_eq e_alg.toLinearEquiv
  -- Now we need: finrank(κ(v)) = finrank(R/I) via the bijective algebraMap
  haveI hmax : (linearPlace (Fq := Fq) α).asIdeal.IsMaximal := (linearPlace α).isMaximal
  have hbij := Ideal.bijective_algebraMap_quotient_residueField (linearPlace (Fq := Fq) α).asIdeal
  -- Build RingEquiv from the bijective algebraMap
  let e_ring : (Polynomial Fq ⧸ (linearPlace (Fq := Fq) α).asIdeal) ≃+*
      residueFieldAtPrime (Polynomial Fq) (linearPlace α) :=
    RingEquiv.ofBijective _ hbij
  -- Upgrade to AlgEquiv: need to show algebraMap commutes
  have hcomm : ∀ c : Fq, e_ring (algebraMap Fq (Polynomial Fq ⧸ (linearPlace (Fq := Fq) α).asIdeal) c) =
      algebraMap Fq (residueFieldAtPrime (Polynomial Fq) (linearPlace α)) c := fun c => by
    simp only [e_ring, RingEquiv.ofBijective_apply]
    rfl
  let e_alg' : (Polynomial Fq ⧸ (linearPlace (Fq := Fq) α).asIdeal) ≃ₐ[Fq]
      residueFieldAtPrime (Polynomial Fq) (linearPlace α) :=
    AlgEquiv.ofRingEquiv hcomm
  rw [← h1]
  exact LinearEquiv.finrank_eq e_alg'.symm.toLinearEquiv

/-- Finiteness for D + [v] when D is finite-dim and v is a linear place.

The proof uses Module.Finite.of_submodule_quotient: if N ⊆ M is a submodule and both
N and M/N are Module.Finite, then M is Module.Finite.

We take M = L(D + [α]), N = LD (the embedding of L(D)).
- N ≅ L(D) is finite by hypothesis
- M/N injects into κ(α) which has dimension 1 (from gap bound proof structure)
-/
instance RRSpace_ratfunc_projective_add_single_finite (α : Fq)
    (D : DivisorV2 (Polynomial Fq))
    [hD : Module.Finite Fq (RRSpace_ratfunc_projective D)] :
    Module.Finite Fq (RRSpace_ratfunc_projective (D + DivisorV2.single (linearPlace α) 1)) := by
  let v := linearPlace (Fq := Fq) α
  let big := RRSpace_ratfunc_projective (D + DivisorV2.single v 1)
  let small := RRSpace_ratfunc_projective D

  -- small ≤ big as submodules of RatFunc Fq
  have hmono : small ≤ big := RRSpace_ratfunc_projective_mono Fq D α

  -- LD := small viewed as a submodule of ↥big
  let LD := small.comap big.subtype

  -- Step 1: LD is Module.Finite (isomorphic to small which is finite by hD)
  have h_range : small ≤ LinearMap.range big.subtype := by
    rw [Submodule.range_subtype]; exact hmono
  let e : LD ≃ₗ[Fq] small :=
    Submodule.comap_equiv_self_of_inj_of_le (Submodule.injective_subtype big) h_range
  haveI hLD : Module.Finite Fq LD := Module.Finite.equiv e.symm

  -- Step 2: The quotient big/LD is Module.Finite
  -- The quotient injects into κ(v) which has dimension 1

  -- Build the projective evaluation map ψ : ↥big →ₗ[Fq] κ(v)
  have h_proj_to_affine : ∀ f, f ∈ big →
      f ∈ RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1) :=
    fun f hf => hf.1
  let φ := evaluationMapAt_complete (R := Polynomial Fq) (K := RatFunc Fq) v D
  let ψ : ↥big →ₗ[Fq] residueFieldAtPrime (Polynomial Fq) v := {
    toFun := fun x => φ ⟨x.val, h_proj_to_affine x.val x.property⟩
    map_add' := fun x y => by
      have := φ.map_add ⟨x.val, h_proj_to_affine x.val x.property⟩
          ⟨y.val, h_proj_to_affine y.val y.property⟩
      convert this using 1 <;> rfl
    map_smul' := fun c x => by
      have h1 : (c • x).val = (algebraMap Fq (Polynomial Fq) c) • x.val :=
        (IsScalarTower.algebraMap_smul (Polynomial Fq) c x.val).symm
      have hmem : (algebraMap Fq (Polynomial Fq) c) • x.val ∈
          RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1) :=
        Submodule.smul_mem _ _ (h_proj_to_affine x.val x.property)
      have h2 : φ ⟨(algebraMap Fq (Polynomial Fq) c) • x.val, hmem⟩ =
          (algebraMap Fq (Polynomial Fq) c) • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ := by
        convert φ.map_smul (algebraMap Fq (Polynomial Fq) c) ⟨x.val, h_proj_to_affine x.val x.property⟩
      have h3 : (algebraMap Fq (Polynomial Fq) c) • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ =
          c • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ :=
        IsScalarTower.algebraMap_smul (Polynomial Fq) c _
      simp only [RingHom.id_apply]
      calc φ ⟨(c • x).val, h_proj_to_affine (c • x).val (c • x).property⟩
          = φ ⟨(algebraMap Fq (Polynomial Fq) c) • x.val, hmem⟩ := by simp only [h1]
        _ = (algebraMap Fq (Polynomial Fq) c) • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ := h2
        _ = c • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ := h3
  }

  -- Show LD ≤ ker(ψ)
  have hle := divisor_le_add_single D v
  have h_LD_le_ker : LD ≤ LinearMap.ker ψ := by
    intro x hx
    rw [LinearMap.mem_ker]
    rw [Submodule.mem_comap] at hx
    have h_affine_mem : x.val ∈ RRModuleV2_real (Polynomial Fq) (RatFunc Fq) D := hx.1
    have h_in_affine_Dv : x.val ∈ RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1) :=
      RRModuleV2_mono_inclusion (Polynomial Fq) (RatFunc Fq) hle h_affine_mem
    let y_affine : RRModuleV2_real (Polynomial Fq) (RatFunc Fq) D := ⟨x.val, h_affine_mem⟩
    have hinc : (⟨x.val, h_in_affine_Dv⟩ : RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1)) =
        Submodule.inclusion (RRModuleV2_mono_inclusion (Polynomial Fq) (RatFunc Fq) hle) y_affine := rfl
    show ψ x = 0
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
    have hx_eq : (⟨x.val, h_proj_to_affine x.val x.property⟩ :
        RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1)) =
        ⟨x.val, h_in_affine_Dv⟩ := rfl
    rw [hx_eq, hinc]
    exact LD_element_maps_to_zero v D y_affine

  -- Show ker(ψ) ≤ LD
  have h_ker_le_LD : LinearMap.ker ψ ≤ LD := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk] at hx
    have h_in_ker : (⟨x.val, h_proj_to_affine x.val x.property⟩ :
        RRModuleV2_real (Polynomial Fq) (RatFunc Fq) (D + DivisorV2.single v 1)) ∈
        LinearMap.ker φ := hx
    rw [kernel_evaluationMapAt_complete_proof, LinearMap.mem_range] at h_in_ker
    obtain ⟨y, hy⟩ := h_in_ker
    rw [Submodule.mem_comap, Submodule.coe_subtype]
    have hval : y.val = x.val := congrArg Subtype.val hy
    have h_affine : x.val ∈ RRModuleV2_real (Polynomial Fq) (RatFunc Fq) D := by
      rw [← hval]; exact y.property
    have h_infty : x.val = 0 ∨ noPoleAtInfinity x.val := x.property.2
    exact ⟨h_affine, h_infty⟩

  -- LD = ker(ψ)
  have h_eq_ker : LD = LinearMap.ker ψ := le_antisymm h_LD_le_ker h_ker_le_LD

  -- κ(v) is finite-dimensional over Fq (dimension 1)
  haveI hκv_finite : Module.Finite Fq (residueFieldAtPrime (Polynomial Fq) v) := by
    have hfr : Module.finrank Fq (residueFieldAtPrime (Polynomial Fq) v) = 1 :=
      linearPlace_residue_finrank Fq α
    have hpos : 0 < Module.finrank Fq (residueFieldAtPrime (Polynomial Fq) v) := by omega
    exact Module.finite_of_finrank_pos hpos

  -- The quotient big/LD injects into κ(v), so it's finite
  haveI hquot : Module.Finite Fq (↥big ⧸ LD) := by
    let desc := Submodule.liftQ LD ψ h_LD_le_ker
    have h_desc_inj : Function.Injective desc := by
      rw [← LinearMap.ker_eq_bot]
      have hker := Submodule.ker_liftQ LD ψ h_LD_le_ker
      rw [hker, h_eq_ker, Submodule.mkQ_map_self]
    exact Module.Finite.of_injective desc h_desc_inj

  -- Apply Module.Finite.of_submodule_quotient
  exact Module.Finite.of_submodule_quotient LD

/-! ## Zero Divisor Finiteness

The base case: RRSpace_ratfunc_projective 0 is 1-dimensional (just the constants).
-/

/-- RRSpace_ratfunc_projective 0 is finite-dimensional (dimension 1). -/
instance RRSpace_ratfunc_projective_zero_finite :
    Module.Finite Fq (RRSpace_ratfunc_projective (0 : DivisorV2 (Polynomial Fq))) := by
  -- L(0) consists of functions with no poles and no pole at infinity
  -- These are exactly the constants: k ⊆ L(0) ⊆ k
  -- So dim L(0) = 1
  -- Use the single linear place instance with n = 0
  have h_eq : (0 : DivisorV2 (Polynomial Fq)) =
      ((0 : ℕ) : ℤ) • DivisorV2.single (linearPlace (Fq := Fq) 0) 1 := by simp
  rw [h_eq]
  exact RRSpace_ratfunc_projective_single_linear_finite Fq 0 0

end RiemannRochV2
