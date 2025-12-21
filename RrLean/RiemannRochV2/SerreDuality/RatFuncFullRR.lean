import RrLean.RiemannRochV2.FullRRData
import RrLean.RiemannRochV2.SerreDuality.RatFuncPairing

/-!
# Full Riemann-Roch for RatFunc Fq (Genus 0)

This module instantiates `FullRRData` for `RatFunc Fq`, completing the proof of
Riemann-Roch for the projective line P¹ over a finite field.

## Mathematical Background

For P¹ over Fq:
- genus g = 0
- canonical divisor K has degree -2
- ℓ(D) = max(0, deg(D) + 1) for divisors with linear place support

Since `DivisorV2 R` only covers finite places, we represent the canonical divisor
K = -2[∞] by choosing an equivalent divisor -2·[linearPlace 0]. Any degree -2
divisor works since they're all linearly equivalent on P¹.

## Main Results

* `canonical_ratfunc` - The canonical divisor K = -2·[linearPlace 0]
* `deg_canonical_ratfunc` - deg(K) = -2
* `ell_canonical_sub_zero` - ℓ(K - D) = 0 when deg(D) ≥ -1

## References

* Hartshorne "Algebraic Geometry" Chapter IV, Section 1
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-! ## Canonical Divisor for P¹

For P¹, we choose K = -2·[linearPlace 0] as a representative of the canonical class.
Any degree -2 divisor on P¹ is linearly equivalent to K = -2[∞].
-/

/-- The canonical divisor for RatFunc Fq (P¹ over Fq).
We use -2·[linearPlace 0] as a finite-place representative of K = -2[∞]. -/
def canonical_ratfunc : DivisorV2 (Polynomial Fq) :=
  -2 • DivisorV2.single (linearPlace 0) 1

/-- The genus of P¹ is 0. -/
def genus_ratfunc : ℕ := 0

/-- The canonical divisor has degree -2. -/
theorem deg_canonical_ratfunc : (canonical_ratfunc Fq).deg = -2 := by
  -- Note: We write the proof without referencing genus_ratfunc
  unfold canonical_ratfunc DivisorV2.deg
  -- -2 • single(v, 1) = single(v, -2)
  have h : (-2 : ℤ) • DivisorV2.single (linearPlace (Fq := Fq) 0) 1 =
      DivisorV2.single (linearPlace (Fq := Fq) 0) (-2) := by
    ext w
    simp only [Finsupp.smul_apply, smul_eq_mul, DivisorV2.single, Finsupp.single_apply]
    by_cases hw : w = linearPlace (Fq := Fq) 0 <;> simp [hw]
  rw [h]
  simp only [DivisorV2.single, Finsupp.sum_single_index]

/-- deg(K) = 2g - 2 for g = 0. -/
theorem deg_canonical_eq_formula :
    (canonical_ratfunc Fq).deg = 2 * (genus_ratfunc : ℤ) - 2 := by
  rw [deg_canonical_ratfunc]
  unfold genus_ratfunc
  norm_num

/-! ## Linear Support Preservation

K - D has linear support when D has linear support.
-/

/-- The canonical divisor is supported on linear places. -/
theorem canonical_ratfunc_linear_support : IsLinearPlaceSupport (canonical_ratfunc Fq) := by
  intro v hv
  unfold canonical_ratfunc at hv
  simp only [Finsupp.mem_support_iff, ne_eq] at hv
  -- Support of -2 • single(linearPlace 0, 1) is just {linearPlace 0}
  by_cases heq : v = linearPlace (Fq := Fq) 0
  · exact ⟨0, heq⟩
  · -- v ≠ linearPlace 0, so (K)(v) = 0
    exfalso
    apply hv
    simp only [Finsupp.smul_apply, smul_eq_mul, DivisorV2.single, Finsupp.single_apply]
    -- Goal: -2 * if linearPlace 0 = v then 1 else 0 = 0
    -- Since heq : v ≠ linearPlace 0, we have linearPlace 0 ≠ v
    have heq' : linearPlace (Fq := Fq) 0 ≠ v := fun h => heq h.symm
    simp only [heq', ↓reduceIte, mul_zero]

/-- K - D has linear support when D has linear support. -/
theorem sub_linear_support (D : DivisorV2 (Polynomial Fq))
    (hD : IsLinearPlaceSupport D) :
    IsLinearPlaceSupport (canonical_ratfunc Fq - D) := by
  intro v hv
  simp only [Finsupp.mem_support_iff, ne_eq] at hv
  -- (K - D)(v) = K(v) - D(v) ≠ 0 means K(v) ≠ D(v)
  -- So v ∈ supp(K) ∪ supp(D)
  rw [sub_eq_add_neg, Finsupp.add_apply, Finsupp.neg_apply] at hv
  by_cases hK : (canonical_ratfunc Fq) v ≠ 0
  · -- v ∈ supp(K), so v is linear
    exact canonical_ratfunc_linear_support Fq v (Finsupp.mem_support_iff.mpr hK)
  · -- K(v) = 0, so D(v) ≠ 0 (since K(v) - D(v) ≠ 0)
    push_neg at hK
    rw [hK, zero_add] at hv
    have hD_ne : D v ≠ 0 := by
      intro h
      apply hv
      rw [h, neg_zero]
    have hD_supp : v ∈ D.support := Finsupp.mem_support_iff.mpr hD_ne
    exact hD v hD_supp

/-! ## Serre Duality Equation

For deg(D) ≥ -1:
- deg(K - D) = -2 - deg(D) ≤ -1 < 0
- So ℓ(K - D) = 0 by `ell_ratfunc_projective_zero_of_neg_deg`
- RR becomes: ℓ(D) - 0 = deg(D) + 1
-/

/-- When deg(D) ≥ -1, we have deg(K - D) < 0. -/
theorem deg_canonical_sub_neg (D : DivisorV2 (Polynomial Fq))
    (hD : D.deg ≥ -1) :
    (canonical_ratfunc Fq - D).deg < 0 := by
  rw [sub_eq_add_neg, DivisorV2.deg_add, DivisorV2.deg_neg, deg_canonical_ratfunc]
  omega

/-- ℓ(K - D) = 0 when deg(D) ≥ -1 and D has linear support. -/
theorem ell_canonical_sub_zero (D : DivisorV2 (Polynomial Fq))
    (hD_deg : D.deg ≥ -1) (hD_lin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective (canonical_ratfunc Fq - D) = 0 := by
  apply ell_ratfunc_projective_zero_of_neg_deg
  · exact deg_canonical_sub_neg Fq D hD_deg
  · exact sub_linear_support Fq D hD_lin

/-! ## Projective L(0) = Constants

For the ProperCurve axiom, we need ℓ(0) = 1.
This is proved via `projective_L0_eq_constants` showing L_proj(0) = Fq.
-/

/-- The projective L(0) equals the constants. -/
theorem projective_L0_eq_constants :
    RRSpace_ratfunc_projective (0 : DivisorV2 (Polynomial Fq)) =
    Submodule.map (Algebra.linearMap Fq (RatFunc Fq)) ⊤ := by
  apply le_antisymm
  · -- L_proj(0) ⊆ constants
    intro f hf
    rw [Submodule.mem_map]
    -- f ∈ L_proj(0) means f has no poles anywhere and no pole at infinity
    -- This means f is a constant
    rcases hf with ⟨hval, hinfty⟩
    rcases hinfty with rfl | hf_nopole
    · -- f = 0, which is a constant
      exact ⟨0, Submodule.mem_top, by simp⟩
    · -- noPoleAtInfinity f case (f may still be 0)
      -- f has no poles at finite places (from hval with D = 0)
      -- and no pole at infinity (from hf_nopole)
      -- Such f must be constant
      -- Key: if denom has positive degree, there's a pole, contradicting hval for D = 0

      -- First check if f = 0
      by_cases hf_ne : f = 0
      · -- f = 0 is a constant
        exact ⟨0, Submodule.mem_top, by simp [hf_ne]⟩

      -- Now f ≠ 0, so extract the valuation condition from hval
      have hval_fn : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) f ≤ WithZero.exp ((0 : DivisorV2 (Polynomial Fq)) v) := by
        rcases hval with rfl | hval'
        · exact (hf_ne rfl).elim
        · exact hval'

      -- First show: denom has degree 0
      have hdenom_deg_zero : f.denom.natDegree = 0 := by
        by_contra hdenom_pos'
        push_neg at hdenom_pos'
        have hdenom_pos : 0 < f.denom.natDegree := Nat.pos_of_ne_zero hdenom_pos'

        -- Get an irreducible factor of denom
        have hdenom_ne : f.denom ≠ 0 := f.denom_ne_zero
        have hexists_factor : ∃ π : Polynomial Fq, Irreducible π ∧ π ∣ f.denom :=
          Polynomial.exists_irreducible_of_natDegree_pos hdenom_pos
        obtain ⟨π, hπ_irr, hπ_dvd⟩ := hexists_factor

        -- Define the place v_π corresponding to π
        have hπ_ne : π ≠ 0 := hπ_irr.ne_zero
        let v_π : HeightOneSpectrum (Polynomial Fq) :=
          ⟨Ideal.span {π}, Ideal.span_singleton_prime hπ_ne |>.mpr hπ_irr.prime,
           by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hπ_ne⟩

        -- At v_π, denom has valuation < 1
        have hdenom_in_v : f.denom ∈ v_π.asIdeal := by
          simp only [v_π, Ideal.mem_span_singleton]; exact hπ_dvd
        have hdenom_val_lt : v_π.intValuation f.denom < 1 :=
          (intValuation_lt_one_iff_mem v_π f.denom).mpr hdenom_in_v

        -- Since num and denom are coprime, π ∤ num
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

        -- valuation(f) > 1 at v_π
        have hf_val_gt_one : v_π.valuation (RatFunc Fq) f > 1 := by
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

        -- But hval_fn says valuation ≤ exp(0) = 1 at all places
        have hf_val_le := hval_fn v_π
        -- exp(0) = 1
        simp only [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero] at hf_val_le
        -- Contradiction: valuation > 1 but also ≤ 1
        exact (not_lt.mpr hf_val_le) hf_val_gt_one

      -- Now denom has degree 0, so it's a constant
      have hmonic : f.denom.Monic := RatFunc.monic_denom f
      have hdenom_ne : f.denom ≠ 0 := RatFunc.denom_ne_zero f
      have hdenom_const : ∃ c : Fq, c ≠ 0 ∧ f.denom = Polynomial.C c := by
        rw [Polynomial.natDegree_eq_zero] at hdenom_deg_zero
        obtain ⟨c, hc⟩ := hdenom_deg_zero
        refine ⟨c, ?_, hc.symm⟩
        intro hc_zero
        rw [hc_zero, Polynomial.C_0] at hc
        exact hdenom_ne hc.symm
      obtain ⟨c, hc_ne, hdenom_eq⟩ := hdenom_const

      -- From noPoleAtInfinity: deg(num) ≤ deg(denom) = 0
      have hnum_deg_zero : f.num.natDegree = 0 := by
        have h1 : f.num.natDegree ≤ f.denom.natDegree := hf_nopole
        rw [hdenom_deg_zero] at h1
        exact Nat.eq_zero_of_le_zero h1

      -- num has degree 0, so it's a constant
      rw [Polynomial.natDegree_eq_zero] at hnum_deg_zero
      obtain ⟨n, hnum_eq⟩ := hnum_deg_zero

      -- f = C n / C c = C (n / c), a constant
      use n / c
      constructor
      · exact Submodule.mem_top
      · -- Show algebraMap (n / c) = f
        rw [Algebra.linearMap_apply, ← RatFunc.num_div_denom f, ← hnum_eq, hdenom_eq]
        simp only [RatFunc.algebraMap_C, RatFunc.C]
        have hc_ne' : (algebraMap Fq (RatFunc Fq)) c ≠ 0 := by
          intro h
          rw [map_eq_zero] at h
          exact hc_ne h
        field_simp [hc_ne']
        rw [← map_mul, div_mul_cancel₀ n hc_ne]
  · -- constants ⊆ L_proj(0)
    intro f hf
    rw [Submodule.mem_map] at hf
    obtain ⟨c, _, hc⟩ := hf
    rw [← hc]
    exact constant_mem_projective_zero c

/-- ℓ_proj(0) = 1 for RatFunc Fq. -/
theorem ell_ratfunc_projective_zero_eq_one :
    ell_ratfunc_projective (0 : DivisorV2 (Polynomial Fq)) = 1 := by
  unfold ell_ratfunc_projective
  -- Need to show finrank(L_proj(0)) = 1
  -- L_proj(0) = constants ≅ Fq as Fq-vector space
  rw [projective_L0_eq_constants]

  -- The algebra map Fq → RatFunc Fq is injective
  have halg_inj : Function.Injective (Algebra.linearMap Fq (RatFunc Fq)) := by
    intro x y hxy
    -- Algebra.linearMap_apply gives algebraMap x = algebraMap y
    -- algebraMap Fq (RatFunc Fq) is definitionally RatFunc.C
    -- Need to show RatFunc.C x = RatFunc.C y implies x = y
    have h1 : RatFunc.C x = RatFunc.C y := by
      change algebraMap Fq (RatFunc Fq) x = algebraMap Fq (RatFunc Fq) y
      exact hxy
    exact RatFunc.C_injective h1

  -- The map is a linear equiv from Fq onto its range (image of ⊤)
  -- finrank(map f ⊤) = finrank(range f) = finrank Fq Fq = 1
  have hmap_eq : (Submodule.map (Algebra.linearMap Fq (RatFunc Fq)) ⊤ : Submodule Fq (RatFunc Fq)) =
      LinearMap.range (Algebra.linearMap Fq (RatFunc Fq)) := by
    rw [Submodule.map_top]

  rw [hmap_eq]

  -- Use that finrank of range of injective map equals finrank of domain
  have hrange_finrank : Module.finrank Fq (LinearMap.range (Algebra.linearMap Fq (RatFunc Fq))) =
      Module.finrank Fq Fq := by
    exact (LinearEquiv.ofInjective (Algebra.linearMap Fq (RatFunc Fq)) halg_inj).finrank_eq.symm

  rw [hrange_finrank]
  -- finrank Fq Fq = 1
  exact Module.finrank_self Fq

/-! ## The Riemann-Roch Theorem for P¹

The main RR theorems (riemann_roch_ratfunc, etc.) are in DimensionScratch.lean,
which imports this file and proves the dimension formula ℓ(D) = deg(D) + 1.
-/

end RiemannRochV2
