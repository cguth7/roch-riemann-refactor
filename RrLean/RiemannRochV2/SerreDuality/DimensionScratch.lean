import RrLean.RiemannRochV2.SerreDuality.RatFuncFullRR

/-!
# Scratch file for dimension formula development

Goal: Prove ℓ(D) = deg(D) + 1 for effective D with linear place support on P¹.

For P¹ with g = 0:
- K has degree -2
- When deg(D) ≥ 0, deg(K-D) = -2 - deg(D) < 0
- So ℓ(K-D) = 0 (already proved: `ell_canonical_sub_zero`)
- Riemann-Roch becomes: ℓ(D) = deg(D) + 1
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Polynomial RatFunc
open scoped Classical

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-! ## Dimension Formula via Gap Bound

Strategy: Prove by induction on deg(D) using the gap bound.
- Base: ℓ(0) = 1 (proved in RatFuncFullRR)
- Step: ℓ(D + [v]) = ℓ(D) + 1 for linear v

For the step, we need:
1. ℓ(D + [v]) ≤ ℓ(D) + 1 (gap bound, need to prove for projective case)
2. ℓ(D + [v]) ≥ ℓ(D) + 1 (construct explicit element in L(D+[v]) \ L(D))
-/

/-! ## Upper bound: Gap ≤ 1 for projective space -/

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

/-- Gap bound for projective RRSpace: ℓ(D + [v]) ≤ ℓ(D) + 1.

This uses the evaluation map which sends f to its "residue" at v.
The kernel equals L(D), so the quotient has dimension at most 1 (dim κ(v) = 1). -/
theorem ell_ratfunc_projective_gap_le (D : DivisorV2 (Polynomial Fq)) (α : Fq) :
    ell_ratfunc_projective (D + DivisorV2.single (linearPlace α) 1) ≤
    ell_ratfunc_projective D + 1 := by
  -- The proof follows the same structure as gap_le_one_proj_of_rational in Projective.lean
  -- Key: evaluation map has kernel = L(D) and image ⊆ κ(v) which has dim 1
  sorry

/-! ## Lower bound: Explicit elements -/

/-- The valuation of (X-α) at linearPlace α is exp(-1).
Uses intValuation_linearPlace_eq_exp_neg_rootMultiplicity and Polynomial.rootMultiplicity_X_sub_C. -/
lemma valuation_X_sub_at_self (α : Fq) :
    (linearPlace α).valuation (RatFunc Fq) (RatFunc.X - RatFunc.C α) = WithZero.exp (-1 : ℤ) := by
  have heq : RatFunc.X - RatFunc.C α = algebraMap (Polynomial Fq) (RatFunc Fq)
      (Polynomial.X - Polynomial.C α) := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [heq, HeightOneSpectrum.valuation_of_algebraMap]
  rw [intValuation_linearPlace_eq_exp_neg_rootMultiplicity α _ (Polynomial.X_sub_C_ne_zero α)]
  -- rootMultiplicity_X_sub_C : (X - C a).rootMultiplicity a = 1
  simp only [Polynomial.rootMultiplicity_X_sub_C]
  rfl

/-- The valuation of (X-α)⁻¹^k at linearPlace α is exp(k).
Uses valuation_X_sub_at_self, WithZero.exp_inv_eq_neg_int, and WithZero.exp_nsmul. -/
lemma valuation_inv_X_sub_pow_at_self (α : Fq) (k : ℕ) :
    (linearPlace α).valuation (RatFunc Fq) ((RatFunc.X - RatFunc.C α)⁻¹ ^ k) =
    WithZero.exp (k : ℤ) := by
  rw [Valuation.map_pow, Valuation.map_inv, valuation_X_sub_at_self]
  rw [WithZero.exp_inv_eq_neg_int, neg_neg]
  rw [← WithZero.exp_nsmul]
  simp only [nsmul_eq_mul, mul_one]

/-- At a place v ≠ linearPlace α, (X-α) has valuation 1.
Key: if (X-α) ∈ v.asIdeal then v = linearPlace α by maximality.
Proof: v.asIdeal maximal containing irreducible (X-α) must equal span{X-α}. -/
lemma valuation_X_sub_at_other (α : Fq) (v : HeightOneSpectrum (Polynomial Fq))
    (hv : v ≠ linearPlace α) :
    v.valuation (RatFunc Fq) (RatFunc.X - RatFunc.C α) = 1 := by
  have heq : RatFunc.X - RatFunc.C α = algebraMap (Polynomial Fq) (RatFunc Fq)
      (Polynomial.X - Polynomial.C α) := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [heq, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem; apply hv
  -- v.asIdeal is maximal and contains (X-α), so equals span{X-α} = linearPlace α
  have hmax : v.asIdeal.IsMaximal := HeightOneSpectrum.isMaximal v
  have hle : Ideal.span {Polynomial.X - Polynomial.C α} ≤ v.asIdeal := by
    rw [Ideal.span_le]; intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact hmem
  have heq' : v.asIdeal = Ideal.span {Polynomial.X - Polynomial.C α} :=
    (hmax.eq_of_le (Ideal.span_singleton_ne_top (Polynomial.not_isUnit_X_sub_C α)) hle).symm
  exact HeightOneSpectrum.ext _ _ (by simp only [linearPlace, heq'])

/-- 1/(X-α)^k satisfies the valuation condition for k·[linearPlace α]. -/
lemma inv_X_sub_C_pow_satisfies_valuation (α : Fq) (k : ℕ) (hk : k ≠ 0) :
    satisfiesValuationCondition (Polynomial Fq) (RatFunc Fq)
      ((k : ℤ) • DivisorV2.single (linearPlace α) 1)
      ((RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ k) := by
  right
  intro v
  by_cases hv : v = linearPlace α
  · -- At linearPlace α: val = exp(k) ≤ exp(k)
    subst hv
    simp only [Finsupp.smul_apply, smul_eq_mul, DivisorV2.single, Finsupp.single_apply, if_pos rfl,
               mul_one]
    rw [valuation_inv_X_sub_pow_at_self]
  · -- At other places: val = 1 ≤ 1 = exp(0)
    simp only [Finsupp.smul_apply, smul_eq_mul, DivisorV2.single, Finsupp.single_apply]
    have hne : linearPlace (Fq := Fq) α ≠ v := fun h => hv h.symm
    simp only [hne, ↓reduceIte, mul_zero, WithZero.exp_zero]
    rw [Valuation.map_pow, Valuation.map_inv, valuation_X_sub_at_other Fq α v hv]
    simp only [inv_one, one_pow, le_refl]

/-- 1/(X-α)^k has no pole at infinity.
For 1/(X-α)^k: num = 1 (deg 0), denom = (X-α)^k (deg k), so deg(num) ≤ deg(denom).

Note: The proof is blocked by a typeclass instance mismatch with `gcd` between
`Classical.propDecidable` and the default `DecidableEq` instance. The math is trivial:
gcd(1, q) = 1, so num = C(lc⁻¹) * 1 = 1 and denom = C(lc⁻¹) * q = q.
-/
lemma inv_X_sub_C_pow_noPoleAtInfinity (α : Fq) (k : ℕ) (hk : k ≠ 0) :
    noPoleAtInfinity ((RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ k) := by
  -- deg(num) = 0 ≤ k = deg(denom)
  -- Blocked by typeclass instance mismatch with gcd
  sorry

/-- 1/(X-α)^k is in L_proj(k·[linearPlace α]). -/
lemma inv_X_sub_C_pow_mem_projective (α : Fq) (k : ℕ) :
    (RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ k ∈
    RRSpace_ratfunc_projective ((k : ℤ) • DivisorV2.single (linearPlace α) 1) := by
  by_cases hk : k = 0
  · -- k = 0: 1 ∈ L(0)
    subst hk
    simp only [pow_zero, Nat.cast_zero, zero_smul]
    have h1 : (1 : RatFunc Fq) = algebraMap Fq (RatFunc Fq) 1 := by simp
    rw [h1]
    exact constant_mem_projective_zero (1 : Fq)
  · constructor
    · exact inv_X_sub_C_pow_satisfies_valuation Fq α k hk
    · right; exact inv_X_sub_C_pow_noPoleAtInfinity Fq α k hk

/-- 1/(X-α)^k is NOT in L_proj((k-1)·[linearPlace α]) for k ≥ 1.

This shows the gap is exactly 1, not just ≤ 1. -/
lemma inv_X_sub_C_pow_not_mem_projective_smaller (α : Fq) (k : ℕ) (hk : 0 < k) :
    (RatFunc.X (K := Fq) - RatFunc.C α)⁻¹ ^ k ∉
    RRSpace_ratfunc_projective (((k : ℤ) - 1) • DivisorV2.single (linearPlace α) 1) := by
  -- The valuation at linearPlace α is exp(k) > exp(k-1)
  sorry

/-! ## Dimension formula for single-point divisors -/

/-- For D = n·[linearPlace α] with n ≥ 0, ℓ(D) = n + 1. -/
theorem ell_ratfunc_projective_single_linear (α : Fq) (n : ℕ) :
    ell_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1) = n + 1 := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_smul, zero_add]
    exact ell_ratfunc_projective_zero_eq_one Fq
  | succ m ih =>
    -- ℓ((m+1)·[v]) = ℓ(m·[v] + [v])
    have h_eq : ((m + 1 : ℕ) : ℤ) • DivisorV2.single (linearPlace (Fq := Fq) α) 1 =
        (m : ℤ) • DivisorV2.single (linearPlace α) 1 + DivisorV2.single (linearPlace α) 1 := by
      simp only [Nat.cast_succ, add_smul, one_smul]
    rw [h_eq]
    -- Use gap bound for upper and explicit element for lower
    have h_le := ell_ratfunc_projective_gap_le Fq ((m : ℤ) • DivisorV2.single (linearPlace α) 1) α
    have h_ge : ell_ratfunc_projective
        ((m : ℤ) • DivisorV2.single (linearPlace α) 1 + DivisorV2.single (linearPlace α) 1) ≥
        ell_ratfunc_projective ((m : ℤ) • DivisorV2.single (linearPlace α) 1) + 1 := by
      -- The explicit element 1/(X-α)^(m+1) is in L((m+1)·[v]) but not in L(m·[v])
      sorry
    omega

/-! ## General dimension formula -/

/-- For effective D with linear support and deg(D) ≥ 0, ℓ(D) = deg(D) + 1. -/
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective D = D.deg.toNat + 1 := by
  -- Proof by induction on deg(D)
  -- Base case: deg(D) = 0 means D = 0 (since D is effective)
  -- Inductive case: D = D' + [v] for some linear v
  sorry

end RiemannRochV2
