import RrLean.RiemannRochV2.ResidueTheory.ResidueAtX

/-!
# Residue at Linear Places (X - α) for RatFunc Fq

For the place (X - α) where α ∈ Fq, the residue is the coefficient of (X - α)^{-1}
in the Laurent expansion at X = α.

For a rational function f = p/q with (X - α) dividing q exactly once (simple pole),
the residue is p(α) / (q/(X-α))(α).

For f = c/(X - α), the residue at α is simply c.

## Definition

`residueAtLinear` is defined via: multiply f by (X - α), then evaluate at α.
This works correctly for simple poles but returns 0 for higher-order poles,
which breaks additivity.

For a truly linear residue functional, use `residueAt` from `ResidueLinearCorrect.lean`
which is defined via translation to the origin.

## References

- Rosen "Number Theory in Function Fields" Chapter 4
- Stichtenoth "Algebraic Function Fields and Codes" Section 1.4
-/

noncomputable section

open scoped LaurentSeries
open HahnSeries Polynomial

namespace RiemannRochV2.Residue

variable {Fq : Type*} [Field Fq]

/-- The residue at the place (X - α) for a rational function.

This is defined via: multiply f by (X - α), then evaluate at α.
If f has no pole at α, the result is 0.
If f has a simple pole at α, the result is the residue.
If f has a higher-order pole, the multiplication doesn't fully cancel it,
and evaluation gives 0/0 which Lean handles as 0.

Key properties:
- residueAtLinear α (c/(X - α)) = c for c ∈ Fq (simple pole)
- residueAtLinear α (polynomial) = 0 (no pole)
- residueAtLinear α (1/(X - α)²) = 0 (higher-order pole, no X^{-1} term)
-/
def residueAtLinear (α : Fq) (f : RatFunc Fq) : Fq :=
  -- Multiply by (X - C α) to potentially cancel the pole
  let g := (RatFunc.X - RatFunc.C α) * f
  -- Evaluate at α: this extracts the residue for simple poles
  -- For no pole: (X - α) * f evaluates to 0 at α
  -- For simple pole: (X - α) * (p/(X - α)) = p, evaluates to p(α)
  -- For higher pole: still has pole, eval gives 0 by convention
  g.num.eval α / g.denom.eval α

/-- residueAtLinear agrees with residueAtX at α = 0 for simple poles.

At the place (X - 0) = (X), both definitions should give the same result.
However, they use different computational approaches:
- residueAtX uses Laurent series coeff(-1)
- residueAtLinear uses multiplication and evaluation

For simple poles, they agree. This is a sanity check.
-/
theorem residueAtLinear_zero_eq_residueAtX_simple (c : Fq) :
    residueAtLinear (0 : Fq) (c • RatFunc.X⁻¹) = residueAtX (c • RatFunc.X⁻¹) := by
  simp only [residueAtLinear]
  -- RatFunc.C 0 = 0, so X - C 0 = X
  have hC0 : (RatFunc.C (0 : Fq) : RatFunc Fq) = 0 := map_zero _
  simp only [hC0, sub_zero]
  -- g = X * (c • X⁻¹) = c • (X * X⁻¹) = c • 1 = c
  have h : (RatFunc.X : RatFunc Fq) * (c • RatFunc.X⁻¹) = RatFunc.C c := by
    rw [mul_smul_comm, mul_inv_cancel₀ RatFunc.X_ne_zero, Algebra.smul_def, mul_one,
        ← RatFunc.algebraMap_eq_C]
  rw [h]
  simp only [RatFunc.num_C, RatFunc.denom_C]
  simp only [Polynomial.eval_C, Polynomial.eval_one, div_one]
  -- Now show this equals residueAtX (c • X⁻¹) = c
  rw [residueAtX_smul]
  simp only [residueAtX_inv_X, smul_eq_mul, mul_one]

/-- The residue at α of c/(X - α) is c.

This is the fundamental test case: a simple pole with residue c.
-/
theorem residueAtLinear_inv_X_sub (α c : Fq) :
    residueAtLinear α (c • (RatFunc.X - RatFunc.C α)⁻¹) = c := by
  simp only [residueAtLinear]
  -- g = (X - C α) * (c • (X - C α)⁻¹) = c • ((X - C α) * (X - C α)⁻¹) = c • 1 = c
  have hne : (RatFunc.X : RatFunc Fq) - RatFunc.C α ≠ 0 := by
    intro h
    have heq : (RatFunc.X : RatFunc Fq) = RatFunc.C α := sub_eq_zero.mp h
    -- X ≠ C α since their num/denom are different
    have hX_num : (RatFunc.X : RatFunc Fq).num = Polynomial.X := RatFunc.num_X
    have hC_num : (RatFunc.C α : RatFunc Fq).num = Polynomial.C α := RatFunc.num_C α
    rw [heq] at hX_num
    rw [hX_num] at hC_num
    -- X ≠ C α as polynomials
    have : Polynomial.X = Polynomial.C α := hC_num
    have hdeg := congr_arg Polynomial.natDegree this
    simp only [Polynomial.natDegree_X, Polynomial.natDegree_C] at hdeg
    omega
  have h : (RatFunc.X - RatFunc.C α) * (c • (RatFunc.X - RatFunc.C α)⁻¹) = RatFunc.C c := by
    rw [mul_smul_comm, mul_inv_cancel₀ hne, Algebra.smul_def, mul_one, ← RatFunc.algebraMap_eq_C]
  rw [h]
  simp only [RatFunc.num_C, RatFunc.denom_C]
  simp only [Polynomial.eval_C, Polynomial.eval_one, div_one]

/-- The residue at α of a polynomial is 0 (no pole at any finite place). -/
theorem residueAtLinear_polynomial (α : Fq) (p : Polynomial Fq) :
    residueAtLinear α (algebraMap (Polynomial Fq) (RatFunc Fq) p) = 0 := by
  simp only [residueAtLinear]
  -- g = (X - C α) * p, which is a polynomial
  have h : (RatFunc.X - RatFunc.C α) * (algebraMap (Polynomial Fq) (RatFunc Fq) p) =
           algebraMap (Polynomial Fq) (RatFunc Fq) ((Polynomial.X - Polynomial.C α) * p) := by
    rw [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub, ← map_mul]
  rw [h]
  simp only [RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp only [Polynomial.eval_one, div_one]
  -- ((X - C α) * p).eval α = (X - C α)(α) * p(α) = 0 * p(α) = 0
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  ring

/-- Residue at a linear place of zero is zero. -/
@[simp]
theorem residueAtLinear_zero (α : Fq) : residueAtLinear α (0 : RatFunc Fq) = 0 := by
  simp only [residueAtLinear, mul_zero]
  rw [RatFunc.num_zero, RatFunc.denom_zero]
  simp

/-- Residue at a linear place respects scalar multiplication.

For c ∈ Fq and f : RatFunc Fq:
  res_α(c • f) = c • res_α(f)
-/
theorem residueAtLinear_smul (α : Fq) (c : Fq) (f : RatFunc Fq) :
    residueAtLinear α (c • f) = c * residueAtLinear α f := by
  by_cases hc : c = 0
  · simp [hc, residueAtLinear_zero]
  · -- c ≠ 0 case: Use that c • f = (C c / 1) * f = C c * f
    -- and exploit the linearity structure
    simp only [residueAtLinear]
    -- (X - C α) * (c • f) = c • ((X - C α) * f)
    have hcomm : (RatFunc.X - RatFunc.C α) * (c • f) = c • ((RatFunc.X - RatFunc.C α) * f) := by
      rw [mul_smul_comm]
    simp only [hcomm]
    set g := (RatFunc.X - RatFunc.C α) * f with hg_def
    -- c • g = (C c) * g
    have hsmul_eq : c • g = RatFunc.C c * g := by
      rw [Algebra.smul_def, RatFunc.algebraMap_eq_C]
    rw [hsmul_eq]
    have hCc_ne : (RatFunc.C c : RatFunc Fq) ≠ 0 := by
      intro h
      have : c = 0 := by
        have heq : RatFunc.C c = RatFunc.C 0 := by simp only [h, map_zero]
        exact RatFunc.C_injective heq
      exact hc this
    -- Use num_denom_mul relation
    have hCc_denom : (RatFunc.C c : RatFunc Fq).denom = 1 := RatFunc.denom_C c
    have hCc_num : (RatFunc.C c : RatFunc Fq).num = Polynomial.C c := RatFunc.num_C c
    have hmul := RatFunc.num_denom_mul (RatFunc.C c) g
    rw [hCc_denom, one_mul, hCc_num] at hmul
    have heval := congr_arg (Polynomial.eval α) hmul
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at heval
    -- heval: (C c * g).num.eval α * g.denom.eval α = c * g.num.eval α * (C c * g).denom.eval α
    by_cases hgd : g.denom.eval α = 0
    · -- g has a pole at α
      simp only [hgd, div_zero, mul_zero]
      rw [hgd, mul_zero] at heval
      -- Need: (C c * g).num / (C c * g).denom = 0
      -- From heval: 0 = c * g.num.eval α * (C c * g).denom.eval α
      -- If (C c * g).denom.eval α ≠ 0 and c ≠ 0, then g.num.eval α = 0
      -- But g.num and g.denom are coprime, so if denom.eval = 0, num.eval ≠ 0
      -- This means (C c * g).denom.eval α = 0
      -- Actually, simpler: just show the division is 0/0 = 0 or num = 0
      by_cases hcgd : (RatFunc.C c * g).denom.eval α = 0
      · simp [hcgd]
      · -- (C c * g).denom ≠ 0 but g.denom = 0
        -- From heval: 0 = c * g.num.eval α * (C c * g).denom.eval α
        -- Since c ≠ 0 and (C c * g).denom.eval α ≠ 0, we get g.num.eval α = 0
        have hgn : g.num.eval α = 0 := by
          by_contra hgn_ne
          have h0 : c * g.num.eval α * (RatFunc.C c * g).denom.eval α = 0 := heval.symm
          simp only [mul_eq_zero, hc, hgn_ne, hcgd, or_self] at h0
        -- But g.num and g.denom are coprime, so both can't be roots at the same point
        -- This is a contradiction via polynomial coprimality
        have hcoprime := RatFunc.isCoprime_num_denom g
        -- If eval at α is 0 for both, then (X - α) divides both
        -- But gcd(num, denom) = 1, so (X - α) | 1, contradiction
        exfalso
        have hroot_denom : Polynomial.IsRoot g.denom α := by
          rwa [Polynomial.IsRoot.def]
        have hroot_num : Polynomial.IsRoot g.num α := by
          rwa [Polynomial.IsRoot.def]
        have hdvd_denom := Polynomial.dvd_iff_isRoot.mpr hroot_denom
        have hdvd_num := Polynomial.dvd_iff_isRoot.mpr hroot_num
        have hXa_ne : Polynomial.X - Polynomial.C α ≠ 0 := by
          intro h
          have := congr_arg Polynomial.natDegree h
          simp at this
        have hdeg : (Polynomial.X - Polynomial.C α).natDegree = 1 := Polynomial.natDegree_X_sub_C α
        have hdvd1 : (Polynomial.X - Polynomial.C α) ∣ 1 := by
          have h1 := hcoprime.isUnit_of_dvd' hdvd_num hdvd_denom
          exact h1.dvd
        have hdeg1 := Polynomial.natDegree_le_of_dvd hdvd1 one_ne_zero
        rw [hdeg, Polynomial.natDegree_one] at hdeg1
        omega
    · -- g.denom.eval α ≠ 0
      -- Key: (C c * g).denom divides g.denom, so if g.denom.eval α ≠ 0,
      -- then (C c * g).denom.eval α ≠ 0 as well
      have hcgd : (RatFunc.C c * g).denom.eval α ≠ 0 := by
        intro hcgd_zero
        -- (C c * g).denom divides g.denom (from denom_mul_dvd)
        have hdvd := RatFunc.denom_mul_dvd (RatFunc.C c) g
        rw [hCc_denom, one_mul] at hdvd
        -- If p | q and p.eval α = 0, then q.eval α = 0
        have heval_zero := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd hcgd_zero
        exact hgd heval_zero
      -- Now both denominators are nonzero at α, use the relation
      -- heval: (C c * g).num.eval α * g.denom.eval α = c * g.num.eval α * (C c * g).denom.eval α
      -- Goal: (C c * g).num.eval α / (C c * g).denom.eval α = c * (g.num.eval α / g.denom.eval α)
      have h1 : (RatFunc.C c * g).num.eval α / (RatFunc.C c * g).denom.eval α =
                ((RatFunc.C c * g).num.eval α * g.denom.eval α) / ((RatFunc.C c * g).denom.eval α * g.denom.eval α) := by
        field_simp [hgd, hcgd]
      have h2 : c * (g.num.eval α / g.denom.eval α) =
                (c * g.num.eval α * (RatFunc.C c * g).denom.eval α) / ((RatFunc.C c * g).denom.eval α * g.denom.eval α) := by
        field_simp [hgd, hcgd]
      rw [h1, h2, heval]

/-- Auxiliary lemma: for rational functions with the same denominator after multiplication by (X - α),
    the residue is additive.

This is the key step for proving residueAtLinear_add. -/
private lemma residueAtLinear_add_aux (α : Fq) (f g : RatFunc Fq)
    (hf_denom : ((RatFunc.X - RatFunc.C α) * f).denom.eval α ≠ 0)
    (hg_denom : ((RatFunc.X - RatFunc.C α) * g).denom.eval α ≠ 0) :
    residueAtLinear α (f + g) = residueAtLinear α f + residueAtLinear α g := by
  simp only [residueAtLinear, mul_add]
  set fX := (RatFunc.X - RatFunc.C α) * f with hfX_def
  set gX := (RatFunc.X - RatFunc.C α) * g with hgX_def
  -- The goal is now in terms of fX + gX
  -- Use RatFunc.num_denom_add for (fX + gX)
  have hadd := RatFunc.num_denom_add fX gX
  -- hadd : (fX + gX).num * (fX.denom * gX.denom) = (fX.num * gX.denom + fX.denom * gX.num) * (fX + gX).denom
  have heval := congr_arg (Polynomial.eval α) hadd
  simp only [Polynomial.eval_mul, Polynomial.eval_add] at heval
  -- Goal: (fX + gX).num.eval α / (fX + gX).denom.eval α
  --     = fX.num.eval α / fX.denom.eval α + gX.num.eval α / gX.denom.eval α
  have hprod_ne : fX.denom.eval α * gX.denom.eval α ≠ 0 := mul_ne_zero hf_denom hg_denom
  by_cases hsum_denom : (fX + gX).denom.eval α = 0
  · -- If (fX + gX).denom.eval α = 0
    -- This is actually impossible via coprimality!
    -- From heval: lhs * (fX.denom * gX.denom).eval α = rhs * 0 = 0
    -- But (fX.denom * gX.denom).eval α ≠ 0, so lhs = (fX + gX).num.eval α = 0
    rw [hsum_denom, mul_zero] at heval
    have hsum_num : (fX + gX).num.eval α = 0 := by
      by_contra h
      have : (fX + gX).num.eval α * (fX.denom.eval α * gX.denom.eval α) = 0 := heval
      simp only [mul_eq_zero, h, hprod_ne, or_self] at this
    -- But now we have both num and denom evaluating to 0, which contradicts coprimality
    -- (X - C α) would divide both, but gcd(num, denom) = 1
    exfalso
    have hcoprime := RatFunc.isCoprime_num_denom (fX + gX)
    have hroot_denom : Polynomial.IsRoot (fX + gX).denom α := by
      rwa [Polynomial.IsRoot.def]
    have hroot_num : Polynomial.IsRoot (fX + gX).num α := by
      rwa [Polynomial.IsRoot.def]
    have hdvd_denom := Polynomial.dvd_iff_isRoot.mpr hroot_denom
    have hdvd_num := Polynomial.dvd_iff_isRoot.mpr hroot_num
    have hXa_ne : Polynomial.X - Polynomial.C α ≠ 0 := by
      intro h; have := congr_arg Polynomial.natDegree h; simp at this
    have hdeg : (Polynomial.X - Polynomial.C α).natDegree = 1 := Polynomial.natDegree_X_sub_C α
    have hdvd1 : (Polynomial.X - Polynomial.C α) ∣ 1 := by
      have h1 := hcoprime.isUnit_of_dvd' hdvd_num hdvd_denom
      exact h1.dvd
    have hdeg1 := Polynomial.natDegree_le_of_dvd hdvd1 one_ne_zero
    rw [hdeg, Polynomial.natDegree_one] at hdeg1
    omega
  · -- (fX + gX).denom.eval α ≠ 0
    -- All three denominators are nonzero, so we can use field_simp
    -- Goal: (fX + gX).num.eval α / (fX + gX).denom.eval α
    --     = fX.num.eval α / fX.denom.eval α + gX.num.eval α / gX.denom.eval α
    -- Using div_eq_div_iff to reduce to multiplication equation
    rw [div_add_div _ _ hf_denom hg_denom]
    rw [div_eq_div_iff hsum_denom (mul_ne_zero hf_denom hg_denom)]
    -- Goal: (fX + gX).num.eval α * (fX.denom.eval α * gX.denom.eval α) =
    --       (fX.num.eval α * gX.denom.eval α + gX.num.eval α * fX.denom.eval α) * (fX + gX).denom.eval α
    -- This follows from heval with ring manipulation
    have h := heval
    ring_nf at h ⊢
    exact h

/-- Additivity for residueAtLinear when both functions have at most simple poles at α.

The hypothesis conditions are equivalent to: f and g have poles of order at most 1 at α.
This is a "conditional" additivity - it holds when the pole conditions are satisfied.

**Important**: residueAtLinear is NOT additive in general for higher-order poles.
For a truly linear residue functional, use `residueAt` which is defined via translation
to the origin where `residueAtX` (using HahnSeries.coeff) handles all pole orders correctly.
-/
theorem residueAtLinear_add (α : Fq) (f g : RatFunc Fq)
    (hf : ((RatFunc.X - RatFunc.C α) * f).denom.eval α ≠ 0)
    (hg : ((RatFunc.X - RatFunc.C α) * g).denom.eval α ≠ 0) :
    residueAtLinear α (f + g) = residueAtLinear α f + residueAtLinear α g :=
  residueAtLinear_add_aux α f g hf hg

end RiemannRochV2.Residue
