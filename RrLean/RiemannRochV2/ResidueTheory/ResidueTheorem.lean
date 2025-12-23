import RrLean.RiemannRochV2.ResidueTheory.ResidueAtX
import RrLean.RiemannRochV2.ResidueTheory.ResidueAtInfinity
import RrLean.RiemannRochV2.ResidueTheory.ResidueAtLinear
import RrLean.RiemannRochV2.ResidueTheory.ResidueLinearCorrect

/-!
# Residue Theorem

The global residue theorem states that for any f ∈ RatFunc Fq:
  ∑_v res_v(f) = 0

where the sum is over all places v (finite and infinite).

For simple poles at linear places (X - α), we can prove this directly.

## Main Results

- `residue_sum_simple_pole`: For f = c/(X - α), res_α(f) + res_∞(f) = 0
- `residueAtLinear_inv_X_sub_ne`: res_β(c/(X - α)) = 0 when β ≠ α

## References

- Rosen "Number Theory in Function Fields" Chapter 4
- Stichtenoth "Algebraic Function Fields and Codes" Section 1.4
-/

noncomputable section

open scoped LaurentSeries
open HahnSeries Polynomial

namespace RiemannRochV2.Residue

variable {Fq : Type*} [Field Fq]

/-- The sum of residues is zero for a simple pole at a linear place.

For f = c • (X - α)⁻¹:
- res_α(f) = c   (from residueAtLinear_inv_X_sub)
- res_∞(f) = -c  (from residueAtInfty_smul_inv_X_sub)
- Sum = c + (-c) = 0

This is the fundamental test case for the residue theorem.
-/
theorem residue_sum_simple_pole (α c : Fq) :
    residueAtLinear α (c • (RatFunc.X - RatFunc.C α)⁻¹) +
    residueAtInfty (c • (RatFunc.X - RatFunc.C α)⁻¹) = 0 := by
  rw [residueAtLinear_inv_X_sub, residueAtInfty_smul_inv_X_sub]
  ring

-- Helper lemmas for residueAtLinear_inv_X_sub_ne

open Classical in
private lemma RatFunc_num_X_sub_C' (β : Fq) :
    (RatFunc.X - RatFunc.C β : RatFunc Fq).num = Polynomial.X - Polynomial.C β := by
  simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub, RatFunc.num_algebraMap]

open Classical in
private lemma RatFunc_denom_X_sub_C' (β : Fq) :
    (RatFunc.X - RatFunc.C β : RatFunc Fq).denom = 1 := by
  rw [RatFunc.X, ← RatFunc.algebraMap_C β, ← map_sub, RatFunc.denom_algebraMap]

open Classical in
private lemma denom_inv_X_sub_C_dvd (α : Fq) :
    ((RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq).denom ∣ (Polynomial.X - Polynomial.C α) := by
  have hne : (Polynomial.X - Polynomial.C α) ≠ (0 : Polynomial Fq) := by
    intro h; have hdeg := congr_arg Polynomial.natDegree h; simp at hdeg
  rw [RatFunc.denom_dvd hne]
  use 1
  rw [map_one, RatFunc.X, ← RatFunc.algebraMap_C α, ← map_sub, one_div]

open Classical in
private lemma denom_smul_inv_X_sub_dvd (α c : Fq) :
    (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq).denom ∣ (Polynomial.X - Polynomial.C α) := by
  by_cases hc : c = 0
  · simp only [hc, zero_smul, RatFunc.denom_zero]
    exact one_dvd _
  · have hh_eq : (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) =
                 RatFunc.C c * (RatFunc.X - RatFunc.C α)⁻¹ := by
      rw [Algebra.smul_def, RatFunc.algebraMap_eq_C]
    rw [hh_eq]
    have hdvd := RatFunc.denom_mul_dvd (RatFunc.C c) (RatFunc.X - RatFunc.C α)⁻¹
    rw [RatFunc.denom_C, one_mul] at hdvd
    exact hdvd.trans (denom_inv_X_sub_C_dvd α)

private lemma Polynomial.eval_ne_zero_of_dvd' {R : Type*} [CommRing R] [NoZeroDivisors R]
    {p q : Polynomial R} {x : R} (hdvd : p ∣ q) (hq : q.eval x ≠ 0) : p.eval x ≠ 0 := by
  intro hp
  exact hq (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd hp)

/-- The residue at a different linear place is zero for a simple pole.

For f = c • (X - α)⁻¹ and β ≠ α:
- res_β(f) = 0 (f has no pole at β)

Proof strategy: (X - C β) is a factor of the numerator of g = (X - C β) * f,
so g.num.eval β = 0. Meanwhile, g.denom | (X - C α) and (X - C α).eval β ≠ 0,
so g.denom.eval β ≠ 0. Thus g.num.eval β / g.denom.eval β = 0.
-/
theorem residueAtLinear_inv_X_sub_ne (α β c : Fq) (hne : α ≠ β) :
    residueAtLinear β (c • (RatFunc.X - RatFunc.C α)⁻¹) = 0 := by
  simp only [residueAtLinear]
  by_cases hc : c = 0
  · simp [hc]
  · set f := (RatFunc.X - RatFunc.C β : RatFunc Fq) with hf_def
    set h := (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) with hh_def
    -- Use num_denom_mul: (f*h).num * (f.denom * h.denom) = f.num * h.num * (f*h).denom
    have hmul := RatFunc.num_denom_mul f h
    rw [RatFunc_denom_X_sub_C', one_mul] at hmul
    have heval := congr_arg (Polynomial.eval β) hmul
    simp only [Polynomial.eval_mul] at heval
    -- f.num.eval β = (X - C β).eval β = 0
    have hf_zero : f.num.eval β = 0 := by
      simp only [hf_def, RatFunc_num_X_sub_C', Polynomial.eval_sub,
                 Polynomial.eval_X, Polynomial.eval_C, sub_self]
    rw [hf_zero, zero_mul, zero_mul] at heval
    -- (f * h).num.eval β * h.denom.eval β = 0
    -- h.denom | (X - C α) and (X - C α).eval β = β - α ≠ 0, so h.denom.eval β ≠ 0
    have hXa_eval_ne : (Polynomial.X - Polynomial.C α).eval β ≠ 0 := by
      simp [sub_ne_zero.mpr hne.symm]
    have hdvd : h.denom ∣ (Polynomial.X - Polynomial.C α) := by
      simp only [hh_def]
      exact denom_smul_inv_X_sub_dvd α c
    have hh_denom_ne : h.denom.eval β ≠ 0 := Polynomial.eval_ne_zero_of_dvd' hdvd hXa_eval_ne
    -- So (f * h).num.eval β = 0
    have hnum_zero : (f * h).num.eval β = 0 := by
      have h0 : (f * h).num.eval β * h.denom.eval β = 0 := by rw [heval]
      exact (mul_eq_zero.mp h0).resolve_right hh_denom_ne
    simp [hnum_zero]

-- residue_sum_eq_zero moved to Archive/SorriedLemmas.lean (needs residueAtIrreducible)

end RiemannRochV2.Residue

end
