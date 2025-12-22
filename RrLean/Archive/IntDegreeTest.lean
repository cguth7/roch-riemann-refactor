import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Test file for intDegree approach to noPoleAtInfinity

This file tests the approach of using `RatFunc.intDegree` to prove
that 1/(X-α)^k has no pole at infinity, avoiding typeclass issues with gcd.
-/

noncomputable section

namespace IntDegreeTest

open Polynomial RatFunc

variable (Fq : Type*) [Field Fq]

/-- X - C α is nonzero in RatFunc. -/
lemma RatFunc_X_sub_C_ne_zero (α : Fq) : (RatFunc.X : RatFunc Fq) - RatFunc.C α ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have h1 : (RatFunc.X : RatFunc Fq).intDegree = 1 := RatFunc.intDegree_X
  have h2 : (RatFunc.C α : RatFunc Fq).intDegree = 0 := RatFunc.intDegree_C α
  rw [h, h2] at h1
  exact zero_ne_one h1

/-- The intDegree of (X - C α)⁻¹ ^ k is -k. -/
lemma intDegree_inv_X_sub_C_pow (α : Fq) (k : ℕ) :
    ((RatFunc.X - RatFunc.C α : RatFunc Fq)⁻¹ ^ k).intDegree = -(k : ℤ) := by
  -- intDegree(X - C α) = 1
  have hXα_deg : (RatFunc.X - RatFunc.C α : RatFunc Fq).intDegree = 1 := by
    have heq : RatFunc.X - RatFunc.C α = algebraMap (Polynomial Fq) (RatFunc Fq)
        (Polynomial.X - Polynomial.C α) := by
      simp [RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    rw [heq, RatFunc.intDegree_polynomial, Polynomial.natDegree_X_sub_C]
    rfl
  -- intDegree((X - C α)⁻¹) = -1
  have hinv_deg : (RatFunc.X - RatFunc.C α : RatFunc Fq)⁻¹.intDegree = -1 := by
    rw [RatFunc.intDegree_inv, hXα_deg]
  -- Helper: (X - C α)⁻¹ ≠ 0
  have hinv_ne : (RatFunc.X - RatFunc.C α : RatFunc Fq)⁻¹ ≠ 0 :=
    inv_ne_zero (RatFunc_X_sub_C_ne_zero Fq α)
  -- Induction on k
  induction k with
  | zero => simp [RatFunc.intDegree_one]
  | succ m ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero m hinv_ne) hinv_ne, ih, hinv_deg]
    omega

/-- noPoleAtInfinity expressed via intDegree. -/
def noPoleAtInfinity' (f : RatFunc Fq) : Prop :=
  f.num.natDegree ≤ f.denom.natDegree

/-- noPoleAtInfinity is equivalent to intDegree ≤ 0. -/
lemma noPoleAtInfinity_iff_intDegree_le_zero (f : RatFunc Fq) :
    noPoleAtInfinity' Fq f ↔ f.intDegree ≤ 0 := by
  unfold noPoleAtInfinity'
  simp only [RatFunc.intDegree, sub_nonpos, Int.ofNat_le]

/-- 1/(X-α)^k has no pole at infinity for k ≥ 1. -/
theorem inv_X_sub_C_pow_noPoleAtInfinity (α : Fq) (k : ℕ) :
    noPoleAtInfinity' Fq ((RatFunc.X - RatFunc.C α)⁻¹ ^ k) := by
  rw [noPoleAtInfinity_iff_intDegree_le_zero, intDegree_inv_X_sub_C_pow]
  omega

end IntDegreeTest
