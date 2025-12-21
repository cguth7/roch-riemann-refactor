import RrLean.RiemannRochV2.SerreDuality.RatFuncPairing
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

/-- Key lemma: If f ∈ RRSpace_ratfunc_projective (n·[linearPlace α]), then
(X-α)^n · f is a polynomial (has no poles at finite places) of degree ≤ n. -/
lemma mul_X_sub_pow_is_polynomial (α : Fq) (n : ℕ) (f : RatFunc Fq)
    (hf : f ∈ RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) :
    ∃ p : Polynomial Fq, (Polynomial.X - Polynomial.C α)^n * RatFunc.num f =
        p * RatFunc.denom f ∧ p.natDegree ≤ n := by
  -- First handle the case f = 0
  rcases hf with ⟨hval, hinfty⟩
  by_cases hf0 : f = 0
  · use 0
    simp [hf0]
  -- For f ≠ 0, extract the valuation condition at linearPlace α
  rcases hval with hzero | hval_all
  · exact (hf0 hzero).elim
  -- The valuation condition says v_α(f) ≤ n
  -- which means ord_α(f) ≥ -n
  -- so (X-α)^n · f has ord_α ≥ 0, i.e., no pole at α
  sorry -- Technical: need to show polynomial form from valuation bounds

/-- Partial pole clearing: maps f to the polynomial part of (X-α)^n · f.
This is only defined on the subspace RRSpace_ratfunc_projective (n·[α]). -/
def partialClearPoles (α : Fq) (n : ℕ) :
    RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1) →ₗ[Fq]
    Polynomial.degreeLT Fq (n + 1) where
  toFun f := by
    -- For now, we construct using choice from the existence lemma
    have hpoly := mul_X_sub_pow_is_polynomial Fq α n f.val f.property
    refine ⟨hpoly.choose, ?_⟩
    have hdeg := hpoly.choose_spec.2
    simp only [Polynomial.mem_degreeLT]
    -- Convert natDegree ≤ n to degree < n+1
    calc hpoly.choose.degree
        ≤ hpoly.choose.natDegree := Polynomial.degree_le_natDegree
      _ ≤ n := Nat.cast_le.mpr hdeg
      _ < n + 1 := by exact_mod_cast Nat.lt_succ_self n
  map_add' := by
    intro f g
    ext
    sorry -- Need to show polynomial extraction respects addition
  map_smul' := by
    intro c f
    ext
    sorry -- Need to show polynomial extraction respects scalar mult

/-- The pole clearing map is injective: if (X-α)^n · f = 0, then f = 0. -/
lemma partialClearPoles_injective (α : Fq) (n : ℕ) :
    Function.Injective (partialClearPoles Fq α n) := by
  intro f g heq
  ext
  -- If the polynomials are equal, then the original functions are equal
  -- because (X-α)^n ≠ 0 and we're in a domain
  sorry

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

/-- Finiteness for D + [v] when D is finite-dim and v is a linear place. -/
instance RRSpace_ratfunc_projective_add_single_finite (α : Fq)
    (D : DivisorV2 (Polynomial Fq))
    [hD : Module.Finite Fq (RRSpace_ratfunc_projective D)] :
    Module.Finite Fq (RRSpace_ratfunc_projective (D + DivisorV2.single (linearPlace α) 1)) := by
  -- Similar embedding argument, using deg(D) + 1 as the polynomial degree bound
  sorry

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
