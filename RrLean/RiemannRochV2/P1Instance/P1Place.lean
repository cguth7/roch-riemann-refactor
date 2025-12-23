/-
# P¹ Place Infrastructure

This file connects P¹ = RatFunc Fq to the unified Place infrastructure from Place.lean.

## Main Definitions

* `p1InftyPlace Fq` - The unique infinite place on P¹ (= RatFunc Fq)
* `HasInfinitePlaces Fq[X] (RatFunc Fq)` - Instance providing the infinite place
* `ConstantsValuationBound Fq Fq[X] (RatFunc Fq)` - Constants have valuation ≤ 1 at all places

## Key Properties

For P¹ = Frac(Fq[X]):
- There is exactly ONE infinite place (the place at ∞)
- This place has degree 1 (rational point)
- The infty valuation is v_∞(f/g) = deg(g) - deg(f)
- For c ∈ Fq: v(c) = 1 at all places (finite and infinite)

## References

- Mathlib.NumberTheory.FunctionField (inftyValuation, FqtInfty)
-/

import RrLean.RiemannRochV2.Core.Place
import RrLean.RiemannRochV2.Core.RRSpaceV3
import Mathlib.NumberTheory.FunctionField

noncomputable section

open IsDedekindDomain
open scoped Polynomial

namespace RiemannRochV2

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

-- RatFunc Fq needs classical DecidableEq for Valuation API
noncomputable instance instDecidableEqRatFunc : DecidableEq (RatFunc Fq) := Classical.decEq _

/-! ## The Infinite Place on P¹ -/

/-- The unique infinite place on P¹ = RatFunc Fq.

This is defined using Mathlib's `FunctionField.inftyValuedFqt`, which provides
the valued structure with v_∞(f/g) = deg(g) - deg(f) (in multiplicative notation:
exp(deg(g) - deg(f))).

The degree is 1 because the residue field at ∞ is isomorphic to Fq (it's a
rational point on the projective line).
-/
def p1InftyPlace : InfinitePlace (RatFunc Fq) where
  val := (FunctionField.inftyValuedFqt Fq).v
  deg := 1
  deg_pos := Nat.one_pos

/-- The infinite place on P¹ has degree 1 (it's a rational point). -/
@[simp]
lemma p1InftyPlace_deg : (p1InftyPlace Fq).deg = 1 := rfl

/-- The valuation at the P¹ infinite place equals the infinity valuation. -/
lemma p1InftyPlace_valuation_eq (f : RatFunc Fq) :
    (p1InftyPlace Fq).valuation f = (FunctionField.inftyValuedFqt Fq).v f := rfl

/-- Alternative form: valuation equals inftyValuationDef. -/
lemma p1InftyPlace_valuation_eq' (f : RatFunc Fq) :
    (p1InftyPlace Fq).valuation f = FunctionField.inftyValuationDef Fq f := rfl

/-! ## HasInfinitePlaces Instance -/

/-- DecidableEq for InfinitePlace (RatFunc Fq).

We use classical decidability since comparing valuations directly is tricky. -/
noncomputable instance : DecidableEq (InfinitePlace (RatFunc Fq)) := Classical.decEq _

/-- The (singleton) set of infinite places on P¹. -/
def p1InfinitePlaces : Finset (InfinitePlace (RatFunc Fq)) := {p1InftyPlace Fq}

/-- The infinite places set is nonempty (contains the unique ∞). -/
lemma p1InfinitePlaces_nonempty : (p1InfinitePlaces Fq).Nonempty :=
  ⟨p1InftyPlace Fq, Finset.mem_singleton_self _⟩

/-- HasInfinitePlaces instance for P¹ = Polynomial Fq / RatFunc Fq. -/
instance instHasInfinitePlacesP1 : HasInfinitePlaces Fq[X] (RatFunc Fq) where
  infinitePlaces := p1InfinitePlaces Fq
  nonempty := p1InfinitePlaces_nonempty Fq

/-- There is exactly one infinite place on P¹. -/
lemma p1InfinitePlaces_card : (p1InfinitePlaces Fq).card = 1 := Finset.card_singleton _

/-- The sum of infinite degrees on P¹ is 1. -/
lemma p1InfiniteDegreeSum : HasInfinitePlaces.infiniteDegreeSum (R := Fq[X]) (K := RatFunc Fq) = 1 := by
  simp only [HasInfinitePlaces.infiniteDegreeSum, instHasInfinitePlacesP1,
             p1InfinitePlaces, Finset.sum_singleton, p1InftyPlace_deg]

/-! ## ConstantsValuationBound Instance

For P¹, constants c ∈ Fq have valuation = 1 at all places:
- At finite places: c is a unit in Fq ⊂ Fq[X] ⊂ Fq[X]_p, so v_p(c) = 1
- At the infinite place: deg(c) = 0, so v_∞(c) = exp(0) = 1
-/

/-- Constants from Fq have valuation ≤ 1 at finite places. -/
lemma p1_constant_valuation_finite (c : Fq) (v : HeightOneSpectrum Fq[X]) :
    (Place.finite v : Place Fq[X] (RatFunc Fq)).valuation (algebraMap Fq (RatFunc Fq) c) ≤ 1 := by
  simp only [Place.valuation_finite]
  -- algebraMap Fq (RatFunc Fq) factors through Polynomial Fq
  rw [IsScalarTower.algebraMap_apply Fq Fq[X] (RatFunc Fq)]
  -- Now use HeightOneSpectrum.valuation_le_one for polynomial constants
  exact HeightOneSpectrum.valuation_le_one v (algebraMap Fq Fq[X] c)

/-- Constants from Fq have valuation ≤ 1 at the P¹ infinite place.

In fact, for c ≠ 0, the valuation is exactly 1 (constants have degree 0).
-/
lemma p1_constant_valuation_p1InftyPlace (c : Fq) :
    (Place.infinite (p1InftyPlace Fq) : Place Fq[X] (RatFunc Fq)).valuation
      (algebraMap Fq (RatFunc Fq) c) ≤ 1 := by
  -- Unfold to get (p1InftyPlace Fq).val (algebraMap c)
  simp only [Place.valuation_infinite, InfinitePlace.valuation]
  by_cases hc : c = 0
  · subst hc
    simp only [map_zero, Valuation.map_zero]
    exact WithZero.zero_le 1
  · -- For nonzero c, use FunctionField.inftyValuation.C
    -- algebraMap Fq (RatFunc Fq) c = RatFunc.C c
    have halg : algebraMap Fq (RatFunc Fq) c = RatFunc.C c := rfl
    -- (p1InftyPlace Fq).val = (FunctionField.inftyValuedFqt Fq).v = FunctionField.inftyValuationDef
    have hval_eq : (p1InftyPlace Fq).val = (FunctionField.inftyValuedFqt Fq).v := rfl
    rw [hval_eq, halg]
    -- inftyValuation (RatFunc.C c) = 1 for c ≠ 0
    have hval : (FunctionField.inftyValuedFqt Fq).v (RatFunc.C c) = 1 := by
      -- inftyValuedFqt.v = inftyValuationDef
      show FunctionField.inftyValuationDef Fq (RatFunc.C c) = 1
      rw [← FunctionField.inftyValuation_apply]
      exact FunctionField.inftyValuation.C Fq hc
    rw [hval]

/-- Constants from Fq have valuation ≤ 1 at all registered infinite places on P¹.

Since P¹ has exactly one registered infinite place (p1InftyPlace), this follows
from p1_constant_valuation_p1InftyPlace.
-/
lemma p1_constant_valuation_infinite (c : Fq) (v : InfinitePlace (RatFunc Fq))
    (hv : v ∈ (instHasInfinitePlacesP1 Fq).infinitePlaces) :
    (Place.infinite v : Place Fq[X] (RatFunc Fq)).valuation (algebraMap Fq (RatFunc Fq) c) ≤ 1 := by
  -- The only element in p1InfinitePlaces is p1InftyPlace
  simp only [instHasInfinitePlacesP1, p1InfinitePlaces, Finset.mem_singleton] at hv
  subst hv
  exact p1_constant_valuation_p1InftyPlace Fq c

/-- ConstantsValuationBound instance for P¹.

This proves that constants from Fq have valuation ≤ 1 at all places (finite and registered infinite).
-/
instance instConstantsValuationBoundP1 : ConstantsValuationBound Fq Fq[X] (RatFunc Fq) where
  valuation_le_one_finite := p1_constant_valuation_finite Fq
  valuation_le_one_infinite := p1_constant_valuation_infinite Fq

/-! ## Summary

For P¹ = RatFunc Fq, we have:
1. ✅ `p1InftyPlace Fq` - The unique infinite place with degree 1
2. ✅ `HasInfinitePlaces Fq[X] (RatFunc Fq)` - The curve has exactly one infinite place
3. ✅ `ConstantsValuationBound Fq Fq[X] (RatFunc Fq)` - Constants from Fq have valuation ≤ 1

These instances enable using `RRModuleV3` and `ellV3` for projective Riemann-Roch on P¹.
-/

end RiemannRochV2

end
