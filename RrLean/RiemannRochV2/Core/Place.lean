import RrLean.RiemannRochV2.Core.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Unified Place Type for Algebraic Curves

This module defines a unified `Place` type that represents both finite and infinite
places on an algebraic curve. This is the key abstraction needed to move from
"affine Riemann-Roch" (HeightOneSpectrum only) to "projective Riemann-Roch".

## The Affine Trap (Cycle 248 Discovery)

Any Dedekind domain R models the AFFINE part of a curve:
- `HeightOneSpectrum R` = finite places only (prime ideals of R)
- Missing: the point(s) at infinity

For projective curves:
| Curve Type | Coordinate Ring R | Missing Place(s) |
|------------|-------------------|------------------|
| P¹ | k[t] | ∞ |
| Elliptic | k[x,y]/(y²-x³-ax-b) | Point O at infinity |
| Hyperelliptic | k[x,y]/(y²-f(x)) | 1-2 points at infinity |

## Main Definitions

* `InfinitePlace K` - An infinite place on function field K
* `Place R K` - Either a finite place (HeightOneSpectrum R) or infinite place
* `Place.valuation` - The valuation at a place (finite or infinite)
* `Place.degree` - The degree of a place (residue field degree over base)

## Design Decisions

1. **InfinitePlace as structure**: For now, we define InfinitePlace as a structure
   containing a valuation. This is abstract enough to handle P¹ (single ∞) and
   hyperelliptic curves (1-2 points at ∞).

2. **Valuation type**: We use `WithZero (Multiplicative ℤ)` for uniformity with
   `HeightOneSpectrum.valuation`.

3. **Degree**: Finite places have degree = [κ(v) : k]. Infinite places also have
   a degree (often 1 for rational points, higher for places of higher degree).

## References

- Mathlib: `RingTheory.DedekindDomain.Ideal` (HeightOneSpectrum)
- Mathlib: `NumberTheory.FunctionField` (FqtInfty, inftyValuation for P¹)
-/

namespace RiemannRochV2

open IsDedekindDomain

/-! ## Infinite Place Structure -/

/-- An infinite place on a function field K.

For function fields K/k, infinite places correspond to valuations that are
trivial on k but non-trivial on K, measuring "degree at infinity".

For P¹ = Frac(k[t]), there is exactly one infinite place given by:
  v_∞(f/g) = deg(g) - deg(f)

For hyperelliptic curves y² = f(x), there are 1 or 2 infinite places
depending on whether f has odd or even degree.
-/
structure InfinitePlace (K : Type*) [Field K] where
  /-- The valuation at this infinite place. -/
  val : Valuation K (WithZero (Multiplicative ℤ))
  /-- The degree of this place (residue field degree over base field). -/
  deg : ℕ
  /-- Degree is positive. -/
  deg_pos : 0 < deg

namespace InfinitePlace

variable {K : Type*} [Field K]

/-- The valuation function at an infinite place. -/
def valuation (v : InfinitePlace K) : K → WithZero (Multiplicative ℤ) := v.val

/-- The degree of an infinite place is at least 1. -/
lemma one_le_deg (v : InfinitePlace K) : 1 ≤ v.deg := v.deg_pos

/-- If there exists an infinite place, we can choose one as a default. -/
noncomputable instance instInhabitedOfNonempty [h : Nonempty (InfinitePlace K)] :
    Inhabited (InfinitePlace K) := Classical.inhabited_of_nonempty h

end InfinitePlace

/-! ## Unified Place Type -/

/-- A place on a curve is either finite (HeightOneSpectrum R) or infinite.

This unifies:
- Finite places: prime ideals of the coordinate ring R (= points on affine part)
- Infinite places: valuations at infinity (= points at infinity on projective model)

For a projective curve, the set of all places corresponds bijectively to
the closed points of the curve.
-/
inductive Place (R : Type*) (K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Field K] [Algebra R K]
  | finite : HeightOneSpectrum R → Place R K
  | infinite : InfinitePlace K → Place R K

namespace Place

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## Basic Operations -/

/-- A place is finite iff it comes from HeightOneSpectrum. -/
def isFinite : Place R K → Bool
  | finite _ => true
  | infinite _ => false

/-- A place is infinite iff it comes from InfinitePlace. -/
def isInfinite : Place R K → Bool
  | finite _ => false
  | infinite _ => true

/-- Extract the finite place, if it is one. -/
def asFinite : Place R K → Option (HeightOneSpectrum R)
  | finite v => some v
  | infinite _ => none

/-- Extract the infinite place, if it is one. -/
def asInfinite : Place R K → Option (InfinitePlace K)
  | finite _ => none
  | infinite v => some v

/-! ## Valuation at a Place -/

/-- The valuation at a place, dispatching to the appropriate valuation. -/
noncomputable def valuation (p : Place R K) : K → WithZero (Multiplicative ℤ) :=
  match p with
  | finite v => v.valuation K
  | infinite v => v.valuation

/-- The valuation of zero is zero at any place. -/
@[simp]
lemma valuation_zero (p : Place R K) : p.valuation 0 = 0 := by
  cases p with
  | finite v => exact Valuation.map_zero _
  | infinite v => exact Valuation.map_zero _

/-- The valuation of one is one at any place. -/
@[simp]
lemma valuation_one (p : Place R K) : p.valuation 1 = 1 := by
  cases p with
  | finite v => exact Valuation.map_one _
  | infinite v => exact Valuation.map_one _

/-- The valuation is multiplicative. -/
lemma valuation_mul (p : Place R K) (x y : K) :
    p.valuation (x * y) = p.valuation x * p.valuation y := by
  cases p with
  | finite v => exact Valuation.map_mul _ x y
  | infinite v => exact Valuation.map_mul _ x y

/-- The valuation satisfies the ultrametric inequality. -/
lemma valuation_add_le (p : Place R K) (x y : K) :
    p.valuation (x + y) ≤ max (p.valuation x) (p.valuation y) := by
  cases p with
  | finite v => exact Valuation.map_add_le_max' _ x y
  | infinite v => exact Valuation.map_add_le_max' _ x y

/-! ## Degree of a Place -/

/-- The degree of an infinite place (stored in the structure). -/
def degreeInfinite (p : Place R K) : Option ℕ :=
  match p with
  | finite _ => none
  | infinite v => some v.deg

/-- Check if a place is a degree-1 (rational) place.

For finite places, this would mean [κ(v) : k] = 1.
For infinite places, this checks the stored degree.
-/
def isDegreeOne (p : Place R K) : Prop :=
  match p with
  | finite _ => True  -- Needs base field to define properly
  | infinite v => v.deg = 1

/-! ## Decidable Equality -/

/-- Places have decidable equality when both components do. -/
instance [DecidableEq (HeightOneSpectrum R)] [DecidableEq (InfinitePlace K)] :
    DecidableEq (Place R K) :=
  fun p q => by
    cases p <;> cases q
    case finite.finite v w =>
      exact if h : v = w then isTrue (by rw [h]) else isFalse (by intro heq; injection heq; contradiction)
    case infinite.infinite v w =>
      exact if h : v = w then isTrue (by rw [h]) else isFalse (by intro heq; injection heq; contradiction)
    case finite.infinite v w => exact isFalse (by intro heq; injection heq)
    case infinite.finite v w => exact isFalse (by intro heq; injection heq)

/-! ## Finite Place Coercion -/

/-- Coerce HeightOneSpectrum to Place. -/
instance : Coe (HeightOneSpectrum R) (Place R K) := ⟨Place.finite⟩

/-- Coerce InfinitePlace to Place. -/
instance : Coe (InfinitePlace K) (Place R K) := ⟨Place.infinite⟩

/-- Valuation at a finite place agrees with HeightOneSpectrum.valuation. -/
lemma valuation_finite (v : HeightOneSpectrum R) (x : K) :
    (finite v : Place R K).valuation x = v.valuation K x := rfl

/-- Valuation at an infinite place agrees with InfinitePlace.valuation. -/
lemma valuation_infinite (v : InfinitePlace K) (x : K) :
    (infinite v : Place R K).valuation x = v.valuation x := rfl

/-- The finite place constructor is injective. -/
lemma finite_injective : Function.Injective (finite : HeightOneSpectrum R → Place R K) :=
  fun _ _ h => by injection h

/-- The infinite place constructor is injective. -/
lemma infinite_injective : Function.Injective (infinite : InfinitePlace K → Place R K) :=
  fun _ _ h => by injection h

end Place

/-! ## Place Collection Typeclass -/

/-- Typeclass for a curve providing its collection of infinite places.

Different curves have different numbers of infinite places:
- P¹: exactly 1 infinite place
- Elliptic curves: exactly 1 infinite place (the point O)
- Hyperelliptic y² = f(x): 1 if deg(f) odd, 2 if deg(f) even
-/
class HasInfinitePlaces (R : Type*) (K : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] [Field K] [Algebra R K] where
  /-- The (finite) set of infinite places. -/
  infinitePlaces : Finset (InfinitePlace K)
  /-- There is at least one infinite place (projective curves are complete). -/
  nonempty : infinitePlaces.Nonempty

namespace HasInfinitePlaces

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K]
variable [hip : HasInfinitePlaces R K]

/-- The set of all places (finite + infinite). -/
def allPlaces [Fintype (HeightOneSpectrum R)] [DecidableEq (HeightOneSpectrum R)]
    [DecidableEq (InfinitePlace K)] : Finset (Place R K) :=
  (Finset.univ.map ⟨Place.finite, fun _ _ h => by injection h⟩) ∪
  (hip.infinitePlaces.map ⟨Place.infinite, fun _ _ h => by injection h⟩)

/-- Sum of degrees of all infinite places. -/
def infiniteDegreeSum : ℕ := hip.infinitePlaces.sum (·.deg)

end HasInfinitePlaces

end RiemannRochV2
