import RrLean.RiemannRochV2.Core.Place
import RrLean.RiemannRochV2.Core.Divisor

/-!
# Projective Divisor Theory

This module defines divisors on projective curves using the unified `Place` type,
which includes both finite places (HeightOneSpectrum R) and infinite places.

## Main Definitions

* `DivisorV3 R K` - Divisors as `Place R K →₀ ℤ` (finite + infinite places)
* `DivisorV3.deg` - Degree (sum of coefficients)
* `DivisorV3.degFinite` - Degree contribution from finite places only
* `DivisorV3.degInfinite` - Degree contribution from infinite places only
* `DivisorV3.single` - Single-place divisor constructor
* `DivisorV3.Effective` - Non-negative divisors

## Relationship to DivisorV2

`DivisorV2 R` = `HeightOneSpectrum R →₀ ℤ` (affine divisors, finite places only)
`DivisorV3 R K` = `Place R K →₀ ℤ` (projective divisors, all places)

There is an injection from DivisorV2 to DivisorV3 (embed finite places).

## Design Note

For P¹ = Frac(k[t]), the canonical divisor is K = -2[∞], which lives entirely
at the infinite place. DivisorV2 cannot represent this; DivisorV3 can.
-/

namespace RiemannRochV2

open IsDedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## Projective Divisor Definition -/

/-- A projective divisor on a curve is a finitely supported function from all places to ℤ.
This extends `DivisorV2` to include infinite places, allowing representation of
divisors like the canonical divisor K = -2[∞] on P¹. -/
abbrev DivisorV3 := Place R K →₀ ℤ

namespace DivisorV3

variable {R K}
variable [DecidableEq (HeightOneSpectrum R)] [DecidableEq (InfinitePlace K)]

/-! ## Degree -/

/-- The degree of a projective divisor is the sum of its coefficients.
For a proper curve, this equals the sum over all places (finite + infinite). -/
def deg (D : DivisorV3 R K) : ℤ := D.sum (fun _ n => n)

/-- Degree is additive. -/
lemma deg_add (D E : DivisorV3 R K) : deg (D + E) = deg D + deg E := by
  simp only [deg]
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- Degree of zero divisor. -/
lemma deg_zero : deg (0 : DivisorV3 R K) = 0 := by
  simp only [deg, Finsupp.sum_zero_index]

/-- Degree of negation. -/
lemma deg_neg (D : DivisorV3 R K) : deg (-D) = -deg D := by
  have h : deg (D + (-D)) = deg D + deg (-D) := deg_add D (-D)
  simp only [add_neg_cancel, deg_zero] at h
  omega

/-- Degree of subtraction. -/
lemma deg_sub (D E : DivisorV3 R K) : deg (D - E) = deg D - deg E := by
  rw [sub_eq_add_neg, deg_add, deg_neg]
  ring

/-! ## Single-Place Divisors -/

/-- Single-place divisor constructor (n · p). -/
noncomputable abbrev single (p : Place R K) (n : ℤ) : DivisorV3 R K :=
  Finsupp.single p n

/-- Degree of single-place divisor. -/
lemma deg_single (p : Place R K) (n : ℤ) : deg (single p n) = n := by
  simp only [deg, single, Finsupp.sum_single_index]

/-- Single-place divisor at a finite place. -/
noncomputable abbrev singleFinite (v : HeightOneSpectrum R) (n : ℤ) : DivisorV3 R K :=
  single (Place.finite v) n

/-- Single-place divisor at an infinite place. -/
noncomputable abbrev singleInfinite (v : InfinitePlace K) (n : ℤ) : DivisorV3 R K :=
  single (Place.infinite v) n

/-- Degree of single finite-place divisor. -/
lemma deg_singleFinite (v : HeightOneSpectrum R) (n : ℤ) :
    deg (singleFinite v n : DivisorV3 R K) = n :=
  deg_single (Place.finite v) n

/-- Degree of single infinite-place divisor. -/
lemma deg_singleInfinite (v : InfinitePlace K) (n : ℤ) :
    deg (singleInfinite v n : DivisorV3 R K) = n :=
  deg_single (Place.infinite v) n

/-! ## Degree Decomposition -/

/-- Filter a projective divisor to its finite part. -/
def finiteFilter (D : DivisorV3 R K) : DivisorV3 R K :=
  D.filter (fun p => p.isFinite)

/-- Filter a projective divisor to its infinite part. -/
def infiniteFilter (D : DivisorV3 R K) : DivisorV3 R K :=
  D.filter (fun p => p.isInfinite)

/-- Degree contribution from finite places only. -/
def degFinite (D : DivisorV3 R K) : ℤ := (D.finiteFilter).deg

/-- Degree contribution from infinite places only. -/
def degInfinite (D : DivisorV3 R K) : ℤ := (D.infiniteFilter).deg

/-- A place is either finite or infinite (exclusively). -/
lemma isFinite_xor_isInfinite (p : Place R K) :
    (p.isFinite = true ∧ p.isInfinite = false) ∨
    (p.isFinite = false ∧ p.isInfinite = true) := by
  cases p with
  | finite _ => left; simp [Place.isFinite, Place.isInfinite]
  | infinite _ => right; simp [Place.isFinite, Place.isInfinite]

/-- Finite and infinite filters partition the support. -/
lemma finiteFilter_add_infiniteFilter (D : DivisorV3 R K) :
    D.finiteFilter + D.infiniteFilter = D := by
  ext p
  simp only [Finsupp.coe_add, Pi.add_apply, finiteFilter, infiniteFilter,
             Finsupp.filter_apply]
  cases p with
  | finite v => simp [Place.isFinite, Place.isInfinite]
  | infinite v => simp [Place.isFinite, Place.isInfinite]

/-- Total degree equals sum of finite and infinite contributions. -/
lemma deg_eq_degFinite_add_degInfinite (D : DivisorV3 R K) :
    D.deg = D.degFinite + D.degInfinite := by
  unfold degFinite degInfinite
  rw [← deg_add, finiteFilter_add_infiniteFilter]

/-! ## Effectivity -/

/-- A projective divisor is effective if all coefficients are non-negative. -/
def Effective (D : DivisorV3 R K) : Prop := 0 ≤ D

lemma Effective_iff (D : DivisorV3 R K) : Effective D ↔ ∀ p, 0 ≤ D p := Iff.rfl

lemma Effective_zero : Effective (0 : DivisorV3 R K) := le_refl 0

/-- Effective divisors have non-negative degree. -/
lemma deg_nonneg_of_effective {D : DivisorV3 R K} (hD : Effective D) : 0 ≤ D.deg := by
  unfold deg
  apply Finsupp.sum_nonneg
  intro p _
  exact hD p

/-! ## Embedding from Affine Divisors -/

/-- Embed an affine divisor (DivisorV2) into a projective divisor (DivisorV3).
Finite places are included; infinite places get coefficient 0. -/
noncomputable def ofAffine (D : DivisorV2 R) : DivisorV3 R K :=
  D.mapDomain Place.finite

/-- Degree is preserved by embedding. -/
lemma deg_ofAffine (D : DivisorV2 R) : (ofAffine D : DivisorV3 R K).deg = D.deg := by
  unfold deg ofAffine DivisorV2.deg
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

/-- Affine embedding preserves effectivity. -/
lemma ofAffine_effective {D : DivisorV2 R} (hD : D.Effective) :
    (ofAffine D : DivisorV3 R K).Effective := by
  intro p
  unfold ofAffine
  simp only [Finsupp.mapDomain]
  by_cases hp : ∃ v : HeightOneSpectrum R, Place.finite v = p
  · obtain ⟨v, hv⟩ := hp
    simp only [← hv, Finsupp.sum_apply, Finsupp.single_apply]
    apply Finsupp.sum_nonneg
    intro w _
    split_ifs with h
    · exact hD w
    · rfl
  · push_neg at hp
    simp only [Finsupp.sum_apply, Finsupp.single_apply]
    apply Finsupp.sum_nonneg
    intro w _
    split_ifs with h
    · exact (hp w h).elim
    · rfl

/-! ## Divisor Arithmetic Helpers -/

/-- Degree of D + single p 1 is deg D + 1. -/
lemma deg_add_single' (D : DivisorV3 R K) (p : Place R K) :
    (D + single p 1).deg = D.deg + 1 := by
  rw [deg_add, deg_single]

/-- If D is effective with positive degree, there exists p with D(p) > 0. -/
lemma exists_pos_of_deg_pos {D : DivisorV3 R K} (hD : D.Effective)
    (hdeg : 0 < D.deg) : ∃ p : Place R K, 0 < D p := by
  by_contra h_all_zero
  push_neg at h_all_zero
  have h_zero_deg : D.deg = 0 := by
    unfold deg
    rw [Finsupp.sum, Finset.sum_eq_zero]
    intro x _
    specialize h_all_zero x
    have hDx : 0 ≤ D x := hD x
    omega
  omega

/-- If D is effective and D(p) > 0, then D - single p 1 is effective. -/
lemma effective_sub_single {D : DivisorV3 R K} (hD : D.Effective)
    (p : Place R K) (hp : 0 < D p) :
    (D - single p 1).Effective := by
  intro q
  simp only [Finsupp.coe_sub, Finsupp.coe_zero, Pi.sub_apply, Pi.zero_apply, single]
  by_cases h : q = p
  · subst h
    simp only [Finsupp.single_eq_same]
    omega
  · simp only [Finsupp.single_eq_of_ne h, sub_zero]
    exact hD q

/-- Degree subtraction: deg(D - single p 1) = deg D - 1. -/
lemma deg_sub_single (D : DivisorV3 R K) (p : Place R K) :
    (D - single p 1).deg = D.deg - 1 := by
  rw [sub_eq_add_neg, deg_add, deg_neg, deg_single]
  ring

/-- Reconstruction: (D - single p 1) + single p 1 = D. -/
lemma sub_add_single_cancel (D : DivisorV3 R K) (p : Place R K) :
    (D - single p 1) + single p 1 = D := by
  simp only [sub_add_cancel]

end DivisorV3

end RiemannRochV2
