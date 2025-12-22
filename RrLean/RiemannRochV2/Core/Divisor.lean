import RrLean.RiemannRochV2.Core.Basic

/-!
# Divisor Theory for Dedekind Domains

This module defines divisors on Dedekind domains as finitely supported functions
from height-1 primes to ℤ, along with basic operations and properties.

## Main Definitions

* `DivisorV2 R` - Divisors as `HeightOneSpectrum R →₀ ℤ`
* `DivisorV2.deg` - Degree (sum of coefficients)
* `DivisorV2.single` - Single-point divisor constructor
* `DivisorV2.Effective` - Non-negative divisors
-/

namespace RiemannRochV2

open IsDedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]

/-! ## Divisor Foundations -/

-- Candidate 1 [tag: bundle_divisor_bridge] [status: OK]
/-- A divisor on a Dedekind domain is a finitely supported function from height-1 primes to ℤ.
This is the constructive analog of formal sums of points on a curve.
HeightOneSpectrum R represents the "points" of the associated curve. -/
abbrev DivisorV2 := HeightOneSpectrum R →₀ ℤ

namespace DivisorV2

variable {R}

set_option linter.unusedSectionVars false in
section
variable [IsDomain R] [IsDedekindDomain R]

-- Candidate 2 [tag: degree_bridge] [status: OK]
/-- The degree of a divisor is the sum of its coefficients.
For a curve, this is the total number of points counted with multiplicity. -/
def deg (D : DivisorV2 R) : ℤ := D.sum (fun _ n => n)

-- Candidate 3 [tag: degree_bridge] [status: PROVED]
/-- Degree is additive. -/
lemma deg_add (D E : DivisorV2 R) : deg (D + E) = deg D + deg E := by
  simp only [deg]
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- Degree of zero divisor. -/
lemma deg_zero : deg (0 : DivisorV2 R) = 0 := by
  simp only [deg, Finsupp.sum_zero_index]

/-- Degree of negation. -/
lemma deg_neg (D : DivisorV2 R) : deg (-D) = -deg D := by
  have h : deg (D + (-D)) = deg D + deg (-D) := deg_add D (-D)
  simp only [add_neg_cancel, deg_zero] at h
  omega

/-- Single-point divisor constructor (n · v). -/
noncomputable abbrev single (v : HeightOneSpectrum R) (n : ℤ) : DivisorV2 R :=
  Finsupp.single v n

/-- Degree of single-point divisor. -/
lemma deg_single (v : HeightOneSpectrum R) (n : ℤ) : deg (single v n) = n := by
  simp only [deg, single, Finsupp.sum_single_index]

/-- A divisor is effective if all coefficients are non-negative. -/
def Effective (D : DivisorV2 R) : Prop := 0 ≤ D

lemma Effective_iff (D : DivisorV2 R) : Effective D ↔ ∀ v, 0 ≤ D v := Iff.rfl

lemma Effective_zero : Effective (0 : DivisorV2 R) := le_refl 0

/-- Effective divisors have non-negative degree.
Since all coefficients are ≥ 0, their sum is ≥ 0. -/
lemma deg_nonneg_of_effective {D : DivisorV2 R} (hD : Effective D) : 0 ≤ D.deg := by
  unfold deg
  apply Finsupp.sum_nonneg
  intro v _
  exact hD v

end

/-! ## Divisor Helpers for Riemann Inequality

These lemmas support the degree induction proof of the Riemann inequality.
-/

-- Candidate 2 [tag: degree_helpers] [status: OK]
/-- Degree of D + single v 1 is deg D + 1. -/
lemma deg_add_single' (D : DivisorV2 R) (v : HeightOneSpectrum R) :
    (D + DivisorV2.single v 1).deg = D.deg + 1 := by
  rw [deg_add, deg_single]

-- Candidate 3 [tag: degree_helpers] [status: OK]
/-- If D is effective with positive degree, there exists v with D(v) > 0.
This is key for "peeling off" a point in the induction step. -/
lemma exists_pos_of_deg_pos {D : DivisorV2 R} (hD : D.Effective)
    (hdeg : 0 < D.deg) : ∃ v : HeightOneSpectrum R, 0 < D v := by
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

-- Candidate 4 [tag: effectivity_subtraction] [status: OK]
/-- If D is effective and D(v) > 0, then D - single v 1 is effective.
This ensures the induction hypothesis applies to the smaller divisor. -/
lemma effective_sub_single {D : DivisorV2 R} (hD : D.Effective)
    (v : HeightOneSpectrum R) (hv : 0 < D v) :
    (D - DivisorV2.single v 1).Effective := by
  intro w
  simp only [Finsupp.coe_sub, Finsupp.coe_zero, Pi.sub_apply, Pi.zero_apply, single]
  by_cases h : w = v
  · subst h
    simp only [Finsupp.single_eq_same]
    omega
  · simp only [Finsupp.single_eq_of_ne h, sub_zero]
    exact hD w

-- Candidate 5 [tag: degree_subtraction] [status: OK]
/-- Degree subtraction: deg(D - single v 1) = deg D - 1. -/
lemma deg_sub_single (D : DivisorV2 R) (v : HeightOneSpectrum R) :
    (D - DivisorV2.single v 1).deg = D.deg - 1 := by
  rw [sub_eq_add_neg, deg_add, deg_neg, deg_single]
  ring

-- Candidate 6 [tag: single_reconstruction] [status: OK]
/-- Reconstruction: (D - single v 1) + single v 1 = D. -/
lemma sub_add_single_cancel (D : DivisorV2 R) (v : HeightOneSpectrum R) :
    (D - DivisorV2.single v 1) + DivisorV2.single v 1 = D := by
  simp only [sub_add_cancel]

end DivisorV2

end RiemannRochV2
