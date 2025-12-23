import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.FieldTheory.Finiteness
import RrLean.RiemannRochV2.ResidueTheory.ResidueLinearCorrect
import RrLean.RiemannRochV2.ResidueTheory.ResidueAtInfinity
import RrLean.RiemannRochV2.SerreDuality.RatFuncResidues

/-!
# Traced Residues for Higher-Degree Places

For a place v of degree d = [κ(v) : k] > 1, the "local residue" gives an element
of the residue field κ(v), not the base field k. To get a value in k, we need
to apply the trace map Tr_{κ(v)/k}.

## Mathematical Background

For a curve C over a finite field k = Fq:
- Places v correspond to prime ideals in the coordinate ring R
- The residue field κ(v) = R/v is a finite extension of k
- deg(v) = [κ(v) : k]

For the residue theorem ∑_v res_v(ω) = 0 with values in k, we need:
- For degree-1 places: res_v ∈ k directly
- For higher-degree places: Tr_{κ(v)/k}(local_res_v) ∈ k

## Key Insight for P¹

For P¹ = RatFunc Fq, ALL finite places have κ(v) ≅ Fq (degree 1).
This means Tr_{κ(v)/Fq} = id, so traced residue = local residue.

For other curves (elliptic, hyperelliptic), there may be higher-degree places
where the trace is non-trivial.

## References

- Rosen "Number Theory in Function Fields" Chapter 5
- Stichtenoth "Algebraic Function Fields and Codes" Section 3.1
-/

noncomputable section

open scoped LaurentSeries
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace RiemannRochV2.ResidueTrace

/-! ## Residue Field as k-Algebra

The residue field κ(v) = R ⧸ v.asIdeal inherits an algebra structure from k → R.
-/

variable {k : Type*} [Field k]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra k R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Algebra k K]
  [IsScalarTower k R K]

/-- The residue field κ(v) = R/v as a k-algebra.

The algebra structure comes from the composition k → R → R/v. -/
instance residueField_algebra (v : HeightOneSpectrum R) :
    Algebra k (R ⧸ v.asIdeal) :=
  Ideal.Quotient.algebra k

/-! ## Degree of a Place

The degree of a place v is the dimension [κ(v) : k].
For P¹ over k, all places have degree 1 (linear places).
-/

/-- The degree of a finite place v is [κ(v) : k].
This is 1 for "rational" points (where κ(v) ≅ k). -/
def residueFieldDegree (v : HeightOneSpectrum R) : ℕ :=
  Module.finrank k (R ⧸ v.asIdeal)

/-- A place is degree-1 (rational) if κ(v) ≅ k. -/
def isRationalPlace (v : HeightOneSpectrum R) : Prop :=
  residueFieldDegree (k := k) v = 1

/-! ## Traced Residue Framework

The traced residue is defined for places where κ(v) is a finite extension of k.
It combines:
1. Local residue at v (an element of κ(v))
2. Trace from κ(v) to k
-/

section TracedResidue

variable (Fq : Type*) [Field Fq]

/-- The trace map from the residue field to the base field.

For a place v where κ(v) is a finite-dimensional k-algebra, this is
the standard algebraic trace Tr_{κ(v)/k}. -/
def traceToBase (v : HeightOneSpectrum (Polynomial Fq))
    [FiniteDimensional Fq (Polynomial Fq ⧸ v.asIdeal)] :
    (Polynomial Fq ⧸ v.asIdeal) →ₗ[Fq] Fq :=
  Algebra.trace Fq (Polynomial Fq ⧸ v.asIdeal)

/-- For a degree-1 place, the trace map acts as the identity (after
identifying κ(v) with Fq via the canonical isomorphism).

More precisely, if [κ(v) : Fq] = 1, then Tr(x) = x for all x ∈ κ(v). -/
theorem trace_degree_one_eq (v : HeightOneSpectrum (Polynomial Fq))
    [FiniteDimensional Fq (Polynomial Fq ⧸ v.asIdeal)]
    (hv : residueFieldDegree (k := Fq) v = 1) (x : Polynomial Fq ⧸ v.asIdeal) :
    ∃ (e : (Polynomial Fq ⧸ v.asIdeal) ≃ₐ[Fq] Fq),
      Algebra.trace Fq (Polynomial Fq ⧸ v.asIdeal) x = e x := by
  sorry

/-! ## P¹-Specific: Linear Places

For P¹ = RatFunc Fq, all finite places correspond to irreducible polynomials.
Linear places correspond to (X - α) for α ∈ Fq.
-/

/-- HeightOneSpectrum for linear place (X - α). -/
def linearPlace (α : Fq) : HeightOneSpectrum (Polynomial Fq) where
  asIdeal := Ideal.span {Polynomial.X - Polynomial.C α}
  isPrime := Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero α) |>.mpr
              (Polynomial.irreducible_X_sub_C α).prime
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Polynomial.X_sub_C_ne_zero α

/-- The residue field at a linear place is isomorphic to Fq.

This is the evaluation map: Fq[X]/(X - α) → Fq via p ↦ p(α). -/
def linearPlace_residueField_equiv (α : Fq) :
    (Polynomial Fq ⧸ (linearPlace Fq α).asIdeal) ≃ₐ[Fq] Fq :=
  -- (linearPlace Fq α).asIdeal = Ideal.span {X - C α} by definition
  Polynomial.quotientSpanXSubCAlgEquiv α

/-- Linear places have degree 1. -/
theorem linearPlace_degree_eq_one (α : Fq) :
    residueFieldDegree (k := Fq) (linearPlace Fq α) = 1 := by
  unfold residueFieldDegree
  have e := linearPlace_residueField_equiv Fq α
  have h1 : Module.finrank Fq Fq = 1 := Module.finrank_self Fq
  rw [← h1]
  exact LinearEquiv.finrank_eq e.toLinearEquiv

/-- Linear places are rational. -/
theorem linearPlace_isRational (α : Fq) :
    isRationalPlace (k := Fq) (linearPlace Fq α) :=
  linearPlace_degree_eq_one Fq α

/-- The residue field at a linear place is finite-dimensional over Fq.

This is required for the trace map to be well-defined. -/
instance linearPlace_finiteDimensional (α : Fq) :
    FiniteDimensional Fq (Polynomial Fq ⧸ (linearPlace Fq α).asIdeal) := by
  have e := linearPlace_residueField_equiv Fq α
  -- Fq over Fq is finite-dimensional (dimension 1)
  haveI : FiniteDimensional Fq Fq := inferInstance
  -- Transfer via the linear equivalence: if W is fin-dim and V ≃ₗ W, then V is fin-dim
  exact LinearEquiv.finiteDimensional e.symm.toLinearEquiv

/-! ## Traced Residue Definition -/

/-- The traced residue at a linear place α.

For linear places, this equals the standard residue because the trace
from a degree-1 extension is the identity.

IMPLEMENTATION: We use the existing `residueAt` and show equality with
the traced version for linear places. -/
def residueAtLinearTraced (α : Fq) (f : RatFunc Fq) : Fq :=
  RiemannRochV2.Residue.residueAt α f

/-- The traced residue at a linear place equals the standard residue.

This is the key compatibility theorem for P¹. -/
theorem residueAtLinearTraced_eq_residueAt (α : Fq) (f : RatFunc Fq) :
    residueAtLinearTraced Fq α f = RiemannRochV2.Residue.residueAt α f :=
  rfl

/-- Traced residue at linear place is additive. -/
theorem residueAtLinearTraced_add (α : Fq) (f g : RatFunc Fq) :
    residueAtLinearTraced Fq α (f + g) =
    residueAtLinearTraced Fq α f + residueAtLinearTraced Fq α g := by
  simp only [residueAtLinearTraced]
  exact RiemannRochV2.Residue.residueAt_add α f g

/-- Traced residue at linear place respects scalar multiplication. -/
theorem residueAtLinearTraced_smul (α : Fq) (c : Fq) (f : RatFunc Fq) :
    residueAtLinearTraced Fq α (c • f) = c * residueAtLinearTraced Fq α f := by
  simp only [residueAtLinearTraced]
  exact RiemannRochV2.Residue.residueAt_smul α c f

end TracedResidue

/-! ## Global Residue Theorem with Traced Residues

For P¹, where all finite places are linear, the traced residue theorem
reduces to the standard residue theorem.

The general formulation (for arbitrary curves with higher-degree places)
would sum Tr_{κ(v)/k}(res_v(f)) over all finite places v.
-/

section GlobalResidueTheorem

variable (Fq : Type*) [Field Fq]

/-- Sum of traced residues at specified linear places.

This is the finite part of the residue sum for P¹. -/
def tracedResidueSum (S : Finset Fq) (f : RatFunc Fq) : Fq :=
  S.sum fun α => residueAtLinearTraced Fq α f

/-- Traced residue sum is additive. -/
theorem tracedResidueSum_add (S : Finset Fq) (f g : RatFunc Fq) :
    tracedResidueSum Fq S (f + g) =
    tracedResidueSum Fq S f + tracedResidueSum Fq S g := by
  unfold tracedResidueSum
  simp only [residueAtLinearTraced_add]
  rw [← Finset.sum_add_distrib]

/-- The global residue theorem for P¹ with traced residues.

This is equivalent to the standard residue theorem since all places are linear.

∑_{α ∈ S} Tr(res_α(f)) + res_∞(f) = 0

For P¹, Tr = id, so this is just:
∑_{α ∈ S} res_α(f) + res_∞(f) = 0
-/
theorem residue_sum_traced_eq_zero_P1 [Fintype Fq] (f : RatFunc Fq) (S : Finset Fq)
    (hS : ∀ α, α ∉ S → RiemannRochV2.Residue.residueAt α f = 0)
    (hsplit : ∃ p : Polynomial Fq, ∃ poles : Finset Fq, f =
      (algebraMap (Polynomial Fq) (RatFunc Fq) p) /
      (poles.prod fun a => RatFunc.X - RatFunc.C a)) :
    tracedResidueSum Fq S f + RiemannRochV2.Residue.residueAtInfty f = 0 := by
  -- The traced residue sum over S equals the full sum over Fq
  -- because residues outside S are zero by hypothesis hS
  have h_sum_eq : tracedResidueSum Fq S f =
      Finset.univ.sum (fun α => RiemannRochV2.Residue.residueAt α f) := by
    unfold tracedResidueSum residueAtLinearTraced
    rw [Finset.sum_subset (Finset.subset_univ S)]
    intro α _ hα
    exact hS α hα
  rw [h_sum_eq]
  -- The sum over Finset.univ equals residueSumFinite
  have h_eq_finite : Finset.univ.sum (fun α => RiemannRochV2.Residue.residueAt α f) =
      RiemannRochV2.residueSumFinite f := by
    rfl
  rw [h_eq_finite]
  -- Now residueSumFinite + residueAtInfty = residueSumTotal = 0 for split denominators
  have h_total : RiemannRochV2.residueSumFinite f + RiemannRochV2.Residue.residueAtInfty f =
      RiemannRochV2.residueSumTotal f := rfl
  rw [h_total]
  -- Apply the residue theorem for split denominators
  exact RiemannRochV2.residueSumTotal_splits f hsplit

end GlobalResidueTheorem

end RiemannRochV2.ResidueTrace

end
