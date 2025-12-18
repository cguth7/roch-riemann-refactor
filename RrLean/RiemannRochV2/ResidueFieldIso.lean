/-
# Residue Field Isomorphism for Adic Completions

This file proves that for a Dedekind domain R with fraction field K and a height-one prime v,
the residue field of the adic completion is isomorphic to R ⧸ v.asIdeal.

This allows us to transfer finiteness from `R ⧸ v.asIdeal` to the completion's residue field,
which is the key step needed to discharge the `FiniteCompletionResidueFields` axiom.

## Main Results

* `residueFieldIso`: ResidueField(v.adicCompletionIntegers K) ≃+* R ⧸ v.asIdeal
* `finite_residueField_of_finite_quotient`: If R ⧸ v.asIdeal is finite, so is the completion's
  residue field.

## Strategy

1. Show algebraMap R → adicCompletionIntegers sends v.asIdeal to maximal ideal
   (using valuation < 1 characterization)
2. Show the induced map R ⧸ v.asIdeal → ResidueField is bijective
   - Injective: valuation preservation
   - Surjective: density of R in completion
-/

import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Valuation.RankOne
import RrLean.RiemannRochV2.AdelicTopology
import RrLean.RiemannRochV2.DedekindDVR
import RrLean.RiemannRochV2.AllIntegersCompactProof

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Valued NNReal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace RiemannRochV2.ResidueFieldIso

/-! ## Step 1: algebraMap sends v.asIdeal to the maximal ideal -/

/-- Elements of v.asIdeal map to elements with valuation < 1 in the completion. -/
lemma algebraMap_mem_asIdeal_val_lt_one (v : HeightOneSpectrum R) (r : R) (hr : r ∈ v.asIdeal) :
    Valued.v (algebraMap R (v.adicCompletion K) r) < 1 := by
  rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
  exact (v.intValuation_lt_one_iff_mem r).mpr hr

/-- Elements not in v.asIdeal map to elements with valuation = 1 in the completion. -/
lemma algebraMap_notMem_asIdeal_val_eq_one (v : HeightOneSpectrum R) (r : R) (hr : r ∉ v.asIdeal) :
    Valued.v (algebraMap R (v.adicCompletion K) r) = 1 := by
  rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
  exact v.intValuation_eq_one_iff.mpr hr

/-- The algebraMap from R to adicCompletionIntegers. -/
def algebraMapToIntegers (v : HeightOneSpectrum R) : R →+* v.adicCompletionIntegers K :=
  algebraMap R (v.adicCompletionIntegers K)

/-- The composition: R → adicCompletionIntegers → ResidueField -/
def toResidueField (v : HeightOneSpectrum R) : R →+* Valued.ResidueField (v.adicCompletion K) :=
  (IsLocalRing.residue (v.adicCompletionIntegers K)).comp (algebraMapToIntegers v)

/-- Elements of v.asIdeal map to 0 in the residue field. -/
lemma toResidueField_mem_asIdeal (v : HeightOneSpectrum R) (r : R) (hr : r ∈ v.asIdeal) :
    toResidueField (K := K) v r = 0 := by
  -- Need to show algebraMap v r is in the maximal ideal
  -- The maximal ideal of a valuation subring consists of elements with val < 1
  have hnu : ¬IsUnit (algebraMap R (v.adicCompletionIntegers K) r) := by
    intro hu
    -- If algebraMap v r is a unit, its valuation equals 1
    have hval1 : Valued.v ((algebraMap R (v.adicCompletionIntegers K) r) : v.adicCompletion K) = 1 := by
      have hint : Valuation.Integers Valued.v (v.adicCompletionIntegers K) :=
        Valuation.integer.integers Valued.v
      exact (hint.isUnit_iff_valuation_eq_one).mp hu
    -- But r ∈ v.asIdeal means valuation < 1
    have hval_lt : Valued.v (algebraMap R (v.adicCompletion K) r) < 1 :=
      algebraMap_mem_asIdeal_val_lt_one v r hr
    -- Contradiction: the coercions give the same element
    have heq : ((algebraMap R (v.adicCompletionIntegers K) r) : v.adicCompletion K) =
        algebraMap R (v.adicCompletion K) r := rfl
    rw [heq] at hval1
    exact (ne_of_lt hval_lt) hval1
  -- Now show residue = 0
  have hmem : algebraMap R (v.adicCompletionIntegers K) r ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rw [← IsLocalRing.residue_eq_zero_iff] at hmem
  exact hmem

/-- The kernel of toResidueField contains v.asIdeal. -/
lemma asIdeal_le_ker_toResidueField (v : HeightOneSpectrum R) :
    v.asIdeal ≤ RingHom.ker (toResidueField (K := K) v) := by
  intro r hr
  rw [RingHom.mem_ker]
  exact toResidueField_mem_asIdeal v r hr

/-! ## Step 2: The kernel equals v.asIdeal (injectivity) -/

/-- If r maps to 0 in the residue field, then r ∈ v.asIdeal. -/
lemma ker_toResidueField_le_asIdeal (v : HeightOneSpectrum R) :
    RingHom.ker (toResidueField (K := K) v) ≤ v.asIdeal := by
  intro r hr
  rw [RingHom.mem_ker] at hr
  -- hr : toResidueField v r = 0
  -- This means the residue of algebraMap r is 0, so algebraMap r is in the maximal ideal
  have hmem : algebraMap R (v.adicCompletionIntegers K) r ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hne := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu
    exact hne hr
  -- In maximal ideal means non-unit means valuation < 1
  have hnu : ¬IsUnit (algebraMap R (v.adicCompletionIntegers K) r) := by
    rwa [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
  -- Non-unit in valuation subring means valuation < 1
  have hval_lt : Valued.v ((algebraMap R (v.adicCompletionIntegers K) r) : v.adicCompletion K) < 1 := by
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hnu
    exact hnu
  -- The valuation equals the original valuation
  have heq : ((algebraMap R (v.adicCompletionIntegers K) r) : v.adicCompletion K) =
      algebraMap R (v.adicCompletion K) r := rfl
  rw [heq, valuedAdicCompletion_eq_valuation, valuation_of_algebraMap,
      (v.intValuation_lt_one_iff_mem r)] at hval_lt
  exact hval_lt

/-- The kernel of toResidueField equals v.asIdeal. -/
lemma ker_toResidueField_eq_asIdeal (v : HeightOneSpectrum R) :
    RingHom.ker (toResidueField (K := K) v) = v.asIdeal :=
  le_antisymm (ker_toResidueField_le_asIdeal v) (asIdeal_le_ker_toResidueField v)

/-! ## Step 3: Surjectivity (density argument)

This is the harder part. We need to show that every element of the residue field
is represented by an element of R.

For now, we axiomatize surjectivity. This requires proving that R is dense enough
in the completion that it maps onto the residue field.
-/

-- Axiom: surjectivity of the residue field map from R
-- This follows from density of R in the completion, but the proof is non-trivial.
axiom toResidueField_surjective (v : HeightOneSpectrum R) :
    Function.Surjective (toResidueField (K := K) v)

/-! ## Step 4: The ring isomorphism -/

/-- The residue field of the adic completion is isomorphic to R ⧸ v.asIdeal. -/
def residueFieldIso (v : HeightOneSpectrum R) :
    (R ⧸ v.asIdeal) ≃+* Valued.ResidueField (v.adicCompletion K) := by
  let f := Ideal.Quotient.lift v.asIdeal (toResidueField (K := K) v)
      (fun r hr => toResidueField_mem_asIdeal v r hr)
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · -- Injective: use ker = v.asIdeal
    intro x y hxy
    obtain ⟨rx, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨ry, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq]
    have : toResidueField (K := K) v rx = toResidueField (K := K) v ry := by
      simp only [f, Ideal.Quotient.lift_mk] at hxy
      exact hxy
    have hdiff : toResidueField (K := K) v (rx - ry) = 0 := by
      simp only [map_sub, this, sub_self]
    have hmem : rx - ry ∈ RingHom.ker (toResidueField (K := K) v) := hdiff
    rw [ker_toResidueField_eq_asIdeal] at hmem
    exact hmem
  · -- Surjective: follows from toResidueField_surjective
    intro x
    obtain ⟨r, hr⟩ := toResidueField_surjective (K := K) v x
    use Ideal.Quotient.mk v.asIdeal r
    simp only [f, Ideal.Quotient.lift_mk, hr]

/-! ## Step 5: Finiteness transfer -/

/-- If R ⧸ v.asIdeal is finite, then the residue field of the completion is finite. -/
theorem finite_residueField_of_finite_quotient (v : HeightOneSpectrum R)
    [h : Finite (R ⧸ v.asIdeal)] :
    Finite (Valued.ResidueField (v.adicCompletion K)) :=
  Finite.of_equiv (R ⧸ v.asIdeal) (residueFieldIso (K := K) v)

/-! ## Step 6: Connection to FiniteCompletionResidueFields -/

/-- For function fields: if all quotients R ⧸ v.asIdeal are finite, then
FiniteCompletionResidueFields holds. -/
def finiteCompletionResidueFields_of_finite_quotients
    (h : ∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)) :
    AllIntegersCompactProof.FiniteCompletionResidueFields R K where
  finite v := @finite_residueField_of_finite_quotient R _ _ K _ _ _ v (h v)

end RiemannRochV2.ResidueFieldIso

end
