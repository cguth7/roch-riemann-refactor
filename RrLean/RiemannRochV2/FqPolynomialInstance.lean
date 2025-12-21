/-
# Concrete Instance: Fq[X] with Fraction Field RatFunc(Fq)

This file provides concrete instances of `FiniteCompletionResidueFields` and `AllIntegersCompact`
for the polynomial ring Fq[X] over a finite field Fq, with fraction field RatFunc Fq.

## Main Results

* `IsDedekindDomain (Polynomial Fq)` - automatic from PID
* `IsFractionRing (Polynomial Fq) (RatFunc Fq)` - standard
* `finite_quotient_polynomial` - R/v.asIdeal is finite for all height-one primes
* `instFiniteCompletionResidueFields` - FiniteCompletionResidueFields for Fq[X]
* `instAllIntegersCompact` - AllIntegersCompact for Fq[X]

## Key Insight

For Fq[X] over a finite field Fq:
1. Height-one primes are exactly (p) for irreducible polynomials p
2. Fq[X]/(p) is a finite extension of Fq (degree = deg p)
3. Module.finite_of_finite: finite field + finite-dimensional extension → finite ring
4. ResidueFieldIso: residue field of completion ≃ R/v.asIdeal
5. AllIntegersCompactProof.allIntegersCompact_of_axioms gives the result

## Status

WORK IN PROGRESS - This file establishes the concrete instance to validate the pipeline.
-/

import Mathlib.NumberTheory.FunctionField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.Finiteness.Cardinality
import RrLean.RiemannRochV2.AllIntegersCompactProof
import RrLean.RiemannRochV2.ResidueFieldIso

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq Fq]

namespace FqPolynomialInstance

/-! ## Step 1: Polynomial Fq is a Dedekind Domain

This follows automatically:
- Polynomial Fq is a EuclideanDomain (Polynomial.instEuclideanDomain)
- EuclideanDomain → IsPrincipalIdealRing (EuclideanDomain.to_principal_ideal_domain)
- IsPrincipalIdealRing + IsDomain → IsDedekindDomain (IsPrincipalIdealRing.isDedekindDomain)
-/

-- Polynomial Fq has all the required instances automatically
example : EuclideanDomain Fq[X] := inferInstance
example : IsDomain Fq[X] := inferInstance
example : IsPrincipalIdealRing Fq[X] := inferInstance
example : IsDedekindDomain Fq[X] := inferInstance

/-! ## Step 2: RatFunc Fq is the Fraction Field

This is standard from Mathlib.
-/

example : IsFractionRing Fq[X] (RatFunc Fq) := inferInstance

/-! ## Step 3: Quotients by Height-One Primes are Finite

For a height-one prime v in Fq[X], the quotient Fq[X]/v.asIdeal is:
1. A finite extension of Fq (since Fq[X] is a PID, height-one = maximal, quotient is a field)
2. Finite-dimensional as an Fq-vector space (degree equals the degree of the generator)
3. Finite as a type (Module.finite_of_finite)
-/

/-- The quotient Fq[X]/v.asIdeal is finite for any height-one prime v.

Proof: v is principal (Fq[X] is a PID), so v = (p) for some polynomial p.
Normalizing p gives a monic polynomial with the same ideal.
Quotient by monic polynomial is finite-dimensional over Fq.
Module.finite_of_finite transfers to Finite type.
-/
instance finite_quotient_polynomial (v : HeightOneSpectrum Fq[X]) :
    Finite (Fq[X] ⧸ v.asIdeal) := by
  classical
  -- In a PID, all ideals are principal - get generator p with v.asIdeal = span {p}
  have hprinc := IsPrincipalIdealRing.principal v.asIdeal
  let p := hprinc.generator
  have hp : v.asIdeal = Ideal.span {p} := hprinc.span_singleton_generator.symm
  -- p is nonzero since v ≠ ⊥
  have hp_ne : p ≠ 0 := by
    intro hp0
    have : v.asIdeal = ⊥ := by rw [hp, hp0, Ideal.span_singleton_eq_bot]
    exact v.ne_bot this
  -- Normalize p to make it monic
  have hmonic : Polynomial.Monic (normalize p) := Polynomial.monic_normalize hp_ne
  -- Normalization preserves the ideal (Associated → same span)
  have hnorm : Ideal.span {normalize p} = Ideal.span {p} :=
    Ideal.span_singleton_eq_span_singleton.mpr (associated_normalize p).symm
  -- Quotient by monic polynomial is finite dimensional over Fq
  haveI : Module.Finite Fq (Fq[X] ⧸ Ideal.span {normalize p}) := hmonic.finite_quotient
  -- Transfer to v.asIdeal using hp and hnorm
  haveI : Module.Finite Fq (Fq[X] ⧸ v.asIdeal) := by rw [hp, ← hnorm]; infer_instance
  -- Finite Fq + Module.Finite Fq M → Finite M
  exact Module.finite_of_finite Fq

/-! ## Step 4: FiniteCompletionResidueFields Instance

Using ResidueFieldIso.finiteCompletionResidueFields_of_finite_quotients, we get the instance.
-/

instance instFiniteCompletionResidueFields :
    RiemannRochV2.AllIntegersCompactProof.FiniteCompletionResidueFields Fq[X] (RatFunc Fq) :=
  RiemannRochV2.ResidueFieldIso.finiteCompletionResidueFields_of_finite_quotients
    (fun v => finite_quotient_polynomial v)

/-! ## Step 5: AllIntegersCompact Instance

Using AllIntegersCompactProof.allIntegersCompact_of_axioms, we get the final result.
-/

instance instAllIntegersCompact :
    RiemannRochV2.AdelicTopology.AllIntegersCompact Fq[X] (RatFunc Fq) :=
  RiemannRochV2.AllIntegersCompactProof.allIntegersCompact_of_axioms Fq[X] (RatFunc Fq)

/-! ## Final Summary

For Fq[X] / RatFunc(Fq), we have instantiated:
1. ✅ `IsDedekindDomain (Polynomial Fq)` - automatic from PID
2. ✅ `Finite (Fq[X] ⧸ v.asIdeal)` - proved via finite extension
3. ✅ `FiniteCompletionResidueFields Fq[X] (RatFunc Fq)` - via ResidueFieldIso
4. ✅ `AllIntegersCompact Fq[X] (RatFunc Fq)` - via AllIntegersCompactProof

This validates the full pipeline from concrete finite field to adelic compactness.

**Note (Cycle 121)**: DiscreteCocompactEmbedding for *finite* adeles was attempted but
K is NOT discrete in the finite adeles (neighborhoods contain infinitely many polynomials).
Discreteness requires including the place at infinity via FullAdeleRing.
See FullAdelesBase.lean and FullAdelesCompact.lean for the correct approach.
-/

end FqPolynomialInstance

end
