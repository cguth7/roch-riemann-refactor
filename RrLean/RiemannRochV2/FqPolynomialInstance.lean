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

/-! ## Summary (AllIntegersCompact)

We have now instantiated:
1. `IsDedekindDomain (Polynomial Fq)` - automatic from PID
2. `Finite (Fq[X] ⧸ v.asIdeal)` - proved via finite extension
3. `FiniteCompletionResidueFields Fq[X] (RatFunc Fq)` - via ResidueFieldIso
4. `AllIntegersCompact Fq[X] (RatFunc Fq)` - via AllIntegersCompactProof

This validates the full pipeline from concrete finite field to adelic compactness!
-/

/-! ## Step 6: DiscreteCocompactEmbedding for Fq[X]

For Fq[X] (a PID), the discrete cocompact embedding of RatFunc(Fq) into the finite adeles
follows from:

1. **Discrete**: Elements of RatFunc(Fq) have trivial valuation at all but finitely many places
   (only finitely many primes divide a nonzero polynomial).

2. **Closed**: Follows from discrete + locally compact + T2 (Mathlib: `Subgroup.isClosed_of_discrete`)

3. **Compact fundamental domain**: For a PID, the integral adeles ∏_v O_v form a fundamental domain.
   This is because any fractional ideal is principal, so "clearing denominators" always works.

**Mathematical Background**:

For K = RatFunc(Fq) and R = Fq[X]:
- The diagonal embedding K → FiniteAdeleRing sends f/g to (f/g at each place)
- K ∩ (∏_v O_v) = R (elements integral at all finite places)
- For any a = (a_v) in the finite adeles, since Fq[X] is a PID:
  - Only finitely many v have a_v ∉ O_v (by restricted product definition)
  - We can find x ∈ K such that a - x ∈ ∏_v O_v (weak approximation + PID)
- The quotient structure is simple: class group = 0 for PIDs
-/

section DiscreteCocompactFqPolynomial

open RiemannRochV2.AdelicTopology

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-! ### Discreteness of K in finite adeles

The key insight: for any nonzero f ∈ RatFunc(Fq), only finitely many height-one primes
divide f (i.e., have v(f) ≠ 0). This makes K discrete in the restricted product topology.
-/

/-- Nonzero elements of K have trivial valuation at almost all places.
This is the "almost all valuations are 1" property. -/
lemma valuation_eq_one_almost_all (f : RatFunc Fq) (hf : f ≠ 0) :
    {v : HeightOneSpectrum Fq[X] | v.valuation (RatFunc Fq) f ≠ 1}.Finite := by
  -- Elements of RatFunc Fq are quotients a/b of polynomials
  -- Only finitely many irreducible polynomials divide a or b
  -- Those are exactly the places where valuation ≠ 1
  sorry

/-
**Neighborhood basis at 0** (informal description):
For the finite adeles, neighborhoods of 0 are determined by valuation bounds at finitely many places.
The restricted product topology has basis neighborhoods:
{a | ∀ v ∈ S, v(a_v) ≥ n_v} ∩ {a | ∀ v ∉ S, a_v ∈ O_v}
for finite S and integers n_v.

This is a standard result about restricted products, but formalizing it requires
careful navigation of Mathlib's product/restricted product topology API.
-/

/-- K is discrete in the finite adeles: the diagonal image has discrete topology.

Proof sketch:
- For any nonzero f ∈ K, let S = {v | v(f) ≠ 1} (finite)
- A neighborhood of f excludes all other elements of K:
  - If g ≠ f and g is close to f at places in S, then g - f ≠ 0 but close to 0 at S
  - But g - f must have some v(g - f) ≠ 1, which is bounded away from 0
-/
theorem discrete_diagonal_embedding :
    DiscreteTopology (Set.range (diagonalEmbedding Fq[X] (RatFunc Fq))) := by
  -- To show discrete, we show every singleton is open in the subspace topology
  -- This follows from valuation_eq_one_almost_all: nonzero elements have bounded support
  rw [discreteTopology_iff_forall_isClosed]
  intro s
  -- Every subset of a discrete space is closed
  sorry

/-- K is closed in the finite adeles.

For locally compact groups, discrete subgroups are closed.
Since FiniteAdeleRing is locally compact (under AllIntegersCompact) and
K embeds as an additive subgroup, discreteness implies closedness.
-/
theorem closed_diagonal_embedding [AllIntegersCompact Fq[X] (RatFunc Fq)] :
    IsClosed (Set.range (diagonalEmbedding Fq[X] (RatFunc Fq))) := by
  -- The range is an additive subgroup
  -- Discrete subgroups of T2 locally compact groups are closed
  sorry

/-! ### Compact fundamental domain for PIDs

For Fq[X] (a PID), the integral adeles form a compact fundamental domain.
This is the key result that uses the PID structure.
-/

/-- The integral adeles: elements (a_v) with a_v ∈ O_v for all v. -/
def integralAdeles : Set (FiniteAdeleRing Fq[X] (RatFunc Fq)) :=
  {a | ∀ v, a.val v ∈ v.adicCompletionIntegers (RatFunc Fq)}

/-- The integral adeles are compact (product of compact sets). -/
theorem isCompact_integralAdeles [AllIntegersCompact Fq[X] (RatFunc Fq)] :
    IsCompact (integralAdeles Fq) := by
  -- Each O_v is compact by AllIntegersCompact
  -- The restricted product with compact factors is compact
  sorry

/-- For a PID, any element of the finite adeles can be shifted by K to land in the integral adeles.

This is weak approximation + clearing denominators:
- Given a = (a_v) in finite adeles, only finitely many v have a_v ∉ O_v
- For those v, find p_v uniformizer with large enough power to clear denominators
- Since Fq[X] is PID, the ideal ∏_v p_v^{n_v} is principal, generated by some f
- Then a - f⁻¹ · something lands in integral adeles

**Mathematical detail**: This is where PID is essential. For non-PIDs with nontrivial
class group, we'd only get a compact quotient after quotienting by units, not by K itself.
-/
theorem exists_K_translate_in_integralAdeles (a : FiniteAdeleRing Fq[X] (RatFunc Fq)) :
    ∃ x : RatFunc Fq, a - diagonalEmbedding Fq[X] (RatFunc Fq) x ∈ integralAdeles Fq := by
  sorry

/-- DiscreteCocompactEmbedding instance for Fq[X] / RatFunc(Fq).

This combines:
1. discrete_diagonal_embedding (K is discrete in A_K^fin)
2. closed_diagonal_embedding (K is closed in A_K^fin)
3. exists_K_translate_in_integralAdeles + isCompact_integralAdeles (compact fundamental domain)
-/
instance instDiscreteCocompactEmbedding [AllIntegersCompact Fq[X] (RatFunc Fq)] :
    DiscreteCocompactEmbedding Fq[X] (RatFunc Fq) where
  discrete := discrete_diagonal_embedding Fq
  closed := closed_diagonal_embedding Fq
  compact_fundamental_domain := by
    refine ⟨integralAdeles Fq, isCompact_integralAdeles Fq, ?_⟩
    intro a
    exact exists_K_translate_in_integralAdeles Fq a

end DiscreteCocompactFqPolynomial

/-! ## Final Summary

For Fq[X] / RatFunc(Fq), we now have instances for BOTH key axiom classes:

1. ✅ `AllIntegersCompact Fq[X] (RatFunc Fq)` - via finite quotients + ResidueFieldIso
2. ✅ `DiscreteCocompactEmbedding Fq[X] (RatFunc Fq)` - via PID structure

**Remaining sorries** (for DiscreteCocompactEmbedding):
- `valuation_eq_one_almost_all` - finiteness of divisors
- `discrete_diagonal_embedding` - discreteness from valuation bounds
- `closed_diagonal_embedding` - closedness from discrete + locally compact
- `isCompact_integralAdeles` - compactness of restricted product
- `exists_K_translate_in_integralAdeles` - weak approximation for PIDs

These are all standard results in algebraic number theory / function field theory.
The proofs require careful navigation of Mathlib's adelic topology API.

**Significance**:
- This validates the full axiom structure for the simplest function field case
- For other function fields over finite k, the same pattern applies but with
  class group considerations for the fundamental domain
-/

end FqPolynomialInstance

end
