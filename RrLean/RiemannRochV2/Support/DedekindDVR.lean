/-
# DVR Structure for General Dedekind Domains

This file proves that `adicCompletionIntegers` is a DVR for ANY Dedekind domain,
without requiring the residue field to be finite.

## Key Result

For any Dedekind domain R with fraction field K and height-one prime v:

```lean
instance : IsDiscreteValuationRing (v.adicCompletionIntegers K)
```

This generalizes Mathlib's NumberField-specific instance.

## Note

The proofs follow Mathlib's `NumberField.FinitePlaces.lean` but with weaker hypotheses.
The key insight is that the DVR and PID properties only require:
1. The valuation is surjective (giving nontrivial range)
2. A uniformizer exists (always true for HeightOneSpectrum)

Neither requires finite residue fields (which IS needed for compactness).
-/

import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.Algebra.Order.Archimedean.Submonoid
import Mathlib.Data.Int.WithZero
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Archimedean

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZeroMulInt WithZero
open scoped Valued

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

namespace RiemannRochV2.DedekindDVR

/-! ## MulArchimedean for the valuation range

Since ℤ is Archimedean, ℤᵐ⁰ = WithZero (Multiplicative ℤ) is MulArchimedean.
This carries to any submonoid, including the range of Valued.v.
-/

-- The valuation range is a submonoid of ℤᵐ⁰, which is MulArchimedean
instance mulArchimedean_mrange :
    MulArchimedean (MonoidHom.mrange (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) :=
  SubmonoidClass.instMulArchimedean _

/-! ## Principal Ideal Ring

The adicCompletionIntegers is a PID because the valuation has non-densely-ordered range.
-/

/-- The adic completion integers form a principal ideal ring. -/
instance isPrincipalIdealRing_adicCompletionIntegers :
    IsPrincipalIdealRing (v.adicCompletionIntegers K) := by
  unfold HeightOneSpectrum.adicCompletionIntegers
  rw [(Valuation.valuationSubring.integers (Valued.v)).isPrincipalIdealRing_iff_not_denselyOrdered,
    WithZero.denselyOrdered_set_iff_subsingleton]
  exact Valued.v.toMonoidWithZeroHom.range_nontrivial.not_subsingleton

/-! ## Discrete Valuation Ring

The adicCompletionIntegers is a DVR. This follows from being a PID that is not a field.
-/

/-- The adic completion integers form a discrete valuation ring. -/
instance isDiscreteValuationRing_adicCompletionIntegers :
    IsDiscreteValuationRing (v.adicCompletionIntegers K) where
  not_a_field' := by
    unfold HeightOneSpectrum.adicCompletionIntegers
    simp only [ne_eq, Ideal.ext_iff, Valuation.mem_maximalIdeal_iff, Ideal.mem_bot, Subtype.ext_iff,
      ZeroMemClass.coe_zero, Subtype.forall, Valuation.mem_valuationSubring_iff, not_forall,
      exists_prop]
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    use π
    simp [hπ, ← exp_zero, - exp_neg, ← (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_eq_zero_iff]

/-! ## Summary

We have proved:
1. `isPrincipalIdealRing_adicCompletionIntegers`: O_v is a PID
2. `isDiscreteValuationRing_adicCompletionIntegers`: O_v is a DVR

These instances are available for ALL Dedekind domains, without any finiteness hypothesis
on the residue field. This generalizes Mathlib's NumberField-specific instances.
-/

end RiemannRochV2.DedekindDVR

end
