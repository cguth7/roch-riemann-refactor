/-
# AllIntegersCompact: Incremental Proof

Goal: Prove `CompactSpace (v.adicCompletionIntegers K)` using Mathlib's compactness theorem.

## Key Mathlib Theorem

```
Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField :
    CompactSpace 𝒪[K] ↔ CompleteSpace 𝒪[K] ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K]
```

This requires `Valuation.RankOne` on the valuation.

## Key Result: DVR is PROVED (not axiomatized!)

See `DedekindDVR.lean` for the proof that:
```lean
instance : IsDiscreteValuationRing (v.adicCompletionIntegers K)
```
This holds for ALL Dedekind domains, without any finiteness hypothesis.
-/

import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Valuation.RankOne
import RrLean.RiemannRochV2.Adelic.AdelicTopology
import RrLean.RiemannRochV2.Support.DedekindDVR

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Valued NNReal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace RiemannRochV2.AllIntegersCompactProof

/-! ## Step 1: Understand what we need

The compactness theorem requires:
1. `RankOne` instance on `Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))`
2. `Finite` residue field

Let's first check what instances are available.
-/

-- Check: What is the type of adicCompletionIntegers?
#check @HeightOneSpectrum.adicCompletionIntegers
-- adicCompletionIntegers : (v : HeightOneSpectrum R) → K → ValuationSubring (adicCompletion K v)

-- Check: What is adicCompletion?
#check @HeightOneSpectrum.adicCompletion
-- adicCompletion : K → (v : HeightOneSpectrum R) → Type*
-- It's the completion of K with respect to v-adic valuation

-- Check: The Valued instance on adicCompletion
#check @Valued.v
-- For v.adicCompletion K, Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))

-- Check: The compactness theorem
#check @Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
-- Requires: [RankOne Valued.v]

/-! ## Step 2: The blocking issue

The compactness theorem requires `Valuation.RankOne` on `Valued.v`.

For NumberFields, Mathlib provides this via `instRankOneValuedAdicCompletion`.
For general Dedekind domains, we need to either:
1. Axiomatize it
2. Construct it from `MulArchimedean` + `IsNontrivial`

The valuation is nontrivial (it surjects onto WithZero (Multiplicative ℤ)).
-/

-- Check: Surjectivity of the valuation
#check @valuedAdicCompletion_surjective
-- valuedAdicCompletion_surjective K v : Function.Surjective Valued.v

-- Check: nonempty_rankOne_iff_mulArchimedean
#check @Valuation.nonempty_rankOne_iff_mulArchimedean
-- Says: Nonempty v.RankOne ↔ MulArchimedean Γ₀ (when v.IsNontrivial)

/-! ## Step 3: What we've proved vs what remains

**PROVED** (see DedekindDVR.lean):
- `IsDiscreteValuationRing (v.adicCompletionIntegers K)` for ALL Dedekind domains!

**Still needed** (axiomatized or to be proved):
- `RankOne` on the valuation - requires a finite residue field
- `Finite` residue field - depends on the specific Dedekind domain

For function fields over finite k, both should be provable.
-/

variable (R K)

/-! ## Step 4: Verify the existing axiom approach works -/

-- The existing AllIntegersCompact is already the right abstraction
#check RiemannRochV2.AdelicTopology.AllIntegersCompact
-- class AllIntegersCompact : Prop where
--   compact : ∀ v, CompactSpace (v.adicCompletionIntegers K)

/-! ## Documenting the discharge path

To instantiate `AllIntegersCompact` for a specific function field k(C)/k:

1. **Finite residue fields**: For k finite, each residue field is a finite extension of k
2. **IsDiscreteValuationRing**: Each adicCompletionIntegers is a DVR
   - Proof: Local ring + principal ideals (follows from completing a DVR)
3. **CompleteSpace**: Automatic from completion construction
4. **RankOne**: Construct using |R/v| as exponential base
5. Apply compactSpace_iff... to get CompactSpace

For now, we keep `AllIntegersCompact` as an axiom (Track A approach).
The instances above would need to be proved for Track B.
-/

/-! ## Remaining axioms (after DVR is proved)

The DVR property is now PROVED in DedekindDVR.lean. Only these remain:
-/

-- DVR is now a theorem! (see DedekindDVR.lean)
-- We get this automatically via the import:
-- instance : IsDiscreteValuationRing (v.adicCompletionIntegers K)

/-- The adic completion valuation is nontrivial: there exists a uniformizer with valuation exp(-1).
This follows from `valuation_exists_uniformizer`. -/
instance isNontrivial_adicCompletionValuation (v : HeightOneSpectrum R) :
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).IsNontrivial := by
  rw [Valuation.isNontrivial_iff_exists_lt_one]
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  -- π : K with v.valuation K π = exp(-1)
  -- We use the coercion K → v.adicCompletion K
  use (π : v.adicCompletion K)
  constructor
  · intro hπ0
    -- If ↑π = 0 in adicCompletion, then Valued.v ↑π = 0
    -- But by valuedAdicCompletion_eq_valuation', Valued.v ↑π = v.valuation K π = exp(-1) ≠ 0
    have hv0 : Valued.v (π : v.adicCompletion K) = 0 := by
      rw [hπ0, Valuation.map_zero]
    rw [valuedAdicCompletion_eq_valuation', hπ] at hv0
    exact WithZero.coe_ne_zero hv0
  · rw [valuedAdicCompletion_eq_valuation', hπ]
    exact WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0)

/-- RankOne for the adic completion valuation follows from MulArchimedean.
Since ℤ is Archimedean, WithZero (Multiplicative ℤ) is MulArchimedean, and
with IsNontrivial we get RankOne. -/
def rankOne_adicCompletionValuation (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    Valuation.RankOne (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))) :=
  (Valuation.nonempty_rankOne_iff_mulArchimedean.mpr inferInstance).some

/-! ## Legacy axiom (now superseded by instances above) -/

/-- Axiom: All adic completion valuations have rank one.
DEPRECATED: Now this is a theorem, not an axiom! See `rankOne_adicCompletionValuation` above. -/
class RankOneValuations where
  rankOne : ∀ v : HeightOneSpectrum R, Valuation.RankOne
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))

/-- RankOneValuations is now trivially satisfied since we have the instances. -/
instance rankOneValuations_instance : RankOneValuations R K where
  rankOne v := rankOne_adicCompletionValuation R K v

/-- Axiom: All residue fields of adic completions are finite. -/
class FiniteCompletionResidueFields : Prop where
  finite : ∀ v : HeightOneSpectrum R, Finite (Valued.ResidueField (v.adicCompletion K))

/-- The adicCompletionIntegers is a closed subset of adicCompletion. -/
lemma isClosed_adicCompletionIntegers (v : HeightOneSpectrum R) :
    IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isClosed_valuationSubring (v.adicCompletion K)

/-- The adicCompletionIntegers is complete (as a closed subset of a complete space). -/
instance completeSpace_adicCompletionIntegers (v : HeightOneSpectrum R) :
    CompleteSpace (v.adicCompletionIntegers K) := by
  haveI : IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isClosed_adicCompletionIntegers (R := R) K v
  exact IsClosed.completeSpace_coe

/-- Each adicCompletionIntegers is compact, given only the finite residue field axiom.
Note: DVR and RankOne are now automatically available as theorems! -/
theorem compactSpace_adicCompletionIntegers
    [FiniteCompletionResidueFields R K]
    (v : HeightOneSpectrum R) :
    CompactSpace (v.adicCompletionIntegers K) := by
  -- RankOne is now a theorem! (from rankOne_adicCompletionValuation)
  letI hrank := rankOne_adicCompletionValuation R K v
  -- DVR is now a theorem! (from DedekindDVR.lean)
  haveI hdvr : IsDiscreteValuationRing (v.adicCompletionIntegers K) :=
    RiemannRochV2.DedekindDVR.isDiscreteValuationRing_adicCompletionIntegers (K := K) v
  -- Only the finite residue field is still an axiom
  haveI hfinite := FiniteCompletionResidueFields.finite (R := R) (K := K) v
  -- adicCompletionIntegers K v = 𝒪[adicCompletion K v] by definition
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨completeSpace_adicCompletionIntegers (R := R) K v, hdvr, hfinite⟩

/-- AllIntegersCompact follows from only the FiniteCompletionResidueFields axiom.
DVR and RankOne are now proved for ALL Dedekind domains! -/
theorem allIntegersCompact_of_axioms
    [FiniteCompletionResidueFields R K] :
    RiemannRochV2.AdelicTopology.AllIntegersCompact R K :=
  ⟨fun v => compactSpace_adicCompletionIntegers R K v⟩

/-! ## Summary (Cycle 108 Update)

**Axiom hierarchy** (simplified - TWO of THREE requirements now PROVED!):
```
PROVED (Cycle 105):
  IsDiscreteValuationRing (v.adicCompletionIntegers K)  ← DedekindDVR.lean

PROVED (Cycle 106):
  RankOne (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)  ← rankOne_adicCompletionValuation

PROVED (automatic):
  CompleteSpace (v.adicCompletionIntegers K)  ← completeSpace_adicCompletionIntegers

REMAINING AXIOM (ONLY ONE!):
  FiniteCompletionResidueFields R K
         |
         v
  compactSpace_adicCompletionIntegers  (uses compactSpace_iff...)
         |
         v
  AllIntegersCompact R K
```

**Residue Field Analysis (Cycle 108 Deep Dive)**:

The remaining axiom requires: `Finite (Valued.ResidueField (v.adicCompletion K))`

Where `Valued.ResidueField K = IsLocalRing.ResidueField (Valued.integer K) = 𝒪[K] ⧸ 𝓂[K]`

**Key Finding (Cycle 108)**: The residue field isomorphism is NOT in Mathlib!

The standard mathematical fact that "completion preserves residue fields" is NOT formalized:
```
ResidueField(O_v^) ≅ R ⧸ v.asIdeal
```
where O_v^ = v.adicCompletionIntegers K is the valuation ring of the completion.

**Mathlib has**:
- `Valued.ResidueField K := IsLocalRing.ResidueField 𝒪[K]` (definition)
- `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField` (compactness theorem)
- `finite_quotient_maximalIdeal_pow_of_finite_residueField` (finite powers from finite residue)

**Mathlib does NOT have** (as of v4.16.0):
- ResidueField(completion) ≃ ResidueField(original)
- Any direct connection between R ⧸ v.asIdeal and the completion's residue field

**Why this isomorphism is needed**:

For function fields k(C)/k where k is finite:
1. R ⧸ v.asIdeal is a finite extension of k (standard fact about function fields)
2. Therefore R ⧸ v.asIdeal is finite
3. The completion O_v^ has maximal ideal generated by a uniformizer
4. The residue field O_v^ ⧸ 𝓂 should be isomorphic to R ⧸ v.asIdeal
5. This would give Finite (Valued.ResidueField (v.adicCompletion K))

**Possible approaches to discharge**:

1. **Prove the isomorphism directly**: Show that the natural map
   `R → v.adicCompletion K → 𝒪[v.adicCompletion K] → 𝓀[v.adicCompletion K]`
   factors through R ⧸ v.asIdeal and is an isomorphism.

2. **Axiomatize more fundamentally**: Replace `FiniteCompletionResidueFields` with
   `FiniteResidueFields R` (each R ⧸ v.asIdeal is finite). This is more natural for
   function fields but still requires the isomorphism to get compactness.

3. **Accept current axiom**: Keep `FiniteCompletionResidueFields` as the single axiom,
   understanding that the discharge path requires proving the residue field isomorphism.

**Discharge Path for Function Fields k(C) over finite k**:
1. ✅ `IsDiscreteValuationRing`: PROVED for ALL Dedekind domains (Cycle 105)
2. ✅ `RankOne`: PROVED for ALL Dedekind domains (Cycle 106)
3. ✅ `CompleteSpace`: Automatic from completion construction
4. ⏳ `FiniteCompletionResidueFields`: Need to show residue field is finite
   - **Blocker**: Residue field isomorphism not in Mathlib
   - Mathematical path: Residue field of completion ≃ R/v.asIdeal (needs proof)
   - For function fields over finite k: R/v.asIdeal is finite extension of k, hence finite

**Progress**: TWO of THREE compactness requirements are now proved as theorems!
Only finite residue fields remains as an axiom.
-/

end RiemannRochV2.AllIntegersCompactProof

end
