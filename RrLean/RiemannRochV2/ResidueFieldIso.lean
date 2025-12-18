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

## Current Status

The isomorphism is complete modulo one axiom: `toResidueField_surjective`.

## Strategies to Discharge `toResidueField_surjective`

### Option 1: Bridge Path (RECOMMENDED - potentially cleanest)

Mathlib has `AdicCompletion.evalOneₐ_surjective` (in `RingTheory/AdicCompletion/Algebra.lean`):
```
lemma evalOneₐ_surjective : Function.Surjective (evalOneₐ I)
```
This says `AdicCompletion I R → R/I` is surjective.

The challenge: `AdicCompletion I R` (I-adic completion) differs from `v.adicCompletion K`
(valuation completion). For a DVR, these are isomorphic, but this isn't in Mathlib.

To use this:
1. Prove `AdicCompletion v.asIdeal (Localization.AtPrime v.asIdeal) ≃ v.adicCompletionIntegers K`
2. Transfer surjectivity via the isomorphism

### Option 2: Direct Density Argument (current approach)

Use the helper lemmas in this file:
- `denseRange_algebraMap_adicCompletion`: K is dense in K_v
- `mem_maximalIdeal_iff_val_lt_one`: maximal ideal = {x : v(x) < 1}
- `residue_eq_of_sub_mem_maximalIdeal`: close elements have same residue
- `exists_mul_eq_one_mod`: inverse exists in R/v.asIdeal

The 9-step proof outline is documented in the `toResidueField_surjective` axiom docstring.

### Option 3: Use `IsFractionRing`

Mathlib has `IsFractionRing (R ⧸ I) I.ResidueField` for prime I.
When I is maximal, R/I is already a field, so R/I ≃ I.ResidueField.
This connects to `Ideal.ResidueField` which might bridge to `Valued.ResidueField`.
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

The surjectivity proof uses:
1. v.asIdeal is maximal (in a Dedekind domain, height-one primes are maximal)
2. K is dense in K_v (the v-adic completion)
3. For any x in O_v, find k ∈ K close to x (by density)
4. By ultrametric property, k has valuation ≤ 1, so k ∈ K ∩ O_v = R_v (localization at v)
5. Write k = a/s with a ∈ R, s ∈ R \ v.asIdeal
6. Since R/v.asIdeal is a field, find t ∈ R with st ≡ 1 mod v.asIdeal
7. Then residue(k) = residue(at), where at ∈ R
-/

/-- In a Dedekind domain, v.asIdeal is maximal. -/
lemma asIdeal_isMaximal (v : HeightOneSpectrum R) : v.asIdeal.IsMaximal :=
  v.isPrime.isMaximal v.ne_bot

/-- For s ∉ v.asIdeal, the image of s in the completion has valuation 1. -/
lemma algebraMap_val_eq_one_of_not_mem (v : HeightOneSpectrum R) (s : R) (hs : s ∉ v.asIdeal) :
    Valued.v (algebraMap R (v.adicCompletion K) s) = 1 := by
  rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
  exact v.intValuation_eq_one_iff.mpr hs

/-- For s ∉ v.asIdeal, s is a unit in the completion integer ring. -/
lemma algebraMap_isUnit_of_not_mem (v : HeightOneSpectrum R) (s : R) (hs : s ∉ v.asIdeal) :
    IsUnit (algebraMap R (v.adicCompletionIntegers K) s) := by
  have hval1 : Valued.v ((algebraMap R (v.adicCompletionIntegers K) s) : v.adicCompletion K) = 1 := by
    exact algebraMap_val_eq_one_of_not_mem v s hs
  have hint : Valuation.Integers Valued.v (v.adicCompletionIntegers K) :=
    Valuation.integer.integers Valued.v
  exact hint.isUnit_iff_valuation_eq_one.mpr hval1

/-- In a Dedekind domain quotient field, nonzero elements are units. -/
lemma quotient_unit_of_nonzero (v : HeightOneSpectrum R) (x : R ⧸ v.asIdeal) (hx : x ≠ 0) :
    IsUnit x := by
  haveI : v.asIdeal.IsMaximal := asIdeal_isMaximal v
  letI : Field (R ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  exact isUnit_iff_ne_zero.mpr hx

/-- For s ∉ v.asIdeal, there exists t ∈ R such that st ≡ 1 mod v.asIdeal. -/
lemma exists_mul_eq_one_mod (v : HeightOneSpectrum R) (s : R) (hs : s ∉ v.asIdeal) :
    ∃ t : R, Ideal.Quotient.mk v.asIdeal (s * t) = 1 := by
  have hne : Ideal.Quotient.mk v.asIdeal s ≠ 0 := by
    simp only [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hs
  obtain ⟨u, hu⟩ := quotient_unit_of_nonzero v _ hne
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective u.inv
  use t
  rw [map_mul, ← hu, ht]
  exact u.val_inv

/-- Two elements with difference in the maximal ideal have the same residue. -/
lemma residue_eq_of_sub_mem_maximalIdeal (v : HeightOneSpectrum R)
    (x y : v.adicCompletionIntegers K)
    (h : x - y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    IsLocalRing.residue (R := v.adicCompletionIntegers K) x =
    IsLocalRing.residue (R := v.adicCompletionIntegers K) y := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact h

/-- The maximal ideal consists of elements with valuation < 1. -/
lemma mem_maximalIdeal_iff_val_lt_one (v : HeightOneSpectrum R)
    (x : v.adicCompletionIntegers K) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔
    Valued.v (x : v.adicCompletion K) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hnu
    exact hnu
  · intro hlt
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    exact hlt

/-- Elements of K form a dense subset in the completion. -/
lemma denseRange_algebraMap_adicCompletion (v : HeightOneSpectrum R) :
    DenseRange (algebraMap K (v.adicCompletion K)) := by
  -- adicCompletion K = UniformSpace.Completion of K (with valuation topology)
  -- The coercion K → Completion K has dense range
  have h : DenseRange ((↑) : WithVal (v.valuation K) → UniformSpace.Completion (WithVal (v.valuation K))) :=
    UniformSpace.Completion.denseRange_coe
  -- adicCompletion K = (v.valuation K).Completion = UniformSpace.Completion (WithVal (v.valuation K))
  -- And algebraMap K (adicCompletion K) is essentially this coercion
  convert h

/-- The residue field map from R is surjective.

Mathematical proof outline:
1. For any y in the residue field, lift to x ∈ O_v^
2. By density of K in K_v, find k ∈ K close to x (i.e., v(x - k) < 1)
3. Then residue(k) = residue(x) = y in the completion's residue field
4. k ∈ K with v(k) ≤ 1 means k ∈ R_v (localization at v.asIdeal)
5. Write k = a/s with a ∈ R, s ∈ R \ v.asIdeal
6. In O_v^, s is a unit (v(s) = 1), so residue(k) = residue(a) · residue(s)⁻¹
7. Find t ∈ R with st ≡ 1 mod v.asIdeal (using exists_mul_eq_one_mod)
8. Then residue(s)⁻¹ = residue(t) in the completion residue field
9. So residue(k) = residue(a) · residue(t) = residue(at), and at ∈ R

The density argument (steps 1-4) requires navigating the Mathlib API for valued fields.
Key ingredients already available:
- `denseRange_algebraMap_adicCompletion`: K is dense in K_v
- `mem_maximalIdeal_iff_val_lt_one`: maximal ideal characterized by v < 1
- `residue_eq_of_sub_mem_maximalIdeal`: close elements have same residue
- `exists_mul_eq_one_mod`: multiplicative inverse exists in R/v.asIdeal

This axiom is expected to be dischargeable using the above ingredients.
-/
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
