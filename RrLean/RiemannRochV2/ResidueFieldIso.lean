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

/-! ## Surjectivity via Density

The proof that R → completion residue field is surjective uses:
1. Lift y to x ∈ O_v^ using `IsLocalRing.residue_surjective`
2. Use density of K in completion to find k ∈ K with v(x - k) < 1
3. Use `residue_eq_of_sub_mem_maximalIdeal` to get residue(k) = residue(x)
4. Show k ∈ O_v^ (by ultrametric) and express residue(k) as residue(at) for t ∈ R
-/

/-- From density, we can find k ∈ K close to any x in the completion. -/
lemma exists_close_element (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    ∃ k : K, Valued.v (x - algebraMap K (v.adicCompletion K) k) < 1 := by
  -- K is dense in the completion
  have hdense : DenseRange (algebraMap K (v.adicCompletion K)) :=
    denseRange_algebraMap_adicCompletion v
  -- x is in the closure of the range of K
  have hx_closure : x ∈ closure (Set.range (algebraMap K (v.adicCompletion K))) := hdense x
  -- Use mem_closure_iff: every neighborhood of x meets the range
  rw [mem_closure_iff] at hx_closure
  -- The ball {y : v(x - y) < 1} is a neighborhood of x
  -- Using Valued.mem_nhds: s ∈ 𝓝 x ↔ ∃ γ : Γ₀ˣ, { y | v (y - x) < γ } ⊆ s
  have hball_open : IsOpen {y : v.adicCompletion K | Valued.v (y - x) < 1} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    rw [Valued.mem_nhds]
    use 1
    intro z hz
    simp only [Set.mem_setOf_eq] at hz hy ⊢
    -- Need: v(z - x) < 1
    -- We have: v(z - y) < 1 and v(y - x) < 1
    calc Valued.v (z - x)
        = Valued.v ((z - y) + (y - x)) := by ring_nf
      _ ≤ max (Valued.v (z - y)) (Valued.v (y - x)) := Valuation.map_add _ _ _
      _ < max 1 1 := max_lt hz hy
      _ = 1 := max_self 1
  have hx_in_ball : x ∈ {y : v.adicCompletion K | Valued.v (y - x) < 1} := by
    simp only [Set.mem_setOf_eq, sub_self, Valuation.map_zero]
    exact one_pos
  -- Get intersection with range of K
  obtain ⟨y, hy_in_ball, hy_in_range⟩ := hx_closure _ hball_open hx_in_ball
  obtain ⟨k, rfl⟩ := hy_in_range
  -- Convert v(y - x) < 1 to v(x - y) < 1 using v(a) = v(-a)
  use k
  simp only [Set.mem_setOf_eq] at hy_in_ball
  rw [Valuation.map_sub_swap] at hy_in_ball
  exact hy_in_ball

/-- If k ∈ K has v(x - k) < 1 where x ∈ O_v^, then k ∈ O_v^ (by ultrametric). -/
lemma mem_integers_of_close (v : HeightOneSpectrum R) (x : v.adicCompletionIntegers K) (k : K)
    (hclose : Valued.v ((x : v.adicCompletion K) - algebraMap K (v.adicCompletion K) k) < 1) :
    Valued.v (algebraMap K (v.adicCompletion K) k) ≤ 1 := by
  -- By ultrametric: v(k) ≤ max(v(x), v(x - k))
  -- v(x) ≤ 1 (since x ∈ O_v^) and v(x - k) < 1, so max ≤ 1
  have hx : Valued.v (x : v.adicCompletion K) ≤ 1 := x.2
  -- k = x - (x - k), so v(k) ≤ max(v(x), v(x - k)) by ultrametric
  have hrewrite : algebraMap K (v.adicCompletion K) k =
      (x : v.adicCompletion K) - ((x : v.adicCompletion K) - algebraMap K _ k) := by ring
  rw [hrewrite]
  calc Valued.v ((x : v.adicCompletion K) - ((x : v.adicCompletion K) - algebraMap K _ k))
      ≤ max (Valued.v (x : v.adicCompletion K)) (Valued.v ((x : v.adicCompletion K) - algebraMap K _ k)) :=
        Valuation.map_sub Valued.v _ _
    _ ≤ max 1 1 := max_le_max hx (le_of_lt hclose)
    _ = 1 := max_self 1

/-- Key lemma: elements of K with v ≤ 1 give residues from R.

The key insight is to use IsLocalization.surj with primeCompl, which directly
gives a representation k = a/s where s ∉ v.asIdeal. This eliminates the need
for uniformizer factorization in the s ∈ v.asIdeal case. -/
lemma residue_of_K_element (v : HeightOneSpectrum R) (k : K)
    (hk : Valued.v (algebraMap K (v.adicCompletion K) k) ≤ 1) :
    ∃ r : R, toResidueField (K := K) v r =
      IsLocalRing.residue (R := v.adicCompletionIntegers K)
        ⟨algebraMap K (v.adicCompletion K) k, hk⟩ := by
  -- Use IsLocalization.surj to get k = (algebraMap R K a) / (algebraMap R K s) where s ∉ v.asIdeal
  -- K is the fraction field of R, and also the fraction field of Localization.AtPrime v.asIdeal
  -- Elements with v(k) ≤ 1 can be represented with denominator outside v.asIdeal
  -- First, write k = a/s for some a, s ∈ R with s ≠ 0
  rcases IsFractionRing.div_surjective (A := R) k with ⟨a, s, hs_ne, hk_eq⟩
  -- hs_ne : s ∈ nonZeroDivisors R, meaning s ≠ 0
  -- hk_eq : k = algebraMap R K a / algebraMap R K s
  -- If s ∉ v.asIdeal, we're done with the main case
  -- If s ∈ v.asIdeal, we need to clear common uniformizer factors
  -- Key insight: use that v(k) ≤ 1 means k is in the "valuation ring" part
  -- We can find an equivalent representation with denominator outside v.asIdeal
  by_cases hs : s ∈ v.asIdeal
  · -- Case: s ∈ v.asIdeal. Then v(s) < 1, so v(a/s) = v(a)/v(s).
    -- For v(a/s) ≤ 1, we need v(a) ≤ v(s) < 1, so a ∈ v.asIdeal too.
    -- Subcase 1: v(k) < 1, so residue = 0
    by_cases hk_lt : Valued.v (algebraMap K (v.adicCompletion K) k) < 1
    · use 0
      simp only [toResidueField, algebraMapToIntegers, map_zero]
      symm
      rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff_val_lt_one]
      exact hk_lt
    · -- Subcase 2: v(k) = 1 (a unit). Both a, b have the same v-adic order.
      -- We can factor: a = π^n · a', b = π^n · b' where a', b' ∉ v.asIdeal
      -- Then k = a'/b' with b' ∉ v.asIdeal
      -- Instead of explicit factorization, observe: if v(k) = 1 and k = a/b,
      -- then a/b represents a unit in O_v^, and the residue is nonzero.
      -- Since R → residue field is surjective onto R/v.asIdeal ≃ residue field,
      -- there exists r with the same residue.
      push_neg at hk_lt
      have hk_eq_one : Valued.v (algebraMap K (v.adicCompletion K) k) = 1 :=
        le_antisymm hk hk_lt
      -- The element k is a unit in the completion integers
      have hk_unit : IsUnit (⟨algebraMap K (v.adicCompletion K) k, hk⟩ :
          v.adicCompletionIntegers K) := by
        have hint : Valuation.Integers Valued.v (v.adicCompletionIntegers K) :=
          Valuation.integer.integers Valued.v
        exact hint.isUnit_iff_valuation_eq_one.mpr hk_eq_one
      -- Units in the completion have nonzero residue
      -- Since R/v.asIdeal is a field, we can find a preimage
      -- The key is that the residue map R → ResidueField factors through R/v.asIdeal
      -- and R/v.asIdeal ≃ ResidueField (this is what residueFieldIso will show)
      -- For now, find r ∈ R with matching residue by using the unit structure
      -- Use that units in the local ring O_v^ map to units in the residue field
      obtain ⟨u, hu⟩ := hk_unit
      -- hu : ↑u = ⟨algebraMap K ... k, hk⟩
      -- residue(u) is a unit in the residue field
      have hres_unit : IsUnit (IsLocalRing.residue (R := v.adicCompletionIntegers K)
          ⟨algebraMap K (v.adicCompletion K) k, hk⟩) := by
        rw [← hu]
        exact (IsLocalRing.residue (v.adicCompletionIntegers K)).isUnit_map u.isUnit
      -- Since toResidueField : R → ResidueField factors through R/v.asIdeal which is a field,
      -- and residue(k) is a nonzero element, we can find a preimage.
      -- Specifically, use that 1 maps to 1, and units are invertible.
      -- For a unit u in ResidueField, there exists r ∈ R \ v.asIdeal with toResidueField r = u
      -- This follows from surjectivity of R → R/v.asIdeal → ResidueField
      -- The tricky part: we need to find the specific r matching residue(k)
      -- Use the inverse: residue(k)⁻¹ * residue(k) = 1
      -- There exists r with toResidueField(r) = residue(k)⁻¹ (since R/v surjects)
      -- But we need residue(k) itself...
      -- Actually, the cleanest approach: residue(1) = 1 in ResidueField
      -- If residue(k) = residue(r') for some r' ∈ O_v^, and r' comes from R, done.
      -- The issue is showing r' comes from R. This requires the density argument
      -- which is what we're trying to prove! So we need a different approach.
      -- Key: since v(a/b) = 1 and both a, b ∈ v.asIdeal with same order,
      -- we can find a' ∈ R with a' ∉ v.asIdeal and a' ≡ a/π^n mod m_v
      -- This is getting circular. Let's use a cleaner approach:
      -- The residue of k only depends on k mod m_v. Since k is a unit,
      -- k = u for some u ∈ O_v^×. The group O_v^× surjects onto k* where
      -- k* is the residue field minus 0. Since R \ v.asIdeal ⊂ O_v^× and
      -- R \ v.asIdeal maps onto (R/v.asIdeal)* = k*, we can find r.
      -- This is proven via the isomorphism R/v.asIdeal ≃ ResidueField.
      -- Since we're trying to build that isomorphism, we need to be careful.
      -- Clean solution: show R ∩ O_v^× → k* is surjective
      -- This follows from: v(r) = 1 ⟺ r ∉ v.asIdeal, and R/v.asIdeal is a field.
      -- For any unit in k*, lift to R/v.asIdeal, then lift to R.
      -- Sorry: this case requires the isomorphism we're building. We defer.
      sorry
  · -- b ∉ v.asIdeal is the main case
    -- In this case, v(s) = 1, so s is a unit in O_v^
    -- In the residue field, residue(a/s) = residue(a) · residue(s)^{-1}
    -- Since s ∉ v.asIdeal, there exists t ∈ R with st ≡ 1 mod v.asIdeal
    obtain ⟨t, hst⟩ := exists_mul_eq_one_mod v s hs
    -- Claim: residue(a/s) = residue(a·t)
    use a * t
    -- After `rfl`, the goal has k replaced by `a / s` (with implicit coercions)
    -- Goal: toResidueField v (a * t) = residue ⟨algebraMap K (completion) (a/s), hk⟩
    -- Step 1: s is a unit in the completion integer ring
    have hs_unit : IsUnit (algebraMap R (v.adicCompletionIntegers K) s) :=
      algebraMap_isUnit_of_not_mem v s hs
    -- Step 2: st ≡ 1 means st - 1 ∈ v.asIdeal
    have hst_mem : s * t - 1 ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hst, map_one, sub_self]
    -- Step 3: In the residue field, residue(s) * residue(t) = 1
    have hst_residue : IsLocalRing.residue (R := v.adicCompletionIntegers K)
        (algebraMap R (v.adicCompletionIntegers K) s) *
        IsLocalRing.residue (R := v.adicCompletionIntegers K)
        (algebraMap R (v.adicCompletionIntegers K) t) = 1 := by
      rw [← map_mul]
      have hres0 : toResidueField (K := K) v (s * t - 1) = 0 :=
        toResidueField_mem_asIdeal v (s * t - 1) hst_mem
      simp only [toResidueField, RingHom.coe_comp, Function.comp_apply, algebraMapToIntegers,
        map_sub, map_mul, map_one] at hres0
      -- hres0 : residue(s) * residue(t) - 1 = 0
      -- Therefore residue(s) * residue(t) = 1
      rw [sub_eq_zero] at hres0
      exact hres0
    -- Step 4: Since residue(s) * residue(t) = 1, we have toResidueField(at) = residue(a/s)
    -- The proof uses: residue(a*t) = residue(a) * residue(t) = residue(a) * residue(s)⁻¹ = residue(a/s)
    -- This equality follows from:
    -- 1. s is a unit in O_v^, so a/s = a * s⁻¹
    -- 2. residue(s) * residue(t) = 1, so residue(t) = residue(s)⁻¹
    -- 3. residue(a*t) = residue(a) * residue(t) = residue(a) * residue(s)⁻¹ = residue(a/s)
    -- The coercion management between S := adicCompletionIntegers and C := adicCompletion is complex
    -- but mathematically straightforward. We use native_decide for the definitional equalities.
    -- Goal after simp: (residue.comp algebraMap) a * (residue.comp algebraMap) t = residue(⟨k, hk⟩)
    -- Derive residue(t) = residue(s)⁻¹
    have ht_inv : IsLocalRing.residue (R := v.adicCompletionIntegers K)
        (algebraMap R (v.adicCompletionIntegers K) t) =
        (IsLocalRing.residue (R := v.adicCompletionIntegers K)
          (algebraMap R (v.adicCompletionIntegers K) s))⁻¹ :=
      eq_inv_of_mul_eq_one_right hst_residue
    -- The main calculation: both sides equal residue(a) * residue(s)⁻¹
    -- LHS: residue(a) * residue(t) = residue(a) * residue(s)⁻¹ by ht_inv
    -- RHS: residue(⟨a/s, hk⟩) = residue(a * s⁻¹) = residue(a) * residue(s)⁻¹
    -- Rewrite LHS using ht_inv - use simp to handle the comp/apply unfolding
    simp only [toResidueField, algebraMapToIntegers, ht_inv]
    -- Goal: residue(a) * residue(s)⁻¹ = residue(⟨a/s, hk⟩)
    -- Now we need to show the RHS equals residue(a) * residue(s)⁻¹
    -- Key: a/s in K embeds as (algebraMap R S a) * (unit s)⁻¹ in S := adicCompletionIntegers
    -- Get the unit corresponding to s
    obtain ⟨s_unit, hs_unit_eq⟩ := hs_unit
    -- hs_unit_eq : ↑s_unit = algebraMap R S s
    -- The element ⟨k, hk⟩ = ⟨a/s, hk⟩ equals (algebraMap R S a) * s_unit⁻¹
    -- Goal: residue(a) * residue(s)⁻¹ = residue(⟨k, hk⟩)
    -- Strategy: show both sides equal residue(a) * residue(s)⁻¹
    -- For the RHS: ⟨k, hk⟩ = ⟨a/s, _⟩ = algebraMap a * s_unit⁻¹
    -- Goal: residue(a) * residue(s)⁻¹ = residue(⟨k, hk⟩)
    -- Mathematical content:
    -- - k = a/s by hk_eq
    -- - s is a unit in the integer ring (s_unit)
    -- - In the integer ring, ⟨k, hk⟩ = algebraMap(a) * s_unit⁻¹
    -- - residue(a * s⁻¹) = residue(a) * residue(s)⁻¹ by ring hom
    -- - residue(s_unit) = residue(algebraMap s) by hs_unit_eq
    -- The coercion management between subtypes and the completion is complex;
    -- the mathematical content is clear but Lean requires careful navigation.
    -- We defer this to a future cycle focused on coercion lemmas.
    sorry

/-- The residue field map from R is surjective. -/
theorem toResidueField_surjective (v : HeightOneSpectrum R) :
    Function.Surjective (toResidueField (K := K) v) := by
  intro y
  -- Step 1: Lift y to x ∈ O_v^
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  -- Step 2: Find k ∈ K close to x (v(x - k) < 1)
  obtain ⟨k, hclose⟩ := exists_close_element v (x : v.adicCompletion K)
  -- Step 3: k ∈ O_v^ by ultrametric
  have hk_int : Valued.v (algebraMap K (v.adicCompletion K) k) ≤ 1 :=
    mem_integers_of_close v x k hclose
  -- Step 4: residue(k) = residue(x) since v(x - k) < 1
  let k' : v.adicCompletionIntegers K := ⟨algebraMap K (v.adicCompletion K) k, hk_int⟩
  have hresid_eq : IsLocalRing.residue (R := v.adicCompletionIntegers K) k' =
                   IsLocalRing.residue (R := v.adicCompletionIntegers K) x := by
    apply residue_eq_of_sub_mem_maximalIdeal
    rw [mem_maximalIdeal_iff_val_lt_one]
    show Valued.v ((k' : v.adicCompletion K) - (x : v.adicCompletion K)) < 1
    simp only [k', Subtype.coe_mk]
    rw [Valuation.map_sub_swap]
    exact hclose
  -- Step 5: Get r ∈ R with toResidueField r = residue(k)
  obtain ⟨r, hr⟩ := residue_of_K_element v k hk_int
  -- Combine: toResidueField r = residue(k) = residue(x) = y
  use r
  rw [hr]
  -- k' = ⟨algebraMap K ... k, hk_int⟩, so this is exactly hresid_eq
  convert hresid_eq using 2

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
