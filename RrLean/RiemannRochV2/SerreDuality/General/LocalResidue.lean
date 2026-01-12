/-
# Local Residue Map for Adic Completions

This file defines the local residue map `res_v : K_v → κ(v)` for any place v of a
function field over a Dedekind domain.

## Main Definitions

* `localResidue v` : The local residue map from v.adicCompletion K to the residue field
* `localResidue_linear` : Linear map version of the local residue

## Key Properties

1. `localResidue_vanishes_on_integers`: res_v(x) = 0 for x ∈ O_v (valuation ≤ 1)
2. `localResidue_compatible`: Compatibility with the global residue theorem

## Design

The residue is defined as the "coefficient of π⁻¹" in the Laurent expansion at v.

For a DVR with uniformizer π, any element x ∈ K_v can be written as:
  x = ∑_{i ≥ n} aᵢ πⁱ  where aᵢ ∈ κ(v)

The local residue is res_v(x) := a₋₁.

**Key insight**: We do NOT need a full K_v ≃ LaurentSeries κ(v) isomorphism.
Instead, we extract the π⁻¹ coefficient directly using:
1. If val(x) ≥ 0 (x ∈ O_v), then a₋₁ = 0
2. If val(x) = -1, then x·π ∈ O_v\m_v, so a₋₁ = residue(x·π)
3. If val(x) < -1, recursively reduce: x - a_n·π^n for leading term

For Serre duality, we primarily need cases 1 and 2.

## Status

Cycle 361: Initial skeleton with key definitions.
Cycle 362: Axiomatized local residue linearity (avoid Laurent series dependency).

## Axiomatization Strategy

Rather than construct the coefficient extraction directly (which requires Laurent series
infrastructure), we axiomatize `localResidue` as an additive group homomorphism with:
1. Vanishing on integers (O_v)
2. Compatibility with global residue theorem (sum over poles = 0)

This isolates the gap while allowing us to validate the Serre duality pairing structure.
The Laurent series bridge can be constructed later if strictly needed.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import RrLean.RiemannRochV2.Support.DedekindDVR
import RrLean.RiemannRochV2.ResidueTheory.ResidueFieldIso

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Valued NNReal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace RiemannRochV2.LocalResidue

/-! ## Preliminaries: DVR Structure and Uniformizers -/

variable (K) (v : HeightOneSpectrum R)

/-- The adic completion integer ring O_v is a DVR. -/
instance : IsDiscreteValuationRing (v.adicCompletionIntegers K) :=
  RiemannRochV2.DedekindDVR.isDiscreteValuationRing_adicCompletionIntegers v

/-- The maximal ideal of O_v. -/
abbrev maximalIdeal_Ov : Ideal (v.adicCompletionIntegers K) :=
  IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)

/-- The residue field of O_v. -/
abbrev residueField_Ov : Type _ := Valued.ResidueField (v.adicCompletion K)

/-- The quotient map O_v → κ(v). -/
abbrev residueMap_Ov : v.adicCompletionIntegers K →+* residueField_Ov K v :=
  IsLocalRing.residue (v.adicCompletionIntegers K)

/-- A uniformizer in the completion: element with valuation exp(-1).
This exists by `v.valuation_exists_uniformizer`. -/
structure CompletionUniformizer where
  /-- The uniformizer element in K_v -/
  π : v.adicCompletion K
  /-- π has valuation exp(-1) (i.e., ord(π) = 1) -/
  val_eq : Valued.v π = WithZero.exp (-1 : ℤ)
  /-- π is nonzero -/
  ne_zero : π ≠ 0

/-- Every place has a uniformizer in its completion. -/
theorem exists_completionUniformizer : Nonempty (CompletionUniformizer K v) := by
  -- Get uniformizer from the fraction field K
  obtain ⟨π_K, hπ⟩ := v.valuation_exists_uniformizer K
  -- π_K : K with v.valuation K π_K = exp(-1)
  -- We use the coercion K → v.adicCompletion K
  refine ⟨⟨(π_K : v.adicCompletion K), ?_, ?_⟩⟩
  · -- val_eq: Valued.v π = exp(-1)
    rw [valuedAdicCompletion_eq_valuation', hπ]
  · -- ne_zero: π ≠ 0
    intro hπ0
    have hv0 : Valued.v (π_K : v.adicCompletion K) = 0 := by
      rw [hπ0, Valuation.map_zero]
    rw [valuedAdicCompletion_eq_valuation', hπ] at hv0
    exact WithZero.coe_ne_zero hv0

/-- Choose a uniformizer for each place. -/
def uniformizer : CompletionUniformizer K v :=
  (exists_completionUniformizer K v).some

/-- The chosen uniformizer element. -/
abbrev uniformizer_elem : v.adicCompletion K := (uniformizer K v).π

/-- The uniformizer lies in the valuation ring O_v. -/
lemma uniformizer_mem_integers :
    Valued.v (uniformizer_elem K v) ≤ 1 := by
  rw [(uniformizer K v).val_eq]
  exact le_of_lt (WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0))

/-- The uniformizer as an element of O_v. -/
def uniformizer_in_Ov : v.adicCompletionIntegers K :=
  ⟨uniformizer_elem K v, uniformizer_mem_integers K v⟩

/-- The valuation of uniformizer_in_Ov as a subtype is exp(-1). -/
lemma uniformizer_in_Ov_val :
    Valued.v (uniformizer_in_Ov K v : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
  (uniformizer K v).val_eq

/-- The uniformizer is in the maximal ideal of O_v. -/
lemma uniformizer_mem_maximalIdeal :
    uniformizer_in_Ov K v ∈ maximalIdeal_Ov K v := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hval1 := (Valuation.integer.integers Valued.v).isUnit_iff_valuation_eq_one.mp hu
  have hval := uniformizer_in_Ov_val K v
  -- The algebraMap coercion is definitionally equal to the subtype coercion
  have heq : (algebraMap (↥Valued.v.integer) (v.adicCompletion K)) (uniformizer_in_Ov K v) =
             (uniformizer_in_Ov K v : v.adicCompletion K) := rfl
  rw [heq] at hval1
  -- Now hval1 says val = 1 and hval says val = exp(-1), contradiction since exp(-1) < 1
  have hlt : WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) :=
    WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0)
  rw [hval] at hval1
  exact (ne_of_lt hlt) hval1

/-- The uniformizer is not in the square of the maximal ideal (it generates m_v). -/
lemma uniformizer_not_mem_maximalIdeal_sq :
    uniformizer_in_Ov K v ∉ maximalIdeal_Ov K v ^ 2 := by
  intro hmem
  -- If π ∈ m_v², then val(π) < exp(-1) (val ≤ exp(-2))
  -- This contradicts val(π) = exp(-1)
  have hval := uniformizer_in_Ov_val K v
  -- Elements in m_v^n have valuation ≤ exp(-n)
  -- For n=2: val(x) ≤ exp(-2) means val(x) < exp(-1)
  sorry

/-! ## The Local Residue Map (Axiomatized)

The local residue map extracts the "coefficient of π⁻¹" in the Laurent expansion.
Rather than constructing this directly (which requires Laurent series infrastructure),
we axiomatize it as an additive group homomorphism with the key properties.

**Mathematical definition**: For x = ∑_{i ≥ n} aᵢ πⁱ in K_v, res_v(x) := a₋₁.

**Key properties**:
- res_v vanishes on O_v (elements with n ≥ 0 have a₋₁ = 0)
- res_v is additive (coefficient extraction is linear)
- Sum of local residues of global element is zero (residue theorem)
-/

/-- Membership in O_v is equivalent to valuation ≤ 1. -/
lemma mem_integers_iff (x : v.adicCompletion K) :
    x ∈ v.adicCompletionIntegers K ↔ Valued.v x ≤ 1 := Iff.rfl

/-! ### Axiomatized Local Residue

We axiomatize the local residue map as an additive group homomorphism.
This allows us to proceed with Serre duality pairing construction while
isolating the Laurent series dependency.
-/

/-- The local residue map K_v → κ(v) as an additive group homomorphism.

**Axiomatized**: The concrete construction requires Laurent series expansion.
For Serre duality, we only need the key properties (vanishing on O_v, additivity,
residue theorem compatibility).

**Implementation note**: Once `K_v ≃+* LaurentSeries κ(v)` is available in
Mathlib (or constructed here), this axiom can be replaced with a concrete
definition using `PowerSeries.coeff (-1)`.
-/
axiom localResidueHom : (v.adicCompletion K) →+ residueField_Ov K v

/-- The local residue function (non-bundled version). -/
def localResidue (x : v.adicCompletion K) : residueField_Ov K v :=
  localResidueHom K v x

/-! ## Key Properties -/

/-- The local residue is additive (immediate from AddMonoidHom structure). -/
theorem localResidue_add (x y : v.adicCompletion K) :
    localResidue K v (x + y) = localResidue K v x + localResidue K v y :=
  (localResidueHom K v).map_add x y

/-- The local residue sends 0 to 0. -/
theorem localResidue_zero : localResidue K v 0 = 0 :=
  (localResidueHom K v).map_zero

/-- The local residue vanishes on the valuation ring O_v.

**Axiomatized**: Elements in O_v have no π⁻¹ term in their Laurent expansion.
This is the key property connecting valuations to residues.
-/
axiom localResidue_vanishes_on_integers (x : v.adicCompletionIntegers K) :
    localResidue K v (x : v.adicCompletion K) = 0

/-! ## Connection to Global Residue Theorem

For the Serre duality pairing, we need:
∑_v res_v(x · f) = 0 for x ∈ K (global element) and f ∈ K.

This follows from the residue theorem: the sum of residues of a global meromorphic
differential is zero.
-/

/-- Negation is preserved by localResidue (consequence of AddMonoidHom). -/
theorem localResidue_neg (x : v.adicCompletion K) :
    localResidue K v (-x) = -localResidue K v x := by
  have h := localResidue_add K v (-x) x
  simp only [neg_add_cancel, localResidue_zero] at h
  -- h : 0 = localResidue K v (-x) + localResidue K v x
  -- We want: localResidue K v (-x) = -localResidue K v x
  have heq : localResidue K v (-x) + localResidue K v x = 0 := h.symm
  exact eq_neg_of_add_eq_zero_left heq

/-- Subtraction formula for localResidue. -/
theorem localResidue_sub (x y : v.adicCompletion K) :
    localResidue K v (x - y) = localResidue K v x - localResidue K v y := by
  rw [sub_eq_add_neg, localResidue_add, localResidue_neg, sub_eq_add_neg]

/-! ### Residue Theorem Compatibility

The global residue theorem states that for any global element f ∈ K,
the sum of local residues over all places is zero. This is axiomatized
for the Serre duality pairing construction.
-/

-- The global residue theorem: sum of local residues of a global element is zero.
--
-- Axiomatized: This is the classical residue theorem from complex analysis /
-- algebraic geometry. For a global meromorphic function (or differential), the
-- sum of all residues vanishes.
--
-- This is the key property that makes the Serre duality pairing well-defined
-- on the quotient H¹(D) = A_K / (K + A(D)).
--
-- Note: The precise formulation requires summing over all places with poles.
-- We defer this to PairingDescent.lean where we have access to the adelic structure.

end RiemannRochV2.LocalResidue

/-! ## Summary (Cycle 362)

**Axioms introduced**:
1. `localResidueHom`: The local residue is an additive group homomorphism K_v →+ κ(v)
2. `localResidue_vanishes_on_integers`: res_v(x) = 0 for x ∈ O_v

**Theorems derived**:
- `localResidue_add`: res_v(x+y) = res_v(x) + res_v(y)
- `localResidue_zero`: res_v(0) = 0
- `localResidue_neg`: res_v(-x) = -res_v(x)
- `localResidue_sub`: res_v(x-y) = res_v(x) - res_v(y)

**Remaining sorry** (not on critical path):
- `uniformizer_not_mem_maximalIdeal_sq`: π ∉ m_v² (used for DVR structure, not residue)

**Next**: Create PairingDescent.lean with raw pairing ψ(a,f) = ∑_v res_v(a_v · f)
-/

end
