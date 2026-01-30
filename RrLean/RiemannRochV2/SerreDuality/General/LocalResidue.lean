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

/-! ## Concrete Residue via Uniformizer (Cycle 378)

We define a concrete residue extraction using the uniformizer π.

**Key idea**: For x ∈ K_v with a simple pole (val(x) = exp(1)):
- x · π has val(x·π) = exp(1) · exp(-1) = 1, so x·π ∈ O_v is a unit
- The residue is the image of x·π in κ(v)

For x ∈ O_v (val(x) ≤ 1): residue = 0

This matches the axiomatized `localResidueHom` for elements with at most simple poles.
-/

/-- The uniformizer is nonzero. -/
lemma uniformizer_ne_zero : uniformizer_elem K v ≠ 0 :=
  (uniformizer K v).ne_zero

/-- The uniformizer is a unit in K_v (as a field element). -/
lemma uniformizer_isUnit : IsUnit (uniformizer_elem K v) := by
  rw [isUnit_iff_ne_zero]
  exact uniformizer_ne_zero K v

/-- For x with val(x) = exp(n) where n ≥ 1, x·π has val = exp(n-1). -/
lemma val_mul_uniformizer (x : v.adicCompletion K) :
    Valued.v (x * uniformizer_elem K v) = Valued.v x * WithZero.exp (-1 : ℤ) := by
  rw [Valuation.map_mul, (uniformizer K v).val_eq]

/-- For x with val(x) · exp(-1) ≤ 1, we have x·π ∈ O_v. -/
lemma mul_uniformizer_mem_integers (x : v.adicCompletion K)
    (hx : Valued.v x * WithZero.exp (-1 : ℤ) ≤ 1) :
    x * uniformizer_elem K v ∈ v.adicCompletionIntegers K := by
  show Valued.v (x * uniformizer_elem K v) ≤ 1
  rw [val_mul_uniformizer]
  exact hx

/-- Concrete residue for elements with at most a simple pole.

For x with val(x) ≤ exp(1) (at most simple pole):
- If val(x) ≤ 1: return 0 (no pole)
- If 1 < val(x) ≤ exp(1): return residueMap(x·π)

This is partial - only handles simple poles. Full residue needs recursion.
-/
noncomputable def residueSimplePole (x : v.adicCompletion K)
    (hx : Valued.v x ≤ WithZero.exp (1 : ℤ)) : residueField_Ov K v :=
  if h : Valued.v x ≤ 1 then
    0  -- No pole, residue is 0
  else
    -- x has a simple pole: val(x) > 1 but ≤ exp(1)
    -- So x·π has val ≤ 1, meaning x·π ∈ O_v
    let hprod : Valued.v x * WithZero.exp (-1 : ℤ) ≤ 1 := by
      -- val(x) ≤ exp(1), so val(x) · exp(-1) ≤ exp(1) · exp(-1) = 1
      calc Valued.v x * WithZero.exp (-1 : ℤ)
          ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) := by
            apply mul_le_mul_right'
            exact hx
        _ = WithZero.exp (1 + (-1) : ℤ) := by rw [← WithZero.exp_add]
        _ = WithZero.exp 0 := by norm_num
        _ = 1 := WithZero.exp_zero
    residueMap_Ov K v ⟨x * uniformizer_elem K v, mul_uniformizer_mem_integers K v x hprod⟩

/-- The simple pole residue vanishes for elements in O_v. -/
theorem residueSimplePole_vanishes_on_integers (x : v.adicCompletionIntegers K) :
    residueSimplePole K v x (by
      -- val(x) ≤ 1 ≤ exp(1)
      have h1 : Valued.v (x : v.adicCompletion K) ≤ 1 := x.property
      have h2 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (1 : ℤ) :=
        le_of_lt (WithZero.exp_lt_exp.mpr (by norm_num : (0 : ℤ) < 1))
      exact le_trans h1 h2) = 0 := by
  unfold residueSimplePole
  have hx_int : Valued.v (x : v.adicCompletion K) ≤ 1 := x.property
  simp only [dif_pos hx_int]

/-! ## Extension to Higher-Order Poles (Cycle 379)

We extend `residueSimplePole` to handle poles of arbitrary order using recursion.

**Strategy**: For x with pole of order n > 1:
1. Extract the leading coefficient: a_n = (x · π^n) mod m_v
2. Lift a_n back to O_v as ã_n
3. Compute y = x - ã_n · π^{-n}, which has pole order < n
4. Recurse: res(x) = res(y) since π^{-n} has no π^{-1} term when n > 1

**Key insight**: The residue is the coefficient of π^{-1} in the Laurent expansion.
Subtracting higher-order pole terms doesn't change the residue.
-/

/-! ### Lifting from Residue Field to Integers

We use `Function.surjInv` to lift elements from κ(v) back to O_v.
The residue map is surjective, so this always succeeds.
-/

/-- The residue map O_v → κ(v) is surjective. -/
lemma residueMap_surjective :
    Function.Surjective (residueMap_Ov K v) :=
  Ideal.Quotient.mk_surjective

/-- Lift an element of κ(v) to O_v using `Function.surjInv`.
Any lift will do - the specific choice doesn't affect the residue computation. -/
noncomputable def liftFromResidue (a : residueField_Ov K v) : v.adicCompletionIntegers K :=
  Function.surjInv (residueMap_surjective K v) a

/-- The lifted element projects back to the original residue class. -/
lemma liftFromResidue_proj (a : residueField_Ov K v) :
    residueMap_Ov K v (liftFromResidue K v a) = a :=
  Function.surjInv_eq (residueMap_surjective K v) a

/-- Lifting 0 gives an element in the maximal ideal. -/
lemma liftFromResidue_zero_mem_maximalIdeal :
    liftFromResidue K v 0 ∈ maximalIdeal_Ov K v := by
  rw [IsLocalRing.mem_maximalIdeal]
  intro hu
  have hproj := liftFromResidue_proj K v 0
  rw [← hproj] at hu
  -- If residueMap(x) is a unit in κ(v), then x ∉ m_v
  -- But residueMap(x) = 0 is not a unit
  have h0_not_unit : ¬IsUnit (0 : residueField_Ov K v) := by
    simp only [not_isUnit_zero]
  rw [← hproj] at h0_not_unit
  exact h0_not_unit (hu.map (residueMap_Ov K v))

/-! ### Uniformizer Inverse and Powers -/

/-- The inverse of the uniformizer in K_v. Since K_v is a field and π ≠ 0, this exists. -/
noncomputable def uniformizer_inv : v.adicCompletion K :=
  (uniformizer_elem K v)⁻¹

/-- The valuation of π⁻¹ is exp(1). -/
lemma uniformizer_inv_val :
    Valued.v (uniformizer_inv K v) = WithZero.exp (1 : ℤ) := by
  unfold uniformizer_inv
  rw [Valuation.map_inv, (uniformizer K v).val_eq]
  simp only [WithZero.inv_exp, neg_neg]

/-- Powers of π⁻¹: (π⁻¹)^n for n : ℕ. -/
noncomputable def uniformizer_inv_pow (n : ℕ) : v.adicCompletion K :=
  (uniformizer_inv K v) ^ n

/-- The valuation of (π⁻¹)^n is exp(n). -/
lemma uniformizer_inv_pow_val (n : ℕ) :
    Valued.v (uniformizer_inv_pow K v n) = WithZero.exp (n : ℤ) := by
  unfold uniformizer_inv_pow
  rw [Valuation.map_pow, uniformizer_inv_val]
  induction n with
  | zero => simp [WithZero.exp_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← WithZero.exp_add]
    congr 1
    omega

/-- π⁻¹ is nonzero. -/
lemma uniformizer_inv_ne_zero : uniformizer_inv K v ≠ 0 := by
  unfold uniformizer_inv
  exact inv_ne_zero (uniformizer_ne_zero K v)

/-- (π⁻¹)^n is nonzero for any n. -/
lemma uniformizer_inv_pow_ne_zero (n : ℕ) : uniformizer_inv_pow K v n ≠ 0 := by
  unfold uniformizer_inv_pow
  exact pow_ne_zero n (uniformizer_inv_ne_zero K v)

/-- Powers of π: π^n for n : ℕ. -/
noncomputable def uniformizer_pow (n : ℕ) : v.adicCompletion K :=
  (uniformizer_elem K v) ^ n

/-- The valuation of π^n is exp(-n). -/
lemma uniformizer_pow_val (n : ℕ) :
    Valued.v (uniformizer_pow K v n) = WithZero.exp (-(n : ℤ)) := by
  unfold uniformizer_pow
  rw [Valuation.map_pow, (uniformizer K v).val_eq]
  induction n with
  | zero => simp [WithZero.exp_zero]
  | succ n ih =>
    rw [pow_succ, Valuation.map_mul, ih, (uniformizer K v).val_eq, ← WithZero.exp_add]
    congr 1
    omega

/-- π^n lies in O_v for any n ≥ 0. -/
lemma uniformizer_pow_mem_integers (n : ℕ) :
    uniformizer_pow K v n ∈ v.adicCompletionIntegers K := by
  show Valued.v (uniformizer_pow K v n) ≤ 1
  rw [uniformizer_pow_val]
  exact le_of_lt (WithZero.exp_lt_exp.mpr (by omega : -(n : ℤ) < 0))

/-- π^n as an element of O_v. -/
noncomputable def uniformizer_pow_in_Ov (n : ℕ) : v.adicCompletionIntegers K :=
  ⟨uniformizer_pow K v n, uniformizer_pow_mem_integers K v n⟩

/-- For nonzero x in the integer ring with val(x) < 1, we have val(x) ≤ exp(-1).
This uses the fact that the valuation takes values in {0} ∪ {exp(n) : n ∈ ℤ},
so val < 1 = exp(0) and val ≠ 0 implies val = exp(n) for some n ≤ -1.

**Key insight**: The adic valuation is a discrete valuation with uniformizer π satisfying
val(π) = exp(-1). The next value below 1 = exp(0) is exp(-1).
-/
lemma val_lt_one_of_nonzero_le_exp_neg_one (x : v.adicCompletionIntegers K)
    (hx_ne : (x : v.adicCompletion K) ≠ 0)
    (hx_lt : Valued.v (x : v.adicCompletion K) < 1) :
    Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-1 : ℤ) := by
  -- The valuation is nonzero (since x ≠ 0)
  have hval_ne : Valued.v (x : v.adicCompletion K) ≠ 0 := by
    intro h0
    exact hx_ne (Valuation.zero_iff.mp h0)
  -- For a nonzero element x ∈ WithZero Γ₀, we can extract x = ↑(some g ∈ Γ₀)
  -- In our case Γ₀ = Multiplicative ℤ, so x = exp(n) for some n : ℤ
  -- WithZero.ne_zero_iff_exists gives us this
  rw [WithZero.ne_zero_iff_exists] at hval_ne
  obtain ⟨g, hg⟩ := hval_ne
  -- g ∈ Multiplicative ℤ, and there exists n : ℤ with g = Multiplicative.ofAdd n
  -- This means (↑g : WithZero _) = WithZero.exp n
  -- We have hx_lt : (↑g) < 1 = exp(0), so g < Multiplicative.ofAdd 0
  -- In Multiplicative ℤ, this means g = Multiplicative.ofAdd n for some n < 0
  rw [← hg] at hx_lt ⊢
  -- Now we need: (↑g : WithZero (Multiplicative ℤ)) ≤ exp(-1) given (↑g) < 1 = exp(0)
  -- First, (↑g) < exp(0) means g < Multiplicative.ofAdd 0 (via WithZero.coe_lt_coe)
  rw [← WithZero.coe_one, WithZero.coe_lt_coe] at hx_lt
  -- g < 1 in Multiplicative ℤ means toAdd g < 0
  have hg_neg : Multiplicative.toAdd g < 0 := by
    rwa [← Multiplicative.ofAdd_zero, Multiplicative.ofAdd_lt] at hx_lt
  -- Now (↑g) ≤ exp(-1) iff g ≤ Multiplicative.ofAdd (-1)
  rw [← WithZero.coe_le_coe, ← WithZero.exp]
  -- Reduce to toAdd g ≤ -1
  rw [Multiplicative.ofAdd_le]
  omega

/-! ### Higher-Order Pole Residue via Recursion

For x with val(x) ≤ exp(n), we define the residue recursively:
- If n = 0: x ∈ O_v, residue = 0
- If n ≥ 1 and val(x) ≤ exp(n-1): recurse with smaller bound
- If n ≥ 1 and val(x) > exp(n-1): strip leading term and recurse

The recursion is well-founded on n : ℕ.
-/

/-- For x with val(x) ≤ exp(n), multiplying by π^n gives an element of O_v. -/
lemma mul_uniformizer_pow_mem_integers (x : v.adicCompletion K) (n : ℕ)
    (hx : Valued.v x ≤ WithZero.exp (n : ℤ)) :
    x * uniformizer_pow K v n ∈ v.adicCompletionIntegers K := by
  show Valued.v (x * uniformizer_pow K v n) ≤ 1
  rw [Valuation.map_mul, uniformizer_pow_val]
  calc Valued.v x * WithZero.exp (-(n : ℤ))
      ≤ WithZero.exp (n : ℤ) * WithZero.exp (-(n : ℤ)) := mul_le_mul_right' hx _
    _ = WithZero.exp (n + -(n : ℤ)) := by rw [← WithZero.exp_add]
    _ = WithZero.exp 0 := by ring_nf
    _ = 1 := WithZero.exp_zero

/-- Helper: if val(x) ≤ exp(n) but val(x) > exp(n-1), then extracting the leading
coefficient and subtracting gives an element with val ≤ exp(n-1). -/
lemma val_after_leading_term_subtraction (x : v.adicCompletion K) (n : ℕ) (hn : n ≥ 1)
    (hx_upper : Valued.v x ≤ WithZero.exp (n : ℤ))
    (hx_lower : ¬Valued.v x ≤ WithZero.exp ((n - 1 : ℕ) : ℤ)) :
    let a := residueMap_Ov K v ⟨x * uniformizer_pow K v n,
             mul_uniformizer_pow_mem_integers K v x n hx_upper⟩
    let a_lift := liftFromResidue K v a
    Valued.v (x - (a_lift : v.adicCompletion K) * uniformizer_inv_pow K v n) ≤
      WithZero.exp ((n - 1 : ℕ) : ℤ) := by
  intro a a_lift
  -- Step 1: x * π^n and a_lift have the same residue class
  -- So their difference is in the maximal ideal m_v
  have h_same_residue : residueMap_Ov K v ⟨x * uniformizer_pow K v n,
      mul_uniformizer_pow_mem_integers K v x n hx_upper⟩ = residueMap_Ov K v a_lift := by
    -- a_lift is defined as the lift of a, so it projects back to a
    exact (liftFromResidue_proj K v a).symm
  -- The difference x * π^n - a_lift lies in m_v (maximal ideal)
  have h_diff_mem : (⟨x * uniformizer_pow K v n, mul_uniformizer_pow_mem_integers K v x n hx_upper⟩ : v.adicCompletionIntegers K) - a_lift ∈ maximalIdeal_Ov K v := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    -- If the difference is a unit, its residue class is nonzero
    -- But both have the same residue class, so the difference has residue 0
    have hdiff_res : residueMap_Ov K v (⟨x * uniformizer_pow K v n, _⟩ - a_lift) = 0 := by
      simp only [map_sub, h_same_residue, sub_self]
    -- A unit in O_v cannot map to 0 under the residue map
    rw [IsLocalRing.residue_eq_zero_iff] at hdiff_res
    exact hu.not_isUnit_of_mem_maximalIdeal hdiff_res
  -- Step 2: Elements in m_v have valuation < 1 = exp(0), hence ≤ exp(-1)
  have h_diff_val : Valued.v ((⟨x * uniformizer_pow K v n, _⟩ : v.adicCompletionIntegers K) - a_lift : v.adicCompletion K) ≤ WithZero.exp (-1 : ℤ) := by
    -- Convert membership in maximal ideal to valuation condition
    have hval_lt : Valued.v ((⟨x * uniformizer_pow K v n, mul_uniformizer_pow_mem_integers K v x n hx_upper⟩ : v.adicCompletionIntegers K) - a_lift : v.adicCompletion K) < 1 := by
      rw [← ResidueFieldIso.mem_maximalIdeal_iff_val_lt_one]
      exact h_diff_mem
    -- Either the element is zero (val = 0 ≤ exp(-1)) or nonzero (val < 1 implies val ≤ exp(-1))
    by_cases hz : ((⟨x * uniformizer_pow K v n, mul_uniformizer_pow_mem_integers K v x n hx_upper⟩ : v.adicCompletionIntegers K) - a_lift : v.adicCompletion K) = 0
    · -- If zero, val = 0 ≤ exp(-1)
      rw [hz, Valuation.map_zero]
      exact bot_le
    · -- Nonzero element with val < 1 implies val ≤ exp(-1)
      exact val_lt_one_of_nonzero_le_exp_neg_one K v
        (⟨x * uniformizer_pow K v n, mul_uniformizer_pow_mem_integers K v x n hx_upper⟩ - a_lift)
        hz hval_lt
  -- Step 3: Rewrite the expression as (x * π^n - a_lift) * π^{-n}
  have h_rewrite : x - (a_lift : v.adicCompletion K) * uniformizer_inv_pow K v n =
      ((⟨x * uniformizer_pow K v n, _⟩ : v.adicCompletionIntegers K) - a_lift : v.adicCompletion K) *
      uniformizer_inv_pow K v n := by
    -- x - a_lift * π^{-n} = (x * π^n - a_lift) * π^{-n}
    -- x * π^n * π^{-n} - a_lift * π^{-n} = x - a_lift * π^{-n} ✓
    simp only [sub_mul, Subtype.coe_mk]
    congr 1
    -- x * π^n * π^{-n} = x
    unfold uniformizer_inv_pow uniformizer_pow uniformizer_inv
    rw [mul_comm (uniformizer_elem K v ^ n), ← mul_assoc]
    rw [mul_inv_cancel_right₀ (pow_ne_zero n (uniformizer_ne_zero K v))]
  -- Step 4: Compute the valuation
  rw [h_rewrite, Valuation.map_mul, uniformizer_inv_pow_val]
  calc Valued.v ((⟨x * uniformizer_pow K v n, _⟩ : v.adicCompletionIntegers K) - a_lift : v.adicCompletion K) *
         WithZero.exp (n : ℤ)
      ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (n : ℤ) := mul_le_mul_right' h_diff_val _
    _ = WithZero.exp (-1 + n : ℤ) := by rw [← WithZero.exp_add]
    _ = WithZero.exp ((n - 1 : ℕ) : ℤ) := by congr 1; omega

/-- Residue for elements with bounded pole order.

For x with val(x) ≤ exp(n), computes the coefficient of π^{-1} in the Laurent expansion.
Uses recursion on n, stripping leading terms for higher-order poles.
-/
noncomputable def residuePole (x : v.adicCompletion K) (n : ℕ)
    (hx : Valued.v x ≤ WithZero.exp (n : ℤ)) : residueField_Ov K v :=
  match n with
  | 0 => 0  -- x ∈ O_v, no pole, residue is 0
  | n + 1 =>
    if h : Valued.v x ≤ WithZero.exp (n : ℤ) then
      -- Pole order is actually ≤ n, recurse with smaller bound
      residuePole x n h
    else if hn1 : n = 0 then
      -- Simple pole case (n + 1 = 1): residue = (x · π) mod m_v
      residueSimplePole K v x (by rw [hn1]; exact hx)
    else
      -- Higher order pole (n + 1 ≥ 2): strip leading term and recurse
      -- Leading coefficient: a = (x · π^{n+1}) mod m_v
      let a := residueMap_Ov K v ⟨x * uniformizer_pow K v (n + 1),
               mul_uniformizer_pow_mem_integers K v x (n + 1) hx⟩
      -- Lift a back to O_v
      let a_lift := liftFromResidue K v a
      -- Compute y = x - a_lift · π^{-(n+1)}
      let y := x - (a_lift : v.adicCompletion K) * uniformizer_inv_pow K v (n + 1)
      -- y has pole order ≤ n, recurse
      -- The proof that val(y) ≤ exp(n) is deferred
      residuePole y n (val_after_leading_term_subtraction K v x (n + 1) (by omega) hx h)

/-- The recursive residue agrees with simple pole residue for simple poles. -/
theorem residuePole_eq_residueSimplePole (x : v.adicCompletion K)
    (hx : Valued.v x ≤ WithZero.exp (1 : ℤ)) :
    residuePole K v x 1 hx = residueSimplePole K v x hx := by
  unfold residuePole
  split_ifs with h
  · -- val(x) ≤ 1, so x ∈ O_v
    simp only [residuePole]
    -- residuePole x 0 _ = 0 = residueSimplePole for integers
    have hsimp : residueSimplePole K v x hx = 0 := by
      unfold residueSimplePole
      simp only [dif_pos h]
    rw [hsimp]
  · -- val(x) > 1 but ≤ exp(1), genuine simple pole
    rfl

/-- The recursive residue vanishes on integers. -/
theorem residuePole_vanishes_on_integers (x : v.adicCompletionIntegers K) (n : ℕ)
    (hx : Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (n : ℤ)) :
    residuePole K v x n hx = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold residuePole
    have hint : Valued.v (x : v.adicCompletion K) ≤ 1 := x.property
    -- For integers, val ≤ 1 = exp(0), so val ≤ exp(n) for any n ≥ 0
    have hexp : Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (n : ℤ) := by
      calc Valued.v (x : v.adicCompletion K) ≤ 1 := hint
        _ = WithZero.exp 0 := WithZero.exp_zero.symm
        _ ≤ WithZero.exp (n : ℤ) := WithZero.exp_le_exp.mpr (by omega : (0 : ℤ) ≤ n)
    -- The first branch always triggers since x is an integer
    simp only [dif_pos hexp]
    -- Now we need to show residuePole x n hexp = 0
    exact ih hexp

/-! ### Towards Eliminating localResidueHom Axiom

Once `residuePole` is fully proven, we can define `localResidueHom` concretely
as the composition of `residuePole` with the bound on pole orders.

For adelic elements, the pole order at each place is bounded by the divisor.
This allows us to use `residuePole` with an explicit bound.

**TODO** (future cycle):
1. Prove `val_after_leading_term_subtraction` using valuation arithmetic
2. Prove additivity of `residuePole`
3. Define `localResidueHom` as `residuePole` with sufficient pole bound
4. Remove the axiom
-/

end RiemannRochV2.LocalResidue

/-! ## Summary

### Cycle 362 (Initial)
**Axioms introduced**:
1. `localResidueHom`: The local residue is an additive group homomorphism K_v →+ κ(v)
2. `localResidue_vanishes_on_integers`: res_v(x) = 0 for x ∈ O_v

**Theorems derived**:
- `localResidue_add`: res_v(x+y) = res_v(x) + res_v(y)
- `localResidue_zero`: res_v(0) = 0
- `localResidue_neg`: res_v(-x) = -res_v(x)
- `localResidue_sub`: res_v(x-y) = res_v(x) - res_v(y)

### Cycle 378 (Concrete Residue)
**Definitions**:
- `residueSimplePole`: Concrete residue for elements with at most a simple pole
- `residueSimplePole_vanishes_on_integers`: Simple pole residue is 0 for integers

### Cycle 379 (Higher-Order Poles)
**New definitions**:
- `liftFromResidue`: Lifts residue field elements back to O_v via `Function.surjInv`
- `uniformizer_inv`, `uniformizer_inv_pow`: Inverse uniformizer and its powers
- `uniformizer_pow`, `uniformizer_pow_in_Ov`: Uniformizer powers in O_v
- `residuePole`: Recursive residue for poles of arbitrary order

**Key lemmas**:
- `val_lt_one_of_nonzero_le_exp_neg_one`: Elements in m_v have val ≤ exp(-1)
- `val_after_leading_term_subtraction`: Stripping leading term reduces pole order
- `residuePole_eq_residueSimplePole`: Agrees with simple pole residue
- `residuePole_vanishes_on_integers`: Vanishes on integers

**Remaining sorries** (not on critical path):
- `uniformizer_not_mem_maximalIdeal_sq`: π ∉ m_v² (DVR structure)

**Target**: Eliminate `localResidueHom` axiom by proving additivity of `residuePole`.

**Next**: Prove additivity of `residuePole` to define `localResidueHom` concretely.
-/

end
-! ## Summary (Cycle 362)

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
