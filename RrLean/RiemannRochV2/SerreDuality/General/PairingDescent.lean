/-
# Serre Duality Pairing Descent

This file defines the raw pairing for Serre duality and shows it descends to a
well-defined pairing on H¹(D) = A_K / (K + A(D)).

## Main Definitions

* `embeddedResidue v f` : Local residue of f ∈ K embedded in K_v
* `fullRawPairing` : The raw Serre duality pairing on FiniteAdeleRing
* `serrePairingLeft` : Bundled linear map for use with liftQ

## Mathematical Setup

For a smooth projective curve C over a field k with function field K:
- A_K = restricted product Π'_v K_v (adeles)
- H¹(D) = A_K / (K + A(D)) (first adelic cohomology)
- L(K-D) = {f ∈ K : div(f) + K - D ≥ 0} (Riemann-Roch space)

The Serre duality pairing:
  φ : H¹(D) × L(K-D) → k
  φ([a], f) = Σ_v res_v(a_v · f)

is well-defined (vanishes on K + A(D)) and non-degenerate.

## Status

Cycle 364: Refactor for liftQ compatibility.
- Use FiniteAdeleRing R K directly (no witness parameter)
- Add bilinearity axioms
- Add canonical divisor parameter for L(K-D) bounds
-/

import RrLean.RiemannRochV2.SerreDuality.General.LocalResidue
import RrLean.RiemannRochV2.Core.Divisor
import RrLean.RiemannRochV2.Core.RRSpace
import RrLean.RiemannRochV2.Adelic.AdelicH1v2
import RrLean.RiemannRochV2.ResidueTheory.DifferentIdealBridge
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Trace.Basic

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped Valued nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace RiemannRochV2.PairingDescent

/-! ## Embedding K into Completions

For f ∈ K, we embed it into K_v = v.adicCompletion K via algebraMap.
Then we can apply localResidue to get an element of κ(v).
-/

variable (K) (v : HeightOneSpectrum R)

/-- Embed an element f ∈ K into the completion K_v using algebraMap. -/
abbrev embed (f : K) : v.adicCompletion K :=
  algebraMap K (v.adicCompletion K) f

/-- The local residue of a global element f ∈ K at place v.
This embeds f into K_v and applies the local residue map. -/
def embeddedResidue (f : K) : LocalResidue.residueField_Ov K v :=
  LocalResidue.localResidue K v (embed K v f)

/-! ## Properties of Embedded Residue -/

/-- Embedded residue is additive in f. -/
theorem embeddedResidue_add (f g : K) :
    embeddedResidue K v (f + g) = embeddedResidue K v f + embeddedResidue K v g := by
  unfold embeddedResidue embed
  simp only [map_add]
  exact LocalResidue.localResidue_add K v _ _

/-- Embedded residue of 0 is 0. -/
theorem embeddedResidue_zero : embeddedResidue K v 0 = 0 := by
  unfold embeddedResidue embed
  simp only [map_zero]
  exact LocalResidue.localResidue_zero K v

/-- Embedded residue vanishes for elements with no pole at v.

When v(f) ≤ 1, f embeds into O_v, so the residue is 0.
-/
theorem embeddedResidue_vanishes_no_pole (f : K) (hf : v.valuation K f ≤ 1) :
    embeddedResidue K v f = 0 := by
  unfold embeddedResidue
  -- Need to show embed K v f ∈ adicCompletionIntegers K
  have hmem : embed K v f ∈ v.adicCompletionIntegers K := by
    show Valued.v (embed K v f) ≤ 1
    -- The embedding preserves valuation
    have hcoe : embed K v f = (f : v.adicCompletion K) := rfl
    rw [hcoe, valuedAdicCompletion_eq_valuation' (R := R)]
    exact hf
  exact LocalResidue.localResidue_vanishes_on_integers K v ⟨embed K v f, hmem⟩

/-! ## Global Residue Theorem

The key property: for any global element f ∈ K, the sum of local residues
over all places with poles is zero. This is the residue theorem.
-/

/-- The support of f: finite places where f has a pole (v(f) > 1). -/
def poleSupport (f : K) : Set (HeightOneSpectrum R) :=
  { w | w.valuation K f > 1 }

/-- The pole support is finite for any nonzero f ∈ K.

This is a fundamental property of function fields: a global element
has only finitely many poles.

**Proof** (Cycle 376): Uses `FractionalIdeal.finite_factors` from Mathlib.
The key steps:
1. v.valuation K f > 1 iff count K v (spanSingleton f) < 0 (via valuation_eq_exp_neg_count)
2. The set {v | count K v I ≠ 0} is finite for any fractional ideal I
3. {v | count < 0} ⊆ {v | count ≠ 0}, so the pole support is finite
-/
theorem poleSupport_finite (f : K) (hf : f ≠ 0) : (poleSupport (R := R) K f).Finite := by
  -- The pole support is {v | v.valuation K f > 1}
  -- By valuation_eq_exp_neg_count: v.valuation K f = exp(-count K v (spanSingleton f))
  -- So v.valuation K f > 1 iff -count K v (spanSingleton f) > 0 iff count < 0
  -- The support of count is finite by FractionalIdeal.finite_factors

  -- First, get the fractional ideal corresponding to f
  let I := spanSingleton R⁰ f
  have hI : I ≠ 0 := spanSingleton_ne_zero_iff.mpr hf

  -- finite_factors says: eventually (wrt cofinite), count K v I = 0
  -- This means {v | count K v I ≠ 0} is finite
  have h_finite_support : {v : HeightOneSpectrum R | count K v I ≠ 0}.Finite := by
    have h := FractionalIdeal.finite_factors I
    rw [Filter.eventually_cofinite] at h
    exact h

  -- The pole support is a subset of this finite set
  apply Set.Finite.subset h_finite_support
  intro v hv
  -- hv : v ∈ poleSupport K f, i.e., v.valuation K f > 1
  -- Need: count K v I ≠ 0
  unfold poleSupport at hv
  simp only [Set.mem_setOf_eq] at hv

  -- Use valuation_eq_exp_neg_count to relate valuation to count
  have h_val := RiemannRochV2.valuation_eq_exp_neg_count R K v f hf
  rw [h_val] at hv
  -- hv : WithZero.exp (-count K v I) > 1

  -- exp(-n) > 1 = exp(0) iff -n > 0 iff n < 0
  -- So count K v I < 0, which means count K v I ≠ 0
  simp only [Set.mem_setOf_eq]
  by_contra h_count_zero
  rw [h_count_zero, neg_zero, WithZero.exp_zero] at hv
  exact lt_irrefl 1 hv

/-! ## The Raw Pairing Structure

For a ∈ (HeightOneSpectrum R → K) (simplified adele) and f ∈ K:
  ψ(a, f) = Σ_v res_v(a_v · f)

The full formalization requires:
1. A target field for summing residues (isomorphic residue fields)
2. Finite sum over effective support
3. Proof that pairing vanishes on K + A(D)

We outline the structure here; full implementation needs additional infrastructure.
-/

/-- Check if a function a : HeightOneSpectrum R → K has finite "effective support"
relative to a function f: places where a_v · f might have poles. -/
def hasFiniteEffectiveSupport (a : HeightOneSpectrum R → K) (f : K) : Prop :=
  { w : HeightOneSpectrum R | w.valuation K (a w * f) > 1 }.Finite

/-! ## Vanishing Principles

The key theorems for pairing descent:

### Part 1: Vanishing on K (global elements)

When a is a global element (constant function v ↦ g for some g ∈ K),
ψ(diag(g), f) = Σ_v res_v(g · f) = 0 by the global residue theorem.

### Part 2: Vanishing on A(D) for f ∈ L(K-D)

When a ∈ A(D) (v(a_v) ≤ D(v) for all v) and f ∈ L(K-D) (v(f) ≤ (K-D)(v) for all v):
- At each v: v(a_v · f) ≤ D(v) + (K-D)(v) = K(v)
- For the canonical divisor K: this bounds the pole order
- Careful analysis shows the product has residue 0
-/

/-- Bounded adele times L(K-D) element has zero residue.

**Axiomatized**: When a_v has bounded pole (v(a_v) ≤ exp(D(v))) and
f ∈ L(K-D) (v(f) ≤ exp((K-D)(v))), the product a_v · f has residue 0.

This follows from valuation arithmetic: v(a_v · f) = v(a_v) · v(f).
When the valuations multiply to something ≤ 1 (no pole), the residue vanishes.
-/
axiom boundedTimesLKD_residue_zero (D : DivisorV2 R) (w : HeightOneSpectrum R)
    (a_w : K) (f : K)
    (ha : w.valuation K a_w ≤ WithZero.exp (D w))
    (hf : ∀ u : HeightOneSpectrum R, u.valuation K f ≤ WithZero.exp ((-D) u))
    : embeddedResidue K w (a_w * f) = 0

/-! ## Sum of Residues to Base Field

To define a pairing H¹(D) × L(K-D) → k, we need to sum residues in a common base field.

For each place v, the local residue lies in κ(v) = O_v/m_v. To get a value in k,
we use the trace map Tr_{κ(v)/k}.

**Axiomatization**: We axiomatize the traced residue sum directly, assuming:
1. A base field k over which everything is defined
2. For each place v, there's a trace Tr_{κ(v)/k} : κ(v) → k
3. The sum Σ_v Tr_{κ(v)/k}(res_v(f)) is well-defined and finite for global f ∈ K
-/

section TracedResidueSum

variable (k : Type*) [Field k] [Algebra k R] [Algebra k K] [IsScalarTower k R K]

/-- A traced residue sum map as a k-linear map.

This takes a global element f ∈ K and returns the sum of traced residues:
  Σ_v Tr_{κ(v)/k}(res_v(f)) ∈ k

**Axiomatized**: The concrete construction requires:
1. Trace maps Tr_{κ(v)/k} for each place
2. Finiteness of the sum (only finitely many poles contribute)
3. Linearity over k

Using →ₗ[k] (LinearMap) rather than →+ (AddMonoidHom) for compatibility with
Submodule.liftQ which requires linearity.
-/
axiom tracedResidueSum : K →ₗ[k] k

/-- The Global Residue Theorem: sum of traced residues of a global element is zero.

This is the fundamental theorem that makes the Serre duality pairing well-defined:
For any f ∈ K, Σ_v Tr(res_v(f)) = 0.

**Axiomatized**: This is a classical theorem from algebraic geometry.
For P¹, it follows from the residue theorem for rational functions.
For general curves, it's the Residue Theorem / Stokes' theorem on curves.
-/
axiom globalResidueTheorem_traced (f : K) : tracedResidueSum (K := K) k f = 0

end TracedResidueSum

/-! ## The Raw Serre Duality Pairing

The Serre duality pairing is built from residues:
  ψ(a, f) = Σ_v Tr(res_v(a_v · f))

For a ∈ A_K (adele) and f ∈ K (global element).

We need this to:
1. Be bilinear over k
2. Vanish on K (global elements) by the residue theorem
3. Vanish on A(D) when f ∈ L(K-D) by pole cancellation

## Key Design Decision (Cycle 364)

We use `FiniteAdeleRing R K` directly rather than `HeightOneSpectrum R → K` with
a witness parameter. The FiniteAdeleRing type from Mathlib handles the finite
support condition automatically, making the API cleaner for liftQ.

## Key Axioms for the Pairing

Rather than constructing the pairing from local residues (which requires Laurent series),
we axiomatize the full pairing directly with its essential properties:
1. Bilinearity (add/smul in both arguments)
2. Vanishing on K (residue theorem)
3. Vanishing on A(D) for f ∈ L(K-D) (pole cancellation)

This isolates the gap while validating the Serre duality structure.
-/

section RawPairing

variable (k : Type*) [Field k] [Algebra k R] [Algebra k K] [IsScalarTower k R K]

/-- The full Serre duality raw pairing on finite adeles.

ψ : FiniteAdeleRing R K × K → k
ψ(a, f) = Σ_v Tr(res_v(a_v · f))

**Axiomatized**: The sum is well-defined and finite for any adele a ∈ A_K and f ∈ K.
The FiniteAdeleRing type ensures adeles have finite support outside integers.
-/
axiom fullRawPairing : FiniteAdeleRing R K → K → k

/-! ### Bilinearity Axioms

The pairing is k-bilinear. This is essential for descent via Submodule.liftQ.
-/

/-- Additivity in the left (adele) argument. -/
axiom fullRawPairing_add_left (a b : FiniteAdeleRing R K) (f : K) :
    fullRawPairing (R := R) (K := K) k (a + b) f =
    fullRawPairing (R := R) (K := K) k a f + fullRawPairing (R := R) (K := K) k b f

/-- Additivity in the right (function) argument. -/
axiom fullRawPairing_add_right (a : FiniteAdeleRing R K) (f g : K) :
    fullRawPairing (R := R) (K := K) k a (f + g) =
    fullRawPairing (R := R) (K := K) k a f + fullRawPairing (R := R) (K := K) k a g

/-- Scalar multiplication in the left argument.
Note: FiniteAdeleRing has an R-algebra structure via Mathlib. We axiomatize k-linearity.
-/
axiom fullRawPairing_smul_left (c : k) (a : FiniteAdeleRing R K) (f : K) :
    fullRawPairing (R := R) (K := K) k (c • a) f =
    c * fullRawPairing (R := R) (K := K) k a f

/-- Scalar multiplication in the right argument. -/
axiom fullRawPairing_smul_right (a : FiniteAdeleRing R K) (c : k) (f : K) :
    fullRawPairing (R := R) (K := K) k a (c • f) =
    c * fullRawPairing (R := R) (K := K) k a f

/-- Pairing with zero adele is zero. -/
axiom fullRawPairing_zero_left (f : K) :
    fullRawPairing (R := R) (K := K) k 0 f = 0

/-- Pairing with zero function is zero. -/
axiom fullRawPairing_zero_right (a : FiniteAdeleRing R K) :
    fullRawPairing (R := R) (K := K) k a 0 = 0

/-! ### Bundled Linear Maps

For use with Submodule.liftQ, we provide bundled linear maps.
-/

/-- The pairing as a k-linear map in the left argument, fixing f ∈ K. -/
def serrePairingLeft (f : K) : FiniteAdeleRing R K →ₗ[k] k where
  toFun := fun a => fullRawPairing (R := R) (K := K) k a f
  map_add' := fun a b => fullRawPairing_add_left (R := R) (K := K) (k := k) a b f
  map_smul' := fun c a => fullRawPairing_smul_left (R := R) (K := K) (k := k) c a f

/-- The pairing as a k-linear map in the right argument, fixing a ∈ A_K. -/
def serrePairingRight (a : FiniteAdeleRing R K) : K →ₗ[k] k where
  toFun := fun f => fullRawPairing (R := R) (K := K) k a f
  map_add' := fun f g => fullRawPairing_add_right (R := R) (K := K) (k := k) a f g
  map_smul' := fun c f => fullRawPairing_smul_right (R := R) (K := K) (k := k) a c f

/-! ## Vanishing on K + A(D)

The key properties for descent to the quotient H¹(D) = A_K / (K + A(D)).

### Vanishing on K (diagonal embedding)

When a is the diagonal embedding of g ∈ K:
  ψ(diag(g), f) = Σ_v Tr(res_v(g · f)) = 0

by the global residue theorem for g · f ∈ K.

### Vanishing on A(D) for f ∈ L(KDiv - D)

When a ∈ A(D) (v(a_v) ≤ D(v)) and f ∈ L(KDiv - D) (v(f) ≥ -(KDiv - D)(v)):
  v(a_v · f) ≤ D(v) + (KDiv - D)(v) = KDiv(v)

For the canonical divisor KDiv with deg(KDiv) = 2g-2: when KDiv(v) ≤ -1 at all places
where a has poles, the product a · f has no contribution to the residue.
-/

/-- Vanishing on K: the pairing is zero for diagonal adeles.

For g ∈ K embedded diagonally via FiniteAdeleRing.algebraMap:
ψ(diag(g), f) = Σ_v Tr(res_v(g · f)) = 0 by the global residue theorem.

This includes g = 0 (trivially zero).
-/
axiom fullRawPairing_vanishes_on_K (g f : K) :
    fullRawPairing (R := R) (K := K) k (FiniteAdeleRing.algebraMap R K g) f = 0

/-- Vanishing on A(D): the pairing is zero for bounded adeles when f ∈ L(KDiv - D).

For a ∈ A(D) and f ∈ L(KDiv - D) where KDiv is the canonical divisor:
Each local contribution ψ_v(a_v, f) vanishes because the product has residue 0.

The canonical divisor KDiv is passed as a parameter to make the bound explicit.
For smooth projective curves, deg(KDiv) = 2g - 2.
-/
axiom fullRawPairing_vanishes_on_AD (D KDiv : DivisorV2 R) (a : FiniteAdeleRing R K) (f : K)
    (ha_bound : ∀ v, Valued.v (a.1 v) ≤ WithZero.exp (D v))
    (hf_bound : ∀ v, v.valuation K f ≤ WithZero.exp ((KDiv - D) v)) :
    fullRawPairing (R := R) (K := K) k a f = 0

/-! ### Trace-Residue Bridge Axiom (Cycle 374)

The following axiom connects the residue-based `fullRawPairing` to the global trace form.
This bridges the gap between:
1. Mathlib's `traceForm_nondegenerate` which gives trace witnesses
2. The adelic pairing structure needed for Serre duality

The mathematical content is: a trace witness for f (i.e., x with Tr(xf) ≠ 0) can be
"lifted" to an adelic witness (i.e., an adele a with pairing(a, f) ≠ 0).
-/

variable [FiniteDimensional k K] [Algebra.IsSeparable k K]

/-- Trace non-degeneracy lifts to the residue pairing.

If f ≠ 0 and there exists x ∈ K with Tr_{K/k}(x · f) ≠ 0 (a trace witness),
then there exists an adele a not in K + A_K(D) such that fullRawPairing(a, f) ≠ 0.

This bridges the global trace non-degeneracy (from Mathlib) to the adelic residue pairing,
enabling derivation of non-degeneracy of the Serre duality pairing.

**Mathematical justification**:
The trace Tr_{K/k}(x · f) relates to the sum Σ_v Tr_{κ(v)/k}(res_v(...)) via:
1. Local-global principle for residues
2. The trace decomposes as sum of local traces over places
3. A suitable adele can be constructed from the trace witness

**Axiomatized** because the full proof requires Laurent series or
detailed local-global residue analysis.
-/
axiom fullRawPairing_from_trace_witness (D : DivisorV2 R) (f : K) (hf : f ≠ 0)
    (x : K) (htr : Algebra.trace k K (x * f) ≠ 0) :
    ∃ a : FiniteAdeleRing R K,
      a ∉ AdelicH1v2.globalPlusBoundedSubmodule k R K D ∧
      fullRawPairing (R := R) (K := K) k a f ≠ 0

/-- Left non-degeneracy from trace: universal pairing vanishing implies membership.

This is the left-side dual of `fullRawPairing_from_trace_witness`.

If fullRawPairing(a, f) = 0 for all f satisfying the L(KDiv-D) valuation conditions,
then a ∈ K + A(D).

**Mathematical justification**:
1. L(KDiv-D) corresponds to a fractional ideal (the trace dual of I_{2*KDiv-D})
2. If the residue pairing vanishes on this entire space
3. By trace non-degeneracy properties, the adele must be "trivial" (in K + A(D))

The key insight is that L(KDiv-D) is "large enough" that universal vanishing
on this space forces membership in the kernel K + A(D).

**Axiomatized** because proving this requires the detailed connection between
local residues at each place and the global trace structure, similar to the
right-side axiom `fullRawPairing_from_trace_witness`.
-/
axiom fullRawPairing_left_vanishing_to_mem (D KDiv : DivisorV2 R)
    (a : FiniteAdeleRing R K)
    (h_all_vanish : ∀ f : K, satisfiesValuationCondition R K (KDiv - D) f →
        fullRawPairing (R := R) (K := K) k a f = 0) :
    a ∈ AdelicH1v2.globalPlusBoundedSubmodule k R K D

end RawPairing

/-! ## Summary

This file establishes the framework for the Serre duality pairing.

### Local Infrastructure (Cycle 362, updated Cycle 376)
1. **embeddedResidue**: Local residue of global elements via K → K_v embedding
2. **embeddedResidue_vanishes_no_pole**: No pole means zero residue
3. **poleSupport_finite**: Global elements have finitely many poles (**THEOREM** Cycle 376)
4. **boundedTimesLKD_residue_zero**: Bounded × L(K-D) gives zero residue (axiom)

### Global Traced Residue (Cycle 363)
5. **tracedResidueSum**: K →ₗ[k] k for summing traced residues (axiom)
6. **globalResidueTheorem_traced**: Σ_v Tr(res_v(f)) = 0 for global f (axiom)

### Full Pairing (Cycle 364 - Refactored)
7. **fullRawPairing**: Pairing ψ : FiniteAdeleRing R K → K → k (axiom)
8. **Bilinearity axioms**: add_left, add_right, smul_left, smul_right, zero_left, zero_right
9. **serrePairingLeft/Right**: Bundled linear maps for liftQ compatibility
10. **fullRawPairing_vanishes_on_K**: Pairing vanishes on K (axiom)
11. **fullRawPairing_vanishes_on_AD**: Pairing vanishes on A(D) for f ∈ L(KDiv-D) (axiom)

**Axioms introduced** (current count: 14):
- Cycle 362 (1 axiom): `boundedTimesLKD_residue_zero`
  - `poleSupport_finite` now THEOREM (Cycle 376)
- Cycle 363 (2 axioms): `tracedResidueSum`, `globalResidueTheorem_traced`
- Cycle 364 (9 axioms): `fullRawPairing`, `fullRawPairing_add_left`, `fullRawPairing_add_right`,
  `fullRawPairing_smul_left`, `fullRawPairing_smul_right`, `fullRawPairing_zero_left`,
  `fullRawPairing_zero_right`, `fullRawPairing_vanishes_on_K`, `fullRawPairing_vanishes_on_AD`
- Cycle 374 (1 axiom): `fullRawPairing_from_trace_witness` (trace-residue bridge, right non-deg)
- Cycle 375 (1 axiom): `fullRawPairing_left_vanishing_to_mem` (trace-residue bridge, left non-deg)

**Key Changes in Cycle 364**:
- Use FiniteAdeleRing R K directly (no witness parameter)
- tracedResidueSum now K →ₗ[k] k (linear over k)
- Added full bilinearity axioms for liftQ compatibility
- Added bundled linear maps serrePairingLeft/Right
- Use canonical divisor KDiv parameter in vanishing_on_AD
- Handle g = 0 case (no longer requires g ≠ 0)

**Cycle 365**:
- Define induced pairing on H¹(D) × L(KDiv-D) via Submodule.liftQ
- serrePairingLeft vanishes on K + A(D) for f ∈ L(KDiv-D)

**TODO (Cycle 366+)**:
- Prove non-degeneracy (→ Serre duality)
- Connect to existing serre_duality axiom in EllipticH1.lean
-/

end RiemannRochV2.PairingDescent

/-! ## Cycle 365: Induced Pairing on H¹(D)

The raw pairing `fullRawPairing : FiniteAdeleRing R K → K → k` descends to the quotient
H¹(D) = FiniteAdeleRing R K / (K + A_K(D)) when restricted to f ∈ L(KDiv - D).

The key facts:
1. `fullRawPairing_vanishes_on_K` → pairing vanishes on diagonal K
2. `fullRawPairing_vanishes_on_AD` → pairing vanishes on A_K(D) when f ∈ L(KDiv - D)

Combined, `serrePairingLeft f` vanishes on `globalPlusBoundedSubmodule k R K D`,
so it descends via `Submodule.liftQ` to a well-defined linear map on H¹(D).
-/

namespace RiemannRochV2.SerrePairingDescent

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open RiemannRochV2.PairingDescent
open RiemannRochV2.AdelicH1v2

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (k : Type*) [Field k] [Algebra k R] [Algebra k K] [IsScalarTower k R K]

/-! ## Vanishing on K + A(D)

We prove that `serrePairingLeft f` vanishes on `globalPlusBoundedSubmodule k R K D`
when f ∈ L(KDiv - D).
-/

/-- serrePairingLeft f vanishes on the diagonal embedding of K. -/
theorem serrePairingLeft_vanishes_on_globalSubmodule (f : K) :
    ∀ a ∈ globalSubmodule k R K, serrePairingLeft (R := R) (K := K) k f a = 0 := by
  intro a ha
  -- a is in the image of diagonalK = FiniteAdeleRing.algebraMap R K
  obtain ⟨g, rfl⟩ := ha
  -- serrePairingLeft k f (diagonalK R K g) = fullRawPairing k (diagonalK R K g) f
  simp only [serrePairingLeft]
  -- diagonalK R K = FiniteAdeleRing.algebraMap R K
  show fullRawPairing (R := R) (K := K) k (diagonalK R K g) f = 0
  -- By definition, diagonalK R K = FiniteAdeleRing.algebraMap R K
  exact fullRawPairing_vanishes_on_K (R := R) (K := K) k g f

/-- serrePairingLeft f vanishes on A_K(D) when f ∈ L(KDiv - D). -/
theorem serrePairingLeft_vanishes_on_boundedSubmodule (D KDiv : DivisorV2 R) (f : K)
    (hf : satisfiesValuationCondition R K (KDiv - D) f) :
    ∀ a ∈ boundedSubmodule k R K D, serrePairingLeft (R := R) (K := K) k f a = 0 := by
  intro a ha
  simp only [serrePairingLeft]
  -- ha : a ∈ boundedSubmodule k R K D means ∀ v, valuationAt R K a v ≤ exp(D v)
  -- hf : f ∈ L(KDiv - D) means f = 0 ∨ ∀ v, v.valuation K f ≤ exp((KDiv - D) v)
  -- Need to apply fullRawPairing_vanishes_on_AD
  rcases hf with rfl | hf_bound
  · -- f = 0 case
    exact fullRawPairing_zero_right (R := R) (K := K) k a
  · -- f satisfies valuation bounds
    apply fullRawPairing_vanishes_on_AD (R := R) (K := K) k D KDiv a f
    · -- ha_bound : ∀ v, Valued.v (a.1 v) ≤ WithZero.exp (D v)
      intro v
      have ha_v := ha v
      simp only [satisfiesBoundAt, valuationAt] at ha_v
      exact ha_v
    · -- hf_bound : ∀ v, v.valuation K f ≤ WithZero.exp ((KDiv - D) v)
      exact hf_bound

/-- serrePairingLeft f vanishes on K + A_K(D) when f ∈ L(KDiv - D).

This is the key lemma for descent to the quotient H¹(D). -/
theorem serrePairingLeft_vanishes_on_globalPlusBoundedSubmodule (D KDiv : DivisorV2 R) (f : K)
    (hf : satisfiesValuationCondition R K (KDiv - D) f) :
    ∀ a ∈ globalPlusBoundedSubmodule k R K D, serrePairingLeft (R := R) (K := K) k f a = 0 := by
  intro a ha
  -- globalPlusBoundedSubmodule = globalSubmodule + boundedSubmodule (as submodule sum)
  -- ha : a ∈ globalSubmodule k R K + boundedSubmodule k R K D
  rw [globalPlusBoundedSubmodule] at ha
  obtain ⟨g, hg, b, hb, rfl⟩ := Submodule.mem_sup.mp ha
  -- a = g + b where g ∈ globalSubmodule and b ∈ boundedSubmodule
  rw [(serrePairingLeft (R := R) (K := K) k f).map_add]
  rw [serrePairingLeft_vanishes_on_globalSubmodule k f g hg]
  rw [serrePairingLeft_vanishes_on_boundedSubmodule k D KDiv f hf b hb]
  ring

/-! ## Induced Pairing on H¹(D)

Using Submodule.liftQ, we lift the pairing to the quotient.
-/

/-- The induced pairing on H¹(D) for a fixed f ∈ L(KDiv - D).

Given f ∈ L(KDiv - D), this is the k-linear map:
  φ_f : H¹(D) → k
  φ_f([a]) = ψ(a, f)

Well-defined because ψ(·, f) vanishes on K + A_K(D). -/
def inducedPairingOnH1 (D KDiv : DivisorV2 R) (f : K)
    (hf : satisfiesValuationCondition R K (KDiv - D) f) :
    SpaceModule k R K D →ₗ[k] k :=
  Submodule.liftQ (globalPlusBoundedSubmodule k R K D)
    (serrePairingLeft (R := R) (K := K) k f)
    (serrePairingLeft_vanishes_on_globalPlusBoundedSubmodule k D KDiv f hf)

/-- The induced pairing applied to a quotient element. -/
theorem inducedPairingOnH1_apply (D KDiv : DivisorV2 R) (f : K)
    (hf : satisfiesValuationCondition R K (KDiv - D) f)
    (a : FiniteAdeleRing R K) :
    inducedPairingOnH1 k D KDiv f hf (Submodule.Quotient.mk a) =
    fullRawPairing (R := R) (K := K) k a f := by
  simp only [inducedPairingOnH1, Submodule.liftQ_apply, serrePairingLeft, LinearMap.coe_mk,
    AddHom.coe_mk]

/-! ## The Full Serre Duality Pairing

The pairing H¹(D) × L(KDiv - D) → k defined by φ([a], f) = ψ(a, f).
-/

/-- The Serre duality pairing as a bilinear map.

φ : H¹(D) × L(KDiv - D) → k
φ([a], f) = Σ_v Tr(res_v(a_v · f))

This is well-defined because:
- The pairing vanishes on K (global residue theorem)
- The pairing vanishes on A_K(D) when f ∈ L(KDiv - D) (pole cancellation)
-/
def serreDualityPairing (D KDiv : DivisorV2 R) :
    SpaceModule k R K D →ₗ[k] (RRModuleV2_real R K (KDiv - D) →ₗ[k] k) where
  toFun := fun h1_class => {
    toFun := fun ⟨f, hf⟩ => inducedPairingOnH1 k D KDiv f hf h1_class
    map_add' := fun ⟨f1, hf1⟩ ⟨f2, hf2⟩ => by
      -- Need: inducedPairingOnH1 k D KDiv (f1 + f2) h12 h1_class
      --     = inducedPairingOnH1 k D KDiv f1 hf1 h1_class + inducedPairingOnH1 k D KDiv f2 hf2 h1_class
      -- This follows from linearity of fullRawPairing in the right argument
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ h1_class
      simp only [inducedPairingOnH1_apply]
      exact fullRawPairing_add_right (R := R) (K := K) k a f1 f2
    map_smul' := fun c ⟨f, hf⟩ => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ h1_class
      simp only [inducedPairingOnH1_apply, RingHom.id_apply]
      exact fullRawPairing_smul_right (R := R) (K := K) k a c f
  }
  map_add' := fun h1 h2 => by
    ext ⟨f, hf⟩
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    exact (inducedPairingOnH1 k D KDiv f hf).map_add h1 h2
  map_smul' := fun c h1 => by
    ext ⟨f, hf⟩
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
    exact (inducedPairingOnH1 k D KDiv f hf).map_smul c h1

/-- Serre duality pairing applied to concrete representatives. -/
theorem serreDualityPairing_apply (D KDiv : DivisorV2 R)
    (a : FiniteAdeleRing R K) (f : RRModuleV2_real R K (KDiv - D)) :
    serreDualityPairing k D KDiv (Submodule.Quotient.mk a) f =
    fullRawPairing (R := R) (K := K) k a f.val := by
  simp only [serreDualityPairing, LinearMap.coe_mk, AddHom.coe_mk, inducedPairingOnH1_apply]

end RiemannRochV2.SerrePairingDescent

end
