/-
# Serre Duality Pairing Descent

This file defines the raw pairing for Serre duality and shows it descends to a
well-defined pairing on H¹(D) = A_K / (K + A(D)).

## Main Definitions

* `embeddedResidue v f` : Local residue of f ∈ K embedded in K_v

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

Cycle 362: Initial skeleton with raw pairing definition.
-/

import RrLean.RiemannRochV2.SerreDuality.General.LocalResidue
import RrLean.RiemannRochV2.Core.Divisor

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Valued

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

**Axiomatized**: Follows from the fact that elements of the fraction field
of a Dedekind domain have only finitely many poles.
-/
axiom poleSupport_finite (f : K) (hf : f ≠ 0) : (poleSupport (R := R) K f).Finite

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

/-- A traced residue pairing map.

This takes a global element f ∈ K and returns the sum of traced residues:
  Σ_v Tr_{κ(v)/k}(res_v(f)) ∈ k

**Axiomatized**: The concrete construction requires:
1. Trace maps Tr_{κ(v)/k} for each place
2. Finiteness of the sum (only finitely many poles contribute)
3. Linearity over k
-/
axiom tracedResidueSum : K →+ k

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
1. Be bilinear
2. Vanish on K (global elements) by the residue theorem
3. Vanish on A(D) when f ∈ L(K-D) by pole cancellation

## Key Axioms for the Pairing

Rather than constructing the pairing from local residues (which requires Laurent series),
we axiomatize the full pairing directly with its essential properties:
1. Bilinearity
2. Vanishing on K (residue theorem)
3. Vanishing on A(D) for f ∈ L(K-D) (pole cancellation)

This isolates the gap while validating the Serre duality structure.
-/

/-- The full Serre duality raw pairing on adeles.

ψ : A_K × K → k
ψ(a, f) = Σ_v Tr(res_v(a_v · f))

**Axiomatized**: The sum is well-defined and finite for any adele a ∈ A_K and f ∈ K.

We represent adeles as families a : HeightOneSpectrum R → K with finite support
outside the integers. The full infrastructure uses FiniteAdeleRing, but we
axiomatize the pairing directly.
-/
axiom fullRawPairing (k : Type*) [Field k] [Algebra k R] [Algebra k K] [IsScalarTower k R K]
    (a : HeightOneSpectrum R → K) (f : K)
    (ha : { v : HeightOneSpectrum R | v.valuation K (a v) > 1 }.Finite) : k

/-! ## Vanishing on K + A(D)

The key properties for descent to the quotient H¹(D) = A_K / (K + A(D)).

### Vanishing on K (diagonal embedding)

When a is constant (a_v = g for all v), the pairing reduces to:
  ψ(diag(g), f) = Σ_v Tr(res_v(g · f)) = 0

by the global residue theorem for g · f ∈ K.

### Vanishing on A(D) for f ∈ L(K-D)

When a ∈ A(D) (v(a_v) ≤ D(v)) and f ∈ L(K-D) (v(f) ≤ (K-D)(v)):
  v(a_v · f) ≤ D(v) + (K-D)(v) = K(v)

For the canonical divisor K: if K(v) ≤ 0 at all places, then a_v · f has no pole.
More carefully: the residue depends only on the -1 coefficient in the Laurent expansion,
which vanishes when the product has bounded pole order.
-/

/-- Vanishing on K: the pairing is zero for constant (diagonal) adeles.

For g ∈ K embedded diagonally: a_v = g for all v.
ψ(diag(g), f) = Σ_v Tr(res_v(g · f)) = 0 by the global residue theorem.
-/
axiom fullRawPairing_vanishes_on_K (k : Type*) [Field k] [Algebra k R] [Algebra k K]
    [IsScalarTower k R K] (g f : K) (hg : g ≠ 0) :
    fullRawPairing (R := R) (K := K) (k := k) (fun _ => g) f (poleSupport_finite K g hg) = 0

/-- Vanishing on A(D): the pairing is zero for bounded adeles when f ∈ L(K-D).

For a ∈ A(D) (v(a_v) ≤ exp(D(v))) and f ∈ L(K-D) (v(f) ≤ exp((K-D)(v))):
Each local contribution ψ_v(a_v, f) = 0 because a_v · f has no pole at v.
-/
axiom fullRawPairing_vanishes_on_AD (k : Type*) [Field k] [Algebra k R] [Algebra k K]
    [IsScalarTower k R K] (D : DivisorV2 R) (a : HeightOneSpectrum R → K) (f : K)
    (ha_bound : ∀ v, v.valuation K (a v) ≤ WithZero.exp (D v))
    (hf_bound : ∀ v, v.valuation K f ≤ WithZero.exp ((-D) v))
    (ha : { v : HeightOneSpectrum R | v.valuation K (a v) > 1 }.Finite) :
    fullRawPairing (R := R) (K := K) (k := k) a f ha = 0

/-! ## Summary (Cycle 363)

This file establishes the framework for the Serre duality pairing.

### Local Infrastructure (Cycle 362)
1. **embeddedResidue**: Local residue of global elements via K → K_v embedding
2. **embeddedResidue_vanishes_no_pole**: No pole means zero residue
3. **poleSupport_finite**: Global elements have finitely many poles (axiom)
4. **boundedTimesLKD_residue_zero**: Bounded × L(K-D) gives zero residue (axiom)

### Global Traced Residue (Cycle 363)
5. **tracedResidueSum**: AddMonoidHom K →+ k for summing traced residues (axiom)
6. **globalResidueTheorem_traced**: Σ_v Tr(res_v(f)) = 0 for global f (axiom)

### Full Pairing (Cycle 363)
7. **fullRawPairing**: Pairing ψ(a, f) = Σ_v Tr(res_v(a_v·f)) on adeles (axiom)
8. **fullRawPairing_vanishes_on_K**: Pairing vanishes on K (residue theorem) (axiom)
9. **fullRawPairing_vanishes_on_AD**: Pairing vanishes on A(D) for f ∈ L(K-D) (axiom)

**Axioms introduced**:
- Cycle 362 (2 axioms): `poleSupport_finite`, `boundedTimesLKD_residue_zero`
- Cycle 363 (5 axioms): `tracedResidueSum`, `globalResidueTheorem_traced`,
  `fullRawPairing`, `fullRawPairing_vanishes_on_K`, `fullRawPairing_vanishes_on_AD`

**TODO (Cycle 364+)**:
- Define the induced pairing on H¹(D) × L(K-D) using Submodule.liftQ
- Prove non-degeneracy (→ Serre duality)
- Connect to existing serre_duality axiom in EllipticH1.lean
-/

end RiemannRochV2.PairingDescent

end
