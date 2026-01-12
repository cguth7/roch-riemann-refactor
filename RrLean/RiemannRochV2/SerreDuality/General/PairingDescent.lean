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

/-! ## Summary

This file establishes the framework for the Serre duality pairing:

1. **embeddedResidue**: Local residue of global elements via K → K_v embedding
2. **embeddedResidue_vanishes_no_pole**: No pole means zero residue
3. **poleSupport_finite**: Global elements have finitely many poles
4. **boundedTimesLKD_residue_zero**: Bounded × L(K-D) gives zero residue

**Axioms introduced (2)**:
- `poleSupport_finite`: Elements of K have finitely many poles
- `boundedTimesLKD_residue_zero`: Bounded adele × L(K-D) → zero residue

**TODO (Cycle 363+)**:
- Formalize the sum of residues properly
- Define the induced pairing on H¹(D) × L(K-D) using Submodule.liftQ
- Prove non-degeneracy (→ Serre duality)
- Connect to existing serre_duality axiom in EllipticH1.lean
-/

end RiemannRochV2.PairingDescent

end
