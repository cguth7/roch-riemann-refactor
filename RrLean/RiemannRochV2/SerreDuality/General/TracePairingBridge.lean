/-
# Trace Pairing Bridge for Serre Duality

This file establishes the connection between the residue-based Serre duality pairing
and Mathlib's trace form machinery. This is Lemma 2 of the trace-dual attack plan.

## Mathematical Context

The Serre duality pairing:
  φ : H¹(D) × L(KDiv - D) → k
  φ([a], f) = Σ_v Tr_{κ(v)/k}(res_v(a_v · f))

The Mathlib trace pairing on fractional ideals:
  ⟨x, y⟩ = Tr_{K/k}(x · y)

The key bridge is:
1. L(KDiv - D) = divisorToFractionalIdeal(D - KDiv) as sets (Lemma 1)
2. The residue sum relates to the trace form
3. Non-degeneracy of trace form implies non-degeneracy of Serre pairing

## Main Results

* `tracePairing_nondegenerate_left` : Trace pairing is non-degenerate on the left
* `residuePairing_controlled_by_trace` : Bridge axiom connecting residues to trace
* `serreDualityPairing_injective_from_trace` : Non-degeneracy from trace (future)

## References

* `Mathlib.FieldTheory.Finite.Trace` - `traceForm_nondegenerate`
* `Mathlib.RingTheory.DedekindDomain.Different` - Trace dual properties
-/

import RrLean.RiemannRochV2.SerreDuality.General.TraceDualBridge
import RrLean.RiemannRochV2.SerreDuality.General.PairingDescent
import Mathlib.RingTheory.Trace.Basic

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open FractionalIdeal
open scoped nonZeroDivisors

namespace RiemannRochV2.TracePairingBridge

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (k : Type*) [Field k] [Algebra k R] [Algebra k K] [IsScalarTower k R K]

/-! ## Trace Form Non-Degeneracy

The trace form B(x, y) = Tr_{K/k}(x · y) is a symmetric bilinear form on K.
For separable extensions, this form is non-degenerate.

We use Mathlib's `traceForm_nondegenerate` directly.
-/

section NonDegeneracy

variable [FiniteDimensional k K] [Algebra.IsSeparable k K]

/-- The trace pairing is non-degenerate on the left:
    if Tr(x · y) = 0 for all y, then x = 0. -/
theorem tracePairing_nondegenerate_left (x : K) (hx : x ≠ 0) :
    ∃ y : K, Algebra.trace k K (x * y) ≠ 0 := by
  -- Use Mathlib's traceForm_nondegenerate
  -- traceForm_nondegenerate : (traceForm k K).Nondegenerate
  -- Nondegenerate means: ∀ m, (∀ n, B m n = 0) → m = 0
  -- So contrapositive: x ≠ 0 → ∃ y, B x y ≠ 0
  by_contra h_all_zero
  push_neg at h_all_zero
  have h_nondeg := traceForm_nondegenerate k K
  have hx_zero : x = 0 := h_nondeg x (fun y => h_all_zero y)
  exact hx hx_zero

/-- The trace pairing is non-degenerate on the right:
    if Tr(x · y) = 0 for all x, then y = 0. -/
theorem tracePairing_nondegenerate_right (y : K) (hy : y ≠ 0) :
    ∃ x : K, Algebra.trace k K (x * y) ≠ 0 := by
  by_contra h_all_zero
  push_neg at h_all_zero
  have h_nondeg := traceForm_nondegenerate k K
  -- Use that trace pairing is symmetric: Tr(xy) = Tr(yx)
  have hy_zero : y = 0 := h_nondeg y (fun x => by
    have h := h_all_zero x
    rw [mul_comm] at h
    exact h)
  exact hy hy_zero

end NonDegeneracy

/-! ## Bridge: Residue Pairing to Trace Pairing

The key connection between the residue-based Serre duality pairing and the trace form.

For a global function f ∈ K and an adele a ∈ A_K:
  fullRawPairing(a, f) = Σ_v Tr_{κ(v)/k}(res_v(a_v · f))

The mathematical fact we need:
- The residue at a place v of a product (local adele) · (global function)
- Summed over all places with appropriate traces
- Relates to the global trace form in a specific way
-/

section ResidueTraceBridge

variable [FiniteDimensional k K] [Algebra.IsSeparable k K]

open RiemannRochV2.PairingDescent
open RiemannRochV2.AdelicH1v2
open RiemannRochV2.SerrePairingDescent

/-! ### Key Structural Lemma

For the non-degeneracy proof, we need:

1. **Injectivity on the left**: If φ([a], f) = 0 for all f ∈ L(KDiv-D), then [a] = 0

2. **Non-triviality on the right**: For f ≠ 0 in L(KDiv-D), ∃ [a] with φ([a], f) ≠ 0

The trace connection helps because:
- L(KDiv-D) = divisorToFractionalIdeal(D-KDiv) has a fractional ideal structure
- The trace form on fractional ideals is non-degenerate
- We can lift this to the adelic quotient
-/

/-- Key insight: Elements of L(KDiv-D) live in divisorToFractionalIdeal(D-KDiv).

By TraceDualBridge.mem_RRModuleV2_iff_mem_divisorToFractionalIdeal:
  x ∈ L(E) ↔ x ∈ divisorToFractionalIdeal(-E)

So for E = KDiv - D:
  x ∈ L(KDiv-D) ↔ x ∈ divisorToFractionalIdeal(-(KDiv-D)) = divisorToFractionalIdeal(D-KDiv)
-/
theorem L_KDivMinusD_eq_divisorToFractionalIdeal (D KDiv : DivisorV2 R) (x : K) :
    x ∈ RRModuleV2_real R K (KDiv - D) ↔
    x ∈ divisorToFractionalIdeal R K (D - KDiv) := by
  rw [TraceDualBridge.mem_RRModuleV2_iff_mem_divisorToFractionalIdeal]
  have h_neg : -(KDiv - D) = D - KDiv := by
    ext v
    simp only [Finsupp.coe_neg, Pi.neg_apply, Finsupp.coe_sub, Pi.sub_apply]
    ring
  rw [h_neg]

/-! ### The Trace-Residue Connection Axioms

The following axioms capture the key mathematical fact that the residue-based pairing
is "controlled by" the trace form.

These axioms are the mathematical heart of Serre duality: the residue pairing and
trace pairing are related in a precise way that preserves non-degeneracy.
-/

/-- The residue pairing is controlled by trace non-degeneracy.

**Mathematical statement**: If [a] ∈ H¹(D) pairs to zero with all f ∈ L(KDiv-D),
then [a] = 0.

**Proof** (Cycle 375): Derived from `fullRawPairing_left_vanishing_to_mem`:
1. The hypothesis says pairing vanishes for all f in the subtype L(KDiv-D)
2. Apply the bridging axiom which takes the vanishing condition on K
3. The subtype membership exactly provides the required condition
-/
theorem residuePairing_controlled_by_trace (D KDiv : DivisorV2 R)
    (a : FiniteAdeleRing R K)
    (h_pairs_zero : ∀ f : RRModuleV2_real R K (KDiv - D),
      fullRawPairing (R := R) (K := K) k a f.val = 0) :
    a ∈ globalPlusBoundedSubmodule k R K D := by
  -- Apply the bridging axiom from PairingDescent
  apply fullRawPairing_left_vanishing_to_mem (R := R) (K := K) k D KDiv a
  -- Need to show: ∀ f : K, satisfiesValuationCondition R K (KDiv - D) f → pairing = 0
  intro f hf
  -- Construct the subtype element and apply the hypothesis
  exact h_pairs_zero ⟨f, hf⟩

/-- Right non-degeneracy: trace non-degeneracy implies existence of witness.

**Mathematical statement**: For nonzero f ∈ L(KDiv-D), there exists an adele a
(representing a non-zero class [a] ∈ H¹(D)) such that φ([a], f) ≠ 0.

**Proof** (Cycle 374): Derived from `fullRawPairing_from_trace_witness` and
Mathlib's `traceForm_nondegenerate`:
1. Since f ≠ 0, by trace non-degeneracy (tracePairing_nondegenerate_right),
   there exists x ∈ K with Tr(x · f) ≠ 0.
2. Apply `fullRawPairing_from_trace_witness` with this trace witness to get
   an adele a ∉ K + A(D) with pairing(a, f) ≠ 0.
-/
theorem witness_from_trace_nondegen (D KDiv : DivisorV2 R)
    (f : RRModuleV2_real R K (KDiv - D)) (hf : f ≠ 0) :
    ∃ a : FiniteAdeleRing R K,
      a ∉ globalPlusBoundedSubmodule k R K D ∧
      fullRawPairing (R := R) (K := K) k a f.val ≠ 0 := by
  -- f ≠ 0 as a subtype means f.val ≠ 0
  have hf_val : f.val ≠ 0 := by
    intro h
    apply hf
    ext
    exact h
  -- By trace non-degeneracy, there exists x with Tr(x · f.val) ≠ 0
  obtain ⟨x, htr⟩ := tracePairing_nondegenerate_right k f.val hf_val
  -- Apply the bridging axiom
  exact fullRawPairing_from_trace_witness (R := R) (K := K) k D f.val hf_val x htr

end ResidueTraceBridge

/-! ## Deriving Non-Degeneracy from Trace Bridge

Using the trace-residue bridge axioms, we can prove the non-degeneracy
properties needed for Serre duality.
-/

section DerivingNonDegeneracy

variable [FiniteDimensional k K] [Algebra.IsSeparable k K]

open RiemannRochV2.AdelicH1v2
open RiemannRochV2.SerrePairingDescent
open RiemannRochV2.PairingDescent

/-- Left non-degeneracy of the Serre duality pairing, derived from trace bridge.

If φ([a], f) = 0 for all f ∈ L(KDiv-D), then [a] = 0 in H¹(D).

This is the theorem version of `serreDualityPairing_injective`, proved
using the trace-residue bridge. -/
theorem serreDualityPairing_injective_from_trace (D KDiv : DivisorV2 R) :
    Function.Injective (serreDualityPairing (R := R) (K := K) k D KDiv) := by
  intro h1_class₁ h1_class₂ heq
  -- Get representatives
  obtain ⟨a₁, rfl⟩ := Submodule.Quotient.mk_surjective _ h1_class₁
  obtain ⟨a₂, rfl⟩ := Submodule.Quotient.mk_surjective _ h1_class₂
  -- Need to show: Submodule.Quotient.mk a₁ = Submodule.Quotient.mk a₂
  rw [Submodule.Quotient.eq]
  -- Show a₁ - a₂ pairs to zero with all f
  have h_pairs_zero : ∀ f : RRModuleV2_real R K (KDiv - D),
      fullRawPairing (R := R) (K := K) k (a₁ - a₂) f.val = 0 := by
    intro f
    have h₁ : serreDualityPairing (R := R) (K := K) k D KDiv (Submodule.Quotient.mk a₁) f =
              fullRawPairing (R := R) (K := K) k a₁ f.val :=
      serreDualityPairing_apply k D KDiv a₁ f
    have h₂ : serreDualityPairing (R := R) (K := K) k D KDiv (Submodule.Quotient.mk a₂) f =
              fullRawPairing (R := R) (K := K) k a₂ f.val :=
      serreDualityPairing_apply k D KDiv a₂ f
    have heq_f : serreDualityPairing (R := R) (K := K) k D KDiv (Submodule.Quotient.mk a₁) f =
                 serreDualityPairing (R := R) (K := K) k D KDiv (Submodule.Quotient.mk a₂) f := by
      rw [heq]
    rw [h₁, h₂] at heq_f
    -- Need to show fullRawPairing k (a₁ - a₂) f.val = 0
    -- Use linearity: ψ(a₁ - a₂, f) = ψ(a₁, f) + ψ(-a₂, f) = ψ(a₁, f) - ψ(a₂, f)
    have h_sub : a₁ - a₂ = a₁ + (-1 : k) • a₂ := by
      simp only [sub_eq_add_neg, neg_smul, one_smul]
    rw [h_sub, fullRawPairing_add_left (R := R) (K := K) k a₁ ((-1 : k) • a₂) f.val,
        fullRawPairing_smul_left (R := R) (K := K) k (-1) a₂ f.val, heq_f]
    ring
  exact residuePairing_controlled_by_trace k D KDiv (a₁ - a₂) h_pairs_zero

/-- Right non-degeneracy of the Serre duality pairing, derived from trace bridge.

For nonzero f ∈ L(KDiv-D), there exists [a] ∈ H¹(D) with φ([a], f) ≠ 0.

This is the theorem version of `serreDualityPairing_right_nondegen`, proved
using the trace-residue bridge. -/
theorem serreDualityPairing_right_nondegen_from_trace (D KDiv : DivisorV2 R)
    (f : RRModuleV2_real R K (KDiv - D)) (hf : f ≠ 0) :
    ∃ h1_class : SpaceModule k R K D, serreDualityPairing (R := R) (K := K) k D KDiv h1_class f ≠ 0 := by
  -- Use the trace bridge to get a witness adele
  obtain ⟨a, ha_not_mem, ha_pairs⟩ := witness_from_trace_nondegen k D KDiv f hf
  use Submodule.Quotient.mk a
  rw [serreDualityPairing_apply (R := R) (K := K)]
  exact ha_pairs

end DerivingNonDegeneracy

/-! ## Summary

This file establishes the trace-pairing bridge (Lemma 2 of the attack plan).

**Infrastructure proved**:
1. `tracePairing_nondegenerate_left/right` : Non-degeneracy from Mathlib
2. `L_KDivMinusD_eq_divisorToFractionalIdeal` : L(KDiv-D) = I_{D-KDiv} bridge

**Axioms**: None (all derived from PairingDescent bridging axioms as of Cycle 375)

**Theorems derived**:
1. `residuePairing_controlled_by_trace` : Left non-degeneracy (Cycle 375: now PROVED from
   `fullRawPairing_left_vanishing_to_mem`)
2. `witness_from_trace_nondegen` : Right non-degeneracy (Cycle 374: now PROVED from
   `fullRawPairing_from_trace_witness` + Mathlib's `traceForm_nondegenerate`)
3. `serreDualityPairing_injective_from_trace` : Proves left non-degeneracy
4. `serreDualityPairing_right_nondegen_from_trace` : Proves right non-degeneracy

**Key insight**: The non-degeneracy of the Serre duality pairing follows from
the non-degeneracy of the trace form, via the residue-trace connection.

**Next steps**:
- Prove the 2 trace-bridge axioms using Mathlib's perfect pairing machinery
- Use `dual_mul_self`, `dual_dual`, and `mem_dual` from Mathlib.Different
- The mathematical path: residue sum relates to trace via local-global principle

**Axiom reduction path** (updated Cycle 375):
- PairingNondegenerate.lean axioms: 0 (all derived from TracePairingBridge)
- TracePairingBridge.lean axioms: 0 (all derived from PairingDescent bridging axioms)
- PairingDescent.lean axioms: 15 (including both trace bridging axioms)
- Both `witness_from_trace_nondegen` and `residuePairing_controlled_by_trace` are THEOREMS
- All non-degeneracy now flows from the 2 bridging axioms in PairingDescent
-/

/-! ## Axiom Replacement Roadmap (Updated Cycle 375)

This section documents the axiom hierarchy for Serre duality non-degeneracy.

### Current State (Cycle 375)
- `PairingNondegenerate.lean`: 0 axioms (all derived from TracePairingBridge)
- `TracePairingBridge.lean` (this file): 0 axioms (all derived from PairingDescent)
- `PairingDescent.lean`: 15 axioms (including 2 trace bridging axioms)

### Axiom Hierarchy

```
PairingDescent bridging axioms (most fundamental):
├── fullRawPairing_from_trace_witness (Cycle 374)
│   └── Trace witness (x with Tr(xf) ≠ 0) → Adelic witness (a with pairing ≠ 0)
└── fullRawPairing_left_vanishing_to_mem (Cycle 375)
    └── Universal pairing vanishing → Membership in K + A(D)
         ↓
TracePairingBridge theorems (derived):
├── witness_from_trace_nondegen (uses Mathlib traceForm_nondegenerate + bridging)
└── residuePairing_controlled_by_trace (direct application of bridging)
         ↓
PairingNondegenerate theorems (derived):
├── serreDualityPairing_injective
└── serreDualityPairing_right_nondegen
         ↓
Serre duality theorem: h¹(D) = ℓ(KDiv - D)
```

### Key Insight

The 2 bridging axioms in PairingDescent capture the essential trace-residue connection:
1. **Right**: A trace witness can be lifted to an adelic pairing witness
2. **Left**: Universal vanishing on L(KDiv-D) forces membership in K + A(D)

These are "elementary" in the sense that they're about the raw `fullRawPairing`,
not the descended pairing on quotients.

### Proving the Bridging Axioms (Future Work)

The bridging axioms would follow from:
1. Laurent series expansion at each place: K_v ≃ κ(v)((t))
2. Residue = coefficient of 1/t, and Tr_{κ(v)/k}(res_v(...)) relates to global trace
3. Local-global principle connecting adelic residue sum to trace

### Key Mathlib Lemmas

From `Mathlib.RingTheory.DedekindDomain.Different`:
- `dual_mul_self : dual(I) * I = dual(1)` — perfect pairing property
- `dual_dual : dual(dual(I)) = I` — involutive
- `mem_dual : x ∈ dual(I) ↔ ∀ a ∈ I, Tr(xa) ∈ R` — membership characterization

From `Mathlib.FieldTheory.Finite.Trace`:
- `traceForm_nondegenerate : (traceForm k K).Nondegenerate` — trace is non-degenerate
-/

end RiemannRochV2.TracePairingBridge

end
