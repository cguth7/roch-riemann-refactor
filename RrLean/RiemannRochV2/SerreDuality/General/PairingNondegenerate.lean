/-
# Serre Duality Pairing Non-Degeneracy

This file proves non-degeneracy of the Serre duality pairing and derives
the dimension equality h¹(D) = ℓ(KDiv - D).

## Main Results

* `serreDualityPairing_injective` : The pairing induces an injection H¹(D) → L(KDiv-D)*
* `serre_duality_finrank` : h¹(D) = ℓ(KDiv - D)

## Mathematical Context

The Serre duality pairing φ : H¹(D) × L(KDiv - D) → k is a perfect pairing.
This means the induced map H¹(D) → L(KDiv-D)* is an isomorphism.

Non-degeneracy says: if φ([a], f) = 0 for all f ∈ L(KDiv - D), then [a] = 0.

From the perfect pairing and finite-dimensionality, we get:
  dim H¹(D) = dim L(KDiv - D)

## Status

Cycle 366: Initial axiom-based version with 2 axioms.
Cycle 372: Refactored to derive from TracePairingBridge (0 axioms here).
           Now requires [FiniteDimensional k K] [Algebra.IsSeparable k K].
-/

import RrLean.RiemannRochV2.SerreDuality.General.PairingDescent
import RrLean.RiemannRochV2.SerreDuality.General.TracePairingBridge
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open RiemannRochV2.PairingDescent
open RiemannRochV2.AdelicH1v2
open RiemannRochV2.SerrePairingDescent

namespace RiemannRochV2.PairingNondegenerate

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (k : Type*) [Field k] [Algebra k R] [Algebra k K] [IsScalarTower k R K]
variable [FiniteDimensional k K] [Algebra.IsSeparable k K]

/-! ## Non-Degeneracy Theorems (Cycle 372)

The Serre duality pairing is non-degenerate. This was previously axiomatized,
but is now derived from trace form non-degeneracy via TracePairingBridge.lean.

Non-degeneracy means: if the pairing with a class [a] ∈ H¹(D) vanishes
for all f ∈ L(KDiv - D), then [a] = 0.

Combined with the symmetric statement (existence of witness for nonzero elements),
this gives the perfect pairing property.

**Note**: This file now requires `[FiniteDimensional k K] [Algebra.IsSeparable k K]`
assumptions, which are needed for trace form non-degeneracy.
-/

/-- Non-degeneracy on the left: if φ([a], f) = 0 for all f ∈ L(KDiv - D), then [a] = 0.

**Derived from trace non-degeneracy** (Cycle 372): This follows from the
trace-residue connection established in TracePairingBridge.lean.

The key insight is that trace form non-degeneracy on K implies that the
residue-based Serre pairing is also non-degenerate.
-/
theorem serreDualityPairing_injective (D KDiv : DivisorV2 R) :
    Function.Injective (serreDualityPairing (R := R) (K := K) k D KDiv) :=
  TracePairingBridge.serreDualityPairing_injective_from_trace k D KDiv

/-- Non-degeneracy on the right: for any nonzero f ∈ L(KDiv - D), there exists
[a] ∈ H¹(D) such that φ([a], f) ≠ 0.

**Derived from trace non-degeneracy** (Cycle 372): This follows from the
trace-residue connection established in TracePairingBridge.lean.

This is equivalent to the surjectivity of the transpose pairing.
Combined with left non-degeneracy, this gives the perfect pairing.
-/
theorem serreDualityPairing_right_nondegen (D KDiv : DivisorV2 R)
    (f : RRModuleV2_real R K (KDiv - D)) (hf : f ≠ 0) :
    ∃ h1_class : SpaceModule k R K D, serreDualityPairing k D KDiv h1_class f ≠ 0 :=
  TracePairingBridge.serreDualityPairing_right_nondegen_from_trace k D KDiv f hf

/-! ## Dimension Consequences

From non-degeneracy and finite-dimensionality, we derive the
dimension equality h¹(D) = ℓ(KDiv - D).
-/

/-- The Serre duality pairing gives an injection H¹(D) ↪ L(KDiv - D)*.

Since both spaces are finite-dimensional (over an algebraically closed field),
this gives dim H¹(D) ≤ dim L(KDiv - D)* = dim L(KDiv - D).
-/
theorem serreDualityPairing_ker_eq_bot (D KDiv : DivisorV2 R) :
    LinearMap.ker (serreDualityPairing (R := R) (K := K) k D KDiv) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (serreDualityPairing_injective (R := R) (K := K) k D KDiv)

/-- The finrank of H¹(D) is at most the finrank of L(KDiv - D).

This follows from the injection H¹(D) ↪ L(KDiv - D)* and the fact that
dim(V*) = dim(V) for finite-dimensional V.
-/
theorem h1_finrank_le_ell (D KDiv : DivisorV2 R)
    [Module.Finite k (SpaceModule k R K D)]
    [Module.Finite k (RRModuleV2_real R K (KDiv - D))] :
    Module.finrank k (SpaceModule k R K D) ≤
    Module.finrank k (RRModuleV2_real R K (KDiv - D)) := by
  -- The pairing gives an injection H¹(D) → L(KDiv-D)*
  -- So dim H¹(D) ≤ dim L(KDiv-D)* = dim L(KDiv-D)
  have hinj := serreDualityPairing_injective (R := R) (K := K) k D KDiv
  -- serreDualityPairing : SpaceModule k R K D →ₗ[k] (RRModuleV2_real R K (KDiv - D) →ₗ[k] k)
  -- The codomain is the dual space L(KDiv-D)*
  -- By LinearMap.finrank_le_finrank_of_injective: dim(domain) ≤ dim(codomain)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  -- dim(L(KDiv-D)*) = dim(L(KDiv-D)) for finite-dimensional spaces
  -- Module.finrank k (M →ₗ[k] k) = Module.finrank k M when M is finite-dim
  calc Module.finrank k (SpaceModule k R K D)
      ≤ Module.finrank k (RRModuleV2_real R K (KDiv - D) →ₗ[k] k) := hle
    _ = Module.finrank k (RRModuleV2_real R K (KDiv - D)) :=
        Subspace.dual_finrank_eq (K := k) (V := RRModuleV2_real R K (KDiv - D))

/-! ## Serre Duality Theorem

The main result: h¹(D) = ℓ(KDiv - D).

For this we need the symmetric inequality: ℓ(KDiv - D) ≤ h¹(D).
This follows from right non-degeneracy, which says the transpose pairing
L(KDiv - D) → H¹(D)* is injective.
-/

/-- The transpose pairing: L(KDiv - D) → H¹(D)*.

This sends f to the functional [a] ↦ φ([a], f).
-/
def transposePairing (D KDiv : DivisorV2 R) :
    RRModuleV2_real R K (KDiv - D) →ₗ[k] (SpaceModule k R K D →ₗ[k] k) where
  toFun f := {
    toFun := fun h1_class => serreDualityPairing (R := R) (K := K) k D KDiv h1_class f
    map_add' := fun h1 h2 => by
      rw [map_add, LinearMap.add_apply]
    map_smul' := fun c h1 => by
      rw [map_smul, LinearMap.smul_apply, RingHom.id_apply]
  }
  map_add' := fun f g => by
    apply LinearMap.ext
    intro h1_class
    show serreDualityPairing (R := R) (K := K) k D KDiv h1_class (f + g) = _
    rw [(serreDualityPairing (R := R) (K := K) k D KDiv h1_class).map_add]
    rfl
  map_smul' := fun c f => by
    apply LinearMap.ext
    intro h1_class
    show serreDualityPairing (R := R) (K := K) k D KDiv h1_class (c • f) = _
    rw [(serreDualityPairing (R := R) (K := K) k D KDiv h1_class).map_smul, RingHom.id_apply]
    rfl

/-- Right non-degeneracy implies the transpose pairing is injective.

If f ≠ 0 and the transpose pairing sends f to 0, then φ([a], f) = 0 for all [a],
contradicting right non-degeneracy.
-/
theorem transposePairing_injective (D KDiv : DivisorV2 R) :
    Function.Injective (transposePairing (R := R) (K := K) k D KDiv) := by
  intro f g heq
  by_contra hne
  -- f ≠ g means f - g ≠ 0
  push_neg at hne
  have hfg : f - g ≠ 0 := sub_ne_zero.mpr hne
  -- By right non-degeneracy, there exists [a] with φ([a], f - g) ≠ 0
  obtain ⟨h1_class, hpair⟩ := serreDualityPairing_right_nondegen (R := R) (K := K) k D KDiv (f - g) hfg
  -- But heq says transposePairing f = transposePairing g
  -- So for all h1_class: φ([h1_class], f) = φ([h1_class], g)
  have heq_at : transposePairing (R := R) (K := K) k D KDiv f h1_class =
                transposePairing (R := R) (K := K) k D KDiv g h1_class := by
    rw [heq]
  unfold transposePairing at heq_at
  simp only [LinearMap.coe_mk, AddHom.coe_mk] at heq_at
  -- φ([h1_class], f - g) = φ([h1_class], f) - φ([h1_class], g) = 0
  have hzero : serreDualityPairing (R := R) (K := K) k D KDiv h1_class (f - g) = 0 := by
    rw [(serreDualityPairing (R := R) (K := K) k D KDiv h1_class).map_sub, heq_at, sub_self]
  exact hpair hzero

/-- The finrank of L(KDiv - D) is at most the finrank of H¹(D).

This follows from the injective transpose pairing L(KDiv - D) ↪ H¹(D)*.
-/
theorem ell_finrank_le_h1 (D KDiv : DivisorV2 R)
    [Module.Finite k (SpaceModule k R K D)]
    [Module.Finite k (RRModuleV2_real R K (KDiv - D))] :
    Module.finrank k (RRModuleV2_real R K (KDiv - D)) ≤
    Module.finrank k (SpaceModule k R K D) := by
  have hinj := transposePairing_injective (R := R) (K := K) k D KDiv
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  calc Module.finrank k (RRModuleV2_real R K (KDiv - D))
      ≤ Module.finrank k (SpaceModule k R K D →ₗ[k] k) := hle
    _ = Module.finrank k (SpaceModule k R K D) :=
        Subspace.dual_finrank_eq (K := k) (V := SpaceModule k R K D)

/-! ## Main Theorem: Serre Duality -/

/-- **Serre Duality**: h¹(D) = ℓ(KDiv - D).

The dimension of the first adelic cohomology H¹(D) equals the dimension
of the Riemann-Roch space L(KDiv - D).

This is the key duality theorem that relates cohomology to global sections
and is essential for the Riemann-Roch formula.
-/
theorem serre_duality_finrank (D KDiv : DivisorV2 R)
    [Module.Finite k (SpaceModule k R K D)]
    [Module.Finite k (RRModuleV2_real R K (KDiv - D))] :
    Module.finrank k (SpaceModule k R K D) =
    Module.finrank k (RRModuleV2_real R K (KDiv - D)) :=
  le_antisymm
    (h1_finrank_le_ell k D KDiv)
    (ell_finrank_le_h1 k D KDiv)

/-- Alternative statement using the named h1_finrank function.

Note: h1_finrank k R K D = Module.finrank k (SpaceModule k R K D)
And Module.finrank k (RRModuleV2_real R K (KDiv - D)) is ℓ(KDiv - D).
-/
theorem serre_duality_h1_eq_ell (D KDiv : DivisorV2 R)
    [Module.Finite k (SpaceModule k R K D)]
    [Module.Finite k (RRModuleV2_real R K (KDiv - D))] :
    h1_finrank k R K D = Module.finrank k (RRModuleV2_real R K (KDiv - D)) :=
  serre_duality_finrank k D KDiv

end RiemannRochV2.PairingNondegenerate

/-! ## Summary (Updated Cycle 372)

**File**: `PairingNondegenerate.lean`

**Cycle 366**: Initial axiom-based version with 2 axioms.
**Cycle 372**: Refactored to derive from TracePairingBridge (0 axioms here).

**Theorems** (all derived, no axioms in this file):
- `serreDualityPairing_injective`: Left non-degeneracy (from trace bridge)
- `serreDualityPairing_right_nondegen`: Right non-degeneracy (from trace bridge)
- `serreDualityPairing_ker_eq_bot`: Kernel is trivial
- `h1_finrank_le_ell`: dim H¹(D) ≤ dim L(KDiv - D)
- `transposePairing_injective`: Transpose is injective (from right non-deg)
- `ell_finrank_le_h1`: dim L(KDiv - D) ≤ dim H¹(D)
- `serre_duality_finrank`: **h¹(D) = ℓ(KDiv - D)**
- `serre_duality_h1_eq_ell`: Named version

**Dependencies**:
- Requires `[FiniteDimensional k K] [Algebra.IsSeparable k K]`
- Derives from `TracePairingBridge.serreDualityPairing_injective_from_trace`
- Derives from `TracePairingBridge.serreDualityPairing_right_nondegen_from_trace`

**Axiom hierarchy** (Cycle 372):
- PairingNondegenerate.lean: 0 axioms (all derived)
- TracePairingBridge.lean: 2 axioms (residuePairing_controlled_by_trace, witness_from_trace_nondegen)

**Key insight**: Non-degeneracy of Serre pairing follows from trace form non-degeneracy.
The axioms are now at the trace-residue level rather than the abstract pairing level.
-/

end
