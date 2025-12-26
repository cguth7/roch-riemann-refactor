import RrLean.RiemannRochV2.General.WeilDifferential
import RrLean.RiemannRochV2.Adelic.EulerCharacteristic

/-!
# General Curve Infrastructure for Riemann-Roch

This module re-exports the general curve infrastructure using Weil differentials.

## Module Structure

* `WeilDifferential` - Weil differentials as linear functionals on adeles vanishing on K

## Mathematical Background

For a smooth projective curve X over a finite field k:
- Weil differentials ω : A_K → k with ω(K) = 0
- Divisor-constrained differentials Ω(D) with poles bounded by D
- Serre pairing ⟨f, ω⟩ = ω(diag(f))

## Status (Cycle 318)

WeilDifferential.lean contains:
- `WeilDifferential` structure with k-module and K-module actions
- `DivisorDifferentials Ω(D)` submodule
- `serrePairingGeneral` bilinear pairing L(D) × Ω(E) → k

Upcoming:
- Non-degeneracy definitions (Cycle 318)
- HasCanonicalDivisor typeclass (Cycle 318)
- Instantiation for P¹/elliptic (Cycle 319-320)

## The Approach

The Weil differential approach bypasses the P¹-specific sorries:
1. The pairing ⟨f, ω⟩ = ω(diag f) is just evaluation
2. The residue theorem is built into the definition (ω vanishes on K)
3. No need for strong approximation edge cases

## Key References

- Rosen, "Number Theory in Function Fields", Ch. 6
- Stichtenoth, "Algebraic Function Fields", §1.7
-/
