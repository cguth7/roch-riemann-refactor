import RrLean.RiemannRochV2.Definitions.Projective
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Full Riemann-Roch via Axiomatic Approach (Track A)

This module provides the full Riemann-Roch theorem using axiomatized data for
the canonical divisor K and genus g.

## Track A: Axiomatize First

We define a `FullRRData` typeclass that extends `ProperCurve` with:
- `canonical : DivisorV2 R` — the canonical divisor K
- `genus : ℕ` — the genus g
- `deg_canonical` — deg(K) = 2g - 2
- `serre_duality_eq` — the key axiom relating ℓ(D) and ℓ(K-D)

The full Riemann-Roch theorem then follows algebraically from these axioms.

## Track B: Discharge Axioms (Future)

In future cycles, we will instantiate `FullRRData` by:
- Defining `canonical` via `differentIdeal` from Mathlib
- Proving `serre_duality_eq` via `Submodule.traceDual`

## Main Definitions

* `FullRRData k R K` — Typeclass packaging canonical divisor and genus
* `riemann_roch_full` — The full RR theorem: ℓ(D) - ℓ(K-D) = deg(D) + 1 - g

## References

* Mathlib: `RingTheory.DedekindDomain.Different` for `differentIdeal`, `traceDual`
* Liu "Algebraic Geometry and Arithmetic Curves" Chapter 7
-/

namespace RiemannRochV2

open IsDedekindDomain

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable [Algebra k R] [Algebra k K] [IsScalarTower k R K]

/-! ## Full Riemann-Roch Data

The typeclass `FullRRData` packages the canonical divisor and genus,
along with the key axioms that make the full RR theorem provable.
-/

/-- Full Riemann-Roch data for a proper curve over k.

This typeclass extends `ProperCurve` (which gives ℓ(0) = 1) with:
- `canonical`: The canonical divisor K (corresponds to global differentials)
- `genus`: The genus g of the curve
- `deg_canonical`: deg(K) = 2g - 2 (standard formula)
- `serre_duality_eq`: The full RR equation as an axiom

Track B will instantiate this by proving `serre_duality_eq` using
the trace dual machinery from `Mathlib.RingTheory.DedekindDomain.Different`.
-/
class FullRRData extends ProperCurve k R K where
  /-- The canonical divisor K (arithmetic analog of global differentials) -/
  canonical : DivisorV2 R
  /-- The genus g ≥ 0 -/
  genus : ℕ
  /-- The canonical divisor has degree 2g - 2 -/
  deg_canonical : canonical.deg = 2 * (genus : ℤ) - 2
  /-- The full Riemann-Roch equation (core axiom).

  This is the key axiom that encapsulates Serre duality.
  Mathematically: ℓ(D) - h¹(D) = deg(D) + 1 - g, where h¹(D) = ℓ(K-D) by duality. -/
  serre_duality_eq : ∀ D : DivisorV2 R,
    (ell_proj k R K D : ℤ) - ell_proj k R K (canonical - D) = D.deg + 1 - genus
  /-- Divisors of negative degree have no sections.

  This is the fundamental vanishing theorem. The classical proof uses:
  - If f ∈ L(D) is nonzero, then div(f) + D is effective
  - deg(div(f) + D) = 0 + deg(D) = deg(D) (since principal divisors have degree 0)
  - But effective divisors have degree ≥ 0, contradiction if deg(D) < 0

  We axiomatize this rather than proving it, since the proof requires principal
  divisor theory (specifically, that deg(div(f)) = 0 for all f ∈ K×). -/
  ell_zero_of_neg_deg : ∀ D : DivisorV2 R, D.deg < 0 → ell_proj k R K D = 0

/-! ## The Full Riemann-Roch Theorem

The main theorem is essentially a restatement of the axiom `serre_duality_eq`,
but packaged as a standalone theorem for external use.
-/

/-- The Full Riemann-Roch Theorem.

For any divisor D on a proper curve:
  ℓ(D) - ℓ(K - D) = deg(D) + 1 - g

where K is the canonical divisor and g is the genus.

This is the central result of the theory. The proof is immediate from
the `serre_duality_eq` axiom of `FullRRData`, but we state it as a
standalone theorem for clarity and modularity.
-/
theorem riemann_roch_full [frr : FullRRData k R K] {D : DivisorV2 R} :
    (ell_proj k R K D : ℤ) - ell_proj k R K (frr.canonical - D) = D.deg + 1 - frr.genus :=
  frr.serre_duality_eq D

/-! ## Corollaries

Standard consequences of the full Riemann-Roch theorem.
-/

section Corollaries

variable [frr : FullRRData k R K]

/-- Riemann-Roch at D = 0: ℓ(0) - ℓ(K) = 1 - g.
Combined with ℓ(0) = 1, we get ℓ(K) = g. -/
lemma ell_canonical_eq_genus
    [Module.Finite k (RRSpace_proj k R K frr.canonical)] :
    ell_proj k R K frr.canonical = frr.genus := by
  have h_rr := riemann_roch_full k R K (D := 0)
  simp only [DivisorV2.deg_zero, sub_zero] at h_rr
  have h_zero : ell_proj k R K 0 = 1 := frr.ell_zero_eq_one
  omega

/-- Riemann-Roch at D = K: ℓ(K) - ℓ(0) = deg(K) + 1 - g = 2g - 2 + 1 - g = g - 1.
This is consistent with ℓ(K) = g and ℓ(0) = 1. -/
lemma riemann_roch_at_canonical
    [Module.Finite k (RRSpace_proj k R K frr.canonical)]
    [Module.Finite k (RRSpace_proj k R K 0)] :
    (ell_proj k R K frr.canonical : ℤ) - ell_proj k R K 0 = frr.genus - 1 := by
  have h_rr := riemann_roch_full k R K (D := frr.canonical)
  simp only [sub_self] at h_rr
  have h_zero : ell_proj k R K 0 = 1 := frr.ell_zero_eq_one
  have h_deg : frr.canonical.deg = 2 * (frr.genus : ℤ) - 2 := frr.deg_canonical
  omega

/-- Lower bound from RR: ℓ(D) ≥ deg(D) + 1 - g (when ℓ(K-D) = 0).

This is equivalent to the Riemann inequality when deg(D) > 2g - 2,
since then ℓ(K-D) = 0 (no effective divisor in the class K-D). -/
lemma ell_ge_of_ell_complement_zero {D : DivisorV2 R}
    (h_zero : ell_proj k R K (frr.canonical - D) = 0) :
    (ell_proj k R K D : ℤ) ≥ D.deg + 1 - frr.genus := by
  have h_rr := riemann_roch_full k R K (D := D)
  omega

/-- The degree bound on the canonical class complement.
If deg(D) > 2g - 2, then deg(K - D) < 0, so ℓ(K - D) = 0.

This now follows directly from the `ell_zero_of_neg_deg` axiom. -/
lemma ell_canonical_minus_eq_zero_of_large_deg {D : DivisorV2 R}
    (h_large : D.deg > 2 * (frr.genus : ℤ) - 2) :
    ell_proj k R K (frr.canonical - D) = 0 := by
  -- deg(K - D) = deg(K) - deg(D) = (2g-2) - deg(D) < 0
  apply frr.ell_zero_of_neg_deg
  -- Use sub_eq_add_neg and deg_add, deg_neg
  rw [sub_eq_add_neg, DivisorV2.deg_add, DivisorV2.deg_neg, frr.deg_canonical]
  omega

end Corollaries

/-! ## Future Work: Track B Instantiation

To discharge the `serre_duality_eq` axiom, we need to:

1. **Define canonical via Different ideal**:
   The canonical divisor K corresponds to the "Different ideal" from
   `Mathlib.RingTheory.DedekindDomain.Different`:
   ```
   def differentIdeal : Ideal B :=
     (1 / Submodule.traceDual A K 1).comap (algebraMap B L)
   ```

2. **Prove duality via trace pairing**:
   The dual L(K-D)* ≅ (some cohomology) using `Submodule.traceDual`:
   ```
   def Submodule.traceDual (I : Submodule B L) : Submodule B L :=
     -- x ∈ Iᵛ ↔ ∀ y ∈ I, Tr(x * y) ∈ A
   ```

3. **Instantiate genus**:
   Define g = ℓ(K) or via arithmetic invariants.

This will be done in Track B (Cycles 81+).
-/

end RiemannRochV2
