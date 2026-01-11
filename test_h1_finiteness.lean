/-
# Cycle 350: H¹(D) Finiteness via Compactness - Proof Strategy

Goal: Prove Module.Finite for SpaceModule_full when deg(D) < -1

## Key Insight

For deg(D) < -1, the quotient H¹(D) = FullAdeleRing / (K + A_K(D)) is:
1. Covered by the compact set integralFullAdeles (fundamental domain property)
2. Has discrete topology (because A_K(D) is open)
3. Therefore is finite, hence Module.Finite

## Strategy

1. **boundedSubmodule_full D is open** in FqFullAdeleRing
   - Each v-component ball {x : v(x) ≤ exp(n)} is open in adicCompletion
   - The infinity component ball is open by isOpen_ball_le_one_FqtInfty
   - Product of open sets is open

2. **globalPlusBoundedSubmodule_full D is open**
   - K is closed (discrete), A_K(D) is open
   - K + A_K(D) = ⋃_{k ∈ K} (k + A_K(D)) is union of opens, hence open

3. **H¹(D) has discrete topology**
   - Quotient by open subgroup is discrete

4. **integralFullAdeles maps onto H¹(D)**
   - By exists_translate_in_integralFullAdeles (fundamental domain)

5. **Compact + discrete = finite**
   - Continuous image of compact is compact
   - Compact discrete space is finite

6. **Finite Fq-vector space is Module.Finite**
   - Standard fact

## What's Already Proved

- `isCompact_integralFullAdeles` ✅ (FullAdelesCompact.lean)
- `exists_translate_in_integralFullAdeles` ✅ (fundamental domain)
- `fq_discrete_in_fullAdeles` ✅ (K is discrete)
- `fq_closed_in_fullAdeles` ✅ (K is closed)
- `isOpen_ball_le_one_FqtInfty` ✅ (infinity ball is open)
- `Valued.isOpen_closedBall` ✅ (finite place balls are open)

## Key Gap: Connecting RestrictedProduct Topology

The main missing piece is showing that boundedSubmodule_full is open in the
RestrictedProduct topology. This requires:

1. Showing that for D.finite with finite support S:
   - For v ∈ S: the constraint v(a_v) ≤ exp(D(v)) defines an open set
   - For v ∉ S: the constraint v(a_v) ≤ 1 is the integer ring (already open)
   - The finite intersection over S gives an open set in restricted product

2. The infinity constraint |a_∞|_∞ ≤ exp(D.inftyCoeff) is open in FqtInfty

3. Product of open sets in FqFullAdeleRing = (RestrictedProduct × FqtInfty) is open

## Alternative Approach: Direct Finiteness

Instead of topological argument, we could try:
- For deg(D) < -1, H¹(D) ≅ L(K-D)* (Serre duality)
- L(K-D) is finite-dimensional by ell_finite
- Dual of finite-dimensional is finite-dimensional

But this requires the residue pairing construction, which is blocked
(Cycle 349 finding: residues can't be computed on completion elements).

## Recommended Next Step

Complete the topological infrastructure:
1. Prove `boundedSubmodule_full_isOpen` using RestrictedProduct API
2. This requires `Mathlib.Topology.Algebra.RestrictedProduct` lemmas about
   when a subset of the restricted product is open
-/

import RrLean.RiemannRochV2.SerreDuality.General.AdelicH1Full
import RrLean.RiemannRochV2.Adelic.FullAdelesCompact

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open RiemannRochV2 RiemannRochV2.FullAdeles RiemannRochV2.AdelicH1v2
open RiemannRochV2.AdelicTopology
open scoped Polynomial

noncomputable section

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-! ## Core Lemma: Quotient Covered by Fundamental Domain -/

/-- Every element of H¹(D) has a representative in integralFullAdeles. -/
theorem integralFullAdeles_covers_h1 (D : ExtendedDivisor (Polynomial Fq)) :
    ∀ x : SpaceModule_full Fq D, ∃ a ∈ integralFullAdeles Fq,
      Submodule.Quotient.mk a = x := by
  intro x
  -- Get any representative a
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  -- Use fundamental domain property
  obtain ⟨k, hk⟩ := exists_translate_in_integralFullAdeles Fq a
  -- a - diag(k) ∈ integralFullAdeles and represents the same class
  use a - fqFullDiagonalEmbedding Fq k, hk
  -- diag(k) ∈ globalSubmodule_full ⊆ globalPlusBoundedSubmodule_full
  symm
  rw [Submodule.Quotient.eq]
  -- Need: a - (a - diag(k)) ∈ globalPlusBoundedSubmodule_full
  simp only [sub_sub_cancel]
  apply Submodule.mem_sup_left
  exact ⟨k, rfl⟩

/-! ## Key Topology Lemma (requires RestrictedProduct API) -/

/-- boundedSubmodule_full is open in FqFullAdeleRing.

This is the key lemma connecting valuations to topology.
The proof requires:
1. Each valuation ball is open in adicCompletion
2. The product topology on FqFullAdeleRing = RestrictedProduct × FqtInfty
3. Finite intersection of open constraints gives open set
-/
theorem boundedSubmodule_full_isOpen (D : ExtendedDivisor (Polynomial Fq)) :
    IsOpen (boundedSubmodule_full Fq D : Set (FqFullAdeleRing Fq)) := by
  -- The bounded submodule is:
  -- { a | (∀ v, v(a_v) ≤ exp(D.finite(v))) ∧ (|a_∞|_∞ ≤ exp(D.inftyCoeff)) }
  --
  -- In the product topology (RestrictedProduct × FqtInfty):
  -- - The infinity constraint defines an open set in FqtInfty (by isOpen_ball_le_one_FqtInfty)
  -- - The finite part constraint defines an open set in RestrictedProduct:
  --   * For v ∉ supp(D.finite): the constraint is just O_v (the integer ring)
  --   * For v ∈ supp(D.finite): valuation balls are open (Valued.isOpen_closedBall)
  --   * Finite intersection is open
  --
  -- Technical gap: need Mathlib API for RestrictedProduct topology
  sorry

/-! ## Main Strategy Summary

When `boundedSubmodule_full_isOpen` is proved:

1. globalPlusBoundedSubmodule_full is open (union of translates of open set by K)
2. H¹(D) = FqFullAdeleRing / (K + A_K(D)) has discrete topology
3. integralFullAdeles maps surjectively onto H¹(D) (fundamental domain)
4. The image is compact (continuous image of compact)
5. Compact + discrete = finite
6. Therefore H¹(D) is finite-dimensional

This fills the sorry at Abstract.lean:299 for deg(D) < -1.
-/

end
