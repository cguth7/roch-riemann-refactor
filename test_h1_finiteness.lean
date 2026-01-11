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
open RiemannRochV2.AdelicTopology FunctionField
open scoped Polynomial WithZero

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

/-- The finite part constraint set is open in FiniteAdeleRing.

The key insight is that for elements of the RestrictedProduct (which are integral
at cofinitely many places), the condition "Valued.v (a v) ≤ exp(D v)" is:
- Automatically satisfied at places where D v = 0 (because exp(0) = 1 and a v is integral)
- An open condition at finitely many places in supp(D)

This makes the infinite intersection effectively a finite one.
-/
theorem isOpen_bounded_finiteAdeles (D : DivisorV2 Fq[X]) :
    IsOpen {a : FiniteAdeleRing Fq[X] (RatFunc Fq) |
      ∀ v, Valued.v (a.1 v) ≤ WithZero.exp (D v)} := by
  /-
  Proof strategy:
  1. The topology on FiniteAdeleRing is ⨆ S (cofinite), coinduced from S-principal product
  2. By isOpen_iSup_iff, we need to show openness in each coinduced topology
  3. By isOpen_coinduced, we need the preimage under inclusion to be open
  4. Key insight: in the S-principal product, elements satisfy f v ∈ O_v for v ∈ S
  5. When D v ≥ 0, Ball_v ⊇ O_v, so the condition is automatic for v ∈ S with D v ≥ 0
  6. Only for v ∈ T := (S ∩ {D < 0}) ∪ Sᶜ is the condition non-trivial, and T is finite!
  7. Use isOpen_set_pi on the finite set T

  The mathematical argument is clear:
  - For cofinite S, elements of S-principal satisfy f_v ∈ O_v for v ∈ S
  - For v ∈ S with D_v ≥ 0, Ball_v ⊇ O_v, so f_v ∈ Ball_v is automatic
  - For v ∈ S with D_v < 0 or v ∉ S, we need an explicit check
  - Since supp(D) is finite, {D < 0} is finite
  - So T = (S ∩ {D < 0}) ∪ Sᶜ is finite
  - The preimage is {f | ∀ v ∈ T, f_v ∈ Ball_v} ∩ S-principal
  - This is open by isOpen_set_pi

  The formalization requires careful handling of the RestrictedProduct API,
  which involves supremum topologies and coinduced topologies.
  -/
  sorry

omit [Fintype Fq] [DecidableEq Fq] in
/-- The infinity part constraint set is open in FqtInfty. -/
theorem isOpen_bounded_infty (n : ℤ) :
    IsOpen { x : FqtInfty Fq | Valued.v x ≤ WithZero.exp n } := by
  have h_exp_ne : (WithZero.exp n : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  apply Valued.isOpen_closedBall
  exact h_exp_ne

theorem boundedSubmodule_full_isOpen (D : ExtendedDivisor (Polynomial Fq)) :
    IsOpen (boundedSubmodule_full Fq D : Set (FqFullAdeleRing Fq)) := by
  -- The bounded submodule is:
  -- { a | (∀ v, v(a_v) ≤ exp(D.finite(v))) ∧ (|a_∞|_∞ ≤ exp(D.inftyCoeff)) }
  --
  -- Step 1: Rewrite as product of two sets
  have h_eq : (boundedSubmodule_full Fq D : Set (FqFullAdeleRing Fq)) =
      { a : FiniteAdeleRing Fq[X] (RatFunc Fq) |
          ∀ v, Valued.v (a.1 v) ≤ WithZero.exp (D.finite v) } ×ˢ
      { x : FqtInfty Fq | Valued.v x ≤ WithZero.exp D.inftyCoeff } := by
    ext ⟨a_fin, a_infty⟩
    constructor
    · intro h
      constructor
      · intro v
        exact h.1 v
      · exact h.2
    · intro ⟨hfin, hinfty⟩
      constructor
      · intro v
        exact hfin v
      · exact hinfty
  rw [h_eq]

  -- Step 2: Product of open sets is open
  exact (isOpen_bounded_finiteAdeles D.finite).prod (isOpen_bounded_infty D.inftyCoeff)

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
