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

/-- The bounded set is open in the RestrictedProduct type directly.

The key insight is that for elements of the RestrictedProduct (which are integral
at cofinitely many places), the condition "Valued.v (a v) ≤ exp(D v)" is:
- Automatically satisfied at places where D v = 0 (because exp(0) = 1 and a v is integral)
- An open condition at finitely many places in supp(D)

This makes the infinite intersection effectively a finite one.
-/
theorem isOpen_bounded_finiteAdeles (D : DivisorV2 Fq[X]) :
    IsOpen {a : FiniteAdeleRing Fq[X] (RatFunc Fq) |
      ∀ v, Valued.v (a.1 v) ≤ WithZero.exp (D v)} := by
  -- The bounded set can be written as:
  -- {a | ∀ v ∈ T, a.1 v ∈ Ball_v} ∩ {a | ∀ v ∉ T, a.1 v ∈ O_v}
  -- where T = supp(D) is finite, Ball_v = {x | v(x) ≤ exp(D v)}, and O_v is the valuation ring.

  -- For v ∉ T, D v = 0, so Ball_v = O_v.
  -- For v ∈ T with D v ≥ 0, Ball_v ⊇ O_v.
  -- For v ∈ T with D v < 0, Ball_v ⊊ O_v.

  -- Key observation: The restricted product topology has the property that
  -- a set is open if for each cofinite S, the S-principal elements satisfy the constraint
  -- via a finite intersection.

  -- We use isOpen_forall_imp_mem which handles the case where constraints apply
  -- only at finitely many places (where p is true).

  let T : Set (HeightOneSpectrum Fq[X]) := {v | D v ≠ 0}
  have hT_finite : T.Finite := D.finite_support

  -- The bounded set equals: (∀ v ∈ T, a.1 v ∈ Ball_v) ∧ (∀ v ∉ T, a.1 v ∈ O_v)
  -- For v ∉ T, D v = 0, so exp(D v) = 1 and Ball_v = O_v.
  -- So the constraint "∀ v ∉ T, a.1 v ∈ O_v" is equivalent to "∀ v ∉ T, v(a.1 v) ≤ exp(D v)".

  -- Each constraint "v(a.1 v) ≤ exp(D v)" is:
  -- - For v ∉ T: same as "a.1 v ∈ O_v" (automatic for S-principal when v ∈ S)
  -- - For v ∈ T: an explicit open constraint

  -- Strategy: show the set equals {a | ∀ v, v ∈ T → a.1 v ∈ Ball_v} ∩ {a | ∀ v, a.1 v ∈ O_v}
  -- Wait, that's too strong. Let me just use the topology directly.

  -- The topology is characterized by: open iff open in each S-principal for cofinite S.
  -- In each S-principal, elements satisfy a.1 v ∈ O_v for v ∈ S.
  -- For v ∈ S with D v ≥ 0: O_v ⊆ Ball_v, constraint automatic.
  -- For v ∈ S with D v < 0 or v ∉ S: need explicit constraint.
  -- The set of non-trivial places T_S = Sᶜ ∪ (S ∩ {D < 0}) is finite.

  -- Since proving this directly is complex, we use a strategic sorry with proof sketch.
  -- The full proof requires carefully handling the RestrictedProduct.topologicalSpace_eq_iSup
  -- and showing that finite product of opens is open in the S-principal topology.
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
