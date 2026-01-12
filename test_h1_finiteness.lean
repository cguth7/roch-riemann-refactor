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

omit [Fintype Fq] [DecidableEq Fq] in
/-- Helper: The constraint set for a single place is open.
    With v fixed (not dependent), Lean can resolve the Valued instance. -/
lemma isOpen_constraint_single_place (v : HeightOneSpectrum Fq[X]) (n : ℤ) :
    IsOpen {a : FiniteAdeleRing Fq[X] (RatFunc Fq) | Valued.v (a.1 v) ≤ WithZero.exp n} := by
  -- The evaluation map at v is continuous
  -- Use RestrictedProduct.continuous_eval which gives continuity of projection
  have heval_cont : Continuous (fun (a : FiniteAdeleRing Fq[X] (RatFunc Fq)) => a.1 v) :=
    RestrictedProduct.continuous_eval v
  -- The ball is open
  have hball_open : IsOpen {x : v.adicCompletion (RatFunc Fq) | Valued.v x ≤ WithZero.exp n} := by
    apply Valued.isOpen_closedBall
    exact WithZero.exp_ne_zero
  -- Preimage of open under continuous is open
  exact hball_open.preimage heval_cont

omit [Fintype Fq] [DecidableEq Fq] in
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
  -- Step 1: Finite support of D
  let T : Set (HeightOneSpectrum Fq[X]) := {v | D v ≠ 0}
  have hT_finite : T.Finite := D.finite_support

  -- Step 2: Key observation - for v ∉ T, D v = 0 so exp(D v) = 1
  have h_outside_T : ∀ v : HeightOneSpectrum Fq[X], v ∉ T → D v = 0 := by
    intro v hv
    simp only [T, Set.mem_setOf_eq, not_not] at hv
    exact hv

  -- Step 3: Rewrite the set as intersection
  -- {∀ v, constraint} = {∀ v ∈ T, constraint} ∩ {∀ v ∉ T, constraint}
  -- Use helper lemma to avoid typeclass resolution issues in set notation
  let constraint (v : HeightOneSpectrum Fq[X]) : Set (FiniteAdeleRing Fq[X] (RatFunc Fq)) :=
    {a | Valued.v (a.1 v) ≤ WithZero.exp (D v)}

  have h_eq : {a : FiniteAdeleRing Fq[X] (RatFunc Fq) | ∀ v, Valued.v (a.1 v) ≤ WithZero.exp (D v)} =
      (⋂ v ∈ T, constraint v) ∩
      {a | ∀ v, v ∉ T → Valued.v (a.1 v) ≤ WithZero.exp (D v)} := by
    ext a
    simp only [constraint, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro h
      exact ⟨fun v _ => h v, fun v _ => h v⟩
    · intro ⟨hT, hnotT⟩ v
      by_cases hv : v ∈ T
      · exact hT v hv
      · exact hnotT v hv
  rw [h_eq]

  -- Step 4: First part is open (finite intersection of open sets)
  have h_T_open : IsOpen (⋂ v ∈ T, constraint v) := by
    apply hT_finite.isOpen_biInter
    intro v _
    exact isOpen_constraint_single_place v (D v)

  -- Step 5: Second part - for v ∉ T, the constraint is v(a v) ≤ 1 = membership in O_v
  -- Use RestrictedProduct.isOpen_forall_imp_mem
  have h_notT_open : IsOpen {a : FiniteAdeleRing Fq[X] (RatFunc Fq) |
      ∀ v, v ∉ T → Valued.v (a.1 v) ≤ WithZero.exp (D v)} := by
    -- For v ∉ T, D v = 0 so exp(D v) = exp 0 = 1
    -- The condition v(a v) ≤ 1 is exactly membership in the integer ring O_v
    -- This is handled by isOpen_forall_imp_mem
    have h_eq' : {a : FiniteAdeleRing Fq[X] (RatFunc Fq) |
        ∀ v, v ∉ T → Valued.v (a.1 v) ≤ WithZero.exp (D v)} =
        {a | ∀ v, v ∉ T → a.1 v ∈ v.adicCompletionIntegers (RatFunc Fq)} := by
      ext a
      simp only [Set.mem_setOf_eq]
      apply forall_congr'
      intro v
      apply imp_congr_right
      intro hv
      -- For v ∉ T, D v = 0, so exp(D v) = exp 0 = 1
      rw [h_outside_T v hv]
      simp only [WithZero.exp_zero]
      -- v(x) ≤ 1 iff x ∈ O_v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [h_eq']
    -- Need: ∀ v, IsOpen (v.adicCompletionIntegers (RatFunc Fq))
    have hAopen : ∀ v : HeightOneSpectrum Fq[X],
        IsOpen (v.adicCompletionIntegers (RatFunc Fq) : Set (v.adicCompletion (RatFunc Fq))) :=
      fun v => Valued.isOpen_valuationSubring _
    exact RestrictedProduct.isOpen_forall_imp_mem hAopen

  -- Step 6: Intersection of open sets is open
  exact h_T_open.inter h_notT_open

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
