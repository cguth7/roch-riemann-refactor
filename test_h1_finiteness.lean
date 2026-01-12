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
  -- Strategy: Use the direct characterization of openness in restricted products.
  -- For each cofinite S, elements in S-principal satisfy f v ∈ O_v for v ∈ S.
  -- The constraint "∀ v, v(f v) ≤ exp(D v)" becomes finite when restricted to S-principal:
  -- only v ∈ T_S = Sᶜ ∪ {v ∈ S | D v < 0} need explicit checking, and T_S is finite.

  -- Step 1: Open sets at each place
  have hOv_open : ∀ v : HeightOneSpectrum Fq[X],
      IsOpen (v.adicCompletionIntegers (RatFunc Fq) : Set (v.adicCompletion (RatFunc Fq))) :=
    fun v ↦ Valued.isOpen_valuationSubring _

  -- Step 2: Balls are open
  have hBall_open : ∀ v : HeightOneSpectrum Fq[X],
      IsOpen {x : v.adicCompletion (RatFunc Fq) | Valued.v x ≤ WithZero.exp (D v)} := by
    intro v
    apply Valued.isOpen_closedBall
    exact WithZero.exp_ne_zero

  -- Step 3: Finite support of D
  let T : Set (HeightOneSpectrum Fq[X]) := {v | D v ≠ 0}
  have hT_finite : T.Finite := D.finite_support

  -- Step 4: The key decomposition
  -- For v ∉ T: D v = 0, so Ball_v = {x | v(x) ≤ 1} = O_v
  -- The bounded set = {a | ∀ v, a v ∈ Ball_v}
  --                 = {a | (∀ v ∈ T, a v ∈ Ball_v) ∧ (∀ v ∉ T, a v ∈ O_v)}

  -- Step 5: Apply topology characterization
  -- Using that the topology is ⨆ S, coinduced from S-principal.
  -- In S-principal, a v ∈ O_v for v ∈ S, so:
  -- - For v ∈ S ∩ Tᶜ: automatic (D v = 0, Ball_v = O_v)
  -- - For v ∈ S ∩ T with D v ≥ 0: automatic (O_v ⊆ Ball_v)
  -- - For v ∈ S ∩ T with D v < 0: need a v ∈ Ball_v ⊂ O_v
  -- - For v ∈ Sᶜ: need a v ∈ Ball_v
  -- Non-trivial places: T_S = Sᶜ ∪ {v ∈ S | D v < 0} which is finite.

  -- The complete proof is blocked by Lean's typeclass resolution for dependent types.
  -- The mathematical argument is:
  -- 1. Use RestrictedProduct.topologicalSpace_eq_iSup to expand the topology
  -- 2. For each cofinite S, define T_S = Sᶜ ∪ {v | D v < 0} (finite)
  -- 3. Show preimage under inclusion equals {f | ∀ v ∈ T_S, f.1 v ∈ Ball_v}
  -- 4. This is open by isOpen_set_pi + continuous_coe
  --
  -- The formalization fails because Lean can't resolve `Valued` instances on
  -- dependent function types in RestrictedProduct. This is a Lean limitation,
  -- not a mathematical gap.
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
