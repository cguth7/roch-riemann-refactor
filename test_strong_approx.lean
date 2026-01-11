/-
# Cycle 347: P¹ Strong Approximation Proof Structure

This file reduces the P¹ StrongApprox sorry to a single topology lemma.

## Goal
Prove: DenseRange (FiniteAdeleRing.algebraMap (Polynomial Fq) (RatFunc Fq))

## What We Have
- `strong_approximation_ratfunc` (PROVED in RatFuncPairing.lean):
  For any a ∈ FiniteAdeleRing and D, ∃ k with a - diag(k) ∈ boundedSubmodule D
- `globalPlusBoundedSubmodule_eq_top` (PROVED): K + A(D) = FiniteAdeleRing for ALL D

## Proof Structure (This file)
1. Given neighborhood U of a, show { x | a - x ∈ U } ∈ nhds 0 ✓
2. Find D such that boundedSubmodule D ⊆ { x | a - x ∈ U } (KEY LEMMA - needs proof)
3. Use strong_approximation_ratfunc to get k with a - diag(k) ∈ boundedSubmodule D ✓
4. Conclude diag(k) ∈ U ✓

## Remaining Work
The only remaining sorry is `exists_boundedSubmodule_subset_nhds`, which states:
"For any neighborhood U of 0 in FiniteAdeleRing, there exists D such that
boundedSubmodule D ⊆ U."

This requires proving that bounded submodules form a neighborhood basis of 0
in the restricted product topology. The mathematical argument is clear:
- Basic opens in RestrictedProduct: { a | a_v ∈ U_v (v ∈ S), a_v ∈ O_v (v ∉ S) }
- Valuation balls { x | v(x) ≤ exp(n) } are open and form a neighborhood basis at 0
- For any basic open U ∋ 0, we can choose D such that boundedSubmodule D ⊆ U

The formalization requires connecting Mathlib's RestrictedProduct topology API
with our boundedSubmodule definition.

## Impact
Once `exists_boundedSubmodule_subset_nhds` is proved, the P¹ StrongApprox sorry is filled.
This is NOT on the critical path for elliptic RR but shows the approach works.
-/

import RrLean.RiemannRochV2.SerreDuality.P1Specific.RatFuncPairing
import RrLean.RiemannRochV2.Adelic.StrongApproximation
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open RiemannRochV2 AdelicH1v2
open scoped Polynomial

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq Fq]

-- The key algebraic result (already proved in RatFuncPairing.lean)
#check @strong_approximation_ratfunc

-- KEY TOPOLOGY LEMMA (needs proof):
-- Bounded submodules can be made to fit inside any neighborhood of 0
-- This is the main gap in proving StrongApprox
lemma exists_boundedSubmodule_subset_nhds
    (U : Set (FiniteAdeleRing (Polynomial Fq) (RatFunc Fq))) (hU : U ∈ nhds 0) :
    ∃ D : DivisorV2 (Polynomial Fq),
      (boundedSubmodule Fq (Polynomial Fq) (RatFunc Fq) D : Set _) ⊆ U := by
  -- The proof needs:
  -- 1. Valuation balls { x | v(x) ≤ c } are open in adicCompletion K v
  -- 2. For c < 1, these balls are subsets of the integer ring O_v
  -- 3. The restricted product topology has basis: { a | a_v ∈ U_v (v ∈ S), a_v ∈ O_v (v ∉ S) }
  -- 4. boundedSubmodule D with negative D(v) gives small neighborhoods
  --
  -- Mathematical argument:
  -- Any neighborhood U of 0 contains a basic open B = { a | a_v ∈ B_v (v ∈ S), a_v ∈ O_v (v ∉ S) }
  -- where each B_v is open in K_v and contains 0.
  -- Since valuation balls form a neighborhood basis in K_v, each B_v contains { x | v(x) ≤ exp(n_v) }
  -- for some n_v ≤ 0 (negative to be inside O_v).
  -- Define D(v) = n_v for v ∈ S, D(v) = 0 for v ∉ S.
  -- Then boundedSubmodule D ⊆ B ⊆ U.
  sorry

-- Main theorem: P¹ has dense range of algebraMap
-- Assuming the topology lemma above, this proof works
theorem p1_denseRange_algebraMap :
    DenseRange (FiniteAdeleRing.algebraMap (Polynomial Fq) (RatFunc Fq)) := by
  rw [DenseRange, Dense]
  intro a
  rw [mem_closure_iff_nhds]
  intro U hU

  -- Step 1: { x | a - x ∈ U } is a neighborhood of 0
  -- f(x) = a - x satisfies f(0) = a, so f⁻¹(U) ∈ nhds 0
  let f : FiniteAdeleRing (Polynomial Fq) (RatFunc Fq) →
          FiniteAdeleRing (Polynomial Fq) (RatFunc Fq) := fun x => a - x
  have hf_cont : Continuous f := continuous_const.sub continuous_id
  have hf_zero : f 0 = a := sub_zero a
  have h_preimage_nhds : f ⁻¹' U ∈ nhds (0 : FiniteAdeleRing (Polynomial Fq) (RatFunc Fq)) := by
    -- ContinuousAt f 0 means: nhds (f 0) ≤ map f (nhds 0)
    -- Since f 0 = a and U ∈ nhds a, we have f ⁻¹' U ∈ nhds 0
    have h := hf_cont.continuousAt (x := 0)
    have h' : U ∈ nhds (f 0) := by rw [hf_zero]; exact hU
    exact h.preimage_mem_nhds h'

  -- Step 2: Find D such that boundedSubmodule D ⊆ { x | a - x ∈ U }
  obtain ⟨D, hD⟩ := exists_boundedSubmodule_subset_nhds (f ⁻¹' U) h_preimage_nhds

  -- Step 3: Use strong approximation to get k with a - diag(k) ∈ boundedSubmodule D
  obtain ⟨k, hk⟩ := strong_approximation_ratfunc a D

  -- Step 4: Show that range(algebraMap) ∩ U is nonempty
  -- diagonalK = FiniteAdeleRing.algebraMap by definition
  have heq_diag : diagonalK (Polynomial Fq) (RatFunc Fq) k =
                  FiniteAdeleRing.algebraMap (Polynomial Fq) (RatFunc Fq) k := rfl

  -- We have: a - diagonalK k ∈ boundedSubmodule D ⊆ f⁻¹(U) = { x | a - x ∈ U }
  have h1 : a - diagonalK (Polynomial Fq) (RatFunc Fq) k ∈ f ⁻¹' U := hD hk
  simp only [Set.mem_preimage] at h1
  -- h1 : f (a - diagonalK k) ∈ U, i.e., a - (a - diagonalK k) ∈ U
  -- Simplify: a - (a - diagonalK k) = diagonalK k
  simp only [f, sub_sub_cancel] at h1
  -- h1 : diagonalK k ∈ U

  -- Now show the result
  rw [heq_diag] at h1
  -- The goal is: (U ∩ Set.range algebraMap).Nonempty
  refine ⟨FiniteAdeleRing.algebraMap (Polynomial Fq) (RatFunc Fq) k, h1, ⟨k, rfl⟩⟩
