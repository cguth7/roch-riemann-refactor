import RrLean.RiemannRochV2.Support.TraceDualityProof

/-!
# Adelic Cohomology for Riemann-Roch (Track B)

This module defines H¹(D) = A_K / (K + A_K(D)) using a simplified adelic model.

## Main Definitions

* `AdelicH1.globalField` : K embedded diagonally in functions HeightOneSpectrum R → K
* `AdelicH1.adelicSubspace` : Functions satisfying v(f_v) ≥ -D(v) at each place
* `AdelicH1.Space` : H¹(D) = quotient by (K + A_K(D))
* `AdelicH1.h1` : dim_k H¹(D)

## Mathematical Background

The adelic Riemann-Roch approach:
- h⁰(D) = ℓ(D) = dim_k L(D)
- h¹(D) = dim_k (A_K / (K + A_K(D)))
- Riemann-Roch: h⁰(D) - h¹(D) = deg(D) + 1 - g
- Serre duality: h¹(D) = h⁰(K - D) = ℓ(K - D)

## Status

Cycle 85: Established basic structure with 2 sorries for valuation properties.
Next steps: Prove the valuation sorries using Mathlib's valuation API.

## References

* Liu "Algebraic Geometry and Arithmetic Curves" Chapter 7
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Algebra k R]
variable (K : Type*) [Field K] [Algebra k K] [Algebra R K] [IsFractionRing R K]
variable [IsScalarTower k R K]

namespace AdelicH1

/-! ## Global Field Embedding

K embeds diagonally into the space of functions HeightOneSpectrum R → K
via the map f ↦ (f, f, f, ...).
-/

/-- The subspace of global elements: K embedded diagonally as constant functions. -/
def globalField : Submodule k (HeightOneSpectrum R → K) where
  carrier := { f | ∃ (x : K), f = fun _ => x }
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    use x + y
    ext v
    simp only [Pi.add_apply]
  zero_mem' := ⟨0, by ext v; simp only [Pi.zero_apply]⟩
  smul_mem' := by
    rintro c _ ⟨x, rfl⟩
    use c • x
    ext v
    simp only [Pi.smul_apply]

/-! ## Adelic Subspace A_K(D)

A_K(D) consists of "adeles" satisfying the valuation bound v(f_v) ≥ -D(v) at each place.
This is the local analog of L(D) = {f ∈ K : v(f) ≥ -D(v) for all v}.
-/

/-- The adelic subspace for divisor D: functions with v(f_v) ≤ exp(D(v)) at each place.

This matches the L(D) definition: v.valuation K f ≤ WithZero.exp (D v)
meaning poles at v are bounded by D(v). -/
def adelicSubspace (D : DivisorV2 R) : Submodule k (HeightOneSpectrum R → K) where
  carrier := { f | ∀ v, f v = 0 ∨ v.valuation K (f v) ≤ WithZero.exp (D v) }
  add_mem' := by
    intro a b ha hb v
    -- Need: (a+b)_v = 0 ∨ v((a+b)_v) ≤ exp(D(v))
    -- Uses ultrametric: v(a+b) ≤ max(v(a), v(b)) ≤ exp(D(v))
    by_cases h : (a + b) v = 0
    · left; exact h
    · right
      -- Get bounds for a v and b v from hypotheses
      have hav : v.valuation K (a v) ≤ WithZero.exp (D v) := by
        cases ha v with
        | inl h => simp only [h, Valuation.map_zero]; exact WithZero.zero_le _
        | inr h => exact h
      have hbv : v.valuation K (b v) ≤ WithZero.exp (D v) := by
        cases hb v with
        | inl h => simp only [h, Valuation.map_zero]; exact WithZero.zero_le _
        | inr h => exact h
      -- Ultrametric inequality + max_le
      calc v.valuation K ((a + b) v)
          = v.valuation K (a v + b v) := by rfl
        _ ≤ max (v.valuation K (a v)) (v.valuation K (b v)) :=
            Valuation.map_add_le_max' (v.valuation K) (a v) (b v)
        _ ≤ WithZero.exp (D v) := max_le hav hbv
  zero_mem' := by
    intro v
    left
    rfl
  smul_mem' := by
    intro c x hx v
    -- Need: c • x v = 0 ∨ v(c • x v) ≤ exp(D(v))
    -- Strategy: c • x v = algebraMap k K c * (x v)
    -- For c ∈ k, v(algebraMap k K c) ≤ 1 (constants have no poles)
    -- So v(c • x) = v(c) * v(x) ≤ v(x) ≤ exp(D(v))
    by_cases h : c • x v = 0
    · left; exact h
    · right
      -- c • (x v) = algebraMap k K c * (x v)
      simp only [Pi.smul_apply, Algebra.smul_def]
      -- Use multiplicativity of valuation
      rw [Valuation.map_mul]
      -- Key: algebraMap k K c = algebraMap R K (algebraMap k R c) by IsScalarTower
      have hc : v.valuation K (algebraMap k K c) ≤ 1 := by
        rw [IsScalarTower.algebraMap_apply k R K]
        exact HeightOneSpectrum.valuation_le_one v (algebraMap k R c)
      -- Get bound on x v
      have hxv : v.valuation K (x v) ≤ WithZero.exp (D v) := by
        cases hx v with
        | inl h' => simp only [h', Valuation.map_zero]; exact WithZero.zero_le _
        | inr h' => exact h'
      -- Combine: v(c * x) = v(c) * v(x) ≤ 1 * exp(D v)
      calc v.valuation K (algebraMap k K c) * v.valuation K (x v)
          ≤ 1 * WithZero.exp (D v) := mul_le_mul' hc hxv
        _ = WithZero.exp (D v) := one_mul _

/-! ## H¹(D) as Quotient

H¹(D) := A_K / (K + A_K(D))

where A_K is modeled as all functions HeightOneSpectrum R → K (simplified from
the true restricted product, but sufficient for dimension counting).
-/

/-- The sum K + A_K(D) as a submodule. -/
def adelicSum (D : DivisorV2 R) : Submodule k (HeightOneSpectrum R → K) :=
  globalField k R K + adelicSubspace k R K D

/-- H¹(D) = A_K / (K + A_K(D)), the first adelic cohomology group.
Using `abbrev` so that instances on the quotient are automatically available. -/
abbrev Space (D : DivisorV2 R) : Type _ :=
  (HeightOneSpectrum R → K) ⧸ (adelicSum k R K D)

/-- The quotient map from functions to H¹(D). -/
def quotientMap (D : DivisorV2 R) :
    (HeightOneSpectrum R → K) →ₗ[k] Space k R K D :=
  Submodule.mkQ (adelicSum k R K D)

/-- The dimension h¹(D) = dim_k H¹(D). -/
def h1 (D : DivisorV2 R) : Cardinal :=
  Module.rank k (Space k R K D)

/-- When H¹(D) is finite-dimensional, h¹(D) as a natural number. -/
def h1_finrank (D : DivisorV2 R) [Module.Finite k (Space k R K D)] : ℕ :=
  Module.finrank k (Space k R K D)

/-! ## Key Properties (TODO)

The main results needed to complete Track B:

1. **L(D) ⊆ A_K(D)**: Elements of L(D) satisfy the valuation bounds at each place.
   This embeds L(D) into H¹(D) quotient.

2. **Finiteness**: h¹(D) is finite for all D.

3. **Vanishing**: h¹(D) = 0 for deg(D) >> 0 (strong approximation).

4. **Serre Duality**: h¹(D) = ℓ(K - D).
   This is the key theorem that, combined with Riemann inequality,
   gives full Riemann-Roch.

Once Serre duality is proved, we can discharge the `serre_duality_eq` axiom
in FullRRData.lean, completing Track B.
-/

/-- Elements of L(D) embed into A_K(D) via the diagonal map. -/
lemma globalInAdelicSubspace (D : DivisorV2 R) (f : K)
    (hf : satisfiesValuationCondition R K D f) :
    (fun _ => f) ∈ adelicSubspace k R K D := by
  intro v
  -- f ∈ L(D) means f = 0 ∨ v.valuation K f ≤ exp(D v)
  unfold satisfiesValuationCondition at hf
  rcases hf with rfl | hf'
  · left; rfl  -- f = 0
  · right; exact hf' v  -- use the valuation bound directly

/-- Elements of K map to zero in H¹(D). -/
lemma quotientMap_of_global (D : DivisorV2 R) (f : K) :
    quotientMap k R K D (fun _ => f) = 0 := by
  unfold quotientMap
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  apply Submodule.mem_sup_left
  exact ⟨f, rfl⟩

end AdelicH1

/-! ## Next Steps for Track B

To complete the full Riemann-Roch proof:

1. **Prove valuation sorries** (Cycle 86):
   - `adelicSubspace.add_mem'`: Use Mathlib's ultrametric inequality
   - `adelicSubspace.zero_mem'`: Use intValuation behavior on zero
   - `adelicSubspace.smul_mem'`: Need k = constant field hypothesis

2. **Prove finiteness of H¹(D)** (Cycle 87):
   - For effective D with large degree, H¹(D) = 0
   - Use strong approximation theorem

3. **Prove Serre duality** (Cycles 88-89):
   - h¹(D) = ℓ(K - D)
   - Use trace pairing / different ideal
   - Connect to DifferentIdealBridge.lean

4. **Instantiate FullRRData** (Cycle 90):
   - Discharge `serre_duality_eq` axiom
   - Full RR theorem becomes unconditional!
-/

end RiemannRochV2
