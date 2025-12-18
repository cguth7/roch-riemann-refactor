import RrLean.RiemannRochV2.TraceDualityProof
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Adelic Riemann-Roch Infrastructure (Track B)

This module provides the adelic approach to the Riemann-Roch theorem by connecting
Mathlib's `FiniteAdeleRing` to our divisor framework.

## Main Definitions

* `AdeleBoundedByDivisor` : The adeles bounded by a divisor D
* `adelicSubspace` : K + A_K(D) as a subspace

## Mathematical Background

The adelic approach to Riemann-Roch uses the exact sequence:
```
0 → K → A_K → A_K/K → 0
```
where:
- A_K = FiniteAdeleRing R K = restricted product ∏'_v K_v
- The cohomology H¹(D) = A_K / (K + A_K(D))

The key theorem (Serre duality) states:
```
h¹(D) = ℓ(K - D)
```
Combined with the definition h⁰(D) = ℓ(D) and deg(K) = 2g-2, this gives RR.

## References

* `Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing`
* `Mathlib.RingTheory.DedekindDomain.AdicValuation`
* Liu "Algebraic Geometry and Arithmetic Curves" Chapter 7
-/

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors RestrictedProduct

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## Adeles and Divisor-Bounded Adeles

The finite adele ring `FiniteAdeleRing R K` is already defined in Mathlib as:
```
Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]
```

We define the "adeles bounded by divisor D" as those adeles where at each place v,
the component lies in P_v^{-D(v)} ⊆ K_v.
-/

section AdelicSpaces

/-- The finite adele ring. This is Mathlib's definition. -/
abbrev FiniteAdele := FiniteAdeleRing R K

/-- An element of the adele ring satisfies the divisor bound D at place v
if its valuation (as a norm) is at most exp(D(v)).

More precisely, x ∈ A_K(D) iff v(x_v) ≤ exp(D(v)) for all v.
This matches L(D) = {f : v(f) ≤ exp(D(v))}, allowing poles up to order D(v).

Using Mathlib's `Valued.v` for the valuation on the adic completion. -/
def adeleAtPlaceSatisfiesBound (x : FiniteAdele R K) (D : DivisorV2 R)
    (v : HeightOneSpectrum R) : Prop :=
  -- x_v has valuation ≤ exp(D(v)) in the completion K_v
  -- Valued.v : v.adicCompletion K → WithZero (Multiplicative ℤ)
  Valued.v (x v) ≤ WithZero.exp (D v)

/-- The adeles bounded by divisor D.

A_K(D) = {x ∈ A_K : v(x_v) ≤ exp(D(v)) for all v}

This is a subset of the adele ring, matching the L(D) definition. -/
def AdeleBoundedByDivisor (D : DivisorV2 R) : Set (FiniteAdele R K) :=
  {x | ∀ v, adeleAtPlaceSatisfiesBound R K x D v}

/-- Zero adele is in A_K(D) for any D. -/
lemma zero_mem_adeleBoundedByDivisor (D : DivisorV2 R) :
    (0 : FiniteAdele R K) ∈ AdeleBoundedByDivisor R K D := by
  intro v
  unfold adeleAtPlaceSatisfiesBound
  rw [RestrictedProduct.zero_apply, Valuation.map_zero]
  exact bot_le

/-- The adeles bounded by D form an additive subgroup. -/
lemma adeleBoundedByDivisor_add (D : DivisorV2 R) :
    ∀ x y, x ∈ AdeleBoundedByDivisor R K D → y ∈ AdeleBoundedByDivisor R K D →
      x + y ∈ AdeleBoundedByDivisor R K D := by
  intro x y hx hy v
  unfold AdeleBoundedByDivisor adeleAtPlaceSatisfiesBound at *
  -- The valuation satisfies v(x + y) ≤ max(v(x), v(y))
  have hval : Valued.v ((x + y) v) ≤ max (Valued.v (x v)) (Valued.v (y v)) := by
    rw [RestrictedProduct.add_apply]
    exact Valuation.map_add_le_max' _ _ _
  calc Valued.v ((x + y) v)
      ≤ max (Valued.v (x v)) (Valued.v (y v)) := hval
    _ ≤ WithZero.exp (D v) := max_le (hx v) (hy v)

/-- Negation preserves divisor bounds. -/
lemma adeleBoundedByDivisor_neg (D : DivisorV2 R) :
    ∀ x, x ∈ AdeleBoundedByDivisor R K D → -x ∈ AdeleBoundedByDivisor R K D := by
  intro x hx v
  unfold adeleAtPlaceSatisfiesBound
  rw [RestrictedProduct.neg_apply, Valuation.map_neg]
  exact hx v

/-- The diagonal embedding of K into the adele ring.
This is `FiniteAdeleRing.algebraMap R K` from Mathlib. -/
abbrev diagonalEmbedding : K →+* FiniteAdele R K := FiniteAdeleRing.algebraMap R K

/-- Elements of L(D) embed diagonally into A_K(D).

If f ∈ L(D), then for all v, v(f) ≤ exp(D(v)).
The diagonal embedding sends f to (f, f, f, ...) in A_K.
At each component, the valuation bound is preserved. -/
lemma RRSpace_subset_AdeleBounded (D : DivisorV2 R) :
    ∀ f : K, f ∈ RRModuleV2_real R K D → diagonalEmbedding R K f ∈ AdeleBoundedByDivisor R K D := by
  intro f hf v
  unfold adeleAtPlaceSatisfiesBound
  -- f ∈ L(D) means satisfiesValuationCondition R K D f
  -- which is f = 0 ∨ ∀ v, v.valuation K f ≤ WithZero.exp (D v)
  simp only [RRModuleV2_real, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, satisfiesValuationCondition] at hf
  -- The diagonal embedding at component v is just f viewed in the completion
  have h_embed : (diagonalEmbedding R K f) v = (f : v.adicCompletion K) := rfl
  rw [h_embed]
  rw [valuedAdicCompletion_eq_valuation']
  rcases hf with rfl | hf'
  · rw [Valuation.map_zero]; exact bot_le
  · exact hf' v

end AdelicSpaces

/-! ## Cohomology H¹(D)

H¹(D) is defined as the quotient:
```
H¹(D) := A_K / (K + A_K(D))
```

The key properties are:
1. H¹(D) is finite-dimensional over k
2. h¹(D) = dim_k(H¹(D)) = ℓ(K - D) (Serre duality)
-/

section AdelicCohomology

variable (k : Type*) [Field k] [Algebra k R] [Algebra k K] [IsScalarTower k R K]

/-- The image of K + A_K(D) in A_K.

This is the subset consisting of adeles of the form f + x where f ∈ K
and x ∈ A_K(D). -/
def adelicSubspace (D : DivisorV2 R) : Set (FiniteAdele R K) :=
  {a | ∃ f : K, ∃ x ∈ AdeleBoundedByDivisor R K D, a = diagonalEmbedding R K f + x}

/-- K embeds into the adelic subspace K + A_K(D). -/
lemma K_subset_adelicSubspace (D : DivisorV2 R) (f : K) :
    diagonalEmbedding R K f ∈ adelicSubspace R K D := by
  use f, 0, zero_mem_adeleBoundedByDivisor R K D
  simp

/-- A_K(D) is contained in K + A_K(D). -/
lemma adeleBounded_subset_adelicSubspace (D : DivisorV2 R) :
    AdeleBoundedByDivisor R K D ⊆ adelicSubspace R K D := by
  intro x hx
  use 0, x, hx
  simp

/-- The Riemann-Roch equation via adelic cohomology.

If we define:
- h⁰(D) = ℓ(D) = dim_k L(D)
- h¹(D) = dim_k (A_K / (K + A_K(D)))

Then Riemann-Roch states:
  h⁰(D) - h¹(D) = deg(D) + 1 - g

And Serre duality states:
  h¹(D) = h⁰(K - D)

Combining these gives the classical form:
  ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
-/
theorem riemann_roch_via_adeles
    [frr : FullRRData k R K]
    (D : DivisorV2 R)
    [Module.Finite k (RRSpace_proj k R K D)]
    [Module.Finite k (RRSpace_proj k R K (frr.canonical - D))] :
    (ell_proj k R K D : ℤ) - ell_proj k R K (frr.canonical - D) = D.deg + 1 - frr.genus :=
  -- This follows from the FullRRData axiom
  frr.serre_duality_eq D

end AdelicCohomology

/-! ## Next Steps for Track B

To complete Track B (discharge `serre_duality_eq` axiom):

1. **Prove A_K(D) is an additive subgroup**: Already shown above via lemmas.

2. **Finiteness of H¹(D)**: Show A_K / (K + A_K(D)) is finite-dimensional.
   Key: For D effective with large enough degree, h¹(D) = 0.

3. **Serre duality**: Prove h¹(D) = ℓ(K - D) via trace pairing.
   - At each place v, use local duality: K_v / O_v ≅ (O_v)*^dual
   - Global: piece together via product formula

4. **Instantiate FullRRData**: Use concrete K (from differentIdeal) and g (from arithmetic genus)
   to create an instance satisfying the axioms.

Estimated: 5-8 more cycles for full proof.
-/

end RiemannRochV2
