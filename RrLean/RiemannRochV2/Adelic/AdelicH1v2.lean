import RrLean.RiemannRochV2.Adelic.Adeles
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Adelic H¹(D) using Mathlib's FiniteAdeleRing (Track B v2)

This module defines H¹(D) using Mathlib's proper `FiniteAdeleRing` (restricted product)
instead of the simplified model in `Adeles.lean`.

## Key Advantage

Using `FiniteAdeleRing R K` (the restricted product Πʳ_v K_v) gives:
1. Elements are integral at almost all places (built-in)
2. For large deg(D), A_K(D) covers all finite adeles → H¹(D) = 0
3. Strong approximation theorem applies directly

## Main Definitions

* `AdelicH1v2.boundedSubset` : {a ∈ FiniteAdeleRing : v(a_v) ≤ exp(D(v)) for all v}
* `AdelicH1v2.boundedSubmodule` : A_K(D) as a k-submodule
* `AdelicH1v2.globalSubmodule` : K embedded diagonally as a k-submodule
* `AdelicH1v2.globalPlusBoundedSubmodule` : K + A_K(D) as a k-submodule
* `AdelicH1v2.SpaceModule` : H¹(D) = FiniteAdeleRing / (K + A_K(D)) as a k-module
* `AdelicH1v2.h1_finrank` : dim_k H¹(D)

## Algebra Structure (Cycle 93)

We establish `Algebra k (FiniteAdeleRing R K)` via the composition:
  k → K → FiniteAdeleRing R K

This allows us to view H¹(D) as a k-module quotient, enabling proper dimension counting.

## Mathematical Background

The adelic Riemann-Roch theorem states:
- h⁰(D) - h¹(D) = deg(D) + 1 - g

where h¹(D) = dim_k(A_K / (K + A_K(D))).

Combined with Serre duality h¹(D) = h⁰(K - D), this gives full Riemann-Roch.

## References

* Mathlib's `IsDedekindDomain.FiniteAdeleRing`
* Liu "Algebraic Geometry and Arithmetic Curves" Chapter 7
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Algebra k R]
variable (K : Type*) [Field K] [Algebra k K] [Algebra R K] [IsFractionRing R K]
variable [IsScalarTower k R K]

namespace AdelicH1v2

/-! ## Algebra Structure on FiniteAdeleRing

We establish that `FiniteAdeleRing R K` is a k-algebra via the scalar tower k → R → K → FiniteAdeleRing.
-/

/-- The k-algebra structure on FiniteAdeleRing R K, obtained via composition. -/
instance : Algebra k (FiniteAdeleRing R K) :=
  (FiniteAdeleRing.algebraMap R K).comp (algebraMap k K) |>.toAlgebra

/-- The scalar tower k → K → FiniteAdeleRing R K. -/
instance : IsScalarTower k K (FiniteAdeleRing R K) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The scalar tower k → R → FiniteAdeleRing R K. -/
instance : IsScalarTower k R (FiniteAdeleRing R K) := by
  constructor
  intro x y z
  simp only [Algebra.smul_def]
  rw [← mul_assoc]
  congr 1
  -- algebraMap k (FiniteAdeleRing R K) x * algebraMap R (FiniteAdeleRing R K) y
  -- = algebraMap R (FiniteAdeleRing R K) (algebraMap k R x * y)
  rw [map_mul]
  congr 1
  -- algebraMap k (FiniteAdeleRing R K) x = algebraMap R (FiniteAdeleRing R K) (algebraMap k R x)
  -- By the definition, algebraMap k (FiniteAdeleRing R K) = FiniteAdeleRing.algebraMap R K ∘ algebraMap k K
  -- And algebraMap R (FiniteAdeleRing R K) = FiniteAdeleRing.algebraMap R K ∘ algebraMap R K
  -- Using IsScalarTower k R K: algebraMap k K = algebraMap R K ∘ algebraMap k R
  simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp, Function.comp_apply]
  rw [IsScalarTower.algebraMap_apply k R K]

/-! ## Bounded Adeles using FiniteAdeleRing

We define A_K(D) as a subset of `FiniteAdeleRing R K`.
-/

open FiniteAdeleRing

/-- The diagonal embedding of K into FiniteAdeleRing.
This uses Mathlib's `FiniteAdeleRing.algebraMap`. -/
def diagonalK : K →+* FiniteAdeleRing R K :=
  FiniteAdeleRing.algebraMap R K

/-- Access the component of a finite adele at place v. -/
def component (a : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    v.adicCompletion K :=
  a v

/-- The valuation of the v-th component of a finite adele.
Uses `Valued.v` on the adicCompletion. -/
def valuationAt (a : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    WithZero (Multiplicative ℤ) :=
  Valued.v (a v)

/-- Predicate: an adele satisfies the divisor bound at v.
We say a satisfies the bound at v if v(a_v) ≤ exp(D(v)).
This allows poles up to order D(v) at v. -/
def satisfiesBoundAt (a : FiniteAdeleRing R K) (v : HeightOneSpectrum R)
    (D : DivisorV2 R) : Prop :=
  valuationAt R K a v ≤ WithZero.exp (D v)

/-- The set of adeles bounded by divisor D.
A_K(D) = {a ∈ FiniteAdeleRing : v(a_v) ≤ exp(D(v)) for all v} -/
def boundedSubset (D : DivisorV2 R) : Set (FiniteAdeleRing R K) :=
  {a | ∀ v, satisfiesBoundAt R K a v D}

/-- Zero is in A_K(D) for any D. -/
lemma zero_mem_boundedSubset (D : DivisorV2 R) :
    (0 : FiniteAdeleRing R K) ∈ boundedSubset R K D := by
  intro v
  unfold satisfiesBoundAt valuationAt
  -- (0 : FiniteAdeleRing) at v gives 0 in adicCompletion
  have h : (0 : FiniteAdeleRing R K) v = (0 : v.adicCompletion K) := rfl
  rw [h, Valuation.map_zero]
  exact WithZero.zero_le _

/-- A_K(D) is closed under addition (ultrametric inequality). -/
lemma add_mem_boundedSubset {D : DivisorV2 R} {a b : FiniteAdeleRing R K}
    (ha : a ∈ boundedSubset R K D) (hb : b ∈ boundedSubset R K D) :
    a + b ∈ boundedSubset R K D := by
  intro v
  simp only [satisfiesBoundAt, valuationAt]
  -- For the v-th component: (a + b) v = a v + b v
  -- Use ultrametric: v(a + b) ≤ max(v(a), v(b)) ≤ exp(D v)
  have ha_v := ha v
  have hb_v := hb v
  simp only [satisfiesBoundAt, valuationAt] at ha_v hb_v
  calc Valued.v ((a + b) v)
      = Valued.v (a v + b v) := by rfl
    _ ≤ max (Valued.v (a v)) (Valued.v (b v)) :=
        Valuation.map_add_le_max' _ (a v) (b v)
    _ ≤ WithZero.exp (D v) := max_le ha_v hb_v

/-- A_K(D) is closed under negation. -/
lemma neg_mem_boundedSubset {D : DivisorV2 R} {a : FiniteAdeleRing R K}
    (ha : a ∈ boundedSubset R K D) :
    -a ∈ boundedSubset R K D := by
  intro v
  unfold satisfiesBoundAt valuationAt
  have ha_v := ha v
  unfold satisfiesBoundAt valuationAt at ha_v
  -- (-a) v = -(a v) and v(−x) = v(x)
  have hneg : (-a) v = -(a v) := rfl
  rw [hneg, Valuation.map_neg]
  exact ha_v

/-- A_K(D) as an additive subgroup of FiniteAdeleRing. -/
def boundedAddSubgroup (D : DivisorV2 R) : AddSubgroup (FiniteAdeleRing R K) where
  carrier := boundedSubset R K D
  add_mem' := add_mem_boundedSubset R K
  zero_mem' := zero_mem_boundedSubset R K D
  neg_mem' := neg_mem_boundedSubset R K

/-- A_K(D) is closed under k-scalar multiplication.

For c ∈ k, we have c • a = algebraMap k (FiniteAdeleRing R K) c * a.
Since algebraMap factors through R, and elements of R have valuation ≤ 1 at each place,
we get v(c • a) = v(c) * v(a) ≤ 1 * v(a) ≤ exp(D v). -/
lemma smul_mem_boundedSubset (D : DivisorV2 R) (c : k) {a : FiniteAdeleRing R K}
    (ha : a ∈ boundedSubset R K D) :
    c • a ∈ boundedSubset R K D := by
  intro v
  unfold satisfiesBoundAt valuationAt
  have ha_v := ha v
  unfold satisfiesBoundAt valuationAt at ha_v
  -- c • a = algebraMap k (FiniteAdeleRing R K) c * a by Algebra.smul_def
  rw [Algebra.smul_def]
  -- (algebraMap k (FiniteAdeleRing R K) c * a) v = algebraMap k (FiniteAdeleRing R K) c v * a v
  have hmul : (algebraMap k (FiniteAdeleRing R K) c * a) v =
      (algebraMap k (FiniteAdeleRing R K) c) v * a v := rfl
  rw [hmul, Valuation.map_mul]
  -- Need: v(algebraMap k (FiniteAdeleRing R K) c) ≤ 1
  -- The algebraMap factors: k → K → FiniteAdeleRing R K
  -- At component v, (algebraMap k (FiniteAdeleRing R K) c) v = (algebraMap k K c : v.adicCompletion K)
  have hc_val : Valued.v ((algebraMap k (FiniteAdeleRing R K) c) v) ≤ 1 := by
    -- The algebraMap k → FiniteAdeleRing factors through K via diagonal embedding
    -- At component v: (algebraMap k (FiniteAdeleRing R K) c) v = (algebraMap k K c : adicCompletion)
    -- This is just the coercion of algebraMap k K c into the completion
    have heq : ((algebraMap k (FiniteAdeleRing R K) c) v) = (algebraMap k K c : v.adicCompletion K) := rfl
    rw [heq, valuedAdicCompletion_eq_valuation']
    -- Now goal: v.valuation K (algebraMap k K c) ≤ 1
    -- Use scalar tower: algebraMap k K c = algebraMap R K (algebraMap k R c)
    rw [IsScalarTower.algebraMap_apply k R K]
    exact HeightOneSpectrum.valuation_le_one v (algebraMap k R c)
  -- Use transitivity: v(c) * v(a) ≤ 1 * v(a) ≤ v(a) ≤ exp(D v)
  have h1 : Valued.v ((algebraMap k (FiniteAdeleRing R K) c) v) * Valued.v (a v)
      ≤ 1 * Valued.v (a v) := by
    apply mul_le_mul_of_nonneg_right hc_val
    exact WithZero.zero_le _
  have h2 : (1 : WithZero (Multiplicative ℤ)) * Valued.v (a v) = Valued.v (a v) := one_mul _
  calc Valued.v ((algebraMap k (FiniteAdeleRing R K) c) v) * Valued.v (a v)
      ≤ 1 * Valued.v (a v) := h1
    _ = Valued.v (a v) := h2
    _ ≤ WithZero.exp (D v) := ha_v

/-- A_K(D) as a k-submodule of FiniteAdeleRing. -/
def boundedSubmodule (D : DivisorV2 R) : Submodule k (FiniteAdeleRing R K) where
  carrier := boundedSubset R K D
  add_mem' := add_mem_boundedSubset R K
  zero_mem' := zero_mem_boundedSubset R K D
  smul_mem' := smul_mem_boundedSubset k R K D

/-! ## Global Elements

The image of K in FiniteAdeleRing via diagonal embedding.
-/

/-- The set of global elements (diagonal K).
Elements of the form (x, x, x, ...) for x ∈ K. -/
def globalSubset : Set (FiniteAdeleRing R K) :=
  Set.range (diagonalK R K)

/-- The diagonal of K is an additive subgroup. -/
def globalAddSubgroup : AddSubgroup (FiniteAdeleRing R K) where
  carrier := globalSubset R K
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, (diagonalK R K).map_add x y⟩
  zero_mem' := ⟨0, (diagonalK R K).map_zero⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, (diagonalK R K).map_neg x⟩

/-- The diagonal of K is closed under k-scalar multiplication. -/
lemma smul_mem_globalSubset (c : k) {a : FiniteAdeleRing R K}
    (ha : a ∈ globalSubset R K) :
    c • a ∈ globalSubset R K := by
  obtain ⟨x, rfl⟩ := ha
  -- c • (diagonalK R K x) = diagonalK R K (c • x)
  -- Because diagonalK R K = FiniteAdeleRing.algebraMap R K is a ring hom
  -- and c • x = algebraMap k K c * x
  use c • x
  simp only [Algebra.smul_def]
  -- Need: diagonalK R K (algebraMap k K c * x) = algebraMap k (FiniteAdeleRing R K) c * diagonalK R K x
  -- Both sides are ring hom applications
  rw [map_mul]
  rfl

/-- The diagonal of K as a k-submodule. -/
def globalSubmodule : Submodule k (FiniteAdeleRing R K) where
  carrier := globalSubset R K
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, (diagonalK R K).map_add x y⟩
  zero_mem' := ⟨0, (diagonalK R K).map_zero⟩
  smul_mem' := smul_mem_globalSubset k R K

/-! ## H¹(D) Definition

H¹(D) = FiniteAdeleRing / (K + A_K(D))

We define two versions:
1. `globalPlusBounded` - AddSubgroup version (for compatibility)
2. `globalPlusBoundedSubmodule` - k-Submodule version (for dimension counting)
-/

/-- K + A_K(D) as an additive subgroup.
This is the sum of the global diagonal and the bounded adeles. -/
def globalPlusBounded (D : DivisorV2 R) : AddSubgroup (FiniteAdeleRing R K) :=
  globalAddSubgroup R K ⊔ boundedAddSubgroup R K D

/-- K + A_K(D) as a k-submodule.
This is the sum of the global diagonal and the bounded adeles as k-subspaces. -/
def globalPlusBoundedSubmodule (D : DivisorV2 R) : Submodule k (FiniteAdeleRing R K) :=
  globalSubmodule k R K + boundedSubmodule k R K D

/-- H¹(D) = FiniteAdeleRing / (K + A_K(D)) as an additive quotient group. -/
abbrev Space (D : DivisorV2 R) : Type _ :=
  (FiniteAdeleRing R K) ⧸ (globalPlusBounded R K D)

/-- H¹(D) as a k-module quotient.
This is the mathematically correct definition for dimension counting. -/
abbrev SpaceModule (D : DivisorV2 R) : Type _ :=
  (FiniteAdeleRing R K) ⧸ (globalPlusBoundedSubmodule k R K D)

/-- The quotient map from FiniteAdeleRing to H¹(D) (additive group version). -/
def quotientMap (D : DivisorV2 R) :
    FiniteAdeleRing R K →+ Space R K D :=
  QuotientAddGroup.mk' (globalPlusBounded R K D)

/-- The quotient map from FiniteAdeleRing to H¹(D) (k-linear version). -/
def quotientMapLinear (D : DivisorV2 R) :
    FiniteAdeleRing R K →ₗ[k] SpaceModule k R K D :=
  Submodule.mkQ (globalPlusBoundedSubmodule k R K D)

/-- Global elements map to zero in H¹(D). -/
lemma quotientMap_of_global (D : DivisorV2 R) (x : K) :
    quotientMap R K D (diagonalK R K x) = 0 := by
  unfold quotientMap
  -- QuotientAddGroup.mk' N x = 0 ↔ x ∈ N
  -- The goal is: (QuotientAddGroup.mk' ...) (diagonalK R K x) = 0
  -- Which means: diagonalK R K x ∈ globalPlusBounded R K D
  have hmem : diagonalK R K x ∈ globalPlusBounded R K D := by
    apply AddSubgroup.mem_sup_left
    exact ⟨x, rfl⟩
  simp only [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, hmem]

/-- Global elements map to zero in H¹(D) (k-module version). -/
lemma quotientMapLinear_of_global (D : DivisorV2 R) (x : K) :
    quotientMapLinear k R K D (diagonalK R K x) = 0 := by
  unfold quotientMapLinear
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  apply Submodule.mem_sup_left
  exact ⟨x, rfl⟩

/-! ## Dimension h¹(D)

The dimension of H¹(D) as a k-vector space.
-/

/-- The rank of H¹(D) as a cardinal. -/
def h1_rank (D : DivisorV2 R) : Cardinal :=
  Module.rank k (SpaceModule k R K D)

/-- The dimension h¹(D) when H¹(D) is finite-dimensional. -/
def h1_finrank (D : DivisorV2 R) : ℕ :=
  Module.finrank k (SpaceModule k R K D)

/-! ## Key Properties (To be proved)

1. **Monotonicity**: D ≤ E → A_K(D) ⊆ A_K(E)
2. **Cofinality**: For D >> 0, A_K(D) ⊇ {integral adeles} (almost all places)
3. **Vanishing**: h¹(D) = 0 for deg(D) >> 0
4. **Serre duality**: h¹(D) = ℓ(K - D)
-/

/-- Monotonicity: larger divisors give larger bounded subsets. -/
lemma boundedSubset_mono {D E : DivisorV2 R} (h : D ≤ E) :
    boundedSubset R K D ⊆ boundedSubset R K E := by
  intro a ha v
  have hD := ha v
  simp only [satisfiesBoundAt, valuationAt] at hD ⊢
  have hv : D v ≤ E v := h v
  calc Valued.v (a v) ≤ WithZero.exp (D v) := hD
    _ ≤ WithZero.exp (E v) := WithZero.exp_le_exp.mpr hv

/-- Monotonicity for boundedSubmodule: D ≤ E implies A_K(D) ⊆ A_K(E) as k-submodules. -/
lemma boundedSubmodule_mono {D E : DivisorV2 R} (h : D ≤ E) :
    boundedSubmodule k R K D ≤ boundedSubmodule k R K E :=
  boundedSubset_mono R K h

/-- Monotonicity for globalPlusBoundedSubmodule: D ≤ E implies K + A_K(D) ⊆ K + A_K(E). -/
lemma globalPlusBoundedSubmodule_mono {D E : DivisorV2 R} (h : D ≤ E) :
    globalPlusBoundedSubmodule k R K D ≤ globalPlusBoundedSubmodule k R K E :=
  sup_le_sup_left (boundedSubmodule_mono k R K h) _

/-- Elements of L(D) ⊆ K embed into A_K(D) via the diagonal.

If f ∈ L(D), meaning v(f) ≤ exp(D(v)) for all v, then the diagonal
embedding of f is in A_K(D). -/
lemma globalInBounded (D : DivisorV2 R) (f : K)
    (hf : satisfiesValuationCondition R K D f) :
    diagonalK R K f ∈ boundedSubset R K D := by
  intro v
  unfold satisfiesBoundAt valuationAt
  -- The diagonal embedding gives f at each place
  -- diagonalK R K = FiniteAdeleRing.algebraMap R K
  -- So (diagonalK R K f) v = (f : adicCompletion K v)
  -- Need: Valued.v (f : adicCompletion K v) ≤ exp(D v)
  -- This follows from hf : v(f) ≤ exp(D v) since adicCompletion extends K
  unfold satisfiesValuationCondition at hf
  rcases hf with rfl | hf'
  · -- f = 0 case
    -- (diagonalK R K 0) = 0 by map_zero, and (0 : FiniteAdeleRing) v = 0 in adicCompletion
    have h0 : (diagonalK R K 0) v = (0 : v.adicCompletion K) := by
      simp only [diagonalK, map_zero]
      rfl
    rw [h0, Valuation.map_zero]
    exact WithZero.zero_le _
  · -- f ≠ 0 case with valuation bounds
    specialize hf' v
    -- The key: (diagonalK R K f) v = (f : adicCompletion K v) by definition
    -- And Valued.v (f : adicCompletion K v) = valuation K v f by valuedAdicCompletion_eq_valuation'
    have heq : (diagonalK R K f) v = (f : v.adicCompletion K) := rfl
    rw [heq, valuedAdicCompletion_eq_valuation']
    exact hf'

/-! ## Adelic Riemann-Roch Data

The adelic approach to Riemann-Roch axiomatizes:
1. Finiteness of h¹(D)
2. Vanishing: h¹(D) = 0 for deg(D) >> 0
3. Serre duality: h¹(D) = ℓ(K - D)

Combined with the Riemann inequality, this gives full Riemann-Roch.
-/

/-- Adelic Riemann-Roch data for a proper curve.

This typeclass packages the key properties of h¹(D) needed for full Riemann-Roch:
- `h1_finite`: H¹(D) is finite-dimensional as a k-vector space
- `h1_vanishing`: h¹(D) = 0 when deg(D) is large enough
- `adelic_rr`: ℓ(D) - h¹(D) = deg(D) + 1 - g (the "raw" adelic RR)
- `serre_duality`: h¹(D) = ℓ(K - D) for all D
- `deg_canonical`: deg(K) = 2g - 2

The combination of adelic_rr and serre_duality gives the full Riemann-Roch equation.
-/
class AdelicRRData (canonical : DivisorV2 R) (genus : ℕ) where
  /-- H¹(D) is always finite-dimensional. -/
  h1_finite : ∀ D : DivisorV2 R, Module.Finite k (SpaceModule k R K D)
  /-- L(D) is finite-dimensional (needed for ℓ(D)). -/
  ell_finite : ∀ D : DivisorV2 R, Module.Finite k (RRSpace_proj k R K D)
  /-- h¹(D) = 0 when deg(D) > 2g - 2.
  This follows from strong approximation: for large D, K + A_K(D) = FiniteAdeleRing. -/
  h1_vanishing : ∀ D : DivisorV2 R, D.deg > 2 * (genus : ℤ) - 2 → h1_finrank k R K D = 0
  /-- The adelic Riemann-Roch equation (Euler characteristic).
  This is the fundamental relation between h⁰ and h¹. -/
  adelic_rr : ∀ D : DivisorV2 R,
    (ell_proj k R K D : ℤ) - h1_finrank k R K D = D.deg + 1 - genus
  /-- Serre duality: h¹(D) = ℓ(K - D).
  This is the key theorem connecting adelic cohomology to Riemann-Roch spaces. -/
  serre_duality : ∀ D : DivisorV2 R, h1_finrank k R K D = ell_proj k R K (canonical - D)
  /-- The canonical divisor has degree 2g - 2. -/
  deg_canonical : canonical.deg = 2 * (genus : ℤ) - 2

/-- Bridge: AdelicRRData implies FullRRData.

This shows that proving the adelic axioms is sufficient to discharge
the FullRRData axioms, completing Track B.

The key derivation:
1. By Serre duality: h¹(D) = ℓ(K - D)
2. By adelic RR: ℓ(D) - h¹(D) = deg(D) + 1 - g
3. Substituting: ℓ(D) - ℓ(K - D) = deg(D) + 1 - g ✓
-/
def adelicRRData_to_FullRRData [arr : AdelicRRData k R K canonical genus]
    [pc : ProperCurve k R K] : FullRRData k R K where
  toProperCurve := pc
  canonical := canonical
  genus := genus
  deg_canonical := arr.deg_canonical
  serre_duality_eq := fun D => by
    -- Use Serre duality: h¹(D) = ℓ(K - D)
    -- So ℓ(D) - ℓ(K - D) = ℓ(D) - h¹(D)
    -- And by adelic RR: ℓ(D) - h¹(D) = deg(D) + 1 - g
    calc (ell_proj k R K D : ℤ) - ell_proj k R K (canonical - D)
        = (ell_proj k R K D : ℤ) - h1_finrank k R K D := by rw [arr.serre_duality D]
      _ = D.deg + 1 - genus := arr.adelic_rr D
  ell_zero_of_neg_deg := fun D hD => by
    -- If deg(D) < 0, then deg(K - D) = (2g-2) - deg(D) > 2g - 2
    -- So h¹(K - D) = 0 by h1_vanishing
    -- By Serre duality: h¹(K - D) = ℓ(K - (K - D)) = ℓ(D)
    -- So ℓ(D) = 0
    have h_deg_comp : (canonical - D).deg > 2 * (genus : ℤ) - 2 := by
      -- deg(K - D) = deg(K + (-D)) = deg(K) + deg(-D) = deg(K) - deg(D)
      rw [sub_eq_add_neg, DivisorV2.deg_add, DivisorV2.deg_neg, arr.deg_canonical]
      omega
    have h_vanish := arr.h1_vanishing (canonical - D) h_deg_comp
    -- By Serre duality for (K - D): h¹(K - D) = ℓ(K - (K - D)) = ℓ(D)
    have h_serre := arr.serre_duality (canonical - D)
    -- Simplify K - (K - D) = D
    simp only [sub_sub_cancel] at h_serre
    omega

/-- The full Riemann-Roch theorem from adelic data. -/
theorem riemann_roch_from_adelic [arr : AdelicRRData k R K canonical genus]
    [pc : ProperCurve k R K] {D : DivisorV2 R} :
    (ell_proj k R K D : ℤ) - ell_proj k R K (canonical - D) = D.deg + 1 - genus :=
  (adelicRRData_to_FullRRData k R K).serre_duality_eq D

/-! ## Corollaries from Adelic RR

These are stated with explicit parameters to avoid instance scoping issues.
-/

/-- For deg(D) > 2g - 2, we have ℓ(D) = deg(D) + 1 - g.
This follows from h¹(D) = 0 and the adelic RR equation. -/
theorem ell_eq_deg_plus_one_minus_g_of_large_deg
    (canonical : DivisorV2 R) (genus : ℕ)
    (arr : AdelicRRData k R K canonical genus)
    {D : DivisorV2 R} (h : D.deg > 2 * (genus : ℤ) - 2) :
    (ell_proj k R K D : ℤ) = D.deg + 1 - genus := by
  have h_vanish := arr.h1_vanishing D h
  have h_rr := arr.adelic_rr D
  simp only [h_vanish, CharP.cast_eq_zero, sub_zero] at h_rr
  exact h_rr

/-- h¹(K) = 1 for the canonical divisor.
This follows from Serre duality: h¹(K) = ℓ(K - K) = ℓ(0) = 1. -/
theorem h1_canonical_eq_one
    (canonical : DivisorV2 R) (genus : ℕ)
    (arr : AdelicRRData k R K canonical genus)
    (pc : ProperCurve k R K) :
    h1_finrank k R K canonical = 1 := by
  rw [arr.serre_duality canonical]
  simp only [sub_self]
  exact pc.ell_zero_eq_one

/-! ## Monotonicity for h¹

Larger divisors have smaller h¹ (anti-monotone).
-/

/-- h¹ is anti-monotone: D ≤ E implies h¹(E) ≤ h¹(D).

This follows from: D ≤ E implies A_K(D) ⊆ A_K(E) implies
(K + A_K(D)) ⊆ (K + A_K(E)) implies the quotient gets smaller.

Note: This requires the source quotient to be finite-dimensional.
This is guaranteed by `AdelicRRData.h1_finite` when working with proper curves.
-/
lemma h1_anti_mono {D E : DivisorV2 R} (h : D ≤ E)
    [hfin : Module.Finite k (SpaceModule k R K D)] :
    h1_finrank k R K E ≤ h1_finrank k R K D := by
  -- Since D ≤ E, we have globalPlusBoundedSubmodule D ≤ globalPlusBoundedSubmodule E
  have hmono := globalPlusBoundedSubmodule_mono k R K h
  -- Construct the surjective map from quotient by smaller submodule to quotient by larger
  -- Using mapQ: for M/N → M/N' when N ≤ N', we use mapQ with f = id
  -- The condition is: N ≤ comap id N' = N'
  let f : SpaceModule k R K D →ₗ[k] SpaceModule k R K E :=
    Submodule.mapQ (globalPlusBoundedSubmodule k R K D) (globalPlusBoundedSubmodule k R K E)
      LinearMap.id (by rwa [Submodule.comap_id])
  -- f is surjective: for any [x] in the target, it equals f [x]
  have hf_surj : Function.Surjective f := by
    intro y
    -- Every element of SpaceModule E is a quotient of some x ∈ FiniteAdeleRing
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    -- The same x represents an element in SpaceModule D
    use Submodule.Quotient.mk x
    -- f sends [x] in D to [x] in E
    rfl
  -- Use: finrank of range ≤ finrank of domain
  -- Since f is surjective, range f = ⊤, so finrank (target) = finrank (range f) ≤ finrank (source)
  unfold h1_finrank
  calc Module.finrank k (SpaceModule k R K E)
      = Module.finrank k (LinearMap.range f) := by
        rw [LinearMap.range_eq_top.mpr hf_surj, finrank_top]
    _ ≤ Module.finrank k (SpaceModule k R K D) := LinearMap.finrank_range_le f

end AdelicH1v2

/-! ## Connection to Previous Infrastructure

This module provides a more mathematically correct H¹(D) using the restricted
product structure. The previous `Adeles.lean` used all functions, which made
H¹(D) too large.

**Key Differences**:
1. `Adeles.lean`: Uses `HeightOneSpectrum R → K` (all functions)
2. `AdelicH1v2.lean`: Uses `FiniteAdeleRing R K` (restricted product)

The restricted product ensures that elements are integral at almost all places,
which is essential for:
- Finiteness of H¹(D)
- Strong approximation (vanishing for large degree)
- Connection to classical adelic theory
-/

end RiemannRochV2
