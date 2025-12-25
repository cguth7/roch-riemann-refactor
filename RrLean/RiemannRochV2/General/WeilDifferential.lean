/-
# Weil Differentials

This file defines Weil differentials as linear functionals on the adele ring
that vanish on the diagonal image of the function field K.

## Mathematical Background

For a smooth projective curve over a finite field, a Weil differential is
a k-linear map ω : A_K → k such that ω(K) = 0, where K is diagonally
embedded in the adeles A_K.

The space of Weil differentials forms a K-vector space under the action:
  (c · ω)(a) = ω(c · a)

for c ∈ K and a ∈ A_K.

## Main Definitions

* `WeilDifferential` : The type of Weil differentials
* `WeilDifferential.toLinearMap` : The underlying linear map
* `WeilDifferential.vanishes_on_K` : The vanishing condition on K

## Key Properties

The Serre duality pairing uses Weil differentials:
  ⟨f, ω⟩ = ω(embed f)

where embed : L(D) → A_K embeds elements into the adeles.

## References

* Rosen, "Number Theory in Function Fields", Ch. 6
* Stichtenoth, "Algebraic Function Fields", §1.7

## Status

Cycle 312: Structure definition, AddCommGroup, and Module k instances.
Cycle 313: Module K instance (deferred - requires careful handling).
-/

import RrLean.RiemannRochV2.Adelic.FullAdelesBase

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open RiemannRochV2.FullAdeles

namespace RiemannRochV2

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Algebra k R]
variable (K : Type*) [Field K] [Algebra k K] [Algebra R K] [IsFractionRing R K]
variable [IsScalarTower k R K]
variable (K_infty : Type*) [Field K_infty] [Algebra K K_infty]
variable [TopologicalSpace K_infty] [IsTopologicalRing K_infty]

/-! ## Algebra Structure on FullAdeleRing

We establish that `FullAdeleRing R K K_infty` is a k-algebra via the scalar tower.
-/

section AlgebraStructure

/-- The k-algebra structure on FullAdeleRing R K K_infty. -/
instance instAlgebraFullAdeleRing : Algebra k (FullAdeleRing R K K_infty) :=
  (fullDiagonalEmbedding R K K_infty).comp (algebraMap k K) |>.toAlgebra

/-- The scalar tower k → K → FullAdeleRing R K K_infty. -/
instance instScalarTowerKFullAdele : IsScalarTower k K (FullAdeleRing R K K_infty) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The algebraMap from k to FullAdeleRing factors through K. -/
lemma algebraMap_fullAdele_eq (c : k) :
    algebraMap k (FullAdeleRing R K K_infty) c =
    fullDiagonalEmbedding R K K_infty (algebraMap k K c) := rfl

end AlgebraStructure

/-! ## Weil Differential Definition -/

/-- A Weil differential is a k-linear functional on the full adele ring
that vanishes on the diagonal image of K.

Mathematically, this represents ω ∈ Ω¹(K) where:
- toLinearMap : A_K →ₗ[k] k is the linear functional
- vanishes_on_K : ω(K) = 0 encodes the residue theorem

The residue theorem states that the sum of residues of a meromorphic differential
over a global function equals zero. Here we encode this as vanishing on K.
-/
structure WeilDifferential where
  /-- The underlying k-linear map from adeles to k. -/
  toLinearMap : FullAdeleRing R K K_infty →ₗ[k] k
  /-- The linear map vanishes on diagonally embedded K. -/
  vanishes_on_K : ∀ x : K, toLinearMap (fullDiagonalEmbedding R K K_infty x) = 0

namespace WeilDifferential

variable {k R K K_infty}

/-! ## Basic Operations -/

/-- Coercion to the underlying linear map. -/
instance : CoeFun (WeilDifferential k R K K_infty) (fun _ => FullAdeleRing R K K_infty → k) :=
  ⟨fun ω => ω.toLinearMap⟩

@[simp]
lemma coe_toLinearMap (ω : WeilDifferential k R K K_infty) :
    (ω : FullAdeleRing R K K_infty → k) = ω.toLinearMap := rfl

@[simp]
lemma apply_diag (ω : WeilDifferential k R K K_infty) (x : K) :
    ω (fullDiagonalEmbedding R K K_infty x) = 0 := ω.vanishes_on_K x

@[ext]
lemma ext {ω₁ ω₂ : WeilDifferential k R K K_infty}
    (h : ∀ a, ω₁ a = ω₂ a) : ω₁ = ω₂ := by
  cases ω₁; cases ω₂
  simp only [mk.injEq]
  ext a
  exact h a

/-! ## AddCommGroup Structure

Weil differentials form an additive group under pointwise operations.
-/

/-- Zero Weil differential. -/
instance : Zero (WeilDifferential k R K K_infty) :=
  ⟨⟨0, fun _ => by simp⟩⟩

@[simp]
lemma zero_apply (a : FullAdeleRing R K K_infty) : (0 : WeilDifferential k R K K_infty) a = 0 := rfl

@[simp]
lemma zero_toLinearMap : (0 : WeilDifferential k R K K_infty).toLinearMap = 0 := rfl

/-- Addition of Weil differentials. -/
instance : Add (WeilDifferential k R K K_infty) :=
  ⟨fun ω₁ ω₂ => ⟨ω₁.toLinearMap + ω₂.toLinearMap, fun x => by simp [ω₁.vanishes_on_K, ω₂.vanishes_on_K]⟩⟩

@[simp]
lemma add_apply (ω₁ ω₂ : WeilDifferential k R K K_infty) (a : FullAdeleRing R K K_infty) :
    (ω₁ + ω₂) a = ω₁ a + ω₂ a := rfl

@[simp]
lemma add_toLinearMap (ω₁ ω₂ : WeilDifferential k R K K_infty) :
    (ω₁ + ω₂).toLinearMap = ω₁.toLinearMap + ω₂.toLinearMap := rfl

/-- Negation of Weil differentials. -/
instance : Neg (WeilDifferential k R K K_infty) :=
  ⟨fun ω => ⟨-ω.toLinearMap, fun x => by simp [ω.vanishes_on_K]⟩⟩

@[simp]
lemma neg_apply (ω : WeilDifferential k R K K_infty) (a : FullAdeleRing R K K_infty) :
    (-ω) a = -ω a := rfl

@[simp]
lemma neg_toLinearMap (ω : WeilDifferential k R K K_infty) :
    (-ω).toLinearMap = -ω.toLinearMap := rfl

/-- Subtraction of Weil differentials. -/
instance : Sub (WeilDifferential k R K K_infty) :=
  ⟨fun ω₁ ω₂ => ω₁ + (-ω₂)⟩

@[simp]
lemma sub_apply (ω₁ ω₂ : WeilDifferential k R K K_infty) (a : FullAdeleRing R K K_infty) :
    (ω₁ - ω₂) a = ω₁ a - ω₂ a := by
  show (ω₁ + (-ω₂)) a = ω₁ a - ω₂ a
  rw [add_apply, neg_apply, sub_eq_add_neg]

/-- Weil differentials form an additive commutative group. -/
instance : AddCommGroup (WeilDifferential k R K K_infty) where
  add_assoc := fun _ _ _ => by ext; simp [add_assoc]
  zero_add := fun _ => by ext; simp
  add_zero := fun _ => by ext; simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := fun _ => by ext; simp
  add_comm := fun _ _ => by ext; simp [add_comm]

/-! ## k-Module Structure

Weil differentials form a k-vector space under scalar multiplication.
-/

/-- Scalar multiplication by k. -/
instance : SMul k (WeilDifferential k R K K_infty) :=
  ⟨fun c ω => ⟨c • ω.toLinearMap, fun x => by simp [ω.vanishes_on_K]⟩⟩

@[simp]
lemma smul_apply (c : k) (ω : WeilDifferential k R K K_infty) (a : FullAdeleRing R K K_infty) :
    (c • ω) a = c • ω a := rfl

@[simp]
lemma smul_toLinearMap (c : k) (ω : WeilDifferential k R K K_infty) :
    (c • ω).toLinearMap = c • ω.toLinearMap := rfl

/-- Weil differentials form a k-module. -/
instance : Module k (WeilDifferential k R K K_infty) where
  one_smul := fun _ => by ext; simp
  mul_smul := fun _ _ _ => by ext; simp [mul_smul]
  smul_add := fun _ _ _ => by ext; simp [smul_add]
  smul_zero := fun _ => by ext; simp
  add_smul := fun _ _ _ => by ext; simp [add_smul]
  zero_smul := fun _ => by ext; simp

/-! ## K-Module Structure

The space of Weil differentials carries a K-module structure where:
  (c · ω)(a) = ω(c · a)

This makes the evaluation pairing K-bilinear.
-/

section KModule

variable [Nonempty (HeightOneSpectrum R)]

/-- Scalar multiplication by K on Weil differentials.

For c ∈ K and ω a Weil differential, we define:
  (c · ω)(a) = ω(c · a)

This is the natural action making Hom_k(A_K, k) into a K-module,
restricted to the subspace of differentials vanishing on K.
-/
def kMul (c : K) (ω : WeilDifferential k R K K_infty) : WeilDifferential k R K K_infty :=
  ⟨{ toFun := fun a => ω (fullDiagonalEmbedding R K K_infty c * a)
     map_add' := fun a₁ a₂ => by simp [mul_add, ω.toLinearMap.map_add]
     map_smul' := fun r a => by
       simp only [RingHom.id_apply]
       -- r • a = (algebraMap k A) r * a
       have h1 : r • a = (algebraMap k (FullAdeleRing R K K_infty) r) * a := Algebra.smul_def r a
       rw [h1, algebraMap_fullAdele_eq]
       -- diag c * (diag (alg r) * a) = diag (alg r) * (diag c * a)
       -- This uses commutativity of the diagonal elements
       have h2 : fullDiagonalEmbedding R K K_infty c *
           (fullDiagonalEmbedding R K K_infty (algebraMap k K r) * a) =
           fullDiagonalEmbedding R K K_infty (algebraMap k K r) *
           (fullDiagonalEmbedding R K K_infty c * a) := by
         rw [← mul_assoc, ← mul_assoc]
         congr 1
         -- Now show diag c * diag (alg r) = diag (alg r) * diag c
         -- Both equal diag (c * alg r) = diag (alg r * c) since K is commutative
         rw [← map_mul, ← map_mul, mul_comm]
       rw [h2, ← algebraMap_fullAdele_eq, ← Algebra.smul_def, ω.toLinearMap.map_smul] },
   fun x => by
     simp only [LinearMap.coe_mk, AddHom.coe_mk]
     have h : fullDiagonalEmbedding R K K_infty c * fullDiagonalEmbedding R K K_infty x =
         fullDiagonalEmbedding R K K_infty (c * x) := by
       rw [← map_mul]
     rw [h, ω.vanishes_on_K]
  ⟩

/-- The K-SMul instance on WeilDifferential. -/
instance instSMulK : SMul K (WeilDifferential k R K K_infty) := ⟨kMul⟩

@[simp]
lemma kMul_apply (c : K) (ω : WeilDifferential k R K K_infty)
    (a : FullAdeleRing R K K_infty) :
    kMul c ω a = ω (fullDiagonalEmbedding R K K_infty c * a) := rfl

@[simp]
lemma smulK_apply (c : K) (ω : WeilDifferential k R K K_infty)
    (a : FullAdeleRing R K K_infty) :
    (c • ω) a = ω (fullDiagonalEmbedding R K K_infty c * a) := rfl

lemma one_smulK (ω : WeilDifferential k R K K_infty) :
    (1 : K) • ω = ω := by
  ext a
  simp only [smulK_apply, map_one, one_mul]

lemma mul_smulK (c₁ c₂ : K) (ω : WeilDifferential k R K K_infty) :
    (c₁ * c₂) • ω = c₁ • (c₂ • ω) := by
  ext a
  simp only [smulK_apply, map_mul]
  -- LHS: ω ((diag c₁ * diag c₂) * a)
  -- RHS: (c₁ • (c₂ • ω)) a = (c₂ • ω) (diag c₁ * a) = ω (diag c₂ * (diag c₁ * a))
  -- So we need: (diag c₁ * diag c₂) * a = diag c₂ * (diag c₁ * a)
  -- Rewrite using associativity and commutativity
  congr 1
  have hcomm : fullDiagonalEmbedding R K K_infty c₁ * fullDiagonalEmbedding R K K_infty c₂ =
      fullDiagonalEmbedding R K K_infty c₂ * fullDiagonalEmbedding R K K_infty c₁ := mul_comm _ _
  rw [hcomm, mul_assoc]

lemma smulK_add (c : K) (ω₁ ω₂ : WeilDifferential k R K K_infty) :
    c • (ω₁ + ω₂) = c • ω₁ + c • ω₂ := by
  ext a
  simp only [smulK_apply, add_apply]

lemma add_smulK (c₁ c₂ : K) (ω : WeilDifferential k R K K_infty) :
    (c₁ + c₂) • ω = c₁ • ω + c₂ • ω := by
  ext a
  simp only [smulK_apply, add_apply, map_add, add_mul, ω.toLinearMap.map_add]

lemma zero_smulK (ω : WeilDifferential k R K K_infty) :
    (0 : K) • ω = 0 := by
  ext a
  simp only [smulK_apply, map_zero, zero_mul, zero_apply]

lemma smulK_zero (c : K) :
    c • (0 : WeilDifferential k R K K_infty) = 0 := by
  ext a
  simp only [smulK_apply, zero_apply]

/-- WeilDifferential is a K-module with the action (c · ω)(a) = ω(c · a). -/
instance instModuleK : Module K (WeilDifferential k R K K_infty) where
  one_smul := one_smulK
  mul_smul := mul_smulK
  smul_add := smulK_add
  smul_zero := fun _ => smulK_zero _
  add_smul := add_smulK
  zero_smul := zero_smulK

/-- The K-module structure is compatible with the k-module structure via the scalar tower. -/
instance instIsScalarTowerKk : IsScalarTower k K (WeilDifferential k R K K_infty) := by
  constructor
  intro r c ω
  ext a
  simp only [smul_apply, smulK_apply]
  -- Goal: ω(diag(r • c) * a) = r • ω(diag c * a)
  -- In K, r • c = (algebraMap k K r) * c
  have h1 : (r • c : K) = (algebraMap k K r) * c := Algebra.smul_def r c
  rw [h1]
  have h2 : fullDiagonalEmbedding R K K_infty (algebraMap k K r * c) =
      fullDiagonalEmbedding R K K_infty (algebraMap k K r) *
      fullDiagonalEmbedding R K K_infty c := by rw [map_mul]
  rw [h2]
  have h3 : fullDiagonalEmbedding R K K_infty (algebraMap k K r) *
      fullDiagonalEmbedding R K K_infty c * a =
      fullDiagonalEmbedding R K K_infty (algebraMap k K r) *
      (fullDiagonalEmbedding R K K_infty c * a) := mul_assoc _ _ _
  rw [h3, ← algebraMap_fullAdele_eq, ← Algebra.smul_def, ω.toLinearMap.map_smul]

end KModule

/-! ## Divisor-Constrained Weil Differentials

The space Ω(D) of Weil differentials with prescribed poles/zeros.
For a divisor D, we define Ω(-D) as differentials ω such that
the local component ω_v has order ≥ -D(v) at each place v.

This is related to L(D) via Serre duality: dim Ω(-D) = dim L(K+D) where K is canonical.
-/

-- To be defined in subsequent cycles (Cycle 313+)

end WeilDifferential

end RiemannRochV2

end
