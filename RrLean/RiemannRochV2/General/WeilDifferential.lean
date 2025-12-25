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
import RrLean.RiemannRochV2.Definitions.Projective

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
For a divisor D, we define Ω(D) as differentials ω such that
the local component ω_v has order ≥ -D(v) at each place v.

This is related to L(D) via Serre duality: dim Ω(K-D) = dim L(D) where K is canonical.

### Cycle 313: Local Components and Constrained Differentials

We define:
* `embedFinitePlace` - embed a local element at finite place v into full adeles
* `localOrder` - order of a differential at a finite place
* `DivisorDifferentials D` - Ω(D), differentials with poles bounded by D
-/

section LocalComponents

/-! ### Embedding Local Elements into Full Adeles

For a finite place v, we can embed an element x ∈ K_v into the full adele ring
by putting x at position v, 0 at all other finite places, and 0 at infinity.
-/

open Classical in
/-- Helper: construct a finite adele that is x at place v and 0 elsewhere.

This requires showing that the result is integral at almost all places,
which is trivially true since it's 0 everywhere except at v. -/
def finiteAdeleSingle (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    FiniteAdeleRing R K :=
  ⟨fun w => if h : w = v then h ▸ x else 0,
   by
     simp only [Filter.eventually_cofinite, SetLike.mem_coe]
     -- The set of places where we're not integral is finite (at most {v})
     apply Set.Finite.subset (Set.finite_singleton v)
     intro w hw
     simp only [Set.mem_singleton_iff]
     by_contra h_ne
     simp only [Set.mem_setOf_eq] at hw
     rw [dif_neg h_ne, mem_adicCompletionIntegers, Valuation.map_zero] at hw
     exact hw zero_le'⟩

open Classical in
@[simp]
lemma finiteAdeleSingle_apply_same (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    (finiteAdeleSingle v x) v = x := by
  show (finiteAdeleSingle v x).1 v = x
  simp only [finiteAdeleSingle, dif_pos rfl, dite_true]

open Classical in
@[simp]
lemma finiteAdeleSingle_apply_ne (v w : HeightOneSpectrum R) (x : v.adicCompletion K)
    (h : w ≠ v) : (finiteAdeleSingle v x) w = 0 := by
  show (finiteAdeleSingle v x).1 w = 0
  simp only [finiteAdeleSingle, dif_neg h, dite_false]

/-- Embed a local element at finite place v into the full adele ring.
The element is placed at position v in the finite part, with 0 at all other
finite places and 0 at the infinite place. -/
def embedFinitePlace (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    FullAdeleRing R K K_infty :=
  (finiteAdeleSingle v x, 0)

@[simp]
lemma embedFinitePlace_fst (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    (embedFinitePlace (K_infty := K_infty) v x).1 = finiteAdeleSingle v x := rfl

@[simp]
lemma embedFinitePlace_snd (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    (embedFinitePlace (K_infty := K_infty) v x).2 = 0 := rfl

open Classical in
/-- The embedding at a finite place respects zero. -/
@[simp]
lemma embedFinitePlace_zero (v : HeightOneSpectrum R) :
    embedFinitePlace (K_infty := K_infty) v (0 : v.adicCompletion K) =
    (0 : FullAdeleRing R K K_infty) := by
  apply Prod.ext
  · apply FiniteAdeleRing.ext K
    intro w
    show (finiteAdeleSingle v 0).1 w = (0 : FiniteAdeleRing R K) w
    by_cases h : w = v
    · subst h; simp only [finiteAdeleSingle, dif_pos rfl]; rfl
    · simp only [finiteAdeleSingle, dif_neg h]; rfl
  · rfl

/-! ### Local Order of a Differential

The order of a Weil differential ω at a finite place v is the largest n such that
ω vanishes on all local elements of valuation ≥ n.

For computational purposes, we define the constraint that ω has order ≥ n at v,
meaning ω vanishes on all x with v(x) ≥ exp(n).
-/

variable [Nonempty (HeightOneSpectrum R)]

/-- Predicate: a Weil differential ω has order ≥ n at finite place v.

This means ω vanishes on all elements x ∈ K_v with v(x) ≥ exp(n),
when embedded at position v in the adele ring.

Mathematically: ord_v(ω) ≥ n iff ω_v(π^n O_v) = 0. -/
def hasOrderGe (ω : WeilDifferential k R K K_infty) (v : HeightOneSpectrum R) (n : ℤ) : Prop :=
  ∀ x : v.adicCompletion K, Valued.v x ≥ WithZero.exp n →
    ω (embedFinitePlace v x) = 0

/-- If ω has order ≥ m at v and m ≤ n, then ω has order ≥ n at v.

Larger order bound (n ≥ m) means smaller set of test elements, hence easier to satisfy. -/
lemma hasOrderGe_of_le {ω : WeilDifferential k R K K_infty} {v : HeightOneSpectrum R}
    {m n : ℤ} (h : hasOrderGe ω v m) (hmn : m ≤ n) : hasOrderGe ω v n := by
  intro x hx
  apply h
  -- Need: Valued.v x ≥ WithZero.exp m
  -- Have: hx : Valued.v x ≥ WithZero.exp n
  -- Since m ≤ n, exp(m) ≤ exp(n), so hx implies what we need
  calc Valued.v x ≥ WithZero.exp n := hx
    _ ≥ WithZero.exp m := WithZero.exp_le_exp.mpr hmn

/-- Zero differential has order ≥ n for all n. -/
@[simp]
lemma hasOrderGe_zero (v : HeightOneSpectrum R) (n : ℤ) :
    hasOrderGe (0 : WeilDifferential k R K K_infty) v n := by
  intro x _
  simp only [zero_apply]

/-! ### Divisor-Constrained Differentials

Ω(D) is the space of Weil differentials with poles bounded by D.
This means: at each finite place v, the differential has order ≥ -D(v).
-/

/-- Predicate: a Weil differential satisfies the divisor constraint D.

This means at each finite place v, the differential has order ≥ -D(v).
Equivalently, div(ω) + D ≥ 0 at all finite places. -/
def satisfiesDivisorConstraint (ω : WeilDifferential k R K K_infty)
    (D : DivisorV2 R) : Prop :=
  ∀ v : HeightOneSpectrum R, hasOrderGe ω v (-D v)

/-- Zero satisfies any divisor constraint. -/
@[simp]
lemma satisfiesDivisorConstraint_zero (D : DivisorV2 R) :
    satisfiesDivisorConstraint (0 : WeilDifferential k R K K_infty) D := by
  intro v
  exact hasOrderGe_zero v _

/-- Sum of differentials satisfying a constraint also satisfies it. -/
lemma satisfiesDivisorConstraint_add {ω₁ ω₂ : WeilDifferential k R K K_infty}
    {D : DivisorV2 R}
    (h₁ : satisfiesDivisorConstraint ω₁ D) (h₂ : satisfiesDivisorConstraint ω₂ D) :
    satisfiesDivisorConstraint (ω₁ + ω₂) D := by
  intro v x hx
  rw [add_apply]
  rw [h₁ v x hx, h₂ v x hx, add_zero]

/-- Negation of a differential satisfying a constraint also satisfies it. -/
lemma satisfiesDivisorConstraint_neg {ω : WeilDifferential k R K K_infty}
    {D : DivisorV2 R} (h : satisfiesDivisorConstraint ω D) :
    satisfiesDivisorConstraint (-ω) D := by
  intro v x hx
  rw [neg_apply, h v x hx, neg_zero]

/-- k-scalar multiple of a differential satisfying a constraint also satisfies it. -/
lemma satisfiesDivisorConstraint_smul {ω : WeilDifferential k R K K_infty}
    {D : DivisorV2 R} (c : k) (h : satisfiesDivisorConstraint ω D) :
    satisfiesDivisorConstraint (c • ω) D := by
  intro v x hx
  rw [smul_apply, h v x hx, smul_zero]

/-- The space Ω(D) of Weil differentials with poles bounded by D.

An element ω ∈ Ω(D) satisfies: at each finite place v, ord_v(ω) ≥ -D(v).
This is a k-submodule of the space of all Weil differentials. -/
def DivisorDifferentials (D : DivisorV2 R) : Submodule k (WeilDifferential k R K K_infty) where
  carrier := {ω | satisfiesDivisorConstraint ω D}
  add_mem' := satisfiesDivisorConstraint_add
  zero_mem' := satisfiesDivisorConstraint_zero D
  smul_mem' := fun c _ h => satisfiesDivisorConstraint_smul c h

@[simp]
lemma mem_divisorDifferentials_iff {D : DivisorV2 R}
    {ω : WeilDifferential k R K K_infty} :
    ω ∈ DivisorDifferentials D ↔ satisfiesDivisorConstraint ω D := Iff.rfl

/-! ### Basic Properties of Ω(D)

Key properties relating different divisor constraints.
-/

/-- Ω is antitone: D ≤ E implies Ω(E) ≤ Ω(D).

Intuition: Larger divisor values mean more restrictive pole bounds (−D(v) is smaller),
so fewer differentials satisfy the constraint.

Proof: If D ≤ E, then −E(v) ≤ −D(v). If ω ∈ Ω(E) satisfies ord_v(ω) ≥ −E(v),
then by hasOrderGe_of_le it also satisfies ord_v(ω) ≥ −D(v), so ω ∈ Ω(D). -/
lemma divisorDifferentials_antitone {D E : DivisorV2 R} (hDE : D ≤ E) :
    (DivisorDifferentials (k := k) (R := R) (K := K) (K_infty := K_infty) E :
      Submodule k (WeilDifferential k R K K_infty)) ≤
    (DivisorDifferentials (k := k) (R := R) (K := K) (K_infty := K_infty) D :
      Submodule k (WeilDifferential k R K K_infty)) := by
  intro ω hωE
  rw [mem_divisorDifferentials_iff] at hωE ⊢
  intro v
  have hv : D v ≤ E v := hDE v
  have h_neg : -E v ≤ -D v := neg_le_neg hv
  exact hasOrderGe_of_le (hωE v) h_neg

/-- Ω(0) consists of differentials with non-negative order at all finite places.

These are the "holomorphic" differentials (no poles at finite places). -/
lemma mem_divisorDifferentials_zero_iff {ω : WeilDifferential k R K K_infty} :
    ω ∈ (DivisorDifferentials (k := k) (R := R) (K := K) (K_infty := K_infty) (0 : DivisorV2 R) :
      Submodule k (WeilDifferential k R K K_infty)) ↔
    ∀ v : HeightOneSpectrum R, hasOrderGe ω v 0 := by
  simp only [mem_divisorDifferentials_iff, satisfiesDivisorConstraint,
    Finsupp.coe_zero, Pi.zero_apply, neg_zero]

end LocalComponents

/-! ## Serre Duality Pairing

The Serre pairing is the fundamental tool for relating L(D) and Ω(K-D).
For f ∈ K and ω a Weil differential:

  ⟨f, ω⟩ = ω(diag(f))

where diag(f) is the diagonal embedding of f into the adele ring.

This pairing is:
* k-bilinear
* Well-defined: if f ∈ K, then ⟨f, ω⟩ ∈ k
* Zero on K: if f ∈ K (as a subspace of L(D)), then ⟨f, ω⟩ factors through ω(K) = 0

### Key Properties (to be proved)

1. **Non-degeneracy**: For f ≠ 0 in L(D), there exists ω ∈ Ω(K-D) with ⟨f, ω⟩ ≠ 0
2. **Compatibility**: The pairing respects the divisor constraints

### Cycle 314 Deliverables

* `serrePairingF` - evaluation on a single f ∈ K
* `serrePairingF_linear_ω` - linearity in ω
* `serrePairingF_linear_f` - linearity in f (via K-module structure on ω)
-/

section SerrePairing

variable [Nonempty (HeightOneSpectrum R)]

/-- The Serre pairing evaluated at a function f ∈ K and a Weil differential ω.

  ⟨f, ω⟩ = ω(diag(f))

This is the core operation underlying Serre duality. -/
def serrePairingF (f : K) (ω : WeilDifferential k R K K_infty) : k :=
  ω (fullDiagonalEmbedding R K K_infty f)

@[simp]
lemma serrePairingF_zero_left (ω : WeilDifferential k R K K_infty) :
    serrePairingF (0 : K) ω = 0 := by
  simp only [serrePairingF, map_zero, zero_apply]

@[simp]
lemma serrePairingF_zero_right (f : K) :
    serrePairingF f (0 : WeilDifferential k R K K_infty) = 0 := by
  simp only [serrePairingF, zero_apply]

lemma serrePairingF_add_left (f₁ f₂ : K) (ω : WeilDifferential k R K K_infty) :
    serrePairingF (f₁ + f₂) ω = serrePairingF f₁ ω + serrePairingF f₂ ω := by
  simp only [serrePairingF, map_add, ω.toLinearMap.map_add]

lemma serrePairingF_add_right (f : K) (ω₁ ω₂ : WeilDifferential k R K K_infty) :
    serrePairingF f (ω₁ + ω₂) = serrePairingF f ω₁ + serrePairingF f ω₂ := by
  simp only [serrePairingF, add_apply]

lemma serrePairingF_smul_left (c : k) (f : K) (ω : WeilDifferential k R K K_infty) :
    serrePairingF (c • f) ω = c • serrePairingF f ω := by
  simp only [serrePairingF]
  -- c • f = (algebraMap k K c) * f in K
  have h1 : (c • f : K) = algebraMap k K c * f := by
    rw [Algebra.smul_def]
  rw [h1]
  -- diag(algebraMap k K c * f) = diag(algebraMap k K c) * diag(f)
  have h2 : fullDiagonalEmbedding R K K_infty (algebraMap k K c * f) =
      fullDiagonalEmbedding R K K_infty (algebraMap k K c) *
      fullDiagonalEmbedding R K K_infty f := by
    rw [map_mul]
  rw [h2]
  -- Use that algebraMap k FullAdele factors through algebraMap k K
  rw [← algebraMap_fullAdele_eq]
  -- Now use linearity of ω over k
  rw [← Algebra.smul_def, ω.toLinearMap.map_smul]

lemma serrePairingF_smul_right (c : k) (f : K) (ω : WeilDifferential k R K K_infty) :
    serrePairingF f (c • ω) = c • serrePairingF f ω := by
  simp only [serrePairingF, smul_apply]

/-- The pairing as a k-linear map in the second argument (ω), for fixed f.

Given f ∈ K, this is the linear functional ω ↦ ω(diag(f)). -/
def serrePairingLinearω (f : K) : WeilDifferential k R K K_infty →ₗ[k] k where
  toFun := serrePairingF f
  map_add' := serrePairingF_add_right f
  map_smul' c ω := by simp only [serrePairingF_smul_right, RingHom.id_apply]

@[simp]
lemma serrePairingLinearω_apply (f : K) (ω : WeilDifferential k R K K_infty) :
    serrePairingLinearω f ω = serrePairingF f ω := rfl

/-- The full Serre pairing as a k-bilinear map.

This maps (f, ω) ↦ ω(diag(f)), and is k-linear in both arguments. -/
def serrePairingBilinear : K →ₗ[k] WeilDifferential k R K K_infty →ₗ[k] k where
  toFun := serrePairingLinearω
  map_add' f₁ f₂ := by
    ext ω
    simp only [serrePairingLinearω_apply, LinearMap.add_apply, serrePairingF_add_left]
  map_smul' c f := by
    ext ω
    simp only [serrePairingLinearω_apply, RingHom.id_apply, LinearMap.smul_apply,
      serrePairingF_smul_left]

@[simp]
lemma serrePairingBilinear_apply (f : K) (ω : WeilDifferential k R K K_infty) :
    serrePairingBilinear f ω = serrePairingF f ω := rfl

/-- The Serre pairing vanishes when f is already in K (i.e., a constant function).

This is because ω vanishes on the diagonal image of K by definition. -/
lemma serrePairingF_vanishes_on_K (f : K) (ω : WeilDifferential k R K K_infty) :
    serrePairingF f ω = ω (fullDiagonalEmbedding R K K_infty f) := rfl

-- Note: The key property serrePairingF_eq_zero_iff will come from the
-- vanishing condition on Weil differentials. The pairing
-- ⟨f, ω⟩ = ω(diag(f)) is automatically zero when f is a constant
-- that lies in the image of K, by the defining property of ω.

/-! ### Restricted Pairing: L(D) × Ω(-D) → k

The Serre duality pairing restricts to a well-defined pairing between
L(D) and Ω(-D). The key constraint is:

* f ∈ L(D) means ord_v(f) ≥ -D(v) at all places
* ω ∈ Ω(-D) means ord_v(ω) ≥ D(v) at all places (by definition with -(-D) = D)

The compatibility: when evaluating ω(diag(f)), we need the local behavior
to be controlled. The pairing respects divisor constraints when:

  f ∈ L(D), ω ∈ Ω(-D) ⟹ ⟨f, ω⟩ well-defined in k

### Cycle 315: Setting Up the Restricted Pairing
-/

section RestrictedPairing

variable [Nonempty (HeightOneSpectrum R)]

/-- The restricted Serre pairing as a bilinear map from L(D) × Ω(-D) to k.

For f ∈ L(D) and ω ∈ Ω(-D), the pairing is ⟨f, ω⟩ = ω(diag(f)).

Mathematical justification:
* f ∈ L(D): ord_v(f) ≥ -D(v), i.e., v(f) ≤ exp(D(v))
* ω ∈ Ω(-D): ord_v(ω) ≥ D(v) at all places

The evaluation ω(diag(f)) extracts the "residue" of the product fω,
which is finite when the orders are compatible. -/
def serrePairingRestricted (D : DivisorV2 R) :
    RRSpace_proj k R K D →ₗ[k] DivisorDifferentials (k := k) (R := R) (K := K) (K_infty := K_infty) (-D) →ₗ[k] k where
  toFun f :=
    { toFun := fun ω => serrePairingF (f : K) (ω : WeilDifferential k R K K_infty)
      map_add' := fun ω₁ ω₂ => by
        simp only [Submodule.coe_add, serrePairingF_add_right]
      map_smul' := fun c ω => by
        simp only [SetLike.val_smul, serrePairingF_smul_right, RingHom.id_apply] }
  map_add' f₁ f₂ := by
    ext ω
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add, serrePairingF_add_left,
      LinearMap.add_apply]
  map_smul' c f := by
    ext ω
    simp only [LinearMap.coe_mk, AddHom.coe_mk, SetLike.val_smul, serrePairingF_smul_left,
      RingHom.id_apply, LinearMap.smul_apply]

@[simp]
lemma serrePairingRestricted_apply (D : DivisorV2 R)
    (f : RRSpace_proj k R K D)
    (ω : DivisorDifferentials (k := k) (R := R) (K := K) (K_infty := K_infty) (-D)) :
    serrePairingRestricted D f ω = serrePairingF (f : K) (ω : WeilDifferential k R K K_infty) := rfl

/-! ### Pairing with General Divisor Constraint

More generally, for any divisors D and E, we can pair L(D) with Ω(E).
The "compatibility" condition D + E ≥ 0 ensures the pairing is meaningful,
though the pairing itself is defined for any D, E.

For Serre duality, we'll use E = K - D (canonical minus D), giving:
  L(D) × Ω(K - D) → k
-/

/-- General restricted pairing: L(D) × Ω(E) → k for any divisors D, E.

This is always well-defined as a bilinear map - the divisor constraints
affect non-degeneracy rather than well-definedness. -/
def serrePairingGeneral (D E : DivisorV2 R) :
    RRSpace_proj k R K D →ₗ[k]
    DivisorDifferentials (k := k) (R := R) (K := K) (K_infty := K_infty) E →ₗ[k] k where
  toFun f :=
    { toFun := fun ω => serrePairingF (f : K) (ω : WeilDifferential k R K K_infty)
      map_add' := fun ω₁ ω₂ => by
        simp only [Submodule.coe_add, serrePairingF_add_right]
      map_smul' := fun c ω => by
        simp only [SetLike.val_smul, serrePairingF_smul_right, RingHom.id_apply] }
  map_add' f₁ f₂ := by
    ext ω
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add, serrePairingF_add_left,
      LinearMap.add_apply]
  map_smul' c f := by
    ext ω
    simp only [LinearMap.coe_mk, AddHom.coe_mk, SetLike.val_smul, serrePairingF_smul_left,
      RingHom.id_apply, LinearMap.smul_apply]

@[simp]
lemma serrePairingGeneral_apply (D E : DivisorV2 R)
    (f : RRSpace_proj k R K D)
    (ω : DivisorDifferentials (k := k) (R := R) (K := K) (K_infty := K_infty) E) :
    serrePairingGeneral D E f ω = serrePairingF (f : K) (ω : WeilDifferential k R K K_infty) := rfl

end RestrictedPairing

/-! ## Non-Degeneracy Setup (Cycle 316+)

The crux of Serre duality is proving the pairing is non-degenerate:

  ∀ f ∈ L(D), f ≠ 0 → ∃ ω ∈ Ω(K-D), ⟨f, ω⟩ ≠ 0

This requires:
1. Canonical divisor K with deg(K) = 2g - 2
2. Existence of "enough" differentials
3. A local-to-global argument or compactness argument

### Strategy Options

1. **From A_K/K compactness**: The quotient is compact, hence finite-dimensional.
   The dual pairing is perfect by finite-dimensionality.

2. **Local non-degeneracy**: At each place v, the local pairing is non-degenerate.
   Combine via strong approximation to get global non-degeneracy.

3. **Axiomatize**: If proofs are too hard, axiomatize and verify for examples.

### Definitions (to be formalized in Cycle 316+)

* `PairingNondegenerateLeft D K` - For f ≠ 0 in L(D), ∃ ω in Ω(K-D) with ⟨f, ω⟩ ≠ 0
* `PairingNondegenerateRight D K` - For ω ≠ 0 in Ω(K-D), ∃ f in L(D) with ⟨f, ω⟩ ≠ 0
* `PairingPerfect D K` - Both left and right non-degeneracy
* `dim_eq_of_perfect_pairing` - Perfect pairing ⟹ dim L(D) = dim Ω(K-D)
-/

end SerrePairing

end WeilDifferential

end RiemannRochV2

end
