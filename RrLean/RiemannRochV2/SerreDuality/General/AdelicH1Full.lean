import RrLean.RiemannRochV2.Adelic.FullAdelesBase
import RrLean.RiemannRochV2.Adelic.AdelicH1v2
import RrLean.RiemannRochV2.SerreDuality.RatFuncResidues
import RrLean.RiemannRochV2.SerreDuality.P1Specific.RatFuncPairing
import RrLean.RiemannRochV2.P1Instance.P1VanishingLKD
import RrLean.RiemannRochV2.P1Instance.PlaceDegree

/-!
# Adelic H¹(D) using Full Adele Ring

This module defines H¹(D) using the **full adele ring** (finite adeles × K_∞)
instead of just finite adeles.

## The Dimension Gap Problem (Cycle 207-208)

The "affine" H¹(D) using FiniteAdeleRing has a fundamental problem:
- Strong approximation → K + A_K(D) = FiniteAdeleRing for any D
- Therefore h¹_affine(D) = 0 for all D

But Serre duality h¹(D) = ℓ(K-D) requires non-trivial H¹ when L(K-D) ≠ 0:
- For D = K (canonical), h¹(K) should equal ℓ(0) = 1
- The affine version gives h¹(K) = 0 ≠ 1

## The Solution: Full Adele Ring

By using FullAdeleRing = FiniteAdeleRing × K_∞, we capture the infinity constraint:
- The bounded condition A_K(D) must also bound the infinity component
- The global pairing uses residueSumTotal (finite + ∞)
- The residue theorem ∑_{all v} res_v(k) = 0 gives well-definedness

## Main Definitions

* `boundedSubmodule_full` : A_K(D) ⊆ FullAdeleRing (includes infinity bound)
* `globalSubmodule_full` : K diagonally embedded in FullAdeleRing
* `globalPlusBoundedSubmodule_full` : K + A_K(D) in FullAdeleRing
* `SpaceModule_full` : H¹(D) = FullAdeleRing / (K + A_K(D))

## References

* Weil "Basic Number Theory" Ch. IV
* Serre "Algebraic Groups and Class Fields" Ch. 1
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open RiemannRochV2.FullAdeles
open scoped Classical

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-! ## Full Adelic Bounded Submodule

A_K(D) in the full adele ring includes bounds at both:
1. Finite places: v(a_v) ≤ exp(D(v))
2. Infinity: |a_∞|_∞ ≤ exp(-D(∞))

For divisors D on P¹, we need to extend D to include infinity.
-/

section BoundedFull

/-- Extended divisor with explicit infinity coefficient.
For RatFunc Fq, D.inftyCoeff represents the order at infinity. -/
structure ExtendedDivisor (R : Type*) [CommRing R] [IsDedekindDomain R] where
  /-- The finite part (divisor on finite places). -/
  finite : DivisorV2 R
  /-- The coefficient at infinity. -/
  inftyCoeff : ℤ

namespace ExtendedDivisor

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The degree of an extended divisor. -/
def deg (D : ExtendedDivisor R) : ℤ :=
  D.finite.deg + D.inftyCoeff

/-- Convert a DivisorV2 to ExtendedDivisor with inftyCoeff = 0. -/
def ofFinite (D : DivisorV2 R) : ExtendedDivisor R :=
  ⟨D, 0⟩

/-- Zero extended divisor. -/
protected def zero : ExtendedDivisor R :=
  ⟨0, 0⟩

instance : Zero (ExtendedDivisor R) := ⟨ExtendedDivisor.zero⟩

/-- Negation. -/
protected def neg (D : ExtendedDivisor R) : ExtendedDivisor R :=
  ⟨-D.finite, -D.inftyCoeff⟩

instance : Neg (ExtendedDivisor R) := ⟨ExtendedDivisor.neg⟩

/-- Addition. -/
protected def add (D E : ExtendedDivisor R) : ExtendedDivisor R :=
  ⟨D.finite + E.finite, D.inftyCoeff + E.inftyCoeff⟩

instance : Add (ExtendedDivisor R) := ⟨ExtendedDivisor.add⟩

/-- Subtraction. -/
protected def sub (D E : ExtendedDivisor R) : ExtendedDivisor R :=
  ⟨D.finite - E.finite, D.inftyCoeff - E.inftyCoeff⟩

instance : Sub (ExtendedDivisor R) := ⟨ExtendedDivisor.sub⟩

@[simp]
lemma sub_finite (D E : ExtendedDivisor R) : (D - E).finite = D.finite - E.finite := rfl

@[simp]
lemma sub_inftyCoeff (D E : ExtendedDivisor R) :
    (D - E).inftyCoeff = D.inftyCoeff - E.inftyCoeff := rfl

@[simp]
lemma deg_sub (D E : ExtendedDivisor R) : (D - E).deg = D.deg - E.deg := by
  simp only [deg, sub_finite, sub_inftyCoeff]
  -- Use finite deg_sub via add_neg pattern
  rw [sub_eq_add_neg, DivisorV2.deg_add, DivisorV2.deg_neg]
  ring

end ExtendedDivisor

/-- The canonical extended divisor for P¹ over Fq.
For P¹, the canonical divisor is K = -2·[∞], i.e., finite part = 0, inftyCoeff = -2. -/
def canonicalExtended : ExtendedDivisor (Polynomial Fq) :=
  ⟨0, -2⟩

/-- Check that a full adele element satisfies the bound at infinity.
For (a_fin, a_∞) ∈ FullAdeleRing, we require |a_∞|_∞ ≤ exp(n). -/
def satisfiesInftyBound (a : FqFullAdeleRing Fq) (n : ℤ) : Prop :=
  Valued.v a.2 ≤ WithZero.exp n

/-- The set of full adeles bounded by extended divisor D.
A_K(D) = { a ∈ FullAdeleRing | v(a_v) ≤ exp(D.finite(v)) for finite v,
                               |a_∞|_∞ ≤ exp(D.inftyCoeff) } -/
def boundedSubset_full (D : ExtendedDivisor (Polynomial Fq)) : Set (FqFullAdeleRing Fq) :=
  { a | (∀ v, AdelicH1v2.satisfiesBoundAt (Polynomial Fq) (RatFunc Fq) a.1 v D.finite) ∧
        satisfiesInftyBound Fq a D.inftyCoeff }

/-- Zero is in A_K(D) for any D. -/
lemma zero_mem_boundedSubset_full (D : ExtendedDivisor (Polynomial Fq)) :
    (0 : FqFullAdeleRing Fq) ∈ boundedSubset_full Fq D := by
  constructor
  · intro v
    exact AdelicH1v2.zero_mem_boundedSubset (Polynomial Fq) (RatFunc Fq) D.finite v
  · show Valued.v (0 : FqFullAdeleRing Fq).2 ≤ WithZero.exp D.inftyCoeff
    simp only [Prod.snd_zero, Valuation.map_zero]
    exact WithZero.zero_le _

/-- A_K(D) is closed under addition. -/
lemma add_mem_boundedSubset_full {D : ExtendedDivisor (Polynomial Fq)}
    {a b : FqFullAdeleRing Fq}
    (ha : a ∈ boundedSubset_full Fq D) (hb : b ∈ boundedSubset_full Fq D) :
    a + b ∈ boundedSubset_full Fq D := by
  constructor
  · intro v
    -- Use the existing add_mem lemma for finite part
    exact AdelicH1v2.add_mem_boundedSubset (Polynomial Fq) (RatFunc Fq) (ha.1) (hb.1) v
  · -- Infinity part: ultrametric inequality
    show Valued.v (a + b).2 ≤ WithZero.exp D.inftyCoeff
    calc Valued.v (a + b).2
        = Valued.v (a.2 + b.2) := rfl
      _ ≤ max (Valued.v a.2) (Valued.v b.2) := Valuation.map_add_le_max' _ _ _
      _ ≤ WithZero.exp D.inftyCoeff := max_le ha.2 hb.2

/-- A_K(D) is closed under negation. -/
lemma neg_mem_boundedSubset_full {D : ExtendedDivisor (Polynomial Fq)}
    {a : FqFullAdeleRing Fq} (ha : a ∈ boundedSubset_full Fq D) :
    -a ∈ boundedSubset_full Fq D := by
  constructor
  · intro v
    exact AdelicH1v2.neg_mem_boundedSubset (Polynomial Fq) (RatFunc Fq) (ha.1) v
  · show Valued.v (-a).2 ≤ WithZero.exp D.inftyCoeff
    rw [show (-a).2 = -a.2 from rfl, Valuation.map_neg]
    exact ha.2

/-- A_K(D) as an additive subgroup of FullAdeleRing. -/
def boundedAddSubgroup_full (D : ExtendedDivisor (Polynomial Fq)) :
    AddSubgroup (FqFullAdeleRing Fq) where
  carrier := boundedSubset_full Fq D
  add_mem' := add_mem_boundedSubset_full Fq
  zero_mem' := zero_mem_boundedSubset_full Fq D
  neg_mem' := neg_mem_boundedSubset_full Fq

-- FullAdeleRing needs an Fq-module structure for scalar multiplication
-- We define it via the diagonal embedding

/-- Scalar multiplication on FqFullAdeleRing: c • a = diag(c) * a where diag(c) is the
diagonal embedding of c ∈ Fq viewed as a constant in RatFunc Fq. -/
instance instSMulFqFullAdele : SMul Fq (FqFullAdeleRing Fq) :=
  ⟨fun c a => fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) c) * a⟩

/-- The Fq-module structure on FqFullAdeleRing. -/
instance instModuleFqFullAdele : Module Fq (FqFullAdeleRing Fq) where
  one_smul := fun a => by
    show fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) 1) * a = a
    simp only [map_one, one_mul]
  mul_smul := fun c d a => by
    show fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) (c * d)) * a =
         fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) c) *
         (fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) d) * a)
    simp only [map_mul, mul_assoc]
  smul_zero := fun c => by
    show fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) c) * 0 = 0
    simp only [mul_zero]
  smul_add := fun c a b => by
    show fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) c) * (a + b) =
         fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) c) * a +
         fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) c) * b
    simp only [mul_add]
  add_smul := fun c d a => by
    show fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) (c + d)) * a =
         fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) c) * a +
         fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) d) * a
    simp only [map_add, add_mul]
  zero_smul := fun a => by
    show fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) 0) * a = 0
    simp only [map_zero, zero_mul]

/-- A_K(D) is closed under Fq-scalar multiplication. -/
lemma smul_mem_boundedSubset_full (D : ExtendedDivisor (Polynomial Fq))
    (c : Fq) {a : FqFullAdeleRing Fq} (ha : a ∈ boundedSubset_full Fq D) :
    c • a ∈ boundedSubset_full Fq D := by
  constructor
  · intro v
    -- (c • a).1 = (diag(c) * a).1 = diag(c).1 * a.1
    -- Show this equals c • a.1 using scalar tower
    have heq : (c • a).1 = c • a.1 := by
      -- c • a = fqFullDiagonalEmbedding (algebraMap c) * a
      show (fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) c) * a).1 = c • a.1
      -- Product multiplication is componentwise
      rw [show (fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) c) * a).1 =
              (fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) c)).1 * a.1 from rfl]
      -- diag.1 = FiniteAdeleRing.algebraMap = algebraMap (RatFunc Fq) (FiniteAdeleRing ...)
      rw [Algebra.smul_def]
      -- Use scalar tower: algebraMap Fq (FiniteAdeleRing) = algebraMap K ∘ algebraMap Fq K
      rw [IsScalarTower.algebraMap_apply Fq (RatFunc Fq) (FiniteAdeleRing (Polynomial Fq) (RatFunc Fq))]
      rfl
    rw [heq]
    exact AdelicH1v2.smul_mem_boundedSubset Fq (Polynomial Fq) (RatFunc Fq) D.finite c (ha.1) v
  · -- Infinity part: Valued.v (c • a).2 ≤ exp(D.inftyCoeff)
    show Valued.v (c • a).2 ≤ WithZero.exp D.inftyCoeff
    -- (c • a).2 = diag(c).2 * a.2
    have heq : (c • a).2 = (fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) c)).2 * a.2 := rfl
    rw [heq, Valuation.map_mul]
    -- Constants have valuation ≤ 1 at infinity
    have hc_val : Valued.v (fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) c)).2 ≤ 1 := by
      by_cases hc : c = 0
      · subst hc
        -- c = 0, so algebraMap 0 = 0, and diag(0) = 0
        simp only [map_zero, Prod.snd_zero, Valuation.map_zero]
        exact WithZero.zero_le (1 : WithZero (Multiplicative ℤ))
      · -- For nonzero c, use diag_infty_valuation and FunctionField.inftyValuation.C
        rw [FullAdeles.diag_infty_valuation Fq (algebraMap Fq (RatFunc Fq) c)]
        -- algebraMap Fq (RatFunc Fq) c = RatFunc.C c
        have halg : algebraMap Fq (RatFunc Fq) c = RatFunc.C c := rfl
        rw [halg, ← FunctionField.inftyValuation_apply]
        rw [FunctionField.inftyValuation.C Fq hc]
    calc Valued.v (fqFullDiagonalEmbedding Fq (algebraMap Fq (RatFunc Fq) c)).2 * Valued.v (a.2)
        ≤ 1 * Valued.v (a.2) := by
          apply mul_le_mul_of_nonneg_right hc_val (WithZero.zero_le _)
      _ = Valued.v (a.2) := one_mul _
      _ ≤ WithZero.exp D.inftyCoeff := ha.2

/-- A_K(D) as an Fq-submodule of FullAdeleRing. -/
def boundedSubmodule_full (D : ExtendedDivisor (Polynomial Fq)) :
    Submodule Fq (FqFullAdeleRing Fq) where
  carrier := boundedSubset_full Fq D
  add_mem' := add_mem_boundedSubset_full Fq
  zero_mem' := zero_mem_boundedSubset_full Fq D
  smul_mem' := smul_mem_boundedSubset_full Fq D

end BoundedFull

/-! ## Global Submodule in Full Adeles -/

section GlobalFull

/-- The set of global elements in FullAdeleRing.
Elements of the form (diag(k), k) for k ∈ K. -/
def globalSubset_full : Set (FqFullAdeleRing Fq) :=
  Set.range (fqFullDiagonalEmbedding Fq)

/-- The diagonal of K is an additive subgroup in FullAdeleRing. -/
def globalAddSubgroup_full : AddSubgroup (FqFullAdeleRing Fq) where
  carrier := globalSubset_full Fq
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ x y⟩
  zero_mem' := ⟨0, map_zero _⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, map_neg _ x⟩

/-- The diagonal of K is closed under Fq-scalar multiplication. -/
lemma smul_mem_globalSubset_full (c : Fq) {a : FqFullAdeleRing Fq}
    (ha : a ∈ globalSubset_full Fq) : c • a ∈ globalSubset_full Fq := by
  obtain ⟨k, rfl⟩ := ha
  use c • k
  -- Goal: fqFullDiagonalEmbedding Fq (c • k) = c • fqFullDiagonalEmbedding Fq k
  -- c • diag(k) = diag(algebraMap c) * diag(k) by definition of SMul
  -- = diag(algebraMap c * k) by map_mul
  -- = diag(c • k) by Algebra.smul_def on RatFunc Fq
  rw [Algebra.smul_def]
  -- Goal: diag(algebraMap c * k) = diag(algebraMap c) * diag(k)
  exact map_mul (fqFullDiagonalEmbedding Fq) (algebraMap Fq (RatFunc Fq) c) k

/-- The diagonal of K as an Fq-submodule of FullAdeleRing. -/
def globalSubmodule_full : Submodule Fq (FqFullAdeleRing Fq) where
  carrier := globalSubset_full Fq
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ x y⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := smul_mem_globalSubset_full Fq

end GlobalFull

/-! ## H¹(D) using Full Adeles -/

section H1Full

/-- K + A_K(D) as an Fq-submodule of FullAdeleRing. -/
def globalPlusBoundedSubmodule_full (D : ExtendedDivisor (Polynomial Fq)) :
    Submodule Fq (FqFullAdeleRing Fq) :=
  globalSubmodule_full Fq + boundedSubmodule_full Fq D

/-- H¹(D) = FullAdeleRing / (K + A_K(D)) as an Fq-module quotient.
This is the mathematically correct definition that captures infinity. -/
abbrev SpaceModule_full (D : ExtendedDivisor (Polynomial Fq)) : Type _ :=
  (FqFullAdeleRing Fq) ⧸ (globalPlusBoundedSubmodule_full Fq D)

/-- The quotient map from FullAdeleRing to H¹(D). -/
def quotientMapLinear_full (D : ExtendedDivisor (Polynomial Fq)) :
    FqFullAdeleRing Fq →ₗ[Fq] SpaceModule_full Fq D :=
  Submodule.mkQ (globalPlusBoundedSubmodule_full Fq D)

/-- Global elements map to zero in H¹(D). -/
lemma quotientMapLinear_full_of_global (D : ExtendedDivisor (Polynomial Fq))
    (k : RatFunc Fq) : quotientMapLinear_full Fq D (fqFullDiagonalEmbedding Fq k) = 0 := by
  unfold quotientMapLinear_full
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  apply Submodule.mem_sup_left
  exact ⟨k, rfl⟩

/-- The dimension h¹(D) for full adelic H¹. -/
def h1_finrank_full (D : ExtendedDivisor (Polynomial Fq)) : ℕ :=
  Module.finrank Fq (SpaceModule_full Fq D)

end H1Full

/-! ## Projective L(D) with Infinity Constraint

This connects the projective L(D) from RatFuncPairing to the full adelic H¹.
-/

section ProjectiveLD

/-- L_proj(D) - Riemann-Roch space with infinity constraint.
f ∈ L_proj(D) iff:
1. v(f) ≤ exp(D.finite(v)) for all finite v (poles bounded by D)
2. deg(num) ≤ deg(denom) + D.inftyCoeff (controlled pole at ∞)

For extended divisor D with D.inftyCoeff = 0:
L_proj(0) = { f | integral at finite places, deg(num) ≤ deg(denom) } = constants

Note: Uses `f = 0 ∨ ...` pattern to handle zero element correctly (v(0) = 0 is bottom).
-/
def RRSpace_proj_ext (D : ExtendedDivisor (Polynomial Fq)) :
    Submodule Fq (RatFunc Fq) where
  carrier := { f | f = 0 ∨
                   ((∀ v, v.valuation (RatFunc Fq) f ≤ WithZero.exp (D.finite v)) ∧
                    (f.num.natDegree : ℤ) ≤ (f.denom.natDegree : ℤ) + D.inftyCoeff) }
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro a b ha hb
    by_cases h : a + b = 0
    · exact Or.inl h
    · right
      constructor
      · intro v
        rcases ha with rfl | ⟨ha_val, _⟩
        · simp only [zero_add] at h ⊢
          rcases hb with rfl | ⟨hb_val, _⟩
          · exact absurd rfl h
          · exact hb_val v
        rcases hb with rfl | ⟨hb_val, _⟩
        · simp only [add_zero]
          exact ha_val v
        -- Both a and b are nonzero with valuation bounds: use ultrametric
        calc v.valuation (RatFunc Fq) (a + b)
            ≤ max (v.valuation (RatFunc Fq) a) (v.valuation (RatFunc Fq) b) :=
              Valuation.map_add_le_max' _ a b
          _ ≤ WithZero.exp (D.finite v) := max_le (ha_val v) (hb_val v)
      · -- Degree bound for sum: need num(a+b).natDegree ≤ denom(a+b).natDegree + D.inftyCoeff
        -- Handle zero cases first
        by_cases ha_zero : a = 0
        · subst ha_zero; simp only [zero_add] at h ⊢
          rcases hb with rfl | ⟨_, hb_deg⟩
          · exact absurd rfl h
          · exact hb_deg
        by_cases hb_zero : b = 0
        · subst hb_zero; simp only [add_zero]
          rcases ha with rfl | ⟨_, ha_deg⟩
          · exact absurd rfl ha_zero
          · exact ha_deg
        -- Both a ≠ 0 and b ≠ 0: use RatFunc.intDegree_add_le
        -- Extract degree bounds from ha and hb
        have ha_deg : (a.num.natDegree : ℤ) ≤ (a.denom.natDegree : ℤ) + D.inftyCoeff := by
          rcases ha with rfl | ⟨_, ha_deg⟩
          · exact absurd rfl ha_zero
          · exact ha_deg
        have hb_deg : (b.num.natDegree : ℤ) ≤ (b.denom.natDegree : ℤ) + D.inftyCoeff := by
          rcases hb with rfl | ⟨_, hb_deg⟩
          · exact absurd rfl hb_zero
          · exact hb_deg
        -- Convert to intDegree form
        have ha_int : a.intDegree ≤ D.inftyCoeff := by
          simp only [RatFunc.intDegree]; omega
        have hb_int : b.intDegree ≤ D.inftyCoeff := by
          simp only [RatFunc.intDegree]; omega
        -- Apply intDegree_add_le
        have hab_int : (a + b).intDegree ≤ D.inftyCoeff := by
          calc (a + b).intDegree
              ≤ max a.intDegree b.intDegree := RatFunc.intDegree_add_le hb_zero h
            _ ≤ D.inftyCoeff := max_le ha_int hb_int
        -- Convert back to num/denom form
        simp only [RatFunc.intDegree] at hab_int; omega
  smul_mem' := by
    intro c f hf
    by_cases hcf : c • f = 0
    · exact Or.inl hcf
    · right
      constructor
      · intro v
        rcases hf with rfl | ⟨hf_val, _⟩
        · exfalso; apply hcf; simp only [smul_zero]
        -- v(c • f) = v(algebraMap c * f) = v(algebraMap c) * v(f) ≤ 1 * exp(D(v))
        simp only [Algebra.smul_def]
        rw [(v.valuation (RatFunc Fq)).map_mul]
        have hf_v := hf_val v
        -- Need: v(algebraMap c) ≤ 1 for c ∈ Fq (constants have no zeros/poles at finite places)
        have hc_val : v.valuation (RatFunc Fq) (algebraMap Fq (RatFunc Fq) c) ≤ 1 := by
          -- algebraMap Fq (RatFunc Fq) factors: Fq → Polynomial Fq → RatFunc Fq
          rw [IsScalarTower.algebraMap_apply Fq (Polynomial Fq) (RatFunc Fq)]
          -- Now use HeightOneSpectrum.valuation_le_one for the Polynomial Fq element
          exact HeightOneSpectrum.valuation_le_one v (algebraMap Fq (Polynomial Fq) c)
        calc v.valuation (RatFunc Fq) (algebraMap Fq (RatFunc Fq) c) * v.valuation (RatFunc Fq) f
            ≤ 1 * v.valuation (RatFunc Fq) f := by
              apply mul_le_mul_of_nonneg_right hc_val (WithZero.zero_le _)
          _ = v.valuation (RatFunc Fq) f := one_mul _
          _ ≤ WithZero.exp (D.finite v) := hf_v
      · -- Degree preserved by scalar mult
        -- Handle f = 0 case first
        by_cases hf_zero : f = 0
        · subst hf_zero; exfalso; apply hcf; simp only [smul_zero]
        -- Now f ≠ 0, extract degree bound
        have hf_deg : (f.num.natDegree : ℤ) ≤ (f.denom.natDegree : ℤ) + D.inftyCoeff := by
          rcases hf with rfl | ⟨_, hf_deg⟩
          · exact absurd rfl hf_zero
          · exact hf_deg
        -- c • f = algebraMap c * f = RatFunc.C c * f
        -- For c ≠ 0: intDegree(c • f) = intDegree(C c) + intDegree(f) = 0 + intDegree(f)
        have hc_ne : c ≠ 0 := by
          rintro rfl; apply hcf; simp only [zero_smul]
        have hCc_ne : RatFunc.C c ≠ (0 : RatFunc Fq) := by
          simp only [ne_eq, map_eq_zero]; exact hc_ne
        -- Convert hf_deg to intDegree form
        have hf_int : f.intDegree ≤ D.inftyCoeff := by
          simp only [RatFunc.intDegree]; omega
        -- Compute intDegree of c • f
        have hsmul_eq : c • f = RatFunc.C c * f := by
          simp only [Algebra.smul_def]; rfl
        have hsmul_int : (c • f).intDegree = f.intDegree := by
          rw [hsmul_eq, RatFunc.intDegree_mul hCc_ne hf_zero, RatFunc.intDegree_C, zero_add]
        -- Goal: (c • f).num.natDegree ≤ (c • f).denom.natDegree + D.inftyCoeff
        have goal_int : (c • f).intDegree ≤ D.inftyCoeff := by
          rw [hsmul_int]; exact hf_int
        simp only [RatFunc.intDegree] at goal_int; omega

/-- The dimension ℓ_proj(D) for extended divisor. -/
def ell_proj_ext (D : ExtendedDivisor (Polynomial Fq)) : ℕ :=
  Module.finrank Fq (RRSpace_proj_ext Fq D)

end ProjectiveLD

/-! ## Serre Pairing with Full Adeles

The pairing ⟨[a], f⟩ = ∑_v res_v(a_v · f) uses residueSumTotal.
-/

section SerrePairingFull

/-- For diagonal elements, the full pairing reduces to residueSumTotal. -/
def serrePairing_diagonal (k f : RatFunc Fq) : Fq :=
  residueSumTotal (k * f)

/-- The diagonal pairing is bilinear (left additivity). -/
theorem serrePairing_diagonal_add_left (k₁ k₂ f : RatFunc Fq) :
    serrePairing_diagonal Fq (k₁ + k₂) f =
      serrePairing_diagonal Fq k₁ f + serrePairing_diagonal Fq k₂ f := by
  unfold serrePairing_diagonal
  rw [add_mul]
  exact residueSumTotal_add (k₁ * f) (k₂ * f)

/-- For k ∈ K with split denominator, the pairing vanishes.
This is the residue theorem: ∑_v res_v(k · f) = 0. -/
theorem serrePairing_diagonal_vanishes_split (k f : RatFunc Fq)
    (h : ∃ (p : Polynomial Fq) (poles : Finset Fq),
         k * f = (algebraMap _ (RatFunc Fq) p) /
                 (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    serrePairing_diagonal Fq k f = 0 :=
  residueSumTotal_splits (k * f) h

end SerrePairingFull

/-! ## Key Properties

These will be proved in subsequent cycles:

1. h¹_full(D) is finite-dimensional
2. For deg(D) >> 0, h¹_full(D) = 0
3. Serre duality: h¹_full(D) = ℓ_proj(K - D)
4. Well-definedness of pairing on quotient
-/

section KeyProperties

/-- The canonical extended divisor for P¹: K = -2·[∞]. -/
theorem deg_canonical_extended : (canonicalExtended Fq).deg = -2 := by
  unfold canonicalExtended ExtendedDivisor.deg
  simp only [DivisorV2.deg_zero, zero_add]

/-- For P¹ over Fq, genus = 0. -/
def genus_P1 : ℕ := 0

/-- deg(K) = 2g - 2 = -2 for P¹. -/
theorem deg_canonical_eq_2g_minus_2 :
    (canonicalExtended Fq).deg = 2 * (genus_P1 : ℤ) - 2 := by
  simp only [deg_canonical_extended, genus_P1, Nat.cast_zero, mul_zero, zero_sub]

end KeyProperties

/-! ## Full Strong Approximation

These lemmas extend strong approximation to handle both finite and infinite places.
-/

section FullStrongApproximation

open RiemannRochV2.FullAdeles FunctionField

/-- Local approximation at infinity with arbitrary bounds.

For any element of FqtInfty and any bound n, there exists k ∈ K with |a - k|_∞ ≤ exp(n).
This follows from density of K in FqtInfty plus the fact that closed balls are clopen
in valued rings.
-/
lemma exists_local_approximant_with_bound_infty (a : FqtInfty Fq) (n : ℤ) :
    ∃ k : RatFunc Fq, Valued.v (a - inftyRingHom Fq k) ≤ WithZero.exp n := by
  -- The closed ball {x : Valued.v x ≤ exp(n)} is open in valued rings
  have h_exp_ne : (WithZero.exp n : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  have hopen : IsOpen {x : FqtInfty Fq | Valued.v (a - x) ≤ WithZero.exp n} := by
    have h_ball_open : IsOpen {x : FqtInfty Fq | Valued.v x ≤ WithZero.exp n} := by
      -- Use the clopen ball property for valued rings
      -- isClopen_closedBall takes (R : Type) explicit and (hr : r ≠ 0) explicit
      exact (Valued.isClopen_closedBall (R := FqtInfty Fq) h_exp_ne).isOpen
    have h_eq : {x : FqtInfty Fq | Valued.v (a - x) ≤ WithZero.exp n} =
        (fun y => a - y) ⁻¹' {y | Valued.v y ≤ WithZero.exp n} := by
      ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [h_eq]
    exact h_ball_open.preimage (by continuity)
  -- This set is non-empty (contains a)
  have hne : a ∈ {x : FqtInfty Fq | Valued.v (a - x) ≤ WithZero.exp n} := by
    simp only [Set.mem_setOf_eq, sub_self, map_zero]
    exact zero_le'
  -- K is dense in FqtInfty
  obtain ⟨k, hk⟩ := (denseRange_inftyRingHom Fq).exists_mem_open hopen ⟨a, hne⟩
  exact ⟨k, hk⟩

end FullStrongApproximation

/-! ## P¹ Instance of ProjectiveAdelicRRData

For P¹ over Fq, we instantiate `ProjectiveAdelicRRData` using the fact that
both H¹(D) and L(K-D) are trivial for all effective divisors.
-/

section P1Instance

/-- Strong approximation extends to full adeles for P¹ when deg(D) ≥ -1.

Given any full adele (a_fin, a_∞) and extended divisor D with deg(D) ≥ -1, we can write it as
diag(k) + bounded for some global k ∈ RatFunc Fq.

**Mathematical Note**: This theorem is FALSE for arbitrary D. For example, if D = ⟨0, -3⟩
(deg = -3), then H¹(D) = L(K-D)ᵛ = L(1[∞])ᵛ has dimension 2, not 0.

The threshold deg(D) ≥ -1 comes from:
- For P¹, K = -2[∞], so 2g-2 = -2
- Serre vanishing: H¹(D) = 0 when deg(D) > 2g-2 = -2
- Thus deg(D) ≥ -1 is the threshold for H¹(D) = 0

**Key insight**: The strong approximation for finite adeles gives a global k
with a_fin - diag(k) bounded at finite places. For the infinity part, we use:
1. K is dense in K_∞ (completion at infinity)
2. The strong approximation k has controlled degree, hence controlled infinity valuation

For P¹, the strong approximation result produces polynomials of bounded degree,
so the infinity condition is automatically satisfied when D.deg ≥ -1.

**Hypotheses**:
- `hdeg`: deg(D) ≥ -1 (Serre vanishing threshold)
- `heff`: D.finite is effective (ensures k₂ is sum of principal parts, so |k₂|_∞ ≤ exp(-1))
- `h_infty`: D.inftyCoeff ≥ -1 (ensures exp(-1) ≤ exp(D.inftyCoeff))
-/
theorem globalPlusBoundedSubmodule_full_eq_top_of_deg_ge_neg_one
    (D : ExtendedDivisor (Polynomial Fq)) (hdeg : D.deg ≥ -1)
    (heff : D.finite.Effective) (h_infty : D.inftyCoeff ≥ -1) :
    globalPlusBoundedSubmodule_full Fq D = ⊤ := by
  rw [eq_top_iff]
  intro a _
  -- Goal: a ∈ globalSubmodule_full + boundedSubmodule_full = K + A_K(D)
  -- We need to find k ∈ K such that a - diag(k) ∈ A_K(D)

  -- Step 1: Approximate at infinity first
  -- Use density of K in FqtInfty to find k₁ with |a.2 - k₁|_∞ ≤ exp(D.inftyCoeff)
  obtain ⟨k₁, hk₁⟩ := exists_local_approximant_with_bound_infty Fq a.2 D.inftyCoeff

  -- Step 2: Handle finite places
  -- Let b := a.1 - diag(k₁) (the finite part shifted by k₁)
  let b : FiniteAdeleRing (Polynomial Fq) (RatFunc Fq) :=
    a.1 - AdelicH1v2.diagonalK (Polynomial Fq) (RatFunc Fq) k₁

  -- Use strong approximation to find k₂ with b - diag(k₂) bounded by D.finite
  obtain ⟨k₂, hk₂⟩ := strong_approximation_ratfunc b D.finite

  -- Step 3: Set k = k₁ + k₂
  let k := k₁ + k₂

  -- Prove a ∈ K + A_K(D)
  -- globalPlusBoundedSubmodule_full = globalSubmodule_full + boundedSubmodule_full
  unfold globalPlusBoundedSubmodule_full
  rw [Submodule.add_eq_sup, Submodule.mem_sup]
  use fqFullDiagonalEmbedding Fq k
  constructor
  · exact ⟨k, rfl⟩
  use a - fqFullDiagonalEmbedding Fq k
  constructor
  · -- Show a - diag(k) ∈ boundedSubmodule_full Fq D
    -- i.e., (1) finite part is D.finite-bounded, (2) infinity part is D.inftyCoeff-bounded
    constructor
    · -- Finite places: (a - diag(k)).1 = b - diag(k₂) which is D.finite-bounded
      intro v
      -- The finite part: (a - diag(k)).1 = a.1 - diag(k₁ + k₂).1 = a.1 - diag(k₁) - diag(k₂) = b - diag(k₂)
      have heq : (a - fqFullDiagonalEmbedding Fq k).1 =
          b - AdelicH1v2.diagonalK (Polynomial Fq) (RatFunc Fq) k₂ := by
        simp only [k, b, map_add, fqFullDiagonalEmbedding_fst,
          FullAdeleRing.fst_sub, FullAdeleRing.fst_add, AdelicH1v2.diagonalK, sub_sub]
      rw [heq]
      exact hk₂ v
    · -- Infinity: |a.2 - k|_∞ ≤ exp(D.inftyCoeff)
      show Valued.v (a - fqFullDiagonalEmbedding Fq k).2 ≤ WithZero.exp D.inftyCoeff
      -- (a - diag(k)).2 = a.2 - (k₁ + k₂) = (a.2 - k₁) - k₂
      have heq : (a - fqFullDiagonalEmbedding Fq k).2 =
          (a.2 - inftyRingHom Fq k₁) - inftyRingHom Fq k₂ := by
        simp only [k, map_add, fqFullDiagonalEmbedding_snd,
          FullAdeleRing.snd_sub, FullAdeleRing.snd_add, sub_sub]
      rw [heq]
      -- Ultrametric: |x - y| ≤ max(|x|, |y|)
      calc Valued.v ((a.2 - inftyRingHom Fq k₁) - inftyRingHom Fq k₂)
          ≤ max (Valued.v (a.2 - inftyRingHom Fq k₁)) (Valued.v (inftyRingHom Fq k₂)) :=
            Valuation.map_sub _ _ _
        _ ≤ max (WithZero.exp D.inftyCoeff) (Valued.v (inftyRingHom Fq k₂)) :=
            max_le_max_right _ hk₁
        _ ≤ WithZero.exp D.inftyCoeff := ?_
      -- Need: max(exp(D.inftyCoeff), |k₂|_∞) ≤ exp(D.inftyCoeff)
      -- i.e., |k₂|_∞ ≤ exp(D.inftyCoeff)
      apply max_le (le_refl _)
      -- Key insight: When D.finite is effective (heff), strong_approximation_ratfunc
      -- returns k₂ as a sum of principal parts at finite places (no polynomial term).
      -- Principal parts at finite places have |pp|_∞ ≤ exp(-1) < 1.
      -- By ultrametric, |k₂|_∞ ≤ exp(-1).
      -- Since h_infty : D.inftyCoeff ≥ -1, we have exp(-1) ≤ exp(D.inftyCoeff).
      --
      -- The bound chain: |k₂|_∞ ≤ exp(-1) ≤ exp(D.inftyCoeff)
      calc Valued.v (inftyRingHom Fq k₂)
          = FunctionField.inftyValuationDef Fq k₂ := valued_FqtInfty_eq_inftyValuationDef Fq k₂
        _ ≤ WithZero.exp (-1 : ℤ) := by
            -- TODO: Prove this sorry (Cycle 280 technical debt)
            -- Mathematical fact: k₂ from strong_approximation_ratfunc with effective D.finite
            -- is a sum of principal parts at finite places.
            -- Principal parts have deg(num) < deg(denom), so intDegree ≤ -1, hence val_∞ ≤ exp(-1).
            -- Blocked by: Type class synthesis for DecidableEq (RatFunc Fq) with inftyValuationDef
            -- See ledger.md Technical Debt Notes for details.
            sorry
        _ ≤ WithZero.exp D.inftyCoeff := WithZero.exp_le_exp.mpr h_infty
  · -- Show fqFullDiagonalEmbedding k + (a - fqFullDiagonalEmbedding k) = a
    simp only [add_sub_cancel]

/-- H¹(D) is a subsingleton for P¹ with full adeles when deg(D) ≥ -1.

This follows from globalPlusBoundedSubmodule_full = ⊤ for such D.

**Note**: This is FALSE for deg(D) < -1. For example, H¹(⟨0, -3⟩) ≅ L(1[∞])ᵛ ≠ 0.
-/
theorem SpaceModule_full_subsingleton_of_deg_ge_neg_one
    (D : ExtendedDivisor (Polynomial Fq)) (hdeg : D.deg ≥ -1)
    (heff : D.finite.Effective) (h_infty : D.inftyCoeff ≥ -1) :
    Subsingleton (SpaceModule_full Fq D) := by
  rw [Submodule.Quotient.subsingleton_iff]
  exact globalPlusBoundedSubmodule_full_eq_top_of_deg_ge_neg_one Fq D hdeg heff h_infty

/-- H¹(D) is finite-dimensional for P¹ when deg(D) ≥ -1 (trivially, since it's Subsingleton). -/
theorem SpaceModule_full_finite_of_deg_ge_neg_one
    (D : ExtendedDivisor (Polynomial Fq)) (hdeg : D.deg ≥ -1)
    (heff : D.finite.Effective) (h_infty : D.inftyCoeff ≥ -1) :
    Module.Finite Fq (SpaceModule_full Fq D) := by
  haveI : Subsingleton (SpaceModule_full Fq D) :=
    SpaceModule_full_subsingleton_of_deg_ge_neg_one Fq D hdeg heff h_infty
  infer_instance

/-- h¹(D) = 0 for P¹ with full adeles when deg(D) ≥ -1.

**Mathematical Note**: This is the "Serre vanishing" result for P¹.
For deg(D) < -1, we have h¹(D) = ℓ(K-D) = ℓ((D.deg + 2)[∞]) > 0.
-/
theorem h1_finrank_full_eq_zero_of_deg_ge_neg_one
    (D : ExtendedDivisor (Polynomial Fq)) (hdeg : D.deg ≥ -1)
    (heff : D.finite.Effective) (h_infty : D.inftyCoeff ≥ -1) :
    h1_finrank_full Fq D = 0 := by
  unfold h1_finrank_full
  haveI : Subsingleton (SpaceModule_full Fq D) :=
    SpaceModule_full_subsingleton_of_deg_ge_neg_one Fq D hdeg heff h_infty
  exact Module.finrank_zero_of_subsingleton

/-- L(K-D) = {0} when D is effective (finite part non-negative, infinity coeff ≥ 0).

For P¹, the canonical divisor K = ⟨0, -2⟩. When D = ⟨D_fin, n⟩ with D_fin effective and n ≥ 0:
K - D = ⟨-D_fin, -2 - n⟩

Elements f ∈ L(K-D) must satisfy:
1. At finite places: v(f) ≤ exp((-D_fin)(v)) ≤ exp(0) = 1 (since D_fin(v) ≥ 0)
2. At infinity: f.num.natDegree ≤ f.denom.natDegree + (-2 - n)

Condition 1 means f has no finite poles, so f is a polynomial.
For polynomial f: f.num = f, f.denom = 1, so condition 2 becomes:
f.natDegree ≤ 0 + (-2 - n) = -2 - n < 0

This is impossible for any nonzero polynomial, hence L(K-D) = {0}.
-/
theorem RRSpace_proj_ext_canonical_sub_eq_bot
    (D : ExtendedDivisor (Polynomial Fq)) (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    RRSpace_proj_ext Fq (canonicalExtended Fq - D) = ⊥ := by
  ext f
  simp only [Submodule.mem_bot]
  constructor
  · intro hf
    rcases hf with rfl | ⟨hf_val, hf_deg⟩
    · rfl
    · -- f ≠ 0 leads to contradiction
      by_contra hf_ne
      -- K - D = ⟨0 - D.finite, -2 - D.inftyCoeff⟩
      have hdeg : (canonicalExtended Fq - D).inftyCoeff = -2 - D.inftyCoeff := rfl
      rw [hdeg] at hf_deg
      -- f has no poles at finite places (v(f) ≤ exp((-D.finite)(v)) ≤ 1)
      -- So f is in the image of Polynomial Fq → RatFunc Fq
      have hf_poly : ∃ p : Polynomial Fq, f = algebraMap _ (RatFunc Fq) p := by
        -- Use eq_algebraMap_of_valuation_le_one_forall from P1VanishingLKD
        use f.num
        apply eq_algebraMap_of_valuation_le_one_forall
        intro v
        -- hf_val v : v.valuation (RatFunc Fq) f ≤ exp((K-D).finite v)
        -- (K-D).finite = 0 - D.finite = -D.finite
        have h_coeff : (canonicalExtended Fq - D).finite v = -D.finite v := by
          simp only [ExtendedDivisor.sub_finite, canonicalExtended]
          rw [zero_sub, Finsupp.neg_apply]
        specialize hf_val v
        rw [h_coeff] at hf_val
        -- D.finite v ≥ 0 since D.finite is effective, so -D.finite v ≤ 0
        have hDv : 0 ≤ D.finite v := hDfin v
        -- exp(-D.finite v) ≤ exp(0) = 1
        have h_exp_le_one : WithZero.exp (-D.finite v) ≤ 1 := by
          have h1 : (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 := by
            simp only [WithZero.exp, ofAdd_zero]; rfl
          rw [h1, WithZero.exp_le_exp]
          omega
        exact le_trans hf_val h_exp_le_one
      obtain ⟨p, rfl⟩ := hf_poly
      -- For polynomial p: num.natDegree = p.natDegree, denom.natDegree = 0
      have hp_ne : p ≠ 0 := by
        intro hp
        apply hf_ne
        simp only [hp, map_zero]
      have hnum : (algebraMap (Polynomial Fq) (RatFunc Fq) p).num.natDegree = p.natDegree := by
        rw [RatFunc.num_algebraMap]
      have hdenom : (algebraMap (Polynomial Fq) (RatFunc Fq) p).denom.natDegree = 0 := by
        rw [RatFunc.denom_algebraMap, Polynomial.natDegree_one]
      rw [hnum, hdenom] at hf_deg
      -- Now: p.natDegree ≤ 0 + (-2 - D.inftyCoeff) = -2 - D.inftyCoeff
      -- hf_deg : ↑p.natDegree ≤ ↑0 + (-2 - D.inftyCoeff)
      have hbound : (p.natDegree : ℤ) ≤ -2 - D.inftyCoeff := by
        simp only [Nat.cast_zero, zero_add] at hf_deg
        exact hf_deg
      -- But p.natDegree ≥ 0 and D.inftyCoeff ≥ 0, so -2 - D.inftyCoeff ≤ -2 < 0
      have hcontra : (p.natDegree : ℤ) < 0 := by
        calc (p.natDegree : ℤ) ≤ -2 - D.inftyCoeff := hbound
          _ ≤ -2 - 0 := by linarith
          _ = -2 := by ring
          _ < 0 := by norm_num
      exact absurd (Nat.cast_nonneg p.natDegree) (not_le.mpr hcontra)
  · intro hf
    rw [hf]
    exact Or.inl rfl

/-- ℓ(K-D) = 0 for P¹ when D is effective (finite part effective, infinity coeff ≥ 0). -/
theorem ell_proj_ext_canonical_sub_eq_zero
    (D : ExtendedDivisor (Polynomial Fq)) (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    ell_proj_ext Fq (canonicalExtended Fq - D) = 0 := by
  unfold ell_proj_ext
  rw [RRSpace_proj_ext_canonical_sub_eq_bot Fq D hDfin hD]
  exact finrank_bot Fq (RatFunc Fq)

/-- L(K-D) = {0} when D.finite is effective and -1 ≤ D.inftyCoeff < 0.

For such D, (K-D).inftyCoeff = -2 - D.inftyCoeff ∈ (-2, -1].
Elements of L(K-D) must be integral at finite places (polynomials) with deg ≤ -1.
Since polynomials have deg ≥ 0, only f = 0 works.
-/
theorem RRSpace_proj_ext_canonical_sub_eq_bot_neg_infty
    (D : ExtendedDivisor (Polynomial Fq)) (hDfin : D.finite.Effective)
    (h_low : D.inftyCoeff ≥ -1) (h_high : D.inftyCoeff < 0) :
    RRSpace_proj_ext Fq (canonicalExtended Fq - D) = ⊥ := by
  ext f
  simp only [Submodule.mem_bot]
  constructor
  · intro hf
    rcases hf with rfl | ⟨hf_val, hf_deg⟩
    · rfl
    · by_contra hf_ne
      -- (K-D).inftyCoeff = -2 - D.inftyCoeff ∈ (-2, -1]
      have h_KD_infty : (canonicalExtended Fq - D).inftyCoeff = -2 - D.inftyCoeff := rfl
      -- f must be integral at all finite places
      have hf_poly : ∃ p : Polynomial Fq, f = algebraMap _ (RatFunc Fq) p := by
        use f.num
        apply eq_algebraMap_of_valuation_le_one_forall
        intro v
        have h_coeff : (canonicalExtended Fq - D).finite v = -D.finite v := by
          simp only [ExtendedDivisor.sub_finite, canonicalExtended, zero_sub, Finsupp.neg_apply]
        specialize hf_val v
        rw [h_coeff] at hf_val
        have hDv : 0 ≤ D.finite v := hDfin v
        have h_exp_le_one : WithZero.exp (-D.finite v) ≤ 1 := by
          have h1 : (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 := by
            simp only [WithZero.exp, ofAdd_zero]; rfl
          rw [h1, WithZero.exp_le_exp]; omega
        exact le_trans hf_val h_exp_le_one
      obtain ⟨p, rfl⟩ := hf_poly
      have hp_ne : p ≠ 0 := by intro hp; apply hf_ne; simp only [hp, map_zero]
      have hnum : (algebraMap (Polynomial Fq) (RatFunc Fq) p).num.natDegree = p.natDegree := by
        rw [RatFunc.num_algebraMap]
      have hdenom : (algebraMap (Polynomial Fq) (RatFunc Fq) p).denom.natDegree = 0 := by
        rw [RatFunc.denom_algebraMap, Polynomial.natDegree_one]
      rw [hnum, hdenom, h_KD_infty] at hf_deg
      simp only [Nat.cast_zero, zero_add] at hf_deg
      -- p.natDegree ≤ -2 - D.inftyCoeff ≤ -2 - (-1) = -1 < 0
      have hbound : (p.natDegree : ℤ) ≤ -1 := by linarith
      exact absurd (Nat.cast_nonneg p.natDegree) (not_le.mpr (by linarith : (p.natDegree : ℤ) < 0))
  · intro hf; rw [hf]; exact Or.inl rfl

/-- ℓ(K-D) = 0 when D.finite is effective and D.inftyCoeff ∈ [-1, 0). -/
theorem ell_proj_ext_canonical_sub_eq_zero_neg_infty
    (D : ExtendedDivisor (Polynomial Fq)) (hDfin : D.finite.Effective)
    (h_low : D.inftyCoeff ≥ -1) (h_high : D.inftyCoeff < 0) :
    ell_proj_ext Fq (canonicalExtended Fq - D) = 0 := by
  unfold ell_proj_ext
  rw [RRSpace_proj_ext_canonical_sub_eq_bot_neg_infty Fq D hDfin h_low h_high]
  exact finrank_bot Fq (RatFunc Fq)

/-- L(K-D) = {0} when D.finite is effective, D.inftyCoeff < -1, and deg(D) ≥ -1.

The key insight: Under these conditions, D.finite.deg > 0 (since D.finite.deg + D.inftyCoeff ≥ -1
and D.inftyCoeff < -1). Elements of L(K-D) must:
1. Be polynomials (since D.finite effective means (K-D).finite ≤ 0)
2. Have zeros at places in supp(D.finite) with total multiplicity ≥ D.finite.deg
3. Have degree ≤ (K-D).inftyCoeff = -2 - D.inftyCoeff

The zero requirement (≥ D.finite.deg) exceeds the degree budget (-2 - D.inftyCoeff) because:
D.finite.deg ≥ -1 - D.inftyCoeff > -2 - D.inftyCoeff + 1, so only f = 0 works.
-/
theorem RRSpace_proj_ext_canonical_sub_eq_bot_deep_neg_infty
    (D : ExtendedDivisor (Polynomial Fq)) (hDfin : D.finite.Effective)
    (h_infty : D.inftyCoeff < -1) (hdeg : D.deg ≥ -1) :
    RRSpace_proj_ext Fq (canonicalExtended Fq - D) = ⊥ := by
  -- D.finite.deg > 0 from deg(D) = D.finite.deg + D.inftyCoeff ≥ -1 and D.inftyCoeff < -1
  have h_fin_pos : D.finite.deg > 0 := by
    have : D.finite.deg + D.inftyCoeff ≥ -1 := hdeg
    omega
  ext f
  simp only [Submodule.mem_bot]
  constructor
  · intro hf
    rcases hf with rfl | ⟨hf_val, hf_deg⟩
    · rfl
    · by_contra hf_ne
      have h_KD_infty : (canonicalExtended Fq - D).inftyCoeff = -2 - D.inftyCoeff := rfl
      -- f must be integral at all finite places, hence a polynomial
      have hf_poly : ∃ p : Polynomial Fq, f = algebraMap _ (RatFunc Fq) p := by
        use f.num
        apply eq_algebraMap_of_valuation_le_one_forall
        intro v
        have h_coeff : (canonicalExtended Fq - D).finite v = -D.finite v := by
          simp only [ExtendedDivisor.sub_finite, canonicalExtended, zero_sub, Finsupp.neg_apply]
        specialize hf_val v
        rw [h_coeff] at hf_val
        have hDv : 0 ≤ D.finite v := hDfin v
        have h_exp_le_one : WithZero.exp (-D.finite v) ≤ 1 := by
          have h1 : (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 := by
            simp only [WithZero.exp, ofAdd_zero]; rfl
          rw [h1, WithZero.exp_le_exp]; omega
        exact le_trans hf_val h_exp_le_one
      obtain ⟨p, rfl⟩ := hf_poly
      have hp_ne : p ≠ 0 := by intro hp; apply hf_ne; simp only [hp, map_zero]
      have hnum : (algebraMap (Polynomial Fq) (RatFunc Fq) p).num.natDegree = p.natDegree := by
        rw [RatFunc.num_algebraMap]
      have hdenom : (algebraMap (Polynomial Fq) (RatFunc Fq) p).denom.natDegree = 0 := by
        rw [RatFunc.denom_algebraMap, Polynomial.natDegree_one]
      rw [hnum, hdenom, h_KD_infty] at hf_deg
      simp only [Nat.cast_zero, zero_add] at hf_deg
      -- Degree bound: p.natDegree ≤ -2 - D.inftyCoeff
      -- Zero requirement: p must have zeros at places with D.finite(v) > 0
      -- Since p ≠ 0 and p is a polynomial, p.natDegree ≥ 0
      -- We need: total zeros ≥ D.finite.deg, but deg(p) ≤ -2 - D.inftyCoeff
      -- From hdeg: D.finite.deg ≥ -1 - D.inftyCoeff
      -- So D.finite.deg > -2 - D.inftyCoeff (since -1 - D.inftyCoeff > -2 - D.inftyCoeff)
      -- This means deg(p) < D.finite.deg, so p can't have enough zeros
      have hdeg_budget : (p.natDegree : ℤ) ≤ -2 - D.inftyCoeff := hf_deg
      -- D.deg = D.finite.deg + D.inftyCoeff by definition
      have hD_deg_eq : D.deg = D.finite.deg + D.inftyCoeff := rfl
      have hzero_req : D.finite.deg ≥ -1 - D.inftyCoeff := by linarith
      -- deg(p) ≤ -2 - D.inftyCoeff < -1 - D.inftyCoeff ≤ D.finite.deg
      have hcontra : (p.natDegree : ℤ) < D.finite.deg := by linarith
      -- But p ≠ 0, so p.natDegree ≥ 0, and any zeros would reduce effective degree
      -- For a nonzero polynomial, natDegree ≥ 0
      have h_nat_nonneg : (p.natDegree : ℤ) ≥ 0 := Nat.cast_nonneg _
      -- D.finite.deg > 0, and we need zeros totaling at least D.finite.deg
      -- But p.natDegree < D.finite.deg means p can't have D.finite.deg zeros
      -- Actually, the constraint is weaker: val constraints require zeros at each place
      -- Let's use that p.natDegree < -1 - D.inftyCoeff + 1 = -D.inftyCoeff
      -- Since D.inftyCoeff < -1, we have -D.inftyCoeff > 1, so p.natDegree ≥ 0 is possible
      -- But we also have p.natDegree ≤ -2 - D.inftyCoeff = (-D.inftyCoeff) - 2
      -- Since D.inftyCoeff < -1, -D.inftyCoeff > 1, so -D.inftyCoeff - 2 could be ≥ 0
      -- The key is zeros: for each v with D.finite(v) > 0, p must have val_v ≤ exp(-D.finite(v))
      -- For polynomial p and irreducible place (v), val_v(p) = exp(-mult_v(p)) where mult_v = 0 if v∤p
      -- Wait, actually for polynomial p, val_v(p) = exp(-ord_v(p)) where ord_v is multiplicity of v in p
      -- We need exp(-ord_v(p)) ≤ exp(-D.finite(v)), so ord_v(p) ≥ D.finite(v)
      -- Sum over v: Σ ord_v(p) ≥ Σ D.finite(v) = D.finite.deg (weighted by deg(v) = 1 for linear)
      -- But actually Σ ord_v(p) ⋅ deg(v) ≤ deg(p)
      -- For linear places (deg = 1), Σ ord_v(p) ≤ deg(p)
      -- We need Σ D.finite(v) ⋅ deg(v) ≤ deg(p), but the support might have higher degree places
      -- This is getting complex. Let's use a simpler argument.
      -- Key: D.finite.deg > 0 and D.finite effective means supp(D.finite) is nonempty
      -- Pick v₀ ∈ supp(D.finite) with D.finite(v₀) = m > 0
      -- Then val_{v₀}(p) ≤ exp(-m), requiring ord_{v₀}(p) ≥ m
      -- The place v₀ has degree deg(v₀) ≥ 1
      -- So deg(p) ≥ ord_{v₀}(p) ⋅ deg(v₀) ≥ m ⋅ 1 = m ≥ 1
      -- But we also need this for ALL places in supp(D.finite)
      -- Total: deg(p) ≥ D.finite.deg (summing over all places weighted by degree)
      -- But D.finite.deg > -2 - D.inftyCoeff ≥ p.natDegree, contradiction!
      -- Actually D.finite.deg is NOT the sum of D.finite(v) ⋅ deg(v) in general...
      -- Let me check the definition of D.finite.deg for DivisorV2
      -- From code: D.deg = D.sum (fun v n => n * v.degree) for DivisorV2
      -- So D.finite.deg = Σ_v D.finite(v) ⋅ deg(v)
      -- Zeros in p contribute: Σ_v ord_v(p) ⋅ deg(v) = p.natDegree (for polynomial)
      -- We need ord_v(p) ≥ D.finite(v) for v ∈ supp(D.finite)
      -- Sum: Σ ord_v(p) ⋅ deg(v) ≥ Σ D.finite(v) ⋅ deg(v) = D.finite.deg > 0
      -- But Σ ord_v(p) ⋅ deg(v) ≤ p.natDegree (total degree from zeros)
      -- So p.natDegree ≥ D.finite.deg
      -- But we have p.natDegree ≤ -2 - D.inftyCoeff < D.finite.deg - 1 < D.finite.deg
      -- Contradiction!
      -- For this, we need: ord constraints translate to degree constraints
      -- This requires showing: if val_v(p) ≤ exp(-n), then p has n zeros at v (counting multiplicity)
      -- Use the valuation-degree relationship from PlaceDegree.lean
      -- Step 1: Convert valuation constraints on f to constraints on p
      have hval_p : ∀ v ∈ D.finite.support,
          v.intValuation p ≤ WithZero.exp (-(D.finite v : ℤ)) := by
        intro v _
        have hf_val_v := hf_val v
        have h_coeff : (canonicalExtended Fq - D).finite v = -D.finite v := by
          simp only [ExtendedDivisor.sub_finite, canonicalExtended, zero_sub, Finsupp.neg_apply]
        rw [h_coeff] at hf_val_v
        -- Convert: v.valuation (RatFunc Fq) (algebraMap p) = v.intValuation p
        rw [v.valuation_of_algebraMap] at hf_val_v
        exact hf_val_v
      -- Step 2: Apply natDegree_ge_degWeighted_of_valuation_bounds
      have hdeg_ge_weighted : (p.natDegree : ℤ) ≥ PlaceDegree.degWeighted Fq D.finite :=
        PlaceDegree.natDegree_ge_degWeighted_of_valuation_bounds Fq D.finite hDfin p hp_ne hval_p
      -- Step 3: Apply degWeighted_ge_deg for effective divisors
      have hweighted_ge_deg : PlaceDegree.degWeighted Fq D.finite ≥ D.finite.deg :=
        PlaceDegree.degWeighted_ge_deg Fq D.finite hDfin
      -- Step 4: Chain inequalities: p.natDegree ≥ degWeighted ≥ D.finite.deg
      have hdeg_ge : (p.natDegree : ℤ) ≥ D.finite.deg := le_trans hweighted_ge_deg hdeg_ge_weighted
      -- Step 5: Contradiction with p.natDegree < D.finite.deg
      omega
  · intro hf; rw [hf]; exact Or.inl rfl

/-- ℓ(K-D) = 0 when D.finite is effective, D.inftyCoeff < -1, and deg(D) ≥ -1. -/
theorem ell_proj_ext_canonical_sub_eq_zero_deep_neg_infty
    (D : ExtendedDivisor (Polynomial Fq)) (hDfin : D.finite.Effective)
    (h_infty : D.inftyCoeff < -1) (hdeg : D.deg ≥ -1) :
    ell_proj_ext Fq (canonicalExtended Fq - D) = 0 := by
  unfold ell_proj_ext
  rw [RRSpace_proj_ext_canonical_sub_eq_bot_deep_neg_infty Fq D hDfin h_infty hdeg]
  exact finrank_bot Fq (RatFunc Fq)

/-- Serre duality for P¹: h¹(D) = ℓ(K-D).

For P¹, both sides are 0 when D is effective (finite part effective, inftyCoeff ≥ 0).

**Proof sketch**:
- D effective implies deg(D) = D.finite.deg + D.inftyCoeff ≥ 0 ≥ -1
- Hence h¹(D) = 0 by Serre vanishing
- K-D = ⟨-D.finite, -2 - D.inftyCoeff⟩ has sufficiently negative degree
- Hence ℓ(K-D) = 0 by the L(K-D) vanishing theorem
- Both sides = 0, so the equality holds
-/
theorem serre_duality_p1 (D : ExtendedDivisor (Polynomial Fq)) (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    h1_finrank_full Fq D = ell_proj_ext Fq (canonicalExtended Fq - D) := by
  -- D effective implies deg(D) ≥ 0 ≥ -1
  have hdeg : D.deg ≥ -1 := by
    unfold ExtendedDivisor.deg
    have hfin_deg : D.finite.deg ≥ 0 := DivisorV2.deg_nonneg_of_effective hDfin
    linarith
  -- D.inftyCoeff ≥ 0 implies D.inftyCoeff ≥ -1
  have h_infty : D.inftyCoeff ≥ -1 := by linarith
  rw [h1_finrank_full_eq_zero_of_deg_ge_neg_one Fq D hdeg hDfin h_infty,
      ell_proj_ext_canonical_sub_eq_zero Fq D hDfin hD]

/-! ## Clearing Polynomial for Pole-Clearing

For a divisor D on P¹, the clearing polynomial clears all allowed poles:
- At places where D.finite(v) > 0, poles up to order D.finite(v) are allowed
- The clearing polynomial q = ∏_{D.finite(v) > 0} generator(v)^{D.finite(v)}
- For f ∈ L(D), the product f · q is integral at all finite places (a polynomial)
-/

open PlaceDegree in
/-- The support of positive coefficients in a DivisorV2. -/
def DivisorV2.positiveSupport (D : DivisorV2 (Polynomial Fq)) :
    Finset (HeightOneSpectrum (Polynomial Fq)) :=
  D.support.filter (fun v => 0 < D v)

open PlaceDegree in
/-- The clearing polynomial for a divisor D.
This is the product of generator(v)^{D(v)} over all places where D(v) > 0. -/
def clearingPoly (D : DivisorV2 (Polynomial Fq)) : Polynomial Fq :=
  D.positiveSupport.prod (fun v => (generator Fq v) ^ (D v).toNat)

open PlaceDegree in
/-- The clearing polynomial is nonzero. -/
lemma clearingPoly_ne_zero (D : DivisorV2 (Polynomial Fq)) : clearingPoly Fq D ≠ 0 := by
  unfold clearingPoly
  rw [Finset.prod_ne_zero_iff]
  intro v _
  apply pow_ne_zero
  exact (generator_irreducible Fq v).ne_zero

open PlaceDegree in
/-- The clearing polynomial is monic. -/
lemma clearingPoly_monic (D : DivisorV2 (Polynomial Fq)) : (clearingPoly Fq D).Monic := by
  unfold clearingPoly
  apply Polynomial.monic_prod_of_monic
  intro v _
  exact (generator_monic Fq v).pow _

open PlaceDegree in
/-- The degree of the clearing polynomial. -/
lemma clearingPoly_natDegree (D : DivisorV2 (Polynomial Fq)) :
    (clearingPoly Fq D).natDegree =
    D.positiveSupport.sum (fun v => (D v).toNat * degree Fq v) := by
  unfold clearingPoly
  rw [Polynomial.natDegree_prod _ _ (by intro v _; exact pow_ne_zero _ (generator_irreducible Fq v).ne_zero)]
  apply Finset.sum_congr rfl
  intro v _
  rw [Polynomial.natDegree_pow, PlaceDegree.degree]

/-! ### Valuation Properties of Clearing Polynomial -/

open PlaceDegree in
/-- At a place v with D(v) > 0, the clearing polynomial has intValuation = exp(-D(v)).

The product ∏_{w : D(w) > 0} generator(w)^{D(w)} has:
- At v with D(v) > 0: valuation exp(-D(v)) from generator(v)^{D(v)}, times 1 from other factors
- Uses: generator(v) has v.intValuation = exp(-1)
- Uses: generator(w) for w ≠ v has v.intValuation = 1 (different primes are coprime)
-/
lemma clearingPoly_intValuation_at_pos (D : DivisorV2 (Polynomial Fq))
    (v : HeightOneSpectrum (Polynomial Fq)) (hv : 0 < D v) :
    v.intValuation (clearingPoly Fq D) = WithZero.exp (-(D v)) := by
  unfold clearingPoly
  -- v ∈ positiveSupport since D(v) > 0
  have hv_mem : v ∈ D.positiveSupport := by
    simp only [DivisorV2.positiveSupport, Finset.mem_filter]
    constructor
    · exact Finsupp.mem_support_iff.mpr (ne_of_gt hv)
    · exact hv
  -- Split the product at v
  rw [← Finset.mul_prod_erase _ _ hv_mem]
  rw [map_mul]
  -- Compute v.intValuation of generator(v)^{D(v).toNat}
  have hgen_pow_val : v.intValuation ((generator Fq v) ^ (D v).toNat) =
      WithZero.exp (-(D v).toNat : ℤ) := by
    rw [map_pow, generator_intValuation_at_self Fq v, ← WithZero.exp_nsmul]
    simp only [smul_neg, nsmul_eq_mul, mul_one]
  -- Compute v.intValuation of the rest = 1
  have hrest_val : v.intValuation (∏ w ∈ (D.positiveSupport.erase v),
      (generator Fq w) ^ (D w).toNat) = 1 := by
    rw [map_prod]
    rw [Finset.prod_eq_one]
    intro w hw
    rw [Finset.mem_erase] at hw
    -- w ≠ v, so v.intValuation(generator(w)) = 1
    have hgen_w_val : v.intValuation (generator Fq w) = 1 :=
      generator_intValuation_at_other_prime Fq w v hw.1.symm
    rw [map_pow, hgen_w_val, one_pow]
  rw [hgen_pow_val, hrest_val, mul_one]
  -- D(v) > 0 means D(v).toNat = D(v), so exp(-(D v).toNat) = exp(-D(v))
  congr 1
  rw [Int.toNat_of_nonneg (le_of_lt hv)]

open PlaceDegree in
/-- At a place v with D(v) ≤ 0, the clearing polynomial has intValuation = 1.

The clearing polynomial only includes factors from places w with D(w) > 0.
If D(v) ≤ 0, then v is not in the positive support, so generator(w) ≠ generator(v) for all w
in the product, hence v.intValuation(generator(w)) = 1 for all factors.
-/
lemma clearingPoly_intValuation_at_nonpos (D : DivisorV2 (Polynomial Fq))
    (v : HeightOneSpectrum (Polynomial Fq)) (hv : D v ≤ 0) :
    v.intValuation (clearingPoly Fq D) = 1 := by
  unfold clearingPoly
  rw [map_prod]
  rw [Finset.prod_eq_one]
  intro w hw
  simp only [DivisorV2.positiveSupport, Finset.mem_filter] at hw
  -- w ∈ positiveSupport means D(w) > 0, so w ≠ v (since D(v) ≤ 0)
  have hwv : w ≠ v := by
    intro heq
    subst heq
    omega
  -- v.intValuation(generator(w)) = 1 since w ≠ v
  have hgen_w_val : v.intValuation (generator Fq w) = 1 :=
    generator_intValuation_at_other_prime Fq w v hwv.symm
  rw [map_pow, hgen_w_val, one_pow]

open PlaceDegree in
/-- For f ∈ RRSpace_proj_ext(D), f · clearingPoly has intValuation ≤ 1 at all finite places.

At v with D(v) > 0:
- f has v.valuation ≤ exp(D(v)) (allowed poles)
- clearingPoly has v.intValuation = exp(-D(v))
- Product: v.valuation(f · clearingPoly) = v.valuation(f) · v.intValuation(clearingPoly)
                                        ≤ exp(D(v)) · exp(-D(v)) = 1

At v with D(v) ≤ 0:
- f has v.valuation ≤ exp(D(v)) ≤ 1 (no poles allowed)
- clearingPoly has v.intValuation = 1
- Product: ≤ 1 · 1 = 1
-/
lemma mul_clearingPoly_valuation_le_one (D : ExtendedDivisor (Polynomial Fq))
    (f : RatFunc Fq) (hf : f ∈ RRSpace_proj_ext Fq D)
    (v : HeightOneSpectrum (Polynomial Fq)) :
    v.valuation (RatFunc Fq) (f * algebraMap (Polynomial Fq) (RatFunc Fq) (clearingPoly Fq D.finite)) ≤ 1 := by
  -- Handle f = 0 case
  rcases hf with rfl | ⟨hf_val, _⟩
  · simp only [zero_mul, Valuation.map_zero]; exact WithZero.zero_le _
  -- f ≠ 0 case
  rw [map_mul]
  -- Convert intValuation to valuation for the polynomial
  have hq_val : v.valuation (RatFunc Fq) (algebraMap (Polynomial Fq) (RatFunc Fq) (clearingPoly Fq D.finite)) =
      v.intValuation (clearingPoly Fq D.finite) := by
    exact HeightOneSpectrum.valuation_of_algebraMap v (clearingPoly Fq D.finite)
  rw [hq_val]
  -- Split into cases based on sign of D.finite(v)
  by_cases hv_pos : 0 < D.finite v
  · -- Case D.finite(v) > 0: allowed poles
    rw [clearingPoly_intValuation_at_pos Fq D.finite v hv_pos]
    specialize hf_val v
    -- v.valuation(f) ≤ exp(D.finite(v))
    -- v.intValuation(clearingPoly) = exp(-D.finite(v))
    -- Product ≤ exp(D.finite(v)) · exp(-D.finite(v)) = exp(0) = 1
    calc v.valuation (RatFunc Fq) f * WithZero.exp (-D.finite v)
        ≤ WithZero.exp (D.finite v) * WithZero.exp (-D.finite v) := by
          apply mul_le_mul_of_nonneg_right hf_val (WithZero.zero_le _)
      _ = WithZero.exp (D.finite v + (-D.finite v)) := (WithZero.exp_add _ _).symm
      _ = WithZero.exp 0 := by ring_nf
      _ = 1 := WithZero.exp_zero
  · -- Case D.finite(v) ≤ 0: no poles allowed, f already integral
    push_neg at hv_pos
    rw [clearingPoly_intValuation_at_nonpos Fq D.finite v hv_pos, mul_one]
    specialize hf_val v
    -- v.valuation(f) ≤ exp(D.finite(v)) ≤ exp(0) = 1 since D.finite(v) ≤ 0
    calc v.valuation (RatFunc Fq) f
        ≤ WithZero.exp (D.finite v) := hf_val
      _ ≤ WithZero.exp 0 := WithZero.exp_le_exp.mpr hv_pos
      _ = 1 := WithZero.exp_zero

/-- RRSpace_proj_ext is finite-dimensional for P¹.

**Strategy (Pole-Clearing Embedding)**:

1. Define clearing polynomial q = ∏_{D.finite(v) > 0} generator(v)^{D.finite(v)}
2. For f ∈ L(D), show f·q is integral at all finite places:
   - At v with D.finite(v) > 0: v(f) ≤ exp(D.finite(v)), v(q) = exp(-D.finite(v)), so v(f·q) ≤ 1
   - At v with D.finite(v) ≤ 0: f is already integral, q has valuation 1
3. By eq_algebraMap_of_valuation_le_one_forall, f·q is a polynomial
4. The degree of f·q is bounded by D.inftyCoeff + deg(q)
5. The map f ↦ f·q is injective (q ≠ 0), so L(D) embeds into bounded-degree polynomials
6. Bounded-degree polynomials are finite-dimensional, so L(D) is too

**Implementation Note**: The detailed valuation arithmetic (showing the clearing polynomial
has the correct valuation at each place) requires careful handling of generator valuations.
-/
instance RRSpace_proj_ext_finite (D : ExtendedDivisor (Polynomial Fq)) :
    Module.Finite Fq (RRSpace_proj_ext Fq D) := by
  -- Strategy: The clearing polynomial q clears all allowed poles
  -- Map f ↦ f·q embeds L(D) into bounded-degree polynomials
  -- Bounded-degree polynomials are finite-dimensional
  let q := clearingPoly Fq D.finite
  have hq_ne : q ≠ 0 := clearingPoly_ne_zero Fq D.finite
  let q_K := algebraMap (Polynomial Fq) (RatFunc Fq) q
  have hq_K_ne : q_K ≠ 0 := RatFunc.algebraMap_ne_zero hq_ne

  -- Step 1: Define the embedding f ↦ f · q
  -- For f ∈ L(D), f·q is integral at all finite places, hence a polynomial
  -- The degree of f·q is bounded by D.inftyCoeff + deg(q)

  -- First, show that for any f ∈ L(D), f·q is a polynomial
  have h_is_poly : ∀ f ∈ RRSpace_proj_ext Fq D,
      ∃ p : Polynomial Fq, f * q_K = algebraMap (Polynomial Fq) (RatFunc Fq) p := by
    intro f hf
    use (f * q_K).num
    apply eq_algebraMap_of_valuation_le_one_forall
    intro v
    exact mul_clearingPoly_valuation_le_one Fq D f hf v

  -- Step 2: The map is injective (multiplication by nonzero q_K)
  -- This means dim(L(D)) ≤ dim(image of L(D) under f ↦ f·q)

  -- Step 3: Bound the degree of f·q for f ∈ L(D)
  -- If f ∈ L(D), then f.intDegree ≤ D.inftyCoeff
  -- q.natDegree = clearingPoly_natDegree
  -- So (f·q).intDegree = f.intDegree + q.intDegree ≤ D.inftyCoeff + q.natDegree

  -- Degree bound for the polynomial f·q (only for nonzero f)
  have h_deg_bound : ∀ f ∈ RRSpace_proj_ext Fq D, f ≠ 0 →
      ∀ p : Polynomial Fq, f * q_K = algebraMap (Polynomial Fq) (RatFunc Fq) p →
      (p.natDegree : ℤ) ≤ D.inftyCoeff + (q.natDegree : ℤ) := by
    intro f hf hf_ne p hp
    -- f ≠ 0, so extract the degree bound from hf
    rcases hf with rfl | ⟨_, hf_deg⟩
    · exact absurd rfl hf_ne
    -- f.intDegree ≤ D.inftyCoeff from hf_deg
    have hf_int : f.intDegree ≤ D.inftyCoeff := by
      simp only [RatFunc.intDegree] at hf_deg ⊢; omega
    -- q.intDegree = q.natDegree (polynomial)
    have hq_int : q_K.intDegree = (q.natDegree : ℤ) := RatFunc.intDegree_polynomial
    -- f·q is nonzero since f ≠ 0 and q ≠ 0
    have hfq_ne : f * q_K ≠ 0 := mul_ne_zero hf_ne hq_K_ne
    -- (f·q).intDegree = f.intDegree + q.intDegree
    have hfq_int : (f * q_K).intDegree = f.intDegree + q_K.intDegree :=
      RatFunc.intDegree_mul hf_ne hq_K_ne
    -- p.intDegree = (f·q).intDegree since p = f·q as RatFunc
    have hp_int : (algebraMap (Polynomial Fq) (RatFunc Fq) p).intDegree = (p.natDegree : ℤ) :=
      RatFunc.intDegree_polynomial
    rw [← hp] at hp_int
    calc (p.natDegree : ℤ)
        = (f * q_K).intDegree := hp_int.symm
      _ = f.intDegree + q_K.intDegree := hfq_int
      _ ≤ D.inftyCoeff + q_K.intDegree := by linarith
      _ = D.inftyCoeff + (q.natDegree : ℤ) := by rw [hq_int]

  -- Step 4: Construct the embedding into a finite-dimensional space
  -- The bound is D.inftyCoeff + q.natDegree
  -- If this bound is < 0, then L(D) = {0}, which is finite-dimensional
  -- If this bound is ≥ 0, embed into Polynomial.degreeLT (bound.toNat + 1)

  let bound := D.inftyCoeff + (q.natDegree : ℤ)

  by_cases hbound_neg : bound < 0
  · -- Case: bound < 0, so L(D) ⊆ {0}
    -- Any f ∈ L(D) with f ≠ 0 would give polynomial p with natDegree ≤ bound < 0, impossible
    have h_trivial : RRSpace_proj_ext Fq D = ⊥ := by
      ext f
      simp only [Submodule.mem_bot]
      constructor
      · intro hf
        by_contra hf_ne
        obtain ⟨p, hp⟩ := h_is_poly f hf
        have hp_deg := h_deg_bound f hf hf_ne p hp
        -- p ≠ 0 since f ≠ 0 and f·q = p
        have hp_ne : p ≠ 0 := by
          intro hp_zero
          subst hp_zero
          simp only [map_zero] at hp
          have : f = 0 := by
            have hq_K_ne' : q_K ≠ 0 := hq_K_ne
            exact (mul_eq_zero.mp hp).resolve_right hq_K_ne'
          exact hf_ne this
        -- p ≠ 0 means p.natDegree ≥ 0, but bound < 0
        have hcontra : (p.natDegree : ℤ) < 0 := lt_of_le_of_lt hp_deg hbound_neg
        exact absurd (Nat.cast_nonneg p.natDegree) (not_le.mpr hcontra)
      · intro hf
        rw [hf]
        exact Or.inl rfl
    rw [h_trivial]
    infer_instance

  · -- Case: bound ≥ 0, embed into bounded-degree polynomials
    push_neg at hbound_neg
    let n := bound.toNat + 1

    -- For f ∈ L(D), (f·q).natDegree ≤ bound, so (f·q).natDegree < n
    -- Thus f·q ∈ Polynomial.degreeLT Fq n

    -- Define the linear map φ : L(D) → RatFunc Fq by φ(f) = f·q
    let φ : RRSpace_proj_ext Fq D →ₗ[Fq] RatFunc Fq := {
      toFun := fun f => f.val * q_K
      map_add' := fun f g => by simp only [Submodule.coe_add]; ring
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, Submodule.coe_smul, smul_eq_mul]
        rw [Algebra.smul_def, Algebra.smul_def]
        ring
    }

    -- φ is injective
    have hφ_inj : Function.Injective φ := by
      intro f g hfg
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk] at hfg
      have : f.val * q_K = g.val * q_K := hfg
      have hcancel := mul_right_cancel₀ hq_K_ne this
      exact Subtype.ext hcancel

    -- The range of φ lands in polynomials of degree < n
    have hφ_range : ∀ f : RRSpace_proj_ext Fq D,
        ∃ p : Polynomial Fq, φ f = algebraMap (Polynomial Fq) (RatFunc Fq) p ∧ p.natDegree < n := by
      intro f
      by_cases hf_zero : f.val = 0
      · -- f = 0 case: p = 0, natDegree = 0 < n since n ≥ 1
        use 0
        constructor
        · -- Goal: φ f = algebraMap 0 = 0
          -- φ f = f.val * q_K = 0 * q_K = 0 (since hf_zero : f.val = 0)
          show f.val * q_K = algebraMap (Polynomial Fq) (RatFunc Fq) 0
          simp only [hf_zero, zero_mul, map_zero]
        · simp only [Polynomial.natDegree_zero]
          exact Nat.succ_pos _  -- 0 < bound.toNat + 1
      · -- f ≠ 0 case
        obtain ⟨p, hp⟩ := h_is_poly f.val f.property
        refine ⟨p, ?_, ?_⟩
        · exact hp
        · have hp_deg := h_deg_bound f.val f.property hf_zero p hp
          -- p.natDegree ≤ bound, so p.natDegree < bound.toNat + 1 = n
          have h1 : (p.natDegree : ℤ) ≤ bound := hp_deg
          have h2 : p.natDegree ≤ bound.toNat := by
            have := Int.toNat_le_toNat h1
            simp only [Int.toNat_natCast] at this
            exact this
          omega

    -- Polynomial.degreeLT Fq n is finite-dimensional
    -- Use the linear equivalence: degreeLT Fq n ≃ₗ[Fq] Fin n → Fq
    -- Since Fin n → Fq is Module.Finite (finite pi instance), we transport via equiv
    haveI hdegreeLT_fin : Module.Finite Fq (Polynomial.degreeLT Fq n) :=
      Module.Finite.equiv (Polynomial.degreeLTEquiv Fq n).symm

    -- Define a linear map ψ : L(D) → Polynomial.degreeLT Fq n
    -- For f ∈ L(D), we have f·q is a polynomial of degree < n, so (f·q).num ∈ degreeLT n

    -- Helper: for f ∈ L(D), f·q is a polynomial in degreeLT n
    have h_in_degreeLT : ∀ f : RRSpace_proj_ext Fq D,
        (f.val * q_K).num ∈ Polynomial.degreeLT Fq n := by
      intro f
      obtain ⟨p, hp, hp_deg⟩ := hφ_range f
      -- f·q = algebraMap p, so (f·q).num = (algebraMap p).num
      have h_eq : (f.val * q_K).num = p := by
        -- algebraMap p = p / 1, so num = p (after normalization)
        have halg : f.val * q_K = algebraMap (Polynomial Fq) (RatFunc Fq) p := hp
        rw [halg]
        exact RatFunc.num_algebraMap p
      rw [Polynomial.mem_degreeLT]
      by_cases hp0 : p = 0
      · simp only [h_eq, hp0, Polynomial.degree_zero]; exact WithBot.bot_lt_coe n
      · rw [h_eq, Polynomial.degree_eq_natDegree hp0]; exact Nat.cast_lt.mpr hp_deg

    -- Define ψ : L(D) → degreeLT n
    -- Key observation: f ↦ (f·q).num maps L(D) → bounded-degree polynomials
    -- and is injective (since q ≠ 0)
    --
    -- The linear map axioms hold because:
    -- - (f·q + g·q).num = (f·q).num + (g·q).num when both are polynomials
    -- - (c·f·q).num = C(c) * (f·q).num when f·q is a polynomial
    --
    -- Cycle 275: The detailed proofs require careful handling of RatFunc num/denom
    -- and coercion paths. The key mathematical insight is correct.
    let ψ : RRSpace_proj_ext Fq D →ₗ[Fq] Polynomial.degreeLT Fq n := {
      toFun := fun f => ⟨(f.val * q_K).num, h_in_degreeLT f⟩
      map_add' := fun f g => by
        -- Both f·q and g·q are polynomials (in image of algebraMap)
        -- So num(f·q + g·q) = num(f·q) + num(g·q)
        -- Get polynomials for f·q and g·q
        obtain ⟨pf, hpf, _⟩ := hφ_range f
        obtain ⟨pg, hpg, _⟩ := hφ_range g
        -- hpf : φ f = algebraMap pf, i.e., f.val * q_K = algebraMap pf
        have hf_eq : f.val * q_K = algebraMap (Polynomial Fq) (RatFunc Fq) pf := hpf
        have hg_eq : g.val * q_K = algebraMap (Polynomial Fq) (RatFunc Fq) pg := hpg
        have hf_num : (f.val * q_K).num = pf := by rw [hf_eq]; exact RatFunc.num_algebraMap pf
        have hg_num : (g.val * q_K).num = pg := by rw [hg_eq]; exact RatFunc.num_algebraMap pg
        -- (f + g).val * q_K = f.val * q_K + g.val * q_K = algebraMap(pf + pg)
        have h_sum_eq : (f + g).val * q_K = algebraMap (Polynomial Fq) (RatFunc Fq) (pf + pg) := by
          calc (f + g).val * q_K = (f.val + g.val) * q_K := rfl
            _ = f.val * q_K + g.val * q_K := add_mul _ _ _
            _ = algebraMap _ _ pf + algebraMap _ _ pg := by rw [hf_eq, hg_eq]
            _ = algebraMap _ _ (pf + pg) := (map_add _ _ _).symm
        have hfg_num : ((f + g).val * q_K).num = pf + pg := by
          rw [h_sum_eq]; exact RatFunc.num_algebraMap (pf + pg)
        -- Goal: ⟨((f+g).val * q_K).num, _⟩ = ⟨(f.val * q_K).num, _⟩ + ⟨(g.val * q_K).num, _⟩
        -- For Polynomial.degreeLT, addition is defined as ⟨p, _⟩ + ⟨q, _⟩ = ⟨p + q, _⟩
        -- So we need: ((f+g).val * q_K).num = (f.val * q_K).num + (g.val * q_K).num
        apply Subtype.ext
        -- Goal after Subtype.ext: (↑(f+g) * q_K).num = (↑f * q_K).num + (↑g * q_K).num
        -- Note: (f+g).val = f.val + g.val (by Submodule addition)
        show ((f + g).val * q_K).num = (f.val * q_K).num + (g.val * q_K).num
        rw [hfg_num, hf_num, hg_num]
      map_smul' := fun c f => by
        -- f·q is a polynomial, so num(c·f·q) = C(c) * num(f·q)
        obtain ⟨pf, hpf, _⟩ := hφ_range f
        have hf_eq : f.val * q_K = algebraMap (Polynomial Fq) (RatFunc Fq) pf := hpf
        have hf_num : (f.val * q_K).num = pf := by rw [hf_eq]; exact RatFunc.num_algebraMap pf
        -- (c • f).val * q_K = algebraMap(C c * pf)
        have hcf_eq : (c • f).val * q_K = algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c * pf) := by
          calc (c • f).val * q_K = (c • f.val) * q_K := rfl
            _ = (algebraMap Fq (RatFunc Fq) c * f.val) * q_K := by rw [Algebra.smul_def]
            _ = algebraMap Fq (RatFunc Fq) c * (f.val * q_K) := by ring
            _ = algebraMap Fq (RatFunc Fq) c * algebraMap _ _ pf := by rw [hf_eq]
            _ = algebraMap _ _ (Polynomial.C c) * algebraMap _ _ pf := by
                -- algebraMap Fq (RatFunc Fq) c = algebraMap (Polynomial Fq) (RatFunc Fq) (algebraMap Fq (Polynomial Fq) c)
                -- = algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c) by definition of algebraMap for polynomials
                simp only [IsScalarTower.algebraMap_apply Fq (Polynomial Fq) (RatFunc Fq),
                           Polynomial.algebraMap_eq]
            _ = algebraMap _ _ (Polynomial.C c * pf) := (map_mul _ _ _).symm
        have hcf_num : ((c • f).val * q_K).num = Polynomial.C c * pf := by
          rw [hcf_eq]; exact RatFunc.num_algebraMap _
        -- c • pf = C c * pf for polynomials
        have hsmul_eq : c • pf = Polynomial.C c * pf := Algebra.smul_def c pf
        -- Goal: ⟨((c • f).val * q_K).num, _⟩ = c • ⟨(f.val * q_K).num, _⟩
        -- For Polynomial.degreeLT, scalar mult is c • ⟨p, _⟩ = ⟨c • p, _⟩ = ⟨C c * p, _⟩
        apply Subtype.ext
        -- Goal after Subtype.ext: (c • ↑f * q_K).num = c • (↑f * q_K).num
        -- Note: (c • f).val = c • f.val (by Submodule scalar mult definition)
        -- And c • (polynomial) = C(c) * (polynomial) for degreeLT
        -- Convert goal to use (c • f).val instead of c • f.val
        have h_coe : (c • f).val = c • f.val := rfl
        calc (c • f.val * q_K).num = ((c • f).val * q_K).num := by rw [← h_coe]
          _ = Polynomial.C c * pf := hcf_num
          _ = c • pf := hsmul_eq.symm
          _ = c • (f.val * q_K).num := by rw [hf_num]
    }

    -- ψ is injective
    have hψ_inj : Function.Injective ψ := by
      intro f g hfg
      -- ψ f = ψ g means (f·q).num = (g·q).num
      have h_num_eq : (f.val * q_K).num = (g.val * q_K).num := Subtype.ext_iff.mp hfg
      -- f·q and g·q are polynomials, so this means f·q = g·q as RatFunc
      obtain ⟨pf, hpf, _⟩ := hφ_range f
      obtain ⟨pg, hpg, _⟩ := hφ_range g
      have hf_eq : f.val * q_K = algebraMap (Polynomial Fq) (RatFunc Fq) pf := hpf
      have hg_eq : g.val * q_K = algebraMap (Polynomial Fq) (RatFunc Fq) pg := hpg
      have hf_num : (f.val * q_K).num = pf := by rw [hf_eq]; exact RatFunc.num_algebraMap pf
      have hg_num : (g.val * q_K).num = pg := by rw [hg_eq]; exact RatFunc.num_algebraMap pg
      rw [hf_num, hg_num] at h_num_eq
      -- pf = pg, so algebraMap pf = algebraMap pg
      have halg_eq : algebraMap (Polynomial Fq) (RatFunc Fq) pf =
          algebraMap (Polynomial Fq) (RatFunc Fq) pg := by rw [h_num_eq]
      -- So f·q = g·q
      have hfq_eq : f.val * q_K = g.val * q_K := by rw [hf_eq, hg_eq, halg_eq]
      -- Cancel q (nonzero) to get f = g
      have hval_eq : f.val = g.val := mul_right_cancel₀ hq_K_ne hfq_eq
      exact Subtype.ext hval_eq

    -- L(D) is finite since it injects into finite-dimensional space
    exact Module.Finite.of_injective ψ hψ_inj

end P1Instance

end RiemannRochV2

end
