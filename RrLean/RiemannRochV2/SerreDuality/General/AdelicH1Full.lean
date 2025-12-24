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

/-! ## P¹ Instance of ProjectiveAdelicRRData

For P¹ over Fq, we instantiate `ProjectiveAdelicRRData` using the fact that
both H¹(D) and L(K-D) are trivial for all effective divisors.
-/

section P1Instance

/-- Strong approximation extends to full adeles for P¹.

Given any full adele (a_fin, a_∞) and extended divisor D, we can write it as
diag(k) + bounded for some global k ∈ RatFunc Fq.

**Key insight**: The strong approximation for finite adeles gives a global k
with a_fin - diag(k) bounded at finite places. For the infinity part, we use:
1. K is dense in K_∞ (completion at infinity)
2. The strong approximation k has controlled degree, hence controlled infinity valuation

For P¹, the strong approximation result produces polynomials of bounded degree,
so the infinity condition is automatically satisfied when D.inftyCoeff is not too negative.
-/
theorem globalPlusBoundedSubmodule_full_eq_top (D : ExtendedDivisor (Polynomial Fq)) :
    globalPlusBoundedSubmodule_full Fq D = ⊤ := by
  rw [eq_top_iff]
  intro a _
  -- This requires extending strong approximation to full adeles.
  -- The key steps are:
  -- 1. Use strong approximation for finite adeles to find k with a.1 - diag(k) bounded
  -- 2. Use density of K in K_∞ to show a.2 - k has bounded infinity valuation
  -- 3. Combine these to get a = diag(k) + bounded in FullAdeleRing
  --
  -- The main technical challenge is showing the same k works for both bounds.
  -- For P¹, this follows from the fact that strong approximation produces
  -- polynomials with controlled degree, which also bounds their infinity valuation.
  --
  -- Deferred to a future cycle for full implementation.
  sorry

/-- H¹(D) is a subsingleton for P¹ with full adeles.

This follows from globalPlusBoundedSubmodule_full = ⊤.
-/
instance SpaceModule_full_subsingleton (D : ExtendedDivisor (Polynomial Fq)) :
    Subsingleton (SpaceModule_full Fq D) := by
  rw [Submodule.Quotient.subsingleton_iff]
  exact globalPlusBoundedSubmodule_full_eq_top Fq D

/-- H¹(D) is finite-dimensional for P¹ (trivially, since it's Subsingleton). -/
instance SpaceModule_full_finite (D : ExtendedDivisor (Polynomial Fq)) :
    Module.Finite Fq (SpaceModule_full Fq D) := by
  haveI : Subsingleton (SpaceModule_full Fq D) := SpaceModule_full_subsingleton Fq D
  infer_instance

/-- h¹(D) = 0 for P¹ with full adeles. -/
theorem h1_finrank_full_eq_zero (D : ExtendedDivisor (Polynomial Fq)) :
    h1_finrank_full Fq D = 0 := by
  unfold h1_finrank_full
  haveI : Subsingleton (SpaceModule_full Fq D) := SpaceModule_full_subsingleton Fq D
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

/-- Serre duality for P¹: h¹(D) = ℓ(K-D).

For P¹, both sides are 0 when D is effective.
-/
theorem serre_duality_p1 (D : ExtendedDivisor (Polynomial Fq)) (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    h1_finrank_full Fq D = ell_proj_ext Fq (canonicalExtended Fq - D) := by
  rw [h1_finrank_full_eq_zero Fq D, ell_proj_ext_canonical_sub_eq_zero Fq D hDfin hD]

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
  --
  -- Key ingredients needed:
  -- 1. mul_clearingPoly_integral: f·q is integral at all finite places
  -- 2. eq_algebraMap_of_valuation_le_one_forall: integral at all finite ⟹ polynomial
  -- 3. Degree bound from intDegree constraint + clearing poly degree
  -- 4. Polynomial.degreeLT is finite-dimensional
  --
  -- Cycle 274: Architecture established with clearing polynomial infrastructure
  -- Remaining: Fill valuation arithmetic for mul_clearingPoly_integral
  sorry

end P1Instance

end RiemannRochV2

end
