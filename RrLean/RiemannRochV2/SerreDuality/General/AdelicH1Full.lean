import RrLean.RiemannRochV2.Adelic.FullAdelesBase
import RrLean.RiemannRochV2.Adelic.AdelicH1v2
import RrLean.RiemannRochV2.SerreDuality.RatFuncResidues

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
        rcases ha with rfl | ⟨_, ha_deg⟩
        · simp only [zero_add] at h ⊢
          rcases hb with rfl | ⟨_, hb_deg⟩
          · exact absurd rfl h
          · exact hb_deg
        rcases hb with rfl | ⟨_, hb_deg⟩
        · simp only [add_zero]
          exact ha_deg
        -- Both nonzero: use RatFunc.intDegree_add_le
        -- Strategy: convert to intDegree, apply intDegree_add_le, convert back
        -- Condition: num.natDegree ≤ denom.natDegree + D.inftyCoeff ↔ intDegree ≤ D.inftyCoeff
        -- This requires careful handling of the type coercions and arithmetic
        -- TODO (Cycle 247): Complete the degree bound proof using intDegree_add_le
        sorry
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
        rcases hf with rfl | ⟨_, hf_deg⟩
        · exfalso; apply hcf; simp only [smul_zero]
        -- For c ≠ 0, (c • f).intDegree = intDegree(C c) + intDegree(f) = 0 + intDegree(f)
        -- Strategy: use intDegree_mul and intDegree_C to show degree preserved
        -- TODO (Cycle 247): Complete the scalar mult degree proof
        sorry

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

end RiemannRochV2

end
