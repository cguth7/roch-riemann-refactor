-- Specific imports for ~12x faster build times (8s vs 90s)
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.BigOperators
import Mathlib.Order.Preorder.Finsupp
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Field.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

open AlgebraicGeometry

namespace RiemannRoch

/-! ## Divisor Foundations (Cycle 4)

Concrete divisor type grounded in mathlib's Finsupp.
This provides a real mathematical foundation rather than abstract `Div : Type*`.
-/

/-- A divisor on a set α is a finitely supported function α → ℤ.
This is the standard definition: a formal sum of points with integer coefficients. -/
abbrev Divisor (α : Type*) := α →₀ ℤ

namespace Divisor

variable {α : Type*}

/-- Degree of a divisor is the sum of its coefficients. -/
def deg (D : Divisor α) : ℤ := D.sum (fun _ n => n)

/-- Single-point divisor constructor (n · p). -/
noncomputable abbrev single (p : α) (n : ℤ) : Divisor α := Finsupp.single p n

-- Candidate 3: Degree is additive
lemma deg_add (D E : Divisor α) : deg (D + E) = deg D + deg E := by
  simp only [deg]
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

-- Candidate 4: Degree of zero
lemma deg_zero : deg (0 : Divisor α) = 0 := by
  simp only [deg, Finsupp.sum_zero_index]

-- Candidate 5: Degree of negation
lemma deg_neg (D : Divisor α) : deg (-D) = -deg D := by
  have h : deg (D + (-D)) = deg D + deg (-D) := deg_add D (-D)
  simp only [add_neg_cancel, deg_zero] at h
  omega

-- Candidate 6: Degree of subtraction
lemma deg_sub (D E : Divisor α) : deg (D - E) = deg D - deg E := by
  rw [sub_eq_add_neg, deg_add, deg_neg, sub_eq_add_neg]

-- Candidate 8: Degree of single-point divisor
lemma deg_single (p : α) (n : ℤ) : deg (single p n) = n := by
  simp only [deg, single, Finsupp.sum_single_index]

/-! ### Effective Divisors (Cycle 5) -/

/-- A divisor is effective if all coefficients are non-negative.
This uses the pointwise order on Finsupp: D ≤ E ↔ ∀ p, D p ≤ E p. -/
def Effective (D : Divisor α) : Prop := 0 ≤ D

-- Candidate 2: Explicit pointwise characterization
lemma Effective_iff (D : Divisor α) : Effective D ↔ ∀ p, 0 ≤ D p := by
  rfl

-- Candidate 3: Zero divisor is effective
lemma Effective_zero : Effective (0 : Divisor α) := le_refl 0

-- Candidate 4: Sum of effective divisors is effective
lemma Effective_add {D E : Divisor α} (hD : Effective D) (hE : Effective E) :
    Effective (D + E) := by
  intro p
  have h1 : 0 ≤ D p := hD p
  have h2 : 0 ≤ E p := hE p
  simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply]
  omega

-- Candidate: Effective single (n ≥ 0)
lemma Effective_single {p : α} {n : ℤ} (hn : 0 ≤ n) : Effective (single p n) := by
  intro q
  simp only [single, Finsupp.coe_zero, Pi.zero_apply]
  by_cases h : q = p
  · simp [h, hn]
  · simp [h]

end Divisor

/-! ## Function Field Data (Cycle 5)

This structure axiomatizes the relationship between a function field K and divisors.
The key property is that principal divisors have degree zero, which is essential for RR.
-/

/-- Data for a function field associated with divisors on α.

This captures the relationship between meromorphic functions and divisors:
- `div f` is the principal divisor of f (zeros minus poles)
- `div` is a group homomorphism from K× to Div(α)
- Principal divisors have degree zero (fundamental for Riemann-Roch)
-/
structure FunctionFieldData (α : Type*) (k : Type*) [Field k] where
  /-- The function field -/
  K : Type*
  /-- K is a field -/
  [field : Field K]
  /-- K is a k-algebra (contains k as constants) -/
  [algebra : Algebra k K]
  /-- Principal divisor map: f ↦ div(f) = zeros - poles -/
  div : K → Divisor α
  /-- div is multiplicative: div(fg) = div(f) + div(g) -/
  div_mul : ∀ f g, div (f * g) = div f + div g
  /-- div(1) = 0 -/
  div_one : div 1 = 0
  /-- div(f⁻¹) = -div(f) for f ≠ 0 -/
  div_inv : ∀ f, f ≠ 0 → div f⁻¹ = -div f
  /-- Principal divisors have degree zero -/
  deg_div : ∀ f, f ≠ 0 → Divisor.deg (div f) = 0
  /-- Strong triangle inequality: div(f + g) ≥ min(div f, div g) pointwise.
      This is the key property that makes L(D) a vector subspace. -/
  div_add : ∀ f g, div f ⊓ div g ≤ div (f + g)
  /-- Constants have zero divisor: algebraMap k K embeds constants which have no zeros or poles -/
  div_algebraMap : ∀ c : k, div (algebraMap k K c) = 0

attribute [instance] FunctionFieldData.field
attribute [instance] FunctionFieldData.algebra

namespace FunctionFieldData

variable {α : Type*} {k : Type*} [Field k] (data : FunctionFieldData α k)

/-- div(0) = 0 (by convention, though 0 has no well-defined divisor) -/
lemma div_zero : data.div 0 = 0 := by
  have h : data.div (0 * 0) = data.div 0 + data.div 0 := data.div_mul 0 0
  simp only [mul_zero] at h
  -- h : data.div 0 = data.div 0 + data.div 0
  have h2 : data.div 0 - data.div 0 = (data.div 0 + data.div 0) - data.div 0 := congrArg (· - data.div 0) h
  simp only [sub_self, add_sub_cancel_right] at h2
  exact h2.symm

end FunctionFieldData

/-! ## Riemann-Roch Space L(D) (Cycles 5-6)

L(D) = { f ∈ K | f = 0 or div(f) + D ≥ 0 }

This is the space of meromorphic functions whose poles are bounded by D.
The dimension ℓ(D) = dim L(D) is what appears in the Riemann-Roch theorem.

**Cycle 6**: L(D) is a K-submodule (vector subspace). The key ingredients are:
- `div_add`: Strong triangle inequality ensures closure under addition
- `div_mul`: Multiplicativity ensures closure under scalar multiplication
-/

/-- The carrier set for L(D): functions f such that div(f) + D ≥ 0. -/
def RRSpaceCarrier {k : Type*} [Field k] (data : FunctionFieldData α k) (D : Divisor α) : Set data.K :=
  { f | f = 0 ∨ Divisor.Effective (data.div f + D) }

namespace RRSpace

variable {α : Type*} {k : Type*} [Field k] (data : FunctionFieldData α k) (D : Divisor α)

-- Zero is always in L(D)
lemma zero_mem' : (0 : data.K) ∈ RRSpaceCarrier data D := Or.inl rfl

-- Closure under addition using div_add (strong triangle inequality)
lemma add_mem' {f g : data.K} (hf : f ∈ RRSpaceCarrier data D) (hg : g ∈ RRSpaceCarrier data D) :
    f + g ∈ RRSpaceCarrier data D := by
  rcases hf with rfl | hf_eff
  · simp only [zero_add]; exact hg
  rcases hg with rfl | hg_eff
  · simp only [add_zero]; exact Or.inr hf_eff
  -- Both f, g nonzero with div f + D ≥ 0, div g + D ≥ 0
  by_cases h : f + g = 0
  · exact Or.inl h
  · right
    intro p
    -- Goal: 0 ≤ (div(f+g) + D) p
    -- We have: div f ⊓ div g ≤ div(f + g) from div_add
    -- And: div f + D ≥ 0, div g + D ≥ 0
    have htri := data.div_add f g
    have htri_p : (data.div f ⊓ data.div g) p ≤ (data.div (f + g)) p := htri p
    have hf_p : 0 ≤ (data.div f + D) p := hf_eff p
    have hg_p : 0 ≤ (data.div g + D) p := hg_eff p
    simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at hf_p hg_p ⊢
    simp only [Finsupp.inf_apply] at htri_p
    -- (div f) p ⊓ (div g) p ≤ (div (f+g)) p
    -- (div f) p + D p ≥ 0 means (div f) p ≥ -D p
    -- (div g) p + D p ≥ 0 means (div g) p ≥ -D p
    -- So min((div f) p, (div g) p) ≥ -D p
    -- Therefore (div (f+g)) p ≥ -D p, i.e., (div (f+g)) p + D p ≥ 0
    have : -D p ≤ (data.div f) p ⊓ (data.div g) p := by
      simp only [le_inf_iff]
      constructor <;> omega
    omega

-- Closure under scalar multiplication using div_mul and div_algebraMap
-- L(D) is a k-module: scalars are from the ground field k, not the function field K
lemma smul_mem' (c : k) {f : data.K} (hf : f ∈ RRSpaceCarrier data D) :
    c • f ∈ RRSpaceCarrier data D := by
  -- c • f = algebraMap k K c * f in an algebra
  simp only [Algebra.smul_def]
  rcases hf with rfl | hf_eff
  · simp only [mul_zero]; exact Or.inl rfl
  by_cases hc : c = 0
  · simp only [hc, map_zero, zero_mul]; exact Or.inl rfl
  by_cases hf_zero : f = 0
  · simp only [hf_zero, mul_zero]; exact Or.inl rfl
  -- c ≠ 0, f ≠ 0, so (algebraMap k K c) * f ≠ 0
  right
  intro p
  -- div((algebraMap k K c) * f) = div(algebraMap k K c) + div f = 0 + div f = div f
  have hmul := data.div_mul (algebraMap k data.K c) f
  have hconst := data.div_algebraMap c
  simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at hf_eff ⊢
  rw [hmul, hconst, Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply, zero_add]
  exact hf_eff p

end RRSpace

/-- The Riemann-Roch space L(D) as a k-submodule of K.

L(D) consists of functions f ∈ K such that div(f) + D ≥ 0.
This is a k-vector space because:
- div(f + g) ≥ min(div f, div g) (strong triangle inequality)
- div(c * f) = div c + div f = 0 + div f = div f for c ∈ k (constants have zero divisor) -/
def RRSpace {k : Type*} [Field k] (data : FunctionFieldData α k) (D : Divisor α) : Submodule k data.K where
  carrier := RRSpaceCarrier data D
  zero_mem' := RRSpace.zero_mem' data D
  add_mem' := RRSpace.add_mem' data D
  smul_mem' := RRSpace.smul_mem' data D

namespace RRSpace

variable {α : Type*} {k : Type*} [Field k] (data : FunctionFieldData α k) (D : Divisor α)

-- Monotonicity: D ≤ E → L(D) ⊆ L(E)
lemma mono {D E : Divisor α} (h : D ≤ E) : (RRSpace data D : Set data.K) ⊆ RRSpace data E := by
  intro f hf
  simp only [SetLike.mem_coe] at hf ⊢
  rcases hf with rfl | heff
  · exact Or.inl rfl
  · right
    intro p
    have hD : 0 ≤ (data.div f + D) p := heff p
    have hDE : D p ≤ E p := h p
    simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at hD ⊢
    omega

end RRSpace

/-! ## Dimension ℓ(D) = finrank k L(D) (Cycle 7)

The dimension ℓ(D) of the Riemann-Roch space L(D) is what appears in the
Riemann-Roch theorem: ℓ(D) - ℓ(K - D) = deg D + 1 - g
-/

/-- The dimension ℓ(D) of the Riemann-Roch space L(D).
This is the key invariant in the Riemann-Roch theorem. -/
noncomputable def ell {α : Type*} {k : Type*} [Field k] (data : FunctionFieldData α k)
    (D : Divisor α) : ℕ := Module.finrank k (RRSpace data D)

namespace RRSpace

variable {α : Type*} {k : Type*} [Field k] (data : FunctionFieldData α k)

-- Candidate 2: Convert set inclusion to submodule inequality
lemma le_of_divisor_le {D E : Divisor α} (h : D ≤ E) :
    RRSpace data D ≤ RRSpace data E :=
  SetLike.coe_subset_coe.mp (mono data h)

-- Candidate 4: 1 ∈ L(D) if D is effective
lemma one_mem_of_effective {D : Divisor α} (hD : Divisor.Effective D) :
    (1 : data.K) ∈ RRSpace data D := by
  right
  rw [data.div_one, zero_add]
  exact hD

-- Candidate 6: Constants are in L(0)
lemma algebraMap_mem_zero (c : k) :
    algebraMap k data.K c ∈ RRSpace data 0 := by
  by_cases hc : c = 0
  · simp only [hc, map_zero]; exact Or.inl rfl
  · right
    rw [data.div_algebraMap, zero_add]
    exact Divisor.Effective_zero

-- Candidate 8: Constants are in L(D) for effective D
lemma algebraMap_mem_of_effective {D : Divisor α} (hD : Divisor.Effective D) (c : k) :
    algebraMap k data.K c ∈ RRSpace data D := by
  by_cases hc : c = 0
  · simp only [hc, map_zero]; exact Or.inl rfl
  · right
    rw [data.div_algebraMap, zero_add]
    exact hD

end RRSpace

namespace ell

variable {α : Type*} {k : Type*} [Field k] (data : FunctionFieldData α k)

-- Candidate 3: Monotonicity of ℓ
lemma mono {D E : Divisor α} [Module.Finite k (RRSpace data E)] (h : D ≤ E) :
    ell data D ≤ ell data E := by
  unfold ell
  exact Submodule.finrank_mono (RRSpace.le_of_divisor_le data h)

-- Candidate 5: ℓ(D) ≥ 1 for effective D
lemma pos_of_effective {D : Divisor α} [Module.Finite k (RRSpace data D)]
    (hD : Divisor.Effective D) : 1 ≤ ell data D := by
  unfold ell
  have h1 : (1 : data.K) ∈ RRSpace data D := RRSpace.one_mem_of_effective data hD
  have hne : (1 : data.K) ≠ 0 := one_ne_zero
  -- L(D) contains a nonzero element, so finrank ≥ 1
  have hnt : Nontrivial (RRSpace data D) := ⟨⟨⟨1, h1⟩, ⟨0, (RRSpace data D).zero_mem⟩,
    fun heq => hne (Subtype.ext_iff.mp heq)⟩⟩
  exact Module.finrank_pos_iff.mpr hnt

-- Candidate 7: ℓ(0) ≥ 1
lemma zero_pos [Module.Finite k (RRSpace data (0 : Divisor α))] [Nontrivial k] :
    1 ≤ ell data 0 :=
  pos_of_effective data Divisor.Effective_zero

end ell

/-!
# Riemann-Roch Theorem: Axiomatized Interface

## WARNING: This is NOT a proof of Riemann-Roch

This file contains an **axiomatized theory interface** for Riemann-Roch, not a proof.
The theorem `RRDataWithEuler.riemannRoch` is derived from assumed structure fields,
including `eulerChar_formula` which IS the Riemann-Roch equation in disguise.

**What we have**: An interface that elaborates in Lean, showing the algebraic structure of RR.
**What we don't have**: A proof from first principles or mathlib foundations.

## Why this exists

mathlib (as of Dec 2024) lacks the fundamental objects needed for RR:
- Divisors (Weil or Cartier) on schemes
- Line bundles / invertible sheaves
- Sheaf cohomology H⁰, H¹
- Genus, degree for curves
- Serre duality theorem

Without these, we cannot state or prove RR using real mathematical objects.
This file defines abstract interfaces that capture the *shape* of RR.

## Structure hierarchy

- `RRData`: Base interface with curve, divisors, deg, ℓ, genus, K
- `RRDataWithCohomology`: Adds h¹ and Serre duality (as assumed field)
- `RRDataWithEuler`: Adds Euler characteristic formula (= RR, as assumed field)

## Semantic status

| Component | Status |
|-----------|--------|
| `RRData` | Abstract interface, no assumptions |
| `RRDataWithCohomology.serreDuality` | **ASSUMPTION** (deep theorem) |
| `RRDataWithEuler.eulerChar_formula` | **ASSUMPTION** (= Riemann-Roch!) |
| `RRDataWithEuler.riemannRoch` | DERIVED from above assumptions |

The derivation is algebraically valid but mathematically circular.
-/

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- Abstract data for Riemann-Roch theorem on curves.

This bundles curve, divisor, degree, ℓ-function, and genus
without requiring mathlib definitions that don't exist.

**Note**: This is an abstract interface. `Div` has no semantic connection to `X`.
To instantiate with real objects, mathlib would need divisor definitions. -/
structure RRData (k : Type*) [Field k] where
  /-- The underlying scheme (a smooth projective curve) -/
  X : Scheme
  /-- The structure morphism to Spec k -/
  toSpec : X ⟶ Spec (.of k)
  /-- Divisor type on X (abstract, not connected to X) -/
  Div : Type*
  /-- Divisors form an additive group -/
  divAddCommGroup : AddCommGroup Div
  /-- Degree of a divisor (integer-valued) -/
  deg : Div → ℤ
  /-- Degree is additive -/
  deg_add : ∀ D E : Div, deg (divAddCommGroup.toAdd.add D E) = deg D + deg E
  /-- Dimension of H⁰(X, O_X(D)) as a natural number (abstract) -/
  ell : Div → ℕ
  /-- Genus of the curve (abstract) -/
  genus : ℕ
  /-- Canonical divisor (abstract) -/
  K : Div

namespace RRData

variable {k : Type*} [Field k] (data : RRData k)

instance : AddCommGroup data.Div := data.divAddCommGroup

/-- The Riemann-Roch equation as a proposition.
    ℓ(D) - ℓ(K - D) = deg(D) + 1 - g -/
def riemannRochEq (D : data.Div) : Prop :=
  (data.ell D : ℤ) - (data.ell (data.K - D) : ℤ) = data.deg D + 1 - data.genus

end RRData

/-! ## Extended Structures with Assumed Axioms

**WARNING**: The Prop fields in these structures are **assumptions**, not derived facts.
`serreDuality` assumes Serre duality holds.
`eulerChar_formula` assumes the Riemann-Roch equation for Euler characteristic.
-/

/-- RRData extended with H¹ dimension and Serre duality.

**ASSUMPTION**: `serreDuality` is a deep theorem in algebraic geometry.
We assume it as a structure field, not prove it. -/
structure RRDataWithCohomology (k : Type*) [Field k] extends RRData k where
  /-- Dimension of H¹(X, O_X(D)) (abstract) -/
  h1 : Div → ℕ
  /-- **ASSUMED**: Serre duality: ℓ(K - D) = h¹(D) -/
  serreDuality : ∀ D : Div, ell (K - D) = h1 D

/-- RRDataWithCohomology extended with Euler characteristic.

**ASSUMPTION**: `eulerChar_formula` IS the Riemann-Roch theorem for Euler characteristic.
Assuming this field and deriving RR from it is **circular**. -/
structure RRDataWithEuler (k : Type*) [Field k] extends RRDataWithCohomology k where
  /-- Euler characteristic χ(D) -/
  eulerChar : Div → ℤ
  /-- Euler characteristic equals ℓ(D) - h¹(D) (definition, harmless) -/
  eulerChar_def : ∀ D : Div, eulerChar D = (ell D : ℤ) - (h1 D : ℤ)
  /-- **ASSUMED**: χ(D) = deg(D) + 1 - g. THIS IS RIEMANN-ROCH. -/
  eulerChar_formula : ∀ D : Div, eulerChar D = deg D + 1 - genus

/-! ## Lemmas derived from assumptions -/

namespace RRDataWithCohomology

variable {k : Type*} [Field k] (data : RRDataWithCohomology k)

instance : AddCommGroup data.Div := data.divAddCommGroup

/-- Serre duality (from assumed field) -/
lemma serreDuality_eq (D : data.Div) :
    data.ell (data.K - D) = data.h1 D :=
  data.serreDuality D

end RRDataWithCohomology

namespace RRDataWithEuler

variable {k : Type*} [Field k] (data : RRDataWithEuler k)

instance : AddCommGroup data.Div := data.divAddCommGroup

/-- Euler characteristic equals ℓ(D) - h¹(D) (from definition field) -/
lemma eulerChar_eq_ell_sub_h1 (D : data.Div) :
    data.eulerChar D = (data.ell D : ℤ) - (data.h1 D : ℤ) :=
  data.eulerChar_def D

/-- Euler characteristic formula (from assumed field) -/
lemma eulerChar_eq_deg (D : data.Div) :
    data.eulerChar D = data.deg D + 1 - data.genus :=
  data.eulerChar_formula D

/-- Combining definition and assumed formula -/
lemma ell_sub_h1_eq_deg (D : data.Div) :
    (data.ell D : ℤ) - (data.h1 D : ℤ) = data.deg D + 1 - data.genus := by
  rw [← data.eulerChar_def D, data.eulerChar_formula D]

/-- Substituting Serre duality -/
lemma ell_sub_ell_K_sub_D (D : data.Div) :
    (data.ell D : ℤ) - (data.ell (data.K - D) : ℤ) = data.deg D + 1 - data.genus := by
  have h := data.serreDuality D
  simp only [h]
  exact data.ell_sub_h1_eq_deg D

/-- Riemann-Roch "theorem" for RRDataWithEuler.

**WARNING**: This is DERIVED FROM ASSUMPTIONS, not proved from first principles.
The assumed field `eulerChar_formula` IS the Riemann-Roch equation.
This derivation is algebraically valid but mathematically circular.

To actually prove RR, one would need to:
1. Define real divisors, line bundles, sheaf cohomology in Lean
2. Prove Serre duality from first principles
3. Prove the Euler characteristic formula from first principles
None of this infrastructure exists in mathlib as of Dec 2024. -/
theorem riemannRoch (D : data.Div) : data.riemannRochEq D :=
  data.ell_sub_ell_K_sub_D D

end RRDataWithEuler

/-! ## Base RRData theorem (no proof path without assumptions) -/

/-- Riemann-Roch for base RRData.

This has `sorry` because RRData lacks the assumed fields needed for derivation.
There is no known proof path without real mathlib infrastructure. -/
theorem riemannRoch {k : Type*} [Field k] (data : RRData k) (D : data.Div) :
    data.riemannRochEq D := by
  sorry

/-- Riemann-Roch (expanded form) for base RRData. -/
theorem riemannRoch' {k : Type*} [Field k] (data : RRData k) (D : data.Div) :
    (data.ell D : ℤ) - (data.ell (data.K - D) : ℤ) = data.deg D + 1 - data.genus := by
  sorry

/-! ## Cycle 8 Candidates: Finite-Dimensionality and Unconditional Bounds

The key observation is that all Riemann-Roch spaces L(D) should be finite-dimensional.
Rather than modifying FunctionFieldData, we use a typeclass instance hypothesis.
-/

-- Candidate 1 [tag: degree_bridge] [status: PROVED]
-- Unconditional monotonicity with typeclass instance
lemma ell.mono_unconditional {α : Type*} {k : Type*} [Field k]
    (data : FunctionFieldData α k) [hFin : ∀ D, Module.Finite k (RRSpace data D)]
    {D E : Divisor α} (h : D ≤ E) :
    ell data D ≤ ell data E := by
  haveI : Module.Finite k (RRSpace data E) := hFin E
  exact ell.mono data h

-- Candidate 2 [tag: degree_bridge] [status: PROVED]
-- Unconditional positivity for effective divisors
lemma ell.pos_of_effective_unconditional {α : Type*} {k : Type*} [Field k]
    (data : FunctionFieldData α k) [hFin : ∀ D, Module.Finite k (RRSpace data D)]
    {D : Divisor α} (hD : Divisor.Effective D) :
    1 ≤ ell data D := by
  haveI : Module.Finite k (RRSpace data D) := hFin D
  exact ell.pos_of_effective data hD

-- Candidate 3 [tag: degree_bridge] [status: PROVED]
-- ℓ(D) ≥ ℓ(0) for effective D
lemma ell.ge_zero_of_effective {α : Type*} {k : Type*} [Field k]
    (data : FunctionFieldData α k) [hFin : ∀ D, Module.Finite k (RRSpace data D)]
    {D : Divisor α} (hD : Divisor.Effective D) :
    ell data 0 ≤ ell data D := by
  exact ell.mono_unconditional data hD

-- Candidate 4 [tag: degree_bridge] [status: PROVED]
-- Monotonicity for effective divisors (explicit version)
lemma ell.mono_of_effective {α : Type*} {k : Type*} [Field k]
    (data : FunctionFieldData α k) [hFin : ∀ D, Module.Finite k (RRSpace data D)]
    {D E : Divisor α} (_hD : Divisor.Effective D) (_hE : Divisor.Effective E) (h : D ≤ E) :
    ell data D ≤ ell data E :=
  ell.mono_unconditional data h

-- Candidate 5 [tag: degree_bridge] [status: PROVED]
-- Adding effective divisors increases dimension
lemma ell.add_effective_le {α : Type*} {k : Type*} [Field k]
    (data : FunctionFieldData α k) [hFin : ∀ D, Module.Finite k (RRSpace data D)]
    {D E : Divisor α} (_hD : Divisor.Effective D) (hE : Divisor.Effective E) :
    ell data D ≤ ell data (D + E) := by
  apply ell.mono_unconditional
  intro p
  have h2 : 0 ≤ E p := hE p
  simp only [Finsupp.add_apply]
  omega

-- Candidate 6 [tag: degree_bridge] [status: PROVED]
-- Zero divisor has positive dimension (unconditional)
lemma ell.zero_pos_unconditional {α : Type*} {k : Type*} [Field k]
    (data : FunctionFieldData α k) [hFin : ∀ D, Module.Finite k (RRSpace data D)] [Nontrivial k] :
    1 ≤ ell data 0 := by
  haveI : Module.Finite k (RRSpace data 0) := hFin 0
  exact ell.zero_pos data

-- Candidate 7 [tag: rewrite_bridge] [status: PROVED]
-- Nontriviality of L(D) for effective D
lemma RRSpace.nontrivial_of_effective {α : Type*} {k : Type*} [Field k]
    (data : FunctionFieldData α k) {D : Divisor α} (hD : Divisor.Effective D) :
    Nontrivial (RRSpace data D) := by
  have h1 : (1 : data.K) ∈ RRSpace data D := RRSpace.one_mem_of_effective data hD
  have hne : (1 : data.K) ≠ 0 := one_ne_zero
  exact ⟨⟨⟨1, h1⟩, ⟨0, (RRSpace data D).zero_mem⟩, fun heq => hne (Subtype.ext_iff.mp heq)⟩⟩

-- Candidate 8 [tag: degree_bridge] [status: PROVED]
-- Integer cast version of monotonicity
lemma ell.diff_le_deg_diff {α : Type*} {k : Type*} [Field k]
    (data : FunctionFieldData α k) [hFin : ∀ D, Module.Finite k (RRSpace data D)]
    {D E : Divisor α} (_hD : Divisor.Effective D) (h : D ≤ E) :
    (ell data D : ℤ) ≤ (ell data E : ℤ) := by
  exact Int.ofNat_le.mpr (ell.mono_unconditional data h)

end RiemannRoch
