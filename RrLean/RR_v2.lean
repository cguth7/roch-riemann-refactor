import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Order

/-!
# Riemann-Roch V2: Constructive Dedekind Domain Approach

This file implements the Riemann-Roch theorem using real mathlib infrastructure
based on Dedekind domains, rather than the axiom-based approach in RR.lean.

## Strategy (Jiedong Jiang approach)

1. **Points**: HeightOneSpectrum R (height-1 primes of Dedekind domain R)
2. **Divisors**: HeightOneSpectrum R →₀ ℤ (finitely supported formal sums)
3. **L(D)**: Defined via valuations at each prime
4. **ℓ(D)**: Module.length (additive in exact sequences)
5. **Proofs**: Use DVR localization and exact sequence additivity

## Affine vs Projective Models (Cycle 23 Discovery)

**CRITICAL ARCHITECTURAL DISTINCTION**:

**Affine Model** (current HeightOneSpectrum R implementation):
- Points = finite places only (height-1 primes of R)
- L(0) = R (all integral functions) → ℓ(0) = ∞ for Dedekind domains
- Proves: ℓ(D) ≤ deg(D) + ℓ(0) (affine Riemann inequality)
- Typeclass: `LocalGapBound R K` (gap ≤ 1 via evaluation map)

**Projective Model** (requires compactification):
- Points = finite + infinite places (complete curve)
- L(0) = k (only constants) → ℓ(0) = 1
- Proves: ℓ(D) ≤ deg(D) + 1 (classical Riemann inequality)
- Typeclass: `SinglePointBound R K extends LocalGapBound R K`

**Typeclass Hierarchy**:
```
LocalGapBound R K          -- PROVABLE (gap ≤ 1 via evaluation)
    ↑ extends
SinglePointBound R K       -- PROJECTIVE (adds ℓ(0) = 1)

BaseDim R K                -- SEPARATE: explicit base dimension
```

The `LocalGapBound` captures what's derivable from DVR structure alone.
The `SinglePointBound` adds global completeness (proper curve).
The `BaseDim` provides the base constant explicitly.

## References
- mathlib: RingTheory.DedekindDomain.*
- mathlib: RingTheory.Length (Module.length_eq_add_of_exact)
-/

namespace RiemannRochV2

open IsDedekindDomain

/-! ## Divisor Foundations -/

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]

-- Candidate 1 [tag: bundle_divisor_bridge] [status: OK]
/-- A divisor on a Dedekind domain is a finitely supported function from height-1 primes to ℤ.
This is the constructive analog of formal sums of points on a curve.
HeightOneSpectrum R represents the "points" of the associated curve. -/
abbrev DivisorV2 := HeightOneSpectrum R →₀ ℤ

namespace DivisorV2

variable {R}

set_option linter.unusedSectionVars false in
section
variable [IsDomain R] [IsDedekindDomain R]

-- Candidate 2 [tag: degree_bridge] [status: OK]
/-- The degree of a divisor is the sum of its coefficients.
For a curve, this is the total number of points counted with multiplicity. -/
def deg (D : DivisorV2 R) : ℤ := D.sum (fun _ n => n)

-- Candidate 3 [tag: degree_bridge] [status: PROVED]
/-- Degree is additive. -/
lemma deg_add (D E : DivisorV2 R) : deg (D + E) = deg D + deg E := by
  simp only [deg]
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- Degree of zero divisor. -/
lemma deg_zero : deg (0 : DivisorV2 R) = 0 := by
  simp only [deg, Finsupp.sum_zero_index]

/-- Degree of negation. -/
lemma deg_neg (D : DivisorV2 R) : deg (-D) = -deg D := by
  have h : deg (D + (-D)) = deg D + deg (-D) := deg_add D (-D)
  simp only [add_neg_cancel, deg_zero] at h
  omega

/-- Single-point divisor constructor (n · v). -/
noncomputable abbrev single (v : HeightOneSpectrum R) (n : ℤ) : DivisorV2 R :=
  Finsupp.single v n

/-- Degree of single-point divisor. -/
lemma deg_single (v : HeightOneSpectrum R) (n : ℤ) : deg (single v n) = n := by
  simp only [deg, single, Finsupp.sum_single_index]

/-- A divisor is effective if all coefficients are non-negative. -/
def Effective (D : DivisorV2 R) : Prop := 0 ≤ D

lemma Effective_iff (D : DivisorV2 R) : Effective D ↔ ∀ v, 0 ≤ D v := Iff.rfl

lemma Effective_zero : Effective (0 : DivisorV2 R) := le_refl 0

end

end DivisorV2

/-! ## Riemann-Roch Space L(D)

The key insight is that L(D) = {f ∈ K : ord_v(f) + D(v) ≥ 0 for all v}
where K is the fraction field and ord_v is the valuation at prime v.
-/

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 8 [tag: bundle_divisor_bridge] [status: PROVED]
/-- At each height-1 prime v, the localization is a discrete valuation ring.
This is the foundational fact that enables us to define valuations ord_v. -/
instance localization_at_prime_is_dvr (v : HeightOneSpectrum R) :
    IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot _

/-! ## Cycle 18: Valuation-based membership condition

The key insight is that the v-adic valuation from `HeightOneSpectrum.valuation` allows
us to define the membership condition for L(D):

  f ∈ L(D) ⟺ f = 0 ∨ (∀ v, v.valuation K f ≥ WithZero.exp (-D v))

This uses the multiplicative notation where:
- `v.valuation K f : ℤᵐ⁰ = WithZero (Multiplicative ℤ)`
- `WithZero.exp n` embeds n : ℤ into ℤᵐ⁰
- The condition `ord_v(f) + D(v) ≥ 0` becomes `v.valuation K f ≥ WithZero.exp (-D v)`
-/

-- Candidate 2 [tag: membership_condition] [status: PROVED]
/-- The membership condition for L(D): f = 0 or all valuations satisfy ord_v(f) + D(v) ≥ 0.
In multiplicative notation: v.valuation K f ≤ WithZero.exp (D v).

Mathematical explanation:
- Standard convention: ord_v(f) ≥ -D(v) (poles bounded by D)
- Mathlib's multiplicative valuation: v(f) = exp(-ord_v(f))
- So ord_v(f) ≥ -D(v) becomes -ord_v(f) ≤ D(v), i.e., v(f) ≤ exp(D(v))
-/
def satisfiesValuationCondition (D : DivisorV2 R) (f : K) : Prop :=
  f = 0 ∨ ∀ v : HeightOneSpectrum R, v.valuation K f ≤ WithZero.exp (D v)

-- Candidate 3 [tag: rrmodule_real] [status: PROVED]
/-- The Riemann-Roch space L(D) as a submodule of K (REAL VERSION).

L(D) = {f ∈ K : f = 0 ∨ (∀ v, v.valuation K f ≤ WithZero.exp (D v))}

This is the space of functions whose poles are bounded by D. -/
def RRModuleV2_real (D : DivisorV2 R) : Submodule R K where
  carrier := { f | satisfiesValuationCondition R K D f }
  zero_mem' := Or.inl rfl
  add_mem' := fun {a b} ha hb => by
    by_cases h : a + b = 0
    · exact Or.inl h
    · right
      intro v
      rcases ha with rfl | ha'
      · simp only [zero_add] at h ⊢
        rcases hb with rfl | hb'
        · exact absurd rfl h
        · exact hb' v
      rcases hb with rfl | hb'
      · simp only [add_zero] at h ⊢
        exact ha' v
      -- Both a and b are nonzero with valuation bounds
      have hav := ha' v
      have hbv := hb' v
      -- The ultrametric inequality: v(a+b) ≤ max(v(a), v(b))
      calc v.valuation K (a + b)
          ≤ max (v.valuation K a) (v.valuation K b) := by
            exact Valuation.map_add_le_max' (v.valuation K) a b
        _ ≤ WithZero.exp (D v) := by
            exact max_le hav hbv
  smul_mem' := fun r {f} hf => by
    by_cases h : r • f = 0
    · exact Or.inl h
    · right
      intro v
      -- r • f = algebraMap R K r * f for an algebra
      simp only [Algebra.smul_def]
      -- v.valuation K (r * f) = v.valuation K r * v.valuation K f
      rw [(v.valuation K).map_mul]
      rcases hf with rfl | hf'
      · exfalso; apply h; simp only [smul_zero]
      have hfv := hf' v
      -- Key: v.valuation K (algebraMap R K r) ≤ 1 for all r ∈ R
      have hr : v.valuation K (algebraMap R K r) ≤ 1 := by
        exact HeightOneSpectrum.valuation_le_one v r
      -- For ordered monoids: if a ≤ b and c ≤ d then a*c ≤ b*d
      calc v.valuation K (algebraMap R K r) * v.valuation K f
          ≤ 1 * WithZero.exp (D v) := by
            exact mul_le_mul' hr hfv
        _ = WithZero.exp (D v) := by
            exact one_mul _

set_option linter.unusedSectionVars false in
-- Candidate 4 [tag: zero_mem_real] [status: PROVED]
/-- Zero is in L(D) for any divisor D. -/
lemma RRModuleV2_real_zero_mem (D : DivisorV2 R) :
    (0 : K) ∈ (RRModuleV2_real R K D).carrier := Or.inl rfl

set_option linter.unusedSectionVars false in
-- Candidate 7 [tag: inclusion_submodule] [status: PROVED]
/-- When D ≤ E, we have L(D) ⊆ L(E), giving a submodule inclusion. -/
lemma RRModuleV2_mono_inclusion {D E : DivisorV2 R} (hDE : D ≤ E) :
    RRModuleV2_real R K D ≤ RRModuleV2_real R K E := by
  intro f hf
  cases hf with
  | inl h => exact Or.inl h
  | inr h =>
    apply Or.inr
    intro v
    have hDv := hDE v  -- D v ≤ E v
    have hfv := h v    -- v.valuation K f ≤ WithZero.exp (D v)
    -- Since D v ≤ E v, we have WithZero.exp (D v) ≤ WithZero.exp (E v)
    -- So v.valuation K f ≤ WithZero.exp (D v) ≤ WithZero.exp (E v)
    calc v.valuation K f ≤ WithZero.exp (D v) := hfv
       _ ≤ WithZero.exp (E v) := by
           apply WithZero.exp_le_exp.mpr
           exact hDv

/-! ## Cycle 20: ℓ(D) using RRModuleV2_real -/

-- Candidate 1 [tag: rr_bundle_bridge] [status: OK]
/-- The dimension ℓ(D) of L(D) using module length (REAL VERSION).

Uses RRModuleV2_real which has the correct valuation-based membership condition.
Module.length is additive in exact sequences, which is key for proving Riemann-Roch.

Returns ℕ∞ because length can be infinite; we extract ℕ when finite. -/
noncomputable def ellV2_real_extended (D : DivisorV2 R) : ℕ∞ :=
  Module.length R (RRModuleV2_real R K D)

-- Candidate 2 [tag: rr_bundle_bridge] [status: OK]
/-- The dimension ℓ(D) as a natural number (REAL VERSION, assuming finiteness). -/
noncomputable def ellV2_real (D : DivisorV2 R) : ℕ :=
  (ellV2_real_extended R K D).toNat

-- Candidate 3 [tag: rr_bundle_bridge] [status: PROVED]
/-- Monotonicity: D ≤ E implies ℓ(D) ≤ ℓ(E) at the ℕ∞ level.

PROOF STRATEGY:
1. Use RRModuleV2_mono_inclusion (already PROVED) to get L(D) ≤ L(E)
2. Apply Submodule.inclusion to get an injective linear map L(D) →ₗ[R] L(E)
3. Use Submodule.inclusion_injective to verify injectivity
4. Apply Module.length_le_of_injective to get length(L(D)) ≤ length(L(E)) -/
lemma ellV2_real_mono_extended {D E : DivisorV2 R} (hDE : D ≤ E) :
    ellV2_real_extended R K D ≤ ellV2_real_extended R K E := by
  unfold ellV2_real_extended
  -- Get the submodule inclusion L(D) ≤ L(E)
  have hle := RRModuleV2_mono_inclusion R K hDE
  -- Apply Module.length_le_of_injective with the inclusion map
  exact Module.length_le_of_injective
    (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

-- Candidate 4 [tag: rr_bundle_bridge] [status: PROVED]
/-- Monotonicity at the ℕ level: D ≤ E implies ℓ(D) ≤ ℓ(E).

Uses ellV2_real_mono_extended and ENat.toNat_le_toNat.
Note: This requires finiteness of ellV2_real_extended E. Without that hypothesis,
we use the fact that toNat maps ⊤ to 0, so the inequality holds trivially. -/
lemma ellV2_real_mono {D E : DivisorV2 R} (hDE : D ≤ E)
    (hfin : ellV2_real_extended R K E ≠ ⊤) :
    ellV2_real R K D ≤ ellV2_real R K E := by
  unfold ellV2_real
  exact ENat.toNat_le_toNat (ellV2_real_mono_extended R K hDE) hfin

-- Candidate 5 [tag: rr_bundle_bridge] [status: PROVED]
/-- Alternative monotonicity: always holds, but may give 0 for infinite length. -/
lemma ellV2_real_mono' {D E : DivisorV2 R} (hDE : D ≤ E) :
    ellV2_real R K D ≤ ellV2_real R K E ∨ ellV2_real_extended R K E = ⊤ := by
  by_cases h : ellV2_real_extended R K E = ⊤
  · exact Or.inr h
  · exact Or.inl (ellV2_real_mono R K hDE h)

/-! ## Original placeholder (kept for reference) -/

-- Candidate 4 [tag: bundle_divisor_bridge] [status: OK]
/-- The Riemann-Roch space L(D) as a submodule of K.

L(D) = {f ∈ K : f = 0 ∨ (∀ v, ord_v(f) + D(v) ≥ 0)}

This is the space of functions whose poles are bounded by D.

NOTE: The full definition requires valuations at each HeightOneSpectrum prime.
For now we provide the structure; the membership condition uses sorry. -/
def RRModuleV2 (_D : DivisorV2 R) : Submodule R K where
  carrier := { f | f = 0 ∨ True }  -- Placeholder: real condition uses valuations
  zero_mem' := Or.inl rfl
  add_mem' := fun _ _ => Or.inr trivial  -- Placeholder
  smul_mem' := fun _ _ _ => Or.inr trivial  -- Placeholder

-- Candidate 5 [tag: rr_bundle_bridge] [status: OK]
/-- The dimension ℓ(D) of L(D) using module length.

Module.length is additive in exact sequences (Module.length_eq_add_of_exact),
which is the key property for proving Riemann-Roch by induction.

Returns ℕ∞ because length can be infinite; we extract ℕ when finite. -/
noncomputable def ellV2_extended (D : DivisorV2 R) : ℕ∞ :=
  Module.length R (RRModuleV2 R K D)

/-- The dimension ℓ(D) as a natural number (assuming finiteness). -/
noncomputable def ellV2 (D : DivisorV2 R) : ℕ :=
  (ellV2_extended R K D).toNat

-- Candidate 6 [tag: rr_bundle_bridge] [status: BLOCKED]
/-- Monotonicity: D ≤ E implies ℓ(D) ≤ ℓ(E).

PROOF STRATEGY: When D ≤ E, we have L(D) ⊆ L(E), giving a short exact sequence
  0 → L(D) → L(E) → L(E)/L(D) → 0
By Module.length_eq_add_of_exact: ℓ(D) + length(quotient) = ℓ(E)
Since length(quotient) ≥ 0, we get ℓ(D) ≤ ℓ(E).

BLOCKED: Requires proper definition of RRModuleV2 with valuation conditions. -/
lemma ellV2_mono {D E : DivisorV2 R} (hDE : D ≤ E) :
    ellV2 R K D ≤ ellV2 R K E := by
  sorry

-- Candidate 7 [tag: bundle_divisor_bridge] [status: OK]
/-- The fractional ideal associated to a divisor D.

In a Dedekind domain, there's a bijection between:
- Divisors: D = Σ n_v · v
- Fractional ideals: I = ∏ v^{n_v}

This uses the prime factorization structure of Dedekind domains.

NOTE: Full implementation requires mathlib's fractional ideal API. -/
noncomputable def divisorToFractionalIdeal (_D : DivisorV2 R) :
    FractionalIdeal (nonZeroDivisors R) K := 1
  -- Placeholder: real implementation is ∏_{v} v^{D(v)} as fractional ideal

/-! ## Key Properties for Riemann-Roch

The constructive proof strategy uses these facts:

1. **Single-point bound**: Adding one point increases ℓ by at most 1
   - Proof: evaluation map L(D+v) → κ(v) has kernel containing L(D)
   - The residue field κ(v) has dimension 1 over the ground field

2. **Exact sequence additivity**: Module.length_eq_add_of_exact
   - If 0 → A → B → C → 0 exact, then length(A) + length(C) = length(B)

3. **DVR structure**: At each prime v, localization is DVR
   - Gives well-defined valuation ord_v : K× → ℤ
   - ord_v(fg) = ord_v(f) + ord_v(g)
   - ord_v(f+g) ≥ min(ord_v(f), ord_v(g))

4. **Degree-length connection**: For D effective,
   - ℓ(D) ≤ deg(D) + 1 (Riemann inequality)
   - Proof by induction on deg(D) using single-point bound
-/

/-! ## Cycle 21-23: LocalGapBound / SinglePointBound Typeclass Hierarchy

### Cycle 23 Refactor: Affine vs Projective Model Distinction

**Problem (discovered Cycle 22)**:
- `ell_zero_eq_one : ellV2_real R K 0 = 1` is IMPOSSIBLE for affine models
- HeightOneSpectrum R captures only FINITE places
- L(0) = R (integral elements) → Module.length R R = ⊤

**Solution: Two-tier typeclass hierarchy**:
- `LocalGapBound`: PROVABLE (gap ≤ 1 via evaluation map to residue field)
- `SinglePointBound extends LocalGapBound`: PROJECTIVE (adds ℓ(0) = 1)
- `BaseDim`: SEPARATE (explicit base dimension constant)
-/

-- Candidate 1 [tag: typeclass_local_gap_bound] [status: OK] [cycle: 23]
/-- Typeclass capturing the local gap bound for Riemann-Roch (AFFINE VERSION).

This encodes ONE key geometric fact that's PROVABLE from affine model:
1. Adding a single point increases ℓ(D) by at most 1 (gap_le_one)

The bound comes from the evaluation map L(D + v) → κ(v) with kernel ⊇ L(D).

This is the PROVABLE subset that works for affine models (HeightOneSpectrum R).
Does NOT assume ℓ(0) = 1, which requires compactification. -/
class LocalGapBound (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] where
  /-- Adding a single point increases dimension by at most 1 -/
  gap_le_one : ∀ (D : DivisorV2 R) (v : HeightOneSpectrum R),
    ellV2_real R K (D + DivisorV2.single v 1) ≤ ellV2_real R K D + 1

-- Candidate 2 [tag: typeclass_single_point_bound] [status: OK] [cycle: 23]
/-- Typeclass capturing the single-point dimension bound for Riemann-Roch (PROJECTIVE VERSION).

This extends LocalGapBound with the additional axiom:
2. The only functions with no poles are constants, so ℓ(0) = 1 (ell_zero_eq_one)

This REQUIRES compactification (including infinite places).
For affine models using HeightOneSpectrum R alone, ell_zero_eq_one is FALSE.

Geometric meaning:
- LocalGapBound: Local evaluation gives dimension jump ≤ 1
- ell_zero_eq_one: Global holomorphic sections = constants (proper curve)

These axioms enable the degree induction proof of Riemann inequality. -/
class SinglePointBound (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    extends LocalGapBound R K where
  /-- L(0) has dimension 1 (only constants have no poles) -/
  ell_zero_eq_one : ellV2_real R K 0 = 1

-- Candidate 3 [tag: typeclass_base_dim] [status: OK] [cycle: 23]
/-- Typeclass providing the base dimension constant for Riemann-Roch.

For affine models: basedim = ℓ_affine(0) (dimension of integral functions)
For projective models: basedim = ℓ(0) = 1 (only constants)

This separates the DIMENSION CONSTANT from the PROVABILITY ASSUMPTION.

Example values:
- Function field k(t) affine: basedim = ∞ (k[t] has infinite length)
- Function field k(t) projective: basedim = 1 (only constants k)
- Elliptic curve: basedim = 1 -/
class BaseDim (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] where
  /-- The base dimension ℓ(0) -/
  basedim : ℕ
  /-- The base dimension equals ℓ(0) -/
  ell_zero_eq : ellV2_real R K 0 = basedim

-- Candidate 6 [tag: instance_single_to_base] [status: OK] [cycle: 23]
/-- Derive BaseDim instance from SinglePointBound.

For projective models with SinglePointBound, we get basedim = 1.
This instance allows reusing affine results in projective contexts. -/
instance SinglePointBound.toBaseDim [spb : SinglePointBound R K] : BaseDim R K where
  basedim := 1
  ell_zero_eq := spb.ell_zero_eq_one

namespace DivisorV2

-- Candidate 2 [tag: degree_helpers] [status: OK]
/-- Degree of D + single v 1 is deg D + 1. -/
lemma deg_add_single' (D : DivisorV2 R) (v : HeightOneSpectrum R) :
    (D + DivisorV2.single v 1).deg = D.deg + 1 := by
  rw [deg_add, deg_single]

-- Candidate 3 [tag: degree_helpers] [status: OK]
/-- If D is effective with positive degree, there exists v with D(v) > 0.
This is key for "peeling off" a point in the induction step. -/
lemma exists_pos_of_deg_pos {D : DivisorV2 R} (hD : D.Effective)
    (hdeg : 0 < D.deg) : ∃ v : HeightOneSpectrum R, 0 < D v := by
  by_contra h_all_zero
  push_neg at h_all_zero
  have h_zero_deg : D.deg = 0 := by
    unfold deg
    rw [Finsupp.sum, Finset.sum_eq_zero]
    intro x _
    specialize h_all_zero x
    have hDx : 0 ≤ D x := hD x
    omega
  omega

-- Candidate 4 [tag: effectivity_subtraction] [status: OK]
/-- If D is effective and D(v) > 0, then D - single v 1 is effective.
This ensures the induction hypothesis applies to the smaller divisor. -/
lemma effective_sub_single {D : DivisorV2 R} (hD : D.Effective)
    (v : HeightOneSpectrum R) (hv : 0 < D v) :
    (D - DivisorV2.single v 1).Effective := by
  intro w
  simp only [Finsupp.coe_sub, Finsupp.coe_zero, Pi.sub_apply, Pi.zero_apply, single]
  by_cases h : w = v
  · subst h
    simp only [Finsupp.single_eq_same]
    omega
  · simp only [Finsupp.single_eq_of_ne h, sub_zero]
    exact hD w

-- Candidate 5 [tag: degree_subtraction] [status: OK]
/-- Degree subtraction: deg(D - single v 1) = deg D - 1. -/
lemma deg_sub_single (D : DivisorV2 R) (v : HeightOneSpectrum R) :
    (D - DivisorV2.single v 1).deg = D.deg - 1 := by
  rw [sub_eq_add_neg, deg_add, deg_neg, deg_single]
  ring

-- Candidate 6 [tag: single_reconstruction] [status: OK]
/-- Reconstruction: (D - single v 1) + single v 1 = D. -/
lemma sub_add_single_cancel (D : DivisorV2 R) (v : HeightOneSpectrum R) :
    (D - DivisorV2.single v 1) + DivisorV2.single v 1 = D := by
  simp only [sub_add_cancel]

end DivisorV2

-- Candidate 4 [tag: typeclass_application] [status: OK] [cycle: 23]
/-- Application of LocalGapBound: ℓ(D + v) ≤ ℓ(D) + 1.

Updated in Cycle 23 to use LocalGapBound instead of SinglePointBound.
This makes the helper lemma usable in affine contexts. -/
lemma ellV2_real_add_single_le_succ [LocalGapBound R K]
    (D : DivisorV2 R) (v : HeightOneSpectrum R) :
    ellV2_real R K (D + DivisorV2.single v 1) ≤ ellV2_real R K D + 1 :=
  LocalGapBound.gap_le_one D v

-- Candidate 8 [tag: riemann_inequality] [status: OK]
/-- Riemann inequality: ℓ(D) ≤ deg(D) + 1 for effective divisors.

PROOF STRATEGY (degree induction):
1. Induct on n = (deg D).toNat
2. Base case (n = 0): Effective D with deg 0 implies D = 0
   - Use SinglePointBound.ell_zero_eq_one to get ℓ(0) = 1 ≤ 0 + 1
3. Inductive step (n → n+1):
   - deg D = n+1 > 0, so exists v with D(v) > 0 (DivisorV2.exists_pos_of_deg_pos)
   - Let D' = D - single v 1, then D = D' + single v 1
   - D' is effective (DivisorV2.effective_sub_single) with deg D' = n
   - IH: ℓ(D') ≤ deg(D') + 1 = n + 1
   - Bound: ℓ(D) ≤ ℓ(D') + 1 (SinglePointBound.bound)
   - Combine: ℓ(D) ≤ n + 1 + 1 = deg(D) + 1 -/
lemma riemann_inequality_real [SinglePointBound R K] {D : DivisorV2 R} (hD : D.Effective) :
    (ellV2_real R K D : ℤ) ≤ D.deg + 1 := by
  -- Induction on n = (deg D).toNat
  have h_deg_nonneg : 0 ≤ D.deg := by
    unfold DivisorV2.deg
    apply Finsupp.sum_nonneg
    intro v _
    exact hD v
  generalize hn : D.deg.toNat = n
  induction n generalizing D with
  | zero =>
    -- If deg(D).toNat = 0 and D is effective, then D = 0
    have hdeg_zero : D.deg = 0 := by
      have : D.deg.toNat = 0 := hn
      have := Int.toNat_of_nonneg h_deg_nonneg
      omega
    have h_zero : D = 0 := by
      ext v
      by_contra h_neq
      have h_pos : 0 < D v := lt_of_le_of_ne (hD v) (Ne.symm h_neq)
      have h_in_supp : v ∈ D.support := Finsupp.mem_support_iff.mpr (ne_of_gt h_pos)
      have h_sum_pos : 0 < D.deg := by
        unfold DivisorV2.deg
        apply Finsupp.sum_pos'
        · intro x _; exact hD x
        · exact ⟨v, h_in_supp, h_pos⟩
      omega
    subst h_zero
    simp only [DivisorV2.deg_zero, zero_add]
    have h1 : ellV2_real R K 0 = 1 := SinglePointBound.ell_zero_eq_one
    omega
  | succ n ih =>
    -- deg(D).toNat = n + 1 > 0, so exists v with D(v) > 0
    have hdeg_pos : D.deg = n + 1 := by
      have h1 := Int.toNat_of_nonneg h_deg_nonneg
      omega
    have h_exists_pos : ∃ v, 0 < D v := DivisorV2.exists_pos_of_deg_pos (R := R) hD (by omega)
    obtain ⟨v, hv⟩ := h_exists_pos
    -- D' = D - single v 1
    let D' := D - DivisorV2.single v 1
    have h_decomp : D = D' + DivisorV2.single v 1 := by
      simp only [D', DivisorV2.sub_add_single_cancel]
    -- D' is effective
    have hD' : D'.Effective := DivisorV2.effective_sub_single (R := R) hD v hv
    -- deg(D') = n
    have hdeg' : D'.deg.toNat = n := by
      have h1 : D'.deg = D.deg - 1 := DivisorV2.deg_sub_single (R := R) D v
      have h2 : 0 ≤ D'.deg := by
        unfold DivisorV2.deg
        apply Finsupp.sum_nonneg
        intro w _; exact hD' w
      omega
    -- Apply IH to D'
    have h_le := ih hD' (by
      unfold DivisorV2.deg
      apply Finsupp.sum_nonneg
      intro w _; exact hD' w) hdeg'
    -- Apply single point bound (inherited from LocalGapBound via extends)
    rw [h_decomp]
    have h_step : ellV2_real R K (D' + DivisorV2.single v 1) ≤ ellV2_real R K D' + 1 :=
      LocalGapBound.gap_le_one D' v
    -- Combine
    have hdeg_D' : D'.deg = n := by
      have h1 : D'.deg = D.deg - 1 := DivisorV2.deg_sub_single (R := R) D v
      rw [h1, hdeg_pos]
      ring
    have hdeg_total : (D' + DivisorV2.single v 1).deg = D'.deg + 1 :=
      DivisorV2.deg_add_single' (R := R) D' v
    -- h_le : (ellV2_real R K D' : ℤ) ≤ D'.deg + 1
    -- h_step : ellV2_real R K (D' + DivisorV2.single v 1) ≤ ellV2_real R K D' + 1
    -- hdeg_D' : D'.deg = n
    -- hdeg_total : (D' + DivisorV2.single v 1).deg = n + 1 = D.deg
    -- Goal: (ellV2_real R K (D' + DivisorV2.single v 1) : ℤ) ≤ (D' + DivisorV2.single v 1).deg + 1
    calc (ellV2_real R K (D' + DivisorV2.single v 1) : ℤ)
        ≤ ellV2_real R K D' + 1 := by exact_mod_cast h_step
      _ ≤ (D'.deg + 1) + 1 := by linarith
      _ = D'.deg + 2 := by ring
      _ = n + 2 := by rw [hdeg_D']
      _ = (n + 1) + 1 := by ring
      _ = (D' + DivisorV2.single v 1).deg + 1 := by rw [hdeg_total, hdeg_D']

-- Candidate 5 [tag: riemann_inequality_affine] [status: OK] [cycle: 23]
/-- Riemann inequality for affine models: ℓ(D) ≤ deg(D) + basedim.

This version uses LocalGapBound + BaseDim instead of SinglePointBound.
It's PROVABLE for affine models without assuming ℓ(0) = 1.

PROOF STRATEGY (degree induction with explicit base):
1. Induct on n = (deg D).toNat
2. Base case (n = 0): Effective D with deg 0 implies D = 0
   - Use BaseDim.basedim to get ℓ(0) = basedim
   - Goal: basedim ≤ 0 + basedim ✓
3. Inductive step (n → n+1):
   - deg D = n+1 > 0, so exists v with D(v) > 0
   - Let D' = D - single v 1, then D = D' + single v 1
   - D' is effective with deg D' = n
   - IH: ℓ(D') ≤ deg(D') + basedim = n + basedim
   - Bound: ℓ(D) ≤ ℓ(D') + 1 (LocalGapBound.gap_le_one)
   - Combine: ℓ(D) ≤ (n + basedim) + 1 = deg(D) + basedim -/
lemma riemann_inequality_affine [LocalGapBound R K] [bd : BaseDim R K] {D : DivisorV2 R} (hD : D.Effective) :
    (ellV2_real R K D : ℤ) ≤ D.deg + bd.basedim := by
  -- Induction on n = (deg D).toNat
  have h_deg_nonneg : 0 ≤ D.deg := by
    unfold DivisorV2.deg
    apply Finsupp.sum_nonneg
    intro v _
    exact hD v
  generalize hn : D.deg.toNat = n
  induction n generalizing D with
  | zero =>
    -- If deg(D).toNat = 0 and D is effective, then D = 0
    have hdeg_zero : D.deg = 0 := by
      have : D.deg.toNat = 0 := hn
      have := Int.toNat_of_nonneg h_deg_nonneg
      omega
    have h_zero : D = 0 := by
      ext v
      by_contra h_neq
      have h_pos : 0 < D v := lt_of_le_of_ne (hD v) (Ne.symm h_neq)
      have h_in_supp : v ∈ D.support := Finsupp.mem_support_iff.mpr (ne_of_gt h_pos)
      have h_sum_pos : 0 < D.deg := by
        unfold DivisorV2.deg
        apply Finsupp.sum_pos'
        · intro x _; exact hD x
        · exact ⟨v, h_in_supp, h_pos⟩
      omega
    subst h_zero
    simp only [DivisorV2.deg_zero, zero_add]
    -- ℓ(0) = basedim, so ℓ(0) ≤ basedim
    rw [bd.ell_zero_eq]
  | succ n ih =>
    -- deg(D).toNat = n + 1 > 0, so exists v with D(v) > 0
    have hdeg_pos : D.deg = n + 1 := by
      have h1 := Int.toNat_of_nonneg h_deg_nonneg
      omega
    have h_exists_pos : ∃ v, 0 < D v := DivisorV2.exists_pos_of_deg_pos (R := R) hD (by omega)
    obtain ⟨v, hv⟩ := h_exists_pos
    -- D' = D - single v 1
    let D' := D - DivisorV2.single v 1
    have h_decomp : D = D' + DivisorV2.single v 1 := by
      simp only [D', DivisorV2.sub_add_single_cancel]
    -- D' is effective
    have hD' : D'.Effective := DivisorV2.effective_sub_single (R := R) hD v hv
    -- deg(D') = n
    have hdeg' : D'.deg.toNat = n := by
      have h1 : D'.deg = D.deg - 1 := DivisorV2.deg_sub_single (R := R) D v
      have h2 : 0 ≤ D'.deg := by
        unfold DivisorV2.deg
        apply Finsupp.sum_nonneg
        intro w _; exact hD' w
      omega
    -- Apply IH to D'
    have h_le := ih hD' (by
      unfold DivisorV2.deg
      apply Finsupp.sum_nonneg
      intro w _; exact hD' w) hdeg'
    -- Apply single point bound
    rw [h_decomp]
    have h_step : ellV2_real R K (D' + DivisorV2.single v 1) ≤ ellV2_real R K D' + 1 :=
      LocalGapBound.gap_le_one D' v
    -- Combine
    have hdeg_D' : D'.deg = n := by
      have h1 : D'.deg = D.deg - 1 := DivisorV2.deg_sub_single (R := R) D v
      rw [h1, hdeg_pos]
      ring
    have hdeg_total : (D' + DivisorV2.single v 1).deg = D'.deg + 1 :=
      DivisorV2.deg_add_single' (R := R) D' v
    -- h_le : (ellV2_real R K D' : ℤ) ≤ D'.deg + basedim
    -- h_step : ellV2_real R K (D' + DivisorV2.single v 1) ≤ ellV2_real R K D' + 1
    -- Goal: (ellV2_real R K (D' + DivisorV2.single v 1) : ℤ) ≤ (D' + DivisorV2.single v 1).deg + basedim
    calc (ellV2_real R K (D' + DivisorV2.single v 1) : ℤ)
        ≤ ellV2_real R K D' + 1 := by exact_mod_cast h_step
      _ ≤ (D'.deg + bd.basedim) + 1 := by linarith
      _ = D'.deg + (bd.basedim + 1) := by ring
      _ = n + (bd.basedim + 1) := by rw [hdeg_D']
      _ = (n + 1) + bd.basedim := by ring
      _ = (D' + DivisorV2.single v 1).deg + bd.basedim := by rw [hdeg_total, hdeg_D']

/-! ## Original placeholder (superseded by riemann_inequality_real) -/

/-- The Riemann inequality (stated): ℓ(D) ≤ deg(D) + 1 for effective D.
DEPRECATED: Use riemann_inequality_real with SinglePointBound typeclass instead. -/
lemma riemann_inequality {D : DivisorV2 R} (hD : D.Effective) :
    (ellV2 R K D : ℤ) ≤ D.deg + 1 := by
  sorry

/-! ## Cycle 22: Residue Field Infrastructure

These definitions support the evaluation map construction for proving SinglePointBound.

**ARCHITECTURAL DISCOVERY (Cycle 22)**:
The current model using `HeightOneSpectrum R` captures only FINITE places.
For a function field k(t)/k:
- Finite places = height-1 primes of k[t]
- Missing = place at infinity
- L(0) = {no poles at finite places} = k[t], NOT k!

This means `ell_zero_eq_one` is FALSE in the current setup:
- L(0) = R (integral elements), not k (constants)
- Module.length R R = ∞ for Dedekind domains
- So ellV2_real R K 0 = 0, not 1

**CONSEQUENCE**: Current model proves "affine Riemann inequality" only.
For complete curve RR, need to add compactification (infinite places).
-/

-- Candidate 1 [tag: residue_field] [status: OK] [cycle: 22]
/-- The residue field at a height-1 prime v of a Dedekind domain R.
This is the quotient of the localization at v by its maximal ideal.

Geometrically: κ(v) is the "value field" at point v. For a curve over k,
this is a finite extension of k (dimension 1 when k is algebraically closed).

Uses: `Ideal.ResidueField (v.asIdeal)` from mathlib. -/
noncomputable abbrev residueFieldAtPrime (v : HeightOneSpectrum R) : Type _ :=
  v.asIdeal.ResidueField

-- Candidate 2 [tag: residue_field] [status: OK] [cycle: 22]
/-- The residue field at a height-1 prime is a field.
Automatic from mathlib's `Ideal.ResidueField` infrastructure. -/
noncomputable instance residueFieldAtPrime.field (v : HeightOneSpectrum R) :
    Field (residueFieldAtPrime R v) :=
  inferInstance

-- Candidate 3 [tag: residue_field] [status: OK] [cycle: 22]
/-- The residue map from R to κ(v), sending r ↦ r mod v.
This is the composition R → Localization.AtPrime v.asIdeal → κ(v).

Key property: r ∈ ker(residue) ⟺ r ∈ v (membership in the prime ideal).
From mathlib: `Ideal.algebraMap_residueField_eq_zero`. -/
noncomputable def residueMapAtPrime (v : HeightOneSpectrum R) :
    R →+* residueFieldAtPrime R v :=
  algebraMap R (residueFieldAtPrime R v)

/-! ## Cycle 24 Phase 1: Linear Algebra Bridge

The "Linear Algebra Bridge" lemma establishes the bound ℓ(D+v) ≤ ℓ(D) + 1 CONDITIONALLY
on the existence of a linear map φ : L(D+v) → κ(v) with the right kernel.

**STRATEGY**:
1. D ≤ D + single v 1 always holds (pointwise: D(w) ≤ D(w) + δ_{v,w})
2. By RRModuleV2_mono_inclusion, we get L(D) ≤ L(D+v) as submodules of K
3. If φ : L(D+v) → κ(v) has ker φ = L(D), the induced map L(D+v)/L(D) ↪ κ(v) is injective
4. By exact sequence: length(L(D+v)) = length(L(D)) + length(L(D+v)/L(D))
5. Since L(D+v)/L(D) injects into κ(v) and κ(v) has length ≤ 1, we get the bound

**Phase 2** (next cycle): Construct the actual evaluation map φ using uniformizers.
-/

section LinearAlgebraBridge

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Helper: D ≤ D + single v 1 always holds
lemma divisor_le_add_single (D : DivisorV2 R) (v : HeightOneSpectrum R) :
    D ≤ D + DivisorV2.single v 1 := by
  intro w
  simp only [Finsupp.coe_add, Pi.add_apply, DivisorV2.single]
  by_cases h : w = v
  · subst h; simp only [Finsupp.single_eq_same]; omega
  · simp only [Finsupp.single_eq_of_ne h, add_zero]; exact le_refl _

-- Helper: v.asIdeal is maximal in a Dedekind domain
lemma HeightOneSpectrum.isMaximal (v : HeightOneSpectrum R) : v.asIdeal.IsMaximal :=
  v.isPrime.isMaximal v.ne_bot

-- Candidate 1 [tag: residue_field_equiv] [status: PROVED] [cycle: 24.2]
/-- Linear equivalence between R ⧸ v.asIdeal and κ(v).

Since v.asIdeal is maximal (via HeightOneSpectrum.isMaximal), R ⧸ v.asIdeal is a field.
The algebraMap `R ⧸ v.asIdeal → κ(v)` is bijective for maximal ideals
(via `Ideal.bijective_algebraMap_quotient_residueField`).

This bijective R-algebra homomorphism gives an R-linear isomorphism. -/
noncomputable def residueFieldAtPrime.linearEquiv (v : HeightOneSpectrum R) :
    (R ⧸ v.asIdeal) ≃ₗ[R] residueFieldAtPrime R v := by
  -- The algebraMap is bijective when v.asIdeal is maximal
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hbij := Ideal.bijective_algebraMap_quotient_residueField v.asIdeal
  -- Construct the linear equivalence from the bijective algebra map
  exact LinearEquiv.ofBijective
    { toFun := algebraMap (R ⧸ v.asIdeal) (residueFieldAtPrime R v)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        -- r • x in R ⧸ v.asIdeal means (algebraMap R (R ⧸ v.asIdeal) r) * x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        -- Need: algebraMap (R ⧸ v.asIdeal) κ(v) (algebraMap R (R ⧸ v.asIdeal) r)
        --     = algebraMap R κ(v) r
        rw [IsScalarTower.algebraMap_apply R (R ⧸ v.asIdeal) (residueFieldAtPrime R v) r] }
    hbij

-- Helper: The residue field is a simple R-module (length = 1)
-- This follows because v.asIdeal is maximal, so R/v.asIdeal is simple,
-- and κ(v) ≅ R/v.asIdeal as R-modules for Dedekind domains.
instance residueFieldAtPrime.isSimpleModule (v : HeightOneSpectrum R) :
    IsSimpleModule R (residueFieldAtPrime R v) := by
  -- R ⧸ v.asIdeal is simple as R-module since v.asIdeal is maximal (= coatom in ideal lattice)
  -- And κ(v) ≃ R ⧸ v.asIdeal as R-modules
  rw [isSimpleModule_iff_quot_maximal]
  refine ⟨v.asIdeal, v.isMaximal, ?_⟩
  -- Use the linear equivalence
  exact ⟨(residueFieldAtPrime.linearEquiv v).symm⟩

-- Helper: Module.length of residue field is 1
lemma residueFieldAtPrime.length_eq_one (v : HeightOneSpectrum R) :
    Module.length R (residueFieldAtPrime R v) = 1 :=
  Module.length_eq_one R (residueFieldAtPrime R v)

/-- The Linear Algebra Bridge:
    IF there exists a linear map φ : L(D+v) → κ(v) with ker φ = L(D) (as submodules of L(D+v)),
    THEN ℓ(D+v) ≤ ℓ(D) + 1.

This lemma establishes the dimension bound CONDITIONALLY on the existence of the evaluation map.
The actual construction of φ (Phase 2) will use uniformizers and the DVR structure.

PROOF OUTLINE:
1. By exact sequence additivity: length(L(D+v)) = length(ker φ) + length(range φ)
2. The kernel condition ensures ker φ = L(D), so length(ker φ) = length(L(D))
3. range φ ⊆ κ(v) and κ(v) is simple, so length(range φ) ≤ 1
4. Therefore: length(L(D+v)) ≤ length(L(D)) + 1 -/
lemma local_gap_bound_of_exists_map
    (D : DivisorV2 R) (v : HeightOneSpectrum R)
    (φ : ↥(RRModuleV2_real R K (D + DivisorV2.single v 1)) →ₗ[R] residueFieldAtPrime R v)
    (h_ker : LinearMap.ker φ = LinearMap.range (Submodule.inclusion
      (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v)))) :
    ellV2_real_extended R K (D + DivisorV2.single v 1) ≤ ellV2_real_extended R K D + 1 := by
  -- Define the inclusion map
  let ι := Submodule.inclusion (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v))

  -- The inclusion ι is injective
  have hι_inj : Function.Injective ι := Submodule.inclusion_injective _

  -- Apply Module.length_eq_add_of_exact with rangeRestrict:
  -- length(LDv) = length(LD) + length(range φ)
  have h_add := Module.length_eq_add_of_exact ι (LinearMap.rangeRestrict φ) hι_inj
    (LinearMap.surjective_rangeRestrict φ) (by
      -- Need: Function.Exact ι (LinearMap.rangeRestrict φ)
      rw [LinearMap.exact_iff]
      ext x
      simp only [LinearMap.mem_ker, LinearMap.mem_range]
      constructor
      · intro hx
        -- x ∈ ker(rangeRestrict φ) means (φ x : κ(v)) = 0
        have hx' : φ x = 0 := Subtype.ext_iff.mp hx
        -- So x ∈ ker φ = range ι
        have hmem : x ∈ LinearMap.ker φ := hx'
        rw [h_ker] at hmem
        exact hmem
      · intro ⟨y, hy⟩
        -- x = ι y means x ∈ range ι = ker φ
        have hmem : x ∈ LinearMap.range ι := ⟨y, hy⟩
        rw [← h_ker] at hmem
        simp only [LinearMap.mem_ker] at hmem
        exact Subtype.ext hmem)

  -- Simplify: length(LDv) = length(LD) + length(range φ)
  unfold ellV2_real_extended
  rw [h_add]

  -- range φ is a submodule of κ(v), which has length 1
  -- So length(range φ) ≤ 1
  have h_range_le : Module.length R (LinearMap.range φ) ≤ 1 := by
    calc Module.length R (LinearMap.range φ)
        ≤ Module.length R (residueFieldAtPrime R v) :=
          Module.length_le_of_injective (LinearMap.range φ).subtype
            (Submodule.subtype_injective _)
      _ = 1 := residueFieldAtPrime.length_eq_one v

  -- Final calculation: length(LD) + length(range φ) ≤ length(LD) + 1
  -- h_range_le : Module.length R (LinearMap.range φ) ≤ 1
  -- Goal: Module.length R (RRModuleV2_real R K D) + Module.length R (LinearMap.range φ) ≤ ...
  have h_bound : Module.length R ↥(RRModuleV2_real R K D) + Module.length R ↥(LinearMap.range φ)
      ≤ Module.length R ↥(RRModuleV2_real R K D) + 1 := by
    gcongr
  exact h_bound

end LinearAlgebraBridge

/-! ## Cycle 24 Phase 2: Uniformizer Infrastructure

The uniformizer π at a height-1 prime v is a generator of v (up to units).
It satisfies v.intValuation π = exp(-1), meaning ord_v(π) = 1.

This infrastructure is essential for the "shifted evaluation" strategy:
- For f ∈ L(D+v), multiply by π^{D(v)+1} to shift poles
- The shifted element has valuation ≤ 1 at v
- Map to κ(v) via the residue structure
-/

section UniformizerInfrastructure

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: bundle_divisor_bridge] [status: PROVED] [cycle: 24.2]
/-- Choose a uniformizer at v: an element π ∈ R with v.intValuation π = exp(-1).

This exists by `IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer`.
Geometric meaning: π generates the maximal ideal v (up to units). -/
noncomputable def uniformizerAt (v : HeightOneSpectrum R) : R :=
  Classical.choose v.intValuation_exists_uniformizer

-- Candidate 2 [tag: bundle_divisor_bridge] [status: PROVED] [cycle: 24.2]
/-- The chosen uniformizer satisfies v.intValuation π = exp(-1). -/
lemma uniformizerAt_val (v : HeightOneSpectrum R) :
    v.intValuation (uniformizerAt v) = WithZero.exp (-1 : ℤ) :=
  Classical.choose_spec v.intValuation_exists_uniformizer

-- Candidate 3 [tag: bundle_divisor_bridge] [status: PROVED] [cycle: 24.2]
/-- The uniformizer is nonzero in R. -/
lemma uniformizerAt_ne_zero (v : HeightOneSpectrum R) : uniformizerAt v ≠ 0 := by
  intro h
  have hval := uniformizerAt_val v
  rw [h, map_zero] at hval
  -- 0 ≠ exp(-1), use that 0 is the absorbing element
  exact (WithZero.coe_ne_zero).symm hval

-- Candidate 4 [tag: bundle_divisor_bridge] [status: PROVED] [cycle: 24.2]
/-- The valuation of π^n is exp(-n) in the integral valuation. -/
lemma uniformizerAt_pow_val (v : HeightOneSpectrum R) (n : ℕ) :
    v.intValuation ((uniformizerAt v) ^ n) = WithZero.exp (-(n : ℤ)) := by
  induction n with
  | zero =>
    simp only [pow_zero, map_one, Nat.cast_zero, neg_zero, WithZero.exp_zero]
  | succ n ih =>
    rw [pow_succ, map_mul, ih, uniformizerAt_val]
    -- exp(-n) * exp(-1) = exp(-n + (-1)) = exp(-(n+1))
    rw [← WithZero.exp_add, Nat.cast_succ]
    ring_nf

-- Candidate 5 [tag: bundle_divisor_bridge] [status: PROVED] [cycle: 24.2]
/-- The valuation of the uniformizer in K (via algebraMap). -/
lemma uniformizerAt_valuation (v : HeightOneSpectrum R) :
    v.valuation K (algebraMap R K (uniformizerAt v)) = WithZero.exp (-1 : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact uniformizerAt_val v

-- Candidate 6 [tag: bundle_divisor_bridge] [status: PROVED] [cycle: 24.2]
/-- The valuation of π^n in K (via algebraMap). -/
lemma uniformizerAt_pow_valuation (v : HeightOneSpectrum R) (n : ℕ) :
    v.valuation K (algebraMap R K ((uniformizerAt v) ^ n)) = WithZero.exp (-(n : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact uniformizerAt_pow_val v n

-- Candidate 7 [tag: coercion_simplify] [status: SORRY] [cycle: 24.2]
/-- For f ∈ L(D+v), the shifted element f · π^{D(v)+1} has valuation ≤ 1 at v.

This is KEY: allows us to "evaluate f at v" by shifting the pole away.

PROOF OUTLINE:
- f ∈ L(D+v) means v(f) ≤ exp(D(v)+1)
- By uniformizer: v(π^{D(v)+1}) = exp(-(D(v)+1))
- Product: v(f·π^{D(v)+1}) ≤ exp(D(v)+1) · exp(-(D(v)+1)) = 1

TECHNICAL NOTE: The proof involves careful case analysis on whether D(v)+1 ≥ 0
and manipulation of WithZero.exp with integer arguments. -/
lemma shifted_element_valuation_le_one
    (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : K) (hf : f ∈ RRModuleV2_real R K (D + DivisorV2.single v 1)) :
    v.valuation K (f * algebraMap R K ((uniformizerAt v) ^ (D v + 1).toNat)) ≤ 1 := by
  -- Handle f = 0 case
  rcases hf with rfl | hf'
  · simp only [zero_mul, map_zero, zero_le']
  -- f ≠ 0 case: use membership condition and uniformizer properties
  have hfv := hf' v
  simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_eq_same] at hfv
  rw [Valuation.map_mul]
  -- Technical proof: v(f) * v(π^n) ≤ 1 using uniformizer valuation
  sorry -- Valuation arithmetic with WithZero.exp

end UniformizerInfrastructure

/-! ## Cycle 25: Evaluation Map and LocalGapBound Instance

With the uniformizer infrastructure, we can construct the evaluation map:
  evaluationMapAt v D : L(D+v) →ₗ[R] κ(v)

The key property is:
- ker(evaluationMapAt) = L(D) (embedded in L(D+v))

This allows us to apply `local_gap_bound_of_exists_map` to get the instance. -/

section EvaluationMapConstruction

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 25]
/-- The evaluation map φ : L(D+v) →ₗ[R] κ(v) defined by shifted evaluation.

CONSTRUCTION: For f ∈ L(D+v):
1. Compute g = f · π^{D(v)+1}
2. By shifted_element_valuation_le_one, v(g) ≤ 1
3. Map g to κ(v) via mem_integers → residue map

NOTE: This requires careful handling of the fraction field structure. -/
noncomputable def evaluationMapAt (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    RRModuleV2_real R K (D + DivisorV2.single v 1) →ₗ[R] residueFieldAtPrime R v := sorry

-- Candidate 2 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 25]
/-- The kernel of evaluationMapAt is exactly L(D).

ker(evaluationMapAt v D) = range(Submodule.inclusion : L(D) → L(D+v))

PROOF OUTLINE:
- L(D) ⊆ ker: If f ∈ L(D), then v(f·π^{D(v)+1}) ≤ exp(-1) < 1, so maps to 0
- ker ⊆ L(D): If f maps to 0, then f·π^{D(v)+1} ∈ v.asIdeal, so v(f) ≤ exp(D(v)) -/
lemma kernel_evaluationMapAt (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    LinearMap.ker (evaluationMapAt v D) = LinearMap.range (Submodule.inclusion
      (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v))) := sorry

-- Candidate 3 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 25]
/-- LocalGapBound instance for Dedekind domains.

This completes the proof that ℓ(D+v) ≤ ℓ(D) + 1 unconditionally.
Uses local_gap_bound_of_exists_map with evaluationMapAt and kernel_evaluationMapAt. -/
instance instLocalGapBound (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] : LocalGapBound R K where
  gap_le_one := fun D v => by
    -- Apply the bridge lemma
    have h := local_gap_bound_of_exists_map (R := R) (K := K) D v
      (evaluationMapAt v D)
      (kernel_evaluationMapAt v D)
    -- h : ellV2_real_extended R K (D + single v 1) ≤ ellV2_real_extended R K D + 1
    -- Convert from ℕ∞ to ℕ using toNat
    unfold ellV2_real
    -- Need to show: (ellV2_real_extended R K (D + single v 1)).toNat ≤ (ellV2_real_extended R K D).toNat + 1
    -- From h at ℕ∞ level, need ENat reasoning
    sorry -- Technical ℕ∞ → ℕ conversion via ENat.toNat_le_toNat

end EvaluationMapConstruction

/-! ## Cycle 26 Candidates: Evaluation Map Construction via Valuation Ring

The strategy is to use the valuation ring at v as an intermediate object:
1. Shifted element g = f · π^{D(v)+1} has v(g) ≤ 1
2. g belongs to valuation ring at v (not necessarily to R)
3. Valuation ring ≃ Localization.AtPrime v.asIdeal (DVR)
4. Use DVR residue structure to map to κ(v)
-/

section Cycle26Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: coercion_simplify] [status: OK]
/-- WithZero.exp arithmetic: exp(a) * exp(b) = exp(a+b).
This is the key identity needed for shifted_element_valuation_le_one. -/
lemma withzero_exp_mul (a b : ℤ) :
    WithZero.exp a * WithZero.exp b = WithZero.exp (a + b) :=
  (WithZero.exp_add a b).symm

-- Candidate 2 [tag: coercion_simplify] [status: OK]
/-- Exp of negation: exp(-a) is the inverse of exp(a). -/
lemma withzero_exp_neg (a : ℤ) :
    WithZero.exp (-a) = (WithZero.exp a)⁻¹ := by
  rw [WithZero.exp_neg]

-- Candidate 3 [tag: bundle_divisor_bridge] [status: OK]
/-- The valuation ring of v in K: {g ∈ K : v(g) ≤ 1}.
This is the natural domain for the residue map to κ(v). -/
noncomputable def valuationRingAt (v : HeightOneSpectrum R) : ValuationSubring K :=
  (v.valuation K).valuationSubring

-- Candidate 4 [tag: bundle_divisor_bridge] [status: PROVED]
/-- Elements with v-valuation ≤ 1 belong to the valuation ring at v. -/
lemma mem_valuationRingAt_iff (v : HeightOneSpectrum R) (g : K) :
    g ∈ valuationRingAt v ↔ v.valuation K g ≤ 1 :=
  Valuation.mem_valuationSubring_iff (v.valuation K) g

-- Candidate 5 [tag: bundle_divisor_bridge] [status: PROVED]
/-- R embeds into the valuation ring at any prime v.
Elements of R have v-valuation ≤ 1 for all v. -/
lemma algebraMap_mem_valuationRingAt (v : HeightOneSpectrum R) (r : R) :
    algebraMap R K r ∈ valuationRingAt v := by
  rw [mem_valuationRingAt_iff]
  exact v.valuation_le_one r

-- Candidate 6 [tag: rr_bundle_bridge] [status: PROVED]
/-- The valuation ring at v is a local ring with maximal ideal {g : v(g) < 1}. -/
instance valuationRingAt.isLocalRing (v : HeightOneSpectrum R) :
    IsLocalRing (valuationRingAt (R := R) (K := K) v) :=
  ValuationSubring.isLocalRing (valuationRingAt v)

-- Candidate 7 [tag: rr_bundle_bridge] [status: OK]
/-- The residue field of the valuation ring at v. -/
noncomputable abbrev valuationRingAt.residueField (v : HeightOneSpectrum R) :=
  IsLocalRing.ResidueField (valuationRingAt (R := R) (K := K) v)

-- Candidate 8 [tag: rr_bundle_bridge] [status: OK]
/-- The residue map from the valuation ring at v to its residue field. -/
noncomputable def valuationRingAt.residue (v : HeightOneSpectrum R) :
    valuationRingAt (R := R) (K := K) v →+* valuationRingAt.residueField (R := R) (K := K) v :=
  IsLocalRing.residue (valuationRingAt (R := R) (K := K) v)

end Cycle26Candidates

end RiemannRochV2
