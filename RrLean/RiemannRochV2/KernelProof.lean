import RrLean.RiemannRochV2.LocalGapInstance

/-!
# Kernel Proof for evaluationMapAt

This file contains the kernel characterization lemmas for evaluationMapAt,
extracted from LocalGapInstance.lean to reduce build times.

## Contents

- Cycle 66: kernel_evaluationMapAt candidates
- Cycle 67: Helper lemmas for kernel proof
- Cycle 68: Complete kernel proof chain

## Victory Path

```
extract_valuation_bound (PROVED in Cycle 68)
    |
LD_element_maps_to_zero (SORRY - needs sub-lemmas)
    |
kernel_evaluationMapAt_complete (SORRY)
    |
LocalGapBound instance -> VICTORY
```
-/

namespace RiemannRochV2

open IsDedekindDomain

/-! ## Cycle 66 Candidates: Proving kernel_evaluationMapAt

Goal: Prove ker(evaluationMapAt) = range(Submodule.inclusion : L(D) -> L(D+v))

Strategy:
- L(D) ⊆ ker: If f ∈ L(D), then v(f) ≤ exp(D(v)), so v(f·π^{D(v)+1}) ≤ exp(-1) < 1,
  meaning shifted element is in maximalIdeal, so residue is 0.
- ker ⊆ L(D): If f maps to 0, then shifted element is in maximalIdeal,
  so v(f·π^{D(v)+1}) < 1, hence v(f) ≤ exp(D(v)), meaning f ∈ L(D).

Key mathlib lemma: `IsLocalRing.residue_eq_zero_iff`: residue x = 0 ↔ x ∈ maximalIdeal
-/

section Cycle66Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 66]
/-- Helper for L(D) ⊆ ker direction: elements of L(D) have shifted valuation < 1.
If f ∈ L(D) ⊆ L(D+v), then v(f) ≤ exp(D(v)), so v(f·π^{D(v)+1}) ≤ exp(-1) < 1.
This means the shifted element lies in the maximal ideal, so residue is zero. -/
lemma LD_element_shifted_in_maximalIdeal (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : RRModuleV2_real R K D) :
    (⟨shiftedElement v D (Submodule.inclusion
      (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v)) f).val,
      shiftedElement_mem_valuationRingAt v D
        (Submodule.inclusion (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v)) f)⟩ :
      valuationRingAt (R := R) (K := K) v) ∈
    IsLocalRing.maximalIdeal (valuationRingAt (R := R) (K := K) v) := sorry

-- Candidate 2 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 66]
/-- The valuation bound for elements of L(D): if f ∈ L(D), then v(f·π^{D(v)+1}) < 1.
This uses that f ∈ L(D) means v(f) ≤ exp(D(v)), so
v(f·π^{D(v)+1}) = v(f) · exp(-(D(v)+1)) ≤ exp(D(v)) · exp(-(D(v)+1)) = exp(-1) < 1. -/
lemma LD_element_valuation_strict_bound (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : K) (hf : f ∈ RRModuleV2_real R K D) (hf_ne : f ≠ 0) :
    v.valuation K (f * algebraMap R K ((uniformizerAt v) ^ (D v + 1).toNat)) <
      WithZero.exp (0 : ℤ) := sorry

-- Candidate 3 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 66]
/-- L(D) ⊆ ker direction: elements of L(D) map to zero under evaluationMapAt.
Uses that shifted element is in maximal ideal, hence residue_eq_zero_iff. -/
lemma LD_inclusion_in_kernel (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    LinearMap.range (Submodule.inclusion
      (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v))) ≤
    LinearMap.ker (evaluationMapAt_complete v D) := sorry

-- Candidate 4 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 66]
/-- Helper for ker ⊆ L(D) direction: if evaluationFun maps f to 0, then shifted element
is in the maximal ideal of the valuation ring.
Uses that the bridge is an isomorphism and residue_eq_zero_iff. -/
lemma kernel_element_shifted_in_maximalIdeal (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : RRModuleV2_real R K (D + DivisorV2.single v 1))
    (hf : evaluationFun_via_bridge v D f = 0) :
    (⟨shiftedElement v D f.val, shiftedElement_mem_valuationRingAt v D f⟩ :
      valuationRingAt (R := R) (K := K) v) ∈
    IsLocalRing.maximalIdeal (valuationRingAt (R := R) (K := K) v) := sorry

-- Candidate 5 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 66]
/-- ker ⊆ L(D) direction: if f maps to 0, then v(f) ≤ exp(D(v)).
If evaluationFun f = 0, then f·π^{D(v)+1} ∈ maximalIdeal, so v(f·π^{D(v)+1}) < 1.
This means v(f) · exp(-(D(v)+1)) < 1, hence v(f) < exp(D(v)+1), so v(f) ≤ exp(D(v)). -/
lemma kernel_element_satisfies_LD_bound (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : K) (hf_mem : f ∈ RRModuleV2_real R K (D + DivisorV2.single v 1)) (hf_ne : f ≠ 0)
    (hf_zero : evaluationFun_via_bridge v D ⟨f, hf_mem⟩ = 0) :
    v.valuation K f ≤ WithZero.exp (D v) := sorry

-- Candidate 6 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 66]
/-- ker ⊆ L(D) direction: kernel elements belong to L(D).
If f ∈ ker(evaluationMapAt), then f satisfies the L(D) valuation condition. -/
lemma kernel_element_in_LD (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : RRModuleV2_real R K (D + DivisorV2.single v 1))
    (hf : evaluationFun_via_bridge v D f = 0) :
    f.val ∈ RRModuleV2_real R K D := sorry

-- Candidate 7 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 66]
/-- ker ⊆ L(D) direction: the kernel is contained in the range of the inclusion.
This is the set-theoretic containment needed for the equality. -/
lemma kernel_subset_LD_range (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    LinearMap.ker (evaluationMapAt_complete v D) ≤
    LinearMap.range (Submodule.inclusion
      (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v))) := sorry

-- Candidate 8 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 66]
/-- Main lemma: kernel equals range of inclusion from L(D).
Combines both directions to establish the kernel characterization.
Uses evaluationMapAt_complete as the definition of evaluationMapAt. -/
lemma kernel_evaluationMapAt_complete (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    LinearMap.ker (evaluationMapAt_complete v D) = LinearMap.range (Submodule.inclusion
      (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v))) := sorry

end Cycle66Candidates

/-! ### Cycle 67 Candidates: Helper lemmas for kernel proof

Goal: Prove helpers for kernel_evaluationMapAt_complete

Key achievements:
- exp_neg_one_lt_one: PROVED (trivial via exp_lt_exp)
- exp_mul_exp_neg: PROVED (exp_add + add_neg_cancel)
- valuation_product_strict_bound_nonneg: PROVED (forward direction arithmetic)
- valuation_lt_one_of_neg: PROVED (negative case arithmetic)
- RingEquiv.apply_eq_zero_iff': PROVED (trivial via map_eq_zero_iff)

Remaining sorries:
- extract_valuation_bound_from_maxIdeal_nonneg: Key inversion lemma (needs WithZero.log)
- extract_valuation_bound_from_maxIdeal_neg: Negative case inversion
- valuation_bound_at_other_prime: Multi-prime condition
-/

section Cycle67Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 67]
/-- Helper: exp(-1) < exp(0) = 1 for WithZero valuations.
This is the key strict inequality needed for LD_element_valuation_strict_bound.
Uses WithZero.exp_lt_exp to reduce to -1 < 0. -/
lemma exp_neg_one_lt_one :
    WithZero.exp (-1 : ℤ) < WithZero.exp (0 : ℤ) :=
  WithZero.exp_lt_exp.mpr (by omega)

-- Candidate 2 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 67]
/-- Helper: exp(a) * exp(-a) = 1 for any integer a.
Needed for cancellation in valuation arithmetic.
This is exp_add with b = -a: exp(a + (-a)) = exp(0) = 1. -/
lemma exp_mul_exp_neg (a : ℤ) :
    WithZero.exp a * WithZero.exp (-a) = 1 := by
  rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

-- Candidate 3 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 67]
/-- If v(f) ≤ exp(D(v)) and n = D(v)+1, then v(f·π^n) ≤ exp(-1).
Key calculation for the forward direction showing strict inequality.
Uses that v(f) ≤ exp(D(v)) and v(π^{D(v)+1}) = exp(-(D(v)+1)). -/
lemma valuation_product_strict_bound_nonneg
    (v : HeightOneSpectrum R) (D : DivisorV2 R) (f : K)
    (hn : 0 ≤ D v + 1)
    (hfv : v.valuation K f ≤ WithZero.exp (D v)) :
    v.valuation K (f * algebraMap R K ((uniformizerAt v) ^ (D v + 1).toNat)) ≤
      WithZero.exp (-1 : ℤ) := by
  rw [Valuation.map_mul]
  rw [uniformizerAt_pow_valuation_of_nonneg v (D v + 1) hn]
  calc v.valuation K f * WithZero.exp (-(D v + 1))
      ≤ WithZero.exp (D v) * WithZero.exp (-(D v + 1)) := mul_le_mul_right' hfv _
    _ = WithZero.exp (D v + (-(D v + 1))) := by rw [← WithZero.exp_add]
    _ = WithZero.exp (-1) := by ring_nf

-- Candidate 4 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 67]
/-- When D(v)+1 < 0, v(f) ≤ exp(D(v)) implies v(f) < 1.
Key for showing the strict bound in the negative exponent case. -/
lemma valuation_lt_one_of_neg
    (v : HeightOneSpectrum R) (D : DivisorV2 R) (f : K)
    (hn : D v + 1 < 0)
    (hfv : v.valuation K f ≤ WithZero.exp (D v)) :
    v.valuation K f < WithZero.exp (0 : ℤ) := by
  calc v.valuation K f
      ≤ WithZero.exp (D v) := hfv
    _ < WithZero.exp 0 := WithZero.exp_lt_exp.mpr (by omega : D v < 0)

-- Candidate 5 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 67]
/-- If shifted element is in maxIdeal and D(v)+1 ≥ 0, extract the v(f) bound.
Inverts the valuation multiplication to get v(f) from v(f·π^n) < 1.
Key: v(f) · exp(-(D(v)+1)) < 1, so v(f) < exp(D(v)+1).
In WithZero ℤᵐ, strict inequality with exp means we can get ≤ for the previous value. -/
lemma extract_valuation_bound_from_maxIdeal_nonneg
    (v : HeightOneSpectrum R) (D : DivisorV2 R) (f : K) (hf_ne : f ≠ 0)
    (hn : 0 ≤ D v + 1)
    (h_maxIdeal : v.valuation K (f * algebraMap R K ((uniformizerAt v) ^ (D v + 1).toNat)) < 1) :
    v.valuation K f ≤ WithZero.exp (D v) := by
  -- This is the key inversion lemma. Proof strategy:
  -- v(f·π^n) < 1 where n = D(v)+1 ≥ 0
  -- v(f) · exp(-n) < 1
  -- v(f) < exp(n) = exp(D(v)+1)
  -- Since valuation is discrete (values in ℤᵐ₀), v(f) < exp(D(v)+1) ⟹ v(f) ≤ exp(D(v))
  sorry

-- Candidate 6 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 67]
/-- If shifted element is in maxIdeal and D(v)+1 < 0, extract the v(f) bound.
When (D(v)+1).toNat = 0, we have v(f·1) = v(f) < 1.
Need to show v(f) < 1 implies v(f) ≤ exp(D(v)) when D(v) < -1. -/
lemma extract_valuation_bound_from_maxIdeal_neg
    (v : HeightOneSpectrum R) (D : DivisorV2 R) (f : K) (hf_ne : f ≠ 0)
    (hn : D v + 1 < 0)
    (h_maxIdeal : v.valuation K (f * algebraMap R K ((uniformizerAt v) ^ (D v + 1).toNat)) < 1) :
    v.valuation K f ≤ WithZero.exp (D v) := sorry

-- Candidate 7 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 67]
/-- RingEquiv preserves zero: if f(x) = 0 for a RingEquiv f, then x = 0.
Specialization of RingEquiv.map_eq_zero_iff for use with residueFieldBridge_explicit.
This is the key to working backward through the bridge in Candidate 4 of Cycle 66. -/
lemma RingEquiv_apply_eq_zero_iff' {A B : Type*} [Ring A] [Ring B]
    (f : A ≃+* B) (x : A) :
    f x = 0 ↔ x = 0 := map_eq_zero_iff f f.injective

-- Candidate 8 [tag: rr_bundle_bridge] [status: SORRY] [cycle: 67]
/-- For v' ≠ v, if f ∈ L(D+v) then f ∈ L(D) at v' (by monotonicity).
This is needed for kernel_element_in_LD to show the valuation condition holds at all primes.
Uses that D ≤ D + single v 1, and v' ≠ v means (D + single v 1)(v') = D(v'). -/
lemma valuation_bound_at_other_prime
    (v v' : HeightOneSpectrum R) (D : DivisorV2 R) (f : K)
    (hf : f ∈ RRModuleV2_real R K (D + DivisorV2.single v 1))
    (hne : v' ≠ v) :
    f = 0 ∨ v'.valuation K f ≤ WithZero.exp (D v') := sorry

end Cycle67Candidates

/-! ### Cycle 68 Candidates: Complete kernel proof chain

Goal: Prove remaining 3 Cycle 67 sorries and complete Cycle 66 kernel candidates

Key discoveries:
- WithZero.lt_mul_exp_iff_le: x < y * exp 1 ↔ x ≤ y (line 585, Canonical.lean)
- Int.lt_add_one_iff: a < b + 1 ↔ a ≤ b
- Finsupp.single_eq_of_ne: single a b c = 0 when c ≠ a

Proof chain:
- Candidate 1: Discrete step-down (core WithZero lemma)
- Candidates 2-4: Prove remaining Cycle 67 sorries
- Candidates 5-8: Complete Cycle 66 kernel characterization -> LocalGapBound
-/

section Cycle68Candidates

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- Candidate 1 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 68]
/-- In WithZero ℤᵐ⁰, if x < exp(n+1) and x ≠ 0, then x ≤ exp(n).
Key discrete valuation property: strict inequality with exp allows stepping down.
This is the bridge between v(f·π^n) < 1 and v(f) ≤ exp(D v). -/
lemma withzero_lt_exp_succ_imp_le_exp
    (x : WithZero (Multiplicative ℤ)) (n : ℤ) (_hx : x ≠ 0)
    (h : x < WithZero.exp (n + 1)) :
    x ≤ WithZero.exp n := by
  -- exp(n + 1) = exp(n) * exp(1) by exp_add
  rw [WithZero.exp_add] at h
  -- By lt_mul_exp_iff_le: x < exp(n) * exp(1) ↔ x ≤ exp(n)
  exact (WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero).mp h

-- Candidate 2 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 68]
/-- Prove extract_valuation_bound_from_maxIdeal_nonneg using discrete step-down.
From v(f·π^n) < 1 where n = D(v)+1 ≥ 0, extract v(f) ≤ exp(D v).
Strategy: v(f) · exp(-n) < exp(0) gives v(f) < exp(n), then step down. -/
lemma extract_valuation_bound_from_maxIdeal_nonneg_proof
    (v : HeightOneSpectrum R) (D : DivisorV2 R) (f : K) (hf_ne : f ≠ 0)
    (hn : 0 ≤ D v + 1)
    (h_maxIdeal : v.valuation K (f * algebraMap R K ((uniformizerAt v) ^ (D v + 1).toNat)) < 1) :
    v.valuation K f ≤ WithZero.exp (D v) := by
  -- v(f·π^n) < 1 where n = (D v + 1).toNat
  -- Since hn : 0 ≤ D v + 1, we have (D v + 1).toNat = D v + 1
  have hn_nat : ((D v + 1).toNat : ℤ) = D v + 1 := Int.toNat_of_nonneg hn
  -- v(f) · v(π^n) < 1
  rw [Valuation.map_mul] at h_maxIdeal
  rw [uniformizerAt_pow_valuation_of_nonneg v (D v + 1) hn] at h_maxIdeal
  -- v(f) · exp(-(D v + 1)) < exp(0) means v(f) < exp(D v + 1)
  have hval_ne : v.valuation K f ≠ 0 := (Valuation.ne_zero_iff (v.valuation K)).mpr hf_ne
  -- Use exp_mul_exp_neg: exp(a) * exp(-a) = 1
  have hexp_inv : WithZero.exp (D v + 1) * WithZero.exp (-(D v + 1)) = 1 := by
    rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  -- From v(f) * exp(-(D v+1)) < 1, multiply both sides by exp(D v+1) on left
  have h1 : v.valuation K f < WithZero.exp (D v + 1) := by
    have h2 : v.valuation K f * WithZero.exp (-(D v + 1)) < WithZero.exp (0 : ℤ) := h_maxIdeal
    rw [WithZero.exp_zero] at h2
    -- v(f) < exp(D v + 1) follows from v(f) * exp(-n) < 1 and exp(n) * exp(-n) = 1
    calc v.valuation K f
        = v.valuation K f * 1 := (mul_one _).symm
      _ = v.valuation K f * (WithZero.exp (D v + 1) * WithZero.exp (-(D v + 1))) := by rw [hexp_inv]
      _ = (v.valuation K f * WithZero.exp (-(D v + 1))) * WithZero.exp (D v + 1) := by
          rw [mul_assoc, mul_comm (WithZero.exp (D v + 1))]
      _ < 1 * WithZero.exp (D v + 1) := by
          apply mul_lt_mul_of_pos_right h2 WithZero.exp_pos
      _ = WithZero.exp (D v + 1) := one_mul _
  -- Now use discrete step-down: v(f) < exp(D v + 1) ⟹ v(f) ≤ exp(D v)
  exact withzero_lt_exp_succ_imp_le_exp (v.valuation K f) (D v) hval_ne h1

-- Candidate 3 [tag: rr_bundle_bridge] [status: OBSOLETE] [cycle: 68/70]
/-- OBSOLETE (Cycle 70): This toNat-based lemma is REPLACED by extract_valuation_bound_zpow.

The old .toNat approach was broken for D(v)+1 < 0 because toNat clamped to 0.
The new zpow-based shiftedElement handles all cases uniformly.

See extract_valuation_bound_zpow for the correct, unified approach. -/
lemma extract_valuation_bound_from_maxIdeal_neg_proof
    (v : HeightOneSpectrum R) (D : DivisorV2 R) (f : K) (hf_ne : f ≠ 0)
    (hf_mem : f ∈ RRModuleV2_real R K (D + DivisorV2.single v 1))
    (hn : D v + 1 < 0)
    (h_maxIdeal : v.valuation K (f * algebraMap R K ((uniformizerAt v) ^ (D v + 1).toNat)) < 1) :
    v.valuation K f ≤ WithZero.exp (D v) := by
  -- OBSOLETE: This lemma with .toNat hypothesis is no longer needed.
  -- Use extract_valuation_bound_zpow with the zpow-based hypothesis instead.
  sorry

-- Candidate 3.5 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 70]
/-- UNIFIED zpow-based extraction: From v(f·π^(D v+1)) < 1, extract v(f) ≤ exp(D v).

CYCLE 70 KEY INSIGHT: Using zpow instead of toNat makes this work for ALL integers.
The proof is the same as extract_valuation_bound_from_maxIdeal_nonneg_proof but uses
uniformizerAt_zpow_valuation instead of uniformizerAt_pow_valuation_of_nonneg.

Strategy:
- v(f · π^(D v+1)) = v(f) · exp(-(D v+1)) by uniformizerAt_zpow_valuation
- If this is < 1 = exp(0), then v(f) · exp(-(D v+1)) < exp(0)
- Multiply both sides by exp(D v+1): v(f) < exp(D v+1)
- By discrete step-down: v(f) ≤ exp(D v) -/
lemma extract_valuation_bound_zpow
    (v : HeightOneSpectrum R) (D : DivisorV2 R) (f : K) (hf_ne : f ≠ 0)
    (h_maxIdeal : v.valuation K (f * (algebraMap R K (uniformizerAt v)) ^ (D v + 1)) < 1) :
    v.valuation K f ≤ WithZero.exp (D v) := by
  -- v(f · π^(D v+1)) < 1 using zpow
  rw [Valuation.map_mul, uniformizerAt_zpow_valuation] at h_maxIdeal
  -- v(f) · exp(-(D v + 1)) < exp(0)
  have hval_ne : v.valuation K f ≠ 0 := (Valuation.ne_zero_iff (v.valuation K)).mpr hf_ne
  -- exp(D v+1) * exp(-(D v+1)) = 1
  have hexp_inv : WithZero.exp (D v + 1) * WithZero.exp (-(D v + 1)) = 1 := by
    rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  -- From v(f) * exp(-(D v+1)) < 1, derive v(f) < exp(D v+1)
  have h1 : v.valuation K f < WithZero.exp (D v + 1) := by
    have h2 : v.valuation K f * WithZero.exp (-(D v + 1)) < WithZero.exp (0 : ℤ) := h_maxIdeal
    rw [WithZero.exp_zero] at h2
    calc v.valuation K f
        = v.valuation K f * 1 := (mul_one _).symm
      _ = v.valuation K f * (WithZero.exp (D v + 1) * WithZero.exp (-(D v + 1))) := by rw [hexp_inv]
      _ = (v.valuation K f * WithZero.exp (-(D v + 1))) * WithZero.exp (D v + 1) := by
          rw [mul_assoc, mul_comm (WithZero.exp (D v + 1))]
      _ < 1 * WithZero.exp (D v + 1) := by
          apply mul_lt_mul_of_pos_right h2 WithZero.exp_pos
      _ = WithZero.exp (D v + 1) := one_mul _
  -- Discrete step-down: v(f) < exp(D v + 1) ⟹ v(f) ≤ exp(D v)
  exact withzero_lt_exp_succ_imp_le_exp (v.valuation K f) (D v) hval_ne h1

-- Candidate 4 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 68]
/-- For v' ≠ v, (D + single v 1)(v') = D(v') by Finsupp.single_eq_of_ne.
Therefore f ∈ L(D+v) gives v'(f) ≤ exp((D + single v 1)(v')) = exp(D(v')).
This is exactly the condition for f ∈ L(D) at prime v'. -/
lemma valuation_bound_at_other_prime_proof
    (v v' : HeightOneSpectrum R) (D : DivisorV2 R) (f : K)
    (hf : f ∈ RRModuleV2_real R K (D + DivisorV2.single v 1))
    (hne : v' ≠ v) :
    f = 0 ∨ v'.valuation K f ≤ WithZero.exp (D v') := by
  classical
  -- (D + single v 1)(v') = D(v') + (single v 1)(v') = D(v') + 0 = D(v')
  have hcoeff : (D + DivisorV2.single v 1) v' = D v' := by
    simp only [Finsupp.add_apply]
    rw [Finsupp.single_apply, if_neg (Ne.symm hne), add_zero]
  -- From f ∈ L(D+v), get the valuation condition
  simp only [RRModuleV2_real, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, satisfiesValuationCondition] at hf
  cases hf with
  | inl hf_zero => exact Or.inl hf_zero
  | inr hf_bound =>
    right
    have hv'_bound := hf_bound v'
    rw [hcoeff] at hv'_bound
    exact hv'_bound

-- Candidate 5 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 68]
/-- If v(x) < 1 and x ∈ valuationRingAt, then x ∈ maximalIdeal.
Uses that valuationRingAt.maximalIdeal = {x | v(x) < 1}. -/
lemma valuation_lt_one_imp_mem_maxIdeal
    (v : HeightOneSpectrum R)
    (x : K) (hx_mem : x ∈ valuationRingAt (R := R) (K := K) v)
    (hx_lt : v.valuation K x < WithZero.exp (0 : ℤ)) :
    (⟨x, hx_mem⟩ : valuationRingAt (R := R) (K := K) v) ∈
      IsLocalRing.maximalIdeal (valuationRingAt (R := R) (K := K) v) := by
  -- valuationRingAt v = (v.valuation K).valuationSubring
  -- The maximal ideal of a valuation ring is {x | v(x) < 1}
  -- Convert to the valuationSubring type for the maximalIdeal lemma
  show (⟨x, hx_mem⟩ : (v.valuation K).valuationSubring) ∈
       IsLocalRing.maximalIdeal (v.valuation K).valuationSubring
  rw [Valuation.mem_maximalIdeal_iff]
  rw [WithZero.exp_zero] at hx_lt
  exact hx_lt

-- Candidate 6 [tag: rr_bundle_bridge] [status: PROVED] [cycle: 68 → 71]
/-- Complete LD ⊆ ker direction: if f ∈ L(D), then evaluationFun f = 0.
Uses that shifted element lands in maxIdeal, so residue is zero.

CYCLE 71: Completed using zpow-based arithmetic:
- f ∈ L(D) means v(f) ≤ exp(D v) (STRICT bound, not D v + 1)
- shiftedElement = f * π^(D v + 1)
- v(shiftedElement) = v(f) * exp(-(D v + 1)) ≤ exp(D v) * exp(-(D v + 1)) = exp(-1) < 1
- So shiftedElement ∈ maximalIdeal, and residue sends it to 0 -/
lemma LD_element_maps_to_zero
    (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : RRModuleV2_real R K D) :
    evaluationFun_via_bridge v D
      (Submodule.inclusion (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v)) f) = 0 := by
  -- Key observation: (Submodule.inclusion hle f).val = f.val
  -- So shiftedElement v D (inclusion f).val = shiftedElement v D f.val
  set f' := Submodule.inclusion (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v)) f with hf'_def
  have hf'_val : (f' : K) = (f : K) := rfl
  -- Get f's membership in L(D)
  have hf_mem : (f : K) ∈ RRModuleV2_real R K D := f.property
  -- RRModuleV2_real membership: f = 0 ∨ (∀ v', v'.valuation K f ≤ exp(D v'))
  rcases hf_mem with hf_zero | hf_bound
  · -- Case 1: f.val = 0
    -- The inclusion of f into L(D+v) has the same underlying value, which is 0
    -- shiftedElement = 0 * π^n = 0
    -- residue(⟨0, _⟩) = 0 by map_zero
    -- bridge(0) = 0 by map_zero
    have h1 : shiftedElement v D (f' : K) = 0 := by
      simp only [hf'_val, hf_zero, shiftedElement, zero_mul]
    simp only [evaluationFun_via_bridge]
    -- We need to show (residueFieldBridge_explicit v) ((valuationRingAt.residue v) ⟨0, _⟩) = 0
    -- Since h1 : shiftedElement v D (f' : K) = 0, the subtype is ⟨0, _⟩
    -- residue maps ⟨0, _⟩ to 0
    have h2 : (⟨shiftedElement v D (f' : K), shiftedElement_mem_valuationRingAt v D f'⟩ :
        valuationRingAt (R := R) (K := K) v) = ⟨0, Subring.zero_mem _⟩ := by
      apply Subtype.ext
      exact h1
    rw [h2]
    -- residue maps 0 to 0
    have h3 : valuationRingAt.residue (R := R) (K := K) v (⟨0, Subring.zero_mem _⟩) = 0 :=
      map_zero (valuationRingAt.residue (R := R) (K := K) v)
    rw [h3]
    -- bridge maps 0 to 0
    exact map_zero (residueFieldBridge_explicit (R := R) (K := K) v)
  · -- Case 2: f.val ≠ 0 and ∀ v', v'.valuation K f.val ≤ exp(D v')
    -- Get the bound at v specifically
    have hfv : v.valuation K (f : K) ≤ WithZero.exp (D v) := hf_bound v
    -- Compute v(shiftedElement) using zpow
    -- shiftedElement v D f.val = f.val * π^(D v + 1)
    -- v(shiftedElement) = v(f.val) * exp(-(D v + 1)) ≤ exp(D v) * exp(-(D v + 1)) = exp(-1)
    have h_val_bound : v.valuation K (shiftedElement v D (f : K)) ≤ WithZero.exp (-1 : ℤ) := by
      unfold shiftedElement
      rw [Valuation.map_mul, uniformizerAt_zpow_valuation]
      calc v.valuation K (f : K) * WithZero.exp (-(D v + 1))
          ≤ WithZero.exp (D v) * WithZero.exp (-(D v + 1)) := mul_le_mul_right' hfv _
        _ = WithZero.exp (D v + (-(D v + 1))) := by rw [← WithZero.exp_add]
        _ = WithZero.exp (-1) := by ring_nf
    -- exp(-1) < 1 = exp(0)
    have h_strict : v.valuation K (shiftedElement v D (f : K)) < 1 := by
      calc v.valuation K (shiftedElement v D (f : K))
          ≤ WithZero.exp (-1 : ℤ) := h_val_bound
        _ < WithZero.exp (0 : ℤ) := exp_neg_one_lt_one
        _ = 1 := WithZero.exp_zero
    -- Since f'.val = f.val, the shiftedElement for f' equals that for f
    have h_shifted_eq : shiftedElement v D (f' : K) = shiftedElement v D (f : K) := by
      rw [hf'_val]
    -- v(shiftedElement f') < 1 as well
    have h_strict' : v.valuation K (shiftedElement v D (f' : K)) < 1 := by
      rw [h_shifted_eq]; exact h_strict
    -- shiftedElement f' ∈ maximalIdeal since v(shiftedElement) < 1
    -- valuationRingAt v = (v.valuation K).valuationSubring by definition
    have h_mem_maxIdeal :
        (⟨shiftedElement v D (f' : K), shiftedElement_mem_valuationRingAt v D f'⟩ :
          valuationRingAt (R := R) (K := K) v) ∈
        IsLocalRing.maximalIdeal (valuationRingAt (R := R) (K := K) v) := by
      -- Unfold valuationRingAt to expose (v.valuation K).valuationSubring
      unfold valuationRingAt
      rw [Valuation.mem_maximalIdeal_iff]
      exact h_strict'
    -- residue sends maximalIdeal elements to 0
    -- valuationRingAt.residue is defined as IsLocalRing.residue (valuationRingAt v)
    have h_res_zero : valuationRingAt.residue (R := R) (K := K) v
        ⟨shiftedElement v D (f' : K), shiftedElement_mem_valuationRingAt v D f'⟩ = 0 := by
      -- Use erw to see through definitional equalities
      erw [IsLocalRing.residue_eq_zero_iff]
      exact h_mem_maxIdeal
    -- bridge preserves 0
    simp only [evaluationFun_via_bridge, h_res_zero, map_zero]

-- Candidate 7 [tag: rr_bundle_bridge] [status: PARTIAL] [cycle: 68 → 70]
/-- Complete ker ⊆ LD direction: if evaluationFun f = 0, then f ∈ L(D).
Combines extract_valuation_bound_zpow for v and valuation_bound_at_other_prime for v' ≠ v.

CYCLE 70 UPDATE: With zpow-based shiftedElement, this works for ALL integers D v + 1.
The hn hypothesis is no longer needed! The proof uses extract_valuation_bound_zpow
which handles all cases uniformly. -/
lemma kernel_element_satisfies_all_bounds
    (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : RRModuleV2_real R K (D + DivisorV2.single v 1))
    (hf : evaluationFun_via_bridge v D f = 0) :
    f.val ∈ RRModuleV2_real R K D := by
  -- Need to show: f.val = 0 ∨ ∀ v', v'.valuation K f.val ≤ exp(D v')
  -- Case analysis on f.val = 0
  by_cases hf_ne : f.val = 0
  · left; exact hf_ne
  · right
    intro v'
    by_cases hv'_eq : v' = v
    · -- At v' = v: use extract_valuation_bound_zpow
      rw [hv'_eq]
      -- Trace: evaluationFun f = 0 → residue(shifted) = 0 → shifted ∈ maxIdeal → v(shifted) < 1
      -- Then apply extract_valuation_bound_zpow
      -- Step 1: evaluationFun f = 0 means bridge(residue(shifted)) = 0
      -- Step 2: bridge is RingEquiv, hence injective, so residue(shifted) = 0
      have h_res_zero : valuationRingAt.residue (R := R) (K := K) v
          ⟨shiftedElement v D f.val, shiftedElement_mem_valuationRingAt v D f⟩ = 0 := by
        -- evaluationFun_via_bridge v D f = bridge(residue(shifted)) = 0
        -- Since bridge is a RingEquiv, it's injective, so residue(shifted) = 0
        simp only [evaluationFun_via_bridge] at hf
        -- hf : (residueFieldBridge_explicit v) (residue shifted) = 0
        -- Use that RingEquiv maps x to 0 iff x = 0
        have h_inj := (residueFieldBridge_explicit (R := R) (K := K) v).injective
        exact h_inj (hf.trans (map_zero _).symm)
      -- Step 3: residue(shifted) = 0 → shifted ∈ maximalIdeal
      have h_mem_maxIdeal :
          (⟨shiftedElement v D f.val, shiftedElement_mem_valuationRingAt v D f⟩ :
            valuationRingAt (R := R) (K := K) v) ∈
          IsLocalRing.maximalIdeal (valuationRingAt (R := R) (K := K) v) := by
        erw [← IsLocalRing.residue_eq_zero_iff]
        exact h_res_zero
      -- Step 4: shifted ∈ maximalIdeal → v(shifted) < 1
      have h_val_lt_one : v.valuation K (shiftedElement v D f.val) < 1 := by
        unfold valuationRingAt at h_mem_maxIdeal
        rw [Valuation.mem_maximalIdeal_iff] at h_mem_maxIdeal
        exact h_mem_maxIdeal
      -- Step 5: Apply extract_valuation_bound_zpow
      exact extract_valuation_bound_zpow v D f.val hf_ne h_val_lt_one
    · -- At v' ≠ v: use valuation_bound_at_other_prime_proof
      exact (valuation_bound_at_other_prime_proof v v' D f.val f.property hv'_eq).resolve_left hf_ne

-- Candidate 8 [tag: rr_bundle_bridge] [status: PARTIAL] [cycle: 68 → 70]
/-- Final assembly: kernel equals range of inclusion from L(D).
Combines both directions: LD ⊆ ker and ker ⊆ LD.

CYCLE 70 UPDATE: With zpow-based shiftedElement, the hn hypothesis is NO LONGER NEEDED.
The extract_valuation_bound_zpow lemma handles all integers uniformly, so the kernel
characterization works for ALL divisors D, not just those with D v + 1 ≥ 0.

This is a significant improvement over the toNat-based approach! -/
lemma kernel_evaluationMapAt_complete_proof
    (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    LinearMap.ker (evaluationMapAt_complete v D) =
    LinearMap.range (Submodule.inclusion
      (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v))) := by
  ext x
  constructor
  · -- ker ⊆ range: if x ∈ ker, show x ∈ range of inclusion
    intro hx
    rw [LinearMap.mem_ker] at hx
    -- hx : evaluationMapAt_complete v D x = 0
    -- evaluationMapAt_complete is defined with toFun = evaluationFun_via_bridge
    -- So hx means evaluationFun_via_bridge v D x = 0
    have hx' : evaluationFun_via_bridge v D x = 0 := hx
    -- By kernel_element_satisfies_all_bounds, x.val ∈ L(D)
    have h_mem_LD : x.val ∈ RRModuleV2_real R K D :=
      kernel_element_satisfies_all_bounds v D x hx'
    -- Construct element of L(D) with same underlying value
    let f : RRModuleV2_real R K D := ⟨x.val, h_mem_LD⟩
    -- Show x = inclusion(f)
    rw [LinearMap.mem_range]
    use f
    -- inclusion(f).val = f.val = x.val, so they're equal as subtypes
    apply Subtype.ext
    rfl
  · -- range ⊆ ker: if x = inclusion(f) for f ∈ L(D), show x ∈ ker
    intro hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨f, hf⟩ := hx
    rw [LinearMap.mem_ker, ← hf]
    -- evaluationMapAt_complete v D (inclusion f) = evaluationFun_via_bridge v D (inclusion f)
    -- By LD_element_maps_to_zero, this equals 0
    exact LD_element_maps_to_zero v D f

end Cycle68Candidates

end RiemannRochV2
