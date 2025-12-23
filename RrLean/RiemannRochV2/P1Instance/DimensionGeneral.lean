import RrLean.RiemannRochV2.P1Instance.GapBoundGeneral
import RrLean.RiemannRochV2.SerreDuality.P1Specific.DimensionScratch

/-!
# Generalized Dimension Formula for P¹

This module removes the `IsLinearPlaceSupport` restriction from the dimension formula,
proving `ℓ(D) = degWeighted(D) + 1` for all effective divisors on P¹.

## Main Results

* `evaluationMapAt_surj` - Evaluation map is surjective for effective D
* `ell_ratfunc_projective_gap_eq` - Gap = deg(v) for effective D
* `ell_ratfunc_projective_eq_degWeighted_plus_one` - ℓ(D) = degWeighted(D) + 1

## Strategy

The key insight is that for effective divisors, the evaluation map
ψ : L(D+[v]) → κ(v) is surjective. This is because for any c ∈ κ(v),
the element q/p (where q represents c and p is the generator of v)
belongs to L(D+[v]).

This gives the tight gap bound: ℓ(D+[v]) - ℓ(D) = deg(v).

Then induction on degWeighted(D) completes the proof:
- Base: degWeighted(D) = 0 ⟹ D = 0 ⟹ ℓ(0) = 1
- Step: Pick v with D(v) > 0. Let D' = D - [v].
  ℓ(D) = ℓ(D') + deg(v) = (degWeighted(D') + 1) + deg(v) = degWeighted(D) + 1
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Polynomial RatFunc PlaceDegree
open scoped Classical

variable (k : Type*) [Field k] [Fintype k] [DecidableEq k]

/-! ## Surjectivity of Evaluation Map

For effective D, the evaluation map ψ : L(D+[v]) → κ(v) is surjective.

The strategy: For any c ∈ κ(v) represented by polynomial q with deg(q) < deg(v),
the element q/generator(v) ∈ L(D+[v]) maps to c.
-/

/-- The evaluation map is surjective for effective D.

This is the key lemma for proving the tight gap bound.
-/
theorem evaluationMapAt_surj (v : HeightOneSpectrum (Polynomial k))
    (D : DivisorV2 (Polynomial k)) (hD : D.Effective) :
    Function.Surjective (evaluationMapAt_complete (R := Polynomial k) (K := RatFunc k) v D) := by
  sorry

/-! ## Tight Gap Bound

For effective D, the gap ℓ(D+[v]) - ℓ(D) equals exactly deg(v). -/

/-- Gap bound is tight for effective D: ℓ(D+[v]) = ℓ(D) + deg(v).

The proof combines:
- Upper bound from ell_ratfunc_projective_gap_le_general: gap ≤ deg(v)
- Lower bound from surjectivity: quotient ≅ κ(v) has dim = deg(v)
-/
theorem ell_ratfunc_projective_gap_eq (D : DivisorV2 (Polynomial k))
    (hD : D.Effective)
    (v : HeightOneSpectrum (Polynomial k))
    [hfin : Module.Finite k (RRSpace_ratfunc_projective (D + DivisorV2.single v 1))] :
    ell_ratfunc_projective (D + DivisorV2.single v 1) =
    ell_ratfunc_projective D + degree k v := by
  -- Upper bound from gap bound
  have h_le := ell_ratfunc_projective_gap_le_general k D v
  -- For the lower bound, use surjectivity of evaluation map
  have h_surj := evaluationMapAt_surj k v D hD
  -- Surjectivity implies: L(D+[v])/L(D) ≅ κ(v), so dim = deg(v)
  sorry

/-! ## Finiteness for Arbitrary Effective Divisors -/

/-- Finiteness of L(D) for effective D (by induction on degWeighted). -/
instance RRSpace_ratfunc_projective_effective_finite (D : DivisorV2 (Polynomial k))
    (hD : D.Effective) :
    Module.Finite k (RRSpace_ratfunc_projective D) := by
  sorry

/-! ## Helper Lemmas for Induction -/

/-- For effective D, degWeighted(D) ≥ 0. -/
lemma degWeighted_nonneg_of_effective (D : DivisorV2 (Polynomial k)) (hD : D.Effective) :
    0 ≤ degWeighted k D := by
  unfold degWeighted
  apply Finsupp.sum_nonneg
  intro v _
  have hdv : 0 ≤ D v := hD v
  exact mul_nonneg hdv (Nat.cast_nonneg (degree k v))

/-- For effective D, degWeighted(D) = 0 implies D = 0. -/
lemma effective_degWeighted_zero_imp_zero (D : DivisorV2 (Polynomial k))
    (hD : D.Effective) (hdeg : degWeighted k D = 0) :
    D = 0 := by
  ext v
  have hdv : 0 ≤ D v := hD v
  by_contra hne
  push_neg at hne
  have hpos : 0 < D v := lt_of_le_of_ne hdv (Ne.symm hne)
  -- D(v) * deg(v) > 0 contributes positively
  have hcontrib : D v * (degree k v : ℤ) > 0 := by
    apply mul_pos hpos
    exact Nat.cast_pos.mpr (degree_pos k v)
  -- But total degWeighted = 0, contradiction
  have hdeg_pos : 0 < degWeighted k D := by
    unfold degWeighted
    have hv_mem : v ∈ D.support := Finsupp.mem_support_iff.mpr (ne_of_gt hpos)
    have hsum_nn : 0 ≤ (D.support.erase v).sum (fun w => D w * (degree k w : ℤ)) := by
      apply Finset.sum_nonneg
      intro w _
      exact mul_nonneg (hD w) (Nat.cast_nonneg _)
    calc D.sum (fun v n => n * (degree k v : ℤ))
        = D v * (degree k v : ℤ) +
            (D.support.erase v).sum (fun w => D w * (degree k w : ℤ)) := by
          simp only [Finsupp.sum]
          rw [← Finset.add_sum_erase _ _ hv_mem]
      _ ≥ D v * (degree k v : ℤ) + 0 := by linarith
      _ = D v * (degree k v : ℤ) := add_zero _
      _ > 0 := hcontrib
  omega

/-- There exists v with D(v) > 0 when degWeighted(D) > 0 for effective D. -/
lemma exists_pos_of_degWeighted_pos (D : DivisorV2 (Polynomial k))
    (hD : D.Effective) (hdeg : 0 < degWeighted k D) :
    ∃ v, 0 < D v := by
  by_contra h_all_zero
  push_neg at h_all_zero
  have hD_zero : D = 0 := by
    ext w
    have hw := hD w
    by_contra hne
    push_neg at hne
    exact absurd (lt_of_le_of_ne hw (Ne.symm hne)) (not_lt.mpr (h_all_zero w))
  rw [hD_zero] at hdeg
  unfold degWeighted at hdeg
  simp at hdeg

/-! ## Main Theorem: Dimension Formula -/

/-- For effective D on P¹, ℓ(D) = degWeighted(D) + 1.

This generalizes `ell_ratfunc_projective_eq_deg_plus_one` by removing the
`IsLinearPlaceSupport` hypothesis and using weighted degree.
-/
theorem ell_ratfunc_projective_eq_degWeighted_plus_one (D : DivisorV2 (Polynomial k))
    (hD : D.Effective) :
    ell_ratfunc_projective D = (degWeighted k D).toNat + 1 := by
  -- Get finiteness
  haveI hfin : Module.Finite k (RRSpace_ratfunc_projective D) :=
    RRSpace_ratfunc_projective_effective_finite k D hD

  -- Weighted degree is non-negative for effective D
  have hdeg_nn : 0 ≤ degWeighted k D := degWeighted_nonneg_of_effective k D hD

  -- Convert to natural number for induction
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hdeg_nn
  rw [hn, Int.toNat_natCast]

  -- Strong induction on n = degWeighted(D)
  induction n using Nat.strong_induction_on generalizing D with
  | _ n ih =>
    by_cases hn0 : n = 0
    · -- Base case: degWeighted(D) = 0 ⟹ D = 0 ⟹ ℓ(0) = 1
      subst hn0
      have hD_zero : D = 0 := effective_degWeighted_zero_imp_zero k D hD hn
      rw [hD_zero]
      simp only [zero_add]
      exact ell_ratfunc_projective_zero_eq_one k

    · -- Inductive case: degWeighted(D) = n > 0
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hdeg_pos : 0 < degWeighted k D := by rw [hn]; exact Nat.cast_pos.mpr hn_pos

      -- There exists v with D(v) > 0
      obtain ⟨v, hv_pos⟩ := exists_pos_of_degWeighted_pos k D hD hdeg_pos

      -- Let D' = D - [v]
      set D' := D - DivisorV2.single v 1 with hD'_def

      -- D' is effective
      have hD'_eff : D'.Effective := DivisorV2.effective_sub_single hD v hv_pos

      -- Get finiteness for D'
      haveI hfin_D' : Module.Finite k (RRSpace_ratfunc_projective D') :=
        RRSpace_ratfunc_projective_effective_finite k D' hD'_eff

      -- degWeighted(D') = n - deg(v)
      -- This follows from: degWeighted(D - [v]) = degWeighted(D) - deg(v)
      have hdegW_D' : degWeighted k D' = (n : ℤ) - (degree k v : ℤ) := by
        -- degWeighted is additive and degWeighted(single v 1) = deg(v)
        -- D' = D - single v 1, so degWeighted(D') = degWeighted(D) - deg(v) = n - deg(v)
        sorry

      -- deg(v) ≤ n (since D(v) ≥ 1 contributes at least deg(v) to degWeighted)
      have hdeg_v_le_n : (degree k v : ℤ) ≤ n := by
        have hv_mem : v ∈ D.support := Finsupp.mem_support_iff.mpr (ne_of_gt hv_pos)
        have hsum_nn : 0 ≤ (D.support.erase v).sum (fun w => D w * (degree k w : ℤ)) := by
          apply Finset.sum_nonneg
          intro w _
          exact mul_nonneg (hD w) (Nat.cast_nonneg _)
        calc (degree k v : ℤ)
            = 1 * (degree k v : ℤ) := (one_mul _).symm
          _ ≤ D v * (degree k v : ℤ) := by
              apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
              omega
          _ ≤ D v * (degree k v : ℤ) +
                (D.support.erase v).sum (fun w => D w * (degree k w : ℤ)) := by
              linarith
          _ = degWeighted k D := by
              unfold degWeighted
              simp only [Finsupp.sum]
              rw [← Finset.add_sum_erase _ _ hv_mem]
          _ = n := hn

      -- degWeighted(D') ≥ 0
      have hdegW_D'_nn : 0 ≤ degWeighted k D' := by
        rw [hdegW_D']
        omega

      -- degWeighted(D') as natural number
      have hdeg_v_pos : 0 < degree k v := degree_pos k v
      have hdegW_D'_nat : degWeighted k D' = ((n - degree k v : ℕ) : ℤ) := by
        rw [hdegW_D']
        have h : degree k v ≤ n := by omega
        omega

      -- IH hypothesis: n - deg(v) < n
      have ih_hyp : n - degree k v < n := Nat.sub_lt hn_pos hdeg_v_pos

      -- Apply IH to D'
      have ih_result : ell_ratfunc_projective D' = n - degree k v + 1 :=
        ih (n - degree k v) ih_hyp D' hD'_eff hfin_D' hdegW_D'_nn hdegW_D'_nat

      -- D = D' + [v]
      have hD_eq : D = D' + DivisorV2.single v 1 := by
        rw [hD'_def, sub_add_cancel]

      -- Get finiteness for D' + [v]
      haveI hfin_Dv : Module.Finite k (RRSpace_ratfunc_projective (D' + DivisorV2.single v 1)) :=
        RRSpace_ratfunc_projective_effective_finite k (D' + DivisorV2.single v 1) (by
          intro w
          simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_apply]
          by_cases hw : w = v
          · -- w = v case
            simp only [hw, ↓reduceIte]
            have hD'v := hD'_eff v
            -- D' v ≥ 0 and we add 1
            linarith
          · simp only [if_neg (Ne.symm hw), add_zero]
            exact hD'_eff w)

      -- Apply tight gap bound: ℓ(D' + [v]) = ℓ(D') + deg(v)
      have h_gap := ell_ratfunc_projective_gap_eq k D' hD'_eff v

      -- Conclude
      calc ell_ratfunc_projective D
          = ell_ratfunc_projective (D' + DivisorV2.single v 1) := by rw [← hD_eq]
        _ = ell_ratfunc_projective D' + degree k v := h_gap
        _ = (n - degree k v + 1) + degree k v := by rw [ih_result]
        _ = n + 1 := by omega

end RiemannRochV2
