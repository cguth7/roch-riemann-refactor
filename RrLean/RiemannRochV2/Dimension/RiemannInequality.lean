import RrLean.RiemannRochV2.Core.Typeclasses
import RrLean.RiemannRochV2.Dimension.DimensionCounting

/-!
# Riemann Inequality

This module contains the main Riemann inequality theorems:

* `riemann_inequality_real` - Projective version: ℓ(D) ≤ deg(D) + 1
* `riemann_inequality_affine` - Affine version: ℓ(D) ≤ deg(D) + basedim

Both are proved by induction on degree, using the single-point bound.
-/

namespace RiemannRochV2

open IsDedekindDomain

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

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
    haveI : LocalGapBound R K := SinglePointBound.toLocalGapBound
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
lemma riemann_inequality_affine [bd : BaseDim R K] {D : DivisorV2 R} (hD : D.Effective) :
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
    -- Apply gap bound (now unconditional via DimensionCounting.lean)
    rw [h_decomp]
    haveI : LocalGapBound R K := localGapBound_of_dedekind R K
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

end RiemannRochV2
