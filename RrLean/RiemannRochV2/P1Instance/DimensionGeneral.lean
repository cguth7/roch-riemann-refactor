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
  intro c
  -- Step 1: Lift c ∈ κ(v) to a polynomial representative q
  -- κ(v) ≅ k[X]/v.asIdeal via residueFieldAtPrime.linearEquiv
  let c_quot := (residueFieldAtPrime.linearEquiv v).symm c
  obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective c_quot

  -- Step 2: Construct candidate preimage f = q' / generator(v)^{D(v)+1}
  -- Use q' = q %ₘ gen to ensure deg(q') < deg(gen), so noPoleAtInfinity holds
  let gen := generator k v
  let n := D v + 1  -- The exponent
  have hgen_monic : gen.Monic := generator_monic k v
  have hgen_ne : gen ≠ 0 := (generator_irreducible k v).ne_zero
  have hgen_ne_one : gen ≠ 1 := (generator_irreducible k v).ne_one

  -- q' = q %ₘ gen has deg(q') < deg(gen)
  let q' := q %ₘ gen

  -- Key: q and q' give the same element in the quotient κ(v) = k[X]/⟨gen⟩
  have hq'_quot : Ideal.Quotient.mk v.asIdeal q' = Ideal.Quotient.mk v.asIdeal q := by
    rw [Ideal.Quotient.eq]
    -- q' - q = -(q - q') = -gen * (q /ₘ gen) ∈ ⟨gen⟩
    -- From modByMonic_add_div: q %ₘ gen + gen * (q /ₘ gen) = q
    have hdiv : q' - q = -(gen * (q /ₘ gen)) := by
      have h := Polynomial.modByMonic_add_div q hgen_monic
      -- h : q %ₘ gen + gen * (q /ₘ gen) = q
      calc q' - q = q %ₘ gen - q := rfl
        _ = q %ₘ gen - (q %ₘ gen + gen * (q /ₘ gen)) := by rw [h]
        _ = -(gen * (q /ₘ gen)) := by ring
    rw [hdiv, asIdeal_eq_span_generator k v, Ideal.neg_mem_iff]
    -- Need to show gen * (q /ₘ gen) ∈ span{gen}
    -- Use Ideal.mul_mem_right: a * c ∈ I if c ∈ I
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self (generator k v))

  -- Handle case where q' = 0 (which means gen | q, so c = 0)
  by_cases hq'_zero : q' = 0
  · -- If q' = 0, then gen | q, so q ∈ ideal, so c = 0
    use ⟨0, by simp [satisfiesValuationCondition, RRModuleV2_real]⟩
    -- q' = 0 implies q ∈ ideal implies c_quot = 0
    have hc_quot_zero : c_quot = 0 := by
      rw [← hq, ← hq'_quot, hq'_zero, map_zero]
    have hc_zero : c = 0 := by
      rw [← (residueFieldAtPrime.linearEquiv v).apply_symm_apply c]
      simp only [c_quot, hc_quot_zero, map_zero]
    rw [hc_zero]
    exact (evaluationMapAt_complete v D).map_zero

  -- Case q' ≠ 0: construct f = q' / gen^n
  · let q'_K := algebraMap (Polynomial k) (RatFunc k) q'
    let gen_K := algebraMap (Polynomial k) (RatFunc k) gen
    have hgen_K_ne : gen_K ≠ 0 := RatFunc.algebraMap_ne_zero hgen_ne

    -- f = q'_K / gen_K^n
    let f : RatFunc k := q'_K / gen_K ^ n.toNat

    -- Step 3: Show f ∈ L(D+[v]) - the affine part (valuation conditions)
    -- At v: v(f) = v(q')/v(gen^n) = 1/exp(-n) = exp(n) = exp(D(v)+1) ≤ exp((D+[v])(v)) ✓
    -- At w ≠ v: w(f) = w(q')/w(gen^n) ≤ 1/1 = 1 ≤ exp(D(w)) for effective D ✓
    have hf_affine : f ∈ RRModuleV2_real (Polynomial k) (RatFunc k) (D + DivisorV2.single v 1) := by
      -- f ≠ 0 since q' ≠ 0
      right
      intro w
      -- Compute f = q'_K / gen_K^n
      have hgen_pow_ne : gen_K ^ n.toNat ≠ 0 := pow_ne_zero _ hgen_K_ne
      -- val(f) = val(q') / val(gen^n)
      rw [map_div₀]

      by_cases hw : w = v
      · -- Case w = v: substitute and prove
        rw [hw]
        -- v.val(gen) = exp(-1) by generator_intValuation_at_self
        have hgen_val : v.valuation (RatFunc k) gen_K = WithZero.exp (-1 : ℤ) := by
          rw [HeightOneSpectrum.valuation_of_algebraMap]
          exact generator_intValuation_at_self k v
        -- v.val(gen^n) = exp(-n.toNat) using exp_nsmul: exp(a)^n = exp(n•a)
        have hgen_pow_val : v.valuation (RatFunc k) (gen_K ^ n.toNat) =
            WithZero.exp (-(n.toNat : ℤ)) := by
          rw [map_pow, hgen_val, ← WithZero.exp_nsmul]
          simp only [smul_neg, nsmul_eq_mul, mul_one]
        -- v.val(q') ≤ 1 (q' is a polynomial)
        have hq'_val_le : v.valuation (RatFunc k) q'_K ≤ 1 := by
          rw [HeightOneSpectrum.valuation_of_algebraMap]
          exact v.intValuation_le_one q'
        -- Goal: v.val(q')/v.val(gen^n) ≤ exp((D + [v])(v)) = exp(D(v) + 1) = exp(n)
        have hDv_eq : (D + DivisorV2.single v 1) v = n := by
          simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_eq_same]
          ring
        rw [hDv_eq, hgen_pow_val]
        -- n ≥ 0 since D is effective (D v ≥ 0, so D v + 1 ≥ 1 > 0)
        have hDv_ge : 0 ≤ D v := hD v
        have hn_nn : 0 ≤ n := by show 0 ≤ D v + 1; omega
        -- exp(-n.toNat) = exp(-n) since n ≥ 0
        have hexp_neg : WithZero.exp (-(n.toNat : ℤ)) = WithZero.exp (-n) := by
          congr 1
          rw [Int.toNat_of_nonneg hn_nn]
        rw [hexp_neg]
        -- val(q')/exp(-n) ≤ exp(n) ↔ val(q') ≤ exp(n) * exp(-n) = exp(0) = 1
        have hexp_pos : 0 < WithZero.exp (-n) := WithZero.exp_pos
        rw [div_le_iff₀ hexp_pos]
        calc v.valuation (RatFunc k) q'_K
            ≤ 1 := hq'_val_le
          _ = WithZero.exp (0 : ℤ) := WithZero.exp_zero.symm
          _ = WithZero.exp (n + -n) := by ring_nf
          _ = WithZero.exp n * WithZero.exp (-n) := WithZero.exp_add n (-n)

      · -- Case w ≠ v
        -- w.val(gen) = 1 at other primes
        have hgen_val_w : w.valuation (RatFunc k) gen_K = 1 := by
          rw [HeightOneSpectrum.valuation_of_algebraMap]
          exact generator_intValuation_at_other_prime k v w hw
        -- w.val(gen^n) = 1
        have hgen_pow_val_w : w.valuation (RatFunc k) (gen_K ^ n.toNat) = 1 := by
          rw [map_pow, hgen_val_w, one_pow]
        -- w.val(q') ≤ 1
        have hq'_val_le_w : w.valuation (RatFunc k) q'_K ≤ 1 := by
          rw [HeightOneSpectrum.valuation_of_algebraMap]
          exact w.intValuation_le_one q'
        -- Goal: w.val(q')/1 ≤ exp((D+[v])(w))
        have hDw_eq : (D + DivisorV2.single v 1) w = D w := by
          simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_apply]
          rw [if_neg (Ne.symm hw)]
          ring
        rw [hDw_eq, hgen_pow_val_w, div_one]
        -- D w ≥ 0 since D is effective, so exp(D w) ≥ 1
        have hDw_nn : 0 ≤ D w := hD w
        calc w.valuation (RatFunc k) q'_K
            ≤ 1 := hq'_val_le_w
          _ = WithZero.exp (0 : ℤ) := WithZero.exp_zero.symm
          _ ≤ WithZero.exp (D w) := WithZero.exp_le_exp.mpr hDw_nn

    -- Step 4: Show f satisfies no pole at infinity (projective condition)
    -- Key: deg(q') < deg(gen) ≤ deg(gen^n) for n ≥ 1, so intDegree(f) ≤ 0
    have hf_infty : f = 0 ∨ noPoleAtInfinity f := by
      right
      -- noPoleAtInfinity means intDegree ≤ 0
      rw [noPoleAtInfinity_iff_intDegree_le_zero]
      -- f = q'_K / gen_K^n
      -- intDegree(f) = intDegree(q') - intDegree(gen^n)
      have hq'_K_ne : q'_K ≠ 0 := RatFunc.algebraMap_ne_zero hq'_zero
      have hgen_pow_K_ne : gen_K ^ n.toNat ≠ 0 := pow_ne_zero _ hgen_K_ne

      -- intDegree(q') = natDegree(q') (polynomial)
      have h_q'_deg : q'_K.intDegree = (q'.natDegree : ℤ) := RatFunc.intDegree_polynomial

      -- intDegree(gen^n) = n.toNat * natDegree(gen)
      have h_gen_pow_deg : (gen_K ^ n.toNat).intDegree = n.toNat * (gen.natDegree : ℤ) := by
        induction n.toNat with
        | zero => simp [RatFunc.intDegree_one]
        | succ m ih =>
          rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero m hgen_K_ne) hgen_K_ne,
              ih, RatFunc.intDegree_polynomial]
          simp only [Nat.cast_succ]
          ring

      -- intDegree(f) = intDegree(q' / gen^n) = intDegree(q') + intDegree((gen^n)⁻¹)
      --             = intDegree(q') - intDegree(gen^n)
      have h_f_deg : f.intDegree = q'_K.intDegree - (gen_K ^ n.toNat).intDegree := by
        show (q'_K / gen_K ^ n.toNat).intDegree = _
        rw [div_eq_mul_inv, RatFunc.intDegree_mul hq'_K_ne (inv_ne_zero hgen_pow_K_ne),
            RatFunc.intDegree_inv]
        ring

      rw [h_f_deg, h_q'_deg, h_gen_pow_deg]
      -- Goal: natDegree(q') - n.toNat * natDegree(gen) ≤ 0
      -- i.e., natDegree(q') ≤ n.toNat * natDegree(gen)

      -- natDegree(q') < natDegree(gen) since q' = q %ₘ gen with monic gen
      have h_q'_lt : q'.natDegree < gen.natDegree :=
        Polynomial.natDegree_modByMonic_lt q hgen_monic hgen_ne_one

      -- n.toNat ≥ 1 since n = D v + 1 ≥ 1 (D effective means D v ≥ 0)
      have hn_pos : 0 < n.toNat := by
        have hDv_nn : 0 ≤ D v := hD v
        -- n = D v + 1 ≥ 1 > 0, so n.toNat > 0
        simp only [n, Int.lt_toNat, Int.ofNat_zero]
        omega

      -- n.toNat * natDegree(gen) ≥ natDegree(gen) ≥ natDegree(q') + 1 > natDegree(q')
      have h_bound : q'.natDegree < n.toNat * gen.natDegree := by
        calc q'.natDegree
            < gen.natDegree := h_q'_lt
          _ = 1 * gen.natDegree := (one_mul _).symm
          _ ≤ n.toNat * gen.natDegree := Nat.mul_le_mul_right _ hn_pos

      omega

    -- Step 5: Combine to get f ∈ RRSpace_ratfunc_projective
    let f_mem : RRSpace_ratfunc_projective (D + DivisorV2.single v 1) := ⟨f, hf_affine, hf_infty⟩

    -- Step 6: Show evaluationMapAt_complete maps f to c
    use ⟨f, hf_affine⟩
    -- The evaluation is: f ↦ (f * π^n).residue → κ(v)
    -- Since f = q/gen^n and π is a uniformizer, f*π^n = q * (π/gen)^n
    -- The residue of this should give back [q] = c
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

/-- Finiteness of L(D) for effective D (by induction on degWeighted).

Strategy:
- Base: degWeighted(D) = 0 ⟹ D = 0 ⟹ L(0) is finite
- Step: D = D' + [v] where D' has smaller degWeighted
  - L(D') is finite by IH
  - L(D)/L(D') embeds into κ(v) which is finite-dimensional
  - Therefore L(D) is finite
-/
instance RRSpace_ratfunc_projective_effective_finite (D : DivisorV2 (Polynomial k))
    (hD : D.Effective) :
    Module.Finite k (RRSpace_ratfunc_projective D) := by
  -- Weighted degree is non-negative for effective D
  have hdeg_nn : 0 ≤ degWeighted k D := degWeighted_nonneg_of_effective k D hD
  -- Convert to natural number for induction
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hdeg_nn

  -- Strong induction on n = degWeighted(D)
  induction n using Nat.strong_induction_on generalizing D with
  | _ n ih =>
    by_cases hn0 : n = 0
    · -- Base case: degWeighted(D) = 0 ⟹ D = 0 ⟹ L(0) is finite
      subst hn0
      have hD_zero : D = 0 := effective_degWeighted_zero_imp_zero k D hD hn
      rw [hD_zero]
      exact RRSpace_ratfunc_projective_zero_finite k

    · -- Inductive case: degWeighted(D) = n > 0
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hdeg_pos : 0 < degWeighted k D := by rw [hn]; exact Nat.cast_pos.mpr hn_pos

      -- There exists v with D(v) > 0
      obtain ⟨v, hv_pos⟩ := exists_pos_of_degWeighted_pos k D hD hdeg_pos

      -- Let D' = D - [v]
      set D' := D - DivisorV2.single v 1 with hD'_def

      -- D' is effective
      have hD'_eff : D'.Effective := DivisorV2.effective_sub_single hD v hv_pos

      -- degWeighted(D') = n - deg(v) < n
      have hdegW_D' : degWeighted k D' = (n : ℤ) - (degree k v : ℤ) := by
        rw [hD'_def, degWeighted_sub, degWeighted_single, one_mul, hn]

      have hdeg_v_pos : 0 < degree k v := degree_pos k v

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

      -- degWeighted(D') as natural number
      have hdegW_D'_nat : degWeighted k D' = ((n - degree k v : ℕ) : ℤ) := by
        rw [hdegW_D']
        have h : degree k v ≤ n := by omega
        omega

      have hdegW_D'_nn : 0 ≤ degWeighted k D' := by
        rw [hdegW_D']
        omega

      -- IH hypothesis: n - deg(v) < n
      have ih_hyp : n - degree k v < n := Nat.sub_lt hn_pos hdeg_v_pos

      -- Apply IH to D': L(D') is finite
      haveI hfin_D' : Module.Finite k (RRSpace_ratfunc_projective D') :=
        ih (n - degree k v) ih_hyp D' hD'_eff hdegW_D'_nn hdegW_D'_nat

      -- D = D' + [v]
      have hD_eq : D = D' + DivisorV2.single v 1 := by
        rw [hD'_def, sub_add_cancel]

      -- Now prove L(D) = L(D' + [v]) is finite
      -- Strategy: L(D')/L(D' + [v]) embeds into κ(v) which is finite

      -- The inclusion L(D') ↪ L(D' + [v])
      have hincl : RRSpace_ratfunc_projective D' ≤
          RRSpace_ratfunc_projective (D' + DivisorV2.single v 1) :=
        RRSpace_ratfunc_projective_mono_general k D' v

      -- The comap LD = L(D').comap(subtype) in L(D' + [v])
      let LD := (RRSpace_ratfunc_projective D').comap
          (RRSpace_ratfunc_projective (D' + DivisorV2.single v 1)).subtype

      -- LD equals range of inclusion
      have hLD_eq_range : LD = LinearMap.range (Submodule.inclusion hincl) := by
        ext x
        constructor
        · intro hx
          rw [Submodule.mem_comap] at hx
          rw [LinearMap.mem_range]
          exact ⟨⟨x.val, hx⟩, rfl⟩
        · intro hx
          rw [LinearMap.mem_range] at hx
          obtain ⟨y, hy⟩ := hx
          rw [Submodule.mem_comap]
          rw [← hy]; exact y.2

      -- LD is finite-dimensional (same as L(D'))
      haveI hLD_fin : Module.Finite k LD := by
        rw [hLD_eq_range]
        exact Module.Finite.range (Submodule.inclusion hincl)

      -- κ(v) is finite-dimensional
      haveI hκ_fin : Module.Finite k (residueFieldAtPrime (Polynomial k) v) :=
        residueFieldAtPrime_finite k v

      -- Build the evaluation map ψ : L(D' + [v]) → κ(v)
      let φ := evaluationMapAt_complete (R := Polynomial k) (K := RatFunc k) v D'

      have h_proj_to_affine : ∀ f, f ∈ RRSpace_ratfunc_projective (D' + DivisorV2.single v 1) →
          f ∈ RRModuleV2_real (Polynomial k) (RatFunc k) (D' + DivisorV2.single v 1) :=
        fun f hf => hf.1

      let ψ : ↥(RRSpace_ratfunc_projective (D' + DivisorV2.single v 1)) →ₗ[k]
          residueFieldAtPrime (Polynomial k) v := {
        toFun := fun x => φ ⟨x.val, h_proj_to_affine x.val x.property⟩
        map_add' := fun x y => by
          have := φ.map_add ⟨x.val, h_proj_to_affine x.val x.property⟩
              ⟨y.val, h_proj_to_affine y.val y.property⟩
          convert this using 1 <;> rfl
        map_smul' := fun c x => by
          have h1 : (c • x).val = (algebraMap k (Polynomial k) c) • x.val :=
            (IsScalarTower.algebraMap_smul (Polynomial k) c x.val).symm
          have hmem : (algebraMap k (Polynomial k) c) • x.val ∈
              RRModuleV2_real (Polynomial k) (RatFunc k) (D' + DivisorV2.single v 1) :=
            Submodule.smul_mem _ _ (h_proj_to_affine x.val x.property)
          have h2 : φ ⟨(algebraMap k (Polynomial k) c) • x.val, hmem⟩ =
              (algebraMap k (Polynomial k) c) • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ := by
            convert φ.map_smul (algebraMap k (Polynomial k) c) ⟨x.val, h_proj_to_affine x.val x.property⟩
          have h3 : (algebraMap k (Polynomial k) c) • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ =
              c • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ :=
            IsScalarTower.algebraMap_smul (Polynomial k) c _
          simp only [RingHom.id_apply]
          calc φ ⟨(c • x).val, h_proj_to_affine (c • x).val (c • x).property⟩
              = φ ⟨(algebraMap k (Polynomial k) c) • x.val, hmem⟩ := by simp only [h1]
            _ = (algebraMap k (Polynomial k) c) • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ := h2
            _ = c • φ ⟨x.val, h_proj_to_affine x.val x.property⟩ := h3
      }

      -- LD ≤ ker(ψ) (same proof as in GapBoundGeneral)
      have hle := divisor_le_add_single_general k D' v
      have h_LD_le_ker : LD ≤ LinearMap.ker ψ := by
        intro x hx
        rw [LinearMap.mem_ker]
        rw [Submodule.mem_comap] at hx
        have h_affine_mem : x.val ∈ RRModuleV2_real (Polynomial k) (RatFunc k) D' := hx.1
        have h_in_affine_Dv : x.val ∈ RRModuleV2_real (Polynomial k) (RatFunc k) (D' + DivisorV2.single v 1) :=
          RRModuleV2_mono_inclusion (Polynomial k) (RatFunc k) hle h_affine_mem
        let y_affine : RRModuleV2_real (Polynomial k) (RatFunc k) D' := ⟨x.val, h_affine_mem⟩
        have hinc : (⟨x.val, h_in_affine_Dv⟩ : RRModuleV2_real (Polynomial k) (RatFunc k) (D' + DivisorV2.single v 1)) =
            Submodule.inclusion (RRModuleV2_mono_inclusion (Polynomial k) (RatFunc k) hle) y_affine := rfl
        show ψ x = 0
        simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
        have hx_eq : (⟨x.val, h_proj_to_affine x.val x.property⟩ :
            RRModuleV2_real (Polynomial k) (RatFunc k) (D' + DivisorV2.single v 1)) =
            ⟨x.val, h_in_affine_Dv⟩ := rfl
        rw [hx_eq, hinc]
        exact LD_element_maps_to_zero v D' y_affine

      -- ker(ψ) ≤ LD (same proof as in GapBoundGeneral)
      have h_ker_le_LD : LinearMap.ker ψ ≤ LD := by
        intro x hx
        rw [LinearMap.mem_ker] at hx
        simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk] at hx
        have h_in_ker : (⟨x.val, h_proj_to_affine x.val x.property⟩ :
            RRModuleV2_real (Polynomial k) (RatFunc k) (D' + DivisorV2.single v 1)) ∈
            LinearMap.ker φ := hx
        rw [kernel_evaluationMapAt_complete_proof, LinearMap.mem_range] at h_in_ker
        obtain ⟨y, hy⟩ := h_in_ker
        rw [Submodule.mem_comap, Submodule.coe_subtype]
        have hval : y.val = x.val := congrArg Subtype.val hy
        have h_affine : x.val ∈ RRModuleV2_real (Polynomial k) (RatFunc k) D' := by
          rw [← hval]; exact y.property
        have h_infty : x.val = 0 ∨ noPoleAtInfinity x.val := x.property.2
        exact ⟨h_affine, h_infty⟩

      -- 1. The descended map quotient → κ(v) is injective
      let desc := Submodule.liftQ LD ψ h_LD_le_ker
      have hinj : Function.Injective desc :=
        LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ h_ker_le_LD)

      -- 2. κ(v) is finite dimensional, so the quotient is finite (injection into finite-dim)
      haveI : Module.Finite k (↥(RRSpace_ratfunc_projective (D' + DivisorV2.single v 1)) ⧸ LD) :=
        Module.Finite.of_injective desc hinj

      -- 3. Extension of finite by finite is finite
      rw [hD_eq]
      exact Module.Finite.of_submodule_quotient LD

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
        rw [hD'_def, degWeighted_sub, degWeighted_single, one_mul, hn]

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
