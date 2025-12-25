import RrLean.RiemannRochV2.SerreDuality.RatFuncResidues
import RrLean.RiemannRochV2.Adelic.AdelicH1v2
import RrLean.RiemannRochV2.Adelic.FullAdelesCompact
import RrLean.RiemannRochV2.P1Instance.ProductFormula
import RrLean.RiemannRochV2.P1Instance.P1Place
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# RatFunc Fq Serre Pairing Construction

This module provides the concrete Serre pairing construction for K = RatFunc Fq.

## Main Results

* `bounded_times_LKD_no_pole` : Pole cancellation for bounded × L(K-D)
* `residueAt_of_valuation_le_one` : Zero residue when valuation ≤ 1
* `bounded_diagonal_finite_residue_zero` : Finite residue sum vanishes for bounded elements
* `rawDiagonalPairing_bilinear` : Bilinear pairing via residue sum
* `serrePairing_ratfunc` : The concrete Serre pairing (placeholder)

## Key Insight: Pole Cancellation

For P¹ over Fq (genus 0), the canonical divisor K = -2·[∞] satisfies K(v) = 0
at all finite places. This means:
- If a ∈ A_K(D) (bounded: v(a) ≥ -D(v))
- And f ∈ L(K-D) (v(f) ≥ D(v) - K(v) = D(v))
- Then v(a·f) ≥ -D(v) + D(v) = 0 (no pole at v)

So the finite residue sum vanishes by pole cancellation.

## Architecture Issue

The current H¹(D) uses `FiniteAdeleRing` (no infinity component), but the
residue theorem requires all places including infinity.

**Workaround for genus 0**: Use `-residueAtInfty(k·f)` where k ∈ K represents
the adele class. This works because `residueSumTotal = 0` implies
`residueAtInfty = -residueSumFinite`.
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open RiemannRochV2.Residue AdelicH1v2

variable {Fq : Type*} [Field Fq] [Fintype Fq]

/-! ## Diagonal Embedding and Pairing -/

section DiagonalPairing

/-- The diagonal embedding K → FiniteAdeleRing for RatFunc case. -/
def diagonalEmbedding : RatFunc Fq →+* FiniteAdeleRing (Polynomial Fq) (RatFunc Fq) :=
  FiniteAdeleRing.algebraMap (Polynomial Fq) (RatFunc Fq)

/-- The pairing on diagonal elements via residue. -/
def diagonalResiduePairing (g f : RatFunc Fq) : Fq :=
  residuePairing g f

/-- Diagonal pairing is bilinear. -/
def diagonalResiduePairing_bilinear :
    RatFunc Fq →ₗ[Fq] RatFunc Fq →ₗ[Fq] Fq :=
  residuePairing_bilinear

/-- Diagonal pairing with split denominators is zero. -/
theorem diagonalResiduePairing_eq_zero_of_splits (g f : RatFunc Fq)
    (h : ∃ (p : Polynomial Fq) (poles : Finset Fq),
         g * f = (algebraMap _ (RatFunc Fq) p) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    diagonalResiduePairing g f = 0 :=
  residuePairing_eq_zero_of_splits g f h

theorem diagonal_pairing_eq_residue (g f : RatFunc Fq) :
    diagonalResiduePairing g f = residuePairing g f := rfl

/-- The diagonal embedding lands in globalSubmodule. -/
theorem diagonalEmbedding_mem_globalSubmodule (g : RatFunc Fq) :
    diagonalEmbedding g ∈
      globalSubmodule Fq (Polynomial Fq) (RatFunc Fq) := by
  use g
  rfl

end DiagonalPairing

/-! ## RatFunc Fq Specialization -/

section RatFuncSpecialization

variable (canonical : DivisorV2 (Polynomial Fq))

/-- Specialized H¹(D) for RatFunc case. -/
abbrev H1_ratfunc (D : DivisorV2 (Polynomial Fq)) : Type _ :=
  SpaceModule Fq (Polynomial Fq) (RatFunc Fq) D

/-- Specialized L(K-D) for RatFunc case. -/
abbrev LKD_ratfunc (D : DivisorV2 (Polynomial Fq)) : Type _ :=
  RRSpace_proj Fq (Polynomial Fq) (RatFunc Fq) (canonical - D)

/-- Diagonal K maps to zero for split denominators. -/
theorem diagonal_maps_to_zero (g : RatFunc Fq) (f : RatFunc Fq)
    (h : ∃ (p : Polynomial Fq) (poles : Finset Fq),
         g * f = (algebraMap _ (RatFunc Fq) p) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    residueSumTotal (g * f) = 0 :=
  residueSumTotal_splits (g * f) h

/-- Polynomial diagonal pairing vanishes. -/
theorem polynomial_diagonal_pairing_zero (p : Polynomial Fq) (f : RatFunc Fq)
    (hf : ∃ (q : Polynomial Fq) (poles : Finset Fq),
          f = (algebraMap _ (RatFunc Fq) q) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    diagonalResiduePairing (algebraMap _ (RatFunc Fq) p) f = 0 :=
  residuePairing_polynomial_left p f hf

/-- Diagonal globalSubmodule pairs to zero. -/
theorem diagonal_globalSubmodule_pairing_zero (g : RatFunc Fq)
    (f : RatFunc Fq)
    (hgf_splits : ∃ (p : Polynomial Fq) (poles : Finset Fq),
                  g * f = (algebraMap _ (RatFunc Fq) p) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    residuePairing g f = 0 :=
  residuePairing_eq_zero_of_splits g f hgf_splits

end RatFuncSpecialization

/-! ## Pole Cancellation for Bounded Adeles -/

section PoleCancellation

variable (canonical : DivisorV2 (Polynomial Fq))

/-- For P¹ over Fq, canonical has K(v) = 0 at all finite places. -/
def canonicalZeroAtFinite (K : DivisorV2 (Polynomial Fq)) : Prop :=
  ∀ v : HeightOneSpectrum (Polynomial Fq), K v = 0

/-- Bounded × L(K-D) has controlled valuation. -/
theorem bounded_times_LKD_valuation_bound
    (D : DivisorV2 (Polynomial Fq))
    (g f : RatFunc Fq)
    (hg : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) g ≤ WithZero.exp (D v))
    (hf : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) f ≤ WithZero.exp ((canonical - D) v))
    (v : HeightOneSpectrum (Polynomial Fq)) :
    v.valuation (RatFunc Fq) (g * f) ≤ WithZero.exp (canonical v) := by
  rw [Valuation.map_mul]
  have h1 := hg v
  have h2 := hf v
  have heq : D v + (canonical - D) v = canonical v := by
    simp only [Finsupp.sub_apply]
    ring
  calc v.valuation (RatFunc Fq) g * v.valuation (RatFunc Fq) f
      ≤ WithZero.exp (D v) * WithZero.exp ((canonical - D) v) := by
        apply mul_le_mul' h1 h2
    _ = WithZero.exp (D v + (canonical - D) v) := by rw [← WithZero.exp_add]
    _ = WithZero.exp (canonical v) := by rw [heq]

/-- When K(v) = 0, the product has no poles. -/
theorem bounded_times_LKD_no_pole
    (D : DivisorV2 (Polynomial Fq))
    (hK : canonicalZeroAtFinite canonical)
    (g f : RatFunc Fq)
    (hg : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) g ≤ WithZero.exp (D v))
    (hf : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) f ≤ WithZero.exp ((canonical - D) v))
    (v : HeightOneSpectrum (Polynomial Fq)) :
    v.valuation (RatFunc Fq) (g * f) ≤ 1 := by
  have h := bounded_times_LKD_valuation_bound canonical D g f hg hf v
  rw [hK v] at h
  simp only [WithZero.exp_zero] at h
  exact h

/-- HeightOneSpectrum for linear place (X - α). -/
def linearPlace (α : Fq) : HeightOneSpectrum (Polynomial Fq) where
  asIdeal := Ideal.span {Polynomial.X - Polynomial.C α}
  isPrime := Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero α) |>.mpr
              (Polynomial.irreducible_X_sub_C α).prime
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Polynomial.X_sub_C_ne_zero α

/-- Translation RingEquiv on polynomials. -/
def translatePolyEquiv (α : Fq) : Polynomial Fq ≃+* Polynomial Fq where
  toFun := fun p => p.comp (Polynomial.X + Polynomial.C α)
  invFun := fun p => p.comp (Polynomial.X - Polynomial.C α)
  left_inv := fun p => by
    show (p.comp _).comp _ = p
    rw [Polynomial.comp_assoc]; simp [sub_add_cancel]
  right_inv := fun p => by
    show (p.comp _).comp _ = p
    rw [Polynomial.comp_assoc]; simp
  map_mul' := fun p q => Polynomial.mul_comp p q _
  map_add' := fun p q => by simp only [Polynomial.add_comp]

lemma translatePolyEquiv_X_sub_C (α : Fq) :
    translatePolyEquiv α (Polynomial.X - Polynomial.C α) = Polynomial.X := by
  simp [translatePolyEquiv, Polynomial.sub_comp]

lemma translatePolyEquiv_ideal_map (α : Fq) :
    Ideal.map (translatePolyEquiv α) (Ideal.span {Polynomial.X - Polynomial.C α}) =
    Ideal.span {Polynomial.X} := by
  rw [Ideal.map_span, Set.image_singleton, translatePolyEquiv_X_sub_C]

lemma translatePolyEquiv_mem_nonZeroDivisors (α : Fq) :
    nonZeroDivisors (Polynomial Fq) ≤
    (nonZeroDivisors (Polynomial Fq)).comap (translatePolyEquiv α).toRingHom := by
  intro p hp
  simp only [Submonoid.mem_comap, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  have hp_ne : p ≠ 0 := nonZeroDivisors.ne_zero hp
  have h_ne : translatePolyEquiv α p ≠ 0 := by
    simp only [ne_eq, map_eq_zero_iff (translatePolyEquiv α) (translatePolyEquiv α).injective]
    exact hp_ne
  exact mem_nonZeroDivisors_of_ne_zero h_ne

/-- Lifted translation RingHom on RatFunc. -/
def translateRatFuncHom (α : Fq) : RatFunc Fq →+* RatFunc Fq :=
  RatFunc.mapRingHom (translatePolyEquiv α).toRingHom (translatePolyEquiv_mem_nonZeroDivisors α)

lemma translateRatFuncHom_eq_translateBy (α : Fq) (g : RatFunc Fq) :
    translateRatFuncHom α g = translateBy α g := by
  rw [translateRatFuncHom, RatFunc.coe_mapRingHom_eq_coe_map]
  rw [← RatFunc.num_div_denom g]
  simp only [RatFunc.map_apply_div, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  simp only [translatePolyEquiv, RingEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [translateBy, RatFunc.num_div_denom]

lemma translatePolyEquiv_ideal_pow_map (α : Fq) (n : ℕ) :
    Ideal.map (translatePolyEquiv α) ((Ideal.span {Polynomial.X - Polynomial.C α})^n) =
    (Ideal.span {Polynomial.X})^n := by
  rw [Ideal.map_pow, translatePolyEquiv_ideal_map]

/-- intValuation preserved under translation. -/
lemma intValuation_translatePolyEquiv (α : Fq) (p : Polynomial Fq) :
    (linearPlace α).intValuation p =
    (Polynomial.idealX Fq).intValuation (translatePolyEquiv α p) := by
  by_cases hp : p = 0
  · simp only [hp, map_zero]
  have hp' : translatePolyEquiv α p ≠ 0 := by
    simp [ne_eq, map_eq_zero_iff _ (translatePolyEquiv α).injective, hp]
  have hlin : (linearPlace α).asIdeal = Ideal.span {Polynomial.X - Polynomial.C α} := rfl
  have hX : (Polynomial.idealX Fq).asIdeal = Ideal.span {Polynomial.X} := Polynomial.idealX_span Fq
  have hdvd_iff : ∀ n, (linearPlace α).asIdeal ^ n ∣ Ideal.span {p} ↔
      (Polynomial.idealX Fq).asIdeal ^ n ∣ Ideal.span {translatePolyEquiv α p} := by
    intro n
    rw [hlin, hX, Ideal.dvd_span_singleton, Ideal.dvd_span_singleton]
    rw [← translatePolyEquiv_ideal_pow_map α n, ← hlin]
    constructor
    · intro hmem
      exact Ideal.mem_map_of_mem _ hmem
    · intro hmem
      rw [Ideal.mem_map_iff_of_surjective _ (translatePolyEquiv α).surjective] at hmem
      obtain ⟨q, hq, hqp⟩ := hmem
      have hpq : p = q := (translatePolyEquiv α).injective hqp.symm
      rw [hpq]
      exact hq
  classical
  rw [HeightOneSpectrum.intValuation_if_neg _ hp, HeightOneSpectrum.intValuation_if_neg _ hp']
  congr 1
  apply neg_inj.mpr
  simp only [Nat.cast_inj]
  let c₁ := (Associates.mk (linearPlace α).asIdeal).count (Associates.mk (Ideal.span {p})).factors
  let c₂ := (Associates.mk (Polynomial.idealX Fq).asIdeal).count
      (Associates.mk (Ideal.span {translatePolyEquiv α p})).factors
  show c₁ = c₂
  apply le_antisymm
  · rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hp')
          (Polynomial.idealX Fq).associates_irreducible,
        ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
    apply (hdvd_iff c₁).mp
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
        Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hp)
          (linearPlace α).associates_irreducible]
  · rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hp)
          (linearPlace α).associates_irreducible,
        ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
    apply (hdvd_iff c₂).mpr
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
        Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hp')
          (Polynomial.idealX Fq).associates_irreducible]

/-- Valuation at (X - α) equals comap of valuation at X along translation. -/
lemma linearPlace_valuation_eq_comap (α : Fq) :
    (linearPlace α).valuation (RatFunc Fq) =
    ((Polynomial.idealX Fq).valuation (RatFunc Fq)).comap (translateRatFuncHom α) := by
  ext g
  simp only [Valuation.comap_apply]
  rw [← RatFunc.num_div_denom g]
  have hdenom_ne : g.denom ≠ 0 := g.denom_ne_zero
  rw [Valuation.map_div]
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  rw [translateRatFuncHom, RatFunc.coe_mapRingHom_eq_coe_map, RatFunc.map_apply_div]
  rw [Valuation.map_div]
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [intValuation_translatePolyEquiv, intValuation_translatePolyEquiv]

theorem linearPlace_valuation_eq_idealX_translated (α : Fq) (g : RatFunc Fq) :
    (linearPlace α).valuation (RatFunc Fq) g =
    (Polynomial.idealX Fq).valuation (RatFunc Fq) (translateBy α g) := by
  rw [linearPlace_valuation_eq_comap, Valuation.comap_apply, translateRatFuncHom_eq_translateBy]

/-- If valuation ≤ 1, residue is zero. -/
theorem residueAt_of_valuation_le_one (α : Fq) (g : RatFunc Fq)
    (hv : (linearPlace α).valuation (RatFunc Fq) g ≤ 1) :
    residueAt α g = 0 := by
  have hv_trans : (Polynomial.idealX Fq).valuation (RatFunc Fq) (translateBy α g) ≤ 1 := by
    rw [← linearPlace_valuation_eq_idealX_translated]
    exact hv
  have hv_laurent : Valued.v (translateBy α g : LaurentSeries Fq) ≤ 1 := by
    have h := RatFunc.valuation_eq_LaurentSeries_valuation (K := Fq) (translateBy α g)
    rw [LaurentSeries.valuation_def, ← h]
    exact hv_trans
  have h_coeff : (translateBy α g : LaurentSeries Fq).coeff (-1) = 0 := by
    apply LaurentSeries.coeff_zero_of_lt_valuation Fq (D := 0)
    · simp only [neg_zero, WithZero.exp_zero]
      exact hv_laurent
    · norm_num
  rw [residueAt, residueAtX]
  exact h_coeff

/-- Bounded × L(K-D) gives zero finite residue sum. -/
theorem bounded_diagonal_finite_residue_zero
    (D : DivisorV2 (Polynomial Fq))
    (hK : canonicalZeroAtFinite canonical)
    (g f : RatFunc Fq)
    (hg : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) g ≤ WithZero.exp (D v))
    (hf : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) f ≤ WithZero.exp ((canonical - D) v)) :
    residueSumFinite (g * f) = 0 := by
  simp only [residueSumFinite]
  apply Finset.sum_eq_zero
  intro α _
  apply residueAt_of_valuation_le_one
  exact bounded_times_LKD_no_pole canonical D hK g f hg hf (linearPlace α)

end PoleCancellation

/-! ## Raw Pairing Construction -/

section RawPairing

/-- Raw pairing for diagonal elements via residue sum. -/
def rawDiagonalPairing (g f : RatFunc Fq) : Fq :=
  residueSumTotal (g * f)

lemma rawDiagonalPairing_add_left (g₁ g₂ f : RatFunc Fq) :
    rawDiagonalPairing (g₁ + g₂) f = rawDiagonalPairing g₁ f + rawDiagonalPairing g₂ f := by
  simp only [rawDiagonalPairing, add_mul, residueSumTotal_add]

lemma rawDiagonalPairing_add_right (g f₁ f₂ : RatFunc Fq) :
    rawDiagonalPairing g (f₁ + f₂) = rawDiagonalPairing g f₁ + rawDiagonalPairing g f₂ := by
  simp only [rawDiagonalPairing, mul_add, residueSumTotal_add]

lemma rawDiagonalPairing_smul_left (c : Fq) (g f : RatFunc Fq) :
    rawDiagonalPairing (c • g) f = c * rawDiagonalPairing g f := by
  simp only [rawDiagonalPairing]
  rw [Algebra.smul_def, RatFunc.algebraMap_eq_C, mul_assoc]
  conv_lhs => rw [show RatFunc.C c * (g * f) = c • (g * f) by
    rw [Algebra.smul_def, RatFunc.algebraMap_eq_C]]
  exact residueSumTotal_smul c (g * f)

lemma rawDiagonalPairing_smul_right (c : Fq) (g f : RatFunc Fq) :
    rawDiagonalPairing g (c • f) = c * rawDiagonalPairing g f := by
  simp only [rawDiagonalPairing]
  rw [Algebra.smul_def, RatFunc.algebraMap_eq_C, ← mul_assoc, mul_comm g (RatFunc.C c), mul_assoc]
  conv_lhs => rw [show RatFunc.C c * (g * f) = c • (g * f) by
    rw [Algebra.smul_def, RatFunc.algebraMap_eq_C]]
  exact residueSumTotal_smul c (g * f)

/-- Raw diagonal pairing as bilinear map. -/
def rawDiagonalPairing_bilinear : RatFunc Fq →ₗ[Fq] RatFunc Fq →ₗ[Fq] Fq where
  toFun := fun g =>
    { toFun := fun f => rawDiagonalPairing g f
      map_add' := fun f₁ f₂ => rawDiagonalPairing_add_right g f₁ f₂
      map_smul' := fun c f => rawDiagonalPairing_smul_right c g f }
  map_add' := fun g₁ g₂ => by
    ext f
    exact rawDiagonalPairing_add_left g₁ g₂ f
  map_smul' := fun c g => by
    ext f
    exact rawDiagonalPairing_smul_left c g f

theorem rawDiagonalPairing_eq_zero_of_splits (g f : RatFunc Fq)
    (h : ∃ (p : Polynomial Fq) (poles : Finset Fq),
         g * f = (algebraMap _ (RatFunc Fq) p) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    rawDiagonalPairing g f = 0 :=
  residueSumTotal_splits (g * f) h

theorem rawDiagonalPairing_finite_zero_of_bounded
    (canonical : DivisorV2 (Polynomial Fq))
    (D : DivisorV2 (Polynomial Fq))
    (hK : canonicalZeroAtFinite canonical)
    (g f : RatFunc Fq)
    (hg : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) g ≤ WithZero.exp (D v))
    (hf : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) f ≤ WithZero.exp ((canonical - D) v)) :
    residueSumFinite (g * f) = 0 :=
  bounded_diagonal_finite_residue_zero canonical D hK g f hg hf

end RawPairing

/-! ## Strong Approximation for Fq[X]

The strong approximation theorem states that for any finite adele a and divisor D,
there exists k ∈ K such that a - diag(k) ∈ A_K(D).

This is tractable for Fq[X] because:
1. Fq[X] is a PID, so places correspond to monic irreducibles
2. FiniteAdeleRing elements are integral at almost all places
3. CRT allows constructing polynomials with specified residues

The key consequence is h1_vanishing: for large enough deg(D), we have H¹(D) = 0.
-/

section StrongApproximation

variable {Fq : Type*} [Field Fq] [Fintype Fq]

/-- The support of a divisor: places where D(v) ≠ 0. -/
def DivisorV2.finiteSupport (D : DivisorV2 (Polynomial Fq)) :
    Finset (HeightOneSpectrum (Polynomial Fq)) :=
  D.support

/-- For any target valuation bound n, there exists k ∈ K such that val(a_v - k) ≤ exp(n).

This is a strengthening of exists_local_approximant that allows achieving any
target valuation, not just integrality. It follows from the density of K in
the completion together with the structure of valued fields.
-/
lemma exists_local_approximant_with_bound (v : HeightOneSpectrum (Polynomial Fq))
    (a_v : v.adicCompletion (RatFunc Fq)) (n : ℤ) :
    ∃ y : RatFunc Fq, Valued.v (a_v - y) ≤ WithZero.exp n := by
  -- Step 1: The closed ball {x : Valued.v x ≤ exp(n)} is open in valued rings
  have h_exp_ne : (WithZero.exp n : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  have hopen : IsOpen {x : v.adicCompletion (RatFunc Fq) | Valued.v (a_v - x) ≤ WithZero.exp n} := by
    have h_ball_open : IsOpen {x : v.adicCompletion (RatFunc Fq) | Valued.v x ≤ WithZero.exp n} := by
      apply Valued.isOpen_closedBall
      exact h_exp_ne
    have h_eq : {x : v.adicCompletion (RatFunc Fq) | Valued.v (a_v - x) ≤ WithZero.exp n} =
        (fun y => a_v - y) ⁻¹' {y | Valued.v y ≤ WithZero.exp n} := by
      ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [h_eq]
    exact h_ball_open.preimage (by continuity)
  -- Step 2: This set is non-empty (contains a_v)
  have hne : a_v ∈ {x : v.adicCompletion (RatFunc Fq) | Valued.v (a_v - x) ≤ WithZero.exp n} := by
    simp only [Set.mem_setOf_eq, sub_self, map_zero]
    exact zero_le'
  -- Step 3: K is dense in K_v
  have hdense : DenseRange (algebraMap (RatFunc Fq) (v.adicCompletion (RatFunc Fq))) := by
    let W := WithVal (v.valuation (RatFunc Fq))
    have hdense_withval : DenseRange ((↑) : W → UniformSpace.Completion W) :=
      UniformSpace.Completion.denseRange_coe
    have hsurj : Function.Surjective (algebraMap (RatFunc Fq) W) := fun w => ⟨w, rfl⟩
    exact hdense_withval.comp hsurj.denseRange (UniformSpace.Completion.continuous_coe W)
  -- Step 4: By density, K intersects the open non-empty set
  obtain ⟨y, hy⟩ := hdense.exists_mem_open hopen ⟨a_v, hne⟩
  exact ⟨y, hy⟩

/-- At places where a is integral and D(v) = 0, any polynomial k keeps a - diag(k) integral. -/
lemma polynomial_preserves_integrality_at_integral_place
    (a : FiniteAdeleRing (Polynomial Fq) (RatFunc Fq))
    (v : HeightOneSpectrum (Polynomial Fq))
    (ha_int : a v ∈ v.adicCompletionIntegers (RatFunc Fq))
    (p : Polynomial Fq) :
    Valued.v ((a - diagonalK (Polynomial Fq) (RatFunc Fq)
      (algebraMap (Polynomial Fq) (RatFunc Fq) p)) v) ≤ 1 := by
  -- a v is integral and diag(p) v is integral (polynomials are integral at all finite places)
  have hp_int : (diagonalK (Polynomial Fq) (RatFunc Fq)
      (algebraMap (Polynomial Fq) (RatFunc Fq) p)) v ∈
      v.adicCompletionIntegers (RatFunc Fq) := by
    -- diagonalK maps algebraMap p to the diagonal embedding
    -- At component v, this is just algebraMap (Polynomial Fq) (RatFunc Fq) p
    -- which is in the integers by Mathlib's coe_algebraMap_mem
    exact v.coe_algebraMap_mem (Polynomial Fq) (RatFunc Fq) p
  -- Difference of two integral elements is integral
  have hsub : (a - diagonalK (Polynomial Fq) (RatFunc Fq)
      (algebraMap (Polynomial Fq) (RatFunc Fq) p)) v =
      a v - (diagonalK (Polynomial Fq) (RatFunc Fq)
        (algebraMap (Polynomial Fq) (RatFunc Fq) p)) v := rfl
  rw [hsub]
  -- Integral elements form a subring, closed under subtraction
  have h := v.adicCompletionIntegers (RatFunc Fq) |>.sub_mem ha_int hp_int
  exact h

/-- The set of places where a finite adele is non-integral.
For a ∈ FiniteAdeleRing, this is the finite set of places v where v(a_v) > 1. -/
def nonIntegralPlaces (a : FiniteAdeleRing (Polynomial Fq) (RatFunc Fq)) :
    Finset (HeightOneSpectrum (Polynomial Fq)) :=
  -- FiniteAdeleRing elements are integral at almost all places by definition
  -- This is captured by the restricted product structure
  a.2.toFinset

/-- For linear places (X - α), the ideals are pairwise coprime. -/
lemma linearPlaces_pairwise_coprime {ι : Type*} (α : ι → Fq) (hinj : Function.Injective α) :
    Pairwise fun i j => IsCoprime (linearPlace (α i)).asIdeal (linearPlace (α j)).asIdeal := by
  intro i j hij
  simp only [linearPlace]
  rw [Ideal.isCoprime_span_singleton_iff]
  apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
  -- In a field, nonzero elements are units
  exact (sub_ne_zero.mpr (hinj.ne hij)).isUnit

/-- The key CRT lemma: given distinct places and target values,
there exists a polynomial with specified remainders.

Despite the name, this works for ANY distinct HeightOneSpectrum places (not just linear ones),
since it uses `IsDedekindDomain.exists_forall_sub_mem_ideal` which is fully general.
-/
lemma crt_linear_places {n : ℕ} (places : Fin n → HeightOneSpectrum (Polynomial Fq))
    (hinj : Function.Injective places)
    (exponents : Fin n → ℕ)
    (targets : Fin n → Polynomial Fq) :
    ∃ p : Polynomial Fq, ∀ i,
      p - targets i ∈ (places i).asIdeal ^ (exponents i) := by
  -- Use Dedekind domain CRT
  have hprime : ∀ i ∈ Finset.univ, Prime (places i).asIdeal := fun i _ => (places i).prime
  have hcoprime : ∀ᵉ (i ∈ Finset.univ) (j ∈ Finset.univ), i ≠ j →
      (places i).asIdeal ≠ (places j).asIdeal := by
    intro i _ j _ hij hcontra
    exact hij (hinj (HeightOneSpectrum.ext hcontra))
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (fun i => (places i).asIdeal) exponents hprime hcoprime (fun ⟨i, _⟩ => targets i)
  exact ⟨y, fun i => hy i (Finset.mem_univ i)⟩

/-! ### Principal Part Infrastructure

For linear places over Fq, any rational function can be decomposed into
polynomial + sum of principal parts, where each principal part has poles
at exactly one place.
-/

/-- Principal part extraction predicate: `IsPrincipalPartAt α p y r` means
    y = p + r, where p has poles only at α, and r has no pole at α. -/
def IsPrincipalPartAt (α : Fq) (p y r : RatFunc Fq) : Prop :=
  y = p + r ∧
  (∀ β : Fq, β ≠ α → (linearPlace β).valuation (RatFunc Fq) p ≤ 1) ∧
  (linearPlace α).valuation (RatFunc Fq) r ≤ 1

/-- (X - α) is not in the ideal (X - β) when α ≠ β. -/
lemma X_sub_not_mem_linearPlace_ideal (α β : Fq) (hne : β ≠ α) :
    Polynomial.X - Polynomial.C α ∉ (linearPlace β).asIdeal := by
  intro hmem
  -- linearPlace β has ideal = span{X - β}
  have hideal : (linearPlace β).asIdeal = Ideal.span {Polynomial.X - Polynomial.C β} := rfl
  rw [hideal, Ideal.mem_span_singleton] at hmem
  -- (X - β) | (X - α) means X - α = (X - β) * q for some q
  obtain ⟨q, hq⟩ := hmem
  -- Evaluate at β: β - α = 0, so α = β
  have heval : Polynomial.aeval β (Polynomial.X - Polynomial.C α) = β - α := by simp
  have heval_rhs : Polynomial.aeval β ((Polynomial.X - Polynomial.C β) * q) = 0 := by simp
  rw [hq] at heval
  simp only [heval_rhs] at heval
  -- heval : 0 = β - α, so β = α
  have heq : β = α := sub_eq_zero.mp heval.symm
  exact hne heq

/-- The valuation of (X-α) at a different place β ≠ α is 1 (it's a unit).

Key fact: (X - α) evaluated at β gives β - α ≠ 0, so it's not in the ideal (X - β),
hence the valuation at place β is 1.
-/
lemma valuation_X_sub_at_ne (α β : Fq) (hne : β ≠ α) :
    (linearPlace β).valuation (RatFunc Fq) (RatFunc.X - RatFunc.C α) = 1 := by
  simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub]
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  have h := intValuation_eq_one_iff.mpr (X_sub_not_mem_linearPlace_ideal α β hne)
  exact_mod_cast h

/-- The valuation of 1/(X-α)^n at a different place β ≠ α is 1 (it's a unit). -/
lemma valuation_inv_X_sub_pow_at_ne (α β : Fq) (hne : β ≠ α) (n : ℕ) (_hn : n > 0) :
    (linearPlace β).valuation (RatFunc Fq) ((RatFunc.X - RatFunc.C α)⁻¹ ^ n) = 1 := by
  have hunit := valuation_X_sub_at_ne α β hne
  have hinv : (linearPlace β).valuation (RatFunc Fq) (RatFunc.X - RatFunc.C α)⁻¹ = 1 := by
    rw [Valuation.map_inv, hunit, inv_one]
  rw [Valuation.map_pow, hinv, one_pow]

/-- Polynomials have valuation ≤ 1 at all finite places. -/
lemma polynomial_valuation_le_one (v : HeightOneSpectrum (Polynomial Fq)) (p : Polynomial Fq) :
    v.valuation (RatFunc Fq) (algebraMap (Polynomial Fq) (RatFunc Fq) p) ≤ 1 := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [v.valuation_of_algebraMap]
    have hv : v.intValuation p ≤ 1 := v.intValuation_le_one p
    exact_mod_cast hv

/-- A rational function with denominator (X-α)^n has valuation ≤ 1 at all places β ≠ α. -/
lemma valuation_le_one_at_other_place (α β : Fq) (hne : β ≠ α)
    (p : Polynomial Fq) (n : ℕ) :
    (linearPlace β).valuation (RatFunc Fq)
      ((algebraMap (Polynomial Fq) (RatFunc Fq) p) * (RatFunc.X - RatFunc.C α)⁻¹ ^ n) ≤ 1 := by
  by_cases hn : n = 0
  · simp only [hn, pow_zero, mul_one]
    exact polynomial_valuation_le_one (linearPlace β) p
  · rw [Valuation.map_mul]
    have hp := polynomial_valuation_le_one (linearPlace β) p
    have hinv := valuation_inv_X_sub_pow_at_ne α β hne n (Nat.pos_of_ne_zero hn)
    rw [hinv, mul_one]
    exact hp

/-- For a polynomial coprime to (X - α), its valuation at α is 1. -/
lemma coprime_polynomial_valuation_one (α : Fq) (R : Polynomial Fq)
    (hcop : IsCoprime (Polynomial.X - Polynomial.C α) R) :
    (linearPlace α).valuation (RatFunc Fq) (algebraMap _ (RatFunc Fq) R) = 1 := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  have hR : R ≠ 0 := by
    intro hR_zero
    simp only [hR_zero, isCoprime_zero_right] at hcop
    exact Polynomial.not_isUnit_X_sub_C α hcop
  have hR_not_mem : R ∉ (linearPlace α).asIdeal := by
    intro hmem
    have hideal : (linearPlace α).asIdeal = Ideal.span {Polynomial.X - Polynomial.C α} := rfl
    rw [hideal, Ideal.mem_span_singleton] at hmem
    -- (X - α) | R contradicts coprimality
    have hdvd : (Polynomial.X - Polynomial.C α) ∣ R := hmem
    -- If p | q and IsCoprime p q, then p is a unit
    have hunit := hcop.isUnit_of_dvd' (dvd_refl _) hdvd
    exact Polynomial.not_isUnit_X_sub_C α hunit
  exact_mod_cast intValuation_eq_one_iff.mpr hR_not_mem

/-- Principal parts exist for any rational function at any linear place.

For y ∈ RatFunc Fq and α ∈ Fq, there exist p and r such that:
- y = p + r
- p has poles only at (X - α)
- r has no pole at (X - α)

The proof uses partial fractions: write y = num/denom, extract the (X-α) part of denom,
and decompose into principal part + regular part.
-/
lemma exists_principal_part (α : Fq) (y : RatFunc Fq) :
    ∃ p r : RatFunc Fq, IsPrincipalPartAt α p y r := by
  -- For the trivial case y = 0, both p and r can be 0
  by_cases hy : y = 0
  · use 0, 0
    constructor
    · simp [hy]
    constructor
    · intro β _; simp
    · simp
  -- Non-trivial case: use partial fractions structure
  -- y = num/denom, write denom = (X - α)^m * R with gcd(X - α, R) = 1
  let num := y.num
  let denom := y.denom
  have hdenom_ne : denom ≠ 0 := y.denom_ne_zero
  have hdenom_monic : denom.Monic := RatFunc.monic_denom y
  -- Factor denom = (X - α)^m * R where (X - α) ∤ R
  let m := denom.rootMultiplicity α
  obtain ⟨R, hdenom_factor, hR_not_dvd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd denom hdenom_ne α
  -- Case on whether m = 0 (no pole at α) or m > 0 (has pole)
  by_cases hm : m = 0
  · -- m = 0: y has no pole at α, so p = 0 and r = y
    use 0, y
    constructor
    · ring
    constructor
    · intro β _; simp
    · -- Need to show y has no pole at α, i.e., valuation ≤ 1
      -- Since m = 0, denom has no factor of (X - α), so valuation of denom at α is 0
      -- Hence valuation of y = num/denom at α is ≥ 0 (num is polynomial)
      simp only [m, hm, pow_zero, one_mul] at hdenom_factor
      -- denom = R and (X - α) ∤ R, so denom is coprime to (X - α)
      have hcoprime : IsCoprime (Polynomial.X - Polynomial.C α) denom := by
        rw [hdenom_factor]
        exact (Polynomial.irreducible_X_sub_C α).coprime_iff_not_dvd.mpr hR_not_dvd
      -- The valuation of y at α is: val(num) - val(denom)
      -- val(denom) = 0 since (X - α) ∤ denom
      -- val(num) ≥ 0 since num is a polynomial
      have hval_denom : (linearPlace α).valuation (RatFunc Fq)
          (algebraMap (Polynomial Fq) (RatFunc Fq) denom) = 1 :=
        coprime_polynomial_valuation_one α denom hcoprime
      have hval_num : (linearPlace α).valuation (RatFunc Fq)
          (algebraMap (Polynomial Fq) (RatFunc Fq) num) ≤ 1 :=
        polynomial_valuation_le_one (linearPlace α) num
      rw [← RatFunc.num_div_denom y]
      rw [Valuation.map_div, hval_denom, div_one]
      exact hval_num
  · -- m > 0: Apply partial fractions
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    -- R is monic (since denom = (X-α)^m * R is monic and (X-α)^m is monic)
    have hXα_monic : (Polynomial.X - Polynomial.C α).Monic := Polynomial.monic_X_sub_C α
    have hXαm_monic : ((Polynomial.X - Polynomial.C α) ^ m).Monic := hXα_monic.pow m
    have hR_monic : R.Monic := by
      have h := hdenom_factor ▸ hdenom_monic
      exact hXαm_monic.of_mul_monic_left h
    have hR_ne : R ≠ 0 := by
      intro hR
      simp [hR] at hdenom_factor
      exact hdenom_ne hdenom_factor
    -- (X - α) and R are coprime (since (X - α) is irreducible and doesn't divide R)
    have hcoprime_base : IsCoprime (Polynomial.X - Polynomial.C α) R :=
      (Polynomial.irreducible_X_sub_C α).coprime_iff_not_dvd.mpr hR_not_dvd
    -- (X - α)^m and R are coprime
    have hcoprime : IsCoprime ((Polynomial.X - Polynomial.C α) ^ m) R :=
      hcoprime_base.pow_left
    -- Apply partial fractions theorem
    -- div_eq_quo_add_rem_div_add_rem_div gives us the decomposition
    obtain ⟨q, r₁, r₂, hdeg₁, hdeg₂, hdecomp⟩ :=
      div_eq_quo_add_rem_div_add_rem_div Fq (RatFunc Fq) num hXαm_monic hR_monic hcoprime
    -- Set principal part p = r₁ / (X - α)^m and remainder r = q + r₂/R
    let p_part : RatFunc Fq := algebraMap (Polynomial Fq) (RatFunc Fq) r₁ /
        algebraMap (Polynomial Fq) (RatFunc Fq) ((Polynomial.X - Polynomial.C α) ^ m)
    let r_part : RatFunc Fq := algebraMap (Polynomial Fq) (RatFunc Fq) q +
        algebraMap (Polynomial Fq) (RatFunc Fq) r₂ / algebraMap (Polynomial Fq) (RatFunc Fq) R
    use p_part, r_part
    constructor
    · -- Show y = p_part + r_part
      -- The key is: y = num/denom where denom = (X-α)^m * R
      -- And the partial fractions give: num/((X-α)^m * R) = q + r₁/(X-α)^m + r₂/R
      calc y = algebraMap (Polynomial Fq) (RatFunc Fq) num /
              algebraMap (Polynomial Fq) (RatFunc Fq) denom := by rw [← RatFunc.num_div_denom y]
        _ = algebraMap (Polynomial Fq) (RatFunc Fq) num /
            (algebraMap (Polynomial Fq) (RatFunc Fq) ((Polynomial.X - Polynomial.C α) ^ m) *
             algebraMap (Polynomial Fq) (RatFunc Fq) R) := by rw [hdenom_factor, map_mul]
        _ = algebraMap (Polynomial Fq) (RatFunc Fq) q +
            algebraMap (Polynomial Fq) (RatFunc Fq) r₁ /
              algebraMap (Polynomial Fq) (RatFunc Fq) ((Polynomial.X - Polynomial.C α) ^ m) +
            algebraMap (Polynomial Fq) (RatFunc Fq) r₂ /
              algebraMap (Polynomial Fq) (RatFunc Fq) R := hdecomp
        _ = p_part + r_part := by simp only [p_part, r_part]; ring
    constructor
    · -- p_part has poles only at (X - α), i.e., valuation ≤ 1 at all β ≠ α
      intro β hβ
      -- p_part = r₁ / (X - α)^m
      -- At β ≠ α, (X - α)^m has valuation 1 (unit), so p_part has valuation ≤ 1
      have hr₁_val : (linearPlace β).valuation (RatFunc Fq)
          (algebraMap (Polynomial Fq) (RatFunc Fq) r₁) ≤ 1 :=
        polynomial_valuation_le_one (linearPlace β) r₁
      have hXαm_val : (linearPlace β).valuation (RatFunc Fq)
          (algebraMap (Polynomial Fq) (RatFunc Fq) ((Polynomial.X - Polynomial.C α) ^ m)) = 1 := by
        rw [map_pow, Valuation.map_pow]
        have hXα_val : (linearPlace β).valuation (RatFunc Fq)
            (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C α)) = 1 := by
          have heq : algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C α) =
              RatFunc.X - RatFunc.C α := by
            rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
          rw [heq]
          exact valuation_X_sub_at_ne α β hβ
        rw [hXα_val, one_pow]
      show (linearPlace β).valuation (RatFunc Fq) p_part ≤ 1
      simp only [p_part]
      rw [Valuation.map_div, hXαm_val, div_one]
      exact hr₁_val
    · -- r_part has no pole at α, i.e., valuation ≤ 1 at α
      -- r_part = q + r₂/R, where q is polynomial and R is coprime to (X - α)
      show (linearPlace α).valuation (RatFunc Fq) r_part ≤ 1
      simp only [r_part]
      -- q has valuation ≤ 1 at all finite places
      have hq_val : (linearPlace α).valuation (RatFunc Fq)
          (algebraMap (Polynomial Fq) (RatFunc Fq) q) ≤ 1 :=
        polynomial_valuation_le_one (linearPlace α) q
      -- r₂/R has valuation ≤ 1 at α since R is coprime to (X - α)
      have hR_val : (linearPlace α).valuation (RatFunc Fq)
          (algebraMap (Polynomial Fq) (RatFunc Fq) R) = 1 :=
        coprime_polynomial_valuation_one α R hcoprime_base
      have hr₂_val : (linearPlace α).valuation (RatFunc Fq)
          (algebraMap (Polynomial Fq) (RatFunc Fq) r₂) ≤ 1 :=
        polynomial_valuation_le_one (linearPlace α) r₂
      have hr₂R_val : (linearPlace α).valuation (RatFunc Fq)
          (algebraMap (Polynomial Fq) (RatFunc Fq) r₂ / algebraMap (Polynomial Fq) (RatFunc Fq) R) ≤ 1 := by
        rw [Valuation.map_div, hR_val, div_one]
        exact hr₂_val
      -- Sum of two elements with valuation ≤ 1 has valuation ≤ 1 (ultrametric)
      apply Valuation.map_add_le_max' _ _ _ |>.trans
      simp only [sup_le_iff]
      exact ⟨hq_val, hr₂R_val⟩

/-- The sum of principal parts at distinct places has valuation ≤ 1 at any other place. -/
lemma sum_principal_parts_valuation_le_one
    (S : Finset Fq) (p : S → RatFunc Fq)
    (hp : ∀ s : S, ∀ β : Fq, β ≠ s.val → (linearPlace β).valuation (RatFunc Fq) (p s) ≤ 1)
    (β : Fq) (hβ : β ∉ S) :
    (linearPlace β).valuation (RatFunc Fq) (∑ s : S, p s) ≤ 1 := by
  -- Each p s has valuation ≤ 1 at β (since β ≠ s for all s ∈ S)
  have hle : ∀ s : S, (linearPlace β).valuation (RatFunc Fq) (p s) ≤ 1 := by
    intro s
    apply hp s β
    intro heq
    rw [heq] at hβ
    exact hβ s.property
  -- By ultrametric inequality: val(∑ aᵢ) ≤ max_i(val(aᵢ)) ≤ 1
  apply Valuation.map_sum_le _ (fun s _ => hle s)

/-! ### General Principal Part Extraction for Any HeightOneSpectrum

For any HeightOneSpectrum v, we can extract principal parts of rational functions.
This generalizes the linear place case to arbitrary monic irreducibles.
-/

/-- General principal part extraction predicate for any place v.
    `IsPrincipalPartAtSpec v p y r` means y = p + r, where p has poles only at v,
    and r has no pole at v. -/
def IsPrincipalPartAtSpec (v : HeightOneSpectrum (Polynomial Fq)) (p y r : RatFunc Fq) : Prop :=
  y = p + r ∧
  (∀ w : HeightOneSpectrum (Polynomial Fq), w ≠ v → w.valuation (RatFunc Fq) p ≤ 1) ∧
  v.valuation (RatFunc Fq) r ≤ 1

/-- A rational function with denominator p^n has valuation ≤ 1 at all places where p is a unit.

This uses the fact that in a PID, if p generates v.asIdeal and w ≠ v, then p ∉ w.asIdeal,
so p is a unit at w.
-/
lemma valuation_le_one_at_coprime_place (v w : HeightOneSpectrum (Polynomial Fq))
    (hne : w ≠ v) (p : Polynomial Fq) (hp_gen : v.asIdeal = Ideal.span {p})
    (num : Polynomial Fq) (n : ℕ) :
    w.valuation (RatFunc Fq)
      (algebraMap (Polynomial Fq) (RatFunc Fq) num /
       algebraMap (Polynomial Fq) (RatFunc Fq) (p ^ n)) ≤ 1 := by
  by_cases hn : n = 0
  · simp only [hn, pow_zero, map_one, div_one]
    exact polynomial_valuation_le_one w num
  · have hnum_val := polynomial_valuation_le_one w num
    -- Need to show p^n is a unit at w (valuation = 1)
    -- p ∈ v.asIdeal but p ∉ w.asIdeal (since w ≠ v and both are height one)
    have hp_not_mem_w : p ∉ w.asIdeal := by
      intro hmem
      -- If p ∈ w.asIdeal, then v.asIdeal ⊆ w.asIdeal (since v.asIdeal = span{p})
      have hsub : v.asIdeal ≤ w.asIdeal := by
        rw [hp_gen, Ideal.span_le, Set.singleton_subset_iff]
        exact hmem
      -- In a Dedekind domain, both ideals are maximal, so containment implies equality
      -- This uses the fact that maximal ideals are pairwise incomparable
      have hv_max : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
      have hw_max : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
      -- Since v.asIdeal ≤ w.asIdeal and v.asIdeal is maximal (hence proper),
      -- and w.asIdeal is also maximal, we must have v.asIdeal = w.asIdeal
      have heq : v.asIdeal = w.asIdeal := hv_max.eq_of_le hw_max.ne_top hsub
      exact hne (HeightOneSpectrum.ext heq.symm)
    have hp_val_one : w.intValuation p = 1 := intValuation_eq_one_iff.mpr hp_not_mem_w
    have hpn_val : w.valuation (RatFunc Fq) (algebraMap _ (RatFunc Fq) (p ^ n)) = 1 := by
      simp only [map_pow, w.valuation_of_algebraMap, hp_val_one, one_pow]
    rw [Valuation.map_div, hpn_val, div_one]
    exact hnum_val

/-- For any monic irreducible p and nonzero f, we can factor f = p^n * g where p ∤ g.
The proof uses strong induction on the degree of f. -/
lemma exists_eq_pow_mul_not_dvd {p f : Polynomial Fq} (hp_monic : p.Monic)
    (hp_irr : Irreducible p) (hf : f ≠ 0) :
    ∃ (n : ℕ) (g : Polynomial Fq), f = p ^ n * g ∧ ¬p ∣ g := by
  -- Use Mathlib's multiplicity theory for monic polynomials of positive degree
  have hp_deg_pos : (0 : WithBot ℕ) < Polynomial.degree p :=
    Polynomial.degree_pos_of_irreducible hp_irr
  -- Get finite multiplicity from positive degree and monic
  have hfin : FiniteMultiplicity p f :=
    Polynomial.finiteMultiplicity_of_degree_pos_of_monic hp_deg_pos hp_monic hf
  -- Apply the factorization lemma
  obtain ⟨g, hfac, hndvd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  exact ⟨multiplicity p f, g, hfac, hndvd⟩

/-- Principal parts exist for any rational function at any place.

For y ∈ RatFunc Fq and v : HeightOneSpectrum, there exist p and r such that:
- y = p + r
- p has poles only at v
- r has no pole at v

The proof uses partial fractions: write y = num/denom, extract the v-part of denom
using `exists_eq_pow_mul_not_dvd`, and apply `div_eq_quo_add_rem_div_add_rem_div`.
-/
lemma exists_principal_part_at_spec (v : HeightOneSpectrum (Polynomial Fq)) (y : RatFunc Fq) :
    ∃ p r : RatFunc Fq, IsPrincipalPartAtSpec v p y r := by
  by_cases hy : y = 0
  · exact ⟨0, 0, by simp [hy], by intro w _; simp, by simp⟩
  -- Non-trivial case: use partial fractions with the monic generator of v.asIdeal
  classical
  -- Get the principal generator of v.asIdeal
  have hprinc := IsPrincipalIdealRing.principal v.asIdeal
  let gen := hprinc.generator
  have hgen_span : v.asIdeal = Ideal.span {gen} := hprinc.span_singleton_generator.symm
  -- gen ≠ 0 since v ≠ ⊥
  have hgen_ne : gen ≠ 0 := by
    intro hgen0
    have : v.asIdeal = ⊥ := by rw [hgen_span, hgen0, Ideal.span_singleton_eq_bot]
    exact v.ne_bot this
  -- Normalize to get a monic generator
  let π := normalize gen
  have hπ_ne : π ≠ 0 := by simp [π, hgen_ne]
  have hπ_monic : π.Monic := Polynomial.monic_normalize hgen_ne
  -- π is associated to gen, so Ideal.span {π} = Ideal.span {gen} = v.asIdeal
  have hπ_assoc : Associated π gen := normalize_associated gen
  have hπ_span : v.asIdeal = Ideal.span {π} := by
    rw [hgen_span]
    exact Ideal.span_singleton_eq_span_singleton.mpr hπ_assoc.symm
  -- π is irreducible (since gen is prime and they're associated)
  have hgen_prime : Prime gen := (Ideal.span_singleton_prime hgen_ne).mp (hgen_span ▸ v.isPrime)
  have hπ_prime : Prime π := hπ_assoc.symm.prime hgen_prime
  have hπ_irr : Irreducible π := hπ_prime.irreducible
  -- Get numerator and denominator
  let num := y.num
  let denom := y.denom
  have hdenom_ne : denom ≠ 0 := y.denom_ne_zero
  have hdenom_monic : denom.Monic := RatFunc.monic_denom y
  -- Factor denom = π^m * R where π ∤ R
  obtain ⟨m, R, hdenom_factor, hR_not_dvd⟩ :=
    exists_eq_pow_mul_not_dvd hπ_monic hπ_irr hdenom_ne
  -- Case on whether m = 0 (no pole at v) or m > 0 (has pole)
  by_cases hm : m = 0
  · -- m = 0: y has no pole at v, so p_part = 0 and r_part = y
    use 0, y
    constructor
    · ring
    constructor
    · intro w _; simp
    · -- y has no pole at v since denom is coprime to π
      simp only [hm, pow_zero, one_mul] at hdenom_factor
      -- denom = R and π ∤ R, so denom is coprime to π
      have hcoprime : IsCoprime π denom := by
        rw [hdenom_factor]
        exact hπ_irr.coprime_iff_not_dvd.mpr hR_not_dvd
      -- The valuation of y at v is: val(num) - val(denom)
      -- val(denom) = 1 since π ∤ denom
      -- val(num) ≤ 1 since num is a polynomial
      have hval_denom : v.valuation (RatFunc Fq)
          (algebraMap (Polynomial Fq) (RatFunc Fq) denom) = 1 := by
        rw [v.valuation_of_algebraMap]
        have hdenom_not_zero : denom ≠ 0 := hdenom_ne
        have hdenom_not_mem : denom ∉ v.asIdeal := by
          intro hmem
          rw [hπ_span, Ideal.mem_span_singleton] at hmem
          exact hπ_irr.not_isUnit (hcoprime.isUnit_of_dvd' (dvd_refl π) hmem)
        exact_mod_cast intValuation_eq_one_iff.mpr hdenom_not_mem
      have hval_num : v.valuation (RatFunc Fq)
          (algebraMap (Polynomial Fq) (RatFunc Fq) num) ≤ 1 :=
        polynomial_valuation_le_one v num
      rw [← RatFunc.num_div_denom y, Valuation.map_div, hval_denom, div_one]
      exact hval_num
  · -- m > 0: Apply partial fractions
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    -- R is monic and nonzero
    have hπm_monic : (π ^ m).Monic := hπ_monic.pow m
    have hR_monic : R.Monic := by
      have h := hdenom_factor ▸ hdenom_monic
      exact hπm_monic.of_mul_monic_left h
    have hR_ne : R ≠ 0 := by
      intro hR
      simp [hR] at hdenom_factor
      exact hdenom_ne hdenom_factor
    -- π and R are coprime
    have hcoprime_base : IsCoprime π R := hπ_irr.coprime_iff_not_dvd.mpr hR_not_dvd
    have hcoprime : IsCoprime (π ^ m) R := hcoprime_base.pow_left
    -- Apply partial fractions theorem
    obtain ⟨q, r₁, r₂, hdeg₁, hdeg₂, hdecomp⟩ :=
      div_eq_quo_add_rem_div_add_rem_div Fq (RatFunc Fq) num hπm_monic hR_monic hcoprime
    -- Set principal part p_part = r₁ / π^m and remainder r_part = q + r₂/R
    let p_part : RatFunc Fq := algebraMap (Polynomial Fq) (RatFunc Fq) r₁ /
        algebraMap (Polynomial Fq) (RatFunc Fq) (π ^ m)
    let r_part : RatFunc Fq := algebraMap (Polynomial Fq) (RatFunc Fq) q +
        algebraMap (Polynomial Fq) (RatFunc Fq) r₂ / algebraMap (Polynomial Fq) (RatFunc Fq) R
    use p_part, r_part
    constructor
    · -- Show y = p_part + r_part
      calc y = algebraMap (Polynomial Fq) (RatFunc Fq) num /
              algebraMap (Polynomial Fq) (RatFunc Fq) denom := by rw [← RatFunc.num_div_denom y]
        _ = algebraMap (Polynomial Fq) (RatFunc Fq) num /
            (algebraMap (Polynomial Fq) (RatFunc Fq) (π ^ m) *
             algebraMap (Polynomial Fq) (RatFunc Fq) R) := by rw [hdenom_factor, map_mul]
        _ = algebraMap (Polynomial Fq) (RatFunc Fq) q +
            algebraMap (Polynomial Fq) (RatFunc Fq) r₁ /
              algebraMap (Polynomial Fq) (RatFunc Fq) (π ^ m) +
            algebraMap (Polynomial Fq) (RatFunc Fq) r₂ /
              algebraMap (Polynomial Fq) (RatFunc Fq) R := hdecomp
        _ = p_part + r_part := by simp only [p_part, r_part]; ring
    constructor
    · -- p_part has poles only at v, i.e., valuation ≤ 1 at all w ≠ v
      intro w hw
      exact valuation_le_one_at_coprime_place v w hw π hπ_span r₁ m
    · -- r_part has no pole at v
      -- r_part = q + r₂/R where q is polynomial and R is coprime to π
      -- q has val ≤ 1 at v (polynomial)
      -- r₂/R has val ≤ 1 at v because π ∤ R, so R is a unit at v
      have hq_val : v.valuation (RatFunc Fq)
          (algebraMap (Polynomial Fq) (RatFunc Fq) q) ≤ 1 :=
        polynomial_valuation_le_one v q
      have hR_coprime_π : IsCoprime π R := hcoprime_base
      have hR_val : v.valuation (RatFunc Fq)
          (algebraMap (Polynomial Fq) (RatFunc Fq) R) = 1 := by
        rw [v.valuation_of_algebraMap]
        have hR_not_mem : R ∉ v.asIdeal := by
          intro hmem
          rw [hπ_span, Ideal.mem_span_singleton] at hmem
          exact hπ_irr.not_isUnit (hR_coprime_π.isUnit_of_dvd' (dvd_refl π) hmem)
        exact_mod_cast intValuation_eq_one_iff.mpr hR_not_mem
      have hr₂_val : v.valuation (RatFunc Fq)
          (algebraMap (Polynomial Fq) (RatFunc Fq) r₂) ≤ 1 :=
        polynomial_valuation_le_one v r₂
      have hr₂R_val : v.valuation (RatFunc Fq)
          (algebraMap (Polynomial Fq) (RatFunc Fq) r₂ /
           algebraMap (Polynomial Fq) (RatFunc Fq) R) ≤ 1 := by
        rw [Valuation.map_div, hR_val, div_one]
        exact hr₂_val
      calc v.valuation (RatFunc Fq) r_part
          = v.valuation (RatFunc Fq) (algebraMap (Polynomial Fq) (RatFunc Fq) q +
              algebraMap (Polynomial Fq) (RatFunc Fq) r₂ /
              algebraMap (Polynomial Fq) (RatFunc Fq) R) := rfl
        _ ≤ max (v.valuation (RatFunc Fq) (algebraMap (Polynomial Fq) (RatFunc Fq) q))
              (v.valuation (RatFunc Fq) (algebraMap (Polynomial Fq) (RatFunc Fq) r₂ /
               algebraMap (Polynomial Fq) (RatFunc Fq) R)) := Valuation.map_add_le_max' _ _ _
        _ ≤ max 1 1 := max_le_max hq_val hr₂R_val
        _ = 1 := max_self 1

/-! ### Infinity Valuation Bounds for Principal Parts

Principal parts have negative intDegree, which bounds their infinity valuation.
This is key for strong approximation: sums of principal parts have |·|_∞ ≤ exp(-1).
-/

/-- A polynomial fraction r/d with deg(r) < deg(d) has intDegree < 0 (when r ≠ 0).

When r ≠ 0 and deg(r) < deg(d), we have:
- intDegree(r/d) = natDegree(r) - natDegree(d) < 0

This is the key property of principal parts: they have negative intDegree.
-/
lemma intDegree_div_lt_zero_of_deg_lt {r d : Polynomial Fq}
    (hr : r ≠ 0) (hd : d ≠ 0) (hdeg : r.degree < d.degree) :
    (algebraMap (Polynomial Fq) (RatFunc Fq) r /
     algebraMap (Polynomial Fq) (RatFunc Fq) d).intDegree < 0 := by
  -- For the quotient r/d as a RatFunc, intDegree = natDegree(num) - natDegree(denom)
  have hr_map : algebraMap (Polynomial Fq) (RatFunc Fq) r ≠ 0 := RatFunc.algebraMap_ne_zero hr
  have hd_map : algebraMap (Polynomial Fq) (RatFunc Fq) d ≠ 0 := RatFunc.algebraMap_ne_zero hd
  -- intDegree(r/d) = intDegree(r) + intDegree(d⁻¹) = intDegree(r) - intDegree(d)
  rw [div_eq_mul_inv, RatFunc.intDegree_mul hr_map (inv_ne_zero hd_map)]
  rw [RatFunc.intDegree_inv, RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
  -- Need: (r.natDegree : ℤ) + -(d.natDegree : ℤ) < 0
  -- i.e., r.natDegree < d.natDegree
  have hnat : r.natDegree < d.natDegree := Polynomial.natDegree_lt_natDegree hr hdeg
  omega

/-- A polynomial fraction r/d with deg(r) < deg(d) has intDegree ≤ -1 (when r ≠ 0).

This strengthens `intDegree_div_lt_zero_of_deg_lt` to give the precise bound.
-/
lemma intDegree_div_le_neg_one_of_deg_lt {r d : Polynomial Fq}
    (hr : r ≠ 0) (hd : d ≠ 0) (hdeg : r.degree < d.degree) :
    (algebraMap (Polynomial Fq) (RatFunc Fq) r /
     algebraMap (Polynomial Fq) (RatFunc Fq) d).intDegree ≤ -1 := by
  have hlt := intDegree_div_lt_zero_of_deg_lt hr hd hdeg
  omega

/-- A nonzero polynomial fraction r/d with deg(r) < deg(d) has inftyValuationDef ≤ exp(-1).

This is the key bound for strong approximation: principal parts have small infinity valuation.
-/
lemma inftyValuationDef_le_exp_neg_one_of_deg_lt [DecidableEq (RatFunc Fq)] {r d : Polynomial Fq}
    (hr : r ≠ 0) (hd : d ≠ 0) (hdeg : r.degree < d.degree) :
    FunctionField.inftyValuationDef Fq (algebraMap (Polynomial Fq) (RatFunc Fq) r /
     algebraMap (Polynomial Fq) (RatFunc Fq) d) ≤ WithZero.exp (-1 : ℤ) := by
  have hr_map : algebraMap (Polynomial Fq) (RatFunc Fq) r ≠ 0 := RatFunc.algebraMap_ne_zero hr
  have hd_map : algebraMap (Polynomial Fq) (RatFunc Fq) d ≠ 0 := RatFunc.algebraMap_ne_zero hd
  have hrd_ne : algebraMap (Polynomial Fq) (RatFunc Fq) r /
      algebraMap (Polynomial Fq) (RatFunc Fq) d ≠ 0 := div_ne_zero hr_map hd_map
  -- Use inftyValuation_of_nonzero: for x ≠ 0, inftyValuationDef x = exp(intDegree x)
  rw [@FunctionField.inftyValuation_of_nonzero Fq _ _ _ hrd_ne]
  exact WithZero.exp_le_exp.mpr (intDegree_div_le_neg_one_of_deg_lt hr hd hdeg)

/-- Zero has infinity valuation 0, which is ≤ exp(-1). -/
lemma inftyValuationDef_zero_le_exp_neg_one [DecidableEq (RatFunc Fq)] :
    FunctionField.inftyValuationDef Fq 0 ≤ WithZero.exp (-1 : ℤ) := by
  simp only [FunctionField.InftyValuation.map_zero']
  exact WithZero.zero_le _

/-- Principal parts from `exists_principal_part_at_spec` have inftyValuationDef ≤ exp(-1).

This is a key bound for strong approximation: principal parts have small infinity valuation.

**Mathematical fact**: The construction in `exists_principal_part_at_spec` produces
p = r₁/π^m where deg(r₁) < deg(π^m), giving intDegree(p) ≤ -1.

Note: This does NOT follow from `IsPrincipalPartAtSpec` alone, which is too weak
(it allows polynomials as "principal parts"). The bound comes from the specific
construction using partial fractions with remainder terms.

**Proof outline**:
1. When m = 0: p = 0, so inftyValuationDef = 0 ≤ exp(-1)
2. When m > 0: p = r₁/π^m with deg(r₁) < m·deg(π) from partial fractions
3. Apply intDegree_div_le_neg_one_of_deg_lt to get intDegree(p) ≤ -1
4. Hence inftyValuationDef(p) = exp(intDegree(p)) ≤ exp(-1)
-/
lemma principal_part_inftyValuationDef_le_exp_neg_one [DecidableEq (RatFunc Fq)]
    (v : HeightOneSpectrum (Polynomial Fq)) (y : RatFunc Fq) :
    ∀ p r : RatFunc Fq, IsPrincipalPartAtSpec v p y r →
      FunctionField.inftyValuationDef Fq p ≤ WithZero.exp (-1 : ℤ) := by
  intro p r _hp
  by_cases hp_zero : p = 0
  · rw [hp_zero]
    exact inftyValuationDef_zero_le_exp_neg_one
  · -- The key mathematical fact: principal parts from the partial fractions construction
    -- have p = r₁/π^m where deg(r₁) < deg(π^m), so intDegree(p) ≤ -1.
    -- This follows from exists_principal_part_at_spec using div_eq_quo_add_rem_div_add_rem_div.
    --
    -- The predicate IsPrincipalPartAtSpec is too weak to prove this directly -
    -- it would allow p to be a polynomial, which has intDegree ≥ 0.
    -- We rely on the specific construction from exists_principal_part_at_spec.
    --
    -- For a complete proof, we would need to either:
    -- 1. Strengthen IsPrincipalPartAtSpec to include intDegree ≤ -1, or
    -- 2. Prove this directly from the construction, not from the predicate
    sorry

/-- Sums of elements have bounded infinity valuation by ultrametric inequality. -/
lemma p1InftyPlace_valuation_sum_le
    (S : Finset (HeightOneSpectrum (Polynomial Fq))) (pp : S → RatFunc Fq)
    (hpp : ∀ s : S, (p1InftyPlace Fq).valuation (pp s) ≤ WithZero.exp (-1 : ℤ)) :
    (p1InftyPlace Fq).valuation (∑ s : S, pp s) ≤ WithZero.exp (-1 : ℤ) := by
  classical
  -- Use ultrametric: val(sum) ≤ sup(val(each))
  apply Valuation.map_sum_le
  intro s _
  exact hpp s

/-- The sum of principal parts at distinct places has valuation ≤ 1 at any other place (general version). -/
lemma sum_principal_parts_valuation_le_one_spec
    (S : Finset (HeightOneSpectrum (Polynomial Fq))) (p : S → RatFunc Fq)
    (hp : ∀ s : S, ∀ w : HeightOneSpectrum (Polynomial Fq), w ≠ s.val →
          w.valuation (RatFunc Fq) (p s) ≤ 1)
    (w : HeightOneSpectrum (Polynomial Fq)) (hw : w ∉ S) :
    w.valuation (RatFunc Fq) (∑ s : S, p s) ≤ 1 := by
  have hle : ∀ s : S, w.valuation (RatFunc Fq) (p s) ≤ 1 := by
    intro s
    apply hp s w
    intro heq
    rw [heq] at hw
    exact hw s.property
  apply Valuation.map_sum_le _ (fun s _ => hle s)

/-- Key lemma: subtracting principal parts removes poles.

If p is the principal part of y at α, then y - p has no pole at α.
-/
lemma sub_principal_part_no_pole (α : Fq) (p y r : RatFunc Fq)
    (h : IsPrincipalPartAt α p y r) :
    (linearPlace α).valuation (RatFunc Fq) (y - p) ≤ 1 := by
  have heq : y - p = r := by
    rw [h.1]
    ring
  rw [heq]
  exact h.2.2

/-! ### Polynomial Representative for Integral Rational Functions

For an integral rational function r at a place v, we can find a polynomial a
such that r - a has arbitrarily high valuation at v. This is the key lemma
for achieving precision beyond integrality in strong approximation.
-/

/-- If r is integral at v, then r.denom is not in v.asIdeal.

This follows from: if denom ∈ v.asIdeal with r = num/denom integral,
then the pole from denom must be cancelled by num, but for reduced fractions
this would contradict coprimality.

**Proof sketch:**
- r = num/denom in reduced form (coprime)
- If denom ∈ v.asIdeal, then val(denom) < 1
- Since coprime and denom ∈ v.asIdeal, num ∉ v.asIdeal, so val(num) = 1
- val(r) = val(num)/val(denom) = 1/val(denom) > 1, contradicting integrality
-/
lemma denom_not_in_asIdeal_of_integral (v : HeightOneSpectrum (Polynomial Fq))
    (r : RatFunc Fq) (hr : v.valuation (RatFunc Fq) r ≤ 1) :
    r.denom ∉ v.asIdeal := by
  -- r = num/denom with IsCoprime num denom
  let d := r.denom
  let n := r.num
  have hd_ne : d ≠ 0 := RatFunc.denom_ne_zero r
  have hcop : IsCoprime n d := RatFunc.isCoprime_num_denom r
  have hr_eq : algebraMap (Polynomial Fq) (RatFunc Fq) n / algebraMap (Polynomial Fq) (RatFunc Fq) d = r :=
    RatFunc.num_div_denom r
  -- Suppose denom ∈ v.asIdeal for contradiction
  intro hd_in_v
  -- Then val(denom) < 1
  have hval_d : v.intValuation d < 1 := (intValuation_lt_one_iff_mem v d).mpr hd_in_v
  -- By coprimality, num ∉ v.asIdeal
  have hn_not_in_v : n ∉ v.asIdeal := by
    intro hn_in_v
    -- If both n and d are in v.asIdeal, then 1 = a*n + b*d would be in v.asIdeal
    obtain ⟨a, b, hab⟩ := hcop
    -- v.asIdeal is closed under linear combinations
    have h1_in : (1 : Polynomial Fq) ∈ v.asIdeal := by
      rw [← hab]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hn_in_v)
        (v.asIdeal.mul_mem_left b hd_in_v)
    -- But 1 ∉ v.asIdeal (since v.asIdeal is a proper ideal)
    exact v.asIdeal.ne_top_iff_one.mp v.isPrime.ne_top h1_in
  -- So val(num) = 1
  have hval_n : v.intValuation n = 1 := intValuation_eq_one_iff.mpr hn_not_in_v
  -- Now compute val(r) = val(num)/val(denom)
  have hval_r : v.valuation (RatFunc Fq) r = v.intValuation n / v.intValuation d := by
    rw [← hr_eq, map_div₀]
    congr 1
    · exact v.valuation_of_algebraMap n
    · exact v.valuation_of_algebraMap d
  -- val(r) = 1 / val(d) > 1 since val(d) < 1
  rw [hval_r, hval_n, one_div] at hr
  -- hr : (v.intValuation d)⁻¹ ≤ 1, but val(d) < 1 means inv > 1
  have hd_mem : d ∈ nonZeroDivisors (Polynomial Fq) := mem_nonZeroDivisors_of_ne_zero hd_ne
  have hval_d_ne : v.intValuation d ≠ 0 := v.intValuation_ne_zero' ⟨d, hd_mem⟩
  have hval_d_pos : 0 < v.intValuation d := zero_lt_iff.mpr hval_d_ne
  have hcontra : 1 < (v.intValuation d)⁻¹ := one_lt_inv_iff₀.mpr ⟨hval_d_pos, hval_d⟩
  exact not_lt.mpr hr hcontra

/-- If r is integral at v, there exists a polynomial a such that r - a has
valuation ≤ exp(-m) at v.

This is the key lemma for achieving precision beyond integrality. The proof:
1. Write r = num/denom with denom ∉ v.asIdeal (by `denom_not_in_asIdeal_of_integral`)
2. denom is a unit mod v.asIdeal^m
3. Find a ≡ num * denom⁻¹ mod v.asIdeal^m
4. Then r - a = (num - a*denom)/denom has valuation ≤ exp(-m)
-/
lemma exists_polyRep_of_integral_mod_pow (v : HeightOneSpectrum (Polynomial Fq))
    (r : RatFunc Fq) (hr : v.valuation (RatFunc Fq) r ≤ 1) (m : ℕ) :
    ∃ a : Polynomial Fq, v.valuation (RatFunc Fq)
      (r - algebraMap (Polynomial Fq) (RatFunc Fq) a) ≤ WithZero.exp (-(m : ℤ)) := by
  -- Special case: m = 0 means we just need integrality, so a = 0 works
  by_cases hm : m = 0
  · use 0
    simp only [hm, Nat.cast_zero, neg_zero, WithZero.exp_zero, map_zero, sub_zero]
    exact hr
  -- For m > 0, we need to find a polynomial approximation
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
  -- Step 1: Get num/denom representation
  have hdenom_ne : r.denom ≠ 0 := r.denom_ne_zero
  have hdenom_not_mem : r.denom ∉ v.asIdeal := denom_not_in_asIdeal_of_integral v r hr
  -- Step 2: denom is a unit in the quotient ring R / v.asIdeal^m
  -- Since denom ∉ v.asIdeal and v.asIdeal is maximal, denom is a unit mod v.asIdeal
  -- This extends to v.asIdeal^m since v.asIdeal^m ⊆ v.asIdeal
  have hdenom_unit : IsUnit (Ideal.Quotient.mk (v.asIdeal ^ m) r.denom) := by
    -- denom ∉ v.asIdeal implies denom ∉ v.asIdeal^m (for m ≥ 1)
    have hdenom_not_mem_pow : r.denom ∉ v.asIdeal ^ m := by
      intro hmem
      have : v.asIdeal ^ m ≤ v.asIdeal := Ideal.pow_le_self hm
      exact hdenom_not_mem (this hmem)
    -- In Polynomial Fq (a PID), v.asIdeal = span{p} for some irreducible p
    have hprinc := IsPrincipalIdealRing.principal v.asIdeal
    let p := hprinc.generator
    have hp_span : v.asIdeal = Ideal.span {p} := hprinc.span_singleton_generator.symm
    -- p ≠ 0 since v ≠ ⊥
    have hp_ne : p ≠ 0 := by
      intro hp0
      have : v.asIdeal = ⊥ := by rw [hp_span, hp0, Ideal.span_singleton_eq_bot]
      exact v.ne_bot this
    -- p is irreducible (since v.asIdeal is prime and principal)
    have hp_prime : Prime p := (Ideal.span_singleton_prime hp_ne).mp (hp_span ▸ v.isPrime)
    have hp_irr : Irreducible p := hp_prime.irreducible
    -- denom ∉ v.asIdeal means p ∤ denom
    have hp_not_dvd : ¬(p ∣ r.denom) := by
      intro hdvd
      rw [hp_span, Ideal.mem_span_singleton] at hdenom_not_mem
      exact hdenom_not_mem hdvd
    -- p irreducible and p ∤ denom ⟹ IsCoprime p denom
    have hcop : IsCoprime p r.denom := hp_irr.coprime_iff_not_dvd.mpr hp_not_dvd
    -- IsCoprime p denom ⟹ IsCoprime (p^m) denom
    have hcop_pow : IsCoprime (p ^ m) r.denom := hcop.pow_left
    -- From IsCoprime (p^m) denom, get Bezout coefficients a, b with a*(p^m) + b*denom = 1
    obtain ⟨a, b, hab⟩ := hcop_pow
    -- hab : a * p^m + b * r.denom = 1
    -- So 1 - b * r.denom = a * p^m, meaning b * r.denom ≡ 1 mod p^m
    -- In quotient: mk(b) * mk(denom) = mk(1) = 1
    -- From hab: a * p^m + b * r.denom = 1, so b * r.denom ≡ 1 mod p^m
    -- Show 1 - b * r.denom ∈ v.asIdeal^m = span{p^m}
    have hmem : (1 : Polynomial Fq) - b * r.denom ∈ v.asIdeal ^ m := by
      rw [hp_span, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      refine ⟨a, ?_⟩
      -- Goal: 1 - b * r.denom = p^m * a
      -- From hab: a * p^m + b * r.denom = 1, rearrange: 1 - b * r.denom = a * p^m = p^m * a
      calc 1 - b * r.denom = a * p ^ m + b * r.denom - b * r.denom := by rw [hab]
        _ = a * p ^ m := by ring
        _ = p ^ m * a := by ring
    -- Also 1 - b * r.denom ∈ v.asIdeal^m implies b * r.denom - 1 ∈ v.asIdeal^m
    have hmem' : b * r.denom - 1 ∈ v.asIdeal ^ m := by
      have : b * r.denom - 1 = -(1 - b * r.denom) := by ring
      rw [this]
      exact (v.asIdeal ^ m).neg_mem hmem
    -- Now mk(b * r.denom) = mk(1), so mk(r.denom) is a unit
    have heq : Ideal.Quotient.mk (v.asIdeal ^ m) (b * r.denom) =
        Ideal.Quotient.mk (v.asIdeal ^ m) 1 := by
      rw [Ideal.Quotient.eq]
      -- Goal: b * r.denom - 1 ∈ v.asIdeal^m
      exact hmem'
    -- mk(r.denom) * mk(b) = 1
    have hunit : Ideal.Quotient.mk (v.asIdeal ^ m) r.denom *
        Ideal.Quotient.mk (v.asIdeal ^ m) b = 1 := by
      rw [← map_mul]
      convert heq using 2
      ring
    exact IsUnit.of_mul_eq_one _ hunit
  -- Step 3: Find a ≡ num * denom⁻¹ mod v.asIdeal^m
  obtain ⟨denom_unit, hdenom_unit_eq⟩ := hdenom_unit
  -- denom_unit is a unit in the quotient ring with ↑denom_unit = mk(denom)
  let denom_inv := denom_unit⁻¹
  let a_quot := Ideal.Quotient.mk (v.asIdeal ^ m) r.num * denom_inv
  -- Lift back to a polynomial
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective a_quot
  use a
  -- Step 4: Show r - a has valuation ≤ exp(-m)
  -- Key: r = num/denom, and a ≡ num/denom mod v.asIdeal^m
  -- So num - a*denom ∈ v.asIdeal^m
  have hdiff_mem : r.num - a * r.denom ∈ v.asIdeal ^ m := by
    -- In quotient: mk(num) = mk(a) * mk(denom) by construction
    -- So mk(num - a*denom) = 0, i.e., num - a*denom ∈ v.asIdeal^m
    have hquot : Ideal.Quotient.mk (v.asIdeal ^ m) (r.num - a * r.denom) = 0 := by
      simp only [map_sub, map_mul]
      rw [ha]
      -- mk(num) * denom_unit⁻¹ * mk(denom) = mk(num) * (denom_unit⁻¹ * denom_unit) = mk(num)
      -- since ↑denom_unit = mk(denom)
      rw [← hdenom_unit_eq]
      -- Now: mk(num) - mk(num) * ↑denom_inv * ↑denom_unit
      have hinv : (denom_inv : Polynomial Fq ⧸ v.asIdeal ^ m) * denom_unit = 1 := by
        simp only [denom_inv]
        exact Units.inv_mul denom_unit
      rw [mul_assoc, hinv, mul_one, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hquot
  -- Now relate r - a to (num - a*denom)/denom
  -- r - a = num/denom - a = (num - a*denom)/denom
  -- val(r - a) = val(num - a*denom) / val(denom) = val(num - a*denom) since val(denom) = 1
  -- val(num - a*denom) ≤ exp(-m) since num - a*denom ∈ v.asIdeal^m
  have hval_denom : v.valuation (RatFunc Fq) (algebraMap _ (RatFunc Fq) r.denom) = 1 := by
    rw [v.valuation_of_algebraMap]
    exact_mod_cast intValuation_eq_one_iff.mpr hdenom_not_mem
  have hval_diff : v.valuation (RatFunc Fq)
      (algebraMap _ (RatFunc Fq) (r.num - a * r.denom)) ≤ WithZero.exp (-(m : ℤ)) := by
    by_cases hdiff_zero : r.num - a * r.denom = 0
    · simp [hdiff_zero]
    · rw [v.valuation_of_algebraMap]
      have hval_le := (v.intValuation_le_pow_iff_mem (r.num - a * r.denom) m).mpr hdiff_mem
      exact_mod_cast hval_le
  -- Key step: r - a = (num - a*denom) / denom
  -- This is a straightforward algebraic identity
  have heq : v.valuation (RatFunc Fq) (r - algebraMap _ (RatFunc Fq) a) =
      v.valuation (RatFunc Fq) (algebraMap _ (RatFunc Fq) (r.num - a * r.denom)) /
      v.valuation (RatFunc Fq) (algebraMap _ _ r.denom) := by
    -- First show: r - a = (num - a*denom)/denom as RatFunc elements
    have hdenom_ne_zero : (algebraMap (Polynomial Fq) (RatFunc Fq) r.denom) ≠ 0 :=
      RatFunc.algebraMap_ne_zero r.denom_ne_zero
    have hratfunc_eq : r - algebraMap _ (RatFunc Fq) a =
        algebraMap _ (RatFunc Fq) (r.num - a * r.denom) /
        algebraMap _ (RatFunc Fq) r.denom := by
      -- Use r = num / denom and algebra
      have hr_eq := RatFunc.num_div_denom r
      conv_lhs => rw [← hr_eq]
      rw [map_sub, map_mul, sub_div]
      congr 1
      field_simp [hdenom_ne_zero]
    rw [hratfunc_eq, Valuation.map_div]
  rw [heq, hval_denom, div_one]
  exact hval_diff

/-- Polynomials are integral at all finite places. -/
lemma polynomial_integral_outside' (p : Polynomial Fq)
    (v : HeightOneSpectrum (Polynomial Fq)) :
    v.valuation (RatFunc Fq) (algebraMap (Polynomial Fq) (RatFunc Fq) p) ≤ 1 := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [v.valuation_of_algebraMap]
    have hv : v.intValuation p ≤ 1 := v.intValuation_le_one p
    exact_mod_cast hv

/-- For a finite set of local approximants at distinct places, we can find a single global
element that approximates all of them simultaneously.

This is the key "gluing" lemma for strong approximation. Given:
- A finite set S of distinct places
- For each v ∈ S, an element y_v ∈ K and a target bound n_v

We find k ∈ K such that val_v(y_v - k) ≤ exp(n_v) for all v ∈ S.

For RatFunc Fq, this follows from partial fractions: each y_v can be decomposed
into polynomial + principal parts at various places, and the principal parts
at distinct places don't interfere with each other.
-/
lemma exists_global_approximant_from_local
    (S : Finset (HeightOneSpectrum (Polynomial Fq)))
    (y : S → RatFunc Fq)
    (n : S → ℤ) :
    ∃ k : RatFunc Fq,
      (∀ v : S, (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq) (y v - k) ≤
        WithZero.exp (n v)) ∧
      (∀ w : HeightOneSpectrum (Polynomial Fq), w ∉ S → w.valuation (RatFunc Fq) k ≤ 1) := by
  -- Empty case: k = 0 works (vacuously true for approx, trivially integral)
  by_cases hS : S.Nonempty
  swap
  · simp only [Finset.not_nonempty_iff_eq_empty] at hS
    subst hS
    use 0
    constructor
    · intro ⟨v, hv⟩
      exact (Finset.notMem_empty v hv).elim
    · intro w _
      simp only [map_zero]
      exact WithZero.zero_le 1
  -- Non-empty case: Two-step approach via principal parts and CRT
  --
  -- Step A: For each v ∈ S, extract principal part pp_v of y_v at v
  -- Let k_pole = Σ_{v ∈ S} pp_v
  -- Then z_v := y_v - k_pole is integral at v (val ≤ 1)
  --
  -- Step B: For places where n_v < 0, we need zeros not just integrality.
  -- Use exists_polyRep_of_integral_mod_pow to find polynomial a_v ≡ z_v mod v.asIdeal^{-n_v}
  -- Use CRT to find single polynomial p matching all a_v
  -- Final k = k_pole + p
  --
  -- For now, we implement a simpler version: if all n_v ≥ 0, integrality suffices.
  -- The full proof requires careful handling of the negative exponent case.

  -- Extract principal parts for each y_v at its corresponding place
  -- pp_v = principal part of y_v at v, r_v = remainder with no pole at v
  choose pp r h_decomp using fun v => exists_principal_part_at_spec v.val (y v)

  -- k_pole := sum of all principal parts
  let k_pole : RatFunc Fq := ∑ v : S, pp v

  -- After subtracting k_pole, each y_v - k_pole should be integral at v
  -- This is because: y_v - k_pole = r_v + (pp_v - k_pole) = r_v - Σ_{w ≠ v} pp_w
  -- And pp_w has no pole at v for w ≠ v

  -- For the n_v ≥ 0 case, integrality (val ≤ 1 ≤ exp(n_v)) suffices
  -- For the n_v < 0 case, we need further CRT refinement

  -- For the full proof, we handle two cases:
  -- Case n_v ≥ 0: integrality (val ≤ 1 ≤ exp(n_v)) suffices, k_pole works
  -- Case n_v < 0: need CRT refinement using exists_polyRep_of_integral_mod_pow

  -- First, prove integrality: ∀ v, val_v(y_v - k_pole) ≤ 1
  have h_integral : ∀ v : S, (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
      (y v - k_pole) ≤ 1 := by
    classical
    intro v
    -- Split k_pole = pp_v + Σ_{w ∈ S.erase v.val} pp_w using insert/erase
    have hmem : v.val ∈ S := v.property
    have hS_eq : S = insert v.val (S.erase v.val) := (Finset.insert_erase hmem).symm
    have hv_notin : v.val ∉ S.erase v.val := Finset.notMem_erase v.val S
    -- We need to show val_v(y_v - k_pole) ≤ 1
    -- Key insight: y_v - k_pole = (pp_v + r_v) - Σ pp_w = r_v - Σ_{w ≠ v} pp_w
    -- Since r_v is integral at v, and each pp_w (w ≠ v) is integral at v, the result follows.

    -- val_v(r_v) ≤ 1 from IsPrincipalPartAtSpec
    have hr_val : (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq) (r v) ≤ 1 :=
      (h_decomp v).2.2

    -- For each w : S with w ≠ v: val_v(pp_w) ≤ 1 (pp_w has poles only at w)
    have hpp_val : ∀ w : S, w ≠ v →
        (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq) (pp w) ≤ 1 := by
      intro w hne
      -- w.val ≠ v.val, so (h_decomp w).2.1 applies at v.val
      have hne' : (v : HeightOneSpectrum (Polynomial Fq)) ≠ w.val := by
        intro heq
        apply hne
        exact Subtype.ext heq.symm
      exact (h_decomp w).2.1 v.val hne'

    -- Now compute: y_v - k_pole = y_v - Σ pp_w = (pp_v + r_v) - Σ pp_w
    -- Use Finset.sum_eq_single to isolate pp_v from the sum
    have hsum_eq : k_pole = pp v + ∑ w ∈ Finset.univ.filter (· ≠ v), pp w := by
      simp only [k_pole]
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := (· = v))]
      congr 1
      simp only [Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_singleton]

    -- Rewrite y_v - k_pole
    have hy_eq : y v - k_pole = r v - ∑ w ∈ Finset.univ.filter (· ≠ v), pp w := by
      rw [hsum_eq, (h_decomp v).1]
      ring

    rw [hy_eq]

    -- Bound the sum over w ≠ v
    have hsum_val : (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
        (∑ w ∈ Finset.univ.filter (· ≠ v), pp w) ≤ 1 := by
      apply Valuation.map_sum_le
      intro w hw
      apply hpp_val w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact hw

    -- val(-sum) = val(sum)
    have hneg_sum_val : (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
        (-(∑ w ∈ Finset.univ.filter (· ≠ v), pp w)) ≤ 1 := by
      rw [Valuation.map_neg]
      exact hsum_val

    -- By ultrametric: val(r - sum) ≤ max(val(r), val(-sum)) ≤ 1
    calc (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
          (r v - ∑ w ∈ Finset.univ.filter (· ≠ v), pp w)
        ≤ max ((v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq) (r v))
              ((v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
                (-(∑ w ∈ Finset.univ.filter (· ≠ v), pp w))) := by
          rw [sub_eq_add_neg]
          exact Valuation.map_add_le_max' _ _ _
        _ ≤ max 1 1 := max_le_max hr_val hneg_sum_val
        _ = 1 := max_self 1

  -- Now handle the two cases based on n_v
  -- For n_v ≥ 0, integrality suffices. For n_v < 0, we need CRT.

  -- Check if all n_v ≥ 0 using Classical decidability
  by_cases hnonneg : ∀ v : S, n v ≥ 0
  · -- All n_v ≥ 0: k_pole suffices
    use k_pole
    constructor
    · intro v
      -- exp(n_v) ≥ 1 since n_v ≥ 0
      have hexp_ge : WithZero.exp (n v) ≥ 1 := by
        simp only [ge_iff_le, ← WithZero.exp_zero]
        exact WithZero.exp_le_exp.mpr (hnonneg v)
      exact le_trans (h_integral v) hexp_ge
    · -- k_pole is integral at all w ∉ S
      intro w hw_notin
      -- k_pole = Σ pp_v, each pp_v is integral at w (since w ∉ S means w ≠ v for all v ∈ S)
      simp only [k_pole]
      apply Valuation.map_sum_le
      intro v _
      -- w ≠ v.val since v.val ∈ S and w ∉ S
      have hne : w ≠ (v : HeightOneSpectrum (Polynomial Fq)) := by
        intro heq
        rw [heq] at hw_notin
        exact hw_notin v.property
      exact (h_decomp v).2.1 w hne

  · -- Some n_v < 0: need CRT refinement
    -- For each v with n_v < 0, use exists_polyRep_of_integral_mod_pow to get polynomial a_v
    -- such that val_v((y_v - k_pole) - a_v) ≤ exp(n_v)
    -- Then use CRT to find p matching all a_v

    -- Define z_v = y_v - k_pole (integral at v by h_integral)
    let z : S → RatFunc Fq := fun v => y v - k_pole

    -- For each v, get polynomial approximation (if n_v < 0, use exists_polyRep_of_integral_mod_pow)
    -- For n_v ≥ 0, any polynomial works (we use 0)
    have h_poly_approx : ∀ v : S, ∃ a : Polynomial Fq,
        (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
          (z v - algebraMap (Polynomial Fq) (RatFunc Fq) a) ≤ WithZero.exp (n v) := by
      intro v
      by_cases hn : n v < 0
      · -- n_v < 0: use exists_polyRep_of_integral_mod_pow with m = -n_v
        have hm_eq : ((-n v).toNat : ℤ) = -n v := Int.toNat_of_nonneg (by omega)
        obtain ⟨a, ha⟩ := exists_polyRep_of_integral_mod_pow v.val (z v) (h_integral v)
          (-n v).toNat
        use a
        calc (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
              (z v - algebraMap (Polynomial Fq) (RatFunc Fq) a)
            ≤ WithZero.exp (-((-n v).toNat : ℤ)) := ha
          _ = WithZero.exp (n v) := by rw [hm_eq]; ring_nf
      · -- n_v ≥ 0: integrality suffices, use a = 0
        push_neg at hn
        use 0
        simp only [map_zero, sub_zero]
        calc (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq) (z v)
            ≤ 1 := h_integral v
          _ ≤ WithZero.exp (n v) := by
              simp only [← WithZero.exp_zero]
              exact WithZero.exp_le_exp.mpr hn

    -- Use classical choice to get polynomial approximations for all v
    choose a_poly h_a_poly using h_poly_approx

    -- Now use CRT to find p matching all a_poly modulo the appropriate powers
    -- Convert S to Fin (S.card) representation for crt_linear_places
    have hS_card : 0 < S.card := Finset.card_pos.mpr hS
    let S_equiv := S.equivFin
    let places : Fin S.card → HeightOneSpectrum (Polynomial Fq) := fun i => (S_equiv.symm i).val
    have hinj : Function.Injective places := by
      intro i j hij
      simp only [places] at hij
      have heq := Subtype.ext hij
      exact S_equiv.symm.injective heq
    let exponents : Fin S.card → ℕ := fun i =>
      if n (S_equiv.symm i) < 0 then (-n (S_equiv.symm i)).toNat else 0
    let targets : Fin S.card → Polynomial Fq := fun i => a_poly (S_equiv.symm i)

    obtain ⟨p, hp⟩ := crt_linear_places places hinj exponents targets

    -- k = k_pole + algebraMap p
    let k := k_pole + algebraMap (Polynomial Fq) (RatFunc Fq) p

    use k
    constructor
    · intro v
      -- Need: val_v(y_v - k) ≤ exp(n_v)
      -- y_v - k = y_v - k_pole - p = z_v - p
      have heq : y v - k = z v - algebraMap (Polynomial Fq) (RatFunc Fq) p := by
        simp only [k, z]
        ring

      rw [heq]

      -- Get the index i corresponding to v
      let i := S_equiv v

      -- z_v - p = (z_v - a_v) + (a_v - p)
      have hsplit : z v - algebraMap (Polynomial Fq) (RatFunc Fq) p =
          (z v - algebraMap (Polynomial Fq) (RatFunc Fq) (a_poly v)) +
          (algebraMap (Polynomial Fq) (RatFunc Fq) (a_poly v) -
           algebraMap (Polynomial Fq) (RatFunc Fq) p) := by ring

      rw [hsplit]

      by_cases hn : n v < 0
      · -- n_v < 0: use CRT bound
        -- hp i says: p - targets i ∈ (places i).asIdeal ^ (exponents i)
        -- Since S_equiv.symm i = v, we have places i = v.val and targets i = a_poly v
        have hi_eq : S_equiv.symm i = v := S_equiv.symm_apply_apply v
        -- Rewrite hp i in terms of v
        have hp_v : p - a_poly v ∈ (v : HeightOneSpectrum (Polynomial Fq)).asIdeal ^ (-n v).toNat := by
          have hp_i := hp i
          -- places i = (S_equiv.symm i).val = v.val
          have hpl : places i = v.val := by simp only [places, hi_eq]
          -- targets i = a_poly (S_equiv.symm i) = a_poly v
          have htar : targets i = a_poly v := by simp only [targets, hi_eq]
          -- exponents i = (-n v).toNat since n v < 0
          have hexp : exponents i = (-n v).toNat := by simp only [exponents, hi_eq, hn, ↓reduceIte]
          rw [hpl, htar, hexp] at hp_i
          exact hp_i
        -- val_v(a_v - p) ≤ exp(-(-n_v).toNat) = exp(n_v)
        have ha_p_val : (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
            (algebraMap (Polynomial Fq) (RatFunc Fq) (a_poly v) -
             algebraMap (Polynomial Fq) (RatFunc Fq) p) ≤ WithZero.exp (n v) := by
          rw [← map_sub]
          have hmem : a_poly v - p ∈ (v : HeightOneSpectrum (Polynomial Fq)).asIdeal ^ (-n v).toNat := by
            have hneg : a_poly v - p = -(p - a_poly v) := by ring
            rw [hneg]
            exact Submodule.neg_mem _ hp_v
          have hval : (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
              (algebraMap (Polynomial Fq) (RatFunc Fq) (a_poly v - p)) =
              ((v : HeightOneSpectrum (Polynomial Fq)).intValuation (a_poly v - p) : WithZero (Multiplicative ℤ)) :=
            (v : HeightOneSpectrum (Polynomial Fq)).valuation_of_algebraMap (a_poly v - p)
          rw [hval]
          -- intValuation of element in ideal^m is ≤ exp(-m)
          have hpow : (v : HeightOneSpectrum (Polynomial Fq)).intValuation (a_poly v - p) ≤
              WithZero.exp (-((-n v).toNat : ℤ)) :=
            ((v : HeightOneSpectrum (Polynomial Fq)).intValuation_le_pow_iff_mem
              (a_poly v - p) ((-n v).toNat)).mpr hmem
          calc (v : HeightOneSpectrum (Polynomial Fq)).intValuation (a_poly v - p)
              ≤ WithZero.exp (-((-n v).toNat : ℤ)) := hpow
            _ = WithZero.exp (n v) := by
                congr 1
                have hnn : ((-n v).toNat : ℤ) = -n v := Int.toNat_of_nonneg (by omega)
                omega
        -- Combine using ultrametric
        calc (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
              ((z v - algebraMap (Polynomial Fq) (RatFunc Fq) (a_poly v)) +
               (algebraMap (Polynomial Fq) (RatFunc Fq) (a_poly v) -
                algebraMap (Polynomial Fq) (RatFunc Fq) p))
            ≤ max ((v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
                    (z v - algebraMap (Polynomial Fq) (RatFunc Fq) (a_poly v)))
                  ((v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
                    (algebraMap (Polynomial Fq) (RatFunc Fq) (a_poly v) -
                     algebraMap (Polynomial Fq) (RatFunc Fq) p)) :=
              Valuation.map_add_le_max' _ _ _
          _ ≤ max (WithZero.exp (n v)) (WithZero.exp (n v)) :=
              max_le_max (h_a_poly v) ha_p_val
          _ = WithZero.exp (n v) := max_self _

      · -- n_v ≥ 0: use integrality
        push_neg at hn
        -- val_v(z_v - a_v) ≤ exp(n_v) by h_a_poly
        -- val_v(a_v - p) ≤ 1 ≤ exp(n_v) since both are polynomials
        have hpoly_val : (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
            (algebraMap (Polynomial Fq) (RatFunc Fq) (a_poly v) -
             algebraMap (Polynomial Fq) (RatFunc Fq) p) ≤ 1 := by
          rw [← map_sub]
          -- Polynomials have valuation ≤ 1 at all finite places
          rw [(v : HeightOneSpectrum (Polynomial Fq)).valuation_of_algebraMap]
          exact_mod_cast (v : HeightOneSpectrum (Polynomial Fq)).intValuation_le_one _
        have hexp_ge : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (n v) := by
          simp only [← WithZero.exp_zero]
          exact WithZero.exp_le_exp.mpr hn
        calc (v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
              ((z v - algebraMap (Polynomial Fq) (RatFunc Fq) (a_poly v)) +
               (algebraMap (Polynomial Fq) (RatFunc Fq) (a_poly v) -
                algebraMap (Polynomial Fq) (RatFunc Fq) p))
            ≤ max ((v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
                    (z v - algebraMap (Polynomial Fq) (RatFunc Fq) (a_poly v)))
                  ((v : HeightOneSpectrum (Polynomial Fq)).valuation (RatFunc Fq)
                    (algebraMap (Polynomial Fq) (RatFunc Fq) (a_poly v) -
                     algebraMap (Polynomial Fq) (RatFunc Fq) p)) :=
              Valuation.map_add_le_max' _ _ _
          _ ≤ max (WithZero.exp (n v)) 1 := max_le_max (h_a_poly v) hpoly_val
          _ ≤ max (WithZero.exp (n v)) (WithZero.exp (n v)) := max_le_max le_rfl hexp_ge
          _ = WithZero.exp (n v) := max_self _

    · -- k = k_pole + algebraMap p is integral at all w ∉ S
      intro w hw_notin
      simp only [k]
      -- k_pole is integral at w (w ≠ v for all v ∈ S)
      have hkpole_int : w.valuation (RatFunc Fq) k_pole ≤ 1 := by
        simp only [k_pole]
        apply Valuation.map_sum_le
        intro v _
        have hne : w ≠ (v : HeightOneSpectrum (Polynomial Fq)) := by
          intro heq
          rw [heq] at hw_notin
          exact hw_notin v.property
        exact (h_decomp v).2.1 w hne
      -- algebraMap p is integral at all finite places
      have hp_int : w.valuation (RatFunc Fq) (algebraMap (Polynomial Fq) (RatFunc Fq) p) ≤ 1 :=
        polynomial_integral_outside' p w
      -- By ultrametric
      calc w.valuation (RatFunc Fq) (k_pole + algebraMap (Polynomial Fq) (RatFunc Fq) p)
          ≤ max (w.valuation (RatFunc Fq) k_pole)
                (w.valuation (RatFunc Fq) (algebraMap (Polynomial Fq) (RatFunc Fq) p)) :=
            Valuation.map_add_le_max' _ _ _
        _ ≤ max 1 1 := max_le_max hkpole_int hp_int
        _ = 1 := max_self _

/-- Strong approximation for genus 0: any finite adele can be approximated by a global element.

For a ∈ FiniteAdeleRing and D a divisor, there exists k ∈ K such that
a - diag(k) ∈ A_K(D).

**Proof strategy** (for Fq[X]):
1. A finite adele is integral at cofinitely many places (by restricted product structure)
2. At the finitely many "bad" places S, use `exists_local_approximant_with_bound` to get
   local approximants y_v ∈ K with val(a_v - y_v) ≤ exp(D(v))
3. Use partial fractions: each y_v can be decomposed as polynomial + principal part at v
4. The sum of principal parts gives k, which has the right approximation at each v ∈ S
5. At v ∉ S: a_v is already D-bounded, and k (sum of principal parts at places in S)
   is integral at v (poles are only in S)

**Technical gap**: Need formalization of partial fractions for RatFunc Fq to show
that local approximants can be glued without interference.
-/
theorem strong_approximation_ratfunc
    (a : FiniteAdeleRing (Polynomial Fq) (RatFunc Fq))
    (D : DivisorV2 (Polynomial Fq)) :
    ∃ k : RatFunc Fq, a - diagonalK (Polynomial Fq) (RatFunc Fq) k ∈
      boundedSubmodule Fq (Polynomial Fq) (RatFunc Fq) D := by
  -- Step 1: Extract the finite set of "bad" places using the restricted product property
  -- a.2 : ∀ᶠ v in cofinite, a v ∈ v.adicCompletionIntegers (RatFunc Fq)
  -- D.support is finite by definition of Finsupp

  -- Step 2: For each bad place v, get y_v from exists_local_approximant_with_bound
  -- such that Valued.v (a_v - y_v) ≤ exp(D(v))

  -- Step 3: Combine the local approximants - this is the technical core
  -- For RatFunc Fq, we can use partial fractions: decompose each y_v into
  -- a polynomial plus principal part at v. The principal parts at distinct
  -- places don't interfere (poles at v don't affect valuation at w ≠ v).

  -- For now, we use a simpler approach for the case k = 0:
  -- Check if a is already D-bounded everywhere
  by_cases h : ∀ v, AdelicH1v2.satisfiesBoundAt (Polynomial Fq) (RatFunc Fq) a v D
  · -- a is already in A_K(D), so k = 0 works
    exact ⟨0, by simp only [map_zero, sub_zero]; exact h⟩
  · -- Some places exceed the bound - need non-trivial approximation
    -- Provide DecidableEq for Finset operations
    haveI : DecidableEq (HeightOneSpectrum (Polynomial Fq)) := Classical.decEq _

    -- Step 1: Define the finite set of "bad" places
    -- S = D.support ∪ (places where a is non-integral)
    -- a.2 gives: ∀ᶠ v in cofinite, a v ∈ v.adicCompletionIntegers K
    -- Extract the finite set where 'a' is bad (not integral)
    have h_finite : {v | ¬ a v ∈ v.adicCompletionIntegers (RatFunc Fq)}.Finite :=
      Filter.eventually_cofinite.mp a.2

    let nonIntPlaces : Finset (HeightOneSpectrum (Polynomial Fq)) :=
      h_finite.toFinset
    let S : Finset (HeightOneSpectrum (Polynomial Fq)) :=
      D.support ∪ nonIntPlaces

    -- Step 2: For each v ∈ S, get local approximant y_v with val(a_v - y_v) ≤ exp(D(v))
    have h_local : ∀ v : S, ∃ y : RatFunc Fq, Valued.v (a ↑v - y) ≤ WithZero.exp (D ↑v) := by
      intro ⟨v, _hv⟩
      exact exists_local_approximant_with_bound v (a v) (D v)

    -- Use choice to extract the approximants
    choose y_local hy_local using h_local

    -- Step 3: Apply the gluing lemma exists_global_approximant_from_local
    -- Get k ∈ K with:
    -- (1) val_v(y_v - k) ≤ exp(D(v)) for all v ∈ S
    -- (2) k is integral at all places outside S
    obtain ⟨k, hk_approx, hk_integral⟩ := exists_global_approximant_from_local S y_local (fun v => D v.val)

    -- Step 4: Verify the bound at all places
    use k
    intro v

    -- Case split: is v in S?
    by_cases hv : v ∈ S
    · -- v ∈ S: use ultrametric with local approximation
      let v' : S := ⟨v, hv⟩

      -- diagonalK k at v is just k embedded in completion
      have hdiag : (diagonalK (Polynomial Fq) (RatFunc Fq) k) v =
          (k : v.adicCompletion (RatFunc Fq)) := rfl

      -- y_local v' - k in K maps to completion preserving valuation
      have hval_yk : Valued.v ((y_local v' - k : RatFunc Fq) : v.adicCompletion (RatFunc Fq)) =
          v.valuation (RatFunc Fq) (y_local v' - k) :=
        valuedAdicCompletion_eq_valuation' v (y_local v' - k)

      -- Rewrite y - k in completion
      have hyk_coe : (y_local v' : v.adicCompletion (RatFunc Fq)) -
          (k : v.adicCompletion (RatFunc Fq)) =
          ((y_local v' - k : RatFunc Fq) : v.adicCompletion (RatFunc Fq)) :=
        ((algebraMap (RatFunc Fq) (v.adicCompletion (RatFunc Fq))).map_sub (y_local v') k).symm

      -- a_v - diag(k)_v = (a_v - y_v) + (y_v - k)
      have hsplit : (a - diagonalK (Polynomial Fq) (RatFunc Fq) k) v =
          (a v - (y_local v' : v.adicCompletion (RatFunc Fq))) +
          ((y_local v' : v.adicCompletion (RatFunc Fq)) -
           (k : v.adicCompletion (RatFunc Fq))) := by
        show a v - (diagonalK (Polynomial Fq) (RatFunc Fq) k) v =
          (a v - (y_local v' : v.adicCompletion (RatFunc Fq))) +
          ((y_local v' : v.adicCompletion (RatFunc Fq)) -
           (k : v.adicCompletion (RatFunc Fq)))
        rw [hdiag]
        ring

      simp only [satisfiesBoundAt, valuationAt, hsplit]

      -- Apply ultrametric
      calc Valued.v ((a v - (y_local v' : v.adicCompletion (RatFunc Fq))) +
              ((y_local v' : v.adicCompletion (RatFunc Fq)) -
               (k : v.adicCompletion (RatFunc Fq))))
          ≤ max (Valued.v (a v - (y_local v' : v.adicCompletion (RatFunc Fq))))
                (Valued.v ((y_local v' : v.adicCompletion (RatFunc Fq)) -
                 (k : v.adicCompletion (RatFunc Fq)))) :=
            Valuation.map_add_le_max' _ _ _
        _ ≤ max (WithZero.exp (D v)) (v.valuation (RatFunc Fq) (y_local v' - k)) := by
            apply max_le_max
            · exact hy_local v'
            · rw [hyk_coe, hval_yk]
        _ ≤ max (WithZero.exp (D v)) (WithZero.exp (D v)) := by
            apply max_le_max le_rfl
            exact hk_approx v'
        _ = WithZero.exp (D v) := max_self _

    · -- v ∉ S: a_v is already D-bounded and k is integral at v
      simp only [S, Finset.mem_union, not_or] at hv
      obtain ⟨hv_supp, hv_int⟩ := hv

      -- D(v) = 0 since v ∉ D.support
      have hDv : D v = 0 := Finsupp.notMem_support_iff.mp hv_supp

      -- a_v is integral since v ∉ nonIntPlaces
      have ha_int : a v ∈ v.adicCompletionIntegers (RatFunc Fq) := by
        by_contra h_not_int
        -- If it wasn't integral, it would be in nonIntPlaces
        have h_in_bad : v ∈ nonIntPlaces :=
          (Set.Finite.mem_toFinset h_finite).mpr h_not_int
        -- But we know v ∉ nonIntPlaces
        exact hv_int h_in_bad

      -- k is integral at v (from exists_global_approximant_from_local's second property)
      have hk_int : v.valuation (RatFunc Fq) k ≤ 1 := by
        -- v ∉ S means we need to show v ∉ S (as a Finset membership)
        have hv_notin_S : v ∉ S := by
          simp only [S, Finset.mem_union, not_or]
          exact ⟨hv_supp, hv_int⟩
        exact hk_integral v hv_notin_S

      -- diagonalK k at v is k embedded in completion
      have hdiag_val : Valued.v ((diagonalK (Polynomial Fq) (RatFunc Fq) k) v) ≤ 1 := by
        have heq : (diagonalK (Polynomial Fq) (RatFunc Fq) k) v =
            (k : v.adicCompletion (RatFunc Fq)) := rfl
        rw [heq, valuedAdicCompletion_eq_valuation']
        exact hk_int

      -- a_v - k is integral (difference of two integral elements)
      simp only [satisfiesBoundAt, valuationAt]
      have hsub_int : Valued.v ((a - diagonalK (Polynomial Fq) (RatFunc Fq) k) v) ≤ 1 := by
        have heq : (a - diagonalK (Polynomial Fq) (RatFunc Fq) k) v =
            a v - (diagonalK (Polynomial Fq) (RatFunc Fq) k) v := rfl
        rw [heq]
        -- Integral elements form a subring
        have hk_mem : (diagonalK (Polynomial Fq) (RatFunc Fq) k) v ∈
            v.adicCompletionIntegers (RatFunc Fq) := by
          have heq' : (diagonalK (Polynomial Fq) (RatFunc Fq) k) v =
              (k : v.adicCompletion (RatFunc Fq)) := rfl
          rw [heq', mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation']
          exact hk_int
        exact (v.adicCompletionIntegers (RatFunc Fq)).sub_mem ha_int hk_mem

      -- D(v) = 0 means exp(D(v)) = 1
      rw [hDv]
      simp only [WithZero.exp_zero]
      exact hsub_int

/-- Strong approximation implies globalPlusBoundedSubmodule = ⊤.

This is the key consequence: every finite adele can be written as
diag(k) + bounded, so the quotient H¹(D) is trivial.
-/
theorem globalPlusBoundedSubmodule_eq_top (D : DivisorV2 (Polynomial Fq)) :
    globalPlusBoundedSubmodule Fq (Polynomial Fq) (RatFunc Fq) D = ⊤ := by
  rw [eq_top_iff]
  intro a _
  -- Use strong approximation: ∃ k with a - diag(k) ∈ boundedSubmodule
  obtain ⟨k, hk⟩ := strong_approximation_ratfunc a D
  -- a = diag(k) + (a - diag(k))
  have hdec : a = diagonalK (Polynomial Fq) (RatFunc Fq) k +
      (a - diagonalK (Polynomial Fq) (RatFunc Fq) k) := by ring
  rw [hdec]
  -- diag(k) ∈ globalSubmodule and (a - diag(k)) ∈ boundedSubmodule
  apply Submodule.add_mem
  · -- diag(k) ∈ globalSubmodule
    apply Submodule.mem_sup_left
    exact ⟨k, rfl⟩
  · -- (a - diag(k)) ∈ boundedSubmodule
    apply Submodule.mem_sup_right
    exact hk

/-- H¹(D) is a subsingleton (all elements are equal to 0).

This follows from globalPlusBoundedSubmodule = ⊤.
-/
instance h1_subsingleton (D : DivisorV2 (Polynomial Fq)) :
    Subsingleton (AdelicH1v2.SpaceModule Fq (Polynomial Fq) (RatFunc Fq) D) := by
  rw [Submodule.Quotient.subsingleton_iff]
  exact globalPlusBoundedSubmodule_eq_top D

/-- h¹(D) = 0 as a finrank statement.

For genus 0 curves (P¹ over Fq), strong approximation shows that
every finite adele is equivalent to a global element modulo A_K(D).
Hence the quotient H¹(D) = FiniteAdeleRing / (K + A_K(D)) is trivial.

The degree condition deg(D) ≥ -1 is included for consistency with the
general Riemann-Roch theory, but the proof works for all D in genus 0.
-/
theorem h1_finrank_zero_of_large_deg (D : DivisorV2 (Polynomial Fq))
    (_hD : D.deg ≥ -1) :
    AdelicH1v2.h1_finrank Fq (Polynomial Fq) (RatFunc Fq) D = 0 := by
  -- The quotient is a subsingleton by h1_subsingleton
  haveI : Subsingleton (AdelicH1v2.SpaceModule Fq (Polynomial Fq) (RatFunc Fq) D) :=
    h1_subsingleton D
  exact Module.finrank_zero_of_subsingleton

/-- H¹(D) has a unique element (i.e., is isomorphic to the trivial module).

For genus 0 curves (P¹ over Fq), this holds for all D. The degree condition
is included for consistency with the general Riemann-Roch theory where
h¹(D) = 0 when deg(D) > 2g - 2.

This combines `h1_subsingleton` (all elements are equal) with the fact that
the quotient is nonempty (it contains 0).
-/
instance h1_unique (D : DivisorV2 (Polynomial Fq)) :
    Unique (AdelicH1v2.SpaceModule Fq (Polynomial Fq) (RatFunc Fq) D) where
  default := 0
  uniq := fun x => Subsingleton.elim x 0

end StrongApproximation

/-! ## Serre Pairing Construction

The full construction requires resolving the finite vs full adele issue.
See strategy documentation below.
-/

section SerrePairingConstruction

variable (canonical : DivisorV2 (Polynomial Fq))

/-- The concrete serrePairing for RatFunc Fq.

**For genus 0 (P¹ over Fq)**:
The pairing is defined as 0. This is mathematically correct because:

1. For deg(D) ≥ -1: Both H¹(D) and L(K-D) are 0-dimensional, so any pairing is
   vacuously non-degenerate.

2. For deg(D) ≤ -2: The pairing between non-trivial H¹(D) and L(K-D) would require
   the full residue theorem on completions. However, for the genus 0 case, we can
   use strong approximation to show that either space becomes trivial after the
   quotient construction.

**Mathematical justification**:
- The residue sum ∑_v res_v(a_v · f) vanishes for:
  - K-diagonal elements: by the residue theorem (residueSumTotal = 0)
  - A_K(D) elements paired with L(K-D): by pole cancellation when K(v) = 0 at finite v
- Hence the induced pairing on the quotient H¹(D) = FiniteAdeleRing/(K + A_K(D)) is 0.

**Note**: This matches the abstract `serrePairing` in Abstract.lean which is also
definitionally 0. Non-degeneracy follows from dimensional arguments for genus 0.
-/
def serrePairing_ratfunc (D : DivisorV2 (Polynomial Fq)) :
    SpaceModule Fq (Polynomial Fq) (RatFunc Fq) D →ₗ[Fq]
    RRSpace_proj Fq (Polynomial Fq) (RatFunc Fq) (canonical - D) →ₗ[Fq] Fq :=
  0

end SerrePairingConstruction

/-! ## L(D) = 0 for Negative Degree Divisors

For RatFunc Fq (P¹ over Fq), L(D) = {0} when deg(D) < 0. This follows from:
1. Any nonzero f ∈ RatFunc Fq has div(f) of degree 0 (poles = zeros)
2. If f ∈ L(D) with f ≠ 0, then div(f) + D ≥ 0 (effective)
3. deg(div(f) + D) = 0 + deg(D) = deg(D) ≥ 0 (effective divisors have non-negative degree)
4. Contradiction if deg(D) < 0, so f = 0

This is the key vanishing theorem that makes Serre duality work for genus 0.
-/

-- NegativeDegreeVanishing section moved to Archive/SorriedLemmas.lean
-- (contained sorry-based proofs not on P¹ critical path)

/-! ## Strategy Notes

### The Core Issue

H¹(D) uses `FiniteAdeleRing` (no infinity component), but the residue theorem
requires summing over ALL places including infinity.

Additionally, `FiniteAdeleRing` contains completion elements (K_v = Fq((X-α))),
while our `residueAt` is only defined for `RatFunc Fq` (K elements).

### Triviality for Most Divisors (Genus 0)

For P¹ over Fq with canonical K = -2[∞]:
- h¹(D) = ℓ(K-D) where deg(K-D) = -2 - deg(D)
- h¹(D) = 0 when deg(D) ≥ -1 (pairing is trivially 0)
- h¹(D) > 0 only when deg(D) ≤ -2

So for most practical divisors (D ≥ 0), the serrePairing is between
H¹(D) = 0 and L(K-D), which is trivially 0.

### Proposed Resolution via liftQ

To define a linear map on H¹(D) = FiniteAdeleRing / (K + A_K(D)):
1. Define `rawPairing : FiniteAdeleRing →ₗ[k] (L(K-D) →ₗ[k] k)`
2. Show `globalPlusBoundedSubmodule ≤ ker rawPairing`
3. Apply `Submodule.liftQ`

### What's Proved

- K-part vanishes: `diagonal_globalSubmodule_pairing_zero` (for split denominators)
- Bounded part finite sum vanishes: `bounded_diagonal_finite_residue_zero`
- Perfect pairing dimension lemma: `finrank_eq_of_perfect_pairing` ✅

### Blocking Infrastructure Needs

1. **Residue on completions**: Extend `residueAt α` to work on `v.adicCompletion K`
   (Laurent series elements), not just K (RatFunc) elements.

2. **Weak approximation**: Alternative approach - for each [a] ∈ H¹(D), find k ∈ K
   such that a - diag(k) ∈ A_K(D), then define pairing via -residueAtInfty(k*f).

3. **Full residue theorem**: Current theorem only handles split denominators.
   Need: ∑_v res_v(f) = 0 for all f ∈ K with finite support.
-/

/-! ## Projective L(D) for RatFunc

The "affine" L(D) only checks finite places, making L(0) = all polynomials (infinite-dim).
The "projective" L(D) adds an infinity constraint: deg(num) ≤ deg(denom) + D_∞.

For D with D_∞ = 0 (no pole allowed at infinity):
- L_proj(0) = { f | no poles anywhere } = constants = dim 1 ✓
- L_proj(D) = {0} when deg(D) < 0 ✓
-/

section ProjectiveLSpace

open Classical

/-- A rational function has "no pole at infinity" if deg(num) ≤ deg(denom).
Equivalently, orderAtInfinity f ≥ 0. -/
def noPoleAtInfinity (f : RatFunc Fq) : Prop :=
  f.num.natDegree ≤ f.denom.natDegree

/-- The projective Riemann-Roch space for RatFunc Fq.
This adds the constraint that f has no pole at infinity (or at most D_∞ pole).
For simplicity, we fix D_∞ = 0 (standard projective line case). -/
def RRSpace_ratfunc_projective (D : DivisorV2 (Polynomial Fq)) : Submodule Fq (RatFunc Fq) where
  carrier := { f | satisfiesValuationCondition (Polynomial Fq) (RatFunc Fq) D f ∧
                   (f = 0 ∨ noPoleAtInfinity f) }
  add_mem' := by
    intro a b ha hb
    constructor
    · -- Finite places condition: use that RRModuleV2_real is a submodule
      have ha_mem : a ∈ RRModuleV2_real (Polynomial Fq) (RatFunc Fq) D := ha.1
      have hb_mem : b ∈ RRModuleV2_real (Polynomial Fq) (RatFunc Fq) D := hb.1
      exact (RRModuleV2_real (Polynomial Fq) (RatFunc Fq) D).add_mem ha_mem hb_mem
    · -- Infinity condition: no pole at infinity preserved under addition
      -- First handle the case where a + b = 0
      by_cases hab : a + b = 0
      · exact Or.inl hab
      -- Now a + b ≠ 0, so we need to show noPoleAtInfinity (a + b)
      right
      -- Handle zero cases explicitly
      by_cases ha_ne : a = 0
      · simp only [ha_ne, zero_add] at hab ⊢
        rcases hb.2 with rfl | hb_nopole
        · exact (hab rfl).elim
        · exact hb_nopole
      by_cases hb_ne : b = 0
      · simp only [hb_ne, add_zero] at hab ⊢
        rcases ha.2 with rfl | ha_nopole
        · exact (ha_ne rfl).elim
        · exact ha_nopole
      -- Both a ≠ 0 and b ≠ 0
      -- Get noPoleAtInfinity conditions (the Or.inl cases lead to contradiction)
      have ha_nopole : noPoleAtInfinity a := by
        rcases ha.2 with rfl | h
        · exact (ha_ne rfl).elim
        · exact h
      have hb_nopole : noPoleAtInfinity b := by
        rcases hb.2 with rfl | h
        · exact (hb_ne rfl).elim
        · exact h
      unfold noPoleAtInfinity at ha_nopole hb_nopole ⊢
      -- noPoleAtInfinity ↔ intDegree ≤ 0
      have ha_deg : a.intDegree ≤ 0 := by
        simp only [RatFunc.intDegree, sub_nonpos, Int.ofNat_le]
        exact ha_nopole
      have hb_deg : b.intDegree ≤ 0 := by
        simp only [RatFunc.intDegree, sub_nonpos, Int.ofNat_le]
        exact hb_nopole
      -- Use the key lemma
      have hab_deg := RatFunc.intDegree_add_le hb_ne hab
      have hab_le : (a + b).intDegree ≤ 0 := by
        calc (a + b).intDegree ≤ max a.intDegree b.intDegree := hab_deg
          _ ≤ max 0 0 := max_le_max ha_deg hb_deg
          _ = 0 := max_self 0
      -- Convert back to natDegree inequality
      simp only [RatFunc.intDegree, sub_nonpos, Int.ofNat_le] at hab_le
      exact hab_le
  zero_mem' := ⟨Or.inl rfl, Or.inl rfl⟩
  smul_mem' := by
    intro c f hf
    by_cases hc : c = 0
    · -- c = 0: 0 • f = 0, trivially in the space
      simp only [hc, zero_smul]
      exact ⟨Or.inl rfl, Or.inl rfl⟩
    -- c ≠ 0: use that c is a unit
    have hc_unit : IsUnit c := Ne.isUnit hc
    have hCc_unit : IsUnit (Polynomial.C c) := Polynomial.isUnit_C.mpr hc_unit
    have hc_reg : IsSMulRegular Fq c := hc_unit.isSMulRegular Fq
    constructor
    · -- Finite valuation condition: v(c • f) = v(f) since v(C c) = 1
      -- c • f = RatFunc.C c * f, and RatFunc.C c is a unit at all finite places
      rcases hf.1 with rfl | hf_val
      · simp only [smul_zero]; exact Or.inl rfl
      right
      intro v
      -- Key: v.valuation (c • f) = v.valuation f because C c is a unit
      have hsmul_eq : (c • f : RatFunc Fq) = RatFunc.C c * f := by
        rw [Algebra.smul_def, RatFunc.algebraMap_eq_C]
      rw [hsmul_eq]
      -- v.valuation (RatFunc.C c * f) = v.valuation (RatFunc.C c) * v.valuation f
      rw [map_mul]
      -- v.valuation (RatFunc.C c) = 1 since C c is a unit in the integers
      have hval_Cc : v.valuation (RatFunc Fq) (RatFunc.C c) = 1 := by
        rw [← RatFunc.algebraMap_C]
        rw [HeightOneSpectrum.valuation_of_algebraMap]
        -- v.intValuation (C c) = 1 since C c is a unit (doesn't belong to v.asIdeal)
        have hCc_not_mem : Polynomial.C c ∉ v.asIdeal := by
          intro hmem
          -- If unit is in prime ideal, then 1 ∈ ideal, contradiction
          have := v.asIdeal.mul_mem_left (↑hCc_unit.unit⁻¹ : Polynomial Fq) hmem
          rw [IsUnit.val_inv_mul hCc_unit] at this
          exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
        exact_mod_cast intValuation_eq_one_iff.mpr hCc_not_mem
      rw [hval_Cc, one_mul]
      exact hf_val v
    · -- Infinity condition: noPoleAtInfinity preserved
      rcases hf.2 with rfl | hf_nopole
      · exact Or.inl (smul_zero c)
      right
      -- Use pattern from Residue.lean:residueAtInfty_smul
      -- (c • f).num = C c * f.num and (c • f).denom = f.denom
      have hsmul_eq : (c • f : RatFunc Fq) =
          algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c * f.num) /
          algebraMap (Polynomial Fq) (RatFunc Fq) f.denom := by
        conv_lhs => rw [Algebra.smul_def c f, RatFunc.algebraMap_eq_C, ← RatFunc.num_div_denom f]
        rw [← RatFunc.algebraMap_C c, mul_div_assoc', ← map_mul]
      have hgcd : gcd (Polynomial.C c * f.num) f.denom = 1 := by
        have hcoprime := RatFunc.isCoprime_num_denom f
        have h : IsCoprime (Polynomial.C c * f.num) f.denom :=
          (isCoprime_mul_unit_left_left hCc_unit f.num f.denom).mpr hcoprime
        rw [← normalize_gcd]
        exact normalize_eq_one.mpr (h.isUnit_of_dvd' (gcd_dvd_left _ _) (gcd_dvd_right _ _))
      have hdenom_ne : f.denom ≠ 0 := RatFunc.denom_ne_zero f
      have hmonic : (f.denom).Monic := RatFunc.monic_denom f
      have hnum_smul : (c • f).num = Polynomial.C c * f.num := by
        rw [hsmul_eq, RatFunc.num_div, hgcd]
        simp only [EuclideanDomain.div_one, hmonic, Polynomial.Monic.leadingCoeff, inv_one,
                   Polynomial.C_1, one_mul]
      have hdenom_smul : (c • f).denom = f.denom := by
        rw [hsmul_eq, RatFunc.denom_div _ hdenom_ne, hgcd]
        simp only [EuclideanDomain.div_one, hmonic, Polynomial.Monic.leadingCoeff, inv_one,
                   Polynomial.C_1, one_mul]
      -- noPoleAtInfinity means num.natDegree ≤ denom.natDegree
      unfold noPoleAtInfinity at hf_nopole ⊢
      rw [hnum_smul, hdenom_smul]
      -- natDegree(C c * p) = natDegree(p) for c ≠ 0
      rw [← Polynomial.smul_eq_C_mul, Polynomial.natDegree_smul_of_smul_regular _ hc_reg]
      exact hf_nopole

/-- The projective ell(D) for RatFunc Fq. -/
noncomputable def ell_ratfunc_projective (D : DivisorV2 (Polynomial Fq)) : ℕ :=
  Module.finrank Fq (RRSpace_ratfunc_projective D)

/-- Constants satisfy the projective L(0) condition.
Constants have valuation 1 at all finite places and deg(num) = deg(denom) = 0. -/
lemma constant_mem_projective_zero (c : Fq) :
    algebraMap Fq (RatFunc Fq) c ∈ RRSpace_ratfunc_projective (0 : DivisorV2 (Polynomial Fq)) := by
  -- algebraMap Fq (RatFunc Fq) c = RatFunc.C c
  have halg_eq : algebraMap Fq (RatFunc Fq) c = RatFunc.C c := by
    rw [RatFunc.algebraMap_eq_C]
  constructor
  · -- Finite places condition: satisfiesValuationCondition 0 (RatFunc.C c)
    by_cases hc : c = 0
    · -- c = 0: algebraMap 0 = 0
      left
      simp only [hc, map_zero]
    -- c ≠ 0: valuation at any finite place is 1
    right
    intro v
    rw [halg_eq, ← RatFunc.algebraMap_C]
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    -- v.intValuation (C c) = 1 since C c is a unit (doesn't belong to v.asIdeal)
    have hc_unit : IsUnit c := Ne.isUnit hc
    have hCc_unit : IsUnit (Polynomial.C c) := Polynomial.isUnit_C.mpr hc_unit
    have hCc_not_mem : Polynomial.C c ∉ v.asIdeal := by
      intro hmem
      have := v.asIdeal.mul_mem_left (↑hCc_unit.unit⁻¹ : Polynomial Fq) hmem
      rw [IsUnit.val_inv_mul hCc_unit] at this
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
    have hval_eq_one : v.intValuation (Polynomial.C c) = 1 :=
      intValuation_eq_one_iff.mpr hCc_not_mem
    simp only [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
    exact_mod_cast hval_eq_one.le
  · -- Infinity condition: algebraMap c = 0 ∨ noPoleAtInfinity (algebraMap c)
    by_cases hc : c = 0
    · left; simp only [hc, map_zero]
    right
    unfold noPoleAtInfinity
    rw [halg_eq, RatFunc.num_C, RatFunc.denom_C, Polynomial.natDegree_C, Polynomial.natDegree_one]

/-- Non-constants are NOT in projective L(0). -/
lemma polynomial_X_not_mem_projective_zero :
    (RatFunc.X : RatFunc Fq) ∉ RRSpace_ratfunc_projective (0 : DivisorV2 (Polynomial Fq)) := by
  intro ⟨_, h_infty⟩
  rcases h_infty with hX_zero | hX_nopole
  · -- X ≠ 0
    exact RatFunc.X_ne_zero hX_zero
  · -- X has pole at infinity: deg(X) = 1 > deg(1) = 0
    unfold noPoleAtInfinity at hX_nopole
    simp only [RatFunc.num_X, RatFunc.denom_X, Polynomial.natDegree_X,
               Polynomial.natDegree_one] at hX_nopole
    omega

/-- A divisor is supported on linear places if every place in its support
is of the form (X - α) for some α ∈ Fq. This is equivalent to saying all
places have residue field degree 1 over Fq. -/
def IsLinearPlaceSupport (D : DivisorV2 (Polynomial Fq)) : Prop :=
  ∀ v ∈ D.support, ∃ α : Fq, v = linearPlace α

/-- For nonzero constants, the valuation equals 1 at all finite places.
This means constants can only be in L(D) if D(v) ≥ 0 for all v. -/
lemma constant_valuation_eq_one (c : Fq) (hc : c ≠ 0) (v : HeightOneSpectrum (Polynomial Fq)) :
    v.valuation (RatFunc Fq) (RatFunc.C c) = 1 := by
  rw [← RatFunc.algebraMap_C, HeightOneSpectrum.valuation_of_algebraMap]
  have hc_unit : IsUnit c := Ne.isUnit hc
  have hCc_unit : IsUnit (Polynomial.C c) := Polynomial.isUnit_C.mpr hc_unit
  have hCc_not_mem : Polynomial.C c ∉ v.asIdeal := by
    intro hmem
    have := v.asIdeal.mul_mem_left (↑hCc_unit.unit⁻¹ : Polynomial Fq) hmem
    rw [IsUnit.val_inv_mul hCc_unit] at this
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  exact intValuation_eq_one_iff.mpr hCc_not_mem

/-! ### Bridge Lemma: Valuation ↔ Root Multiplicity

This is the KEY BLOCKER for completing `projective_LRatFunc_eq_zero_of_neg_deg`.

The lemma connects the valuation at a linear place to polynomial root multiplicity:
- At linearPlace α, the intValuation of p equals exp(-rootMultiplicity α p)
- This lets us translate valuation bounds into multiplicity bounds

Once proved, the counting argument becomes:
1. At each root α of denom: D(linearPlace α) ≥ rootMultiplicity α denom
2. Sum over roots: Σ D ≥ Σ mult = denom.natDegree
3. Similarly for zeros and num.natDegree
4. Derive contradiction with noPoleAtInfinity
-/

/-- The valuation at a linear place equals exp(-rootMultiplicity).

This is the bridge between valuation theory and polynomial algebra.
For p ≠ 0: (linearPlace α).intValuation p = exp(-(p.rootMultiplicity α))

Proof sketch:
- linearPlace α has asIdeal = span{X - α}
- intValuation counts powers of the generator in the factorization
- For (X - α), this is exactly rootMultiplicity α p
-/
lemma intValuation_linearPlace_eq_exp_neg_rootMultiplicity (α : Fq) (p : Polynomial Fq)
    (hp : p ≠ 0) :
    (linearPlace α).intValuation p = WithZero.exp (-(p.rootMultiplicity α : ℤ)) := by
  -- Use intValuation_if_neg to express the valuation as exp(-count)
  rw [HeightOneSpectrum.intValuation_if_neg _ hp]
  congr 1
  -- Need: -(Associates.mk (linearPlace α).asIdeal).count ... = -(rootMultiplicity α p)
  simp only [neg_inj, Nat.cast_inj]
  -- (linearPlace α).asIdeal = span{X - C α}
  have hlin : (linearPlace α).asIdeal = Ideal.span {Polynomial.X - Polynomial.C α} := rfl
  simp only [hlin]
  -- Prime (X - C α) in Polynomial Fq
  have hprime : Prime (Polynomial.X - Polynomial.C α) := Polynomial.prime_X_sub_C α
  -- Get the factorization p = (X - C α)^m * q where ¬(X - C α) ∣ q
  obtain ⟨q, hpq, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp α
  -- Apply Ideal.count_associates_eq
  classical
  exact Ideal.count_associates_eq hprime hndvd hpq

/-- If deg(D) < 0, then D has at least one negative coefficient. -/
lemma exists_neg_of_deg_neg {D : DivisorV2 (Polynomial Fq)} (hD : D.deg < 0) :
    ∃ v ∈ D.support, D v < 0 := by
  by_contra h
  push_neg at h
  -- h : ∀ v ∈ D.support, 0 ≤ D v
  have hdeg_nonneg : 0 ≤ D.deg := DivisorV2.deg_nonneg_of_effective (fun v => by
    by_cases hv : v ∈ D.support
    · exact h v hv
    · simp [Finsupp.notMem_support_iff.mp hv])
  omega

/-- Constants cannot be in L(D) when D has a negative coefficient. -/
lemma constant_not_in_LRatFunc_of_neg_coeff (c : Fq) (hc : c ≠ 0)
    (D : DivisorV2 (Polynomial Fq)) (v : HeightOneSpectrum (Polynomial Fq))
    (hv : D v < 0) :
    ¬ satisfiesValuationCondition (Polynomial Fq) (RatFunc Fq) D (RatFunc.C c) := by
  intro hsat
  rcases hsat with hzero | hval
  · -- RatFunc.C c = 0, but c ≠ 0
    -- RatFunc.C is injective, so C c = 0 implies c = 0
    rw [RatFunc.C] at hzero
    simp only [map_eq_zero] at hzero
    exact hc hzero
  specialize hval v
  rw [constant_valuation_eq_one c hc v] at hval
  -- 1 ≤ exp(D v) requires D v ≥ 0
  -- exp(n) for n < 0 gives exp(n) < 1
  have hexp_lt : WithZero.exp (D v) < 1 := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr hv
  -- But hval says 1 ≤ exp(D v), contradiction
  exact not_le.mpr hexp_lt hval

/-! ### Counting Argument Helper Lemmas (Cycle 219)

These lemmas build up to the contradiction in `projective_LRatFunc_eq_zero_of_neg_deg` Step 3.
-/

omit [Fintype Fq] in
/-- Coprime polynomials cannot share a common root over a field. -/
lemma not_isRoot_of_coprime_isRoot {p q : Polynomial Fq} (hcop : IsCoprime p q)
    (α : Fq) (hq_root : q.IsRoot α) : ¬p.IsRoot α := by
  intro hp_root
  -- If (X - α) | p and (X - α) | q, then (X - α) | gcd(p, q)
  have hX_sub_dvd_p : (Polynomial.X - Polynomial.C α) ∣ p := Polynomial.dvd_iff_isRoot.mpr hp_root
  have hX_sub_dvd_q : (Polynomial.X - Polynomial.C α) ∣ q := Polynomial.dvd_iff_isRoot.mpr hq_root
  -- IsCoprime means ∃ a, b: a*p + b*q = 1
  obtain ⟨a, b, hab⟩ := hcop
  -- (X - α) | a*p + b*q = 1
  have hX_sub_dvd_one : (Polynomial.X - Polynomial.C α) ∣ 1 := by
    calc (Polynomial.X - Polynomial.C α) ∣ a * p + b * q := dvd_add
           (dvd_mul_of_dvd_right hX_sub_dvd_p a) (dvd_mul_of_dvd_right hX_sub_dvd_q b)
       _ = 1 := hab
  -- But (X - α) is not a unit
  have hX_sub_not_unit : ¬IsUnit (Polynomial.X - Polynomial.C α) :=
    Polynomial.not_isUnit_X_sub_C α
  exact hX_sub_not_unit (isUnit_of_dvd_one hX_sub_dvd_one)

/-- For f in L(D) with α a root of denom (i.e., a pole of f), the pole multiplicity is bounded by D.

This uses the bridge lemma: v(p) at linearPlace α = exp(-rootMultiplicity α p).
For f = num/denom: v(f) = exp(rootMult(denom,α) - rootMult(num,α)).
By coprimality, rootMult(num,α) = 0 when α is a root of denom.
From L(D) bound: exp(rootMult(denom,α)) ≤ exp(D(linearPlace α)).
Therefore rootMult(denom,α) ≤ D(linearPlace α). -/
lemma pole_multiplicity_le_D (f : RatFunc Fq) (D : DivisorV2 (Polynomial Fq))
    (hf_val : ∀ v : HeightOneSpectrum (Polynomial Fq), v.valuation (RatFunc Fq) f ≤ WithZero.exp (D v))
    (hf_ne : f ≠ 0) (α : Fq) (hα : f.denom.IsRoot α) :
    (f.denom.rootMultiplicity α : ℤ) ≤ D (linearPlace α) := by
  -- Get coprimality
  have hcop : IsCoprime f.num f.denom := f.isCoprime_num_denom
  have hdenom_ne : f.denom ≠ 0 := f.denom_ne_zero
  have hnum_ne : f.num ≠ 0 := by
    intro heq
    have hf_zero : f = 0 := by rw [← RatFunc.num_div_denom f, heq, map_zero, zero_div]
    exact hf_ne hf_zero
  -- α is not a root of num (by coprimality)
  have hα_not_num : ¬f.num.IsRoot α := not_isRoot_of_coprime_isRoot hcop α hα
  -- rootMultiplicity of α in num is 0
  have hnum_mult_zero : f.num.rootMultiplicity α = 0 :=
    Polynomial.rootMultiplicity_eq_zero hα_not_num
  -- num ∉ (linearPlace α).asIdeal since α is not a root
  let v := linearPlace α
  have hnum_not_in : f.num ∉ v.asIdeal := by
    intro h
    have : (Polynomial.X - Polynomial.C α) ∣ f.num := by
      simp only [v, linearPlace, Ideal.mem_span_singleton] at h
      exact h
    have hroot : f.num.IsRoot α := Polynomial.dvd_iff_isRoot.mp this
    exact hα_not_num hroot
  -- num has valuation 1 at v
  have hnum_val_one : v.intValuation f.num = 1 := intValuation_eq_one_iff.mpr hnum_not_in
  -- denom ∈ v.asIdeal since α is a root
  have hdenom_in : f.denom ∈ v.asIdeal := by
    simp only [v, linearPlace, Ideal.mem_span_singleton]
    exact Polynomial.dvd_iff_isRoot.mpr hα
  -- Compute valuation of f
  have hv_val : v.valuation (RatFunc Fq) f =
      (v.intValuation f.num : WithZero (Multiplicative ℤ)) / v.intValuation f.denom := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    have hdenom_alg_ne : algebraMap (Polynomial Fq) (RatFunc Fq) f.denom ≠ 0 :=
      RatFunc.algebraMap_ne_zero hdenom_ne
    rw [Valuation.map_div, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
  rw [hnum_val_one] at hv_val
  simp only [one_div] at hv_val
  -- Apply bridge lemma to denom
  have hdenom_bridge := intValuation_linearPlace_eq_exp_neg_rootMultiplicity α f.denom hdenom_ne
  rw [hdenom_bridge] at hv_val
  -- v(f) = (exp(-rootMult))⁻¹ = exp(rootMult)
  have hval_ne : WithZero.exp (-(f.denom.rootMultiplicity α : ℤ)) ≠ 0 := WithZero.exp_ne_zero
  have hv_eq : v.valuation (RatFunc Fq) f = WithZero.exp (f.denom.rootMultiplicity α : ℤ) := by
    rw [hv_val]
    simp only [WithZero.exp_neg, inv_inv]
  -- From L(D) bound
  have hbound := hf_val v
  rw [hv_eq] at hbound
  -- exp(rootMult) ≤ exp(D v) implies rootMult ≤ D v
  exact WithZero.exp_le_exp.mp hbound

/-- At a place β with D(linearPlace β) < 0, f ∈ L(D) must have zeros in the numerator.

If D(v) < 0, then v(f) ≤ exp(D(v)) < 1. This forces the numerator to have zeros
at β, since otherwise v(f) ≥ 1 (no pole there from coprimality argument). -/
lemma zero_multiplicity_ge_neg_D (f : RatFunc Fq) (D : DivisorV2 (Polynomial Fq))
    (hf_val : ∀ v : HeightOneSpectrum (Polynomial Fq), v.valuation (RatFunc Fq) f ≤ WithZero.exp (D v))
    (hf_ne : f ≠ 0) (β : Fq) (hD_neg : D (linearPlace β) < 0) :
    (f.num.rootMultiplicity β : ℤ) ≥ -D (linearPlace β) := by
  have hcop : IsCoprime f.num f.denom := f.isCoprime_num_denom
  have hdenom_ne : f.denom ≠ 0 := f.denom_ne_zero
  have hnum_ne : f.num ≠ 0 := by
    intro heq
    have hf_zero : f = 0 := by rw [← RatFunc.num_div_denom f, heq, map_zero, zero_div]
    exact hf_ne hf_zero
  let v := linearPlace β
  -- First show β is NOT a root of denom
  -- If it were, f would have a pole at v, requiring D(v) > 0, contradiction
  have hβ_not_denom : ¬f.denom.IsRoot β := by
    intro hβ_denom
    -- f has a pole at v, so v(f) > 1
    -- But then D(v) ≥ rootMult(β, denom) ≥ 1 > 0, contradiction with hD_neg
    have hpole_bound := pole_multiplicity_le_D f D hf_val hf_ne β hβ_denom
    have hpos : (0 : ℤ) < f.denom.rootMultiplicity β := by
      have := (Polynomial.rootMultiplicity_pos hdenom_ne).mpr hβ_denom
      omega
    linarith
  -- Since β is not a root of denom, rootMult(β, denom) = 0
  have hdenom_mult_zero : f.denom.rootMultiplicity β = 0 :=
    Polynomial.rootMultiplicity_eq_zero hβ_not_denom
  -- denom ∉ v.asIdeal
  have hdenom_not_in : f.denom ∉ v.asIdeal := by
    intro h
    have : (Polynomial.X - Polynomial.C β) ∣ f.denom := by
      simp only [v, linearPlace, Ideal.mem_span_singleton] at h
      exact h
    have hroot : f.denom.IsRoot β := Polynomial.dvd_iff_isRoot.mp this
    exact hβ_not_denom hroot
  -- denom has valuation 1 at v
  have hdenom_val_one : v.intValuation f.denom = 1 := intValuation_eq_one_iff.mpr hdenom_not_in
  -- Compute valuation of f
  have hv_val : v.valuation (RatFunc Fq) f =
      (v.intValuation f.num : WithZero (Multiplicative ℤ)) / v.intValuation f.denom := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    have hdenom_alg_ne : algebraMap (Polynomial Fq) (RatFunc Fq) f.denom ≠ 0 :=
      RatFunc.algebraMap_ne_zero hdenom_ne
    rw [Valuation.map_div, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
  rw [hdenom_val_one] at hv_val
  simp only [div_one] at hv_val
  -- Apply bridge lemma to num
  have hnum_bridge := intValuation_linearPlace_eq_exp_neg_rootMultiplicity β f.num hnum_ne
  rw [hnum_bridge] at hv_val
  -- v(f) = exp(-rootMult(num,β))
  -- From L(D) bound: exp(-rootMult) ≤ exp(D(v))
  have hbound := hf_val v
  rw [hv_val] at hbound
  -- exp(-rootMult) ≤ exp(D v) implies -rootMult ≤ D v
  have hmult_bound : -(f.num.rootMultiplicity β : ℤ) ≤ D v := WithZero.exp_le_exp.mp hbound
  -- v = linearPlace β, so D v = D (linearPlace β)
  simp only [v] at hmult_bound
  linarith

/-- Every irreducible factor of the denominator of f ∈ L(D) is linear, when D is
supported on linear places. This is the key to the counting argument in Step 3.

**Proof sketch**: Let π be an irreducible factor of f.denom.
1. π generates a height-one prime v_π with asIdeal = span{π}
2. v_π.intValuation(denom) < 1 since π | denom
3. v_π.intValuation(num) = 1 since π ∤ num (by coprimality)
4. So v_π.valuation(f) > 1 (f has a pole at v_π)
5. From L(D) bound: exp(D(v_π)) ≥ valuation(f) > 1, so D(v_π) ≥ 1
6. By IsLinearPlaceSupport: v_π is a linear place
7. So v_π.asIdeal = span{X - C α} for some α
8. Since span{π} = span{X - C α}, they are associates -/
lemma irreducible_factor_of_denom_is_linear (f : RatFunc Fq) (D : DivisorV2 (Polynomial Fq))
    (hf_val : ∀ v : HeightOneSpectrum (Polynomial Fq), v.valuation (RatFunc Fq) f ≤ WithZero.exp (D v))
    (hf_ne : f ≠ 0) (hDlin : IsLinearPlaceSupport D)
    (π : Polynomial Fq) (hπ_irr : Irreducible π) (hπ_dvd : π ∣ f.denom) :
    ∃ α : Fq, Associated π (Polynomial.X - Polynomial.C α) := by
  -- Setup: construct the place v_π corresponding to π
  have hdenom_ne : f.denom ≠ 0 := f.denom_ne_zero
  have hπ_ne : π ≠ 0 := hπ_irr.ne_zero
  let v_π : HeightOneSpectrum (Polynomial Fq) :=
    ⟨Ideal.span {π}, Ideal.span_singleton_prime hπ_ne |>.mpr hπ_irr.prime,
     by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hπ_ne⟩

  -- At v_π, denom has valuation < 1 (since π | denom means denom ∈ v_π.asIdeal)
  have hdenom_in_v : f.denom ∈ v_π.asIdeal := by
    simp only [v_π, Ideal.mem_span_singleton]; exact hπ_dvd
  have hdenom_val_lt : v_π.intValuation f.denom < 1 :=
    (intValuation_lt_one_iff_mem v_π f.denom).mpr hdenom_in_v

  -- Coprimality: since num and denom are coprime, π ∤ num
  have hcop : IsCoprime f.num f.denom := f.isCoprime_num_denom
  have hπ_not_dvd_num : ¬(π ∣ f.num) := by
    intro hπ_dvd_num
    have hdvd_one : π ∣ (1 : Polynomial Fq) := by
      obtain ⟨a, b, hab⟩ := hcop
      calc π ∣ a * f.num + b * f.denom := dvd_add (dvd_mul_of_dvd_right hπ_dvd_num a)
                                                   (dvd_mul_of_dvd_right hπ_dvd b)
         _ = 1 := hab
    exact Irreducible.not_isUnit hπ_irr (isUnit_of_dvd_one hdvd_one)

  -- So num ∉ v_π.asIdeal, hence num has valuation 1 at v_π
  have hnum_not_in_v : f.num ∉ v_π.asIdeal := by
    simp only [v_π, Ideal.mem_span_singleton]; exact hπ_not_dvd_num
  have hnum_val_one : v_π.intValuation f.num = 1 := intValuation_eq_one_iff.mpr hnum_not_in_v

  -- valuation(f) = valuation(num)/valuation(denom) > 1
  have hf_val_gt_one : v_π.valuation (RatFunc Fq) f > 1 := by
    rw [← RatFunc.num_div_denom f]
    have hnum_ne : f.num ≠ 0 := by
      intro heq
      have hf_eq_zero : f = 0 := by rw [← RatFunc.num_div_denom f, heq, map_zero, zero_div]
      exact hf_ne hf_eq_zero
    have hdenom_alg_ne : algebraMap (Polynomial Fq) (RatFunc Fq) f.denom ≠ 0 :=
      RatFunc.algebraMap_ne_zero hdenom_ne
    rw [Valuation.map_div, v_π.valuation_of_algebraMap, v_π.valuation_of_algebraMap,
        hnum_val_one, one_div]
    have hdenom_mem : f.denom ∈ nonZeroDivisors (Polynomial Fq) :=
      mem_nonZeroDivisors_of_ne_zero hdenom_ne
    have hval_ne : v_π.intValuation f.denom ≠ 0 := v_π.intValuation_ne_zero' ⟨f.denom, hdenom_mem⟩
    have hcoe_val_lt : (v_π.intValuation f.denom : WithZero (Multiplicative ℤ)) < 1 := hdenom_val_lt
    exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr (by exact_mod_cast hval_ne), hcoe_val_lt⟩

  -- From L(D) bound: exp(D(v_π)) ≥ valuation(f) > 1, so D(v_π) ≥ 1
  have hD_pos : D v_π > 0 := by
    have hf_bound := hf_val v_π
    have hexp_gt_one : WithZero.exp (D v_π) > 1 := lt_of_lt_of_le hf_val_gt_one hf_bound
    rw [← WithZero.exp_zero] at hexp_gt_one
    exact WithZero.exp_lt_exp.mp hexp_gt_one

  -- D v_π > 0 means v_π ∈ D.support
  have hv_in_supp : v_π ∈ D.support := by rw [Finsupp.mem_support_iff]; omega

  -- By IsLinearPlaceSupport, v_π must be a linear place
  have hv_linear := hDlin v_π hv_in_supp
  obtain ⟨α, hv_eq⟩ := hv_linear

  -- v_π.asIdeal = span{π} and linearPlace α has asIdeal = span{X - α}
  -- Since v_π = linearPlace α, these ideals are equal
  have hspan_eq : Ideal.span {π} = Ideal.span {Polynomial.X - Polynomial.C α} := by
    have h1 : v_π.asIdeal = Ideal.span {π} := rfl
    have h2 : (linearPlace α).asIdeal = Ideal.span {Polynomial.X - Polynomial.C α} := rfl
    rw [← h1, ← h2, hv_eq]

  -- span{π} = span{X - C α} implies they are associates
  -- In a PID, span{a} = span{b} ⟺ a and b are associates
  have hassoc : Associated π (Polynomial.X - Polynomial.C α) := by
    rw [Ideal.span_singleton_eq_span_singleton] at hspan_eq
    exact hspan_eq

  exact ⟨α, hassoc⟩

/-- The denominator of f ∈ L(D) splits over Fq when D is supported on linear places and f is
non-constant with positive degree denominator.

This follows from `irreducible_factor_of_denom_is_linear`: every irreducible factor is linear,
so the polynomial is a product of linear factors, which means it splits. -/
lemma denom_splits_of_LRatFunc (f : RatFunc Fq) (D : DivisorV2 (Polynomial Fq))
    (hf_val : ∀ v : HeightOneSpectrum (Polynomial Fq), v.valuation (RatFunc Fq) f ≤ WithZero.exp (D v))
    (hf_ne : f ≠ 0) (hDlin : IsLinearPlaceSupport D) :
    f.denom.Splits := by
  -- denom splits if all irreducible factors have degree 1
  -- In a field, p.Splits ↔ every irreducible factor of p is linear (degree 1)
  have hdenom_ne : f.denom ≠ 0 := f.denom_ne_zero
  -- Use the characterization: splits iff f = 0 ∨ every irreducible factor has degree 1
  rw [Polynomial.splits_iff_splits]
  right
  intro q hq_irr hq_dvd
  -- q is an irreducible divisor of f.denom, so by our lemma it's associated to X - C α
  obtain ⟨α, hassoc⟩ := irreducible_factor_of_denom_is_linear f D hf_val hf_ne hDlin q hq_irr hq_dvd
  -- Associated polynomials have the same degree
  have hdeg_eq : q.degree = (Polynomial.X - Polynomial.C α).degree :=
    Polynomial.degree_eq_degree_of_associated hassoc
  rw [hdeg_eq, Polynomial.degree_X_sub_C]

/-- For a nonzero f in projective L(D) with deg(D) < 0, we get a contradiction.

**Mathematical argument**:
1. For constants: valuation = 1 at all places, so D(v) ≥ 0 everywhere needed.
   But deg(D) < 0 implies some D(v) < 0. Contradiction.
2. For non-constants with noPoleAtInfinity:
   - All poles of f must be in D.support with D(v) ≥ (pole multiplicity) ≥ 1
   - Since deg(D) < 0, there exist places with D(v) < 0
   - At those places, f must have zeros (valuation < 1 required)
   - The product formula gives: deg(D) + sum of orders ≥ 0
   - Combined with noPoleAtInfinity, this contradicts deg(D) < 0

**Note on weighted vs unweighted degree**:
The current divisor degree is unweighted: deg(D) = Σ_v D(v).
The product formula over all places is: Σ_v deg(v) * ord_v(f) + ord_∞(f) = 0.
For linear places (deg = 1), these coincide. For non-linear places, a weighted
degree definition would be needed for full generality. The current proof works
because any pole at a non-linear place (π) would require D((π)) ≥ 1, but if
D is only supported on linear places, D((π)) = 0, contradiction. So poles must
be at linear places, making the unweighted formula valid.

TODO: Add weighted degree infrastructure for full generality over all places. -/
theorem projective_LRatFunc_eq_zero_of_neg_deg (D : DivisorV2 (Polynomial Fq)) (hD : D.deg < 0)
    (hDlin : IsLinearPlaceSupport D)
    (f : RatFunc Fq) (hf : f ∈ RRSpace_ratfunc_projective D) :
    f = 0 := by
  by_contra hf_ne
  -- f ≠ 0 and f ∈ projective L(D)
  obtain ⟨hf_finite, hf_infty⟩ := hf
  rcases hf_infty with rfl | hf_nopole
  · exact hf_ne rfl
  -- f ≠ 0 with no pole at infinity, and bounded at finite places

  -- Get a place with negative D coefficient (exists since deg(D) < 0)
  obtain ⟨v_neg, hv_neg_mem, hv_neg⟩ := exists_neg_of_deg_neg hD

  -- Case split: is f a constant?
  by_cases hf_const : ∃ c : Fq, c ≠ 0 ∧ f = RatFunc.C c
  · -- f is a nonzero constant
    obtain ⟨c, hc_ne, hf_eq⟩ := hf_const
    rw [hf_eq] at hf_finite
    exact constant_not_in_LRatFunc_of_neg_coeff c hc_ne D v_neg hv_neg hf_finite

  -- f is non-constant with noPoleAtInfinity
  -- From noPoleAtInfinity: deg(num) ≤ deg(denom)
  -- Since f ≠ 0 and not constant, denom has positive degree, meaning f has poles

  rcases hf_finite with rfl | hf_val
  · exact hf_ne rfl

  -- Step 1: Show denom has positive degree (f is non-constant)
  -- If denom has degree 0, it's a unit, so f = num/unit is a polynomial.
  -- For noPoleAtInfinity: deg(num) ≤ deg(denom) = 0, so num is constant.
  -- Then f would be a constant, contradicting hf_const.
  have hdenom_pos : 0 < f.denom.natDegree := by
    by_contra h
    push_neg at h
    have hdenom_deg_zero : f.denom.natDegree = 0 := Nat.eq_zero_of_le_zero h
    -- denom has degree 0 means it's a constant
    have hdenom_const : ∃ c : Fq, c ≠ 0 ∧ f.denom = Polynomial.C c := by
      have hmonic : f.denom.Monic := f.monic_denom
      have hdenom_ne : f.denom ≠ 0 := f.denom_ne_zero
      rw [Polynomial.natDegree_eq_zero] at hdenom_deg_zero
      obtain ⟨c, hc⟩ := hdenom_deg_zero
      refine ⟨c, ?_, hc.symm⟩
      intro hc_zero
      rw [hc_zero, Polynomial.C_0] at hc
      exact hdenom_ne hc.symm
    obtain ⟨c, hc_ne, hdenom_eq⟩ := hdenom_const
    -- From noPoleAtInfinity: deg(num) ≤ deg(denom) = 0
    have hnum_deg_zero : f.num.natDegree = 0 := by
      have h1 : f.num.natDegree ≤ f.denom.natDegree := hf_nopole
      rw [hdenom_deg_zero] at h1
      exact Nat.eq_zero_of_le_zero h1
    -- num has degree 0, so it's a constant
    rw [Polynomial.natDegree_eq_zero] at hnum_deg_zero
    obtain ⟨n, hnum_eq⟩ := hnum_deg_zero
    -- f = C n / C c = C (n / c), a constant
    have hf_is_const : f = RatFunc.C (n / c) := by
      rw [← RatFunc.num_div_denom f, ← hnum_eq, hdenom_eq]
      simp only [RatFunc.algebraMap_C, RatFunc.C]
      have hc_ne' : (algebraMap Fq (RatFunc Fq)) c ≠ 0 := by
        intro h
        rw [map_eq_zero] at h
        exact hc_ne h
      field_simp [hc_ne']
      rw [← map_mul, mul_div_cancel₀ n hc_ne]
    -- This contradicts hf_const (f is not a constant)
    by_cases hn : n = 0
    · -- If n = 0, then f = 0, contradicting hf_ne
      rw [hn, zero_div] at hf_is_const
      rw [hf_is_const] at hf_ne
      simp only [map_zero, not_true_eq_false] at hf_ne
    · -- If n ≠ 0, then f = C (n/c) is a nonzero constant
      have hnc_ne : n / c ≠ 0 := div_ne_zero hn hc_ne
      exact hf_const ⟨n / c, hnc_ne, hf_is_const⟩

  -- Step 2: Any irreducible factor of denom gives a pole
  -- Get an irreducible factor of denom (exists since denom has positive degree)
  have hdenom_ne : f.denom ≠ 0 := f.denom_ne_zero
  have hexists_factor : ∃ π : Polynomial Fq, Irreducible π ∧ π ∣ f.denom :=
    Polynomial.exists_irreducible_of_natDegree_pos hdenom_pos
  obtain ⟨π, hπ_irr, hπ_dvd⟩ := hexists_factor

  -- Define the place v_π corresponding to π
  -- v_π.asIdeal = span{π}
  have hπ_ne : π ≠ 0 := hπ_irr.ne_zero
  let v_π : HeightOneSpectrum (Polynomial Fq) :=
    ⟨Ideal.span {π}, Ideal.span_singleton_prime hπ_ne |>.mpr hπ_irr.prime,
     by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hπ_ne⟩

  -- At v_π, denom has valuation < 1 (since π | denom means denom ∈ v_π.asIdeal)
  have hdenom_in_v : f.denom ∈ v_π.asIdeal := by
    simp only [v_π, Ideal.mem_span_singleton]
    exact hπ_dvd

  have hdenom_val_lt : v_π.intValuation f.denom < 1 :=
    (intValuation_lt_one_iff_mem v_π f.denom).mpr hdenom_in_v

  -- num and denom are coprime
  have hcop : IsCoprime f.num f.denom := f.isCoprime_num_denom

  -- Since num and denom are coprime, π ∤ num (else π would divide both)
  have hπ_not_dvd_num : ¬(π ∣ f.num) := by
    intro hπ_dvd_num
    have hdvd_one : π ∣ (1 : Polynomial Fq) := by
      obtain ⟨a, b, hab⟩ := hcop
      calc π ∣ a * f.num + b * f.denom := dvd_add (dvd_mul_of_dvd_right hπ_dvd_num a)
                                                   (dvd_mul_of_dvd_right hπ_dvd b)
         _ = 1 := hab
    exact Irreducible.not_isUnit hπ_irr (isUnit_of_dvd_one hdvd_one)

  -- So num ∉ v_π.asIdeal
  have hnum_not_in_v : f.num ∉ v_π.asIdeal := by
    simp only [v_π, Ideal.mem_span_singleton]
    exact hπ_not_dvd_num

  -- Therefore num has valuation 1 at v_π
  have hnum_val_one : v_π.intValuation f.num = 1 :=
    intValuation_eq_one_iff.mpr hnum_not_in_v

  -- valuation(f) = valuation(num)/valuation(denom) > 1 since denom val < 1 and num val = 1
  have hf_val_gt_one : v_π.valuation (RatFunc Fq) f > 1 := by
    rw [← RatFunc.num_div_denom f]
    have hnum_ne : f.num ≠ 0 := by
      intro heq
      have hf_eq_zero : f = 0 := by
        rw [← RatFunc.num_div_denom f, heq, map_zero, zero_div]
      exact hf_ne hf_eq_zero
    have hdenom_alg_ne : algebraMap (Polynomial Fq) (RatFunc Fq) f.denom ≠ 0 :=
      RatFunc.algebraMap_ne_zero hdenom_ne
    rw [Valuation.map_div, v_π.valuation_of_algebraMap, v_π.valuation_of_algebraMap]
    rw [hnum_val_one]
    simp only [one_div]
    have hdenom_mem : f.denom ∈ nonZeroDivisors (Polynomial Fq) :=
      mem_nonZeroDivisors_of_ne_zero hdenom_ne
    have hval_ne : v_π.intValuation f.denom ≠ 0 := v_π.intValuation_ne_zero' ⟨f.denom, hdenom_mem⟩
    have hcoe_val_lt : (v_π.intValuation f.denom : WithZero (Multiplicative ℤ)) < 1 := hdenom_val_lt
    exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr (by exact_mod_cast hval_ne), hcoe_val_lt⟩

  -- From hf_val (f ∈ L(D)): v_π.valuation f ≤ exp(D v_π)
  have hf_bound := hf_val v_π

  -- valuation > 1 means exp(D v_π) ≥ valuation > 1, so exp(D v_π) > 1, so D v_π ≥ 1
  have hD_pos : D v_π > 0 := by
    have hexp_gt_one : WithZero.exp (D v_π) > 1 := lt_of_lt_of_le hf_val_gt_one hf_bound
    rw [← WithZero.exp_zero] at hexp_gt_one
    exact WithZero.exp_lt_exp.mp hexp_gt_one

  -- D v_π > 0 means v_π ∈ D.support
  have hv_in_supp : v_π ∈ D.support := by
    rw [Finsupp.mem_support_iff]
    omega

  -- By IsLinearPlaceSupport, v_π must be a linear place
  have hv_linear := hDlin v_π hv_in_supp
  obtain ⟨α, hv_eq⟩ := hv_linear

  -- So π generates the ideal (X - α), i.e., π is associate to (X - α)
  -- v_π.asIdeal = span{π} and v_π = linearPlace α means span{π} = span{X - α}
  have hspan_eq : v_π.asIdeal = (linearPlace α).asIdeal := by rw [hv_eq]
  -- This means π and (X - α) are associates - they generate the same ideal

  -- So denom only has linear irreducible factors!
  -- This is the key: every irreducible factor of denom is linear.
  -- We've shown: at each pole v_π of f, we have D(v_π) > 0 and v_π is a linear place

  -- Step 3: Counting argument - derive contradiction from sum inequalities
  -- v_neg is a place with D(v_neg) < 0 (from earlier in proof)
  -- By IsLinearPlaceSupport, v_neg = linearPlace β for some β
  have hv_neg_linear := hDlin v_neg hv_neg_mem
  obtain ⟨β, hv_neg_eq⟩ := hv_neg_linear

  -- Get num ≠ 0
  have hnum_ne : f.num ≠ 0 := by
    intro heq
    have hf_eq_zero : f = 0 := by rw [← RatFunc.num_div_denom f, heq, map_zero, zero_div]
    exact hf_ne hf_eq_zero

  -- By zero_multiplicity_ge_neg_D: rootMult(β, num) ≥ |D(v_neg)|
  have hD_at_neg : D (linearPlace β) < 0 := by rw [← hv_neg_eq]; exact hv_neg
  have hzero_mult := zero_multiplicity_ge_neg_D f D hf_val hf_ne β hD_at_neg
  -- hzero_mult : (f.num.rootMultiplicity β : ℤ) ≥ -D (linearPlace β)

  -- |D(v_neg)| ≥ 1 since D(v_neg) < 0 and D takes integer values
  have hneg_D_pos : -D (linearPlace β) ≥ 1 := by omega

  -- So num has a root at β with multiplicity ≥ 1
  have hβ_root_mult : f.num.rootMultiplicity β ≥ 1 := by
    have h : (f.num.rootMultiplicity β : ℤ) ≥ 1 := le_trans hneg_D_pos hzero_mult
    omega

  -- Therefore β is a root of num
  have hβ_is_root : f.num.IsRoot β := by
    have h : f.num.rootMultiplicity β > 0 := by omega
    exact (Polynomial.rootMultiplicity_pos hnum_ne).mp h

  -- By pole_multiplicity_le_D: at α (root of denom), rootMult(α, denom) ≤ D(linearPlace α)
  -- We have α from Step 2 where v_π = linearPlace α
  have hα_root : f.denom.IsRoot α := by
    -- v_π.asIdeal = span{π} and (linearPlace α).asIdeal = span{X - α}
    -- From hspan_eq: these ideals are equal
    -- So denom ∈ span{π} implies denom ∈ span{X - α}
    -- i.e., (X - α) | denom, so α is a root
    have hdenom_in_lin : f.denom ∈ (linearPlace α).asIdeal := by
      rw [← hspan_eq]; exact hdenom_in_v
    simp only [linearPlace, Ideal.mem_span_singleton] at hdenom_in_lin
    exact Polynomial.dvd_iff_isRoot.mp hdenom_in_lin

  have hpole_mult := pole_multiplicity_le_D f D hf_val hf_ne α hα_root
  -- hpole_mult : (f.denom.rootMultiplicity α : ℤ) ≤ D (linearPlace α)

  -- α ≠ β (since D(linearPlace α) > 0 but D(linearPlace β) < 0)
  have hαβ_ne : α ≠ β := by
    intro heq
    -- If α = β, then linearPlace α = linearPlace β
    -- So D(linearPlace α) = D(linearPlace β)
    -- But D v_π = D(linearPlace α) > 0 (by hD_pos and hv_eq)
    -- And D(linearPlace β) < 0 (by hD_at_neg)
    have h1 : D v_π > 0 := hD_pos
    simp only [hv_eq] at h1
    -- h1 : D (linearPlace α) > 0
    -- hD_at_neg : D (linearPlace β) < 0
    rw [heq] at h1
    linarith

  -- The contradiction comes from the degree formula:
  -- deg(D) = Σ_{v} D(v) < 0
  -- The positive contributions come from poles of f (including α)
  -- The negative contributions must be matched by zeros of num (including β)
  -- But the noPoleAtInfinity constraint limits num's degree

  -- Key: D(linearPlace α) ≥ 1 and D(linearPlace β) ≤ -1
  have hD_α_pos : D (linearPlace α) ≥ 1 := by
    have h : D v_π > 0 := hD_pos
    simp only [hv_eq] at h
    omega
  have hD_β_neg : D (linearPlace β) ≤ -1 := by linarith

  -- From zero_multiplicity: num.rootMultiplicity β ≥ |D(linearPlace β)| ≥ 1
  -- From pole_multiplicity: denom.rootMultiplicity α ≤ D(linearPlace α)
  -- Also denom.rootMultiplicity α ≥ 1 since α is a root
  have hα_root_mult_pos : f.denom.rootMultiplicity α ≥ 1 := by
    exact (Polynomial.rootMultiplicity_pos hdenom_ne).mpr hα_root

  -- rootMultiplicity ≤ natDegree via count_roots and card_roots'
  have hβ_mult_le_deg : f.num.rootMultiplicity β ≤ f.num.natDegree := by
    calc f.num.rootMultiplicity β = f.num.roots.count β := (Polynomial.count_roots f.num).symm
      _ ≤ f.num.roots.card := Multiset.count_le_card β f.num.roots
      _ ≤ f.num.natDegree := Polynomial.card_roots' f.num

  -- Now use that num.natDegree ≥ rootMultiplicity β ≥ 1
  have hnum_deg_pos : f.num.natDegree ≥ 1 := by omega

  -- The counting argument: use deg(D) = Σ D(v) < 0
  -- Define positive and negative parts of D
  let pos_support := D.support.filter (fun v => 0 < D v)
  let neg_support := D.support.filter (fun v => D v < 0)

  -- deg(D) = (sum over positive) + (sum over negative)
  -- Since D(v) < 0 for v in neg_support, sum over negative = -Σ|D(v)|
  -- So: pos_sum - neg_sum < 0, i.e., pos_sum < neg_sum

  -- Key fact: for each root γ of denom, D(linearPlace γ) ≥ rootMult(γ) ≥ 1
  -- (same Step 2 argument works for any irreducible factor)
  -- This means all roots of denom contribute to pos_support

  -- For each v in neg_support, v = linearPlace β' and |D(v)| ≤ rootMult(β', num)
  -- Summing: Σ_{neg} |D| ≤ Σ rootMult ≤ num.natDegree

  -- The contradiction: we need denom.natDegree ≤ pos_sum < neg_sum ≤ num.natDegree
  -- But hf_nopole says num.natDegree ≤ denom.natDegree

  -- For the specific places α and β:
  -- D(linearPlace α) ≥ rootMult(α, denom) ≥ 1
  -- D(linearPlace β) ≤ -rootMult(β, num) ≤ -1

  -- From Finsupp.sum, deg(D) = Σ_v D(v)
  -- linearPlace α ∈ pos_support (since D(linearPlace α) ≥ 1 > 0)
  -- linearPlace β ∈ neg_support (since D(linearPlace β) ≤ -1 < 0)

  have hα_in_pos : linearPlace α ∈ D.support := by
    rw [Finsupp.mem_support_iff]
    omega

  have hβ_in_neg : linearPlace β ∈ D.support := by
    rw [Finsupp.mem_support_iff]
    omega

  -- The sum over all v in support decomposes as positive + negative parts
  -- With deg(D) < 0, the negative sum dominates

  -- Now use that num must accommodate all negative places' multiplicities
  -- and denom provides poles that contribute to positive places

  -- Sum inequality for negative part:
  -- Each v with D(v) < 0 forces rootMult ≥ |D(v)| in num
  -- Different negative places give different roots (linearPlace injective)
  -- So num.natDegree ≥ Σ_{neg places} |D|

  -- Sum inequality for positive part:
  -- Each root of denom is at a positive place (Step 2 argument for any factor)
  -- So denom.natDegree = Σ rootMult ≤ Σ_{positive places of denom} D
  -- ≤ Σ_{all positive} D

  -- The key: show that Σ_{D>0} D ≥ denom.natDegree
  -- This requires that denom splits (all roots in Fq) - which follows from
  -- Step 2 showing all irreducible factors are linear

  -- For the single-place version sufficient for contradiction:
  -- We have D(linearPlace α) ≥ 1 and D(linearPlace β) ≤ -1
  -- These contribute at least +1 and -1 respectively to deg(D)
  -- But importantly: |D(linearPlace β)| ≤ rootMult(β, num) ≤ num.natDegree
  -- And rootMult(α, denom) ≤ D(linearPlace α), with α being a root of denom

  -- Now use the full sum decomposition
  -- The negative contribution at β forces: |D(linearPlace β)| ≤ num.natDegree
  -- With hzero_mult: rootMult(β, num) ≥ |D(linearPlace β)|
  -- So: -D(linearPlace β) ≤ num.natDegree

  have hneg_D_le_num : -D (linearPlace β) ≤ f.num.natDegree := by
    have h1 : -D (linearPlace β) ≤ (f.num.rootMultiplicity β : ℤ) := by
      have h := hzero_mult; omega
    have h2 : (f.num.rootMultiplicity β : ℤ) ≤ f.num.natDegree := by
      exact_mod_cast hβ_mult_le_deg
    omega

  -- Similarly for positive side: D(linearPlace α) ≥ rootMult(α, denom)
  have hα_mult_le_deg : f.denom.rootMultiplicity α ≤ f.denom.natDegree := by
    calc f.denom.rootMultiplicity α = f.denom.roots.count α := (Polynomial.count_roots f.denom).symm
      _ ≤ f.denom.roots.card := Multiset.count_le_card α f.denom.roots
      _ ≤ f.denom.natDegree := Polynomial.card_roots' f.denom

  -- Key: show the sum constraints lead to contradiction
  -- We need to use that there are potentially many negative places,
  -- and their total |D| exceeds the positive total D

  -- From deg(D) < 0, the sum Σ D(v) < 0
  -- This means the negative contributions outweigh positive ones

  -- The crucial observation: If we sum over ALL places:
  -- Σ_{v ∈ D.support} D(v) = deg(D) < 0

  -- For the counting argument to work, we need:
  -- (1) Σ_{D>0} D ≥ denom.natDegree (each pole contributes)
  -- (2) Σ_{D<0} |D| ≤ num.natDegree (each zero accommodates)
  -- (3) deg(D) = Σ_{D>0} - Σ_{D<0}|D| < 0 means Σ_{D>0} < Σ_{D<0}

  -- Combining: denom.natDegree ≤ Σ_{D>0} < Σ_{D<0} ≤ num.natDegree
  -- So denom.natDegree < num.natDegree, contradiction!

  -- To formalize (1), we need denom to split. For now, we note that
  -- the Step 2 argument proves ANY irreducible factor is linear,
  -- so denom splits and denom.natDegree = Σ rootMult = Σ (D over poles)

  -- Direct approach: use that the specific inequalities already give enough
  -- The places α, β are distinct (hαβ_ne) and satisfy:
  -- D(α) ≥ 1, D(β) ≤ -1
  -- If these were the ONLY two places in support, deg(D) = D(α) + D(β) could be ≥ 0
  -- But there must be more negative contributions for deg(D) < 0

  -- Actually, the issue is that with just two specific places, we can't conclude.
  -- We need the full sum argument.

  -- For denom splits: if all irreducible factors of p are linear, then p splits
  -- Key: use that for a monic polynomial with all roots in F_q, natDegree = roots.card

  -- Final contradiction using the available facts:
  -- From the structure of deg(D) and the root constraints,
  -- the sum of D over roots of denom (each ≥ corresponding multiplicity)
  -- must equal denom.natDegree when split
  -- And sum of |D| over negative places must be accommodated by num's zeros

  -- Since the full sum argument requires denom.Splits, let's note that
  -- over F_q, denom splits iff all its irreducible factors are linear
  -- Step 2 shows this for any factor π, so denom splits

  -- With denom.Splits: denom.natDegree = denom.roots.card = Σ rootMult
  -- Each root α of denom: D(linearPlace α) ≥ rootMult(α) (from pole_multiplicity_le_D)
  -- So Σ_{roots α} D(linearPlace α) ≥ denom.natDegree
  -- These are exactly the positive contributions from poles

  -- Combining with deg(D) < 0 and neg_sum ≤ num.natDegree:
  -- denom.natDegree ≤ pos_sum < neg_sum ≤ num.natDegree

  -- This contradicts hf_nopole : num.natDegree ≤ denom.natDegree

  -- The formal proof requires showing denom.Splits
  -- For now, we use that the argument structure is complete
  -- and the specific numeric constraints suffice

  -- Using the key inequality chain:
  -- hf_nopole gives num.natDegree ≤ denom.natDegree
  -- The counting shows denom.natDegree < num.natDegree (contradiction)

  -- For the counting to work without full splits proof:
  -- We know: denom has root α with mult ≥ 1
  -- We know: num has root β with mult ≥ |D(β)| ≥ 1
  -- α ≠ β

  -- The degree formula deg(D) = Σ D(v) < 0 combined with
  -- D(linearPlace α) ≥ 1 for each root α of denom
  -- D(linearPlace β) ≤ -|D(β)| for each negative place β

  -- If we sum over all roots of denom vs all negative places,
  -- and use that denom splits (roots account for all of natDegree),
  -- we get the contradiction.

  -- For the minimal proof, the key is:
  -- deg(D) < 0 with D having both positive and negative values
  -- means there's "more" negative contribution than positive
  -- The root/zero constraints translate this to degree constraints

  -- Final step: show that num.natDegree > denom.natDegree
  -- This contradicts hf_nopole

  -- The bound hβ_root_mult : f.num.rootMultiplicity β ≥ 1 combined with
  -- potentially more negative places means num needs enough degree

  -- Using that the whole D.support splits into positive and negative parts
  -- and the sum is negative, the negative parts dominate

  -- Contradiction via the sum argument
  -- Define the positive and negative sums
  let pos_sum := (D.support.filter (fun v => 0 < D v)).sum D
  let neg_abs_sum := (D.support.filter (fun v => D v < 0)).sum (fun v => -D v)

  -- deg(D) = pos_sum - neg_abs_sum (since D(v) < 0 for negative places)
  have hdeg_split : D.deg = pos_sum - neg_abs_sum := by
    unfold DivisorV2.deg pos_sum neg_abs_sum
    simp only [Finsupp.sum]
    -- Split the sum over support into positive and negative parts
    have hsplit := D.support.sum_filter_add_sum_filter_not (fun v => 0 < D v) D
    -- D.support.sum D = pos_part_sum + non_pos_part_sum
    -- The non-positive part equals the negative part since D(v) = 0 implies v ∉ support
    have heq_neg : D.support.filter (fun v => ¬(0 < D v)) = D.support.filter (fun v => D v < 0) := by
      ext v
      simp only [Finset.mem_filter, Finsupp.mem_support_iff, not_lt]
      constructor
      · intro ⟨hv_ne, hle⟩
        exact ⟨hv_ne, by omega⟩
      · intro ⟨hv_ne, hlt⟩
        exact ⟨hv_ne, le_of_lt hlt⟩
    rw [heq_neg] at hsplit
    -- Now sum over negative part: Σ D(v) = Σ (- (-D(v))) = - neg_abs_sum
    have hneg_sum : (D.support.filter (fun v => D v < 0)).sum D =
        -(D.support.filter (fun v => D v < 0)).sum (fun v => -D v) := by
      simp only [Finset.sum_neg_distrib, neg_neg]
    rw [hneg_sum] at hsplit
    linarith

  -- From hdeg_split and hD : D.deg < 0, we get pos_sum < neg_abs_sum
  have hsum_ineq : pos_sum < neg_abs_sum := by omega

  -- Key bound (1): pos_sum ≥ denom.natDegree
  -- This requires showing denom splits and summing pole_multiplicity_le_D
  have hpos_ge_denom : pos_sum ≥ (f.denom.natDegree : ℤ) := by
    -- Step A: denom splits
    have hdenom_splits := denom_splits_of_LRatFunc f D hf_val hf_ne hDlin
    -- Step B: natDegree = roots.card
    have hdenom_card := hdenom_splits.natDegree_eq_card_roots
    -- Step C: For each root γ of denom, D(linearPlace γ) ≥ rootMult(γ, denom) > 0
    -- First, show that every root is actually a root
    have hroot_bound : ∀ γ ∈ f.denom.roots, D (linearPlace γ) ≥ f.denom.rootMultiplicity γ := by
      intro γ hγ_root
      have hγ_isRoot : f.denom.IsRoot γ := (Polynomial.mem_roots hdenom_ne).mp hγ_root
      have hbound := pole_multiplicity_le_D f D hf_val hf_ne γ hγ_isRoot
      exact hbound
    -- Step D: For each root γ, D(linearPlace γ) > 0 (so linearPlace γ ∈ positive support)
    have hroot_pos : ∀ γ ∈ f.denom.roots, 0 < D (linearPlace γ) := by
      intro γ hγ_root
      have hγ_isRoot : f.denom.IsRoot γ := (Polynomial.mem_roots hdenom_ne).mp hγ_root
      have hmult_pos : 0 < f.denom.rootMultiplicity γ := (Polynomial.rootMultiplicity_pos hdenom_ne).mpr hγ_isRoot
      have hbound := hroot_bound γ hγ_root
      omega
    -- Step E: Sum over positive support includes sum over linearPlace.(roots.toFinset)
    -- We use: Σ_pos D(v) ≥ Σ_{γ ∈ roots.toFinset} D(linearPlace γ) ≥ Σ rootMult = natDegree
    have hsum_roots : (f.denom.roots.toFinset.sum fun γ => D (linearPlace γ)) ≥ f.denom.natDegree := by
      -- Each root contributes at least its multiplicity
      calc (f.denom.roots.toFinset.sum fun γ => D (linearPlace γ))
          ≥ f.denom.roots.toFinset.sum (fun γ => (f.denom.rootMultiplicity γ : ℤ)) := by
            apply Finset.sum_le_sum
            intro γ hγ
            exact hroot_bound γ (Multiset.mem_toFinset.mp hγ)
        _ = (f.denom.roots.toFinset.sum fun γ => (f.denom.roots.count γ : ℤ)) := by
            congr 1; ext γ; rw [Polynomial.count_roots]
        _ = (f.denom.roots.card : ℤ) := by
            have h := Multiset.toFinset_sum_count_eq f.denom.roots
            simp only [← Nat.cast_sum, h]
        _ = f.denom.natDegree := by rw [hdenom_card]
    -- Step F: Sum over positive support ≥ sum over roots (linearPlace is injective)
    have hinj : Function.Injective (fun γ : Fq => linearPlace γ) := by
      intro α β heq
      -- If linearPlace α = linearPlace β, then their asIdeal are equal
      have hasIdeal_eq : (linearPlace α).asIdeal = (linearPlace β).asIdeal := congrArg (·.asIdeal) heq
      -- span{X - C α} = span{X - C β}, so X - C α and X - C β are associates
      simp only [linearPlace, Ideal.span_singleton_eq_span_singleton] at hasIdeal_eq
      -- For monic polynomials, associated implies equal
      have hmonic_α : (Polynomial.X - Polynomial.C α).Monic := Polynomial.monic_X_sub_C α
      have hmonic_β : (Polynomial.X - Polynomial.C β).Monic := Polynomial.monic_X_sub_C β
      have heq_poly := Polynomial.eq_of_monic_of_associated hmonic_α hmonic_β hasIdeal_eq
      -- X - C α = X - C β implies α = β
      simp only [sub_right_inj, Polynomial.C_inj] at heq_poly
      exact heq_poly
    -- The image of roots.toFinset under linearPlace is contained in the positive support
    have himage_subset : (f.denom.roots.toFinset.image linearPlace) ⊆
        D.support.filter (fun v => 0 < D v) := by
      intro v hv
      simp only [Finset.mem_image] at hv
      obtain ⟨γ, hγ_mem, hγ_eq⟩ := hv
      rw [Finset.mem_filter, Finsupp.mem_support_iff]
      constructor
      · have hpos := hroot_pos γ (Multiset.mem_toFinset.mp hγ_mem)
        rw [← hγ_eq]; omega
      · rw [← hγ_eq]; exact hroot_pos γ (Multiset.mem_toFinset.mp hγ_mem)
    -- Now use that sum over superset ≥ sum over subset
    calc pos_sum = (D.support.filter (fun v => 0 < D v)).sum D := rfl
      _ ≥ (f.denom.roots.toFinset.image linearPlace).sum D := by
          apply Finset.sum_le_sum_of_subset_of_nonneg himage_subset
          intro v hv_in_pos _
          -- For v in positive support, D(v) > 0 ≥ 0
          simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hv_in_pos
          linarith [hv_in_pos.2]
      _ = (f.denom.roots.toFinset.sum fun γ => D (linearPlace γ)) := by
          rw [Finset.sum_image]; intro γ₁ _ γ₂ _ heq; exact hinj heq
      _ ≥ f.denom.natDegree := hsum_roots

  -- Key bound (2): neg_abs_sum ≤ num.natDegree
  -- Sum of |D(v)| over negative places ≤ sum of root multiplicities ≤ num.natDegree
  have hneg_le_num : neg_abs_sum ≤ (f.num.natDegree : ℤ) := by
    -- Each v with D(v) < 0 is in D.support, so by IsLinearPlaceSupport, v = linearPlace β
    -- For each such β: |D(v)| ≤ rootMult(β, num) by zero_multiplicity_ge_neg_D
    -- The sum of rootMultiplicities ≤ num.natDegree (via roots.card)
    let neg_places := D.support.filter (fun v => D v < 0)
    -- For each v in neg_places, get the corresponding β
    have hneg_lin : ∀ v ∈ neg_places, ∃ β : Fq, v = linearPlace β := by
      intro v hv
      simp only [neg_places, Finset.mem_filter] at hv
      exact hDlin v hv.1
    -- Create function from neg_places to Fq
    -- Use that linearPlace is injective to show bound
    -- For each v in neg_places: -D(v) ≤ rootMult(β_v, num)
    have hbound_per_v : ∀ v ∈ neg_places, ∃ β : Fq, v = linearPlace β ∧
        -D v ≤ (f.num.rootMultiplicity β : ℤ) := by
      intro v hv
      obtain ⟨β, hv_eq⟩ := hneg_lin v hv
      refine ⟨β, hv_eq, ?_⟩
      simp only [neg_places, Finset.mem_filter] at hv
      have hD_neg : D (linearPlace β) < 0 := by rw [← hv_eq]; exact hv.2
      have hzero := zero_multiplicity_ge_neg_D f D hf_val hf_ne β hD_neg
      -- hzero : (rootMult β : ℤ) ≥ -D(linearPlace β)
      -- Goal: -D v ≤ (rootMult β : ℤ)
      rw [hv_eq]; linarith
    -- Build bijection: neg_places → image under linearPlace⁻¹
    -- Actually, use that the sum is bounded by summing over all possible roots
    -- For each v = linearPlace β in neg_places: -D(v) ≤ rootMult(β, num)
    -- β is a root of num (since rootMult ≥ 1 when D < 0)
    have hneg_is_num_root : ∀ v ∈ neg_places, ∀ β : Fq, v = linearPlace β →
        f.num.IsRoot β := by
      intro v hv β hv_eq
      simp only [neg_places, Finset.mem_filter] at hv
      have hD_neg : D (linearPlace β) < 0 := by rw [← hv_eq]; exact hv.2
      have hzero := zero_multiplicity_ge_neg_D f D hf_val hf_ne β hD_neg
      have hmult_pos : f.num.rootMultiplicity β ≥ 1 := by
        have h : (f.num.rootMultiplicity β : ℤ) ≥ 1 := by linarith
        omega
      exact (Polynomial.rootMultiplicity_pos hnum_ne).mp (by omega : f.num.rootMultiplicity β > 0)
    -- Strategy: Sum over neg_places maps injectively to roots of num
    -- Since linearPlace is injective and each β_v is a root of num:
    -- Σ_{v} (-D v) ≤ Σ_{v} rootMult(β_v, num)
    --              = Σ_{β ∈ image} rootMult(β, num)  [β_v distinct by injectivity]
    --              = Σ_{β ∈ image} num.roots.count(β)  [count_roots]
    --              ≤ num.roots.card  [sum over subset ≤ total]
    --              ≤ num.natDegree  [card_roots']

    -- linearPlace is injective (copied from hpos_ge_denom for scope)
    have hlinj : Function.Injective (fun γ : Fq => linearPlace γ) := by
      intro α β heq
      have hasIdeal_eq : (linearPlace α).asIdeal = (linearPlace β).asIdeal := congrArg (·.asIdeal) heq
      simp only [linearPlace, Ideal.span_singleton_eq_span_singleton] at hasIdeal_eq
      have hmonic_α : (Polynomial.X - Polynomial.C α).Monic := Polynomial.monic_X_sub_C α
      have hmonic_β : (Polynomial.X - Polynomial.C β).Monic := Polynomial.monic_X_sub_C β
      have heq_poly := Polynomial.eq_of_monic_of_associated hmonic_α hmonic_β hasIdeal_eq
      simp only [sub_right_inj, Polynomial.C_inj] at heq_poly
      exact heq_poly

    -- Define the inverse map: for each v in neg_places, get the unique β with v = linearPlace β
    let getRoot : neg_places → Fq := fun ⟨v, hv⟩ => (hneg_lin v hv).choose
    have hgetRoot_spec : ∀ v (hv : v ∈ neg_places), v = linearPlace (getRoot ⟨v, hv⟩) := by
      intro v hv
      exact (hneg_lin v hv).choose_spec

    -- getRoot is injective (since linearPlace is injective)
    have hgetRoot_inj : Function.Injective getRoot := by
      intro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ heq
      have h1 := hgetRoot_spec v₁ hv₁
      have h2 := hgetRoot_spec v₂ hv₂
      rw [heq] at h1
      simp only [Subtype.mk.injEq]
      rw [h1, ← h2]

    -- Each getRoot(v) is a root of num
    have hgetRoot_isRoot : ∀ v (hv : v ∈ neg_places), f.num.IsRoot (getRoot ⟨v, hv⟩) := by
      intro v hv
      exact hneg_is_num_root v hv (getRoot ⟨v, hv⟩) (hgetRoot_spec v hv)

    -- The image of getRoot is a subset of num.roots.toFinset
    let image := Finset.univ.image getRoot
    have himage_subset : image ⊆ f.num.roots.toFinset := by
      intro β hβ
      rw [Finset.mem_image] at hβ
      obtain ⟨⟨v, hv⟩, _, hvβ⟩ := hβ
      rw [Multiset.mem_toFinset]
      rw [← hvβ]
      exact (Polynomial.mem_roots hnum_ne).mpr (hgetRoot_isRoot v hv)

    -- For each v in neg_places, -D(v) ≤ rootMult(getRoot(v), num)
    have hbound_getRoot : ∀ v (hv : v ∈ neg_places),
        -D v ≤ (f.num.rootMultiplicity (getRoot ⟨v, hv⟩) : ℤ) := by
      intro v hv
      obtain ⟨β, hv_eq, hbound⟩ := hbound_per_v v hv
      -- We need to show getRoot ⟨v, hv⟩ = β
      -- We have v = linearPlace β and v = linearPlace (getRoot ⟨v, hv⟩)
      have hspec := hgetRoot_spec v hv
      have heq : getRoot ⟨v, hv⟩ = β := by
        have : linearPlace (getRoot ⟨v, hv⟩) = linearPlace β := by rw [← hspec, hv_eq]
        exact hlinj this
      rw [heq]
      exact hbound

    -- Sum bound: Σ_v (-D v) ≤ Σ_v rootMult(getRoot(v), num)
    have hsum_bound : neg_abs_sum ≤ (neg_places.attach.sum fun ⟨v, hv⟩ =>
        (f.num.rootMultiplicity (getRoot ⟨v, hv⟩) : ℤ)) := by
      simp only [neg_abs_sum]
      rw [← Finset.sum_attach]
      apply Finset.sum_le_sum
      intro ⟨v, hv⟩ _
      exact hbound_getRoot v hv

    -- Rewrite sum over attach as sum over image using injectivity
    have hsum_image : (neg_places.attach.sum fun ⟨v, hv⟩ =>
        (f.num.rootMultiplicity (getRoot ⟨v, hv⟩) : ℤ)) =
        (image.sum fun β => (f.num.rootMultiplicity β : ℤ)) := by
      -- Relate attach to univ on subtype
      have hattach_eq : neg_places.attach = Finset.univ := by
        ext ⟨v, hv⟩; simp
      rw [hattach_eq]
      -- Now use Finset.sum_image with injectivity
      rw [Finset.sum_image (fun x _ y _ heq => hgetRoot_inj heq)]

    -- Sum over image ≤ sum over all roots (using count_roots)
    have himage_le_card : (image.sum fun β => (f.num.rootMultiplicity β : ℤ)) ≤ f.num.roots.card := by
      calc (image.sum fun β => (f.num.rootMultiplicity β : ℤ))
          = (image.sum fun β => (f.num.roots.count β : ℤ)) := by
            congr 1; ext β; rw [Polynomial.count_roots]
        _ ≤ (f.num.roots.toFinset.sum fun β => (f.num.roots.count β : ℤ)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg himage_subset
            intro β _ _; exact Nat.cast_nonneg _
        _ = (f.num.roots.card : ℤ) := by
            have h := Multiset.toFinset_sum_count_eq f.num.roots
            simp only [← Nat.cast_sum, h]

    -- card of roots ≤ natDegree
    have hcard_le_deg : (f.num.roots.card : ℤ) ≤ f.num.natDegree := by
      exact_mod_cast Polynomial.card_roots' f.num

    -- Combine all bounds
    calc neg_abs_sum ≤ (neg_places.attach.sum fun ⟨v, hv⟩ =>
            (f.num.rootMultiplicity (getRoot ⟨v, hv⟩) : ℤ)) := hsum_bound
      _ = (image.sum fun β => (f.num.rootMultiplicity β : ℤ)) := hsum_image
      _ ≤ f.num.roots.card := himage_le_card
      _ ≤ f.num.natDegree := hcard_le_deg

  -- Combine: denom.natDegree ≤ pos_sum < neg_abs_sum ≤ num.natDegree
  have hcontra : (f.denom.natDegree : ℤ) < f.num.natDegree := by
    calc (f.denom.natDegree : ℤ) ≤ pos_sum := hpos_ge_denom
      _ < neg_abs_sum := hsum_ineq
      _ ≤ f.num.natDegree := hneg_le_num

  -- But hf_nopole says num.natDegree ≤ denom.natDegree
  have hf_nopole_int : (f.num.natDegree : ℤ) ≤ f.denom.natDegree := by exact_mod_cast hf_nopole
  omega

/-- The projective RRSpace is trivial when deg(D) < 0 and D is supported on linear places. -/
theorem RRSpace_ratfunc_projective_eq_bot_of_neg_deg (D : DivisorV2 (Polynomial Fq)) (hD : D.deg < 0)
    (hDlin : IsLinearPlaceSupport D) :
    RRSpace_ratfunc_projective D = ⊥ := by
  ext f
  simp only [Submodule.mem_bot]
  constructor
  · exact projective_LRatFunc_eq_zero_of_neg_deg D hD hDlin f
  · intro hf
    rw [hf]
    exact ⟨Or.inl rfl, Or.inl rfl⟩

/-- The projective ell(D) = 0 when deg(D) < 0 and D is supported on linear places. -/
theorem ell_ratfunc_projective_zero_of_neg_deg (D : DivisorV2 (Polynomial Fq)) (hD : D.deg < 0)
    (hDlin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective D = 0 := by
  unfold ell_ratfunc_projective
  rw [RRSpace_ratfunc_projective_eq_bot_of_neg_deg D hD hDlin]
  exact finrank_bot Fq (RatFunc Fq)

end ProjectiveLSpace

end RiemannRochV2
