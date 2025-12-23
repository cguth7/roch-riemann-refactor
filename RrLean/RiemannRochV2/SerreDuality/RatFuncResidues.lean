import RrLean.RiemannRochV2.ResidueTheory.ResidueTheorem
import Mathlib.Algebra.Polynomial.PartialFractions

/-!
# Residue Infrastructure for RatFunc Fq

This module provides residue sum operations and the residue theorem for
rational functions over finite fields.

## Main Definitions

* `residueSumFinite` : Sum of residues at all linear places (α : Fq)
* `residueSumTotal` : Finite sum + residue at infinity
* `residuePairing` : Bilinear pairing via residue sum of products

## Main Results

* `residueSumTotal_splits` : Residue theorem for split denominators
* `residuePairing_eq_zero_of_splits` : Pairing vanishes for split products

## Limitations

The residue sum only covers degree-1 places (linear factors over Fq).
For a complete treatment, residues at higher-degree irreducible places
would need traces to Fq. This is sufficient for genus 0 (P¹) applications
where all poles are linear.

## References

* Liu "Algebraic Geometry and Arithmetic Curves" Chapter 7
-/

noncomputable section

namespace RiemannRochV2

open RiemannRochV2.Residue
open Classical

variable {Fq : Type*} [Field Fq]

/-! ## Residue Sums -/

/-- Residue sum over all linear places for a rational function.

This sums res_α(f) over all α ∈ Fq (the linear places (X - α)).
For a finite field Fq, this is a finite sum.

Note: This captures residues at all degree-1 places only.
-/
def residueSumFinite [Fintype Fq] (f : RatFunc Fq) : Fq :=
  ∑ α : Fq, residueAt α f

/-- The finite residue sum is linear: respects addition. -/
theorem residueSumFinite_add [Fintype Fq] (f g : RatFunc Fq) :
    residueSumFinite (f + g) = residueSumFinite f + residueSumFinite g := by
  simp only [residueSumFinite, residueAt_add]
  rw [Finset.sum_add_distrib]

/-- The finite residue sum is linear: respects scalar multiplication. -/
theorem residueSumFinite_smul [Fintype Fq] (c : Fq) (f : RatFunc Fq) :
    residueSumFinite (c • f) = c * residueSumFinite f := by
  simp only [residueSumFinite, residueAt_smul]
  rw [← Finset.mul_sum]

/-- The finite residue sum as a linear map. -/
def residueSumFinite_linearMap [Fintype Fq] : RatFunc Fq →ₗ[Fq] Fq where
  toFun := residueSumFinite
  map_add' := residueSumFinite_add
  map_smul' := residueSumFinite_smul

/-- Total residue sum: linear places + infinity.

For the residue theorem, this should equal zero for any f ∈ RatFunc Fq
whose denominator splits into distinct linear factors.
-/
def residueSumTotal [Fintype Fq] (f : RatFunc Fq) : Fq :=
  residueSumFinite f + residueAtInfty f

/-- The total residue sum is linear. -/
theorem residueSumTotal_add [Fintype Fq] (f g : RatFunc Fq) :
    residueSumTotal (f + g) = residueSumTotal f + residueSumTotal g := by
  simp only [residueSumTotal, residueSumFinite_add, residueAtInfty_add]
  ring

/-- Residue theorem for simple poles: c/(X-α) has total residue 0. -/
theorem residueSumTotal_eq_zero_simple [Fintype Fq] (c : Fq) (α : Fq) :
    residueSumTotal (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) = 0 := by
  simp only [residueSumTotal]
  have h_finite : residueSumFinite (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) = c := by
    simp only [residueSumFinite]
    rw [← Finset.insert_erase (Finset.mem_univ α)]
    rw [Finset.sum_insert (Finset.notMem_erase α Finset.univ)]
    have h1 : residueAt α (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) = c :=
      residueAt_eq_residueAtLinear_simple α c
    rw [h1]
    have h2 : ∑ β ∈ Finset.univ.erase α,
              residueAt β (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) = 0 := by
      apply Finset.sum_eq_zero
      intro β hβ
      have hne : α ≠ β := by
        rw [Finset.mem_erase] at hβ
        exact hβ.1.symm
      exact residueAt_inv_X_sub_ne α β c hne
    rw [h2, add_zero]
  have h_infty : residueAtInfty (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) = -c :=
    residueAtInfty_smul_inv_X_sub α c
  rw [h_finite, h_infty]
  ring

/-- The total residue sum distributes over finite sums. -/
theorem residueSumTotal_sum [Fintype Fq] {ι : Type*} (s : Finset ι) (f : ι → RatFunc Fq) :
    residueSumTotal (∑ i ∈ s, f i) = ∑ i ∈ s, residueSumTotal (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simp only [residueSumTotal, residueSumFinite]
    rw [Finset.sum_eq_zero (fun α _ => residueAt_zero' (Fq := Fq) α)]
    simp [residueAtInfty_zero]
  | insert a s' ha ih =>
    simp only [Finset.sum_insert ha]
    rw [residueSumTotal_add, ih]

/-- Sum of simple poles has zero total residue. -/
theorem residueSumTotal_eq_zero_sum_simple [Fintype Fq] {ι : Type*} (s : Finset ι)
    (coeffs : ι → Fq) (poles : ι → Fq) :
    residueSumTotal (∑ i ∈ s, coeffs i • (RatFunc.X - RatFunc.C (poles i))⁻¹ : RatFunc Fq) = 0 := by
  rw [residueSumTotal_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact residueSumTotal_eq_zero_simple (coeffs i) (poles i)

/-- Polynomials have zero total residue. -/
theorem residueSumTotal_polynomial [Fintype Fq] (p : Polynomial Fq) :
    residueSumTotal (algebraMap (Polynomial Fq) (RatFunc Fq) p) = 0 := by
  simp only [residueSumTotal, residueSumFinite]
  have h_finite : ∑ α : Fq, residueAt α (algebraMap (Polynomial Fq) (RatFunc Fq) p) = 0 := by
    apply Finset.sum_eq_zero
    intro α _
    exact residueAt_polynomial α p
  rw [h_finite, residueAtInfty_polynomial, add_zero]

/-- Scalar multiplication for total residue sum. -/
theorem residueSumTotal_smul [Fintype Fq] (c : Fq) (f : RatFunc Fq) :
    residueSumTotal (c • f) = c * residueSumTotal f := by
  simp only [residueSumTotal]
  conv_lhs => rw [show residueSumFinite (c • f) = c * residueSumFinite f from residueSumFinite_smul c f]
  rw [residueAtInfty_smul, mul_add]

/-- The total residue sum as a linear map. -/
def residueSumTotal_linearMap [Fintype Fq] : RatFunc Fq →ₗ[Fq] Fq where
  toFun := residueSumTotal
  map_add' := residueSumTotal_add
  map_smul' := residueSumTotal_smul

/-! ## Partial Fractions Helpers -/

/-- Coprimality of distinct linear factors. -/
lemma isCoprime_X_sub_of_ne (α β : Fq) (h : α ≠ β) :
    IsCoprime (Polynomial.X - Polynomial.C α) (Polynomial.X - Polynomial.C β) :=
  Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr h).isUnit

/-- Constant divided by linear factor as scalar multiplication. -/
lemma const_div_X_sub_eq_smul (c α : Fq) :
    (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c)) /
    (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C α)) =
    c • (RatFunc.X - RatFunc.C α)⁻¹ := by
  rw [div_eq_mul_inv, Algebra.smul_def, RatFunc.algebraMap_eq_C]
  congr 1
  simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub]

/-- Polynomials of degree < 1 are constants. -/
lemma polynomial_degree_lt_one_eq_C (p : Polynomial Fq) (h : p.degree < 1) :
    ∃ c : Fq, p = Polynomial.C c := by
  have hle : p.degree ≤ 0 := by
    by_cases hp : p = 0
    · simp only [hp, Polynomial.degree_zero, bot_le]
    · have hne : p.degree ≠ ⊥ := Polynomial.degree_ne_bot.mpr hp
      obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hne
      rw [← hn] at h ⊢
      have h' : n < 1 := by simpa using h
      have h'' : n = 0 := Nat.lt_one_iff.mp h'
      simp [h'']
  exact ⟨p.coeff 0, Polynomial.eq_C_of_degree_le_zero hle⟩

/-- Pairwise coprimality of distinct linear factors. -/
lemma pairwise_coprime_X_sub_of_injective {ι : Type*} (poles : ι → Fq) (s : Finset ι)
    (hinj : Set.InjOn poles s) :
    Set.Pairwise (s : Set ι) fun i j => IsCoprime
      (Polynomial.X - Polynomial.C (poles i))
      (Polynomial.X - Polynomial.C (poles j)) := by
  intro i hi j hj hij
  apply isCoprime_X_sub_of_ne
  intro heq
  exact hij (hinj hi hj heq)

/-! ## Residue Theorem for Split Denominators -/

/-- Residue theorem for two distinct poles. -/
theorem residueSumTotal_two_poles [Fintype Fq] (f : Polynomial Fq) (α β : Fq) (hne : α ≠ β) :
    residueSumTotal ((algebraMap _ (RatFunc Fq) f) /
                     ((RatFunc.X - RatFunc.C α) * (RatFunc.X - RatFunc.C β))) = 0 := by
  have hcop : IsCoprime (Polynomial.X - Polynomial.C α) (Polynomial.X - Polynomial.C β) :=
    isCoprime_X_sub_of_ne α β hne
  have hmonic1 : (Polynomial.X - Polynomial.C α).Monic := Polynomial.monic_X_sub_C α
  have hmonic2 : (Polynomial.X - Polynomial.C β).Monic := Polynomial.monic_X_sub_C β
  obtain ⟨q, r₁, r₂, hdeg1, hdeg2, heq⟩ :=
    div_eq_quo_add_rem_div_add_rem_div Fq (RatFunc Fq) f hmonic1 hmonic2 hcop
  have hdeg_Xα : (Polynomial.X - Polynomial.C α).degree = 1 := Polynomial.degree_X_sub_C α
  have hdeg_Xβ : (Polynomial.X - Polynomial.C β).degree = 1 := Polynomial.degree_X_sub_C β
  rw [hdeg_Xα] at hdeg1
  rw [hdeg_Xβ] at hdeg2
  obtain ⟨c₁, hc₁⟩ := polynomial_degree_lt_one_eq_C r₁ hdeg1
  obtain ⟨c₂, hc₂⟩ := polynomial_degree_lt_one_eq_C r₂ hdeg2
  rw [hc₁, hc₂] at heq
  have h_c₁_div : (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c₁)) /
                  (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C α)) =
                  c₁ • (RatFunc.X - RatFunc.C α)⁻¹ := const_div_X_sub_eq_smul c₁ α
  have h_c₂_div : (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c₂)) /
                  (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C β)) =
                  c₂ • (RatFunc.X - RatFunc.C β)⁻¹ := const_div_X_sub_eq_smul c₂ β
  rw [h_c₁_div, h_c₂_div] at heq
  have hXα : RatFunc.X - RatFunc.C α =
             (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C α)) := by
    simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub]
  have hXβ : RatFunc.X - RatFunc.C β =
             (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C β)) := by
    simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub]
  rw [hXα, hXβ, heq]
  rw [residueSumTotal_add, residueSumTotal_add]
  rw [residueSumTotal_polynomial q]
  rw [residueSumTotal_eq_zero_simple c₁ α]
  rw [residueSumTotal_eq_zero_simple c₂ β]
  ring

/-- Residue theorem for n distinct linear poles. -/
theorem residueSumTotal_n_poles_finset [Fintype Fq] (f : Polynomial Fq) (poles : Finset Fq) :
    residueSumTotal ((algebraMap _ (RatFunc Fq) f) /
                     (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) = 0 := by
  induction poles using Finset.induction_on generalizing f with
  | empty =>
    simp only [Finset.prod_empty]
    rw [div_one]
    exact residueSumTotal_polynomial f
  | insert α s hα ih =>
    rw [Finset.prod_insert hα]
    set g₁ := Polynomial.X - Polynomial.C α with hg₁_def
    set g₂ := ∏ β ∈ s, (Polynomial.X - Polynomial.C β) with hg₂_def
    by_cases hs : s = ∅
    · subst hs
      simp only [Finset.prod_empty, mul_one] at hg₂_def ⊢
      have hmonic1 : g₁.Monic := Polynomial.monic_X_sub_C α
      have hmonic2 : (1 : Polynomial Fq).Monic := Polynomial.monic_one
      have hcop : IsCoprime g₁ (1 : Polynomial Fq) := isCoprime_one_right
      obtain ⟨q, r₁, r₂, hdeg1, _, heq⟩ :=
        div_eq_quo_add_rem_div_add_rem_div Fq (RatFunc Fq) f hmonic1 hmonic2 hcop
      have hdeg_g1 : g₁.degree = 1 := Polynomial.degree_X_sub_C α
      rw [hdeg_g1] at hdeg1
      obtain ⟨c, hc⟩ := polynomial_degree_lt_one_eq_C r₁ hdeg1
      rw [hc] at heq
      have h_c_div : (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c)) /
                      (algebraMap (Polynomial Fq) (RatFunc Fq) g₁) =
                      c • (RatFunc.X - RatFunc.C α)⁻¹ := by
        rw [hg₁_def]; exact const_div_X_sub_eq_smul c α
      simp only [mul_one, map_one, div_one] at heq
      rw [h_c_div] at heq
      have hXα : RatFunc.X - RatFunc.C α =
                 (algebraMap (Polynomial Fq) (RatFunc Fq) g₁) := by
        rw [hg₁_def]; simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub]
      rw [hXα, heq, residueSumTotal_add, residueSumTotal_add]
      rw [residueSumTotal_polynomial q]
      rw [residueSumTotal_eq_zero_simple c α]
      rw [residueSumTotal_polynomial r₂]
      ring
    · have hmonic1 : g₁.Monic := Polynomial.monic_X_sub_C α
      have hmonic2 : g₂.Monic := by
        rw [hg₂_def]
        apply Polynomial.monic_prod_of_monic
        intro β _
        exact Polynomial.monic_X_sub_C β
      have hcop : IsCoprime g₁ g₂ := by
        rw [hg₁_def, hg₂_def]
        apply IsCoprime.prod_right
        intro β hβ
        apply isCoprime_X_sub_of_ne
        intro heq
        rw [heq] at hα
        exact hα hβ
      obtain ⟨q, r₁, r₂, hdeg1, _, heq⟩ :=
        div_eq_quo_add_rem_div_add_rem_div Fq (RatFunc Fq) f hmonic1 hmonic2 hcop
      have hdeg_g1 : g₁.degree = 1 := Polynomial.degree_X_sub_C α
      rw [hdeg_g1] at hdeg1
      obtain ⟨c, hc⟩ := polynomial_degree_lt_one_eq_C r₁ hdeg1
      rw [hc] at heq
      have h_c_div : (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c)) /
                      (algebraMap (Polynomial Fq) (RatFunc Fq) g₁) =
                      c • (RatFunc.X - RatFunc.C α)⁻¹ := by
        rw [hg₁_def]; exact const_div_X_sub_eq_smul c α
      rw [h_c_div] at heq
      have hXα : RatFunc.X - RatFunc.C α =
                 (algebraMap (Polynomial Fq) (RatFunc Fq) g₁) := by
        rw [hg₁_def]; simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub]
      have hprod_eq : ∏ β ∈ s, (RatFunc.X - RatFunc.C β) =
                      (algebraMap (Polynomial Fq) (RatFunc Fq) g₂) := by
        rw [hg₂_def, map_prod]
        apply Finset.prod_congr rfl
        intro β _
        simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub]
      rw [hXα, hprod_eq, heq]
      rw [residueSumTotal_add, residueSumTotal_add]
      rw [residueSumTotal_polynomial q]
      rw [residueSumTotal_eq_zero_simple c α]
      simp only [zero_add]
      convert (ih r₂) using 1
      rw [hprod_eq]

/-- Main residue theorem: split denominators give zero total residue. -/
theorem residueSumTotal_splits [Fintype Fq] (f : RatFunc Fq)
    (h : ∃ (p : Polynomial Fq) (poles : Finset Fq),
         f = (algebraMap _ (RatFunc Fq) p) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    residueSumTotal f = 0 := by
  obtain ⟨p, poles, hf⟩ := h
  rw [hf]
  exact residueSumTotal_n_poles_finset p poles

/-! ## Residue Pairing -/

/-- The pairing on K × K via residue sum of products. -/
def residuePairing [Fintype Fq] (g f : RatFunc Fq) : Fq :=
  residueSumTotal (g * f)

theorem residuePairing_add_left [Fintype Fq] (g₁ g₂ f : RatFunc Fq) :
    residuePairing (g₁ + g₂) f = residuePairing g₁ f + residuePairing g₂ f := by
  simp only [residuePairing, add_mul, residueSumTotal_add]

theorem residuePairing_add_right [Fintype Fq] (g f₁ f₂ : RatFunc Fq) :
    residuePairing g (f₁ + f₂) = residuePairing g f₁ + residuePairing g f₂ := by
  simp only [residuePairing, mul_add, residueSumTotal_add]

theorem residuePairing_smul_left [Fintype Fq] (c : Fq) (g f : RatFunc Fq) :
    residuePairing (c • g) f = c * residuePairing g f := by
  simp only [residuePairing]
  rw [Algebra.smul_def, RatFunc.algebraMap_eq_C, mul_assoc]
  conv_lhs => rw [show RatFunc.C c * (g * f) = c • (g * f) by
    rw [Algebra.smul_def, RatFunc.algebraMap_eq_C]]
  exact residueSumTotal_smul c (g * f)

theorem residuePairing_smul_right [Fintype Fq] (c : Fq) (g f : RatFunc Fq) :
    residuePairing g (c • f) = c * residuePairing g f := by
  simp only [residuePairing]
  rw [Algebra.smul_def, RatFunc.algebraMap_eq_C, ← mul_assoc, mul_comm g (RatFunc.C c), mul_assoc]
  conv_lhs => rw [show RatFunc.C c * (g * f) = c • (g * f) by
    rw [Algebra.smul_def, RatFunc.algebraMap_eq_C]]
  exact residueSumTotal_smul c (g * f)

/-- The residue pairing as a bilinear map. -/
def residuePairing_bilinear [Fintype Fq] : RatFunc Fq →ₗ[Fq] RatFunc Fq →ₗ[Fq] Fq where
  toFun := fun g =>
    { toFun := fun f => residuePairing g f
      map_add' := fun f₁ f₂ => residuePairing_add_right g f₁ f₂
      map_smul' := fun c f => residuePairing_smul_right c g f }
  map_add' := fun g₁ g₂ => by
    ext f
    exact residuePairing_add_left g₁ g₂ f
  map_smul' := fun c g => by
    ext f
    exact residuePairing_smul_left c g f

/-- The residue pairing vanishes for products with split denominators. -/
theorem residuePairing_eq_zero_of_splits [Fintype Fq] (g f : RatFunc Fq)
    (h : ∃ (p : Polynomial Fq) (poles : Finset Fq),
         g * f = (algebraMap _ (RatFunc Fq) p) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    residuePairing g f = 0 :=
  residueSumTotal_splits (g * f) h

/-- Polynomial on right gives zero pairing (when left has split denominator). -/
theorem residuePairing_polynomial_right [Fintype Fq] (g : RatFunc Fq) (p : Polynomial Fq)
    (hg : ∃ (q : Polynomial Fq) (poles : Finset Fq),
          g = (algebraMap _ (RatFunc Fq) q) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    residuePairing g (algebraMap _ (RatFunc Fq) p) = 0 := by
  obtain ⟨q, poles, hg_eq⟩ := hg
  apply residuePairing_eq_zero_of_splits
  use q * p, poles
  rw [hg_eq, div_mul_eq_mul_div, map_mul]

/-- Polynomial on left gives zero pairing (when right has split denominator). -/
theorem residuePairing_polynomial_left [Fintype Fq] (p : Polynomial Fq) (f : RatFunc Fq)
    (hf : ∃ (q : Polynomial Fq) (poles : Finset Fq),
          f = (algebraMap _ (RatFunc Fq) q) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    residuePairing (algebraMap _ (RatFunc Fq) p) f = 0 := by
  obtain ⟨q, poles, hf_eq⟩ := hf
  apply residuePairing_eq_zero_of_splits
  use p * q, poles
  rw [hf_eq, mul_div_assoc', map_mul]

end RiemannRochV2
