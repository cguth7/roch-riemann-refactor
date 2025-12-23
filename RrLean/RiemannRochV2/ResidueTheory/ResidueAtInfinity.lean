import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import RrLean.RiemannRochV2.Core.Basic

/-!
# Residue at Infinity for RatFunc Fq

The residue at infinity is computed by substituting X ↦ 1/Y and extracting
the coefficient of Y^{-1}. For f(X) = P(X)/Q(X), we consider f(1/Y) · (appropriate power).

Mathematically: res_∞(f) = -res_X(f(1/X) · X⁻²)

The minus sign comes from the differential: d(1/Y) = -Y⁻² dY.

## Implementation

For a rational function f = p/q (in lowest terms), the residue at infinity is the
coefficient of X^{-1} in the Laurent expansion at X = ∞.

Mathematical derivation:
- Write f = (polynomial part) + (proper fraction) where the proper fraction is rem/q
  with deg(rem) < deg(q).
- The polynomial part has no residue at ∞ (no X^{-1} term when expanded in 1/X).
- For the proper fraction rem/q:
  - If deg(rem) = deg(q) - 1, the leading term at ∞ is X^{-1} with coefficient
    -leadingCoeff(rem)/leadingCoeff(q).
  - If deg(rem) < deg(q) - 1, there is no X^{-1} term, so residue is 0.

## References

- Rosen "Number Theory in Function Fields" Chapter 4
- Stichtenoth "Algebraic Function Fields and Codes" Section 1.4
-/

noncomputable section

open scoped LaurentSeries
open HahnSeries Polynomial

namespace RiemannRochV2.Residue

variable {Fq : Type*} [Field Fq]

/-- The residue at infinity.

For a rational function f = p/q (in lowest terms), the residue at infinity is the
coefficient of X^{-1} in the Laurent expansion at X = ∞.

Examples:
- res_∞(1/(X-1)) = -1  (simple pole at ∞)
- res_∞(1/(X²-1)) = 0  (no pole at ∞, f → 0 too fast)
- res_∞(X/(X²-1)) = -1 (simple pole at ∞)
- res_∞(X) = 0         (pole at ∞ but no X^{-1} term in expansion)
-/
def residueAtInfty (f : RatFunc Fq) : Fq :=
  let p := f.num
  let q := f.denom
  -- Compute the proper fraction part: rem = p mod q
  let rem := p % q
  -- Check if deg(rem) + 1 = deg(q), i.e., the proper fraction has a simple pole at ∞
  if rem.natDegree + 1 = q.natDegree then
    -(rem.leadingCoeff / q.leadingCoeff)
  else
    0

@[simp]
theorem residueAtInfty_zero : residueAtInfty (0 : RatFunc Fq) = 0 := by
  simp only [residueAtInfty]
  -- For f = 0: num = 0, denom = 1
  -- rem = 0 % 1 = 0, deg(rem) = 0, deg(denom) = 0
  -- 0 + 1 ≠ 0, so we get 0
  have h1 : (0 : RatFunc Fq).num = 0 := RatFunc.num_zero
  have h2 : (0 : RatFunc Fq).denom = 1 := RatFunc.denom_zero
  simp only [h1, h2, EuclideanDomain.zero_mod, Polynomial.natDegree_zero, Polynomial.natDegree_one]
  -- The if condition is 0 + 1 = 0, which is false
  norm_num

/-- The residue at infinity of a polynomial is 0.

This is because polynomials have no pole at infinity in the "residue" sense:
expanding a polynomial in powers of 1/X gives only non-positive powers of 1/X,
hence no X^{-1} term.
-/
theorem residueAtInfty_polynomial (p : Polynomial Fq) :
    residueAtInfty (algebraMap (Polynomial Fq) (RatFunc Fq) p) = 0 := by
  simp only [residueAtInfty]
  -- For a polynomial: num = normalize(p), denom = 1
  -- rem = num % 1 = 0
  have hdenom : (algebraMap (Polynomial Fq) (RatFunc Fq) p).denom = 1 := RatFunc.denom_algebraMap _
  simp only [hdenom, EuclideanDomain.mod_one, Polynomial.natDegree_zero, Polynomial.natDegree_one]
  norm_num

/-- The residue at infinity of 1/(X - c) is -1 for any c ∈ Fq.

This is a fundamental test case: 1/(X - c) has a simple pole at X = c (finite)
and a simple pole at X = ∞. The residue at ∞ is -1, which together with the
residue +1 at X = c gives a total residue sum of 0.

Proof outline:
- For 1/(X - c): num = 1, denom = X - c
- rem = 1 % (X - c) = 1 (since deg(1) < deg(X - c))
- deg(rem) + 1 = 0 + 1 = 1 = deg(X - c) ✓
- residue = -leadingCoeff(1) / leadingCoeff(X - c) = -1/1 = -1
-/
theorem residueAtInfty_inv_X_sub (c : Fq) :
    residueAtInfty ((RatFunc.X - RatFunc.C c)⁻¹ : RatFunc Fq) = -1 := by
  -- Express the inverse as 1 / (X - C c)
  have hXc_ne : (Polynomial.X - Polynomial.C c) ≠ (0 : Polynomial Fq) := by
    intro h
    have hdeg := congr_arg Polynomial.natDegree h
    simp only [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_zero] at hdeg
    omega
  have hinv_eq : (RatFunc.X - RatFunc.C c)⁻¹ =
      (algebraMap (Polynomial Fq) (RatFunc Fq) 1) /
      (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C c)) := by
    rw [map_one, RatFunc.X, (RatFunc.algebraMap_C c).symm, ← map_sub]
    ring
  simp only [residueAtInfty, hinv_eq]
  -- Compute num and denom using the simp lemmas
  rw [RatFunc.num_div, RatFunc.denom_div (1 : Polynomial Fq) hXc_ne]
  -- Simplify gcd and div_one
  simp only [gcd_one_left, EuclideanDomain.div_one]
  -- leadingCoeff(X - C c) = 1
  simp only [Polynomial.leadingCoeff_X_sub_C, inv_one, Polynomial.C_1, one_mul]
  -- Now rem = 1 % (X - C c) = 1
  have hrem : (1 : Polynomial Fq) % (Polynomial.X - Polynomial.C c) = 1 := by
    rw [Polynomial.mod_eq_self_iff hXc_ne]
    rw [Polynomial.degree_one, Polynomial.degree_X_sub_C]
    exact zero_lt_one
  simp only [hrem, Polynomial.natDegree_one, Polynomial.natDegree_X_sub_C, zero_add]
  -- if 1 = 1 then ... else ... = -1
  norm_num

/-- Helper: Express residueAtInfty in terms of coefficient extraction.

When denom.natDegree ≥ 1, the residue is the negated coefficient of X^{deg(denom)-1}
in the remainder. This is key for proving additivity.
-/
lemma residueAtInfty_eq_neg_coeff (f : RatFunc Fq) :
    residueAtInfty f = -((f.num % f.denom).coeff (f.denom.natDegree - 1)) := by
  simp only [residueAtInfty]
  -- Since denom is monic, leadingCoeff = 1
  have hmonic : f.denom.Monic := RatFunc.monic_denom f
  have hlc : f.denom.leadingCoeff = 1 := hmonic
  -- Let rem = f.num % f.denom
  set rem := f.num % f.denom with hrem_def
  -- Case split on whether deg(rem) + 1 = deg(denom)
  by_cases hdeg : rem.natDegree + 1 = f.denom.natDegree
  · -- Case: deg(rem) + 1 = deg(denom), so the X^{-1} coefficient is nonzero
    simp only [hdeg, ↓reduceIte, hlc, div_one]
    -- rem.coeff(denom.natDegree - 1) = rem.leadingCoeff when deg(rem) = denom.natDegree - 1
    have hdeg' : rem.natDegree = f.denom.natDegree - 1 := by omega
    simp only [hdeg', Polynomial.leadingCoeff]
  · -- Case: deg(rem) + 1 ≠ deg(denom)
    simp only [hdeg, ↓reduceIte]
    -- The coefficient at position denom.natDegree - 1 is 0 because deg(rem) < that
    -- Need: rem.coeff(denom.natDegree - 1) = 0
    by_cases hdenom_pos : f.denom.natDegree = 0
    · -- If denom has degree 0, then denom = 1 (since monic), so rem = 0
      simp only [hdenom_pos]
      -- 0 - 1 in ℕ is 0
      have hsub : (0 : ℕ) - 1 = 0 := rfl
      rw [hsub]
      -- f is a polynomial, so num % 1 = 0
      have hdenom_eq : f.denom = 1 := by
        apply Polynomial.eq_one_of_monic_natDegree_zero hmonic hdenom_pos
      have hrem_eq : rem = 0 := by
        rw [hrem_def, hdenom_eq, EuclideanDomain.mod_one]
      rw [hrem_eq, Polynomial.coeff_zero, neg_zero]
    · -- denom.natDegree ≥ 1
      have hdenom_ge : f.denom.natDegree ≥ 1 := Nat.one_le_iff_ne_zero.mpr hdenom_pos
      -- rem has degree < denom.natDegree (by mod property)
      -- If hdeg fails, then rem.natDegree ≠ denom.natDegree - 1
      -- Combined with rem.natDegree < denom.natDegree, we get rem.natDegree < denom.natDegree - 1
      have hrem_deg : rem.natDegree < f.denom.natDegree := by
        apply Polynomial.natDegree_mod_lt f.num hdenom_pos
      have hrem_small : rem.natDegree < f.denom.natDegree - 1 := by
        omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hrem_small]
      ring

/-- Coefficient extraction for products at the "critical" index.

For a proper fraction r/d₁ (deg r < deg d₁) multiplied by a monic polynomial d₂,
the coefficient at index (deg d₁ - 1 + deg d₂) equals r.coeff(deg d₁ - 1).
-/
lemma coeff_mul_at_sum_sub_one {r d₁ d₂ : Polynomial Fq}
    (hr : r.natDegree < d₁.natDegree) (hd₂_monic : d₂.Monic) :
    (r * d₂).coeff (d₁.natDegree - 1 + d₂.natDegree) = r.coeff (d₁.natDegree - 1) := by
  by_cases hd₁ : d₁.natDegree = 0
  · -- If d₁ has degree 0, then r has degree < 0 which is impossible, so r = 0
    have hr_zero : r = 0 := by
      by_contra h
      have : r.natDegree ≥ 0 := Nat.zero_le _
      omega
    simp [hr_zero, hd₁]
  have hd₁_pos : 0 < d₁.natDegree := Nat.zero_lt_of_ne_zero hd₁
  have hr_bound : r.natDegree ≤ d₁.natDegree - 1 := by omega
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hr_bound (le_refl _)]
  simp [hd₂_monic]

open Classical in
/-- Auxiliary function for residue at infinity on unreduced fractions.
For p/q (not necessarily reduced), extracts the coefficient at the critical index.
This is additive in p for fixed q, which is key for proving residueAtInfty_add. -/
noncomputable def residueAtInftyAux (p q : Polynomial Fq) : Fq :=
  if q = 0 then 0
  else -((p % q).coeff (q.natDegree - 1))

/-- residueAtInftyAux is additive in the numerator for fixed denominator. -/
lemma residueAtInftyAux_add (p₁ p₂ q : Polynomial Fq) :
    residueAtInftyAux (p₁ + p₂) q = residueAtInftyAux p₁ q + residueAtInftyAux p₂ q := by
  unfold residueAtInftyAux
  by_cases hq : q = 0
  · simp [hq]
  simp only [if_neg hq]
  rw [Polynomial.add_mod, Polynomial.coeff_add]
  ring

/-- residueAtInftyAux equals residueAtInfty for reduced fractions. -/
lemma residueAtInfty_eq_aux (f : RatFunc Fq) :
    residueAtInfty f = residueAtInftyAux f.num f.denom := by
  rw [residueAtInfty_eq_neg_coeff]
  unfold residueAtInftyAux
  simp only [if_neg (RatFunc.denom_ne_zero f)]

/-- Key scaling lemma: multiplying both num and denom by a monic polynomial preserves residue.
This uses coeff_mul_at_sum_sub_one for the coefficient extraction. -/
lemma residueAtInftyAux_mul_monic (p q k : Polynomial Fq)
    (hq : q ≠ 0) (hq_monic : q.Monic) (hk : k.Monic) (hk_ne : k ≠ 0) :
    residueAtInftyAux (p * k) (q * k) = residueAtInftyAux p q := by
  unfold residueAtInftyAux
  have hqk_ne : q * k ≠ 0 := mul_ne_zero hq hk_ne
  simp only [if_neg hqk_ne, if_neg hq]
  -- Key lemma: (p * k) % (q * k) = (p % q) * k for monic q, k
  -- This follows from uniqueness of polynomial division
  have hqk_monic : (q * k).Monic := hq_monic.mul hk
  -- Step 1: Express mod using modByMonic (they're equal for monic divisors)
  rw [← Polynomial.modByMonic_eq_mod p hq_monic]
  rw [← Polynomial.modByMonic_eq_mod (p * k) hqk_monic]
  -- Step 2: Prove (p * k) %ₘ (q * k) = (p %ₘ q) * k using uniqueness
  -- We have: p = (p /ₘ q) * q + (p %ₘ q) (modByMonic_add_div)
  -- Multiply by k: p * k = (p /ₘ q) * (q * k) + (p %ₘ q) * k
  have hdiv : (p %ₘ q) * k + (q * k) * (p /ₘ q) = p * k := by
    have h := Polynomial.modByMonic_add_div p hq_monic
    calc (p %ₘ q) * k + (q * k) * (p /ₘ q)
        = (p %ₘ q) * k + q * (p /ₘ q) * k := by ring
      _ = (p %ₘ q + q * (p /ₘ q)) * k := by ring
      _ = p * k := by rw [h]
  -- Step 3: Check degree condition: deg((p %ₘ q) * k) < deg(q * k)
  have hdeg : ((p %ₘ q) * k).degree < (q * k).degree := by
    by_cases hp_mod : p %ₘ q = 0
    · simp only [hp_mod, zero_mul]
      exact Ne.bot_lt (fun h => hqk_monic.ne_zero (Polynomial.degree_eq_bot.mp h))
    · rw [hk.degree_mul, hk.degree_mul]
      have hk_deg_ne_bot : k.degree ≠ ⊥ := Polynomial.degree_eq_bot.not.mpr hk_ne
      exact WithBot.add_lt_add_right hk_deg_ne_bot (Polynomial.degree_modByMonic_lt p hq_monic)
  -- Step 4: Apply uniqueness
  -- div_modByMonic_unique {f g} (q r) (hg : Monic g) (h : r + g * q = f ∧ deg r < deg g)
  -- gives: f /ₘ g = q ∧ f %ₘ g = r
  -- Here: f = p * k, g = q * k, quotient = p /ₘ q, remainder = (p %ₘ q) * k
  have huniq := Polynomial.div_modByMonic_unique (p /ₘ q) ((p %ₘ q) * k) hqk_monic ⟨hdiv, hdeg⟩
  rw [huniq.2]
  -- Now prove the coefficient extraction gives the same result
  -- (q * k).natDegree = q.natDegree + k.natDegree and use coeff_mul_at_sum_sub_one
  have hdeg_eq : (q * k).natDegree = q.natDegree + k.natDegree := hq_monic.natDegree_mul hk
  rw [hdeg_eq]
  -- Need: ((p %ₘ q) * k).coeff(q.natDegree + k.natDegree - 1) = (p %ₘ q).coeff(q.natDegree - 1)
  by_cases hq_deg : q.natDegree = 0
  · -- If q has degree 0, then q = 1 (since monic), so p %ₘ q = 0
    have hq_eq : q = 1 := Polynomial.eq_one_of_monic_natDegree_zero hq_monic hq_deg
    simp only [hq_eq, Polynomial.modByMonic_one, zero_mul, Polynomial.coeff_zero]
  · -- q.natDegree ≥ 1, so we can use coeff_mul_at_sum_sub_one
    have hq_pos : 0 < q.natDegree := Nat.pos_of_ne_zero hq_deg
    -- q ≠ 1 since q.natDegree ≠ 0
    have hq_ne_one : q ≠ 1 := fun h => hq_deg (by simp [h])
    have hmod_deg : (p %ₘ q).natDegree < q.natDegree := by
      by_cases hp_mod : p %ₘ q = 0
      · simp only [hp_mod, Polynomial.natDegree_zero]; exact hq_pos
      · exact Polynomial.natDegree_modByMonic_lt p hq_monic hq_ne_one
    -- Rewrite: q.natDegree + k.natDegree - 1 = (q.natDegree - 1) + k.natDegree (for q.natDegree ≥ 1)
    have hsub : q.natDegree + k.natDegree - 1 = (q.natDegree - 1) + k.natDegree := by omega
    rw [hsub, coeff_mul_at_sum_sub_one hmod_deg hk]

/-- The residue at infinity is additive.

Proof strategy using auxiliary function:
1. Convert to residueAtInftyAux using residueAtInfty_eq_aux
2. Use scaling (residueAtInftyAux_mul_monic) to express everything over common denominator
3. Use additivity of residueAtInftyAux in the numerator
4. Show the result equals residueAtInfty(f+g)

Key insight: The reduced form of f+g may have a different denominator than d_f * d_g,
but the residue is invariant under multiplying num/denom by the same monic polynomial
(or dividing by a common monic factor).
-/
theorem residueAtInfty_add (f g : RatFunc Fq) :
    residueAtInfty (f + g) = residueAtInfty f + residueAtInfty g := by
  -- Convert to auxiliary function
  rw [residueAtInfty_eq_aux f, residueAtInfty_eq_aux g, residueAtInfty_eq_aux (f + g)]
  -- Scale f and g to common denominator
  have hf_denom_monic : f.denom.Monic := RatFunc.monic_denom f
  have hg_denom_monic : g.denom.Monic := RatFunc.monic_denom g
  have hfg_denom_monic : (f + g).denom.Monic := RatFunc.monic_denom (f + g)
  have hf_denom_ne : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hg_denom_ne : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hfg_denom_ne : (f + g).denom ≠ 0 := RatFunc.denom_ne_zero (f + g)
  -- Scale f by g.denom and g by f.denom
  have h1 : residueAtInftyAux f.num f.denom = residueAtInftyAux (f.num * g.denom) (f.denom * g.denom) :=
    (residueAtInftyAux_mul_monic f.num f.denom g.denom hf_denom_ne hf_denom_monic hg_denom_monic hg_denom_ne).symm
  have h2 : residueAtInftyAux g.num g.denom = residueAtInftyAux (g.num * f.denom) (g.denom * f.denom) :=
    (residueAtInftyAux_mul_monic g.num g.denom f.denom hg_denom_ne hg_denom_monic hf_denom_monic hf_denom_ne).symm
  -- Rewrite g.denom * f.denom = f.denom * g.denom
  rw [mul_comm g.denom f.denom] at h2
  rw [h1, h2]
  -- Use additivity: the sum is residueAtInftyAux (f.num * g.denom + g.num * f.denom) (f.denom * g.denom)
  rw [← residueAtInftyAux_add]
  -- Now relate unreduced form to reduced form using num_denom_add
  -- From num_denom_add: (f + g).num * (f.denom * g.denom) = (f.num * g.denom + f.denom * g.num) * (f + g).denom
  have hrel := RatFunc.num_denom_add f g
  -- This is: (f + g).num * (f.denom * g.denom) = (f.num * g.denom + f.denom * g.num) * (f + g).denom
  -- Reorder the unreduced numerator to match
  have hreorder : f.num * g.denom + g.num * f.denom = f.num * g.denom + f.denom * g.num := by ring
  rw [hreorder]
  -- Let d = f.denom * g.denom (unreduced denom), d' = (f+g).denom (reduced denom)
  -- Let n = f.num * g.denom + f.denom * g.num (unreduced num), n' = (f+g).num (reduced num)
  -- From hrel: n' * d = n * d'
  -- Since gcd(n', d') = 1, we have d' | d. Let k = d / d'.
  -- Then d = d' * k and n = n' * k.
  -- By residueAtInftyAux_mul_monic: residueAtInftyAux (n' * k) (d' * k) = residueAtInftyAux n' d'
  -- Need to show (f+g).denom divides (f.denom * g.denom)
  have hdiv : (f + g).denom ∣ f.denom * g.denom := by
    -- Since (f+g).num and (f+g).denom are coprime and n' * d = n * d', we have d' | d
    have hcoprime : IsCoprime (f + g).num (f + g).denom := RatFunc.isCoprime_num_denom (f + g)
    -- From hrel: (f + g).num * (f.denom * g.denom) = n * (f + g).denom
    -- So (f + g).denom | (f + g).num * (f.denom * g.denom)
    -- Since gcd((f+g).num, (f+g).denom) = 1, (f+g).denom | (f.denom * g.denom)
    have hdvd : (f + g).denom ∣ (f + g).num * (f.denom * g.denom) := by
      rw [hrel]; exact dvd_mul_left _ _
    exact (hcoprime.symm.dvd_of_dvd_mul_left hdvd)
  -- Get the quotient k
  obtain ⟨k, hk_eq⟩ := hdiv
  -- Show k is monic (since d and d' are monic)
  have hk_monic : k.Monic := by
    have hd_monic : (f.denom * g.denom).Monic := hf_denom_monic.mul hg_denom_monic
    rw [hk_eq] at hd_monic
    exact Polynomial.Monic.of_mul_monic_left hfg_denom_monic hd_monic
  have hk_ne : k ≠ 0 := hk_monic.ne_zero
  -- From hrel: (f + g).num * (f.denom * g.denom) = n * (f + g).denom
  -- Substitute (f.denom * g.denom) = (f + g).denom * k:
  -- (f + g).num * ((f + g).denom * k) = n * (f + g).denom
  -- (f + g).num * k * (f + g).denom = n * (f + g).denom
  -- Cancel (f + g).denom (nonzero): (f + g).num * k = n
  have hn_eq : f.num * g.denom + f.denom * g.num = (f + g).num * k := by
    have h := hrel
    rw [hk_eq] at h
    -- h : (f + g).num * ((f + g).denom * k) = (f.num * g.denom + f.denom * g.num) * (f + g).denom
    -- Need to cancel (f + g).denom from both sides
    have hne : (f + g).denom ≠ 0 := RatFunc.denom_ne_zero (f + g)
    -- Rearrange h: (f + g).num * k * (f + g).denom = (f.num * g.denom + f.denom * g.num) * (f + g).denom
    have h' : (f.num * g.denom + f.denom * g.num) * (f + g).denom = (f + g).num * k * (f + g).denom := by
      calc (f.num * g.denom + f.denom * g.num) * (f + g).denom
          = (f + g).num * ((f + g).denom * k) := h.symm
        _ = (f + g).num * (k * (f + g).denom) := by ring
        _ = (f + g).num * k * (f + g).denom := by ring
    exact mul_right_cancel₀ hne h'
  -- Now use residueAtInftyAux_mul_monic
  rw [hn_eq, hk_eq]
  exact (residueAtInftyAux_mul_monic (f + g).num (f + g).denom k hfg_denom_ne hfg_denom_monic hk_monic hk_ne).symm

open Classical in
/-- The residue at infinity respects scalar multiplication.

For c ∈ Fq and f ∈ RatFunc Fq, res_∞(c • f) = c * res_∞(f).

Proof idea: Express c • f = (C c) * f and use the structure of residueAtInfty.
The key steps are:
1. (c • f).num = C c * f.num and (c • f).denom = f.denom (via coprimality)
2. (C c * p) % q = C c * (p % q) (scalar multiplication commutes with remainder)
3. leadingCoeff(C c * p) = c * leadingCoeff(p)
4. natDegree(C c * p) = natDegree(p) for c ≠ 0
-/
theorem residueAtInfty_smul (c : Fq) (f : RatFunc Fq) :
    residueAtInfty (c • f) = c * residueAtInfty f := by
  by_cases hc : c = 0
  · simp only [hc, zero_smul, residueAtInfty_zero, zero_mul]
  by_cases hf : f = 0
  · simp only [hf, smul_zero, residueAtInfty_zero, mul_zero]
  -- c is a unit, hence scalar multiplication by c is regular
  have hc_unit : IsUnit c := Ne.isUnit hc
  have hCc_unit : IsUnit (Polynomial.C c) := Polynomial.isUnit_C.mpr hc_unit
  have hc_reg : IsSMulRegular Fq c := hc_unit.isSMulRegular Fq
  -- Express c • f as (C c * f.num) / f.denom via the algebra structure
  have hsmul_eq : (c • f : RatFunc Fq) =
      algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c * f.num) /
      algebraMap (Polynomial Fq) (RatFunc Fq) f.denom := by
    conv_lhs => rw [Algebra.smul_def c f, RatFunc.algebraMap_eq_C, ← RatFunc.num_div_denom f]
    rw [← RatFunc.algebraMap_C c, mul_div_assoc', ← map_mul]
  -- Key: gcd(C c * f.num, f.denom) = 1 since C c is a unit and gcd(f.num, f.denom) = 1
  have hgcd : gcd (Polynomial.C c * f.num) f.denom = 1 := by
    have hcoprime := RatFunc.isCoprime_num_denom f
    -- gcd(unit * a, b) = gcd(a, b) = 1 when gcd(a, b) = 1
    have h : IsCoprime (Polynomial.C c * f.num) f.denom :=
      (isCoprime_mul_unit_left_left hCc_unit f.num f.denom).mpr hcoprime
    rw [← normalize_gcd]
    exact normalize_eq_one.mpr (h.isUnit_of_dvd' (gcd_dvd_left _ _) (gcd_dvd_right _ _))
  -- Get num and denom of c • f
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
  -- Now compute residueAtInfty
  simp only [residueAtInfty, hnum_smul, hdenom_smul]
  -- Key lemma: (C c * p) % q = C c * (p % q) using smul_modByMonic
  have hmod : Polynomial.C c * f.num % f.denom = Polynomial.C c * (f.num % f.denom) := by
    rw [← Polynomial.smul_eq_C_mul, ← Polynomial.smul_eq_C_mul]
    rw [← Polynomial.modByMonic_eq_mod _ hmonic]
    rw [← Polynomial.modByMonic_eq_mod _ hmonic]
    exact Polynomial.smul_modByMonic c f.num
  rw [hmod]
  -- The degree conditions are equivalent since natDegree(C c * p) = natDegree(p) for c ≠ 0
  have hdeg_equiv : (Polynomial.C c * (f.num % f.denom)).natDegree = (f.num % f.denom).natDegree := by
    rw [← Polynomial.smul_eq_C_mul, Polynomial.natDegree_smul_of_smul_regular _ hc_reg]
  -- Case analysis on the degree condition
  by_cases hdeg : (Polynomial.C c * (f.num % f.denom)).natDegree + 1 = f.denom.natDegree
  · -- Condition holds for both
    have hdeg_eq : (f.num % f.denom).natDegree + 1 = f.denom.natDegree := by
      rw [← hdeg_equiv]; exact hdeg
    simp only [hdeg, ↓reduceIte, hdeg_eq]
    -- leadingCoeff(C c * p) = c * leadingCoeff(p)
    rw [← Polynomial.smul_eq_C_mul, Polynomial.leadingCoeff_smul_of_smul_regular _ hc_reg]
    simp only [smul_eq_mul]
    -- Since f.denom is monic, leadingCoeff = 1
    simp only [hmonic, Polynomial.Monic.leadingCoeff, div_one]
    ring
  · -- Condition fails for c • f version
    -- Need to show it also fails for f version, making both sides 0
    have hdeg' : ¬((f.num % f.denom).natDegree + 1 = f.denom.natDegree) := by
      intro h; apply hdeg; rw [hdeg_equiv]; exact h
    simp only [hdeg, ↓reduceIte, hdeg', mul_zero]

open Classical in
/-- The residue at infinity of c • (1/(X - α)) is -c.

This is a key test case for scalar multiplication of residue at infinity.
Proved using linearity: c • f = c • 1 * f = C c * f and residueAtInfty_add.
-/
theorem residueAtInfty_smul_inv_X_sub (α c : Fq) :
    residueAtInfty (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) = -c := by
  by_cases hc : c = 0
  · simp only [hc, zero_smul, residueAtInfty_zero, neg_zero]
  · -- For c ≠ 0, express as (C c) / (X - C α) and compute directly
    have hXa_ne : (Polynomial.X - Polynomial.C α) ≠ (0 : Polynomial Fq) := by
      intro h
      have hdeg := congr_arg Polynomial.natDegree h
      simp only [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_zero] at hdeg
      omega
    have hCc_ne : (Polynomial.C c : Polynomial Fq) ≠ 0 := Polynomial.C_ne_zero.mpr hc
    -- Express c • (X - α)⁻¹ as (C c) / (X - C α)
    have hinv_eq : (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) =
        (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c)) /
        (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C α)) := by
      rw [Algebra.smul_def, RatFunc.algebraMap_eq_C]
      rw [← RatFunc.algebraMap_C c, RatFunc.X, ← RatFunc.algebraMap_C α, ← map_sub]
      rw [div_eq_mul_inv]
    simp only [residueAtInfty, hinv_eq]
    -- Compute num and denom
    rw [RatFunc.num_div, RatFunc.denom_div (Polynomial.C c) hXa_ne]
    -- gcd(C c, X - C α) = 1: C c is a unit (c ≠ 0), gcd divides unit → gcd is unit → gcd = 1
    -- For NormalizedGCDMonoid: gcd = normalize(gcd), and normalize(unit) = 1
    have hgcd : gcd (Polynomial.C c) (Polynomial.X - Polynomial.C α) = 1 := by
      have hunit : IsUnit (Polynomial.C c) := Polynomial.isUnit_C.mpr (Ne.isUnit hc)
      have hdvd := gcd_dvd_left (Polynomial.C c) (Polynomial.X - Polynomial.C α)
      have hgcd_unit : IsUnit (gcd (Polynomial.C c) (Polynomial.X - Polynomial.C α)) :=
        isUnit_of_dvd_unit hdvd hunit
      rw [← normalize_gcd (Polynomial.C c) (Polynomial.X - Polynomial.C α)]
      exact normalize_eq_one.mpr hgcd_unit
    -- Simplify / 1 and leadingCoeff(X - C α) = 1 structures from RatFunc.denom_div
    simp only [hgcd, EuclideanDomain.div_one, Polynomial.leadingCoeff_X_sub_C, inv_one,
               Polynomial.C_1, one_mul]
    -- Now goal is: (if (C c % (X - C α)).natDegree + 1 = (X - C α).natDegree
    --               then -((C c % (X - C α)).leadingCoeff / (X - C α).leadingCoeff)
    --               else 0) = -c
    -- Show (C c) % (X - C α) = C c since deg(C c) < deg(X - C α)
    have hrem : (Polynomial.C c) % (Polynomial.X - Polynomial.C α) = Polynomial.C c := by
      rw [Polynomial.mod_eq_self_iff hXa_ne]
      simp only [Polynomial.degree_X_sub_C]
      exact Polynomial.degree_C_lt
    -- Combine: remainder = C c, natDegree(C c) = 0, if-condition true, leadingCoeff(C c) = c
    simp only [hrem, Polynomial.natDegree_C, Polynomial.natDegree_X_sub_C, zero_add,
               ↓reduceIte, Polynomial.leadingCoeff_C]

end RiemannRochV2.Residue
