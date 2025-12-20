import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import RrLean.RiemannRochV2.Basic

/-!
# Residues for RatFunc Fq

For the rational function field Fq(t), residues are explicit coefficient extractions
from Laurent series expansions. This is the foundation for Serre duality.

## Mathematical Background

For F = RatFunc Fq (the rational function field over a finite field):
- Places = irreducible polynomials in Fq[X] + the place at infinity
- Completion at prime p ≅ Laurent series over the residue field Fq[X]/(p)
- Residue at p = coefficient of (uniformizer)^{-1} in the local expansion

## Key Mathlib Tools

- `LaurentSeries K` = `HahnSeries ℤ K` - formal Laurent series
- `HahnSeries.coeff : HahnSeries Γ R → Γ → R` - coefficient extraction
- Coercion `RatFunc F → LaurentSeries F` - X-adic expansion (via algebraMap)

## Implementation Strategy (Cycle 158+)

### Phase A: X-adic Residue (simplest case)
The X-adic place corresponds to the prime ideal (X) in Fq[X].
The completion is Fq((X)) ≅ LaurentSeries Fq.
Mathlib provides a direct coercion `RatFunc Fq → LaurentSeries Fq`.

### Phase B: Residue at Infinity
The place at infinity corresponds to expanding in 1/X.
For f = P(X)/Q(X), substitute X ↦ 1/Y, multiply by appropriate power of Y,
then extract the Y^{-1} coefficient.

### Phase C: Residue Theorem
Sum over all places (including infinity) equals zero.
Proof via partial fractions: f = polynomial + Σ (residue terms).

## References

- Rosen "Number Theory in Function Fields" Chapter 4
- Stichtenoth "Algebraic Function Fields and Codes" Section 1.4
-/

noncomputable section

open scoped LaurentSeries
open HahnSeries Polynomial

namespace RiemannRochV2.Residue

variable {Fq : Type*} [Field Fq]

/-! ## Section 1: X-adic Residue

The X-adic residue is the coefficient of X^{-1} in the Laurent series expansion.
This is the residue at the place corresponding to the prime ideal (X).
-/

/-- The X-adic residue of a rational function.

This is the residue at the place v = (X), which corresponds to evaluating
at X = 0. The residue is the coefficient of X^{-1} in the Laurent expansion.

For example:
- res_X(1/X) = 1
- res_X(1/X²) = 0
- res_X(X) = 0
- res_X(1/(X-1)) = 0 (no pole at X = 0)
-/
def residueAtX (f : RatFunc Fq) : Fq :=
  (f : LaurentSeries Fq).coeff (-1)

/-- The X-adic residue is additive. -/
theorem residueAtX_add (f g : RatFunc Fq) :
    residueAtX (f + g) = residueAtX f + residueAtX g := by
  simp only [residueAtX, map_add, HahnSeries.coeff_add]

/-- The X-adic residue respects scalar multiplication. -/
theorem residueAtX_smul (c : Fq) (f : RatFunc Fq) :
    residueAtX (c • f) = c • residueAtX f := by
  simp only [residueAtX]
  -- c • f = RatFunc.C c * f
  rw [RatFunc.smul_eq_C_mul]
  rw [map_mul]
  -- Show that (RatFunc.C c : LaurentSeries) = HahnSeries.C c
  have h : ((RatFunc.C c : RatFunc Fq) : LaurentSeries Fq) = HahnSeries.C c := by
    -- RatFunc.C c = (Polynomial.C c : RatFunc)
    rw [← RatFunc.algebraMap_C c]
    -- (Polynomial.C c : RatFunc : LaurentSeries) = (Polynomial.C c : PowerSeries : LaurentSeries)
    rw [show ((algebraMap Fq[X] (RatFunc Fq) (Polynomial.C c) : RatFunc Fq) : LaurentSeries Fq) =
            ((Polynomial.C c : PowerSeries Fq) : LaurentSeries Fq) from (RatFunc.coe_coe _).symm]
    rw [Polynomial.coe_C, HahnSeries.ofPowerSeries_C]
  rw [h, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]

/-- The X-adic residue as a linear map. -/
def residueAtX_linearMap : RatFunc Fq →ₗ[Fq] Fq where
  toFun := residueAtX
  map_add' := residueAtX_add
  map_smul' := residueAtX_smul

@[simp]
theorem residueAtX_zero : residueAtX (0 : RatFunc Fq) = 0 := by
  simp [residueAtX]

/-- The residue of 1/X is 1.

In Laurent series, X maps to `single 1 1`, so X⁻¹ maps to `single (-1) 1`.
The coefficient at -1 of `single (-1) 1` is 1.
-/
theorem residueAtX_inv_X : residueAtX (RatFunc.X⁻¹ : RatFunc Fq) = 1 := by
  simp only [residueAtX]
  -- X in RatFunc maps to single 1 1 in LaurentSeries
  have hX : ((RatFunc.X : RatFunc Fq) : LaurentSeries Fq) = single 1 1 := RatFunc.coe_X
  -- X⁻¹ maps to (single 1 1)⁻¹ = single (-1) 1
  have hXinv : ((RatFunc.X⁻¹ : RatFunc Fq) : LaurentSeries Fq) = (single 1 (1 : Fq))⁻¹ := by
    rw [map_inv₀, hX]
  rw [hXinv, HahnSeries.inv_single, HahnSeries.coeff_single_same]
  simp

/-- The residue of 1/X² is 0. -/
theorem residueAtX_inv_X_sq : residueAtX ((RatFunc.X⁻¹)^2 : RatFunc Fq) = 0 := by
  simp only [residueAtX]
  have hX : ((RatFunc.X : RatFunc Fq) : LaurentSeries Fq) = single 1 1 := RatFunc.coe_X
  have h : (((RatFunc.X⁻¹)^2 : RatFunc Fq) : LaurentSeries Fq) = (single 1 (1 : Fq))⁻¹ ^ 2 := by
    rw [map_pow, map_inv₀, hX]
  rw [h, HahnSeries.inv_single]
  -- (single (-1) 1⁻¹)^2 = single (-2) 1 (since 1⁻¹ = 1 in a field)
  simp only [inv_one]
  have hpow : (single (-1) (1 : Fq))^2 = single (-2) (1 : Fq) := by
    rw [sq, HahnSeries.single_mul_single]
    simp
  rw [hpow, HahnSeries.coeff_single_of_ne]
  omega

/-- The residue of a polynomial is 0 (no pole at X = 0).

Polynomials embed into power series (non-negative powers only),
so the coefficient of X^{-1} is always 0.
-/
theorem residueAtX_polynomial (p : Polynomial Fq) :
    residueAtX (p : RatFunc Fq) = 0 := by
  simp only [residueAtX]
  -- (p : RatFunc : LaurentSeries) = (p : PowerSeries : LaurentSeries) by coe_coe
  rw [show ((p : RatFunc Fq) : LaurentSeries Fq) =
          ((p : PowerSeries Fq) : LaurentSeries Fq) from (RatFunc.coe_coe _).symm]
  -- PowerSeries embeds via ofPowerSeries which uses embDomain with Nat.cast : ℕ → ℤ
  -- The support is in ℕ ⊆ ℤ≥0, so -1 is not in the range
  rw [ofPowerSeries_apply]
  apply embDomain_notin_range
  simp only [Set.mem_range, not_exists]
  intro n hn
  simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at hn
  have h : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  omega

/-! ## Section 2: Residue at Infinity

The residue at infinity is computed by substituting X ↦ 1/Y and extracting
the coefficient of Y^{-1}. For f(X) = P(X)/Q(X), we consider f(1/Y) · (appropriate power).

Mathematically: res_∞(f) = -res_X(f(1/X) · X⁻²)

The minus sign comes from the differential: d(1/Y) = -Y⁻² dY.
-/

/-- The residue at infinity.

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

/-! ## Section 3: Residue at Linear Places (X - α)

For the place (X - α) where α ∈ Fq, the residue is the coefficient of (X - α)^{-1}
in the Laurent expansion at X = α.

For a rational function f = p/q with (X - α) dividing q exactly once (simple pole),
the residue is p(α) / (q/(X-α))(α).

For f = c/(X - α), the residue at α is simply c.
-/

/-- The residue at the place (X - α) for a rational function.

This is defined via: multiply f by (X - α), then evaluate at α.
If f has no pole at α, the result is 0.
If f has a simple pole at α, the result is the residue.
If f has a higher-order pole, the multiplication doesn't fully cancel it,
and evaluation gives 0/0 which Lean handles as 0.

Key properties:
- residueAtLinear α (c/(X - α)) = c for c ∈ Fq (simple pole)
- residueAtLinear α (polynomial) = 0 (no pole)
- residueAtLinear α (1/(X - α)²) = 0 (higher-order pole, no X^{-1} term)
-/
def residueAtLinear (α : Fq) (f : RatFunc Fq) : Fq :=
  -- Multiply by (X - C α) to potentially cancel the pole
  let g := (RatFunc.X - RatFunc.C α) * f
  -- Evaluate at α: this extracts the residue for simple poles
  -- For no pole: (X - α) * f evaluates to 0 at α
  -- For simple pole: (X - α) * (p/(X - α)) = p, evaluates to p(α)
  -- For higher pole: still has pole, eval gives 0 by convention
  g.num.eval α / g.denom.eval α

/-- residueAtLinear agrees with residueAtX at α = 0 for simple poles.

At the place (X - 0) = (X), both definitions should give the same result.
However, they use different computational approaches:
- residueAtX uses Laurent series coeff(-1)
- residueAtLinear uses multiplication and evaluation

For simple poles, they agree. This is a sanity check.
-/
theorem residueAtLinear_zero_eq_residueAtX_simple (c : Fq) :
    residueAtLinear (0 : Fq) (c • RatFunc.X⁻¹) = residueAtX (c • RatFunc.X⁻¹) := by
  simp only [residueAtLinear]
  -- RatFunc.C 0 = 0, so X - C 0 = X
  have hC0 : (RatFunc.C (0 : Fq) : RatFunc Fq) = 0 := map_zero _
  simp only [hC0, sub_zero]
  -- g = X * (c • X⁻¹) = c • (X * X⁻¹) = c • 1 = c
  have h : (RatFunc.X : RatFunc Fq) * (c • RatFunc.X⁻¹) = RatFunc.C c := by
    rw [mul_smul_comm, mul_inv_cancel₀ RatFunc.X_ne_zero, Algebra.smul_def, mul_one,
        ← RatFunc.algebraMap_eq_C]
  rw [h]
  simp only [RatFunc.num_C, RatFunc.denom_C]
  simp only [Polynomial.eval_C, Polynomial.eval_one, div_one]
  -- Now show this equals residueAtX (c • X⁻¹) = c
  rw [residueAtX_smul]
  simp only [residueAtX_inv_X, smul_eq_mul, mul_one]

/-- The residue at α of c/(X - α) is c.

This is the fundamental test case: a simple pole with residue c.
-/
theorem residueAtLinear_inv_X_sub (α c : Fq) :
    residueAtLinear α (c • (RatFunc.X - RatFunc.C α)⁻¹) = c := by
  simp only [residueAtLinear]
  -- g = (X - C α) * (c • (X - C α)⁻¹) = c • ((X - C α) * (X - C α)⁻¹) = c • 1 = c
  have hne : (RatFunc.X : RatFunc Fq) - RatFunc.C α ≠ 0 := by
    intro h
    have heq : (RatFunc.X : RatFunc Fq) = RatFunc.C α := sub_eq_zero.mp h
    -- X ≠ C α since their num/denom are different
    have hX_num : (RatFunc.X : RatFunc Fq).num = Polynomial.X := RatFunc.num_X
    have hC_num : (RatFunc.C α : RatFunc Fq).num = Polynomial.C α := RatFunc.num_C α
    rw [heq] at hX_num
    rw [hX_num] at hC_num
    -- X ≠ C α as polynomials
    have : Polynomial.X = Polynomial.C α := hC_num
    have hdeg := congr_arg Polynomial.natDegree this
    simp only [Polynomial.natDegree_X, Polynomial.natDegree_C] at hdeg
    omega
  have h : (RatFunc.X - RatFunc.C α) * (c • (RatFunc.X - RatFunc.C α)⁻¹) = RatFunc.C c := by
    rw [mul_smul_comm, mul_inv_cancel₀ hne, Algebra.smul_def, mul_one, ← RatFunc.algebraMap_eq_C]
  rw [h]
  simp only [RatFunc.num_C, RatFunc.denom_C]
  simp only [Polynomial.eval_C, Polynomial.eval_one, div_one]

/-- The residue at α of a polynomial is 0 (no pole at any finite place). -/
theorem residueAtLinear_polynomial (α : Fq) (p : Polynomial Fq) :
    residueAtLinear α (algebraMap (Polynomial Fq) (RatFunc Fq) p) = 0 := by
  simp only [residueAtLinear]
  -- g = (X - C α) * p, which is a polynomial
  have h : (RatFunc.X - RatFunc.C α) * (algebraMap (Polynomial Fq) (RatFunc Fq) p) =
           algebraMap (Polynomial Fq) (RatFunc Fq) ((Polynomial.X - Polynomial.C α) * p) := by
    rw [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub, ← map_mul]
  rw [h]
  simp only [RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp only [Polynomial.eval_one, div_one]
  -- ((X - C α) * p).eval α = (X - C α)(α) * p(α) = 0 * p(α) = 0
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  ring

/-- Residue at a linear place of zero is zero. -/
@[simp]
theorem residueAtLinear_zero (α : Fq) : residueAtLinear α (0 : RatFunc Fq) = 0 := by
  simp only [residueAtLinear, mul_zero]
  rw [RatFunc.num_zero, RatFunc.denom_zero]
  simp

/-- Residue at a linear place respects scalar multiplication.

For c ∈ Fq and f : RatFunc Fq:
  res_α(c • f) = c • res_α(f)
-/
theorem residueAtLinear_smul (α : Fq) (c : Fq) (f : RatFunc Fq) :
    residueAtLinear α (c • f) = c * residueAtLinear α f := by
  by_cases hc : c = 0
  · simp [hc, residueAtLinear_zero]
  · -- c ≠ 0 case: Use that c • f = (C c / 1) * f = C c * f
    -- and exploit the linearity structure
    simp only [residueAtLinear]
    -- (X - C α) * (c • f) = c • ((X - C α) * f)
    have hcomm : (RatFunc.X - RatFunc.C α) * (c • f) = c • ((RatFunc.X - RatFunc.C α) * f) := by
      rw [mul_smul_comm]
    simp only [hcomm]
    set g := (RatFunc.X - RatFunc.C α) * f with hg_def
    -- c • g = (C c) * g
    have hsmul_eq : c • g = RatFunc.C c * g := by
      rw [Algebra.smul_def, RatFunc.algebraMap_eq_C]
    rw [hsmul_eq]
    have hCc_ne : (RatFunc.C c : RatFunc Fq) ≠ 0 := by
      intro h
      have : c = 0 := by
        have heq : RatFunc.C c = RatFunc.C 0 := by simp only [h, map_zero]
        exact RatFunc.C_injective heq
      exact hc this
    -- Use num_denom_mul relation
    have hCc_denom : (RatFunc.C c : RatFunc Fq).denom = 1 := RatFunc.denom_C c
    have hCc_num : (RatFunc.C c : RatFunc Fq).num = Polynomial.C c := RatFunc.num_C c
    have hmul := RatFunc.num_denom_mul (RatFunc.C c) g
    rw [hCc_denom, one_mul, hCc_num] at hmul
    have heval := congr_arg (Polynomial.eval α) hmul
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at heval
    -- heval: (C c * g).num.eval α * g.denom.eval α = c * g.num.eval α * (C c * g).denom.eval α
    by_cases hgd : g.denom.eval α = 0
    · -- g has a pole at α
      simp only [hgd, div_zero, mul_zero]
      rw [hgd, mul_zero] at heval
      -- Need: (C c * g).num / (C c * g).denom = 0
      -- From heval: 0 = c * g.num.eval α * (C c * g).denom.eval α
      -- If (C c * g).denom.eval α ≠ 0 and c ≠ 0, then g.num.eval α = 0
      -- But g.num and g.denom are coprime, so if denom.eval = 0, num.eval ≠ 0
      -- This means (C c * g).denom.eval α = 0
      -- Actually, simpler: just show the division is 0/0 = 0 or num = 0
      by_cases hcgd : (RatFunc.C c * g).denom.eval α = 0
      · simp [hcgd]
      · -- (C c * g).denom ≠ 0 but g.denom = 0
        -- From heval: 0 = c * g.num.eval α * (C c * g).denom.eval α
        -- Since c ≠ 0 and (C c * g).denom.eval α ≠ 0, we get g.num.eval α = 0
        have hgn : g.num.eval α = 0 := by
          by_contra hgn_ne
          have h0 : c * g.num.eval α * (RatFunc.C c * g).denom.eval α = 0 := heval.symm
          simp only [mul_eq_zero, hc, hgn_ne, hcgd, or_self] at h0
        -- But g.num and g.denom are coprime, so both can't be roots at the same point
        -- This is a contradiction via polynomial coprimality
        have hcoprime := RatFunc.isCoprime_num_denom g
        -- If eval at α is 0 for both, then (X - α) divides both
        -- But gcd(num, denom) = 1, so (X - α) | 1, contradiction
        exfalso
        have hroot_denom : Polynomial.IsRoot g.denom α := by
          rwa [Polynomial.IsRoot.def]
        have hroot_num : Polynomial.IsRoot g.num α := by
          rwa [Polynomial.IsRoot.def]
        have hdvd_denom := Polynomial.dvd_iff_isRoot.mpr hroot_denom
        have hdvd_num := Polynomial.dvd_iff_isRoot.mpr hroot_num
        have hXa_ne : Polynomial.X - Polynomial.C α ≠ 0 := by
          intro h
          have := congr_arg Polynomial.natDegree h
          simp at this
        have hdeg : (Polynomial.X - Polynomial.C α).natDegree = 1 := Polynomial.natDegree_X_sub_C α
        have hdvd1 : (Polynomial.X - Polynomial.C α) ∣ 1 := by
          have h1 := hcoprime.isUnit_of_dvd' hdvd_num hdvd_denom
          exact h1.dvd
        have hdeg1 := Polynomial.natDegree_le_of_dvd hdvd1 one_ne_zero
        rw [hdeg, Polynomial.natDegree_one] at hdeg1
        omega
    · -- g.denom.eval α ≠ 0
      -- Key: (C c * g).denom divides g.denom, so if g.denom.eval α ≠ 0,
      -- then (C c * g).denom.eval α ≠ 0 as well
      have hcgd : (RatFunc.C c * g).denom.eval α ≠ 0 := by
        intro hcgd_zero
        -- (C c * g).denom divides g.denom (from denom_mul_dvd)
        have hdvd := RatFunc.denom_mul_dvd (RatFunc.C c) g
        rw [hCc_denom, one_mul] at hdvd
        -- If p | q and p.eval α = 0, then q.eval α = 0
        have heval_zero := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd hcgd_zero
        exact hgd heval_zero
      -- Now both denominators are nonzero at α, use the relation
      -- heval: (C c * g).num.eval α * g.denom.eval α = c * g.num.eval α * (C c * g).denom.eval α
      -- Goal: (C c * g).num.eval α / (C c * g).denom.eval α = c * (g.num.eval α / g.denom.eval α)
      have h1 : (RatFunc.C c * g).num.eval α / (RatFunc.C c * g).denom.eval α =
                ((RatFunc.C c * g).num.eval α * g.denom.eval α) / ((RatFunc.C c * g).denom.eval α * g.denom.eval α) := by
        field_simp [hgd, hcgd]
      have h2 : c * (g.num.eval α / g.denom.eval α) =
                (c * g.num.eval α * (RatFunc.C c * g).denom.eval α) / ((RatFunc.C c * g).denom.eval α * g.denom.eval α) := by
        field_simp [hgd, hcgd]
      rw [h1, h2, heval]

/-- Auxiliary lemma: for rational functions with the same denominator after multiplication by (X - α),
    the residue is additive.

This is the key step for proving residueAtLinear_add. -/
private lemma residueAtLinear_add_aux (α : Fq) (f g : RatFunc Fq)
    (hf_denom : ((RatFunc.X - RatFunc.C α) * f).denom.eval α ≠ 0)
    (hg_denom : ((RatFunc.X - RatFunc.C α) * g).denom.eval α ≠ 0) :
    residueAtLinear α (f + g) = residueAtLinear α f + residueAtLinear α g := by
  simp only [residueAtLinear, mul_add]
  set fX := (RatFunc.X - RatFunc.C α) * f with hfX_def
  set gX := (RatFunc.X - RatFunc.C α) * g with hgX_def
  -- The goal is now in terms of fX + gX
  -- Use RatFunc.num_denom_add for (fX + gX)
  have hadd := RatFunc.num_denom_add fX gX
  -- hadd : (fX + gX).num * (fX.denom * gX.denom) = (fX.num * gX.denom + fX.denom * gX.num) * (fX + gX).denom
  have heval := congr_arg (Polynomial.eval α) hadd
  simp only [Polynomial.eval_mul, Polynomial.eval_add] at heval
  -- Goal: (fX + gX).num.eval α / (fX + gX).denom.eval α
  --     = fX.num.eval α / fX.denom.eval α + gX.num.eval α / gX.denom.eval α
  have hprod_ne : fX.denom.eval α * gX.denom.eval α ≠ 0 := mul_ne_zero hf_denom hg_denom
  by_cases hsum_denom : (fX + gX).denom.eval α = 0
  · -- If (fX + gX).denom.eval α = 0
    -- From heval: lhs * (fX.denom * gX.denom).eval α = rhs * 0 = 0
    -- But (fX.denom * gX.denom).eval α ≠ 0, so lhs = 0
    rw [hsum_denom, mul_zero] at heval
    have hsum_num : (fX + gX).num.eval α = 0 := by
      by_contra h
      have : (fX + gX).num.eval α * (fX.denom.eval α * gX.denom.eval α) = 0 := heval
      simp only [mul_eq_zero, h, hprod_ne, or_self] at this
    simp only [hsum_num, hsum_denom, zero_div]
    -- Need: fX.num.eval α / fX.denom.eval α + gX.num.eval α / gX.denom.eval α = 0
    -- From heval: 0 = (fX.num * gX.denom + fX.denom * gX.num).eval α * 0 = 0
    -- This doesn't directly give us the sum = 0...
    -- Actually, we also need that the gcd doesn't introduce issues
    -- This case is subtle; let's use field_simp
    -- Actually, from hadd with denom.eval = 0 and prod_ne ≠ 0, we have num.eval = 0
    -- And hadd gives: 0 * prod = (fX.num * gX.denom + fX.denom * gX.num).eval α * 0
    -- So 0 = 0, which is fine but doesn't help.
    -- We need to show: fn/fd + gn/gd = 0
    -- From hadd at eval: (fn*gd + fd*gn) * sum_denom = sum_num * (fd * gd)
    -- With sum_denom.eval = 0 and sum_num.eval = 0: 0 = 0, no info
    -- But we know sum_denom.eval = 0, and (fn*gd + fd*gn) might not be 0
    -- Hmm, this case needs more careful analysis
    -- For now, let's add an assumption that we're in the "nice" case
    sorry
  · -- (fX + gX).denom.eval α ≠ 0
    -- This case needs more careful analysis using heval and the field structure
    -- The core relation is from heval (reordered):
    -- (fX + gX).num.eval α * (fX.denom.eval α * gX.denom.eval α) =
    -- (fX.num.eval α * gX.denom.eval α + gX.num.eval α * fX.denom.eval α) * (fX + gX).denom.eval α
    -- TODO: Complete this proof in future cycle
    sorry

/-- Placeholder for residue at an arbitrary finite place.

For a prime p ∈ Fq[X], the residue at (p) is the coefficient of p^{-1}
in the p-adic expansion of f.

For degree-1 primes (X - α), use `residueAtLinear` instead.
General finite places will be handled via partial fractions in future cycles.
-/
def residueAt (p : Polynomial Fq) (hp : p.Monic) (hirr : Irreducible p)
    (f : RatFunc Fq) : Fq :=
  sorry

/-! ## Section 4: Residue Theorem

The global residue theorem states that for any f ∈ RatFunc Fq:
  ∑_v res_v(f) = 0

where the sum is over all places v (finite and infinite).

For simple poles at linear places (X - α), we can prove this directly.
-/

/-- The sum of residues is zero for a simple pole at a linear place.

For f = c • (X - α)⁻¹:
- res_α(f) = c   (from residueAtLinear_inv_X_sub)
- res_∞(f) = -c  (from residueAtInfty_smul_inv_X_sub)
- Sum = c + (-c) = 0

This is the fundamental test case for the residue theorem.
-/
theorem residue_sum_simple_pole (α c : Fq) :
    residueAtLinear α (c • (RatFunc.X - RatFunc.C α)⁻¹) +
    residueAtInfty (c • (RatFunc.X - RatFunc.C α)⁻¹) = 0 := by
  rw [residueAtLinear_inv_X_sub, residueAtInfty_smul_inv_X_sub]
  ring

-- Helper lemmas for residueAtLinear_inv_X_sub_ne

open Classical in
private lemma RatFunc_num_X_sub_C' (β : Fq) :
    (RatFunc.X - RatFunc.C β : RatFunc Fq).num = Polynomial.X - Polynomial.C β := by
  simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub, RatFunc.num_algebraMap]

open Classical in
private lemma RatFunc_denom_X_sub_C' (β : Fq) :
    (RatFunc.X - RatFunc.C β : RatFunc Fq).denom = 1 := by
  rw [RatFunc.X, ← RatFunc.algebraMap_C β, ← map_sub, RatFunc.denom_algebraMap]

open Classical in
private lemma denom_inv_X_sub_C_dvd (α : Fq) :
    ((RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq).denom ∣ (Polynomial.X - Polynomial.C α) := by
  have hne : (Polynomial.X - Polynomial.C α) ≠ (0 : Polynomial Fq) := by
    intro h; have hdeg := congr_arg Polynomial.natDegree h; simp at hdeg
  rw [RatFunc.denom_dvd hne]
  use 1
  rw [map_one, RatFunc.X, ← RatFunc.algebraMap_C α, ← map_sub, one_div]

open Classical in
private lemma denom_smul_inv_X_sub_dvd (α c : Fq) :
    (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq).denom ∣ (Polynomial.X - Polynomial.C α) := by
  by_cases hc : c = 0
  · simp only [hc, zero_smul, RatFunc.denom_zero]
    exact one_dvd _
  · have hh_eq : (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) =
                 RatFunc.C c * (RatFunc.X - RatFunc.C α)⁻¹ := by
      rw [Algebra.smul_def, RatFunc.algebraMap_eq_C]
    rw [hh_eq]
    have hdvd := RatFunc.denom_mul_dvd (RatFunc.C c) (RatFunc.X - RatFunc.C α)⁻¹
    rw [RatFunc.denom_C, one_mul] at hdvd
    exact hdvd.trans (denom_inv_X_sub_C_dvd α)

private lemma Polynomial.eval_ne_zero_of_dvd' {R : Type*} [CommRing R] [NoZeroDivisors R]
    {p q : Polynomial R} {x : R} (hdvd : p ∣ q) (hq : q.eval x ≠ 0) : p.eval x ≠ 0 := by
  intro hp
  exact hq (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd hp)

/-- The residue at a different linear place is zero for a simple pole.

For f = c • (X - α)⁻¹ and β ≠ α:
- res_β(f) = 0 (f has no pole at β)

Proof strategy: (X - C β) is a factor of the numerator of g = (X - C β) * f,
so g.num.eval β = 0. Meanwhile, g.denom | (X - C α) and (X - C α).eval β ≠ 0,
so g.denom.eval β ≠ 0. Thus g.num.eval β / g.denom.eval β = 0.
-/
theorem residueAtLinear_inv_X_sub_ne (α β c : Fq) (hne : α ≠ β) :
    residueAtLinear β (c • (RatFunc.X - RatFunc.C α)⁻¹) = 0 := by
  simp only [residueAtLinear]
  by_cases hc : c = 0
  · simp [hc]
  · set f := (RatFunc.X - RatFunc.C β : RatFunc Fq) with hf_def
    set h := (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) with hh_def
    -- Use num_denom_mul: (f*h).num * (f.denom * h.denom) = f.num * h.num * (f*h).denom
    have hmul := RatFunc.num_denom_mul f h
    rw [RatFunc_denom_X_sub_C', one_mul] at hmul
    have heval := congr_arg (Polynomial.eval β) hmul
    simp only [Polynomial.eval_mul] at heval
    -- f.num.eval β = (X - C β).eval β = 0
    have hf_zero : f.num.eval β = 0 := by
      simp only [hf_def, RatFunc_num_X_sub_C', Polynomial.eval_sub,
                 Polynomial.eval_X, Polynomial.eval_C, sub_self]
    rw [hf_zero, zero_mul, zero_mul] at heval
    -- (f * h).num.eval β * h.denom.eval β = 0
    -- h.denom | (X - C α) and (X - C α).eval β = β - α ≠ 0, so h.denom.eval β ≠ 0
    have hXa_eval_ne : (Polynomial.X - Polynomial.C α).eval β ≠ 0 := by
      simp [sub_ne_zero.mpr hne.symm]
    have hdvd : h.denom ∣ (Polynomial.X - Polynomial.C α) := by
      simp only [hh_def]
      exact denom_smul_inv_X_sub_dvd α c
    have hh_denom_ne : h.denom.eval β ≠ 0 := Polynomial.eval_ne_zero_of_dvd' hdvd hXa_eval_ne
    -- So (f * h).num.eval β = 0
    have hnum_zero : (f * h).num.eval β = 0 := by
      have h0 : (f * h).num.eval β * h.denom.eval β = 0 := by rw [heval]
      exact (mul_eq_zero.mp h0).resolve_right hh_denom_ne
    simp [hnum_zero]

/-- The sum of all residues is zero (statement only, proof in future cycle).

Full residue theorem for general rational functions requires partial fractions. -/
theorem residue_sum_eq_zero (f : RatFunc Fq) :
    residueAtX f + residueAtInfty f +
    ∑ᶠ p : {q : Polynomial Fq | q.Monic ∧ Irreducible q ∧ q ≠ Polynomial.X},
      residueAt p.val p.prop.1 p.prop.2.1 f = 0 := by
  sorry

end RiemannRochV2.Residue

end
