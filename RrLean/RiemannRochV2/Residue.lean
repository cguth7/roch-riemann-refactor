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
  -- Need: -((p * k) % (q * k)).coeff((q * k).natDegree - 1) = -(p % q).coeff(q.natDegree - 1)
  -- This follows from:
  -- 1. (p * k) % (q * k) = (p % q) * k (by uniqueness of polynomial division)
  -- 2. (q * k).natDegree = q.natDegree + k.natDegree (for monic q, k)
  -- 3. coeff_mul_at_sum_sub_one: ((p % q) * k).coeff(q.natDegree - 1 + k.natDegree) = (p % q).coeff(q.natDegree - 1)
  sorry

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
  -- Strategy: Use the auxiliary function which is additive in the numerator
  -- residueAtInfty f = residueAtInftyAux f.num f.denom (by residueAtInfty_eq_aux)
  -- We want to show the residue is additive by expressing everything over common denominator
  --
  -- Key facts:
  -- 1. f = f.num / f.denom, g = g.num / g.denom (reduced forms)
  -- 2. f + g as an unreduced fraction is (f.num * g.denom + g.num * f.denom) / (f.denom * g.denom)
  -- 3. The reduced form (f+g).num / (f+g).denom divides out the gcd
  -- 4. Dividing by a monic factor preserves residue (by residueAtInftyAux_mul_monic)
  -- 5. residueAtInftyAux is additive in the numerator
  --
  -- The proof combines these facts to show additivity.
  sorry

/-! ## Section 3: Residue at General Finite Place

For a monic irreducible polynomial p(X), the residue at the place (p) requires
expanding in terms of a uniformizer at that place. This is more complex and
will be developed in subsequent cycles.

The key insight is that for partial fractions, we only need residues at
places where the function has poles, and these can be computed via
the partial fraction decomposition itself.
-/

/-- Placeholder for residue at an arbitrary finite place.

For a prime p ∈ Fq[X], the residue at (p) is the coefficient of p^{-1}
in the p-adic expansion of f.

For now, we focus on the X-adic residue. General finite places will
be handled via partial fractions in future cycles.
-/
def residueAt (p : Polynomial Fq) (hp : p.Monic) (hirr : Irreducible p)
    (f : RatFunc Fq) : Fq :=
  sorry

/-! ## Section 4: Residue Theorem (Preview)

The global residue theorem states that for any f ∈ RatFunc Fq:
  ∑_v res_v(f) = 0

where the sum is over all places v (finite and infinite).

For the function field case, this follows from partial fractions:
- Write f = polynomial + Σᵢ rᵢ/pᵢ^{nᵢ} where deg(rᵢ) < deg(pᵢ)
- Each rᵢ/pᵢ^{nᵢ} contributes residues only at roots of pᵢ
- The polynomial contributes no residue at finite places
- Sum of finite residues cancels with residue at infinity

This will be formalized in future cycles once partial fractions
infrastructure is in place.
-/

/-- The sum of all residues is zero (statement only, proof in future cycle). -/
theorem residue_sum_eq_zero (f : RatFunc Fq) :
    residueAtX f + residueAtInfty f +
    ∑ᶠ p : {q : Polynomial Fq | q.Monic ∧ Irreducible q ∧ q ≠ Polynomial.X},
      residueAt p.val p.prop.1 p.prop.2.1 f = 0 := by
  sorry

end RiemannRochV2.Residue

end
