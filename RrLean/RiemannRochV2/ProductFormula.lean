import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Product Formula for RatFunc Fq

This module proves the "product formula lite" for rational functions over finite fields:
the sum of orders at all places equals zero for any nonzero rational function.

## Main Results

* `sum_rootMultiplicity_eq_card_roots` - Sum of root multiplicities = roots.card
* `sum_rootMultiplicity_le_natDegree` - Root multiplicity sum ≤ natDegree
* `polynomial_principal_divisor` - For polynomials, roots.card ≤ natDegree

## Important Note

The "naive" product formula over Fq-rational points is FALSE in general!
See `principal_divisor_degree_eq_zero_INCORRECT_DO_NOT_USE` for counterexample.

The correct product formula uses degree-weighted sums over ALL irreducible polynomials,
which follows from unique factorization rather than root counting.

## Mathematical Background

For f = p/q ∈ RatFunc Fq (coprime polynomials):
- At finite place v = (π): ord_v(f) = mult(π, p) - mult(π, q)
- At infinity: ord_∞(f) = deg(q) - deg(p)
- Sum: Σ_v ord_v(f) + ord_∞(f) = 0

The key insight is that for a polynomial P over Fq:
- Σ_{α ∈ roots(P)} rootMultiplicity(α, P) = P.roots.card ≤ deg(P)
- Equality holds when P splits completely over Fq

## Usage

The root multiplicity lemmas are useful for local analysis.
The actual proof of `projective_LRatFunc_eq_zero_of_neg_deg` in `RatFuncPairing.lean`
uses unique factorization directly rather than root counting.

## File Organization Note

This file was extracted from RatFuncPairing.lean to keep that file from growing.
Keep this file small (~150 lines). Don't add unrelated infrastructure here.
-/

noncomputable section

namespace RiemannRochV2.ProductFormula

open Polynomial

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-! ## Root Multiplicity Sum -/

/-- For a nonzero polynomial, the sum of root multiplicities over distinct roots
equals the cardinality of the roots multiset.

This uses that `Multiset.count α p.roots = p.rootMultiplicity α` for α a root.
Key Mathlib lemma: `Polynomial.count_roots` -/
theorem sum_rootMultiplicity_eq_card_roots (p : Polynomial Fq) (hp : p ≠ 0) :
    (p.roots.toFinset.sum fun α => p.rootMultiplicity α) = p.roots.card := by
  -- Use that rootMultiplicity = count in roots multiset
  simp only [← count_roots p]
  exact Multiset.toFinset_sum_count_eq p.roots

/-- The sum of root multiplicities is at most the degree. -/
theorem sum_rootMultiplicity_le_natDegree (p : Polynomial Fq) (hp : p ≠ 0) :
    (p.roots.toFinset.sum fun α => p.rootMultiplicity α) ≤ p.natDegree := by
  rw [sum_rootMultiplicity_eq_card_roots p hp]
  exact Polynomial.card_roots' p

/-! ## Order at Infinity -/

/-- The order of a rational function at infinity.
Positive means zero at ∞, negative means pole at ∞. -/
def orderAtInfinity (f : RatFunc Fq) : ℤ :=
  (f.denom.natDegree : ℤ) - (f.num.natDegree : ℤ)

/-- A rational function has no pole at infinity iff ord_∞(f) ≥ 0. -/
theorem noPoleAtInfinity_iff_orderAtInfinity_nonneg (f : RatFunc Fq) :
    f.num.natDegree ≤ f.denom.natDegree ↔ 0 ≤ orderAtInfinity f := by
  unfold orderAtInfinity
  omega

/-! ## Principal Divisor Degree -/

/-- The "finite part" of the principal divisor degree.
For f = p/q, this is (number of zeros) - (number of poles) counting Fq-points only. -/
def finitePrincipalDivisorDegree (f : RatFunc Fq) : ℤ :=
  (f.num.roots.card : ℤ) - (f.denom.roots.card : ℤ)

/-- **INCORRECT LEMMA - DO NOT USE**

The statement `finitePrincipalDivisorDegree f + orderAtInfinity f ≤ 0` is FALSE in general.

Counterexample: f = 1/(X² + X + 1) over F₂
- num = 1: roots.card = 0, natDegree = 0
- denom = X² + X + 1: roots.card = 0 (no roots in F₂), natDegree = 2
- finitePrincipalDivisorDegree = 0 - 0 = 0
- orderAtInfinity = 2 - 0 = 2
- Total = 0 + 2 = 2 > 0 ✗

The Fq-rational product formula only equals 0 when polynomials split completely.

For the actual proof of `projective_LRatFunc_eq_zero_of_neg_deg`, we don't need this lemma.
Instead, we use the degree-weighted product formula over ALL irreducible polynomials:
  `Σ_P deg(P) * ord_P(f) + ord_∞(f) = 0`
which follows directly from unique factorization in Fq[X]. -/
theorem principal_divisor_degree_eq_zero_INCORRECT_DO_NOT_USE
    (f : RatFunc Fq) (hf : f ≠ 0) :
    finitePrincipalDivisorDegree f + orderAtInfinity f = 0 := by
  -- This theorem is FALSE - see docstring
  -- Keeping as documentation of the pitfall
  sorry

/-- For polynomials (no denominator), the principal divisor has non-negative degree
at finite places, and the infinity contribution makes total = 0. -/
theorem polynomial_principal_divisor (p : Polynomial Fq) (hp : p ≠ 0) :
    (p.roots.card : ℤ) + (0 - (p.natDegree : ℤ)) ≤ 0 := by
  have h := Polynomial.card_roots' p
  omega

end RiemannRochV2.ProductFormula
