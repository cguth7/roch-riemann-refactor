/-
# Full Adele Ring - Compactness and Weak Approximation

This file contains the compactness proofs and weak approximation theorems for the full adele ring.
Split from FullAdeles.lean for faster incremental builds.

## Main Results (TODO - currently has build errors)
* RankOne instance for FqtInfty
* Compactness of integral adeles
* Weak approximation theorems
-/

import RrLean.RiemannRochV2.FullAdelesBase

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open RiemannRochV2.AdelicTopology
open scoped Classical

namespace RiemannRochV2.FullAdeles

open FunctionField Polynomial
open scoped Polynomial WithZero

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

section FqInstance

/-! ### RankOne Instance for FqtInfty

To use the compactness characterization theorem
`compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`,
we need a `RankOne` instance for the infinity valuation.
-/

/-- The valuation on RatFunc Fq extended to FqtInfty agrees with inftyValuationDef on elements of K.

This is a helper to connect Valued.v on the completion with inftyValuationDef on RatFunc Fq.
-/
theorem valued_FqtInfty_eq_inftyValuationDef (x : RatFunc Fq) :
    Valued.v (inftyRingHom Fq x) = FunctionField.inftyValuationDef Fq x := by
  simp only [inftyRingHom, FunctionField.valuedFqtInfty.def]
  letI : Valued (RatFunc Fq) (WithZero (Multiplicative ℤ)) := FunctionField.inftyValuedFqt Fq
  exact Valued.extension_extends x

/-- The FqtInfty valuation is nontrivial: 1/X has valuation exp(-1) < 1 and ≠ 0.

This is needed to get RankOne via MulArchimedean.
-/
instance isNontrivial_FqtInfty :
    (Valued.v (R := FqtInfty Fq)).IsNontrivial := by
  rw [Valuation.isNontrivial_iff_exists_lt_one]
  -- Use 1/X which has inftyValuation = exp(-1) < 1
  use inftyRingHom Fq (1 / RatFunc.X)
  constructor
  · -- v(1/X) ≠ 0
    simp only [ne_eq, Valuation.zero_iff, map_eq_zero]
    exact one_div_ne_zero RatFunc.X_ne_zero
  · -- v(1/X) < 1
    have hval : Valued.v (inftyRingHom Fq (1 / RatFunc.X)) =
        FunctionField.inftyValuationDef Fq (1 / RatFunc.X) :=
      valued_FqtInfty_eq_inftyValuationDef Fq (1 / RatFunc.X)
    rw [hval]
    have hX_inv : FunctionField.inftyValuationDef Fq (1 / RatFunc.X) = WithZero.exp (-1) := by
      rw [← FunctionField.inftyValuation_apply]
      exact FunctionField.inftyValuation.X_inv Fq
    rw [hX_inv]
    -- exp(-1) < exp(0) = 1
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0)

/-- RankOne for the FqtInfty valuation follows from MulArchimedean.

Since ℤ is Archimedean, WithZero (Multiplicative ℤ) is MulArchimedean, and
with IsNontrivial we get RankOne.
-/
def rankOne_FqtInfty :
    Valuation.RankOne (Valued.v (R := FqtInfty Fq)) :=
  (Valuation.nonempty_rankOne_iff_mulArchimedean.mpr inferInstance).some

/-- The integer ring of FqtInfty is closed in FqtInfty. -/
lemma isClosed_integer_FqtInfty :
    IsClosed (Valued.integer (FqtInfty Fq) : Set (FqtInfty Fq)) :=
  Valued.isClosed_valuationSubring (FqtInfty Fq)

/-- FqtInfty is complete (it's a uniform space completion). -/
instance completeSpace_FqtInfty : CompleteSpace (FqtInfty Fq) :=
  @UniformSpace.Completion.completeSpace (RatFunc Fq)
    (FunctionField.inftyValuedFqt Fq).toUniformSpace

/-- The integer ring of FqtInfty is complete (as a closed subset of a complete space). -/
instance completeSpace_integer_FqtInfty :
    CompleteSpace (Valued.integer (FqtInfty Fq)) :=
  (isClosed_integer_FqtInfty Fq).isComplete.completeSpace_coe

/-- The valuation range on FqtInfty is nontrivial.

This is used to show the integer ring is a PID.
-/
lemma range_nontrivial_FqtInfty :
    (Set.range (Valued.v (R := FqtInfty Fq))).Nontrivial := by
  -- exp(-1) ∈ range, 0 ∈ range, and exp(-1) ≠ 0
  refine ⟨Valued.v (inftyRingHom Fq (1 / RatFunc.X)), ⟨_, rfl⟩, 0, ⟨0, map_zero _⟩, ?_⟩
  rw [valued_FqtInfty_eq_inftyValuationDef, ← FunctionField.inftyValuation_apply,
      FunctionField.inftyValuation.X_inv]
  exact WithZero.coe_ne_zero

/-- The integer ring of FqtInfty is a principal ideal ring.

Uses the fact that WithZero (Multiplicative ℤ) is not densely ordered.
-/
instance isPrincipalIdealRing_integer_FqtInfty :
    IsPrincipalIdealRing (Valued.integer (FqtInfty Fq)) := by
  -- API mismatches with current mathlib - needs investigation
  sorry

/-- The integer ring of FqtInfty is a discrete valuation ring.

This follows from being a PID that is not a field (uniformizer 1/X has valuation < 1).
-/
instance isDiscreteValuationRing_integer_FqtInfty :
    IsDiscreteValuationRing (Valued.integer (FqtInfty Fq)) := by
  -- API mismatches with current mathlib - needs investigation
  sorry

/-- Compactness of integral full adeles.

The integral full adeles form a compact set because:
1. ∏_v O_v is compact (AllIntegersCompact for finite adeles)
2. {x ∈ FqtInfty | |x|_∞ ≤ 1} is compact (integer ring of local field)
3. Product of compact sets is compact

**Axioms used**:
- `AllIntegersCompact Fq[X] (RatFunc Fq)` for finite adeles compactness
- `Finite (Valued.ResidueField (FqtInfty Fq))` for infinity compactness
-/
theorem isCompact_integralFullAdeles [AllIntegersCompact Fq[X] (RatFunc Fq)]
    [Finite (Valued.ResidueField (FqtInfty Fq))] :
    IsCompact (integralFullAdeles Fq) := by
  -- Step 1: Show integralFullAdeles = (integral finite adeles) ×ˢ (integers at ∞)
  -- Step 2: Show each factor is compact
  -- Step 3: Apply IsCompact.prod

  -- Define the two factor sets
  let integralFin : Set (FiniteAdeleRing Fq[X] (RatFunc Fq)) :=
    {a | ∀ v, a.val v ∈ v.adicCompletionIntegers (RatFunc Fq)}
  let integralInfty : Set (FqtInfty Fq) := {x | Valued.v x ≤ 1}

  -- integralFullAdeles is the product of these two sets
  have hprod : integralFullAdeles Fq = integralFin ×ˢ integralInfty := by
    ext ⟨af, ai⟩
    simp only [integralFullAdeles, Set.mem_setOf_eq]
    rfl

  -- Prove compactness of the finite adeles factor
  have hCompactFin : IsCompact integralFin := by
    -- Each O_v is compact by AllIntegersCompact
    haveI hOv_compact : ∀ v : HeightOneSpectrum Fq[X],
        CompactSpace (v.adicCompletionIntegers (RatFunc Fq)) :=
      fun v => AllIntegersCompact.compact v
    -- Π v, O_v is compact by Tychonoff (Pi.compactSpace)
    -- The integral adeles are the image of structureMap, which is a continuous embedding
    -- Image of compact set under continuous map is compact
    let R' := fun v : HeightOneSpectrum Fq[X] => v.adicCompletion (RatFunc Fq)
    let A' := fun v : HeightOneSpectrum Fq[X] => (v.adicCompletionIntegers (RatFunc Fq) : Set (R' v))
    -- Use range_structureMap to show integralFin = range(structureMap)
    have hrange : integralFin = Set.range (RestrictedProduct.structureMap R' A' Filter.cofinite) := by
      ext a
      rw [RestrictedProduct.range_structureMap]
      -- a ∈ integralFin ↔ ∀ v, a.1 v ∈ A' v
      -- Both express: every component is in the integers
      rfl
    rw [hrange]
    -- Now need: range of structureMap is compact
    -- structureMap is continuous, Π v, O_v is compact, so image is compact
    exact isCompact_range (RestrictedProduct.isEmbedding_structureMap.continuous)

  -- Prove compactness of the infinity factor
  have hCompactInfty : IsCompact integralInfty := by
    -- Use the compactSpace_iff characterization:
    -- CompactSpace 𝒪[K] ↔ CompleteSpace 𝒪[K] ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K]
    -- All three conditions are now available as instances!
    letI hrank := rankOne_FqtInfty Fq
    haveI hcompact : CompactSpace (Valued.integer (FqtInfty Fq)) :=
      Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
        ⟨completeSpace_integer_FqtInfty Fq,
         isDiscreteValuationRing_integer_FqtInfty Fq,
         inferInstance⟩
    -- Convert CompactSpace to IsCompact via isCompact_univ and subtype embedding
    -- integralInfty = Valued.integer as a set
    have heq : integralInfty = (Valued.integer (FqtInfty Fq) : Set (FqtInfty Fq)) := rfl
    rw [heq]
    exact isCompact_iff_compactSpace.mpr hcompact

  -- Combine using IsCompact.prod
  rw [hprod]
  exact hCompactFin.prod hCompactInfty

/-! ### Helper lemmas for weak approximation -/

/-- The set {x : Valued.v x ≤ 1} is a neighborhood of any point in it.

For valued fields with discrete value group, the closed ball is also open (clopen).
-/
theorem isOpen_ball_le_one_FqtInfty :
    IsOpen {x : FqtInfty Fq | Valued.v x ≤ 1} := by
  /-
  **Proof approach**:
  For discrete valuations, {v ≤ 1} = {v < exp(1)} which is open.
  Since value group is ℤ, there's nothing between 1 = exp(0) and exp(1).

  Key steps:
  - convert to showing {v ≤ 1} = {v < exp(1)} via Valued.isClopen_ball
  - Forward: v x ≤ 1 = exp(0) < exp(1)
  - Backward: v x < exp(1), with v x = exp(n) for some n ∈ ℤ, so n < 1 hence n ≤ 0

  API issues: WithZero.coe_lt_coe rewrite patterns not matching
  -/
  sorry

/-- K is dense in FqtInfty (the completion at infinity). -/
theorem denseRange_inftyRingHom :
    DenseRange (inftyRingHom Fq) := by
  letI : Valued (RatFunc Fq) (WithZero (Multiplicative ℤ)) := FunctionField.inftyValuedFqt Fq
  -- inftyRingHom is the coe from K to its completion
  exact UniformSpace.Completion.denseRange_coe

/-- For any element of FqtInfty, there exists k ∈ K with |a - k|_∞ ≤ 1.

This follows from density of K in FqtInfty and the clopen nature of the unit ball.
-/
theorem exists_approx_in_ball_infty (a : FqtInfty Fq) :
    ∃ k : RatFunc Fq, Valued.v (a - inftyRingHom Fq k) ≤ 1 := by
  -- The ball {x : |x - a| ≤ 1} is an open neighborhood of a
  -- By density, K intersects it
  have hopen : IsOpen {x : FqtInfty Fq | Valued.v (a - x) ≤ 1} := by
    -- Translate the open set {y : |y| ≤ 1} by a
    have h1 : {x : FqtInfty Fq | Valued.v (a - x) ≤ 1} = (fun y => a - y) ⁻¹' {y | Valued.v y ≤ 1} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [h1]
    apply IsOpen.preimage (by continuity) (isOpen_ball_le_one_FqtInfty Fq)
  have hmem : a ∈ {x : FqtInfty Fq | Valued.v (a - x) ≤ 1} := by
    simp only [Set.mem_setOf_eq, sub_self, map_zero]
    exact zero_le'
  -- Use density
  obtain ⟨k, hk⟩ := (denseRange_inftyRingHom Fq).exists_mem_open hopen ⟨a, hmem⟩
  exact ⟨k, hk⟩

/-- Polynomials are integral at all finite places.

For k ∈ Fq[X] ⊂ RatFunc Fq, at any finite place v, we have v(k) ≥ 0.
-/
theorem polynomial_integral_at_finite_places (p : Fq[X]) (v : HeightOneSpectrum Fq[X]) :
    (algebraMap Fq[X] (RatFunc Fq) p : v.adicCompletion (RatFunc Fq)) ∈
      v.adicCompletionIntegers (RatFunc Fq) := by
  -- Polynomials are integral: val_v(p) ≤ 1 for any polynomial p
  -- API issue: valuedAdicCompletion_eq_valuation rewrite not matching
  sorry

/-- For a polynomial P, diag(P) is integral at all finite places. -/
theorem polynomial_diag_integral (p : Fq[X]) (v : HeightOneSpectrum Fq[X]) :
    ((fqFullDiagonalEmbedding Fq (algebraMap Fq[X] (RatFunc Fq) p)).1).val v ∈
      v.adicCompletionIntegers (RatFunc Fq) :=
  polynomial_integral_at_finite_places Fq p v

/-- The finite adele component of the diagonal embedding. -/
theorem fqFullDiagonalEmbedding_fst (k : RatFunc Fq) :
    (fqFullDiagonalEmbedding Fq k).1 = FiniteAdeleRing.algebraMap Fq[X] (RatFunc Fq) k := rfl

/-- The infinity component of the diagonal embedding. -/
theorem fqFullDiagonalEmbedding_snd (k : RatFunc Fq) :
    (fqFullDiagonalEmbedding Fq k).2 = inftyRingHom Fq k := rfl

/-- For any element a_v ∈ K_v, there exists y ∈ K approximating it: a_v - y ∈ O_v.

This follows from density of K in K_v. The set {x ∈ K_v : a_v - x ∈ O_v} = a_v - O_v
is open (since O_v is open for discrete valuations), and non-empty (contains a_v - 0 = a_v
only if a_v ∈ O_v, otherwise we need to find an approximant).

For elements with poles, this approximation exists by the structure of completions.
-/
theorem exists_local_approximant (v : HeightOneSpectrum Fq[X]) (a_v : v.adicCompletion (RatFunc Fq)) :
    ∃ y : RatFunc Fq, (a_v - y) ∈ v.adicCompletionIntegers (RatFunc Fq) := by
  -- K is dense in K_v, and the ball a_v - O_v is open
  -- So K intersects this ball
  -- Using density of K in K_v and openness of the integer ring
  -- Proof has API issues with current mathlib - using sorry
  sorry

/-- Construct a HeightOneSpectrum from an irreducible polynomial.

For an irreducible p ∈ Fq[X], the ideal (p) is a height-one prime.
-/
def HeightOneSpectrum.ofIrreducible (p : Fq[X]) (hp_irr : Irreducible p) :
    HeightOneSpectrum Fq[X] where
  asIdeal := Ideal.span {p}
  isPrime := (Ideal.span_singleton_prime hp_irr.ne_zero).mpr hp_irr.prime
  ne_bot := by simp only [ne_eq, Ideal.span_singleton_eq_bot]; exact hp_irr.ne_zero

/-- The set of height-one primes dividing a nonzero polynomial is finite.

This follows from the fact that Fq[X] is a UFD with finitely many normalized prime factors.
-/
theorem HeightOneSpectrum.finite_divisors (D : Fq[X]) (hD : D ≠ 0) :
    {v : HeightOneSpectrum Fq[X] | v.intValuation D < 1}.Finite := by
  -- The set of primes dividing D corresponds to (normalizedFactors D).toFinset
  -- This is a finite set since normalizedFactors returns a finite multiset
  -- Proof has API issues with current mathlib - needs refinement
  sorry

/-- The intValuation of D is at least exp(-natDegree D).
This bounds the multiplicity of any prime in D by the degree of D.
Proof: g is irreducible so deg(g) ≥ 1, and g^n | D implies n·deg(g) ≤ deg(D). -/
lemma intValuation_ge_exp_neg_natDegree (v : HeightOneSpectrum Fq[X]) (D : Fq[X]) (hD : D ≠ 0) :
    v.intValuation D ≥ WithZero.exp (-(D.natDegree : ℤ)) := by
  -- Key idea: multiplicity of v in D is bounded by degree of D
  -- because deg(g) ≥ 1 for any irreducible generator g of v
  -- API mismatches with current mathlib - using sorry
  sorry

/-- For any finite adele, there exists k ∈ K such that a - diag(k) is integral at all finite places.

**Proof strategy** (CRT with enlarged set):
1. S = {v : a.val v ∉ O_v} is finite (restricted product property)
2. For each v ∈ S, use `exists_local_approximant` to get y_v ∈ K with a_v - y_v ∈ O_v
3. Let T = S ∪ {all pole places of all y_v} - still finite
4. Let D = ∏_{w∈T} p_w^{N_w} for powers clearing all denominators of y_v
5. Now D · y_v ∈ R = Fq[X] for all v ∈ S
6. By CRT in R, find P with P ≡ D · y_v (mod p_v^{M_v}) for each v ∈ S
7. Set k = P / D
8. Verify: a_v - k ∈ O_v for all v

**Key insight**: We work entirely with global elements y_v ∈ K, then do CRT in R.
-/
theorem exists_finite_integral_translate (a : FiniteAdeleRing Fq[X] (RatFunc Fq)) :
    ∃ k : RatFunc Fq, ∀ v, (a.val v - k) ∈ v.adicCompletionIntegers (RatFunc Fq) := by
  /-
  **Proof approach** (CRT with enlarged set - preserved for future reference):

  1. S = {v : a.val v ∉ O_v} is finite (restricted product property)
  2. For each v ∈ S, use `exists_local_approximant` to get y_v ∈ K with a_v - y_v ∈ O_v
  3. Let D = ∏_{v∈S} (y_v).denom - clears all denominators
  4. D · y_v ∈ R for all v ∈ S, call it Py_v
  5. T = S ∪ {v : v.intValuation D < 1} - finite by HeightOneSpectrum.finite_divisors
  6. Apply CRT: ∃ P with P ≡ Py_v (mod v^{deg(D)+1}) for v ∈ S, P ≡ 0 for v ∈ T\S
  7. Let k = P / D

  Verification for v ∈ S:
  - a_v - k = (a_v - y_v) - (k - y_v)
  - k - y_v = (P - Py_v)/D
  - val_v(P - Py_v) ≤ exp(-(deg(D)+1)) (from CRT)
  - val_v(D) ≥ exp(-deg(D)) (by intValuation_ge_exp_neg_natDegree)
  - So val_v((P - Py_v)/D) ≤ exp(-1) ≤ 1, hence k - y_v ∈ O_v
  - By ultrametric: a_v - k ∈ O_v

  Verification for v ∈ T\S:
  - a_v ∈ O_v (since v ∉ S)
  - val_v(P) ≤ exp(-(deg(D)+1)) (from CRT)
  - val_v(D) ≥ exp(-deg(D))
  - So val_v(k) = val_v(P/D) ≤ exp(-1) ≤ 1

  Verification for v ∉ T:
  - a_v ∈ O_v (since v ∉ S ⊆ T)
  - val_v(D) = 1 (since v doesn't divide D)
  - val_v(P) ≤ 1 (P is polynomial)
  - val_v(k) = val_v(P)/val_v(D) ≤ 1

  API issues blocking this proof:
  - simp issues with RatFunc.algebraMap_apply
  - CRT application type mismatches
  - Various valuation computation issues
  -/
  sorry

/-- Combined: existence of translate with controlled infinity valuation.

This strengthens `exists_finite_integral_translate` by adding a bound on the infinity valuation.
The bound is achievable because for Fq[X]:
- The CRT solution k = P/D where D = ∏_{v∈S} f_v^{n_v} (product of prime powers)
- The numerator P can be chosen with deg(P) < deg(D) (reduce mod D)
- Then |k|_∞ = exp(deg(P) - deg(D)) < 1

**Mathematical proof sketch**:
1. Use `exists_finite_integral_translate` to get k₀ making a - k₀ integral at finite places
2. If |k₀|_∞ > bound, we need to modify k₀
3. Key insight: adding any polynomial p ∈ Fq[X] to k₀ preserves integrality at finite places
   (because polynomials are integral at all finite places)
4. Choose p such that |k₀ + p|_∞ ≤ bound (possible by density at infinity)
-/
theorem exists_finite_integral_translate_with_infty_bound
    (a : FiniteAdeleRing Fq[X] (RatFunc Fq)) (bound : WithZero (Multiplicative ℤ)) :
    ∃ k : RatFunc Fq, (∀ v, (a.val v - k) ∈ v.adicCompletionIntegers (RatFunc Fq)) ∧
      Valued.v (inftyRingHom Fq k) ≤ bound := by
  /-
  **Proof approach** (preserved for future reference):

  1. Get k₀ from exists_finite_integral_translate (finite integrality achieved)
  2. Strategy: Write k₀ = q + r/denom where q is polynomial part, r/denom has |·|_∞ < 1
  3. For bound ≥ 1: k = k₀ - q = r/denom has |k|_∞ < 1 ≤ bound

  Key steps for bound ≥ 1 case:
  - let num := k₀.num, denom := k₀.denom
  - let q := num / denom (EuclideanDomain quotient)
  - let r := num % denom (EuclideanDomain remainder)
  - EuclideanDomain.div_add_mod gives: denom * q + r = num
  - So k₀ = num/denom = q + r/denom
  - Let k = r/denom = k₀ - q
  - Finite integrality: (a.val v - k) = (a.val v - k₀) + q ∈ O_v (q is polynomial → integral)
  - Infinity bound: deg(r) < deg(denom) by EuclideanDomain, so |r/denom|_∞ < 1

  API issues blocking this proof:
  - Need correct lemma for natDegree = 0 → degree = 0 → IsUnit
  - Need FunctionField.inftyValuationDef API for exp(intDegree)
  - Various rewrite patterns not matching current mathlib
  -/
  sorry

/-- Weak approximation: every element can be shifted into integral adeles.

For Fq[X] (a PID), this is straightforward:
- Only finitely many places have non-integral components
- Find a polynomial that "clears denominators" at all these places
- The result lands in the integral adeles

**Proof strategy**:
1. Use `exists_approx_in_ball_infty` to find P with |a.2 - P|_∞ ≤ 1
2. Work with b = a - diag(P), which has |b.2|_∞ ≤ 1
3. Use `exists_finite_integral_translate_with_infty_bound` to find z with:
   - b.1 - diag(z) integral at all finite places
   - |z|_∞ ≤ 1
4. Combine: x = P + z satisfies a - diag(x) ∈ integralFullAdeles
-/
theorem exists_translate_in_integralFullAdeles (a : FqFullAdeleRing Fq) :
    ∃ x : RatFunc Fq, a - fqFullDiagonalEmbedding Fq x ∈ integralFullAdeles Fq := by
  /-
  **Proof approach** (preserved for future reference):

  1. Get P from exists_approx_in_ball_infty: |a.2 - P|_∞ ≤ 1
  2. Let b = a - diag(P), so |b.2|_∞ ≤ 1
  3. Get z from exists_finite_integral_translate_with_infty_bound:
     - b.1 v - z ∈ O_v for all v, and |z|_∞ ≤ 1
  4. Let x = P + z
  5. Finite places: (a - diag(x)).1 v = b.1 v - z ∈ O_v ✓
  6. Infinity: |b.2 - z|_∞ ≤ max(|b.2|_∞, |z|_∞) ≤ 1 by ultrametric ✓

  API issues blocking this proof:
  - Prod.fst_sub / Prod.snd_sub simp lemmas
  - RestrictedProduct.sub_apply not found
  - Ring arithmetic in completions
  -/
  sorry

/-! ### Full Instance -/

/-- FullDiscreteCocompactEmbedding instance for Fq[X] / RatFunc Fq / FqtInfty.

This is the CORRECT axiom class for function fields over finite fields.
Unlike `DiscreteCocompactEmbedding` for finite adeles (which is FALSE),
this instance is TRUE because the infinite place is included.

**Axioms used**:
- `AllIntegersCompact Fq[X] (RatFunc Fq)` for finite adeles compactness
- `Finite (Valued.ResidueField (FqtInfty Fq))` for infinity compactness
-/
instance instFullDiscreteCocompactEmbedding [AllIntegersCompact Fq[X] (RatFunc Fq)]
    [Finite (Valued.ResidueField (FqtInfty Fq))] :
    FullDiscreteCocompactEmbedding Fq[X] (RatFunc Fq) (FqtInfty Fq) where
  discrete := fq_discrete_in_fullAdeles Fq
  closed := fq_closed_in_fullAdeles Fq
  compact_fundamental_domain := by
    refine ⟨integralFullAdeles Fq, isCompact_integralFullAdeles Fq, ?_⟩
    intro a
    exact exists_translate_in_integralFullAdeles Fq a

end FqInstance

/-! ## Summary

This file provides the corrected adelic framework:

### Completed (sorry-free, general definitions)
- `FullAdeleRing R K K_infty` definition as product
- `fullDiagonalEmbedding` into full adeles
- `FullDiscreteCocompactEmbedding` class (corrected axioms)
- `fullDiagonalEmbedding_injective` theorem

### Concrete Instance: Fq[X] / RatFunc Fq / FqtInfty (with sorries)
- `FqFullAdeleRing Fq` type alias
- `inftyEmbedding` : RatFunc Fq →+* FqtInfty Fq
- `fqFullDiagonalEmbedding` into full adeles
- `integralFullAdeles` using Valued.v
- `instFullDiscreteCocompactEmbedding` instance (sorries in proofs)

### Key Insight
The infinite place provides the "missing constraint" that makes K discrete.
- In finite adeles: neighborhoods constrain only finitely many places → K NOT discrete
- In full adeles: |k|_∞ = q^{deg k} constrains degree → K IS discrete
-/

end RiemannRochV2.FullAdeles

end
