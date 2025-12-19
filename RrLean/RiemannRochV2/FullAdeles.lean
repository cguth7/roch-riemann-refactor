/-
# Full Adele Ring with Infinite Place

This file defines the full adele ring as a product of the finite adele ring and the
completion at infinity. This resolves the mathematical obstruction discovered in Cycle 121:
K is NOT discrete in the finite adeles, but IS discrete in the full adeles.

## Mathematical Background

For a function field K = Fq(t) over a finite field Fq:
- The finite adele ring A_f uses only finite places (HeightOneSpectrum primes)
- K is NOT discrete in A_f (every neighborhood of 0 contains infinitely many k ∈ K)
- The full adele ring A = A_f × K_∞ includes the infinite place
- K IS discrete in A (the product formula constrains elements at all places)

## Main Definitions

* `FullAdeleRing R K K_infty` - Product of FiniteAdeleRing and completion at infinity
* `fullDiagonalEmbedding` - Diagonal embedding K → FullAdeleRing
* `FullDiscreteCocompactEmbedding` - K is discrete and cocompact in full adeles

## For Polynomial Fq / RatFunc(Fq)

We use Mathlib's `FqtInfty Fq` (completion at infinity via `inftyValuation`) as K_∞.
This gives:
- `FullAdeleRing (Polynomial Fq) (RatFunc Fq) (FqtInfty Fq)`
- K is discrete in full adeles (provable)
- Cocompact fundamental domain (with class group considerations)

## References

- Cassels-Fröhlich "Algebraic Number Theory" Ch. II (adeles for number fields)
- Weil "Basic Number Theory" Ch. IV (adeles for function fields)
- Mathlib.NumberTheory.FunctionField (FqtInfty, inftyValuation)
-/

import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.DiscreteSubset
import Mathlib.Data.Int.WithZero
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import RrLean.RiemannRochV2.AdelicTopology
import RrLean.RiemannRochV2.FqPolynomialInstance

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open RiemannRochV2.AdelicTopology
open scoped Classical

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace RiemannRochV2.FullAdeles

/-! ## General Definition of Full Adele Ring

For any Dedekind domain R with fraction field K, the full adele ring is parameterized
by a type K_∞ representing the completion at infinity.
-/

section GeneralDefinition

variable (R K)
variable (K_infty : Type*) [Field K_infty] [Algebra K K_infty]

/-- The full adele ring is the product of finite adeles and completion at infinity.

For function fields, this includes ALL places, making K discrete in the full adeles.
For number fields, this generalizes to include all infinite (archimedean) places.
-/
def FullAdeleRing := FiniteAdeleRing R K × K_infty

instance instAddCommGroup : AddCommGroup (FullAdeleRing R K K_infty) :=
  Prod.instAddCommGroup

instance instRing : Ring (FullAdeleRing R K K_infty) :=
  Prod.instRing

variable [TopologicalSpace K_infty]

instance instTopologicalSpace :
    TopologicalSpace (FullAdeleRing R K K_infty) :=
  instTopologicalSpaceProd

variable [IsTopologicalRing K_infty]

-- The FiniteAdeleRing has IsTopologicalRing from Mathlib
-- and K_infty has it by assumption
-- Prod of two topological rings is a topological ring
instance instIsTopologicalRing :
    IsTopologicalRing (FullAdeleRing R K K_infty) := by
  unfold FullAdeleRing
  infer_instance

/-- The diagonal embedding into the full adele ring.

An element k ∈ K is sent to:
- Its diagonal image in FiniteAdeleRing (via Mathlib's algebraMap)
- Its image in K_∞ (via the provided algebra map)
-/
def fullDiagonalEmbedding : K →+* FullAdeleRing R K K_infty :=
  RingHom.prod (FiniteAdeleRing.algebraMap R K) (algebraMap K K_infty)

/-- The projection from full adeles to finite adeles. -/
def projFinite : FullAdeleRing R K K_infty →+* FiniteAdeleRing R K :=
  RingHom.fst _ _

/-- The projection from full adeles to the infinite place. -/
def projInfty : FullAdeleRing R K K_infty →+* K_infty :=
  RingHom.snd _ _

/-- The diagonal embedding is injective when both projections are injective.

For function fields over finite fields, this is always true:
- FiniteAdeleRing embedding is injective (Dedekind domain has height-one primes)
- K_∞ embedding is injective (field extension)
-/
theorem fullDiagonalEmbedding_injective
    [Nonempty (HeightOneSpectrum R)]
    (h_infty : Function.Injective (algebraMap K K_infty)) :
    Function.Injective (fullDiagonalEmbedding R K K_infty) := by
  intro x y hxy
  -- Extract equality in both components
  have h2 : projInfty R K K_infty (fullDiagonalEmbedding R K K_infty x) =
            projInfty R K K_infty (fullDiagonalEmbedding R K K_infty y) := by
    simp only [hxy]
  -- Use injectivity of K → K_∞
  simp only [fullDiagonalEmbedding, projInfty] at h2
  exact h_infty h2

end GeneralDefinition

/-! ## Full Discrete Cocompact Embedding

This is the corrected version of DiscreteCocompactEmbedding that uses full adeles.
K IS discrete in the full adele ring.
-/

section FullDiscreteCocompact

variable (R K)
variable (K_infty : Type*) [Field K_infty] [Algebra K K_infty]
variable [TopologicalSpace K_infty] [IsTopologicalRing K_infty]

/-- Hypothesis: The diagonal embedding of K is discrete and cocompact in FULL adeles.

This is the corrected version of DiscreteCocompactEmbedding. Unlike the finite adele
version (which is FALSE), this statement is TRUE for function fields when K_∞ is the
completion at infinity.

Key difference from finite adeles:
- In finite adeles: neighborhoods constrain only finitely many places
- In full adeles: neighborhoods constrain all places including infinity
- The product formula ∏_v |x|_v = 1 enforces discreteness when all places are included
-/
class FullDiscreteCocompactEmbedding : Prop where
  /-- K is discrete in the full adele ring. -/
  discrete : DiscreteTopology (Set.range (fullDiagonalEmbedding R K K_infty))
  /-- K is closed in the full adele ring. -/
  closed : IsClosed (Set.range (fullDiagonalEmbedding R K K_infty))
  /-- There exists a compact fundamental domain for K in the full adeles. -/
  compact_fundamental_domain : ∃ (F : Set (FullAdeleRing R K K_infty)), IsCompact F ∧
      ∀ a, ∃ x : K, a - fullDiagonalEmbedding R K K_infty x ∈ F

/-- The image of K under the full diagonal embedding is closed. -/
theorem full_closed_diagonal [FullDiscreteCocompactEmbedding R K K_infty] :
    IsClosed (Set.range (fullDiagonalEmbedding R K K_infty)) :=
  FullDiscreteCocompactEmbedding.closed

/-- The image of K under the full diagonal embedding is discrete. -/
theorem full_discrete_diagonal [FullDiscreteCocompactEmbedding R K K_infty] :
    DiscreteTopology (Set.range (fullDiagonalEmbedding R K K_infty)) :=
  FullDiscreteCocompactEmbedding.discrete

/-- The full adelic Minkowski theorem. -/
theorem full_compact_adelic_quotient [FullDiscreteCocompactEmbedding R K K_infty] :
    ∃ (F : Set (FullAdeleRing R K K_infty)), IsCompact F ∧
      ∀ a, ∃ x : K, a - fullDiagonalEmbedding R K K_infty x ∈ F :=
  FullDiscreteCocompactEmbedding.compact_fundamental_domain

end FullDiscreteCocompact

/-! ## Concrete Instance: Polynomial Fq / RatFunc(Fq)

For function fields, we would use Mathlib's `FqtInfty Fq` as the completion at infinity.
This is the completion of `RatFunc Fq` with respect to `inftyValuation`.

**Status**: The concrete instance requires careful navigation of Mathlib's completion API:
- `FunctionField.FqtInfty Fq` is the completion type
- The `Algebra (RatFunc Fq) (FqtInfty Fq)` instance comes from `UniformSpace.Completion`
- The valuation on completion elements uses `Valued.v` (not `inftyValuation` directly)

This will be instantiated in a future cycle once the API is better understood.
-/

/-! ### Why K IS discrete in full adeles

The key difference from finite adeles:

**Finite adeles (K NOT discrete)**:
- Neighborhoods of 0 constrain finitely many finite places
- For any finite set S of primes, the ideal ∏_{p∈S} p contains infinitely many polynomials
- Hence K ∩ U is infinite for every neighborhood U

**Full adeles (K IS discrete)**:
- Neighborhoods constrain all places including infinity
- For k ∈ K nonzero: ∏_v |k|_v = 1 (product formula)
- If |k|_p ≤ 1 for all finite p, then |k|_∞ ≥ 1 (forced by product formula)
- Conversely, if |k|_∞ < ε for small ε, then |k|_p > 1 for some finite p
- This extra constraint from infinity makes K discrete

**Mathematical proof sketch**:
1. Take neighborhood U = U_f × U_∞ where:
   - U_f constrains finitely many finite places (val ≥ 1)
   - U_∞ constrains infinity (val ≥ N for large N)
2. For k ∈ K with diagonal(k) ∈ U:
   - |k|_p ≤ 1 for almost all finite p (finitely many exceptions bounded by U_f)
   - |k|_∞ ≤ ε for small ε (from U_∞)
3. Product formula: if all |k|_v ≤ 1 and |k|_∞ ≤ ε, then |k|_v = 1 a.a. and k bounded
4. Only finitely many k ∈ K satisfy these bounds (Riemann-Roch!)
5. Hence K ∩ U is finite, making K discrete.
-/

/-! ## Concrete Instance: Polynomial Fq / RatFunc(Fq) / FqtInfty

For function fields over finite fields, we instantiate the full adeles using:
- R = Polynomial Fq (the integer ring)
- K = RatFunc Fq (the fraction field / function field)
- K_∞ = FqtInfty Fq (completion at infinity)
-/

section FqInstance

open FunctionField Polynomial
open scoped Polynomial

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

/-- There exist height-one primes in Fq[X] (e.g., the ideal generated by X). -/
instance : Nonempty (HeightOneSpectrum Fq[X]) := by
  -- X is irreducible in Fq[X], so (X) is a height-one prime
  have hX : Irreducible (X : Fq[X]) := Polynomial.irreducible_X
  have hX_ne : (X : Fq[X]) ≠ 0 := Polynomial.X_ne_zero
  have hprime : (Ideal.span {X} : Ideal Fq[X]).IsPrime :=
    (Ideal.span_singleton_prime hX_ne).mpr hX.prime
  have hne_bot : (Ideal.span {X} : Ideal Fq[X]) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact hX_ne
  exact ⟨⟨Ideal.span {X}, hprime, hne_bot⟩⟩

/-- Type alias for the full adele ring of Fq(t). -/
abbrev FqFullAdeleRing : Type _ := FullAdeleRing Fq[X] (RatFunc Fq) (FqtInfty Fq)

/-- The ring homomorphism from RatFunc Fq to FqtInfty Fq via completion.

FqtInfty is the uniform space completion of RatFunc Fq with respect to inftyValuation.
The coeRingHom provides the canonical embedding.
-/
noncomputable def inftyRingHom : RatFunc Fq →+* FqtInfty Fq := by
  -- FqtInfty Fq = UniformSpace.Completion (RatFunc Fq) with valued uniform structure
  -- UniformSpace.Completion.coeRingHom gives the embedding
  letI : Valued (RatFunc Fq) (WithZero (Multiplicative ℤ)) := FunctionField.inftyValuedFqt Fq
  exact UniformSpace.Completion.coeRingHom

/-- The Algebra instance from RatFunc Fq to FqtInfty Fq.

Constructed from the ring homomorphism given by the completion embedding.
-/
noncomputable instance instAlgebraRatFuncFqtInfty : Algebra (RatFunc Fq) (FqtInfty Fq) :=
  (inftyRingHom Fq).toAlgebra

/-- The embedding of RatFunc Fq into FqtInfty Fq is injective.

This is a standard property of completions: the original space embeds as a
dense subspace, and hence injectively (for separated spaces).
-/
theorem algebraMap_FqtInfty_injective :
    Function.Injective (algebraMap (RatFunc Fq) (FqtInfty Fq)) := by
  -- The algebraMap is inftyRingHom, which is the completion embedding
  show Function.Injective (inftyRingHom Fq)
  -- Strategy: Use the fact that coeRingHom is injective for T0 spaces
  intro x y hxy
  -- inftyRingHom Fq = coeRingHom with the valued uniform space from inftyValuedFqt
  -- FqtInfty Fq = Completion of (RatFunc Fq) with this uniform space
  -- hxy : (↑x : FqtInfty Fq) = (↑y : FqtInfty Fq)
  simp only [inftyRingHom] at hxy
  -- Need Valued instance for T0Space (ValuedRing.separated)
  letI : Valued (RatFunc Fq) (WithZero (Multiplicative ℤ)) := FunctionField.inftyValuedFqt Fq
  -- RatFunc Fq is T0 (Valued rings are T0 by ValuedRing.separated)
  -- Use coe_inj: (↑x : Completion α) = ↑y ↔ x = y
  exact UniformSpace.Completion.coe_inj.mp hxy

/-- The diagonal embedding for Fq(t) into full adeles.

Combines:
- Finite places: FiniteAdeleRing.algebraMap (the existing diagonal into finite adeles)
- Infinite place: algebraMap to FqtInfty (completion at infinity)
-/
def fqFullDiagonalEmbedding : RatFunc Fq →+* FqFullAdeleRing Fq :=
  fullDiagonalEmbedding Fq[X] (RatFunc Fq) (FqtInfty Fq)

/-- The full diagonal embedding for Fq(t) is injective. -/
theorem fqFullDiagonalEmbedding_injective :
    Function.Injective (fqFullDiagonalEmbedding Fq) := by
  apply fullDiagonalEmbedding_injective
  exact algebraMap_FqtInfty_injective Fq

/-! ### Integral Full Adeles

The integral full adeles are elements that are:
1. Integral at all finite places (a_v ∈ O_v)
2. Integral at infinity (|a_∞|_∞ ≤ 1)

For valuations on the completion, we use `Valued.v` which extends the valuation.
-/

/-- The integral full adeles for Fq(t).

An element (a_f, a_∞) is integral if:
- a_f ∈ ∏_v O_v (integral at all finite places)
- Valued.v a_∞ ≤ 1 (integral at infinity, using the extended valuation)
-/
def integralFullAdeles : Set (FqFullAdeleRing Fq) :=
  {a | (∀ v, a.1.val v ∈ v.adicCompletionIntegers (RatFunc Fq)) ∧
       Valued.v a.2 ≤ 1}

/-! ### Key Helper Lemmas for Discreteness

These lemmas establish the core algebraic facts needed for discreteness.
-/

/-- For a nonzero polynomial, the infinity valuation is ≥ 1.

This is because inftyValuation(p) = exp(deg p) and exp(n) ≥ 1 for n ≥ 0.
-/
theorem polynomial_inftyVal_ge_one {p : Fq[X]} (hp : p ≠ 0) :
    1 ≤ FunctionField.inftyValuationDef Fq (algebraMap Fq[X] (RatFunc Fq) p) := by
  rw [FunctionField.inftyValuation.polynomial (Fq := Fq) hp]
  -- exp(natDegree) ≥ 1 since natDegree ≥ 0 and 1 = exp 0
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  exact Int.ofNat_nonneg _

/-- The open ball {x | Valued.v x < 1} in FqtInfty is open.

This follows from the general fact that balls in valued rings are clopen.
-/
theorem isOpen_inftyBall_lt_one :
    IsOpen {x : FqtInfty Fq | Valued.v x < (1 : WithZero (Multiplicative ℤ))} :=
  (Valued.isClopen_ball (R := FqtInfty Fq) (1 : WithZero (Multiplicative ℤ))).isOpen

/-- Key algebraic lemma: an element of RatFunc Fq that is integral at all finite places
is in the image of Polynomial Fq.

Proof sketch: If k = p/q with gcd(p,q) = 1, and |k|_v ≤ 1 for all finite v, then q has
no prime factors (since at any prime dividing q but not p, we'd have |k|_v > 1).
Hence q is a unit, so k is a polynomial.
-/
theorem finite_integral_implies_polynomial (k : RatFunc Fq)
    (hint : ∀ v : HeightOneSpectrum Fq[X], v.valuation (RatFunc Fq) k ≤ 1) :
    ∃ p : Fq[X], algebraMap Fq[X] (RatFunc Fq) p = k := by
  -- Strategy: Show denom(k) = 1, hence k is a polynomial
  -- If denom(k) ≠ 1, then it has an irreducible factor p
  -- This creates a HeightOneSpectrum v where |k|_v > 1, contradiction
  let d := k.denom
  let n := k.num
  have hd_monic : d.Monic := RatFunc.monic_denom k
  have hd_ne : d ≠ 0 := RatFunc.denom_ne_zero k
  have hcop : IsCoprime n d := RatFunc.isCoprime_num_denom k
  have hk_eq : algebraMap Fq[X] (RatFunc Fq) n / algebraMap Fq[X] (RatFunc Fq) d = k :=
    RatFunc.num_div_denom k
  -- Goal: show d = 1
  suffices hd_one : d = 1 by
    use n
    rw [← hk_eq, hd_one, map_one, div_one]
  -- Suppose d ≠ 1, derive contradiction
  by_contra hd_ne_one
  -- Monic polynomial ≠ 1 means it's not a unit
  have hd_not_unit : ¬IsUnit d := by
    intro h
    exact hd_ne_one (hd_monic.eq_one_of_isUnit h)
  -- In UFD (Fq[X] is a PID hence UFD), non-unit non-zero has irreducible factor
  obtain ⟨p, hp_irr, hp_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hd_not_unit hd_ne
  -- p is prime (in UFD, irreducible ⟹ prime)
  have hp_prime : Prime p := hp_irr.prime
  have hp_ne : p ≠ 0 := hp_prime.ne_zero
  -- Construct HeightOneSpectrum from p
  have hp_ideal_prime : (Ideal.span {p}).IsPrime :=
    (Ideal.span_singleton_prime hp_ne).mpr hp_prime
  have hp_ideal_ne_bot : (Ideal.span {p} : Ideal Fq[X]) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact hp_ne
  let v : HeightOneSpectrum Fq[X] := ⟨Ideal.span {p}, hp_ideal_prime, hp_ideal_ne_bot⟩
  -- Since p | d, we have d ∈ v.asIdeal
  have hd_in_v : d ∈ v.asIdeal := by
    simp only [v]
    rw [Ideal.mem_span_singleton]
    exact hp_dvd
  -- So v.intValuation d < 1
  have hval_d : v.intValuation d < 1 := (intValuation_lt_one_iff_mem v d).mpr hd_in_v
  -- By coprimality, p does not divide n
  have hp_not_dvd_n : ¬(p ∣ n) := by
    -- Need to show p ∤ n given IsCoprime n d and p | d
    -- IsCoprime n d means ∃ a b, a*n + b*d = 1
    -- If p | n and p | d, then p | (a*n + b*d) = 1, so p is a unit
    -- But p is irreducible, hence not a unit. Contradiction.
    intro hdvd_n
    -- p divides both n and d, hence divides their linear combination
    obtain ⟨a, b, hab⟩ := hcop
    have hp_dvd_one : p ∣ 1 := by
      calc p ∣ a * n + b * d := dvd_add (dvd_mul_of_dvd_right hdvd_n a) (dvd_mul_of_dvd_right hp_dvd b)
           _ = 1 := hab
    -- p | 1 means p is a unit, contradicting irreducibility
    have hp_unit : IsUnit p := isUnit_of_dvd_one hp_dvd_one
    exact hp_irr.1 hp_unit
  -- So n ∉ v.asIdeal
  have hn_not_in_v : n ∉ v.asIdeal := by
    simp only [v]
    rw [Ideal.mem_span_singleton]
    exact hp_not_dvd_n
  -- So v.intValuation n = 1
  have hval_n : v.intValuation n = 1 := intValuation_eq_one_iff.mpr hn_not_in_v
  -- Now compute v.valuation k
  -- k = n / d, so v.valuation k = v.valuation n / v.valuation d
  have hval_k : v.valuation (RatFunc Fq) k = v.intValuation n / v.intValuation d := by
    rw [← hk_eq]
    rw [map_div₀]
    congr 1
    · exact v.valuation_of_algebraMap n
    · exact v.valuation_of_algebraMap d
  -- v.intValuation n = 1, v.intValuation d < 1
  -- So v.valuation k = 1 / (something < 1) > 1
  specialize hint v
  rw [hval_k, hval_n, one_div] at hint
  -- hint : (v.intValuation d)⁻¹ ≤ 1
  -- hval_d : v.intValuation d < 1
  -- In ordered group with zero, if 0 < x < 1, then x⁻¹ > 1
  have hd_mem : d ∈ nonZeroDivisors Fq[X] := mem_nonZeroDivisors_of_ne_zero hd_ne
  have hval_d_ne : v.intValuation d ≠ 0 := v.intValuation_ne_zero' ⟨d, hd_mem⟩
  have hval_d_pos : 0 < v.intValuation d := zero_lt_iff.mpr hval_d_ne
  have hcontra : 1 < (v.intValuation d)⁻¹ := by
    rw [one_lt_inv_iff₀]
    exact ⟨hval_d_pos, hval_d⟩
  -- From hint: x⁻¹ ≤ 1 and hcontra: 1 < x⁻¹, derive contradiction
  exact (not_lt.mpr hint) hcontra

/-- Consequence: For a nonzero k ∈ RatFunc Fq that is integral at all finite places,
the infinity valuation is ≥ 1 (since k is a nonzero polynomial). -/
theorem finite_integral_inftyVal_ge_one (k : RatFunc Fq) (hk : k ≠ 0)
    (hint : ∀ v : HeightOneSpectrum Fq[X], v.valuation (RatFunc Fq) k ≤ 1) :
    1 ≤ FunctionField.inftyValuationDef Fq k := by
  obtain ⟨p, hp⟩ := finite_integral_implies_polynomial Fq k hint
  have hp_ne : p ≠ 0 := by
    intro h
    simp only [h, map_zero] at hp
    exact hk hp.symm
  rw [← hp]
  exact polynomial_inftyVal_ge_one (Fq := Fq) hp_ne

/-! ### Helper Lemmas for Discreteness -/

/-- The set of integral finite adeles is open. -/
theorem isOpen_integralFiniteAdeles :
    IsOpen {a : FiniteAdeleRing Fq[X] (RatFunc Fq) |
      ∀ v, a.1 v ∈ v.adicCompletionIntegers (RatFunc Fq)} := by
  have hOv_open : ∀ v : HeightOneSpectrum Fq[X],
      IsOpen (v.adicCompletionIntegers (RatFunc Fq) : Set (v.adicCompletion (RatFunc Fq))) :=
    fun v ↦ Valued.isOpen_valuationSubring _
  exact RestrictedProduct.isOpen_forall_mem hOv_open

/-- For d in the fraction field, if diag(d).1 v ∈ O_v then v.valuation d ≤ 1. -/
theorem diag_integral_implies_valuation_le (d : RatFunc Fq) (v : HeightOneSpectrum Fq[X])
    (h : (fqFullDiagonalEmbedding Fq d).1.1 v ∈ v.adicCompletionIntegers (RatFunc Fq)) :
    v.valuation (RatFunc Fq) d ≤ 1 := by
  rw [mem_adicCompletionIntegers] at h
  -- The finite component of diag(d) at v equals d coerced to the completion
  -- (fqFullDiagonalEmbedding Fq d).1 = FiniteAdeleRing.algebraMap d
  -- and at v: (FiniteAdeleRing.algebraMap d) v = (d : v.adicCompletion K)
  have heq : (fqFullDiagonalEmbedding Fq d).1.1 v = (d : v.adicCompletion (RatFunc Fq)) := rfl
  rw [heq, valuedAdicCompletion_eq_valuation'] at h
  exact h

/-- The infinity component of diag(d) has valuation equal to inftyValuationDef. -/
theorem diag_infty_valuation (d : RatFunc Fq) :
    Valued.v ((fqFullDiagonalEmbedding Fq d).2) = FunctionField.inftyValuationDef Fq d := by
  -- The second component is algebraMap d = inftyRingHom Fq d
  -- The Valued instance on FqtInfty is valuedFqtInfty
  -- valuedFqtInfty = (inftyValuedFqt Fq).valuedCompletion
  -- For x : RatFunc Fq, valuedCompletion_apply says Valued.v (x : hat K) = v x
  -- where v = (inftyValuedFqt Fq).v = inftyValuationDef Fq
  have heq : (fqFullDiagonalEmbedding Fq d).2 = inftyRingHom Fq d := rfl
  rw [heq, FunctionField.valuedFqtInfty.def]
  -- Now: (inftyValuedFqt Fq).extension (inftyRingHom Fq d) = inftyValuationDef Fq d
  -- inftyRingHom is UniformSpace.Completion.coeRingHom with inftyValuedFqt
  -- By extension_extends, extension ↑x = v x for x : K
  simp only [inftyRingHom]
  -- Now: Valued.extension (coeRingHom d) = inftyValuationDef Fq d
  -- coeRingHom d is definitionally (d : Completion (RatFunc Fq))
  -- Use convert to handle the definitional equality
  letI : Valued (RatFunc Fq) (WithZero (Multiplicative ℤ)) := FunctionField.inftyValuedFqt Fq
  convert Valued.extension_extends (K := RatFunc Fq) d using 2

/-- Discreteness of Fq(t) in full adeles.

**Proof strategy**:
1. U_fin = {a | ∀ v, a_v ∈ O_v} is open (by isOpen_integralFiniteAdeles using RestrictedProduct.isOpen_forall_mem)
2. U_infty = {x | |x|_∞ < 1} is open (by isOpen_inftyBall_lt_one)
3. U = preimage of (U_fin × U_infty) under translation by diag(k) is open
4. For diag(m) ∈ U: let d = m - k, then diag(d) ∈ U_fin × U_infty
5. From U_fin: d is integral at all finite places
6. By finite_integral_implies_polynomial: d is a polynomial
7. From U_infty: |d|_∞ < 1
8. By polynomial_inftyVal_ge_one: nonzero polynomial has |·|_∞ ≥ 1
9. Contradiction unless d = 0, so m = k
-/
theorem fq_discrete_in_fullAdeles :
    DiscreteTopology (Set.range (fqFullDiagonalEmbedding Fq)) := by
  -- Use discreteTopology_subtype_iff': for each y in range, find open U with U ∩ range = {y}
  rw [discreteTopology_subtype_iff']
  intro y hy
  -- y is in the range, so y = diag(k) for some k
  obtain ⟨k, hk⟩ := hy
  -- Define U = {a | (a - y).1 is integral at all finite places ∧ Valued.v (a - y).2 < 1}
  let U_fin : Set (FiniteAdeleRing Fq[X] (RatFunc Fq)) :=
    {b | ∀ v, b.1 v ∈ v.adicCompletionIntegers (RatFunc Fq)}
  let U_infty : Set (FqtInfty Fq) := {x | Valued.v x < 1}
  let U : Set (FqFullAdeleRing Fq) := {a | a.1 - y.1 ∈ U_fin ∧ a.2 - y.2 ∈ U_infty}
  refine ⟨U, ?_, ?_⟩
  · -- U is open: preimage of open product under continuous subtraction
    have hU_fin_open : IsOpen U_fin := isOpen_integralFiniteAdeles Fq
    have hU_infty_open : IsOpen U_infty := isOpen_inftyBall_lt_one Fq
    have hprod_open : IsOpen (U_fin ×ˢ U_infty) := hU_fin_open.prod hU_infty_open
    have hU_eq : U = (fun a : FqFullAdeleRing Fq => (a.1 - y.1, a.2 - y.2)) ⁻¹' (U_fin ×ˢ U_infty) := rfl
    rw [hU_eq]
    apply IsOpen.preimage _ hprod_open
    have h1 : Continuous (fun a : FqFullAdeleRing Fq => a.1 - y.1) := continuous_fst.sub continuous_const
    have h2 : Continuous (fun a : FqFullAdeleRing Fq => a.2 - y.2) := continuous_snd.sub continuous_const
    exact Continuous.prodMk h1 h2
  · -- U ∩ range = {y}
    ext a
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · -- If a ∈ U and a ∈ range, then a = y
      intro ⟨⟨ha_fin, ha_infty⟩, ⟨m, hm⟩⟩
      -- Substitute a = diag(m)
      subst hm
      -- Now we need: fqFullDiagonalEmbedding Fq m = y, where y = fqFullDiagonalEmbedding Fq k
      -- Let d = m - k
      set d := m - k with hd_def
      -- Key: diag(m) - diag(k) = diag(m - k) = diag(d)
      have hdiag_sub : fqFullDiagonalEmbedding Fq m - fqFullDiagonalEmbedding Fq k =
          fqFullDiagonalEmbedding Fq d := by simp only [hd_def, map_sub]
      -- ha_fin tells us: (diag(m).1 - y.1).val v ∈ O_v for all v
      -- Since y = diag(k), we rewrite and get diag(d).1.val v ∈ O_v
      have hd_integral : ∀ v : HeightOneSpectrum Fq[X], (fqFullDiagonalEmbedding Fq d).1.val v ∈
          v.adicCompletionIntegers (RatFunc Fq) := fun v => by
        have h1 := ha_fin v
        -- The key: (diag(m).1 - diag(k).1) = diag(d).1
        have h2 : (fqFullDiagonalEmbedding Fq m).1 - (fqFullDiagonalEmbedding Fq k).1 =
            (fqFullDiagonalEmbedding Fq d).1 := congr_arg Prod.fst hdiag_sub
        -- hk : fqFullDiagonalEmbedding Fq k = y, so ← hk replaces y with diag(k)
        simp only [← hk] at h1
        -- h1 : ((diag m).1 - (diag k).1).val v ∈ O_v
        -- h2 : (diag m).1 - (diag k).1 = (diag d).1
        rw [← h2]; exact h1
      -- Using diag_integral_implies_valuation_le: d is integral at all finite places
      have hd_val_le : ∀ v : HeightOneSpectrum Fq[X], v.valuation (RatFunc Fq) d ≤ 1 := fun v =>
        diag_integral_implies_valuation_le Fq d v (hd_integral v)
      -- ha_infty tells us: Valued.v (diag(m).2 - y.2) < 1
      -- Since y = diag(k), this is Valued.v (diag(d).2) < 1
      have hd_infty_lt : Valued.v ((fqFullDiagonalEmbedding Fq d).2) < 1 := by
        have h1 := ha_infty
        have h2 : (fqFullDiagonalEmbedding Fq m).2 - (fqFullDiagonalEmbedding Fq k).2 =
            (fqFullDiagonalEmbedding Fq d).2 := congr_arg Prod.snd hdiag_sub
        simp only [← hk] at h1
        rw [← h2]; exact h1
      -- Valued.v (diag(d).2) = inftyValuationDef d
      have hd_infty_eq : FunctionField.inftyValuationDef Fq d < 1 := by
        rw [← diag_infty_valuation Fq d]; exact hd_infty_lt
      -- Now we show d = 0
      have hd_zero : d = 0 := by
        by_contra hd_ne
        obtain ⟨p, hp⟩ := finite_integral_implies_polynomial Fq d hd_val_le
        have hp_ne : p ≠ 0 := by rintro rfl; simp at hp; exact hd_ne hp.symm
        have hp_val := polynomial_inftyVal_ge_one (Fq := Fq) hp_ne
        -- hp : algebraMap p = d, so inftyValuationDef d = inftyValuationDef (algebraMap p)
        rw [← hp] at hd_infty_eq
        exact not_lt.mpr hp_val hd_infty_eq
      -- d = 0 means m = k, so diag(m) = diag(k) = y
      have hm_eq_k : m = k := sub_eq_zero.mp hd_zero
      simp only [hm_eq_k, hk]
    · -- If a = y, then a ∈ U ∩ range
      intro ha_eq
      subst ha_eq
      refine ⟨⟨?_, ?_⟩, ⟨k, hk⟩⟩
      · -- y.1 - y.1 = 0 is in U_fin (0 ∈ O_v for all v)
        intro v
        simp only [sub_self]
        -- Goal: (0 : FiniteAdeleRing).val v ∈ O_v
        -- 0.val v = 0 in v.adicCompletion, and 0 ∈ O_v
        rw [mem_adicCompletionIntegers]
        -- Goal: Valued.v ((0 : FiniteAdeleRing).val v) ≤ 1
        -- (0 : FiniteAdeleRing).val = 0 (as a function to the product)
        have h0 : (0 : FiniteAdeleRing Fq[X] (RatFunc Fq)).val v = 0 := by
          rfl
        rw [h0, Valuation.map_zero]
        exact zero_le'
      · -- y.2 - y.2 = 0 ∈ U_infty: Valued.v 0 < 1
        simp only [sub_self]
        show Valued.v (0 : FqtInfty Fq) < 1
        simp only [map_zero]
        exact zero_lt_one

/-- Closedness of Fq(t) in full adeles.

Discrete subgroups of Hausdorff groups are closed.
-/
theorem fq_closed_in_fullAdeles :
    IsClosed (Set.range (fqFullDiagonalEmbedding Fq)) := by
  -- Strategy:
  -- 1. Show FqFullAdeleRing Fq is T2Space (product of T2 spaces)
  -- 2. The range is an AddSubgroup with discrete topology
  -- 3. Apply AddSubgroup.isClosed_of_discrete
  --
  -- Step 1: T2Space for FqFullAdeleRing = FiniteAdeleRing × FqtInfty
  -- FqtInfty has Valued instance → T2 via IsTopologicalAddGroup.t2Space_of_zero_sep
  haveI hT2_infty : T2Space (FqtInfty Fq) := by
    apply IsTopologicalAddGroup.t2Space_of_zero_sep
    intro x x_ne
    -- Use Valued structure: {y | Valued.v y < Valued.v x} is a neighborhood of 0 not containing x
    refine ⟨{ k | Valued.v k < Valued.v x }, ?_, ?_⟩
    · rw [Valued.mem_nhds]
      have vx_ne := (Valuation.ne_zero_iff (Valued.v (R := FqtInfty Fq))).mpr x_ne
      exact ⟨Units.mk0 _ vx_ne, fun y hy => by simpa using hy⟩
    · simp only [Set.mem_setOf_eq]
      exact lt_irrefl _
  -- FiniteAdeleRing is T2 (RestrictedProduct of T2 spaces is T2)
  -- Each v.adicCompletion K is Valued → T2 by the same argument as FqtInfty
  haveI hT2_components : ∀ v : HeightOneSpectrum Fq[X], T2Space (v.adicCompletion (RatFunc Fq)) := fun v => by
    apply IsTopologicalAddGroup.t2Space_of_zero_sep
    intro x x_ne
    refine ⟨{ k | Valued.v k < Valued.v x }, ?_, ?_⟩
    · rw [Valued.mem_nhds]
      have vx_ne := (Valuation.ne_zero_iff (Valued.v (R := v.adicCompletion (RatFunc Fq)))).mpr x_ne
      exact ⟨Units.mk0 _ vx_ne, fun y hy => by simpa using hy⟩
    · simp only [Set.mem_setOf_eq]
      exact lt_irrefl _
  -- FiniteAdeleRing = RestrictedProduct, and RestrictedProduct of T2 is T2
  -- Use T2Space.of_injective_continuous with the embedding into Pi
  haveI hT2_fin : T2Space (FiniteAdeleRing Fq[X] (RatFunc Fq)) :=
    T2Space.of_injective_continuous DFunLike.coe_injective RestrictedProduct.continuous_coe
  -- Product of T2 is T2
  haveI : T2Space (FqFullAdeleRing Fq) := Prod.t2Space
  -- Step 2: The range is an AddSubgroup
  have hrange : Set.range (fqFullDiagonalEmbedding Fq) =
      ((fqFullDiagonalEmbedding Fq).range.toAddSubgroup : Set _) := by
    ext x
    simp only [Set.mem_range]
    constructor <;> intro ⟨a, ha⟩ <;> exact ⟨a, ha⟩
  -- Step 3: The range has discrete topology (from fq_discrete_in_fullAdeles)
  haveI hdiscrete : DiscreteTopology (Set.range (fqFullDiagonalEmbedding Fq)) := fq_discrete_in_fullAdeles Fq
  -- The carrier set of the AddSubgroup equals Set.range
  have hcarrier : ((fqFullDiagonalEmbedding Fq).range.toAddSubgroup : Set _) =
      Set.range (fqFullDiagonalEmbedding Fq) := by
    ext x
    simp only [Set.mem_range]
    constructor <;> intro ⟨a, ha⟩ <;> exact ⟨a, ha⟩
  -- Transfer discrete topology via the carrier equality
  haveI : DiscreteTopology (fqFullDiagonalEmbedding Fq).range.toAddSubgroup := by
    -- Use SetLike.isDiscrete_iff_discreteTopology
    rw [← SetLike.isDiscrete_iff_discreteTopology, hcarrier]
    exact isDiscrete_iff_discreteTopology.mpr hdiscrete
  -- Apply AddSubgroup.isClosed_of_discrete
  rw [hrange]
  exact AddSubgroup.isClosed_of_discrete

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
    intro h0
    have hval : Valued.v (inftyRingHom Fq (1 / RatFunc.X)) =
        FunctionField.inftyValuationDef Fq (1 / RatFunc.X) :=
      valued_FqtInfty_eq_inftyValuationDef Fq (1 / RatFunc.X)
    rw [h0] at hval
    -- inftyValuationDef (1/X) = exp(-1) ≠ 0 (using inftyValuation.X_inv)
    have hX_inv : FunctionField.inftyValuationDef Fq (1 / RatFunc.X) = WithZero.exp (-1) := by
      rw [← FunctionField.inftyValuation_apply]
      exact FunctionField.inftyValuation.X_inv Fq
    rw [hX_inv] at hval
    exact WithZero.coe_ne_zero hval.symm
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

/-- The integer ring of FqtInfty is complete (as a closed subset of a complete space). -/
instance completeSpace_integer_FqtInfty :
    CompleteSpace (Valued.integer (FqtInfty Fq)) := by
  haveI : IsClosed (Valued.integer (FqtInfty Fq) : Set (FqtInfty Fq)) :=
    isClosed_integer_FqtInfty Fq
  exact IsClosed.completeSpace_coe

/-- The valuation range on FqtInfty is nontrivial.

This is used to show the integer ring is a PID.
-/
lemma range_nontrivial_FqtInfty :
    (Valued.v : Valuation (FqtInfty Fq) ℤᵐ⁰).toMonoidWithZeroHom.range_nontrivial := by
  rw [MonoidWithZeroHom.range_nontrivial]
  use Valued.v (inftyRingHom Fq (1 / RatFunc.X))
  constructor
  · -- ≠ 0
    rw [valued_FqtInfty_eq_inftyValuationDef, ← FunctionField.inftyValuation_apply,
        FunctionField.inftyValuation.X_inv]
    exact WithZero.coe_ne_zero
  · -- ≠ 1
    rw [valued_FqtInfty_eq_inftyValuationDef, ← FunctionField.inftyValuation_apply,
        FunctionField.inftyValuation.X_inv, ← WithZero.exp_zero]
    exact (WithZero.exp_injective).ne (by norm_num : (-1 : ℤ) ≠ 0)

/-- The integer ring of FqtInfty is a principal ideal ring. -/
instance isPrincipalIdealRing_integer_FqtInfty :
    IsPrincipalIdealRing (Valued.integer (FqtInfty Fq)) := by
  rw [(Valuation.valuationSubring.integers (Valued.v (R := FqtInfty Fq))).isPrincipalIdealRing_iff_not_denselyOrdered,
    WithZero.denselyOrdered_set_iff_subsingleton]
  exact (range_nontrivial_FqtInfty Fq).not_subsingleton

/-- The integer ring of FqtInfty is a discrete valuation ring.

This follows from being a PID that is not a field (uniformizer 1/X has valuation < 1).
-/
instance isDiscreteValuationRing_integer_FqtInfty :
    IsDiscreteValuationRing (Valued.integer (FqtInfty Fq)) where
  not_a_field' := by
    simp only [ne_eq, Ideal.ext_iff, Valuation.mem_maximalIdeal_iff, Ideal.mem_bot, Subtype.ext_iff,
      ZeroMemClass.coe_zero, Subtype.forall, Valuation.mem_valuationSubring_iff, not_forall,
      exists_prop]
    -- Use 1/X as uniformizer: it's in the integers (v(1/X) = exp(-1) ≤ 1) and has v < 1
    use inftyRingHom Fq (1 / RatFunc.X)
    constructor
    · -- 1/X is in the integers: v(1/X) ≤ 1
      rw [valued_FqtInfty_eq_inftyValuationDef, ← FunctionField.inftyValuation_apply,
          FunctionField.inftyValuation.X_inv]
      rw [← WithZero.exp_zero]
      exact (WithZero.exp_le_exp.mpr (by norm_num : (-1 : ℤ) ≤ 0))
    constructor
    · -- v(1/X) < 1
      rw [valued_FqtInfty_eq_inftyValuationDef, ← FunctionField.inftyValuation_apply,
          FunctionField.inftyValuation.X_inv, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0)
    · -- 1/X ≠ 0 in FqtInfty
      intro h0
      have : (inftyRingHom Fq (1 / RatFunc.X) : FqtInfty Fq) ≠ 0 := by
        rw [map_ne_zero]
        exact one_div_ne_zero RatFunc.X_ne_zero
      exact this h0

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
    have heq : integralInfty = (Valued.integer (FqtInfty Fq) : Set (FqtInfty Fq)) := by
      ext x
      simp only [Valuation.mem_valuationSubring_iff]
      rfl
    rw [heq]
    exact isCompact_of_compactSpace_subtype

  -- Combine using IsCompact.prod
  rw [hprod]
  exact hCompactFin.prod hCompactInfty

/-! ### Helper lemmas for weak approximation -/

/-- The set {x : Valued.v x ≤ 1} is a neighborhood of any point in it.

For valued fields with discrete value group, the closed ball is also open (clopen).
-/
theorem isOpen_ball_le_one_FqtInfty :
    IsOpen {x : FqtInfty Fq | Valued.v x ≤ 1} := by
  -- For discrete valuations, {v ≤ 1} = {v < exp(1)} which is open
  -- Since value group is ℤ, there's nothing between 1 = exp(0) and exp(1)
  convert (Valued.isClopen_ball (R := FqtInfty Fq) (WithZero.exp (1 : ℤ))).isOpen using 1
  ext x
  simp only [Set.mem_setOf_eq, Valued.mem_ball_zero_iff]
  constructor
  · intro hle
    calc Valued.v x ≤ 1 := hle
      _ = WithZero.exp (0 : ℤ) := by rw [WithZero.exp_zero]
      _ < WithZero.exp (1 : ℤ) := WithZero.exp_lt_exp.mpr (by norm_num)
  · intro hlt
    -- v < exp(1) means v ≤ exp(0) = 1 since value group is ℤ
    by_cases hx : x = 0
    · simp [hx]
    · -- v x ∈ {exp n : n ∈ ℤ} for x ≠ 0
      -- v x < exp 1 means v x ≤ exp 0 = 1
      have hval_pos : (0 : WithZero (Multiplicative ℤ)) < Valued.v x :=
        (Valuation.ne_zero_iff _).mpr hx
      -- The key: valuation range is discrete (values in exp(ℤ) ∪ {0})
      -- For x ≠ 0, v x = exp(n) for some n ∈ ℤ
      -- If v x < exp(1) and v x > 0, then n < 1, so n ≤ 0, so v x ≤ 1
      rw [← WithZero.exp_zero]
      -- Use the fact that in WithZero (Multiplicative ℤ), the only values between
      -- 0 and exp(1) are {0} ∪ {exp(n) : n ≤ 0}
      -- Since v x > 0 and v x < exp(1), and v x takes values in exp(ℤ),
      -- we must have v x = exp(n) for some n < 1, hence n ≤ 0
      -- Strategy: use that WithZero (Multiplicative ℤ) is well-ordered in a sense
      -- Below exp(1), the maximum non-zero value is exp(0) = 1
      -- For x ≠ 0, Valued.v x ∈ range(Valued.v) ⊆ image of exp on ℤ
      -- The only values < exp(1) and > 0 are exp(n) for n ≤ 0
      -- All these are ≤ exp(0) = 1
      by_contra hgt
      push_neg at hgt
      -- hgt : 1 < v x, hlt : v x < exp(1), hval_pos : 0 < v x
      -- This is a contradiction in the ordered structure of WithZero (Multiplicative ℤ)
      -- 1 = exp(0) < v x < exp(1) implies 0 < n < 1 for v x = exp(n), impossible for n ∈ ℤ
      -- Use WithZero.coe_lt_coe to convert to Multiplicative ℤ comparisons
      have h1 : (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 := (WithZero.exp_zero).symm
      have h2 : WithZero.exp (1 : ℤ) = ((Multiplicative.ofAdd 1 : Multiplicative ℤ) : WithZero _) := rfl
      have h3 : (1 : WithZero (Multiplicative ℤ)) = ((1 : Multiplicative ℤ) : WithZero _) := rfl
      rw [h1] at hgt
      -- Now hgt : exp(0) < v x and hlt : v x < exp(1)
      -- v x must be in the image of (coe : Multiplicative ℤ → WithZero _) since v x ≠ 0
      obtain ⟨m, hm⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = Valued.v x := by
        have : Valued.v x ≠ 0 := ne_of_gt hval_pos
        exact WithZero.ne_zero_iff_exists.mp this
      rw [← hm] at hgt hlt
      -- Now hgt : exp(0) < m and hlt : m < exp(1) in WithZero (Multiplicative ℤ)
      rw [WithZero.coe_lt_coe] at hgt hlt
      -- hgt : Multiplicative.ofAdd 0 < m, hlt : m < Multiplicative.ofAdd 1
      simp only [Multiplicative.ofAdd_lt] at hgt hlt
      -- hgt : 0 < toAdd m, hlt : toAdd m < 1, with toAdd m : ℤ
      omega

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
  rw [mem_adicCompletionIntegers]
  simp only [adicCompletion, Valued.valuedCompletion_apply]
  exact v.valuation_of_algebraMap_le p

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
  have hdense : DenseRange (algebraMap (RatFunc Fq) (v.adicCompletion (RatFunc Fq))) :=
    UniformSpace.Completion.denseRange_coe
  have hopen : IsOpen {x : v.adicCompletion (RatFunc Fq) | (a_v - x) ∈ v.adicCompletionIntegers (RatFunc Fq)} := by
    -- {x : a_v - x ∈ O_v} = a_v - O_v, open since O_v is open
    convert (Valued.isOpen_valuationSubring (v.adicCompletion (RatFunc Fq))).preimage
      (continuous_const.sub continuous_id) using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, sub_sub_cancel]
    constructor <;> intro h <;> exact h
  have hne : (a_v - (v.adicCompletionIntegers (RatFunc Fq) : Set _)).Nonempty := by
    use a_v
    simp only [Set.mem_sub, SetLike.mem_coe]
    exact ⟨0, Subring.zero_mem _, sub_zero a_v⟩
  obtain ⟨y, hy⟩ := hdense.exists_mem_open hopen hne
  exact ⟨y, hy⟩

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
  have hfin : (UniqueFactorizationMonoid.normalizedFactors D).toFinset.Finite :=
    Multiset.toFinset.finite _
  -- We need to relate {v | v.intValuation D < 1} to the normalized factors
  -- v.intValuation D < 1 iff the generator of v divides D
  -- For a PID like Fq[X], height-one primes are principal, generated by irreducibles
  -- This is finite because there are finitely many prime factors
  apply Set.Finite.subset (s := {v | ∃ p ∈ (normalizedFactors D).toFinset,
      v.asIdeal = Ideal.span {p}})
  · -- The set of HeightOneSpectrum corresponding to normalized factors is finite
    apply Set.Finite.of_finite_image (f := fun v => v.asIdeal)
    · apply Set.Finite.subset (s := Ideal.span '' (normalizedFactors D).toFinset)
      · exact Set.Finite.image _ hfin.finite
      · intro I hI
        obtain ⟨v, ⟨p, hp_mem, hv_eq⟩, rfl⟩ := hI
        exact ⟨p, hp_mem, hv_eq⟩
    · intro v₁ v₂ hv₁ hv₂ heq
      obtain ⟨p₁, _, hp₁⟩ := hv₁
      obtain ⟨p₂, _, hp₂⟩ := hv₂
      ext
      rw [hp₁, hp₂, heq]
  · -- Containment: if v.intValuation D < 1, then v corresponds to a factor of D
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    -- v.intValuation D < 1 means D ∈ v.asIdeal
    have hD_mem_v : D ∈ v.asIdeal := (v.intValuation_lt_one_iff_mem D).mp hv
    -- In a PID, v.asIdeal is principal
    haveI : v.asIdeal.IsPrincipal := IsPrincipalIdealRing.principal v.asIdeal
    let g := Submodule.IsPrincipal.generator v.asIdeal
    -- g is irreducible (prime generator of prime ideal)
    have hg_irr : Irreducible g := by
      have hprime := Submodule.IsPrincipal.prime_generator_of_isPrime v.asIdeal v.ne_bot
      exact hprime.irreducible
    -- g | D (since D ∈ v.asIdeal = (g))
    have hg_dvd_D : g ∣ D := (Submodule.IsPrincipal.mem_iff_generator_dvd v.asIdeal).mp hD_mem_v
    -- By UFD, there exists q ∈ normalizedFactors D with g ~ᵤ q
    obtain ⟨q, hq_mem, hq_assoc⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
      hD hg_irr hg_dvd_D
    -- v.asIdeal = span {g} = span {q} (since g ~ᵤ q)
    use q
    constructor
    · exact Multiset.mem_toFinset.mpr hq_mem
    · rw [← Ideal.span_singleton_generator v.asIdeal]
      exact Ideal.span_singleton_eq_span_singleton.mpr hq_assoc

/-- The intValuation of D is at least exp(-natDegree D).
This bounds the multiplicity of any prime in D by the degree of D.
Proof: g is irreducible so deg(g) ≥ 1, and g^n | D implies n·deg(g) ≤ deg(D). -/
lemma intValuation_ge_exp_neg_natDegree (v : HeightOneSpectrum Fq[X]) (D : Fq[X]) (hD : D ≠ 0) :
    v.intValuation D ≥ WithZero.exp (-(D.natDegree : ℤ)) := by
  by_cases hD_mem : D ∈ v.asIdeal
  · -- D ∈ v.asIdeal: bound the multiplicity
    haveI : v.asIdeal.IsPrincipal := IsPrincipalIdealRing.principal v.asIdeal
    let g := Submodule.IsPrincipal.generator v.asIdeal
    have hg_irr : Irreducible g := (Submodule.IsPrincipal.prime_generator_of_isPrime v.asIdeal v.ne_bot).irreducible
    have hg_deg : 1 ≤ g.natDegree := Polynomial.Irreducible.natDegree_pos hg_irr
    let n := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {D})).factors
    have hval : v.intValuation D = WithZero.exp (-(n : ℤ)) := v.intValuation_if_neg hD
    rw [hval]
    apply WithZero.exp_le_exp.mpr
    simp only [neg_le_neg_iff, Int.ofNat_le]
    by_cases hn : n = 0
    · simp [hn]
    · -- g^n | D, so n * deg(g) = deg(g^n) ≤ deg(D), hence n ≤ deg(D)
      have hgn_dvd : g ^ n ∣ D := by
        have hmem : D ∈ v.asIdeal ^ n := by rw [v.intValuation_le_pow_iff_mem, hval]
        have hpow_eq : v.asIdeal ^ n = Ideal.span {g ^ n} := by
          rw [← Ideal.span_singleton_generator v.asIdeal, Ideal.span_singleton_pow]
        rw [hpow_eq] at hmem
        exact Ideal.mem_span_singleton.mp hmem
      have hdeg : (g ^ n).natDegree ≤ D.natDegree := Polynomial.natDegree_le_of_dvd hgn_dvd hD
      calc n ≤ n * g.natDegree := Nat.le_mul_of_pos_right n hg_deg
        _ = (g ^ n).natDegree := (Polynomial.natDegree_pow g n).symm
        _ ≤ D.natDegree := hdeg
  · -- D ∉ v.asIdeal: valuation is 1
    have hval : v.intValuation D = 1 := by
      by_contra h
      exact hD_mem ((v.intValuation_lt_one_iff_mem D).mp (lt_of_le_of_ne (v.intValuation_le_one D) h))
    rw [hval]
    exact le_of_lt (WithZero.exp_lt_one_iff.mpr (by linarith [D.natDegree.cast_nonneg] : -(D.natDegree : ℤ) < 0))

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
  -- Step 1: The bad set S is finite
  have hfin : {v : HeightOneSpectrum Fq[X] | a.val v ∉ v.adicCompletionIntegers (RatFunc Fq)}.Finite := by
    rw [← Set.compl_setOf]
    exact Filter.eventually_cofinite.mp a.2
  -- Base case: if already integral everywhere, k = 0 works
  by_cases hbase : ∀ v, a.val v ∈ v.adicCompletionIntegers (RatFunc Fq)
  · exact ⟨0, fun v => by rw [sub_zero]; exact hbase v⟩
  push_neg at hbase

  -- Let S be the bad set as a Finset
  let S := hfin.toFinset

  -- Step 2: For each v ∈ S, get y_v ∈ K with a_v - y_v ∈ O_v
  have happrox : ∀ v ∈ S, ∃ y : RatFunc Fq, (a.val v - y) ∈ v.adicCompletionIntegers (RatFunc Fq) :=
    fun v _ => exists_local_approximant Fq v (a.val v)
  choose! y hy using happrox

  -- Step 3: Let D = product of all denominators of y_v for v ∈ S
  let D := S.prod (fun v => (y v).denom)
  have hD_ne : D ≠ 0 := Finset.prod_ne_zero (fun v _ => RatFunc.denom_ne_zero (y v))

  -- D · y_v ∈ R for all v ∈ S (D clears the denominator of y_v)
  have hDy_in_R : ∀ v ∈ S, ∃ P : Fq[X], algebraMap Fq[X] (RatFunc Fq) P = D • y v := by
    intro v hv
    -- y v = num / denom, and denom divides D (since D is product including denom)
    have hdiv : (y v).denom ∣ D := Finset.dvd_prod_of_mem (fun w => (y w).denom) hv
    obtain ⟨c, hc⟩ := hdiv
    -- D · y_v = D · (num/denom) = (D/denom) · num = c · num
    use c * (y v).num
    rw [Algebra.smul_def, RingHom.map_mul]
    simp only [RatFunc.algebraMap_apply]
    rw [← RatFunc.num_div_denom (y v)]
    field_simp
    ring_nf
    rw [← hc]
    ring
  choose Py hPy using hDy_in_R

  -- Step 4: Set of primes dividing D (the "enlarged set T")
  -- T = S ∪ {v : v divides D} - finite by HeightOneSpectrum.finite_divisors
  let T := S ∪ (HeightOneSpectrum.finite_divisors Fq D hD_ne).toFinset

  -- Step 5: Apply CRT to get P ∈ Fq[X] such that k = P/D works at all places
  -- Use natDegree D as a uniform exponent bound (simpler than computing exact valuations)
  let e : HeightOneSpectrum Fq[X] → ℕ := fun _ => D.natDegree + 1

  -- CRT targets: Py v for v ∈ S, 0 for v ∈ T \ S
  let target : T → Fq[X] := fun ⟨v, hv⟩ =>
    if hvS : v ∈ S then Py v hvS else 0

  -- Prime ideals
  have hprime : ∀ v ∈ T, (v.asIdeal).Prime := fun v _ => v.isPrime

  -- Distinct primes have distinct ideals
  have hcoprime : ∀ v₁ ∈ T, ∀ v₂ ∈ T, v₁ ≠ v₂ → v₁.asIdeal ≠ v₂.asIdeal := by
    intro v₁ _ v₂ _ hne h
    apply hne
    ext : 1
    exact h

  -- Apply CRT
  obtain ⟨P, hP⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (fun v : HeightOneSpectrum Fq[X] => v.asIdeal) e hprime hcoprime target

  -- Define k = P / D
  let k : RatFunc Fq := algebraMap Fq[X] (RatFunc Fq) P / algebraMap Fq[X] (RatFunc Fq) D

  use k
  intro v

  -- Case split on whether v ∈ T
  by_cases hvT : v ∈ T
  · -- v ∈ T: use CRT result
    have hPv := hP v hvT
    by_cases hvS : v ∈ S
    · -- v ∈ S: need a_v - k ∈ O_v
      -- We have: a_v - y_v ∈ O_v (from hy)
      -- We have: P - Py_v ∈ v.asIdeal^(natDegree D + 1) (from CRT)
      -- Need to show: k - y_v ∈ O_v, then a_v - k = (a_v - y_v) - (k - y_v) ∈ O_v
      have hay := hy v hvS
      -- k - y_v = (P - D·y_v)/D = (P - Py_v)/D
      have hPy_eq : algebraMap Fq[X] (RatFunc Fq) (Py v hvS) = D • y v := hPy v hvS
      -- The CRT gives us P - Py_v ∈ v^{e(v)} where e(v) = natDegree D + 1
      have hPv_crt : P - (if hvS' : v ∈ S then Py v hvS' else 0) ∈ v.asIdeal ^ e v := hPv
      simp only [hvS, ↓reduceDIte] at hPv_crt
      -- P - Py_v ∈ v^{e(v)} means val_v(P - Py_v) ≤ exp(-(natDegree D + 1))
      have hPPy_val : v.intValuation (P - Py v hvS) ≤ WithZero.exp (-(D.natDegree + 1 : ℤ)) := by
        rw [intValuation_le_pow_iff_mem]
        exact hPv_crt
      -- Use the key bound: v.intValuation D ≥ exp(-natDegree D)
      have hD_val_bound : v.intValuation D ≥ WithZero.exp (-(D.natDegree : ℤ)) :=
        intValuation_ge_exp_neg_natDegree Fq v D hD_ne
      -- Show k - y_v is integral at v
      -- k - y_v = P/D - y_v = (P - D·y_v)/D = (P - Py_v)/D (since Py_v = D·y_v)
      have hk_sub_y : k - y v = (algebraMap Fq[X] (RatFunc Fq) (P - Py v hvS)) /
          algebraMap Fq[X] (RatFunc Fq) D := by
        simp only [k]
        rw [div_sub_eq_iff]
        · rw [sub_mul, div_mul_cancel₀]
          · rw [RingHom.map_sub, hPy_eq, Algebra.smul_def]
            ring
          · exact RatFunc.algebraMap_ne_zero hD_ne
        · exact RatFunc.algebraMap_ne_zero hD_ne
      have hk_sub_y_val : v.valuation (k - y v) ≤ 1 := by
        rw [hk_sub_y, map_div₀]
        have hPPy_val' : v.valuation (algebraMap Fq[X] (RatFunc Fq) (P - Py v hvS)) ≤
            WithZero.exp (-(D.natDegree + 1 : ℤ)) := by
          rw [v.valuation_of_algebraMap]
          exact hPPy_val
        have hD_val' : v.valuation (algebraMap Fq[X] (RatFunc Fq) D) ≥
            WithZero.exp (-(D.natDegree : ℤ)) := by
          rw [v.valuation_of_algebraMap]
          exact hD_val_bound
        have hD_ne' : v.valuation (algebraMap Fq[X] (RatFunc Fq) D) ≠ 0 := by
          rw [v.valuation_of_algebraMap]
          exact v.intValuation_ne_zero hD_ne
        calc v.valuation (algebraMap Fq[X] (RatFunc Fq) (P - Py v hvS)) /
               v.valuation (algebraMap Fq[X] (RatFunc Fq) D)
            ≤ WithZero.exp (-(D.natDegree + 1 : ℤ)) / v.valuation (algebraMap Fq[X] (RatFunc Fq) D) := by
              apply div_le_div_of_nonneg_right hPPy_val' (zero_lt_iff.mpr hD_ne')
          _ ≤ WithZero.exp (-(D.natDegree + 1 : ℤ)) / WithZero.exp (-(D.natDegree : ℤ)) := by
              apply div_le_div_of_nonneg_left _ (WithZero.exp_ne_zero _) hD_val'
              exact le_of_lt (WithZero.exp_lt_one_iff.mpr (by linarith : -(D.natDegree + 1 : ℤ) < 0))
          _ = WithZero.exp (-1) := by
              rw [← WithZero.exp_sub]
              congr 1
              ring
          _ ≤ 1 := le_of_lt (WithZero.exp_lt_one_iff.mpr (by norm_num : (-1 : ℤ) < 0))
      -- Now use ultrametric: a_v - k = (a_v - y_v) - (k - y_v) ∈ O_v
      rw [mem_adicCompletionIntegers]
      have hay' : Valued.v (a.val v - y v : v.adicCompletion (RatFunc Fq)) ≤ 1 := by
        rw [← mem_adicCompletionIntegers]
        exact hay
      have hky' : Valued.v ((k - y v) : v.adicCompletion (RatFunc Fq)) ≤ 1 := by
        rw [valuedAdicCompletion_eq_valuation]
        exact hk_sub_y_val
      -- a_v - k = (a_v - y_v) - (k - y_v)
      have hsub_eq : (a.val v : v.adicCompletion (RatFunc Fq)) - k =
          (a.val v - y v) - (k - y v) := by ring
      rw [hsub_eq]
      exact Valuation.map_sub_le hay' hky'
    · -- v ∈ T \ S: need a_v - k ∈ O_v
      -- We have: a_v ∈ O_v (since v ∉ S)
      -- We have: P ≡ 0 (mod v^{e(v)}) from CRT (target is 0)
      -- Need: k = P/D ∈ O_v
      have ha_int : a.val v ∈ v.adicCompletionIntegers (RatFunc Fq) := by
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hvS
        exact hvS
      -- From CRT: P - target = P - 0 = P ∈ v^{e(v)}
      have hPv_crt : P - (if hvS' : v ∈ S then Py v hvS' else 0) ∈ v.asIdeal ^ e v := hPv
      simp only [hvS, ↓reduceDIte, sub_zero] at hPv_crt
      -- P ∈ v^{e(v)} means val_v(P) ≥ e(v) = D.natDegree + 1
      have hP_val : v.intValuation P ≤ WithZero.exp (-(D.natDegree + 1 : ℤ)) := by
        rw [intValuation_le_pow_iff_mem]
        exact hPv_crt
      -- Use the key bound: v.intValuation D ≥ exp(-natDegree D)
      have hD_val_bound : v.intValuation D ≥ WithZero.exp (-(D.natDegree : ℤ)) :=
        intValuation_ge_exp_neg_natDegree Fq v D hD_ne
      -- Show k = P/D is integral at v
      have hk_val : v.valuation k ≤ 1 := by
        simp only [k]
        rw [map_div₀]
        -- val(P/D) = val(P) / val(D)
        -- val(P) ≤ exp(-(D.natDegree + 1)) and val(D) ≥ exp(-D.natDegree)
        -- So val(P)/val(D) ≤ exp(-(D.natDegree + 1)) / exp(-D.natDegree) = exp(-1) ≤ 1
        have hP_val' : v.valuation (algebraMap Fq[X] (RatFunc Fq) P) ≤
            WithZero.exp (-(D.natDegree + 1 : ℤ)) := by
          rw [v.valuation_of_algebraMap]
          exact hP_val
        have hD_val' : v.valuation (algebraMap Fq[X] (RatFunc Fq) D) ≥
            WithZero.exp (-(D.natDegree : ℤ)) := by
          rw [v.valuation_of_algebraMap]
          exact hD_val_bound
        have hD_ne' : v.valuation (algebraMap Fq[X] (RatFunc Fq) D) ≠ 0 := by
          rw [v.valuation_of_algebraMap]
          exact v.intValuation_ne_zero hD_ne
        -- Dividing: val(P)/val(D) ≤ exp(-(D.natDegree + 1)) / exp(-D.natDegree) = exp(-1)
        calc v.valuation (algebraMap Fq[X] (RatFunc Fq) P) /
               v.valuation (algebraMap Fq[X] (RatFunc Fq) D)
            ≤ WithZero.exp (-(D.natDegree + 1 : ℤ)) / v.valuation (algebraMap Fq[X] (RatFunc Fq) D) := by
              apply div_le_div_of_nonneg_right hP_val' (zero_lt_iff.mpr hD_ne')
          _ ≤ WithZero.exp (-(D.natDegree + 1 : ℤ)) / WithZero.exp (-(D.natDegree : ℤ)) := by
              apply div_le_div_of_nonneg_left _ (WithZero.exp_ne_zero _) hD_val'
              exact le_of_lt (WithZero.exp_lt_one_iff.mpr (by linarith : -(D.natDegree + 1 : ℤ) < 0))
          _ = WithZero.exp (-1) := by
              rw [← WithZero.exp_sub]
              congr 1
              ring
          _ ≤ 1 := le_of_lt (WithZero.exp_lt_one_iff.mpr (by norm_num : (-1 : ℤ) < 0))
      -- Now use ultrametric inequality
      rw [mem_adicCompletionIntegers]
      have hk_coe : Valued.v (k : v.adicCompletion (RatFunc Fq)) ≤ 1 := by
        rw [valuedAdicCompletion_eq_valuation]
        exact hk_val
      have ha_coe : Valued.v (a.val v) ≤ 1 := by
        rw [← mem_adicCompletionIntegers]
        exact ha_int
      exact Valuation.map_sub_le ha_coe hk_coe
  · -- v ∉ T: val_v(D) = 0, so val_v(k) = val_v(P) ≥ 0 (P is a polynomial)
    -- Also a_v ∈ O_v since v ∉ S ⊆ T
    have hvS : v ∉ S := fun h => hvT (Finset.mem_union_left _ h)
    have ha_int : a.val v ∈ v.adicCompletionIntegers (RatFunc Fq) := by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hvS
      exact hvS
    -- val_v(D) = 0 since v ∉ T ⊇ {divisors of D}
    have hvD : v.intValuation D = 1 := by
      by_contra h
      have hlt : v.intValuation D < 1 := lt_of_le_of_ne (v.intValuation_le_one D) h
      have hmem : v ∈ (HeightOneSpectrum.finite_divisors Fq D hD_ne).toFinset := by
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        exact hlt
      exact hvT (Finset.mem_union_right S hmem)
    -- Since P is a polynomial, val_v(P) ≥ 0, i.e., v.intValuation P ≤ 1
    have hP_int : v.intValuation P ≤ 1 := v.intValuation_le_one P
    -- k = P/D with val_v(D) = 1, so val_v(k) = val_v(P) ≥ 0
    -- First show k is integral at v (as element of K)
    have hk_val : v.valuation k ≤ 1 := by
      simp only [k]
      rw [map_div₀]
      -- val(P/D) = val(P) / val(D) = val(P) (since val(D) = 1)
      have hD_val : v.valuation (algebraMap Fq[X] (RatFunc Fq) D) = 1 := by
        rw [v.valuation_of_algebraMap]
        exact hvD
      rw [hD_val, div_one]
      -- val(P) ≤ 1 follows from P being a polynomial
      rw [v.valuation_of_algebraMap]
      exact hP_int
    -- Now show a.val v - k ∈ O_v using ultrametric inequality
    rw [mem_adicCompletionIntegers]
    -- Valued.v on completion extends v.valuation on K
    have hk_coe : Valued.v (k : v.adicCompletion (RatFunc Fq)) ≤ 1 := by
      rw [valuedAdicCompletion_eq_valuation]
      exact hk_val
    have ha_coe : Valued.v (a.val v) ≤ 1 := by
      rw [← mem_adicCompletionIntegers]
      exact ha_int
    exact Valuation.map_sub_le ha_coe hk_coe

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
  -- First get k₀ from exists_finite_integral_translate
  obtain ⟨k₀, hk₀⟩ := exists_finite_integral_translate Fq a
  -- The key insight: we can adjust k₀ by any polynomial without breaking finite integrality
  -- because polynomials are integral at all finite places.
  --
  -- Strategy: Write k₀ = q + r/denom where q is the polynomial part and r/denom has |·|_∞ < 1.
  -- Then k = k₀ - q = r/denom has |k|_∞ < 1 ≤ bound (for bound ≥ 1).
  -- For bound < 1, we need a different approach.
  --
  -- For bound ≥ 1: subtract the polynomial part of k₀ to get |k|_∞ < 1 ≤ bound.
  -- For bound < 1: this requires more careful construction, left as sorry.
  by_cases hbound : bound ≥ 1
  · -- Case: bound ≥ 1. We can achieve |k|_∞ ≤ 1 ≤ bound.
    -- Write k₀ = num/denom, and let q = num /% denom (quotient), r = num % denom.
    -- Then k₀ = q + r/denom, and k = r/denom has deg(r) < deg(denom), so |k|_∞ < 1.
    let num := k₀.num
    let denom := k₀.denom
    have hdenom_ne : denom ≠ 0 := RatFunc.denom_ne_zero k₀
    let q := num /ₘ denom  -- Quotient in polynomial division
    let r := num %ₘ denom  -- Remainder
    -- k₀ = num/denom = (q * denom + r)/denom = q + r/denom
    have hk₀_eq : k₀ = algebraMap Fq[X] (RatFunc Fq) q +
        algebraMap Fq[X] (RatFunc Fq) r / algebraMap Fq[X] (RatFunc Fq) denom := by
      have hdiv : num = q * denom + r := (Polynomial.div_add_mod num denom).symm
      rw [← RatFunc.num_div_denom k₀]
      rw [hdiv]
      simp only [RingHom.map_add, RingHom.map_mul]
      rw [add_div, mul_div_assoc]
      congr 1
      rw [div_self]
      exact RatFunc.algebraMap_ne_zero hdenom_ne
    -- Let k = r/denom = k₀ - q
    let k := algebraMap Fq[X] (RatFunc Fq) r / algebraMap Fq[X] (RatFunc Fq) denom
    have hk_eq : k = k₀ - algebraMap Fq[X] (RatFunc Fq) q := by
      simp only [k, hk₀_eq]
      ring
    use k
    constructor
    · -- Finite integrality: (a.val v - k) = (a.val v - k₀) + q ∈ O_v
      intro v
      have hk₀v := hk₀ v
      -- a.val v - k = a.val v - (k₀ - q) = (a.val v - k₀) + q
      have hsub_eq : (a.val v : v.adicCompletion (RatFunc Fq)) - k = (a.val v - k₀) + q := by
        rw [hk_eq]
        ring
      rw [mem_adicCompletionIntegers] at hk₀v ⊢
      rw [hsub_eq]
      -- q is a polynomial, hence integral at all finite places
      have hq_int : Valued.v (algebraMap Fq[X] (RatFunc Fq) q : v.adicCompletion (RatFunc Fq)) ≤ 1 := by
        rw [valuedAdicCompletion_eq_valuation, v.valuation_of_algebraMap]
        exact v.intValuation_le_one q
      exact Valuation.map_add_le hk₀v hq_int
    · -- Infinity bound: |k|_∞ ≤ bound
      -- |k|_∞ = |r/denom|_∞ = exp(deg(r) - deg(denom))
      -- Since deg(r) < deg(denom) (remainder is smaller), this is < 1 ≤ bound.
      have hr_deg : r.natDegree < denom.natDegree ∨ r = 0 := by
        by_cases hr0 : r = 0
        · right; exact hr0
        · left
          exact Polynomial.natDegree_mod_lt num hdenom_ne
      trans (1 : WithZero (Multiplicative ℤ))
      · -- |k|_∞ < 1
        simp only [k]
        rw [valued_FqtInfty_eq_inftyValuationDef, ← FunctionField.inftyValuation_apply,
            RingHom.map_div₀]
        by_cases hr0 : r = 0
        · simp [hr0]
        · -- r ≠ 0, so |r|_∞ / |denom|_∞ = exp(deg(r) - deg(denom)) < 1
          have hdeg_lt : r.natDegree < denom.natDegree := hr_deg.resolve_right hr0
          rw [FunctionField.inftyValuation_apply, FunctionField.inftyValuation_apply,
              FunctionField.inftyValuationDef_eq Fq (algebraMap Fq[X] (RatFunc Fq) r),
              FunctionField.inftyValuationDef_eq Fq (algebraMap Fq[X] (RatFunc Fq) denom)]
          · simp only [RatFunc.intDegree_polynomial]
            rw [div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]
            apply WithZero.exp_lt_one_iff.mpr
            simp only [neg_neg]
            omega
          · exact RatFunc.algebraMap_ne_zero hdenom_ne
          · exact RatFunc.algebraMap_ne_zero hr0
      · exact hbound
  · -- Case: bound < 1. This requires a more refined construction.
    -- For now, we use k₀ directly and note that the bound may not be achievable for all bounds.
    -- The main theorem `exists_translate_in_integralFullAdeles` only needs bound = 1.
    push_neg at hbound
    -- For bound < 1, we'd need to further reduce the numerator modulo higher powers.
    -- This is possible but complex; the key use case (bound = 1) is covered above.
    use k₀
    exact ⟨hk₀, by
      -- This case is not needed for the main application
      -- For bound < 1 = exp(0), we'd need |k₀|_∞ < bound < 1
      -- which requires specific construction not done here
      sorry⟩

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
  -- Step 1: Approximate a.2 at infinity
  obtain ⟨P, hP⟩ := exists_approx_in_ball_infty Fq a.2
  -- Step 2: Work with the modified adele
  let b : FqFullAdeleRing Fq := a - fqFullDiagonalEmbedding Fq P
  -- Step 3: Find z clearing finite places with bounded infinity valuation
  -- Need: for all v, (b.1 v - z) ∈ O_v and |z|_∞ ≤ 1
  obtain ⟨z, hz_fin, hz_inf⟩ := exists_finite_integral_translate_with_infty_bound Fq b.1 1
  -- Step 4: Combine
  use P + z
  constructor
  · -- Finite places
    intro v
    -- (a - diag(P + z)).1 v = (a - diag(P)).1 v - z = b.1 v - z
    have heq : ((a - fqFullDiagonalEmbedding Fq (P + z)).1).val v = (b.1.val v - z) := by
      simp only [b, Prod.fst_sub, fqFullDiagonalEmbedding_fst, map_add]
      rfl
    rw [heq]
    exact hz_fin v
  · -- Infinity place
    -- (a - diag(P + z)).2 = a.2 - (P + z) = (a.2 - P) - z = b.2 - z
    have heq : (a - fqFullDiagonalEmbedding Fq (P + z)).2 = b.2 - inftyRingHom Fq z := by
      simp only [b, Prod.snd_sub, fqFullDiagonalEmbedding_snd, map_add]
      ring
    rw [heq]
    -- |b.2 - z|_∞ ≤ max(|b.2|_∞, |z|_∞) ≤ 1 by ultrametric inequality
    -- But we need to be careful: b.2 = a.2 - P, so |b.2|_∞ = |a.2 - P|_∞ ≤ 1
    have hb2 : Valued.v b.2 ≤ 1 := by
      simp only [b, Prod.snd_sub, fqFullDiagonalEmbedding_snd]
      exact hP
    -- Use ultrametric: |b.2 - z| ≤ max(|b.2|, |z|)
    calc Valued.v (b.2 - inftyRingHom Fq z)
        ≤ max (Valued.v b.2) (Valued.v (inftyRingHom Fq z)) := Valued.v.map_sub_le_max' _ _
      _ ≤ max 1 1 := max_le_max hb2 hz_inf
      _ = 1 := max_self 1

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
