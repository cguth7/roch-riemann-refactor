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
import RrLean.RiemannRochV2.Adelic.AdelicTopology
import RrLean.RiemannRochV2.P1Instance.FqPolynomialInstance

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

instance instCommRing : CommRing (FullAdeleRing R K K_infty) :=
  Prod.instCommRing

-- Simp lemmas for FullAdeleRing projections
-- These are needed because FullAdeleRing is a def, not an abbrev,
-- so Prod.fst_sub etc. don't apply directly
@[simp] lemma FullAdeleRing.fst_sub (a b : FullAdeleRing R K K_infty) :
    (a - b).1 = a.1 - b.1 := rfl

@[simp] lemma FullAdeleRing.snd_sub (a b : FullAdeleRing R K K_infty) :
    (a - b).2 = a.2 - b.2 := rfl

@[simp] lemma FullAdeleRing.fst_add (a b : FullAdeleRing R K K_infty) :
    (a + b).1 = a.1 + b.1 := rfl

@[simp] lemma FullAdeleRing.snd_add (a b : FullAdeleRing R K K_infty) :
    (a + b).2 = a.2 + b.2 := rfl

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
  exact Int.natCast_nonneg _

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


end FqInstance

end RiemannRochV2.FullAdeles

end
