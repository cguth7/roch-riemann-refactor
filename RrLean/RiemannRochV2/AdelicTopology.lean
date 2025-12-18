import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import RrLean.RiemannRochV2.AdelicH1v2

/-!
# Topological Properties of Adele Rings

This module establishes topological properties of finite adele rings needed for
the finiteness of H¹(D) in Riemann-Roch theory.

## Main Results

We prove that under suitable hypotheses (finite residue fields), the finite adele ring
`FiniteAdeleRing R K` is locally compact, which is essential for proving that
H¹(D) = A_K / (K + A_K(D)) is finite-dimensional.

## Strategy

For function fields over finite base fields:
1. Each `adicCompletion K v` is locally compact (complete + DVR + finite residue)
2. Each `adicCompletionIntegers K v` is open (Mathlib: `Valued.isOpen_valuationSubring`)
3. Each `adicCompletionIntegers K v` is compact (from finite residue field)
4. The restricted product inherits local compactness via `locallyCompactSpace_of_group`

## Key Mathlib Results Used

- `Valued.isOpen_valuationSubring`: Valuation subrings are open
- `RestrictedProduct.locallyCompactSpace_of_group`: Restricted product local compactness
- `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`:
  Characterization of when valuation integers are compact

## References

- Mathlib's `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- Mathlib's `Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace`
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace RiemannRochV2.AdelicTopology

/-! ## Local Compactness of adic completions

For the restricted product to be locally compact, we need each `adicCompletion K v`
to be locally compact. This requires the valuation integers to be compact.
-/

section LocalCompactness

variable (K) (v : HeightOneSpectrum R)

/-- The valuation integers of an adic completion are open.
This is a direct application of Mathlib's `Valued.isOpen_valuationSubring`. -/
theorem isOpen_adicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

/-- If valuation integers are compact, the completion is locally compact.

This uses the fact that the valuation integers form an open neighborhood of 0,
and `IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup` gives local compactness.
-/
theorem locallyCompactSpace_adicCompletion_of_compact
    [hcompact : CompactSpace (v.adicCompletionIntegers K)] :
    LocallyCompactSpace (v.adicCompletion K) := by
  have hopen : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isOpen_adicCompletionIntegers K v
  have hc : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isCompact_iff_compactSpace.mpr hcompact
  have h0mem : (0 : v.adicCompletion K) ∈ v.adicCompletionIntegers K :=
    (v.adicCompletionIntegers K).zero_mem
  exact hc.locallyCompactSpace_of_mem_nhds_of_addGroup (hopen.mem_nhds h0mem)

end LocalCompactness

/-! ## Local Compactness of FiniteAdeleRing

We establish that the finite adele ring is locally compact under appropriate hypotheses.
-/

section FiniteAdeleRingTopology

variable (R K)

/-- Hypothesis: all adic completion integers are compact.
This is true for function fields over finite base fields. -/
class AllIntegersCompact : Prop where
  compact : ∀ v : HeightOneSpectrum R, CompactSpace (v.adicCompletionIntegers K)

/-- Each adicCompletion is locally compact when integers are compact. -/
instance locallyCompactSpace_adicCompletion [AllIntegersCompact R K]
    (v : HeightOneSpectrum R) :
    LocallyCompactSpace (v.adicCompletion K) := by
  haveI : CompactSpace (v.adicCompletionIntegers K) := AllIntegersCompact.compact v
  exact locallyCompactSpace_adicCompletion_of_compact K v

/-- The finite adele ring is locally compact when all integers are compact.

This follows from the restricted product theorem:
- Each `adicCompletion K v` is locally compact
- Each `adicCompletionIntegers K v` is open (Mathlib: `Valued.isOpen_valuationSubring`)
- All `adicCompletionIntegers K v` are compact

The instance `RestrictedProduct.instLocallyCompactSpace` applies automatically when:
- All R_i are groups with open subgroups B_i
- All B_i are compact
-/
instance locallyCompactSpace_finiteAdeleRing [AllIntegersCompact R K] :
    LocallyCompactSpace (FiniteAdeleRing R K) := by
  -- FiniteAdeleRing R K = Πʳ v, [v.adicCompletion K, v.adicCompletionIntegers K]
  -- We need to establish the Fact for openness
  haveI hopen : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun v => Valued.isOpen_valuationSubring _⟩
  -- Each adicCompletionIntegers is compact (from our hypothesis)
  haveI : ∀ v : HeightOneSpectrum R, CompactSpace (v.adicCompletionIntegers K) :=
    fun v => AllIntegersCompact.compact v
  -- FiniteAdeleRing is definitionally equal to the restricted product
  -- Use inferInstanceAs to explicitly match the type
  exact inferInstanceAs (LocallyCompactSpace
    (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]))

end FiniteAdeleRingTopology

/-! ## Discreteness of K in Adeles

For H¹(D) to be finite-dimensional, we need K to embed discretely into the adeles.

**Mathematical Background**:

For a function field K over finite field k:
1. K embeds diagonally into the finite adele ring A_K
2. K ∩ (∏_v O_v) = R (the ring of integers)
3. K is discrete in A_K (strong approximation)
4. A_K / K has finite covolume (adelic Minkowski)

We axiomatize these deep properties, following the Track A approach.
-/

section DiscreteEmbedding

variable (R K)

/-- The diagonal embedding of K into FiniteAdeleRing.
This is just Mathlib's `FiniteAdeleRing.algebraMap`. -/
def diagonalEmbedding : K →+* FiniteAdeleRing R K :=
  FiniteAdeleRing.algebraMap R K

/-- The diagonal embedding is injective because K embeds into each completion.

This requires at least one height-one prime (otherwise the adele ring is trivial).
For Dedekind domains that are not fields, this is always satisfied. -/
theorem diagonalEmbedding_injective [Nonempty (HeightOneSpectrum R)] :
    Function.Injective (diagonalEmbedding R K) := by
  intro x y hxy
  -- Two elements of K are equal if their images in FiniteAdeleRing are equal
  -- Extract that x = y at each component
  have heq : ∀ v : HeightOneSpectrum R, (x : v.adicCompletion K) = (y : v.adicCompletion K) := by
    intro v
    have h := congrFun (Subtype.ext_iff.mp hxy) v
    exact h
  -- Pick any height-one prime
  obtain ⟨v⟩ : Nonempty (HeightOneSpectrum R) := inferInstance
  -- The coercion K → adicCompletion K v is injective
  -- adicCompletion K v = Completion (WithVal (v.valuation K))
  -- The coercion factors through WithVal, which has T0Space
  have hinj : Function.Injective (fun k : K => (k : v.adicCompletion K)) := by
    intro a b hab
    -- The coercion factors as: K ≃ WithVal (v.valuation K) → Completion (WithVal ...)
    -- Step 1: view a and b as elements of WithVal
    let a' : WithVal (v.valuation K) := a
    let b' : WithVal (v.valuation K) := b
    -- Step 2: hab says their images in the completion are equal
    have hcoe : (a' : v.adicCompletion K) = (b' : v.adicCompletion K) := hab
    -- Step 3: Use coe_injective on WithVal (which has T0Space from ValuedRing.separated)
    have hinj' := @UniformSpace.Completion.coe_injective (WithVal (v.valuation K)) _ _
    have hab' : a' = b' := hinj' hcoe
    -- Step 4: a' = b' as WithVal means a = b as K (same underlying type)
    exact hab'
  exact hinj (heq v)

/-! ### Axiomatization of Discrete Cocompact Embedding

The following properties are deep results about function fields.
We axiomatize them to enable the H¹(D) finiteness proof, following the
Track A approach (axiomatize first, discharge for specific curves later).

**Mathematical Statement**: For a function field K / k with ring of integers R:
1. K is discrete in A_K (the diagonal image has discrete topology)
2. K is closed in A_K (the diagonal image is closed)
3. A_K / K has a compact fundamental domain (cocompact embedding)

These follow from:
- Strong approximation theorem
- Product formula for valuations
- Finiteness of class group (for compactness)

**References**:
- Cassels-Fröhlich "Algebraic Number Theory" Ch. II
- Weil "Basic Number Theory" Ch. IV
-/

/-- Hypothesis: The diagonal embedding of K is discrete and cocompact.

This typeclass packages the key topological properties of the diagonal embedding
K → FiniteAdeleRing R K needed for finiteness of H¹(D).

For function fields over finite fields, these are theorems (Track B).
For now, we axiomatize them (Track A). -/
class DiscreteCocompactEmbedding : Prop where
  /-- K is discrete in the adele ring. -/
  discrete : DiscreteTopology (Set.range (diagonalEmbedding R K))
  /-- K is closed in the adele ring. -/
  closed : IsClosed (Set.range (diagonalEmbedding R K))
  /-- There exists a compact fundamental domain for K in A_K.
  This is the adelic Minkowski theorem: the quotient A_K / K is compact
  (or more precisely, has a compact fundamental domain). -/
  compact_fundamental_domain : ∃ (F : Set (FiniteAdeleRing R K)), IsCompact F ∧
      ∀ a, ∃ x : K, a - diagonalEmbedding R K x ∈ F

/-- The image of K under the diagonal embedding is closed. -/
theorem closed_diagonal [DiscreteCocompactEmbedding R K] :
    IsClosed (Set.range (diagonalEmbedding R K)) :=
  DiscreteCocompactEmbedding.closed

/-- The image of K under the diagonal embedding is discrete. -/
theorem discrete_diagonal [DiscreteCocompactEmbedding R K] :
    DiscreteTopology (Set.range (diagonalEmbedding R K)) :=
  DiscreteCocompactEmbedding.discrete

end DiscreteEmbedding

/-! ## Cocompactness and Finiteness

The key result: the quotient A_K / (K + bounded subset) is compact,
which implies finite-dimensionality.
-/

section Cocompactness

variable (R K)

/-- The adelic Minkowski theorem:
The quotient A_K / K is compact (after suitable compactification).

More precisely, there exists a compact fundamental domain for the
action of K on the adele ring.

For our application to H¹(D), we use a relative version:
A_K / (K + A_K(D)) is compact (and finite-dimensional as k-space).

This follows from `DiscreteCocompactEmbedding.compact_fundamental_domain`. -/
theorem compact_adelic_quotient [DiscreteCocompactEmbedding R K] :
    ∃ (F : Set (FiniteAdeleRing R K)), IsCompact F ∧
      ∀ a, ∃ x : K, a - diagonalEmbedding R K x ∈ F :=
  DiscreteCocompactEmbedding.compact_fundamental_domain

end Cocompactness

/-! ## Summary of Axiomatization

This module provides two levels of topological axiomatization:

1. **AllIntegersCompact**: Each `adicCompletionIntegers K v` is compact.
   - True for function fields over finite base fields
   - Implies `LocallyCompactSpace (FiniteAdeleRing R K)`

2. **DiscreteCocompactEmbedding**: K embeds discretely and cocompactly into A_K.
   - Captures the "adelic Minkowski theorem"
   - Implies closed_diagonal, discrete_diagonal, compact_adelic_quotient

**Expected Route to H¹(D) Finiteness** (Track B target):
1. `LocallyCompactSpace (FiniteAdeleRing R K)` - from (1)
2. Discrete + cocompact embedding - from (2)
3. Blichfeldt/Haar measure argument: discrete lattice ∩ compact = finite set
4. Over finite k: finite set spans finite-dimensional k-module

Note: The finiteness of H¹(D) is axiomatized in `AdelicRRData.h1_finite` in
`AdelicH1v2.lean`, which is the primary Track A axiom for this property.

**Track B Goal**: Prove these axioms for specific function fields.
For a function field K = k(C) where k is finite:
- AllIntegersCompact: finite residue field + complete DVR → compact O_v
- DiscreteCocompactEmbedding: product formula + strong approximation
-/

end RiemannRochV2.AdelicTopology
