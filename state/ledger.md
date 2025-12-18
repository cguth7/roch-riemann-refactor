# Ledger Vol. 3.2 (Cycles 118+) - Full Adeles & Riemann-Roch

*For Cycles 1-34, see `state/ledger_archive.md` (Vol. 1)*
*For Cycles 35-79, see `state/ledger_archive.md` (Vol. 2)*
*For Cycles 80-99, see `state/ledger_archive.md` (Vol. 3.1)*
*For Cycles 100-117, see `state/ledger_archive.md` (Vol. 3.2 Part 1 - AllIntegersCompact)*

---

## 🎯 NEXT CLAUDE: Start Here (Post-Cycle 122)

### Critical Context
**Cycle 121 discovered a spec bug**: K is NOT discrete in the *finite* adeles.
**Cycle 122 created `FullAdeles.lean`** with the product definition A = A_f × K_∞.

### Current State
- ✅ `FullAdeles.lean` created with general definitions (SORRY-FREE)
- ✅ `FullAdeleRing R K K_infty := FiniteAdeleRing R K × K_infty`
- ✅ `fullDiagonalEmbedding : K →+* FullAdeleRing R K K_infty`
- ✅ `fullDiagonalEmbedding_injective` proved
- ✅ `FullDiscreteCocompactEmbedding` class defined
- ⏳ Concrete instance for `Polynomial Fq / RatFunc Fq / FqtInfty Fq` needs Mathlib API work

### Concrete Next Steps (Cycle 123+)

**PRIORITY: Complete the concrete instance for `Polynomial Fq / RatFunc Fq / FqtInfty Fq`**

The general framework is done. Now wire up the concrete instance using these Mathlib APIs:

**Step 1**: Add imports and set up embeddings
```lean
import Mathlib.Topology.Algebra.UniformRing  -- For completion ring hom/algebra

-- The ring hom RatFunc Fq →+* FqtInfty Fq
def diag_infty : RatFunc Fq →+* FunctionField.FqtInfty Fq :=
  UniformSpace.Completion.coeRingHom

-- For diagonal embedding into full adeles:
def fullDiag : RatFunc Fq →+* FqFullAdeleRing Fq :=
  RingHom.prod (FiniteAdeleRing.algebraMap (Polynomial Fq) (RatFunc Fq)) diag_infty
```

**Step 2**: Fix `integralFullAdeles` to use correct valuation API
```lean
-- WRONG: FunctionField.inftyValuation Fq a.2  (inftyValuation is for RatFunc, not FqtInfty)
-- RIGHT: Use Valued.v for completion elements
def integralFullAdeles : Set (FqFullAdeleRing Fq) :=
  {a | (∀ v, a.1.val v ∈ v.adicCompletionIntegers (RatFunc Fq)) ∧
       Valued.v a.2 ≤ 1 }  -- Valued.v extends inftyValuation to completion
```

**Step 3**: Prove discrete/closed/compact for full adeles
- `fq_discrete_in_fullAdeles` - TRUE, uses product formula
- `fq_closed_in_fullAdeles` - follows from discrete + locally compact
- `isCompact_integralFullAdeles` - product of compacts

**Step 4**: Audit usages of `DiscreteCocompactEmbedding`
- `AdelicH1v2.lean` - does it use discreteness?
- Migrate to full adeles where needed

### Key Mathlib APIs for FqtInfty

| What you need | How to get it |
|---------------|---------------|
| Ring hom `RatFunc Fq →+* FqtInfty Fq` | `UniformSpace.Completion.coeRingHom` |
| Algebra instance | Import `Mathlib.Topology.Algebra.UniformRing` |
| Valuation on `FqtInfty` elements | `Valued.v : FqtInfty Fq → ℤᵐ⁰` |
| Valued instance on FqtInfty | `FunctionField.valuedFqtInfty` (automatic) |

### What NOT To Do
- ❌ Don't try to prove `discrete_diagonal_embedding` for finite adeles (it's false)
- ❌ Don't use `inftyValuation` directly on `FqtInfty` elements (use `Valued.v`)
- ❌ Don't defer the concrete instance further - the pieces are ready

---

## ⚡ Quick Reference: Current Axiom/Sorry Status (Cycle 122)

### Sorries (proof holes)
| File | Item | Status | Notes |
|------|------|--------|-------|
| `TraceDualityProof.lean` | `finrank_dual_eq` | ⚪ 1 sorry | NOT on critical path |
| `FqPolynomialInstance.lean` | `discrete_diagonal_embedding` | ❌ FALSE | **CANNOT BE PROVED** - K not discrete in finite adeles |
| `FqPolynomialInstance.lean` | `closed_diagonal_embedding` | ⚪ 1 sorry | Needs different approach (not from discreteness) |
| `FqPolynomialInstance.lean` | `isCompact_integralAdeles` | ⚪ 1 sorry | Product compactness - may still work |
| `FqPolynomialInstance.lean` | `exists_K_translate_in_integralAdeles` | ⚪ 1 sorry | Weak approximation - may still work |
| `FullAdeles.lean` | (none) | ✅ SORRY-FREE | General definitions complete |

### Axiom Classes (still need instantiation for concrete types)
| File | Class | Status | Notes |
|------|-------|--------|-------|
| `AllIntegersCompactProof.lean` | `FiniteCompletionResidueFields` | ✅ INSTANTIATED | For Fq[X] in FqPolynomialInstance.lean |
| `AdelicTopology.lean` | `AllIntegersCompact` | ✅ INSTANTIATED | For Fq[X] in FqPolynomialInstance.lean |
| `AdelicTopology.lean` | `DiscreteCocompactEmbedding` | ✅ INSTANTIATED | For Fq[X] (with sorries) |
| `AdelicH1v2.lean` | `AdelicRRData` | ⏳ CLASS | Full adelic RR axioms |
| `FullRRData.lean` | `FullRRData` | 🔗 CLASS | Derived from `AdelicRRData` |

### Proofs (sorry-free)
| File | Item | Status | Notes |
|------|------|--------|-------|
| `ResidueFieldIso.lean` | `residueFieldIso` | ✅ PROVED | R/v.asIdeal ≃ ResidueField(completion) |
| `ResidueFieldIso.lean` | `toResidueField_surjective` | ✅ PROVED | Via localization approach |
| `AllIntegersCompactProof.lean` | `allIntegersCompact_of_axioms` | ✅ PROVED | Needs `FiniteCompletionResidueFields` |
| `FqPolynomialInstance.lean` | `finite_quotient_polynomial` | ✅ PROVED | Fq[X]/v finite for all v |
| `FqPolynomialInstance.lean` | `instFiniteCompletionResidueFields` | ✅ INSTANCE | For Fq[X] / RatFunc(Fq) |
| `FqPolynomialInstance.lean` | `instAllIntegersCompact` | ✅ INSTANCE | For Fq[X] / RatFunc(Fq) |
| `FqPolynomialInstance.lean` | `valuation_eq_one_almost_all` | ✅ PROVED | Finiteness of valuations ≠ 1 |
| `FqPolynomialInstance.lean` | `instDiscreteCocompactEmbedding` | ✅ INSTANCE | For Fq[X] (sorries in proofs) |

**Build Status**: ✅ Compiles with 5 sorries (1 non-critical, 1 **mathematically false**, 3 under investigation)

**Key Distinction**:
- **Sorries**: Holes in existing proofs → 5 remaining
- **CRITICAL (Cycle 121)**: `discrete_diagonal_embedding` is **FALSE** - K is NOT discrete in finite adeles!
- **Axiom Classes**: `AllIntegersCompact` has valid instance; `DiscreteCocompactEmbedding` has specification issue

**Next Priority**: Decide on resolution path for discreteness issue:
1. Add infinite place (full adeles) - most correct but requires refactoring
2. Weaken DiscreteCocompactEmbedding - if applications don't need discreteness
3. Alternative adelic framework

---

## ✅ RESOLVED: Finite Places Issue (Cycle 121)

**Status**: RESOLVED - Architectural decision made.

**The Issue** (discovered Cycle 121):
- `FiniteAdeleRing R K` uses only finite places (HeightOneSpectrum primes)
- K is **NOT discrete** in finite adeles (mathematically false, not just hard to prove)
- The previous assessment ("weaker statement IS correct for PIDs") was **wrong**

**The Fix**: Add the infinite place via product construction:
```
FullAdeleRing := FiniteAdeleRing R K × K_∞
```

**Why This Works**:
- Classical discreteness of K in A_K uses ALL places including infinity
- The infinite place provides the "missing constraint" that makes K discrete
- Product formula ∏_v |x|_v = 1 uses all places, enforcing discreteness

**Implementation**: See "NEXT CLAUDE: Start Here" section above for concrete steps.

**What's Preserved**:
- `AllIntegersCompact` for finite adeles - still valid and useful
- `valuation_eq_one_almost_all` - still valid for finite places
- Core RR equation machinery - unchanged

---

## Phase 3: Full Riemann-Roch

### Milestone Achieved (v1.0-riemann-inequality)

**Tag**: `git checkout v1.0-riemann-inequality`

**Completed Theorems**:
```lean
-- Affine (unconditional)
lemma riemann_inequality_affine [bd : BaseDim R K] {D : DivisorV2 R} (hD : D.Effective) :
    (ellV2_real R K D : ℤ) ≤ D.deg + bd.basedim

-- Projective (with axioms)
theorem riemann_inequality_proj [ProperCurve k R K] [AllRational k R]
    {D : DivisorV2 R} (hD : D.Effective)
    [∀ E, Module.Finite k (RRSpace_proj k R K E)] :
    (ell_proj k R K D : ℤ) ≤ D.deg + 1
```

### New Goal: Full Riemann-Roch Theorem

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

---

## Strategy Validation (2025-12-18)

**Gemini Report Analysis**: Validated key Mathlib resources exist.

### Validated Mathlib Files

| Component | File | Status |
|-----------|------|--------|
| Kähler Differentials | `Mathlib/RingTheory/Kaehler/Basic.lean` | ✅ EXISTS - `Ω[S⁄R]` notation |
| Different Ideal | `Mathlib/RingTheory/DedekindDomain/Different.lean` | ✅ EXISTS - `differentIdeal`, `traceDual` |
| Hilbert Polynomial | `Mathlib/RingTheory/Polynomial/HilbertPoly.lean` | ✅ EXISTS - `hilbertPoly` |
| Function Field | `Mathlib/AlgebraicGeometry/FunctionField.lean` | ✅ EXISTS - `Scheme.functionField` |
| Projective Spectrum | `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/` | ✅ EXISTS - Full directory |

### Key Discovery: `Different.lean` Has Arithmetic Duality

The file `Mathlib/RingTheory/DedekindDomain/Different.lean` contains:

```lean
-- Trace dual (arithmetic Serre duality!)
def Submodule.traceDual (I : Submodule B L) : Submodule B L :=
  -- x ∈ Iᵛ ↔ ∀ y ∈ I, Tr(x * y) ∈ A

-- Different ideal (arithmetic canonical divisor!)
def differentIdeal : Ideal B :=
  (1 / Submodule.traceDual A K 1).comap (algebraMap B L)

-- Duality via fractional ideals
def FractionalIdeal.dual (I : FractionalIdeal B⁰ L) : FractionalIdeal B⁰ L
```

**This is exactly what we need for Serre duality without derived categories!**

---

## Revised Roadmap

### Track A: Axiomatize First (Fast)

Create `FullRRData` typeclass with axioms, prove RR algebraically.

### Track B: Discharge Axioms (Complete)

Use `differentIdeal` and `traceDual` to prove the axioms.

---

## Cycle Log

### 2025-12-18

*Cycles 80-99 archived to `state/ledger_archive.md` (Vol. 3.1)*


#### Cycle 118 - Concrete Fq[X] Instance: AllIntegersCompact INSTANTIATED!

**Goal**: Create concrete instance of `AllIntegersCompact` for Fq[X] / RatFunc(Fq).

**Status**: ✅ COMPLETE - First concrete instance!

**Results**:
- [x] Created `FqPolynomialInstance.lean` (~145 lines)
- [x] `finite_quotient_polynomial`: Proved `Finite (Fq[X] ⧸ v.asIdeal)` for all v
- [x] `instFiniteCompletionResidueFields`: Instance for Fq[X] / RatFunc(Fq)
- [x] `instAllIntegersCompact`: Instance for Fq[X] / RatFunc(Fq)
- [x] Full pipeline validated: finite quotients → residue field iso → compactness!

**Key Proof Strategy** (for `finite_quotient_polynomial`):

```lean
instance finite_quotient_polynomial (v : HeightOneSpectrum Fq[X]) :
    Finite (Fq[X] ⧸ v.asIdeal) := by
  classical
  -- In PID, all ideals are principal
  have hprinc := IsPrincipalIdealRing.principal v.asIdeal
  let p := hprinc.generator
  have hp : v.asIdeal = Ideal.span {p} := hprinc.span_singleton_generator.symm
  -- p ≠ 0 since v ≠ ⊥
  have hp_ne : p ≠ 0 := ...
  -- Normalize p to make it monic
  have hmonic : Polynomial.Monic (normalize p) := Polynomial.monic_normalize hp_ne
  -- Associated elements generate same ideal
  have hnorm : Ideal.span {normalize p} = Ideal.span {p} :=
    Ideal.span_singleton_eq_span_singleton.mpr (associated_normalize p).symm
  -- Quotient by monic polynomial is finite dimensional over Fq
  haveI : Module.Finite Fq (Fq[X] ⧸ Ideal.span {normalize p}) := hmonic.finite_quotient
  -- Transfer via ideal equality
  haveI : Module.Finite Fq (Fq[X] ⧸ v.asIdeal) := by rw [hp, ← hnorm]; infer_instance
  -- Finite Fq + Module.Finite Fq M → Finite M
  exact Module.finite_of_finite Fq
```

**Key Mathlib Lemmas Used**:
- `IsPrincipalIdealRing.principal` - Every ideal in PID is principal
- `Polynomial.monic_normalize` - Normalizing nonzero polynomial gives monic
- `Ideal.span_singleton_eq_span_singleton` - Associated elements generate same ideal
- `associated_normalize` - x and normalize(x) are associated
- `Polynomial.Monic.finite_quotient` - Quotient by monic is finite dimensional
- `Module.finite_of_finite` - Finite module over finite ring is finite type

**Instance Chain** (now complete for Fq[X]):
```
Fintype Fq + DecidableEq Fq
       ↓
finite_quotient_polynomial (Fq[X]/v finite for all v)
       ↓
instFiniteCompletionResidueFields (via ResidueFieldIso)
       ↓
instAllIntegersCompact (via allIntegersCompact_of_axioms)
```

**Significance**: This is the FIRST concrete instantiation of our axiom classes!
- Validates the entire pipeline from finite field to adelic compactness
- Proves the axiom classes are not vacuously satisfiable
- Establishes the pattern for other Dedekind domains

**Sorry Status** (unchanged from Cycle 117):
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 1 sorry in main path (unchanged)

**Build**: ✅ Compiles successfully

**Next Steps** (Cycle 119+):
1. **Option A**: Work on `DiscreteCocompactEmbedding` for Fq[X] (PID case is simpler)
2. **Option B**: Generalize to other function fields (ringOfIntegers Fq F)
3. **Option C**: Tag milestone for AllIntegersCompact concrete instance

---

#### Cycle 119 - DiscreteCocompactEmbedding Instance for Fq[X] (Structure Complete!)

**Goal**: Create instance of `DiscreteCocompactEmbedding` for Fq[X] / RatFunc(Fq).

**Status**: ✅ COMPLETE (instance created with sorries for deep proofs)

**Results**:
- [x] Extended `FqPolynomialInstance.lean` with DiscreteCocompactEmbedding section
- [x] `valuation_eq_one_almost_all` - finiteness of non-trivial valuations (sorry)
- [x] `discrete_diagonal_embedding` - K is discrete in finite adeles (sorry)
- [x] `closed_diagonal_embedding` - K is closed in finite adeles (sorry)
- [x] `integralAdeles` - defined as {a | ∀ v, a_v ∈ O_v}
- [x] `isCompact_integralAdeles` - integral adeles are compact (sorry)
- [x] `exists_K_translate_in_integralAdeles` - weak approximation for PIDs (sorry)
- [x] `instDiscreteCocompactEmbedding` - INSTANCE for Fq[X] / RatFunc(Fq)!

**Key Structure**:
```lean
instance instDiscreteCocompactEmbedding [AllIntegersCompact Fq[X] (RatFunc Fq)] :
    DiscreteCocompactEmbedding Fq[X] (RatFunc Fq) where
  discrete := discrete_diagonal_embedding Fq
  closed := closed_diagonal_embedding Fq
  compact_fundamental_domain := ⟨integralAdeles Fq, isCompact_integralAdeles Fq, ...⟩
```

**Remaining Sorries** (5 in DiscreteCocompactEmbedding):

1. **`valuation_eq_one_almost_all`**: Nonzero elements have trivial valuation at almost all places
   - Mathematical content: Only finitely many irreducible polynomials divide a nonzero rational function
   - Mathlib path: Factor through `RatFunc.div_surjective`, use `Polynomial.irreducible_factors`

2. **`discrete_diagonal_embedding`**: K is discrete in finite adeles
   - Mathematical content: Follows from (1) - bounded support → isolated points
   - Mathlib path: Use restricted product topology characterization

3. **`closed_diagonal_embedding`**: K is closed in finite adeles
   - Mathematical content: Discrete subgroups of locally compact groups are closed
   - Mathlib path: Use `Subgroup.isClosed_of_discrete` (requires additive version)

4. **`isCompact_integralAdeles`**: ∏_v O_v is compact
   - Mathematical content: Product of compact sets in restricted product is compact
   - Mathlib path: `RestrictedProduct` compactness lemmas + `AllIntegersCompact`

5. **`exists_K_translate_in_integralAdeles`**: Weak approximation for PIDs
   - Mathematical content: For PID, can clear denominators at all places simultaneously
   - Mathlib path: Use `IsPrincipalIdealRing`, `Associates.factors_unique`

**Significance**:
- BOTH key adelic axiom classes now have instances for Fq[X]!
- The "Track A → Track B" pattern is validated: axiomatize first, then discharge
- For Fq[X] (PID), the sorries are all standard number-theoretic facts
- The structure shows the path for general function fields (with class group modifications)

**Mathematical Background** (why PIDs are simpler):
- For a PID, every fractional ideal is principal
- Weak approximation holds unconditionally (no class group obstruction)
- The fundamental domain is simply ∏_v O_v (no need for idele class group quotient)
- For non-PIDs, would need to quotient by class group or use Minkowski's theorem

**Sorry Status**:
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)
- FqPolynomialInstance.lean: 5 sorries (DiscreteCocompactEmbedding proofs)

**Total**: 6 sorries in proof path

**Build**: ✅ Compiles successfully

**Next Steps** (Cycle 120+):
1. Fill `valuation_eq_one_almost_all` using polynomial factorization
2. Fill `isCompact_integralAdeles` using RestrictedProduct API
3. Fill discreteness/closedness from the above
4. Fill weak approximation using PID structure
5. Or: Move to other axioms (`AdelicRRData`)

---

#### Cycle 120 - First DiscreteCocompactEmbedding Sorry Filled!

**Goal**: Fill sorries in DiscreteCocompactEmbedding proofs for Fq[X].

**Status**: 🔶 PARTIAL (1 of 5 sorries filled!)

**Results**:
- [x] `valuation_eq_one_almost_all` - PROVED! Key lemma for discreteness
- [ ] `discrete_diagonal_embedding` - Pending (requires restricted product topology work)
- [ ] `closed_diagonal_embedding` - Pending (follows from discrete)
- [ ] `isCompact_integralAdeles` - Pending (product compactness)
- [ ] `exists_K_translate_in_integralAdeles` - Pending (weak approximation)

**Key Proof Strategy** (for `valuation_eq_one_almost_all`):

Used Mathlib's `HeightOneSpectrum.Support.finite` which proves that for any `k : K`,
the set `{v | 1 < v.valuation K k}` is finite. For nonzero `f`:

```lean
{v | v.valuation f ≠ 1} = {v | v.valuation f > 1} ∪ {v | v.valuation f < 1}
                        = Support(f) ∪ Support(f⁻¹)
```

Both are finite by `Support.finite`, so their union is finite.

**Key Mathlib Lemma Used**:
```lean
-- In Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean
lemma HeightOneSpectrum.Support.finite (k : K) : (Support R k).Finite
```

**Remaining Sorries Analysis**:

1. **`discrete_diagonal_embedding`**: Requires showing {0} is open in subspace topology
   - Needs: Basic neighborhood characterization in restricted product
   - Approach: Use `valuation_eq_one_almost_all` to show nonzero elements are bounded away from 0

2. **`closed_diagonal_embedding`**: Standard result for discrete subgroups
   - Needs: `Subgroup.isClosed_of_discrete` or equivalent
   - Approach: Discrete + locally compact → closed

3. **`isCompact_integralAdeles`**: Product of compact sets
   - Needs: Tychonoff for restricted products, or embedding lemma
   - Approach: Show ∏_v O_v embeds as compact subset

4. **`exists_K_translate_in_integralAdeles`**: Weak approximation for PIDs
   - Needs: Strong approximation theorem machinery
   - Approach: Use PID structure to clear denominators

**Sorry Status**:
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)
- FqPolynomialInstance.lean: 4 sorries (DiscreteCocompactEmbedding proofs)

**Total**: 5 sorries in proof path (down from 6!)

**Build**: ✅ Compiles successfully

**Significance**: The `valuation_eq_one_almost_all` proof demonstrates that Mathlib's adelic
infrastructure (specifically `Support.finite`) can be leveraged for our concrete instances.
The remaining proofs require deeper work with restricted product topology.

**Next Steps** (Cycle 121+):
1. Research restricted product neighborhood basis for discreteness proof
2. Find/prove Tychonoff-like theorem for restricted products
3. Or: Accept remaining sorries with clear mathematical justification and move to AdelicRRData

---

#### Cycle 121 - CRITICAL FINDING: K is NOT Discrete in Finite Adeles

**Goal**: Prove `discrete_diagonal_embedding` using `valuation_eq_one_almost_all`.

**Status**: ⚠️ MATHEMATICAL OBSTRUCTION DISCOVERED

**Results**:
- [x] Thorough analysis of restricted product topology
- [x] Discovered: K is **NOT discrete** in the finite adeles
- [x] Updated FqPolynomialInstance.lean with detailed documentation
- [x] Identified root cause and resolution options

**The Mathematical Obstruction**:

K is **NOT** discrete in the finite adeles. This statement is FALSE and cannot be proved.

**Proof that discreteness fails**:

1. In the cofinite restricted product topology, neighborhoods of 0 are characterized by:
   - At finitely many places v₁,...,vₙ: component aᵥᵢ ∈ Uᵢ for some open Uᵢ ∋ 0
   - At all other places: component is in O_v (automatic from restricted product)

2. The smallest neighborhood at each vᵢ is {x | v(x) > 1} = m_v (maximal ideal).

3. For k ∈ Fq[X] to have diagonalEmbedding(k) in such a neighborhood:
   k must satisfy vᵢ(k) > 1 for all i, i.e., k must be divisible by v₁,...,vₙ.

4. The set {k ∈ Fq[X] | v₁ | k ∧ ... ∧ vₙ | k} = (v₁ · ... · vₙ) · Fq[X] is **INFINITE**.

5. Therefore, every neighborhood of 0 contains infinitely many elements of K.

6. Hence {0} is NOT open in the subspace topology, so K is NOT discrete.

**Root Cause**: The finite adeles use only `HeightOneSpectrum R` (finite places).
For function fields, the **place at infinity** is NOT included.
Full discreteness requires including all places via `FunctionField.inftyValuation`.

**Impact on DiscreteCocompactEmbedding**:
- `discrete_diagonal_embedding`: **CANNOT BE PROVED** (mathematically false)
- `closed_diagonal_embedding`: Cannot derive from discreteness; needs different approach
- `isCompact_integralAdeles`: Independent of discreteness; might still be provable
- `exists_K_translate_in_integralAdeles`: Weak approximation; might still work

**Options for Resolution**:

1. **Add Infinity**: Extend to full adeles including `FunctionField.inftyValuation`
   - Most mathematically correct approach
   - Requires significant refactoring of adelic infrastructure

2. **Weaken DiscreteCocompactEmbedding**: Remove discreteness requirement
   - If H¹ finiteness doesn't need discreteness, this suffices
   - Need to verify which applications actually need discrete

3. **Different Framework**: Alternative formulation of adelic theory
   - E.g., use norm topology instead of restricted product topology

**Sorry Status** (updated):
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)
- FqPolynomialInstance.lean: 4 sorries (1 is **mathematically impossible**)

**Total**: 5 sorries in proof path (1 is false statement, 3 need investigation)

**Build**: ✅ Compiles successfully

**Significance**: This is a fundamental specification issue, not a proof difficulty.
The ledger's "SPEC RISK" section warned about this, but the previous assessment
("weaker statement IS correct for PIDs") was incorrect.

**Recommendation**: Before proceeding with more cycle work on DiscreteCocompactEmbedding,
decide on which resolution option to pursue. The most robust approach is Option 1
(add infinity), but this requires significant infrastructure changes.

**POST-CYCLE UPDATE**: Architectural decision confirmed by user:
- ✅ **Option 1 (Add Infinity) selected** as the correct path
- Implementation strategy: Define `FullAdeleRing := FiniteAdeleRing × K_∞` (product approach)
- Don't rework HeightOneSpectrum; build on top of existing finite adeles
- See "NEXT CLAUDE: Start Here" section at top of ledger for detailed next steps

---

#### Cycle 122 - FullAdeles.lean Created (Product Definition)

**Goal**: Implement Step 1 of the full adeles plan - create `FullAdeles.lean` with the product definition.

**Status**: ✅ COMPLETE (SORRY-FREE!)

**Results**:
- [x] Created `RrLean/RiemannRochV2/FullAdeles.lean` (~245 lines)
- [x] `FullAdeleRing R K K_infty := FiniteAdeleRing R K × K_infty` - general definition
- [x] `fullDiagonalEmbedding : K →+* FullAdeleRing R K K_infty` - ring homomorphism
- [x] `fullDiagonalEmbedding_injective` - PROVED (uses injectivity at infinity)
- [x] `FullDiscreteCocompactEmbedding` class - corrected axioms for full adeles
- [x] Build compiles successfully with NO SORRIES

**Key Definitions**:
```lean
def FullAdeleRing := FiniteAdeleRing R K × K_infty

def fullDiagonalEmbedding : K →+* FullAdeleRing R K K_infty :=
  RingHom.prod (FiniteAdeleRing.algebraMap R K) (algebraMap K K_infty)

class FullDiscreteCocompactEmbedding : Prop where
  discrete : DiscreteTopology (Set.range (fullDiagonalEmbedding R K K_infty))
  closed : IsClosed (Set.range (fullDiagonalEmbedding R K K_infty))
  compact_fundamental_domain : ∃ F, IsCompact F ∧ ∀ a, ∃ x : K, a - fullDiagonalEmbedding R K K_infty x ∈ F
```

**Mathematical Insight** (why K IS discrete in full adeles):
- In finite adeles: neighborhoods constrain only finitely many finite places
- For any finite set S of primes, infinitely many polynomials are divisible by all of them
- Hence K ∩ U is infinite for every neighborhood U in finite adeles

- In full adeles: neighborhoods constrain ALL places including infinity
- Product formula: ∏_v |k|_v = 1 enforces global constraint
- If |k|_p ≤ 1 for all finite p AND |k|_∞ < ε, then k is bounded by Riemann-Roch
- Only finitely many k ∈ K satisfy such bounds → K is discrete

**Concrete Instance Status**:
The concrete instance for `Polynomial Fq / RatFunc Fq / FqtInfty Fq` requires navigating
Mathlib's completion API more carefully:
- `FunctionField.FqtInfty Fq` is the completion at infinity
- `Algebra (RatFunc Fq) (FqtInfty Fq)` comes from `UniformSpace.Completion`
- Valuation on completion elements uses `Valued.v` (not `inftyValuation` directly)
This is deferred to Cycle 123.

**Sorry Status**:
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)
- FqPolynomialInstance.lean: 4 sorries (1 FALSE, 3 for finite adeles)
- FullAdeles.lean: 0 sorries (SORRY-FREE!)

**Total**: 5 sorries in proof path (unchanged, FullAdeles adds no new sorries)

**Build**: ✅ Compiles successfully

**Next Steps** (Cycle 123+):
1. Instantiate `FullDiscreteCocompactEmbedding` for `Polynomial Fq / RatFunc Fq / FqtInfty Fq`
2. Prove `fq_discrete_in_fullAdeles` using product formula
3. Audit `AdelicH1v2.lean` for full adele requirements

---

## Key Discoveries for Future Cycles

### NEW: Class Group Finiteness in Mathlib (Cycle 117)

**Key Theorem**: `ClassGroup.fintypeOfAdmissibleOfFinite`
- Location: `Mathlib/NumberTheory/ClassNumber/Finite.lean:349`
- Proves `Fintype (ClassGroup S)` for integral closures
- Uses admissible absolute values (NOT Riemann-Roch)

**Pre-built Function Field Instance**:
```lean
-- In Mathlib/NumberTheory/ClassNumber/FunctionField.lean
noncomputable instance : Fintype (ClassGroup (ringOfIntegers Fq F)) :=
  ClassGroup.fintypeOfAdmissibleOfFinite (RatFunc Fq) F
    (Polynomial.cardPowDegreeIsAdmissible : AbsoluteValue.IsAdmissible ...)
```

**This is non-circular** - the proof uses norm bounds and pigeonhole arguments, not dimension counting.

**For DiscreteCocompactEmbedding**: The cocompact fundamental domain follows from class group finiteness, not RR.

---

### CRITICAL: `evalOneₐ_surjective` in Mathlib (Found Cycle 110)

**Location**: `Mathlib/RingTheory/AdicCompletion/Algebra.lean`

```lean
/-- The canonical projection from the `I`-adic completion to `R ⧸ I`. -/
def evalOneₐ : AdicCompletion I R →ₐ[R] R ⧸ I :=
  (Ideal.Quotient.factorₐ _ (by simp)).comp (evalₐ _ 1)

lemma evalOneₐ_surjective : Function.Surjective (evalOneₐ I) := by
  dsimp [evalOneₐ]
  exact (Ideal.Quotient.factor_surjective (show I ^ 1 ≤ I by simp)).comp
    (AdicCompletion.surjective_evalₐ I 1)
```

**What it says**: The natural map `AdicCompletion I R → R/I` is surjective.

**The Gap**: Two different completion APIs in Mathlib:

| Completion | Definition | API Location |
|------------|------------|--------------|
| `AdicCompletion I R` | I-adic completion (inverse limit of R/Iⁿ) | `Mathlib/RingTheory/AdicCompletion/` |
| `v.adicCompletion K` | Valuation completion (uniform space) | `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` |

**Connection NOT in Mathlib**: For a DVR (or localization at height-one prime), these completions are isomorphic:
```
AdicCompletion v.asIdeal R_v ≅ v.adicCompletionIntegers K
```
This isomorphism is standard mathematics but NOT formalized in Mathlib (as of v4.16.0).

**Two Paths to Discharge `toResidueField_surjective`**:

1. **Bridge Path** (potentially cleaner):
   - Prove `AdicCompletion v.asIdeal (Localization.AtPrime v.asIdeal) ≅ v.adicCompletionIntegers K`
   - Transfer `evalOneₐ_surjective` via this isomorphism
   - Get surjectivity for free

2. **Direct Path** (current approach):
   - Use `denseRange_algebraMap_adicCompletion` (already proved)
   - Navigate the density argument through Mathlib's valued field API
   - Use helper lemmas in `ResidueFieldIso.lean`

**Recommendation**: Try the Bridge Path first - if the isomorphism exists or is easy to prove, it gives surjectivity immediately. If blocked, fall back to Direct Path.

### Related Mathlib Resources

| Resource | Location | Use |
|----------|----------|-----|
| `evalOneₐ_surjective` | `AdicCompletion/Algebra.lean:181` | I-adic → R/I surjective |
| `surjective_evalₐ` | `AdicCompletion/Algebra.lean:151` | General n version |
| `IsFractionRing (R ⧸ I) I.ResidueField` | `LocalRing/ResidueField/Ideal.lean:99` | R/I ≃ residue field when I maximal |
| `equivQuotMaximalIdeal` | `Localization/AtPrime/Basic.lean:387` | R/p ≃ R_p/m |
| `Completion.denseRange_coe` | `UniformSpace/Completion.lean` | Density in completions |

---

## References

### Primary (Validated)
- `Mathlib/RingTheory/DedekindDomain/Different.lean` - traceDual, differentIdeal
- `Mathlib/RingTheory/Kaehler/Basic.lean` - Ω[S⁄R], KaehlerDifferential

### Secondary
- flt-regular project - arithmetic duality patterns
- Liu "Algebraic Geometry and Arithmetic Curves" Ch. 7 - arithmetic RR

### Mathematical Background
- The "Different Ideal" approach: K corresponds to the inverse of the different ideal
- Serre duality becomes: L(K-D)* ≅ H¹(D) via trace pairing
- For curves: H¹(D) = (global differentials with prescribed poles) / (exact forms)
