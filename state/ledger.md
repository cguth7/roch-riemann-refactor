# Ledger Vol. 3.2 (Cycles 118+) - Full Adeles & Riemann-Roch

*For Cycles 1-34, see `state/ledger_archive.md` (Vol. 1)*
*For Cycles 35-79, see `state/ledger_archive.md` (Vol. 2)*
*For Cycles 80-99, see `state/ledger_archive.md` (Vol. 3.1)*
*For Cycles 100-117, see `state/ledger_archive.md` (Vol. 3.2 Part 1 - AllIntegersCompact)*

---

## 🎯 NEXT CLAUDE: Start Here (Post-Cycle 133)

### Critical Context
**Cycle 121 discovered a spec bug**: K is NOT discrete in the *finite* adeles.
**Cycle 122 created `FullAdeles.lean`** with the product definition A = A_f × K_∞.
**Cycle 130 PROVED `fq_discrete_in_fullAdeles`** - the KEY discreteness theorem!
**Cycle 131 PROVED `fq_closed_in_fullAdeles`** - discrete + T2 → closed!
**Cycle 132**: Finite adeles compactness DONE!
**Cycle 133**: Infinity compactness structure written, RankOne/IsNontrivial proofs blocked on tactic issues

### Current State
- ✅ `algebraMap_FqtInfty_injective` - PROVED
- ✅ `polynomial_inftyVal_ge_one` - PROVED
- ✅ `isOpen_inftyBall_lt_one` - PROVED
- ✅ `finite_integral_implies_polynomial` - PROVED
- ✅ `isOpen_integralFiniteAdeles` - PROVED
- ✅ `diag_integral_implies_valuation_le` - PROVED
- ✅ `diag_infty_valuation` - PROVED
- ✅ **`fq_discrete_in_fullAdeles` - PROVED in Cycle 130!**
- ✅ **`fq_closed_in_fullAdeles` - PROVED in Cycle 131!**
- 🔶 `isCompact_integralFullAdeles` - Finite adeles PROVED, infinity sorry
- ⚪ `exists_translate_in_integralFullAdeles` - SORRY: weak approximation

### Concrete Next Steps (Cycle 133+)

**PRIORITY 1: Finish `isCompact_integralFullAdeles` - Infinity Component**

The finite adeles compactness is PROVED via:
- `RestrictedProduct.range_structureMap` identifies integral adeles as image
- `isCompact_range` + `isEmbedding_structureMap.continuous`

For the infinity component `{x : FqtInfty | Valued.v x ≤ 1}`, need:
1. **RankOne instance** for `Valued.v` on `FqtInfty Fq` (ℤᵐ⁰ embeds into ℝ≥0)
2. **CompleteSpace** for `Valued.integer (FqtInfty Fq)` - follows from completion
3. **IsDiscreteValuationRing** for the integer ring
4. **Finite residue field** - should be Fq

Then use `Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`

**PRIORITY 2: Weak approximation `exists_translate_in_integralFullAdeles`**
- For any adele a, find x ∈ K such that a - diag(x) is integral
- Use PID structure: only finitely many places with non-integral components
- Find polynomial that "clears denominators" at all finite places
- May need degree control for infinity place

### Key Mathlib APIs

| What you need | How to get it |
|---------------|---------------|
| Product compact | `IsCompact.prod` |
| Infinity integers compact | `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField` |
| RankOne for ℤᵐ⁰ | Need to construct embedding `ℤᵐ⁰ →*₀ ℝ≥0` |
| Finite adeles compact | ✅ Done via `range_structureMap` + `isCompact_range` |

### What NOT To Do
- ❌ Don't try to prove `discrete_diagonal_embedding` for finite adeles (it's false)
- ❌ Don't use `inftyValuation` directly on `FqtInfty` elements (use `Valued.v`)
- ❌ Don't guess Mathlib lemma names - search with `rg` first

---

## ⚡ Quick Reference: Current Axiom/Sorry Status (Cycle 132)

### Sorries (proof holes)
| File | Item | Status | Notes |
|------|------|--------|-------|
| `TraceDualityProof.lean` | `finrank_dual_eq` | ⚪ 1 sorry | NOT on critical path |
| `FqPolynomialInstance.lean` | `discrete_diagonal_embedding` | ❌ FALSE | **CANNOT BE PROVED** - K not discrete in finite adeles |
| `FqPolynomialInstance.lean` | `closed_diagonal_embedding` | ⚪ 1 sorry | Needs different approach (not from discreteness) |
| `FqPolynomialInstance.lean` | `isCompact_integralAdeles` | ⚪ 1 sorry | Product compactness - may still work |
| `FqPolynomialInstance.lean` | `exists_K_translate_in_integralAdeles` | ⚪ 1 sorry | Weak approximation - may still work |
| `FullAdeles.lean` | `algebraMap_FqtInfty_injective` | ✅ PROVED | Cycle 124: uses `coe_inj` for T0 spaces |
| `FullAdeles.lean` | `finite_integral_implies_polynomial` | ✅ PROVED | **Cycle 125**: UFD/coprimality argument |
| `FullAdeles.lean` | `fq_discrete_in_fullAdeles` | ✅ PROVED | **Cycle 130**: KEY discreteness theorem! |
| `FullAdeles.lean` | `fq_closed_in_fullAdeles` | ✅ PROVED | **Cycle 131**: T2Space + discreteness → closed |
| `FullAdeles.lean` | `isCompact_integralFullAdeles` | 🔶 PARTIAL | **Cycle 132**: Finite adeles DONE, infinity sorry |
| `FullAdeles.lean` | `exists_translate_in_integralFullAdeles` | ⚪ 1 sorry | Weak approximation |

### New Helper Lemmas (Cycle 124)
| File | Item | Status | Notes |
|------|------|--------|-------|
| `FullAdeles.lean` | `polynomial_inftyVal_ge_one` | ✅ PROVED | Nonzero poly has |·|_∞ ≥ 1 |
| `FullAdeles.lean` | `isOpen_inftyBall_lt_one` | ✅ PROVED | {x \| |x|_∞ < 1} is open |
| `FullAdeles.lean` | `finite_integral_inftyVal_ge_one` | ✅ PROVED | Uses `finite_integral_implies_polynomial` |

### Axiom Classes (instantiation status)
| File | Class | Status | Notes |
|------|-------|--------|-------|
| `AllIntegersCompactProof.lean` | `FiniteCompletionResidueFields` | ✅ INSTANTIATED | For Fq[X] in FqPolynomialInstance.lean |
| `AdelicTopology.lean` | `AllIntegersCompact` | ✅ INSTANTIATED | For Fq[X] in FqPolynomialInstance.lean |
| `AdelicTopology.lean` | `DiscreteCocompactEmbedding` | ⚠️ FALSE | K NOT discrete in finite adeles |
| `FullAdeles.lean` | `FullDiscreteCocompactEmbedding` | ✅ INSTANTIATED | For Fq[X] (with sorries) - CORRECT class |
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
| `FullAdeles.lean` | `Nonempty HeightOneSpectrum Fq[X]` | ✅ PROVED | X is irreducible |
| `FullAdeles.lean` | `inftyRingHom` | ✅ DEFINED | RatFunc Fq →+* FqtInfty Fq |
| `FullAdeles.lean` | `fqFullDiagonalEmbedding_injective` | ✅ PROVED | Uses infinity injection |

**Build Status**: ✅ Compiles with 7 sorries total (+ 1 FALSE)
- TraceDualityProof.lean: 1 sorry (non-critical)
- FqPolynomialInstance.lean: 4 sorries (1 FALSE, 3 finite adeles related)
- FullAdeles.lean: 2 sorries (compactness partial, weak approx)

**Key Progress (Cycle 123)**:
- ✅ Full adeles concrete instance structure complete
- ✅ `FullDiscreteCocompactEmbedding` replaces broken `DiscreteCocompactEmbedding`
- ⏳ 5 sorries in FullAdeles.lean are mathematically provable (not false like finite adeles discreteness)

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

#### Cycle 124 - Discreteness Proof Structure & Helper Lemmas

**Goal**: Prove helper lemmas and establish the structure for `fq_discrete_in_fullAdeles`.

**Status**: 🔶 PARTIAL - Key helper lemmas proved, one algebraic lemma remains

**Results**:
- [x] `algebraMap_FqtInfty_injective` - PROVED using `coe_inj` for T0 spaces
- [x] `polynomial_inftyVal_ge_one` - PROVED: nonzero poly p has |p|_∞ ≥ 1
- [x] `isOpen_inftyBall_lt_one` - PROVED: {x | |x|_∞ < 1} is open via `Valued.isClopen_ball`
- [x] `finite_integral_inftyVal_ge_one` - PROVED: integral at all finite + k ≠ 0 ⟹ |k|_∞ ≥ 1
- [ ] `finite_integral_implies_polynomial` - SORRY: key algebraic lemma

**Key Proof Techniques**:

1. **T0Space for completions**: `Valued` rings are T0 via `ValuedRing.separated`, and
   `UniformSpace.Completion.coe_inj` uses T0Space to prove injectivity.

2. **Polynomial valuation**: Used `FunctionField.inftyValuation.polynomial` which gives
   `inftyValuationDef(p) = exp(deg p)`. Combined with `WithZero.exp_le_exp` and `exp_zero`
   to show `1 ≤ exp(deg p)` for deg p ≥ 0.

3. **Open balls in valued spaces**: `Valued.isClopen_ball` directly gives that
   `{x | Valued.v x < r}` is clopen (hence open).

**Discreteness Proof Strategy** (now concrete):
```
For k ∈ K with diagonal(k) ∈ U = U_fin × {x | |x|_∞ < 1}:
1. From U_fin: k is integral at all finite places
2. By finite_integral_implies_polynomial: k ∈ Fq[X]
3. By polynomial_inftyVal_ge_one: nonzero k has |k|_∞ ≥ 1
4. But |k|_∞ < 1 from U_∞ ⟹ k = 0
5. Hence U ∩ range(diagonal) = {0}, so K is discrete
```

**Remaining Sorry** (`finite_integral_implies_polynomial`):
For k = p/q with gcd(p,q) = 1:
- If |k|_v ≤ 1 for all finite v, then at any prime v dividing q but not p,
  we'd have |k|_v = |p|_v / |q|_v > 1 (contradiction)
- Hence q has no prime factors, so q ∈ Fq× and k is a polynomial

**Sorry Status**:
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)
- FqPolynomialInstance.lean: 4 sorries (1 FALSE, 3 finite adeles related)
- FullAdeles.lean: 5 sorries (1 new algebraic, 4 existing)

**Total**: 10 sorries in proof path (replaced `algebraMap_FqtInfty_injective` with `finite_integral_implies_polynomial`)

**Build**: ✅ Compiles successfully

**Next Steps** (Cycle 125+):
1. Prove `finite_integral_implies_polynomial` using UFD/PID properties
2. Complete `fq_discrete_in_fullAdeles` using the established structure
3. Derive `fq_closed_in_fullAdeles` from discreteness via `AddSubgroup.isClosed_of_discrete`

---

#### Cycle 125 - Key Algebraic Lemma PROVED! (`finite_integral_implies_polynomial`)

**Goal**: Prove `finite_integral_implies_polynomial` - the key algebraic lemma for discreteness.

**Status**: ✅ COMPLETE - Key lemma proved!

**Results**:
- [x] `finite_integral_implies_polynomial` - **PROVED** (~90 lines)
- [x] Documented proof strategies for `fq_discrete_in_fullAdeles` and `fq_closed_in_fullAdeles`
- [x] Identified remaining technical challenge: RestrictedProduct topology API

**Key Proof Techniques** (for `finite_integral_implies_polynomial`):

The proof shows: if k ∈ RatFunc Fq is integral at all finite places (|k|_v ≤ 1), then k is a polynomial.

```lean
-- Strategy: Show denom(k) = 1, hence k is a polynomial
-- If denom(k) ≠ 1, it has an irreducible factor p
-- This creates HeightOneSpectrum v where |k|_v > 1, contradiction

let d := k.denom  -- monic by monic_denom
let n := k.num
have hcop : IsCoprime n d := isCoprime_num_denom k

-- If d ≠ 1, d is not a unit (monic_eq_one_of_isUnit)
-- By WfDvdMonoid.exists_irreducible_factor, ∃ irreducible p | d
-- Construct HeightOneSpectrum v from p (Irreducible.prime + span_singleton_prime)

-- Since p | d: d ∈ v.asIdeal, so v.intValuation d < 1
-- By IsCoprime + Irreducible.coprime_iff_not_dvd: p ∤ n
-- Hence n ∉ v.asIdeal, so v.intValuation n = 1

-- v.valuation k = v.valuation(n/d) = 1 / v.intValuation d > 1
-- Contradiction with hypothesis v.valuation k ≤ 1
-- Therefore d = 1, and k is a polynomial
```

**Key Mathlib Lemmas Used**:
- `RatFunc.monic_denom`, `RatFunc.isCoprime_num_denom`, `RatFunc.num_div_denom`
- `Polynomial.Monic.eq_one_of_isUnit` - monic units are 1
- `WfDvdMonoid.exists_irreducible_factor` - non-unit has irreducible factor
- `Irreducible.prime` (in UFD/DecompositionMonoid)
- `Ideal.span_singleton_prime` - span{p} is prime iff p is prime
- `intValuation_lt_one_iff_mem`, `intValuation_eq_one_iff`
- `Irreducible.coprime_iff_not_dvd` - IsCoprime p n ↔ ¬p ∣ n

**Remaining Sorries**:

| Sorry | Challenge |
|-------|-----------|
| `fq_discrete_in_fullAdeles` | Need to show "integral at all finite places" is open in restricted product |
| `fq_closed_in_fullAdeles` | Need T2Space instance for full adeles |
| `isCompact_integralFullAdeles` | Product of compacts |
| `exists_translate_in_integralFullAdeles` | Weak approximation |

**Sorry Status**:
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)
- FqPolynomialInstance.lean: 4 sorries (1 FALSE, 3 finite adeles related)
- FullAdeles.lean: 4 sorries (down from 5!)

**Total**: 9 sorries in proof path (down from 10!)

**Build**: ✅ Compiles successfully

**Significance**: The key algebraic lemma is now proved! The discreteness proof has all its mathematical lemmas in place. The remaining challenge is navigating Mathlib's RestrictedProduct topology API to formalize that "integral at all finite places" gives an open neighborhood.

**Next Steps** (Cycle 126+):
1. Explore RestrictedProduct API for open neighborhoods
2. Prove T2Space instance for full adeles (product of T2 spaces)
3. Complete discreteness and closedness proofs
4. Tackle compactness and weak approximation

---

#### Cycle 126 - Fixed Proof Errors & Discreteness Strategy Documented

**Goal**: Fix compilation errors in `finite_integral_implies_polynomial` and document discreteness proof strategy.

**Status**: ✅ COMPLETE - Proof fixed, strategy documented

**Results**:
- [x] Fixed `IsCoprime.gcd_eq_one` → direct Bézout argument with `dvd_add`
- [x] Fixed `Irreducible.not_unit` → use `hp_irr.1` (first part of Irreducible)
- [x] Fixed `valuation_of_algebraMap` argument order → `v.valuation_of_algebraMap n`
- [x] Fixed `intValuation_ne_zero'` → use `mem_nonZeroDivisors_of_ne_zero`
- [x] Fixed `linarith` on `WithZero (Multiplicative ℤ)` → use `not_lt.mpr`
- [x] Documented key Mathlib lemma: `RestrictedProduct.isOpen_forall_mem`

**Key Fix** (`finite_integral_implies_polynomial` coprimality argument):

```lean
-- Old (incorrect): hp_irr.coprime_iff_not_dvd, hcop.gcd_eq_one
-- New (correct): Direct Bézout identity argument
have hp_not_dvd_n : ¬(p ∣ n) := by
  intro hdvd_n
  obtain ⟨a, b, hab⟩ := hcop  -- Bézout: a*n + b*d = 1
  have hp_dvd_one : p ∣ 1 := by
    calc p ∣ a * n + b * d := dvd_add (dvd_mul_of_dvd_right hdvd_n a) (dvd_mul_of_dvd_right hp_dvd b)
         _ = 1 := hab
  exact hp_irr.1 (isUnit_of_dvd_one hp_dvd_one)
```

**Key Discovery**: `RestrictedProduct.isOpen_forall_mem`
- Shows that `{f | ∀ v, f.1 v ∈ A_v}` is open when each `A_v` is open
- Apply with `A_v = v.adicCompletionIntegers K` (open by `Valued.isOpen_valuationSubring`)
- This proves ∏_v O_v is open in FiniteAdeleRing

**Sorry Status** (unchanged):
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)
- FqPolynomialInstance.lean: 4 sorries (1 FALSE, 3 finite adeles related)
- FullAdeles.lean: 4 sorries (discreteness, closedness, compactness, weak approx)

**Total**: 9 sorries in proof path (unchanged)

**Build**: ✅ Compiles successfully

**Next Steps** (Cycle 127+):
1. Apply `RestrictedProduct.isOpen_forall_mem` to prove U_fin is open
2. Complete `fq_discrete_in_fullAdeles` using the documented strategy
3. Prove `fq_closed_in_fullAdeles` from discreteness + T2Space

---

#### Cycle 128 - Helper Lemmas & Discreteness Structure

**Goal**: Apply `RestrictedProduct.isOpen_forall_mem` and structure the discreteness proof.

**Status**: 🔶 PARTIAL - Key helper proved, main proof has sorry with documented strategy

**Results**:
- [x] Added import `Mathlib.Topology.DiscreteSubset` for `isDiscrete_iff_forall_exists_isOpen`
- [x] **PROVED `isOpen_integralFiniteAdeles`**: U_fin = {a | ∀ v, a_v ∈ O_v} is open
  - Uses `RestrictedProduct.isOpen_forall_mem` with `Valued.isOpen_valuationSubring`
- [x] Created `diag_integral_implies_valuation_le` (sorry): connects finite component to valuation
- [x] Created `diag_infty_valuation` (sorry): connects infinity component to inftyValuationDef
- [x] Documented detailed proof strategy in `fq_discrete_in_fullAdeles` docstring

**Key Progress**:
```lean
/-- The set of integral finite adeles is open. -/
theorem isOpen_integralFiniteAdeles :
    IsOpen {a : FiniteAdeleRing Fq[X] (RatFunc Fq) |
      ∀ v, a.1 v ∈ v.adicCompletionIntegers (RatFunc Fq)} := by
  have hOv_open : ∀ v : HeightOneSpectrum Fq[X],
      IsOpen (v.adicCompletionIntegers (RatFunc Fq) : Set (v.adicCompletion (RatFunc Fq))) :=
    fun v ↦ Valued.isOpen_valuationSubring _
  exact RestrictedProduct.isOpen_forall_mem hOv_open
```

**Remaining Sorries in FullAdeles.lean** (6 total):
| Sorry | Description | Difficulty |
|-------|-------------|------------|
| `diag_integral_implies_valuation_le` | Connect finite component to valuation | Easy (API) |
| `diag_infty_valuation` | Connect infinity component to inftyValuationDef | Easy (API) |
| `fq_discrete_in_fullAdeles` | Main discreteness proof | Medium (plumbing) |
| `fq_closed_in_fullAdeles` | Discrete + T2 → closed | Easy |
| `isCompact_integralFullAdeles` | Product of compacts | Medium |
| `exists_translate_in_integralFullAdeles` | Weak approximation | Medium |

**Technical Lesson**: Extracting helper lemmas (even with sorry) keeps the main proof clean
and avoids "simp thrash" where repeated simp failures cause wasted cycles.

**Build**: ✅ Compiles successfully with 11 sorries total

**Next Steps** (Cycle 129+):
1. Fill `diag_integral_implies_valuation_le` using `Valued.valuedCompletion_apply`
2. Fill `diag_infty_valuation` using completion embedding properties
3. Fill `fq_discrete_in_fullAdeles` using the documented strategy

---

#### Cycle 130 - DISCRETENESS PROVED! (`fq_discrete_in_fullAdeles`)

**Goal**: Complete the discreteness proof for K in full adeles.

**Status**: ✅ COMPLETE - Key theorem proved!

**Results**:
- [x] **PROVED `fq_discrete_in_fullAdeles`** (~90 lines) - The main discreteness theorem!
- [x] Fixed type issues with `← hk` direction for simp substitution
- [x] Used `Valuation.map_zero` (not `map_zero`) for valuation goals
- [x] Used `Continuous.prodMk` for product continuity

**Key Proof Techniques**:

1. **Use `discreteTopology_subtype_iff'`**: Reduces to showing each point has isolating open set
2. **Define U = {a | a.1 - y.1 ∈ U_fin ∧ a.2 - y.2 ∈ U_infty}** where:
   - `U_fin = {b | ∀ v, b.val v ∈ O_v}` (integral finite adeles, open by `isOpen_integralFiniteAdeles`)
   - `U_infty = {x | Valued.v x < 1}` (open unit ball, open by `isOpen_inftyBall_lt_one`)
3. **Show U is open**: Preimage of open product under continuous subtraction
4. **Show U ∩ range = {y}**:
   - For `diag(m) ∈ U`: let `d = m - k`, use `← hk` to substitute `y = diag(k)`
   - `diag(d)` is integral at all finite places → `d ∈ Fq[X]` by `finite_integral_implies_polynomial`
   - `|d|_∞ < 1` but nonzero polynomial has `|·|_∞ ≥ 1` → `d = 0` → `m = k`

**Lessons Learned**:
- Use `← hk` (not `hk`) when you want to replace `y` with `diag(k)` in simp
- For valuation of 0, use `Valuation.map_zero` not `map_zero`
- Use `Continuous.prodMk` for product continuity, not `Continuous.prod`
- When proving `0 ∈ O_v`, use `rfl` to show `(0 : FiniteAdeleRing).val v = 0`

**Sorry Status**:
- FullAdeles.lean: 3 sorries (closedness, compactness, weak approx) - down from 4!

**Build**: ✅ Compiles successfully

**Next Steps** (Cycle 131+):
1. Prove `fq_closed_in_fullAdeles` using discreteness + T2Space
2. Prove compactness and weak approximation

---

#### Cycle 131 - CLOSEDNESS PROVED! (`fq_closed_in_fullAdeles`)

**Goal**: Prove that the diagonal embedding of K is closed in full adeles.

**Status**: ✅ COMPLETE - Closedness theorem proved!

**Results**:
- [x] **PROVED `fq_closed_in_fullAdeles`** (~70 lines) - The closedness theorem!
- [x] Proved T2Space for `FqtInfty Fq` via `IsTopologicalAddGroup.t2Space_of_zero_sep`
- [x] Proved T2Space for `FiniteAdeleRing` via `T2Space.of_injective_continuous` + `DFunLike.coe_injective`
- [x] Used `Prod.t2Space` for full adeles = FiniteAdeleRing × FqtInfty
- [x] Applied `AddSubgroup.isClosed_of_discrete` to get closedness from discreteness

**Key Proof Techniques**:

1. **T2Space for valued fields**: Used `IsTopologicalAddGroup.t2Space_of_zero_sep` with Valued structure
   - For each x ≠ 0, the set `{k | Valued.v k < Valued.v x}` separates 0 from x
   - This is a neighborhood of 0 (via `Valued.mem_nhds`) not containing x

2. **T2Space for FiniteAdeleRing**: Used `T2Space.of_injective_continuous` with
   - `DFunLike.coe_injective` for injectivity of embedding into Pi type
   - `RestrictedProduct.continuous_coe` for continuity

3. **Transfer discrete topology**: Used `SetLike.isDiscrete_iff_discreteTopology` to convert
   between `DiscreteTopology (Set.range f)` and `DiscreteTopology (Subring.range.toAddSubgroup)`

**Key Mathlib Lemmas Used**:
- `IsTopologicalAddGroup.t2Space_of_zero_sep` - T2 via separation at 0
- `Valued.mem_nhds` - neighborhood basis in valued rings
- `T2Space.of_injective_continuous` - T2 from injection into T2 space
- `DFunLike.coe_injective` - RestrictedProduct → Pi is injective
- `RestrictedProduct.continuous_coe` - embedding is continuous
- `Prod.t2Space` - product of T2 is T2
- `AddSubgroup.isClosed_of_discrete` - discrete subgroups are closed in T2 spaces
- `SetLike.isDiscrete_iff_discreteTopology` - discrete topology transfer

**Sorry Status**:
- FullAdeles.lean: 2 sorries (compactness, weak approx) - down from 3!

**Build**: ✅ Compiles successfully

**Next Steps** (Cycle 132+):
1. Prove `isCompact_integralFullAdeles` - product of compact sets
2. Prove `exists_translate_in_integralFullAdeles` - weak approximation for PIDs

---

#### Cycle 133 - Infinity Compactness Structure (Blocked on Tactic Issues)

**Goal**: Complete infinity compactness proof for `isCompact_integralFullAdeles`.

**Status**: 🔶 PARTIAL - Structure complete, blocked on ℝ≥0 literal proofs

**Results**:
- [x] Added imports: `Mathlib.Data.Int.WithZero`, `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- [x] Wrote `inftyValuation_isNontrivial` theorem (commented out - blocked)
- [x] Wrote `instRankOneFqtInfty` instance structure (commented out - blocked)
- [x] Documented full proof strategy following `AllIntegersCompactProof.compactSpace_adicCompletionIntegers`
- [x] Added detailed TODO section in code for next Claude

**Blocking Issue**: The ℝ≥0 literal proofs like `(2 : ℝ≥0) ≠ 0` and `(1 : ℝ≥0) < 2` fail with:
- `norm_num` generates `sorry ()` garbage
- `native_decide` fails ("failed to synthesize OfNat Type 0")
- Need to use `NNReal.coe_lt_coe.mp (by norm_num : (1:ℝ) < 2)` or similar coercion trick

**Proof Strategy Documented** (in FullAdeles.lean comments):

1. **RankOne instance**:
   ```lean
   instance instRankOneFqtInfty : Valuation.RankOne (Valued.v (R := FqtInfty Fq)) where
     toIsNontrivial := inftyValuation_isNontrivial Fq
     hom := WithZeroMulInt.toNNReal h2  -- where h2 : (2 : ℝ≥0) ≠ 0
     strictMono' := WithZeroMulInt.toNNReal_strictMono h1  -- where h1 : (1 : ℝ≥0) < 2
   ```

2. **Nontriviality**: Show `v(X) = exp(1) ≠ 0, 1` using `Valued.extension_extends`

3. **Compactness** (same pattern as `AllIntegersCompactProof.lean`):
   - CompleteSpace: `Valued.integer` is closed in complete space
   - DVR: value group is ℤ (discrete)
   - Finite residue field: isomorphic to Fq
   - Apply `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`

**Sorry Status**:
- FullAdeles.lean: 2 sorries (infinity compactness, weak approx)

**Build**: ✅ Compiles successfully with 2 sorries

**Next Steps** (Cycle 134+):
1. Fix ℝ≥0 literal proofs using coercion from ℝ
2. Uncomment and complete RankOne instance
3. Complete infinity compactness proof
4. Start weak approximation

---

#### Cycle 132 - PARTIAL: Finite Adeles Compactness Proved

**Goal**: Prove `isCompact_integralFullAdeles` - compactness of integral full adeles.

**Status**: 🔶 PARTIAL - Finite adeles part proved, infinity component needs more work

**Results**:
- [x] **PROVED finite adeles compactness** using `RestrictedProduct.range_structureMap`
  - Showed `{a ∈ FiniteAdeleRing | ∀ v, a.val v ∈ O_v} = range(structureMap)`
  - Used `isCompact_range` + `isEmbedding_structureMap.continuous`
  - Each `O_v` compact from `AllIntegersCompact`
- [x] Structured proof with `IsCompact.prod` for final combination
- [x] Documented requirements for infinity component

**Key Proof Techniques**:

1. **Finite adeles as range of structureMap**:
   ```lean
   have hrange : integralFin = Set.range (RestrictedProduct.structureMap R' A' Filter.cofinite) := by
     ext a
     rw [RestrictedProduct.range_structureMap]
     rfl
   ```

2. **Compactness from embedding**:
   ```lean
   exact isCompact_range (RestrictedProduct.isEmbedding_structureMap.continuous)
   ```
   - `isEmbedding_structureMap` gives continuous embedding from `Π v, O_v`
   - `Π v, O_v` is compact via `Pi.compactSpace` (Tychonoff)
   - Image of compact under continuous is compact

**Remaining Sorry - Infinity Component**:

For `{x : FqtInfty Fq | Valued.v x ≤ 1}` to be compact, need:
1. `RankOne` instance for `Valued.v` on `FqtInfty Fq`
2. `CompleteSpace (Valued.integer (FqtInfty Fq))`
3. `IsDiscreteValuationRing` for integer ring
4. `Finite` residue field

Then use `Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`

**Key Mathlib Lemmas Used**:
- `RestrictedProduct.range_structureMap` - identifies integral adeles
- `RestrictedProduct.isEmbedding_structureMap` - embedding property
- `isCompact_range` - image of compact under continuous is compact
- `AllIntegersCompact.compact` - each O_v is compact
- `IsCompact.prod` - product of compact sets

**Sorry Status**:
- FullAdeles.lean: 2 sorries (1 partial = infinity sorry, 1 full = weak approx)

**Build**: ✅ Compiles successfully

**Next Steps** (Cycle 133+):
1. Establish `RankOne` instance for `FqtInfty Fq` (need ℤᵐ⁰ →*₀ ℝ≥0)
2. Complete infinity compactness proof
3. Start weak approximation `exists_translate_in_integralFullAdeles`

---

#### Cycle 129 - Helper Lemmas Proved, Discreteness Proof In Progress

**Goal**: Fill the helper lemmas connecting diagonal embedding to valuations, complete discreteness proof.

**Status**: 🔶 PARTIAL - Helper lemmas proved, main proof structure complete but has technical issue

**Results**:
- [x] **PROVED `diag_integral_implies_valuation_le`**: Connects finite component membership to valuation bound
  - Uses `valuedAdicCompletion_eq_valuation'` from Mathlib
  - Key insight: `(fqFullDiagonalEmbedding Fq d).1.1 v = (d : v.adicCompletion K)` by rfl
- [x] **PROVED `diag_infty_valuation`**: Connects infinity component to `inftyValuationDef`
  - Uses `valuedFqtInfty.def` + `Valued.extension_extends`
  - Shows `Valued.v ((fqFullDiagonalEmbedding Fq d).2) = inftyValuationDef Fq d`
- [x] Wrote complete proof structure for `fq_discrete_in_fullAdeles` (documented in code)

**Key Proofs**:
```lean
theorem diag_integral_implies_valuation_le (d : RatFunc Fq) (v : HeightOneSpectrum Fq[X])
    (h : (fqFullDiagonalEmbedding Fq d).1.1 v ∈ v.adicCompletionIntegers (RatFunc Fq)) :
    v.valuation (RatFunc Fq) d ≤ 1 := by
  rw [mem_adicCompletionIntegers] at h
  have heq : (fqFullDiagonalEmbedding Fq d).1.1 v = (d : v.adicCompletion (RatFunc Fq)) := rfl
  rw [heq, valuedAdicCompletion_eq_valuation'] at h
  exact h

theorem diag_infty_valuation (d : RatFunc Fq) :
    Valued.v ((fqFullDiagonalEmbedding Fq d).2) = FunctionField.inftyValuationDef Fq d := by
  have heq : (fqFullDiagonalEmbedding Fq d).2 = inftyRingHom Fq d := rfl
  rw [heq, FunctionField.valuedFqtInfty.def]
  simp only [inftyRingHom]
  letI : Valued (RatFunc Fq) (WithZero (Multiplicative ℤ)) := FunctionField.inftyValuedFqt Fq
  convert Valued.extension_extends (K := RatFunc Fq) d using 2
```

**Remaining Issue**:
- `fq_discrete_in_fullAdeles` proof structure is complete but has a technical issue:
  - Need to use `subst hm` instead of `rw [hm]` when substituting `a = fqFullDiagonalEmbedding Fq m`
  - The goal structure after simp doesn't allow direct rewrite

**Remaining Sorries in FullAdeles.lean** (4 total):
| Sorry | Description | Difficulty |
|-------|-------------|------------|
| `fq_discrete_in_fullAdeles` | Main discreteness (structure complete) | Easy (technical fix) |
| `fq_closed_in_fullAdeles` | Discrete + T2 → closed | Easy |
| `isCompact_integralFullAdeles` | Product of compacts | Medium |
| `exists_translate_in_integralFullAdeles` | Weak approximation | Medium |

**Build**: ✅ Compiles successfully

**Next Steps** (Cycle 130+):
1. Fix `fq_discrete_in_fullAdeles` using `subst` or restructure proof
2. Complete `fq_closed_in_fullAdeles` using discreteness + T2

---

#### Cycle 123 - Concrete Fq[X] Instance for Full Adeles

**Goal**: Implement the concrete instance of `FullDiscreteCocompactEmbedding` for `Polynomial Fq / RatFunc Fq / FqtInfty Fq`.

**Status**: ✅ COMPLETE (instance structure with sorries for deep proofs)

**Results**:
- [x] Added `Nonempty (HeightOneSpectrum Fq[X])` instance (X is irreducible)
- [x] Defined `FqFullAdeleRing Fq` type alias
- [x] Defined `inftyRingHom : RatFunc Fq →+* FqtInfty Fq` via `coeRingHom`
- [x] Created `instAlgebraRatFuncFqtInfty` from ring hom
- [x] Defined `fqFullDiagonalEmbedding` into full adeles
- [x] Proved `fqFullDiagonalEmbedding_injective`
- [x] Defined `integralFullAdeles` using `Valued.v` for infinity valuation
- [x] Created `instFullDiscreteCocompactEmbedding` for Fq[X]

**Key Technical Challenges Resolved**:

1. **Algebra Instance**: Mathlib doesn't directly provide `Algebra (RatFunc Fq) (FqtInfty Fq)`.
   Constructed via `inftyRingHom.toAlgebra` where `inftyRingHom` uses `coeRingHom` with
   explicit valued structure: `letI : Valued (RatFunc Fq) (WithZero (Multiplicative ℤ)) := FunctionField.inftyValuedFqt Fq`

2. **Height-One Primes**: Proved `Nonempty (HeightOneSpectrum Fq[X])` by showing `X` is irreducible,
   hence `(X)` is a height-one prime.

3. **Valuation on Completion**: Used `Valued.v` (not `inftyValuation` directly) for elements of `FqtInfty Fq`.

**Remaining Sorries** (5 in FullAdeles.lean):

| Sorry | Mathematical Content | Difficulty |
|-------|---------------------|------------|
| `algebraMap_FqtInfty_injective` | `coeRingHom` = `Completion.coe'` | Easy (definitional) |
| `fq_discrete_in_fullAdeles` | `|k|_∞ = q^{deg k}` bounds degree | Medium (KEY) |
| `fq_closed_in_fullAdeles` | Discrete + LCH → closed | Easy (standard) |
| `isCompact_integralFullAdeles` | Product of compacts | Medium |
| `exists_translate_in_integralFullAdeles` | Weak approximation for PIDs | Medium |

**Key Insight for Discreteness Proof**:
- For polynomials: `|k|_∞ = q^{deg k}` (infinity valuation = negated degree)
- If `|k|_∞ ≤ ε` (small), then `deg k ≤ -log_q(ε)` (bounded)
- Finitely many polynomials over finite field with bounded degree
- Combined with integrality at finite places → finite intersection with neighborhoods

**Sorry Status**:
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)
- FqPolynomialInstance.lean: 4 sorries (1 FALSE, 3 finite adeles related)
- FullAdeles.lean: 5 sorries (concrete proofs)

**Total**: 10 sorries in proof path

**Build**: ✅ Compiles successfully

**Next Steps** (Cycle 124+):
1. Fill `algebraMap_FqtInfty_injective` (should be definitional equality)
2. Fill `fq_discrete_in_fullAdeles` using degree bound argument
3. Fill remaining compactness/approximation sorries
4. Audit `AdelicH1v2.lean` for migration to full adeles

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
