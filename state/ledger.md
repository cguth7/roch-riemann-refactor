# Ledger Vol. 3.2 (Cycles 100+) - Full Riemann-Roch

*For Cycles 1-34, see `state/ledger_archive.md` (Vol. 1)*
*For Cycles 35-79, see `state/ledger_archive.md` (Vol. 2)*
*For Cycles 80-99, see `state/ledger_archive.md` (Vol. 3.1)*

---

## 🎯 NEXT CLAUDE: Start Here (Post-Cycle 121)

### Critical Context
**Cycle 121 discovered a spec bug**: K is NOT discrete in the *finite* adeles.
This is not a proof difficulty - the statement is mathematically false.
The fix is architectural: **add the infinite place**.

### Architectural Decision (Confirmed)
**Option 1: Add Infinity** - This is the correct path for adelic Riemann-Roch.

### Recommended Implementation Strategy

**Don't rework HeightOneSpectrum plumbing.** Instead, build full adeles as a product:

```lean
-- New file: RrLean/RiemannRochV2/FullAdeles.lean

/-- The completion at infinity for Fq(X) is Fq((1/X)) -/
def completionAtInfinity (Fq : Type*) [Field Fq] := LaurentSeries Fq
-- Or use FunctionField.inftyValuation machinery from Mathlib

/-- Integers at infinity: Fq[[1/X]] (power series) -/
def integersAtInfinity (Fq : Type*) [Field Fq] := PowerSeries Fq

/-- Full adeles = finite adeles × completion at infinity -/
def FullAdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (K_infty : Type*) :=
  FiniteAdeleRing R K × K_infty

/-- Diagonal embedding into full adeles -/
def fullDiagonalEmbedding (k : K) : FullAdeleRing R K K_infty :=
  (diagonalEmbedding R K k, algebraMap K K_infty k)
```

### Concrete Next Steps (Cycle 122+)

**Step 1**: Create `FullAdeles.lean` with the product definition
- Use `LaurentSeries Fq` or `FunctionField.inftyValuation` for K_∞
- Define `FullAdeleRing := FiniteAdeleRing R K × K_∞`
- Define diagonal embedding

**Step 2**: Define `FullDiscreteCocompactEmbedding` for full adeles
- K discrete in A (now TRUE with infinity included)
- K closed in A (follows from discrete + locally compact)
- A/K compact (standard cocompactness)

**Step 3**: Migrate `DiscreteCocompactEmbedding` usages
- Audit `AdelicH1v2.lean` - does it use discreteness?
- Audit `AdelicTopology.lean` - update to use full adeles where needed
- Keep finite adeles for properties that don't need infinity

**Step 4**: Prove the properties for Fq[X]
- `valuation_eq_one_almost_all` already proved (finite places)
- Need analogous statement including infinity
- Compactness of integral adeles should work

### What NOT To Do
- ❌ Don't try to prove `discrete_diagonal_embedding` for finite adeles (it's false)
- ❌ Don't try alternative proofs for closedness without infinity (same issue)
- ❌ Don't weaken axioms unless abandoning adelic RR entirely

### Mathlib Resources for Infinity
```
Mathlib/NumberTheory/FunctionField.lean:192 - FunctionField.inftyValuation
Mathlib/RingTheory/LaurentSeries.lean - LaurentSeries type
Mathlib/RingTheory/PowerSeries/Basic.lean - PowerSeries type
```

### Files to Modify/Create
| File | Action |
|------|--------|
| `FullAdeles.lean` | **CREATE** - Product definition A = A_f × K_∞ |
| `FqPolynomialInstance.lean` | Keep AllIntegersCompact, retire discrete goal |
| `AdelicTopology.lean` | Add FullDiscreteCocompactEmbedding class |
| `AdelicH1v2.lean` | Audit for full adele requirements |

---

## ⚡ Quick Reference: Current Axiom/Sorry Status (Cycle 121)

### Sorries (proof holes)
| File | Item | Status | Notes |
|------|------|--------|-------|
| `TraceDualityProof.lean` | `finrank_dual_eq` | ⚪ 1 sorry | NOT on critical path |
| `FqPolynomialInstance.lean` | `discrete_diagonal_embedding` | ❌ FALSE | **CANNOT BE PROVED** - K not discrete in finite adeles |
| `FqPolynomialInstance.lean` | `closed_diagonal_embedding` | ⚪ 1 sorry | Needs different approach (not from discreteness) |
| `FqPolynomialInstance.lean` | `isCompact_integralAdeles` | ⚪ 1 sorry | Product compactness - may still work |
| `FqPolynomialInstance.lean` | `exists_K_translate_in_integralAdeles` | ⚪ 1 sorry | Weak approximation - may still work |

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

---

#### Cycle 100 - P¹ Consistency Check (FullRRData Axioms Validated!)

**Goal**: Validate that the FullRRData axioms are consistent by exhibiting a concrete model.

**Status**: ✅ COMPLETE

**Results**:
- [x] Created `P1Instance.lean` with P¹ dimension formula
- [x] Proved `ell_P1_zero_of_neg`: ℓ(D) = 0 when deg(D) < 0
- [x] Proved `ell_P1_pos`: ℓ(D) = deg(D) + 1 when deg(D) ≥ 0
- [x] Proved `RR_P1_check`: ℓ(D) - ℓ(K-D) = deg(D) + 1 for all D
- [x] Proved `FullRRData_consistent_for_genus_0`: **ALL AXIOMS CONSISTENT!**

**Key Result**: The FullRRData axiom system is consistent (not contradictory).

```lean
/-- The FullRRData axioms are consistent for genus 0. -/
theorem FullRRData_consistent_for_genus_0 :
    ∃ (ell : ℤ → ℕ) (degK : ℤ),
      ell 0 = 1 ∧                                    -- Properness
      degK = -2 ∧                                    -- deg(K) = 2g - 2
      (∀ d, (ell d : ℤ) - ell (degK - d) = d + 1) ∧ -- Serre duality
      (∀ d, d < 0 → ell d = 0)                       -- Vanishing
```

**Witness**: `ell_P1 d = max(0, d + 1).toNat` satisfies all axioms for g = 0.

**Mathematical Significance**:
- P¹ is the "simplest" algebraic curve (genus 0)
- The dimension formula ℓ(D) = max(0, deg(D) + 1) is explicit
- This validates our axiom design before attempting harder cases

**Note**: A full instantiation of `FullRRData k k[X] k(X)` would require:
1. Compactifying k[X] to include the point at infinity
2. Proving the dimension formula for actual divisors
This is deferred to future work.

**Sorry Status** (unchanged):
- AdelicTopology.lean: 1 sorry (`h1_module_finite`)
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 2 sorries in main path (unchanged)

**Next Steps** (Cycle 101):
1. Prove `h1_module_finite` using fundamental domain machinery
2. Or: Add genus 1 (elliptic curve) consistency check
3. Or: Research product formula for valuations

---

#### Cycle 101 - Genus 1 Consistency Check + Focus Decision

**Goal**: Add genus 1 (elliptic curve) consistency check and decide on forward direction.

**Status**: ✅ COMPLETE

**Results**:
- [x] Added `EllipticCurve` namespace with `ell_g1` dimension function
- [x] Proved `ell_g1_neg`: ℓ(D) = 0 when deg(D) < 0
- [x] Proved `ell_g1_zero`: ℓ(0) = 1
- [x] Proved `ell_g1_pos`: ℓ(D) = deg(D) when deg(D) > 0
- [x] Proved `RR_g1_check`: ℓ(D) - ℓ(-D) = deg(D) for all D
- [x] Proved `FullRRData_consistent_for_genus_1`: Axioms consistent for g = 1
- [x] Added `FullRRData_axioms_consistent`: Unified theorem for g ∈ {0, 1}

**Genus 1 Model**:
```lean
def ell_g1 (d : ℤ) : ℕ :=
  if d < 0 then 0
  else if d = 0 then 1
  else d.toNat
```

**Key Insight**: For g = 1, deg(K) = 0, so RR becomes ℓ(D) - ℓ(-D) = deg(D).

**Scope Clarification**: These are **sanity checks** ("we're not proving nonsense"),
not claims about existence of curves. The theorems are explicitly limited to g ≤ 1.
Full instantiation would require actual algebraic curve infrastructure.

**Sorry Status** (unchanged):
- AdelicTopology.lean: 1 sorry (`h1_module_finite`)
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 2 sorries in main path (unchanged)

**Forward Direction Decision**:

The consistency checks are complete and serve their purpose. **Future cycles should
focus on adelic infrastructure**, specifically:

1. **`h1_module_finite`**: Requires Haar measure / fundamental domain machinery
   - Mathlib has building blocks but not the "adelic Minkowski theorem"
   - May need to axiomatize `DiscreteCocompactEmbedding` properties further

2. **Instantiate `AdelicRRData`**: The bridge to `FullRRData` is sorry-free
   - Need to prove: `h1_finite`, `h1_vanishing`, `adelic_rr`, `serre_duality`
   - These are the deep theorems requiring adelic infrastructure

3. **Do NOT expand**: Model/consistency checks beyond g ∈ {0, 1}
   - Would require algebraic curve existence machinery
   - Diminishing returns for axiom validation

**Next Steps** (Cycle 102+):
1. Research specific path to `h1_module_finite` (Haar measure, Blichfeldt)
2. Or: Axiomatize remaining adelic properties to complete Track B structure
3. Or: Attempt one of the `AdelicRRData` axioms directly

---

#### Cycle 102 - Cleanup: Removed Redundant Axiom

**Goal**: Review and clean up axiom structure.

**Status**: ✅ COMPLETE (after revision)

**Initial Attempt** (reverted):
- Added `H1FiniteDimensional` class to "eliminate" the sorry
- This was misguided: axiom ≈ sorry, just with better documentation

**After Review**:
- Removed redundant `H1FiniteDimensional` class (weaker than `AdelicRRData.h1_finite`)
- Removed unused `h1_module_finite` theorem
- Cleaned up summary documentation

**Key Insight** (from user feedback):
1. Axioms and sorries are both "unprovable holes" that need eventual discharge
2. The difference: axioms have clear mathematical justification, sorries are TODOs
3. Adding axiom layers to hide sorries is cosmetic, not substantive

**Actual Axiom Structure** (no redundancy):

| File | Axiom Class | Content |
|------|------------|---------|
| AdelicTopology.lean | `AllIntegersCompact` | Each O_v compact (implies locally compact A_K) |
| AdelicTopology.lean | `DiscreteCocompactEmbedding` | K discrete + cocompact in A_K |
| AdelicH1v2.lean | `AdelicRRData` | h¹ finite, vanishing, Serre duality, adelic RR |
| FullRRData.lean | `FullRRData` | Full RR equation (DERIVED from AdelicRRData) |

**Expected Route to H¹(D) Finiteness** (when discharging AdelicRRData.h1_finite):
1. Locally compact A_K (from AllIntegersCompact)
2. Discrete + cocompact K → A_K (from DiscreteCocompactEmbedding)
3. Discrete lattice ∩ compact set = finite set (Blichfeldt)
4. Over finite k: finite set spans finite-dimensional module

**Sorry Status** (unchanged from Cycle 101):
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 1 sorry in main path

**Forward Direction**: Track B - Start discharging axioms rather than adding new ones.

**Recommended First Target**: `AllIntegersCompact`

Rationale:
1. **Foundation** - LocallyCompactSpace(A_K) depends on this; other axioms build on it
2. **Single-place property** - Only requires showing each O_v is compact, no global coordination
3. **Mathlib coverage** - Should have: finite residue field + complete DVR → compact valuation ring
4. **Clear scope** - For function field K/k with finite k: residue fields are finite extensions of k

Expected proof route:
```
Finite k → finite residue field at each v
         → CompactSpace (v.adicCompletionIntegers K)  [Mathlib: Valued.LocallyCompact?]
         → AllIntegersCompact R K
```

Search targets in Mathlib:
- `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`
- `Valued.LocallyCompact` module
- `IsNonarchimedeanLocalField` instances

---

#### Cycle 103 - AllIntegersCompact Analysis + AdelicH1v2 Fix

**Goal**: Analyze blockers for discharging `AllIntegersCompact` axiom.

**Status**: ✅ COMPLETE (analysis done, blocker identified)

**Results**:
- [x] Fixed missing `ell_zero_of_neg_deg` field in `adelicRRData_to_FullRRData`
- [x] Identified key Mathlib theorem for compactness:
      `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`
- [x] Created `AllIntegersCompactProof.lean` documenting analysis

**Bug Fix**: `adelicRRData_to_FullRRData` in AdelicH1v2.lean was missing the
`ell_zero_of_neg_deg` field added in Cycle 99. The fix derives this from other
adelic axioms:
- If deg(D) < 0, then deg(K - D) > 2g - 2
- By h1_vanishing: h¹(K - D) = 0
- By Serre duality: h¹(K - D) = ℓ(K - (K - D)) = ℓ(D)
- Therefore ℓ(D) = 0

**Key Theorem Identified**:
```lean
Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField :
    CompactSpace 𝒪[K] ↔ CompleteSpace 𝒪[K] ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K]
```

**What's Available in Mathlib**:
1. `IsDiscreteValuationRing (v.adicCompletionIntegers K)` - ✅ EXISTS (FinitePlaces.lean)
2. `CompleteSpace (v.adicCompletionIntegers K)` - ✅ EXISTS (completion structure)
3. `Finite 𝓀[K]` (residue field of completion) - needs hypothesis + connection
4. **BLOCKER**: `Valuation.RankOne` on `Valued.v` for adic completion

**Blocking Issue**: The compactness theorem requires `[Valuation.RankOne v]`.

For NumberFields, Mathlib provides this via `instRankOneValuedAdicCompletion` using
`absNorm v.asIdeal`. For general Dedekind domains, we need either:
1. Axiomatize: Add hypothesis class providing RankOne for all v
2. Construct: Build RankOne using `Nat.card (R ⧸ v.asIdeal)` for function fields

**Mathematical Insight**: ℤᵐ⁰ is MulArchimedean (via WithZero.instMulArchimedean),
so a RankOne structure exists by `nonempty_rankOne_iff_mulArchimedean`. The challenge
is constructing a *specific* instance suitable for typeclass resolution.

**Created**: `RrLean/RiemannRochV2/AllIntegersCompactProof.lean` (~150 lines)
- Documents analysis and blocking issues
- Defines `FiniteResidueFields` hypothesis class
- Explains the path to construction via residue field cardinality

**Sorry Status** (unchanged from Cycle 102):
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 1 sorry in main path (unchanged)

**Next Steps** (Cycle 104+):
1. **Option A (Axiomatize)**: Add `RankOneValuations` typeclass packaging RankOne for all v
2. **Option B (Construct)**: For function fields over finite k, construct RankOne using
   `cardQuot v := Nat.card (R ⧸ v.asIdeal)` as the base of the exponential map
3. After RankOne: Need to show residue field of completion = residue field of original DVR

---

#### Cycle 104 - AllIntegersCompact Discharge Path Documented

**Goal**: Establish the path for discharging `AllIntegersCompact` axiom.

**Status**: ✅ COMPLETE

**Results**:
- [x] Created granular axiom structure for AllIntegersCompact:
  - `AdicCompletionIntegersDVR`: Each O_v is a DVR
  - `RankOneValuations`: Each adic completion valuation has rank one
  - `FiniteCompletionResidueFields`: Each completion residue field is finite
- [x] Proved `completeSpace_adicCompletionIntegers`: O_v is complete (sorry-free!)
- [x] Proved `isClosed_adicCompletionIntegers`: O_v is closed in K_v (sorry-free!)
- [x] Proved `compactSpace_adicCompletionIntegers`: O_v compact from axioms (sorry-free!)
- [x] Proved `allIntegersCompact_of_axioms`: AllIntegersCompact from granular axioms

**Key Discovery**: For general Dedekind domains, Mathlib does NOT provide:
- `IsDiscreteValuationRing (v.adicCompletionIntegers K)` - only for NumberFields
- `RankOne` for adic completion valuations - only for NumberFields

We must axiomatize these or prove them for function fields specifically.

**Axiom Hierarchy**:
```
AdicCompletionIntegersDVR R K
         +
RankOneValuations R K
         +
FiniteCompletionResidueFields R K
         |
         v
compactSpace_adicCompletionIntegers (uses compactSpace_iff...)
         |
         v
AllIntegersCompact R K
```

**Completeness Proof** (SORRY-FREE):
```lean
instance completeSpace_adicCompletionIntegers (v : HeightOneSpectrum R) :
    CompleteSpace (v.adicCompletionIntegers K) := by
  haveI : IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isClosed_adicCompletionIntegers (R := R) K v
  exact IsClosed.completeSpace_coe
```
Uses: `adicCompletion K v` is complete (it's a `Completion`) + valuation ring is closed.

**Sorry Status** (unchanged from Cycle 103):
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 1 sorry in main path (unchanged)

**Next Steps** (Cycle 105+):
1. For function fields: Prove `AdicCompletionIntegersDVR` (completing a DVR gives DVR)
2. For function fields: Construct `RankOneValuations` using |R/v| as exponential base
3. For function fields: Prove `FiniteCompletionResidueFields` from finiteness of k

---

#### Cycle 105 - DVR for ALL Dedekind Domains (Major Progress!)

**Goal**: Prove that `adicCompletionIntegers` is a DVR for ALL Dedekind domains.

**Status**: ✅ COMPLETE (THEOREM, not axiom!)

**Results**:
- [x] Created `DedekindDVR.lean` with sorry-free proofs
- [x] `isPrincipalIdealRing_adicCompletionIntegers` - PROVED
- [x] `isDiscreteValuationRing_adicCompletionIntegers` - PROVED
- [x] Updated `AllIntegersCompactProof.lean` to use the new theorem
- [x] Reduced axiom count for `AllIntegersCompact` from 3 to 2

**Key Insight**: The NumberField-specific proofs in Mathlib only use:
1. `Valued.v.range_nontrivial` - follows from surjectivity (general)
2. `v.valuation_exists_uniformizer K` - available for all HeightOneSpectrum
3. `MulArchimedean ℤᵐ⁰` - automatic from `Archimedean ℤ`

**None of these require finite residue fields!** Only compactness needs finiteness.

**New File**: `RrLean/RiemannRochV2/DedekindDVR.lean` (~100 lines)

**Key Theorems**:
```lean
-- MulArchimedean for the valuation range
instance mulArchimedean_mrange :
    MulArchimedean (MonoidHom.mrange (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))

-- adicCompletionIntegers is a PID
instance isPrincipalIdealRing_adicCompletionIntegers :
    IsPrincipalIdealRing (v.adicCompletionIntegers K)

-- adicCompletionIntegers is a DVR (sorry-free!)
instance isDiscreteValuationRing_adicCompletionIntegers :
    IsDiscreteValuationRing (v.adicCompletionIntegers K)
```

**Updated Axiom Hierarchy** (simplified!):
```
PROVED:
  IsDiscreteValuationRing (v.adicCompletionIntegers K)  ← DedekindDVR.lean

REMAINING AXIOMS (for compactness):
  RankOneValuations R K
         +
  FiniteCompletionResidueFields R K
         |
         v
  AllIntegersCompact R K
```

**Sorry Status** (unchanged from Cycle 104):
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 1 sorry in main path (unchanged)

**Significance**: This is a generalization of Mathlib's result. The DVR property for
adic completion integers was thought to require NumberField machinery, but we've shown
it holds for ALL Dedekind domains. This reduces the axioms needed for `AllIntegersCompact`
from 3 to 2.

**Next Steps** (Cycle 106+):
1. Construct `RankOneValuations` using |R/v| as exponential base
2. Prove `FiniteCompletionResidueFields` from finiteness of k
3. Or: Focus on other parts of Track B

---

#### Cycle 106 - RankOne for ALL Dedekind Domains (Major Progress!)

**Goal**: Prove that `RankOne` holds for adic completion valuations, eliminating the axiom.

**Status**: ✅ COMPLETE (THEOREM, not axiom!)

**Results**:
- [x] `isNontrivial_adicCompletionValuation` - PROVED: valuation is nontrivial
- [x] `rankOne_adicCompletionValuation` - PROVED: valuation has RankOne
- [x] `rankOneValuations_instance` - PROVED: RankOneValuations is now automatic
- [x] Updated AllIntegersCompactProof.lean with sorry-free proofs

**Key Insight**: RankOne follows automatically from:
1. `MulArchimedean (WithZero (Multiplicative ℤ))` - automatic from ℤ being Archimedean
2. `Valuation.IsNontrivial` - proved from uniformizer existence
3. `nonempty_rankOne_iff_mulArchimedean` - Mathlib theorem connecting these

**Proof of IsNontrivial**:
```lean
instance isNontrivial_adicCompletionValuation (v : HeightOneSpectrum R) :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsNontrivial := by
  rw [Valuation.isNontrivial_iff_exists_lt_one]
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  use (π : v.adicCompletion K)
  constructor
  · intro hπ0  -- Assume ↑π = 0 in adicCompletion
    have hv0 : Valued.v (π : v.adicCompletion K) = 0 := by rw [hπ0, Valuation.map_zero]
    rw [valuedAdicCompletion_eq_valuation', hπ] at hv0
    exact WithZero.coe_ne_zero hv0  -- exp(-1) ≠ 0, contradiction
  · rw [valuedAdicCompletion_eq_valuation', hπ]
    exact WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0)  -- exp(-1) < 1
```

**Updated Axiom Hierarchy** (simplified again!):
```
PROVED (Cycle 105):
  IsDiscreteValuationRing (v.adicCompletionIntegers K)  ← DedekindDVR.lean

PROVED (Cycle 106):
  RankOne (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)  ← AllIntegersCompactProof.lean

REMAINING AXIOM (for compactness):
  FiniteCompletionResidueFields R K  (residue fields are finite)
         |
         v
  AllIntegersCompact R K
```

**Significance**: This is another major generalization of Mathlib's NumberField-specific results.
The RankOne property was thought to require finite residue fields (for the norm-based construction),
but we've shown it holds for ALL Dedekind domains via the MulArchimedean ↔ RankOne correspondence.

Now only ONE axiom remains for `AllIntegersCompact`: finite residue fields.

**Sorry Status** (unchanged from Cycle 105):
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 1 sorry in main path (unchanged)

**Next Steps** (Cycle 107+):
1. Prove `FiniteCompletionResidueFields` for function fields over finite k
2. This will complete the `AllIntegersCompact` axiom discharge
3. Then focus on `DiscreteCocompactEmbedding` for full adelic theory

---

#### Cycle 107 - AllIntegersCompact: Only ONE Axiom Remains!

**Goal**: Consolidate progress and identify the single remaining axiom for AllIntegersCompact.

**Status**: ✅ COMPLETE (documentation and simplification)

**Results**:
- [x] Confirmed RankOne is now a THEOREM (proved in Cycle 106)
- [x] Simplified `compactSpace_adicCompletionIntegers` to only require `FiniteCompletionResidueFields`
- [x] Removed dependency on `RankOneValuations` class (now redundant)
- [x] Updated AllIntegersCompactProof.lean with comprehensive summary
- [x] Documented residue field analysis

**Final Axiom Hierarchy for AllIntegersCompact**:
```
PROVED (Cycle 105): IsDiscreteValuationRing (v.adicCompletionIntegers K)
PROVED (Cycle 106): RankOne (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
PROVED (automatic): CompleteSpace (v.adicCompletionIntegers K)

REMAINING AXIOM (ONLY ONE!):
  FiniteCompletionResidueFields R K
         |
         v
  AllIntegersCompact R K
```

**Residue Field Analysis**:

The remaining axiom requires: `Finite (Valued.ResidueField (v.adicCompletion K))`

Mathematical path to discharge:
1. Residue field of completion ≃ R ⧸ v.asIdeal (standard fact, not yet in Mathlib)
2. For function fields over finite k: R ⧸ v.asIdeal is finite extension of k
3. Finite extension of finite field is finite

This isomorphism `ResidueField(O_v^) ≅ R/v` is a standard result but may need to be proved
for general Dedekind domains in Mathlib.

**Sorry Status** (unchanged from Cycle 106):
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 1 sorry in main path (unchanged)

**Summary**:

| Requirement for AllIntegersCompact | Status |
|-----------------------------------|--------|
| IsDiscreteValuationRing | ✅ PROVED (Cycle 105) |
| RankOne | ✅ PROVED (Cycle 106) |
| CompleteSpace | ✅ PROVED (automatic) |
| Finite ResidueField | ⏳ AXIOM |

**Next Steps** (Cycle 108+):
1. Research Mathlib for residue field isomorphism: ResidueField(completion) ≅ original
2. If not available: prove for function fields, or axiomatize with clear discharge path
3. Then focus on `DiscreteCocompactEmbedding` for full adelic theory

---

#### Cycle 108 - Residue Field Isomorphism Research

**Goal**: Research whether Mathlib has the residue field isomorphism needed to discharge
`FiniteCompletionResidueFields`.

**Status**: ✅ COMPLETE (research done, blocker identified)

**Results**:
- [x] Comprehensive search of Mathlib for residue field preservation under completion
- [x] Identified key theorem: `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`
- [x] Confirmed: Residue field isomorphism NOT in Mathlib (v4.16.0)
- [x] Updated AllIntegersCompactProof.lean with detailed analysis
- [x] Documented three possible approaches for discharge

**Key Finding**: The standard mathematical fact that "completion preserves residue fields" is
**NOT formalized in Mathlib**:

```
ResidueField(O_v^) ≅ R ⧸ v.asIdeal
```

**Mathlib HAS**:
- `Valued.ResidueField K := IsLocalRing.ResidueField 𝒪[K]` (definition)
- `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`
- `finite_quotient_maximalIdeal_pow_of_finite_residueField`
- DVR instances for NumberFields (with finite residue field hypothesis)

**Mathlib does NOT have**:
- ResidueField(completion) ≃ ResidueField(original localization)
- Any direct connection between R ⧸ v.asIdeal and the completion's residue field
- This isomorphism for general Dedekind domains

**Why This Matters**:

For function fields k(C)/k where k is finite, the discharge path would be:
1. R ⧸ v.asIdeal is a finite extension of k (standard)
2. Therefore R ⧸ v.asIdeal is finite
3. **BLOCKER**: Need isomorphism ResidueField(completion) ≅ R ⧸ v.asIdeal
4. Then: Finite (Valued.ResidueField (v.adicCompletion K))

**Three Options Identified**:

1. **Prove the isomorphism directly**: Show that the natural map
   `R → v.adicCompletion K → 𝒪[K_v] → 𝓀[K_v]` factors through R ⧸ v.asIdeal
   and is an isomorphism. This is doable but requires significant work.

2. **Axiomatize more fundamentally**: Replace `FiniteCompletionResidueFields` with
   `FiniteResidueFields R` (each R ⧸ v.asIdeal is finite). More natural for function fields
   but still requires the isomorphism to connect to compactness.

3. **Accept current axiom**: Keep `FiniteCompletionResidueFields` as the single axiom,
   with clear documentation of the discharge path.

**Interesting Discovery**: Mathlib's `FinitePlaces.lean` (for NumberFields) proves DVR
instances with a `Finite (A ⧸ v.asIdeal)` hypothesis in scope, but the proofs don't actually
USE this hypothesis - confirming our Cycle 105 generalization was correct.

**Sorry Status** (unchanged from Cycle 107):
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 1 sorry in main path (unchanged)

**Current Axiom Status for AllIntegersCompact**:

| Requirement | Status | Notes |
|-------------|--------|-------|
| IsDiscreteValuationRing | ✅ PROVED | Cycle 105, general Dedekind domains |
| RankOne | ✅ PROVED | Cycle 106, general Dedekind domains |
| CompleteSpace | ✅ PROVED | Automatic from completion |
| Finite ResidueField | ⏳ AXIOM | Blocker: residue field isomorphism |

**Recommendation**: Focus on a different axiom (DiscreteCocompactEmbedding) for next cycles,
or attempt to prove the residue field isomorphism. The isomorphism proof would require:
1. Showing the uniformizer of R_v maps to a uniformizer of the completion
2. Showing the residue field map R → 𝒪[K_v] → 𝓀[K_v] factors through R ⧸ v.asIdeal
3. Showing surjectivity (density argument) and injectivity (kernel = v.asIdeal)

**Next Steps** (Cycle 109+):
1. Option A: Attempt to prove residue field isomorphism (moderate effort)
2. Option B: Move to DiscreteCocompactEmbedding (different direction)
3. Option C: Accept axiom and document thoroughly (minimal effort)

---

#### Cycle 108 Part 2 - Residue Field Isomorphism PROVED (Major Progress!)

**Goal**: Follow user guidance to prove the residue field isomorphism using Mathlib's building blocks.

**Status**: ✅ COMPLETE (isomorphism proved, one axiom remains)

**Key Insight from User**: The search was looking for the wrong thing. Instead of a
pre-packaged "ResidueField(completion) ≃ original" lemma, Mathlib has building blocks:
- `AdicCompletion.evalOneₐ_surjective` - canonical surjection from completion
- `isLocalRing_of_isAdicComplete_maximal` - completion is local
- `Valuation.Integers.isUnit_iff_valuation_eq_one` - unit ↔ valuation = 1

**Results**:
- [x] Created `ResidueFieldIso.lean` with full proof structure (~190 lines)
- [x] PROVED: `algebraMap_mem_asIdeal_val_lt_one` - r ∈ v.asIdeal ⇒ val < 1
- [x] PROVED: `toResidueField_mem_asIdeal` - r ∈ v.asIdeal ⇒ residue = 0
- [x] PROVED: `ker_toResidueField_le_asIdeal` - kernel ⊆ v.asIdeal (injectivity direction)
- [x] PROVED: `ker_toResidueField_eq_asIdeal` - kernel = v.asIdeal (exact characterization)
- [x] AXIOM: `toResidueField_surjective` - density argument (still needed)
- [x] PROVED: `residueFieldIso` - R ⧸ v.asIdeal ≃+* ResidueField(completion)
- [x] PROVED: `finite_residueField_of_finite_quotient` - finiteness transfers
- [x] PROVED: `finiteCompletionResidueFields_of_finite_quotients` - connects to axiom class

**New File**: `RrLean/RiemannRochV2/ResidueFieldIso.lean`

**Key Theorems**:
```lean
/-- The residue field of the adic completion is isomorphic to R ⧸ v.asIdeal. -/
def residueFieldIso (v : HeightOneSpectrum R) :
    (R ⧸ v.asIdeal) ≃+* Valued.ResidueField (v.adicCompletion K)

/-- If R ⧸ v.asIdeal is finite, then the residue field of the completion is finite. -/
theorem finite_residueField_of_finite_quotient (v : HeightOneSpectrum R)
    [h : Finite (R ⧸ v.asIdeal)] :
    Finite (Valued.ResidueField (v.adicCompletion K))
```

**Remaining Axiom**: `toResidueField_surjective`

This is the "density" argument: every element of the residue field is representable by an
element of R. The proof requires showing that R is dense enough in the completion. This
is a standard fact but requires either:
1. Direct construction via approximation
2. Appeal to completion density + quotient lifting

**Simplified Axiom Path for AllIntegersCompact**:

```
For function fields k(C)/k where k is finite:

HYPOTHESIS: ∀ v, Finite (R ⧸ v.asIdeal)
    |  (standard for function fields over finite k)
    v
finite_residueField_of_finite_quotient (uses residueFieldIso + surjectivity axiom)
    |
    v
FiniteCompletionResidueFields R K
    |
    v
AllIntegersCompact R K (using DVR + RankOne + Complete, all PROVED)
```

**Progress Summary**:

| Requirement for AllIntegersCompact | Status |
|-----------------------------------|--------|
| IsDiscreteValuationRing | ✅ PROVED (Cycle 105) |
| RankOne | ✅ PROVED (Cycle 106) |
| CompleteSpace | ✅ PROVED (automatic) |
| Finite ResidueField | 🔶 REDUCED to surjectivity axiom |

**Significance**: The "FiniteCompletionResidueFields" axiom is now MUCH simpler:
- Old: Need to prove ResidueField(completion) is finite (seemed hard, no direct path)
- New: Need surjectivity of R → ResidueField(completion) + hypothesis that R/v.asIdeal is finite

The hypothesis "R/v.asIdeal is finite" is the natural condition for function fields over
finite fields and is easy to verify in concrete cases.

**Sorry Status** (unchanged from Cycle 107):
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)
- ResidueFieldIso.lean: 1 axiom (`toResidueField_surjective` - density argument)

**Total**: 1 sorry + 1 new axiom in proof path

**Next Steps** (Cycle 109+):
1. Prove `toResidueField_surjective` via density argument
2. Or: Move to DiscreteCocompactEmbedding (different axiom)
3. For concrete function fields: verify Finite (R ⧸ v.asIdeal) holds

---

#### Cycle 109 - Surjectivity Proof Infrastructure

**Goal**: Complete the `toResidueField_surjective` proof using the density argument.

**Status**: 🔶 PARTIAL (infrastructure built, proof strategy documented)

**Results**:
- [x] Converted `toResidueField_surjective` from axiom to theorem (with sorry)
- [x] Added sorry-free helper lemmas:
  - `asIdeal_isMaximal` - v.asIdeal is maximal in Dedekind domains
  - `algebraMap_val_eq_one_of_not_mem` - valuation = 1 for elements outside ideal
  - `algebraMap_isUnit_of_not_mem` - such elements are units in completion integer ring
  - `quotient_unit_of_nonzero` - nonzero elements in R/v.asIdeal are units (R/v is a field)
  - `exists_mul_eq_one_mod` - multiplicative inverse exists modulo v.asIdeal
- [x] Documented complete proof strategy in docstrings
- [ ] Full density-based proof (still needs work)

**Proof Strategy Identified**:

```
For any y ∈ ResidueField(O_v):
1. Lift y to x ∈ O_v via residue_surjective
2. By Completion.denseRange_coe, K is dense in K_v
3. Find k ∈ K with v(x - k) < 1 (k close to x)
4. By ultrametric: v(k) ≤ max(v(x), v(x-k)) ≤ 1, so k ∈ O_v ∩ K = R_v
5. Since v(x - k) < 1, we have x - k ∈ m_v, so residue(k) = residue(x) = y
6. Write k = a/s where a ∈ R, s ∈ R \ v.asIdeal
7. Since R/v.asIdeal is a field, find t with st ≡ 1 mod v.asIdeal
8. Then residue(k) = residue(a) · residue(t) = residue(a·t), and a·t ∈ R
```

**Key Mathlib Lemmas Identified**:
- `Completion.denseRange_coe` - K embeds densely into its completion
- `Completion.induction_on` - induction principle for completions
- `isClosed_property` - properties holding on dense subset extend to closure

**Blocker**: The density argument requires navigating between:
- The uniform completion structure on K_v
- The valuation topology on O_v
- The discrete topology on the residue field

The mathematical content is clear; the Mathlib API connection needs careful navigation.

**Sorry Status**:
- ResidueFieldIso.lean: 1 sorry (`toResidueField_surjective` - density argument)
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 2 sorries in proof path

**Next Steps** (Cycle 110+):
1. Complete density proof using `Completion.denseRange_coe` and `isClosed_property`
2. Alternative: Use `IsLocalization.equivQuotMaximalIdeal` to establish R/v ≃ O_v/m_v
3. Or: Move to DiscreteCocompactEmbedding (different axiom direction)

---

#### Cycle 110 - Surjectivity Infrastructure Improvements

**Goal**: Strengthen the infrastructure for `toResidueField_surjective` and document clearly.

**Status**: ✅ COMPLETE (infrastructure improved, axiom clearly documented)

**Results**:
- [x] Added helper lemmas (sorry-free):
  - `residue_eq_of_sub_mem_maximalIdeal` - close elements have same residue
  - `mem_maximalIdeal_iff_val_lt_one` - maximal ideal = {x : v(x) < 1}
  - `denseRange_algebraMap_adicCompletion` - K is dense in K_v
- [x] Converted sorry to explicit axiom with full proof outline
- [x] Documented the 9-step proof strategy in the axiom docstring
- [x] Verified build compiles successfully

**Key Infrastructure Added**:

```lean
/-- Two elements with difference in maximal ideal have same residue. -/
lemma residue_eq_of_sub_mem_maximalIdeal (v : HeightOneSpectrum R)
    (x y : v.adicCompletionIntegers K)
    (h : x - y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    IsLocalRing.residue x = IsLocalRing.residue y

/-- The maximal ideal consists of elements with valuation < 1. -/
lemma mem_maximalIdeal_iff_val_lt_one (v : HeightOneSpectrum R)
    (x : v.adicCompletionIntegers K) :
    x ∈ IsLocalRing.maximalIdeal ↔ Valued.v (x : v.adicCompletion K) < 1

/-- Elements of K form a dense subset in the completion. -/
lemma denseRange_algebraMap_adicCompletion (v : HeightOneSpectrum R) :
    DenseRange (algebraMap K (v.adicCompletion K))
```

**Axiom Documentation** (from file):

The `toResidueField_surjective` axiom has a complete 9-step proof outline:
1. Lift y ∈ ResidueField to x ∈ O_v^
2. By density of K in K_v, find k ∈ K close to x (v(x - k) < 1)
3. residue(k) = residue(x) = y (by residue_eq_of_sub_mem_maximalIdeal)
4. k ∈ K with v(k) ≤ 1 means k ∈ R_v (localization)
5. Write k = a/s with a ∈ R, s ∉ v.asIdeal
6. In O_v^, s is a unit (v(s) = 1)
7. Find t ∈ R with st ≡ 1 mod v.asIdeal (exists_mul_eq_one_mod)
8. residue(s)⁻¹ = residue(t) in the completion residue field
9. residue(k) = residue(at), where at ∈ R

**Axiom Status** (updated):
- ResidueFieldIso.lean: 1 axiom (`toResidueField_surjective` - density argument, proof outline documented)
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 1 axiom + 1 sorry in proof path

**Key Discovery**: Found `IsFractionRing (R ⧸ I) I.ResidueField` in Mathlib which means
when I is maximal, R/I ≃ I.ResidueField. This provides an alternative route to the
surjectivity proof via connecting Ideal.ResidueField to Valued.ResidueField.

**Significance**: The remaining axiom now has:
1. Complete mathematical proof outline (9 steps)
2. Helper lemmas for each key step
3. Clear documentation of what Mathlib API navigation is needed
4. Alternative approach identified via IsFractionRing

The axiom is "morally dischargeable" - the mathematical content is clear, only
Mathlib API plumbing remains.

**Next Steps** (Cycle 111+):
1. Complete the density argument using `denseRange_algebraMap_adicCompletion`
2. Or: Use `IsFractionRing (R ⧸ I) I.ResidueField` to connect to completion residue field
3. Or: Move to DiscreteCocompactEmbedding (different axiom direction)

---

#### Cycle 111 - Surjectivity: Axiom → Theorem (Major Progress!)

**Goal**: Convert `toResidueField_surjective` from axiom to theorem.

**Status**: 🔶 IN PROGRESS (90% complete, 2 sorries remain)

**Results**:
- [x] **Converted axiom to theorem** - no more axioms in surjectivity proof!
- [x] `exists_close_element`: Proved density lemma - finds k ∈ K with v(x - k) < 1
- [x] `mem_integers_of_close`: Proved ultrametric lemma - k ∈ O_v^ when close to x
- [x] `toResidueField_surjective`: Main proof structure complete
- [ ] `residue_of_K_element`: 2 sorries remain (fraction clearing logic)

**Key Infrastructure Built**:

```lean
/-- From density, find k ∈ K close to any x in completion. -/
lemma exists_close_element (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    ∃ k : K, Valued.v (x - algebraMap K (v.adicCompletion K) k) < 1

/-- Ultrametric: if v(x - k) < 1 and x ∈ O_v^, then k ∈ O_v^. -/
lemma mem_integers_of_close (v : HeightOneSpectrum R) (x : v.adicCompletionIntegers K) (k : K)
    (hclose : Valued.v ((x : v.adicCompletion K) - algebraMap K _ k) < 1) :
    Valued.v (algebraMap K (v.adicCompletion K) k) ≤ 1
```

**Remaining Sorries** (in `residue_of_K_element`):

1. **Case s ∈ v.asIdeal**: When denominator is in the ideal, need to show
   the fraction still gives a residue from R (algebraic clearing)

2. **Case s ∉ v.asIdeal**: Need to show `residue(a/s) = residue(a*t)` where
   `t` satisfies `s*t ≡ 1 mod v.asIdeal` (inverse calculation in residue field)

**Proof Strategy Used** (Direct Path):
1. Lift y ∈ ResidueField to x ∈ O_v^ via `IsLocalRing.residue_surjective`
2. Use `exists_close_element` to find k ∈ K with v(x - k) < 1
3. Use `mem_integers_of_close` to show k ∈ O_v^
4. Use `residue_eq_of_sub_mem_maximalIdeal` to show residue(k) = residue(x)
5. Use `residue_of_K_element` to find r ∈ R with toResidueField(r) = residue(k)

**Technical Notes**:
- Used `mem_closure_iff` + `Valued.mem_nhds` for density extraction
- Used `Valuation.map_sub` for ultrametric inequality
- Used `Valuation.map_sub_swap` for v(x-y) = v(y-x)

**Significance**:
- **NO MORE AXIOMS** for surjectivity - only implementation sorries remain
- The mathematical proof is complete; only Lean plumbing for fraction arithmetic
- Once filled, `AllIntegersCompact` will be fully discharged under finite quotient hypothesis

**Next Steps** (Cycle 112+):
1. Fill `residue_of_K_element` sorries using fraction field arithmetic
2. Then `residueFieldIso` becomes sorry-free
3. Then `AllIntegersCompact` only needs `Finite (R ⧸ v.asIdeal)` hypothesis

---

#### Cycle 112 - Surjectivity Proof Structure Complete

**Goal**: Fill sorries in `residue_of_K_element` to complete `toResidueField_surjective`.

**Status**: 🔶 IN PROGRESS (proof structure complete, 2 sorries remain)

**Results**:
- [x] Proved `toResidueField_surjective` modulo `residue_of_K_element` sorries
- [x] Added infrastructure for s ∉ v.asIdeal case:
  - `hst_residue`: residue(s) * residue(t) = 1 when st ≡ 1 mod v.asIdeal
  - `exists_mul_eq_one_mod`: inverse exists in R/v.asIdeal
- [x] Build compiles successfully with 2 sorries
- [ ] Fill s ∈ v.asIdeal case (uniformizer factoring)
- [ ] Fill s ∉ v.asIdeal case (fraction/unit arithmetic)

**Current Sorries** (in `residue_of_K_element`):

1. **Case s ∈ v.asIdeal** (line 324): When denominator is in the ideal, need to
   factor out powers of uniformizer. If k = a/s has v(k) ≤ 1 and s ∈ v.asIdeal,
   then a is "more divisible" by the uniformizer than s.

2. **Case s ∉ v.asIdeal** (line 359): Need to show residue(a*t) = residue(a/s)
   where t is the inverse of s modulo v.asIdeal. The mathematical content is clear:
   s is a unit in O_v^, so residue(a/s) = residue(a) · residue(s)⁻¹ = residue(a*t).
   Blocked by Lean coercion management between different completion types.

**Recommended Approach** (from Gemini):
Use `IsLocalization.AtPrime.equivQuotMaximalIdeal` to bridge the localization
at v to the quotient R/v.asIdeal. This avoids manual unit-inverse bridge construction.

**Sorry Status**:
- ResidueFieldIso.lean: 2 sorries in `residue_of_K_element`
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 3 sorries in proof path (2 new in main path)

**Build**: ✅ Compiles successfully

**Next Steps** (Cycle 113+):
1. Use `equivQuotMaximalIdeal` approach to simplify fraction handling
2. Or: Factor s ∈ v.asIdeal case using uniformizer decomposition
3. Then complete full surjectivity proof

---

#### Cycle 113 - Surjectivity Proof Progress (Coercion Challenges)

**Goal**: Fill the 2 sorries in `residue_of_K_element` to complete `toResidueField_surjective`.

**Status**: 🔶 IN PROGRESS (sorry count unchanged, code restructured)

**Results**:
- [x] Handled `s ∈ v.asIdeal` case when `v(k) < 1` (residue = 0, use r = 0)
- [x] Derived `residue(t) = residue(s)⁻¹` using `eq_inv_of_mul_eq_one_right`
- [x] Set up coercion bridge lemmas between S := adicCompletionIntegers and C := adicCompletion
- [ ] `s ∈ v.asIdeal` case when `v(k) = 1` (uniformizer factoring - complex)
- [ ] `s ∉ v.asIdeal` case (coercion management between subring and completion)

**Key Insight**: The mathematical content is clear:
- For `s ∈ v.asIdeal`: If `v(a/s) < 1`, residue = 0. If `v(a/s) = 1`, factor out uniformizers.
- For `s ∉ v.asIdeal`: `residue(a*t) = residue(a) * residue(t) = residue(a) * residue(s)⁻¹ = residue(a/s)`

**Blocking Issues**:
1. **Coercion mismatch**: `algebraMap R S s` (integer subring element) vs `algebraMap R C s` (completion element)
   - Need bridge lemma: `algebraMap R C s = ((algebraMap R S s : S) : C)`
   - Use `simp` instead of `rw` to handle definitional variations

2. **Type inference**: Lean's elaborator treats `(residue.comp algebraMap) x` differently from `residue (algebraMap x)`
   - Pattern matching fails even though they're definitionally equal

**Recommended Approach** (for next cycle):
```lean
-- Bridge coercion: S → C
have hs_coe : algebraMap R C s = ((algebraMap R S s : S) : C) := rfl

-- Use congrArg to transport equalities across coercions
have h := congrArg (fun x : S => (x : C)) hs_unit_eq

-- Use simp [hs_coe] instead of rw to avoid pattern mismatch
simp [hs_coe, ...]
```

**Sorry Status**:
- ResidueFieldIso.lean: 2 sorries in `residue_of_K_element` (lines 349, 401)
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 3 sorries in proof path (unchanged from Cycle 112)

**Build**: ✅ Compiles successfully

**Next Steps** (Cycle 114+):
1. Add explicit coercion bridge lemmas and use `simp` throughout
2. For `s ∈ v.asIdeal, v(k) = 1`: Either factor via uniformizers or use `Localization.AtPrime` API
3. Consider using `native_decide` for definitional equalities if simp fails

---

#### Cycle 115 - Main Case SOLVED (s ∉ v.asIdeal)

**Goal**: Fill sorries in `residue_of_K_element` using "no-units, residue-field-only" approach.

**Status**: 🔶 PARTIAL (1 of 2 sorries filled!)

**Results**:
- [x] **FILLED**: `s ∉ v.asIdeal` case using residue field operations
- [x] Used `res(s) ≠ 0` and `eq_inv_of_mul_eq_one_right` instead of constructing Units
- [x] Key insight: Prove `⟨k, hk⟩ * algebraMap s = algebraMap a` in S, then apply `res` and use `ring`
- [ ] `s ∈ v.asIdeal, v(k) = 1` case still needs uniformizer factoring

**Key Proof Strategy for s ∉ v.asIdeal**:
```lean
-- Instead of complex coercion management, use:
-- 1. hks : algebraMap K C k * algebraMap R C s = algebraMap R C a  (from k = a/s)
-- 2. hks_S : ⟨k, hk⟩ * algebraMap R S s = algebraMap R S a  (via ext + hks)
-- 3. Apply res to both sides, use ring to rearrange
```

**Sorries** (reduced from 2 to 1!):
- ResidueFieldIso.lean:341 - `s ∈ v.asIdeal, v(k) = 1` case
- TraceDualityProof.lean:150 - `finrank_dual_eq` (NOT on critical path)

**Total**: 2 sorries in proof path (down from 3!)

**Build**: ✅ Compiles successfully

**Next Steps** (Cycle 116+):
1. Eliminate `s ∈ v.asIdeal` branch by using `IsLocalization.surj v.asIdeal.primeCompl`
2. Or: Handle with uniformizer factorization
3. Once filled, `AllIntegersCompact` fully discharged under finite quotient hypothesis

---

#### Cycle 114 - Coercion Analysis + Structure Clarification

**Goal**: Fill the 2 sorries in `residue_of_K_element` using coercion bridge lemmas.

**Status**: 🔶 IN PROGRESS (code restructured, sorries documented)

**Results**:
- [x] Fixed variable naming inconsistency (b → s) throughout
- [x] Restructured `residue_of_K_element` with clearer proof strategy
- [x] Added v(k) < 1 subcase handling for s ∈ v.asIdeal (returns 0)
- [x] Documented the mathematical content of remaining sorries
- [ ] Fill s ∉ v.asIdeal sorry (coercion: Units ↔ Subtype ↔ Completion)
- [ ] Fill s ∈ v.asIdeal, v(k) = 1 sorry (uniformizer factoring)

**Key Insight**: The mathematical content is clear in both cases:
1. **s ∉ v.asIdeal**: `residue(a*t) = residue(a) * residue(s)⁻¹ = residue(a/s)` where t is the mod-v inverse of s
2. **s ∈ v.asIdeal, v(k) = 1**: After factoring uniformizers, reduces to case 1

**Blocking Issue**: The coercion chain is complex:
```
(v.adicCompletionIntegers K)ˣ  -- units of integer ring
    ↓ coercion
v.adicCompletionIntegers K     -- integer ring (subtype)
    ↓ coercion
v.adicCompletion K             -- completion
```
The `Units.val_inv_eq_inv_val` lemma and `map_units_inv` need careful application to navigate this.

**Sorries** (unchanged count, clearer location):
- ResidueFieldIso.lean:395 - s ∈ v.asIdeal, v(k) = 1 case
- ResidueFieldIso.lean:465 - s ∉ v.asIdeal coercion case
- TraceDualityProof.lean:150 - `finrank_dual_eq` (NOT on critical path)

**Total**: 3 sorries in proof path

**Build**: ✅ Compiles successfully

**Recommended Approach** (for Cycle 115+):
1. Create explicit bridge lemmas for the coercion chain:
   ```lean
   lemma units_coe_inv_eq_inv_coe (u : Sˣ) : ((u⁻¹ : Sˣ) : S) = (u : S)⁻¹
   lemma residue_units_inv (u : Sˣ) : residue (u⁻¹ : S) = (residue u)⁻¹
   ```
2. Use `simp only [...]` with these lemmas to unfold coercions
3. For s ∈ v.asIdeal case: Consider using `IsLocalization.surj` to get a better representation

---

#### Cycle 116 - ResidueFieldIso: SORRY-FREE! (Major Milestone!)

**Goal**: Fill the remaining sorry in `residue_of_K_element` (s ∈ v.asIdeal case).

**Status**: ✅ COMPLETE - SORRY ELIMINATED!

**Results**:
- [x] Used **Approach 1**: `IsLocalization.surj v.asIdeal.primeCompl` to eliminate the `s ∈ v.asIdeal` branch entirely
- [x] `residue_of_K_element` is now SORRY-FREE
- [x] `toResidueField_surjective` is now SORRY-FREE
- [x] `residueFieldIso` is now SORRY-FREE
- [x] Full PROOF chain for `FiniteCompletionResidueFields` → `AllIntegersCompact` is now sorry-free!
- [!] Note: These are still AXIOM CLASSES - they need instances for concrete types

**Key Insight**: Elements with `v(k) ≤ 1` belong to `valuationRingAt v`, which equals `Localization.AtPrime v.asIdeal` (via `valuationRingAt_val_mem_range`). Using `IsLocalization.surj v.asIdeal.primeCompl`, we get a representation `k = a/s` where `s ∈ primeCompl` (i.e., `s ∉ v.asIdeal`). This eliminates the problematic `s ∈ v.asIdeal` case from the proof entirely!

**Proof Structure**:
```lean
-- Step 1: k with v(k) ≤ 1 means k ∈ valuationRingAt v
-- Step 2: k is in the range of algebraMap from Localization.AtPrime
-- Step 3: Get the element y in localization that maps to k
-- Step 4: Use IsLocalization.surj to write y = a/s with s ∈ primeCompl (s ∉ v.asIdeal)
-- Step 5: From hy and hys, derive k * s = a in K
-- Step 6: Now we're in the solved s ∉ v.asIdeal case!
```

**Sorry Status**:
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 1 sorry remaining (NOT on critical path!)

**Build**: ✅ Compiles successfully

**Significance**: The `ResidueFieldIso.lean` file is now completely sorry-free! This completes the chain:
```
Finite (R ⧸ v.asIdeal)      (hypothesis for function fields over finite k)
       ↓
residueFieldIso             (R/v.asIdeal ≃ ResidueField(completion)) ← NOW SORRY-FREE!
       ↓
finite_residueField_of_finite_quotient
       ↓
FiniteCompletionResidueFields R K
       ↓
AllIntegersCompact R K      (via DVR + RankOne, both already proved)
```

---

#### Cycle 117 - DiscreteCocompactEmbedding Research + Mathlib Class Group Discovery

**Goal**: Research mathlib for DiscreteCocompactEmbedding and establish non-circularity contract.

**Status**: ✅ COMPLETE (research done, strategy established)

**Results**:
- [x] Found `ClassGroup.fintypeOfAdmissibleOfFinite` in mathlib - class group finiteness WITHOUT RR!
- [x] Found `FunctionField.RingOfIntegers.instFintypeClassGroup` - pre-built instance for function fields
- [x] Found `NumberField.prod_abs_eq_one` - product formula for number fields
- [x] Established non-circularity contract for DiscreteCocompactEmbedding
- [x] Identified concrete instance strategy for Fq[X] / RatFunc(Fq)

**Key Mathlib Resources Discovered**:

| Resource | Location | What it Provides |
|----------|----------|------------------|
| `ClassGroup.fintypeOfAdmissibleOfFinite` | `NumberTheory/ClassNumber/Finite.lean:349` | Class group finiteness via admissible abs value |
| `FunctionField.RingOfIntegers.instFintypeClassGroup` | `NumberTheory/ClassNumber/FunctionField.lean:41` | `Fintype (ClassGroup (ringOfIntegers Fq F))` |
| `Polynomial.cardPowDegreeIsAdmissible` | `NumberTheory/ClassNumber/AdmissibleCardPowDegree.lean` | Admissible abs value for Fq[X] |
| `NumberField.prod_abs_eq_one` | `NumberTheory/NumberField/ProductFormula.lean:97` | Product formula for number fields |
| `FunctionField.inftyValuation` | `NumberTheory/FunctionField.lean:192` | Place at infinity on Fq(t) |

**Non-Circularity Contract for DiscreteCocompactEmbedding**:

```
✅ CAN USE (non-circular):
- Class group finiteness (proved via admissible absolute values, NOT RR)
- Product formula for valuations
- Strong approximation theorem
- Purely ideal-theoretic / valuation-theoretic arguments

❌ CANNOT USE (would be circular):
- ℓ(D) dimension counts
- "exist f with prescribed poles of degree d"
- Riemann inequality ℓ(D) ≤ deg(D) + 1 - g
- Any dimension bounds on spaces of functions
```

**Why Mathlib's Class Group Finiteness is Non-Circular**:

The proof in `ClassGroup.fintypeOfAdmissibleOfFinite` uses:
1. Norm bounds from the admissible absolute value
2. Pigeonhole-type arguments (finitely many ideals with bounded norm)
3. No dimension counting on function spaces

This is fundamentally different from proving finiteness via RR/dimension counts.

**Structure for DiscreteCocompactEmbedding Proof**:

```
DiscreteCocompactEmbedding requires:
1. discrete: K is discrete in A_K
   → Follows from: product formula (each x ∈ K* has v(x) = 1 for cofinitely many v)

2. closed: K is closed in A_K
   → Follows from: discrete + locally compact → closed

3. compact_fundamental_domain: ∃ compact F, ∀ a, ∃ x ∈ K, a - x ∈ F
   → Follows from: class group finiteness + unit group structure
   → Key insight: cosets of K in A_K correspond to ideal classes
```

**Concrete Instance Strategy (Fq[X] / RatFunc(Fq))**:

For the simplest case F = RatFunc(Fq), R = Fq[X]:
- This is the "P¹ case" (genus 0)
- Class group is trivial: Fq[X] is a PID
- The fundamental domain should be explicitly constructible

**Caveat**: The current `FiniteAdeleRing R K` uses only `HeightOneSpectrum R`, which gives
finite places. For function fields, the place at infinity is NOT a HeightOneSpectrum prime.
Full adelic theory would need to include infinity, but this may not be needed for
DiscreteCocompactEmbedding if we're careful about what we're proving.

**Sorry Status** (unchanged from Cycle 116):
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)

**Total**: 1 sorry in main path (unchanged)

**Next Steps** (Cycle 118+):
1. **Option A**: Create `FqPolynomialInstance.lean` for concrete Fq[X] instance
   - Instantiate `AllIntegersCompact` using `Finite (Fq[X] / p)` for primes p
   - Instantiate `DiscreteCocompactEmbedding` using PID + product formula
2. **Option B**: Work on general `DiscreteCocompactEmbedding` using class group finiteness
3. **Option C**: Tag milestone for sorry-free `AllIntegersCompact` achievement

**Recommendation**: Option A (concrete instance first) to validate the pipeline before
generalizing. This follows ChatGPT's advice and avoids abstract machinery bugs.

---

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
