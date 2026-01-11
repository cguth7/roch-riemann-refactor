# Riemann-Roch Formalization Ledger

---

## Mission

**Goal**: Prove Riemann-Roch for curves over algebraically closed fields in Lean 4, using only the standard 3 foundational axioms (propext, Classical.choice, Quot.sound).

**Motivation**: Daniel Litt's Twitter challenge (Dec 15, 2025) - a fully formalized RR theorem.

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 353
**Phase**: 9 (General Curve Infrastructure)

### What We Have (Core RR Proof Complete)

| Theorem | Status | Notes |
|---------|--------|-------|
| `euler_characteristic` | ✅ PROVED | χ(D) = deg(D) + 1 - g |
| `chi_additive` | ✅ PROVED | χ(D+v) = χ(D) + 1 |
| 6-term exact sequence | ✅ PROVED | All exactness lemmas complete |
| `riemann_roch_from_euler` | ✅ PROVED | Full RR via Euler + Serre duality |

### What Blocks Litt's Challenge

The proof uses only propext/choice/quot.sound BUT has `axiom` declarations and `sorry` placeholders that need elimination:

#### Current Axiom Status

The main RR theorem (`riemann_roch_fullRRData`) now shows **NO sorryAx**!

Axioms used by the elliptic curve RR proof (6 on critical path):
| File | Axiom | Status | Notes |
|------|-------|--------|-------|
| EllipticRRData | `adelic_euler_char` | ✅ **THEOREM** | Uses euler_characteristic |
| EllipticRRData | `h1_finite_all` | axiom | Shortcut via Serre duality |
| EllipticRRData | `ell_finite_all` | ✅ **THEOREM** | Cycle 342 - gap bound + posPart |
| EllipticRRData | `degreeOnePlaces_elliptic` | ✅ **THEOREM** | Cycle 346: Fully proved via F-linear equiv |
| EllipticH1 | `h1_zero_eq_one` | axiom | Genus = 1 |
| EllipticH1 | `h1_zero_finite` | ✅ **THEOREM** | From h1_zero_eq_one |
| EllipticH1 | `h1_vanishing_positive` | axiom | Vanishing theorem |
| EllipticH1 | `serre_duality` | axiom | Residue pairing |
| EllipticSetup | `isDedekindDomain_coordinateRing_axiom` | axiom | Standard AG |

**Not on critical path** (still have sorries but don't affect RR proof):
| File | Instance | Notes |
|------|----------|-------|
| StrongApprox | `instStrongApprox_P1` | P¹ density |
| StrongApprox | `instStrongApprox_Elliptic` | Elliptic density |

#### Sorry Placeholders (13 found - updated Cycle 347)

| File | Count | Lines | Notes |
|------|-------|-------|-------|
| Abstract.lean | 8 | 200,201,203,294,299,312,345,351 | P¹ instance, IsLinearPlaceSupport |
| AdelicH1Full.lean | 3 | 811,1508,1519 | Strong approx edge cases |
| StrongApproximation.lean | 2 | 127,171 | P¹ and Elliptic density |

#### All Axioms (6 in Elliptic/, 5 on critical path)

| Axiom | File | Critical Path? |
|-------|------|----------------|
| `h1_finite_all` | EllipticRRData | ✅ Yes |
| `h1_zero_eq_one` | EllipticH1 | ✅ Yes |
| `h1_vanishing_positive` | EllipticH1 | ✅ Yes |
| `serre_duality` | EllipticH1 | ✅ Yes |
| `isDedekindDomain_coordinateRing_axiom` | EllipticSetup | ✅ Yes |
| `exists_localUniformizer` | EllipticPlaces | ❌ No |

**See INVENTORY_REPORT_V2.md for detailed scoping.**

---

## Phase 9: General Curve Infrastructure (Cycle 347+)

**Goal**: Prove the 5 remaining axioms in a way that generalizes to genus N curves.

### The 5 Remaining Axioms

| Axiom | What It Says | General Form |
|-------|--------------|--------------|
| `h1_finite_all` | H¹(D) is finite-dim for all D | Compactness of A_K/K |
| `h1_vanishing_positive` | H¹(D) = 0 when deg(D) > 2g-2 | Strong Approximation + degree |
| `h1_zero_eq_one` | dim H¹(O) = g | Genus via differentials |
| `serre_duality` | h¹(D) = ℓ(K-D) | Residue pairing construction |
| `isDedekindDomain_coordRing` | Smooth → Dedekind | Keep as axiom (orthogonal) |

### Strategy: Build General Infrastructure

Rather than proving these for elliptic curves only, we build infrastructure that works for any smooth projective curve over an algebraically closed field.

**IMPORTANT: Active Edge Rule** - Each cycle picks ONE specific target from the tracks below. Avoid diluting focus across multiple tracks.

#### Track A: Adelic Compactness → H¹ Finiteness
**Goal**: Prove A_K/K is compact (or locally compact with discrete K)

| Component | Status | Notes |
|-----------|--------|-------|
| DVR structure at places | ✅ DONE | AllIntegersCompactProof.lean |
| RankOne valuations | ✅ DONE | Cycles 105-106 |
| Local compactness of A(D) | Partial | Need restricted product topology |
| K discrete in A_K | Needed | Standard fact |
| Compactness of quotient | Needed | Gives Module.Finite for H¹ |

#### Track B: Strong Approximation → H¹ Vanishing
**Goal**: Prove K + A(D) = A_K when deg(D) > 2g-2

| Component | Status | Notes |
|-----------|--------|-------|
| Local density (K dense in K_v) | ✅ DONE | UniformSpace.Completion.denseRange_coe |
| P¹ strong approximation | Cycle 347 | Reduced to single topology lemma |
| Elliptic strong approximation | Needed | Requires group structure or CFT |
| General curve strong approx | Needed | Follows from Riemann-Roch itself! |

**Speculative Insight** (needs careful verification to avoid circularity):
For deg(D) > 2g-2, strong approximation MAY follow from Riemann-Roch:
- RR says ℓ(D) - h¹(D) = deg(D) + 1 - g
- For deg(D) > 2g-2: ℓ(D) ≥ deg(D) + 1 - g > g - 1
- This gives enough global sections to approximate
- ⚠️ CONDITIONAL: Must verify no circular dependency with h1_vanishing_positive

#### Track C: Residue Pairing → Serre Duality
**Goal**: Construct perfect pairing H¹(D) × L(K-D) → k

| Component | Status | Notes |
|-----------|--------|-------|
| Residue infrastructure | ✅ DONE | RatFuncResidues.lean |
| Residue theorem | ✅ DONE | Sum of residues = 0 |
| Diagonal pairing K × K → Fq | ✅ DONE | RatFuncPairing.lean |
| Pole cancellation (bounded × L(K-D)) | ✅ DONE | bounded_times_LKD_no_pole |
| Vanishing case (both = 0) | ✅ DONE | For deg(D) ≥ -1 on P¹ |
| **Quotient pairing descent** | BLOCKING | φ: H¹(D) × L(K-D) → Fq |
| **Non-degeneracy** | BLOCKING | Each non-zero pairs non-trivially |
| Transfer to general curves | Needed | Abstract from RatFunc |

**Key insight (Cycle 348)**: The quotient pairing construction is the critical blocker.
Once φ descends to H¹(D) and is non-degenerate, we get:
- H¹(D) ≅ L(K-D)* (perfect pairing duality)
- h1_finite follows from ell_finite (L(K-D) finite → L(K-D)* finite → H¹(D) finite)
- serre_duality follows from dimension equality

#### Track D: Genus = dim H¹(O)
**Goal**: Prove h¹(O) = g via invariant differentials

| Component | Status | Notes |
|-----------|--------|-------|
| Canonical divisor K | ✅ DONE | ellipticCanonical = 0 |
| deg(K) = 2g - 2 | ✅ DONE | For g=1: deg(K)=0 |
| Invariant differential | Needed | ω = dx/(2y) for elliptic |
| H¹(O) ≅ space of differentials | Needed | Duality statement |

### Recommended Attack Order

1. **Track C first**: Serre duality gives us h¹(D) = ℓ(K-D)
   - Once we have this, h1_finite follows from ell_finite
   - The residue pairing infrastructure exists

2. **Track B second**: Strong approximation for vanishing
   - Needs careful dependency analysis (see speculative note above)

3. **Track A third**: Compactness for full finiteness
   - Needed for cases where Serre duality shortcut fails
   - Deepest infrastructure

4. **Track D last**: Genus calculation
   - Can be axiomatized if needed (defines the curve)
   - Or prove via differential forms

### Active Edge for Cycle 354

**Target**: Complete the `isOpen_bounded_finiteAdeles` proof in test_h1_finiteness.lean

**Current state**: Mathematical argument fully documented, but Lean formalization needs work on:
1. Type coercion between `FiniteAdeleRing` (def alias) and `RestrictedProduct`
2. Typeclass resolution for `Valued` on components of the restricted product
3. Working with `simp_rw` across topology instance equality

**Alternative approach to explore**:
- Use `RestrictedProduct.isOpen_forall_imp_mem` with predicate `p v := v ∈ T` where T = {D v ≠ 0}
- For v ∉ T, D v = 0 means Ball_v = O_v (automatically in restricted product constraint)
- For v ∈ T, explicitly check Ball_v constraint
- This may avoid the complex topology instance manipulation

**What's proved** (Cycles 350-352):
- `integralFullAdeles_covers_h1` ✅
- `isOpen_bounded_infty` ✅
- `boundedSubmodule_full_isOpen` ✅ (modulo finite adeles lemma)
- Complete chain from openness → Module.Finite documented

### Phase 8 Summary (Completed)

| Task | Status |
|------|--------|
| `euler_char_axiom` | ✅ Wired (Cycle 340) |
| `h1_zero_finite` | ✅ From h1_zero_eq_one (Cycle 341) |
| `ell_finite_all` | ✅ Gap bound (Cycle 342) |
| `degreeOnePlaces_elliptic` | ✅ F-linear equiv (Cycle 346) |
| P¹ strong approx structure | ✅ Reduced to 1 lemma (Cycle 347) |

---

## Recent Cycles

### Cycle 353 - Topology Instance Challenges

**Attempted to formalize the isOpen_bounded_finiteAdeles proof**

Key findings:
1. **FiniteAdeleRing is a `def` not `abbrev`**: This creates a separate type with `inferInstanceAs` for topology
2. **Type parameter issues**: Writing `IsOpen (X := RestrictedProduct ...)` works but typeclass resolution for `Valued` on dependent types fails
3. **simp_rw limitations**: The `simp_rw [topologicalSpace_eq_iSup, isOpen_iSup_iff, isOpen_coinduced]` pattern from Mathlib doesn't apply directly due to type aliasing

Attempted approaches:
- Direct `show @IsOpen ...` with explicit type - syntax issues with restricted product notation
- Helper lemma on RestrictedProduct type - typeclass resolution stuck
- Using `rw [show inferInstance = ... from rfl]` - type mismatch

**Insight**: The problem isn't the mathematical argument (which is clear), but how Lean handles type aliases and typeclass inference across definitionally equal but nominally distinct types.

**Recommendation for next cycle**: Try using the existing `isOpen_forall_imp_mem` lemma with a predicate approach rather than fighting the topology instance issues.

**Build status:** ✅ PASSING (1 sorry with detailed proof sketch)

---

### Cycle 352 - RestrictedProduct Topology Investigation

**Deep dive into proving isOpen_bounded_finiteAdeles**

Key discoveries:
1. **RestrictedProduct topology structure**: Topology = ⨆ S (cofinite), coinduced from S-principal product
2. **The key lemmas**:
   - `topologicalSpace_eq_iSup Filter.cofinite`: characterizes the topology
   - `isOpen_iSup_iff`: reduces to showing openness in each coinduced topology
   - `isOpen_coinduced`: reduces to showing preimage is open
3. **Mathematical argument validated**:
   - For each cofinite S, define T = (S ∩ {D < 0}) ∪ Sᶜ (finite!)
   - In S-principal product, ∀ v, f.1 v ∈ Ball_v ⟺ ∀ v ∈ T, f.1 v ∈ Ball_v
   - The finite condition is open by `isOpen_set_pi`
   - Preimage under continuous coercion is open
4. **Technical gap identified**:
   - Applying `@IsOpen` with the right topology instance
   - Working with `isOpen_iSup_iff` when the topology is definitionally equal but not syntactically

Remaining sorry: `isOpen_bounded_finiteAdeles` (with detailed proof sketch in comments)

**Build status:** ✅ PASSING (1 sorry)

---

### Cycle 351 - Openness Proof Structure

**Progress on proving boundedSubmodule_full is open**

Key achievements:
1. **PROVED `isOpen_bounded_infty`**: Valuation balls in FqtInfty are open
2. Proved `boundedSubmodule_full_isOpen` structure (product of open sets approach)
3. Identified precise gap in `isOpen_bounded_finiteAdeles`:
   - Mathematical argument is clear (cofinite principal products + finite ball conditions)
   - Technical gap: need variant of `RestrictedProduct.isOpen_forall_mem` for variable sets

Remaining sorry: `isOpen_bounded_finiteAdeles` in test_h1_finiteness.lean

The proof requires using `topologicalSpace_eq_iSup` to show openness via principal products, combined with `isOpen_set_pi` for finite conditions.

---

### Cycle 350 - Compactness Strategy Proof Structure

**Developed complete strategy for h1_finite via compactness (Track A)**

Key achievements:
1. Created `test_h1_finiteness.lean` with proof structure
2. **PROVED `integralFullAdeles_covers_h1`**: Every element of H¹(D) has a representative in integralFullAdeles (uses fundamental domain property from FullAdelesCompact.lean)
3. Documented the full compactness → finiteness chain

**The proof path**:
1. A_K(D) is open in FqFullAdeleRing (needs `boundedSubmodule_full_isOpen` - 1 sorry)
2. K + A_K(D) is open (union of translates of open set)
3. H¹(D) = FullAdeleRing / (K + A_K(D)) has discrete topology
4. integralFullAdeles maps surjectively onto H¹(D) ✅
5. Compact + discrete = finite
6. Finite Fq-vector space = Module.Finite

**Key gap identified**: `boundedSubmodule_full_isOpen`
- Requires connecting Mathlib's RestrictedProduct topology with component-wise valuations
- Mathematical argument is clear: valuation balls are open, finite intersection of opens is open
- Technical implementation needs RestrictedProduct API

**Infrastructure confirmed as available**:
- `isCompact_integralFullAdeles` ✅
- `exists_translate_in_integralFullAdeles` ✅
- `fq_discrete_in_fullAdeles` ✅
- `fq_closed_in_fullAdeles` ✅
- `Valued.isOpen_closedBall` ✅

**Build status:** ✅ PASSING

### Cycle 349 - Track C Blocked, Pivot to Track A (Compactness)

**Attempted quotient pairing construction, found fundamental blocker**

Key work:
1. Created `test_quotient_pairing.lean` with raw pairing infrastructure
2. Defined `rawKPairing : K × K → Fq` via `residueSumTotal`
3. Proved bilinearity and vanishing for split denominators

**Blocker discovered**: Residue pairing cannot descend to quotient
- Residues are defined for RatFunc, not adicCompletion elements
- To define φ([a], f) we need to compute res_v(a_v · f) where a_v ∈ K_v
- The workaround (weak approximation: a = diag(k) + bounded) FAILS for deg D < -1
- This is precisely when strong approximation fails

**Pivot to compactness approach (Track A)**:
- Found `isCompact_integralFullAdeles` already proved in FullAdelesCompact.lean
- The standard path: K discrete → A_K/K compact → H¹(D) finite
- This avoids needing residues on completion elements

**Build status:** ✅ PASSING

### Cycle 348 - Track C Investigation: Circular Dependency Found

**Investigated Serre duality non-vanishing case (Abstract.lean:351)**

Key findings:
1. **Circular dependency discovered**: h1_finite (line 299) and serre_duality (line 351) both need the same thing for deg D < -1
2. **Root cause**: `Module.finrank` returns 0 for non-finite modules
   - If we don't prove H¹(D) finite first, h1_finrank_full = 0
   - But ell_proj_ext(K-D) > 0 for deg D < -1
   - So the equality can't hold without finiteness
3. **Solution identified**: Construct perfect pairing H¹(D) × L(K-D) → Fq
   - The isomorphism H¹(D) ≅ L(K-D)* gives both finiteness and dimension equality
   - This breaks the circular dependency

**Infrastructure audit**:
| Component | Location | Status |
|-----------|----------|--------|
| Residue sum at finite places | RatFuncResidues.lean | ✅ DONE |
| Total residue sum (finite + ∞) | RatFuncResidues.lean | ✅ DONE |
| Diagonal pairing K × K → Fq | RatFuncPairing.lean | ✅ DONE |
| Pole cancellation for bounded × L(K-D) | RatFuncPairing.lean | ✅ DONE |
| Quotient pairing (descent to H¹) | — | ❌ NEEDED |
| Non-degeneracy proof | — | ❌ NEEDED |

**Next step**: Build the quotient pairing construction. The hard part is showing the pairing descends to the quotient (vanishes on K + A(D)).

**Build status:** ✅ PASSING

### Cycle 347 - Phase 9 Setup + P¹ Strong Approx Progress

**Pivoted to building general curve infrastructure for genus N**

Key achievements:
1. Analyzed remaining 5 axioms for generalization potential
2. Created 4-track plan (Compactness, Strong Approx, Serre Duality, Genus)
3. Reduced P¹ StrongApprox to single topology lemma (`exists_boundedSubmodule_subset_nhds`)

**P¹ Strong Approx proof structure** (in test_strong_approx.lean):
- Uses `strong_approximation_ratfunc` (fully proved algebraic result)
- Main theorem `p1_denseRange_algebraMap` compiles with 1 sorry
- The sorry is: "bounded submodules form a neighborhood basis of 0"
- Mathematical argument clear, needs Mathlib RestrictedProduct topology API

**Ledger accuracy fixes** (after external review):
- Updated sorry count: 13 (was 9) - Abstract.lean(8), AdelicH1Full.lean(3), StrongApprox(2)
- Added missing axiom: `exists_localUniformizer` in EllipticPlaces.lean (not on critical path)
- Added "Active Edge" rule to prevent focus dilution
- Marked RR bootstrap for strong approx as speculative (needs circularity check)

**Build status:** ✅ PASSING

### Cycle 346 - degreeOnePlaces_elliptic FULLY PROVED ✅✅

**Eliminated the remaining sorry in degreeOnePlaces_elliptic!**

Key achievements:
1. Proved `algebraMap_quot_res_comp`: algebraMap compatibility for scalar tower transfer
2. Built `quotToResLinearMapF`: F-linear map from quotient to residue field
3. Built `quotToResLinearEquivF`: F-linear equivalence (using bijective algebraMap)
4. Proved `finrank_quot_eq_finrank_res`: finrank transfers via linear equiv

**The fix:**
The sorry was about transferring finrank from quotient to residue field. The key insight:
- Both quotient and residue field have F-algebra structures via F → CoordRing W
- The algebraMap quotient → residue field respects the F-action (via scalar tower)
- This means it's actually an F-linear map, not just an R-linear map
- Bijective F-linear map = F-linear equivalence
- Linear equivalences preserve finrank

**Proof structure for scalar tower compatibility:**
```
algebraMap F quotient = Ideal.Quotient.mk ∘ algebraMap F (CoordRing W)      [scalar tower 1]
algebraMap F residue = algebraMap (CoordRing W) residue ∘ algebraMap F (CoordRing W)  [scalar tower 2]
algebraMap quotient residue ∘ Ideal.Quotient.mk = algebraMap (CoordRing W) residue    [scalar tower 3]
```
These compose to: `algebraMap quotient residue ∘ algebraMap F quotient = algebraMap F residue`

**Current axiom status (5 axioms on critical path):**
- `h1_finite_all`: axiom (blocked by circular dep)
- `h1_zero_eq_one`: axiom
- `h1_vanishing_positive`: axiom
- `serre_duality`: axiom
- `isDedekindDomain_coordinateRing_axiom`: axiom

**Build status:** ✅ PASSING

### Cycle 345 - degreeOnePlaces_elliptic CONVERTED TO THEOREM ✅

**Major progress: Converted from axiom to theorem (with 1 remaining sorry)**

Key achievements:
1. Proved `finrank_eq_one_of_algebraMap_bijective` helper lemma
2. Showed `Algebra.IsIntegral F ((CoordRing W) ⧸ v.asIdeal)` using Jacobson ring theory
3. Proved `halg_bij`: algebraMap F → quotient is bijective (via IsAlgClosed)
4. Proved `hquot_finrank`: finrank F quotient = 1

**Proof structure:**
1. `CoordRing W` is `Algebra.FiniteType F` (AdjoinRoot of polynomial ring) ✅
2. `(CoordRing W) ⧸ v.asIdeal` is FiniteType over F (via `Algebra.FiniteType.of_surjective`) ✅
3. F is `IsJacobsonRing` (field → Artinian → Jacobson) ✅
4. `finite_of_finite_type_of_isJacobsonRing` gives `Module.Finite` ✅
5. `IsIntegral.of_finite` gives integrality ✅
6. `IsAlgClosed.algebraMap_bijective_of_isIntegral` gives bijective algebraMap ✅
7. Bijective algebraMap → finrank = 1 ✅

**Remaining sorry:** Transfer from quotient (finrank 1) to residue field (same finrank).
This is a Mathlib instance threading issue (need IsScalarTower F quotient residue_field).
The mathematical content is complete.

**Build status:** ✅ PASSING

### Cycle 344 - degreeOnePlaces_elliptic investigation

**Added [IsAlgClosed F] assumption and documented proof strategy**

Key changes to EllipticRRData.lean:
1. Added imports: `Mathlib.FieldTheory.IsAlgClosed.Basic`, `Mathlib.RingTheory.Jacobson.Ring`
2. Added `[IsAlgClosed F]` to the variable block (line 46)
3. Documented complete proof strategy for `degreeOnePlaces_elliptic`

**Build status:** ✅ PASSING

### Cycle 343 - h1_finite_all investigation

**Attempted to convert axiom to theorem - found circular dependency**

Key discovery: The "Serre duality shortcut" (h1(D) = ell(-D)) creates a circular dependency:
```
h1_finite_all → ellipticH1Finite → euler_characteristic → riemann_roch_positive' → h1_finite_all
```

**What we proved (partial progress):**
- `ell_proj_ge_one_of_effective`: For effective D, ℓ(D) ≥ 1
- `ell_proj_pos_of_effective`: For effective D, ℓ(D) > 0
- `h1_finite_of_neg_effective`: **H¹(D) is finite when -D is effective** ✅

**Case analysis for h1_finite_all:**
| Case | Status | Blocker |
|------|--------|---------|
| -D effective (includes deg(D) ≤ 0 with D ≤ 0) | ✅ PROVED | - |
| deg(D) < 0, -D not effective | Blocked | Need linear equivalence to effective |
| deg(D) = 0, general | Blocked | Requires case analysis |
| deg(D) > 0 | Blocked | `h1_vanishing_positive` gives finrank=0, not Module.Finite |

**Conclusion:** Keep `h1_finite_all` as axiom. The deg > 0 case genuinely needs strong approximation
to show the quotient is trivial (not just finrank = 0). This confirms the original assessment that
compactness/strong approximation is required.

**Build status:** ✅ PASSING

### Cycle 342 - ell_finite_all PROVED ✅

**Converted axiom to theorem** - Major milestone!

Infrastructure added to EulerCharacteristic.lean:
- `gap_le_one_proj_of_degreeOne`: Gap bound ℓ(D+v) ≤ ℓ(D) + 1 using DegreeOnePlaces
- `RRSpace_proj_zero_finite`: L(0) is finite for proper curves
- `ell_finite_of_effective`: L(D) finite for effective D by degree induction

Proof strategy for `ell_finite_all`:
1. For effective D: Use `ell_finite_of_effective`
2. For non-effective D: L(D) ⊆ L(D.posPart) where D.posPart is effective
3. Use `Module.Finite.of_injective` to transfer finiteness via inclusion

**Result**: 6 axioms on critical path (down from 7)

### Cycle 341 - h1_zero_finite proved + Infrastructure Discovery

**Converted axiom to theorem:**
- `h1_zero_finite` now derived from `h1_zero_eq_one`
- Proof: if h¹(0) = 1 > 0, then `Module.finite_of_finrank_pos` applies
- 8 axioms remain total (7 on critical path for RR)

**Major Infrastructure Discovery** (via systematic exploration):

| Axiom | What We Found | Reusability |
|-------|---------------|-------------|
| `ell_finite_all` | **P¹ proof EXISTS in DimensionGeneral.lean** | ~80% |
| `h1_finite_all` | DVR/RankOne/CompleteSpace ALL PROVED (Cycles 105-106) | High |
| `degreeOnePlaces` | PlaceDegree.lean has `linearPlace_degree_eq_one` | Need wiring |
| `serre_duality` | Vanishing case (deg≥-1) PROVED | Full for P¹ |
| `h1_vanishing` | Needs StrongApprox (sorried) | Blocked |

**Key files with reusable proofs:**
- `DimensionGeneral.lean`: Complete L(D) finiteness via weighted degree induction
- `DimensionCore.lean`: Pole-clearing technique
- `GapBoundGeneral.lean`: Gap bounds, `residueFieldAtPrime_finite`
- `AllIntegersCompactProof.lean`: DVR, RankOne infrastructure
- `PlaceDegree.lean`: Degree 1 places for P¹

**Research on remaining axioms:**
- `degreeOnePlaces_elliptic`: Proof sketch using `degree_eq_one_of_irreducible_of_root` + IsAlgClosed
- AllIntegersCompact only missing Mathlib's residue field isomorphism
- Serre duality shortcut: h1_finite can follow from ell_finite via h1(D) = ell(-D)

### Cycle 340 - adelic_euler_char WIRED + sorryAx ELIMINATED ✅✅

**Major cleanup of the proof chain!**

Part 1 - adelic_euler_char conversion:
- Broke circular dependency: `ell_zero_eq_one` now uses `serre_duality` directly
- Converted `adelic_euler_char` from axiom to theorem using `euler_characteristic`
- Added `degreeOnePlaces_elliptic` axiom (all places degree 1 over alg closed)
- Added finiteness instances from existing axioms

Part 2 - sorryAx elimination:
- Removed sorried `riemann_roch_positive/full` stubs from EllipticH1.lean
- Removed unnecessary StrongApproximation import from EllipticH1.lean
- Converted `isDedekindDomain_coordinateRing` from sorry to proper axiom

**Result**: `#print axioms riemann_roch_fullRRData` now shows NO sorryAx!
Only depends on propext/Classical.choice/Quot.sound + our declared axioms.

### Cycle 339 - euler_characteristic PROVED

**Major accomplishment**: Completed the critical path!

- Added `chi_additive_sub` and `chi_additive_general` (integer induction)
- Proved `euler_characteristic` using Finsupp.induction
- **Critical path sorries: 0**

### Cycle 338 - chi_additive PROVED

- Dimension counting from 6-term exact sequence
- Key lemmas: `ell_diff_eq_rangeEval`, `h1_diff_eq_rangeδ`, `rangeδ_plus_rangeEval_eq_one`

---

## Architecture

```
RrLean/RiemannRochV2/
├── Core/              - Divisors, RRSpace, basic infrastructure
├── Adelic/            - Full adeles, Euler characteristic ✅
├── SerreDuality/      - H¹ framework, Serre duality
├── Elliptic/          - Elliptic curve instances (has axioms)
├── ResidueTheory/     - Residue field isomorphisms
└── General/           - Weil differentials, abstract interfaces
```

---

## Key Files

| File | Purpose | Status |
|------|---------|--------|
| EulerCharacteristic.lean | Main theorems | ✅ Sorry-free |
| EllipticRRData.lean | Elliptic instances | Has 3 axioms |
| EllipticSetup.lean | Elliptic setup | Has 1 axiom |
| StrongApproximation.lean | Density | Has 2 axioms |
| Abstract.lean | Abstraction layer | Has 3 sorries |

---

## References

- [Litt's Challenge](https://twitter.com/littmath/status/1868344897046298846) - Dec 15, 2025
- **INVENTORY_REPORT_V2.md** - Detailed Phase 8 scoping (axioms, sorries, strategies)
- INVENTORY_REPORT.md - Original asset inventory

---

*Updated Cycle 350. Phase 9 continues - Track A (compactness) is the active edge. Key blocker: `boundedSubmodule_full_isOpen`. Once this is proved, h1_finite_all follows via compactness.*
