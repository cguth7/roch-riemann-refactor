# Inventory Report V2: Phase 8 Scoping

**Generated**: Cycle 339, **Updated**: Cycle 341 (Jan 2026)
**Purpose**: Detailed assessment of remaining work for Litt's challenge

---

## Executive Summary

**Core RR proof**: ✅ COMPLETE (euler_characteristic, chi_additive, riemann_roch_from_euler)

**Remaining for Litt's challenge**:
- 7 axiom declarations on critical path (8 total)
- Several sorry placeholders in non-critical P¹ code

**Estimated effort**: 12-21 cycles (optimistic: 12, realistic: 18, pessimistic: 25+)

**Cycle 341 Discovery**: We have MORE infrastructure than previously thought! See "Key Infrastructure Discoveries" section.

---

## Key Infrastructure Discoveries (Cycle 341)

**Critical finding**: Much more infrastructure exists than previously documented!

### ell_finite_all - P¹ Proof EXISTS

| Component | Status | Location |
|-----------|--------|----------|
| **Complete P¹ finiteness proof** | ✅ PROVED | DimensionGeneral.lean |
| Pole-clearing via (X-α)^n multiplication | ✅ PROVED | DimensionCore.lean |
| Induction on weighted degree | ✅ PROVED | DimensionGeneral.lean |
| Surjective evaluation maps | ✅ PROVED | DimensionGeneral.lean |
| Gap bound ℓ(D+[v]) = ℓ(D) + deg(v) | ✅ PROVED | GapBoundGeneral.lean |
| `residueFieldAtPrime_finite` | ✅ PROVED | GapBoundGeneral.lean |

**Reusability for elliptic**: ~80% direct copy. Needs:
- Negative degree case: L(D) = {0} when deg(D) < 0
- ConstantsValuationBound typeclass instantiation

### h1_finite_all - AllIntegersCompact Almost Done

| Component | Status | Location |
|-----------|--------|----------|
| DVR for adic completions | ✅ PROVED | DedekindDVR.lean |
| RankOne for valuations | ✅ PROVED | AllIntegersCompactProof.lean:154 |
| CompleteSpace for completions | ✅ PROVED | (automatic from completion) |
| h1_anti_mono (monotonicity) | ✅ PROVED | AdelicH1v2.lean:523 |
| **FiniteCompletionResidueFields** | ❌ AXIOM | Only remaining blocker! |

**Blocker**: Mathlib lacks `ResidueField(O_v^) ≃ R/v.asIdeal` isomorphism.

**Alternative**: Use Serre duality shortcut: h1(D) = ell(-D), so h1_finite follows from ell_finite.

### degreeOnePlaces - PlaceDegree Infrastructure Ready

| Component | Status | Location |
|-----------|--------|----------|
| DegreeOnePlaces typeclass | ✅ DEFINED | EulerCharacteristic.lean |
| `linearPlace_degree_eq_one` | ✅ PROVED | PlaceDegree.lean |
| `finrank_residueField_eq_degree` | ✅ PROVED | PlaceDegree.lean:176-183 |
| `linear_of_degree_eq_one` (converse) | ✅ PROVED | PlaceDegree.lean |
| Finite quotient instances | ✅ PROVED | FqPolynomialInstance.lean |

**For elliptic over alg closed**: Need `[IsAlgClosed F]` + prove finite extensions are trivial.
Proof sketch developed in Cycle 341 using `degree_eq_one_of_irreducible_of_root`.

### serre_duality - Vanishing Case Done

| Component | Status | Location |
|-----------|--------|----------|
| Abstract serrePairing framework | ✅ DEFINED | Abstract.lean (as placeholder 0) |
| Residue theorem (split denominators) | ✅ PROVED | RatFuncResidues.lean |
| **Vanishing case (deg ≥ -1)** | ✅ PROVED | AdelicH1Full.lean |
| Non-vanishing case (deg < -1) | ❌ SORRY | Needs actual residue pairing |
| Pole cancellation structure | ✅ PROVED | RatFuncPairing.lean |

**Key insight**: For P¹ (genus 0), the vanishing case covers almost everything.
For elliptic (genus 1), need full pairing for some divisors.

### h1_vanishing - Needs StrongApprox

| Component | Status | Location |
|-----------|--------|----------|
| h1_vanishing axiom in AdelicRRData | ✅ DEFINED | AdelicH1v2.lean:419 |
| StrongApprox typeclass | ✅ DEFINED | StrongApproximation.lean |
| P¹ strong approximation | ❌ SORRY | CRT + topology wiring needed |
| Elliptic strong approximation | ❌ SORRY | Deep number theory |

**Dependency**: h1_vanishing proof requires StrongApprox instance.

---

## Axiom Declarations: Detailed Assessment

### 1. `h1_finite_all` - H¹(D) is finite-dimensional

**Location**: `EllipticRRData.lean:71-72`
```lean
axiom h1_finite_all (D : DivisorV2 (CoordRing W)) :
    Module.Finite F (EllipticH1 W D)
```

**What Exists**:
| Component | Status | Location |
|-----------|--------|----------|
| SpaceModule definition | ✅ | AdelicH1v2.lean:293 |
| AdelicRRData typeclass | ✅ | AdelicH1v2.lean:419 |
| AllIntegersCompact infrastructure | ✅ | AdelicTopology.lean:94 |
| DVR for completions | ✅ PROVED | DedekindDVR.lean |
| RankOne on valuations | ✅ PROVED | AllIntegersCompactProof.lean:154 |
| h1_anti_mono (monotonicity) | ✅ PROVED | AdelicH1v2.lean:523 |

**What's Missing**:
- Residue field isomorphism (Mathlib gap): `ResidueField(O_v^) ≃ R/v.asIdeal`
- This blocks the full topological approach

**Proof Strategies**:

| Strategy | Effort | Notes |
|----------|--------|-------|
| Via Serre duality + monotonicity | 100-200 lines | **RECOMMENDED** |
| Via full compactness | 500-1000 lines | Requires Mathlib patch |

**Difficulty**: MEDIUM (2-3 cycles)

---

### 2. `ell_finite_all` - L(D) is finite-dimensional

**Location**: `EllipticRRData.lean:87-88`
```lean
axiom ell_finite_all (D : DivisorV2 (CoordRing W)) :
    Module.Finite F (RRSpace_proj F (CoordRing W) (FuncField W) D)
```

**What Exists** (UPDATED Cycle 341 - more than expected!):
| Component | Status | Location |
|-----------|--------|----------|
| RRSpace_proj definition | ✅ | Projective.lean:50 |
| ell_proj dimension function | ✅ | Projective.lean:55 |
| Valuation membership condition | ✅ PROVED | RRSpace.lean:64 |
| Monotonicity | ✅ PROVED | Projective.lean:61 |
| **Complete P¹ proof** | ✅ PROVED | DimensionGeneral.lean (NOT AdelicH1Full!) |
| Pole-clearing technique | ✅ PROVED | DimensionCore.lean |
| Weighted degree induction | ✅ PROVED | DimensionGeneral.lean |
| Surjective evaluation maps | ✅ PROVED | DimensionGeneral.lean |
| Gap bounds | ✅ PROVED | GapBoundGeneral.lean |

**What's Missing for Elliptic**:
- Negative degree case: prove L(D) = {0} when deg(D) < 0
- ConstantsValuationBound typeclass instance for elliptic

**Proof Strategy** (UPDATED):
The P¹ proof in **DimensionGeneral.lean** is ~80% reusable:
1. Uses strong induction on `degWeighted D`
2. Surjective evaluation φ: L(D+v) → κ(v)
3. Kernel is L(D), apply induction hypothesis
4. Works for ANY Dedekind domain with proper valuation properties

**Difficulty**: MEDIUM (3-5 cycles) - Better than expected!

---

### 3. `isDedekindDomain_coordRing` - Smooth curves have Dedekind coordinate rings

**Location**: `EllipticSetup.lean:105-107`
```lean
instance isDedekindDomain_coordinateRing (W : Affine F) [NonsingularCurve W] :
    IsDedekindDomain (CoordRing W) := by
  sorry -- Standard AG fact: smooth curves have Dedekind coordinate rings
```

**What Exists**:
| Component | Status | Location |
|-----------|--------|----------|
| NonsingularCurve typeclass | ✅ | EllipticSetup.lean:87 |
| IsDomain instance | ✅ | Mathlib |
| IsNoetherian (quotient) | ✅ | Mathlib (implicit) |
| IsFractionRing instance | ✅ | EllipticSetup.lean:119 |

**What's Missing**:
- `DimensionLEOne (CoordRing W)` - requires Krull dimension theory
- `IsIntegralClosure` - requires smoothness → regularity

**Why This Is Hard**:
1. Krull dimension theory: Need to show quotienting F[X,Y] by Weierstrass polynomial gives dim 1
2. Smoothness → regularity: Scheme-theoretic to ring-theoretic connection
3. Neither is in Mathlib for Weierstrass curves

**Difficulty**: VERY HARD (2-3 weeks, or keep as axiom)

**Recommendation**: Keep as axiom. This is a standard textbook fact that's orthogonal to RR content.

---

### 4. `instStrongApprox_P1` - Strong approximation for P¹

**Location**: `StrongApproximation.lean:115-127`
```lean
instance instStrongApprox_P1 : StrongApprox (Polynomial Fq) (RatFunc Fq) := by
  sorry -- CRT + local density
```

**What Exists** (surprisingly complete!):
| Component | Status | Location |
|-----------|--------|----------|
| StrongApprox typeclass | ✅ | StrongApproximation.lean:72 |
| Local density at infinity | ✅ PROVED | FullAdelesCompact.lean:262 |
| Local approximation | ✅ PROVED | FullAdelesCompact.lean:322 |
| Finite divisors lemma | ✅ PROVED | FullAdelesCompact.lean:370 |
| Global gluing | ✅ MOSTLY | RatFuncPairing.lean:1378 |
| `strong_approximation_ratfunc` | ✅ PROVED | RatFuncPairing.lean:1729 |

**What's Missing**:
- RestrictedProduct topology composition lemmas
- ~50-100 lines of topology wiring

**Difficulty**: MEDIUM (1-2 cycles) - Infrastructure exists, just needs wiring

---

### 5. `instStrongApprox_Elliptic` - Strong approximation for elliptic curves

**Location**: `StrongApproximation.lean:164-171`
```lean
instance instStrongApprox_Elliptic ... := by
  sorry -- Standard textbook (Weil, Cassels-Fröhlich)
```

**Why This Is Hard**:
- Non-PID ring (unlike polynomial ring)
- Requires deep adelic analysis
- Standard reference: Weil "Basic Number Theory" Ch. IV

**Difficulty**: VERY HARD (keep as axiom)

**Recommendation**: Axiomatize with textbook justification.

---

### 6. `euler_char_axiom` - Euler characteristic formula

**Location**: `EllipticRRData.lean:112-114` (if exists)

**Status**: **WE PROVED THIS!**

The `euler_characteristic` theorem in EulerCharacteristic.lean proves exactly this. Just need to wire it.

**Difficulty**: EASY (1 cycle) - Just connect existing proof

---

## Sorry Placeholders: Detailed Assessment

### Abstract.lean (4 sorries)

| Line | What | Difficulty | Notes |
|------|------|------------|-------|
| 294 | `IsLinearPlaceSupport` | MEDIUM | Alg. closed field fact |
| 312 | `IsLinearPlaceSupport` | MEDIUM | Duplicate of 294 |
| 345 | `IsLinearPlaceSupport` | MEDIUM | Duplicate of 294 |
| 351 | Non-vanishing Serre duality | HARD | Needs residue pairing |

**Quick win**: Extract single `IsLinearPlaceSupport` lemma for all 3 uses.

---

### AdelicH1Full.lean (3 sorries)

| Line | What | Difficulty | Notes |
|------|------|------------|-------|
| 811 | Deep negative infinity (effective) | HARD | K_S density |
| 1508 | Valuation bound arithmetic | MEDIUM | Clear from comments |
| 1519 | Deep negative infinity (non-effective) | HARD | Constrained strong approx |

**Context**: These are edge cases in strong approximation. The main cases are proved.

---

### EllipticH1.lean (2 sorries)

| Line | What | Difficulty | Notes |
|------|------|------------|-------|
| 213 | `riemann_roch_positive` | HARD | RR integration |
| 225 | `riemann_roch_full` | HARD | RR integration |

**Note**: These depend on the axioms above being discharged first.

---

## Priority Ranking

### Tier 1: Quick Wins (1-3 cycles each)

| Task | Effort | Impact |
|------|--------|--------|
| Wire `euler_char_axiom` to our proof | 1 cycle | Removes 1 axiom |
| P¹ strong approximation topology | 1-2 cycles | Removes 1 axiom |
| `IsLinearPlaceSupport` lemma | 1 cycle | Removes 3 sorries |
| Valuation bound (line 1508) | 1 cycle | Removes 1 sorry |

### Tier 2: Medium Work (3-6 cycles each)

| Task | Effort | Impact |
|------|--------|--------|
| `h1_finite_all` via Serre + mono | 2-3 cycles | Removes 1 axiom |
| `ell_finite_all` adapt from P¹ | 4-6 cycles | Removes 1 axiom |
| EllipticH1 RR integration | 2-3 cycles | Removes 2 sorries |

### Tier 3: Hard Work (6+ cycles each)

| Task | Effort | Impact |
|------|--------|--------|
| Deep negative infinity cases | 4-6 cycles | Removes 2 sorries |
| Non-vanishing Serre duality | 4-6 cycles | Removes 1 sorry |

### Tier 4: Keep as Axioms

| Task | Justification |
|------|---------------|
| `isDedekindDomain_coordRing` | Standard AG, orthogonal to RR |
| `instStrongApprox_Elliptic` | Deep number theory, textbook fact |

---

## Infrastructure Assets (What's Already Proved)

### Core Theorems (Sorry-Free)

| Theorem | File | Lines |
|---------|------|-------|
| `euler_characteristic` | EulerCharacteristic.lean | ~100 |
| `chi_additive` | EulerCharacteristic.lean | ~50 |
| `riemann_roch_from_euler` | EulerCharacteristic.lean | ~10 |
| `riemann_inequality_real` | RiemannInequality.lean | 250 |
| All exactness lemmas | EulerCharacteristic.lean | ~800 |
| Connecting homomorphism δ | EulerCharacteristic.lean | ~300 |

### Supporting Infrastructure (Sorry-Free)

| Component | File | Status |
|-----------|------|--------|
| DVR for adic completion | DedekindDVR.lean | ✅ PROVED |
| Residue field isomorphism | ResidueFieldIso.lean | ✅ PROVED |
| Kernel = L(D) | KernelProof.lean | ✅ PROVED |
| Gap bounds | DimensionCounting.lean | ✅ PROVED |
| H¹ surjection | AdelicH1v2.lean | ✅ PROVED |
| Local density | FullAdelesCompact.lean | ✅ PROVED |
| Finite adele gluing | RatFuncPairing.lean | ✅ PROVED |

### Total Lines of Proved Code

| Category | Lines |
|----------|-------|
| Core infrastructure | ~3,700 |
| Euler characteristic | ~1,300 |
| Strong approximation (partial) | ~2,000 |
| **Total proved** | **~7,000** |

---

## Recommended Attack Order

### Phase 8a: Quick Wins (Cycles 340-343)
1. Wire euler_char_axiom
2. P¹ strong approximation topology
3. IsLinearPlaceSupport lemma
4. Valuation bound (line 1508)

**Expected result**: 1 axiom removed, 4 sorries removed

### Phase 8b: Finiteness (Cycles 344-350)
1. h1_finite_all via Serre duality approach
2. ell_finite_all adapted from P¹

**Expected result**: 2 axioms removed

### Phase 8c: Integration (Cycles 351-355)
1. EllipticH1 RR integration (uses 8b results)
2. Deep negative infinity cases

**Expected result**: 4 sorries removed

### Phase 8d: Hard Remaining (Cycles 356-360)
1. Non-vanishing Serre duality
2. Any remaining edge cases

**Expected result**: Complete or near-complete

### Keep as Axioms
- `isDedekindDomain_coordRing` - Justify in docs
- `instStrongApprox_Elliptic` - Justify in docs

---

## Success Metrics

For Litt's challenge:
```bash
# Check foundational axioms only
#print axioms riemann_roch_from_euler
# Expected: [propext, Classical.choice, Quot.sound]

# Check no sorries
grep -rn "sorry" RrLean/RiemannRochV2 --include="*.lean" | grep -v Archive | wc -l
# Expected: 0

# Check no axiom declarations
grep -rn "^axiom " RrLean/RiemannRochV2 --include="*.lean" | wc -l
# Expected: 0
```

---

## References

- **Litt's Challenge**: https://twitter.com/littmath/status/1868344897046298846
- **Weil, Basic Number Theory**: Ch. IV (strong approximation)
- **Cassels-Fröhlich**: Algebraic Number Theory (adelic methods)
- **Rosen, Number Theory in Function Fields**: Ch. 6 (Weil differentials)

---

*Generated Cycle 339. Updated Cycle 341 with infrastructure discoveries.*
*Core proof complete. More reusable infrastructure exists than expected!*
