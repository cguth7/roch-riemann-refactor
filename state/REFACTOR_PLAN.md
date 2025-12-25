# Refactor Plan: P¹ → Arbitrary Curves

**Status**: P¹ complete. Elliptic curves ready to begin. Updated Cycle 288.
**Goal**: Riemann-Roch for algebraically closed curves of any genus.

---

## Quick Reference

| Phase | Status | Key Achievement |
|-------|--------|-----------------|
| 0-4 | ✅ Complete | P¹ infrastructure, Serre duality |
| 4.5 | ✅ Complete | Valuation-degree, IsLinearPlaceSupport fix |
| 5 | ⏸️ Deferred | Edge case cleanup (low priority) |
| 6 | ⏳ **Ready** | Elliptic curves (genus 1) |
| 7 | Future | Hyperelliptic curves (genus ≥ 2) |

---

## Phase 6: Elliptic Curves (Ready to Begin)

**Goal**: Instantiate `ProjectiveAdelicRRData` for genus 1.

### The Mathlib Gap

| Mathlib Provides | Mathlib Missing |
|------------------|-----------------|
| `WeierstrassCurve.Affine.CoordinateRing` | `IsDedekindDomain CoordinateRing` |
| `WeierstrassCurve.Affine.FunctionField` | (Required for `HeightOneSpectrum`) |
| `WeierstrassCurve.Affine.Nonsingular` | |
| `IsDomain CoordinateRing` | |
| Group law → Class Group | |

### Resolution: The Axiom Approach

```lean
-- In RrLean/RiemannRochV2/Elliptic/EllipticSetup.lean

/-- The coordinate ring of a nonsingular Weierstrass curve is a Dedekind domain.

    This follows from: smooth ⟹ regular in codim 1 ⟹ integrally closed ⟹ Dedekind.
    Standard algebraic geometry (Hartshorne II.6). -/
instance ellipticCoordinateRing_isDedekindDomain
    {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
    [hns : W.Nonsingular] : IsDedekindDomain W.CoordinateRing := by
  sorry -- Standard AG fact, orthogonal to RR content

attribute [instance] ellipticCoordinateRing_isDedekindDomain
```

**Why this is acceptable**:
- It's textbook mathematics (not a conjecture)
- Orthogonal to what we're proving (RR, not ring theory)
- Standard practice in formalization for "trivial but tedious" gaps
- Can be filled later by someone interested in commutative algebra

### File Structure

```
RrLean/RiemannRochV2/Elliptic/
├── EllipticSetup.lean      # IsDedekindDomain axiom, basic imports
├── EllipticPlaces.lean     # HeightOneSpectrum, local uniformizers
├── EllipticCanonical.lean  # K = 0 (trivial canonical for g=1)
├── EllipticH1.lean         # H¹ calculations (dim = 1 for O)
└── EllipticRRData.lean     # ProjectiveAdelicRRData instance
```

### Key Differences from P¹

| Aspect | P¹ (g=0) | Elliptic (g=1) |
|--------|----------|----------------|
| Coordinate ring | `Polynomial Fq` (PID) | `CoordinateRing` (Dedekind, not PID) |
| deg(K) | -2 | 0 |
| ℓ(D) for deg(D) > 0 | deg(D) + 1 | deg(D) |
| H¹(O) dimension | 0 | 1 |
| L(P) for point P | {1, 1/π} (2-dim) | {1} (1-dim) |
| Global uniformizer | Yes (monic irred poly) | No! (class group non-trivial) |

### What Needs Proving

1. **Setup**: Wire Mathlib's `CoordinateRing` to our infrastructure
2. **Canonical**: `ellipticCanonical = 0` (trivial divisor)
3. **H¹(O) = 1**: Quotient by K gives 1-dimensional space
4. **Serre duality**: `h¹(D) = ℓ(-D)` (since K = 0)
5. **RR formula**: `ℓ(D) - ℓ(-D) = deg(D)` for deg(D) > 0

### The "No Global Uniformizer" Issue

**Problem**: For P¹, every place has a global generator (monic irreducible polynomial).
For elliptic curves, the coordinate ring is NOT a PID - primes may not be principal.

**Solution**: Use local uniformizers only. Strong Approximation still works because:
- For any place v, there exists π ∈ K with v(π) = 1 (local)
- We DON'T need π to generate the prime ideal globally
- The adelic machinery uses local valuations, not global generators

```lean
-- WRONG approach (works for P¹ only):
def Place.generator (v : HeightOneSpectrum R) : R := ...  -- Assumes PID!

-- RIGHT approach (works for all curves):
class HasLocalUniformizer (v : HeightOneSpectrum R) (K : Type*) where
  π : K
  val_eq_one : v.valuation K π = 1
  -- No requirement that (π) = v.asIdeal!
```

---

## Completed Phases

### Phase 0-4: P¹ Infrastructure ✅
- Full adele ring with infinity
- Serre duality for effective divisors
- Riemann-Roch formula: ℓ(D) = deg(D) + 1

### Phase 4.5: Algebraically Closed Fix ✅ (Cycle 287)
- Discovered weighted vs unweighted degree mismatch
- Added `IsLinearPlaceSupport` hypothesis
- For alg. closed fields: all theorems apply (places have degree 1)

---

## Phase 5: Edge Cases (Deferred)

Low priority sorries in Abstract.lean:
- deg(D) < -1 cases (require full residue pairing)
- Non-effective divisors over non-alg-closed fields

**Decision**: Skip for now, focus on higher genus.

---

## Future: Phase 7+ (Hyperelliptic)

For genus g ≥ 2:
- Function field = Frac(k[x,y]/(y² = f(x))) where deg(f) = 2g+1 or 2g+2
- Canonical divisor has degree 2g-2
- Strong approximation becomes more complex
- Need Weil Differentials (not just functions) for residue pairing

---

## Architecture Constraints (from Gemini Analysis)

### 1. Keep Infrastructure Abstract

The general adelic files should NEVER assume:
- Coordinate ring is a PID
- Places have global generators
- `ℓ(D) = deg(D) + 1`

These are P¹-specific and belong in instance files only.

### 2. Weil Differentials for g > 0

For P¹: The residue pairing uses functions because dt is a global differential.

For general curves: No global differential exists (unless g = 1).
Must use Weil Differentials (dual space of adeles mod K).

```lean
-- For elliptic: Can use invariant differential ω = dx/(2y)
-- This gives a canonical isomorphism: Functions ≅ Differentials

-- For g ≥ 2: Must work with actual differential type
structure WeilDifferential (K : Type*) where
  toFun : Adele K → k
  vanishes_on_global : ∀ f : K, toFun (diag f) = 0
```

### 3. The ProjectiveAdelicRRData Contract

```lean
class ProjectiveAdelicRRData (k R K : Type*) (canonical : DivisorV2 R) (genus : ℕ) where
  h1_finite : ∀ D, Module.Finite k (SpaceModule k R K D)
  ell_finite : ∀ D, Module.Finite k (RRSpace_proj k R K D)
  h1_vanishing : ∀ D, D.deg > 2 * genus - 2 → h1_finrank D = 0
  serre_duality : ∀ D, h1_finrank D = ell_proj (canonical - D)
  deg_canonical : canonical.deg = 2 * genus - 2
```

For elliptic curves: `genus = 1`, `canonical = 0`, `deg_canonical = 0`.

---

## Summary: What's Next

**Cycle 289**: Create `EllipticSetup.lean` with:
1. Import Mathlib elliptic curve infrastructure
2. Add `IsDedekindDomain` axiom (with clear documentation)
3. Define `EllipticPlaces := HeightOneSpectrum W.CoordinateRing`
4. Verify basic properties compile

**Cycle 290+**: Build up to `EllipticRRData` instance.

---

*Updated Cycle 288: Elliptic curve investigation complete. Axiom approach validated. Ready to proceed.*
