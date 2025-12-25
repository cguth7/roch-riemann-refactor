# Refactor Plan: P¹ → Arbitrary Curves

**Status**: P¹ complete for algebraically closed fields (Cycle 287)
**Goal**: Riemann-Roch for algebraically closed curves of any genus

---

## Quick Reference

| Phase | Status | Key Achievement |
|-------|--------|-----------------|
| 0-4 | ✅ Complete | P¹ infrastructure, Serre duality |
| 4.5 | ✅ Complete | Valuation-degree, IsLinearPlaceSupport fix |
| 5 | ⏸️ Deferred | Edge case cleanup (low priority) |
| 6 | ⏳ **Active** | Elliptic curves (genus 1) |
| 7 | Future | Hyperelliptic curves (genus ≥ 2) |

---

## Phase 6: Elliptic Curves (Current)

**Goal**: Instantiate `ProjectiveAdelicRRData` for genus 1.

### Mathlib Provides

```lean
-- In Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:
abbrev CoordinateRing := ...           -- F[X,Y]/(Weierstrass eqn)
abbrev FunctionField := FractionRing CoordinateRing
```

### What We Need to Check/Build

| Component | Status | Notes |
|-----------|--------|-------|
| `CoordinateRing` is `IsDedekindDomain` | ❓ Check | Required for HeightOneSpectrum |
| Places = HeightOneSpectrum | ❓ Depends on above | Points on the curve |
| Canonical divisor (deg 0) | 📝 Define | K = 0 for genus 1 |
| Strong approximation | 📝 Prove | Main work |

### Key Differences from P¹

| Aspect | P¹ (genus 0) | Elliptic (genus 1) |
|--------|--------------|-------------------|
| H¹(O) | 0 | 1-dimensional |
| deg(K) | -2 | 0 |
| Serre duality | trivial (0=0) | non-trivial |

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

---

## Architecture for New Curves

```lean
-- The typeclass we instantiate:
class ProjectiveAdelicRRData (k : Type*) [Field k]
    (canonical : ExtendedDivisor R) (genus : ℕ) where
  h1_finite : ∀ D, Module.Finite k (SpaceModule_full k D)
  ell_finite : ∀ D, Module.Finite k (RRSpace_proj_ext k D)
  h1_vanishing : ∀ D, D.deg > 2*genus - 2 → h1_finrank k D = 0
  serre_duality : ∀ D, h1_finrank k D = ell_proj_ext k (canonical - D)
  deg_canonical : canonical.deg = 2*genus - 2
```

---

*Updated Cycle 287: P¹ complete for alg. closed, beginning elliptic curve phase.*
