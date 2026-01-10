# Refactor Plan: Phase 8 - Axiom Elimination

**Status**: Phase 8 Planned. Core RR proof complete.
**Goal**: Eliminate all `axiom` declarations to satisfy Litt's challenge.

---

## Current State (Cycle 339)

### Completed

| Phase | Achievement |
|-------|-------------|
| 1-4 | P¹ infrastructure |
| 5 | P¹ edge cases (archived) |
| 6 | Elliptic instances |
| 7 | **Euler characteristic PROVED** |

### The Core Proof is Done

- `euler_characteristic`: χ(D) = deg(D) + 1 - g ✅
- `chi_additive`: χ(D+v) = χ(D) + 1 ✅
- `riemann_roch_from_euler`: Full RR ✅
- 6-term exact sequence: All proved ✅

---

## Phase 8: Axiom Elimination

### What Must Be Eliminated

#### Axiom Declarations (6)

| Axiom | File | Strategy | Difficulty |
|-------|------|----------|------------|
| `euler_char_axiom` | EllipticRRData | Wire to our proof | Easy |
| `h1_finite_all` | EllipticRRData | Compactness of A_K/K | Medium |
| `ell_finite_all` | EllipticRRData | RRSpace theory | Medium |
| `isDedekindDomain_coordRing` | EllipticSetup | AG: smooth → Dedekind | Medium-Hard |
| `strong_approx_K` | StrongApproximation | Function field density | Hard |
| `strong_approx_places` | StrongApproximation | Function field density | Hard |

#### Sorry Placeholders (~7)

| Location | Description | Difficulty |
|----------|-------------|------------|
| Abstract.lean (3) | Instance wiring | Medium |
| AdelicH1Full.lean (2) | Strong approx edge cases | Hard |
| EllipticH1.lean (2) | Elliptic-specific | Medium |

---

## Implementation Plan

### Cycle 340: Remove euler_char_axiom (Easy Win)

We proved `euler_characteristic`! Just wire it to replace the axiom.

```lean
-- Before (axiom)
axiom euler_char_axiom (D : DivisorV2 R) : χ(D) = deg(D) + 1 - g

-- After (use our theorem)
theorem euler_char_axiom (D : DivisorV2 R) : χ(D) = deg(D) + 1 - g :=
  euler_characteristic k R K D genus ⟨...⟩ h_genus h_ell_zero
```

### Cycles 341-343: Finiteness Axioms

**h1_finite_all**: H¹(D) = A_K/(K + A_K(D)) is finite-dimensional.
- Key: A_K/K is compact (already have infrastructure)
- Quotient of compact by closed is compact
- Compact k-vector space is finite-dimensional

**ell_finite_all**: L(D) is finite-dimensional.
- Already have RRSpace theory
- May need to connect to existing lemmas

### Cycles 344-347: isDedekindDomain_coordRing

Standard AG fact: coordinate rings of smooth affine curves are Dedekind.

Needs:
- Integrally closed (smooth → normal)
- Noetherian (affine variety)
- Dimension 1 (curve)

May require importing/developing AG infrastructure.

### Cycles 348-355: Strong Approximation (Hard)

The real blockers. Need to prove:
- K is dense in finite adeles (weak approximation)
- With prescribed behavior at finitely many places

This requires function field arithmetic.

### Cycles 356-360: Remaining Sorries

Clean up abstraction layer instances and edge cases.

---

## Estimated Timeline

| Task | Cycles | Confidence |
|------|--------|------------|
| Remove euler_char_axiom | 1 | High |
| Finiteness axioms | 2-3 | Medium |
| Dedekind domain | 2-4 | Medium |
| Strong approximation | 4-8 | Low |
| Remaining sorries | 3-5 | Medium |
| **Total** | **12-21** | |

---

## Success Criteria

For Litt's challenge:
1. No `axiom` declarations (except Lean's foundational 3)
2. No `sorry` placeholders
3. Build passes cleanly
4. `#print axioms riemann_roch_from_euler` shows only propext/choice/quot.sound

---

## Key Infrastructure (Already Done)

| Asset | Lines | Status |
|-------|-------|--------|
| Core infrastructure | 3,700+ | ✅ Sorry-free |
| Euler characteristic | ~500 | ✅ Sorry-free |
| Riemann inequality | 250 | ✅ Sorry-free |
| 6-term exact sequence | ~800 | ✅ Sorry-free |
| H¹ framework | 550 | ✅ Done |
| Compactness | 300 | ✅ Done |

---

*Updated Cycle 339. Phase 8: Eliminate axioms for full formalization.*
