# Riemann-Roch Formalization Ledger

---

## Mission

**Goal**: Prove Riemann-Roch for curves over algebraically closed fields in Lean 4, using only the standard 3 foundational axioms (propext, Classical.choice, Quot.sound).

**Motivation**: Daniel Litt's Twitter challenge (Dec 15, 2025) - a fully formalized RR theorem.

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 339
**Phase**: 8 (Axiom Elimination) - PLANNED

### What We Have (Core RR Proof Complete)

| Theorem | Status | Notes |
|---------|--------|-------|
| `euler_characteristic` | ✅ PROVED | χ(D) = deg(D) + 1 - g |
| `chi_additive` | ✅ PROVED | χ(D+v) = χ(D) + 1 |
| 6-term exact sequence | ✅ PROVED | All exactness lemmas complete |
| `riemann_roch_from_euler` | ✅ PROVED | Full RR via Euler + Serre duality |

### What Blocks Litt's Challenge

The proof uses only propext/choice/quot.sound BUT has `axiom` declarations and `sorry` placeholders that need elimination:

#### Axiom Declarations (6) - Must Become Theorems

| File | Axiom | Description | Difficulty |
|------|-------|-------------|------------|
| EllipticRRData.lean | `h1_finite_all` | H¹(D) is finite-dim for all D | Medium |
| EllipticRRData.lean | `ell_finite_all` | L(D) is finite-dim for all D | Medium |
| EllipticSetup.lean | `isDedekindDomain_coordRing` | Smooth curves → Dedekind | Medium-Hard |
| EllipticRRData.lean | `euler_char_axiom` | χ(D) = deg(D) + 1 - g | **DONE** (can remove) |
| StrongApproximation.lean | (2 axioms) | Function field density | Hard |

#### Sorry Placeholders (~7)

| File | Location | Description | Difficulty |
|------|----------|-------------|------------|
| Abstract.lean | 3 sorries | Abstraction layer instances | Medium |
| AdelicH1Full.lean | 2 sorries | Strong approximation cases | Hard |
| EllipticH1.lean | 2 sorries | Elliptic-specific H1 | Medium |

---

## Phase 8: Axiom Elimination Plan

### Priority Order

1. **Remove `euler_char_axiom`** (Easy)
   - We proved this! Just need to wire the proof to replace the axiom.

2. **Prove finiteness axioms** (Medium)
   - `h1_finite_all`: Use compactness of A_K/K
   - `ell_finite_all`: From RRSpace theory already developed

3. **Prove `isDedekindDomain_coordRing`** (Medium-Hard)
   - Standard AG fact: smooth affine curves have Dedekind coordinate rings
   - May need to import/develop integrally closed + Noetherian + dim 1

4. **Strong approximation axioms** (Hard)
   - These are the real blockers
   - Need function field density arguments

5. **Clear remaining sorries** (Varies)
   - Abstract.lean: Instance wiring
   - AdelicH1Full.lean: Edge cases in strong approximation
   - EllipticH1.lean: Elliptic-specific facts

### Estimated Work

| Task | Cycles | Confidence |
|------|--------|------------|
| Remove euler_char_axiom | 1 | High |
| Finiteness axioms | 2-3 | Medium |
| Dedekind domain | 2-4 | Medium |
| Strong approximation | 4-8 | Low |
| Remaining sorries | 3-5 | Medium |
| **Total** | **12-21** | |

---

## Recent Cycles

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
- [Rosen Ch. 6](https://link.springer.com/chapter/10.1007/978-1-4757-6046-0_6) - Weil Differentials
- INVENTORY_REPORT.md - Full asset inventory

---

*Updated Cycle 339. Core RR proof complete. Phase 8: Eliminate axioms for Litt challenge.*
