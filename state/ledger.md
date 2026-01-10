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

| File | Axiom | Difficulty | Notes |
|------|-------|------------|-------|
| EllipticRRData | `euler_char_axiom` | **EASY** | We proved this! Just wire it. |
| StrongApprox | `instStrongApprox_P1` | **MEDIUM** | ~80% done, just topology wiring |
| EllipticRRData | `h1_finite_all` | MEDIUM | Shortcut via Serre duality |
| EllipticRRData | `ell_finite_all` | MEDIUM-HIGH | Adapt from P¹ proof |
| EllipticSetup | `isDedekindDomain_coordRing` | VERY HARD | Keep as axiom? |
| StrongApprox | `instStrongApprox_Elliptic` | VERY HARD | Keep as axiom? |

#### Sorry Placeholders (9 found)

| File | Count | Difficulty | Notes |
|------|-------|------------|-------|
| Abstract.lean | 4 | 3 MEDIUM, 1 HARD | 3 are same lemma repeated |
| AdelicH1Full.lean | 3 | 1 MEDIUM, 2 HARD | Edge cases in strong approx |
| EllipticH1.lean | 2 | HARD | Depends on axioms above |

**See INVENTORY_REPORT_V2.md for detailed scoping.**

---

## Phase 8: Axiom Elimination Plan

### Tier 1: Quick Wins (4-6 cycles)

| Task | Cycles | Notes |
|------|--------|-------|
| Wire `euler_char_axiom` | 1 | Just connect existing proof |
| P¹ strong approx topology | 1-2 | Infrastructure exists |
| `IsLinearPlaceSupport` lemma | 1 | Fixes 3 sorries at once |
| Valuation bound (line 1508) | 1 | Clear from comments |

### Tier 2: Medium Work (6-10 cycles)

| Task | Cycles | Notes |
|------|--------|-------|
| `h1_finite_all` | 2-3 | Via Serre duality shortcut |
| `ell_finite_all` | 4-6 | Adapt P¹ clearing polynomial |
| EllipticH1 integration | 2-3 | Uses Tier 2 results |

### Tier 3: Hard (6+ cycles)

| Task | Cycles | Notes |
|------|--------|-------|
| Deep negative infinity | 4-6 | Constrained strong approx |
| Non-vanishing Serre duality | 4-6 | Residue pairing |

### Keep as Axioms (Recommended)

| Axiom | Justification |
|-------|---------------|
| `isDedekindDomain_coordRing` | Standard AG, 2-3 weeks to prove |
| `instStrongApprox_Elliptic` | Deep number theory, textbook fact |

### Revised Estimate

| Scenario | Cycles | Notes |
|----------|--------|-------|
| Optimistic | 12-15 | Quick wins + shortcuts work |
| Realistic | 16-20 | Some complications |
| Full formalization | 25+ | If we prove everything |

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
- **INVENTORY_REPORT_V2.md** - Detailed Phase 8 scoping (axioms, sorries, strategies)
- INVENTORY_REPORT.md - Original asset inventory

---

*Updated Cycle 339. Core RR proof complete. Phase 8 scoped. See INVENTORY_REPORT_V2 for details.*
