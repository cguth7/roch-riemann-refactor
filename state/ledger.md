# Riemann-Roch Formalization Ledger

---

## Mission

**Goal**: Prove Riemann-Roch for curves over algebraically closed fields in Lean 4, using only the standard 3 foundational axioms (propext, Classical.choice, Quot.sound).

**Motivation**: Daniel Litt's Twitter challenge (Dec 15, 2025) - a fully formalized RR theorem.

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 361
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

#### Sorry Placeholders (13 found - updated Cycle 360)

| File | Count | Lines | Notes |
|------|-------|-------|-------|
| Abstract.lean | 8 | 200,201,203,294,299,312,345,351 | P¹ instance, IsLinearPlaceSupport |
| AdelicH1Full.lean | 3 | 757,1458,2309 | Strong approx + residue surj |
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

#### Track A: Adelic Compactness → H¹ Finiteness (PARKED - P¹ only)
**Goal**: Prove A_K/K is compact (or locally compact with discrete K)
**Status**: PARKED. This track is P¹-specific and does not generalize to arbitrary genus.

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

### Active Edge for Cycle 361

**PIVOT**: Track A (Compactness) deprioritized in favor of Track C (Serre Duality).

**Reason**: The Track A sorry (`constantToResidue_FqtInfty_surjective`) is P¹-specific. It proves ResidueField(FqtInfty Fq) ≅ Fq by extracting leading coefficients from RatFunc. This work doesn't generalize to higher genus curves.

**Better path**: Track C gives `h1_finite_all` via `ell_finite_all` (already proved!) through the perfect pairing H¹(D) ≅ L(K-D)*. This is:
- More general (works for any smooth projective curve)
- Avoids P¹-specific topology arguments
- Solves multiple axioms at once (h1_finite + serre_duality)

**Track A sorries (PARKED - P¹ only, does not generalize)**:
- `constantToResidue_FqtInfty_surjective` (AdelicH1Full.lean:2309) - P¹ only
- Strong approximation sorries (lines 757, 1458) - P¹ only

---

### Track C: Serre Duality - Next Steps

**Goal**: Construct perfect pairing φ: H¹(D) × L(K-D) → Fq

**Infrastructure status** (Cycle 361):
| Component | Location | Status |
|-----------|----------|--------|
| DVR for completions | DedekindDVR.lean | ✅ DONE (general) |
| Uniformizer existence | DedekindDVR.lean | ✅ DONE |
| Residue field isomorphism | ResidueFieldIso.lean | ✅ DONE |
| **Local residue map res_v** | LocalResidue.lean | ❌ NEEDED (Option 3) |
| Raw pairing ψ(a,f) = Σ res_v(a_v·f) | PairingDescent.lean | ❌ NEEDED |
| Pairing vanishes on K + A(D) | PairingDescent.lean | ❌ NEEDED |
| Non-degeneracy | PairingNondegenerate.lean | ❌ NEEDED |

**The Core Problem** (documented in RatFuncPairing.lean:2211-2221):

Current residue infrastructure is on **RatFunc**, not **adicCompletion** elements.
For H¹(D) = A_K / (K + A(D)), representatives a ∈ A_K have components a_v ∈ K_v (completions).

**IMPORTANT: We target genus-N Riemann-Roch. Do NOT fall back to P¹/RatFunc tricks.**

**Approaches** (in priority order):

**Option 3: Minimal residue map on completions (PREFERRED)**
- Build `res_v : K_v → κ(v)` using DVR + uniformizer structure
- Minimal API needed:
  1. `res_v : K_v →ₗ[k] κ(v)` - linear map on completion
  2. `res_v` vanishes on valuation ring O_v (bounded elements)
  3. Compatibility with global residue theorem on K
- Uses "coefficient of π⁻¹" without full `K_v ≃ LaurentSeries` isomorphism
- **Status**: DVR infrastructure exists (`DedekindDVR.lean`), uniformizers exist
- **Gap**: Need to define the coefficient extraction map

**Option 1: Full Laurent series isomorphism (FALLBACK if Option 3 stalls)**
- Build general `v.adicCompletion K ≃+* LaurentSeries κ(v)`
- More foundational but heavier lift
- Mathlib has this for X-adic only, not general places

**Option 2: Weak approximation (REJECTED - do not use)**
- P¹-specific, fails for deg D < -1 (Cycle 349)
- Creates circularity (depends on strong approximation axiom)
- Does NOT generalize to genus > 0

---

**File structure plan**:

```
RrLean/RiemannRochV2/SerreDuality/General/
├── LocalResidue.lean       # res_v : K_v → κ(v) via uniformizer
├── PairingDescent.lean     # Raw pairing + descent to quotient
└── PairingNondegenerate.lean  # Non-degeneracy + serre_duality
```

- `LocalResidue.lean`: NEW FILE
  - Define `localResidue_v : v.adicCompletion K →ₗ[k] κ(v)`
  - Use DVR structure + uniformizer (NOT RatFunc-specific)
  - Prove vanishing on O_v
  - Prove compatibility with residue theorem

- `PairingDescent.lean`: imports LocalResidue, AdelicH1Full
  - Define raw pairing ψ(a, f) = Σ_v res_v(a_v · f)
  - Prove pairing vanishes on K + A(D)
  - Induced pairing on H¹(D) × L(K-D)

- `PairingNondegenerate.lean`: imports PairingDescent, Abstract
  - Prove non-degeneracy
  - Derive serre_duality

**Cycle 361 target**:
1. Create `LocalResidue.lean` skeleton
2. Define `localResidue_v` using DVR + uniformizer structure
3. Prove it vanishes on O_v (valuation ring)
4. If blocked, document gap and reassess Option 1

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

*Cycles 340-360 archived to ledger_archive.md (Track A work, P¹-specific)*

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

*Updated Cycle 361. Phase 9 continues - Track C (Serre Duality) is the active edge. Key blocker: quotient pairing descent. Once perfect pairing H¹(D) × L(K-D) → Fq is constructed, h1_finite follows from ell_finite via duality.*
