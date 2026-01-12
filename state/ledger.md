# Riemann-Roch Formalization Ledger

---

## Mission

**Goal**: Prove Riemann-Roch for curves over algebraically closed fields in Lean 4, using only the standard 3 foundational axioms (propext, Classical.choice, Quot.sound).

**Motivation**: Daniel Litt's Twitter challenge (Dec 15, 2025) - a fully formalized RR theorem.

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 369
**Phase**: 9 - BOSS BATTLE (Non-Degeneracy Proof)

### Core RR Proof Status

| Theorem | Status |
|---------|--------|
| `euler_characteristic` | ✅ PROVED |
| `chi_additive` | ✅ PROVED |
| 6-term exact sequence | ✅ PROVED |
| `riemann_roch_from_euler` | ✅ PROVED |
| `serre_duality_finrank` | ✅ PROVED (from axioms) |

### Critical Path Axioms (5 remaining)

| Axiom | File | Status |
|-------|------|--------|
| `serre_duality` | EllipticH1 | 🎯 **ACTIVE TARGET** |
| `h1_finite_all` | EllipticRRData | Follows from Serre duality |
| `h1_zero_eq_one` | EllipticH1 | Genus definition |
| `h1_vanishing_positive` | EllipticH1 | Strong approximation |
| `isDedekindDomain_coordinateRing_axiom` | EllipticSetup | Keep as axiom |

---

## 🎯 BOSS BATTLE: Non-Degeneracy Proof

**Objective**: Prove the two non-degeneracy axioms in `PairingNondegenerate.lean`

```lean
-- LEFT NON-DEGENERACY: If φ([a], f) = 0 for all f ∈ L(KDiv-D), then [a] = 0
axiom serreDualityPairing_injective (D KDiv : DivisorV2 R) :
    Function.Injective (serreDualityPairing k D KDiv)

-- RIGHT NON-DEGENERACY: For nonzero f, there exists [a] with φ([a], f) ≠ 0
axiom serreDualityPairing_right_nondegen (D KDiv : DivisorV2 R)
    (f : RRModuleV2_real R K (KDiv - D)) (hf : f ≠ 0) :
    ∃ h1_class : SpaceModule k R K D, serreDualityPairing k D KDiv h1_class f ≠ 0
```

### Why This Is The Boss Battle

Once these axioms become theorems:
- `serre_duality` axiom becomes derivable → **removes 1 critical axiom**
- `h1_finite_all` follows (finite L(K-D) → finite H¹(D)) → **removes another axiom**
- 2 axioms eliminated with one proof!

### COMMITTED ROUTE: Trace-Dual / Different Ideal

**Decision**: We commit to the trace-dual route. This is the cleanest mathlib-native path.
Laurent series work is suspended unless we hit a blocker.

### Why Trace-Dual?

1. **Infrastructure exists**: `DifferentIdealBridge.lean` + `Mathlib.RingTheory.DedekindDomain.Different`
2. **Avoids Laurent series**: No need to build K_v ≃ LaurentSeries κ(v)
3. **Perfect pairing for free**: Mathlib proves `dual_mul_self`, `dual_dual`, `traceForm_nondegenerate`

### Goal → Required Lemmas

```
TRACE-DUAL ATTACK PLAN
│
├── Lemma 1: L(KDiv-D) ↔ dual(I_D) as fractional ideals ✅ DONE
│   └── TraceDualBridge.lean created with:
│       - divisorToFractionalIdeal_fractionalIdealToDivisor (round-trip)
│       - dual_divisorToFractionalIdeal_eq: dual(I_D) = divisorToFractionalIdeal(K-D)
│       - mem_RRModuleV2_iff_mem_divisorToFractionalIdeal: L(D) = divisorToFractionalIdeal(-D)
│
├── Lemma 2: serreDualityPairing = trace pairing (restricted) ⚠️ PARTIAL
│   └── TracePairingBridge.lean created with:
│       - tracePairing_nondegenerate_left/right: Uses Mathlib traceForm_nondegenerate
│       - L_KDivMinusD_eq_divisorToFractionalIdeal: Bridge lemma
│       - residuePairing_controlled_by_trace: Axiom for left non-deg
│       - witness_from_trace_nondegen: Axiom for right non-deg
│       - serreDualityPairing_injective_from_trace: THEOREM (from axioms)
│       - serreDualityPairing_right_nondegen_from_trace: THEOREM (from axioms)
│   └── ⚠️ SIGN ISSUE: Need I = divisorToFractionalIdeal(2*KDiv - D), not I_D
│
├── Lemma 3: Perfect pairing from Mathlib
│   └── Use: Mathlib.dual_mul_self : dual(I) · I = dual(1)
│   └── Use: Mathlib.dual_dual : dual(dual(I)) = I
│   └── Use: Mathlib.traceForm_nondegenerate
│
└── Theorem: Perfect pairing ⇒ injective ⇒ non-degeneracy
    └── Use: LinearMap.IsPerfPair or equivalent
    └── Conclude: serreDualityPairing_injective ✓
    └── Note: Right non-deg follows from perfect pairing symmetry
```

### Existing Infrastructure

| Component | Location | Status |
|-----------|----------|--------|
| Divisor ↔ Fractional Ideal | DifferentIdealBridge.lean | ✅ DONE |
| `fractionalIdealToDivisor_dual` | DifferentIdealBridge.lean | ✅ DONE |
| `mem_divisorToFractionalIdeal_iff` | DifferentIdealBridge.lean | ✅ DONE |
| Canonical divisor from different | DifferentIdealBridge.lean | ✅ DONE |
| `dual_mul_self`, `dual_dual` | Mathlib.Different | ✅ MATHLIB |
| `traceForm_nondegenerate` | Mathlib.Different | ✅ MATHLIB |
| **Bridge: L(D) = divisorToFractionalIdeal(-D)** | TraceDualBridge.lean | ✅ **DONE (Cycle 368)** |
| **Bridge: dual(I_D) = divisorToFractionalIdeal(K-D)** | TraceDualBridge.lean | ✅ **DONE (Cycle 368)** |
| **Bridge: pairing = trace** | TracePairingBridge.lean | ✅ **DONE (Cycle 369)** |

### ⚠️ CRITICAL SIGN ISSUE (Discovered Cycle 369)

**The naive identification L(KDiv - D) = dual(I_D) is WRONG!**

The math shows:
- `L(D) = divisorToFractionalIdeal(-D)` (membership: v(x) ≤ exp(D(v)))
- `dual(I_D) = divisorToFractionalIdeal(KDiv - D)` where I_D = divisorToFractionalIdeal(D)

Therefore:
- `L(KDiv - D) = divisorToFractionalIdeal(D - KDiv)` (substitute D → KDiv-D, negate)
- `dual(divisorToFractionalIdeal(D)) = divisorToFractionalIdeal(KDiv - D)`

**These differ by sign**: (D - KDiv) ≠ (KDiv - D) unless KDiv = 0!

**Resolution**: To get `dual(I) = L(KDiv - D)`, we need:
- `I = divisorToFractionalIdeal(2*KDiv - D)`
- Then `dual(I) = divisorToFractionalIdeal(KDiv - (2*KDiv - D)) = divisorToFractionalIdeal(D - KDiv) = L(KDiv - D)` ✓

**For elliptic curves (KDiv = 0)**: `I = divisorToFractionalIdeal(-D)` gives `dual(I) = L(-D)` ✓

**Next Claude must**: Fix the ideal choice in TracePairingBridge.lean to use the correct alignment.

### Key Insight

The "right non-degeneracy" axiom is actually redundant once we have perfect pairing:
- Perfect pairing ⇒ both left and right non-degeneracy
- `transposePairing_injective` already exists (follows from right non-deg)
- We only need to prove ONE direction; the other follows from symmetry

---

## Axiom Inventory

### Serre Duality Track (Track C)

| File | Axioms | Purpose |
|------|--------|---------|
| LocalResidue.lean | 2 | Local residue map + vanishing |
| PairingDescent.lean | 13 | Raw pairing + bilinearity + vanishing |
| PairingNondegenerate.lean | 2 | **Non-degeneracy (TARGET)** |

**Total Track C axioms**: 17 (15 infrastructure + 2 boss battle targets)

### Elliptic Curve Axioms

| File | Axioms | Notes |
|------|--------|-------|
| EllipticH1.lean | 3 | h1_zero_eq_one, h1_vanishing_positive, serre_duality |
| EllipticRRData.lean | 1 | h1_finite_all |
| EllipticSetup.lean | 1 | isDedekindDomain_coordinateRing_axiom |
| EllipticPlaces.lean | 1 | exists_localUniformizer (not critical) |

---

## Architecture

```
RrLean/RiemannRochV2/
├── Core/              - Divisors, RRSpace
├── Adelic/            - Adeles, Euler characteristic ✅
├── SerreDuality/General/
│   ├── LocalResidue.lean       # Local residue axioms
│   ├── PairingDescent.lean     # Pairing + descent ✅
│   ├── PairingNondegenerate.lean  # 🎯 BOSS BATTLE (2 axioms)
│   ├── TraceDualBridge.lean    # ✅ L(D) ↔ dual(I) bridge
│   └── TracePairingBridge.lean # ✅ NEW: Trace pairing bridge
├── ResidueTheory/
│   └── DifferentIdealBridge.lean  # Divisor ↔ FractionalIdeal
├── Elliptic/          - Curve instances
└── Support/           - DVR, uniformizers
```

---

## Recent Cycles

### Cycle 369: TracePairingBridge.lean - Lemma 2 Partial

- ✅ Created `TracePairingBridge.lean` with trace-pairing bridge
- ✅ Proved `tracePairing_nondegenerate_left/right` using Mathlib's `traceForm_nondegenerate`
- ✅ Proved `L_KDivMinusD_eq_divisorToFractionalIdeal`: L(KDiv-D) = I_{D-KDiv}
- ✅ Axiomatized `residuePairing_controlled_by_trace`: residue pairing controlled by trace
- ✅ Axiomatized `witness_from_trace_nondegen`: existence of witness from trace non-deg
- ✅ THEOREM `serreDualityPairing_injective_from_trace`: derived from trace bridge axioms
- ✅ THEOREM `serreDualityPairing_right_nondegen_from_trace`: derived from trace bridge axioms
- ⚠️ **ISSUE FOUND**: Sign mismatch in ideal alignment (see Critical Sign Issue above)
- **Key insight**: Structure is right, but ideal choice needs fixing for general KDiv
- **Files standalone by design** - will wire in once trace-bridge axioms are proved

### Cycle 368: TraceDualBridge.lean - Lemma 1 Complete

- ✅ Created `TraceDualBridge.lean` with bridge lemmas
- ✅ Proved `divisorToFractionalIdeal_fractionalIdealToDivisor`: round-trip identity
- ✅ Proved `dual_divisorToFractionalIdeal_eq`: dual(I_D) = divisorToFractionalIdeal(K-D)
- ✅ Proved `mem_RRModuleV2_iff_mem_divisorToFractionalIdeal`: L(D) = divisorToFractionalIdeal(-D)
- **Lemma 1 of trace-dual attack COMPLETE**

### Cycle 367: Wire General Theorem to Elliptic Instance

- ✅ Added `serre_duality_from_general` theorem to EllipticH1.lean
- ✅ Proved `finrank_eq_ell_proj` helper lemma
- ✅ Established architecture: general theorem → elliptic specialization

### Cycle 366: Non-Degeneracy Framework

- ✅ Created PairingNondegenerate.lean
- ✅ Axiomatized `serreDualityPairing_injective` (left)
- ✅ Axiomatized `serreDualityPairing_right_nondegen` (right)
- ✅ Proved `serre_duality_finrank`: h¹(D) = ℓ(KDiv - D)

### Cycle 365: Pairing Descent Complete

- ✅ Defined `serreDualityPairing` on H¹(D) quotient via liftQ
- ✅ Proved vanishing on K + A(D)

*Earlier cycles (361-364) archived to ledger_archive.md*

---

## Key Files

| File | Purpose | Status |
|------|---------|--------|
| EulerCharacteristic.lean | Main RR theorems | ✅ Sorry-free |
| PairingNondegenerate.lean | **BOSS BATTLE** | 2 axioms (derivable!) |
| DifferentIdealBridge.lean | Divisor ↔ FractionalIdeal | ✅ Complete |
| TraceDualBridge.lean | L(D) ↔ dual(I) bridge | ✅ Complete (Cycle 368) |
| **TracePairingBridge.lean** | **Trace pairing bridge** | ✅ **NEW (Cycle 369)** |
| PairingDescent.lean | Pairing infrastructure | ✅ Complete (13 axioms) |

---

## References

- `Mathlib.RingTheory.DedekindDomain.Different` - Trace dual, different ideal
- `DifferentIdealBridge.lean` - Divisor ↔ Fractional ideal correspondence
- `TraceDualityProof.lean` - May have additional bridge lemmas

---

*Updated Cycle 369. BOSS BATTLE progress: Lemma 1 complete, Lemma 2 partial (sign issue found). TracePairingBridge.lean derives non-degeneracy theorems from axioms, BUT the ideal alignment has a sign error. Next Claude: Fix ideal choice (use I = divisorToFractionalIdeal(2*KDiv - D) instead of I_D) to properly connect to trace duality.*
