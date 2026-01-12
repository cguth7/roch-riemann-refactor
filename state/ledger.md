# Riemann-Roch Formalization Ledger

---

## Mission

**Goal**: Prove Riemann-Roch for curves over algebraically closed fields in Lean 4, using only the standard 3 foundational axioms (propext, Classical.choice, Quot.sound).

**Motivation**: Daniel Litt's Twitter challenge (Dec 15, 2025) - a fully formalized RR theorem.

---

## Current State

**Build**: ✅ PASSING
**Cycle**: 368
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

### Attack Strategy

**Mathematical approach**: Show the residue pairing is non-degenerate.

For **left non-degeneracy**: If [a] ≠ 0 in H¹(D), construct f ∈ L(KDiv-D) with φ([a], f) ≠ 0.
- Idea: [a] ≠ 0 means a ∉ K + A(D), so a has "residual information" at some place
- Find f that "detects" this residue via the pairing

For **right non-degeneracy**: If f ≠ 0 in L(KDiv-D), construct [a] ∈ H¹(D) with φ([a], f) ≠ 0.
- Idea: f ≠ 0 has poles (at places where val < 0)
- Construct adele a that pairs non-trivially with f at a pole

### Required Infrastructure

| Component | Status | Notes |
|-----------|--------|-------|
| Pairing on quotient | ✅ DONE | `serreDualityPairing` via liftQ |
| Pairing formula | ✅ DONE | `φ([a], f) = fullRawPairing k a f.val` |
| Local residue | ✅ AXIOM | `localResidueHom : K_v →+ κ(v)` |
| Residue vanishes on O_v | ✅ AXIOM | `localResidue_vanishes_on_integers` |
| **Residue non-zero detection** | ❌ NEEDED | Key lemma for non-degeneracy |
| **Laurent series (maybe)** | ❓ TBD | May need K_v ≃ LaurentSeries κ(v) |

### Potential Approaches

**Option A: Direct residue analysis**
- For f with pole at v, show ∃ a_v with res_v(a_v · f) ≠ 0
- Construct global adele from local witness
- May avoid full Laurent series

**Option B: Laurent series infrastructure**
- Build K_v ≃ LaurentSeries κ(v)
- Residue = coefficient of t⁻¹
- More foundational, enables coefficient manipulation

**Option C: Duality via Tate's thesis style**
- Use self-duality of adeles
- More abstract but potentially cleaner

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
│   └── PairingNondegenerate.lean  # 🎯 BOSS BATTLE
├── Elliptic/          - Curve instances
└── Support/           - DVR, uniformizers
```

---

## Recent Cycles

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
| PairingNondegenerate.lean | **BOSS BATTLE** | 2 axioms to prove |
| PairingDescent.lean | Pairing infrastructure | ✅ Complete (13 axioms) |
| LocalResidue.lean | Residue map | ✅ Axiomatized (2 axioms) |

---

*Updated Cycle 368. BOSS BATTLE ENGAGED: Proving non-degeneracy axioms. Victory conditions: eliminate serreDualityPairing_injective and serreDualityPairing_right_nondegen. Reward: serre_duality and h1_finite_all axioms become theorems.*
