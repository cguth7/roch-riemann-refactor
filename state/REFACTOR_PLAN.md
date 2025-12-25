# Refactor Plan: P¹ → Arbitrary Curves

**Status**: P¹ Frozen. Phase 7 (General Curves via Weil Differentials) Active. Updated Cycle 311.
**Goal**: Riemann-Roch for curves of any genus g ≥ 0 using Weil Differentials.

---

## Quick Reference

| Phase | Status | Key Achievement |
|-------|--------|-----------------|
| 0-4 | ✅ Complete | P¹ infrastructure, Serre duality |
| 4.5 | ✅ Complete | Valuation-degree, IsLinearPlaceSupport fix |
| 5 | ⏸️ Archived | P¹ edge cases (PID-specific, not generalizable) |
| 6 | ✅ Complete | Elliptic curves (genus 1) - RR proved with axioms |
| 7 | ⏳ **Active** | Weil Differentials for general curves |

---

## Phase 7: General Curves via Weil Differentials (Active)

### Motivation

The P¹ proof uses `RatFunc Fq` directly for the Serre duality pairing because:
- The canonical bundle is trivializable (dt is a global differential)
- Functions can substitute for differentials

For g ≥ 2, this fails:
- No global differential exists
- Must use **Weil Differentials** (functional-analytic approach)

### Key References

- [Rosen "Number Theory in Function Fields" Ch. 6](https://link.springer.com/chapter/10.1007/978-1-4757-6046-0_6) - "Weil Differentials and the Canonical Class"
- [Stichtenoth "Algebraic Function Fields and Codes" §1.7](https://link.springer.com/book/10.1007/978-3-540-76878-4) - "Local Components of Weil Differentials"
- [Charles University Thesis on Weil Differentials](https://dspace.cuni.cz/bitstream/handle/20.500.11956/62611/DPTX_2012_2_11320_0_392289_0_137152.pdf) - Computational algorithms

### Mathematical Framework

**Definition (Weil Differential)**:
A Weil differential of F/K is a K-linear mapping ω : A_F → K that vanishes on A_F(A) + F for some divisor A.

```lean
/-- A Weil differential is a linear functional on full adeles vanishing on K -/
def WeilDifferential (K : Type*) [Field K] :=
  { ω : FullAdeleRing R K K_infty →ₗ[k] k //
    ∀ x : K, ω (fullDiagonalEmbedding R K K_infty x) = 0 }
```

**Definition (Local Component)**:
For a Weil differential ω and place P, the local component ω_P is extracted via the adele product structure. The relationship: residue algorithms can compute local components.

**Definition (Valuation of Differential)**:
v_P(ω) = max { n : ω vanishes on A_F(nP) at place P }

**Definition (Canonical Divisor)**:
(ω) = Σ_P v_P(ω) · P for any nonzero Weil differential ω

**Key Property**: dim_K(WeilDifferential) = 1, so the canonical class is well-defined.

### Implementation Plan

#### Cycle 312: Define WeilDifferential
**File**: `RrLean/RiemannRochV2/General/WeilDifferential.lean`

```lean
/-- Weil differential: linear functional on adeles vanishing on K -/
structure WeilDifferential (k R K K_infty : Type*)
    [Field k] [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field K_infty] [Algebra K K_infty] where
  toLinearMap : FullAdeleRing R K K_infty →ₗ[k] k
  vanishes_on_K : ∀ x : K, toLinearMap (fullDiagonalEmbedding R K K_infty x) = 0

instance : Module K (WeilDifferential k R K K_infty) := ...
```

**Deliverables**:
- [ ] Define `WeilDifferential` structure
- [ ] Prove it forms a K-vector space
- [ ] Prove K-linear maps compose correctly

#### Cycle 313: Local Components (THE HARD PART)
**File**: `RrLean/RiemannRochV2/General/LocalComponent.lean`

The challenge: extract ω_P from global ω using adele product structure.

**Strategy**:
1. Use that A_K = ∏'_v K_v (restricted product)
2. For each place v, project adele to v-component
3. Define localComponent_v(ω) : K_v → k

```lean
/-- Extract local component at place v -/
def localComponent (ω : WeilDifferential k R K K_infty)
    (v : HeightOneSpectrum R) : v.adicCompletion K →ₗ[k] k := ...

/-- Local components determine the global differential -/
theorem ext_localComponent :
    (∀ v, localComponent ω₁ v = localComponent ω₂ v) → ω₁ = ω₂ := ...
```

**Deliverables**:
- [ ] Define `localComponent` extraction
- [ ] Prove extensionality (local components determine global)
- [ ] Connect to existing residue infrastructure

#### Cycle 314: Divisor of a Differential
**File**: `RrLean/RiemannRochV2/General/DifferentialDivisor.lean`

```lean
/-- Valuation of differential at a place -/
def valuation_differential (ω : WeilDifferential k R K K_infty)
    (v : HeightOneSpectrum R) : ℤ :=
  -- Largest n such that ω vanishes on A_K(n·v)
  ...

/-- Divisor of a differential -/
def div (ω : WeilDifferential k R K K_infty) : DivisorV2 R :=
  Finsupp.ofSupportFinite (fun v => valuation_differential ω v) (by ...)
```

**Deliverables**:
- [ ] Define `valuation_differential`
- [ ] Define `div ω`
- [ ] Prove div is finite (uses compactness)

#### Cycle 315: The Serre Duality Pairing
**File**: `RrLean/RiemannRochV2/General/SerrePairingGeneral.lean`

The beautiful simplification: ⟨f, ω⟩ = ω(f) is just evaluation!

```lean
/-- Serre duality pairing via evaluation -/
def serrePairing_general (D : DivisorV2 R) :
    RRSpace_proj k R K D →ₗ[k] WeilDifferential k R K K_infty →ₗ[k] k :=
  fun f => fun ω => ω.toLinearMap (embed_function_to_adele f)
```

**Deliverables**:
- [ ] Define the pairing
- [ ] Prove bilinearity
- [ ] Axiomatize non-degeneracy (or derive from RR)

#### Cycle 316: Canonical Divisor Properties
**File**: `RrLean/RiemannRochV2/General/Canonical.lean`

```lean
/-- The canonical divisor class is well-defined -/
theorem canonical_class_unique :
    ∀ ω₁ ω₂ : WeilDifferential k R K K_infty,
    ω₁ ≠ 0 → ω₂ ≠ 0 → div ω₁ ≈ div ω₂ := ...

/-- Degree of canonical divisor -/
theorem deg_canonical : (div ω).deg = 2 * genus - 2 := ...
```

**Deliverables**:
- [ ] Prove canonical class well-defined
- [ ] Prove deg(K) = 2g - 2
- [ ] Connect to existing elliptic canonical (g=1 case)

#### Cycle 317+: Complete RR
- Fill axioms or derive from general theory
- Prove h¹(D) = ℓ(K-D) using the new pairing
- Unify with existing P¹ and elliptic proofs

---

## Archived: Phase 5 (P¹ Edge Cases)

**Decision**: SKIPPED. Cycle 311 archives these.

The remaining sorries in AdelicH1Full.lean (lines 757, 1458) are:
- `globalPlusBoundedSubmodule_full_eq_top_deep_neg_infty`
- `globalPlusBoundedSubmodule_full_eq_top_not_effective`

These are **PID-specific artifacts**:
- Rely on Euclidean division for strong approximation bounds
- Not generalizable to non-PID coordinate rings
- Not needed for the Weil differential approach

**Legacy Status**: P¹ proof is "complete enough" to validate architecture.

---

## Completed Phases (Summary)

### Phase 0-4: P¹ Infrastructure ✅
- Full adele ring with infinity
- Serre duality for effective divisors
- Riemann-Roch formula: ℓ(D) = deg(D) + 1

### Phase 6: Elliptic Curves ✅
- RR proved with axioms (genus = 1)
- 5 axioms: IsDedekindDomain, StrongApprox, h1_zero_eq_one, h1_vanishing, serre_duality

---

## Architecture for General Curves

### File Structure (Proposed)

```
RrLean/RiemannRochV2/General/
├── WeilDifferential.lean      # Definition, K-module structure
├── LocalComponent.lean        # Extract ω_P from global ω
├── DifferentialDivisor.lean   # div(ω), valuation
├── SerrePairingGeneral.lean   # ⟨f, ω⟩ = ω(f)
├── Canonical.lean             # Canonical class, deg(K) = 2g-2
└── GeneralRRData.lean         # ProjectiveAdelicRRData instance
```

### Key Insight: Pairing Simplification

**P¹ approach** (current):
```lean
⟨f, g⟩ = Σ_v res_v(f · g)  -- Sum of residues
```
Requires: residue infrastructure, residue theorem, pole cancellation.

**Weil approach** (new):
```lean
⟨f, ω⟩ = ω(f)  -- Just evaluation!
```
The residue theorem is *built into* the definition of WeilDifferential (vanishes on K).

### What We Keep vs Replace

| Component | P¹ Version | General Version |
|-----------|------------|-----------------|
| Adele ring | FullAdeleRing ✅ | Same (reuse) |
| H¹(D) definition | FullAdeleRing / (K + A_K(D)) ✅ | Same (reuse) |
| Serre pairing | residueSumTotal | ω(f) evaluation |
| Canonical divisor | -2[∞] (hardcoded) | div(ω) (intrinsic) |
| Residue infrastructure | Heavy (2000 LOC) | Implicit in WeilDiff |

---

## Remaining Sorries After Phase 7

### To Be Axiomatized (Acceptable)
- `dim_K(WeilDifferential) = 1` - standard, orthogonal to RR
- `serrePairing_nondegenerate` - follows from RR or axiomatize
- `StrongApprox K` for general K - standard, avoids circularity

### To Be Proved (Core RR Content)
- `h¹(D) = ℓ(K-D)` - the Serre duality statement
- `deg(K) = 2g-2` - follows from Weil differential theory

---

*Updated Cycle 311. Phase 7 active. See ledger.md for current state.*
