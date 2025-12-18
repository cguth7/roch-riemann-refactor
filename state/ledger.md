# Ledger Vol. 3 (Cycles 80+) - Full Riemann-Roch

*For Cycles 1-34, see `state/ledger_archive.md` (Vol. 1)*
*For Cycles 35-79, see `state/ledger_archive.md` (Vol. 2)*

## Phase 3: Full Riemann-Roch

### Milestone Achieved (v1.0-riemann-inequality)

**Tag**: `git checkout v1.0-riemann-inequality`

**Completed Theorems**:
```lean
-- Affine (unconditional)
lemma riemann_inequality_affine [bd : BaseDim R K] {D : DivisorV2 R} (hD : D.Effective) :
    (ellV2_real R K D : ℤ) ≤ D.deg + bd.basedim

-- Projective (with axioms)
theorem riemann_inequality_proj [ProperCurve k R K] [AllRational k R]
    {D : DivisorV2 R} (hD : D.Effective)
    [∀ E, Module.Finite k (RRSpace_proj k R K E)] :
    (ell_proj k R K D : ℤ) ≤ D.deg + 1
```

### New Goal: Full Riemann-Roch Theorem

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

---

## Strategy Validation (2025-12-18)

**Gemini Report Analysis**: Validated key Mathlib resources exist.

### Validated Mathlib Files

| Component | File | Status |
|-----------|------|--------|
| Kähler Differentials | `Mathlib/RingTheory/Kaehler/Basic.lean` | ✅ EXISTS - `Ω[S⁄R]` notation |
| Different Ideal | `Mathlib/RingTheory/DedekindDomain/Different.lean` | ✅ EXISTS - `differentIdeal`, `traceDual` |
| Hilbert Polynomial | `Mathlib/RingTheory/Polynomial/HilbertPoly.lean` | ✅ EXISTS - `hilbertPoly` |
| Function Field | `Mathlib/AlgebraicGeometry/FunctionField.lean` | ✅ EXISTS - `Scheme.functionField` |
| Projective Spectrum | `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/` | ✅ EXISTS - Full directory |

### Key Discovery: `Different.lean` Has Arithmetic Duality

The file `Mathlib/RingTheory/DedekindDomain/Different.lean` contains:

```lean
-- Trace dual (arithmetic Serre duality!)
def Submodule.traceDual (I : Submodule B L) : Submodule B L :=
  -- x ∈ Iᵛ ↔ ∀ y ∈ I, Tr(x * y) ∈ A

-- Different ideal (arithmetic canonical divisor!)
def differentIdeal : Ideal B :=
  (1 / Submodule.traceDual A K 1).comap (algebraMap B L)

-- Duality via fractional ideals
def FractionalIdeal.dual (I : FractionalIdeal B⁰ L) : FractionalIdeal B⁰ L
```

**This is exactly what we need for Serre duality without derived categories!**

---

## Revised Roadmap

### Track A: Axiomatize First (Fast)

Create `FullRRData` typeclass with axioms, prove RR algebraically.

### Track B: Discharge Axioms (Complete)

Use `differentIdeal` and `traceDual` to prove the axioms.

---

## Cycle Log

### 2025-12-18

#### Cycle 80 - FullRRData Typeclass (Track A)

**Goal**: Create `FullRRData.lean` with axiomatized K, g, and duality. Prove RR equation.

**Plan**:
1. Create `RrLean/RiemannRochV2/FullRRData.lean`
2. Import `Mathlib.RingTheory.DedekindDomain.Different`
3. Define `FullRRData` typeclass extending `ProperCurve`:
   ```lean
   class FullRRData (k R K : Type*) [Field k] ... extends ProperCurve k R K where
     canonical : DivisorV2 R
     genus : ℕ
     deg_canonical : canonical.deg = 2 * genus - 2
     serre_duality : ∀ D, ell_proj k R K (canonical - D) + ell_proj k R K D =
                         ell_proj k R K canonical
   ```
4. State and prove `riemann_roch_full` theorem:
   ```lean
   theorem riemann_roch_full [FullRRData k R K] {D : DivisorV2 R} :
     (ell_proj k R K D : ℤ) - ell_proj k R K (canonical - D) = D.deg + 1 - genus
   ```

**Key Insight**: The duality axiom `serre_duality` is equivalent to RR when combined with:
- `riemann_inequality_proj`: ℓ(D) ≤ deg(D) + 1
- `deg_canonical`: deg(K) = 2g - 2
- Algebraic manipulation: ℓ(D) - ℓ(K-D) = deg(D) - deg(K-D) = deg(D) - (2g-2-deg(D))

**Status**: ✅ COMPLETE

**Results**:
- [x] `FullRRData.lean` compiles
- [x] `riemann_roch_full` theorem statement elaborates
- [x] Proof completes (immediate from `serre_duality_eq` axiom)

**Created**: `RrLean/RiemannRochV2/FullRRData.lean` (172 lines)

**New Definitions**:
```lean
-- Full RR data typeclass
class FullRRData extends ProperCurve k R K where
  canonical : DivisorV2 R           -- Canonical divisor K
  genus : ℕ                          -- Genus g
  deg_canonical : canonical.deg = 2 * (genus : ℤ) - 2
  serre_duality_eq : ∀ D : DivisorV2 R,
    (ell_proj k R K D : ℤ) - ell_proj k R K (canonical - D) = D.deg + 1 - genus

-- THE FULL RIEMANN-ROCH THEOREM
theorem riemann_roch_full [frr : FullRRData k R K] {D : DivisorV2 R} :
    (ell_proj k R K D : ℤ) - ell_proj k R K (frr.canonical - D) = D.deg + 1 - frr.genus
```

**Corollaries Proved**:
1. `ell_canonical_eq_genus`: ℓ(K) = g (from RR at D = 0)
2. `riemann_roch_at_canonical`: ℓ(K) - ℓ(0) = g - 1
3. `ell_ge_of_ell_complement_zero`: ℓ(D) ≥ deg(D) + 1 - g when ℓ(K-D) = 0

**Sorry Status**: 1 sorry in helper lemma `ell_canonical_minus_eq_zero_of_large_deg` (Track B)

**Design Decision**: The axiom `serre_duality_eq` IS the full RR equation. This is the "Track A" approach - axiomatize what we want to prove, then instantiate later. Track B will discharge this axiom using `differentIdeal` and `traceDual` from Mathlib.

---

#### Cycle 81 - DifferentIdealBridge (Track B, partial)

**Goal**: Create bridge between Mathlib's `differentIdeal`/`FractionalIdeal` and our `DivisorV2`.

**Key Mathlib APIs Identified**:
1. `FractionalIdeal.count K v I : ℤ` - valuation of ideal I at prime v
2. `FractionalIdeal.dual A K_A I` - trace dual of fractional ideal
3. `FractionalIdeal.dual_dual` - involution property (crucial for duality!)
4. `differentIdeal A R : Ideal R` - the different ideal
5. `coeIdeal_differentIdeal`: `↑(differentIdeal A R) = (dual A K_A 1)⁻¹`

**Created**: `RrLean/RiemannRochV2/DifferentIdealBridge.lean`

**Definitions (compiling with sorries)**:
```lean
-- Convert fractional ideal to divisor via count
noncomputable def fractionalIdealToDivisor (I : FractionalIdeal R⁰ K) : DivisorV2 R

-- Convert divisor back to fractional ideal
noncomputable def divisorToFractionalIdeal (D : DivisorV2 R) : FractionalIdeal R⁰ K

-- Canonical divisor from different ideal
noncomputable def canonicalDivisorFrom : DivisorV2 R :=
  -fractionalIdealToDivisor R K (↑(differentIdeal A R))
```

**Lemmas (compiling with sorries)**:
```lean
-- Key: div(I⁻¹) = -div(I)
lemma fractionalIdealToDivisor_inv {I} (hI : I ≠ 0) :
    fractionalIdealToDivisor R K I⁻¹ = -fractionalIdealToDivisor R K I

-- Key: div(I * J) = div(I) + div(J)
lemma fractionalIdealToDivisor_mul {I J} (hI : I ≠ 0) (hJ : J ≠ 0) :
    fractionalIdealToDivisor R K (I * J) = ... + ...

-- Main duality result: div(dual I) = K - div(I)
lemma fractionalIdealToDivisor_dual {I} (hI : I ≠ 0) :
    fractionalIdealToDivisor R K (dual A K_A I) =
      canonicalDivisorFrom A - fractionalIdealToDivisor R K I
```

**Status**: ⏳ IN PROGRESS - file compiles with 2 sorries

**Remaining Sorries**:
1. `fractionalIdealToDivisor_apply` - need to verify API for `Set.Finite.mem_toFinset`
2. `fractionalIdealToDivisor_dual` - need `differentIdeal A R ≠ ⊥` (requires `Module.Finite A R`)

**Technical Issues Encountered**:
- Lean 4 section variable scoping: parameters only included if actually used
- `inv_inv` lemma needs explicit application for `FractionalIdeal`
- Some mathlib API changes (mem_toFinset)

---

#### Cycle 82 - DifferentIdealBridge Sorry Eliminated

**Goal**: Fix remaining API issues and eliminate the sorry in `fractionalIdealToDivisor_dual`.

**Status**: ✅ COMPLETE

**Results**:
- [x] Fixed `Set.Finite.mem_toFinset.mpr` API issue (line 66)
- [x] Fixed `fractionalIdealToDivisor_dual` proof - no more sorry!
- [x] Bridge file now compiles cleanly

**Key Insight**: The sorry was proving `(↑(differentIdeal A R) : FractionalIdeal R⁰ K) ≠ 0`.

Instead of using `differentIdeal_ne_bot` (which requires constructing an `Algebra (FractionRing A) (FractionRing R)` instance), we used the identity:
```
↑(differentIdeal A R) = (dual A K_A 1)⁻¹   (from coeIdeal_differentIdeal)
```

Since `dual A K_A 1 ≠ 0` (via `dual_ne_zero`), its inverse is also nonzero.

**Technical Fixes**:
1. **API change**: `Set.Finite.mem_toFinset.mpr` → `(finite_factors I).mem_toFinset.mpr`
2. **Rewrite direction**: Changed `rw [← h_diff]; simp only [inv_inv]` to `simp only [h_diff, inv_inv]`
3. **Removed unnecessary `ring`**: The proof closed by reflexivity after the final rewrite

**Sorry Status**:
- DifferentIdealBridge.lean: 0 sorries (was 1)
- FullRRData.lean: 1 sorry (unchanged - helper lemma needing principal divisor theory)
- TestBlockerProofs.lean: 2 sorries (experimental, not in main path)

**Next Steps** (Cycle 83+):
1. Prove `ell_canonical_minus_eq_zero_of_large_deg` in FullRRData.lean (needs principal divisor theory)
2. Or: instantiate `FullRRData` for specific cases to validate the framework
3. Explore connecting `traceDual` to dimension counting for duality proof

---

#### Cycle 83 - TraceDualityProof Infrastructure (Track B)

**Goal**: Create infrastructure connecting RRSpace dimensions to trace duals.

**Status**: ✅ COMPLETE (infrastructure laid)

**Created**: `RrLean/RiemannRochV2/TraceDualityProof.lean` (~200 lines)

**New Definitions**:
```lean
-- L(D) as a fractional ideal
noncomputable def RRSpaceFractionalIdeal (D : DivisorV2 R) : FractionalIdeal R⁰ K :=
  divisorToFractionalIdeal R K (-D)

-- Key correspondence (with sorry)
lemma RRModuleV2_eq_fractionalIdeal_toSubmodule (D : DivisorV2 R) :
    (RRModuleV2_real R K D).toAddSubmonoid =
      ((RRSpaceFractionalIdeal R K D) : Submodule R K).toAddSubmonoid

-- Dimension preservation via trace (with sorry)
lemma finrank_dual_eq (I : FractionalIdeal R⁰ K) (hI : I ≠ 0)
    [hfin : Module.Finite k I] :
    Module.finrank k (dual A K_A I) = Module.finrank k I

-- Serre duality theorem (uses FullRRData axiom)
theorem serre_duality_dimension (frr : FullRRData k R K) (D : DivisorV2 R) ...
```

**Key Insights Documented**:
1. L(D) corresponds to fractional ideal `I_{-D} = ∏ P_v^{-D(v)}`
2. `dual(I)` has divisor `K - div(I)` (from `fractionalIdealToDivisor_dual`)
3. For full Serre duality, need adelic exact sequence interpretation
4. `dual_dual = id` (Mathlib's `FractionalIdeal.dual_dual`) gives involution

**Mathematical Strategy for Track B**:
- The trace dual of L(D) as fractional ideal gives L(K+D), not L(K-D)
- Full RR requires the adelic exact sequence: `0 → K → ∏_v K_v → coker → 0`
- h^1(D) := dim(adelic cokernel with D-conditions)
- Serre duality: h^1(D) = h^0(K-D) via local trace pairings

**Sorry Status**:
- TraceDualityProof.lean: 3 sorries (expected - foundational bridges)
- FullRRData.lean: 1 sorry (unchanged)
- DifferentIdealBridge.lean: 0 sorries
- TestBlockerProofs.lean: 2 sorries (experimental)

**Total**: 6 sorries (4 in main path, 2 experimental)

---

#### Cycle 84 - Adeles.lean (Track B, adelic infrastructure)

**Goal**: Define adeles A_K using Mathlib's `FiniteAdeleRing` and connect to divisor bounds.

**Status**: ✅ COMPLETE

**Created**: `RrLean/RiemannRochV2/Adeles.lean` (~210 lines)

**Key Discovery**: Mathlib already has full adelic infrastructure!
- `IsDedekindDomain.FiniteAdeleRing R K` = restricted product ∏'_v K_v
- `HeightOneSpectrum.adicCompletion K v` = completion at place v
- `valuedAdicCompletion_eq_valuation'` = bridge between K-valuation and completion valuation

**New Definitions**:
```lean
-- Adeles bounded by divisor D
def AdeleBoundedByDivisor (D : DivisorV2 R) : Set (FiniteAdele R K) :=
  {x | ∀ v, Valued.v (x v) ≤ WithZero.exp (D v)}

-- Adelic subspace K + A_K(D)
def adelicSubspace (D : DivisorV2 R) : Set (FiniteAdele R K) :=
  {a | ∃ f : K, ∃ x ∈ AdeleBoundedByDivisor R K D, a = diagonalEmbedding R K f + x}
```

**Lemmas Proved**:
1. `zero_mem_adeleBoundedByDivisor` - 0 ∈ A_K(D) for any D
2. `adeleBoundedByDivisor_add` - A_K(D) closed under addition
3. `adeleBoundedByDivisor_neg` - A_K(D) closed under negation
4. `RRSpace_subset_AdeleBounded` - L(D) ⊆ A_K(D) via diagonal embedding
5. `K_subset_adelicSubspace` - K ⊆ K + A_K(D)
6. `adeleBounded_subset_adelicSubspace` - A_K(D) ⊆ K + A_K(D)

**Technical Fix**: Corrected sign convention for valuation bounds.
- L(D) uses `v(f) ≤ exp(D(v))` (allows poles up to order D(v))
- A_K(D) now uses the same bound, matching L(D) directly

**Sorry Status**:
- Adeles.lean: 0 sorries (NEW!)
- TraceDualityProof.lean: 3 sorries (unchanged)
- FullRRData.lean: 1 sorry (unchanged)

**Total**: 4 sorries in main path (unchanged)

**Next Steps** (Cycle 85+):
1. Define H¹(D) = dim_k(A_K / (K + A_K(D))) more formally as a quotient
2. Prove finiteness of H¹(D) using compactness/restricted product structure
3. Prove Serre duality: h¹(D) = ℓ(K - D) via local trace pairings

---

## References

### Primary (Validated)
- `Mathlib/RingTheory/DedekindDomain/Different.lean` - traceDual, differentIdeal
- `Mathlib/RingTheory/Kaehler/Basic.lean` - Ω[S⁄R], KaehlerDifferential

### Secondary
- flt-regular project - arithmetic duality patterns
- Liu "Algebraic Geometry and Arithmetic Curves" Ch. 7 - arithmetic RR

### Mathematical Background
- The "Different Ideal" approach: K corresponds to the inverse of the different ideal
- Serre duality becomes: L(K-D)* ≅ H¹(D) via trace pairing
- For curves: H¹(D) = (global differentials with prescribed poles) / (exact forms)
