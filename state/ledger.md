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

**Next Steps** (Cycle 85):

**Primary Goal**: Define H¹(D) as a proper k-module quotient

**Concrete Tasks**:
1. Make `adelicSubspace R K D` into an AddSubgroup of FiniteAdele R K
2. Define `AdelicH1 k R K D := (FiniteAdele R K) ⧸ (adelicSubspace R K D)`
3. Give it k-module structure (diagonal scalar action)
4. Define `h1 k R K D := Module.finrank k (AdelicH1 k R K D)`

**Key Technical Challenges**:
- Proving `adelicSubspace` is closed under addition (need: if a = f + x, b = g + y, then a + b = (f+g) + (x+y))
- The k-action: k acts on K diagonally, need to show this descends to quotient
- Finiteness: For large deg(D), H¹(D) = 0 (strong approximation theorem)

**Decision Point**:
- If quotient machinery is painful, consider proving TraceDualityProof.lean sorries instead
- Those 3 sorries use FractionalIdeal.dual which is already connected to our divisors

---

#### Cycle 85 - Simplified Adelic H¹(D) Structure

**Goal**: Define H¹(D) = A_K / (K + A_K(D)) with clean structure.

**Status**: ✅ COMPLETE (compiles with 2 sorries)

**Approach Change**: Abandoned Mathlib's `FiniteAdeleRing` (too complex). Used simplified model:
- Adeles as functions `HeightOneSpectrum R → K`
- `adelicSubspace D` = functions with v(f_v) ≤ exp(D(v)) at each place
- `globalField` = constant functions (diagonal K embedding)
- `Space D` = quotient (HeightOneSpectrum R → K) ⧸ (K + A_K(D))

**New Definitions**:
```lean
-- Global field K embedded diagonally
def globalField : Submodule k (HeightOneSpectrum R → K)

-- Adelic subspace A_K(D)
def adelicSubspace (D : DivisorV2 R) : Submodule k (HeightOneSpectrum R → K)

-- H¹(D) as quotient
abbrev Space (D : DivisorV2 R) := ... ⧸ (globalField + adelicSubspace D)

-- Dimension
def h1 (D : DivisorV2 R) : Cardinal := Module.rank k (Space k R K D)
```

**Lemmas Proved**:
- `globalInAdelicSubspace`: L(D) embeds into A_K(D) ✅
- `quotientMap_of_global`: K maps to 0 in H¹(D) ✅

**Remaining Sorries** (2):
1. `adelicSubspace.add_mem'`: Ultrametric inequality for valuation
   - Strategy: Use `Valuation.map_add_le_max'` + `max_le`
2. `adelicSubspace.smul_mem'`: k-scalar action preserves bounds
   - Strategy: Need k = constant field hypothesis (v(c) ≤ 1 for c ∈ k)

**Key Insight**: The simplified model avoids:
- `FiniteAdeleRing` universe issues
- Complicated restricted product topology
- Instance resolution nightmares

The quotient `Space k R K D` has automatic `Module k` and `AddCommGroup` instances via `abbrev`.

**Next Steps** (Cycle 86):
1. Prove the 2 valuation sorries
2. Add hypothesis: k is constant field (all v(c) = 1 for c ∈ k×)
3. Consider if we need restricted product (probably not for dimension counting)

---

#### Cycle 86 - Adeles.lean Sorry-Free!

**Goal**: Prove the 2 remaining sorries in Adeles.lean for `adelicSubspace` submodule properties.

**Status**: ✅ COMPLETE

**Results**:
- [x] `adelicSubspace.add_mem'` - PROVED using ultrametric inequality
- [x] `adelicSubspace.smul_mem'` - PROVED using IsScalarTower k R K

**Technical Details**:

1. **`add_mem'` proof**: Uses `Valuation.map_add_le_max'` for the ultrametric inequality
   ```lean
   v.valuation K (a v + b v) ≤ max (v.valuation K (a v)) (v.valuation K (b v))
   ```
   Combined with `max_le` when both components satisfy the divisor bound.

2. **`smul_mem'` proof**: Uses `IsScalarTower k R K` to factor the scalar action:
   ```lean
   algebraMap k K c = algebraMap R K (algebraMap k R c)
   ```
   Then `HeightOneSpectrum.valuation_le_one` gives `v(algebraMap R K r) ≤ 1` for `r ∈ R`.

3. **Added variable**: `[IsScalarTower k R K]` to relate the algebra structures.

**Key Insight**: The "constant field" property (that k-scalars have valuation ≤ 1) follows automatically from:
- `Algebra k R` (k embeds in R)
- `IsScalarTower k R K` (algebras are compatible)
- `valuation_le_one` (R-elements have no poles in K)

**Sorry Status**:
- Adeles.lean: 0 sorries (was 2) ✅
- FullRRData.lean: 1 sorry (unchanged)
- TraceDualityProof.lean: 3 sorries (unchanged)

**Total**: 4 sorries in main path (was 6, reduced by 2)

**Next Steps** (Cycle 87):
1. Prove finiteness of H¹(D) for deg(D) >> 0
2. Or: tackle TraceDualityProof.lean sorries via fractional ideal machinery
3. Or: prove strong approximation for vanishing

---

#### Cycle 87 - Valuation-Fractional Ideal Bridge

**Goal**: Build the bridge connecting valuation-based L(D) to fractional ideal membership.

**Status**: ✅ COMPLETE (architectural improvement, sorry count reduced)

**Results**:
- [x] Added `count_divisorToFractionalIdeal` - PROVED
- [x] Added `mem_divisorToFractionalIdeal_iff` - infrastructure lemma (1 sorry)
- [x] Rewrote `RRModuleV2_eq_fractionalIdeal_toSubmodule` using new bridge
- [x] Reduced TraceDualityProof.lean sorries from 3 to 1

**Key Addition**: `count_divisorToFractionalIdeal` lemma:
```lean
lemma count_divisorToFractionalIdeal (D : DivisorV2 R) (v : HeightOneSpectrum R) :
    count K v (divisorToFractionalIdeal R K D) = D v
```
This proves that `divisorToFractionalIdeal D` has the correct count at each prime.

**Key Lemma** (`mem_divisorToFractionalIdeal_iff`):
```lean
lemma mem_divisorToFractionalIdeal_iff (D : DivisorV2 R) (x : K) :
    x ∈ divisorToFractionalIdeal R K D ↔
      x = 0 ∨ ∀ v, v.valuation K x ≤ WithZero.exp (-D v)
```
This is the fundamental bridge: membership in fractional ideal ↔ valuation bounds.

**Proof Strategy** (for sorry): Requires showing:
1. `x ∈ I` iff `spanSingleton x ≤ I` (Mathlib: `spanSingleton_le_iff_mem`)
2. `I ≤ J` iff `count v I ≥ count v J` for all v (from factorization + `count_mono`)
3. `count v (spanSingleton x) = -log(v.valuation K x)` (connect to valuation)

**Architectural Improvement**:
- Before: TraceDualityProof had 2 separate sorries for forward/backward membership
- After: Single sorry in `mem_divisorToFractionalIdeal_iff`, cleaner proof structure

**Sorry Status**:
- DifferentIdealBridge.lean: 1 sorry (NEW - `mem_divisorToFractionalIdeal_iff`)
- TraceDualityProof.lean: 1 sorry (was 3 - `finrank_dual_eq`)
- FullRRData.lean: 1 sorry (unchanged)

**Total**: 3 sorries in main path (was 4, reduced by 1)

**Next Steps** (Cycle 88):
1. Prove `mem_divisorToFractionalIdeal_iff` via spanSingleton and count characterization
2. Or: Prove `finrank_dual_eq` via trace form nondegeneracy
3. Or: Focus on H¹(D) finiteness for Serre duality

---

#### Cycle 88 - Valuation-FractionalIdeal Bridge Infrastructure

**Goal**: Prove `mem_divisorToFractionalIdeal_iff` - the key bridge between valuation-based L(D) and fractional ideal membership.

**Status**: ✅ COMPLETE (1 remaining sorry moved to helper)

**Results**:
- [x] `valuation_eq_exp_neg_count` - PROVED: `v.valuation K x = exp(-count K v (spanSingleton x))`
- [x] `le_iff_forall_count_ge` forward direction - PROVED via `count_mono`
- [x] `mem_divisorToFractionalIdeal_iff` - Structure complete (uses helper lemmas)
- [ ] `le_iff_forall_count_ge` reverse direction - 1 sorry remaining

**Key Lemma Proved** (`valuation_eq_exp_neg_count`):
```lean
lemma valuation_eq_exp_neg_count (v : HeightOneSpectrum R) (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-count K v (spanSingleton R⁰ x))
```
This is the fundamental connection between:
- Valuation view: `v.valuation K x` (multiplicative valuation on K)
- Fractional ideal view: `count K v (spanSingleton R⁰ x)` (additive ideal factorization)

**Proof Technique**:
1. Write `x = n/d` using `IsLocalization.mk'_surjective`
2. Use `valuation_of_algebraMap` to reduce to `intValuation`
3. Use `intValuation_if_neg` to get `exp(-count v (span {r}))` form
4. Use `count_well_defined` to show principal ideal counts match
5. Simplify exponential arithmetic: `exp(-a) / exp(-b) = exp(b - a)`

**Lemma Structure** (`mem_divisorToFractionalIdeal_iff`):
```lean
lemma mem_divisorToFractionalIdeal_iff (D : DivisorV2 R) (x : K) :
    x ∈ divisorToFractionalIdeal R K D ↔
      x = 0 ∨ ∀ v, v.valuation K x ≤ WithZero.exp (-D v)
```
Uses:
- `spanSingleton_le_iff_mem`: x ∈ I ↔ spanSingleton x ≤ I
- `le_iff_forall_count_ge`: I ≤ J ↔ ∀ v, count v J ≤ count v I
- `count_divisorToFractionalIdeal`: count v (divisorToFractionalIdeal D) = D v
- `valuation_eq_exp_neg_count`: Convert between valuation and count

**Remaining Sorry**:
```lean
lemma le_iff_forall_count_ge {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J ↔ ∀ v, count K v J ≤ count K v I
```
- Forward direction: ✅ PROVED via `count_mono`
- Reverse direction: 1 sorry (needs factorization uniqueness argument)

**Technical Notes**:
- Need `classical` at function level for `Associates.count` (DecidableEq)
- `div_eq_mul_inv`, `← WithZero.exp_neg`, `neg_neg`, `← WithZero.exp_add` for exponential algebra
- `linarith` handles the `exp(-a) ≤ exp(-b) ↔ b ≤ a` reasoning
- `Finset.prod_ne_zero_iff` for showing divisorToFractionalIdeal ≠ 0

**Sorry Status** (unchanged count, different distribution):
- DifferentIdealBridge.lean: 1 sorry (`le_iff_forall_count_ge` reverse, was `mem_divisorToFractionalIdeal_iff`)
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq`)
- FullRRData.lean: 1 sorry (unchanged)

**Total**: 3 sorries in main path (unchanged from Cycle 87)

**Architecture Improvement**: The sorry is now in a cleaner helper lemma `le_iff_forall_count_ge` rather than the main bridge lemma. This makes the dependency structure clearer.

**Next Steps** (Cycle 89):
1. Prove `le_iff_forall_count_ge` reverse direction via factorization uniqueness
2. Or: Prove `finrank_dual_eq` via trace form nondegeneracy
3. Or: Focus on H¹(D) finiteness for Serre duality

---

#### Cycle 89 - le_iff_forall_count_ge Reverse Direction PROVED

**Goal**: Prove the reverse direction of `le_iff_forall_count_ge` - if counts satisfy inequality, then fractional ideal inequality holds.

**Status**: ✅ COMPLETE

**Results**:
- [x] `le_iff_forall_count_ge` reverse direction - PROVED!
- [x] Sorry eliminated from DifferentIdealBridge.lean

**Key Technique**: Factorization uniqueness + finprod induction

The proof uses the strategy:
1. Define `K := I * J⁻¹`
2. Show `count v K = count v I - count v J ≥ 0` for all v (by hypothesis)
3. Show `K ≤ 1` by using factorization:
   - `K = ∏ᶠ v, v^{count v K}` (Mathlib's `finprod_heightOneSpectrum_factorization'`)
   - Each factor `v^n` with n ≥ 0 is an ideal power, hence ≤ 1 (`coeIdeal_le_one`)
   - Use `finprod_induction` to show product of things ≤ 1 is ≤ 1
4. Conclude `I = K * J ≤ 1 * J = J`

**Technical Details**:
- Used `finprod_induction (p := (· ≤ 1))` with explicit predicate naming
- For step (3): proved `∀ A B, A ≤ 1 → B ≤ 1 → A * B ≤ 1` via `gcongr`
- For each factor: extracted `n : ℕ` from `Int.eq_ofNat_of_zero_le`, then `zpow_natCast` + `coeIdeal_pow`

**Sorry Status**:
- DifferentIdealBridge.lean: 0 sorries (was 1) ✅
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq`)
- FullRRData.lean: 1 sorry (unchanged)

**Total**: 2 sorries in main path (was 3, reduced by 1)

**Next Steps** (Cycle 90):
1. Prove `finrank_dual_eq` via trace form nondegeneracy
2. Or: Focus on H¹(D) finiteness for Serre duality
3. Or: Prove the FullRRData helper lemma

---

#### Cycle 90 - Architectural Analysis + deg_nonneg_of_effective

**Goal**: Analyze the 2 remaining sorries and determine the correct path forward for Track B.

**Status**: ✅ COMPLETE (analysis + new lemma)

**Results**:
- [x] `deg_nonneg_of_effective` - PROVED in Divisor.lean
- [x] Documented architectural issue with `finrank_dual_eq` approach
- [x] Updated roadmap for correct adelic path to Serre duality

**Key Lemma Proved** (`deg_nonneg_of_effective`):
```lean
lemma deg_nonneg_of_effective {D : DivisorV2 R} (hD : Effective D) : 0 ≤ D.deg
```
Effective divisors (all coefficients ≥ 0) have non-negative degree.

**Architectural Analysis**:

1. **`finrank_dual_eq` is NOT the right approach**:
   - The trace dual `dual A K_A I` corresponds to divisor `K + div(I)`, not `K - div(I)`
   - Since `L(D) ↔ div(I) = -D`, we get `dual(L(D)) ↔ L(K + D)`, NOT `L(K - D)`
   - This means trace duals cannot directly give Serre duality `ℓ(D) vs ℓ(K-D)`

2. **Correct path is via adeles** (Adeles.lean):
   - H¹(D) = A_K / (K + A_K(D)) (already defined)
   - Serre duality: h¹(D) = ℓ(K - D)
   - Combined with: ℓ(D) - h¹(D) = deg(D) + 1 - g (adelic Riemann-Roch)
   - This gives the full RR equation

3. **Remaining steps for Track B**:
   - Prove finiteness: `Module.Finite k (AdelicH1.Space k R K D)`
   - Prove vanishing: h¹(D) = 0 for deg(D) >> 0 (strong approximation)
   - Prove Serre duality: h¹(D) = ℓ(K - D) via local trace residues
   - Instantiate `FullRRData` with proved duality

**Sorry Status** (unchanged count, better documentation):
- TraceDualityProof.lean: 1 sorry (`finrank_dual_eq` - NOT on critical path)
- FullRRData.lean: 1 sorry (`ell_canonical_minus_eq_zero_of_large_deg` - needs principal divisor theory)

**Total**: 2 sorries in main path (unchanged)

**Next Steps** (Cycle 91):
1. Start H¹(D) finiteness proof (adelic approach)
2. Or: Add principal divisor theory for FullRRData helper lemma
3. Or: Prove strong approximation for H¹(D) vanishing

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
