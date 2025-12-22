# Playbook

Strategic guide for formalizing Riemann-Roch. Updated Cycle 236.

---

## Ultimate Goal

Formalize the **Riemann-Roch theorem** for function fields in Lean 4 — **no axioms, no sorries**:

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

Where:
- `ℓ(D)` = dimension of L(D) over the base field k
- `K` = canonical divisor (from differentIdeal)
- `g` = genus
- `deg(D)` = degree of divisor D

---

## Mathematical Strategy: Adelic Serre Duality

We prove Serre duality `h¹(D) = ℓ(K-D)` via the adelic approach, using only Mathlib primitives.

### Why Not Trace Dual Directly?

The naive approach fails because:
```
div(dual I) = K - div(I)
→ dual(I_{-D}) gives I_{K+D}, hence L(K+D)
→ But we need L(K-D) for Serre duality
```

### The Correct Approach

Construct a perfect pairing via residues:
```
⟨·,·⟩ : H¹(D) × L(K-D) → k
⟨[a], f⟩ := ∑_v res_v(a_v · f)
```

**Step 1: Construct the pairing**
- Define local residue `res_v : K_v → k` at each place
- Sum over all places to get global pairing

**Step 2: Show well-defined**
- If `a ∈ K`, then `∑_v res_v(a·f) = 0` (residue theorem)
- If `a ∈ A_K(D)` and `f ∈ L(K-D)`, product has no poles

**Step 3: Show non-degenerate**
- Left: `⟨[a], f⟩ = 0` for all f ⟹ `[a] = 0`
- Right: `⟨[a], f⟩ = 0` for all [a] ⟹ `f = 0`
- Uses: `FractionalIdeal.dual_dual`, `differentIdeal_ne_bot`

**Step 4: Conclude dimension equality**
- Perfect pairing ⟹ `dim H¹(D) = dim L(K-D)`
- Therefore: `h¹(D) = ℓ(K-D)`

### Key Mathlib Resources

| Component | Import | Key Definitions |
|-----------|--------|-----------------|
| Laurent series | `RingTheory.LaurentSeries` | `LaurentSeries`, `HahnSeries.coeff` |
| Trace dual | `RingTheory.DedekindDomain.Different` | `Submodule.traceDual`, `differentIdeal` |
| Fractional ideal dual | `RingTheory.DedekindDomain.Different` | `FractionalIdeal.dual`, `dual_dual` |
| Finite adeles | `RingTheory.DedekindDomain.FiniteAdeleRing` | `FiniteAdeleRing`, `adicCompletion` |
| RatFunc coercion | `RingTheory.LaurentSeries` | `RatFunc F → LaurentSeries F` |

### Critical Definitions

```lean
-- Trace dual: x such that Tr(x·y) ∈ A for all y ∈ I
def Submodule.traceDual (I : Submodule B L) : Submodule B L :=
  {x : L | ∀ y ∈ I, Algebra.trace A L (x * y) ∈ A}

-- Different ideal: inverse of trace dual of 1
def differentIdeal : Ideal B :=
  (1 / Submodule.traceDual A K 1).comap (algebraMap B L)

-- Key property
lemma coeIdeal_differentIdeal :
  ↑(differentIdeal A B) = (FractionalIdeal.dual A K 1)⁻¹
```

---

## Architecture

### Type Hierarchy
```
k : Field                    -- base field (e.g., Fq)
R : CommRing, IsDedekindDomain  -- coordinate ring (e.g., Fq[X])
K : Field, IsFractionRing R K   -- function field (e.g., RatFunc Fq)

HeightOneSpectrum R          -- finite places
K∞ : Valued field            -- completion at infinity

FiniteAdeleRing R K          -- restricted product ∏'_v K_v
FullAdeleRing := FiniteAdeleRing × K∞
```

### Key Constructions
```
DivisorV2 R := v →₀ ℤ           -- divisor as Finsupp
L(D) := {f ∈ K | v(f) ≥ -D(v)}  -- Riemann-Roch space
ℓ(D) := finrank k L(D)          -- dimension

A_K(D) := {a ∈ 𝔸_K | v(a_v) ≥ -D(v)}  -- bounded adeles
H¹(D) := 𝔸_K / (K + A_K(D))           -- adelic H¹

canonical := -div(differentIdeal)
```

### Architectural Shortcut: FiniteAdeleRing for H¹

**Decision (Cycle 188)**: Use `FiniteAdeleRing` (not `FullAdeleRing`) for H¹(D).

**Issue**: The residue theorem requires summing over ALL places (finite + ∞), but
`AdelicH1v2.SpaceModule` uses `FiniteAdeleRing` which excludes infinity.

**Workaround for genus 0** (RatFunc Fq):
- Canonical divisor K = -2[∞] has K(v) = 0 at all finite v
- So L(K-D) functions have no poles at finite places
- Finite residue sum vanishes for bounded × L(K-D) by pole cancellation
- For diagonal K: use `residueSumFinite = -residueAtInfty` (residue theorem)
- Pairing: extract diagonal part, compute via `-residueAtInfty(k·f)`

**Limitation**: This shortcut relies on genus 0. For higher genus curves, may need
to refactor to use `FullAdeleRing` or extend `DivisorV2` to include infinity.

### File Structure
```
RrLean/RiemannRochV2/
├── Basic.lean              # Shared imports
├── Divisor.lean            # DivisorV2, deg, Effective
├── RRSpace.lean            # L(D), ℓ(D)
├── Typeclasses.lean        # LocalGapBound, SinglePointBound
├── RiemannInequality.lean  # ℓ(D) ≥ deg(D) + 1 - g ✅
├── Infrastructure.lean     # Residue field, uniformizer
├── RRDefinitions.lean      # DVR-valuation bridge
├── FullAdelesBase.lean     # Full adele ring definition
├── FullAdelesCompact.lean  # Compactness, discreteness ✅
├── DifferentIdealBridge.lean  # L(D) ↔ FractionalIdeal ✅
├── AdelicH1v2.lean         # H¹(D), AdelicRRData ✅
├── Residue.lean            # residueAtX, residueAtInfty, residueAt ✅
├── SerreDuality.lean       # residuePairing, serrePairing (in progress)
└── FullRRData.lean         # Full RR theorem (pending)
```

---

## Heuristics

### General Lean Advice
- Prefer `finrank k` for dimensions; avoid Nat-based dims
- Keep lemma statements small: fewer binders, fewer coercions
- When stuck on coercions, introduce explicit `let` bindings

### Archaeology-First Rule
Before writing a new proof, spend 15+ min searching Mathlib:
- `*_iff_*` for characterizations
- `exists_*` for existence lemmas
- Check specific module APIs (`ValuationSubring`, `IsFractionRing`, etc.)

### Frontier Freeze Rule
Don't add new sorry candidates while a key blocker is stuck. Sorry count creeping up without progress on the hard lemma is a warning sign.

### DVR/Valuation Anti-Pattern
Avoid constructing uniformizers manually. The moment you say "find π with v(π)=...", you're in for `Associates`, `Irreducible`, `UniqueFactorizationMonoid` juggling. Instead:
- Use localization universal properties
- Work inside the DVR where API is cleanest, then transport
- Look for `exists_lift_of_le_one` patterns

### Reframing Rule
If a "converse" lemma is hard, check if there's a higher-level equivalence giving both directions for free.

---

## What's Proved (Milestones)

### Phase 1: Riemann Inequality ✅
```lean
lemma riemann_inequality_affine [BaseDim R K] {D : DivisorV2 R} (hD : D.Effective) :
    (ellV2_real R K D : ℤ) ≤ D.deg + bd.basedim
```
- Tag: `v1.0-riemann-inequality` (2025-12-18)
- Cycles 1-75

### Phase 2: Adelic Infrastructure ✅
- K discrete in full adeles
- K closed in full adeles
- Integral adeles compact
- Weak approximation
- Cycles 76-155

### Phase 3: Dimension Formula for P¹ - IN PROGRESS (Cycle 236)

**Status**: Build compiles. Core theorem `ell_ratfunc_projective_single_linear` proved (modulo DimensionCore sorries).

---

## ⚠️ POST-MORTEM: The Cycle 232-236 Disconnect

### What Happened

**Cycle 232** claimed "RIEMANN-ROCH FOR P¹ PROVED! 🎉" in the git commit. This was **incorrect**.

What was actually true:
- Theorem *statements* existed and type-checked
- There were sorries in the proof chain
- The claim conflated "compiles with sorries" with "proved"

**Cycles 233-235** attempted to fill those sorries and made things worse:
- Tried to prove `Module.Finite` using `finrank` (circular: finrank needs Module.Finite)
- Broke the build entirely - DimensionScratch.lean had compilation errors, not just sorries
- Each cycle added more attempted fixes, creating technical debt

**Cycle 236** fixed the architecture:
- Created DimensionCore.lean with correct finiteness approach (embedding into finite-dim space)
- Build compiles again
- Added Smoke.lean for build hygiene verification

### Root Cause Analysis

1. **Premature victory declaration**: Cycle 232 claimed completion without checking `#print axioms`
2. **Circular reasoning trap**: Cycles 233-235 attempted the same broken pattern repeatedly
3. **No mechanical verification**: No smoke test to catch when "proved" theorems used `sorryAx`

### Lessons Learned

1. **Never claim "proved" without `#print axioms` showing no `sorryAx`**
2. **Finiteness must come from embeddings, not from finrank bounds**
3. **Add smoke tests that mechanically verify proof completeness**

---

## Honest Sorry Audit (Cycle 236)

### CRITICAL PATH FOR P¹ (6 sorries)

**DimensionCore.lean** (5 sorries) - finiteness via embedding:
| Line | Lemma | What's needed |
|------|-------|---------------|
| 67 | `mul_X_sub_pow_is_polynomial` | Prove (X-α)^n·f is poly of deg ≤ n from valuation bounds |
| 88 | `partialClearPoles.map_add'` | Linear map respects addition |
| 92 | `partialClearPoles.map_smul'` | Linear map respects scalar mult |
| 101 | `partialClearPoles_injective` | Multiplication by nonzero is injective |
| 126 | `RRSpace_ratfunc_projective_add_single_finite` | Finiteness for D + [v] |

**DimensionScratch.lean** (1 sorry):
| Line | Theorem | What's needed |
|------|---------|---------------|
| 892 | `ell_ratfunc_projective_eq_deg_plus_one` | Strong induction on deg(D), uses single_linear as base |

### NOT ON P¹ CRITICAL PATH (15 sorries)

These are imported but not used by the dimension theorems:

| File | Sorries | Purpose |
|------|---------|---------|
| AdelicH1Full.lean | 8 | Adelic approach (alternative track) |
| FullAdelesCompact.lean | 1 | Adelic infrastructure |
| Residue.lean | 2 | General residue theorem, higher-degree places |
| RatFuncPairing.lean | 1 | Negative degree edge case |
| TraceDualityProof.lean | 1 | Trace dual dimension |
| ProductFormula.lean | 1 | Product formula |
| FullAdeles.lean | 1 | Full adele infrastructure |

### What's Actually Proved (no sorryAx)

- ✅ `linearPlace_residue_equiv` - κ(v) ≃+* Fq
- ✅ `linearPlace_residue_finrank` - finrank Fq κ(v) = 1
- ✅ `ell_ratfunc_projective_gap_le` - ℓ(D+[v]) ≤ ℓ(D) + 1
- ✅ `inv_X_sub_C_pow_mem_projective` - explicit elements in L(D)
- ✅ `inv_X_sub_C_pow_not_mem_projective_smaller` - strict inclusion
- ✅ `ell_canonical_sub_zero` - ℓ(K-D) = 0 for deg(D) ≥ -1

### What's Proved Modulo DimensionCore Sorries

- ⚠️ `ell_ratfunc_projective_single_linear` - ℓ(n·[v]) = n+1
  - Proof structure complete, uses DimensionCore finiteness instances
  - When DimensionCore sorries filled, this becomes sorry-free

### Verification Command

```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
# Currently shows sorryAx (expected)
# When empty, P¹ RR is complete
```

---

## Technical Reference: Strong Approximation (PROVED - Cycle 204)

The key infrastructure for strong approximation is complete. For reference:

### FiniteAdeleRing Structure
```lean
def FiniteAdeleRing : Type _ :=
  Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]
```
- `a v` - component at place v
- `a.2` - proof of eventual integrality

### Key Proved Lemmas
- `linearPlaces_pairwise_coprime` - Coprimality of (X - α) ideals
- `crt_linear_places` - CRT for distinct places
- `exists_principal_part_at_spec` - Principal part extraction
- `exists_polyRep_of_integral_mod_pow` - Polynomial representatives
- `exists_global_approximant_from_local` - Gluing local to global
- `strong_approximation_ratfunc` ✅ - Main theorem

---

## Key References

- Mathlib: `RingTheory.DedekindDomain.Different` (trace dual, different ideal)
- Mathlib: `RingTheory.DedekindDomain.FiniteAdeleRing` (adeles)
- Mathlib: `RingTheory.DedekindDomain.Ideal.Lemmas` (CRT: `exists_forall_sub_mem_ideal`)
- Mathlib: `RingTheory.Ideal.Quotient.Operations` (general CRT)
- Mathlib: `RingTheory.Length` (Module.length for exact sequences)
- Mathlib: `Algebra.Trace` (trace form)
- Stacks Project: Tag 0BXE (Serre duality for curves)
