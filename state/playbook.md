# Playbook

Strategic guide for formalizing Riemann-Roch. Updated Cycle 255.

---

## State Folder Overview

```
state/
├── playbook.md          # This file - strategy, heuristics, lessons learned
├── ledger.md            # Tactical tracking - current cycle, recent changes, next steps
├── ledger_archive.md    # Historical cycles 1-240
├── PROOF_CHAIN.md       # Import chain from theorems to Mathlib, file status
├── REFACTOR_PLAN.md     # Roadmap for generalizing P¹ → arbitrary curves
└── INVENTORY_REPORT.md  # Deep scan of all files (from Cycle 241 refactor)
```

| File | When to read | When to update |
|------|--------------|----------------|
| `ledger.md` | Start of every cycle | End of every cycle |
| `playbook.md` | When stuck or planning | When learning new lessons |
| `PROOF_CHAIN.md` | After adding new files | After connecting files to chain |
| `REFACTOR_PLAN.md` | When planning next phase | After completing a phase |
| `INVENTORY_REPORT.md` | Reference only | Rarely (was a one-time scan) |

---

## Cycle Discipline

**Critical Lesson from Cycles 230-241**: We got impatient near the end and tried to do too much per cycle. This led to context overflow, incomplete work, and debugging spirals.

### The ~50k Token Reality

Each Claude cycle has ~50k usable tokens of context. This means:
- **Read**: ~3-5 files deeply, or ~10 files shallowly
- **Write**: ~200-400 lines of new code max
- **Debug**: 2-3 error-fix iterations before context exhaustion

### One Cycle = One Focused Goal

**Good cycle scope**:
- Fill ONE sorry with a clean proof
- Add ONE new definition + basic lemmas
- Fix ONE compilation error chain
- Refactor ONE file (extract/reorganize)

**Bad cycle scope**:
- "Fill all sorries in this file" (unless trivial)
- "Implement the full residue theorem"
- "Refactor the adelic infrastructure"

### When to Slow Down for Infrastructure

If you're about to write a proof and find yourself saying:
- "I need a helper lemma for X"
- "This would be cleaner if Y existed"
- "I'm pattern-matching on the same thing repeatedly"

**STOP.** That cycle should become an infrastructure cycle:
1. Write the helper/abstraction
2. Prove basic properties
3. Leave the original goal for NEXT cycle

### Ledger Discipline

The "Next Steps" section should contain:
1. **Immediate** (this cycle): ONE specific task with clear success criteria
2. **Context**: 1-2 sentences on WHY this task matters
3. **After**: Brief note on what unlocks after this task

Example:
```
## Next Steps

**Immediate**: Fill `smul_mem_boundedSubset_full` sorry (line 230)
- Show k-scalar multiplication preserves valuation bounds
- Success: `lake build AdelicH1Full` with no sorries

**Context**: This unblocks `SpaceModule_full` as the correct H¹(D) for arbitrary curves.

**After**: Complete the second sorry (line 234), then move to Place type definition.
```

### Refactor Plan Discipline

Update `REFACTOR_PLAN.md` when:
1. **Completing a phase**: Mark phase complete, note actual vs planned cycles
2. **Discovering blockers**: Add notes about unexpected dependencies
3. **Changing scope**: If a phase needs more/fewer cycles than planned, update estimates
4. **Learning insights**: Add lessons that affect future phases

Example update after completing Phase 1:
```
## Phase 1: Complete Incomplete Infrastructure
**Status**: COMPLETE (Cycles 243-247, originally estimated 243-249)
**Actual work**: AdelicH1Full sorries filled, RRSpace_proj_ext degree proofs added
**Lessons**: Degree bounds needed more infrastructure than expected
```

---

## Ultimate Goal

Formalize the **Riemann-Roch theorem** for **arbitrary smooth projective curves** over finite fields in Lean 4 — **no axioms, no sorries**:

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

Where:
- `ℓ(D)` = dimension of L(D) over the base field k
- `K` = canonical divisor (from differentIdeal)
- `g` = genus of the curve
- `deg(D)` = degree of divisor D

### Scope

| Curve Type | Genus | Status |
|------------|-------|--------|
| P¹ (projective line) | 0 | Current focus (linear places proved) |
| Elliptic curves | 1 | Future (Phase 6) |
| Hyperelliptic curves | (deg f - 1)/2 | Future (Phase 6) |
| General smooth projective | any g | Architecture supports it |

The core infrastructure (~3,700 lines) is **curve-agnostic**. Only the `AdelicRRData` instance needs to be provided for each curve family.

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

### Design Philosophy

The codebase is split into **curve-agnostic infrastructure** and **curve-specific instances**:

- **Infrastructure** (general): Divisors, L(D), adeles, H¹(D), Serre pairing machinery
- **Instances** (specific): P¹ over Fq, elliptic curves, hyperelliptic curves, etc.

To add a new curve, you provide an `AdelicRRData` instance. The RR theorem follows automatically.

### Type Hierarchy
```
k : Field                    -- base field (e.g., Fq)
R : CommRing, IsDedekindDomain  -- coordinate ring (e.g., Fq[X], or k[x,y]/(f))
K : Field, IsFractionRing R K   -- function field (e.g., RatFunc Fq, or Frac(R))

HeightOneSpectrum R          -- finite places (prime ideals of R)
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

### WithZero Valuation Anti-Pattern (Cycle 255 Lesson)
When proving properties about valuations in `WithZero (Multiplicative ℤ)`:
- **DON'T**: Try to compute with valuation outputs (division, inverse inequalities)
- **DO**: Work with polynomial structure (num/denom, coprimality, divisibility)

Example: To show "v(f) ≤ 1 at all finite places ⟹ f is polynomial":
- Bad: Try to prove `1/v(denom) > 1` when `v(denom) < 1` using WithZero lemmas
- Good: Use `IsCoprime`, `WfDvdMonoid.exists_irreducible_factor`, and `intValuation_lt_one_iff_mem`

The valuation API is designed for membership tests (`< 1 ↔ ∈ ideal`), not arithmetic.

---

## What's Proved (Milestones)

### Phase 1: Riemann Inequality ✅ (Curve-Agnostic)
```lean
lemma riemann_inequality_affine [BaseDim R K] {D : DivisorV2 R} (hD : D.Effective) :
    (ellV2_real R K D : ℤ) ≤ D.deg + bd.basedim
```
- Works for ANY Dedekind domain R with fraction field K
- Tag: `v1.0-riemann-inequality` (2025-12-18)
- Cycles 1-75

### Phase 2: Adelic Infrastructure ✅ (Curve-Agnostic)
- K discrete in full adeles
- K closed in full adeles
- Integral adeles compact
- Weak approximation
- Cycles 76-155

### Phase 3: Projective Framework - ✅ COMPLETE (Cycle 255)

**Status**: P¹ projective infrastructure complete and sorry-free.

**Completed** (Cycles 249-255):
- `Place.lean` ✅ - Unified Place type (finite + infinite)
- `DivisorV3.lean` ✅ - Projective divisors over all places
- `RRSpaceV3.lean` ✅ - Projective L(D) as k-module
- `P1Place.lean` ✅ - P¹ infinite place and ConstantsValuationBound
- `P1Canonical.lean` ✅ - Canonical divisor K = -2[∞]
- `P1VanishingLKD.lean` ✅ - L(K-D) = 0 for effective D

**Key Discovery** (Cycle 248): The "Affine Trap" - `HeightOneSpectrum R` only gives
finite places. Projective RR requires adding infinite places. See REFACTOR_PLAN.md.

**Next**: Wire P¹ projective infrastructure into Abstract.lean to fill remaining sorries.

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
4. **Don't use static sorry audits** - Cycle 236's "Honest Sorry Audit" table wasn't updated when sorries were filled (Cycles 237-240), causing stale info to propagate through Cycle 247. Use `grep -rn sorry` or the Smoke test instead of manually-maintained tables.

---

## Honest Sorry Audit (Cycle 255)

### Total: 3 sorries in non-archived code

**Abstract.lean** (3 sorries) - placeholder `AdelicRRData` instance:
| Line | Field | What's needed |
|------|-------|---------------|
| 199 | `h1_finite` | H¹ finiteness from compactness argument |
| 200 | `ell_finite` | L(D) finiteness from RRSpace theory |
| 202 | `h1_vanishing` | H¹ vanishing from strong approximation |

**Note**: These sorries require connecting P¹ projective infrastructure to Abstract.lean.
Phase 3 is now complete - next step is wiring the pieces together.

### Sorry-Free Files ✅

| File | Status |
|------|--------|
| P1VanishingLKD.lean | ✅ Sorry-free (Cycle 255) - NEW! |
| P1Canonical.lean | ✅ Sorry-free (Cycle 253) |
| P1Place.lean | ✅ Sorry-free (Cycle 252) |
| Place.lean | ✅ Sorry-free (Cycle 249) |
| DivisorV3.lean | ✅ Sorry-free (Cycle 250) |
| RRSpaceV3.lean | ✅ Sorry-free (Cycle 251) |
| DimensionCore.lean | ✅ Sorry-free |
| DimensionScratch.lean | ✅ Sorry-free |
| AdelicH1Full.lean | ✅ Sorry-free |
| All Core/ files | ✅ Sorry-free |
| All Adelic/ files | ✅ Sorry-free |

### What's Actually Proved (no sorryAx)

- ✅ `linearPlace_residue_equiv` - κ(v) ≃+* Fq
- ✅ `linearPlace_residue_finrank` - finrank Fq κ(v) = 1
- ✅ `ell_ratfunc_projective_gap_le` - ℓ(D+[v]) ≤ ℓ(D) + 1
- ✅ `inv_X_sub_C_pow_mem_projective` - explicit elements in L(D)
- ✅ `inv_X_sub_C_pow_not_mem_projective_smaller` - strict inclusion
- ✅ `ellV3_p1Canonical_sub_ofAffine_eq_zero` - ℓ(K-D) = 0 for effective D on P¹ (NEW Cycle 255!)
- ✅ `eq_algebraMap_of_valuation_le_one_forall` - polynomial characterization via valuations

### What's Proved Modulo DimensionCore Sorries

- ⚠️ `ell_ratfunc_projective_single_linear` - ℓ(n·[v]) = n+1
  - Proof structure complete, uses DimensionCore finiteness instances
  - When DimensionCore sorries filled, this becomes sorry-free

### Verification Command

```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
# No output = P¹ RR is complete (achieved Cycle 247!)
```

**See also**: `state/PROOF_CHAIN.md` for the full import chain and file status.

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
