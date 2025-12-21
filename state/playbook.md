# Playbook

Strategic guide for formalizing Riemann-Roch. Updated Cycle 182.

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

### Phase 3: Serre Duality (Current - Cycle 192)

**Completed:**
- Residue at X (X-adic) via HahnSeries.coeff(-1) ✅
- Residue at infinity via degree formula ✅
- Residue at linear places via translation ✅
- Residue theorem for split denominators ✅
- Bilinear pairing `residuePairing g f := residueSumTotal(g*f)` ✅
- Perfect pairing → equal dimensions ✅
- Diagonal embedding infrastructure (RatFunc Fq) ✅
- K-part of well-definedness (globalSubmodule → 0) ✅
- CRT for linear places (`crt_linear_places`) ✅
- Pairwise coprimality of linear place ideals ✅

**In Progress - Strong Approximation:**
- Statement added: `strong_approximation_ratfunc` (sorry)
- Key lemma: For any finite adele a, exists k ∈ K with a - diag(k) ∈ A_K(D)
- Proof strategy: Use CRT to construct polynomial matching adele at bad places
- Technical gap: connecting adicCompletion to ideal quotients

**Blocked On:**
- `strong_approximation_ratfunc` → unlocks `h1_vanishing_ratfunc`
- `h1_vanishing_ratfunc` → makes non-degeneracy vacuous
- Non-degeneracy → completes Serre duality for genus 0

---

## Strong Approximation Details (Cycle 192)

### FiniteAdeleRing Structure

```lean
-- Mathlib definition (restricted product):
def FiniteAdeleRing : Type _ :=
  Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

-- Key: Πʳ means restricted product with cofinite filter
-- Elements are integral at almost all places
```

**Accessing elements:**
- `a v` - component at place v (via DFunLike)
- `a.1` - underlying function `v → v.adicCompletion K`
- `a.2` - proof: `∀ᶠ v in cofinite, a v ∈ v.adicCompletionIntegers K`

**Key Mathlib files:**
- `Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean` - main definition
- `Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean` - RestrictedProduct

### CRT Infrastructure (Proved)

```lean
-- Pairwise coprimality of linear place ideals
lemma linearPlaces_pairwise_coprime {ι : Type*} (α : ι → Fq) (hinj : Function.Injective α) :
    Pairwise fun i j => IsCoprime (linearPlace (α i)).asIdeal (linearPlace (α j)).asIdeal

-- CRT for distinct places with specified remainders
lemma crt_linear_places {n : ℕ} (places : Fin n → HeightOneSpectrum (Polynomial Fq))
    (hinj : Function.Injective places)
    (exponents : Fin n → ℕ)
    (targets : Fin n → Polynomial Fq) :
    ∃ p : Polynomial Fq, ∀ i,
      p - targets i ∈ (places i).asIdeal ^ (exponents i)
```

### Proof Strategy for `strong_approximation_ratfunc`

Given `a : FiniteAdeleRing (Polynomial Fq) (RatFunc Fq)` and `D : DivisorV2`:

1. **Find bad places S**: Use `a.2` (eventually integral) to get finite set where either:
   - `a_v` is non-integral, OR
   - `Valued.v (a_v) > WithZero.exp (D v)`

2. **For each v ∈ S**: Extract a polynomial approximation of `a_v`:
   - `v.adicCompletion K` is completion of K at v
   - For RatFunc Fq, this is Laurent series in local parameter
   - Truncating at valuation level gives polynomial approximation

3. **Apply CRT**: Use `crt_linear_places` to find `p : Polynomial Fq` matching targets

4. **Verify**: Show `∀ v, Valued.v ((a - diag p)_v) ≤ WithZero.exp (D v)`

### Technical Gap

The missing piece is the connection:
```
v.adicCompletion K ←→ R / v.asIdeal^n (for large n)
```

Possible approaches:
- Use `ValuationSubring` and `Valuation.map` properties
- For RatFunc Fq specifically: use Laurent series structure directly
- Look for `IsDedekindDomain.quotientEquivPiSpanPowQuot` or similar

---

## Key References

- Mathlib: `RingTheory.DedekindDomain.Different` (trace dual, different ideal)
- Mathlib: `RingTheory.DedekindDomain.FiniteAdeleRing` (adeles)
- Mathlib: `RingTheory.DedekindDomain.Ideal.Lemmas` (CRT: `exists_forall_sub_mem_ideal`)
- Mathlib: `RingTheory.Ideal.Quotient.Operations` (general CRT)
- Mathlib: `RingTheory.Length` (Module.length for exact sequences)
- Mathlib: `Algebra.Trace` (trace form)
- Stacks Project: Tag 0BXE (Serre duality for curves)
