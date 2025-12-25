# Playbook

Strategic guide for formalizing Riemann-Roch. Updated Cycle 311.

---

## State Folder Overview

```
state/
├── playbook.md          # This file - strategy, heuristics, lessons learned
├── ledger.md            # Tactical tracking - current cycle, recent changes, next steps
├── ledger_archive.md    # Historical cycles 1-240
├── PROOF_CHAIN.md       # Import chain from theorems to Mathlib, file status
├── REFACTOR_PLAN.md     # Roadmap for generalizing P¹ → arbitrary curves
├── INVENTORY_REPORT.md  # Deep scan of all files (from Cycle 241 refactor)
└── gemini_deepthink.md  # External architectural analysis (Gemini)
```

| File | When to read | When to update |
|------|--------------|----------------|
| `ledger.md` | Start of every cycle | End of every cycle |
| `playbook.md` | When stuck or planning | When learning new lessons |
| `PROOF_CHAIN.md` | After adding new files | After connecting files to chain |
| `REFACTOR_PLAN.md` | When planning next phase | After completing a phase |

---

## Ultimate Goal

Formalize **Riemann-Roch** for **algebraically closed curves** in Lean 4:

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

### Current Status (Cycle 311)

| Component | Status |
|-----------|--------|
| P¹ Riemann-Roch formula | ✅ Complete (frozen) |
| P¹ Serre duality (effective D) | ✅ Complete (frozen) |
| Elliptic curves (genus 1) | ✅ RR proved (axiomatized) |
| **Phase 7: Weil Differentials** | ⏳ **Active** |

---

## Phase 7: The Weil Differential Strategy

### Why Weil Differentials?

**P¹ Limitation**: The current residue pairing uses functions directly because:
- The canonical bundle Ω is trivial on P¹ (dt is global)
- Functions can substitute for differentials

**General Curves (g ≥ 2)**: No global differential exists. Must use Weil differentials.

### The Key Insight

**Old approach** (P¹-specific):
```lean
⟨f, g⟩ = Σ_v res_v(f · g)  -- Residue sum
```
Requires: 2000+ LOC of residue infrastructure, residue theorem, pole cancellation.

**New approach** (general):
```lean
⟨f, ω⟩ = ω(f)  -- Just evaluation!
```
The residue theorem is *implicit* in the definition of WeilDifferential (vanishes on K).

### Definition

A **Weil differential** is a K-linear functional ω : A_K → k that vanishes on K embedded diagonally.

```lean
structure WeilDifferential (k R K K_infty : Type*) ... where
  toLinearMap : FullAdeleRing R K K_infty →ₗ[k] k
  vanishes_on_K : ∀ x : K, toLinearMap (fullDiagonalEmbedding x) = 0
```

### Key Properties to Prove

1. **dim_K(WeilDifferential) = 1** - Space is 1-dimensional over K
2. **Local components** - Extract ω_P from global ω at each place P
3. **Valuation** - v_P(ω) = max n s.t. ω vanishes on A_K(nP) at P
4. **Canonical divisor** - (ω) = Σ_P v_P(ω) · P
5. **deg(K) = 2g - 2** - Follows from theory

### Key References

- [Rosen "Number Theory in Function Fields" Ch. 6](https://link.springer.com/chapter/10.1007/978-1-4757-6046-0_6)
- [Stichtenoth "Algebraic Function Fields and Codes" §1.7](https://link.springer.com/book/10.1007/978-3-540-76878-4)
- [Charles University Thesis](https://dspace.cuni.cz/bitstream/handle/20.500.11956/62611/DPTX_2012_2_11320_0_392289_0_137152.pdf)

---

## What's Proved

```lean
-- Main Serre duality for P¹
theorem serre_duality_p1 (D : ExtendedDivisor (Polynomial Fq))
    (hDfin : D.finite.Effective) (hD : D.inftyCoeff ≥ 0) :
    h1_finrank_full Fq D = ell_proj_ext Fq (canonicalExtended Fq - D)

-- Full P¹ Riemann-Roch formula
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) : ell_ratfunc_projective D = D.deg.toNat + 1
```

---

## Architectural Lessons

### 1. The Generator Trap

**Problem**: P¹ works because `Polynomial Fq` is a PID (every prime ideal is principal).
General curves have Dedekind but NOT PID coordinate rings.

**Rule**: Keep infrastructure abstract. Use `uniformizerAt` (local uniformizers always exist).

```lean
-- WRONG (in general infrastructure):
structure Place where
  generator : Polynomial Fq  -- Assumes PID!

-- RIGHT:
class HasUniformizer (v : HeightOneSpectrum R) where
  π : K
  val_eq_one : v.valuation K π = 1
```

### 2. The Dimension Formula Trap

**Problem**: `ℓ(D) = deg(D) + 1` is genus-0 ONLY.

| Curve | Formula |
|-------|---------|
| P¹ (g=0) | ℓ(D) = deg(D) + 1 |
| Elliptic (g=1) | ℓ(D) = deg(D) for deg > 0 |
| General | ℓ(D) - ℓ(K-D) = deg(D) + 1 - g |

**Rule**: Any file proving `ℓ(D) = deg(D) + 1` is P¹-specific, not general.

### 3. The Residue/Differential Trap (Resolved by Phase 7)

**Problem**: Residues are defined on *differentials*, not functions.
For P¹, dt is a global differential, so we can identify functions with differentials.
General curves have no global differential.

**Solution**: Use Weil Differentials (dual of adeles mod K).

```lean
-- For P¹: Functions work because dt trivializes Ω
def residuePairing (f : RatFunc Fq) (a : Adele) : Fq := ...

-- For general curves: Use Weil differentials
structure WeilDifferential (K : Type*) where
  toFun : Adele K → k
  vanishes_on_K : ∀ f : K, toFun (diagonal f) = 0
```

### 4. The Axiom Strategy

**When to axiom**: "Trivial but tedious" gaps orthogonal to your goal.

**Current Axiom Stack**:
| Axiom | Justification | Used For |
|-------|---------------|----------|
| `IsDedekindDomain CoordRing` | Hartshorne II.6 | HeightOneSpectrum |
| `StrongApprox K` | K dense in A_S | H¹ computations |
| `h1_zero_eq_one` | Genus = 1 | Elliptic RR |
| `dim_K(WeilDiff) = 1` | Standard theory | Canonical class |

**When NOT to axiom**: The actual RR content you're trying to prove.

---

## Heuristics

### Weighted vs Unweighted Degree (Cycle 287)
- `DivisorV2.deg` = Σ D(v) (unweighted)
- `degWeighted` = Σ D(v) · deg(v) (weighted)
- For algebraically closed fields: these are equal

### What We Keep vs Replace (Phase 7)

| Component | P¹ Version | General Version |
|-----------|------------|-----------------|
| Adele ring | FullAdeleRing ✅ | Same (reuse) |
| H¹(D) definition | Quotient ✅ | Same (reuse) |
| Serre pairing | residueSumTotal | ω(f) evaluation |
| Canonical divisor | -2[∞] (hardcoded) | div(ω) (intrinsic) |

---

## Cycle Discipline

### One Cycle = One Focused Goal

**Good scope**:
- Fill ONE sorry with a clean proof
- Add ONE new definition + basic lemmas
- Explore ONE new curve type

**Bad scope**:
- "Fill all sorries in this file"
- "Implement general curves completely"

### Sorry Classification

| Type | Example | Action |
|------|---------|--------|
| **Content** | Serre duality proof | Must fill |
| **Infrastructure** | `IsDedekindDomain` | Can axiom |
| **Archived** | P¹ edge cases | Skip (PID-specific) |

---

## Verification Commands

```bash
# Check sorry count
lake build 2>&1 | grep -E "sorry|^error:"

# Full build
lake build

# Check specific file
lake build RrLean.RiemannRochV2.SerreDuality.General.AdelicH1Full
```

---

## Key Files for New Contributors

| Goal | Start Here |
|------|------------|
| Understand P¹ proof | `P1Instance/P1VanishingLKD.lean` |
| Understand Serre duality | `SerreDuality/General/Abstract.lean` |
| Understand adelic H¹ | `Adelic/AdelicH1v2.lean` |
| **Start Phase 7** | `General/WeilDifferential.lean` (new) |
| See what's proved | `state/PROOF_CHAIN.md` |

---

*Updated Cycle 311. Phase 7 active. See ledger.md for current state and REFACTOR_PLAN.md for roadmap.*
