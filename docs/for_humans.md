# Riemann-Roch Formalization: Current State

*Last updated: Cycle 9 (December 2024)*

## The Goal

Prove the Riemann-Roch theorem for smooth projective curves:

```
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
```

Where:
- `ℓ(D)` = dim H⁰(X, O_X(D)) - dimension of global sections
- `K` = canonical divisor
- `g` = genus = dim H¹(X, O_X)

---

## Project Architecture: Two Parallel Tracks

### Track A: Axiomatized Interface (Cycles 1-3)
We built an abstract interface that captures the *shape* of Riemann-Roch:
- `RRData` → `RRDataWithCohomology` → `RRDataWithEuler`
- The "theorem" `RRDataWithEuler.riemannRoch` is **DERIVED FROM ASSUMPTIONS** (circular)
- `eulerChar_formula` IS Riemann-Roch in disguise

### Track B: Real Foundations (Cycles 4-9) ✅ ACTIVE
We're building real mathematical infrastructure from scratch:
- Divisors, function fields, Riemann-Roch spaces
- Eventually will instantiate Track A with these real objects

---

## What We've Built (Cycles 4-9)

### Cycle 4: Divisor Foundations ✅
```lean
abbrev Divisor (α : Type*) := α →₀ ℤ  -- Finitely supported functions
def deg (D : Divisor α) : ℤ := D.sum (fun _ n => n)  -- Sum of coefficients
```
**PROVED**: `deg_add`, `deg_zero`, `deg_neg`, `deg_sub`, `deg_single`

### Cycle 5: Function Field Interface ✅
```lean
structure FunctionFieldData (α : Type*) (k : Type*) [Field k] where
  K : Type*              -- The function field
  div : K → Divisor α    -- Principal divisor map
  div_mul : div(f*g) = div(f) + div(g)
  deg_div : deg(div f) = 0  -- Principal divisors have degree 0
  ...
```
**PROVED**: `Effective_iff`, `Effective_zero`, `Effective_add`, `div_zero`

### Cycle 6: L(D) is a Vector Space ✅
```lean
def RRSpace (data : FunctionFieldData α k) (D : Divisor α) : Submodule k data.K
-- L(D) = { f ∈ K | f = 0 or div(f) + D ≥ 0 }
```
**PROVED**: `zero_mem'`, `add_mem'`, `smul_mem'`, `mono`

### Cycle 7: Dimension ℓ(D) ✅
```lean
def ell (data : FunctionFieldData α k) (D : Divisor α) : ℕ :=
  Module.finrank k (RRSpace data D)
```
**PROVED**: `ell.mono`, `ell.pos_of_effective`, `ell.zero_pos`

### Cycle 8: Finite-Dimensionality ✅
Using typeclass `[∀ D, Module.Finite k (RRSpace data D)]`:
**PROVED**: All 8 unconditional versions of Cycle 7 lemmas

### Cycle 9: Quotient Infrastructure ✅
```lean
lemma ell.quotient_add_eq_of_le (h : D ≤ E) :
    finrank k (L(E) / L(D)) + ℓ(D) = ℓ(E)
```
**PROVED**: `submodule_inclusion_injective`, `quotient_add_eq_of_le`, `quotient_le_of_le`
**STATED**: `add_single_le_succ`, `le_deg_add_ell_zero` (Riemann inequality)

---

## Current Score

| Category | Count |
|----------|-------|
| **Definitions** | 7 (Divisor, deg, single, Effective, FunctionFieldData, RRSpace, ell) |
| **Lemmas PROVED** | 28 |
| **Lemmas STATED (sorry)** | 4 (Riemann inequality chain) |
| **Axiomatized interface** | Exists but circular |

---

## The Current Blocker

To prove **Riemann's inequality** `ℓ(D) ≤ deg(D) + ℓ(0)`, we need:

```
ℓ(D + p) ≤ ℓ(D) + 1   (single-point dimension bound)
```

This requires: `dim(L(E)/L(D)) ≤ deg(E) - deg(D)`

**Why we can't prove this yet:**
- Need an **evaluation map** `eval_p : L(D + p) → k`
- With kernel `ker(eval_p) = L(D)`
- First isomorphism theorem gives: `L(D+p)/L(D) ≅ im(eval_p) ⊆ k`
- Therefore dimension ≤ 1

**Options for Cycle 10:**
1. Axiomatize `single_point_bound` as structure field (simple)
2. Add evaluation map to `FunctionFieldData` (principled)
3. Add valuations `v_p : K* → ℤ` (general)

---

## Dependency Graph

```
                    Divisor (α →₀ ℤ)
                          │
                    ┌─────┴─────┐
                    ▼           ▼
                   deg       Effective
                    │           │
                    └─────┬─────┘
                          ▼
                  FunctionFieldData
                    (K, div, ...)
                          │
                          ▼
                  RRSpace (L(D) ⊆ K)
                          │
              ┌───────────┼───────────┐
              ▼           ▼           ▼
           mono       add_mem     smul_mem
              │           │           │
              └─────┬─────┴───────────┘
                    ▼
            ell = finrank k L(D)
                    │
         ┌──────────┼──────────┐
         ▼          ▼          ▼
    ell.mono   pos_of_eff   zero_pos
         │          │          │
         └────┬─────┴──────────┘
              ▼
      quotient_add_eq_of_le
        dim(L(E)/L(D)) + ℓ(D) = ℓ(E)
              │
              ▼
      ??? BLOCKER: eval map ???
              │
              ▼
      add_single_le_succ
        ℓ(D+p) ≤ ℓ(D) + 1
              │
              ▼
      le_deg_add_ell_zero
        ℓ(D) ≤ deg(D) + ℓ(0)   (Riemann inequality!)
```

---

## mathlib Gaps (Still True)

mathlib **lacks**:
- Divisors on schemes (Weil or Cartier)
- Line bundles / invertible sheaves
- Genus, canonical divisor, canonical sheaf
- Sheaf cohomology H⁰, H¹
- Serre duality

mathlib **has** (and we use):
- `Finsupp` - finitely supported functions (our `Divisor`)
- `Submodule` - vector subspaces
- `Module.finrank` - dimension
- `Submodule.finrank_quotient_add_finrank` - rank-nullity

---

## File Structure

```
roch-riemann/
├── RrLean/
│   └── RR.lean              # Main formalization (659 lines)
├── problem/
│   └── problem.md           # Mathematical target (READ-ONLY)
├── state/
│   ├── playbook.md          # Strategy and heuristics
│   ├── candidates.json      # All candidates with status
│   └── ledger.md            # Cycle-by-cycle history
├── agents/
│   ├── orchestrator.md      # ACE loop controller
│   ├── generator.md         # Proposes candidates
│   ├── reflector.md         # Scores candidates
│   └── curator.md           # Updates state files
├── scripts/
│   ├── rg_mathlib.sh        # Search mathlib
│   └── commit_cycle.sh      # Commit helper
└── docs/
    ├── for_humans.md        # This file
    └── explainer.html       # Visual explainer
```

---

## Lessons Learned

1. **Build foundations first** - Abstract interfaces are useful scaffolding but not proofs
2. **Use mathlib idioms** - `Finsupp`, `Submodule`, typeclasses work well
3. **Track dependencies** - Know what blocks what
4. **Fail fast, recover faster** - Don't delete working code (see Cycle 9 recovery)
5. **Semantic honesty** - Label PROVED vs STATED vs DERIVED_FROM_ASSUMPTIONS

---

## What's Next?

**Cycle 10**: Add evaluation machinery and prove Riemann inequality

**Eventually**: Connect `FunctionFieldData` to `RRData` and complete the circle

**Dream**: A real, verified proof of Riemann-Roch in Lean 4
