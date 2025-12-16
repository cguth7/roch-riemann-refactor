# Ledger

## 2025-12-15
- Initial project setup: lakefile, toolchain, RR.lean stub
- Playbook initialized with 4 heuristic bullets
- ACE orchestration loop ready for Cycle 1

### Cycle 1
- **Discovery**: Searched mathlib for RR-related types
  - FOUND: `Scheme`, `IsSmooth`, `IsProper`, `Sheaf.H` (cohomology via Ext)
  - MISSING: WeilDivisor, CartierDivisor, InvertibleSheaf, LineBundle, genus, degree, canonical sheaf
- **Generator**: 8 candidates proposed, 6 BLOCKED due to missing mathlib types
- **Reflector**: No viable candidates. All blocked or fail relevance filter.
- **Decision**: RR.lean unchanged. Bootstrap invariant remains active.
- **Next step**: Need to either (1) define divisor/line bundle types in RR.lean, or (2) find alternative formulation using existing mathlib types.

### Cycle 2
- **Progress Gate triggered**: Same blockers for 2 consecutive cycles (mathlib lacks divisor, line bundle, genus, etc.)
- **Pivot decision**: Option 1 - Define internal interface `RRData`
- **Implementation**:
  - Created `structure RRData` bundling: X (Scheme), toSpec, Div (abstract type), divAddCommGroup, deg, ell, genus, K
  - Defined `RRData.riemannRochEq` as the RR equation proposition
  - Stated `theorem riemannRoch` and `riemannRoch'` with `sorry`
- **Result**: RR.lean elaborates successfully (only sorry warnings)
- **Bootstrap invariant**: DISABLED - theorem statement now typechecks
- **Next**: Fill sorry proofs; may need to add Serre duality as Prop field to RRData (NOT axiom)

#### Equivalence Audit (Trigger A, retroactive)
| problem.md concept | RRData representation | Status |
|---|---|---|
| Smooth projective curve X over k | `X : Scheme`, `toSpec : X ⟶ Spec k` | GROUNDED (real mathlib) |
| Divisor D on X | `Div : Type*`, no connection to X | ABSTRACTED (fake type concern) |
| H^0(X, O_X(D)) | `ell : Div → ℕ` | ABSTRACTED (opaque) |
| H^1(X, O_X) | `genus : ℕ` | ABSTRACTED (opaque) |
| Canonical divisor K | `K : Div` | ABSTRACTED (opaque) |
| deg(D) | `deg : Div → ℤ` | ABSTRACTED (opaque) |
| RR equation | `riemannRochEq` | PRESERVED (structurally identical) |

**Fake type concern**: `Div : Type*` has no semantic connection to `X`. To instantiate later, we need `Div` to be something like `WeilDivisor X` or `CartierDivisor X`.

**Equivalence**: CONDITIONAL. The theorem statement is structurally equivalent to problem.md, but only if we can later provide an `RRData` instance where:
- `Div` = actual divisors on X
- `ell D` = `finrank k (H^0(X, O_X(D)))`
- `genus` = `finrank k (H^1(X, O_X))`
- `K` = actual canonical divisor

**Verdict**: Acceptable as temporary scaffolding. Must track instantiation path.

### Cycle 3
- **Active edge**: Fill `sorry` in `riemannRoch` theorem
- **Discovery**: mathlib still lacks Serre duality, Euler characteristic, genus for schemes
- **Generator**: 8 candidates proposed - structure extensions with h1, Serre duality, Euler char
- **Integration**: All 8 candidates typecheck
- **Result**: `RRDataWithEuler.riemannRoch` has no `sorry` in Lean
  - Extended `RRData` → `RRDataWithCohomology` (adds h1, serreDuality field)
  - Extended further → `RRDataWithEuler` (adds eulerChar, eulerChar_def, eulerChar_formula)
  - Derivation chain: `serreDuality → ell_sub_h1_eq_deg → ell_sub_ell_K_sub_D → riemannRoch`
- **Remaining**: Base `RRData.riemannRoch` still has sorry

#### Assumption Accounting (Cycle 3)

| Prop field introduced | Classification | Notes |
|----------------------|----------------|-------|
| `serreDuality : ∀ D, ell (K - D) = h1 D` | **ASSUMPTION** | Serre duality is a deep theorem, not provable without real cohomology |
| `eulerChar_def : ∀ D, eulerChar D = ell D - h1 D` | Definition | Harmless definition of χ |
| `eulerChar_formula : ∀ D, eulerChar D = deg D + 1 - genus` | **ASSUMPTION (= RR!)** | This IS Riemann-Roch for Euler characteristic |

**Semantic issue**: `eulerChar_formula` is equivalent to the target theorem. Deriving RR from it is circular.
The "proof" is algebraically valid but mathematically vacuous—we assumed the answer.

**Status correction**: `RRDataWithEuler.riemannRoch` should be labeled **DERIVED_FROM_ASSUMPTIONS**, not "PROVED".

### Cycle 3.1 (Honesty Pivot)
- Renamed statuses: PROVED → DERIVED_FROM_ASSUMPTIONS
- Added Assumption Accounting to ledger
- Clarified that eulerChar_formula = RR in disguise
- New active edge: Build real divisor/cohomology foundations

### Cycle 4 (Foundation Building - Divisors) - COMPLETED
- **Active edge**: Define `Divisor α := α →₀ ℤ`, `deg`, prove additivity
- **Approach**: Use mathlib's `Finsupp` (finitely supported functions) as the basis

#### Results
| Definition/Lemma | Status | Notes |
|-----------------|--------|-------|
| `Divisor α := α →₀ ℤ` | ✅ DEFINED | `abbrev` for transparent unification |
| `deg : Divisor α → ℤ` | ✅ DEFINED | `D.sum (fun _ n => n)` |
| `single : α → ℤ → Divisor α` | ✅ DEFINED | Wraps `Finsupp.single` |
| `deg_add` | ✅ **PROVED** | Via `Finsupp.sum_add_index'` |
| `deg_zero` | ✅ **PROVED** | Via `Finsupp.sum_zero_index` |
| `deg_neg` | ✅ **PROVED** | Derived from `deg_add` + `omega` |
| `deg_sub` | ✅ **PROVED** | Derived from `deg_add` + `deg_neg` |
| `deg_single` | ✅ **PROVED** | Via `Finsupp.sum_single_index` |

#### Discovery (mathlib patterns used)
- `Finsupp.sum_add_index' h_zero h_add` - key lemma for additivity
- `Finsupp.sum_zero_index` - sum over empty support is zero
- `Finsupp.sum_single_index` - sum of single element
- `AddCommGroup` instance automatic from `Mathlib/Algebra/Group/Finsupp.lean`

#### Significance
**First real mathlib-grounded proofs** in this project. All 5 lemmas are derived from mathlib facts about Finsupp, not assumed as structure fields.

#### Next cycle
- See playbook for detailed Cycle 5 plan

### Cycle 5 - Function Field Interface - COMPLETED
- **Active edge**: Define L(D) = { f ∈ K | div(f) + D ≥ 0 } (Riemann-Roch space)
- **Approach**: Introduce FunctionFieldData structure with axiomatized div : K → Divisor α
- **Rationale**: Gives semantic meaning to ℓ(D) = dim L(D) instead of opaque field
- **Constraint**: NO schemes, NO sheaf cohomology (complexity cliff)

#### Results
| Definition/Lemma | Status | Notes |
|-----------------|--------|-------|
| `Divisor.Effective` | ✅ DEFINED | `0 ≤ D` using Finsupp's pointwise order |
| `Divisor.Effective_iff` | ✅ **PROVED** | `Effective D ↔ ∀ p, 0 ≤ D p` |
| `Divisor.Effective_zero` | ✅ **PROVED** | Via `le_refl` |
| `Divisor.Effective_add` | ✅ **PROVED** | Via pointwise omega |
| `Divisor.Effective_single` | ✅ **PROVED** | Case split on equality |
| `FunctionFieldData` | ✅ DEFINED | Structure with K, div, div_mul, div_one, div_inv, deg_div |
| `FunctionFieldData.div_zero` | ✅ **PROVED** | From div_mul 0 0, algebraic manipulation |
| `RRSpace` | ✅ DEFINED | L(D) = { f | f = 0 ∨ Effective (div f + D) } |
| `RRSpace.zero_mem` | ✅ **PROVED** | `Or.inl rfl` |
| `RRSpace.mono` | ✅ **PROVED** | D ≤ E → L(D) ⊆ L(E) via omega |

#### Discovery
- Finsupp already has `LE`, `Preorder`, `PartialOrder` instances in `Mathlib.Order.Preorder.Finsupp`
- Pointwise order: `D ≤ E ↔ ∀ p, D p ≤ E p`
- No need to define custom order - mathlib provides it

#### Significance
**First semantic definition of L(D)**. The Riemann-Roch space is now defined with real meaning:
- `f ∈ L(D)` iff poles of f are bounded by D
- `ℓ(D) = dim L(D)` can be defined (once L(D) shown to be a vector space)

#### Next cycle
- Cycle 6: Prove L(D) is a k-vector subspace (add_mem, smul_mem)
- This will enable `ℓ(D) = finrank k L(D)`

### Cycle 6 - L(D) is a k-Submodule - COMPLETED
- **Active edge**: Prove L(D) is a k-vector subspace
- **Key insight**: L(D) is a k-submodule (ground field), not K-submodule
- **Mathematical foundation**: Strong triangle inequality for valuations

#### Structure Changes
| Change | Description |
|--------|-------------|
| `FunctionFieldData α k` | Added ground field parameter `k : Type*` with `[Field k]` |
| `[Algebra k K]` | K is now a k-algebra |
| `div_add` | Strong triangle inequality: `div f ⊓ div g ≤ div (f + g)` |
| `div_algebraMap` | Constants have zero divisor: `∀ c : k, div (algebraMap k K c) = 0` |

#### Results
| Definition/Lemma | Status | Notes |
|-----------------|--------|-------|
| `RRSpaceCarrier` | ✅ DEFINED | Carrier set for L(D) |
| `RRSpace.zero_mem'` | ✅ **PROVED** | `Or.inl rfl` |
| `RRSpace.add_mem'` | ✅ **PROVED** | Uses `div_add` (strong triangle inequality) |
| `RRSpace.smul_mem'` | ✅ **PROVED** | Uses `div_mul` + `div_algebraMap` |
| `RRSpace : Submodule k data.K` | ✅ DEFINED | Full k-submodule structure |
| `RRSpace.mono` | ✅ **PROVED** | Monotonicity preserved |

#### Significance
**L(D) is now a proper k-vector space**, not just a set. This enables:
- `ℓ(D) = finrank k (RRSpace data D)` - semantic dimension
- Standard linear algebra tools from mathlib

#### Next cycle
- Cycle 7: Define `ℓ(D) = finrank k L(D)`, prove monotonicity
