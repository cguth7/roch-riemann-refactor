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

### Cycle 4 (Foundation Building - Divisors)
- **Active edge**: Define `Divisor α := α →₀ ℤ`, `deg`, prove additivity, refactor RRData
- **Approach**: Use mathlib's `Finsupp` (finitely supported functions) as the basis
- **Goal**: Replace abstract `Div : Type*` with concrete `Divisor α` grounded in mathlib
