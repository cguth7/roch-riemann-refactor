# Playbook (Curator maintained)

## Heuristics
- Prefer line-bundle / invertible-sheaf RR statements; divisor RR is a wrapper.
- Use `finrank k` for dimensions; avoid `Nat`-based dims until the end.
- Keep lemma statements small: fewer binders, fewer coercions, fewer implicit arguments.
- When stuck on coercions, introduce explicit `let` bindings for objects (e.g. `L : LineBundle X`).

## Status
- RESOLVED (Cycle 2): Defined `RRData` structure bundling Div, deg, ell, genus, K. RR statement elaborates.
- RESOLVED (Cycle 3): Extended to `RRDataWithCohomology` and `RRDataWithEuler`.
- **DERIVED** (not proved): `RRDataWithEuler.riemannRoch` is derived from assumed structure fields.
- **RESOLVED (Cycle 4)**: Foundation building - Divisor type and degree
  - `Divisor α := α →₀ ℤ` (abbrev for transparent unification)
  - `deg : Divisor α → ℤ` (sum of coefficients)
  - **PROVED**: `deg_add`, `deg_zero`, `deg_neg`, `deg_sub`, `deg_single`
- **RESOLVED (Cycle 5)**: Function Field Interface
  - `Effective : Divisor α → Prop` (uses mathlib's Finsupp order)
  - **PROVED**: `Effective_iff`, `Effective_zero`, `Effective_add`, `Effective_single`
  - `FunctionFieldData α` structure (K, div, div_mul, div_one, div_inv, deg_div)
  - **PROVED**: `FunctionFieldData.div_zero`
- **RESOLVED (Cycle 6)**: L(D) is a k-Submodule
  - Extended `FunctionFieldData α k` with ground field k, `Algebra k K`, `div_add`, `div_algebraMap`
  - `RRSpace data D : Submodule k data.K` (Riemann-Roch space as proper k-submodule)
  - **PROVED**: `RRSpace.zero_mem'`, `RRSpace.add_mem'`, `RRSpace.smul_mem'`, `RRSpace.mono`

## Blockers (fundamental)
- mathlib lacks: line bundles, sheaf cohomology H⁰/H¹, genus for schemes
- Cannot yet instantiate `RRData.Div` with real `Divisor α` (needs point type from curve)
- `RRData.deg` is abstract; not yet connected to `Divisor.deg`
- `RRData.ell` is abstract; not yet connected to `finrank k (RRSpace data D)`

## Next Steps (Cycle 7) - Connect ℓ(D) to finrank

**WARNING**: Do NOT touch Schemes or Sheaf Cohomology. Complexity cliff.

**Goal**: Define `ℓ(D) = finrank k (RRSpace data D)` and prove basic properties.

### Deliverables (in order)
1. **Define ℓ(D)**:
   - `def ell (data : FunctionFieldData α k) (D : Divisor α) := finrank k (RRSpace data D)`
   - May need to import `Mathlib.LinearAlgebra.Dimension.Finrank`

2. **Prove ℓ monotonicity**:
   - `ell_mono : D ≤ E → ℓ(D) ≤ ℓ(E)` (larger divisor = more functions = larger dimension)

3. **Finite-dimensionality assumption**:
   - May need to add `[FiniteDimensional k (RRSpace data D)]` hypothesis
   - Or add as field to FunctionFieldData

4. **Connect ℓ to RRData.ell** (stretch goal):
   - Show how abstract `RRData.ell` can be instantiated with `finrank k (RRSpace data D)`

### Why this matters
| Old (RRData) | New (FunctionFieldData) |
|---|---|
| `ell : Div → ℕ` (opaque) | `finrank k L(D)` (semantic) |

### Do NOT do
- Schemes, sheaves, cohomology
- Trying to instantiate FunctionFieldData with real objects yet
