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
  - `RRSpace data D : Set data.K` (Riemann-Roch space L(D))
  - **PROVED**: `RRSpace.zero_mem`, `RRSpace.mono`

## Blockers (fundamental)
- mathlib lacks: line bundles, sheaf cohomology H⁰/H¹, genus for schemes
- Cannot yet instantiate `RRData.Div` with real `Divisor α` (needs point type from curve)
- `RRData.deg` is abstract; not yet connected to `Divisor.deg`
- `RRData.ell` is abstract; not yet connected to `dim RRSpace`

## Next Steps (Cycle 6) - Vector Space Structure for L(D)

**WARNING**: Do NOT touch Schemes or Sheaf Cohomology. Complexity cliff.

**Goal**: Prove L(D) is a K-vector subspace, enabling `ℓ(D) = finrank K L(D)`.

### Deliverables (in order)
1. **L(D) is a subgroup**:
   - `RRSpace.add_mem : f ∈ L(D) → g ∈ L(D) → f + g ∈ L(D)`
   - `RRSpace.neg_mem : f ∈ L(D) → -f ∈ L(D)`

2. **L(D) is closed under scalar multiplication**:
   - `RRSpace.smul_mem : c ∈ K → f ∈ L(D) → c • f ∈ L(D)`
   - Requires: `div (c * f) = div c + div f = div f` (for c ≠ 0, div c = 0 since c is constant)

3. **Subspace instance**:
   - `instance : Submodule K (data.K)` or similar structure

4. **Connect to dimension**:
   - Define `ell (data : FunctionFieldData α) (D : Divisor α) := finrank data.K (RRSpace data D)`
   - This requires L(D) to be finite-dimensional (may need to assume)

### Why this matters
| Old (RRData) | New (FunctionFieldData) |
|---|---|
| `ell : Div → ℕ` (opaque) | `finrank K L(D)` (semantic) |

### Do NOT do
- Schemes, sheaves, cohomology
- Trying to instantiate FunctionFieldData with real objects yet
- Connecting to RRData (that's Cycle 7+)
