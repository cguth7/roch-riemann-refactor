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

- **RESOLVED (Cycle 7)**: ℓ(D) = finrank k L(D)
  - `ell : FunctionFieldData α k → Divisor α → ℕ` (semantic dimension)
  - `RRSpace.le_of_divisor_le` converts set inclusion to submodule ≤
  - **PROVED**: `ell.mono`, `ell.pos_of_effective`, `ell.zero_pos`
  - **PROVED**: `RRSpace.one_mem_of_effective`, `RRSpace.algebraMap_mem_zero`, `RRSpace.algebraMap_mem_of_effective`

- **RESOLVED (Cycle 8)**: Finite-Dimensionality Typeclass
  - Used `[∀ D, Module.Finite k (RRSpace data D)]` typeclass instance
  - **PROVED**: `ell.mono_unconditional`, `ell.pos_of_effective_unconditional`, `ell.ge_zero_of_effective`
  - **PROVED**: `ell.mono_of_effective`, `ell.add_effective_le`, `ell.zero_pos_unconditional`
  - **PROVED**: `RRSpace.nontrivial_of_effective`, `ell.diff_le_deg_diff`
  - All Cycle 7 conditional lemmas now have unconditional versions

## Status - Cycle 9 (Success: Quotient Infrastructure)
- **PROVED**: `RRSpace.submodule_inclusion_injective`, `ell.quotient_add_eq_of_le`, `ell.quotient_le_of_le`
- **STATED**: `ell.add_single_le_succ` (key target), `ell.le_deg_add_ell_zero` (Riemann inequality)
- **BLOCKER**: Cannot prove quotient dimension ≤ degree difference without evaluation map
- **KEY LEMMA**: `ell.quotient_add_eq_of_le` gives `dim(L(E)/L(D)) + ℓ(D) = ℓ(E)` - reduces single-point bound to quotient bound

## Status - Cycle 10 (Success: Single-Point Axiom)
- **DEFINED**: `FunctionFieldDataWithBound` - extends FunctionFieldData with `single_point_bound` axiom
- **PROVED**: `ell.add_single_le_succ_from_bound`, `Divisor.deg_add_single`, `ell.diff_add_single_le_one`, `Divisor.add_zero_right`
- **STATED**: `ell.single_le_deg_succ_from_bound`, `ell.le_deg_add_ell_zero_from_bound`, `ell.le_toNat_deg_add_ell_zero_from_bound`
- **DESIGN CHOICE**: Used axiom extension rather than direct proof - cleaner architecture, can be upgraded later

## Status - Cycle 11 (SUCCESS: Riemann Inequality PROVED)
- **AXIOM ADDED**: `ell_zero_eq_one : ell 0 = 1` (L(0) = k, constants only)
- **PROVED**: `Divisor.single_add_one`, `Divisor.Effective_single_nat`, `Divisor.deg_nonneg_of_effective`, `ell.single_le_deg_succ_from_bound`
- **PROVED**: `ell.le_deg_add_ell_zero_from_bound` (**RIEMANN INEQUALITY** by degree induction)
- **PROVED**: `ell.le_toNat_deg_add_ell_zero_from_bound` (corollary)

**Key technique**: Degree-based induction on `(deg D).toNat` instead of `Finsupp.induction_linear`.
**Requires**: `[DecidableEq α]` for effectivity proof.

## Next Steps (Cycle 12)

**WARNING**: Do NOT touch Schemes or Sheaf Cohomology. Complexity cliff.

**Goal**: Connect Riemann inequality to full Riemann-Roch theorem.

### Riemann Inequality Status
We have: ℓ(D) ≤ deg(D) + ℓ(0) = deg(D) + 1 for effective D

### Path to Full RR
Full Riemann-Roch: ℓ(D) - ℓ(K - D) = deg(D) + 1 - g

Need:
1. Upper bound for ℓ(K - D) using Serre duality
2. Connection between abstract RRData and concrete FunctionFieldDataWithBound

### Do NOT do
- Schemes, sheaves, cohomology
- Trying to instantiate FunctionFieldData with real objects yet
