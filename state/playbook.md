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
  - `eulerChar_formula` field IS Riemann-Roch; derivation is circular.
  - This is an axiomatized theory interface, not a proof of RR.

## Blockers (fundamental)
- mathlib lacks: divisors, line bundles, sheaf cohomology H⁰/H¹, genus, degree for schemes
- Cannot instantiate abstract structures with real mathlib objects
- No path to actual RR proof without building foundations

## Next Steps (Cycle 4)
- **Foundation building**: Define real Divisor type
- `Divisor α := α →₀ ℤ` (Finsupp - finitely supported functions from points to ℤ)
- `deg D := D.sum (fun _ n => n)` (sum of coefficients)
- Prove `deg_add : deg (D + E) = deg D + deg E` (should follow from Finsupp.sum_add)
- Subtraction `K - D` comes free from AddCommGroup instance on Finsupp
- Refactor `RRData.Div` to use `Divisor α` instead of abstract `Type*`
