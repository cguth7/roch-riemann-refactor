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

## Next Steps
- **Option 3 selected**: Build divisor/cohomology foundations in Lean
- This is a major undertaking (months of work, thousands of lines)
- Start with simplest component: Weil divisors on a curve?
