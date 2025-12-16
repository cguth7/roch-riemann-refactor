# Playbook (Curator maintained)

- Prefer line-bundle / invertible-sheaf RR statements; divisor RR is a wrapper.
- Use `finrank k` for dimensions; avoid `Nat`-based dims until the end.
- Keep lemma statements small: fewer binders, fewer coercions, fewer implicit arguments.
- When stuck on coercions, introduce explicit `let` bindings for objects (e.g. `L : LineBundle X`).
- RESOLVED (Cycle 2): Defined `RRData` structure bundling Div, deg, ell, genus, K. RR statement now elaborates.
- RESOLVED (Cycle 3): Extended to `RRDataWithCohomology` (h1, Serre duality) and `RRDataWithEuler` (Euler characteristic).
- **PROVED**: `RRDataWithEuler.riemannRoch` is fully proved via Serre duality + Euler characteristic.
- CAVEAT: Base `RRData.riemannRoch` still has sorry. Need to show `RRData → RRDataWithEuler` extension exists.
- Next: Either (1) prove extension lemma, or (2) accept `RRDataWithEuler` as the primary formulation.
