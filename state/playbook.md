# Playbook (Curator maintained)

- Prefer line-bundle / invertible-sheaf RR statements; divisor RR is a wrapper.
- Use `finrank k` for dimensions; avoid `Nat`-based dims until the end.
- Keep lemma statements small: fewer binders, fewer coercions, fewer implicit arguments.
- When stuck on coercions, introduce explicit `let` bindings for objects (e.g. `L : LineBundle X`).
- RESOLVED (Cycle 2): Defined `RRData` structure bundling Div, deg, ell, genus, K. RR statement now elaborates.
- CAVEAT: RRData abstracts H^0, H^1, canonical divisor into opaque fields. Must later instantiate with real mathlib objects.
- Next: Add Serre duality as a Prop field (NOT axiom), then prove riemannRoch from structure fields.
