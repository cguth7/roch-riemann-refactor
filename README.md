# Riemann-Roch for P¹ in Lean 4

A "vibe-coded" formalization of a restricted Riemann-Roch theorem for the projective line over finite fields.

## What's Proved

```lean
theorem ell_ratfunc_projective_eq_deg_plus_one (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    ell_ratfunc_projective D = D.deg.toNat + 1
```

For effective divisors D supported only at **linear places** (degree-1 primes of the form X - α for α ∈ Fq), dim L(D) = deg(D) + 1.

## Limitations

**This is NOT full P¹ Riemann-Roch.** The `IsLinearPlaceSupport` hypothesis restricts to divisors supported at Fq-rational points only:

```lean
def IsLinearPlaceSupport (D : DivisorV2 (Polynomial Fq)) : Prop :=
  ∀ v ∈ D.support, ∃ α : Fq, v = linearPlace α
```

Not covered:
- Places of degree > 1 (e.g., over F₂, the place (X² + X + 1) is not handled)
- Divisors mixing linear and non-linear places

Full P¹ RR is mathematically trivial anyway - L(n·[0]) is spanned by {1, 1/X, ..., 1/Xⁿ}. The "vibe coding" methodology is probably more interesting than the result.

## How It Was Built

~241 cycles of Claude Code with some Gemini assistance. The human operator has no algebraic geometry background - navigation was done by reading AI "thinking traces" for emotional texture (hedging, frustration, circling) rather than mathematical content.

## Build

```bash
lake update && lake build
```

Verify sorry-free:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
# No output = complete proof
```

## File Structure

```
RrLean/RiemannRochV2/
├── Divisor.lean                 # Divisor definitions
├── RRSpace.lean                 # Riemann-Roch spaces L(D)
├── Infrastructure.lean          # Valuation rings, residue fields
├── KernelProof.lean             # ker(eval) = L(D)
├── DimensionCounting.lean       # Gap bounds
├── RiemannInequality.lean       # Riemann inequality
│
└── SerreDuality/
    ├── DimensionCore.lean       # Core finiteness lemmas
    ├── DimensionScratch.lean    # Main theorem
    ├── RatFuncPairing.lean      # RatFunc-specific machinery
    └── Smoke.lean               # Build verification
```

## Sorries

**0 sorries in main codebase.** 6 dead-code lemmas moved to `RrLean/Archive/SorriedLemmas.lean`.

## License

MIT
