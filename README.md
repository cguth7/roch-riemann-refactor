# Riemann-Roch Formalization

A Lean 4 formalization of the Riemann-Roch theorem for algebraic curves over finite fields, built on Dedekind domain and adelic foundations.

**Ultimate Goal**: Full Riemann-Roch with **zero axioms, zero sorries**.

**Live Documentation:** [cguth7.github.io/roch-riemann](https://cguth7.github.io/roch-riemann/)

## Current Status

| Metric | Value |
|--------|-------|
| Cycles | 134 |
| Lines of Lean | ~7,200 |
| Modules | 22 |
| Sorries in main inequality proof | **0** |
| Sorries remaining (full RR) | 1 |

### What's Proven

**Riemann Inequality** (sorry-free):
```lean
-- Affine version (fully unconditional)
lemma riemann_inequality_affine [bd : BaseDim R K] {D : DivisorV2 R} (hD : D.Effective) :
    (ellV2_real R K D : ℤ) ≤ D.deg + bd.basedim

-- Projective version
lemma riemann_inequality_real [SinglePointBound R K] {D : DivisorV2 R} (hD : D.Effective) :
    (ellV2_real R K D : ℤ) ≤ D.deg + 1
```

**Adelic Foundations** (Cycles 118-134):
- K is discrete in full adeles
- K is closed in full adeles
- Integral adeles are compact

### What Remains

| Task | Status |
|------|--------|
| Weak approximation | 1 sorry |
| Canonical divisor via Different ideal | Not started |
| Serre duality | Not started |
| Discharge finite residue field axioms | In progress |

## Proof Architecture

Two parallel tracks:

**Track A - Riemann Inequality** (COMPLETE):
```
Divisor → RRSpace → KernelProof → DimensionCounting → RiemannInequality
```
Uses degree induction with gap bound from exact sequence `0 → L(D) → L(D+v) → κ(v)`.

**Track B - Full Riemann-Roch** (IN PROGRESS):
```
Adeles → FullAdeles → Compactness → Serre Duality → Full RR
```
Uses adelic methods: K discrete/cocompact in adeles implies finite cohomology.

### Module Structure

```
RrLean/RiemannRochV2/
├── Core Proof Chain (sorry-free)
│   ├── Divisor.lean              # DivisorV2, degree, Effective
│   ├── RRSpace.lean              # L(D), l(D) definitions
│   ├── Typeclasses.lean          # LocalGapBound, SinglePointBound
│   ├── Infrastructure.lean       # Valuation rings, residue fields
│   ├── RRDefinitions.lean        # Evaluation map
│   ├── KernelProof.lean          # ker(eval) = L(D)
│   ├── DimensionCounting.lean    # Gap ≤ 1 via Module.length
│   └── RiemannInequality.lean    # Main theorems
│
├── Adelic Infrastructure
│   ├── AdelicTopology.lean       # Topology + axiom classes
│   ├── FullAdeles.lean           # Full adeles (finite + infinity)
│   ├── AllIntegersCompactProof.lean  # Compactness proofs
│   └── FqPolynomialInstance.lean # Concrete Fq[X] instance
│
└── Full RR Track
    ├── FullRRData.lean           # Canonical divisor, Serre duality axioms
    ├── TraceDualityProof.lean    # Toward Serre duality
    └── DifferentIdealBridge.lean # Canonical → Different ideal
```

## How This Was Built

This project was developed over 134 cycles in ~2 days using a novel AI-assisted approach.

### The Method

Multiple Claude instances running in parallel, orchestrated by a human who:
- **Doesn't know the mathematics** — zero algebraic geometry background
- **Reads thinking traces for "emotion"** — detecting when reasoning goes off-track by patterns (hedging, circling, frustration) rather than content
- **Cross-pollinates between AI systems** — feeding insights between Claude, Gemini, ChatGPT
- **Triggers pivots via deep research** — escalating to research mode when truly stuck
- **Maintains coherence via ledger** — `state/ledger.md` acts as shared memory across instances

### Why It Works

The human acts as a **coherence detector**, not a **correctness verifier**. Key insight: you can navigate complex technical work by reading the *texture* of AI reasoning without understanding the content.

The ledger system (`state/ledger.md`) provides:
- Context for each new Claude instance
- Sorry/axiom tracking
- Architecture documentation
- "Start here" instructions for the next cycle

### Key Pivots

| Cycle | Discovery |
|-------|-----------|
| 17 | Pivot from axiom-based to constructive Dedekind foundations |
| 52 | `mapEquiv` discovery — bypassed 20 cycles of stuck work |
| 73 | `LocalGapBound` instance complete — core inequality proven |
| 121 | K not discrete in *finite* adeles — need full adeles |
| 134 | `nonempty_rankOne_iff_mulArchimedean` — avoids ℝ≥0 literal issues |

## Setup & Build

```bash
git clone https://github.com/cguth7/roch-riemann.git
cd roch-riemann
lake update
lake build
```

## Development History

- **Cycles 1-16**: Axiom-based approach, derived 70+ lemmas
- **Cycle 17**: Pivot to constructive Dedekind foundations
- **Cycles 17-73**: Riemann inequality proven (sorry-free)
- **Cycles 74-117**: Infrastructure for full RR
- **Cycles 118-134**: Full adeles, discreteness, compactness

See `state/ledger.md` for detailed cycle-by-cycle progress.

## License

MIT
