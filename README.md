# Riemann-Roch Formalization

Lean 4 formalization of the Riemann-Roch theorem using ACE-style orchestration.

## Setup

```bash
lake update
lake build
```

## Run single file

```bash
lake env lean RrLean/RR.lean
```

## Cycle commit

```bash
./scripts/commit_cycle.sh "short summary"
```
