# ChatGPT Context System

Purpose: keep sessions grounded in the live codebase with minimal overhead.

## Minimal Set (use these every cycle)
- CURRENT_STATUS.md (verified counts + snapshot)
- TASKS.md (one active edge + next steps)
- SESSION_LOG.md (short append-only record)

## Optional (use only if needed)
- BLOCKERS.md (hard problems with sketch)
- DRIFT_LOG.md (doc/code mismatches)
- DECISIONS.md (architectural choices)
- COMMANDS.md (canonical checks)
- CONTEXT_PACK.md (new session bootstrap)

## Update Routine (Per Cycle)
1) Set the Active Edge in TASKS.md.
2) Run verification commands (COMMANDS.md) if claims are made.
3) Update CURRENT_STATUS.md with verified counts + date.
4) Append a short entry to SESSION_LOG.md.
5) If docs and code disagree, add DRIFT_LOG.md entry.

## Ground Rules
- Prefer code over docs when they conflict.
- Keep context small; avoid bulk file reads.
- Avoid refactors unless they remove a blocker.
