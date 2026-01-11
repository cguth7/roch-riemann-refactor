# Context Pack (paste into a new ChatGPT session)

Project: Lean 4 formalization of Riemann-Roch for curves over algebraically closed fields.
Goal: Prove full RR using only propext, Classical.choice, Quot.sound.
Repo: roch-riemann-refactor.

Rules:
- Do NOT edit files unless explicitly asked.
- Trust code over docs if they conflict.
- Verify axioms/sorries with rg before claiming progress.
- Keep responses short, tie plans to files/lemmas.

Primary references:
- state/ledger.md
- state/PROOF_CHAIN.md
- state/REFACTOR_PLAN.md
- state/chatgpt/CURRENT_STATUS.md
- state/chatgpt/TASKS.md (Active Edge)

Verification commands:
- rg -n "^axiom\\s" RrLean/RiemannRochV2 --glob "*.lean"
- rg -n "(:=\\s*sorry|by\\s+sorry|\\bsorry\\b$)" RrLean/RiemannRochV2 --glob "*.lean"
