import Lake
open Lake DSL

package rrLean where
  -- Give Lean a bit more breathing room; safe default
  moreServerArgs := #["-K", "102400"]

-- mathlib dependency
-- NOTE: the exact commit will be resolved into lake-manifest.json
-- and should be COMMITTED.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib RrLean where
  -- Disable unused section variable linter (too noisy for this codebase)
  moreLeanArgs := #["-Dlinter.unusedSectionVars=false"]
