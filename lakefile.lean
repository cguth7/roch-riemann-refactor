import Lake
open Lake DSL

package rrLean where
  moreServerArgs := #["-K", "102400"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib RrLean where
  globs := #[.submodules `RrLean]
