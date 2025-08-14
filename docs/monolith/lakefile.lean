import Lake
open Lake DSL

package «IndisputableMonolith» where
  -- standalone monolith build

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "stable"

@[default_target]
lean_lib «IndisputableMonolith» where
  srcDir := "src"
