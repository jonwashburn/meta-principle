import Lake
open Lake DSL

package «IndisputableChain» where
  -- The indisputable logical chain for Recognition Science

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «IndisputableChain» where
  -- add library configuration options here
