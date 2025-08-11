import Lake
open Lake DSL

package «RS» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «RS» where
  -- add library configuration options here
