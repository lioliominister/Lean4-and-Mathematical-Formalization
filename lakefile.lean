import Lake
open Lake DSL

package "proof"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Proof» where
  srcDir := "."
