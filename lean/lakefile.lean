import Lake
open Lake DSL

package «type-theory-and-formal-proof» where
  -- add package configuration options here

lean_lib «TypeTheoryAndFormalProof» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "main"

@[default_target]
lean_exe «type-theory-and-formal-proof» where
  root := `Main
