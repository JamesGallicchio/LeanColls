import Lake
open System Lake DSL

package leancolls

@[default_target]
lean_lib LeanColls

lean_exe test {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.13.0"
