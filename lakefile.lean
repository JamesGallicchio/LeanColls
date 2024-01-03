import Lake
open System Lake DSL

package leancolls {
  precompileModules := true
}

@[default_target]
lean_lib LeanColls {
}

@[default_target]
lean_exe test {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
