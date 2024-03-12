import Lake
open Lake DSL

package leancolls

@[default_target]
lean_lib LeanColls

lean_exe test {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

meta if get_config? doc = some "on" then
  require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
