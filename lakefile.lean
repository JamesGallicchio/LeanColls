import Lake
open System Lake DSL

package leancolls

@[default_target]
lean_lib LeanColls

lean_exe test {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.8.0"

meta if get_config? doc = some "on" then
  require «doc-gen4» from git "https://github.com/leanprover/doc-gen4"
    @ "cf138201a0a4fa8ca78b6e2a42a0a4860369d10e"

