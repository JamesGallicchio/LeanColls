import Lake
open System Lake DSL

package leancolls

@[default_target]
lean_lib LeanColls

lean_exe test {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.11.0"

meta if get_config? doc = some "on" then
  require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "8a0bea3e0ae08f4973608e85f7a3bfd247ea1ac0"
