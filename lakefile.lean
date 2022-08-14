import Lake
open System Lake DSL

package leancolls {
  precompileModules := false
}

@[defaultTarget]
lean_lib LeanColls {
  srcDir := __dir__
  roots := #[`LeanColls]
}

@[defaultTarget]
lean_exe test {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
    @ "a4f624b2fc85f02897a51d3149469a19975867d2"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4"
    @ "422e6bec91bee589f667b8f2e83d149b419ac431"