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
  "https://github.com/leanprover-community/mathlib4" @ "master"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"