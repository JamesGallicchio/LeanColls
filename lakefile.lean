import Lake
open System Lake DSL

package leancolls {
  precompileModules := true
}

@[defaultTarget]
lean_lib LeanColls

@[defaultTarget]
lean_exe test {
  root := `Main
}

target leancolls_array.o (pkg : Package) : FilePath := do
  let oFile := pkg.buildDir / "c" / "leancolls_array.o"
  let srcJob ← inputFile <| pkg.dir / "bindings" / "leancolls_array.c"
  buildFileAfterDep oFile srcJob fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString]
    compileO "leancolls_array.c" oFile srcFile flags

extern_lib libleancolls_array (pkg : Package) := do
  let name := nameToStaticLib "leancolls_array"
  let ffiO ← fetch <| pkg.target ``leancolls_array.o
  buildStaticLib (pkg.buildDir / "lib" / name) #[ffiO]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"