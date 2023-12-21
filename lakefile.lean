import Lake
open System Lake DSL

package leancolls {
  precompileModules := true
}

@[default_target]
lean_lib LeanColls

@[default_target]
lean_exe test {
  root := `Main
}

target leancolls_array.o (pkg : NPackage _) : FilePath := do
  let oFile := pkg.buildDir / "c" / "leancolls_array.o"
  let srcJob ← inputFile <| pkg.dir / "bindings" / "leancolls_array.c"
  buildFileAfterDep oFile srcJob fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString, "-O3"]
    compileO "leancolls_array.c" oFile srcFile flags

extern_lib libleancolls_array (pkg : NPackage _) := do
  let name := nameToStaticLib "leancolls_array"
  let ffiO ← fetch <| pkg.target ``leancolls_array.o
  buildStaticLib (pkg.buildDir / "lib" / name) #[ffiO]

target leancolls_hole.o (pkg : NPackage _) : FilePath := do
  let oFile := pkg.buildDir / "c" / "leancolls_hole.o"
  let srcJob ← inputFile <| pkg.dir / "bindings" / "leancolls_hole.c"
  buildFileAfterDep oFile srcJob fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString, "-O3"]
    compileO "leancolls_hole.c" oFile srcFile flags

extern_lib libleancolls_hole (pkg : NPackage _) := do
  let name := nameToStaticLib "leancolls_hole"
  let ffiO ← fetch <| pkg.target ``leancolls_hole.o
  buildStaticLib (pkg.buildDir / "lib" / name) #[ffiO]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

meta if get_config? docs = some "on" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"