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

/-
def pkgDir := __dir__
def cSrcDir := pkgDir / "bindings"
def cBuildDir := pkgDir / _package.buildDir / "bindings"

def ffiOTarget : FileTarget :=
  let oFile := cBuildDir / "leancolls_array.o"
  let srcTarget := inputFileTarget <| cSrcDir / "leancolls_array.c"
  fileTargetWithDep oFile srcTarget fun srcFile => do
    compileO oFile srcFile #["-I", (← getLeanIncludeDir).toString, "-fPIC"] "c++"

extern_lib cLib :=
  let libFile := cBuildDir / nameToStaticLib "leancolls_array"
  staticLibTarget libFile #[ffiOTarget]
-/

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "7da24c4024a2cb547d9d6e85943027daa77d850f"