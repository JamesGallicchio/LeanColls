import Lake
open System Lake DSL

def cDir : FilePath := "bindings"

def cSrc := cDir / "leancolls_array.c"

def buildDir := defaultBuildDir

def oTarget (pkgDir : FilePath) : FileTarget :=
  let oFile := pkgDir / buildDir / cDir / "leancolls_array.o"
  let srcTarget := inputFileTarget <| pkgDir / cSrc
  fileTargetWithDep oFile srcTarget fun srcFile => do
    compileO oFile srcFile #["-I", (← getLeanIncludeDir).toString]

def cLibTarget (pkgDir : FilePath) : FileTarget :=
  let libFile := pkgDir / buildDir / cDir / "leancolls_array.a"
  staticLibTarget libFile #[oTarget pkgDir]

package lean_colls (pkgDir) {
  moreLibTargets := #[cLibTarget pkgDir]
--  defaultFacet := PackageFacet.sharedLib
--  moreServerArgs := #["--load-dynlib=build/lib/LeanColls.so"]
}