/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls
import LeanColls.Array.Test

open LeanColls

set_option compiler.extract_closed false

def main : IO Unit := benchmarkArrayBuffer
