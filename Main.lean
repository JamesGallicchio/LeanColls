/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Array

open LeanColls

set_option compiler.extract_closed false

def main : IO Unit := do
  /- Some linear usage (all gucci!) -/
  let mut arr := COWArray.new 73 100
  for i in @Range.mk 100 do
    arr := arr.set i i.val
  let mut sum := 0
  for i in @Range.mk 100 do
    sum := sum + arr.get i
  IO.println sum /- 4950 -/
  /- Now we do a not-allowed mutation: -/
  let arrOld := arr
  arr := arr.set 0 20
  IO.println (arrOld.get 0)
  IO.println (arr.get 0)
