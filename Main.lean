/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Array

open LeanColls

def main : IO Unit := do
  let mut arr := Array.new 73 100
  for i in Range.mk 100 do
    arr := arr.set i i.val
  let mut sum := 0
  for i in Range.mk 100 do
    sum := sum + arr.get i
  IO.println sum
  let arrOld := arr
  arr := arr.set 0 20
  IO.println (arrOld.get 0)
  IO.println (arr.get 0)
