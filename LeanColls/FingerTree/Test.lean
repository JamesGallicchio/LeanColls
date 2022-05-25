/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.AuxLemmas
import LeanColls.Classes
import LeanColls.FingerTree.FingerTree
import LeanColls.FingerTree.RadixBalancedFT
import LeanColls.TestHelpers

open LeanColls

def ephReps := 500000
def persReps := 50000
def altReps := 500000

def testColl (α) [Enumerable α Nat] [Iterable α Nat] : IO (Nat × Nat × Nat) := do
  let (tEph,_) ← time (do
    let mut q := Enumerable.insert none
    for i in [:ephReps] do
      q := Enumerable.insert (some (i, q))
    let mut q' : Iterable.ρ α Nat := Iterable.toIterator <| Enumerable.fromEnumerator q
    for i in [:ephReps] do
      match Iterable.step q' with
      | none => IO.print "Early empty"
      | some (x,q'') =>
        if x = ephReps - 1 - i then
          q' := q''
        else
          IO.print "Wrong number"
  )
  let (tPers,_) ← time (do
    let mut q := Enumerable.insert none
    for i in [:persReps] do
      q := Enumerable.insert (some (i,q))
    let mut q' : Iterable.ρ α Nat := Iterable.toIterator <| Enumerable.fromEnumerator q
    for i in [:persReps] do
      match Iterable.step q' with
      | none => IO.print "jinkies"
      | some (x,q'') =>
        if x = persReps - 1 - i then
          q' := q''
        else
          IO.print "jeepers"
  )
  let (tAlt,_) ← time (do
    for i in [:persReps] do
      let q := Enumerable.insert (some (i,Enumerable.insert none))
      let q' : Iterable.ρ α Nat := Iterable.toIterator <| Enumerable.fromEnumerator q
      match Iterable.step q' with
      | none => IO.print "wh!"
      | some (x,q'') =>
        if x ≠ i then
          IO.print "whaa!"
  )
  return (tEph, tPers, tAlt)

def testAll : IO Unit :=
  open LeanColls in do
  let toStrLine := λ (eph, pers, alt) => [toString eph, toString pers, toString alt]
  IO.println <| formatTable
    ["Name", "Ephemeral", "Persistent", "Alternate"] [
      "FingerTree" :: toStrLine (← testColl (FingerTree Nat 0)),
      --"Array" :: toStrLine (← testColl (Array Nat)),
      "RBFT" :: toStrLine (← testColl (RadixBalancedFT Nat))
    ]
    (by sorry)
