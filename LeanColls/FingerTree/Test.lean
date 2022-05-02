/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.AuxLemmas
import LeanColls.FingerTree.FingerTree

def ephReps := 5000000
def persReps := 10000

def testFT : IO (Nat × Nat) := do
  let (tEph,_) ← time (do
    let mut q : FingerTree Nat 0 := FingerTree.Empty
    for i in [:ephReps] do
      q := q.snoc i
    for i in [:ephReps] do
      match q.back? with
      | none => IO.print "Early empty"
      | some (q',(x : Nat)) =>
        if x = ephReps - 1 - i then
          q := q'
        else
          IO.print "Wrong number"
  )
  let (tPers,_) ← time (do
    let mut q : FingerTree Nat 0 := FingerTree.Empty
    for i in [:persReps] do
      q := FingerTree.snoc q i
    for i in [:persReps] do
      let q1 := q.back?
      match q1 with
      | none => IO.print "jinkies"
      | some (q',(x:Nat)) =>
        if x = persReps - 1 - i then
          q := q'
        else
          IO.print "jeepers"
  )
  return (tEph, tPers)

def testArr : IO (Nat × Nat) := do
  let (tEph,_) ← time (do
    let mut q : Array Nat := Array.empty
    for i in [:ephReps] do
      q := q.push i
    for i in [:ephReps] do
      match q.back? with
      | none => IO.print "Early empty"
      | some (x : Nat) =>
        if x = ephReps - 1 - i then
          q := q.pop
        else
          IO.print s!"Got {x} instead of {ephReps-1-i}"
          break
  )
  let (tPers,_) ← time (do
    let mut q : Array Nat := Array.empty
    for i in [:persReps] do
      q := q.push i
    for i in [:persReps] do
      let q1 := q.pop
      match q.back? with
      | none => IO.print "jinkies"
      | some (x:Nat) =>
        if x = persReps - 1 - i then
          q := q1
        else
          IO.print "jeepers"
  )
  return (tEph, tPers)

def testAll : IO Unit := do
  let (ftEph, ftPers) ← testFT
  let (arrEph, arrPers) ← testArr
  IO.print s!"           | Ephemeral\t| Persistent\n"
  IO.print s!"FingerTree | {ftEph}\t| {ftPers}\n"
  IO.print s!"Array      | {arrEph}\t| {arrPers}\n"
