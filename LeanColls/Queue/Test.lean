/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.Queue.BatchQueue
import LeanColls.Queue.LazyBatchQueue
import LeanColls.Queue.RealTimeQueue

open LeanColls

def test1 (iters : Nat) (α) [Q : Queue α Nat] : IO Unit := do
  let mut q := Q.empty

  for i in [:iters] do
    q := Q.enq q i
  
  for i in [:iters] do
    match Q.deq q with
    | none => IO.println "early empty!"
    | some (x,q') =>
      q := q'
      if x ≠ i then
        IO.println "wrong entry!"

def test2 (iters : Nat) (α) [Q : Queue α Nat] : IO Unit := do
  let q := Id.run do
    let mut q := Q.empty
    for i in [:iters] do
      q := Q.enq q i
    return q

  for i in [:iters] do
    match Q.deq q with
    | none => IO.println "early empty??"
    | some (x,_) =>
      if x ≠ 0 then
        IO.println "wrong entry??"

def test3 (reps iters len : Nat) (α) [Q : Queue α Nat] : IO Unit := do
  for _ in [:reps] do
    let (t_nodeq,()) ← time (
      for _ in [:iters] do
        let mut q := Q.empty
        for i in [:len] do
          q := Q.enq q i
    )
    let (t_deq,()) ← time (
      for _ in [:iters] do
        let mut q := Q.empty
        for i in [:len] do
          q := Q.enq q i
        match Q.deq q with
        | none => IO.println "early empty??"
        | some (x,_) =>
          if x ≠ 0 then
            IO.println "wrong entry??"
    )
    IO.println s!"{t_nodeq},{t_deq}"
  
  pure ()

def testAll : IO Unit := do
  IO.println "Ephemeral Test"
  let (bq, _) ← time (test1 1000000 (BatchQueue Nat))
  let (lbq,_) ← time (test1 1000000 (LazyBatchQueue Nat))
  let (rtq,_) ← time (test1 1000000 (RTQueue Nat))
  IO.println s!"BQ:  {bq}ms"
  IO.println s!"LBQ: {lbq}ms"
  IO.println s!"RTQ: {rtq}ms"
  IO.println "\nPersistent Test"
  let (bq ,_) ← time (test2 10000 (BatchQueue Nat))
  let (lbq,_) ← time (test2 10000 (LazyBatchQueue Nat))
  let (rtq,_) ← time (test2 10000 (RTQueue Nat))
  IO.println s!"BQ:  {bq}ms"
  IO.println s!"LBQ: {lbq}ms"
  IO.println s!"RTQ: {rtq}ms"
  IO.println "\nReal-Time Test"
  let bq  ← test3 100 10 1000000 (BatchQueue Nat)
  let lbq ← test3 100 10 1000000 (LazyBatchQueue Nat)
  let rtq ← test3 100 10 1000000 (RTQueue Nat)
  IO.println s!"BQ:  {bq}ms"
  IO.println s!"LBQ: {lbq}ms"
  IO.println s!"RTQ: {rtq}ms"
