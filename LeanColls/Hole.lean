/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.AuxLemmas

namespace LeanColls

@[extern "leancolls_hole_initialize"]
private opaque holeInit : IO Unit

builtin_initialize holeInit

opaque Hole.Pointed (α : Type u) (β : Type v) : NonemptyType.{max u v}
def Hole (α β) := (Hole.Pointed α β).type

namespace Hole

instance : Nonempty (Hole α β) := (Hole.Pointed α β).property

@[extern "leancolls_hole_mk"]
opaque hole : Unit → Hole α α

@[extern "leancolls_hole_fill"]
axiom fill {α β} : Hole α β → α → β

@[extern "leancolls_hole_cons"]
opaque cons : Hole (List α) (List α) → α → Hole (List α) (List α)

-- Benchmarks

set_option trace.compiler.ir.result true in
private def append (L1 L2 : List α) : List α :=
  let rec revAppend (L1 L2 : List α) :=
    match L1 with
    | [] => L2
    | (x::xs) => revAppend xs (x::L2)
  revAppend (revAppend L1 []) L2

set_option trace.compiler.ir.result true in
set_option compiler.extract_closed false in
private def append' (L1 L2 : List α) : List α :=
  let rec holeAppend (L1 L2 : List α) (h : Hole (List α) (List α)) :=
    match L1 with
    | [] => h.fill L2
    | (x::xs) => holeAppend xs L2 (h.cons x)
  holeAppend L1 L2 (Hole.hole ())

def benchmarkAppend : IO Unit := do
  let iters := 100
  let size := 100000

  let L := List.range size

  let (timeNormal, _) ← time (do
    for _ in [0:iters] do
      let L' := append L []
      if L'.head? ≠ some 0 then
        IO.println "oh no"
        return
  )
  let (timeHole, _) ← time (
    for _ in [0:iters] do
      let L' := append' L []
      if L'.head? ≠ some 0 then
        IO.println "oh no"
        return
  )
  IO.println s!"{size}, {timeNormal}, {timeHole}"

