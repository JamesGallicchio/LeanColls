/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

-- Utility collection library I wrote (not distributed by default)
import LeanColls

open LeanColls

set_option compiler.extract_closed false

-- **************************
-- *   Generic CNF stuff    *
-- **************************

@[reducible]
def Atom := String
deriving Inhabited, DecidableEq, Hashable, Repr

structure Literal where
  neg : Bool
  atom : Atom
deriving Inhabited, DecidableEq, Hashable, Repr

namespace Literal

nonrec def not : Literal → Literal
| ⟨neg,name⟩ => ⟨not neg, name⟩

instance : ToString Literal where
  toString := λ ⟨neg, num⟩ =>
    if neg then "¬" ++ num else num

end Literal

structure Clause where
  lits : List Literal
  original : List Literal := lits -- represents "original" clause before simplifications
deriving Inhabited, DecidableEq, Repr

instance : ToString Clause where
  toString := λ L => "(" ++ FoldableOps.toString L.lits (sep := " ∨ ") ++ ")"

structure Formula where
  clauses : VarArray Clause
deriving Inhabited

instance : ToString Formula where
  toString := λ L => FoldableOps.toString L.clauses (sep := " ∧ ")

def Formula.buildAtomMap : Formula → Nat × HashMap Atom Nat × HashMap Nat Atom
| ⟨clauses⟩ =>
  let (nameMap, lastVar, _) := Foldable.fold clauses (fun acc c =>
    c.lits.foldl (fun (map,last,count) ⟨_,atom⟩ =>
      -- if `atom` is in map, do nothing, else assign `atom` to next
      match map.get? atom with
      | some _  => (map,last,count+1)
      | none    => (map.set atom (last+1), last+1,count+1)
    ) acc
  ) (HashMap.new, 0, 0)
  let revMap := nameMap.fold (fun acc (k, v) => acc.set v k) (HashMap.new)
  (lastVar, nameMap, revMap)

def Formula.printFromMap (println : String → IO Unit)
  : Formula → Nat × HashMap Atom Nat × HashMap Nat Atom → IO Unit
| ⟨clauses⟩, ⟨lastVar, nameMap, revMap⟩ => do
  println s!"p cnf {lastVar} {clauses.size}"
  for i in [1:lastVar+1] do
    println s!"c {i} {revMap.get? i |>.get!}"
  for c in clauses do
    let nums := c.lits.map (fun ⟨neg,a⟩ =>
      let n := nameMap.get? a |>.get!
      if neg then "-" ++ toString n else toString n
    )
    println (FoldableOps.toString (nums ++ ["0"]) (sep := " "))

def Formula.printDimacs (f : Formula) : IO Unit :=
  f.printFromMap (IO.println) (f.buildAtomMap)

def Formula.checkSAT (f : Formula) (cnfFile : String) 
  : IO (Option (HashMap String Bool)) := do
  let mapStuff := f.buildAtomMap
  -- Write formula to cnfFile
  IO.FS.withFile cnfFile .write (fun handle =>
    f.printFromMap handle.putStrLn mapStuff
  )
  -- Run cadical on cnfFile
  let out := (← IO.Process.output {
    stdin := .piped
    stdout := .piped
    stderr := .piped
    cmd := "cadical"
    args := #[cnfFile]
  }).stdout
  let lines := out.splitOn "\n" |>.filter (not <| ·.startsWith "c")
  match lines with
  | "s SATISFIABLE" :: satis =>
    return some (
      satis
      |>.filter (not <| ·.isEmpty)
      |>.map (·.drop 2 |>.splitOn " ")
      |>.join
      |>.map (·.toInt!)
      |>.filter (· ≠ 0)
      |>.foldl (fun acc i =>
          acc.set (mapStuff.2.2.get? (Int.natAbs i) |>.get!) (i > 0)
        ) (HashMap.new)
    )
  | "s UNSATISFIABLE" :: _ => return none
  | _ =>
    IO.println out
    return none


structure MaxSATFormula where
  hard : List Clause
  soft : List (Nat × Clause)

def MaxSATFormula.buildAtomMap : MaxSATFormula → HashMap Atom Nat × HashMap Nat Atom × Nat × Nat
| ⟨hard, soft⟩ =>
  let (nameMap, lastVar) :=
    (HashMap.new, 0)
    |> Foldable.fold hard (fun acc c =>
        acc
        |> c.lits.foldl (fun (map,last) ⟨_,atom⟩ =>
          -- if `atom` is in map, do nothing, else assign `atom` to next
          match map.get? atom with
          | some _  => (map,last)
          | none    => (map.set atom (last+1), last+1)
        )
      )
  let (nameMap, lastVar, weightSum) :=
    (nameMap, lastVar, 0)
    |> Foldable.fold soft (fun (nameMap, lastVar, weightSum) (weight, c) =>
      let (nameMap, lastVar) :=
        (nameMap, lastVar)
        |> c.lits.foldl (fun (map,last) ⟨_,atom⟩ =>
            -- if `atom` is in map, do nothing, else assign `atom` to next term
            match map.get? atom with
            | some _  => (map,last)
            | none    => (map.set atom (last+1), last+1)
            )
      (nameMap, lastVar, weight + weightSum))
  let revMap := nameMap.fold (fun acc (k, v) => acc.set v k) (HashMap.new)
  (nameMap, revMap, lastVar, weightSum)

def MaxSATFormula.printFromMap (println : String → IO Unit)
  : MaxSATFormula → HashMap Atom Nat × HashMap Nat Atom × Nat × Nat → IO Unit
| ⟨hard, soft⟩, ⟨nameMap, revMap, numVars, weightSum⟩ => do
  println s!"p wcnf {numVars} {hard.length + soft.length} {weightSum+1}"
  for i in [1:numVars+1] do
    println s!"c {i} {revMap.get? i |>.get!}"
  for c in hard do
    let nums := s!"{weightSum+1}" :: c.lits.map (fun ⟨neg,a⟩ =>
      let n := nameMap.get? a |>.get!
      if neg then "-" ++ toString n else toString n
    )
    println (FoldableOps.toString (nums ++ ["0"]) (sep := " "))
  for (weight, c) in soft do
    let nums := s!"{weight}" :: c.lits.map (fun ⟨neg,a⟩ =>
      let n := nameMap.get? a |>.get!
      if neg then "-" ++ toString n else toString n
    )
    println (FoldableOps.toString (nums ++ ["0"]) (sep := " "))

def MaxSATFormula.printWDimacs (f : MaxSATFormula) : IO Unit :=
  f.printFromMap (IO.println) (f.buildAtomMap)



-- **************************
-- *    Unit Prop / DPLL    *
-- **************************


inductive unitPropClause.Result
| sat | updated (C : Clause)

def unitPropClause (C : Clause) (assn : HashMap String Bool) : unitPropClause.Result :=
  let (sat, remAtoms) :=
    C.lits.foldr
      (fun l (sat, acc) =>
        match assn.get? l.atom with
        | none => (sat, l :: acc)
        | some b => (sat || b ≠ l.neg, acc))
      (false, [])
  if sat then .sat
  else .updated ⟨remAtoms, C.original⟩

-- returns none if formula is unsat after unit prop
-- else returns formula & assignments after unit prop
-- & ordered list of atoms & the clause they were propagated from

inductive unitProp.Result
| unsat (falsified : Clause) (pf : List (Literal × Clause))
| updated (F : Formula) (assn : HashMap Atom Bool) (props : List (Literal × Clause))
deriving Inhabited

partial def unitProp (F : Formula) (assn : HashMap Atom Bool) : unitProp.Result :=
  let rec iter (clauses : List Clause) (assn : HashMap Atom Bool)
                (props : List (Literal × Clause)) :=
    match
      clauses.foldl
        (fun
        | Sum.inl pf, _ => .inl pf
        | (.inr (acc, newAssns)), C =>
          match unitPropClause C assn with
          | .sat => .inr (acc, newAssns)
          | .updated ⟨[], _⟩ => .inl (C, props)
          | .updated ⟨[x], _⟩ => .inr (acc, (x,C) :: newAssns)
          | .updated C => .inr (C :: acc, newAssns))
        (.inr ([], []))
    with
    | .inl (badC, pf) => .unsat badC pf
    | .inr (clauses', []) => .updated ⟨clauses' |> Unfoldable.unfold⟩ assn props
    | .inr (clauses', newAssns) =>
      let assn := newAssns.foldl (fun assn ⟨⟨neg,a⟩, _⟩ =>
          assn.set a (not neg)
        ) assn
      iter clauses' assn (newAssns ++ props)
  iter (FoldableOps.toList F.clauses) assn []

partial def dpll (F : Formula) (assn : HashMap String Bool := HashMap.new)
  : Option (HashMap String Bool) :=
  -- F should not have empty clauses
  let rec iter (F : Formula) (assn : HashMap String Bool) :=
    match
      FoldableOps.findMap F.clauses
        (fun C => C.lits.head?)
    with
    | none =>
      assert! (F.clauses.size = 0)
      some assn -- sat
    | some x =>
      (match unitProp F (assn.set x.atom true) with
      | .unsat _ _ => none -- x=true unsat
      | .updated F' assn _ => iter F' assn)
      |>.orElse fun () =>
      match unitProp F (assn.set x.atom false) with
      | .unsat _ _ => none -- x=false unsat (entire thing unsat)
      | .updated F' assn _ => iter F' assn
  match unitProp F assn with
  | .unsat _ _ => none
  | .updated F' assn _ => iter F' assn

def resolve (a : Atom) (C1 C2 : Clause) : Clause :=
  {lits :=
    C1.original.filter (·.atom ≠ a) ++ C2.original.filter (fun l => l.atom ≠ a ∧ not (C1.original.contains l))}

def reverseUnitProp (falsifiedClause : Clause) (props : List (Literal × Clause)) :=
  match props with
  | .nil =>
    -- assert! falsifiedClause.lits.isEmpty
    []
  | .cons (l,C) props =>
    if falsifiedClause.original.any (·.atom = l.atom) then
      let res := resolve l.atom falsifiedClause C
      (l.atom, falsifiedClause, C, res) :: reverseUnitProp res props
    else
      reverseUnitProp falsifiedClause props

def amoConstraints (A : Array Literal n) (temps : Array Atom n) : View Clause :=
  View.view' (Range.mk n) |>.flatMap (fun ⟨j,h⟩ =>
    have : j < n+1 := Nat.le_step h
    have : j+1 < n+1 := Nat.succ_le_succ h 
    -- A[j] -> temps[j]
    ({lits := [A[j].not, ⟨false, temps[j]⟩]} ::
    if h : j+1 < n then
      [ -- temps[j] -> temps[j+1]
        {lits := [⟨true, temps[j]⟩, ⟨false, temps[j.succ]⟩]},
        -- temps[j] -> not A[j+1]
        {lits := [⟨true, temps[j]⟩, A[j+1].not]}]
    else [])
    |> View.view (F := List Clause)
  )

def amkConstraints (A : Array Literal n) (k : Nat) (temps : Array (Array Atom n) k) : View Clause :=
  sorry



-- ******************************
-- *      Question 1(a)         *
-- ******************************

structure SudokuEncoding (n : Nat) where
  vars : Array (Array (Array Atom n.square) n.square) n.square
  formula : Formula

-- Given some collection of squares (x,y), generate constraints
-- that each square is different
def allSquaresDiff {n : Nat}
  (sqVars : Array (Array (Array Atom n.square) n.square) n.square)
  (v : View (Fin n.square × Fin n.square))
  : View Clause
  :=
  v.flatMap (fun (x,y) =>
    v.flatMap (fun (x',y') =>
      if x = x' ∧ y = y'
      then (View.view [] : View Clause)
      else View.view' (Range.mk n.square) |>.map (fun (k : { x // x ∈ Range.mk n.square }) =>
        have : k.val < n.square := by cases k; simp; assumption
        {lits := [⟨true, sqVars[x][y][k.val]⟩, ⟨true, sqVars[x'][y'][k.val]⟩]}
      )))

-- Given some collection of the variables for squares (x,y)
-- generate constraints that at least one square is
-- assigned to `k` for each `k : Fin n.square`
def allKCovered {n : Nat}
  (sqVars : Array (Array (Array Atom n.square) n.square) n.square)
  (v : View (Fin n.square × Fin n.square)) : View Clause
  := View.view' (Range.mk n.square) |>.map (fun ⟨k,h⟩ =>
    {lits := v.map (fun (x,y) => ⟨false, sqVars[x][y][k]⟩) |> FoldableOps.toList}
  )

def sudokuConstraints (n : Nat) (squareVar : Array (Array (Array Atom n.square) n.square) n.square):=
  -- Each square must have at least one assignment
  let perSquareConstraint : View Clause :=
    View.view' (Range.mk n.square) |>.flatMap (fun x =>
      View.view' (Range.mk n.square) |>.map (fun y =>
        {lits := View.view' (Range.mk n.square) |>.map (fun k =>
            have := x.prop; have := y.prop; have := k.prop
            ⟨false, squareVar[x.val][y.val][k.val]⟩)
          |> FoldableOps.toList }))
  -- For each block/row/col, each square should be different
  let blockConstraints : View Clause :=
    View.view' (Range.mk n) |>.flatMap (fun xb =>
      View.view' (Range.mk n) |>.flatMap (fun yb =>
        allSquaresDiff squareVar (
          View.view' (Range.mk n) |>.flatMap (fun x =>
            View.view' (Range.mk n) |>.map (fun y =>
              ( ⟨xb*n+x, by sorry⟩, 
                ⟨yb*n+y, by sorry⟩)
            ))
        )))
  let rowConstraints : View Clause :=
    View.view' (Range.mk n.square) |>.flatMap (fun x =>
      allSquaresDiff squareVar (
        View.view' (Range.mk n.square) |>.map (fun y =>
          (⟨x.val, x.prop⟩,⟨y.val, y.prop⟩))
      ))
  let colConstraints : View Clause :=
    View.view' (Range.mk n.square) |>.flatMap (fun y =>
      allSquaresDiff squareVar (
        View.view' (Range.mk n.square) |>.map (fun x =>
          (⟨x.val, x.prop⟩,⟨y.val, y.prop⟩))
      ))
  -- Collect constraints into formula
  perSquareConstraint ++ blockConstraints ++
    rowConstraints ++ colConstraints

def sudokuBoard (n : Nat) (fixed : List (Fin n.square × Fin n.square × Fin n.square)) :=
  -- `vars[x][y][k]` ≝ whether square (`x`, `y`) is assigned `k`
  let vars : Array (Array (Array Atom n.square) n.square) n.square :=
    Array.init (fun x => Array.init (fun y => Array.init (fun k =>
      s!"square{x},{y}_is_{k.val+1}")))
  let constraints := sudokuConstraints n vars
  let fixedConstraints : List Clause := fixed.map (fun ((x,y,k) : Fin n.square × Fin n.square × Fin n.square) =>
    {lits := [⟨false, vars[x][y][k]⟩]})
  SudokuEncoding.mk vars ⟨Unfoldable.unfold (constraints ++ View.view fixedConstraints)⟩

partial def printAllSols : SudokuEncoding n → IO Unit
| ⟨vars, formula⟩ =>
  let rec iter (F) (count) := do
    match dpll F with
    | none => IO.println s!"Formula UNSAT after {count} solutions"
    | some assn =>
    IO.println s!"Solution {count}:"
    for h : x in Range.mk n.square do
      for h : y in Range.mk n.square do
        for h : k in Range.mk n.square do
          if assn.get? (vars[x][y][k]) |>.get! then
            IO.print (k+1)
        IO.print " "
      IO.println ""
    let newClause : Clause :=
      {lits := View.view vars |>.flatten.flatten
        |>.flatMap (fun a =>
          if assn.get? a |>.get! then
            [⟨true, a⟩]
          else []
        )
        |> FoldableOps.toList}
    iter ⟨F.clauses.push newClause⟩ (count+1)
  iter formula 0



-- ******************************
-- *      Question 2(a)         *
-- ******************************

def aIffbc (a b c : Atom) : List Clause :=
  [ { lits := [⟨true,a⟩, ⟨false,b⟩] }
  , { lits := [⟨true,a⟩, ⟨false,c⟩] }
  , { lits := [⟨false,a⟩, ⟨true,b⟩, ⟨true,c⟩]}]

def question2a : MaxSATFormula :=
  let (S, G) : Atom × Atom := ("S", "G")
  let xs : Array Atom 6 := Array.init (fun i => s!"x{i+1}")
  { hard := [ { lits := [⟨false,S⟩] }
            , { lits := [⟨false,G⟩] } ]
            -- S constraint
            ++ aIffbc S xs[0] xs[2]
            ++ aIffbc xs[0] S xs[1]
            ++ aIffbc xs[1] xs[0] xs[3]
            ++ aIffbc xs[2] S xs[4]
            ++ aIffbc xs[3] xs[1] xs[5]
            ++ aIffbc xs[4] xs[2] G
            ++ aIffbc xs[5] xs[3] G
    soft := [ (1, { lits := [⟨true, xs[0]⟩] })
            , (1, { lits := [⟨true, xs[1]⟩] })
            , (1, { lits := [⟨true, xs[2]⟩] })
            , (1, { lits := [⟨true, xs[3]⟩] })
            , (1, { lits := [⟨true, xs[4]⟩] })
            , (1, { lits := [⟨true, xs[5]⟩] })]
  }


def main : IO Unit := do
  let left := sudokuBoard 2 [
    (0,0,1),
    (1,2,2),
    (2,3,0),
    (3,2,1)]
  let middle := sudokuBoard 2 [
    (0,0,1),
    (1,2,2),
    (2,3,0),
    (3,1,0)]
  let right := sudokuBoard 2 [
    (0,0,1),
    (1,2,2),
    (2,3,0),
    (3,1,2)]
  
  IO.println "***** Question 1(b) *****"
  IO.println "Middle can be solved by UP:"
  (match unitProp middle.formula HashMap.new with
  | .unsat _ _ => IO.println "something went wrong"
  | .updated _ _ prop => do
    for (l,C) in prop.reverse do
      IO.println (l :: C.lits.filter (· ≠ l)))
  
  IO.println "\n***** Question 1(c) *****"
  IO.println "Left (satisfiable but not valid):"
  printAllSols left
  IO.println "Middle (satisfiable & valid):"
  printAllSols middle
  IO.println "Right (unsatisfiable):"
  printAllSols right

  IO.println "\n***** Question 1(d) *****"
  (match unitProp right.formula HashMap.new with
  | .updated .. => IO.println "something went wrong"
  | .unsat badC pf => do
    IO.println "formula:"
    for C in right.formula.clauses do
      IO.println C.original
    IO.println "proof:"
    for (l, _, _, res) in reverseUnitProp badC pf do
      IO.println s!"resolve on {l} to get:"
      IO.println res)

  IO.println "\n***** Question 2(a) *****"
  question2a.printWDimacs

  IO.println "\n***** Question 2(b) *****"
  IO.println "Shortest path = {S, x3, x5, G}"

