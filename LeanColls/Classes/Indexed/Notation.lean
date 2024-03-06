/- Copyright (c) 2023 Tomáš Skřivan.

Authors: Tomáš Skřivan
-/

import LeanColls.Classes.Indexed.Basic

namespace LeanColls

/-! ## Notation for Indexed Collections

This file defines notation:
 - `x[i,j,k]` for getting elements
 - `x[i,j,k] := xi` for setting elements
-/


namespace Indexed.Notation

open Lean Meta

/-- Assuming `e = X₁ × ... Xₘ` this function returns `#[X₁, ..., Xₘ]`.

You can provide the expected number `n?` of elemnts then this function returns
`#[X₁, ..., (Xₙ × ... Xₘ)].

Returns none if `n? = 0` or `n? > m` i.e. `e` does not have enough terms.
-/
private partial def splitProdType (e : Expr) (n? : Option Nat := none)  : Option (Array Expr) :=
  if n? = .some 0 then
    none
  else
    go e #[]
  where
    go (e : Expr) (xs : Array Expr) : Option (Array Expr) :=
      if .some (xs.size + 1) = n? then
        xs.push e
      else
        if e.isAppOfArity ``Prod 2 then
          go (e.getArg! 1) (xs.push (e.getArg! 0))
        else
          if n?.isNone then
            xs.push e
          else
            .none

/-- Make product element `(x₁, ..., xₙ)` from `#[x₁, ..., xₙ]` -/
private def mkProdElem (xs : Array Expr) : MetaM Expr :=
  match xs.size with
  | 0 => return default
  | 1 => return xs[0]!
  | _ =>
    let n := xs.size
    xs[0:n-1].foldrM (init:=xs[n-1]!) fun x p => mkAppM ``Prod.mk #[x,p]


/-- Turn an array of terms in into a tuple. -/
private def mkTuple (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  `(term| ($(xs[0]!), $(xs[1:]),*))


/-- Element index can either be an index or a range. -/
syntax elemIndex := (term)? (":" (term)?)?


/--
The syntax `x[i,j,k]` gets the element of `x : X` indexed by `(i,j,k)`. It is required that there is
an instance `Indexed X I E` and `(i,j,k)` has type `I`.

This notation also support ranges, `x[:i,j₁:j₂,k]` returns a slice of `x`.

Note that product is right associated thus `x[i,j,k]`, `x[i,(j,k)]` and `x[(i,j,k)]` result in
the same expression.
-/
syntax:max (name:=indexedGet) (priority:=high) term noWs "[" elemIndex,* "]" : term


macro (priority:=high) x:ident noWs "[" ids:term,* "]" " := " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := Indexed.set $x $i $xi)

macro (priority:=high) x:ident noWs "[" ids:term,* "]" " ← " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := Indexed.set $x $i (← $xi))

macro x:ident noWs "[" ids:term,* "]" " += " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := Indexed.update $x $i (fun xi => xi + $xi))

macro x:ident noWs "[" ids:term,* "]" " -= " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := Indexed.update $x $i (fun xi => xi - $xi))

macro x:ident noWs "[" ids:term,* "]" " *= " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := Indexed.update $x $i (fun xi => xi * $xi))

macro x:ident noWs "[" ids:term,* "]" " /= " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := Indexed.update $x $i (fun xi => xi / $xi))

macro x:ident noWs "[" ids:term,* "]" " •= " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := Indexed.update $x $i (fun xi => $xi • xi))



/-- Elaborated index, it can be either index value or range. -/
private inductive Index
  | index (i : Expr)
  | range (r : Expr)

/-- Returns expression of elaborated index. -/
private def Index.getExpr (i : Index) : Expr :=
  match i with
  | index e => e
  | range e => e

/-- Is is elaborated index an index value? I.e. not a slice. -/
private def Index.isIndex (i : Index) : Bool :=
  match i with
  | index _ => true
  | range _ => false


open Elab Term
/-- Elaborate indices.

Returns `.inl` if `ids` does not contain ranges and returns `.inr` otherwise -/
private def elabIndices (ids : TSyntaxArray ``elemIndex) (Is : Array Expr) :
    TermElabM (Array Expr ⊕ Array Index) := do

  let mut isSlice := false
  let mut is : Array Index := #[]

  for id in ids, I in Is do
    match id with
    | `(elemIndex| $i:term) => do
      let i := Index.index (← elabTerm i I)
      is := is.push i
    | _ =>
      isSlice := true
      throwError "ranges are not yet suppored"

  if ¬isSlice then
    return .inl (is.map (·.getExpr))
  else
    return .inr is


open Lean Elab Term Meta Qq in
elab_rules (kind:=indexedGet) : term <= _expectedType
| `($x[$ids:elemIndex,*]) => do

  let ids := ids.getElems

  let getElemFallback : TermElabM (Option Expr) := do
    if ids.size ≠ 1 then
      return none
    match ids[0]! with
    | `(elemIndex| $i:term) => elabTerm (← `(getElem $x $i (by get_elem_tactic))) none
    | `(elemIndex| $i : $j) => elabTerm (← `(let a := $x; Array.toSubarray a $i $j)) none
    | `(elemIndex| $i :) => elabTerm (← `(let a := $x; Array.toSubarray a $i a.size)) none
    | `(elemIndex| : $j) => elabTerm (← `(let a := $x; Array.toSubarray a 0 $j)) none
    | _ => return none


  let x ← elabTerm x none
  let X ← inferType x
  let I ← mkFreshTypeMVar
  let E ← mkFreshTypeMVar
  let indexed := (mkAppN (← mkConstWithFreshMVarLevels ``Indexed) #[X, I, E])
  let .some inst ← synthInstance? indexed
    | if let .some xi ← getElemFallback then
         return xi
      else
        throwError s!"`{← ppExpr x} : {← ppExpr X}` is not indexed type.
Please provide instance `Indexed {← ppExpr X} ?I ?E`."

  let I ← instantiateMVars I
  let .some Is := splitProdType I ids.size
    | throwError "expected {(splitProdType I).getD #[] |>.size} indices to access elements of type `{← ppExpr X}` but {ids.size} are provided"

  match ← elabIndices ids Is with
    | .inl is =>
      let i ← mkProdElem is
      return ← mkAppOptM ``Indexed.get #[X,I,E,inst,x,i]
    | .inr _is =>
      throwError "ranges are not yet suppored"


@[app_unexpander Indexed.get] def unexpandIndexedGet : Lean.PrettyPrinter.Unexpander
  | `($(_) $x ($i, $is,*)) => `($x[$i:term,$[$is:term],*])
  | `($(_) $x $i) => `($x[$i:term])
  | _ => throw ()
