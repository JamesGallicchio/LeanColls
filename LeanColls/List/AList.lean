/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.List.Basic
import Std.Data.AssocList

open LeanColls

/-! ## Association Lists -/

namespace Std.AssocList

variable [BEq κ]

instance : LeanColls.MapLike (AssocList κ τ) κ τ where
  fold l f a := l.foldl (f · <| .mk · ·) a
  get? := find?

def modifyOrInsert (k : κ) (f : Option (κ × τ) → Option τ) : AssocList κ τ → AssocList κ τ
| .nil =>
  match f none with
  | none => .nil
  | some t => .cons k t .nil
| .cons k' t' as =>
  if k' == k then
    match f (k', t') with
    | none => as
    | some t => .cons k t as
  else
    .cons k' t' <| modifyOrInsert k f as

def update (k : κ) (t : Option τ) : AssocList κ τ → AssocList κ τ
| .nil  =>
  match t with
  | none => .nil
  | some t => .cons k t .nil
| .cons k' t' as =>
  if k' == k then
    match t with
    | none => update k none as
    | some t => .cons k t as
  else
    .cons k' t' <| update k t as

def set (k : κ) (t : τ) (as : AssocList κ τ) := update k (some t) as

def remove (k : κ) (as : AssocList κ τ) := update k none as

def findAndUpdate (k : κ) (t : Option τ) : AssocList κ τ → Option τ × AssocList κ τ
| .nil  => match t with | none => (none, .nil) | some t => (none, .cons k t .nil)
| .cons k' t' as =>
  if k' == k then
    (t', match t with
    | none => update k none as
    | some t => .cons k t as)
  else
    let (old, as') := findAndUpdate k t as
    (old, .cons k' t' as')

def findAndSet (k : κ) (t : τ) (as : AssocList κ τ) := findAndUpdate k (some t) as

def findAndRemove (k : κ) (as : AssocList κ τ) := findAndUpdate k none as


@[simp]
theorem findAndUpdate_eq (k t) (as : AssocList κ τ)
  : findAndUpdate k t as = (find? k as, update k t as)
  := by
  induction as with
  | nil =>
    simp [findAndUpdate, find?, update]
    split <;> simp
  | cons _ _ tl ih =>
    simp [findAndUpdate, find?, update, ih]
    split <;> simp [*]

@[simp]
theorem findAndSet_eq (k t) (as : AssocList κ τ)
  : findAndSet k t as = (find? k as, set k t as)
  := by simp [findAndSet, set]

@[simp]
theorem findAndRemove_eq (k) (as : AssocList κ τ)
  : findAndRemove k as = (find? k as, remove k as)
  := by simp [findAndRemove, remove]
