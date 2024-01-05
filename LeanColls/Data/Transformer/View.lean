/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Ops

/-! ## Views

Views are suspended collection computations.

This allows programmers to avoid producing intermediary values
in a series of collection operations,
which can often produce faster and more memory-efficient code.
-/

namespace LeanColls

inductive View.{u,v,w} : Type u → Type (max (u+1) (v+1) (w+1))
| of [Fold.{v,u,w} C τ] (c : C) : View τ
| map (f : τ → τ') (v : View τ) : View τ'
| filter (f : τ → Bool) (v : View τ) : View τ
| filterMap (f : τ → Option τ') (v : View τ) : View τ'
| flatMap {τ τ' : Type u} (f : τ → View τ') (v : View τ) : View τ'

namespace View

def fold (f : β → τ → β) (init : β) : View τ → β
| @View.of _ _ _ c => Fold.fold c f init
| .map       g v =>
  fold
    (fun acc x => f acc (g x))
    init v
| .filter    g v =>
  fold
    (fun acc x => if g x then f acc x else acc)
    init v
| .filterMap g v =>
  fold
    (fun acc x =>
      match g x with
      | none => acc
      | some y => f acc y)
    init v
| .flatMap   g v =>
  fold
    (fun acc x => fold f acc (g x))
    init v

def foldM [Monad m] (f : β → τ → m β) (init : β) : View τ → m β
| @View.of _ _ _ c => Fold.foldM c f init
| .map       g v =>
  foldM
    (fun acc x => f acc (g x))
    init v
| .filter    g v =>
  foldM
    (fun acc x => if g x then f acc x else pure acc)
    init v
| .filterMap g v =>
  foldM
    (fun acc x =>
      match g x with
      | none => pure acc
      | some y => f acc y)
    init v
| .flatMap   g v =>
  foldM
    (fun acc x => foldM f acc (g x))
    init v

instance : Fold (View τ) τ where
  fold v f init := fold f init v
