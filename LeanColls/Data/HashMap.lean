/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Map
import LeanColls.Data.Transformer.View

import Std.Data.HashMap


namespace LeanColls

export Std (HashMap)

variable [BEq κ] [Hashable κ]

instance : Fold (HashMap κ τ) (κ × τ) where
  fold := fun m f init => m.fold (fun acc k t => f acc (k,t)) init
  foldM := fun m f init => m.foldM (fun acc k t => f acc (k,t)) init

instance : Fold (Map.KeySet (HashMap κ τ)) κ where
  fold := fun m f init => m.data.fold (fun acc k _ => f acc k) init
  foldM := fun m f init => m.data.foldM (fun acc k _ => f acc k) init

instance : Map (HashMap κ τ) κ τ where
  mem := fun (k,t) m => m.find? k = some t
  toMultiset := fun m => m.toList
  fold := fun m f init => m.fold (fun acc k t => f acc (k,t)) init
  size := fun m => m.size
  empty := .empty
  insert := fun m (k,t) => m.insert k t
  get? := fun m k => m.find? k
  set := fun m k t => m.insert k t
  alter := fun m k f =>
    let cur := m.find? k
    match cur, f cur with
    | none, none => m
    | _, some v => m.insert k v
    | some _, none => m.erase k
  modify := fun m k f => m.modify k (Function.const _ f)
  toBagKeySet := {
    mem := fun x m => m.data.contains x
    size := fun s => s.data.size
    toFinset := sorry
  }
