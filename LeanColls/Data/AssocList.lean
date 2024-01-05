/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Map
import LeanColls.Data.Transformer.View

import Std.Data.AssocList


namespace LeanColls

export Std (AssocList)

instance [BEq κ] : Fold (AssocList κ τ) (κ × τ) where
  fold := fun m f init => m.foldl (fun acc k t => f acc (k,t)) init
  foldM := fun m f init => m.foldlM (fun acc k t => f acc (k,t)) init

instance [BEq κ] : Fold (Map.KeySet (AssocList κ τ)) κ where
  fold := fun m f init => m.data.foldl (fun acc k _ => f acc k) init
  foldM := fun m f init => m.data.foldlM (fun acc k _ => f acc k) init

instance [BEq κ] : Map (AssocList κ τ) κ τ where
  mem := fun (k,t) m => m.find? k = some t
  toMultiset := fun m => m.toList
  size := fun m => m.length
  empty := .nil
  insert := fun m (k,t) => m.cons k t
  get? := fun m k => m.find? k
  set := fun m k x => m.cons k x
  modify := fun m k f => m.modify k (Function.const _ f)
  alter := fun m k f => sorry
  toBagKeySet := {
    toFinset := sorry
    size := sorry
  }
