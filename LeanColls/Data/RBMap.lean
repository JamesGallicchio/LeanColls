/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Dict
import LeanColls.Data.Transformer.View

import Std.Data.RBMap


namespace LeanColls

structure RBMap (κ) [Ord κ] (τ) where
  data : Std.RBMap κ τ compare

instance [Ord κ] : Fold (RBMap κ τ) (κ × τ) where
  fold := fun m f init => m.data.foldl (fun acc k t => f acc (k,t)) init
  foldM := fun m f init => m.data.foldlM (fun acc k t => f acc (k,t)) init

instance [Ord κ] : Fold (Dict.KeySet (RBMap κ τ)) κ where
  fold := fun m f init => m.data.data.foldl (fun acc k _ => f acc k) init
  foldM := fun m f init => m.data.data.foldlM (fun acc k _ => f acc k) init

instance [Ord κ] : Membership (κ × τ) (RBMap κ τ) where
  mem := fun (k,t) m => m.data.find? k = some t

instance [Ord κ] : Membership κ (Dict.KeySet (RBMap κ τ)) where
  mem := fun k ⟨m⟩ => m.data.keys.contains k

instance [Ord κ] : Bag.ReadOnly (Dict.KeySet (RBMap κ τ)) κ where
  toMultiset := fun ⟨m⟩ => m.data.keysList

instance [Ord κ] : Dict (RBMap κ τ) κ τ where
  toMultiset := fun m => m.data.toList
  size := fun m => m.data.size
  empty := ⟨.empty⟩
  insert := fun m (k,t) => ⟨m.data.insert k t⟩
  get? := fun m k => m.data.find? k
  set := fun m k x => ⟨m.data.insert k x⟩
  modify := fun m k f => ⟨m.data.modify k f⟩
  alter := fun m k f => ⟨m.data.alter k f⟩
  toBagKeySet := inferInstance
