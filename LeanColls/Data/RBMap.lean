/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Map
import LeanColls.Data.Transformer.View

import Std.Data.RBMap


namespace LeanColls

structure RBMap (κ) [Ord κ] (τ) where
  data : Std.RBMap κ τ compare

instance [Ord κ] : Map (RBMap κ τ) κ τ where
  mem := fun (k,t) m => m.data.find? k = some t
  toMultiset := fun m => m.data.toList
  fold := fun m f init => m.data.foldl (fun acc k t => f acc (k,t)) init
  size := fun m => m.data.size
  empty := ⟨.empty⟩
  insert := fun m (k,t) => ⟨m.data.insert k t⟩
  get? := fun m k => m.data.find? k
  update := fun m k f => ⟨m.data.alter k f⟩
  toBagKeySet := sorry -- TODO
