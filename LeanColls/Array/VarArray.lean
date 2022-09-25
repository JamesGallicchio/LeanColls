/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Array.COWArray

namespace LeanColls

structure VarArray (α) where
  size : Nat
  backing : COWArray α size

namespace VarArray

instance : FoldableOps (VarArray α) α :=
  FoldableOps.mapImpl' (λ a => COWArray α a.size) (VarArray.backing)

instance : Indexed (VarArray α) α where
  size a := a.size
  nth a i := a.backing.get i

instance : IndexedOps (VarArray α) α := default

def empty : VarArray α := ⟨0, COWArray.empty⟩
