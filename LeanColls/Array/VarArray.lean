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

instance : Indexed (VarArray α) α where
  size a := a.size
  nth a i := a.backing.get i

def empty : VarArray α := ⟨0, COWArray.empty⟩
