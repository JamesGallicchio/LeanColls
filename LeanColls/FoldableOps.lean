/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes

namespace LeanColls

class FoldableOps (F τ) where
  mem : [DecidableEq τ] → F → τ → Bool

instance [Foldable F τ] : Inhabited (FoldableOps F τ) where
  default := {
    mem := λ C x => Foldable.fold (λ y found => x = y ∨ found) false C
  }

end LeanColls
