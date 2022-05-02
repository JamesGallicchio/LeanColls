/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes

namespace LeanColls

class FoldableOps (C τ) [Foldable C τ] [BEq τ] where
  toList : C → List τ
  h_toList : toList = Foldable.fold (· :: ·) []
  all : C → (τ → Bool) → Bool
  h_all : all = List.all ∘ toList
  contains : C → τ → Bool
  h_contains : contains = List.contains ∘ toList

instance [Foldable C τ] [BEq τ] : Inhabited (FoldableOps C τ) where
  default := {
    toList := _
    h_toList := rfl
    all := _
    h_all := rfl
    contains := _
    h_contains := rfl
  }

namespace FoldableOps

theorem toList_ind [Foldable C τ] [BEq τ] [FoldableOps C τ] {α : Type u} {motive : List τ → Sort v}
        (nil : motive List.nil)
        (cons : (hd : τ) → (tl : List τ) → motive tl → motive (List.cons hd tl))
        (t : C) : motive (FoldableOps.toList t)
  := by
  induction toList t
  assumption
  exact cons _ _ (by assumption)

end FoldableOps

end LeanColls
