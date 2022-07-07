/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes

namespace LeanColls

class FoldableOps (C τ) [Foldable C τ] where
  toList : C → List τ
  all : C → (τ → Bool) → Bool

namespace FoldableOps

def defaultImpl (F : Foldable C τ) : FoldableOps C τ where
  toList    := λ c    => Foldable.fold (fun acc x => x::acc) [] c |>.reverse
  all       := λ c f  => Foldable.fold (fun acc x => acc && f x) true c

instance [F : Foldable C τ] : Inhabited (FoldableOps C τ) where
  default := defaultImpl F

/- TODO: figure out how to generate foldable' generically
def foldable' [F : Foldable C τ] [B : BEq τ] [M : Membership τ C]
  (h_mem : ∀ c x, x ∈ c ↔ (defaultImpl F B).contains c x)
  : Foldable' C τ M where
  fold' := F.fold
  -/

theorem toList_ind [Foldable C τ] [BEq τ] [FoldableOps C τ] {α : Type u} {motive : List τ → Sort v}
        (nil : motive List.nil)
        (cons : (hd : τ) → (tl : List τ) → motive tl → motive (List.cons hd tl))
        (t : C) : motive (FoldableOps.toList t)
  := by
  induction toList t
  assumption
  exact cons _ _ (by assumption)

end FoldableOps

class FoldableEqOps (C τ) [Foldable C τ] [BEq τ] extends FoldableOps C τ where
  contains : C → τ → Bool

namespace FoldableEqOps

def defaultImpl (F : Foldable C τ) (B : BEq τ) : FoldableEqOps C τ :=
  { FoldableOps.defaultImpl F with
    contains := λ c x  => Foldable.fold (fun acc y => acc || BEq.beq x y) true c}

end FoldableEqOps

end LeanColls
