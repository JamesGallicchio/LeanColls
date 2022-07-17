/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes

namespace LeanColls

class FoldableOps (C τ) [Foldable C τ] where
  toList : C → List τ
  all : C → (τ → Bool) → Bool
  contains : C → [BEq τ] → τ → Bool
  sum : C → [Add τ] → [OfNat τ 0] → τ

namespace FoldableOps

def defaultImpl (F : Foldable C τ) : FoldableOps C τ where
  toList    := λ c      => Foldable.fold (fun acc x => x::acc) [] c |>.reverse
  all       := λ c f    => Foldable.fold (fun acc x => acc && f x) true c
  contains  := λ c _ x  => Foldable.fold (fun acc y => acc || BEq.beq x y) true c
  sum       := λ c      => Foldable.fold (fun acc x => acc + x) 0 c

instance [F : Foldable C τ] : Inhabited (FoldableOps C τ) where
  default := defaultImpl F

/- TODO: figure out if can generate foldable' generically
def foldable' [F : Foldable C τ] [B : BEq τ] [M : Membership τ C]
  (h_mem : ∀ c x, x ∈ c ↔ (defaultImpl F B).contains c x)
  : Foldable' C τ M where
  fold' := F.fold
  -/

end FoldableOps

end LeanColls
