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
  toList    := λ c      => Foldable.fold c (fun acc x => x::acc) [] |>.reverse
  all       := λ c f    => Foldable.fold c (fun acc x => acc && f x) true
  contains  := λ c _ x  => Foldable.fold c (fun acc y => acc || BEq.beq x y) true
  sum       := λ c      => Foldable.fold c (fun acc x => acc + x) 0

instance [F : Foldable C τ] : Inhabited (FoldableOps C τ) where
  default := defaultImpl F

