import LeanColls.Sequence

inductive NTree (r : Nat) (τ : Type) : Type
| Empty : NTree r τ
| Leaf : τ → NTree r τ
| Node : (a : Array τ) → (h : Array.size a = r) → NTree r τ

namespace NTree

open Sequence

def fold_until {r} {τ final α}
  (f : α → τ → ContOrDone final α)
  (init : α)
  : NTree r τ → ContOrDone final α
| Empty => ContOrDone.Cont init
| Leaf x => f init x
| Node children _ =>
  Array.foldl

instance {τ} : Iterable (BinTree τ) :=
  {τ, fold_until}

end BinTree
