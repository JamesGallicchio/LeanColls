import LeanColls.Iterable

inductive BinTree (τ : Type) : Type
| Empty : BinTree τ
| Node : BinTree τ → τ → BinTree τ → BinTree τ

namespace BinTree

def foldUntil {τ final α}
  (f : α → τ → ContOrDone final α)
  (init : α)
  : BinTree τ → ContOrDone final α
| Empty => ContOrDone.Cont init
| Node L x R => do
  let l_acc <- foldUntil f init L
  let x_acc <- f l_acc x
  let r_acc <- foldUntil f x_acc R
  return r_acc

instance : FoldUntil (BinTree τ) τ :=
  ⟨foldUntil⟩

end BinTree
