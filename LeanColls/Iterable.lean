
inductive ContOrDone (final acc : Type u)
| Cont : acc -> ContOrDone final acc
| Done : final -> ContOrDone final acc

namespace ContOrDone

def bind {final a b} (cod : ContOrDone final a)
  (f : a → ContOrDone final b) 
  : ContOrDone final b :=
  match cod with
  | Cont a => f a
  | Done b => Done b

instance {final} : Monad (ContOrDone final) :=
  {bind, pure := Cont}

end ContOrDone


open ContOrDone

class FoldUntil (C : Type u) (τ : outParam (Type v)) where
  foldUntil : {acc final : Type w}
                → (f : acc -> τ -> ContOrDone final acc)
                → (init : acc)
                → C → ContOrDone final acc

class Fold (C : Type u) (τ : outParam (Type v)) where
  fold : C → (α → τ → α) → α → α

instance {C} [FoldUntil C τ] : Fold C τ where
  fold c f init :=
    match FoldUntil.foldUntil (λ acc elem => Cont (f acc elem)) init c with
    | Cont a => a
    | Done a => a

  