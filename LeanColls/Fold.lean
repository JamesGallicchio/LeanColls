
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


instance : FoldUntil {r : Std.Range // 0 < r.step} Nat where
  foldUntil := λ {α φ} f acc ⟨⟨start,stop,step⟩,h_step⟩ =>
    let rec loop (acc : α) (i : Nat) : ContOrDone φ α :=
      if h:i ≥ stop then pure acc else do
        let acc ← f acc i
        have : stop - (i + step) < stop - i := by
          sorry
        loop acc (i + step)
    loop acc start
    termination_by loop _ i => stop - i
