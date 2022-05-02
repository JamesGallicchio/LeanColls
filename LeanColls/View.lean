/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio, Mario Carneiro
-/

import LeanColls.Classes

namespace LeanColls

inductive View : Type u → Type (u+1)
| of {F τ} (c : F) [Foldable F τ] : View τ
| map (f : τ → τ') (v : View τ) : View τ'
| filter (f : τ → Bool) (v : View τ) : View τ
| filterMap (f : τ → Option τ') (v : View τ) : View τ'

namespace View

@[inline]
def fold (foldF : τ → β → β) (foldAcc : β) : View τ → β
| of c          => Foldable.fold foldF foldAcc c
| map f v       => fold (foldF ∘ f) foldAcc v
| filter f v    =>
    fold (λ x a =>
      if f x then foldF x a else a
    ) foldAcc v
| filterMap f v =>
    fold (λ x a =>
      match f x with
      | none    => a
      | some x' => foldF x' a
    ) foldAcc v

instance : Foldable (View τ) τ where
  fold := fold

end View

end LeanColls