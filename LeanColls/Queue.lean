/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes

namespace LeanColls


-- How to ensure model is erased at runtime?
class Queue (C : Type u) (τ : outParam (Type v)) :=
  model : C → List τ
  empty : C
  h_empty : [] = model empty
  enq : C → τ → C
  h_enq : ∀ c t, (model c) ++ [t] = model (enq c t)
  deq : C → Option (τ × C)
  h_deq : ∀ c, List.front? (model c) = Option.map  (λ (x,c') => (x, model c')) (deq c)

end LeanColls
