/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes

namespace LeanColls


-- How to ensure model is erased at runtime?
class Queue (C : Type u) (τ : outParam (Type v)) where
  empty : C
  enq : C → τ → C
  deq : C → Option (τ × C)

namespace Queue

structure CorrectFIFO (Q : Queue C τ) where
  model : C → List τ
  h_empty : [] = model empty
  h_enq : ∀ c t, (model c) ++ [t] = model (enq c t)
  h_deq : ∀ c, List.front? (model c) = Option.map  (λ (x,c') => (x, model c')) (deq c)

structure CorrectLIFO (Q : Queue C τ) where
  model : C → List τ
  h_empty : [] = model empty
  h_enq : ∀ c t, t :: (model c) = model (enq c t)
  h_deq : ∀ c, List.front? (model c) = Option.map (λ (x,c') => (x, model c')) (deq c)
