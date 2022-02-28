/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

def Model := List

namespace Model

def enq (Q : Model τ) (x : τ) : Model τ
:= Q.append (x :: [])

def deq : Model τ → Option (τ × Model τ)
| [] => none
| (x::xs) => some (x,xs)

end Model


-- How to ensure model is erased at runtime?
class Queue (C : Type u) (τ : outParam (Type v)) :=
  model : C → Model τ
  empty : C
  h_empty : [] = model empty
  enq : C → τ → C
  h_enq : ∀ c t, (model c).enq t = model (enq c t)
  deq : C → Option (τ × C)
  h_deq : ∀ c, (model c).deq = Option.map  (λ (x,c') => (x, model c')) (deq c)
