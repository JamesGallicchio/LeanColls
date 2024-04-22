/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Bag

/-! ## Dictionaries

Dictionaries are collections which encode relational data.
The math model is a partial function `α → Option β`.
-/

namespace LeanColls

namespace Dict

/-- Represents the key set of a `C` map.

This is a trivial wrapper structure,
on which dictionary implementations should provide a `Bag` instance.
-/
structure KeySet (C : Type u) where
  data : C

end Dict

class Dict (C : Type u) (κ : outParam (Type v)) (τ : outParam (Type w))
  extends MultiBag C (κ × τ) where
  /-- The [Bag] instance providing functions on this collection's [KeySet]. -/
  toBagKeySet : Bag.ReadOnly (Dict.KeySet C) κ
  /-- Look up `k` in collection `cont` -/
  get? : (cont : C) → (k : κ) → Option τ
  /-- Alter the entry at key `k` in `cont`.
    The `f` is given the current value at `k`,
    or none if not defined at `k`.
    If `f` returns `none`, `k` is erased. -/
  alter : (cont : C) → (k : κ) → (f : Option τ → Option τ) → C
  /-- Set the entry at key `k` to `v` in `cont`. -/
  set : (cont : C) → (k : κ) → (v : τ) → C := (alter · · <| Function.const _ <| some ·)
  /-- Modify the value at key `k`, if present, by applying `f`.
    Otherwise leave the map unchanged. -/
  modify : (cont : C) → (k : κ) → (f : τ → τ) → C := (alter · · <| Option.map · )
  /-- Remove the entry at key `k`, if present. -/
  remove : (cont : C) → (k : κ) → C := (alter · · (Function.const _ none))

attribute [instance] Dict.toBagKeySet

namespace Dict

def keySet (cont : C) : KeySet C := ⟨cont⟩
