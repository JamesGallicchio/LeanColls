/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Bag

/-! ## Maps

Maps are collections which encode relational data.
This file defines a few varieties of map:
- [Map]: many-to-one map; math model is a partial function
- [Indexed]: total map; math model is a total function

These classes all build on those defined in `Bag.lean`.
-/

namespace LeanColls

namespace Map

/-- Represents the key set of a `C` map.

This is a trivial wrapper structure on which [Map] instances
provide a [Bag] instance.
-/
structure KeySet (C : Type u) where
  data : C

end Map

class Map (C : Type u) (κ : outParam (Type v)) (τ : outParam (Type w))
  extends MultiBag C (κ × τ) where
  /-- The [Bag] instance providing functions on this collection's [KeySet]. -/
  toBagKeySet : Bag.ReadOnly (Map.KeySet C) κ
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

attribute [instance] Map.toBagKeySet

namespace Map

def keySet (cont : C) : KeySet C := ⟨cont⟩
