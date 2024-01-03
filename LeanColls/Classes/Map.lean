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

-- TODO docstrings

class Map (C : Type u) (κ : outParam (Type v)) (τ : outParam (Type w))
  extends MultiBag C (κ × τ) where
  get? : C → κ → Option τ
  update : C → κ → (Option τ → Option τ) → C
  set : C → κ → τ → C := (update · · <| Function.const _ <| some ·)
  remove : C → κ → C := (update · · (Function.const _ none))
