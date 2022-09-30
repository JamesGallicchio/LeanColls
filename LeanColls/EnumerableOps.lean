/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes

namespace LeanColls

namespace Enumerable

instance instPartition.{uAB,uab,uF,ur}
  [EA : Enumerable.{uAB,uab,uF,ur} A α]
  [EB : Enumerable.{uAB,uab,uF,ur} B β] : Enumerable.{uAB, uab, uF, ur} (A × B) (α ⊕ β) where
  ρ := Enumerable.ρ A × Enumerable.ρ B
  insert := fun
    | .none => (Enumerable.insert none, Enumerable.insert none)
    | .some (.inl a, (accA, accB)) => (Enumerable.insert (some (a,accA)), accB)
    | .some (.inr b, (accA, accB)) => (accA, Enumerable.insert (some (b,accB)))
  fromEnumerator := fun (accA, accB) =>
    (Enumerable.fromEnumerator accA, Enumerable.fromEnumerator accB)