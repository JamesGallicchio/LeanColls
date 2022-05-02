/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

class ExpectedSize (ρ : Type u) where
  expectedSize : ρ → Nat

class ToArray (ρ : Type u) (α : outParam (Type v)) where
  toArray : ρ → Array α

instance [ForIn Id ρ α] [ExpectedSize ρ] : ToArray ρ α where
  toArray r := Id.run do
    let mut a := Array.mkEmpty (ExpectedSize.expectedSize r)
    for x in r do
      a := a.push x
    return a
