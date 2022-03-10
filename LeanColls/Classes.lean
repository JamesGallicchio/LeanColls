/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.AuxLemmas

/-!
# Generic Collection Classes

These classes form the top-level organization of the collections
hierarchy. At the top of the hierarchy is `Iterable`. This
exposes a means of "external iteration" on a collection.

This is extended by `Foldable`, which provides "internal
iteration" by folding the entire object into a single value.

We also have a dual notion of consuming elements rather than
producing them. The `Enumerable` class provides a natural
insertion operation, allowing a collection to be built
from individual elements (potentially within some external
iteration scheme). The `Unfoldable` class provides a bulk
insertion operation, folding one collection to produce a new
one with all its elements.

Types which are `Foldable` and `Unfoldable` are `CollLike`, in the
sense that items can be inserted and removed from them. `CollLike`
types are divided into `SeqLike` (finite-length vectors),
`MapLike` (finite key-set maps), and `SetLike` (finite sets).
-/

namespace LeanColls

/-!
## Destruction
-/

/-!
### Iterable

Exposes `toIterator`, which gives an object that can traverse
the collection one item at a time.
-/
class Iterable (C : Type u) (τ : Type v) where
  ρ : Type v
  step : ρ → Option (τ × ρ)
  toIterator : C → ρ

instance [ToStream C ρ] [Stream ρ τ] : Iterable C τ where
  ρ := ρ
  step := Stream.next?
  toIterator := ToStream.toStream

/-!
### Foldable

Exposes `fold`, which reduces a collection by 
Gives a default implementation of `ToStream C` by first
building a `List τ` and then using this as the stream.
-/
class Foldable (C : Type u) (τ : outParam (Type v)) where
  fold : (τ → β → β) → β → C → β
  toIterable : Iterable C τ := ⟨List τ, List.front?, fold (· :: ·) []⟩

attribute [instance] Foldable.toIterable

/-!
## Construction
-/

/-!
### Unfoldable

Exposes an `unfold` which folds on a collection to build a
new collection with the folded elements.
-/
class Unfoldable (C : Type u) (τ : outParam (Type v)) where
  unfold : [Foldable F τ] → F → C

/-!
### Enumerable

Dual class to `Iterable`. Provides a builder which constructs
a collection one item at a time.
-/
class Enumerable (C : Type u) (τ : Type v)
  extends Unfoldable C τ where
  ρ : Type v
  fromEnumerable : ρ → C
  insert : Option (τ × ρ) → ρ
  unfold := fromEnumerable ∘
    Foldable.fold (λ t r => insert (some (t,r))) (insert none)

/-!
## CollLike

A utility class for types that are foldable and unfoldable.
-/
class CollLike (C : Type u) (τ : outParam (Type v))
  extends Foldable C τ, Unfoldable C τ

/-!
### SeqLike

Class of collections that are isomorphic to `Fin n → τ`
-/
class SeqLike (C : Type u) (τ : outParam (Type u))
  extends CollLike C τ where
  size : C → Nat
  nth c : Fin (size c) → β

/-!
### MapLike

Class of collections that are isomorphic to `α → Option β`
with an explicit set of keys
-/
class MapLike (C : Type u) (α β : outParam (Type u))
  extends ToStream C (α × β) where
  get : α → C → Option β

/-!
### SetLike

Class of collections that are isomorphic to `{ a : α // P a }`
for a decidable proposition `P : α → Bool`.
-/
class SetLike (C : Type u) (τ : outParam (Type u))
  extends MapLike C τ PUnit
