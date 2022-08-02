/-
Copyright (c) 2022 James Gallicchio.

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
  ρ : Type w
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
  fold : {β : Type w} → C → (β → τ → β) → β → β

class Foldable' (C : Type u) (τ : outParam (Type v)) (mem : outParam (Membership τ C))
  extends Foldable C τ where
  fold' : {β : Type w} → (c : C) → (β → (t : τ) → t ∈ c → β) → β → β
  fold c f acc := fold' c (λ acc x h => f acc x) acc

/-!
Foldables can be Iterable by first collecting everything
into a list. Note that the iteration occurs in the same
order that elements are applied in when folding.
-/
@[defaultInstance]
instance [Foldable C τ] : Iterable C τ where
  ρ := List τ
  step := List.front?
  toIterator c :=
    Foldable.fold c (fun acc x => x::acc) []
    |> List.reverse

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
  fromEnumerator : ρ → C
  insert : Option (τ × ρ) → ρ
  unfold c :=
    Foldable.fold c (λ r t => insert (some (t,r))) (insert none)
    |> fromEnumerator

/-!
## Miscellaneous
-/

/-!
### Size

Class of collections with an efficient `size` operation
-/
class Size (C : Type u) where
  size : C → Nat

/-!
### SetLike

Class of collections with efficient membership checking
-/
class SetLike (C : Type u) (τ : outParam (Type v))
  extends Foldable C τ, Membership τ C where

/-!
### MapLike

Class of collections that have efficient key value lookup
-/
class MapLike (C : Type u) (α : outParam (Type v)) (β : outParam (Type w))
  extends Foldable C (α × β) where
  get? : C → α → Option β

/-!
### Indexed

Class of collections with efficient size and indexed
access operations
-/
class Indexed (C : Type u) (τ : outParam (Type u))
  extends Size C where
  nth c : Fin (size c) → τ


/-!
## External Hooks

We plug LeanColls into built-ins from Lean.
Each `Foldable` type gives rise to a `ForIn`, allowing
a collection `C` to be used in `for x in C do ...` syntax.
-/

instance instForInOfFoldable [Monad M] [Foldable F τ] : ForIn M F τ where
  forIn c acc f := do
    Foldable.fold c
      (λ ma x => do
        let a ← ma
        let res ← f x a
        match res with
        | ForInStep.yield y => pure y
        | ForInStep.done y => return y
      )
      (pure acc)

instance instForIn'OfFoldable' [Monad M] [Me : Membership τ F] [Foldable' F τ Me] : ForIn' M F τ Me where
  forIn' c acc f := do
    Foldable'.fold'
      c
      (λ ma x h => do
        let a ← ma
        let res ← f x h a
        match res with
        | ForInStep.yield y => pure y
        | ForInStep.done y => return y
      )
      (pure acc)

/-!
## Utility functions

We declare a number of utility functions for interacting with
collections. Operation classes are prefixed by the smallest
collection class which is sufficient to provide a default
implementation; for example, `FoldableOps` provides operations
on `Foldable` classes.

Default implementations are NOT registered as instances here.
Instead, each collection should manually register an instance
of the relevant operations classes, overriding operations for
which more efficient versions exist.
-/

