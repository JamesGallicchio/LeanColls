/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.AuxLemmas

/-!
# Top-Level Collection Classes

See [Scala 2.13 Collections Library](https://docs.scala-lang.org/overviews/collections-2.13/overview.html)
for inspiration reference.
-/
namespace LeanColls

/-!
# ToStream

Highest class in the collections hierarchy. Exposes the ability
to do external iteration on the collection.
-/
#check ToStream


/-
# Seqlike

Class of collections that are isomorphic to `Fin n → τ`
-/
class Seqlike (C : Type u) (τ : outParam (Type u))
  extends ToStream C τ where
  size : C → Nat
  nth c : Fin (size c) → β

/-
# Maplike

Class of collections that are isomorphic to `α → Option β`
with an explicit set of keys
-/
class Maplike (C : Type u) (α β : outParam (Type u))
  extends ToStream C (α × β) where
  get : C → α → Option β

/-
# Setlike

Class of collections that are isomorphic to `{ a : α // P a }`
for a decidable proposition `P : α → Bool`.
-/
class Set (C : Type u) (τ : outParam (Type u))
  extends Maplike C τ PUnit
