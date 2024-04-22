/- Copyright (c) 2023 James Gallicchio

Authors: James Gallicchio
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

import LeanColls.Classes.Ops

/-! ## Bags

Bags are collections of elements of a single type.
Other languages often call these collections "sets",
but in Lean this word is quite overloaded.

This file defines two common classes of bag:
- [Bag]: no duplicates; math model is [Finset]
- [MultiBag]: duplicates; math model is [Multiset]

It also defines classes for read-only variants which
do not include a way to insert or remove elements.

-/

namespace LeanColls

/-- [Bag] operations expected on read-only "set-like" collections.

Note that this requires `ToMultiset` even though the model is `ToFinset`;
lawfulness is stated in terms of `ToFinset`,
but some `Bag`s can't provide `ToFinset` without some extra hypotheses.
-/
class Bag.ReadOnly (C : Type u) (τ : outParam (Type v)) extends
  Membership τ C,
  ToMultiset C τ,
  Fold C τ,
  Size C

/-- [Bag] includes operations expected on most "set-like" collections. -/
class Bag (C : Type u) (τ : outParam (Type v)) extends
  Bag.ReadOnly C τ,
  Insert C τ

/-- [MultiBag] operations expected on read-only "multiset-like" collections -/
class MultiBag.ReadOnly (C : Type u) (τ : outParam (Type v)) extends
  Membership τ C,
  ToMultiset C τ,
  Fold C τ,
  Size C

/-- [MultiBag] includes operations expected on most "multiset-like" collections -/
class MultiBag (C : Type u) (τ : outParam (Type v)) extends
  MultiBag.ReadOnly C τ,
  Insert C τ
