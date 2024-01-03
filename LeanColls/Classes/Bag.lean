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

This file defines two common variants of bag:
- [Bag]: no duplicates; math model is [Finset]
- [MultiBag]: duplicates; math model is [Multiset]

-/

namespace LeanColls

-- TODO: docstrings

class Bag (C : Type u) (τ : outParam (Type v)) extends
  Membership τ C,
  ToFinset C τ,
  Fold C τ,
  Size C,
  Insert C τ

class MultiBag (C : Type u) (τ : outParam (Type v)) extends
  Membership τ C,
  ToMultiset C τ,
  Fold C τ,
  Size C,
  Insert C τ
