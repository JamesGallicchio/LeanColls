/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Ops
import LeanColls.Classes.IndexType

namespace LeanColls

/-! ## Indexed Collections

This file defines [Indexed] collections, which are indexed by some type `ι`.
The math model for indexed collections is a total function `ι → α`.

**Note:** technically [Indexed] does not require `ι` to be [IndexType],
but a lawful [Indexed] instance implies an [IndexType] instance on `ι`.
-/

class Indexed (C : Type u) (ι : outParam (Type v)) (τ : outParam (Type w))
  extends
    Membership τ C,
    ToMultiset C τ,
    Fold C (ι × τ),
    Size C
   where
  /-- Form an instance of the collection type by
    specifying its value at every index. -/
  ofFn : (ι → τ) → C
  /-- Get the value of a collection at an index. -/
  get : (cont : C) → (i : ι) → τ
  /-- Apply a function at an index (often done in-place). -/
  update : (cont : C) → (i : ι) → (τ → τ) → C
  /-- Set the value of the function at an index -/
  set : (cont : C) → (i : ι) → τ → C := (update · · <| Function.const _ ·)
  size cont := fold cont (fun acc _ => acc + 1) 0

class LawfulIndexed (C ι τ) [DecidableEq ι] [Indexed C ι τ] where
  get_ofFn : ∀ f, Indexed.get (Indexed.ofFn (C := C) f) = f
  get_set : ∀ (cont : C) i a j,
    Indexed.get (Indexed.set cont i a) j =
      if i = j then a else Indexed.get cont j
  get_update : ∀ (cont : C) i f j,
    Indexed.get (Indexed.update cont i f) j =
      if i = j then f (Indexed.get cont j) else Indexed.get cont j

namespace Indexed

variable [Indexed C ι τ] [DecidableEq ι] [LawfulIndexed C ι τ]

@[simp] theorem get_set_eq (cont : C)
  : Indexed.get (Indexed.set cont i a) i = a := by
  rw [LawfulIndexed.get_set]; simp

@[simp] theorem get_set_ne (cont : C) (h : i ≠ j)
  : Indexed.get (Indexed.set cont i a) j = Indexed.get cont j := by
  rw [LawfulIndexed.get_set]; simp [h]

@[simp] theorem get_update_eq (cont : C)
  : Indexed.get (Indexed.update cont i f) i = f (Indexed.get cont i) := by
  rw [LawfulIndexed.get_update]; simp

@[simp] theorem get_update_ne (cont : C) (h : i ≠ j)
  : Indexed.get (Indexed.update cont i a) j = Indexed.get cont j := by
  rw [LawfulIndexed.get_update]; simp [h]

export LawfulIndexed (get_ofFn)
attribute [simp] get_ofFn
