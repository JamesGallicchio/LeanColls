/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Bag
import LeanColls.Classes.IndexType

namespace LeanColls

/-! ## Indexed Collections

This file defines [Indexed] collections, which are indexed by some type `ι`.
The math model for indexed collections is a total function `ι → α`.

**Note:** technically [Indexed] does not require `ι` to be [IndexType],
but a lawful [Indexed] instance implies an [IndexType] instance on `ι`.
-/

/-- An indexed collection `cont` can be reinterpreted as a
  multibag of pairs `(i, cont[i])`.

  This is similar to the `List.enum` operation. -/
structure Indexed.WithIdx (C : Type u) where
  cont : C

class Indexed (C : Type u) (ι : outParam (Type v)) (τ : outParam (Type w))
  extends
    MultiBag.ReadOnly C τ
  where
  toMultiBagWithIdx : MultiBag.ReadOnly (Indexed.WithIdx C) (ι × τ)
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

namespace Indexed

def withIdx (cont : C) : Indexed.WithIdx C := .mk cont

end Indexed

class LawfulIndexed (C ι τ) [Indexed C ι τ] where
  get_ofFn : ∀ f, Indexed.get (Indexed.ofFn (C := C) f) = f
  get_set_eq : ∀ (cont : C) i a j,
    i = j → Indexed.get (Indexed.set cont i a) j = a
  get_set_neq : ∀ (cont : C) i a j,
    i ≠ j → Indexed.get (Indexed.set cont i a) j = Indexed.get cont j
  update_set_get : ∀ (cont : C) i f,
    (Indexed.update cont i f) = Indexed.set cont i (f (Indexed.get cont i))

namespace Indexed

variable [Indexed C ι τ] [LawfulIndexed C ι τ]

@[simp] theorem get_set_eq (cont : C)
  : Indexed.get (Indexed.set cont i a) i = a := by
  rw [LawfulIndexed.get_set_eq]; simp

@[simp] theorem get_set_ne (cont : C) (h : i ≠ j)
  : Indexed.get (Indexed.set cont i a) j = Indexed.get cont j := by
  rw [LawfulIndexed.get_set_neq]; simp [h]

@[simp] theorem get_update_eq (cont : C)
  : Indexed.get (Indexed.update cont i f) i = f (Indexed.get cont i) := by
  simp[LawfulIndexed.update_set_get]

@[simp] theorem get_update_ne (cont : C) (h : i ≠ j)
  : Indexed.get (Indexed.update cont i a) j = Indexed.get cont j := by
  simp[LawfulIndexed.update_set_get,h]

export LawfulIndexed (get_ofFn)
attribute [simp] get_ofFn
