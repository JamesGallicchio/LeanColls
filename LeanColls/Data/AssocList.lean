/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Dict
import LeanColls.Classes.Ops.Fold
import LeanColls.Data.Transformer.View

import Batteries.Data.AssocList

/-! ### AssocList

This file hooks `Batteries.AssocList` and mathlib's `AList`
into the `LeanColls` framework.

Note `AssocList` has a very ugly theory without an assumption
that there are no duplicate keys.
Mathlib's `AList` has a nicer theory but worse computational properties.
-/

namespace LeanColls

export Batteries (AssocList)

namespace AssocList

instance : Fold (AssocList κ τ) (κ × τ) where
  fold := fun m f init => m.foldl (fun acc k t => f acc (k,t)) init
  foldM := fun m f init => m.foldlM (fun acc k t => f acc (k,t)) init

instance : ToList (AssocList κ τ) (κ × τ) where
  toList := Batteries.AssocList.toList

instance : Fold.ToList (AssocList κ τ) (κ × τ) where
  fold_eq_fold_toList := by
    intro c
    use c.toList
    simp only [toList]
    simp [fold]
  foldM_eq_fold := by
    simp [foldM, fold]
    intros
    rw [List.foldlM_eq_foldl]

instance [BEq κ] : Membership (κ × τ) (AssocList κ τ) where
  mem := fun (k,t) m => m.find? k = some t

instance : Fold (Dict.KeySet (AssocList κ τ)) κ where
  fold := fun m f init => m.data.foldl (fun acc k _ => f acc k) init
  foldM := fun m f init => m.data.foldlM (fun acc k _ => f acc k) init

instance : ToList (Dict.KeySet (AssocList κ τ)) (κ) where
  toList := fun ⟨al⟩ => al.toList.map (·.1)

instance : Fold.ToList (Dict.KeySet (AssocList κ τ)) κ where
  fold_eq_fold_toList := by
    intro c
    use c.data.toList.map (·.1)
    simp only [toList]
    simp [fold, List.foldl_map]
  foldM_eq_fold := by
    simp [foldM, fold]
    intros
    rw [List.foldlM_eq_foldl]

instance [DecidableEq κ] : Membership κ (Dict.KeySet (AssocList κ τ)) := Fold.toMem

-- TODO(JG)
instance [DecidableEq κ] : Dict (AssocList κ τ) κ τ where
  size := fun m => m.length
  empty := .nil
  insert := fun m (k,t) => m.cons k t
  toMultiset := fun m => m.toList
  get? := fun m k => m.find? k
  set := fun m k x => m.erase k |>.cons k x
  remove := fun m k => m.erase k
  modify := fun m k f => m.modify k (Function.const _ f)
  -- TODO: can implement much more efficiently by just doing recursively
  alter := fun m k f =>
    match m.find? k with
    | none =>
      match f none with
      | none => m
      | some v => m.cons k v
    | some v =>
      match f (some v) with
      | none => m.erase k
      | some v' => m.replace k v'
  toBagKeySet := {
    toMultiset := fun ⟨m⟩ => m.toList.map (·.1)
    size := fun ⟨m⟩ => m.length
  }

end AssocList
