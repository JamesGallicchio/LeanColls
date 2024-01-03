/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Seq

import Mathlib.Data.List.Lemmas

namespace List

@[simp] theorem length_ofFn (f : Fin n → α) : length (ofFn f) = n := by
  simp [ofFn]

@[simp] theorem get_ofFn (f : Fin n → α) (i : Fin _)
  : get (ofFn f) i = f (i.cast (length_ofFn f)) := by
  rcases i with ⟨i,hi⟩
  simp
  rw [← Array.getElem_ofFn f i (by simp_all), ← Array.getElem_eq_data_get]
  suffices ∀ L (hL : L = ofFn f) (hi' : i < length L),
    (Array.mk L)[i] = (Array.ofFn f)[i]'(by clear hi; simp_all) from
    this _ rfl hi
  clear hi
  rintro L hL hi
  congr 1
  cases hL; simp [ofFn]

@[simp] theorem ofFn_def (f : Fin n → α)
  : ofFn f = (Array.ofFn f).data := by
  rw [←Array.toList_eq]; rfl

instance : LeanColls.Seq (List τ) τ where
  toList := id
  empty := []
  insert L x := x::L
  size := length
  fold L f init := foldl f init L
  ofFn := List.ofFn
  get := List.get
  set L i x := List.set L i x
