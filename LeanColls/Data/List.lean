/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Seq

import Mathlib.Data.List.Lemmas

open LeanColls

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

def snoc? : List α → Option (List α × α)
| [] => none
| x::xs =>
  match snoc? xs with
  | none => some ([],x)
  | some (xs',x') => some (x::xs', x')

@[simp] theorem snoc?_eq_none (c : List α) : snoc? c = none ↔ c = [] := by
  induction c <;> simp_all [snoc?]
  intro h; split at h <;> simp_all

@[simp] theorem snoc?_eq_some (c : List α) : snoc? c = some (xs,x) ↔ c = xs ++ [x] := by
  induction c generalizing xs x <;> simp_all [snoc?]
  case cons hd tl ih =>
  generalize ho : snoc? tl = o at ih
  cases o <;> simp_all
  · cases xs <;> simp
  · cases xs <;> simp_all
    · rintro rfl rfl; simp_all; apply ih; rfl
    · aesop; rw [←ih]; simp

instance : Seq (List τ) τ where
  toList := id
  empty := []
  insert L x := x::L
  size := length
  fold L f init := foldl f init L
  ofFn := List.ofFn
  get := List.get
  set L i x := List.set L i x
  cons := List.cons
  cons? := fun | [] => none | x::xs => (x,xs)
  snoc? := snoc?


@[simp] theorem toList_eq (L : List α) : toList L = L := rfl

instance : LawfulSeq (List τ) τ where
  mem_iff_mem_toList := by simp
  toList_append := by intros; rfl
  toMultiset_empty := rfl
  toMultiset_insert := by intros; rfl
  toMultiset_singleton := by intro; rfl
  size_def := by intro; rfl
  toList_ofFn := by intros; rfl
  get_def := by intros; rfl
  toList_set := by intros; rfl
  cons?_eq_none := by
    intro c; simp [Seq.cons?]
    split <;> simp
  cons?_eq_some := by
    intro c x c'; simp [Seq.cons?]
    split <;> simp
  cons?_eq_some_of_toList := by
    intro c x c' h; simp_all [Seq.cons?]
  snoc?_eq_none := by
    simp [Seq.snoc?]
  snoc?_eq_some := by
    simp [Seq.snoc?]
  snoc?_eq_some_of_toList := by
    simp [Seq.snoc?]; intros; use ?_

end List

namespace LeanColls.Seq

variable [Seq C τ] [LawfulSeq C τ]

@[simp] theorem size_toList (c : C)
  : size (toList c) = size c := by
  simp [size, size_def]

end LeanColls.Seq
