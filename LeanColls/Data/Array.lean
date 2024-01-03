/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import Std.Data.Array.Lemmas
import Mathlib.Data.Array.Lemmas

import LeanColls.Classes.Seq
import LeanColls.Data.List

open LeanColls

namespace Array

def cons (x : α) (A : Array α) : Array α := #[x] ++ A

def snoc := @Array.push
def snoc? (A : Array α) :=
  if h : A.size > 0 then
    let x := A[A.size-1]'(tsub_lt_self h (by decide))
    some (A.pop, x)
  else
    none

instance : ToList (Array α) α where
  toList := Array.toList

instance : Seq (Array α) α where
  ofFn := Array.ofFn
  size := Array.size
  empty := Array.empty
  insert := Array.push
  singleton := Array.singleton
  fold c f init := Array.foldl f init c
  get := Array.get
  set := Array.set
  cons := Array.cons
  snoc := Array.push
  snoc? := Array.snoc?

instance : LawfulSeq (Array α) α where
  mem_iff_mem_toList := by simp [LeanColls.toList, mem_def]
  toList_append := by simp [LeanColls.toList]
  toMultiset_empty := by
    simp [LeanColls.toList, ToMultiset.toMultiset, LeanColls.empty, empty]
  toMultiset_insert := by
    simp [LeanColls.toList, ToMultiset.toMultiset, LeanColls.insert]
  toMultiset_singleton := by
    simp [LeanColls.toList, ToMultiset.toMultiset, LeanColls.singleton]
  size_def := by
    simp [LeanColls.toList, LeanColls.size]
  toList_ofFn := by
    simp [LeanColls.toList, Seq.ofFn, List.ofFn]
  get_def := by
    rintro c ⟨i,hi⟩
    simp [LeanColls.toList, Seq.get]
    rw [getElem_eq_data_get, ← Option.some_inj,
      ← List.get?_eq_get, ← List.get?_eq_get, toList_eq]
  toList_set := by
    rintro c ⟨i,hi⟩ x
    simp [LeanColls.toList, Seq.set]
  cons?_eq_none := by
    intro ⟨L⟩
    simp [LeanColls.toList, Seq.cons?]
    split <;> simp <;> cases L <;> simp at *
  cons?_eq_some := by
    intro ⟨L⟩ x ⟨L'⟩ h
    simp [LeanColls.toList]
    simp [Seq.cons?] at h; split at h <;> simp at h
    next hs =>
    rcases h with ⟨rfl,h⟩
    replace h := congrArg Array.data h; simp at h; cases h
    rw [size_eq_length_data] at hs; simp at hs
    cases L <;> simp at hs ⊢
    simp [getElem_eq_data_get]
    rw [← toList_eq, show (ofFn _).toList = List.ofFn _ from rfl]
    apply List.ext_get
    · simp [hs]
    intro n h1 h2
    simp
  cons?_eq_some_of_toList := by
    rintro ⟨L⟩ x L'
    simp [LeanColls.toList]
    rintro rfl; use ⟨L'⟩
    simp [Seq.cons?]
    split
    next h => simp [size] at h
    next h =>
      simp [size] at h; simp [getElem_eq_data_get]
      apply ext
      · simp [h]
      intro i hi hi'
      simp; simp [Array.getElem_eq_data_get]
  snoc?_eq_none := by
    simp [LeanColls.toList, Seq.snoc?]
    rintro ⟨L⟩; simp [snoc?]; exact List.length_eq_zero
  snoc?_eq_some := by
    rintro ⟨L⟩ x ⟨L'⟩ h
    simp [LeanColls.toList]
    simp [Seq.snoc?, snoc?] at h; split at h <;> simp at h
    rcases h with ⟨hL', rfl⟩
    replace hL' := congrArg (Array.data) hL'
    simp at hL'; cases hL'
    rw [eq_comm]; convert List.dropLast_append_getLast _
    rw [getElem_eq_data_get, List.getLast_eq_get]
    exact List.length_pos.mp ‹_›
  snoc?_eq_some_of_toList := by
    rintro ⟨L⟩ x L' h
    simp [LeanColls.toList] at h; cases h
    use ⟨L'⟩
    simp [Seq.snoc?, snoc?]
    constructor
    · apply ext'; simp
    · rw [getElem_eq_data_get, List.get_append_right]
      repeat simp

end Array

abbrev NArray (α : Type u) (n : Nat) := Seq.FixSize (Array α) n
