/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import Std.Data.Array.Lemmas
import Std.Data.List.Lemmas
import Mathlib.Data.Array.Lemmas

import LeanColls.Classes.Seq
import LeanColls.Data.List
import LeanColls.Data.Range
import LeanColls.Data.Transformer.FixSize

open LeanColls

namespace Array

def cons (x : α) (A : Array α) : Array α := #[x] ++ A

def snoc := @Array.push
def getSnoc? (A : Array α) :=
  if h : A.size > 0 then
    let x := A[A.size-1]'(tsub_lt_self h (by decide))
    some (A.pop, x)
  else
    none

theorem ext_iff (A B : Array α) (h : A.size = B.size) : A = B ↔ ∀ (i : Nat) h1 h2, A[i]'h1 = B[i]'h2 := by
  constructor
  · rintro rfl; simp
  · apply ext _ _ h

theorem ext'_iff (A B : Array α) : A = B ↔ A.data = B.data := by
  cases A; cases B; simp

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
  getSnoc? := Array.getSnoc?

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
  getCons?_eq_none := by
    intro ⟨L⟩
    simp [LeanColls.toList, Seq.getCons?]
    split <;> simp <;> cases L <;> simp at *
  getCons?_eq_some := by
    intro ⟨L⟩ x ⟨L'⟩
    cases L
    · simp [LeanColls.toList, Seq.getCons?]
      intro h; split at h; simp_all; rw [size_eq_length_data] at *; simp at *
    next hd tl =>
    simp [LeanColls.toList, Seq.getCons?, getElem_eq_data_get]
    split <;> simp_all [size_mk]
    rintro rfl
    constructor
    · intro h
      have := congrArg size h
      simp at this; cases this
      have : List.length tl = List.length L' := by
        clear h; simp_all [size_mk]
      rw [Array.ext_iff] at h
      · simp at h; simp [getElem_eq_data_get] at h
        apply List.ext_get
        · assumption
        intro i h1 h2
        apply h i (this ▸ h1) h2
      · simp
    · rintro rfl
      rw [Array.ext_iff]
      · simp; simp [getElem_eq_data_get]
      · simp; simp_all [size_mk]
  getSnoc?_eq_none := by
    simp [LeanColls.toList, Seq.getSnoc?]
    rintro ⟨L⟩; simp [getSnoc?]; exact List.length_eq_zero
  getSnoc?_eq_some := by
    rintro ⟨L⟩ x ⟨L'⟩
    simp [LeanColls.toList, Seq.getSnoc?, getSnoc?]
    split <;> simp_all [List.length_eq_zero]
    simp [pop]
    rw [getElem_eq_data_get, ← List.getLast_eq_get L (List.ne_nil_of_length_pos ‹_›)]
    constructor
    · rintro ⟨rfl,rfl⟩
      simp only [List.dropLast_append_getLast]
    · rintro rfl
      simp only [List.dropLast_concat, List.getLast_append, and_self]
  toList_update := by
    rintro ⟨c⟩ ⟨i,h⟩ f
    simp [Seq.update, LeanColls.toList, getElem_eq_data_get]
    congr 2; apply List.get_eq_get
    · rw [toList_eq]
    · simp
  toList_cons := by
    simp [LeanColls.toList, Seq.cons, cons]
  toList_snoc := by
    simp [LeanColls.toList, Seq.snoc, snoc]

end Array

abbrev NArray (α : Type u) (n : Nat) := FixSize (Array α) n

/-! ### Scalar Arrays -/

namespace ByteArray

instance : Fold ByteArray UInt8 where
  fold arr := arr.foldl
  foldM arr := arr.foldlM

instance : Seq ByteArray UInt8 where
  size := size
  get := get
  set := set
  empty := empty
  insert := push
  toList := toList
  ofFn := ofFn

end ByteArray
