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
  foldM c f init := Array.foldlM f init c
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
    rintro ⟨L⟩; simp [getSnoc?]
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
  fold_eq_fold_toList := by
    intro A; use A.toList; refine ⟨.rfl, ?_⟩
    intros
    simp [fold, foldl_eq_foldl_data]
  foldM_eq_fold := by
    intros
    simp [fold, foldM]
    rw [foldlM_eq_foldlM_data, foldl_eq_foldl_data, List.foldlM_eq_foldl]
end Array

abbrev ArrayN.{u,w} (α : Type u) (n : Nat) :=
  FixSize.{u,0,w} (Array α) (Fin n)
abbrev ArrayI.{u,v,w} (ι : Type u) [IndexType ι] (α : Type v) :=
  FixSize.{v,u,w} (Array α) ι

/-! ### Scalar Arrays -/

namespace ByteArray

instance : ToList ByteArray UInt8 where
  toList := toList

instance : Fold ByteArray UInt8 where
  fold arr := arr.foldl
  foldM arr := arr.foldlM

instance : Membership UInt8 ByteArray := Fold.toMem
--instance : Mem.ToList ByteArray UInt8 := Fold.toMem.ToList

instance : Seq ByteArray UInt8 where
  size := size
  get := get
  set := set
  empty := empty
  insert := push
  ofFn := ofFn
  snoc := push
  -- TODO(JG): implement bytearray append directly

end ByteArray

namespace FloatArray

instance : ToList FloatArray Float where
  toList := toList

instance : Fold FloatArray Float where
  fold arr := arr.foldl
  foldM arr := arr.foldlM

instance : Membership Float FloatArray := Fold.toMem
--instance : Mem.ToList FloatArray Float := Fold.toMem.ToList

def append (A1 A2 : FloatArray) : FloatArray :=
  aux A1 0
where aux (acc : FloatArray) (i : Nat) : FloatArray :=
  if _h : i < A2.size then
    aux (acc.push A2[i]) (i+1)
  else
    acc
termination_by A2.size - i

instance : Append FloatArray where
  append := append

def ofFn (f : Fin n → Float) : FloatArray :=
  aux (FloatArray.mkEmpty n) 0
where aux (acc : FloatArray) (i : Nat) : FloatArray :=
  if h : i < n then
    aux (acc.push (f ⟨i,h⟩)) (i+1)
  else
    acc
termination_by n - i

instance : Seq FloatArray Float where
  size := size
  get := get
  set := set
  empty := empty
  insert := push
  toList := toList
  ofFn := ofFn
  snoc := push
  append := append

end FloatArray
