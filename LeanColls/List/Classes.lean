/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.List.Basic
import LeanColls.FoldableCorrect

open LeanColls

namespace List

@[simp]
theorem canonicalToList_eq_id (l : List τ)
  : canonicalToList l.foldl = l
  := by
  simp [canonicalToList, foldl]
  suffices ∀ acc, foldl (fun acc x => acc ++ [x]) acc l = acc ++ l by
    have := this []
    simp at this
    exact this
  induction l with
  | nil =>
    simp [foldl]
  | cons x xs ih =>
    intro acc
    simp [foldl]
    rw [ih]
    simp [List.append_assoc]

instance instFoldable'Correct : Foldable'.Correct (List τ) τ inferInstance where
  fold l := l.foldl
  foldCorrect := by
    simp [Foldable.fold, canonicalToList_eq_id]
  fold' := foldl'
  memCorrect := by
    simp [Foldable.fold, canonicalToList_eq_id]
  fold'Correct := by
    intro β c f acc
    simp [Foldable.fold]
    simp
    suffices ∀ l (_ : c = l) (h' : ∀ {x}, x ∈ l → x ∈ c), foldl' c f acc = foldl' l (fun acc x h => f acc x (h' h)) acc from
      this (canonicalToList c.foldl) (by rw [canonicalToList_eq_id]) (by
        rw [canonicalToList_eq_id]
        intros; trivial
        )
    intro l h_l h'
    cases h_l
    apply congrArg
    rfl

@[simp]
theorem canonicalToList_of_foldable (l : List τ)
  : canonicalToList (Foldable.fold l) = l
  := by simp [Foldable.fold]

instance : Iterable (List τ) τ where
  ρ := List τ
  step := List.front?
  toIterator := id

instance : Enumerable (List τ) τ where
  ρ := List τ
  fromEnumerator := id
  insert := λ
    | none => []
    | some ⟨x,xs⟩ => x::xs
