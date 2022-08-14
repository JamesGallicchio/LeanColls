/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.List.Basic
import LeanColls.FoldableCorrect
import LeanColls.FoldableOps

open LeanColls

namespace List

theorem canonicalToList_eq_id (l : List τ)
  : canonicalToList (fold l) = l
  := by
  simp [canonicalToList, fold]
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

instance : Foldable'.Correct (List τ) τ inferInstance where
  fold := fold
  foldCorrect := by
    simp [Foldable.fold, canonicalToList_eq_id]
  fold' := fold'
  memCorrect := by
    simp [Foldable.fold, canonicalToList_eq_id]
  fold'Correct := by
    intro β c f acc
    simp [Foldable.fold]
    suffices ∀ l (h : c = l) (h' : ∀ {x}, x ∈ l → x ∈ c), fold' c f acc = fold' l (fun acc x h => f acc x (h' h)) acc from
      this (canonicalToList (fold c)) (by rw [canonicalToList_eq_id]) (by
        rw [canonicalToList_eq_id]
        intros; trivial
        )
    intro l h_l h'
    cases h_l
    apply congrArg
    rfl

instance : Iterable (List τ) τ where
  ρ := List τ
  step := List.front?
  toIterator := id

instance : FoldableOps (List τ) τ := default

instance : Enumerable (List τ) τ where
  ρ := List τ
  fromEnumerator := id
  insert := λ
    | none => []
    | some ⟨x,xs⟩ => x::xs
