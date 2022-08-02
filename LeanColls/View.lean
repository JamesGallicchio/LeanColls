/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.FoldableOps
import LeanColls.FoldableCorrect

namespace LeanColls

structure View (τ) where
  fold : {β : Type w} → (β → τ → β) → β → β

namespace View

instance : Foldable (View τ) τ where
  fold c f acc := c.fold f acc

instance [BEq τ] : FoldableOps (View τ) τ := default

@[inline,reducible]
def view {F τ} (c : F) [Foldable F τ] : View τ where
  fold f acc := Foldable.fold c f acc

@[inline,reducible]
def map {τ : Type u} {τ' : Type v} (f : τ → τ') (v : View τ) : View τ' where
  fold foldF foldAcc :=
    v.fold (λ acc t => foldF acc (f t)) foldAcc

@[inline,reducible]
def filter (f : τ → Bool) (v : View τ) : View τ where
  fold foldF foldAcc :=
    v.fold (λ a x =>
      if f x then foldF a x else a
    ) foldAcc

@[inline,reducible]
def filterMap (f : τ → Option τ') (v : View τ) : View τ' where
  fold := λ foldF foldAcc =>
    v.fold (λ a x =>
      match f x with
      | none    => a
      | some x' => foldF a x'
    ) foldAcc

instance : FoldableOps (View τ) τ := default

structure WithMem (τ) (c : C) (M : outParam (Membership τ C)) where
  fold' : {β : Type w} → (β → (x : τ) → x ∈ c → β) → β → β

@[inline,reducible]
def view' [Foldable' C τ M] (c : C) : WithMem τ c M where
  fold' := Foldable'.fold' c

namespace WithMem

@[inline,reducible]
def map' {τ : Type u} {c : C} {M} (v : View.WithMem τ c M) {τ' : Type v} (f : (x : τ) → M.mem x c → τ') : View τ' where
  fold foldF foldAcc :=
    v.fold' (λ acc t h => foldF acc (f t h)) foldAcc

end WithMem


theorem canonicalToList_map [Foldable.Correct C τ] (c : C) (f : τ → τ')
  : canonicalToList (((View.view c).map f).fold)
    = List.map f (canonicalToList (Foldable.fold c))
  := by
  generalize h : canonicalToList (Foldable.fold c) = list
  simp [canonicalToList]
  rw [Foldable.Correct.foldCorrect, h]
  clear h c
  simp [List.fold]
  suffices ∀ init,
    List.foldl (fun acc t => acc ++ [f t]) init list = init ++ List.map f list
    from this []
  intro init
  induction list generalizing init with
  | nil =>
    simp [List.foldl, List.map]
  | cons x xs ih =>
    simp [List.foldl, List.map]
    rw [List.append_cons _ _ (List.map _ _)]
    exact ih _

theorem canonicalToList_filter [Foldable.Correct C τ] (c : C) (f)
  : canonicalToList (((View.view c).filter f).fold)
    = List.filter f (canonicalToList (Foldable.fold c))
  := by
  generalize h : canonicalToList (Foldable.fold c) = list
  simp [canonicalToList]
  rw [Foldable.Correct.foldCorrect, h]
  clear h c
  simp [List.fold]
  suffices ∀ init,
    List.foldl (fun acc t => if f t = true then acc ++ [t] else acc) init list
      = List.filterAux f list init.reverse
    from this []
  intro init
  induction list generalizing init with
  | nil =>
    simp [List.foldl, List.filter, List.filterAux]
  | cons x xs ih =>
    simp [List.foldl, List.filter, List.filterAux]
    split
    case inl h =>
      simp [h]
      have : x :: List.reverse init = List.reverse (init ++ [x]) := by
        simp
      rw [this]
      exact ih _
    case inr h =>
      simp [h, ih]
