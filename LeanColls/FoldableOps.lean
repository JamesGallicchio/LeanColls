/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.FoldableCorrect
import LeanColls.List.Basic
import LeanColls.List.Classes

namespace LeanColls

class FoldableOps.{uC,uT} (C : Type uC) (τ : outParam (Type uT)) where
  toList : C → List τ
  all : C → (τ → Bool) → Bool
  contains : C → [BEq τ] → τ → Bool
  sum : C → [AddMonoid τ] → τ

namespace FoldableOps

def defaultImpl (C : Type u) (τ : Type v) [Foldable C τ] : FoldableOps C τ where
  toList := λ c =>
    Foldable.fold c (fun acc x => x::acc) []
    |>.reverse
  all := λ c f =>
    Foldable.fold c (β := ULift Bool) (fun acc x => ⟨acc.down && f x⟩) ⟨true⟩
    |>.down
  contains := λ c _ x  =>
    Foldable.fold c (β := ULift Bool) (fun acc y => ⟨acc.down || BEq.beq x y⟩) ⟨true⟩
    |>.down
  sum := λ c =>
    Foldable.fold c (fun acc x => acc + x) 0

instance [Foldable C τ] : Inhabited (FoldableOps C τ) where
  default := defaultImpl C τ

@[simp]
theorem default_toList_list (L : List τ)
  : (defaultImpl (List τ) τ).toList L = L
  := by
  simp [toList, defaultImpl, Foldable.fold, List.fold, List.reverse]
  apply List.reverseAux_reverseAux_nil

theorem default_toList_pred_fold (c : C) (c' : C')
  [Foldable C τ] [Foldable C' τ]
  (h : Foldable.fold c (β := List τ) = Foldable.fold c')
  : (defaultImpl C τ).toList c = (defaultImpl C' τ).toList c'
  := by
  simp [toList, defaultImpl, h]

@[simp]
theorem default_toList_eq_canonicalToList [Foldable.Correct C τ] (c : C)
  : (defaultImpl C τ).toList c = canonicalToList (Foldable.fold c)
  := by
  rw [default_toList_pred_fold c (canonicalToList (Foldable.fold c))]
  simp [toList]
  simp [Foldable.fold]
  funext f acc
  apply Foldable.Correct.foldCorrect

@[simp]
theorem default_sum_list_eq_list_sum [AddMonoid τ] (L : List τ)
  : (defaultImpl (List τ) τ).sum L = L.sum
  := by
  simp [defaultImpl, sum]
  simp [Foldable.fold, List.fold]
  suffices ∀ (acc : τ), List.foldl (fun acc x => acc + x) acc L = acc + List.sum L by
    have := this 0
    simp at this
    exact this
  intro acc
  induction L generalizing acc with
  | nil =>
    simp [List.foldl, List.sum]
  | cons x xs ih =>
    simp [List.foldl, List.sum, ih]
    rw [AddMonoid.toAddSemigroup.add_assoc]

theorem default_sum_pred_fold (c : C) (c' : C')
  [Foldable C τ] [Foldable C' τ] [AddMonoid τ]
  (h : Foldable.fold c (β := τ) = Foldable.fold c')
  : (defaultImpl C τ).sum c = (defaultImpl C' τ).sum c'
  := by
  simp [sum, defaultImpl, h]