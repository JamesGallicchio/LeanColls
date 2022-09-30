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
  toList    (c : C) : List τ
  all       (c : C) (f : τ → Bool) : Bool
  any       (c : C) (f : τ → Bool) : Bool
  contains  (c : C) [BEq τ] : τ → Bool
  sum       (c : C) [Add τ] [Zero τ] : τ
  max       (c : C) [L : LT τ] [DecidableRel L.lt] : Option τ
  toString  (c : C) [ToString τ] (sep : String) : String 
  find      (c : C) (f : τ → Bool) : Option τ
  findMap   (c : C) (f : τ → Option τ') : Option τ'  

namespace FoldableOps

def defaultImpl (C : Type u) (τ : Type v) [Foldable C τ] : FoldableOps C τ where
  toList := λ c =>
    Foldable.fold c (fun acc x => x::acc) []
    |>.reverse
  all := λ c f =>
    Foldable.fold c (β := ULift Bool) (fun acc x => ⟨acc.down && f x⟩) ⟨true⟩
    |>.down
  any := λ c f =>
    Foldable.fold c (β := ULift Bool) (fun acc x => ⟨acc.down || f x⟩) ⟨false⟩
    |>.down
  contains := λ c _ x  =>
    Foldable.fold c (β := ULift Bool) (fun acc y => ⟨acc.down || BEq.beq x y⟩) ⟨false⟩
    |>.down
  sum := λ c =>
    Foldable.fold c (fun acc x => acc + x) 0
  max := λ c =>
    Foldable.fold c (fun
      | none   => λ x => some x
      | some x => λ y => some (_root_.max x y)
    ) none
  toString := λ c _ sep =>
    Foldable.fold c
      (fun
      | ⟨none⟩  , x => ⟨some (ToString.toString x)⟩
      | ⟨some x⟩, y => ⟨some (x ++ sep ++ ToString.toString y)⟩)
      (⟨none⟩ : ULift (Option String))
    |>.down.getD ""
  find := λ c f =>
    Foldable.fold c
      (fun
      | none, x => if f x then some x else none
      | some x, _ => some x)
      none
  findMap := λ c f =>
    Foldable.fold c
      (fun
      | none, x => f x
      | some x, _ => some x)
      none

def mapImpl' (F : C → Type u) (f : (c : C) → F c) [(c : C) → FoldableOps (F c) τ] : FoldableOps C τ := {
  toList    := λ c => FoldableOps.toList (f c)
  all       := λ c => FoldableOps.all (f c)
  any       := λ c => FoldableOps.all (f c)
  sum       := λ c => FoldableOps.sum (f c)
  contains  := λ c => FoldableOps.contains (f c)
  max       := λ c => FoldableOps.max (f c)
  toString  := λ c => FoldableOps.toString (f c)
  find      := λ c => FoldableOps.find (f c)
  findMap   := λ c => FoldableOps.findMap (f c)
}

def mapImpl (f : C → C') [FoldableOps C' τ] : FoldableOps C τ :=
  mapImpl' (λ _ => C') f

instance [Foldable C τ] : Inhabited (FoldableOps C τ) where
  default := defaultImpl C τ


/-! # Lemmas -/

@[simp]
theorem default_toList_list (L : List τ)
  : (defaultImpl (List τ) τ).toList L = L
  := by
  simp [toList, defaultImpl]
  rw [Foldable.Correct.foldCorrect, List.foldl_eq_reverseAux]
  simp [List.reverse]
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
  simp [Foldable.fold, List.foldl]
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