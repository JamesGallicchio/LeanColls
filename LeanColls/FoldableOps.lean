/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.FoldableCorrect
import LeanColls.List.Basic

namespace LeanColls

class FoldableOps.{uC,uT} (C : Type uC) (τ : Type uT) where
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

theorem sum_eq_sum_toList [F : Foldable.Correct C τ] [FoldableOps C τ] [AddMonoid τ] (c : C)
  (h : FoldableOps.sum c = (defaultImpl C τ).sum c := by rfl)
  : FoldableOps.sum c = List.sum (canonicalToList (Foldable.fold c))
  := by
  simp [autoParam] at h
  rw [h]
  simp [defaultImpl, sum]
  rw [Foldable.Correct.foldCorrect]
  generalize canonicalToList _ = list
  simp [List.fold]
  suffices ∀ (acc : τ) list, List.foldl (fun acc x => acc + x) acc list = acc + List.sum list by
    have := this 0 list
    simp at this
    exact this
  intro acc list
  induction list generalizing acc with
  | nil =>
    simp [List.foldl, List.sum]
  | cons x xs ih =>
    simp [List.foldl, List.sum, ih]
    rw [AddMonoid.toAddSemigroup.add_assoc]
