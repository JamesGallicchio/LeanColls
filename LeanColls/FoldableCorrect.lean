/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.List.Basic

namespace LeanColls

/-! Definition of toList in terms of a fold.

Used to define correctness for [Foldable] and [Foldable']
-/
def canonicalToList (fold : {β : Type w} → (β → τ → β) → β → β) : List τ :=
  fold (λ acc x => acc ++ [x]) []

namespace Foldable

class Correct (C τ) extends Foldable C τ where
  foldCorrect : ∀ {β} (f : β → τ → β) acc (c : C),
    fold c f acc = (
      canonicalToList (fold c)
      |>.fold f acc)

end Foldable

namespace Foldable'

class Correct (C τ) (M : outParam (Membership τ C))
  extends Foldable.Correct C τ, Foldable' C τ M where
  memCorrect : ∀ x (c : C), x ∈ c ↔ x ∈ canonicalToList (fold c)
  fold'Correct : ∀ {β} (c : C) (f : β → (x : τ) → x ∈ c → β) acc,
    fold' c f acc = (
      canonicalToList (fold c)
      |>.fold' (λ acc x h => f acc x ((memCorrect x c).mpr h)) acc)

theorem fold_eq_fold' [M : Membership τ C] [F : Foldable'.Correct C τ M]
  (c : C) (f : β → τ → β) (acc : β)
  : F.fold c f acc = F.fold' c (λ acc x _ => f acc x) acc
  := by
  rw [F.foldCorrect]
  rw [F.fold'Correct]
  simp [canonicalToList, List.fold_eq_fold']

theorem fold_pair [F : Foldable.Correct C τ]
  (f₁ : β₁ → τ → β₁) (acc₁ : β₁) (f₂ : β₂ → τ → β₂) (acc₂ : β₂) (c : C)
  : F.fold c (λ (acc₁,acc₂) x => (f₁ acc₁ x, f₂ acc₂ x)) (acc₁, acc₂)
    = (F.fold c (λ acc₁ x => f₁ acc₁ x) acc₁,
       F.fold c (λ acc₂ x => f₂ acc₂ x) acc₂)
  := by
  let list := canonicalToList (F.fold c)
  suffices
    List.fold list (λ (acc₁,acc₂) x => (f₁ acc₁ x, f₂ acc₂ x)) (acc₁, acc₂)
      = (List.fold list (λ acc₁ x => f₁ acc₁ x) acc₁,
         List.fold list (λ acc₂ x => f₂ acc₂ x) acc₂)
         by
    simp at this
    simp [←F.foldCorrect] at this
    exact this
  induction list generalizing acc₁ acc₂ with
  | nil =>
    simp [List.fold, List.foldl]
  | cons x xs ih =>
    simp
    apply ih
  
end Foldable'
