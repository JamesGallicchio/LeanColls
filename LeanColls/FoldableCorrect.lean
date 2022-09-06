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

class Correct (C) (τ : outParam _) extends Foldable C τ where
  foldCorrect : ∀ {β} (c : C) (f : β → τ → β) acc,
    fold c f acc = (
      canonicalToList (fold c)
      |>.foldl f acc)

theorem fold_pair [F : Foldable.Correct C τ]
  (f₁ : β₁ → τ → β₁) (acc₁ : β₁) (f₂ : β₂ → τ → β₂) (acc₂ : β₂) (c : C)
  : F.fold c (λ (acc₁,acc₂) x => (f₁ acc₁ x, f₂ acc₂ x)) (acc₁, acc₂)
    = (F.fold c (λ acc₁ x => f₁ acc₁ x) acc₁,
       F.fold c (λ acc₂ x => f₂ acc₂ x) acc₂)
  := by
  let list := canonicalToList (F.fold c)
  suffices
    List.foldl (λ (acc₁,acc₂) x => (f₁ acc₁ x, f₂ acc₂ x)) (acc₁, acc₂) list
      = (List.foldl (λ acc₁ x => f₁ acc₁ x) acc₁ list,
         List.foldl (λ acc₂ x => f₂ acc₂ x) acc₂ list)
         by
    simp at this
    simp [←F.foldCorrect] at this
    exact this
  induction list generalizing acc₁ acc₂ with
  | nil =>
    simp [List.foldl]
  | cons x xs ih =>
    simp
    apply ih

end Foldable

namespace Foldable'

class Correct (C) (τ : outParam _) (M : outParam (Membership τ C))
  extends Foldable.Correct C τ, Foldable' C τ M where
  memCorrect : ∀ x (c : C), x ∈ c ↔ x ∈ canonicalToList (fold c)
  fold'Correct : ∀ {β} (c : C) (f : β → (x : τ) → x ∈ c → β) acc,
    fold' c f acc = (
      canonicalToList (fold c)
      |>.foldl' (λ acc x h => f acc x ((memCorrect x c).mpr h)) acc)

theorem fold_eq_fold' [M : Membership τ C] [F : Foldable'.Correct C τ M]
  (c : C) (f : β → τ → β) (acc : β)
  : F.fold c f acc = F.fold' c (λ acc x _ => f acc x) acc
  := by
  rw [F.foldCorrect]
  rw [F.fold'Correct]
  simp [canonicalToList, List.foldl_eq_foldl']

theorem fold'_append_singleton_eq_map [M : Membership τ C] [Foldable'.Correct C τ M]
  (c : C) (f : (x : τ) → x ∈ c → τ')
  : Foldable'.Correct.fold' c (λ acc x h => acc ++ [f x h]) []
    = (canonicalToList (Foldable.fold c)
      |>.map' (fun x h => f x ((Foldable'.Correct.memCorrect _ _).mpr h)))
  := by
  rw [Correct.fold'Correct]
  rw [List.foldl'_eq_subtypeByMem_foldl]
  rw [List.map', List.foldl_eq_map]

theorem fold_canonicalToList_fold'_eq_fold' [Foldable'.Correct C τ M]
  (c : C) (f' : (x : τ) → M.mem x c → τ') (f : β → τ' → β) (acc)
  : List.foldl f acc
    (canonicalToList (fun f init =>
      Foldable'.Correct.fold' c (fun acc x h => f acc (f' x h)) init
      )) = Foldable'.Correct.fold' c (fun acc x h => f acc (f' x h)) acc
  := by
  simp [canonicalToList]
  rw [fold'_append_singleton_eq_map]
  rw [List.map', List.foldl_map,
      Foldable'.Correct.fold'Correct,
      List.foldl'_eq_subtypeByMem_foldl]

theorem canonicalToList_fold'_eq_map' [Foldable'.Correct C τ M]
  (c : C) (f' : (x : τ) → M.mem x c → τ')
  : canonicalToList (fun f init =>
      Foldable'.Correct.fold' c (fun acc x h => f acc (f' x h)) init
      ) =
    (canonicalToList (Foldable.fold c)).map' (fun x h =>
      f' x ((Foldable'.Correct.memCorrect _ _).mpr h))
  := by
  conv =>
    lhs simp [canonicalToList]
    rw [Correct.fold'Correct]
    rw [List.foldl'_eq_subtypeByMem_foldl]
    rw [List.foldl_eq_map]
