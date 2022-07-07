/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.FoldableOps

namespace LeanColls

structure View (τ) where
  fold : {β : Type w} → (β → τ → β) → β → β

namespace View

instance : Foldable (View τ) τ where
  fold f acc c := c.fold f acc

instance [BEq τ] : FoldableOps (View τ) τ := default

@[inline]
def view {F τ} (c : F) [Foldable F τ] : View τ where
  fold f acc := Foldable.fold f acc c

@[inline]
def map {τ : Type u} {τ' : Type v} (f : τ → τ') (v : View τ) : View τ' where
  fold foldF foldAcc :=
    v.fold (λ acc t => foldF acc (f t)) foldAcc

@[inline]
def filter (f : τ → Bool) (v : View τ) : View τ where
  fold foldF foldAcc :=
    v.fold (λ a x =>
      if f x then foldF a x else a
    ) foldAcc

@[inline]
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

@[inline]
def view' [Foldable' C τ M] (c : C) : WithMem τ c M where
  fold' := Foldable'.fold' c

namespace WithMem

@[inline]
def map' {τ : Type u} {c : C} {M} (v : View.WithMem τ c M) {τ' : Type v} (f : (x : τ) → M.mem x c → τ') : View τ' where
  fold foldF foldAcc :=
    v.fold' (λ acc t h => foldF acc (f t h)) foldAcc
