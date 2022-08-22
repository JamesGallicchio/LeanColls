/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Array.Basic

namespace LeanColls

structure COWArray (α n) where
  backing : Array α n
deriving Repr

namespace COWArray
variable (A : COWArray α n)

def new (x : α) (n : Nat) := Array.new x n |> COWArray.mk
def empty : COWArray α 0 := ⟨Array.empty⟩
def singleton (x : α) : COWArray α 1 := ⟨Array.init (λ _ => x)⟩

@[inline] def get : Fin n → α := A.backing.get
@[inline] def set (i : Fin n) (x : α) : COWArray α n :=
  A.backing.copy |>.set i x |> COWArray.mk

@[inline] def update (i : Fin n) (f : α → α) : COWArray α n :=
  A.set i (f <| A.get i)

@[inline] def cons (x : α) : COWArray α n.succ :=
  ⟨Array.init (λ i => match i with
    | ⟨0,_⟩ => x
    | ⟨i+1,h⟩ => A.get ⟨i, Nat.lt_of_succ_lt_succ h⟩)⟩

@[inline] def snoc (x : α) : COWArray α n.succ :=
  ⟨Array.init (λ i =>
    if h:i.val < n then
      A.get ⟨i, h⟩
    else x)⟩

@[inline] def front (A : COWArray α n.succ) : α × COWArray α n :=
  (A.get ⟨0, Nat.zero_lt_succ _⟩,
  ⟨Array.init (λ i => A.get i.succ)⟩)

@[inline] def back (A : COWArray α n.succ) : COWArray α n × α :=
  (⟨Array.init (λ i => A.get i.embed_succ)⟩,
  A.get ⟨n, Nat.lt_succ_self _⟩)

instance : Indexed (COWArray α n) α where
  size _ := n
  nth := get

@[simp]
theorem fold_eq_backing_fold (A : COWArray α n)
  : ∀ {β}, Foldable.fold A (β := β) = Foldable.fold A.backing
  := by
  intro β
  simp [Foldable.fold, Size.size, Indexed.nth, get]

@[simp]
theorem backing_set (A : COWArray α n) (i : Fin n) (x : α)
  : (A.set i x).backing = A.backing.set i x
  := by
  simp [set, Array.copy_def]